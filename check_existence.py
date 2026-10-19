import argparse
import csv  # CHANGED: for the audit CSV
import hashlib  # CHANGED: for the per-row hash in the audit CSV
import json
import re
import sys  # CHANGED: needed for sys.exit(1) in the clean --input error handling below
import time
import difflib
import xml.etree.ElementTree as ET
from datetime import datetime, timezone, timedelta
from pathlib import Path

import requests

# API URLs and constants
PUBMED_ESUMMARY_URL = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi"
PUBMED_EFETCH_URL = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi"
CROSSREF_WORKS_URL = "https://api.crossref.org/works/{doi}"
PUBMED_BATCH_SIZE = 200
PUBMED_DELAY = 0.4
CROSSREF_DELAY = 0.15
URL_DELAY = 0.15
MAX_RETRIES = 3
RETRY_BACKOFF = 2.0

# Reads a JSON file containing references and returns verdicts based on quality status of each reference,
# whether reference has changed since last run,
# count of each verdict type,
# ranking of each reference based on evidence quality

# This script is meant to be run on a regular schedule since bibliography entries can change
# frequently (e.g., papers redacted or deleted). This is achieved by rerunning the cache every 28 days rather than trusting that the entries queried before
# and stored in the cache never change. CACHE_TTL_DAYS (default is 28) determines the length of time before the cache is considered stale and
# needs to be refreshed.
CACHE_TTL_DAYS = 28

# Regexes for normalizing PMID and DOI strings as well as Jats tags in CrossRef abstracts
PMID_PREFIX_RE = re.compile(r"^\s*pmid\s*:?\s*", re.IGNORECASE)
DOI_URL_PREFIX_RE = re.compile(r"^\s*(https?://)?(dx\.)?doi\.org/", re.IGNORECASE)
DOI_LABEL_RE = re.compile(r"^\s*doi\s*:?\s*", re.IGNORECASE)
JATS_TAG_RE = re.compile(r"<[^>]+>")

# Checked against NLM's official publication type list
# Includes both terms below as they are both used in PubMed's vocabulary to indicate a guideline document
# Guideline refers to a policy statement or recommendation while practice guideline is used to guide clinical practice
GUIDELINE_PUBTYPES = {"Guideline", "Practice Guideline"}

# Also from NLM's official publication type list, these are tags that should raise a red flag
# Retracted publications and retraction notices should be excluded from the bibliography
# Expression of concern and corrected and republished articles should be flagged for manual review
INTEGRITY_PUBTYPES = {
    "Retracted Publication", "Retraction Notice", "Expression of Concern",
    "Corrected and Republished Article",
}

# Also from NLM's official publication type list, these are tags that should raise a yellow flag for low-quality evidence
# These should be flagged manual review before being included in the bibliography
LOW_QUALITY_EVIDENCE_PUBTYPES = {
    "Case Reports",              # single-patient anecdote, no control group -- Oxford level 4
    "Meeting Abstract",          # preliminary data, presented before full peer review
    "Preprint",                  # not peer-reviewed at all yet
    "Review",                    # narrative/non-systematic -- no reproducible methodology
    "Editorial",                 # opinion piece, not original data
    "Comment",                   # opinion on another article, not original data
    "Letter",                    # typically uncontrolled observation or critique
    "Consensus Statement",       # expert opinion without a described systematic review
    "Consensus Development Conference (NIH)",  # expert consensus, not a study design
    "Historical Article",        # not current clinical evidence
    "Personal Narrative",        # subjective, single-perspective
    "Anecdotes",                 # definitionally anecdotal
    "News",                      # not research at all
}

# Determines whether pmid value has no ID (None or empty string), is a valid pmid (digits only), or is malformed (non-digit characters)
# Returns a tuple containing cleaned pmid string (or None) and a boolean value indicating whether the pmid is malformed (True) or not (False)
def normalize_pmid(raw):
    if raw is None:
        return None, False
    s = str(raw).strip()
    if not s:
        return None, False
    s = PMID_PREFIX_RE.sub("", s).strip() # Strip leading label using regex above, leaving only what is left after label removed
    if s.isdigit(): # If what is left after stripping the label is all digits, it is a valid pmid
        return s, False
    return None, True # If what is left after stripping the label is not all digits, it is a malformed pmid


def normalize_doi(raw):
    # Normalizes a raw doi field (may be in the form of a bare DOI, doi.org URL, or
    # a "doi:"-labeled string) into lowercased canonical DOI string or None)
    # Returns a tuple containing cleaned doi string (or None) and a boolean value indicating whether the doi is malformed (True) or not (False)
    if raw is None:
        return None, False
    s = str(raw).strip()
    if not s:
        return None, False
    s = DOI_URL_PREFIX_RE.sub("", s) # Strips URL wrapper using regex above, leaving only what is left after label removed
    s = DOI_LABEL_RE.sub("", s).strip() # Strip leading label using regex above, leaving only what is left after label removed
    s = s.rstrip(".") # Strip trailing period that is not actually part of the doi itself but often present
    if s.lower().startswith("10.") and "/" in s: # If in doi format (10.xxxx/xxxx), return lowercased doi string and False for malformed - valid format
        return s.lower(), False
    return None, True # If not in doi format (10.xxxx/xxxx), return None and True for malformed - invalid format

# This URL identifier is used for citations (e.g., guideline pages or society sites) that were not indexed to pubmed or have a doi
# Returns a tuple containing a cleaned url string (or None) and a boolean value indicating whether the url is malformed (True) or not (False)
# Only urls in the format "http(s)://xxxx" are considered a usable ID; anything else that is present but not in that format considered malformed
# (as below, missing or blank string urls are not considered malformed)
def normalize_url(raw):
    if raw is None:
        return None, False
    s = str(raw).strip()
    if not s:
        return None, False
    if s.lower().startswith("http://") or s.lower().startswith("https://"): # If in url format (http(s)://xxxx), return url string and False for malformed - valid format
        return s, False
    return None, True # Otherwise, return None and True for malformed - invalid format


def extract_entries(data):
    # Extracts list of citations from the JSON file, since the input JSON can be in multiple shapes described below
    # Returns a tuple (entries, skipped counts)) where skipped count is the number items skipped because
    # they weren't dicts (see comment on branch 3 below for why this matters). Skipped counts are reported in main() instead of happening invisibly
    if isinstance(data, list):
        # A list of entry dicts (e.g, [{"pmid": "12345", "title": "Some Paper"}, ...]). Use this list directly
        # Drop and count anything not a dict - e.g., a stray string/number/null so that 
        # the the rest of the entries can be processed without crashing when .get() is called in main() on every entry()
        entries = [e for e in data if isinstance(e, dict)]
        return entries, len(data) - len(entries)
    if isinstance(data, dict):
        if data and all(isinstance(v, dict) for v in data.values()):
            # A dict whose values are all entry dicts (e.g., {"entry1": {"pmid": "12345", "title": "Some Paper"}, "entry2": {...}, ...})
            # Checking "all" tells this shape apart from the real bibliography's wrapper below
            # This check has to stay strict so that a metadata-heavy wrapper doesn't get misread as a dict of entries
            # Nothing skipped since everything is already in dict form
            return list(data.values()), 0  # CHANGED: was `return list(data.values()), ` - a dangling comma with nothing after it, which builds a 1-element tuple instead of the 
            #(entries, skipped_count) pair every caller expects. Crashed with "not enough values to unpack" the 
            # moment this branch (dict-of-dicts input) was actually exercised
        for v in data.values():
            # A dict containing one list-of-dicts field (e.g. {"citations": [...]}), where the list contains entry dicts.
            # If not list of dicts, loop through each value in the dict to see if it meets the format of a dict containing one list of dicts field
            # Over half of the items in the list must be dicts to be considered a valid list of entries
            # This 50% threshold is arbitrary and intended to keep the script from accidentally rejecting an entire list if only a few of them are actually corrupted
            # Entries that do not meet criteria in the code branch are dropped and counted in the skipped count
            if isinstance(v, list) and v:
                dict_items = [e for e in v if isinstance(e, dict)]
                if len(dict_items) > len(v) / 2:
                    return dict_items, len(v) - len(dict_items)

    raise ValueError(
        "Unrecognized JSON structure: expected a list of reference objects, "
        "or a dict whose values are reference objects / contain such a list."
    ) 


def load_cache(path):
    # Cache is a flat dict keyed "pmid:<id>" / "doi:<id>" / "url:<id>" -> last-known lookup result
    if path.exists():
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_cache(path, cache):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(cache, f, indent=2)


def is_cache_stale(cache_entry, ttl_days):
    # Checks whether entry was cached greater than TTL (default is 28) days, is missing a timestamp or has an unparseable timestamp
    # If true, entry meets any of the above conditions and should be requeried
    checked_at = cache_entry.get("checked_at") # Get the timestamp of when the entry was last checked from the cache
    # If timestamp missing, return True
    if not checked_at:
        return True
    # Convert checked_at, a string, into a datetime object for comparison against "now"
    # Check if timestamp is parseable, if not return True. Catch ValueError exception if timestamp is unparseable to avoid crashing the script
    try:
        checked_dt = datetime.fromisoformat(checked_at)
    except ValueError:
        return True
    # Return True if difference between current UTC time and checked_at timestamp is greater than TTL days, otherwise return False and do not requery entry
    return (datetime.now(timezone.utc) - checked_dt) > timedelta(days=ttl_days)

# Crossref's abstract field, when supplied (often not), is usually wrapped in JATS XML tags
# e.g., <jats:sec><jats:title>Background</jats:title>Acne is common.</jats:sec><jats:sec><jats:title>Methods</jats:title>We reviewed studies.</jats:sec>
# This function strips those tags and returns the plain text using a regex similar to the normalize functions above
# Returns cleaned text or None if the input is None or empty
# Not a real XML parse as with PubMed abstracts, but will leave readable text in output field. Does not preserve structure of sections which is a limitation of this function
def strip_jats_tags(text):
    if not text:
        return None
    cleaned = JATS_TAG_RE.sub(" ", text) # Replace tag with whitespace to avoid concatenating words together that were separated by a tag
    cleaned = re.sub(r"\s+", " ", cleaned).strip() # Extra cleaning step to remove extra whitespace that may be left after stripping tags
    return cleaned or None

def infer_oxford_level(pubtypes):
    # Since no Oxford Centre for Evidence-Based Medicine Level (2011 Scale) can be directly extracted from an API, this is a heuristic grading system to estimate the level
    # Therefore, the results returned are NOT THE ACTUAL LEVELS
    # Actual levels depend on execution quality (e.g., blinding, allocation concealment, risk of bias, sample size) that cannot be captured by a PubMed tag
    # Based on evidence type, so the values returned often correspond to the pubtype tags in PubMed
    # Returns a tuple (level_or_None, note) which indicates (estimated Oxford level, note (always populated) 
    # explaining how the level was estimated or why it could not be estimated)
    # This level will be used in script 2 to determine which evidence to include in final JSON
    types = set(pubtypes or [])
    if not types:
        return None, "No PubMed publication-type data available to estimate from."
    if "Practice Guideline" in types or "Guideline" in types:
        # Guidelines synthesize evidence across many levels rather than sitting at one level
        # themselves - assigning a single Oxford grade to a guideline would misrepresent what
        # the classification means, so this deliberately returns no number rather than a guess
        return None, ("Guideline: Oxford Levels of Evidence doesn't directly grade guidelines "
                       "(they synthesize evidence across levels) -- check the guideline's own "
                       "evidence-grading system (e.g. GRADE) if it reports one.")
    if "Meta-Analysis" in types:
        return "1a", "Estimated from tag: Meta-Analysis (assumes meta-analysis of RCTs)."
    if "Systematic Review" in types and "Randomized Controlled Trial" in types:
        return "1a", "Estimated from tags: Systematic Review + Randomized Controlled Trial."
    if "Randomized Controlled Trial" in types:
        return "1b", "Estimated from tag: Randomized Controlled Trial."
    if "Systematic Review" in types:
        return "2a", ("Estimated from tag: Systematic Review, but PubMed's tag doesn't specify "
                       "the underlying study design -- treated conservatively as a review of "
                       "non-randomized studies.")
    if "Controlled Clinical Trial" in types:
        return "2b", "Estimated from tag: Controlled Clinical Trial (non-randomized)."
    if {"Comparative Study", "Observational Study", "Multicenter Study"} & types:
        return "2b", "Estimated from tag: observational/comparative study design."
    if "Case Reports" in types:
        return "4", "Estimated from tag: Case Reports."
    if "Review" in types:
        return None, "Narrative review (tag: Review) -- not a systematically graded evidence level."
    return None, f"No heuristic mapping defined for PubMed publication type(s): {sorted(types)}."


def compute_evidence_rating(is_guideline, oxford_level, is_low_quality, integrity_flags):
    # Locally-defined ranking for sorting and analysis purposes
    # Combines fields computed above: is_guideline, oxford_level_of_evidence_estimate, is_low_quality_evidence_type, 
    # pubmed_integrity_flags into one ordered field
    # Guidelines ranked highest and receives lowest number rank of 1, followed by lower-quality evidence types
    # Then finally retracted/withdrawn sources are ranked lowest and receive the highest number rank of 9
    # Returns a tuple (label, rank) where label is the evidence type and rank is the priority ranking
    # If none of the below conditions are met, return "Unrated -- no usable publication-type data" and rank of 8
    if integrity_flags:
        return "Retracted or withdrawn", 9
    if is_guideline:
        return "Guideline", 1
    if oxford_level == "1a":
        return "Meta-Analysis / Systematic Review of RCTs (Oxford ~1a)", 2
    if oxford_level == "1b":
        return "Randomized Controlled Trial (Oxford ~1b)", 3
    if oxford_level == "2a":
        return "Systematic Review, underlying design unspecified (Oxford ~2a)", 4
    if oxford_level == "2b":
        return "Controlled/Observational/Comparative Study (Oxford ~2b)", 5
    if oxford_level == "4":
        return "Case Reports (Oxford ~4)", 6
    if is_low_quality:
        return "Low-quality evidence type (opinion/narrative/preliminary/consensus)", 7
    return "Unrated -- no usable publication-type data", 8


def fetch_pubmed_batch(pmids, email, session):
    # Fetches metadata for a batch of PMIDs from PubMed. Returns {pmid: {exists, title, authors, year, pubtype, raw_record}}
    # Session is a requests.Session() object, therefore reusing one session across multiple requests
    params = { # Parameters for NCBI's esummary endpoint
        "db": "pubmed", # Database to search
        "id": ",".join(pmids), # Comma-joined list of PMIDs to fetch (up to PUBMED_BATCH_SIZE, default is 200)
        # joined into a single string and sent as a single request
        "retmode": "json", # Returns results in JSON format
        "email": email, # Requires email per NCBI's policy
        "tool": "reference-existence-checker", # Polite-usage identifier
    }
    last_error = None # Keeps track of last error during request; initialize to None
    for attempt in range(1, MAX_RETRIES + 1): # Attempt to fetch the batch up to MAX_RETRIES times (default is 3)
        try:
            resp = session.get(PUBMED_ESUMMARY_URL, params=params, timeout=30)
            if resp.status_code == 200: # If request successful (200), parse the JSON response and extract metadata for each PMID
                result = resp.json().get("result", {})
                uids = result.get("uids", []) # Get the list of UIDs from result object above
                # UIDs are the PMIDs that were actually found in PubMed
                found = {} # Create dictionary to store metadata for each PMID
                for pmid in pmids: # Loops over every requested PMID in the batch, even if it wasn't found in PubMed
                    # to ensure every requested PMID is represented in the output
                    record = result.get(pmid)
                    if pmid in uids and record is not None and "error" not in record:
                        # If the PMID was found in PubMed and the record is valid (not None and no error), 
                        # extract metadata fields and store in found dictionary
                        found[pmid] = {
                            "exists": True,
                            "title": record.get("title", "").strip(),
                            "authors": [a.get("name", "") for a in record.get("authors", [])],
                            "year": record.get("pubdate", "").split()[0] if record.get("pubdate") else None,
                            "pubtype": record.get("pubtype", []),
                            "raw_record": record, # Store entire record in case needed later
                        }
                    else:
                        found[pmid] = {"exists": False, "title": None, "authors": [], "year": None, "pubtype": [], "raw_record": None}
                return found # Return dictionary of metadata for each PMID in the batch
            last_error = f"HTTP {resp.status_code}"
        except requests.RequestException as exc:
            last_error = str(exc)
        time.sleep(RETRY_BACKOFF * attempt) # Wait this amount of time before retry attempt (default is 2 seconds * attempt number)
    raise RuntimeError(f"PubMed batch lookup failed after {MAX_RETRIES} attempts: {last_error}")


def fetch_pubmed_abstracts_batch(pmids, email, session):
    # Esummary (used in the fetch_pubmed_batch function above)
    # doesn't include abstract text - must call efetch endpoint
    # Batched the same way as esummary (comma-joined ids, same batch size),
    # but is a separate request to a separate endpoint that returns XML instead of JSON
    # Returns a dictionary of {pmid: abstract_text_or_None} for each PMID in the batch
    params = {
        "db": "pubmed",
        "id": ",".join(pmids),
        "rettype": "abstract", # Tells efetch to return abstract-formatted view of the record
        # instead of other options, like full citation
        "retmode": "xml", # Returns results in XML format
        # JSON return not available; parse XML in _parse_efetch_abstracts below
        "email": email,
        "tool": "reference-existence-checker",
    }
    last_error = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            resp = session.get(PUBMED_EFETCH_URL, params=params, timeout=60)
            # Timeout 60s rather than 30 since abstract text is much larger response body than summaries above
            if resp.status_code == 200:
                return _parse_efetch_abstracts(resp.text, pmids) # resp.text for raw XML string, not JSON
            last_error = f"HTTP {resp.status_code}"
        except requests.RequestException as exc:
            last_error = str(exc)
        except ET.ParseError as exc:
            last_error = f"XML parse error: {exc}" # If XML is malformed/truncated, catches error
        time.sleep(RETRY_BACKOFF * attempt)
    raise RuntimeError(f"PubMed abstract fetch failed after {MAX_RETRIES} attempts: {last_error}")


def _parse_efetch_abstracts(xml_text, requested_pmids):
    # Parses XML response from efetch - esummary doesn't include abstract text, efetch only returns XML, not JSON
    # Matches results back to pmids by reading each article's pmid individually rather than
    # assuming response order matches request order
    # Preserves structure of abstracts with section labels (e.g., background, methods, etc.)
    # Note: this function is only ever called by the above function fetch_pubmed_abstracts_batch
    # which handles the request and error handling
    root = ET.fromstring(xml_text) # Parse XML string into ElementTree object that is searched/navigated below
    results = {p: None for p in requested_pmids} # Pre-fill output dict with None
    # Guarantees something is always returned for every PMID requested
    # This prevents a pmid from being silently absent in result dict
    for article in root.findall(".//PubmedArticle"): # Search entire XML tree for every pubmed element at any depth
        # Processes each article one at a time
        # There is one article per PMID requested
        pmid_el = article.find(".//MedlineCitation/PMID")
        # For each article, find the PMID element in the XML tree and extract its text
        # This prevents assuming the order of articles in the XML matches the order of requested PMIDs
        # which could lead to mismatched abstracts if the order is different
        if pmid_el is None or pmid_el.text not in results: 
            # Skip article if no pmid element found
            # or if the pmid is not in the requested list
            continue
        parts = [] # Initialize list to hold abstract text parts for this article
        for abst in article.findall(".//Abstract/AbstractText"):
            # For each article, find all abstract text elements in the XML tree
            # Can be multiple per pmid if the abstract is structured with section labels (e.g., background, methods, results)
            label = abst.get("Label") # Read label attribute of specific abstract text tag
            # Return None if no label attribute
            text = "".join(abst.itertext()).strip()
            # Iterate over abstract element and sub elements' text content
            # Extract all text content from these elements, joining into a single string and trimming surrounding whitespace
            if not text: # Skip empty abstract text elements -- don't add blank entry to parts []
                continue
            parts.append(f"{label}: {text}" if label else text)
            # If label exists, prepend it to the text with a colon and space separator
        if parts: # Join arcticle's abstract parts into a single string with newlines separating each part
            results[pmid_el.text] = "\n".join(parts)
    return results # Return dictionary of {pmid: abstract_text_or_None} for each PMID requested


def fetch_crossref_doi(doi, email, session):
# Fetch metadata for a DOI from CrossRef. Returns {exists, title, authors, year, abstract, raw_record}
# Where logic is similar to fetch_pubmed_batch, not commented in detail
    url = CROSSREF_WORKS_URL.format(doi=doi) # Format the CrossRef API URL with the DOI
    last_error = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            resp = session.get(url, params={"mailto": email}, timeout=30)
            if resp.status_code == 200:
                data = resp.json().get("message", {})
                return {
                    "exists": True,
                    "title": data.get("title", [""])[0] if data.get("title") else None,
                    "authors": [author.get("family", "") for author in data.get("author", [])],
                    "year": data.get("published-online", {}).get("date-parts", [[None]])[0][0]
                    or data.get("published", {}).get("date-parts", [[None]])[0][0],
                    # Two different date fields used for different formats of CrossRef records, so check both
                    "abstract": strip_jats_tags(data.get("abstract")),
                    "raw_record": data,
                }
            if resp.status_code == 404:
                return {"exists": False, "title": None, "authors": [], "year": None, "abstract": None, "raw_record": None}
            last_error = f"HTTP {resp.status_code}"
        except requests.RequestException as exc:
            last_error = str(exc)
        time.sleep(RETRY_BACKOFF * attempt)
    raise RuntimeError(f"CrossRef lookup failed after {MAX_RETRIES} attempts: {last_error}")


def fetch_url_exists(url, session):
# Checks whether a url resolves
# Returns {exists, title: None, authors: [], year: None}
# URLs carry no bibliographic metadata, so they only ever contribute 
# an existence signal, never a metadata comparison
    headers = {"User-Agent": "Mozilla/5.0 (reference-existence-checker)"}
    # Use a user-agent header to avoid being blocked by some sites that reject requests with no user-agent
    # Use conventional Mozilla user-agent string to avoid being blocked by sites that reject non-browser user-agents
    last_error = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            resp = session.get(url, headers=headers, timeout=20, allow_redirects=True, stream=True)
            # stream=True ensures that only status line and headers come back immediately,
            # not the entire response body (can be very large), increasing efficiency 
            status = resp.status_code # Store HTTP status code for conditional checks below
            resp.close() # Close response after stream=True
            if status in (404, 410): # 404 not found and 410 gone are treated as non-existent
                return {"exists": False, "title": None, "authors": [], "year": None, "raw_record": None}
            if status == 403 or status < 400: # 403 forbidden and any 1xx/2xx/3xx status is treated as existing
                return {"exists": True, "title": None, "authors": [], "year": None, "raw_record": None}
            last_error = f"HTTP {status}"
        except requests.RequestException as exc:
            last_error = str(exc)
        time.sleep(RETRY_BACKOFF * attempt)
    raise RuntimeError(f"URL check failed after {MAX_RETRIES} attempts: {last_error}")


# CHANGED: helper for the word-order check in titles_match below
# Very common connecting words are ignored; numbers are kept, since they often distinguish
# documents (e.g. "Guideline No. 5" vs "Guideline No. 6")
_TITLE_FILLER_WORDS = {"and", "of", "the", "for", "a", "an", "in", "on", "to", "with", "from", "by", "no"}


def _title_words(title):
    return {w for w in re.findall(r"[a-z0-9]+", title.lower()) if w not in _TITLE_FILLER_WORDS}


def titles_match(title_a, title_b, similarity_threshold=0.85, min_containment_len=12, min_words_for_reorder=4):
    # Return True if lowercased/stripped titles close enough to be the same word
    # Note: given that some titles are truncated in CrossRef, accept a match when
    # the shorter title is a clean substring of the longer one as well
    if not title_a or not title_b:
        return False
    if difflib.SequenceMatcher(None, title_a, title_b).ratio() > similarity_threshold:
        return True
    # Strip trailing periods from both titles before checking substrings
    shorter, longer = sorted((title_a.rstrip("."), title_b.rstrip(".")), key=len)
    if len(shorter) >= min_containment_len and shorter in longer:
        return True
    # Accepts titles made of exactly the same words in a different order
    # PubMed and CrossRef sometimes reorder a title, e.g. "Treatment of X: ACOG Guideline No. 5"
    # vs "ACOG Guideline No. 5: Treatment of X". Character similarity drops below the bar when a
    # chunk moves, which produced a false PMID/DOI mismatch. Requires the SAME set of words (not
    # just overlap) and at least min_words_for_reorder of them, so different documents still differ
    words_a, words_b = _title_words(title_a), _title_words(title_b)
    if len(words_a) >= min_words_for_reorder and words_a == words_b:
        return True
    return False


def compare_metadata(entry_title, entry_authors, entry_year, api_record):
    # Compares what the citing entry CLAIMS (title/authors/year) against what the API actually
    # returned for the id it supplied, to catch "id is real but doesn't back up this citation."
    if not api_record: # If no API record was returned, mark for manual review rather than assuming a mismatch
        return "inconclusive"

    api_title = (api_record.get("title") or "").lower().strip()
    entry_title_lower = str(entry_title or "").lower().strip()

    if entry_title_lower and api_title and not titles_match(entry_title_lower, api_title):
        return "mismatch"

    entry_year_str = str(entry_year or "").strip()
    api_year_str = str(api_record.get("year") or "").strip()
    if entry_year_str and api_year_str and entry_year_str != api_year_str:
        # Tolerates a one-year difference between entry year and API year
        # This is common in real bibliographic data due to print vs epub-ahead-of-print year differences
        try:
            year_diff = abs(int(entry_year_str[:4]) - int(api_year_str[:4]))
        except ValueError:
            year_diff = None  # Refers to non-numeric year strings - fall back to treating any difference as a mismatch
        if year_diff is None or year_diff > 1:
            return "mismatch"

    # Institutional guidelines are often recorded with the issuing body's name as the author(s)
    # (e.g. "AACE", "WHO", "American College of Rheumatology") instead of named individuals.
    # An org name/acronym will never match a real per-person author list from PubMed/CrossRef,
    # so detect an institutional attribution and skip the author check rather than false-flag it
    _ORG_KEYWORDS = (
        "society", "association", "college", "academy", "committee", "institute",
        "foundation", "organization", "organisation", "group", "council", "center",
        "centers", "centre", "federation", "alliance", "network", "board", "program",
        "programme", "consortium", "panel", "task force", "collaborative", "coalition",
    )

    def _looks_institutional(author):
    # Nested helper function, only called within compare_metadata()
    # Determines whether author appears to be an institutional author (org name or acronyn)
    # Avoids these being incorrectly flagged as a mismatch
        s = str(author).strip()
        if not s: 
            return False
        # If author string is empty, return False and skip the author checks below
        # Note: this only catches empty strings or pure whitespace, but
        # it does not catch None because this code produces "None" instead of an empty string
        # This will cause these entries to fall through past this check, though None in an authors list would be unusual
        # so potentially not an issue, but worth noting
        stripped = s.replace("-", "").replace(" ", "")
        is_acronym = s == s.upper() and stripped.isalpha()
        # If author string is all uppercase and contains only letters
        # after being stripped of spaces hyphens, considered a plausible acronym for an organization
        has_org_keyword = any(kw in s.lower() for kw in _ORG_KEYWORDS)
        # Returns True if any of the org keywords above are found in the author string (case-insensitive)
        return is_acronym or has_org_keyword

    entry_authors_list = [a for a in (entry_authors or []) if str(a).strip()]
    # Note: entry is treated as institutional only if every listed
    # author looks institutional -- a mix of one real name and one org name should still be
    # author-checked
    is_institutional_author = bool(entry_authors_list) and all(_looks_institutional(a) for a in entry_authors_list)
    # If entry_authors_list is empty, it is false, which provides a guard against
    # the right side of the boolean expression being evaluated as an empty list
    # which would be evaluated as vacuously true and incorrectly mark the entry as institutional
    if not is_institutional_author:
        # If institutional entry, skip this block
        # This is because institutional entries have no per-person name to compare, so
        # attempting the match would always "fail" and wrongly flag a genuine, title-confirmed source as a mismatch
        # The right side of the boolean expression returns True only if ALL authors in the entry's author list
        # look like institutional names - if any look like a real person's name, the entry is treated as non-institutional
        entry_authors_lower = [str(a).lower().split()[0] for a in (entry_authors or []) if str(a).strip()]
        # Build a list of names from the entry's authors, lowercased and split on whitespace to get the first token
        # This token is usually the last name per pubmed's format
        api_authors = api_record.get("authors", []) or []
        # Same action as above except for the API's author list
        api_authors_lower = [str(a).lower().split()[0] for a in api_authors if str(a).strip()]

        if entry_authors_lower and api_authors_lower:
            # If both entry and API lists are not empty, check for any match between the two lists
            # This code takes care not to confuse not having author info to compare with authors not matching
            has_author_match = any(a in api_authors_lower for a in entry_authors_lower)
            if not has_author_match:
                return "mismatch"

    return "match"
    # If all checks passed, this means one of the following:
    # Entry was institutional
    # Authors matched between entry and API
    # One or both sides had no authors to compare at all


def resolve_entry_verdict(entry, ids_present, cache):
    # Determine a single entry's verdict from however many identifiers (pmid/doi/url) it carries
    if not ids_present: # If no pmid, doi, or url is present in the entry, return "invalid_no_id"
        return "invalid_no_id"

    statuses = []  # (id_type, id_value, status, cached_record)
    # List has one tuple per identifier present in the entry, 
    # with the status of that identifier and its cached record (if any)
    for id_type, id_value in ids_present:
        cached = cache.get(f"{id_type}:{id_value}")
        if not cached: # If record not in cache, mark as UNVERIFIED,
            # NOT missing since the entry may be valid but just was not able to be checked due to
            # network issues, API downtime, etc
            # To be manually checked later
            statuses.append((id_type, id_value, "UNVERIFIED", None))
        elif not cached.get("exists"): # If record in cache but cache "exists" field
            # is False, mark as hallucinated (the id resolves to nothing)
            statuses.append((id_type, id_value, "hallucinated", cached))
        else:
            statuses.append((id_type, id_value, "found", cached))

    # Return verdicts based on above statuses
    # Note: unverified is checked first because if an entry has both an
    # id marked as UNVERIFIED and one as hallucinated,
    # UNVERIFIED takes precedence since it is a more conservative verdict
    if any(s == "UNVERIFIED" for _, _, s, _ in statuses):
        return "UNVERIFIED"
    if any(s == "hallucinated" for _, _, s, _ in statuses):
        return "invalid_hallucinated"

    # If PMID and DOI are both present, check whether they resolve to the same metadata (title/authors/year)
    # URL not compared since line below gets the title from the cached response
    # which returns None for url-only entries
    titled = [c for _, _, _, c in statuses if c and c.get("title")]
    if len(titled) >= 2:
        # If two or more resolved sources carry a title (in practice, PMID and DOI), compare them
        base_title = titled[0]["title"].lower().strip()
        # Compare the first title titled[0] against the titles 
        # in the rest of the list titled[1:]
        for other in titled[1:]:
            other_title = (other.get("title") or "").lower().strip()
            if base_title and other_title and not titles_match(base_title, other_title):
                # If two or more resolved sources carry a title (in practice, pmid and doi),
                # but their titles do not match, return "invalid_pmid_doi_mismatch"
                return "invalid_pmid_doi_mismatch"

    reference_record = titled[0] if titled else None
    # Compares entry's own claimed title/authors/year against one source record:
    # PubMed record if the entry has a PMID (ids_present lists PMID first, see main())
    # otherwise the DOI. URL records have no title, so they're no used here
    # If the claim doesn't match that record, the whole entry is invalid_hallucinated
    # Disagreement between a PMID and a DOI is caught separately by the cross-title check above
    # None (no titled record, e.g., url only) -> compare_metadata returns "inconclusive" -> stays valid

    comparison = compare_metadata(entry.get("title"), entry.get("authors"), entry.get("year"), reference_record)
    if comparison == "mismatch":
        return "invalid_hallucinated"
    return "valid" 
    # Includes conditions where comparison is "match" or "inconclusive" (no metadata to compare)
    # IMPORTANT note: for entries with url only, even if it resolves to a different
    # reference than the entry indicates, it always comes back VALID
    # because cannot check the metadata of a url-only entry

def attach_evidence_fields(entry, ids_present, cache):
    # Pulls the abstract / PubMed publication-type tags / heuristic Oxford Level of
    # Evidence estimate / is_guideline flag / retraction-or-correction flags onto the entry from
    # whichever cached id record has them
    # PMID is preferred when present, since efetch gives real
    # publication-type tags plus the full abstract text
    # DOI (CrossRef) is a lower-quality fallback
    # CrossRef only sometimes carries an abstract, and never a study-design classification, so
    # entries resolved only via DOI get an abstract at best and no Oxford estimate, guideline flag,
    # or integrity flag. A url-only entry gets none of this, since fetch_url_exists only ever
    # returns an existence signal, no metadata

    # Loop through pmid and doi and store the pmid and doi cached records in two separate variables
    pmid_cached = None
    doi_cached = None
    for id_type, id_value in ids_present:
        if id_type == "pmid":
            pmid_cached = cache.get(f"pmid:{id_value}")

        elif id_type == "doi":
            doi_cached = cache.get(f"doi:{id_value}")

    # If a pmid is present and exists (not hallucinated), use its cached record to populate the evidence fields
    # Use pmid first because it has the most complete metadata (abstract, pubtypes, etc.) compared to doi or url
    if pmid_cached and pmid_cached.get("exists"):
        pubtypes = pmid_cached.get("pubtype", [])
        entry["_abstract"] = pmid_cached.get("abstract")
        entry["_pubmed_pubtypes"] = pubtypes
        entry["_oxford_level_of_evidence_estimate"] = pmid_cached.get("oxford_level_of_evidence_estimate")
        entry["_oxford_level_of_evidence_note"] = pmid_cached.get("oxford_level_of_evidence_note")
        # Is_guideline and integrity flags are separate from the Oxford estimate on purpose
        # "this is a guideline" and "the Oxford scale doesn't grade guidelines numerically"
        # are two different facts, and collapsing them into one field would lose one of them
        entry["_is_guideline"] = bool(GUIDELINE_PUBTYPES & set(pubtypes))
        # Create boolean field indicating whether the entry is a guideline based on its pubtype
        entry["_pubmed_integrity_flags"] = [t for t in pubtypes if t in INTEGRITY_PUBTYPES]
        # Create a list of integrity flags based on whether pubtype is in the INTEGRITY_PUBTYPES set
        # e.g., retracted publications, retraction notices, expressions of concern, corrected/republished articles
        entry["_low_quality_evidence_reasons"] = [t for t in pubtypes if t in LOW_QUALITY_EVIDENCE_PUBTYPES]
        # Create list of low-quality evidence reasons based on whether pubtype is in the LOW_QUALITY_EVIDENCE_PUBTYPES set 
        # (e.g., opinion, narrative, preliminary, consensus)
        entry["_is_low_quality_evidence_type"] = bool(entry["_low_quality_evidence_reasons"])
    elif doi_cached and doi_cached.get("exists"):
        # if pmid not usable, doi is next best, but has no pubtype/guideline/retraction classification at all
        # so Oxford estimate and guideline flag can't be derived from it
        # Store these fields as None/empty rather than a guess
        entry["_abstract"] = doi_cached.get("abstract")
        entry["_pubmed_pubtypes"] = []
        entry["_oxford_level_of_evidence_estimate"] = None
        entry["_oxford_level_of_evidence_note"] = (
            "No PubMed publication-type data -- entry has no PMID "
            "(CrossRef doesn't classify study design)."
        )
        entry["_is_guideline"] = None
        entry["_pubmed_integrity_flags"] = []
        entry["_is_low_quality_evidence_type"] = None
        entry["_low_quality_evidence_reasons"] = []
    else: # If neither pmid nor doi resolved, set all evidence fields to None/empty
        # This is the case for url-only entries or entries with no ids, hallucinated verdicts, or were UNVERIFIED (not in cache)
        # This is another limitation of url-only entries, since they can resolve to a real page but
        # that may actually be a real publication but this program does not currently check whether that is valid
        entry["_abstract"] = None
        entry["_pubmed_pubtypes"] = []
        entry["_oxford_level_of_evidence_estimate"] = None
        entry["_oxford_level_of_evidence_note"] = "No resolved PMID/DOI record available to derive evidence fields from."
        entry["_is_guideline"] = None
        entry["_pubmed_integrity_flags"] = []
        entry["_is_low_quality_evidence_type"] = None
        entry["_low_quality_evidence_reasons"] = []

    # Produces a final evidence ranking for the entry, based on the cached metadata of whichever identifier(s) it carries
    rating_label, rating_rank = compute_evidence_rating(
        entry["_is_guideline"],
        entry["_oxford_level_of_evidence_estimate"],
        entry["_is_low_quality_evidence_type"],
        entry["_pubmed_integrity_flags"],
    )
    entry["_evidence_rating_overall"] = rating_label
    entry["_evidence_rating_rank"] = rating_rank


def load_previous_verdicts(output_path):
    # Used for purposes of monthly re-run
    # Reads whatever the script wrote last time it ran (last month or whatever specified on command line argument)
    # Output file specified by output_path argument, or default <input>.checked.json
    if not output_path.exists():
        # If output file doesn't exist (e.g., first run, error in previous run), then return empty dict
        return {}
    try:
        with open(output_path, "r", encoding="utf-8") as f:
            prev_data = json.load(f)
        prev_entries, _ = extract_entries(prev_data)  # skip count not needed here -- already reported when that run happened
    except (ValueError, OSError, json.JSONDecodeError):
        # Catches errors in parsing JSON, value errors (if data structure does not match expected; see extract_entries)
        # or OS errors (e.g., file not found, permission denied)
        return {} # If any error occurs while reading the previous output file, return empty dict
    
    previous = {}
    for e in prev_entries:
        # Loop through each entry in the previous run's output and extract its id and verdict
        entry_id = e.get("id")
        verdict = e.get("_tier1_existence")
        if entry_id and verdict:
            # If no id on entry, skip it -- can't track drift without a stable identifier
            # If no verdict on entry, skip it -- can't track drift without a previous verdict to compare against
            previous[entry_id] = verdict
    return previous


# CHANGED: audit CSV -- a readable, one-row-per-reference record of this run's results for
# review and MD/CTO sign-off. Not read by any script; sort_guidelines.py still reads the JSON

# Plain-language reason for each excluded verdict
EXCLUDED_REASONS = {
    "invalid_no_id": "no PMID, DOI, or URL to check",
    "invalid_hallucinated": "identifier points to no record (reference may not exist)",
    "invalid_pmid_doi_mismatch": "PMID and DOI point to different papers",
    "UNVERIFIED": "could not be checked (lookup failed or site blocked); retried next run",
}
RETRACTION_PUBTYPES = {"Retracted Publication", "Retraction Notice"}
# No Tier 2 (claim-support) column: claims will be matched to references in a separate process
ID_YEAR_RE = re.compile(r"(?<!\d)(19[5-9]\d|20[0-2]\d)(?!\d)")  # a 4-digit year 1950-2029 in an id

AUDIT_CSV_COLUMNS = [
    "id", "title", "year", "ids_checked",
    "tier1_verdict", "evidence_type", "evidence_level",
    "excluded", "excluded_reason", "changed", "changed_from_to", "retracted_withdrawn",
    "flagged_for_manual_review", "manual_review_reasons", "abstract",
    "run_id", "row_hash", "md_cto_signoff_name", "md_cto_signoff_date",
]
# Columns left out of the row hash: the hash itself, and the sign-off columns filled in by hand afterward
UNHASHED_COLUMNS = {"row_hash", "md_cto_signoff_name", "md_cto_signoff_date"}


def id_year_mismatch(entry):
    # Returns the year in the id if it differs from the entry's year by more than 1 (e.g. IDSA2024cUTI
    # attached to a 2011 document), else None. The id names what the protocol author meant to cite,
    # so a big gap often means an older edition or the wrong document is attached
    id_years = ID_YEAR_RE.findall(str(entry.get("id") or ""))
    year = entry.get("year")
    if len(id_years) != 1 or not isinstance(year, int):
        return None
    id_year = int(id_years[0])
    return id_year if abs(id_year - year) > 1 else None


def audit_row(entry, run_id, has_previous_run):
    verdict = entry.get("_tier1_existence")
    integrity_flags = entry.get("_pubmed_integrity_flags") or []
    previous = entry.get("_tier1_previous_existence")
    changed = bool(entry.get("_tier1_existence_changed"))

    # Excluded = what sort_guidelines.py drops before sorting: any non-valid verdict, or a
    # retraction/integrity notice even when the verdict is valid
    excluded_reason = EXCLUDED_REASONS.get(verdict, "")
    if verdict == "valid" and integrity_flags:
        excluded_reason = "PubMed integrity notice: " + ", ".join(integrity_flags)

    # Flagged = a person should look at it this run
    review_reasons = []
    if verdict == "UNVERIFIED":
        review_reasons.append("could not be verified")
    if verdict == "invalid_pmid_doi_mismatch":
        review_reasons.append("PMID/DOI mismatch")
    if integrity_flags:
        review_reasons.append("integrity notice: " + ", ".join(integrity_flags))
    if changed:
        review_reasons.append(f"verdict changed since last run ({previous} -> {verdict})")
    mismatch_year = id_year_mismatch(entry)
    if mismatch_year:
        review_reasons.append(f"id says {mismatch_year} but document is {entry.get('year')} (possible wrong or older document)")

    if changed:
        changed_from_to = f"{previous} -> {verdict}"
    elif not has_previous_run or previous is None:
        changed_from_to = "no previous run to compare"
    else:
        changed_from_to = ""

    row = {
        "id": entry.get("id") or "",
        "title": entry.get("title") or "",
        "year": entry.get("year") or "",
        "ids_checked": ", ".join(entry.get("_tier1_ids_checked") or []),
        "tier1_verdict": verdict or "",
        "evidence_type": entry.get("_evidence_rating_overall") or "",
        "evidence_level": entry.get("_oxford_level_of_evidence_estimate") or "Unrated",
        "excluded": "Y" if excluded_reason else "N",
        "excluded_reason": excluded_reason,
        "changed": "Y" if changed else "N",
        "changed_from_to": changed_from_to,
        "retracted_withdrawn": "Y" if RETRACTION_PUBTYPES & set(integrity_flags) else "N",
        "flagged_for_manual_review": "Y" if review_reasons else "N",
        "manual_review_reasons": "; ".join(review_reasons),
        "abstract": entry.get("_abstract") or "",
        "run_id": run_id,
        "row_hash": "",
        "md_cto_signoff_name": "",
        "md_cto_signoff_date": "",
    }
    # SHA-256 fingerprint of the row's contents: if any value is edited after the run, recomputing
    # the hash will no longer match. Sign-off columns are left out so filling them in doesn't break it
    hashed = [str(row[c]) for c in AUDIT_CSV_COLUMNS if c not in UNHASHED_COLUMNS]
    row["row_hash"] = hashlib.sha256(json.dumps(hashed, ensure_ascii=False).encode("utf-8")).hexdigest()
    return row


def write_audit_csv(entries, csv_path, run_id, has_previous_run):
    # utf-8-sig so Excel opens accented characters and dashes correctly
    with open(csv_path, "w", encoding="utf-8-sig", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=AUDIT_CSV_COLUMNS)
        writer.writeheader()
        for entry in entries:
            writer.writerow(audit_row(entry, run_id, has_previous_run))


def main():
    # Command line parsing arguments
    parser = argparse.ArgumentParser(description="Tier 1 existence check for a references JSON file.")
    parser.add_argument("--input", required=True, help="Path to the references JSON file.")
    parser.add_argument("--output", help="Path to write the annotated JSON (default: <input>.checked.json).")
    parser.add_argument("--email", required=True, help="Contact email, required by NCBI/CrossRef usage policy.")
    parser.add_argument("--cache", default=".existence_cache.json", help="Path to the local cache file.")
    parser.add_argument("--limit", type=int, help="Only process the first N entries (for a quick test run).")
    # CHANGED: where to write the audit CSV
    parser.add_argument("--audit-csv", help="Path to write the audit CSV (default: <output>.audit.csv).")
    # Can override the default 28-day cache lifetime without editing the script with the number of days entered
    # e.g., --cache-ttl-days 0 to force a full re-check of everything on demand
    parser.add_argument("--cache-ttl-days", type=int, default=CACHE_TTL_DAYS,
                         help=f"Re-query a cached id if its last check is older than this many days (default: {CACHE_TTL_DAYS}).")
    args = parser.parse_args()

    # Convert input/output/cache paths to Path objects for easier manipulation
    input_path = Path(args.input)
    output_path = Path(args.output) if args.output else input_path.with_suffix(".checked.json")
    cache_path = Path(args.cache)
    # CHANGED: audit CSV path, and a run id that ties every CSV row to this run (UTC start time)
    audit_csv_path = Path(args.audit_csv) if args.audit_csv else output_path.with_suffix(".audit.csv")
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

    # Read output of last run (if any) before it is overwritten by this run
    # This way, it can be tagged in phase 5 below with whether its verdict changed since the last monthly check
    previous_verdicts = load_previous_verdicts(output_path)

    # Load new input JSON file
    try:
        with open(input_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"ERROR: input file not found: {input_path}")
        sys.exit(1)

    # Extract entries from the input JSON and apply any limit if specified
    # Include count of skipped items (non-dict entries) for logging and possible manual review purposes
    # See extract_entries function for details
    try:
        entries, skipped_count = extract_entries(data)
    except ValueError as exc:
        print(f"ERROR: {exc}")
        sys.exit(1)
    if args.limit:
        entries = entries[: args.limit]

    # Load the local cache of previously checked ids (pmid/doi/url) to avoid redundant API calls
    cache = load_cache(cache_path)
    # Load session for requests with a custom User-Agent header to comply with NCBI/CrossRef usage policies
    session = requests.Session()
    session.headers.update({"User-Agent": f"reference-existence-checker (mailto:{args.email})"})

    pmid_lookup = {} # Holds normalized pmids as keys and lists of entries that have that pmid as values 
    doi_lookup = {}  # Holds normalized dois as keys and lists of entries that have that doi as values
    url_lookup = {}  # Holds normalized urls as keys and lists of entries that have that url as values
    entry_ids = {} # keyed by Python's id(entry) (not the citation's own "id" field) -> [(id_type, id_value), ...]


    # Initialize counts for each verdict category
    counts = {
        "valid": 0,
        "invalid_no_id": 0,
        "invalid_pmid_doi_mismatch": 0,
        "invalid_hallucinated": 0,
        "UNVERIFIED": 0,
    }
    changed_entries = []  # (entry_id, previous_verdict, new_verdict) for entries whose status flipped

    # Store the current timestamp in ISO 8601 format for logging when each entry was checked
    now = lambda: datetime.now(timezone.utc).isoformat()

    # ========== PHASE 1: Normalize ids (pmid/doi/url), bucket for batch lookups ==========
    print("\n=== PHASE 1: Normalizing IDs ===")
    # In extract_entries when non-dict items are silently dropped from the output, they are
    # loudly announced here
    if skipped_count:
        print(f"  WARNING: skipped {skipped_count} item(s) in the input that weren't valid citation objects (not a dict) -- they were NOT checked and are NOT included in the counts below.")
    for entry in entries:
        pmid, _ = normalize_pmid(entry.get("pmid"))
        doi, _ = normalize_doi(entry.get("doi"))
        url, _ = normalize_url(entry.get("url"))

       # Stores the NORMALIZED id, not the raw input field - never read back elsewhere in this script,
       # but kept in the output so you can see exactly what was extracted from a messy raw pmid/doi/url,
       # and so it matches the exact string used to build cache keys (e.g. f"pmid:{entry['_pmid']}").
        entry["_pmid"] = pmid
        entry["_doi"] = doi
        entry["_url"] = url

        # Fields for further analysis (abstract, PubMed publication-type tags, and a
        # heuristic Oxford Level of Evidence estimate) are declared here, at the start, on every
        # entry - same pattern as the id/status fields below - so the output JSON's shape is
        # consistent even for entries where these end up staying None (e.g. no id, or a url-only
        # entry that was never going to have this data). Real values get filled in during
        # PHASE 5 by attach_evidence_fields, once the API responses are in
        entry["_abstract"] = None
        entry["_pubmed_pubtypes"] = []
        entry["_oxford_level_of_evidence_estimate"] = None
        entry["_oxford_level_of_evidence_note"] = None
        entry["_is_guideline"] = None
        entry["_pubmed_integrity_flags"] = None
        entry["_is_low_quality_evidence_type"] = None
        entry["_low_quality_evidence_reasons"] = None
        entry["_evidence_rating_overall"] = None
        entry["_evidence_rating_rank"] = None

        ids_present = []
        # Holds a list of tuples (id_type, id_value) for each identifier present in the entry
        # Fed into resolve_entry_verdict and attach_evidence_fields

        if pmid:
            # setdefault: if pmid already a key, reuse its list; otherwise create a new empty
            # list for it. Either way, append this entry - groups every entry sharing the same
            # pmid together, so PHASE 2 below only has to query PubMed once per distinct pmid
            pmid_lookup.setdefault(pmid, []).append(entry)
            ids_present.append(("pmid", pmid)) 
        if doi:
            # NOT elif - an entry can have pmid AND doi AND url all at once
            # Same logic as above for pmid_lookup, but for doi_lookup
            doi_lookup.setdefault(doi, []).append(entry)
            ids_present.append(("doi", doi))
        if url:
            url_lookup.setdefault(url, []).append(entry)
            ids_present.append(("url", url))


        entry_ids[id(entry)] = ids_present
        # Keyed by Python's id(entry) (object identity, not the citation's own "id" field)
        # lets PHASE 5 look this entry's ids_present back up later without recomputing it
        entry["_tier1_ids_checked"] = [t for t, _ in ids_present]
        # Human-readable summary for the output JSON: just the id TYPES (e.g. ["pmid", "doi"]),
        # not the actual values - unpacks each (id_type, id_value) tuple with `for t, _ in ...`,
        # discarding the value half

    print(f"  Entries with no id: {sum(1 for e in entries if not entry_ids[id(e)])}")
    print(f"  Distinct PMIDs to check: {len(pmid_lookup)}")
    print(f"  Distinct DOIs to check: {len(doi_lookup)}")
    print(f"  Distinct URLs to check: {len(url_lookup)}")

    # ========== PHASE 2: Query PubMed for PMIDs (batched) ==========
    print("\n=== PHASE 2: Querying PubMed ===")
    # Note: re-queries anything whose cached check has aged past --cache-ttl-days,
    # so that changes to previously cached results (e.g. a retraction notice added to a previously valid PMID)
    # will be picked up on the next run

    # Construct a list of PMIDs that either aren't in the cache or whose cached result is stale
    to_query_pmid = [ 
        p for p in pmid_lookup
        if f"pmid:{p}" not in cache or is_cache_stale(cache[f"pmid:{p}"], args.cache_ttl_days)
    ]
    print(f"PMIDs to check: {len(pmid_lookup)} ({len(pmid_lookup) - len(to_query_pmid)} cached, {len(to_query_pmid)} to query)")
    for i in range(0, len(to_query_pmid), PUBMED_BATCH_SIZE):
        batch = to_query_pmid[i : i + PUBMED_BATCH_SIZE]
        # Batch PMIDs into chunks of PUBMED_BATCH_SIZE (default 200) for the PubMed API call
        try:
            results = fetch_pubmed_batch(batch, args.email, session)
        except RuntimeError as exc:
            print(f"  WARNING: {exc} -- this batch will be retried on the next run.")
            time.sleep(PUBMED_DELAY)
            continue 
            # Note: the rest of the batch is skipped and not cached, and the next run's cache staleness run will
            # pick them back up and retry them
        time.sleep(PUBMED_DELAY)

        # Fetch abstracts for the same batch of PMIDs. Separate NCBI endpoint (efetch, not esummary)
        # Note: abstracts are fetched in the same batch as the esummary
        try:
            abstracts = fetch_pubmed_abstracts_batch(batch, args.email, session)
        except RuntimeError as exc:
            print(f"  WARNING: {exc} -- abstracts for this batch will be retried on a later run.")
            abstracts = {} # Unlike above, the rest of the batch is not skipped if error, just abstract: None
            # Since abstracts are not critical to the existence check, don't throw away the esummary data already fetched above
            # Will also be picked back up and retried by next run's cache staleness run
        time.sleep(PUBMED_DELAY)

        # Loop through the results of the PubMed batch query and store them in the cache
        for pmid, record_data in results.items():
            oxford_level, oxford_note = infer_oxford_level(record_data.get("pubtype"))
            cache[f"pmid:{pmid}"] = {
                "status": "found" if record_data["exists"] else "not_found",
                "exists": record_data["exists"],
                "title": record_data["title"],
                "authors": record_data["authors"],
                "year": record_data["year"],
                "pubtype": record_data.get("pubtype", []),
                "abstract": abstracts.get(pmid),
                "oxford_level_of_evidence_estimate": oxford_level,
                "oxford_level_of_evidence_note": oxford_note,
                "checked_at": now(),
            }

    # ========== PHASE 3: Query CrossRef for DOIs (one at a time) ==========
    print("\n=== PHASE 3: Querying CrossRef ===")
    # Same core logic as phase 2 but for dois
    # Queried one at a time since CrossRef does not have a batch API and
    # the rate limit is low enough that batching would not make much difference
    # Same staleness check as PHASE 2, applied to the doi cache
    to_query_doi = [
        d for d in doi_lookup
        if f"doi:{d}" not in cache or is_cache_stale(cache[f"doi:{d}"], args.cache_ttl_days)
    ]
    print(f"DOIs to check: {len(doi_lookup)} ({len(doi_lookup) - len(to_query_doi)} cached, {len(to_query_doi)} to query)")
    for doi in to_query_doi:
        try:
            record_data = fetch_crossref_doi(doi, args.email, session)
            cache[f"doi:{doi}"] = {
                "status": "found" if record_data["exists"] else "not_found",
                "exists": record_data["exists"],
                "title": record_data["title"],
                "authors": record_data["authors"],
                "year": record_data["year"],
                "abstract": record_data.get("abstract"),
                "checked_at": now(),
            }
        except RuntimeError as exc:
            print(f"  WARNING: {exc} for DOI {doi} -- will retry on next run.")
        time.sleep(CROSSREF_DELAY)

    # ========== PHASE 4: Check URLs (one at a time; no batch API exists for arbitrary URLs) ==========
    print("\n=== PHASE 4: Checking URLs ===")
    # Same core logic as phase 2 and 3 but for urls
    to_query_url = [
        u for u in url_lookup
        if f"url:{u}" not in cache or is_cache_stale(cache[f"url:{u}"], args.cache_ttl_days)
    ]
    print(f"URLs to check: {len(url_lookup)} ({len(url_lookup) - len(to_query_url)} cached, {len(to_query_url)} to query)")
    for url in to_query_url:
        try:
            record_data = fetch_url_exists(url, session)
            # None/blank metadata for fields with url only entries, since fetch_url_exists only returns an existence signal
            cache[f"url:{url}"] = {
                "status": "found" if record_data["exists"] else "not_found",
                "exists": record_data["exists"],
                "title": None,
                "authors": [],
                "year": None,
                "checked_at": now(),
            }
        except RuntimeError as exc:
            print(f"  WARNING: {exc} for URL {url} -- will retry on next run.")
        time.sleep(URL_DELAY)

    # ========== PHASE 5: Roll up a verdict per entry from whichever ids it carries ==========
    print("\n=== PHASE 5: Resolving verdicts ===")
    # Returns verdict for each entry based on the cached results of its identifiers (pmid/doi/url)

    # Loop through each entry and resolve its verdict
    for entry in entries:
        ids_present = entry_ids[id(entry)]
        verdict = resolve_entry_verdict(entry, ids_present, cache)
        entry["_tier1_existence"] = verdict
        entry["_tier1_checked_at"] = now()
        counts[verdict] += 1 
        # Increment the count for this verdict category, which will be used to report the summary at the end of the run

        # Fill in abstract / pubtypes / oxford heuristic estimate
        attach_evidence_fields(entry, ids_present, cache)  
        
        # Compare this entry's verdict against the previous run's verdict for the same entry
        entry_id = entry.get("id")
        previous_verdict = previous_verdicts.get(entry_id) if entry_id else None
        entry["_tier1_previous_existence"] = previous_verdict
        entry["_tier1_existence_changed"] = previous_verdict is not None and previous_verdict != verdict
        if entry["_tier1_existence_changed"]:
            changed_entries.append((entry_id, previous_verdict, verdict))

    # ========== PHASE 6: Save cache and output ==========
    print("\n=== PHASE 6: Saving results ===")
    save_cache(cache_path, cache)

    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

    # CHANGED: write the audit CSV (only the entries checked this run, so --limit runs list just those)
    write_audit_csv(entries, audit_csv_path, run_id, bool(previous_verdicts))

    # Collect every entry PubMed tagged with a retraction/correction notice
    # Printed first as this is a major patient safety signal
    integrity_hits = [
        (e.get("id"), e.get("_pubmed_integrity_flags"))
        for e in entries if e.get("_pubmed_integrity_flags")
    ]
    if integrity_hits:
        print()
        print("*" * 50)
        print(f"RETRACTION/CORRECTION NOTICES FOUND: {len(integrity_hits)}")
        print("*" * 50)
        for entry_id, flags in integrity_hits:
            print(f"  {entry_id}: {', '.join(flags)}")

    print()
    print("=" * 50)
    print("SUMMARY:")
    print("=" * 50)
    print(f"  valid: {counts['valid']}")
    print(f"  invalid_no_id: {counts['invalid_no_id']}")
    print(f"  invalid_pmid_doi_mismatch: {counts['invalid_pmid_doi_mismatch']}")
    print(f"  invalid_hallucinated: {counts['invalid_hallucinated']}")
    print(f"  UNVERIFIED: {counts['UNVERIFIED']}")
    print(f"Total: {sum(counts.values())}")

    # Surface month-over-month drift instead of leaving it buried in the output JSON
    if previous_verdicts:
        print()
        print(f"Changed since last run: {len(changed_entries)}")
        for entry_id, prev, new in changed_entries:
            print(f"  {entry_id}: {prev} -> {new}")
    else:
        print()
        print("No previous run found at the output path -- this is treated as a first run (no drift to report).")

    print(f"Output written to: {output_path}")
    print(f"Audit CSV written to: {audit_csv_path} (run id {run_id})")  # CHANGED
    print("=" * 50)


if __name__ == "__main__":
    main()
