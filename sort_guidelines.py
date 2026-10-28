import argparse
import csv
import json
import re
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path
import sys

from check_existence import titles_match

# ========== CONFIG (draft values -- confirm with a clinical reviewer before relying on these) ==========

# CERT-* specialty prefixes paired with years before a guideline is considered stale
# Specialty determines how quickly a guideline becomes outdated
# A citation tied to multiple specialties uses whichever applicable prefix that gives the
# shortest (most conservative) staleness window (see function pick_primary_specialty)
SPECIALTY_STALENESS_YEARS = {
    # Fast-moving
    "CERT-INF": 3, "CERT-GLP1": 3, "CERT-CV": 3, "CERT-BH": 3, "CERT-ENDO": 3,
    # Moderate
    "CERT-MSK": 4, "CERT-GI": 4, "CERT-RESP": 4, "CERT-RHEUM": 4, "CERT-RENAL": 4,
    "CERT-HEME": 4, "CERT-NEURO": 4, "CERT-GU": 4, "CERT-OB": 4, "CERT-GYN": 4,
    "CERT-EM": 4, "CERT-GERI": 4, "CERT-PEDS": 4, "CERT-PRIM": 4,
    # Slower-moving
    "CERT-DERM": 6, "CERT-ENT": 6, "CERT-EYE": 6, "CERT-TOX": 6, "CERT-ENVT": 6,
    "CERT-CONSTITUTIONAL": 6, "CERT-BURN": 6, "CERT-DENT": 6, "CERT-SLEEP": 6,
    "CERT-INTAKE": 6, "CERT-ANA": 6,
}
DEFAULT_STALENESS_YEARS = 5  # used only if a specialty prefix isn't in the table above

# Organization keywords recognized in the PubMed collective-author field as a second
# signal (alongside the pubtype tag) that a reference is really a guideline
# Not populated yet
GUIDELINE_ORG_KEYWORDS = {
    "AAFP", "AAP", "ACOG", "ACC", "AHA", "IDSA", "ACR", "AAOS", "ACG", "ADA",
    "AACE", "USPSTF", "WHO", "CDC", "ACP", "ATS", "ASCO", "NCCN",
}

# bibliography "type" values that count as a guideline
GUIDELINE_TYPE_LABELS = {"guideline", "clinical-guideline"}

# CHANGED: removed the fallback evidence cascade (EVIDENCE_CASCADE_TIERS) that suggested
# non-guideline studies as replacements for out-of-date guidelines. Suggestions were rarely
# on topic, and only guidelines and FDA documents are wanted in the output

# Fields check_existence.py adds on top of original bibliography schema
# Stripped back out before writing clean, re-uploadable output files
# These fields are used internally for tracking evidence and guideline status
# "_pubmed_corporate_author" is not added yet (held for a later change) but is
# listed here so stripping stays correct once it exists
DIAGNOSTIC_FIELDS = {
    "_pmid", "_doi", "_url", "_abstract", "_pubmed_pubtypes",
    "_oxford_level_of_evidence_estimate", "_oxford_level_of_evidence_note",
    "_is_guideline", "_pubmed_integrity_flags", "_is_low_quality_evidence_type",
    "_low_quality_evidence_reasons", "_evidence_rating_overall", "_evidence_rating_rank",
    "_tier1_ids_checked", "_tier1_existence", "_tier1_checked_at",
    "_tier1_previous_existence", "_tier1_existence_changed", "_pubmed_corporate_author",
}

CERT_PREFIX_RE = re.compile(r"^(CERT-[A-Z0-9]+)")

# ========== FDA TRACK CONFIG ==========
# FDA documents (labels, safety communications, REMS) skip guideline/specialty logic
# since they aren't research
# They track a drug rather than a specialty

# Only frozen FDA label PDFs (accessdata.fda.gov .../label/YYYY/...) get a year cutoff since they do not update on their own like DailyMed
# DailMed links always serve the current label, so no year cutoff is applied
FDA_FROZEN_LABEL_MAX_AGE_YEARS = 5

# Groups too varied to detect by pattern - explicit ids, reviewed and approved by the user
# Discovered through analysis completed prior to this program being written
FDA_SAFETY_COMMUNICATION_IDS = {
    "FDA2005AntipsychoticDementia", "FDA2007PDE5i", "FDA2007PDE5iSafety",
    "FDA2013ValproateBlackBox", "FDA2015SGLT2DKA", "FDA2017Codeine", "FDA2018Benzocaine",
    "FDA2020NSAID", "FDA2020_NSAIDs", "FDA2022JAKBlackBox", "FDA2022PulseOx",
    "FDA_FQ_BlackBox", "FDA_GLP1_Neuropsych_Surveillance",
}
FDA_REMS_IDS = {"Brodell2024iPLEDGE", "FDA_ClozapineREMS"}

# FDA-related entries previously reviewed and deliberately left out, so the new-entry report skips them
FDA_EXCLUDED_IDS = {
    "VAERS2024", "FDA_ConsumerECG_Clearance", "FDA_PLLR_2014", "FDA_AI_Bias_2024",
    "FDA_PCCP_2024", "Darrow2021", "Lin2025FDA", "Lyell2023", "Mehta2025ACTR", "Warraich2025",
    "Clark2023", "Stone2009BlackBox", 
}

# Pairs that look like duplicates - possibly the same document entered twice
# Not merged; needs further review/approval
FDA_POSSIBLE_DUPLICATES = [("FDA2020NSAID", "FDA2020_NSAIDs")]

# Regexes for identifying FDA and DailyMed documents and related patterns
DAILYMED_RE = re.compile(r"dailymed\.nlm\.nih\.gov", re.IGNORECASE)
ACCESSDATA_LABEL_RE = re.compile(r"accessdata\.fda\.gov.*/label/", re.IGNORECASE)
ACCESSDATA_LABEL_YEAR_RE = re.compile(r"/label/(\d{4})/", re.IGNORECASE)
LABEL_TITLE_RE = re.compile(
    r"prescribing information|package insert|highlights of prescribing|drug label|product label",
    re.IGNORECASE,
)
ARCHIVE_URL_RE = re.compile(r"archive\.org|archive-it\.org", re.IGNORECASE)
FDA_ID_RE = re.compile(r"^fda|_fda|fda_", re.IGNORECASE)
FDA_URL_RE = re.compile(r"fda\.gov", re.IGNORECASE)
FDA_TEXT_RE = re.compile(r"\bFDA\b|Food and Drug")


def is_guideline_reference(entry):
    # Checks whether reference is a guideline through either pubtype-based flag
    # calculated in check_existence.py or through the presence of a recognized guideline
    # organization in the corporate author field in (currently rare) cases where 
    # PubMed's pubtype tag is missing/incomplete
    # Currently have not implemented a way to pull in orgs but the logic is there for
    # when we do
    if entry.get("_is_guideline"):
        return True
    # Also trust the bibliography's own type label as a second signal, so
    # guidelines with only a DOI or URL (no PubMed pubtypes) aren't missed.
    # Less reliable than PubMed's tag
    if (entry.get("type") or "").lower() in GUIDELINE_TYPE_LABELS:
        return True
    return confirmed_by_pubmed(entry)


# CHANGED: PubMed publication types that contradict a bibliography "guideline" label
TRIAL_PUBTYPES = {"Randomized Controlled Trial"}


def label_conflicts_with_pubmed(entry):
    # CHANGED: True if only the bibliography's label says guideline while PubMed says it's a
    # randomized trial. Usually means the wrong document is attached (e.g., an id naming a
    # guideline but pointing to a trial), so these go to review with their own reason
    # instead of being treated as guidelines
    return not confirmed_by_pubmed(entry) and bool(TRIAL_PUBTYPES & set(entry.get("_pubmed_pubtypes") or []))


def confirmed_by_pubmed(entry):
    # True if PubMed data (pubtype tag or corporate author) says this is a guideline,
    # as opposed to only the bibliography's own type label
    # Only PubMed-confirmed guidelines are approved automatically
    if entry.get("_is_guideline"):
        return True
    corp_author = (entry.get("_pubmed_corporate_author") or "").upper()
    return any(kw in corp_author for kw in GUIDELINE_ORG_KEYWORDS)


def pick_primary_specialty(entry, duplicates=()):
    # A reference can be associated with more than one CERT-* protocol
    # Among all specialties it is associated with, use the one with the shortest
    # (most conservative) staleness window for determining the primary specialty
    # This specialty is used for both grouping and currency check; a citation
    # will not be duplicated across multiple specialty buckets
    # Note: if a reference has a protocol containing a valid specialty/protocol prefix
    # and one that doesn't match the regex pattern, the one that doesn't match will be
    # silently skipped. This only matters if we care about keeping a record of all processing
    # of protocols though should not affect the overall specialty assignment process because
    # the valid specialty/protocol prefix will still be used for the assignment.
    # CHANGED: duplicates = other copies of the same document (same PubMed ID/DOI); their
    # protocols count too, so one document gets one specialty and the strictest limit applies
    prefixes = specialty_prefixes(entry)
    for copy in duplicates:
        prefixes |= specialty_prefixes(copy)
    if not prefixes:
        return None
   # Return the specialty with the shortest staleness window, breaking ties alphabetically
    return min(prefixes, key=lambda p: (SPECIALTY_STALENESS_YEARS.get(p, DEFAULT_STALENESS_YEARS), p))


def specialty_prefixes(entry):
    # CHANGED: split out of pick_primary_specialty so a duplicate group's protocols can be pooled
    prefixes = set()
    for p in entry.get("cited_by_protocols") or []:
        if not isinstance(p, str):
            continue
        m = CERT_PREFIX_RE.match(p)
        if m:
            prefixes.add(m.group(1))
    return prefixes


def group_duplicates(candidates):
    # CHANGED: finds the same document stored under several ids. Entries that share a PubMed ID
    # or DOI are grouped (chains included: A shares a PMID with B, B shares a DOI with C).
    # Safeguard: a group only counts as duplicates if the titles agree (same_document). If they
    # don't, two different documents share an identifier, so one has the wrong identifier
    # attached (e.g. the Tokyo Guidelines cholangitis and cholecystitis papers under one PMID).
    # Returns (duplicate_groups, identifier_conflicts), each a list of member lists
    n = len(candidates)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    first_seen = {}
    for i, e in enumerate(candidates):
        for key in (("pmid", e.get("_pmid")), ("doi", e.get("_doi"))):
            if not key[1]:
                continue
            if key in first_seen:
                union(i, first_seen[key])
            else:
                first_seen[key] = i

    groups = defaultdict(list)
    for i in range(n):
        groups[find(i)].append(candidates[i])

    duplicate_groups, identifier_conflicts = [], []
    for members in groups.values():
        if len(members) < 2:
            continue
        if len(cluster_by_title(members, same=same_document)) == 1:
            duplicate_groups.append(members)
        else:
            identifier_conflicts.append(members)
    return duplicate_groups, identifier_conflicts


def pick_representative(members):
    # CHANGED: the copy that stands for a duplicate group through the sorting steps. Prefers a
    # PubMed-confirmed copy, then the one cited by the most protocols, then alphabetical by id
    # so the choice is the same every run. The decision made for it applies to every copy
    return min(members, key=lambda e: (not confirmed_by_pubmed(e),
                                       -len([p for p in e.get("cited_by_protocols") or [] if isinstance(p, str)]),
                                       e.get("id") or ""))


# Decides whether two guideline titles are editions of the same guideline
# Requires both: titles_match() (overall wording near-identical) AND at most one meaningful
# word differing between the titles (years and generic words ignored via title_keywords)
# titles_match() alone wrongly merged different guidelines from the same organization,
# because long shared phrases (e.g. "A Report of the American College of Cardiology/
# American Heart Association Joint Committee...") pushed unrelated titles over the
# similarity bar, e.g. heart failure + atrial fibrillation + valve disease guidelines
def same_guideline(title_a, title_b):
    if not titles_match(title_a, title_b):
        return False
    differing_words = title_keywords(title_a) ^ title_keywords(title_b)
    return len(differing_words) <= 1


def same_document(title_a, title_b):
    # CHANGED: decides whether two entries that share a PubMed ID/DOI really are the same
    # document. Formatting differences are fine: one title may be a truncation or expansion of
    # the other (a dropped subtitle, or "A Report of the ... Committee" added). A substitution is
    # not: if each title has a meaningful word the other lacks (cholangitis vs cholecystitis),
    # they're different papers sharing an identifier
    if not titles_match(title_a, title_b):
        return False
    words_a, words_b = title_keywords(title_a), title_keywords(title_b)
    return words_a <= words_b or words_b <= words_a


def cluster_by_title(entries, same=same_guideline):
    # Union-find over pairwise title comparisons, so A-similar-to-B-similar-to-C
    # all land in one cluster even if A and C alone aren't similar enough.
    # CHANGED: `same` is the comparison to use: same_guideline (editions of one guideline,
    # the default) or same_document (copies of one document, for duplicate groups)
    n = len(entries)
    parent = list(range(n))

    # Finds the group in which a guideline is clustered (e.g., different year, same guideline)
    # Returns the representative guideline group for the given entry index
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    # Merges the clusters of two entries, ensuring they share the same representative
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    # Iterate over all pairs of entries and union their clusters if their titles match.
    # This ensures that all entries with similar titles end up in the same cluster.
    # Allows union-find to correctly cluster all related titles together, even if
    # some pairs are not directly similar
    for i in range(n):
        for j in range(i + 1, n):
            if same(entries[i].get("title") or "", entries[j].get("title") or ""):
                union(i, j)

    # Iterate through all guidelines
    # Build the final clusters of guideline groups based on their group representative find(i)
    clusters = defaultdict(list)
    for i in range(n):
        clusters[find(i)].append(entries[i])
    return list(clusters.values())


# Generic clinical/guideline boilerplate words - stripped out before comparing titles,
# so what's left is (mostly) the actual subject matter: the disease, drug, or procedure
# name, which is the part that actually indicates two papers are about the same thing
TITLE_STOPWORDS = {
    "guideline", "guidelines", "practice", "clinical", "management", "recommendation",
    "recommendations", "statement", "consensus", "update", "updated", "position",
    "policy", "approach", "care", "bulletin", "criteria", "committee", "society",
    "association", "college", "academy", "panel", "expert", "report", "reports",
    "review", "evidence-based", "evidence", "based", "diagnosis", "treatment",
    "therapy", "assessment", "evaluation", "screening", "prevention", "revision",
    "and", "of", "for", "the", "a", "an", "in", "on", "to", "with", "from", "by",
}
# Splits titles into words by stripping out non-alphanumeric characters
TITLE_TOKEN_RE = re.compile(r"[a-z0-9]+") 

# Extracts meaningful words from entry title, excluding stopwords,
# digits, and very short words
def title_keywords(title):
    tokens = TITLE_TOKEN_RE.findall((title or "").lower())
    return {t for t in tokens if t not in TITLE_STOPWORDS and not t.isdigit() and len(t) > 2}


# CHANGED: removed title_relevance_score() and cascading_fallback_search(), which scored
# and suggested non-guideline studies as replacements; they're no longer used


def clean_entry(entry):
    # Backfill existing issuing_body field from PubMed's corporate author field
    # if the PubMed field is available and issuing_body is empty
    # Not currently operational as the field doesn't exist yet
    # but activates automatically once it does
    # Also strips checking fields (e.g., oxford_level_of_evidence_estimate) from the entry
    # to ensure final JSON file has only necessary fields added to original JSON
    cleaned = {k: v for k, v in entry.items() if k not in DIAGNOSTIC_FIELDS}
    corp_author = entry.get("_pubmed_corporate_author")
    if corp_author and not (cleaned.get("issuing_body") or "").strip():
        cleaned["issuing_body"] = corp_author
    return cleaned

# entry_url, fda_category, fda_route, and looks_fda_related added for the FDA track
# Returns the URL for the entry, prioritizing _url, then url, and
# defaults to an empty string if neither is present
def entry_url(entry):
    return entry.get("_url") or entry.get("url") or ""


def fda_category(entry):
    # Returns the FDA category for the entry, or None if not applicable
    # Returns None if category in IDs excluded from FDA consideration (FDA_EXCLUDED_IDS)
    # These IDs were determined to be excluded from FDA consideration based on prior analysis
    entry_id = entry.get("id")
    if entry_id in FDA_EXCLUDED_IDS:
        return None
    if entry_id in FDA_SAFETY_COMMUNICATION_IDS:
        return "safety_communication"
    if entry_id in FDA_REMS_IDS:
        return "rems"
    url, title = entry_url(entry), entry.get("title") or ""
    if DAILYMED_RE.search(url) or ACCESSDATA_LABEL_RE.search(url) or LABEL_TITLE_RE.search(title):
        return "prescribing_information"
    return None


def fda_route(entry, category, current_year):
    # Returns ("auto", "") or ("review", <question for the reviewer>)
    # Determines the appropriate review route (straight to JSON or to exported spreadsheet for review)
    # based on predefined rules for FDA-related entries
    # "review" indicates the entry needs manual review
    # "auto" indicates the entry can be processed automatically and goes straight to JSON output
    url = entry_url(entry)
    if category == "rems":
        return "review", "fda_rems: is this program still active as described?"
    if category == "safety_communication":
        if ARCHIVE_URL_RE.search(url):
            return "review", "fda_archived_safety_communication: is this still in force?"
        return "auto", ""
    if DAILYMED_RE.search(url):
        return "auto", ""
    if ACCESSDATA_LABEL_RE.search(url):
        match = ACCESSDATA_LABEL_YEAR_RE.search(url)
        if not match:
            return "review", "fda_label_pdf_no_year_in_url: verify this is the current label"
        label_year = int(match.group(1))
        if current_year - label_year > FDA_FROZEN_LABEL_MAX_AGE_YEARS:
            return "review", (
                f"fda_label_snapshot_{label_year}: older than {FDA_FROZEN_LABEL_MAX_AGE_YEARS} "
                "years, find the current label on DailyMed"
            )
        return "auto", ""
    return "review", "fda_label_unrecognized_link_type: verify this is the current label"


def looks_fda_related(entry):
    # Returns True if the entry appears to be related to the FDA based on ID, URL, issuing body, or title
    # Ensures that these fields are flagged by new-entry report that haven't been categorized or excluded yet
    return bool(
        FDA_ID_RE.search(entry.get("id") or "")
        or FDA_URL_RE.search(entry_url(entry))
        or FDA_TEXT_RE.search(entry.get("issuing_body") or "")
        or FDA_TEXT_RE.search(entry.get("title") or "")
    )


def main():
    parser = argparse.ArgumentParser(description="Sort checked bibliography entries into current guidelines vs. items needing manual review.")
    parser.add_argument("--input", required=True, help="Path to a check_existence.py output file (e.g. bibliography (1).checked.json)")
    parser.add_argument("--output", default="current_guidelines.json", help="Where to write the approved, upload-ready guidelines JSON")
    parser.add_argument("--review-output", default="guideline_review_candidates.csv", help="Where to write the manual-review candidate spreadsheet")
    parser.add_argument("--fda-categories-output", default="fda_categories.csv", help="Where to write the companion id/category list for FDA entries")
    args = parser.parse_args()

    input_path = Path(args.input)
    try:
        with open(input_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"ERROR: input file not found: {input_path}")
        sys.exit(1)
    entries = [e for e in data.get("citations", []) if isinstance(e, dict)]

    # This script assumes it is running on a file with only valid entries
    # However, the output file from check_existence keeps every entry deliberately,
    # including invalid ones, so they are filtered out here
    before_count = len(entries)
    entries = [e for e in entries if e.get("_tier1_existence") == "valid"]
    print(f"Excluded {before_count - len(entries)} entries with a non-valid Tier-1 verdict before sorting ({len(entries)} remain).")

    current_year = datetime.now().year

    # ---- FDA track: labels, safety communications, REMS ----
    # Builds a list containing tuples of (entry, category), each corresponding to 
    # an FDA-related entry (categorized earlier in the script) and its determined category
    # Retracted entries skipped ("continue")
    # Loop runs in order so output is identical from run to run
    fda_entries = []
    for e in sorted(entries, key=lambda e: e.get("id") or ""):
        if e.get("_pubmed_integrity_flags"):
            continue
        category = fda_category(e)
        if category:
            fda_entries.append((e, category))

    # Remove FDA-related entries from the main entries list to avoid duplication in later processing
    fda_ids = {e.get("id") for e, _ in fda_entries}
    entries = [e for e in entries if e.get("id") not in fda_ids]

    # Sends each FDA-related entry through the routing function fda_route to determine
    # whether it can be automatically approved ("auto") or needs manual review
    # Also creates a file with entry ID, category, and routing destination for each FDA-related entry
    # This keeps a record of how each FDA-related entry was categorized and routed without modifying the original entries
    # since it is not yet known if MedCanon accepts new fields
    fda_approved = []
    fda_review_rows = []
    fda_category_rows = []
    for e, category in fda_entries:
        destination, reason = fda_route(e, category, current_year)
        fda_category_rows.append({"id": e.get("id"), "category": category, "destination": destination})
        if destination == "auto":
            fda_approved.append(e)
        else:
            fda_review_rows.append({
                "id": e.get("id"), "title": e.get("title"), "year": e.get("year"),
                "specialty": "", "evidence_level": "",
                "reason": reason, "decision": "",  # CHANGED: suggestion columns removed
                "category": category,
            })

    # Finds references that appear FDA-related but were not categorized earlier; do not appear on list to exclude (FDA_EXCLUDED_IDS)
    uncategorized_fda = sorted(
        (e for e in entries if looks_fda_related(e) and e.get("id") not in FDA_EXCLUDED_IDS),
        key=lambda e: e.get("id") or "",
    )

    # ---- Step 1: guideline candidate pool ----
    guideline_candidates = [e for e in entries if is_guideline_reference(e) and not e.get("_pubmed_integrity_flags")]
    # CHANGED: removed the non-guideline pool that fed the fallback suggestions

    # ---- Step 2 (CHANGED): the same document under several ids ----
    # Each duplicate group is decided once, through one representative copy; the decision then
    # applies to every copy (all ids uploaded if approved, one review row otherwise).
    # Identifier conflicts (same PubMed ID/DOI, different titles) are held for review as a whole
    duplicate_groups, identifier_conflicts = group_duplicates(guideline_candidates)
    copies_of = {}  # representative (by object identity) -> its other copies
    handled_elsewhere = set()
    for members in duplicate_groups:
        rep = pick_representative(members)
        copies_of[id(rep)] = [m for m in members if m is not rep]
        handled_elsewhere.update(id(m) for m in members if m is not rep)
    handled_elsewhere.update(id(m) for members in identifier_conflicts for m in members)

    def copies(entry):
        return copies_of.get(id(entry), [])

    def also_cited_as(entry):
        return "; ".join(sorted(m.get("id") or "" for m in copies(entry)))

    # ---- Step 3: group guideline candidates by specialty ----
    by_specialty = defaultdict(list)
    unspecified = []
    label_conflicts = []  # CHANGED: labeled guideline but PubMed says randomized trial
    for e in guideline_candidates:
        if id(e) in handled_elsewhere:  # CHANGED: follows its representative, or held as a conflict
            continue
        # CHANGED: kept out of the guideline families, so a trial can't be picked as a
        # family's newest edition or approved; reviewed separately below
        if label_conflicts_with_pubmed(e):
            label_conflicts.append(e)
            continue
        specialty = pick_primary_specialty(e, copies(e))
        if specialty is None:
            unspecified.append(e)
        else:
            by_specialty[specialty].append(e)

    approved = []
    approved_documents = 0  # CHANGED: documents approved; approved holds every id (copies included)
    label_only_count = 0  # Current guidelines sent to review because only the type label says guideline
    review_rows = list(fda_review_rows)
    specialties_with_no_guideline = []

    # Combine all specialties from the staleness configuration and the guideline candidates
    all_specialties = set(SPECIALTY_STALENESS_YEARS) | set(by_specialty)

    # Iterates through each specialty, looking up how old a guideline can be before it is out of date
    # Gets list of guidelines in each specialty
    for specialty in sorted(all_specialties):
        threshold = SPECIALTY_STALENESS_YEARS.get(specialty, DEFAULT_STALENESS_YEARS)
        candidates = by_specialty.get(specialty, [])

        if not candidates:
            # ---- Step 8: no guideline at all for this specialty ----
            # CHANGED: one review row for the specialty, instead of suggesting non-guideline studies
            specialties_with_no_guideline.append(specialty) # Record specialty with no guideline for display on console
            review_rows.append({
                "id": "", "title": "", "year": "", "specialty": specialty, "evidence_level": "",
                "reason": "no_guideline_for_specialty: find a guideline, or confirm none is needed",
                "decision": "",
            })
            continue

        # ---- Steps 4-5: title-cluster within specialty, take most recent per cluster ----
        for cluster in cluster_by_title(candidates):
            newest = max(cluster, key=lambda e: e.get("year") or 0)

            # A guideline with no year can't be age-checked, so it goes to review
            # instead of being approved
            # Only happens when no edition in the family has a year, 
            # since max() above prefers editions with one
            if not newest.get("year"):
                review_rows.append({
                    "id": newest.get("id"), "also_cited_as": also_cited_as(newest),
                    "title": newest.get("title"), "year": "",
                    "specialty": specialty, "evidence_level": "",
                    "reason": "guideline_no_year: no year recorded, check how current this is",
                    "decision": "",
                })
                continue

            age = current_year - newest.get("year")

            # A current guideline is only approved automatically if PubMed confirms it's
            # a guideline. If only the bibliography's type label says so, it goes to review instead
            if age <= threshold and not confirmed_by_pubmed(newest):
                review_rows.append({
                    "id": newest.get("id"), "also_cited_as": also_cited_as(newest),
                    "title": newest.get("title"), "year": newest.get("year"),
                    "specialty": specialty, "evidence_level": newest.get("_oxford_level_of_evidence_estimate"),
                    "reason": "guideline_label_only: labeled guideline in bibliography only, confirm",
                    "decision": "",
                })
                label_only_count += 1
            elif age <= threshold:
                # ---- Step 6: approved ----
                # CHANGED: every copy's id is uploaded, since protocols cite references by id
                approved.append(newest)
                approved.extend(copies(newest))
                approved_documents += 1
            else:
                # ---- Step 7: aged out ----
                # CHANGED: one review row for the out-of-date guideline itself, instead of rows
                # suggesting non-guideline studies. The reviewer keeps it (still the latest
                # edition), replaces it (newer guideline added to the bibliography), or rejects it
                review_rows.append({
                    "id": newest.get("id"), "also_cited_as": also_cited_as(newest),
                    "title": newest.get("title"), "year": newest.get("year"),
                    "specialty": specialty, "evidence_level": newest.get("_oxford_level_of_evidence_estimate"),
                    "reason": f"guideline_aged_out: {age} years old (limit {threshold}), keep if still the latest edition",
                    "decision": "",
                })

    # CHANGED: labeled guideline in the bibliography but PubMed says randomized trial --
    # never approved; one review row each so the reviewer can check for a wrong attached document
    for e in label_conflicts:
        review_rows.append({
            "id": e.get("id"), "also_cited_as": also_cited_as(e),
            "title": e.get("title"), "year": e.get("year"),
            "specialty": pick_primary_specialty(e, copies(e)) or "UNSPECIFIED",
            "evidence_level": e.get("_oxford_level_of_evidence_estimate"),
            "reason": ("guideline_label_conflict: bibliography says guideline but PubMed says "
                       "randomized trial; check whether the wrong document is attached"),
            "decision": "",
        })

    # CHANGED: identifier conflicts -- entries that share a PubMed ID/DOI but have different
    # titles. One of them has the wrong identifier attached, so none is approved and every
    # member gets a review row until the identifier is fixed in the bibliography
    for members in identifier_conflicts:
        member_ids = sorted(m.get("id") or "" for m in members)
        for m in members:
            others = "; ".join(i for i in member_ids if i != m.get("id"))
            review_rows.append({
                "id": m.get("id"), "also_cited_as": "",
                "title": m.get("title"), "year": m.get("year"),
                "specialty": pick_primary_specialty(m) or "UNSPECIFIED",
                "evidence_level": m.get("_oxford_level_of_evidence_estimate"),
                "reason": (f"identifier_conflict: shares a PubMed ID/DOI with {others} but the titles "
                           "differ; one has the wrong identifier attached"),
                "decision": "",
            })

    # Entries with no identifiable specialty at all -- can't apply a specialty-specific
    # currency rule, so route straight to manual review rather than guessing.
    for e in unspecified:
        review_rows.append({
            "id": e.get("id"), "also_cited_as": also_cited_as(e),
            "title": e.get("title"), "year": e.get("year"),
            "specialty": "UNSPECIFIED", "evidence_level": e.get("_oxford_level_of_evidence_estimate"),
            "reason": "no_specialty_identified",
            "decision": "",
        })

    # ---- Write clean, upload-ready output ----
    clean_output = [clean_entry(e) for e in approved + fda_approved]
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump({"schema_version": data.get("schema_version", 1), "citations": clean_output}, f, indent=2, ensure_ascii=False)

    # CHANGED: rows grouped by specialty, then by type of reason (aged out, label only, etc.),
    # then by id, so each specialty's rows sit together and the order is the same every run
    review_rows.sort(key=lambda r: (r["specialty"], r["reason"].split(":")[0], r["id"] or ""))

    # ---- Write manual-review spreadsheet ----
    with open(args.review_output, "w", encoding="utf-8", newline="") as f:
        # CHANGED: also_cited_as lists the other ids of the same document, so one decision
        # covers all of them. Rows without the key (FDA, empty specialty) get a blank
        writer = csv.DictWriter(f, fieldnames=["id", "also_cited_as", "title", "year", "specialty", "evidence_level", "reason", "decision", "category"])
        writer.writeheader()
        writer.writerows(review_rows)

    with open(args.fda_categories_output, "w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["id", "category", "destination"])
        writer.writeheader()
        writer.writerows(fda_category_rows)

    print("=" * 50)
    print("SUMMARY")
    print("=" * 50)
    print(f"Guideline candidates evaluated: {len(guideline_candidates)}")
    print(f"Approved (current): {approved_documents} documents, {len(approved)} ids (every id of an approved document is uploaded)")  # CHANGED
    extra_ids = sum(len(members) - 1 for members in duplicate_groups)
    print(f"Same document under several ids: {len(duplicate_groups)} groups decided once ({extra_ids} extra ids)")  # CHANGED
    conflict_ids = sum(len(members) for members in identifier_conflicts)
    print(f"Identifier conflicts (same PubMed ID/DOI, different titles; sent to review): {len(identifier_conflicts)} groups, {conflict_ids} ids")  # CHANGED
    print(f"Current but labeled guideline in bibliography only (sent to review): {label_only_count}")
    print(f"Labeled guideline but PubMed says randomized trial (sent to review): {len(label_conflicts)}")  # CHANGED
    print(f"Specialties with zero guideline coverage: {len(specialties_with_no_guideline)}")
    if specialties_with_no_guideline:
        print(f"  {', '.join(specialties_with_no_guideline)}")
    print(f"Entries with no identifiable specialty: {len(unspecified)}")
    print(f"Manual-review candidates (guidelines + FDA): {len(review_rows)}")  # CHANGED: no fallback suggestions
    print()
    by_category = Counter(category for _, category in fda_entries)
    print(f"FDA track: {len(fda_entries)} entries ({', '.join(f'{c}: {n}' for c, n in sorted(by_category.items()))})")
    print(f"  Included automatically: {len(fda_approved)}")
    print(f"  Sent to manual review: {len(fda_review_rows)}")
    print(f"New FDA-related entries not yet categorized: {len(uncategorized_fda)}")
    for e in uncategorized_fda:
        print(f"  {e.get('id')} | {e.get('title')}")
    for first, second in FDA_POSSIBLE_DUPLICATES:
        if first in fda_ids and second in fda_ids:
            print(f"Possible duplicate FDA entries (not merged): {first} / {second}")
    print()
    print(f"Approved entries written to: {args.output} ({len(clean_output)} total)")
    print(f"Review candidates written to: {args.review_output}")
    print(f"FDA categories written to: {args.fda_categories_output}")
    print("=" * 50)


if __name__ == "__main__":
    main()

