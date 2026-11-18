"""Turn the arXiv v1 release's accepted records into manuscript and Lean links.

The environment registry sometimes links supporting work beyond its printed
span. Keep those associations in the registry and distinguish them from the
passages that actually lie in the environment. Ordinary prose is indexed from
the frozen manuscript as well. This module reads files and checks evidence
identities; it does not invoke Lean or fetch mutable dependencies.
"""
from collections import defaultdict
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import re


PROJECT = "lean-rectangle-clt-arxiv-v1"
GITHUB = "https://github.com/VC2015/rectangle-clt-singular"
CHAINING_PIN = "b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc"
# Declaration headers verified in these files at the pinned dependency commit.
CHAINING = {
    "gamma_eq_finset": ("FiniteNets", 33),
    "gamma_mul_nnreal": ("GaussianFunctional", 37),
    "dirksen_expectation": ("Dirksen", 24),
    "gamma1_discrete_le_cutoff": ("Discrete", 29),
    "gamma1_discrete_le_log2": ("Discrete", 58),
    "gamma2_le_gaussianWidth": ("GaussianChaining", 28),
    "gamma_pullback": ("Functional", 59),
    "maximum_ae_eq_of_zero_contrasts": ("GaussianGeometry", 29),
    "gaussianWidth_mono_of_increment_le": ("GaussianComparison", 276),
}

# Anonymous proofs and proofs of intermediate displays cannot all be identified
# by a TeX caption. These entries follow the source order in both manuscripts.
ENV_RESULTS = [
    "Theorem 1", "Lemma 2", "Lemma A.1", "Lemma B.1", "Lemma B.2",
    "Proposition 1", "Lemma B.3", "Lemma B.4", "Lemma B.5", "Lemma C.1",
    "Lemma 1", "Lemma C.2", "Corollary 2", "Corollary 3", "Lemma E.1",
    "Lemma E.3", "Lemma E.4", "Lemma E.2", "Lemma E.5", "Lemma F.1",
    "Theorem 3", "Lemma F.2", "Lemma F.3", "Lemma G.1", "Lemma G.2",
    "Proposition G.1", "Lemma H.1", "Lemma H.2", "Proposition H.1",
    "Proposition H.2", "Lemma H.3", "Corollary 4", "Corollary 4", "Corollary 5",
]

SPECIAL_TITLES = {
    "P-main-06": "Seeded derivative estimates for Proposition 1",
    "P-supplement-32": "The late-time estimate for Corollary 4",
}

# Supports in ordinary prose. The coordinates distinguish common construction
# steps from the specializations of each distinct theorem.
PROSE_SPANS = [
    ("main", 302, 304, ("Corollary 1",)),
    ("main", 1468, 1741, ("Proposition 1",)),
    ("main", 6850, 7171, ("Theorem 2",)),
    ("main", 7667, 7792, ("Theorem 2",)),
    ("main", 8134, 8279, ("Theorem 4", "Theorem 5", "Theorem 6", "Theorem 7", "Theorem 8")),
    ("main", 8404, 8497, ("Theorem 4", "Theorem 5", "Theorem 6", "Theorem 7", "Theorem 8")),
    ("main", 8499, 8550, ("Theorem 5", "Theorem 7")),
    ("main", 8551, 8560, ("Theorem 5",)),
    ("main", 8561, 8569, ("Theorem 7",)),
    ("main", 8571, 8654, ("Theorem 5", "Theorem 7")),
    ("main", 8670, 8838, ("Theorem 6", "Theorem 8")),
    ("main", 8840, 8844, ("Theorem 6",)),
    ("main", 8844, 8848, ("Theorem 6", "Theorem 8")),
    ("supplement", 387, 410, ("Lemma G.2",)),
    ("supplement", 903, 1225, ("Lemma H.1",)),
    ("supplement", 1520, 1540, ("Proposition H.2",)),
    ("supplement", 1221, 1283, ("Proposition H.1", "Proposition H.2")),
]

# Use compact mathematical captions where the underlying record has no title.
PASSAGE_TITLES = {
    "H.SUBSYSTEM.DCT_CONCENTRATION": "Dominated convergence for concentration on a subsystem of faces",
    "H1.RADIUS_ACTUAL": "The Gaussian radius in the boundary layer",
    "H1.TRIPLE.ACTUAL_RADIUS": "The Gaussian radius in a three-face section",
    "H1.JF.DEFINITION_PAIRING": "Pairing the face integrals with their weights",
    "H1.ACTUAL_FACETS.POINTWISE_SLACK": "Slack inequalities on the selected facets",
    "H.POSITIVE.ACTUAL_RADIUS": "The positive tube estimate with the Gaussian radius",
    "H.FINAL.ACTUAL_PAIR_MATRIX_TRANSPORT": "Transport of the angle-weighted two-face matrix bound",
    "supplemental-g-array-decomposition.SUPPORT": "Decomposition of the fourth derivative by repeated directions",
    "H1.NONSIMPLE.GREEN": "The Gauss–Green identity on an actual nonsimple ridge",
    "H1.NONSIMPLE.SPHERICAL": "The spherical conormal identity for any number of incident edges",
    "H1.ALL_THRESHOLD.ACTUAL_VALUE_CONTINUITY": "Continuity of the ridge integral at a fixed threshold",
    "H1.ALL_THRESHOLD.FATOU_EXTENSION": "Extension from almost every threshold by Fatou’s lemma",
    "H1.ALL_THRESHOLD.EMPTY_OR_FULLD": "The pointwise bound for empty or full-dimensional polyhedra",
    "H1.ALL_THRESHOLD.ACTUAL_FACET_EXPECTATION": "The weighted ridge bound for the selected facets",
    "F4.DUPLICATION.COMPLETE": "Coordinate duplication preserves the discrepancy and Gaussian width",
    "T3.STMT": "The independent-coordinate lower bound",
    "T3.WIDTH": "Gaussian width for independent coordinates",
    "T3.LAW": "The product law of the two-point summands",
    "T3.MOMENTS": "Centering, variance and skewness of the summands",
    "T3.THRESHOLD": "The threshold for the detecting orthant",
    "T3.MODERATE": "The moderate-tail expansion",
    "T3.LINEAR": "Linearization of the tail correction",
    "T3.PRODUCT": "From a coordinate tail to an orthant probability",
    "E1.STMT": "The maximum bound with a nonnegative envelope budget",
    "E1.FINITE": "Finite second moments of the coordinates",
    "E1.ZERO": "The zero-budget case",
    "E1.TRUNC": "Truncation and centering",
    "E1.BERNSTEIN": "The exponential bound for the bounded part",
    "E1.LAYERCAKE": "Integration of the maximum tail probability",
    "E1.OMITTED": "The tail contribution of discarded observations",
    "E1.ALGEBRA": "Choice of the truncation level",
    "G3.source-connection-1": "Single-face and two-face fourth derivative contributions",
    "G3.source-connection-2": "The small-angle estimate",
    "G3.source-connection-3": "The translated-copy bound",
    "G3.source-connection-4": "Bound on the two-face contribution",
    "G3.source-connection-5": "Assembly of the complementary estimates",
    "H2.STATEMENT": "The two Gaussian matrix estimates",
    "H2.COVARIANCE": "Covariance under the weighted Gaussian law",
    "H2.NUCLEAR": "The nuclear norm bound",
    "H2.PROJECTED_MEAN": "The projected Gaussian mean",
    "H3.SIGNED_CONDITIONAL_RESTORATION": "Conditional restoration of the signed fourth derivative",
    "H.FINAL.NORMALIZED_PHYSICAL_BASE": "The normalized interpolation base",
    "H.FINAL.COMPLETE_MATRIX_INSTANTIATION": "Applying both matrix estimates to the Gaussian half-base",
    "H3.ACTUAL_SEEDED_APPLICATION": "The fourth-order estimate on the seeded path",
    "H3.GAP_TIME_AND_COROLLARY_ASSEMBLY": "Integration in time under the correlation gap",
}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|nonrec|partial|local|scoped)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|inductive|structure|class|instance)\s+([^\s(:{\[]+)"
)
STATEMENT = re.compile(rb"\\begin\{(theorem|lemma|proposition|corollary|conjecture)\}.*?\\end\{\1\}", re.S)


def check(condition, message):
    if not condition:
        raise ValueError(message)


def verify(data, expected, description):
    check(sha256(data).hexdigest() == expected, f"Hash mismatch for {description}")


def public_blob(base, revision, path, span=None):
    url = f"{base}/blob/{revision}/{path}"
    if span:
        first, last = span
        return url + (f"#L{first}" if first == last else f"#L{first}-L{last}")
    return url


def lean_headers(path):
    """Follow namespace and section commands and ignore nested Lean comments."""
    names = {}
    stack = []
    depth = 0
    for number, line in enumerate(path.read_text().splitlines(), 1):
        parts = []
        for piece in re.split(r"(/-|-\/|--)", line):
            if piece == "--" and not depth:
                break
            if piece == "/-":
                depth += 1
            elif piece == "-/" and depth:
                depth -= 1
            elif not depth:
                parts.append(piece)
        code = "".join(parts).strip()
        namespace = re.match(r"^namespace\s+(\S+)", code)
        if namespace:
            stack.append(namespace[1])
        elif re.match(r"^(?:noncomputable\s+)?section(?:\s|$)", code):
            stack.append("")
        elif re.match(r"^end(?:\s|$)", code) and stack:
            stack.pop()
        elif m := DECL.match(code):
            local_name = m[1]
            name = ".".join(s for s in [*stack, local_name] if s)
            names[name.removeprefix("_root_.")] = number
    return names


def passage_title(row, raw, owner):
    key = row["id"]
    if key in PASSAGE_TITLES:
        return PASSAGE_TITLES[key]
    title = raw.get("title")
    if isinstance(title, str) and title:
        title = re.sub(r"^(?:Actual |Literal )", "", title)
        title = re.sub(r"(Theorem|Corollary|Lemma|Proposition)(?=\d)", r"\1 ", title)
        title = title.replace("forq", "for q")
        return title[0].upper() + title[1:]
    # Numeric and module-based identifiers are less informative than a subject
    # and precise paper location. Ordinary words in structured IDs can be used.
    name = key.split(".")[-1] if "." in key else key.partition("-")[-1]
    if re.fullmatch(r"[A-Z]+(?:_[A-Z]+)+|[a-z]+(?:-[a-z]+)+", name):
        words = re.sub(r"[_-]", " ", name).lower()
        words = re.sub(r"^(?:actual |printed )", "", words)
        for lower, upper in (("gaussian", "Gaussian"), ("rademacher", "Rademacher"),
                             ("bennett", "Bennett"), ("bernstein", "Bernstein"),
                             ("cdf", "CDF"), ("fubini", "Fubini"), ("gamma", "Gamma"),
                             ("jensen", "Jensen"), ("fatou", "Fatou"), ("stein", "Stein")):
            words = re.sub(r"\b" + lower + r"\b", upper, words)
        return words[0].upper() + words[1:]
    a, b = row["location"]["lines"]
    return f"{owner}, lines {a}–{b}"


def collect(repo: Path, release: str):
    """Return the named-result index and the 34 explicit proof environments."""
    check(re.fullmatch(r"[0-9a-f]{40}", release), "Use a peeled release commit")
    project = repo / PROJECT
    registry = project / "correspondence"

    @lru_cache(maxsize=None)
    def read_json(path):
        return json.loads(path.read_bytes())

    pins = read_json(project / "source-pins.json")
    statements = read_json(registry / "statements.json")
    proofs = read_json(registry / "proof-environments.json")
    coverage = read_json(registry / "final-coverage.json")
    acceptance = read_json(registry / "final-acceptance.json")
    completed = coverage["post_acceptance_addenda"][0]
    check(completed == proofs["post_acceptance_addenda"][0] ==
          statements["final_acceptance"]["post_acceptance_addenda"][0] ==
          acceptance["post_acceptance_addenda"][0], "Inconsistent H.1 completion identity")
    verify((project / completed["path"]).read_bytes(), completed["sha256"], completed["path"])
    addendum = read_json(project / completed["path"])
    check(pins["paper_commit"] == statements["snapshot"] == proofs["snapshot"], "Wrong paper revision")

    sources = {}
    source_names = {}
    for which, source in pins["sources"].items():
        path = source["path"]
        data = (repo / path).read_bytes()
        verify(data, source["sha256"], path)
        sources[path] = data.splitlines(keepends=True)
        source_names[path] = which

    def paper(location):
        path = location["path"]
        first, last = location["lines"]
        check(1 <= first <= last <= len(sources[path]), f"Invalid interval {path}:{first}-{last}")
        data = b"".join(sources[path][first - 1:last])
        verify(data, location["sha256"], f"{path}:{first}-{last}")
        return public_blob(GITHUB, pins["paper_commit"], path, (first, last))

    packages = read_json(project / "lake-manifest.json")["packages"]
    chain = next(p for p in packages if p["name"] == "generic_chaining")
    check(chain["rev"] == CHAINING_PIN == pins["generic_chaining_commit"], "Unexpected chaining pin")
    project_dirs = [project, *[project / p["dir"] for p in packages if p["type"] == "path"]]
    project_dirs.append(repo / "lean-rectangle-clt-singular/third_party/isoperimetric")

    @lru_cache(maxsize=None)
    def module_headers(module):
        rel = Path(*module.split(".")).with_suffix(".lean")
        candidates = [(root / rel).resolve() for root in project_dirs if (root / rel).is_file()]
        check(len(candidates) == 1, f"Ambiguous or missing module {module}")
        path = candidates[0]
        return path.relative_to(repo.resolve()), lean_headers(path)

    @lru_cache(maxsize=None)
    def declaration(name, module):
        if name.startswith("GenericChaining."):
            filename, n = CHAINING[name.split(".")[-1]]
            check(module == "GenericChaining." + filename, f"Wrong external module for {name}")
            url = public_blob(chain["url"].removesuffix(".git"), chain["rev"],
                              f"GenericChaining/{filename}.lean", (n, n))
        else:
            path, names = module_headers(module)
            local_name = name.removeprefix(f"_private.{module}.0.")
            check(local_name in names, f"Missing declaration of {name} in {path}")
            n = names[local_name]
            url = public_blob(GITHUB, release, path, (n, n))
        return {"name": name, "url": url}

    results = {}
    labels = {}
    title_by_label = {}
    statement_passages = defaultdict(set)
    statement_spans = {}
    for s in statements["statements"]:
        label = s["statement"]
        loc = s["location"]
        a, b = loc["lines"]
        statement_spans[label] = (loc["path"], a, b)
        statement_url = paper(loc)
        span = b"".join(sources[loc["path"]][a - 1:b])
        matches = [m.group() for m in STATEMENT.finditer(span) if
                   ("\\label{" + s["tex_label"] + "}").encode() in m.group()]
        check(len(matches) == 1, f"Named environment missing for {label}")
        verify(matches[0], s["statement_environment_sha256"], label)
        modules = {d["declaration"]: d["kernel_import_module"] for d in s["expanded_types"]}
        results[label] = {"location": statement_url, "declarations": [
            declaration(name, modules[name]) for name in s["lean_declarations"]
        ], "proofs": [], "passages": []}
        labels[s["id"]] = label
        title_by_label[label] = s["title"]
        for key in s["proof_passage_ids"] + s.get("detailed_internal_passage_ids", []):
            statement_passages[key].add(label)
    check(len(results) == 41 and not results["Conjecture 1"]["declarations"], "Statement count or scope changed")

    registry_path = registry / "proof-environments.json"
    anchors = {m[1]: i for i, line in enumerate(registry_path.read_text().splitlines(), 1)
               if (m := re.match(r'\s*"id": "(P-(?:main|supplement)-[0-9]+)"', line))}
    environments = {}
    spans = {}
    check(len(proofs["proof_environments"]) == len(ENV_RESULTS), "Proof inventory changed")
    for number, (row, label) in enumerate(zip(proofs["proof_environments"], ENV_RESULTS), 1):
        key = row["id"]
        check(int(key.split("-")[-1]) == number, "Proof environment order changed")
        check(all(labels[sid] == label for sid in row["statement_ids"]), f"Wrong result for {key}")
        loc = row["location"]
        source_url = paper(loc)
        start, end = loc["lines"]
        lines = sources[loc["path"]]
        check(b"\\begin{proof}" in lines[start-1] and b"\\end{proof}" in lines[end-1], f"Proof delimiters for {key}")
        title = SPECIAL_TITLES.get(key, f"{label} · {title_by_label[label]}")
        environments[key] = {
            "id": key, "source_url": source_url, "results": [label], "title": title,
            "passages": [], "ledger_url": public_blob(GITHUB, release, registry_path.relative_to(repo),
                                                      (anchors[key], anchors[key])),
            "status": row["status"], "scope_notes": row["final_scope_notes"],
        }
        results[label]["proofs"].append(key)
        spans[key] = (loc["path"], start, end)

    check(coverage["frozen_passage_ledgers"] == acceptance["frozen_passage_ledgers"], "Accepted ledgers disagree")
    for file, digest in coverage["frozen_passage_ledgers"].items():
        verify((project / file).read_bytes(), digest, file)
    bindings = coverage["passage_bindings"]
    check(len(bindings) == 547 and len({r["canonical_unit_id"] for r in bindings if r["canonical_unit_id"]}) == 345,
          "Historical binding inventory changed")
    superseded = coverage["optional_paragraph_supersession"]["old_id"]
    for row in bindings:
        key = row["id"]
        loc = row["location"]
        url = paper(loc)
        ledger = read_json(project / row["ledger"])
        raw = ledger
        if row["json_pointer"]:
            group, i = row["json_pointer"].strip("/").split("/")
            raw = ledger[group][int(i)]
        frozen_row = json.dumps(raw, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
        verify(frozen_row, row["canonical_row_sha256"], key)
        check(coverage["frozen_passage_ledgers"][row["ledger"]] == row["ledger_sha256"], f"Wrong ledger for {key}")
        if (row["binding_kind"] != "direct_declarations" or
                row["correspondence_status"].startswith("superseded") or key == superseded):
            continue

        # Use the order chosen in the passage's source ledger before the
        # alphabetical order of the kernel export. Prefer a non-private entry.
        modules = {d["declaration"]: d["kernel_import_module"] for d in row["kernel_bindings"]}
        preferred = []
        for field in ("lean_endpoints", "new_declarations", "mapped_declarations", "lean_declarations", "declarations", "theorems"):
            v = raw.get(field, [])
            if isinstance(v, list):
                preferred.extend(n for n in v if isinstance(n, str) and n in modules)
        names = list(dict.fromkeys([*preferred, *modules]))
        ds = [declaration(n, modules[n]) for n in names]
        check(bool(ds), f"No declared endpoint for checked binding {key}")
        selected = {
            "C2.4": "GenericChaining.dirksen_expectation",
            "C2.5": "GenericChaining.gamma1_discrete_le_log2",
            "C2.6": "GenericChaining.gamma2_le_gaussianWidth",
            "H1.ALL_THRESHOLD.EMPTY_OR_FULLD": "RectangleCLTArxivV1.exists_fixed_surface_bound_of_empty_or_fullDimensional",
        }.get(key)
        if selected:
            first = next(d for d in ds if d["name"] == selected)
        else:
            first = next((d for d in ds if not d["name"].startswith("_private.")), ds[0])
        ekeys = row["proof_environment_ids"]
        a, b = loc["lines"]
        which = source_names[loc["path"]]
        owners = set(statement_passages[key])
        for label, (path, lo, hi) in statement_spans.items():
            if loc["path"] == path and lo <= a <= b <= hi and label != "Conjecture 1":
                owners.add(label)
        related_envs = []
        for e, (path, lo, hi) in spans.items():
            in_proof = lo <= a <= b <= hi
            overlaps_linked_proof = e in ekeys and lo <= b and a <= hi
            if loc["path"] == path and (in_proof or overlaps_linked_proof):
                owners.update(environments[e]["results"])
                related_envs.append(e)
        for side, lo, hi, group in PROSE_SPANS:
            if which == side and lo <= a <= b <= hi:
                owners.update(group)
        # Several formal passages cover the statement and some preliminaries.
        # A direct registry association is evidence for the route, even where
        # the paper places its supporting calculation outside the proof block.
        if not owners:
            for e in ekeys:
                owners.update(environments[e]["results"])
        topic = next((title_by_label[l] for l in results if l in owners),
                     "Main paper" if which == "main" else "Supplement")
        title = passage_title(row, raw, topic)
        passage = {"id": key, "title": title, "source_url": url, "lean_url": first["url"],
                   "lean_name": first["name"], "declarations": ds, "status": row["correspondence_status"]}
        for e in related_envs:
            environments[e]["passages"].append(passage)
        for label in owners:
            results[label]["passages"].append(passage)
    # The earlier full release uses generic thresholds and Fatou. These two
    # later obligations have their own source spans and kernel endpoints.
    endpoints = {d["name"]: d["kernel_import_module"] for d in addendum["checked_endpoints"]}
    for item in addendum["source_obligations_resolved"]:
        key = item["id"]
        if key == "H1.NONSIMPLE.GREEN":
            selected = ["hardGaussianWeightedRidgeIntegral_Green_actualFaces", "exists_actual_facet_ridge_Green"]
        else:
            check(key == "H1.NONSIMPLE.SPHERICAL", "Unknown H.1 addendum obligation")
            selected = ["nonsimpleActualConormalSum_eq_spherical_vector", "nonsimpleActualConormalSum_norm_le_spherical_area"]
        names = ["RectangleCLTArxivV1." + n for n in selected]
        ds = [declaration(name, endpoints[name]) for name in names]
        passage = {"id": key, "title": PASSAGE_TITLES[key], "source_url": paper(item["location"]),
                   "lean_name": ds[0]["name"], "lean_url": ds[0]["url"], "declarations": ds,
                   "status": addendum["status"]}
        environments["P-supplement-27"]["passages"].append(passage)
        results["Lemma H.1"]["passages"].append(passage)

    # The detailed draft for Theorem 4 was excluded from final acceptance.
    # The semantic review binds the unmasked construction to its theorem;
    # the numerical 1/8 example has a separate checked declaration and receipt.
    main = pins["sources"]["main"]["path"]
    review_path = project / "evidence/lower-bounded-theorem/independent-intrinsic-review.json"
    review = read_json(review_path)
    check(review["status"] == "PASS" and review["main_tex_sha256"] == pins["sources"]["main"]["sha256"],
          "Theorem 4 proof review changed")
    theorem = results["Theorem 4"]["declarations"][0]
    one_path = project / "evidence/lower-bounded-one/checkpoint-1/run.json"
    one = read_json(one_path)
    check(one["status"] == "passed", "Missing bounded-width example receipt")
    for file, digest in one["source_sha256"].items():
        verify((project / file).read_bytes(), digest, file)
    example = declaration("RectangleCLTArxivV1.bounded_width_example_one_eighth_from_main_regime",
                          "RectangleCLTArxivV1.LowerBoundedOne")
    for key, span, title, d, receipt, status in (
        ("T4.UNMASKED", (8499, 8651), "Unmasked observations with bounded amplitude", theorem,
         review_path, "independently_reviewed_theorem_endpoint"),
        ("T4.ONE_EIGHTH", (8656, 8668), "One leading coordinate and the constant 1/8", example,
         one_path, "separately_checked_example"),
    ):
        results["Theorem 4"]["passages"].append({
            "id": key, "title": title, "source_url": public_blob(GITHUB, pins["paper_commit"], main, span),
            "lean_name": d["name"], "lean_url": d["url"], "declarations": [d], "status": status,
            "ledger_url": public_blob(GITHUB, release, receipt.relative_to(repo)),
        })

    def ordered(rows):
        by_binding = {}
        for r in rows:
            signature = (r["source_url"], tuple(sorted(d["name"] for d in r["declarations"])))
            by_binding.setdefault(signature, r)
        return sorted(by_binding.values(), key=lambda r: (
            "Supplement_" in r["source_url"], int(r["source_url"].split("#L")[-1].split("-")[0]), r["id"]))

    for entry in [*environments.values(), *results.values()]:
        entry["passages"] = ordered(entry["passages"])
    check(all(e["passages"] for e in environments.values()), "Empty explicit proof")
    check(all(e["passages"] for k, e in results.items() if k != "Conjecture 1"), "Missing proof route")
    return results, list(environments.values())
