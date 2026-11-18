#!/usr/bin/env python3
"""Prepare reviewable final acceptance outputs; apply only an approved receipt.

The record command never changes live registries.  It checks the frozen plan,
preserves every pre-acceptance correspondence JSON file and both status texts,
and writes candidate outputs below a new evidence directory.  The apply command
requires the SHA-256 of that exact candidate receipt.  Frozen passage ledgers,
Lean sources, Root and Audit are never mutation targets.
"""
import argparse
import copy
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OUTPUTS = {"correspondence/statements.json", "correspondence/proof-environments.json",
           "correspondence/final-coverage.json", "correspondence/final-acceptance.json",
           "correspondence/README.md", "STATUS.md"}
N = "RectangleCLTArxivV1."
FINAL_PROMOTIONS = [
    ("S-hgap-lem-surfaces", "exists_fixed_surface_bound_of_empty_or_fullDimensional",
     "evidence/supplemental-h-surface-full/checkpoint-1/independent-review.json",
     "Actual all-threshold empty-or-topologically-full-dimensional surface bound. Fixed exact original-index facet presentation precedes every base law. The nonsimple ridge Green identity is bypassed by generic-threshold geometry, actual value continuity and Fatou; it is not separately proved."),
    ("S-hgap-prop-cubic", "proposition_H1_cubic_matrix_shifted",
     "evidence/supplement-h-cubic-matrix/independent-g3-review/receipt.json",
     "Actual arbitrary-length cubic matrix estimate with retained tuple factors, deterministic shift, arbitrary rectangular covariance factor and genuine concentrated base. Quantitative suppliers are discharged."),
    ("S-hgap-prop-pair", "proposition_H2_pair_matrix_shifted",
     "evidence/supplement-h-pair-matrix/independent-root-review.json",
     "Actual angle-weighted arbitrary-length pair matrix estimate with retained tuple factors, deterministic shift, arbitrary rectangular factor and genuine concentrated base. Quantitative suppliers are discharged."),
    ("S-hgap-thm-fourth", "lemma_H3_fourth_derivative",
     "evidence/actual-h-fourth-printed/independent-root-review.json",
     "Exact printed fixed-b bandwidth wrapper: its explicit positive constant is chosen before all dimensions/data. Actual fourth derivative integrability and expectation follow with both matrix suppliers discharged."),
    ("S-cor-positive-correlation-gap", "corollary4_canonical_correlation_gap",
     "evidence/corollary4-canonical/independent-review.json",
     "Actual rectangle distance using the canonical covariance correlation gap, with all analytic suppliers discharged. A covariance factor and its Gram equality remain ordinary representation inputs; the canonical gap inequality is derived internally."),
    ("S-cor-correlation-budget", "corollary5_exceptional_correlation_budget",
     "evidence/actual-h-corollaries/independent-root-review.json",
     "Actual exceptional-correlation-budget rectangle-distance result. Full matrix suppliers, separated/exceptional remainder split, actual source laws, time integration, bandwidth optimization and intrinsic width substitution are discharged.")]
PRIMARY_DETAILS = {"main06-seeded-internal", "b4-intrinsic-internal", "b5-intrinsic-internal",
                   "c1-rademacher-internal", "e3-gaussian-endpoint-internal",
                   "supplemental-h-surface-full", "supplemental-h-cubic-matrix",
                   "supplemental-h-pair-matrix", "actual-h-fourth-printed",
                   "corollary4-canonical", "exceptional-corollary-assembly"}
PRIMARY_OUTSIDE = {"corollary-1-normalization", "lower-fourth-dense", "lower-sparse-f6",
                   "lower-leading-common-internal", "lower-duplication-completion"}
EXTRA_REVIEWS = {
    "c1-rademacher-internal": ["evidence/c1-rademacher-internal/independent-review.json",
                               "evidence/c1-rademacher-internal/independent-mgf-subreview.json"],
    "main06-seeded-internal": ["evidence/main06-seeded-internal/independent-review.json",
                              "evidence/main06-seeded-internal/independent-copy-subreview.json"],
    "lower-duplication-completion": ["evidence/lower-duplication-completion/independent-root-review.json"],
    "lower-leading-common-internal": ["evidence/early-internal-correspondence/independent-root-lower-review.json"],
    "supplemental-h-active-face-reindex": ["evidence/supplement-h-active-face-reindex/independent-bounded-review.json"],
    "supplemental-h-actual-facets": ["evidence/supplemental-h-actual-facets/independent-g3-review/receipt.json"],
    "supplemental-h-cubic-coarea": ["evidence/supplement-h-cubic-coarea/independent-g3-review/receipt.json"],
    "supplemental-h-gamma-positive-mixed": ["evidence/supplemental-h-positive-cross-review/independent-intrinsic-review.json"],
    "supplemental-h-gamma-signed-mixed": ["evidence/supplement-h-gamma-signed-mixed/independent-g3-review/receipt.json"],
    "supplemental-h-logistic-pair-coordinate": ["evidence/supplemental-h-logistic-pair-coordinate/independent-g3-review/receipt.json"],
    "supplemental-h-matrix-support": ["evidence/supplement-h-matrix-support/independent-root-review.json"],
    "supplemental-h-pair-reference": ["evidence/supplement-h-pair-reference/independent-intrinsic-review.json"],
    "supplemental-h-projected-reference": ["evidence/supplement-h-projected-reference/independent-root-review.json"],
    "supplemental-h-subsystem-concentration": ["evidence/supplemental-h-subsystem-concentration/checkpoint-1/independent-review.json"],
    "supplemental-h-weighted-threshold": ["evidence/supplement-h-weighted-threshold/independent-g3-review/receipt.json"]}
LEGACY_REVIEW_SHA256 = {
    "evidence/expected-maximum-envelope/independent-review.json": "322fb8df4b16806713aaebd34a3b459b08f481f174bc1be103ff7fb9c8180557",
    "evidence/intrinsic-main-review/independent-review.json": "8c5fe0717455673e198ccd1fb0aa9dd1133a10daac627fd6075f81ac91edd2e0",
    "evidence/lower-fourth-dense-independent-review.md": "e200a19382b40af1b50c3928ecd1344d797f3170258344ed41c03f371dbe6554",
    "evidence/lower-sparse-numeric-independent-review.md": "7727c5d491181ba6657e7ca9afcd774ee08020fa2ad609ccaab8f4e496517d48",
    "evidence/polyhedral-intrinsic/orlicz-independent-review.json": "afacc4a205fb4289a6389d9cfc462e0010cfd6752922b161732e0322368fdc6c",
    "evidence/subexponential-intrinsic/independent-review.json": "1f464889796c386b547d32881bfdf24d257a38aa98ce0e8f0a75ac5d53fd4cfd"}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical_sha(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, ensure_ascii=False,
                                    separators=(",", ":")).encode()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def pointer(data, path):
    for key in path.split("/")[1:]:
        key = key.replace("~1", "/").replace("~0", "~")
        data = data[int(key)] if isinstance(data, list) else data[key]
    return data


def existing_path(root, value, nearby=None):
    path = Path(value)
    candidates = [path] if path.is_absolute() else [root / path]
    if nearby is not None:
        candidates += [nearby / path, nearby / path.name]
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    raise RuntimeError("Missing evidence artifact: " + str(value))


def reference(root, path):
    path = Path(path).resolve()
    return {"path": os.path.relpath(path, root), "sha256": sha(path)}


def verify_hashes(root, entries):
    for name, expected in entries.items():
        path = root / name
        require(path.is_file() and sha(path) == expected, "Changed/missing input: " + name)


def verify_location(root, location):
    path = root.parent / location["path"]
    a, b = location["lines"]
    lines = path.read_bytes().splitlines(keepends=True)
    require(1 <= a <= b <= len(lines), "Invalid source interval: " + str(location))
    actual = hashlib.sha256(b"".join(lines[a - 1:b])).hexdigest()
    require(actual == location["sha256"], "Frozen source span changed: " + str(location))


def verify_plan(root, plan):
    require(plan["expected_counts"] == {"unqualified_statements": 39,
            "qualified_statements": 1, "excluded_conjectures": 1,
            "proof_environments": 34}, "Unexpected acceptance scope")
    verify_hashes(root, plan["pre_acceptance_identity"])
    actual_preimages = {str(p.relative_to(root)) for p in (root / "correspondence").glob("*.json")}
    actual_preimages.update({"STATUS.md", "correspondence/README.md"})
    require(actual_preimages == set(plan["pre_acceptance_identity"]),
            "The complete pre-acceptance ledger inventory changed; regenerate the plan")
    verify_hashes(root, plan["review_identity"])
    verify_hashes(root, plan["frozen_source_identity"])
    inventory = read(root / plan["proof_environment_inventory"]["path"])
    require(sha(root / plan["proof_environment_inventory"]["path"]) ==
            plan["proof_environment_inventory"]["sha256"], "Environment inventory changed")
    require(len(inventory["proof_environments"]) == 34, "Not all proof environments are bound")
    for env in inventory["proof_environments"]:
        verify_location(root, env["source_location"])
        require(env["independent_reviews"], "No environment review: " + env["proof_environment_id"])
        for binding in env["candidate_detailed_bindings"]:
            require(sha(root / binding["ledger"]) == binding["sha256"],
                    "Changed environment ledger: " + binding["ledger"])
            data = read(root / binding["ledger"])
            for passage in binding["passages"]:
                row = pointer(data, passage["json_pointer"])
                require(canonical_sha(row) == passage["canonical_row_sha256"],
                        "Changed passage row: " + passage["id"])
    for row in plan["passage_bindings"]:
        verify_location(root, row["location"])
        data = read(root / row["ledger"])
        require(canonical_sha(pointer(data, row["json_pointer"])) == row["canonical_row_sha256"],
                "Changed planned passage: " + row["id"])
    require(inventory["literal_unproved_internal_claims"], "H1 internal exclusion was dropped")
    require(all("bypassed" in x["status"] for x in inventory["literal_unproved_internal_claims"]),
            "Unproved H1 identity must remain explicitly bypassed")
    return inventory


def review_paths(root, data):
    paths = set()
    def walk(value):
        if isinstance(value, str):
            # A preserved ledger under '*-reviewed-ledgers' is not a review.
            if (value.startswith("evidence/") and "review" in value.lower()
                    and value.endswith((".json", ".md"))
                    and "reviewed-ledgers" not in value and "pre-acceptance" not in value
                    and not value.endswith("-passages.json")):
                if (root / value).is_file():
                    paths.add(value)
        elif isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, dict):
            for key, item in value.items():
                if key not in {"expanded_types", "dependency_bindings", "project_dependency_graph",
                               "source_identity", "source_files", "direct_dependencies"}:
                    walk(key)
                    walk(item)
    walk(data)
    return paths


def passed_review(root, path):
    p = root / path
    require(p.is_file(), "Missing independent review: " + path)
    if p.suffix == ".md":
        require(LEGACY_REVIEW_SHA256.get(path) == sha(p), "Unrecognized historical prose review: " + path)
        result = "Exact approved historical Markdown review bytes"
    else:
        data = read(p)
        markers = [str(data.get(k, "")) for k in
                   ("status", "result", "conclusion", "overall_status", "overall_result")]
        require(not any(re.match(r"(?:not[ _-]+pass|fail(?:ed|ure)?|reject(?:ed)?|error)(?:[ _-]|$)",
                                 x, re.I) for x in markers),
                "Review explicitly records a negative result: " + path)
        good = [x for x in markers if re.fullmatch(r"pass(?:ed)?(?:_[a-z0-9]+)*", x, re.I)
                and not any(t.startswith(("FAIL", "NOT", "REJECT", "ERROR")) for t in x.upper().split("_"))]
        if not good and LEGACY_REVIEW_SHA256.get(path) == sha(p):
            good = ["Exact approved historical prose conclusion bytes"]
        require(good, "Review has no top-level PASS result: " + path)
        result = good[0]
    return {"path": path, "sha256": sha(p), "recorded_result": result}


def prepare(args):
    """Prepare a concrete immutable plan without accepting or changing old data."""
    root = args.root.resolve()
    inventory_path = args.inventory.resolve()
    inventory = read(inventory_path)
    mp = read(args.mapping_plan)
    require(len(mp["target_origins"]) == 1949, "Review any change to the full target scope")
    require(not args.out.exists(), "Acceptance plan already exists")
    registry = read(root / "correspondence/statements.json")
    registry_by_id = {x["id"]: x for x in registry["statements"]}
    reviews = set()
    promotions = []
    for sid, name, review, scope in FINAL_PROMOTIONS:
        require(registry_by_id[sid]["status"] == "open", "Unexpected current statement status: " + sid)
        require(N + name in mp["target_origins"], "Final headline absent from mapper plan: " + name)
        verify_location(root, registry_by_id[sid]["location"])
        rr = passed_review(root, review)
        reviews.add(review)
        promotions.append({"statement_id": sid, "declarations": [N + name],
                           "independent_reviews": [rr], "formalization_scope": scope,
                           "printed_proof_status": ("checked_final_statement_via_alternative_proof_internal_identity_bypassed"
                               if sid == "S-hgap-lem-surfaces" else
                               "checked_mapped_passages_with_explicit_method_notes")})
    selected, ledger_reviews = {}, {}
    for env in inventory["proof_environments"]:
        for rr in env["independent_reviews"]:
            reviews.add(rr["path"])
        for binding in env["candidate_detailed_bindings"]:
            ledger_reviews.setdefault(binding["ledger"], set()).update(
                rr["path"] for rr in binding["independent_reviews"] + env["independent_reviews"])
            for row in binding["passages"]:
                key = (binding["ledger"], row["json_pointer"])
                item = selected.setdefault(key, {"environments": [], "classes": set(), "primary": False,
                                                 "reviews": set()})
                item["environments"].append(env["proof_environment_id"])
                item["classes"].add(row["classification"])
                stem = Path(binding["ledger"]).name.removesuffix("-passages.json")
                item["primary"] |= binding["role"] == "primary_existing" or stem in PRIMARY_DETAILS
                item["reviews"].update(rr["path"] for rr in binding["independent_reviews"])
                item["reviews"].update(rr["path"] for rr in env["independent_reviews"])
    supersessions = {(x["historical_ledger"], x["json_pointer"]): x
                     for x in inventory["provisional_row_supersessions"]}
    rows, all_ledger_hashes, excluded_historical = [], {}, {}
    for path in sorted((root / "correspondence").glob("*-passages.json")):
        rel = str(path.relative_to(root))
        if path.name == "lower-width-passages.json":
            excluded_historical[rel] = {"sha256": sha(path),
                "scope": "Excluded untracked historical draft; preserve only in the complete pre-acceptance snapshot. Not an authoritative live-ledger dependency or accepted correspondence."}
            continue  # Explicitly historical draft; preserved and inventoried, never promoted.
        all_ledger_hashes[rel] = sha(path)
        data = read(path)
        stem = path.name.removesuffix("-passages.json")
        inherited_reviews = (review_paths(root, data) | set(EXTRA_REVIEWS.get(stem, []))
                             | ledger_reviews.get(rel, set()))
        candidates = []
        for key in ["passages", "source_connections"]:
            if isinstance(data.get(key), list):
                candidates += [("/" + key + "/" + str(i), value) for i, value in enumerate(data[key])
                               if isinstance(value, dict)]
        if not candidates and isinstance(data.get("frozen_location"), dict):
            candidates = [("", data)]
        for ptr, row in candidates:
            location = next((row[k] for k in ["location", "frozen_location", "source_span"]
                             if isinstance(row.get(k), dict) and "path" in row[k] and "lines" in row[k]), None)
            require(location is not None, "Unmapped source location: " + rel + ptr)
            verify_location(root, location)
            key = (rel, ptr)
            selection = selected.get(key, {"environments": [], "classes": set(), "primary": False, "reviews": set()})
            rr_paths = inherited_reviews | selection["reviews"] | review_paths(root, row)
            rr = []
            for p in sorted(rr_paths):
                rr.append(passed_review(root, p))
                reviews.add(p)
            names = sorted(n for n, origins in mp["target_origins"].items()
                           if any(x["ledger"] == rel and
                                  (not ptr or x["pointer"] == ptr or x["pointer"].startswith(ptr + "/"))
                                  for x in origins))
            original_status = row.get("status", row.get("inclusion_status", data.get("status", "not_recorded")))
            rid = row.get("id", stem + ".SUPPORT")
            primary = selection["primary"] or stem in PRIMARY_OUTSIDE
            classes = selection["classes"]
            if key in supersessions:
                status = supersessions[key]["sidecar_status"]
                primary = False
            elif "qualified_step_nonnegative_budget" in classes or original_status == "checked_with_explicit_nonnegative_budget_qualification":
                status = "checked_with_explicit_nonnegative_budget_qualification"
            elif "P-supplement-27" in selection["environments"]:
                status = "checked_alternative_route_support_with_explicit_H1_internal_bypass"
            elif "documented_equivalent_or_alternative_route_support" in classes:
                status = "checked_with_documented_route_variation"
            elif "printed_step" in classes:
                status = "checked_printed_proof"
            elif original_status in ["checked_printed_proof", "checked_with_documented_route_variation"]:
                status = original_status
            elif stem in PRIMARY_OUTSIDE and rr:
                status = "checked_with_documented_route_variation"
            elif rr:
                status = "checked_supporting_binding_not_an_additional_printed_atom"
                primary = False
            else:
                status = "fresh_kernel_binding_without_new_semantic_promotion"
                primary = False
            if "historical_provisional_open_obligation_must_use_explicit_supersession" in classes:
                require(key in supersessions, "Open provisional row lacks supersession: " + rid)
            if primary:
                require(rr, "Canonical unit lacks independent review: " + rid)
            support_links = {p: h for p, h in data.get("supporting_packets", {}).items()
                             if p.startswith("correspondence/") and p.endswith("-passages.json")}
            for p, h in support_links.items():
                require(sha(root / p) == h, "Changed explicit supporting packet: " + p)
            require(names or key in supersessions or (support_links and rr),
                    "Empty declaration list needs an explicit obligation supersession: " + rel + ptr)
            if not names and key not in supersessions:
                primary = False
                status = "checked_support_packet_link_without_separate_declaration_claim"
            rows.append({"id": rid, "ledger": rel, "ledger_sha256": sha(path), "json_pointer": ptr,
                         "canonical_row_sha256": canonical_sha(row), "location": location,
                         "recorded_status": original_status, "correspondence_status": status,
                         "canonical_unit_id": (rid if primary else None),
                         "proof_environment_ids": selection["environments"],
                         "declarations": names, "independent_reviews": rr,
                         "binding_kind": ("direct_declarations" if names else "superseded_obligation"
                                          if key in supersessions else "explicit_support_packet_links"),
                         "support_ledger_links": support_links,
                         "supersession": supersessions.get(key),
                         "preserved_route_notes": {k: row[k] for k in
                             ["route_variation", "method_variation", "method_note", "route_note",
                              "qualification", "formal_scope", "correspondence", "proof_adaptation"] if k in row}})
    # Identical canonical IDs can appear in overlapping review packets; count one.
    # Source overlaps remain explicit and are never represented as disjoint atoms.
    baseline_paths = sorted((root / "correspondence").glob("*.json"))
    baseline_paths += [root / "STATUS.md", root / "correspondence/README.md"]
    baseline = {str(p.relative_to(root)): sha(p) for p in baseline_paths}
    source_identity = {"../" + x["path"]: x["sha256"] for x in registry["source_files"].values()}
    plan = {"schema_version": 1, "status": "prepared_waiting_for_final_clean_pass_and_root_review",
            "created_at_utc": now(), "scope": "All40 named results in their checked concrete types:39 unqualified and E1 explicitly qualified by A≥0. All34 proof environments have individual reviewed bindings. Printed steps and alternative proof supports remain distinct; the H1 nonsimple Green identity is explicitly bypassed and not certified as a separate all-threshold theorem.",
            "expected_counts": {"unqualified_statements": 39, "qualified_statements": 1,
                                "excluded_conjectures": 1, "proof_environments": 34},
            "expected_mapped_targets": 1949, "final_proof_commit": mp["source_commit"],
            "mapping_plan": reference(root, args.mapping_plan),
            "pre_acceptance_identity": baseline, "frozen_source_identity": source_identity,
            "frozen_passage_ledgers": all_ledger_hashes,
            "excluded_historical_snapshot_inputs": excluded_historical,
            "review_identity": {p: sha(root / p) for p in sorted(reviews)},
            "proof_environment_inventory": reference(root, inventory_path),
            "statement_promotions": promotions, "passage_bindings": rows,
            "count_policy": "Count distinct explicitly listed canonical_unit_id values once; additional independently reviewed or kernel-bound supporting rows are separate binding counts. Overlapping source intervals are not disjoint proof atoms. The old F4.DUPLICATION row is superseded and its completed replacement counts once. Historical totals are preserved, never added to the new enumeration.",
            "mutation_allowlist_after_approval": sorted(OUTPUTS),
            "execution": {"first": "record verifies passed clean evidence, snapshots every old correspondence JSON/STATUS/README, and writes candidate outputs only",
                          "second": "apply requires the root-approved exact candidate receipt SHA256 and revalidates source/evidence/preimage identities"}}
    verify_plan(root, plan)
    write(args.out, plan)
    print(json.dumps({"plan": str(args.out), "sha256": sha(args.out),
                      "passage_rows": len(rows), "canonical_units": len({r["canonical_unit_id"] for r in rows if r["canonical_unit_id"]}),
                      "preserved_json_and_text_inputs": len(baseline), "review_files": len(reviews)}))


def verify_clean_run(root, path):
    path = Path(path).resolve()
    run = read(path)
    require(run.get("status") == "passed", "Clean checkpoint has not passed: " + str(path))
    require("initial_git_status" in run and not run["initial_git_status"],
            "Checkpoint did not start in a clean checkout")
    if "source_identity" in run:
        identity = run["source_identity"]
        require(isinstance(identity.get("files"), dict), "Incomplete clean source identity")
        verify_hashes(root, identity["files"])
        aggregate = hashlib.sha256(json.dumps(identity["files"], sort_keys=True).encode()).hexdigest()
        require(aggregate == identity["aggregate_sha256"], "Clean source identity aggregate differs")
    for command in run["commands"]:
        require(command.get("exit_code") == 0, "Failed/incomplete command: " + command["label"])
        log = existing_path(root, command["log"], path.parent)
        require(sha(log) == command["log_sha256"], "Command log changed: " + str(log))
    return run


def verify_mapping(root, mapping_plan_path, run_path, clean_run_path, expected_count):
    mapping_plan_path, run_path = Path(mapping_plan_path).resolve(), Path(run_path).resolve()
    mp = read(mapping_plan_path)
    run = verify_clean_run(root, run_path)
    clean = verify_clean_run(root, clean_run_path)
    if Path(clean_run_path).resolve() != run_path:
        require("source_identity" in clean, "Separate clean checkpoint lacks its source/harness identity")
    require(run["plan_sha256"] == sha(mapping_plan_path), "Mapper plan/receipt mismatch")
    require(run["source_commit"] == clean["source_commit"] == mp["source_commit"],
            "Clean checkpoints have different proof commits")
    require(any(c["argv"] in [["lake", "build"], ["lake", "build", mp["root_module"]]]
                for c in clean["commands"]),
            "No fresh Root build in the selected clean checkpoint")
    require(not mp["unresolved_unqualified_values"] and not mp["unresolved_project_imports"],
            "Unresolved mapper target/imports")
    verify_hashes(root, mp["ledger_sha256"])
    verify_hashes(root, mp["source_identity"])
    require(sha(root / mp["mapping_tool_identity"]["path"]) ==
            mp["mapping_tool_identity"]["sha256"], "Mapping tool changed")
    export_path = run_path.parent / "expanded-types-and-dependencies.json"
    require(sha(export_path) == run["export_sha256"], "Fresh type export hash mismatch")
    export = read(export_path)
    endpoints = export["endpoints"]
    types = {x["name"]: x for x in endpoints}
    names = set(mp["target_origins"])
    require(len(endpoints) == len(types) == len(names) == run["target_count"] == expected_count,
            "Fresh target count differs from approved scope")
    require(set(types) == names, "Exact mapped type export is incomplete")
    require(all(x["expanded_type"] and x["kernel_import_module"] for x in endpoints),
            "A fresh type or actual kernel provider is missing")
    harness = (run_path.parent / "TypesAndAudit.lean").read_text()
    require("set_option pp.all true" in harness, "Full pp.all type printing was not enabled")
    require(set(export["axiom_union"]) <= ALLOWED and
            set(run["axiom_union"]) == set(export["axiom_union"]), "Unexpected kernel axiom")
    graph_rows = export["project_dependency_graph"]
    graph = {x["name"]: x["direct_project_dependencies"] for x in graph_rows}
    require(len(graph) == len(graph_rows) == run["project_dependency_nodes"], "Graph count mismatch")
    require(names <= set(graph), "Graph omits an exact mapped target")
    require(all(set(ds) <= set(graph) for ds in graph.values()), "Project graph is not closed")
    bindings_path = run_path.parent / "ledger-bindings.json"
    require(sha(bindings_path) == run["bindings_sha256"], "Ledger binding export changed")
    bindings = read(bindings_path)
    require(bindings["ledger_sha256"] == mp["ledger_sha256"] and
            bindings["export_sha256"] == sha(export_path) and set(bindings["bindings"]) == names,
            "Incomplete ledger/type provenance")
    for name, binding in bindings["bindings"].items():
        require(binding["origins"] == mp["target_origins"][name] and
                binding["expanded_type"] == types[name]["expanded_type"] and
                binding["kernel_import_module"] == types[name]["kernel_import_module"],
                "Type/provenance drift: " + name)
    providers = read(run_path.parent / "actual-provider-bindings.json")["present"]
    require({x["name"] for x in providers} == names and
            all(x["kernel_import_module"] == types[x["name"]]["kernel_import_module"]
                for x in providers), "Actual mapped providers disagree")
    forced = read(run_path.parent / "forced-source-inventory.json")
    forced_modules = set(forced["modules"])
    require(len(forced_modules) == len(forced["modules"]), "Duplicate forced-source inventory module")
    required_root_replay = {m for m in mp["root_project_import_closure"] if m.startswith("RectangleCLTArxivV1")}
    require(required_root_replay <= forced_modules, "Root ArxivV1 source replay is incomplete")
    require({x["kernel_import_module"] for x in endpoints} <= forced_modules,
            "An actual mapped provider was not replayed")
    force_commands = [c for c in run["commands"] if c["label"].startswith("force-")]
    for module in forced_modules:
        source = mp["source_module_paths"][module]
        require(forced["source_sha256"][module] == mp["source_identity"][source],
                "Forced-source pinned hash differs: " + module)
        matching = [c for c in force_commands if c["argv"] == ["lake", "env", "lean", source]
                    and c["label"].endswith("-" + module.replace(".", "-"))]
        require(len(matching) == 1, "Missing/duplicate exact module/source replay command: " + module)
    for name in ["Kane.exp_avg_le_avg_exp", "Kane.avg_le_sqrt_of_exp_moment"]:
        require(name in types and name in graph, "Kane proof route missing: " + name)
        require(types[name]["kernel_import_module"] in forced_modules, "Kane source was not replayed")
    require(sum(c["label"].startswith("force-") for c in run["commands"]) == len(forced_modules),
            "Forced source command inventory mismatch")
    refs = {"clean_checkpoint": reference(root, clean_run_path),
            "mapping_checkpoint": reference(root, run_path),
            "mapping_plan": reference(root, mapping_plan_path),
            "expanded_types_and_project_graph": reference(root, export_path),
            "ledger_bindings": reference(root, bindings_path),
            "actual_provider_bindings": reference(root, run_path.parent / "actual-provider-bindings.json"),
            "forced_source_inventory": reference(root, run_path.parent / "forced-source-inventory.json"),
            "source_commit": run["source_commit"], "target_count": len(names),
            "project_dependency_nodes": len(graph), "axiom_union": export["axiom_union"],
            "allowed_axioms": sorted(ALLOWED), "pp_all": True}
    return types, graph, refs


def fresh_bindings(names, types, graph, refs):
    require(set(names) <= set(types), "Missing required mapped declarations: " + str(set(names) - set(types)))
    return [{"declaration": n, "expanded_type": types[n]["expanded_type"],
             "direct_dependencies": types[n]["direct_dependencies"],
             "direct_project_dependencies": graph[n],
             "kernel_import_module": types[n]["kernel_import_module"],
             "fresh_export": refs["expanded_types_and_project_graph"]} for n in names]


def build_outputs(root, plan, inventory, types, graph, refs):
    coverage_rows = []
    for prepared in plan["passage_bindings"]:
        row = copy.deepcopy(prepared)
        row["kernel_bindings"] = fresh_bindings(row["declarations"], types, graph, refs)
        row["fresh_kernel_status"] = ("passed_exact_type_complete_axiom_union_and_closed_project_graph"
                                       if row["declarations"] else
                                       "historical_obligation_only_see_checked_supersession"
                                       if row["binding_kind"] == "superseded_obligation" else
                                       "see_explicit_checked_support_packets_no_separate_declaration_claim")
        coverage_rows.append(row)
    canonical = {r["canonical_unit_id"] for r in coverage_rows if r["canonical_unit_id"] is not None}
    qualified = {r["canonical_unit_id"] for r in coverage_rows if r["canonical_unit_id"] is not None
                 and r["correspondence_status"] == "checked_with_explicit_nonnegative_budget_qualification"}
    coverage = {"schema_version": 1, "status": "accepted_in_the_explicitly_disclosed_scope",
                "release_wide_unqualified_certification": False,
                "scope": plan["scope"], "fresh_evidence": refs,
                "frozen_passage_ledgers": plan["frozen_passage_ledgers"],
                "excluded_historical_snapshot_inputs": plan["excluded_historical_snapshot_inputs"],
                "proof_environments": inventory["proof_environments"],
                "passage_bindings": coverage_rows,
                "literal_unproved_internal_claims": inventory["literal_unproved_internal_claims"],
                "provisional_row_supersessions": inventory["provisional_row_supersessions"],
                "optional_paragraph_supersession": inventory["optional_paragraph_supersession"],
                "count_policy": plan["count_policy"],
                "counts": {"distinct_canonical_accepted_units": len(canonical),
                           "qualified_canonical_units": len(qualified),
                           "additional_checked_binding_rows": sum(r["canonical_unit_id"] is None and bool(r["declarations"]) for r in coverage_rows),
                           "historical_obligation_only_rows": sum(r["binding_kind"] == "superseded_obligation" for r in coverage_rows),
                           "explicit_support_packet_link_rows": sum(r["binding_kind"] == "explicit_support_packet_links" for r in coverage_rows),
                           "total_fresh_passage_binding_rows": len(coverage_rows),
                           "all_exact_mapped_declarations": refs["target_count"]}}
    statements = read(root / "correspondence/statements.json")
    promotions = {r["statement_id"]: r for r in plan["statement_promotions"]}
    for row in statements["statements"]:
        if row["id"] in promotions:
            change = promotions[row["id"]]
            require(row["status"] == "open", "A promotion no longer starts open: " + row["id"])
            row["lean_declarations"] = change["declarations"]
            row["status"] = "proved_and_freshly_checked"
            row["reading_order_reviews"] = change["independent_reviews"]
            row["formalization_scope"] = change["formalization_scope"]
            row["printed_proof_status"] = change["printed_proof_status"]
        if row["status"].startswith("proved"):
            row["expanded_types"] = fresh_bindings(row["lean_declarations"], types, graph, refs)
            row["final_clean_binding"] = refs
            row["final_coverage"] = {"path": "correspondence/final-coverage.json",
                                     "statement_id": row["id"]}
    counts = {"unqualified_statements": sum(x["status"] == "proved_and_freshly_checked" for x in statements["statements"]),
              "qualified_statements": sum(x["status"] == "proved_with_explicit_nonnegative_budget_qualification" for x in statements["statements"]),
              "excluded_conjectures": sum(x["status"] == "excluded" for x in statements["statements"]),
              "proof_environments": len(inventory["proof_environments"])}
    require(counts == plan["expected_counts"], "Final statement counts disagree")
    e1 = next(x for x in statements["statements"] if x["id"] == "S-lem-maximum")
    require(e1["status"] == "proved_with_explicit_nonnegative_budget_qualification" and e1.get("qualification"),
            "E1 nonnegative-budget qualification was dropped")
    old_summary = copy.deepcopy(statements["summary"])
    statements["summary"].update(new_accepted_statement_correspondences=39,
                                  new_qualified_statement_correspondences=1,
                                  new_accepted_passage_correspondences=len(canonical - qualified),
                                  qualified_passage_correspondences=len(qualified),
                                  accepted_passages_with_documented_route_variation=len({r["canonical_unit_id"] for r in coverage_rows
                                      if r["canonical_unit_id"] is not None and r["correspondence_status"] in
                                      {"checked_with_documented_route_variation", "checked_alternative_route_support_with_explicit_H1_internal_bypass"}}),
                                  final_coverage_counts=coverage["counts"],
                                  historical_pre_final_passage_counts=old_summary,
                                  passage_count_scope=plan["count_policy"])
    statements["final_acceptance"] = {"path": "correspondence/final-acceptance.json",
                                      "unqualified_whole_printed_proof_claim": False}
    proofs = read(root / "correspondence/proof-environments.json")
    by_id = {x["proof_environment_id"]: x for x in inventory["proof_environments"]}
    for row in proofs["proof_environments"]:
        binding = by_id[row["id"]]
        row["status"] = binding["proposed_status_after_clean_replay"]
        row["subdivision_status"] = "Exact immutable passage pointers bound in final-coverage.json"
        row["passage_ids"] = list(dict.fromkeys(p["id"] for b in binding["candidate_detailed_bindings"] for p in b["passages"]))
        row["reading_order_reviews"] = binding["independent_reviews"]
        row["final_clean_binding"] = refs
        row["final_scope_notes"] = binding["scope_notes"]
        row["final_coverage"] = {"path": "correspondence/final-coverage.json", "proof_environment_id": row["id"]}
    proofs["coverage_note"] = plan["scope"]
    proofs["literal_unproved_internal_claims"] = inventory["literal_unproved_internal_claims"]
    table = "\n".join("| " + x["statement"] + " | " + ", ".join("`" + n.removeprefix(N) + "`" for n in x["lean_declarations"]) + " |"
                      for x in statements["statements"] if x["status"].startswith("proved"))
    status = f"""# Verification status

All 40 named results have checked Lean statements: 39 unqualified statements and Lemma E.1 with the explicit envelope-budget hypothesis A ≥ 0. Conjecture 1 is excluded.

The final clean proof commit is `{refs['source_commit']}`. Its Root build, forced source replay, all {refs['target_count']:,} exact mapped `pp.all` types, complete shared kernel axiom union and {refs['project_dependency_nodes']:,}-node closed project graph passed. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`; actual Kane providers are included in source replay and the graph.

All 34 explicit proof environments have frozen source-byte, declaration and independent-review bindings. The final sidecar records {len(canonical)} distinct canonical units and {coverage['counts']['additional_checked_binding_rows']} additional binding rows. These are enumerated correspondence units, not disjoint source intervals or an addition to historical passage totals. Frozen passage ledgers remain byte-identical, and all pre-acceptance registries are preserved.

The all-threshold Lemma H.1 bound uses genuine value continuity and Fatou after generic-threshold geometry. The printed nonsimple ridge Green identity at supplement1081–1100 is bypassed and remains unproved as a separate all-threshold internal claim. The arbitrary-edge spherical generality and raw unnormalized Hausdorff normalization are not silently certified. The fixed-b H.3 endpoint and canonical covariance-gap Corollary4 endpoint match the published quantifiers. The completed F4 duplication paragraph replaces its earlier support-only binding once.

Statement correctness, checked printed steps and documented alternative routes remain separate in [final-coverage.json](correspondence/final-coverage.json). This record does not claim unqualified certification of every printed internal identity. Earlier failed attempts, historical receipts and source/PDF reviews remain available.

| Paper statement | Checked endpoint(s) in `RectangleCLTArxivV1` |
|---|---|
{table}

See [final-acceptance.json](correspondence/final-acceptance.json) for the exact clean evidence and [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for pinned dependencies and collaborator access requirements.
"""
    readme = f"""# Frozen-source correspondence record

The frozen 16 November paper and Supplemental Material have 40 named results: 39 statements are proved and freshly checked without a new statement qualification; Lemma E.1 is separately checked with A ≥ 0. Conjecture 1 is excluded. All 34 explicit proof environments have exact source spans, immutable passage pointers, independent reviews and final clean evidence.

[statements.json](statements.json) records the actual checked endpoints and expanded types. [proof-environments.json](proof-environments.json) binds the 34 proof blocks. [final-coverage.json](final-coverage.json) records {len(canonical)} distinct canonical units and {coverage['counts']['additional_checked_binding_rows']} additional binding rows; its explicit count policy prevents supporting packets and F4 duplication from being counted twice. These units can overlap in source lines. The older aggregate passage counts remain historical.

The {len(plan['frozen_passage_ledgers'])} frozen detailed ledgers remain byte-identical. Authoritative final per-row statuses, source-byte hashes, types, kernel routes, reviews and explicit supersessions are appended in the sidecar. Complete shared-union axiom checking covers all {refs['target_count']:,} mapped names, with actual GenericChaining and Kane dependencies included. Historical archive candidates are not promoted by name harvesting.

The all-threshold H.1 statement follows an explicit continuity/Fatou variation. Its printed nonsimple ridge Green identity at supplement1081–1100 remains bypassed and unproved as a separate all-threshold internal claim. E.1 requires a nonnegative envelope budget. Consequently this record does not claim unqualified verification of every literal printed internal argument.

The source snapshot is `1803366cc994d9facae8e128ee180f68e319486f`; main SHA-256 `e96aaf12ca782c94d70587f128b58a20d3ace8b31a8c324a3272b2b1d71677a2`, supplement SHA-256 `5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb`. Inclusive-line hashes retain original UTF-8 line endings. [final-acceptance.json](final-acceptance.json) pins the final clean proof commit, receipts and complete pre-acceptance snapshot. [../REPRODUCIBILITY.md](../REPRODUCIBILITY.md) explains private dependency access.
"""
    acceptance = {"schema_version": 1, "status": "passed_with_explicit_scope_and_qualification",
                  "recorded_at_utc": now(), "release_wide_unqualified_certification": False,
                  "all_named_results_covered_under_disclosed_E1_qualification": True,
                  "every_literal_printed_internal_claim_certified": False,
                  "counts": counts, "fresh_evidence": refs, "coverage_counts": coverage["counts"],
                  "count_policy": plan["count_policy"],
                  "literal_unproved_internal_claims": inventory["literal_unproved_internal_claims"],
                  "statement_promotions": plan["statement_promotions"],
                  "frozen_passage_ledgers": plan["frozen_passage_ledgers"],
                  "qualified_E1": {"statement_id": "S-lem-maximum", "required_hypothesis": "0 ≤ A",
                                   "qualification": e1["qualification"]}}
    return {"correspondence/statements.json": statements,
            "correspondence/proof-environments.json": proofs,
            "correspondence/final-coverage.json": coverage,
            "correspondence/final-acceptance.json": acceptance,
            "STATUS.md": status, "correspondence/README.md": readme}


def record(args):
    root, out = args.root.resolve(), args.out.resolve()
    plan_path = args.plan.resolve()
    plan = read(plan_path)
    inventory = verify_plan(root, plan)
    require(sha(args.mapping_plan) == plan["mapping_plan"]["sha256"], "Acceptance mapping plan changed")
    require(read(args.mapping_plan)["source_commit"] == plan["final_proof_commit"],
            "Acceptance plan selects a different final proof commit")
    types, graph, refs = verify_mapping(root, args.mapping_plan, args.mapping_run,
                                       args.clean_run or args.mapping_run, plan["expected_mapped_targets"])
    outputs = build_outputs(root, plan, inventory, types, graph, refs)
    require(not out.exists(), "Candidate output directory already exists")
    out.mkdir(parents=True)
    for path in plan["pre_acceptance_identity"]:
        target = out / "pre-acceptance" / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / path, target)
    snapshot = {p: sha(out / "pre-acceptance" / p) for p in plan["pre_acceptance_identity"]}
    require(snapshot == plan["pre_acceptance_identity"], "Pre-acceptance snapshot mismatch")
    write(out / "pre-acceptance-manifest.json", snapshot)
    outputs["correspondence/final-acceptance.json"].update(
        acceptance_plan=reference(root, plan_path), pre_acceptance_snapshot={
            "manifest": reference(root, out / "pre-acceptance-manifest.json"),
            "file_count": len(snapshot), "preserved_every_correspondence_json": True})
    historical = {name: {"snapshot": reference(root, out / "pre-acceptance" / name),
                          "scope": value["scope"]}
                  for name, value in plan["excluded_historical_snapshot_inputs"].items()}
    outputs["correspondence/final-coverage.json"]["excluded_historical_snapshot_inputs"] = historical
    outputs["correspondence/final-acceptance.json"]["excluded_historical_snapshot_inputs"] = historical
    for name, data in outputs.items():
        target = out / "outputs" / name
        if isinstance(data, str):
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(data)
        else:
            write(target, data)
    accepted = outputs["correspondence/final-acceptance.json"]
    accepted["accepted_output_sha256"] = {p: sha(out / "outputs" / p) for p in outputs
                                         if p != "correspondence/final-acceptance.json"}
    write(out / "outputs/correspondence/final-acceptance.json", accepted)
    verify_plan(root, plan)
    receipt = {"status": "passed_candidate_waiting_for_root_approval",
               "created_at_utc": now(), "global_files_changed": False,
               "plan": reference(root, plan_path), "recorder": reference(root, Path(__file__)),
               "pre_acceptance_manifest": reference(root, out / "pre-acceptance-manifest.json"),
               "pre_acceptance_identity": snapshot, "fresh_evidence": refs,
               "output_sha256": {p: sha(out / "outputs" / p) for p in outputs},
               "frozen_passage_ledgers": plan["frozen_passage_ledgers"],
               "apply_requires_exact_candidate_receipt_sha256": True}
    write(out / "receipt.json", receipt)
    print(json.dumps({"candidate": str(out / "receipt.json"), "sha256": sha(out / "receipt.json"),
                      "status": receipt["status"]}))


def apply(args):
    root, candidate = args.root.resolve(), args.candidate.resolve()
    require(sha(candidate) == args.approved_receipt_sha256, "Candidate receipt approval hash differs")
    receipt = read(candidate)
    require(receipt["status"] == "passed_candidate_waiting_for_root_approval", "Candidate has not passed")
    snapshot_path = candidate.parent / "pre-acceptance-manifest.json"
    require(sha(snapshot_path) == receipt["pre_acceptance_manifest"]["sha256"],
            "Preservation manifest changed")
    require(read(snapshot_path) == receipt["pre_acceptance_identity"], "Preservation inventory differs")
    for name, expected in receipt["pre_acceptance_identity"].items():
        require(sha(candidate.parent / "pre-acceptance" / name) == expected,
                "Preserved pre-acceptance file changed: " + name)
    verify_hashes(root, receipt["pre_acceptance_identity"])
    verify_hashes(root, receipt["frozen_passage_ledgers"])
    require(set(receipt["output_sha256"]) == OUTPUTS, "Unexpected mutation target")
    plan_path = existing_path(root, receipt["plan"]["path"])
    require(sha(plan_path) == receipt["plan"]["sha256"], "Candidate plan changed")
    plan = read(plan_path)
    verify_plan(root, plan)
    require(sha(__file__) == receipt["recorder"]["sha256"], "Recorder changed after candidate review")
    fresh = receipt["fresh_evidence"]
    for item in fresh.values():
        if isinstance(item, dict) and "path" in item and "sha256" in item:
            require(sha(existing_path(root, item["path"])) == item["sha256"], "Approved fresh evidence changed")
    require(fresh["mapping_plan"]["sha256"] == plan["mapping_plan"]["sha256"] and
            fresh["source_commit"] == plan["final_proof_commit"], "Approved clean proof scope changed")
    _, _, rechecked_refs = verify_mapping(root, existing_path(root, fresh["mapping_plan"]["path"]),
                   existing_path(root, fresh["mapping_checkpoint"]["path"]),
                   existing_path(root, fresh["clean_checkpoint"]["path"]),
                   plan["expected_mapped_targets"])
    require(rechecked_refs == fresh, "Fresh evidence bindings drifted after candidate review")
    for name, expected in receipt["output_sha256"].items():
        require(sha(candidate.parent / "outputs" / name) == expected, "Candidate output changed: " + name)
        require(name in receipt["pre_acceptance_identity"] or not (root / name).exists(),
                "New acceptance output already exists: " + name)
    written = []
    try:
        for name in sorted(OUTPUTS):
            target = root / name
            temporary = target.with_name(target.name + ".final-acceptance-tmp")
            shutil.copyfile(candidate.parent / "outputs" / name, temporary)
            os.replace(temporary, target)
            written.append(name)
        verify_hashes(root, receipt["frozen_passage_ledgers"])
    except Exception:
        for name in written:
            if name in receipt["pre_acceptance_identity"]:
                shutil.copyfile(candidate.parent / "pre-acceptance" / name, root / name)
            else:
                (root / name).unlink(missing_ok=True)
        raise
    write(candidate.parent / "applied.json", {"status": "applied", "applied_at_utc": now(),
          "approved_receipt_sha256": args.approved_receipt_sha256,
          "output_sha256": receipt["output_sha256"], "frozen_passage_ledgers_unchanged": True})
    print(json.dumps({"status": "applied", "files": sorted(OUTPUTS)}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare", help="write an immutable proposed plan; no global changes")
    p.add_argument("--inventory", type=Path, required=True)
    p.add_argument("--mapping-plan", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.set_defaults(action=prepare)
    p = sub.add_parser("record", help="verify clean evidence and write candidate outputs only")
    p.add_argument("--plan", type=Path, required=True)
    p.add_argument("--mapping-plan", type=Path, required=True)
    p.add_argument("--mapping-run", type=Path, required=True)
    p.add_argument("--clean-run", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.set_defaults(action=record)
    p = sub.add_parser("apply", help="apply exactly the root-approved candidate receipt")
    p.add_argument("--candidate", type=Path, required=True)
    p.add_argument("--approved-receipt-sha256", required=True)
    p.set_defaults(action=apply)
    args = parser.parse_args()
    args.action(args)


if __name__ == "__main__":
    main()
