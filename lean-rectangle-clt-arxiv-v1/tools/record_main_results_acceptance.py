#!/usr/bin/env python3
"""Bind remaining main results and reviewed G2/H2 components to fresh evidence.

The qualified envelope-maximum statement is deliberately counted separately.
The clean two-source extension reuses byte-identical base proof sources.
"""
import datetime
import hashlib
import json
import shutil
from record_transfers_lower_acceptance import PROJECT, HERE, read, sha, rel, write

RUN = PROJECT / "evidence/main-results-clean-checkpoint/run.json"
MAPPING = PROJECT / "evidence/main-results-clean-mapping/receipt.json"


def main():
    run, mapping = read(RUN), read(MAPPING)
    assert run["status"] == mapping["status"] == "passed"
    assert not run["initial_git_status"] and not mapping["initial_git_status"]
    assert mapping["base_clean_checkpoint"]["sha256"] == sha(RUN)
    assert mapping["base_source_identity_unchanged"]
    for f, expected in run["source_identity"]["files"].items():
        assert sha(PROJECT / f) == expected, f
    for f, expected in mapping["additional_source_identity"].items():
        path = __import__("pathlib").Path(f)
        assert sha(path if path.is_absolute() else PROJECT / path) == expected, f
    for receipt in (run, mapping):
        for row in receipt["commands"]:
            assert row["exit_code"] == 0
            log = RUN.parent / row["log"] if receipt is run else PROJECT / row["log"]
            assert sha(log) == row["log_sha256"]
    assert read(RUN.parent / "dependency-check.json")["passed"]
    export = PROJECT / mapping["log"]
    assert sha(export) == mapping["log_sha256"]
    data = read(export)
    types = {r["name"]: r for r in data["endpoints"]}
    graph = {r["name"]: r["direct_project_dependencies"] for r in data["project_dependency_graph"]}
    assert len(types) == mapping["targets"]
    blocked = {"RectangleCLT.Companion.SplitV4.relativeFourthMomentCLT",
               "RectangleCLT.Companion.SplitV4.polynomialMomentCLTExists"}
    assert not blocked.intersection(graph)
    build = {"path": rel(RUN), "sha256": sha(RUN), "source_commit": run["source_commit"],
             "status": "passed", "initial_checkout_clean": True,
             "source_digest": run["source_identity"]["aggregate_sha256"],
             "clean_support_extension": {"path": rel(MAPPING), "sha256": sha(MAPPING),
                 "source_commit": mapping["source_commit"], "unchanged_base_sources": True}}
    command = next(r for r in run["commands"] if r["label"] == "c2-audit")
    log = RUN.parent / command["log"]
    audit = {"run": rel(RUN), "log": rel(log), "log_sha256": sha(log), "exit_code": 0,
             "allowed_axioms": mapping["allowed_axioms"],
             "strict_passage_audit": {"path": rel(MAPPING), "sha256": sha(MAPPING)}}
    reviews = {
        "t3": ["evidence/skew-lower-intrinsic/independent-lower-resume-review.json"],
        "t8": ["evidence/lower-sparse-numeric-independent-review.md",
               "evidence/lower-sparse-theorem/independent-intrinsic-wrapper-review.json",
               "evidence/lower-sparse-reading-order/independent-intrinsic-review.json"],
        "f123": ["evidence/lower-lemmas-f1-f3/independent-intrinsic-review.json"],
        "e1": ["evidence/expected-maximum-envelope/independent-review.json"],
        "g2": ["evidence/cap-concentration/independent-intrinsic-review.json"],
        "h2": ["evidence/supplemental-h-gaussian/independent-root-review.json"],
        "b12": ["evidence/seeded-identity-restoration/independent-root-review.json"],
    }
    for paths in reviews.values():
        for f in paths:
            path = PROJECT / f
            if path.suffix == ".md":
                assert "PASS" in path.read_text()
                continue
            d = read(path)
            assert "pass" in (d.get("status", "") + d.get("conclusion", "")).lower(), f
            assert not d.get("issues", []) and not d.get("headline_hypothesis_gap")
            for field in ("reviewed_source_hashes", "reviewed_source_sha256", "frozen_lean_sources"):
                for source, expected in d.get(field, {}).items():
                    if isinstance(expected, str) and len(expected) == 64:
                        assert sha(PROJECT / source) == expected, (f, source)

    def reviewed(key):
        return [{"path": f, "sha256": sha(PROJECT / f), "result": "PASS"} for f in reviews[key]]

    def expanded(names):
        return [{"declaration": n, "expanded_type": types[n]["expanded_type"], "export": rel(export)} for n in names]

    def deps(names):
        return [{"declaration": n, "direct_dependencies": types[n]["direct_dependencies"],
                 "direct_project_dependencies": graph[n], "transitive_project_graph": rel(export)} for n in names]

    files = {"skew-lower-intrinsic-passages.json": "t3", "lower-sparse-f6-passages.json": "t8",
             "lower-lemmas-f1-f3-passages.json": "f123", "expected-maximum-passages.json": "e1",
             "cap-concentration-passages.json": "g2", "supplemental-h-gaussian-passages.json": "h2",
             "seeded-identity-restoration-passages.json": "b12"}
    backup = PROJECT / "evidence/main-results-reviewed-ledgers"
    backup.mkdir(exist_ok=True)
    variations = {"B1.signed-hessian", "B1.same-copy", "F1.saddlepoint", "F1.relative-log-error",
                  "H2.COVARIANCE", "H2.NUCLEAR", "H2.PROJECTED_MEAN"}
    passage_keys = {}
    for filename, key in files.items():
        path = HERE / filename
        if not (backup / filename).exists():
            shutil.copyfile(path, backup / filename)
        d = read(path)
        for row in d["passages"]:
            loc = row.get("location")
            if loc is None:
                source = d["frozen_source"]["tex_file"].removeprefix("../")
                a, b = row["tex_lines"]
                content = b"".join((PROJECT.parent / source).read_bytes().splitlines(keepends=True)[a-1:b])
                loc = {"source": "main", "path": source, "lines": [a, b],
                       "sha256": hashlib.sha256(content).hexdigest()}
                row["location"] = loc
            a, b = loc["lines"]
            content = b"".join((PROJECT.parent / loc["path"]).read_bytes().splitlines(keepends=True)[a-1:b])
            assert hashlib.sha256(content).hexdigest() == loc["sha256"], row["id"]
            names = next(row[k] for k in ("lean_endpoints", "lean_declarations", "mapped_declarations", "new_declarations") if k in row)
            names = [n if isinstance(n, str) else n["declaration"] for n in names]
            assert set(names) <= types.keys(), row["id"]
            status = ("checked_with_explicit_nonnegative_budget_qualification" if key == "e1" else
                      "checked_with_documented_route_variation" if key == "g2" or row["id"] in variations else
                      "checked_printed_proof")
            if row.get("status") != status:
                row.setdefault("status_history", []).append(row.get("status", row.get("inclusion_status")))
            row.update(status=status, new_declarations=names, expanded_types=expanded(names),
                       dependency_bindings=deps(names), clean_build_receipt=build,
                       transitive_axiom_receipt=audit, reading_order_reviews=reviewed(key))
            passage_keys[row["id"]] = key
        d["clean_integrated_checkpoint"] = build
        d["pre_acceptance_ledger"] = {"path": rel(backup / filename), "sha256": sha(backup / filename)}
        write(path, d)
    targets = {
        "S-opt-skew-lower": ("t3", ["theorem_3_intrinsic", "theorem_3_intrinsic_positive_dimensions"]),
        "S-lower-sparse": ("t8", ["theorem_8_sparse_polynomial_moment_lower", "theorem_8_sparse_polynomial_moment_two_sided"]),
        "S-opt-moderate-tail": ("f123", ["lemma_F_1_uniform_scalar_moderate_tail"]),
        "S-lower-shift-comparison": ("f123", ["lemma_F_2_independently_shifted_variables"]),
        "S-lower-family-properties": ("f123", ["lemma_F_3_common_symmetric_construction"]),
        "S-appx-an-lem-identity": ("b12", ["lemma_B1_gaussian_seed_interpolation"]),
        "S-appx-an-lem-restoration": ("b12", ["lemma_B2_intrinsic_paired_restoration"]),
        "S-lem-cap-concentration": ("g2", ["cap_one_projection_small_interval_nonneg", "cap_two_projection_small_box_nonneg"]),
        "S-hgap-lem-gaussian": ("h2", ["lemma_H2_gaussian_matrix", "lemma_H2_projected_reference"]),
        "S-lem-maximum": ("e1", ["lemma_E1_expected_maximum"]),
    }
    statements = read(HERE / "statements.json")
    for row in statements["statements"]:
        if row["id"] not in targets:
            continue
        key, ns = targets[row["id"]]
        names = ["RectangleCLTArxivV1." + n for n in ns]
        row.update(status="proved_with_explicit_nonnegative_budget_qualification" if key == "e1" else "proved_and_freshly_checked",
                   lean_declarations=names, expanded_types=expanded(names), dependency_declarations=deps(names),
                   build_receipt=build, audit_receipt=audit, reading_order_reviews=reviewed(key),
                   printed_proof_status="checked_mapped_passages_with_explicit_method_notes")
        if key == "e1":
            row["qualification"] = "The envelope budget A is nonnegative. The unrestricted-real-budget statement is false; a checked negative-budget obstruction and the corrected actual theorem are recorded separately."
    all_files = ["c2-passages.json", "intrinsic-main-passages.json", "a1-passages.json", "b3-passages.json",
                 "theorem-2-envelope-passages.json", "paired-intrinsic-passages.json",
                 "subexponential-intrinsic-passages.json", "polyhedral-intrinsic-passages.json", "lower-fourth-dense-passages.json", *files]
    rows = [r for f in all_files for r in read(HERE / f)["passages"]]
    statements["summary"].update(
        new_accepted_statement_correspondences=sum(r["status"] == "proved_and_freshly_checked" for r in statements["statements"]),
        new_qualified_statement_correspondences=sum(r["status"] == "proved_with_explicit_nonnegative_budget_qualification" for r in statements["statements"]),
        new_accepted_passage_correspondences=sum(r["status"] in ("checked_printed_proof", "checked_with_documented_route_variation") for r in rows),
        qualified_passage_correspondences=sum(r["status"] == "checked_with_explicit_nonnegative_budget_qualification" for r in rows),
        accepted_passages_with_documented_route_variation=sum(r["status"] == "checked_with_documented_route_variation" for r in rows))
    write(HERE / "statements.json", statements)
    proofs = read(HERE / "proof-environments.json")
    prefixes = {"P-main-04": ["B1."], "P-main-05": ["B2."], "P-main-15": ["E1."],
                "P-main-20": ["F1."], "P-main-21": ["T3.", "F2.SKEW"], "P-main-22": ["F2."],
                "P-main-23": ["F3."], "P-supplement-24": ["G2."], "P-supplement-28": ["H2."]}
    for row in proofs["proof_environments"]:
        if row["id"] in prefixes:
            ids = [r["id"] for r in rows if any(r["id"].startswith(s) for s in prefixes[row["id"]])]
            if not ids:
                continue
            row.update(status="checked_with_explicit_nonnegative_budget_qualification" if row["id"] == "P-main-15" else
                       "checked_with_documented_route_variation" if row["id"] in ("P-main-04", "P-main-20", "P-supplement-24", "P-supplement-28") else "checked_printed_proof",
                       passage_ids=ids, build_receipt=build, audit_receipt=audit)
    write(HERE / "proof-environments.json", proofs)
    write(HERE / "main-results-acceptance.json", {"recorded_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "release_wide_certification": False, "scope": "Theorems3/8, B1/B2, F1–F3, G2/H2, and qualified E1",
        "build": build, "audit": audit, "summary": statements["summary"],
        "remaining_scope": "Full supplemental surface, matrix, complementary/cap and correlation-gap acceptance remains separate, as do unbound internal passages.",
        "ledgers": {f: sha(HERE / f) for f in ["statements.json", "proof-environments.json", *files]}})
    print(statements["summary"])


if __name__ == "__main__":
    main()
