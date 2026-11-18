#!/usr/bin/env python3
"""Bind six reviewed statements and 39 passages to the clean Theorem 2 run.

This records source identities and Lean evidence. It neither performs a
mathematical review nor certifies the remaining manuscript and supplement.
"""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
HERE = PROJECT / "correspondence"
RUN = PROJECT / "evidence/theorem2-clean-checkpoint/run.json"
MAPPING = PROJECT / "evidence/theorem2-clean-mapping/receipt.json"
REVIEWS = {
    "envelope": PROJECT / "evidence/theorem-2-envelope-review/checkpoint-2.json",
    "paired": PROJECT / "evidence/paired-intrinsic/independent-expectation-review.json",
    "threshold": PROJECT / "evidence/averaged-threshold-intrinsic/independent-review.json",
}


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path):
    return str(path.relative_to(PROJECT))


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    run = read(RUN)
    assert run["status"] == "passed" and not run["initial_git_status"]
    assert run["scope"] == "Entire exported checked import closure"
    for name, expected in run["source_identity"]["files"].items():
        assert sha(PROJECT / name) == expected, name
    commands = {row["label"]: row for row in run["commands"]}
    for row in commands.values():
        assert row["exit_code"] == 0, row["label"]
        assert sha(RUN.parent / row["log"]) == row["log_sha256"]
    assert read(RUN.parent / "dependency-check.json")["passed"]
    for key, path in REVIEWS.items():
        data = read(path)
        assert data["status"] == "PASS", key
        identities = data.get("reviewed_source_hashes", data.get("reviewed_sources"))
        if identities is None:
            identities = {data["source"]: data["source_sha256"]}
        for name, expected in identities.items():
            assert sha(PROJECT / name) == expected, (key, name)
    mapped = read(MAPPING)
    assert mapped["exit_code"] == 0 and not mapped["initial_git_status"]
    assert mapped["source_commit"] == run["source_commit"]
    assert sha(PROJECT / mapped["harness"]) == mapped["harness_sha256"]
    assert sha(PROJECT / mapped["log"]) == mapped["log_sha256"]
    export = PROJECT / mapped["log"]
    data = read(export)
    graph = {r["name"]: r["direct_project_dependencies"]
             for r in data["project_dependency_graph"]}
    types = {r["name"]: r for r in data["endpoints"]}
    build = {"path": rel(RUN), "sha256": sha(RUN),
             "source_commit": run["source_commit"],
             "source_digest": run["source_identity"]["aggregate_sha256"],
             "initial_checkout_clean": True, "status": "passed"}
    audit_log = RUN.parent / commands["c2-audit"]["log"]
    audit = {"run": rel(RUN), "log": rel(audit_log),
             "log_sha256": sha(audit_log), "exit_code": 0,
             "allowed_axioms": mapped["allowed_axioms"],
             "passage_endpoint_audit": {"receipt": rel(MAPPING), "sha256": sha(MAPPING)},
             "note": "Historical c2-audit command label checks the entire exported target list."}

    def expanded(names):
        return [{"declaration": n, "expanded_type": types[n]["expanded_type"],
                 "export": rel(export)} for n in names]

    def dependencies(names):
        return [{"declaration": n, "direct_dependencies": types[n]["direct_dependencies"],
                 "direct_project_dependencies": graph[n],
                 "transitive_project_graph": rel(export), "export": rel(export)} for n in names]

    pins = read(PROJECT / "source-pins.json")
    frozen = {}
    passage_ids = {}
    filenames = ["theorem-2-envelope-passages.json", "paired-intrinsic-passages.json"]
    for filename in filenames:
        path = HERE / filename
        ledger = read(path)
        key = "envelope" if filename.startswith("theorem") else "paired"
        review = {"path": rel(REVIEWS[key]), "sha256": sha(REVIEWS[key]), "result": "PASS"}
        for row in ledger["passages"]:
            loc = row["location"]
            source = loc["path"]
            if source not in frozen:
                frozen[source] = subprocess.check_output(
                    ["git", "show", pins["paper_commit"] + ":" + source], cwd=PROJECT.parent)
            start, end = loc["lines"]
            content = b"".join(frozen[source].splitlines(keepends=True)[start-1:end])
            assert hashlib.sha256(content).hexdigest() == loc["sha256"], row["id"]
            names = row.get("lean_endpoints", row.get("lean_declarations"))
            assert names and set(names) <= types.keys(), row["id"]
            if row["status"] != "checked_printed_proof":
                row.setdefault("status_history", []).append(row["status"])
            row.update(status="checked_printed_proof", expanded_types=expanded(names),
                       dependency_bindings=dependencies(names), clean_build_receipt=build,
                       transitive_axiom_receipt=audit, reading_order_review=review)
            statement = row.get("statement_id", ledger.get("statement_id"))
            if statement:
                passage_ids.setdefault(statement, []).append(row["id"])
        ledger["clean_integrated_checkpoint"] = build
        write(path, ledger)

    targets = {
        "S-thm-polynomial": ["theorem_2_i_intrinsic", "theorem_2_ii_intrinsic",
                              "theorem_2_intrinsic", "theorem_2_intrinsic_with_min"],
        "S-appx-an-lem-threshold": ["lemma_B5_intrinsic_threshold"],
        "S-ben-comparison": ["lemma_E2_intrinsic_comparison"],
        "S-ben-smoothing": ["lemma_E3_intrinsic_smoothing"],
        "S-ben-paired-interpolation": ["lemma_E4_paired_slepian"],
        "S-ben-maximum": ["lemma_E5_truncated_bennett_maximum",
                           "lemma_E5_truncated_bennett_maximum_zero_variance"],
    }
    statements = read(HERE / "statements.json")
    for row in statements["statements"]:
        if row["id"] not in targets:
            continue
        names = ["RectangleCLTArxivV1." + n for n in targets[row["id"]]]
        key = "threshold" if row["id"] == "S-appx-an-lem-threshold" else "paired"
        reviews = [REVIEWS["envelope"], REVIEWS["paired"]] if row["id"] == "S-thm-polynomial" else [REVIEWS[key]]
        row.update(status="proved_and_freshly_checked", lean_declarations=names,
                   expanded_types=expanded(names), dependency_declarations=dependencies(names),
                   build_receipt=build, audit_receipt=audit,
                   reading_order_reviews=[{"path": rel(p), "sha256": sha(p), "result": "PASS"} for p in reviews],
                   formalization_scope="Checked displayed statement; detailed printed-proof coverage is a separate field.")
        row["proof_passage_ids"] = passage_ids.get(row["id"], [])
        row["printed_proof_status"] = ("checked_mapped_passages" if row["proof_passage_ids"] else
                                        "semantic_review_passed_detailed_passage_binding_open")
    statements["summary"]["new_accepted_statement_correspondences"] = sum(
        r["status"] == "proved_and_freshly_checked" for r in statements["statements"])
    all_ledgers = ["c2-passages.json", "intrinsic-main-passages.json", "a1-passages.json", "b3-passages.json", *filenames]
    statements["summary"]["new_accepted_passage_correspondences"] = sum(
        r["status"] == "checked_printed_proof" for f in all_ledgers for r in read(HERE / f)["passages"])
    write(HERE / "statements.json", statements)
    proofs = read(HERE / "proof-environments.json")
    environments = {"P-main-17": "S-ben-paired-interpolation",
                    "P-main-18": "S-ben-comparison", "P-main-19": "S-ben-maximum"}
    for row in proofs["proof_environments"]:
        if row["id"] in environments:
            statement = environments[row["id"]]
            row.update(status="checked_printed_proof", passage_ids=passage_ids[statement],
                       statement_ids=[statement], build_receipt=build, audit_receipt=audit)
    write(HERE / "proof-environments.json", proofs)
    write(HERE / "theorem2-acceptance.json", {
        "recorded_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Theorem 2, Lemmas B.5 and E.2–E.5, and 39 mapped passages",
        "release_wide_certification": False, "source_commit": run["source_commit"],
        "build": build, "audit": audit, "summary": statements["summary"],
        "remaining_coverage": "Lower constructions, other transfers, supplement, and unbound internal passages remain open.",
        "ledgers": {f: sha(HERE / f) for f in ["statements.json", "proof-environments.json", *filenames]}})
    print("Recorded", statements["summary"]["new_accepted_statement_correspondences"],
          "checked statements and", statements["summary"]["new_accepted_passage_correspondences"], "mapped passages.")


if __name__ == "__main__":
    main()
