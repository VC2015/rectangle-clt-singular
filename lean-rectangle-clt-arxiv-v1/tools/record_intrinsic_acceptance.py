#!/usr/bin/env python3
"""Bind reviewed intrinsic statements/passages to the recorded clean run.

Statement correctness and full printed-passage coverage are separate fields.
This tool records evidence; it does not replace mathematical review or Lean.
"""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
HERE = PROJECT / "correspondence"
RUN = PROJECT / "evidence/intrinsic-clean-checkpoint-2/run.json"
MAIN_REVIEW = PROJECT / "evidence/intrinsic-main-review/independent-review.json"
A1_REVIEW = PROJECT / "evidence/intrinsic-smoothing/independent-review-a1-recheck.json"
B3_REVIEW = PROJECT / "evidence/intrinsic-smoothing/b3-printed/independent-review.json"
MAPPING = PROJECT / "evidence/intrinsic-clean-mapping-checks/receipt.json"


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
        assert row["exit_code"] == 0
        assert sha(RUN.parent / row["log"]) == row["log_sha256"]
    review = read(MAIN_REVIEW)
    assert not review["open_issues"]
    for name, expected in review["lean_source_identity"].items():
        assert sha(PROJECT / name) == expected, name
    for path in (A1_REVIEW, B3_REVIEW):
        data = read(path)
        assert data.get("result", data.get("status")) == "PASS_SAME_PRINTED_ARGUMENT" and not data.get("issues", [])
        identities = data["source_sha256"]
        if isinstance(identities, str):
            identities = {data["source_path"]: identities}
        for name, expected in identities.items():
            assert sha(PROJECT / name) == expected, name
    mapped = read(MAPPING)
    assert mapped["exit_code"] == 0 and mapped["source_commit"] == run["source_commit"]
    assert sha(PROJECT / mapped["harness"]) == mapped["harness_sha256"]
    assert sha(PROJECT / mapped["log"]) == mapped["log_sha256"]
    exports = [RUN.parent / commands["dependencies"]["log"],
               RUN.parent / commands["mapped-A1"]["log"],
               RUN.parent / commands["mapped-B3"]["log"], PROJECT / mapped["log"]]
    types = {}
    for path in exports:
        data = read(path)
        graph = {row["name"]: row["direct_project_dependencies"]
                 for row in data["project_dependency_graph"]}
        for row in data["endpoints"]:
            types[row["name"]] = dict(row, export=rel(path),
                                      direct_project_dependencies=graph[row["name"]])
    build = {"path": rel(RUN), "sha256": sha(RUN), "source_commit": run["source_commit"],
             "source_digest": run["source_identity"]["aggregate_sha256"],
             "initial_checkout_clean": True, "status": "passed"}
    audit_command = commands["c2-audit"]
    audit_log = RUN.parent / audit_command["log"]
    audit = {"run": rel(RUN), "log": rel(audit_log), "log_sha256": sha(audit_log),
             "exit_code": 0, "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
             "note": "The historical command label c2-audit now checks the full exported target list."}

    def expanded(names):
        return [{"declaration": name, "expanded_type": types[name]["expanded_type"],
                 "export": types[name]["export"]} for name in names]

    def bindings(names):
        return [{"declaration": name, "direct_dependencies": types[name]["direct_dependencies"],
                 "direct_project_dependencies": types[name]["direct_project_dependencies"],
                 "transitive_project_graph": types[name]["export"],
                 "export": types[name]["export"]} for name in names]

    files = ["intrinsic-main-passages.json", "a1-passages.json", "b3-passages.json"]
    pins = read(PROJECT / "source-pins.json")
    frozen_sources = {}

    def check_location(location):
        path = location["path"]
        if path not in frozen_sources:
            frozen_sources[path] = subprocess.check_output(
                ["git", "show", pins["paper_commit"] + ":" + path], cwd=PROJECT.parent)
        start, end = location["lines"]
        content = b"".join(frozen_sources[path].splitlines(keepends=True)[start-1:end])
        assert hashlib.sha256(content).hexdigest() == location["sha256"], location

    for filename in files:
        path = HERE / filename
        ledger = read(path)
        for row in ledger["passages"]:
            check_location(row["location"])
            if row["id"] == "P1.D0":
                if row["status"] != "checked_printed_proof":
                    row.setdefault("history", []).append(
                        {"status": row["status"], "inference": row["inference"]})
                row["new_declarations"] = [
                    "RectangleCLTArxivV1.thresholdEnvelope_le_common_threshold_difference",
                    "RectangleCLTArxivV1.smallerEnvelope_le_threshold_integral"]
                row["inference"] = "Literal common-shift window h, logarithmic envelope derivative, and two FTC integrations give the printed e/2 comparison."
                row["scope_constraints"] = ["The former h log 2 numerical variant is superseded by the literal printed argument."]
            names = row["new_declarations"]
            assert names and set(names) <= types.keys(), row["id"]
            row.update(status="checked_printed_proof", expanded_types=expanded(names),
                       dependency_bindings=bindings(names), clean_build_receipt=build,
                       transitive_axiom_receipt=audit)
            if "build_receipts" in row:
                if "historical_build_receipts" not in row:
                    row["historical_build_receipts"] = row["build_receipts"]
                row["build_receipts"] = [build]
            review_path = MAIN_REVIEW if filename.startswith("intrinsic-main") else (
                A1_REVIEW if filename.startswith("a1") else B3_REVIEW)
            row["reading_order_review"] = {"path": rel(review_path), "sha256": sha(review_path),
                                           "result": "PASS", "passage": row["id"]}
            if "statement_acceptance" in row:
                row["statement_acceptance"] = "Bound to the clean exported checkpoint; release-wide coverage remains open."
        write(path, ledger)

    targets = {
        "S-thm-unrestricted": ["theorem_1_intrinsic_clt", "intrinsicFourthMomentCLT_factor_exists"],
        "S-cor-observations": ["corollary_1_normalized_observations"],
        "S-lem-concentration": ["lemma_1_bounded_model", "lemma_C1_gaussian_model"],
        "S-lem-endpoint": ["lemma_2_smoothing_error"],
        "S-an-prop-derivative": ["proposition_1_intrinsic_derivatives"],
        "S-appx-lem-envelope": ["integral_logisticEnvelope_intrinsic", "averaged_translated_derivative_intrinsic"],
        "S-appx-an-lem-mean": ["gaussian_mean_relative_to_single_face"],
        "S-appx-an-lem-matrix": ["logistic_matrix_estimate_intrinsic", "selector_nuclear_bound_intrinsic_paper"],
        "S-appx-lem-cube-boundary": ["lemma_C1_rademacher_boundary", "lemma_C1_rademacher_maximum"],
    }
    full_passages = {}
    passage_statement = {}
    for filename in files:
        for row in read(HERE / filename)["passages"]:
            full_passages.setdefault(row["statement_id"], []).append(row["id"])
            passage_statement[row["id"]] = row["statement_id"]
    statements = read(HERE / "statements.json")
    for row in statements["statements"]:
        if row["id"] not in targets:
            continue
        names = ["RectangleCLTArxivV1." + name for name in targets[row["id"]]]
        row.update(status="proved_and_freshly_checked", lean_declarations=names,
                   expanded_types=expanded(names), dependency_declarations=bindings(names),
                   build_receipt=build, audit_receipt=audit,
                   reading_order_review={"path": rel(MAIN_REVIEW), "sha256": sha(MAIN_REVIEW)})
        if row["id"] in full_passages:
            row["proof_passage_ids"] = full_passages[row["id"]]
            row["printed_proof_status"] = "checked_mapped_passages"
        else:
            row["printed_proof_status"] = "semantic_review_passed_detailed_passage_binding_open"
        row["formalization_scope"] = (
            "Concrete Gaussian factor law; arbitrary singular factors are allowed. "
            "The Gaussian representation differences and detailed archive reuse remain explicit in the side ledgers."
            if row["id"] == "S-lem-concentration" else
            "Checked displayed statement; detailed printed-proof coverage is a separate field.")
    statements["summary"]["new_accepted_statement_correspondences"] = sum(
        row["status"] == "proved_and_freshly_checked" for row in statements["statements"])
    statements["summary"]["new_accepted_passage_correspondences"] = sum(
        row["status"] == "checked_printed_proof"
        for filename in ["c2-passages.json", *files] for row in read(HERE / filename)["passages"])
    write(HERE / "statements.json", statements)
    proofs = read(HERE / "proof-environments.json")
    environment_passages = {
        "P-main-01": ["M1." + str(i) for i in range(1, 8)],
        "P-main-03": ["A1." + str(i) for i in range(1, 5)],
        "P-main-07": ["B3." + str(i) for i in range(1, 5)],
    }
    for row in proofs["proof_environments"]:
        if row["id"] in environment_passages:
            row.update(status="checked_printed_proof", passage_ids=environment_passages[row["id"]],
                       statement_ids=sorted({passage_statement[p] for p in environment_passages[row["id"]]}),
                       build_receipt=build, audit_receipt=audit)
    write(HERE / "proof-environments.json", proofs)
    write(HERE / "intrinsic-acceptance.json", {
        "recorded_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Intrinsic statements and mapped passages only", "release_wide_certification": False,
        "source_commit": run["source_commit"], "build": build, "audit": audit,
        "summary": statements["summary"],
        "remaining_coverage": "Theorem 2, lower constructions, supplement, and unbound internal passages remain outside this acceptance record.",
        "ledgers": {name: sha(HERE / name) for name in ["statements.json", "proof-environments.json", *files]}})
    print("Recorded", statements["summary"]["new_accepted_statement_correspondences"],
          "checked statements and", statements["summary"]["new_accepted_passage_correspondences"], "mapped passages.")


if __name__ == "__main__":
    main()
