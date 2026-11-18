#!/usr/bin/env python3
"""Bind C.2 correspondence to a successful clean run and independent review.

This records reviewed evidence; it does not replace Lean or mathematical
review. Every named mapped declaration must occur in the fresh type export.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1]
HERE = PROJECT / "correspondence"


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def relative(path):
    return str(path.resolve().relative_to(PROJECT))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run", type=Path, required=True)
    ap.add_argument("--review", type=Path, required=True)
    args = ap.parse_args()
    run_path, review_path = args.run.resolve(), args.review.resolve()
    run, review = read(run_path), read(review_path)
    if run["status"] != "passed" or run["initial_git_status"]:
        raise SystemExit("A successful clean-checkout run is required")
    if review["result"] != "PASS_SEMANTIC_CORRESPONDENCE" or review["issues"]:
        raise SystemExit("An independent passing C.2 review without open issues is required")
    for name, expected in run["source_identity"]["files"].items():
        if sha(PROJECT / name) != expected:
            raise SystemExit("Source differs from clean run: " + name)
    for name, expected in review["source_sha256"].items():
        if sha(PROJECT / name) != expected:
            raise SystemExit("Source differs from independent review: " + name)
    commands = {row["label"]: row for row in run["commands"]}
    for row in commands.values():
        if row["exit_code"] != 0 or sha(run_path.parent / row["log"]) != row["log_sha256"]:
            raise SystemExit("Failed or changed command log: " + row["label"])
    deps_path = run_path.parent / commands["dependencies"]["log"]
    deps = read(deps_path)
    endpoints = {row["name"]: row for row in deps["endpoints"]}
    reviewed = {row["id"]: row for row in review["passages"]}
    if set(reviewed) != {f"C2.{i}" for i in range(1, 8)}:
        raise SystemExit("The review must cover exactly C2.1–C2.7")
    build_ref = {"path": relative(run_path), "sha256": sha(run_path),
                 "source_commit": run["source_commit"],
                 "source_digest": run["source_identity"]["aggregate_sha256"],
                 "status": "passed", "initial_checkout_clean": True}
    audit_log = run_path.parent / commands["c2-audit"]["log"]
    audit_ref = {"run": relative(run_path), "command_label": "c2-audit",
                 "log": relative(audit_log), "log_sha256": sha(audit_log),
                 "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
                 "exit_code": 0}

    def types(names):
        return [{"declaration": name, "expanded_type": endpoints[name]["expanded_type"],
                 "export": relative(deps_path)} for name in names]

    def bindings(names):
        return [{"declaration": name,
                 "direct_dependencies": endpoints[name]["direct_dependencies"],
                 "transitive_project_graph": relative(deps_path)} for name in names]

    passages = read(HERE / "c2-passages.json")
    for row in passages["passages"]:
        check = reviewed[row["id"]]
        if check["result"] != "PASS":
            raise SystemExit("A passage review failed: " + row["id"])
        names = check["declarations"]
        missing = sorted(set(names) - endpoints.keys())
        if missing:
            raise SystemExit("Missing mapped type/audit export: " + ", ".join(missing))
        row.update(status="checked_printed_proof", new_declarations=names,
                   expanded_types=types(names), dependency_bindings=bindings(names),
                   reading_order_review={"path": relative(review_path), "sha256": sha(review_path),
                                         "passage": row["id"], "result": "PASS"},
                   build_receipt=build_ref, transitive_axiom_receipt=audit_ref,
                   inference_review=check["review"])
    statements = read(HERE / "statements.json")
    statement = next(row for row in statements["statements"]
                     if row["id"] == "S-intrinsic-lem-maximum")
    names = ["RectangleCLTArxivV1.lemma_C2_expected_maximum",
             "RectangleCLTArxivV1.bounded_sum_expected_maximum_factor_exists"]
    statement.update(status="proved_and_freshly_checked", printed_proof_status="checked",
                     lean_declarations=names, expanded_types=types(names),
                     dependency_declarations=bindings(names), build_receipt=build_ref,
                     audit_receipt=audit_ref,
                     reading_order_review={"path": relative(review_path), "sha256": sha(review_path)})
    statements["summary"]["new_accepted_statement_correspondences"] = sum(
        row["status"] == "proved_and_freshly_checked" for row in statements["statements"])
    statements["summary"]["new_accepted_passage_correspondences"] = 7
    proofs = read(HERE / "proof-environments.json")
    proof = next(row for row in proofs["proof_environments"] if row["id"] == "P-main-12")
    proof.update(status="checked_printed_proof", build_receipt=build_ref,
                 audit_receipt=audit_ref, reading_order_review=relative(review_path))
    write(HERE / "c2-passages.json", passages)
    write(HERE / "statements.json", statements)
    write(HERE / "proof-environments.json", proofs)
    acceptance = {"recorded_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "scope": "Lemma C.2 and C2.1–C2.7 only", "release_wide_certification": False,
                  "build": build_ref, "audit": audit_ref,
                  "review": {"path": relative(review_path), "sha256": sha(review_path)},
                  "updated_ledgers": {name: sha(HERE / name) for name in
                    ("c2-passages.json", "statements.json", "proof-environments.json")}}
    write(HERE / "c2-acceptance.json", acceptance)
    print("Recorded one checked statement and seven checked C.2 passages.")


if __name__ == "__main__":
    main()
