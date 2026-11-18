#!/usr/bin/env python3
"""Record six independently reviewed transfers/lower results after a clean run."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
HERE = PROJECT / "correspondence"
RUN = PROJECT / "evidence/transfers-lower-clean-checkpoint/run.json"
MAPPING = PROJECT / "evidence/transfers-lower-clean-mapping/receipt.json"


def read(p):
    return json.loads(p.read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def rel(p):
    return str(p.relative_to(PROJECT))


def write(p, d):
    p.write_text(json.dumps(d, indent=2) + "\n")


def main():
    run = read(RUN)
    assert run["status"] == "passed" and not run["initial_git_status"]
    for f, expected in run["source_identity"]["files"].items():
        assert sha(PROJECT / f) == expected, f
    commands = {r["label"]: r for r in run["commands"]}
    for row in commands.values():
        assert row["exit_code"] == 0
        assert sha(RUN.parent / row["log"]) == row["log_sha256"]
    assert read(RUN.parent / "dependency-check.json")["passed"]
    mapped = read(MAPPING)
    assert mapped["exit_code"] == 0 and not mapped["initial_git_status"]
    assert mapped["source_commit"] == run["source_commit"]
    for k in ("harness", "log"):
        assert sha(PROJECT / mapped[k]) == mapped[k + "_sha256"]
    export = PROJECT / mapped["log"]
    data = read(export)
    types = {r["name"]: r for r in data["endpoints"]}
    graph = {r["name"]: r["direct_project_dependencies"] for r in data["project_dependency_graph"]}
    build = {"path": rel(RUN), "sha256": sha(RUN), "source_commit": run["source_commit"],
             "source_digest": run["source_identity"]["aggregate_sha256"],
             "initial_checkout_clean": True, "status": "passed"}
    log = RUN.parent / commands["c2-audit"]["log"]
    audit = {"run": rel(RUN), "log": rel(log), "log_sha256": sha(log), "exit_code": 0,
             "allowed_axioms": mapped["allowed_axioms"],
             "passage_endpoint_audit": {"path": rel(MAPPING), "sha256": sha(MAPPING)}}
    reviews = {
        "cor2": ["evidence/subexponential-intrinsic/independent-review.json"],
        "cor3": ["evidence/polyhedral-intrinsic/independent-review.json",
                 "evidence/polyhedral-intrinsic/orlicz-independent-review.json"],
        "t4": ["evidence/lower-bounded-theorem/independent-intrinsic-review.json"],
        "t5t7": ["evidence/lower-fourth-dense-independent-review.md"],
        "t6": ["evidence/lower-masked-fourth-theorem/independent-intrinsic-review.json"],
    }
    for files in reviews.values():
        for f in files:
            path = PROJECT / f
            if path.suffix == ".md":
                assert "PASS" in path.read_text()
                continue
            d = read(path)
            assert d.get("status", "").lower().startswith("pass") or "pass" in d.get("conclusion", "").lower()
            assert not d.get("blocking_mathematical_gaps", [])
            hashes = d.get("reviewed_source_sha256", d.get("reviewed_source_hashes", {}))
            for source, expected in hashes.items():
                assert sha(PROJECT / source) == expected, source

    def reviewed(key):
        return [{"path": f, "sha256": sha(PROJECT / f), "result": "PASS"} for f in reviews[key]]

    def expanded(names):
        return [{"declaration": n, "expanded_type": types[n]["expanded_type"], "export": rel(export)} for n in names]

    def deps(names):
        return [{"declaration": n, "direct_dependencies": types[n]["direct_dependencies"],
                 "direct_project_dependencies": graph[n], "transitive_project_graph": rel(export)} for n in names]

    pins = read(PROJECT / "source-pins.json")
    frozen = {}
    files = {"subexponential-intrinsic-passages.json": "cor2",
             "polyhedral-intrinsic-passages.json": "cor3", "lower-fourth-dense-passages.json": "t5t7"}
    variations = {r["id"] for r in read(PROJECT / reviews["cor2"][0])["passages"]
                  if r["status"] == "accepted_with_explicit_local_route_differences"}
    for filename, key in files.items():
        path = HERE / filename
        d = read(path)
        for row in d["passages"]:
            loc = row.get("location", row.get("source_span"))
            source = loc["path"]
            if source not in frozen:
                frozen[source] = subprocess.check_output(["git", "show", pins["paper_commit"] + ":" + source], cwd=PROJECT.parent)
            a, b = loc["lines"]
            assert hashlib.sha256(b"".join(frozen[source].splitlines(keepends=True)[a-1:b])).hexdigest() == loc["sha256"]
            names = row.get("lean_endpoints", row.get("lean_declarations"))
            assert names and set(names) <= types.keys(), row["id"]
            status = "checked_with_documented_route_variation" if row["id"] in variations else "checked_printed_proof"
            if row["status"] != status:
                row.setdefault("status_history", []).append(row["status"])
            row.update(status=status, expanded_types=expanded(names), dependency_bindings=deps(names),
                       clean_build_receipt=build, transitive_axiom_receipt=audit, reading_order_reviews=reviewed(key))
        d["clean_integrated_checkpoint"] = build
        write(path, d)
    targets = {
        "S-cor-subexponential": ("cor2", ["corollary_2_intrinsic"]),
        "S-cor-polyhedral-transfer": ("cor3", ["corollary_3_intrinsic"]),
        "S-opt-symmetric-lower": ("t4", ["theorem4_bounded_symmetric_lower"]),
        "S-opt-q4-lower": ("t5t7", ["theorem_5_fourth_moment_lower", "theorem_5_fourth_moment_two_sided"]),
        "S-opt-q4-growing": ("t6", ["theorem_6_growing_fourth_moment_lower"]),
        "S-lower-dense": ("t5t7", ["theorem_7_polynomial_envelope_lower", "theorem_7_fixed_envelope_fourth_lower", "exists_lowerDense_upper_constant"]),
    }
    statements = read(HERE / "statements.json")
    for row in statements["statements"]:
        if row["id"] not in targets:
            continue
        key, ns = targets[row["id"]]
        names = ["RectangleCLTArxivV1." + n for n in ns]
        row.update(status="proved_and_freshly_checked", lean_declarations=names,
                   expanded_types=expanded(names), dependency_declarations=deps(names),
                   build_receipt=build, audit_receipt=audit, reading_order_reviews=reviewed(key),
                   printed_proof_status="checked_mapped_passages" if key in ("cor2", "cor3", "t5t7") else
                       "semantic_review_passed_detailed_passage_binding_open",
                   formalization_scope="Actual probability models and universal constants; documented local proof variations remain explicit in the passage ledgers.")
    all_files = ["c2-passages.json", "intrinsic-main-passages.json", "a1-passages.json", "b3-passages.json",
                 "theorem-2-envelope-passages.json", "paired-intrinsic-passages.json", *files]
    rows = [r for f in all_files for r in read(HERE / f)["passages"]]
    statements["summary"].update(
        new_accepted_statement_correspondences=sum(r["status"] == "proved_and_freshly_checked" for r in statements["statements"]),
        new_accepted_passage_correspondences=sum(r["status"] in ("checked_printed_proof", "checked_with_documented_route_variation") for r in rows),
        accepted_passages_with_documented_route_variation=sum(r["status"] == "checked_with_documented_route_variation" for r in rows))
    write(HERE / "statements.json", statements)
    proofs = read(HERE / "proof-environments.json")
    for row in proofs["proof_environments"]:
        if row["id"] in ("P-main-13", "P-main-14"):
            key = "cor2" if row["id"] == "P-main-13" else "cor3"
            file = next(f for f, k in files.items() if k == key)
            row.update(status="checked_with_documented_route_variation" if key == "cor2" else "checked_printed_proof",
                       passage_ids=[r["id"] for r in read(HERE / file)["passages"]],
                       build_receipt=build, audit_receipt=audit, reading_order_reviews=reviewed(key))
    write(HERE / "proof-environments.json", proofs)
    write(HERE / "transfers-lower-acceptance.json", {
        "recorded_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Corollaries 2–3, Theorems 4–7, and 42 mapped passages",
        "release_wide_certification": False, "build": build, "audit": audit,
        "summary": statements["summary"], "documented_route_variations": sorted(variations),
        "ledgers": {f: sha(HERE / f) for f in ["statements.json", "proof-environments.json", *files]}})
    print(statements["summary"])


if __name__ == "__main__":
    main()
