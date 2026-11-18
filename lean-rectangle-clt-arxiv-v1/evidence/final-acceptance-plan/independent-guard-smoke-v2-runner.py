#!/usr/bin/env python3
"""Synthetic recorder guard tests. These fixtures are not Lean proof evidence."""
from pathlib import Path
import copy
import hashlib
import importlib.util
import json
import tempfile
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("recorder", ROOT / "tools/record_final_acceptance.py")
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
checks = []


def rejects(name, action, substring):
    try:
        action()
    except RuntimeError as error:
        assert substring in str(error), (name, str(error))
        checks.append({"id": name, "status": "PASS", "rejection": str(error)})
    else:
        raise RuntimeError("Guard did not reject: " + name)


with tempfile.TemporaryDirectory(prefix="final-recorder-guard-") as directory:
    base = Path(directory)
    root, out = base / "root", base / "out"
    root.mkdir()
    out.mkdir()
    (root / "fixture.lean").write_text("-- Deliberately synthetic, not Lean evidence.\n")
    (root / "mapper.py").write_text("# synthetic mapper identity\n")
    (root / "clean-harness.py").write_text("# separate synthetic clean harness\n")
    (root / "correspondence").mkdir()
    r.write(root / "correspondence/fixture.json", {"synthetic": True})
    names = ["Kane.exp_avg_le_avg_exp", "Kane.avg_le_sqrt_of_exp_moment"]
    origins = {n: [{"ledger": "correspondence/fixture.json", "pointer": "/synthetic"}] for n in names}
    mp = {"source_commit": "SYNTHETIC_NOT_A_PROOF_COMMIT", "root_module": "RectangleCLTArxivV1", "unresolved_unqualified_values": [],
          "unresolved_project_imports": [], "ledger_sha256": {"correspondence/fixture.json": r.sha(root / "correspondence/fixture.json")},
          "source_identity": {"fixture.lean": r.sha(root / "fixture.lean")},
          "mapping_tool_identity": {"path": "mapper.py", "sha256": r.sha(root / "mapper.py")},
          "target_origins": origins, "root_project_import_closure": [],
          "source_module_paths": {"Kane.Analytic": "fixture.lean"}}
    r.write(out / "plan.json", mp)
    endpoints = [{"name": n, "expanded_type": "SYNTHETIC_TYPE_NOT_LEAN_EVIDENCE",
                  "kernel_import_module": "Kane.Analytic", "direct_dependencies": []} for n in names]
    export = {"endpoints": endpoints, "axiom_union": sorted(r.ALLOWED),
              "project_dependency_graph": [{"name": n, "direct_project_dependencies": []} for n in names]}
    bindings = {"ledger_sha256": mp["ledger_sha256"], "bindings": {
        n: {"origins": origins[n], "expanded_type": endpoints[i]["expanded_type"],
            "kernel_import_module": "Kane.Analytic"} for i, n in enumerate(names)}}
    r.write(out / "actual-provider-bindings.json", {"present": endpoints})
    forced = {"modules": ["Kane.Analytic"], "source_sha256": {"Kane.Analytic": mp["source_identity"]["fixture.lean"]}}
    (out / "TypesAndAudit.lean").write_text("-- synthetic fixture\nset_option pp.all true\n")
    (out / "synthetic.log").write_text("SYNTHETIC_NO_LEAN_EXECUTION\n")
    commands = [{"label": "project-build", "argv": ["lake", "build"], "exit_code": 0,
                 "log": str(out / "synthetic.log"), "log_sha256": r.sha(out / "synthetic.log")},
                {"label": "force-0000-Kane-Analytic", "argv": ["lake", "env", "lean", "fixture.lean"],
                 "exit_code": 0, "log": str(out / "synthetic.log"), "log_sha256": r.sha(out / "synthetic.log")}]
    run = {"status": "passed", "initial_git_status": "", "source_commit": mp["source_commit"],
           "plan_sha256": r.sha(out / "plan.json"), "commands": commands, "target_count": 2,
           "project_dependency_nodes": 2, "axiom_union": sorted(r.ALLOWED)}
    clean_files = {"clean-harness.py": r.sha(root / "clean-harness.py")}
    run["source_identity"] = {"files": clean_files,
        "aggregate_sha256": hashlib.sha256(json.dumps(clean_files, sort_keys=True).encode()).hexdigest()}

    def save():
        r.write(out / "expanded-types-and-dependencies.json", export)
        bindings["export_sha256"] = r.sha(out / "expanded-types-and-dependencies.json")
        r.write(out / "ledger-bindings.json", bindings)
        r.write(out / "forced-source-inventory.json", forced)
        run["export_sha256"] = r.sha(out / "expanded-types-and-dependencies.json")
        run["bindings_sha256"] = r.sha(out / "ledger-bindings.json")
        r.write(out / "run.json", run)

    def verify():
        return r.verify_mapping(root, out / "plan.json", out / "run.json", out / "run.json", 2)

    save()
    verify()
    checks.append({"id": "complete_synthetic_fixture", "status": "PASS"})
    original = copy.deepcopy((export, bindings, forced, run))
    (root / "clean-harness.py").write_text("# changed harness\n")
    rejects("extra_clean_harness_drift", verify, "Changed/missing input: clean-harness.py")
    (root / "clean-harness.py").write_text("# separate synthetic clean harness\n")
    run["source_identity"]["aggregate_sha256"] = "0" * 64
    save()
    rejects("clean_harness_aggregate_drift", verify, "identity aggregate differs")
    export, bindings, forced, run = copy.deepcopy(original)
    run["status"] = "running"
    save()
    rejects("unfinished_checkpoint", verify, "has not passed")
    export, bindings, forced, run = copy.deepcopy(original)
    export["axiom_union"].append("sorryAx")
    save()
    rejects("nonstandard_axiom", verify, "Unexpected kernel axiom")
    export, bindings, forced, run = copy.deepcopy(original)
    export["endpoints"].pop()
    save()
    rejects("missing_type", verify, "target count differs")
    export, bindings, forced, run = copy.deepcopy(original)
    export["project_dependency_graph"][0]["direct_project_dependencies"] = ["Kane.missing"]
    save()
    rejects("unclosed_project_graph", verify, "graph is not closed")
    export, bindings, forced, run = copy.deepcopy(original)
    bindings["bindings"][names[0]]["origins"] = []
    save()
    rejects("origin_pointer_drift", verify, "Type/provenance drift")
    export, bindings, forced, run = copy.deepcopy(original)
    run["commands"][1]["argv"] = ["lake", "env", "lean", "wrong.lean"]
    save()
    rejects("wrong_module_source_replay", verify, "exact module/source replay command")
    export, bindings, forced, run = copy.deepcopy(original)
    run["commands"].append(copy.deepcopy(run["commands"][1]))
    save()
    rejects("duplicate_module_replay", verify, "exact module/source replay command")
    export, bindings, forced, run = copy.deepcopy(original)
    (out / "TypesAndAudit.lean").write_text("-- no pp.all\n")
    save()
    rejects("missing_pp_all", verify, "Full pp.all")

    candidate = out / "candidate"
    candidate.mkdir()
    old = "correspondence/fixture.json"
    preimages = {old: r.sha(root / old)}
    r.write(candidate / "pre-acceptance-manifest.json", preimages)
    backup = candidate / "pre-acceptance" / old
    backup.parent.mkdir(parents=True)
    backup.write_text("CORRUPTED_BACKUP\n")
    receipt = {"status": "passed_candidate_waiting_for_root_approval", "pre_acceptance_identity": preimages,
               "pre_acceptance_manifest": {"sha256": r.sha(candidate / "pre-acceptance-manifest.json")}}
    r.write(candidate / "receipt.json", receipt)
    args = SimpleNamespace(root=root, candidate=candidate / "receipt.json",
                           approved_receipt_sha256=r.sha(candidate / "receipt.json"))
    rejects("corrupt_preservation_copy", lambda: r.apply(args), "Preserved pre-acceptance file changed")
    args.approved_receipt_sha256 = "0" * 64
    rejects("wrong_approval_hash", lambda: r.apply(args), "approval hash differs")
    r.write(root / "bad-review.json", {"status": "NOT PASS"})
    rejects("negative_review_marker", lambda: r.passed_review(root, "bad-review.json"), "negative result")
    r.write(root / "bad-review.json", {"status": "failed", "conclusion": "PASS"})
    rejects("contradictory_review_marker", lambda: r.passed_review(root, "bad-review.json"), "negative result")
    r.write(root / "bad-review.json", {"status": "PASS_WITH_FAILURES"})
    rejects("qualified_failure_marker", lambda: r.passed_review(root, "bad-review.json"), "no top-level PASS")

plan_path = ROOT / "evidence/final-acceptance-plan/plan-final.json"
plan = r.read(plan_path)
inventory = r.verify_plan(ROOT, plan)
# In-memory output accounting test. Placeholder types never leave this process.
mp = r.read(ROOT / plan["mapping_plan"]["path"])
types = {n: {"expanded_type": "SYNTHETIC_ACCOUNTING_ONLY", "direct_dependencies": [],
             "kernel_import_module": "SYNTHETIC"} for n in mp["target_origins"]}
graph = {n: [] for n in types}
refs = {"expanded_types_and_project_graph": {"path": "SYNTHETIC", "sha256": "0" * 64},
        "source_commit": "SYNTHETIC_ACCOUNTING_ONLY", "target_count": 1949,
        "project_dependency_nodes": 1949}
outputs = r.build_outputs(ROOT, plan, inventory, types, graph, refs)
assert set(outputs) == r.OUTPUTS
assert outputs["correspondence/final-acceptance.json"]["counts"] == plan["expected_counts"]
assert len(outputs["correspondence/proof-environments.json"]["proof_environments"]) == 34
assert outputs["correspondence/final-coverage.json"]["literal_unproved_internal_claims"]
assert next(x for x in outputs["correspondence/statements.json"]["statements"] if x["id"] == "S-lem-maximum")["qualification"]
r.verify_plan(ROOT, plan)
checks.append({"id": "in_memory_statement_environment_scope_accounting", "status": "PASS",
               "counts": outputs["correspondence/final-acceptance.json"]["counts"],
               "coverage_counts": outputs["correspondence/final-coverage.json"]["counts"]})
r.write(ROOT / "evidence/final-acceptance-plan/independent-guard-smoke-v2.json", {
    "status": "PASS", "scope": "Synthetic recorder guard fixtures and in-memory output accounting only. No Lean theorem/evidence claim, no global mutation, no clean build run.",
    "recorder": r.reference(ROOT, ROOT / "tools/record_final_acceptance.py"),
    "plan": r.reference(ROOT, plan_path), "checks": checks})
print(json.dumps({"status": "PASS", "checks": len(checks), "global_files_changed": False}))
