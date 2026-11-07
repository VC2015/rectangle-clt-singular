#!/usr/bin/env python3
"""Read-only evidence gate for an isolated frozen printed-proof checkpoint.

Run the existing run.py checkpoint --skip-cache first. This script reads its
evidence and immutable Git objects; it never refreshes the result certificate,
writes a receipt, edits metadata, or treats correspondence as a paper repair.
"""
from __future__ import annotations

import argparse
from collections import Counter
import datetime as dt
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CERT = HERE.parent
PACKAGE = CERT.parent
REPO = PACKAGE.parent
PACKAGE_NAME = "lean-rectangle-clt-singular"
PACKAGES = {"lean-kane", "lean-rectangle-clt-local", PACKAGE_NAME}
BASE_PROOF = "69f89747f4b845491b75cb23134c056bfbcd40f7"
BASE_MERGE = "e692196356de50c00fcdd66ddad0f3706db0241c"
PAPER = "research-rectangle-clt-singular/Unrestricted_CLT-split-V4.tex"
PAPER_SHA = "f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1"
PAPER_BLOB = "3dd7ea1a9c92e1d8d7ddfcbb6438b20a65ebc78e"
HANDOFF = "research-rectangle-clt-singular/Unrestricted_CLT_split_V4_Lean_Handoff.md"
HANDOFF_COMMIT = "2bd43fd98d2a8687ccdda3745f9ac8eac96260dd"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=REPO, stderr=subprocess.PIPE)


def blob(commit: str, path: str) -> bytes:
    return git("show", f"{commit}:{path}")


def tagged_records(path: Path, tag: str) -> tuple[dict, int]:
    records: dict = {}
    count = 0
    for number, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw
        # Lake can wrap the direct Lean message in JSON; direct audit output
        # is normally plain. Do not change the contents of a record.
        if raw.startswith("{"):
            try:
                wrapped = json.loads(raw)
                if isinstance(wrapped, dict) and "message" in wrapped:
                    line = str(wrapped["message"])
            except json.JSONDecodeError:
                pass
        position = line.find(tag + " ")
        if position < 0:
            continue
        try:
            item = json.loads(line[position + len(tag) + 1:])
        except json.JSONDecodeError as exc:
            raise ValueError(f"Malformed {tag} record at {path}:{number}") from exc
        require(isinstance(item, dict), f"Expected JSON object at {path}:{number}")
        name = item.get("declaration")
        require(isinstance(name, str) and bool(name), f"Missing declaration at {path}:{number}")
        require(name not in records or records[name] == item, f"Conflicting records for {name}")
        records[name] = item
        count += 1
    require(bool(records), f"No {tag} records in {path}")
    return records, count


def dependencies(path: Path, tag: str) -> tuple[dict, int]:
    records, count = tagged_records(path, tag)
    for name, item in records.items():
        require(set(item["transitive_axioms"]) <= ALLOWED, f"Unexpected axiom at {name}")
        require(bool(item["expanded_lean_type"]), f"No elaborated type at {name}")
        require(bool(item["module"]), f"No actual module at {name}")
        require(item["declaration_kind"] in {"theorem", "definition"}, f"Unexpected declaration kind at {name}")
        for field in ("type_used_constants", "value_used_constants"):
            require(isinstance(item[field], list), f"Missing dependency edges at {name}")
    return records, count


def coverage_input_gate(coverage: dict) -> dict:
    """Dispose of the q=0 counterexample without certifying its false estimate."""
    steps = coverage["proof_steps"]
    require(coverage.get("schema_version") == 1, "Unsupported correspondence schema")
    require(coverage["frozen_manuscript"] == {"commit": HANDOFF_COMMIT, "path": PAPER, "sha256": PAPER_SHA}, "Correspondence names a different frozen manuscript")
    require(bool(steps), "No substantive printed-step map")
    require(len({step["id"] for step in steps}) == len(steps), "Duplicate substantive printed-step identifiers")
    references = set()
    for step in steps:
        for field in ("baseline_declarations", "new_declarations"):
            names = step.get(field, [])
            require(isinstance(names, list) and all(isinstance(name, str) and name for name in names), f"Invalid declaration list in {step['id']}")
            references.update(names)
    require(references == set(coverage["declaration_index"]), "Printed-step references differ from the exact kernel-binding index")
    statements = coverage["manuscript_statements"]
    require(len(statements) == 31 and all(statement["lean_declaration"] for statement in statements), "Expected all 31 named manuscript statements")
    counts = dict(Counter(step["classification"] for step in steps))
    require(counts == coverage["counts"], "Coverage classification counts do not match the actual rows")
    repairs = []
    for step in steps:
        if step["id"] == "interpolation:A1-zero-order-scope":
            require(step["classification"] == "UNVERIFIED_STEP", "Do not certify the literal order-zero derivative estimate")
            require(step.get("disposition") == "COUNTEREXAMPLE_PROVED_REPAIR_REQUIRED", "The order-zero scope finding needs an explicit counterexample/repair disposition")
            needed = {
                "RectangleCLT.Companion.SplitV4.Printed.no_uniform_closedBox_zero_order_averaged_bound",
                "RectangleCLT.Companion.SplitV4.Printed.zero_order_local_envelope_fails",
            }
            require(needed <= set(step["new_declarations"]), "Missing exact local/full-signed Gaussian counterexample bindings")
            repairs.append(step["id"])
        else:
            require(step["classification"] == "SAME_ARGUMENT", f"Undisposed substantive printed step: {step['id']}")
    require(repairs == ["interpolation:A1-zero-order-scope"], "Expected the explicit frozen A1 order-zero qualification")
    require(coverage["completion_gate"]["manuscript_changed"] is False, "Frozen manuscript must remain unchanged")
    return {"substantive_rows": len(steps), "counts": counts,
            "every_substantive_printed_step_disposed": True,
            "literal_unqualified_claims_certified": False,
            "counterexample_repair_dispositions": repairs,
            "required_qualification": "Derivative-envelope assertions are certified for integers q >= 1; literal q=0 is disproved and requires the documented text qualification."}


def verify(args: argparse.Namespace) -> dict:
    logs = args.logs.resolve()
    run_path = logs / "run.json"
    require(run_path.is_file() and not run_path.is_symlink(), "Missing/unsafe run.json evidence")
    run = json.loads(run_path.read_text())
    require(run.get("schema_version") == 1, "Unsupported checkpoint evidence schema")
    proof = git("rev-parse", args.proof_commit + "^{commit}").decode().strip()
    require(len(proof) == 40, "A full frozen proof commit is required")
    tree = set(git("ls-tree", "-r", "--name-only", proof).decode().splitlines())
    validator_path = f"{PACKAGE_NAME}/split-v4-certification/printed-proof-extension/verify_record.py"
    require(Path(__file__).read_bytes() == blob(proof, validator_path), "Validator differs from the frozen proof commit")
    lean_paths = {p for p in tree if p.endswith(".lean") and p.split("/")[0] in PACKAGES and "/.lake/" not in p}
    config_names = {"lake-manifest.json", "lakefile.toml", "lakefile.lean", "lean-toolchain"}
    config_paths = {p for p in tree if len(p.split("/")) == 2 and p.split("/")[0] in PACKAGES and Path(p).name in config_names}
    dependency_specs = {}
    for package in PACKAGES:
        for dep in json.loads(blob(proof, f"{package}/lake-manifest.json"))["packages"]:
            dependency_specs[f"{package}:{dep['name']}"] = dep
    require(run.get("mode") == "checkpoint", "Expected checkpoint evidence")
    require(run.get("handoff_commit") == HANDOFF_COMMIT, "Wrong handoff commit")
    require(run.get("required_commands_passed") is True and run.get("exit_code") == 0, "Checkpoint did not pass")
    require(run.get("paper_certified") is False, "Command evidence must not itself claim paper certification")
    for flag in ("failed_commands", "not_run", "inputs_changed_during_run", "dependency_revision_mismatches", "interrupted", "toolchain_version_mismatch", "stopped_at_first_failing_build"):
        require(not run.get(flag), f"Checkpoint reports {flag}")
    runner_path = f"{PACKAGE_NAME}/split-v4-certification/run.py"
    require(run["runner_sha256"] == digest(blob(proof, runner_path)), "Runner differs from frozen Git input")
    for which in ("before", "after"):
        snapshot = run[which]
        require(snapshot["git_commit"] == proof, f"{which}: wrong Git commit")
        require(snapshot["git_status_porcelain"] == "", f"{which}: dirty or missing Git source status")
        require(snapshot["git_tracked_diff_sha256"] == digest(b""), f"{which}: tracked diff present")
        require(set(snapshot["sources_sha256"]) == lean_paths, f"{which}: incomplete committed Lean inventory")
        require(set(snapshot["manifests_sha256"]) == config_paths, f"{which}: incomplete build/config inventory")
        require(set(snapshot["dependencies"]) == set(dependency_specs), f"{which}: incomplete dependency inventory")
        require(set(snapshot["frozen_records_sha256"]) == {"VERIFICATION.json", "SUBEXPONENTIAL_VERIFICATION.json", "LOWER_RESULTS_VERIFICATION.json"}, f"{which}: incomplete historical record inventory")
        require(snapshot["proof_inputs_sha256"] == snapshot["sources_sha256"], f"{which}: incomplete checkpoint proof inputs")
        require(snapshot["manuscript_sha256"] == PAPER_SHA, f"{which}: manuscript bytes changed")
        require(snapshot["manuscript_git_blob"] == PAPER_BLOB, f"{which}: manuscript Git blob changed")
        require(snapshot["handoff_sha256"] == digest(blob(HANDOFF_COMMIT, HANDOFF)), f"{which}: frozen handoff changed")
        for path, expected in snapshot["sources_sha256"].items():
            require(digest(blob(proof, path)) == expected, f"{which}: source hash mismatch: {path}")
        for path, expected in snapshot["manifests_sha256"].items():
            require(path in tree and digest(blob(proof, path)) == expected, f"{which}: config hash mismatch: {path}")
        for name, expected in snapshot["frozen_records_sha256"].items():
            require(digest(blob(proof, f"{PACKAGE_NAME}/{name}")) == expected, f"{which}: frozen record changed: {name}")
        for name, dep in snapshot["dependencies"].items():
            specification = dependency_specs[name]
            require(dep["type"] == specification["type"] and dep["manifest_revision"] == specification.get("rev"), f"{which}: dependency differs from frozen manifest: {name}")
            require(dep["dirty"] == "", f"{which}: dirty or missing Git dependency status: {name}")
            if dep["type"] == "git":
                require(dep["actual_revision"] == dep["manifest_revision"], f"{which}: unpinned dependency {name}")
            elif dep["type"] == "path":
                require(dep["actual_revision"] == proof, f"{which}: path dependency is outside frozen proof: {name}")
            else:
                raise ValueError(f"Unsupported dependency kind at {name}")
    for key in ("sources_sha256", "proof_inputs_sha256", "manifests_sha256", "frozen_records_sha256", "dependencies", "manuscript_sha256", "handoff_sha256"):
        require(run["before"][key] == run["after"][key], f"Input changed during verification: {key}")
    require(digest(blob(proof, PAPER)) == PAPER_SHA, "Frozen proof has wrong manuscript")
    require(blob(proof, f"{PACKAGE_NAME}/lean-toolchain").decode().strip() == "leanprover/lean4:v4.19.0", "Wrong Lean toolchain")
    manifest = json.loads(blob(proof, f"{PACKAGE_NAME}/lake-manifest.json"))
    require(next(d["rev"] for d in manifest["packages"] if d["name"] == "mathlib") == "c44e0c8ee63ca166450922a373c7409c5d26b00b", "Wrong mathlib revision")
    reached = set()
    pending = ["RectangleCLTCompanion.SplitV4.PrintedProofs"]
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        path = f"{PACKAGE_NAME}/{module.replace('.', '/')}.lean"
        if path in tree:
            pending.extend(line.split()[1] for line in blob(proof, path).decode().splitlines() if line.startswith("import "))
    implementation_modules = {p.removeprefix(PACKAGE_NAME + "/").removesuffix(".lean").replace("/", ".")
                              for p in lean_paths if p.startswith(f"{PACKAGE_NAME}/RectangleCLTCompanion/SplitV4/Printed/") and not p.endswith("Audit.lean")}
    require(implementation_modules <= reached, "Printed implementation modules are missing from the fresh kernel import closure: " + ", ".join(sorted(implementation_modules - reached)))
    route_path = f"{PACKAGE_NAME}/RectangleCLTCompanion/SplitV4/PrintedRouteAudit.lean"
    route_source = blob(proof, route_path).decode()
    blocks = re.findall(r"^-- BEGIN PRINTED_ROUTE ([^\n]+)\n(.*?)\n-- END PRINTED_ROUTE \1$", route_source, re.MULTILINE | re.DOTALL)
    nested_audits = {p.removeprefix(PACKAGE_NAME + "/") for p in lean_paths if p.startswith(f"{PACKAGE_NAME}/RectangleCLTCompanion/SplitV4/Printed/") and p.endswith("Audit.lean")}
    require(len(blocks) == len(nested_audits) and {name for name, _ in blocks} == nested_audits, "Fresh aggregate route audit omits/duplicates a nested audit")
    expected_route_imports = {"import RectangleCLTCompanion.SplitV4.PrintedProofs"}
    for name, body in blocks:
        nested_source = blob(proof, f"{PACKAGE_NAME}/{name}").decode()
        expected_route_imports.update(line for line in nested_source.splitlines() if line.startswith("import "))
        expected_body = "\n".join(line for line in nested_source.splitlines() if not line.startswith("import "))
        require(body.strip() == expected_body.strip(), f"Fresh aggregate route audit differs from nested source: {name}")
    require({line for line in route_source.splitlines() if line.startswith("import ")} == expected_route_imports, "Aggregate route audit imports differ from nested audit imports")

    prefix = f"{PACKAGE_NAME}/RectangleCLTCompanion/SplitV4/"
    top_files = sorted(p.removeprefix(PACKAGE_NAME + "/") for p in lean_paths if p.startswith(prefix) and "/" not in p[len(prefix):])
    expected = [("version", ["lake", "env", "lean", "--version"], "toolchain"),
                ("build", ["lake", "build", "RectangleCLTCompanion"], "proof_build"),
                ("CompleteAudit", ["lake", "env", "lean", "RectangleCLTCompanion/CompleteAudit.lean"], "axiom_audit"),
                ("split-v4-build", ["lake", "build", *[p.removesuffix(".lean").replace("/", ".") for p in top_files]], "proof_build")]
    expected += [(Path(p).stem, ["lake", "env", "lean", p], "axiom_audit") for p in top_files if p.endswith("Audit.lean")]
    actual = [(c["name"], c["argv"], c["kind"]) for c in run["commands"]]
    require(actual == expected, "Recorded commands differ from the full frozen checkpoint plan/order")
    commands = {c["name"]: c for c in run["commands"]}
    require({"DependencyAudit", "PrintedDependencyAudit", "PrintedCorrespondenceAudit", "PrintedRouteAudit"} <= commands.keys(), "Missing exhaustive dependency/correspondence/route audit")
    expected_evidence_files = {"run.json", *[c["log"] for c in run["commands"]]}
    require({p.name for p in logs.iterdir()} == expected_evidence_files, "Evidence directory has missing or unrecorded files")
    require(all(p.is_file() and not p.is_symlink() for p in logs.iterdir()), "Evidence must contain regular files, not symlinks/directories")
    started = dt.datetime.fromisoformat(run["started_at"])
    finished = dt.datetime.fromisoformat(run["finished_at"])
    require(started.tzinfo is not None and finished.tzinfo is not None and started <= finished, "Missing/invalid run timestamps")
    previous = started
    for number, command in enumerate(run["commands"], 1):
        require(command["log"] == f"{number:02d}-{command['name']}.log", f"Unexpected/duplicated runner log filename: {command['name']}")
        require(command["exit_code"] == 0, f"Command failed: {command['name']}")
        require(command["cwd"] == run["cwd"], f"Unexpected command cwd: {command['name']}")
        path = logs / command["log"]
        require(path.parent == logs and path.is_file() and not path.is_symlink(), f"Missing/unsafe log path: {command['name']}")
        require(digest(path.read_bytes()) == command["log_sha256"], f"Changed log: {command['name']}")
        command_started = dt.datetime.fromisoformat(command["started_at"])
        command_finished = dt.datetime.fromisoformat(command["finished_at"])
        require(command_started.tzinfo is not None and command_finished.tzinfo is not None and previous <= command_started <= command_finished <= finished, f"Invalid command timestamps/order: {command['name']}")
        duration = command["duration_seconds"]
        require(isinstance(duration, (int, float)) and math.isfinite(duration) and duration >= 0, f"Missing/invalid command duration: {command['name']}")
        previous = command_finished
    def log(name: str) -> Path:
        return logs / commands[name]["log"]
    require("version 4.19.0" in log("version").read_text(), "Actual Lean version mismatch")

    baseline_dir = args.baseline_logs.resolve()
    baseline_path = baseline_dir / "run.json"
    baseline = json.loads(baseline_path.read_text())
    require(baseline["before"]["git_commit"] == BASE_PROOF and baseline["required_commands_passed"], "Wrong/failed preserved result baseline")
    baseline_rel = f"{PACKAGE_NAME}/split-v4-certification/logs-checkpoint-69f8974/run.json"
    require(baseline_path.read_bytes() == blob(BASE_MERGE, baseline_rel), "Preserved result run record changed")
    baseline_command = next(c for c in baseline["commands"] if c["name"] == "DependencyAudit")
    baseline_log = baseline_dir / baseline_command["log"]
    require(digest(baseline_log.read_bytes()) == baseline_command["log_sha256"], "Preserved dependency log changed")
    old_records, _ = dependencies(baseline_log, "SPLITV4_DEPENDENCY")
    require(len(old_records) == 3751, "Preserved dependency baseline must contain exactly 3751 declarations")
    for key in ("sources_sha256", "manifests_sha256"):
        for path, value in baseline["before"][key].items():
            require(run["before"][key].get(path) == value, f"Preserved result input changed: {path}")
    require(run["before"]["frozen_records_sha256"] == baseline["before"]["frozen_records_sha256"], "Historical result records changed")
    base_tree = set(git("ls-tree", "-r", "--name-only", BASE_MERGE).decode().splitlines())
    protected = {p for p in base_tree if p.startswith(f"{PACKAGE_NAME}/split-v4-certification/") or (p.startswith(PACKAGE_NAME + "/") and p.endswith("VERIFICATION.json"))}
    changed = set(git("diff", "--name-only", BASE_MERGE, proof, "--", PACKAGE_NAME).decode().splitlines())
    require(not protected.intersection(changed), "Existing result evidence/records were edited: " + ", ".join(sorted(protected.intersection(changed))))
    current_old, _ = dependencies(log("DependencyAudit"), "SPLITV4_DEPENDENCY")
    build_old, _ = dependencies(log("split-v4-build"), "SPLITV4_DEPENDENCY")
    require(current_old == old_records == build_old, "The original 3751 dependency/type/axiom records differ")
    printed, printed_raw = dependencies(log("PrintedDependencyAudit"), "PRINTEDV4_DEPENDENCY")
    build_printed, _ = dependencies(log("split-v4-build"), "PRINTEDV4_DEPENDENCY")
    require(printed == build_printed, "Fresh build/direct printed dependency records differ")
    require(all(printed.get(name) == item for name, item in old_records.items()), "Printed closure changed an original dependency/type/axiom record")
    extension = {n: d for n, d in printed.items() if d["module"].startswith("RectangleCLTCompanion.SplitV4.Printed.")}
    require(bool(extension), "No printed-extension theorem records")

    coverage_path = f"{PACKAGE_NAME}/split-v4-certification/printed-proof-extension/coverage.json"
    coverage = json.loads(blob(proof, coverage_path))
    coverage_gate = coverage_input_gate(coverage)
    # Some preserved result endpoints are not repeated as references in a
    # printed-step row. They are still bound, typed and axiom-audited by the
    # exhaustive dependency audit, including its explicit historical roots.
    require({statement["lean_declaration"] for statement in coverage["manuscript_statements"]} <= printed.keys(), "A named manuscript statement has no checked dependency/type/axiom record")
    mapped = set(coverage["declaration_index"])
    bindings, binding_raw = tagged_records(log("PrintedCorrespondenceAudit"), "PRINTED_CORRESPONDENCE_BINDING")
    build_bindings, _ = tagged_records(log("split-v4-build"), "PRINTED_CORRESPONDENCE_BINDING")
    require(set(bindings) == mapped and bindings == build_bindings, "Mapped declaration bindings differ from frozen coverage/build")
    for name, item in bindings.items():
        require(bool(item["module"]), f"No kernel binding module for {name}")
        index_entry = coverage["declaration_index"][name]
        require(item["module"] == index_entry["module"], f"Frozen correspondence/kernel module mismatch at {name}")
        source_path = index_entry["source"]["path"]
        require(source_path in lean_paths and digest(blob(proof, source_path)) == index_entry["source_sha256"], f"Frozen correspondence source hash mismatch at {name}")
        if name in printed:
            require(item["module"] == printed[name]["module"], f"Binding/dependency module mismatch at {name}")
    summary_counts = re.findall(r"PRINTED_CORRESPONDENCE_AUDIT_PASS (\d+) exact mapped declarations/types", log("PrintedCorrespondenceAudit").read_text())
    require(summary_counts == [str(len(mapped))], "Missing/mismatched official mapped-type/axiom audit summary")
    return {"validation_only": True, "evidence_gate_passed": True, "proof_commit": proof,
            "run_json": str(run_path), "run_json_sha256": digest(run_path.read_bytes()),
            "required_commands": len(expected), "preserved_dependency_records": len(old_records),
            "printed_dependency_records": len(printed), "printed_dependency_raw_records": printed_raw,
            "new_printed_theorem_records": len(extension), "mapped_declaration_bindings": len(bindings),
            "printed_implementation_modules": len(implementation_modules),
            "fresh_nested_route_audit_bodies": len(nested_audits),
            "mapped_binding_raw_records": binding_raw, "permitted_axioms": sorted(ALLOWED),
            "source_files": len(lean_paths), "configuration_files": len(run["before"]["manifests_sha256"]),
            "protected_old_result_files": len(protected), "manuscript_sha256": PAPER_SHA,
            "correspondence_input_gate": coverage_gate,
            "printed_theorem_modules": dict(sorted(Counter(d["module"] for d in extension.values()).items())),
            "scope": "Formal command/dependency/type/binding evidence only. Mathematical correspondence and manuscript qualifications remain separately documented; no existing certificate was rewritten."}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--logs", required=True, type=Path)
    parser.add_argument("--proof-commit", required=True)
    parser.add_argument("--baseline-logs", type=Path, default=CERT / "logs-checkpoint-69f8974")
    parser.add_argument("--validate-only", action="store_true", help="Explicitly request the read-only gate (all invocations are read-only)")
    args = parser.parse_args()
    try:
        report = verify(args)
    except (ValueError, TypeError, KeyError, OSError, json.JSONDecodeError, subprocess.CalledProcessError) as exc:
        print(f"VALIDATION FAILED: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
