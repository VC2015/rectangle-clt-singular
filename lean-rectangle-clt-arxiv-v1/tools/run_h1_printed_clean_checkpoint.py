#!/usr/bin/env python3
"""Check the printed nonsimple H.1 extension in a separate clean checkout.

The sealed 443fbc6 checkpoint remains the evidence for unchanged old native
sources. This run builds the entire library, directly elaborates every new
or changed native source, audits the registered endpoints, and checks the
full types and complete axiom union of all new explicit public declarations.
It does not claim to replay the old 1,949-target manuscript mapping audit.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def put(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def git(*args):
    return subprocess.check_output(["git", *args], cwd=PROJECT, text=True).strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--dependency-cache-receipt", type=Path, required=True)
    ap.add_argument("--native-cache-receipt", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(PROJECT.parent.resolve()):
        raise SystemExit("Checkpoint output must be outside the clean checkout")
    if output.exists():
        raise SystemExit("Refusing to overwrite checkpoint")
    if git("status", "--porcelain"):
        raise SystemExit("A clean checkout is required, including untracked files")
    baseline_path = PROJECT / "evidence/final-clean-checkpoint/run.json"
    assert sha(baseline_path) == "3500c2efdb929397434a7e2201f0b203b51b14bd362d53e78666be40afb62ba5"
    baseline = json.loads(baseline_path.read_text())
    assert baseline["source_commit"] == "443fbc667ed3c3ee47369e028c2c4280a5eed604"
    assert baseline["status"] == "passed" and not baseline["initial_git_status"]
    assert all(row["exit_code"] == 0 for row in baseline["commands"])
    old = baseline["final_source_identity"]["files"]
    natives = {str(p.relative_to(PROJECT)): sha(p)
               for p in sorted((PROJECT / "RectangleCLTArxivV1").rglob("*.lean"))}
    missing = {p for p in old if p.startswith("RectangleCLTArxivV1/") and p.endswith(".lean")} - set(natives)
    assert not missing, sorted(missing)
    changed = {p for p, h in natives.items() if old.get(p) != h}
    assert changed, "No new or changed native proof sources"
    dependency_cache_path = args.dependency_cache_receipt.resolve()
    native_cache_path = args.native_cache_receipt.resolve()
    dependency_cache = json.loads(dependency_cache_path.read_text())
    native_cache = json.loads(native_cache_path.read_text())
    assert dependency_cache["proof_check"] is False
    assert dependency_cache["new_c2_build_artifacts_copied"] is False
    assert Path(dependency_cache["destination_checkout"]).resolve() == PROJECT.parent.resolve()
    assert native_cache["proof_check"] is False
    assert native_cache["baseline_commit"] == baseline["source_commit"]
    assert native_cache["baseline_receipt_sha256"] == sha(baseline_path)
    assert Path(native_cache["destination_checkout"]).resolve() == PROJECT.parent.resolve()
    assert native_cache["new_native_artifacts_copied"] is False
    assert native_cache["root_artifact_copied"] is False
    reusable = {row["source"]: row["sha256"] for row in native_cache["source_identical_native_modules"]}
    assert reusable == {p: h for p, h in natives.items() if p not in changed}
    for artifact in native_cache["artifacts"]:
        source = artifact["source"]
        assert source in reusable and artifact["source_sha256"] == reusable[source]
        module = str(Path(source).with_suffix(""))
        allowed_paths = {".lake/build/lib/lean/" + module + suffix for suffix in
                         (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")}
        allowed_paths |= {".lake/build/ir/" + module + suffix for suffix in (".c", ".c.hash")}
        assert artifact["path"] in allowed_paths
        assert sha(PROJECT / artifact["path"]) == artifact["sha256"]
    artifact_paths = [row["path"] for row in native_cache["artifacts"]]
    assert len(artifact_paths) == len(set(artifact_paths)), "Duplicate cached artifact"
    for source in reusable:
        module = str(Path(source).with_suffix(""))
        assert ".lake/build/lib/lean/" + module + ".olean" in artifact_paths
        assert ".lake/build/lib/lean/" + module + ".olean.hash" in artifact_paths
    new_modules = {str(Path(p).with_suffix("")).replace("/", ".") for p in changed}
    catalog = runpy.run_path(str(PROJECT / "tools/prepare_full_clean_mapping.py"))
    module_paths, declarations = catalog["modules_and_declarations"](PROJECT)
    closure, missing_imports = catalog["imported_modules"](module_paths,
        ["RectangleCLTArxivV1"] + sorted(new_modules))
    assert not missing_imports, missing_imports
    ordered, seen = [], set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for dep in re.findall(r"^import\s+([\w.]+)", module_paths[module].read_text(), re.M):
            if dep in module_paths:
                visit(dep)
        if module in new_modules:
            ordered.append(module)

    for module in sorted(new_modules):
        visit(module)
    assert set(ordered) == new_modules
    targets = sorted(name for name, providers in declarations.items() if providers & new_modules)
    assert targets and all(len(declarations[name]) == 1 for name in targets)
    output.mkdir(parents=True)
    harness = output / "NewTypesAndAudit.lean"
    harness.write_text(catalog["render"](["RectangleCLTArxivV1"] + ordered, targets))
    configs = ["RectangleCLTArxivV1.lean", "Audit.lean", "Correspondence/Dependencies.lean",
               "Correspondence/SupplementH.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
               "source-pins.json", "tools/check_pins.py", "tools/prepare_full_clean_mapping.py",
               "correspondence/build_source_ledger.py", "inventory.json", "correspondence/statements.json",
               "correspondence/c2-passages.json", "correspondence/proof-environments.json",
               "tools/prepare_verified_cache.py", "tools/prepare_h1_verified_native_cache.py",
               "tools/run_h1_printed_clean_checkpoint.py", "evidence/final-clean-checkpoint/run.json"]
    bound = {name: sha(PROJECT / name) for name in configs}
    bound.update(natives)
    bound.update({os.path.relpath(module_paths[m], PROJECT): sha(module_paths[m]) for m in closure})
    harness_digest = sha(harness)
    packages = catalog["pinned_git_packages"](PROJECT)
    package_identities = catalog["check_git_packages"](PROJECT, packages)
    report = {"status": "running", "scope": "Clean nonsimple printed H.1 extension; entire library build and registered endpoint axiom audit; direct source elaboration and full-type/axiom audit of every new or changed native module",
              "historical_1949_target_mapping_replayed": False, "release_wide_certification": False,
              "started_at_utc": now(), "source_commit": git("rev-parse", "HEAD"),
              "source_tree": git("rev-parse", "HEAD^{tree}"), "initial_git_status": "",
              "baseline_source_commit": baseline["source_commit"],
              "unchanged_baseline_native_sources": {p: h for p, h in natives.items() if p not in changed},
              "new_or_changed_native_sources": {p: natives[p] for p in sorted(changed)},
              "forced_modules": ordered, "new_public_targets": targets,
              "source_identity": bound, "harness_sha256": harness_digest,
              "cache_preparation": {
                  "dependency_receipt": str(dependency_cache_path), "dependency_receipt_sha256": sha(dependency_cache_path),
                  "native_receipt": str(native_cache_path), "native_receipt_sha256": sha(native_cache_path),
                  "unchanged_native_modules_reused": len(reusable), "new_native_artifacts_reused": False},
              "git_dependencies": package_identities, "commands": []}
    receipt = output / "run.json"

    def command(label, argv):
        log = output / f"{len(report['commands']) + 1:02d}-{label}.log"
        row = {"label": label, "argv": argv, "cwd": str(PROJECT), "started_at_utc": now(),
               "log": log.name}
        report["commands"].append(row)
        put(receipt, report)
        print("Running", label, flush=True)
        with log.open("wb") as stream:
            result = subprocess.run(argv, cwd=PROJECT, stdout=stream, stderr=subprocess.STDOUT)
        row.update(exit_code=result.returncode, finished_at_utc=now(), log_sha256=sha(log))
        put(receipt, report)
        assert result.returncode == 0, label
        return log

    put(receipt, report)
    try:
        version_log = command("lean-version", ["lake", "env", "lean", "--version"])
        version = (PROJECT / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
        assert re.search(r"\bversion\s+" + re.escape(version) + r"[,)]", version_log.read_text())
        command("pins", [sys.executable, "tools/check_pins.py", "--dependencies", "--output", str(output / "pins.json")])
        command("frozen-source-ledger", [sys.executable, "correspondence/build_source_ledger.py", "--check"])
        command("library-and-extension-build", ["lake", "build", "RectangleCLTArxivV1"] + ordered)
        for module in ordered:
            path = module.replace(".", "/")
            command("force-" + module.rsplit(".", 1)[-1], ["lake", "env", "lean", path + ".lean",
                "-o", ".lake/build/lib/lean/" + path + ".olean"])
        command("force-root", ["lake", "env", "lean", "RectangleCLTArxivV1.lean", "-o", ".lake/build/lib/lean/RectangleCLTArxivV1.olean"])
        audit_log = command("registered-axiom-audit", ["lake", "env", "lean", "Audit.lean"])
        command("mapped-supplement-H", ["lake", "env", "lean", "Correspondence/SupplementH.lean"])
        new_log = command("new-full-types-and-axiom-audit", ["lake", "env", "lean", str(harness)])
        new = json.loads(new_log.read_text())
        assert {row["name"] for row in new["endpoints"]} == set(targets)
        assert all(row["expanded_type"] for row in new["endpoints"])
        assert all(row["kernel_import_module"] in declarations[row["name"]]
                   for row in new["endpoints"]), "New public type has an unexpected kernel provider"
        assert set(new["axiom_union"]) <= {"propext", "Classical.choice", "Quot.sound"}
        graph = {row["name"]: set(row["direct_project_dependencies"]) for row in new["project_dependency_graph"]}
        assert all(deps <= set(graph) for deps in graph.values())
        deps_log = command("registered-types-and-dependencies", ["lake", "env", "lean", "Correspondence/Dependencies.lean"])
        deps = json.loads(deps_log.read_text())
        registered_graph = {row["name"]: set(row["direct_project_dependencies"]) for row in deps["project_dependency_graph"]}
        assert all(ds <= set(registered_graph) for ds in registered_graph.values())
        assert sha(harness) == harness_digest
        assert {p: sha(PROJECT / p) for p in bound} == bound, "Bound sources changed during checkpoint"
        final_natives = {str(p.relative_to(PROJECT)): sha(p)
                         for p in sorted((PROJECT / "RectangleCLTArxivV1").rglob("*.lean"))}
        assert final_natives == natives, "Native source file set changed during checkpoint"
        assert git("rev-parse", "HEAD") == report["source_commit"]
        assert git("rev-parse", "HEAD^{tree}") == report["source_tree"]
        assert not git("status", "--porcelain"), "Clean checkout changed during checkpoint"
        assert sha(dependency_cache_path) == report["cache_preparation"]["dependency_receipt_sha256"]
        assert sha(native_cache_path) == report["cache_preparation"]["native_receipt_sha256"]
        assert catalog["check_git_packages"](PROJECT, packages) == package_identities
        report.update(status="passed", finished_at_utc=now(), final_source_identity=bound,
            new_public_expanded_types=len(new["endpoints"]), new_project_dependency_nodes=len(graph),
            new_axiom_union=new["axiom_union"], registered_expanded_types=len(deps["endpoints"]),
            registered_project_dependency_nodes=len(registered_graph),
            registered_axiom_audit_targets=audit_log.read_text().count("(shared transitive axiom audit)"))
    except Exception as error:
        report.update(status="failed", finished_at_utc=now(), failure=str(error))
        raise
    finally:
        put(receipt, report)
    print(json.dumps({k: report[k] for k in ("status", "new_public_expanded_types", "registered_axiom_audit_targets", "registered_expanded_types")}))


if __name__ == "__main__":
    main()
