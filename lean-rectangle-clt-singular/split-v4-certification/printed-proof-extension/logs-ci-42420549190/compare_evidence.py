#!/usr/bin/env python3
"""Compare preserved CI artifacts with the exact frozen R local execution.

This does not relax or invoke the strict local verify_record.py against CI.
It records the actual synthetic checkout and checks source equivalence.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import stat
import zipfile

R = "92896b8a2a4099357486587d17ca1921a3dba161"
M = "e692196356de50c00fcdd66ddad0f3706db0241c"
CI = "88b6db94075c9f3fcb8cd2d1de062ad4412da1a6"
HANDOFF = "2bd43fd98d2a8687ccdda3745f9ac8eac96260dd"
TREE = "2b1a8ff7f82daa435e3313108bf438b35566c2eb"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PACKAGE = "lean-rectangle-clt-singular"
LOCAL_RUN_SHA = "7f7d9b51c82b948bf6c9be2bfac5ef3739ac97fcb219b57f2aaa9d85243031eb"
LOCAL_VALIDATION_SHAS = {"d7c6af672e6cad33e272f3f1c890ba4d19a5cbecf7a895fcad939cfced02a975",
                         "5a998a9d6680a621bce3c235efa71e440e8210aaac06f2cf470f7a0e16ab0bd7"}
RUNNER_SHA = "dcc92f85f5eb05146dd0553d0fe838245db3edec7912f156862d4a26f8b484fe"
R_VALIDATOR_SHA = "ed96ef5102fd1cc413b92f02f8404fb4ec53b24f4c9bf76c70e94a3b9420aaad"
PAPER = "research-rectangle-clt-singular/Unrestricted_CLT-split-V4.tex"
HANDOFF_PATH = "research-rectangle-clt-singular/Unrestricted_CLT_split_V4_Lean_Handoff.md"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_digest(value: dict) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()


def git_blob(repo: Path, commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=repo)


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def tagged(path: Path, tag: str) -> tuple[dict, int]:
    records = {}
    count = 0
    with path.open() as f:
        for line_number, raw in enumerate(f, 1):
            line = raw
            if raw.startswith("{"):
                try:
                    item = json.loads(raw)
                    if isinstance(item, dict) and "message" in item:
                        line = str(item["message"])
                except json.JSONDecodeError:
                    pass
            pos = line.find(tag + " ")
            if pos < 0:
                continue
            item = json.loads(line[pos + len(tag) + 1:])
            require(isinstance(item, dict), f"Nonobject {tag} record {path}:{line_number}")
            name = item.get("declaration")
            require(isinstance(name, str) and bool(name), f"Missing declaration {path}:{line_number}")
            require(name not in records or records[name] == item, f"Conflicting repeated record {name}")
            if "transitive_axioms" in item:
                require(set(item["transitive_axioms"]) <= ALLOWED, f"Unexpected axiom {name}")
            records[name] = item
            count += 1
    require(bool(records), f"No {tag} records: {path}")
    return records, count


def validate_logs(directory: Path, mode: str, expected_commands: list | None = None) -> tuple[dict, dict]:
    run = read_json(directory / "run.json")
    require(run.get("schema_version") == 1, "Unsupported run evidence schema")
    require(run["mode"] == mode, f"Wrong mode {directory}")
    require(run["required_commands_passed"] is True and run["exit_code"] == 0, f"Required command failure {directory}")
    require(run["paper_certified"] is False, "Runner may not claim paper certification")
    require(run["handoff_commit"] == HANDOFF, "Different handoff")
    for flag in ("failed_commands", "not_run", "inputs_changed_during_run", "dependency_revision_mismatches", "interrupted", "toolchain_version_mismatch", "stopped_at_first_failing_build"):
        require(not run.get(flag), f"Run flag {flag}: {directory}")
    commands = run["commands"]
    if expected_commands is not None:
        require([(c["name"], c["argv"], c["kind"]) for c in commands] == expected_commands, f"Command plan mismatch {directory}")
    require(len({c["name"] for c in commands}) == len(commands), "Duplicate command names")
    expected_files = {"run.json", *(c["log"] for c in commands)}
    require({p.name for p in directory.iterdir()} == expected_files, f"Extra/missing evidence files {directory}")
    require(all(p.is_file() and not p.is_symlink() for p in directory.iterdir()), "Unsafe evidence file")
    previous = dt.datetime.fromisoformat(run["started_at"])
    finished = dt.datetime.fromisoformat(run["finished_at"])
    optional = []
    required = []
    log_hashes = {}
    for index, c in enumerate(commands, 1):
        require(c["log"] == f"{index:02d}-{c['name']}.log", "Noncanonical or duplicate command log reference")
        require(c["cwd"] == run["cwd"], "Command working directory differs from recorded run directory")
        started = dt.datetime.fromisoformat(c["started_at"])
        ended = dt.datetime.fromisoformat(c["finished_at"])
        require(previous <= started <= ended <= finished, f"Nonmonotone command timestamps: {c['name']}")
        previous = ended
        path = directory / c["log"]
        require(digest(path) == c["log_sha256"], f"Log hash mismatch: {path}")
        log_hashes[c["log"]] = c["log_sha256"]
        if c["kind"] == "optional_infrastructure":
            optional.append({"name": c["name"], "exit_code": c["exit_code"], "log": c["log"], "log_sha256": c["log_sha256"], "duration_seconds": c["duration_seconds"]})
        else:
            require(c["exit_code"] == 0, f"Required command failed: {c['name']}")
            required.append(c["name"])
    require("version 4.19.0" in (directory / commands[0]["log"]).read_text(), "Wrong actual Lean version")
    return run, {"commands": len(commands), "required_successful_commands": len(required), "optional_infrastructure": optional,
                 "run_json_sha256": digest(directory / "run.json"), "log_sha256": log_hashes,
                 "started_at": run["started_at"], "finished_at": run["finished_at"]}


def validate_snapshot(ci: dict, local: dict, which: str) -> dict:
    c, l = ci[which], local[which]
    require(c["git_commit"] == CI, f"CI {which} checkout is not the recorded synthetic merge")
    require(l["git_commit"] == R, f"Local {which} checkout is not R")
    for snapshot, label in ((c, "CI"), (l, "local")):
        require(snapshot["git_status_porcelain"] == "", f"Dirty {label} {which}")
        require(snapshot["git_tracked_diff_sha256"] == hashlib.sha256(b"").hexdigest(), f"Tracked diff {label}")
    fields = ["sources_sha256", "proof_inputs_sha256", "manifests_sha256", "frozen_records_sha256", "manuscript_sha256", "manuscript_git_blob", "handoff_sha256"]
    for field in fields:
        require(c[field] == l[field], f"CI/local {which} {field} differs")
    require(len(c["sources_sha256"]) == 1024 and len(c["manifests_sha256"]) == 9, "Incomplete frozen source/config inventory")
    require(c["proof_inputs_sha256"] == c["sources_sha256"], "Incomplete proof inventory")
    require(c["dependencies"].keys() == l["dependencies"].keys(), "Dependency inventory differs")
    git_dependencies, path_dependencies = {}, {}
    for name, dep in c["dependencies"].items():
        old = l["dependencies"][name]
        for field in ("type", "manifest_revision"):
            require(dep[field] == old[field], f"Dependency specification differs {name}")
        require(dep["dirty"] == "" and old["dirty"] == "", f"Dirty dependency {name}")
        if dep["type"] == "git":
            require(dep["actual_revision"] == dep["manifest_revision"] == old["actual_revision"], f"Unpinned Git dependency {name}")
            git_dependencies[name] = dep["actual_revision"]
        elif dep["type"] == "path":
            require(dep["actual_revision"] == CI and old["actual_revision"] == R, f"Path dependency checkout mismatch {name}")
            path_dependencies[name] = {"ci": CI, "local": R}
        else:
            raise ValueError(f"Unknown dependency type {name}")
    return {"source_files": len(c["sources_sha256"]), "configuration_files": len(c["manifests_sha256"]),
            "source_inventory_sha256": canonical_digest(c["sources_sha256"]), "configuration_inventory_sha256": canonical_digest(c["manifests_sha256"]),
            "manuscript_sha256": c["manuscript_sha256"], "frozen_records_sha256": c["frozen_records_sha256"],
            "clean_pinned_git_dependencies": git_dependencies, "clean_path_dependencies": path_dependencies}


def compare(args: argparse.Namespace) -> dict:
    local_path = args.local.resolve()
    ci_path = args.ci.resolve()
    baseline_path = args.baseline.resolve()
    require(digest(local_path / "run.json") == LOCAL_RUN_SHA, "Local run is not the independently approved frozen R run")
    require(digest(args.local_validation) in LOCAL_VALIDATION_SHAS, "Local validation is not an independently approved R receipt")
    tree = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", R], cwd=args.repo).decode().splitlines()
    packages = {"lean-kane", "lean-rectangle-clt-local", PACKAGE}
    r_lean = {p for p in tree if p.endswith(".lean") and p.split("/")[0] in packages and "/.lake/" not in p}
    prefix = PACKAGE + "/RectangleCLTCompanion/SplitV4/"
    top_files = sorted(p.removeprefix(PACKAGE + "/") for p in r_lean if p.startswith(prefix) and "/" not in p[len(prefix):])
    plan = [("version", ["lake", "env", "lean", "--version"], "toolchain"),
            ("build", ["lake", "build", "RectangleCLTCompanion"], "proof_build"),
            ("CompleteAudit", ["lake", "env", "lean", "RectangleCLTCompanion/CompleteAudit.lean"], "axiom_audit"),
            ("split-v4-build", ["lake", "build", *[p.removesuffix(".lean").replace("/", ".") for p in top_files]], "proof_build")]
    plan += [(Path(p).stem, ["lake", "env", "lean", p], "axiom_audit") for p in top_files if p.endswith("Audit.lean")]
    require(len(plan) == 170, "Wrong local checkpoint plan")
    local, local_report = validate_logs(local_path, "checkpoint", plan)
    ci, ci_report = validate_logs(ci_path, "checkpoint", plan)
    baseline_plan = [("version", ["lake", "env", "lean", "--version"], "toolchain"),
        ("cache", ["lake", "exe", "cache", "get"], "optional_infrastructure"),
        ("build", ["lake", "build", "RectangleCLTCompanion"], "proof_build")]
    baseline_plan += [(n, ["lake", "env", "lean", f"RectangleCLTCompanion/{n}.lean"], "axiom_audit")
                      for n in ("Audit", "MainAudit", "CompleteAudit", "SubexponentialAudit", "LowerResultsAudit")]
    baseline, baseline_report = validate_logs(baseline_path, "baseline", baseline_plan)
    require(baseline["before"]["git_commit"] == baseline["after"]["git_commit"] == HANDOFF, "Pristine baseline checkout differs")
    require(hashlib.sha256(git_blob(args.repo, R, PACKAGE + "/split-v4-certification/run.py")).hexdigest() == RUNNER_SHA, "Immutable R runner bytes differ")
    require(hashlib.sha256(git_blob(args.repo, R, PACKAGE + "/split-v4-certification/printed-proof-extension/verify_record.py")).hexdigest() == R_VALIDATOR_SHA, "Immutable strict R validator bytes differ")
    require(ci["runner_sha256"] == local["runner_sha256"] == baseline["runner_sha256"] == RUNNER_SHA, "Runner bytes differ from frozen R")
    snapshots = {which: validate_snapshot(ci, local, which) for which in ("before", "after")}
    require(snapshots["before"] == snapshots["after"], "CI source/config/dependencies changed during run")
    require(ci["before"]["dependencies"] == ci["after"]["dependencies"], "CI dependency paths/revisions changed")
    config_names = {"lake-manifest.json", "lakefile.lean", "lakefile.toml", "lean-toolchain"}
    r_configs = {p for p in tree if len(p.split("/")) == 2 and p.split("/")[0] in packages and Path(p).name in config_names}
    r_specs = {}
    for package in packages:
        for dep in json.loads(git_blob(args.repo, R, package + "/lake-manifest.json"))["packages"]:
            r_specs[package + ":" + dep["name"]] = dep
    for which in ("before", "after"):
        require(set(ci[which]["manifests_sha256"]) == r_configs, "CI configuration inventory differs from immutable R")
        require(set(ci[which]["dependencies"]) == set(r_specs), "CI dependency inventory differs from immutable R")
        for name, dep in ci[which]["dependencies"].items():
            spec = r_specs[name]
            require(dep["type"] == spec["type"] and dep["manifest_revision"] == spec.get("rev"), "CI dependency differs from immutable R manifest: " + name)
    require(subprocess.check_output(["git", "rev-parse", R + "^{tree}"], cwd=args.repo).decode().strip() == TREE, "Immutable R Git tree differs")
    for field in ("sources_sha256", "manifests_sha256"):
        for path, expected in ci["before"][field].items():
            require(hashlib.sha256(git_blob(args.repo, R, path)).hexdigest() == expected, f"Immutable R blob differs: {path}")
    require(set(ci["before"]["sources_sha256"]) == r_lean, "CI Lean inventory differs from immutable R tree")
    for path, field in ((PAPER, "manuscript_sha256"), (HANDOFF_PATH, "handoff_sha256")):
        require(hashlib.sha256(git_blob(args.repo, R, path)).hexdigest() == ci["before"][field], f"CI {field} differs from immutable R")
    require(ci["before"]["manuscript_git_blob"] == subprocess.check_output(["git", "rev-parse", R + ":" + PAPER], cwd=args.repo).decode().strip(), "CI manuscript Git blob differs from immutable R")
    for name, expected in ci["before"]["frozen_records_sha256"].items():
        require(hashlib.sha256(git_blob(args.repo, R, PACKAGE + "/" + name)).hexdigest() == expected, f"Immutable frozen record differs: {name}")
    handoff_tree = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", HANDOFF], cwd=args.repo).decode().splitlines()
    handoff_lean = {p for p in handoff_tree if p.endswith(".lean") and p.split("/")[0] in packages and "/.lake/" not in p}
    handoff_configs = {p for p in handoff_tree if len(p.split("/")) == 2 and p.split("/")[0] in packages and Path(p).name in config_names}
    baseline_snapshots = {}
    handoff_specs = {}
    for package in packages:
        for dep in json.loads(git_blob(args.repo, HANDOFF, package + "/lake-manifest.json"))["packages"]:
            handoff_specs[package + ":" + dep["name"]] = dep
    baseline_invariant_fields = ("sources_sha256", "proof_inputs_sha256", "manifests_sha256", "git_status_porcelain", "git_tracked_diff_sha256",
                                 "frozen_records_sha256", "manuscript_sha256", "manuscript_git_blob", "handoff_sha256")
    expected_baseline_infrastructure = {"?? lean-kane/.lake", "?? lean-rectangle-clt-local/.lake", "?? lean-rectangle-clt-singular/.lake",
                                        "?? lean-rectangle-clt-singular/split-v4-certification/"}
    for field in baseline_invariant_fields:
        require(baseline["before"][field] == baseline["after"][field], "Pristine baseline field changed during run: " + field)
    initialized_baseline_git_dependencies = []
    require(baseline["before"]["dependencies"].keys() == baseline["after"]["dependencies"].keys(), "Pristine baseline dependency inventory changed")
    for name, dep in baseline["before"]["dependencies"].items():
        after_dep = baseline["after"]["dependencies"][name]
        require(dep.keys() == after_dep.keys() == {"type", "path", "manifest_revision", "actual_revision", "dirty"}, "Pristine dependency record fields differ: " + name)
        for field in ("type", "path", "manifest_revision"):
            require(dep[field] == after_dep[field], "Pristine baseline dependency specification/path changed: " + name)
        if dep["type"] == "path":
            require(dep == after_dep, "Pristine baseline path dependency changed: " + name)
    for which in ("before", "after"):
        snapshot = baseline[which]
        require(snapshot["proof_inputs_sha256"] == snapshot["sources_sha256"], "Incomplete pristine baseline proof input inventory")
        require(set(snapshot["git_status_porcelain"].splitlines()) == expected_baseline_infrastructure, "Pristine baseline status differs from the exact planned cache symlinks/copied runner")
        require(set(snapshot["sources_sha256"]) == handoff_lean, f"Incomplete pristine handoff Lean inventory {which}")
        require(set(snapshot["manifests_sha256"]) == handoff_configs, f"Incomplete pristine handoff configuration inventory {which}")
        for field in ("sources_sha256", "manifests_sha256", "proof_inputs_sha256"):
            for path, expected in snapshot[field].items():
                require(hashlib.sha256(git_blob(args.repo, HANDOFF, path)).hexdigest() == expected, f"Pristine handoff input differs: {path}")
        require(snapshot["git_tracked_diff_sha256"] == hashlib.sha256(b"").hexdigest(), f"Tracked pristine baseline source change {which}")
        require(hashlib.sha256(git_blob(args.repo, HANDOFF, PAPER)).hexdigest() == snapshot["manuscript_sha256"], f"Pristine baseline manuscript differs {which}")
        require(hashlib.sha256(git_blob(args.repo, HANDOFF, HANDOFF_PATH)).hexdigest() == snapshot["handoff_sha256"], f"Pristine baseline handoff differs {which}")
        require(snapshot["manuscript_git_blob"] == subprocess.check_output(["git", "rev-parse", HANDOFF + ":" + PAPER], cwd=args.repo).decode().strip(), "Pristine manuscript Git blob differs")
        require(set(snapshot["frozen_records_sha256"]) == {"VERIFICATION.json", "SUBEXPONENTIAL_VERIFICATION.json", "LOWER_RESULTS_VERIFICATION.json"}, "Incomplete pristine historical-record inventory")
        for name, expected in snapshot["frozen_records_sha256"].items():
            require(hashlib.sha256(git_blob(args.repo, HANDOFF, PACKAGE + "/" + name)).hexdigest() == expected, "Pristine historical record differs: " + name)
        require(set(snapshot["dependencies"]) == set(handoff_specs), "Incomplete pristine dependency inventory")
        for name, dep in snapshot["dependencies"].items():
            spec = handoff_specs[name]
            require(dep["type"] == spec["type"] and dep["manifest_revision"] == spec.get("rev"), "Pristine dependency differs from frozen handoff manifest: " + name)
            if dep["type"] == "git":
                if which == "before" and dep["actual_revision"] is None:
                    require(dep["dirty"] is None, f"Partly initialized pristine Git dependency {name}")
                    require(next(c for c in baseline["commands"] if c["name"] == "cache")["exit_code"] == 0, "Cold baseline dependency initialization requires a successful recorded cache command")
                    initialized_baseline_git_dependencies.append({"dependency": name, "manifest_revision": dep["manifest_revision"],
                        "before_actual_revision": None, "before_dirty": None,
                        "after_actual_revision": baseline["after"]["dependencies"][name]["actual_revision"],
                        "after_dirty": baseline["after"]["dependencies"][name]["dirty"]})
                else:
                    require(dep["dirty"] == "", f"Dirty pristine Git dependency {name}")
                    require(dep["actual_revision"] == dep["manifest_revision"], f"Unpinned pristine Git dependency {name}")
            elif dep["type"] == "path":
                require(dep["dirty"] == snapshot["git_status_porcelain"], "Pristine path dependency status differs from the exact planned infrastructure: " + name)
                require(dep["actual_revision"] == HANDOFF, f"Pristine path dependency checkout differs {name}")
            else:
                raise ValueError(f"Unknown pristine dependency type {name}")
        baseline_snapshots[which] = {"actual_checkout": snapshot["git_commit"], "git_status_porcelain": snapshot["git_status_porcelain"],
            "source_files": len(handoff_lean), "configuration_files": len(handoff_configs), "dependencies": snapshot["dependencies"],
            "source_inventory_sha256": canonical_digest(snapshot["sources_sha256"]), "configuration_inventory_sha256": canonical_digest(snapshot["manifests_sha256"]),
            "manuscript_sha256": snapshot["manuscript_sha256"]}
    baseline_report["snapshots"] = baseline_snapshots
    baseline_report["git_dependencies_initialized_from_manifest"] = initialized_baseline_git_dependencies
    baseline_report["dependency_initialization_note"] = "Absent Git checkouts in the cold baseline may be exactly (actual_revision=None, dirty=None) before the successful cache command; all are required to be clean and manifest-pinned afterward. Specifications and paths cannot change. This exception does not apply to either checkpoint snapshot."
    baseline_report["planned_untracked_runner_note"] = "The workflow copies run.py into the frozen handoff worktree; actual porcelain status is preserved above. Lean/config/manuscript hashes must still equal immutable 2bd43fd inputs."
    validation = read_json(args.local_validation)
    require(validation["evidence_gate_passed"] is True and validation["proof_commit"] == R, "Local strict R evidence gate did not pass")
    require(validation["required_commands"] == 170 and validation["run_json_sha256"] == local_report["run_json_sha256"], "Local validation names a different run")
    commands = {c["name"]: c for c in ci["commands"]}
    local_commands = {c["name"]: c for c in local["commands"]}
    datasets = {}
    for name, tag, expected in [("DependencyAudit", "SPLITV4_DEPENDENCY", 3751),
            ("PrintedDependencyAudit", "PRINTEDV4_DEPENDENCY", 4724),
            ("PrintedCorrespondenceAudit", "PRINTED_CORRESPONDENCE_BINDING", 811)]:
        c_records, c_raw = tagged(ci_path / commands[name]["log"], tag)
        l_records, l_raw = tagged(local_path / local_commands[name]["log"], tag)
        b_records, b_raw = tagged(ci_path / commands["split-v4-build"]["log"], tag)
        require(len(c_records) == expected, f"Wrong {name} record count")
        require(c_records == l_records == b_records, f"CI/local/build {name} records differ")
        if name == "PrintedDependencyAudit":
            extension = {n: x for n, x in c_records.items() if x["module"].startswith("RectangleCLTCompanion.SplitV4.Printed.")}
            require(len(extension) == 973, "Wrong new printed declaration count")
            old, _ = tagged(ci_path / commands["DependencyAudit"]["log"], "SPLITV4_DEPENDENCY")
            require(all(c_records.get(n) == x for n, x in old.items()), "Printed closure changes original records")
        datasets[name] = {"exact_records": expected, "ci_raw_records": c_raw, "local_raw_records": l_raw,
                          "ci_build_raw_records": b_raw, "canonical_sha256": canonical_digest(c_records),
                          "ci_equals_local_equals_ci_build": True}
    merge = read_json(args.merge_metadata)
    require(merge["sha"] == CI and merge["tree"]["sha"] == TREE, "Synthetic merge metadata differs")
    require([p["sha"] for p in merge["parents"]] == [M, R], "Synthetic merge parents differ")
    run_meta = read_json(args.run_metadata)
    require(run_meta["id"] == 42420549190 and run_meta["head_sha"] == R and run_meta["conclusion"] == "success", "Wrong/failed exact-head workflow")
    require(run_meta["head_commit"]["tree_id"] == TREE, "R and CI synthetic trees differ")
    checks = read_json(args.check_metadata)
    check = next(c for c in checks["check_runs"] if c["id"] == 128547820210)
    require(check["head_sha"] == R and check["conclusion"] == "success" and check["status"] == "completed", "Wrong/failed exact-R check run")
    jobs = read_json(args.job_metadata)
    job = next(j for j in jobs["jobs"] if j["id"] == 128547820210)
    require(job["run_id"] == 42420549190 and job["head_sha"] == R and job["conclusion"] == "success" and job["status"] == "completed", "Wrong/failed exact-R workflow job")
    artifact = read_json(args.artifact_metadata)
    require(artifact["workflow_run"]["id"] == 42420549190 and artifact["workflow_run"]["head_sha"] == R, "Artifact associated with different workflow/head")
    archive_sha = digest(args.archive)
    server_digest = artifact.get("digest")
    if server_digest:
        require(server_digest == "sha256:" + archive_sha, "Downloaded archive differs from GitHub artifact digest")
    extraction = read_json(args.extraction_manifest)
    require(extraction["archive_sha256"] == archive_sha and extraction["archive_bytes"] == args.archive.stat().st_size, "Extraction manifest names different archive")
    root = args.extracted_root.resolve()
    require(not args.extracted_root.is_symlink(), "Unsafe extraction root")
    actual_files = {str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()}
    manifest_files = {f["path"]: f for f in extraction["files"]}
    require(len(manifest_files) == len(extraction["files"]), "Duplicate extraction manifest path")
    require(actual_files == set(manifest_files), "Extracted artifact inventory differs")
    with zipfile.ZipFile(args.archive) as archive:
        zip_files = {}
        canonical_names = set()
        for item in archive.infolist():
            from pathlib import PurePosixPath
            posix = PurePosixPath(item.filename)
            require(not posix.is_absolute() and ".." not in posix.parts and "\\" not in item.filename and ":" not in item.filename, "Unsafe ZIP member path")
            canonical_name = str(posix)
            require(canonical_name not in canonical_names, "Duplicate canonical ZIP member")
            canonical_names.add(canonical_name)
            mode = item.external_attr >> 16
            require(not stat.S_ISLNK(mode) and stat.S_IFMT(mode) in (0, stat.S_IFREG, stat.S_IFDIR), "Nonregular ZIP member")
            if item.is_dir():
                continue
            require(item.filename == canonical_name, "Noncanonical ZIP file path")
            zip_files[item.filename] = item
        require(set(zip_files) == set(manifest_files), "ZIP payload/member inventory differs from extraction manifest")
        for name, item in zip_files.items():
            expected = manifest_files[name]
            require(item.file_size == expected["bytes"] and item.CRC == expected["zip_crc32"], "ZIP size/CRC differs from manifest: " + name)
            h = hashlib.sha256()
            count = 0
            with archive.open(item) as source:
                for chunk in iter(lambda: source.read(1024 * 1024), b""):
                    h.update(chunk)
                    count += len(chunk)
            require(count == expected["bytes"] and h.hexdigest() == expected["sha256"], "ZIP payload bytes differ from manifest: " + name)
    for item in extraction["files"]:
        path = root / item["path"]
        require(path.is_file() and not path.is_symlink() and digest(path) == item["sha256"], "Extracted artifact file differs: " + item["path"])
    require(ci_path.is_relative_to(root) and baseline_path.is_relative_to(root), "Compared logs are not inside the preserved artifact extraction")
    published_root = "logs-ci-42420549190"
    published_extracted_root = published_root + "/" + args.extracted_root.name
    ci_relative = str(ci_path.relative_to(root))
    baseline_relative = str(baseline_path.relative_to(root))
    return {"schema_version": 1, "comparison_passed": True, "comparison_created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
            "scope": "Independent CI source-equivalence and exact execution-record comparison; the strict local R validator is unchanged and was not applied to the synthetic CI checkout.",
            "proof_commit": R, "preserved_baseline_merge": M, "actual_ci_checkout": CI, "actual_ci_checkout_tree": TREE,
            "synthetic_merge_tree_equals_R_tree": True, "workflow_run_id": 42420549190, "workflow_run_attempt": run_meta["run_attempt"],
            "workflow_url": run_meta["html_url"], "api_head_sha": R, "ci_conclusion": run_meta["conclusion"],
            "check_run_id": check["id"], "check_run_url": check["html_url"], "check_run_conclusion": check["conclusion"],
            "workflow_job_id": job["id"], "workflow_job_url": job["html_url"], "workflow_job_conclusion": job["conclusion"],
            "artifact": {"id": artifact["id"], "name": artifact["name"], "workflow_run_id": artifact["workflow_run"]["id"],
                "archive_file": args.archive.name, "archive_sha256": archive_sha, "archive_bytes": args.archive.stat().st_size,
                "github_digest": server_digest, "github_digest_verified": bool(server_digest),
                "extraction_manifest_sha256": digest(args.extraction_manifest), "extracted_files": len(extraction["files"])},
            "api_evidence_sha256": {"run": digest(args.run_metadata), "jobs": digest(args.job_metadata), "check_runs": digest(args.check_metadata),
                "synthetic_merge": digest(args.merge_metadata), "artifact": digest(args.artifact_metadata)},
            "evidence_paths": {"root": published_root, "archive": published_root + "/" + args.archive.name,
                "extraction_manifest": published_root + "/" + args.extraction_manifest.name,
                "checkpoint_log_directory": published_extracted_root + "/" + ci_relative,
                "checkpoint_run_json": published_extracted_root + "/" + ci_relative + "/run.json",
                "pristine_baseline_log_directory": published_extracted_root + "/" + baseline_relative,
                "pristine_baseline_run_json": published_extracted_root + "/" + baseline_relative + "/run.json",
                "api_run": published_root + "/" + args.run_metadata.name, "api_jobs": published_root + "/" + args.job_metadata.name,
                "api_check_runs": published_root + "/" + args.check_metadata.name,
                "api_merge": published_root + "/" + args.merge_metadata.name, "api_artifact": published_root + "/" + args.artifact_metadata.name},
            "comparison_scripts_sha256": {"compare_evidence.py": digest(Path(__file__)), "extract_artifact.py": digest(Path(__file__).with_name("extract_artifact.py"))},
            "ci_checkpoint": ci_report, "pristine_ci_baseline": baseline_report, "local_checkpoint": local_report,
            "strict_local_validation_sha256": digest(args.local_validation), "immutable_R_blobs_match": True,
            "snapshot_equivalence": snapshots, "exact_semantic_records": datasets,
            "preserved_dependency_records": 3751, "expanded_dependency_records": 4724,
            "new_printed_declaration_records": 973, "exact_correspondence_bindings": 811,
            "permitted_axioms": sorted(ALLOWED), "source_files": 1024, "configuration_files": 9}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("ci", "baseline", "local", "merge-metadata", "run-metadata", "job-metadata", "check-metadata", "artifact-metadata", "archive", "extracted-root", "extraction-manifest", "local-validation", "repo", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = compare(args)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("comparison_passed", "proof_commit", "actual_ci_checkout", "workflow_run_id", "source_files", "configuration_files", "expanded_dependency_records", "exact_correspondence_bindings")}))


if __name__ == "__main__":
    main()
