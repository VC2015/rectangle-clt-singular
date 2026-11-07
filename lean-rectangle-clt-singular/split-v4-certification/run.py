#!/usr/bin/env python3
"""Record fresh split-V4 builds without claiming manuscript certification."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import time
from typing import BinaryIO

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
REPO = PACKAGE.parent
TARGET = REPO / "research-rectangle-clt-singular/Unrestricted_CLT-split-V4.tex"
HANDOFF = REPO / "research-rectangle-clt-singular/Unrestricted_CLT_split_V4_Lean_Handoff.md"
TARGET_SHA256 = "f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1"
TARGET_BLOB = "3dd7ea1a9c92e1d8d7ddfcbb6438b20a65ebc78e"
HANDOFF_COMMIT = "2bd43fd98d2a8687ccdda3745f9ac8eac96260dd"
MATHLIB_REV = "c44e0c8ee63ca166450922a373c7409c5d26b00b"


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str, cwd: Path = REPO) -> str | None:
    p = subprocess.run(["git", *args], cwd=cwd, text=True, capture_output=True)
    return p.stdout.strip() if p.returncode == 0 else None


def inventory() -> dict:
    packages = [REPO / p for p in ("lean-kane", "lean-rectangle-clt-local", "lean-rectangle-clt-singular")]
    sources = {}
    manifests = {}
    dependencies = {}
    for package in packages:
        for path in sorted(package.rglob("*.lean")):
            if ".lake" not in path.relative_to(package).parts:
                sources[str(path.relative_to(REPO))] = sha256(path)
        for name in ("lake-manifest.json", "lakefile.toml", "lakefile.lean", "lean-toolchain"):
            path = package / name
            if path.is_file():
                manifests[str(path.relative_to(REPO))] = sha256(path)
        manifest = package / "lake-manifest.json"
        if manifest.is_file():
            for dep in json.loads(manifest.read_text())["packages"]:
                key = f"{package.name}:{dep['name']}"
                # All commands run in the singular root package. Lake resolves
                # inherited Git dependencies in that root's packagesDir, even
                # when their declaring sibling has no local cache of its own.
                depdir = (package / dep["dir"]).resolve() if dep["type"] == "path" else PACKAGE / ".lake/packages" / dep["name"]
                dependencies[key] = {
                    "type": dep["type"], "path": str(depdir),
                    "manifest_revision": dep.get("rev"),
                    "actual_revision": git("rev-parse", "HEAD", cwd=depdir) if depdir.exists() else None,
                    "dirty": git("status", "--porcelain", cwd=depdir) if depdir.exists() else None,
                }
    frozen = {}
    for name in ("VERIFICATION.json", "SUBEXPONENTIAL_VERIFICATION.json", "LOWER_RESULTS_VERIFICATION.json"):
        path = PACKAGE / name
        frozen[name] = sha256(path)
    return {
        "git_commit": git("rev-parse", "HEAD"), "git_branch": git("branch", "--show-current"),
        "git_status_porcelain": git("status", "--porcelain"),
        "git_tracked_diff_sha256": hashlib.sha256((git("diff", "HEAD") or "").encode()).hexdigest(),
        "sources_sha256": sources, "manifests_sha256": manifests,
        "dependencies": dependencies, "frozen_records_sha256": frozen,
        "manuscript_sha256": sha256(TARGET),
        "manuscript_git_blob": git("hash-object", str(TARGET)),
        "handoff_sha256": sha256(HANDOFF),
    }


def proof_inputs(snapshot: dict, mode: str) -> dict:
    # New, unimported SplitV4 files may be edited while reproducing the old
    # baseline. They do not enter its Lean closure. Once the root imports any
    # SplitV4 module, or for a checkpoint run, fingerprint every source.
    root = PACKAGE / "RectangleCLTCompanion.lean"
    exclude_new = mode == "baseline" and "import RectangleCLTCompanion.SplitV4" not in root.read_text()
    return {path: digest for path, digest in snapshot["sources_sha256"].items()
            if not (exclude_new and "/RectangleCLTCompanion/SplitV4/" in path)}


def environment_metadata() -> dict:
    # These are directory selectors, not credentials. Never record the full
    # process environment: proxy and service variables may contain secrets.
    configured = {name: os.environ.get(name) for name in
                  ("ELAN_HOME", "MATHLIB_CACHE_DIR", "XDG_CACHE_HOME")}
    if configured["MATHLIB_CACHE_DIR"] is not None:
        cache_dir = Path(configured["MATHLIB_CACHE_DIR"])
        source = "MATHLIB_CACHE_DIR"
    elif configured["XDG_CACHE_HOME"] is not None:
        cache_dir = Path(configured["XDG_CACHE_HOME"]) / "mathlib"
        source = "XDG_CACHE_HOME/mathlib"
    elif os.environ.get("HOME") is not None:
        cache_dir = Path(os.environ["HOME"]) / ".cache/mathlib"
        source = "HOME/.cache/mathlib"
    else:
        cache_dir = Path(".cache")
        source = "relative .cache fallback"
    if not cache_dir.is_absolute():
        cache_dir = PACKAGE / cache_dir
    return {**configured, "mathlib_effective_cache_dir": str(cache_dir.resolve()),
            "mathlib_cache_dir_source": source}


def commands(mode: str, skip_cache: bool) -> list[tuple[str, list[str], str]]:
    result = [("version", ["lake", "env", "lean", "--version"], "toolchain")]
    if not skip_cache:
        result.append(("cache", ["lake", "exe", "cache", "get"], "optional_infrastructure"))
    result.append(("build", ["lake", "build", "RectangleCLTCompanion"], "proof_build"))
    if mode == "baseline":
        for name in ("Audit", "MainAudit", "CompleteAudit", "SubexponentialAudit", "LowerResultsAudit"):
            result.append((name, ["lake", "env", "lean", f"RectangleCLTCompanion/{name}.lean"], "axiom_audit"))
    else:
        result.append(("CompleteAudit", ["lake", "env", "lean", "RectangleCLTCompanion/CompleteAudit.lean"], "axiom_audit"))
        files = sorted((PACKAGE / "RectangleCLTCompanion/SplitV4").glob("*.lean"))
        targets = [str(p.relative_to(PACKAGE).with_suffix("")).replace("/", ".") for p in files]
        if targets:
            result.append(("split-v4-build", ["lake", "build", *targets], "proof_build"))
        for path in files:
            if path.name.endswith("Audit.lean"):
                result.append((path.stem, ["lake", "env", "lean", str(path.relative_to(PACKAGE))], "axiom_audit"))
    return result


def run_logged(command: list[str], log: BinaryIO, stream: bool) -> int:
    if not stream:
        return subprocess.run(command, cwd=PACKAGE, stdout=log,
                              stderr=subprocess.STDOUT).returncode
    process = subprocess.Popen(command, cwd=PACKAGE, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, bufsize=0,
                               start_new_session=(os.name == "posix"))
    assert process.stdout is not None
    try:
        while chunk := process.stdout.read(65536):
            log.write(chunk)
            log.flush()
            binary_stdout = getattr(sys.stdout, "buffer", None)
            if binary_stdout is not None:
                binary_stdout.write(chunk)
                binary_stdout.flush()
            else:
                # Supports notebook/text-only stdout wrappers. The binary log
                # always retains the exact bytes, including non-UTF-8 output.
                sys.stdout.write(chunk.decode("utf-8", errors="replace"))
                sys.stdout.flush()
        return process.wait()
    except BaseException:
        # Stop Lake and its subprocesses before recording a user interrupt.
        # A separate process group lets this cleanup include child Lean jobs.
        if process.poll() is None or os.name == "posix":
            try:
                if os.name == "posix":
                    os.killpg(process.pid, signal.SIGINT)
                else:
                    process.terminate()
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    if os.name == "posix":
                        os.killpg(process.pid, signal.SIGKILL)
                    else:
                        process.kill()
                except ProcessLookupError:
                    pass
                process.wait()
        raise
    finally:
        process.stdout.close()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("baseline", "checkpoint"))
    parser.add_argument("--output", type=Path, help="New or empty output directory; relative to current directory")
    parser.add_argument("--skip-cache", action="store_true", help="Omit optional cache download, never update dependencies")
    parser.add_argument("--plan", action="store_true", help="Print commands without running them or writing records")
    parser.add_argument("--stream", action="store_true", help="Tee command output live to stdout while preserving exact log bytes")
    args = parser.parse_args()
    plan = commands(args.mode, args.skip_cache)
    if args.plan:
        for name, command, kind in plan:
            print(f"{name} [{kind}]: {shlex.join(command)}")
        return 0
    output = (args.output or HERE / f"logs-{args.mode}").resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error(f"Refusing to overwrite existing evidence in {output}; choose a new directory")
    before = inventory()
    before["proof_inputs_sha256"] = proof_inputs(before, args.mode)
    if before["manuscript_sha256"] != TARGET_SHA256 or before["manuscript_git_blob"] != TARGET_BLOB:
        parser.error("Manuscript bytes do not match pinned handoff; no build run")
    if (PACKAGE / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
        parser.error("Toolchain differs from pinned Lean 4.19.0; no build run")
    manifest = json.loads((PACKAGE / "lake-manifest.json").read_text())
    if next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib") != MATHLIB_REV:
        parser.error("Manifest differs from pinned mathlib revision; no build run")
    record = {
        "schema_version": 1, "mode": args.mode, "started_at": now(),
        "runner_sha256": sha256(Path(__file__).resolve()),
        "environment_metadata": environment_metadata(),
        "stream_stdout": args.stream,
        "handoff_commit": HANDOFF_COMMIT, "cwd": str(PACKAGE),
        "paper_certified": False,
        "scope": "Fresh command evidence only; statement and revised-proof-route certification requires separate mapping and review.",
        "before": before, "commands": [],
    }
    record_path = output / "run.json"

    def save() -> None:
        record_path.write_text(json.dumps(record, indent=2) + "\n")

    save()
    failure = False
    for index, (name, command, kind) in enumerate(plan, 1):
        entry = {"name": name, "argv": command, "shell_display": shlex.join(command), "kind": kind,
                 "cwd": str(PACKAGE), "started_at": now(), "log": f"{index:02d}-{name}.log"}
        print(f"[{now()}] {shlex.join(command)}", flush=True)
        start = time.monotonic()
        with (output / entry["log"]).open("wb") as log:
            try:
                entry["exit_code"] = run_logged(command, log, args.stream)
            except OSError as exc:
                log.write((str(exc) + "\n").encode())
                entry["exit_code"] = 127
            except KeyboardInterrupt:
                log.write(b"Runner interrupted; this is not a proof failure.\n")
                entry["exit_code"] = 130
        entry["finished_at"] = now()
        entry["duration_seconds"] = round(time.monotonic() - start, 3)
        entry["log_sha256"] = sha256(output / entry["log"])
        record["commands"].append(entry)
        print(f"  exit {entry['exit_code']}; {output / entry['log']}", flush=True)
        save()
        if entry["exit_code"] == 130:
            failure = True
            record["interrupted"] = True
            record["not_run"] = [n for n, _, _ in plan[index:]]
            break
        if entry["exit_code"] != 0:
            if kind == "optional_infrastructure":
                record.setdefault("infrastructure_warnings", []).append(name)
            else:
                failure = True
                record.setdefault("failed_commands", []).append(name)
                if kind in ("toolchain", "proof_build"):
                    record["stopped_at_first_failing_build"] = name
                    record["not_run"] = [n for n, _, _ in plan[index:]]
                    break
        if kind == "toolchain" and entry["exit_code"] == 0:
            if "version 4.19.0" not in (output / entry["log"]).read_text():
                failure = True
                record["toolchain_version_mismatch"] = True
                record["not_run"] = [n for n, _, _ in plan[index:]]
                break
    record["after"] = inventory()
    record["after"]["proof_inputs_sha256"] = proof_inputs(record["after"], args.mode)
    for key in ("proof_inputs_sha256", "manifests_sha256", "frozen_records_sha256", "manuscript_sha256"):
        if record["after"][key] != before[key]:
            record.setdefault("inputs_changed_during_run", []).append(key)
            failure = True
    for key, dep in record["after"]["dependencies"].items():
        if dep["type"] == "git" and dep["actual_revision"] != dep["manifest_revision"]:
            record.setdefault("dependency_revision_mismatches", []).append(key)
            failure = True
    record["finished_at"] = now()
    record["required_commands_passed"] = not failure
    record["exit_code"] = 1 if failure else 0
    save()
    print(f"Evidence: {record_path}; paper_certified=false", flush=True)
    return record["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
