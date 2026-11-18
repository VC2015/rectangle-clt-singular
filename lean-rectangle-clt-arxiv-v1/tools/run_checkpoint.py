#!/usr/bin/env python3
"""Fresh C.2 elaboration and audit with immutable, hash-addressed run logs.

Run from any directory, after fetching the locked Lake dependencies. This
checks the C.2 checkpoint, not the entire November manuscript or supplement.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[1]
REPO = PROJECT.parent
MODULES = [
    "SignedCoordinates", "SignedObservations", "SignedVariance",
    "BernsteinMixedTail", "ChainingComparison", "GaussianCalibration",
    "ExpectedMaximum",
]
SOURCES = [f"RectangleCLTArxivV1/{name}.lean" for name in MODULES] + [
    "RectangleCLTArxivV1.lean", "Audit.lean", "ChainingImports.lean",
    "Correspondence/C2.lean", "Correspondence/Dependencies.lean",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain", "source-pins.json",
    "tools/check_pins.py", "tools/run_checkpoint.py",
]


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()


def source_identity():
    files = {name: sha(PROJECT / name) for name in SOURCES}
    digest = hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()
    return {"files": files, "aggregate_sha256": digest}


def main():
    global MODULES, SOURCES
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True,
                    help="New output directory; an existing path is refused")
    ap.add_argument("--require-clean", action="store_true")
    ap.add_argument("--scope", choices=("c2", "exported"), default="c2",
                    help="Force C.2 modules or the entire current exported import closure")
    args = ap.parse_args()
    if args.scope == "exported":
        ordered, seen = [], set()

        def visit(name):
            if name in seen:
                return
            seen.add(name)
            path = PROJECT / (name.replace(".", "/") + ".lean")
            for dependency in re.findall(r"(?m)^import (RectangleCLTArxivV1(?:\.[A-Za-z0-9_]+)*)\s*$",
                                         path.read_text()):
                visit(dependency)
            if name != "RectangleCLTArxivV1":
                ordered.append(name.removeprefix("RectangleCLTArxivV1."))

        visit("RectangleCLTArxivV1")
        MODULES = ordered
        SOURCES = list(dict.fromkeys(
            [f"RectangleCLTArxivV1/{name}.lean" for name in MODULES] + SOURCES))
        SOURCES += ["Correspondence/IntrinsicEndpoints.lean", "Correspondence/A1.lean",
                    "Correspondence/B3.lean", "Correspondence/C1Gaussian.lean"]
        for extra in ("Transfers", "IntrinsicTransfersAndLower"):
            if (PROJECT / ("Correspondence/" + extra + ".lean")).exists():
                SOURCES.append("Correspondence/" + extra + ".lean")
    output = args.output.resolve()
    status = git("status", "--porcelain")
    if args.require_clean and status:
        raise SystemExit("A clean checkout is required (including untracked files).")
    output.mkdir(parents=True, exist_ok=False)
    identity = source_identity()
    scope = "Lemma C.2 only" if args.scope == "c2" else "Entire exported checked import closure"
    report = {"scope": scope, "release_wide_certification": False,
              "started_at": now(), "source_commit": git("rev-parse", "HEAD"),
              "source_tree": git("rev-parse", "HEAD^{tree}"),
              "initial_git_status": status, "source_identity": identity,
              "commands": [], "status": "running"}
    receipt = output / "run.json"

    def save():
        receipt.write_text(json.dumps(report, indent=2) + "\n")

    def run(label, argv):
        log = output / f"{len(report['commands']) + 1:02d}-{label}.log"
        row = {"label": label, "argv": argv, "cwd": str(PROJECT),
               "started_at": now(), "log": log.name}
        report["commands"].append(row)
        save()
        print("Running", label, flush=True)
        with log.open("wb") as stream:
            child = subprocess.run(argv, cwd=PROJECT, env=os.environ.copy(),
                                   stdout=stream, stderr=subprocess.STDOUT)
        row.update(finished_at=now(), exit_code=child.returncode, log_sha256=sha(log))
        save()
        if child.returncode:
            raise RuntimeError(f"{label} failed ({child.returncode}); see {log}")
        return log

    save()
    try:
        run("lake-version", ["lake", "--version"])
        run("lean-version", ["lake", "env", "lean", "--version"])
        run("pins", [sys.executable, "tools/check_pins.py", "--dependencies",
                     "--output", str(output / "pins.json")])
        run("frozen-source-ledger", [sys.executable,
                                     "correspondence/build_source_ledger.py", "--check"])
        run("project-build", ["lake", "build"])
        # Re-elaborate source even if the Lake build used an existing artifact.
        # Install the new olean before elaborating the next dependent module.
        for name in MODULES:
            run(f"force-{name}", ["lake", "env", "lean",
                f"RectangleCLTArxivV1/{name}.lean", "-o",
                f".lake/build/lib/lean/RectangleCLTArxivV1/{name}.olean"])
        run("force-root", ["lake", "env", "lean", "RectangleCLTArxivV1.lean", "-o",
                            ".lake/build/lib/lean/RectangleCLTArxivV1.olean"])
        run("chaining-smoke", ["lake", "env", "lean", "ChainingImports.lean"])
        run("chaining-audit", ["lake", "env", "lean",
                               ".lake/packages/generic_chaining/Audit.lean"])
        run("c2-audit", ["lake", "env", "lean", "Audit.lean"])
        run("mapped-types", ["lake", "env", "lean", "Correspondence/C2.lean"])
        if args.scope == "exported":
            for name in ("IntrinsicEndpoints", "A1", "B3", "C1Gaussian"):
                run("mapped-" + name, ["lake", "env", "lean", "Correspondence/" + name + ".lean"])
            for extra in ("Transfers", "IntrinsicTransfersAndLower"):
                if (PROJECT / ("Correspondence/" + extra + ".lean")).exists():
                    run("mapped-" + extra, ["lake", "env", "lean", "Correspondence/" + extra + ".lean"])
        deps_log = run("dependencies", ["lake", "env", "lean", "Correspondence/Dependencies.lean"])
        deps = json.loads(deps_log.read_text())
        graph = {row["name"] for row in deps["project_dependency_graph"]}
        archive_map = json.loads((REPO / "lean-rectangle-clt-singular" /
            "split-v4-certification/statement-map.json").read_text())
        blocked = {row.get("lean_declaration") for row in archive_map["entries"]
                   if row["kind"] == "theorem" and row["number"] in ("1", "2")}
        circular = sorted(graph & blocked)
        dependency_check = {"project_nodes": len(graph), "endpoints": len(deps["endpoints"]),
            "forbidden_final_clt_dependencies": sorted(blocked), "found": circular,
            "passed": not circular}
        (output / "dependency-check.json").write_text(json.dumps(dependency_check, indent=2) + "\n")
        if circular:
            raise RuntimeError(f"C.2 depends on an archived final CLT: {circular}")
        if source_identity() != identity:
            raise RuntimeError("Checkpoint source changed during execution")
        report.update(status="passed", finished_at=now(),
                      final_source_identity=source_identity())
    except Exception as error:
        report.update(status="failed", finished_at=now(), error=str(error))
        save()
        raise
    save()
    print("Checkpoint PASS:", receipt, flush=True)


if __name__ == "__main__":
    main()
