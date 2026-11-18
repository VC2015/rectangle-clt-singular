#!/usr/bin/env python3
"""Build, force and audit the intrinsic paired/Bennett comparison checkpoint."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
MODULES = ["PairedGaussianContractions", "PairedCommonPointFourth",
           "PairedGaussianRemainder", "PairedIntrinsicComparison", "PairedIntrinsicBennett"]
EVIDENCE = PROJECT / "evidence/paired-intrinsic"


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=PROJECT, text=True).strip()


def identity():
    paths = set()
    queue = [PROJECT / "RectangleCLTArxivV1/PairedIntrinsicBennett.lean"]
    while queue:
        path = queue.pop()
        if path in paths:
            continue
        paths.add(path)
        for name in re.findall(r"^import (RectangleCLTArxivV1(?:\.[A-Za-z0-9_]+)*)", path.read_text(), re.M):
            dep = PROJECT / (name.replace(".", "/") + ".lean")
            assert dep.is_file(), dep
            queue.append(dep)
    paths.update(EVIDENCE / name for name in ["Audit.lean", "ExpandedTypes.lean", "targets.json"])
    paths.update(PROJECT / name for name in ["tools/run_paired_checkpoint.py", "lakefile.toml",
        "lake-manifest.json", "lean-toolchain", "source-pins.json"])
    return {str(path.relative_to(PROJECT)): sha(path) for path in sorted(paths)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--require-clean", action="store_true")
    args = ap.parse_args()
    status = git("status", "--porcelain")
    if args.require_clean and status:
        raise SystemExit("A clean checkout is required.")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    initial = identity()
    report = {"scope": "Intrinsic Lemmas E.1/E.3/E.4 and Theorem 2(ii)",
              "release_wide_certification": False, "started_at": now(),
              "source_commit": git("rev-parse", "HEAD"), "source_tree": git("rev-parse", "HEAD^{tree}"),
              "initial_git_status": status, "initial_source_identity": initial,
              "commands": [], "status": "running"}
    receipt = out / "run.json"

    def save():
        receipt.write_text(json.dumps(report, indent=2) + "\n")

    def run(name, argv):
        log = out / f"{len(report['commands']) + 1:02d}-{name}.log"
        row = {"label": name, "argv": argv, "cwd": str(PROJECT), "started_at": now(), "log": log.name}
        report["commands"].append(row)
        save()
        print("Running", name, flush=True)
        with log.open("wb") as stream:
            result = subprocess.run(argv, cwd=PROJECT, env=os.environ.copy(),
                                    stdout=stream, stderr=subprocess.STDOUT)
        row.update(exit_code=result.returncode, finished_at=now(), log_sha256=sha(log))
        save()
        if result.returncode:
            raise RuntimeError(f"{name} failed; see {log}")
        return log

    save()
    try:
        run("lake-version", ["lake", "--version"])
        run("lean-version", ["lake", "env", "lean", "--version"])
        run("pins", ["python3", "tools/check_pins.py", "--dependencies", "--output", str(out / "pins.json")])
        run("build", ["lake", "build", "RectangleCLTArxivV1.PairedIntrinsicBennett"])
        for name in MODULES:
            run("force-" + name, ["lake", "env", "lean", "RectangleCLTArxivV1/" + name + ".lean",
                "-o", ".lake/build/lib/lean/RectangleCLTArxivV1/" + name + ".olean"])
        run("audit", ["lake", "env", "lean", "evidence/paired-intrinsic/Audit.lean"])
        path = run("expanded-types", ["lake", "env", "lean", "evidence/paired-intrinsic/ExpandedTypes.lean"])
        data = json.loads(path.read_text())
        nodes = {row["name"] for row in data["project_dependency_graph"]}
        prefix = "RectangleCLT.Companion.SplitV4."
        forbidden = [prefix + name for name in ["largeIncrement_smooth_expectation_comparison_conditional",
            "largeIncrement_smooth_expectation_comparison", "largeIncrementGaussianComparison_bandwidth",
            "largeIncrementGaussianComparison", "gaussianComparisonWithLargeIncrementRemainders",
            "gaussianEndpointSmoothing", "bennett_polynomial_small_regime", "bennett_polynomial_large_regime",
            "bennettPolynomialCLT", "bennettPolynomialCLT_observations", "polynomialMomentCLTExists"]]
        found = sorted(nodes.intersection(forbidden))
        check = {"endpoints": len(data["endpoints"]), "project_dependency_nodes": len(nodes),
                 "forbidden_dimension_only_analytic_comparisons": forbidden, "found": found, "passed": not found}
        (out / "dependency-check.json").write_text(json.dumps(check, indent=2) + "\n")
        assert len(data["endpoints"]) == 31, "Unexpected endpoint inventory"
        assert not found, found
        report["final_source_identity"] = identity()
        assert initial == report["final_source_identity"], "Proof sources changed during execution"
        report.update(status="passed", finished_at=now())
    except Exception as error:
        report.update(status="failed", error=str(error), finished_at=now())
        save()
        raise
    save()
    print("Intrinsic paired/Bennett checkpoint PASS:", receipt, flush=True)


if __name__ == "__main__":
    main()
