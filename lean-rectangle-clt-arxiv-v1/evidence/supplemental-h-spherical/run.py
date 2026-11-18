#!/usr/bin/env python3
"""Hash-bound local build and strict axiom audit of spherical balance."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "evidence/supplemental-h-spherical"
def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2) + "\n")

owned = [f"RectangleCLTArxivV1/SupplementalHSpherical{x}.lean"
         for x in ["Polar", "Sectors", "Balance"]]
deps = [f"RectangleCLTArxivV1/SupplementalH{x}.lean"
        for x in ["ThresholdRegularity", "SurfaceMeasure", "GaussianBoundary"]]
files = owned + deps + ["lake-manifest.json", "lakefile.toml", "lean-toolchain",
    "evidence/supplemental-h-spherical/Audit.lean",
    "evidence/supplemental-h-spherical/run.py",
    "evidence/supplemental-h-spherical/targets.json"]
freeze = {f: digest(ROOT / f) for f in files}
write_json(OUT / "source-freeze.json", {"created_at": now(), "sha256": freeze})
receipt = {"started_at": now(), "scope": "actual polyhedral-cone spherical balance",
    "paper_certified": False, "source_sha256": freeze, "commands": []}
write_json(OUT / "receipt.json", receipt)
commands = [("build", ["lake", "build"] +
    [f"RectangleCLTArxivV1.SupplementalHSpherical{x}" for x in ["Polar", "Sectors", "Balance"]])]
commands += [("force-" + Path(f).stem, ["lake", "env", "lean", f]) for f in owned]
commands += [("audit", ["lake", "env", "lean", "evidence/supplemental-h-spherical/Audit.lean"])]
env = dict(os.environ)
env["PATH"] = "/workspace/lean-toolchain-bin/bin:" + env["PATH"]
for label, argv in commands:
    log = OUT / (label + ".log")
    row = {"label": label, "argv": argv, "cwd": str(ROOT), "started_at": now(),
           "log": str(log.relative_to(ROOT))}
    with log.open("w") as stream:
        result = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    row.update(finished_at=now(), exit_code=result.returncode, log_sha256=digest(log))
    receipt["commands"].append(row)
    write_json(OUT / "receipt.json", receipt)
    print(label + ": " + str(result.returncode), flush=True)
    if result.returncode:
        break
receipt["finished_at"] = now()
receipt["source_unchanged"] = all(digest(ROOT / f) == h for f, h in freeze.items())
receipt["checked_target_count"] = json.loads((OUT / "targets.json").read_text())["target_count"]
receipt["passed"] = (len(receipt["commands"]) == len(commands)
    and all(r["exit_code"] == 0 for r in receipt["commands"])
    and receipt["source_unchanged"])
write_json(OUT / "receipt.json", receipt)
print("PASS" if receipt["passed"] else "FAIL", flush=True)
