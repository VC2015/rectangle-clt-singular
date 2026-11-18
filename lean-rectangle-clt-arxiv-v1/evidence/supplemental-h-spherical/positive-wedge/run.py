#!/usr/bin/env python3
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess

root = Path(__file__).resolve().parents[3]
out = root / "evidence/supplemental-h-spherical/positive-wedge"
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p): return hashlib.sha256((root / p).read_bytes()).hexdigest()
def save(p, x): p.write_text(json.dumps(x, indent=2) + "\n")
owned = "RectangleCLTArxivV1/SupplementalHPositiveWedge.lean"
seen = set()
def visit(path):
    if path in seen: return
    seen.add(path)
    for mod in re.findall(r"^import\s+(RectangleCLTArxivV1\.[\w.]+)", (root / path).read_text(), re.M):
        visit(mod.replace(".", "/") + ".lean")
visit(owned)
files = sorted(seen) + ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "source-pins.json"]
files += ["evidence/supplemental-h-spherical/positive-wedge/" + n
          for n in ["Audit.lean", "run.py", "targets.json"]]
freeze = {f: sha(f) for f in files}
save(out / "source-freeze.json", {"created_at": now(), "sha256": freeze})
receipt = {"started_at": now(), "scope": "actual positive planar wedge angular area",
    "source_sha256": freeze,
    "checked_target_count": json.loads((out / "targets.json").read_text())["target_count"],
    "commands": []}
save(out / "receipt.json", receipt)
commands = [
    ("build", ["lake", "build", "RectangleCLTArxivV1.SupplementalHPositiveWedge"]),
    ("force", ["lake", "env", "lean", owned]),
    ("audit", ["lake", "env", "lean", "evidence/supplemental-h-spherical/positive-wedge/Audit.lean"])]
env = dict(os.environ)
env["PATH"] = "/workspace/lean-toolchain-bin/bin:" + env["PATH"]
for label, argv in commands:
    log = out / (label + ".log")
    row = {"label": label, "argv": argv, "cwd": str(root), "started_at": now(),
           "log": str(log.relative_to(root))}
    with log.open("w") as stream:
        result = subprocess.run(argv, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
    row.update(finished_at=now(), exit_code=result.returncode, log_sha256=sha(log.relative_to(root)))
    receipt["commands"].append(row)
    save(out / "receipt.json", receipt)
    print(label + ": " + str(result.returncode), flush=True)
    if result.returncode: break
receipt["finished_at"] = now()
receipt["source_unchanged"] = all(sha(f) == h for f, h in freeze.items())
receipt["passed"] = (len(receipt["commands"]) == len(commands)
    and all(r["exit_code"] == 0 for r in receipt["commands"]) and receipt["source_unchanged"])
save(out / "receipt.json", receipt)
print("PASS" if receipt["passed"] else "FAIL", flush=True)
