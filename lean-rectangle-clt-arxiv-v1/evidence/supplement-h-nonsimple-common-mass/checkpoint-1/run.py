"""Check the common actual-face mass and finite Green-sum support packet."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
MODULES = ["SupplementalHNonsimpleFaceMass", "SupplementalHNonsimpleFaceFrame",
           "SupplementalHNonsimpleActualMass", "SupplementalHNonsimpleGreenSum"]
FILES = [Path("RectangleCLTArxivV1") / (name + ".lean") for name in MODULES]
TARGETS = ["RectangleCLTArxivV1." + name for path in FILES
           for name in re.findall(r"^(?:theorem|def)\s+([A-Za-z0-9_]+)",
                                  (ROOT / path).read_text(), re.M)]
assert len(TARGETS) == len(set(TARGETS)) == 29

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")

imports = "".join("import RectangleCLTArxivV1." + name + "\n" for name in MODULES)
targets = "#[" + ",".join("``" + name for name in TARGETS) + "]"
audit = imports + '''import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let targets := TARGETS
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows),
    ("all_axioms_allowed", toJson true)]).compress
'''.replace("TARGETS", targets)
(OUT / "Audit.lean").write_text(audit)
mapper = ROOT / "tools/prepare_full_clean_mapping.py"
renderer = runpy.run_path(str(mapper))["render"]
(OUT / "Types.lean").write_text(renderer(["RectangleCLTArxivV1." + m for m in MODULES], TARGETS))
bound = FILES + [Path("RectangleCLTArxivV1/SupplementalHNonsimpleFaceGeometry.lean"),
                 Path("lakefile.toml"), Path("lake-manifest.json"), Path("lean-toolchain"),
                 mapper.relative_to(ROOT)] + [p.relative_to(ROOT) for p in
                 [Path(__file__).resolve(), OUT / "Audit.lean", OUT / "Types.lean"]]
identity = {str(p): sha(ROOT / p) for p in bound}
report = {"status": "running", "scope": "Supporting actual-face Gaussian masses, canonical normal frames, and finite signed incidence grouping. This packet does not assert the pending final nonsimple Green identity.",
          "release_wide_certification": False, "started_at_utc": now(),
          "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
          "initial_checkout_clean": not subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip(),
          "source_identity": identity, "targets": TARGETS, "commands": []}
env = dict(os.environ, PATH="/workspace/lean-toolchain-bin/bin:" + os.environ["PATH"])

def command(label, argv):
    log = OUT / (label + ".log")
    row = {"label": label, "argv": argv, "cwd": str(ROOT), "started_at_utc": now(),
           "log": str(log.relative_to(ROOT))}
    report["commands"].append(row)
    save(OUT / "run.json", report)
    with log.open("wb") as stream:
        result = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    row.update(exit_code=result.returncode, finished_at_utc=now(), log_sha256=sha(log))
    save(OUT / "run.json", report)
    assert result.returncode == 0, label
    return log

try:
    command("01-build", ["lake", "build"] + ["RectangleCLTArxivV1." + m for m in MODULES])
    for i, name in enumerate(MODULES, 2):
        command(f"{i:02}-force-" + name, ["lake", "env", "lean", "RectangleCLTArxivV1/" + name + ".lean",
                "-o", ".lake/build/lib/lean/RectangleCLTArxivV1/" + name + ".olean"])
    a = json.loads(command("06-strict-audit", ["lake", "env", "lean", str((OUT / "Audit.lean").relative_to(ROOT))]).read_text())
    assert a["all_axioms_allowed"] and {x["name"] for x in a["targets"]} == set(TARGETS)
    t = json.loads(command("07-full-types", ["lake", "env", "lean", str((OUT / "Types.lean").relative_to(ROOT))]).read_text())
    assert {x["name"] for x in t["endpoints"]} == set(TARGETS)
    assert set(t["axiom_union"]) <= {"propext", "Classical.choice", "Quot.sound"}
    assert all(x["expanded_type"] for x in t["endpoints"])
    graph = {x["name"]: set(x["direct_project_dependencies"]) for x in t["project_dependency_graph"]}
    assert set(TARGETS) <= set(graph)
    assert all(ds <= set(graph) for ds in graph.values())
    assert identity == {str(p): sha(ROOT / p) for p in bound}, "Source identity changed"
    report.update(status="passed", public_declarations_audited=len(TARGETS), expanded_types=len(t["endpoints"]),
                  project_dependency_nodes=len(graph), axiom_union=t["axiom_union"],
                  finished_at_utc=now(), final_source_identity=identity)
except Exception as error:
    report.update(status="failed", failure=str(error), finished_at_utc=now())
    raise
finally:
    save(OUT / "run.json", report)
print(json.dumps({k: report[k] for k in ["status", "public_declarations_audited", "expanded_types", "project_dependency_nodes"]}))
