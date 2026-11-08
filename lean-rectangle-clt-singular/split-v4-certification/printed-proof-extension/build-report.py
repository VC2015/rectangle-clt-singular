#!/usr/bin/env python3
"""Render the printed-proof report with Pandoc and XeLaTeX.

This renderer writes REPORT.pdf and the documentation-artifact inventory
REPORT_ARTIFACTS.json beside this script. The inventory is not a proof-execution
certificate. The separate result-certificate report and its rendering assets
are preserved unchanged.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


root = Path(__file__).resolve().parent
title = "Split-V4 printed-proof Lean certification — 7 November 2026"
input_names = [
    "REPORT.md", "build-report.py", "report-pdf.lua", "report-pdf-header.tex",
    "REPORT_STATEMENT_MAP.json",
]
preserved_hashes = {
    "../REPORT.md": "a31a882b8e74d2bd115c0bc18c671c3d1ab9acfc0282989d7abf52424ff08df7",
    "../REPORT.pdf": "57c83f56c21ef6cf5d1221a61381c73b712f9552d4ed1efeb7206c314bd7ffc2",
}


def inventory(path):
    data = path.read_bytes()
    return {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def version_first_line(command):
    result = subprocess.run(
        command, check=True, text=True, capture_output=True, env=env,
    )
    return result.stdout.splitlines()[0]


before = {name: inventory(root / name) for name in input_names}
preserved_before = {name: inventory(root / name) for name in preserved_hashes}
for name, expected in preserved_hashes.items():
    if preserved_before[name]["sha256"] != expected:
        raise RuntimeError(f"Preserved result-certificate report changed: {name}")

cache = Path(tempfile.gettempdir()) / "split-v4-printed-report-cache"
cache.mkdir(exist_ok=True)
env = dict(os.environ)
env["XDG_CACHE_HOME"] = str(cache)
env["SOURCE_DATE_EPOCH"] = str(
    int(datetime(2026, 11, 7, tzinfo=timezone.utc).timestamp())
)
subprocess.run([
    "pandoc", str(root / "REPORT.md"), "--standalone", "--pdf-engine=xelatex",
    "--metadata", f"title={title}",
    "--metadata", "date=", "--variable", "documentclass=article",
    "--variable", "papersize=a4", "--variable", "geometry:margin=20mm",
    "--variable", "fontsize=11pt", "--variable", "mainfont=DejaVu Serif",
    "--variable", "monofont=DejaVu Sans Mono", "--variable", "monofontoptions=Scale=0.86",
    "--variable", "linestretch=1.05",
    "--lua-filter", str(root / "report-pdf.lua"),
    "--include-in-header", str(root / "report-pdf-header.tex"),
    "--output", str(root / "REPORT.pdf"),
], env=env, check=True)

after = {name: inventory(root / name) for name in input_names}
preserved_after = {name: inventory(root / name) for name in preserved_hashes}
if after != before or preserved_after != preserved_before:
    raise RuntimeError("A report input or preserved report changed during rendering; rerun.")

manifest = {
    "schema_version": 1,
    "kind": "documentation_artifact_inventory",
    "scope": (
        "Inventories the reader-facing report and rendering inputs. This is not "
        "a Lean proof-execution certificate; proof and execution-evidence commits "
        "identify the existing verification. Git history identifies the report's "
        "publication commit."
    ),
    "report_title": title,
    "report_client_date": "2026-11-07",
    "report_client_timezone": "America/New_York",
    "generated_at_utc": datetime.now(timezone.utc).isoformat(),
    "proof_commit": "92896b8a2a4099357486587d17ca1921a3dba161",
    "execution_evidence_commit": "0ef13b938895535fe2dcc135b9400688ed97fa61",
    "artifacts": {
        **after,
        "REPORT.pdf": inventory(root / "REPORT.pdf"),
    },
    "rendering_environment": {
        "python": version_first_line([sys.executable, "--version"]),
        "pandoc": version_first_line(["pandoc", "--version"]),
        "xelatex": version_first_line(["xelatex", "--version"]),
        "SOURCE_DATE_EPOCH": int(env["SOURCE_DATE_EPOCH"]),
    },
    "preserved_result_report": {
        "snapshot_tag": "split-v4-lean-certified-2026-11-07",
        "snapshot_commit": "e692196356de50c00fcdd66ddad0f3706db0241c",
        "checked_read_only": True,
        "unchanged_during_rendering": True,
        "matches_preserved_hashes": True,
        "artifacts": preserved_after,
    },
}
(root / "REPORT_ARTIFACTS.json").write_text(
    json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
)
print(f"Rendered {root / 'REPORT.pdf'}")
print(f"Wrote documentation inventory {root / 'REPORT_ARTIFACTS.json'}")
