#!/usr/bin/env python3
"""Render the reader-facing Markdown report with Pandoc and XeLaTeX."""
from datetime import datetime, timezone
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parent
cache = Path(tempfile.gettempdir()) / "split-v4-report-cache"
cache.mkdir(exist_ok=True)
env = dict(os.environ)
env["XDG_CACHE_HOME"] = str(cache)
env["SOURCE_DATE_EPOCH"] = str(int(datetime(2026, 11, 7, tzinfo=timezone.utc).timestamp()))
subprocess.run([
    "pandoc", str(root / "REPORT.md"), "--standalone", "--pdf-engine=xelatex",
    "--metadata", "title=Split-V4 Lean certification — 7 November 2026",
    "--metadata", "date=", "--variable", "documentclass=article",
    "--variable", "papersize=a4", "--variable", "geometry:margin=20mm",
    "--variable", "fontsize=11pt", "--variable", "mainfont=DejaVu Serif",
    "--variable", "monofont=DejaVu Sans Mono", "--variable", "monofontoptions=Scale=0.86",
    "--variable", "linestretch=1.05",
    "--lua-filter", str(root / "report-pdf.lua"),
    "--include-in-header", str(root / "report-pdf-header.tex"),
    "--output", str(root / "REPORT.pdf"),
], env=env, check=True)
print(f"Rendered {root / 'REPORT.pdf'}")
