#!/usr/bin/env python3
"""Combine the nested route audits for fresh execution by the checkpoint runner."""
from pathlib import Path
import hashlib

PACKAGE = Path(__file__).resolve().parents[2]
SPLIT = PACKAGE / "RectangleCLTCompanion" / "SplitV4"
audits = sorted((SPLIT / "Printed").glob("*Audit.lean"))
imports = {"import RectangleCLTCompanion.SplitV4.PrintedProofs"}
blocks = []
for source in audits:
    text = source.read_text()
    imports.update(line for line in text.splitlines() if line.startswith("import "))
    body = "\n".join(line for line in text.splitlines() if not line.startswith("import "))
    path = source.relative_to(PACKAGE).as_posix()
    sha = hashlib.sha256(source.read_bytes()).hexdigest()
    blocks.append(f"\n-- Source SHA-256: {sha}\n-- BEGIN PRINTED_ROUTE {path}\n"
                  + body + f"\n-- END PRINTED_ROUTE {path}\n")
header = "\n".join(sorted(imports)) + "\n\n" + """/-! Fresh strict execution of every nested printed-route audit.
The bodies are verbatim apart from import consolidation. Regenerate with
split-v4-certification/printed-proof-extension/generate_route_audit.py after
changing a nested audit. The existing checkpoint runner executes this file
directly, rerunning every route and transitive-axiom assertion. -/
"""
(SPLIT / "PrintedRouteAudit.lean").write_text(header + "".join(blocks))
print(f"Generated PrintedRouteAudit.lean from {len(audits)} nested audits")
