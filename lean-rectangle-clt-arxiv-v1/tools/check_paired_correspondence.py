#!/usr/bin/env python3
"""Check frozen spans, type bindings and receipts; no mathematical review."""
import hashlib
import json
from pathlib import Path
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
REPO = PROJECT.parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads((PROJECT / path).read_text())


def main():
    ledger = read("correspondence/paired-intrinsic-passages.json")
    inventory = read("inventory.json")
    assert ledger["snapshot"] == inventory["snapshot"]
    assert ledger["source_files"] == inventory["source_files"]
    raw = {}
    for key, source in ledger["source_files"].items():
        data = subprocess.check_output(["git", "show",
            ledger["snapshot"] + ":" + source["path"]], cwd=REPO)
        assert digest(data) == source["sha256"], key
        raw[key] = data.splitlines(keepends=True)

    def location(loc):
        a, b = loc["lines"]
        assert 1 <= a <= b <= len(raw[loc["source"]])
        assert digest(b"".join(raw[loc["source"]][a - 1:b])) == loc["sha256"]

    for loc in ledger["statement_locations"].values():
        location(loc)
    for row in ledger["passages"]:
        location(row["location"])
        assert len(row["lean_declarations"]) == len(row["expanded_types"])
        for bound in row["expanded_types"]:
            export = read(bound["export"])
            endpoint = next(x for x in export["endpoints"]
                            if x["name"] == bound["declaration"])
            assert bound["expanded_type"] == endpoint["expanded_type"]
        for bound in row["dependency_bindings"]:
            export = read(bound["transitive_project_graph"])
            endpoint = next(x for x in export["project_dependency_graph"]
                            if x["name"] == bound["declaration"])
            assert bound["direct_project_dependencies"] == endpoint["direct_project_dependencies"]
        for receipt in [row["build_receipt"], row["mapped_build_audit_receipt"]]:
            path = PROJECT / receipt["path"]
            assert digest(path.read_bytes()) == receipt["sha256"]
            assert read(receipt["path"])["status"] == receipt["status"] == "passed"
    print(json.dumps({"status": "PASS_SOURCE_TYPE_RECEIPT_IDENTITY_ONLY",
        "mathematical_correspondence_certification": False,
        "snapshot": ledger["snapshot"], "passages": len(ledger["passages"])}))


if __name__ == "__main__":
    main()
