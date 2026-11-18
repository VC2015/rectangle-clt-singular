#!/usr/bin/env python3
"""Validate B.3 source bindings and recorded checks; does not invoke Lean."""

import hashlib
import json
import subprocess
from pathlib import Path


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    project = Path(__file__).resolve().parent.parent
    repo = project.parent
    ledger = json.loads((project / "correspondence/b3-passages.json").read_text())
    pins = json.loads((project / "source-pins.json").read_text())
    assert ledger["snapshot"] == pins["paper_commit"]
    proof = ledger["proof_source"]
    assert digest((project / proof["path"]).read_bytes()) == proof["sha256"]
    assert [p["id"] for p in ledger["passages"]] == ["B3.1", "B3.2", "B3.3", "B3.4"]
    previous = 4977
    source_cache = {}
    export_cache = {}
    receipts = set()
    for passage in ledger["passages"]:
        assert passage["status"] in {"reviewed_compiled_pending_clean_export", "checked_printed_proof"}
        assert passage["statement_id"] == "S-appx-an-lem-mean"
        location = passage["location"]
        path = location["path"]
        if path not in source_cache:
            raw = subprocess.check_output(
                ["git", "show", pins["paper_commit"] + ":" + path], cwd=repo
            )
            assert digest(raw) == pins["sources"]["main"]["sha256"]
            source_cache[path] = raw.splitlines(keepends=True)
        lo, hi = location["lines"]
        assert lo == previous + 1
        assert digest(b"".join(source_cache[path][lo - 1 : hi])) == location["sha256"]
        previous = hi
        assert passage["archive_correspondence"]["id"].startswith("matrix:b3-")
        for entry in passage["expanded_types"]:
            export = entry["export"]
            if export not in export_cache:
                metadata = json.loads((project / export).read_text())
                export_cache[export] = {x["name"]: x for x in metadata["endpoints"]}
            actual = export_cache[export][entry["declaration"]]
            assert entry["expanded_type"] == actual["expanded_type"]
        for binding in passage["dependency_bindings"]:
            actual = export_cache[binding["transitive_project_graph"]][binding["declaration"]]
            assert binding["direct_dependencies"] == actual["direct_dependencies"]
        for receipt in passage["verification_receipts"]:
            assert digest((project / receipt["path"]).read_bytes()) == receipt["sha256"]
            receipts.add(receipt["path"])
    assert previous == 5046
    review = json.loads(
        (project / "evidence/intrinsic-smoothing/b3-printed/independent-review.json").read_text()
    )
    assert review["status"] == "PASS_SAME_PRINTED_ARGUMENT"
    assert review["source_sha256"] == proof["sha256"]
    validation = json.loads(
        (project / "evidence/intrinsic-smoothing/b3-printed/audit-validation.json").read_text()
    )
    assert validation["status"] == "PASS"
    assert set(validation["observed_axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    print(json.dumps({
        "status": "PASS",
        "scope": "SOURCE_BINDINGS_AND_RECORDED_EVIDENCE_ONLY",
        "passages": 4,
        "frozen_lines": [4978, 5046],
        "distinct_receipts": len(receipts),
        "statement_acceptance": ("clean_export_recorded" if all(
            p["status"] == "checked_printed_proof" for p in ledger["passages"])
            else "pending_root_clean_export"),
    }, indent=2))


if __name__ == "__main__":
    main()
