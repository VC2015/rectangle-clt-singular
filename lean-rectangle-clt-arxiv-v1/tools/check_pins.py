#!/usr/bin/env python3
"""Check source identity and resolved dependency revisions; this is not a proof check."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
REPO = PROJECT.parent


def git(*args, cwd=REPO):
    return subprocess.check_output(["git", *args], cwd=cwd, text=False)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dependencies", action="store_true")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    pins = json.loads((PROJECT / "source-pins.json").read_text())
    inventory = json.loads((PROJECT / "inventory.json").read_text())
    checks = []
    for key, source in inventory["source_files"].items():
        path = source["path"]
        frozen = git("show", f'{pins["paper_commit"]}:{path}')
        current = (REPO / path).read_bytes()
        checks.append({"kind": "source", "source": key, "path": path,
                       "expected_sha256": source["sha256"],
                       "git_object_sha256": sha(frozen), "working_tree_sha256": sha(current),
                       "passed": sha(frozen) == source["sha256"] == sha(current)})
    archived = ["lean-kane", "lean-rectangle-clt-local", "lean-rectangle-clt-singular",
                "LEAN_VERIFICATION.md", "provenance"]
    base = pins["assignment_commit"]
    changed = git("diff", "--name-only", base, "--", *archived).decode().splitlines()
    checks.append({"kind": "archive-preservation", "base": base,
                   "changed_tracked_paths": changed, "passed": not changed})
    if args.dependencies:
        manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            if package["type"] != "git":
                continue
            path = PROJECT / ".lake" / "packages" / package["name"]
            try:
                actual = git("rev-parse", "HEAD", cwd=path).decode().strip()
                dirty = git("status", "--porcelain", "--untracked-files=no", cwd=path).decode().splitlines()
            except (OSError, subprocess.CalledProcessError):
                actual, dirty = None, []
            checks.append({"kind": "dependency", "name": package["name"],
                           "url": package["url"], "expected_revision": package["rev"],
                           "actual_revision": actual, "tracked_changes": dirty,
                           "passed": actual == package["rev"] and not dirty})
    report = {"scope": "SOURCE_AND_DEPENDENCY_IDENTITY_ONLY", "proof_certification": False,
              "passed": all(check["passed"] for check in checks), "checks": checks}
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
