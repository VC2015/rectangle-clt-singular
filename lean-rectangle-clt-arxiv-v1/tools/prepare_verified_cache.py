#!/usr/bin/env python3
"""Prepare ignored dependency caches for a separate C.2 checkout.

Git dependencies must be clean at their locked revisions. Archive artifacts
are copied only alongside byte-identical Lean sources. New C.2 artifacts
are deliberately not copied. This is cache preparation, not a proof check.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

PROJECT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path, *args):
    return subprocess.check_output(["git", *args], cwd=path, text=True).strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--from-checkout", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    source = args.from_checkout.resolve()
    destination = PROJECT.parent
    output = args.output.resolve()
    if output.exists():
        raise SystemExit("Refusing to overwrite a cache preparation receipt")
    packages = source / PROJECT.name / ".lake/packages"
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    identities = []
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        path = packages / package["name"]
        actual = git(path, "rev-parse", "HEAD")
        dirty = git(path, "status", "--porcelain", "--untracked-files=no")
        if actual != package["rev"] or dirty:
            raise SystemExit("Unverified Git dependency: " + package["name"])
        identities.append({"name": package["name"], "revision": actual,
                           "resolved_path": str(path.resolve()), "tracked_changes": dirty})
    projects = ("lean-kane", "lean-rectangle-clt-local", "lean-rectangle-clt-singular")
    for package in (*projects, PROJECT.name):
        lake = destination / package / ".lake"
        lake.mkdir(exist_ok=True)
        link = lake / "packages"
        if link.exists() or link.is_symlink():
            raise SystemExit("Refusing an existing packages path: " + str(link))
        link.symlink_to(packages, target_is_directory=True)
    artifacts = []
    module_count = 0
    for package in projects:
        build = source / package / ".lake/build"
        for trace in sorted((build / "lib/lean").rglob("*.trace")):
            module = trace.relative_to(build / "lib/lean").with_suffix("")
            lean_source = Path(package) / module.with_suffix(".lean")
            if not (source / lean_source).is_file() or not (destination / lean_source).is_file():
                continue
            if (source / lean_source).read_bytes() != (destination / lean_source).read_bytes():
                raise SystemExit("Source mismatch: " + str(lean_source))
            olean = build / "lib/lean" / module.with_suffix(".olean")
            if not olean.is_file() or not Path(str(olean) + ".hash").is_file():
                continue
            module_count += 1
            candidates = [build / "lib/lean" / Path(str(module) + suffix)
                          for suffix in (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")]
            candidates += [build / "ir" / Path(str(module) + suffix)
                           for suffix in (".c", ".c.hash")]
            for artifact in candidates:
                if not artifact.is_file():
                    continue
                relative = artifact.relative_to(source)
                target = destination / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                temporary = target.with_name(target.name + ".verified-copy.tmp")
                shutil.copy2(artifact, temporary)
                os.replace(temporary, target)
                artifacts.append({"path": str(relative), "sha256": sha(target),
                                  "source_path": str(lean_source), "source_sha256": sha(source / lean_source)})
    report = {"scope": "DEPENDENCY_CACHE_PREPARATION_ONLY", "proof_check": False,
              "prepared_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "source_checkout": str(source), "destination_checkout": str(destination),
              "git_dependencies": identities, "source_identical_modules": module_count,
              "new_c2_build_artifacts_copied": False, "artifacts": artifacts}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"source_identical_modules": module_count, "artifacts": len(artifacts)}))


if __name__ == "__main__":
    main()
