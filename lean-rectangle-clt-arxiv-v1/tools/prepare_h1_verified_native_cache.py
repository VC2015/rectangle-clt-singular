#!/usr/bin/env python3
"""Reuse only previously checked, unchanged native modules in a new H.1 checkout.

Run prepare_verified_cache.py first for the locked external dependencies.
This operation copies caches, not proof evidence. The subsequent checkpoint
builds and directly elaborates every new or changed native source.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

PROJECT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--from-clean-checkout", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    source = args.from_clean_checkout.resolve() / PROJECT.name
    output = args.output.resolve()
    if output.exists():
        raise SystemExit("Refusing to overwrite cache receipt")
    baseline_path = PROJECT / "evidence/final-clean-checkpoint/run.json"
    assert sha(baseline_path) == "3500c2efdb929397434a7e2201f0b203b51b14bd362d53e78666be40afb62ba5"
    baseline = json.loads(baseline_path.read_text())
    assert baseline["source_commit"] == "443fbc667ed3c3ee47369e028c2c4280a5eed604"
    assert baseline["status"] == "passed"
    assert not baseline["initial_git_status"]
    assert all(row["exit_code"] == 0 for row in baseline["commands"])
    assert git(source, "rev-parse", "HEAD") == baseline["source_commit"]
    assert not git(source, "status", "--porcelain")
    bound = baseline["final_source_identity"]["files"]
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        assert sha(PROJECT / name) == sha(source / name) == bound[name]
    copied, reused, changed = [], [], []
    for name, digest in sorted(bound.items()):
        if not name.startswith("RectangleCLTArxivV1/") or not name.endswith(".lean"):
            continue
        original, destination = source / name, PROJECT / name
        assert sha(original) == digest
        if not destination.is_file() or sha(destination) != digest:
            changed.append(name)
            continue
        module = Path(name).with_suffix("")
        assert str(module) != "RectangleCLTArxivV1"  # Root has no slash and was excluded above.
        old_build, new_build = source / ".lake/build", PROJECT / ".lake/build"
        olean = old_build / "lib/lean" / module.with_suffix(".olean")
        assert olean.is_file() and Path(str(olean) + ".hash").is_file(), name
        reused.append({"source": name, "sha256": digest})
        candidates = [old_build / "lib/lean" / Path(str(module) + suffix)
                      for suffix in (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")]
        candidates += [old_build / "ir" / Path(str(module) + suffix)
                       for suffix in (".c", ".c.hash")]
        for artifact in candidates:
            if not artifact.is_file():
                continue
            target = new_build / artifact.relative_to(old_build)
            if target.exists():
                raise SystemExit("Refusing existing native artifact: " + str(target))
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(artifact, target)
            copied.append({"path": str(target.relative_to(PROJECT)), "sha256": sha(target),
                           "source": name, "source_sha256": digest})
    # Old modules cannot silently acquire dependencies on new files: all their
    # complete source texts agree with the sealed baseline. Root is not copied.
    receipt = {"scope": "UNCHANGED_NATIVE_CACHE_PREPARATION_ONLY", "proof_check": False,
               "prepared_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "baseline_commit": baseline["source_commit"],
               "baseline_receipt_sha256": sha(PROJECT / "evidence/final-clean-checkpoint/run.json"),
               "source_checkout": str(source.parent), "destination_checkout": str(PROJECT.parent),
               "source_identical_native_modules": reused, "changed_baseline_sources_not_copied": changed,
               "new_native_artifacts_copied": False, "root_artifact_copied": False,
               "artifacts": copied}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"unchanged_native_modules": len(reused), "artifacts": len(copied)}))


if __name__ == "__main__":
    main()
