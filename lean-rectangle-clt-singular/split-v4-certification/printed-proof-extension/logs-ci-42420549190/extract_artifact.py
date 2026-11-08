#!/usr/bin/env python3
"""Preserve raw ZIP bytes and extract only regular, safe artifact paths."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import stat
import zipfile

parser = argparse.ArgumentParser()
parser.add_argument("archive", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--manifest", type=Path, required=True)
args = parser.parse_args()
if args.output.is_symlink() or (args.output.exists() and not args.output.is_dir()):
    raise ValueError("Extraction output must be a real directory")
if args.output.exists() and any(args.output.iterdir()):
    raise ValueError("Refusing to overwrite extracted evidence")
args.output.mkdir(parents=True, exist_ok=True)
manifest = {"archive": args.archive.name, "archive_sha256": hashlib.sha256(args.archive.read_bytes()).hexdigest(),
            "archive_bytes": args.archive.stat().st_size, "files": []}
with zipfile.ZipFile(args.archive) as archive:
    names = set()
    for item in archive.infolist():
        path = PurePosixPath(item.filename)
        if path.is_absolute() or ".." in path.parts or "\\" in item.filename or ":" in item.filename or item.filename in names:
            raise ValueError("Unsafe or duplicate artifact path: " + item.filename)
        names.add(item.filename)
        mode = item.external_attr >> 16
        if stat.S_ISLNK(mode) or (stat.S_IFMT(mode) not in (0, stat.S_IFREG, stat.S_IFDIR)):
            raise ValueError("Artifact contains nonregular file: " + item.filename)
    required = sum(item.file_size for item in archive.infolist())
    if required + 512 * 1024 * 1024 > shutil.disk_usage(args.output).free:
        raise ValueError("Insufficient disk space for preserved artifact")
    for item in archive.infolist():
        target = args.output.joinpath(*PurePosixPath(item.filename).parts)
        if item.is_dir():
            target.mkdir(parents=True, exist_ok=True)
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        with archive.open(item) as source, target.open("xb") as destination:
            shutil.copyfileobj(source, destination)
        data = target.read_bytes()
        manifest["files"].append({"path": item.filename, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(), "zip_crc32": item.CRC})
args.manifest.write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"archive_sha256": manifest["archive_sha256"], "files": len(manifest["files"]), "expanded_bytes": required}))
