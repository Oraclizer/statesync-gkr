#!/usr/bin/env python3
"""Build the deterministic StateSync-GKR source archive from a final manifest."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import stat
import tarfile


def strict_json(path: Path) -> dict:
    def pairs(items: list[tuple[str, object]]) -> dict:
        out: dict[str, object] = {}
        for key, value in items:
            if key in out:
                raise ValueError(f"duplicate JSON key in {path}: {key}")
            out[key] = value
        return out

    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs)
    if not isinstance(value, dict):
        raise ValueError("source manifest must be a JSON object")
    return value


def safe_member(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if path.is_absolute() or not path.parts or any(part in ("", ".", "..") for part in path.parts):
        raise ValueError(f"unsafe archive path: {name!r}")
    if "\\" in name:
        raise ValueError(f"non-POSIX archive path: {name!r}")
    return path


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--mtime", type=int, default=0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve(strict=True)
    manifest_path = args.manifest.resolve(strict=True)
    output = args.output.resolve()
    if output == manifest_path or root not in manifest_path.parents:
        raise ValueError("manifest must be inside root and output must be separate")

    manifest = strict_json(manifest_path)
    entries = manifest.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("SOURCE_MANIFEST.json requires a non-empty entries array")

    normalized: list[tuple[str, Path, int]] = []
    seen: set[str] = set()
    for item in entries:
        if not isinstance(item, dict):
            raise ValueError("manifest entry must be an object")
        name = str(item.get("path", ""))
        safe_member(name)
        if name in seen:
            raise ValueError(f"duplicate manifest path: {name}")
        seen.add(name)
        path = (root / Path(*PurePosixPath(name).parts)).resolve(strict=True)
        if root not in path.parents or path.is_symlink() or not path.is_file():
            raise ValueError(f"member is not a regular in-root file: {name}")
        expected_size = int(item.get("bytes", -1))
        expected_hash = str(item.get("sha256", ""))
        if path.stat().st_size != expected_size or digest(path) != expected_hash:
            raise ValueError(f"manifest mismatch: {name}")
        mode_text = str(item.get("mode", ""))
        if mode_text not in ("100644", "100755"):
            raise ValueError(f"unsupported mode for {name}: {mode_text}")
        normalized.append((name, path, 0o755 if mode_text == "100755" else 0o644))

    relative_manifest = manifest_path.relative_to(root).as_posix()
    if relative_manifest in seen:
        raise ValueError("SOURCE_MANIFEST.json must self-exclude")
    normalized.append((relative_manifest, manifest_path, 0o644))
    normalized.sort(key=lambda item: item[0].encode("utf-8"))

    output.parent.mkdir(parents=True, exist_ok=True)
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w", format=tarfile.USTAR_FORMAT) as archive:
        for name, path, mode in normalized:
            info = tarfile.TarInfo(name=name)
            info.size = path.stat().st_size
            info.mode = mode
            info.uid = 0
            info.gid = 0
            info.uname = ""
            info.gname = ""
            info.mtime = args.mtime
            info.type = tarfile.REGTYPE
            with path.open("rb") as stream:
                archive.addfile(info, stream)

    with output.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=args.mtime, compresslevel=9) as zipped:
            zipped.write(buffer.getvalue())

    print(f"archive={output}")
    print(f"bytes={output.stat().st_size}")
    print(f"sha256={digest(output)}")
    print(f"members={len(normalized)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
