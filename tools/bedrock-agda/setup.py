#!/usr/bin/env python3
"""Install Bedrock's pinned Agda library dependencies into a local home."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tarfile
import urllib.request


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def safe_extract(archive: Path, destination: Path) -> None:
    destination = destination.resolve()
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar.getmembers():
            target = (destination / member.name).resolve()
            if destination not in target.parents and target != destination:
                raise RuntimeError(f"unsafe archive member: {member.name}")
        tar.extractall(destination)


def require_python(minimum: str) -> None:
    required = tuple(int(part) for part in minimum.split("."))
    if sys.version_info[: len(required)] < required:
        raise RuntimeError(
            f"Python {minimum}+ is required; found {sys.version.split()[0]}"
        )


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    environment = json.loads(
        (root / "tools/bedrock-agda/environment.json").read_text(encoding="utf-8")
    )
    require_python(environment["minimum_python_version"])

    version = environment["cubical_version"]
    expected = environment["cubical_sha256"]
    dependencies = root / "_build/dependencies"
    downloads = dependencies / "downloads"
    archive = downloads / f"cubical-{version}.tar.gz"
    cubical = dependencies / f"cubical-{version}"
    marker = cubical / ".bedrock-source-sha256"

    downloads.mkdir(parents=True, exist_ok=True)
    if not archive.exists() or sha256(archive) != expected:
        archive.unlink(missing_ok=True)
        print(f"downloading cubical {version}", file=sys.stderr)
        urllib.request.urlretrieve(environment["cubical_url"], archive)
    actual = sha256(archive)
    if actual != expected:
        raise RuntimeError(
            f"cubical checksum mismatch: expected {expected}, got {actual}"
        )

    if not marker.exists() or marker.read_text(encoding="utf-8").strip() != expected:
        temporary = dependencies / f".cubical-{version}.tmp"
        shutil.rmtree(temporary, ignore_errors=True)
        temporary.mkdir(parents=True)
        safe_extract(archive, temporary)
        extracted = temporary / f"cubical-{version}"
        if not (extracted / "cubical.agda-lib").is_file():
            raise RuntimeError("cubical archive has an unexpected layout")
        shutil.rmtree(cubical, ignore_errors=True)
        extracted.replace(cubical)
        shutil.rmtree(temporary)
        marker.write_text(expected + "\n", encoding="utf-8")

    agda_dir = Path(
        os.environ.get("AGDA_DIR", root / "_build/agda-home")
    ).expanduser().resolve()
    agda_dir.mkdir(parents=True, exist_ok=True)
    libraries = agda_dir / "libraries"
    library = str((cubical / "cubical.agda-lib").resolve())
    lines = libraries.read_text(encoding="utf-8").splitlines() if libraries.exists() else []
    if library not in lines:
        lines.append(library)
        libraries.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"cubical {version}: {cubical}")
    print(f"Agda libraries: {libraries}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
