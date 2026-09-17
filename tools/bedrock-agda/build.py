#!/usr/bin/env python3
"""Build Bedrock's pinned Agda with the external type-trace overlay."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import urllib.request


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tree_hash(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        digest.update(path.relative_to(root).as_posix().encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def run(command: list[str], *, cwd: Path | None = None) -> None:
    print("+", " ".join(command), file=sys.stderr)
    subprocess.run(command, cwd=cwd, check=True)


def macos_ghc_options() -> list[str]:
    """Use an older installed SDK when GHC 9.4 cannot parse a newer .tbd."""
    if platform.system() != "Darwin":
        return []
    sdk_root = Path("/Library/Developer/CommandLineTools/SDKs")
    for name in ("MacOSX14.4.sdk", "MacOSX14.sdk", "MacOSX13.3.sdk", "MacOSX13.sdk"):
        sdk = sdk_root / name
        if sdk.is_dir():
            return [
                f"--ghc-option=-L{sdk / 'usr/lib'}",
                f"--ghc-option=-optl-isysroot{sdk}",
            ]
    return []


def safe_extract(archive: Path, destination: Path) -> None:
    destination = destination.resolve()
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar.getmembers():
            target = (destination / member.name).resolve()
            if destination not in target.parents and target != destination:
                raise RuntimeError(f"unsafe archive member: {member.name}")
        tar.extractall(destination)


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    tool_root = root / "tools/bedrock-agda"
    manifest_path = tool_root / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    version = manifest["agda_version"]
    source_url = manifest["source_url"]
    source_sha256 = manifest["source_sha256"]
    adapter = tool_root / manifest["adapter"]
    overlay = tool_root / "src"

    build_root = root / "_build/bedrock-agda"
    downloads = build_root / "downloads"
    archive = downloads / f"Agda-{version}.tar.gz"
    source = build_root / "source" / f"Agda-{version}"
    marker = source / ".bedrock-overlay"
    overlay_hash = tree_hash(overlay)
    fingerprint = hashlib.sha256(
        manifest_path.read_bytes() + adapter.read_bytes() + overlay_hash.encode()
    ).hexdigest()
    expected_marker = f"{source_sha256}\n{fingerprint}\n"

    downloads.mkdir(parents=True, exist_ok=True)
    if not archive.exists() or sha256(archive) != source_sha256:
        archive.unlink(missing_ok=True)
        print(f"downloading {source_url}", file=sys.stderr)
        urllib.request.urlretrieve(source_url, archive)
    actual = sha256(archive)
    if actual != source_sha256:
        raise RuntimeError(
            f"Agda source checksum mismatch: expected {source_sha256}, got {actual}"
        )

    if not marker.exists() or marker.read_text(encoding="utf-8") != expected_marker:
        shutil.rmtree(source.parent, ignore_errors=True)
        source.parent.mkdir(parents=True, exist_ok=True)
        safe_extract(archive, source.parent)
        shutil.copytree(overlay, source / "src/full", dirs_exist_ok=True)
        run(["patch", "-p1", "--forward", "--batch", "-i", str(adapter)], cwd=source)
        marker.write_text(expected_marker, encoding="utf-8")

    allow_newer = ",".join(manifest.get("cabal_allow_newer", []))
    # Cabal 3.12 resolves Agda's packaged build tools incorrectly when this
    # local build directory is expressed as an absolute path.
    command = [
        "cabal", "build", "exe:agda", "--builddir=dist-bedrock", "-j2",
    ]
    if allow_newer:
        command.append(f"--allow-newer={allow_newer}")
    command.extend(macos_ghc_options())
    run(command, cwd=source)
    executable = subprocess.check_output(
        ["cabal", "list-bin", "exe:agda", "--builddir=dist-bedrock"],
        cwd=source, text=True,
    ).strip()

    install = build_root / "install"
    binary = install / "bin/agda"
    data = install / "data"
    binary.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(executable, binary)
    shutil.rmtree(data, ignore_errors=True)
    shutil.copytree(source / "src/data", data)
    (install / "bedrock-agda.json").write_text(
        json.dumps(
            {
                "schema": 1,
                "agda_version": version,
                "source_sha256": source_sha256,
                "adapter": manifest["adapter"],
                "overlay_sha256": overlay_hash,
                "fingerprint": fingerprint,
            },
            indent=2,
            sort_keys=True,
        ) + "\n",
        encoding="utf-8",
    )

    wrapper = root / "_build/bin/bedrock-agda"
    wrapper.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text(
        "#!/bin/sh\n"
        "set -eu\n"
        "bedrock_build=$(CDPATH= cd -- \"$(dirname -- \"$0\")/..\" && pwd)\n"
        "if [ \"${1-}\" = --bedrock-version ]; then\n"
        "  cat \"$bedrock_build/bedrock-agda/install/bedrock-agda.json\"\n"
        "  exit 0\n"
        "fi\n"
        "Agda_datadir=\"$bedrock_build/bedrock-agda/install/data\"; export Agda_datadir\n"
        "exec \"$bedrock_build/bedrock-agda/install/bin/agda\" \"$@\"\n",
        encoding="utf-8",
    )
    wrapper.chmod(0o755)
    print(f"built {wrapper}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
