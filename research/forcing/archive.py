#!/usr/bin/env python3
"""Verify and restore the immutable, deduplicated forcing research sources."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["verify", "list", "restore", "prepare"])
    parser.add_argument("--origin")
    parser.add_argument("--destination", type=Path)
    args = parser.parse_args()
    entries = json.loads((ROOT / "manifest.json").read_text())
    origins = sorted({entry["origin"] for entry in entries})
    if args.command == "list":
        print("\n".join(origins))
        return
    if args.command == "prepare":
        prefix = "k10-k11-resume-2026-09-18/reference-production/"
        entries = [dict(entry, path=entry["path"][len(prefix):])
                   for entry in entries
                   if entry["origin"] == "archive" and entry["path"].startswith(prefix)]
        args.destination = ROOT / "active" / "reference-production"
        if not entries:
            raise ValueError("Missing archived production foundation")
    if args.origin:
        if args.origin not in origins:
            parser.error("unknown origin")
        entries = [entry for entry in entries if entry["origin"] == args.origin]
    if args.command == "restore" and (not args.origin or not args.destination):
        parser.error("restore requires --origin and --destination")
    if args.command == "restore" and args.destination.exists():
        parser.error("destination must not exist; existing work is never overwritten")
    verified = set()
    for entry in entries:
        digest = entry["sha256"]
        if digest in verified and args.command == "verify":
            continue
        data = gzip.decompress(
            (ROOT / "objects" / digest[:2] / (digest[2:] + ".gz")).read_bytes()
        )
        if len(data) != entry["size"] or hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f"Corrupt object: {entry['origin']}:{entry['path']}")
        verified.add(digest)
        if args.command in {"restore", "prepare"}:
            relative = Path(entry["path"])
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError(f"Unsafe archive path: {relative}")
            target = args.destination / relative
            if target.exists():
                if target.read_bytes() != data:
                    raise ValueError(f"Existing file differs; refusing overwrite: {target}")
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    print(f"{args.command}: {len(entries)} entries, {len(verified)} verified objects")


if __name__ == "__main__":
    main()
