"""Count source lines in literate Agda masters, independently of their prose."""

import argparse
import json
from pathlib import Path


def count(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    inside = False
    code = []
    for line in lines:
        if inside:
            if line.strip() == "```":
                inside = False
            else:
                code.append(line)
        elif line.strip() == "```agda":
            inside = True
    return {
        "nonblank_code": sum(bool(line.strip()) for line in code),
        "code": len(code),
        "physical": len(lines),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path,
                        default=Path(__file__).resolve().parents[2] / "src")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    files = {str(path.relative_to(args.src)): count(path)
             for path in sorted(args.src.rglob("*.lagda.md"))}
    if not files:
        parser.error(f"no literate Agda masters found in {args.src}")
    totals = {key: sum(row[key] for row in files.values())
              for key in ("nonblank_code", "code", "physical")}
    if args.json:
        print(json.dumps({"totals": totals, "files": files}, indent=2))
    else:
        print(f"{len(files)} modules; " + "; ".join(
            f"{value:,} {key}" for key, value in totals.items()))


if __name__ == "__main__":
    main()
