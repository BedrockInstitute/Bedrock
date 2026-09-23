#!/usr/bin/env python3
"""Check the classified inventory of direct host-LEM uses in literate Agda."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
INVENTORY = ROOT / "dev" / "host-lem-inventory.json"
SOURCE_ROOTS = (ROOT / "src" / "FOL", ROOT / "src" / "L", ROOT / "src" / "V")
CLASSIFICATIONS = {
    "resizing-bridge",
    "formula-satisfaction",
    "atomic-membership",
    "atomic-equality",
    "constructively-decidable",
    "host-only",
    "unresolved",
}
SKIP_PREFIXES = ("module ", "private module ", "open import ", "import ")
DECLARATION = re.compile(r"^\s*([^\s:(){}]+)\s*:")
EQUATION = re.compile(r"^\s*([^\s:(){}]+)(?:\s|\{).*=")
LEM_TOKEN = re.compile(r"(?<![\w→←-])(?:lem|lemℓ)(?![\w→←-])")


def code_lines(path: Path):
    in_code = False
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if line.strip() == "```agda":
            in_code = True
            continue
        if in_code and line.strip() == "```":
            in_code = False
            continue
        if in_code:
            yield number, line


def classify(path: str, source: str) -> tuple[str, str, str, str]:
    if "LEM→Resizing" in source or "LEM→ΩResizing" in source or "SetChoice→LEM" in source:
        return "resizing-bridge", "LEM→Resizing / LEM→ΩResizing", "resizing equivalence", "migrated"
    if "decideMembership" in source or "definedCell" in source:
        return "atomic-membership", "FOL.Semantics.decideMembership", "atomic membership computes by refl", "migrated"
    if "decideEquality" in source or "definedDenotes" in source:
        return "atomic-equality", "FOL.Semantics.decideEquality or equality formula package", "atomic equality computes by refl", "migrated"
    if any(name in source for name in ("decideSatisfaction", "satDecision", "searchPredicate", "definedGood", "definedP")):
        return "formula-satisfaction", "formula plus environment supplied at call", "FormulaPredicate.reading or definitional equality", "migrated"
    if "leastOfFormula" in source:
        return "formula-satisfaction", "FormulaPredicate argument", "FormulaPredicate.reading", "migrated"
    if path.endswith("L/GCH/BelowSuccessorCardinal.lagda.md") and "lem (Ex" in source:
        return (
            "unresolved",
            "direct host decision bypasses the available injLAt formula adapter",
            "injLAt with InjLAt.fill/read",
            "pending",
        )
    if path.endswith("L/GCH/Assembly.lagda.md") and "HostLeast.leastOf" in source:
        return (
            "unresolved",
            "host search bypasses the available cardinalAt formula adapter",
            "cardinalAt with CardinalAt.fill/read",
            "pending",
        )
    if path.endswith("L/GCH/CardinalRepresentative.lagda.md") and "HostLeast.leastOf" in source:
        return (
            "unresolved",
            "host search bypasses the available injLAt formula adapter",
            "injLAt with InjLAt.fill/read",
            "pending",
        )
    if "∈" in source:
        return "atomic-membership", "atomic formula adapter not yet installed", "pending", "pending"
    if "≡" in source or "setIsSet" in source:
        return "atomic-equality", "atomic formula adapter not yet installed", "pending", "pending"
    if path.endswith("FOL/Semantics.lagda.md"):
        return "formula-satisfaction", "FOL.Semantics.decideSatisfaction", "the decided proposition is satisfaction itself", "migrated"
    host_modules = (
        "V/CantorBernstein.lagda.md",
        "L/WellOrder/Base.lagda.md",
        "L/Choice/FiniteStageOrders.lagda.md",
        "L/Ordinal/Linear.lagda.md",
        "L/Ordinal/SquareLaw.lagda.md",
        "L/Stage.lagda.md",
        "L/CardinalAbove.lagda.md",
    )
    if path.endswith("L/GCH/SkolemHull.lagda.md") and ("lem P" in source):
        return "host-only", "classical host proposition exposed by the local theorem", "not applicable", "allowlisted"
    if path.endswith(host_modules):
        return "host-only", "module theorem explicitly assumes host LEM", "not applicable", "allowlisted"
    return "unresolved", "none recorded", "none recorded", "pending"


def discover() -> list[dict[str, object]]:
    uses: list[dict[str, object]] = []
    paths = sorted(path for root in SOURCE_ROOTS for path in root.rglob("*.lagda.md"))
    for path in paths:
        definitions: list[tuple[int, str]] = []
        for number, line in code_lines(path):
            stripped = line.strip()
            if not stripped or stripped.startswith(SKIP_PREFIXES):
                continue
            indent = len(line) - len(line.lstrip())
            declaration = DECLARATION.match(line)
            equation = EQUATION.match(line)
            if declaration:
                while definitions and definitions[-1][0] >= indent:
                    definitions.pop()
                definitions.append((indent, declaration.group(1)))
            elif equation and not stripped.startswith(("where", "with")):
                name = equation.group(1)
                if not definitions or definitions[-1][1] != name:
                    while definitions and definitions[-1][0] >= indent:
                        definitions.pop()
                    definitions.append((indent, name))

            if declaration and "=" not in line:
                continue
            segment = line.split("=", 1)[1] if "=" in line else line
            matches = list(LEM_TOKEN.finditer(segment))
            if not matches:
                continue
            source = " ".join(stripped.split())
            relative = path.relative_to(ROOT).as_posix()
            definition = definitions[-1][1] if definitions else "<module>"
            classification, supplier, reading, status = classify(relative, source)
            for occurrence, match in enumerate(matches, 1):
                uses.append(
                    {
                        "module": relative.removeprefix("src/").removesuffix(".lagda.md").replace("/", "."),
                        "definition": definition,
                        "decided_proposition": source,
                        "classification": classification,
                        "supplier": supplier,
                        "reading_lemma": reading,
                        "migration_status": status,
                        "site": f"{relative}:{source}:{match.group(0)}:{occurrence}",
                    }
                )
    return uses


def validate(entries: list[dict[str, object]]) -> list[str]:
    errors: list[str] = []
    required = {
        "module", "definition", "decided_proposition", "classification",
        "supplier", "reading_lemma", "migration_status", "site",
    }
    for index, entry in enumerate(entries):
        missing = sorted(required - entry.keys())
        if missing:
            errors.append(f"entry {index}: missing {', '.join(missing)}")
        if entry.get("classification") not in CLASSIFICATIONS:
            errors.append(f"entry {index}: invalid classification {entry.get('classification')!r}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="refresh the inventory from the current tree")
    args = parser.parse_args()
    discovered = discover()
    if args.write:
        INVENTORY.write_text(json.dumps({"schema_version": 1, "uses": discovered}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {len(discovered)} direct host-LEM uses to {INVENTORY.relative_to(ROOT)}")
        return 0
    try:
        payload = json.loads(INVENTORY.read_text(encoding="utf-8"))
        recorded = payload["uses"]
    except (OSError, json.JSONDecodeError, KeyError) as error:
        print(f"host-LEM inventory error: {error}")
        return 1
    errors = validate(recorded)
    actual_sites = Counter(entry["site"] for entry in discovered)
    recorded_sites = Counter(entry.get("site") for entry in recorded)
    for site, count in sorted((actual_sites - recorded_sites).items()):
        errors.append(f"unclassified direct host-LEM use ({count}): {site}")
    for site, count in sorted((recorded_sites - actual_sites).items()):
        errors.append(f"stale host-LEM inventory entry ({count}): {site}")
    discovered_by_site = {entry["site"]: entry for entry in discovered}
    for entry in recorded:
        actual = discovered_by_site.get(entry.get("site"))
        if actual is not None and entry != actual:
            errors.append(f"stale host-LEM classification: {entry.get('site')}")
    if errors:
        print("host-LEM inventory check failed:")
        for error in errors:
            print(f"  - {error}")
        return 1
    counts = Counter(entry["classification"] for entry in recorded)
    summary = ", ".join(f"{key}={counts[key]}" for key in sorted(counts))
    print(f"host-LEM inventory: {len(recorded)} uses classified ({summary})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
