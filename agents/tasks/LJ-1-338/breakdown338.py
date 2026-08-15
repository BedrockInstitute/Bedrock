"""[LJ-1.338] The site-3 line breakdown, on the ledger caliber.

It counts non-blank lines and code-only lines for each named span of
`ProbeLeaf338.agda`, so the third site's figure is not one number an
author chose but a table anybody can re-run.

Run it from the repository root.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PROBE = ROOT / "agents" / "tasks" / "LJ-1-338" / "ProbeLeaf338.agda"

SPANS = [
    ("head: OPTIONS, comment, imports, opens", 1, 46),
    ("the ambient transport, [LJ-1.297]'s", 76, 84),
    ("the sixteen indices", 85, 102),
    ("Supply telescope, with residues 1 and 2", 112, 128),
    ("environment, KFacts lift, shared block", 129, 180),
    ("SUPPLIED ties 1 to 10", 181, 313),
    ("Leaf telescope: residues 3 to 6 plus twelve", 315, 352),
    ("instantiation and the two ambient crossings", 353, 366),
]


TASKS = ROOT / "agents" / "tasks"

# The two measured sites, on the caliber their own reports used, so this
# script re-derives 51 and 42 instead of quoting them (C-44).
SIBLINGS = [
    ("site 1, DomainAgree, ProbeLJ1302B.agda:81-142",
     TASKS / "LJ-1-302" / "ProbeLJ1302B.agda", 81, 142),
    ("site 2, EnvOneAgree, ProbeTies336.agda:94-145",
     TASKS / "LJ-1-336" / "ProbeTies336.agda", 94, 145),
]


def siblings():
    print()
    print("== THE TWO MEASURED SITES, RE-DERIVED ==")
    for name, path, first, last in SIBLINGS:
        chunk = path.read_text(encoding="utf-8").splitlines()[first - 1:last]
        nb = [r for r in chunk if r.strip()]
        code = [r for r in nb if not r.strip().startswith("--")]
        print("%-46s %9d %9d" % (name, len(nb), len(code)))


def main():
    rows = PROBE.read_text(encoding="utf-8").splitlines()
    total_nb = 0
    total_code = 0
    print("%-46s %9s %9s" % ("span", "non-blank", "code"))
    for name, first, last in SPANS:
        chunk = rows[first - 1:last]
        nb = [r for r in chunk if r.strip()]
        code = [r for r in nb if not r.strip().startswith("--")]
        total_nb += len(nb)
        total_code += len(code)
        print("%-46s %9d %9d" % (name, len(nb), len(code)))
    print("%-46s %9d %9d" % ("TOTAL", total_nb, total_code))

    whole = [r for r in rows if r.strip()]
    whole_code = [r for r in whole if not r.strip().startswith("--")]
    print("%-46s %9d %9d" % ("whole file, as a check", len(whole), len(whole_code)))
    siblings()


if __name__ == "__main__":
    main()
