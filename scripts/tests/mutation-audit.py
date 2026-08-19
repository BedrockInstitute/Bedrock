#!/usr/bin/env python3
"""A gate that exists is not a gate that BITES. This breaks each one and asks.

**WHY THIS FILE EXISTS.** L3's first round asked whether every rule still has an
enforcer and answered yes: 22 pre-flight codes declared and 22 emitted, every point R1
to R18 names present in the tree, every checker any conjunct names on disk. That answer
is worth exactly as much as the gates are awake. A checker that is imported, run, and
whose result nothing asserts is indistinguishable from a checker that is deleted, and
`--check` cannot tell you which one you have.

**THE METHOD.** Break one gate, run the suites, and require that at least one goes RED.
A mutant that SURVIVES names a gate no test notices. On 2026-08-19, the first full run,
every mutant died: 22 of 22 pre-flight checks, 6 of 6 conjuncts, 8 of 8 pre-commit hook
members, 2 of 2 spec-surface refusal paths and 5 R rule properties.

**IT IS NOT PART OF `make check` AND IT MUST NOT BE.** One full pass edits real source
files and runs four suites once per mutant, which is minutes, not seconds. It is a
maintainer tool, run when a gate is added or when a gate class is under suspicion.

**WHAT IT CANNOT TELL YOU, and this is a limitation and not a defect.** It reports the
first suite that goes red and never WHICH test. A mutant can therefore die because it
broke an unrelated assertion rather than the gate's own, and it still reads as「the gate
bites」. Raised while attacking this tool on 2026-08-19. Closing it means running one
named test per mutant, which needs a mutant-to-test map that nothing carries today; until
then a `died in <suite>` is evidence that SOMETHING noticed and not proof that the right
thing did.

**IT REFUSES A DIRTY TREE, and that guard is not optional.** It restores by
`git checkout --`, so an uncommitted edit to a file it mutates would be DESTROYED. The
refusal names the file.

Usage:
  mutation-audit.py --preflight | --conjuncts | --gates | --rules | --all
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent

#: Ordered cheapest first, so a biting mutant is usually caught by the first suite.
SUITES = ["scripts/tests/test_pod_table.py", "scripts/tests/test_pod_facts.py",
          "scripts/tests/test_pod_gates.py", "scripts/tests/test_pod_loop.py",
          "scripts/tests/test_scripts_layout.py"]

PREFLIGHT = "scripts/pod/preflight.py"
ACCEPT = "scripts/pod/accept.py"
POD = "scripts/pod/pod.py"
TABLE = "scripts/pod/table.py"
HOOK = "scripts/git-hooks/pre-commit"
SURFACE = "scripts/pod/check-spec-surface.py"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def clean(paths) -> list[str]:
    """The files among `paths` that carry an uncommitted change."""
    out = git("status", "--porcelain", "--", *paths).stdout
    return sorted({line[3:].strip() for line in out.split("\n") if len(line) > 3})


def suites_notice() -> str | None:
    """The first suite that goes red, or None when every one stays green."""
    for s in SUITES:
        if subprocess.run([sys.executable, s], cwd=ROOT,
                          capture_output=True).returncode != 0:
            return pathlib.Path(s).stem.replace("test_pod_", "").replace("test_", "")
    return None


def trial(rel: str, mutate, label: str, results: list) -> None:
    """Write one mutant, ask the suites, restore. `mutate` takes and returns source."""
    p = ROOT / rel
    orig = p.read_text(encoding="utf-8")
    new = mutate(orig)
    if new is None or new == orig:
        print(f"  {label:<52} SKIP  the anchor moved")
        results.append((label, "SKIP"))
        return
    p.write_text(new, encoding="utf-8")
    try:
        caught = suites_notice()
    finally:
        git("checkout", "--", rel)
    print(f"  {label:<52} {'SURVIVED' if not caught else 'died in ' + caught}")
    results.append((label, "SURVIVED" if not caught else "died"))


# ---------------------------------------------------------------- the mutant families


def _first_literal(node):
    import ast
    a = node.args[0] if node.args else None
    if isinstance(a, ast.Constant) and isinstance(a.value, str):
        return a.value
    if isinstance(a, ast.JoinedStr) and a.values:
        v = a.values[0]
        if isinstance(v, ast.Constant) and isinstance(v.value, str):
            return v.value
    return ""


def preflight_family(results):
    """DELETE one pre-flight check. It is deleted and never renamed, because renaming
    tests whether the CODE is asserted and deleting tests whether the check bites."""
    import ast
    src = (ROOT / PREFLIGHT).read_text(encoding="utf-8")
    codes = sorted({m for m in re.findall(r'f?"(P\d+)\b', src)}, key=lambda x: int(x[1:]))
    print(f"pre-flight, {len(codes)} check(s):")

    class Killer(ast.NodeTransformer):
        def __init__(self, code):
            self.code, self.n = code, 0

        def visit_Expr(self, node):
            c = node.value
            if (isinstance(c, ast.Call) and isinstance(c.func, ast.Attribute)
                    and c.func.attr == "append"
                    and re.match(rf"{self.code}\b", _first_literal(c))):
                self.n += 1
                return ast.Pass()
            return node

    for code in codes:
        def m(o, code=code):
            tree = ast.parse(o)
            k = Killer(code)
            tree = k.visit(tree)
            ast.fix_missing_locations(tree)
            return ast.unparse(tree) if k.n else None
        # P22 PRINTS AND NEVER REFUSES, by design, so it has no `d.append` site and its
        # mutant is the print loop instead. The module docstring carries the reason.
        if code == "P22":
            def m(o):
                a = ('        for rel in p22_readmes(text, root):')
                return o.replace(a, "        for rel in []:", 1) if a in o else None
        trial(PREFLIGHT, m, f"{code} deleted", results)


CONJUNCTS = {5: "(5, c5)", 1: '(1, r1["rc"] == 0)', 2: "(2, d3 <= 0)",
             3: "(3, c3)", 4: "(4, c4)", 6: "(6, c6)"}
CONJUNCT_NAMES = {5: "spec_surface", 1: "agda", 2: "obligations_up",
                  3: "closure_open", 4: "unbound_hyp", 6: "lint"}


def conjunct_family(results):
    """Force one conjunct to always HOLD. A conjunct that cannot fail guards nothing."""
    print(f"acceptance, {len(CONJUNCTS)} conjunct(s):")
    for n, term in CONJUNCTS.items():
        def m(o, n=n, term=term):
            line = next((l for l in o.split("\n") if l.startswith("    held = [")), None)
            return o.replace(line, line.replace(term, f"({n}, True)"), 1) if line and term in line else None
        trial(ACCEPT, m, f"conjunct {n} ({CONJUNCT_NAMES[n]}) always holds", results)


def gate_family(results):
    """Drop one pre-commit hook member, then break each spec-surface refusal path."""
    hook = (ROOT / HOOK).read_text(encoding="utf-8")
    members = [l for l in hook.split("\n") if l.startswith("$PY ")]
    print(f"pre-commit hook, {len(members)} member(s):")
    for line in members:
        def m(o, line=line):
            return o.replace(line + "\n", "", 1) if line + "\n" in o else None
        trial(HOOK, m, line.replace("$PY ", "").split()[0] + " dropped", results)

    print("spec-surface, 2 refusal path(s):")

    def no_diff(o):
        mm = re.search(r"^def differences\((?:[^)]|\n)*\)[^:\n]*:\n", o, re.M)
        return o[:mm.end()] + "    return []  # MUTANT\n" + o[mm.end():] if mm else None
    trial(SURFACE, no_diff, "differences() reports nothing", results)

    def no_trailer(o):
        a = "    if TRAILER_RE.search(message):\n        return 0"
        return o.replace(a, "    if True:\n        return 0  # MUTANT", 1) if a in o else None
    trial(SURFACE, no_trailer, "the commit-msg trailer is not required", results)


def head_end(src: str, name: str):
    m = re.search(rf"^def {re.escape(name)}\((?:[^)]|\n)*\)[^:\n]*:\n", src, re.M)
    return m.end() if m else None


RULES = [
    ("R3  the replay stops guarding an admission", TABLE, "admit_rows", "    return True\n"),
    ("R4  a done row closes with a conjunct red", ACCEPT, "r4_holds", "    return True\n"),
    ("R12 admits() stops capping concurrency", POD, "admits", "    return True\n"),
    ("R15 the maintainer's scope stops being checked", POD, "maintainer_scope_ok",
     "    return True\n"),
]


def rule_family(results):
    """Break the PROPERTY an R rule claims, rather than deleting a call."""
    print(f"R rule properties, {len(RULES) + 1} of them:")
    for label, rel, fn, body in RULES:
        def m(o, fn=fn, body=body):
            i = head_end(o, fn)
            return None if i is None else o[:i] + body + o[i:]
        trial(rel, m, label, results)

    def r7(o):
        a = "    if not ch:\n        return None"
        return o.replace(a, "    if False:\n        return None  # MUTANT", 1) if a in o else None
    trial(ACCEPT, r7, "R7  a return with no change is NOT dropped", results)


FAMILIES = {"--preflight": (preflight_family, [PREFLIGHT]),
            "--conjuncts": (conjunct_family, [ACCEPT]),
            "--gates": (gate_family, [HOOK, SURFACE]),
            "--rules": (rule_family, [TABLE, ACCEPT, POD])}


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 2
    want = list(FAMILIES) if argv[0] == "--all" else [a for a in argv if a in FAMILIES]
    if not want:
        print(f"mutation-audit: REFUSED. unknown family {argv[0]!r}", file=sys.stderr)
        print(__doc__[__doc__.index("Usage:"):], file=sys.stderr)
        return 2
    touched = sorted({f for w in want for f in FAMILIES[w][1]})
    dirty = clean(touched)
    if dirty:
        print("mutation-audit: REFUSED. It restores by `git checkout --`, so an "
              "uncommitted\nchange to a file it mutates would be DESTROYED. Commit or "
              "stash these first:", file=sys.stderr)
        for f in dirty:
            print(f"  {f}", file=sys.stderr)
        return 2
    # **THE BASELINE IS CHECKED FIRST, AND SKIPPING IT INVERTS EVERY RESULT.** MEASURED
    # 2026-08-19, by this tool against itself: one suite was ALREADY red for an unrelated
    # reason, so `suites_notice()` returned that suite for every mutant and all eight
    # pre-commit mutants read as「died」. They had not died. When the unrelated failure
    # was fixed the same eight SURVIVED, which was the true answer. A red baseline turns
    # this tool into one that always says the gates are awake, which is the exact defect
    # it exists to find.
    print("baseline: every suite must be GREEN before a mutant means anything.")
    red = suites_notice()
    if red is not None:
        print(f"mutation-audit: REFUSED. `{red}` is red before any mutation, so every "
              f"mutant would\nread as caught by it. Fix that suite first.",
              file=sys.stderr)
        return 2
    print("baseline: clean.\n")
    results: list = []
    for w in want:
        FAMILIES[w][0](results)
        print()
    survived = [l for l, v in results if v == "SURVIVED"]
    skipped = [l for l, v in results if v == "SKIP"]
    if skipped:
        # **A SKIP IS AN UNTESTED GATE AND IT USED TO EXIT CLEAN.** An anchor that moved
        # means the mutant was never built, so nothing was learned about that gate, and
        # printing it while returning 0 reads as「every gate bites」. Raised by an
        # adversarial review on 2026-08-19.
        print(f"mutation-audit: FAIL. {len(skipped)} mutant(s) could not be BUILT, so "
              f"those gates are UNTESTED and not clean. An anchor moved:")
        for l in skipped:
            print(f"  {l}")
        return 1
    if survived:
        print(f"mutation-audit: FAIL. {len(survived)} of {len(results)} mutant(s) "
              f"SURVIVED, so no test notices these gates:")
        for l in survived:
            print(f"  {l}")
        return 1
    print(f"mutation-audit: clean. {len(results)} mutant(s), every one died.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
