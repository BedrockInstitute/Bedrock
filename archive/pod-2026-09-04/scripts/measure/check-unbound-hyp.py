#!/usr/bin/env python3
"""Find telescope hypotheses that are refutable by regularity.

WHY THIS EXISTS. Phase LJ-1 lost about a thousand delivered lines to seven
statement-level defects, and every one was the same species: a module
telescope hypothesis whose conclusion asserts a membership for a set that no
premise constrains. Instantiate the free set at the bounding set's own
element and regularity closes it, so the type is EMPTY and the module is
vacuous. It typechecks, it is fast, and it proves nothing.

`dev/LESSONS.md` C-38 named the shape and said a checker was worth writing
but that a grep is not enough: the orchestrator's one-line regex over-matched
and flagged `carrierK`, which is sound. This is the parse.

TWO RULES, and between them they catch all eleven of the phase's refuted
hypotheses.

  Rule 1, the conclusion side. The hypothesis concludes `⟨ A ∈ B ⟩` and some
  variable free in `A` is bound by the hypothesis's own telescope and occurs
  in NO premise. `tmKeyK`, `valK`, `valK-un`, `succK`, `keyK-un`, `keyK-neg`,
  `succK-allin`, `keyK-allin` are this shape.

  Rule 2, the premise side. A membership premise `⟨ A ∈ B ⟩` has `B` a bare
  variable bound by the same telescope and constrained by nothing else, so
  the premise is satisfiable at a set the author never intended. `entryK` and
  the `arSubK-*` family are this shape.

WHAT IT DOES NOT CLAIM. A flag is a question, never a verdict: the cure is a
refutation probe (`agents/tasks/LJ-1-97/ProbeLJ197A.agda` is the shape, and it is one line of
real content per fact). A clean run is not a proof that the telescopes are
inhabited, because inhabitation is not decidable here. Read the report as
"these are worth a refutation attempt", which is exactly what C-38 asks.

Usage:
    check-unbound-hyp.py [--check] [paths ...]

With no paths it reads every tracked `.lagda.md` under `src/`.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

# LJ-1.291: the root is found by walking up to the repository marker, never by
# counting directories; `scripts/repo_root.py` holds the one walk. LJ-1.295:
# this script lives in a group directory under scripts/, so the SCRIPTS root,
# where `repo_root.py` and `agents_tree.py` sit flat, is found the same way,
# by walking up to `repo_root.py` itself; the group directory joins sys.path
# for siblings imported by bare name.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)

# A telescope hypothesis opens a line at some indent with `(name : ` and runs
# until its parenthesis closes. Agda allows `{name : ...}` too; an implicit
# hypothesis is the same defect, so both are read.
OPEN = re.compile(r"^(\s*)([({])\s*([A-Za-z_][^\s:]*(?:\s+[A-Za-z_][^\s:]*)*)\s*:\s")

# A membership, in the two spellings the tree uses.
MEMBER = re.compile(r"⟨([^⟨⟩]*?)\s*∈ˢ?\s*([^⟨⟩]*?)⟩")

# Tokens that are never a bound variable of a telescope.
NOT_A_VAR = {
    "fst", "snd", "lookup", "suc", "zero", "pr", "prʟ", "pairʟ", "sucV",
    "numeralL", "Lset", "Empty", "⊥", "S", "ℕ", "Type", "Fin", "Σ", "Π",
    "λ", "let", "in", "where", "with", "if", "then", "else", "sett",
    "true", "false", "refl", "cong", "sym", "transport", "the",
}

VAR = re.compile(r"(?<![\w'ʟ′])([a-z][\w'′]*)(?![\w'ʟ′])")


def tracked_masters() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "src/**/*.lagda.md", "src/*.lagda.md"],
        cwd=ROOT, capture_output=True, text=True, check=False,
    ).stdout.split()
    return [ROOT / f for f in out if f.endswith(".lagda.md")]


def fences(path: Path) -> list[tuple[int, str]]:
    """Lines inside ```agda fences, as (1-based line number, text)."""
    out: list[tuple[int, str]] = []
    inside = False
    for n, line in enumerate(path.read_text().split("\n"), 1):
        stripped = line.strip()
        if stripped.startswith("```"):
            inside = stripped.startswith("```agda")
            continue
        if inside:
            out.append((n, line))
    return out


def balanced(text: str) -> bool:
    depth = 0
    for ch in text:
        if ch in "({":
            depth += 1
        elif ch in ")}":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def hypotheses(lines: list[tuple[int, str]]):
    """Yield (line_number, names, body) for each telescope hypothesis."""
    i = 0
    while i < len(lines):
        n, line = lines[i]
        m = OPEN.match(line)
        if not m:
            i += 1
            continue
        indent, opener, names = m.group(1), m.group(2), m.group(3)
        chunk = line[len(indent):]
        j = i
        # A telescope entry may wrap; gather until the parens balance.
        while not balanced(chunk) and j + 1 < len(lines) and j - i < 40:
            j += 1
            chunk += "\n" + lines[j][1]
        if balanced(chunk):
            body = chunk.strip()
            body = body[1:-1] if body[:1] == opener and body[-1:] in ")}" else body
            after = body.split(":", 1)
            if len(after) == 2:
                yield n, names.split(), after[1]
        i = j + 1


def split_arrows(body: str) -> list[str]:
    """Split a hypothesis body on top-level `→`."""
    parts, depth, cur = [], 0, ""
    k = 0
    while k < len(body):
        ch = body[k]
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        if ch == "→" and depth == 0:
            parts.append(cur)
            cur = ""
            k += 1
            continue
        cur += ch
        k += 1
    parts.append(cur)
    return [p.strip() for p in parts if p.strip()]


def binder_groups(part: str) -> list[tuple[str, str]] | None:
    """Parse a part into `(vars, type)` groups, or None if it is not a
    pure binder group.

    The type may itself carry parentheses (`Fin (11 + n)` is the case that
    made the first draft miss `succK`), so the scan is by depth and not by a
    character class.
    """
    groups: list[tuple[str, str]] = []
    i, n = 0, len(part)
    while i < n:
        if part[i].isspace():
            i += 1
            continue
        if part[i] not in "({":
            return None
        close = ")" if part[i] == "(" else "}"
        depth, j = 0, i
        while j < n:
            if part[j] in "({":
                depth += 1
            elif part[j] in ")}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if j >= n or part[j] != close:
            return None
        inner = part[i + 1:j]
        if ":" not in inner:
            return None
        names, ty = inner.split(":", 1)
        groups.append((names.strip(), ty.strip()))
        i = j + 1
    return groups or None


# Regularity refutes a membership claim about a SET. A variable at ℕ or at a
# slot index is not a set, so an unconstrained one is not this defect: that
# is what over-flagged `innerK`, whose loose variable is `k : ℕ`.
SET_TYPE = re.compile(r"^S$|^V\b|⟪|hProp")


def telescope(parts: list[str]) -> tuple[set[str], list[str]]:
    """Split a hypothesis body into its leading Pi-telescope and the rest.

    Only SET-typed binders are returned. Counting a binder group as a premise
    is the bug that made the first draft silently clean: the bound variable
    appeared in its own binder, so every conclusion variable looked
    constrained.
    """
    bound: set[str] = set()
    k = 0
    for part in parts:
        groups = binder_groups(part)
        if groups is None:
            break
        for names, ty in groups:
            if SET_TYPE.search(ty):
                bound.update(v for v in names.split() if v not in NOT_A_VAR)
        k += 1
    return bound, parts[k:]


def _arg(text: str, k: int) -> tuple[str, int]:
    """Read one argument starting at k: a balanced group or a bare token."""
    while k < len(text) and text[k].isspace():
        k += 1
    if k >= len(text):
        return "", k
    if text[k] == "(":
        depth, j = 0, k
        while j < len(text):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    return text[k + 1:j], j + 1
            j += 1
        return text[k:], len(text)
    j = k
    while j < len(text) and not text[j].isspace() and text[j] not in "()":
        j += 1
    return text[k:j], j


def resolve_lookups(text: str) -> str:
    """Rewrite `lookup (suc^n zero) (v0 ∷ v1 ∷ ... ∷ γ)` to `vn`.

    Without this the whole cons list counts as free in the term, and every
    tied hypothesis in this tree reads as unconstrained: `succK`'s repaired
    form carries the premise `ar ∈ K` and concludes about
    `lookup 5 (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)`, which IS `ar` and mentions
    six other names. That spelling was the dominant false positive, and it
    needs a balanced-paren read: the index is `suc (suc (suc ...))`, which no
    character class walks.
    """
    for _ in range(6):
        out, k, changed = "", 0, False
        while True:
            hit = text.find("lookup", k)
            if hit < 0:
                out += text[k:]
                break
            out += text[k:hit]
            idx, after = _arg(text, hit + 6)
            lst, after2 = _arg(text, after)
            if "zero" in idx and "∷" in lst:
                n = idx.count("suc")
                items = [x.strip() for x in lst.split("∷")]
                if n < len(items) - 1:
                    out += " " + items[n] + " "
                    k, changed = after2, True
                    continue
            out += text[hit:after2]
            k = after2
        text = out
        if not changed:
            break
    return text


def free_vars(text: str) -> set[str]:
    return {v for v in VAR.findall(resolve_lookups(text))
            if v not in NOT_A_VAR}


def scan(path: Path) -> list[tuple[int, str, str]]:
    found: list[tuple[int, str, str]] = []
    for n, names, body in hypotheses(fences(path)):
        parts = split_arrows(body)
        if len(parts) < 1:
            continue
        bound, rest = telescope(parts)
        if not bound or not rest:
            continue
        concl = rest[-1]
        prems = rest[:-1]
        prem_text = " ".join(prems)
        name = names[0]

        # Rule 3: a non-empty telescope with NO premise at all, concluding
        # something that is not an equality. `tmKeyK`, `succK`, `keyK-un`,
        # `keyK-neg`, `succK-allin` and `keyK-allin` are this shape, and it
        # is the cheapest signal there is: the conclusion cannot depend on
        # anything, so every bound set is free.
        if not prems and "≡" not in concl:
            found.append((n, name, "rule 3, no premise at all: "
                          f"{', '.join(sorted(bound))} are free"))
            continue

        # Rule 1: a conclusion membership whose subject carries a bound
        # variable that no premise mentions.
        for subj, _obj in MEMBER.findall(concl):
            loose = (free_vars(subj) & bound) - free_vars(prem_text)
            if loose:
                found.append((n, name, "rule 1, conclusion subject "
                              f"unconstrained: {', '.join(sorted(loose))}"))
                break

        # Rule 2: a membership premise whose OBJECT is built only from
        # variables this telescope binds, none of which reaches the
        # conclusion. The premise is then satisfiable at a set the author
        # never intended: `entryK` takes `pr x y ∈ fst z` for a free `z`,
        # and the `arSubK-*` family takes `x ∈ ar` for a free `ar` spelled
        # through a `lookup`. Requiring the intersection to be NON-EMPTY is
        # what keeps a sound conditional such as `carrierK` unflagged: its
        # bound is a module parameter, not a variable of its own telescope.
        for idx, prem in enumerate(prems):
            hit = False
            for _subj, obj in MEMBER.findall(prem):
                obj_bound = free_vars(obj) & bound
                if not obj_bound:
                    continue
                others = " ".join(prems[:idx] + prems[idx + 1:])
                if obj_bound & (free_vars(others) | free_vars(concl)):
                    continue
                found.append((n, name, "rule 2, premise bound only by "
                              f"free variables: {', '.join(sorted(obj_bound))}"))
                hit = True
                break
            if hit:
                break

    return found


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 when anything is flagged")
    args = ap.parse_args()

    targets = [Path(p) for p in args.paths] if args.paths else tracked_masters()
    total = 0
    for path in targets:
        if not path.exists():
            print(f"check-unbound-hyp: no such file: {path}", file=sys.stderr)
            return 2
        for n, name, why in scan(path):
            rel = path.relative_to(ROOT) if path.is_absolute() else path
            print(f"{rel}:{n}: {name}: {why}")
            total += 1

    if total:
        print(f"\ncheck-unbound-hyp: {total} hypothesis/hypotheses worth a "
              f"refutation attempt (see dev/LESSONS.md C-38, and "
              f"agents/tasks/LJ-1-97/ProbeLJ197A.agda for the probe shape)")
        return 1 if args.check else 0
    print(f"check-unbound-hyp: clean ({len(targets)} file(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main())
