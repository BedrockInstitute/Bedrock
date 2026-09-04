#!/usr/bin/env python3
"""The pre-flight of AD21: twenty-three checks over a brief, before the program spawns it.

WHY THIS FILE EXISTS, and the measurement is the project's own.
`agents/tasks/LJ-1-211/lj-1.211-report.md:21` reads: `The brief caused 8 of the 10. The
agent caused 2. The reviewer caused 0.` A bad brief is the most expensive defect this
repository has measured, and a worker cannot refuse one it has already been given. Every
check below is a predicate over the brief text and the filesystem: NO CHECK RUNS AGDA, NO
CHECK CALLS A MODEL, and no check touches the network.

FIVE CHECKS EXIST BECAUSE A SPECIFIC FAILURE HAPPENED, and they are the ones to read first:

- **P18, DD25's mechanised half.** A brief that can finish must also be attackable.
  `dev/ORCHESTRATION.md:108-112` records `[LJ-0.4]` refusing four blocks on measurement,
  the orchestrator accepting all four, and `[LJ-0.8]` then finding a propagated sign error
  standing in five places.
- **P20, because P18 can kill the branch it protects.** If the escalate branch outranks a
  `done` branch and both match the same record, the `done` branch is dead code, `route()`
  reproduces the same winner on every retry, and `attempt_max` parks the task instead of
  closing it.
- **P19 with amendment A6.** A `done` branch passes EITHER by
  `obligations_delta_max <= -len(obligations)` OR by `outcome = "no-go"`. A NO-GO leaves
  every declared name unresolved, so its delta is 0 and the first limb can never hold;
  without the second limb no brief could express a refusal.
- **P16, so a task is not blamed for its predecessor.** It tells the program whether the
  tree was already open BEFORE this task ran.
- **P23, because ARCHIVE and LITERATURE both point away from the present.** ARCHIVE looks
  backward at retired work and LITERATURE looks outward at the field; neither one names
  the tree's CURRENT shape. `[LJ-1.628]` heap-walled HEAVY on a ten-line landing with a
  truthful `ARCHIVE USED: NO HIT`, because the archive genuinely had nothing about a
  dependent count. P23 RE-RUNS the measurement the brief claims rather than checking a
  section exists, so a truthful heading can no longer stand in for a real number.

THE ONE CHECK THAT CANNOT REFUSE IS P22, and it exists so a per-directory `README.md` has
a named reader and a named occasion. Twenty of them live in the tree and no live document
names most of them.

ON A FAILED PRE-FLIGHT THE PROGRAM PARKS THE TASK AND NEVER DROPS IT. `preflight()`
returns a LIST of refusal strings, each starting with its check id, so rule (f) reads
`d[0].split()[0]` and writes `reason: "preflight:P4"` with the whole list in `detail`.
Rule (a2) un-parks the task once the brief passes.

WHERE A DEFECT WITH NO NAMED CHECK IS REPORTED. The table of section 6.5 names 22 checks
and a brief can be broken in ways no row names. This file never invents a check id: a
missing `action` reports under P6 with the value `<none>`, a missing `priority` or `id`
reports under P7, and a missing or empty `[branch.when]` block reports under P4 with the
key `<none>`. The refusal strings stay exactly as section 6.5 writes them, with ONE
disclosed departure, P11's second direction.

P11 TESTS BOTH DIRECTIONS, AND ONE OF THEM HAS NO MESSAGE IN SECTION 6.5. Section 4.2
rules that `head_slot` is required exactly when `action` is `escalate` AND ABSENT
OTHERWISE, and `table.check_row()` refuses both directions at admission. The pre-flight
tested only the first, so a brief carrying `head_slot` on a `park` branch passed the
pre-flight, reached `admit_rows()`, was refused there, and parked with
`reason: "admission"` instead of `reason: "preflight:P11"`. The check id stays P11; the
second direction's text says which direction failed, because section 6.5's one message,
`head slot <value> is not in heads.toml`, is FALSE about a legal slot on a `park` branch.

FOUR MORE RAISES WERE FOUND IN THIS FILE AND EACH ONE REACHED THE UNATTENDED LOOP.
`preflight()` must return a LIST and never raise, because rule (f) reads that list. An
unreadable `heads.toml` raised `TableError` out of P11; a non-string obligation entry
raised `AttributeError` out of P14; a branch whose `priority` was a string raised
`TypeError` inside P20's sort; and a branch whose `_in` value was a scalar raised
`TypeError` inside `contradicts()`. A branch VALUE of the wrong type is refused at
admission by `table.check_row()`, so the pre-flight only has to survive it.

Usage:
  preflight.py --brief <path>      run every check and print each refusal
  preflight.py --brief <path> -q   print nothing, and let the exit status speak
Exit status: 0 the brief passes, 1 one refusal or more, 2 usage error.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tomllib
from pathlib import Path

# LJ-1.291 and LJ-1.295: the root is found by walking up to the repository marker, never
# by counting directories. The group directory joins sys.path for siblings imported by
# bare name, and the scripts root is found by walking up to `repo_root.py` itself.
_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

import agents_tree  # noqa: E402
import facts  # noqa: E402
import table  # noqa: E402
import witness  # noqa: E402

ROOT = find_root(__file__)
CLOSURE = ROOT / "scripts" / "pod" / "check-closure.py"

SECTION = "^##[ \t]+{}"
#: A repository-relative path inside a brief. The trees are named rather than left open,
#: so a dotted module name such as `L.Cardinal` is never read as a path. `agents/` is in
#: the list because P8 must check exactly the paths `write_paths()` at `dispatch.py:1537`
#: drops: its own regex matches `src/`, `dev/`, `scripts/` and `_build/` only, and a
#: probe-only task writes nothing outside `agents/tasks/<CODE>/`.
PATH_TOKEN = re.compile(
    r"(?<![\w./-])((?:src|dev|scripts|_build|agents|docs|archive)/[\w./*?\[\]-]*"
    r"[\w*?\]])")
#: A basis, as `## PREMISES` writes one: `Basis: src/L/Cardinal.lagda.md:194-195`.
BASIS = re.compile(r"([\w./-]+\.(?:lagda\.md|agda|md|toml|py|sh|yml|jsonl))"
                   r":(\d+)(?:-(\d+))?")
GLOB_CHARS = "*?["
#: A `## MEASURED TODAY` line, P23: `- dependents: L.Choice.Faithful => 2`. Bulleted,
#: the same convention `## PREMISES` and `## OBLIGATION NAMES` already use, so `units()`
#: reads each line as its own entry instead of joining it onto its neighbour. The KIND is
#: one of the two fixed forms and never free text, so nothing here ever becomes a shell
#: command: the brief supplies the argument and the claimed count, and P23 recomputes
#: both itself.
MEASURED_LINE = re.compile(
    r"^[ \t]*-[ \t]*(dependents|supply)[ \t]*:[ \t]*(\S+)[ \t]*=>[ \t]*(\d+)[ \t]*$")


# ---------------------------------------------------------------- brief reading


def section(text: str, name: str) -> str | None:
    """One `## NAME` section body, or None when the heading is absent.

    The match is a PREFIX match, because the program appends a note to three headings:
    `## ARCHIVE (program-generated, do not edit)` is the heading section 7.4 writes.
    """
    m = re.search(SECTION.format(re.escape(name)) + r"[^\n]*\n(.*?)(?=\n##[ \t]|\Z)",
                  text, re.S | re.M)
    return m.group(1) if m else None


def units(body: str) -> list[str]:
    """The non-empty lines of a section, with a wrapped bullet joined to its head.

    `[L3.32-T249]` measured why: a prohibition that WRAPS puts its verb on one line and
    its paths on the next, and a per-line reader then treats the second line as its own
    unit. `write_paths()` at `dispatch.py:1552-1564` joins the same way.
    """
    out, cur = [], ""
    for ln in (body or "").split("\n"):
        if not ln.strip() or re.match(r"\s*([-*+]|\d+\.|#)", ln):
            if cur.strip():
                out.append(cur.strip())
            cur = ln
        else:
            cur = (cur + " " + ln).strip() if cur else ln
    if cur.strip():
        out.append(cur.strip())
    return out


def brief_code(text: str) -> str | None:
    """The code in the `# <CODE>: <one line>` heading, or None."""
    m = re.search(r"^#[ \t]+([A-Za-z0-9][\w.-]*)[ \t]*:", text, re.M)
    return m.group(1) if m else None


def head_field(text: str, name: str) -> str | None:
    """One `<name>: <value>` line of the `## HEAD` block, or None."""
    body = section(text, "HEAD")
    if body is None:
        return None
    m = re.search(rf"^[ \t]*{re.escape(name)}[ \t]*:[ \t]*(.+?)[ \t]*$", body, re.M)
    return m.group(1) if m else None


def scope_paths(text: str) -> list[str]:
    """Every path token under `## SCOPE (write)`, in order, with duplicates removed."""
    body = section(text, "SCOPE")            # the heading is `## SCOPE (write)`
    if body is None:
        return []
    out = []
    for u in units(body):
        for m in PATH_TOKEN.finditer(u):
            if m.group(1) not in out:
                out.append(m.group(1))
    return out


# ---------------------------------------------------------------- path predicates


def path_under_root(p: str, root=None) -> bool:
    """P8's first half: the path resolves UNDER the repository root.

    An absolute path and a `..` escape both fail. The check runs on the non-glob prefix,
    so a pattern is judged by the directory it lives in.
    """
    root = ROOT if root is None else Path(root)
    if not p or p.startswith("/") or p.startswith("~"):
        return False
    try:
        target = (root / _non_glob_prefix(p)).resolve()
        target.relative_to(root.resolve())
    except (ValueError, OSError):
        return False
    return True


def _non_glob_prefix(p: str) -> str:
    keep = []
    for seg in p.split("/"):
        if any(c in seg for c in GLOB_CHARS):
            break
        keep.append(seg)
    return "/".join(keep)


def path_resolves(p: str, root=None) -> bool:
    """P8: under the root, AND either the file exists or its parent directory exists.

    P8 ACCEPTS A FILE THAT DOES NOT YET EXIST, because `agents/tasks/LJ-1-386/Probe386.agda`
    is what the task writes. A GLOB is judged by its non-glob prefix, which must be a real
    directory, so `.../review-of-*.md` passes as soon as the task directory exists.
    """
    root = ROOT if root is None else Path(root)
    if not path_under_root(p, root):
        return False
    prefix = _non_glob_prefix(p)
    cand = root / prefix
    if prefix != p:                          # the path carries a glob
        return cand.is_dir()
    return cand.exists() or cand.parent.is_dir()


# ---------------------------------------------------------------- branch predicates


def branch_sort_key(b):
    """Section 4.4's order, inside ONE brief. Every branch shares one scope, so step 2 of
    the order is constant here and only steps 1, 3 and 4 can separate two branches.

    A NON-INTEGER PRIORITY SORTS AS ZERO rather than raising. P7 already refuses it, and a
    `TypeError` here from comparing a string with an integer would stop the loop before
    P7's refusal ever reached rule (f).
    """
    pri = b.get("priority", 0)
    if isinstance(pri, bool) or not isinstance(pri, int):
        pri = 0
    return (0 if b.get("action") == "stop_loop" else 1, pri, str(b.get("id", "")))


def outranks(a, b) -> bool:
    return branch_sort_key(a) < branch_sort_key(b)


def contradicts(a: dict, b: dict) -> bool:
    """P20's FIXED contradiction table over two `when` blocks. It needs no solver.

    THE FOUR TESTS, and section 6.5 names each one: two `exit_code` values that differ;
    two `_in` lists that are disjoint; two delta ranges that do not overlap; or ONE glob
    that appears verbatim in one block's `changed_files_any` and in the other's
    `changed_files_none`.

    THE LIMIT IS DISCLOSED. A separation written two different ways is not recognised, and
    P20 then REFUSES the brief, which is the safe direction. Two differing `error_class`
    scalars are exactly that case: they separate the two blocks and this table does not
    say so, so the author writes the separation as an `_in` pair or as a glob pair.

    A VALUE OF THE WRONG TYPE READS AS NO CONTRADICTION and never raises. `set(5)` and
    `"x" > 0` both raise `TypeError`, and this function runs BEFORE admission, where
    `table.check_row()` refuses the type. No contradiction is the safe direction, because
    P20 then refuses the brief.
    """
    def _list(block, k):
        """The key's value as a SET, or None when it is not a list of hashable scalars."""
        v = block.get(k)
        if not isinstance(v, list):
            return None
        try:
            return set(v)
        except TypeError:                    # a list holding a table
            return None

    def _int(block, k):
        v = block.get(k)
        return None if isinstance(v, bool) or not isinstance(v, int) else v

    if "exit_code" in a and "exit_code" in b and a["exit_code"] != b["exit_code"]:
        return True
    for k in ("exit_code_in", "error_class_in"):
        la, lb = _list(a, k), _list(b, k)
        if la is not None and lb is not None and not (la & lb):
            return True
    lo_a, hi_a = _int(a, "obligations_delta_min"), _int(a, "obligations_delta_max")
    lo_b, hi_b = _int(b, "obligations_delta_min"), _int(b, "obligations_delta_max")
    if lo_a is not None and hi_b is not None and lo_a > hi_b:
        return True
    if lo_b is not None and hi_a is not None and lo_b > hi_a:
        return True
    for one, two in ((a, b), (b, a)):
        any_, none_ = _list(one, "changed_files_any"), _list(two, "changed_files_none")
        if any_ is not None and none_ is not None and any_ & none_:
            return True
    return False


def closure_ok(root=None) -> bool:
    """P16: `check-closure.py --check closure` exits 0. It starts no Agda process."""
    root = ROOT if root is None else Path(root)
    try:
        done = subprocess.run([sys.executable, str(CLOSURE), "--check", "closure"],
                              cwd=root, capture_output=True, text=True)
    except OSError:
        return False
    return done.returncode == 0


def p22_readmes(text: str, root=None) -> list[str]:
    """P22: the `README.md` of every directory the write scope names, when one exists.

    IT PRINTS AND IT NEVER REFUSES. The pre-flight prints the paths that cover the write
    scope, so a worker meets a per-directory README before it writes. This file restates
    none of their content.
    """
    root = ROOT if root is None else Path(root)
    out = []
    for p in scope_paths(text):
        d = (root / _non_glob_prefix(p))
        d = d if d.is_dir() else d.parent
        cand = d / "README.md"
        rel = str(cand)[len(str(root)) + 1:]
        if cand.is_file() and rel not in out:
            out.append(rel)
    return out


# ---------------------------------------------------------------- P23's two fixed forms


def _src_files(root):
    root = ROOT if root is None else Path(root)
    src = root / "src"
    if not src.is_dir():
        return
    for p in src.rglob("*"):
        if p.is_file():
            yield p


def dependent_count(module: str, root=None) -> int:
    """Files under `src/` (never `archive/src/`) whose text names `import <module>`.

    Mirrors `grep -rl "import <module>" src/ | wc -l` in pure Python. P23's fixed forms
    never shell out and never eval a brief's text: the brief supplies only `module`, a
    dotted name, and this function does the counting itself.

    MEASURED 2026-08-25: `L.Constructible` has 71 and heap-walled HEAVY warm at a
    landing that added ten lines and zero new imports; `L.StageCardinal` has 2 and
    landed inside a fifth of WIDE's cap. Import-edge count, what `[LJ-1.625]` sited
    four rows by, predicted neither.
    """
    needle = f"import {module}"
    n = 0
    for p in _src_files(root):
        try:
            text = p.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if needle in text:
            n += 1
    return n


def supply_count(token: str, root=None) -> int:
    """Matching lines for `token`, summed across every file under `src/`.

    Mirrors `grep -rc <token> src/`, summed to one number. The companion to
    `dependent_count()`: it asks whether the tree already supplies the object a brief
    is about to fund the construction of, before it funds it. `[LJ-1.560]`'s obligation
    turned out to be an instantiation of something already present; this is the check
    that would have found it before the dispatch, not after.
    """
    n = 0
    for p in _src_files(root):
        try:
            text = p.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        n += sum(1 for line in text.split("\n") if token in line)
    return n


# ---------------------------------------------------------------- the pre-flight


def preflight(brief, root=None, show=True, closure=None, slots=None):
    """P1 to P22 over one brief. It returns a LIST of refusal strings, empty on a pass.

    Each string starts with its check id, so rule (f) reads `d[0].split()[0]` and parks
    with `reason: "preflight:<id>"`. The list is ORDERED by check id, so the first entry
    names the earliest defect and the whole list goes into `detail`.
    """
    root = ROOT if root is None else Path(root)
    d: list[str] = []
    path = Path(brief) if brief else None
    text = ""
    if path is None or not path.is_file():
        return ["P1 no brief, no branch block, or more than one"]
    try:
        # `errors="replace"` and not a raise: a brief that is not UTF-8 has no branch
        # block a decoder can find, so P1 refuses it. A `UnicodeDecodeError` here would
        # instead stop the loop before any check ran.
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ["P1 no brief, no branch block, or more than one"]

    # P1. Exactly one fenced block carries the info string `toml pod-branches`.
    found = table.BRANCH_FENCE.findall(text)
    if len(found) != 1:
        d.append("P1 no brief, no branch block, or more than one")
        block = None
    else:
        block = found[0]

    # P2. The block parses. P3. The branch list is non-empty.
    branches: list[dict] = []
    if block is not None:
        try:
            data = tomllib.loads(block)
        except tomllib.TOMLDecodeError:
            d.append("P2 branch block does not parse")
            data = None
        if data is not None:
            got = data.get("branch")
            if not isinstance(got, list) or not got:
                d.append("P3 branch set is empty")
            else:
                branches = [b for b in got if isinstance(b, dict)]

    def bid(n, b):
        return str(b.get("id", f"<{n}>"))

    # P4. Every `when` key is in the closed list. AMENDED BY A10: fact 7's keys are in it.
    for n, b in enumerate(branches, 1):
        when = b.get("when")
        if not isinstance(when, dict) or not when:
            d.append(f"P4 branch {bid(n, b)} matches on <none>")
            continue
        for k in when:
            if k not in table.WHEN_TYPES:
                d.append(f"P4 branch {bid(n, b)} matches on {k}")

    # P5. Every `error_class` value is one of the eleven.
    for n, b in enumerate(branches, 1):
        when = b.get("when") if isinstance(b.get("when"), dict) else {}
        vals = []
        if "error_class" in when:
            vals.append(when["error_class"])
        if isinstance(when.get("error_class_in"), list):
            vals += list(when["error_class_in"])
        for v in vals:
            if v not in facts.ERROR_CLASSES:
                d.append(f"P5 branch {bid(n, b)} names class {v}")

    # P6. Every `action` is one of the eight.
    for n, b in enumerate(branches, 1):
        if b.get("action") not in table.ACTIONS:
            d.append(f"P6 branch {bid(n, b)} names action {b.get('action', '<none>')}")

    # P7. A unique brief-local id, a priority, and no two branches share a priority.
    seen_id, seen_pri = set(), {}
    for n, b in enumerate(branches, 1):
        name = bid(n, b)
        if "id" not in b or name in seen_id:
            d.append(f"P7 branch {name} is a duplicate")
        seen_id.add(name)
        pri = b.get("priority")
        if not isinstance(pri, int) or isinstance(pri, bool):
            d.append(f"P7 branch {name} is a duplicate")
        elif pri in seen_pri:
            d.append(f"P7 branch {name} is a duplicate")
        else:
            seen_pri[pri] = name

    # P8. Every path in `changed_files_*` and under `## SCOPE (write)` resolves.
    for n, b in enumerate(branches, 1):
        when = b.get("when") if isinstance(b.get("when"), dict) else {}
        for k in ("changed_files_any", "changed_files_none", "changed_files_all_within"):
            for p in when.get(k, []) if isinstance(when.get(k), list) else []:
                if not isinstance(p, str) or not path_resolves(p, root):
                    d.append(f"P8 branch {bid(n, b)} names {p}")
    for p in scope_paths(text):
        # The scope is not a branch, so the id slot carries the word `scope`. The refusal
        # string of section 6.5 is otherwise unchanged.
        if not path_resolves(p, root):
            d.append(f"P8 branch scope names {p}")

    # P9. One branch or more can finish the task.
    if branches and not any(b.get("action") == "done" for b in branches):
        d.append("P9 no branch can finish this task")

    # P10. No two branches have an identical `when` block.
    def frozen(when):
        return tuple(sorted((k, tuple(v) if isinstance(v, list) else v)
                            for k, v in when.items()))
    for i, a in enumerate(branches):
        for b in branches[i + 1:]:
            wa = a.get("when") if isinstance(a.get("when"), dict) else None
            wb = b.get("when") if isinstance(b.get("when"), dict) else None
            if wa and wb and frozen(wa) == frozen(wb):
                d.append(f"P10 branches {a.get('id')} and {b.get('id')} are identical")

    # P11. The head slot names one of the five, and `head_slot` is present exactly when
    # the action is `escalate`. SECTION 4.2 RULES BOTH DIRECTIONS and `table.check_row()`
    # refuses both; testing one let a brief park with `reason: "admission"` instead.
    try:
        legal = table.head_slots(root) if slots is None else tuple(slots)
    except table.TableError:
        # `heads.toml` is unreadable. That is not a defect of this brief, and it is still
        # a refusal: nothing can resolve a slot, so nothing may be dispatched. One line
        # goes out, and the per-branch tests are skipped rather than made up.
        legal = None
        d.append("P11 head slot <none> is not in heads.toml")
    if legal is not None:
        declared = head_field(text, "head_slot")
        if declared is None or declared not in legal:
            d.append(f"P11 head slot {declared or '<none>'} is not in heads.toml")
        for b in branches:
            act = b.get("action")
            if act == "escalate" and "head_slot" not in b:
                d.append("P11 head slot <none> is not in heads.toml")
            elif "head_slot" not in b:
                continue
            elif b["head_slot"] not in legal:
                d.append(f"P11 head slot {b['head_slot']} is not in heads.toml")
            elif act != "escalate":
                # THE SECOND DIRECTION. Section 6.5 writes no message for it, and its one
                # message would be false here: the slot IS in heads.toml.
                d.append(f"P11 head slot {b['head_slot']} is not admitted on a "
                         f"{act if act is not None else '<none>'} branch")

    # P12. The heading code equals the directory name, mapped.
    code = brief_code(text)
    if code is None or agents_tree.normalise(code) != agents_tree.normalise(
            path.parent.name):
        d.append("P12 brief code and directory disagree")

    # P13. The `machine:` line reads `exclusive` or `shared`.
    if head_field(text, "machine") not in ("exclusive", "shared"):
        d.append("P13 machine class is missing")

    # P14. `obligations` is non-empty and every entry is `<probe path>::<dotted name>`.
    # THE FIELD IS AUTHOR-WRITTEN TOML, so it can hold anything TOML can hold. A
    # non-string entry reached `parse_obligation()` and raised `AttributeError` on
    # `.count`, which is a traceback in the unattended loop and not a refusal.
    try:
        obligations = witness.obligations_of(path)
    except (tomllib.TOMLDecodeError, OSError, KeyError, TypeError, ValueError):
        obligations = []
    if not isinstance(obligations, list):
        obligations = []
    if not obligations:
        d.append("P14 obligation 1 is empty or malformed")
    for n, entry in enumerate(obligations, 1):
        if not isinstance(entry, str):
            d.append(f"P14 obligation {n} is empty or malformed")
            continue
        try:
            probe, _ = witness.parse_obligation(entry)
        except witness.DerivationError:
            d.append(f"P14 obligation {n} is empty or malformed")
            continue
        if not path_under_root(probe, root):
            d.append(f"P14 obligation {n} is empty or malformed")

    # P15. `## ARCHIVE` and `## LITERATURE` are present and every path in them resolves.
    for name in ("ARCHIVE", "LITERATURE"):
        body = section(text, name)
        if body is None or not body.strip():
            d.append("P15 injected block missing or dead path")
            continue
        for m in PATH_TOKEN.finditer(body):
            if not (root / _non_glob_prefix(m.group(1))).exists():
                d.append("P15 injected block missing or dead path")

    # P16. The tree was closed before this task started.
    ok = closure_ok(root) if closure is None else bool(closure)
    if not ok:
        d.append("P16 the tree was already open before this task")

    # P17. `## PREMISES` is non-empty and every basis `file:line` resolves.
    premises = units(section(text, "PREMISES") or "")
    if not premises:
        d.append("P17 premise 1 has no live basis")
    for n, u in enumerate(premises, 1):
        hits = BASIS.findall(u)
        if not hits:
            d.append(f"P17 premise {n} has no live basis")
            continue
        for fname, first, _last in hits:
            target = root / fname
            if not target.is_file():
                d.append(f"P17 premise {n} has no live basis")
                break
            count = len(target.read_text(encoding="utf-8", errors="replace").split("\n"))
            if int(first) < 1 or int(first) > count:
                d.append(f"P17 premise {n} has no live basis")
                break

    # P18. One branch or more attacks this return.
    if not any(b.get("action") == "escalate"
               and b.get("head_slot") == "mathematician_adversarial" for b in branches):
        d.append("P18 nothing can attack this return")

    # P19. Every `done` branch carries an outcome and cannot close on no work. A6.
    need = -len(obligations)
    for n, b in enumerate(branches, 1):
        if b.get("action") != "done":
            continue
        when = b.get("when") if isinstance(b.get("when"), dict) else {}
        cap = when.get("obligations_delta_max")
        by_delta = isinstance(cap, int) and not isinstance(cap, bool) and cap <= need
        by_outcome = b.get("outcome") == "no-go"
        if "outcome" not in b or not (by_delta or by_outcome):
            d.append(f"P19 branch {bid(n, b)} can close on no work")

    # P20. No branch that is not `done` may be satisfiable together with a `done` branch
    # it OUTRANKS. Otherwise the `done` branch is dead code and `attempt_max` parks the
    # task instead of closing it.
    for a in branches:
        if a.get("action") == "done":
            continue
        for b in branches:
            if b.get("action") != "done" or not outranks(a, b):
                continue
            wa = a.get("when") if isinstance(a.get("when"), dict) else {}
            wb = b.get("when") if isinstance(b.get("when"), dict) else {}
            if not contradicts(wa, wb):
                d.append(f"P20 branch {a.get('id')} shadows done branch {b.get('id')}")

    # P21. The LAWS bundle is present and non-empty. R17.
    laws = section(text, "LAWS")
    if laws is None or not laws.strip():
        d.append("P21 the LAWS bundle is absent or empty")

    # P22. It prints and it never refuses.
    if show:
        for rel in p22_readmes(text, root):
            print(f"P22 read {rel}")

    # P23. `## MEASURED TODAY` re-verifies a claimed dependent count or supply count
    # against the CURRENT tree, when the brief touches `src/` or declares HEAVY. Owner's
    # ruling 2026-08-25. It RE-RUNS the measurement rather than checking a section
    # exists: P15 is satisfied by a heading and truthful text ("ARCHIVE USED: NO HIT"),
    # because ARCHIVE and LITERATURE point backward and outward and neither one names
    # the tree's CURRENT shape. `dev/pod/instructions/mathematician.md`'s own clause
    # already binds the two greps; this makes paying them checkable rather than only
    # asked for. MEASURED cost of not having it: five landing attempts against one cap
    # a single direct measurement of `src/Everything.lagda.md` exposed (`[LJ-1.628]`).
    if any(p.startswith("src/") for p in scope_paths(text)) \
            or (head_field(text, "agda_tier") or "").strip().lower() == "heavy":
        measured = section(text, "MEASURED TODAY")
        if measured is None or not measured.strip():
            d.append("P23 no `## MEASURED TODAY` section, and this brief touches "
                      "src/ or declares agda_tier: heavy")
        else:
            seen_kinds = set()
            for u in units(measured):
                m = MEASURED_LINE.match(u)
                if m is None:
                    d.append("P23 a `## MEASURED TODAY` line does not parse as "
                             f"`- <dependents|supply>: <arg> => <number>`: {u!r}")
                    continue
                kind, arg, claimed = m.group(1), m.group(2), int(m.group(3))
                seen_kinds.add(kind)
                actual = (dependent_count(arg, root) if kind == "dependents"
                          else supply_count(arg, root))
                if actual != claimed:
                    d.append(f"P23 {kind} {arg!r} claimed {claimed}, measured "
                             f"{actual} just now")
            for kind in ("dependents", "supply"):
                if kind not in seen_kinds:
                    d.append(f"P23 `## MEASURED TODAY` carries no {kind} line, and "
                             "both are mandatory")
    return d


def main(argv):
    if len(argv) < 2 or argv[0] != "--brief":
        print(__doc__)
        return 2
    quiet = "-q" in argv or "--quiet" in argv
    d = preflight(argv[1], show=not quiet)
    if not quiet:
        for line in d:
            print(line)
        if not d:
            print(f"{argv[1]}: 23 checks, no refusal")
    return 1 if d else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
