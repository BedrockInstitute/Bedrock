#!/usr/bin/env python3
"""Fact 3, the witness meter of amendments A1 and A4. It DERIVES a witness and never
authors one.

WHAT FACT 3 IS. "The change in the count of UNRESOLVED names on the task's own declared
obligation list." The brief writes one field per obligation, and this module derives the
four parts of the witness module that decides whether the name resolves.

WHY THE AMENDMENT WAS NEEDED, and it is measured
(`dev/memos/LJ-4-pod-program-design.md` section 4.7). `scan()` at
`scripts/measure/obligations.py:112` counts signatures, which are DISCHARGED obligations,
so the count RISES when a task lands work. Reconstructed over every task code whose commit
touched a master: 63 codes, delta min -18, median +22 and 45 positive. That caliber would
have failed 45 of the last 63 real landings. The three other proposals were refuted too:
metas plus postulates plus holes are all zero on this tree today, and the module telescope
count is a whole-tree proxy that work landed elsewhere moves.

FOUR MEASURED RULES, AND EACH OF THE FOUR WOULD HAVE SHIPPED A BROKEN METER:

- **The term-reference form is mandatory.** `open <probe> using ( <name> )` does NOT fail
  on an absent name. Agda returns EXIT 0 and prints only
  `warning: -W[no]ModuleDoesntExport`, so every NO-GO would read as a PASS.
  `witness = Target.<dotted-name>` returns exit 42 with `error: [NotInScope]`.
- **One witness per obligation.** Agda stops at the FIRST unresolved name. A combined
  witness over three obligations, two of them absent, named only one. A combined witness
  is a valid fast path WHEN IT RETURNS EXIT 0, because that proves every name present in
  one run, and this module uses it exactly that way: one grouped run per probe, then a
  run per obligation as soon as the grouped run is not green.
- **PROBE RED is common, not rare, so it needs its own value.** `[NotInScope]` also fires
  INSIDE a red probe, measured at `agents/tasks/LJ-1-286/ProbeLJ1286A.agda:30` and
  `agents/tasks/LJ-1-280/ReRun.agda:66`. A meter that greps the tag anywhere in the output
  reports a red probe as a missing obligation, so the rule anchors on the file path in the
  error's location line. 6 of 30 sampled live probes do not typecheck today.
- **`--safe` is a free guarantee, so every witness carries it.** A witness with `--safe`
  REFUSES a probe without one: `error: [CoInfectiveImport]`, exit 42, so a probe cannot
  discharge an obligation with a postulate. The cost is stated: 8 of the 389 live tracked
  probes declare no `--safe`, and an obligation inside one reads PROBE RED for ever.

THE NAME FORM IS NECESSARY AND NOT A CONVENIENCE. Measured over the live tracked probes:
389 files, of which 341 are directory-qualified, 340 take parameters and 294 are both. A
bare declaration name never resolves. `Probe383` exports no value declaration at its own
top level: its obligations sit inside a SECOND parameterised module, and the witness
reaches `Wire.residue2-false-at-record` WITHOUT discharging `Wire`'s eight parameters,
because a qualified reference into a parameterised submodule is a legal term.

THE PRICE, measured on 2026-08-17 with a warm interface cache and one Agda process at a
time: one obligation costs a median of 1.3 s, p90 2.8 s and a minimum of 0.7 s, and 60
runs cost 200.5 s. The worst single warm run measured 49.4 s. COLD CACHE IS NOT MEASURED
AND THIS FILE DOES NOT BOUND IT.

Usage:
  witness.py <path>::<dotted-name> [...]   meter one obligation or more
  witness.py --brief <brief.md>            meter every obligation the brief declares
  Options: --code <CODE>  --deadline <seconds>  --show (print the derived witness)
           --keep (leave the witness file in place; the default keeps it too)
Exit status: 0 every obligation resolved, 1 one or more UNRESOLVED or `agda` could not
start, 2 usage error, which includes an unreadable or malformed brief.
"""

from __future__ import annotations

import hashlib
import re
import sys
import tomllib
from pathlib import Path

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

ROOT = find_root(__file__)

# Section 4.7.5. The witness home sits outside the index and inside `.gitignore`, so
# neither fact 4 nor `check-probes.py` sees it.
WITNESS_DIR = ".pod-state/witness"

# Section 4.7.3. Term 1 is the directory that holds the witness. Terms 2 and 3 are the two
# include roots of `bedrock.agda-lib`, which reads `include: src agents/tasks`, and the
# probe's qualified name resolves against the second. The POD runs with `cwd` at the
# repository root, so three terms are enough: MEASURED with `cwd=/`, the run fails with
# `[FileNotFound]` in 0.1 s.
INCLUDE = (WITNESS_DIR, "src", "agents/tasks")

# `dev/pod/heads.toml [limits] agda_deadline_s` is the ONE home of this number once day 2
# lands its loader. The default below is that file's value, and every caller may pass its
# own. This module never reads a second configuration file.
DEADLINE_S = 1800

FENCE = re.compile(r"```agda\n(.*?)```", re.S)
OPTIONS = re.compile(r"\{-#\s+OPTIONS\b(?P<flags>[^#]*)#-\}")
OBLIGATIONS = re.compile(r"^[ \t]*obligations\s*=\s*(\[[^\]]*\])", re.M | re.S)
WHERE = re.compile(r"(?<![^\s(){}])where(?![^\s(){}])")
COMMENT = re.compile(r"--(?![^\s]).*$|--$", re.M)

# The four values of the pass rule, section 4.7.4. PASS is the only resolved one.
PASS, MISSING, PROBE_RED, NO_FILE = "pass", "missing", "probe-red", "no-file"


class DerivationError(ValueError):
    """The derivation cannot express this obligation, so nothing is run.

    Cost one of the disclosed departure in section 4.7.2: the derivation copies only the
    lines ABOVE the module header, so it cannot express an obligation whose telescope
    types are introduced below that header.

    IT IS A `ValueError` ON PURPOSE. Pre-flight P14 at `scripts/pod/preflight.py:485`
    already wraps `obligations_of()` in `except (TOMLDecodeError, OSError, KeyError,
    TypeError, ValueError)`, so every refusal this module raises out of that call reaches
    an existing handler and P14 reports `obligation 1 is empty or malformed` instead of
    ending the tick with a traceback.
    """


def parse_obligation(entry: str) -> tuple[str, str]:
    """`<probe-path>::<dotted-name>`. The grammar of section 4.7.1, and nothing else.

    Pre-flight P14 refuses a malformed entry before any dispatch, so a raise here means
    the brief reached the meter without its pre-flight.
    """
    if not isinstance(entry, str):
        # THE FIELD IS AUTHOR-WRITTEN TOML, so it holds anything TOML holds. A non-string
        # entry used to reach `.count` and raise `AttributeError`, which is a traceback in
        # the unattended loop and not a refusal.
        raise DerivationError(f"obligation {entry!r} is not a string")
    if entry.count("::") != 1:
        raise DerivationError(f"obligation `{entry}` is not <path>::<dotted-name>")
    path, dotted = (s.strip() for s in entry.split("::"))
    if not path or not dotted:
        raise DerivationError(f"obligation `{entry}` has an empty half")
    if not re.fullmatch(r"[^\s.]+(\.[^\s.]+)*", dotted):
        raise DerivationError(f"obligation `{entry}` has no dotted name")
    return path, dotted


def probe_code(path: Path) -> str:
    """The Agda code of a probe. A `.lagda.md` probe gives its fences, joined.

    The design's grammar names a `.agda` probe. A task directory also holds literate
    files, and a literate preamble copied verbatim would put Markdown prose into the
    witness, so the fences are extracted first. Nothing else changes.

    A PATH THAT WILL NOT READ IS A REFUSAL, never a traceback. `measure()` below turns
    every `DerivationError` into a PROBE RED row, so the name stays UNRESOLVED and the
    tick continues. Before this, an obligation whose probe path named a DIRECTORY raised
    `IsADirectoryError` here and stopped the loop.
    """
    try:
        text = Path(path).read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        raise DerivationError(f"cannot read the probe {path}: {exc}") from exc
    if str(path).endswith(".lagda.md"):
        return "\n".join(FENCE.findall(text))
    return text


def split_header(code: str) -> tuple[str, str, str]:
    """Steps 1 and 2 of the derivation: (preamble, module name, telescope).

    Step 1 copies every line ABOVE the top-level module header, verbatim, which puts the
    telescope's own types in scope. Step 2 reads the module header, joining lines until
    `where`.
    """
    lines = code.split("\n")
    start = next((n for n, l in enumerate(lines) if l.startswith("module ")), None)
    if start is None:
        raise DerivationError("no top-level module header")
    header, end = "", None
    for n in range(start, len(lines)):
        header = header + ("\n" if header else "") + lines[n]
        if WHERE.search(COMMENT.sub("", header)):
            end = n
            break
    if end is None:
        raise DerivationError("the module header never reaches `where`")
    stripped = COMMENT.sub("", header)
    m = re.match(r"module\s+(\S+)", stripped)
    if m is None:
        raise DerivationError("the module header names no module")
    body = stripped[m.end():]
    cut = WHERE.search(body)
    telescope = body[:cut.start()].strip()
    return "\n".join(lines[:start]).rstrip(), m.group(1), telescope


def binder_application(telescope: str) -> str:
    """Step 3: the application. A `{ }` name is wrapped in braces, a `( )` name is bare.

    The derivation never reads a type, so telescope shape does not bound it: the 389 live
    probes use only 11 distinct telescopes, 295 of them exactly
    `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))`.
    """
    out, i, n = [], 0, len(telescope)
    while i < n:
        ch = telescope[i]
        if ch.isspace():
            i += 1
            continue
        if ch not in "({":
            raise DerivationError(f"telescope holds a bare binder near `{telescope[i:i + 20]}`")
        instance = ch == "{" and telescope[i + 1:i + 2] == "{"
        close = ")" if ch == "(" else "}"
        depth, j = 0, i
        while j < n:
            if telescope[j] in "({":
                depth += 1
            elif telescope[j] in ")}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if depth != 0:
            raise DerivationError("the telescope brackets do not balance")
        inner = telescope[i + 1:j]
        if instance:
            inner = inner.strip()[1:-1]
        head = _names_before_colon(inner)
        for name in head:
            out.append("{{" + name + "}}" if instance
                       else ("{" + name + "}" if ch == "{" else name))
        i = j + 1
    return " ".join(out)


def _names_before_colon(inner: str) -> list[str]:
    """The binder names of one group: the tokens before its top-level `:`."""
    depth = 0
    for k, c in enumerate(inner):
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
        elif c == ":" and depth == 0:
            return inner[:k].split()
    raise DerivationError(f"binder group `{inner.strip()[:30]}` has no `:`")


def ensure_safe(preamble: str) -> str:
    """One added rule: the witness OPTIONS line ALWAYS carries `--safe` (section 4.7.4).

    A probe that declares no OPTIONS pragma gets one that carries `--safe` and no other
    flag. No flag is invented for it: an inherited `--cubical` this file did not read
    would be a guess.
    """
    m = OPTIONS.search(preamble)
    if m is None:
        return "{-# OPTIONS --safe #-}\n" + preamble
    if "--safe" in m.group("flags"):
        return preamble
    flags = m.group("flags").rstrip() + " --safe "
    return preamble[:m.start()] + "{-# OPTIONS" + flags + "#-}" + preamble[m.end():]


def witness_source(probe_path, dotted_names, module_name: str) -> str:
    """The whole derivation, steps 1 to 4, with no authored line anywhere.

    Step 4 writes `witness = Target.<dotted-name>`. A grouped witness numbers the names
    `witness0`, `witness1`, and so on, so one run references every one of them.
    """
    preamble, probe_module, telescope = split_header(probe_code(probe_path))
    application = binder_application(telescope)
    head = ensure_safe(preamble)
    header = " ".join(x for x in ("module", module_name, telescope, "where") if x)
    body = [header,
            "",
            f"import {probe_module}",
            f"module Target = {probe_module} {application}".rstrip(),
            ""]
    if len(dotted_names) == 1:
        body.append(f"witness = Target.{dotted_names[0]}")
    else:
        for k, dotted in enumerate(dotted_names):
            body.append(f"witness{k} = Target.{dotted}")
    return head.rstrip() + "\n\n" + "\n".join(body) + "\n"


def witness_name(code, key: str) -> str:
    """A stable file name per obligation, so the two measurement points reuse one file.

    The name is an Agda module name and the file name must equal it, so the digest of the
    obligation carries the uniqueness and the task code carries the readability.
    """
    digest = hashlib.sha1(key.encode("utf-8")).hexdigest()[:8]
    stem = agents_tree.normalise(code) if code else "POD"
    stem = re.sub(r"[^A-Za-z0-9-]", "-", stem)
    return f"Witness-{stem}-{digest}"


def write_witness(source: str, module_name: str, root=None) -> Path:
    root = ROOT if root is None else Path(root)
    home = root / WITNESS_DIR
    home.mkdir(parents=True, exist_ok=True)
    path = home / (module_name + ".agda")
    path.write_text(source, encoding="utf-8")
    return path


def verdict(result, witness_path, root=None) -> tuple[str, str]:
    """The pass rule of section 4.7.4, keyed on what Agda really reports.

    | PASS      | exit 0                                                          |
    | MISSING   | exit 42 AND `[NotInScope]` whose file group IS the witness file  |
    | PROBE RED | exit 42 with any other tag, or `[NotInScope]` somewhere else     |

    The `file` group is the one `facts.ERR` already captures, so the meter adds no parser.

    DISCLOSED READING, because section 4.7.4 does not rule it. A heap wall, a deadline and
    any other exit code are none of the three rows above. They are counted PROBE RED, so
    the name stays UNRESOLVED and the flag says the probe could not be metered. The
    alternative, counting them resolved, would let a heap wall close a `go` branch.
    """
    rc, out = result["rc"], result["out"]
    if rc == 0:
        return PASS, ""
    want = Path(witness_path).resolve()
    root = ROOT if root is None else Path(root)
    if rc == 42:
        for m in facts.ERR.finditer(out):
            if m.group("cls") != "NotInScope":
                continue
            where = m.group("file")
            if where is None:
                continue
            here = Path(where) if Path(where).is_absolute() else (root / where)
            if here.resolve() == want:
                return MISSING, f"[NotInScope] at {where}:{m.group('line')}"
        return PROBE_RED, "exit 42 inside the probe: " + ", ".join(
            result["error_names_all"][:4] or ["no bracketed name"])
    if result["heap_wall"]:
        return PROBE_RED, "heap wall at " + result["caliber"]
    if rc is None:
        return PROBE_RED, "deadline passed"
    return PROBE_RED, f"exit {rc}"


def _run(probe_path, dotted_names, code, root, deadline_s, slots):
    """One witness run over one probe: derive, write, start Agda, read the verdict."""
    key = str(probe_path) + "::" + "::".join(dotted_names)
    name = witness_name(code, key)
    source = witness_source(root / probe_path, dotted_names, name)
    path = write_witness(source, name, root)
    rel = str(path.relative_to(root))
    result = facts.run_agda(rel, root, deadline_s, slots, include=INCLUDE)
    value, detail = verdict(result, path, root)
    return {"witness": rel, "source": source, "rc": result["rc"],
            "seconds": result["seconds"], "value": value, "detail": detail,
            "error_names_all": result["error_names_all"]}


def measure(obligations, code=None, root=None, deadline_s=DEADLINE_S, slots=None):
    """Meter one obligation list at ONE measurement point.

    Returns the UNRESOLVED count, the wall seconds of every witness run, the probe-red
    flag and one row per obligation. The witness runs are NOT part of fact 5: section
    4.3.1 excludes them and the record carries them as `witness_seconds`, so a longer
    obligation list can never read as a slower proof.

    IT NEVER RAISES ON A BAD OBLIGATION LIST. Every malformed entry becomes a row, and an
    unresolved row is the strict direction: it can only stop a `go` branch closing, never
    open one.
    """
    root = ROOT if root is None else Path(root)
    if slots is None:
        slots = facts.slots()
    if not isinstance(obligations, (list, tuple)):
        raise DerivationError(f"the obligation list is {type(obligations).__name__}, "
                              f"not a list")
    rows, seconds = {}, 0.0

    # The key of `rows` is the brief's own string, never a reconstructed one, so an entry
    # written with spaces around `::` still reaches the count. A NON-STRING entry has no
    # such name and is keyed by its `repr`, because a TOML author may write a list, which
    # is not hashable and cannot be a key at all.
    keys, groups = [], {}
    for entry in obligations:
        key = entry if isinstance(entry, str) else repr(entry)
        keys.append(key)
        try:
            path, dotted = parse_obligation(entry)
        except DerivationError as exc:
            rows[key] = {"value": PROBE_RED, "detail": str(exc), "rc": None,
                         "seconds": 0.0, "witness": None}
            continue
        if not (root / path).is_file():
            # NO FILE: no probe file at that path, so NO PROCESS STARTS. `is_file()` and
            # not `exists()`: a path that names a DIRECTORY passed `exists()`, reached
            # `probe_code()` and raised `IsADirectoryError` into the tick.
            why = "is a directory, not a probe file" if (root / path).is_dir() \
                else "does not exist"
            rows[key] = {"value": NO_FILE, "detail": f"{path} {why}",
                         "rc": None, "seconds": 0.0, "witness": None}
            continue
        groups.setdefault(path, []).append((key, dotted))

    for path, pairs in groups.items():
        entries = [e for e, _ in pairs]
        names = [d for _, d in pairs]
        if len(names) > 1:
            # THE FAST PATH, and it is only ever a fast path: exit 0 proves every name in
            # this probe present in one run. Anything else falls through to one run per
            # obligation, because Agda stops at the FIRST unresolved name.
            try:
                grouped = _run(path, names, code, root, deadline_s, slots)
            except DerivationError as exc:
                for entry in entries:
                    rows[entry] = {"value": PROBE_RED, "detail": str(exc), "rc": None,
                                   "seconds": 0.0, "witness": None}
                continue
            seconds += grouped["seconds"]
            if grouped["value"] == PASS:
                for entry in entries:
                    rows[entry] = dict(grouped, detail="grouped run, exit 0")
                continue
        for entry, dotted in zip(entries, names):
            try:
                rows[entry] = _run(path, [dotted], code, root, deadline_s, slots)
            except DerivationError as exc:
                rows[entry] = {"value": PROBE_RED, "detail": str(exc), "rc": None,
                               "seconds": 0.0, "witness": None}
                continue
            seconds += rows[entry]["seconds"]

    ordered = [dict(rows[k], obligation=k) for k in keys if k in rows]
    unresolved = sum(1 for r in ordered if r["value"] != PASS)
    red = any(r["value"] == PROBE_RED for r in ordered)
    return {"unresolved": unresolved, "witness_seconds": round(seconds, 2),
            "probe_red": red, "rows": ordered}


def obligations_of(brief) -> list[str]:
    """The `obligations = [...]` field of one brief, under `## OBLIGATION NAMES`.

    The value is parsed with `tomllib` and never with a hand-written string reader, so the
    brief and the pre-flight read one syntax.

    THREE REFUSALS, and none of them is an empty list. A brief that cannot be read, a
    field that is not TOML, and a field whose value is not a list are all DEFECTS in the
    brief. Returning `[]` for any of them would state that the brief declares no
    obligation, which is a fact nothing measured, and pre-flight P14 would then report the
    wrong defect. `DerivationError` is a `ValueError`, which P14 already catches.
    """
    try:
        text = Path(brief).read_text(encoding="utf-8")
    except OSError as exc:
        raise DerivationError(f"cannot read the brief {brief}: {exc}") from exc
    m = OBLIGATIONS.search(text)
    if m is None:
        return []
    try:
        value = tomllib.loads("obligations = " + m.group(1))["obligations"]
    except tomllib.TOMLDecodeError as exc:
        raise DerivationError(f"the obligations field of {brief} is not TOML: "
                              f"{exc}") from exc
    if not isinstance(value, list):
        raise DerivationError(f"the obligations field of {brief} is a "
                              f"{type(value).__name__}, not a list")
    return value


def _obligations_of_task(t) -> list[str]:
    """The task's own declared list: the state file's copy first, then the brief.

    A DECLARED VALUE THAT IS NOT A LIST FALLS THROUGH TO THE BRIEF. The state file is
    written by the program, but it is also hand-editable, and `list(5)` is a `TypeError`
    inside the tick.
    """
    declared = getattr(t, "obligations", None)
    if declared and isinstance(declared, (list, tuple)):
        return list(declared)
    brief = getattr(t, "brief", None)
    return obligations_of(brief) if brief else []


def witness_unresolved(t) -> int:
    """The DISPATCH-point half of fact 3, called by rule (f) of the tick.

    It runs the meter over the brief's obligation list and returns the UNRESOLVED count
    into `obl_before`. `witness_delta()` subtracts it at exit. It costs the price of
    section 4.7.5 once per dispatch, and rule (f) pays it a second time at the return.
    """
    return measure(_obligations_of_task(t), code=getattr(t, "code", None))["unresolved"]


def witness_delta(t) -> tuple[int, float, bool]:
    """The EXIT half of fact 3: (delta, witness seconds, probe red).

    Fact 3 is the UNRESOLVED count at exit minus the UNRESOLVED count at dispatch. A task
    that discharges two names gives -2. A task that writes nothing gives 0, because NO
    FILE holds at both ends.
    """
    m = measure(_obligations_of_task(t), code=getattr(t, "code", None))
    before = getattr(t, "obl_before", None)
    if before is None:
        raise ValueError("witness_delta: the task carries no obl_before, so fact 3 has no "
                         "dispatch point. R7 applies: drop the return, never guess a fact")
    return m["unresolved"] - before, m["witness_seconds"], m["probe_red"]


def _usage(message: str) -> int:
    """One refusal shape for the command line: the reason, then the contract. Exit 2.

    EVERY USAGE ERROR PRINTS WHY. `--deadline abc` used to reach `float()` and end in a
    `ValueError` traceback, which reads as a broken tool rather than a wrong flag. It
    prints the `Usage:` block and not the whole module docstring, because 60 lines of
    measured rules bury the one line that says what to type.
    """
    print(f"witness: REFUSED. {message}", file=sys.stderr)
    print(__doc__[__doc__.index("Usage:"):], file=sys.stderr)
    return 2


def main(argv: list[str]) -> int:
    args, code, deadline, show = list(argv[1:]), None, DEADLINE_S, False
    entries: list[str] = []
    while args:
        a = args.pop(0)
        if a in ("--code", "--deadline", "--brief") and not args:
            return _usage(f"{a} takes a value")
        if a == "--code":
            code = args.pop(0)
        elif a == "--deadline":
            raw = args.pop(0)
            try:
                deadline = float(raw)
            except ValueError:
                return _usage(f"--deadline {raw!r} is not a number of seconds")
            if deadline <= 0:
                return _usage(f"--deadline {raw} is not above zero")
        elif a == "--show":
            show = True
        elif a == "--keep":
            pass                        # the witness file is always kept; see 4.7.5
        elif a == "--brief":
            brief = args.pop(0)
            try:
                entries += obligations_of(brief)
            except DerivationError as exc:
                return _usage(str(exc))
        elif a.startswith("-"):
            return _usage(f"unknown option {a}")
        else:
            entries.append(a)
    if not entries:
        return _usage("name one obligation, or a brief that declares one")
    try:
        m = measure(entries, code=code, deadline_s=deadline)
    except facts.AgdaStartError as exc:
        print(f"witness: FAILED. {exc}", file=sys.stderr)
        return 1
    for r in m["rows"]:
        if show and r.get("source"):
            print("--- " + str(r.get("witness")))
            print(r["source"])
        print(f"{r['value']:<9} exit={r['rc']!s:<5} {r['seconds']:>7.2f}s  "
              f"{r['obligation']}" + (f"  ({r['detail']})" if r["detail"] else ""))
    print(f"witness: {m['unresolved']} UNRESOLVED of {len(m['rows'])}, "
          f"{m['witness_seconds']:.2f} s, probe_red={m['probe_red']}")
    return 1 if m["unresolved"] else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
