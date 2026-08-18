#!/usr/bin/env python3
"""The spec surface gate: R9 over the trophy statement, R16 over the rule homes.

Design: `dev/memos/L9-pod-program-design.md` section 7.3 (AD22), wired by
section 5.4 as acceptance conjunct 5 and by the `commit-msg` hook.

WHY THIS EXISTS, and no compiler catches this class. The trophy statement is
built from the vocabulary of eight files. Change `isZFCModel` at
`src/FOL/ZFModel.lagda.md:419`, or `𝒮ʟ` at `src/L/Constructible.lagda.md:410`,
or `LEM` at `src/Base/Classical.lagda.md:41`, and THE TROPHY STILL TYPECHECKS
WHILE IT ASSERTS SOMETHING DIFFERENT. Agda is green, every gate is green, and
the theorem changed. This gate hashes the declaration signatures of the surface
and refuses a silent move.

THE SURFACE, and the derivation reproduces the ruled figures exactly.
`src/Landmarks.lagda.md` plus ONE FILE PER `open import` in its fences. A bare
`import M` is excluded, because the bare imports hold the PROOFS and
`src/Landmarks.lagda.md:77` reads `L⊨ZFC = L.Model.L⊨ZFC`, so a signature
change there fails to typecheck. VERIFIED 2026-08-17: 8 files and 499 non-blank
in-fence lines, which is the ruled figure to the line. One audit counted all 9
imports and reported 819 lines as a mismatch.

WHAT A DECLARATION SIGNATURE IS, four forms, inside an ` ```agda ` fence, with
the full type text:

  1. A named signature. The first token is a name and the next token at the same
     nesting is `:` and not `:=`.
  2. A `data` or `record` head, plus every constructor and every `field`
     signature under it.
  3. A parameterized `module` header, because the parameter is part of the
     statement.
  4. An `import`, `open import` or `open import ... public` line, with its whole
     `using` or `renaming` clause. The import block is itself a guarded
     declaration: delete `open import Base.Classical using (LEM)`, inline a
     local `LEM`, and the surface silently shrinks to 7 files.

A definition body, a `where` block's contents, a comment and all prose are NOT
signatures, so a worker may rewrite a proof freely.

EXTRACTION, without a full Agda run. It reuses `FENCE` at
`archive/scripts/gate/check-tree.py:101` and the fence join of `code_of()` at
`:115`. It cuts declarations by INDENT: a head starts at column `c`, and its
signature text runs to the first line at or left of `c`, or to a bare `where`.
It strips
comments, collapses whitespace, and never sorts tokens. It emits
`<module>#<name> :: <type>` and hashes that.

THE SKIP LIST OF SECTION 7.3 IS NINE KEYWORDS, and each one has a disposition
here. NONE of them is ever a declaration NAME, and the scan splits them in two:

  * `private`, `abstract`, `opaque`, `instance` and `variable` OPEN A BLOCK. The
    keyword is skipped and the scan RECURSES, because a private name can still
    appear in a public type, and because a generalized `variable` sits inside
    every signature that uses it. `field` joins them, which form 2 requires.
  * `infix`, `infixl`, `infixr`, `syntax`, `pattern` and `{-#` STATE NO TYPE.
    `RESERVED` refuses the first three groups as a name, and `PRAGMA` deletes a
    `{-# ... #-}` block before the scan starts, keeping the line count.

An unparameterized `module M where` header states nothing a caller depends on,
so it is not a head either, and form 3 takes the parameterized header only.

TWO READERS, ONE DERIVATION, AND THE MODE PICKS THE READER. `--check` reads the
WORKING TREE, because that is the tree the acceptance runner just typechecked.
`--msg-file` reads the GIT INDEX, because the index is what the next commit
contains, and refusing that commit is the whole job of a `commit-msg` hook. The
copied gate `archive/scripts/gate/check-live-territory.py:387-391` reads the
index for the same reason. A working-tree read in the hook is a MEASURED defect
and not a detail: on 2026-08-17 the design memo was amended eight times, the live
derivation left the snapshot, and the hook then refused every commit in the
repository, including commits that staged nothing guarded.

THE SNAPSHOT, `dev/pod/spec-surface.toml`, tracked. It carries `derived_from`,
`derivation`, `files`, `lines`, one `[[declaration]]` per signature with `file`,
`name`, `text` and `sha`, and one `[[guarded]]` per R16 rule home with `path`
and `sha`. Regenerate it with `--write`.

THE SNAPSHOT IS VALIDATED BEFORE IT IS USED, and a bad one REFUSES. The file is
generated, so a hand-edited one is already outside the contract; valid TOML with
a wrong value type used to reach `differences()` and raise a TypeError, and a
traceback in an unattended loop stops the loop with no message. Every table, key
and value type is checked at load, and a failure exits 2 with the offending key.

`lines` is PROVENANCE and is never compared. A comparison on it would fail every
proof-body edit, and section 7.3 states the opposite: this gate cannot see a
definition body.

R16 RIDES THE SAME SNAPSHOT, AND THAT IS THE WHOLE MECHANISM. A `[[guarded]]`
entry is one sha256 over the WHOLE file and needs no parser. The rule homes are
`AGENTS.md`, the design memo, which carries section 3 and section 3.1,
`dev/pod/heads.toml`, and every `dev/pod/instructions/*.md`. A changed sha fails
`--check` exactly as a changed signature does. No second mechanism, no second
trailer, no second checker.

`AGENTS.md` IS GUARDED HERE BECAUSE ITS OWN GUARD WAS ARCHIVED AND THIS FILE
REPLACED IT. Before the cutover `archive/scripts/gate/check-agents-guard.py`
refused any commit that staged `AGENTS.md` without an `AGENTS-diff-approved:`
trailer. The cutover retired that gate on the premise that the guarded file was
void, and amendment A8 then ruled the opposite: `AGENTS.md` is NOT archived, and
`scripts/pod/instructions.py:2` makes it the ONE hand-written source of the
shared half of all five slot files. So an edit there reaches every agent, and
since the cutover nothing has asked for approval. That is the 2026-08-04 drift
the design cites as its own reason, one level up.

THE STALENESS OF THE FIVE SLOT FILES IS A SECOND QUESTION AND THIS GATE DOES NOT
ANSWER IT. A sha over `AGENTS.md` sees an edit; it cannot see whether
`instructions.py --write` was run afterwards. `instructions.py --check` is that
gate, and the `instructions` target of `make check` runs it. **The two gates are
not interchangeable and both are needed.** This one refuses an unapproved edit to
the Boundary; that one refuses an approved edit that never reached the five files
agents read. The pre-commit hook runs NEITHER, so a commit that skips `make check`
can still ship a stale slot file.

EVERY GATE THIS FILE COPIES IS UNDER `archive/`. The POD cutover of 2026-08-18
archived them, and the mirror rule keeps each one at the same path with an
`archive/` prefix. The line numbers below are the archived file's own.

THE APPROVAL MECHANISM copies `archive/scripts/gate/check-agents-guard.py`,
where DD19's harvested half lands. Three parts reuse directly: the trailer regex at
`:66`, the commit-time gate at `:120-133`, which reads
`git diff --cached --name-only`, and the self-anchoring history audit at
`:86-117`, where `tree_has_guard` asks `git cat-file -e <commit>:<home>`, so a
commit from before the guard existed is never judged.

THREE MODES.

  --check           Acceptance conjunct 5, section 5.4. It runs FIRST of the
                    six, because it is the cheapest and because A3 makes the
                    spec surface undefeatable. A failure gives the record
                    `error_class = "spec_surface"`, and the system row
                    `sys-spec-surface` stops the loop.

  --msg-file PATH   The `commit-msg` hook. It reads the INDEX, never the
                    working tree. It refuses the commit unless the message
                    carries the trailer, when the commit stages a guarded rule
                    home, or stages the snapshot, or leaves the INDEXED
                    derivation disagreeing with the INDEXED snapshot. An
                    unstaged edit is not in the next commit, so it is not this
                    hook's business; `--check` catches it at acceptance.

  (no arguments)    The history audit. Every commit that touches a guarded home
                    or the snapshot, and whose own tree carries this checker,
                    must carry the trailer.

  --write           Regenerate the snapshot. It is not a gate.

The trailer is `Spec-surface-approved: YYYY-MM-DD (name)`.

THE HONEST LIMITS, written down so no row claims more than the checker delivers.
It cannot tell a good change from a bad one. It makes the change visible and
dated. IT CANNOT SEE A DEFINITION BODY, and that is a real hole:
`src/L/Constructible.lagda.md:410-411` reads `𝒮ʟ : ...` and then
`𝒮ʟ = 𝒮ᵥ ↾ isL`, so weakening `isL` makes the trophy a different theorem while
every hash holds. Gap M6. It also stops at the repository boundary, gap m4. AND
IT GUARDS THE LANDED TROPHY ONLY: `src/Landmarks.lagda.md` does not import
`L.GCH`, so `GCHStatement` at `src/L/GCH.lagda.md:59-60` sits outside the
guarded set for the whole build. When the GCH trophy lands, its statement joins
`src/Landmarks.lagda.md` as an `open import` and the surface grows to 9 files by
the same derivation, with no rule change. Gap M15 carries it until then.

Exit status: 0 clean, 1 a change with no approval, 2 an environment failure.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
import tomllib
from datetime import date
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
LANDMARKS_REL = "src/Landmarks.lagda.md"
LANDMARKS = ROOT / LANDMARKS_REL
SNAPSHOT = ROOT / "dev" / "pod" / "spec-surface.toml"
SNAPSHOT_REL = "dev/pod/spec-surface.toml"

DERIVATION = ("src/Landmarks.lagda.md plus one file per `open import` in its "
              "fences; a bare `import M` is excluded")

#: The trailer, copied from `archive/scripts/gate/check-agents-guard.py:66` with
#: R16's name. The machine cannot verify that the owner ruled, and it does not
#: pretend to: the
#: trailer turns silent drift into an explicit, dated assertion, and
#: `git log --grep=Spec-surface-approved` audits every one in seconds.
TRAILER_RE = re.compile(
    r"^Spec-surface-approved: \d{4}-\d{2}-\d{2}(?: \(.+\))?\s*$", re.M)

#: R16's rule homes. Each is one sha256 over the whole file. `GUARDED_DIRS` holds
#: a directory: every file under it is guarded, so a new instruction file is a
#: change and not a hole.
GUARDED_FILES = [
    # `AGENTS.md` is the shared Boundary and amendment A8 makes it the ONE
    # hand-written source of every slot file's shared half. Its own guard,
    # `archive/scripts/gate/check-agents-guard.py`, archived at the cutover on
    # the premise that the file was void, which A8 refutes. R16's own text
    # ("a change to this rule set") already covered it; only this list was short.
    "AGENTS.md",
    "dev/memos/L9-pod-program-design.md",
    "dev/pod/heads.toml",
]
GUARDED_DIRS = ["dev/pod/instructions"]

#: The homes whose committed trees count as "this guard exists". DERIVED from
#: where this file sits, so a move cannot orphan it
#: (`archive/scripts/gate/check-agents-guard.py:75-78`, and `[LJ-1.290]` measured
#: the false green a rewritten literal gives).
GUARD_HOMES = [Path(__file__).resolve().relative_to(ROOT).as_posix()]

#: The fence and the code join of `archive/scripts/gate/check-tree.py:101` and
#: `:115`.
FENCE = re.compile(r"```agda\n(.*?)```", re.S)

PRAGMA = re.compile(r"\{-#.*?#-\}", re.S)
BLOCK_COMMENT = re.compile(r"\{-.*?-\}", re.S)
LINE_COMMENT = re.compile(r"(?:^|(?<=\s))--(?=\s|$).*")

#: A bare `where` token: the other cut of a signature.
WHERE = re.compile(r"(?:^|\s)where\b")

#: An `open import` in the Landmarks import block. A bare `import M` does not
#: match, and that exclusion is what reproduces 8 files and 499 lines.
OPEN_IMPORT = re.compile(r"^open import ([A-Za-z0-9_.]+)", re.M)

#: Agda words that are never a declaration NAME. A line whose first token sits
#: here is not a form-1 head.
RESERVED = {
    "module", "open", "import", "data", "record", "field", "where", "with",
    "let", "in", "do", "postulate", "primitive", "mutual", "abstract",
    "private", "instance", "opaque", "unfolding", "variable", "syntax",
    "pattern", "constructor", "using", "hiding", "renaming", "public",
    "rewrite", "macro", "quote", "quoteTerm", "unquote", "unquoteDecl",
    "tactic", "inductive", "coinductive", "eta-equality", "no-eta-equality",
    "overlap", "interleaved", "forall", "infix", "infixl", "infixr",
}

#: Keywords that OPEN a block of declarations. The scan recurses into each, and
#: `field` is not optional: form 2 names every field signature.
BLOCK_KEYWORDS = {"private", "opaque", "abstract", "instance", "mutual",
                  "postulate", "field", "variable"}

#: A token that can never start a declaration name. It is punctuation or an
#: application argument, so a body line that begins with one is not a head.
NOT_A_NAME_START = tuple("(){}[];,.=|\\→←")


class GitError(Exception):
    """git failed, or git is absent. Every mode that runs git refuses on it.

    A gate that raises a CalledProcessError inside a `commit-msg` hook prints a
    traceback and takes the commit down with it. C-48: a tool that can read a
    condition refuses on it.
    """


def git(*args: str) -> str:
    try:
        proc = subprocess.run(["git", *args], capture_output=True, text=True,
                              cwd=ROOT)
    except OSError as exc:                      # git is not installed
        raise GitError(f"cannot run git: {exc}") from exc
    if proc.returncode != 0:
        raise GitError(f"git {' '.join(args)}: {proc.stderr.strip()}")
    return proc.stdout


class Tree:
    """One reader of the repository. The MODE picks it, and nothing else does.

    `WORKING` reads the files on disk, which is what Agda typechecked.
    `INDEX` reads the git index, which is what the next commit contains. Both
    answer the same three questions, so ONE derivation serves both and the two
    modes can never drift apart.
    """

    def data(self, rel: str) -> bytes | None:
        raise NotImplementedError

    def text(self, rel: str) -> str | None:
        raw = self.data(rel)
        return None if raw is None else raw.decode("utf-8", "replace")

    def files_under(self, rel: str) -> list[str]:
        raise NotImplementedError

    def snapshot(self) -> bytes | None:
        raise NotImplementedError


class WorkingTree(Tree):
    """The files on disk. `SNAPSHOT` names the snapshot, so a test may move it."""

    def data(self, rel: str) -> bytes | None:
        try:
            return (ROOT / rel).read_bytes()
        except OSError:                          # absent, or a directory
            return None

    def files_under(self, rel: str) -> list[str]:
        base = ROOT / rel
        if not base.is_dir():
            return []
        return sorted(p.relative_to(ROOT).as_posix()
                      for p in base.rglob("*") if p.is_file())

    def snapshot(self) -> bytes | None:
        try:
            return SNAPSHOT.read_bytes()
        except OSError:
            return None


class IndexTree(Tree):
    """The git index: the content of the NEXT commit, staged or already tracked.

    `git show :<path>` reads one index blob and `git ls-files` lists the index,
    so a staged deletion is absent here and a staged edit is what this reader
    returns. A path that is not in the index at all reads as absent, which is
    the honest answer: the next commit does not carry it.
    """

    def data(self, rel: str) -> bytes | None:
        try:
            proc = subprocess.run(["git", "show", f":{rel}"], cwd=ROOT,
                                  capture_output=True)
        except OSError as exc:
            raise GitError(f"cannot run git: {exc}") from exc
        return proc.stdout if proc.returncode == 0 else None

    def files_under(self, rel: str) -> list[str]:
        out = git("ls-files", "-z", "--", rel)
        return sorted(p for p in out.split("\0") if p)

    def snapshot(self) -> bytes | None:
        return self.data(SNAPSHOT_REL)


WORKING = WorkingTree()
INDEX = IndexTree()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def fence_code(text: str) -> str:
    """Every ` ```agda ` fence of one master, joined, with comments removed."""
    code = "\n".join(FENCE.findall(text))
    code = PRAGMA.sub(lambda m: "\n" * m.group(0).count("\n"), code)
    code = BLOCK_COMMENT.sub(lambda m: "\n" * m.group(0).count("\n"), code)
    return "\n".join(LINE_COMMENT.sub("", line).rstrip()
                     for line in code.splitlines())


def in_fence_lines(text: str) -> int:
    """Non-blank lines inside the fences, the project's one size caliber."""
    code = "\n".join(FENCE.findall(text))
    return sum(1 for line in code.splitlines() if line.strip())


def module_of(rel: str) -> str:
    return rel.removeprefix("src/").removesuffix(".lagda.md").replace("/", ".")


def surface_files(tree: Tree) -> list[str]:
    """The guarded set: Landmarks, then one file per `open import` in it.

    A tree with no `src/Landmarks.lagda.md` has NO surface. That is a real state
    in the index mode, where a commit may stage the deletion of the trophy root,
    and `differences()` then reports every file as removed rather than crashing.
    """
    text = tree.text(LANDMARKS_REL)
    if text is None:
        return []
    out = [LANDMARKS_REL]
    for name in OPEN_IMPORT.findall(fence_code(text)):
        rel = "src/" + name.replace(".", "/") + ".lagda.md"
        if tree.text(rel) is not None:
            out.append(rel)
    return out


def indent_of(line: str) -> int:
    return len(line) - len(line.lstrip())


def tokenize(line: str) -> list[tuple[str, int]]:
    """(token, bracket depth) pairs. Depth counts `(`, `{` and `[`."""
    out: list[tuple[str, int]] = []
    depth = 0
    token = ""
    start_depth = 0
    for ch in line:
        if ch.isspace():
            if token:
                out.append((token, start_depth))
                token = ""
            continue
        if ch in "({[":
            if token:
                out.append((token, start_depth))
                token = ""
            depth += 1
            continue
        if ch in ")}]":
            if token:
                out.append((token, start_depth))
                token = ""
            depth = max(0, depth - 1)
            continue
        if not token:
            start_depth = depth
        token += ch
    if token:
        out.append((token, start_depth))
    return out


def named_signature(line: str) -> str | None:
    """The name of a form-1 head, or None.

    The first token is a name and the next token at the same nesting is `:` and
    not `:=`. A grouped left side (`a b : T`) keeps every name, joined.
    """
    names: list[str] = []
    for token, depth in tokenize(line):
        if depth != 0:
            return None
        if token == ":":
            return " ".join(names) if names else None
        if token in (":=", "=", "->", "→", "|", "where"):
            return None
        if token in RESERVED or token.startswith(NOT_A_NAME_START):
            return None
        names.append(token)
    return None


def head_of(line: str) -> tuple[str, str] | None:
    """(kind, name) of a declaration head, or None. Kind names the form."""
    parts = line.split()
    if not parts:
        return None
    first = parts[0]
    if first in ("data", "record") and len(parts) >= 2:
        return (first, parts[1])
    if first == "import" and len(parts) >= 2:
        return ("import", parts[1])
    if first == "open" and len(parts) >= 3 and parts[1] == "import":
        return ("import", parts[2])
    if first == "module" or (first == "open" and len(parts) >= 2
                             and parts[1] == "module"):
        rest = parts[1:] if first == "module" else parts[2:]
        if not rest:
            return None
        name = rest[0]
        tail = " ".join(rest[1:])
        # Form 3 takes a PARAMETERIZED header only. `module M where` states
        # nothing a caller can depend on; `module M {ℓ} (P : hProp ℓ) where`
        # does.
        if tail.strip() in ("", "where"):
            return None
        return ("module", name)
    name = named_signature(line)
    return ("signature", name) if name else None


def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def declarations(rel: str, source: str) -> list[dict]:
    """Every declaration signature of one master, in document order.

    It takes the file's TEXT and not its path, so the working tree and the index
    run the SAME extraction, and so a test can drive one synthetic module
    through it without writing a probe into `src/`.
    """
    module = module_of(rel)
    lines = fence_code(source).splitlines()
    out: list[dict] = []
    blocks = [0]          # the legal declaration column of each open block
    pending = False       # a block opened; the next deeper line sets its column
    skip_until: int | None = None
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        col = indent_of(line)
        if skip_until is not None:
            if col > skip_until:
                i += 1
                continue
            skip_until = None
        if pending:
            pending = False
            if col > blocks[-1]:
                blocks.append(col)
        while len(blocks) > 1 and col < blocks[-1]:
            blocks.pop()
        if col != blocks[-1]:
            # A body line or a type continuation the gather below already took.
            # A `where` here belongs to the clause above it, so its contents are
            # not signatures. The test is deliberately narrow, on the FIRST
            # token: a missed skip guards a `where` helper, which is noise, and
            # a false skip drops a real declaration, which is a hole.
            if line.strip().split()[0] == "where":
                skip_until = blocks[-1]
            i += 1
            continue

        # Skip a leading block keyword before deciding whether the line is a
        # head, which is what section 7.3 orders. `field x : T` on one line is
        # a field signature, and `private foo : T` is a private one.
        stripped = line.strip()
        first = stripped.split()[0]
        while True:
            words = stripped.split(None, 1)
            if len(words) == 2 and words[0] in BLOCK_KEYWORDS:
                stripped = words[1]
                continue
            break
        head = head_of(stripped)
        if head is None:
            if first in BLOCK_KEYWORDS:
                pending = True
            elif WHERE.search(stripped) or first == "where":
                skip_until = col   # a definition's own `where` block
            i += 1
            continue

        kind, name = head
        # The signature text runs to the first line at or left of `col`, or to
        # a bare `where`. The `where` cut is not decoration: without it the
        # gather swallows a record's whole `field` block and a data type's
        # constructors, and form 2 requires both.
        parts: list[str] = []
        j = i
        while j < n and lines[j].strip() and (j == i or indent_of(lines[j]) > col):
            piece = stripped if j == i else lines[j].strip()
            parts.append(piece)
            j += 1
            if WHERE.search(piece):
                break
        text = normalize(" ".join(parts))
        cut = WHERE.search(text)
        if cut:
            text = text[:cut.start()].strip()
            pending = kind in ("data", "record", "module")
        emitted = f"{module}#{name} :: {type_text(kind, name, text)}"
        out.append({"file": rel, "name": name,
                    "text": text, "sha": sha256_text(emitted)})
        i = j
    return out


def type_text(kind: str, name: str, text: str) -> str:
    """The `<type>` half of `<module>#<name> :: <type>`.

    A form-1 head gives what follows the `:`. The other three forms carry the
    statement in the head itself, so the head is the type.
    """
    if kind != "signature":
        return text
    head, _, tail = text.partition(":")
    return tail.strip() if head.strip() == name else text


def guarded_entries(tree: Tree) -> list[dict]:
    """One sha256 per R16 rule home that this tree holds."""
    out: list[dict] = []
    for rel in [*GUARDED_FILES,
                *(f for d in GUARDED_DIRS for f in tree.files_under(d))]:
        raw = tree.data(rel)
        if raw is not None:
            out.append({"path": rel, "sha": sha256_bytes(raw)})
    return out


def derive(tree: Tree | None = None) -> dict:
    """The live snapshot, derived from ONE tree. The default is the disk."""
    tree = WORKING if tree is None else tree
    files = surface_files(tree)
    decls: list[dict] = []
    lines = 0
    for rel in files:
        source = tree.text(rel) or ""
        decls += declarations(rel, source)
        lines += in_fence_lines(source)
    return {"derived_from": LANDMARKS_REL,
            "derivation": DERIVATION,
            "files": files,
            "lines": lines,
            "declaration": decls,
            "guarded": guarded_entries(tree)}


def toml_string(value: str) -> str:
    body = (value.replace("\\", "\\\\").replace('"', '\\"')
            .replace("\n", "\\n").replace("\t", "\\t").replace("\r", "\\r"))
    return f'"{body}"'


def render(snapshot: dict) -> str:
    out = [
        "# The spec surface snapshot, AD22 and R9, and R16's rule homes.",
        "# GENERATED by `scripts/pod/check-spec-surface.py --write`.",
        "# Never edit it by hand. A change here needs the trailer",
        "# `Spec-surface-approved: YYYY-MM-DD (name)` on the commit.",
        "",
        f"derived_from = {toml_string(snapshot['derived_from'])}",
        f"derivation = {toml_string(snapshot['derivation'])}",
        f"generated = {toml_string(str(date.today()))}",
        f"lines = {snapshot['lines']}  # provenance only; it is never compared",
        "files = [",
    ]
    out += [f"  {toml_string(f)}," for f in snapshot["files"]]
    out += ["]", ""]
    for d in snapshot["declaration"]:
        out += ["[[declaration]]",
                f"file = {toml_string(d['file'])}",
                f"name = {toml_string(d['name'])}",
                f"text = {toml_string(d['text'])}",
                f"sha = {toml_string(d['sha'])}",
                ""]
    for g in snapshot["guarded"]:
        out += ["[[guarded]]",
                f"path = {toml_string(g['path'])}",
                f"sha = {toml_string(g['sha'])}",
                ""]
    return "\n".join(out)


class SnapshotError(Exception):
    """The snapshot exists and cannot be read. It is never a silent pass."""


#: The snapshot's shape: one table name, and the string keys each entry needs.
#: `differences()` reads exactly these, so a value of another type there used to
#: raise a TypeError one frame deeper instead of refusing here.
SNAPSHOT_TABLES = {"declaration": ("file", "name", "text", "sha"),
                   "guarded": ("path", "sha")}


def validate_snapshot(data: dict) -> dict:
    """Refuse a snapshot whose TYPES are wrong, however valid its TOML is.

    The file is generated, so a wrong type means a hand edit or a corrupt write.
    The gate refuses with the offending key and exits 2. It never guesses, and
    it never lets a wrong type reach the comparison (C-48).
    """
    if not isinstance(data, dict):
        raise SnapshotError(f"{SNAPSHOT_REL}: the top level is not a table")
    files = data.setdefault("files", [])
    if not isinstance(files, list) or not all(isinstance(f, str) for f in files):
        raise SnapshotError(f"{SNAPSHOT_REL}: `files` must be a list of strings")
    for table, keys in SNAPSHOT_TABLES.items():
        rows = data.setdefault(table, [])
        if not isinstance(rows, list):
            raise SnapshotError(f"{SNAPSHOT_REL}: `{table}` must be a list of "
                                f"tables, not {type(rows).__name__}")
        for i, row in enumerate(rows):
            if not isinstance(row, dict):
                raise SnapshotError(f"{SNAPSHOT_REL}: [[{table}]] entry {i} is "
                                    f"not a table")
            for k in keys:
                if not isinstance(row.get(k), str):
                    raise SnapshotError(
                        f"{SNAPSHOT_REL}: [[{table}]] entry {i} needs a string "
                        f"`{k}`, and it has {type(row.get(k)).__name__}")
    return data


def load_snapshot(tree: Tree | None = None) -> dict | None:
    """The snapshot THIS tree holds, validated, or None when it holds none."""
    tree = WORKING if tree is None else tree
    try:
        raw = tree.snapshot()
    except GitError as exc:
        raise SnapshotError(str(exc)) from exc
    if raw is None:
        return None
    try:
        data = tomllib.loads(raw.decode("utf-8"))
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as exc:
        raise SnapshotError(f"{SNAPSHOT_REL}: {exc}") from exc
    return validate_snapshot(data)


def differences(snapshot: dict, live: dict) -> list[str]:
    """Every difference between the snapshot and the tree, as one line each.

    `lines` is not compared. Comparing it would fail every proof-body edit,
    which section 7.3 states this gate must not do.
    """
    out: list[str] = []
    was, now = list(snapshot["files"]), list(live["files"])
    for f in now:
        if f not in was:
            out.append(f"surface file added: {f}")
    for f in was:
        if f not in now:
            out.append(f"surface file removed: {f}")

    def key(d: dict) -> tuple[str, str]:
        return (d["file"], d["name"])

    old_by_key: dict[tuple[str, str], list[dict]] = {}
    for d in snapshot["declaration"]:
        old_by_key.setdefault(key(d), []).append(d)
    new_by_key: dict[tuple[str, str], list[dict]] = {}
    for d in live["declaration"]:
        new_by_key.setdefault(key(d), []).append(d)
    for k in sorted(set(new_by_key) | set(old_by_key)):
        old, new = old_by_key.get(k, []), new_by_key.get(k, [])
        file, name = k
        if not old:
            out.append(f"declaration added: {file} :: {name}")
            continue
        if not new:
            out.append(f"declaration removed: {file} :: {name}")
            continue
        for a, b in zip(old, new):
            if a["sha"] != b["sha"]:
                out.append(f"declaration changed: {file} :: {name}\n"
                           f"      was: {a['text']}\n      now: {b['text']}")
        if len(new) > len(old):
            out.append(f"declaration added: {file} :: {name} "
                       f"({len(new) - len(old)} more with this name)")
        if len(old) > len(new):
            out.append(f"declaration removed: {file} :: {name} "
                       f"({len(old) - len(new)} fewer with this name)")

    old_g = {g["path"]: g["sha"] for g in snapshot["guarded"]}
    new_g = {g["path"]: g["sha"] for g in live["guarded"]}
    for path in sorted(set(old_g) | set(new_g)):
        if path not in old_g:
            out.append(f"guarded rule home added: {path}")
        elif path not in new_g:
            out.append(f"guarded rule home removed: {path}")
        elif old_g[path] != new_g[path]:
            out.append(f"guarded rule home changed: {path}")
    return out


def audited_paths() -> list[str]:
    """What the history audit and the commit gate watch: R16's homes and the
    snapshot. A snapshot change IS a surface change that landed."""
    return [*GUARDED_FILES, *GUARDED_DIRS, SNAPSHOT_REL]


def is_audited(path: str) -> bool:
    for watched in audited_paths():
        if path == watched or path.startswith(watched.rstrip("/") + "/"):
            return True
    return False


def tree_has_guard(commit: str) -> bool:
    """Could THIS commit's tree have enforced the guard? Self-anchoring, no epoch hash.

    THE ANCHOR IS THE WIRING AND NOT THE FILE, and that correction cost two false
    failures. The old AGENTS.md guard anchored on "the tree contains this checker",
    which was sound for it because the checker and its hook line landed in ONE commit.
    This checker did not: it entered at `ed09b26` with the hardening round and was wired
    into `commit-msg` at the cutover, `fc676cb`. Between them, two commits touched a
    guarded home under a tree that HELD this file and could not RUN it, so presence
    judged authors for a rule no hook could have told them about. **A gate that fails a
    commit whose author could not have complied teaches every author to ignore it.**

    So the probe reads the hook. A commit whose `commit-msg` does not call this checker
    predates enforcement and is not judged.
    """
    try:
        probe = subprocess.run(
            ["git", "show", f"{commit}:scripts/git-hooks/commit-msg"],
            capture_output=True, text=True, cwd=ROOT)
    except OSError as exc:
        raise GitError(f"cannot run git: {exc}") from exc
    if probe.returncode != 0:
        return False                      # no hook in that tree: nothing to enforce
    return Path(GUARD_HOMES[0]).name in probe.stdout


def check() -> int:
    """Acceptance conjunct 5, over the WORKING TREE. Exit 1 gives fact 2
    `spec_surface`."""
    try:
        snapshot = load_snapshot(WORKING)
    except SnapshotError as exc:
        print(f"check-spec-surface: unreadable snapshot: {exc}", file=sys.stderr)
        return 2
    if snapshot is None:
        print(f"check-spec-surface: NO SNAPSHOT at {SNAPSHOT_REL}. Run "
              f"`--write` once and commit it. The gate refuses to pass a "
              f"surface it has never seen (C-48).", file=sys.stderr)
        return 2
    live = derive(WORKING)
    bad = differences(snapshot, live)
    if bad:
        print("check-spec-surface: FAIL. The trophy spec surface moved and no "
              "approval names it:", file=sys.stderr)
        for line in bad:
            print(f"  {line}", file=sys.stderr)
        print("\nA change inside the surface changes what the trophy asserts "
              "while the tree stays\ngreen. Show the owner the diff, get the "
              "ruling, run `--write`, and commit with\n"
              "`Spec-surface-approved: YYYY-MM-DD (name)`.", file=sys.stderr)
        return 1
    print(f"check-spec-surface: clean ({len(live['files'])} surface file(s), "
          f"{len(live['declaration'])} declaration(s), "
          f"{len(live['guarded'])} guarded rule home(s), "
          f"{live['lines']} in-fence lines)")
    return 0


def gate_commit(msg_file: str) -> int:
    """The `commit-msg` hook, and it reads the INDEX and never the disk.

    The hook's one job is to refuse the NEXT COMMIT, so it asks what that commit
    contains: `git diff --cached` for the paths it touches, and the index blobs
    for the surface and the snapshot it will carry. An unstaged edit belongs to
    `--check`, at acceptance. The archived gate
    `archive/scripts/gate/check-live-territory.py:387-391` reads the index for
    the same reason.
    """
    drift: list[str] = []
    try:
        staged = [p for p in git("diff", "--cached", "--name-only", "-z")
                  .split("\0") if p]
        snapshot = load_snapshot(INDEX)
        if snapshot is not None:
            drift = differences(snapshot, derive(INDEX))
    except SnapshotError as exc:
        print(f"check-spec-surface: unreadable snapshot: {exc}", file=sys.stderr)
        return 2
    except GitError as exc:
        print(f"check-spec-surface: cannot read the index: {exc}",
              file=sys.stderr)
        return 2
    watched = sorted(p for p in staged if is_audited(p))
    if not watched and not drift:
        return 0
    try:
        with open(msg_file, encoding="utf-8") as fh:
            message = fh.read()
    except OSError as exc:
        print(f"check-spec-surface: cannot read {msg_file}: {exc}",
              file=sys.stderr)
        return 2
    if TRAILER_RE.search(message):
        return 0
    print("check-spec-surface: REFUSED. This commit STAGES a move of the trophy "
          "spec surface\nor a rule home, and the message carries no "
          "`Spec-surface-approved: YYYY-MM-DD (name)`\ntrailer (R9 and R16).",
          file=sys.stderr)
    for path in watched:
        print(f"  staged: {path}", file=sys.stderr)
    for line in drift:
        print(f"  {line}", file=sys.stderr)
    print("Show the owner the diff and the reason first. Add the trailer only "
          "after the ruling.", file=sys.stderr)
    return 1


def audit_history() -> int:
    """Every commit that touches a guarded home and could run this guard."""
    bad: list[str] = []
    guarded = 0
    try:
        commits = git("log", "--format=%H", "--", *audited_paths()).split()
        for commit in commits:
            if not tree_has_guard(commit):
                continue  # predates the guard; not judged
            guarded += 1
            message = git("show", "-s", "--format=%B", commit)
            if not TRAILER_RE.search(message):
                bad.append(git("show", "-s", "--format=%h %s", commit).strip())
    except GitError as exc:
        print(f"check-spec-surface: cannot read the history: {exc}",
              file=sys.stderr)
        return 2
    if bad:
        print("check-spec-surface: FAIL. A rule home or the snapshot changed "
              "without the owner's dated approval trailer (R9, R16):",
              file=sys.stderr)
        for line in bad:
            print(f"  {line}", file=sys.stderr)
        return 1
    print(f"check-spec-surface: clean ({guarded} guarded commit(s), "
          f"{len(commits) - guarded} pre-guard)")
    return 0


def write_snapshot() -> int:
    """Regenerate the snapshot from the WORKING TREE. It is not a gate.

    The owner approves the change; this only records it. The write is atomic:
    a temporary file beside the target, then one rename, so a crash never leaves
    half a snapshot for the next `--check` to refuse.
    """
    live = derive(WORKING)
    SNAPSHOT.parent.mkdir(parents=True, exist_ok=True)
    tmp = SNAPSHOT.with_name(SNAPSHOT.name + ".tmp")
    try:
        tmp.write_text(render(live), encoding="utf-8")
        tmp.replace(SNAPSHOT)
    except OSError as exc:
        tmp.unlink(missing_ok=True)
        print(f"check-spec-surface: cannot write {SNAPSHOT_REL}: {exc}",
              file=sys.stderr)
        return 2
    print(f"check-spec-surface: wrote {SNAPSHOT_REL} "
          f"({len(live['files'])} file(s), {len(live['declaration'])} "
          f"declaration(s), {len(live['guarded'])} guarded rule home(s), "
          f"{live['lines']} in-fence lines)")
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="the spec surface gate, AD22")
    parser.add_argument("--check", action="store_true",
                        help="acceptance conjunct 5: the tree against the snapshot")
    parser.add_argument("--write", action="store_true",
                        help="regenerate dev/pod/spec-surface.toml")
    parser.add_argument("--msg-file", metavar="PATH",
                        help="commit-msg hook mode: the commit message file")
    args = parser.parse_args(argv[1:])
    if sum(bool(x) for x in (args.check, args.write, args.msg_file)) > 1:
        print("check-spec-surface: pick ONE mode", file=sys.stderr)
        return 2
    # THE ROOT CHECK BINDS THE TWO WORKING-TREE MODES ONLY. The commit gate
    # reads the index, where a staged deletion of the root is a legal state and
    # a refusal to commit, not an environment failure; the history audit reads
    # commits and never the disk.
    if (args.write or args.check) and not LANDMARKS.is_file():
        print(f"check-spec-surface: no {LANDMARKS}: the surface has no root",
              file=sys.stderr)
        return 2
    if args.write:
        return write_snapshot()
    if args.msg_file:
        return gate_commit(args.msg_file)
    if args.check:
        return check()
    return audit_history()


if __name__ == "__main__":
    sys.exit(main(sys.argv))
