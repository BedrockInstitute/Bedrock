#!/usr/bin/env python3
"""Regression tests for the three POD gates of day 6.

WHY THIS FILE EXISTS. Each gate below refuses one measured failure, and a gate
that inverts silently is worse than no gate at all.

  1. `scripts/pod/check-spec-surface.py` (AD22, R9 and R16). A worker can edit
     `isZFCModel`, `𝒮ʟ` or `LEM` and leave the tree green while the trophy
     asserts something different. The gate hashes 8 files and 499 in-fence
     lines, which are the ruled figures of section 7.3, and one audit that
     counted the two bare imports too reported 819 lines as a mismatch. These
     tests pin the derivation, the four declaration forms, the nine skipped
     keywords, both readers and all three exit codes.
  2. `scripts/pod/check-survey-quotes.py` (AD23, section 7.4 Part 2). It keeps
     both gated halves of `scripts/gate/check-dd18-survey.py`: `answered()` and
     `audit_quotes()` with `WINDOW = 3`. These tests pin the three verdicts, the
     decline escape, and the exit codes.
  3. `scripts/pod/retrieve.py` (section 7.4 Parts 1a and 1b). THE SCOPE IS THE
     MEASURED PART. The scoped column of
     `dev/measurements/pod-retrieval-scoping-2026-08-17.txt:19-31` REPRODUCES,
     because the archive corpus last changed on 2026-08-13 and the briefs are
     frozen records. So the ranker must reproduce it to the rank, and this file
     is that regression test. It also pins the corpus rule, the `NO HIT` result,
     and the producer of the miss signal.

THREE ASSERTIONS OF AN EARLIER FORM OF THIS FILE COULD NOT FAIL, and they are
named here because a test suite is judged by what it refuses, never by its
green line. (1) The `--msg-file` cases drove the gate against the WORKING TREE
and never staged anything, so they passed while the hook read the wrong tree;
they are replaced by `fixture_repo()`, which builds one real git repository and
stages real changes. (2) One case built a hash from a literal string it had just
written and compared it with another literal; it is replaced by a re-derivation
of the real file with one type weakened. (3) One case called `retrieve()` twice
with the same argument and compared the results, which no implementation can
fail; it is replaced by the tie-and-zero-score case, which a ranker that keeps
zero scores fails.

Run: `python3 scripts/tests/test_pod_gates.py`
"""

from __future__ import annotations

import importlib.util
import io
import json
import shutil
import subprocess
import sys
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
POD = ROOT / "scripts" / "pod"


def load(name: str, filename: str, where: Path = POD):
    spec = importlib.util.spec_from_file_location(name, where / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


css = load("check_spec_surface", "check-spec-surface.py")
csq = load("check_survey_quotes", "check-survey-quotes.py")
retr = load("retrieve", "retrieve.py")

failures: list[str] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    if condition:
        print(f"  ok    {name}")
    else:
        print(f"  FAIL  {name}{(': ' + detail) if detail else ''}")
        failures.append(name)


def quiet(fn, *args):
    """Run one gate mode and return (exit code, stdout + stderr)."""
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        code = fn(*args)
    return code, out.getvalue() + err.getvalue()


tmp = Path(tempfile.mkdtemp(prefix="pod-gates-"))

# ---------------------------------------------------------------------------
# 1. THE RANKER, against the frozen measurement. The scoped column reproduces.
print("retrieve.py reproduces the scoped column of the 2026-08-17 measurement")

SRC_SCOPE = ["archive/src"]
DEV_SCOPE = ["archive/dev"]
RUD = "archive/src/2026-08-09-rud-route"

#: (episode, brief, gold, scope, the rank the ranker gives TODAY).
#: The measurement is `dev/measurements/pod-retrieval-scoping-2026-08-17.txt:21-29`.
#:
#: THE TWO `DEV_SCOPE` RANKS MOVED ON 2026-08-18 AND THE RECORD PREDICTED IT.
#: Its own reproducibility note reads: the scoped column reproduces because the
#: archive corpus last changed 2026-08-13. **The POD cutover changed it**, by
#: archiving `dev/ORCHESTRATION.md` into `archive/dev/`. One 604-line document
#: entering a six-file corpus moves the document frequencies and the average
#: length, so episode 11 went 2 -> 3 and episode 10 went 3 -> 5.
#: **The `SRC_SCOPE` ranks are untouched**, because `archive/src/` did not change,
#: and that is the control that proves the cause.
#: The ranker is unchanged. Retrieval is a function of its corpus, and this is what
#: that costs: archiving a document re-ranks every query against that scope.
EPISODES = [
    ("7", "agents/tasks/LJ-1-237/LJ-1.237.md", f"{RUD}/L/Condensation.lagda.md",
     SRC_SCOPE, 1),
    ("7b", "agents/tasks/LJ-1-239/LJ-1.239.md", f"{RUD}/L/Condensation.lagda.md",
     SRC_SCOPE, 1),
    ("11", "agents/tasks/archive/LJ-1-10/LJ-1.10.md",
     "archive/dev/TASKS-archived.md", DEV_SCOPE, 4),  # episode 11: 2 pre-cutover, 3 post-cutover, 5 after the slimming, 4 after PLAN-archived.md
    ("5", "agents/tasks/LJ-1-353/LJ-1.353.md", f"{RUD}/L/Cardinal.lagda.md",
     SRC_SCOPE, 3),
    ("10", "agents/tasks/archive/LJ-1-6/LJ-1.6.md",
     "archive/dev/TASKS-archived.md", DEV_SCOPE, 7),  # episode 10: 3 pre-cutover, 5 post-cutover, 7 after the slimming
    ("5b", "agents/tasks/LJ-1-136/LJ-1.136.md", f"{RUD}/L/Cardinal.lagda.md",
     SRC_SCOPE, 16),
    ("6", "agents/tasks/LJ-1-92/LJ-1.92.md",
     f"{RUD}/L/Ordinal/Pairing.lagda.md", SRC_SCOPE, 28),
]


def rank_of(brief: str, gold: str, scope: list[str]) -> int | None:
    hits = retr.retrieve(retr.goal_text(brief), scope, 500)
    for position, (path, _score) in enumerate(hits, 1):
        if path == gold:
            return position
    return None


check("archive/src holds the 97 masters the record scoped",
      len(retr.corpus(SRC_SCOPE)) == 97, str(len(retr.corpus(SRC_SCOPE))))
# 7 SINCE THE POD CUTOVER, and the count is the point rather than a detail. The
# record scoped 6; cutover step 4b archived `dev/ORCHESTRATION.md` here, and that
# one document is why the two DEV_SCOPE ranks above moved. Pin the count, so the
# next document to enter this corpus fails a test instead of moving a rank quietly.
# 9 SINCE THE DEV/ SLIMMING OF 2026-08-18. It was 6 at the frozen record, 7 after the
# cutover archived ORCHESTRATION.md, and 9 after DD-archived.md and LJ-dispatch-index.md
# joined it. **THE PIN DID ITS JOB TWICE:** each time a document entered this corpus the
# ranks below moved and this line went red first, instead of a rank sliding in silence.
# 10 SINCE THE HISTORY SWEEP OF 2026-08-18 added L-goals-archived.md. THE PIN HAS NOW
# FIRED THREE TIMES: 6 -> 7 (ORCHESTRATION.md) -> 9 (DD-archived, LJ-dispatch-index)
# -> 10. **This time the ranks did NOT move**, because a table of goal rows shares no
# discriminative token with either query. That is the useful reading: the pin catches
# every corpus change, and only some of them move a rank.
# 2026-08-20: `direction_changed()` filed archive/dev/direction/20260820-142326.md
# and this pin went 10 -> 11. That directory is designed to grow. retrieve.corpus
# now excludes it, so the pin still tracks the retrieval records.
# 11 SINCE PLAN.md was archived as archive/dev/PLAN-archived.md on 2026-08-20.
# THE PIN FIRED: 10 -> 11, and episode 11 moved 5 -> 4. Direction history stays
# excluded; this file is a retrieval record.
check("archive/dev holds 11 records after PLAN.md was archived",
      len(retr.corpus(DEV_SCOPE)) == 11, str(len(retr.corpus(DEV_SCOPE))))
check("a filed direction is history and is not a retrieval record",
      not any(p.startswith("archive/dev/direction/")
              for p in retr.corpus(DEV_SCOPE)))
check("the corpus rule keeps a README index out of a code archive",
      not [p for p in retr.corpus(SRC_SCOPE) if p.endswith("README.md")])

for eid, brief, gold, scope, want in EPISODES:
    got = rank_of(brief, gold, scope)
    check(f"episode {eid}: gold at rank {want}", got == want, f"rank {got}")

check("k clamps the result",
      len(retr.retrieve("condensation", SRC_SCOPE, 3)) == 3)
check("an empty scope returns nothing, and never raises",
      retr.retrieve("condensation", ["archive/no-such-directory"], 5) == [])

# NO HIT IS REACHABLE, and it is the whole point of section 7.4's first-class
# result. BM25 scores every file of the scope, so a top-k over the raw ranking
# always returns k paths; a query that shares no token with the corpus must
# return NOTHING instead. This case fails against a ranker that keeps 0.0.
_nonsense = "zzqqxx flurblewombat qwertyuiopfoo"
check("a query that shares no token with the scope returns NO HIT",
      retr.retrieve(_nonsense, SRC_SCOPE, 5) == [],
      str(retr.retrieve(_nonsense, SRC_SCOPE, 5)))
check("the block writes NO HIT for a query nothing in the scope shares",
      "NO HIT" in retr.candidate_block("ARCHIVE", _nonsense, SRC_SCOPE, 5))

# The same two rules over a corpus this test owns, where the scores are known:
# two identical files tie, and the third shares no token with the query.
_mini = tmp / "mini"
(_mini / "sub").mkdir(parents=True)
(_mini / "b.md").write_text("residue leaf supply lemma\n", encoding="utf-8")
(_mini / "a.md").write_text("residue leaf supply lemma\n", encoding="utf-8")
(_mini / "sub" / "c.md").write_text("cardinal ordinal pairing\n", encoding="utf-8")
_saved_root = retr.ROOT
try:
    retr.ROOT = _mini
    _hits = retr.retrieve("residue leaf supply", ["."], 5)
    check("a tie keeps path order and a zero-score file never enters the list",
          [p for p, _ in _hits] == ["a.md", "b.md"], str(_hits))
    check("the two tied files really tie",
          len(_hits) == 2 and _hits[0][1] == _hits[1][1], str(_hits))
finally:
    retr.ROOT = _saved_root

# The candidate block, and the NO HIT line that removes "declined by ritual".
block = retr.candidate_block("ARCHIVE", retr.goal_text(EPISODES[0][1]),
                             SRC_SCOPE, 3)
check("the ARCHIVE block carries the do-not-edit heading",
      block.startswith("## ARCHIVE (program-generated, do not edit)"))
# IT COUNTS CANDIDATE LINES AND NOT THE BARE WORD. The block gained a paragraph on
# 2026-08-19 telling the author how to ANSWER it, and that paragraph names the word
# once, so a bare `count("CANDIDATE")` read 4 where 3 candidates were offered. The
# `bears` half is unchanged and still load-bearing: the program lists files and never
# says one BEARS on the task, because that judgement belongs to the author.
check("the block writes CANDIDATE and never says a file bears",
      len([ln for ln in block.splitlines() if ln.startswith("- CANDIDATE ")]) == 3
      and "bears" not in block)
check("an empty scope writes NO HIT",
      "NO HIT" in retr.candidate_block("ARCHIVE", "x", ["archive/nope"], 3))

# ---------------------------------------------------------------------------
# 2. THE MISS SIGNAL of Part 1b, and the PRODUCER that builds it.
print("retrieve.py measures its own retrieval")

_offered = [f"{RUD}/L/Condensation.lagda.md", "archive/dev/TASKS-archived.md"]
_used = [f"{RUD}/L/Condensation.lagda.md", f"{RUD}/L/Cardinal.lagda.md"]
signal = retr.miss_signal("LJ-1.386", _offered, _used,
                          retr.goal_text(EPISODES[3][1]), SRC_SCOPE)
check("the signal carries the six keys of section 7.4",
      list(signal) == ["event", "task", "offered", "used", "missed", "overlap"],
      str(list(signal)))
check("the event is `retrieval`", signal["event"] == "retrieval")
check("the miss set is what the return used and the injection did not offer",
      signal["missed"] == [f"{RUD}/L/Cardinal.lagda.md"], str(signal["missed"]))
check("a missed file that shares rare words carries a HIGH overlap",
      signal["overlap"] > 0, str(signal["overlap"]))

# THE TWO FAILURE KINDS MUST SEPARATE, because the adoption trigger of section
# 7.4 reads exactly this number: a HIGH overlap is a scope or ranker problem, a
# ZERO overlap is the semantic case. The same missed file, a query that shares
# no discriminative token with it, and the overlap must fall to 0.0.
_semantic = retr.miss_signal("LJ-1.386", _offered, _used, _nonsense, SRC_SCOPE)
check("a missed file that shares no discriminative token carries overlap 0.0",
      _semantic["overlap"] == 0.0 and _semantic["missed"] == signal["missed"],
      str(_semantic))

_none = retr.miss_signal("LJ-1.386", _offered, _offered, "x", SRC_SCOPE)
check("no miss gives overlap 0.0 and an empty miss set",
      _none["missed"] == [] and _none["overlap"] == 0.0)

# The record goes to a JSONL log, so every value must be a JSON native type. A
# Path or a set here raises TypeError inside the loop's own writer, which is a
# stop with a traceback and nobody watching.
try:
    _round = json.loads(json.dumps(signal, ensure_ascii=False))
except TypeError as exc:                                # pragma: no cover
    _round, _why = None, str(exc)
else:
    _why = ""
check("the record is JSON-native, so the transition log can write it",
      _round == signal, _why)

_used_section = """
## ARCHIVE USED

- `archive/dev/TASKS-archived.md:80`: read it.
- `dev/ARCHIVE.md`: NOT read.
"""
check("the return's ARCHIVE USED paths are extracted",
      retr.used_paths(_used_section)
      == ["archive/dev/TASKS-archived.md", "dev/ARCHIVE.md"],
      str(retr.used_paths(_used_section)))

# THE PRODUCER, Part 1b. `miss_signal()` had NO caller before this: the loop
# injected the blocks and never measured the return. The producer reads one
# dispatch's two tracked artifacts and needs no second state file.
_task_dir = tmp / "LJ-1-999"
_task_dir.mkdir()
_fixture_brief = _task_dir / "LJ-1.999.md"
_fixture_brief.write_text(f"""# LJ-1.999: a fixture

## GOAL

The condensation lemma and the layer residue of the constructible hierarchy.

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src:
- CANDIDATE {RUD}/L/Condensation.lagda.md  (score 53.063)
- CANDIDATE archive/dev/TASKS-archived.md  (score 12.000)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature: NO HIT
""", encoding="utf-8")
(_task_dir / "lj-1.999-report.md").write_text(f"""# Report

## ARCHIVE USED

- `{RUD}/L/Condensation.lagda.md:12`: TOOK the shape.
- `{RUD}/L/Cardinal.lagda.md:5`: TOOK the residue.
""", encoding="utf-8")

_blocks = retr.injected_blocks(_fixture_brief.read_text(encoding="utf-8"))
check("both program-generated blocks are read back out of the brief",
      [b[0] for b in _blocks] == ["ARCHIVE", "LITERATURE"], str(_blocks))
check("the block's own scope line is the scope the producer re-ranks with",
      _blocks[0][1] == ["archive/src"] and _blocks[1][1] == ["dev/literature"],
      str([b[1] for b in _blocks]))
check("a NO HIT block offers nothing", _blocks[1][2] == [], str(_blocks[1][2]))

_prod = retr.dispatch_signal("LJ-1.999", _fixture_brief)
check("the producer finds the report beside the brief",
      retr.report_beside(_fixture_brief) == _task_dir / "lj-1.999-report.md",
      str(retr.report_beside(_fixture_brief)))
check("the producer counts what the program offered, from the brief itself",
      _prod["offered"] == 2, str(_prod))
check("the producer names the file the worker used and the program missed",
      _prod["missed"] == [f"{RUD}/L/Cardinal.lagda.md"], str(_prod))
check("the producer's record is the same six-key shape",
      list(_prod) == list(signal), str(list(_prod)))
_no_report = retr.dispatch_signal("LJ-1.999", _fixture_brief,
                                  _task_dir / "no-such-report.md")
check("a return with no report uses nothing and never raises",
      _no_report["used"] == 0 and _no_report["missed"] == [], str(_no_report))

code, text = quiet(retr.main, ["x", "--signal", "LJ-1.999",
                               "--brief", str(_fixture_brief)])
check("`--signal` prints ONE line the transition log can hold",
      code == 0 and len(text.strip().splitlines()) == 1
      and json.loads(text)["task"] == "LJ-1.999", text)
code, text = quiet(retr.main, ["x", "--signal", "LJ-1.999",
                               "--brief", str(tmp / "absent.md")])
check("`--signal` on a missing brief exits 2 and never raises", code == 2, text)
code, text = quiet(retr.main, ["x", "--signal", "LJ-1.999"])
check("`--signal` without --brief exits 2", code == 2, text)

# ---------------------------------------------------------------------------
# 3. THE SPEC SURFACE, AD22. The derivation reproduces the ruled figures.
print("check-spec-surface.py derives the ruled surface")

live = css.derive()
check("the surface is 8 files", len(live["files"]) == 8, str(len(live["files"])))
check("the surface is 499 in-fence lines", live["lines"] == 499,
      str(live["lines"]))
check("a bare `import M` is outside the surface",
      not [f for f in live["files"] if f.endswith("V/Model.lagda.md")])
check("Landmarks is the root of the surface",
      live["files"][0] == "src/Landmarks.lagda.md")

names = {(d["file"].split("/")[-1], d["name"]) for d in live["declaration"]}
for form, want in (
    ("form 1, a named signature", ("Classical.lagda.md", "LEM")),
    ("form 2, a record head", ("ZFModel.lagda.md", "isZFCModel")),
    ("form 2, a field under it", ("ZFModel.lagda.md", "hasChoice")),
    ("form 2, a data head", ("Constructible.lagda.md", "isLayer")),
    ("form 2, a constructor under it", ("Constructible.lagda.md", "𝒟-layer")),
    ("form 3, a parameterized module", ("Choice.lagda.md", "Diaconescu")),
    ("form 4, an `open import` with its using clause",
     ("Landmarks.lagda.md", "Base.Classical")),
    ("form 4, a bare `import`", ("Landmarks.lagda.md", "V.Model")),
    ("the trophy's own signature", ("Landmarks.lagda.md", "L⊨ZFC")),
    ("the private names a public type can name",
     ("Classical.lagda.md", "decodeB")),
):
    check(f"{form} is guarded", want in names, str(want))

check("an unparameterized module header states nothing and is not guarded",
      not [d for d in live["declaration"]
           if d["text"] in ("module Base.Prelude", "module Landmarks")])
check("a `where` block's contents are not signatures",
      not [d for d in live["declaration"] if d["name"] in ("fromDec", "lifted")])
check("a definition body is not a signature",
      not [d for d in live["declaration"] if "= 𝒮ᵥ ↾ isL" in d["text"]])

# THE NINE SKIPPED KEYWORDS of section 7.3, each one driven through the real
# extractor. Five open a block the scan recurses into; four state no type at
# all. A missed skip guards noise; a missed recursion is a HOLE in the surface.
SKIP_FIXTURE = """# fixture

```agda
{-# OPTIONS --safe #-}
module Fixture where

open import Base.Classical using (LEM)

infix 20 _⊆ˢ_
infixl 6 _+ᶠ_
infixr 5 _∷ᶠ_

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

pattern two = suc (suc zero)

variable
  ℓ : Level

private
  helper : Type ℓ → Type ℓ

abstract
  hidden : Type ℓ

opaque
  sealed : Type ℓ

instance
  inst : Type ℓ

{-# TERMINATING #-}
loopy : Type ℓ
loopy = whatever
```
"""
_skip = {d["name"]: d["text"]
         for d in css.declarations("src/Fixture.lagda.md", SKIP_FIXTURE)}
for keyword, name in (("private", "helper"), ("abstract", "hidden"),
                      ("opaque", "sealed"), ("instance", "inst"),
                      ("variable", "ℓ")):
    check(f"`{keyword}` is skipped and the scan recurses into its block",
          name in _skip, str(sorted(_skip)))
check("a pragma does not swallow the signature under it", "loopy" in _skip)
# The exhaustive form, and it is the discriminating one: `infix`, `infixl`,
# `infixr`, `syntax`, `pattern`, `{-#` and an unparameterized `module` header
# state no type, so ANY extra name here is a spurious guarded declaration.
check("the fixture yields exactly the seven names that state a type",
      sorted(_skip) == sorted(["Base.Classical", "ℓ", "helper", "hidden",
                               "sealed", "inst", "loopy"]),
      str(sorted(_skip)))

# THE FOUR FORMS CARRY A TYPE, AND A CHANGED TYPE CHANGES THE HASH. The mutation
# is applied to the REAL file's text and re-derived by the gate's own extractor,
# so this case fails if the emitted line ever stops carrying the type.
_lem = next(d for d in live["declaration"]
            if d["file"].endswith("Classical.lagda.md") and d["name"] == "LEM")
check("a signature carries its full type text",
      _lem["text"] == "LEM : ∀ ℓ → Type (ℓ-suc ℓ)", _lem["text"])

CLASSICAL = "src/Base/Classical.lagda.md"
_classical_src = (ROOT / CLASSICAL).read_text(encoding="utf-8")
_weak_src = _classical_src.replace("LEM : ∀ ℓ → Type (ℓ-suc ℓ)",
                                   "LEM : ∀ ℓ → Type ℓ")
check("the weakening fixture really changes the file",
      _weak_src != _classical_src)
_weakened = next(d for d in css.declarations(CLASSICAL, _weak_src)
                 if d["name"] == "LEM")
check("weakening a type changes the sha the gate emits",
      _weakened["sha"] != _lem["sha"] and _weakened["text"] == "LEM : ∀ ℓ → Type ℓ",
      _weakened["text"])

# THE DOCUMENTED HOLE, gap M6, pinned as a test so it cannot be claimed shut. A
# definition BODY is invisible to this gate, and the docstring says so.
CONSTRUCTIBLE = "src/L/Constructible.lagda.md"
_con_src = (ROOT / CONSTRUCTIBLE).read_text(encoding="utf-8")
_body_src = _con_src.replace("𝒮ʟ = 𝒮ᵥ ↾ isL", "𝒮ʟ = 𝒮ᵥ ↾ isWeaker")
check("the body fixture really changes the file", _body_src != _con_src)
check("a changed definition body moves NO sha (gap M6, stated not hidden)",
      css.declarations(CONSTRUCTIBLE, _body_src)
      == css.declarations(CONSTRUCTIBLE, _con_src))

# ---------------------------------------------------------------------------
# 4. THE SNAPSHOT REFUSES A WRONG SHAPE, and never raises inside the loop.
print("check-spec-surface.py refuses a snapshot it cannot trust")

# The unvalidated dict is exactly what `load_snapshot()` used to hand on, and
# `differences()` raises on it. That is the crash this validation removes.
try:
    css.differences({"files": [], "declaration": 5, "guarded": []}, live)
except TypeError:
    _raises = True
else:
    _raises = False
check("an unvalidated wrong type still raises one frame deeper", _raises)

BAD_SNAPSHOTS = [
    ("a table where a list belongs", 'files = ["x"]\ndeclaration = 5\n',
     "`declaration` must be a list"),
    ("an entry that is not a table", "declaration = [1, 2]\n",
     "entry 0 is not a table"),
    ("a number where a name belongs",
     '[[declaration]]\nfile = "a"\nname = 12\ntext = "t"\nsha = "s"\n',
     "needs a string `name`"),
    ("a guarded home with no sha", '[[guarded]]\npath = "dev/pod/heads.toml"\n',
     "needs a string `sha`"),
    ("files that is not a list of strings", "files = 8\n",
     "`files` must be a list of strings"),
    ("TOML that does not parse", "files = [\n", "unreadable snapshot"),
]
_real_snapshot = css.SNAPSHOT
try:
    for label, body, want in BAD_SNAPSHOTS:
        bad = tmp / "bad.toml"
        bad.write_text(body, encoding="utf-8")
        css.SNAPSHOT = bad
        code, text = quiet(css.main, ["x", "--check"])
        check(f"--check refuses {label}: exit 2, no traceback",
              code == 2 and want in text, f"exit {code}: {text.strip()[:120]}")
finally:
    css.SNAPSHOT = _real_snapshot

# ---------------------------------------------------------------------------
# 5. THE SPEC SURFACE EXIT CODES, at conjunct 5.
print("check-spec-surface.py exits 0, 1 and 2 where section 7.3 says")

clean_snapshot = tmp / "clean.toml"
clean_snapshot.write_text(css.render(live), encoding="utf-8")

moved = dict(live)
moved["declaration"] = [_weakened if d is _lem else d
                        for d in live["declaration"]]
moved_snapshot = tmp / "moved.toml"
moved_snapshot.write_text(css.render(moved), encoding="utf-8")

_real = css.SNAPSHOT
try:
    css.SNAPSHOT = clean_snapshot
    code, text = quiet(css.main, ["x", "--check"])
    check("--check exits 0 on an unchanged surface", code == 0, text)
    check("the clean line names the figures",
          "8 surface file(s)" in text and "499 in-fence lines" in text, text)

    css.SNAPSHOT = moved_snapshot
    code, text = quiet(css.main, ["x", "--check"])
    check("--check exits 1 when a declaration signature moved", code == 1, text)
    check("the failure names the declaration and both texts",
          "declaration changed" in text and "Type ℓ" in text, text)

    css.SNAPSHOT = tmp / "absent.toml"
    code, text = quiet(css.main, ["x", "--check"])
    check("--check exits 2 with no snapshot at all", code == 2, text)
finally:
    css.SNAPSHOT = _real

check("the trailer regex takes the dated, named form",
      bool(css.TRAILER_RE.search(
          "Spec-surface-approved: 2026-08-17 (choukh)\n")))
check("the trailer regex refuses an undated one",
      not css.TRAILER_RE.search("Spec-surface-approved: yes\n"))
check("R16 guards the design memo and the slot instructions",
      css.is_audited("dev/memos/LJ-4-pod-program-design.md")
      and css.is_audited("AGENTS.md")
      and css.is_audited("dev/pod/instructions/coder.md"))
check("R16 does not guard heads.toml: a role's model may move without this gate",
      not css.is_audited("dev/pod/heads.toml"))
check("R16 does not guard an unrelated file",
      not css.is_audited("src/L/Constructible.lagda.md"))

_audit = subprocess.run([sys.executable, "scripts/pod/check-spec-surface.py"],
                        cwd=ROOT, capture_output=True, text=True)
check("the history audit exits 0 and judges no pre-guard commit",
      _audit.returncode == 0, _audit.stdout + _audit.stderr)

# ---------------------------------------------------------------------------
# 6. THE COMMIT GATE READS THE INDEX, over ONE REAL REPOSITORY.
#
# THIS IS THE CASE THE OLD SUITE COULD NOT MAKE. It drove `--msg-file` against
# the working tree and staged nothing, so it passed while the hook asked the
# wrong tree and refused every commit in a repository whose memo had moved. A
# hook decides what the NEXT COMMIT may contain, so the test must stage.
print("check-spec-surface.py --msg-file judges the INDEX and not the disk")

FIXTURE = {
    "src/Landmarks.lagda.md": (
        "# Landmarks\n\n```agda\n{-# OPTIONS --safe #-}\nmodule Landmarks where\n"
        "\nopen import Base.Classical using (LEM)\nimport V.Model\n\n"
        "L⊨ZFC : isZFCModel\nL⊨ZFC = V.Model.L⊨ZFC\n```\n"),
    "src/Base/Classical.lagda.md": (
        "# Classical\n\n```agda\nmodule Base.Classical where\n\n"
        "LEM : ∀ ℓ → Type (ℓ-suc ℓ)\nLEM ℓ = (P : hProp ℓ) → ⟨ P ⟩\n```\n"),
    "src/V/Model.lagda.md": (
        "# Model\n\n```agda\nmodule V.Model where\n\n"
        "L⊨ZFC : isZFCModel\nL⊨ZFC = proof\n```\n"),
    "dev/memos/LJ-4-pod-program-design.md": "the rule home fixture\n",
    "AGENTS.md": "the shared Boundary\n",
    "dev/pod/heads.toml": 'mathematician = "opus"\n',
    "dev/pod/instructions/coder.md": "the coder slot\n",
}


def fixture_repo(where: Path):
    """One real git repository, with the gate inside it and one commit made.

    The gate finds its root by walking to `.git`, so a copy inside a throwaway
    repository guards that repository and nothing else
    (`scripts/repo_root.py`, and `[LJ-1.290]` measured the false green a
    hard-coded depth gives).
    """
    where.mkdir(parents=True, exist_ok=True)
    for rel, body in FIXTURE.items():
        p = where / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body, encoding="utf-8")
    (where / "scripts" / "pod").mkdir(parents=True, exist_ok=True)
    shutil.copy2(ROOT / "scripts" / "repo_root.py", where / "scripts")
    shutil.copy2(POD / "check-spec-surface.py", where / "scripts" / "pod")
    git("init", "-q", ".", cwd=where)
    module = load("css_fixture", "check-spec-surface.py",
                  where / "scripts" / "pod")
    quiet(module.main, ["x", "--write"])
    git("add", "-A", cwd=where)
    git("-c", "user.email=pod@test", "-c", "user.name=pod",
        "commit", "-q", "-m", "the fixture", cwd=where)
    return module


def git(*args, cwd: Path):
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                          text=True, check=True).stdout


repo = tmp / "repo"
fix = fixture_repo(repo)
msg_bad, msg_ok = repo / "msg-bad.txt", repo / "msg-ok.txt"
msg_bad.write_text("[LJ-4] a commit\n", encoding="utf-8")
msg_ok.write_text("[LJ-4] a commit\n\nSpec-surface-approved: 2026-08-17 (choukh)\n",
                  encoding="utf-8")

check("the fixture surface is Landmarks plus its one `open import`",
      fix.derive()["files"] == ["src/Landmarks.lagda.md",
                                "src/Base/Classical.lagda.md"],
      str(fix.derive()["files"]))
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_bad)])
check("a commit that stages nothing passes with no trailer", code == 0, text)

# The working tree moves and NOTHING is staged. The next commit does not carry
# the change, so the hook has nothing to refuse; `--check` still sees it.
weak = repo / "src" / "Base" / "Classical.lagda.md"
weak.write_text(FIXTURE["src/Base/Classical.lagda.md"].replace(
    "Type (ℓ-suc ℓ)", "Type ℓ"), encoding="utf-8")
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_bad)])
check("an UNSTAGED surface edit does not refuse the commit", code == 0, text)
code, text = quiet(fix.main, ["x", "--check"])
check("the same unstaged edit still fails --check, at acceptance",
      code == 1 and "declaration changed" in text, text)

git("add", "src/Base/Classical.lagda.md", cwd=repo)
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_bad)])
check("a STAGED surface edit refuses the commit with no trailer",
      code == 1 and "LEM" in text, text)
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_ok)])
check("the same staged edit passes with the trailer", code == 0, text)

git("reset", "-q", cwd=repo)
git("checkout", "--", "src/Base/Classical.lagda.md", cwd=repo)

# R16's own path: a rule home. The same split holds, and the staged case names
# the file (`check-agents-guard.py:120-133` is the copied shape).
agents = repo / "AGENTS.md"
agents.write_text("the shared Boundary, edited\n", encoding="utf-8")
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_bad)])
check("an UNSTAGED rule home edit does not refuse the commit", code == 0, text)
git("add", "AGENTS.md", cwd=repo)
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_bad)])
check("a STAGED rule home refuses the commit and names the file",
      code == 1 and "AGENTS.md" in text, text)
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_ok)])
check("a staged rule home passes with the trailer", code == 0, text)
git("reset", "-q", cwd=repo)
git("checkout", "--", "AGENTS.md", cwd=repo)

# Owner 2026-08-20: a role's model is not this gate. Staging heads.toml
# without the trailer must pass.
(repo / "dev" / "pod" / "heads.toml").write_text('coder = "grok"\n', encoding="utf-8")
git("add", "dev/pod/heads.toml", cwd=repo)
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_bad)])
check("a staged heads.toml does not refuse: role models are not R16",
      code == 0, text)
git("reset", "-q", cwd=repo)
git("checkout", "--", "dev/pod/heads.toml", cwd=repo)

# A staged snapshot with a wrong value type refuses through the INDEX reader
# too, with the same exit 2 and no traceback.
(repo / "dev" / "pod" / "spec-surface.toml").write_text(
    "files = 8\n", encoding="utf-8")
git("add", "dev/pod/spec-surface.toml", cwd=repo)
code, text = quiet(fix.main, ["x", "--msg-file", str(msg_bad)])
check("a staged snapshot with a wrong type exits 2, not a traceback",
      code == 2 and "must be a list of strings" in text, text)
git("reset", "-q", cwd=repo)
git("checkout", "--", "dev/pod/spec-surface.toml", cwd=repo)

# `--write` must work, because the owner regenerates the snapshot by hand after
# a ruling. It round-trips: write, then `--check` is clean.
weak.write_text(FIXTURE["src/Base/Classical.lagda.md"].replace(
    "Type (ℓ-suc ℓ)", "Type ℓ"), encoding="utf-8")
code, text = quiet(fix.main, ["x", "--write"])
check("--write exits 0 and names what it wrote",
      code == 0 and "wrote dev/pod/spec-surface.toml" in text, text)
code, text = quiet(fix.main, ["x", "--check"])
check("--check is clean against the snapshot --write just made",
      code == 0, text)
check("the rewritten snapshot carries the new type",
      "Type ℓ" in (repo / "dev" / "pod" / "spec-surface.toml").read_text(
          encoding="utf-8"))

# ---------------------------------------------------------------------------
# 7. THE SURVEY QUOTES, AD23 Part 2. The three verdicts and the exit codes.
print("check-survey-quotes.py keeps both gated halves")

BRIEF = """# LJ-1.999: a fixture

## ARCHIVE (program-generated, do not edit)

Corpus search for: isLayer
- CANDIDATE archive/dev/TASKS-archived.md
- CANDIDATE archive/dev/JOURNAL-archived.md

## THE REASONING

Nothing here is parsed.
"""

# `archive/dev/TASKS-archived.md:80` reads the T45 row and `:171` reads the
# T136 row, 91 lines away. The file is a frozen record, so a quote either sits
# at the cited line or it does not.
QUOTED = "L3.32-T45 | Bridge's two sequence residues | STOP"
ELSEWHERE = "L3.32-T136 | Build A text block: two atoms, two readings"
GOOD = """# Report

## ARCHIVE USED

- `archive/dev/TASKS-archived.md:80`: 「%s」. TOOK the shape only.
- `archive/dev/JOURNAL-archived.md`: NOT read, nothing in it bears.
""" % QUOTED

CASES = [
    ("a correct quote at the cited line passes", GOOD, 0, ""),
    ("an unanswered injected path fails", GOOD.replace(
        "- `archive/dev/JOURNAL-archived.md`: NOT read, nothing in it bears.\n",
        ""), 1, "unanswered"),
    ("a quote off by a few lines fails", GOOD.replace(":80", ":78"), 1,
     "off by a few lines"),
    ("a quote from elsewhere in the file fails",
     GOOD.replace(QUOTED, ELSEWHERE), 1, "quoted from elsewhere"),
    ("a quote the file does not hold fails",
     GOOD.replace(QUOTED, "the archive says the residue was green"), 1,
     "does not hold"),
    ("a return with no ARCHIVE USED heading fails",
     GOOD.replace("## ARCHIVE USED", "## WHAT I DID"), 1, "no-heading"),
    ("a file named as read with no quote fails",
     GOOD.replace("「%s」. " % QUOTED, ""), 1, "no-quote"),
    ("a written decline is compliance",
     GOOD.replace("「%s」. TOOK the shape only." % QUOTED,
                  "NOT read, and the brief's own reason stands."), 0, ""),
]

brief_path = tmp / "LJ-1.999.md"
brief_path.write_text(BRIEF, encoding="utf-8")
for label, report_text, want_code, want_word in CASES:
    report_path = tmp / "lj-1.999-report.md"
    report_path.write_text(report_text, encoding="utf-8")
    code, text = quiet(csq.main, ["x", "--brief", str(brief_path),
                                  "--report", str(report_path)])
    check(label, code == want_code and want_word in text,
          f"exit {code}: {text.strip()[:140]}")

code, text = quiet(csq.main, ["x", "--brief", str(brief_path),
                              "--report", str(tmp / "no-such-report.md")])
check("a missing file exits 2, an environment failure", code == 2, text)
code, text = quiet(csq.main, ["x", "--brief", str(brief_path)])
check("--brief without --report exits 2", code == 2, text)

# The design names one real return as the worked example of the quote duty.
_real_task = subprocess.run(
    [sys.executable, "scripts/pod/check-survey-quotes.py", "LJ-1.383"],
    cwd=ROOT, capture_output=True, text=True)
check("the real return of LJ-1-383 passes, as `check-dd18-survey.py` says",
      _real_task.returncode == 0, _real_task.stdout + _real_task.stderr)

# THE PROGRAM'S OWN BLOCK, read by the gate that judges the return. The two
# files meet here, and the provenance line is where they used to disagree: it
# names the CORPORA searched, and reading those as injected paths made the
# return decline by hand exactly what the program had already declined.
_gen_block = retr.candidate_block("ARCHIVE", "condensation isLayer residue",
                                  retr.ARCHIVE_SCOPE, 2)
_gen_paths = retr.OFFERED_LINE.findall(_gen_block)
# IT ASSERTS THE RELATION AND NOT THE COUNT. The point under test is that the block
# offers FEWER candidates than the provenance line names corpora, which is the gap the
# two files used to disagree about. Pinning `len(ARCHIVE_SCOPE) == 5` pinned a snapshot
# instead: backlog item 3 widened the scope on 2026-08-19, because 48 of the 152 archived
# files sat outside it, and this went red for a repair it does not test.
check("the block under test offers fewer candidates than the corpora searched",
      len(_gen_paths) == 2 and len(retr.ARCHIVE_SCOPE) > len(_gen_paths),
      f"{_gen_paths} of {len(retr.ARCHIVE_SCOPE)} corpora")
_gen_brief = tmp / "LJ-1.998.md"
_gen_brief.write_text("# LJ-1.998: a fixture\n\n" + _gen_block, encoding="utf-8")
_answer = ("# Report\n\n## ARCHIVE USED\n\n"
           + "".join(f"- `{p}`: NOT read, nothing in it bears.\n"
                     for p in _gen_paths))
_gen_report = tmp / "lj-1.998-report.md"
_gen_report.write_text(_answer, encoding="utf-8")
check("the answering report names no corpus the program declined",
      "dev/ARCHIVE.md" not in _answer)
code, text = quiet(csq.main, ["x", "--brief", str(_gen_brief),
                              "--report", str(_gen_report)])
check("answering every CANDIDATE is enough for a program-generated block",
      code == 0, text)
_gen_report.write_text(_answer.replace(f"- `{_gen_paths[0]}`", "- `dev/ARCHIVE.md`"),
                       encoding="utf-8")
code, text = quiet(csq.main, ["x", "--brief", str(_gen_brief),
                              "--report", str(_gen_report)])
check("a CANDIDATE the return never names is still unanswered",
      code == 1 and "unanswered" in text and _gen_paths[0] in text, text)

check("WINDOW is 3 lines of slack, as section 7.4 rules", csq.WINDOW == 3)
check("answered() takes a deeper path and refuses a vaguer parent",
      csq.answered("archive/src", {"archive/src/2026-08-09-rud-route/x.md"})
      and not csq.answered("archive/src/x/y.md", {"archive/src"}))

# ---------------------------------------------------------------------------
shutil.rmtree(tmp, ignore_errors=True)

if failures:
    print(f"FAIL: {len(failures)} check(s) failed")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("test_pod_gates: all checks passed")
