# LJ-1.291: repair the 24 scripts that hard-code their own depth

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch_policy.py` before writing this line and took the head it
gave**: `pi-subagent-mode` is IN FORCE, PINNED by the owner 2026-08-15, and
the default case is `herdr` / `pi` / `glm-5.3`.

## GOAL

**24 of the 34 scripts compute the repository root as
`Path(__file__).resolve().parent.parent`. That is a hard-coded DEPTH, and it is
a silent failure waiting for the first directory change.**

`[LJ-1.290]` found it while planning a `scripts/` reorganisation. **I reproduced
it myself before writing this brief**, by copying one gate one level deeper
inside the repository and running it unchanged:

```
check-probes: clean (  55 tracked files, ...)   <- the copy, one level deeper
check-probes: clean (2369 tracked files, ...)   <- the real one
```

**Both exit 0. Both say `clean`. One guarded 2,369 files and the other guarded
55.** Nothing in the exit code says which.

**Repair the anchor so a script finds the root by WALKING UP to a marker,
never by counting directories.**

## PREMISES

- **24 scripts contain `parent.parent`**, by `grep -l "parent.parent" scripts/*.py | wc -l`.
  **RE-DERIVE IT.** Some may be unrelated uses; count the ones that compute a ROOT.
- **`scripts/check-probes.py:53` and `scripts/check-live-territory.py:68` both
  read `ROOT = Path(__file__).resolve().parent.parent`**, and both are
  never-commit gates. VERIFY.
- **`scripts/check-agents-guard.py:47` self-anchors on its own path**, per
  `[LJ-1.290]`. **A wrong root there flips it from a real finding to
  `0 guarded commit(s)` and exit 0.** VERIFY, and treat it as the sharpest case.
- **`scripts/check-rule-ids.py:308` uses a NON-RECURSIVE glob**, per
  `[LJ-1.290]`, so a deeper layout would scan almost nothing and still pass.
  **That is a second failure of the same family and it is in scope.**
- **`scripts/dispatch_policy.py` and `scripts/agents_tree.py` are imported by
  other scripts and by the untracked `.claude/skills/codex-dispatch/dispatch.py`
  at `:112-113` and `:124`.** **Do not change how they are IMPORTED**, only how
  they find the root.

## WHAT TO DO

**Give every root-computing script one shared way to find the root: walk up
from `__file__` until a marker is found.** `.git` is one candidate and
`AGENTS.md` is another; **pick one, say why, and use it everywhere.** A script
that cannot find the marker must **fail loudly**, never fall back to a guess
(C-43).

**Where the helper lives is your call and it has a constraint:**
`scripts/agents_tree.py` already exists as a shared module, and DD19 forbids a
rule being canonical twice. **Say where you put it and why that is not a second
home for something that already has one.**

## THE ACCEPTANCE BAR: EVERY GATE COUNTS THE SAME THINGS AS BEFORE

**Capture the current output of every checker BEFORE you edit**, and diff after.
`[LJ-1.290]` measured that 24 of 25 checkers and 16 of 16 test suites reproduce
their baseline; you must not be the one that breaks the twenty-fifth.

**Then prove the repair does what it is for:** copy a repaired gate one level
deeper inside the repository, run it unchanged, and show it reports the SAME
count as the original. **That test is the whole point of the task.** Delete the
copy afterwards.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **EVERY GATE MATCHES ITS BASELINE AND THE DEPTH TEST PASSES.** Report both.
  STOP.
- **A SCRIPT CANNOT USE THE SHARED ANCHOR.** Name it and why. **Some scripts are
  run from odd places and a marker walk may not reach.** Say so rather than
  forcing it.
- **A BASELINE DOES NOT REPRODUCE EVEN BEFORE YOUR EDIT.** **That is a finding
  and it is not yours.** Report it and continue with the rest.
- **THE REPAIR CHANGES A COUNT.** Stop. A gate that guards a different number of
  files after a refactor is the exact defect this task exists to remove.

## WHAT YOU MUST NOT DO

- **DO NOT MOVE, RENAME OR DELETE ANY FILE UNDER `scripts/`.** This task repairs
  anchors. **The reorganisation is a separate decision the owner has not made.**
- **DO NOT EDIT** `AGENTS.md`, `CLAUDE.md`, `dev/PLAN.md`, `dev/vendors.toml`,
  anything under `src/`, anything under `.claude/`, or another task directory.
  **`.claude/skills/codex-dispatch/dispatch.py` imports two of your files: if it
  needs a change, say so and I make it.**
- **DO NOT RUN AGDA.** No task here needs it.
- **Do not run `make check`**; I run it.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- **Create `agents/tasks/LJ-1-291/lj-1.291-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report. **No em
  dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**C-43. An escape hatch is the shape a wrong choice hides in.** A root fallback
that guesses is that shape. **A gate that says `clean` over 55 files is that
shape already.**

**C-48, written 2026-08-15. A policy that only a document states is not
enforced, and a tool that can read a condition must refuse on it.** A script CAN
read whether it found its marker. It must refuse when it did not.

**C-44.** Every number in this brief is mine or `[LJ-1.290]`'s and you must
re-derive each one.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. This task writes no mathematics, so DD4 does not
bind its content. It binds its shape, and the connection is exact: 24 scripts
each solved the same problem separately, and this task writes it once. **Say in
one line whether a new script would get the anchor for free or would have to
remember it, and name the enforcement point if there is one.**

## ARCHIVE (DD18)

`agents/tasks/LJ-1-290/lj-1.290-report.md` read WHOLE: the depth finding, the
three named failure sites, and the taxonomy work that is NOT this task.
`archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

No mathematical literature bears on a path anchor. Say so in one line and return
a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-290/lj-1.290-report.md` FIRST, whole.

## SCOPE (write)

`scripts/` (edits to existing files ONLY, no moves) and
`agents/tasks/LJ-1-291/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **C-42.** A refutation measures the site it names. **`[LJ-1.290]` named three
  sites; the sweep for the rest is yours.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.
- **P-l.** A judgement at one site is a hypothesis at another.
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-32, C-36, C-38, C-39, C-40, C-43, C-44, C-45, C-46, C-48. I-5. DD0, DD4,
  DD8, DD18, DD19, DD24.**

## CONSTRAINTS

- Run every checker you touch and diff against the baseline you captured.
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the count of scripts repaired and the depth test's two numbers,
which must now agree.** Then every checker's baseline against its post-edit
output. Then where you put the shared anchor and why it is not a second home.
Then any script that could not use it. Then whether a new script gets the anchor
for free. **Mark every negative MEASURED or INFERRED.**
