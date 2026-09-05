# [LJ-1.612] report: the rehoming defect, re-measured at its own site and repaired with the flags

tier: probe. **No master was edited. Nothing landed in `src/`. No
commit, no push.** The obligation
`agents/tasks/LJ-1-612/Probe612.agda::rehomed-import-works` is
delivered and green (runs/final-2.out, cold re-elaboration).

**STATUS: GO.** The symptom reproduces at this tree (runs/w3-1.out),
the library path itself is measured shut (runs/dot-1.out), the flag
cure is measured green, warm and cold (runs/w3-2.out,
runs/final-2.out), and the affected count is in the section
**HOW MANY PROBES ARE AFFECTED** (53 live, 216 archive, 269 total).

A note on the predecessor before the ledger: [LJ-1.607] is NO-GO on
its own obligation `band-untruncation`, and this task does NOT take a
module hypothesis from it. What this task takes is a separate
plumbing observation the 607 report makes at
agents/tasks/LJ-1-607/lj-1.607-report.md:200-205, and it is
reproduced here independently (runs/w3-1.out) before anything is
claimed cured.

## 1. THE RUN LEDGER

One agda process at a time. The caliber is the program's, on this
pane: `GHCRTS=-A64m -I0 -M2g`, recorded in every `.out`. Nothing in
this task sets it. The wrapper is runs/run.sh, the [LJ-1.605]
mechanism taken in via [LJ-1.607]'s copy, with the agda arguments
passed through so a run can add `-i` include roots.

| run | file | cap | result |
|---|---|---|---|
| runs/w3-0.out | runs/W3.agda, first attempt, headerless | 60 s | EXIT 42, 0.22 s. [ModuleNameDoesntMatchFileName]: a headerless file is refused before the import is reached (w3-0.out:5-8) |
| runs/w3-1.out | runs/W3.agda | 60 s | EXIT 42, 0.23 s. [FileNotFound] for `ProbeLJ1136B` (w3-1.out:5-16). **THE SYMPTOM, AT THIS TREE** |
| runs/dot-1.out | runs/DotW3.agda, the library-path import | 600 s | EXIT 42, 0.09 s. [ModuleNameUnexpected] (dot-1.out:6-8): the file is found and its path name refused |
| runs/w3-flagrel-1.out | W3.agda, `-i ../LJ-1-136` from runs/ | 60 s | EXIT 42. The search list at w3-flagrel-1.out:16-17 shows the flag resolved against the CWD, and the directory does not exist there |
| runs/w3-2.out | W3.agda, `-i ../../LJ-1-136 -i ../../LJ-1-134` from runs/ | 600 s | **EXIT 0, 1.37 s, 349 MB peak** |
| runs/w3-flagrel-2.out | W3.agda, `-i agents/tasks/LJ-1-136` from the root | 60 s | EXIT 0. Together with the row above: `-i` paths resolve against the CWD |
| runs/final-1.out | Probe612.agda, the two flags | 600 s | **EXIT 0, 1.58 s, 351 MB peak** |
| runs/final-2.out | Probe612.agda, the two flags, after deleting the two probe `.agdai` files | 600 s | **EXIT 0, 2.35 s, 384 MB peak. Cold: `Checking ProbeLJ1136B` then `Checking ProbeLJ1134A` re-elaborated from source (final-2.out:4-5)** |

THE CACHE CONTEXT, MEASURED, because it decides which numbers mean
what: this worktree arrived pre-seeded with 704 `.agdai` files under
`_build/2.8.0/agda/` dated 2026-08-11 to 2026-08-19, including the
rehomed probe's own interface of 2026-08-19 (the date [LJ-1.607]
recorded for it). So w3-2 and final-1 VALIDATED the cached interface;
final-2 is the true re-elaboration, and it is the number the repair
carries.

## 2. THE SYMPTOM AND THE CURE

THE SYMPTOM, at file:line. The library's include roots are
`src` and `agents/tasks` (bedrock.agda-lib:2, `include: src
agents/tasks`). The rehomed probe's file sits one directory below the
second root, agents/tasks/LJ-1-136/ProbeLJ1136B.agda, and its
declared top module name is still the flat pre-rehome name
`ProbeLJ1136B` (agents/tasks/LJ-1-136/ProbeLJ1136B.agda:35). The two
import directions fail in two different ways, both measured here:

- import by the declared name: [FileNotFound], the search list covers
  `src/` and `agents/tasks/` and nothing under `LJ-1-136/`
  (runs/w3-1.out:5-16; [LJ-1.607]'s copy is
  agents/tasks/LJ-1-607/runs/p136-1.out:5-15 in the main tree);
- import by the path name `LJ-1-136.ProbeLJ1136B`: the file IS found
  (runs/dot-1.out:5) and then refused: "The module ProbeLJ1136B
  should probably be named LJ-1-136.ProbeLJ1136B" (dot-1.out:6-8).

The defect is in the declaration, not in the search path: a path
rename alone cannot close it.

THE CURE USED IS THE FLAGS, not a copy. The green runs are invoked
with `-i agents/tasks/LJ-1-136 -i agents/tasks/LJ-1-134` (CWD-
relative; runs/ uses `../../LJ-1-136`). Both roots are part of the
cure: ProbeLJ1136B imports its rehomed dependency ProbeLJ1134A by its
flat name (agents/tasks/LJ-1-136/ProbeLJ1136B.agda:48-49), so the
second root restores that edge too. Result: the probe is imported in
place, no line of it duplicated, its file untouched
(runs/w3-2.out EXIT 0; runs/final-2.out EXIT 0 cold).

THE COPY CURE, for the record: [LJ-1.607] copied both probe files
VERBATIM into its runs/cold/ directory (agents/tasks/LJ-1-607/
runs/cold/P136Cold.agda:1-18; the run is agents/tasks/LJ-1-607/
runs/p136-cold-1.out:5-6, green at 1.83 s, 327 MB). That technique
exists to defeat interface-cache validation, and as a standing fix it
duplicates content. R-42 (dev/LESSONS.md:4882; the brief cited
:4404, which sits inside C-53) prices carrying one object across two
files at 155.02 s against 1.74 s, and a copy also goes stale when
the original moves. The flags import in place; the flags are used.

A SECOND QUirk, MEASURED, for whoever wires this up next: agda
resolves `-i` paths against the CURRENT WORKING DIRECTORY, and a
headerless probe file is refused before any import is reached
(runs/w3-0.out:5-8; runs/w3-flagrel-1.out:16-17;
runs/w3-flagrel-2.out).

## 3. W3, THE WIDEST UNMEASURED TERM

The W3 was the failing import itself, written first as runs/W3.agda
(about 19 lines, the obligation's eight-line core is the import), and
typechecked alone. It did NOT import cleanly: runs/w3-1.out, exit 42,
the symptom at this tree. The brief's one-minute cap was applied to
the symptom run; the green verification and the cold run ran at the
campaign's 600 s cap and landed at 1.37 s and 2.35 s, both inside a
minute.

## 4. THE OBLIGATION

`rehomed-import-works` (agents/tasks/LJ-1-612/Probe612.agda:65-66)
takes two proofs of non-emptiness inside the probe's `Sel` module and
returns the equality the probe's `pick h₁ ≡ pick h₂` demands. The term
on the right is `pick-canonical`, defined in the rehomed probe at
agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114-116, re-ascribed here
through the import at Probe612.agda:47. Imported and used: the probe
is the source, this file is the use, and the probe file is byte-
identical to before this task.

## 5. HOW MANY PROBES AFFECTED

THE PROPERTY, IN WORDS (C-42): a tracked `.agda` file under
agents/tasks/ is affected iff its declared top-level module name does
not spell the name its path gives it under the library's include root
agents/tasks/. For such a file, import by the declared name fails
[FileNotFound] and import by the path name fails
[ModuleNameUnexpected]: the two directions measured in section 2,
generalized. Files without any top-level declaration are a second,
separate shape (runs/w3-0.out).

THE SWEEP: runs/sweep.py compares, for every `.agda` file under
agents/tasks/, the first column-0 `module` line that is not a
`module X =` alias against the dotted path name. The full output is
runs/affected.out; no count below comes from a command containing
head.

- **269 affected** (declared name ≠ path name): **53 live, 216
  archive**, out of 971 files scanned.
- The 53 live files are 45 flat-named rehome probes in the measured
  shape (LJ-1-90 through LJ-1-235, including the site this task
  repaired, LJ-1-136) and 8 files of other mismatch shapes:
  LJ-1-142/NAMETEST-L3.32-DOT/ProbeNameNegDot.agda,
  LJ-1-142/NAMETEST-L3_32_UNDERSCORE/ProbeNameNegUnd.agda,
  LJ-1-213/GenPowersetMasterBody.agda, LJ-1-238/_Header.agda,
  LJ-1-238/_SeqBody.agda, LJ-1-238/_SeqBodyRaw.agda,
  LJ-1-299/ParseCheckOrch.agda, LJ-1-336/head336.agda.
- THE WEAKER FILTER (a flat, single-component declaration, without
  checking the path): 262 (47 live, 215 archive). Its blind spot is
  the 7 files whose stale declaration carries dots, which the flat-
  name heuristic cannot see (runs/affected.out, last section).
- One live file is headerless, LJ-1-238/_SeqBodyIndent.agda, the
  second shape; it is not counted in the 53.
- The count is a measurement of the un-importable SHAPE at today's
  tree. It does not assert that all 269 were ever imported, and it
  does not fix them: this task priced the cure at one site. The W4
  pass [LJ-1.607] predicted at
  agents/tasks/LJ-1-607/lj-1.607-report.md:200-205 takes this count
  as its row.

## 6. THE PREMISES, VERIFIED AND CORRECTED

1. [LJ-1.607] names the defect. CONFIRMED, with two corrections:
   the task directory of 607 is NOT in this worktree; 607 expired
   (commit 2560b303) and its directory sits UNTRACKED in the main
   tree, read here read-only. The defect bullet is at
   lj-1.607-report.md:200-205; the brief cited :186, which is a blank
   line. Content matches the brief's quote.
2. runs/cold/P136Cold.agda:1 CONFIRMED: the verbatim-copy header.
3. The cold cure CONFIRMED at runs/p136-cold-1.out:5-8 (green,
   1.83 s, 327 MB).
4. [LJ-1.160]'s precedent CONFIRMED: the `crossOut` parameter at
   agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71.
5. [LJ-1.572]'s recovered stop CONFIRMED at line 1 of its review
   ("the obligation is not delivered, and the brief's premise is
   inverted"); the 572 directory is likewise untracked in the main
   tree, not in this worktree.
6. R-42 CONFIRMED at dev/LESSONS.md:4882-4900, with the 1.74 s /
   155.02 s figures; the brief cited :4404, which sits inside C-53.
   Line drift, content as cited.
7. [LJ-1.559]'s re-measured floor CONFIRMED at its report line 1.
8-12. AGENTS.md clauses. Observed: no generated file enters the
   tree, `_build/` untouched by this task (the worktree's pre-
   seeded interfaces are the pod's), no commit, no push.

## 7. W2, ANSWERED

The mathematics here is import plumbing, not a theorem: the
obligation re-instantiates a term a predecessor already wrote, and
sharing is the mechanism of the repair itself. W2 holds by
construction; nothing had to be written once for the two towers,
because nothing was written at all. No deadline conflict arose.

W4 does not arise in this task: no module is retired, and the W4
pass the direction queues after LJ-1 receives the section-5 count as
its input, not a repair from this task.

## 8. SCOPE AND COMPLIANCE

Written, in scope only: Probe612.agda, lj-1.612-report.md,
runs/W3.agda, runs/DotW3.agda, runs/run.sh, runs/sweep.py,
runs/affected.out, and the eight `.out` files of the ledger.
`review-of-rehomed-import.md` is NOT written: the task is a GO, and
that file is the NO-GO channel. No existing probe was edited: the
136, 134, 607 and 572 files were read, and 607's and 572's are read
from the main tree because this worktree predates them. No
postulate. The `.venv` this task created is a Python 3.11.16 venv
with no packages added (the worktree ships without one, and the
sweep script needs only the standard library); git ignores it. The
ratio bar cannot fire on this write scope: raw `.agda` probes carry
no in-fence lines.

## ARCHIVE USED

- `archive/dev/JOURNAL.md` — read. Line 879, the `[LJ-1.227]` entry
  the 607 report cited: "I moved all three into
  `agents/tasks/LJ-1-134/` and `agents/tasks/LJ-1-136/` and tracked
  them, which" — the rehome that left the flat declaration behind,
  the defect's origin.
- `archive/dev/LJ-dispatch-index.md` — not read, declined: a
  dispatch history; this task's provenance is the live files it
  measured.
- `archive/dev/JOURNAL-archived.md` — not read, declined: the same
  reason.
- `archive/dev/ORCHESTRATION.md` — not read, declined: orchestration
  history, no bearing on the import defect.
- `archive/dev/DD-archived.md` — not read, declined: retired rulings,
  none of which this task touches.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md` — not read, declined:
  [LJ-1.607] cited its Theorem 16 for the untruncation round, which
  is closed and not this task; the import defect sits below the
  mathematics.
- `dev/literature/digest.md` — not read, declined: no bearing.
- `dev/literature/devlin-II5.md` — not read, declined: no bearing.
- `dev/literature/terms-2026-08.md` — not read, declined: no bearing.
- `dev/literature/level-formula-slot-roles.md` — not read, declined:
  no bearing.
