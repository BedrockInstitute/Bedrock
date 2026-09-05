# [LJ-1.701] Free LJ-1.636's delivered work from its park

**GO.** `param-at-omega` is built and green. It is one term at
`agents/tasks/LJ-1-701/Probe701.agda:64-66`. It has no hole and no
postulate. The file declares `--safe`.

One green run of the final file: `runs/final-1.out` at 1.67 s real,
`EXIT=0`, maximum resident set size 373850112 bytes
(`agents/tasks/LJ-1-701/runs/final-1.out:5-6` and `:23`). The caliber is
the one the program set on this pane (`GHCRTS=[-A64m -I0 -M2g]`). I did
not set it. One Agda process at a time.

**There is no heap wall.** No wall occurred at any point in this dispatch.

Nothing landed in `src/`. I did not write
`agents/tasks/LJ-1-701/review-of-param-at-omega.md`. I did not touch
`agents/tasks/LJ-1-636/Probe636.agda`,
`agents/tasks/LJ-1-636/lj-1.636-report.md`, or any `.out` file.

## 1. THE ANSWER

**The predecessor type re-derives outside its own probe, from `squareω`
alone.**

The predecessor report is **GO**, not NO-GO, and it does not name the
statement false. `agents/tasks/LJ-1-636/lj-1.636-report.md:3-5` reads
that the census is built and green with no hole and no postulate. The
type I took is the one that typechecked there:
`param-at-ω : SqParam ω` at `Probe636.agda:391-392`, whose body is
`subst Sq` along `collapse-at-ω` applied to `squareω`. The brief's
obligation name is the ASCII form `param-at-omega`. I inhabited that
name. I did not inhabit a different type.

`collapse-at-ω` is five lines at `Probe701.agda:56-60`. It is
`∈sucV-elim` with `Empty.rec` on the left limb, copied from
`Probe636.agda:377-381`. `param-at-omega` is two lines at
`Probe701.agda:64-66`, copied from `Probe636.agda:391-392` with the
identifier renamed to the obligation name.

The shape did not resist. I did not weaken the type. I closed the
obligation.

## 2. W3. WHETHER `squareω` IS IN SCOPE CHEAPLY

**Yes.** The brief estimated 10 to 40 lines. The floor that imports
`squareω` and names it at `Sq ω` is 37 lines
(`agents/tasks/LJ-1-701/runs/Floor.agda.txt`). The measured price, not
the guess, is 1.91 s real, `EXIT=0`, maximum resident set size
375963648 bytes (`agents/tasks/LJ-1-701/runs/floor-1.out:5-6` and
`:23`), under the same caliber.

`delivered-at-ω : Sq ω` at `Probe701.agda:51-52` is `squareω`, the same
inhabitant as `Probe636.agda:100-101`. It typechecks only because the
parameter's value type at `ω` and `src/L/InjChain.lagda.md:184` are the
same type on the nose.

The full obligation, with `collapse-at-ω` and `param-at-omega` on top of
that floor, is 1.67 s real (`runs/final-1.out:5`). Both runs said
`Checking` their own module, with warm `L.InjChain` interfaces already
in `_build/`. The collapse is lost in cache noise. **The import of
`squareω` is the whole price of this miniature.** It is cheaper here
than inside [LJ-1.636]'s census probe (that report's green runs were
4.11 s, 3.49 s and 3.67 s at `lj-1.636-report.md:6-7`).

I then renamed `runs/Floor.agda` to `runs/Floor.agda.txt`, so conjunct 1
of THIS task sees one `.agda` file, `Probe701.agda`. The floor
typechecks. The rename is the lesson this task exists to land: a scratch
file under the task home is a conjunct-1 target if it keeps the `.agda`
suffix.

## 3. THE FILE REPAIR

I renamed every `.agda` file under `agents/tasks/LJ-1-636/runs/` to the
same name with `.agda.txt`. Seventeen files: `Bisect1` to `Bisect9`,
`BisectB` to `BisectF`, `Floor`, `Warm1` and `Warm2`. Content did not
change. No `.out` file changed. `Probe636.agda` was not renamed.

[LJ-1.636] is parked and not in git. The live copy sits in the sibling
worktree
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-636`
and a second untracked copy sits in the main tree. I renamed in both,
and I placed the seventeen `.agda.txt` files under this worktree's
`agents/tasks/LJ-1-636/runs/` so the `ls` command below is a command in
THIS tree. `Probe636.agda` in the parked worktree still exists and
compares identical to the main-tree copy.

The predecessor report says the walled runs are the superseded shape,
not the deliverable (`lj-1.636-report.md:9-14`). After the rename, the
only `.agda` file under that task home is the deliverable.

Output of `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-636`:

```
check-survey-quotes: LJ-1-636 clean (0 note(s), 0 defect(s))
```

Output of `ls agents/tasks/LJ-1-636/runs/*.agda`:

```
ls: agents/tasks/LJ-1-636/runs/*.agda: No such file or directory
```

That `ls` finds nothing. Conjunct 6 of [LJ-1.636] still holds.

## 4. WHAT THE NEXT BRIEF NEEDS

**This task does not close [LJ-1.636].** The term now lives in a home
that can close, `Probe701.agda`. The parked task's conjunct-1 cause is
removed: its `runs/` directory holds no `.agda` file. A later arm that
re-accepts [LJ-1.636] in its own worktree should see only
`Probe636.agda` as a conjunct-1 target.

**What I could not close.** I could not commit [LJ-1.636]. The program
commits only at a `done` close, and this dispatch is [LJ-1.701]. The
parked worktree still holds `Probe636.agda` and its report as untracked
files. They are not on this branch.

**No residue on the term.** `param-at-omega` is untruncated, uses one
inhabitant already in the tree, and needs no further lemma.

## 5. CLAUSES

- **W2 (generic carrier).** Answered and not violated. This task writes
  no mathematics into `src/`. `collapse-at-ω` is one use of
  `∈sucV-elim` (`src/V/Model.lagda.md:218-219`) at carrier `ω`. The
  square-law inhabitant is `squareω`, already defined once. I did not
  write a fixed-form duplicate.
- **W4 (retirement).** No module was retired and `dev/ARCHIVE.md` needs
  no row.
- **RATIO BAR.** Not applicable. `Probe701.agda` is a raw `.agda` file
  and carries no ` ```agda ` fence, so its in-fence line count is 0.
- **CALIBER.** `GHCRTS=[-A64m -I0 -M2g]`, set by the program on this
  pane. I did not set it. Every `.out` records it. One Agda process at
  a time throughout.
- **PROBE LOCATION.** `agents/tasks/LJ-1-701/Probe701.agda`, with its
  runs in `agents/tasks/LJ-1-701/runs/`. Nothing in `src/`.
- **DIRECTION.** The standing direction is one SRC collection after
  LJ-1, not after `[LJ-2.5]`. This task writes no `src/` file, so it
  does not start that collection and it does not conflict with a
  Boundary clause.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md` **not read, declined.** This task
  re-derives a two-line term and renames scratch files. It is not a
  process-design question.
- `archive/dev/PLAN-archived.md` **not read, declined.** The live
  screen is `dev/pod/screen.toml`. The archived plan is not this
  obligation.
- `archive/dev/DD-archived.md` **not read, declined.** The live rulings
  are `dev/pod/rulings.toml`. No archived DD is this term.
- `archive/dev/TASKS-archived.md` **not read, declined.** The live
  producer is `dev/pod/queue.toml`. The archived task list is not this
  repair.
- `archive/dev/STATUS-archived.md` **not read, declined.** The live
  standing status is the screen. The archived status file is not this
  measurement.

## LITERATURE USED

- `dev/literature/primary-sources.md` **not read, declined.** The
  inhabitant is `squareω` already in the tree. No primary-source
  question arose.
- `dev/literature/glossary-review-2026-08.md` **not read, declined.**
  I added no glossary entry and named no new term.
- `dev/literature/level-formula-slot-roles.md` **not read, declined.**
  This obligation is a square-law parameter at `ω`, not a level-formula
  slot.
- `dev/literature/formalizations-landscape.md` **not read, declined.**
  The type is the predecessor's type. No landscape comparison arose.
- `dev/literature/BIBLIOGRAPHY.md` **not read, declined.** No citation
  from the bibliography was needed to inhabit `SqParam ω`.

## 6. FILES

- `agents/tasks/LJ-1-701/Probe701.agda` (66 lines) the obligation
- `agents/tasks/LJ-1-701/runs/Floor.agda.txt` the floor, section 2
- `agents/tasks/LJ-1-701/runs/run.sh` the run wrapper
- `agents/tasks/LJ-1-701/runs/floor-1.out` **the floor, 1.91 s**
- `agents/tasks/LJ-1-701/runs/final-1.out` **the price, 1.67 s**
- `agents/tasks/LJ-1-636/runs/*.agda.txt` the seventeen renamed scratch
  files (this worktree copy)
