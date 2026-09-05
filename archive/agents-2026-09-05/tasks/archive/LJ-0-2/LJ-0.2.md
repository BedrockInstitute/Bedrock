# LJ-0.2: sufficiency audit of the route switch

tier: codex (default)

## GOAL

Find what the route switch has NOT yet reached. Name each document and each
section that must still change, so the two-tower bridge route can execute.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## CONTEXT

On 2026-08-09 the owner changed the route. The old route was internalization,
and its goal was `L ⊨ AC`. The new route is the two-tower bridge: build the L
tower, build the J tower through rud, build the bridge between them, and prove
BOTH `L ⊨ AC` and `L ⊨ GCH` on it. Read `dev/PLAN.md` section 3 rows DD2 and
DD5 for the ruling.

Thirteen commits then applied the switch. They did six things at once:

1. They archived the whole `D` decision series and rebuilt it as 15 `DD` rows.
2. They archived 264 `L3.32-T` task codes and rebuilt the index as `LJ-x.y`.
3. They archived the 4,260-line journal and reopened an empty one.
4. They restored `src/` to the internalization tree and archived the 72
   differing files to `archive/rud-route/`.
5. They suspended three ledger thresholds behind flags, because the new
   constraints are relative and nobody has measured them yet.
6. They added `scripts/check-ratio.py` for DD24's seconds-per-line bar.

## WHAT THIS TASK IS, AND WHAT IT IS NOT

A sibling task, LJ-0.1, already audited these commits for CONSISTENCY: what
contradicts, what dangles, what claims an enforcement it does not have. It
found 30 defects and its report is at `_build/lj-0.1-consistency.md`. **Read
that report first, and do not repeat its findings.** Anything already in it is
out of scope for you.

**Your question is the opposite one: what is MISSING?** A document can be
perfectly self-consistent and still describe a route nobody is walking. Look
for the sections that were never touched because nobody thought of them, not
for the sections that were touched wrongly.

## THE CHECK CLASSES

Work through these. Each one asks "what does the new route need that is not
there yet?"

**S1. Documents the switch never opened.** Thirteen commits touched 98 files.
Get that list with `git diff --name-only faf02fca8720fd7bfc6dacb7c9e07dfba3aafe0d..HEAD`.
Then find every developer document and every `README.md` that the switch did
NOT touch, and judge each one: does it describe the retired route, or is it
route-neutral? A file that says nothing about the route is fine. A file that
silently assumes internalization is a defect. `dev/README.md` and
`scripts/README.md` are known unreviewed; there will be others.

**S2. Sections inside touched files that the switch skipped.** A commit that
fixed a file's citations may have left its content on the old route. Check
`dev/PLAN.md` section by section, and `dev/ORCHESTRATION.md` section by
section. Name each section whose SUBJECT is now retired.

**S3. Machinery the new route needs and does not have.** The new route has
parts the old one did not: a J tower, a bridge, a shared core the two proofs
both use, and a reuse measurement that says how much they share. Ask what
document should carry each, and whether it exists. DD2's core constraint is
"maximize the code the two proofs share" and nothing measures sharing today.

**S4. Rules with no home.** The consolidation merged 25 rows into 15. Compare
`dev/DECISIONS-archived.md` against `dev/PLAN.md` section 3 and find rules
that the old route enforced, that the new route still needs, and that no
current DD row states. **Two are already known and repaired, so skip them:**
the emergency dispatch tier and the glossary pipeline's tiers.

**S5. Checkers the new route needs.** `scripts/` has checkers built for the
old route's thresholds. Which invariant of the NEW route has no checker at
all? Name the checker that should exist and what it would read.

**S6. The phase-1 starting line.** `dev/PLAN.md` section 11 lists `LJ-1.1`
through `LJ-1.9`, an internalization GCH wing. Read those rows and say what a
build agent would still have to ask before it could start `LJ-1.1`. That is
the practical test of whether the switch is finished.

## ARCHIVE

Per DD19, this brief names what may bear on the task. You must read:

- `dev/DECISIONS-archived.md`. Required for S4. It is the only record of what
  the retired route's rulings said, so it is the only way to see a rule the
  consolidation dropped.
- `dev/TASKS-archived.md`. 264 dispatch rows. Useful for S3: the retired route
  attempted a J tower and a bridge, and these rows say what was tried.
- `archive/rud-route/README.md`. Names four things worth knowing about the
  retired code, including which modules carried the generic machinery.
- `dev/JOURNAL-archived.md`. 4,260 lines. Consult it only when S3 or S4 turns
  up a question the other three cannot answer; do not read it through.
- `dev/LESSONS.md` is NOT archived and still binds.

Your report must carry an **ARCHIVE USED** section naming what you actually
read and what you took from each, at `file:line`. "I looked at the archive" is
not a return. If you read none of it, say why.

## SCOPE (read)

In this order: `dev/PLAN.md`, `dev/ORCHESTRATION.md`, `AGENTS.md`,
`_build/lj-0.1-consistency.md`, `dev/ledger.toml`, `scripts/README.md`,
`dev/README.md`, `README.md`, then `scripts/*.py` as the classes require, then
the four archives above.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. These bind this task.

- **D-10. Price the truth of a recorded residue before pricing its proof.** A
  residue recorded under the wall protocol names a TARGET, and a target can be
  false. Before dispatching a discharge batch, spend the five minutes checking
  the target's truth at the intended generality; a Tarskian or cardinality
  obstruction is the usual killer. Record the corrected target beside the
  original. **For you:** an archived task row that names an unfinished target
  is not evidence that the target is true. Say so when you cite one.
- **C-22. A dispatched agent writes its deliverable incrementally, never at
  the end.** Write the report EARLY as a skeleton and fill it as each answer
  lands, saving each time. An agent that researches for its whole budget and
  leaves the writing to the end returns nothing when the budget runs out. A
  partial report is a real deliverable; an unwritten perfect one is not.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Being about a concrete position is not
  what costs; naming a transparent construction in a statement's TYPE is. If
  stage values are `opaque` upstream, a theorem may quantify over them freely,
  because the stage is an ATOM to the elaborator and nothing unfolds.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** Ask first what a stage's members CARRY. A stage built as the values
  of finitely many total operations carries its own generation data, so a
  well-founded key exists with no syntax at all: the operation index, then the
  arguments, ordered recursively. A stage built as a definable power carries
  nothing. **For you:** this is the fault line between the J tower and the L
  tower, so it bears directly on S3.

## SCOPE (write)

`_build/lj-0.2-sufficiency.md` and nothing else.

## CONSTRAINTS

- **Do not edit any file except your report.** Do not commit. Do not push.
- **Do not run `agda` and do not run `make check`.** A typecheck takes twelve
  minutes and another process may be using the machine.
- **Evidence is `file:line`.** A claim with no location cannot be checked.
- **Separate a DEFECT from a PREFERENCE.** A defect blocks the route or
  misleads a reader. A preference is how you would have written it. Report
  defects. Put preferences in one short list at the end.
- **A stop is a deliverable.** If you find the switch is already sufficient,
  say so with the evidence and stop.
- **Rank what you find.** A finding that blocks `LJ-1.1` outranks a stale
  sentence. Say which is which.
- Write ASD-STE100 Simplified Technical English: active voice, one instruction
  per sentence, 20 words or fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-0.2-sufficiency.md` INCREMENTALLY. Create it in your first
minutes and fill it as answers land, so a budget exhaustion does not lose the
work. Structure:

1. **VERDICT.** Is the route switch sufficient to start phase 1? One
   paragraph.
2. **BLOCKING GAPS.** What must change before `LJ-1.1` is dispatched. Each
   with: the file and section, what is missing, why it blocks, and the
   smallest fix.
3. **NON-BLOCKING GAPS.** Same shape, ranked.
4. **WHAT I CHECKED AND FOUND SUFFICIENT.** Name each document and section, so
   the coverage is auditable. A short list of what you did NOT reach.
5. **ARCHIVE USED.**
6. **PREFERENCES**, if any.
