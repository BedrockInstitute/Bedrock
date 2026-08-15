# LJ-1.307: are the thirty `Agree` modules thirty things, or one thing thirty times?

tier: pi (pi-subagent-mode), **model `glm-5.3`**. I ran
`scripts/dispatch/dispatch_policy.py` and took the head it gave. **NO AGDA**:
both Agda slots are held by siblings on the phase terminus, and this task reads.
**`scripts/` moved today**: `rules.py` is `scripts/dispatch/rules.py`, the
linters are `scripts/gate/`, `ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**DD13 asks the question nobody has asked about this family: not「how do we
move these lines」but「what would this look like written fresh today」.**

The `Agree` family is 30 modules, 4,208 lines, at
`src/L/Condensation.lagda.md:2774-7319`. **Three tasks have priced MOVING it.
None has asked whether it should exist at its current size.**

**THE HINT THAT MAKES THIS WORTH ASKING.** `[LJ-1.302]` read the seven dirty
modules and found: **「The ties are ONE debt, not sixteen. Read together, every
tie says the same thing」**, and the shared block that proves them is about 20
lines written ONCE.

**If the TIES are one thing sixteen times, are the MODULES one thing thirty
times?** Nobody has looked.

## WHY IT MATTERS MORE THAN THE ANSWER'S SIZE

`src/L/Condensation.lagda.md` is **6,718 lines and 132.28 s**, and I measured
today that it is **62 percent of the GCH wing's whole seconds** and that its
overage is 61.7 s against a wing gap of 63.1 s. **Removing it from the wing's
excess would close the DD24 gap by itself.**

And the owner ruled REPLACE: the generic port archives the original. **So the
question「port it or rewrite it」is live RIGHT NOW, and a port is already being
built by `[LJ-1.306]` in the next pane.**

**This is the only action measured today that could improve the line count AND
the seconds at once.** Every other lever trades one for the other (P-q).

## WHAT TO BRING BACK

**1. THE ANSWER, in one word: THIRTY or ONE.** Read the 30 modules. **Do they
differ in MATHEMATICS, or only in which object they are instantiated at?**

**2. THE EVIDENCE, structural and countable.** For each module: its statement's
SHAPE, and what varies between it and its neighbours. **A table of 30 rows.**
**If they share a shape, say what the shape is and how many instantiate it.**

**3. THE DD13 COMPARISON.** **What would the family be, written fresh today?**
One generic module plus 30 instantiations? Five shapes plus 30? Thirty, because
they really are thirty? **Give a LINE ESTIMATE with its basis named** (DD8), and
compare it to today's 4,208.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THEY COLLAPSE.** Report the shape, the count, and the estimate. **Then the
  port `[LJ-1.306]` is building may be the wrong move and I stop it.** STOP.
- **THEY DO NOT COLLAPSE.** **Say so plainly with the evidence.** **That is a
  real answer and it settles the question for good**, and it means the port is
  right. **Do not manufacture a collapse to be interesting.**
- **THEY PARTLY COLLAPSE.** **Give the partition**: how many share a shape, how
  many are genuinely their own. **That is the likeliest answer and the most
  useful one.**
- **THE FAMILY IS NOT 30 MODULES.** `[LJ-1.298]` and `[LJ-1.302]` both counted
  it; `[LJ-1.302]` also corrected `[LJ-1.298]` on where the chapter ends.
  **Count it yourself** (C-44).

## CONSTRAINTS

- **DO NOT RUN AGDA.** Both slots are held by the phase terminus. **This task
  reads.** If you believe a typecheck is needed to answer, say so and stop.
- **LAND NOTHING. Do not edit `src/L/Condensation.lagda.md`** or any master.
- **A SIBLING IS BUILDING THE PORT** in `agents/tasks/LJ-1-306/`, and another
  is in `agents/tasks/LJ-1-305/`. **Touch neither.** **You may READ
  `[LJ-1.306]`'s report if it exists, but it is mid-run and its file may be
  half-written.**
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-307/lj-1.307-report.md` in your FIRST five
  minutes** (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on your report.
  **No em dash in any language.**
- Count with `.venv/bin/python scripts/measure/ledger.py`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**DD13. Price a retirement from the REWRITE side.** **「We already paid for it」
decides nothing, in either direction.** This task IS that law, applied to the
largest file in the tree.

**C-42. A refutation measures the site it names and never how far it extends.**
**`[LJ-1.302]` measured collapse at the TIES. Whether it extends to the modules
is exactly this sweep.**

**D-10. Price the truth of a recorded residue before pricing its proof.** **The
record says「4,208 lines of family」. Whether it NEEDS to be 4,208 is a
different question and nobody has asked it.**

**P-l. A judgement at one site is a hypothesis at another.**

**D-26.** A well-founded key on a tower needs generation data, or syntax. **It
bears only if the modules differ by what their carrier CARRIES; say so if they
do and say it does not bear if they do not.**

**C-22.** Write your deliverable incrementally.

**C-44.** Every count in this brief is another report's.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**THIS TASK IS DD4'S OWN QUESTION at the largest site in the tree.** Thirty
modules that differ only by instantiation are thirty copies of one shared thing
that was never shared. **Say whether the collapse, if it exists, would serve
BOTH towers or only the Def side**, and **NAME YOUR AXIS** (C-46): DD4's own
axis is AC-against-GCH, and `src/L/Condensation.lagda.md` sits in NEITHER trophy
closure today, which I measured an hour ago.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-302/lj-1.302-report.md`, section 4 especially, for the
「ties are ONE debt」finding that motivates this. `agents/tasks/LJ-1-298/lj-1.298-report.md`
for the clean-versus-dirty partition and the 23/7 split.
`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`: **the
retired route also had agreement machinery, and what it cost is on the record.
Take SHAPE from the archive, never a claim**, and say what would NOT transfer.
Return an **ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Devlin proves
condensation once. Say how many agreement lemmas he states**, and whether thirty
is the mathematics or the port. Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Condensation.lagda.md:2774-7319` FIRST, the family itself.

## SCOPE (write)

`agents/tasks/LJ-1-307/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement. **OPEN the full entry for any law you act on.**

- **D-10, C-22, P-l, D-26, C-42.**
- **DD13, DD4, DD8, DD18, DD24. C-32, C-36, C-38, C-39, C-40, C-43, C-44,
  C-45, C-46, C-49, C-50. P-h, P-k, P-m, P-q, P-t, P-y. I-5.**

## RETURN

**Lead with ONE word: THIRTY, ONE, or PARTLY.** Then the table of 30 rows with
each module's shape. Then the DD13 estimate with its basis. Then whether
`[LJ-1.306]`'s port is the right move or the wrong one. Then the DD4 answer with
its axis. **Mark every negative MEASURED or INFERRED.**
