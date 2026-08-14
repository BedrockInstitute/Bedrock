# LJ-1.232: A1 and A3, the two cheap probes of the gate list, in ONE dispatch

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.227]` produced the gate list DD8 demands: five blocks, five named
widest terms, five probes.** **`[LJ-1.229]` ran the first and A2 landed at 186
against a standing 170.**

**Two of the four remaining probes are INFERRED at under 2 Agda minutes each.
Run BOTH. One dispatch, two separate answers.**

**One dispatch because `[LJ-1.221]` measured that walking one item per dispatch
cost this project three dispatches for two links.** **Two separate answers
because A1 and A3 are different objects and a merged verdict would hide which
one moved.**

## PROBE ONE: A1, the per-site `⟨ isL α ⟩`, standing 40 lines

**What A1 is.** The per-site hypothesis `⟨ isL α ⟩` on each ordinal the chain
touches, in place of one global「assume V = L」. **Route A-prime exists to avoid
that global assumption.**

**The widest unmeasured term, in `[LJ-1.227]`'s words:** whether `⟨ isL α ⟩`
ALONE supplies every ordinal fact the restated chain needs at each site, or a
site silently needs more. **The candidates it names are `⟨ isL (sucV α) ⟩`,
`isL-trans` and `Lset-cumul`.**

**Why nobody knows.** The chain masters open `hPropStructure 𝒮ᵥ`, the AMBIENT
carrier (`src/L/BoundedSubset.lagda.md:56`), and carry no `⟨ isL α ⟩`. **The
three delivered sites that take the shape are `src/L/Choice/Order.lagda.md:679`,
`src/L/Choice/Table.lagda.md:795` and
`src/L/Choice/Transversal.lagda.md:77`, and all three consume the ORDER stack
rather than the square-law chain.** **Nobody has restated one chain theorem
with `⟨ isL α ⟩` per site.**

**The probe.** Restate ONE theorem of the ambient chain, `Chain.theorem` or
`LeastCardInj`, with `⟨ isL α ⟩` per site and no global assumption. `--safe`,
exit 0. **RECORD WHICH EXTRA L-LEMMAS THE SITE DEMANDS.** That list is the
deliverable, not the line count.

**Comparable, and P-l says it is not a price:** the ambient chain is 393 lines
at 133 s cold (`agents/tasks/LJ-1-156/lj-1.156-report.md:189`, `:252`).

## PROBE TWO: A3, the `<_L`-least injection, standing 45 lines

**What A3 is.** The canonical selection `leastOf (orderAt β)` over A2's
predicate. **Canonicity is what makes the truncation discharge**, and
`[LJ-1.227]` measured that the selection is the ONLY term that discharges the
chain's `inj` parameter.

**The widest unmeasured term:** obtaining `β` from the delivered `stageBound`,
and the master-level crossing. **`[LJ-1.134]`'s Part B fixed `β` as a
PARAMETER** (`lj-1.134-report.md:238`). **A master must produce `β` from
`stageBound`, delivered at `src/L/Choice/Stage.lagda.md:328`.** **The unmeasured
piece is whether `stageBound` supplies `β` for free at every site, or each site
owes its own bound proof.**

**The probe.** Instantiate `stageBound` at one real ordinal, feed the result to
`leastOf (orderAt β)` over A2's predicate, and check the canonical selection
elaborates with NO `β` hypothesis.

**The selection itself is already measured GO at 22 lines and 1.27 s**
(`agents/tasks/LJ-1-136/lj-1.136-report.md:897-913`, `:12`). **P-l: that is the
selection, not the `β` production.**

## START FROM GREEN, and one file is fresh

**`agents/tasks/LJ-1-229/ProbeLJ1229A.agda` is green as of today**: A2's
predicate `injAt` with both adequacy directions at its S1, plus the range set
and `ranAt`. **A3 needs A2's predicate. Import or copy S1; do not rewrite it.**

**`agents/tasks/LJ-1-134/ProbeLJ1134A.agda` holds the readback device**,
`Extract` and `Small`. **I moved it out of `src/` today, so a report that says
it is gone is reading a stale tree.** **A3 does NOT need the readback.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1), and it is PER PROBE

**A1:**

- **`⟨ isL α ⟩` ALONE SUFFICES.** Report it, and report the restated theorem's
  written lines against the standing 40. **Then A1 is measured and the global
  assumption is provably avoidable.** STOP.
- **THE SITE DEMANDS MORE.** **NAME every extra lemma** (C-36). **That list is
  worth more than the line count**, because each extra lemma is a term nobody
  has priced.
- **A SITE CANNOT BE RESTATED.** If a chain theorem cannot take `⟨ isL α ⟩` per
  site at all, **say why.** **That would refute Route A-prime's premise and it
  is the most valuable outcome available in this task.**

**A3:**

- **`stageBound` SUPPLIES `β` FOR FREE.** Report the written lines against the
  standing 45. **Then A3 is measured.** STOP.
- **EACH SITE OWES A BOUND PROOF.** **Price one such proof** and say how many
  sites need one. That re-prices A3.
- **THE CROSSING IS REAL.** If the master-level crossing needs machinery the
  tree lacks, **name it and stop.**

**BOTH:**

- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME bound
  as its green control, and the control's elapsed time is reported BEFORE any
  cut is interpreted** (`[LJ-1.215]`'s law).
- **BOTH ARE INFERRED AT UNDER 2 AGDA MINUTES.** **If either runs materially
  longer, that is itself a finding and you report it before you interpret
  anything else.**

## WHAT YOU MUST NOT DO

- **Do not merge the two answers.** Two probes, two verdicts, two line counts.
- **Do not price A4 or A7.** `[LJ-1.227]` named their terms and they are the
  next two dispatches, not yours.
- **Do not re-derive A2.** `[LJ-1.229]` measured it at 186, with the
  description plus adequacy at 27 and the readback at 51.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.** I moved three strays out of `src/`
  today; **do not put one back.**
- **Do not touch `agents/tasks/LJ-1-230/` or `LJ-1-231/`.** Two siblings are
  live there.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-232/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **A sibling
  holds the other Agda slot.** **Report the load beside every absolute figure**,
  discard a warm-up, and take at least three kept runs for any figure a decision
  rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` MEASURED that A1 and A3 are both PER-TOWER**, and it mapped them
onto Devlin's two objects: **A1 is the level-hood certificate, A3 is the
definable well-order** (`dev/literature/devlin-II5.md:387-389`).

**So neither can be shared, and that is the point.** **Write both with a
STRUCTURE PARAMETER rather than fixed to `isL`**, so the J tower
re-instantiates rather than re-derives. **`[LJ-1.210]` measured that
retrofitting a structure parameter costs 42 lines on a 1,288-line module, and
writing one at the start costs nothing.** **Say for each probe whether the
parameter form cost anything.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-227/lj-1.227-report.md`** sections 1, 3 and 8, read
  WHOLE. **Your two probes are specified there.**
- **`agents/tasks/LJ-1-229/lj-1.229-report.md` and `ProbeLJ1229A.agda`, read
  WHOLE**: A2 green, and its S1 is A3's input.
- `agents/tasks/LJ-1-134/lj-1.134-report.md:238` and `ProbeLJ1134A.agda`: Part
  B's fixed `β`, which is exactly what A3 must remove.
- `agents/tasks/LJ-1-136/lj-1.136-report.md:897-913`, `:12`: the selection GO at
  22 lines and 1.27 s.
- `agents/tasks/LJ-1-156/lj-1.156-report.md:189`, `:252`: the ambient chain at
  393 lines and 133 s.
- **`src/L/Choice/Stage.lagda.md:328` (`stageBound`),
  `src/L/BoundedSubset.lagda.md:56`, and the three `⟨ isL α ⟩` sites at
  `src/L/Choice/Order.lagda.md:679`, `src/L/Choice/Table.lagda.md:795`,
  `src/L/Choice/Transversal.lagda.md:77`. Read the source, never a report about
  it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route carried a global assumption and this block exists to avoid
  one. Take SHAPE from the archive, never a claim**, and say what would NOT
  transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:387-389` names the two per-tower objects and
`[LJ-1.227]` mapped A1 and A3 onto them.** **Say whether Devlin's proof needs a
per-site relativization or a global one**, and whether he prices the
well-order's selection. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-227/lj-1.227-report.md` FIRST, sections 1 and 3.

## SCOPE (write)

`agents/tasks/LJ-1-232/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above, per probe.
- **DD8.** One estimate each, and each names its basis.
- **P-l.** 393 lines, 133 s, 22 lines and 1.27 s are comparables and NOT your
  prices.
- **C-36.** Write the term you could not write. **For A1 that is the extra
  lemma list, and it is the deliverable.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **A3's whole question is whether `stageBound` SUPPLIES `β`.**
- **C-42.** A refutation measures the site it names, never its extent.
- **I-5.** No probe under `src/`.
- **P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22, C-39, C-40. DD0, DD24, D-10,
  D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with TWO verdicts and TWO numbers, A1 then A3, each against its standing
40 and 45.** Then A1's extra-lemma list, named. Then whether `stageBound`
supplies `β` for free. Then the seconds with load and run count, per probe.
Then whether the structure-parameter form cost anything. **Mark every negative
MEASURED or INFERRED.**
