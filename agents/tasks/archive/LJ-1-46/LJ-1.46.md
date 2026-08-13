# LJ-1.46: gate LJ-1.7, the bounded-subset lemma (Devlin 5.5)

tier: codex (default)

## GOAL

`[LJ-1.7]` is the last mathematical block before the trophy, and it is
`planned` with no price. **Price it, and name the ONE widest unmeasured term
with the probe that would measure it.** DD8 forbids funding a block whose brief
cannot do that. **Write no Agda and hold no Agda slot.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, HEAD `8019b6a`.

## WHY YOU MAY NOT TOUCH AGDA

`[LJ-1.45]` is measuring timings on this machine and I promised it a quiet
one. **A single `agda` run corrupts its numbers.** Every figure you produce
comes from the record and from reading, and you say so.

## THE TARGET

Devlin 5.5, quoted in `dev/literature/devlin-II5.md:147`:

> **5.5 Lemma.** Assume V = L. Let κ be a cardinal. If x is a bounded subset of
> κ, then x appears early.

5.6 then reads GCH off it (`:159-164`): `𝒫(κ) ⊆ L_{κ⁺}` for every infinite
cardinal κ, then 1.1(vii) counts.

## WHAT IS DELIVERED THAT 5.5 CONSUMES

- **Condensation.** `src/L/Condensation.lagda.md`, 4,512 in-fence lines. The
  twelve-row table and block 1 are CLOSED and machine-checked against the
  delivered machine.
- **The hull**, `src/L/Hull.lagda.md`, on the meta term algebra (DD27), whose
  `hull-closed` gives Tarski-Vaught at HULL parameters.
- **The level size**, `src/L/StageCardinal.lagda.md`, `|Lset α| = |α|`'s upper
  half at every infinite ordinal, owing `fin-inj` at 50 to 100 lines.
- **The counting**, `src/FOL/Count.lagda.md`, 620 lines, zero `L` imports.
- **The collapse**, `src/V/Collapse.lagda.md`.
- **The stage arithmetic**, `src/L/Ordinal/StageArith.lagda.md`.

## THE FOUR QUESTIONS

1. **What does 5.5 need that the tree does not have?** State it as a list of
   obligations, each at `file:line` where the gap is, not as an impression.
2. **Which delivered result discharges each obligation it can?** A NAME IS NOT
   A SIGNATURE. `[LJ-1.18]` found `FOL.Count.encode` off by one after a review
   claimed a match. Check signatures.
3. **The price**, in lines and in SECONDS, with the content class named against
   P-m's bands. **One best-effort number per obligation, naming its basis**
   (DD8): a probe, a delivered comparable, or a survey. Say which.
4. **THE WIDEST UNMEASURED TERM, and the probe that measures it.** Name one.
   Say what the probe would build, what it would cost in minutes, and what GO
   and NO-GO would mean. **A gate that cannot name its probe is not a gate.**

## THE CONSTRAINT THAT DECIDES WHETHER IT FUNDS

DD24's live bar is **0.0127** seconds per line, computed from the AC baseline
0.011057 times the 1.15 tolerance. **Do not use 0.013193; that figure is stale
and several of my earlier briefs quote it.** Re-derive from `dev/ledger.toml`.

The GCH side today measures **0.0131 over 6,407 lines and 84.13 s, OVER the
bar**, and `[LJ-1.45]` is working that down. **So 5.5 must not be priced as if
there were room.** Say plainly what its seconds do to the aggregate.

## THE SECOND-ORDER QUESTION, and it may matter more than the price

5.6 derives GCH from 5.5 in three lines of book. **Say whether the formal
distance from 5.5 to `L ⊨ GCH` is comparable, or whether `[LJ-1.8]` hides work
that nobody has priced.** `[LJ-1.8]` is currently one PLAN row with no
estimate at all. **If the trophy assembly is bigger than its row suggests, that
is the most valuable thing you can report.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

`[LJ-0.7]` found exactly TWO per-tower objects on the whole GCH chain: the
level-hood certificate and the definable well-order, and DD27 removed the
second. **Say which parts of 5.5 are template and which are per-tower**, and
price them separately. A price that does not split them tells the owner nothing
about whether the J tower pays twice.

## ARCHIVE (DD18)

- **`archive/rud-route/`** holds the retired route's code. Its `Condensation`
  target is classically FALSE (`[LJ-1.11]`), **so read it for SHAPE and never
  for a price.** Look for whatever it had at 5.5 and say what survives.
- `archive/dev/TASKS-archived.md` and `JOURNAL-archived.md` for what the
  retired dispatches found at this step.
- **What bears and is NOT archived:** `dev/LESSONS.md`, and the live reports
  `_build/lj-1.43-report.md`, `_build/lj-1.44-report.md`,
  `_build/lj-1.21-report.md` and `_build/lj-1.12-report.md`. **Read those
  whole**, not by section: C-32 exists because a brief of mine named a section
  and hid the decisive probe.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 1.5 and 2.x**, and
  `_build/literature/dev2.txt:1369-1388` for 5.5 and 5.6 themselves.
- **Devlin assumes the cardinal arithmetic and asserts absoluteness.** Say in
  one line what he assumes that the formal proof must supply, because that gap
  IS the price you are estimating.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`dev/literature/devlin-II5.md` FIRST, then `src/L/Condensation.lagda.md`'s
exports, then `src/L/StageCardinal.lagda.md`, then `_build/lj-1.12-report.md`.

## SCOPE (write)

`_build/lj-1.46-report.md` only. **No file under `src/` and no file under
`dev/`.**

## MANDATORY RULES FOR A RECON

Run `python3 scripts/rules.py --for recon` and read every statement.

- **D-10.** Price the truth of a recorded residue before pricing its proof.
  **Every figure in this brief is a residue, including the bar, which I quoted
  wrongly in three earlier briefs.**
- **C-22.** Write the deliverable incrementally.
- **P-l.** A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.
- **D-26.** A well-founded key on a tower needs generation data, or it needs
  syntax. **Say whether it bears on 5.5.**

## CONSTRAINTS

- **Run NO `agda` and NO `make check`.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- **ONE best-effort number per obligation, naming its basis** (DD8). The
  two-caliber rule is REVOKED.
- **Separate MEASURED from ESTIMATED everywhere.**
- **A finding that a block is bigger than its row says is a SUCCESS.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.46-report.md` incrementally, skeleton first.

Lead with the verdict: 5.5's price in lines and seconds, its basis, and the one
widest unmeasured term with its probe. Then the obligations and what discharges
each. Then what `[LJ-1.8]` hides. Then the DD4 split, the archive and
literature sections, and what you are not sure of.
