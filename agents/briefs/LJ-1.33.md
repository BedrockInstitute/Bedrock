# LJ-1.33: gate the next condensation block by measuring leg D

tier: codex (default)

## GOAL

`[LJ-1.5]` landed block 1 and named the widest unmeasured term for the rest.
**Measure leg D's rate.** It carries a 13x spread on its own, and DD8 forbids
funding the next block until it is measured. **This is a PROBE. Throw the code
away.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS ONE TERM DECIDES THE BLOCK

`[LJ-1.5]` delivered `src/L/Condensation.lagda.md` at 308 lines and **0.0079 s
per line, 0.60 of DD24's bar.** I re-measured it cold myself at 2.43 s. Block 1
is done and it is cheap.

Its own pricing of what remains (`_build/lj-1.5-report.md` section 6):

| piece | lines | rate | seconds |
|---|---|---|---:|
| the clause-shaped residue, eleven more clauses | 2.7 to 3.0k | 0.008 to 0.010, MEASURED at block 1 | **22 to 30** |
| **leg D, the story-to-machine agreement at `L`** | **0.3 to 0.8k** | **0.0052 to 0.085, UNMEASURED** | **5 to 68** |

The GCH side's whole seconds budget is **99.6 to 147.7 s** over a PROJECTED
7,553 to 11,197 lines (`dev/ledger.toml`). Today the side measures about 2,200
lines at about 18 s.

**At leg D's low end the block is comfortable. At its high end the side busts
the low projection.** No other remaining term carries that spread.

## WHAT LEG D IS

`[LJ-1.28]` named it (`_build/lj-1.28-report.md`, read the WHOLE document, and
see section 3's Leg D and section 4). It is the **two-way decode between the
bounded table's clause and the DELIVERED machine's clause, at variable slots.**

The machine side is delivered: `src/L/Coding/Sequence.lagda.md:217-229` and
`:295-312`. `[LJ-1.28]` found the clause-to-content half was proved at variable
slots with no carrier fact, measured at **0.0052** by `[LJ-1.15]`
(`_build/lj-1.15-report.md:82-91`).

**The clause-to-MACHINE half is the unmeasured one.** Its nearest measured
cousin is the 0.085 neutral-carrier decode class (`dev/ledger.toml:643`).
**That gap, 0.0052 against 0.085, IS the spread.** Measure the real half at
its own site (P-l).

## THE MEASUREMENT

Build the smallest decisive miniature: **one clause's decode against the
delivered machine's projections**, at variable slots, and report its rate.

- **Use a DELIVERED machine projection**, not a synthetic stand-in, so the
  answer is about the real site.
- **`src/L/Condensation.lagda.md` is committed and green.** Build against it,
  and take its `Clause` shapes as the source rather than re-inventing them.
- **Report the rate against 0.013193**, DD24's bar, and say which of the two
  cousin classes it lands in.

**GO: at or below 0.013.** Leg D costs 5 to 10 s and the next block funds.
**NO-GO: at or above 0.05.** Leg D costs 15 to 68 s and the block needs a
re-shape before funding. **A number between is a real outcome; report it and
say which end it leans to. Do not round toward either.**

## THE LAW THAT DECIDES THE SHAPE

**P-u, admitted 2026-08-10: a Levy witness travels along a relabelling for free
and does not travel along a placement at all. Certify BEFORE you place.**

`[LJ-1.5]` landed block 1 with **NO placement anywhere** and that is why it
costs 0.0079. **If leg D's decode needs a placement, say so immediately and
report the wall rather than fighting it**: `[LJ-1.32]` measured that wall flat
at 8 GB across constant counts 0, 1, 2 and 5, so no constant-count trick
escapes it.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

`[LJ-1.5]` split block 1 cleanly: `EraseTransfer` is TEMPLATE, the `Clause` and
`ClauseDecode` halves are per-tower Def content, and two rides are delivered and
neither side.

**Say which side leg D falls on.** `[LJ-1.28]` called the equivalence row
per-tower, because each tower's story differs and each proves its own agreement
with its own machine. **If your measurement shows a template half hiding inside
it, that is a DD4 finding worth having**, because the J tower would then pay
less than `[LJ-1.26]`'s split assumes.

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md`, sections 2.1 to 2.8, Step C. **Devlin has NO
  story-to-machine agreement row at all**, because his machine IS the level
  formula (`[LJ-1.28]` found this). **So the literature cannot price this row;
  say so in one line and spend nothing more.**
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

**Read these documents WHOLE. C-32 was admitted because a brief of mine named a
SECTION and the decisive probe sat in another one.**

- **`_build/lj-1.28-report.md`**, which named leg D and gave the spread.
- **`_build/lj-1.5-report.md`**, block 1 and its pricing of the rest.
- `_build/lj-1.15-report.md`, the 0.0052 at variable slots.
- `_build/lj-1.32-review.md` and `_build/lj-1.27-review.md`, why placement is
  banned and what the erase route buys.
- `archive/rud-route/src/L/Condensation.lagda.md`. **Its target is classically
  FALSE (`[LJ-1.11]`), so read it for SHAPE and never for a price.**
- `dev/LESSONS.md` is NOT archived and still binds. **P-l, P-m, P-n, P-t, P-u,
  D-1, D-10 and C-32 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES

**Run BOTH `python3 scripts/rules.py --for probe` and
`python3 scripts/rules.py --for recon`, and read each statement.**

- **D-1.** The smallest decisive miniature, GO or NO-GO with a price, thrown
  away.
- **D-10.** Every figure here is a residue. Re-verify the delivered machine
  projections' signatures before you build on them; a NAME is not a signature,
  and `[LJ-1.18]` found `FOL.Count.encode` off by one after a review claimed a
  match.
- **P-l.** A measured cure does not transfer by analogy. **Neither does a
  measured RATE**: 0.0052 was measured on the other half.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-u.** Certify BEFORE you place.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. Report a heap
  exhaustion as a wall and never raise the cap.
- **C-22.** Write the deliverable incrementally.
- **C-32.** A cure invalidates downstream measurements. `[LJ-1.31]`'s cure
  landed today, so **re-verify any figure taken from a report written before
  it**, including the 0.0052.
- **D-26, AND IT BEARS DIRECTLY. Say how.** A well-founded key on a tower needs
  generation data, or it needs syntax. **`Lset` is a definable power, so its
  members carry nothing and the Def side's only key IS the defining syntax.**
  That is why the Def tower has a story-to-machine agreement row at all, and
  why `[LJ-1.28]` called the row per-tower. **If your measurement shows the
  agreement is really about the MACHINE rather than the syntax, D-26 predicts
  the J tower's row is much smaller, and that is a finding worth reporting.**

## SCOPE (read)

`_build/lj-1.28-report.md` FIRST, then `src/L/Condensation.lagda.md`, then
`src/L/Coding/Sequence.lagda.md` at the named lines.

## SCOPE (write)

`src/ProbeLJ133*.agda` only, and your report `_build/lj-1.33-report.md`. **No
master. No file under `dev/`. Never `src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.** `scripts/check-probes.py` refuses a
  committed probe.
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.**
- **Do NOT run `make check`.**
- **Interfaces live in `_build/2.8.0/agda/src/`, NOT beside the source.**
  Deleting a `.agdai` next to a `.agda` removes nothing and silently turns a
  cold measurement into a warm read. I made that mistake and C-32 records it.
- **Report cold seconds and the RATE**, noise rule: under 0.5 s or 5 percent,
  whichever is larger, is flat.
- **The machine is quiet and both Agda slots are yours.**
- **Evidence is `file:line`.**
- **Either answer is a full success.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.33-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: leg D's measured rate, and GO, NO-GO, or the
   in-between with which end it leans to.
2. **WHAT YOU BUILT**, and why it is the decisive miniature.
3. **COLD SECONDS AND LINES.**
4. **WHICH COUSIN CLASS** it lands in, 0.0052 or 0.085, and why.
5. **DID IT NEED A PLACEMENT?**
6. **THE PRICE OF THE NEXT BLOCK** with leg D now measured.
7. **DD4**: which side leg D falls on.
8. **LITERATURE USED.** 9. **ARCHIVE USED.** 10. **WHAT I AM NOT SURE OF.**
