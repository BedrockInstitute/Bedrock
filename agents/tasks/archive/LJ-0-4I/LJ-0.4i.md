# LJ-0.4i: the measured dedup sweep, within-file first

tier: codex (default)

## GOAL

Extract byte-identical repeated blocks into local helpers, file by file. Land
about **80 to 140 net**, or refuse per file with numbers.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS ONE IS DIFFERENT FROM THE FIVE THAT FAILED

**The surface is MEASURED, not surveyed.** `[LJ-0.8]` scanned all 78 masters
for four-line repeated blocks with keep-one-copy accounting. Every site below
came out of that scan with a raw saving attached.

**And it has no kit to pay for**, which is the whole reason it is worth
sending. Five blocks have now been measured against the July survey and four
refused: B measured plus 24, E plus 19, G plus 49, and C netted minus 59 by
gutting two chapters. **Every one failed the same way: a parameterized kit
cost 31, 43 or 111 lines, and the sites it served saved less than the kit
cost.** The survey priced savings at the call sites and never priced the kit.

Block A is the only block that landed, at minus 240, because deletion has no
kit. **This sweep has the same shape:** a local helper inside the file that
already holds the repeats. Nothing new is created that must pay for itself.

The AC side stands at **17,273** against an owner target of about 16,400.
`[LJ-0.8]` puts the honest floor near 17,000 and found the missing mass
absent rather than mispriced. **So do not stretch for the band.** Land what is
really there and report the number.

## THE SITES, with measured raw savings

- `src/L/Coding/Unique.lagda.md`: about **54 raw** in 7 classes. `:299`/`:343`
  6x3, `:500`/`:545` 8x2, `:512`/`:557`, `:601`/`:658`, `:731`/`:798`,
  `:399`/`:641`, plus the `domAt-in` setup family.
- `src/L/Coding/Sound.lagda.md`: about **38 raw** in 5 classes. `:873`/`:912`
  8x2, `:890`/`:929` 8x2, `:346`/`:498` 9x2, `:338`/`:490`, `:358`/`:511`.
- `src/L/Axioms/Separation.lagda.md`: about **30 raw**. `:452`/`:459` 6x3,
  `:303`/`:318` 4x4, `:478`/`:485` 6x2. **No survey ever named this file.**
- `src/L/Coding/Slot.lagda.md` `:177`/`:200` 8x2; `src/L/Coding/Recover.lagda.md`
  `:206`/`:229` 4x3; `src/FOL/Manipulation/Parameters.lagda.md` `:377`/`:382`
  4x3.
- **Cross-file, LAST and only if the within-file net is already banked:**
  `Faithful:112`/`Order:126` 9x2, `Adequate:112`/`Internal:931` 7x2,
  `EnvSet:88`/`Recursion:168` 6x2.

**Re-verify every line number before editing.** The scan ran on 2026-08-10 and
the tree moves. D-10: a recorded residue names a target and the target can be
false.

## THE RULES THAT DECIDE IT

- **Within-file extraction uses a LOCAL helper**, private or `where`. **No new
  module for within-file work.** A cross-file pair may justify at most ONE
  tiny shared module, and only if the pair savings exceed its cost.
- **A chapter must remain a chapter.** Block C took `Sound` from 801 in-fence
  lines to seven and `Unique` from 630 to eleven by moving 1,354 lines into a
  new module, for a net of minus 59. If a file you touch ends up a stub, you
  have failed.
- **THE TWICE-TODAY RULE.** A helper may hold only lines that exist **at least
  twice in today's tree**, verified against the scan. A line occurring once
  stays in its chapter. Moving a once-occurring line is relocation, and
  relocation is failure.
- **PER-FILE STAGING.** Extract, typecheck, measure net and seconds, fill the
  report row, then move to the next file. **Any file whose net is not negative
  reverts ALONE.** Do not let one file sink the sweep.
- **P-q: expect zero seconds saved.** The bar is flat seconds, not faster.

## THE STANDING GATES, from `[LJ-0.8]`, which five blocks paid to learn

- **THE BREAK-EVEN GATE, before any wiring.** If you build any helper, count
  its in-fence lines and compute break-even as kit lines divided by measured
  saving per site. **If break-even exceeds your site count, STOP and report
  the three numbers.** B, E and G each discovered this only after building.
- **THE STAGING GATE.** Convert ONE site first, measure its net, and write the
  projection (one-site net times sites, plus any helper) into your report
  **before converting a second**. If the projection misses the floor, stop
  with the projection as your result.
- **THE LINE-BAND STOP TRIGGER.** A stop is a deliverable in THREE cases:
  seconds rise, a consumer must unfold what it did not before, or **the
  measured net cannot reach the floor**. The third is a refusal with a number,
  and two of five blocks have already returned it with full credit.
- **THE NOISE RULE FOR SECONDS.** A per-file delta under 0.5 s or under 5
  percent, whichever is larger, is NOISE: report it as flat. Above that, run
  the file a third time and report all three numbers. The wall's own three
  measurements spread 0.82 s. **Never report a verdict word where a number
  fits.**
- **KIT PRESERVATION.** If you build a helper and then refuse it, do NOT
  delete it. Move it to `_build/kits/lj-0.4i-<name>.lagda.md` and cite the
  path. E and G deleted theirs; B parked one in volatile `/tmp`.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For this block DD4 applies in the negative, and `[LJ-0.8]` says so
explicitly.** These are local proof-shape helpers. **Their wing value is nil
and that is fine.** Say so in the return and spend no effort forcing
generality. Block A's brief carries the same clause. If you see a
generalization worth building, RECORD it and do not build it.

## LITERATURE (DD18)

`dev/literature/` holds the digested mathematics. This is a mechanical
within-file dedup of proof shapes, so the live question is narrow: does any
repeated block you are about to fold correspond to a distinction the
literature treats as two different objects?

- `dev/literature/digest.md`, the orthodox route.
- `dev/literature/j-hierarchy.md` if a repeat sits in order or well-order
  material.

**If none of it bears on the sweep, say so in one line naming
`dev/literature/`.** That is an honest answer and it satisfies DD18. Silence
is not.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- `_build/lj-0.8-review.md` section 7.5, the scan that produced your sites,
  and 7.1, the six gates above.
- `_build/lj-0.4e-report.md` and `_build/lj-0.4b-report.md`: the model
  returns. Both refused with numbers and both were worth having.
- `dev/memos/simplification-register.md:33-38`: S13 to S18, two SHIPPED, two
  REVERTED at their gates, one probe RED. Do not re-propose their shapes.
- `dev/LESSONS.md` is NOT archived and still binds. **P-q, P-r and P-m decide
  compression questions.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.** Directly on
  point: a local helper belongs where its uses are, not hoisted.
- **P-m. The check-cost rate is a content-class certificate.**
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38**: sealing and opacity.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. Heap
  exhaustion is a wall to report, never a cap to raise.
- **C-22. Write the deliverable incrementally.** Block C ran 38 minutes and
  left an all-TODO skeleton, so nobody could see it going wrong until the tree
  was measured. Fill each file's row as its numbers land.
- **D-10. Price the truth of a recorded residue before pricing its proof.**

## SCOPE (read)

`_build/lj-0.8-review.md` 7.1 and 7.5 first. Then each target file at the
named lines. Then the two model returns.

## SCOPE (write)

`src/L/Coding/Unique.lagda.md`, `src/L/Coding/Sound.lagda.md`,
`src/L/Axioms/Separation.lagda.md`, `src/L/Coding/Slot.lagda.md`,
`src/L/Coding/Recover.lagda.md`, `src/FOL/Manipulation/Parameters.lagda.md`,
and only if the within-file net is banked, `src/L/Choice/Faithful.lagda.md`,
`src/L/Choice/Order.lagda.md`, `src/L/Choice/Adequate.lagda.md`,
`src/L/Choice/Internal.lagda.md`, `src/L/Coding/EnvSet.lagda.md`,
`src/L/Recursion.lagda.md`. Your report is `_build/lj-0.4i-report.md`. Never
`src/Everything.lagda.md`.

## CONSTRAINTS

- **Never commit and never push.**
- **Do not change any theorem STATEMENT** and do not weaken a proof.
- **Typecheck every file you edit**, one process at a time. Do NOT run
  `make check` or a whole-tree check.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py`** on your files.
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS**, per file or for the sweep.
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-0.4i-report.md` INCREMENTALLY. One row per file, filled as
its numbers land.

1. **THE VERDICT**, first line: the net landed, or refused with the net.
2. **PER FILE**: in-fence before, after, net, seconds before, seconds after,
   exit code, landed or reverted.
3. **THE ONE-SITE PROJECTION** you wrote before converting the second site,
   and how it compared to the outturn.
4. **WHAT I LEFT**, and why: once-occurring lines, or a fold that would make a
   consumer unfold.
5. **LITERATURE USED.**
6. **ARCHIVE USED.**
7. **WHAT I AM NOT SURE OF.**
