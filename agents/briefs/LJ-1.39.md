# LJ-1.39: compress the de Bruijn index padding, and MEASURE it before it lands

tier: codex (default)

## GOAL

The owner ruled that compressible padding is compressed, not kept. **Measure
the compression of `src/L/Condensation.lagda.md`'s index literals: what it
saves in LINES and what it costs in SECONDS.** **This is a PROBE. You may NOT
edit the master.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY YOU MAY NOT TOUCH THE MASTER

**`[LJ-1.38]` is editing `src/L/Condensation.lagda.md` RIGHT NOW** (C-25). Work
on a COPY under `src/ProbeLJ139*.agda` or a copied `.lagda.md` you never commit.
**The orchestrator lands the compression after `[LJ-1.38]` returns**, using your
measurement. **If you edit the master you destroy a sibling's work.**

## THE TARGET, measured by the orchestrator on the committed file

`src/L/Condensation.lagda.md` is 2,031 in-fence lines.

| shape | lines | share |
|---|---:|---:|
| lines carrying ONLY a de Bruijn index argument | **218** | 10.7% |
| lines containing 4 or more nested `suc` | 343 | 16.9% |
| lines that are only closing parens | 0 | 0% |
| DISTINCT index literals in the file | 272 | |

The most repeated literals: `(suc (suc (suc zero)))` 23 times,
`(suc (suc (suc (suc (suc (suc (suc K)))))))` 16 times,
`(suc (suc (suc (suc (suc (suc (suc (suc (suc (suc t0))))))))))` 12 times,
`(suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))` 12 times.

## TWO DELIVERED PRECEDENTS IN THIS TREE, so this is not a survey

1. **`src/L/Choice/Before.lagda.md:248-256`** already does exactly this: a
   `private` block naming `s1 : Fin 5` through `s4 : Fin 5`, built from a `sh2`
   shift helper.
2. **`src/L/Coding/Shape.lagda.md:68,428`** uses `fromℕ'` from
   `Cubical.Data.FinData.Properties` to build an index numerically.
   `src/FOL/Count.lagda.md`, `src/L/Choice/Internal.lagda.md` and
   `src/L/Coding/EnvSet.lagda.md` also use the numeric idiom.

**A delivered comparable beats a survey, but P-l still forbids transferring a
measured cure by analogy. Re-measure at this site.**

## THE HISTORY THAT SAYS THIS CAN FAIL, and it is this project's own

`[LJ-0.4]`'s compression campaign ran nine blocks and **FOUR REFUSED**. The one
systematic reason is `dev/LESSONS.md` **D-28**: **a kit costs 31 to 111 lines
and its sites save less**, because every survey priced the savings and never
the kit. `dev/LESSONS.md` **C-30** holds the nine compression gates.

**The ONE compression that both landed and improved the ratio was `[LJ-0.4n]`:
it took ONE parameter, saved 104 lines, and the tree got 0.53 s FASTER.** Every
other kit that took many parameters lost.

**So the shape that wins here is the smallest possible abbreviation set, not the
most general one.**

## THE TWO STOP-LINES, and they cut in opposite directions

**STOP-LINE 1: if the compression makes the file SLOWER, refuse it.** The
committed master checks at **9.00 s cold over 2,031 lines, 0.0046 s per line**
(orchestrator's own re-run). **Improving a ratio by making the build slower is
as dishonest as improving it by padding**, and the owner asked for neither.

**STOP-LINE 2: report the saving even if it is small.** If naming the literals
saves 40 lines rather than 218, that is the answer and it is worth having.

**Report BOTH numbers for every variant you try: lines saved AND seconds
delta.** A variant that saves lines and costs seconds is a REFUSAL with a
measurement, which is a full deliverable.

## WHAT TO TRY, cheapest first

1. **A private abbreviation block**, the `Before.lagda.md` shape. Name the most
   repeated literals only. **Start with the top 10 by frequency and stop when
   the marginal saving falls below the cost of the name.**
2. **A shift helper**, the `sh2` shape, if a family of literals is one helper
   applied repeatedly.
3. **Numeric literals** via `fromℕ'`, the `Shape.lagda.md` idiom, **only if it
   typechecks without a coercion at every use site.** Say plainly if it does
   not.

**Do not build all three. Measure the first, and go on only if it disappoints.**

## WHAT YOU MUST NOT CHANGE

- **No theorem's statement or type may change.** The compression is
  presentational. **Prove that by diffing the exported signatures**, and say in
  the report that you did.
- **No `postulate`, no `TERMINATING`, no hole.** The file is `--safe`.
- **No placement.** The master has zero `absFo`, `placeFo`, `mapΔ₀` and
  `mapΣ`, and that is load-bearing (P-u).
- **DD23 freezes mathematical prose.** Code and its own comments only.

## THE TREE-WIDE QUESTION, cheap and worth asking

**Does the same padding exist in other masters?** A grep and a count, not a
survey. Report the top five masters by index-only line count. **Do not compress
them; just say where the mass is.** That turns a one-file fix into a tree-wide
finding for `[LJ-1.9]` at almost no cost.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**An abbreviation block is template content if it is generic in the arity.**
`Before.lagda.md`'s `s1 : Fin 5` is fixed at 5 and therefore not reusable.
**Say whether an arity-generic version costs more than the fixed one**, and by
how much. If the generic version is free, both towers get it.

## LITERATURE (DD18)

**None bears.** This is a presentational compression inside this tree's own
code. **Say so in one line naming `dev/literature/` and spend nothing.**

## ARCHIVE (DD18)

**Read these WHOLE. C-32 exists because a brief of mine named a SECTION and hid
the decisive probe.**

- **`src/L/Choice/Before.lagda.md`** and **`src/L/Coding/Shape.lagda.md`**, the
  two delivered precedents.
- **`_build/lj-1.37-report.md`**, which built the content you are compressing.
- `src/L/Condensation.lagda.md` as committed at `92e8b8b`.
- `dev/LESSONS.md` is NOT archived and still binds. **D-28 and C-30 are the
  compression laws and they decide this block. Also P-l, P-m, P-q, D-1, D-10.**
- **P-q** measured 315 lines removed buying 11.8 s: **a line lever is not a
  seconds lever.** Expect the two to move independently.

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES

**Run BOTH `python3 scripts/rules.py --for probe` and
`python3 scripts/rules.py --for recon`, and read each statement.**

- **D-1.** The smallest decisive miniature, GO or NO-GO with a price.
- **D-10.** Every figure in this brief is the orchestrator's own measurement
  from today. **Re-verify the 218 and the 2,031 before you build on them.**
- **D-28.** A kit costs 31 to 111 lines and its sites save less.
- **C-30.** The nine compression gates.
- **P-q.** A line lever is not a seconds lever.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. **A sibling
  holds the other slot.**
- **C-22.** Write the deliverable incrementally.
- **C-32.** **Interfaces live in `_build/2.8.0/agda/src/`, NOT beside the
  source.** Deleting a `.agdai` beside a `.agda` removes nothing and silently
  turns a cold measurement into a warm read. I made that mistake this week.
- **C-33.** I have tried to name the OBLIGATION and not an entry point. **If I
  named an idiom where I should have named a job, say so and use the better
  one.**
- **C-34.** Build the cure or report the wall. **A named unpriced cure is not a
  caveat.**
- **D-26. It does NOT bear, and say so in one line.** A well-founded key on a
  tower needs generation data or syntax. This block changes how an index is
  SPELLED and touches no key, no tower and no statement. **If you find that it
  does bear, that means the compression changed a type, and STOP: that is
  forbidden here.** So D-26 is your canary rather than your guide.

## SCOPE (read)

`src/L/Condensation.lagda.md` FIRST, then `src/L/Choice/Before.lagda.md:248-256`
and `src/L/Coding/Shape.lagda.md`, then `dev/LESSONS.md` D-28 and C-30.

## SCOPE (write)

`src/ProbeLJ139*.agda` and any copied working file you never commit, plus
`_build/lj-1.39-report.md`. **NEVER `src/L/Condensation.lagda.md`. NEVER any
master. NEVER `src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.** `scripts/check-probes.py` refuses a
  committed probe.
- **Never `git checkout .`, `git stash`, `git reset --hard` or `git clean`.** A
  sibling has uncommitted work in the file you are copying.
- **Do NOT run `make check`.**
- **Report cold seconds and in-fence lines for the control and every variant.**
  Noise rule: under 0.5 s or 5 percent, whichever is larger, is flat.
- **Evidence is `file:line`.**
- **A measured refusal is a SUCCESS**, and D-28 says it is the likelier
  outcome.
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.39-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: lines saved and the seconds delta, or a
   measured refusal.
2. **THE VARIANT THAT WON**, and why you stopped there.
3. **LINES AND SECONDS**, control and every variant, as one table.
4. **DID ANY EXPORTED SIGNATURE CHANGE?** You diffed them; say so.
5. **THE EXACT PATCH**, as a list of edits the orchestrator can apply to the
   master after `[LJ-1.38]` lands. **This is the deliverable I will act on.**
6. **THE TREE-WIDE COUNT**: top five masters by index-only lines.
7. **DD4**: is an arity-generic abbreviation block free?
8. **ARCHIVE USED.** 9. **WHAT I AM NOT SURE OF.**
