# LJ-0.4n: the shape half of the recursion assembly, one parameter

tier: codex (default)

## GOAL

Share the SHAPE half of the recursion assembly across four files, through one
generic module with **one** parameter, hosted in a master that already exists.
Land at or below **minus 60**. Refuse with numbers otherwise.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS ONE, AFTER SEVEN BANDS FAILED

`[LJ-0.4f]` built an eleven-parameter kit of 208 lines for this material and
refused it: one wired site measured minus 96, and the two-site net came out
about **plus 4**. `[LJ-0.4f-R]`, an adversarial review, UPHELD that refusal and
then found the cure the refusal missed.

**The eleven parameters were the defect, not the idea.** The assembly has two
halves. The INDUCTION half needs the whole telescope and has two consumers:
leave it alone, that is what LJ-0.4f measured and the measurement stands. The
SHAPE half is generic in **one** parameter, `Step`, and it has five instances
in four files.

**Your kit takes one parameter. If you find yourself adding a second, stop and
report why.**

## THE SITES, MEASURED by `[LJ-0.4f-R]` at ledger caliber

| File | Block | file:line | in-fence |
|---|---|---|---:|
| `L.Coding.Sequence` | `ApproxAt` and four reads | `:281-307` | 23 |
| `L.Coding.Sequence` | `LsetGraphAt`, `GraphOf`, two reads | `:361-379` | 15 |
| `L.Choice.Table` | shape block | `:406-446` | 31 |
| `L.Choice.Before` | shape block | `:714-746` | 27 |
| `L.Choice.Before` | graph block | `:747-766` | 15 |
| `L.Hierarchy` | pair graph | `:448-476` | 21 |
| `L.Choice.Table` | pair graph | `:601-622` | 17 |
| `L.Choice.Before` | pair graph | `:1213-1241` | 24 |
| **gross deletable** | | | **173** |

**Re-verify every line number before you edit.** These were counted on
2026-08-10 and the tree moves. D-10: a recorded residue names a target and the
target can be false. **On this exact material a residue verdict was already
wrong once today**, and section "THE FALSE FINDING" below says how.

## THE KIT, PRICED BY THE REVIEW

One parameter: `Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n`.

Content and its source in `_build/kits/lj-0.4f-recassembly.lagda.md`:
`Domain₀` at `kit:49-50` (3 lines), `ApproxAt₀` and `GraphAt₀` at `kit:56-64`
(8), the `ApproxAt-*` block at `kit:116-136` (18), `GraphOf` with `Graph-in`
and `Graph-out` at `kit:138-148` (9), the pair graph at `kit:235-254` (17),
plus a module header. **About 56 in-fence lines.**

**HOST IT INSIDE `src/L/Coding/Sequence.lagda.md`. Write NO new master.**
Sequence already holds a copy of this material and already pays the preamble;
a new master adds about 26 lines for nothing. `L.Hierarchy` already imports
from Sequence at `Hierarchy:57-60`, so it holds no copy of the shape half and
is a consumer rather than a site for it.

Everything the kit needs is already exported by `L.Coding.Model`: `domAt-out`,
`domAt-in`, `appAt-adequate`, `prAtL`, `prAtL-adequate`.

## THE ARITHMETIC YOU ARE TESTING

Deletions MEASURED, instantiation ESTIMATED, by `[LJ-0.4f-R]`:

| File | deletes | pays | net |
|---|---:|---:|---:|
| `L.Coding.Sequence` hosts and re-exports | -38 | +60 | **+22** |
| `L.Choice.Table` shape and pair | -48 | +3 | **-45** |
| `L.Choice.Before` shape and pair | -66 | +3 | **-63** |
| `L.Hierarchy` pair | -21 | +1 | **-20** |
| **total** | **-173** | **+67** | **-106** |

**MINUS 106 IS AN ESTIMATE, NOT A MEASUREMENT, AND YOU MAY NOT TREAT IT AS A
TARGET YOU OWE.** The deletions are measured; every instantiation cost is a
guess. Seven survey bands have been tested in this campaign and five failed.
Your floor is minus 60.

## ORDER OF WORK, AND THIS IS NOT NEGOTIABLE

**`L.Choice.Before` GOES FIRST.** The whole block is gated on it: without
Before the net is about minus 43 and misses the floor. Before is also the
risk. `src/L/Choice/Before.lagda.md:680` records a **measured 99x seal**: the
region is `opaque` and unsealing it took 376 s against 3.8 s sealed.

1. Convert `Before`'s shape and graph blocks first.
2. **Measure Before's cold seconds before and after, and report them before
   you touch a second file.** If seconds rise above the noise rule, STOP. That
   is a refusal with a number and it is a full deliverable.
3. Then `Table`, then `Hierarchy`, then close by hosting and re-exporting in
   `Sequence`.

## THE STANDING GATES, which eight blocks have paid for

- **THE BREAK-EVEN GATE, before wiring the SECOND site.** Write the kit and
  typecheck it. Count its in-fence lines. Convert one site, measure the
  saving, and compute break-even as kit lines divided by that saving. **If
  break-even exceeds your site count, STOP and report the three numbers.**
  (The old wording said "before any wiring", which cannot be run because it
  needs a measured per-site saving. `[LJ-0.4f-R]` caught that.)
- **THE STAGING GATE.** Write the projection into your report before
  converting a second site, not after.
- **COUNT THE SITES BY GREPPING THE MECHANISM, tree-wide, before you write the
  kit.** Report the grep and the per-site line counts. **This gate exists
  because of today:** `[T208]`'s survey misread `Before` and never counted
  `L.Coding.Sequence` at all.
- **SUM THE SECONDS, including the kit's own.** A new module's check time is a
  cost the tree pays forever. LJ-0.4f measured plus 1.50 s for its kit and
  never entered it in the decision. **Report the tree-level seconds delta, not
  only the per-file ones.**
- **THE LINE-BAND STOP TRIGGER.** A stop is a deliverable in three cases:
  seconds rise, a consumer must unfold what it did not before, or the measured
  net cannot reach minus 60.
- **A CHAPTER MUST REMAIN A CHAPTER.** Block C took `Sound` from 801 in-fence
  lines to seven by moving 1,354 lines out, for a net of minus 59. If a file
  you touch ends up a re-export stub, you have failed.
- **D-27, NEW TODAY AND DIRECTLY ON POINT.** "No code consumer" identifies a
  dead helper, never a dead result. **Do not delete anything in this block.**
  You are MOVING shared shapes and leaving the mathematics where it is. If a
  block you fold turns out to have no consumer, leave it and say so.
- **THE NOISE RULE.** A per-file delta under 0.5 s or under 5 percent,
  whichever is larger, is noise: report it flat. Above that, run a third time
  and report all three numbers. **Never report a verdict word where a number
  fits.**
- **KIT PRESERVATION.** If you refuse, do NOT delete the kit. Move it to
  `_build/kits/lj-0.4n-<name>.lagda.md` and cite the path.

## THE FALSE FINDING, so you do not inherit it

`[LJ-0.4f]` reported that `Before` is "a direct recursion over ℕ with no graph
and no approximation, a different mechanism, not a third copy." **That is
FALSE and I repeated it in `dev/PLAN.md` before the review caught it.** It
read `Before:229-398` and generalized from one region.

`Before` holds a full assembly further down the same file: `RelStepAt` at
`:685`, `ApproxAt` at `:715`, `RelGraphAt` and `GraphOf` at `:747-766`,
`approx-val` at `:986-1014`, `rel-only` at `:1015-1026`, `PairRelGraph` at
`:1213-1241`. The file says so itself at `:662`: "follow the template".

**Before IS your largest site, at minus 63 estimated.** One grep would have
found it, which is why the site-grep gate above now exists.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Answer DD4 honestly here, and the honest answer is probably NO WING VALUE.**
`[LJ-0.4f-R]` read all six funded GCH blocks and found none that builds an
object-language recorded-graph recursion; `_build/lj-1.1-recon.md:181` says
the wing "leaves the delivered machinery alone: `L.Hierarchy`,
`L.Coding.Sequence` consumed as delivered, never copied." **So this block pays
for itself out of today's four sites or it does not pay at all.** Do not
inflate the kit to serve a consumer that does not exist. **But write it
generic in `Step` anyway**, because that is what makes it one parameter
instead of eleven.

## LITERATURE (DD18), AND IT DECIDES YOUR KIT'S SHAPE

`dev/literature/` holds the digested mathematics. This is not a formality for
this block. `[LJ-0.4f-R]` found the answer in the sources:

**Sacks and Zeman's Lemma 1.10 and Lemma 1.11 are two objects with one form.**
Two different recursions, with identical two-clause statements. The
consequence for you is exact:

- **Sharing the SHAPE captures what the literature states twice.** Correct.
- **Sharing the VALUE would unify what the literature keeps apart.** Wrong,
  and it is what LJ-0.4f's eleven-parameter kit drifted toward.

Read `dev/literature/digest.md` and `dev/literature/j-hierarchy.md` at the
order and well-order material. **If your kit starts to mention a recursion's
value, you have crossed the line the literature draws.** Say in the report
which side of it you stayed on.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-0.4f-review.md` sections 6 and 7. Read these FIRST.** Section 6
  is your kit, priced line by line, and section 7 ordered this dispatch.
- `_build/lj-0.4f-report.md`, the refusal you are building on, and
  `_build/kits/lj-0.4f-recassembly.lagda.md`, the 208-line kit your content
  comes out of. **Take the shape half and leave the induction half.**
- `_build/kits/lj-0.4f-hierarchy-wiring.diff`, the rescued 20-line
  instantiation that proves the wiring works.
- `_build/lj-0.8-review.md` 7.1, the standing gates.
- `dev/memos/simplification-register.md:33-38`, S13 to S18 with their
  verdicts. Do not re-propose their shapes.
- `dev/LESSONS.md` is NOT archived and still binds. **P-q, P-r, P-l, P-m and
  D-27 decide this block. D-10 is why you re-verify every line number.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk. **This is
  the rule that makes your kit one parameter: parameterize the MODULE.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.** Parameterized
  0.010 to 0.013 s per line, instantiation 0.22 to 0.297.
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **P-r.** A fold costs about 3x when consumers must UNFOLD its result type.
  Share the statement SHAPE, not a stored structure consumers take apart.
- **R-35, R-38**: sealing and opacity. **Before's seal is measured at 99x. Do
  not open it.**
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. Heap
  exhaustion is a wall to report, never a cap to raise.
- **C-22. Write the deliverable incrementally.** Block C ran 38 minutes and
  left an all-TODO skeleton. Fill each number as it lands.
- **D-10. Price the truth of a recorded residue before pricing its proof.**

## SCOPE (read)

`_build/lj-0.4f-review.md` sections 6 and 7 first. Then
`_build/kits/lj-0.4f-recassembly.lagda.md`. Then each site at its named lines.
Then the consumers by grep.

## SCOPE (write)

`src/L/Coding/Sequence.lagda.md`, `src/L/Choice/Table.lagda.md`,
`src/L/Choice/Before.lagda.md`, `src/L/Hierarchy.lagda.md`. **NO new master.**
Your report is `_build/lj-0.4n-report.md`. A refused kit goes to
`_build/kits/`. Never `src/Everything.lagda.md`.

## CONSTRAINTS

- **Never commit and never push.**
- **Do not change any theorem STATEMENT** and do not weaken a proof.
- **Do not delete anything.** See D-27 above. This block MOVES shapes.
- **Typecheck every file you edit AND every consumer you touch**, one process
  at a time. Do NOT run `make check` or a whole-tree check.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS.** Five of eight blocks refused
  and every refusal was worth having.
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-0.4n-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: LANDED with a net, or REFUSED with a net.
2. **THE SITE GREP**, with per-site line counts, written before the kit.
3. **BEFORE'S SECONDS**, before and after, reported before you touched a
   second file.
4. **THE NUMBER**: one table, in-fence before and after per file, and the net.
5. **THE SECONDS, SUMMED**, including the kit's own, tree level.
6. **WHAT I SHARED**, and what I left, with the P-r reasoning.
7. **DD4**: one line, and say plainly if the wing value is nil.
8. **LITERATURE USED**, and which side of the SZ shape-versus-value line you
   stayed on.
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
