# LJ-0.4c: compression block C, the Unique and Sound clause frames

tier: codex (default)

## GOAL

Extract the repeated clause frames out of `L/Coding/Unique` and
`L/Coding/Sound` into one new shared module, and land 180 to 315 non-blank
in-fence lines of reduction with the tree still green.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## CONTEXT AND PRIORITY

The owner set a compression target of about **16.4k** on the AC side of the
tree, as a PREREQUISITE to the GCH wing. That is the highest-priority work in
this campaign.

The AC side stands at **17,272** non-blank in-fence lines, so about **872**
are still owed. `[LJ-0.4a]` delivered block A, minus 240. **You are block C**,
the largest single remaining block by value.

`src/` proves `L ⊨ ZF` and `L ⊨ ZFC`. The whole tree, including a 239-line GCH
wing chapter, is 17,511 and checks cold in 133.39 s.

**A sibling agent holds the other Agda slot**, building `src/L/Hull.lagda.md`,
a NEW file. `dev/LESSONS.md` C-25: two writers may not share a file. **Your
territory is `src/L/Coding/Unique.lagda.md`, `src/L/Coding/Sound.lagda.md`,
and one new module.** Nothing else.

## WHAT TO EXTRACT

`[L3.32-T208]` measured lever (b), verbatim-repeat extraction in `Sound` and
`Unique`, at **minus 55 to minus 75**: byte-identical blocks, naming the
`Sound` termAgree witness and the `Unique` domAt-in setup
(`_build/l3.32-t208-report.md` 3.2). `[LJ-0.4]` then found two more classes at
the same site that the July survey missed:

- **N2, the per-clause proof shell in `Unique`**, minus 60 to minus 130: the
  twelve clause bodies at `Unique` 117-603, 487 lines total. The `PT.rec` over
  `domAt-in`, the where-blocks, and the `extensionalV` skeleton repeat once per
  clause.
- **N3, the residual connective pairs in `Sound`**, minus 30 to minus 60:
  and/or at 257-301, exist/forall at 576-661, allIn/exIn at 471-576, mem/eq at
  661-739, top/bot at 437-471, imp/neg at 739-792.

Plus lever (d)'s share at this site: the frame retrofit of the pre-law
chapters, `Unique` clause types 61-83 and the `Sound` soundness product
792-801, measured at minus 90 to minus 125 across the block
(`_build/l3.32-t208-report.md` 3.4).

**Re-verify every site before you touch it.** These are measurements of
`main`, and block A has since edited neither of your two files, but check
rather than assume. D-10: a recorded residue names a target and the target can
be false.

## THE HAZARD THAT DECIDES THIS BLOCK

`[LJ-0.4]` rates the consumer risk **medium** with a specific reason: **the
pinned result type is unfolded by consumers.** That is the P-r shape.

`dev/LESSONS.md` **P-r**: a fold over a clause list costs about **3x the
hand-written conjunction** when its result type must be UNFOLDED by every
consumer. `[LJ-0.4]` checked and reports that a full fold over the twelve
clauses is OUT, because `Uniform` 99-101 and `Internal` 372 unfold the pinned
type.

**So extract the SHELL, not the fold.** Share the proof skeleton that repeats
around each clause. Do not introduce a data structure that consumers must
unfold to use. **If your extraction makes a consumer unfold something it did
not before, you have built the P-r shape and the seconds will tell you.**

**Measure it, do not assume it.** Time `Unique` and `Sound` before and after,
one process each, and report both. A block that removes 200 lines and adds 60
seconds is a loss, and `dev/LESSONS.md` P-q is the reason the two must be
measured separately: a line lever is not a seconds lever.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**This block has the highest DD4 value of all eight**, and `[LJ-0.4]` says so.
The frames you extract are the frames **the GCH wing's twelve clauses will
instantiate**. `[LJ-1.2]`'s NO-GO and `[LJ-1.10]`'s re-price both turn on the
twelve-clause satisfaction structure, and `[LJ-1.5]`'s condensation core will
meet the same shape.

**So price your work by what it makes cheaper later, not only by the lines it
removes today.** Write the shared module generic at full strength: a frame the
wing can instantiate is worth more than a frame that only serves these two
files. Say in your report what the wing would inherit. A stop-line is never a
reason to write fixed.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk. Your shared
  module should take its carrier and its clause data as MODULE parameters.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.** Relevant: a
  shared frame tempts you to move lemmas to the new module. Move only what the
  consumers of the new module use.
- **P-m. The check-cost rate is a content-class certificate.** Parameterized
  0.010 to 0.013 s per line, instantiation 0.22 to 0.297.
- **P-n. Satisfaction content at a concrete carrier is a payable floor**, not
  a defect. `Sound` and `Unique` ARE satisfaction content; do not try to make
  their floor go away.
- **R-35, R-38**: sealing and opacity.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot. Heap exhaustion is a wall to report, never a cap to
  raise.
- **C-22. Write the deliverable incrementally.**
- **D-10. Price the truth of a recorded residue before pricing its proof.**

## ARCHIVE

Per DD18.

- `_build/l3.32-t208-report.md` 3.2 and 3.4: the measured levers at your site.
- `_build/lj-0.4-compression.md` sections 3 and 5: N2, N3, and block C's row.
- `dev/memos/simplification-register.md:33-38`: **S14 and S16 were REVERTED at
  their gates and S17's probe returned RED.** Read those three before you
  propose anything resembling them: S14 was a defSet computation table at 112
  lines against a 57-line stop-line, S16 an axiom-frame kit whose conversion
  regression ran over 15 minutes, S17 a fold whose stored decomposition walled
  at 12 GB.
- `_build/lj-0.4a-report.md` section 6: generalizations the block-A agent saw
  at your site and deliberately did not build.
- `dev/LESSONS.md` is NOT archived and still binds. **P-r is the one that
  decides this block.**

Report an **ARCHIVE USED** section at `file:line`.

## SCOPE (read)

`src/L/Coding/Unique.lagda.md` and `src/L/Coding/Sound.lagda.md` in full, then
their consumers `src/L/Coding/Uniform.lagda.md` and
`src/L/Choice/Internal.lagda.md` at the unfold sites named above. Then the
reports.

## SCOPE (write)

`src/L/Coding/Unique.lagda.md`, `src/L/Coding/Sound.lagda.md`, and ONE new
module under `src/L/Coding/`. Your report is `_build/lj-0.4c-report.md`.
Nothing else under `src/`, and `src/Everything.lagda.md` is the
orchestrator's.

## CONSTRAINTS

- **Never commit and never push.**
- **Do not change any theorem STATEMENT**, and do not weaken a proof. The tree
  proves `L ⊨ ZF` and `L ⊨ ZFC` and must still prove them.
- **Typecheck both edited masters AND their named consumers**, one process at
  a time, `GHCRTS="-A64m -I0 -M8g"`. A frame change that breaks a consumer is
  the failure mode here. Do NOT run `make check` or a whole-tree check.
- **Report seconds before and after** for `Unique`, `Sound`, and any consumer
  you touched.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py`** on your files.
- **Evidence is `file:line`.**
- **A stop is a deliverable.** If the extraction costs seconds, or forces a
  consumer to unfold, report the measurement and STOP. A refused block with a
  number is worth more than a landed block that slows the tree.
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-0.4c-report.md` INCREMENTALLY, skeleton first.

1. **THE NUMBER**: in-fence lines before and after, per file and total.
2. **SECONDS**: before and after, per file, with exit codes. **This section
   decides whether the block should land.**
3. **WHAT I EXTRACTED**, and what I deliberately left, with the P-r reasoning.
4. **WHAT THE GCH WING INHERITS** (DD4), concretely.
5. **CONSUMERS RE-VERIFIED**: which, exit codes.
6. **ARCHIVE USED.**
7. **WHAT I AM NOT SURE OF.**
