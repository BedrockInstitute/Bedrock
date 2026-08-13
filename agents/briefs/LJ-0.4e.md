# LJ-0.4e: compression blocks E and G

tier: codex (default)

## GOAL

Two small independent blocks, one agent, disjoint files. Share the identical
traversals across `FOL/Manipulation`, and collapse the two lex orders in
`L/Choice/Name` into one kit. Land 100 to 200 non-blank in-fence lines of
reduction **without adding wall seconds**.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## CONTEXT AND THE BAR

The owner set the compression as a PREREQUISITE to the GCH wing, with a
two-part bar recorded in `dev/ledger.toml`:

- **reach about 16,400 AC-side in-fence lines**, from 17,272 today;
- **without badly worsening the seconds-per-line ratio.**

**Understand what the second half can mean, because it decides how you work.**
Compression removes lines. If seconds stay flat the ratio MUST rise: 132.87 s
over 16,400 lines is 0.008102 against today's 0.007693, up 5.3 percent, and
that is arithmetic rather than failure. **So the real bar is on SECONDS: your
block must not add any.** The failure to catch is a block that buys lines by
paying seconds.

Sibling agents hold the other territories. `dev/LESSONS.md` C-25: two writers
may not share a file. **Your territory is exactly:
`src/FOL/Manipulation/{Renaming,Relabelling,Bounding,Relativize,Parameters}.lagda.md`
and `src/L/Choice/Name.lagda.md`.** Nothing else, and never
`src/Everything.lagda.md`.

## BLOCK E: the FOL/Manipulation traversal share

`[L3.32-T208]` measured lever (e) at **minus 60 to minus 120**, narrowed from
the July survey's minus 120 to minus 200. The sites: `Renaming` 13-25 and
`Relabelling` 15-27 carry **identical traversals**
(`_build/l3.32-t208-report.md` 3.5). `[LJ-0.4]` extends the block to
`Bounding`, `Relativize` and `Parameters`.

**THE BOUNDARY IS S17 AND IT IS A HARD ONE.** `dev/memos/simplification-register.md:37`
records S17, the `FOL.Fold` fusion over these very modules: **probe RED. A
stored decomposition walled at 12 GB; the inline version ran in one second.**

So: **share the bare traversal SKELETON only.** No stored decomposition. No
fusion lemma. No datatype that consumers must unfold. If your extraction
introduces either, you are rebuilding S17 and the probe already said what
happens.

## BLOCK G: the lex-order kit

`[LJ-0.4]`'s N6, **minus 40 to minus 80**. `src/L/Choice/Name.lagda.md` carries
`_≺ᵥ_` at 265-334 and `_≺ₙ_` at 336-410: **two levels of the same
lexicographic order with the same law suite.** One kit, instantiated twice.

**The risk `[LJ-0.4]` names is that a well-founded lex is delicate.** The laws
include well-foundedness, and a generic kit must carry it without weakening
it. If the accessibility proof does not go through generically, that is a stop
for this block, not a reason to weaken the law.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Both blocks ARE the rule applied.** Block E replaces repeated fixed
traversals with one generic traversal. Block G replaces two copies of a lex
order with one kit instantiated twice. `[LJ-0.4]` scores E medium-high and G
medium on DD4 value.

**So write the shared forms generic at full strength**, and say in your report
what the GCH wing or the later two-tower route could instantiate. A kit that
serves only these two call sites is worth less than one the wing can reuse. A
stop-line is never a reason to write fixed: say so and stop for a re-price.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk. Your shared
  traversal and your lex kit take their parameters as MODULE parameters.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.** Parameterized
  0.010 to 0.013 s per line, instantiation 0.22 to 0.297.
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38**: sealing and opacity.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. Siblings hold
  the other slots. Heap exhaustion is a wall to report, never a cap to raise.
- **C-22. Write the deliverable incrementally.**
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  Both figures are T208's measurements of `main`. Re-verify the sites.

## ARCHIVE

Per DD18.

- `_build/l3.32-t208-report.md` 3.5: lever (e) measured, with its sites.
- `_build/lj-0.4-compression.md` sections 3 and 5: N6, and the E and G rows.
- **`dev/memos/simplification-register.md:37`, S17.** The RED probe that
  bounds block E. Read it before you design anything.
- `_build/lj-0.4a-report.md` section 6: generalizations block A saw and did
  not build. Item 3 is about spec lemmas and P-k; it may touch your files.
- `dev/LESSONS.md` is NOT archived and still binds. **P-r and P-q are the two
  that decide these blocks.**

Report an **ARCHIVE USED** section at `file:line`.

## SCOPE (read)

Your six files in full. Then their consumers, found by grep, at the sites you
intend to change. Then the reports above.

## SCOPE (write)

`src/FOL/Manipulation/Renaming.lagda.md`,
`src/FOL/Manipulation/Relabelling.lagda.md`,
`src/FOL/Manipulation/Bounding.lagda.md`,
`src/FOL/Manipulation/Relativize.lagda.md`,
`src/FOL/Manipulation/Parameters.lagda.md`,
`src/L/Choice/Name.lagda.md`, plus at most ONE new shared module for E and
ONE for G. Your report is `_build/lj-0.4e-report.md`. Nothing else under
`src/`, and never `src/Everything.lagda.md`.

## CONSTRAINTS

- **Never commit and never push.**
- **Do not change any theorem STATEMENT** and do not weaken a proof. The tree
  proves `L ⊨ ZF` and `L ⊨ ZFC` and must still prove them.
- **Typecheck every file you edit AND every consumer you touch**, one process
  at a time. Do NOT run `make check` or a whole-tree check: the orchestrator
  schedules those and siblings hold the other slots.
- **REPORT SECONDS BEFORE AND AFTER for every file you edit.** This is the
  owner's bar and the report is judged on it. A block that removes lines and
  adds seconds does not land.
- **The two blocks are independent.** If E stops, G may still land, and the
  reverse. Report them separately and do not let one failure sink the other.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py`** on your files.
- **Evidence is `file:line`.**
- **A stop is a deliverable**, per block. A refused block with a measurement
  is worth more than a landed block that slows the tree.
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-0.4e-report.md` INCREMENTALLY, skeleton first. Report E and G
under separate headings, each with:

1. **THE NUMBER**: in-fence lines before and after, per file.
2. **SECONDS**: before and after, per file and per consumer, with exit codes.
   **The owner's bar is here.**
3. **WHAT I SHARED**, and for E specifically, how you stayed on the safe side
   of S17: no stored decomposition, no fusion lemma.
4. **WHAT THE WING COULD INSTANTIATE** (DD4).
5. **CONSUMERS RE-VERIFIED**: which, exit codes.

Then once, at the end:

6. **ARCHIVE USED.**
7. **WHAT I AM NOT SURE OF.**
