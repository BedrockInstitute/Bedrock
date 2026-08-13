# LJ-1.3: build the Skolem hull

tier: codex (default)

## GOAL

Deliver `src/L/Hull.lagda.md`: the Skolem hull of a parameter set inside an L
stage, built as a least-witness search over the delivered well-order, with the
Tarski-Vaught criterion. Target 340 to 540 non-blank in-fence lines.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## CONTEXT

`src/` proves `L ⊨ ZF` and `L ⊨ ZFC` on the internalization tower: 77 masters,
17,511 non-blank in-fence lines, cold 133.39 s. Phase 1 builds a `L ⊨ GCH`
wing, planned by `[LJ-1.1]` in `_build/lj-1.1-recon.md`.

**You are block 1 of that plan.** The hull is the FIRST step of the
condensation argument: for a set `X` inside a stage, take a `Σ₁`-elementary
substructure of that stage containing `X`, of the same cardinality. Its
collapse is then an earlier L stage, which is condensation.

**Block 2 already landed.** `[LJ-1.4]` delivered `src/V/Collapse.lagda.md`,
239 in-fence lines, carrier-generic, checking at 0.0080 s/line inside DD24's
bar. Your hull feeds it.

**No prose.** DD23 freezes mathematical prose until both trophies land. Write
the marker structure a master needs and the shortest honest catalog line.
**This is code.**

## THE STATEMENT, from `[LJ-1.1]` block 1

- `Elementary` and `TarskiVaught` are equivalent at a transitive set carrier
  inside a stage.
- The hull of a parameter set `X` inside `Lset α` is the `sett` over pairs of
  a formula and a small witness.
- The value at a pair is the **least witness in the meta well-order**.
- The hull contains `X`.
- The hull satisfies the Tarski-Vaught criterion at its own parameter source.

## WHAT IT RIDES, ALL DELIVERED, WITH SITES

`[LJ-1.1]` section 2 read the tree for exactly this and named them:

- `abs₀`, `σ₁-up`, `π₁-down` (`src/FOL/Absoluteness.lagda.md:122-190`), the
  transfer theorems. **`[LJ-0.4a]` deliberately kept `σ₁-up` and `π₁-down`
  when it removed 48 dead names, because this block rides them.** They have no
  other consumer yet. You are it.
- `leastOf` (`src/L/WellOrder/Base.lagda.md:158`).
- `orderAt` (`src/L/Choice/Step.lagda.md:740`) and `stageOrder` (`:748`).
- `∈-asFiber` (`src/V/Smallness.lagda.md:41`).
- `Lset-layer` (`src/L/Constructible.lagda.md:246`).
- `Δ₀`, `Σ₁`, `Π₁` (`src/FOL/LevyHierarchy.lagda.md:47-80`).

**Verify each site before you build on it.** `[LJ-1.1]` was a recon and one of
its citations was already found wrong by an audit, so check rather than trust.

## THE METHOD IS THE WELL-ORDER, NOT REFLECTION

`[LJ-1.1]` is explicit about this and it is its disagreement number 2 with the
original plan: **do not build fresh `Σ₁` machinery, and do not build the hull
out of reflection.** The archived hull chapter prices reflection as the wrong
instrument, because its closures cannot be iterated into a hull
(`archive/rud-route/src/L/Hull.lagda.md:5-9`).

**The hull rides the AC wing's delivered well-order.** The value at a
formula-and-witness pair is the least witness under `leastOf` over `orderAt`.
That is why this block is affordable at all, and it is a direct DD4 win: the
GCH wing reuses the machinery `L ⊨ AC` already paid for.

## THE ARCHIVE IS ADAPTABLE, NOT PORTABLE

`archive/rud-route/src/L/Hull.lagda.md`, **241 in-fence lines**. `[LJ-1.1]`
graded it **ADAPTABLE**, one step weaker than the collapse's PORTABLE:

> The shape (`Elementary`, `TarskiVaught`, `TV-thm`, `Hull` as a `sett` over
> formula-and-witness pairs, `leastWit` via `leastOf` over `orderAt`) rides the
> current tree. The imports need re-pointing: `V.Presentation` is missing, and
> the tree uses `∈-asFiber` instead.

**`V.Presentation` is now in the tree** (`[LJ-0.6]` restored it), so you may
use either it or `∈-asFiber`. Say which you chose and why.

**DD13: price the port against a fresh write before you take it.** The archive
served the rud/J tower, so its stage-side assumptions may not hold here. This
is the difference between ADAPTABLE and PORTABLE, and it is your judgement to
make. `dev/LESSONS.md` P-l: a measured cure does not transfer by analogy.

**One data point from `[LJ-1.4]`, and it cuts toward porting**: the collapse
ported at 181 archived lines to 239 delivered, stayed fully generic, and
checked at the parameterized rate. The archive's idiom does fit this tree.
**That is evidence, not a decision.** The collapse was graded PORTABLE and
yours is not.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**`[LJ-1.1]` priced both shapes for this block.** Generic in the stage `α` and
the parameter set `X`: 241 to 388 lines. Fixed at a concrete stage: 300 to 450
lines, checking at about twenty times the seconds, because P-m puts
instantiation near 0.22 s per line against 0.01 for parameterized work.
**Generic wins on lines and on seconds.**

`[LJ-1.1]` also names the ONE atom that must be fixed: the order membership
`pr x y ∈̇ con orderL` at hull parameters, with its adequacy from `orderL-fill`
and `orderL-rep` (`src/L/Choice/Order.lagda.md:696-702`). **Fix that one and
nothing else**, and say in your report if you had to fix more. A stop-line is
never a reason to write fixed: say so and stop for a re-price.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk. The hull is
  exactly a definability walk. **Make the stage and the parameter set module
  parameters.** `[LJ-1.4]` did this and checked at the parameterized rate.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** The hull is about a concrete stage
  `Lset α`. Keep `α` opaque and the stage an ATOM to the elaborator. **This is
  the single biggest seconds risk in this block.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.** Parameterized
  0.010 to 0.013 s per line, instantiation 0.22 to 0.297.
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38**: sealing and opacity.
- **R-40. A deep successor-chain membership witness normalizes
  super-linearly; climb by small closures.** The hull quantifies over stage
  members; state witnesses SHALLOW.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. Heap
  exhaustion is a wall to report, never a cap to raise.
- **C-22. Write the deliverable incrementally.** Chapter and report both.
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  The Tarski-Vaught equivalence at a transitive set carrier inside a stage is
  a recorded TARGET. **Check it is TRUE at the generality you need before you
  price its proof.** This campaign lost a bridge kernel to a hypothesis that
  was classically false.

## ARCHIVE

Per DD18.

- `archive/rud-route/src/L/Hull.lagda.md`, 241 in-fence. **Your comparable.**
  Read it in full, including its own design note at `:5-9` about reflection.
- `_build/lj-1.1-recon.md` block 1, section 2, and section 8's verdicts.
- `_build/lj-1.4-report.md`: how the sibling port went, what it kept generic.
- `src/V/Collapse.lagda.md`: the chapter your hull feeds. Match its idiom.
- `archive/dev/TASKS-archived.md` for any hull row.
- `dev/LESSONS.md` is NOT archived and still binds.

Report an **ARCHIVE USED** section at `file:line`, with what you took and what
you rejected.

## SCOPE (read)

`archive/rud-route/src/L/Hull.lagda.md` first. Then the delivered sites listed
above. Then `src/V/Collapse.lagda.md` for idiom, `dev/STYLE-agda.md` and
`dev/STYLE-i18n.md` for the master's shape.

## SCOPE (write)

`src/L/Hull.lagda.md`, new, and your report `_build/lj-1.3-report.md`. Nothing
else under `src/`, and `src/Everything.lagda.md` is the orchestrator's.

## CONSTRAINTS

- **Never commit and never push.**
- **Typecheck your chapter**, `GHCRTS="-A64m -I0 -M8g" agda
  src/L/Hull.lagda.md`, ONE process. Report exit code and seconds. Do NOT run
  `make check` or a whole-tree check.
- **Do not touch `src/Everything.lagda.md`.** Your chapter will not be in the
  tree index until the orchestrator wires it. That is expected.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py`** on your file.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand.
- **Evidence is `file:line`.**
- **A stop is a deliverable.** If Tarski-Vaught is false at the needed
  generality, or the least-witness search does not close over the delivered
  order, give the evidence and STOP.
- Write ASD-STE100 in the report: active voice, one instruction per sentence,
  20 words or fewer, no em dash.

## RETURN

Write `_build/lj-1.3-report.md` INCREMENTALLY, skeleton first.

1. **WHAT LANDED**: statements delivered, at `file:line` in your chapter.
2. **PORT OR FRESH WRITE** (DD13): which, the price of each, why.
3. **GENERIC OR FIXED** (DD4): what stayed generic, what you fixed beyond the
   one named atom, and why.
4. **THE TARSKI-VAUGHT EQUIVALENCE** (D-10): true at the generality used, and
   how you checked.
5. **THE MEASUREMENT**: in-fence lines, typecheck seconds, exit code, and your
   seconds per line against the tree's 0.007693 baseline
   (`dev/ledger.toml` `[ratio]`), because DD24 judges the wing on that.
6. **WHAT THE CONDENSATION BLOCK WILL NEED FROM YOU**, so `[LJ-1.5]` can be
   briefed without re-reading your chapter.
7. **ARCHIVE USED.**
8. **WHAT I AM NOT SURE OF.**
