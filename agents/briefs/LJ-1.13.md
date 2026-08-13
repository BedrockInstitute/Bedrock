# LJ-1.13: the collapse at an EXTENSIONAL carrier

tier: codex (default)

## GOAL

Deliver the Mostowski collapse's injectivity half at an **extensional**
carrier, not a transitive one. **Survey and price it before you build it**, and
report a refusal with a number if the price is wrong.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE FINDING YOU ARE ANSWERING

`[LJ-1.11]`, an adversarial review, finding **F2**, at
`_build/lj-1.11-review.md:368-392`. Read it before anything else.

Its content, and I have verified each claim against the tree myself:

- `src/V/Collapse.lagda.md:109` opens `module Inj (Xtr : isTrans X)`, and
  **everything downstream lives inside it**: `π-inj`, `π∈-bwd`, `iso`,
  `Mostowski`, `mostowski`, at `:170-205`.
- **But the chapter itself proves the collapse is the IDENTITY on a transitive
  carrier**: `fixes-X : isTrans X → ∀ y ∈ᵗ X → π y ≡ y`, at `:272-273`.
- **So the delivered Mostowski package holds only where it is trivial.**
- The condensation step collapses the HULL, and the hull **is not transitive**
  (`_build/lj-1.3-report.md` section 4).
- Devlin 5.2 collapses an **extensional** substructure and derives
  extensionality from `X ≺₁ L_α` (`dev2.txt:1178-1183`).

**The proof shape does not adapt by weakening a hypothesis.** `in⊆` and `out⊆`
at `:115-155` pull members of `x` into `X` through `Xtr`, which is simply
false at a non-transitive carrier. It needs the structure-extensionality
argument instead.

**What stays sound and must not be touched:** `π`, `π-compute`, `πX`,
`πX-trans`, `π∈-fwd`, `unique` and `fixes` are delivered WITHOUT `Xtr` and
match the literature. `fixes` is exactly 5.2(ii).

## SURVEY FIRST, AND THE SURVEY IS A DELIVERABLE

`[LJ-1.11]` estimated 80 to 200 lines, one ∈-induction of the same size class
as `Inj`, and **marked it INF, survey**. That is a bracket from a comparable,
not a price at this site, and `dev/LESSONS.md` **P-l** refuses that transfer.

So: **before you write the induction, write the statement and the shape, and
put your own estimate in the report.** If your estimate lands outside 80 to
200, say so with the reason. A survey that corrects the review is a full
result.

**The extensionality hypothesis is yours to choose and to state.** Devlin
derives it from `X ≺₁ L_α`. You are building the collapse, not the hull, so
take extensionality as a hypothesis on the carrier and name it exactly.
`[LJ-1.14]` is separately proving the elementarity that would discharge it.

## DD4, AND HERE IT IS THE POINT OF THE TASK

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**A collapse at an extensional carrier is tower-agnostic**, and that is why
this is worth building well. The J tower collapses too. So:

- **Parameterize the MODULE, not the functions** (P-h). `Inj` already shows
  the shape: the hypothesis is a module parameter.
- **Do not mention `Lset`, the Def tower or any stage presentation** in the
  new statements. If a stage's presentation reaches your types, P-l says you
  bought lines and lost seconds.
- Say in the return **what the J tower would have to supply** to instantiate
  it. One paragraph, and it is a real deliverable.

## D-28, BECAUSE YOU MAY BE TEMPTED TO SHARE

`dev/LESSONS.md` **D-28**: a kit's break-even is set by its PARAMETER count,
not its line count. If you find yourself factoring the transitive and
extensional cases through one parameterized core, **count the parameters
first**. Eleven parameters over two sites measured plus 4 lines this week; one
parameter over five sites measured minus 104.

**Two consumers is not enough to pay for a kit.** Write the extensional case
directly unless the shared core takes one or two parameters.

## LITERATURE (DD18)

- **`dev2.txt:1178-1183` is your target statement.** Devlin 5.2. Read it in
  `_build/literature/dev2.txt` and quote it in the report.
- `dev/literature/digest.md` for the orthodox route.
- `dev/literature/devlin-errata.md`: the book has known errors, so check
  before you trust a step.
- **`[LJ-0.7]` is digesting II.5 right now and its output is not available to
  you.** Work from the source. If your reading of 5.2 disagrees with the
  review's, say so; two independent readings of one page are worth having.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- `_build/lj-1.11-review.md:368-392`, F2, your commissioning document.
- `_build/lj-1.4-report.md`, what the delivered collapse actually did, and
  where it took Devlin 5.2(ii) beyond the archive.
- `archive/rud-route/` and `archive/dev/TASKS-archived.md`: the retired route
  had a collapse. **Say whether its shape survives the route change**, and if
  it assumed transitivity too, say that.
- `dev/LESSONS.md` is NOT archived and still binds. **P-h, P-l, R-35, R-40 and
  D-28 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.**
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38**: sealing and opacity.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot. Heap exhaustion is a wall to report, never a cap to
  raise.
- **C-22. Write the deliverable incrementally.**
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  F2 is a residue and I have verified its `file:line` claims, not its
  estimate.

## THE SIBLING, AND THE TERRITORY RULE

`[LJ-1.14]` is building in `src/L/Hull.lagda.md` right now. **Neither file
imports the other**, which I checked, so you are cone-disjoint and may both
measure. Keep it that way:

- **Write only `src/V/Collapse.lagda.md`.**
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only.
- **Never commit and never push.**

## SCOPE (read)

`_build/lj-1.11-review.md:368-392` first. Then `src/V/Collapse.lagda.md` in
full. Then `dev2.txt` at the cited lines. Then `_build/lj-1.4-report.md`.

## SCOPE (write)

`src/V/Collapse.lagda.md`. Your report is `_build/lj-1.13-report.md`. Never
`src/Everything.lagda.md`, and never `src/L/Hull.lagda.md`.

## CONSTRAINTS

- **Do not weaken or delete anything that stands.** `π`, `π-compute`, `πX`,
  `πX-trans`, `π∈-fwd`, `unique` and `fixes` are correct as delivered.
- **Keep the transitive `Inj` module.** It is not wrong, only trivial, and
  D-27 says a chapter's stated result is not deleted to make room.
- **Typecheck every file you edit**, one process at a time. Do NOT run `make
  check` or a whole-tree check.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand. DD26
  excludes the two catalogs from every size figure.
- **Report cold seconds** for the file, before and after, with the noise rule:
  under 0.5 s or under 5 percent, whichever is larger, is flat.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only. Do not
  write chapter narrative.
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.13-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: delivered with a line count, or refused with a
   price.
2. **YOUR OWN ESTIMATE**, written BEFORE you built, against the review's 80 to
   200.
3. **THE STATEMENT**: the extensionality hypothesis you took, exactly.
4. **THE NUMBER**: in-fence before and after, ledger caliber.
5. **SECONDS**: cold, before and after, with exit codes.
6. **WHAT THE J TOWER WOULD SUPPLY** to instantiate it (DD4).
7. **WHERE MY READING OF 5.2 DIFFERS** from the review's, if it does.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
