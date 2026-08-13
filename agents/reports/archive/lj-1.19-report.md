# LJ-1.19 report: Cure A, closure under plus omega

## 1. THE VERDICT

**GO, at 30 body lines.** The bound closes under the restriction. The
consumer survives. The probe is `src/ProbeLJ119.agda`. It typechecks under
`GHCRTS="-A64m -I0 -M8g"`, one process, exit 0. The body is 30 non-blank
non-comment lines (`src/ProbeLJ119.agda:35-76`). The full probe is 48
non-blank non-comment lines. Both sit under the 50-line gate.

The cure is generic in the carrier. The stage `δ` and the level `α` are
variables; no concrete stage enters a type (P-l). The module is
parameterized by `{ℓ}` and `lem` (P-h).

## 2. DOES THE CONSUMER SURVIVE THE RESTRICTION?

**YES.** The wing applies condensation once. Devlin 5.5 takes a hull of
`L_λ` with `λ` a limit ordinal at or above the cardinal `κ`, and collapses
it to `L_γ` with `γ < κ` (`_build/literature/dev2.txt:1372-1384`). The
crossing's bound sits at `γ+ω`. The cardinal arithmetic gives `γ+ω < κ`,
because `|γ+ω| = |γ| < κ`. So the bound lands inside `L_κ`, hence inside
`L_λ`. Devlin 5.6 inherits the shape at `κ⁺`
(`_build/literature/dev2.txt:1386-1388`). A successor cardinal is closed
under `+ω`.

The consumer must choose `λ` closed under `+ω`. The choice is free. Devlin
asks only that `λ` be a limit, `λ ≥ κ`, and `x ∈ L_λ`. Any cardinal above
both `κ` and the stage of `x` meets all three and is closed under `+ω`.
That is a hypothesis change, exactly what Cure A means.

The generic condensation lemma 5.2 gains the side condition "`α` closed
under `+ω`". No wing application violates it. `[LJ-1.7]` applies 5.5 at
cardinals. `[LJ-1.8]` applies 5.6 at `κ⁺`. The `κ ≤ ω` case is trivial and
uses no condensation (`dev2.txt:1375`). The wing's single application is
documented (`dev/literature/devlin-II5.md:420-428`), and the archive names
the condensation site as the level Devlin 5.5 uses
(`_build/l3.32-t91-report.md:85-89`). The J tower has no Def step, so the
restriction does not touch it (`_build/lj-1.15-review.md:359`).

## 3. THE LINE COUNT

The cure's body is 30 non-blank non-comment lines
(`src/ProbeLJ119.agda:35-76`). The pieces are: the `+ω` extension and its
iterate law (`:35-61`), the closure predicate (`:43-44`), and the two
closing theorems (`:66-76`). The full probe is 48 non-blank non-comment
lines and 66 non-blank lines with comments. The gate is 50. Every code
caliber passes.

The gate measures the cure, not the scaffolding. The review's estimate,
"under 50 lines, a case split", matches the 30-line body
(`_build/lj-1.15-review.md:175`).

## 4. SECONDS AND RATE

The warm check takes 0.57 seconds. The first check after the import fix
takes 0.70 seconds. One Agda process, heap cap `-M8g`, exit 0.

The rate at the full-probe caliber, 48 lines with comments excluded, is
0.0119 seconds per line. That sits under the 0.013193 bar
(`dev/ledger.toml:243-246`). The rate at the ledger caliber, 66 lines with
comments, is 0.0086. The rate at the 30-line body is 0.019, above the bar.
The body is a small unit; it pays a fixed module-load floor. The bar
assumes a build-sized module.

## 5. WHERE THE ARCHIVE USED THIS ON THE J SIDE

The J side answered the same bound-in-carrier question by restricting the
carrier, not by new mathematics. The strengthened domain bound "is a member
of the carrier only above the first limit", and the chapter records the
bound as a parameter of the meta clause, discharged wherever the carrier
names it (`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:203`,
`:209-213`). The review's citation at `:210-212` sits inside that passage.

## 6. THE RIVAL CURE

The induction-hypothesis route and Cure A address different claims. The
retired route carried `hierL β ∈ˢ Sset γ` as an induction hypothesis
(`_build/l3.31-r2probe-report.md:153-158`). That is the GRAPH containment,
the other half of statement 2. It does not move the BOUND's rank `δ+ω`.
Cure A moves the bound. It does not close the graph's set-as-element
definability step (`_build/lj-1.15-review.md:216`). The two cures are
complementary.

For the bound, Cure A is the cheaper route. It is a hypothesis change, and
this probe measures it at 30 lines. The induction route does not supply the
bound's rank. For the graph, the induction route is cheaper than building
the missing definability content, at the archive's measured 13-line
re-derivation pattern (`_build/l3.31-r2probe-report.md:175-180`).

## 7. THE STAGE-ARITHMETIC KIT (DD4)

The kit would contain: the `+ω` extension with its two membership
directions and its limit law, the closure predicate, the finite-iterate
membership law, the two `Lset-mono` lifting patterns, and the
members-to-set definability step. Both towers want it. The current tree
has no `+ω` in any master; the archived `L.Rud.OrdBlocks` held it, and the
probe re-derives the slice it needs (`archive/rud-route/src/L/Rud/OrdBlocks.lagda.md:97-155`).

## 8. LITERATURE USED

- `_build/literature/dev2.txt:1372-1384` (5.5). **USED and decisive.** The
  consumer's `λ` and `γ` satisfy `γ+ω < κ ≤ λ`. The `κ ≤ ω` case is
  trivial, no condensation.
- `_build/literature/dev2.txt:600-609` (K(u)). **USED.** Devlin's finite
  sequences make his bound rank `δ+4`.
- `_build/literature/dev2.txt:676-678` (2.6(ii)). **USED.** The sequence up
  to `γ` lies in `L_{γ+4}`. So Devlin's argument needs no closure: for
  every limit `α > γ`, the witness lands inside `L_α`. His coding makes
  the restriction unnecessary. The tree's tree-coding makes it necessary.
- `_build/literature/dev2.txt:1386-1388` (5.6). **USED.** The application
  at `κ⁺`, closed under `+ω`.
- `dev/literature/devlin-II5.md:145-164`. **USED.** The 5.5-5.6 digest with
  the `λ ≥ κ` choice.
- `dev/literature/devlin-II5.md:218-226`. **USED.** The witness inside the
  carrier is the load-bearing requirement.
- `dev/literature/devlin-II5.md:420-428`. **USED.** The wing's single
  condensation application.
- `dev/literature/j-hierarchy.md:75-110`. **USED.** The SZ side, for the
  condensation shape and the omega-times-alpha indexing.
- `dev/literature/devlin-errata.md`. **NOT USED.** `[LJ-1.14]` verified it
  does not cover Chapter II section 5. No errata changes a rank.

## 9. ARCHIVE USED

- `_build/lj-1.15-review.md`. Read in full. Took section 3.4 (Cure A and
  the failure case), section 3.5 and 8.5 (the fourth cure), section 7 (the
  J-side precedent), and section 8.4 (the consumer check this probe runs).
- `_build/lj-1.15-report.md:70-321`. Took the measured clause and the 37
  closing lines, and the bound's `δ+ω` diagnosis.
- `archive/rud-route/src/L/Rud/LevelSigma.lagda.md:203`, `:209-213`. The
  J-side restriction precedent. Section 5 rests on it.
- `archive/rud-route/src/L/Rud/OrdBlocks.lagda.md:97-155`. The `+ω`
  construction and its iterate law. The probe re-derives that slice.
- `archive/rud-route/src/L/Condensation.lagda.md:150-190`. The condensation
  face: `HasLevels`, `Covered`, `CrossOut`, `Condenses`. Read for the
  consumer's shape. The current tree has no `src/L/Condensation.lagda.md`;
  the chapter was cut by D32, and `[LJ-1.5]` is still planned.
- `_build/l3.31-r2probe-report.md:153-158` and `:175-180`. The
  induction-hypothesis cure and the 13-line re-derivation pattern. Section
  6 rests on them.
- `_build/l3.32-t91-report.md:85-89`. The condensation site named as the
  level Devlin 5.5 uses. Section 2 rests on it.
- `_build/lj-1.12-report.md:176-194`. Statement 2's statement, "for delta
  below alpha at a limit alpha".
- `_build/lj-1.16-review.md:65` and `:259`. The hull uses limit ordinals;
  the 5.5 shape `L_α ∪ {x} ⊆ M`, `|M| = |L_α|`.
- `_build/l3.32-t260-bridge.md:243-258`. The condensation limit case as
  the wing's obligation. Its cited `src/L/Condensation.lagda.md` lines no
  longer exist; the archive holds the chapter.
- `dev/LESSONS.md:1038` (D-1), `:2264-2320` (P-l), `:829-843` and `:2295`
  (R-38), `:1316` (D-10). The rules this block runs on.
- `dev/ledger.toml:243-246` and `:273-274`. The DD24 bar and the wing's
  seconds budget.
- **WHY NOT** `archive/dev/*`: the review already surveyed the archived
  task and decision records, and nothing in them bears on the
  `α`-restriction beyond the review's citations.

## 10. WHAT I AM NOT SURE OF

1. The body-caliber rate, 0.019, sits above the DD24 bar. A 30-line unit
   pays a fixed module floor. The bar assumes build-sized modules. I flag
   the number for the ledger.
2. The facts "cardinals are closed under `+ω`" and "`γ+ω < κ`" rest on
   ordinal cardinality arithmetic. The current tree has no cardinal
   machinery in its masters. `src/L/StageCardinal.lagda.md` is untracked.
   The consumer check is document-strength, not machine-checked.
3. The 5.5 choice of a `+ω`-closed `λ` is standard mathematics. The tree
   does not yet verify its existence mechanically.
4. The environment premise, stage `δ+3`, rests on the delivered EnvSet
   bound. `envSet` is opaque, so the probe does not re-derive the
   set-stage.
5. The probe defines `+ω` locally. The masters lack `+ω`. The wing needs
   the stage-arithmetic kit before the crossing build opens.
6. Devlin's 5.2 chain uses the witness inside `L_α` at every limit `α`.
   Cure A restricts the lemma's statement to `+ω`-closed `α`. I checked
   the wing's single application, not every 5.9-5.11 instance.
