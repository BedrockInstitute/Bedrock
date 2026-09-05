# LJ-1.91: gate the cardinal chapter, by pricing ONE cardinal

tier: codex (default)

## STATUS

COMPLETE. Recon and pricing only. No master was touched. No commit, no
push. The report is `_build/lj-1.91-report.md`.

## 0. THE VERDICT

**The cheapest route to one `IsCardinal` instance is the ambient Hartogs
number of `ω`: the set of order types of all well-orders on subsets of
`ω`. It is the least uncountable ordinal of the ambient universe. It is
provable from delivered machinery. It needs no choice and no new
principle. The widest unmeasured term is the order-type module, priced
at 300 to 500 lines of it.**

The consumer's statement is ambient, not internal. `S` in
`L.BoundedSubset` is the type of V-sets (`src/L/BoundedSubset.lagda.md:56`,
the unqualified `hPropStructure 𝒮ᵥ`; the L-sets are the separate
`module CS = hPropStructure 𝒮ʟ` at `:58`). `IsCardinal` quantifies over
V-sets and speaks of injections between their presentations
(`src/L/BoundedSubset.lagda.md:1045-1046`). So the construction must
name a V-set, and the ambient Hartogs is exactly that.

## 1. WHY THE INTERNAL HARTOGS IS NOT THE ROUTE

The L-model has replacement (`hasReplacementL`,
`src/L/Axioms/Full.lagda.md:277`) and internal recursion
(`src/L/Recursion.lagda.md:103-169`). An internal Hartogs inside L is
buildable. It gives `ω₁^L`, the least L-uncountable ordinal.

That set does NOT provably satisfy the ambient `IsCardinal`. For
`κ = ω₁^L`, the statement `IsCardinal κ` is equivalent to "`ω₁^L` is
uncountable in V", because every `δ ∈ κ` is L-countable and hence
V-countable. That sentence is independent of the metatheory: it holds
when V = L, and it fails after forcing `Coll(ω, ω₁^L)`. Both are
consistent with classical set theory, so neither is derivable.
**This negative is INFERRED**, a meta-mathematical argument, not a
machine-checked fact of the tree. It sets no verdict on its own; the
positive route in section 2 carries the report.

The route must therefore collect the order types of ALL V-well-orders on
subsets of `ω`, not only the constructible ones.

## 2. THE ROUTE, STEP BY STEP

The construction has five steps. Three ride delivered machinery. Two
are new content.

1. **The set `W` of well-orders on subsets of `ω`.** The power set
   `𝒫V (ω × ω)` is delivered (`src/V/Model.lagda.md:295-329`, under the
   impredicativity parameter). Full separation for every internal
   formula is delivered (`V⊨ZF-impredicative`,
   `src/V/Model.lagda.md:361-371`). The well-order formula and its
   adequacy lemmas are new content. This step is 60 to 120 lines.
2. **The order type of a well-order.** For each `R ∈ W`, the ordinal
   `ot R` with an order isomorphism `(field R, R) ≅ (ot R, ∈)`, plus
   uniqueness for isomorphic well-orders. This is the widest unmeasured
   term. It is 300 to 500 lines.
3. **The Hartogs set.** `κ = { ot R | R ∈ W }` is a V-set by `sett`
   over the small member type `⟪ W ⟫` (`src/V/Presentation.lagda.md:1-8`).
   The image of a small family is replacement for free
   (`src/V/Model.lagda.md:371`). This step is a few lines.
4. **Ordinality and the countability facts.** `κ` is transitive
   (a member of an order type is a smaller countable ordinal, hence
   itself an order type). `ω ∈ κ` via the natural well-order on `ω`.
   Every `δ ∈ κ` injects into `ω` through the isomorphism. This is 70
   to 150 lines.
5. **Initiality and the consumer supply.** If `κ ↪ δ` for `δ ∈ κ`, then
   `κ ↪ ω` by composition, which contradicts the defining uncountability
   of `κ`. `κ ∉ ω` follows. The same facts supply `ordκ`, `cardκ`,
   `κ∉ω` and `α ∈ κ` at the `[LJ-1.90]` site shape
   (`src/ProbeLJ190A.agda:204-211`). This is 60 to 120 lines.

No step needs a principle the tree lacks. Step 1 needs the delivered
power set and separation. Step 2 needs the delivered well-founded
recursion pattern. Step 3 needs `sett`. Step 5 needs injection
composition and `∈-irrefl`, both delivered.

## 3. THE PRICE

**One best-effort figure: 650 in-fence lines**, with the band 500 to
850. The basis is a delivered comparable for the core plus a survey for
the assembly:

| step | lines | basis |
|---|---:|---|
| 1. `W` and the well-order formula | 60-120 | delivered comparable, the archived CardinalPredicates at 399 in-fence (`archive/rud-route/src/L/CardinalPredicates.lagda.md`, module at `:34`), and the delivered separation idiom (`src/V/Model.lagda.md:361`) |
| 2. order types | 300-500 | delivered comparable, the collapse core measured at 319 lines and 1.31 s by `[LJ-1.47]` (`_build/lj-1.47-report.md` section 3), and the archived Pairing order-type section (`archive/rud-route/src/L/Ordinal/Pairing.lagda.md:436-575`, 376 in-fence) |
| 3. the Hartogs set | 5-15 | delivered, `sett` and `hasReplacement` (`src/V/Model.lagda.md:371`) |
| 4. ordinality and countability | 70-150 | survey |
| 5. initiality and supply | 60-120 | survey |

The in-fence counts of the archived modules re-verify at the ledger
caliber (non-blank lines inside ` ```agda ` fences): Cardinal 299,
CardinalPredicates 399, Pairing 376, SquareLaw 907. Load average at the
count: 7.75 / 4.82 / 4.51, four users, 1:00.

The seconds dimension is a rate expectation, not a measurement:
the order-type core is body-bound content at a parameterized carrier,
the class `[LJ-1.47]` measured at 0.0107 s per line, so roughly 6 to 8
seconds cold for the block. The well-order formula step is
satisfaction content at a concrete carrier, which runs hotter. Both are
**INFERRED**; the probe in section 4 is what would measure them.

## 4. THE WIDEST UNMEASURED TERM AND ITS PROBE

The widest unmeasured term is step 2, the order-type module: the
transfinite recursion that builds `ot R` from a well-order `R` on a
subset of `ω`, the ordinality proof, the order isomorphism, and the
uniqueness for isomorphic well-orders. It is 300 to 500 of the 650
lines, and its cost class is not measured at this carrier.

**The probe that would measure it is `src/ProbeLJ191A.agda`:** a fresh
instance of the delivered collapse pattern (`src/L/Ordinal/SquareLaw.lagda.md:373-437`,
the `colPick` recursion and the `col-*` lemmas) at the new carrier, a
well-order on a subset of `ω` as a module parameter. It checks the
recursion and the isomorphism at the C-12 cap, one process, cold, on a
quiet machine, and reports the seconds. This dispatch stops at naming
it, per the abort criterion: the route exists and is priced.

## 5. WHAT THE TREE ALREADY HAS

- The ambient universe is a ZF model: `V⊨ZF : LEM (ℓ-suc ℓ) → isZFModel`
  (`src/V/Model.lagda.md:415-416`). The record has full separation and
  replacement (`src/FOL/ZFModel.lagda.md:194-199`).
- The power set is delivered: `module Power` (`src/V/Model.lagda.md:280`),
  `𝒫V` and `power-spec` (`:295-329`).
- Ambient replacement for small families is `sett` itself; the chapter
  states it as "Replacement, for free" (`src/V/Model.lagda.md:109-122`,
  `hasReplacement` at `:371`).
- The small member type: `⟪ a ⟫` presents the V-set `a` at type level
  `ℓ` (`src/V/Presentation.lagda.md:1-8`).
- The Mostowski collapse for V-sets is delivered: `module Collapse`
  (`src/V/Collapse.lagda.md:40`), `πX` (`:75`), `mostowski` under
  transitivity (`:213-214`) and under extensionality (`:311-312`).
- The collapse-of-a-well-order pattern is delivered twice: the `col`
  machinery at `src/L/Ordinal/SquareLaw.lagda.md:373-437`, and the
  archived order type at `archive/rud-route/src/L/Ordinal/Pairing.lagda.md:436-575`.
- The ordinal supply is delivered: `boundingOrd`
  (`src/L/Ordinal.lagda.md:154-156`), `mem-ord`, `suc-ord`,
  `setUnion-ord`; ranks with `rank-fix`
  (`src/L/Rank.lagda.md:191-192`).
- The stage cardinality half is delivered: `stage-card-lower`
  (`src/L/StageCardinal.lagda.md:205`), `stage-card-upper` (`:508-571`),
  `OrdSWO` (`:226`).
- The square-law interface exists and has no instance: `Init`
  (`src/L/Ordinal/SquareLaw.lagda.md:692-700`) is a hypothesis module,
  never supplied.
- The consumer is fixed: `IsCardinal` at
  `src/L/BoundedSubset.lagda.md:1045-1046`, the telescope at
  `:1396-1402`, the concrete site at `src/ProbeLJ190A.agda:199-211`.

## 6. THE NEGATIVES AND THEIR STATUS

1. "No `IsCardinal` instance exists in the tree": **MEASURED**. The
   definition appears only at
   `src/L/BoundedSubset.lagda.md:1045-1046`, the hypothesis only at
   `:1397`. No other occurrence exists in `src/`.
2. "No initial ordinal beyond `ω` exists in the tree": **MEASURED by
   search**. No Hartogs, no aleph, no uncountable content appears in
   `src/`; `Init` has no instance
   (`src/L/Ordinal/SquareLaw.lagda.md:692-700`, applied only as a module
   parameter at `:938`); the earlier record agrees
   (`_build/l3.31-ivprobe-report.md:536`).
3. "The internal Hartogs supplies the ambient `IsCardinal`":
   **INFERRED FALSE**. The independence argument of section 1. The
   verdict of this dispatch does not rest on this negative.
4. "Cantor and Schroeder-Bernstein are absent from the tree":
   **MEASURED**. They are absent from `src/` but present in the archive:
   `csb` at `archive/rud-route/src/L/Cardinal.lagda.md:183`, `csb-eq`
   at `:277`, `cantor` at `:305`. This corrects the survey's claim.
5. "The order-type module is the widest unmeasured term":
   **INFERRED** from the delivered comparable; nothing measures it at
   this carrier. Section 4 names its probe.

## 7. THE SURVEY FIGURE, CHECKED

The earlier survey priced the missing cardinal chapter at about seven
hundred lines with no successor cardinal, no Cantor and no
Schroeder-Bernstein. Checked:

- The seven-hundred figure matches the recon's rows 4f (299 to 400) and
  4g (200 to 500), centered near 700 (`_build/lj-1.1-recon.md:147-149`).
- The "no Cantor, no Schroeder-Bernstein" half is wrong relative to the
  archive. The recon itself prices them as a delivered comparable
  (`_build/lj-1.1-recon.md:147`, `:243-245`).
- The genuinely missing row is the one the recon never priced: the
  existence of an initial ordinal above `ω`. That is this dispatch's
  Hartogs block, 500 to 850 lines on top of everything the recon
  listed.

## 8. CHOICE

The route needs no choice. It needs classical logic in the tree's
standing form: the ZF model record needs `LEM` through
`lem→impredicativity` (`src/V/Model.lagda.md:415-416`), and the whole
consumer chain is already parameterized by `lem`
(`src/L/BoundedSubset.lagda.md:10`). The `SetChoice` upgrade
(`V⊨ZFC`, `src/V/Model.lagda.md:528-529`) is not used.

## 9. DD4

The Hartogs block is template content. Its statements range over V-sets,
presentations, injections and well-orders. No Def-tower object appears
in any type, the same class as the square law
(`_build/lj-1.47-report.md` section 5). The J tower inherits the whole
block unchanged. The Devlin digest already classifies the cardinal
content of 5.5 as EITHER-tower
(`dev/literature/devlin-II5.md:382-387`). The J half is **INFERRED**:
no J tower exists in this tree.

## 10. ARCHIVE USED

- `_build/lj-1.90-report.md`, read WHOLE. TOOK the verdict that the
  supply stops at `cardκ` (section 1.1) and the concrete site shape
  (`κ = sucV ω`).
- `src/ProbeLJ190A.agda`, read WHOLE. TOOK the site's parameters
  (`:199-211`) and the generic `Site` module (`:74`).
- `_build/lj-1.1-recon.md`, read the cardinal rows (`:133-149`,
  `:213`, `:243-247`). TOOK the block figures and the archive
  comparables, and checked them (section 7).
- `_build/lj-1.47-report.md`, read WHOLE. TOOK the measured collapse
  core (319 lines, 1.31 s, section 3), the Init residual (section 2),
  and the DD4 shape (section 5).
- `src/L/StageCardinal.lagda.md`, read WHOLE. TOOK `stage-card-lower`
  (`:205`), `stage-card-upper` (`:508-571`), `OrdSWO` (`:226`).
- `src/L/Ordinal/SquareLaw.lagda.md`, read the `col` machinery
  (`:146-437`) and `Init` (`:692-700`).
- `src/L/Ordinal.lagda.md`, read WHOLE. TOOK `boundingOrd` (`:154-156`),
  `mem-ord`, `suc-ord`, `setUnion-ord`.
- `src/L/BoundedSubset.lagda.md`, read the scope
  (`:1040-1050`, `:1390-1402`) and the collapse sections (`:1040-1210`).
- `dev/LESSONS.md`, read P-l (`:2305`), C-35 (`:3200`), C-36 (`:3284`),
  D-30 (`:3332`), whole, and the `--for build` and `--for recon`
  bundles via `scripts/rules.py`.
- `archive/rud-route/src/L/Cardinal.lagda.md`, read WHOLE. TOOK `csb`
  (`:183`), `csb-eq` (`:277`), `cantor` (`:305`), 299 in-fence lines.
- `archive/rud-route/src/L/Ordinal/Pairing.lagda.md`, read the order
  type (`:436-575`), 376 in-fence lines, file ends at `:633`.
- `archive/rud-route/src/L/CardinalPredicates.lagda.md`, read the
  headers and the recon's row. 399 in-fence lines.
- `archive/rud-route/`, SHAPE only. TOOK nothing further.

## 11. LITERATURE USED

At 5.5 Devlin assumes `κ` is a cardinal with a successor `κ⁺`, and the
initial-ordinal fact `|γ| = |α| < κ` implies `γ < κ`
(`dev/literature/devlin-II5.md:145-166`). He proves none of it in II.5;
the cardinal arithmetic is Chapter I ZF content
(`dev2.txt:1369-1388`). The level-size arithmetic of 1.1(vii) is
sketched, not proved (`dev2.txt:200-215`, `devlin-II5.md:411-417`).

## 12. GATES

- `scripts/check-fences.py --check`: clean, 87 masters, run threshold 3.
- `scripts/lint-prose.py --check` on this report: exit 0.
- `scripts/lint-agda.py --check` on this report: exit 0.
- `scripts/ledger.py --brief`: standing 28,189 lines over 85 masters,
  measured from HEAD `cc516ea`.
- `git status`: clean. No commit, no push, no `make check`.
- Masters: none touched. DD23: no mathematical prose was written.
- Load average at the counts above: 7.75 / 4.82 / 4.51, four users,
  at 1:00. The `[LJ-1.47]` figures cited in section 3 were measured by
  that dispatch on a quiet machine at its own site.
- No Agda was run in this dispatch. No process was left alive.
