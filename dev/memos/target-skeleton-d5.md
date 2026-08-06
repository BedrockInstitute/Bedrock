# Target skeleton D5, and the rename ledger (archived from dev/PLAN.md section 4)

> **STATUS: SUPERSEDED.** The authorities for what `src/` contains today are `src/README.md` (the master symbol table) and `src/Everything.lagda.md` (the reading catalog), per ruling D5; the diagram here is the port-era record, not the live tree. Read it when a rename's history or the port-era part layout is needed. Moved out of dev/PLAN.md by [L3.32-T113] because it updates rarely. The live part-level rule is D5 in dev/PLAN.md section 3.

---

## 4. Target skeleton (D5)

Top-level parts mirror the book's parts. The part level (Base, FOL, ZF, V, L,
Landmarks) is fixed; **cluster-internal layout is provisional until the L3.10
re-layering review** (tension T2), and file splits inside a cluster are
finalized at port time under the STYLE-agda rules (L0.0).

**Reading this section today.** The diagram below is the ratified D5 skeleton
as designed for the port, and it is kept as that record. The tree has since
grown past it and is about to shrink back past it: `L/Rud/` (the rudimentary
function engine and its tower) is a whole cluster the diagram predates, and
under D18 the satisfaction-internalization cone, the choice tree, the Goedel
trees and the coded cluster retire. **For what the tree contains right now, the
authorities are `src/README.md` (the master symbol table) and
`src/Everything.lagda.md` (the reading catalog), not this diagram.** The rename
ledger below it stays append-only and remains accurate as history.

```
src/
├─ Everything.lagda.md       aggregator; import order = reading order; site landing page
├─ Landmarks.lagda.md        milestone theorems restated, with pointers into the text
├─ Base/                     Part 0: host-language groundwork
│   ├─ Prelude               cubical re-exports, global conventions
│   ├─ Truth                 truth values (hProp toolkit; see S1 in §10)
│   └─ Classical             LEM as a parameter interface and its consequences; no postulate
├─ FOL/                      Part 1: first-order logic as an object of study
│   ├─ Syntax                Formula (12 constructors, incl. Δ₀ bounded quantifiers)
│   ├─ Structure             ZFStructure: carrier, equality, membership; ↾, environments
│   ├─ Semantics             Tarski satisfaction by structural recursion (holds by refl)
│   ├─ LevyHierarchy         the Levy hierarchy as inductive witnesses
│   ├─ Absoluteness          transitive classes; Δ₀ absolute, Σ₁ up, Π₁ down
│   ├─ Manipulation/         syntax manipulation, zero trunk consumers, reads at the tail
│   │   (Relabelling: the constant-domain kit; Renaming; Relativize)
│   └─ Reification/          host predicate ↔ object formula, with adequacy certificates
│       (Base, Combinators, Certified; the rest deferred, see ledger)
├─ ZF.lagda.md               Part 2: what a ZF(C) model is: isZFModel / isZFCModel records
│                            (single chapter; Encoding deferred, Coding returns under ZF/ at L2)
├─ V/                        Part 3: the cumulative hierarchy realizes ZF(C)
│   ├─ Hierarchy             the HIT V and its ZF structure 𝒮ᵥ
│   ├─ Smallness             the resizing interface
│   ├─ Coding, Satisfaction
│   └─ Model                 V ⊨ ZF; with set choice, V ⊨ ZFC
└─ L/                        Part 4: the constructible universe (the capstone)
    ├─ Constructible         isL as an inductive predicate
    ├─ Model                 ★ root: L ⊨ ZFC (LEM-parameterized; the Frontier is deleted, §11)
    ├─ Ordinal/, Hierarchy/  ordinals, L-stages
    ├─ Definability/         the Def operator
    ├─ Recursion/            the internalization theorem for L-recursion (L.Recursion)
    ├─ Coding/               formula and sequence coding
    ├─ Axioms/               per-axiom chapters: Basic, Separation, Replacement, Infinity, Power
    ├─ Condensation/         condensation and the power-set bound
    ├─ WellOrder/            the global well-order <L
    └─ Choice/               the choice set in L
```

Rationale, briefly: `Base/` collects everything that is about the host rather
than the mathematics, so the remaining parts read as book parts. Reification
nests under `FOL/` because it is logic machinery, not a peer subject of V and
L. The source's `Models/HITV` becomes `V/` because in a textbook V is a
subject, not "a model instance". `Landmarks` is the trophy case and gives
stable statement anchors.

Rename ledger (append-only; extend as porting proceeds; a re-cut after L3 adds
new rows rather than editing old ones):

| Source (fol-reification) | Bedrock | Notes |
|---|---|---|
| `Prelude`, `Truth`, `Classical` | `Base.Prelude`, `Base.Truth`, `Base.Classical` | `Classical` loses its postulate (D2); `LEM` stated per level, dividends take it explicitly; `lem→smallΩ` returns `Lift Bool ≃ hProp ℓ` directly (the source's Σ-packaging happens at the V-side `smallΩ` field, `[L1.5]`) |
| `Classical.lem→VResizing` | lands in `V/` with `[L1.5]` | re-layered: the V-side redemption belongs to Part 3; `Base.Classical` keeps `lem→smallΩ` / `lem→resize` |
| `Prelude._^_` | `FOL.Structure`, with `[L1.2]` | just-in-time (STYLE-agda §2): environments are assignments into a carrier, and the parameterized `FOL.Semantics` module cannot host a generic definition |
| `Prelude.absurd` | dropped (owner ruling, 2026-07-17) | the library's `Empty.rec*` serves: `embed = mapFo Empty.rec*`, and `embed-⊨` names it in its statement |
| `ZF.Structure.Transitive` | lands with `[L1.3]` (owner ruling, 2026-07-17) | just-in-time: its first consumer is the absoluteness chapter; deferred out of `FOL.Structure` |
| `FOL.Syntax.Closed` | `ParamFree` (owner ruling, 2026-07-17) | "closed" collides with closed formula = sentence; the standard set-theoretic name is parameter-free (constants are how parameters enter); zh 无参 |
| `FOL.Syntax.Sentence` | dropped (owner question, 2026-07-17) | zero consumers in the entire source development; where closed-ness matters the index says it (`ParamFree 0`), and the concept stays as prose |
| `FOL.Syntax` / `FOL.Semantics` / `FOL.Rename` | `FOL.Syntax` / `FOL.Semantics` / `FOL.Renaming` | |
| `Reification.{Base, Combinators, Graded, Absoluteness, Relativize}` | `FOL.Reification.*` | `[L1.3]`; `Absoluteness` restructured: unparameterized top + `Transitive` + inner `module Single`; downstream instantiates `Absoluteness.Single` |
| `Reification.Absoluteness2` | deferred (zero code consumers) | its route was superseded by the source's RAW reflection breakthrough; revisit at `[L2.2]` only if the reflection engine wants it |
| `Reification.Graph` | deferred to `[L2.2]` | sole consumer is `L.ModelACSep`; on landing, its private renaming copy is replaced by `FOL.Renaming` |
| `Reification.Characterization` | deferred (zero consumers) | `charac→/←` unconsumed; `RepPred` and `toFormula` deferred with it |
| `Reification.Universe` | deferred (zero consumers) | the Code universe scaffolded a coding layer that was built via parameter-free formulas instead |
| `Reification.Ceiling` | dropped as code | zero consumers; the compactness-ceiling argument becomes prose in the `ZF.Model` chapter (`[L1.4]`), where it explains why strong axioms are model fields |
| `Reification.Tactic` | deferred (zero consumers) | the source's entire L development hand-builds its representations |
| `Reification.Base.{ClassOf, Definable}` | deferred | parameterized definable classes; land with the geology part |
| `ZF.Structure` | `FOL.Structure` | re-cut `[L1.2]`: the bare {∈,≐}-structure is model-theory material and must be read before `FOL.Semantics`, which consumes it as a module parameter; `ZF/` keeps the axioms (`Model`) |
| `ZF.Model` | same name | |
| `Models.HITV.{Smallness, ZF, Def, Coding, Sat, Instance}` | `V.{Smallness, Model, Definability, Coding, Satisfaction}` | `Instance` folds into `V.Model`; `V.Hierarchy` introduces the HIT |
| `Examples.HITV` | folds into `V.Hierarchy` | the structure instance is part of the chapter |
| `L.Constructible` (`isL'`) | `L.Constructible` (`isL`) | primes dropped (D7) |
| `L.ModelZFCFinal`, `L.ModelZFC`, `L.ModelAC*` | `L.Model` + `L.Axioms.*` | |
| `L.{Hierarchy*, Stage*, Lset*, Rank*, OrdLadder}` | `L.Hierarchy.*` | |
| `L.{Ordinal, OrdinalLinear}` | `L.Ordinal.*` | |
| `L.{Def*, DefEnv, Defstep, Delta0Local}` | `L.Definability.*` | |
| `L.{Sat*, Tarski*, Realize, Reflect*}` | `L.Satisfaction.*` | |
| `L.{Code*, Formula*, VarCoding, SeqChar}` | `L.Coding.*` | |
| `L.{FFST*, Canon*, SatSetInL, SeqSetInL}` | `L.Closure.*` | |
| `L.{Condensation, PowerBound, CondReduce}` | `L.Condensation.*`, feeding `L.Axioms.Power` | |
| `L.{ConstructibleOrder, WellOrder2}` | `L.WellOrder.*` | |
| `L.{Cmp*, Depth*, Order*, Trace*, Coh*}` | `L.Recursion` + per-function instances | D12, 2026-07-25; delivered as `L.Recursion` and its instances |
| `L.{ChoiceSetInL2, Choice*}` | `L.Choice.*` | |
| `ZF.Model.foundation` | `regularity` | `[L1.4]`: aligns with the glossary's canonical term for the axiom; one axiom, one name |
| `ZF.Model.{hasSep, hasRepl, sep, num0, numS}` | `hasSeparation`, `hasReplacement`, `separate`, `numeral-zero`, `numeral-suc` | `[L1.4]`: registered-abbreviation rule (STYLE-agda §3); `Sep`/`Repl`/`num` are unregistered |
| `ZF.Model.ℕ̄` | `isNumeral` | `[L1.4]`: no invented symbols (STYLE-agda §0); the bar had no tradition to lean on |
| `ZF.Model.contrFromExt` | `setOf-unique` | `[L1.4]`: theorem names are kebab phrases; `Contr`/`Ext` unregistered |
| `ZF.Model.iter` | deferred to `[L1.5]` | just-in-time: zero consumers in this chapter; first consumer is the V-side chain assembly (`numeral = iterate ∅ _⁺` with two `refl` equations); rename to `iterate` on landing |
| `ZF.Encoding` | deferred (zero consumers) | `Class`/`Encoding` are consumed by nothing outside `Everything` in the source; the class concept appears as prose in `ZF.Model`; revisit if a consumer lands |
| `ZF.Coding` | deferred to `[L2.x]` | all consumers are the L-side coding stack (`L.{VarCoding, SubBridge, SatCert*, Defstep, CodeOrder, OrderGraph}`) and `V.Coding` |
| `Models.HITV.ZF.{extensionalV, foundationV}` | `V.Hierarchy.{extensionalV, regularityV}` | `[L1.5]`: structural facts of the HIT itself, re-homed to the chapter that introduces it; `foundationV` renamed per the regularity row |
| `Models.HITV.ZF.sepΔ₀` | `V.Smallness.separateΔ₀` | `[L1.5]`: the smallness chapter's capstone; `sepFromSmall`→`separateFromSmall` (abbreviation rule) |
| `Models.HITV.Smallness.{small-⋀, small-⋁, InnerSmall}` | deferred to `[L2.x]` | sole consumer is the Def operator (`Models.HITV.Def`), itself deferred |
| `Models.HITV.{Def, Sat, Coding}` | deferred to `[L2.x]` | consumers are the L definability/coding stack; the `sucV` lemmas `∈sucV-elim` (from `L.Ordinal`) and `∈sucV-inl`/`self∈sucV` (from `Models.HITV.Coding`) are re-homed to `V.Model` for the numeral pinning |
| `Models.HITV.ZF.NumeralSpec` | inlined as `V.Model.numeralV≡#` | `[L1.5]`: the field-form `numeral` (L1.4 row) removed the parameterization's purpose; `iter` (deferred at L1.4) is dropped entirely, `numeralV` is direct recursion |
| `Models.HITV.Instance.{fullSep, replImage, con!}` | `separateFull`, `replaceImage`, `one` | `[L1.5]`: abbreviation rule; `con!` was local and stays local |
| `V.Model.SetChoice` | `Base.Choice.SetChoice` | `[L1.9]`: re-homed and level-indexed (LEM-style packaging) so Diaconescu can be applied at two levels; owner ruling 2026-07-18: reads in Part 0, right after `Base.Classical` (the boundary's second interface) |
| `FOL.Reification.{Graded, Absoluteness, Relativize}` | `FOL.{Graded, Absoluteness, Relativize}` | owner ruling 2026-07-18: certificate, absoluteness, and relativization theory is FOL material parallel to `Renaming`; only the representation framework keeps the `Reification` namespace |
| `FOL.Reification.Graded.Certified`, `FOL.Reification.Absoluteness.Single.{Inner, transfer}` | `FOL.Reification.Certified` | extracted so `FOL.Graded` and `FOL.Absoluteness` genuinely do not inherit the representation line (they no longer import it); the framework's graded tier, zero consumers, closes the catalog |
| `ZF.Model` | `ZF` | owner ruling 2026-07-18: a one-module namespace read abrupt; the chapter is the part; `ZF.Coding` will nest under it when it returns at `[L2.x]` |
| `V.Definability` | `L.Definability` | owner ruling 2026-07-18: the Def operator is the L-construction step, matching the fixed skeleton's `L/Definability`; reading position unchanged (head of Part 4) |
| `TruthAlg`, `hPropAlg` | `TruthAlgebra`, `hPropAlgebra` | owner ruling 2026-07-18: `Alg` reads as "algorithm" and was an unregistered abbreviation (STYLE-agda §3); D7 naming hygiene, repo-wide mechanical rename |
| `V.Model.{VResizing, lem→VResizing}` | `Base.Classical.{Resizing, lem→Resizing}` | owner ruling 2026-07-18: the record is pure universe-level policy, the `V` was consumer-naming; promoted to the assumption-interface pattern D2/STYLE §1 always anticipated for resizing, level-indexed like `LEM`, minted beside the dividends it bundles |
| `Base.Classical.{Resizing (record), lem→Resizing, lem→resize, lem→smallΩ}` | `Impredicativity`, `lem→impredicativity`, `lem→resizing : … → Resizing ℓ`, `lem→hPropSmallness : … → HPropSmallness ℓ` | owner ruling 2026-07-18: the two instruments get named types (`Resizing` = the function type, `HPropSmallness` = the Σ), the packing is renamed for what it is, impredicativity |
| `V.Model.{V⊨ZF, VZFC.V⊨ZFC, V⊨ZFC-fromChoice}` | `VModel.V⊨ZF-impredicative`, (deleted), `V⊨ZFC` | owner ruling 2026-07-18: headline names carry the classical reading (`V⊨ZF` from LEM, `V⊨ZFC` from choice alone via Diaconescu); the exact-price form wears its hypothesis as a suffix; the two-hypothesis ZFC form is retired |
| `ZF.{ZFModel, ZFCModel}` | `isZFModel`, `isZFCModel` | owner ruling 2026-07-18: the records are predicates on a structure, and the names now read as such (`isZFModel 𝒮` = "𝒮 is a ZF model"), matching the library's is-prefix convention |
| landmark hypotheses `∀ {ℓ'} → LEM ℓ'` / `∀ {ℓ'} → SetChoice ℓ'` | single instances `LEM (ℓ-suc ℓ)` / `SetChoice (ℓ-suc ℓ)` | owner ruling 2026-07-18: both interfaces transfer downward (`lowerLEM`, `lowerSetChoice`, by lifting), so one instance at the model's truth level suffices; `lem→impredicativity` tightened likewise, and `L.Model`'s telescope takes `LEM (ℓ-suc ℓ)` |
| `FOL.Syntax.{mapTm, mapFo, ParamFree, embed}`, `FOL.Semantics.{⟦⟧-map, ⊨-map, embed-⊨}`, `FOL.Graded.{mapΔ₀, mapΣₙ, mapΠₙ}` | `FOL.Relabelling` | owner ruling 2026-07-18: the constant-domain toolkit has zero trunk consumers and gathers into one tail chapter, three altitudes (syntax, meaning, certificates); zh rendering re-cut: relabelling = 常量改名 and renaming = 改名 (the pair named by its objects) |
| `FOL.{Relabelling, Renaming, Relativize}` | `FOL.Manipulation.{Relabelling, Renaming, Relativize}` | owner ruling 2026-07-18: the three syntax-manipulation chapters cluster under one sub-namespace, mirroring `FOL.Reification`; reading order unchanged (the tail's tools section) |
| `FOL.Graded` | `FOL.LevyHierarchy` | owner ruling 2026-07-18: the term graded certificates (分级证书) collided with the adequacy certificates, so the Levy data are **witnesses** (见证) and the word certificate is reserved for adequacy; the zh rendering keeps the surname in Latin, giving Levy 层级 (with 列维 in the avoid list) |
| `Classical.lem→VResizing` | `V.Model.lem→VResizing` | `[L1.5]`: as planned in the L1.1 row; consumes `Base.Classical.{lem→resize, lem→smallΩ}` |
| `Models.HITV.Smallness.{small-⋀, small-⋁, InnerSmall}` | un-deferred into `V.Smallness` | `[L1.6]`: their consumer `Def` un-deferred; supersedes the L1.5 deferral row |
| `Models.HITV.Def` | `V.Definability` | `[L1.6]`: un-deferred (first consumer is `L.Constructible`); `abs-defSet` + `module Abs` deferred to `[L2.x]` (condensation-side); `DemoEmpty` and `ι-fst` dropped |
| `L.Rank.{_∈ᵗ_, ∈-induction, ∈-induction-compute}` | `V.Hierarchy.{∈-induction, ∈-induction-compute}` | `[L1.6]`: regularity's dividend, re-homed to the chapter that proves regularity; `_∈ᵗ_` already lives in `FOL.Structure`; `rank` and the rest of `L.Rank` at `[L2.x]` |
| `L.Ordinal.{IsOrd, isPropIsOrd}` | `L.Constructible` | `[L1.6]`: just-in-time, the class `isL` needs only the predicate; the rest of `L.Ordinal` at `[L2.x]` |
| `L.Hierarchy.{isTransV, isPropIsTransV, ∅/𝒟/⋃/∪/setUnion-trans, isLayer, layer-trans}` | `L.Constructible` | `[L1.6]`: folded into the one chapter; member-form `isL`, `layer∈L`, `layer⊆L`, `L-trans`, `L-directed`, `Lₙ`/`Lω` deferred to `[L2.x]` |
| `L.Constructible.{isL', isL'-trans}` | `isL`, `isL-trans` | `[L1.6]`: primes dropped per D7 (the Lset-form predicate IS the book's `isL`); `Lset` gains an `opaque` seal (conversion-blowup countermeasure, measured: `L.Frontier` 5 min → 1 s); `Lset-mono`, `Lset⊆𝒟ₒ`, `𝒟ₒ-inv`, `𝒟ₒ-intro`, `Lset→isL'`, `isL'→isL` deferred to `[L2.x]` |
| `FOL.Manipulation.Relabelling.ParamFree` | dropped (owner ruling, 2026-07-19) | like `Sentence`, the concept keeps its prose name (parameter-free formulas and zh 无参公式) but no code name: the type `Formula (⊥* {ℓ}) n` says it whole, and the two use sites (`embed`, `embed-⊨`) spell it out |
| `module V.Hierarchy where` + per-def `∀ {ℓ}` | `module V.Hierarchy {ℓ : Level} where` | owner ruling 2026-07-19, after an implicit-level audit: every one of the 15 downstream `𝒮ᵥ {ℓ}` pins sat inside an already-`{ℓ}`-parameterized chapter, so the level moves to the module telescope, L-side style; consumers import applied (`open import V.Hierarchy {ℓ}`) and use `𝒮ᵥ`, `∈-induction`, `regularityV` bare; `Landmarks` alone imports unapplied and keeps its explicit pins |
| `hPropAlgebra : ∀ {ℓ} → …` | `hPropAlgebra : ∀ ℓ → …` | owner ruling 2026-07-19, same audit: the implicit was never once inferred (every code use pinned it with braces), so the level becomes an honest explicit argument; ~25 use sites now read `hPropAlgebra ℓ` / `hPropAlgebra (ℓ-suc ℓ)` |
| `FOL.Structure.pathStructure` | dropped (owner ruling, 2026-07-19) | consumption audit found exactly one consumer (`𝒮ᵥ`; `𝒮ʟ` goes through `↾`), so the convenience constructor dissolves: `V.Hierarchy` writes the four-field record literal in place, and the structure chapter's propositional-side promise now points at the hierarchy chapter |
| bare witness/见证 as a standalone noun | anchored compounds only (owner ruling, 2026-07-19) | 见证 read like a coined proper name but nothing in the code bears it; the licensed forms are anchored compounds only, the Δ₀ witness with its zh mirror Δ₀ 见证 and the Lévy 见证 and 小性见证 analogues; verbal and anaphoric uses stay; ~17 prose sites re-anchored, and the leftover graded/分级 wording in `V.Smallness` retired with them |
| `FOL.Structure._∈ᵗ_` (anonymous module, prefix-applied `_∈ᵗ_ 𝒮 y x`) | `module hPropStructure {ℓ} (𝒮 : …)` with `open ZFStructure 𝒮 public` + `_∈ᵗ_` | owner ruling 2026-07-19: call sites should read `y ∈ᵗ x` after opening the structure; the record itself cannot host `∈ᵗ` (it is generic over the truth algebra, `Ω` abstract, no `⟨_⟩`), so the propositional side gets a named opening module that re-exports the fields; consumers swap `open ZFStructure` for `open hPropStructure` (ZF, V.Hierarchy, L.Constructible, L.Model) and `Transitive` opens it in a `where` |
| prefix application of mixfix operators | banned, STYLE §6 rule (owner ruling, 2026-07-19) | the `_∈ᵗ_ 𝒮 y x` episode generalized: operators are opened and written infix, two coexisting instances get `renaming` marks; repo sweep found the last offenders in `FOL.Manipulation.Relabelling` (`At._⊨_ ι γ φ` and `At.⟦_⟧` in `⟦⟧-map`/`⊨-map`/`embed-⊨`), now inner modules over `(f , ι)` with `_⊨∘_`/`⟦_⟧∘` and `_⊨∅_`; review-enforced (regex cannot tell application from operator-as-value) |
| `⟨ M x ⟩` (class applied to a point) | `x ∈ᶜ M` (owner ruling, 2026-07-19) | the library's `Cubical.Foundations.Powerset._∈_` re-exported through the Prelude hub, renamed `_∈ᶜ_` so the plain `_∈_` (the HIT membership in `V.Hierarchy`/`L.Model`) never clashes; class sites swept (`↾` carrier, `Transitive`, `SM` twice, `InnerSmall`, `DefOf.e/ι`, `accL`, `isContrΣ-fromCenter`); plain-hProp projections `⟨ P ⟩` are untouched |
| `FOL.Structure` | `FOL.ZFStructure` (owner ruling, 2026-07-19) | the chapter defines `ZFStructure` and its retinue, and the file now says so; all 15 importers follow |
| `ZF` (top-level chapter) | `FOL.ZFModel` (owner ruling, 2026-07-19) | the model specification is first-order logic's business, so the chapter joins `FOL/` beside `ZFStructure`; reading order unchanged (Part 2 between Absoluteness and V.Hierarchy); `V.Model`, `L.Frontier`, `L.Model`, `Landmarks`, and the catalog follow |
| `FOL.Absoluteness.Transitive` | `FOL.ZFStructure.Transitive` (owner ruling, 2026-07-19) | transitive classes are structure-side vocabulary (the definition needs only `∈ᵗ`/`∈ᶜ`), minted beside the memberships; `L.Definability`, `L.Constructible`, and `Certified` import from the new home, and `Certified` keeps only `module Single` from Absoluteness |
| `FOL.Structure._^_` | `FOL.Semantics._^_` (owner ruling, 2026-07-19) | environments belong to evaluation; the definition now sits inside the parameterized semantics module, so consumers take `_^_` from their applied instance (`open SemV`, `open Sem`, the `using` list of an applied import) and `Single` re-exports it for `Transfer` |
| `V.Smallness.isSmall` + `Base.Classical.{Resizing, HPropSmallness, Impredicativity}` | `Base.Impredicativity` (new chapter, owner ruling 2026-07-19) | `isSmall` moves to Part 0 so `Resizing ℓ` reads as "every `P : hProp (ℓ-suc ℓ)` is small"; the owner does not want `V.Smallness` to depend on the classical chapter, so the size vocabulary gets its own chapter between Truth and Classical, interfaces only; Classical keeps `LEM`, `lowerLEM`, and the three `lem→` redemptions (`resizeDec` restated over `isSmall`) |
| identity lambdas (`ι x = x`, `λ m → m`, `λ (x : S) → x`) | `id`, minted in `Base.Prelude` (owner ruling, 2026-07-20) | cubical has only the explicit-argument `idfun`, so per owner instruction the hub defines the book's one home-grown function; the seven canonical-interpretation sites (`ZFModel`, `V.Smallness` twice, `V.Model`, `L.Frontier`, `Absoluteness.Single`, `Certified.Transfer`) now read `open At id`-style |
| `module At {ℓc} {K} (ι : K → S)` | `module At {ℓc} (K : Type ℓc) (ι : K → S)` (owner ruling, 2026-07-20) | the constant domain is the load-bearing datum of an interpretation and every open now names it (`open At S id`, `SemV.At SM fst`, `open At (⊥* {ℓe}) …`), retiring the `{K = …}` pins at `Renaming` and `Single` |
| `L.{Cmp*, Depth*}` + `FFST*` / `L.{Order*, Trace*, Canon*, Env*}` / `L.{Sat*, Tarski*, Coh*}` | `L.Recursion` instances / staged/partial variants as once planned | `[L3.0.3]`, 2026-07-25: refined the row above into three tiers; the tier boundaries dissolved with `L.Recursion`, and the staged and partial variants were abandoned (L3.12, L3.13) |
| `L.Ordinal.{∅-ord, suc-ord, setUnion-ord, boundingOrd}` | `L.Ordinal` (new chapter) | `[L2.0]`: un-deferred from the L1.6 row that kept only `IsOrd`. Consumption-pruned to what the closure axioms need; `mem-ord`, the numeral and ω lemmas, `A∉A` and `ord-antisym` stay deferred to `[L2.1]` and later. **`L.OrdinalLinear` is not ported and may never be**: its `ord-tri` was the source's route to pairing, and `boundingOrd` replaces it constructively |
| `L.Constructible.{Lset-mono, 𝒟ₒ-intro, Lset⊆𝒟ₒ, Lset→isL}` | same names, back in `L.Constructible` | `[L2.0]`: un-deferred from the L1.6 deferral row, which named them for exactly this moment; `𝒟ₒ-inv` and `isL'→isL` stay deferred |
| `L.ModelAC.{extensional', foundation', hasEmpty', hasPair', hasUnion', con!, mere→isContr, isL'-directed, 𝒟ₒ→isL', ∅ₗ}` | `L.Axioms.Basic.{extensionalL, regularityL, hasEmptyL, hasPairL, hasUnionL, uniqueL, mere→uniqueL, isL-directed, 𝒟ₒ→isL, ∅ʟ}` | `[L2.0]`: the source's basic-axiom block becomes the first axiom chapter. `extensionalL` and `regularityL` **move here from `L.Model`** (they were proven there at `[L1.7]`): the uniqueness of every existence field flows from extensionality, so the chapter that needs it must own it, and `L.Model` becomes a pure assembly chapter |
| `L.ModelACNum.{pairₗ, unionₗ, sucₗ, pairₗ-fst, unionₗ-fst, suc-proj, numₗ, num-fst}`, `L.ModelZFC.{num0L, numSL}` | `L.Axioms.Infinity.{pairʟ, unionʟ, sucʟ, pairʟ-fst, unionʟ-fst, sucʟ-fst, numeralL, numeralL-fst, numeralL-zero, numeralL-suc}` | `[L2.1]`: the numeral chain becomes the second axiom chapter. Suffix convention settled here: `ʟ` marks an **object** of L (`∅ʟ`, `pairʟ`, mirroring `𝒮ʟ`), `-L` marks the L-instance of a **named model field** (`numeralL`, `hasEmptyL`), which is why the two coexist. `L.ModelACNum.{NumeralSpecL', ℕ̄ₗ, ω-specₗ', hasInfinityₗ'}` and all of `L.ModelACInfinity` wait for the collection step |
| `L.Ordinal.{mem-ord, A∉A, numeral-ord, #∈ω, numeral-mem, ω-mem-ord, ω-ord}` | `L.Ordinal.{mem-ord, ∈-irrefl, numeral-ord, #∈ω, numeral-mem, ω-mem-ord, ω-ord}` | `[L2.1]`: un-deferred as the collection step reaches them. `A∉A` renamed `∈-irrefl` (a theorem name is a kebab phrase, not a formula); `ord-antisym` stays deferred (no consumer), and it is asymmetry rather than antisymmetry if it ever lands |
| `L.Rank.{rank, rank-compute, rank-ord, rank-fix}` | `L.Rank` (new chapter) | `[L2.1]`: `_∈ᵗ_`, `∈-induction` and `∈-induction-compute` already live in `FOL.ZFStructure` / `V.Hierarchy` from `[L1.6]`, so the chapter is just the rank theory; `rank-mono` deferred (no consumer yet) |
| `L.OrdinalLinear.{⊆ᵇ, ⊆ᵇ-prop, extByBig, ¬sub→wit, ord-tri}` | `L.Ordinal.Linear.{_⊆ᵇ_, ⊆ᵇ-prop, ext-⊆ᵇ, ¬⊆ᵇ→witness, ord-tri}` | `[L2.1]`: **the first Bedrock chapter to take a `lem` parameter**, packaged per the L1.9 ruling as a single instance `LEM (ℓ-suc ℓ)` rather than the source's postulate. `extByBig`/`¬sub→wit` renamed to kebab phrases naming what they do |
| `L.FormulaBound.{BoundedTm, BoundedFo, BoundedTm-mono, BoundedFo-mono}` | `FOL.Manipulation.Bounding` (new chapter) | `[L3.0.4]`: minimal prerequisite for the theorem statement. Re-homed from `L/` to `FOL.Manipulation`, where it belongs by subject: it is relabelling when the map is only partial, and the source module is already pure syntax with no `Lset`/`defSet`/V dependency. `Relabel` (`liftFo`, `liftFo-correct`, `Δ₀-liftFo`) stays deferred to `[L2.2]`, where its consumer lands |
| `L.ChoiceSetInL.metaφ⟹isL'` | `L.Axioms.Basic.defSet→isL` | `[L3.0.4]`: the probe's checklist item 4. The source buries the closure engine in the choice chapter though the whole closure tower uses it; in Bedrock it is two lines over `[L2.0]` (`𝒟ₒ→isL` after `𝒟ₒ-intro`) and sits with the axioms that first exhibit the pattern |
| `Models.HITV.Def.Refine.{abs-defSet, module Abs}` | `L.Definability.Refine.{abs-defSet, module Abs}` | `[L2.1]`: un-deferred from the `[L1.6]` row that parked it as condensation-side; its first consumer is the ordinal formula of the collection step. Landing it executes the reading-order re-cut `[L1.4]` promised for `[L2.x]`: `FOL.Manipulation.{Relabelling, Bounding}` move from the tail to the Part 4 doorstep, since `L.Definability` is now their first consumer. `Renaming` and `Relativize` stay at the tail, still unconsumed |
| `L.{OrdLset, RankLset, OrdLsetSuc, OrdinalFormula}` | `L.Ordinal.Stages` (one chapter) | `[L2.1]`: four source modules merge, since they are one theorem read two ways (`ord∈Lset→∈` and `ord∈Lset-suc`) plus its two comparison lemmas and the Δ₀ predicate. `sucβ∈or≡` → `suc∈or≡`, `φ_ord` → `φ-ord` (kebab, no underscore). The source's per-branch helper discipline is kept verbatim and narrated: the conclusions are heavy membership types and inlining them in a case split normalizes them per branch |
| `L.ModelACInfinity.{ω∈L', ωₗ'}`, `L.ModelACNum.{ℕ̄ₗ, ω-specₗ', hasInfinityₗ'}` | `L.Axioms.Infinity.{ω∈L, ωʟ, isNumeralL, ω-specL, hasInfinityL}` | `[L2.1]`: the collection step joins the chain chapter rather than getting its own, and the chapter gains the `lem` parameter for it. `ℕ̄` → `isNumeralL` per the `[L1.4]` ruling that retired the invented bar |
| `ZF.Coding` | `FOL.Coding` | `[L3.3]`: un-deferred as L3 phase B opens. Namespace by subject, `FOL/`: it codes the object language into a structure, and it is generic over that structure (an injective pairing and an injection of the naturals, as module parameters), so it belongs beside `FOL.ZFStructure` rather than under the model chapter. **`⌜⌝-inj` is dropped by consumption audit** (`[L3.1]`, S9). **A consumer demanded it, 2026-07-27** (`[L3.0.1]`'s satisfaction table), and it returns as `[L3.22]`, not as `[L3.9]` work: that pointer named the wrong goal, and `[L3.9]` is abandoned with "a future need returns as a new code" |
| `Models.HITV.Coding` | `V.Coding` | `[L3.3]`: un-deferred; discharges `FOL.Coding`'s two parameters (`#-inj` through monotonicity and irreflexivity, `pr-inj` through the classification specifications). Its `A∉A` is dropped, superseded by `V.Hierarchy.∈-irrefl` |
| `L.Ordinal.∈-irrefl` | `V.Hierarchy.∈-irrefl` | `[L3.3]`: re-homed one chapter earlier, to the chapter that proves regularity, following the `[L1.6]` precedent for `∈-induction`. `V.Coding` needs it and must read before `L/`, so the L-side home was an inversion waiting to happen |
| `L.ConstructibleOrder.{SWO, IsLeast, isPropLeastOf, leastOf, Tri}` | `L.WellOrder.Base` | `[L3.14]`: un-deferred at owner request, ahead of `[L2.2]` which is its first consumer. `Tri` is re-minted here as a general three-way datatype (the source imports it from `FormulaOrder`, which is instance data and stays deferred). **The `lem` parameter moves from the module to `leastOf` alone**: the bundle and the uniqueness of least elements are constructive, so charging the whole chapter classically would have overstated the price. `ΣSWO` and the pullback stay deferred to `[L2.4]`, where the order they build is defined |
| `L.SatCertBase.{ClosedΣ, FixedFormulaSetΣ, FFSΣterm, codeΣ-mem, sgl-char, pair-char, prChar-fwd, prChar-bwd, sglAt, sglConAt, pairAt, pairConAt, prAt, tagAt}` | `L.Coding.Base` with `FixedFormulaSetΣ` → `allCodes`, `FFSΣterm` → `allCodesTerm`, `codeΣ-mem` → `code∈allCodes` | `[L3.14]`: the Δ₀ readers, the substrate 68 source modules consume. Names lose the provenance flavour (`FixedFormulaSetΣ` was arity-Σ bookkeeping, not a concept). The source's own lesson is kept as narration: the auxiliary predicates `SglOf`/`PairOf` are written in the shape the readers' satisfaction unfolds to, which is what makes each adequacy lemma one line instead of a second proof |
| `L.SatCertEnv.{envF, envV, envF-spec, lookupF-spec, memPairAt, sucAt, envA, consF, seqSet}` | `L.Coding.Environment.{env, envOf, env-spec, lookup-spec, memPairAt, sucAt, envIn, cons, seqSet}` | `[L3.14]`: the environment layer. The `F`/`V`/`A` suffixes were argument-shape bookkeeping rather than concepts and are dropped; `lookup-spec` keeps its name because functionality of the graph is the chapter's point |
| `L.SatCertLen.{∈#-elim, #∈#-elim}` | `L.Ordinal` | `[L3.14]`: the members of a numeral are exactly the smaller numerals. Re-homed from the certificate base to the ordinal chapter, where the numerals are introduced and the companion `numeral-mem` already lives; the source keeps it with its consumer. `mkFin`/`toℕ-mkFin` are **not** ported, having no consumer until `lenAt` lands |
| `L.SatCertLen.{FixedFormulaSetT, codeT-mem, FFSTterm, pairInAt, tagPairAt}` | `L.Coding.Tagged.{taggedCodes, taggedCode-mem, taggedCodesTerm, pairInAt, tagPairAt}` | `[L3.14]`: the arity-tagged code set and the binary-constructor shape matcher. Split out of `SatCertLen` because it is self-contained; the length guard is the rest of that source module and lands separately. `L.Coding.Base`'s singleton and pair membership lemmas were made public here, since `tagPairAt`'s backward direction has to exhibit the Kuratowski intermediates |
| `L.SatCertLen.{lenAt, lenAt-intro, lenAt-len, mkFin, toℕ-mkFin}` | `L.Coding.Length` | `[L3.14]`: the length guard, the rest of `SatCertLen` after the tagged-code half. `mkFin`/`toℕ-mkFin` return here, having been dropped by the sweep one goal earlier when `∈#-elim` moved to `L.Ordinal` without them; they are private to this chapter, which is their only consumer |
| `L.SatCertCons.{shiftPairAt, consAt}` | `L.Coding.Environment` | `[L3.14]`: environment extension, re-homed to the environment chapter whose `sucAt` they consume. `consAt`'s adequacy is stated against the encoded environment, which is the form the certificates hold |
| `L.SatCertCons.tripleInT` | `L.Coding.Entry` | `[L3.14]`: the certificate-entry form. **The source module is split by subject**: `tripleInT` is about how a certificate records an entry, while `shiftPairAt` and `consAt` are environment extension and belong with `L.Coding.Environment`, whose `sucAt` they consume. The source keeps all three together because they were built in one session |
| `L.Stage` | same name | `[L2.2]`: the earliest-stage function. `isLeastSt`/`Least`/`leastBelow`/`theLeast` become `isEarliest`/`Earliest`/`earliestBelow`/`theEarliest`, since "least" was ambiguous against `L.WellOrder.Base`'s `IsLeast` for an arbitrary predicate; here the order is fixed and the content is "earliest stage". `lem` is a module parameter per D2, replacing the source's `Classical` import |
| `L.FormulaBound.Relabel` | `FOL.Manipulation.Bounding.Relabel` | `[L2.2]`: the deferral recorded at `[L3.0.4]` is discharged; the module joins the chapter that defines the certificate it consumes. The source's `V` parameter is renamed `W`, since `V` is the hierarchy everywhere else in Bedrock and the parameter is an arbitrary common codomain |
| `L.ModelAC.{ReplQ, module SepAt}` | `L.Axioms.Separation.{ReplImage, module AtStage}` | `[L2.2]`: the Δ₀ separation and replacement engine. `φLeg`/`φKey`/`defKey` become `satBridge`/`carveSat`/`carveSatAnd`, `sealedDefSet` becomes `carve`, `sepBuild`/`replBuild` become `separateAt`/`replaceAt`, and `⊨transp` becomes `⊨-transport`: the source's names record how the proof was assembled, the new ones what each step says. The `opaque` seal on the carved set is kept and narrated |
| `Reification.Tactic` | revisited by S6 (§10) | 2026-07-25: the "deferred (zero consumers)" row above stands for the port itself, but the macro is the second-largest measured lever (4k to 6k); if S6 is taken up, the deferral is reversed under the goal code that takes it |
