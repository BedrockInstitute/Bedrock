All evidence gathered. Here is the full consumption inventory.

# 1. The Def-tower surface

The constructible predicate lives in **`L.Constructible`**. Exact definition shape:

- `isL : S → Ω` ([Constructible.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Constructible.lagda.md:376)): `isL x = ⋁ S (λ α → ((IsOrd α , isPropIsOrd α) ⊓ (x ∈ˢ Lset α)))`. "Constructible" is literally **containment in some ordinal stage**, and the witness is the truncated Σ of `(α, ordinality, membership)`.
- The tower: `Lset : S → S` (:222) = `∈-induction LsetStep` (:223), `LsetStep α rec = ⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (rec …)))` (:215-216), `Lset-compute` (:227), step `𝒟ₒ : S → S` (:212-213) = `𝒟` (:53-54) = `DefOf.Def` ([Definability.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Definability.lagda.md:114)).
- `isLayer` (:175-181), 5 constructors; `layer-trans` (:183); `Lset-layer` (:246); the operator's membership recognition `𝒟ₒ-intro`/`𝒟ₒ-inv` (:301-308); the tower in/out characterizations `Lset-in`/`Lset-out` (:319, :336); `Lset-mono` (:355); `Lset⊆𝒟ₒ` (:310), `𝒟ₒ∋⊆` (:313); the class facts `isL-trans` (:379), `Lset→isL` (:395); and the structure `𝒮ʟ = 𝒮ᵥ ↾ isL` (:410-411).
- The definable-power step itself: `module DefOf (A : S)` ([Definability.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Definability.lagda.md:78)) with `ι` (:89), `smallSat` (:108), `defSet` (:111), `Def` (:114), `Def-spec` (:137), `defSet⊆A` (:141), `defSet-mem` (:150), `defSet⊤≡A` (:182), `A∈Def` (:195), `Def∋⊆A` (:198), `module Refine` (:222) with `A⊆Def` (:254) and `abs-defSet` (:287); `InnerSmall` opened public at :50 supplies `⊨ᵐ`/`⊨ᵐ-small`.

**Every export survivors consume, with definition line** (all in `L.Constructible` unless noted):

| Export | Def line | External consumers |
|---|---|---|
| `𝒮ʟ` | 410 | Model, Numerals, Infinity, Recursion, Hierarchy, Absoluteness, Basic, Separation, Full, Power, Transversal, Reflect, ReflectFo, Landmarks |
| `isL` | 376 | Stage, Reflect, ReflectFo, Recursion, Hierarchy, Absoluteness, Basic, Separation, Full, Power, Infinity, Transversal |
| `isL-trans` | 379 | Reflect, ReflectFo, Recursion, Hierarchy, Absoluteness, Basic, Separation, Full, Power, Transversal |
| `Lset→isL` | 395 | Reflect, Basic, Separation, Transversal |
| `IsOrd` | 141 | all of the above plus Ordinal, Linear, Stages, Rank, Rud/OrdArith, Rud/Order, Rud/Hierarchy |
| `isPropIsOrd` | 144 | Stage, Ordinal, Rud/OrdArith, Rud/Order |
| `Lset` | 222 | every survivor except Rank, Absoluteness, Model, Numerals |
| `Lset-mono` | 355 | Reflect, Recursion, Stages, Basic, Separation, Full, Power, Hierarchy |
| `Lset-in` | 319 | Reflect, Basic, Hierarchy |
| `Lset-out` | 336 | Reflect, Basic, Hierarchy |
| `Lset-compute` | 227 | Basic, Stages |
| `Lset-layer` | 246 | Basic, Separation, Full, ReflectFo, Stages |
| `layer-trans` | 183 | Basic, Separation, Full, ReflectFo, Stages |
| `𝒟ₒ` | 212 | Basic, Separation, Stages, Hierarchy |
| `𝒟ₒ-intro` | 301 | Basic, Separation, Stages |
| `𝒟ₒ-inv` | 306 | Stages |
| `Lset⊆𝒟ₒ` | 310 | Basic |
| `𝒟ₒ∋⊆` | 313 | Stages |
| `isTransV` | 83 | Ordinal, Stages, Rud/Hierarchy |
| `isPropIsTransV` | 86 | Ordinal |
| `∅-trans` | 89 | Ordinal, Rud/Hierarchy |
| `setUnion-trans` | 115 | Ordinal, Rud/Hierarchy |
| `module DefOf` | Def.78 | Basic, Separation, Stages, Rud/Realize, Rud/Describe, Rud/Switch |
| `defSet`, `defSet⊆A`, `defSet-mem`, `defSet⊤≡A`, `abs-defSet`, `Def∋⊆A`, `ι`, `⊨ᵐ` | Def.111/141/150/182/287/198/89/50 | Basic, Separation, Stages |

Consumed **only internally** (no survivor import): `𝒟`, `𝒟-trans`, `∪-trans`, `⋃-trans` (Rud/Hierarchy does import it), `isLayer` (and its 5 constructors), `LsetStep`, `𝒟ₒ-layer`, `stageFam`, `Def`, `Def-spec`, `A∈Def`, `smallSat`, `e`.

# 2. Per-chapter consumption table

Classification: **(G)** holds for any cumulative tower with the same surface (`Lset α = ⋃_{β∈α} J(Lset β)`, transitive J, ordinal predicate, `isL` = "in some ordinal stage"); **(D)** leans on the definable-power step itself (defSet/𝒟ₒ-intro/𝒟ₒ-inv, the `defSet→isL` shape, `Lset-suc` = definable powerset); **(R)** reflection-dependent (consumes `mkReflect`/arbitrary-formula separation, or is the L ⊨ ZF assembly). Use sites are code-block lines; import lines are listed first.

**Stage** (import :48). IsOrd@89,92,104,132,135-136,140,149; isPropIsOrd@105,140; Lset@176-177,188,192; isL@176,180,185,188,191. All G. The chapter is a generic least-ordinal descent; `isL` enters only as the property's witness shape.

**Reflect** (import :51-52). 𝒮ʟ@71; isL@73,130; isL-trans@73; IsOrd@103,108,122,168,188,193,256,271,444-445,452,458,461,465,474,488; Lset@103-110,114,123,127,129,165,312,325,334,365,382,465,491; Lset-mono@120,329,336; Lset-in@315; Lset-out@317; Lset→isL@105; 𝒟ₒ@314. All G, with one shape-sensitive spot: `witnessed` (:167-171) pattern-matches the isL Σ-witness (`q .snd`) as `α , IsOrd α × q ∈ Lset α`; if the rud isL keeps the same witness shape (or the bridge exposes it), no edit, otherwise this one declaration re-points. This chapter **is** the reflection machinery (its deliverable `reflect`/`Single` is what R-consumers use).

**ReflectFo** (import :50-56, plus Basic's `LsetS` :54). 𝒮ʟ@69,105; isL@71; isL-trans@71; IsOrd@104,138,153,208,223,234,238,284,288,293,307,525,532,534; Lset@348,351,356,438,464,474,529; Lset-layer@349; layer-trans@349. Tower use is G. D-indirect: `Cor` (:104-105) and `reflectRel`/`mkReflect` (:518-526) instantiate the relativization correctness at `LsetS β oβ`, whose certificate is D (carved by `defSet⊤≡A` in Basic). The chapter's deliverable `mkReflect` (:525) is the R endpoint for Full/Power.

**Ordinal** (import :44-45). isTransV@99,103,129,266; isPropIsTransV@104,130-131; ∅-trans@78; setUnion-trans@127; IsOrd@77,96,125,154,162,185,193,221,244,258,263; isPropIsOrd@259. All G.

**Ordinal/Linear** (import :43). IsOrd@136,140,144,146-147. All G.

**Ordinal/Stages** (import :52-58). G: IsOrd@109,131,137,164,190-196,216,265,341,350,378-379,434-439; isTransV@345,347; Lset-mono@159; Lset-layer@332; layer-trans@332; Lset-compute@204,417 (tower equation, G in shape once 𝒟ₒ is swapped to the rud step). D: DefOf@333; defSet@361-395; defSet⊆A@371; abs-defSet@376,387; 𝒟ₒ@200,218-222,415-432; 𝒟ₒ-inv@222; Def∋⊆A@222; 𝒟ₒ-intro@447; `defSet-φ-ord`@361 and `ord∈Lset-suc`@434-448 (carving "is an ordinal" as a definable subset of the stage; `rank-Lset`'s subset bound @221-222 uses `DefOf.Def∋⊆A`).

**Rank** (import :43). IsOrd@151-155,191-195. All G.

**Recursion** (import :51-55). 𝒮ʟ@63,65; isL@68; isL-trans@68; IsOrd@172; Lset-mono@175; Lset (via `LsetS`)@167,174. G surface; D-indirect via Basic's `LsetS`; the chapter's engine is `hasReplacementL` (Full), so R in substance.

**Hierarchy** (import :52-59). G tower: 𝒮ʟ@72,74; isL@77,168,270,303,569-578,615,650-656; isL-trans@77,182,203,211,551; IsOrd@166-179,190,220,273,286,300,333,381,409,542,563,599,678; Lset@118-121,174,185-217,223,229,270-296,333-350,384-395,526-566,585,591,618,644,678-681; Lset-in@187; Lset-out@208,229; 𝒟ₒ@168-174,188,213. D: `isL-𝒟ₒ` (Basic) @170 discharges PowOK ("definable powerset of a stage is constructible"); `LsetS` @177,212,395,560,566,585; the whole object-language graph (Coding.Sequence's `StepAt`/`PowOK`/`LsetGraphAt`) describes the definable-powerset step. R: `hasReplacementL` (@632).

**Absoluteness** (import :47). 𝒮ʟ@53; isL@59,88; isL-trans@59. All G (Δ₀ transfer into L).

**Model** (import :49, :57). 𝒮ʟ@59,61. G surface; `L⊨ZF`/`L⊨ZFC` (:83-99) are R in substance (twelve fields + choice). Cross-link: `L.Choice.Transversal` @57.

**Axioms/Basic** (import :49-54). G: `isL-directed`@385-400 (Lset@386-395, IsOrd@390-392, Lset-mono@394-395), `extensionalL`@431-439 (isL, isL-trans), `regularityL`@445, `uniqueL`/`mere→uniqueL`@449-452, `hasEmptyL`@511, `hasPairL`@639, `hasUnionL`@727. D: essentially everything else, the `defSet→isL` chain: `𝒟ₒ→isL`@98-127 (𝒟ₒ, Lset, Lset-compute@113, Lset→isL, IsOrd), `defSet→isL`@130-133 (𝒟ₒ-intro@133, DefOf.defSet@131), `isL-Lset`@156-158 (DefOf.defSet⊤≡A@158), `LsetS`@160-161, `Lset-suc`@196-215 (𝒟ₒ, Lset⊆𝒟ₒ@204, Lset-in@204, Lset-out@210, Lset-compute@204), `isL-𝒟ₒ`@230-235, `𝒟ₒS`@234, `FinOf`@296-359 (DefOf@297, defSet@328-346, defSet-mem@339,347, 𝒟ₒ-intro@354, finSet∈𝒟ₒ@352-354, finSetL@356-359), `∅∈𝒟ₒ`@490-491, `∅∈L`@504-505, `pair∈𝒟ₒ`@547-549 (defSet, defSet-mem@573,585), `pair∈Lset-suc`/`sgl∈Lset-suc`/`pr∈Lset-suc`@592-607, `PairOf`@621-639, `UnionOf`@661-725 (DefOf@664, layer-trans/Lset-layer@665, defSet-mem@687,699, 𝒟ₒ-intro@714, 𝒟ₒ→isL@717).

**Axioms/Separation** (import :54-59). G: `⊨-transport`/`⊨-transport₂`@232-260 (absoluteness), `Below′`/`liftTmTo`/`liftFoTo`@416-432 (Lset-mono@423,429), `mkBoundedTm`/`mkBoundedFo`@434-512, `separateΔ₀`@520-527, `replaceΔ₀`@561-602 (isL-trans@561, stage machinery, Lset-mono@571,586,592). D: the carving engine `AtStage`@119-230 (DefOf@120, defSet@165-176, abs-defSet@168,176, 𝒟ₒ-intro@199, defSet⊆A@203), `memberIsL`@277-278 (Lset→isL), `separateAt`@284-330, `replaceAt`@332-350 (𝒟ₒ→isL@294,363).

**Axioms/Full** (import :48-55). G: `transIn`@101-102 (layer-trans, Lset-layer, Lset), `Images`@215-240 (isL-trans@215, stage, Lset-mono@233), Lset-mono@157,295,300. R: `hasSeparationL`@133-166 and `hasReplacementL`@292-334 (both: `mkReflect`, `LsetS`, plus `separateΔ₀`/`replaceΔ₀` and stage function).

**Axioms/Power** (import :55-58). G: `rsz`/`unres`@136-143 (isL), `Bound`@154-171 (IsOrd, Lset, Lset-mono@160, isL-trans@163). R: `hasPowerL`@192-194 (`hasSeparationL`, `LsetS`).

**Axioms/Infinity** (import :22-24). 𝒮ʟ@36,38; `ω∈L`@66-68 (isL; proof via `ord∈Lset-suc`, which is D in Stages). Surface G, proof D-indirect.

**Axioms/Numerals** (import :39-41). 𝒮ʟ@54,56; `isL-directed` (Basic)@41, used in `pairʟ-fst`@127-136. Surface G, re-point only if Basic internals change.

**Choice/Transversal** (import :59-60, :74-79). G surface: 𝒮ʟ@75,77; isL@80,342; isL-trans@80; IsOrd@188; Lset@191,197-200,204,207,210,214,243,261,264,281,285-288,297; Lset→isL@198-199. D/R indirect: `LsetS`@281; `bound-below₂`@207,211 (Choice/Stage, built on the old tower); `Bound`/`orderL`/`orderL-rep`/`orderL-fill`@188-199,243-268 (Choice/Order); `appAt`/`appAt-adequate`@220,243-268 (Coding.Model); the model's arbitrary-formula `separate`@281 (R).

**Landmarks** (import :27). 𝒮ʟ@76. R restatement of `L⊨ZFC` (:76-77).

**Rud trunk (found by grep; outside the enumerated read scope, flagging because it is the incoming R5 machinery)**: `Rud/Hierarchy` imports `isTransV; ∅-trans; ⋃-trans; setUnion-trans; IsOrd` (:46-47, 19 declarations); `Rud/Order` `IsOrd; isPropIsOrd` (:67, 29); `Rud/OrdArith` `IsOrd; isPropIsOrd` (:34, 12) all G; `Rud/Realize` (:31), `Rud/Describe` (:50), `Rud/Switch` (:43) import `module DefOf` (D, 2/62/15 declarations). These are the new-tower chapters that currently lean on the old tower's transitivity/ordinal lemmas.

# 3. Retirement cross-links (surviving chapters importing L/Godel, L/Coding, L/Choice)

- [Model.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Model.lagda.md:57): `open import L.Choice.Transversal {ℓ} lem using ( hasChoiceL )`
- [Hierarchy.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Hierarchy.lagda.md:57): `open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; domAt-intro )` and :59 `open import L.Coding.Sequence {ℓ} lem using ( StepAt; StepOf; PowOK; StepAt-in; StepAt-out; StepAt-back; ApproxAt; ApproxAt-dom; ApproxAt-value; ApproxAt-step; ApproxAt-in; LsetGraphAt; LsetGraph-in; LsetGraph-out; GraphOf )`
- [Transversal.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Transversal.lagda.md:78): `open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )` (Transversal itself retires, but Model@57 depends on it, so this must be re-pointed on the way out)
- [Rud/Describe.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Describe.lagda.md:58): `open import L.Coding.Base {ℓ}`
- [Rud/LevelDesc.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/LevelDesc.lagda.md:52): `open import L.Coding.Base {ℓ} using ( prChar-fwd; prChar-bwd )`
- Catalog: [Everything.lagda.md](/Users/alsg/Agentic/Bedrock/src/Everything.lagda.md:318) :318-319, :328-330, :332-360 (Coding + the whole Godel block), :364-375 (Choice block).
- No surviving chapter imports `L.Godel` directly (only the catalog, :332-345). `L.Ordinal` imports `V.Coding` (:43, `#-inj′`), which is Part 3, not retiring.

# 4. Transversal

- Where: [src/L/Choice/Transversal.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Transversal.lagda.md:1), module `L.Choice.Transversal` (:44).
- Re-exports: `ChoiceStatement : isZFModel → Type` (:337) and `hasChoiceL : (zf : isZFModel) → ChoiceStatement zf` (:342-347). Internally: `Pick` (:113), `Trans` (:176) with `transversalSet` (:281) and `transversal` (:335).
- Its imports: L.Constructible (:74), L.Axioms.Basic `LsetS` (:75), L.Choice.Stage `bound-below₂` (:76), L.Choice.Step `Mem; relOf` (:77), L.Choice.Order `module Bound` (:77), L.Coding.Model `appAt; appAt-adequate` (:78), L.WellOrder.Base (:79), V.Coding `pr` (:73).
- Re-pointing, concretely: (1) Model:57 re-points `hasChoiceL` to wherever the choice theorem is re-homed. (2) If Transversal is rescued, its own imports re-point: `bound-below₂` (the family/member bounding lemma, which is old-tower-built) to the surviving stage-bounding surface; `Mem`/`relOf`/`Bound` (the per-stage well-order bundle, Coding-built) to wherever the rud-order machinery lands; `appAt`/`appAt-adequate` (the slot-application reader used in `Pick` at :220, :243-268) to the surviving description machinery. (3) `LsetS` and the model's own `separate` (:281) survive (Basic and Full persist), so the two remaining anchors are the well-order bundle and the application atom. In total: 1 import line in Model, 3-4 import lines and the `Pick` atom block in Transversal.

# 5. Counts

Rule: named declarations in code blocks (top-level and private/`where` helpers; module headers, `open`/`import` lines excluded) whose signature or proof text references the Def-hierarchy surface, counted once each. Under the bridge: G-only declarations need no proof edits (re-point imports only); D declarations need real proof edits; R declarations are untouched by the swap itself (they consume the rebuilt reflection layer). Per chapter:

| Chapter | Ref. decls | G (re-point only) | D (proof edits) | R (indirect) |
|---|---|---|---|---|
| L.Constructible (swap target) | 43 | ~13 transitivity/ordinal decls kept | ~30 tower decls replaced | - |
| L.Definability (DefOf) | 18 (self-refs) | 0 touched, survives | - | - |
| L.Stage | 13 | 13 | 0 | 0 |
| L.Reflect | 26 | 26 (1 witness-shape spot, :167-171) | 0 | 0 (is the machinery) |
| L.ReflectFo | 23 | 22 | ~1 (Cor/LsetS cert, :104-105) | deliverable `mkReflect` |
| L.Ordinal | 15 | 15 | 0 | 0 |
| L.Ordinal.Linear | 4 | 4 | 0 | 0 |
| L.Ordinal.Stages | 34 | ~16 | ~18 | 0 |
| L.Rank | 4 | 4 | 0 | 0 |
| L.Recursion | 3 | 2 | 0 | 1 (wraps hasReplacementL) |
| L.Hierarchy | 53 | ~44 | ~8 | 1 |
| L.Absoluteness | 1 | 1 | 0 | 0 |
| L.Model | 0 text; 2 theorems | 0 | 0 | 2 (`L⊨ZF`/`L⊨ZFC`) + 1 import re-point (:57) |
| Axioms.Basic | 63 | ~7 | ~56 | 0 |
| Axioms.Separation | 52 | ~14 | ~38 | 0 |
| Axioms.Full | 12 | ~5 | 0 | ~7 |
| Axioms.Power | 8 | ~5 | 0 | ~3 |
| Axioms.Infinity | 1-3 | 1-2 | 0 (proof goes through Stages) | 0 |
| Axioms.Numerals | 1 | 1 | 0 | 0 |
| Choice.Transversal | 16 | ~10 | ~4 (LsetS, bound-below₂, Bound, appAt) | ~2 (separate, hasChoiceL) |
| Landmarks | 1 | 0 | 0 | 1 |

Totals across the enumerated survivors: ~330 declarations reference the surface; the "must edit proofs" bucket is roughly 115-125, concentrated in **Axioms/Basic (~56)**, **Axioms/Separation (~38)**, **Ordinal/Stages (~18)**, plus **Constructible itself (~30 tower statements)** which is where the bridge is built. Everything else is re-pointing: roughly 20 import lines across the survivors, plus the ~11 import lines in section 3 that unblock the Godel/Coding/Choice retirement. The Rud trunk (out-of-scope, grep-only) adds 143 referencing declarations, of which the 3 `DefOf` imports (Realize:31, Describe:50, Switch:43) and 2 Coding.Base imports (Describe:58, LevelDesc:52) are the ones that would force edits there.