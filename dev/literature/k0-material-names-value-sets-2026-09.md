# K0 material names and internal value sets

Date: 2026-09-08. Repository source baseline: `34e56691`. Status: eight safe probes checked; K0 remains open. These probes extend the [earlier extraction results](k0-bounded-extraction-probes-2026-09.md). They use copied sources in temporary directories and do not modify production modules. The [Cohen roadmap](cohen-implementation-roadmap-2026-09.md) remains subordinate to the [master architecture](forcing-geology-design-2026-09.md).

## Checked results and exact assumptions

| Probe | Result | Premises and limits |
|---|---|---|
| GroundClosure | Actual empty, singleton, Kuratowski pair, weighted entry and two-entry codes, with membership specifications | Existing generic `isZFModel`; structural-equality reflexivity additionally needed for component membership. No arbitrary host-image closure |
| NameDescent | Well-founded subname relation; unary and two-coordinate recursion with propositional computation laws | Existing generic model's **external** regularity and structural-equality reflexivity. Does not derive external accessibility from ordinary first-order Foundation |
| MaterialNamePredicate | Hereditary material-name hProp, unfolding, subname closure, h-set subtype carrier and an actual empty name | Same strong ground profile and supplied Boolean carrier code B. This is a host predicate on ground codes, not yet a first-order recognizer |
| MaterialNameL | Instantiation of that name carrier and its two-entry constructor in actual L at `Type (ℓ-suc ℓ)` | Only `LEM (ℓ-suc ℓ)` and B as an L element; no extra ground-existence/equality/choice hypothesis |
| CoordinateDecoder | Unique coordinates from truncated pair representation; existing first-order pair formula adequacy; bridge to the generic name encoding | Actual L pairing is constructive; bridge to assembled ground model uses existing LEM. No assumed coordinate selector |
| FiniteNameClosure | Two valid names and two weights in B produce a valid two-entry name in the exact hereditary predicate | Generic model, coherent equality reflection/reflexivity and injective pair encoding; discharged in the L instance |
| FixedValueSet | Ground Separation constructs attained-value set; graph adequacy gives upper-bound equivalence and transfers a supplied internal LUB | Generic ground ZF, a fixed formula graph, and explicit representation/soundness evidence for an already-defined subformula value. No Collection or chosen name witnesses |
| FixedValueSetIdentity | Actual identity graph on members of arbitrary B; resulting set equals B, including its L instance | Generic coherent structural equality, discharged for L under its original LEM. B need not be finite or inhabited |

The generic constructions introduce no LEM, host Choice, DC, BPI, resizing or postulate. The L instantiations use the existing L theorem and its stated LEM. The coordinate decoder itself is constructive; only its bridge to the assembled ground model uses LEM. Importing a model record is not proof that its fields express only ordinary first-order satisfaction: these probes explicitly consume the stronger current profile where needed.

## 1. Material names and recursion

Use sets of Kuratowski pairs `entry(x,b) = {{x},{x,b}}`. Two entries with the same first coordinate and different Boolean weights are permitted; there is no requirement to choose a functional weight map. A functional presentation would need a separate normalization theorem.

The finite constructors now come from actual `isZFModel` operations. They are elements of the supplied ground by construction. This closes the earlier finite-constructor interface risk; it does not show that every externally supplied family of ground elements or weights is itself a ground set.

Define `Child x n = ∥ Σ b, entry(x,b) ∈ n ∥`. Every witnessed edge gives the membership chain:

```text
x ∈ {x} ∈ entry(x,b) ∈ n
```

`NameDescent` descends through three actual accessibility constructors. Truncated weights are eliminated only into `Acc Child x`, which is a proposition. The resulting recursion may return arbitrary data; the input accessibility is already proved. No rank arithmetic, representative selection or transitive-closure theorem is assumed. `PairRecursion` also checks a two-coordinate recursion interface whose recursive calls descend to children in both arguments. It implements this by induction on the first argument with a function over the second as its motive, and proves its computation law. This supports a proposed expanded equality definition: both conjuncts use values `eq(u,v)` with u a child of x and v a child of y, including in the second implication. Prove symmetry by first-coordinate induction, using the hypothesis for each child and all second arguments. After symmetry, recover the usual second Bell clause and define membership from equality. The separate mathematical review confirms this dependency order. The Boolean equations, symmetry proof and internally admitted joins/meets are not yet formalized; the checked result is the recursion interface. This strategy needs no lexicographic or multiset rank order.

`MaterialNamePredicate` defines `Shape n` to say each member is some `entry(x,b)` with b in B. Well-founded recursion defines `IsName n` as Shape plus hereditary validity of every child. It proves unfolding, shape and child elimination, and `isSet (Σ n, IsName n)` using the ground carrier's h-set property. The empty ground code satisfies this predicate. `MaterialNameL` checks the whole package on actual L and fixes the carrier universe at the existing successor level.

`FiniteNameClosure` now proves that the two-entry constructor preserves this exact hereditary predicate, given equality reflection and pair injectivity. `MaterialNameL` discharges both on actual L and exports an actual two-entry name constructor. The proof preserves truncated alternatives and weights; it does not pick arbitrary representatives.

`CoordinateDecoder` uses actual `prʟ-inj` to prove that `Σ x b, e ≡ prʟ x b` is a proposition. Mere representation therefore returns unique coordinates, without Choice. It also proves adequacy of the existing `prAtL` formula to this actual pair equality. The generic material ordered-pair code is connected to `prʟ` by a proved bridge, so the new carrier and existing coding library do not remain separate implementations. Only that bridge uses LEM through the assembled L model; direct L coordinate decoding and its formula adequacy are constructive.

Important remaining boundary: `IsName` is a host hProp, not a supplied or proved `Formula S 1`. Internally collected supports, check names and infinite internal families remain open. Coordinate decoding is now checked on L, but its general-ground adapter still needs the chosen pair-formula adequacy/injectivity contract. The current bare `ZFStructure` has no automatic equality laws; the generic probe keeps reflexivity explicit, while the L instance discharges it.

## 2. Quantifier values without selecting witnesses

For a supplied fixed two-variable graph formula, put:

```text
values = separate B (∃ graph)
b ∈ values  ↔  b ∈ B and merely some x satisfies graph(x,b)
```

This is actual use of the existing ground Separation operation, not a new closure field. The adequacy adapter consumes:

- an already-defined subformula evaluator `value : Name → S`, whose values belong to B;
- for each name, mere existence of a graph witness at its value;
- soundness: any graph witness yields mere existence of a name attaining that value.

The graph must enforce the name restriction itself or through a compiled guard. These premises are substantial fixed-formula internalization obligations, not automatically true for arbitrary host evaluators. Both directions preserve truncation; no function choosing a name for each value is constructed.

Given those premises, the internal value set has exactly the same upper bounds as all name values. A supplied supremum j in B transfers, with leastness tested **only against c in B**. The interface does not demand a supremum over the whole ground carrier or completeness for arbitrary external subsets. Internal Boolean completeness and the internal description of its order still need implementation.

The identity instance writes the actual formula `x ∈ B ∧ x ≈ b`, takes names to be members of B, proves the adequacy premises and proves `values = B` by extensionality. It works for arbitrary B, including empty/infinite cases, and checks the actual L adapter. It exercises the general Separation interface; it is not a Boolean forcing evaluator.

Design refinement: attained-value sets are the preferred first quantifier backend once subformula definability exists. Collection is still needed when a subsequent theorem needs a **set of name witnesses**, rank bounds, mixing or fullness. It is not necessary merely to form the attained subset of the already internal Boolean carrier. The earlier unique-value extraction remains applicable after existence/uniqueness is proved; it supplies neither graph definability nor internal completeness.

## 3. Noncircular implementation order and K0 gate

1. Generalize the checked L coordinate decoder/formula interface where needed; prove domains/supports are actual ground sets by actual Replacement on the coordinate formula. Retain the checked material carrier and unary recursion as the candidate representation.
2. Give a fixed first-order name recognizer and prove it agrees with the host hereditary predicate. A proposed recognizer uses a ground set of names closed under subnames and bounded finite reachability; existence/adequacy are not yet checked.
3. Build internally coded local atomic value tables on sets of relevant subnames/pairs. Prove existence, uniqueness, independence of local domains and agreement with external atomic recursion. An external recursive function plus an assumed internal-graph field is not this proof.
4. Induct on fixed formulas. Boolean operations consume their internal graphs. At an existential step, use the already-established subformula graph to construct the attained-value set, then internal completeness and the LUB formula to construct and describe the new value. Do not assume definability of the very quantifier being defined.
5. Derive ground Collection when witness sets are needed; only then use those sets for rank bounds/mixing/fullness and extension axiom transfer. Never use extension Replacement to justify its own ground construction.

The source audit found that `L.Recursion.Recursion` already requires `graph` and `funct`; `Definition` already requires graph adequacy. `L.Recursion.Graph` collects an already justified relation. These are useful consumers, not a generic theorem internalizing arbitrary host recursion. Relevant source: [L.Recursion](../../src/L/Recursion.lagda.md), [L.Recursion.Graph](../../src/L/Recursion/Graph.lagda.md), [pair formulas](../../src/L/Coding/PairFormulas.lagda.md), and [L coding model](../../src/L/Coding/Model.lagda.md). The existing pinned satisfaction recursion is an architectural example requiring substantive local coding, not a ready Boolean evaluator.

K0 is not complete. The new checks resolve finite ground construction, unary material descent, the host h-set carrier, and conditional internal attained-value construction. The next blocking representation decisions are internally collected supports and their generic adapter, internal name recognition and the local atomic-table interface. Full general forcing, Boolean completion, fullness and ultrafilter existence remain later implementation packages; do not expand K0 into proving every package in full.

## 4. Verification

The agent checked `GroundClosure` and `CoordinateDecoder` in `/tmp/bedrock-k0-probes/ground-closure`; the coordinator reviewed its source and checked it again as imported dependencies of `NameDescent` and `MaterialNameL` in the copied compile root. All other commands ran serially from `/tmp/bedrock-k0-probes/extraction/compile-root`:

```text
GHCRTS="-A64m -I0 -M8g" agda src/GroundClosure.agda
GHCRTS="-A64m -I0 -M8g" agda src/FixedValueSet.agda
GHCRTS="-A64m -I0 -M8g" agda src/FixedValueSetIdentity.agda
GHCRTS="-A64m -I0 -M8g" agda src/NameDescent.agda
GHCRTS="-A64m -I0 -M8g" agda src/MaterialNamePredicate.agda
GHCRTS="-A64m -I0 -M8g" agda src/CoordinateDecoder.agda
GHCRTS="-A64m -I0 -M8g" agda src/FiniteNameClosure.agda
GHCRTS="-A64m -I0 -M8g" agda src/MaterialNameL.agda
```

All eight final probe modules exited 0. The final `FixedValueSet` revision was checked through the identity module's import. Final coordinator logs have no warnings. An initial version of the finite L combination exhausted the fixed 8 GiB heap (exit 251). Adding explicit injectivity parameters and sealing its proof was insufficient (a near-limit retry was stopped, exit 130); sealing only the hereditary predicate was also insufficient (exit 251). The successful version seals the proved ground record `ground = L⊨ZF` and unfolds it locally only in the pair-injectivity bridge. It retains the sealed IsName definition with its proved unfolding law. No resource limit was increased, and no field or assumption was added. This makes the opacity boundary part of the K0 interface evidence: downstream modules should consume proved model operations without repeatedly normalizing the whole model proof. The error was:

```text
agda: Heap exhausted;
agda: Current maximum heap size is 8589934592 bytes (8192 MB).
```

The identity L adapter initially left an inference meta at `↾-reflects`; explicitly specifying the ambient structure and predicate fixed it. The coordinate adapter also corrected its ambient absoluteness instance and the qualified target of local `pairʟ` unfolding before successful checking. No unresolved goal or additional axiom remained. Existing copied dependency caches were reused. No whole-tree source check was needed for temporary-only code and Markdown changes.

A separate read-only mathematical audit reviewed the descent and hereditary predicate after compilation and agreed with these scope limits. Its temporary report is `/tmp/bedrock-k0-probes/name-recursion-audit/REPORT.md`. In particular, host hProp recognition is not internal first-order recognition, and the checked recursive interfaces do not supply the Boolean atomic equations or internal graph theorem.

## 5. Exact checked source snapshots

### GroundClosure.agda

SHA-256: `f81284aa3b9b30d9c3dbb65cfc172c152a67d3c733d52805d32c9ffa79488c83`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module GroundClosure {ℓ : Level} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFModel 𝒮 using ( isZFModel )
import FOL.ZFModel as Model
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module MaterialNames (zf : isZFModel) where
  open Model.isZFModel zf using ( hasEmpty; ∅; pair; pair-spec )

  emptyName : S
  emptyName = ∅

  singletonName : S → S
  singletonName x = pair x x

  orderedPairName : S → S → S
  orderedPairName x y = pair (singletonName x) (pair x y)

  weightedEntry : S → S → S
  weightedEntry x b = orderedPairName x b

  twoEntryWeightedName : S → S → S → S → S
  twoEntryWeightedName x b y c = pair (weightedEntry x b) (weightedEntry y c)

  emptyName-spec : (z : S) → (z ∈ˢ emptyName) ≡ ⊥
  emptyName-spec = hasEmpty .fst .snd

  singletonName-spec : (x z : S)
                     → (z ∈ˢ singletonName x) ≡ ((z ≈ˢ x) ⊔ (z ≈ˢ x))
  singletonName-spec x = pair-spec x x

  orderedPairName-spec : (x y z : S)
                       → (z ∈ˢ orderedPairName x y)
                       ≡ ((z ≈ˢ singletonName x) ⊔ (z ≈ˢ pair x y))
  orderedPairName-spec x y = pair-spec (singletonName x) (pair x y)

  weightedEntry-spec : (x b z : S)
                     → (z ∈ˢ weightedEntry x b)
                     ≡ ((z ≈ˢ singletonName x) ⊔ (z ≈ˢ pair x b))
  weightedEntry-spec = orderedPairName-spec

  twoEntryWeightedName-spec : (x b y c z : S)
                            → (z ∈ˢ twoEntryWeightedName x b y c)
                            ≡ ((z ≈ˢ weightedEntry x b)
                              ⊔ (z ≈ˢ weightedEntry y c))
  twoEntryWeightedName-spec x b y c =
    pair-spec (weightedEntry x b) (weightedEntry y c)

  module WithEqualityReflexivity
      (≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩) where

    singletonName-member : (x : S) → ⟨ x ∈ˢ singletonName x ⟩
    singletonName-member x =
      subst ⟨_⟩ (sym (singletonName-spec x x)) ∣ inl (≈ˢ-refl x) ∣₁

    orderedPairName-left : (x y : S)
                         → ⟨ singletonName x ∈ˢ orderedPairName x y ⟩
    orderedPairName-left x y =
      subst ⟨_⟩ (sym (orderedPairName-spec x y (singletonName x)))
        ∣ inl (≈ˢ-refl (singletonName x)) ∣₁

    orderedPairName-right : (x y : S)
                          → ⟨ pair x y ∈ˢ orderedPairName x y ⟩
    orderedPairName-right x y =
      subst ⟨_⟩ (sym (orderedPairName-spec x y (pair x y)))
        ∣ inr (≈ˢ-refl (pair x y)) ∣₁

    twoEntryWeightedName-left : (x b y c : S)
                              → ⟨ weightedEntry x b ∈ˢ twoEntryWeightedName x b y c ⟩
    twoEntryWeightedName-left x b y c =
      subst ⟨_⟩
        (sym (twoEntryWeightedName-spec x b y c (weightedEntry x b)))
        ∣ inl (≈ˢ-refl (weightedEntry x b)) ∣₁

    twoEntryWeightedName-right : (x b y c : S)
                               → ⟨ weightedEntry y c ∈ˢ twoEntryWeightedName x b y c ⟩
    twoEntryWeightedName-right x b y c =
      subst ⟨_⟩
        (sym (twoEntryWeightedName-spec x b y c (weightedEntry y c)))
        ∣ inr (≈ˢ-refl (weightedEntry y c)) ∣₁
```

### FixedValueSet.agda

SHA-256: `9f12cd65821490a23e0116b6efa1205d24869408adc729afa02be3a9862199ad`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module FixedValueSet {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open hPropStructure 𝒮
open import FOL.ZFModel 𝒮 using ( isZFModel )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open At S id using ( _⊨_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module Construction (ground : isZFModel) (B : S) (graph : Formula S 2) where

  open isZFModel ground using ( separate; separate-spec )

  values : S
  values = separate B (∃̇ graph)

  Graph : S → S → Type ℓ
  Graph x b = ⟨ (x ∷ b ∷ []) ⊨ graph ⟩

  into : ∀ b → ⟨ b ∈ˢ B ⟩ → ∥ Σ[ x ∈ S ] Graph x b ∥₁
       → ⟨ b ∈ˢ values ⟩
  into b inB occurs = subst (λ p → ⟨ p ⟩)
    (sym (separate-spec B (∃̇ graph) b)) (inB , occurs)

  out : ∀ b → ⟨ b ∈ˢ values ⟩
      → ⟨ b ∈ˢ B ⟩ × ∥ Σ[ x ∈ S ] Graph x b ∥₁
  out b = subst (λ p → ⟨ p ⟩) (separate-spec B (∃̇ graph) b)

  module Adequacy {ℓn} (Name : Type ℓn) (value : Name → S)
    (inB : ∀ n → ⟨ value n ∈ˢ B ⟩)
    (represented : ∀ n → ∥ Σ[ x ∈ S ] Graph x (value n) ∥₁)
    (sound : ∀ x b → Graph x b → ∥ Σ[ n ∈ Name ] value n ≡ b ∥₁)
    (order : S → S → hProp ℓ) where

    occurs : ∀ n → ⟨ value n ∈ˢ values ⟩
    occurs n = into (value n) (inB n) (represented n)

    UpperNames : S → Type (ℓ-max ℓn ℓ)
    UpperNames c = ∀ n → ⟨ order (value n) c ⟩

    UpperValues : S → Type ℓ
    UpperValues c = ∀ b → ⟨ b ∈ˢ values ⟩ → ⟨ order b c ⟩

    toNames : ∀ c → UpperValues c → UpperNames c
    toNames c upper n = upper (value n) (occurs n)

    toValues : ∀ c → UpperNames c → UpperValues c
    toValues c upper b member = PT.rec (snd (order b c))
      (λ { (x , g) → PT.rec (snd (order b c))
        (λ { (n , eq) → subst (λ z → ⟨ order z c ⟩) eq (upper n) })
        (sound x b g) })
      (snd (out b member))

    transferLUB : ∀ j → ⟨ j ∈ˢ B ⟩ → UpperValues j
      → (∀ c → ⟨ c ∈ˢ B ⟩ → UpperValues c → ⟨ order j c ⟩)
      → ⟨ j ∈ˢ B ⟩ × UpperNames j ×
        (∀ c → ⟨ c ∈ˢ B ⟩ → UpperNames c → ⟨ order j c ⟩)
    transferLUB j member upper least =
      member , toNames j upper , λ c inCarrier all → least c inCarrier (toValues c all)
```

### FixedValueSetIdentity.agda

SHA-256: `9f69ff8cc69fe28e456b1d437b8b327c971479a8cea3152fe7a84d85268c5a96`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module FixedValueSetIdentity where

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure; ↾-reflects; module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
import FixedValueSet
import FOL.ZFModel
open import L.Constructible using ( 𝒮ʟ; isL )
open import V.Hierarchy using ( 𝒮ᵥ )
import L.Model

module Generic {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ground : FOL.ZFModel.isZFModel 𝒮) where

  open hPropStructure 𝒮
  open FOL.ZFModel.isZFModel ground using ( extensional )

  module Identity
    (reflects : ∀ {x y} → ⟨ x ≈ˢ y ⟩ → x ≡ y)
    (reflexive : ∀ x → ⟨ x ≈ˢ x ⟩)
    (B : S) where

    graph : Formula S 2
    graph = (var zero ∈̇ con B) ∧̇ (var zero ≐ var (suc zero))

    module Values = FixedValueSet.Construction 𝒮 ground B graph

    Name : Type _
    Name = Σ[ x ∈ S ] ⟨ x ∈ˢ B ⟩

    represented : ∀ n → PT.∥ Σ[ x ∈ S ] Values.Graph x (fst n) ∥₁
    represented n = PT.∣ fst n , snd n , reflexive (fst n) ∣₁

    sound : ∀ x b → Values.Graph x b
      → PT.∥ Σ[ n ∈ Name ] fst n ≡ b ∥₁
    sound x b (member , equal) = PT.∣ (x , member) , reflects equal ∣₁

    module Adequate (order : S → S → hProp _) =
      Values.Adequacy Name fst snd represented sound order

    exact-set : Values.values ≡ B
    exact-set = extensional (λ b → ⇔toPath
      (λ member → fst (Values.out b member))
      (λ member → Values.into b member (represented (b , member))))

module InL {ℓ} (lem : LEM (ℓ-suc ℓ)) where
  module Ground = Generic (𝒮ʟ {ℓ}) (L.Model.L⊨ZF lem)
  module Identity (B : ZFStructure.S (𝒮ʟ {ℓ})) =
    Ground.Identity (λ p → ↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} p) (λ _ → refl) B
```

### NameDescent.agda

SHA-256: `badf864da460483931fd3ee56086493465694841b046de71f1379aa972d0dc1b`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module NameDescent {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open hPropStructure 𝒮
open import FOL.ZFModel 𝒮 using ( isZFModel )
open import GroundClosure 𝒮 using ( module MaterialNames )
open import Cubical.Induction.WellFounded using
  ( Acc; acc; WellFounded; isPropAcc; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module Descent (ground : isZFModel)
  (reflexive : ∀ x → ⟨ x ≈ˢ x ⟩) where

  open isZFModel ground using ( regularity )
  open MaterialNames ground using
    ( singletonName; weightedEntry; module WithEqualityReflexivity )
  open WithEqualityReflexivity reflexive using
    ( singletonName-member; orderedPairName-left )

  Child : S → S → Type ℓ
  Child x n = ∥ Σ[ b ∈ S ] ⟨ weightedEntry x b ∈ˢ n ⟩ ∥₁

  mutual
    descend : ∀ n → Acc _∈ᵗ_ n → Acc Child n
    descend n (acc below) = acc (λ x edge → PT.rec (isPropAcc x)
      (λ { (b , member) → throughEntry x b (below (weightedEntry x b) member) }) edge)

    throughEntry : ∀ x b → Acc _∈ᵗ_ (weightedEntry x b) → Acc Child x
    throughEntry x b (acc below) =
      throughSingleton x (below (singletonName x) (orderedPairName-left x b))

    throughSingleton : ∀ x → Acc _∈ᵗ_ (singletonName x) → Acc Child x
    throughSingleton x (acc below) = descend x (below x (singletonName-member x))

  child-well-founded : WellFounded Child
  child-well-founded n = descend n (regularity n)

  module Recursion {ℓp} (P : S → Type ℓp)
    (step : ∀ n → (∀ x → Child x n → P x) → P n) where

    result : ∀ n → P n
    result = WFI.induction child-well-founded step

    computation : ∀ n → result n ≡ step n (λ x _ → result x)
    computation = WFI.induction-compute child-well-founded step

  module PairRecursion {ℓp} (P : S → S → Type ℓp)
    (step : ∀ x y → (∀ u v → Child u x → Child v y → P u v) → P x y) where

    firstStep : ∀ x → (∀ u → Child u x → (∀ v → P u v)) → ∀ y → P x y
    firstStep x below y = step x y (λ u v left right → below u left v)

    module First = Recursion (λ x → ∀ y → P x y) firstStep

    result : ∀ x y → P x y
    result = First.result

    computation : ∀ x y → result x y ≡ step x y (λ u v _ _ → result u v)
    computation x y = cong (λ f → f y) (First.computation x)
```

### MaterialNamePredicate.agda

SHA-256: `63b0dbee8ae84f6baa288a11f63c6af8f2ad6cf2b2d831712cf9ce4d9df43f75`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module MaterialNamePredicate {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open hPropStructure 𝒮
open import FOL.ZFModel 𝒮 using ( isZFModel )
open import GroundClosure 𝒮 using ( module MaterialNames )
open import NameDescent 𝒮 using ( module Descent )
open import Cubical.Foundations.HLevels using ( isProp×; isSetΣ )
open import Cubical.Data.Empty using ( rec* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module Names (ground : isZFModel)
  (reflexive : ∀ x → ⟨ x ≈ˢ x ⟩) (B : S) where

  open MaterialNames ground using ( weightedEntry; emptyName; emptyName-spec )
  open Descent ground reflexive using ( Child; module Recursion )

  Entry : S → Type ℓ
  Entry e = Σ[ x ∈ S ] Σ[ b ∈ S ] (e ≡ weightedEntry x b) × ⟨ b ∈ˢ B ⟩

  Shape : S → hProp ℓ
  Shape n = (∀ e → ⟨ e ∈ˢ n ⟩ → ∥ Entry e ∥₁) ,
    isPropΠ (λ e → isPropΠ (λ _ → PT.squash₁))

  step : ∀ n → (∀ x → Child x n → hProp ℓ) → hProp ℓ
  step n below =
    (⟨ Shape n ⟩ × (∀ x (edge : Child x n) → ⟨ below x edge ⟩)) ,
    isProp× (snd (Shape n)) (isPropΠ (λ x → isPropΠ (λ edge → snd (below x edge))))

  module Definition = Recursion (λ _ → hProp ℓ) step

  opaque
    IsName : S → hProp ℓ
    IsName = Definition.result
  
    unfold : ∀ n → IsName n ≡ step n (λ x _ → IsName x)
    unfold = Definition.computation

  name-shape : ∀ n → ⟨ IsName n ⟩ → ⟨ Shape n ⟩
  name-shape n proof = fst (subst ⟨_⟩ (unfold n) proof)

  child-is-name : ∀ n → ⟨ IsName n ⟩ → ∀ x → Child x n → ⟨ IsName x ⟩
  child-is-name n proof = snd (subst ⟨_⟩ (unfold n) proof)

  Name : Type ℓ
  Name = Σ[ n ∈ S ] ⟨ IsName n ⟩

  name-is-set : isSet Name
  name-is-set = isSetΣ isSetS (λ n → isProp→isSet (snd (IsName n)))

  empty-is-name : ⟨ IsName emptyName ⟩
  empty-is-name = subst ⟨_⟩ (sym (unfold emptyName))
    ((λ e member → rec* (subst ⟨_⟩ (emptyName-spec e) member)) ,
     λ x edge → PT.rec (snd (IsName x))
       (λ { (b , member) → rec* (subst ⟨_⟩ (emptyName-spec (weightedEntry x b)) member) }) edge)

  empty : Name
  empty = emptyName , empty-is-name
```

### CoordinateDecoder.agda

SHA-256: `551ac9bb25c4f83feb645da092df63d2ca845fd747dd0ae13685323da1272f54`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module CoordinateDecoder {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; prʟ-inj )
import L.Axioms.Numerals as Numerals
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; isSetS )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

Representation : S → Type (ℓ-suc ℓ)
Representation e = Σ[ x ∈ S ] Σ[ b ∈ S ] e ≡ prʟ x b

representation-is-prop : (e : S) → isProp (Representation e)
representation-is-prop e (x , b , q) (x' , b' , q') =
  Σ≡Prop inner (prʟ-inj (sym q ∙ q') .fst)
  where
  inner : (x : S) → isProp (Σ[ b ∈ S ] e ≡ prʟ x b)
  inner x (b , q) (b' , q') =
    Σ≡Prop (λ b → isSetS e (prʟ x b))
      (prʟ-inj (sym q ∙ q') .snd)

decodeCoordinates : (e : S) → ∥ Representation e ∥₁ → Representation e
decodeCoordinates e = PT.rec (representation-is-prop e) (λ r → r)

entryFormula-adequate : (e x b : S)
  → ((e ∷ x ∷ b ∷ [])
       ⊨ prAtL zero (suc zero) (suc (suc zero)))
  ≡ ((e ≡ prʟ x b) , isSetS e (prʟ x b))
entryFormula-adequate e x b = ⇔toPath forward backward
  where
  adequate = prAtL-adequate zero (suc zero) (suc (suc zero))
    (e ∷ x ∷ b ∷ [])

  forward : ⟨ (e ∷ x ∷ b ∷ [])
                ⊨ prAtL zero (suc zero) (suc (suc zero)) ⟩
          → e ≡ prʟ x b
  forward h = Σ≡Prop (λ v → snd (isL v))
    (subst ⟨_⟩ adequate h ∙ sym (prʟ-fst x b))

  backward : e ≡ prʟ x b
           → ⟨ (e ∷ x ∷ b ∷ [])
                 ⊨ prAtL zero (suc zero) (suc (suc zero)) ⟩
  backward q = subst ⟨_⟩ (sym adequate)
    (cong fst q ∙ prʟ-fst x b)

module WithLEM (lem : LEM (ℓ-suc ℓ)) where
  open import L.Model {ℓ} lem using ( L⊨ZF )
  import FOL.ZFModel as Model
  import GroundClosure as GenericClosure

  module Closure = GenericClosure 𝒮ʟ
  module Names = Closure.MaterialNames L⊨ZF

  opaque
    unfolding Numerals.pairʟ
    pair-bridge : (a b : S)
                → Model.isZFModel.pair L⊨ZF a b ≡ Numerals.pairʟ a b
    pair-bridge a b = refl

  orderedPairName-bridge : (x b : S)
                         → Names.orderedPairName x b ≡ prʟ x b
  orderedPairName-bridge x b =
    pair-bridge
        (Model.isZFModel.pair L⊨ZF x x)
        (Model.isZFModel.pair L⊨ZF x b)
    ∙ cong₂ Numerals.pairʟ (pair-bridge x x) (pair-bridge x b)
```

### FiniteNameClosure.agda

SHA-256: `e919d09b0508f44b2fa0bc2019455beaa9f1d7b97b6f4aef80219dfb129aa03d`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module FiniteNameClosure {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open hPropStructure 𝒮
open import FOL.ZFModel 𝒮 using ( isZFModel )
open import GroundClosure 𝒮 using ( module MaterialNames )
open import MaterialNamePredicate 𝒮 using ( module Names )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT

module Closure (ground : isZFModel)
  (reflexive : ∀ x → ⟨ x ≈ˢ x ⟩)
  (reflects : ∀ {x y} → ⟨ x ≈ˢ y ⟩ → x ≡ y)
  (B : S) where

  open MaterialNames ground using
    ( weightedEntry; twoEntryWeightedName; twoEntryWeightedName-spec )
  open Names ground reflexive B using ( Name; IsName; Entry; Shape; unfold )

  module WithPairInjectivity
    (injective : ∀ {x b y c} → weightedEntry x b ≡ weightedEntry y c
      → (x ≡ y) × (b ≡ c)) where

    module Build (x y : Name) (b c : S) (b-in : ⟨ b ∈ˢ B ⟩) (c-in : ⟨ c ∈ˢ B ⟩) where

      code : S
      code = twoEntryWeightedName (fst x) b (fst y) c

      alternatives : ∀ e → ⟨ e ∈ˢ code ⟩ →
        PT.∥ (e ≡ weightedEntry (fst x) b) ⊎ (e ≡ weightedEntry (fst y) c) ∥₁
      alternatives e member = PT.map
        (λ { (inl p) → inl (reflects p); (inr p) → inr (reflects p) })
        (subst ⟨_⟩ (twoEntryWeightedName-spec (fst x) b (fst y) c e) member)

      shape : ⟨ Shape code ⟩
      shape e member = PT.map
        (λ { (inl p) → fst x , b , p , b-in; (inr p) → fst y , c , p , c-in })
        (alternatives e member)

      hereditary : ∀ z → PT.∥ Σ[ d ∈ S ] ⟨ weightedEntry z d ∈ˢ code ⟩ ∥₁
        → ⟨ IsName z ⟩
      hereditary z edge = PT.rec (snd (IsName z))
        (λ { (d , member) → PT.rec (snd (IsName z))
          (λ { (inl p) → subst (λ u → ⟨ IsName u ⟩) (sym (fst (injective p))) (snd x)
             ; (inr p) → subst (λ u → ⟨ IsName u ⟩) (sym (fst (injective p))) (snd y) })
          (alternatives (weightedEntry z d) member) }) edge

      valid : ⟨ IsName code ⟩
      valid = subst ⟨_⟩ (sym (unfold code)) (shape , hereditary)

      name : Name
      name = code , valid
```

### MaterialNameL.agda

SHA-256: `c08bfa5d8ab4757b3bc70c69230076ea6914fa6d407c18c1a21d009b35b0a9cb`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module MaterialNameL {ℓ} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; ↾-reflects; module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Model {ℓ} lem using ( L⊨ZF )
open import FOL.ZFModel 𝒮ʟ using ( isZFModel )

opaque
  ground : isZFModel
  ground = L⊨ZF

open import MaterialNamePredicate 𝒮ʟ using ( module Names )

open import L.Coding.Model {ℓ} using ( prʟ-inj )
open import CoordinateDecoder {ℓ} using ( module WithLEM )
open WithLEM lem using ( orderedPairName-bridge )
open import GroundClosure 𝒮ʟ using ( module MaterialNames )
open MaterialNames ground using ( weightedEntry )
open import FiniteNameClosure 𝒮ʟ using ( module Closure )
open hPropStructure 𝒮ʟ using ( _∈ˢ_ )

opaque
  unfolding ground
  weighted-injective : ∀ {x b y c} → weightedEntry x b ≡ weightedEntry y c
    → (x ≡ y) × (b ≡ c)
  weighted-injective {x} {b} {y} {c} eq =
    prʟ-inj {a = x} {b = b} {c = y} {d = c} (sym (orderedPairName-bridge x b) ∙ eq ∙ orderedPairName-bridge y c)

module At (B : ZFStructure.S 𝒮ʟ) where
  module Predicate = Names ground (λ _ → refl) B

  Name : Type (ℓ-suc ℓ)
  Name = Predicate.Name

  name-is-set : isSet Name
  name-is-set = Predicate.name-is-set

  empty : Name
  empty = Predicate.empty

  module Finite = Closure ground (λ _ → refl)
    (λ p → ↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} p) B
  module Constructors = Finite.WithPairInjectivity weighted-injective

  two : (x y : Name) (b c : ZFStructure.S 𝒮ʟ)
    → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ B ⟩ → Name
  two x y b c b-in c-in = Constructors.Build.name x y b c b-in c-in
```

