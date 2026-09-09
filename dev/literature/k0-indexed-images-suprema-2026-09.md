# K0 indexed weighted images and relative supremum syntax

Date: 2026-09-09. Repository source baseline: `0177f9b3`. Status: four safe temporary probes checked. This follows the [real-name-pair and image probes](k0-name-pair-weighted-images-2026-09.md). The uniform inner-image syntax and predecessor-agreement adapter are now checked in both key orientations. A variable-indexed relative-supremum formula is also checked. K0 remains open; no actual Boolean operation/completeness instance or complete atomic Step has been proved.

## From predecessor values to graph membership

`PredecessorValueAgreement` is a universe-polymorphic relational lemma. Given two graphs with proposition-valued membership, merely inhabited fibers at every relevant predecessor, and equality of all cross-graph values there, it proves both directions of graph membership at any fixed value. It requires neither a set-level Value carrier nor LEM or Choice.

For example, to transfer G(q,b) to H(q,b), coverage gives merely an H-value c. Eliminate that existence into the proposition H(q,b); the supplied value agreement identifies b and c, and transports the graph witness. This never extracts a simultaneous family of predecessor values. It does not turn arbitrary mere existence into data.

`WeightedPredecessorAgreement` instantiates the lemma with actual L pair keys and values in the internal B. Its coverage and cross-value agreement types match the earlier recursion step's predecessor obligations. Proof irrelevance for B-membership lifts raw value equality to equality in the value subtype. The module produces graph agreement for both equality-clause images:

- Left image: fix u, range over pair(v,c) ∈ y, read H(u,v).
- Right image: fix v, range over pair(u,a) ∈ x, still read H(u,v).

The pair dependency witnesses are supplied by the checked `pair-edge` theorem. The same graph-transfer proof handles both directions; no symmetry of Boolean equality is assumed. The `LeftImage` composition feeds the proved graph agreement to the earlier actual weighted-set congruence theorem, obtaining equality of the two internally constructed left images. Thus that particular graph-agreement premise is now derived from coverage and predecessor-value agreement, rather than left as a new unexplained interface field.

## One variable-indexed image template

`IndexedWeightedImage` supplies `WithKey.WithOperation.imageAt C B parent H f z`. Every one of these six arguments is a variable index. Its reading theorem holds for arbitrary environments and includes all parameter shifts through the quantifiers.

The key constructor and operation each have syntax with a proved reading theorem. The image predicate reads:

    exists v ∈ C, c ∈ B, d ∈ B:
      pair(v,c) ∈ parent and pair(Key(f,v),d) ∈ H and Op(c,d,z).

The output guard z ∈ B is intentionally outside this predicate. It belongs to the surrounding Separation/image-set description; the witness predicate alone does not assert it. The operation remains an arbitrary relation with syntax and adequacy, not a Boolean meet operation already proved total.

There is one intermediate unbounded object-language existential for the encoded key. This is legal first-order syntax and does not collect a host family or need a separate key-image set. Unrestricted ground Separation can use such syntax. This template makes no Delta-zero complexity claim. If a later weak-theory or absoluteness argument needs bounded syntax, the concrete pair-key adapters can restore an internal product bound with a separate proved complexity contract.

The two checked adapters share the complete image reading proof:

| Adapter | Fixed and varying arguments | Actual table key |
|---|---|---|
| ForwardKey | f = u, vary v in y | pair(u,v) |
| ReverseKey | f = v, vary u in x | pair(u,v) |

ReverseKey reverses the key constructor's input positions relative to the fixed/varying template. It does not reverse the arguments of H. This gives the required second orientation without copying the image proof or assuming symmetry first.

The present module proves uniform syntax/reading. It does not yet specialize that template to construct both actual internal image sets or prove a variable-indexed formula describing their set codes. The earlier constant-parameter first-image construction remains checked. A shared formula specialization/realization bridge must connect these presentations; a second independent branch-specific image implementation is not the preferred production route.

## Relative supremum formula

`IndexedSupremum` builds `upperAt A b` and `supremumAt B A b` from an indexed order formula and its reading theorem. The latter reads exactly:

    b ∈ B,
    every member of A is below b,
    and b is below every c ∈ B that bounds A.

The carrier B, internal image A and proposed value b are all variable indices. Both directions of the reading theorem are proved at arbitrary environments. In particular, minimality compares only upper bounds belonging to B; there is no implicit supremum over the entire host carrier or all external families.

The predicate does not independently assert A ⊆ B; the image construction must provide that bound. The module assumes no order laws and proves neither supremum existence nor uniqueness. Supply actual internally represented Boolean order/operations, their laws and relative completeness before using it to obtain a step output. Reuse the earlier unique-value machinery once its restricted-carrier hypotheses have been discharged, rather than introduce another selector or duplicate supremum-uniqueness proof.

## Remaining atomic construction

1. Prove a shared specialization/realization bridge from the indexed image template to actual internal sets, in both orientations, and connect the right image to the checked predecessor-agreement adapter. Keep the output B guard explicit.
2. Supply actual coded Boolean operations and order. Prove their laws and internal relative suprema, including the empty-family cases. The supremum formula by itself cannot discharge completeness.
3. Assemble the inner supremum and outer image/infimum formulas into the single expanded atomic Step. Prove its internal admission, uniqueness and locality before instantiating the already checked real-name-pair recursion engine.
4. Prove domain independence, fixed equality/membership adequacy and semantic laws, then the general-ground adapters. Fullness/Collection and the internal ultrafilter construction remain separate later obligations.

No production source, landmark or trilingual content changed. The generic value-agreement and syntax modules require no LEM. The actual L adapter uses only the existing successor-level LEM through its set/coordinate infrastructure. No host Choice, BPI, dependent/countable choice, resizing or host-wide image closure was introduced. This does not complete K0 or certify the whole T3 route.

## Verification

Final commands in `/tmp/bedrock-k0-probes/extraction/compile-root` all exited 0 with the required memory cap:

```text
GHCRTS="-A64m -I0 -M8g" agda src/PredecessorValueAgreement.agda
GHCRTS="-A64m -I0 -M8g" agda src/WeightedPredecessorAgreement.agda
GHCRTS="-A64m -I0 -M8g" agda src/IndexedWeightedImage.agda
GHCRTS="-A64m -I0 -M8g" agda src/IndexedSupremum.agda
```

The weighted adapter was rechecked after composing actual first-image equality. IndexedWeightedImage was rechecked after the coordinator expanded temporary helper/module names. IndexedSupremum's first check found unresolved implicit model-set arguments in two hProp proofs; explicit environment lookups closed them. Only final safe sources are archived. Baseline dependency caches were reused; no whole-tree build is claimed.

The scoped read-only audit is appended to `/tmp/bedrock-k0-probes/table-totality-design/REPORT.md`. It confirms both orientations, the absence of choice in graph transfer, the B-restricted supremum statement and the still-missing actual Boolean and uniform-set realization proofs.

Scoped prose/glossary gates and `git diff --check` exited 0. All tracked and copied baseline source files were compared byte-for-byte against `0177f9b3`, and archived snapshots match their SHA-256 values. Chapter-framework and whole-tree gates were not run for this temporary-probe/document-only change.

### PredecessorValueAgreement.agda

SHA-256: `b9f6270734eeb2f1f8a90c0f6b83f00bfe73d4875ec427a047ebb5a64bd0f0a6`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module PredecessorValueAgreement {ℓk ℓv ℓr ℓg : Level}
  (Key : Type ℓk) (Value : Type ℓv) (R : Key → Key → Type ℓr)
  (G H : Key → Value → hProp ℓg) where

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

Domain : (Key → Value → hProp ℓg) → Key → Type (ℓ-max ℓv ℓg)
Domain F q = ∥ Σ[ b ∈ Value ] ⟨ F q b ⟩ ∥₁

module At (p : Key)
  (left : ∀ q → R q p → Domain G q)
  (right : ∀ q → R q p → Domain H q)
  (same : ∀ q → R q p → ∀ b c → ⟨ G q b ⟩ → ⟨ H q c ⟩ → b ≡ c) where

  forward : ∀ q → R q p → ∀ b → ⟨ G q b ⟩ → ⟨ H q b ⟩
  forward q edge b graph = PT.rec (snd (H q b))
    (λ { (c , witness) → subst (λ d → ⟨ H q d ⟩)
      (sym (same q edge b c graph witness)) witness }) (right q edge)

  backward : ∀ q → R q p → ∀ b → ⟨ H q b ⟩ → ⟨ G q b ⟩
  backward q edge b graph = PT.rec (snd (G q b))
    (λ { (c , witness) → subst (λ d → ⟨ G q d ⟩)
      (same q edge c b witness graph) witness }) (left q edge)

  equivalent : ∀ q → R q p → ∀ b
    → (⟨ G q b ⟩ → ⟨ H q b ⟩) × (⟨ H q b ⟩ → ⟨ G q b ⟩)
  equivalent q edge b = forward q edge b , backward q edge b
```

### WeightedPredecessorAgreement.agda

SHA-256: `39f7ec33d3f363f7232792d91f2df5aede59d2ffb763092c70db6f331979b5bc`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module WeightedPredecessorAgreement {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import WeightedTableImage
open import L.Coding.Model {ℓ} using ( prʟ )
open import NameClosureDown lem using ( Child )
import NamePairDependency
import PredecessorValueAgreement
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )
module Dependency = NamePairDependency lem

module Tables (C B H K x y : S) (xC : ⟨ x ∈ˢ C ⟩) (yC : ⟨ y ∈ˢ C ⟩) where

  module Keys = Dependency.Domain C

  Value : Type (ℓ-suc ℓ)
  Value = Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩

  Graph : S → S → S → Type (ℓ-suc ℓ)
  Graph T q b = ⟨ prʟ q b ∈ˢ T ⟩

  Covers : S → Type (ℓ-suc ℓ)
  Covers T = ∀ q → ⟨ q ∈ˢ Keys.Product.product ⟩ → Dependency.Relation q (prʟ x y)
    → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × Graph T q b) ∥₁

  Same : Type (ℓ-suc ℓ)
  Same = ∀ q b c → ⟨ q ∈ˢ Keys.Product.product ⟩ → Dependency.Relation q (prʟ x y)
    → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ B ⟩ → Graph H q b → Graph K q c → b ≡ c

  module Core = PredecessorValueAgreement Keys.Key Value
    (λ q p → Dependency.Relation (fst q) (fst p))
    (λ q b → prʟ (fst q) (fst b) ∈ˢ H) (λ q b → prʟ (fst q) (fst b) ∈ˢ K)

  module Agreement (coversH : Covers H) (coversK : Covers K) (same : Same) where

    parent : Keys.Key
    parent = prʟ x y , Keys.Product.pair-in x y xC yC

    left-cover : ∀ q → Dependency.Relation (fst q) (fst parent)
      → Core.Domain (λ q b → prʟ (fst q) (fst b) ∈ˢ H) q
    left-cover (q , qD) edge = PT.map
      (λ { (b , bB , graph) → (b , bB) , graph }) (coversH q qD edge)

    right-cover : ∀ q → Dependency.Relation (fst q) (fst parent)
      → Core.Domain (λ q b → prʟ (fst q) (fst b) ∈ˢ K) q
    right-cover (q , qD) edge = PT.map
      (λ { (b , bB , graph) → (b , bB) , graph }) (coversK q qD edge)

    value-equality : ∀ q → Dependency.Relation (fst q) (fst parent)
      → ∀ b c → Graph H (fst q) (fst b) → Graph K (fst q) (fst c) → b ≡ c
    value-equality (q , qD) edge (b , bB) (c , cB) hb kc =
      Σ≡Prop (λ z → snd (z ∈ˢ B)) (same q b c qD edge bB cB hb kc)

    module Transfer = Core.At parent left-cover right-cover value-equality

    at-pair : ∀ u v → ⟨ u ∈ˢ C ⟩ → ⟨ v ∈ˢ C ⟩ → Child u x → Child v y
      → ∀ d → ⟨ d ∈ˢ B ⟩
      → (Graph H (prʟ u v) d → Graph K (prʟ u v) d)
        × (Graph K (prʟ u v) d → Graph H (prʟ u v) d)
    at-pair u v uC vC left right d dB = Transfer.equivalent
      (prʟ u v , Keys.Product.pair-in u v uC vC)
      (Dependency.pair-edge u v x y left right) (d , dB)

    left-image : ∀ u → ⟨ u ∈ˢ C ⟩ → Child u x
      → ∀ v c d → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
      → ⟨ prʟ v c ∈ˢ y ⟩
      → (Graph H (prʟ u v) d → Graph K (prʟ u v) d)
        × (Graph K (prʟ u v) d → Graph H (prʟ u v) d)
    left-image u uC left v c d vC cB dB entry =
      at-pair u v uC vC left ∣ c , entry ∣₁ d dB

    right-image : ∀ v → ⟨ v ∈ˢ C ⟩ → Child v y
      → ∀ u a d → ⟨ u ∈ˢ C ⟩ → ⟨ a ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
      → ⟨ prʟ u a ∈ˢ x ⟩
      → (Graph H (prʟ u v) d → Graph K (prʟ u v) d)
        × (Graph K (prʟ u v) d → Graph H (prʟ u v) d)
    right-image v vC right u a d uC aB dB entry =
      at-pair u v uC vC ∣ a , entry ∣₁ right d dB

    module LeftImage (u : S) (uC : ⟨ u ∈ˢ C ⟩) (left : Child u x)
      (Op : S → S → S → hProp (ℓ-suc ℓ))
      (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
      (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
        → (γ ⊨ opAt c d z) ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

      module Images = WeightedTableImage.Congruence lem C B y H K u Op opAt op-reading
        (left-image u uC left)

      image-equal : Images.Left.image ≡ Images.Right.image
      image-equal = Images.image-equal
```

### IndexedWeightedImage.agda

SHA-256: `5623ca6e1760c7ac0e2ae3d9e1781534ebef8dd6acabe13a3b193125e41b5441`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module IndexedWeightedImage {ℓ : Level} where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ )
open import CodedTableFunctionality {ℓ} using ( entryAt; entry-reading )
open import PairFormulaReading {ℓ} using ( reading )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

shiftFour : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
shiftFour i = suc (suc (suc (suc i)))

firstIndex : ∀ {n} → Fin (suc n)
firstIndex = zero

secondIndex : ∀ {n} → Fin (suc (suc n))
secondIndex = suc zero

thirdIndex : ∀ {n} → Fin (suc (suc (suc n)))
thirdIndex = suc (suc zero)

fourthIndex : ∀ {n} → Fin (suc (suc (suc (suc n))))
fourthIndex = suc (suc (suc zero))

module WithKey
  (Key : S → S → S)
  (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (keyAt-adequate : ∀ {n} (q f v : Fin n) (γ : Vec S n)
    → (γ ⊨ keyAt q f v)
      ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
         isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ)))) where

  module WithOperation
    (Op : S → S → S → hProp (ℓ-suc ℓ))
    (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    (opAt-adequate : ∀ {n} (c d z : Fin n) (γ : Vec S n)
      → (γ ⊨ opAt c d z)
        ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

    imageAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
      → Formula S n
    imageAt C B parent H f z =
      ∃̇∈ (var C) (∃̇∈ (var (suc B)) (∃̇∈ (var (suc (suc B))) (∃̇
        (entryAt (shiftFour parent) fourthIndex thirdIndex
        ∧̇ (keyAt firstIndex (shiftFour f) fourthIndex
        ∧̇ (entryAt (shiftFour H) firstIndex secondIndex
        ∧̇ opAt thirdIndex secondIndex (shiftFour z)))))))

    truncatedWitness : S → S → S → S → S → S → Type (ℓ-suc ℓ)
    truncatedWitness C B parent H f z = ∥ Σ[ v ∈ S ] Σ[ c ∈ S ] Σ[ d ∈ S ]
      (⟨ v ∈ˢ C ⟩ × ⟨ c ∈ˢ B ⟩ × ⟨ d ∈ˢ B ⟩
        × ⟨ prʟ v c ∈ˢ parent ⟩ × ⟨ prʟ (Key f v) d ∈ˢ H ⟩
        × ⟨ Op c d z ⟩) ∥₁

    imageAt-out : ∀ {n} (C B parent H f z : Fin n) (γ : Vec S n)
      → ⟨ γ ⊨ imageAt C B parent H f z ⟩
      → truncatedWitness (lookup C γ) (lookup B γ) (lookup parent γ)
          (lookup H γ) (lookup f γ) (lookup z γ)
    imageAt-out C B parent H f z γ = PT.rec PT.squash₁
      (λ { (v , vC , cs) → PT.rec PT.squash₁ (λ { (c , cB , ds) →
        PT.rec PT.squash₁ (λ { (d , dB , ks) → PT.map
          (λ { (k , vc , key , hd , op) →
            v , c , d , vC , cB , dB ,
            subst ⟨_⟩ (entry-reading (shiftFour parent) fourthIndex thirdIndex
              (k ∷ d ∷ c ∷ v ∷ γ)) vc ,
            subst (λ q → ⟨ prʟ q d ∈ˢ lookup H γ ⟩)
              (subst ⟨_⟩ (keyAt-adequate firstIndex (shiftFour f) fourthIndex
                (k ∷ d ∷ c ∷ v ∷ γ)) key)
              (subst ⟨_⟩ (entry-reading (shiftFour H) firstIndex secondIndex
                (k ∷ d ∷ c ∷ v ∷ γ)) hd) ,
            subst ⟨_⟩ (opAt-adequate thirdIndex secondIndex (shiftFour z)
              (k ∷ d ∷ c ∷ v ∷ γ)) op }) ks }) ds }) cs })

    imageAt-in : ∀ {n} (C B parent H f z : Fin n) (γ : Vec S n)
      → truncatedWitness (lookup C γ) (lookup B γ) (lookup parent γ)
          (lookup H γ) (lookup f γ) (lookup z γ)
      → ⟨ γ ⊨ imageAt C B parent H f z ⟩
    imageAt-in C B parent H f z γ = PT.map
      (λ { (v , c , d , vC , cB , dB , vc , hd , op) →
        v , vC , ∣ c , cB , ∣ d , dB , ∣ Key (lookup f γ) v ,
          subst ⟨_⟩ (sym (entry-reading (shiftFour parent) fourthIndex thirdIndex
            (Key (lookup f γ) v ∷ d ∷ c ∷ v ∷ γ))) vc ,
          subst ⟨_⟩ (sym (keyAt-adequate firstIndex (shiftFour f) fourthIndex
            (Key (lookup f γ) v ∷ d ∷ c ∷ v ∷ γ))) refl ,
          subst ⟨_⟩ (sym (entry-reading (shiftFour H) firstIndex secondIndex
            (Key (lookup f γ) v ∷ d ∷ c ∷ v ∷ γ))) hd ,
          subst ⟨_⟩ (sym (opAt-adequate thirdIndex secondIndex (shiftFour z)
            (Key (lookup f γ) v ∷ d ∷ c ∷ v ∷ γ))) op ∣₁ ∣₁ ∣₁ })

    imageAt-reading : ∀ {n} (C B parent H f z : Fin n) (γ : Vec S n)
      → (γ ⊨ imageAt C B parent H f z)
      ≡ (truncatedWitness (lookup C γ) (lookup B γ) (lookup parent γ)
          (lookup H γ) (lookup f γ) (lookup z γ) , PT.squash₁)
    imageAt-reading C B parent H f z γ = ⇔toPath
      (imageAt-out C B parent H f z γ) (imageAt-in C B parent H f z γ)

module ForwardKey = WithKey prʟ prAtL reading

reverseKeyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
reverseKeyAt q f v = prAtL q v f

reverse-key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
  → (γ ⊨ reverseKeyAt q f v)
    ≡ ((lookup q γ ≡ prʟ (lookup v γ) (lookup f γ)) ,
       isSetS (lookup q γ) (prʟ (lookup v γ) (lookup f γ)))
reverse-key-reading q f v γ = reading q v f γ

module ReverseKey = WithKey (λ f v → prʟ v f) reverseKeyAt reverse-key-reading
```

### IndexedSupremum.agda

SHA-256: `3eb3e9816de8e5907530d4b3eb5d73973f7d17dfbe5480938c702b94bac08a74`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module IndexedSupremum {ℓ : Level} where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇∈ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module WithOrder
  (Order : S → S → hProp (ℓ-suc ℓ))
  (orderAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (order-reading : ∀ {n} (x y : Fin n) (γ : Vec S n)
    → (γ ⊨ orderAt x y) ≡ Order (lookup x γ) (lookup y γ)) where

  Upper : S → S → Type (ℓ-suc ℓ)
  Upper A b = ∀ x → ⟨ x ∈ˢ A ⟩ → ⟨ Order x b ⟩

  upperAt : ∀ {n} → Fin n → Fin n → Formula S n
  upperAt A b = ∀̇∈ (var A) (orderAt zero (suc b))

  upper-is-prop : ∀ A b → isProp (Upper A b)
  upper-is-prop A b = isPropΠ (λ x → isPropΠ (λ _ → snd (Order x b)))

  upper-out : ∀ {n} (A b : Fin n) (γ : Vec S n)
    → ⟨ γ ⊨ upperAt A b ⟩ → Upper (lookup A γ) (lookup b γ)
  upper-out A b γ holds x member = subst ⟨_⟩
    (order-reading zero (suc b) (x ∷ γ)) (holds x member)

  upper-in : ∀ {n} (A b : Fin n) (γ : Vec S n)
    → Upper (lookup A γ) (lookup b γ) → ⟨ γ ⊨ upperAt A b ⟩
  upper-in A b γ holds x member = subst ⟨_⟩
    (sym (order-reading zero (suc b) (x ∷ γ))) (holds x member)

  upper-reading : ∀ {n} (A b : Fin n) (γ : Vec S n)
    → (γ ⊨ upperAt A b) ≡ (Upper (lookup A γ) (lookup b γ) , upper-is-prop (lookup A γ) (lookup b γ))
  upper-reading A b γ = ⇔toPath (upper-out A b γ) (upper-in A b γ)

  Supremum : S → S → S → Type (ℓ-suc ℓ)
  Supremum B A b = ⟨ b ∈ˢ B ⟩ × Upper A b ×
    ((c : S) → ⟨ c ∈ˢ B ⟩ → Upper A c → ⟨ Order b c ⟩)

  supremumAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  supremumAt B A b = (var b ∈̇ var B) ∧̇ (upperAt A b ∧̇
    ∀̇∈ (var B) (upperAt (suc A) zero ⇒̇ orderAt (suc b) zero))

  supremum-is-prop : ∀ B A b → isProp (Supremum B A b)
  supremum-is-prop B A b = isProp× (snd (b ∈ˢ B))
    (isProp× (upper-is-prop A b) (isPropΠ (λ c → isPropΠ (λ _ →
      isPropΠ (λ _ → snd (Order b c))))))

  supremum-out : ∀ {n} (B A b : Fin n) (γ : Vec S n)
    → ⟨ γ ⊨ supremumAt B A b ⟩ → Supremum (lookup B γ) (lookup A γ) (lookup b γ)
  supremum-out B A b γ holds = fst holds , upper-out A b γ (fst (snd holds)) ,
    λ c cB upper → subst ⟨_⟩ (order-reading (suc b) zero (c ∷ γ))
      (snd (snd holds) c cB (upper-in (suc A) zero (c ∷ γ) upper))

  supremum-in : ∀ {n} (B A b : Fin n) (γ : Vec S n)
    → Supremum (lookup B γ) (lookup A γ) (lookup b γ) → ⟨ γ ⊨ supremumAt B A b ⟩
  supremum-in B A b γ holds = fst holds , upper-in A b γ (fst (snd holds)) ,
    λ c cB upper → subst ⟨_⟩ (sym (order-reading (suc b) zero (c ∷ γ)))
      (snd (snd holds) c cB (upper-out (suc A) zero (c ∷ γ) upper))

  supremum-reading : ∀ {n} (B A b : Fin n) (γ : Vec S n)
    → (γ ⊨ supremumAt B A b)
      ≡ (Supremum (lookup B γ) (lookup A γ) (lookup b γ) , supremum-is-prop (lookup B γ) (lookup A γ) (lookup b γ))
  supremum-reading B A b γ = ⇔toPath (supremum-out B A b γ) (supremum-in B A b γ)
```
