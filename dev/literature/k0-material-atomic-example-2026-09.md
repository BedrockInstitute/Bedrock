# K0 material atomic examples on the actual recursion tables

Date: 2026-09-09. Baseline: `d689e0a8`. This follows the [attained-value probe](k0-atomic-value-set-2026-09.md) and targets the representative atomic example in E3 of the [exit checklist](k0-exit-checklist-2026-09.md). Production `src` remains unchanged.

## Shared internal membership construction

`PowersetAtomicMembership.For X C x y xC` specializes the existing weighted-image and supremum implementation to the actual solved recursion table on C × C. It does not introduce another recursion or a new definition of the equality value. Its `equality v vC` is the existing canonical table value at pair(x,v).

For a point z, `membership-reading` characterizes membership in the constructed Boolean membership value by the merely existing data:

```text
v belongs to C,
c belongs to B = P(X),
pair(v,c) belongs to y,
z belongs to c,
z belongs to the canonical equality value at (x,v).
```

The proof unfolds the existing internal union specification, reads the weighted image, and uses canonical table functionality to identify the stored value. The reverse implication inserts the actual canonical table entry into the existing image. These are propositional eliminations, not choices of entries.

This interface deliberately states its C restriction. It does not claim that an arbitrary domain C includes every child of y. The actual valid-name closure instance below supplies the required support for the example; a general global membership/domain-independence theorem is later work.

`For.Singleton` proves that a parent with exactly one encoded entry pair(u,c) has membership value equal to the intersection of c with the existing equality value at (x,u). Its input is an entry introduction and an entry decoder; the actual material singleton supplies both. Equality transport through the proposition-valued domain membership ensures that the result does not depend on which proof of u in C is used.

## Actual material constructors and the empty value

`MaterialWeightedSingleton` builds the singleton using the existing actual L pair constructor. It proves exact entry membership, child decoding, validity from a valid child and a weight in B, and that the resulting raw name differs from the empty raw name even when the weight is empty. It reuses the existing material weighted-entry bridge and the pair decoder.

`PowersetAtomicEmpty` proves the actual empty/empty recursion value is X, the top element of P(X). Both outer images are empty, their infima are X, and their intersection is X. The result is obtained from the actual table's coordinate equation; no empty-name computation law is assumed.

## The weighted singleton test

`PowersetSingletonMembership.For.AtWeight` proves:

```text
membership(empty, singleton(empty,b)) = b     for every b in P(X)
membership(empty, empty) = empty.
```

The first theorem composes the shared singleton calculation, the actual empty/empty equality value and intersection with X. `Actual X b bB` constructs the actual closed pair domain from the two valid names and discharges the domain input automatically. Thus this test is not conditional on a caller-supplied suitable container or preconstructed solution table.

The zero-weight specialization has the same membership value as the empty parent while its raw code is distinct. This is an explicit semantic calculation; it is not an assertion that raw names become path-equal.

## One representative substitution test

`PowersetZeroSingletonEquality` proves that the canonical equality value of the zero-weight singleton with the empty name is X. Every entry in the nonempty outer branch has zero weight, so its implication contributes X; the other outer branch is empty. The proof uses the actual coordinate equation. It does not duplicate the calculation for a reverse-direction theorem that this test does not need.

`PowersetAtomicRepresentative.ActualZero X` constructs one actual closed pair domain internally and packages three checked facts in `representative`:

```text
zeroSingleton is not path-equal to the empty name,
the canonical equality value of (zeroSingleton,empty) is X,
membership(empty,zeroSingleton) = membership(empty,empty).
```

No caller domain or table argument is required. This is a representative substitution calculation in the fixed context membership(empty,-). It is not a theorem of congruence for every name, argument position or formula. Together with the arbitrary-weight calculation on the actual tables, it meets E3's original representative-example requirement. The full substitution calculus remains K4.

## Acceptance boundary and assumptions

The pointwise construction and weighted singleton calculation exercise the chosen material representation, actual recursion and actual internal Boolean operations. They are not a second finite evaluator detached from the internal tables. General Boolean laws, all-name substitution, global membership-formula adequacy and arbitrary-formula induction remain K4 work. E3 is passed at its representative-example boundary. E1 and E5 retain their adapter/composition gaps, while E2/E6 still require the final representation and assumption decision. K0 as a whole is not complete.

No host Choice, BPI, Zorn, resizing, ultrafilter selector or stronger LEM is introduced. Concrete L operations retain `LEM (ℓ-suc ℓ)`. The generic bounded-domain interfaces state their memberships and entry contracts explicitly; the actual example discharges them using the existing name-closure construction.

## Verification

The archived sources passed the prescribed safe Agda checks in the temporary compile root, with at most two Agda processes and the 8 GB heap cap. The coordinator checked the membership construction and the integrated concrete example. Scoped prose/glossary gates, exact snapshots and hashes, local links and `git diff --check` passed. All 123 tracked production sources and their copied probe-baseline versions match `d689e0a8` byte-for-byte. Whole-tree and trilingual chapter gates were not run for this temporary-probe/documentation batch.

Earlier empty-value checks exposed scope/import errors; one broad-alias diagnostic was interrupted after about three minutes. Narrowing aliases exposed two unsolved implicit terms in empty-entry elimination, resolved by explicitly supplying pair(u,a). The final source has no holes and its check exited 0. These were elaboration issues, not extra mathematical assumptions.

The zero-singleton diagnostic was likewise interrupted while using broad aliases, then passed in about four seconds after narrow imports. All final sources use the checked kernel. Final checks included:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/MaterialWeightedSingleton.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicEmpty.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicMembership.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetSingletonMembership.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetZeroSingletonEquality.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicRepresentative.agda
```

The last integrated check also rechecked the singleton and zero-equality clients after extracting the empty-weight bound into one reusable `empty-in-B` helper. The final singleton constructor check corrected an initial out-of-scope equality-reflection reference by reusing the existing `ProductSet.S≡` adapter.

## Source snapshots

### MaterialWeightedSingleton.agda

SHA-256: `eb31a03e0c54cffd1dcc29a9abea26e0cdf98d012c4d4f1f67c21b418be8ce4c`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module MaterialWeightedSingleton {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-inj )
open import MaterialNameL {ℓ} lem using ( ground )
open import MaterialNamePredicate 𝒮ʟ using ( module Names )
open import NameRecognition {ℓ} lem using ( entry-bridge )
open import NameClosureDown {ℓ} lem using ( Child )
open import GroundClosure 𝒮ʟ using ( module MaterialNames )
import FOL.ZFModel as Model
open import ProductSet {ℓ} lem using ( S≡ )
open import Cubical.Data.Empty using ( ⊥; rec* )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
module Ground = Model.isZFModel ground

module For (B : S) where

  module Predicate = Names ground (λ _ → refl) B
  module Material = MaterialNames ground

  empty : S
  empty = fst Predicate.empty

  singletonName : S → S → S
  singletonName u b = Ground.pair (prʟ u b) (prʟ u b)

  member-out : ∀ p u b → ⟨ p ∈ˢ singletonName u b ⟩ → p ≡ prʟ u b
  member-out p u b member = PT.rec (isSetS p (prʟ u b))
    (λ { (inl eq) → S≡ eq
       ; (inr eq) → S≡ eq })
    (subst ⟨_⟩ (Ground.pair-spec (prʟ u b) (prʟ u b) p) member)

  member-in : ∀ p u b → p ≡ prʟ u b → ⟨ p ∈ˢ singletonName u b ⟩
  member-in p u b eq = subst (λ z → ⟨ z ∈ˢ singletonName u b ⟩) (sym eq)
    (subst ⟨_⟩ (sym (Ground.pair-spec (prʟ u b) (prʟ u b) (prʟ u b)))
      ∣ inl refl ∣₁)

  member-reading : ∀ p u b
    → (p ∈ˢ singletonName u b) ≡ ((p ≡ prʟ u b) , isSetS p (prʟ u b))
  member-reading p u b = ⇔toPath (member-out p u b) (member-in p u b)

  child-out : ∀ z u b → Child z (singletonName u b) → z ≡ u
  child-out z u b = PT.rec (isSetS z u) λ { (d , member) →
    fst (prʟ-inj (member-out (prʟ z d) u b member)) }

  child-in : ∀ u b → Child u (singletonName u b)
  child-in u b = ∣ b , member-in (prʟ u b) u b refl ∣₁

  valid : ∀ u b → ⟨ Predicate.IsName u ⟩ → ⟨ b ∈ˢ B ⟩
    → ⟨ Predicate.IsName (singletonName u b) ⟩
  valid u b validU bB = subst ⟨_⟩ (sym (Predicate.unfold (singletonName u b)))
    (shape , hereditary)
    where
    shape : ⟨ Predicate.Shape (singletonName u b) ⟩
    shape p member = ∣ u , b ,
      member-out p u b member ∙ sym (entry-bridge u b) , bB ∣₁

    hereditary : ∀ z → ∥ Σ[ d ∈ S ]
      ⟨ Material.weightedEntry z d ∈ˢ singletonName u b ⟩ ∥₁
      → ⟨ Predicate.IsName z ⟩
    hereditary z = PT.rec (snd (Predicate.IsName z)) λ { (d , member) →
      subst (λ v → ⟨ Predicate.IsName v ⟩)
        (sym (fst (prʟ-inj
          (sym (entry-bridge z d) ∙ member-out (Material.weightedEntry z d) u b member))))
        validU }

  singleton≢empty : ∀ u b → singletonName u b ≡ empty → ⊥
  singleton≢empty u b eq = rec*
    (subst ⟨_⟩ (Material.emptyName-spec (prʟ u b))
      (subst (λ n → ⟨ prʟ u b ∈ˢ n ⟩) eq
        (member-in (prʟ u b) u b refl)))
```

### PowersetAtomicEmpty.agda

SHA-256: `a962fc18229de810696d309b7fcd943f9d63bb180b508ad07621bfaf511a077d`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicEmpty {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import MaterialNameL
import GroundClosure
import ClosedNamePairDomain
import PowersetAtomicExpression
import PowersetStepFormula
import PowersetAtomicTable
import InternalPowersetInfimum
import InternalIntersection
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module For (X : S) where

  module Names = MaterialNameL.At lem
    (InternalPowersetInfimum.For.B lem X) using ( empty )
  module EmptySet = GroundClosure.MaterialNames 𝒮ʟ (MaterialNameL.ground lem)
    using ( emptyName-spec )
  module Expression = PowersetAtomicExpression.For lem X
    using ( module Forward; module Reverse; module Expression )
  module Raw = PowersetStepFormula.For lem X using ( Step )
  module Infimum = InternalPowersetInfimum.For lem X
    using ( B; infimum; empty-family-infimum )
  module Ground = InternalPowersetInfimum.Ground lem
  module Intersection = InternalIntersection lem
    using ( intersection; intersection-membership )

  empty : S
  empty = fst Names.empty

  empty-valid : ⟨ ClosedNamePairDomain.For.Names.IsName lem Infimum.B empty ⟩
  empty-valid = snd Names.empty

  empty-spec : ∀ z → (z ∈ˢ empty) ≡ ⊥
  empty-spec = EmptySet.emptyName-spec

  module RawProof (C H : S) where

    module Left = Expression.Forward.Construction C empty empty H
      using ( value; module Image )
    module Right = Expression.Reverse.Construction C empty empty H
      using ( value; module Image )
    module Actual = Expression.Expression C empty empty H using ( value )

    left-image-empty : Left.Image.image ≡ Ground.∅
    left-image-empty = Ground.extensional λ z → ⇔toPath
      (λ member → PT.rec (snd (z ∈ˢ Ground.∅))
        (λ { (u , a , j , uC , aB , jB , entry , inner , op) → Empty.rec*
          (subst ⟨_⟩ (empty-spec (prʟ u a)) entry) })
        (snd (Left.Image.image-out z member)))
      (λ member → Empty.rec*
        (subst ⟨_⟩ (Ground.hasEmpty .fst .snd z) member))

    right-image-empty : Right.Image.image ≡ Ground.∅
    right-image-empty = Ground.extensional λ z → ⇔toPath
      (λ member → PT.rec (snd (z ∈ˢ Ground.∅))
        (λ { (u , a , j , uC , aB , jB , entry , inner , op) → Empty.rec*
          (subst ⟨_⟩ (empty-spec (prʟ u a)) entry) })
        (snd (Right.Image.image-out z member)))
      (λ member → Empty.rec*
        (subst ⟨_⟩ (Ground.hasEmpty .fst .snd z) member))

    left-value-is-X : Left.value ≡ X
    left-value-is-X = cong Infimum.infimum left-image-empty ∙ Infimum.empty-family-infimum

    right-value-is-X : Right.value ≡ X
    right-value-is-X = cong Infimum.infimum right-image-empty ∙ Infimum.empty-family-infimum

    intersection-idempotent : Intersection.intersection X X ≡ X
    intersection-idempotent = Ground.extensional λ z → ⇔toPath
      (λ member → fst (subst ⟨_⟩ (Intersection.intersection-membership z X X) member))
      (λ member → subst ⟨_⟩ (sym (Intersection.intersection-membership z X X))
        (member , member))

    value-is-X : Actual.value ≡ X
    value-is-X = cong₂ Intersection.intersection left-value-is-X right-value-is-X
      ∙ intersection-idempotent

  raw-empty : ∀ C H → ⟨ Raw.Step C empty empty H X ⟩
  raw-empty C H = sym (RawProof.value-is-X C H)

  module AtDomain (C : S) (emptyC : ⟨ empty ∈ˢ C ⟩) where

    module Atomic = PowersetAtomicTable.For lem X C
      using ( D; table; value; coordinate-equation; module Keys )

    key : ⟨ prʟ empty empty ∈ˢ Atomic.D ⟩
    key = Atomic.Keys.Product.pair-in empty empty emptyC emptyC

    value : S
    value = Atomic.value (prʟ empty empty) key

    equation : ⟨ Raw.Step C empty empty Atomic.table value ⟩
    equation = Atomic.coordinate-equation empty empty emptyC emptyC

    value-is-X : value ≡ X
    value-is-X = equation ∙ RawProof.value-is-X C Atomic.table
```

### PowersetAtomicMembership.agda

SHA-256: `7a762181f10c6eb85a5cb6d74561523d104f1535438a84136ab31a4b7ce10d8e`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicMembership {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import PowersetAtomicTable
import PowersetWeightedSupremum
import InternalPowersetSupremum
import InternalIntersection
import NamePairDependency
import FOL.ZFModel as Model
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )

module For (X C x y : S) (xC : ⟨ x ∈ˢ C ⟩) where

  module Algebra = InternalPowersetSupremum.For lem X
    using ( B; module Supremum )
  module Ground = InternalPowersetSupremum.Ground lem using ( hasUnion; extensional )
  module Table = PowersetAtomicTable.For lem X C
    using ( table; value; value-in-B; graph; functional )
  module Product = NamePairDependency.Domain.Product lem C using ( pair-in )
  module Weighted = PowersetWeightedSupremum.For.Forward.Construction lem X C y Table.table x
    using ( value; value-in-B; correct; entry-value-in-image; module Image )
  module Meet = InternalIntersection lem using ( intersection; intersection-in; intersection-out )

  equality : (v : S) → ⟨ v ∈ˢ C ⟩ → S
  equality v vC = Table.value (prʟ x v) (Product.pair-in x v xC vC)

  membership : S
  membership = Weighted.value

  membership-in-B : ⟨ membership ∈ˢ Algebra.B ⟩
  membership-in-B = Weighted.value-in-B

  Pointwise : S → Type (ℓ-suc ℓ)
  Pointwise z = ∥ Σ[ v ∈ S ] Σ[ c ∈ S ] Σ[ vC ∈ ⟨ v ∈ˢ C ⟩ ]
    ⟨ c ∈ˢ Algebra.B ⟩ × ⟨ prʟ v c ∈ˢ y ⟩ ×
    ⟨ z ∈ˢ c ⟩ × ⟨ z ∈ˢ equality v vC ⟩ ∥₁

  entry-in-image : ∀ v c (vC : ⟨ v ∈ˢ C ⟩) → ⟨ c ∈ˢ Algebra.B ⟩
    → ⟨ prʟ v c ∈ˢ y ⟩
    → ⟨ Meet.intersection c (equality v vC) ∈ˢ Weighted.Image.image ⟩
  entry-in-image v c vC cB entry = Weighted.entry-value-in-image v c (equality v vC)
    vC cB (Table.value-in-B (prʟ x v) (Product.pair-in x v xC vC)) entry
    (Table.graph (prʟ x v) (Product.pair-in x v xC vC))

  out : ∀ z → ⟨ z ∈ˢ membership ⟩ → Pointwise z
  out z member = PT.rec PT.squash₁
    (λ { (a , aI , za) → PT.rec PT.squash₁
      (λ { (v , c , d , vC , cB , dB , entry , graph , eq) →
        let parts = Meet.intersection-out z c d
              (subst (λ A → ⟨ z ∈ˢ A ⟩) eq za)
            same = Table.functional (prʟ x v) d (equality v vC)
              (Product.pair-in x v xC vC) dB
              (Table.value-in-B (prʟ x v) (Product.pair-in x v xC vC)) graph
              (Table.graph (prʟ x v) (Product.pair-in x v xC vC))
        in ∣ v , c , vC , cB , entry , fst parts ,
          subst (λ A → ⟨ z ∈ˢ A ⟩) same (snd parts) ∣₁ })
      (snd (Weighted.Image.image-out a aI)) })
    (subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Ground.hasUnion Weighted.Image.image) z) member)

  into : ∀ z → Pointwise z → ⟨ z ∈ˢ membership ⟩
  into z = PT.rec (snd (z ∈ˢ membership))
    (λ { (v , c , vC , cB , entry , zc , zd) → subst ⟨_⟩
      (sym (Model.℩-spec 𝒮ʟ (Ground.hasUnion Weighted.Image.image) z))
      ∣ Meet.intersection c (equality v vC) , entry-in-image v c vC cB entry ,
        Meet.intersection-in z c (equality v vC) zc zd ∣₁ })

  membership-reading : ∀ z → (z ∈ˢ membership) ≡ (Pointwise z , PT.squash₁)
  membership-reading z = ⇔toPath (out z) (into z)

  module Singleton (u c : S) (uC : ⟨ u ∈ˢ C ⟩) (cB : ⟨ c ∈ˢ Algebra.B ⟩)
    (entry-in : ⟨ prʟ u c ∈ˢ y ⟩)
    (entry-out : ∀ v d → ⟨ prʟ v d ∈ˢ y ⟩ → (v ≡ u) × (d ≡ c)) where

    collapse : ∀ z → Pointwise z → ⟨ z ∈ˢ Meet.intersection c (equality u uC) ⟩
    collapse z = PT.rec (snd (z ∈ˢ Meet.intersection c (equality u uC)))
      (λ { (v , d , vC , dB , entry , zd , ze) →
        let decoded = entry-out v d entry
            same = cong (λ p → equality (fst p) (snd p))
              (Σ≡Prop (λ a → snd (a ∈ˢ C)) {u = v , vC} {v = u , uC} (fst decoded))
        in Meet.intersection-in z c (equality u uC)
          (subst (λ a → ⟨ z ∈ˢ a ⟩) (snd decoded) zd)
          (subst (λ a → ⟨ z ∈ˢ a ⟩) same ze) })

    expand : ∀ z → ⟨ z ∈ˢ Meet.intersection c (equality u uC) ⟩ → Pointwise z
    expand z member = ∣ u , c , uC , cB , entry-in ,
      Meet.intersection-out z c (equality u uC) member ∣₁

    exact : membership ≡ Meet.intersection c (equality u uC)
    exact = Ground.extensional (λ z → ⇔toPath
      (λ member → collapse z (out z member))
      (λ member → into z (expand z member)))
```

### PowersetSingletonMembership.agda

SHA-256: `56b751326f4320ac73b3ed6573c7459d72bc160e861d6e21ac0c698654c336f3`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetSingletonMembership {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-inj )
import ClosedNamePairDomain
import MaterialWeightedSingleton
import PowersetAtomicEmpty
import PowersetAtomicMembership
import InternalPowersetSupremum
import InternalIntersection
import FOL.ZFModel as Model
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

empty-in-B : ∀ X → ⟨ PowersetAtomicEmpty.For.empty lem X
  ∈ˢ InternalPowersetSupremum.For.B lem X ⟩
empty-in-B X = subst ⟨_⟩
  (sym (Model.℩-spec 𝒮ʟ (InternalPowersetSupremum.Ground.hasPower lem X)
    (PowersetAtomicEmpty.For.empty lem X)))
  (λ z member → Empty.rec*
    (subst ⟨_⟩ (PowersetAtomicEmpty.For.empty-spec lem X z) member))

module For (X C : S)
  (emptyC : ⟨ PowersetAtomicEmpty.For.empty lem X ∈ˢ C ⟩) where

  module Algebra = InternalPowersetSupremum.For lem X using ( B )
  module Ground = InternalPowersetSupremum.Ground lem using ( extensional; hasPower )
  module Names = MaterialWeightedSingleton.For lem Algebra.B
    using ( singletonName; member-in; member-out; singleton≢empty )
  module Zero = PowersetAtomicEmpty.For lem X using ( empty; empty-spec; module AtDomain )
  module Meet = InternalIntersection lem using ( intersection; intersection-in; intersection-out )

  module AtWeight (b : S) (bB : ⟨ b ∈ˢ Algebra.B ⟩) where

    name : S
    name = Names.singletonName Zero.empty b

    module Member = PowersetAtomicMembership.For lem X C Zero.empty name emptyC
      using ( membership; module Singleton )
    module One = Member.Singleton Zero.empty b emptyC bB
      (Names.member-in (prʟ Zero.empty b) Zero.empty b refl)
      (λ v d entry → prʟ-inj (Names.member-out (prʟ v d) Zero.empty b entry))
      using ( exact )

    meet-top : Meet.intersection b X ≡ b
    meet-top = Ground.extensional (λ z → ⇔toPath
      (λ member → fst (Meet.intersection-out z b X member))
      (λ member → Meet.intersection-in z b X member
        (subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Ground.hasPower X) b) bB z member)))

    membership-is-weight : Member.membership ≡ b
    membership-is-weight = One.exact
      ∙ cong (Meet.intersection b) (Zero.AtDomain.value-is-X C emptyC)
      ∙ meet-top

    raw-nonempty : name ≡ Zero.empty → Empty.⊥
    raw-nonempty = Names.singleton≢empty Zero.empty b

  module EmptyMember = PowersetAtomicMembership.For lem X C Zero.empty Zero.empty emptyC
    using ( membership; out )

  empty-membership : EmptyMember.membership ≡ Zero.empty
  empty-membership = Ground.extensional (λ z → ⇔toPath
    (λ member → PT.rec (snd (z ∈ˢ Zero.empty))
      (λ { (v , c , vC , cB , entry , zc , zd) → Empty.rec*
        (subst ⟨_⟩ (Zero.empty-spec (prʟ v c)) entry) }) (EmptyMember.out z member))
    (λ member → Empty.rec* (subst ⟨_⟩ (Zero.empty-spec z) member)))

  zero-in-B : ⟨ Zero.empty ∈ˢ Algebra.B ⟩
  zero-in-B = empty-in-B X

  zero-membership-agrees : AtWeight.Member.membership Zero.empty zero-in-B
    ≡ EmptyMember.membership
  zero-membership-agrees = AtWeight.membership-is-weight Zero.empty zero-in-B
    ∙ sym empty-membership

module Actual (X b : S) (bB : ⟨ b ∈ˢ InternalPowersetSupremum.For.B lem X ⟩) where

  module Algebra = InternalPowersetSupremum.For lem X using ( B )
  module Zero = PowersetAtomicEmpty.For lem X using ( empty; empty-valid )
  module Names = MaterialWeightedSingleton.For lem Algebra.B using ( singletonName; valid )
  module Domain = ClosedNamePairDomain.For.PairOf lem Algebra.B
    Zero.empty (Names.singletonName Zero.empty b) Zero.empty-valid
    (Names.valid Zero.empty b Zero.empty-valid bB)
    using ( C; contains-x )
  module Test = For X Domain.C Domain.contains-x using ( module AtWeight )

  membership-is-weight : Test.AtWeight.Member.membership b bB ≡ b
  membership-is-weight = Test.AtWeight.membership-is-weight b bB
```

### PowersetZeroSingletonEquality.agda

SHA-256: `5422a4950e99781234c1482ab400e923b712ae01fd01453b85cddb301eeb4347`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetZeroSingletonEquality {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-inj )
import PowersetAtomicEmpty
import PowersetAtomicExpression
import PowersetAtomicTable
import PowersetSingletonMembership
import MaterialWeightedSingleton
import InternalPowersetImplication
import InternalPowersetInfimum
import InternalPowersetSupremum
import InternalIntersection
import FOL.ZFModel as Model
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )

module For (X C : S)
  (emptyC : ⟨ PowersetAtomicEmpty.For.empty lem X ∈ˢ C ⟩) where

  module Algebra = InternalPowersetSupremum.For lem X using ( B )
  module Ground = InternalPowersetSupremum.Ground lem
    using ( ∅; ⋃; extensional; hasEmpty; hasUnion )
  module Zero = PowersetAtomicEmpty.For lem X using ( empty; empty-spec )
  module Membership = PowersetSingletonMembership.For lem X C emptyC using ( zero-in-B )
  module Names = MaterialWeightedSingleton.For lem Algebra.B
    using ( singletonName; member-in; member-out; valid; module Predicate )
  module Expression = PowersetAtomicExpression.For lem X
    using ( module Forward; module Reverse; module Expression )
  module Implication = InternalPowersetImplication lem
    using ( implication; implication-out; implication-in )
  module Infimum = InternalPowersetInfimum.For lem X
    using ( infimum; infimum-membership; empty-family-infimum )
  module Intersection = InternalIntersection lem
    using ( intersection; intersection-out; intersection-in )

  zeroSingleton : S
  zeroSingleton = Names.singletonName Zero.empty Zero.empty

  zeroSingleton-valid : ⟨ Names.Predicate.IsName zeroSingleton ⟩
  zeroSingleton-valid = Names.valid
    Zero.empty Zero.empty (PowersetAtomicEmpty.For.empty-valid lem X) Membership.zero-in-B

  module Proof (zeroSingletonC : ⟨ zeroSingleton ∈ˢ C ⟩) (H : S) where

    module Inner = Expression.Forward.Values.Construction C Zero.empty H Zero.empty

    inner-image-empty : Inner.Image.image ≡ Ground.∅
    inner-image-empty = Ground.extensional λ z → ⇔toPath
      (λ member → PT.rec (snd (z ∈ˢ Ground.∅))
        (λ { (v , c , d , vC , cB , dB , entry , graph , op) → Empty.rec*
          (subst ⟨_⟩ (Zero.empty-spec (prʟ v c)) entry) })
        (snd (Inner.Image.image-out z member)))
      (λ member → Empty.rec* (subst ⟨_⟩ (Ground.hasEmpty .fst .snd z) member))

    union-empty : Ground.⋃ Ground.∅ ≡ Ground.∅
    union-empty = Ground.extensional λ z → ⇔toPath
      (λ member → PT.rec (snd (z ∈ˢ Ground.∅))
        (λ { (A , A∅ , zA) → Empty.rec*
          (subst ⟨_⟩ (Ground.hasEmpty .fst .snd A) A∅) })
        (subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Ground.hasUnion Ground.∅) z) member))
      (λ member → Empty.rec* (subst ⟨_⟩ (Ground.hasEmpty .fst .snd z) member))

    ground-empty-is-zero : Ground.∅ ≡ Zero.empty
    ground-empty-is-zero = Ground.extensional λ z → ⇔toPath
      (λ member → Empty.rec* (subst ⟨_⟩ (Ground.hasEmpty .fst .snd z) member))
      (λ member → Empty.rec* (subst ⟨_⟩ (Zero.empty-spec z) member))

    inner-value-empty : Inner.value ≡ Zero.empty
    inner-value-empty = cong Ground.⋃ inner-image-empty ∙ union-empty ∙ ground-empty-is-zero

    implication-empty : Implication.implication X Zero.empty Zero.empty ≡ X
    implication-empty = Ground.extensional λ z → ⇔toPath
      (λ member → fst (Implication.implication-out X Zero.empty Zero.empty z member))
      (λ zX → Implication.implication-in X Zero.empty Zero.empty z zX
        (λ z∅ → Empty.rec* (subst ⟨_⟩ (Zero.empty-spec z) z∅)))

    module Left = Expression.Forward.Construction C zeroSingleton Zero.empty H

    inner-unique : ∀ j → ⟨ Expression.Forward.Inner C Algebra.B Zero.empty H Zero.empty j ⟩
      → j ≡ Inner.value
    inner-unique j correct = Ground.extensional λ z → ⇔toPath
      (snd (snd correct) Inner.value Inner.value-in-B (fst (snd Inner.correct)) z)
      (snd (snd Inner.correct) j (fst correct) (fst (snd correct)) z)

    image-element-is-X : ∀ z → ⟨ z ∈ˢ Left.Image.image ⟩ → z ≡ X
    image-element-is-X z member = PT.rec (isSetS z X)
      (λ { (u , a , j , uC , aB , jB , entry , inner , op) →
        let decoded = prʟ-inj (Names.member-out (prʟ u a) Zero.empty Zero.empty entry)
            j-equal = inner-unique j
              (subst (λ v → ⟨ Expression.Forward.Inner C Algebra.B Zero.empty H v j ⟩)
                (fst decoded) inner)
        in op ∙ cong₂ (Implication.implication X) (snd decoded) j-equal
          ∙ cong (Implication.implication X Zero.empty) inner-value-empty
          ∙ implication-empty })
      (snd (Left.Image.image-out z member))

    left-value-is-X : Left.value ≡ X
    left-value-is-X = Ground.extensional λ z → ⇔toPath
      (λ member → fst (subst ⟨_⟩ (Infimum.infimum-membership z Left.Image.image) member))
      (λ zX → subst ⟨_⟩ (sym (Infimum.infimum-membership z Left.Image.image))
        (zX , λ A member → subst (λ Y → ⟨ z ∈ˢ Y ⟩)
          (sym (image-element-is-X A member)) zX))

    module Right = Expression.Reverse.Construction C Zero.empty zeroSingleton H

    right-image-empty : Right.Image.image ≡ Ground.∅
    right-image-empty = Ground.extensional λ z → ⇔toPath
      (λ member → PT.rec (snd (z ∈ˢ Ground.∅))
        (λ { (u , a , j , uC , aB , jB , entry , inner , op) → Empty.rec*
          (subst ⟨_⟩ (Zero.empty-spec (prʟ u a)) entry) })
        (snd (Right.Image.image-out z member)))
      (λ member → Empty.rec* (subst ⟨_⟩ (Ground.hasEmpty .fst .snd z) member))

    right-value-is-X : Right.value ≡ X
    right-value-is-X = cong Infimum.infimum right-image-empty ∙ Infimum.empty-family-infimum

    intersection-idempotent : Intersection.intersection X X ≡ X
    intersection-idempotent = Ground.extensional λ z → ⇔toPath
      (λ member → fst (Intersection.intersection-out z X X member))
      (λ member → Intersection.intersection-in z X X member member)

    module Actual = Expression.Expression C zeroSingleton Zero.empty H

    raw-value-is-X : Actual.value ≡ X
    raw-value-is-X = cong₂ Intersection.intersection left-value-is-X right-value-is-X
      ∙ intersection-idempotent

  module AtDomain (zeroSingletonC : ⟨ zeroSingleton ∈ˢ C ⟩) where

    module Atomic = PowersetAtomicTable.For lem X C
      using ( D; table; value; coordinate-equation; module Keys )

    key : ⟨ prʟ zeroSingleton Zero.empty ∈ˢ Atomic.D ⟩
    key = Atomic.Keys.Product.pair-in zeroSingleton Zero.empty zeroSingletonC emptyC

    value : S
    value = Atomic.value (prʟ zeroSingleton Zero.empty) key

    value-is-X : value ≡ X
    value-is-X = Atomic.coordinate-equation zeroSingleton Zero.empty zeroSingletonC emptyC
      ∙ Proof.raw-value-is-X zeroSingletonC Atomic.table
```

### PowersetAtomicRepresentative.agda

SHA-256: `9ef61ff7a174d7d3ca26f086e3d6299c03a7c360e67622268679225120954014`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicRepresentative {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
import InternalPowersetSupremum
import MaterialWeightedSingleton
import PowersetAtomicEmpty
import PowersetSingletonMembership
import PowersetZeroSingletonEquality
import ClosedNamePairDomain
import Cubical.Data.Empty as Empty

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ActualZero (X : S) where

  module Algebra = InternalPowersetSupremum.For lem X using ( B )
  module Zero = PowersetAtomicEmpty.For lem X using ( empty; empty-valid )
  module Names = MaterialWeightedSingleton.For lem Algebra.B
    using ( singletonName; valid; singleton≢empty )

  zero-in-B : ⟨ Zero.empty ∈ˢ Algebra.B ⟩
  zero-in-B = PowersetSingletonMembership.empty-in-B lem X

  name : S
  name = Names.singletonName Zero.empty Zero.empty

  module Domain = ClosedNamePairDomain.For.PairOf lem Algebra.B Zero.empty name
    Zero.empty-valid (Names.valid Zero.empty Zero.empty Zero.empty-valid zero-in-B)
    using ( C; contains-x; contains-y )
  module Member = PowersetSingletonMembership.For lem X Domain.C Domain.contains-x
    using ( zero-membership-agrees; module AtWeight; module EmptyMember )
  module Equality = PowersetZeroSingletonEquality.For.AtDomain lem X Domain.C
    Domain.contains-x Domain.contains-y using ( value; value-is-X )

  raw-distinct : name ≡ Zero.empty → Empty.⊥
  raw-distinct = Names.singleton≢empty Zero.empty Zero.empty

  equality-top : Equality.value ≡ X
  equality-top = Equality.value-is-X

  member-context-agrees : Member.AtWeight.Member.membership Zero.empty zero-in-B
    ≡ Member.EmptyMember.membership
  member-context-agrees = Member.zero-membership-agrees

  representative : (name ≡ Zero.empty → Empty.⊥) × (Equality.value ≡ X) ×
    (Member.AtWeight.Member.membership Zero.empty zero-in-B ≡ Member.EmptyMember.membership)
  representative = raw-distinct , equality-top , member-context-agrees
```
