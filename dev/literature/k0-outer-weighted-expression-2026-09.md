# K0 outer weighted images and the powerset atomic expression

Date: 2026-09-09. Source baseline: `c45bc015`. Four safe temporary probes checked. This continues the [actual powerset weighted joins](k0-powerset-weighted-joins-2026-09.md). K0 remains open.

## Actual implication and relative infima

`InternalPowersetImplication` constructs, by Separation from X, the set of w in X such that membership in c implies membership in d. It proves exact membership, closure in the previously constructed P(X), and the arbitrary-environment reading of `implicationAt X c d z` as literal equality of z with this set. Its adjunction theorem proves, for a ⊆ X:

    a ⊆ implication(X,c,d) iff a ∩ c ⊆ d.

Thus the operation is characterized by its mathematical property, not just given a suggestive name. Full Boolean algebra packaging and the separate Boolean-law audit are still pending. The construction uses the existing LEM budget for the L model and introduces no host choice.

`InternalPowersetInfimum` reverses the already checked subset order and delegates its variable-indexed infimum formula and reading to `IndexedSupremum`. It does not duplicate the generic extremum syntax/proof. For every actual internal A, it constructs

    { w in X | for every a in A, w in a }.

The result belongs to P(X), is below every a in A, and lies above every competing lower bound in P(X). This statement is valid even when A is not bounded by P(X); when A is an internal family of Boolean values, it is its relative infimum. The explicit empty-family theorem identifies the infimum of the internal empty set with X. No nonempty-family premise or selected member of A is required.

## A shared outer-image template

`OuterWeightedImage` takes an inner-value relation with a finite formula and arbitrary-environment reading, and an operation relation with the same kind of certificate. Its image predicate has seven variable parameters X, C, B, outer, inner, H, z. It reads:

    merely some u in C, a in B, j in B satisfy
      pair(u,a) in outer,
      Inner(C,B,inner,H,u,j),
      Op(X,a,j,z).

The formula has bounded quantifiers for u, a and j; the supplied inner/operation formulas may themselves contain unbounded quantifiers. No Delta-zero claim is made. The root module reuses an existing actual L ground adapter for Separation; its image construction does not use powerset algebra operations.

Parameter specialization feeds this single template to actual L Separation from B. Both exact membership directions are proved. Every original weighted entry remains in the existential specification; neither duplicate child coordinates nor repeated values require representatives or a choice of one weight per child.

The generic congruence theorem transfers equivalent inner relations at the relevant entries into actual outer-image equality. It eliminates truncation only into propositions and does not extract an inner-value function from arbitrary mere existence.

## Concrete composition through the final meet

`PowersetAtomicExpression.For X` instantiates the template with the previous weighted-supremum relation and actual implication. The inner relation is the relative-supremum specification of the actual inner image, with its already checked finite reading; it is not an assumed recursive atomic graph.

For fixed internal C, x, y and H it builds:

    left inner at u = sup { c ∩ d | pair(v,c) in y, pair(pair(u,v),d) in H },
    right inner at v = sup { a ∩ d | pair(u,a) in x, pair(pair(u,v),d) in H },
    left outer = { a ⇒ j | pair(u,a) in x, j satisfies the left inner specification },
    right outer = { c ⇒ k | pair(v,c) in y, k satisfies the right inner specification },
    value = inf(left outer) ∩ inf(right outer).

These displayed images retain the coded bounds from the probe: variable name coordinates lie in C; input weights, table values, inner candidates and image outputs lie in B. They are actual internal sets. In particular, the two recursive-key presentations both read H(u,v); the second does not exchange the arguments of H.

Each branch returns an actual infimum with its full relative-infimum specification. The final intersection is an actual member of B. For every typed outer entry, `Entry.implication-in-image` inserts the implication of its actual computed inner value into the outer image. Together with implication closure, this proves the output B guard does not discard those genuine results.

The concrete congruence proof takes graph agreement for the relevant pairs. It uses the shared inner-image equality, transports each fixed-candidate supremum specification across that equality, applies outer-image congruence, then applies congruence of the actual infimum construction. The same proof serves both key orientations. It does not duplicate supremum uniqueness or assume a host-complete algebra.

## What this does and does not close

This closes the concrete expression-construction check through inner joins, outer implication images, both infima and the final meet, under the existing LEM hypothesis. It also supplies branch locality for the fixed internal domain and explicit graph-agreement inputs.

It does not yet prove a single complete finite Step formula and its equivalence with this expression, the required Step uniqueness/admissibility interface, or the composition of both branch localities with the recursion engine's exact predecessor assumptions. The displayed outer sets use a supremum specification; the canonical-value insertion is proved, but reducing every candidate to the canonical value still requires the uniqueness adapter when needed. No complete atomic table instance, closed-domain independence or atomic equality/membership adequacy is claimed.

Next work:

1. Give the outer image a variable-indexed image-set description, reusing a shared set-description combinator where possible rather than copying the earlier inner-image proof.
2. Compose that description, reversed-order extremum syntax and the meet formula into one Step formula. Prove exact reading and unique output using the established unique-fiber machinery.
3. Adapt the two branch graph-agreement inputs to actual name-pair predecessor coverage/value agreement, then instantiate bounded table recursion.
4. Prove closed-domain independence and atomic adequacy; continue the general algebra/RO compiler and forcing program without substituting this powerset instance for the Cohen algebra.

The full Boolean laws and general regular-open completion remain separate obligations. General-ground portability and the final no-host-choice budget remain under audit. The general forcing requirement, T3 actual ordinary non-CH model, and T4 ground definability remain unchanged.

## Verification and source snapshots

From `/tmp/bedrock-k0-probes/extraction/compile-root`:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/InternalPowersetImplication.agda
GHCRTS="-A64m -I0 -M8g" agda src/InternalPowersetInfimum.agda
GHCRTS="-A64m -I0 -M8g" agda src/OuterWeightedImage.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicExpression.agda
```

All exited 0; the final expression check also checked the outer image after its congruence addition. All four files retain `--safe`. Scoped prose/glossary gates, snapshot/hash and local-link checks, and `git diff --check` passed. All 123 tracked production source files and the copied probe-baseline versions match `c45bc015` byte-for-byte. No whole-tree or chapter gate was run for this documentation and temporary-probe change.

### InternalPowersetImplication.agda

SHA-256: `24245f8f9020ecdb2b00d365106d0f6255a21fe5bde25ca89a709414ae32f4eb`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module InternalPowersetImplication {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ∀̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
import InternalIntersection {ℓ} lem as Intersections
import InternalPowersetSupremum {ℓ} lem as Powersets
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module Ground = Powersets.Ground

implication : S → S → S → S
implication X c d = Ground.separate X
  ((var zero ∈̇ con c) ⇒̇ (var zero ∈̇ con d))

implication-membership : ∀ X c d z
  → (z ∈ˢ implication X c d)
    ≡ ((z ∈ˢ X) ⊓ ((z ∈ˢ c) ⇒ (z ∈ˢ d)))
implication-membership X c d z = Ground.separate-spec X
  ((var zero ∈̇ con c) ⇒̇ (var zero ∈̇ con d)) z

implication-out : ∀ X c d z → ⟨ z ∈ˢ implication X c d ⟩
  → ⟨ z ∈ˢ X ⟩ × (⟨ z ∈ˢ c ⟩ → ⟨ z ∈ˢ d ⟩)
implication-out X c d z member = subst ⟨_⟩
  (implication-membership X c d z) member

implication-in : ∀ X c d z → ⟨ z ∈ˢ X ⟩
  → (⟨ z ∈ˢ c ⟩ → ⟨ z ∈ˢ d ⟩)
  → ⟨ z ∈ˢ implication X c d ⟩
implication-in X c d z zX sends = subst ⟨_⟩
  (sym (implication-membership X c d z)) (zX , sends)

Op : S → S → S → S → hProp (ℓ-suc ℓ)
Op X c d z = (z ≡ implication X c d) , isSetS z (implication X c d)

implicationAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
implicationAt X c d z = ∀̇
  (((var zero ∈̇ var (suc z)) ⇒̇
      ((var zero ∈̇ var (suc X)) ∧̇
       ((var zero ∈̇ var (suc c)) ⇒̇ (var zero ∈̇ var (suc d))))) ∧̇
   (((var zero ∈̇ var (suc X)) ∧̇
      ((var zero ∈̇ var (suc c)) ⇒̇ (var zero ∈̇ var (suc d)))) ⇒̇
     (var zero ∈̇ var (suc z))))

implication-reading : ∀ {n} (X c d z : Fin n) (γ : Vec S n)
  → (γ ⊨ implicationAt X c d z)
    ≡ Op (lookup X γ) (lookup c γ) (lookup d γ) (lookup z γ)
implication-reading X c d z γ = ⇔toPath out into
  where
  out : ⟨ γ ⊨ implicationAt X c d z ⟩
    → lookup z γ ≡ implication (lookup X γ) (lookup c γ) (lookup d γ)
  out holds = Ground.extensional λ w → ⇔toPath
    (λ member → implication-in (lookup X γ) (lookup c γ) (lookup d γ) w
      (fst (fst (holds w) member)) (snd (fst (holds w) member)))
    (λ member → snd (holds w)
      (fst (implication-out (lookup X γ) (lookup c γ) (lookup d γ) w member) ,
       snd (implication-out (lookup X γ) (lookup c γ) (lookup d γ) w member)))

  into : lookup z γ ≡ implication (lookup X γ) (lookup c γ) (lookup d γ)
    → ⟨ γ ⊨ implicationAt X c d z ⟩
  into eq w =
    (λ member → implication-out (lookup X γ) (lookup c γ) (lookup d γ) w
      (subst (λ a → ⟨ w ∈ˢ a ⟩) eq member)) ,
    (λ { (wX , sends) → subst (λ a → ⟨ w ∈ˢ a ⟩) (sym eq)
      (implication-in (lookup X γ) (lookup c γ) (lookup d γ) w wX sends) })

implication-bounded : ∀ X c d
  → ⟨ implication X c d ∈ˢ Powersets.For.B X ⟩
implication-bounded X c d = subst ⟨_⟩
  (sym (Model.℩-spec 𝒮ʟ (Ground.hasPower X) (implication X c d))) subset
  where
  subset : ⟨ Model._⊆ˢ_ 𝒮ʟ (implication X c d) X ⟩
  subset z member = fst (implication-out X c d z member)

adjunction : ∀ X a c d → ⟨ Model._⊆ˢ_ 𝒮ʟ a X ⟩
  → (⟨ Model._⊆ˢ_ 𝒮ʟ a (implication X c d) ⟩
      → ⟨ Model._⊆ˢ_ 𝒮ʟ (Intersections.intersection a c) d ⟩)
    × (⟨ Model._⊆ˢ_ 𝒮ʟ (Intersections.intersection a c) d ⟩
      → ⟨ Model._⊆ˢ_ 𝒮ʟ a (implication X c d) ⟩)
adjunction X a c d aX = forward , backward
  where
  forward : ⟨ Model._⊆ˢ_ 𝒮ʟ a (implication X c d) ⟩
    → ⟨ Model._⊆ˢ_ 𝒮ʟ (Intersections.intersection a c) d ⟩
  forward subset z member = snd (implication-out X c d z
    (subset z (fst (Intersections.intersection-out z a c member))))
    (snd (Intersections.intersection-out z a c member))

  backward : ⟨ Model._⊆ˢ_ 𝒮ʟ (Intersections.intersection a c) d ⟩
    → ⟨ Model._⊆ˢ_ 𝒮ʟ a (implication X c d) ⟩
  backward subset z za = implication-in X c d z (aX z za)
    (λ zc → subset z (Intersections.intersection-in z a c za zc))
```

### InternalPowersetInfimum.agda

SHA-256: `217bad5846448a209604a5789f97765338a0f09896cdc33e319005edde9bfdff`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module InternalPowersetInfimum {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ∀̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
import InternalPowersetSupremum {ℓ} lem as Powerset
import IndexedSupremum {ℓ} as Indexed
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module Ground = Powerset.Ground

module For (X : S) where

  module PowersetOf = Powerset.For X

  B : S
  B = PowersetOf.B

  Order : S → S → hProp (ℓ-suc ℓ)
  Order A C = PowersetOf.Order C A

  orderAt : ∀ {n} → Fin n → Fin n → Formula S n
  orderAt A C = PowersetOf.orderAt C A

  order-reading : ∀ {n} (A C : Fin n) (γ : Vec S n)
    → (γ ⊨ orderAt A C) ≡ Order (lookup A γ) (lookup C γ)
  order-reading A C γ = PowersetOf.order-reading C A γ

  module Infimum = Indexed.WithOrder Order orderAt order-reading

  infimumFormula : S → Formula S 1
  infimumFormula A = ∀̇∈ (con A) (var (suc zero) ∈̇ var zero)

  infimum : S → S
  infimum A = Ground.separate X (infimumFormula A)

  infimum-membership : ∀ w A
    → (w ∈ˢ infimum A)
      ≡ ((w ∈ˢ X) ⊓ (((a : S) → ⟨ a ∈ˢ A ⟩ → ⟨ w ∈ˢ a ⟩) ,
        isPropΠ (λ a → isPropΠ (λ _ → snd (w ∈ˢ a)))))
  infimum-membership w A = Ground.separate-spec X (infimumFormula A) w

  infimum-correct : (A : S) → Infimum.Supremum B A (infimum A)
  infimum-correct A = in-B , is-lower , greatest
    where
    power-spec = Model.℩-spec 𝒮ʟ (Ground.hasPower X)

    subset-X : (w : S) → ⟨ w ∈ˢ infimum A ⟩ → ⟨ w ∈ˢ X ⟩
    subset-X w member = fst (subst ⟨_⟩ (infimum-membership w A) member)

    in-B : ⟨ infimum A ∈ˢ B ⟩
    in-B = subst ⟨_⟩ (sym (power-spec (infimum A))) subset-X

    is-lower : Infimum.Upper A (infimum A)
    is-lower a aA w member = snd
      (subst ⟨_⟩ (infimum-membership w A) member) a aA

    greatest : (C : S) → ⟨ C ∈ˢ B ⟩ → Infimum.Upper A C
      → ⟨ Order (infimum A) C ⟩
    greatest C C-in-B is-lower w member = subst ⟨_⟩
      (sym (infimum-membership w A))
      (subst ⟨_⟩ (power-spec C) C-in-B w member ,
       λ a aA → is-lower a aA w member)

  empty-family-infimum : infimum Ground.∅ ≡ X
  empty-family-infimum = Ground.extensional λ w → ⇔toPath
    (λ member → fst (subst ⟨_⟩ (infimum-membership w Ground.∅) member))
    (λ member → subst ⟨_⟩ (sym (infimum-membership w Ground.∅))
      (member , λ a a-empty → Empty.rec*
        (subst ⟨_⟩ (Ground.hasEmpty .fst .snd a) a-empty)))

  infimumAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  infimumAt B A b = Infimum.supremumAt B A b

  infimum-reading : ∀ {n} (B A b : Fin n) (γ : Vec S n)
    → (γ ⊨ infimumAt B A b)
      ≡ (Infimum.Supremum (lookup B γ) (lookup A γ) (lookup b γ) ,
        Infimum.supremum-is-prop (lookup B γ) (lookup A γ) (lookup b γ))
  infimum-reading B A b γ = Infimum.supremum-reading B A b γ
```

### OuterWeightedImage.agda

SHA-256: `d771785ddb229a583d46c6538920e366b8b77e8956fb74cc6d086faa829977b8`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module OuterWeightedImage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
open import CodedTableFunctionality {ℓ} using ( entryAt; entry-reading )
open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( specialize; specialize-reading )
import InternalPowersetSupremum {ℓ} lem as Powersets
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Ground = Powersets.Ground

shiftThree : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
shiftThree i = suc (suc (suc i))

module WithInner
  (Inner : S → S → S → S → S → S → hProp (ℓ-suc ℓ))
  (innerAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (inner-reading : ∀ {n} (C B parent H f j : Fin n) (γ : Vec S n)
    → (γ ⊨ innerAt C B parent H f j)
      ≡ Inner (lookup C γ) (lookup B γ) (lookup parent γ) (lookup H γ) (lookup f γ) (lookup j γ)) where

  module WithOperation
    (Op : S → S → S → S → hProp (ℓ-suc ℓ))
    (opAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
    (op-reading : ∀ {n} (X a j z : Fin n) (γ : Vec S n)
      → (γ ⊨ opAt X a j z) ≡ Op (lookup X γ) (lookup a γ) (lookup j γ) (lookup z γ)) where

    imageAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
    imageAt X C B outer inner H z = ∃̇∈ (var C) (∃̇∈ (var (suc B))
      (∃̇∈ (var (suc (suc B)))
        (entryAt (shiftThree outer) (suc (suc zero)) (suc zero) ∧̇
        (innerAt (shiftThree C) (shiftThree B) (shiftThree inner) (shiftThree H)
          (suc (suc zero)) zero ∧̇ opAt (shiftThree X) (suc zero) zero (shiftThree z)))))

    Witness : S → S → S → S → S → S → S → Type (ℓ-suc ℓ)
    Witness X C B outer inner H z = ∥ Σ[ u ∈ S ] Σ[ a ∈ S ] Σ[ j ∈ S ]
      (⟨ u ∈ˢ C ⟩ × ⟨ a ∈ˢ B ⟩ × ⟨ j ∈ˢ B ⟩ × ⟨ prʟ u a ∈ˢ outer ⟩
        × ⟨ Inner C B inner H u j ⟩ × ⟨ Op X a j z ⟩) ∥₁

    out : ∀ {n} (X C B outer inner H z : Fin n) (γ : Vec S n)
      → ⟨ γ ⊨ imageAt X C B outer inner H z ⟩
      → Witness (lookup X γ) (lookup C γ) (lookup B γ) (lookup outer γ)
          (lookup inner γ) (lookup H γ) (lookup z γ)
    out X C B outer inner H z γ = PT.rec PT.squash₁ λ { (u , uC , rest) →
      PT.rec PT.squash₁ (λ { (a , aB , rest) → PT.map
        (λ { (j , jB , entry , val , op) → u , a , j , uC , aB , jB ,
          subst ⟨_⟩ (entry-reading (shiftThree outer) (suc (suc zero)) (suc zero)
            (j ∷ a ∷ u ∷ γ)) entry ,
          subst ⟨_⟩ (inner-reading (shiftThree C) (shiftThree B) (shiftThree inner)
            (shiftThree H) (suc (suc zero)) zero (j ∷ a ∷ u ∷ γ)) val ,
          subst ⟨_⟩ (op-reading (shiftThree X) (suc zero) zero (shiftThree z)
            (j ∷ a ∷ u ∷ γ)) op }) rest }) rest }

    into : ∀ {n} (X C B outer inner H z : Fin n) (γ : Vec S n)
      → Witness (lookup X γ) (lookup C γ) (lookup B γ) (lookup outer γ)
          (lookup inner γ) (lookup H γ) (lookup z γ)
      → ⟨ γ ⊨ imageAt X C B outer inner H z ⟩
    into X C B outer inner H z γ = PT.map λ { (u , a , j , uC , aB , jB , entry , val , op) →
      u , uC , ∣ a , aB , ∣ j , jB ,
        subst ⟨_⟩ (sym (entry-reading (shiftThree outer) (suc (suc zero)) (suc zero)
          (j ∷ a ∷ u ∷ γ))) entry ,
        subst ⟨_⟩ (sym (inner-reading (shiftThree C) (shiftThree B) (shiftThree inner)
          (shiftThree H) (suc (suc zero)) zero (j ∷ a ∷ u ∷ γ))) val ,
        subst ⟨_⟩ (sym (op-reading (shiftThree X) (suc zero) zero (shiftThree z)
          (j ∷ a ∷ u ∷ γ))) op ∣₁ ∣₁ }

    image-reading : ∀ {n} (X C B outer inner H z : Fin n) (γ : Vec S n)
      → (γ ⊨ imageAt X C B outer inner H z)
        ≡ (Witness (lookup X γ) (lookup C γ) (lookup B γ) (lookup outer γ)
          (lookup inner γ) (lookup H γ) (lookup z γ) , PT.squash₁)
    image-reading X C B outer inner H z γ = ⇔toPath
      (out X C B outer inner H z γ) (into X C B outer inner H z γ)

    template : Formula S 7
    template = imageAt zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
      (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc (suc (suc zero))))))

    module Construction (X C B outer inner H : S) where

      parameters : Vec S 6
      parameters = X ∷ C ∷ B ∷ outer ∷ inner ∷ H ∷ []

      formula : Formula S 1
      formula = specialize parameters template

      formula-reading : ∀ z → ((z ∷ []) ⊨ formula)
        ≡ (Witness X C B outer inner H z , PT.squash₁)
      formula-reading z = specialize-reading parameters template z ∙
        image-reading zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
          (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc (suc (suc (suc zero))))))
          (X ∷ C ∷ B ∷ outer ∷ inner ∷ H ∷ z ∷ [])

      image : S
      image = Ground.separate B formula

      separated : ∀ z → ⟨ z ∈ˢ image ⟩ → ⟨ z ∈ˢ B ⟩ × ⟨ (z ∷ []) ⊨ formula ⟩
      separated z member = subst ⟨_⟩ (Ground.separate-spec B formula z) member

      image-out : ∀ z → ⟨ z ∈ˢ image ⟩ → ⟨ z ∈ˢ B ⟩ × Witness X C B outer inner H z
      image-out z member = fst (separated z member) ,
        subst ⟨_⟩ (formula-reading z) (snd (separated z member))

      image-in : ∀ z → ⟨ z ∈ˢ B ⟩ → Witness X C B outer inner H z → ⟨ z ∈ˢ image ⟩
      image-in z zB witness = subst ⟨_⟩ (sym (Ground.separate-spec B formula z))
        (zB , subst ⟨_⟩ (sym (formula-reading z)) witness)

    module Congruence (X C B outer inner H K : S)
      (agrees : ∀ u a j → ⟨ u ∈ˢ C ⟩ → ⟨ a ∈ˢ B ⟩ → ⟨ j ∈ˢ B ⟩
        → ⟨ prʟ u a ∈ˢ outer ⟩
        → (⟨ Inner C B inner H u j ⟩ → ⟨ Inner C B inner K u j ⟩)
          × (⟨ Inner C B inner K u j ⟩ → ⟨ Inner C B inner H u j ⟩)) where

      module Left = Construction X C B outer inner H
      module Right = Construction X C B outer inner K

      forward : ∀ z → ⟨ z ∈ˢ Left.image ⟩ → ⟨ z ∈ˢ Right.image ⟩
      forward z member = Right.image-in z (fst (Left.image-out z member))
        (PT.map (λ { (u , a , j , uC , aB , jB , entry , val , op) →
          u , a , j , uC , aB , jB , entry , fst (agrees u a j uC aB jB entry) val , op })
          (snd (Left.image-out z member)))

      backward : ∀ z → ⟨ z ∈ˢ Right.image ⟩ → ⟨ z ∈ˢ Left.image ⟩
      backward z member = Left.image-in z (fst (Right.image-out z member))
        (PT.map (λ { (u , a , j , uC , aB , jB , entry , val , op) →
          u , a , j , uC , aB , jB , entry , snd (agrees u a j uC aB jB entry) val , op })
          (snd (Right.image-out z member)))

      image-equal : Left.image ≡ Right.image
      image-equal = Ground.extensional (λ z → ⇔toPath (forward z) (backward z))
```

### PowersetAtomicExpression.agda

SHA-256: `fc4f3ef8b9abfc1b67dc3728f1309331a28ec0065d603e03ff95ff20dfa6848f`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicExpression {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL )
open import PairFormulaReading {ℓ} using ( reading )
import IndexedWeightedImage {ℓ} as Keys
import PowersetWeightedSupremum {ℓ} lem as Weighted
import InternalPowersetSupremum {ℓ} lem as Powersets
import InternalPowersetImplication {ℓ} lem as Implication
import InternalPowersetInfimum {ℓ} lem as Infima
import InternalIntersection {ℓ} lem as Intersection
import OuterWeightedImage {ℓ} lem as Outer
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module For (X : S) where

  module Algebra = Powersets.For X
  module InnerValues = Weighted.For X
  module Bounds = Infima.For X
  open Algebra using ( B )

  module WithKey
    (Key : S → S → S)
    (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    (key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
      → (γ ⊨ keyAt q f v) ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
        isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ)))) where

    module Values = InnerValues.WithKey Key keyAt key-reading

    Inner : S → S → S → S → S → S → hProp (ℓ-suc ℓ)
    Inner C D parent H f j =
      Values.Result.Sup.Supremum D (Image.image) j ,
      Values.Result.Sup.supremum-is-prop D Image.image j
      where
      module Image = Values.Operations.Image.Construction C D parent H f

    inner-reading : ∀ {n} (C D parent H f j : Fin n) (γ : Vec S n)
      → (γ ⊨ Values.Result.resultAt C D parent H f j)
        ≡ Inner (lookup C γ) (lookup D γ) (lookup parent γ) (lookup H γ) (lookup f γ) (lookup j γ)
    inner-reading = Values.Result.Reading.exact

    module Images = Outer.WithInner.WithOperation Inner Values.Result.resultAt inner-reading
      Implication.Op Implication.implicationAt Implication.implication-reading

    module Construction (C outer inner H : S) where

      module Image = Images.Construction X C B outer inner H

      value : S
      value = Bounds.infimum Image.image

      correct : Bounds.Infimum.Supremum B Image.image value
      correct = Bounds.infimum-correct Image.image

      value-in-B : ⟨ value ∈ˢ B ⟩
      value-in-B = fst correct

      module Entry (u a : S) (uC : ⟨ u ∈ˢ C ⟩) (aB : ⟨ a ∈ˢ B ⟩)
        (entry : ⟨ prʟ u a ∈ˢ outer ⟩) where

        module InnerValue = Values.Construction C inner H u

        implication-in-image : ⟨ Implication.implication X a InnerValue.value ∈ˢ Image.image ⟩
        implication-in-image = Image.image-in (Implication.implication X a InnerValue.value)
          (Implication.implication-bounded X a InnerValue.value)
          ∣ u , a , InnerValue.value , uC , aB , InnerValue.value-in-B , entry ,
            InnerValue.correct , refl ∣₁

    module Congruence (C outer inner H K : S)
      (agrees : ∀ u a → ⟨ u ∈ˢ C ⟩ → ⟨ a ∈ˢ B ⟩ → ⟨ prʟ u a ∈ˢ outer ⟩
        → ∀ v c d → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
        → ⟨ prʟ v c ∈ˢ inner ⟩
        → (⟨ prʟ (Key u v) d ∈ˢ H ⟩ → ⟨ prʟ (Key u v) d ∈ˢ K ⟩)
          × (⟨ prʟ (Key u v) d ∈ˢ K ⟩ → ⟨ prʟ (Key u v) d ∈ˢ H ⟩)) where

      inner-agreement : ∀ u a j → ⟨ u ∈ˢ C ⟩ → ⟨ a ∈ˢ B ⟩ → ⟨ j ∈ˢ B ⟩
        → ⟨ prʟ u a ∈ˢ outer ⟩
        → (⟨ Inner C B inner H u j ⟩ → ⟨ Inner C B inner K u j ⟩)
          × (⟨ Inner C B inner K u j ⟩ → ⟨ Inner C B inner H u j ⟩)
      inner-agreement u a j uC aB jB entry =
        subst (λ A → Values.Result.Sup.Supremum B A j) Comparison.image-equal ,
        subst (λ A → Values.Result.Sup.Supremum B A j) (sym Comparison.image-equal)
        where
        module Comparison = Values.Operations.Image.Congruence C B inner H K u
          (agrees u a uC aB entry)

      module Left = Construction C outer inner H
      module Right = Construction C outer inner K
      module ImageEquality = Images.Congruence X C B outer inner H K inner-agreement

      value-equal : Left.value ≡ Right.value
      value-equal = cong Bounds.infimum ImageEquality.image-equal

  module Forward = WithKey prʟ prAtL reading
  module Reverse = WithKey (λ f v → prʟ v f) Keys.reverseKeyAt Keys.reverse-key-reading

  module Expression (C x y H : S) where

    module Left = Forward.Construction C x y H
    module Right = Reverse.Construction C y x H

    value : S
    value = Intersection.intersection Left.value Right.value

    value-in-B : ⟨ value ∈ˢ B ⟩
    value-in-B = InnerValues.meet-bounded Left.value Right.value Left.value-in-B
```
