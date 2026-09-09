# K0 finite powerset Step and predecessor locality

Date: 2026-09-09. Source baseline: `7eccc1f6`. Four new safe probes and a generalized parameter-substitution probe checked; the existing unique-value core is reused unchanged. This continues the [outer weighted expression](k0-outer-weighted-expression-2026-09.md). K0 remains open.

## Shared formula and uniqueness components

`FormulaParameters` now supports `instantiate`: substitute n actual parameters while retaining any m free variables. Its reading theorem holds at any remaining environment. The former one-free-variable `specialize` API is derived from this implementation, so there is one substitution proof home. Substitution introduces neither quantifiers nor logical assumptions and remains parameterized by a general truth algebra and structure. The checked Step uses it to freeze X and B while retaining variable coordinates and table/output arguments.

`SetDescription` takes a bound B and an arbitrary formula body under one extra variable. It forms the finite statement that I has exactly those B-members satisfying the body. Given an actual internal set and its exact membership theorem, the shared reading proof identifies that statement with literal equality to the set. The outer-image adapter now reuses this component rather than copying the earlier inner-image extensionality proof. Production consolidation should also use the component for inner images; historical probe snapshots retain their original proofs.

`RelativeSupremumUniqueness` adapts an actual bounded family A ⊆ B to the existing `UniqueValue` core: indices are members of A, values are members of B, and the relation is the supplied order. Antisymmetry is required only on B-elements. Each relative-supremum specification gives a core result, and `Unique.result-is-prop` identifies any two such results. This reuses the existing proof rather than proving a second extremum uniqueness lemma. The adapter needs no LEM or Choice and does not construct a supremum from nothing. The copied `UniqueValue.agda` is byte-for-byte identical to the earlier source.

## A single finite Step formula

`PowersetStepFormula.For X` fixes the actual internal powerset B and supplies `stepAt C x y H b`, with five variable indices. For each key orientation:

1. A variable-indexed outer image-set description uses `SetDescription` and the actual outer-image membership theorem.
2. A finite existential quantifies the image set and asserts its relative-infimum specification, using the existing reversed-order syntax.
3. Uniqueness over the actual B-bounded image identifies any candidate infimum with the constructed branch value.
4. Parameter substitution freezes X and B, leaving C, the two parents, H and the branch output variable.

The final Step formula existentially quantifies the two branch outputs in B and uses the checked meet formula for their intersection. `Reading.exact` proves at arbitrary environments that it holds exactly when the supplied output is literally equal to the previously constructed expression value. No atomic equality graph, generic filter, Boolean ultrafilter, recursive table or arbitrary host-complete algebra appears as an assumption in this construction.

The corresponding semantic `Step C x y H b` is equality to that expression. Its named laws are checked:

- `step-reading`: the single finite formula has precisely this meaning.
- `unique`: any two outputs satisfying Step are equal.
- `admit`: an actual output in B with its Step proof is returned for any actual C, x, y and H.

Admission is explicit, not merely a selected witness under a new axiom: all images, joins, implications, infima and the final meet have already been constructed internally. It remains meaningful even for a partial table H because these nonrecursive image operations are defined for arbitrary internal H. This alone does not show that such H satisfies recursive equations or that a recursion table exists.

## Locality from actual predecessor assumptions

`PowersetStepLocality.For X.Tables C H K x y xC yC` reuses the existing actual name-pair predecessor interface. Given predecessor coverage of H and K and cross-table value agreement (`Same`), it obtains relevant graph agreement through the previously proved proposition-valued graph transfer.

For the forward outer entry pair(u,a) in x and inner entry pair(v,c) in y, the two entry witnesses supply Child(u,x) and Child(v,y). The reverse branch supplies the same children in the corresponding positions. Both applications read H(u,v), including the reverse branch. No symmetry theorem for Boolean equality is assumed.

The adapter instantiates the two existing branch congruences, then applies congruence of intersection to prove equality of the full expression values. `PowersetStepFormula.Tables.Agreement.transfer` turns this equality into preservation of Step satisfaction. Thus the raw coordinate-level Step now has exact finite syntax, uniqueness, admission and predecessor-based locality, not only separate branch-locality evidence.

## Remaining integration boundary

The checked recursion engine expects a three-argument Step on an encoded key p, whereas this theorem exposes the raw coordinate form with fixed X and variable C, x, y, H, b. The next adapter must freeze the internal domain C, decode or existentially describe p = pair(x,y), and transport the exact membership/typing and predecessor contracts to that engine. That pair-key syntax/reading adapter and a complete actual recursion-table instance are not yet proved. The already checked generic bounded recursion kernel is unchanged.

Next work:

1. Build the pair-key Step formula using the existing product decoder and pair reading; prove its exact semantic reading on the actual domain C × C.
2. Adapt the checked uniqueness, admission and locality laws to the bounded engine's precise arguments; instantiate the existing name-pair recursion interface rather than reprove recursion.
3. Prove closed-domain independence and atomic equality/membership adequacy.
4. Continue full Boolean instance validation and general regular-open completion. The powerset instance still does not replace the Cohen algebra or the required general forcing framework.

The generic formula machinery is independent of the powerset example. The L realization and locality adapter retain exactly `LEM (ℓ-suc ℓ)`, and no host AC, countable/dependent choice, BPI, ultrafilter axiom, selector or resizing premise is added. General-ground portability and the final endpoint assumption budget remain under audit. T3 remains an actual ordinary non-CH model after general forcing results; T4 remains ground definability.

## Verification and source snapshots

From `/tmp/bedrock-k0-probes/extraction/compile-root`, these checks exited 0:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/SetDescription.agda
GHCRTS="-A64m -I0 -M8g" agda src/RelativeSupremumUniqueness.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetStepLocality.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetStepFormula.agda
```

The final Step check includes its locality transfer and imports the generalized parameter substitution, reused unique-value core, and affected image/expression consumers. All archived source files retain `--safe`. Scoped prose/glossary gates, snapshot/hash and local-link checks, and `git diff --check` passed. All 123 tracked production source files and copied probe-baseline versions match `7eccc1f6` byte-for-byte. No production source changed; whole-tree and chapter gates were not run for this temporary-probe/documentation change.

### FormulaParameters.agda

SHA-256: `13c29ed4d3cdc93345f3c29171f32dac284b45b3f88ce0dc7c8da097e0c83ac3`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module FormulaParameters {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ')
                         (𝒮 : ZFStructure 𝕋) where

open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _++_ )

open TruthAlgebra 𝕋
open ZFStructure 𝒮

private module Sem = FOL.Semantics 𝕋 𝒮
open Sem using ( _^_ )
open Sem.At S id using ( _⊨_; ⟦_⟧ )

renameTerm : ∀ {n m} → (Fin n → Fin m) → Term S n → Term S m
renameTerm ρ (con x) = con x
renameTerm ρ (var i) = var (ρ i)

liftTerms : ∀ {n m} → (Fin n → Term S m) → Fin (suc n) → Term S (suc m)
liftTerms σ zero    = var zero
liftTerms σ (suc i) = renameTerm suc (σ i)

substituteTerm : ∀ {n m} → (Fin n → Term S m) → Term S n → Term S m
substituteTerm σ (con x) = con x
substituteTerm σ (var i) = σ i

substitute : ∀ {n m} → (Fin n → Term S m) → Formula S n → Formula S m
substitute σ (t ∈̇ u)  = substituteTerm σ t ∈̇ substituteTerm σ u
substitute σ (t ≐ u)  = substituteTerm σ t ≐ substituteTerm σ u
substitute σ (φ ∧̇ ψ)  = substitute σ φ ∧̇ substitute σ ψ
substitute σ (φ ∨̇ ψ)  = substitute σ φ ∨̇ substitute σ ψ
substitute σ (φ ⇒̇ ψ)  = substitute σ φ ⇒̇ substitute σ ψ
substitute σ ⊥̇        = ⊥̇
substitute σ (∃̇ φ)    = ∃̇ substitute (liftTerms σ) φ
substitute σ (∀̇ φ)    = ∀̇ substitute (liftTerms σ) φ
substitute σ (∀̇∈ t φ) = ∀̇∈ (substituteTerm σ t) (substitute (liftTerms σ) φ)
substitute σ (∃̇∈ t φ) = ∃̇∈ (substituteTerm σ t) (substitute (liftTerms σ) φ)

private
  ⟦⟧-rename-suc : ∀ {n} (t : Term S n) (x : S) (γ : S ^ n)
                → ⟦ renameTerm suc t ⟧ (x ∷ γ) ≡ ⟦ t ⟧ γ
  ⟦⟧-rename-suc (con y) x γ = refl
  ⟦⟧-rename-suc (var i) x γ = refl

  Agreement : ∀ {n m} → (Fin n → Term S m) → S ^ m → S ^ n → Type ℓ
  Agreement σ γ δ = ∀ i → ⟦ σ i ⟧ γ ≡ lookup i δ

  lift-agreement : ∀ {n m} {σ : Fin n → Term S m} {γ : S ^ m} {δ : S ^ n}
                   (x : S) → Agreement σ γ δ
                 → Agreement (liftTerms σ) (x ∷ γ) (x ∷ δ)
  lift-agreement x ag zero    = refl
  lift-agreement {σ = σ} {γ = γ} x ag (suc i) =
    ⟦⟧-rename-suc (σ i) x γ ∙ ag i

  ⟦⟧-substitute : ∀ {n m} (σ : Fin n → Term S m) (t : Term S n)
                  (γ : S ^ m) (δ : S ^ n) → Agreement σ γ δ
                → ⟦ substituteTerm σ t ⟧ γ ≡ ⟦ t ⟧ δ
  ⟦⟧-substitute σ (con x) γ δ ag = refl
  ⟦⟧-substitute σ (var i) γ δ ag = ag i

  ⊨-substitute : ∀ {n m} (σ : Fin n → Term S m) (φ : Formula S n)
                 (γ : S ^ m) (δ : S ^ n) → Agreement σ γ δ
               → (γ ⊨ substitute σ φ) ≡ (δ ⊨ φ)
  ⊨-substitute σ (t ∈̇ u) γ δ ag = cong₂ _∈ˢ_
    (⟦⟧-substitute σ t γ δ ag) (⟦⟧-substitute σ u γ δ ag)
  ⊨-substitute σ (t ≐ u) γ δ ag = cong₂ _≈ˢ_
    (⟦⟧-substitute σ t γ δ ag) (⟦⟧-substitute σ u γ δ ag)
  ⊨-substitute σ (φ ∧̇ ψ) γ δ ag = cong₂ _⊓_
    (⊨-substitute σ φ γ δ ag) (⊨-substitute σ ψ γ δ ag)
  ⊨-substitute σ (φ ∨̇ ψ) γ δ ag = cong₂ _⊔_
    (⊨-substitute σ φ γ δ ag) (⊨-substitute σ ψ γ δ ag)
  ⊨-substitute σ (φ ⇒̇ ψ) γ δ ag = cong₂ _⇒_
    (⊨-substitute σ φ γ δ ag) (⊨-substitute σ ψ γ δ ag)
  ⊨-substitute σ ⊥̇ γ δ ag = refl
  ⊨-substitute σ (∃̇ φ) γ δ ag = cong (⋁ S) (funExt (λ x →
    ⊨-substitute (liftTerms σ) φ (x ∷ γ) (x ∷ δ) (lift-agreement x ag)))
  ⊨-substitute σ (∀̇ φ) γ δ ag = cong (⋀ S) (funExt (λ x →
    ⊨-substitute (liftTerms σ) φ (x ∷ γ) (x ∷ δ) (lift-agreement x ag)))
  ⊨-substitute σ (∀̇∈ t φ) γ δ ag = cong (⋀ S) (funExt (λ x → cong₂ _⇒_
    (cong (x ∈ˢ_) (⟦⟧-substitute σ t γ δ ag))
    (⊨-substitute (liftTerms σ) φ (x ∷ γ) (x ∷ δ) (lift-agreement x ag))))
  ⊨-substitute σ (∃̇∈ t φ) γ δ ag = cong (⋁ S) (funExt (λ x → cong₂ _⊓_
    (cong (x ∈ˢ_) (⟦⟧-substitute σ t γ δ ag))
    (⊨-substitute (liftTerms σ) φ (x ∷ γ) (x ∷ δ) (lift-agreement x ag))))

parametersWith : ∀ {n m} → Vec S n → Fin (n + m) → Term S m
parametersWith [] i = var i
parametersWith (x ∷ δ) zero = con x
parametersWith (x ∷ δ) (suc i) = parametersWith δ i

instantiate : ∀ {n m} → Vec S n → Formula S (n + m) → Formula S m
instantiate δ = substitute (parametersWith δ)

private
  parametersWith-agree : ∀ {n m} (δ : Vec S n) (γ : Vec S m) (i : Fin (n + m))
    → ⟦ parametersWith δ i ⟧ γ ≡ lookup i (δ ++ γ)
  parametersWith-agree [] γ i = refl
  parametersWith-agree (x ∷ δ) γ zero = refl
  parametersWith-agree (x ∷ δ) γ (suc i) = parametersWith-agree δ γ i

instantiate-reading : ∀ {n m} (δ : Vec S n) (φ : Formula S (n + m)) (γ : Vec S m)
  → (γ ⊨ instantiate δ φ) ≡ ((δ ++ γ) ⊨ φ)
instantiate-reading δ φ γ = ⊨-substitute (parametersWith δ) φ γ (δ ++ γ)
  (parametersWith-agree δ γ)

parameters : ∀ {n} → Vec S n → Fin (n + 1) → Term S 1
parameters = parametersWith

specialize : ∀ {n} → Vec S n → Formula S (n + 1) → Formula S 1
specialize = instantiate

specialize-reading : ∀ {n} (δ : Vec S n) (φ : Formula S (n + 1)) (z : S)
  → ((z ∷ []) ⊨ specialize δ φ) ≡ ((δ ++ (z ∷ [])) ⊨ φ)
specialize-reading δ φ z = instantiate-reading δ φ (z ∷ [])
```

### SetDescription.agda

SHA-256: `1d87c920be6b09f383a826e602531bd6bf6b064b1269c10445969bac5678acd7`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module SetDescription {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import InternalPowersetSupremum {ℓ} lem as Powersets
open import Cubical.Functions.Logic using ( ⇔toPath )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Ground = Powersets.Ground

describe : ∀ {n} → Fin n → Fin n → Formula S (suc n) → Formula S n
describe I B body = ∀̇
  (((var zero ∈̇ var (suc I)) ⇒̇
    ((var zero ∈̇ var (suc B)) ∧̇ body)) ∧̇
   (((var zero ∈̇ var (suc B)) ∧̇ body) ⇒̇
    (var zero ∈̇ var (suc I))))

module Reading {n : ℕ} (I B : Fin n) (body : Formula S (suc n))
  (γ : Vec S n) (A : S)
  (exact-membership : ∀ z → (z ∈ˢ A)
    ≡ ((z ∈ˢ lookup B γ) ⊓ ((z ∷ γ) ⊨ body))) where

  out : ⟨ γ ⊨ describe I B body ⟩ → lookup I γ ≡ A
  out holds = Ground.extensional λ z → ⇔toPath
    (λ member → subst ⟨_⟩ (sym (exact-membership z))
      (fst (holds z) member))
    (λ member → snd (holds z)
      (subst ⟨_⟩ (exact-membership z) member))

  into : lookup I γ ≡ A → ⟨ γ ⊨ describe I B body ⟩
  into eq z =
    (λ member → subst ⟨_⟩ (exact-membership z)
      (subst (λ C → ⟨ z ∈ˢ C ⟩) eq member)) ,
    (λ member → subst (λ C → ⟨ z ∈ˢ C ⟩) (sym eq)
      (subst ⟨_⟩ (sym (exact-membership z)) member))

  exact : (γ ⊨ describe I B body)
    ≡ ((lookup I γ ≡ A) , isSetS (lookup I γ) A)
  exact = ⇔toPath out into
```

### UniqueValue.agda

SHA-256: `587492897c6be8755e44ab1e4981732278f99c31efb649f26c1c84c83fb4509d`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module UniqueValue where

open import Cubical.Foundations.Prelude using
  ( Level; Type; _≡_; cong; isProp )
open import Cubical.Foundations.HLevels using
  ( hProp; isPropΠ; isProp× )
open import Cubical.Data.Sigma using
  ( Σ; _×_; _,_; fst; snd; Σ≡Prop )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
import Cubical.HITs.PropositionalTruncation as PT

module Supremum {ℓs ℓb ℓr : Level}
  (S : Type ℓs) (B : Type ℓb) (R : B → B → hProp ℓr)
  (antisym : (a b : B) → fst (R a b) → fst (R b a) → a ≡ b)
  (φ : S → B) where

  Upper : B → Type _
  Upper b = (x : S) → fst (R (φ x) b)

  upper-is-prop : (b : B) → isProp (Upper b)
  upper-is-prop b = isPropΠ (λ x → snd (R (φ x) b))

  Specification : B → Type _
  Specification b = Upper b × ((c : B) → Upper c → fst (R b c))

  specification-is-prop : (b : B) → isProp (Specification b)
  specification-is-prop b = isProp× (upper-is-prop b)
    (isPropΠ (λ c → isPropΠ (λ _ → snd (R b c))))

  Result : Type _
  Result = Σ B Specification

  result-is-prop : isProp Result
  result-is-prop (a , au , al) (b , bu , bl) =
    Σ≡Prop specification-is-prop (antisym a b (al b bu) (bl a au))

  realize : ∥ Result ∥₁ → Result
  realize = PT.rec result-is-prop (λ r → r)

  module Certificates {ℓc : Level} (C : Type ℓc)
    (value : C → B) (correct : (c : C) → Specification (value c)) where

    from-bound-existence : ∥ C ∥₁ → Result
    from-bound-existence = PT.rec result-is-prop (λ c → value c , correct c)

    independent : (p q : ∥ C ∥₁)
      → fst (from-bound-existence p) ≡ fst (from-bound-existence q)
    independent p q = cong fst
      (result-is-prop (from-bound-existence p) (from-bound-existence q))

  compare-certificates : {ℓc ℓd : Level} (C : Type ℓc) (D : Type ℓd)
    (cv : C → B) (dv : D → B)
    (cs : (c : C) → Specification (cv c))
    (ds : (d : D) → Specification (dv d))
    (p : ∥ C ∥₁) (q : ∥ D ∥₁)
    → fst (Certificates.from-bound-existence C cv cs p)
      ≡ fst (Certificates.from-bound-existence D dv ds q)
  compare-certificates C D cv dv cs ds p q = cong fst
    (result-is-prop (Certificates.from-bound-existence C cv cs p)
      (Certificates.from-bound-existence D dv ds q))
```

### RelativeSupremumUniqueness.agda

SHA-256: `650542973d4bede2fdcd313c57958ed40b05f9c18bacc1c7f2c4cbc03efd781c`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module RelativeSupremumUniqueness {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import Base.Truth using ( hPropAlgebra )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import IndexedSupremum {ℓ} as Indexed
import UniqueValue as Core
open import Cubical.Data.Sigma using ( Σ≡Prop )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module WithOrder
  (Order : S → S → hProp (ℓ-suc ℓ))
  (orderAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (order-reading : ∀ {n} (x y : Fin n) (γ : Vec S n)
    → (γ ⊨ orderAt x y) ≡ Order (lookup x γ) (lookup y γ)) where

  module Sup = Indexed.WithOrder Order orderAt order-reading

  module For (B : S)
    (antisym : (a b : S) → ⟨ a ∈ˢ B ⟩ → ⟨ b ∈ˢ B ⟩
      → ⟨ Order a b ⟩ → ⟨ Order b a ⟩ → a ≡ b) where

    Element : Type (ℓ-suc ℓ)
    Element = Σ S (λ a → ⟨ a ∈ˢ B ⟩)

    relation : Element → Element → hProp (ℓ-suc ℓ)
    relation a b = Order (fst a) (fst b)

    relation-antisym : (a b : Element)
      → ⟨ relation a b ⟩ → ⟨ relation b a ⟩ → a ≡ b
    relation-antisym a b ab ba = Σ≡Prop (λ x → snd (x ∈ˢ B))
      (antisym (fst a) (fst b) (snd a) (snd b) ab ba)

    module Value {A : S}
      (boundedA : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ B ⟩) where

      Index : Type (ℓ-suc ℓ)
      Index = Σ S (λ x → ⟨ x ∈ˢ A ⟩)

      value : Index → Element
      value x = fst x , boundedA (fst x) (snd x)

      module Unique = Core.Supremum Index Element relation relation-antisym value

      result : (a : S) → Sup.Supremum B A a → Unique.Result
      result a (aB , upper , least) =
        (a , aB) ,
        (λ x → upper (fst x) (snd x)) ,
        λ c is-upper → least (fst c) (snd c)
          (λ x xA → is-upper (x , xA))

      unique : (a b : S) → Sup.Supremum B A a → Sup.Supremum B A b → a ≡ b
      unique a b a-sup b-sup = cong (λ r → fst (fst r))
        (Unique.result-is-prop (result a a-sup) (result b b-sup))
```

### PowersetStepLocality.agda

SHA-256: `baeaae2d96940cd023c7dff16368321caaa7b05d8de1bc852ba1739ca412a1fa`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetStepLocality {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
import InternalPowersetSupremum {ℓ} lem as Powersets
import InternalIntersection {ℓ} lem as Intersection
import PowersetAtomicExpression {ℓ} lem as Atomic
import WeightedPredecessorAgreement
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module For (X : S) where

  module Algebra = Powersets.For X
  module Expressions = Atomic.For X
  open Algebra using ( B )

  module Tables (C H K x y : S) (xC : ⟨ x ∈ˢ C ⟩) (yC : ⟨ y ∈ˢ C ⟩) where

    module Previous = WeightedPredecessorAgreement.Tables lem C B H K x y xC yC

    module Agreement (coversH : Previous.Covers H) (coversK : Previous.Covers K)
      (same : Previous.Same) where

      module Transfer = Previous.Agreement coversH coversK same

      module Forward = Expressions.Forward.Congruence C x y H K
        (λ u a uC aB entry v c d vC cB dB inner-entry →
          Transfer.at-pair u v uC vC ∣ a , entry ∣₁ ∣ c , inner-entry ∣₁ d dB)
      module Reverse = Expressions.Reverse.Congruence C y x H K
        (λ v c vC cB entry u a d uC aB dB inner-entry →
          Transfer.at-pair u v uC vC ∣ a , inner-entry ∣₁ ∣ c , entry ∣₁ d dB)
      module Left = Expressions.Expression C x y H
      module Right = Expressions.Expression C x y K

      value-equal : Left.value ≡ Right.value
      value-equal = cong₂ Intersection.intersection Forward.value-equal Reverse.value-equal
```

### PowersetStepFormula.agda

SHA-256: `4dd4804d3f31b607ca44760e8a3d9e949ab0fc21f1218a15a0bcd55726dbab8f`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetStepFormula {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; _∧̇_; ∃̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL )
open import PairFormulaReading {ℓ} using ( reading )
open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( instantiate; instantiate-reading )
import SetDescription {ℓ} lem as Description
import RelativeSupremumUniqueness {ℓ} as Uniqueness
import PowersetAtomicExpression {ℓ} lem as Expressions
import PowersetStepLocality {ℓ} lem as Locality
import IndexedWeightedImage {ℓ} as Keys
import InternalIntersection {ℓ} lem as Intersection
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

shiftTwo : ∀ {n} → Fin n → Fin (suc (suc n))
shiftTwo i = suc (suc i)

module For (X : S) where

  module Expression = Expressions.For X
  module Bounds = Expression.Bounds
  open Expression.Algebra using ( B )

  antisym : ∀ a b → ⟨ a ∈ˢ B ⟩ → ⟨ b ∈ˢ B ⟩
    → ⟨ Bounds.Order a b ⟩ → ⟨ Bounds.Order b a ⟩ → a ≡ b
  antisym a b aB bB ab ba = Description.Ground.extensional
    (λ z → ⇔toPath (ba z) (ab z))

  module Unique = Uniqueness.WithOrder.For Bounds.Order Bounds.orderAt Bounds.order-reading B antisym

  module WithKey
    (Key : S → S → S)
    (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    (key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
      → (γ ⊨ keyAt q f v) ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
        isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ)))) where

    module Branch = Expression.WithKey Key keyAt key-reading
    module Images = Branch.Images

    imageSetAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
    imageSetAt I X C D outer inner H = Description.describe I D
      (Images.imageAt (suc X) (suc C) (suc D) (suc outer) (suc inner) (suc H) zero)

    module ImageReading {n : ℕ} (I X C D outer inner H : Fin n) (γ : Vec S n) where

      module Actual = Images.Construction (lookup X γ) (lookup C γ) (lookup D γ)
        (lookup outer γ) (lookup inner γ) (lookup H γ)

      body : Formula S (suc n)
      body = Images.imageAt (suc X) (suc C) (suc D) (suc outer) (suc inner) (suc H) zero

      membership : ∀ z → (z ∈ˢ Actual.image) ≡ ((z ∈ˢ lookup D γ) ⊓ ((z ∷ γ) ⊨ body))
      membership z = ⇔toPath
        (λ member → fst (Actual.image-out z member) ,
          Images.into (suc X) (suc C) (suc D) (suc outer) (suc inner) (suc H) zero
            (z ∷ γ) (snd (Actual.image-out z member)))
        (λ { (zB , witness) → Actual.image-in z zB
          (Images.out (suc X) (suc C) (suc D) (suc outer) (suc inner) (suc H) zero (z ∷ γ) witness) })

      module Read = Description.Reading I D body γ Actual.image membership

    rawAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
    rawAt X C D outer inner H b = ∃̇
      (imageSetAt zero (suc X) (suc C) (suc D) (suc outer) (suc inner) (suc H)
      ∧̇ Bounds.infimumAt (suc D) zero (suc b))

    module RawReading {n : ℕ} (X C D outer inner H b : Fin n) (γ : Vec S n) where

      module Actual = Images.Construction (lookup X γ) (lookup C γ) (lookup D γ)
        (lookup outer γ) (lookup inner γ) (lookup H γ)

      out : ⟨ γ ⊨ rawAt X C D outer inner H b ⟩
        → Bounds.Infimum.Supremum (lookup D γ) Actual.image (lookup b γ)
      out = PT.rec (Bounds.Infimum.supremum-is-prop (lookup D γ) Actual.image (lookup b γ))
        λ { (A , description , bound) → subst
          (λ I → Bounds.Infimum.Supremum (lookup D γ) I (lookup b γ))
          (ImageReading.Read.out zero (suc X) (suc C) (suc D) (suc outer) (suc inner) (suc H)
            (A ∷ γ) description)
          (Bounds.Infimum.supremum-out (suc D) zero (suc b) (A ∷ γ) bound) }

      into : Bounds.Infimum.Supremum (lookup D γ) Actual.image (lookup b γ)
        → ⟨ γ ⊨ rawAt X C D outer inner H b ⟩
      into correct = ∣ Actual.image ,
        ImageReading.Read.into zero (suc X) (suc C) (suc D) (suc outer) (suc inner) (suc H)
          (Actual.image ∷ γ) refl ,
        Bounds.Infimum.supremum-in (suc D) zero (suc b) (Actual.image ∷ γ) correct ∣₁

    parameterized : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S (suc (suc n))
    parameterized C outer inner H b = rawAt zero (shiftTwo C) (suc zero)
      (shiftTwo outer) (shiftTwo inner) (shiftTwo H) (shiftTwo b)

    branchAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
    branchAt C outer inner H b = instantiate (X ∷ B ∷ []) (parameterized C outer inner H b)

    module Reading {n : ℕ} (C outer inner H b : Fin n) (γ : Vec S n) where

      module Actual = Branch.Construction (lookup C γ) (lookup outer γ) (lookup inner γ) (lookup H γ)
      module Raw = RawReading zero (shiftTwo C) (suc zero) (shiftTwo outer) (shiftTwo inner)
        (shiftTwo H) (shiftTwo b) (X ∷ B ∷ γ)

      bounded : ∀ z → ⟨ z ∈ˢ Actual.Image.image ⟩ → ⟨ z ∈ˢ B ⟩
      bounded z member = fst (Actual.Image.image-out z member)

      module Value = Unique.Value {A = Actual.Image.image} bounded

      specialization = instantiate-reading (X ∷ B ∷ []) (parameterized C outer inner H b) γ

      out : ⟨ γ ⊨ branchAt C outer inner H b ⟩ → lookup b γ ≡ Actual.value
      out holds = Value.unique (lookup b γ) Actual.value
        (Raw.out (subst ⟨_⟩ specialization holds)) Actual.correct

      into : lookup b γ ≡ Actual.value → ⟨ γ ⊨ branchAt C outer inner H b ⟩
      into eq = subst ⟨_⟩ (sym specialization) (Raw.into
        (subst (λ v → Bounds.Infimum.Supremum B Actual.Image.image v) (sym eq) Actual.correct))

      exact : (γ ⊨ branchAt C outer inner H b)
        ≡ ((lookup b γ ≡ Actual.value) , isSetS (lookup b γ) Actual.value)
      exact = ⇔toPath out into

  module Forward = WithKey prʟ prAtL reading
  module Reverse = WithKey (λ f v → prʟ v f) Keys.reverseKeyAt Keys.reverse-key-reading

  stepAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  stepAt C x y H b = ∃̇∈ (con B) (∃̇∈ (con B)
    (Forward.branchAt (shiftTwo C) (shiftTwo x) (shiftTwo y) (shiftTwo H) (suc zero)
    ∧̇ (Reverse.branchAt (shiftTwo C) (shiftTwo y) (shiftTwo x) (shiftTwo H) zero
    ∧̇ Intersection.meetAt (suc zero) zero (shiftTwo b))))

  module Reading {n : ℕ} (C x y H b : Fin n) (γ : Vec S n) where

    module Actual = Expression.Expression (lookup C γ) (lookup x γ) (lookup y γ) (lookup H γ)

    out : ⟨ γ ⊨ stepAt C x y H b ⟩ → lookup b γ ≡ Actual.value
    out = PT.rec (isSetS (lookup b γ) Actual.value) λ { (l , lB , rest) →
      PT.rec (isSetS (lookup b γ) Actual.value) (λ { (r , rB , left , right , meet) →
        subst ⟨_⟩ (Intersection.meet-reading (suc zero) zero (shiftTwo b) (r ∷ l ∷ γ)) meet
        ∙ cong₂ Intersection.intersection
          (Forward.Reading.out (shiftTwo C) (shiftTwo x) (shiftTwo y) (shiftTwo H) (suc zero)
            (r ∷ l ∷ γ) left)
          (Reverse.Reading.out (shiftTwo C) (shiftTwo y) (shiftTwo x) (shiftTwo H) zero
            (r ∷ l ∷ γ) right) }) rest }

    into : lookup b γ ≡ Actual.value → ⟨ γ ⊨ stepAt C x y H b ⟩
    into eq = ∣ Actual.Left.value , Actual.Left.value-in-B ,
      ∣ Actual.Right.value , Actual.Right.value-in-B ,
        Forward.Reading.into (shiftTwo C) (shiftTwo x) (shiftTwo y) (shiftTwo H) (suc zero)
          (Actual.Right.value ∷ Actual.Left.value ∷ γ) refl ,
        Reverse.Reading.into (shiftTwo C) (shiftTwo y) (shiftTwo x) (shiftTwo H) zero
          (Actual.Right.value ∷ Actual.Left.value ∷ γ) refl ,
        subst ⟨_⟩ (sym (Intersection.meet-reading (suc zero) zero (shiftTwo b)
          (Actual.Right.value ∷ Actual.Left.value ∷ γ))) eq ∣₁ ∣₁

    exact : (γ ⊨ stepAt C x y H b)
      ≡ ((lookup b γ ≡ Actual.value) , isSetS (lookup b γ) Actual.value)
    exact = ⇔toPath out into

  Step : S → S → S → S → S → hProp (ℓ-suc ℓ)
  Step C x y H b = (b ≡ Actual.value) , isSetS b Actual.value
    where
    module Actual = Expression.Expression C x y H

  step-reading : ∀ {n} (C x y H b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt C x y H b)
      ≡ Step (lookup C γ) (lookup x γ) (lookup y γ) (lookup H γ) (lookup b γ)
  step-reading = Reading.exact

  unique : ∀ C x y H b c → ⟨ Step C x y H b ⟩ → ⟨ Step C x y H c ⟩ → b ≡ c
  unique C x y H b c pb pc = pb ∙ sym pc

  admit : ∀ C x y H → Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Step C x y H b ⟩)
  admit C x y H = Actual.value , Actual.value-in-B , refl
    where
    module Actual = Expression.Expression C x y H

  module Tables (C H K x y : S) (xC : ⟨ x ∈ˢ C ⟩) (yC : ⟨ y ∈ˢ C ⟩) where

    module Values = Locality.For.Tables X C H K x y xC yC

    module Agreement (coversH : Values.Previous.Covers H) (coversK : Values.Previous.Covers K)
      (same : Values.Previous.Same) where

      module Comparison = Values.Agreement coversH coversK same

      transfer : ∀ b → ⟨ Step C x y H b ⟩ → ⟨ Step C x y K b ⟩
      transfer b holds = holds ∙ Comparison.value-equal
```
