# K0 fixed atomic graph formula and shared variable-domain syntax

Date: 2026-09-09. Source baseline: `2c88143d`. This extends the [semantic value relation](k0-good-table-value-relation-2026-09.md). Five safe temporary probe sources are archived below. K0 remains open; production `src` is unchanged.

## Checked endpoint

For a fixed actual L set X and B = P(X), `PowersetAtomicGraphFormula.For X.formula : Formula S 3` is one finite first-order formula with free variables x, y and b. Its all-environment precursor `graphAt x y b` has the exact reading `PowersetAtomicGraph.For X.graph-prop (lookup x γ) (lookup y γ) (lookup b γ)` for every environment γ. The three-variable specialization reads the same relation on the environment x, y, b.

The formula expresses:

```text
there exist C and H such that
  C is child-closed,
  x belongs to C,
  y belongs to C,
  H is good for the C-indexed powerset step,
  b belongs to B,
  there exists p such that p = pair(x,y) and pair(p,b) belongs to H.
```

C, H and p are object-language bound variables. The syntax does not insert a host-computed product(C,C) as a constant under the C binder. The existential pair code p is eliminated using the existing pair-reading theorem and equality transport. Both directions eliminate truncated witnesses only into propositions. The formula reads precisely the previously checked relation; there is no new definition of atomic value or new comparison induction.

The semantic relation already supplies unique witnessed outputs, existence on a supplied closed container and existence for valid material names. The new reading connects this relation to fixed first-order syntax. It does not prove all Boolean equality/membership laws, collect the entire class relation into a set, construct Cohen forcing, or construct the ordinary non-CH model.

## Reusable components and proof ownership

| Component | Checked interface | Reuse boundary |
|---|---|---|
| Variable product membership | `ProductMembershipFormula.productAt C D p` and all-environment `product-reading` | Existing actual product and its membership specification; no second product construction |
| Variable encoded Step | `PowersetPairStep.For X.pairStepAt C H p b` and `pair-step-reading` | One shared `PairStep` and reading; fixed-C Step specializes the same syntax and proof |
| Parameterized Good tables | `CodedGoodTables.WithParameter.goodAt a h` and `good-reading` | One `Semantics` module, one three-clause reading proof; the old fixed-domain API specializes this template |
| Powerset Good instance | `PowersetGoodFormula.For X.goodAt C H` and `good-reading` | Product(C,C), the existing dependency relation, encoded Step and the original recursion Good predicate |
| Fixed atomic graph | `PowersetAtomicGraphFormula.For X.graphAt`, `graph-reading`, `formula`, `formula-reading` | Existing closure, Good, pair and entry readings, and the existing semantic witness relation |

The generic Good template takes an actual domain function D(a), a membership formula with its all-environment reading, a fixed value bound B, a dependency relation with its reading, and a parameter-dependent Step with its reading. This supports domain and Step variation without rebuilding the comparison kernel. It assumes the supplied readings, not the ability to translate arbitrary host functions automatically into first-order formulas. The powerset instance discharges those contracts with checked implementations.

`Semantics D B R Step` owns Domain, Downward, Obeys and Good. Functionality reuses `CodedTableFunctionality.Construction D B`. The old `WithStep.Construction D B` opens the same semantic definitions and instantiates the uniform formula with the parameter D and a Step that ignores that parameter. Its `formula-in/out` are derived from the shared reading. Thus existing recursion consumers retain the same semantic contract, while the implementation has one Good reading proof covering both public interfaces.

The old formula's syntax tree changes: explicit universal quantification with a membership implication replaces some bounded universal nodes. This is not promised to preserve syntactic equality. Existing clients use the formula together with its reading/in/out interface; the actual table and graph dependencies are rechecked to validate this use. The independent product-membership description does not change the actual product implementation.

## Assumptions and remaining work

Successor: the [attained atomic value-set probe](k0-atomic-value-set-2026-09.md) realizes the fixed graph as an internal set of attained values and proves the corresponding admitted join. The [exit checklist](k0-exit-checklist-2026-09.md) bounds the remaining K0 work; full atomic laws still belong to K4.

No host AC, countable/dependent choice, BPI, Zorn, ultrafilter selection, resizing or additional LEM level is added. `CodedGoodTables` itself has no LEM parameter; the concrete L/powerset constructions retain the existing `LEM (ℓ-suc ℓ)` parameter through their dependencies. Supplied formula readings and the semantic closed-container/name conditions remain explicit contracts. This local probe does not certify all eventual T3 assumptions.

The next atomic task is the internally realized membership/value image and the atomic semantic laws, using this fixed graph formula and the previously constructed unique values. General-ground adapters, general Boolean/regular-open completion, quantified value bounds, Collection/fullness and ordinary-model extraction remain open. The broader plan is unchanged: reusable poset and Boolean interfaces and certified translations first, the actual ordinary non-CH model as T3, and ground definability as T4.

## Verification

All five final sources passed the prescribed safe Agda checks in the temporary compile root. Checking `PowersetGoodFormula` also rechecked its changed generic Good and pair-Step consumers through the actual table and semantic graph dependencies. The final `PowersetAtomicGraphFormula` check verified composition with that semantic graph. At most two Agda checks ran concurrently.

```sh
GHCRTS="-A64m -I0 -M8g" agda src/ProductMembershipFormula.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetPairStep.agda
GHCRTS="-A64m -I0 -M8g" agda src/CodedGoodTables.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetGoodFormula.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicGraphFormula.agda
```

An initial generic-template check reported one unsolved implicit arity in the old `domain-reading` alias. Explicit polymorphic signatures for that alias and `domainAt` resolved it; the final template check exited 0. The first powerset Good instance check also exposed a missing `Formula` import after its dependencies checked; adding the narrow syntax import resolved it. No holes or unchecked intermediate variants are archived here.

Scoped prose/glossary gates, snapshot hashes and byte equality, local links, and `git diff --check` passed. All 123 tracked production files and their copied probe-baseline sources match `2c88143d` byte-for-byte. Whole-tree and trilingual chapter gates were not run for this temporary-probe/documentation batch.

## Source snapshots

### ProductMembershipFormula.agda

SHA-256: `1b105499c542b26d1bbc9609c473f82aac7cecee1d37f2181ff3e2cb80eddc4e`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProductMembershipFormula {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prAtL )
open import PairFormulaReading {ℓ} using ( reading )
import ProductSet {ℓ} lem as Product
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

productAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
productAt C D p = ∃̇∈ (var C) (∃̇∈ (var (suc D))
  (prAtL (suc (suc p)) (suc zero) zero))

module Reading {n : ℕ} (C D p : Fin n) (γ : Vec S n) where

  module Actual = Product.Construction (lookup C γ) (lookup D γ)

  out : ⟨ γ ⊨ productAt C D p ⟩ → ⟨ lookup p γ ∈ˢ Actual.product ⟩
  out witnesses = Actual.product-in (lookup p γ)
    (PT.rec PT.squash₁ (λ { (x , xC , ys) → PT.map
      (λ { (y , yD , pair) → x , y , xC , yD , subst ⟨_⟩
        (reading (suc (suc p)) (suc zero) zero (y ∷ x ∷ γ)) pair }) ys })
      witnesses)

  into : ⟨ lookup p γ ∈ˢ Actual.product ⟩ → ⟨ γ ⊨ productAt C D p ⟩
  into member = PT.map (λ { (x , y , xC , yD , pair) →
    x , xC , ∣ y , yD , subst ⟨_⟩
      (sym (reading (suc (suc p)) (suc zero) zero (y ∷ x ∷ γ))) pair ∣₁ })
    (Actual.product-out (lookup p γ) member)

  exact : (γ ⊨ productAt C D p) ≡ (lookup p γ ∈ˢ Actual.product)
  exact = ⇔toPath out into

product-reading : ∀ {n} (C D p : Fin n) (γ : Vec S n)
  → (γ ⊨ productAt C D p)
    ≡ (lookup p γ ∈ˢ Product.Construction.product (lookup C γ) (lookup D γ))
product-reading = Reading.exact
```

### PowersetPairStep.agda

SHA-256: `b710c01553d592435b0cbcf09172a2bdaa059c170fdffeb7fe6c4e3f2b2020db`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetPairStep {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL; prʟ-inj )
open import PairFormulaReading {ℓ} using ( reading )
open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ
  using ( instantiate; instantiate-reading )
import PowersetStepFormula {ℓ} lem as Powerset
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module For (X : S) where

  module Raw = Powerset.For X using ( Step; stepAt; step-reading )

  PairStep : S → S → S → S → hProp (ℓ-suc ℓ)
  PairStep C H p b = (∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
    ⟨ x ∈ˢ C ⟩ × ⟨ y ∈ˢ C ⟩ × (p ≡ prʟ x y) × ⟨ Raw.Step C x y H b ⟩ ∥₁) ,
    PT.squash₁

  shiftTwo : ∀ {n} → Fin n → Fin (suc (suc n))
  shiftTwo i = suc (suc i)

  pairStepAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  pairStepAt C H p b = ∃̇∈ (var C) (∃̇∈ (var (suc C))
    (prAtL (shiftTwo p) (suc zero) zero
    ∧̇ Raw.stepAt (shiftTwo C) (suc zero) zero (shiftTwo H) (shiftTwo b)))

  pair-forward : ∀ {n} (C H p b : Fin n) (γ : Vec S n)
    → ⟨ γ ⊨ pairStepAt C H p b ⟩
    → ⟨ PairStep (lookup C γ) (lookup H γ) (lookup p γ) (lookup b γ) ⟩
  pair-forward C H p b γ = PT.rec PT.squash₁
    (λ { (x , xC , ys) → PT.map
      (λ { (y , yC , pair , raw) → x , y , xC , yC ,
        subst ⟨_⟩ (reading (shiftTwo p) (suc zero) zero (y ∷ x ∷ γ)) pair ,
        subst ⟨_⟩
          (Raw.step-reading (shiftTwo C) (suc zero) zero
            (shiftTwo H) (shiftTwo b) (y ∷ x ∷ γ)) raw }) ys })

  pair-backward : ∀ {n} (C H p b : Fin n) (γ : Vec S n)
    → ⟨ PairStep (lookup C γ) (lookup H γ) (lookup p γ) (lookup b γ) ⟩
    → ⟨ γ ⊨ pairStepAt C H p b ⟩
  pair-backward C H p b γ = PT.rec (snd (γ ⊨ pairStepAt C H p b))
    (λ { (x , y , xC , yC , pair , raw) → ∣ x , xC , ∣ y , yC ,
      subst ⟨_⟩ (sym (reading (shiftTwo p) (suc zero) zero (y ∷ x ∷ γ))) pair ,
      subst ⟨_⟩
        (sym (Raw.step-reading (shiftTwo C) (suc zero) zero
          (shiftTwo H) (shiftTwo b) (y ∷ x ∷ γ))) raw ∣₁ ∣₁ })

  pair-reading : ∀ {n} (C H p b : Fin n) (γ : Vec S n)
    → (γ ⊨ pairStepAt C H p b)
      ≡ PairStep (lookup C γ) (lookup H γ) (lookup p γ) (lookup b γ)
  pair-reading C H p b γ = ⇔toPath
    (pair-forward C H p b γ) (pair-backward C H p b γ)

  module WithDomain (C : S) where

    Step : S → S → S → hProp (ℓ-suc ℓ)
    Step = PairStep C

    parameterized : ∀ {n} → Fin n → Fin n → Fin n → Formula S (suc n)
    parameterized H p b = pairStepAt zero (suc H) (suc p) (suc b)

    stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    stepAt H p b = instantiate (C ∷ []) (parameterized H p b)

    module Reading {n : ℕ} (H p b : Fin n) (γ : Vec S n) where

      specialization = instantiate-reading (C ∷ []) (parameterized H p b) γ

      exact : (γ ⊨ stepAt H p b)
        ≡ Step (lookup H γ) (lookup p γ) (lookup b γ)
      exact = specialization ∙ pair-reading zero (suc H) (suc p) (suc b) (C ∷ γ)

      forward : ⟨ γ ⊨ stepAt H p b ⟩
        → ⟨ Step (lookup H γ) (lookup p γ) (lookup b γ) ⟩
      forward = subst ⟨_⟩ exact

      backward : ⟨ Step (lookup H γ) (lookup p γ) (lookup b γ) ⟩
        → ⟨ γ ⊨ stepAt H p b ⟩
      backward = subst ⟨_⟩ (sym exact)

    step-reading : ∀ {n} (H p b : Fin n) (γ : Vec S n)
      → (γ ⊨ stepAt H p b)
        ≡ Step (lookup H γ) (lookup p γ) (lookup b γ)
    step-reading = Reading.exact

    pair-out : ∀ H x y b → ⟨ Step H (prʟ x y) b ⟩ → ⟨ Raw.Step C x y H b ⟩
    pair-out H x y b = PT.rec (snd (Raw.Step C x y H b))
      λ { (u , v , uC , vC , pair , raw) →
        subst2 (λ a c → ⟨ Raw.Step C a c H b ⟩)
          (sym (fst (prʟ-inj pair))) (sym (snd (prʟ-inj pair))) raw }

    pair-in : ∀ H x y b → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
      → ⟨ Raw.Step C x y H b ⟩ → ⟨ Step H (prʟ x y) b ⟩
    pair-in H x y b xC yC raw = ∣ x , y , xC , yC , refl , raw ∣₁

  pair-step-reading : ∀ {n} (C H p b : Fin n) (γ : Vec S n)
    → (γ ⊨ pairStepAt C H p b)
      ≡ WithDomain.Step (lookup C γ) (lookup H γ) (lookup p γ) (lookup b γ)
  pair-step-reading = pair-reading
```

### CodedGoodTables.agda

SHA-256: `712a6537e132c7116586e5ca8f63476920db8a0139c15f9593d336510cbbd852`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module CodedGoodTables {ℓ : Level} where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; ∀̇_; _∧̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
open import CodedTableFunctionality {ℓ} using ( entryAt; entry-reading )
import CodedTableFunctionality
import CodedTableReadout
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open At S id using ( _⊨_ )

open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ
  using ( instantiate; instantiate-reading )
open import Cubical.Data.Sigma using ( Σ≡Prop )

module Semantics (D B : S) (R : S → S → hProp (ℓ-suc ℓ))
  (Step : S → S → S → hProp (ℓ-suc ℓ)) where

  module Functionality = CodedTableFunctionality.Construction D B

  Domain : S → S → Type (ℓ-suc ℓ)
  Domain H x = ∥ Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩ × ⟨ prʟ x b ∈ˢ H ⟩ ∥₁

  domain-is-prop : ∀ H x → isProp (Domain H x)
  domain-is-prop H x = PT.squash₁

  Downward : S → Type (ℓ-suc ℓ)
  Downward H = (x y : S) → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
    → Domain H x → ⟨ R y x ⟩ → Domain H y

  Obeys : S → Type (ℓ-suc ℓ)
  Obeys H = (x b : S) → ⟨ x ∈ˢ D ⟩ → ⟨ b ∈ˢ B ⟩
    → ⟨ prʟ x b ∈ˢ H ⟩ → ⟨ Step H x b ⟩

  Good : S → Type (ℓ-suc ℓ)
  Good H = Functionality.Functional H × Downward H × Obeys H

  downward-is-prop : ∀ H → isProp (Downward H)
  downward-is-prop H = isPropΠ (λ x → isPropΠ (λ y →
    isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → PT.squash₁))))))

  obeys-is-prop : ∀ H → isProp (Obeys H)
  obeys-is-prop H = isPropΠ (λ x → isPropΠ (λ b → isPropΠ (λ _ →
    isPropΠ (λ _ → isPropΠ (λ _ → snd (Step H x b))))))

  good-is-prop : ∀ H → isProp (Good H)
  good-is-prop H = isProp× (Functionality.functional-is-prop H)
    (isProp× (downward-is-prop H) (obeys-is-prop H))

  domain-readout : ∀ H (functional : Functionality.Functional H) x
    → Domain H x ≡ CodedTableReadout.Readout.Domain D B H functional x
  domain-readout H functional x = refl

module WithParameter
  (D : S → S) (B : S)
  (memberAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (member-reading : ∀ {n} (a x : Fin n) (γ : Vec S n)
    → (γ ⊨ memberAt a x) ≡ (lookup x γ ∈ˢ D (lookup a γ)))
  (R : S → S → hProp (ℓ-suc ℓ))
  (rAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (rAt-adequate : ∀ {n} (y x : Fin n) (γ : Vec S n)
    → (γ ⊨ rAt y x) ≡ R (lookup y γ) (lookup x γ))
  (Step : S → S → S → S → hProp (ℓ-suc ℓ))
  (stepAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (stepAt-adequate : ∀ {n} (a h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt a h x b)
      ≡ Step (lookup a γ) (lookup h γ) (lookup x γ) (lookup b γ)) where

  module Meaning (a : S) = Semantics (D a) B R (Step a)

  domainAt : ∀ {n} → Fin n → Fin n → Formula S n
  domainAt h x = ∃̇∈ (con B) (entryAt (suc h) (suc x) zero)

  domain-reading : ∀ {n} (a : S) (h x : Fin n) (γ : Vec S n)
    → (γ ⊨ domainAt h x) ≡ (Meaning.Domain a (lookup h γ) (lookup x γ) , PT.squash₁)
  domain-reading a h x γ = ⇔toPath
    (PT.map (λ { (b , bB , entry) → b , bB , subst ⟨_⟩
      (entry-reading (suc h) (suc x) zero (b ∷ γ)) entry }))
    (PT.map (λ { (b , bB , entry) → b , bB , subst ⟨_⟩
      (sym (entry-reading (suc h) (suc x) zero (b ∷ γ))) entry }))

  functionalAt : ∀ {n} → Fin n → Fin n → Formula S n
  functionalAt a h = ∀̇ (memberAt (suc a) zero ⇒̇
    ∀̇∈ (con B) (∀̇∈ (con B)
      ((entryAt (suc (suc (suc h))) (suc (suc zero)) (suc zero)
        ∧̇ entryAt (suc (suc (suc h))) (suc (suc zero)) zero)
        ⇒̇ (var (suc zero) ≐ var zero))))

  downwardAt : ∀ {n} → Fin n → Fin n → Formula S n
  downwardAt a h = ∀̇ (memberAt (suc a) zero ⇒̇
    ∀̇ (memberAt (suc (suc a)) zero ⇒̇
      ((domainAt (suc (suc h)) (suc zero) ∧̇ rAt zero (suc zero))
        ⇒̇ domainAt (suc (suc h)) zero)))

  obeysAt : ∀ {n} → Fin n → Fin n → Formula S n
  obeysAt a h = ∀̇ (memberAt (suc a) zero ⇒̇
    ∀̇∈ (con B) (entryAt (suc (suc h)) (suc zero) zero
      ⇒̇ stepAt (suc (suc a)) (suc (suc h)) (suc zero) zero))

  goodAt : ∀ {n} → Fin n → Fin n → Formula S n
  goodAt a h = functionalAt a h ∧̇ (downwardAt a h ∧̇ obeysAt a h)

  module Reading {n : ℕ} (a h : Fin n) (γ : Vec S n) where

    module M = Meaning (lookup a γ)
    H = lookup h γ

    out : ⟨ γ ⊨ goodAt a h ⟩ → M.Good H
    out holds = functional , downward , obeys
      where
      functional : M.Functionality.Functional H
      functional x b c xD bB cB xb xc = Σ≡Prop (λ v → snd (isL v))
        (fst holds x (subst ⟨_⟩ (sym (member-reading (suc a) zero (x ∷ γ))) xD)
          b bB c cB
          (subst ⟨_⟩ (sym (entry-reading (suc (suc (suc h))) (suc (suc zero))
            (suc zero) (c ∷ b ∷ x ∷ γ))) xb ,
           subst ⟨_⟩ (sym (entry-reading (suc (suc (suc h))) (suc (suc zero))
            zero (c ∷ b ∷ x ∷ γ))) xc))

      downward : M.Downward H
      downward x y xD yD domain relation = subst ⟨_⟩
        (domain-reading (lookup a γ) (suc (suc h)) zero (y ∷ x ∷ γ))
        (fst (snd holds)
          x (subst ⟨_⟩ (sym (member-reading (suc a) zero (x ∷ γ))) xD)
          y (subst ⟨_⟩ (sym (member-reading (suc (suc a)) zero (y ∷ x ∷ γ))) yD)
          (subst ⟨_⟩ (sym (domain-reading (lookup a γ) (suc (suc h)) (suc zero)
            (y ∷ x ∷ γ))) domain ,
           subst ⟨_⟩ (sym (rAt-adequate zero (suc zero) (y ∷ x ∷ γ))) relation))

      obeys : M.Obeys H
      obeys x b xD bB entry = subst ⟨_⟩
        (stepAt-adequate (suc (suc a)) (suc (suc h)) (suc zero) zero (b ∷ x ∷ γ))
        (snd (snd holds)
          x (subst ⟨_⟩ (sym (member-reading (suc a) zero (x ∷ γ))) xD) b bB
          (subst ⟨_⟩ (sym (entry-reading (suc (suc h)) (suc zero) zero
            (b ∷ x ∷ γ))) entry))

    into : M.Good H → ⟨ γ ⊨ goodAt a h ⟩
    into (functional , downward , obeys) = functional-in , downward-in , obeys-in
      where
      functional-in : ⟨ γ ⊨ functionalAt a h ⟩
      functional-in x xD b bB c cB entries = cong fst
        (functional x b c
          (subst ⟨_⟩ (member-reading (suc a) zero (x ∷ γ)) xD) bB cB
          (subst ⟨_⟩ (entry-reading (suc (suc (suc h))) (suc (suc zero))
            (suc zero) (c ∷ b ∷ x ∷ γ)) (fst entries))
          (subst ⟨_⟩ (entry-reading (suc (suc (suc h))) (suc (suc zero))
            zero (c ∷ b ∷ x ∷ γ)) (snd entries)))

      downward-in : ⟨ γ ⊨ downwardAt a h ⟩
      downward-in x xD y yD premise = subst ⟨_⟩
        (sym (domain-reading (lookup a γ) (suc (suc h)) zero (y ∷ x ∷ γ)))
        (downward x y
          (subst ⟨_⟩ (member-reading (suc a) zero (x ∷ γ)) xD)
          (subst ⟨_⟩ (member-reading (suc (suc a)) zero (y ∷ x ∷ γ)) yD)
          (subst ⟨_⟩ (domain-reading (lookup a γ) (suc (suc h)) (suc zero)
            (y ∷ x ∷ γ)) (fst premise))
          (subst ⟨_⟩ (rAt-adequate zero (suc zero) (y ∷ x ∷ γ)) (snd premise)))

      obeys-in : ⟨ γ ⊨ obeysAt a h ⟩
      obeys-in x xD b bB entry = subst ⟨_⟩
        (sym (stepAt-adequate (suc (suc a)) (suc (suc h)) (suc zero) zero (b ∷ x ∷ γ)))
        (obeys x b (subst ⟨_⟩ (member-reading (suc a) zero (x ∷ γ)) xD) bB
          (subst ⟨_⟩ (entry-reading (suc (suc h)) (suc zero) zero (b ∷ x ∷ γ)) entry))

    exact : (γ ⊨ goodAt a h) ≡ (M.Good H , M.good-is-prop H)
    exact = ⇔toPath out into

  good-reading : ∀ {n} (a h : Fin n) (γ : Vec S n)
    → (γ ⊨ goodAt a h) ≡ (Meaning.Good (lookup a γ) (lookup h γ) ,
      Meaning.good-is-prop (lookup a γ) (lookup h γ))
  good-reading = Reading.exact

module WithStep
  (R : S → S → hProp (ℓ-suc ℓ))
  (rAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (rAt-adequate : ∀ {n} (y x : Fin n) (γ : Vec S n)
    → (γ ⊨ rAt y x) ≡ R (lookup y γ) (lookup x γ))
  (Step : S → S → S → hProp (ℓ-suc ℓ))
  (stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (stepAt-adequate : ∀ {n} (h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt h x b) ≡ Step (lookup h γ) (lookup x γ) (lookup b γ))
  where

  module Construction (D B : S) where

    open Semantics D B R Step public

    module Uniform = WithParameter id B (λ a x → var x ∈̇ var a)
      (λ a x γ → refl) R rAt rAt-adequate
      (λ _ → Step) (λ _ → stepAt) (λ _ → stepAt-adequate)

    domainAt : ∀ {n} → Fin n → Fin n → Formula S n
    domainAt = Uniform.domainAt
    domain-reading : ∀ {n} (h x : Fin n) (γ : Vec S n)
      → (γ ⊨ domainAt h x) ≡ (Domain (lookup h γ) (lookup x γ) , PT.squash₁)
    domain-reading = Uniform.domain-reading D

    downwardFormula : Formula S 1
    downwardFormula = instantiate (D ∷ []) (Uniform.downwardAt zero (suc zero))

    stepFormula : Formula S 1
    stepFormula = instantiate (D ∷ []) (Uniform.obeysAt zero (suc zero))

    formula : Formula S 1
    formula = instantiate (D ∷ []) (Uniform.goodAt zero (suc zero))

    formula-reading : ∀ H → ((H ∷ []) ⊨ formula) ≡ (Good H , good-is-prop H)
    formula-reading H = instantiate-reading (D ∷ []) (Uniform.goodAt zero (suc zero)) (H ∷ [])
      ∙ Uniform.good-reading zero (suc zero) (D ∷ H ∷ [])

    formula-out : ∀ H → ⟨ (H ∷ []) ⊨ formula ⟩ → Good H
    formula-out H = subst ⟨_⟩ (formula-reading H)

    formula-in : ∀ H → Good H → ⟨ (H ∷ []) ⊨ formula ⟩
    formula-in H = subst ⟨_⟩ (sym (formula-reading H))
```

### PowersetGoodFormula.agda

SHA-256: `83886b15c9d601bc4c0064e04e6307d4d5b9c7484960801711f207ae8e41f256`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetGoodFormula {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import ProductSet
import ProductMembershipFormula
import NamePairDependency
import PowersetPairStep
import PowersetAtomicGraph
import InternalPowersetSupremum
import CodedGoodTables

open hPropStructure 𝒮ʟ using ( S )
open At S id using ( _⊨_ )

module For (X : S) where

  module Algebra = InternalPowersetSupremum.For lem X using ( B )
  module Membership = ProductMembershipFormula lem using ( productAt; product-reading )
  module Dependency = NamePairDependency lem using ( R; relationAt; relation-reading )
  module Pair = PowersetPairStep.For lem X
    using ( PairStep; pairStepAt; pair-step-reading )
  module Graph = PowersetAtomicGraph.For lem X using ( Good )

  module Syntax = CodedGoodTables.WithParameter
    (λ C → ProductSet.Construction.product lem C C) Algebra.B
    (λ C p → Membership.productAt C C p)
    (λ C p γ → Membership.product-reading C C p γ)
    Dependency.R Dependency.relationAt Dependency.relation-reading
    Pair.PairStep Pair.pairStepAt Pair.pair-step-reading

  goodAt : ∀ {n} → Fin n → Fin n → Formula S n
  goodAt = Syntax.goodAt

  good-is-prop : ∀ C H → isProp (Graph.Good C H)
  good-is-prop C H = Syntax.Meaning.good-is-prop C H

  good-reading : ∀ {n} (C H : Fin n) (γ : Vec S n)
    → (γ ⊨ goodAt C H)
      ≡ (Graph.Good (lookup C γ) (lookup H γ) ,
        good-is-prop (lookup C γ) (lookup H γ))
  good-reading = Syntax.good-reading
```

### PowersetAtomicGraphFormula.agda

SHA-256: `2342cfdd94051838450de5171b04021e85d96ac5b2c182efc3c8a7e066a1c83a`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicGraphFormula {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL )
open import PairFormulaReading {ℓ} using ( reading )
open import CodedTableFunctionality {ℓ} using ( entryAt; entry-reading )
import ClosedDomainFormula
import PowersetGoodFormula
import PowersetAtomicGraph
import InternalPowersetSupremum
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module For (X : S) where

  module Algebra = InternalPowersetSupremum.For lem X using ( B )
  module Semantic = PowersetAtomicGraph.For lem X using ( Graph; graph-prop; introduce )
  module Closed = ClosedDomainFormula lem using ( closedAt; closed-reading )
  module Good = PowersetGoodFormula.For lem X using ( goodAt; good-reading )

  shiftTwo : ∀ {n} → Fin n → Fin (suc (suc n))
  shiftTwo i = suc (suc i)

  graphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  graphAt x y b = ∃̇ (∃̇
    (Closed.closedAt (suc zero)
      ∧̇ ((var (shiftTwo x) ∈̇ var (suc zero))
      ∧̇ ((var (shiftTwo y) ∈̇ var (suc zero))
      ∧̇ (Good.goodAt (suc zero) zero
      ∧̇ ((var (shiftTwo b) ∈̇ con Algebra.B)
      ∧̇ ∃̇ (prAtL zero (suc (shiftTwo x)) (suc (shiftTwo y))
        ∧̇ entryAt (suc zero) zero (suc (shiftTwo b)))))))))

  module Reading {n : ℕ} (x y b : Fin n) (γ : Vec S n) where

    out : ⟨ γ ⊨ graphAt x y b ⟩
      → Semantic.Graph (lookup x γ) (lookup y γ) (lookup b γ)
    out = PT.rec PT.squash₁ (λ { (C , tables) → PT.rec PT.squash₁
      (λ { (H , closed , xC , yC , good , bB , entries) → PT.rec PT.squash₁
        (λ { (p , pair , entry) → Semantic.introduce C H
          (lookup x γ) (lookup y γ) (lookup b γ)
          (subst ⟨_⟩ (Closed.closed-reading (suc zero) (H ∷ C ∷ γ)) closed)
          xC yC (subst ⟨_⟩ (Good.good-reading (suc zero) zero (H ∷ C ∷ γ)) good) bB
          (subst (λ q → ⟨ prʟ q (lookup b γ) ∈ˢ H ⟩)
            (subst ⟨_⟩ (reading zero (suc (shiftTwo x)) (suc (shiftTwo y))
              (p ∷ H ∷ C ∷ γ)) pair)
            (subst ⟨_⟩ (entry-reading (suc zero) zero (suc (shiftTwo b))
              (p ∷ H ∷ C ∷ γ)) entry)) }) entries }) tables })

    into : Semantic.Graph (lookup x γ) (lookup y γ) (lookup b γ)
      → ⟨ γ ⊨ graphAt x y b ⟩
    into = PT.rec (snd (γ ⊨ graphAt x y b))
      (λ { (C , H , closed , xC , yC , good , bB , entry) →
        ∣ C , ∣ H ,
          subst ⟨_⟩ (sym (Closed.closed-reading (suc zero) (H ∷ C ∷ γ))) closed ,
          xC , yC , subst ⟨_⟩ (sym (Good.good-reading (suc zero) zero (H ∷ C ∷ γ))) good ,
          bB , ∣ prʟ (lookup x γ) (lookup y γ) ,
            subst ⟨_⟩ (sym (reading zero (suc (shiftTwo x)) (suc (shiftTwo y))
              (prʟ (lookup x γ) (lookup y γ) ∷ H ∷ C ∷ γ))) refl ,
            subst ⟨_⟩ (sym (entry-reading (suc zero) zero (suc (shiftTwo b))
              (prʟ (lookup x γ) (lookup y γ) ∷ H ∷ C ∷ γ))) entry ∣₁ ∣₁ ∣₁ })

    exact : (γ ⊨ graphAt x y b)
      ≡ Semantic.graph-prop (lookup x γ) (lookup y γ) (lookup b γ)
    exact = ⇔toPath out into

  graph-reading : ∀ {n} (x y b : Fin n) (γ : Vec S n)
    → (γ ⊨ graphAt x y b)
      ≡ Semantic.graph-prop (lookup x γ) (lookup y γ) (lookup b γ)
  graph-reading = Reading.exact

  formula : Formula S 3
  formula = graphAt zero (suc zero) (suc (suc zero))

  formula-reading : ∀ x y b → ((x ∷ y ∷ b ∷ []) ⊨ formula)
    ≡ Semantic.graph-prop x y b
  formula-reading x y b = graph-reading zero (suc zero) (suc (suc zero)) (x ∷ y ∷ b ∷ [])
```
