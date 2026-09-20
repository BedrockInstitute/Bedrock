# K0 attained atomic values and an admitted existential join

Date: 2026-09-09. Baseline: `72d01001`. This extends the [fixed graph formula](k0-fixed-atomic-graph-formula-2026-09.md) and addresses E4 of the [K0 exit checklist](k0-exit-checklist-2026-09.md). Two safe temporary sources are archived below. K0 remains open; production `src` is unchanged.

## Actual family over all valid names

For an actual L set X, put B = P(X). Fix a valid material B-name y. `PowersetAtomicValueSet.For X y validY` uses the already constructed atomic recursion value at each valid material name x. It forms an actual L set `values` inside B, with exact membership:

```text
b belongs to values
  iff merely there exists a valid material B-name x
      whose constructed atomic value at (x,y) equals b.
```

The names range over the entire host carrier of valid material names at the stated universe level. No finite enumeration of names and no pre-existing internal set containing all names is assumed. Only the attained values are separated inside B.

A fixed two-variable formula says that x is a valid name and the fixed atomic graph holds at (x,y,b). `FormulaParameters.substitute-reading` publicly exposes the existing capture-avoiding substitution theorem, without a new induction. It embeds the one-variable name-recognition formula and substitutes the fixed parameter y into the three-variable atomic graph formula. `formula-reading` proves their exact conjunction. This is correctness for the particular fixed formula, not an internal global satisfaction predicate.

`FixedValueSet.Construction` supplies the existing Separation construction. The new instance proves every adequacy argument:

- `value-in-B` comes from the actual canonical recursion value.
- `represented` uses the checked valid-name graph existence theorem.
- `sound` reads validity from the formula and uses the graph's exact unique-value characterization.
- `values-membership` packages the two directions as equality of h-propositions.

These are proved arguments, not assumptions of the new instance. The generic value-set and upper-bound transfer proofs remain their single proof homes. The name subtype retains its ordinary validity proof; no representative is selected from Boolean equality classes.

## Actual supremum and upper-bound transfer

The values are subsets of X, so their internal union supplies the existing powerset supremum. `bounded` derives the required bound from Separation membership; `supremum-correct` uses `InternalPowersetSupremum.supremum-correct` on this actual set.

`name-supremum` then proves that this element belongs to B, bounds the atomic value for every valid material name x, and is below every other B-element with that property. It specializes `FixedValueSet.Adequacy.transferLUB`; there is no second least-upper-bound proof and no selected witness family.

This checks an admitted existential join over the actual valid-name family for the constructed atomic relation. It does not yet identify the relation with every law of Boolean equality/membership, or evaluate arbitrary compound formulas. E3's representative atomic semantics check and K4's full formula induction remain separate. A supremum is not asserted to be attained by a name with top truth value.

## What this closes, and what it does not

Successor: the [material atomic examples](k0-material-atomic-example-2026-09.md) close the representative E3 test. The historical remaining-work description below is superseded at that boundary; full K4 laws remain later work.

The attained-value collection and actual join portion of E4 now has a checked instance rather than a conditional graph-adequacy premise or a finite family example. The ground-side order is fixed recognition, fixed graph, Separation of attained values, then the admitted supremum and upper-bound transfer. Collection and witness rank bounds are later consumers when a set of witnesses is needed; they are not used to justify this value set.

The [exit checklist](k0-exit-checklist-2026-09.md) still requires the concrete adapter/completion compositions, representative membership/equality/congruence evidence and final integrated representation/assumption record. This batch does not declare K0 complete or expand it to include all of K4.

The source introduces no host Choice, countable/dependent choice, BPI, Zorn, resizing, ultrafilter selector or stronger LEM. The concrete instance takes only the existing `LEM (ℓ-suc ℓ)`, X, y and y's explicit validity evidence. Truncated existential elimination targets membership or an order proposition. The actual L set is obtained from the existing ground Separation operation; it is not extracted by choosing witnesses from the attained-value relation.

## Verification

The final safe checks exited 0 in the temporary compile root:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/FormulaParameters.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicValueSet.agda
```

The value-set check also validates its composition with the existing recognition, atomic graph, Separation and supremum interfaces. At most two Agda processes ran concurrently with the prescribed heap cap. Scoped prose/glossary gates, exact snapshots and hashes, local-link checks and `git diff --check` passed. All 123 tracked production sources and their copied probe-baseline sources match `72d01001` byte-for-byte. Whole-tree and trilingual chapter gates were not run for this temporary-probe/documentation change.

## Source snapshots

### FormulaParameters.agda

SHA-256: `210ca6683188bcb5b473129ce0232ebd3f212232eff92fc042b514865f3b94c5`.

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

substitute-reading : ∀ {n m} (σ : Fin n → Term S m) (φ : Formula S n)
  (γ : S ^ m) (δ : S ^ n) → (∀ i → ⟦ σ i ⟧ γ ≡ lookup i δ)
  → (γ ⊨ substitute σ φ) ≡ (δ ⊨ φ)
substitute-reading = ⊨-substitute

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

### PowersetAtomicValueSet.agda

SHA-256: `54f014886bec06e883df7a6c8ae83162bae9b3c4bd9f2040bea3e9d45cbba039`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicValueSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Term; Formula; var; con; _∧̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FormulaParameters
import NameRecognition
import NameClosure
import ClosedNamePairDomain
import PowersetAtomicGraph
import PowersetAtomicGraphFormula
import InternalPowersetSupremum
import FixedValueSet
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module For (X y : S)
  (validY : ⟨ ClosedNamePairDomain.For.Names.IsName lem
    (InternalPowersetSupremum.For.B lem X) y ⟩) where

  module Algebra = InternalPowersetSupremum.For lem X
    using ( B; Order; supremum; supremum-correct; module Supremum )
  module Recognition = NameRecognition.Recognition lem Algebra.B using ( formula )
  module Closure = NameClosure.For lem Algebra.B using ( adequate )
  module Atomic = PowersetAtomicGraph.For lem X
    using ( Graph; graph-prop; module AtNames )
  module AtomicFormula = PowersetAtomicGraphFormula.For lem X
    using ( formula; formula-reading )
  module Parameters = FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ
    using ( substitute; substitute-reading )

  nameTerms : Fin 1 → Term S 2
  nameTerms zero = var zero

  graphTerms : Fin 3 → Term S 2
  graphTerms zero = var zero
  graphTerms (suc zero) = con y
  graphTerms (suc (suc zero)) = var (suc zero)

  formula : Formula S 2
  formula = Parameters.substitute nameTerms Recognition.formula
    ∧̇ Parameters.substitute graphTerms AtomicFormula.formula

  name-reading : ∀ x b →
    ((x ∷ b ∷ []) ⊨ Parameters.substitute nameTerms Recognition.formula)
      ≡ ClosedNamePairDomain.For.Names.IsName lem Algebra.B x
  name-reading x b = Parameters.substitute-reading nameTerms Recognition.formula
    (x ∷ b ∷ []) (x ∷ []) (λ { zero → refl }) ∙ Closure.adequate x

  graph-reading : ∀ x b →
    ((x ∷ b ∷ []) ⊨ Parameters.substitute graphTerms AtomicFormula.formula)
      ≡ Atomic.graph-prop x y b
  graph-reading x b = Parameters.substitute-reading graphTerms AtomicFormula.formula
    (x ∷ b ∷ []) (x ∷ y ∷ b ∷ [])
    (λ { zero → refl ; (suc zero) → refl ; (suc (suc zero)) → refl })
    ∙ AtomicFormula.formula-reading x y b

  formula-reading : ∀ x b → ((x ∷ b ∷ []) ⊨ formula)
    ≡ (ClosedNamePairDomain.For.Names.IsName lem Algebra.B x
      ⊓ Atomic.graph-prop x y b)
  formula-reading x b = cong₂ _⊓_ (name-reading x b) (graph-reading x b)

  module Values = FixedValueSet.Construction 𝒮ʟ
    (InternalPowersetSupremum.actualL lem) Algebra.B formula

  Name : Type (ℓ-suc ℓ)
  Name = Σ[ x ∈ S ] ⟨ ClosedNamePairDomain.For.Names.IsName lem Algebra.B x ⟩

  value : Name → S
  value n = Atomic.AtNames.value (fst n) y (snd n) validY

  value-in-B : ∀ n → ⟨ value n ∈ˢ Algebra.B ⟩
  value-in-B n = Atomic.AtNames.value-in-B (fst n) y (snd n) validY

  represented : ∀ n → ∥ Σ[ x ∈ S ] Values.Graph x (value n) ∥₁
  represented n = ∣ fst n , subst ⟨_⟩
    (sym (formula-reading (fst n) (value n)))
    (snd n , Atomic.AtNames.exists (fst n) y (snd n) validY) ∣₁

  sound : ∀ x b → Values.Graph x b → ∥ Σ[ n ∈ Name ] value n ≡ b ∥₁
  sound x b holds = ∣ (x , fst parts) , sym equality ∣₁
    where
    parts : ⟨ ClosedNamePairDomain.For.Names.IsName lem Algebra.B x ⟩
      × Atomic.Graph x y b
    parts = subst ⟨_⟩ (formula-reading x b) holds

    equality : b ≡ Atomic.AtNames.value x y (fst parts) validY
    equality = subst ⟨_⟩ (Atomic.AtNames.exact x y (fst parts) validY b) (snd parts)

  module Adequacy = Values.Adequacy Name value value-in-B represented sound Algebra.Order

  values : S
  values = Values.values

  values-out : ∀ b → ⟨ b ∈ˢ values ⟩
    → ∥ Σ[ n ∈ Name ] value n ≡ b ∥₁
  values-out b member = PT.rec PT.squash₁
    (λ { (x , graph) → sound x b graph }) (snd (Values.out b member))

  values-in : ∀ b → ∥ Σ[ n ∈ Name ] value n ≡ b ∥₁
    → ⟨ b ∈ˢ values ⟩
  values-in b = PT.rec (snd (b ∈ˢ values))
    (λ { (n , eq) → subst (λ z → ⟨ z ∈ˢ values ⟩) eq (Adequacy.occurs n) })

  values-membership : ∀ b → (b ∈ˢ values)
    ≡ (∥ Σ[ n ∈ Name ] value n ≡ b ∥₁ , PT.squash₁)
  values-membership b = ⇔toPath (values-out b) (values-in b)

  bounded : ∀ b → ⟨ b ∈ˢ values ⟩ → ⟨ b ∈ˢ Algebra.B ⟩
  bounded b member = fst (Values.out b member)

  supremum : S
  supremum = Algebra.supremum values bounded

  supremum-correct : Algebra.Supremum.Supremum Algebra.B values supremum
  supremum-correct = Algebra.supremum-correct values bounded

  name-supremum : ⟨ supremum ∈ˢ Algebra.B ⟩
    × Adequacy.UpperNames supremum
    × (∀ c → ⟨ c ∈ˢ Algebra.B ⟩ → Adequacy.UpperNames c
      → ⟨ Algebra.Order supremum c ⟩)
  name-supremum = Adequacy.transferLUB supremum (fst supremum-correct)
    (fst (snd supremum-correct)) (snd (snd supremum-correct))
```
