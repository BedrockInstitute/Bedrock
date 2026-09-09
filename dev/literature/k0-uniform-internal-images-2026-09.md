# K0 uniform internal weighted images

Date: 2026-09-09. Source baseline: `e699bdac`. Four safe temporary probes checked. This continues the [indexed image formulas](k0-indexed-images-suprema-2026-09.md). K0 remains open.

## Checked results

`FormulaParameters` implements capture-avoiding substitution and parameter specialization for any supplied truth algebra and ZF structure. The proof follows all formula constructors, including bounded and unbounded quantifiers. Its public specialization takes n actual parameters and a formula with n + 1 variables, leaving one free variable. The reading theorem identifies its truth value with the original formula interpreted in the concatenated environment. It requires neither LEM nor Choice, and introduces no quantifiers. This is a semantics lemma, not a logical proof calculus or completeness theorem. The specialization does not remove the unbounded key existential already present in the weighted-image template.

`UniformWeightedImage`, under exactly `LEM (ℓ-suc ℓ)`, specializes the existing six-variable image template at C, B, parent, H and f, then applies actual L Separation to B. Its image is an actual member of the L carrier, with exact membership:

    z belongs to image iff z belongs to B and
      merely some v in C, c in B, d in B satisfy
      pair(v,c) in parent, pair(Key(f,v),d) in H, Op(c,d,z).

The output guard is supplied by Separation. No operation totality, selected witness family, or host-family image closure is assumed. The same implementation constructs both orientations:

| Interface | Fixed parameter | Parent being enumerated | Table key |
| --- | --- | --- | --- |
| ForwardKey | u | y, with pair(v,c) in y | pair(u,v) |
| ReverseKey | v | x, with pair(u,a) in x | pair(u,v) |

The module also supplies `imageSetAt I C B parent H f`, with six variable indices and an arbitrary-environment reading theorem. `Description.exact` proves that satisfying this formula is equivalent to I being literally equal to the constructed image. This supplies both a model-internal formula describing the image and an actual realization; it is stronger than a standalone witness-predicate reading theorem. The proof uses ground extensionality, not an external choice operation.

`Congruence` proves equality of the actual images whenever H and K have equivalent graph membership at the relevant keys and B-values. One proof handles both orientations. `UniformPredecessorImages` then obtains both image equalities from the previously checked predecessor coverage and cross-table value agreement. It reuses that graph-transfer lemma; it does not introduce a new choice-like locality premise.

`WeightedImageComparison` proves the new forward image is literally equal to the earlier `WeightedTableImage` image. Their syntactic constructions differ, but their exact membership specifications agree. This justifies consolidating future image construction on the uniform implementation. The previous constant-parameter, singleton/product-bound image remains historical evidence, not a second intended production proof home.

## Architecture and remaining obligations

The proof homes are now separated by purpose: generic formula substitution, the indexed weighted-image syntax, actual image realization and congruence, and adapters from name-pair predecessor agreement. Both image orientations share those components. Temporary probes still import historical modules for reusable predecessor lemmas; production extraction should separate that graph-transfer lemma from its old image consumer rather than preserve a compatibility shell.

The operation relation and its finite syntax are still parameters. No actual internal Boolean meet/order/completeness instance is established here. Empty images are allowed and correctly specified, but there is no theorem yet providing their Boolean suprema. The [relative supremum formula](k0-indexed-images-suprema-2026-09.md) likewise gives a reading theorem rather than existence.

Next work:

1. Supply actual internal Boolean operation/order laws and relative completeness, including the empty family, with all choice confined to the object model where justified.
2. Compose the image-set description with relative supremum syntax, then build outer implication images and infima to describe the complete atomic Step.
3. Prove Step admissibility, uniqueness and locality, and instantiate the checked real-name-pair recursion engine.
4. Prove closed-domain independence and atomic semantic adequacy; then continue the general forcing framework, model construction and geology route.

The third trophy remains an actual ordinary model of ZFC + not-CH, following general forcing results; the fourth remains ground definability. None of these endpoint results is claimed by these probes. The final whole-program LEM-only budget is still under audit.

## Verification and source snapshots

In `/tmp/bedrock-k0-probes/extraction/compile-root`, these commands exited 0:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/FormulaParameters.agda
GHCRTS="-A64m -I0 -M8g" agda src/WeightedImageComparison.agda
GHCRTS="-A64m -I0 -M8g" agda src/UniformPredecessorImages.agda
```

The last two commands also checked the imported final parameter-specialization and uniform-image sources. The final generic helper names are `renameTerm` and `substituteTerm`. All four files retain `--safe`. Source snapshots below are the checked temporary files; no production source was changed. Scoped prose/glossary gates, snapshot/hash checks and `git diff --check` passed. The 123 tracked source files and their copied probe-baseline versions match the baseline byte-for-byte. No whole-tree or chapter gate was run for this documentation and temporary-probe change.

### FormulaParameters.agda

SHA-256: `39d5f2aee417f2615a5a5a286d1e2d306d2024fe38e3a0f4df5705bf87eb21d9`.

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

parameters : ∀ {n} → Vec S n → Fin (n + 1) → Term S 1
parameters []        zero    = var zero
parameters (x ∷ δ)  zero    = con x
parameters (x ∷ δ)  (suc i) = parameters δ i

specialize : ∀ {n} → Vec S n → Formula S (n + 1) → Formula S 1
specialize δ = substitute (parameters δ)

private
  parameters-agree : ∀ {n} (δ : Vec S n) (z : S) (i : Fin (n + 1))
                   → ⟦ parameters δ i ⟧ (z ∷ [])
                   ≡ lookup i (δ ++ (z ∷ []))
  parameters-agree []       z zero    = refl
  parameters-agree (x ∷ δ) z zero    = refl
  parameters-agree (x ∷ δ) z (suc i) = parameters-agree δ z i

specialize-reading : ∀ {n} (δ : Vec S n) (φ : Formula S (n + 1)) (z : S)
                   → ((z ∷ []) ⊨ specialize δ φ)
                   ≡ ((δ ++ (z ∷ [])) ⊨ φ)
specialize-reading δ φ z =
  ⊨-substitute (parameters δ) φ (z ∷ []) (δ ++ (z ∷ []))
    (parameters-agree δ z)
```

### UniformWeightedImage.agda

SHA-256: `ef939eb9a60ac7730f3fe660c52d9a4e2c8dc81113aa3522b06f33ec21725f6c`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module UniformWeightedImage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL )
open import PairFormulaReading {ℓ} using ( reading )
import IndexedWeightedImage {ℓ} as Indexed
open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( specialize; specialize-reading )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

opaque
  actualL : Model.isZFModel 𝒮ʟ
  actualL = L⊨ZF

module Ground = Model.isZFModel actualL

module WithKey
  (Key : S → S → S)
  (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
    → (γ ⊨ keyAt q f v)
      ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
         isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ)))) where

  module WithOperation
    (Op : S → S → S → hProp (ℓ-suc ℓ))
    (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
      → (γ ⊨ opAt c d z) ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

    module Syntax = Indexed.WithKey.WithOperation Key keyAt key-reading Op opAt op-reading

    template : Formula S 6
    template = Syntax.imageAt zero (suc zero) (suc (suc zero))
      (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc zero)))))

    module Construction (C B parent H f : S) where

      parameters : Vec S 5
      parameters = C ∷ B ∷ parent ∷ H ∷ f ∷ []

      formula : Formula S 1
      formula = specialize parameters template

      Witness : S → Type (ℓ-suc ℓ)
      Witness = Syntax.truncatedWitness C B parent H f

      formula-reading : ∀ z → ((z ∷ []) ⊨ formula) ≡ (Witness z , PT.squash₁)
      formula-reading z = specialize-reading parameters template z
        ∙ Syntax.imageAt-reading zero (suc zero) (suc (suc zero))
          (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
          (suc (suc (suc (suc (suc zero)))) )
          (C ∷ B ∷ parent ∷ H ∷ f ∷ z ∷ [])

      image : S
      image = Ground.separate B formula

      separated : ∀ z → ⟨ z ∈ˢ image ⟩
        → ⟨ z ∈ˢ B ⟩ × ⟨ (z ∷ []) ⊨ formula ⟩
      separated z member = subst ⟨_⟩ (Ground.separate-spec B formula z) member

      image-out : ∀ z → ⟨ z ∈ˢ image ⟩ → ⟨ z ∈ˢ B ⟩ × Witness z
      image-out z member = fst (separated z member) ,
        subst ⟨_⟩ (formula-reading z) (snd (separated z member))

      image-in : ∀ z → ⟨ z ∈ˢ B ⟩ → Witness z → ⟨ z ∈ˢ image ⟩
      image-in z zB witness = subst ⟨_⟩ (sym (Ground.separate-spec B formula z))
        (zB , subst ⟨_⟩ (sym (formula-reading z)) witness)

      image-membership : ∀ z → (z ∈ˢ image) ≡ ((z ∈ˢ B) ⊓ (Witness z , PT.squash₁))
      image-membership z = ⇔toPath (image-out z)
        (λ { (zB , witness) → image-in z zB witness })

    imageSetAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
      → Formula S n
    imageSetAt I C B parent H f = ∀̇
      (((var zero ∈̇ var (suc I)) ⇒̇
        ((var zero ∈̇ var (suc B)) ∧̇ Syntax.imageAt (suc C) (suc B)
          (suc parent) (suc H) (suc f) zero)) ∧̇
       (((var zero ∈̇ var (suc B)) ∧̇ Syntax.imageAt (suc C) (suc B)
          (suc parent) (suc H) (suc f) zero) ⇒̇ (var zero ∈̇ var (suc I))))

    module Description {n : ℕ} (I C B parent H f : Fin n) (γ : Vec S n) where

      module Actual = Construction (lookup C γ) (lookup B γ) (lookup parent γ)
        (lookup H γ) (lookup f γ)

      out : ⟨ γ ⊨ imageSetAt I C B parent H f ⟩ → lookup I γ ≡ Actual.image
      out holds = Ground.extensional λ z → ⇔toPath
        (λ member → Actual.image-in z (fst (fst (holds z) member))
          (Syntax.imageAt-out (suc C) (suc B) (suc parent) (suc H) (suc f) zero
            (z ∷ γ) (snd (fst (holds z) member))))
        (λ member → snd (holds z) (fst (Actual.image-out z member) ,
          Syntax.imageAt-in (suc C) (suc B) (suc parent) (suc H) (suc f) zero
            (z ∷ γ) (snd (Actual.image-out z member))))

      into : lookup I γ ≡ Actual.image → ⟨ γ ⊨ imageSetAt I C B parent H f ⟩
      into eq z =
        (λ member → fst (Actual.image-out z (subst (λ A → ⟨ z ∈ˢ A ⟩) eq member)) ,
          Syntax.imageAt-in (suc C) (suc B) (suc parent) (suc H) (suc f) zero
            (z ∷ γ) (snd (Actual.image-out z (subst (λ A → ⟨ z ∈ˢ A ⟩) eq member)))) ,
        (λ { (zB , witness) → subst (λ A → ⟨ z ∈ˢ A ⟩) (sym eq)
          (Actual.image-in z zB (Syntax.imageAt-out (suc C) (suc B)
            (suc parent) (suc H) (suc f) zero (z ∷ γ) witness)) })

      exact : (γ ⊨ imageSetAt I C B parent H f)
        ≡ ((lookup I γ ≡ Actual.image) , isSetS (lookup I γ) Actual.image)
      exact = ⇔toPath out into

    module Congruence (C B parent H K f : S)
      (agrees : ∀ v c d → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
        → ⟨ prʟ v c ∈ˢ parent ⟩
        → (⟨ prʟ (Key f v) d ∈ˢ H ⟩ → ⟨ prʟ (Key f v) d ∈ˢ K ⟩)
          × (⟨ prʟ (Key f v) d ∈ˢ K ⟩ → ⟨ prʟ (Key f v) d ∈ˢ H ⟩)) where

      module Left = Construction C B parent H f
      module Right = Construction C B parent K f

      forward : ∀ z → ⟨ z ∈ˢ Left.image ⟩ → ⟨ z ∈ˢ Right.image ⟩
      forward z member = Right.image-in z (fst (Left.image-out z member))
        (PT.map (λ { (v , c , d , vC , cB , dB , vc , hd , op) →
          v , c , d , vC , cB , dB , vc , fst (agrees v c d vC cB dB vc) hd , op })
          (snd (Left.image-out z member)))

      backward : ∀ z → ⟨ z ∈ˢ Right.image ⟩ → ⟨ z ∈ˢ Left.image ⟩
      backward z member = Left.image-in z (fst (Right.image-out z member))
        (PT.map (λ { (v , c , d , vC , cB , dB , vc , kd , op) →
          v , c , d , vC , cB , dB , vc , snd (agrees v c d vC cB dB vc) kd , op })
          (snd (Right.image-out z member)))

      image-equal : Left.image ≡ Right.image
      image-equal = Ground.extensional (λ z → ⇔toPath (forward z) (backward z))

module ForwardKey = WithKey prʟ prAtL reading
module ReverseKey = WithKey (λ f v → prʟ v f) Indexed.reverseKeyAt Indexed.reverse-key-reading
```

### UniformPredecessorImages.agda

SHA-256: `187f2c7d5d13de553ad3f79462e164d43b876bf1ad9807facaacc28a1f82e418`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module UniformPredecessorImages {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import UniformWeightedImage
import WeightedPredecessorAgreement
open import NameClosureDown lem using ( Child )
import PredecessorValueAgreement

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module Tables (C B H K x y : S) (xC : ⟨ x ∈ˢ C ⟩) (yC : ⟨ y ∈ˢ C ⟩) where

  module Previous = WeightedPredecessorAgreement.Tables lem C B H K x y xC yC

  module Agreement (coversH : Previous.Covers H) (coversK : Previous.Covers K)
    (same : Previous.Same) where

    module Transfer = Previous.Agreement coversH coversK same

    module WithOperation
      (Op : S → S → S → hProp (ℓ-suc ℓ))
      (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
      (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
        → (γ ⊨ opAt c d z) ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

      module Forward = UniformWeightedImage.ForwardKey.WithOperation lem Op opAt op-reading
      module Reverse = UniformWeightedImage.ReverseKey.WithOperation lem Op opAt op-reading

      module LeftImage (u : S) (uC : ⟨ u ∈ˢ C ⟩) (left : Child u x) where

        module Images = Forward.Congruence C B y H K u (Transfer.left-image u uC left)

        image-equal : Images.Left.image ≡ Images.Right.image
        image-equal = Images.image-equal

      module RightImage (v : S) (vC : ⟨ v ∈ˢ C ⟩) (right : Child v y) where

        module Images = Reverse.Congruence C B x H K v (Transfer.right-image v vC right)

        image-equal : Images.Left.image ≡ Images.Right.image
        image-equal = Images.image-equal
```

### WeightedImageComparison.agda

SHA-256: `292d1baa691469b4f4a52210647536e6a308b5de5ce0cb2aeeb251021629f2d1`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module WeightedImageComparison {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import UniformWeightedImage
import WeightedTableImage
import PredecessorValueAgreement
open import Cubical.Functions.Logic using ( ⇔toPath )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module Comparison (C B y H u : S)
  (Op : S → S → S → hProp (ℓ-suc ℓ))
  (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
    → (γ ⊨ opAt c d z) ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

  module Previous = WeightedTableImage.Construction lem C B y H u Op opAt op-reading
  module Shared = UniformWeightedImage.ForwardKey.WithOperation lem Op opAt op-reading
  module Current = Shared.Construction C B y H u

  forward : ∀ z → ⟨ z ∈ˢ Previous.image ⟩ → ⟨ z ∈ˢ Current.image ⟩
  forward z member = Current.image-in z (fst (Previous.image-out z member))
    (snd (Previous.image-out z member))

  backward : ∀ z → ⟨ z ∈ˢ Current.image ⟩ → ⟨ z ∈ˢ Previous.image ⟩
  backward z member = Previous.image-in z (fst (Current.image-out z member))
    (snd (Current.image-out z member))

  image-equal : Previous.image ≡ Current.image
  image-equal = UniformWeightedImage.Ground.extensional lem
    (λ z → ⇔toPath (forward z) (backward z))
```
