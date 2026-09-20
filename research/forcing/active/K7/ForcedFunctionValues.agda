{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )

module K7.ForcedFunctionValues
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (Cond Name : Type ℓ)
  (order : Cond → Cond → hProp ℓ)
  (R : ∀ {n} → Cond → Formula (⊥* {ℓ}) n → Vec Name n → hProp ℓ)
  (M E : Cond → Name → Name → hProp ℓ)
  where

open import FOL.Syntax using
  ( con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; liftρ )
open import FOL.Manipulation.ParameterAbstraction using ( absFo )
import Cubical.HITs.PropositionalTruncation as PT
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
module CB = CardinalBridge 𝒮

Src : ℕ → Type ℓ
Src n = Formula (⊥* {ℓ}) n

Dense : Cond → (Cond → Ω) → Ω
Dense p W = ⋀ Cond (λ q → order q p ⇒ ⋁ Cond (λ r → order r q ⊓ W r))

-- These are the ten primitive forcing clauses, written as paths of
-- propositions. The companion module supplies every path directly from
-- K5.Clauses.ForcingClauses. No logical consequence is a field.
record Clauses : Type (ℓ-suc ℓ) where
  field
    at-∈ : ∀ {n} p (a b : Fin n) ν → R p (var a ∈̇ var b) ν ≡ M p (lookup a ν) (lookup b ν)
    at-≐ : ∀ {n} p (a b : Fin n) ν → R p (var a ≐ var b) ν ≡ E p (lookup a ν) (lookup b ν)
    at-⊥ : ∀ {n} p (ν : Vec Name n) → R p ⊥̇ ν ≡ ⊥
    at-∧ : ∀ {n} p (φ ψ : Src n) ν → R p (φ ∧̇ ψ) ν ≡ (R p φ ν ⊓ R p ψ ν)
    at-∨ : ∀ {n} p (φ ψ : Src n) ν → R p (φ ∨̇ ψ) ν ≡ Dense p (λ r → R r φ ν ⊔ R r ψ ν)
    at-⇒ : ∀ {n} p (φ ψ : Src n) ν → R p (φ ⇒̇ ψ) ν ≡ ⋀ Cond (λ q → order q p ⇒ (R q φ ν ⇒ R q ψ ν))
    at-∀ : ∀ {n} p (φ : Src (suc n)) ν → R p (∀̇ φ) ν ≡ ⋀ Name (λ σ → R p φ (σ ∷ ν))
    at-∃ : ∀ {n} p (φ : Src (suc n)) ν → R p (∃̇ φ) ν ≡ Dense p (λ r → ⋁ Name (λ σ → R r φ (σ ∷ ν)))
    at-∀∈ : ∀ {n} p (j : Fin n) (φ : Src (suc n)) ν → R p (∀̇∈ (var j) φ) ν
      ≡ ⋀ Cond (λ q → order q p ⇒ ⋀ Name (λ σ → M q σ (lookup j ν) ⇒ R q φ (σ ∷ ν)))
    at-∃∈ : ∀ {n} p (j : Fin n) (φ : Src (suc n)) ν → R p (∃̇∈ (var j) φ) ν
      ≡ Dense p (λ r → ⋁ Name (λ σ → M r σ (lookup j ν) ⊓ R r φ (σ ∷ ν)))

module AtClauses (C : Clauses) where
  open Clauses C

  Agrees : ∀ {n m} → (Fin n → Fin m) → Vec Name m → Vec Name n → Type ℓ
  Agrees ρ γ δ = ∀ j → lookup (ρ j) γ ≡ lookup j δ

  agrees∷ : ∀ {n m} {ρ : Fin n → Fin m} {γ δ} (σ : Name)
    → Agrees ρ γ δ → Agrees (liftρ ρ) (σ ∷ γ) (σ ∷ δ)
  agrees∷ σ h zero = refl
  agrees∷ σ h (suc j) = h j

  -- Renaming depends only on the values assigned to variables. Density in
  -- the existential and disjunctive clauses is preserved pointwise, and
  -- extending both environments preserves agreement beneath each binder.
  rename-forcing : ∀ {n m} p (ρ : Fin n → Fin m) (φ : Src n) γ δ
    → Agrees ρ γ δ → R p (renameFo ρ φ) γ ≡ R p φ δ
  rename-forcing p ρ (con () ∈̇ u) γ δ h
  rename-forcing p ρ (var a ∈̇ con ()) γ δ h
  rename-forcing p ρ (var a ∈̇ var b) γ δ h =
    at-∈ p (ρ a) (ρ b) γ ∙ cong₂ (M p) (h a) (h b) ∙ sym (at-∈ p a b δ)
  rename-forcing p ρ (con () ≐ u) γ δ h
  rename-forcing p ρ (var a ≐ con ()) γ δ h
  rename-forcing p ρ (var a ≐ var b) γ δ h =
    at-≐ p (ρ a) (ρ b) γ ∙ cong₂ (E p) (h a) (h b) ∙ sym (at-≐ p a b δ)
  rename-forcing p ρ (φ ∧̇ ψ) γ δ h =
    at-∧ p _ _ γ ∙ cong₂ _⊓_ (rename-forcing p ρ φ γ δ h) (rename-forcing p ρ ψ γ δ h) ∙ sym (at-∧ p φ ψ δ)
  rename-forcing p ρ (φ ∨̇ ψ) γ δ h =
    at-∨ p _ _ γ ∙ cong (Dense p) (funExt (λ r → cong₂ _⊔_ (rename-forcing r ρ φ γ δ h) (rename-forcing r ρ ψ γ δ h))) ∙ sym (at-∨ p φ ψ δ)
  rename-forcing p ρ (φ ⇒̇ ψ) γ δ h =
    at-⇒ p _ _ γ ∙ cong (⋀ Cond) (funExt (λ q → cong (order q p ⇒_) (cong₂ _⇒_ (rename-forcing q ρ φ γ δ h) (rename-forcing q ρ ψ γ δ h)))) ∙ sym (at-⇒ p φ ψ δ)
  rename-forcing p ρ ⊥̇ γ δ h = at-⊥ p γ ∙ sym (at-⊥ p δ)
  rename-forcing p ρ (∀̇ φ) γ δ h =
    at-∀ p _ γ ∙ cong (⋀ Name) (funExt (λ σ → rename-forcing p (liftρ ρ) φ (σ ∷ γ) (σ ∷ δ) (agrees∷ σ h))) ∙ sym (at-∀ p φ δ)
  rename-forcing p ρ (∃̇ φ) γ δ h =
    at-∃ p _ γ ∙ cong (Dense p) (funExt (λ r → cong (⋁ Name) (funExt (λ σ → rename-forcing r (liftρ ρ) φ (σ ∷ γ) (σ ∷ δ) (agrees∷ σ h))))) ∙ sym (at-∃ p φ δ)
  rename-forcing p ρ (∀̇∈ (con ()) φ) γ δ h
  rename-forcing p ρ (∀̇∈ (var j) φ) γ δ h =
    at-∀∈ p _ _ γ ∙ cong (⋀ Cond) (funExt (λ q → cong (order q p ⇒_) (cong (⋀ Name) (funExt (λ σ → cong₂ _⇒_ (cong (M q σ) (h j)) (rename-forcing q (liftρ ρ) φ (σ ∷ γ) (σ ∷ δ) (agrees∷ σ h))))))) ∙ sym (at-∀∈ p j φ δ)
  rename-forcing p ρ (∃̇∈ (con ()) φ) γ δ h
  rename-forcing p ρ (∃̇∈ (var j) φ) γ δ h =
    at-∃∈ p _ _ γ ∙ cong (Dense p) (funExt (λ r → cong (⋁ Name) (funExt (λ σ → cong₂ _⊓_ (cong (M r σ) (h j)) (rename-forcing r (liftρ ρ) φ (σ ∷ γ) (σ ∷ δ) (agrees∷ σ h)))))) ∙ sym (at-∃∈ p j φ δ)

  pairFo : Src 3
  pairFo = absFo CB.PairφK

  functionFo : Src 1
  functionFo = absFo CB.IsFunctionφ

  embed : Fin 3 → Fin 4
  embed zero = zero
  embed (suc zero) = suc zero
  embed (suc (suc zero)) = suc (suc zero)

  valueBody : Src 4
  valueBody = renameFo embed pairFo ∧̇ (var zero ∈̇ var (suc (suc (suc zero))))

  -- The free slots are coordinate, value, and graph. The pair predicate is
  -- the same biconditional Kuratowski formula used by IsFunctionφ.
  valueFo : Src 3
  valueFo = ∃̇ valueBody

  singleBody : Src 6
  singleBody = (renameFo CB.fn-pair₁ pairFo ∧̇ renameFo CB.fn-pair₂ pairFo)
    ⇒̇ (var (suc zero) ≐ var zero)

  uniquenessBody : Src 1
  uniquenessBody = ∀̇∈ (var zero) (∀̇∈ (var (suc zero)) (∀̇ (∀̇ (∀̇ singleBody))))

  function-shape : functionFo ≡ (absFo CB.IsRelationφ ∧̇ uniquenessBody)
  function-shape = refl

  module AtOrder
    (order-refl : ∀ p → ⟨ order p p ⟩)
    (order-trans : ∀ r q p → ⟨ order r q ⟩ → ⟨ order q p ⟩ → ⟨ order r p ⟩)
    (mono : ∀ {n} p q (φ : Src n) ν → ⟨ order q p ⟩ → ⟨ R p φ ν ⟩ → ⟨ R q φ ν ⟩)
    (regular : ∀ {n} p (φ : Src n) ν → ⟨ Dense p (λ r → R r φ ν) ⟩ → ⟨ R p φ ν ⟩)
    where

    pair-at : ∀ p π x y f → ⟨ R p valueBody (π ∷ x ∷ y ∷ f ∷ []) ⟩
      → ⟨ R p pairFo (π ∷ x ∷ y ∷ []) ⟩ × ⟨ M p π f ⟩
    pair-at p π x y f h =
      subst ⟨_⟩ (rename-forcing p embed pairFo _ _ agrees) (fst a)
      , subst ⟨_⟩ (at-∈ p zero (suc (suc (suc zero))) _) (snd a)
      where
      a : ⟨ R p (renameFo embed pairFo) (π ∷ x ∷ y ∷ f ∷ []) ⟩
        × ⟨ R p (var zero ∈̇ var (suc (suc (suc zero)))) (π ∷ x ∷ y ∷ f ∷ []) ⟩
      a = subst ⟨_⟩ (at-∧ p _ _ _) h
      agrees : Agrees embed (π ∷ x ∷ y ∷ f ∷ []) (π ∷ x ∷ y ∷ [])
      agrees zero = refl
      agrees (suc zero) = refl
      agrees (suc (suc zero)) = refl

    -- Once both graph pairs are witnessed at one condition, the two bounded
    -- universals and three ordinary universals in IsFunctionφ instantiate
    -- directly. Reflexivity of refinement discharges the implication guard.
    witnesses-equal : ∀ p f x y z π κ
      → ⟨ R p functionFo (f ∷ []) ⟩
      → ⟨ R p valueBody (π ∷ x ∷ y ∷ f ∷ []) ⟩
      → ⟨ R p valueBody (κ ∷ x ∷ z ∷ f ∷ []) ⟩
      → ⟨ E p y z ⟩
    witnesses-equal p f x y z π κ hf hy hz =
      subst ⟨_⟩ (at-≐ p (suc zero) zero _) (imp p (order-refl p) pairs)
      where
      a : ⟨ R p pairFo (π ∷ x ∷ y ∷ []) ⟩ × ⟨ M p π f ⟩
      a = pair-at p π x y f hy
      b : ⟨ R p pairFo (κ ∷ x ∷ z ∷ []) ⟩ × ⟨ M p κ f ⟩
      b = pair-at p κ x z f hz
      u : ⟨ R p uniquenessBody (f ∷ []) ⟩
      u = snd (subst ⟨_⟩ (at-∧ p _ _ (f ∷ [])) (subst (λ φ → ⟨ R p φ (f ∷ []) ⟩) function-shape hf))
      v : ⟨ R p (∀̇∈ (var (suc zero)) (∀̇ (∀̇ (∀̇ singleBody)))) (π ∷ f ∷ []) ⟩
      v = subst ⟨_⟩ (at-∀∈ p zero _ _) u p (order-refl p) π (snd a)
      w : ⟨ R p (∀̇ (∀̇ (∀̇ singleBody))) (κ ∷ π ∷ f ∷ []) ⟩
      w = subst ⟨_⟩ (at-∀∈ p (suc zero) _ _) v p (order-refl p) κ (snd b)
      j : ⟨ R p (∀̇ (∀̇ singleBody)) (x ∷ κ ∷ π ∷ f ∷ []) ⟩
      j = subst ⟨_⟩ (at-∀ p _ _) w x
      k : ⟨ R p (∀̇ singleBody) (y ∷ x ∷ κ ∷ π ∷ f ∷ []) ⟩
      k = subst ⟨_⟩ (at-∀ p _ _) j y
      l : ⟨ R p singleBody (z ∷ y ∷ x ∷ κ ∷ π ∷ f ∷ []) ⟩
      l = subst ⟨_⟩ (at-∀ p _ _) k z
      imp : (q : Cond) → ⟨ order q p ⟩
        → ⟨ R q (renameFo CB.fn-pair₁ pairFo ∧̇ renameFo CB.fn-pair₂ pairFo) (z ∷ y ∷ x ∷ κ ∷ π ∷ f ∷ []) ⟩
        → ⟨ R q (var (suc zero) ≐ var zero) (z ∷ y ∷ x ∷ κ ∷ π ∷ f ∷ []) ⟩
      imp = subst ⟨_⟩ (at-⇒ p _ _ _) l
      ag₁ : Agrees CB.fn-pair₁ (z ∷ y ∷ x ∷ κ ∷ π ∷ f ∷ []) (π ∷ x ∷ y ∷ [])
      ag₁ zero = refl
      ag₁ (suc zero) = refl
      ag₁ (suc (suc zero)) = refl
      ag₂ : Agrees CB.fn-pair₂ (z ∷ y ∷ x ∷ κ ∷ π ∷ f ∷ []) (κ ∷ x ∷ z ∷ [])
      ag₂ zero = refl
      ag₂ (suc zero) = refl
      ag₂ (suc (suc zero)) = refl
      pairs : ⟨ R p (renameFo CB.fn-pair₁ pairFo ∧̇ renameFo CB.fn-pair₂ pairFo) (z ∷ y ∷ x ∷ κ ∷ π ∷ f ∷ []) ⟩
      pairs = subst ⟨_⟩ (sym (at-∧ p _ _ _))
        (subst ⟨_⟩ (sym (rename-forcing p CB.fn-pair₁ pairFo _ _ ag₁)) (fst a)
        , subst ⟨_⟩ (sym (rename-forcing p CB.fn-pair₂ pairFo _ _ ag₂)) (fst b))

    -- Below any refinement, the first existential yields a graph-pair
    -- witness densely. Refine again for the second witness, carrying the
    -- first witness and functionality down by monotonicity. Equality then
    -- holds densely below the original condition, so regularity forces it
    -- there. Every existential elimination targets a proposition.
    forced-function-values : ∀ p f x y z
      → ⟨ R p functionFo (f ∷ []) ⟩
      → ⟨ R p valueFo (x ∷ y ∷ f ∷ []) ⟩
      → ⟨ R p valueFo (x ∷ z ∷ f ∷ []) ⟩
      → ⟨ E p y z ⟩
    forced-function-values p f x y z hf hy hz =
      subst ⟨_⟩ (at-≐ p zero (suc zero) (y ∷ z ∷ []))
        (regular p (var zero ≐ var (suc zero)) (y ∷ z ∷ []) dense)
      where
      target : Cond → Ω
      target r = R r (var zero ≐ var (suc zero)) (y ∷ z ∷ [])
      dense : ⟨ Dense p target ⟩
      dense q hqp = PT.rec (snd (⋁ Cond (λ r → order r q ⊓ target r)))
        (λ { (r , hrq , hπ) → PT.rec (snd (⋁ Cond (λ s → order s q ⊓ target s)))
          (λ { (π , hπ) → PT.rec (snd (⋁ Cond (λ s → order s q ⊓ target s)))
            (λ { (s , hsr , hκ) → PT.map (λ { (κ , hκ) → s , order-trans s r q hsr hrq
              , subst ⟨_⟩ (sym (at-≐ s zero (suc zero) (y ∷ z ∷ [])))
                  (witnesses-equal s f x y z π κ
                    (mono p s functionFo (f ∷ []) (order-trans s r p hsr (order-trans r q p hrq hqp)) hf)
                    (mono r s valueBody (π ∷ x ∷ y ∷ f ∷ []) hsr hπ) hκ) }) hκ })
            (subst ⟨_⟩ (at-∃ r valueBody (x ∷ z ∷ f ∷ []))
              (mono p r valueFo (x ∷ z ∷ f ∷ []) (order-trans r q p hrq hqp) hz)
              r (order-refl r)) }) hπ })
        (subst ⟨_⟩ (at-∃ p valueBody (x ∷ y ∷ f ∷ [])) hy q hqp)
