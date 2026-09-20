{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K10.BooleanPairFormula
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ∀̇∈ )
open import FOL.Manipulation.ParameterAbstraction using ( absFo )
import CardinalBridge
import K4.Algebra
import K4.Implication
import K9.BooleanNameGround
import K10.BooleanPairs

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module CB = CardinalBridge 𝒮
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B; module NG; module IC; module BK; module Atomic; module Laws; module Translation )
module Pairs = K10.BooleanPairs 𝒮 families accessible images pow κ w lem
  using ( singleB; pairB; singleB-name; pairB-name; singleB-member-value; pairB-member-value )
open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans )
open K4.Algebra.Lattice BG.IC.codedLattice
open K4.Implication 𝒮 BG.NG.extensional BG.NG.≈ˢ-paths
  BG.B BG.IC.codedLattice BG.IC.codedComplement
  using ( _⇒ᴮ_; ≤ᴮ-antisym; ⇒ᴮ-curry )
open BG.Atomic using () renaming ( _≈ᴮ_ to eq; _∈ᴮ_ to mem )

Nameᴮ : Type ℓ
Nameᴮ = Σ[ x ∈ S ] ⟨ BG.BK.IsName x ⟩

Envᴮ : ℕ → Type ℓ
Envᴮ n = Vec Nameᴮ n

singletonφ : Formula (⊥* {ℓ}) 2
singletonφ = absFo CB.IsSingletonφ

pairφ : Formula (⊥* {ℓ}) 3
pairφ = absFo CB.IsPairφ

private
  singleton-memberφ : Formula (⊥* {ℓ}) 2
  singleton-memberφ = var (suc zero) ∈̇ var zero

  singleton-onlyφ : Formula (⊥* {ℓ}) 2
  singleton-onlyφ = ∀̇∈ (var zero) (var zero ≐ var (suc (suc zero)))

  singleton-shape : singletonφ ≡ (singleton-memberφ ∧̇ singleton-onlyφ)
  singleton-shape = refl

  pair-leftφ : Formula (⊥* {ℓ}) 3
  pair-leftφ = var (suc zero) ∈̇ var zero

  pair-rightφ : Formula (⊥* {ℓ}) 3
  pair-rightφ = var (suc (suc zero)) ∈̇ var zero

  pair-onlyφ : Formula (⊥* {ℓ}) 3
  pair-onlyφ = ∀̇∈ (var zero)
    ((var zero ≐ var (suc (suc zero)))
      ∨̇ (var zero ≐ var (suc (suc (suc zero)))))

  pair-shape : pairφ ≡ (pair-leftφ ∧̇ (pair-rightφ ∧̇ pair-onlyφ))
  pair-shape = refl

module Value
  (value : ∀ {n} → Formula (⊥* {ℓ}) n → Envᴮ n → Pt BG.B)
  (law-∈ : ∀ {n} (i j : Fin n) (ν : Envᴮ n)
    → value (var i ∈̇ var j) ν
      ≡ mem (fst (lookup i ν)) (fst (lookup j ν)))
  (law-≐ : ∀ {n} (i j : Fin n) (ν : Envᴮ n)
    → value (var i ≐ var j) ν
      ≡ eq (fst (lookup i ν)) (fst (lookup j ν)))
  (law-∧ : ∀ {n} (φ ψ : Formula (⊥* {ℓ}) n) (ν : Envᴮ n)
    → value (φ ∧̇ ψ) ν ≡ (value φ ν ⊓ᴮ value ψ ν))
  (law-∨ : ∀ {n} (φ ψ : Formula (⊥* {ℓ}) n) (ν : Envᴮ n)
    → value (φ ∨̇ ψ) ν ≡ (value φ ν ⊔ᴮ value ψ ν))
  (law-∀∈-glb : ∀ {n} (i : Fin n) (φ : Formula (⊥* {ℓ}) (suc n))
    (ν : Envᴮ n) (c : Pt BG.B)
    → ((σ : Nameᴮ) → ⟨ c ≤ᴮ
        (mem (fst σ) (fst (lookup i ν)) ⇒ᴮ value φ (σ ∷ ν)) ⟩)
    → ⟨ c ≤ᴮ value (∀̇∈ (var i) φ) ν ⟩)
  where

  translated-name : BG.NG.K.Name → Nameᴮ
  translated-name σ = BG.Translation.trᴮ (fst σ)
    , BG.Translation.trᴮ-name (fst σ) (snd σ)

  singleton-name : BG.NG.K.Name → Nameᴮ
  singleton-name σ = Pairs.singleB (fst σ) , Pairs.singleB-name σ

  pair-name : BG.NG.K.Name → BG.NG.K.Name → Nameᴮ
  pair-name σ τ = Pairs.pairB (fst σ) (fst τ) , Pairs.pairB-name σ τ

  private
    top≤eq-refl : (x : S) → ⟨ ⊤ᴮ ≤ᴮ eq x x ⟩
    top≤eq-refl x = subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
      (sym (BG.Laws.≈ᴮ-refl x)) (≤ᴮ-refl ⊤ᴮ)

    top≤self-imp : (b : Pt BG.B) → ⟨ ⊤ᴮ ≤ᴮ (b ⇒ᴮ b) ⟩
    top≤self-imp b = ⇒ᴮ-curry ⊤ᴮ b b (⊓-lb₂ ⊤ᴮ b)

  IsSingletonφ-singleB-top : (σ : BG.NG.K.Name)
    → value singletonφ (singleton-name σ ∷ translated-name σ ∷ []) ≡ ⊤ᴮ
  IsSingletonφ-singleB-top σ = ≤ᴮ-antisym
    (⊤-greatest (value singletonφ ν))
    (subst (λ φ → ⟨ ⊤ᴮ ≤ᴮ value φ ν ⟩) (sym singleton-shape)
      (subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
        (sym (law-∧ singleton-memberφ singleton-onlyφ ν))
        (⊓-glb (value singleton-memberφ ν) (value singleton-onlyφ ν) ⊤ᴮ
          member-top only-top)))
    where
    m : S
    m = fst σ

    x : S
    x = BG.Translation.trᴮ m

    t : S
    t = Pairs.singleB m

    ν : Envᴮ 2
    ν = singleton-name σ ∷ translated-name σ ∷ []

    member-top : ⟨ ⊤ᴮ ≤ᴮ value singleton-memberφ ν ⟩
    member-top = subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
      (sym (law-∈ (suc zero) zero ν
        ∙ Pairs.singleB-member-value m x
        ∙ BG.Laws.≈ᴮ-refl x)) (≤ᴮ-refl ⊤ᴮ)

    only-top : ⟨ ⊤ᴮ ≤ᴮ value singleton-onlyφ ν ⟩
    only-top = law-∀∈-glb zero (var zero ≐ var (suc (suc zero))) ν ⊤ᴮ step
      where
      step : (ρ : Nameᴮ) → ⟨ ⊤ᴮ ≤ᴮ
        (mem (fst ρ) t ⇒ᴮ
          value (var zero ≐ var (suc (suc zero))) (ρ ∷ ν)) ⟩
      step ρ = subst
        (λ a → ⟨ ⊤ᴮ ≤ᴮ
          (a ⇒ᴮ value (var zero ≐ var (suc (suc zero))) (ρ ∷ ν)) ⟩)
        (sym (Pairs.singleB-member-value m (fst ρ)))
        (subst
          (λ b → ⟨ ⊤ᴮ ≤ᴮ (eq (fst ρ) x ⇒ᴮ b) ⟩)
          (sym (law-≐ zero (suc (suc zero)) (ρ ∷ ν)))
          (top≤self-imp (eq (fst ρ) x)))

  IsPairφ-pairB-top : (σ τ : BG.NG.K.Name)
    → value pairφ (pair-name σ τ ∷ translated-name σ ∷ translated-name τ ∷ []) ≡ ⊤ᴮ
  IsPairφ-pairB-top σ τ = ≤ᴮ-antisym
    (⊤-greatest (value pairφ ν))
    (subst (λ φ → ⟨ ⊤ᴮ ≤ᴮ value φ ν ⟩) (sym pair-shape)
      (subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
        (sym (law-∧ pair-leftφ (pair-rightφ ∧̇ pair-onlyφ) ν))
        (⊓-glb (value pair-leftφ ν) (value (pair-rightφ ∧̇ pair-onlyφ) ν) ⊤ᴮ
          left-top
          (subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
            (sym (law-∧ pair-rightφ pair-onlyφ ν))
            (⊓-glb (value pair-rightφ ν) (value pair-onlyφ ν) ⊤ᴮ
              right-top only-top)))))
    where
    m n : S
    m = fst σ
    n = fst τ

    x y t : S
    x = BG.Translation.trᴮ m
    y = BG.Translation.trᴮ n
    t = Pairs.pairB m n

    ν : Envᴮ 3
    ν = pair-name σ τ ∷ translated-name σ ∷ translated-name τ ∷ []

    left-top : ⟨ ⊤ᴮ ≤ᴮ value pair-leftφ ν ⟩
    left-top = subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
      (sym (law-∈ (suc zero) zero ν))
      (subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
        (sym (Pairs.pairB-member-value m n x))
        (⊆ˢ-trans (top≤eq-refl x) (⊔-ub₁ (eq x x) (eq x y))))

    right-top : ⟨ ⊤ᴮ ≤ᴮ value pair-rightφ ν ⟩
    right-top = subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
      (sym (law-∈ (suc (suc zero)) zero ν))
      (subst (λ b → ⟨ ⊤ᴮ ≤ᴮ b ⟩)
        (sym (Pairs.pairB-member-value m n y))
        (⊆ˢ-trans (top≤eq-refl y) (⊔-ub₂ (eq y x) (eq y y))))

    only-top : ⟨ ⊤ᴮ ≤ᴮ value pair-onlyφ ν ⟩
    only-top = law-∀∈-glb zero
      ((var zero ≐ var (suc (suc zero)))
        ∨̇ (var zero ≐ var (suc (suc (suc zero))))) ν ⊤ᴮ step
      where
      step : (ρ : Nameᴮ) → ⟨ ⊤ᴮ ≤ᴮ
        (mem (fst ρ) t ⇒ᴮ
          value ((var zero ≐ var (suc (suc zero)))
            ∨̇ (var zero ≐ var (suc (suc (suc zero))))) (ρ ∷ ν)) ⟩
      step ρ = subst
        (λ a → ⟨ ⊤ᴮ ≤ᴮ
          (a ⇒ᴮ value ((var zero ≐ var (suc (suc zero)))
            ∨̇ (var zero ≐ var (suc (suc (suc zero))))) (ρ ∷ ν)) ⟩)
        (sym (Pairs.pairB-member-value m n (fst ρ)))
        (subst
          (λ b → ⟨ ⊤ᴮ ≤ᴮ
            ((eq (fst ρ) x ⊔ᴮ eq (fst ρ) y) ⇒ᴮ b) ⟩)
          (sym (law-∨ (var zero ≐ var (suc (suc zero)))
            (var zero ≐ var (suc (suc (suc zero)))) (ρ ∷ ν)
            ∙ cong₂ _⊔ᴮ_
              (law-≐ zero (suc (suc zero)) (ρ ∷ ν))
              (law-≐ zero (suc (suc (suc zero))) (ρ ∷ ν))))
          (top≤self-imp (eq (fst ρ) x ⊔ᴮ eq (fst ρ) y)))
