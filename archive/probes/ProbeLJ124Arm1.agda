{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
import Cubical.Data.Empty as Empty


module ProbeLJ124Arm1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (sq : (α : V ℓ) → (⟨ α ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
          ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.Count {ℓ} using ( composed-count; code; shape-count-inj )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction; regularityV )
open import V.Model {ℓ} using ( ∈sucV-inl )
open import V.Presentation {ℓ} using ( fiber; member; ↪-inj )
open import V.Coding {ℓ} using ( #-inj′ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-inv; Lset-out )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ}
  using ( #∈ω; numeral-ord; numeral-mem; mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; leastOf )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( ω; #_; sucV )

open import Cubical.Foundations.Prelude using ( J; transportRefl; substRefl; PathP; toPathP )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Data.Vec using ( Vec )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open import ProbeLJ124Base {ℓ} lem sq

-- injects into ⟪ α ⟫, given an injection of every member stage's index into
-- ⟪ α ⟫ (the composed induction hypothesis). Route: each member of
-- Lset α is merely a member of 𝒟ₒ (Lset δ) for δ ∈ α (Lset-out), hence
-- merely a defSet φ over Formula ⟪ Lset δ ⟫ 1 (𝒟ₒ-inv); the count of that
-- formula type into ⟪ α ⟫ is Bound.formula-bound at β = α with the supplied
-- branch injection; packing the stage index m and the count value through
-- the pairing, and leastOf over ordSWO, picks the least packed value in the
-- class. Injectivity: equal packed values split by pair-inj, the stage
-- paths are eliminated by J, so no transport-coherence of the branch family
-- is needed, and count-injectivity with defSet-stability close the loop.
module LimitStep (α : S) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                 (D : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S)
                 (inv : (δ : S) (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
                      → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
                 (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫) where

  module B = Bound α oα infα (sq α infα)

  F : ⟪ α ⟫ → Type ℓ
  F m = Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1

  cnt : (m : ⟪ α ⟫) → F m → ⟪ α ⟫
  cnt m = fst (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m))

  cnt-inj : (m : ⟪ α ⟫) (φ ψ : F m) → cnt m φ ≡ cnt m ψ → φ ≡ ψ
  cnt-inj m = snd (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m))

  cnt-stable : (m₁ m₂ : ⟪ α ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
             → cnt m₁ (subst F q φ) ≡ cnt m₂ φ
  cnt-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → cnt m₁ (subst F q φ) ≡ cnt m₂ φ)
      (λ φ → cong (cnt m₂) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable : (m₁ m₂ : ⟪ α ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
                → D (⟪ α ⟫↪ m₁) (subst F q φ)
                  ≡ D (⟪ α ⟫↪ m₂) φ
  defset-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → D (⟪ α ⟫↪ m₁) (subst F q φ)
                ≡ D (⟪ α ⟫↪ m₂) φ)
      (λ φ → cong (D (⟪ α ⟫↪ m₂)) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable-δ : (δ₁ δ₂ : S) (p : δ₁ ≡ δ₂) (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1)
                  → D δ₁ φ₀
                    ≡ D δ₂
                        (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀)
  defset-stable-δ δ₁ δ₂ p φ₀ =
    J (λ δ₂ p → (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1) → D δ₁ φ₀
                ≡ D δ₂
                    (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀))
      (λ φ₀ → sym (cong (D δ₁)
                   (substRefl {B = λ w → Formula ⟪ Lset w ⟫ 1} {x = δ₁} φ₀))) p φ₀

  class-pred : (x : ⟪ Lset α ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  class-pred x y = ( ∥ Σ[ m ∈ ⟪ α ⟫ ] Σ[ φ ∈ F m ]
                        ( ( D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x )
                        × ( B.pair m (cnt m φ) ≡ y ) ) ∥₁
                   , squash₁ )

  nonempty : (x : ⟪ Lset α ⟫)
           → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩ ∥₁
  nonempty x = PT.rec (squash₁) toWitness
    (Lset-out α (⟪ Lset α ⟫↪ x) (member (Lset α) x))
    where
    toWitness : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ ⟪ Lset α ⟫↪ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
              → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩ ∥₁
    toWitness (δ , (δ∈α , x∈𝒟ₒδ)) =
      PT.map mk (inv δ (⟪ Lset α ⟫↪ x) x∈𝒟ₒδ)
      where
      fib = fiber α {x = δ} δ∈α
      m : ⟪ α ⟫
      m = fib .fst
      p : ⟪ α ⟫↪ m ≡ δ
      p = fib .snd
      mk : Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ]
             (D δ φ₀ ≡ ⟪ Lset α ⟫↪ x)
         → Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩
      mk (φ₀ , e₀) = (B.pair m (cnt m φ) , ∣ (m , φ , (e , refl)) ∣₁)
        where
        φ : F m
        φ = subst (λ w → Formula ⟪ Lset w ⟫ 1) (sym p) φ₀
        e : D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x
        e = sym (defset-stable-δ δ (⟪ α ⟫↪ m) (sym p) φ₀) ∙ e₀

  h : ⟪ Lset α ⟫ → ⟪ α ⟫
  h x = fst (leastOf (OrdSWO.ordSWO α oα) lem (class-pred x) (nonempty x))

  h-inj : (x y : ⟪ Lset α ⟫) → h x ≡ h y → x ≡ y
  h-inj x y e = ↪-inj {a = Lset α} (go pm)
    where
    lx = leastOf (OrdSWO.ordSWO α oα) lem (class-pred x) (nonempty x)
    ly = leastOf (OrdSWO.ordSWO α oα) lem (class-pred y) (nonempty y)
    pm : ⟨ class-pred x (fst ly) ⟩
    pm = subst (λ z → ⟨ class-pred x z ⟩) e (fst (snd lx))
    py : ⟨ class-pred y (fst ly) ⟩
    py = fst (snd ly)
    go : ⟨ class-pred x (fst ly) ⟩
       → ⟪ Lset α ⟫↪ x ≡ ⟪ Lset α ⟫↪ y
    go = PT.rec (isSetS (⟪ Lset α ⟫↪ x) (⟪ Lset α ⟫↪ y)) go₁
      where
      go₁ : Σ[ m₁ ∈ ⟪ α ⟫ ] Σ[ φ₁ ∈ F m₁ ]
              ( ( D (⟪ α ⟫↪ m₁) φ₁ ≡ ⟪ Lset α ⟫↪ x )
              × ( B.pair m₁ (cnt m₁ φ₁) ≡ fst ly ) )
          → ⟪ Lset α ⟫↪ x ≡ ⟪ Lset α ⟫↪ y
      go₁ (m₁ , φ₁ , eφ₁ , ec₁) =
        PT.rec (isSetS (⟪ Lset α ⟫↪ x) (⟪ Lset α ⟫↪ y)) go₂ py
        where
        go₂ : Σ[ m₂ ∈ ⟪ α ⟫ ] Σ[ φ₂ ∈ F m₂ ]
                ( ( D (⟪ α ⟫↪ m₂) φ₂ ≡ ⟪ Lset α ⟫↪ y )
                × ( B.pair m₂ (cnt m₂ φ₂) ≡ fst ly ) )
            → ⟪ Lset α ⟫↪ x ≡ ⟪ Lset α ⟫↪ y
        go₂ (m₂ , φ₂ , eφ₂ , ec₂) = sym eφ₁ ∙ eq-defset ∙ eφ₂
          where
          ec : B.pair m₁ (cnt m₁ φ₁) ≡ B.pair m₂ (cnt m₂ φ₂)
          ec = ec₁ ∙ sym ec₂
          p-pair : (m₁ ≡ m₂) × (cnt m₁ φ₁ ≡ cnt m₂ φ₂)
          p-pair = B.pair-inj m₁ (cnt m₁ φ₁) m₂ (cnt m₂ φ₂) ec
          qm : m₁ ≡ m₂
          qm = fst p-pair
          ecount : cnt m₁ φ₁ ≡ cnt m₂ φ₂
          ecount = snd p-pair
          ecount' : cnt m₁ φ₁ ≡ cnt m₁ (subst F (sym qm) φ₂)
          ecount' = ecount ∙ sym (cnt-stable m₁ m₂ (sym qm) φ₂)
          eφ : φ₁ ≡ subst F (sym qm) φ₂
          eφ = cnt-inj m₁ φ₁ (subst F (sym qm) φ₂) ecount'
          eq-defset : D (⟪ α ⟫↪ m₁) φ₁
                    ≡ D (⟪ α ⟫↪ m₂) φ₂
          eq-defset = cong (D (⟪ α ⟫↪ m₁)) eφ
                    ∙ defset-stable m₁ m₂ (sym qm) φ₂

limit-step : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
           → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
limit-step α oα infα ih =
  LimitStep.h α oα infα (λ δ φ → DefOf.defSet (Lset δ) φ)
    (λ δ x h → 𝒟ₒ-inv (Lset δ) x h) ih
    , LimitStep.h-inj α oα infα (λ δ φ → DefOf.defSet (Lset δ) φ)
        (λ δ x h → 𝒟ₒ-inv (Lset δ) x h) ih
