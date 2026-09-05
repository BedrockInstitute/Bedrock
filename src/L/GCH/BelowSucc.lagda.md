# Every ordinal below the successor cardinal injects into the base

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.BelowSucc {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.GCH {ℓ} lem using ( SuccCardL; InjL )
open import L.GCH.Assembly {ℓ} lem using ( inclusion-coded; injl-trans )

open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import Cubical.Induction.WellFounded as WF

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier: the ambient membership lives here.
module SV = hPropStructure 𝒮ᵥ using ( S )
-- The L-carrier: `SuccCardL` and `InjL` live here.
module SL = hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE THEOREM.  Let δ be the successor cardinal of κ in L.  Every
-- ordinal α ∈ δ injects into κ, internally.
--
--   Well-founded induction on α, by trichotomy against κ.  If α ∈ κ or
--   α ≡ κ then α ⊆ κ, and an inclusion is an internal injection.  If
--   κ ∈ α then α is not an L-cardinal: it would be an ordinal
--   L-cardinal above κ, so δ ⊆ α by leastness, so α ∈ α.  With the
--   excluded middle the failure of `IsCardinalL α` yields, merely, some
--   γ ∈ α with α injecting into γ; γ ∈ δ by transitivity, the induction
--   hypothesis injects γ into κ, and the two injections compose.
-- =====================================================================

below-succ-injects :
    (κ δ : SL.S) → SuccCardL δ κ
  → (α : SL.S) → IsOrd (fst α) → ⟨ fst α ∈ˢ fst δ ⟩
  → InjL α κ
below-succ-injects κ δ (ordδ , _ , κ∈δ , least) α =
  WF.WFI.induction regularityV {P = P} step (fst α) (snd α)
  where
  P : SV.S → Type (ℓ-suc ℓ)
  P a = (la : ⟨ isL a ⟩) → IsOrd a → ⟨ a ∈ˢ fst δ ⟩ → InjL (a , la) κ

  ordκ : IsOrd (fst κ)
  ordκ = mem-ord {A = fst δ} ordδ (fst κ) κ∈δ

  step : (a : SV.S) → (∀ a' → ⟨ a' ∈ˢ a ⟩ → P a') → P a
  step a ih la orda a∈δ = go (ord-tri a orda (fst κ) ordκ)
    where
    α' : SL.S
    α' = a , la

    -- Once κ ∈ α, an L-cardinal α would put δ inside α, hence α ∈ α.
    not-card : ⟨ fst κ ∈ˢ a ⟩ → IsCardinalL α' → Empty.⊥
    not-card κ∈a c = ∈-irrefl a (least α' orda c κ∈a α' a∈δ)

    Ex : Type (ℓ-suc ℓ)
    Ex = ∥ Σ[ γ ∈ SL.S ] (⟨ fst γ ∈ˢ a ⟩ × InjL α' γ) ∥₁

    -- The excluded middle turns the refuted Π into a mere witness.
    some-γ : ⟨ fst κ ∈ˢ a ⟩ → Ex
    some-γ κ∈a = decide (lem (Ex , squash₁))
      where
      decide : Ex ⊎ (Ex → Empty.⊥) → Ex
      decide (inl e)  = e
      decide (inr ¬e) =
        Empty.rec (not-card κ∈a (λ γ γ∈a inj → ¬e ∣ γ , γ∈a , inj ∣₁))

    from-γ : Σ[ γ ∈ SL.S ] (⟨ fst γ ∈ˢ a ⟩ × InjL α' γ) → InjL α' κ
    from-γ (γ , γ∈a , α↪γ) =
      injl-trans α' γ κ α↪γ
        (ih (fst γ) γ∈a (snd γ)
            (mem-ord {A = a} orda (fst γ) γ∈a)
            (ordδ .fst γ∈a a∈δ))

    go : Tri a (fst κ) → InjL α' κ
    go (inl a∈κ)       =
      inclusion-coded α' κ (λ z z∈a → ordκ .fst z∈a a∈κ)
    go (inr (inl e))   =
      inclusion-coded α' κ (λ z z∈a → subst (λ w → ⟨ z ∈ˢ w ⟩) e z∈a)
    go (inr (inr κ∈a)) = PT.rec squash₁ from-γ (some-γ κ∈a)
```
