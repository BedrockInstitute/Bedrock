{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.408] PROBE.  pair-cross: injectivity of TWO pairings at one
-- equation.  It runs in agents/tasks/LJ-1-408/ and lands nothing in src/.
--
-- W3, FIRST: `swap-sq`, the swapped pairing.  Stated alone and run
-- before anything else, per the brief.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; #_; sucV )
open import Cubical.Data.Sigma using ( ΣPathP )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-408.Probe408 {ℓ : Level} where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The pairing-and-injectivity Sigma, matching
-- src/L/Ordinal/SquareLaw.lagda.md:685-687, written here so this probe
-- does not load that chapter for a type alias.

sq : V ℓ → Type ℓ
sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
         ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- W3, FIRST.  The swapped pairing.  If s = (f , f-inj), the swap sends
--   (x , y) to f (y , x).  Injectivity is ΣPathP over f-inj of the
--   swapped pair.
-- =====================================================================

swap-sq : (α : V ℓ) → sq α → sq α
swap-sq α (f , f-inj) = g , g-inj
  where
  g : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  g p = f (snd p , fst p)
  g-inj : (x y : ⟪ α ⟫ × ⟪ α ⟫) → g x ≡ g y → x ≡ y
  g-inj x y e = ΣPathP (cong snd p , cong fst p)
    where
    p : (snd x , fst x) ≡ (snd y , fst y)
    p = f-inj (snd x , fst x) (snd y , fst y) e

-- =====================================================================
-- THE OBLIGATION, AS THE BRIEF STATES IT.  REFUTED: see PART 3.
-- =====================================================================

pair-cross :
    (α : V ℓ) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (s₁ s₂ : sq α)
  → (m₁ c₁ m₂ c₂ : ⟪ α ⟫)
  → fst s₁ (m₁ , c₁) ≡ fst s₂ (m₂ , c₂)
  → (m₁ ≡ m₂) × (c₁ ≡ c₂)
pair-cross = ?

-- =====================================================================
-- PART 3.  THE REFUTATION.  The site is α := ω, with any pairing s.
--
--   s₂ is swap-sq of s.  Then fst s (u , v) ≡ fst s₂ (v , u) by refl,
--   and pair-cross would force u ≡ v.  The two numerals # 0 and # 1
--   are members of ω; if they were equal, # 0 ∈ # 0, and ∈-irrefl
--   kills it.  The pairing is a hypothesis: pair-cross is quantified
--   over pairings, and the consumer already has one as data.
-- =====================================================================

m0 : ⟪ ω ⟫
m0 = fiber ω {x = # 0} (#∈ω 0) .fst

m1 : ⟪ ω ⟫
m1 = fiber ω {x = # 1} (#∈ω 1) .fst

m0≢m1 : m0 ≡ m1 → Empty.⊥
m0≢m1 e = ∈-irrefl (# 0) (subst (λ w → ⟨ (# 0) ∈ˢ w ⟩) (sym eq01) n0∈n1)
  where
  eq01 : # 0 ≡ # 1
  eq01 = sym (fiber ω {x = # 0} (#∈ω 0) .snd)
       ∙ cong (⟪ ω ⟫↪) e
       ∙ fiber ω {x = # 1} (#∈ω 1) .snd
  n0∈n1 : ⟨ (# 0) ∈ˢ (# 1) ⟩
  n0∈n1 = subst (λ w → ⟨ (# 0) ∈ˢ w ⟩) suc#0 (self∈sucV (# 0))
    where
    suc#0 : sucV (# 0) ≡ # 1
    suc#0 = refl

pair-cross-refuted :
    (s : sq ω)
  → ((α : V ℓ) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
     → (s₁ s₂ : sq α)
     → (m₁ c₁ m₂ c₂ : ⟪ α ⟫)
     → fst s₁ (m₁ , c₁) ≡ fst s₂ (m₂ , c₂)
     → (m₁ ≡ m₂) × (c₁ ≡ c₂))
  → Empty.⊥
pair-cross-refuted s pc =
  m0≢m1 (fst (pc ω ω-ord (∈-irrefl ω) s (swap-sq ω s) m0 m1 m1 m0 refl))
