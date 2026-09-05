{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.448] PROBE.  The square law as DATA over the whole band,
-- under one hypothesis.
--
--   W3 FIRST  `omega-branch`.  Typechecked ALONE, obligation omitted.
--             If squareω is truncated, the plan dies here.
--
--   TERM      `sq-data-closed`.  ∈-induction at the untruncated
--             motive.  Third branch spends descent-both at the
--             remaining telescope of Probe447.agda:211-213, residue
--             already applied.  This file holds no κL and no κC.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-448.Probe448 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import L.Constructible {ℓ} using ( isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.InjChain {ℓ} lem using ( squareω )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_; S )

-- =====================================================================
-- W3.  omega-branch.  Typechecked ALONE first, obligation omitted.
-- The same line as Probe437.agda:308, without ∣_∣₁.  squareω : sq ω
-- at src/L/InjChain.lagda.md:184.
-- =====================================================================

omega-branch : (x : V ℓ) → x ≡ ω → sq x
omega-branch x x≡ω = subst sq (sym x≡ω) squareω

-- Copied from Probe437.agda:284-288.  Band membership yields the
-- ordinal certificate the motive wants.
band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
  (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
  (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

-- The consumer's family, copied from Probe434.agda:44-48.
SqFam : S → Type (ℓ-suc ℓ)
SqFam α =
  (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- =====================================================================
-- THE OBLIGATION.  descent-both is the remaining telescope of
-- Probe447.agda:211-213, residue already applied.  Writing residue's
-- type would name κL and κC; this file holds neither.  Do not rebuild
-- either seal.  Do not restate the four cases.
-- =====================================================================

module _
  (descent-both :
      (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
    → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
    → sq x)
  where

  Goal : V ℓ → Type (ℓ-suc ℓ)
  Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

  -- Adapter at the call site.  ∈-induction supplies
  -- (y) → ⟨ y ∈ x ⟩ → Goal y, and Goal takes the certificate first
  -- (Probe437.agda:298).  447's IH is
  -- (y) → ⟨ y ∈ˢ x ⟩ → IsOrd y → infinite y → sq y
  -- (Probe447.agda:212).  On 𝒮ᵥ, _∈ˢ_ is _∈_ (src/V/Hierarchy.lagda.md:83),
  -- so unfolding Goal makes the two telescopes the same.  The lambda
  -- is η-expansion.  It is not a subst.
  ih-adapt :
      (x : V ℓ)
    → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y)
    → (y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y
  ih-adapt x ih y y∈x oy infy = ih y y∈x oy infy

  step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
  step x ih ox infx = go (ord-tri x ox ω ω-ord)
    where
    go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → sq x
    go (inl x∈ω) = Empty.rec (infx x∈ω)
    go (inr (inl x≡ω)) = omega-branch x x≡ω
    go (inr (inr ω∈x)) = descent-both x ox ω∈x (ih-adapt x ih)

  sq-data-closed :
      (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → sq δ
  sq-data-closed δ δ∈ infδ =
    ∈-induction {P = Goal} step δ (band-ord δ δ∈) infδ

  -- Adapter to the consumer.  Body is the identity.  If this fails,
  -- the elaborator's error is the finding.  Do not hide a subst.
  meets-consumer :
      ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
    → SqFam α₀
  meets-consumer z = z

  meets-closed : SqFam α₀
  meets-closed = meets-consumer sq-data-closed
