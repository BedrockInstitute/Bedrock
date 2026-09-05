{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.452] PROBE.  The square law as DATA over the band, under
-- one hypothesis.  It runs in agents/tasks/LJ-1-452/ and lands
-- nothing in src/.
--
--   W3 FIRST  `omega-branch`.  Typechecked ALONE, obligation omitted.
--             squareω is data (src/L/InjChain.lagda.md:184-185).
--
--   TERM      `sq-data-closed`.  ∈-induction at the untruncated
--             motive.  descent-both is a module hypothesis at
--             [LJ-1.447]'s delivered type after residue.  This file
--             holds no κL and no κC.  The four cases are not restated.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-452.Probe452 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import L.Constructible {ℓ} using ( isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.StageBound {ℓ} lem using ( SqFam )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- =====================================================================
-- W3.  omega-branch.  Typechecked ALONE first, obligation omitted.
-- squareω is data (src/L/InjChain.lagda.md:184-185).
-- =====================================================================

omega-branch : (x : V ℓ) → x ≡ ω → sq x
omega-branch x x≡ω = subst sq (sym x≡ω) squareω

-- The consumer's band membership produces the ordinal certificate the
-- chapter does not ask for.  Copied from Probe437.agda:284-288.
band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
  (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
  (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

-- =====================================================================
-- THE OBLIGATION.  One module hypothesis: descent-both at the type
-- Probe447.agda:211-213, which is 447's delivered term after its
-- residue argument.  Restating residue names κL and κC; this file
-- holds neither.  The four cases are not restated.
-- =====================================================================

module _
  (descent-both :
      (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
    → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
    → sq x)
  where

  Goal : V ℓ → Type (ℓ-suc ℓ)
  Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

  step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
  step x ih ox infx = go (ord-tri x ox ω ω-ord)
    where
    go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → sq x
    go (inl x∈ω) = Empty.rec (infx x∈ω)
    go (inr (inl x≡ω)) = omega-branch x x≡ω
    go (inr (inr ω∈x)) = descent-both x ox ω∈x ih∈ˢ
      where
      -- Adapter: ∈-induction supplies (y) → ⟨ y ∈ x ⟩ → Goal y, and
      -- Goal puts the certificate first.  descent-both wants
      -- (y) → ⟨ y ∈ˢ x ⟩ → IsOrd y → infinite y → sq y.
      -- No subst: ∈ˢ on 𝒮ᵥ is ∈ (src/V/Hierarchy.lagda.md:83).
      ih∈ˢ : (y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y
           → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y
      ih∈ˢ y y∈x oy infy = ih y y∈x oy infy

  sq-data-closed :
      (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → sq δ
  sq-data-closed δ δ∈ infδ =
    ∈-induction {P = Goal} step δ (band-ord δ δ∈) infδ

  -- Adapter to the landed consumer.  SqFam is
  -- src/L/StageBound.lagda.md:33-38.  S of 𝒮ᵥ is V ℓ
  -- (src/V/Hierarchy.lagda.md:80) and ∈ˢ is ∈ (:83).
  sq-data-to-SqFam : SqFam α₀
  sq-data-to-SqFam = sq-data-closed
