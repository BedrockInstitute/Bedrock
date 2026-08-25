{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.633]  IS ω AN L-CARDINAL?
--
-- THE OBLIGATION.  ONE TERM:
--
--     omega-is-L-cardinal : IsCardinalL ωʟ
--
-- with IsCardinalL as src/L/Cardinal.lagda.md:230-233 and ωʟ as
-- src/L/Axioms/Infinity.lagda.md:69-70.  Nothing lands in src/.
--
-- [LJ-1.629] (agents/tasks/LJ-1-629/Probe629.agda:139-140) closed
-- `target-false : IsCardinalL ωʟ → SiteIsInit → Empty.⊥` and left this
-- fact as the one hypothesis the falsification borrows, pricing the
-- discharge at 60 to 100 lines (lj-1.629-report.md).  This probe
-- measures that price.  This file carries no hole in its final form
-- and no postulate.  One Agda process at a time; the program set
-- GHCRTS on this pane.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-633.Probe633 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import L.Ordinal {ℓ} using ( ω-ord; mem-ord )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE TERM.
--
-- The clause of IsCardinalL is a function of a TRUNCATED code:
--
--     (δ : S) → ⟨ fst δ ∈ ω ⟩ → (∥ Σ[ F ∈ S ] InjCode F ωʟ δ ∥₁ → ⊥)
--
-- so nothing in this file must ever CONSTRUCT an injection.  The code
-- is given, and it is refuted at its own four conjuncts.
--
--   1.  READBACK.  `readL` (src/L/CantorBernstein.lagda.md:33-38,
--       the `Small` readback) turns the code into the ambient
--       injection ⟪ ω ⟫ ↪ ⟪ fst δ ⟫.
--   2.  ORDINALITY.  a member of ω is an ordinal (mem-ord at ω).
--   3.  THE PIGEONHOLE.  `finite-excl-ω`
--       (src/L/InjChain.lagda.md:153-166) refutes, for ANY ordinal
--       member β of ω, an injective ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫: β is a
--       numeral, and the tree's own Fin pigeonhole then contradicts
--       the injection.  This is the SquareLaw no-inj at
--       src/L/Ordinal/SquareLaw.lagda.md:604-610, particularized.
-- =====================================================================

omega-is-L-cardinal : IsCardinalL ωʟ
omega-is-L-cardinal δ δ∈ω code = PT.rec Empty.isProp⊥ hit code
  where
  hit : Σ[ F ∈ S ] InjCode F ωʟ δ → Empty.⊥
  hit (F , sv , dm , ij , ran) =
    finite-excl-ω (fst δ)
      (mem-ord {A = ω} ω-ord (fst δ) δ∈ω)
      δ∈ω
      (λ x → f x , f x)
      (λ x y e → finj x y (cong fst e))
    where
    read : Σ[ f ∈ (⟪ ω ⟫ → ⟪ fst δ ⟫) ]
           ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y)
    read = readL ωʟ δ (F , sv , dm , ij , ran)
    f : ⟪ ω ⟫ → ⟪ fst δ ⟫
    f = fst read
    finj : (x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y
    finj = snd read
