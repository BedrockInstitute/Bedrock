{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.635]  DOES THE BILL SPLIT AT OMEGA?
--
-- THE OBLIGATION.  `gch-splits-at-ω`, stated exactly as the brief
-- names it: one term whose two hypotheses are the two halves of the
-- generalized continuum hypothesis bill at L, the strictly-above-omega
-- half and the at-omega half, and whose conclusion is the bill itself.
-- This is a DECOMPOSITION, not a proof of either half: both halves are
-- hypotheses and neither is discharged here.
--
-- `Concl zf κ` below is GCHStatement's own conclusion at κ, copied
-- letter for letter from src/L/GCH.lagda.md:65-68.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every line of it is a
-- measurement and not a claim ([LJ-1.533]'s discipline).  Nothing
-- lands in src/.  No commit, no push.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  THE CONCLUSION, copied letter for letter, at the
--               generality the split needs (any zf, any κ).
--   Section 2.  THE OBLIGATION, `gch-splits-at-ω`, built on the alone
--               typechecked W3 crossing (runs/Tri.agda, runs/tri-1.out)
--               and the subset-eta bridge for the equal case.
--   Section 3.  THE FORCING ROW, `above-half-misses-ω`: the term that
--               makes the split necessary.  It is an order fact, not
--               an Init fact (SquareLaw is never imported).
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.  No heap wall occurred; the run ledger is
-- in the report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-635.Probe635 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import Cubical.Data.Sigma using ( Σ-syntax; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
import LJ-1-635.runs.Tri
module Tri = LJ-1-635.runs.Tri lem

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  THE CONCLUSION, copied letter for letter from
-- src/L/GCH.lagda.md:65-68.  The only change is the two extra
-- arguments (zf and κ), which the split needs to talk about one site.
-- The carrier split is the chapter's own (src/L/GCH.lagda.md:23-25):
-- `S` is 𝒮ʟ's carrier and `_∈ˢ_` is 𝒮ᵥ's relation, which is why the
-- clause speaks of `fst κ` at `ω`.  The floor run caught a first
-- spelling of this file that took `S` from 𝒮ᵥ instead
-- (runs/floor-1.out, UnequalTerms at the δ binder).
-- =====================================================================

Concl : ModelL.isZFModel → S → Type (ℓ-suc ℓ)
Concl zf κ =
  ∥ Σ[ δ ∈ S ] ( SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )

-- =====================================================================
-- SECTION 2.  THE OBLIGATION.  Trichotomy against ω has three cases;
-- the bill's clause kills the first, so exactly two remain, and each
-- remaining case is one hypothesis of the split: the strictly-above
-- half pays `fst κ ≢ ω`, the at-omega half pays `fst κ ≡ ω` through
-- subset eta (the second component of an `S` is a proposition, so
-- `fst κ ≡ ω` IS `κ ≡ ωʟ`).  No `with` inside a nested `where`: the
-- case dispatch is a plain case function, the shape [LJ-1.629]
-- measured green after the `with`-in-`where` shape walled
-- (agents/tasks/LJ-1-629/runs/final-5.out against runs/final-9.out).
-- =====================================================================

gch-splits-at-ω :
    (zf : ModelL.isZFModel)
  → ((κ : S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ˢ fst κ ⟩ → Concl zf κ)
  → Concl zf ωʟ
  → GCHStatement zf
gch-splits-at-ω zf above at-ω κ oκ cκ κ∉ω =
  at (Tri.tri-above (fst κ) oκ κ∉ω)
  where
    at : (fst κ ≡ ω) ⊎ ⟨ ω ∈ˢ fst κ ⟩ → Concl zf κ
    at (inl κ≡ω) =
      subst (Concl zf) (sym κ≡ωʟ) at-ω
      where
        κ≡ωʟ : κ ≡ ωʟ
        κ≡ωʟ = Σ≡Prop (λ x → snd (isL x)) κ≡ω
    at (inr ω∈κ) = above κ oκ cκ ω∈κ

-- =====================================================================
-- SECTION 3.  THE FORCING ROW.  Is the split forced by something other
-- than `Init`'s definition (the pod-math addendum's question)?  YES,
-- and by a cheaper fact: the strictly-above hypothesis is FALSE at the
-- omega site itself.  `fst ωʟ` is `ω` by definition
-- (src/L/Axioms/Infinity.lagda.md:69-70), and no set is a member of
-- itself by regularity (`∈-irrefl`, src/V/Hierarchy.lagda.md:155).
-- So `above` alone can never pay `GCHStatement zf` at `κ := ωʟ`: the
-- at-omega half is not redundant.  This is an ORDER fact. It is not an
-- artifact of `Init` (SquareLaw is not imported by this file), and the
-- textbook's uniform argument does not remove it: the uniform argument
-- would have to make `above`'s hypothesis true at ω, which ∈-irrefl
-- forbids, or make the bill's clause exclude `κ ≡ ω`, which the bill
-- does not do (src/L/GCH.lagda.md:64 excludes `κ ∈ˢ ω` only).
-- =====================================================================

above-half-misses-ω : ⟨ ω ∈ˢ fst ωʟ ⟩ → Empty.⊥
above-half-misses-ω = ∈-irrefl ω
