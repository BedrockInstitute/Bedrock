{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.718] PROBE.  The repaired LsetGrounded, composed from two
-- named hypotheses.  Lands nothing in src/.
--
--   THE OBLIGATION  grounded-from-complete, the statement the critic
--                   of [LJ-1.673] repaired: Completeness WITH IsOrd on
--                   the parameter code, Convert at matrix₃, IsOrd δ in
--                   the obligation's own telescope
--                   (review-of-LJ-1-673-1.md:158-165).
--   W3 VERDICT      NO-GO, stated in
--                   review-of-grounded-from-complete.md.  The codes
--                   DO match the hull's δ: the Completeness ->
--                   hull-closed half composes green
--                   (runs/d-2.out, EXIT=0).  The obstruction is the
--                   elaboration of At.Convert's APPLICATION, measured
--                   at six shapes (runs/d-1, d-3, d-4, d-5, d-7 and
--                   p-1), two of them heap walls at the 2 GB cap
--                   (runs/d-3.out, runs/d-4.out).  The term is NOT
--                   declared here: no name `grounded-from-complete`
--                   exists in this file, so the witness meter reads
--                   the truth (MISSING), and no hole is shipped.
--                   Probe652's LsetGrounded (Probe652.agda:260-264)
--                   is NOT inhabited here; it has no IsOrd.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-718.Probe718 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ

open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
open import LJ-1-673.Probe673 {ℓ} lem as P673

open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

-- =====================================================================
-- THE FRAME, AND THE PREDECESSOR'S OWN NAMES.  One hull stage, the
-- telescope of Probe692's Spend (agents/tasks/LJ-1-692/Probe692.agda:
-- 37-43).  F is aliased off A so the two module instances of the
-- frame are one name.  Nothing here restates a predecessor type.
-- =====================================================================

module Build (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P673.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  module F = A.F
  module HS = F.HS

  open F.HS.H.T using ( Code; val )

  -- THE SUPPLIERS, AS THE BRIEF NAMES THEM.
  -- Convert: Probe673's own type, verbatim (Probe673.agda:115-119).
  Convert : Type (ℓ-suc ℓ)
  Convert = A.Convert

  -- Completeness: Probe673's type (Probe673.agda:126-130) with the
  -- critic's repair, IsOrd on the parameter code, as Commute already
  -- carries IsOrd on its collapse (Probe652.agda:249-253).  Not
  -- inhabited here.
  Completeness : Type (ℓ-suc ℓ)
  Completeness =
    (ca cp : Code) → IsOrd (fst (val cp))
    → fst (val ca) ≡ Lset (fst (val cp))
    → A.BoundInStage ca cp

  -- THE OBLIGATION'S TYPE, STATED AND NOT INHABITED.  The term is not
  -- declared: its only route to the ambient triple is the
  -- application of Convert, and that application is the measured
  -- wall (review-of-grounded-from-complete.md, section 2).  No
  -- `grounded-from-complete` name exists in this file, so the meter
  -- reads MISSING and no red probe lies about it.
  GroundedFromComplete : Type (ℓ-suc ℓ)
  GroundedFromComplete =
    Completeness
    → Convert
    → ((a p z : S)
       → ⟨ (a ∷ p ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩ → IsOrd p → a ≡ Lset p)
    → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩
    → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ HS.M ⟩ × ⟨ Lset δ ∈ˢ HS.M ⟩
                  × ⟨ (Lset δ ∷ δ ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩) ∥₁
