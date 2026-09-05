{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.767-SPLIT-SPLIT] PROBE, THE OBLIGATION.  grounded-from-complete
-- at the brief's SPLIT-SPLIT Sigma: the READING IS THE ONLY PACKED
-- FACTOR.  This file is built from VendorPack.agda.txt (delivered in
-- this task directory; itself LJ-1-767.Probe767): the module renamed to
-- this task's namespace, the two interface imports retargeted to
-- LJ-1-767-SPLIT-SPLIT.runs.FrameSplit and
-- LJ-1-767-SPLIT-SPLIT.runs.HullHalfSplit, and this header rewritten.
-- Against the vendor pack, the brief orders the SPLIT-SPLIT delta, and
-- it is taken:
--
--   THE TYPE IS CHANGED.  767-SPLIT's grid law: a packing walls iff the
--            packed tuple's FIRST factor is real with at least one
--            further real component; it greens iff the first factor is
--            a hole; a first factor real with no other real component
--            costs the floor.  This brief drops every other component:
--            no membership slot, no `⟨ Lset δ ∈ˢ HS.M ⟩`, no code
--            equation in the Sigma.  The reading stands alone, so it is
--            simultaneously the first factor and the only real slot of
--            the tuple, the law's free shape.
--
--   NO mkWit.  The packing stands inline in the body, every component
--            type inferred from the goal, and conv0's codomain stays a
--            solved meta.  The spelled reading appears once, in the
--            obligation's own type, exactly as the brief's type reads.
--
--   THE GREEN PIECES, each measured alone at -M4g at this site
--   frame      FrameSplit: the repaired telescope, Completeness as
--              a HYPOTHESIS, SatIn, HullM, codeOf (this task's
--              runs/framesplit.out, re-measured at this site).
--   hull half  HullHalfSplit's hullClosed (this task's
--              runs/hullhalfsplit.out, re-measured at this site).
--   S5 here    the vendor S5 shape re-measured at this site
--              (this task's runs/s5remain.out), the first factor's
--              real check alone.
--
--   THE PROHIBITIONS, HELD BY CONSTRUCTION.  No mkWit whose type
-- spells the reading; conv0 NOT ascribed (its codomain stays a
-- solved meta); no subst along fst (val ca) ≡ Lset δ or
-- fst (val cp) ≡ δ (both equations carried as data and dropped from
-- the tuple); no Convert hypothesis (the supplier is [LJ-1.692]'s
-- CONSTRUCTED term, opened through FrameSplit's Spend, never
-- hypothesised); no inhabitant of conv-at-Lδ; no retry of amb;
-- Completeness taken as a HYPOTHESIS and never inhabited.
--
--   NO HOLE, NO POSTULATE.  One Agda process per run, caliber from
-- the pane, never set here.  Floor first (coder law, owner ruling
-- 2026-08-23): runs/FloorSplit.agda.txt is this file with the body
-- a hole, and it runs before this file.  A file that cannot
-- typecheck rests at .agda.txt, never .agda (naming rule).  Lands
-- nothing in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-767-SPLIT-SPLIT.Probe767SplitSplit {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ
open import FOL.Manipulation.Relabelling using ( mapFo )

open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667

-- qualified imports only: this file carries its own module Build,
-- and a plain import of a module holding a Build of its own shadows
-- it (measured: ShadowedModule, SSS runs/hull-1.out).
import LJ-1-767-SPLIT-SPLIT.runs.FrameSplit {ℓ} lem as Frame
import LJ-1-767-SPLIT-SPLIT.runs.HullHalfSplit {ℓ} lem as HullHalf

open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

module Build (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  -- selective open: everything but GroundedFromComplete, which is
  -- re-declared below at code coordinates.  A plain open followed by
  -- a local declaration of the same name is a ClashingDefinition
  -- (measured, SSS runs/shadow notes; the vendor's header).
  open Frame.Build lam ordλ succλ X X⊆Lλ ∅∈λ elem
    using ( Code; val; hull-convert-at-matrix; Completeness
          ; SatIn; HullM; codeOf; module A; module F; module HS )
  open HullHalf.Build lam ordλ succλ X X⊆Lλ ∅∈λ elem
    using ( hullClosed )

  -- THE OBLIGATION'S TYPE, at code coordinates, spelled once (W2):
  -- the brief's type verbatim.  The READING IS THE ONLY PACKED
  -- FACTOR: no membership component, no code equation, no second
  -- membership slot.  The two ≡ keep the vendor's explicit
  -- parentheses and the one-line ⊨ₚ reading (measured layout: a
  -- NoParseForApplication on the bare chain, the floor765ss note).
  GroundedFromComplete : Type (ℓ-suc ℓ)
  GroundedFromComplete =
    Completeness
    → ((a p z : S)
       → ⟨ (a ∷ p ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩ → IsOrd p → a ≡ Lset p)
    → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩
    → ∥ Σ[ ca ∈ Code ] Σ[ cp ∈ Code ] Σ[ z ∈ S ]
         ⟨ (fst (val ca) ∷ fst (val cp) ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩ ∥₁

  -- THE CONSTRUCTED CONVERSION at B6's measured-green shape (SSS
  -- runs/bisect-6.out, 140.69 s): the domain the inline spelling,
  -- the codomain a solved meta, the definition unapplied.  Its
  -- codomain IS the Sigma's only component, so it enters the packing
  -- untransported.
  conv0 : (ca cp : Code) (a : F.HS.ASt.SL)
        → ⟨ (a ∷ []) F.HS.ASt.AbsL.⊨ᵐ (mapFo val (A.inBound ca cp)) ⟩
        → _
  conv0 = hull-convert-at-matrix

  -- THE TERM.  Hull membership gives both codes; Completeness lifts
  -- the pair to the stage existential; hull-closed (the loaded hull
  -- half) produces the witness; the packing stands INLINE in the
  -- body, no mkWit, every component type inferred from the goal.
  -- The packed tuple is ca, cp, the witness's stage element, and the
  -- reading, nothing else: the hull-membership component of the
  -- witness is discharged by the wildcard and names no slot, and
  -- neither code equation nor any membership proof is packed.  The
  -- soundness argument is clause (iii)'s own; the composition does
  -- not need it and does not use it.
  grounded-from-complete : GroundedFromComplete
  grounded-from-complete comp sound δ ordδ δ∈M Lδ∈M =
    PT.rec squash₁
      (λ { (cp , cp≡δ) →
      PT.rec squash₁
        (λ { (ca , ca≡Lδ) →
        PT.map (λ { (a , _ , sat) →
                 ca , cp , fst a , conv0 ca cp a sat })
               (hullClosed comp δ ordδ ca cp ca≡Lδ cp≡δ) })
        (codeOf (Lset δ) Lδ∈M) })
      (codeOf δ δ∈M)

-- THE OBLIGATION'S NAME, exported at the file's top level
-- (Probe692.agda:68's pattern).
grounded-from-complete = Build.grounded-from-complete
