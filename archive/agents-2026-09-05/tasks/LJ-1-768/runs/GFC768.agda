-- [LJ-1.768] TRANSCRIBED, THE SPLIT-SPLIT OBLIGATION.  This file is
-- VendorGFC.agda.txt (delivered in this task directory; itself
-- LJ-1-767-SPLIT-SPLIT.Probe767SplitSplit) transcribed into this
-- worktree, with the module renamed to this task's namespace, the two
-- interface imports retargeted to LJ-1-768.runs.Frame768 and
-- LJ-1-768.runs.HullHalf768, and this header rewritten.  Everything
-- else from the first open-import down is byte-identical to the
-- vendor (measured with diff): the obligation's type at code
-- coordinates, the un-ascribed conv0, the inline reading-only
-- packing, and the top-level export, exactly as SPLIT-SPLIT measured
-- it GREEN at -M4g, rc 0 in 210.63 s
-- (agents/tasks/LJ-1-767-SPLIT-SPLIT/lj-1.767-SPLIT-SPLIT-report.md:5;
-- this task's runs/gfc768.out re-measures it at this site).
--
--   THE PROHIBITIONS STAND AS THE VENDOR STATES THEM, including: no
-- second real factor under the two PT.rec binders; no subst along
-- fst (val ca) ≡ Lset δ or fst (val cp) ≡ δ; conv0 NOT ascribed;
-- Completeness a HYPOTHESIS, never inhabited.
--
--   NO HOLE, NO POSTULATE.  One Agda process per run, caliber from
-- the pane, never set here.  Lands nothing in src/.

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-768.runs.GFC768 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
import LJ-1-768.runs.Frame768 {ℓ} lem as Frame
import LJ-1-768.runs.HullHalf768 {ℓ} lem as HullHalf

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
