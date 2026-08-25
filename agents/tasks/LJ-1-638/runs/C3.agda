{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.638]  W3, THE WIDEST UNMEASURED TERM: does [LJ-1.629]'s
-- conjunct-3 row COMPOSE at this task's frame WITHOUT re-proof?
--
-- THE QUESTION, from the brief.  [LJ-1.629] delivered `c3-payable`
-- (agents/tasks/LJ-1-629/Probe629.agda:227-233) at the BILL's site
-- frame: its hypotheses are IsOrd (fst κ), IsCardinalL κ, the trophy
-- clause ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥, and ⟨ ω ∈ˢ fst κ ⟩.  THIS task's
-- frame drops the trophy clause and keeps ⟨ ω ∈ˢ fst κ ⟩, because
-- [LJ-1.635] split the bill at ω and this is the strictly-above half
-- (agents/tasks/LJ-1-635/Probe635.agda:92).  So the row does not
-- apply by shape alone: one hypothesis it names is not in hand.
--
-- THE ANSWER IS ONE LINE OF ORDER, and it is `above→∉ω` below: the
-- strictly-above hypothesis IMPLIES the trophy clause, by ω's own
-- transitivity and ∈-irrefl.  So this frame is a STRENGTHENING of the
-- bill's site frame and not a sideways move, and `c3-payable` composes
-- at it by ONE application with NO re-proof.
--
-- A MODULE HYPOTHESIS TAKEN FROM A PREDECESSOR IS THE TYPE THAT
-- PREDECESSOR DELIVERED (the coder's standing clause, owner 2026-08-20).
-- This file takes `c3-payable` by IMPORT, not by copy, so no re-spelling
-- can drift from the type [LJ-1.629] typechecked.
--
-- TYPE-CHECKED ALONE, before the probe frame existed: runs/w3-*.out.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE.  Nothing lands in src/.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.  Cap: TWO MINUTES, set and reported by
-- this task.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-638.runs.C3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
import Cubical.Data.Empty as Empty
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
import LJ-1-629.Probe629
module P629 = LJ-1-629.Probe629 {ℓ} lem

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
module SL = hPropStructure 𝒮ʟ

-- =====================================================================
-- THE BRIDGE: strictly above ω implies the bill's trophy clause.
--
-- ω is an ordinal, so it is transitive (ω-ord, src/L/Ordinal.lagda.md;
-- IsOrd's first component is isTransV, src/L/Constructible.lagda.md:142,
-- and isTransV A is ∀ {x y} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ A ⟩ → ⟨ y ∈ˢ A ⟩ by
-- src/FOL/ZFStructure.lagda.md:116-118).  If ω were a member of α and α
-- a member of ω, then ω would be a member of ω, which regularity forbids
-- (∈-irrefl, src/V/Hierarchy.lagda.md:155).
--
-- THIS IS THE ROW THAT MAKES THE RESPELL A STRENGTHENING.  [LJ-1.629]'s
-- report item 1 (agents/tasks/LJ-1-629/lj-1.629-report.md:183-192)
-- proposed replacing the trophy clause by the strictly-above form; this
-- row measures that the replacement LOSES NOTHING, so every row
-- [LJ-1.629] proved under the trophy clause is still available here.
--
-- THE TREE ALREADY CARRIES THIS ROW, AND THIS COPY IS DELIBERATE.  The
-- C-42 sweep of this task found `inf-member`,
-- src/L/SquareLawClosed.lagda.md:60-61, which is this term letter for
-- letter (same statement, same body `∈-irrefl ω (ω-ord .fst _ _)`).  It
-- is NOT imported here because it is trapped inside a module
-- parameterized by `(α₀ : V ℓ) (oα₀ : IsOrd α₀)`
-- (src/L/SquareLawClosed.lagda.md:19-20) that its own body never uses,
-- so reaching it costs an invented α₀ and the whole chapter's frame for
-- one line of order.  The duplication and its cure are reported, not
-- hidden: see the report's C-42 section.
-- =====================================================================

above→∉ω : (α : S) → ⟨ ω ∈ˢ α ⟩ → ⟨ α ∈ˢ ω ⟩ → Empty.⊥
above→∉ω α ω∈α α∈ω = ∈-irrefl ω (ω-ord .fst ω∈α α∈ω)

-- =====================================================================
-- THE W3 TERM: conjunct 3 at THIS frame, from [LJ-1.629]'s row, by one
-- application and no re-proof.  The trophy-clause slot is paid by the
-- bridge above; the ⟨ ω ∈ˢ fst κ ⟩ slot is this frame's own hypothesis.
-- =====================================================================

c3-at-frame :
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ˢ fst κ ⟩
  → (γ : S) → ⟨ γ ∈ˢ fst κ ⟩ → ⟨ sucV γ ∈ˢ fst κ ⟩
c3-at-frame κ oκ cκ ω∈κ =
  P629.c3-payable κ oκ cκ (above→∉ω (fst κ) ω∈κ) ω∈κ
