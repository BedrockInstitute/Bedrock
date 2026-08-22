{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.557] W3.  THE STAGE `InternalLeastCard` SELECTS OVER, AT THIS
-- FRAME, TYPE ONLY.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- the stage InternalLeastCard selects over, at this frame, TYPE
--     -- ONLY
--
-- THIS FRAME is a member `a` of the successor cardinal δ, with its own
-- ordinal certificate.  `[LJ-1.552]`'s route would run
-- `InternalLeastCard` there; the brief's obligation asks instead for a
-- code `F : S` with NO stage side condition.  This slice writes both
-- shapes and the one bridge between them that is free, so the D-10
-- checks are read off types and not off prose.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-557.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Cardinal {ℓ} lem
  using ( InjCode; module SiteBound; module LeastCardInjL )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  The frame: one member `a` of δ, with its ordinal certificate.
-- =====================================================================

module Frame (a : S) (oa : IsOrd (fst a)) where

  -- THE STAGE.  `InternalLeastCard`'s site is `SiteBound`'s β
  -- (src/L/Cardinal.lagda.md:237), and `SiteBound` is `stageBound`
  -- (src/L/Cardinal.lagda.md:163-169).
  open SiteBound a using ( β; oβ; up )

  site : V ℓ
  site = β

  -- THE ORDER `InternalLeastCard` SELECTS WITH
  -- (src/L/Cardinal.lagda.md:247, :249).  It is `orderAt`, the birth
  -- order on the members of a stage (src/L/Choice/Step.lagda.md:730).
  sel : SWO (Mem (Lset β))
  sel = orderAt β oβ

  -- WHAT `InternalLeastCard.Good` DEMANDS at this frame, with the
  -- direction the obligation wants: a code of `a` into a target
  -- (src/L/Cardinal.lagda.md:239-243, transposed).  The code is a
  -- MEMBER OF THE STAGE.
  Demand : Mem (Lset β) → Type (ℓ-suc ℓ)
  Demand γ = ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a (up γ) ∥₁

  -- WHAT THE BRIEF'S OBLIGATION DEMANDS.  The code is any element of
  -- the L-carrier.  NO stage side condition.
  Obl : S → Type (ℓ-suc ℓ)
  Obl b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁

  -- THE ONE FREE DIRECTION: a stage-bounded code IS a code.
  bridge : (γ : Mem (Lset β)) → Demand γ → Obl (up γ)
  bridge γ = PT.map (λ { (F , c) → up F , c })

  -- THE OTHER DIRECTION, TYPE ONLY.  This is the `F` conjunct
  -- `[LJ-1.425]` left as a hole (agents/tasks/LJ-1-425/Probe425.agda:92).
  -- Nothing below inhabits it.
  Converse : Type (ℓ-suc ℓ)
  Converse = (γ : Mem (Lset β)) → Obl (up γ) → Demand γ

  -- THE ORDER THIS TASK SELECTS WITH INSTEAD: `LeastCardInjL`'s sealed
  -- `w` (src/L/Cardinal.lagda.md:96-98), whose comparison IS ambient
  -- membership (`w-lt`, src/L/Cardinal.lagda.md:102-105).
  private
    module M = LeastCardInjL a oa

  memOrd : SWO ⟪ sucV (fst a) ⟫
  memOrd = M.w
