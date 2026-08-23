{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.592]  W3.  THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND
-- TYPECHECKED ALONE.
--
--   The brief names it: "the legality of the recursion", stated as
--
--     -- isProp (InjL (Lset α) α), at this frame, INHABITED
--
--   The whole of route 1 rests on it.  `[LJ-1.584]`'s review says a
--   next brief "may assume `SqFam α` freely under `PT.rec`, because the
--   target is a proposition"
--   (agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:123-126).
--   That sentence is a claim about THIS type and nothing else, and this
--   file is where it is measured rather than repeated.
--
--   Nothing is postulated.  There is no hole.  Nothing lands in `src/`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible using ( IsOrd )

module LJ-1-592.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.GCH {ℓ} lem using ( InjL )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- Every ordinal is an L-element.  One line, and it is
-- `agents/tasks/LJ-1-561/Probe561.agda:110-111` repeated so that this
-- slice stands alone.  `src/L/SquareLawClosed.lagda.md:51-52` is the
-- same term, sealed there and not exported.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

-- The ordinal as an L-element.  `agents/tasks/LJ-1-568/Probe568.agda:102-103`.
ordS : (β : V ℓ) → IsOrd β → S
ordS β oβ = β , isL-ord β oβ

-- THE FRAME.  This is `[LJ-1.584]`'s `Reopener`
-- (agents/tasks/LJ-1-584/Probe584.agda:250-251), taken as the type that
-- predecessor DELIVERED and not restated in other words.
Target : (α : V ℓ) → IsOrd α → Type (ℓ-suc ℓ)
Target α oα = InjL (LsetS α oα) (ordS α oα)

-- W3.  INHABITED.  `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
-- (src/L/GCH.lagda.md:37-38), so the target is a truncation and
-- `squash₁` is the whole proof.  NOTE WHAT THIS DOES NOT NEED: it does
-- not need `isPropInjCode` (agents/tasks/LJ-1-576/Probe576.agda:77-84),
-- because the truncation is outside the Σ.  The propositionality is
-- free at ANY pair, and the frame is irrelevant to it.
isPropTarget : (α : V ℓ) (oα : IsOrd α) → isProp (Target α oα)
isPropTarget α oα = PT.squash₁

-- AND THE RECURSION IS THEREFORE LEGAL, at any hypothesis whatever.
-- This is the freedom in one line: a truncated hypothesis costs nothing
-- when the goal is this target.
untrunc-free : {ℓ' : Level} {A : Type ℓ'} (α : V ℓ) (oα : IsOrd α)
             → (A → Target α oα) → PT.∥ A ∥₁ → Target α oα
untrunc-free α oα f = PT.rec (isPropTarget α oα) f
