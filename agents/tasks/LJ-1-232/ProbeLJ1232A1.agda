{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.232] probe A1.  Does `⟨ isL α ⟩` alone supply the ordinal facts
-- the restated square-law chain needs at each site?
--
-- The ambient chain (`ProbeLJ1156A.agda`, 393 lines, 133 s cold) opens
-- `hPropStructure 𝒮ᵥ` and carries no `⟨ isL α ⟩`.  Route A-prime restates
-- it over the L-carrier 𝒮ʟ with the per-site hypothesis `⟨ isL α ⟩`.
-- This probe restates ONE theorem of that chain, `LeastCardInj`, over
-- the L-carrier, and records which extra L-lemmas the site demands.
--
--   A1  `LeastCardInjL`: the same 44-line term, but α : S = Σ[ x ∈ V ] isL x,
--       and the predicate `InjP'` over `⟪ sucV (fst α) ⟫` is lifted into
--       the L-carrier by `up`.  The lift is where the extra L-lemmas
--       surface.  The deliverable is the LIST, not the line count.
--
-- Probe only.  Nothing lands in src/.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g"; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-232.ProbeLJ1232A1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( ordSWO )
import L.Ordinal {ℓ} as Ord
open Ord using ( mem-ord; suc-ord; ω-ord )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
import V.Hierarchy {ℓ} as Hier
open Hier using ( 𝒮ᵥ )
import V.Model {ℓ} as VModel
open VModel using ( self∈sucV )
import V.Presentation {ℓ} as VPres
open VPres using ( member; fiber; ↪-inj )
import FOL.ZFStructure as ZF
open ZF using ( module hPropStructure )
import Cubical.HITs.CumulativeHierarchy.Properties as CH
open CH using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
open CHC using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )
import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} as WOBase
open WOBase using ( SWO; IsLeast; leastOf; module SWO )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- The injection type, exactly as the ambient chain carries it.
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- A1.  LeastCardInj restated over the L-carrier.
--
--   Ambient (`ProbeLJ1156A.agda:170-242`):
--     module LeastCardInj (α : S) (oα : IsOrd α) where
--       Inj γ = ⟪ α ⟫ ↪ ⟪ γ ⟫           -- S = V, the ambient carrier
--       InjP' γ = InjP (⟪ sucV α ⟫↪ γ)  -- no lift needed
--
--   Restated here:
--     α : S = Σ[ x ∈ V ] isL x, so the carrier is L and every ordinal
--     the chain touches must carry a level-hood certificate.  The lift
--     `up` is where the extra L-lemmas appear.
-- =====================================================================

module LeastCardInjL (α : S) (oα : IsOrd (fst α)) where

  Inj : S → Type ℓ
  Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫

  InjP : S → hProp ℓ
  InjP γ = ∥ Inj γ ∥₁ , squash₁

  -- EXTRA LEMMA 1: sucV (fst α) is an L-ordinal.  `⟨ isL α ⟩` alone
  -- does NOT give this; it needs `ord∈Lset-suc` (an ordinal appears at
  -- the stage after itself) and `Lset→isL` (membership in a stage is
  -- level-hood).
  hSucα : ⟨ isL (sucV (fst α)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst α))) (suc-ord (suc-ord oα)) (sucV (fst α))
            (ord∈Lset-suc (sucV (fst α)) (suc-ord oα))

  -- EXTRA LEMMA 2: `isL-trans` propagates `⟨ isL (sucV (fst α)) ⟩` down
  -- to the members of sucV (fst α), turning a member of the tower into
  -- an L-element.
  up : ⟪ sucV (fst α) ⟫ → S
  up m = ⟪ sucV (fst α) ⟫↪ m
       , isL-trans (member (sucV (fst α)) m) hSucα

  InjP' : ⟪ sucV (fst α) ⟫ → hProp ℓ
  InjP' γ = InjP (up γ)

  w : SWO (⟪ sucV (fst α) ⟫)
  w = ordSWO (sucV (fst α)) (suc-ord oα)

  self : ⟪ sucV (fst α) ⟫
  self = fiber (sucV (fst α)) (self∈sucV (fst α)) .fst

  self-eq : ⟪ sucV (fst α) ⟫↪ self ≡ fst α
  self-eq = fiber (sucV (fst α)) (self∈sucV (fst α)) .snd

  idInj : ⟪ fst α ⟫ ↪ ⟪ fst α ⟫
  idInj = (λ x → x) , (λ x y e → e)

  nonempty : ∥ Σ[ b ∈ ⟪ sucV (fst α) ⟫ ] ⟨ InjP' b ⟩ ∥₁
  nonempty = ∣ self , subst (λ v → ∥ ⟪ fst α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym self-eq)
                ∣ idInj ∣₁ ∣₁

  least : Σ[ γ ∈ ⟪ sucV (fst α) ⟫ ] IsLeast w InjP' γ
  least = leastOf w lem InjP' nonempty

  γ-card : ⟪ sucV (fst α) ⟫
  γ-card = fst least

  κ : S
  κ = up γ-card

  oκ : IsOrd (fst κ)
  oκ = mem-ord {A = sucV (fst α)} (suc-ord oα) (fst κ)
         (member (sucV (fst α)) γ-card)

  κ∈sα : ⟨ fst κ ∈ˢ sucV (fst α) ⟩
  κ∈sα = member (sucV (fst α)) γ-card

  -- The witness, an injection, still truncated, still not an hProp.
  κ-inj : ∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁
  κ-inj = fst (snd least)

  κ-min : (b : ⟪ sucV (fst α) ⟫) → ⟨ InjP' b ⟩
        → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

  κ-min-at : (δ : S) → ⟨ fst δ ∈ˢ fst κ ⟩
           → ∥ ⟪ fst α ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
  κ-min-at δ δ∈κ α↪δ = κ-min b bInjP b<γ
    where
    δ∈sα : ⟨ fst δ ∈ˢ sucV (fst α) ⟩
    δ∈sα = suc-ord oα .fst {x = fst κ} {y = fst δ} δ∈κ κ∈sα
    b : ⟪ sucV (fst α) ⟫
    b = fiber (sucV (fst α)) δ∈sα .fst
    bδ : ⟪ sucV (fst α) ⟫↪ b ≡ fst δ
    bδ = fiber (sucV (fst α)) δ∈sα .snd
    bInjP : ⟨ InjP' b ⟩
    bInjP = subst (λ v → ∥ ⟪ fst α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym bδ) α↪δ
    b<γ : SWO._<∙_ w b γ-card
    b<γ = subst (λ z → ⟨ z ∈ˢ fst κ ⟩) (sym bδ) δ∈κ

-- =====================================================================
-- G.  The C-38 guard: the lift `up` is inhabited at a REAL ordinal.
--   ω is an L-ordinal; `up` carries a real member of sucV ω into S.
-- =====================================================================

module Atω where

  hω : ⟨ isL ω ⟩
  hω = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

  aω : S
  aω = ω , hω

  selfω : ⟪ sucV (fst aω) ⟫
  selfω = fiber (sucV (fst aω)) (self∈sucV (fst aω)) .fst

  module L = LeastCardInjL aω ω-ord

  upω : S
  upω = L.up selfω

  -- the lifted member really is ω itself
  upω-fst : fst upω ≡ fst aω
  upω-fst = fiber (sucV (fst aω)) (self∈sucV (fst aω)) .snd
