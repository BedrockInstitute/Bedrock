{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.236] probe A4.  Internal LeastCard: the least δ (an L-element)
-- such that some L-element F codes an injection ⟪κ⟫ ↪ ⟪δ⟫, plus the
-- internal IsCardinal predicate.  The measured term is the COLD SECONDS
-- of the internal least-of over orderAt, with the truncated L-element
-- existential inside the predicate.
--
--   S1  injAt, copied from [LJ-1.229] ProbeLJ1229A S1 (A2).  Not a
--       master yet.
--   S2  InjCode:  "F codes an injection from a into b" (the four
--       conjuncts A2's Small readback consumes).
--   S3  IsCardinalL:  the internal cardinal (A4), over internal coding.
--   S4  InternalLeastCard:  leastOf (orderAt β oβ) over the predicate
--       "there is an L-element coding ⟪κ⟫ ↪ ⟪δ⟫".  The nonempty witness
--       is a parameter here: it is A2's identity graph `lid`, which is
--       A5's deliverable, not A4's.
--   G   The C-38 guard: instantiated at ω, a real L-ordinal.
--
-- Probe only.  Nothing lands in src/.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g"; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-236.ProbeLJ1236A4 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _≐_; _⇒̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf )
open import L.Coding.Model {ℓ}
  using ( appAt; svAt; domAt )
open import V.Presentation {ℓ} using ( member )
open import Cubical.Data.FinData.Base using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- S1.  injAt, copied from [LJ-1.229] ProbeLJ1229A S1 (A2).
-- ---------------------------------------------------------------------

injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))

-- ---------------------------------------------------------------------
-- S2.  "F codes an injection from a into b."
-- ---------------------------------------------------------------------

InjCode : S → S → S → Type (ℓ-suc ℓ)
InjCode F a b =
    ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)

-- ---------------------------------------------------------------------
-- S3.  The internal cardinal (A4).
-- ---------------------------------------------------------------------

IsCardinalL : S → Type (ℓ-suc ℓ)
IsCardinalL κ =
  (δ : S) → ⟨ fst δ ∈ fst κ ⟩
          → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)

-- ---------------------------------------------------------------------
-- S4.  Internal LeastCard: the least L-ordinal δ above the stage such
-- that some L-element codes ⟪κ⟫ ↪ ⟪δ⟫.  The truncated existential over
-- F sits INSIDE the least-of predicate — the term [LJ-1.136] inferred
-- makes the seconds rise.
-- ---------------------------------------------------------------------

module InternalLeastCard (κ : S) (oκ : IsOrd (fst κ)) where

  β : V ℓ
  β = stageBound (fst κ) (snd κ) .fst

  oβ : IsOrd β
  oβ = stageBound (fst κ) (snd κ) .snd .fst

  up : Mem (Lset β) → S
  up (x , m) = x , Lset→isL β oβ x m

  Good : Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good δ = (∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁) , squash₁

  module Selected
    (nonempty : ∥ Σ[ δ ∈ Mem (Lset β) ] ⟨ Good δ ⟩ ∥₁)
    where

    least : Σ[ δ ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good δ
    least = leastOf (orderAt β oβ) lem Good nonempty

    δ-card : Mem (Lset β)
    δ-card = fst least

    -- the internal least cardinal, as an L-element
    δᴸ : S
    δᴸ = up δ-card

    -- the witness: some L-element codes ⟪κ⟫ ↪ ⟪δᴸ⟫, still truncated
    δ-inj : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ δᴸ ∥₁
    δ-inj = fst (snd least)

    -- leastness at a member of δᴸ: a smaller δ' with a code is absurd
    δ-min : (b : Mem (Lset β)) → ⟨ Good b ⟩ → (SWO._<∙_ (orderAt β oβ) b δ-card → Empty.⊥)
    δ-min = snd (snd least)

-- ---------------------------------------------------------------------
-- G.  The C-38 guard: ω is a real L-ordinal, so the module parameters
-- elaborate at a concrete site.  The nonempty witness is NOT supplied
-- here (it is A2's identity graph `lid`, A5's deliverable); the guard
-- shows only that β, oβ and up are inhabited at ω.
-- ---------------------------------------------------------------------

module Atω where

  hω : ⟨ isL ω ⟩
  hω = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

  aω : S
  aω = ω , hω

  β : V ℓ
  β = stageBound (fst aω) (snd aω) .fst

  oβ : IsOrd β
  oβ = stageBound (fst aω) (snd aω) .snd .fst

  up : Mem (Lset β) → S
  up (x , m) = x , Lset→isL β oβ x m
