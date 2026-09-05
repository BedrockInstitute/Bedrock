{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-234] Probe A.  THE PAIRING ON ω BY THE ORDER ROUTE, ZERO ARITHMETIC.
--
-- THE QUESTION.  Does `pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫` need an
-- object-language arithmetic (addition and multiplication formulas)?  The
-- current tree already delivers the order route `via-col-square` at every
-- INITIAL ordinal (α with ω ∈ α), with zero arithmetic.  The only gap is
-- the base at ω itself, because `Init ω` needs `ω ∈ ω`, refuted by
-- `∈-irrefl`.  This probe closes the base by instantiating the delivered
-- `InitialCore` at ω with three zero-arithmetic hypotheses:
--   ω-limit  : successor closure at ω,
--   noinj²ω  : the vacuous infinite-member clause at ω,
--   finite-excl-ω : the finite-exclusion chase at ω (no injection of ω
--                   into a finite square), which needs no `ω ∈ ω`.
-- The archive's `CoreAtω` shapes all three (SHAPE, never a price).
--
-- ABORT CRITERION, fixed before the run (D-1): if the instantiation or the
-- injectivity WALLS, report the elapsed seconds and stop.  The T59 record
-- says the ARCHIVED route's `pair-inj` (bound ∘ col→τ) walled at concrete
-- ω; the current tree replaced that shape with the direct
-- `p ↦ fiber ω (col∈ω p) .fst`, so the wall may not transfer.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-234.ProbeLJ1234A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase; module InitialCore; sq )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Nat as Nat
open Nat using ( ℕ )
import Cubical.Data.Fin.Base as FB
import Cubical.Foundations.Equiv as Equiv
open Equiv using ( equivFun; invEq; retEq; _≃_ )
open import Cubical.Foundations.Univalence using ( pathToEquiv )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_; ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open FiniteBase using ( ω-mem→numeral; toFin; toFin-inj; fromFin; fromFin-inj )
open FiniteBase using ( module AbstractChase )

-- =====================================================================
-- THE THREE HYPOTHESES OF InitialCore AT ω, all zero-arithmetic.
-- =====================================================================

-- Successor closure at ω: every member of ω is a numeral.
ω-limit : (γ : S) → ⟨ γ ∈ˢ ω ⟩ → ⟨ sucV γ ∈ˢ ω ⟩
ω-limit γ γ∈ω = PT.rec (snd (sucV γ ∈ˢ ω)) go (ω-mem→numeral γ γ∈ω)
  where
  go : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ˢ ω ⟩
  go (n , p) = subst (λ w → ⟨ sucV w ∈ˢ ω ⟩) (sym p) (#∈ω (suc n))

-- No member of ω contains ω.
ω∉β : (β : S) → ⟨ β ∈ˢ ω ⟩ → ⟨ ω ∈ˢ β ⟩ → Empty.⊥
ω∉β β β∈ω ω∈β = PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
  where
  go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (n , p) = ∈-irrefl ω (ω-ord .fst (subst (λ w → ⟨ ω ∈ˢ w ⟩) p ω∈β) (#∈ω n))

-- The vacuous infinite-member clause, in the square form.
noinj²ω : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩ → ⟨ ω ∈ˢ β ⟩
        → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
        → ((m n : ⟪ ω ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
noinj²ω β oβ β∈ω ω∈β f finj = ω∉β β β∈ω ω∈β

-- The numeral-into-ω injection, without `ω ∈ ω`.
numeral-into-ω : (m : ℕ) → ⟪ # m ⟫ → ⟪ ω ⟫
numeral-into-ω m i = fiber ω (ω-ord .fst (member (# m) i) (#∈ω m)) .fst

numeral-into-ω-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                   → numeral-into-ω m i₁ ≡ numeral-into-ω m i₂ → i₁ ≡ i₂
numeral-into-ω-inj m i₁ i₂ e = ↪-inj {a = # m}
  (sym (fiber ω (ω-ord .fst (member (# m) i₁) (#∈ω m)) .snd)
    ∙ cong (⟪ ω ⟫↪) e
    ∙ fiber ω (ω-ord .fst (member (# m) i₂) (#∈ω m)) .snd)

-- No injection of ω into a finite square.
no-inj-finite-ω : (n : ℕ) → (f : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
no-inj-finite-ω n f finj =
  AbstractChase.NoInj.no-inj
    (λ n → ⟪ # n ⟫)
    toFin toFin-inj
    fromFin fromFin-inj
    (⟪ ω ⟫)
    (numeral-into-ω)
    (numeral-into-ω-inj)
    n f finj

-- The finite-exclusion clause at ω.
finite-excl-ω : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
              → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
finite-excl-ω β oβ β∈ω f finj =
  PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
  where
  go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (n , p) = no-inj-finite-ω n f' finj'
    where
    e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
    e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
    f' : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
    f' x = equivFun e (f x)
    finj' : (x y : ⟪ ω ⟫) → f' x ≡ f' y → x ≡ y
    finj' x y e' = finj x y
      (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))

-- =====================================================================
-- THE BASE AT ω: InitialCore instantiated, then the direct pairing.
-- =====================================================================

module Coreω = InitialCore ω ω-ord ω-limit noinj²ω finite-excl-ω

open Coreω using ( PairA; colA; col∈α )

pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
pairω p = fiber ω {x = colA p} (col∈α p) .fst

pairω-inj : (p q : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω p ≡ pairω q → p ≡ q
pairω-inj p q e = SQ.col-inj ω ω-ord {p = p} {q = q}
  (sym (fiber ω {x = colA p} (col∈α p) .snd)
   ∙ cong (⟪ ω ⟫↪) e
   ∙ fiber ω {x = colA q} (col∈α q) .snd)

squareω : sq ω
squareω = pairω , pairω-inj
