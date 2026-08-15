{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.344] A THIRD FALSE TIE.  D-10 AGAIN, ON THE ARITY CONJUNCT.
--
-- `[LJ-1.338]` counted six construction residues.  `[LJ-1.341]` refuted
-- two of them and `[LJ-1.343]` repaired those two.  This file prices the
-- TRUTH of a third before anyone prices its proof.
--
-- THE TIE, verbatim from src/L/Condensation.lagda.md:7130-7136:
--
--   (wCodesK : (w' : S) -> < fst w' in K >
--             -> (k : N) -> (c ar a b : S) -> < fst c in fst w' >
--             -> fst c = pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
--             -> < fst ar in K > x < fst a in K > x < fst b in K >
--             x || Sigma[ n in N ] (fst ar = # n) ||)
--
-- THE LAST CONJUNCT IS THE RESIDUE.  It says the arity component of a
-- code is a NUMERAL.  The premise never says `w'` is a code set: it says
-- only that `w'` is in the bound and that `c` is a member of `w'`.  So
-- ANY set in the bound with ANY member of the pair shape refutes it.
--
-- THE COUNTERMODEL.  Take `ar` to be the singleton of the numeral one,
-- which is not a numeral, put the code inside its own singleton, and
-- close both into the bound with the SAME `KFacts` fields the supply
-- uses.  Nothing here is a new closure fact.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.Data.Nat using ( ℕ; zero; suc; znots )
open import Cubical.Data.Nat.Order using ( zero-≤; suc-≤-suc )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Induction.WellFounded using ( Acc; acc )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-344.Residue344 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Coding {ℓ} using ( pr; #mono; #-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst )
open GM.AbsL using ( _^_ )

open import LJ-1-344.Supply344 {ℓ} lem
  using ( module TieSupply; sglS; x∈pair; pair-only )

open hPropStructure 𝒮ʟ using ( S )
module HV = hPropStructure 𝒮ᵥ

-- =====================================================================
-- PART 0.  THE SINGLETON OF ONE IS NOT A NUMERAL.
--
-- A WALL AND THE WAY ROUND IT, MEASURED.  The obvious `zero` clause
-- reads `# 0` as the empty set and transports along `V.Model`'s
-- `empty-spec`.  That does NOT return: `Bisect344A.agda` ran past 400 s
-- and was interrupted, while `Bisect344B.agda`, the same statement
-- without that one clause, exits in 1.94 s.  A transport along an hProp
-- path out of the hierarchy is the cost.  The cure is to refuse the
-- membership by REGULARITY instead, which never leaves the hProp.
-- =====================================================================

noCycle2 : (a : V ℓ) → Acc HV._∈ᵗ_ a → (b : V ℓ)
         → ⟨ a ∈ b ⟩ → ⟨ b ∈ a ⟩ → Empty.⊥
noCycle2 a (acc rec) b ab ba = noCycle2 b (rec b ba) a ba ab

zero∈one : ⟨ (# 0) ∈ (# 1) ⟩
zero∈one = #mono 0 1 (suc-≤-suc zero-≤)

sgl1-not-numeral : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # m → Empty.⊥
sgl1-not-numeral zero q =
  noCycle2 (# 1) (regularityV (# 1)) (# 0)
    (subst (λ s → ⟨ (# 1) ∈ s ⟩) q (x∈pair (# 1) (# 1)))
    zero∈one
sgl1-not-numeral (suc m) q = znots (#-inj 0 1 zero≡one)
  where
  zero∈ : ⟨ (# 0) ∈ ⁅ # 1 , # 1 ⁆ ⟩
  zero∈ = subst (λ s → ⟨ (# 0) ∈ s ⟩) (sym q)
    (#mono 0 (suc m) (suc-≤-suc zero-≤))

  zero≡one : (# 0) ≡ (# 1)
  zero≡one = pair-only (# 1) (# 0) zero∈

-- =====================================================================
-- PART 1.  THE REFUTATION.
--
-- The four parameters are `KFacts` fields, exactly as `TieSupply` takes
-- them, plus `numK1` for the arity witness.  `u` and `hu` say the
-- carrier slot has a member.  WITHOUT `u` the refutation would be empty
-- and would prove nothing, which is the trap this whole episode is
-- about (C-45).
-- =====================================================================

module Refute {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (u : S) (hu : ⟨ fst u ∈ fst (lookup A γ) ⟩) where

  open TieSupply A K γ numK0 pairK carrierK arityK using ( sglK )

  private
    bnd : V ℓ
    bnd = fst (lookup K γ)

  -- The arity slot.  `fst arS` is `⁅ # 1 , # 1 ⁆`, which PART 0 refutes
  -- as a numeral.
  arS : S
  arS = sglS (numeralL 1)

  ar-fst : fst arS ≡ ⁅ # 1 , # 1 ⁆
  ar-fst = cong (λ w → ⁅ w , w ⁆) (numeralL-fst 1)

  arS∈K : ⟨ fst arS ∈ bnd ⟩
  arS∈K = sglK (numeralL 1) numK1

  -- The code, of exactly the shape the tie's equation names, at `k := 0`
  -- and `a := b := u`.
  cS : S
  cS = prʟ arS (prʟ (numeralL 0) (prʟ u u))

  uK : ⟨ fst u ∈ bnd ⟩
  uK = carrierK u hu

  cS∈K : ⟨ fst cS ∈ bnd ⟩
  cS∈K = pairK arS (prʟ (numeralL 0) (prʟ u u)) arS∈K
           (pairK (numeralL 0) (prʟ u u) numK0 (pairK u u uK uK))

  -- The "code set": the singleton of the code.  It is in the bound by
  -- the SAME closure the supply uses, and the code is its member.
  wS : S
  wS = sglS cS

  wS∈K : ⟨ fst wS ∈ bnd ⟩
  wS∈K = sglK cS cS∈K

  cS∈wS : ⟨ fst cS ∈ fst wS ⟩
  cS∈wS = x∈pair (fst cS) (fst cS)

  codeEq : fst cS ≡ pr (fst arS) (pr (# 0) (pr (fst u) (fst u)))
  codeEq = prʟ-fst arS (prʟ (numeralL 0) (prʟ u u))
    ∙ cong (pr (fst arS))
        (prʟ-fst (numeralL 0) (prʟ u u)
          ∙ cong₂ pr (numeralL-fst 0) (prʟ-fst u u))

  -- THE TIE, type VERBATIM from src/L/Condensation.lagda.md:7130-7136.
  WCodesK : Type (ℓ-suc ℓ)
  WCodesK = (w' : S) → ⟨ fst w' ∈ fst (lookup K γ) ⟩
          → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst ar ∈ fst (lookup K γ) ⟩
            × ⟨ fst a ∈ fst (lookup K γ) ⟩
            × ⟨ fst b ∈ fst (lookup K γ) ⟩
          × ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁

  -- NON-VACUITY.  The three memberships the tie also concludes are TRUE
  -- at these witnesses, so the type is refuted at a point where its
  -- other conjuncts hold.  Only the arity conjunct dies.
  other-conjuncts : ⟨ fst arS ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩
  other-conjuncts = arS∈K , uK , uK

  wCodesK-false : WCodesK → Empty.⊥
  wCodesK-false h = PT.rec Empty.isProp⊥
    (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })
    (h wS wS∈K 0 cS arS u u cS∈wS codeEq .snd .snd .snd)
