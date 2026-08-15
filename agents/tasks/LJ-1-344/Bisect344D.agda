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

module LJ-1-344.Bisect344D {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
