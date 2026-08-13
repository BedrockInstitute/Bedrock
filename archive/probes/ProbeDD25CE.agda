{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.33] The equality check.
--
-- The return's probe writes the story's step body by hand
-- (src/ProbeLJ133.agda:70-76).  This file states that the hand-written
-- body IS the delivered body (src/L/Coding/Sequence.lagda.md:113-117),
-- by refl.  If this file typechecks, the two formulas are definitionally
-- equal, so a story clause that reuses the delivered body proves the
-- SAME theorem as the return's probe.
--
-- Untracked probe; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25CE {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ} using ( appAt; extAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt )
open import L.Coding.Sequence {ℓ} lem using ( StepAt; StepBody )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- The hand-written body of the return's probe, at the shifted slots.
HandBody : {n : ℕ} (b f : Fin n) → Formula S (5 + n)
HandBody b f =
  (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc (suc b))))))
  ∧̇ ( appAt (suc (suc (suc (suc (suc f)))))
             (suc (suc zero)) (suc zero)
    ∧̇ ( DefAt zero (suc zero)
      ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

-- FACT 1: the hand-written body is the DELIVERED body at the shifted
-- slots.  So the story's step body is not new content.
body-eq : {n : ℕ} (b f : Fin n)
        → HandBody b f ≡ StepBody {suc n} (suc b) (suc f)
body-eq b f = refl

-- The return's story clause, written out (src/ProbeLJ133.agda:80-96).
module Hand {n : ℕ} (K : Fin (suc n)) (v b f : Fin n) where
  StepWit : Formula S (suc (suc n))
  StepWit =
    ∃̇∈ (var (suc (suc b)))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          (HandBody b f)))

  StepBnd : Formula S (suc n)
  StepBnd = ∀̇ ((var zero ∈̇ var (suc (suc v))) ⇒̇ StepWit)
          ∧̇ ∀̇ (StepWit ⇒̇ (var zero ∈̇ var (suc (suc v))))

-- FACT 2: the story clause is one extAt over the bounded witness.
bnd-eq : {n : ℕ} (K : Fin (suc n)) (v b f : Fin n)
       → Hand.StepBnd K v b f ≡ extAt (suc v) (Hand.StepWit K v b f)
bnd-eq K v b f = refl

-- FACT 3: the DELIVERED clause is one extAt over the SAME body with the
-- three bounds removed.  Facts 1 to 3 together say leg D is a bound-drop.
mach-eq : {n : ℕ} (v b f : Fin n)
        → StepAt {suc n} (suc v) (suc b) (suc f)
        ≡ extAt (suc v) (∃̇ (∃̇ (∃̇ (HandBody b f))))
mach-eq v b f = refl
