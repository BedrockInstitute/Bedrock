{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.38] THE CONTROL.  THIS FILE MUST FAIL.
--
-- ProbeDD25E1 `story-forces-all` proves that one member of the value
-- forces every member of E in K into the value.  That proof is only
-- evidence of a defect if it FAILS against a correct body.
--
-- This file repeats the proof, word for word, against a body that
-- differs from the delivered `atomBodyB`
-- (src/L/Condensation.lagda.md:940-957) in ONE index: the environment
-- argument of the two term readers moves from `suc (suc (suc zero))`,
-- the frame's member, to `suc (suc zero)`, the extension candidate.
--
-- EXPECTED: a type error at `control`.  The collapse proof must not go
-- through, because the corrected condition mentions the element it
-- defines.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25E3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _∨̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Condensation {ℓ} lem using ( extAtB; tmValB )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The delivered atom body with ONE index corrected.  Everything else
-- is copied from src/L/Condensation.lagda.md:940-957.
atomBodyB' : ∀ {m} → Fin m → Fin m → Fin m → Formula S (10 + m)
           → Formula S (8 + m)
atomBodyB' t0 t1 K cmp =
  (var zero ∈̇ var (suc (suc zero)))
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
        (tmValB (suc (suc (suc (suc (suc (suc (suc zero)))))))
                (suc (suc zero))
                (suc zero)
                (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc t0))))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))))
        ∧̇ tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc (suc zero))
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc t0))))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))))
        ∧̇ cmp))

bodyM' : ∀ {m} → Fin m → Fin m → Fin m → Formula S (7 + m)
bodyM' K t0 t1 =
  extAtB (suc (suc zero))
         (suc (suc (suc (suc (suc (suc (suc K)))))))
         (atomBodyB' t0 t1 K (var (suc zero) ∈̇ var zero))

module AtomRow' {m : ℕ} (K t0 t1 : Fin m) (γ : S ^ m)
                (c ar a b yc E : S) where

  δ : S → S ^ (7 + m)
  δ e = e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  -- THE CONTROL.  Same proof term as ProbeDD25E1 `story-forces-all`.
  control : (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ δ e ⊨ bodyM' K t0 t1 ⟩
    → (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩ → ⟨ fst z ∈ fst E ⟩
    → ⟨ fst z ∈ fst yc ⟩
  control e e∈ h z z∈K z∈E = h .snd z z∈K (z∈E , h .fst e e∈ .snd)
