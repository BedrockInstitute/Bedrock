{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.41] THE ALLIN BODY'S FIRST BINDER, MACHINE-CHECKED.
--
-- The machine's bodyAll (src/L/Coding/Model.lagda.md:1881-1884)
-- reads the term's value at an UNBOUNDED first binder:
-- `∀̇ (tmValAt a9B e9B w9B ⇒̇ ∀̇∈ B ((var zero ∈̇ var (suc zero))
-- ⇒̇ ...))` -- the value w is any set.
--
-- The story's bndBodyAll (src/L/Condensation.lagda.md:996-1008)
-- reads the term's value at the FIRST B-MEMBER:
-- `∀̇∈ (var (suc^8 B)) (tmValB t e v ⇒̇ ...)` with the value slot
-- v = zero, the binder's own variable.
--
-- This probe attempts the story-to-machine direction of the body
-- transfer.  The machine's arbitrary value w must be handed to the
-- story's binder, which quantifies over members of B.  The natural
-- site fact (the value lies in K) cannot supply w ∈ B.
-- EXPECTED: a type error at `in-try`, where the story's first binder
-- is applied at w.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ141B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( tmValAt; bodyAll )
open import L.Condensation {ℓ} lem using ( bndBodyAll )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- THE ATTEMPTED BODY TRANSFER, story-to-machine, at the innermost
-- environment z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (8 + m).  The
-- story's bndBodyAll is peeled at its extAtB frame.  The machine's
-- bodyAll needs its first binder at every value w; the story's first
-- binder ranges over B.  The site fact `valK` says the value lies in
-- K, which cannot make w a member of B.
in-try : ∀ {m} (B K t0 t1 : Fin m) (env : S ^ (7 + m))
       → (z : S) → ⟨ fst z ∈ fst (lookup (suc (suc zero)) env) ⟩
       → ((w : S) → ⟨ (w ∷ z ∷ env) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero) zero ⟩
          → ⟨ fst w ∈ fst
                (lookup (suc (suc (suc (suc (suc (suc (suc K))))))) env) ⟩)
       → ⟨ env ⊨ bndBodyAll B K t0 t1 ⟩
       → ⟨ (z ∷ env) ⊨ bodyAll B ⟩
in-try B K t0 t1 env z z∈yc valK h =
    h .fst z z∈yc .fst
  , (λ w hw x x∈w e' hc →
      let step = h .fst z z∈yc .snd w (valK w hw)
      in x∈w)
