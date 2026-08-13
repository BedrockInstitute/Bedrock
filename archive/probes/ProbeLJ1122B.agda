{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.122] acceptance probe. This is ProbeLJ1120B with the generic
-- construction and its envSetAt adequacy taken from the masters, not from
-- ProbeLJ1120A. It shows that someEnv still closes once envSetK is supplied.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1122B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( envSetAt; envOverAt )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import L.Coding.Sound {ℓ} lem using ( module AmbientHoldsGen )
open import ProbeLJ1115A {ℓ} lem using ( module Obligation )

open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Wire (n : ℕ) (K : Fin (5 + n)) (γ : S ^ (11 + n))
  (BK : ⟨ fst (lookup zero γ) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  (envSetK : (B ar : S)
           → ⟨ fst B ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
           → ⟨ fst (Generic.envSetGen B ar)
                ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩)
  where

  module O = Obligation n K γ
  open O

  B : S
  B = lookup zero γ

  closure : EnvSetClosure
  closure ar arK =
    E , (EK , holdsAt)
    where
    E : S
    E = Generic.envSetGen B ar
    EK : ⟨ fst E ∈ fst KS ⟩
    EK = envSetK B ar BK arK
    holdsAt : (ya yc b a c : S)
            → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 envSetAt zero (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
    holdsAt ya yc b a c =
      let module H = AmbientHoldsGen
            B ar
            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
            zero
            (suc (suc (suc (suc (suc zero)))))
            (suc (suc (suc (suc (suc (suc (suc zero)))))))
            refl refl refl
      in H.holds

  wired : ArityK → EnvInK → Obl
  wired aK iK = build closure aK iK
