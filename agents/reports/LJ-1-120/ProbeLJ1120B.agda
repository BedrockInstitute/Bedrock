{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.120] probe B: wire the generic environment-set into the
-- [LJ-1.115] build. The only missing premise is the K-closure of the
-- constructed set. This file supplies it as a telescope hypothesis and
-- shows that build then produces the whole someEnv obligation.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1120B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( envSetAt; envOverAt )
open import ProbeLJ1115A {ℓ} lem using ( module Obligation )
open import ProbeLJ1120A {ℓ} lem using ( module Generic )

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
    module G = Generic B ar
    E : S
    E = G.envSetGen
    EK : ⟨ fst E ∈ fst KS ⟩
    EK = envSetK B ar BK arK
    holdsAt : (ya yc b a c : S)
            → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 envSetAt zero (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
    holdsAt ya yc b a c =
      let module H = G.Holds
            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
            zero
            (suc (suc (suc (suc (suc zero)))))
            (suc (suc (suc (suc (suc (suc (suc zero)))))))
            refl refl refl
      in H.holds

  -- The decisive wire. With the generic construction and its K-closure
  -- supplied, the two delivered companions close the rest of someEnv.
  wired : ArityK → EnvInK → Obl
  wired aK iK = build closure aK iK
