{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.581]  THE THIRD BISECTION.  `pr-inj` and `↪-inj` cost 679 ms
-- TOGETHER when each stands alone (runs/bisect-2.out), and 159.78 s
-- when composed through `ΣPathP` (runs/bisect-1.out).  So the price is
-- in the COMPOSITION.  Three ways to write the same pair path, one
-- profiled run, each carrying its own number.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-581.runs.Bisect {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Presentation {ℓ} using ( ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import Cubical.Data.Sigma using ( ΣPathP )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

Raw : (κ : S) (p q : ⟪ fst κ ⟫ × ⟪ fst κ ⟫) → Type (ℓ-suc ℓ)
Raw κ p q = pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p))
          ≡ pr (⟪ fst κ ⟫↪ (fst q)) (⟪ fst κ ⟫↪ (snd q))

-- A.  `ΣPathP`, which is what [LJ-1.556] writes at Probe556.agda:178.
viaΣPathP : (κ : S) (p q : ⟪ fst κ ⟫ × ⟪ fst κ ⟫) → Raw κ p q → p ≡ q
viaΣPathP κ p q raw =
  ΣPathP ( ↪-inj {a = fst κ} (fst (pr-inj raw))
         , ↪-inj {a = fst κ} (snd (pr-inj raw)) )

-- B.  The interval abstraction, spelled out.
viaInterval : (κ : S) (p q : ⟪ fst κ ⟫ × ⟪ fst κ ⟫) → Raw κ p q → p ≡ q
viaInterval κ p q raw i =
  ( ↪-inj {a = fst κ} (fst (pr-inj raw)) i
  , ↪-inj {a = fst κ} (snd (pr-inj raw)) i )

-- C.  `cong₂` on the constructor.
viaCong₂ : (κ : S) (p q : ⟪ fst κ ⟫ × ⟪ fst κ ⟫) → Raw κ p q → p ≡ q
viaCong₂ κ p q raw = cong₂ _,_
  (↪-inj {a = fst κ} (fst (pr-inj raw)))
  (↪-inj {a = fst κ} (snd (pr-inj raw)))
