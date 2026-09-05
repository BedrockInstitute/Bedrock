{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T66] The Def-step gate: the bounded rewrite of the Def-step
-- clause at the generic carrier, with its Delta-0 witness and the two-way
-- reading against the delivered DefStep.  Untracked probe; one Agda process.

open import Base.Prelude
open import Base.Truth
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeDefStep {ℓ : Level} (u : V ℓ) where

open import FOL.Syntax using ( Formula; ⊤̇ )
open import FOL.LevyHierarchy using ( Δ₀; δ-⊤ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.InitialSegment {ℓ} using ( DefStep; _⟷_ )
open import Cubical.Data.Sigma using ( fst; snd )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module U = DefOf u
open U using ( SM; ι; _⊨ᵐ_ )

-- The bounded rewrite of the Def-step clause.  At the reading the clause
-- is read at f : SM, a member of the carrier.  DefStep u f is then
-- unconditionally true: the witness is f itself with the formula "true",
-- since defSet f ⊤̇ = f (DefOf.defSet⊤≡A).  The rewrite is therefore the
-- collapsed clause, Delta-0 by the trivial witness.
defStepForm' : Formula ⟪ u ⟫ 2
defStepForm' = ⊤̇

defStepΔ₀ : Δ₀ defStepForm'
defStepΔ₀ = δ-⊤

-- out: satisfaction of the clause implies the Def-step read, at every
-- carrier, with no carrier fact (no transitivity, no rud closure, no LEM).
defStep-out : (f : SM) (x : ⟪ u ⟫)
            → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ defStepForm' ⟩ → DefStep u (fst f)
defStep-out f x _ = ∣ fst f , (⊤̇ , (snd f , DefOf.defSet⊤≡A (fst f))) ∣₁

-- in: the Def-step read implies the clause; the clause is the true
-- formula, so this is the identity.
defStep-in : (f : SM) (x : ⟪ u ⟫)
           → DefStep u (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ defStepForm' ⟩
defStep-in f x _ = tt*

-- The two-way reading, in the face's own _⟷_ shape (c-ok's shape).
defStep-iff : (f : SM) (x : ⟪ u ⟫)
            → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ defStepForm' ⟩ ⟷ DefStep u (fst f)
defStep-iff f x = defStep-out f x , defStep-in f x
