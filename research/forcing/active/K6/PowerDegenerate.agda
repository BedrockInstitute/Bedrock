{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track G's degenerate-G control, and it is EVIDENCE rather than
-- decoration.
--
-- Track J machine-checked which OrdinaryZF fields survive at the degenerate
-- subset G = λ _ → ⊥. Six of them do, so a degenerate audit says nothing about
-- those six. THREE are refuted there, and hasPower is one of the three. So the
-- degenerate instance is a real discriminator for this track, and the question
-- it answers is sharp: WHICH hypothesis of K6/Power.agda's telescope is the one
-- the degenerate G kills?
--
-- The answer is `pos`, and it is the ONLY hypothesis on G that K6/Power.agda
-- charges. Section 2.4 of the architecture warns against charging isFilter
-- where positivity suffices; this file is the other half of that check, that
-- positivity is not itself an under-charge. The localisation is exact: remove
-- `pos` and the degenerate G satisfies every remaining hypothesis of the
-- telescope vacuously, and hasPower would be false; keep it and the degenerate
-- G is excluded by the one line below.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ ; ∣_∣₁ )
import K6.Power

module K6.PowerDegenerate
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Kernel
  (entry        : S → S → S)
  (entry-inj    : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (Child        : S → S → Type ℓ)
  (child-weight : (x n : S) → Child x n → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  (carrierᶠ     : S)
  (IsNameᴾ      : S → Ω)
  (child-nameᴾ  : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (paths        : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  module K6K = K6.Power.Kernel 𝒮 entry entry-inj Child child-weight
                 carrierᶠ IsNameᴾ child-nameᴾ paths

  -- The degenerate subset, in K6/Power.agda's own G slot.

  degenerate : K6K.Cond → Ω
  degenerate _ = ⊥

  -- The whole of the control. The positivity hypothesis of
  -- K6/Power.agda:298 is uninhabited at the degenerate G, so the Conditional
  -- module cannot be instantiated there and hasPower is not derivable there.
  -- Nothing else in the telescope has to be examined.

  no-positivity : ⟨ ⋁ K6K.Cond (λ q → degenerate q) ⟩ → ⟨ ⊥ ⟩
  no-positivity = PT.rec (snd ⊥) snd
