{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K10.NegatedSentences {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.Syntax using ( Formula; ¬̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.ZFStructure using ( module hPropStructure )
import CHSentence
import CardinalBridge
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module CH = CHSentence 𝒮
module CB = CardinalBridge 𝒮

¬GCHωsent : Formula S 0
¬GCHωsent = ¬̇ CH.GCHωsent

¬GCHω-agrees : ([] ⊨ ¬GCHωsent) ≡ (¬ CH.gchωValue)
¬GCHω-agrees = cong (_⇒ ⊥) CH.GCHω-agrees
  ∙ sym (CB.¬-as-⇒⊥ CH.gchωValue)

¬GCHω-satisfaction : (⟨ CH.gchωValue ⟩ → Empty.⊥)
  → ⟨ [] ⊨ ¬GCHωsent ⟩
¬GCHω-satisfaction refute = subst ⟨_⟩ (sym ¬GCHω-agrees) refute
