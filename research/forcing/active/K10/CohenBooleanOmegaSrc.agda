{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import CardinalBridge

module K10.CohenBooleanOmegaSrc {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.Syntax using ( Formula ; var ; ∃̇∈ ; ∀̇∈ ; _∈̇_ ; _∧̇_ ; _⇒̇_ ; ∀̇_ ; ⊥̇ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences (ZFStructure.S 𝒮)

Src : ℕ → Type ℓ
Src n = Formula (⊥* {ℓ}) n

succSrc : Src 2
succSrc = ZO.erase CB.IsSuccOfφ refl

emptyClause : Src 1
emptyClause = ∃̇∈ (var zero) (∀̇∈ (var zero) ⊥̇)

succInner : Src 3
succInner = renameFo CB.wk2 succSrc

succExists : Src 2
succExists = ∃̇∈ (var (suc zero)) succInner

succClause : Src 1
succClause = ∀̇∈ (var zero) succExists

indSrc : Src 1
indSrc = emptyClause ∧̇ succClause

members : Src 2
members = ∀̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero))

leastSrc : Src 1
leastSrc = ∀̇ ((renameFo CB.wk1 indSrc) ⇒̇ members)

omegaSrc : Src 1
omegaSrc = indSrc ∧̇ leastSrc

succSrc-erase : succSrc ≡ ZO.erase CB.IsSuccOfφ refl
succSrc-erase = refl

indSrc-erase : indSrc ≡ ZO.erase CB.IsInductiveφ refl
indSrc-erase = refl

omegaSrc-erase : omegaSrc ≡ ZO.erase CB.IsOmegaφ refl
omegaSrc-erase = refl

om-w : Fin 1 → Fin 2
om-w zero = suc zero

omega-part : Src 2
omega-part = renameFo om-w omegaSrc

erase-om-w : ZO.erase (renameFo om-w CB.IsOmegaφ) refl ≡ omega-part
erase-om-w = refl
