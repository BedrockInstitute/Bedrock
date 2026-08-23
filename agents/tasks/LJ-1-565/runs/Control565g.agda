{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL g.  THE CONTROLLED PAIR, AND THE ONE VARIABLE.
--
-- Control565c and Control565f both wall on `refl` between
-- [LJ-1.536]'s `HierBelow` at a successor and the same set spelled the
-- other way.  Control565e compares `hierL (sucV α) h o` with itself in
-- 1.44 s.  The ONE thing (e) holds abstract and (c)/(f) make concrete
-- is the `isL` WITNESS: (c) and (f) carry
--
--     isL-ord (sucV α) (suc-ord oα)
--       = Lset→isL (sucV (sucV α)) … (ord∈Lset-suc (sucV α) …)
--
-- and `ord∈Lset-suc` is `∈-induction` (src/L/Ordinal/Stages.lagda.md
-- :434-435) applied to a TRANSPARENT `sucV α`.
--
-- THIS FILE IS (c) WITH THAT ONE VARIABLE CHANGED BACK.  `HierBelowH`
-- is [LJ-1.536]'s `HierBelow` with the witness taken as a PARAMETER
-- instead of computed by `isL-ord`.  Nothing else differs.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565g {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; hier-unique )
open import LJ-1-536.Probe536 {ℓ} lem using ( step )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- [LJ-1.536]'s `HierBelow`, with the `isL` witness a PARAMETER.
HierBelowH : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ → Type (ℓ-suc ℓ)
HierBelowH γ hγ oγ = ⟨ fst (hierL γ hγ oγ) ∈ Lset (step 3 γ) ⟩

-- (c)'s ROW, WITH THE WITNESS ABSTRACT.
same-H : (α : V ℓ) (h : ⟨ isL (sucV α) ⟩) (o : IsOrd (sucV α))
       → HierBelowH (sucV α) h o
         ≡ ⟨ fst (hierL (sucV α) h o) ∈ Lset (step 3 (sucV α)) ⟩
same-H α h o = refl

-- AND THE WITNESS DOES NOT MATTER TO THE VALUE, so a statement that
-- holds it abstract loses nothing.  `hierL` is unique against its own
-- specification (src/L/Hierarchy.lagda.md:507-508), so two witnesses
-- give ONE set, and the move across is a `subst` and not a conversion.
hierL-irr : (β : V ℓ) (h₁ h₂ : ⟨ isL β ⟩) (o₁ o₂ : IsOrd β)
          → hierL β h₁ o₁ ≡ hierL β h₂ o₂
hierL-irr β h₁ h₂ o₁ o₂ =
  hier-unique β (hierL β h₁ o₁) (hierL β h₂ o₂)
    (hierL-spec β h₁ o₁) (hierL-spec β h₂ o₂)
