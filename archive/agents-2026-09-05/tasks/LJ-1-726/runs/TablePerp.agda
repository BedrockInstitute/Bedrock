{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.726] TablePerp.  The kill lemma of the 726 refutation, split
-- out of Probe726 so its check runs on its own heap budget (the main
-- probe's check was killed at the 2 g cap while elaborating the two
-- together).  Everything here is delivered lemmas; nothing is new
-- mathematics.
--
--   #inLomega  every numeral sits in Lset omega, by ord-in-Lset-suc
--              (src/L/Ordinal/Stages.lagda.md:434) and Lset-mono.
--   table-perp a table c in Lset omega answering every numeral is
--              impossible: rank-Lset (src/L/Ordinal/Stages.lagda.md:190)
--              puts rank c in omega, so rank c is a numeral # j (the
--              decode behind ω-mem-ord, src/L/Ordinal.lagda.md:258),
--              and the entry at # j drags # j inside rank c = # j
--              through rank-mono (src/L/Rank.lagda.md:117), the pair
--              components, and rank-fix (src/L/Rank.lagda.md:191).

open import Base.Prelude
open import Base.Truth

open import Base.Classical using ( LEM )

module LJ-1-726.runs.TablePerp {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ}
  using ( ω-ord; ∅-ord; suc-ord; numeral-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( rank-Lset; ord∈Lset-suc )
open import L.Rank {ℓ} using ( rank; rank-mono; rank-fix; rank-ord )
open import V.Coding {ℓ} using ( pr )

open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Sum using ( inl )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; pairing-ax; SingletonPackage; SetPackage
        ; module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_; ω )
open import Base.Prelude using () renaming () -- no-op anchor
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ )
open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The two Kuratowski facts the rank chain needs, from the library's
-- own packages (the tree's spellings of them are private in V.Coding).
self∈singlₛ : (a : V ℓ) → ⟨ a ∈ₛ ⁅ a ⁆s ⟩
self∈singlₛ a = SetPackage.classification (SingletonPackage a) a .snd refl

self∈singl : (a : V ℓ) → ⟨ a ∈ˢ ⁅ a ⁆s ⟩
self∈singl a = ∈∈ₛ {a = a} {b = ⁅ a ⁆s} .snd (self∈singlₛ a)

inl∈pairₛ : (a b : V ℓ) → ⟨ ⁅ a ⁆s ∈ₛ pr a b ⟩
inl∈pairₛ a b = pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s .snd ∣ inl refl ∣₁

inl∈pair : (a b : V ℓ) → ⟨ ⁅ a ⁆s ∈ˢ pr a b ⟩
inl∈pair a b = ∈∈ₛ {a = ⁅ a ⁆s} {b = pr a b} .snd (inl∈pairₛ a b)

#∈Lω : (k : ℕ) → ⟨ (# k) ∈ˢ Lset ω ⟩
#∈Lω zero = Lset-mono (#∈ω 1) (ord∈Lset-suc ∅ ∅-ord)
#∈Lω (suc k) = Lset-mono (#∈ω (suc (suc k)))
  (ord∈Lset-suc (sucV (# k)) (suc-ord (numeral-ord k)))

table-⊥ :
  (c : V ℓ) (c∈Lω : ⟨ c ∈ˢ Lset ω ⟩)
  (entry : (x : V ℓ) → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ x ∈ˢ ω ⟩
          → ∥ Σ[ y ∈ V ℓ ] ( ⟨ y ∈ˢ Lset ω ⟩ × ⟨ pr x y ∈ˢ c ⟩ ) ∥₁)
  → Empty.⊥
table-⊥ c c∈Lω entry =
  PT.rec Empty.isProp⊥
    (λ { (j , j≡rc) →
      PT.rec Empty.isProp⊥
        (λ { (y , (_ , pj∈c)) →
          let l = lower j
              m₁ : ⟨ rank (# l) ∈ˢ rank (⁅ # l ⁆s) ⟩
              m₁ = rank-mono (# l) (⁅ # l ⁆s) (self∈singl (# l))
              m₂ : ⟨ rank (⁅ # l ⁆s) ∈ˢ rank (pr (# l) y) ⟩
              m₂ = rank-mono (⁅ # l ⁆s) (pr (# l) y) (inl∈pair (# l) y)
              tr : ⟨ rank (# l) ∈ˢ rank (pr (# l) y) ⟩
              tr = (rank-ord (pr (# l) y)) .fst m₁ m₂
              step₁ = subst (λ w → ⟨ w ∈ˢ rank (pr (# l) y) ⟩)
                            (rank-fix (# l) (numeral-ord l)) tr
              step₂ = rank-mono (pr (# l) y) c pj∈c
              step₃ = (rank-ord c) .fst step₁ step₂
              step₄ = subst (λ w → ⟨ (# l) ∈ˢ w ⟩) (sym j≡rc) step₃
          in  Empty.rec (∈-irrefl (# l) step₄) })
        (entry (# (lower j)) (#∈Lω (lower j)) (#∈ω (lower j))) })
    (rank-Lset ω ω-ord c c∈Lω)
