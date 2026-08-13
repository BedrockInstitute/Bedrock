{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.38] THE CURE, MEASURED.
--
-- ProbeDD25E1 shows the delivered story rows are wrong.  The return
-- prices the repair as a re-lay of five frames, twelve bodies, the
-- certificates and the frame decodes.  This probe asks a cheaper
-- question: what does the bounded frame have to look like, and does it
-- then reach the machine's frame?
--
-- The answer is one lemma.  The bounded extension frame `extAtB`,
-- which block 2 already builds and already uses in nine of the twelve
-- rows, reaches the machine's `extAt` under two hypotheses: the leaves
-- agree, and every satisfier lies in the bound K.  The second is a
-- site fact, not new work: the leaf condition says the candidate lies
-- in E, and E lies in K, and K is transitive.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25E2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( extAt; extAt-in-both )
open import L.Condensation {ℓ} lem using ( extAtB )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE FRAME TRANSFER.  The story's bounded extension frame reaches the
-- machine's extension frame.  Nothing here is new machinery: `extAtB`
-- is delivered at src/L/Condensation.lagda.md:394-396 and `extAt` at
-- src/L/Coding/Model.lagda.md:662-664.
--
-- The third hypothesis is the whole content of the second direction's
-- bound.  It is the site fact, and the row's own leaf supplies it.
-- =====================================================================

extAtB→extAt : ∀ {n} (y K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  → ⟨ γ ⊨ extAtB y K φB ⟩ → ⟨ γ ⊨ extAt y φ ⟩
extAtB→extAt y K φB φ γ fwd bwd inK h =
  extAt-in-both y φ γ
    (λ z z∈ → fwd z (h .fst z z∈))
    (λ z hz → h .snd z (inK z hz) (bwd z hz))

-- The converse direction, which needs no site fact at all.
extAt→extAtB : ∀ {n} (y K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩)
  → ⟨ γ ⊨ extAt y φ ⟩ → ⟨ γ ⊨ extAtB y K φB ⟩
extAt→extAtB y K φB φ γ fwd bwd h =
    (λ z z∈ → bwd z (h .fst z z∈))
  , (λ z _ hz → h .snd z (fwd z hz))
