{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.525] W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: "the match between the two `φ`, because both
-- terms are delivered and the only question is whether they meet", and
-- the shape to write is
--
--     -- extAtB→extAt's `inK` argument, at the leaf's own φ
--
-- `extAtB→extAt` (src/L/Condensation.lagda.md:2514-2521) asks for
--
--     (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩
--
-- at the UNBOUNDED leaf φ.  [LJ-1.522]'s `defPow-closed-noCode`
-- (agents/tasks/LJ-1-522/Probe522.agda:356-364) concludes exactly that
-- membership from `⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩`.  This file writes
-- the term that joins them and nothing else.  If they do not meet at
-- this frame, the task stops at its cheapest point.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-525.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Coding.Powerset {ℓ} lem using ( DefBody )

open import LJ-1-522.Probe522 {ℓ} lem using ( IsLimit; defPow-closed-noCode )

open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The two formulas, at ONE frame.  `γ : S ^ n` is the leaf's base
-- environment, `w` its carrier slot and `K` its bound slot.
--
--   leafFo   the UNBOUNDED leaf: `DefAt`'s own body, two existentials
--            over `DefBody w` (src/L/Coding/Powerset.lagda.md:443).
--   leafBFo  the BOUNDED leaf's inner formula, the shape `leafB` puts
--            under `extAtB` (src/L/Condensation.lagda.md:2399-2402):
--            the same two existentials, each bounded by `K`.
leafFo : ∀ {n} → Fin n → Formula S (suc n)
leafFo w = ∃̇ (∃̇ (DefBody w))

leafBFo : ∀ {n} → Fin n → Formula S (suc (suc (suc n))) → Formula S (suc n)
leafBFo K ψB = ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) ψB)

-- THE MATCH.  `extAtB→extAt`'s third argument, built from [LJ-1.522].
-- The bounded direction `bwd` is the conversion's OWN second argument,
-- and it is what supplies the recorded value's membership in K that the
-- unbounded leaf does not carry.
leaf-inK :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (w K : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩ → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
  → ⟨ fst x ∈ fst (lookup K γ) ⟩
leaf-inK α lim w K ψB γ qK W∈K leafFwd bwd x hx =
  PT.rec (snd (fst x ∈ fst (lookup K γ)))
    (λ { (c , (cK , hc)) → PT.rec (snd (fst x ∈ fst (lookup K γ)))
      (λ { (v , (vK , hv)) →
        defPow-closed-noCode α lim w K γ qK W∈K x c v vK
          (leafFwd x c v hv) })
      hc })
    (bwd x hx)
