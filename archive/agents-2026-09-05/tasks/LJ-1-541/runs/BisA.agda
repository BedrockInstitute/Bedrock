{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-541.runs.BisA {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; con; _≐_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.WellOrder.Base {ℓ} using ( SWO )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; domAt; domAt-intro )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))


-- =====================================================================
-- 1.  D-10, MECHANISED.  The brief orders every piece `[LJ-1.537]` names
--     checked at its `file:line` BEFORE any Agda, and `[LJ-1.537]` states
--     the composition "as a reading of the types and not as a
--     measurement".  Each name below is a TYPE ASCRIPTION over a
--     delivered term, transcribed from the predecessor's own report.  A
--     drift between a report and the tree is then a type error in THIS
--     file, and not a sentence anybody has to believe.
--
--     None of the five is re-proved.  Every right-hand side is one name.
-- =====================================================================

-- (i)  the pair splits.  src/L/Coding/Model.lagda.md:329-330.
piece-pr : (x y : S) → fst (prʟ x y) ≡ pr (fst x) (fst y)
piece-pr = prʟ-fst

-- (ii)  the `Q` witness, INSTANTIATED and not hypothesised.
--       agents/tasks/LJ-1-521/Probe521.agda:1162-1164.
piece-Q : (a : S) (oa : IsOrd (fst a))
        → Σ[ Q ∈ S ] P521.ord-reads-Q Q a oa
piece-Q = P521.ord-set-witness

-- (iii)  the rank's one exported equation.
--        agents/tasks/LJ-1-521/Probe521.agda:438-442.
piece-val :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx)
    ≡ P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa) (fiber (fst a) mx .fst)
piece-val = P521.rank-at′-val

-- (iv)  the bound half.  agents/tasks/LJ-1-529/Probe529.agda:133-140.
piece-bound :
    (a : S) (oa : IsOrd (fst a))
  → Σ[ bnd ∈ S ]
      ((m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa)
                                       (fiber (fst a) mx .fst))
            ∈ fst bnd ⟩)
piece-bound = P529.rank-bound′

-- (v)  the satisfaction half's fourth existential.
--      agents/tasks/LJ-1-537/Probe537.agda:616-620.
piece-approx :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → Σ[ f ∈ S ] P537.Approximates a oa m mx f
piece-approx = P537.approx-carve

-- AND THE ONE THE BRIEF CALLS ALREADY DELIVERED.  `[LJ-1.524]`'s reading
-- (lj-1.524-report.md:277), carried by `[LJ-1.529]` to the RE-BASED
-- bound (Probe529.agda:236-243).  It is the whole of `domAt`'s first
-- direction and section 5.1 spends it.
piece-read :
    (a : S) (oa : IsOrd (fst a)) (x y : S)
  → ⟨ pr (fst x) (fst y) ∈ fst (P529.Carve.G a oa) ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (pr (fst x) (fst y) ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
piece-read = P529.Carve.read

-- =====================================================================
-- 2.  THE CONJUNCT'S TYPE, read out of `InjCode` so that nothing can
--     drift (src/L/Cardinal.lagda.md:223-228).  `domAt zero (suc zero)`
--     at `(F ∷ a ∷ [])` reads slot 0 as the graph and slot 1 as the
--     domain, and the projection below typechecks only if `DomAtOf` is
--     definitionally the SECOND component there.
-- =====================================================================

DomAtOf : S → S → Type (ℓ-suc ℓ)
DomAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩

domAt-is-second-of-InjCode : (F a b : S) → InjCode F a b → DomAtOf F a
domAt-is-second-of-InjCode F a b h = h .snd .fst

