{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.531]  DO [LJ-1.529]'s CARVE AND THIS TASK'S LEMMA MEET IN ONE
-- NAMESPACE, AT ONE `lem`, WITHOUT A REBUILD?
--
-- The brief forbids building `injAt` and asks the report to say whether
-- `injAt` is now a composition of DELIVERED terms.  That is a claim
-- about reachability, so it is measured here rather than reasoned.  This
-- file builds NO new term: every binding below is a name for something a
-- predecessor already delivered, given a type ascription so that the
-- elaborator has to agree the name resolves at THIS instantiation.
--
-- `injAt` IS NOT BUILT, and no proof of its hypothesis is written.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-531.runs.Coexist {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import FOL.Absoluteness
open import Cubical.Data.FinData using ( Fin; zero )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-531.Probe531 {ℓ} lem as P531

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- 1.  [LJ-1.529]'s carve, its codomain and its bound.
the-carve : (a : S) → IsOrd (fst a) → S
the-carve = P529.Carve.G

the-codomain : (a : S) → IsOrd (fst a) → S
the-codomain = P529.Carve.C

the-bound : (a : S) → IsOrd (fst a) → S
the-bound = P529.Bound′.bnd

-- 2.  [LJ-1.529]'s reading of a pair out of the carve, and the value
--     equation.  `injAt-in` (src/L/Coding/Injection.lagda.md:72-75)
--     consumes exactly these two at two pairs sharing a second
--     component.
the-read :
    (a : S) (oa : IsOrd (fst a)) (x y : S)
  → ⟨ pr (fst x) (fst y) ∈ fst (P529.Carve.G a oa) ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (pr (fst x) (fst y) ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
the-read = P529.Carve.read

the-val :
    (a : S) (oa : IsOrd (fst a)) (x y : S)
    (h : ⟨ pr (fst x) (fst y) ∈ fst (P529.Carve.G a oa) ⟩)
  → fst y ≡ fst (P521.rank-at′ a oa (P529.Carve.read a oa x y h .fst)
                                    (P529.Carve.read a oa x y h .snd .fst))
the-val = P529.Carve.val

-- 3.  This task's lemma, at the same instantiation.
the-injectivity :
    (a : S) (oa : IsOrd (fst a)) (m m' : S)
    (mx : ⟨ fst m ∈ fst a ⟩) (mx' : ⟨ fst m' ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx) ≡ fst (P521.rank-at′ a oa m' mx')
  → fst m ≡ fst m'
the-injectivity = P531.rank-at′-inj

-- 4.  `injAt-in` AT THE INSTANTIATION THE CONJUNCT NEEDS, NAMED AND NOT
--     DISCHARGED.  `injAt-in` lives in a module over `(f , γ)`
--     (src/L/Coding/Injection.lagda.md:50), and the conjunct is at
--     `f := zero`, `γ := G ∷ a ∷ []` (src/L/Cardinal.lagda.md:227).  The
--     ascription below therefore MEASURES two things that would
--     otherwise be reasoning: that `lookup zero (G ∷ a ∷ [])` is the
--     carve, so the private `Holds₀`
--     (src/L/Coding/Injection.lagda.md:52-53) is `P529.Carve.Hold`
--     (agents/tasks/LJ-1-529/Probe529.agda:230-231); and that the
--     conjunct's satisfaction is what `injAt-in` returns there.
--
--     THE HYPOTHESIS IS STILL AN ARGUMENT AND NOTHING SUPPLIES IT.
--     `injAt` is NOT built here: this is `injAt-in` partially applied,
--     no more, and the brief's one obligation stays the one obligation.
the-injAt-in :
    (a : S) (oa : IsOrd (fst a))
  → ((y x x' : S)
      → ⟨ pr (fst x) (fst y) ∈ fst (P529.Carve.G a oa) ⟩
      → ⟨ pr (fst x') (fst y) ∈ fst (P529.Carve.G a oa) ⟩
      → fst x ≡ fst x')
  → ⟨ (P529.Carve.G a oa ∷ a ∷ []) ⊨ injAt zero ⟩
the-injAt-in a oa = injAt-in zero (P529.Carve.G a oa ∷ a ∷ [])
