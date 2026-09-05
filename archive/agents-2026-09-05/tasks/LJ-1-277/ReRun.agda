{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.277] re-run against the landed master src/L/Coding/Injection.lagda.md.
-- Every public export is imported and used in a consumer-shaped term, then
-- the whole checks green: injAt, injAt-out, injAt-in, Extract, Small.
-- This is C-45's proof that the landing is a supply, not a copy.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-277.ReRun {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-out; injAt-in; module Extract; module Small )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The consumer's assembly, at the Small API: the range is supplied, not
-- produced.  This is exactly the surface A6 names, and A5 row 1 too.
module Assembled (F D C : S)
                 (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
                 (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
                 (ij : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
                 (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                      → ⟨ fst y ∈ fst C ⟩) where

  module E = Extract F D sv dm
  module Sm = Small F D C sv dm ij ran

  injection : ⟪ fst D ⟫ → ⟪ fst C ⟫
  injection = Sm.small

  injection-inj : (m n : ⟪ fst D ⟫) → injection m ≡ injection n → m ≡ n
  injection-inj = Sm.small-inj

  -- The readback's first half is importable on its own.
  readback : E.Dom → S
  readback = E.toFun

  -- injAt-out at the consumer site: reading injectivity back through the
  -- graph, exactly as Extract.toFun-inj does internally.
  toFun-inj′ : (u v : E.Dom) → fst (E.toFun u) ≡ fst (E.toFun v)
             → fst (fst u) ≡ fst (fst v)
  toFun-inj′ u v e = injAt-out zero (F ∷ D ∷ []) ij (E.toFun v) (fst u) (fst v)
    (subst (λ w → ⟨ pr (fst (fst u)) w ∈ fst F ⟩) e (E.toFun-graph u))
    (E.toFun-graph v)

  -- injAt-in at the consumer site: building the injAt hypothesis from the
  -- S-level injectivity of the graph, exactly as A6 does.
  ij-from : ((y x x' : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
           → ⟨ pr (fst x') (fst y) ∈ fst F ⟩ → fst x ≡ fst x')
          → ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩
  ij-from h = injAt-in zero (F ∷ D ∷ []) h
