{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.520] W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: "the bound on the existential, because that single
-- quantifier is what [LJ-1.516] measured no grade admits", and the shape
-- to write is
--
--     -- the existential of GraphAt, with its witness bounded by a term
--
-- This file writes exactly that and nothing else.  If the approximation
-- cannot be bounded by a term the object language can name, this file
-- fails and the task stops at its cheapest point.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-520.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Condensation {ℓ} lem using ( module GraphB; DefBodyB; Δ₀-DefBodyB )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module CS = hPropStructure 𝒮ʟ

module W3 {m : ℕ} (w b K : Fin m)
          (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin m) where

  -- The leaf environments the two step frames put the code-set
  -- description at.  src/L/Condensation.lagda.md:2394-2397 fixes them:
  -- the step's leaf sits at v' ∷ c' ∷ x ∷ d ∷ w ∷ c ∷ z ∷ γ', so an
  -- ambient slot travels five binders at the graph's own step and seven
  -- at the step under the approximation's two bounded universals.
  private
    sh5 : Fin m → Fin (5 + m)
    sh5 i = suc (suc (suc (suc (suc i))))

    sh7 : Fin m → Fin (7 + m)
    sh7 i = suc (suc (suc (suc (suc (suc (suc i))))))

  -- The concrete leaf content: the bounded code-set description, at the
  -- carrier the step frame puts at leaf slot 1 and the bound this task
  -- carries in K.  src/L/Condensation.lagda.md:2338-2343.
  ψs : Formula CS.S (suc (suc (suc (5 + m))))
  ψs = DefBodyB {m} (suc zero) (sh5 K)
         (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
         (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
         (sh5 t0) (sh5 t1)

  ψa : Formula CS.S (suc (suc (suc (7 + m))))
  ψa = DefBodyB {2 + m} (suc zero) (sh7 K)
         (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
         (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
         (sh7 t0) (sh7 t1)

  module G = GraphB {m} ψs ψa w b K

  -- THE TERM W3 ASKS FOR.  src/L/Condensation.lagda.md:2492-2493 reads
  -- graphBndAt = ∃̇∈ (var K) (approxBndAt ∧̇ stepBndAt): the existential
  -- of the graph, with its witness bounded by the term `var K`.
  w3 : Formula CS.S m
  w3 = G.graphBndAt

  -- AND THE GRADE IT CARRIES.  This is the measurement, not the type.
  w3-Δ₀ : Δ₀ w3
  w3-Δ₀ = G.Δ₀-graphBndAt
    (Δ₀-DefBodyB {m} (suc zero) (sh5 K)
       (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
       (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
       (sh5 t0) (sh5 t1))
    (Δ₀-DefBodyB {2 + m} (suc zero) (sh7 K)
       (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
       (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
       (sh7 t0) (sh7 t1))
