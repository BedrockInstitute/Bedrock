{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track J, file 6 of 7. The omega iterator, as a record, and its discharge
-- at L. This is the adapter the architecture reserves for Track C, and the
-- reason it is a RECORD and not an import is the whole point of the file.
--
-- THE QUESTION Track C answers is completeness of the name recognizer: every
-- name lies in some ground code closed under subnames. Track C answers it by
-- Collection, and that answer is the package contract, because Collection is
-- available at any ground meeting tier 3. The answer costs one truncation:
-- Collection produces SETS from truncated premises, so what comes back is
-- ∥ ClosedFamily n ∥₁ and no particular closed family is named.
--
-- K0 answered the same question differently and got more: iterate a one-step
-- closure operator omega times and take the union. That produces a closed
-- family as a TERM, with no truncation, and it produces the LEAST one. The
-- price is that the iteration is a recursion on the natural numbers whose
-- values are sets, which at the ordinary profile needs Infinity and an
-- internal recursion the profile does not have, and which at L is a theorem:
-- L.GCH.OmegaRecursion's Iterate collects the finite iterates of a DEFINABLE
-- step into a single graph indexed by the internal omega, and its range and
-- union are constructible (src/L/GCH/OmegaRecursion.lagda.md:133,442-449).
--
-- So the two routes are not rivals. The Collection route is the contract and
-- holds everywhere; the iteration route is an L-only refinement that upgrades
-- a truncated existence to a named least witness. What this file supplies is
-- the SHAPE of that refinement, so that Track C can consume it as a
-- hypothesis without importing anything from L, and the L discharge of that
-- shape. A consumer parameterized by the record below compiles against an
-- arbitrary ground and is instantiated here.
--
-- WHAT THE RECORD DOES NOT PROMISE. It says nothing about names, entries or
-- weights: it is the bare statement that a definable step can be iterated
-- omega times inside the ground. The definability of the particular one-step
-- closure operator K3 wants is not discharged here and is not Track J's; it
-- is a formula-writing obligation on whoever builds the adapter, and K0's
-- NameClosureStep.agda is the precedent for how the formula is written.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LInstanceOmega where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

import NameImage
import OrdinaryProfile

-- ---------------------------------------------------------------------
-- The interface, over an arbitrary ground
-- ---------------------------------------------------------------------

-- The two hypotheses are the ones Track D's module takes, and they are taken
-- here for one reason only: to have `DefinableGraph` in scope under the name
-- the package already uses for it. Nothing below consumes extensionality or
-- the path realization mathematically. Using Track D's record rather than
-- restating its three fields is deliberate: the step of an iteration and the
-- function of an internalization are the same kind of object, a host function
-- carrying a formula, and a package that spells that twice will eventually
-- spell it differently.

module Interface {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

  open hPropStructure 𝒮
  open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
  open NameImage 𝒮 ext paths using ( DefinableGraph )

  -- The host iteration. It is a plain recursion on the natural numbers in the
  -- metatheory, costs nothing and assumes nothing; the entire content of the
  -- record is that its omega-th union exists INSIDE the ground.

  iterOf : (S → S) → S → ℕ → S
  iterOf step a zero    = a
  iterOf step a (suc n) = step (iterOf step a n)

  -- Type ℓ and not Type (ℓ-suc ℓ): every field is a Π over carriers, formulas
  -- and truth-value carriers, and no field is a path in Ω. Track D's finding
  -- F2 is the reason this is worth checking rather than assuming, since a
  -- record one level too high cannot index a join.

  record OmegaIterator : Type ℓ where
    field
      iterUnion     : (a : S) (step : S → S) → DefinableGraph step → S
      iterUnion-in  : (a : S) (step : S → S) (g : DefinableGraph step)
                    → (n : ℕ) (z : S)
                    → ⟨ z ∈ˢ iterOf step a n ⟩ → ⟨ z ∈ˢ iterUnion a step g ⟩
      iterUnion-out : (a : S) (step : S → S) (g : DefinableGraph step)
                    → (z : S) → ⟨ z ∈ˢ iterUnion a step g ⟩
                    → ∥ Σ[ n ∈ ℕ ] ⟨ z ∈ˢ iterOf step a n ⟩ ∥₁

    -- The two derived facts a closure argument actually calls. The seed is in
    -- the union because it is the zeroth iterate; and a point produced by one
    -- application of the step to any iterate is in the union, because that is
    -- the next iterate. The second is the closure clause: given a member of
    -- the union, find its stage by iterUnion-out, apply the step there, and
    -- land back in the union.

    seed-in : (a : S) (step : S → S) (g : DefinableGraph step)
            → (z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ iterUnion a step g ⟩
    seed-in a step g = iterUnion-in a step g zero

    after-step : (a : S) (step : S → S) (g : DefinableGraph step)
               → (n : ℕ) (z : S)
               → ⟨ z ∈ˢ step (iterOf step a n) ⟩ → ⟨ z ∈ˢ iterUnion a step g ⟩
    after-step a step g n = iterUnion-in a step g (suc n)

-- ---------------------------------------------------------------------
-- The discharge at L
-- ---------------------------------------------------------------------

-- Three projections and no proof. That is the correct outcome: the theorem is
-- L.GCH.OmegaRecursion's and this file only fixes the shape it is handed on
-- in. The iterator takes the successor-level excluded middle, through
-- L.Recursion and L.Stage, and it does NOT assume the generalized continuum
-- hypothesis despite living in the GCH chapter, which is measured at
-- k0-internal-names-probes-2026-09.md:71 and is worth repeating because the
-- module path invites the opposite assumption.

module AtL {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import L.Constructible {ℓ} using ( 𝒮ʟ )
  open import L.GCH.OmegaRecursion {ℓ} lem using ( module Iterate )
  open import LInstanceCore {ℓ} using ( extensionalityL; ≈ˢ-pathsL )

  open Interface 𝒮ʟ extensionalityL ≈ˢ-pathsL public
  open hPropStructure 𝒮ʟ
  open NameImage 𝒮ʟ extensionalityL ≈ˢ-pathsL using ( DefinableGraph )

  -- ONE MEASURED FRICTION, and it is worth a sentence because every adapter
  -- of a parameterized module hits it. `Iterate` defines its own host
  -- iteration `it` by the same two clauses as `iterOf`, but inside a module
  -- with five parameters, so at a variable index the two are stuck terms with
  -- different heads and are NOT definitionally equal. They are of course
  -- propositionally equal, by an induction with `refl` at zero and one `cong`
  -- at the successor, and the three fields below transport along it. Stating
  -- the interface in terms of the consumer's own iteration rather than the
  -- supplier's is the right trade: the record stays a statement about an
  -- arbitrary ground, and the two lines of transport are paid once, here.

  itL : (a : S) (step : S → S) (g : DefinableGraph step) → ℕ → S
  itL a step g = Iterate.it a (DefinableGraph.graph g) step
                   (DefinableGraph.defines g) (DefinableGraph.only g)

  agree : (a : S) (step : S → S) (g : DefinableGraph step) (n : ℕ)
        → iterOf step a n ≡ itL a step g n
  agree a step g zero    = refl
  agree a step g (suc n) = cong step (agree a step g n)

  opaque
    omegaIteratorL : OmegaIterator
    omegaIteratorL = record
      { iterUnion     = λ a step g →
          Iterate.iterUnion a (DefinableGraph.graph g) step
            (DefinableGraph.defines g) (DefinableGraph.only g)
      ; iterUnion-in  = λ a step g n z h →
          Iterate.iterUnion-in a (DefinableGraph.graph g) step
            (DefinableGraph.defines g) (DefinableGraph.only g) n z
            (subst (λ w → ⟨ z ∈ˢ w ⟩) (agree a step g n) h)
      ; iterUnion-out = λ a step g z h → PT.map
          (λ { (n , hn) → n
             , subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (agree a step g n)) hn })
          (Iterate.iterUnion-out a (DefinableGraph.graph g) step
            (DefinableGraph.defines g) (DefinableGraph.only g) z h) }
