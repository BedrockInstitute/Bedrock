{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.532] PROBE.  Row six's one membership: the approximation
-- function itself in `K`.  It runs in agents/tasks/LJ-1-532/ and lands
-- nothing in src/.
--
--   W3, FIRST      runs/W3.agda, typechecked before this file existed.
--                  It measured that `ApproxAt` is BLIND to a member of
--                  the approximation that is not a Kuratowski pair.
--   NOT DELIVERED  `approx-in-K`, the briefed obligation, IS NOT
--                  INHABITED HERE AND CANNOT BE: section 2 refutes it.
--                  The brief's own stop condition is met and this file
--                  is the evidence.  review-of-approx-in-K.md states it.
--   DELIVERED      the refutation, and the two facts that say what to
--                  put in its place: every approximation on an ordinal
--                  carries EXACTLY the pairs `hierL` carries
--                  (section 3), so the ∀-form fails only on junk and
--                  the corrected statement quantifies over the
--                  CANONICAL witness (section 4).
--
-- THE FINDING IN ONE SENTENCE.  `LsetGraphAt`'s existential is over the
-- whole class carrier and `ApproxAt` constrains only the pair members
-- of its witness, so an arbitrary witness may carry a member of any
-- level whatever; and once the witness is canonicalised, what is left
-- to prove is `hierL β ∈ Lset α`, which is [LJ-1.494]'s and
-- [LJ-1.230]'s recorded gap and not a new one.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-532.runs.Control532 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( ω-ord; ∅-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( ord∈Lset→∈; ord∈Lset-suc; Lset-cumul )
open import L.Axioms.Basic {ℓ} using ( ∅∈L; LsetS )
open import L.Axioms.Infinity {ℓ} lem using ( ω∈L )
open import L.Coding.InL {ℓ} using ( sgl-in; sglʟ; sglʟ-fst; sglʟ-out )
open import L.Coding.Model {ℓ} using ( domAt; domAt-intro )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; ApproxAt; ApproxAt-in; ApproxAt-dom; ApproxAt-value
        ; LsetGraphAt )
open import L.Hierarchy {ℓ} lem
  using ( Values; Entries; Domain; IsHier; hierL; hierL-spec
        ; hier-in; hier-out; approx-val; step-table )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Vec using ( lookup; _∷_; [] )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; ω; ω-empty; ω-next )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ ) using ( _^_ )

-- THE IMPORT LIST AND NOTHING ELSE.  The control for the price table.

