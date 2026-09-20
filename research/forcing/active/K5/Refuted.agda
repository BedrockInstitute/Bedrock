{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track J: the five refutations, collected.
--
-- Each of the five is a statement a competent reader of the K5 architecture
-- would write, transcribed under its own name and shown false. None is
-- repaired; rule 14.
--
--  1. NaiveDisjunction. "A condition forcing a join forces one of the two
--     joinands." Believed because the Boolean value of a disjunction IS the
--     join and joins in a powerset algebra are unions. False at the three
--     element V, where the join of the two atoms' images regularizes back to
--     the top. K5/RefutedClauses.agda.
--
--  2. NaiveExistential. "A condition forcing an infinitary join forces one
--     member of the family." Believed for the same reason, and because the
--     value of an existential IS the join over the names. False at the same
--     notion. K5/RefutedClauses.agda.
--
--  3. OrderReflection. "Forcing the image of p is refining p." Believed
--     because it is true of the bare cone, and the completion map looks like
--     the cone. False on a non-refined presentation, where the map is the
--     double pseudocomplement of the cone. K5/RefutedOrder.agda.
--
--  4. SameName. "The forward translation of the poset generic name is the
--     Boolean generic name." Believed because both are diagonals and the
--     translation carries the diagonal to the diagonal. False because U̇ has
--     one entry per algebra element, including the bottom, while every entry
--     of trᴮ Γᴾ has a weight in the image of the embedding, and no image is
--     the bottom. K5/RefutedOrder.agda.
--
--  5. HostGenericExists. "A generic filter exists." Believed because
--     Rasiowa-Sikorski produces one for any countable family of dense sets,
--     and because the textbook statement is relativized to a countable
--     transitive model. False under LEM at any atomless notion, and this
--     package supplies the atomless notion the programme did not have.
--     K5/RefutedGenericity.agda.
--
-- TWO CONTROLS, both positive, both load bearing:
--
--  A. The two element antichain refutes NEITHER naive clause, so a designer's
--     proposed negative control is not one. K5/AntichainControl.agda.
--
--  B. K2's trivial instance carries a host-generic filter, so no statement in
--     this track says that no filter is host generic, or that an extension
--     properly extends its ground. K5/RefutedGenericity.agda section 3.
--
-- AND TWO POSITIVE CONTROLS ON THE CLAUSE LAYER: the dense-below forms of the
-- disjunction and existential clauses, the ones K5 actually states, hold at
-- the very condition that refutes the naive forms.

open import Base.Prelude
open import Base.Truth

module K5.Refuted {ℓ : Level} where

open import Base.Classical using ( LEM )

import K5.RefutedClauses
import K5.AntichainControl
import K5.RefutedOrder
import K5.RefutedGenericity

open TruthAlgebra (hPropAlgebra ℓ)

module CL = K5.RefutedClauses {ℓ}
module AC = K5.AntichainControl {ℓ}
module OR = K5.RefutedOrder {ℓ}
module GN = K5.RefutedGenericity {ℓ}

--------------------------------------------------------------------------------
-- The five refutations
--------------------------------------------------------------------------------

refuted :
    (CL.NaiveDisjunction → ⟨ ⊥ ⟩)
  × ((CL.NaiveExistential → ⟨ ⊥ ⟩)
  × ((OR.OrderReflection → ⟨ ⊥ ⟩)
  × ((OR.Witnessed.SameName → ⟨ ⊥ ⟩)
  × (LEM ℓ → GN.HostGenericExists → ⟨ ⊥ ⟩))))
refuted =
    CL.naive-disjunction-fails
  , CL.naive-existential-fails
  , OR.order-reflection-fails
  , OR.generic-name-identification-fails
  , GN.host-generic-existence-fails

-- The same five in their alternative spellings, so that no reader escapes a
-- refutation by rewriting the statement with the Boolean order instead of
-- with entailment, or by asking for the converse of monotonicity instead of
-- for order reflection.

refuted-alternative-spellings :
    (CL.NaiveDisjunction≤ → ⟨ ⊥ ⟩)
  × ((OR.OrderReflection≤ → ⟨ ⊥ ⟩)
  × ((OR.MonoConverse → ⟨ ⊥ ⟩)
  × ((OR.OntoImage → ⟨ ⊥ ⟩)
  × (LEM ℓ → (Gᵗ : GN.TREE.Sub) → GN.TREE.isFilter Gᵗ
           → GN.TREE.hostGeneric Gᵗ → ⟨ ⊥ ⟩))))
refuted-alternative-spellings =
    CL.naive-disjunction≤-fails
  , OR.order-reflection≤-fails
  , OR.mono-converse-fails
  , OR.i-not-onto
  , GN.no-generic-on-the-tree

--------------------------------------------------------------------------------
-- The controls
--------------------------------------------------------------------------------

-- A. The antichain refutes nothing, and B. the trivial notion has a
-- host-generic filter which is the whole one-point poset.

controls :
    (LEM ℓ → AC.NaiveDisjunctionA2 × AC.NaiveExistentialA2)
  × (Σ[ Gᵗ ∈ GN.TR.Sub ] (GN.TR.isFilter Gᵗ × GN.TR.hostGeneric Gᵗ))
controls = AC.antichain-refutes-nothing , GN.trivial-host-generic

-- The correctly qualified clauses hold where the naive ones fail, and the
-- reflection holds where separativity is available. The refutations are of
-- missing hypotheses, never of the clause layer K5 states.

boundaries :
    (⟨ CL.DenseBelow CL.vtop (λ r → (CL._⊩ᴴ_ r (CL.R.i CL.va))
                                  ⊔ (CL._⊩ᴴ_ r (CL.R.i CL.vb))) ⟩
  × ⟨ CL.DenseBelow CL.vtop (λ r → ⋁ CL.V3 (λ a → CL._⊩ᴴ_ r (CL.fam a))) ⟩)
  × ((OR.NR.antisymmetric × (OR.NR.separative → ⟨ ⊥ ⟩))
  × (GN.TR.atomless → ⟨ ⊥ ⟩))
boundaries =
    (CL.disjunction-dense-below , CL.existential-dense-below)
  , ((OR.NR.antisym , OR.NR.not-separative) , GN.trivial-not-atomless)

-- Separativity does not repair the two clause refutations. The refuting
-- notion is a separative partial order, which is the strongest hypothesis
-- available at this layer and the one that buys back order reflection and
-- injectivity of the embedding; the naive clauses fail there regardless.

no-repair-by-separativity :
    (CL.R.separative × CL.R.antisymmetric)
  × ((CL.NaiveDisjunction → ⟨ ⊥ ⟩) × (CL.NaiveExistential → ⟨ ⊥ ⟩))
no-repair-by-separativity =
    (CL.V3-separative , CL.V3-antisymmetric)
  , (CL.naive-disjunction-fails , CL.naive-existential-fails)
