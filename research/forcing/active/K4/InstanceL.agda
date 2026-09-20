{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track K, file 4 of 4. The value-set obligation at the constructible
-- structure: what it would take, what is available, and what is not.
--
-- THE TRAP THIS FILE MAKES HARMLESS, and it travels with the code because it
-- is the package's single most likely silent failure. This file imports
-- L.Constructible and, through the three K3 ledger files, V.Hierarchy and the
-- L chapters. THAT IS CORRECT HERE AND WOULD HAVE BEEN WRONG IN TRACKS A TO
-- J. Smallness and the small presentation of a set are facts about the
-- concrete cumulative hierarchy, not about an arbitrary ground: every set of
-- V comes with a small index type, and nothing in the ZFStructure record says
-- so. A generic track that reached for either would have proved a theorem
-- about one model and stated it about all of them, and the failure would
-- have been invisible because the file would compile. K3 put this paragraph
-- in its own instance files for the same reason (LInstanceCore.agda:6-14),
-- and it is repeated rather than referenced so that a reader of this file
-- alone cannot miss it.
--
-- WHAT THIS FILE SETTLES. Track B measured that Route I, K3's tier-4 datum,
-- is the only route to the TOTAL ValueSets contract, and file 3 measured what
-- the contract costs: ValueSets over a carrier B implies that every ambient
-- truth-valued class cuts a set out of B. Instantiating that at 𝒮ʟ gives the
-- statement in the second block below, and it is exactly the statement K3
-- proved equivalent to tier 4 at L (LInstanceImage.agda, the pair
-- memberImage→classSeparation and classSeparation→memberImage). K3's record
-- states the consequence plainly: it says L absorbs every ambient subclass of
-- each of its sets, which is a form of V = L for the ambient theory, and it
-- is false in any ambient model with a non-constructible subset of a
-- constructible set.
--
-- SO THE OBLIGATION IS REPORTED OPEN, WITH ITS REASON, AND NOT DISCHARGED.
-- The obstruction is not smallness and not a missing lemma. A constructible
-- set still has a small presentation and every value of a selection function
-- on it is constructible; L.Recursion's smallDom even produces a single
-- constructible set containing all the values. What is missing is carving the
-- image out of that bound, carving is Separation, and Separation at L reads a
-- formula, which an arbitrary host function has none of.
--
-- WHAT IS AVAILABLE AT L, AND IT IS NOT NOTHING. Both axioms the graph route
-- consumes are discharged at 𝒮ʟ by K3: separationL (LInstanceSets.agda:57)
-- and replacementL (LInstanceFamilies.agda:97), the latter the Collection
-- form. Track B's graph→admits takes exactly those two plus one formula per
-- pair (a , f) and returns the admitted family. The last block below applies
-- it, so the remaining gap at L is not two axioms and one datum but ONE
-- FORMULA PER STEP: a ValueGraph for the family the atomic recursion builds.
-- That is the same obligation K3 handed forward for check, for the generic
-- name and for both translations, and it is not discharged here either.
--
-- HYPOTHESES. One: LEM (ℓ-suc ℓ), which is the hypothesis L⊨ZFC and L⊨GCH
-- already carry, so this file adds nothing to the T3 budget. The algebra is
-- a module parameter and is not built here: K4 has no Boolean completion
-- inside L until a forcing notion in L is presented, which is K8 and K9 work.
-- Every statement below is therefore conditional on an algebra, which is the
-- honest shape: it says what happens at whatever coded algebra L eventually
-- carries.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
import NameKernel
import K4.Algebra
import K4.ValueSets
import K4.InstanceValueSets

module K4.InstanceL {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

open import LInstanceCore {ℓ} using ( extensionalityL; ≈ˢ-pathsL )
open import LInstanceSets {ℓ} lem using ( separationL )
open import LInstanceFamilies {ℓ} lem using ( replacementL )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )
open hPropStructure 𝒮ʟ

module NKL = NameKernel 𝒮ʟ
module AL  = K4.Algebra 𝒮ʟ
module VSL = K4.ValueSets 𝒮ʟ extensionalityL ≈ˢ-pathsL
module RKL = K4.InstanceValueSets 𝒮ʟ extensionalityL ≈ˢ-pathsL

open AL using ( Pt; Lattice; CodedComplete )

-- ---------------------------------------------------------------------
-- The statement the obligation turns on
-- ---------------------------------------------------------------------

-- Spelled out at 𝒮ʟ so that no reader has to unfold a generic definition to
-- see what is being claimed. A class here is an arbitrary predicate of the
-- ambient theory valued in hProp (ℓ-suc ℓ): no formula, no complexity bound,
-- no definability of any kind. The statement says every such class cuts a
-- CONSTRUCTIBLE set out of the constructible set B, that is, that the ambient
-- power set of B is included in L.

AmbientPowerSetInside : S → Type (ℓ-suc (ℓ-suc ℓ))
AmbientPowerSetInside B =
  (P : S → Ω) → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ ((z ∈ˢ B) ⊓ P z))

module AtL (B : S) (L : Lattice B) (Kc : CodedComplete B L) where

  open VSL.Core B L Kc
    using ( ValueSets; ValueGraph; Admits; member→values; graph→admits )
  open RKL.Reduce B L Kc using ( valueSets→absorbs; valueSets→imageᴮ )

  -- ---------------------------------------------------------------------
  -- The upper bound: tier 4 would discharge it
  -- ---------------------------------------------------------------------

  -- Route I, at L, in one line. This is Track B's member→values fed K3's
  -- tier-4 record, and it is here only to fix the direction: the obligation
  -- below is not harder than tier 4, so reporting it open is a report about
  -- tier 4 and not about some new difficulty introduced by the contract.

  memberImage→valueSets : NKL.MemberImage → ValueSets
  memberImage→valueSets mi =
    member→values (NKL.MemberImage.image mi) (NKL.MemberImage.image-spec mi)

  -- ---------------------------------------------------------------------
  -- The lower bound: it is not easier either
  -- ---------------------------------------------------------------------

  -- File 3's reduction, applied. Read the conclusion as the sentence it is:
  -- if the value-set contract holds at this algebra inside L, then for every
  -- ambient class whatever that holds at some point of B, the members of B
  -- satisfying it form a constructible set. Nothing about the class is
  -- assumed, which is why this is a statement about L and not an instance of
  -- Separation.

  valueSets→ambientPowerSet :
      ValueSets → (x₀ : S) → ⟨ x₀ ∈ˢ B ⟩
    → (P : S → Ω) → ⟨ P x₀ ⟩
    → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s) ≡ ((z ∈ˢ B) ⊓ P z))
  valueSets→ambientPowerSet vs = valueSets→absorbs vs lem

  -- The same thing with the seed quantified away, for a class the ground
  -- already knows is inhabited at a named point. The two statements differ
  -- only in where the point is bound.

  valueSets→inside : ((P : S → Ω) → Σ[ x₀ ∈ S ] (⟨ x₀ ∈ˢ B ⟩ × ⟨ P x₀ ⟩))
                   → ValueSets → AmbientPowerSetInside B
  valueSets→inside pointed vs P =
    valueSets→ambientPowerSet vs (pointed P .fst) (pointed P .snd .fst)
                              P (pointed P .snd .snd)

  -- The restricted tier-4 datum, back out of the contract. Together with
  -- memberImage→valueSets this says the contract and the B-valued half of
  -- tier 4 are inter-derivable at L, so there is no gap between them to look
  -- for a discharge in.

  valueSets→image :
      ValueSets
    → (a : S) (g : Pt a → S) → ((p : Pt a) → ⟨ g p ∈ˢ B ⟩)
    → Σ[ s ∈ S ] ((z : S) → (z ∈ˢ s)
                ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ g (x , h))))
  valueSets→image = valueSets→imageᴮ

  -- ---------------------------------------------------------------------
  -- What L does supply
  -- ---------------------------------------------------------------------

  -- The graph route at L, with both axioms discharged. One formula per pair
  -- and the admitted family follows. This is the positive content of the
  -- file and it is the shape a recursion actually consumes: Track B's
  -- REPORT-B section 3 says so, and K0's own atomic value-set instance did
  -- exactly this, with a fixed two-variable formula and one Separation
  -- (k0-atomic-value-set-2026-09.md).
  --
  -- What is NOT supplied is the ValueGraph argument, and supplying it for the
  -- family the atomic recursion builds is the open work: it asks the atomic
  -- value to carry a formula, which is K4's AtomicGraph contract and K0's
  -- bounded table recursion, and at the coded completion neither exists yet.

  admitsAtL : (a : S) (f : Pt a → Pt B) → ValueGraph a f → Admits {I = Pt a} f
  admitsAtL = graph→admits replacementL separationL
