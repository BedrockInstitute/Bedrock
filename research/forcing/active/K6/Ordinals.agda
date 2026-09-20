{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track H, deliverable 2. `no-new-ordinals`, attempted once under ruling
-- D7 and TIME BOXED. This file is the stop report.
--
-- ---------------------------------------------------------------------
-- WHAT IS PROVED HERE AND WHAT IS NOT
-- ---------------------------------------------------------------------
--
-- PROVED. The ordinal vocabulary transports, and its reading at the extension
-- structure is refl. That is trap T-H3 discharged: K1's IsOrdinalφ
-- (CardinalBridge.agda:522-529) is polymorphic over any
-- ZFStructure (hPropAlgebra ℓ), so K6 instantiates it at the extension and
-- never re-spells it. Re-spelling at uniform depth re-opens K1's measured
-- linearity bug, the inner bounded quantifier ranging over the outer bound
-- variable, which collapses the predicate to transitivity alone; the break
-- file K6/breaks/OrdRespell.agda-break holds that exact shift and it is caught
-- only by the reading theorem.
--
-- PROVED. The REFLECTION half: if a name is value equal to the check name of a
-- ground set and is an ordinal in the extension, that ground set is a ground
-- ordinal. This is the half that costs nothing: IsOrdinalφ is Δ₀, so K5's
-- groundSat (K5/Structures.agda:670-671) carries it across the check map at
-- ⟨ positive G ⟩, and sat-cong moves it along the value relation.
--
-- NOT PROVED, AND THIS IS THE DELIVERABLE. `NoNewOrdinals` below is shipped as
-- a TYPE WITH NO INHABITANT, on K3's non-claim model (Valuation.agda:693-715)
-- and K5's (K5/Structures.agda:455-461). The exact open goal is stated at
-- OpenGoal, and the prerequisite is named at OrdinalRankBound.
--
-- ---------------------------------------------------------------------
-- THE EXACT OPEN GOAL, and why the rank free route does not reach it
-- ---------------------------------------------------------------------
--
-- After the reflection half the remaining obligation is RESTRICTED ONTONESS:
--
--     (σ : Nm) → ⟨ (σ ∷ []) ⊨ IsOrdinalφ ⟩
--              → ⟨ ⋁ S (λ a → isOrdinalᴳ a ⊓ (fst σ ≈[G] fst (chk a))) ⟩
--
-- Three routes were tried and each stops at a named place.
--
--   ROUTE 1, Child induction on the name. Every value member of σ is value
--   equal to the value of a CHILD of σ's code, and the children lie in the
--   ground set dom (fst σ), so the induction hypothesis gives, for each active
--   child, SOME ground ordinal with the same value. Finishing needs those
--   ground ordinals gathered into one ground set, which is a ground Collection
--   along the class "a is an ordinal and chk a has the same value as x". THAT
--   CLASS IS NOT GROUND DEFINABLE: the value relation is indexed by G, and G
--   is a host subset of the conditions, Sub = Cond → Ω at Type (ℓ-suc ℓ)
--   (ForcingNotion.agda:88-89), not an element of S. Route 1 stops there and
--   no O7 datum repairs it, because O7 internalizes FORCING, which is G free,
--   and not membership in G.
--
--   ROUTE 2, forcing. Replace "has the same value as" by "some condition of G
--   forces equality with ǎ", which IS ground definable given O7. The premise
--   of the ground Collection is then "for each active child x there merely is
--   a ground ordinal a and a condition forcing x ≐ ǎ". That premise is the
--   classical density argument, and it quantifies over the ground ordinals,
--   so proving it needs a SET of candidate ground ordinals already in hand.
--   That set is the rank bound. Route 2 is circular without it.
--
--   ROUTE 3, Track H's own Collection field. The bound K6/Replacement.agda
--   produces is a bound on WITNESSES OF A FORMULA inside the extension, not on
--   the ground ordinals a name can be value equal to, and the class in route 1
--   is still the class that is not ground definable. Route 3 reduces nothing.
--
-- SO THE PREREQUISITE IS THE RANK, exactly as decision D7 anticipated.
-- NameRankContract is declared at LInstanceRank.agda:159-163 with three
-- fields, rkᴺ, rkᴺ-ord and rkᴺ-mono, and a census over the whole compile root
-- returns those declaration lines and nothing else: rkᴺ occurs in no other
-- file, so the record has ZERO FILLERS. LInstanceRank.agda:165-177 further
-- forbids two identifications a filler might reach for, rkᴺ-is-rank and
-- rkᴺ-is-stage, until a theorem comparing the ambient rank with the
-- constructible stage exists, and none does.
--
-- OrdinalRankBound below is that prerequisite, written as a function type and
-- NOT as a record: rule 9 forbids re-declaring a record another layer owns,
-- and NameRankContract is K3's. The three components are transcribed from
-- LInstanceRank.agda:161-163 with Name := Nm, Index τ := the active children
-- of τ, and isOrdinalᴵ := CardinalBridge.isOrdinal at the ground.
--
-- ---------------------------------------------------------------------
-- RULE 15. THE ROUTE THAT WOULD DISCHARGE THIS CHEAPLY, AND IT IS POISONED
-- ---------------------------------------------------------------------
--
-- `no-new-ordinals` follows in eight lines from ontoness of the check map at
-- the value relation, K5's NON-CLAIM 4 (K5/Structures.agda:532-533). The
-- derivation typechecks: it is parked at K6/breaks/OrdViaOnto.agda-break and
-- it exits 0. That exit 0 is the FINDING and not a result. Ontoness at the
-- value relation says every name is value equal to a copy of a ground set,
-- that is, that the extension IS the ground; it is FALSE at every genuine
-- forcing extension, which is the entire purpose of forcing. A telescope
-- carrying it would discharge this field and every body level grep would pass.
-- Nothing in this file takes it, and `Onto` is named here only inside a
-- comment.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT

module K6.Ordinals {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The ground side of the vocabulary, transported and never re-spelled.

module CBᴳ = CardinalBridge 𝒮

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG public using () renaming ( _⊨_ to _⊨ᴳ_ )

--------------------------------------------------------------------------------
-- The extension structure, flat
--------------------------------------------------------------------------------

module Names (IsNm : S → Ω) where

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNm n))

  module AtG (_≈[G]_ _∈[G]_ : S → S → Ω) where

    𝒮ᴱ : ZFStructure (hPropAlgebra ℓ)
    𝒮ᴱ = record
      { S      = Nm
      ; isSetS = isSetNm
      ; _≈ˢ_   = λ σ τ → fst σ ≈[G] fst τ
      ; _∈ˢ_   = λ σ τ → fst σ ∈[G] fst τ }

    -- THE TRANSPORT, and trap T-H3 discharged. IsOrdinalφ is not written down
    -- again anywhere in K6; it is K1's formula at K6's structure.

    module CBᴱ = CardinalBridge 𝒮ᴱ

    private module SemE = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴱ
    module SatE = SemE.At Nm id
    open SatE public using ( _⊨_ )

    ordinalφ : Formula Nm 1
    ordinalφ = CBᴱ.IsOrdinalφ

    -- The reading at the extension, by refl, which is the theorem the break
    -- file has to destroy.

    ordinal-reading : (σ : Nm) → ((σ ∷ []) ⊨ ordinalφ) ≡ CBᴱ.isOrdinal σ
    ordinal-reading σ = CBᴱ.IsOrdinal-bridge σ

    Agree : ∀ {k} → Vec Nm k → Vec Nm k → Type ℓ
    Agree {k} ν μ = (ix : Fin k) → ⟨ fst (lookup ix ν) ≈[G] fst (lookup ix μ) ⟩

    ------------------------------------------------------------------------
    -- The statement, the reflection half, and the stop
    ------------------------------------------------------------------------

    module Ordinals
      -- K5/Structures.agda:400-402, unconditional.
      (sat-cong : ∀ {k} (ψ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                → (ν ⊨ ψ) ≡ (μ ⊨ ψ))
      -- K3's check name as a map into the carrier, K5/Structures.agda:588-589.
      (chk : S → Nm)
      -- Δ₀ absoluteness of the ordinal predicate along the check map. It is
      -- K5's groundSat (K5/Structures.agda:670-671) at IsOrdinalφ, which is Δ₀
      -- because every quantifier in it is bounded, and it costs ⟨ positive G ⟩
      -- and nothing else. The formula needs no relabelling: IsOrdinalφ carries
      -- no constants, so mapFo groundName sends it to itself.
      (chk-ordinal : (a : S)
                   → ((chk a ∷ []) ⊨ ordinalφ) ≡ ((a ∷ []) ⊨ᴳ CBᴳ.IsOrdinalφ))
      where

      -- THE STATEMENT, exactly as architecture 2.3 prints it. It is shipped
      -- with NO INHABITANT in this file.

      NoNewOrdinals : Type ℓ
      NoNewOrdinals =
        (σ : Nm) → ⟨ (σ ∷ []) ⊨ ordinalφ ⟩
        → ⟨ ⋁ S (λ a → CBᴳ.isOrdinal a ⊓ (fst σ ≈[G] fst (chk a))) ⟩

      -- THE HALF THAT IS PROVED. Value equality with a check name reflects
      -- ordinality downwards. Two steps: sat-cong moves the satisfaction from
      -- the given name onto the check name, and Δ₀ absoluteness reads it in
      -- the ground. Neither step needs a rank, a filter or excluded middle.

      reflect-ordinal : (σ : Nm) (a : S) → ⟨ fst σ ≈[G] fst (chk a) ⟩
                      → ⟨ (σ ∷ []) ⊨ ordinalφ ⟩ → ⟨ CBᴳ.isOrdinal a ⟩
      reflect-ordinal σ a e h =
        subst ⟨_⟩ (CBᴳ.IsOrdinal-bridge a)
          (subst ⟨_⟩ (chk-ordinal a)
            (subst ⟨_⟩ (sat-cong ordinalφ (σ ∷ []) (chk a ∷ []) agr) h))
        where
          agr : Agree (σ ∷ []) (chk a ∷ [])
          agr zero = e

      -- THE EXACT OPEN GOAL. Given the reflection half, NoNewOrdinals is
      -- equivalent to this, and this is what the attempt did not close.

      OpenGoal : Type ℓ
      OpenGoal =
        (σ : Nm) → ⟨ (σ ∷ []) ⊨ ordinalφ ⟩
        → ⟨ ⋁ S (λ a → fst σ ≈[G] fst (chk a)) ⟩

      -- And the reduction, which IS proved: the open goal is the whole gap.

      goal→theorem : OpenGoal → NoNewOrdinals
      goal→theorem g σ hσ = PT.map
        (λ { (a , e) → a , reflect-ordinal σ a e hσ , e })
        (g σ hσ)

      -- THE PREREQUISITE, transcribed from LInstanceRank.agda:161-163. Written
      -- as a function type and not as a record, because NameRankContract is
      -- K3's record and rule 9 forbids a second declaration of it. Index τ is
      -- instantiated at the subnames, which is the only Index the poset side
      -- offers. ZERO FILLERS in the compile root, measured.

      OrdinalRankBound : (Child : S → S → Type ℓ) → Type ℓ
      OrdinalRankBound Child =
        Σ[ rk ∈ (Nm → S) ]
          ( ((τ : Nm) → ⟨ CBᴳ.isOrdinal (rk τ) ⟩)
          × ((τ : Nm) (x : S) (hx : Child x (fst τ)) (hn : ⟨ IsNm x ⟩)
               → ⟨ rk (x , hn) ∈ˢ rk τ ⟩) )
