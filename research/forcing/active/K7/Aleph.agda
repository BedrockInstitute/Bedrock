{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track G. THE FIRST PUBLIC CONSUMER: ω₁ AND ω₂, AND THE INTERFACE K10 EATS.
--
-- roadmap:232 states the assembly this file feeds: K10 combines K9's injection
-- with K7's IDENTIFICATION of the extension's ω₁ and K7's PRESERVATION of the
-- ground's ω₂, so that the extension's CH would give an injection of κ into ω₁
-- and contradict the internal cardinal comparison. Preservation is Track F's
-- theorem applied twice here; identification is this file's own work and is
-- strictly harder, for a reason that is visible in one line of K1.
--
-- WHY IDENTIFICATION IS HARDER THAN PRESERVATION, AT SOURCE.
--
--   isCardinal κ = isOrdinal κ ⊓ ⋀ S (λ β → (β ∈ˢ κ) ⇒ ¬ (injectable κ β))
--                                                (CardinalBridge.agda:553-556)
--
-- The join ranges over all of S, but its body is GUARDED by β ∈ˢ κ, and at the
-- extension that guard is β ∈ᴱ chk κ. K6's copy-members
-- (K6/GroundTransfer.agda:427-429) says every such β is value equal to chk y
-- for a ground y ∈ κ, at ⟨ positiveᴾ ⟩ alone. So the quantifier collapses onto
-- the ground members of κ, and preservation needs no rank, no NoNewOrdinals
-- and no excluded middle. Verified at source in this session, and it is why
-- ruling Q9 holds.
--
--   isSuccCardinal δ κ = isCardinal δ ⊓ ((κ ∈ˢ δ)
--                      ⊓ ⋀ S (λ μ → (isCardinal μ ⊓ (κ ∈ˢ μ))
--                                 ⇒ ((δ ≈ˢ μ) ⊔ (δ ∈ˢ μ))))
--                                                (CardinalBridge.agda:592-597)
--
-- The third conjunct's guard is isCardinal μ ⊓ (κ ∈ˢ μ). NEITHER clause is a
-- membership in a check name, so copy-members does not reach it and the
-- quantifier really does range over all of Nm. That single conjunct is the
-- whole difficulty of this track.
--
-- WHAT IT NEEDS, AND WHAT IT DOES NOT. It needs ordinal comparability at the
-- EXTENSION, which is Track B's ord-compare and arrives here flat. It does NOT
-- need no-new-ordinals, and PART 0 below carries that boundary as a type with
-- no inhabitant, sited in a module that the mathematics cannot see.
--
-- THAT SLOT IS NO LONGER AN UNKNOWN. K7/AlephAtStructures.agda applies Track
-- B's file at the EXTENSION structure and extracts ord-compare there for real,
-- so the slot below is filled by a landed theorem and not by hope. Its price
-- is exactly Track B's: FoundationInduction at the extension, which is
-- unconditional and landed (K6/Foundation.agda:213); Separation at the
-- extension, which is the conditional one; and LEM ℓ, which the programme's
-- single LEM (ℓ-suc ℓ) covers through lowerLEM and which therefore adds zero.
-- All three are ARGUMENTS of the declarations that spend them, never module
-- parameters, so they are visible in the type of ω₁-identified itself.
--
-- MEASURED AGAINST THE LANDED PRODUCERS, and three of the architecture's
-- printed signatures were wrong. Track A ascribes CCC₂ᴵ : S → S → S → Ω with
-- the presentation's carrier and order EXPLICIT (K7/ChainConditions.agda:305),
-- not S → Ω. Track F's preservation theorem is no-collapse-in-range
-- (K7/NoCollapse.agda:609-616) and its range hypothesis is ProvedRangeHolds,
-- not a possible-value bound. Track B's ord-compare does NOT take Pairing
-- (K7/CardinalOrder.agda:474-480), which it measured unused and removed. The
-- telescope below is the LANDED shapes, not architecture 2.6's sketch.
--
-- ONE CORRECTION TO THE ARCHITECTURE'S TELESCOPE FOR THIS TRACK, rule 14.
-- Route M as written in architecture 2.7 is one hypothesis short. After
-- ord-compare has reduced the hard case to "μ is value equal to chk y for a
-- ground y ∈ ω₁", and ω₁-members-countable has produced a GROUND injection
-- y ↪ w, the contradiction with isCardinalᴱ μ needs that injection AT THE
-- EXTENSION. Injectableφ is ∃̇ IsInjectionφ (CardinalBridge.agda:379-380) and
-- IsInjectionφ is NOT Δ₀: IsFunctionφ carries three unbounded ∀̇
-- (CardinalBridge.agda:176-182) and InjDomφ two unbounded ∃̇ (:257-261), so
-- K5's groundSat, whose ∃̇ and ∀̇ clauses are absurd patterns on the Δ₀ witness
-- (K5/Structures.agda:689-690), does not carry it across the check map. The
-- upward transfer is therefore a NAMED PARAMETER of this file, chk-injectable,
-- and it is not free. Its converse is the poisoned direction and PART 0 carries
-- that too.
--
-- WHAT IS NOT PROVED ANYWHERE IN THE PROGRAMME, and ruling Q7's mandatory row.
-- Nothing inhabits isSuccCardinal. Measured over the compile root in this
-- session: isSuccCardinal and IsSuccCardinalφ occur outside CardinalBridge.agda
-- only at CHSentence.agda:170, :177 and :191, all inside sentences, and no term
-- anywhere produces the predicate. The ground existence of ω₁ and ω₂ is NOT
-- delivered by K7 and its owner is K8 or a K1 addendum. The three cardinals are
-- therefore ARGUMENTS of the module below and their defining hypotheses are
-- written in the telescope where a reader sees them, never folded into a body.
-- A parametric theorem with a named unwitnessed hypothesis is a result; the
-- same theorem without the row is K5 Track J's failure shape.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
import CardinalBridge
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT

module K7.Aleph {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Base.Classical using ( LEM )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎ ; inr to inr⊎ )
import Cubical.Data.Empty as Empty
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The ground vocabulary is K1's, transported and never re-spelled. This is
-- trap T-H3 as K6/Ordinals.agda:11-18 records it: re-spelling a bounded
-- quantifier at uniform depth re-opens K1's measured linearity bug, and the
-- reading theorem is the only thing that catches it.

module CBᴳ = CardinalBridge 𝒮

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG public using () renaming ( _⊨_ to _⊨ᴳ_ )

--------------------------------------------------------------------------------
-- The ground order theory this file spends, three projections and one step
--------------------------------------------------------------------------------

-- Everything in this section is a projection out of K1's own unfolding, so it
-- costs nothing and takes no profile axiom. They are named because the proofs
-- below read better with the mathematics visible than with four nested fst and
-- snd, and because ω₂-is-cardinal genuinely uses the ordinal step.

cardinal-ordinal : (κ : S) → ⟨ CBᴳ.isCardinal κ ⟩ → ⟨ CBᴳ.isOrdinal κ ⟩
cardinal-ordinal κ h = fst h

succ-is-cardinal : (δ κ : S) → ⟨ CBᴳ.isSuccCardinal δ κ ⟩ → ⟨ CBᴳ.isCardinal δ ⟩
succ-is-cardinal δ κ h = fst h

succ-is-above : (δ κ : S) → ⟨ CBᴳ.isSuccCardinal δ κ ⟩ → ⟨ κ ∈ˢ δ ⟩
succ-is-above δ κ h = fst (snd h)

-- An ordinal is a transitive set, which is the first conjunct of isOrdinal
-- (CardinalBridge.agda:531-537). This is the one inference the ω₂ statement
-- needs that is not a projection: no-collapse asks for w ∈ˢ ω₂ and the
-- hypotheses give w ∈ˢ ω₁ and ω₁ ∈ˢ ω₂.

ordinal-mem-trans : (α x y : S) → ⟨ CBᴳ.isOrdinal α ⟩
                  → ⟨ x ∈ˢ α ⟩ → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ α ⟩
ordinal-mem-trans α x y hα hx hy = fst hα x hx y hy

--------------------------------------------------------------------------------
-- The extension side, the flat spine of K6/Ordinals.agda:126-161
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

    module CBᴱ = CardinalBridge 𝒮ᴱ
    module OPᴱ = OrdinaryProfile 𝒮ᴱ

    private module SemE = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴱ
    module SatE = SemE.At Nm id
    open SatE public using ( _⊨_ )

    -- The two relations of the extension structure, under names that read.
    -- Each is the record field of 𝒮ᴱ and reduces to it, so a statement written
    -- with them IS a statement of the extension structure and not of a
    -- lookalike; that is trap T11 and it is discharged by computation here.

    _≈ᴱ_ : Nm → Nm → Ω
    σ ≈ᴱ τ = fst σ ≈[G] fst τ

    _∈ᴱ_ : Nm → Nm → Ω
    σ ∈ᴱ τ = fst σ ∈[G] fst τ

    Agree : ∀ {k} → Vec Nm k → Vec Nm k → Type ℓ
    Agree {k} ν μ = (ix : Fin k) → ⟨ fst (lookup ix ν) ≈[G] fst (lookup ix μ) ⟩

    -- The readings at the extension, by refl in both cases, because K1's
    -- formulas are structure-polymorphic and these are K1's own bridges at 𝒮ᴱ.

    ordinal-reading : (σ : Nm) → ((σ ∷ []) ⊨ CBᴱ.IsOrdinalφ) ≡ CBᴱ.isOrdinal σ
    ordinal-reading σ = CBᴱ.IsOrdinal-bridge σ

    injectable-reading : (σ τ : Nm)
                       → ((σ ∷ τ ∷ []) ⊨ CBᴱ.Injectableφ) ≡ CBᴱ.injectable σ τ
    injectable-reading σ τ = CBᴱ.Injectable-bridge σ τ

    ----------------------------------------------------------------------------
    -- PART 0. THE BOUNDARY, AND IT IS A SIBLING OF THE MATHEMATICS
    ----------------------------------------------------------------------------

    -- Ruling Q9: K7 does NOT own no-new-ordinals, and this module is where a
    -- reader sees that decision rather than reading about it. Three statements
    -- are transcribed here and NONE of them is inhabited. The module is a
    -- SIBLING of module Aleph below, on K6/Choice.agda's own model (:415 inside
    -- :343, beside :772), so no theorem of this file can reach them even by
    -- accident. That arrangement, and not a grep, is what makes the boundary
    -- hold under a later edit: falsifying it requires moving a module.

    module Boundary (chk : S → Nm) where

      -- NOT CLAIMED 1. K6 Track H's open statement, transcribed character for
      -- character from K6/Ordinals.agda:187-189. Its prerequisite is an
      -- ordinal rank on names, NameRankContract at LInstanceRank.agda:159-163,
      -- and that record has ZERO FILLERS: re-measured in this session, rkᴺ
      -- occurs at :161, :162, :163 and in prose, and nowhere else in the
      -- compile root. Owner: K6 Track H re-owned, or K8. NOT K7: nothing this
      -- file proves consumes it, and the one conjunct that looked as though it
      -- must is bought by ord-compare instead.

      NotClaimed-NoNewOrdinals : Type ℓ
      NotClaimed-NoNewOrdinals =
        (σ : Nm) → ⟨ (σ ∷ []) ⊨ CBᴱ.IsOrdinalφ ⟩
        → ⟨ ⋁ S (λ a → CBᴳ.isOrdinal a ⊓ (fst σ ≈[G] fst (chk a))) ⟩

      -- NOT CLAIMED 2, and this is rule 15's class (iii) witness for the whole
      -- programme, transcribed from K5/Structures.agda:532-533. Ontoness of the
      -- check map at the value relation says every name is value equal to a
      -- copy of a ground set, that is, that the extension IS the ground. It is
      -- FALSE at every genuine forcing extension, which is the entire purpose
      -- of forcing. From it NotClaimed-NoNewOrdinals follows in two lines at
      -- exit 0, and so does this track's ω₁-identified with ord-compare, CCC₂
      -- and the possible-value bound all removed from scope. The break file
      -- K7/breaks/AlephViaOnto.agda-break holds that derivation and its exit 0
      -- is the finding.

      NotClaimed-Onto : Type ℓ
      NotClaimed-Onto = (σ : Nm) → ∥ Σ[ a ∈ S ] ⟨ fst σ ≈[G] fst (chk a) ⟩ ∥₁

      -- NOT CLAIMED 3, and it is this track's OWN class (iii) shape, which the
      -- architecture does not name. module Aleph takes the UPWARD transfer of
      -- injectability along the check map, chk-injectable, which says a ground
      -- injection is an extension injection and is true at every extension. The
      -- statement below is that arrow REVERSED. Read at a := ω₁ and b := w it
      -- says that if the extension's ω₁ injects into the extension's ω then the
      -- ground's ω₁ already injected into the ground's ω, which is exactly what
      -- a collapsing forcing refutes; and it proves ω₁-is-cardinal on its own,
      -- with no chain condition and no possible-value bound anywhere in the
      -- derivation. K7/breaks/AlephViaDownward.agda-break holds that derivation.
      -- A telescope carrying this arrow discharges this track cheaply and every
      -- body-level grep passes.

      NotClaimed-InjectableDown : Type ℓ
      NotClaimed-InjectableDown =
        (a b : S) → ⟨ CBᴱ.injectable (chk a) (chk b) ⟩ → ⟨ CBᴳ.injectable a b ⟩

    ----------------------------------------------------------------------------
    -- PART 1. THE TRACK
    ----------------------------------------------------------------------------

    module Aleph
      -- K5/Structures.agda:400-402, unconditional, no positivity and no filter.
      (sat-cong : ∀ {k} (ψ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                → (ν ⊨ ψ) ≡ (μ ⊨ ψ))
      -- Valuation.agda:349, :377, inside module Value G, unconditional in G.
      (≈-refl : (x : S) → ⟨ x ≈[G] x ⟩)
      (≈-sym  : {x y : S} → ⟨ x ≈[G] y ⟩ → ⟨ y ≈[G] x ⟩)
      -- K3's check name into the carrier, K5/Structures.agda:588-589.
      (chk : S → Nm)
      -- The positivity predicate of the notion, flat. Every K6 transfer below
      -- costs this and nothing else; see K6/GroundTransfer.agda:499-500.
      (positiveᴾ : Ω)
      -- K6 Track C, flat, at ⟨ positiveᴾ ⟩ alone. K6/GroundTransfer.agda:427-429
      -- for the first and :344 (check-faithful, restated as nat-faithful at
      -- :504-505) for the second.
      (copy-members : ⟨ positiveᴾ ⟩ → (a : S) (τ : Nm) → ⟨ τ ∈ᴱ chk a ⟩
                    → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ ≈[G] fst (chk y))) ⟩)
      (chk-mem : ⟨ positiveᴾ ⟩ → (m n : S) → (chk m ∈ᴱ chk n) ≡ (m ∈ˢ n))
      -- K6 Track H, flat, a PATH. K6/Ordinals.agda:179-180. It is K5's
      -- groundSat at IsOrdinalφ, which is Δ₀, so it costs ⟨ positiveᴾ ⟩ and
      -- nothing else; the Δ₀ certificate itself is Track B's Δ₀-IsOrdinalφ.
      (chk-ordinal : (a : S) → ((chk a ∷ []) ⊨ CBᴱ.IsOrdinalφ)
                             ≡ ((a ∷ []) ⊨ᴳ CBᴳ.IsOrdinalφ))
      -- Track A, flat. The coded presentation's carrier and order, and the
      -- second chain condition at them. THREE arguments, not one: measured
      -- against the landed file, K7/ChainConditions.agda:305 ascribes
      -- CCC₁ᴵ CCC₂ᴵ CCC₃ᴵ : S → S → S → Ω with carrier and order explicit, and
      -- architecture 2.2's S → Ω is wrong. CCC₂ᴵ is opaque here: this file
      -- never looks inside it and never uses it except by handing it on, so no
      -- body can specialize the chain condition to one notion.
      (c o : S)
      (CCC₂ᴵ : S → S → S → Ω)
      -- Track F, flat, and this is its landed no-collapse-in-range
      -- (K7/NoCollapse.agda:609-616) with its five-item unowned prefix bundled
      -- into one opaque type. Those five are FamilySet, ValueAntichain,
      -- InverseSpread, ProvedRangeHolds and the ground's Collection and
      -- Separation; ProvedRangeHolds (K7/NoCollapse.agda:505-508) is Track F's
      -- own unwitnessed row and stays owed by Track F, not by this file.
      -- Bundling is deliberate: nothing in this file may take one of them
      -- apart, and a reader counting this track's hypotheses should count one
      -- supply object with a named owner rather than five it might discharge.
      (Supplies : Type ℓ)
      (no-collapse : Supplies → ⟨ positiveᴾ ⟩ → (v κ : S) → ⟨ CBᴳ.isOmega v ⟩
                   → ⟨ CBᴳ.isCardinal κ ⟩ → ⟨ v ∈ˢ κ ⟩ → ⟨ CCC₂ᴵ c o v ⟩
                   → ⟨ CBᴱ.isCardinal (chk κ) ⟩)
      -- Track B, flat, route M of architecture 2.7, at the EXTENSION. Track B's
      -- theorem is structure-polymorphic (K7/CardinalOrder.agda:478-480) and
      -- this is its instance at 𝒮ᴱ, WITH ITS THREE HYPOTHESES LEFT STANDING
      -- rather than applied, because they are where the identification's whole
      -- conditionality sits and a consumer must see them. Pairing is NOT among
      -- them: Track B measured it unused and removed it, against the
      -- architecture's printed signature. At the extension FoundationInduction
      -- is unconditional and landed (K6/Foundation.agda:213, the schema form,
      -- which IS OrdinaryProfile.FoundationInduction 𝒮ᴱ); Separation is the
      -- conditional one and carries O1 plus the O3b five plus Supply plus LEM
      -- plus O7 with it.
      (ord-compare : OPᴱ.FoundationInduction → OPᴱ.Separation → LEM ℓ
                   → (α δ : Nm) → ⟨ CBᴱ.isOrdinal α ⟩ → ⟨ CBᴱ.isOrdinal δ ⟩
                   → ⟨ (α ∈ᴱ δ) ⊔ ((α ≈ᴱ δ) ⊔ (δ ∈ᴱ α)) ⟩)
      -- THE ONE PARAMETER THE ARCHITECTURE'S TELESCOPE FOR THIS TRACK OMITS.
      -- A ground injection is an extension injection. True at every extension,
      -- unbuilt anywhere in the compile root, and not free: see the header.
      -- Its reversal is PART 0's NotClaimed-InjectableDown.
      (chk-injectable : (a b : S) → ⟨ CBᴳ.injectable a b ⟩
                      → ⟨ CBᴱ.injectable (chk a) (chk b) ⟩)
      -- The three cardinals are ARGUMENTS, ruling Q7. Nothing in the programme
      -- builds them and K7 does not either; the ledger row is in the header.
      (w ω₁ ω₂ : S)
      (w-omega : ⟨ CBᴳ.isOmega w ⟩)
      (ω₁-succ : ⟨ CBᴳ.isSuccCardinal ω₁ w ⟩)
      (ω₂-succ : ⟨ CBᴳ.isSuccCardinal ω₂ ω₁ ⟩)
      -- The one further ground hypothesis route M needs, named rather than
      -- hidden in a body. At a genuine ZFC ground it is the standard fact that
      -- every ordinal below ω₁ is countable; the ordinary profile has no
      -- cardinality theory to prove it, so K7 takes it and names the owner.
      (ω₁-members-countable : (b : S) → ⟨ b ∈ˢ ω₁ ⟩ → ⟨ CBᴳ.injectable b w ⟩)
      (pos : ⟨ positiveᴾ ⟩)
      where

      --------------------------------------------------------------------------
      -- 1.1 The membership copy at an arbitrary κ
      --------------------------------------------------------------------------

      -- K6 stated this only at a ground ω, inside module AtOmega
      -- (K6/GroundTransfer.agda:501-530), and the general form it is an
      -- instance of sits one module up at :427-429. The restatement matters
      -- because THE NAME ωᴳ CARRIES NO CONTENT: K6/GroundTransfer.agda:501
      -- declares module AtOmega (ωᴳ : S) with no isOmega hypothesis at all, and
      -- isOmega occurs nowhere in that file, measured. So what Track C proved is
      -- a statement about an arbitrary ground set, and a consumer that reads
      -- "at ω" off the module name has read a name and not a theorem. This file
      -- supplies ⟨ CBᴳ.isOmega w ⟩ itself, in the telescope, and uses the copy
      -- at ω₁ where it needs it, which is not ω.

      aleph-members : ⟨ positiveᴾ ⟩ → (κ : S) (τ : Nm) → ⟨ τ ∈ᴱ chk κ ⟩
                    → ⟨ ⋁ S (λ a → (a ∈ˢ κ) ⊓ (fst τ ≈[G] fst (chk a))) ⟩
      aleph-members = copy-members

      --------------------------------------------------------------------------
      -- 1.2 Ordinality travels up, and it is a path in both directions
      --------------------------------------------------------------------------

      -- Three substitutions and no mathematics: K1's ground bridge is refl,
      -- chk-ordinal is a path, and K1's extension bridge is refl. Writing it as
      -- an implication rather than as the path it comes from is deliberate,
      -- because the direction this file consumes is the upward one and a reader
      -- should not have to work out which way a path was meant to be read.

      chk-ordinal-up : (κ : S) → ⟨ CBᴳ.isOrdinal κ ⟩ → ⟨ CBᴱ.isOrdinal (chk κ) ⟩
      chk-ordinal-up κ h =
        subst ⟨_⟩ (ordinal-reading (chk κ))
          (subst ⟨_⟩ (sym (chk-ordinal κ))
            (subst ⟨_⟩ (sym (CBᴳ.IsOrdinal-bridge κ)) h))

      --------------------------------------------------------------------------
      -- 1.3 Injectability respects value equality at the extension
      --------------------------------------------------------------------------

      -- This is free and it is proved here rather than taken from Track B,
      -- which is a measured saving of one upstream edge: sat-cong is
      -- unconditional and K1's bridge is the same refl at 𝒮ᴱ that it is at 𝒮,
      -- so congruence of a formula's reading along the value relation needs
      -- nothing else. The second slot of the environment is unchanged and its
      -- Agree obligation is reflexivity of the value relation, which is
      -- Valuation.agda:349 and is likewise unconditional.

      injectable-congᴱ : (σ τ ζ : Nm) → ⟨ σ ≈ᴱ τ ⟩
                       → ⟨ CBᴱ.injectable σ ζ ⟩ → ⟨ CBᴱ.injectable τ ζ ⟩
      injectable-congᴱ σ τ ζ e h =
        subst ⟨_⟩ (injectable-reading τ ζ)
          (subst ⟨_⟩ (sat-cong CBᴱ.Injectableφ (σ ∷ ζ ∷ []) (τ ∷ ζ ∷ []) agr)
            (subst ⟨_⟩ (sym (injectable-reading σ ζ)) h))
        where
          agr : Agree (σ ∷ ζ ∷ []) (τ ∷ ζ ∷ [])
          agr zero       = e
          agr (suc zero) = ≈-refl (fst ζ)

      --------------------------------------------------------------------------
      -- 1.4 PRESERVATION. The two cardinals survive
      --------------------------------------------------------------------------

      -- Both are Track F's theorem, and the only work here is assembling its
      -- hypothesis column out of the two successor-cardinal hypotheses. For ω₁
      -- both clauses are projections. For ω₂ the membership w ∈ˢ ω₂ is not
      -- given and is one transitivity step through ω₁, which is where
      -- ordinal-mem-trans is spent and the only place in this file where the
      -- ground order theory does real work.

      w-in-ω₁ : ⟨ w ∈ˢ ω₁ ⟩
      w-in-ω₁ = succ-is-above ω₁ w ω₁-succ

      w-in-ω₂ : ⟨ w ∈ˢ ω₂ ⟩
      w-in-ω₂ = ordinal-mem-trans ω₂ ω₁ w
        (cardinal-ordinal ω₂ (succ-is-cardinal ω₂ ω₁ ω₂-succ))
        (succ-is-above ω₂ ω₁ ω₂-succ)
        w-in-ω₁

      ω₁-is-cardinal : Supplies → ⟨ CCC₂ᴵ c o w ⟩ → ⟨ CBᴱ.isCardinal (chk ω₁) ⟩
      ω₁-is-cardinal sup ccc =
        no-collapse sup pos w ω₁ w-omega
          (succ-is-cardinal ω₁ w ω₁-succ) w-in-ω₁ ccc

      ω₂-is-cardinal : Supplies → ⟨ CCC₂ᴵ c o w ⟩ → ⟨ CBᴱ.isCardinal (chk ω₂) ⟩
      ω₂-is-cardinal sup ccc =
        no-collapse sup pos w ω₂ w-omega
          (succ-is-cardinal ω₂ ω₁ ω₂-succ) w-in-ω₂ ccc

      --------------------------------------------------------------------------
      -- 1.5 IDENTIFICATION. chk ω₁ is still the successor of chk w
      --------------------------------------------------------------------------

      -- The second conjunct first, because it is the cheap one: membership of
      -- the check names reflects ground membership on the nose, which is K6's
      -- check-faithful and costs ⟨ positiveᴾ ⟩.

      chk-w-in-chk-ω₁ : ⟨ chk w ∈ᴱ chk ω₁ ⟩
      chk-w-in-chk-ω₁ = subst ⟨_⟩ (sym (chk-mem pos w ω₁)) w-in-ω₁

      -- THE HARD CASE, ISOLATED. Suppose an extension cardinal μ lies strictly
      -- below chk ω₁ and strictly above chk w. Then aleph-members puts a ground
      -- y ∈ ω₁ with μ value equal to chk y; ω₁-members-countable injects y into
      -- w in the ground; chk-injectable lifts that injection to the extension;
      -- congruence moves its source from chk y to μ; and μ's own cardinality,
      -- read at the member chk w, forbids exactly that injection. The whole
      -- argument is ONE contradiction and every step in it is named in the
      -- telescope, which is the point: no step of it is doing work the reader
      -- cannot price.
      --
      -- Note which cardinality is used and where. isCardinalᴱ μ is applied at
      -- β := chk w, a MEMBER of μ, so its bounded guard is satisfied by the
      -- hypothesis of the conjunct itself. Nothing here quantifies over host
      -- predicates, host subsets or host functions: μ ranges over Nm, y over S,
      -- and the injection is an element of the model in both structures.

      below-ω₁-absurd : (μ : Nm) → ⟨ CBᴱ.isCardinal μ ⟩ → ⟨ chk w ∈ᴱ μ ⟩
                      → ⟨ μ ∈ᴱ chk ω₁ ⟩ → Empty.⊥
      below-ω₁-absurd μ hcard hmem hbelow =
        PT.rec Empty.isProp⊥ step (aleph-members pos ω₁ μ hbelow)
        where
          step : Σ[ y ∈ S ] ⟨ (y ∈ˢ ω₁) ⊓ (fst μ ≈[G] fst (chk y)) ⟩ → Empty.⊥
          step (y , hy , e) =
            snd hcard (chk w) hmem
              (injectable-congᴱ (chk y) μ (chk w) (≈-sym e)
                (chk-injectable y w (ω₁-members-countable y hy)))

      -- THE THIRD CONJUNCT. ord-compare offers three cases, two of which ARE
      -- the conclusion and the third of which is the contradiction above. This
      -- is the whole of route M, and it is worth saying what it does not use:
      -- no rank on names, no NoNewOrdinals, no ontoness of the check map, and
      -- no filter law. The price is ord-compare's own, which is the extension's
      -- Separation, and that is a price the three conditional K6 fields already
      -- pay.

      ω₁-minimal : OPᴱ.FoundationInduction → OPᴱ.Separation → LEM ℓ
                 → (μ : Nm) → ⟨ (CBᴱ.isCardinal μ) ⊓ (chk w ∈ᴱ μ) ⟩
                 → ⟨ (chk ω₁ ≈ᴱ μ) ⊔ (chk ω₁ ∈ᴱ μ) ⟩
      ω₁-minimal findᴱ sepᴱ lem μ (hcard , hmem) =
        PT.rec PT.squash₁ outer
          (ord-compare findᴱ sepᴱ lem (chk ω₁) μ
             ordinal-chk-ω₁ (cardinal-ordinalᴱ μ hcard))
        where
          ordinal-chk-ω₁ : ⟨ CBᴱ.isOrdinal (chk ω₁) ⟩
          ordinal-chk-ω₁ =
            chk-ordinal-up ω₁
              (cardinal-ordinal ω₁ (succ-is-cardinal ω₁ w ω₁-succ))

          cardinal-ordinalᴱ : (ν : Nm) → ⟨ CBᴱ.isCardinal ν ⟩ → ⟨ CBᴱ.isOrdinal ν ⟩
          cardinal-ordinalᴱ ν h = fst h

          inner : ⟨ chk ω₁ ≈ᴱ μ ⟩ ⊎ ⟨ μ ∈ᴱ chk ω₁ ⟩
                → ⟨ (chk ω₁ ≈ᴱ μ) ⊔ (chk ω₁ ∈ᴱ μ) ⟩
          inner (inl⊎ he) = ∣ inl⊎ he ∣₁
          inner (inr⊎ hb) = Empty.rec (below-ω₁-absurd μ hcard hmem hb)

          outer : ⟨ chk ω₁ ∈ᴱ μ ⟩ ⊎ ⟨ (chk ω₁ ≈ᴱ μ) ⊔ (μ ∈ᴱ chk ω₁) ⟩
                → ⟨ (chk ω₁ ≈ᴱ μ) ⊔ (chk ω₁ ∈ᴱ μ) ⟩
          outer (inl⊎ hi) = ∣ inr⊎ hi ∣₁
          outer (inr⊎ hr) = PT.rec PT.squash₁ inner hr

      -- THE DELIVERABLE K10 CONSUMES. Three conjuncts, in K1's own order.

      ω₁-identified : Supplies → ⟨ CCC₂ᴵ c o w ⟩
                    → OPᴱ.FoundationInduction → OPᴱ.Separation → LEM ℓ
                    → ⟨ CBᴱ.isSuccCardinal (chk ω₁) (chk w) ⟩
      ω₁-identified sup ccc findᴱ sepᴱ lem =
          ω₁-is-cardinal sup ccc
        , chk-w-in-chk-ω₁
        , ω₁-minimal findᴱ sepᴱ lem

      -- And the same statement read through K1's formula rather than through
      -- its host unfolding, which is the shape a later package that works in
      -- the object language will ask for. The bridge is K1's and this file
      -- re-spells nothing.

      ω₁-identified-sat : Supplies → ⟨ CCC₂ᴵ c o w ⟩
                        → OPᴱ.FoundationInduction → OPᴱ.Separation → LEM ℓ
                        → ⟨ (chk ω₁ ∷ chk w ∷ []) ⊨ CBᴱ.IsSuccCardinalφ ⟩
      ω₁-identified-sat sup ccc findᴱ sepᴱ lem =
        subst ⟨_⟩ (sym (CBᴱ.IsSuccCardinal-bridge (chk ω₁) (chk w)))
          (ω₁-identified sup ccc findᴱ sepᴱ lem)

      ω₂-is-cardinal-sat : Supplies → ⟨ CCC₂ᴵ c o w ⟩
                         → ⟨ (chk ω₂ ∷ []) ⊨ CBᴱ.IsCardinalφ ⟩
      ω₂-is-cardinal-sat sup ccc =
        subst ⟨_⟩ (sym (CBᴱ.IsCardinal-bridge (chk ω₂)))
          (ω₂-is-cardinal sup ccc)
