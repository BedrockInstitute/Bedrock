{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track F. THE REUSABLE PRESERVATION THEOREM: NO COLLAPSING SURJECTION.
--
-- The roadmap's words are the specification (roadmap:214): "exclude collapsing
-- surjections and forbidden short cofinal maps ... State the reusable theorem
-- parametrically over ground cardinals in its proved range; do not hide a
-- Cohen-specific preservation proof."
--
-- WHAT THIS FILE PROVES, AND THE BOUNDARY IT DOES NOT CROSS.
--
-- It proves the SURJECTION half and nothing about cofinality. Ruling Q4 ships
-- cofinality as a stop report in Track H and re-owns cofinality preservation
-- to K12a. The evidence is decisive and was re-measured for this file:
-- `cofinal`, `cofinality`, `singular` and `isRegular` have zero declarations
-- in the whole compile root, positively controlled; Bell's regularity proof
-- invokes the Maximum Principle by name; `MaximumPrinciple`
-- (K4/Witnesses.agda:858-861) is uninhabited; and k4-architecture.md:998
-- refuses K7 by name in advance. The type NotClaimed-Regularity at the bottom
-- of this file transcribes the cofinality statement in the vocabulary this
-- file DOES have, and it is shipped with no inhabitant, so that a reader sees
-- the boundary rather than inferring it. The reason the argument here does not
-- reach it is mathematical and not a missing lemma: this file's ProvedRange is
-- a COVERING hypothesis, and the range of a cofinal map need not cover its
-- target. Nothing below weakens that gap.
--
-- THE TWO TRAPS THE ROADMAP NAMES, AND BOTH ARE THIS TRACK'S.
--
-- T3, a Cohen-specific proof dressed as general. The mechanical form of the
-- protection is that the chain condition arrives as a HYPOTHESIS and never as
-- an instance: CCC₂ᴵ is an opaque `S → S → S → Ω` parameter with one use law,
-- so no
-- body in this file can look inside it, and no Cohen vocabulary of any kind
-- (finiteness, coordinates, partial functions, freshness, a product κ × ω)
-- occurs anywhere. The theorem is stated over an arbitrary coded presentation
-- through its carrier c and order o taken flat, over an arbitrary Cond and
-- filter membership G∈, and over an arbitrary ground cardinal.
--
-- T2, a preservation theorem that is vacuous because its cardinal hypothesis is
-- unwitnessed. This is K5 Track J's measured failure shape and it is real here.
-- The only inhabitant of CodedCompletion.Presentation in the compile root is
-- K6/OnePoint.agda:158, the one-point notion, and there the chain condition
-- CANNOT SEE THE ORDER: Track A's K7/breaks/OnePointDiscriminates.agda-break
-- proves at exit 0 that CCC₂ᴵ c o w is invariant under replacing o by any
-- other set of the model, and this track's own
-- K7/breaks/AntichainAtOnePoint.agda-break proves at exit 0 that every ground
-- set whatever is an antichain there. A predicate that cannot see the order is
-- not a chain condition.
--
-- Note the precise form, because architecture 3.9 states it wrongly. It is NOT
-- that the three conditions hold vacuously at the one-point notion: `one-point`
-- (K6/OnePoint.agda:200-201) discharges the conclusion p ≡ q of the HOST
-- antichain predicate (ForcingNotion.agda:153-155), while CCC₂ᴵ concludes
-- injectable d w, about which one-point says nothing. What is vacuous is the
-- antichain HYPOTHESIS; CCC₂ᴵ there is neither vacuously true nor false.
--
-- So no K7 chain-condition hypothesis can be shown load-bearing BY INSTANCE in
-- this tree, only BY BREAK, and K7/breaks/NoCCC.agda-break is this track's.
-- The telescope is honest in the narrow sense (every slot is fillable) and
-- conditional in the wide sense (nothing in this programme yet makes CCC₂
-- non-trivially true). Owner K8, roadmap:219.
-- Ruling Q7 governs the parametric statement: it is permitted WITH a ledger row
-- naming the unwitnessed hypothesis, and ProvedRangeHolds below is that row in
-- type form, transcribed and not inhabited.
--
-- THE ARGUMENT, IN ONE PARAGRAPH.
--
-- Suppose a function f makes the ground set κ a set of values of f at ground
-- members of a smaller ground set β. Truth supplies p ∈ G forcing that f is a
-- function. For each ξ ∈ β its possible values below p form a ground set,
-- bounded inside κ. Directedness of G and forcing monotonicity put each actual
-- value in this local set. The chain condition makes each of those ground
-- sets countable, because the conditions deciding distinct values are pairwise
-- incompatible and so form an antichain. So κ is covered by a β-indexed family
-- of countable ground sets, which for a ground cardinal κ above ω it is not.
-- The contradiction is therefore assembled entirely in the ground, and the only
-- step that mentions the extension is the first.
--
-- THE PROPER-CLASS TRAP, SHARED WITH TRACK E (roadmap:205).
--
-- The family ξ ↦ (possible values of f at ξ) is written here as a host function
-- of a ground element, and a host function is not a set. The proof never uses it
-- as one. FamilySet below is the named hypothesis that the family is COLLECTED
-- by a ground set F, and the ground axiom that supplies it is Collection spent
-- through GroundDescription.hasImage′ (:182-186, whose two standalone Separation
-- and Collection arguments Track D verified at source), with the indexing
-- injection F → β supplied by M's own well ordering through Track D's
-- Well.leastOf (K7/CompletionTransfer.agda:100-110), which is unique choice and
-- not choice. ProvedRange quantifies over ground sets β, F and a only: there is
-- no host predicate and no host family anywhere in its statement, so a reviewer
-- can run the check mechanically by reading its quantifiers.
--
-- WHAT IS NOT APPLIED HERE, and the reason is measured (architecture 1.7).
-- K6.ForcesTruth composed down to truth-at measured 102.95 s and 9.08 GB, above
-- the -M8g cap. `forces` and `truth-at` arrive flat in exactly the shape
-- K6/Separation.agda:276-279 takes them. No K5.Structures, no K5.Truth, no
-- K5.Frame, no CodedCompletion.Core, no Certificate.Nonzero.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
import CardinalBridge
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty

module K7.NoCollapse
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
open OP using ( iff ; Separation ; Collection )
open OP.PathRealization paths using ( ≈ˢ-to-path ; path-to-≈ˢ )

-- The ground side of the cardinal vocabulary, transported and never
-- re-spelled. Rule 9: CardinalBridge owns injectable, isOrdinal, isCardinal
-- and isOmega, and this file re-declares none of them.

module CBᴳ = CardinalBridge 𝒮

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG public using () renaming ( _⊨_ to _⊨ᴳ_ )

--------------------------------------------------------------------------------
-- The extension structure, flat
--------------------------------------------------------------------------------

-- K6/Ordinals.agda:126-141, character for character. The cheapest template in
-- the tree: a names module giving the carrier, then a value-relation module
-- building 𝒮ᴱ as a record literal and applying CardinalBridge to it. Measured
-- cost of the whole pattern in K6: 0.69 s.

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

    private module SemE = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴱ
    module SatE = SemE.At Nm id
    open SatE public using () renaming ( _⊨_ to _⊨ᴱ_ )

    infix 20 _≈ᴱ_ _∈ᴱ_

    _≈ᴱ_ : Nm → Nm → Ω
    σ ≈ᴱ τ = fst σ ≈[G] fst τ

    _∈ᴱ_ : Nm → Nm → Ω
    σ ∈ᴱ τ = fst σ ∈[G] fst τ

    -- K5/Structures.agda:378-382's agreement relation, which is the hypothesis
    -- shape sat-cong wants. Value equality coordinate by coordinate, never a
    -- host path between names.

    Agree : ∀ {k} → Vec Nm k → Vec Nm k → Type ℓ
    Agree {k} ν μ = (ix : Fin k) → ⟨ fst (lookup ix ν) ≈[G] fst (lookup ix μ) ⟩

    ----------------------------------------------------------------------------
    -- The notion, and positivity spelled from the two parameters it is built of
    ----------------------------------------------------------------------------

    -- K6/GroundTransfer.agda:242-243, which is ForcingNotion.agda:160-161 with
    -- the definition of _∈ᴾ_ unfolded. Positivity is the ONLY thing the copy
    -- lemmas below cost: no filter law, no genericity, no rank, no LEM.

    module AtNotion (Cond : Type ℓ) (G∈ : Cond → Ω) where

      positiveᴾ : Ω
      positiveᴾ = ⋁ Cond (λ q → G∈ q)

      ------------------------------------------------------------------------
      -- THE TELESCOPE. Rule 15: this list is the only protection, and the
      -- report audits it in the three classes separately from the bodies.
      ------------------------------------------------------------------------

      module Preserve
        -- The coded presentation's carrier and order, taken FLAT as the two
        -- fields CodedCompletion.Presentation:202-208 declares. Rule 2b as K6's
        -- Track A refined it: a module parameter is maximally stuck and beats
        -- sealing, 1.05 s against 1.08 s. CodedCompletion.Coded and .Core are
        -- NOT applied in this file.
        (c o : S)
        -- Track A, flat. CCC₂ᴵ is opaque here: this file never looks inside it
        -- and takes exactly one use law, so no body can specialize the chain
        -- condition to one notion. That is the mechanical form of the T3 check.
        -- Verified against Track A's landed file, and the architecture's
        -- printed type was wrong: K7/ChainConditions.agda:305 ascribes
        -- CCC₁ᴵ CCC₂ᴵ CCC₃ᴵ : S → S → S → Ω, carrier and order EXPLICIT, not
        -- architecture 2.2's S → Ω with them as module parameters; and the
        -- use law for CCC₂ is spelled ccc-use, not ccc₂-use
        -- (K7/ChainConditions.agda:346-348, whose conclusion is
        -- ⟨ injectable d v ⟩ and not ⟨ countableΔ v d ⟩, the two being the
        -- same term by :265-266). Rule 14: the measurement wins. The use law
        -- below is Track A's at this file's own c and o.
        (subsetΔ    : S → S → Ω)
        (antichainΔ : S → S → S → Ω)
        (maximalΔ   : S → S → S → Ω)
        (CCC₁ᴵ      : S → S → S → Ω)
        (CCC₂ᴵ      : S → S → S → Ω)
        (ccc-use    : (w d : S) → ⟨ CCC₂ᴵ c o w ⟩
                    → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
                    → ⟨ CBᴳ.injectable d w ⟩)
        (ccc₁-use   : (w d : S) → ⟨ CCC₁ᴵ c o w ⟩
                    → ⟨ subsetΔ d c ⟩ → ⟨ maximalΔ c o d ⟩
                    → ⟨ CBᴳ.injectable d w ⟩)
        -- Ground injectability composition is supplied from CardinalOrder at
        -- the ground profile. Keeping it flat avoids adding an unused pairing
        -- parameter to the preservation argument itself.
        (injectable-trans : Separation → Collection → (a b d : S)
                          → ⟨ CBᴳ.injectable a b ⟩ → ⟨ CBᴳ.injectable b d ⟩
                          → ⟨ CBᴳ.injectable a d ⟩)
        -- K5/K6 engine, ABSTRACT, in the shape of K6/Separation.agda:276-279.
        (forces   : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
        (truth-at : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
                  → (ν ⊨ᴱ φ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r φ ν))
        (_≤ᴾ_ : Cond → Cond → Ω)
        (forces-mono : ∀ {k} (r p : Cond) → ⟨ r ≤ᴾ p ⟩
                     → (φ : Formula Nm k) (ν : Vec Nm k)
                     → ⟨ forces p φ ν ⟩ → ⟨ forces r φ ν ⟩)
        (directed : (p q : Cond) → ⟨ G∈ p ⟩ → ⟨ G∈ q ⟩
                  → ⟨ ⋁ Cond (λ r → G∈ r ⊓ ((r ≤ᴾ p) ⊓ (r ≤ᴾ q))) ⟩)
        -- K5/Structures.agda:400-402, unconditional.
        (sat-cong : ∀ {k} (φ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                  → (ν ⊨ᴱ φ) ≡ (μ ⊨ᴱ φ))
        -- K6/Choice.agda:242 and K6/Elementary.agda:235, flat and unconditional.
        (≈-refl : (m : S) → ⟨ m ≈[G] m ⟩)
        -- K6 Track C, flat, at ⟨ positiveᴾ ⟩ alone.
        -- K6/GroundTransfer.agda:324-325, :411-413, :427-429. The K6 export
        -- spells the copy map at the CODE level, chk : S → S, and pairs it with
        -- chk-name to get groundName : S → Nm; groundName-code (:324-325) is
        -- refl, so `fst (chk y)` here and `chk y` there are the same term once
        -- this chk is instantiated at groundName. The architecture's brief and
        -- the source therefore agree; both spellings were checked.
        (chk          : S → Nm)
        (chk-mem←     : ⟨ positiveᴾ ⟩ → (a b : S) → ⟨ a ∈ˢ b ⟩
                      → ⟨ chk a ∈ᴱ chk b ⟩)
        (copy-members : ⟨ positiveᴾ ⟩ → (a : S) (τ : Nm) → ⟨ τ ∈ᴱ chk a ⟩
                      → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ ≈[G] fst (chk y))) ⟩)
        -- K6 Track H, flat, and it is a PATH. K6/Ordinals.agda:179-180.
        (chk-ordinal : (a : S) → ((chk a ∷ []) ⊨ᴱ CBᴱ.IsOrdinalφ)
                               ≡ ((a ∷ []) ⊨ᴳ CBᴳ.IsOrdinalφ))
        -- Track E, flat. The value formula, verified against the landed file:
        -- valueFo : Nm → Formula Nm 2 (K7/PossibleValues.agda:174-175), whose
        -- reading at the extension (:238-241, refl) is "the Kuratowski pair of
        -- the two arguments belongs to f", so the FIRST slot is the argument
        -- and the SECOND is the value. The possible-value operator itself
        -- arrives one module down, at module AtBound, because Track E binds its
        -- bound as a module parameter rather than as an argument; see the note
        -- there. The single named residue inside it is O7's valΔ, consolidated
        -- by O7/Supply.agda's module Chain; this file never names it, because
        -- the universal property is the only thing the argument reads.
        (valueFo : Nm → Formula Nm 2)
        -- Track B, flat: the surjection vocabulary CardinalBridge does not have
        -- (Q6 assigns it to K7/CardinalOrder.agda) read at the EXTENSION, plus
        -- the single elimination law the argument uses. Taking the elimination
        -- rather than the predicate's body is rule 13: the hypothesis is what
        -- the layer must export, not what a design document draws.
        (isSurjectionᴱ : Nm → Nm → Nm → Ω)
        (onto : (f a b : Nm) → ⟨ isSurjectionᴱ f a b ⟩ → (y : Nm) → ⟨ y ∈ᴱ b ⟩
              → ⟨ ⋁ Nm (λ x → (x ∈ᴱ a) ⊓ ((x ∷ y ∷ []) ⊨ᴱ valueFo f)) ⟩)
        (surjection-function : (f a b : Nm) → ⟨ isSurjectionᴱ f a b ⟩
                             → ⟨ CBᴱ.isFunction f ⟩)
        where

        ----------------------------------------------------------------------
        -- PART 1. THE REDUCTION, AND IT IS THE HEADLINE
        ----------------------------------------------------------------------

        -- Architecture 2.6 calls this the single most important mathematical
        -- finding of the K7 reading, and it is proved here rather than assumed.
        -- CBᴱ.isCardinal (chk κ) unfolds (CardinalBridge.agda:553-556) to
        --
        --   isOrdinal (chk κ) ⊓ ⋀ Nm (λ β → (β ∈ᴱ chk κ) ⇒ ¬ injectable (chk κ) β)
        --
        -- whose outer quantifier is BOUNDED by chk κ. copy-members collapses a
        -- bounded quantifier over names to one over ground members, so the whole
        -- statement reduces to a family of ground-indexed obligations. No rank,
        -- no NoNewOrdinals, no filter law and no LEM is spent anywhere in Part 1.

        -- Congruence of the extension's injectability in its second argument,
        -- along value equality. It is not congruence of a host predicate: the
        -- route is through the FORMULA, so the only law used is sat-cong, and
        -- the bridge at either end is CardinalBridge's own.

        inj-cong : (κ y : S) (β : Nm) → ⟨ fst β ≈[G] fst (chk y) ⟩
                 → ⟨ CBᴱ.injectable (chk κ) β ⟩
                 → ⟨ CBᴱ.injectable (chk κ) (chk y) ⟩
        inj-cong κ y β e h =
          subst ⟨_⟩ (CBᴱ.Injectable-bridge (chk κ) (chk y))
            (subst ⟨_⟩
              (sat-cong CBᴱ.Injectableφ (chk κ ∷ β ∷ []) (chk κ ∷ chk y ∷ []) agr)
              (subst ⟨_⟩ (sym (CBᴱ.Injectable-bridge (chk κ) β)) h))
          where
            agr : Agree (chk κ ∷ β ∷ []) (chk κ ∷ chk y ∷ [])
            agr zero       = ≈-refl (fst (chk κ))
            agr (suc zero) = e

        -- Ordinality goes up for free, because chk-ordinal is a path and the
        -- two bridges are refl at both structures.

        ordinal-up : (κ : S) → ⟨ CBᴳ.isOrdinal κ ⟩ → ⟨ CBᴱ.isOrdinal (chk κ) ⟩
        ordinal-up κ h =
          subst ⟨_⟩ (CBᴱ.IsOrdinal-bridge (chk κ))
            (subst ⟨_⟩ (sym (chk-ordinal κ))
              (subst ⟨_⟩ (sym (CBᴳ.IsOrdinal-bridge κ)) h))

        -- The ground-indexed residue: everything the cardinality of chk κ at
        -- the extension still owes, after the reduction has done its work.
        -- Its quantifier ranges over y : S bounded by κ, a ground SET.

        GroundResidue : S → Type ℓ
        GroundResidue κ =
          (y : S) → ⟨ y ∈ˢ κ ⟩ → ⟨ CBᴱ.injectable (chk κ) (chk y) ⟩ → ⟨ ⊥ ⟩

        cardinal-reduce : ⟨ positiveᴾ ⟩ → (κ : S) → ⟨ CBᴳ.isOrdinal κ ⟩
                        → GroundResidue κ → ⟨ CBᴱ.isCardinal (chk κ) ⟩
        cardinal-reduce pos κ hord res = ordinal-up κ hord , second
          where
            second : (β : Nm) → ⟨ β ∈ᴱ chk κ ⟩
                   → ⟨ CBᴱ.injectable (chk κ) β ⟩ → Empty.⊥
            second β hβ hinj =
              PT.rec Empty.isProp⊥
                (λ { (y , hy , e) →
                     Empty.rec* (res y hy (inj-cong κ y β e hinj)) })
                (copy-members pos κ β hβ)

        ----------------------------------------------------------------------
        -- PART 2. SPREADING, AND THE COORDINATE-BY-COORDINATE COVERING
        ----------------------------------------------------------------------

        -- "f spreads κ over β": every ground member of κ is a value of f, in
        -- the extension, at the check name of some ground member of β. This is
        -- the ONE notion the counting argument consumes, and stating it
        -- separately is what keeps the theorem out of T3: nothing about how the
        -- spreading arose survives into Part 3.

        spreadΩ : Nm → S → S → Ω
        spreadΩ f β κ =
          ⋀ S (λ a → (a ∈ˢ κ) ⇒
            ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ ((chk ξ ∷ chk a ∷ []) ⊨ᴱ valueFo f)))

        -- A surjection of chk β onto chk κ spreads κ over β. Two steps and no
        -- more: copy-members pulls the preimage name down to a ground member of
        -- β, and sat-cong moves the value statement onto that member's check
        -- name. Both are at ⟨ positiveᴾ ⟩ alone.

        onto→spread : ⟨ positiveᴾ ⟩ → (f : Nm) (β κ : S)
                    → ⟨ isSurjectionᴱ f (chk β) (chk κ) ⟩ → ⟨ spreadΩ f β κ ⟩
        onto→spread pos f β κ hs a ha =
          PT.rec (snd tgt)
            (λ { (x , hx , hv) →
               PT.rec (snd tgt)
                 (λ { (ξ , hξ , e) →
                    ∣ ξ , hξ
                    , subst ⟨_⟩
                        (sat-cong (valueFo f) (x ∷ chk a ∷ [])
                                  (chk ξ ∷ chk a ∷ []) (agr x ξ e)) hv
                    ∣₁ })
                 (copy-members pos β x hx) })
            (onto f (chk β) (chk κ) hs (chk a) (chk-mem← pos a κ ha))
          where
            tgt : Ω
            tgt = ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ ((chk ξ ∷ chk a ∷ []) ⊨ᴱ valueFo f))

            agr : (x : Nm) (ξ : S) → ⟨ fst x ≈[G] fst (chk ξ) ⟩
                → Agree (x ∷ chk a ∷ []) (chk ξ ∷ chk a ∷ [])
            agr x ξ e zero       = e
            agr x ξ e (suc zero) = ≈-refl (fst (chk a))

        ----------------------------------------------------------------------
        -- PART 3. THE GROUND BOUND, AT TRACK E'S OWN SHAPE
        ----------------------------------------------------------------------

        -- Track E separates the possible values below a specified condition p
        -- inside the ground bound κ. The condition is shared with the forcing
        -- assertion of functionality in the antichain obligation. Collection
        -- is not needed for each separated value set; collecting the family
        -- remains the separate FamilySet obligation below.

        module AtBound
          (κ : S)
          (valuesOf      : Separation → (p : Cond) → (f : Nm) (ξ : S) → S)
          (valuesOf-spec : (sep : Separation) (p : Cond) (f : Nm) (ξ a : S)
                         → (a ∈ˢ valuesOf sep p f ξ)
                           ≡ ((a ∈ˢ κ)
                              ⊓ ⋁ Cond (λ r →
                                  (r ≤ᴾ p) ⊓ forces r (valueFo f) (chk ξ ∷ chk a ∷ []))))
          where

          -- Truth gives q ∈ G forcing an actual value. Since p also lies in G,
          -- directedness supplies r ∈ G below both p and q. Monotonicity moves
          -- the value assertion from q to r, placing it in the local value set.

          covering : (sep : Separation) (p : Cond) → ⟨ G∈ p ⟩
                   → (f : Nm) (β : S)
                   → ⟨ spreadΩ f β κ ⟩
                   → (a : S) → ⟨ a ∈ˢ κ ⟩
                   → ⟨ ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (a ∈ˢ valuesOf sep p f ξ)) ⟩
          covering sep p hp f β sp a ha =
            PT.rec (snd tgt)
              (λ { (ξ , hξ , hsat) →
                 PT.rec (snd tgt)
                   (λ { (q , hq , hf) →
                      PT.rec (snd tgt)
                        (λ { (r , _ , hrp , hrq) →
                           ∣ ξ , hξ
                           , subst ⟨_⟩ (sym (valuesOf-spec sep p f ξ a))
                               (ha , ∣ r , hrp
                                 , forces-mono r q hrq (valueFo f)
                                     (chk ξ ∷ chk a ∷ []) hf ∣₁)
                           ∣₁ })
                        (directed p q hp hq) })
                   (subst ⟨_⟩ (truth-at (valueFo f) (chk ξ ∷ chk a ∷ [])) hsat) })
              (sp a ha)
            where
              tgt : Ω
              tgt = ⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (a ∈ˢ valuesOf sep p f ξ))

          --------------------------------------------------------------------
          -- PART 4. THE CHAIN CONDITION, SPENT, AND WHICH OF THE THREE
          --------------------------------------------------------------------

          -- The single place a chain condition enters the whole argument, and
          -- it enters through ONE named interface so that a reader can see
          -- exactly what is being assumed and at which of the three predicates.

          CountableValues : S → Type ℓ
          CountableValues w =
            (sep : Separation) (p : Cond) (f : Nm)
            → ⟨ forces p CBᴱ.IsFunctionφ (f ∷ []) ⟩ → (ξ : S)
            → ⟨ CBᴳ.injectable (valuesOf sep p f ξ) w ⟩

          -- The step of the classical proof that genuinely wants M's choice,
          -- isolated and named. Bell 2005, Lemma 4.3's route
          -- (bell-2005-boolean-valued-models.fulltext.md:4978-4983): for each
          -- possible value pick a condition deciding it; two conditions
          -- deciding distinct values of the same function at the same argument
          -- have no common refinement below p, where p forces functionality.
          -- All selected conditions lie below that same p, so they form an
          -- antichain and the possible-value set injects into it. "Pick" is the
          -- whole ledger question (roadmap:213) and Track C owns it: picked by
          -- the lt-least member of a ground set under M's own well ordering it
          -- is a theorem of M, picked by a host function S → S it is the
          -- forbidden choiceless transfer. THIS FILE TAKES NEITHER AND NAMES
          -- THE OBLIGATION.
          --
          -- Which of Track D's two structural protections this file relies on:
          -- the SIBLING ARRANGEMENT. ValueAntichain is a top-level type of this
          -- module and no selection, well ordering or least-element operator is
          -- in scope anywhere below, so nothing in the mathematics here can
          -- manufacture one. GroundWellOrder does not occur in this file.

          ValueAntichain : Type ℓ
          ValueAntichain =
            (sep : Separation) (p : Cond) (f : Nm)
            → ⟨ forces p CBᴱ.IsFunctionφ (f ∷ []) ⟩ → (ξ : S)
            → ⟨ ⋁ S (λ d → ((subsetΔ d c) ⊓ antichainΔ c o d)
                 ⊓ CBᴳ.injectable (valuesOf sep p f ξ) d) ⟩

          -- The same obligation strengthened to a MAXIMAL antichain, which is
          -- the form that lets the theorem run off CCC₁ instead of CCC₂. Track
          -- A measured that CCC₁ is the WEAKEST of the three, so this route
          -- assumes strictly less about the notion; its price is that the
          -- deciding antichain must be extended to a maximal one, which is
          -- Track C's MaximalExtension (K7/ChainConditions.agda:445-447) and
          -- has no supplier in this tree. Both routes are shipped and neither
          -- is preferred here.

          ValueMaximalAntichain : Type ℓ
          ValueMaximalAntichain =
            (sep : Separation) (p : Cond) (f : Nm)
            → ⟨ forces p CBᴱ.IsFunctionφ (f ∷ []) ⟩ → (ξ : S)
            → ⟨ ⋁ S (λ d → ((subsetΔ d c) ⊓ maximalΔ c o d)
                 ⊓ CBᴳ.injectable (valuesOf sep p f ξ) d) ⟩

          -- CCC₂: every antichain is countable. This is the route the deciding
          -- antichain of ValueAntichain takes, because that antichain is an
          -- arbitrary one: nothing in its construction makes it maximal or
          -- predense. Track A's AntichainAtEmpty.agda-break (exit 0) records
          -- the price of CCC₂'s weaker hypothesis: the empty coded set is an
          -- antichain with zero hypotheses spent, so it sits inside CCC₂'s
          -- hypothesis and outside CCC₁'s and CCC₃'s.

          countable-from-ccc₂ : ValueAntichain → (coll : Collection)
                              → (w : S) → ⟨ CCC₂ᴵ c o w ⟩ → CountableValues w
          countable-from-ccc₂ va coll w hccc sep p f hf ξ =
            PT.rec (snd tgt)
              (λ { (d , (hsub , hac) , hinj) →
                   injectable-trans sep coll (valuesOf sep p f ξ) d w hinj
                     (ccc-use w d hccc hsub hac) })
              (va sep p f hf ξ)
            where
              tgt : Ω
              tgt = CBᴳ.injectable (valuesOf sep p f ξ) w

          -- CCC₁: every MAXIMAL antichain is countable. Weakest of the three,
          -- hence the strongest theorem, at the cost of the stronger deciding
          -- obligation above.

          countable-from-ccc₁ : ValueMaximalAntichain → (coll : Collection)
                              → (w : S) → ⟨ CCC₁ᴵ c o w ⟩ → CountableValues w
          countable-from-ccc₁ va coll w hccc sep p f hf ξ =
            PT.rec (snd tgt)
              (λ { (d , (hsub , hmx) , hinj) →
                   injectable-trans sep coll (valuesOf sep p f ξ) d w hinj
                     (ccc₁-use w d hccc hsub hmx) })
              (va sep p f hf ξ)
            where
              tgt : Ω
              tgt = CBᴳ.injectable (valuesOf sep p f ξ) w

          --------------------------------------------------------------------
          -- PART 5. THE GROUND ARITHMETIC, AND THE EXACT RANGE
          --------------------------------------------------------------------

          -- The family as a SET, which is the proper-class trap's answer. F is
          -- a ground set that collects the β-indexed family of possible-value
          -- sets, with the biconditional in both directions so that nothing
          -- outside the family sneaks in. Suppliers, named: Collection through
          -- GroundDescription.hasImage′ (:182-186) for the image, and M's well
          -- ordering through Track D's Well.leastOf
          -- (K7/CompletionTransfer.agda:100-110) for the injection F into β,
          -- which is unique choice by a proved-unique least element and not
          -- choice.

          FamilySet : Type ℓ
          FamilySet =
            (sep : Separation) (p : Cond) (f : Nm) (β : S)
            → ⟨ ⋁ S (λ F → (CBᴳ.injectable F β)
                 ⊓ ⋀ S (λ v → iff (v ∈ˢ F)
                      (⋁ S (λ ξ → (ξ ∈ˢ β) ⊓ (v ≈ˢ valuesOf sep p f ξ))))) ⟩

          -- THE EXACT RANGE, AS A PREDICATE AND NOT A PROMISE (roadmap:215).
          -- Read the quantifiers: β, F, v and a all range over S, a ground set.
          -- There is no host predicate, no host family and no index type here,
          -- so the statement is a sentence about M and a reviewer checks it by
          -- reading it. K7/breaks/HostFamilyRange.agda-break is the poisoned
          -- variant, which typechecks at exit 0 and is shorter, and it is the
          -- measurement that this discipline is carried by the binder alone.
          -- In words: for no β ∈ κ is κ covered by a family of at most β-many
          -- w-countable ground sets.
          --
          -- This is a theorem of ZFC in the ground for EVERY cardinal κ with
          -- ω ∈ κ, singular ones included, because a union of at most |β| many
          -- countable sets has size at most max(|β|, ω) < κ. It is class (ii)
          -- here: the ordinary profile has no ordinal arithmetic, no Hartogs
          -- construction and no transfinite recursion (measured:
          -- OrdinaryProfile declares iff, the eight axiom types, the two
          -- records, PathRealization, MinimalElement, TransitiveClosure,
          -- MinimalForm, foundation→minimal, minimal→foundation, Swap and
          -- hasImage, and nothing else). So it is an ARGUMENT here and its
          -- range is stated rather than promised.

          ProvedRange : S → Ω
          ProvedRange w =
            ⋀ S (λ β → (β ∈ˢ κ) ⇒
            ⋀ S (λ F →
                 (  (CBᴳ.injectable F β)
                  ⊓ ((⋀ S (λ v → (v ∈ˢ F) ⇒ CBᴳ.injectable v w))
                  ⊓ (⋀ S (λ a → (a ∈ˢ κ) ⇒
                       ⋁ S (λ v → (v ∈ˢ F) ⊓ (a ∈ˢ v))))))
               ⇒ ⊥))

          -- Ruling Q7's mandatory ledger row, in type form. Transcribed and NOT
          -- inhabited in this file: no inhabitant of this statement exists in
          -- the programme, K7 does not build one, and the owner is K8 or a K1
          -- addendum. A parametric theorem with a named unwitnessed hypothesis
          -- is a result; the same theorem without this row is K5 Track J's
          -- failure.

          ProvedRangeHolds : Type ℓ
          ProvedRangeHolds =
            (w : S) → ⟨ CBᴳ.isOmega w ⟩ → ⟨ CBᴳ.isCardinal κ ⟩ → ⟨ w ∈ˢ κ ⟩
            → ⟨ ProvedRange w ⟩

          --------------------------------------------------------------------
          -- PART 6. THE PRESERVATION THEOREMS
          --------------------------------------------------------------------

          -- A function forced at a common condition in G cannot spread a ground
          -- cardinal in the proved range over a smaller ground set. Both the
          -- possible-value family and its countability use that same condition.

          no-spread : FamilySet → (sep : Separation)
                    → (w β : S) → ⟨ β ∈ˢ κ ⟩
                    → CountableValues w → ⟨ ProvedRange w ⟩
                    → (p : Cond) → ⟨ G∈ p ⟩ → (f : Nm)
                    → ⟨ forces p CBᴱ.IsFunctionφ (f ∷ []) ⟩
                    → ⟨ spreadΩ f β κ ⟩ → ⟨ ⊥ ⟩
          no-spread fs sep w β hβ cv hpr p hp f hf sp =
            PT.rec (snd ⊥)
              (λ { (F , hFβ , hFiff) →
                 hpr β hβ F
                   ( hFβ
                   , (λ v hv →
                        PT.rec (snd (CBᴳ.injectable v w))
                          (λ { (ξ , _ , hveq) →
                             subst (λ u → ⟨ CBᴳ.injectable u w ⟩)
                               (sym (≈ˢ-to-path v (valuesOf sep p f ξ) hveq))
                               (cv sep p f hf ξ) })
                          (fst (hFiff v) hv))
                   , (λ a ha →
                        PT.map
                          (λ { (ξ , hξ , hav) →
                               valuesOf sep p f ξ
                             , snd (hFiff (valuesOf sep p f ξ))
                                 ∣ ξ , hξ
                                 , path-to-≈ˢ (valuesOf sep p f ξ)
                                              (valuesOf sep p f ξ) refl ∣₁
                             , hav })
                          (covering sep p hp f β sp a ha)) ) })
              (fs sep p f β)

          -- Truth supplies one condition of G forcing actual functionality.
          -- No condition outside G, and no universal forcing assertion about f,
          -- is needed to start the local covering argument.

          no-functional-spread : FamilySet → (sep : Separation)
                               → (w β : S) → ⟨ β ∈ˢ κ ⟩
                               → CountableValues w → ⟨ ProvedRange w ⟩
                               → (f : Nm) → ⟨ CBᴱ.isFunction f ⟩
                               → ⟨ spreadΩ f β κ ⟩ → ⟨ ⊥ ⟩
          no-functional-spread fs sep w β hβ cv hpr f hf sp =
            PT.rec (snd ⊥)
              (λ { (p , hp , hforce) →
                 no-spread fs sep w β hβ cv hpr p hp f hforce sp })
              (subst ⟨_⟩ (truth-at CBᴱ.IsFunctionφ (f ∷ []))
                (subst ⟨_⟩ (sym (CBᴱ.IsFunction-bridge f)) hf))

          -- NO COLLAPSING SURJECTION. The roadmap's first named exclusion, and
          -- the public form of the theorem: under the chain condition, no name
          -- is a surjection of the copy of a smaller ground set onto the copy
          -- of a ground cardinal in the proved range.
          --
          -- Read the type. CCC₂ᴵ c o w is Track A's predicate at this file's
          -- own carrier and order, and it is a HYPOTHESIS: nothing in the body
          -- looks inside it and no instance of it is built anywhere in the
          -- file. That is the whole of the T3 protection and the seam probe
          -- K7/PreserveAtTracks.agda pins it to Track A's real export.

          no-onto : FamilySet → ValueAntichain
                  → (coll : Collection) (sep : Separation) → ⟨ positiveᴾ ⟩
                  → (w β : S) → ⟨ β ∈ˢ κ ⟩
                  → ⟨ CCC₂ᴵ c o w ⟩ → ⟨ ProvedRange w ⟩
                  → (f : Nm) → ⟨ isSurjectionᴱ f (chk β) (chk κ) ⟩ → ⟨ ⊥ ⟩
          no-onto fs va coll sep pos w β hβ hccc hpr f hs =
            no-functional-spread fs sep w β hβ
              (countable-from-ccc₂ va coll w hccc) hpr f
              (surjection-function f (chk β) (chk κ) hs)
              (onto→spread pos f β κ hs)

          -- The same at the weakest of the three chain conditions.

          no-onto-via-ccc₁ : FamilySet → ValueMaximalAntichain
                           → (coll : Collection) (sep : Separation)
                           → ⟨ positiveᴾ ⟩
                           → (w β : S) → ⟨ β ∈ˢ κ ⟩
                           → ⟨ CCC₁ᴵ c o w ⟩ → ⟨ ProvedRange w ⟩
                           → (f : Nm) → ⟨ isSurjectionᴱ f (chk β) (chk κ) ⟩
                           → ⟨ ⊥ ⟩
          no-onto-via-ccc₁ fs va coll sep pos w β hβ hccc hpr f hs =
            no-functional-spread fs sep w β hβ
              (countable-from-ccc₁ va coll w hccc) hpr f
              (surjection-function f (chk β) (chk κ) hs)
              (onto→spread pos f β κ hs)

          -- The bridge from the INJECTION form, which is the form
          -- CardinalBridge's isCardinal is stated in
          -- (CardinalBridge.agda:553-556 reads "κ does not inject into any
          -- β ∈ κ"), to the covering form the counting argument runs on.
          --
          -- THIS IS THE ONE PLACE THE ARGUMENT CROSSES BETWEEN AN INJECTION AND
          -- A MAP ONTO, AND IT IS NAMED RATHER THAN USED. Zero theorems in this
          -- tree relate Track A's injection countability (countableΔ w d =
          -- injectable d w, K7/ChainConditions.agda:265-266) to Track B's
          -- surjection form (surjectable, K7/CardinalOrder.agda:228-229),
          -- measured, so any crossing is a new obligation and not a lemma. This
          -- file has exactly one and it is below.
          --
          -- At a genuine extension it is not class (iii): the extension models
          -- ZFC, and in any case the hypothesis is exactly what the theorem
          -- goes on to refute, so no genuine Cohen extension falsifies it. It
          -- is class (ii) here because the extension's own Separation and LEM
          -- are not parameters of this file.

          InverseSpread : Type ℓ
          InverseSpread =
            (y : S) → ⟨ y ∈ˢ κ ⟩ → ⟨ CBᴱ.injectable (chk κ) (chk y) ⟩
            → ⟨ ⋁ Nm (λ g → isSurjectionᴱ g (chk y) (chk κ)) ⟩

          residue-from-ccc : FamilySet → InverseSpread → (sep : Separation)
                           → ⟨ positiveᴾ ⟩
                           → (w : S) → CountableValues w → ⟨ ProvedRange w ⟩
                           → GroundResidue κ
          residue-from-ccc fs isp sep pos w cv hpr y hy hinj =
            PT.rec (snd ⊥)
              (λ { (g , hs) →
                 no-functional-spread fs sep w y hy cv hpr g
                   (surjection-function g (chk y) (chk κ) hs)
                   (onto→spread pos g y κ hs) })
              (isp y hy hinj)

          -- THE PRESERVATION THEOREM. A ground cardinal in the proved range is
          -- still a cardinal at the extension. Parametric over the presentation
          -- (c, o), over the notion (Cond, G∈), over the ground cardinal κ and
          -- over the countability witness w; the chain condition is a
          -- hypothesis throughout and appears nowhere as an instance.

          no-collapse : FamilySet → ValueAntichain → InverseSpread
                      → (coll : Collection) (sep : Separation) → ⟨ positiveᴾ ⟩
                      → (w : S) → ⟨ CBᴳ.isOrdinal κ ⟩
                      → ⟨ CCC₂ᴵ c o w ⟩ → ⟨ ProvedRange w ⟩
                      → ⟨ CBᴱ.isCardinal (chk κ) ⟩
          no-collapse fs va isp coll sep pos w hord hccc hpr =
            cardinal-reduce pos κ hord
              (residue-from-ccc fs isp sep pos w
                (countable-from-ccc₂ va coll w hccc) hpr)

          no-collapse-via-ccc₁ : FamilySet → ValueMaximalAntichain
                               → InverseSpread
                               → (coll : Collection) (sep : Separation)
                               → ⟨ positiveᴾ ⟩
                               → (w : S) → ⟨ CBᴳ.isOrdinal κ ⟩
                               → ⟨ CCC₁ᴵ c o w ⟩ → ⟨ ProvedRange w ⟩
                               → ⟨ CBᴱ.isCardinal (chk κ) ⟩
          no-collapse-via-ccc₁ fs va isp coll sep pos w hord hccc hpr =
            cardinal-reduce pos κ hord
              (residue-from-ccc fs isp sep pos w
                (countable-from-ccc₁ va coll w hccc) hpr)

          -- The same theorem with the range carried by its own hypothesis, so
          -- that the statement reads as architecture 2.6 prints it: given a
          -- ground ω, a ground cardinal above it, and the chain condition, the
          -- copy of the cardinal is a cardinal. isOmega and w ∈ˢ κ are consumed
          -- HERE, by ProvedRangeHolds, and nowhere else; they are the
          -- conditions under which the range predicate is true, not steps of
          -- the proof, and rule 13 says to show that rather than to carry them
          -- unused through every lemma.

          no-collapse-in-range : FamilySet → ValueAntichain → InverseSpread
                               → ProvedRangeHolds
                               → (coll : Collection) (sep : Separation)
                               → ⟨ positiveᴾ ⟩
                               → (w : S) → ⟨ CBᴳ.isOmega w ⟩
                               → ⟨ CBᴳ.isCardinal κ ⟩ → ⟨ w ∈ˢ κ ⟩
                               → ⟨ CCC₂ᴵ c o w ⟩
                               → ⟨ CBᴱ.isCardinal (chk κ) ⟩
          no-collapse-in-range fs va isp prh coll sep pos w hw hκ hwκ hccc =
            no-collapse fs va isp coll sep pos w (fst hκ) hccc
              (prh w hw hκ hwκ)

          --------------------------------------------------------------------
          -- PART 7. THE BOUNDARY, TRANSCRIBED AND NOT INHABITED
          --------------------------------------------------------------------

          -- Ruling Q4. Cofinality is NOT this track's and this file makes no
          -- claim about it. The statement below is the cofinality exclusion the
          -- roadmap names beside the surjection one, written in the vocabulary
          -- this file has: no name sends a smaller ground set to a family of
          -- values cofinal in κ. It is shipped with NO INHABITANT.
          --
          -- The gap is mathematical, not clerical. no-spread refutes a
          -- COVERING: its ProvedRange hypothesis speaks of a family whose union
          -- contains κ. A cofinal range need not contain any given member of κ,
          -- only lie unboundedly below it, so no instantiation of no-spread
          -- reaches this type. Closing it is Bell 1.51(iv), which invokes the
          -- Maximum Principle by name; MaximumPrinciple
          -- (K4/Witnesses.agda:858-861) is uninhabited and
          -- k4-architecture.md:998 refuses K7 by name.

          NotClaimed-Regularity : Type ℓ
          NotClaimed-Regularity =
            (β : S) → ⟨ CBᴳ.isCardinal κ ⟩ → ⟨ β ∈ˢ κ ⟩ → (f : Nm)
            → ⟨ ⋀ S (λ a → (a ∈ˢ κ) ⇒
                  ⋁ S (λ ξ → (ξ ∈ˢ β)
                     ⊓ ⋁ S (λ b → ((b ∈ˢ κ) ⊓ ((a ∈ˢ b) ⊔ (a ≈ˢ b)))
                          ⊓ ((chk ξ ∷ chk b ∷ []) ⊨ᴱ valueFo f)))) ⟩
            → ⟨ ⊥ ⟩
