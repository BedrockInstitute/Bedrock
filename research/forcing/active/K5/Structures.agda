{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track F: the extension structures, and the copy of the ground inside
-- them.
--
-- WHAT THIS FILE IS ABOUT. K3 built a RELATION: two codes have the same value
-- at a filter G when their active entries match, in value, on both sides
-- (Valuation.agda:285, :294). That is a relation on S, and a relation on S is
-- not a model of anything. This file asks the one question that can be
-- answered before the quotient exists: what STRUCTURE do the names carry,
-- taken as they are, with the value relation as the structure's own equality?
--
-- The answer is that the four fields of ZFStructure are exactly available
-- (src/FOL/ZFStructure.lagda.md:64-71) and nothing else has to be invented.
-- The carrier is the names, the equality is _≈[G]_, the membership is _∈[G]_,
-- and satisfaction of the whole first order language follows by re-export
-- from src/FOL/Semantics.lagda.md:113-124, all ten clauses, with the ten
-- clauses of the SAME truth algebra the ground uses. The book's own prose at
-- ZFStructure.lagda.md fixes that this is what the record exists for: "in the
-- forcing part of the book, equality and membership will be a mutually
-- defined pair of graded relations, genuine content of the model that no
-- meta-level equality could supply".
--
-- ---------------------------------------------------------------------
-- THE BOUNDARY. WHAT A STRUCTURE IS AND WHAT A MODEL IS
-- ---------------------------------------------------------------------
--
-- Trap T-F1 and the sharpest line in this track. K3 also wrote down what a
-- VALUATION would be, as a record with a carrier and a map from names into it
-- (Valuation.agda:683-691). One of its four fields, val-eq, demands
--
--     val-eq : (τ σ : Name) → (val τ ≡ val σ) ≃ ⟨ code τ ≈[G] code σ ⟩
--
-- that the carrier's HOST PATH EQUALITY be the value relation. Nothing in this
-- file, and nothing K5 may build, has that property: Nm below is a Σ-type over
-- S, so two names with distinct codes are distinct points of it whatever their
-- values, and making them equal is a set quotient. The record is therefore
-- declared in this file as a Type and shipped with NO inhabitant, exactly as
-- K3 shipped it, and the type-level difference is visible in every signature
-- below:
--
--   * a statement about the VALUE RELATION has _≈[G]_ or _∈[G]_ : S → S → Ω
--     in it, and speaks of CODES;
--   * a statement about a STRUCTURE has ZFStructure (hPropAlgebra ℓ) or
--     _⊨_ : Vec Nm k → Formula Nm k → Ω in it, and speaks of the carrier Nm
--     with the value relation as its two fields;
--   * a statement about a MODEL would have a Carrier : Type ℓ with a val into
--     it and a path in that carrier. There is no such statement in this file.
--
-- K3's REPORT-I section 2 measured the exact cost and the reading that goes
-- with it: the record is inhabitable in eight lines the moment
-- Cubical.HITs.SetQuotients is imported, val-onto being []surjective and
-- val-eq being effective at the equivalence relation _≈[G]_. So the absence of
-- an inhabitant is a SCOPING RULE with a named owner, and NOT an unsolved
-- problem. What genuinely does not exist before genericity is a valuation into
-- anything that behaves like a set: Bell makes well-foundedness of the
-- quotient membership equivalent to genericity, so there is no collapse, no
-- transitive target and no reason to expect Foundation. That is K13's.
--
-- ---------------------------------------------------------------------
-- THE GROUND COPY, AND WHAT IT COSTS
-- ---------------------------------------------------------------------
--
-- Bell 1.23: the check map is a one-one map with x ∈ y ↔ ǎ x ∈ ǎ y. The record
-- GroundCopy below is that statement and nothing more, and it is the honest
-- reading of "the extension contains a copy of the ground": an ∈-monomorphism,
-- which is what Bell gets free, with no claim of ontoness and no claim of
-- elementarity.
--
-- MEASURED, and it is one hypothesis weaker than the architecture prints.
-- groundCopy takes ⟨ positive G ⟩. It does not take isFilter and it does not
-- take genericity, because K3 proved check-≈-inj (Valuation.agda:608) and
-- check-faithful (:611) inside module WithPositivity whose single parameter is
-- ⟨ positive G ⟩, and because K3's own file names positivity as the only
-- filter law any of its theorems consumes (:222-225). Since positive is a
-- predicate on an arbitrary Sub (ForcingNotion.agda:160-161), G need not be a
-- filter at all: it needs one condition in it. The isFilter form is shipped
-- below as a one-line corollary, so that the architecture's signature is
-- available and its over-charge is visible beside it.
--
-- ---------------------------------------------------------------------
-- SATISFACTION PRESERVATION, AND EXACTLY WHICH FORMULAS IT COVERS
-- ---------------------------------------------------------------------
--
-- groundSat below is Bell 1.23(v) on the poset side: for a Δ₀ formula and a
-- ground environment, the truth value of the formula in the extension
-- structure at the copied environment IS the truth value in the ground. It
-- covers, and covers only:
--
--     atoms (∈̇ and ≐), ∧̇, ∨̇, ⇒̇, ⊥̇, and the two BOUNDED quantifiers ∀̇∈, ∃̇∈,
--
-- over Formula S k, the ground's OWN language with its own sets as constants,
-- which is the alphabet exit item X6 words its Elementarity non-claim in.
--
-- The two unbounded quantifier nodes are unreachable, by absurd pattern on the
-- Δ₀ witness, and that is not a technicality: at ∃̇ the extension's join ranges
-- over EVERY name, including names with no ground counterpart, and the whole
-- point of forcing is that such a join can be true when the ground join is
-- false. Arbitrary formula elementarity is declared below as a Type with no
-- inhabitant, under the name Elementarity, and K5 does not claim it in any
-- form. The constraint is K2's and K4 owns the corresponding atomic and
-- bounded agreement on the Boolean side: a complete subalgebra inclusion
-- receives the JUSTIFIED atomic and bounded formula agreement rather than
-- arbitrary formula elementarity (K4/SubalgebraAgreement.agda:7-11), and the
-- justification there is atomic.
--
-- WHAT IS DIFFERENT ON THIS SIDE, and it is a measured negative against a
-- natural expectation. K4's Boolean side pays LEM ℓ and NONTRIVIALITY for the
-- same theorem (K4/CheckValues.agda:606, :821-829), because there the value
-- lives in an abstract Boolean algebra and a join of Boolean values is the top
-- only if some member is, which is exactly what two-valuedness has to supply.
-- Here both sides of the equation are truth values of the SAME algebra
-- hPropAlgebra ℓ, so every connective clause is a congruence and every
-- quantifier clause is a bijection of witnesses. groundSat is CONSTRUCTIVE and
-- needs no nontriviality: grep for LEM over this file returns 0.
--
-- ---------------------------------------------------------------------
-- THE LEDGER, WHICH IS THE MODULE TELESCOPE
-- ---------------------------------------------------------------------
--
-- module Kernel takes K3's seven name-kernel facts, verbatim from
-- Valuation.agda:148-156. module Side takes K3's four poset laws verbatim from
-- :201-205, plus a name recogniser and its hereditary clause. module Copy
-- takes K3's module Standard telescope verbatim from :493-503, plus the
-- validity of the check name. Nothing else.
--
-- NOT taken, and each absence is checkable: no Lattice field on the P side, no
-- Complement, no CodedComplete, no coded completion, no Presentation, no
-- Separation, no PowerSet, no Collection, no Choice of any kind, no LEM, no
-- isGeneric, no meets, no SetQuotients, no forcing relation, no Formula of the
-- ground appearing as a definability claim about the value relation.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import Valuation
import FOL.Semantics
import K4.Algebra
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K5.Structures {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Foundations.Prelude using ( funExt )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.Data.Sigma using ( _×_ ; _,_ )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open import FOL.Syntax
  using ( Term ; Formula ; con ; var
        ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ ; _⇒̇_ ; ⊥̇ ; ∃̇_ ; ∀̇_ ; ∀̇∈ ; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀ ; δ-∈ ; δ-≐ ; δ-∧ ; δ-∨ ; δ-⇒ ; δ-⊥ ; δ-∀∈ ; δ-∃∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm ; mapFo ; embed )

-- Track A's scope contract, one light application. Only the B side uses these,
-- and only for its order and its top (REPORT-A.md section 5, item A-3, records
-- that K4.Algebra is light for clause L2's reason: every argument is a
-- variable).

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ≤ᴮ-refl ; ⊆ˢ-trans ; Lattice )

-- The ground's own satisfaction, at the canonical constant interpretation. It
-- is the right hand side of every preservation statement below, and it is
-- named once so that no signature can confuse it with the extension's.

open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
module Gr = At S id

-- The ground's term evaluation, named in prefix form so that no signature
-- below carries a qualified mixfix bracket. A constant evaluates to the set it
-- names, a variable to its slot.

tmᴳ : ∀ {k} → Term S k → Vec S k → S
tmᴳ = Gr.⟦_⟧

-- K3's Conditions, which is a definition of the file and not of module Names,
-- so naming it here costs no module application (Valuation.agda:121-122).

private module VL = Valuation 𝒮
open VL using ( Conditions ; isSetConditions )

-- The compiler's input alphabet, the book's convention and K4's spelling
-- (K4/Compile.agda:499-500), kept so that a consumer of Track G can read this
-- file's statements in the same alphabet. groundSat below is stated one step
-- WIDER, over Formula S k: a formula of the ground's own language, constants
-- included, which is the alphabet exit item X6 words its non-claim in and the
-- alphabet in which "the ground's truths are the extension's truths" is a
-- sentence about the ground at all. Src k embeds into it by `embed`.

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

--------------------------------------------------------------------------------
-- The name kernel's interface
--------------------------------------------------------------------------------

-- Character for character from Valuation.agda:148-156 (clause L10). A drift in
-- any one of these seven makes the application below fail here rather than
-- pass silently.

module Kernel
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  where

  -- THE ONE HEAVY MODULE APPLICATION OF THIS FILE (rule 10). The value
  -- relation is K3's and K5 declares no second one (rule 9).

  private
    module VN = VL.Names entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec

  ----------------------------------------------------------------------------
  -- One side, instantiated twice
  ----------------------------------------------------------------------------

  -- K3's value relation is bi-instantiable and the architecture's section 1.8
  -- says so: the P side is (carrier, ≼ᶜ, G) and the B side is the SAME module
  -- at (B, ≤ᴮ, Uof G). Writing the structure once, at an abstract
  -- (carrierᶠ, ≼ᶠ), and instantiating it twice is what keeps rule 9 satisfied:
  -- there is one construction of a ZFStructure out of a value relation in the
  -- whole package.
  --
  -- The two parameters beyond K3's four are the name recogniser and its
  -- hereditary clause. Only the hereditary clause is used, and only once, in
  -- extensional below: an active entry of a name is a child of it
  -- (Valuation.agda:257) and a child of a name is a name
  -- (NameKernel.agda:470), which is what turns the structure's extensionality
  -- hypothesis, quantified over NAMES, into the code-level agreement
  -- value-extensional wants, quantified over all of S.

  module Side (carrierᶠ : S)
    (_≼ᶠ_      : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
    (≼ᶠ-refl   : (p : Conditions carrierᶠ) → ⟨ p ≼ᶠ p ⟩)
    (≼ᶠ-trans  : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶠ q ⟩ → ⟨ q ≼ᶠ r ⟩ → ⟨ p ≼ᶠ r ⟩)
    (inhabitedᶠ : ∥ Conditions carrierᶠ ∥₁)
    (IsNm       : S → Ω)
    (child-name : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ IsNm x ⟩)
    where

    private
      module VP = VN.Poset carrierᶠ _≼ᶠ_ ≼ᶠ-refl ≼ᶠ-trans inhabitedᶠ

    open VP public using ( Cond ; Sub ; _∈ᴾ_ ; positive ; isFilter ; filter-positive )

    -- The carrier of both extension structures. It is a Σ-type over S with a
    -- proof-irrelevant second component, so it is an h-set for the same reason
    -- S is, and it is definitionally K4's Fib IsNm (K4/ValueSets.agda:166-167)
    -- and K3's Name (NameKernel.agda:481-482). No fourth copy is declared.

    Nm : Type ℓ
    Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

    isSetNm : isSet Nm
    isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNm n))

    ----------------------------------------------------------------------------
    -- The extension structure at one subset of conditions
    ----------------------------------------------------------------------------

    module Ext (G : Sub) where

      open VP.Value G public
        using ( Active ; ‖Active‖ ; active-child ; active-value ; entry-value
              ; _≈[G]_ ; _∈[G]_ ; ≈-refl ; ≈-sym ; ≈-trans
              ; ≈-fwd ; ≈-bwd ; ≈-intro ; ≈-unfold-∈
              ; ∈-congˡ ; ∈-congʳ ; value-extensional )

      -- THE STRUCTURE. Four fields, all four available, none invented. The
      -- equality is the value relation and not a host path, which is the
      -- whole reason ZFStructure carries _≈ˢ_ as a field.

      structure : ZFStructure (hPropAlgebra ℓ)
      structure = record
        { S      = Nm
        ; isSetS = isSetNm
        ; _≈ˢ_   = λ σ τ → fst σ ≈[G] fst τ
        ; _∈ˢ_   = λ σ τ → fst σ ∈[G] fst τ }

      -- Satisfaction, by re-export. All ten clauses, at the same truth algebra
      -- the ground uses, with no translation layer. Nothing here is proved;
      -- the content is that the structure exists, and this line is what makes
      -- the content usable.

      private module SemS = FOL.Semantics (hPropAlgebra ℓ) structure
      module Sat = SemS.At Nm id
      open Sat public using ( _⊨_ ; ⟦_⟧ )

      -- The level claim of architecture section 1.8, machine checked rather
      -- than asserted: Nm : Type ℓ, so it fills the index slot of ⋁ and ⋀ and
      -- the two unbounded clauses are legal at this structure. Both are refl,
      -- and they are here to make the SLOT check, not to prove a theorem.

      sat-∃ : ∀ {k} (φ : Formula Nm (suc k)) (ν : Vec Nm k)
            → (ν ⊨ (∃̇ φ)) ≡ ⋁ Nm (λ σ → (σ ∷ ν) ⊨ φ)
      sat-∃ φ ν = refl

      sat-∀ : ∀ {k} (φ : Formula Nm (suc k)) (ν : Vec Nm k)
            → (ν ⊨ (∀̇ φ)) ≡ ⋀ Nm (λ σ → (σ ∷ ν) ⊨ φ)
      sat-∀ φ ν = refl

      ------------------------------------------------------------------------
      -- The one axiom K5 claims
      ------------------------------------------------------------------------

      -- Trap T-F3. OrdinaryZF has eight fields (OrdinaryProfile.agda:126-135).
      -- K5 claims ONE of them, here, and the other seven are K6's. The record
      -- itself is written below as a non-claim so that the count is checkable
      -- and not a promise in a comment.
      --
      -- The mathematics: value equality is ALREADY extensional on codes
      -- (Valuation.agda:456), so the structure's Extensionality costs nothing
      -- beyond turning a hypothesis quantified over NAMES into one quantified
      -- over codes. That turn is the only place child-name is spent.

      extensional : OrdinaryProfile.Extensionality structure
      extensional σ τ h = value-extensional (fst σ) (fst τ) pointwise
        where
          agree : (ρ : Nm) → (fst ρ ∈[G] fst σ) ≡ (fst ρ ∈[G] fst τ)
          agree = OrdinaryProfile.iff-to-spec structure σ τ h

          -- An active entry of a name is a name, so the hypothesis applies to
          -- it; and an active entry is a value-member of its own code.

          transfer : (m n : Nm) → ((ρ : Nm) → ⟨ fst ρ ∈[G] fst m ⟩ → ⟨ fst ρ ∈[G] fst n ⟩)
                   → (r : S) → ⟨ r ∈[G] fst m ⟩ → ⟨ r ∈[G] fst n ⟩
          transfer m n f r = PT.rec (snd (r ∈[G] fst n))
            (λ { (y , hy , e) →
                   ∈-congˡ (≈-sym e)
                     (f (y , child-name (fst m) (snd m) y (active-child y (fst m) hy))
                        (active-value hy)) })

          pointwise : (r : S) → (r ∈[G] fst σ) ≡ (r ∈[G] fst τ)
          pointwise r = ⇔toPath
            (transfer σ τ (λ ρ → subst ⟨_⟩ (agree ρ)) r)
            (transfer τ σ (λ ρ → subst ⟨_⟩ (sym (agree ρ))) r)

      ------------------------------------------------------------------------
      -- Satisfaction respects the value relation
      ------------------------------------------------------------------------

      -- The structure's equality is not a host path, so nothing about _⊨_ is
      -- automatic here: a substitution lemma has to be proved. It is the
      -- poset-side analogue of K4's val-subst (K4/CheckValues.agda:987-989) and it
      -- is what the two bounded quantifier clauses of groundSat consume, where
      -- an arbitrary name value-equal to a copied ground set has to be moved
      -- onto that copy.
      --
      -- Rule 1 is met by naming both endpoints of every congruence: the three
      -- helpers below exist so that no refl ever stands for an unchanged
      -- endpoint inside a congruence over a truth value operation.

      ⊓-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⊓ Q) ≡ (P' ⊓ Q')
      ⊓-cong p q = cong₂ _⊓_ p q

      ⊔-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⊔ Q) ≡ (P' ⊔ Q')
      ⊔-cong p q = cong₂ _⊔_ p q

      ⇒-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⇒ Q) ≡ (P' ⇒ Q')
      ⇒-cong p q = cong₂ _⇒_ p q

      Agree : ∀ {k} → Vec Nm k → Vec Nm k → Type ℓ
      Agree {k} ν μ = (ix : Fin k) → ⟨ fst (lookup ix ν) ≈[G] fst (lookup ix μ) ⟩

      agree-cons : ∀ {k} {ν μ : Vec Nm k} → Agree ν μ → (σ : Nm) → Agree (σ ∷ ν) (σ ∷ μ)
      agree-cons ag σ zero     = ≈-refl (fst σ)
      agree-cons ag σ (suc ix) = ag ix

      agree-refl : ∀ {k} (ν : Vec Nm k) → Agree ν ν
      agree-refl ν ix = ≈-refl (fst (lookup ix ν))

      private
        tm-agree : ∀ {k} (t : Term Nm k) (ν μ : Vec Nm k) → Agree ν μ
                 → ⟨ fst (⟦ t ⟧ ν) ≈[G] fst (⟦ t ⟧ μ) ⟩
        tm-agree (con c)  ν μ ag = ≈-refl (fst c)
        tm-agree (var ix) ν μ ag = ag ix

      -- The bound of a bounded quantifier moves by congruence on the RIGHT of
      -- the membership, which is the direction K3 proves from the first clause
      -- of the unfolding (Valuation.agda:445-450).

      bound-cong : ∀ {k} (t : Term Nm k) (ν μ : Vec Nm k) → Agree ν μ → (σ : Nm)
                 → (fst σ ∈[G] fst (⟦ t ⟧ ν)) ≡ (fst σ ∈[G] fst (⟦ t ⟧ μ))
      bound-cong t ν μ ag σ = ⇔toPath
        (∈-congʳ (tm-agree t ν μ ag))
        (∈-congʳ (≈-sym (tm-agree t ν μ ag)))

      sat-cong : ∀ {k} (φ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
               → (ν ⊨ φ) ≡ (μ ⊨ φ)
      sat-cong (t ∈̇ u) ν μ ag = ⇔toPath
        (λ hm → ∈-congʳ (tm-agree u ν μ ag) (∈-congˡ (tm-agree t ν μ ag) hm))
        (λ hm → ∈-congʳ (≈-sym (tm-agree u ν μ ag))
                  (∈-congˡ (≈-sym (tm-agree t ν μ ag)) hm))
      sat-cong (t ≐ u) ν μ ag = ⇔toPath
        (λ he → ≈-trans (≈-sym (tm-agree t ν μ ag)) (≈-trans he (tm-agree u ν μ ag)))
        (λ he → ≈-trans (tm-agree t ν μ ag) (≈-trans he (≈-sym (tm-agree u ν μ ag))))
      sat-cong (φ ∧̇ ψ) ν μ ag = ⊓-cong (sat-cong φ ν μ ag) (sat-cong ψ ν μ ag)
      sat-cong (φ ∨̇ ψ) ν μ ag = ⊔-cong (sat-cong φ ν μ ag) (sat-cong ψ ν μ ag)
      sat-cong (φ ⇒̇ ψ) ν μ ag = ⇒-cong (sat-cong φ ν μ ag) (sat-cong ψ ν μ ag)
      sat-cong ⊥̇ ν μ ag = refl
      sat-cong (∃̇ φ) ν μ ag =
        cong (⋁ Nm) (funExt (λ σ → sat-cong φ (σ ∷ ν) (σ ∷ μ) (agree-cons ag σ)))
      sat-cong (∀̇ φ) ν μ ag =
        cong (⋀ Nm) (funExt (λ σ → sat-cong φ (σ ∷ ν) (σ ∷ μ) (agree-cons ag σ)))
      sat-cong (∀̇∈ t φ) ν μ ag =
        cong (⋀ Nm) (funExt (λ σ →
          ⇒-cong (bound-cong t ν μ ag σ) (sat-cong φ (σ ∷ ν) (σ ∷ μ) (agree-cons ag σ))))
      sat-cong (∃̇∈ t φ) ν μ ag =
        cong (⋁ Nm) (funExt (λ σ →
          ⊓-cong (bound-cong t ν μ ag σ) (sat-cong φ (σ ∷ ν) (σ ∷ μ) (agree-cons ag σ))))

      ------------------------------------------------------------------------
      -- The copy of the ground
      ------------------------------------------------------------------------

      -- K5 owns this record outright (clause L12). It is NOT
      -- Certificate.Embedding (Certificate.agda:414), it is NOT
      -- Valuation.ValueStructure (Valuation.agda:683), and it carries no
      -- surjectivity clause, because there is none to carry: Track H's
      -- ext-onto is conditional on K3's tier-4 datum and Track J refuted the
      -- identification of the two generic names outright.
      --
      -- Rule 8 applied: three fields are functions into ⟨ _ ⟩ and one is a
      -- function into a Σ-type over S. None is a path in Ω, so the record
      -- stays at Type ℓ and may index a ⋁. The parameter G is LARGE
      -- (Sub : Type (ℓ-suc ℓ), ForcingNotion.agda:88-89) and that does not
      -- raise the record, because a record's sort is fixed by its fields.

      record GroundCopy : Type ℓ where
        field
          j      : S → Nm
          j-mem→ : (a b : S) → ⟨ a ∈ˢ b ⟩ → ⟨ fst (j a) ∈[G] fst (j b) ⟩
          j-mem← : (a b : S) → ⟨ fst (j a) ∈[G] fst (j b) ⟩ → ⟨ a ∈ˢ b ⟩
          j-inj  : (a c : S) → ⟨ fst (j a) ≈[G] fst (j c) ⟩ → ⟨ a ≈ˢ c ⟩

      -- The rule 8 check, on Track A's model (REPORT-A.md section 3): this
      -- elaborates only if GroundCopy is at Type ℓ.

      GroundCopy-indexes-⋁ : Ω
      GroundCopy-indexes-⋁ = ⋁ GroundCopy (λ _ → ⊥)

      ------------------------------------------------------------------------
      -- NON-CLAIMS, as signatures, on K3's model
      ------------------------------------------------------------------------

      -- Each of the four below is a Type that a competent reader of this file
      -- would expect to find inhabited. None is inhabited here, and the
      -- comment beside each says who owns it. This is K3's own discipline at
      -- Valuation.agda:693-715, moved one package forward.

      -- NON-CLAIM 1, trap T-F1. The valuation record. Its val-eq field asks
      -- that the carrier's host path equality be _≈[G]_, which forces a set
      -- quotient of Nm. K5 must not build it; K13 does, and K3's REPORT-I
      -- section 2 records that the construction is eight lines given
      -- Cubical.HITs.SetQuotients. No inhabitant here, and the absence is a
      -- scoping rule, not an obstruction.

      ValueStructureAt : Type (ℓ-suc ℓ)
      ValueStructureAt = VP.Value.Target.ValueStructure G Nm fst

      -- The copied environment former, and the relabelling of a ground
      -- formula's constants along the same map. Both are needed to state the
      -- next two items at all: a formula of the GROUND's language has ground
      -- sets as constants, and reading it inside the extension means sending
      -- each of them to its copy.

      mapEnv : ∀ {k} → (S → Nm) → Vec S k → Vec Nm k
      mapEnv f []      = []
      mapEnv f (x ∷ γ) = f x ∷ mapEnv f γ

      -- NON-CLAIM 2. Arbitrary formula elementarity along a map from the
      -- ground into the names, over the ground's own language. groundSat below
      -- inhabits the Δ₀ RESTRICTION of exactly this statement and nothing
      -- wider. At ∃̇ the extension's join ranges over every name, including
      -- names with no ground counterpart, and a forcing extension exists
      -- precisely to make such a join true where the ground join is false.
      -- Nobody in the programme claims this; K4's Boolean side refuses it in
      -- the same words (K4/SubalgebraAgreement.agda:25-27), and the reason is
      -- K2's: a complete subalgebra inclusion receives the JUSTIFIED atomic
      -- and bounded formula agreement and no more.
      --
      -- STATED, NOT REFUTED, and the difference is a measured one. Refuting it
      -- needs a concrete forcing notion at which some unbounded formula changes
      -- truth value, and K5 has an instance of the FRAME and not of the NOTION.
      -- K5's Track I fills every field of the frame record at the coded
      -- completion of an ARBITRARY presentation, and architecture part 6.4's O4
      -- records that no inhabitant of a coded Presentation exists anywhere, so
      -- the three roadmap exit examples are not runnable in K5. Building one
      -- presentation is K8's, not K5's.

      Elementarity : (S → Nm) → Type (ℓ-suc ℓ)
      Elementarity h = ∀ {k} (φ : Formula S k) (γ : Vec S k)
                     → (mapEnv h γ ⊨ mapFo h φ) ≡ Gr._⊨_ γ φ

      -- NON-CLAIM 3. Foundation in the extension structure, in the induction
      -- form the profile uses. Bell makes well-foundedness of the extension's
      -- membership EQUIVALENT to genericity, and it runs through the transitive
      -- collapse of the quotient carrier; K5 has neither the quotient nor the
      -- collapse, so this is K13's and is not claimed here in any form.
      --
      -- Trap T-F3 belongs with it. K5 claims exactly ONE field of the ordinary
      -- profile, `extensional` above; Foundation is the second field a reader
      -- would expect and it is a non-claim, and the remaining six are K6's.
      -- The profile record itself is deliberately NOT named in code, because
      -- exit item X7's negative-evidence table greps every K5 file for it.

      Founded : Type ℓ
      Founded = OrdinaryProfile.FoundationInduction structure

      -- NON-CLAIM 4. That the copy is onto, at an arbitrary name. An
      -- ∈-monomorphism is what Bell gets free from 1.23 and it is what
      -- GroundCopy says. Ontoness at the value relation is Track H's ext-onto,
      -- conditional on K3's tier-4 image datum; ontoness of the check map on
      -- the nose is FALSE as soon as one non-check name exists. Nothing here
      -- says the extension properly extends the ground either: K2's trivial
      -- HOST regular-open instance carries a host-generic filter (Track J,
      -- K5/RefutedGenericity.agda), and at the one-point poset the extension
      -- IS the ground, which is the positive control X6 names.

      Onto : (S → Nm) → Type ℓ
      Onto h = (σ : Nm) → ∥ Σ[ a ∈ S ] ⟨ fst σ ≈[G] fst (h a) ⟩ ∥₁

      -- NON-CLAIM 5, and this one cannot be shipped as a type at all, which is
      -- itself the result. IdentityOnGround is Bell 4.15: the ground sits
      -- inside the extension as ITSELF and not merely as an isomorphic copy.
      -- Writing it needs the transitive collapse of the quotient carrier, and
      -- K5 has neither the quotient (K13's, non-claim 1) nor a collapse (no
      -- Mostowski anywhere in this package). The one statement a reader
      -- mistakes for it IS typeable here, and exit item X6 forbids it by name:
      -- "the check name of a has the same value as a itself". It is a category
      -- error rather than an open problem, because a check name is a code of
      -- entries and a ground set is not, and it is not written anywhere below.

      ------------------------------------------------------------------------
      -- The check names, and everything they buy
      ------------------------------------------------------------------------

      -- K3's module Standard telescope, verbatim from Valuation.agda:493-503,
      -- plus one line: the validity of the poset check name, verbatim from
      -- StandardNames.agda:567.
      --
      -- MEASURED OVER-STATEMENT, and it is forced. Γ and Γ-spec are parameters
      -- of K3's module Standard, and check-≈-inj, check-faithful and
      -- check-value live inside it, so they cannot be reached without
      -- supplying the generic name. NEITHER IS USED by any Track F proof:
      -- `grep -n "Γ" K5/Structures.agda` finds them only in this telescope and
      -- in the application. K3's REPORT-I section 5 made exactly this move for
      -- entry-inj, ≈ˢ-paths and ext-path, on the ground that the parameter
      -- list is the ledger; Γ and Γ-spec belong one module deeper for the same
      -- reason, and that is a K3 correction this track reports rather than
      -- makes.

      module Copy
        (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
        (≈ˢ-paths    : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
        (ext-path    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
        (chk         : S → S)
        (chk-spec    : (a e : S) → (e ∈ˢ chk a)
                     ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrierᶠ)
                            ⊓ (e ≈ˢ entry (chk y) p))))
        (Γ           : S)
        (Γ-spec      : (e : S) → (e ∈ˢ Γ)
                     ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry (chk p) p)))
        (chk-name    : (a : S) → ⟨ IsNm (chk a) ⟩)
        where

        private
          module ST = VP.Value.Standard G entry-inj ≈ˢ-paths ext-path chk chk-spec Γ Γ-spec

        open ST public using ( ≈ˢ→≡ ; ≡→≈ˢ ; ≈ˢ-refl )

        -- The copy as a function into the names. This is the only place
        -- chk-name is spent, and it is what makes the ground's image land in
        -- the carrier of the structure rather than merely in S.

        groundName : S → Nm
        groundName a = chk a , chk-name a

        -- The copied environment, and the fact that every slot of it holds the
        -- check name of the same slot of the ground environment. Both are free
        -- of the filter: they are K4's checkEnv and lookup-check
        -- (K4/CheckValues.agda:424-437) at the poset check name, and they are
        -- placed HERE rather than under positivity so that the ledger reads
        -- true, positivity being spent only by the three theorems below.

        chkEnv : ∀ {k} → Vec S k → Vec Nm k
        chkEnv = mapEnv groundName

        lookup-chk : ∀ {k} (ix : Fin k) (γ : Vec S k)
                   → fst (lookup ix (chkEnv γ)) ≡ chk (lookup ix γ)
        lookup-chk zero     (x ∷ γ) = refl
        lookup-chk (suc ix) (x ∷ γ) = lookup-chk ix γ

        ----------------------------------------------------------------------
        -- At a positive G, and nothing more
        ----------------------------------------------------------------------

        -- Trap T-F2, structurally. Everything below lives under
        -- ⟨ positive G ⟩; isFilter appears nowhere inside this module.

        module WithPos (G-pos : ⟨ positive G ⟩) where

          open ST.WithPositivity G-pos public
            using ( check-active→ ; check-active← ; check-value
                  ; check-≈-inj ; check-faithful )

          -- The equality half of Bell 1.23(ii), on the poset side. K3 proves
          -- one direction as check-≈-inj; the other is free because the
          -- ground's equality is realized as a host path, so equal sets have
          -- the same check name on the nose and ≈-refl finishes.

          chk-≈ : (a c : S) → (chk a ≈[G] chk c) ≡ (a ≈ˢ c)
          chk-≈ a c = ⇔toPath (check-≈-inj a c)
            (λ h → subst (λ w → ⟨ chk a ≈[G] chk w ⟩) (≈ˢ→≡ h) (≈-refl (chk a)))

          -- THE GROUND COPY. Four fields, three of them K3's theorems and one
          -- of them K3's check name. No excluded middle, no nontriviality, no
          -- filter law beyond positivity, no genericity.

          groundCopy : GroundCopy
          groundCopy = record
            { j      = groundName
            ; j-mem→ = λ a b h → subst ⟨_⟩ (sym (check-faithful a b)) h
            ; j-mem← = λ a b h → subst ⟨_⟩ (check-faithful a b) h
            ; j-inj  = check-≈-inj }

          --------------------------------------------------------------------
          -- Bell 1.23(v), the bounded fragment and only the bounded fragment
          --------------------------------------------------------------------

          -- THE INDUCTION. Read the cases. The two atomic ones are chk-≈ and
          -- check-faithful, transported along lookup-chk. The four
          -- propositional ones are congruences of the SAME truth algebra on
          -- both sides, which is why no two-valuedness and no nontriviality
          -- appears anywhere: this is the exact point where the poset side is
          -- cheaper than K4's Boolean side, and the saving is measured rather
          -- than argued (K4/CheckValues.agda:243-247 states the Boolean cost).
          -- The two unbounded quantifier nodes are UNREACHABLE, by absurd
          -- pattern on the Δ₀ witness. The two bounded ones are the
          -- mathematics: one direction feeds the copied bound to the
          -- extension's quantifier, the other reads an arbitrary name below
          -- the copied bound back to a ground member through check-value and
          -- moves it onto that member's copy through sat-cong.

          -- The one term lemma the atomic and bounded cases share: a term of
          -- the ground's language, read in the extension along the copy, is
          -- the copy of what it reads in the ground. A constant is its own
          -- copy by definition and a variable is lookup-chk. There is no third
          -- case, which is why no clause below splits on the term, and it is
          -- why the ground-parameter version costs nothing over the
          -- parameter-free one.

          tm-chk : ∀ {k} (t : Term S k) (γ : Vec S k)
                 → fst (⟦ mapTm groundName t ⟧ (chkEnv γ)) ≡ chk (tmᴳ t γ)
          tm-chk (con a)  γ = refl
          tm-chk (var ix) γ = lookup-chk ix γ

          groundSat : ∀ {k} (φ : Formula S k) → Δ₀ φ → (γ : Vec S k)
                    → (chkEnv γ ⊨ mapFo groundName φ) ≡ Gr._⊨_ γ φ

          groundSat (t ∈̇ u) δ-∈ γ =
            cong₂ _∈[G]_ (tm-chk t γ) (tm-chk u γ)
            ∙ check-faithful (tmᴳ t γ) (tmᴳ u γ)

          groundSat (t ≐ u) δ-≐ γ =
            cong₂ _≈[G]_ (tm-chk t γ) (tm-chk u γ)
            ∙ chk-≈ (tmᴳ t γ) (tmᴳ u γ)

          groundSat (φ ∧̇ ψ) (δ-∧ dφ dψ) γ =
            ⊓-cong (groundSat φ dφ γ) (groundSat ψ dψ γ)
          groundSat (φ ∨̇ ψ) (δ-∨ dφ dψ) γ =
            ⊔-cong (groundSat φ dφ γ) (groundSat ψ dψ γ)
          groundSat (φ ⇒̇ ψ) (δ-⇒ dφ dψ) γ =
            ⇒-cong (groundSat φ dφ γ) (groundSat ψ dψ γ)
          groundSat ⊥̇ δ-⊥ γ = refl

          groundSat (∃̇ φ) () γ
          groundSat (∀̇ φ) () γ

          groundSat (∀̇∈ t φ) (δ-∀∈ dφ) γ = ⇔toPath to from
            where
              a : S
              a = tmᴳ t γ

              agree-cons' : (c d : Nm) → ⟨ fst c ≈[G] fst d ⟩
                          → Agree (c ∷ chkEnv γ) (d ∷ chkEnv γ)
              agree-cons' c d h zero     = h
              agree-cons' c d h (suc jx) = ≈-refl (fst (lookup jx (chkEnv γ)))

              to : ⟨ chkEnv γ ⊨ mapFo groundName (∀̇∈ t φ) ⟩
                 → ⟨ Gr._⊨_ γ (∀̇∈ t φ) ⟩
              to f x hx = subst ⟨_⟩ (groundSat φ dφ (x ∷ γ))
                (f (groundName x)
                   (subst (λ w → ⟨ chk x ∈[G] w ⟩) (sym (tm-chk t γ))
                     (subst ⟨_⟩ (sym (check-faithful x a)) hx)))

              from : ⟨ Gr._⊨_ γ (∀̇∈ t φ) ⟩
                   → ⟨ chkEnv γ ⊨ mapFo groundName (∀̇∈ t φ) ⟩
              from g σ hσ = PT.rec (snd ((σ ∷ chkEnv γ) ⊨ mapFo groundName φ))
                (λ { (y , hy , e) →
                       subst ⟨_⟩
                         (sat-cong (mapFo groundName φ)
                           (groundName y ∷ chkEnv γ) (σ ∷ chkEnv γ)
                           (agree-cons' (groundName y) σ (≈-sym e)))
                         (subst ⟨_⟩ (sym (groundSat φ dφ (y ∷ γ))) (g y hy)) })
                (subst ⟨_⟩ (check-value a (fst σ))
                  (subst (λ w → ⟨ fst σ ∈[G] w ⟩) (tm-chk t γ) hσ))

          groundSat (∃̇∈ t φ) (δ-∃∈ dφ) γ = ⇔toPath to from
            where
              a : S
              a = tmᴳ t γ

              agree-cons' : (c d : Nm) → ⟨ fst c ≈[G] fst d ⟩
                          → Agree (c ∷ chkEnv γ) (d ∷ chkEnv γ)
              agree-cons' c d h zero     = h
              agree-cons' c d h (suc jx) = ≈-refl (fst (lookup jx (chkEnv γ)))

              to : ⟨ chkEnv γ ⊨ mapFo groundName (∃̇∈ t φ) ⟩
                 → ⟨ Gr._⊨_ γ (∃̇∈ t φ) ⟩
              to = PT.rec PT.squash₁
                (λ { (σ , hσ , hφ) → PT.map
                       (λ { (y , hy , e) → y , hy
                          , subst ⟨_⟩ (groundSat φ dφ (y ∷ γ))
                              (subst ⟨_⟩
                                (sat-cong (mapFo groundName φ) (σ ∷ chkEnv γ)
                                  (groundName y ∷ chkEnv γ)
                                  (agree-cons' σ (groundName y) e))
                                hφ) })
                       (subst ⟨_⟩ (check-value a (fst σ))
                         (subst (λ w → ⟨ fst σ ∈[G] w ⟩) (tm-chk t γ) hσ)) })

              from : ⟨ Gr._⊨_ γ (∃̇∈ t φ) ⟩
                   → ⟨ chkEnv γ ⊨ mapFo groundName (∃̇∈ t φ) ⟩
              from = PT.map
                (λ { (x , hx , hφ) → groundName x
                   , subst (λ w → ⟨ chk x ∈[G] w ⟩) (sym (tm-chk t γ))
                       (subst ⟨_⟩ (sym (check-faithful x a)) hx)
                   , subst ⟨_⟩ (sym (groundSat φ dφ (x ∷ γ))) hφ })

        ----------------------------------------------------------------------
        -- The architecture's signature, and the hypothesis it over-charges
        ----------------------------------------------------------------------

        -- Architecture section 1.8 prints groundCopy at ⟨ positive G ⟩ and it
        -- is RIGHT to do so; the reading below is the one a consumer holding a
        -- filter wants, and it shows the direction of the over-charge: a
        -- filter gives positivity by projection and nothing above is reproved.

        groundCopy-at-filter : isFilter G → GroundCopy
        groundCopy-at-filter fil = WithPos.groundCopy (filter-positive fil)

        groundSat-at-filter : (fil : isFilter G) → ∀ {k} (φ : Formula S k) → Δ₀ φ
                            → (γ : Vec S k)
                            → (chkEnv γ ⊨ mapFo groundName φ) ≡ Gr._⊨_ γ φ
        groundSat-at-filter fil = WithPos.groundSat (filter-positive fil)

  ----------------------------------------------------------------------------
  -- The two instantiations
  ----------------------------------------------------------------------------

  -- The P side: the conditions of the forcing notion, its order, and a subset
  -- of conditions. Nothing here mentions an algebra.

  module PosetSide (carrierᶠ : S)
    (_≼ᶜ_       : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
    (≼ᶜ-refl    : (p : Conditions carrierᶠ) → ⟨ p ≼ᶜ p ⟩)
    (≼ᶜ-trans   : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
    (inhabitedᶜ : ∥ Conditions carrierᶠ ∥₁)
    (IsNameᴾ    : S → Ω)
    (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
    where

    module P = Side carrierᶠ _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ IsNameᴾ child-nameᴾ

    Nameᴾ : Type ℓ
    Nameᴾ = P.Nm

    𝒮ᴾ[_] : P.Sub → ZFStructure (hPropAlgebra ℓ)
    𝒮ᴾ[ G ] = P.Ext.structure G

    ext[_] : (G : P.Sub) → OrdinaryProfile.Extensionality 𝒮ᴾ[ G ]
    ext[ G ] = P.Ext.extensional G

  -- The B side: the SAME construction at the algebra's own points and its own
  -- order. Architecture section 1.8's ruling, checked rather than quoted:
  -- Conditions B and K4's Pt B are the same plain Σ-type, so the B side needs
  -- only a Lattice for its top, and 𝒮ᴮ[_] can be stated at (Pt B → Ω) exactly
  -- as the architecture prints it.

  module BooleanSide (B : S)
    (L           : Lattice B)
    (IsNameᴮ     : S → Ω)
    (child-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴮ x ⟩)
    where

    open Lattice L using ( ⊤ᴮ )

    Pt-is-Conditions : Pt B ≡ Conditions B
    Pt-is-Conditions = refl

    module B' = Side B (λ p q → _≤ᴮ_ {B} p q) (λ p → ≤ᴮ-refl {B} p)
                     (λ {p} {q} {r} → ⊆ˢ-trans) ∣ ⊤ᴮ ∣₁
                     IsNameᴮ child-nameᴮ

    Nameᴮ : Type ℓ
    Nameᴮ = B'.Nm

    𝒮ᴮ[_] : (Pt B → Ω) → ZFStructure (hPropAlgebra ℓ)
    𝒮ᴮ[ U ] = B'.Ext.structure U

    extᴮ[_] : (U : Pt B → Ω) → OrdinaryProfile.Extensionality 𝒮ᴮ[ U ]
    extᴮ[ U ] = B'.Ext.extensional U
