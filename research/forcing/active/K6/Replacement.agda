{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track H, deliverable 1. The `hasReplacement` field of the ordinary
-- profile at the extension structure.
--
-- ---------------------------------------------------------------------
-- WHICH STATEMENT THIS FILE PROVES, AND WHICH ONE IT DOES NOT (rule 8)
-- ---------------------------------------------------------------------
--
-- The field is OrdinaryProfile.Collection (OrdinaryProfile.agda:95-100),
-- Bell (3), the COLLECTION form of Replacement. Its premise is TRUNCATED
-- totality, for each x ∈ a SOME y, with no chosen y and no uniqueness; its
-- conclusion is a BOUND b, which may contain junk, and not an image.
--
-- IT IS NOT `hasImage` (OrdinaryProfile.agda:340-344), which takes the whole
-- OrdinaryZF record and demands host contractible functionality
-- `isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)` and concludes the exact image.
-- K1 measured that the two do not imply each other in one step, and an author
-- who writes isContr has proved a weaker theorem under a stronger premise.
-- `isContr` occurs nowhere below; the shipped type is `OP.Collection` and the
-- diff against OrdinaryProfile.agda:95-100 is performed by the typechecker.
--
-- Ruling D4 is in force. Ground Separation and ground Collection are
-- standalone arguments, never a record. Rule 13 applied to Track A's measured
-- list of three: this file spends Separation and Collection directly and
-- ground Union through the operation ⋃ᴳ; PowerSet and Pairing are named
-- nowhere.
--
-- ---------------------------------------------------------------------
-- THE MATHEMATICS, IN SIX MOVES
-- ---------------------------------------------------------------------
--
-- Fix a name α and a formula φ of the extension's own language.
--
--   1. THE DOMAIN IS A GROUND SET. A value member of α is value equal to an
--      ACTIVE ENTRY of α's code, an active entry carries an entry at a
--      condition, and dom collects those. So the whole domain of α is covered
--      by the single ground set dom (fst α). This is the answer to the proper
--      class trap: no class of names is collected by host fiat anywhere below.
--
--   2. THE INNER BOUND, one ground Collection over the CONDITIONS. For a fixed
--      ground code x the class of witnesses is a proper class, but the class
--      of CONDITIONS is the ground set carrierᶠ. Collect over carrierᶠ along
--      the class "if any name forces φ at q then this one does", which is
--      total by excluded middle: where some name forces, take it; where none
--      does, the implication is vacuous and any code serves. The result is a
--      ground set w adequate for x at every condition at once.
--
--   3. THE OUTER BOUND, one ground Collection over the DOMAIN. Collect over
--      dom (fst α) along the class "w is adequate at x", whose premise at each
--      x is move 2. This is Bell's outer Replacement in V and it is the step
--      the roadmap calls uniform bounding.
--
--   4. ONE UNION AND ONE CUT. The union of the collected adequate sets is a
--      ground set; Track A's `mk` cuts it down to its names.
--
--   5. THE FULL NAME. b is Track A's cut of the entry bound of that set of
--      names by a tautology, so every sifted code sits in b at every
--      condition. cut-name certifies it is a name.
--
--   6. READ BACK. For x in the domain the premise gives a witness y and, by
--      the truth lemma, a condition p of G forcing φ at (y , x). Adequacy at
--      p replaces y by some τ inside the bound; τ is then a value member of b,
--      and the truth lemma read backwards turns "p forces" into "φ holds".
--
-- ---------------------------------------------------------------------
-- WHICH HALF OF ARCHITECTURE 3.2 THIS SPENDS, AND A SHARPENING
-- ---------------------------------------------------------------------
--
-- The FREE half is `below b`, the ground SET of conditions forcing a given
-- Boolean ELEMENT, a ForcingBase field (K5/Frame.agda:199-201) shipped by
-- Track E1 as forcedSet with forcedSet-in and forcedSet-out
-- (K6/Definability.agda:89-105). NO SEPARATION IS SPENT ON IT HERE and none is
-- written below; `forcesSet` is never named.
--
-- The half this file spends is the O1 half, and it spends it in a form
-- STRICTLY STRONGER than "a ground set of conditions per environment". That
-- form is the coordinator's ruling of 2026-09-12, obstruction O7, the
-- DEFINABILITY DATUM, class (ii): open at this layer, inhabited in principle,
-- free at the coded completion where `below` is `fst` and the description is
-- Δ₀, unsupplied at the abstract frame. Track F reached it from Separation and
-- Track G from Power Set independently, and roadmap:205 named it in advance
-- when it said to bound witnesses "using ground Collection and forcing
-- definability".
--
-- Why nothing already in the ledger supplies it. Ground Collection reads a
-- Formula S 2, so what moves 2 and 3 need is the forcing relation as a ground
-- FORMULA WITH FREE SLOTS, uniform in the witness, the condition and the
-- domain member at once. Track E2's forcesSet (K6/ForcesTruth.agda:337-338) is
-- a ground set at each FIXED environment and is not that formula: nothing
-- turns a family of sets indexed by a host variable into one internal formula.
-- The datum that is is the compiled value's internal code, K4's
-- Interp.code : Formula S (suc (suc k)) (K4/Compile.agda:538-543), whose
-- environment slots are exactly what keeps the graph uniform in x, composed
-- with an internal description of `below`. It enters below as colΔ and
-- colΔ-reading, and NameImage's colAt (NameImage.agda:285-291) freezes its
-- third slot for move 2.
--
-- HOW THIS TRACK'S SPELLING DIFFERS FROM TRACK F'S, and why it must (ruling
-- part 2 asks the difference be stated). Track F's sepΔ is a Formula S 1 with
-- the name and the formula frozen, because Separation cuts ENTRIES out of one
-- bound at a fixed α and φ, so only the entry code is free. Collection reads a
-- Formula S 2 and, in move 3, must be uniform in the domain member as well, so
-- colΔ is a Formula S 3 with the witness, the condition and the member all
-- free. Same datum, and the arity is forced by which axiom reads it.
--
-- TRACK G'S ATOMIC SAVING DOES NOT APPLY HERE, and this is a measured negative
-- rather than an omission. Track G cut its bounding name by Separation against
-- the FIXED atomic formula `var zero ∈̇ con χ`, so its datum is atomic and its
-- second index is a name. Collection is a SCHEMA: the field quantifies over
-- every φ : Formula Nm 2, and the witnesses of φ are arbitrary names with no
-- candidate bound to cut, so no fixed atomic statement can stand in for φ.
-- The attempt was made and it is the general form or nothing.
--
-- ---------------------------------------------------------------------
-- RULE 15. THE TELESCOPE, AND WHETHER EACH ENTRY IS INHABITED AT A
-- GENUINE FORCING EXTENSION
-- ---------------------------------------------------------------------
--
-- A false hypothesis in a telescope discharges a field with no body level grep
-- catching it. Each entry below is a landed export, a ground operation, or a
-- datum unproved at this layer rather than false at the instance.
--
--   entry, Child, child-entry, carrierᶠ, IsNm, child-name
--     K3's name kernel, the four facts this file spends. Inhabited always.
--   Cond, cnd, cnd-carrier, cndOf, cndOf-cnd, G∈, the value relation and its
--   six laws
--     K5's poset side at one G. At the instance Cond is Conditions carrierᶠ,
--     a plain Σ type, so cndOf q hq is (q , hq) and cndOf-cnd is refl by the
--     eta law for Σ.
--   sat-cong                K5/Structures.agda:400-402, unconditional.
--   sepᴳ, collᴳ             ground axioms, standalone arguments (D4).
--   dom, dom-in, dom-out    K3's support (NameSupport.agda:514, :534, :542).
--   ⋃ᴳ, ⋃ᴳ-in              ground Union (NameSupport.agda:444-448).
--   entryBound, entryBound-in, mk, mk-in, mk-sat, cut-name, nameFo,
--   nameFo-reading          Track A, K6/NameBuild.agda:294, :325, :348, :355,
--                           :363 and K6/NameValid.agda:159, :187, :190.
--   colAt, colAt-reading    NameImage.agda:285-291, pure formula manipulation.
--   forces, truth-at        Track E2, K6/ForcesTruth.agda:306, :316. Their own
--                           module carries the whole conditionality of the
--                           package and this file names none of it.
--   colΔ, colΔ-reading      forcing definability, above. K4's Interp.code is
--                           what inhabits it at a genuine extension.
--   lem                     LEM ℓ, covered by the programme's LEM (ℓ-suc ℓ)
--                           through lowerLEM. Net addition zero.
--
-- NO PARAMETER ASSERTS THAT A BOUND EXISTS FOR THE CLASS THIS FILE BOUNDS.
-- The architecture prints witnessBound and witnessBound-covers as signatures;
-- taking either as a hypothesis would be exactly the poisoned telescope rule
-- 15 names, since a rank bound no genuine extension satisfies would discharge
-- Collection in three tokens. Both are BUILT below, in moves 2 to 4, out of
-- ground Collection, ground Separation and ground Union, and the break file
-- K6/breaks/ColNoBound.agda-break holds the version that assumes them.
--
-- THE SILENT O3b IMPORT, and the check. Track A's graph→image and K3's
-- imageOn have the identical result shape, so a filler that ignores the graph
-- and calls imageOn typechecks and is O3b conditional with nothing saying so.
-- This file forms no image at all: it takes entryBound and mk as variables,
-- and `grep -cE 'imageOn|MemberImage|\.image\b|image-spec'` over it with
-- comments stripped is 0.
--
-- MEASURED NARROWING (rule 13). Architecture 2.1 prints
-- `hasReplacement : Engine → isFilter G → Generic G → …`. Neither isFilter G
-- nor any dense set fact is named below. The condition that witnesses the
-- truth lemma arrives already carrying ⟨ G∈ r ⟩, and active-in asks for
-- nothing more; both are charged once inside Track E2 and charging them again
-- here would put them in this ledger under a false heading.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( Term ; Formula ; con ; var ; _∈̇_ ; _∧̇_ ; _⇒̇_ ; ⊥̇ ; ∃̇_ ; ∀̇∈ ; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo ; module Sat )
import FOL.Semantics
import OrdinaryProfile
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K6.Replacement {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open OrdinaryProfile 𝒮 using ( Separation ; Collection )

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
open SemG using ( _^_ )
module SatG = SemG.At S id
open SatG public using () renaming ( _⊨_ to _⊨ᴳ_ )

private module Ren = Sat (hPropAlgebra ℓ) 𝒮 id

-- Rule 1. No bare reflexivity ever stands for an unchanged endpoint inside a
-- congruence over a truth value operation.

same : (P : Ω) → P ≡ P
same P = refl

⊓-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⊓ Q) ≡ (P' ⊓ Q')
⊓-cong p q = cong₂ _⊓_ p q

⇒-cong : {P P' Q Q' : Ω} → P ≡ P' → Q ≡ Q' → (P ⇒ Q) ≡ (P' ⇒ Q')
⇒-cong p q = cong₂ _⇒_ p q

--------------------------------------------------------------------------------
-- The name kernel, flat
--------------------------------------------------------------------------------

-- Four of K3's seven kernel facts, in the shapes at K5/Structures.agda:209-217
-- and :250. The three this file never spends, isPropChild, child-wf and the
-- empty name with its specification, are absent under rule 13.

module Names
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (carrierᶠ    : S)
  (IsNm        : S → Ω)
  (child-name  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ IsNm x ⟩)
  where

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNm n))

  ------------------------------------------------------------------------------
  -- The extension structure at one subset of the conditions
  ------------------------------------------------------------------------------

  -- The value relation reaches this file as five variables and seven laws, in
  -- Track F's shapes (K6/Separation.agda:131-145) so that the coordinator's
  -- seam line is the same one it already writes. ≈-refl is the one addition:
  -- the congruence below replaces the SECOND slot of a two slot environment
  -- and leaves the first alone, so the first needs reflexivity.

  module AtG
    (Cond        : Type ℓ)
    (cnd         : Cond → S)
    (cnd-carrier : (r : Cond) → ⟨ cnd r ∈ˢ carrierᶠ ⟩)
    (cndOf       : (q : S) → ⟨ q ∈ˢ carrierᶠ ⟩ → Cond)
    (cndOf-cnd   : (r : Cond) → cndOf (cnd r) (cnd-carrier r) ≡ r)
    (G∈          : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    (‖Active‖    : S → S → Ω)
    (≈-refl      : (x : S) → ⟨ x ≈[G] x ⟩)
    (∈-unfold    : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
    (active-value : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩)
    (active-out  : (x n : S) → ⟨ ‖Active‖ x n ⟩
                 → ⟨ ⋁ Cond (λ r → G∈ r ⊓ (entry x (cnd r) ∈ˢ n)) ⟩)
    (active-in   : (x n : S) (r : Cond) → ⟨ G∈ r ⟩ → ⟨ entry x (cnd r) ∈ˢ n ⟩
                 → ⟨ ‖Active‖ x n ⟩)
    where

    -- THE STRUCTURE. Four fields, the same four expressions K5 writes at
    -- K5/Structures.agda:285-291. At Nm := K5's Nm this record is
    -- definitionally K5's `structure`, so OrdinaryProfile.Collection of it is
    -- definitionally the seventh field of OrdinaryZF 𝒮ᴾ[ G ].

    𝒮ᴱ : ZFStructure (hPropAlgebra ℓ)
    𝒮ᴱ = record
      { S      = Nm
      ; isSetS = isSetNm
      ; _≈ˢ_   = λ σ τ → fst σ ≈[G] fst τ
      ; _∈ˢ_   = λ σ τ → fst σ ∈[G] fst τ }

    module OP = OrdinaryProfile 𝒮ᴱ

    private module SemE = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴱ
    module SatE = SemE.At Nm id
    open SatE public using ( _⊨_ )

    Agree : ∀ {k} → Vec Nm k → Vec Nm k → Type ℓ
    Agree {k} ν μ = (ix : Fin k) → ⟨ fst (lookup ix ν) ≈[G] fst (lookup ix μ) ⟩

  ----------------------------------------------------------------------------
  -- The theorem
  ----------------------------------------------------------------------------

    module Collected
      -- K5/Structures.agda:400-402, unconditional, costs only G : Sub.
      (sat-cong : ∀ {k} (ψ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                → (ν ⊨ ψ) ≡ (μ ⊨ ψ))
      -- The two ground axioms, spent only through Track A's sealed terms and
      -- through the two Collection applications below.
      (sepᴳ  : Separation)
      (collᴳ : Collection)
      -- K3's support, in Track F's three shapes.
      (dom     : S → S)
      (dom-in  : (n x p : S) → ⟨ entry x p ∈ˢ n ⟩ → ⟨ x ∈ˢ dom n ⟩)
      (dom-out : (n x : S) → ⟨ x ∈ˢ dom n ⟩ → ⟨ ⋁ S (λ p → entry x p ∈ˢ n) ⟩)
      -- Ground Union as an operation, on K3's own model (NameSpace.agda:554-565).
      (⋃ᴳ    : S → S)
      (⋃ᴳ-in : (b y x : S) → ⟨ y ∈ˢ b ⟩ → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ ⋃ᴳ b ⟩)
      -- Track A. K6/NameBuild.agda:294, :325, :348, :355, :363.
      (entryBound : Collection → Separation → (D : S) → S)
      (entryBound-in : (coll : Collection) (sep : Separation) (D x p : S)
                     → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                     → ⟨ entry x p ∈ˢ entryBound coll sep D ⟩)
      (mk : Separation → (bound : S) → Formula S 1 → S)
      (mk-in : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
             → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩ → ⟨ e ∈ˢ mk sep bound θ ⟩)
      (mk-sat : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
              → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩)
      -- K6/NameValid.agda:159, :187, :190.
      (cut-name : (coll : Collection) (sep : Separation) (D : S) (θ : Formula S 1)
                → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsNm x ⟩)
                → ⟨ IsNm (mk sep (entryBound coll sep D) θ) ⟩)
      (nameFo : Formula S 1)
      (nameFo-reading : (t : S) → ((t ∷ []) ⊨ᴳ nameFo) ≡ IsNm t)
      -- NameImage.agda:285-291. Pure formula manipulation, no axiom.
      (colAt : ∀ {k} → Formula S (suc (suc k)) → Vec S k → Formula S 2)
      (colAt-reading : ∀ {k} (ψ : Formula S (suc (suc k))) (ps : Vec S k) (y x : S)
                     → ((y ∷ x ∷ []) ⊨ᴳ colAt ψ ps) ≡ ((y ∷ x ∷ ps) ⊨ᴳ ψ))
      -- Track E2, module Conditional. The five conditional hypotheses are the
      -- parameters of THAT module and are named nowhere in this file.
      (forces   : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (truth-at : ∀ {k} (ψ : Formula Nm k) (ν : Vec Nm k)
                → (ν ⊨ ψ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r ψ ν))
      -- The definability datum, with the witness, the condition and the domain
      -- member all FREE. See the header for why a set per environment is not
      -- enough and this is.
      (colΔ : Formula Nm 2 → Formula S 3)
      (colΔ-reading : (ψ : Formula Nm 2) (τ : Nm) (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩)
                      (χ : Nm)
                    → ((fst τ ∷ q ∷ fst χ ∷ []) ⊨ᴳ colΔ ψ)
                    ≡ forces (cndOf q hq) ψ (τ ∷ χ ∷ []))
      -- Covered by the programme's single LEM (ℓ-suc ℓ) through lowerLEM.
      (lem : LEM ℓ)
      where

      ------------------------------------------------------------------------
      -- Two formula placements and one tautology
      ------------------------------------------------------------------------

      -- The recogniser at slot zero of a wider context. Rule 6 is sharp here:
      -- a placement at uniform depth still elaborates when the slot is wrong,
      -- so the reading theorem is the only guard.

      nameAt : ∀ {n} → Formula S (suc n)
      nameAt = renameFo (λ _ → zero) nameFo

      nameAt-ag : ∀ {n} (γ : S ^ (suc n))
                → Ren.Agrees (λ _ → zero) γ (lookup zero γ ∷ [])
      nameAt-ag γ zero = refl

      nameAt-reading : ∀ {n} (γ : S ^ (suc n))
                     → (γ ⊨ᴳ nameAt {n}) ≡ IsNm (lookup zero γ)
      nameAt-reading γ =
        Ren.⊨-rename (λ _ → zero) nameFo γ (lookup zero γ ∷ []) (nameAt-ag γ)
        ∙ nameFo-reading (lookup zero γ)

      -- The inner placement: two slots (witness , condition) under one binder,
      -- with the witness taken from the binder.

      ρᵢ : Fin 2 → Fin 3
      ρᵢ zero       = zero
      ρᵢ (suc zero) = suc (suc zero)

      ρᵢ-ag : (v τ q : S) → Ren.Agrees ρᵢ (v ∷ τ ∷ q ∷ []) (v ∷ q ∷ [])
      ρᵢ-ag v τ q zero       = refl
      ρᵢ-ag v τ q (suc zero) = refl

      -- The outer placement: three slots (witness , condition , member) under
      -- two binders, with the witness taken from the inner binder.

      ρₒ : Fin 3 → Fin 4
      ρₒ zero             = zero
      ρₒ (suc zero)       = suc zero
      ρₒ (suc (suc zero)) = suc (suc (suc zero))

      ρₒ-ag : (v q w x : S) → Ren.Agrees ρₒ (v ∷ q ∷ w ∷ x ∷ []) (v ∷ q ∷ x ∷ [])
      ρₒ-ag v q w x zero             = refl
      ρₒ-ag v q w x (suc zero)       = refl
      ρₒ-ag v q w x (suc (suc zero)) = refl

      -- The full name is Track A's cut by a formula that cuts nothing. It is
      -- written as an implication rather than as a negated falsehood so that
      -- its inhabitant is the identity and no elimination is performed.

      topFo : Formula S 1
      topFo = ⊥̇ ⇒̇ ⊥̇

      topFo-true : (e : S) → ⟨ (e ∷ []) ⊨ᴳ topFo ⟩
      topFo-true e h = h

      ------------------------------------------------------------------------
      -- One name, one formula
      ------------------------------------------------------------------------

      module _ (α : Nm) (φ : Formula Nm 2) where

        fo : Formula S 3
        fo = colΔ φ

        frozen : S → Formula S 2
        frozen x = colAt fo (x ∷ [])

        frozen-reading : (x τ q : S)
                       → ((τ ∷ q ∷ []) ⊨ᴳ frozen x) ≡ ((τ ∷ q ∷ x ∷ []) ⊨ᴳ fo)
        frozen-reading x τ q = colAt-reading fo (x ∷ []) τ q

        -- The class of names forcing φ at the condition q with the member x.

        hit : S → S → S → Ω
        hit q x v = IsNm v ⊓ ((v ∷ q ∷ x ∷ []) ⊨ᴳ fo)

        attained : S → S → Ω
        attained x q = ⋁ S (λ v → IsNm v ⊓ ((v ∷ q ∷ []) ⊨ᴳ frozen x))

        attained-hit : (x q : S) → attained x q ≡ ⋁ S (hit q x)
        attained-hit x q = cong (⋁ S) (funExt (λ v →
          ⊓-cong (same (IsNm v)) (frozen-reading x v q)))

        --------------------------------------------------------------------
        -- Move 2. The inner bound, one ground Collection over the conditions
        --------------------------------------------------------------------

        -- Slot 0 is the witness and slot 1 the condition, which is the order
        -- Collection reads (OrdinaryProfile.agda:95-100, whose class is
        -- evaluated at (y ∷ x ∷ []) with x the member of the domain set).

        innFo : S → Formula S 2
        innFo x = (∃̇ (nameAt ∧̇ renameFo ρᵢ (frozen x)))
                ⇒̇ (nameAt ∧̇ frozen x)

        innFo-reading : (x τ q : S)
          → ((τ ∷ q ∷ []) ⊨ᴳ innFo x)
          ≡ (attained x q ⇒ (IsNm τ ⊓ ((τ ∷ q ∷ []) ⊨ᴳ frozen x)))
        innFo-reading x τ q =
          ⇒-cong
            (cong (⋁ S) (funExt (λ v →
              ⊓-cong (nameAt-reading (v ∷ τ ∷ q ∷ []))
                     (Ren.⊨-rename ρᵢ (frozen x)
                        (v ∷ τ ∷ q ∷ []) (v ∷ q ∷ []) (ρᵢ-ag v τ q)))))
            (⊓-cong (nameAt-reading (τ ∷ q ∷ []))
                    (same ((τ ∷ q ∷ []) ⊨ᴳ frozen x)))

        -- Totality of the inner class. The classical step is the only place
        -- excluded middle is spent in this file: where some name forces at q
        -- that name witnesses the class, and where none does the class holds
        -- vacuously of anything, so no witness has to be chosen.

        innerPremise : (x : S)
          → ⟨ ⋀ S (λ q → (q ∈ˢ carrierᶠ) ⇒
               (⋁ S (λ τ → (τ ∷ q ∷ []) ⊨ᴳ innFo x))) ⟩
        innerPremise x q _ = decide (lem (attained x q))
          where
            decide : ⟨ attained x q ⟩ ⊎ (⟨ attained x q ⟩ → Empty.⊥)
                   → ⟨ ⋁ S (λ τ → (τ ∷ q ∷ []) ⊨ᴳ innFo x) ⟩
            decide (inl h) = PT.map
              (λ { (v , hv) →
                     v , subst ⟨_⟩ (sym (innFo-reading x v q)) (λ _ → hv) })
              h
            decide (inr n) =
              ∣ q , subst ⟨_⟩ (sym (innFo-reading x q q))
                              (λ hA → Empty.rec (n hA)) ∣₁

        --------------------------------------------------------------------
        -- Move 3. The outer bound, one ground Collection over the domain
        --------------------------------------------------------------------

        -- Slot 0 is the adequate set and slot 1 the domain member. The bound
        -- quantifier over carrierᶠ is what keeps the condition variable inside
        -- a ground set; the two inner quantifiers over the witness are
        -- UNBOUNDED, which is legal in a first order formula and is exactly
        -- why no class is collected here.

        bodyψ : Formula S 4
        bodyψ = nameAt ∧̇ renameFo ρₒ fo

        bodyψ-reading : (v q w x : S)
                      → ((v ∷ q ∷ w ∷ x ∷ []) ⊨ᴳ bodyψ) ≡ hit q x v
        bodyψ-reading v q w x =
          ⊓-cong (nameAt-reading (v ∷ q ∷ w ∷ x ∷ []))
                 (Ren.⊨-rename ρₒ fo
                    (v ∷ q ∷ w ∷ x ∷ []) (v ∷ q ∷ x ∷ []) (ρₒ-ag v q w x))

        psiFo : Formula S 2
        psiFo = ∀̇∈ (con carrierᶠ)
                  ((∃̇ bodyψ) ⇒̇ (∃̇∈ (var (suc zero)) bodyψ))

        Adequate : S → S → Ω
        Adequate w x = ⋀ S (λ q → (q ∈ˢ carrierᶠ) ⇒
                         ((⋁ S (hit q x)) ⇒ (⋁ S (λ v → (v ∈ˢ w) ⊓ hit q x v))))

        psiFo-reading : (w x : S) → ((w ∷ x ∷ []) ⊨ᴳ psiFo) ≡ Adequate w x
        psiFo-reading w x = cong (⋀ S) (funExt (λ q →
          ⇒-cong (same (q ∈ˢ carrierᶠ))
            (⇒-cong
              (cong (⋁ S) (funExt (λ v → bodyψ-reading v q w x)))
              (cong (⋁ S) (funExt (λ v →
                ⊓-cong (same (v ∈ˢ w)) (bodyψ-reading v q w x)))))))

        domα : S
        domα = dom (fst α)

        domα-name : (x : S) → ⟨ x ∈ˢ domα ⟩ → ⟨ IsNm x ⟩
        domα-name x hx = PT.rec (snd (IsNm x))
          (λ { (p , hp) →
                 child-name (fst α) (snd α) x (child-entry x p (fst α) hp) })
          (dom-out (fst α) x hx)

        outerPremise : ⟨ ⋀ S (λ x → (x ∈ˢ domα) ⇒
                          (⋁ S (λ w → (w ∷ x ∷ []) ⊨ᴳ psiFo))) ⟩
        outerPremise x _ =
          PT.map step (collᴳ carrierᶠ (innFo x) (innerPremise x))
          where
            step : Σ[ w ∈ S ] ⟨ ⋀ S (λ q → (q ∈ˢ carrierᶠ) ⇒
                     (⋁ S (λ τ → (τ ∈ˢ w) ⊓ ((τ ∷ q ∷ []) ⊨ᴳ innFo x)))) ⟩
                 → Σ[ w ∈ S ] ⟨ (w ∷ x ∷ []) ⊨ᴳ psiFo ⟩
            step (w , hw) = w , subst ⟨_⟩ (sym (psiFo-reading w x)) adeq
              where
                adeq : ⟨ Adequate w x ⟩
                adeq q hq hA = PT.map
                  (λ { (τ , hτw , hinn) →
                         τ , hτw
                       , subst ⟨_⟩
                           (⊓-cong (same (IsNm τ)) (frozen-reading x τ q))
                           (subst ⟨_⟩ (innFo-reading x τ q) hinn
                             (subst ⟨_⟩ (sym (attained-hit x q)) hA)) })
                  (hw q hq)

        --------------------------------------------------------------------
        -- Moves 4 and 5. One union, one cut, and the full name
        --------------------------------------------------------------------

        -- Rule 2 has no target here: mk and entryBound are variables of this
        -- telescope, so there is no description operator term in this file to
        -- seal. Both are sealed at their point of definition in SEPARATE
        -- opaque blocks, K6/NameBuild.agda:293 and :347, with the outer one
        -- sealed, which is K5's Track I refinement of rule 2b.

        namesOf : S → S
        namesOf W = mk sepᴳ (⋃ᴳ W) nameFo

        namesOf-name : (W τ : S) → ⟨ τ ∈ˢ namesOf W ⟩ → ⟨ IsNm τ ⟩
        namesOf-name W τ h =
          subst ⟨_⟩ (nameFo-reading τ) (mk-sat sepᴳ (⋃ᴳ W) nameFo τ h)

        namesOf-in : (W w τ : S) → ⟨ w ∈ˢ W ⟩ → ⟨ τ ∈ˢ w ⟩ → ⟨ IsNm τ ⟩
                   → ⟨ τ ∈ˢ namesOf W ⟩
        namesOf-in W w τ hwW hτw hτn =
          mk-in sepᴳ (⋃ᴳ W) nameFo τ (⋃ᴳ-in W w τ hwW hτw)
            (subst ⟨_⟩ (sym (nameFo-reading τ)) hτn)

        boundCode : S → S
        boundCode W = mk sepᴳ (entryBound collᴳ sepᴳ (namesOf W)) topFo

        boundName : S → Nm
        boundName W = boundCode W
                    , cut-name collᴳ sepᴳ (namesOf W) topFo (namesOf-name W)

        -- Every name of the sifted set is a value member of the bound, at any
        -- condition of G. This is the only place the bound's construction is
        -- read, and it reads it forwards only: nothing below asks what else
        -- the bound contains, which is what makes it a BOUND and not an image.

        boundName-mem : (W τ : S) (r : Cond) → ⟨ τ ∈ˢ namesOf W ⟩ → ⟨ G∈ r ⟩
                      → ⟨ τ ∈[G] boundCode W ⟩
        boundName-mem W τ r hτ hGr = active-value
          (active-in τ (boundCode W) r hGr
            (mk-in sepᴳ (entryBound collᴳ sepᴳ (namesOf W)) topFo
              (entry τ (cnd r))
              (entryBound-in collᴳ sepᴳ (namesOf W) τ (cnd r) hτ (cnd-carrier r))
              (topFo-true (entry τ (cnd r)))))

        --------------------------------------------------------------------
        -- Move 6. The field
        --------------------------------------------------------------------

        target : Ω
        target = ⋁ Nm (λ b → ⋀ Nm (λ x → (fst x ∈[G] fst α) ⇒
                   (⋁ Nm (λ y → (fst y ∈[G] fst b) ⊓ ((y ∷ x ∷ []) ⊨ φ)))))

        collect : ⟨ ⋀ Nm (λ x → (fst x ∈[G] fst α) ⇒
                    (⋁ Nm (λ y → (y ∷ x ∷ []) ⊨ φ))) ⟩
                → ⟨ target ⟩
        collect H = PT.rec (snd target) afterOuter (collᴳ domα psiFo outerPremise)
          where
            afterOuter :
                Σ[ W ∈ S ] ⟨ ⋀ S (λ x → (x ∈ˢ domα) ⇒
                  (⋁ S (λ w → (w ∈ˢ W) ⊓ ((w ∷ x ∷ []) ⊨ᴳ psiFo)))) ⟩
              → ⟨ target ⟩
            afterOuter (W , cover) = ∣ boundName W , bounds ∣₁
              where
                goal : Nm → Ω
                goal ζ = ⋁ Nm (λ y → (fst y ∈[G] boundCode W)
                                     ⊓ ((y ∷ ζ ∷ []) ⊨ φ))

                bounds : (ζ : Nm) → ⟨ fst ζ ∈[G] fst α ⟩ → ⟨ goal ζ ⟩
                bounds ζ hζ = PT.rec (snd (goal ζ)) viaActive
                                (subst ⟨_⟩ (∈-unfold (fst ζ) (fst α)) hζ)
                  where
                    viaActive : Σ[ x ∈ S ] ⟨ ‖Active‖ x (fst α)
                                             ⊓ (fst ζ ≈[G] x) ⟩
                              → ⟨ goal ζ ⟩
                    viaActive (x , hact , heq) =
                      PT.rec (snd (goal ζ)) viaEntry (active-out x (fst α) hact)
                      where
                        -- The member is value equal to a subname of α, and
                        -- that subname is a name in the ground set domα. The
                        -- congruence below is what crosses that gap; dropping
                        -- it proves a statement about the code x and not
                        -- about the given member.

                        viaEntry : Σ[ r ∈ Cond ]
                                     ⟨ G∈ r ⊓ (entry x (cnd r) ∈ˢ fst α) ⟩
                                 → ⟨ goal ζ ⟩
                        viaEntry (r₀ , _ , hentry) =
                          PT.rec (snd (goal ζ)) viaWitness (H ζ hζ)
                          where
                            hxD : ⟨ x ∈ˢ domα ⟩
                            hxD = dom-in (fst α) x (cnd r₀) hentry

                            ζ' : Nm
                            ζ' = x , domα-name x hxD

                            agr : (y : Nm) → Agree (y ∷ ζ ∷ []) (y ∷ ζ' ∷ [])
                            agr y zero       = ≈-refl (fst y)
                            agr y (suc zero) = heq

                            moveφ : (y : Nm)
                                  → ((y ∷ ζ ∷ []) ⊨ φ) ≡ ((y ∷ ζ' ∷ []) ⊨ φ)
                            moveφ y =
                              sat-cong φ (y ∷ ζ ∷ []) (y ∷ ζ' ∷ []) (agr y)

                            viaWitness : Σ[ y ∈ Nm ] ⟨ (y ∷ ζ ∷ []) ⊨ φ ⟩
                                       → ⟨ goal ζ ⟩
                            viaWitness (y , hy) =
                              PT.rec (snd (goal ζ)) viaCond
                                (subst ⟨_⟩ (truth-at φ (y ∷ ζ' ∷ []))
                                  (subst ⟨_⟩ (moveφ y) hy))
                              where
                                viaCond : Σ[ r ∈ Cond ]
                                            ⟨ G∈ r ⊓ forces r φ (y ∷ ζ' ∷ []) ⟩
                                        → ⟨ goal ζ ⟩
                                viaCond (r , hGr , hfr) =
                                  PT.rec (snd (goal ζ)) viaAdequate
                                    (cover x hxD)
                                  where
                                    hq : ⟨ cnd r ∈ˢ carrierᶠ ⟩
                                    hq = cnd-carrier r

                                    -- The condition is put back together from
                                    -- its code, which is where cndOf-cnd is
                                    -- spent and the only place it is.

                                    hA : ⟨ ⋁ S (hit (cnd r) x) ⟩
                                    hA = ∣ fst y , snd y
                                       , subst ⟨_⟩
                                           (sym (colΔ-reading φ y (cnd r) hq ζ'))
                                           (subst (λ u → ⟨ forces u φ (y ∷ ζ' ∷ []) ⟩)
                                             (sym (cndOf-cnd r)) hfr) ∣₁

                                    viaAdequate :
                                        Σ[ w ∈ S ] ⟨ (w ∈ˢ W)
                                          ⊓ ((w ∷ x ∷ []) ⊨ᴳ psiFo) ⟩
                                      → ⟨ goal ζ ⟩
                                    viaAdequate (w , hwW , hψ) = PT.map land
                                      (subst ⟨_⟩ (psiFo-reading w x) hψ
                                        (cnd r) hq hA)
                                      where
                                        land : Σ[ τ ∈ S ]
                                                 ⟨ (τ ∈ˢ w) ⊓ hit (cnd r) x τ ⟩
                                             → Σ[ z ∈ Nm ]
                                                 ⟨ (fst z ∈[G] boundCode W)
                                                   ⊓ ((z ∷ ζ ∷ []) ⊨ φ) ⟩
                                        land (τ , hτw , hτn , hτf) =
                                          τ' , hmem , hsat
                                          where
                                            τ' : Nm
                                            τ' = τ , hτn

                                            hmem : ⟨ fst τ' ∈[G] boundCode W ⟩
                                            hmem = boundName-mem W τ r
                                              (namesOf-in W w τ hwW hτw hτn) hGr

                                            hfτ : ⟨ forces r φ (τ' ∷ ζ' ∷ []) ⟩
                                            hfτ = subst
                                              (λ u → ⟨ forces u φ (τ' ∷ ζ' ∷ []) ⟩)
                                              (cndOf-cnd r)
                                              (subst ⟨_⟩
                                                (colΔ-reading φ τ' (cnd r) hq ζ')
                                                hτf)

                                            hsat : ⟨ (τ' ∷ ζ ∷ []) ⊨ φ ⟩
                                            hsat = subst ⟨_⟩ (sym (moveφ τ'))
                                              (subst ⟨_⟩
                                                (sym (truth-at φ (τ' ∷ ζ' ∷ [])))
                                                ∣ r , hGr , hfτ ∣₁)

      ------------------------------------------------------------------------
      -- THE FIELD, at the profile's own type
      ------------------------------------------------------------------------

      hasReplacement : OP.Collection
      hasReplacement α φ H = collect α φ H
