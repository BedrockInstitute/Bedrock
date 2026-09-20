{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track F. Separation at the poset extension structure.
--
-- WHAT IS PROVED HERE. The sixth field of OrdinaryZF, at the structure whose
-- carrier is the names, whose equality is the value relation and whose
-- membership is the value membership. The separated object is BUILT, from one
-- cut of Track A's name calculus, and its reading is proved in both
-- directions; nothing in this file assumes a name together with the
-- specification the field asks for, which is trap T-F2 of the architecture's
-- section 4.6 and would make the field a one line projection.
--
-- THE LOAD BEARING IDENTITY, and the reason this file may be written at all.
-- OrdinaryProfile does `open At S id using ( _⊨_ )`, and at the extension
-- structure the carrier is Nm and the constant interpretation is id. So the
-- satisfaction appearing inside OrdinaryProfile.Separation IS the satisfaction
-- of FOL.Semantics at this structure, the same function, and sat-cong applies
-- to the formula of the Separation obligation without a translation step. The
-- structure below is written as a record VALUE with exactly the four fields
-- K5/Structures.agda:285-291 gives it, so that at G it is definitionally the
-- landed one and no second copy of anything is declared.
--
-- THE CONDITIONALITY, stated once. Everything conditional reaches this file
-- through ONE parameter, `truth-at`, which is Track E2's export from its
-- module Conditional. The conditional row is:
--
--   * atom-∈ and atom-≐, obstruction O1, K5/Truth.agda:733-734;
--   * O3b, which is K3's tier-4 MemberImage taken flat as `image` and
--     `image-spec` by the TRANSLATION LAYER (TranslateForward.agda:21,
--     TranslateReverse.agda:73). The row is the five exports of that layer
--     together, trᴮ, trᴮ-name, ≈-agree, ∈-agree and ext-surjective, and not
--     ext-surjective alone: ext-surjective is itself PROVED, by one induction
--     on child-wf at K5/RoundTrip.agda:507, so charging O3b to it understates
--     what a supplier has to build;
--   * the per formula Supply, K5/Truth.agda:321-341, one Admits per
--     QUANTIFIER node including universal nodes;
--   * LEM ℓ, which the programme's single LEM (ℓ-suc ℓ) covers through
--     lowerLEM, so the net addition is zero.
--
-- This file names none of them, per the architecture's section 4.5, and
-- spends ground Separation and ground Collection only through Track A.
--
-- WHAT THIS TRACK MEASURED ABSENT, under rule 13. The architecture's section
-- 2.1 types this field as `Engine → isFilter G → Generic G → Separation`.
-- Neither filter hypothesis nor any dense meeting fact is used here and both
-- are removed: the forward direction reads one condition out of the truth
-- lemma and the backward direction puts one back, and the two conditions are
-- never merged, which is the only step directedness would be for. See the
-- break file K6/breaks/SepWrongCondition.agda-break, which is exactly the
-- attempt to identify them. Also absent and unused: forces-mono, forcesSet
-- with its two entailments (this track states its definability datum at
-- `forces` and never at the ground set of conditions below a Boolean
-- element), `paths`, ground Extensionality, and three of K3's seven kernel
-- facts, isPropChild, child-wf and the empty name.
--
-- RULE 15, THE TELESCOPE AUDIT. A field's TYPE cannot tell a legitimate proof
-- from one discharged out of a hypothesis nothing satisfies, so the telescope
-- is audited here parameter by parameter, in two classes. Class (i) is landed
-- or provable at this layer. Class (ii) is open at this layer but inhabited in
-- principle. The third class a reader might expect, FALSE at the intended
-- instance, is EMPTY here, and the parameter one would suspect first is not
-- even class (ii): well-foundedness of the extension's membership is a
-- THEOREM, ext-wf at K6/Refuted.agda:551, proved from child-wf with no
-- hypothesis on G, because Nm is a Σ-type and never a quotient. This file does
-- not name it, but the audit is what says so rather than a grep.
--
-- Class (i), 31 of the 35 parameters, every one filled from landed source in
-- K6/SeparationAtStructure.agda:
--   * module Names, six: K3's name kernel, shapes at K5/Structures.agda:
--     209-217 and :250;
--   * module AtG, thirteen: the value relation and its laws, Valuation.agda:
--     236-247, :294-295, :429-448, re-exported at K5/Structures.agda:275-281.
--     ∈-unfold is refl at K5;
--   * sat-cong, K5/Structures.agda:400, unconditional at any G : Sub;
--   * the two ground axioms Separation and Collection, which are profile
--     hypotheses and not a choice leak;
--   * Track A's nine, K6/NameBuild.agda:294-365 and K6/NameValid.agda:159.
--
-- Class (ii), four:
--   * forces and truth-at, Track E2's exports, open under the conditional row
--     above and inhabited exactly when that row is supplied;
--   * sepΔ and sepΔ-reading, the Definability Lemma for one fixed formula,
--     true at every genuine forcing extension, free at the coded completion,
--     unbuilt at the abstract frame.
--
-- Nothing here assumes that G meets anything, that the extension properly
-- extends the ground, or that a check name has the value of its set.
--
-- THE ADDITIONAL DATUM, AND IT IS A FINDING RATHER THAN A CONVENIENCE. The
-- separated name's weight at a subname χ is the set of conditions forcing
-- χ ∈ α ∧ φ(χ), and that set VARIES WITH χ. A single ground Separation can cut
-- the entries out of a ground bound only if the relation "r forces ψ(χ)" is
-- INTERNALLY DEFINABLE in the ground with parameters, for the one fixed
-- formula ψ. Track E2's printed interface exports `forces`, `forcesSet` and
-- its two entailments, and none of them is that. So this file carries one
-- further parameter pair, `sepΔ` and `sepΔ-reading`, which is exactly the
-- classical Definability Lemma for a fixed formula.
--
-- It is not the conclusion in disguise and it is not new mathematics. K4's
-- compiler already produces, for each FIXED parameter free formula, an
-- internal ground formula describing the formula's Boolean value together with
-- a proof that the two agree: `codeOf` at K4/Compile.agda:1209-1210 and
-- `describes` at :1212-1214, the third component of `record Interp` at :538.
-- What is missing at the ABSTRACT frame is the other half of the composite:
-- `below` and `i` are host fields of ForcingBase (K5/Frame.agda:199-201,
-- :176) with no internal description, although at the coded completion
-- `below` is `fst` and the description is Δ₀ in the code. So the datum is
-- free at the coded completion and unsupplied at the abstract frame, which is
-- the same shape as every other K6 conditionality and is recorded as such.
--
-- `sepΔ` is a HOST function from an object formula to a ground formula, the
-- shape `interp` already has at K4/Compile.agda:1061. It is not an internal
-- function on codes of formulas, which is the object non-claim 12 forbids.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; ⊥̇ )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
import OrdinaryProfile
import FOL.Semantics
import Cubical.HITs.PropositionalTruncation as PT

open PT using ( ∥_∥₁; ∣_∣₁ )

module K6.Separation {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The two ground axioms this track spends, as standalone arguments and never
-- as the OrdinaryZF record, which is ruling D4. Ground Separation pays for the
-- cut and ground Collection pays for the entry bound; both arrive through
-- Track A and neither is a hypothesis of anything else here. Track A measured
-- the ground profile for its own exports down to three, Separation, Collection
-- and PowerSet, and this track spends the two that PowerSet is not among.

open OrdinaryProfile 𝒮 using ( Separation; Collection )

-- Ground satisfaction, the one Track A's cut reads its formula in. It is
-- FOL.Semantics at the GROUND structure with the ground sets as their own
-- constants, which is the same instance GroundDescription and NameSpace use.

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
module SatG = SemG.At S id
open SatG public using () renaming ( _⊨_ to _⊨ᴳ_ )

--------------------------------------------------------------------------------
-- The name kernel, flat
--------------------------------------------------------------------------------

-- Four of K3's seven kernel facts, taken verbatim from the shapes at
-- K5/Structures.agda:209-217 and :250. The three this file never spends,
-- isPropChild, child-wf and the empty name with its specification, are absent
-- under rule 13: no declaration below mentions them.

module Names
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (carrierᶠ    : S)
  (IsNm        : S → Ω)
  (child-name  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ IsNm x ⟩)
  where

  -- Definitionally K5's Nm (K5/Structures.agda:263-264), K4's Fib IsNm and
  -- K3's Name. It is spelled out rather than imported because the structure
  -- below must be the landed record and not a copy related to it by a path.

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNm n))

------------------------------------------------------------------------------
-- The extension structure at one subset of the conditions
------------------------------------------------------------------------------

  -- The value relation reaches this file as five variables and six laws. Two
  -- of the laws, active-out and active-in, are the entry presentation of
  -- ‖Active‖ (Valuation.agda:245-247), stated as two entailments rather than
  -- as the Σ itself so that no proof below has to know what a condition is.

  module AtG
    (Cond        : Type ℓ)
    (cnd         : Cond → S)
    (cnd-carrier : (r : Cond) → ⟨ cnd r ∈ˢ carrierᶠ ⟩)
    (G∈          : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    (‖Active‖    : S → S → Ω)
    (≈-sym       : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩)
    (∈-congˡ     : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩)
    (∈-unfold    : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
    (active-value : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩)
    (active-out  : (x n : S) → ⟨ ‖Active‖ x n ⟩
                 → ⟨ ⋁ Cond (λ r → G∈ r ⊓ (entry x (cnd r) ∈ˢ n)) ⟩)
    (active-in   : (x n : S) (r : Cond) → ⟨ G∈ r ⟩ → ⟨ entry x (cnd r) ∈ˢ n ⟩
                 → ⟨ ‖Active‖ x n ⟩)
    where

    -- THE STRUCTURE. Four fields, the same four expressions K5 writes at
    -- K5/Structures.agda:285-291. At Nm := K5's Nm this record is
    -- definitionally K5's `structure`, so OrdinaryProfile.Separation of it is
    -- definitionally the field of OrdinaryZF 𝒮ᴾ[ G ].

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

    -- Environment agreement, in the shape K5 states it at
    -- K5/Structures.agda:376-377. It is spelled out here rather than taken as
    -- an opaque type so that the one instance this file builds, at a one
    -- element environment, can be given by a single clause.

    Agree : ∀ {k} → Vec Nm k → Vec Nm k → Type ℓ
    Agree {k} ν μ = (ix : Fin k) → ⟨ fst (lookup ix ν) ≈[G] fst (lookup ix μ) ⟩

------------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------------

    -- The telescope is the ledger. Reading it top to bottom: one law of the
    -- structure that K5 proves unconditionally; seven exports of Track A, each
    -- of which costs ground Separation and nothing classical; two exports of
    -- Track E2, which carry the whole conditionality of the package; and the
    -- definability datum, which is this track's own finding.

    module Cut
      -- K5/Structures.agda:400-402, unconditional, costs only G : Sub.
      (sat-cong : ∀ {k} (φ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                → (ν ⊨ φ) ≡ (μ ⊨ φ))
      -- The two ground axioms, spent only through Track A's two description
      -- operator terms and nowhere else in this file.
      (sepᴳ  : Separation)
      (collᴳ : Collection)
      -- Track A, five exports, each typed verbatim from the landed source.
      -- `dom` is K3's support with its two edge entailments, support-in at
      -- NameSupport.agda:542-544 and support-out at :534-535. Both are stated
      -- at a Child EDGE rather than at an entry, which is K3's shape and is
      -- why nothing below has to eliminate a truncation to reach a subname.
      (dom     : S → S)
      (dom-in  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ x ∈ˢ dom n ⟩)
      (dom-out : (n x : S) → ⟨ x ∈ˢ dom n ⟩ → Child x n)
      -- K6/NameBuild.agda:294, :325.
      (entryBound : Collection → Separation → (D : S) → S)
      (entryBound-in : (coll : Collection) (sep : Separation) (D x p : S)
                     → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                     → ⟨ entry x p ∈ˢ entryBound coll sep D ⟩)
      -- K6/NameBuild.agda:348, :355, :363.
      (mk : Separation → (bound : S) → Formula S 1 → S)
      (mk-in : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
             → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩ → ⟨ e ∈ˢ mk sep bound θ ⟩)
      (mk-sat : (sep : Separation) (bound : S) (θ : Formula S 1) (e : S)
              → ⟨ e ∈ˢ mk sep bound θ ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩)
      -- K6/NameValid.agda:159. Track A's own composition, not in the
      -- architecture: cut anything out of the entry bound of a set of names
      -- and the result is a name, with the truncation plumbing done once.
      (cut-name : (coll : Collection) (sep : Separation) (D : S) (θ : Formula S 1)
                → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsNm x ⟩)
                → ⟨ IsNm (mk sep (entryBound coll sep D) θ) ⟩)
      -- Track E2, module Conditional. The five conditional hypotheses are the
      -- parameters of THAT module and are named nowhere in this file.
      (forces   : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (truth-at : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
                → (ν ⊨ φ) ≡ ⋁ Cond (λ r → G∈ r ⊓ forces r φ ν))
      -- The definability datum. See the header.
      (sepΔ : (α : Nm) (φ : Formula Nm 1) → Formula S 1)
      (sepΔ-reading : (α : Nm) (φ : Formula Nm 1) (χ : Nm) (r : Cond)
                    → ((entry (fst χ) (cnd r) ∷ []) ⊨ᴳ sepΔ α φ)
                    ≡ forces r ((var zero ∈̇ con α) ∧̇ φ) (χ ∷ []))
      where

      -- The separation formula, and the conjunct that is not decorative. The
      -- left conjunct is `χ ∈ α`. Without it the construction produces a name
      -- whose members need not lie in α at all, because the entries are cut
      -- out of a BOUND on the domain of α and a bound is not a filter on
      -- membership; the break file K6/breaks/sep-drop-guard.agda-break holds
      -- the deliberately wrong version.

      module _ (α : Nm) (φ : Formula Nm 1) where

        sepFo : Formula Nm 1
        sepFo = (var zero ∈̇ con α) ∧̇ φ

        dom-α : S
        dom-α = dom (fst α)

        -- The cut. Rule 2 has no target here: `mk` and `entryBound` are
        -- variables of this telescope, so there is no description operator
        -- term in this file to seal. Both are sealed at their point of
        -- definition, K6/NameBuild.agda:347 and :293, in SEPARATE opaque
        -- blocks with the outer one sealed, which is K5's Track I refinement
        -- of rule 2b.

        sepCode : S
        sepCode = mk sepᴳ (entryBound collᴳ sepᴳ dom-α) (sepΔ α φ)

        -- THE READING OF THE CUT, in two entailments, and it is the theorem
        -- that says what the constructed object CONTAINS. Every entry of a
        -- subname at a condition forcing the separation formula is present,
        -- and every entry present carries that forcing fact back.

        sepCode-in : (χ : Nm) (r : Cond) → ⟨ fst χ ∈ˢ dom-α ⟩
                   → ⟨ forces r sepFo (χ ∷ []) ⟩
                   → ⟨ entry (fst χ) (cnd r) ∈ˢ sepCode ⟩
        sepCode-in χ r hd hf =
          mk-in sepᴳ (entryBound collᴳ sepᴳ dom-α) (sepΔ α φ)
            (entry (fst χ) (cnd r))
            (entryBound-in collᴳ sepᴳ dom-α (fst χ) (cnd r) hd (cnd-carrier r))
            (subst ⟨_⟩ (sym (sepΔ-reading α φ χ r)) hf)

        sepCode-out : (χ : Nm) (r : Cond)
                    → ⟨ entry (fst χ) (cnd r) ∈ˢ sepCode ⟩
                    → ⟨ forces r sepFo (χ ∷ []) ⟩
        sepCode-out χ r h =
          subst ⟨_⟩ (sepΔ-reading α φ χ r)
            (mk-sat sepᴳ (entryBound collᴳ sepᴳ dom-α) (sepΔ α φ)
              (entry (fst χ) (cnd r)) h)

        -- The cut is a name. Every member of it lies in the entry bound, so it
        -- is an entry of something in the domain of α at a condition, and
        -- everything in the domain of α is a child of α, hence a name.

        sepCode-name : ⟨ IsNm sepCode ⟩
        sepCode-name = cut-name collᴳ sepᴳ dom-α (sepΔ α φ) dom-name
          where
            dom-name : (x : S) → ⟨ x ∈ˢ dom-α ⟩ → ⟨ IsNm x ⟩
            dom-name x hx =
              child-name (fst α) (snd α) x (dom-out (fst α) x hx)

        sepName : Nm
        sepName = sepCode , sepCode-name

        -- THE TWO DIRECTIONS.
        --
        -- Forward. A value member of the cut is the value of a subname y that
        -- is active in it, so some condition r of G carries the entry of y.
        -- The reading of the cut turns that entry into `r forces sepFo at y`,
        -- and the truth lemma, read backwards, turns a forcing condition
        -- inside G into satisfaction. Satisfaction of a conjunction is a meet,
        -- so both conjuncts arrive at once, and both are moved from y to the
        -- given x by congruence: membership by ∈-congˡ and satisfaction by
        -- sat-cong. Dropping sat-cong here proves a statement about the CODE y
        -- and not about x.

        sep-fwd : (x : Nm) → ⟨ fst x ∈[G] sepCode ⟩
                → ⟨ (fst x ∈[G] fst α) ⊓ ((x ∷ []) ⊨ φ) ⟩
        sep-fwd x h = PT.rec (snd ((fst x ∈[G] fst α) ⊓ ((x ∷ []) ⊨ φ)))
          atSubname (subst ⟨_⟩ (∈-unfold (fst x) sepCode) h)
          where
            atSubname : Σ[ y ∈ S ] (⟨ ‖Active‖ y sepCode ⟩ × ⟨ fst x ≈[G] y ⟩)
                      → ⟨ (fst x ∈[G] fst α) ⊓ ((x ∷ []) ⊨ φ) ⟩
            atSubname (y , ha , he) =
              PT.rec (snd ((fst x ∈[G] fst α) ⊓ ((x ∷ []) ⊨ φ)))
                atCond (active-out y sepCode ha)
              where
                atCond : Σ[ r ∈ Cond ]
                           (⟨ G∈ r ⟩ × ⟨ entry y (cnd r) ∈ˢ sepCode ⟩)
                       → ⟨ (fst x ∈[G] fst α) ⊓ ((x ∷ []) ⊨ φ) ⟩
                atCond (r , hg , hm) = member , holds
                  where
                    hy : ⟨ IsNm y ⟩
                    hy = child-name sepCode sepCode-name y
                           (child-entry y (cnd r) sepCode hm)

                    χ : Nm
                    χ = y , hy

                    hsat : ⟨ (χ ∷ []) ⊨ sepFo ⟩
                    hsat = subst ⟨_⟩ (sym (truth-at sepFo (χ ∷ [])))
                             ∣ r , hg , sepCode-out χ r hm ∣₁

                    back : Agree (χ ∷ []) (x ∷ [])
                    back zero = ≈-sym he

                    member : ⟨ fst x ∈[G] fst α ⟩
                    member = ∈-congˡ (≈-sym he) (fst hsat)

                    holds : ⟨ (x ∷ []) ⊨ φ ⟩
                    holds = subst ⟨_⟩ (sat-cong φ (χ ∷ []) (x ∷ []) back) (snd hsat)

        -- Backward. The membership hypothesis produces a subname y of α active
        -- at some condition of G, hence a member of the domain of α and a
        -- child of α, hence a name. Satisfaction of the separation formula at
        -- y is then the pair of `y is a value member of α`, which is exactly
        -- what activity gives, and φ moved from x to y by sat-cong. The truth
        -- lemma, read forwards, produces a condition r of G forcing it, and
        -- the introduction half of the reading puts the entry of y at r into
        -- the cut.

        sep-bwd : (x : Nm) → ⟨ fst x ∈[G] fst α ⟩ → ⟨ (x ∷ []) ⊨ φ ⟩
                → ⟨ fst x ∈[G] sepCode ⟩
        sep-bwd x hm hφ = PT.rec (snd (fst x ∈[G] sepCode))
          atSubname (subst ⟨_⟩ (∈-unfold (fst x) (fst α)) hm)
          where
            atSubname : Σ[ y ∈ S ] (⟨ ‖Active‖ y (fst α) ⟩ × ⟨ fst x ≈[G] y ⟩)
                      → ⟨ fst x ∈[G] sepCode ⟩
            atSubname (y , ha , he) =
              PT.rec (snd (fst x ∈[G] sepCode)) atCond (active-out y (fst α) ha)
              where
                atCond : Σ[ r ∈ Cond ]
                           (⟨ G∈ r ⟩ × ⟨ entry y (cnd r) ∈ˢ fst α ⟩)
                       → ⟨ fst x ∈[G] sepCode ⟩
                atCond (q , hq , hentry) =
                  PT.rec (snd (fst x ∈[G] sepCode)) place
                    (subst ⟨_⟩ (truth-at sepFo (χ ∷ [])) hsat)
                  where
                    hy : ⟨ IsNm y ⟩
                    hy = child-name (fst α) (snd α) y
                           (child-entry y (cnd q) (fst α) hentry)

                    χ : Nm
                    χ = y , hy

                    hd : ⟨ y ∈ˢ dom-α ⟩
                    hd = dom-in (fst α) (snd α) y
                           (child-entry y (cnd q) (fst α) hentry)

                    fwd : Agree (x ∷ []) (χ ∷ [])
                    fwd zero = he

                    hsat : ⟨ (χ ∷ []) ⊨ sepFo ⟩
                    hsat = active-value ha
                         , subst ⟨_⟩ (sat-cong φ (x ∷ []) (χ ∷ []) fwd) hφ

                    place : Σ[ r ∈ Cond ]
                              (⟨ G∈ r ⟩ × ⟨ forces r sepFo (χ ∷ []) ⟩)
                          → ⟨ fst x ∈[G] sepCode ⟩
                    place (r , hg , hf) =
                      ∈-congˡ (≈-sym he)
                        (active-value
                          (active-in y sepCode r hg (sepCode-in χ r hd hf)))

        -- The specification, as one path in Ω. This is the sentence "the
        -- separated set contains exactly the members of α satisfying φ", and
        -- it is what the field's biconditional is built from.

        sepName-spec : (x : Nm)
                     → (fst x ∈[G] sepCode)
                     ≡ ((fst x ∈[G] fst α) ⊓ ((x ∷ []) ⊨ φ))
        sepName-spec x =
          ⇔toPath (sep-fwd x) (λ hq → sep-bwd x (fst hq) (snd hq))

      -- THE FIELD. The witness is the constructed name and the biconditional
      -- is the specification read through K1's bridge, which is the only step
      -- of this file that is not about forcing.

      hasSeparation : OP.Separation
      hasSeparation α φ =
        ∣ sepName α φ
        , OP.spec-to-iff (sepName α φ)
            (λ x → (fst x ∈[G] fst α) ⊓ ((x ∷ []) ⊨ φ))
            (sepName-spec α φ)
        ∣₁
