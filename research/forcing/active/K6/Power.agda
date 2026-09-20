{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track G. THE POWER SET AXIOM AT THE EXTENSION STRUCTURE 𝒮ᴾ[ G ].
--
-- WHAT THIS FILE DELIVERS. One theorem, hasPower, whose type is
-- OrdinaryProfile.PowerSet 𝒮ᴾ and nothing narrower. The field type is
-- transcribed here so that no reader has to trust a summary
-- (OrdinaryProfile.agda:74-78):
--
--   PowerSet = (a : S) → ⟨ ⋁ S (λ v → ⋀ S (λ x → iff (x ∈ˢ v)
--                              (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a))))) ⟩
--
-- The inner ⋀ S ranges over EVERY element of the carrier, which at 𝒮ᴾ[ G ] is
-- EVERY name, not over the candidate domain. Trap T-G2 is met by the machine:
-- the declaration below carries that type, and the two helper lemmas of the
-- restricted shape, inPower and covering, are stated with the unrestricted
-- ⋀ Nameᴾ hypothesis as well.
--
-- THE STRUCTURE IS BUILT HERE AS A RECORD LITERAL AND K5.Structures IS NOT
-- APPLIED. Part 4 of the architecture forbids applying K5.Structures outside a
-- seam probe. 𝒮ᴾ below is the same four-field record literal as
-- K5/Structures.agda:288-291, written from the flat spine parameters. The seam
-- probe K6/PowerAtNames.agda checks 𝒮ᴾ ≡ 𝒮ᴾ[ G ] by refl, with every one of
-- the value laws below filled by K5's own export.
--
-- ---------------------------------------------------------------------
-- THE CENTRAL FINDING. O7, THE DEFINABILITY DATUM, NAMED IN THE TELESCOPE
-- ---------------------------------------------------------------------
--
-- The brief fixes the conditionality ledger at atom-∈, atom-≐, the O3b
-- translation layer, the per formula Supply and LEM ℓ, and says a sixth thing
-- is a finding. There is a sixth thing and it is `powΔ` below. It was measured
-- here independently of Track F, which hit the same wall in hasSeparation; the
-- coordinator has since named it O7 and classed it (ii), open at this layer and
-- inhabited in principle. It is the classical Definability Lemma for the
-- forcing relation, and the general repair is an internal description of
-- `below` or of `i`, which composed with K4's codeOf (K4/Compile.agda:1209) and
-- describes (:1212) would discharge every instance of it at once. That is K8's
-- or a Track E2 addendum, not this track's.
--
-- Power Set is the one axiom whose proof must NORMALIZE an arbitrary subset of
-- α to a name whose children lie in the domain of α, and the normalized name
-- is
--
--     { ⟨ y , r ⟩ : y a child of α, r a condition forcing y ∈ χ }.
--
-- Producing that as a GROUND SET is one Separation against a GROUND FORMULA
-- that reads "r forces y ∈ χ", uniformly in y and r with α and χ as constants.
-- No such formula exists in K1 to K5, and the ledger's five rows do not give
-- one:
--
--  * atom-∈ and atom-≐ (K5/Truth.agda:733-734) are HOST PATHS in Ω relating
--    the B side value relation to the compiled atomic value. They carry no
--    internal formula at all. The internal formula is the OTHER half of the
--    same O1 record, memAtˢ / memΔ / mem-sound / mem-total at
--    K4/AtomicGraph.agda:412-432, whose single route table→graph (:719-720)
--    has no supplier either.
--  * The O3b translation layer (TranslateForward.agda:21,
--    TranslateReverse.agda:73) moves names between the two sides. It defines
--    nothing internally.
--  * Supply is Admits data at Type (ℓ-suc ℓ) (K4/ValueSets.agda:291) and
--    produces value SETS, never a graph.
--  * The frame's own forcing relation is host level throughout:
--    p ⊩ᴮ b is i p ≤ᴮ b (K5/Frame.agda:255) and `below`, `i` and `⊩ᴮ` are all
--    fields or host functions of ForcingBase (K5/Frame.agda:150-215). A census
--    over the compile root for an internal graph of `below` or of `i` returns
--    nothing; denseBelowΔ (K5/Frame.agda:85-86) is a Δ predicate on a SET
--    argument, not a function graph.
--
-- So `powΔ` is carried as an explicit parameter with its reading theorem,
-- and the report states it as the finding rather than smuggling it in. It is
-- true at a genuine forcing extension, being the ordinary definability lemma
-- for the atomic forcing relation, so it passes rule 15: unproved at this
-- layer, not false at the instance.
--
-- THE MAXIMUM PRINCIPLE IS NOT NEEDED AND IS NOT NAMED. Fullness,
-- MaximumPrinciple, MaximumPrincipleContract, Refinement, Mixture,
-- MixtureSupply, WitnessSpec, ValueCover, ElementPrinciple, Separated and
-- AdequateDomain all measure 0 in this file.
--
-- ---------------------------------------------------------------------
-- WHERE THE PROOF DEPARTS FROM THE ARCHITECTURE'S SECTION 4.7, AND WHY
-- ---------------------------------------------------------------------
--
-- Section 4.7 builds ONE name whose entries are the candidates weighted by the
-- conditions forcing "candidate ⊆ α", and reads the field's iff off that name.
-- This file uses the ordinary ZF route instead: a BOUNDING name that contains
-- every subset of α, cut down by Separation AT 𝒮ᴾ[ G ]. The reason is a
-- hypothesis count and not a preference.
--
--  * The 4.7 name needs the weight ⟦ χ' ⊆ α ⟧ to be a ground set uniformly in
--    the bound candidate χ'. That is definability of forcing for a formula
--    with a universal quantifier over the whole carrier.
--  * The bounding name needs only the ATOMIC half, which is `powΔ`.
--
-- The route taken here is therefore strictly weaker in hypotheses. It pays one
-- price: it consumes hasSeparation at the same structure, which is Track F's
-- deliverable under the same Engine, so it adds no ledger row but it does add
-- a dependency the architecture's graph does not have.
--
-- A SECOND DEPARTURE, AND IT SHORTENS THE PROOF. Section 4.7 normalizes AT A
-- CONDITION p forcing χ ⊆ α, then argues with forces-mono and the filter's
-- directedness. Normalizing AT G instead makes both inclusions run through the
-- truth lemma directly, and forces-mono, forcesSet, the filter's upward and
-- directed clauses and every genericity fact drop out. What survives of 4.7's
-- hypotheses on G is ⟨ positive G ⟩ alone, spent once, in inPower.
--
-- ---------------------------------------------------------------------
-- THE PROPER CLASS TRAP, MET BY A TYPE AND NOT BY A PROMISE
-- ---------------------------------------------------------------------
--
-- roadmap:205 forbids collecting a proper class of names by host fiat. The
-- candidate domain of this proof is `powerDom α : S`. It is an ELEMENT OF THE
-- GROUND CARRIER, built as
--
--     powerDom α = mk sep (entryBound coll sep (candidates sep pow (fst α))) ⊤̇
--
-- from Track A's landed operations, so the ground axioms that keep it a set
-- are ground PowerSet inside `candidates` (which is separateOf over
-- nameBound pow (support σ), NameSpace.agda:640-646), ground Separation and
-- ground Collection inside `entryBound` and `mk`. All three are standalone
-- arguments below, per ruling D4. `Pairing` and `Union` are not named: rule 13,
-- and Track A measured the same reduction from five to three.
--
-- THE CHECK A REVIEWER RUNS MECHANICALLY, and it is a grep and a reading:
--
--   1. The candidate domain is `powerDom : Nameᴾ → S`. Its RESULT TYPE is the
--      ground carrier, so the domain is a set by typing and there is nothing
--      to argue about. Every quantifier over candidates in every proof below
--      is the ground membership ⟨ χ ∈ˢ powerDom α ⟩, an Ω.
--   2. `grep -cE 'Σ\[ [a-zA-Z]+ ∈ S \]' <this file, comments stripped>`
--      MEASURED 8, NOT 0, and the brief's expectation of 0 is wrong for this
--      file. Rule 14: the measurement is printed rather than the expectation.
--      Each of the eight is one of exactly two shapes, and neither is a
--      candidate domain. Two are the TYPES Cond and Nameᴾ, which are K3's
--      Conditions (Valuation.agda:121-122) and K5's Nm
--      (K5/Structures.agda:259-260) and are checked against them by refl in
--      K6/PowerAtNames.agda. The other six are the untruncated PAYLOAD of a
--      ⋁ S or a ∥ ∥₁ standing under a PT.rec whose motive is `snd` of an Ω.
--      That is the structural counterpart of clause 1.3, and it holds: all
--      eight PT.rec targets in this file are `snd (…)` of an Ω and both
--      PT.map targets are truncations, so no truncated sigma is eliminated
--      into data anywhere.
--   3. `grep -cE 'imageOn|MemberImage|\.image\b|image-spec'` MEASURED 0,
--      comments stripped. This is the silent O3b import: a filler of
--      graph→image that calls imageOn typechecks, because ImageClass
--      (NameImage.agda:86-87) and imageOn-spec (StandardNames.agda:284-285)
--      have the identical shape. This file applies no image route at all; it
--      takes Track A's operations as parameters, and K6/PowerAtNameBuild.agda
--      fills every one of them with a Track A export.
--   4. `grep -cE 'K6.NameBuild|K6.NameValid|K5\.'` MEASURED 0 outside
--      comments. No producer module is applied here.
--
-- RULE 2 AND 2b, AND WHY T-G1 DOES NOT ARISE. powerDom nests `mk` outside
-- `entryBound` outside `candidates`, three description-operator terms deep,
-- and the type of powerName names all three. The seal is not written here
-- because it cannot be: `mk`, `entryBound` and `candidates` are VARIABLES in
-- this file, and a variable cannot unfold, which is a stronger seal than
-- `opaque`. Track A seals all three at the point of definition. The measured
-- consequence is that this file costs 2.22 s at 536 MB rather than not
-- finishing, and `opaque` measures 0 here.
--
-- The forbidden alternative is transcribed and refuted in
-- K6/breaks/PowerHostDomain.agda-break, and the vacuity control is the
-- positive theorem power-contains-self below.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
import OrdinaryProfile
import FOL.Semantics
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ ; ∣_∣₁ )

module K6.Power {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open OrdinaryProfile 𝒮 using ( Separation ; Collection ; PowerSet )

private
  module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮

-- Ground satisfaction, the language Track A's cut formulas are read in.
open SemG.At S id using () renaming ( _⊨_ to _⊨ᴳ_ )

-- The name kernel and the poset side's two name parameters, verbatim from
-- K5/Structures.agda:209-217 and :777-784, minus the entries rule 13 removes.
-- isPropChild, child-wf, ∅ᴺ, ∅ᴺ-spec, the condition order and its three laws
-- are not named below, because no proof below spends one.

module Kernel
  (entry       : S → S → S)
  (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (Child       : S → S → Type ℓ)
  (child-weight : (x n : S) → Child x n → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  (carrierᶠ    : S)
  (IsNameᴾ     : S → Ω)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  -- Conditions and names, both definitionally K3's and K5's: Conditions is
  -- Valuation.agda:121-122 and Nm is K5/Structures.agda:259-260. No third copy
  -- of either is declared; the seam probe checks both by refl.

  Cond : Type ℓ
  Cond = Σ[ p ∈ S ] ⟨ p ∈ˢ carrierᶠ ⟩

  Nameᴾ : Type ℓ
  Nameᴾ = Σ[ n ∈ S ] ⟨ IsNameᴾ n ⟩

  isSetNameᴾ : isSet Nameᴾ
  isSetNameᴾ = isSetΣSndProp isSetS (λ n → snd (IsNameᴾ n))

  ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (paths x y)

  -- The value layer at one subset of the conditions. Active and ‖Active‖ are
  -- Valuation.agda:249-253 written out, because both directions of the
  -- unfolding are spent below; the value relations themselves and their eight
  -- laws are parameters, per Part 4's rule that no K6 file applies K5.

  module At
    (G             : Cond → Ω)
    (_≈[G]_ _∈[G]_ : S → S → Ω)
    where

    Active : S → S → Type ℓ
    Active x n = Σ[ p ∈ S ] Σ[ hp ∈ ⟨ p ∈ˢ carrierᶠ ⟩ ]
                   (⟨ entry x p ∈ˢ n ⟩ × ⟨ G (p , hp) ⟩)

    ‖Active‖ : S → S → Ω
    ‖Active‖ x n = ∥ Active x n ∥₁ , PT.squash₁

    -- THE STRUCTURE, the same record literal as K5/Structures.agda:288-291.

    𝒮ᴾ : ZFStructure (hPropAlgebra ℓ)
    𝒮ᴾ = record
      { S      = Nameᴾ
      ; isSetS = isSetNameᴾ
      ; _≈ˢ_   = λ σ τ → fst σ ≈[G] fst τ
      ; _∈ˢ_   = λ σ τ → fst σ ∈[G] fst τ }

    module Laws
      -- K5/Structures.agda:275-279, the congruence kit, flat. Verbatim from
      -- Valuation.agda:429-475.
      (≈-sym         : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩)
      (≈-trans       : {m n r : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ m ≈[G] r ⟩)
      (∈-congˡ       : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩)
      (value-extensional : (m n : S) → ((r : S) → (r ∈[G] m) ≡ (r ∈[G] n))
                         → ⟨ m ≈[G] n ⟩)
      (∈-unfold      : (m n : S) → (m ∈[G] n)
                     ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
      (active-child  : (x n : S) → ⟨ ‖Active‖ x n ⟩ → Child x n)
      (active-value  : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩)
      (entry-value   : (n x p : S) (hp : ⟨ p ∈ˢ carrierᶠ ⟩) → ⟨ G (p , hp) ⟩
                     → ⟨ entry x p ∈ˢ n ⟩ → ⟨ x ∈[G] n ⟩)
      where

      -- Satisfaction at 𝒮ᴾ. This is the one load-bearing identity of the
      -- shared spine: OrdinaryProfile does `open At S id`, and at 𝒮ᴾ the
      -- structure's S is Nameᴾ and ι is id, so the _⊨_ inside
      -- OrdinaryProfile.Separation 𝒮ᴾ IS the _⊨ᴾ_ named here.

      private
        module SemP = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴾ

      open SemP.At Nameᴾ id using () renaming ( _⊨_ to _⊨ᴾ_ )

      -- The two object-language abbreviations the proof needs, and only these
      -- two. `memφ` is atomic membership at slots 0 and 1; `subφ α` says slot 0
      -- is a subset of the constant α. Both readings are refl and the two
      -- declarations below say so, which is rule 6's protection: a formula with
      -- a mis-ordered slot still elaborates at uniform depth and nothing but a
      -- reading theorem would catch it.

      memφ : Formula Nameᴾ 2
      memφ = var zero ∈̇ var (suc zero)

      subφ : Nameᴾ → Formula Nameᴾ 1
      subφ α = ∀̇ ((var zero ∈̇ var (suc zero)) ⇒̇ (var zero ∈̇ con α))

      memφ-reading : (y χ : Nameᴾ) → ((y ∷ χ ∷ []) ⊨ᴾ memφ) ≡ (fst y ∈[G] fst χ)
      memφ-reading y χ = refl

      subφ-reading : (α χ : Nameᴾ) → ((χ ∷ []) ⊨ᴾ subφ α)
                   ≡ ⋀ Nameᴾ (λ y → (fst y ∈[G] fst χ) ⇒ (fst y ∈[G] fst α))
      subφ-reading α χ = refl

      -- ---------------------------------------------------------------
      -- The conditional layer. Ruling D1: the signature is the ledger.
      -- ---------------------------------------------------------------

      module Conditional
        -- Positivity of G, and NOT isFilter. Section 2.4 of the architecture
        -- records that K3 charges only ⟨ positive G ⟩ where a track is tempted
        -- to charge a filter; the same over-charge is available here and is
        -- declined. This is ForcingNotion.agda:160-161 written flat, and
        -- K6/PowerAtNames.agda derives it from a filter by filter-positive.
        (pos : ⟨ ⋁ Cond (λ q → G q) ⟩)

        -- The three ground axioms, standalone per ruling D4. Ground Pairing
        -- and ground Union are not named: rule 13, the same reduction from
        -- five to three that Track A measured.
        (sep  : Separation)
        (coll : Collection)
        (pow  : PowerSet)

        -- Track A, K6/NameBuild.agda and K6/NameValid.agda, typed verbatim
        -- from its landed exports. Nothing here is applied; all seven are
        -- variables, so Track A cannot drift into this file silently.
        (mk         : Separation → (bound : S) → Formula S 1 → S)
        (mk-in      : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
                    → ⟨ e ∈ˢ bound ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩
                    → ⟨ e ∈ˢ mk sep' bound θ ⟩)
        (mk-bound   : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
                    → ⟨ e ∈ˢ mk sep' bound θ ⟩ → ⟨ e ∈ˢ bound ⟩)
        (mk-sat     : (sep' : Separation) (bound : S) (θ : Formula S 1) (e : S)
                    → ⟨ e ∈ˢ mk sep' bound θ ⟩ → ⟨ (e ∷ []) ⊨ᴳ θ ⟩)
        (entryBound : Collection → Separation → (D : S) → S)
        (entryBound-in : (coll' : Collection) (sep' : Separation) (D x p : S)
                       → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
                       → ⟨ entry x p ∈ˢ entryBound coll' sep' D ⟩)
        (entryBound-out : (coll' : Collection) (sep' : Separation) (D e : S)
                        → ⟨ e ∈ˢ entryBound coll' sep' D ⟩
                        → ⟨ ⋁ S (λ x → (x ∈ˢ D) ⊓
                              ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))) ⟩)
        (cut-name   : (coll' : Collection) (sep' : Separation) (D : S)
                      (θ : Formula S 1)
                    → ((x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsNameᴾ x ⟩)
                    → ⟨ IsNameᴾ (mk sep' (entryBound coll' sep' D) θ) ⟩)
        -- K3's support, NameSupport.agda:507-568, flat.
        (support    : S → S)
        (candidates : Separation → PowerSet → (σ : S) → S)
        (candidates-name : (sep' : Separation) (pow' : PowerSet) (σ χ : S)
                         → ⟨ χ ∈ˢ candidates sep' pow' σ ⟩ → ⟨ IsNameᴾ χ ⟩)
        (candidates-contains : (sep' : Separation) (pow' : PowerSet) (σ χ : S)
                             → ⟨ IsNameᴾ χ ⟩
                             → ((x : S) → Child x χ → ⟨ x ∈ˢ support σ ⟩)
                             → ⟨ χ ∈ˢ candidates sep' pow' σ ⟩)

        (support-in    : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n
                       → ⟨ x ∈ˢ support n ⟩)
        (support-valid : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S)
                       → ⟨ x ∈ˢ support n ⟩ → ⟨ IsNameᴾ x ⟩)

        -- Track E2, K6/ForcesTruth.agda. Two exports are spent and no more:
        -- forces-mono, forcesSet, forcesSet-in and forcesSet-out are NOT named,
        -- because the normalization below is taken at G and never refines a
        -- condition.
        (forces   : ∀ {k} → Cond → Formula Nameᴾ k → Vec Nameᴾ k → Ω)
        (truth-at : ∀ {k} (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k)
                  → (ν ⊨ᴾ φ) ≡ ⋁ Cond (λ p → G p ⊓ forces p φ ν))

        -- O7, THE DEFINABILITY DATUM. The coordinator's ruling names it and
        -- classes it (ii), open at this layer and inhabited in principle, free
        -- at the coded completion where `below` is `fst`. The spelling is
        -- Track F's `sepΔ` adapted to this track's formula rather than a new
        -- shape, per part 2 of that ruling. TWO DIFFERENCES, both stated:
        -- Track F's second index is the Separation formula φ and this track's
        -- is the second NAME χ, because the formula here is the fixed atomic
        -- one; and the subname slot is a Nameᴾ in both, so `fst y` here is
        -- Track F's `fst χ` and `fst r` here is Track F's `cnd r`.
        (powΔ : Nameᴾ → Nameᴾ → Formula S 1)
        (powΔ-reading : (α χ y : Nameᴾ) (r : Cond)
                      → ((entry (fst y) (fst r) ∷ []) ⊨ᴳ powΔ α χ)
                      ≡ forces r (var zero ∈̇ con χ) (y ∷ []))

        -- Track F, K6/Separation.agda, at the SAME structure. This is the one
        -- consumer the 4.7 route would not have had, and it is what buys the
        -- weaker sixth row. It carries the same Engine that Track E2's two
        -- exports above carry, so it adds no ledger row of its own.
        (sepᴾ : OrdinaryProfile.Separation 𝒮ᴾ)
        where

        -- ---------------------------------------------------------------
        -- Step one. The truth lemma at the atomic membership formula.
        -- ---------------------------------------------------------------

        -- Not new mathematics: truth-at read at memφ, whose reading is refl.
        -- It is named because both directions of the covering proof spend it
        -- and neither should re-derive it.

        truth-∈ : (y χ : Nameᴾ) → (fst y ∈[G] fst χ)
                ≡ ⋁ Cond (λ r → G r ⊓ forces r (var zero ∈̇ con χ) (y ∷ []))
        truth-∈ y χ = truth-at (var zero ∈̇ con χ) (y ∷ [])

        -- ---------------------------------------------------------------
        -- Step two. The normalized name, built from Track A and nothing else.
        -- ---------------------------------------------------------------

        norm : Nameᴾ → Nameᴾ → S
        norm α χ = mk sep (entryBound coll sep (support (fst α))) (powΔ α χ)

        norm-name : (α χ : Nameᴾ) → ⟨ IsNameᴾ (norm α χ) ⟩
        norm-name α χ = cut-name coll sep (support (fst α)) (powΔ α χ)
                          (support-valid (fst α) (snd α))

        -- Every child of the normalized name lies in the domain of α. This is
        -- what places it in the candidate set, and it is the only bound the
        -- proof needs; the weights need no bound because entryBound already
        -- confines them to carrierᶠ.

        norm-child : (α χ : Nameᴾ) (x : S) → Child x (norm α χ)
                   → ⟨ x ∈ˢ support (fst α) ⟩
        norm-child α χ x edge =
          PT.rec (snd (x ∈ˢ support (fst α))) viaEntry (child-weight x (norm α χ) edge)
          where
            viaEntry : Σ[ b ∈ S ] ⟨ entry x b ∈ˢ norm α χ ⟩
                     → ⟨ x ∈ˢ support (fst α) ⟩
            viaEntry (b , he) =
              PT.rec (snd (x ∈ˢ support (fst α)))
                (λ { (x' , hx' , inner) → PT.rec (snd (x ∈ˢ support (fst α)))
                       (λ { (p , _ , eq) →
                              subst (λ u → ⟨ u ∈ˢ support (fst α) ⟩)
                                (sym (fst (entry-inj (≈ˢ→≡ eq)))) hx' })
                       inner })
                (entryBound-out coll sep (support (fst α)) (entry x b)
                  (mk-bound sep (entryBound coll sep (support (fst α)))
                    (powΔ α χ) (entry x b) he))

        norm-in : (α χ y : Nameᴾ) (r : Cond) → ⟨ fst y ∈ˢ support (fst α) ⟩
                → ⟨ forces r (var zero ∈̇ con χ) (y ∷ []) ⟩
                → ⟨ entry (fst y) (fst r) ∈ˢ norm α χ ⟩
        norm-in α χ y r hsupp hf =
          mk-in sep (entryBound coll sep (support (fst α))) (powΔ α χ)
            (entry (fst y) (fst r))
            (entryBound-in coll sep (support (fst α)) (fst y) (fst r) hsupp (snd r))
            (subst ⟨_⟩ (sym (powΔ-reading α χ y r)) hf)

        norm-out : (α χ y : Nameᴾ) (r : Cond)
                 → ⟨ entry (fst y) (fst r) ∈ˢ norm α χ ⟩
                 → ⟨ forces r (var zero ∈̇ con χ) (y ∷ []) ⟩
        norm-out α χ y r he =
          subst ⟨_⟩ (powΔ-reading α χ y r)
            (mk-sat sep (entryBound coll sep (support (fst α))) (powΔ α χ)
              (entry (fst y) (fst r)) he)

        -- ---------------------------------------------------------------
        -- Step three. THE SUBSTANTIVE PROOF: normalization covers.
        -- ---------------------------------------------------------------

        -- Every subset of α has the same value as a name whose children lie in
        -- the domain of α. This is the whole content of Bell 1.38 on the poset
        -- side, and architecture section 3.5 is right that landing in the
        -- candidate set is the only direction the argument uses.

        norm-sub : (α χ : Nameᴾ) (z : S)
                 → ⟨ z ∈[G] norm α χ ⟩ → ⟨ z ∈[G] fst χ ⟩
        norm-sub α χ z hz =
          PT.rec (snd (z ∈[G] fst χ)) fromActive
            (subst ⟨_⟩ (∈-unfold z (norm α χ)) hz)
          where
            fromActive : Σ[ y ∈ S ] ⟨ ‖Active‖ y (norm α χ) ⊓ (z ≈[G] y) ⟩
                       → ⟨ z ∈[G] fst χ ⟩
            fromActive (y , hact , hzy) = ∈-congˡ (≈-sym hzy) inχ
              where
                hy : ⟨ IsNameᴾ y ⟩
                hy = child-nameᴾ (norm α χ) (norm-name α χ) y
                       (active-child y (norm α χ) hact)

                inχ : ⟨ y ∈[G] fst χ ⟩
                inχ = subst ⟨_⟩ (sym (truth-∈ (y , hy) χ))
                        (PT.map
                          (λ { (p , hp , member , hG) →
                                 (p , hp) , hG
                               , norm-out α χ (y , hy) (p , hp) member })
                          hact)

        norm-sup : (α χ : Nameᴾ)
                 → ⟨ ⋀ Nameᴾ (λ y → (fst y ∈[G] fst χ) ⇒ (fst y ∈[G] fst α)) ⟩
                 → (z : S) → ⟨ z ∈[G] fst χ ⟩ → ⟨ z ∈[G] norm α χ ⟩
        norm-sup α χ h⊆ z hz =
          PT.rec (snd (z ∈[G] norm α χ)) fromActive
            (subst ⟨_⟩ (∈-unfold z (fst χ)) hz)
          where
            fromActive : Σ[ y ∈ S ] ⟨ ‖Active‖ y (fst χ) ⊓ (z ≈[G] y) ⟩
                       → ⟨ z ∈[G] norm α χ ⟩
            fromActive (y , hact , hzy) =
              PT.rec (snd (z ∈[G] norm α χ)) inDomain
                (subst ⟨_⟩ (∈-unfold y (fst α)) inα)
              where
                hy : ⟨ IsNameᴾ y ⟩
                hy = child-nameᴾ (fst χ) (snd χ) y (active-child y (fst χ) hact)

                inχ : ⟨ y ∈[G] fst χ ⟩
                inχ = active-value hact

                inα : ⟨ y ∈[G] fst α ⟩
                inα = h⊆ (y , hy) inχ

                -- y is a value-member of α, so it is value-equal to an ACTIVE
                -- child w of α, and an active child of a name lies in its
                -- support. That is the only place the domain bound enters, and
                -- it is where the candidate domain gets its ground code.
                inDomain : Σ[ w ∈ S ] ⟨ ‖Active‖ w (fst α) ⊓ (y ≈[G] w) ⟩
                         → ⟨ z ∈[G] norm α χ ⟩
                inDomain (w , hactw , hyw) =
                  PT.rec (snd (z ∈[G] norm α χ)) fromForcing
                    (subst ⟨_⟩ (truth-∈ (w , hw) χ) inχ')
                  where
                    hw : ⟨ IsNameᴾ w ⟩
                    hw = child-nameᴾ (fst α) (snd α) w
                           (active-child w (fst α) hactw)

                    hsupp : ⟨ w ∈ˢ support (fst α) ⟩
                    hsupp = support-in (fst α) (snd α) w
                              (active-child w (fst α) hactw)

                    inχ' : ⟨ w ∈[G] fst χ ⟩
                    inχ' = ∈-congˡ hyw inχ

                    fromForcing :
                        Σ[ r ∈ Cond ] ⟨ G r ⊓ forces r (var zero ∈̇ con χ)
                                                ((w , hw) ∷ []) ⟩
                      → ⟨ z ∈[G] norm α χ ⟩
                    fromForcing (r , hrG , hf) =
                      ∈-congˡ (≈-sym (≈-trans hzy hyw))
                        (entry-value (norm α χ) w (fst r) (snd r) hrG
                          (norm-in α χ (w , hw) r hsupp hf))

        covering : (α χ : Nameᴾ)
                 → ⟨ ⋀ Nameᴾ (λ y → (fst y ∈[G] fst χ) ⇒ (fst y ∈[G] fst α)) ⟩
                 → ⟨ fst χ ≈[G] norm α χ ⟩
        covering α χ h⊆ = value-extensional (fst χ) (norm α χ)
          (λ z → ⇔toPath (norm-sup α χ h⊆ z) (norm-sub α χ z))

        -- ---------------------------------------------------------------
        -- Step four. The bounding name, and what it CONTAINS.
        -- ---------------------------------------------------------------

        -- powerDom α : S. A GROUND SET and not a host collection. This line is
        -- the proper class check, and it is a type rather than a promise.

        powerDom : Nameᴾ → S
        powerDom α =
          mk sep (entryBound coll sep (candidates sep pow (fst α))) ⊤̇

        powerName : Nameᴾ → Nameᴾ
        powerName α = powerDom α
                    , cut-name coll sep (candidates sep pow (fst α)) ⊤̇
                        (candidates-name sep pow (fst α))

        -- Every subset of α is a member of the bounding name. This is the
        -- vacuity control and it is a theorem rather than a remark.

        inPower : (α χ : Nameᴾ)
                → ⟨ ⋀ Nameᴾ (λ y → (fst y ∈[G] fst χ) ⇒ (fst y ∈[G] fst α)) ⟩
                → ⟨ fst χ ∈[G] powerDom α ⟩
        inPower α χ h⊆ = PT.rec (snd (fst χ ∈[G] powerDom α)) atCondition pos
          where
            inCand : ⟨ norm α χ ∈ˢ candidates sep pow (fst α) ⟩
            inCand = candidates-contains sep pow (fst α) (norm α χ)
                       (norm-name α χ) (norm-child α χ)

            atCondition : Σ[ p ∈ Cond ] ⟨ G p ⟩ → ⟨ fst χ ∈[G] powerDom α ⟩
            atCondition (p , hp) =
              ∈-congˡ (≈-sym (covering α χ h⊆))
                (entry-value (powerDom α) (norm α χ) (fst p) (snd p) hp
                  (mk-in sep (entryBound coll sep (candidates sep pow (fst α)))
                     ⊤̇ (entry (norm α χ) (fst p))
                     (entryBound-in coll sep (candidates sep pow (fst α))
                       (norm α χ) (fst p) inCand (snd p))
                     (λ h → h)))

        -- The named non-vacuity instance: α is a subset of itself, so the
        -- bounding name contains α. A powerDom that had collapsed to the empty
        -- name, or a `candidates` that had come back empty, fails this line.

        power-contains-self : (α : Nameᴾ) → ⟨ fst α ∈[G] powerDom α ⟩
        power-contains-self α = inPower α α (λ y hy → hy)

        -- ---------------------------------------------------------------
        -- Step five. THE FIELD.
        -- ---------------------------------------------------------------

        -- Power Set from a bounding set and Separation, the ordinary ZF route.
        -- The Separation is at 𝒮ᴾ and its formula is subφ α, whose reading is
        -- refl by subφ-reading above, so the cut really is "the members of the
        -- bounding name that are subsets of α" and not some other cut.

        hasPower : OrdinaryProfile.PowerSet 𝒮ᴾ
        hasPower α = PT.map cut (sepᴾ (powerName α) (subφ α))
          where
            cut : Σ[ s ∈ Nameᴾ ]
                    ⟨ ⋀ Nameᴾ (λ x → ((fst x ∈[G] fst s)
                                        ⇒ ((fst x ∈[G] powerDom α)
                                           ⊓ ((x ∷ []) ⊨ᴾ subφ α)))
                                   ⊓ (((fst x ∈[G] powerDom α)
                                        ⊓ ((x ∷ []) ⊨ᴾ subφ α))
                                      ⇒ (fst x ∈[G] fst s))) ⟩
                → Σ[ v ∈ Nameᴾ ]
                    ⟨ ⋀ Nameᴾ (λ x → ((fst x ∈[G] fst v)
                                        ⇒ ⋀ Nameᴾ (λ y → (fst y ∈[G] fst x)
                                                          ⇒ (fst y ∈[G] fst α)))
                                   ⊓ ((⋀ Nameᴾ (λ y → (fst y ∈[G] fst x)
                                                       ⇒ (fst y ∈[G] fst α)))
                                      ⇒ (fst x ∈[G] fst v))) ⟩
            cut (s , hs) = s , λ x → (λ hx → snd (fst (hs x) hx))
                                   , (λ h⊆ → snd (hs x) (inPower α x h⊆ , h⊆))
