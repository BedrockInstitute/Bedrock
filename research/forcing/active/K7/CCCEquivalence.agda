{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track C. THE CCC EQUIVALENCE, AND WHERE M's CHOICE ENTERS.
--
-- The project's own design document fixes the three predicates and demands
-- that their equivalence be an explicit theorem rather than a definitional
-- identity (forcing-geology-design-2026-09.md:223): CCC1 is "every MAXIMAL
-- antichain is countable", CCC2 is "every antichain is countable", CCC3 is
-- "every predense set has a countable predense subset".
--
-- Two of the six arrows are free and they belong to Track A. This file owns
-- the two that are PAID, and the whole of its content is an honest account of
-- what pays for them.
--
--   * ccc1 to ccc2 is paid by MaximalExtension: extend an arbitrary antichain
--     to a maximal one. That is the roadmap's own obligation and it is the
--     package's single open item.
--   * ccc2 to ccc3 is paid by MaximalExtensionIn, which architecture 2.3
--     states as "a predense set contains an antichain that is still predense".
--     PART 5 REFUTES THAT STATEMENT. It is not a consequence of ZFC: a seven
--     element poset makes it false, and this file proves it false from
--     hypotheses that poset satisfies. Rule 14 applies and the measurement
--     wins: ccc2 to ccc3 still reduces to it, but the reduction is conditional
--     on a hypothesis that fails at legitimate presentations, so it does not
--     establish CCC2 implies CCC3 "under internal ZFC".
--
-- WHICH DIRECTION IS WHICH, because Track A measured that the three are not
-- interchangeable and CCC1 is the WEAKEST. The direction that is free is
-- CCC2 implies CCC1, weakening a hypothesis, and it is Track A's
-- (K7/ChainConditions.agda:381). The direction this file pays for is its
-- CONVERSE, CCC1 implies CCC2, from the weakest condition to a stronger one.
-- Track A's AntichainAtEmpty.agda-break, exit 0, is why the gap is real: the
-- empty coded set is an antichain with no hypotheses spent and is never
-- predense (K5/Dense.agda:525-527), so it lies inside CCC2's hypothesis and
-- outside CCC1's.
--
-- ONE COUNTABILITY FORM AND ONLY ONE. This file uses the INJECTION form
-- throughout, injectable d w (CardinalBridge.agda:382-383), which is Track A's
-- countableΔ w d by definition (K7/ChainConditions.agda:265-266). The
-- surjection form Track B landed in parallel (IsSurjectionφ,
-- K7/CardinalOrder.agda:180) does not occur here, measured at zero
-- comment-stripped, and nothing in this tree relates the two without choice.
-- The one place the distinction would have bitten is flagged where it arises,
-- in PART 5's account of the correct route to ccc2 implies ccc3.
--
-- WHAT THIS FILE PROVES ABOUT THE OPEN ITEM, and it is a reduction and not a
-- closure. PART 6 defines GreedySpec, the fixpoint characterisation of the
-- antichain a transfinite greedy recursion along the ground well ordering
-- would build, and proves greedy→maximal: ANY set satisfying GreedySpec IS
-- a maximal antichain extending the given one. So the gap between the ground
-- well ordering and MaximalExtension is exactly one thing, GreedySupply, the
-- EXISTENCE of that fixpoint.
--
-- THE STOP, WITH THE THREE ROUTES AND WHERE EACH ENDS. Measured in this
-- session over the whole compile root, comment-stripped, not inherited.
--
--  ROUTE 1, Bell's own (bell-2005-boolean-valued-models.fulltext.md:4978-4983):
--  enumerate A ∪ {(⋁A)*} by an ordinal of M and subtract transfinitely. STOPS
--  AT THE VOCABULARY. The tokens transfinite, Hartogs, enumerat, orderType,
--  otp, wfRec and wellFoundedRec each measure ZERO occurrences in the whole
--  compile root with comments stripped, and OrdinaryProfile.agda declares no
--  recursion theorem of any kind (its full inventory is architecture 2.3's
--  census, re-measured here).
--
--  ROUTE 2, the approximation method: cut the set of lt-approximations by
--  Separation, prove uniqueness by induction along lt, and take the union.
--  STOPS AT DEFINABILITY, AND THE BOUNDARY IS IN THIS FILE. lt-induction in
--  PART 2 proves that induction along the well ordering IS available at this
--  profile, so the obstruction is not well-foundedness. But Separation reads a
--  Formula S 1 (OrdinaryProfile.agda:88-90), so induction is available exactly
--  for predicates the object language can spell, and lt HAS NO FORMULA: it
--  occurs in this tree only as a bare S → S → Ω, at eight declaration sites
--  (K6/Choice.agda:418, K7/CompletionTransfer.agda:102,
--  K7/TransferAtCertificate.agda:127, K7/Refuted.agda:630, this file's :128
--  and three break files), and a search for any ltAt / ltΔ / ltFo / Ltφ shaped
--  name returns ZERO. So route 2 cannot cut its first set. That missing datum
--  is the same one PART 3 had to name as LtDefinable, and PART 3 shows what it
--  buys when it is granted.
--
--  ROUTE 3, the host recursion combinator. Cubical's WFI.induction exists and
--  this tree uses it twenty-seven times. STOPS TWICE, BOTH AT O3b. Every one
--  of those uses feeds it a HOST WellFounded proof taken as a parameter
--  (child-wf at TranslateForward.agda:153, NameSpace.agda:352,
--  NameSupport.agda:300, Valuation.agda:153, TranslateReverse.agda:365 and
--  nine K5 and K6 sites; acc∈ at StandardNames.agda:266), and NOTHING IN THE
--  TREE PRODUCES A WellFounded PROOF: a comment-stripped search for a
--  declaration concluding WellFounded returns parameters only, twenty of them,
--  and no theorem. Producing WellFounded lt from the triple needs the
--  least-element principle over a HOST predicate S → Ω, which is ground CLASS
--  Separation, which is obstruction O3b and is K6's own poisoned form
--  (K6/Choice.agda:411-413, K6/breaks/ClassLeast.agda-break). And granting it
--  would not finish: the recursion returns a HOST predicate on codes, and
--  turning that into the single ground set e : S needs a second Separation
--  over a host predicate. What it would produce is precisely the shape
--  K7/breaks/HostMaximalExtension.agda-break exhibits at exit 0, a host
--  operator that fills MaximalExtension and is not a theorem of M.
--
-- SO THE MEASURED NEGATIVE IS: MaximalExtension does not follow from
-- GroundWellOrder at this profile, the gap is exactly GreedySupply, and
-- GreedySupply is rule 15 class (ii), inhabited at a genuine ZFC ground by the
-- recursion that builds it and with no filler anywhere in this tree.
--
-- WHAT IT DOES CLOSE, and it was measured cheap. PART 3 proves the converse
-- of the gap the coordinator named as the most reusable theorem K7 could
-- deliver: GroundWellOrder plus Separation plus Collection plus one
-- definability datum gives the profile's own ChoiceSet. So K7's well ordering
-- is at least as strong as the profile's internal choice, which is what
-- "consumes M's choice" has to mean.
--
-- THE TWO PROTECTIONS THIS FILE PRESERVES, and Track D measured that the type
-- protects nothing on its own (K7/breaks/HostSelector.agda-break, exit 0).
--
--   1. THE SIBLING ARRANGEMENT. module Free (the chain-condition arrows) and
--      module FromChoice (the greedy reduction) are SIBLINGS inside module At,
--      on K6's model at K6/Choice.agda:415 beside :772. The ground well
--      ordering is not in scope anywhere in Free, so no arrow there can
--      manufacture a MaximalExtension; it must be handed one. A later edit
--      cannot falsify that without moving a module (K6/Choice.agda:31-38).
--   2. GroundWellOrder's FIELDS ARE K6's TRIPLE AND NOTHING ELSE. Every
--      projection of the record is either a relation on ground CODES
--      (lt : S -> S -> Omega) or a proof about ground SETS (wo-least ranges
--      over d : S). There is no field of type S -> S, so a consumer who
--      projects the record gets a ground relation and never a host selection
--      function. Downstream the record still travels opaque: K6 takes it as
--      an opaque Type (l-suc l) at K6/Choice.agda:939 and
--      K6/ChoiceAtStructures.agda:197, and Track D takes it that way at
--      K7/CompletionTransfer.agda:100.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.CCCEquivalence
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _⇒̇_; ⊥̇ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_ )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎ ; inr to inr⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import CodedVocabulary
import GroundDescription

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module GD = GroundDescription 𝒮 ext paths
module CV = CodedVocabulary 𝒮

open OP using ( iff; Separation; Collection )
open OP.PathRealization paths using ( ≈ˢ-to-path; path-to-≈ˢ; subst-member )
open GD using ( hasImage′ )
open CV using ( compatibleΔ; compatibleΔ-sym; subsetΔ; predenseΔ )
open At S id using ( _⊨_ )

--------------------------------------------------------------------------------
-- PART 1. THE GROUND WELL ORDERING, AS A RECORD
--------------------------------------------------------------------------------

-- Declared here and imported from nowhere. Rule 9 says records are generative
-- and a layer that owns one owns it alone; GroundWellOrder is NOWHERE a record
-- in this tree, only an opaque parameter at K6/Choice.agda:939 and
-- K6/ChoiceAtStructures.agda:197, so nobody owns it yet and Track C declares
-- it. The three fields are K6/Choice.agda:418-422 character for character,
-- verified at source in this session.
--
-- THE LEVEL IS Type (ℓ-suc ℓ) AND THAT IS NOT COSMETIC. lt is S → S → Ω and
-- Ω = hProp ℓ lives at Type (ℓ-suc ℓ), so a record collecting these fields is
-- one universe up. Track D's first draft wrote Type ℓ; the parameter form of
-- that draft TYPECHECKS and can never be instantiated, which is rule 15's
-- shape one level down and no grep finds it. K6 has the level right at
-- K6/Choice.agda:939. K7/breaks/GroundWellOrderLevel.agda-break measures both
-- spellings.
--
-- Read the quantifiers, because they are the whole ledger row
-- (K6/Choice.agda:411-413, quoted at source): lt is a relation on ground
-- CODES; lt-tri compares two codes; wo-least ranges over d : S, a ground SET,
-- and not over a host predicate S → Ω. The poisoned form quantifies over a
-- host predicate, which is ground CLASS Separation, which is obstruction O3b.

record GroundWellOrder : Type (ℓ-suc ℓ) where
  field
    lt       : S → S → Ω
    lt-tri   : (z z' : S) → ∥ ⟨ lt z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ lt z' z ⟩) ∥₁
    wo-least : (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩
             → ⟨ ⋁ S (λ z → (z ∈ˢ d)
                   ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((lt z' z) ⇒ ⊥))) ⟩

--------------------------------------------------------------------------------
-- PART 2. WHAT THE TRIPLE GIVES ON ITS OWN
--------------------------------------------------------------------------------

-- The order theory of the record, with no chain condition anywhere in scope.
-- These are Track D's constructions (K7/CompletionTransfer.agda:100-181) at
-- the record rather than at the opaque type plus three projections, and the
-- proofs are the same because the mathematics is the same: the lt-least
-- member of an inhabited ground set is a PROVED UNIQUE witness, so a selection
-- made by it is unique choice and not choice.

module Well (wo : GroundWellOrder) where

  open GroundWellOrder wo public

  -- "z is the lt-least member of d", as a truth value of the model.

  leastIn : S → S → Ω
  leastIn d z = (z ∈ˢ d) ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((lt z' z) ⇒ ⊥))

  Least : S → Type ℓ
  Least d = Σ[ z ∈ S ] ⟨ leastIn d z ⟩

  -- Two lt-minimal members of one ground set are equal. Trichotomy offers
  -- three cases and the two strict ones contradict minimality of the other
  -- side. Nothing is truncated away, so the conclusion is a host PATH.

  least-unique : (d z z' : S) → ⟨ leastIn d z ⟩ → ⟨ leastIn d z' ⟩ → z ≡ z'
  least-unique d z z' hz hz' = PT.rec (isSetS z z') step (lt-tri z z')
    where
      step : ⟨ lt z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ lt z' z ⟩) → z ≡ z'
      step (inl⊎ l)        = Empty.rec* (snd hz' z (fst hz) l)
      step (inr⊎ (inl⊎ e)) = e
      step (inr⊎ (inr⊎ l)) = Empty.rec* (snd hz z' (fst hz') l)

  isPropLeast : (d : S) → isProp (Least d)
  isPropLeast d x y =
    Σ≡Prop (λ z → snd (leastIn d z))
      (least-unique d (fst x) (fst y) (snd x) (snd y))

  -- wo-least supplies a TRUNCATED witness; uniqueness turns the truncation
  -- into the witness itself, because a truncation eliminates into a
  -- proposition. This is the one allowed shape, a proved-unique witness
  -- becoming a simultaneous internal function, and it is the reason nothing
  -- below is a choice function.

  least-contr : (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩ → isContr (Least d)
  least-contr d inh = centre , λ y → isPropLeast d centre y
    where
      centre : Least d
      centre = PT.rec (isPropLeast d) (λ z → z) (wo-least d inh)

  pick : (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩ → S
  pick d inh = fst (fst (least-contr d inh))

  pick-least : (d : S) (inh : ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩) → ⟨ leastIn d (pick d inh) ⟩
  pick-least d inh = snd (fst (least-contr d inh))

  pick-in : (d : S) (inh : ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩) → ⟨ pick d inh ∈ˢ d ⟩
  pick-in d inh = fst (pick-least d inh)

  -- INDUCTION ALONG THE WELL ORDERING LANDS. RECURSION IS WHAT DOES NOT, AND
  -- THIS LEMMA IS HERE TO MAKE THE DIFFERENCE A MEASUREMENT RATHER THAN A
  -- CLAIM.
  --
  -- Everyone's first guess about why the profile cannot extend an antichain is
  -- that it has no well-founded induction along lt. That guess is wrong, and
  -- the proof is thirty lines. Cut the counterexample set b = { x ∈ c : ¬φ(x) }
  -- by one Separation, take its lt-least member if it has one, and the
  -- induction step applies there because everything lt-below it inside c
  -- already satisfies φ. So b is uninhabited, and every member of c satisfies
  -- φ. Excluded middle appears twice and only to turn a refuted negation into
  -- the proposition, which is LEM ℓ and never choice.
  --
  -- WHAT THE HYPOTHESIS COSTS, and it is the whole story of this track's open
  -- item. φ is a Formula S 1 and NOT a host predicate S → Ω, because
  -- Separation reads a formula (OrdinaryProfile.agda:88-90). Induction is
  -- therefore available exactly for predicates the object language can spell.
  -- Two consequences, both of which the stop report leans on.
  --
  --   * Even this lemma is unusable on any predicate mentioning lt, because lt
  --     arrives as a bare S → S → Ω with no formula attached anywhere in this
  --     tree. That is the same missing datum ToChoice above had to name as
  --     LtDefinable.
  --   * Induction proves; it does not DEFINE. A greedy antichain is a
  --     definition by recursion along lt, and the profile has no recursion
  --     theorem, no ordinal enumeration and no Hartogs construction. Turning
  --     this induction into a recursion is the classical approximation method,
  --     and every one of its Separations needs a formula for "a is a greedy
  --     approximation below x", which is a strictly larger object-language job
  --     than anything in CodedVocabulary.

  lt-induction : Separation → LEM ℓ → (c : S) (φ : Formula S 1)
               → ((x : S) → ⟨ x ∈ˢ c ⟩
                  → ((y : S) → ⟨ y ∈ˢ c ⟩ → ⟨ lt y x ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩)
                  → ⟨ (x ∷ []) ⊨ φ ⟩)
               → (x : S) → ⟨ x ∈ˢ c ⟩ → ⟨ (x ∷ []) ⊨ φ ⟩
  lt-induction sep lem c φ step x hx =
    PT.rec (snd ((x ∷ []) ⊨ φ)) atCut (sep c (φ ⇒̇ ⊥̇))
    where
      atCut : (Σ[ b ∈ S ] ⟨ ⋀ S (λ u → iff (u ∈ˢ b)
                              ((u ∈ˢ c) ⊓ ((u ∷ []) ⊨ (φ ⇒̇ ⊥̇)))) ⟩)
            → ⟨ (x ∷ []) ⊨ φ ⟩
      atCut (b , bspec) = decide (lem ((x ∷ []) ⊨ φ))
        where
          inB : (u : S) → ⟨ u ∈ˢ c ⟩ → (⟨ (u ∷ []) ⊨ φ ⟩ → Empty.⊥)
              → ⟨ u ∈ˢ b ⟩
          inB u hu nu = snd (bspec u) (hu , λ h → Empty.rec (nu h))

          bad : (Σ[ z ∈ S ] ⟨ (z ∈ˢ b)
                            ⊓ ⋀ S (λ z' → (z' ∈ˢ b) ⇒ ((lt z' z) ⇒ ⊥)) ⟩)
              → Empty.⊥
          bad (z , hzb , hmin) = nz (step z (fst zc) below)
            where
              zc : ⟨ (z ∈ˢ c) ⊓ ((z ∷ []) ⊨ (φ ⇒̇ ⊥̇)) ⟩
              zc = fst (bspec z) hzb

              nz : ⟨ (z ∷ []) ⊨ φ ⟩ → Empty.⊥
              nz h = Empty.rec* (snd zc h)

              below : (y : S) → ⟨ y ∈ˢ c ⟩ → ⟨ lt y z ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩
              below y hyc hlt = choose (lem ((y ∷ []) ⊨ φ))
                where
                  choose : ⟨ (y ∷ []) ⊨ φ ⟩ ⊎ (⟨ (y ∷ []) ⊨ φ ⟩ → Empty.⊥)
                         → ⟨ (y ∷ []) ⊨ φ ⟩
                  choose (inl⊎ h)  = h
                  choose (inr⊎ nh) = Empty.rec* (hmin y (inB y hyc nh) hlt)

          uninhabited : ⟨ ⋁ S (λ z → z ∈ˢ b) ⟩ → Empty.⊥
          uninhabited inh = PT.rec Empty.isProp⊥ bad (wo-least b inh)

          decide : ⟨ (x ∷ []) ⊨ φ ⟩ ⊎ (⟨ (x ∷ []) ⊨ φ ⟩ → Empty.⊥)
                 → ⟨ (x ∷ []) ⊨ φ ⟩
          decide (inl⊎ h)  = h
          decide (inr⊎ nh) = Empty.rec (uninhabited ∣ x , inB x hx nh ∣₁)

--------------------------------------------------------------------------------
-- PART 3. THE CONVERSE THE COORDINATOR ASKED FOR, AND IT IS CHEAP
--------------------------------------------------------------------------------

-- Ruling Q3 records as a K7 finding that ChoiceSet ⟹ GroundWellOrder HAS NO
-- PROOF IN THIS TREE, and Track D confirmed it by a comment-stripped census:
-- ChoiceSet has 11 non-comment occurrences across 5 files and none is in a
-- hypothesis position producing the triple. The price of that direction is
-- Zermelo, an ordinal enumeration plus transfinite recursion, and the profile
-- has neither. THE CONVERSE IS THE CHEAP HALF AND THIS PART TAKES IT.
--
-- The route is the one Track D's module Image already runs: least-contr makes
-- the selection a functional relation in hasImage′'s sense
-- (GroundDescription.agda:181-185, verified: it takes Separation and
-- Collection as two STANDALONE arguments and not the OrdinaryZF record), and
-- hasImage′ turns the relation into the image set. The choice set is the image
-- of the family under "z is the lt-least member of x".
--
-- ONE DATUM IS NOT FREE AND IT IS NAMED. Separation reads a Formula S 1 and
-- Collection a Formula S 2 (OrdinaryProfile.agda:88-99, verified), so any use
-- of them needs an object-language formula. lt arrives as a bare S → S → Ω
-- with NO formula attached anywhere in this tree, so the definability of the
-- well ordering has to be a hypothesis. LtDefinable is that hypothesis, named,
-- and it is Track D's SelDefinable (K7/CompletionTransfer.agda:399-401) at
-- this family. It is Type (ℓ-suc ℓ) for the same measured reason: the reading
-- is a path between truth values and Ω is hProp ℓ.

module ToChoice (wo : GroundWellOrder) where

  open Well wo

  LtDefinable : Type (ℓ-suc ℓ)
  LtDefinable =
    Σ[ φ ∈ Formula S 2 ] ((x y : S) → ((y ∷ x ∷ []) ⊨ φ) ≡ leastIn x y)

  -- The profile's own internal choice sentence, module-qualified so a ledger
  -- reader can see at a glance that this is the GROUND's ChoiceSet
  -- (OrdinaryProfile.agda:115-124) and not the extension's.

  wo→choiceSet : Separation → Collection → LtDefinable → OP.ChoiceSet
  wo→choiceSet sep coll def a inh disj =
    PT.rec (snd goal) assemble (hasImage′ sep coll a φ functional)
    where
      φ : Formula S 2
      φ = fst def

      read : (x y : S) → ((y ∷ x ∷ []) ⊨ φ) ≡ leastIn x y
      read = snd def

      Fib : S → Type ℓ
      Fib x = Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩

      toLeast : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩ → ⟨ leastIn x y ⟩
      toLeast x y h = subst ⟨_⟩ (read x y) h

      ofLeast : (x y : S) → ⟨ leastIn x y ⟩ → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩
      ofLeast x y h = subst ⟨_⟩ (sym (read x y)) h

      isPropFib : (x : S) → isProp (Fib x)
      isPropFib x u v =
        Σ≡Prop (λ z → snd ((z ∷ x ∷ []) ⊨ φ))
          (least-unique x (fst u) (fst v)
            (toLeast x (fst u) (snd u)) (toLeast x (fst v) (snd v)))

      -- Existence is M's own well ordering through wo-least; uniqueness is
      -- least-unique. Together they are host contractibility, which is what
      -- hasImage′ calls functionality.

      functional : (x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Fib x)
      functional x hx = centre , λ y → isPropFib x centre y
        where
          centre : Fib x
          centre = pick x (inh x hx) , ofLeast x (pick x (inh x hx)) (pick-least x (inh x hx))

      goal : Ω
      goal = ⋁ S (λ cs → ⋀ S (λ x → (x ∈ˢ a) ⇒
               ( (⋁ S (λ z → (z ∈ˢ cs) ⊓ (z ∈ˢ x)))
               ⊓ (⋀ S (λ z → ⋀ S (λ z' →
                     (((z ∈ˢ cs) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ cs) ⊓ (z' ∈ˢ x)))
                     ⇒ (z ≈ˢ z')))))))

      -- The image set IS the choice set. Existence at x is the lt-least member
      -- of x, which lies in the image because x lies in a. Uniqueness is where
      -- the family's disjointness is spent: a second member of the image that
      -- lies in x arrived as the lt-least member of SOME x', and x' shares a
      -- point with x, so disj identifies them and least-unique finishes.

      assemble : (Σ[ b ∈ S ] ⟨ ⋀ S (λ y → iff (y ∈ˢ b)
                   (⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ)))) ⟩)
               → ⟨ goal ⟩
      assemble (b , spec) = ∣ b , (λ x hx → exists x hx , unique x hx) ∣₁
        where
          exists : (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ ⋁ S (λ z → (z ∈ˢ b) ⊓ (z ∈ˢ x)) ⟩
          exists x hx =
            ∣ pick x (inh x hx)
            , snd (spec (pick x (inh x hx)))
                ∣ x , hx , ofLeast x (pick x (inh x hx)) (pick-least x (inh x hx)) ∣₁
            , pick-in x (inh x hx) ∣₁

          -- From "y lies in the image and lies in x" recover "y is the
          -- lt-least member of x".

          recover : (x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩ → ⟨ y ∈ˢ x ⟩
                  → ⟨ leastIn x y ⟩
          recover x y hx hb hy = PT.rec (snd (leastIn x y)) step (fst (spec y) hb)
            where
              step : (Σ[ x' ∈ S ] (⟨ x' ∈ˢ a ⟩ × ⟨ (y ∷ x' ∷ []) ⊨ φ ⟩))
                   → ⟨ leastIn x y ⟩
              step (x' , hx' , hφ) =
                subst (λ u → ⟨ leastIn u y ⟩)
                  (disj x' x hx' hx ∣ y , fst (toLeast x' y hφ) , hy ∣₁)
                  (toLeast x' y hφ)

          unique : (x : S) → ⟨ x ∈ˢ a ⟩
                 → ⟨ ⋀ S (λ z → ⋀ S (λ z' →
                       (((z ∈ˢ b) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ b) ⊓ (z' ∈ˢ x)))
                       ⇒ (z ≈ˢ z'))) ⟩
          unique x hx z z' ((hzb , hzx) , (hz'b , hz'x)) =
            path-to-≈ˢ z z'
              (least-unique x z z' (recover x z hx hzb hzx) (recover x z' hx hz'b hz'x))

--------------------------------------------------------------------------------
-- PART 4. THE PRESENTATION, THE TWO REDUCTION TYPES, AND THE ARROWS
--------------------------------------------------------------------------------

-- carrier and order are the first two fields of CodedCompletion.Presentation
-- (:201-208), taken FLAT. Rule 2b as K6's Track A refined it: a module
-- parameter is maximally stuck and beats sealing, measured at 1.05 s against
-- 1.08 s. The other two fields, order-typed and inhabited, are not taken,
-- because rule 13 says the hypotheses come from what the proofs use and no
-- proof in this file uses either.
--
-- compatibleΔ, subsetΔ and predenseΔ are the REAL CodedVocabulary exports
-- (:167-168, :202-203, :417-418), applied above, so no parameter can drift
-- from them. What arrives flat is Track A's vocabulary, and every type below
-- is Track A's export type CHARACTER FOR CHARACTER, checked against
-- K7/ChainConditions.agda at :125, :156-160, :162-166, :244-249, :265-266,
-- :280-284, :305-334 and :336-365. K7/CCCEquivalenceAtA.agda fills every one
-- of them with the export itself.
--
-- compat-refl is the one presentation fact this file needs that the record's
-- four fields do not carry: a condition is compatible with itself. It is one
-- line from reflexivity of the order graph, and it is a hypothesis here
-- rather than a lemma because the order graph reflexivity is not among
-- Presentation's fields either.

module Presented
  (carrier order : S)
  (compat-refl : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ compatibleΔ carrier order p p ⟩)
  -- Track A's antichain predicate, flat, through its two directions. These
  -- two types are Track D's (K7/CompletionTransfer.agda:265-273) character
  -- for character, so the two K7 tracks that consume Track A cannot disagree
  -- about which equality the antichain uses.
  (antichainΔ : S → S → S → Ω)
  (antichain-use : (c o d p q : S) → ⟨ antichainΔ c o d ⟩
                 → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
                 → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
  (antichain-intro : (c o d : S)
                   → ((p q : S) → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
                      → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
                   → ⟨ antichainΔ c o d ⟩)
  -- Track A's maximalΔ (architecture 2.1), which spells maximality as
  -- predensity and so avoids Zorn in the DEFINITION. Only the introduction
  -- and the two projections are used.
  (maximalΔ : S → S → S → Ω)
  (maximal-intro : (c o d : S) → ⟨ antichainΔ c o d ⟩ → ⟨ predenseΔ c o d ⟩
                 → ⟨ maximalΔ c o d ⟩)
  -- Countability. Track A spells it countableΔ w d and defines it as
  -- injectable d w (K7/ChainConditions.agda:265-266); this telescope writes
  -- the abbreviation out so that exactly one countability notion occurs in
  -- it. Track A's own use and intro directions typecheck against these types
  -- because countableΔ is a definition and not an opaque, and
  -- K7/CCCEquivalenceAtA.agda discharges every parameter here with Track A's
  -- export to show it. injectable-mono-dom is proved at
  -- K7/ChainConditions.agda:280-284.
  (injectable : S → S → Ω)
  (injectable-mono-dom : (a b w : S) → ⟨ subsetΔ a b ⟩
                       → ⟨ injectable b w ⟩ → ⟨ injectable a w ⟩)
  where

  subsetΔ-trans : (a b d : S) → ⟨ subsetΔ a b ⟩ → ⟨ subsetΔ b d ⟩ → ⟨ subsetΔ a d ⟩
  subsetΔ-trans a b d ab bd x hx = bd x (ab x hx)

  -- The two obligations of architecture 2.3. Track A owns them as
  -- MaximalExtension c o and MaximalExtensionIn c o
  -- (K7/ChainConditions.agda:443-454) and says in its own comment that Track C
  -- should ALIAS rather than retype. The flat spine of 4.0 forbids applying a
  -- producer inside a consumer, so the alias is written out here at the fixed
  -- carrier and order, and K7/CCCEquivalenceAtA.agda proves the two are the
  -- SAME TYPE by refl once the parameters carry Track A's definitions. That
  -- refl is the anti-drift check; without it this would be a retype.
  --
  -- Both are Type ℓ
  -- because ⟨_⟩ of a truth value is, which is the level control CCC₁ᴵ, CCC₂ᴵ
  -- and CCC₃ᴵ run at Track A (CodedCompletion.agda:987-993: "a host-quantified
  -- draft lands at Type (ℓ-suc ℓ), which is the diagnostic").

  MaximalExtension : Type ℓ
  MaximalExtension =
    (d : S) → ⟨ subsetΔ d carrier ⟩ → ⟨ antichainΔ carrier order d ⟩
    → ⟨ ⋁ S (λ e → ((subsetΔ d e) ⊓ (subsetΔ e carrier))
                 ⊓ maximalΔ carrier order e) ⟩

  MaximalExtensionIn : Type ℓ
  MaximalExtensionIn =
    (b : S) → ⟨ subsetΔ b carrier ⟩ → ⟨ predenseΔ carrier order b ⟩
    → ⟨ ⋁ S (λ e → ((subsetΔ e b) ⊓ antichainΔ carrier order e)
                 ⊓ predenseΔ carrier order e) ⟩

  ------------------------------------------------------------------------------
  -- The paid arrows. SIBLING of FromChoice below, and the sibling arrangement
  -- is the AC check: no GroundWellOrder is in scope anywhere in this module,
  -- so neither arrow can manufacture its own extension operator.
  ------------------------------------------------------------------------------

  module Free
    (CCC₁ᴵ CCC₂ᴵ CCC₃ᴵ : S → S → S → Ω)
    (ccc₁-use : (c o w d : S) → ⟨ CCC₁ᴵ c o w ⟩ → ⟨ subsetΔ d c ⟩
              → ⟨ maximalΔ c o d ⟩ → ⟨ injectable d w ⟩)
    (ccc-use : (c o v d : S) → ⟨ CCC₂ᴵ c o v ⟩ → ⟨ subsetΔ d c ⟩
             → ⟨ antichainΔ c o d ⟩ → ⟨ injectable d v ⟩)
    (ccc-intro : (c o v : S)
               → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
                  → ⟨ injectable d v ⟩)
               → ⟨ CCC₂ᴵ c o v ⟩)
    (ccc₃-intro : (c o w : S)
                → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ predenseΔ c o d ⟩
                   → ⟨ ⋁ S (λ e → ((subsetΔ e d) ⊓ predenseΔ c o e)
                               ⊓ injectable e w) ⟩)
                → ⟨ CCC₃ᴵ c o w ⟩)
    -- Track A's free arrow, architecture 2.3 and 4.1. It is not re-proved
    -- here: rule 9's spirit and the architecture's own track cut both put it
    -- at Track A, and K7/CCCEquivalenceAtA.agda discharges it from Track A's
    -- stated definitions so the parameter is not an assumption in disguise.
    (ccc₃→ccc₁ : (c o w : S) → ⟨ CCC₃ᴵ c o w ⟩ → ⟨ CCC₁ᴵ c o w ⟩)
    where

    -- Every antichain is countable, from every MAXIMAL antichain countable.
    -- Extend the antichain, apply CCC₁ to the extension, and carry
    -- countability back down the inclusion. The extension is truncated, and
    -- the target is a truth value, so PT.rec is the whole of the bookkeeping.

    ccc₁→ccc₂ : MaximalExtension → (w : S)
              → ⟨ CCC₁ᴵ carrier order w ⟩ → ⟨ CCC₂ᴵ carrier order w ⟩
    ccc₁→ccc₂ mx w h₁ = ccc-intro carrier order w step
      where
        step : (d : S) → ⟨ subsetΔ d carrier ⟩ → ⟨ antichainΔ carrier order d ⟩
             → ⟨ injectable d w ⟩
        step d dsub dac = PT.rec (snd (injectable d w))
          (λ { (e , (dsube , esub) , emax) →
                 injectable-mono-dom d e w dsube
                   (ccc₁-use carrier order w e h₁ esub emax) })
          (mx d dsub dac)

    -- Every predense set has a countable predense subset, from every antichain
    -- countable. The subset is the antichain MaximalExtensionIn produces
    -- inside it, which is predense by that hypothesis and countable by CCC₂.
    -- The reduction is honest; PART 5 shows the hypothesis is not a theorem.

    ccc₂→ccc₃ : MaximalExtensionIn → (w : S)
              → ⟨ CCC₂ᴵ carrier order w ⟩ → ⟨ CCC₃ᴵ carrier order w ⟩
    ccc₂→ccc₃ mxi w h₂ = ccc₃-intro carrier order w step
      where
        step : (b : S) → ⟨ subsetΔ b carrier ⟩ → ⟨ predenseΔ carrier order b ⟩
             → ⟨ ⋁ S (λ e → ((subsetΔ e b) ⊓ predenseΔ carrier order e)
                          ⊓ injectable e w) ⟩
        step b bsub bpd = PT.rec PT.squash₁
          (λ { (e , (esubb , eac) , epd) →
                 ∣ e , (esubb , epd)
                 , ccc-use carrier order w e h₂
                     (subsetΔ-trans e b carrier esubb bsub) eac ∣₁ })
          (mxi b bsub bpd)

    ccc-equivalent :
        MaximalExtension → MaximalExtensionIn → (w : S)
      → (⟨ CCC₁ᴵ carrier order w ⟩ → ⟨ CCC₂ᴵ carrier order w ⟩)
      × ((⟨ CCC₂ᴵ carrier order w ⟩ → ⟨ CCC₃ᴵ carrier order w ⟩)
        × (⟨ CCC₃ᴵ carrier order w ⟩ → ⟨ CCC₁ᴵ carrier order w ⟩))
    ccc-equivalent mx mxi w =
      ccc₁→ccc₂ mx w , ccc₂→ccc₃ mxi w , ccc₃→ccc₁ carrier order w

    -- Rule 14's transcription. This is ccc₁→ccc₂ with the MaximalExtension
    -- argument removed, which is the equivalence the roadmap forbids reading
    -- into K7's theorems: the design document's Corollary 6.5 shows the
    -- failure of a general CCC₂-preserving completion theorem in the
    -- choiceless setting (forcing-geology-design-2026-09.md:223). IT IS NOT
    -- INHABITED IN THIS FILE AND MUST NOT BE.

    ChoicelessEquivalence : Type ℓ
    ChoicelessEquivalence =
      (w : S) → ⟨ CCC₁ᴵ carrier order w ⟩ → ⟨ CCC₂ᴵ carrier order w ⟩

  ------------------------------------------------------------------------------
  -- PART 5. MaximalExtensionIn IS REFUTED. RULE 14.
  ------------------------------------------------------------------------------

  -- Architecture 2.3 writes MaximalExtensionIn as the price of ccc₂→ccc₃ and
  -- calls it "the same Zorn-shaped obligation as extending an antichain to a
  -- maximal one". The second half of that sentence is wrong and the difference
  -- is not a matter of price. MaximalExtension is a consequence of ZFC.
  -- MaximalExtensionIn IS NOT, and the reason is that COMPATIBILITY IS NOT
  -- TRANSITIVE: an antichain inside b can be maximal inside b and still miss
  -- conditions that b itself meets.
  --
  -- THE WITNESS, a seven element poset, exhibited here in prose because
  -- coding a presentation is K8's job and not a reduction.
  --
  --   points      p₁ p₂ r₁ r₂ x y z
  --   order       x ≼ p₁, x ≼ p₂, y ≼ r₁, y ≼ p₂, z ≼ r₂, z ≼ p₁
  --               (plus reflexivity; x, y, z are pairwise incomparable minima)
  --
  -- Then b = {p₁, p₂} is predense: p₁ and p₂ meet themselves, r₁ meets p₂ at
  -- y, r₂ meets p₁ at z, and x, y, z lie below a member of b. The conditions
  -- below r₁ are {r₁, y} and those below p₁ are {p₁, x, z}, so r₁ and p₁ are
  -- INCOMPATIBLE; symmetrically r₂ and p₂ are incompatible. And p₁ meets p₂
  -- at x, so the only antichains contained in b are ∅, {p₁} and {p₂}. None of
  -- the three is predense: ∅ misses everything, {p₁} misses r₁, {p₂} misses
  -- r₂. So no antichain inside b is predense, which is exactly the negation
  -- of MaximalExtensionIn at this presentation.
  --
  -- The theorem below is that argument, machine-checked, from hypotheses the
  -- poset satisfies. It is SCHEMATIC: the hypotheses are stated about an
  -- abstract presentation and the poset above is not coded in this tree, so
  -- what is proved is "MaximalExtensionIn fails at every presentation with
  -- this configuration", not "some coded presentation has it". The
  -- configuration is consistent, by the poset. The coded one-point
  -- presentation (K6/OnePoint.agda:158) does NOT satisfy it, having one point.
  --
  -- CONSEQUENCE FOR THE PACKAGE, and it is the sharp one. ccc₂→ccc₃ above is
  -- a true implication and it is the arrow the architecture asked for, but its
  -- hypothesis is rule 15 class (iii) at some legitimate presentations, so the
  -- arrow does NOT establish "CCC₂ implies CCC₃ under internal ZFC". The
  -- classical proof of that implication goes a different way: take a maximal
  -- antichain in the DOWNWARD CLOSURE of b, which is predense because the
  -- closure is dense, then map each of its members to an element of b above
  -- it. The second step is a selection, and under the ground well ordering it
  -- is the lt-least such element, which is PART 2's pick. So the correct
  -- reduction of ccc₂→ccc₃ consumes MaximalExtension at the downward closure
  -- PLUS M's choice PLUS an image-cardinality lemma, and it is not the
  -- statement at 2.3. K8 must be told this before it quotes CCC₃.
  --
  -- AND THE IMAGE-CARDINALITY LEMMA IS ITSELF AN OPEN ROW, which is why the
  -- correct route is named here and not taken. "The image of a countable set
  -- is countable" is a statement about SURJECTIONS, and this package's
  -- countability is injectable, an INJECTION (CardinalBridge.agda:382-383).
  -- Track B landed the surjection form separately as IsSurjectionφ
  -- (K7/CardinalOrder.agda:180), and NOTHING IN THIS TREE RELATES THE TWO;
  -- without choice they are different notions. So the correct route to
  -- ccc₂→ccc₃ needs, on top of an extension at the downward closure and M's
  -- choice, a bridge from the surjection form to the injection form that has
  -- no supplier. This file therefore changes form nowhere: every countability
  -- in it is injectable, measured at zero surjection occurrences.

  MaximalExtensionIn-refuted :
      (b p₁ p₂ r₁ r₂ : S)
    → ⟨ subsetΔ b carrier ⟩
    → ⟨ predenseΔ carrier order b ⟩
    → ⟨ p₁ ∈ˢ b ⟩ → ⟨ p₂ ∈ˢ b ⟩
    → ((u : S) → ⟨ u ∈ˢ b ⟩ → ⟨ (u ≈ˢ p₁) ⊔ (u ≈ˢ p₂) ⟩)
    → ⟨ compatibleΔ carrier order p₁ p₂ ⟩
    → (⟨ p₁ ≈ˢ p₂ ⟩ → ⟨ ⊥ ⟩)
    → ⟨ r₁ ∈ˢ carrier ⟩ → (⟨ compatibleΔ carrier order p₁ r₁ ⟩ → ⟨ ⊥ ⟩)
    → ⟨ r₂ ∈ˢ carrier ⟩ → (⟨ compatibleΔ carrier order p₂ r₂ ⟩ → ⟨ ⊥ ⟩)
    → MaximalExtensionIn → ⟨ ⊥ ⟩
  MaximalExtensionIn-refuted b p₁ p₂ r₁ r₂ bsub bpd hp₁ hp₂ pair cpp ne
                            hr₁ enemy₁ hr₂ enemy₂ mxi =
    PT.rec (snd ⊥) contradiction (mxi b bsub bpd)
    where
      -- A member of e that meets r must be the one of p₁, p₂ that is not r's
      -- enemy, and membership transports along ≈ˢ.

      contradiction : (Σ[ e ∈ S ] ⟨ ((subsetΔ e b) ⊓ antichainΔ carrier order e)
                                  ⊓ predenseΔ carrier order e ⟩)
                    → ⟨ ⊥ ⟩
      contradiction (e , (esub , eac) , epd) =
        PT.rec (snd ⊥) (λ w₁ → PT.rec (snd ⊥) (λ w₂ → finish w₁ w₂) (epd r₂ hr₂))
               (epd r₁ hr₁)
        where
          -- The member of e meeting r₁ cannot be p₁, so it is p₂; the member
          -- meeting r₂ cannot be p₂, so it is p₁. Both then lie in e, they are
          -- compatible, and e is an antichain, so p₁ ≈ˢ p₂.

          -- w₁ meets r₁ and lies in e ⊆ b, so it is p₁ or p₂; p₁ is r₁'s
          -- enemy, so w₁ is p₂ and p₂ ∈ e. Symmetrically p₁ ∈ e.

          finish : (Σ[ u ∈ S ] ⟨ (u ∈ˢ e) ⊓ compatibleΔ carrier order u r₁ ⟩)
                 → (Σ[ v ∈ S ] ⟨ (v ∈ˢ e) ⊓ compatibleΔ carrier order v r₂ ⟩)
                 → ⟨ ⊥ ⟩
          finish (u , hue , hur₁) (v , hve , hvr₂) =
            PT.rec (snd ⊥)
              (λ su → PT.rec (snd ⊥) (λ sv → close su sv) (pair v (esub v hve)))
              (pair u (esub u hue))
            where
              close : (⟨ u ≈ˢ p₁ ⟩ ⊎ ⟨ u ≈ˢ p₂ ⟩)
                    → (⟨ v ≈ˢ p₁ ⟩ ⊎ ⟨ v ≈ˢ p₂ ⟩) → ⟨ ⊥ ⟩
              close (inl⊎ h) _ =
                enemy₁ (subst (λ t → ⟨ compatibleΔ carrier order t r₁ ⟩)
                          (≈ˢ-to-path u p₁ h) hur₁)
              close (inr⊎ _) (inr⊎ h) =
                enemy₂ (subst (λ t → ⟨ compatibleΔ carrier order t r₂ ⟩)
                          (≈ˢ-to-path v p₂ h) hvr₂)
              close (inr⊎ hu₂) (inl⊎ hv₁) =
                ne (antichain-use carrier order e p₁ p₂ eac
                      (bsub p₁ hp₁)
                      (subst ⟨_⟩ (subst-member v p₁ e hv₁) hve)
                      (bsub p₂ hp₂)
                      (subst ⟨_⟩ (subst-member u p₂ e hu₂) hue)
                      cpp)

  ------------------------------------------------------------------------------
  -- PART 6. WHERE M's CHOICE ENTERS, AND WHAT IT DOES NOT REACH.
  -- SIBLING of module Free, deliberately.
  ------------------------------------------------------------------------------

  -- The greedy antichain, as a FIXPOINT rather than as a recursion. Classical
  -- set theory extends an antichain d to a maximal one by enumerating the
  -- carrier along a well ordering and adding each condition that is
  -- incompatible with everything taken so far. That is a definition by
  -- transfinite recursion. What a recursion produces can also be described,
  -- without any recursion, by the equation its output satisfies:
  --
  --   p ∈ e  iff  p ∈ carrier and ( p ∈ d  or  p is BLOCKED BY NOBODY )
  --
  -- where "blocked by nobody" means p meets no member of d and meets no member
  -- of e that precedes it. GreedySpec is that equation and nothing else.
  --
  -- THE THEOREM OF THIS PART is that the equation ALONE forces maximality. No
  -- recursion, no ordinal, no enumeration is used below: given ANY set
  -- satisfying GreedySpec, the three conclusions follow from the well
  -- ordering's trichotomy, the antichain law of d, and excluded middle. So the
  -- distance from GroundWellOrder to MaximalExtension is exactly one thing,
  -- the EXISTENCE of a solution, and PART 7 records that this file does not
  -- supply it.

  module FromChoice (wo : GroundWellOrder) where

    open Well wo

    Blocked : S → S → S → Ω
    Blocked d e p =
        ⋀ S (λ q → (q ∈ˢ d) ⇒ (compatibleΔ carrier order p q ⇒ ⊥))
      ⊓ ⋀ S (λ q → (q ∈ˢ e) ⇒ ((lt q p) ⇒ (compatibleΔ carrier order p q ⇒ ⊥)))

    GreedySpec : S → S → Ω
    GreedySpec d e =
      ⋀ S (λ p → iff (p ∈ˢ e)
            ((p ∈ˢ carrier) ⊓ ((p ∈ˢ d) ⊔ Blocked d e p)))

    -- A solution lies inside the carrier, by the forward half of its own
    -- equation, so subsetΔ e carrier is not a hypothesis.

    greedy-sub : (d e : S) → ⟨ GreedySpec d e ⟩ → ⟨ subsetΔ e carrier ⟩
    greedy-sub d e g p hp = fst (fst (g p) hp)

    -- And it contains d, by the backward half at the left disjunct. This is
    -- where the greedy equation earns the word "extension", and it costs
    -- nothing beyond d ⊆ carrier.

    greedy-ext : (d e : S) → ⟨ subsetΔ d carrier ⟩ → ⟨ GreedySpec d e ⟩
               → ⟨ subsetΔ d e ⟩
    greedy-ext d e dsub g p hp = snd (g p) (dsub p hp , ∣ inl⊎ hp ∣₁)

    -- ANTICHAIN. Take two compatible members of e and open both equations.
    -- Four cases. Both in d is d's own antichain law. One in d and the other
    -- blocked contradicts the blocked one's FIRST conjunct, which is exactly
    -- why that conjunct is in the equation: without it a late condition could
    -- be added on top of d. Both blocked is settled by trichotomy, and the two
    -- strict cases contradict the SECOND conjunct of the later one. Excluded
    -- middle is not used here.

    greedy-antichain : (d e : S) → ⟨ antichainΔ carrier order d ⟩
                     → ⟨ GreedySpec d e ⟩ → ⟨ antichainΔ carrier order e ⟩
    greedy-antichain d e dac g = antichain-intro carrier order e body
      where
        body : (p q : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ p ∈ˢ e ⟩
             → ⟨ q ∈ˢ carrier ⟩ → ⟨ q ∈ˢ e ⟩
             → ⟨ compatibleΔ carrier order p q ⟩ → ⟨ p ≈ˢ q ⟩
        body p q pc pe qc qe cpq =
          PT.rec (snd (p ≈ˢ q))
            (λ hp → PT.rec (snd (p ≈ˢ q)) (decide hp) (snd (fst (g q) qe)))
            (snd (fst (g p) pe))
          where
            cqp : ⟨ compatibleΔ carrier order q p ⟩
            cqp = subst ⟨_⟩ (compatibleΔ-sym carrier order p q) cpq

            decide : (⟨ p ∈ˢ d ⟩ ⊎ ⟨ Blocked d e p ⟩)
                   → (⟨ q ∈ˢ d ⟩ ⊎ ⟨ Blocked d e q ⟩) → ⟨ p ≈ˢ q ⟩
            decide (inl⊎ hp) (inl⊎ hq) =
              antichain-use carrier order d p q dac pc hp qc hq cpq
            decide (inl⊎ hp) (inr⊎ bq) = Empty.rec* (fst bq p hp cqp)
            decide (inr⊎ bp) (inl⊎ hq) = Empty.rec* (fst bp q hq cpq)
            decide (inr⊎ bp) (inr⊎ bq) = PT.rec (snd (p ≈ˢ q)) tri (lt-tri p q)
              where
                tri : ⟨ lt p q ⟩ ⊎ ((p ≡ q) ⊎ ⟨ lt q p ⟩) → ⟨ p ≈ˢ q ⟩
                tri (inl⊎ l)         = Empty.rec* (snd bq p pe l cqp)
                tri (inr⊎ (inl⊎ eq)) = path-to-≈ˢ p q eq
                tri (inr⊎ (inr⊎ l))  = Empty.rec* (snd bp q qe l cpq)

    -- PREDENSE, and this is the one place excluded middle is spent. Decide the
    -- goal itself. If some member of e meets q there is nothing to do. If none
    -- does, then q is blocked by nobody, for a reason that reads off the
    -- refusal: a member of d meeting q would be a member of e meeting q, since
    -- d ⊆ e, and a member of e meeting q is the very thing refused. So the
    -- equation puts q itself in e, and q meets itself.
    --
    -- LEM ℓ, and the ledger row is 1.3's: K7 names LEM ℓ, which the
    -- programme's single LEM (ℓ-suc ℓ) covers through lowerLEM
    -- (src/Base/Classical.lagda.md:82), and K7's net addition is zero. This is
    -- excluded middle and not choice: it decides one truth value and returns
    -- no witness.

    greedy-predense : LEM ℓ → (d e : S) → ⟨ subsetΔ d carrier ⟩
                    → ⟨ GreedySpec d e ⟩ → ⟨ predenseΔ carrier order e ⟩
    greedy-predense lem d e dsub g q hq = decide (lem goal)
      where
        goal : Ω
        goal = ⋁ S (λ p → (p ∈ˢ e) ⊓ compatibleΔ carrier order p q)

        meet : (r : S) → ⟨ r ∈ˢ e ⟩ → ⟨ compatibleΔ carrier order q r ⟩ → ⟨ goal ⟩
        meet r hr cqr =
          ∣ r , hr , subst ⟨_⟩ (compatibleΔ-sym carrier order q r) cqr ∣₁

        decide : ⟨ goal ⟩ ⊎ (⟨ goal ⟩ → Empty.⊥) → ⟨ goal ⟩
        decide (inl⊎ h) = h
        decide (inr⊎ nh) = ∣ q , inE , compat-refl q hq ∣₁
          where
            blocked : ⟨ Blocked d e q ⟩
            blocked =
                (λ r hr cqr → Empty.rec (nh (meet r (greedy-ext d e dsub g r hr) cqr)))
              , (λ r hr _ cqr → Empty.rec (nh (meet r hr cqr)))

            inE : ⟨ q ∈ˢ e ⟩
            inE = snd (g q) (hq , ∣ inr⊎ blocked ∣₁)

    -- THE REDUCTION. Any solution of the greedy equation IS a maximal
    -- antichain extending d. This is the theorem that makes the open item
    -- exactly one thing.

    greedy→maximal : LEM ℓ → (d e : S) → ⟨ subsetΔ d carrier ⟩
                   → ⟨ antichainΔ carrier order d ⟩ → ⟨ GreedySpec d e ⟩
                   → ⟨ ((subsetΔ d e) ⊓ (subsetΔ e carrier))
                     ⊓ maximalΔ carrier order e ⟩
    greedy→maximal lem d e dsub dac g =
        (greedy-ext d e dsub g , greedy-sub d e g)
      , maximal-intro carrier order e (greedy-antichain d e dac g)
                      (greedy-predense lem d e dsub g)

    -- THE OPEN ITEM, WITH A NAME AND A TYPE. GreedySupply says a solution
    -- exists. It is the fixpoint of a transfinite recursion along lt and
    -- nothing in this file, and nothing in the profile, produces one. Rule 15
    -- class (ii): at a genuine ZFC ground the recursion runs and the set
    -- exists, so the hypothesis is inhabited in principle; no filler exists
    -- anywhere in this tree, measured.

    GreedySupply : Type ℓ
    GreedySupply =
      (d : S) → ⟨ subsetΔ d carrier ⟩ → ⟨ antichainΔ carrier order d ⟩
      → ⟨ ⋁ S (λ e → GreedySpec d e) ⟩

    greedy→extension : LEM ℓ → GreedySupply → MaximalExtension
    greedy→extension lem gs d dsub dac =
      PT.map (λ { (e , g) → e , greedy→maximal lem d e dsub dac g })
             (gs d dsub dac)

    -- Rule 14's transcription for this part. This is what the roadmap asks K7
    -- to deliver and what this file does NOT deliver: MaximalExtension from
    -- the ground well ordering and the profile's axioms alone. IT IS NOT
    -- INHABITED IN THIS FILE. The three routes tried, and where each stops,
    -- are in the track report; the shortest statement of the stop is that
    -- Separation reads a Formula S 1 (OrdinaryProfile.agda:88-90) and there is
    -- no object-language formula for lt anywhere in this tree, so even the
    -- approximation method cannot cut its first set.

    ExtensionFromWellOrder : Type (ℓ-suc ℓ)
    ExtensionFromWellOrder = Separation → Collection → LEM ℓ → MaximalExtension
