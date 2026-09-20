{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track H. COFINALITY: THE VOCABULARY, AND THE STOP REPORT.
--
-- ---------------------------------------------------------------------
-- WHAT THIS FILE IS
-- ---------------------------------------------------------------------
--
-- Ruling Q4 briefed this track to ship the vocabulary plus a stop report by
-- design. It does. The model is K6 Track H (K6/Ordinals.agda), which shipped
-- the transport, the proved half, the exact open goal, a proved reduction from
-- that goal to the theorem, three routes each stopping at a named place, and
-- the theorem itself as an UNINHABITED type.
--
-- PROVED HERE.
--
--   * The cofinality vocabulary that the compile root does not have, as
--     object-language formulas with a reading theorem for EVERY one of them:
--     IsCofinalφ, IsRegularφ, Singularφ, Cofinalityφ. Every reading is a path
--     of hProps in K1's own idiom (CardinalBridge.agda:75, :537, :563), so a
--     later package instantiates them and never re-spells them.
--   * Δ₀-IsCofinalφ. Cofinality of a SUBSET is bounded, so it is absolute
--     along any Δ₀-preserving map. Regularity is not: IsRegularφ leads with an
--     unbounded ∀̇ over subsets, and that unbounded quantifier IS the theorem.
--   * singular→¬regular, free, one direction of the dichotomy, and
--     ¬regular→singular from LEM ℓ, so the classical step is visible.
--   * CofinalityRange, the exact range established, which is EMPTY, and
--     cofinality-range-empty says so by refl. roadmap:215 is the licence:
--     "General cofinality statements must specify the exact range established."
--   * ext-existential, by refl, and it is the measured correction this track
--     returns. See the next banner.
--   * chk-ordinal-up, goal→theorem, bounded→goal and cover→bounded: the whole
--     chain from ONE named prerequisite to the theorem. The gap is exactly
--     GroundCover and nothing else.
--   * cofinal-range→covering-range. Track F's ground residue ProvedRange
--     (K7/NoCollapse.agda:582-596) with COVERING weakened to COFINAL is
--     strictly the stronger hypothesis, PROVED, in one lemma. That is the
--     price of this track's ground half stated against a landed comparable
--     instead of against a guess.
--
-- NOT PROVED, AND THAT IS THE DELIVERABLE. RegularPreserved and
-- NoShortCofinal are shipped as TYPES WITH NO INHABITANT, on K6/Ordinals.agda's
-- model (NoNewOrdinals, :183-186) and K3's (Valuation.agda:693-715).
--
-- ---------------------------------------------------------------------
-- RULE 14. THE BRIEF'S FIRST AND FOURTH PREMISES ARE CONFIRMED, THE SECOND
-- IS REFUTED, AND THE CENSUS PREMISE IS WRONG ON ONE TOKEN
-- ---------------------------------------------------------------------
--
-- (1) CENSUS, re-measured over the whole compile root, at DECLARATION level,
-- because a raw token count over this root is not stable: six other K7 tracks
-- landed while this file was being written and every one of them mentions
-- these words in prose. The stable measurement is
--   grep -rnE --include='*.agda' '^ *<token>[A-Za-zΔφ]* +:' .
-- and before this file it returned, for the four tokens ruling Q4 names:
--   cofinal      0 declarations
--   cofinality   0 declarations
--   singular     0 declarations
--   isRegular    TWO declarations, not zero.
-- The two are HostRegularOpen.agda:229, `isRegular : Sub → Ω`, the REGULAR
-- OPEN predicate on subsets of the conditions, and CodedVocabulary.agda:303,
-- `isRegularΔ : S → S → S → Ω`, its coded form. THE ARCHITECTURE'S Q4
-- EVIDENCE LINE AND ITS SECTION 2.8 BOTH SAY isRegular MEASURES ZERO
-- DECLARATIONS, AND THAT IS FALSE. The token is taken, in a different sense,
-- by K2. What is missing is the CARDINAL sense, which is the sense ruling Q4
-- needs, so the ruling's conclusion survives its evidence. This file declares
-- isRegular in the cardinal sense inside module Vocabulary; the two senses
-- are never in one scope and nothing here imports HostRegularOpen. A future
-- census must key on the TYPE and not on the token.
--
-- (2) BELL 1.51(iv) DOES INVOKE THE MAXIMUM PRINCIPLE BY NAME, verified at
-- bell-2005-boolean-valued-models.fulltext.md, printed p. 51: "and so the
-- Maximum Principle yields an f ∈ V(B) for which a = [φ(f, β)]". Confirmed.
--
-- (3) K4/Witnesses.agda:842 reads, verbatim, "THE FULLNESS CONTRACT. NOTHING
-- BELOW THIS LINE IS INHABITED IN K4." record MaximumPrinciple is at :858-861
-- and record Fullness at :851-852. Confirmed.
--
-- (4) k4-architecture.md:998 refuses K7 by name, verbatim: "a K7 agent reading
-- Bell will find the Maximum Principle in its source proof and may request it
-- from K4; the answer is no." Confirmed. The SAME line also predicts the
-- repair: "The use looks removable by truncated elimination, because the goal
-- is that a Boolean value is bottom, a proposition."
--
-- (5) AND THE MEASURED CORRECTION. THE MAXIMUM PRINCIPLE IS NOT THIS TRACK'S
-- BLOCKER, AND K7 NEED NOT REQUEST IT. Bell needs 1.27 because he never leaves
-- V(B): to turn [∃f φ(f)] ≠ 0 into a single name f he must attain a supremum
-- in a Boolean algebra, and that is fullness. K6 has ALREADY left V(B). The
-- extension is presented as an ordinary first-order structure 𝒮ᴱ whose carrier
-- is Nm and whose satisfaction is FOL.Semantics' own, so
-- FOL/Semantics.lagda.md:120 reads an object existential as ⋁ Nm, a truncated
-- join over NAMES. ext-existential below proves that by refl. The truth lemma
-- K6/ForcesTruth.agda:316-317 is what paid for the move, and it is already
-- paid. So the existential step of Bell's proof is FREE here, the fullness
-- contract is not requested, and k4-architecture.md:998's prediction is
-- confirmed in a stronger form than it states: the repair is not a truncated
-- elimination, it is that the elimination never has to happen.
--
-- ---------------------------------------------------------------------
-- SO WHAT DOES BLOCK IT. THE COUNTING, AND IT IS ONE CLAUSE
-- ---------------------------------------------------------------------
--
-- With the existential free, Bell's proof reduces to Kunen's possible-value
-- argument, and this file carries that reduction as far as the compile root
-- allows. RegularPreserved reduces, in three proved steps, to GroundCover:
-- "a cofinal subset of chk α in the extension that injects into chk b for a
-- ground b ∈ α is COVERED by a ground cofinal subset of α that injects into a
-- member of α". Cover it and ground regularity closes the theorem, which is
-- cover→bounded, proved below.
--
-- THE COMPILE ROOT MOVED WHILE THIS FILE WAS BEING WRITTEN, AND THE PRICE IS
-- RE-MEASURED AGAINST WHAT IS THERE NOW, NOT AGAINST THE ARCHITECTURE'S G3.
-- Tracks B, E and F have landed. Item by item:
--
--   * valuesOf and its spec: LANDED, K7/PossibleValues.agda, on O7's general
--     forcesΔ (O7/Definability.agda:97-99) with the residue valΔ named at
--     O7/Supply.agda module Chain, plus ground Collection and Separation.
--     Track E does the ground set; it explicitly does no counting.
--   * COUNTABILITY of the possible-value set: LANDED AS AN ARROW, not as a
--     theorem. K7/NoCollapse.agda:512-516 proves countable-from-ccc₂ :
--     ValueAntichain → Collection → (w : S) → ⟨ CCC₂ᴵ c o w ⟩ →
--     CountableValues w. Its open premise ValueAntichain (:483-486) is the
--     "pick a condition deciding each possible value" step and is the one
--     place M's choice enters; Track F names it and takes neither side.
--     THE ARCHITECTURE'S D5 LIST IS STILL INCOMPLETE AS PRINTED: 2.5 and
--     4.6 list only valueFo, valuesOf, valuesOf-spec, values-covers and
--     values-bounded, and values-bounded is ⟨ subsetΔ (valuesOf …) β ⟩, a
--     subset statement. Track F supplied the missing row itself.
--   * GROUND CARDINAL ARITHMETIC. The architecture's G3, "injectable has ZERO
--     theorems", IS NOW STALE and this file will not repeat it. Re-measured
--     over the current root: K7/CardinalOrder.agda declares injectable-refl
--     (:950), injectable-trans (:1046), injectable-incl (:886),
--     injectable-mono-dom (:299), injectable-mono-cod (:308),
--     injectable-cong (:315) and injectable-cong-cod (:322), each on
--     Separation, Collection and Pairing. So "cf(α) = α for a regular α" is
--     no longer out of reach for lack of reflexivity.
--     WHAT IS STILL ABSENT IS THE UNION BOUND. Re-measured: no declaration
--     anywhere in the compile root states that a union of β-many w-countable
--     ground sets injects into anything, and no K7 file uses the Union axiom
--     at all. Track F does not prove it either; it states the consequence as
--     ProvedRange (K7/NoCollapse.agda:582-596) and tags it class (ii) with
--     the reason, "the ordinary profile has no ordinal arithmetic, no Hartogs
--     construction and no transfinite recursion".
--   * A GROUND ω ABOVE WHICH α LIES. Still a hypothesis. Bell opens 1.51(iv)
--     with "without loss of generality we may assume α > ℵ₀"; the ordinary
--     profile has no ω, Infinity (OrdinaryProfile.agda:83-86) is the truncated
--     inductive-set form, and K6/GroundTransfer.agda:501-502 takes ωᴳ as a
--     bare parameter with no isOmega hypothesis. Track F carries it as the
--     isOmega w argument of ProvedRangeHolds (:599-603).
--
-- SO THE RESIDUE IS ONE CLAUSE, AND THIS FILE PRICES IT AGAINST A LANDED
-- COMPARABLE. CofinalRange below is Track F's ProvedRange with the covering
-- clause `a ∈ v` weakened to `some m ∈ v with a ∈ m or a ≈ m`. Everything
-- else in the two statements is identical, character for character.
-- cofinal-range→covering-range PROVES that CofinalRange is the stronger
-- hypothesis. Track F's own header says the same thing in words at :22-25
-- and again at :765-772; this file says it in a type and proves the
-- comparison.
--
-- ---------------------------------------------------------------------
-- THREE ROUTES, EACH STOPPING AT A NAMED PLACE
-- ---------------------------------------------------------------------
--
-- ROUTE 1, Bell 1.51(iv) transcribed. Stops TWICE, and the second stop is the
-- one the architecture does not name. First, "the Maximum Principle yields an
-- f ∈ V(B) for which a = [φ(f, β)]" needs record MaximumPrinciple
-- (K4/Witnesses.agda:858-861), uninhabited under the banner at :842, refused
-- to K7 at k4-architecture.md:998, uniform form equivalent to AC (Bell Problem
-- 1.30, fulltext:2618-2640, transcribed at K4/Witnesses.agda:883-888), owner
-- K12a (roadmap:242). Second, and INDEPENDENTLY FATAL: Bell's next sentence is
-- "It follows that for each η < α there are ordinals ξη < β, µη < α such that
-- [f(ξη) = µη] ∧ a ≠ 0", which selects a PAIR PER η over an index set of size
-- α. That is a host selection function on an external family, which is the
-- exact thing roadmap:213 forbids and which the assumption ledger of the
-- shared preamble 1.3 rules out. Route 1 is dead even if K12a lands fullness.
--
-- ROUTE 2, Kunen's possible values, which is the live route. It does not use
-- the Maximum Principle at all, because ext-existential is refl and because
-- the failure of regularity at the extension hands over the injecting name as
-- a member of a ⋁ Nm join, not as a Boolean supremum. It runs through Track
-- E's valuesOf and Track F's countable-from-ccc₂, both landed, and stops at
-- the ground arithmetic: at GroundCover from this end, and at CofinalRange
-- from the other. THIS IS THE ROUTE A LATER PACKAGE SHOULD TAKE, and the file
-- is arranged so that supplying GroundCover alone finishes it.
--
-- AND A CORRECTION TO A LANDED FILE, rule 14, stated so it is not missed.
-- K7/NoCollapse.agda:765-772 diagnoses its own gap correctly ("a cofinal range
-- need not contain any given member of κ") and then attributes the blocker to
-- the Maximum Principle in the next sentence, repeating ruling Q4's evidence.
-- Those two sentences name different things and only the first is this
-- programme's obstruction. The Maximum Principle is Bell's device for
-- attaining a supremum inside V(B); K6 left V(B) and ext-existential proves
-- by refl that the attainment is free at the extension structure. The blocker
-- is the covering-versus-cofinal clause, which K7/NoCollapse.agda had already
-- identified. Track F's TYPE is right and one sentence of its prose is not.
--
-- ROUTE 3, Δ₀ absoluteness. Δ₀-IsCofinalφ is proved below, so a GROUND cofinal
-- subset of α stays cofinal at the extension; that is the easy direction and it
-- is the wrong one. IsRegularφ is NOT Δ₀: it opens with an unbounded ∀̇ over
-- subsets of α, and K5's groundSat (K5/Structures.agda:670-690, where ∃̇ and ∀̇
-- are absurd patterns on the Δ₀ witness) stops exactly there. It stops for a
-- reason: the extension has subsets of α the ground does not, and that is the
-- whole content of the theorem. Route 3 cannot be repaired, only replaced by
-- route 2. This is the same wall K6 met at K6/Ordinals.agda:39-80 and the same
-- wall architecture 4.7 records for isOmega.
--
-- ---------------------------------------------------------------------
-- RULE 15. THE TELESCOPE, CLASSIFIED. THE CLASS QUESTION IS WHETHER AN
-- INHABITANT EXISTS AT A GENUINE FORCING EXTENSION
-- ---------------------------------------------------------------------
--
--   𝒮              [i]   any ZFStructure over hPropAlgebra ℓ. Landed.
--   𝒯 of Vocabulary [i]  applied at 𝒮 and at 𝒮ᴱ only, both landed.
--   IsNm            [i]   K5/Structures.agda:588-589's name predicate.
--   _≈[G]_ _∈[G]_   [i]   the value relations, K5/Structures.agda:277.
--   ≈[G]-refl       [i]   PROVED, K5/Structures.agda exports ≈-refl at :277 and
--                         uses it at :378, :382, :387. Taken flat here.
--   chk             [i]   K5/Structures.agda:588-589, the check map.
--   chk-ordinal     [i]   K6/Ordinals.agda:179-180, a PATH, Δ₀ absoluteness of
--                         IsOrdinalφ along chk at ⟨ positive G ⟩.
--   sat-cong        [i]   K5/Structures.agda:400-402, unconditional.
--   positiveᴾ       [ii]  an Ω, opaque here. Inhabited at any genuine G.
--   copy-members    [i]   K6/GroundTransfer.agda:427-429, at ⟨ positiveᴾ ⟩
--                         alone. Transcribed in architecture 4.6's shape, with
--                         chk : S → Nm, which matches the source's groundName.
--   GroundCover     [ii]  OPEN. Inhabited at a genuine ccc extension; that is
--                         exactly Kunen's theorem. Priced above. Its ground
--                         half is Vocabulary.CofinalRange, also [ii], and
--                         cofinal-range→covering-range measures it strictly
--                         above Track F's landed ProvedRange.
--
-- NO SLOT IS CLASS (iii). The one shape that would be is "every extension
-- subset of chk α lies in the ground", which is Onto (K5/Structures.agda:
-- 532-533) in disguise and is false at every genuine extension. It is NOT a
-- parameter of any module below, and the forbidden-spelling sweep confirms it.
--
-- ---------------------------------------------------------------------
-- WHAT IS NOT CLAIMED
-- ---------------------------------------------------------------------
--
-- No inhabitant of RegularPreserved, NoShortCofinal, GroundCover, OpenGoal,
-- CofinalRange or CoveringRange. No use of the Maximum Principle, fullness,
-- a refinement, a mixture or a value cover, in any spelling, and none of
-- those records is imported. No host choice of any kind: every join below is over the carrier
-- S of a structure or over Nm, and every elimination of one lands in a
-- proposition. No claim that cofinality preservation holds; no claim that it
-- fails. The measured claim is that it reduces to GroundCover and stops.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Manipulation.Renaming using ( renameFo )
import FOL.Semantics
import CardinalBridge
open import Base.Classical using ( LEM )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Functions.Logic as Logic
import Cubical.Data.Empty as Empty

module K7.Cofinality {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Unit using ( tt )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- PART 1. THE VOCABULARY, STRUCTURE POLYMORPHIC
--------------------------------------------------------------------------------

-- The module is parameterized by the structure and not by 𝒮, so it is applied
-- once at the ground and once at the extension and the formulas are written
-- ONCE. That is trap T-H3 of K6/Ordinals.agda:11-18 observed in advance:
-- re-spelling a nested bounded quantifier at a second structure is how K1's
-- IsOrdinalφ linearity defect was introduced, and only a reading theorem
-- catches it.

module Vocabulary (𝒯 : ZFStructure (hPropAlgebra ℓ)) where

  open hPropStructure 𝒯 public using ( S ; isSetS ; _≈ˢ_ ; _∈ˢ_ )

  module CB = CardinalBridge 𝒯
  open CB public
    using ( IsOrdinalφ ; isOrdinal ; IsOrdinal-bridge
          ; Injectableφ ; injectable ; Injectable-bridge
          ; IsInjectionφ ; isInjection ; IsInjection-bridge
          ; isSubset ; same ; ¬-as-⇒⊥ )
  open CB.Ren using ( Agrees ; ⊨-rename )

  private module Sem = FOL.Semantics (hPropAlgebra ℓ) 𝒯
  module SatT = Sem.At S id
  open SatT public using ( _⊨_ )

  ------------------------------------------------------------------------
  -- Subset, in the BOUNDED spelling
  ------------------------------------------------------------------------

  -- K1's Subsetφ (CardinalBridge.agda:68-70) leads with an unbounded ∀̇ and so
  -- carries no Δ₀ witness; CodedVocabulary.agda:22-26 records that objection
  -- in its own words. Cofinality is a bounded notion and must stay one, so the
  -- subset clause is respelled with ∀̇∈ here. The HOST side is K1's isSubset
  -- unchanged, and the reading is refl, which is what says the respelling
  -- changed the syntax and not the meaning.

  SubsetBφ : Formula S 2
  SubsetBφ = ∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero)))

  SubsetB-bridge : (a α : S) → ((a ∷ α ∷ []) ⊨ SubsetBφ) ≡ isSubset a α
  SubsetB-bridge a α = refl

  ------------------------------------------------------------------------
  -- Cofinal
  ------------------------------------------------------------------------

  -- Env (a ∷ α ∷ []), reading "a is a cofinal subset of α": a ⊆ α, and every
  -- member of α is below-or-equal to some member of a. "Below" is membership,
  -- the von Neumann order, exactly as IsCardinalφ (CardinalBridge.agda:541-542)
  -- uses it.
  --
  -- The de Bruijn arithmetic, written out because rule 6 says a uniform-depth
  -- formula gets NO protection from intrinsic scoping. Under ∀̇∈ the
  -- environment grows by one: at the body of the outer bounded quantifier the
  -- slots are (η ∷ a ∷ α ∷ []), so var (suc zero) is a and bounds the inner
  -- quantifier; at the body of the inner one they are (µ ∷ η ∷ a ∷ α ∷ []), so
  -- var (suc zero) is η and var zero is µ. Swapping those last two is the K5
  -- Track C defect, and K7/breaks/CofinalSwap.agda-break is exactly that swap.

  IsCofinalφ : Formula S 2
  IsCofinalφ =
    SubsetBφ
    ∧̇ (∀̇∈ (var (suc zero))
         (∃̇∈ (var (suc zero))
           ((var (suc zero) ∈̇ var zero) ∨̇ (var (suc zero) ≐ var zero))))

  isCofinal : S → S → Ω
  isCofinal a α =
    (isSubset a α)
    ⊓ (⋀ S (λ η → (η ∈ˢ α) ⇒
        (⋁ S (λ µ → (µ ∈ˢ a) ⊓ ((η ∈ˢ µ) ⊔ (η ≈ˢ µ))))))

  IsCofinal-bridge : (a α : S) → ((a ∷ α ∷ []) ⊨ IsCofinalφ) ≡ isCofinal a α
  IsCofinal-bridge a α = refl

  Δ₀-IsCofinalφ : Δ₀ IsCofinalφ
  Δ₀-IsCofinalφ = checkΔ₀ IsCofinalφ tt

  ------------------------------------------------------------------------
  -- Regular, in the cardinal sense
  ------------------------------------------------------------------------

  -- Env (α ∷ []), reading "α is an ordinal no cofinal subset of which injects
  -- into a member of α". Countability is `injectable` against a supplied set,
  -- which is the only cardinal comparison the programme has
  -- (CardinalBridge.agda:379-388) and the only one that hands back no selector:
  -- it is a truncated join.
  --
  -- NAME COLLISION, and it is measured. HostRegularOpen.agda:229 declares
  -- isRegular : Sub → Ω for REGULAR OPEN subsets of the conditions, and
  -- CodedVocabulary.agda:303 declares isRegularΔ. Neither is imported here and
  -- neither is ever in the same scope as this one, but a census keyed on the
  -- token now returns both senses. Key on the type.
  --
  -- IsRegularφ IS NOT Δ₀ and must not be: the ∀̇ ranges over all subsets of α,
  -- and the extension has subsets the ground does not. That single unbounded
  -- quantifier is the entire theorem.
  --
  -- No side condition is folded in, following K1's convention for isOrdinal
  -- and isCardinal: the predicate does not presuppose that α is a limit or a
  -- cardinal, and a consumer that wants either conjoins it. Read at a
  -- successor ordinal the predicate is simply false once α has two members,
  -- since a singleton is cofinal and injects into a member, which is the
  -- classical cf(β+1) = 1; that is a property of the definition and not an
  -- omission.

  reg-inj : Fin 2 → Fin 3
  reg-inj zero       = suc zero
  reg-inj (suc zero) = zero

  IsRegularφ : Formula S 1
  IsRegularφ =
    IsOrdinalφ
    ∧̇ (∀̇ (IsCofinalφ
          ⇒̇ (∀̇∈ (var (suc zero)) (¬̇ (renameFo reg-inj Injectableφ)))))

  isRegular : S → Ω
  isRegular α =
    (isOrdinal α)
    ⊓ (⋀ S (λ a → (isCofinal a α) ⇒
        (⋀ S (λ β → (β ∈ˢ α) ⇒ ¬ (injectable a β)))))

  reg-inj-agrees : (a α β : S)
    → Agrees reg-inj (β ∷ a ∷ α ∷ []) (a ∷ β ∷ [])
  reg-inj-agrees a α β zero       = refl
  reg-inj-agrees a α β (suc zero) = refl

  IsRegular-bridge : (α : S) → ((α ∷ []) ⊨ IsRegularφ) ≡ isRegular α
  IsRegular-bridge α =
    cong₂ _⊓_ (IsOrdinal-bridge α)
      (cong (⋀ S) (funExt (λ a →
        cong₂ _⇒_ (IsCofinal-bridge a α)
          (cong (⋀ S) (funExt (λ β →
            cong ((β ∈ˢ α) ⇒_)
              (cong (_⇒ ⊥)
                (⊨-rename reg-inj Injectableφ (β ∷ a ∷ α ∷ []) (a ∷ β ∷ [])
                  (reg-inj-agrees a α β)
                 ∙ Injectable-bridge a β)
               ∙ sym (¬-as-⇒⊥ (injectable a β)))))))))

  ------------------------------------------------------------------------
  -- Singular
  ------------------------------------------------------------------------

  -- Env (α ∷ []). The POSITIVE form, not ¬̇ IsRegularφ, so that a witness can
  -- be read off it. The renaming is the same one IsRegularφ uses, because the
  -- environment under ∃̇ has the same shape as the one under ∀̇.

  Singularφ : Formula S 1
  Singularφ =
    IsOrdinalφ
    ∧̇ (∃̇ (IsCofinalφ
          ∧̇ (∃̇∈ (var (suc zero)) (renameFo reg-inj Injectableφ))))

  isSingular : S → Ω
  isSingular α =
    (isOrdinal α)
    ⊓ (⋁ S (λ a → (isCofinal a α)
        ⊓ (⋁ S (λ β → (β ∈ˢ α) ⊓ (injectable a β)))))

  Singular-bridge : (α : S) → ((α ∷ []) ⊨ Singularφ) ≡ isSingular α
  Singular-bridge α =
    cong₂ _⊓_ (IsOrdinal-bridge α)
      (cong (⋁ S) (funExt (λ a →
        cong₂ _⊓_ (IsCofinal-bridge a α)
          (cong (⋁ S) (funExt (λ β →
            cong ((β ∈ˢ α) ⊓_)
              (⊨-rename reg-inj Injectableφ (β ∷ a ∷ α ∷ []) (a ∷ β ∷ [])
                (reg-inj-agrees a α β)
               ∙ Injectable-bridge a β)))))))

  -- One direction is free and needs nothing. Both eliminations land in the
  -- library's ⊥, a proposition, so PT.rec is legitimate and no fst is
  -- projected out of a truncation.

  singular→¬regular : (α : S) → ⟨ isSingular α ⟩ → ⟨ ¬ (isRegular α) ⟩
  singular→¬regular α (_ , w) (_ , r) =
    PT.rec Empty.isProp⊥
      (λ { (a , hcof , wβ) →
        PT.rec Empty.isProp⊥
          (λ { (β , hβ , hinj) → r a hcof β hβ hinj })
          wβ })
      w

  -- The converse is the classical step, and naming LEM as an ARGUMENT of the
  -- one declaration that spends it is ruling D4's shape (architecture 4.0).
  -- LEM ℓ is covered by the programme's single LEM (ℓ-suc ℓ) through lowerLEM
  -- (src/Base/Classical.lagda.md:82), so K7's net addition here is zero. This
  -- is a USAGE fact and not an independence claim; the two kinds of zero are
  -- kept apart in the ledger.

  ¬regular→singular : LEM ℓ → (α : S) → ⟨ isOrdinal α ⟩
                    → ⟨ ¬ (isRegular α) ⟩ → ⟨ isSingular α ⟩
  ¬regular→singular lem α hord nreg = decide (lem witness)
    where
    witness : Ω
    witness =
      ⋁ S (λ a → (isCofinal a α) ⊓ (⋁ S (λ β → (β ∈ˢ α) ⊓ (injectable a β))))

    decide : ⟨ witness ⟩ ⊎ (⟨ witness ⟩ → Empty.⊥) → ⟨ isSingular α ⟩
    decide (inl w)  = hord , w
    decide (inr nw) =
      Empty.rec (nreg (hord , λ a hcof β hβ hinj →
        nw ∣ a , hcof , ∣ β , hβ , hinj ∣₁ ∣₁))

  ------------------------------------------------------------------------
  -- Cofinality, as a RELATION
  ------------------------------------------------------------------------

  -- The syntax has no function symbols, so "cf(α)" is not a term and never can
  -- be; CardinalBridge.agda:7-9 states the rule. Env (δ ∷ α ∷ []), reading
  -- "δ is a cofinality of α": δ is an ordinal, some cofinal subset of α injects
  -- into δ, and no cofinal subset of α injects into any member of δ. Three
  -- embeddings are needed because the three clauses bind different depths.

  cf-ord : Fin 1 → Fin 2
  cf-ord zero = zero

  cf-sub : Fin 2 → Fin 3
  cf-sub zero       = zero
  cf-sub (suc zero) = suc (suc zero)

  cf-inj : Fin 2 → Fin 3
  cf-inj zero       = zero
  cf-inj (suc zero) = suc zero

  cf-sub' : Fin 2 → Fin 4
  cf-sub' zero       = zero
  cf-sub' (suc zero) = suc (suc (suc zero))

  cf-inj' : Fin 2 → Fin 4
  cf-inj' zero       = zero
  cf-inj' (suc zero) = suc zero

  Cofinalityφ : Formula S 2
  Cofinalityφ =
    (renameFo cf-ord IsOrdinalφ)
    ∧̇ ((∃̇ ((renameFo cf-sub IsCofinalφ) ∧̇ (renameFo cf-inj Injectableφ)))
    ∧̇ (∀̇∈ (var zero)
         (∀̇ ((renameFo cf-sub' IsCofinalφ)
             ⇒̇ (¬̇ (renameFo cf-inj' Injectableφ))))))

  isCofinalityOf : S → S → Ω
  isCofinalityOf δ α =
    (isOrdinal δ)
    ⊓ ((⋁ S (λ a → (isCofinal a α) ⊓ (injectable a δ)))
    ⊓ (⋀ S (λ γ → (γ ∈ˢ δ) ⇒
         (⋀ S (λ a → (isCofinal a α) ⇒ ¬ (injectable a γ))))))

  cf-ord-agrees : (δ α : S) → Agrees cf-ord (δ ∷ α ∷ []) (δ ∷ [])
  cf-ord-agrees δ α zero = refl

  cf-sub-agrees : (a δ α : S)
    → Agrees cf-sub (a ∷ δ ∷ α ∷ []) (a ∷ α ∷ [])
  cf-sub-agrees a δ α zero       = refl
  cf-sub-agrees a δ α (suc zero) = refl

  cf-inj-agrees : (a δ α : S)
    → Agrees cf-inj (a ∷ δ ∷ α ∷ []) (a ∷ δ ∷ [])
  cf-inj-agrees a δ α zero       = refl
  cf-inj-agrees a δ α (suc zero) = refl

  cf-sub'-agrees : (a γ δ α : S)
    → Agrees cf-sub' (a ∷ γ ∷ δ ∷ α ∷ []) (a ∷ α ∷ [])
  cf-sub'-agrees a γ δ α zero       = refl
  cf-sub'-agrees a γ δ α (suc zero) = refl

  cf-inj'-agrees : (a γ δ α : S)
    → Agrees cf-inj' (a ∷ γ ∷ δ ∷ α ∷ []) (a ∷ γ ∷ [])
  cf-inj'-agrees a γ δ α zero       = refl
  cf-inj'-agrees a γ δ α (suc zero) = refl

  Cofinality-bridge : (δ α : S)
    → ((δ ∷ α ∷ []) ⊨ Cofinalityφ) ≡ isCofinalityOf δ α
  Cofinality-bridge δ α = cong₂ _⊓_ part1 (cong₂ _⊓_ part2 part3)
    where
    part1 : ((δ ∷ α ∷ []) ⊨ (renameFo cf-ord IsOrdinalφ)) ≡ isOrdinal δ
    part1 =
      ⊨-rename cf-ord IsOrdinalφ (δ ∷ α ∷ []) (δ ∷ []) (cf-ord-agrees δ α)
      ∙ IsOrdinal-bridge δ

    inner2 : (a : S)
      → ((a ∷ δ ∷ α ∷ [])
          ⊨ ((renameFo cf-sub IsCofinalφ) ∧̇ (renameFo cf-inj Injectableφ)))
        ≡ ((isCofinal a α) ⊓ (injectable a δ))
    inner2 a =
      cong₂ _⊓_
        (⊨-rename cf-sub IsCofinalφ (a ∷ δ ∷ α ∷ []) (a ∷ α ∷ [])
          (cf-sub-agrees a δ α)
         ∙ IsCofinal-bridge a α)
        (⊨-rename cf-inj Injectableφ (a ∷ δ ∷ α ∷ []) (a ∷ δ ∷ [])
          (cf-inj-agrees a δ α)
         ∙ Injectable-bridge a δ)

    part2 : ((δ ∷ α ∷ [])
             ⊨ (∃̇ ((renameFo cf-sub IsCofinalφ) ∧̇ (renameFo cf-inj Injectableφ))))
            ≡ (⋁ S (λ a → (isCofinal a α) ⊓ (injectable a δ)))
    part2 = cong (⋁ S) (funExt inner2)

    inner3 : (γ a : S)
      → ((a ∷ γ ∷ δ ∷ α ∷ [])
          ⊨ ((renameFo cf-sub' IsCofinalφ)
             ⇒̇ (¬̇ (renameFo cf-inj' Injectableφ))))
        ≡ ((isCofinal a α) ⇒ ¬ (injectable a γ))
    inner3 γ a =
      cong₂ _⇒_
        (⊨-rename cf-sub' IsCofinalφ (a ∷ γ ∷ δ ∷ α ∷ []) (a ∷ α ∷ [])
          (cf-sub'-agrees a γ δ α)
         ∙ IsCofinal-bridge a α)
        (cong (_⇒ ⊥)
          (⊨-rename cf-inj' Injectableφ (a ∷ γ ∷ δ ∷ α ∷ []) (a ∷ γ ∷ [])
            (cf-inj'-agrees a γ δ α)
           ∙ Injectable-bridge a γ)
         ∙ sym (¬-as-⇒⊥ (injectable a γ)))

    part3 : ((δ ∷ α ∷ [])
             ⊨ (∀̇∈ (var zero)
                  (∀̇ ((renameFo cf-sub' IsCofinalφ)
                      ⇒̇ (¬̇ (renameFo cf-inj' Injectableφ))))))
            ≡ (⋀ S (λ γ → (γ ∈ˢ δ)
                 ⇒ (⋀ S (λ a → (isCofinal a α) ⇒ ¬ (injectable a γ)))))
    part3 =
      cong (⋀ S) (funExt (λ γ →
        cong ((γ ∈ˢ δ) ⇒_) (cong (⋀ S) (funExt (inner3 γ)))))

  ------------------------------------------------------------------------
  -- The ground arithmetic, in Track F's own shape, with ONE word changed
  ------------------------------------------------------------------------

  -- K7/NoCollapse.agda landed while this file was being written, and it
  -- states the ground half of the surjection argument as ProvedRange
  -- (K7/NoCollapse.agda:582-596, read at source): "for no β ∈ κ is κ COVERED
  -- by a family of at most β-many w-countable ground sets". Its header at
  -- :22-25 and its NotClaimed-Regularity at :765-772 both say, correctly, why
  -- that does not reach cofinality: "A cofinal range need not contain any
  -- given member of κ, only lie unboundedly below it."
  --
  -- CoveringRange below is that statement transcribed at a general α, and
  -- CofinalRange is the SAME statement with `contains` weakened to `is below
  -- or equal to`. The two differ in exactly one clause and the second is what
  -- regularity preservation needs.

  CoveringRange : S → S → Ω
  CoveringRange α w =
    ⋀ S (λ β → (β ∈ˢ α) ⇒
      ⋀ S (λ F →
        ((injectable F β)
         ⊓ ((⋀ S (λ v → (v ∈ˢ F) ⇒ (injectable v w)))
         ⊓ (⋀ S (λ a → (a ∈ˢ α) ⇒ (⋁ S (λ v → (v ∈ˢ F) ⊓ (a ∈ˢ v)))))))
        ⇒ ⊥))

  CofinalRange : S → S → Ω
  CofinalRange α w =
    ⋀ S (λ β → (β ∈ˢ α) ⇒
      ⋀ S (λ F →
        ((injectable F β)
         ⊓ ((⋀ S (λ v → (v ∈ˢ F) ⇒ (injectable v w)))
         ⊓ (⋀ S (λ a → (a ∈ˢ α) ⇒
              (⋁ S (λ v → (v ∈ˢ F)
                 ⊓ (⋁ S (λ m → (m ∈ˢ v) ⊓ ((a ∈ˢ m) ⊔ (a ≈ˢ m))))))))))
        ⇒ ⊥))

  -- AND THE COMPARISON IS PROVED, WHICH IS WHAT PRICES THE GAP. The cofinal
  -- form is STRICTLY the stronger hypothesis: every covering family is a
  -- cofinal one, witnessed by m := a, so a supplier of CofinalRange supplies
  -- Track F's ProvedRange for free and not conversely. That is the exact sense
  -- in which Track H's ground residue is harder than Track F's, and it is the
  -- reason Track F's argument stops where it says it does. Nothing in this
  -- file supplies either.

  cofinal-range→covering-range :
      ((x : S) → ⟨ x ≈ˢ x ⟩)
    → (α w : S) → ⟨ CofinalRange α w ⟩ → ⟨ CoveringRange α w ⟩
  cofinal-range→covering-range rfl α w cr β hβ F (hFβ , hcount , hcov) =
    cr β hβ F
      (hFβ , hcount ,
       λ a ha → PT.map
         (λ { (v , hv , hav) → v , hv , ∣ a , hav , Logic.inr (rfl a) ∣₁ })
         (hcov a ha))

module Vᴳ = Vocabulary 𝒮
open Vᴳ using ( S ; isSetS ; _≈ˢ_ ; _∈ˢ_ )

--------------------------------------------------------------------------------
-- PART 2. THE EXACT RANGE ESTABLISHED, AND IT IS EMPTY
--------------------------------------------------------------------------------

-- roadmap:215, verbatim: "General cofinality statements must specify the exact
-- range established, rather than promise every future variant." This is that
-- specification. The range of ground ordinals whose cofinality K7 proves is
-- preserved is the EMPTY predicate, and cofinality-range-empty says so by refl
-- rather than in a comment, so a reader cannot mistake a silence for a claim.
--
-- The predicate is shipped anyway, at S → Ω and not as a Type, because a later
-- package that closes GroundCover replaces the body and every consumer's type
-- is unchanged. That is what a range predicate is for.

CofinalityRange : S → Ω
CofinalityRange _ = ⊥

cofinality-range-empty : (κ : S) → CofinalityRange κ ≡ ⊥
cofinality-range-empty κ = refl

--------------------------------------------------------------------------------
-- PART 3. THE EXTENSION, AND THE STOP
--------------------------------------------------------------------------------

-- The spine is K6/Ordinals.agda:126-141 verbatim in shape: a name predicate, a
-- carrier by Σ, the two value relations, and 𝒮ᴱ as a flat record literal. K6
-- measured the whole pattern at 0.69 s. Nothing here applies K5.Structures,
-- K5.Truth, K5.Frame, K6.ForcesTruth, CodedCompletion.Core or
-- Certificate.Nonzero; shared preamble 1.7 forbids it outside a named seam
-- probe and the reason is the measured 102.95 s / 9.08 GB of that composition.

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

    -- The vocabulary at the extension. Not one formula is written twice: the
    -- SAME module is applied at a second structure, which is how K6 discharged
    -- trap T-H3 (K6/Ordinals.agda:150-152) and how this file discharges it.

    module Vᴱ = Vocabulary 𝒮ᴱ

    ----------------------------------------------------------------------
    -- THE MEASURED CORRECTION, IN TWO LINES OF PROOF
    ----------------------------------------------------------------------

    -- Bell 1.51(iv) reads, at the printed page 51 of
    -- bell-2005-boolean-valued-models.fulltext.md:
    --
    --     "Hence there is β < α such that 0 ≠ [∃f φ(f, β)] = a, say, and so
    --      the Maximum Principle yields an f ∈ V(B) for which a = [φ(f, β)]."
    --
    -- That step is attainment of a supremum in a Boolean algebra at a single
    -- name, which is fullness, which is record MaximumPrinciple at
    -- K4/Witnesses.agda:858-861, uninhabited under the banner at :842 and
    -- refused to K7 by name at k4-architecture.md:998.
    --
    -- IT IS NOT NEEDED, AND THE PROOF IS refl. K6 has already left V(B): the
    -- extension is an ordinary first-order structure and FOL.Semantics reads
    -- an object existential as ⋁ over the CARRIER (FOL/Semantics.lagda.md:120),
    -- which here is Nm. So the value of ∃̇ φ at the extension IS a truncated
    -- join over names and an inhabitant of it IS a name, with no supremum to
    -- attain. What paid for the move is the truth lemma, K6/ForcesTruth.agda:
    -- 316-317, and it is already paid.

    ext-existential : ∀ {k} (φ : Formula Nm (suc k)) (ν : Vec Nm k)
                    → (ν Vᴱ.⊨ (∃̇ φ)) ≡ ⋁ Nm (λ τ → (τ ∷ ν) Vᴱ.⊨ φ)
    ext-existential φ ν = refl

    -- The instance Bell's proof actually consumes, stated so that no reader
    -- has to redo the reduction: the failure of a cardinal comparison at the
    -- extension hands over the injecting NAME, merely, and that is the whole
    -- of what the Maximum Principle was being asked for.

    ext-injection-name : (A B : Nm) → ⟨ Vᴱ.injectable A B ⟩
                       → ∥ Σ[ F ∈ Nm ] ⟨ Vᴱ.isInjection F A B ⟩ ∥₁
    ext-injection-name A B h = h

    ----------------------------------------------------------------------
    -- The reduction chain, and the one thing it stops at
    ----------------------------------------------------------------------

    Agree : ∀ {k} → Vec Nm k → Vec Nm k → Type ℓ
    Agree {k} ν μ = (ix : Fin k) → ⟨ fst (lookup ix ν) ≈[G] fst (lookup ix μ) ⟩

    -- The STATEMENTS depend on the check map and on nothing else. They are
    -- separated from the reduction so that a later package, and the break
    -- files, can name the shipped type without filling six slots that the type
    -- does not mention. Rule 13: derive the hypotheses from what the statement
    -- actually uses.

    module Statements (chk : S → Nm) where

      --------------------------------------------------------------------
      -- THE TWO STATEMENTS, SHIPPED WITH NO INHABITANT
      --------------------------------------------------------------------

      -- Architecture 4.8 asks for regular-preserved and no-short-cofinal or a
      -- stop report. These are those two theorems, written down exactly, and
      -- NOTHING IN THIS FILE INHABITS EITHER. Every arrow proved after them is
      -- an arrow INTO them from a hypothesis that is itself not inhabited here.

      RegularPreserved : Type ℓ
      RegularPreserved =
        (α : S) → ⟨ Vᴳ.isRegular α ⟩ → ⟨ Vᴱ.isRegular (chk α) ⟩

      NoShortCofinal : Type ℓ
      NoShortCofinal =
        (α : S) → ⟨ Vᴳ.isRegular α ⟩
        → (A : Nm) → ⟨ Vᴱ.isCofinal A (chk α) ⟩
        → (b : S) → ⟨ b ∈ˢ α ⟩ → ⟨ Vᴱ.injectable A (chk b) ⟩ → Empty.⊥

      -- THE EXACT OPEN GOAL. Given chk-ordinal-up below, RegularPreserved is
      -- equivalent to this, and this is the second conjunct of extension
      -- regularity and nothing else.

      OpenGoal : Type ℓ
      OpenGoal =
        (α : S) → ⟨ Vᴳ.isRegular α ⟩
        → (A : Nm) → ⟨ Vᴱ.isCofinal A (chk α) ⟩
        → (B : Nm) → ⟨ B Vᴱ.∈ˢ chk α ⟩
        → ⟨ Vᴱ.injectable A B ⟩ → Empty.⊥

      --------------------------------------------------------------------
      -- THE PREREQUISITE, AS ONE TYPE, AND THE ARROW OUT OF IT
      --------------------------------------------------------------------

      -- GroundCover is the ccc counting argument and it is the WHOLE of the
      -- gap. Read it as: a short cofinal subset of chk α at the extension is
      -- covered by a short cofinal subset of α in the ground. Kunen's proof
      -- builds the cover from the possible-value sets of the injecting name,
      -- one ground set per index, countable by the chain condition.
      --
      -- The price is itemized in this file's header banner, re-measured
      -- against the compile root as it stands after Tracks B, E and F landed:
      -- valuesOf is landed, the countability step is landed as an arrow off
      -- the open ValueAntichain, the injectable order theory is landed, and
      -- the single thing still absent anywhere in the root is the UNION BOUND,
      -- which Track F also declines and tags class (ii). The other end of the
      -- same gap is Vocabulary.CofinalRange, and cofinal-range→covering-range
      -- proves it is strictly stronger than Track F's landed ProvedRange.
      --
      -- Supply GroundCover and cover→theorem closes the track. Nothing else
      -- in this file is open.
      --
      -- RULE 15 ON THIS TYPE, AND IT IS THE SHARPEST THING IN THE FILE. The
      -- type does NOT force the cover to be built. K7/breaks/HostCofinalCover
      -- .agda-break fills it from a bare host function pick : Nm → S in one
      -- line, at exit 0, exactly as Track D's HostSelector fills WithSelection.
      -- What must protect a real supplier is that the cover is CONSTRUCTED by
      -- ground Collection out of valuesOf, never chosen; and, as Track D
      -- measured, that protection is carried by module structure and is
      -- invisible to the typechecker.

      GroundCover : Type ℓ
      GroundCover =
        (α : S) (A : Nm) → ⟨ Vᴱ.isCofinal A (chk α) ⟩
        → (b : S) → ⟨ b ∈ˢ α ⟩ → ⟨ Vᴱ.injectable A (chk b) ⟩
        → ⟨ ⋁ S (λ u → (Vᴳ.isCofinal u α)
             ⊓ (⋁ S (λ β → (β ∈ˢ α) ⊓ (Vᴳ.injectable u β)))) ⟩

      -- Proved. A ground cofinal subset of α that injects into a member of α
      -- contradicts ground regularity on the nose, so the cover is the whole
      -- of the remaining work.

      cover→bounded : GroundCover → NoShortCofinal
      cover→bounded gc α hα A hA b hb hinj =
        PT.rec Empty.isProp⊥
          (λ w →
            PT.rec Empty.isProp⊥
              (λ v → snd hα (fst w) (fst (snd w))
                       (fst v) (fst (snd v)) (snd (snd v)))
              (snd (snd w)))
          (gc α A hA b hb hinj)

    module Preserve
      -- [i] K5/Structures.agda:277 exports ≈-refl; it is used there at :378,
      -- :382 and :387. Flat, as the shared spine requires.
      (≈[G]-refl : (m : S) → ⟨ m ≈[G] m ⟩)
      -- [i] the check map, K5/Structures.agda:588-589.
      (chk : S → Nm)
      -- [i] K6/Ordinals.agda:179-180, a PATH in both directions. Δ₀
      -- absoluteness of IsOrdinalφ along chk, at ⟨ positive G ⟩ and nothing
      -- else. IsOrdinalφ carries no constants, so no relabelling is needed.
      (chk-ordinal : (a : S)
                   → ((chk a ∷ []) Vᴱ.⊨ Vᴱ.IsOrdinalφ)
                     ≡ ((a ∷ []) Vᴳ.⊨ Vᴳ.IsOrdinalφ))
      -- [i] K5/Structures.agda:400-402, unconditional.
      (sat-cong : ∀ {k} (ψ : Formula Nm k) (ν μ : Vec Nm k) → Agree ν μ
                → (ν Vᴱ.⊨ ψ) ≡ (μ Vᴱ.⊨ ψ))
      -- [ii] an Ω, opaque. Inhabited at any genuine generic filter.
      (positiveᴾ : Ω)
      -- [i] K6/GroundTransfer.agda:427-429, at ⟨ positiveᴾ ⟩ alone, in
      -- architecture 4.6's printed shape with chk : S → Nm. At source the
      -- check map is split as chk : S → S beside groundName : S → Nm, and
      -- fst (chk a) here is that source chk.
      (copy-members : ⟨ positiveᴾ ⟩ → (a : S) (τ : Nm) → ⟨ τ Vᴱ.∈ˢ chk a ⟩
                    → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ ≈[G] fst (chk y))) ⟩)
      where

      open Statements chk public

      --------------------------------------------------------------------
      -- THE HALF THAT IS PROVED
      --------------------------------------------------------------------

      -- The ordinal conjunct of regularity transports for free, because
      -- chk-ordinal is a PATH and IsOrdinal-bridge is refl at both structures.
      -- No rank, no filter law, no excluded middle. This is architecture 2.6's
      -- first observation at the cofinality predicate rather than at isCardinal.

      chk-ordinal-up : (α : S) → ⟨ Vᴳ.isOrdinal α ⟩ → ⟨ Vᴱ.isOrdinal (chk α) ⟩
      chk-ordinal-up α h =
        subst ⟨_⟩
          (sym (Vᴳ.IsOrdinal-bridge α)
           ∙ sym (chk-ordinal α)
           ∙ Vᴱ.IsOrdinal-bridge (chk α))
          h

      goal→theorem : OpenGoal → RegularPreserved
      goal→theorem g α hα =
        chk-ordinal-up α (fst hα) , λ A hA B hB hinj → g α hα A hA B hB hinj

      --------------------------------------------------------------------
      -- THE INNER QUANTIFIER IS FREE TOO
      --------------------------------------------------------------------

      -- The bound B ∈ᴱ chk α is a quantifier bounded by a CHECK NAME, so
      -- copy-members reduces it to a ground member of α at ⟨ positiveᴾ ⟩
      -- alone. That is architecture 2.6's reduction, and it applies here for
      -- the same reason: the outer quantifier of extension regularity is
      -- unbounded and the inner one is not.

      inj-cong : (A B : Nm) (b : S) → ⟨ fst B ≈[G] fst (chk b) ⟩
               → ⟨ Vᴱ.injectable A B ⟩ → ⟨ Vᴱ.injectable A (chk b) ⟩
      inj-cong A B b e h =
        subst ⟨_⟩
          (sym (Vᴱ.Injectable-bridge A B)
           ∙ sat-cong Vᴱ.Injectableφ (A ∷ B ∷ []) (A ∷ chk b ∷ []) agr
           ∙ Vᴱ.Injectable-bridge A (chk b))
          h
        where
        agr : Agree (A ∷ B ∷ []) (A ∷ chk b ∷ [])
        agr zero       = ≈[G]-refl (fst A)
        agr (suc zero) = e

      bounded→goal : ⟨ positiveᴾ ⟩ → NoShortCofinal → OpenGoal
      bounded→goal pos ns α hα A hA B hB hinj =
        PT.rec Empty.isProp⊥
          (λ w → ns α hα A hA (fst w) (fst (snd w))
                   (inj-cong A B (fst w) (snd (snd w)) hinj))
          (copy-members pos α B hB)

      cover→theorem : ⟨ positiveᴾ ⟩ → GroundCover → RegularPreserved
      cover→theorem pos gc =
        goal→theorem (bounded→goal pos (cover→bounded gc))

      --------------------------------------------------------------------
      -- WHAT IS NOT CLAIMED, AT THE END OF THE FILE WHERE A READER STOPS
      --------------------------------------------------------------------

      -- No inhabitant of GroundCover, NoShortCofinal, OpenGoal or
      -- RegularPreserved appears above, and none is derivable from the
      -- telescope: every arrow points INTO them. The owner of GroundCover is
      -- K12a for the fullness half of Bell's route, which this track has just
      -- measured UNNECESSARY, and Track E plus a new countability row for the
      -- possible-value half, which is the route that is actually live.
      --
      -- Cofinality preservation is re-owned. What K7 Track H delivers is the
      -- vocabulary, the range predicate, the proved reduction to one named
      -- type, and the measurement that the Maximum Principle is not the price.
