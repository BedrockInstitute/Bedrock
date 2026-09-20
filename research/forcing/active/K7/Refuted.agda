{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 TRACK J. THE REFUTATIONS, THE DEGENERATE AUDIT, AND THE PACKAGE'S
-- CONTROLS.
--
-- Rule 14 is this track's whole mandate: transcribe the false statement, show
-- it false with machine evidence, stop there. Nothing in this file is imported
-- by any other K7 file and nothing in it is meant to be. Every derivation
-- below that reaches a K7 conclusion reaches it for a BAD reason, and the bad
-- reason is the result.
--
-- WHAT THIS FILE REFUTES, IN ONE LIST, EACH WITH ITS MACHINE EVIDENCE BELOW.
--
--  R1. The architecture's Part 0d sentence that "GroundWellOrder stays opaque
--      ... so no consumer can look inside it and NO HOST FUNCTION CAN BE PASSED
--      WHERE IT IS EXPECTED" is FALSE at the two lines it cites,
--      K7/CompletionTransfer.agda:634 and :667. At both of them GroundWellOrder
--      is an argument of the DECLARATION, universally quantified, so the caller
--      chooses the type. Part 4 passes a bare host choice function there.
--  R2. The same two lines make M's choice ELIMINABLE, by refl: the triple
--      (GroundWellOrder, wo, supply) is exactly SelTotal and nothing more.
--  R3. ChoicelessTransfer (K7/CompletionTransfer.agda:699-702), transcribed as
--      "the statement K7 refuses", is inhabited two ways here: once with no
--      hypothesis at all at the empty presentation, and once FROM MODULE WELL,
--      that is from M's own well ordering. It is therefore not a refusal and
--      it separates nothing.
--  R4. The flat Structural telescope (K7/CompletionTransfer.agda:251-278) drops
--      the coded Presentation record's `inhabited` field
--      (CodedCompletion.agda:207). The whole transfer therefore instantiates at
--      the EMPTY presentation, where every lemma is vacuous and the conclusion
--      is free.
--  R5. OrderGraphFor (K7/CompletionTransfer.agda:222-228), shipped as the name
--      of the missing object O6-for-B⁺, is inhabited at the empty set in three
--      lines. The type names nothing that the empty set does not already have.
--  R6. The unwitnessed-hypothesis census, and it is sharper than the
--      architecture's own. NOTHING in the compile root produces an
--      ⟨ injectable _ _ ⟩: all five declarations that mention one in a
--      conclusion take one as a hypothesis. So no chain condition in this
--      package is provable at ANY presentation, the one-point one and the
--      empty one included, and Track F's header sentence that CCC₂ "is
--      trivially true" at the one-point notion is refuted in PART 3.
--  R7. Two measured corrections to landed files, neither of them
--      mathematical. K7/CompletionTransfer.agda:499 records the
--      [ConstructorDoesNotFitInData] rejection "at exit 1"; re-run this
--      session it is EXIT 42, log at K7/breaks/PredicateField.log. And the
--      architecture's displayed antichainΔ at 2.1 is not definitionally Track
--      A's landed one, refl refused, log at K7/breaks/ArchAntichainRefl.log.
--
-- THE PROTECTION THAT SURVIVES, STATED SO IT IS NOT LOST WITH THE REST.
-- The SIBLING ARRANGEMENT does survive every attack in this file: module Well
-- (K7/CompletionTransfer.agda:100) and module Structural (:251) are top-level
-- siblings, so `ltOf` is out of scope in the transfer's mathematics and no
-- edit can falsify that without moving a module. Track J relies on the sibling
-- arrangement and on NOTHING ELSE, and reports that the second named
-- protection, opacity, is not a protection at all.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.Refuted
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Sum using ( _⊎_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import CodedVocabulary
import CardinalBridge
import K7.CardinalOrder
import K7.ChainConditions
import K7.CompletionTransfer

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module CV = CodedVocabulary 𝒮
module CB = CardinalBridge 𝒮
module CO = K7.CardinalOrder 𝒮
module CC = K7.ChainConditions 𝒮 ext paths
module CT = K7.CompletionTransfer 𝒮 ext paths

open OP using ( iff; Separation; Collection; Pairing )
open OP.PathRealization paths using ( path-to-≈ˢ; ≈ˢ-to-path; subst-member )

-- Track B, applied. Its module Order asks for Extensionality and the two
-- membership congruences (K7/CardinalOrder.agda:252-256); both congruences are
-- the realization contract, so this is the cheapest legitimate application and
-- not a widening. It is applied rather than transcribed because PART 1b's
-- census is a claim about Track B's landed file and a transcription would not
-- test it.

module OrdB = CO.Order ext subst-member
                (λ x y z h → cong (x ∈ˢ_) (≈ˢ-to-path y z h))
open CV using ( subsetΔ; refinesΔ; compatibleΔ; isKPairΔ; denseΔ; predenseΔ )
open CB using ( injectable )
open CC using ( antichainΔ; antichain-use; antichain-intro
              ; maximalΔ; maximal-intro; countableΔ
              ; CCC₁ᴵ; CCC₂ᴵ; CCC₃ᴵ; ccc-use; ccc-intro
              ; injectable-mono-dom
              ; MaximalExtension; MaximalExtensionIn )

--------------------------------------------------------------------------------
-- PART 0. THE DEVICE THIS TRACK MEASURES WITH
--------------------------------------------------------------------------------

-- A hypothesis is LOAD BEARING at an instance when the conclusion is not
-- available without it. The negation is what a degenerate audit measures, and
-- it is a type rather than a grep, so a later edit cannot falsify it silently:
-- to say "H is not load bearing in f : H → C" is to exhibit an inhabitant of C.
--
-- This is the mechanical form of the check Track F needs against a
-- Cohen-specific proof dressed as general (roadmap:214, T3). The recipe is
-- printed in PART 6 and the two instantiations this track can already run are
-- at :deg-hypotheses-not-load-bearing and :choice-slot-eliminable.

NotLoadBearing : (H C : Type ℓ) → (H → C) → Type ℓ
NotLoadBearing H C _ = C

--------------------------------------------------------------------------------
-- PART 1. THE ARCHITECTURE'S PRINTED ANTICHAIN IS NOT TRACK A's
--------------------------------------------------------------------------------

-- A small correction, found by transcribing architecture 2.1 literally before
-- Track A landed and then comparing. The architecture displays
--
--   antichainΔ c o d = ⋀ S (λ p → ⋀ S (λ q →
--     (((p ∈ˢ c) ⊓ (p ∈ˢ d)) ⊓ (((q ∈ˢ c) ⊓ (q ∈ˢ d)) ⊓ compatibleΔ c o p q))
--     ⇒ (p ≈ˢ q)))
--
-- and Track A landed the CURRIED form (K7/ChainConditions.agda:125-130), whose
-- reading theorem is refl against the object-language formula and whose
-- consumer interface is the pair antichain-use / antichain-intro. The two are
-- logically equivalent and are NOT definitionally equal, so a later track that
-- transcribes the architecture's display and expects refl against Track A will
-- not get it. The equivalence is proved here once so nobody else has to.
--
-- This file consumes Track A's LANDED predicate everywhere below. The audit is
-- worthless against a stand-in: a predicate chosen to make the degeneracy work
-- would prove nothing about the package.

antichainΔ-arch : S → S → S → Ω
antichainΔ-arch c o d =
  ⋀ S (λ p → ⋀ S (λ q →
    (((p ∈ˢ c) ⊓ (p ∈ˢ d)) ⊓ (((q ∈ˢ c) ⊓ (q ∈ˢ d)) ⊓ compatibleΔ c o p q))
    ⇒ (p ≈ˢ q)))

arch-is-tracka : (c o d : S) → antichainΔ-arch c o d ≡ antichainΔ c o d
arch-is-tracka c o d = ⇔toPath
  (λ h → antichain-intro c o d
           (λ p q hpc hpd hqc hqd cm → h p q ((hpc , hpd) , ((hqc , hqd) , cm))))
  (λ h p q hyp → antichain-use c o d p q h
                   (hyp .fst .fst) (hyp .fst .snd)
                   (hyp .snd .fst .fst) (hyp .snd .fst .snd) (hyp .snd .snd))

--------------------------------------------------------------------------------
-- PART 1b. THE CENSUS NOBODY ELSE CAN RUN, AND IT IS THIS TRACK'S HEADLINE
--------------------------------------------------------------------------------

-- RE-MEASURED AT THE END OF THIS SESSION, and the first measurement was
-- SUPERSEDED BY A LANDING. Rule 14 applies to this track as much as to any
-- other: Track B's file grew while this audit was being written and the census
-- below is the one that holds against the file on disk now.
--
-- injectable x y is ⋁ S (λ f → isInjection f x y) (CardinalBridge.agda:382-383),
-- a truncated join over a ground CODE, so producing one means exhibiting an
-- injection's graph as a set of the model. Every declaration in the compile
-- root whose conclusion is an ⟨ injectable _ _ ⟩:
--
--   PRODUCERS, that is no ⟨ injectable _ _ ⟩ among their hypotheses, TWO:
--     K7/CardinalOrder.agda:886-887  injectable-incl, Separation + Collection
--                                    + Pairing, and it produces injectable a b
--                                    only for a ⊆ b
--     K7/CardinalOrder.agda:950-951  injectable-refl, injectable-incl at a = a
--   NON-PRODUCERS, each taking an injectable, SIX:
--     K7/ChainConditions.agda:280    injectable-mono-dom
--     K7/CardinalOrder.agda:299      injectable-mono-dom
--     K7/CardinalOrder.agda:308      injectable-mono-cod
--     K7/CardinalOrder.agda:315      injectable-cong
--     K7/CardinalOrder.agda:322      injectable-cong-cod
--     K7/CardinalOrder.agda:1046     injectable-trans
--
-- THE STANDING CONSEQUENCE, WHICH THE LANDING SHARPENED RATHER THAN REMOVED.
-- Every injectable this programme can produce comes from an INCLUSION. So
-- ⟨ injectable d w ⟩ is available exactly where ⟨ subsetΔ d w ⟩ is, and
-- CardinalBridge's isSubset (:72-73) and CodedVocabulary's subsetΔ (:202-203)
-- are the same term, so that is not a gap between two vocabularies either.
-- A chain condition therefore holds, today, exactly at a presentation whose
-- antichains are all subsets of the ground ω code, and at no other.
--
--   AT THE EMPTY PRESENTATION that condition is met vacuously, so CCC₂ is
--   PROVED here, unconditionally, from three ground axioms: PART 2's
--   ccc₂-at-empty. That closes the degenerate audit completely. Every
--   hypothesis of the package's headline transfer, the chain condition
--   included, is discharged at an instance with no conditions in it.
--
--   AT THE ONE-POINT PRESENTATION it is not met, and this refutes the sentence
--   in Track F's header that reads "the one-point notion, at which every
--   antichain is a subset of a singleton and CCC₂ IS TRIVIALLY TRUE". PART 3
--   proves that at one point every SET is an antichain, so CCC₂ there is
--   exactly "every subset of the carrier injects into w", and the only
--   producer in the programme would need the carrier itself to be a subset of
--   w. Nothing supplies that and nothing makes it true. The theorem is still
--   correctly conditional; the ledger row must not say the hypothesis is
--   trivially available, because at the one presentation this programme has,
--   it is not available at all.
--
-- AND THE ARCHITECTURE'S OWN FINDING, WHICH IS UNTOUCHED. Architecture 6.3(2)
-- says no coded presentation makes a chain condition NON-TRIVIALLY true. The
-- census above says why the trivial cases are trivial and names the exact datum
-- that is missing in the non-trivial ones, which is an injection code and not
-- an atomless notion.

--------------------------------------------------------------------------------
-- PART 2. THE DEGENERATE AUDIT AT THE EMPTY PRESENTATION
--------------------------------------------------------------------------------

-- R4. K7/CompletionTransfer.agda:251-254 takes carrier and order flat, as two
-- elements of S. The coded record they come from has FOUR fields
-- (CodedCompletion.agda:201-208) and the two that were dropped are
-- order-typed and INHABITED. Dropping order-typed costs nothing here.
-- Dropping `inhabited` costs the whole audit: K5 records in its own words that
-- "an empty coded set is not dense, because the carrier is inhabited; so a
-- density hypothesis is never vacuous and never free. The antichain condition
-- at the same empty set holds" (K5/Dense.agda:520-523). With `inhabited`
-- dropped, the carrier itself may be empty and the antichain side is all that
-- is left.
--
-- Everything in this module is instantiated at ONE ground set with no members.
-- No axiom of the profile is spent. nul is a parameter rather than a
-- construction because the audit does not need it to be THE empty set: any
-- memberless ground code does.

module AtEmptyPresentation
  (nul : S)
  (nul-empty : (x : S) → ⟨ x ∈ˢ nul ⟩ → ⟨ ⊥ ⟩)
  where

  -- Two consequences of emptiness, used repeatedly below.

  sub-nul : (d x : S) → ⟨ subsetΔ d nul ⟩ → ⟨ x ∈ˢ d ⟩ → ⟨ ⊥ ⟩
  sub-nul d x ds hx = nul-empty x (ds x hx)

  refines-nul : (u v : S) → ⟨ refinesΔ nul u v ⟩ → ⟨ ⊥ ⟩
  refines-nul u v h =
    PT.rec (snd ⊥) (λ { (z , hz , _) → nul-empty z hz }) h

  ------------------------------------------------------------------------------
  -- 2.1 THE EMPTY SET IS AN ANTICHAIN OF EVERY PRESENTATION, AND IS DENSE IN
  --     NONE. This is Track A's named control AntichainAtEmpty, run here
  --     because Track A has not landed, and it is K5's own sentence made into
  --     a pair of theorems.
  ------------------------------------------------------------------------------

  antichain-at-empty : (c o : S) → ⟨ antichainΔ c o nul ⟩
  antichain-at-empty c o =
    antichain-intro c o nul
      (λ p q _ hpd _ _ _ → Empty.rec* (nul-empty p hpd))

  -- And the asymmetry, which is why CCC₃ is the variant a consumer should
  -- prefer: at the same empty set density FAILS, provided the carrier is
  -- inhabited, which is exactly the dropped field.

  empty-not-dense : (c o : S) → ⟨ ⋁ S (λ p → p ∈ˢ c) ⟩
                  → ⟨ denseΔ c o nul ⟩ → ⟨ ⊥ ⟩
  empty-not-dense c o inh dn =
    PT.rec (snd ⊥)
      (λ { (q , hq) →
           PT.rec (snd ⊥) (λ { (p , hpd , _) → nul-empty p hpd }) (dn q hq) })
      inh

  ------------------------------------------------------------------------------
  -- 2.2 R5. OrderGraphFor, THE NAME OF THE MISSING OBJECT, IS INHABITED
  ------------------------------------------------------------------------------

  -- K7/CompletionTransfer.agda:222-228 ships OrderGraphFor as the type whose
  -- non-inhabitation at B⁺set is obstruction O6-for-B⁺. At the empty set both
  -- conjuncts are vacuous, so the empty set has a coded order graph, and the
  -- type on its own names no obstruction: what is missing is
  -- OrderGraphFor B⁺set and not OrderGraphFor. A ledger row that says "the
  -- type is shipped and uninhabited" therefore reports on the tree and not on
  -- the mathematics.

  order-graph-at-empty : CT.OrderGraphFor nul
  order-graph-at-empty =
    nul
    , (λ z hz → Empty.rec* (nul-empty z hz))
    , (λ u v hu _ → Empty.rec* (nul-empty u hu))

  ------------------------------------------------------------------------------
  -- 2.2b THE THREE OBLIGATIONS THE PACKAGE CALLS OPEN ARE FREE AT THE EMPTY
  --      PRESENTATION, AND THE ONE IT CALLS TRIVIAL IS NOT
  ------------------------------------------------------------------------------

  -- MaximalExtension and MaximalExtensionIn (K7/ChainConditions.agda:445-452)
  -- carry the package's two "class (ii), no supplier in this tree" rows, and
  -- architecture 6.1 predicts a STOP on deriving the first from M's choice.
  -- Both are inhabited here with no axiom, no well ordering and no recursion.
  -- That does not make the rows wrong; it makes them rows about the TREE. The
  -- types on their own carry no obstruction, so a ledger entry of the form
  -- "shipped as a type and not inhabited" measures what nobody wrote.
  --
  -- Track C's MaximalExtensionIn-refuted (K7/CCCEquivalence.agda:514) is the
  -- stronger statement and is untouched by this: it exhibits a CONFIGURATION at
  -- which MaximalExtensionIn is false, which is rule 15 class (iii). The two
  -- results together say the type is inhabited at some presentations and
  -- refuted at others, which is exactly what "class (ii)" should mean and is
  -- not what "no supplier in this tree" says.

  maximal-at-empty : (o : S) → ⟨ maximalΔ nul o nul ⟩
  maximal-at-empty o =
    maximal-intro nul o nul (antichain-at-empty nul o)
      (λ q hq → Empty.rec* (nul-empty q hq))

  maximal-extension-at-empty : (o : S) → MaximalExtension nul o
  maximal-extension-at-empty o d ds ac =
    ∣ nul , (ds , (λ x h → h)) , maximal-at-empty o ∣₁

  maximal-extension-in-at-empty : (o : S) → MaximalExtensionIn nul o
  maximal-extension-in-at-empty o b bs bpd =
    ∣ nul
    , ((λ x h → Empty.rec* (nul-empty x h)) , antichain-at-empty nul o)
    , (λ q hq → Empty.rec* (nul-empty q hq)) ∣₁

  -- AND THE ONE THAT IS NOT FREE. At the empty presentation CCC₂ is EQUIVALENT
  -- to one instance of injectable, both directions below, so the whole content
  -- of the chain condition at the most degenerate presentation imaginable is
  -- the single datum PART 1b measured to have no producer anywhere. A reader
  -- who expected a degenerate instance to make the chain condition free should
  -- read these two lines instead: it does not, and the reason is that
  -- countability is about w and never about the notion.

  ccc₂-at-empty-needs : (o w : S) → ⟨ injectable nul w ⟩ → ⟨ CCC₂ᴵ nul o w ⟩
  ccc₂-at-empty-needs o w h =
    ccc-intro nul o w (λ d ds _ → injectable-mono-dom d nul w ds h)

  -- And the residue is supplied, so the chain condition at the empty
  -- presentation is a THEOREM and not a hypothesis. The inclusion is vacuous,
  -- the three axioms are the ones injectable-incl asks for at
  -- K7/CardinalOrder.agda:886-887, and nothing else is spent. This is the
  -- last slot of the degenerate audit and it closes it.

  injectable-nul : Separation → Collection → Pairing → (w : S)
                 → ⟨ injectable nul w ⟩
  injectable-nul sep coll pair w =
    OrdB.injectable-incl sep coll pair nul w
      (λ x hx → Empty.rec* (nul-empty x hx))

  ccc₂-at-empty : Separation → Collection → Pairing
                → (o w : S) → ⟨ CCC₂ᴵ nul o w ⟩
  ccc₂-at-empty sep coll pair o w =
    ccc₂-at-empty-needs o w (injectable-nul sep coll pair w)

  ccc₂-at-empty-gives : (o w : S) → ⟨ CCC₂ᴵ nul o w ⟩ → ⟨ injectable nul w ⟩
  ccc₂-at-empty-gives o w h =
    ccc-use nul o w nul h (λ x hx → hx) (antichain-at-empty nul o)

  ------------------------------------------------------------------------------
  -- 2.3 THE WHOLE TRANSFER, INSTANTIATED AT THE EMPTY PRESENTATION
  ------------------------------------------------------------------------------

  -- Every set-valued parameter of module Structural is nul; the embedding is
  -- the identity; below is constantly nul. Every one of the eight proof
  -- parameters is then vacuous or trivial, and not one of them needed an
  -- axiom. antichainΔ is the REAL predicate of PART 1, so this is not a
  -- degenerate-predicate audit: it is a degenerate-INSTANCE audit, which is
  -- the stronger of the two.

  module St = CT.Structural
    nul nul nul nul
    (λ x → x)
    (λ p h → h)
    (λ r p hr _ _ → Empty.rec* (nul-empty r hr))
    (λ _ → nul)
    (λ b p h → h)
    (λ b p h → Empty.rec* (nul-empty p h))
    (λ u v z h _ → Empty.rec* (refines-nul u v h))
    antichainΔ antichain-use antichain-intro

  -- The selection relation is the empty relation. sel-below and sel-unique are
  -- vacuous at it, which is the first thing the audit measures: module
  -- WithSelection's three parameters do NOT force the selection to select
  -- anything. What forces that is SelTotal, one layer down, and SelTotal is a
  -- FIELD of the record rather than a parameter of the module.

  module WS = St.WithSelection (λ _ _ → ⊥) (λ u p h → Empty.rec* h)
                               (λ u p q h _ → Empty.rec* h)

  -- One host type at the level the transfer's presentation slot wants. It has
  -- one point and no mathematics, and it is enough.

  data OnePointHost : Type (ℓ-suc ℓ) where
    ⋆ : OnePointHost

  ⊤ᴴ : OnePointHost → Ω
  ⊤ᴴ _ = ⊤

  ⊤₃ : S → S → S → Ω
  ⊤₃ _ _ _ = ⊤

  ⊤₂ : S → S → Ω
  ⊤₂ _ _ = ⊤

  module T = WS.Transfer OnePointHost ⋆ ⋆ ⊤ᴴ ⊤ᴴ ⊤₃ ⊤₂ nul
               (λ c o v d _ _ _ → tt*) (λ c o v _ → tt*) refl refl

  -- THE SIX FIELDS OF CCCHypotheses, ALL SIX DISCHARGED WITH NO AXIOM, NO
  -- CHOICE, NO DEFINABILITY DATUM AND NO COUNTING. Compare K6's degenerate G,
  -- which failed to discriminate six fields out of the architecture's claimed
  -- four; here the count is six out of six.

  deg-hypotheses : T.CCCHypotheses
  deg-hypotheses = record
    { sel-total       = λ u hu → Empty.rec* (nul-empty u hu)
    ; selImage        = λ d _ → nul
    ; selImage-sub    = λ d ds y h → h
    ; selImage-in     = λ d ds u y _ h → Empty.rec* h
    ; selImage-out    = λ d ds y h → Empty.rec* (nul-empty y h)
    ; pull-injectable = λ d e _ _ _ → tt* }

  deg-transfer : ⟨ ⊤ ⟩ → ⟨ ⊤ ⟩
  deg-transfer = T.transfer-runs deg-hypotheses

  -- And the measurement that names what just happened. The conclusion of
  -- transfer-runs at this instance is available WITHOUT the record, so at this
  -- instance CCCHypotheses is not load bearing. Nothing here says the theorem
  -- is wrong; it says the theorem's TYPE cannot distinguish this instance from
  -- a genuine one, which is rule 15 at the level of a whole telescope rather
  -- than a field.

  deg-hypotheses-not-load-bearing :
    NotLoadBearing T.CCCHypotheses (⟨ ⊤ ⟩ → ⟨ ⊤ ⟩) T.transfer-runs
  deg-hypotheses-not-load-bearing _ = tt*

  ------------------------------------------------------------------------------
  -- 2.4 R3, FIRST HALF. ChoicelessTransfer IS INHABITED HERE, WITH NOTHING
  ------------------------------------------------------------------------------

  -- K7/CompletionTransfer.agda:699-702 transcribes ChoicelessTransfer under
  -- rule 14 as "the statement K7 refuses", and its own comment says it is
  -- "NOT inhabited anywhere in this tree". That sentence is true of the tree
  -- and false as a statement about the type. Here is an inhabitant, at an
  -- instance whose telescope is completely filled, using the identity function
  -- as the selector and no hypothesis whatever.
  --
  -- The reason is the one the refusal was supposed to exclude: the type asks
  -- for a host function S → S together with a membership fact only at members
  -- of d, and d is empty. Emptiness is not the only route; PART 4 gives the
  -- other one, at a completely arbitrary instance, from M's own choice.

  choiceless-at-empty : T.ChoicelessTransfer
  choiceless-at-empty d ds _ = (λ x → x) , (λ u hu → ds u hu)

--------------------------------------------------------------------------------
-- PART 3. THE ONE-POINT DEGENERACY, PARAMETRICALLY
--------------------------------------------------------------------------------

-- The one-point coded presentation (K6/OnePoint.agda:158) is the only
-- inhabitant of CodedCompletion.Presentation in the compile root, measured:
-- every other occurrence of the record name in a non-comment line is a
-- PARAMETER declaration (NameWeight.agda:139, :381, K4/InstanceCoded.agda:114,
-- K5/InstanceBase.agda:80, K5/InstanceValue.agda:65, K5/ProbeD1.agda:39,
-- K5/ProbeI1.agda:39 through K5/ProbeI6.agda:40), and Certificate.agda:992 is
-- the HOST record's B⁺, itself a function of an assumed host presentation.
--
-- This module does not apply K6.OnePoint. It takes the one fact that matters,
-- carrier-one-point (K6/OnePoint.agda:190-191), flat, and shows that it alone
-- discharges every antichain conclusion. So the discrimination failure is not
-- a property of that file: it is a property of any notion with one condition,
-- and applying the file would measure nothing the two lines below do not.

module AtOnePoint
  (c o p₀ : S)
  (c-only : (x : S) → ⟨ x ∈ˢ c ⟩ → x ≡ p₀)
  where

  -- EVERY ground set is an antichain of a one-point notion, because the
  -- conclusion is discharged without inspecting the hypothesis. All three
  -- chain conditions are therefore whatever countability says about arbitrary
  -- subsets of a one-element carrier, and none of them constrains the notion.

  every-set-is-an-antichain : (d : S) → ⟨ antichainΔ c o d ⟩
  every-set-is-an-antichain d =
    antichain-intro c o d
      (λ p q hp _ hq _ _ → path-to-≈ˢ p q (c-only p hp ∙ sym (c-only q hq)))

  -- The same two lines with the compatibility hypothesis deleted, which is the
  -- honest statement of what the one-point instance measures: nothing.

  antichain-ignores-compatibility :
      (d p q : S) → ⟨ p ∈ˢ c ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ p ≈ˢ q ⟩
  antichain-ignores-compatibility d p q hp hq =
    path-to-≈ˢ p q (c-only p hp ∙ sym (c-only q hq))

  -- AND THE REFUTATION OF THE SENTENCE IN TRACK F's HEADER. CCC₂ at a
  -- one-point notion is not trivially true. It is EQUIVALENT to "every subset
  -- of the carrier injects into w", both directions below, and the antichain
  -- hypothesis is discarded in the forward direction: the underscore is the
  -- machine evidence that the chain condition reads nothing about the notion
  -- there. PART 1b measured that the programme's only producers of an
  -- injectable are injectable-incl and injectable-refl
  -- (K7/CardinalOrder.agda:886-887, :950-951), both of which need the domain
  -- to be a SUBSET of the codomain. The right-hand side below therefore needs
  -- the one-point carrier to be a subset of w, which nothing supplies and
  -- nothing makes true, so CCC₂ is neither trivially true nor provable at the
  -- only presentation this programme has. Contrast ccc₂-at-empty in PART 2,
  -- where the same inclusion IS vacuously available and the chain condition is
  -- a theorem: the difference between the two instances is the whole content
  -- of the chain condition in this package today.

  ccc₂-at-one-point-needs :
      (w : S) → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ injectable d w ⟩)
    → ⟨ CCC₂ᴵ c o w ⟩
  ccc₂-at-one-point-needs w h = ccc-intro c o w (λ d ds _ → h d ds)

  ccc₂-at-one-point-gives :
      (w : S) → ⟨ CCC₂ᴵ c o w ⟩
    → (d : S) → ⟨ subsetΔ d c ⟩ → ⟨ injectable d w ⟩
  ccc₂-at-one-point-gives w h d ds =
    ccc-use c o w d h ds (every-set-is-an-antichain d)

  -- The same for CCC₁ and CCC₃, which at one point are not the same predicate
  -- as CCC₂ and are not free either. maximalΔ is antichainΔ ⊓ predenseΔ
  -- (K7/ChainConditions.agda:244-245), so at one point maximality IS
  -- predensity, and CCC₁ quantifies over the predense subsets alone. Stating
  -- that reduction is the whole of what the one-point instance measures about
  -- the three conditions, and it measures nothing about the notion.

  maximal-is-predense-at-one-point :
      (d : S) → ⟨ predenseΔ c o d ⟩ → ⟨ maximalΔ c o d ⟩
  maximal-is-predense-at-one-point d pd =
    maximal-intro c o d (every-set-is-an-antichain d) pd

--------------------------------------------------------------------------------
-- PART 4. R1, R2 AND R3's SECOND HALF. THE CHOICE SLOT
--------------------------------------------------------------------------------

-- Everything in this part runs at a COMPLETELY ARBITRARY instance of module
-- Structural. Nothing is degenerate, nothing is empty, and the conclusions are
-- about the general declarations at K7/CompletionTransfer.agda:634 and :667.

module Audit
  (carrier order  : S)
  (B⁺set  order⁺  : S)
  (img       : S → S)
  (img-in    : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ img p ∈ˢ B⁺set ⟩)
  (img-mono  : (r p : S) → ⟨ r ∈ˢ carrier ⟩ → ⟨ p ∈ˢ carrier ⟩
             → ⟨ refinesΔ order r p ⟩ → ⟨ refinesΔ order⁺ (img r) (img p) ⟩)
  (below         : S → S)
  (below-sub     : (b p : S) → ⟨ p ∈ˢ below b ⟩ → ⟨ p ∈ˢ carrier ⟩)
  (below-refines : (b p : S) → ⟨ p ∈ˢ below b ⟩ → ⟨ refinesΔ order⁺ (img p) b ⟩)
  (refines⁺-trans : (u v z : S) → ⟨ refinesΔ order⁺ u v ⟩
                  → ⟨ refinesΔ order⁺ v z ⟩ → ⟨ refinesΔ order⁺ u z ⟩)
  where

  module St = CT.Structural carrier order B⁺set order⁺ img img-in img-mono
                below below-sub below-refines refines⁺-trans
                antichainΔ antichain-use antichain-intro

  ------------------------------------------------------------------------------
  -- 4.1 AT AN ARBITRARY SELECTION: THE HOST FUNCTION IN THE CHOICE SLOT
  ------------------------------------------------------------------------------

  module AtSelection
    (selRel     : S → S → Ω)
    (sel-below  : (u p : S) → ⟨ selRel u p ⟩ → ⟨ p ∈ˢ below u ⟩)
    (sel-unique : (u p q : S) → ⟨ selRel u p ⟩ → ⟨ selRel u q ⟩ → p ≡ q)
    where

    module WS = St.WithSelection selRel sel-below sel-unique

    module AtTransfer
      (HostPresentation : Type (ℓ-suc ℓ))
      (𝔓ᴴ B⁺ : HostPresentation)
      (Φ Ψ   : HostPresentation → Ω)
      (CCC₂ᴵ      : S → S → S → Ω)
      (injectable : S → S → Ω)
      (w : S)
      (ccc-use   : (c o v d : S) → ⟨ CCC₂ᴵ c o v ⟩ → ⟨ subsetΔ d c ⟩
                 → ⟨ antichainΔ c o d ⟩ → ⟨ injectable d v ⟩)
      (ccc-intro : (c o v : S)
                 → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
                    → ⟨ injectable d v ⟩)
                 → ⟨ CCC₂ᴵ c o v ⟩)
      (Φ-reading : Φ 𝔓ᴴ ≡ CCC₂ᴵ carrier order  w)
      (Ψ-reading : Ψ B⁺  ≡ CCC₂ᴵ B⁺set  order⁺ w)
      where

      module T = WS.Transfer HostPresentation 𝔓ᴴ B⁺ Φ Ψ CCC₂ᴵ injectable w
                   ccc-use ccc-intro Φ-reading Ψ-reading

      -- The five slots of hyp-from-ground that are not the choice slot,
      -- collected once so the two theorems below differ in nothing else.

      Rest : Type ℓ
      Rest =
        Σ[ im ∈ ((d : S) → ⟨ subsetΔ d B⁺set ⟩ → S) ]
          ( ((d : S) (ds : ⟨ subsetΔ d B⁺set ⟩)
             → ⟨ subsetΔ (im d ds) carrier ⟩)
          × ( ((d : S) (ds : ⟨ subsetΔ d B⁺set ⟩) (u y : S)
               → ⟨ u ∈ˢ d ⟩ → ⟨ selRel u y ⟩ → ⟨ y ∈ˢ im d ds ⟩)
            × ( ((d : S) (ds : ⟨ subsetΔ d B⁺set ⟩) (y : S)
                 → ⟨ y ∈ˢ im d ds ⟩
                 → ⟨ ⋁ S (λ u → (u ∈ˢ d) ⊓ selRel u y) ⟩)
              × ((d e : S)
                 → ((u : S) → ⟨ u ∈ˢ d ⟩
                    → ⟨ ⋁ S (λ p → (p ∈ˢ e) ⊓ selRel u p) ⟩)
                 → ((u v p : S) → ⟨ u ∈ˢ d ⟩ → ⟨ v ∈ˢ d ⟩
                    → ⟨ selRel u p ⟩ → ⟨ selRel v p ⟩ → u ≡ v)
                 → ⟨ injectable e w ⟩ → ⟨ injectable d w ⟩) ) ) )

      from-ground : (GWO : Type (ℓ-suc ℓ)) → GWO → (GWO → T.SelTotal)
                  → Rest → T.CCCHypotheses
      from-ground GWO wo supply (im , im-sub , im-in , im-out , pull) =
        T.hyp-from-ground GWO wo supply im im-sub im-in im-out pull

      --------------------------------------------------------------------------
      -- R1. A BARE HOST CHOICE FUNCTION, IN THE SLOT THE LEDGER CALLS M's
      --     CHOICE. THIS TYPECHECKS.
      --------------------------------------------------------------------------

      -- The architecture's Part 0d says of K7/CompletionTransfer.agda:634 and
      -- :667 that GroundWellOrder "reaches the assembly only as an opaque
      -- Type (ℓ-suc ℓ) ... so no consumer can look inside it and NO HOST
      -- FUNCTION CAN BE PASSED WHERE IT IS EXPECTED". The second clause is
      -- false and this data type is the counterexample. It is a host function
      -- S → S, chosen outside the model, total on the whole of S, with its
      -- graph condition and NOTHING ELSE: no trichotomy, no least-element
      -- principle, no uniqueness, no internal definability. It is declared at
      -- Type (ℓ-suc ℓ) only because that is the level the slot asks for, and
      -- a data declaration may sit above its constructors.
      --
      -- Track D's own break K7/breaks/HostSelector.agda-break showed a host
      -- pick filling module WithSelection's three parameters. This is one
      -- layer further in and one layer worse: the host function is in the slot
      -- whose OPACITY was named as the protection.

      data HostChoiceFunction : Type (ℓ-suc ℓ) where
        hostPick : (f : S → S)
                 → ((u : S) → ⟨ u ∈ˢ B⁺set ⟩ → ⟨ selRel u (f u) ⟩)
                 → HostChoiceFunction

      host-supply : HostChoiceFunction → T.SelTotal
      host-supply (hostPick f hf) u hu = ∣ f u , hf u hu ∣₁

      host-fills-the-choice-slot : HostChoiceFunction → Rest → T.CCCHypotheses
      host-fills-the-choice-slot h =
        from-ground HostChoiceFunction h host-supply

      --------------------------------------------------------------------------
      -- R2. AND THE SLOT IS ELIMINABLE, BY refl
      --------------------------------------------------------------------------

      -- Stronger than R1 and cheaper. GroundWellOrder, its inhabitant and the
      -- supply function are three arguments of the DECLARATION, so the caller
      -- instantiates all three; their joint content is exactly one SelTotal.
      -- The witness type below has one point and no structure at all.

      data NoChoiceAtAll : Type (ℓ-suc ℓ) where
        ⋆ : NoChoiceAtAll

      without-choice : T.SelTotal → Rest → T.CCCHypotheses
      without-choice st = from-ground NoChoiceAtAll ⋆ (λ _ → st)

      choice-slot-eliminable :
          (GWO : Type (ℓ-suc ℓ)) (wo : GWO) (supply : GWO → T.SelTotal)
          (rest : Rest)
        → from-ground GWO wo supply rest ≡ without-choice (supply wo) rest
      choice-slot-eliminable GWO wo supply rest = refl

      -- What survives, and it is the whole of what survives. The sibling
      -- arrangement is untouched by everything above: ltOf is not in scope in
      -- this module, module St's two lemmas were proved without it, and no
      -- edit to a type can put it back. Track J relies on the sibling
      -- arrangement and reports the opacity clause refuted.

    ------------------------------------------------------------------------------
    -- 4.2 R3, SECOND HALF. THE REFUSED STATEMENT FOLLOWS FROM M's OWN CHOICE
    ------------------------------------------------------------------------------

  module AtMChoice
    (GroundWellOrder : Type (ℓ-suc ℓ))
    (ltOf  : GroundWellOrder → S → S → Ω)
    (triOf : (wo : GroundWellOrder) (z z' : S)
           → ∥ ⟨ ltOf wo z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ ltOf wo z' z ⟩) ∥₁)
    (leastOf : (wo : GroundWellOrder) (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩
             → ⟨ ⋁ S (λ z → (z ∈ˢ d)
                   ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((ltOf wo z' z) ⇒ ⊥))) ⟩)
    (wo : GroundWellOrder)
    where

    module W = CT.Well GroundWellOrder ltOf triOf leastOf

    module WS = St.WithSelection
                  (W.selectAt wo below)
                  (W.select-in wo below)
                  (W.select-unique wo below)

    module AtTransfer
      (HostPresentation : Type (ℓ-suc ℓ))
      (𝔓ᴴ B⁺ : HostPresentation)
      (Φ Ψ   : HostPresentation → Ω)
      (CCC₂ᴵ      : S → S → S → Ω)
      (injectable : S → S → Ω)
      (w : S)
      (ccc-use   : (c o v d : S) → ⟨ CCC₂ᴵ c o v ⟩ → ⟨ subsetΔ d c ⟩
                 → ⟨ antichainΔ c o d ⟩ → ⟨ injectable d v ⟩)
      (ccc-intro : (c o v : S)
                 → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
                    → ⟨ injectable d v ⟩)
                 → ⟨ CCC₂ᴵ c o v ⟩)
      (Φ-reading : Φ 𝔓ᴴ ≡ CCC₂ᴵ carrier order  w)
      (Ψ-reading : Ψ B⁺  ≡ CCC₂ᴵ B⁺set  order⁺ w)
      where

      module T = WS.Transfer HostPresentation 𝔓ᴴ B⁺ Φ Ψ CCC₂ᴵ injectable w
                   ccc-use ccc-intro Φ-reading Ψ-reading

      -- THE REFUTATION. ChoicelessTransfer asks for a host function S → S
      -- landing in below u. Module Well's `pick` (K7/CompletionTransfer.agda:
      -- 151) IS a host function S → S once its inhabitation argument is
      -- supplied, because unique choice at a proved-unique witness produces a
      -- HOST term and not an internal one. So M's own well ordering, plus the
      -- hypothesis that below u is inhabited, inhabits the statement the file
      -- refuses, in two lines.
      --
      -- The density hypothesis is the same one the seam probe already takes at
      -- K7/TransferAtCertificate.agda:220-222, there restricted to B⁺set. The
      -- restriction is the only difference and it is not a choice principle:
      -- Bell's "P will be regarded as a dense subset of B" (fulltext:3486).
      --
      -- CONSEQUENCE, AND IT IS THE POINT. ChoicelessTransfer does not
      -- characterise a choiceless transfer. It is Track D's own transfer with
      -- the selection existentially packaged, and the packaging is what loses
      -- the information. Together with Track D's HostSelector break, which
      -- runs the implication the other way, the two show the boundary is
      -- porous in BOTH directions: a host selector fills the internal slot and
      -- the internal selector fills the host slot. Nothing at the level of
      -- types separates them, which is rule 15 stated as a biconditional.

      choiceless-from-M :
          ((u : S) → ⟨ ⋁ S (λ z → z ∈ˢ below u) ⟩) → T.ChoicelessTransfer
      choiceless-from-M dense d ds ac =
          (λ u → W.pick wo (below u) (dense u))
        , (λ u _ → W.pick-in wo (below u) (dense u))

--------------------------------------------------------------------------------
-- PART 5. RULE 14 TRANSCRIPTIONS. NOT CONSUMED BY ANY K7 FILE
--------------------------------------------------------------------------------

-- Device D-I of the exit checklist requires that every token whose count is
-- expected 0 in a delivered K7 file have a named non-zero partner, and names
-- THIS file as the partner. A census that is zero everywhere fails the item,
-- because it cannot distinguish a file that avoids a datum from a package that
-- forgot to look. Everything below is transcribed from the cited source, is
-- uninhabited here, and is imported by nothing.

module NonClaims
  (IsNm : S → Ω)
  (_≈[G]_ : S → S → Ω)
  (isOrdinalᴳ : S → Ω)
  where

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

  ------------------------------------------------------------------------------
  -- 5.1 RULE 15's CLASS (iii) WITNESS, AND WHY IT IS THE PROGRAMME'S SHARPEST
  ------------------------------------------------------------------------------

  -- Onto, K5/Structures.agda:532-533, character for character. K5's own
  -- comment four lines above says "ontoness of the check map on the nose is
  -- FALSE as soon as one non-check name exists", and a genuine Cohen extension
  -- has such names by construction. It is class (iii): an inhabitant exists
  -- only where the extension is the ground.

  Onto : (S → Nm) → Type ℓ
  Onto h = (σ : Nm) → ∥ Σ[ a ∈ S ] ⟨ fst σ ≈[G] fst (h a) ⟩ ∥₁

  -- NoNewOrdinals, K6/Ordinals.agda:186-189, with the extension's satisfaction
  -- of the ordinal formula abbreviated to a parameter, because composing the
  -- engine down to truth-at costs 102.95 s and 9.08 GB (architecture 1.7) and
  -- this file is not allowed to pay it.

  module WithOrdinalReading
    (chk : S → Nm)
    (ordinalᴱ : Nm → Ω)
    where

    NoNewOrdinals : Type ℓ
    NoNewOrdinals =
      (σ : Nm) → ⟨ ordinalᴱ σ ⟩
      → ⟨ ⋁ S (λ a → isOrdinalᴳ a ⊓ (fst σ ≈[G] fst (chk a))) ⟩

    -- THE TWO-LINE DERIVATION, at exit 0, and it is the reason Onto may never
    -- be taken as a hypothesis. The second argument is K6's proved downward
    -- half (K6/Ordinals.agda:193-196), which costs nothing; Onto supplies the
    -- rest. Nothing in this programme consumes the term below.

    onto→NoNewOrdinals :
        Onto chk
      → ((σ : Nm) (a : S) → ⟨ ordinalᴱ σ ⟩ → ⟨ fst σ ≈[G] fst (chk a) ⟩
         → ⟨ isOrdinalᴳ a ⟩)
      → NoNewOrdinals
    onto→NoNewOrdinals onto reflect σ hσ =
      PT.map (λ { (a , e) → a , reflect σ a hσ e , e }) (onto σ)

    -- OrdinalRankBound, K6/Ordinals.agda:227-232, the prerequisite K6 names
    -- for the honest route to the same statement. ZERO FILLERS in the compile
    -- root, re-measured for this file.

    OrdinalRankBound : (Child : S → S → Type ℓ) → Type ℓ
    OrdinalRankBound Child =
      Σ[ rk ∈ (Nm → S) ]
        ( ((τ : Nm) → ⟨ isOrdinalᴳ (rk τ) ⟩)
        × ((τ : Nm) (x : S) (hx : Child x (fst τ)) (hn : ⟨ IsNm x ⟩)
             → ⟨ rk (x , hn) ∈ˢ rk τ ⟩) )

  ------------------------------------------------------------------------------
  -- 5.2 K3's NameRankContract, LInstanceRank.agda:159-163
  ------------------------------------------------------------------------------

  -- Rule 9 says records are generative and K3 owns this one, so what follows
  -- is a TRANSCRIPTION under a different name and never a second declaration
  -- of the same record. Zero fillers, re-measured: rkᴺ occurs at :161, :162,
  -- :163 and in prose only.

  NameRankContract-shape : (Name : Type ℓ) (Index : Name → Type ℓ)
                         → ((τ : Name) → Index τ → Name) → Type ℓ
  NameRankContract-shape Name Index child =
    Σ[ rk ∈ (Name → S) ]
      ( ((τ : Name) → ⟨ isOrdinalᴳ (rk τ) ⟩)
      × ((τ : Name) (i : Index τ) → ⟨ rk (child τ i) ∈ˢ rk τ ⟩) )

--------------------------------------------------------------------------------
-- 5.3 K4's FULLNESS BANNER, K4/Witnesses.agda:842-908
--------------------------------------------------------------------------------

-- "NOTHING BELOW THIS LINE IS INHABITED IN K4", the file's own banner at :842.
-- k4-architecture.md:998 refuses K7 by name: "a K7 agent reading Bell will
-- find the Maximum Principle in its source proof and may request it from K4;
-- the answer is no." Track H's expected deliverable is a stop report and this
-- module is the non-zero partner its zero-expected census needs.

module K4NonClaims
  (Name : Type ℓ) (PtB : Type ℓ)
  (Lub : (Name → PtB) → PtB → Type ℓ)
  (Congruent : (Name → PtB) → Type ℓ)
  where

  Fullness : (Name → PtB) → PtB → Type ℓ
  Fullness v E = ∥ Σ[ τ ∈ Name ] (v τ ≡ E) ∥₁

  MaximumPrinciple : Type ℓ
  MaximumPrinciple =
    (v : Name → PtB) (E : PtB) → Lub v E → Congruent v → Fullness v E

  -- The two names the shape grep of exit item Y6 exists to catch, because a
  -- flat transcription defeats the token grep. Both are uninhabited here.

  mp→fullness : MaximumPrinciple
              → (v : Name → PtB) (E : PtB) → Lub v E → Congruent v
              → Fullness v E
  mp→fullness mp = mp

  module Mixing
    (CodedNameFamily : S → Type ℓ)
    (Mixture : {I : S} → CodedNameFamily I → Name → Type ℓ)
    where

    -- MixtureSupply, K4/Witnesses.agda:906-908. Zero fillers, measured.

    MixtureSupply : Type ℓ
    MixtureSupply = {I : S} (F : CodedNameFamily I)
                  → ∥ Σ[ mx ∈ Name ] Mixture F mx ∥₁

    -- Refinement, WitnessSpec, ValueCover and ElementPrinciple are named in
    -- the ledger's forbidden list and have no declaration in the compile root
    -- to transcribe, measured. They appear here as the names of types that
    -- are empty for that reason and for no other, so the D-I partner count is
    -- non-zero and honest about why.

    Refinement-unbuilt : Type ℓ
    Refinement-unbuilt = MixtureSupply → MaximumPrinciple → ⟨ ⊥ ⟩ → ⟨ ⊥ ⟩

    WitnessSpec-unbuilt : Type ℓ
    WitnessSpec-unbuilt = Refinement-unbuilt

    ValueCover-unbuilt : Type ℓ
    ValueCover-unbuilt = Refinement-unbuilt

    ElementPrinciple-unbuilt : Type ℓ
    ElementPrinciple-unbuilt = Refinement-unbuilt

--------------------------------------------------------------------------------
-- 5.4 O3b's SILENT ROUTE, NameKernel.agda:136-141 and StandardNames.agda:281-285
--------------------------------------------------------------------------------

-- Exit item Y4's zero-expected census over Track E names this file as its
-- non-zero partner. The hazard the census exists for is a shape identity and
-- not a token: imageOn-spec (StandardNames.agda:284-285) has the same return
-- type as the discharged O3a route, so a filler that ignores its graph, coll
-- and sep arguments typechecks and pulls tier-4 MemberImage in invisibly.
-- Both shapes are transcribed below so a reader can compare them side by side.
-- The one token the grep wants that CANNOT appear here is the qualified name
-- StandardNames dot Weighted, because a dot is not legal inside an identifier;
-- it is named in this comment and measured at zero in code, deliberately.

module O3bShapes where

  -- NameKernel.agda:136-141, tier 4, the record K3 owns. Transcribed, not
  -- re-declared (rule 9).

  MemberImage-shape : Type (ℓ-suc ℓ)
  MemberImage-shape =
    Σ[ image ∈ ((a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S) ]
      ((a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
       → (z ∈ˢ image a f)
         ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))))

  -- StandardNames.agda:281-285. Note that the return type mentions no image
  -- datum at all, which is exactly why a body that secretly uses one is
  -- invisible to every grep run at the declaration.

  imageOn-shape : Type (ℓ-suc ℓ)
  imageOn-shape =
    Σ[ imageOn ∈ (S → (S → S) → S) ]
      ((c : S) (f : S → S) (z : S)
       → (z ∈ˢ imageOn c f) ≡ ⋁ S (λ x → (x ∈ˢ c) ⊓ (z ≈ˢ f x)))

  -- member→image is the name the census keys on for the direction K3 proved
  -- (NameImage.agda:190-193). The point of writing it here is that the two
  -- return types above are the SAME SHAPE, so possessing one of them is no
  -- evidence about which route produced it.

  member→image-shape : Type (ℓ-suc ℓ)
  member→image-shape = imageOn-shape

  image-spec-shape : Type (ℓ-suc ℓ)
  image-spec-shape = MemberImage-shape

--------------------------------------------------------------------------------
-- PART 6. THE T3 CHECK, MECHANICALLY, AND WHAT IT MEASURES AT TRACK F
--------------------------------------------------------------------------------

-- roadmap:214 forbids a Cohen-specific proof dressed as general, and the
-- architecture's own proposal for catching one is to instantiate the general
-- theorem at a second notion and see which telescope slot cannot be filled.
-- That is sound and it is expensive. The cheap mechanical form is the
-- following three steps, and the two devices it needs are in this file.
--
--   STEP 1, DEGENERATE INSTANTIATION. Fill every set-valued slot of the
--   telescope with one memberless ground code and every proof slot with the
--   vacuous inhabitant. If the whole telescope fills, no slot of it forces the
--   notion to be non-degenerate, and the theorem's type cannot distinguish a
--   genuine forcing notion from nothing. AtEmptyPresentation runs this on
--   K7/CompletionTransfer.agda and the telescope fills completely, six of six
--   fields of CCCHypotheses included.
--
--   STEP 2, THE CONCLUSION TEST. Exhibit the conclusion at that instance
--   WITHOUT the hypothesis under test. NotLoadBearing is that statement as a
--   type, and deg-hypotheses-not-load-bearing is the instantiation: at the
--   empty presentation the transfer's conclusion is free.
--
--   STEP 3, THE RESIDUE TEST, AND IT IS THE ONE THAT SEPARATES A GENERAL
--   THEOREM FROM A SPECIALIZED ONE. Ask which slot does NOT fill at step 1.
--   That slot, and only that slot, carries the theorem's content. At
--   K7/CompletionTransfer.agda the answer is none; at Track A's chain
--   conditions the answer is exactly countableΔ, that is injectable, which
--   ccc₂-at-empty-needs and ccc₂-at-empty-gives exhibit as an equivalence.
--
-- WHAT THE THREE STEPS SAY ABOUT TRACK F, WITHOUT INSTANTIATING ITS TELESCOPE.
-- K7/NoCollapse.agda's module Preserve takes CCC₂ᴵ as an opaque S → S → S → Ω
-- with the single use law ccc-use, whose CONCLUSION is ⟨ injectable d w ⟩.
-- A degenerate CCC₂ᴵ, that is the constantly true predicate, therefore cannot
-- fill that telescope: ccc-use would have to produce an injectable out of
-- nothing, and PART 1b measured that nothing in the compile root does. So
-- Track F passes the T3 check, and it passes it for exactly the reason that
-- makes its hypothesis unwitnessed. One measured fact does both jobs, and a
-- ledger that reports only the first has reported half of it.
--
-- The cost of not instantiating: this file does not run step 1 on Track F's
-- telescope, whose seventeen slots include forces, truth-at and a valuesOf
-- specification over an abstract Cond. That is a named gap, not an omission,
-- and the reason is 1.7's measurement of what composing the engine costs.

--------------------------------------------------------------------------------
-- PART 7. WHAT TRACK J MEASURED AND DID NOT REFUTE
--------------------------------------------------------------------------------

-- Rule 14 cuts both ways and a refutation track that reports only hits is
-- reporting half a census. Four measured negatives, each of which was a
-- candidate refutation that did not survive contact with the source.
--
--  1. THE UNINHABITABLE RECORD. K7 declares exactly two records:
--     GroundWellOrder (K7/CCCEquivalence.agda:126) at Type (ℓ-suc ℓ) and
--     CCCHypotheses (K7/CompletionTransfer.agda:551) at Type ℓ. Both levels
--     are right, and the second is inhabited by construction here
--     (deg-hypotheses). Every other K7 declaration at Type ℓ or
--     Type (ℓ-suc ℓ) is a function or a Sigma, where the level hazard cannot
--     bite. Track D's finding 3, that a GroundWellOrder at Type ℓ typechecks
--     and can never be instantiated, was acted on before Track C landed. The
--     sweep is a NEGATIVE and the reason it is negative is that the correction
--     arrived in time.
--
--  2. THE SIBLING ARRANGEMENT. Three K7 files name a selection or a well
--     ordering in a non-comment line: K7/CompletionTransfer.agda,
--     K7/CCCEquivalence.agda and K7/TransferAtCertificate.agda. Measured over
--     the other nine, the count is 0, so the host-choice audit has nothing to
--     look at outside those three. In all three the module that holds the
--     choice is a SIBLING of the module that proves the mathematics, and no
--     construction in this file moves one of them. Every attack in PART 4 goes
--     through the type and none through the scope.
--
--  3. TRACK A's PREDICATE IS PINNED. antichain-use and antichain-intro
--     together determine antichainΔ up to logical equivalence, so no degenerate
--     stand-in satisfies both: a constantly true antichainΔ fails antichain-use,
--     whose conclusion is ⟨ p ≈ˢ q ⟩, and a constantly false one fails
--     antichain-intro. This is the one slot of Track D's telescope that the
--     degenerate audit of PART 2 could not defeat, and it had to be filled with
--     Track A's real export, which it was.
--
--  4. TRACK F's T3 PROTECTION IS REAL, per PART 6.

