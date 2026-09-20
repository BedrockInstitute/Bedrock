{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track D. THE ZFC COMPLETION TRANSFER, AS A PROPERTY CERTIFICATE.
--
-- The roadmap's words are the specification (roadmap:213): the transfer
-- "must consume M's choice, not an unmentioned choice function on external
-- families". K7 is the first package in this programme whose mathematics
-- genuinely wants choice, and this is the theorem that wants it.
--
-- WHERE THE CHOICE IS, AND WHY IT IS THE MODEL'S.
--
-- The classical ccc transfer runs: let A be an antichain of the nonzero part
-- B⁺; for each a ∈ A pick a condition p with i p ≤ a; distinct members of A
-- are incompatible, so the picked conditions are pairwise incompatible and
-- pairwise distinct; hence A injects into an antichain of P, and ccc of P
-- bounds A. The word "pick" is the whole ledger question. Picked by a host
-- function S → S supplied from outside, the transfer is a choiceless
-- CCC transfer, which section 8 of the architecture forbids by name and which
-- Corollary 6.5 of the design document shows cannot hold in general. Picked by
-- the lt-least element of a ground set, under M's own well ordering, it is a
-- theorem of M.
--
-- This file makes that distinction visible in a signature and nowhere else:
--
--   * module Well takes M's well ordering and NOTHING ELSE. Its theorem is
--     that the lt-least member of an inhabited ground set is a PROVED UNIQUE
--     witness, so the selection is unique choice and not choice.
--   * module Structural takes the embedding and the antichain vocabulary and
--     is a SIBLING of Well, so the well ordering is not in scope where the
--     two structural lemmas of the transfer are proved. That is K6's own
--     mechanical AC check (K6/Choice.agda:31-38, :415 inside :343 beside
--     :772) and it is stronger than any grep, because no later edit can
--     falsify it without moving a module.
--   * module Transfer assembles the certificate. CCCHypotheses is a NAMED
--     record whose fields are the obligations, and hyp-from-ground is the
--     inhabitation lemma that supplies exactly the ones M's choice pays for.
--
-- WHAT THIS FILE DOES NOT APPLY, and the reason is measured rather than
-- prudent. Certificate.Nonzero is not applied here: Nonzero.B⁺ 𝔓 c sep occurs
-- in the TYPE of PropertyTransfer.transfer, which is rule 3's exact shape and
-- rule 2b's nested-operation shape. The B⁺ block arrives flat, because a
-- module parameter is maximally stuck (rule 2b as K6's Track A refined it,
-- 1.05 s sealed against 1.08 s unsealed). The single application lives in
-- K7/TransferAtCertificate.agda and is measured in this track's report.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.CompletionTransfer
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_ )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎ ; inr to inr⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import GroundDescription
import CodedVocabulary

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module GD = GroundDescription 𝒮 ext paths
module CV = CodedVocabulary 𝒮

open OP using ( iff; Separation; Collection )
open OP.PathRealization paths using ( ≈ˢ-to-path; path-to-≈ˢ )
open GD using ( the; the-spec; SetExists; hasImage′ )
open CV using ( refinesΔ; compatibleΔ; subsetΔ )
open At S id using ( _⊨_ )

--------------------------------------------------------------------------------
-- PART 1. M's CHOICE, AS A UNIQUE-WITNESS OPERATOR
--------------------------------------------------------------------------------

-- The three fields are K6's ground well ordering, K6/Choice.agda:418-422,
-- character for character, reaching this file as an opaque type plus its three
-- projections rather than as a re-declared record: Track C owns the record and
-- rule 9 says records are generative.
--
-- Read the quantifiers. lt is a relation on ground CODES; lt-tri compares two
-- codes; wo-least ranges over d : S, a ground SET, and not over a host
-- predicate S → Ω. The poisoned form quantifies over a host predicate, which
-- is ground CLASS Separation, which is obstruction O3b, and which is on disk
-- as K6/breaks/ClassLeast.agda-break. That distinction is the whole of the
-- ledger row (K6/Choice.agda:411-413).

module Well
  (GroundWellOrder : Type (ℓ-suc ℓ))
  (ltOf  : GroundWellOrder → S → S → Ω)
  (triOf : (wo : GroundWellOrder) (z z' : S)
         → ∥ ⟨ ltOf wo z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ ltOf wo z' z ⟩) ∥₁)
  (leastOf : (wo : GroundWellOrder) (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩
           → ⟨ ⋁ S (λ z → (z ∈ˢ d)
                 ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((ltOf wo z' z) ⇒ ⊥))) ⟩)
  where

  -- "z is the lt-least member of d", as a truth value of the model.

  leastIn : GroundWellOrder → S → S → Ω
  leastIn wo d z = (z ∈ˢ d) ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((ltOf wo z' z) ⇒ ⊥))

  Least : GroundWellOrder → S → Type ℓ
  Least wo d = Σ[ z ∈ S ] ⟨ leastIn wo d z ⟩

  -- THE THEOREM OF THIS TRACK, and the reason the transfer is unique choice
  -- rather than choice. Two lt-minimal members of one ground set are equal:
  -- trichotomy offers three cases and the two strict ones contradict
  -- minimality of the other side. Nothing here is truncated away, so the
  -- conclusion is a host PATH and not a mere ≈ˢ.

  least-unique : (wo : GroundWellOrder) (d z z' : S)
               → ⟨ leastIn wo d z ⟩ → ⟨ leastIn wo d z' ⟩ → z ≡ z'
  least-unique wo d z z' hz hz' = PT.rec (isSetS z z') step (triOf wo z z')
    where
      step : ⟨ ltOf wo z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ ltOf wo z' z ⟩) → z ≡ z'
      step (inl⊎ l)        = Empty.rec* (snd hz' z (fst hz) l)
      step (inr⊎ (inl⊎ e)) = e
      step (inr⊎ (inr⊎ l)) = Empty.rec* (snd hz z' (fst hz') l)

  isPropLeast : (wo : GroundWellOrder) (d : S) → isProp (Least wo d)
  isPropLeast wo d x y =
    Σ≡Prop (λ z → snd (leastIn wo d z))
      (least-unique wo d (fst x) (fst y) (snd x) (snd y))

  -- Contractibility is the shape hasImage′ demands of a functional relation
  -- (GroundDescription.agda:183). wo-least supplies a TRUNCATED witness; the
  -- uniqueness above turns the truncation into the witness itself, because a
  -- truncation eliminates into a proposition. This is the one allowed shape:
  -- a proved-unique witness becoming a simultaneous internal function.

  least-contr : (wo : GroundWellOrder) (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩
              → isContr (Least wo d)
  least-contr wo d inh = centre , λ y → isPropLeast wo d centre y
    where
      centre : Least wo d
      centre = PT.rec (isPropLeast wo d) (λ z → z) (leastOf wo d inh)

  pick : (wo : GroundWellOrder) (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩ → S
  pick wo d inh = fst (fst (least-contr wo d inh))

  pick-least : (wo : GroundWellOrder) (d : S) (inh : ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩)
             → ⟨ leastIn wo d (pick wo d inh) ⟩
  pick-least wo d inh = snd (fst (least-contr wo d inh))

  pick-in : (wo : GroundWellOrder) (d : S) (inh : ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩)
          → ⟨ pick wo d inh ∈ˢ d ⟩
  pick-in wo d inh = fst (pick-least wo d inh)

  -- The selection RELATION, in the shape K6's own Sel carries
  -- (K6/Choice.agda:425-431): an Ω on ground codes, never a host function.

  selectAt : GroundWellOrder → (S → S) → S → S → Ω
  selectAt wo fam u p = leastIn wo (fam u) p

  select-total : (wo : GroundWellOrder) (fam : S → S) (u : S)
               → ⟨ ⋁ S (λ z → z ∈ˢ fam u) ⟩
               → ⟨ ⋁ S (λ p → selectAt wo fam u p) ⟩
  select-total wo fam u inh = ∣ pick wo (fam u) inh , pick-least wo (fam u) inh ∣₁

  select-in : (wo : GroundWellOrder) (fam : S → S) (u p : S)
            → ⟨ selectAt wo fam u p ⟩ → ⟨ p ∈ˢ fam u ⟩
  select-in wo fam u p h = fst h

  select-unique : (wo : GroundWellOrder) (fam : S → S) (u p p' : S)
                → ⟨ selectAt wo fam u p ⟩ → ⟨ selectAt wo fam u p' ⟩ → p ≡ p'
  select-unique wo fam u = least-unique wo (fam u)

--------------------------------------------------------------------------------
-- OBSTRUCTION O6-FOR-B⁺, WRITTEN AS A TYPE SO THE MISSING OBJECT HAS A NAME
--------------------------------------------------------------------------------

-- Decision Q2 asked whether K7 builds the coded order graph of the nonzero
-- part or ships the row. THIS TRACK SHIPS THE ROW, and this is the exact
-- object it is a row about.
--
-- Nonzero.B⁺ (Certificate.agda:996-999) is a Certificate.Presentation, whose
-- order field is _≼_ = λ u v → fst u ⊆ˢ fst v, a HOST relation on points. The
-- coded record (CodedCompletion.agda:201-208) instead carries order : S, a
-- ground set of Kuratowski pairs, because Separation reads a formula and a
-- formula takes the order code as a constant slot. A chain condition read off
-- B⁺'s host relation is therefore not a theorem OF M, and every Ψ this track
-- delivers is applied to a presentation whose order is the parameter order⁺.
--
-- THE ROUTE IS FULLY NAMED AND PRICED, measured at source in this session, so
-- that the next track does not re-discover it.
--
--   * The graph is cut by ONE Separation out of the double power set of B⁺set,
--     since entry u v = {{u},{u,v}} lies in P(P(B⁺set)) when u and v lie in
--     B⁺set. Cost: +PowerSet on this one declaration, as decision Q2 predicted.
--   * The forward direction needs component recovery: from one code z with
--     isKPairΔ z u v and isKPairΔ z p q, conclude u ≡ p and v ≡ q. That is NOT
--     the determinacy lemma the tree proves. kpair-det (NameSupport.agda:233)
--     runs the other way, from equal components to an equal code. The chain
--     that does run is kpair-det composed with entry-isKPair to get
--     z ≡ entry u v (NameSpace.agda:388-389, kpair-unique), then entry-fst
--     (NameKernel.agda:275) and its companion on the second coordinate. That
--     chain costs +Pairing, because entry is pairOf nested three deep
--     (NameKernel.agda:253-254).
--   * entry-inj itself is a PARAMETER wherever it is consumed
--     (TranslateForward.agda:146, StandardNames.agda:159) and is proved only
--     inside NameKernel's own module, so a K7 consumer must either apply
--     NameKernel or carry the three-line interface flat.
--
-- Total price: PowerSet + Pairing + Separation on one declaration, plus the
-- NameKernel entry interface. That is strictly more than this track's ledger
-- and it is a construction, not a certificate, so it belongs beside K6/OnePoint
-- rather than here.

OrderGraphFor : S → Type ℓ
OrderGraphFor b =
  Σ[ o ∈ S ]
    ( ⟨ ⋀ S (λ z → (z ∈ˢ o) ⇒ ⋁ S (λ p → ⋁ S (λ q →
          (p ∈ˢ b) ⊓ ((q ∈ˢ b) ⊓ CV.isKPairΔ z p q)))) ⟩
    × ((u v : S) → ⟨ u ∈ˢ b ⟩ → ⟨ v ∈ˢ b ⟩
       → ⟨ iff (refinesΔ o u v) (u ⊆ˢ v) ⟩) )

--------------------------------------------------------------------------------
-- PART 2. THE TRANSFER'S MATHEMATICS, WITH THE WELL ORDERING OUT OF SCOPE
--------------------------------------------------------------------------------

-- module Structural is a SIBLING of module Well and not a submodule of it.
-- That arrangement is the AC check, and K6 records why it is stronger than a
-- grep (K6/Choice.agda:31-38): a later edit cannot falsify it without moving a
-- module, whereas a token census over a file can be falsified by one rename.
-- Everything below is ordinary order theory about an embedding, and none of it
-- can mention lt, because lt is not in scope.
--
-- The geometry, in the shape the certificate layer exports it
-- (Certificate.agda:414-436). `img p` is the code of the algebra element i p,
-- `below b` is Bell's P_b, the set of conditions whose image refines b
-- (fulltext:3479-3480), and order⁺ is the coded order graph of the nonzero
-- part. That last parameter is obstruction O6-for-B⁺ (architecture 1.4.2):
-- Nonzero.B⁺ (Certificate.agda:996-999) carries _≼_ = λ u v → fst u ⊆ˢ fst v
-- and NO order : S, so a chain condition read off B⁺ directly quantifies
-- through a host relation and is not a theorem of M. Part 4 below builds the
-- missing graph.

module Structural
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
  -- Track A's antichain predicate, flat, through its two directions. Both are
  -- currying at Track A's definition (architecture 2.1) and neither unfolds it
  -- here, so this file cannot drift from Track A's choice of equality.
  (antichainΔ : S → S → S → Ω)
  (antichain-use : (c o d p q : S) → ⟨ antichainΔ c o d ⟩
                 → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
                 → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
  (antichain-intro : (c o d : S)
                   → ((p q : S) → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
                      → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
                   → ⟨ antichainΔ c o d ⟩)
  where

  -- Two conditions whose images both refine a common element are compatible in
  -- the nonzero part, and this is where the embedding's positivity is spent:
  -- img p lies in B⁺set, so it is a legitimate witness of compatibility there.

  meets : (u v p : S) → ⟨ p ∈ˢ carrier ⟩
        → ⟨ refinesΔ order⁺ (img p) u ⟩ → ⟨ refinesΔ order⁺ (img p) v ⟩
        → ⟨ compatibleΔ B⁺set order⁺ u v ⟩
  meets u v p hp hu hv = ∣ img p , img-in p hp , hu , hv ∣₁

  -- A selection, as an internal RELATION on ground codes. This is K6's own
  -- Sel (K6/Choice.agda:425-431) at this track's family: never a host function
  -- S → S, because a host function is precisely the unmentioned choice
  -- function on external families that roadmap:213 forbids.

  module WithSelection
    (selRel        : S → S → Ω)
    (sel-below     : (u p : S) → ⟨ selRel u p ⟩ → ⟨ p ∈ˢ below u ⟩)
    (sel-unique    : (u p q : S) → ⟨ selRel u p ⟩ → ⟨ selRel u q ⟩ → p ≡ q)
    where

    sel-cond : (u p : S) → ⟨ selRel u p ⟩ → ⟨ p ∈ˢ carrier ⟩
    sel-cond u p h = below-sub u p (sel-below u p h)

    sel-refines : (u p : S) → ⟨ selRel u p ⟩ → ⟨ refinesΔ order⁺ (img p) u ⟩
    sel-refines u p h = below-refines u p (sel-below u p h)

    ----------------------------------------------------------------------------
    -- LEMMA ONE. The selection is injective on an antichain.
    ----------------------------------------------------------------------------

    -- If one condition is selected for both u and v then its image refines
    -- both, so u and v meet, so the antichain law identifies them. This is the
    -- step that makes the classical proof's "a ↦ p_a is injective" a theorem
    -- rather than a counting remark.

    sel-injective : (d u v p : S) → ⟨ antichainΔ B⁺set order⁺ d ⟩
                  → ⟨ u ∈ˢ B⁺set ⟩ → ⟨ u ∈ˢ d ⟩ → ⟨ v ∈ˢ B⁺set ⟩ → ⟨ v ∈ˢ d ⟩
                  → ⟨ selRel u p ⟩ → ⟨ selRel v p ⟩ → u ≡ v
    sel-injective d u v p ac hu hud hv hvd su sv =
      ≈ˢ-to-path u v
        (antichain-use B⁺set order⁺ d u v ac hu hud hv hvd
          (meets u v p (sel-cond u p su) (sel-refines u p su) (sel-refines v p sv)))

    ----------------------------------------------------------------------------
    -- LEMMA TWO. The selected conditions are pairwise incompatible.
    ----------------------------------------------------------------------------

    -- Suppose p is selected for u, q for v, and p and q have a common
    -- refinement r in the presentation. Monotonicity of the embedding carries
    -- img r below img p and below img q, transitivity carries it below u and
    -- below v, so u and v meet and the antichain law identifies them; then p
    -- and q are two selections for the SAME element and uniqueness identifies
    -- them. Every step is order theory, and the only property of the selection
    -- used is its uniqueness.

    sel-antichain : (d : S) → ⟨ antichainΔ B⁺set order⁺ d ⟩
                  → ((u : S) → ⟨ u ∈ˢ d ⟩ → ⟨ u ∈ˢ B⁺set ⟩)
                  → (e : S)
                  → ((y : S) → ⟨ y ∈ˢ e ⟩ → ⟨ ⋁ S (λ u → (u ∈ˢ d) ⊓ selRel u y) ⟩)
                  → ⟨ antichainΔ carrier order e ⟩
    sel-antichain d ac dsub e espec = antichain-intro carrier order e step
      where
        step : (p q : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ p ∈ˢ e ⟩
             → ⟨ q ∈ˢ carrier ⟩ → ⟨ q ∈ˢ e ⟩
             → ⟨ compatibleΔ carrier order p q ⟩ → ⟨ p ≈ˢ q ⟩
        step p q hp hpe hq hqe cm =
          PT.rec (snd (p ≈ˢ q))
            (λ { (u , hud , su) →
                 PT.rec (snd (p ≈ˢ q))
                   (λ { (v , hvd , sv) →
                        PT.rec (snd (p ≈ˢ q)) (close u v hud su hvd sv) cm })
                   (espec q hqe) })
            (espec p hpe)
          where
            close : (u v : S) → ⟨ u ∈ˢ d ⟩ → ⟨ selRel u p ⟩
                  → ⟨ v ∈ˢ d ⟩ → ⟨ selRel v q ⟩
                  → Σ[ r ∈ S ] ⟨ (r ∈ˢ carrier)
                        ⊓ (refinesΔ order r p ⊓ refinesΔ order r q) ⟩
                  → ⟨ p ≈ˢ q ⟩
            close u v hud su hvd sv (r , hr , hrp , hrq) =
              path-to-≈ˢ p q (sel-unique u p q su (subst (λ z → ⟨ selRel z q ⟩) (sym u≡v) sv))
              where
                imgr-u : ⟨ refinesΔ order⁺ (img r) u ⟩
                imgr-u = refines⁺-trans (img r) (img p) u
                  (img-mono r p hr (sel-cond u p su) hrp) (sel-refines u p su)

                imgr-v : ⟨ refinesΔ order⁺ (img r) v ⟩
                imgr-v = refines⁺-trans (img r) (img q) v
                  (img-mono r q hr (sel-cond v q sv) hrq) (sel-refines v q sv)

                u≡v : u ≡ v
                u≡v = ≈ˢ-to-path u v
                  (antichain-use B⁺set order⁺ d u v ac
                    (dsub u hud) hud (dsub v hvd) hvd
                    (meets u v r hr imgr-u imgr-v))


    ----------------------------------------------------------------------------
    -- THE IMAGE OF AN ANTICHAIN, AND THE ONE DATUM THAT IS STILL MISSING
    ----------------------------------------------------------------------------

    -- hasImage′ (GroundDescription.agda:181-185) takes Separation and
    -- Collection as two STANDALONE arguments and turns a host-contractible
    -- relation into an internal image set. This is a correction to ruling Q3,
    -- which names OrdinaryProfile.hasImage (:340-344) and records the widening
    -- of K7's ground profile to the whole OrdinaryZF record as the price of
    -- using it. THE WIDENING IS NOT NECESSARY: the flat form exists, it is the
    -- one K3 and K4 already consume (NameImage.agda:215, K4/ValueSets.agda:771),
    -- and this track consumes it too. Rule 14: the measurement wins.
    --
    -- What is still missing is the FORMULA. hasImage′ reads a Formula S 2, and
    -- selRel is an Ω on ground codes with no object-language spelling: at the
    -- instance it is leastIn under M's well ordering, and the well ordering is
    -- three host-valued components with no Δ₀ certificate anywhere. K6 met the
    -- same wall and resolved it the same way, by taking selCand and selName as
    -- PARAMETERS with in/out specifications rather than defining them
    -- (K6/Choice.agda:463-487). SelDefinable is that obligation, named.

    -- Type (ℓ-suc ℓ) and not Type ℓ, measured: the reading is a path between
    -- truth values and Ω is hProp ℓ. That is the same level fact that decided
    -- CCCHypotheses' fields, and it is why SelDefinable is a module parameter
    -- of Image rather than a field of the record.

    SelDefinable : Type (ℓ-suc ℓ)
    SelDefinable =
      Σ[ φ ∈ Formula S 2 ] ((u p : S) → ((p ∷ u ∷ []) ⊨ φ) ≡ selRel u p)

    module Image
      (sep  : Separation)
      (coll : Collection)
      (def  : SelDefinable)
      (sel-total : (u : S) → ⟨ u ∈ˢ B⁺set ⟩ → ⟨ ⋁ S (λ p → selRel u p) ⟩)
      where

      private
        φ : Formula S 2
        φ = fst def

        read : (u p : S) → ((p ∷ u ∷ []) ⊨ φ) ≡ selRel u p
        read = snd def

        Fib : S → Type ℓ
        Fib u = Σ[ y ∈ S ] ⟨ (y ∷ u ∷ []) ⊨ φ ⟩

        toRel : (u y : S) → ⟨ (y ∷ u ∷ []) ⊨ φ ⟩ → ⟨ selRel u y ⟩
        toRel u y h = subst ⟨_⟩ (read u y) h

        ofRel : (u y : S) → ⟨ selRel u y ⟩ → ⟨ (y ∷ u ∷ []) ⊨ φ ⟩
        ofRel u y h = subst ⟨_⟩ (sym (read u y)) h

        isPropFib : (u : S) → isProp (Fib u)
        isPropFib u x y =
          Σ≡Prop (λ z → snd ((z ∷ u ∷ []) ⊨ φ))
            (sel-unique u (fst x) (fst y)
              (toRel u (fst x) (snd x)) (toRel u (fst y) (snd y)))

        -- Host contractibility, which is what hasImage′ calls functionality.
        -- Existence is M's choice through sel-total; uniqueness is the
        -- selection's own uniqueness, which at the instance is least-unique.

        functional : (d : S) → ⟨ subsetΔ d B⁺set ⟩
                   → (u : S) → ⟨ u ∈ˢ d ⟩ → isContr (Fib u)
        functional d dsub u hu = centre , λ y → isPropFib u centre y
          where
            centre : Fib u
            centre = PT.rec (isPropFib u)
              (λ { (p , hp) → p , ofRel u p hp })
              (sel-total u (dsub u hu))

        Pred : S → S → Ω
        Pred d y = ⋁ S (λ u → (u ∈ˢ d) ⊓ selRel u y)

        rewrite-pred : (d : S)
          → (λ y → ⋁ S (λ u → (u ∈ˢ d) ⊓ ((y ∷ u ∷ []) ⊨ φ))) ≡ Pred d
        rewrite-pred d = funExt (λ y →
          cong (⋁ S) (funExt (λ u → cong ((u ∈ˢ d) ⊓_) (read u y))))

        exists : (d : S) → ⟨ subsetΔ d B⁺set ⟩ → ⟨ SetExists (Pred d) ⟩
        exists d dsub =
          subst (λ Q → ⟨ SetExists Q ⟩) (rewrite-pred d)
            (hasImage′ sep coll d φ (functional d dsub))

      selImage : (d : S) → ⟨ subsetΔ d B⁺set ⟩ → S
      selImage d dsub = the (Pred d) (exists d dsub)

      selImage-spec : (d : S) (dsub : ⟨ subsetΔ d B⁺set ⟩) (y : S)
                    → (y ∈ˢ selImage d dsub) ≡ Pred d y
      selImage-spec d dsub = the-spec (Pred d) (exists d dsub)

      selImage-in : (d : S) (dsub : ⟨ subsetΔ d B⁺set ⟩) (u y : S)
                  → ⟨ u ∈ˢ d ⟩ → ⟨ selRel u y ⟩ → ⟨ y ∈ˢ selImage d dsub ⟩
      selImage-in d dsub u y hu h =
        subst ⟨_⟩ (sym (selImage-spec d dsub y)) ∣ u , hu , h ∣₁

      selImage-out : (d : S) (dsub : ⟨ subsetΔ d B⁺set ⟩) (y : S)
                   → ⟨ y ∈ˢ selImage d dsub ⟩ → ⟨ Pred d y ⟩
      selImage-out d dsub y h = subst ⟨_⟩ (selImage-spec d dsub y) h

      selImage-sub : (d : S) (dsub : ⟨ subsetΔ d B⁺set ⟩)
                   → ⟨ subsetΔ (selImage d dsub) carrier ⟩
      selImage-sub d dsub y hy = PT.rec (snd (y ∈ˢ carrier))
        (λ { (u , _ , h) → sel-cond u y h })
        (selImage-out d dsub y hy)

    ----------------------------------------------------------------------------
    -- PART 3. THE PROPERTY CERTIFICATE
    ----------------------------------------------------------------------------

    -- PropertyTransfer (Certificate.agda:1542-1545) has TWO fields, hypotheses
    -- and transfer, and hypotheses : Type ℓ is unconstrained. A true transfer
    -- and a vacuous one therefore have the identical type, and no check run at
    -- the record can tell them apart; K7/breaks/TransferVacuous.agda-break
    -- exhibits the vacuous inhabitant and its exit 0 is the finding. What
    -- discriminates is a NAMED record whose fields are the actual obligations,
    -- together with an inhabitation lemma beside it. Those are the two
    -- constructions below.
    --
    -- TWO MEASURED CONSTRAINTS DECIDED THE SHAPE OF THIS RECORD, and both
    -- contradict the architecture's sketch at 2.4. Rule 14 applies: the
    -- measurement wins.
    --
    --  (a) hypotheses is Type ℓ and Ω is hProp ℓ, which is Type (ℓ-suc ℓ). So
    --      NO field of CCCHypotheses may be a PREDICATE: selRel : S → S → Ω is
    --      rejected with [ConstructorDoesNotFitInData] at exit 1. The selection
    --      relation is therefore a module PARAMETER and the record carries only
    --      proofs about it. That is the better arrangement on rule 2b's
    --      measurement as well, since a parameter is maximally stuck, and it is
    --      the better arrangement on rule 15, since the predicate is in the
    --      telescope, which is where the audit reads it.
    --  (b) For the same reason no field may be a PATH between truth values:
    --      (y ∈ˢ selImage d) ≡ ⋁ S (…) also lands in Type (ℓ-suc ℓ). The image
    --      specification is the in/out PAIR that K6 uses throughout module
    --      Names (K6/Choice.agda, cut-in/cut-out, selCand-in/selCand-out),
    --      which is the same content at Type ℓ.
    --
    -- 2.4's sketch has `order⁺ : S` and `order⁺-typed` as fields. They are
    -- parameters of module Structural here, for reason (a) applied to
    -- order-typed, whose type is a truth value's inhabitant and would be
    -- admissible, but which belongs beside the order it types.

    module Transfer
      (HostPresentation : Type (ℓ-suc ℓ))
      (𝔓ᴴ B⁺ : HostPresentation)
      (Φ Ψ   : HostPresentation → Ω)
      -- Track A's CCC₂ predicate, flat, through its two directions, and the
      -- ground ω code against which countability is read. injectable is
      -- CardinalBridge.agda:379-388: a TRUNCATED join, which hands back no
      -- selector, which is why it is the only countability on the right side
      -- of the ledger. There is no isSurjection and no isFinite in the compile
      -- root, measured.
      (CCC₂ᴵ      : S → S → S → Ω)
      (injectable : S → S → Ω)
      (w : S)
      (ccc-use   : (c o v d : S) → ⟨ CCC₂ᴵ c o v ⟩ → ⟨ subsetΔ d c ⟩
                 → ⟨ antichainΔ c o d ⟩ → ⟨ injectable d v ⟩)
      (ccc-intro : (c o v : S)
                 → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
                    → ⟨ injectable d v ⟩)
                 → ⟨ CCC₂ᴵ c o v ⟩)
      -- The two readings. Both are refl at the seam probe, and without them Φ
      -- and Ψ are arbitrary and transfer-runs says nothing whatever: that is
      -- F2's finding about PropertyTransfer, met here rather than inherited.
      (Φ-reading : Φ 𝔓ᴴ ≡ CCC₂ᴵ carrier order  w)
      (Ψ-reading : Ψ B⁺  ≡ CCC₂ᴵ B⁺set  order⁺ w)
      where

      -- What M's choice pays for, and it is the ONLY thing the record asks of
      -- the model's own axioms: that every element of the nonzero part has a
      -- selected condition. At the instance this is module Well's select-total
      -- at the family λ u → below u, whose inhabitation hypothesis is the
      -- density of i[P] in B⁺ (Bell, fulltext:3486).

      SelTotal : Type ℓ
      SelTotal = (u : S) → ⟨ u ∈ˢ B⁺set ⟩ → ⟨ ⋁ S (λ p → selRel u p) ⟩

      record CCCHypotheses : Type ℓ where
        field
          sel-total : SelTotal
          -- The image of an antichain under the selection, as a ground SET. At
          -- the instance this is hasImage′ (GroundDescription.agda:181-185) at
          -- a formula for selRel, cut down by `the` (:107) since
          -- Extensionality makes the image set unique.
          selImage      : (d : S) → ⟨ subsetΔ d B⁺set ⟩ → S
          selImage-sub  : (d : S) (ds : ⟨ subsetΔ d B⁺set ⟩)
                        → ⟨ subsetΔ (selImage d ds) carrier ⟩
          selImage-in   : (d : S) (ds : ⟨ subsetΔ d B⁺set ⟩) (u y : S)
                        → ⟨ u ∈ˢ d ⟩ → ⟨ selRel u y ⟩ → ⟨ y ∈ˢ selImage d ds ⟩
          selImage-out  : (d : S) (ds : ⟨ subsetΔ d B⁺set ⟩) (y : S)
                        → ⟨ y ∈ˢ selImage d ds ⟩
                        → ⟨ ⋁ S (λ u → (u ∈ˢ d) ⊓ selRel u y) ⟩
          -- The counting step: an injective total internal relation from d
          -- into e carries countability back. Measured: injectable has ZERO
          -- theorems anywhere in the compile root (architecture G3), so this is
          -- Track B's obligation and is carried as a field rather than assumed
          -- away.
          pull-injectable :
              (d e : S)
            → ((u : S) → ⟨ u ∈ˢ d ⟩ → ⟨ ⋁ S (λ p → (p ∈ˢ e) ⊓ selRel u p) ⟩)
            → ((u v p : S) → ⟨ u ∈ˢ d ⟩ → ⟨ v ∈ˢ d ⟩
               → ⟨ selRel u p ⟩ → ⟨ selRel v p ⟩ → u ≡ v)
            → ⟨ injectable e w ⟩ → ⟨ injectable d w ⟩

      --------------------------------------------------------------------------
      -- THE TRANSFER
      --------------------------------------------------------------------------

      -- Bell's ccc transfer, run inside M. Given an antichain d of the nonzero
      -- part, the selection sends it into the presentation; Lemma Two says the
      -- image is an antichain there, so CCC₂ of the presentation makes the
      -- image countable; Lemma One says the selection is injective on d, so the
      -- counting comes back. Neither lemma mentions the well ordering.

      transfer-runs : CCCHypotheses → ⟨ Φ 𝔓ᴴ ⟩ → ⟨ Ψ B⁺ ⟩
      transfer-runs H hΦ = subst ⟨_⟩ (sym Ψ-reading) concl
        where
          open CCCHypotheses H

          ccc : ⟨ CCC₂ᴵ carrier order w ⟩
          ccc = subst ⟨_⟩ Φ-reading hΦ

          concl : ⟨ CCC₂ᴵ B⁺set order⁺ w ⟩
          concl = ccc-intro B⁺set order⁺ w step
            where
              step : (d : S) → ⟨ subsetΔ d B⁺set ⟩
                   → ⟨ antichainΔ B⁺set order⁺ d ⟩ → ⟨ injectable d w ⟩
              step d dsub ac =
                pull-injectable d (selImage d dsub) total inj imageCount
                where
                  imageCount : ⟨ injectable (selImage d dsub) w ⟩
                  imageCount = ccc-use carrier order w (selImage d dsub) ccc
                    (selImage-sub d dsub)
                    (sel-antichain d ac dsub (selImage d dsub)
                      (selImage-out d dsub))

                  total : (u : S) → ⟨ u ∈ˢ d ⟩
                        → ⟨ ⋁ S (λ p → (p ∈ˢ selImage d dsub) ⊓ selRel u p) ⟩
                  total u hu = PT.map
                    (λ { (p , sp) → p , selImage-in d dsub u p hu sp , sp })
                    (sel-total u (dsub u hu))

                  inj : (u v p : S) → ⟨ u ∈ˢ d ⟩ → ⟨ v ∈ˢ d ⟩
                      → ⟨ selRel u p ⟩ → ⟨ selRel v p ⟩ → u ≡ v
                  inj u v p hu hv su sv =
                    sel-injective d u v p ac (dsub u hu) hu (dsub v hv) hv su sv

      --------------------------------------------------------------------------
      -- THE INHABITATION LEMMA
      --------------------------------------------------------------------------

      -- GroundWellOrder is OPAQUE here, exactly as it is at K6/Choice.agda:939
      -- where it reaches zfcᴾ as an opaque type. The assembly must not be able
      -- to look inside it; the composition with module Well's three parameters
      -- is made in K7/TransferAtCertificate.agda and nowhere else. That is what
      -- makes "the transfer consumes M's choice" a fact about a signature
      -- rather than a claim about a proof, and it is why the two structural
      -- lemmas above could be proved with lt out of scope.

      hyp-from-ground :
          (GroundWellOrder : Type (ℓ-suc ℓ))
        → GroundWellOrder
        → (GroundWellOrder → SelTotal)
        → (selImage : (d : S) → ⟨ subsetΔ d B⁺set ⟩ → S)
        → ((d : S) (ds : ⟨ subsetΔ d B⁺set ⟩)
           → ⟨ subsetΔ (selImage d ds) carrier ⟩)
        → ((d : S) (ds : ⟨ subsetΔ d B⁺set ⟩) (u y : S)
           → ⟨ u ∈ˢ d ⟩ → ⟨ selRel u y ⟩ → ⟨ y ∈ˢ selImage d ds ⟩)
        → ((d : S) (ds : ⟨ subsetΔ d B⁺set ⟩) (y : S) → ⟨ y ∈ˢ selImage d ds ⟩
           → ⟨ ⋁ S (λ u → (u ∈ˢ d) ⊓ selRel u y) ⟩)
        → ((d e : S)
           → ((u : S) → ⟨ u ∈ˢ d ⟩ → ⟨ ⋁ S (λ p → (p ∈ˢ e) ⊓ selRel u p) ⟩)
           → ((u v p : S) → ⟨ u ∈ˢ d ⟩ → ⟨ v ∈ˢ d ⟩
              → ⟨ selRel u p ⟩ → ⟨ selRel v p ⟩ → u ≡ v)
           → ⟨ injectable e w ⟩ → ⟨ injectable d w ⟩)
        → CCCHypotheses
      hyp-from-ground GWO wo supply im im-sub im-in im-out pull = record
        { sel-total       = supply wo
        ; selImage        = im
        ; selImage-sub    = im-sub
        ; selImage-in     = im-in
        ; selImage-out    = im-out
        ; pull-injectable = pull }

      -- And the version that actually spends something. Given M's choice
      -- through the opaque carrier, ground Separation and Collection as two
      -- standalone arguments, and the one definability datum, FOUR of the six
      -- obligations are discharged and only the counting step remains. This is
      -- the honest measure of what this track closed: the certificate's
      -- content is now M's choice plus SelDefinable plus Track B's calculus,
      -- and nothing else.

      hyp-from-choice :
          (GroundWellOrder : Type (ℓ-suc ℓ))
        → GroundWellOrder
        → (GroundWellOrder → SelTotal)
        → Separation → Collection → SelDefinable
        → ((d e : S)
           → ((u : S) → ⟨ u ∈ˢ d ⟩ → ⟨ ⋁ S (λ p → (p ∈ˢ e) ⊓ selRel u p) ⟩)
           → ((u v p : S) → ⟨ u ∈ˢ d ⟩ → ⟨ v ∈ˢ d ⟩
              → ⟨ selRel u p ⟩ → ⟨ selRel v p ⟩ → u ≡ v)
           → ⟨ injectable e w ⟩ → ⟨ injectable d w ⟩)
        → CCCHypotheses
      hyp-from-choice GWO wo supply sep coll def pull = record
        { sel-total       = supply wo
        ; selImage        = I.selImage
        ; selImage-sub    = I.selImage-sub
        ; selImage-in     = I.selImage-in
        ; selImage-out    = I.selImage-out
        ; pull-injectable = pull }
        where
          module I = Image sep coll def (supply wo)

      --------------------------------------------------------------------------
      -- RULE 14. THE STATEMENT K7 REFUSES
      --------------------------------------------------------------------------

      -- Transcribed so a reader sees the exact shape, and NOT inhabited
      -- anywhere in this tree. This is the choiceless CCC transfer that
      -- section 8 of the architecture forbids by name and that Corollary 6.5 of
      -- forcing-geology-design-2026-09.md shows fails in general: the selector
      -- is a bare host function S → S on an external family, with no uniqueness
      -- demanded of it, so nothing internal to M names it. Compare selRel and
      -- SelTotal. The difference is invisible in any conclusion's type and
      -- visible only in the telescope, which is rule 15's whole content.

      ChoicelessTransfer : Type ℓ
      ChoicelessTransfer =
          (d : S) → ⟨ subsetΔ d B⁺set ⟩ → ⟨ antichainΔ B⁺set order⁺ d ⟩
        → Σ[ pick ∈ (S → S) ] ((u : S) → ⟨ u ∈ˢ d ⟩ → ⟨ pick u ∈ˢ below u ⟩)
