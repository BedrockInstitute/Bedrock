{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track A: the forcing frame.
--
-- What this module is for. K5 states the forcing relation at an ABSTRACT
-- Boolean algebra with an abstract embedding of an abstract coded poset, and
-- never at CodedCompletion.Core. This file declares the record that carries
-- that abstraction, seals the forcing relation at the algebra, and proves the
-- six direct poset lemmas the roadmap asks for together with the one extension
-- lemma every classical clause of Track B will factor through.
--
-- Ledger. The hypotheses of the Poset layer are the structure and nothing
-- else. The hypotheses of the Forcing layer are the structure, ordinary
-- Extensionality, the path realization, the carrier code B, a Lattice, a
-- Complement and a ForcingBase. Extensionality and the path realization are
-- consumed only through K4.Implication's ≤ᴮ-antisym, and only by ⊩ᴮ-⊥ and
-- ⊩ᴮ-extend. No Separation, no PowerSet, no Collection, no Choice of any
-- kind, no LEM: every lemma below is constructive, and `grep -c "LEM"` over
-- this file with comments stripped is 0. Every remaining occurrence is inside
-- a comment, and every one of those records where the INSTANCE will spend an
-- excluded middle when it builds a ForcingBase, never where a lemma here
-- spends one.
--
-- Three module applications, all light: K4.Algebra, CodedVocabulary and
-- K4.Implication, each of which takes the structure and, in the last case, a
-- carrier code and two records. CodedCompletion.Core is NOT applied here;
-- that is ledger clause L2, and it is what keeps every statement below at
-- depth zero in an unsealed description-operator term.
--
-- Record ownership. ForcingBase is Track A's and no other track declares it.
-- The top-level denseBelowΔ is Track A's too; it is CodedCompletion.agda's
-- denseBelowᴵ (:1007-1010) lifted out of the Core telescope so that a
-- statement about an abstract frame can be written in it.
--
-- Universe ledger, and this is rule 8 discharged by inspection. ForcingBase is
-- at Type ℓ. Every field is a function into ⟨ _ ⟩ : Type ℓ, into Pt B : Type ℓ,
-- into S : Type ℓ, or into a path in Pt B, which is again Type ℓ because
-- Pt B is. NO FIELD IS A PATH IN Ω. That is exactly the difference from
-- Certificate.Embedding (Certificate.agda:414-415), which is at
-- Type (ℓ-suc ℓ) because its below-spec (:428) is a path in Ω; the same
-- content appears here as the two entailments below-in and below-out, so that
-- a join may be indexed by this record's carrier.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedVocabulary
import K4.Algebra
import K4.Implication

module K5.Frame {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The scope contract of K4/Implication.agda:64-76 applies verbatim: the three
-- record TYPE names come from K4.Algebra and never from a module that
-- re-exports them, so that opening K4.Algebra and K4.Implication together is
-- not an ambiguous module name.

open K4.Algebra 𝒮
  using ( Pt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

open CodedVocabulary 𝒮 using ( refinesΔ; compatibleΔ )

--------------------------------------------------------------------------------
-- Dense below, lifted out of the Core telescope
--------------------------------------------------------------------------------

-- "d is dense below r": every condition of the carrier refining r has a
-- refinement inside d. This is CodedCompletion.agda:1007-1010 with the four
-- parameters made explicit, in the argument order (carrier, order, r, d).
-- Nothing about a completion enters: it is a sentence about a carrier code, an
-- order code and two further codes, so it is the right vocabulary for an
-- abstract frame and it is one of the eight names ledger clause L6 permits in
-- a consumer-facing signature.

denseBelowΔ : S → S → S → S → Ω
denseBelowΔ c o r d =
  ⋀ S (λ q → (q ∈ˢ c) ⇒ (refinesΔ o q r ⇒
    ⋁ S (λ p → (p ∈ˢ d) ⊓ refinesΔ o p q)))

--------------------------------------------------------------------------------
-- The poset vocabulary
--------------------------------------------------------------------------------

-- carrier and order are the two codes of a coded presentation. They are module
-- parameters here rather than record fields for the reason K4 records at
-- K4/Algebra.agda:12-16: a projection out of a module parameter is a variable
-- and a variable cannot unfold.

module Poset (carrier order : S) where

  -- A condition is a code together with a proof that it is in the carrier.
  -- CodedCompletion.agda:223-224, and the same Σ shape as Pt.

  Cond : Type ℓ
  Cond = Σ[ x ∈ S ] ⟨ x ∈ˢ carrier ⟩

  -- "p refines q", read off the order graph. CodedVocabulary.agda:144-145.

  infix 20 _≼ᶜ_

  _≼ᶜ_ : S → S → Ω
  p ≼ᶜ q = refinesΔ order p q

  -- Compatibility, in the truncated ⋁-form and never in the Σ-form, so that it
  -- may sit inside a ⋀ or a ⋁. CodedVocabulary.agda:167-169, applied at the two
  -- codes of the conditions. The architecture prints this as
  -- `compatᶜ = compatibleΔ carrier order` and then writes `compatᶜ p q` at
  -- p q : Cond; those two do not typecheck together, and the second is the one
  -- every clause needs, so the projections are taken here.

  compatᶜ : Cond → Cond → Ω
  compatᶜ p q = compatibleΔ carrier order (fst p) (fst q)

--------------------------------------------------------------------------------
-- The one record K5 owns at the algebra level
--------------------------------------------------------------------------------

  -- A ForcingBase is: a preorder on the carrier read off the order graph, an
  -- inhabitedness clause, an embedding of the conditions into the algebra with
  -- the four clauses of Bell's Problem 2.4(iii), density of the image at
  -- nonzero, a coded extension operator with its adjunction split into two
  -- entailments, and regularity.
  --
  -- What it is NOT. It is not Certificate.Embedding (Certificate.agda:414),
  -- which has twelve fields, no inhabitant anywhere in the programme, and one
  -- level more. Three of those twelve fields are absent here on purpose:
  -- iImage, iImage-spec and the equational recover need Collection and an
  -- internal image former that Core's telescope does not supply, and K5
  -- replaces recover by the universal property below-regular.
  --
  -- What is NOT a field, and is not derivable from these. There is no
  -- injectivity of i and no ORDER REFLECTION: ⟨ i p ≤ᴮ i q ⟩ → ⟨ p ≼ᶜ q ⟩ is
  -- FALSE for a nonseparative notion, and every density argument below
  -- therefore travels through i-compat← and a common refinement instead. There
  -- is no separativity field and no antisymmetry field either; both are
  -- additional data, following ForcingNotion.agda:36-38.

  record ForcingBase (B : S) (L : Lattice B) (Cm : Complement B L) : Type ℓ where
    open Lattice L
    field

      -- The poset. Filled at the coded completion by the two ForcingLaws
      -- projections, CodedCompletion.agda:226-231, and by
      -- Presentation.inhabited, :208. All three free.

      ≼-refl    : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ p ≼ᶜ p ⟩
      ≼-trans   : (r q p : S)
                → ⟨ r ∈ˢ carrier ⟩ → ⟨ q ∈ˢ carrier ⟩ → ⟨ p ∈ˢ carrier ⟩
                → ⟨ r ≼ᶜ q ⟩ → ⟨ q ≼ᶜ p ⟩ → ⟨ r ≼ᶜ p ⟩
      inhabited : ⟨ ⋁ S (λ p → p ∈ˢ carrier) ⟩

      -- The embedding. i, i-mono and i-nonzero are free at the coded
      -- completion (:579-580, :594, and :1130 at :591). i-compat→ is free
      -- through i-compat→-at at m := i p ⊓ᴮ i q with meet-join (:1154, :1167).
      -- i-compat← costs LEM ℓ, through i-compat←-at (:1359) at the same m with
      -- meet-split (:1154).
      --
      -- Both compatibility clauses are stated in the NONZERO form rather than
      -- in K2's positive form, because nonzero is what the classical clauses
      -- of Track B produce and what Bell's arguments consume; the two are
      -- interderivable at the coded completion only through
      -- nonzero→positive (:1314), which is where the LEM ℓ of i-compat← is
      -- actually spent.

      i         : Cond → Pt B
      i-mono    : (p q : Cond) → ⟨ fst q ≼ᶜ fst p ⟩ → ⟨ i q ≤ᴮ i p ⟩
      i-nonzero : (p : Cond) → (i p ≡ ⊥ᴮ) → ⟨ ⊥ ⟩
      i-compat→ : (p q : Cond) → ⟨ compatᶜ p q ⟩ → ((i p ⊓ᴮ i q) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩
      i-compat← : (p q : Cond) → (((i p ⊓ᴮ i q) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩) → ⟨ compatᶜ p q ⟩

      -- Density of the image, stated AT NONZERO and not at inhabited, for the
      -- same reason. Free at the coded completion up to that one conversion:
      -- i-dense b ∘ nonzero→positive lem b, :610 and :1314, so LEM ℓ.

      i-dense   : (b : Pt B) → ((b ≡ ⊥ᴮ) → ⟨ ⊥ ⟩) → ⟨ ⋁ Cond (λ p → i p ≤ᴮ b) ⟩

      -- The coded extension. K2 states this as ONE PATH IN Ω
      -- (Certificate.agda:428) and pays a universe level for it. Here it is
      -- the same content as two entailments, which is what keeps this record
      -- at Type ℓ and lets a later track index a ⋁ by it.
      --
      -- At the coded completion all four are free and below itself is fst,
      -- verified in K5/ProbeD1.agda at exit 0: below-sub is B-sub (:441),
      -- below-in is i-self (:588), below-out is the where-bound below inside
      -- i-dense (:615-630), and below-regular is denseBelow→mem (:1101-1112)
      -- composed with below-out. No Separation is spent on any of them.

      below     : Pt B → S
      below-sub : (b : Pt B) → ⟨ below b ⊆ˢ carrier ⟩
      below-in  : (b : Pt B) (p : Cond) → ⟨ i p ≤ᴮ b ⟩ → ⟨ fst p ∈ˢ below b ⟩
      below-out : (b : Pt B) (p : Cond) → ⟨ fst p ∈ˢ below b ⟩ → ⟨ i p ≤ᴮ b ⟩

      -- Regularity, the one field that is a genuine property of a COMPLETION
      -- rather than of an embedding: an element already contains every
      -- condition below which its extension is dense. It is the universal
      -- property that replaces K2's equational recover.

      below-regular : (b : Pt B) (p : Cond)
                    → ⟨ denseBelowΔ carrier order (fst p) (below b) ⟩
                    → ⟨ i p ≤ᴮ b ⟩

  -- Rule 8, checked by the machine and not by inspection. A ⋁ may be indexed
  -- only by a Type ℓ, so this declaration typechecks exactly when ForcingBase
  -- has landed at Type ℓ. Break any one field into a path in Ω, for instance by
  -- replacing below-in and below-out by K2's below-spec, and this line fails
  -- with a level error before anything else in the file does.

  ForcingBase-indexes-⋁ : (B : S) (L : Lattice B) (Cm : Complement B L) → Ω
  ForcingBase-indexes-⋁ B L Cm = ⋁ (ForcingBase B L Cm) (λ _ → ⊥)

--------------------------------------------------------------------------------
-- The forcing relation at the algebra
--------------------------------------------------------------------------------

  -- Extensionality and the path realization enter here and nowhere above,
  -- and they are spent only through ≤ᴮ-antisym of K4/Implication.agda:102.

  module Forcing
    (ext   : OrdinaryProfile.Extensionality 𝒮)
    (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (B : S) (L : Lattice B) (Cm : Complement B L) (Kc : CodedComplete B L)
    (fb : ForcingBase B L Cm)
    where

    open ForcingBase fb
    open K4.Implication 𝒮 ext paths B L Cm

    -- The definition, and the whole of it: a condition forces a Boolean
    -- element when its image refines that element. Nothing recurses on a
    -- name at a condition, here or anywhere in K5.
    --
    -- The seal is not cosmetic and it is not for this file's benefit. At the
    -- instance file `i` is a sealed iᴷ and ⊓ᴮ is a sealed meetᴷ, and the
    -- measured threshold is that a DECLARATION WHOSE TYPE NESTS TWO
    -- OPERATIONS of an unsealed coded algebra does not elaborate. Sealing
    -- _⊩ᴮ_ here puts every clause theorem of Track B at depth zero in coded
    -- operations. The specification travels in the same opaque block, so a
    -- consumer that needs the unfolding has it as a path and never as an
    -- unfolding of the seal.

    opaque
      _⊩ᴮ_ : Cond → Pt B → Ω
      p ⊩ᴮ b = i p ≤ᴮ b

      ⊩ᴮ-spec : (p : Cond) (b : Pt B) → (p ⊩ᴮ b) ≡ (i p ≤ᴮ b)
      ⊩ᴮ-spec p b = refl

    infix 15 _⊩ᴮ_

    -- The two transports along the specification. Every proof below goes
    -- through these and no proof below opens the seal.

    ⊩ᴮ-intro : (p : Cond) (b : Pt B) → ⟨ i p ≤ᴮ b ⟩ → ⟨ p ⊩ᴮ b ⟩
    ⊩ᴮ-intro p b = subst ⟨_⟩ (sym (⊩ᴮ-spec p b))

    ⊩ᴮ-elim : (p : Cond) (b : Pt B) → ⟨ p ⊩ᴮ b ⟩ → ⟨ i p ≤ᴮ b ⟩
    ⊩ᴮ-elim p b = subst ⟨_⟩ (⊩ᴮ-spec p b)

    -- "W is dense below p", for a HOST predicate on conditions. This is the
    -- shape the regularity clause and the classical clauses of Track B both
    -- consume. It is the host-side companion of denseBelowΔ and the two are
    -- related by ⊩ᴮ-reg below.

    DenseBelow : Cond → (Cond → Ω) → Ω
    DenseBelow p W =
      ⋀ Cond (λ q → (fst q ≼ᶜ fst p) ⇒
        ⋁ Cond (λ r → (fst r ≼ᶜ fst q) ⊓ W r))

--------------------------------------------------------------------------------
-- The six direct poset lemmas
--------------------------------------------------------------------------------

    -- Forcing an element and belonging to its coded extension are the same
    -- thing. This is the pair of entailments that replaces K2's path, and it
    -- is what makes the whole relation readable inside the model.

    ⊩ᴮ-mem : (p : Cond) (b : Pt B) → ⟨ p ⊩ᴮ b ⟩ → ⟨ fst p ∈ˢ below b ⟩
    ⊩ᴮ-mem p b h = below-in b p (⊩ᴮ-elim p b h)

    ⊩ᴮ-from : (p : Cond) (b : Pt B) → ⟨ fst p ∈ˢ below b ⟩ → ⟨ p ⊩ᴮ b ⟩
    ⊩ᴮ-from p b h = ⊩ᴮ-intro p b (below-out b p h)

    -- Monotonicity: a stronger condition forces everything a weaker one does.
    -- Note the direction of the hypothesis. It is fst q ≼ᶜ fst p, "q refines
    -- p", and the conclusion moves from p to q.

    ⊩ᴮ-mono : (p q : Cond) (b : Pt B)
            → ⟨ fst q ≼ᶜ fst p ⟩ → ⟨ p ⊩ᴮ b ⟩ → ⟨ q ⊩ᴮ b ⟩
    ⊩ᴮ-mono p q b hqp h =
      ⊩ᴮ-intro q b (⊆ˢ-trans (i-mono p q hqp) (⊩ᴮ-elim p b h))

    -- Forcing is dense below. This half is monotonicity with the refinement
    -- taken to be the condition itself, so it needs only ≼-refl.

    ⊩ᴮ-down : (p : Cond) (b : Pt B)
            → ⟨ p ⊩ᴮ b ⟩ → ⟨ DenseBelow p (λ r → r ⊩ᴮ b) ⟩
    ⊩ᴮ-down p b h q hqp =
      ∣ q , (≼-refl (fst q) (snd q) , ⊩ᴮ-mono p q b hqp h) ∣₁

    -- And the converse: if forcing b is dense below p then p forces b. This is
    -- the dense-below characterization, it is the content of regularity, and
    -- IT COSTS NO EXCLUDED MIDDLE. K2 measured the same thing on its own side
    -- and wrote the correction into its source at
    -- CodedCompletion.agda:1136-1142: "The architecture charged this direction
    -- a LEM and it does not cost one."

    ⊩ᴮ-reg : (p : Cond) (b : Pt B)
           → ⟨ DenseBelow p (λ r → r ⊩ᴮ b) ⟩ → ⟨ p ⊩ᴮ b ⟩
    ⊩ᴮ-reg p b db = ⊩ᴮ-intro p b (below-regular b p step)
      where
        step : ⟨ denseBelowΔ carrier order (fst p) (below b) ⟩
        step q hq hqp =
          PT.map (λ { (r , hrq , hr) → fst r , (⊩ᴮ-mem r b hr , hrq) })
                 (db (q , hq) hqp)

    -- Nothing forces the bottom. The proof spends i-nonzero and could not be
    -- written without it: at a DEGENERATE algebra, where ⊤ᴮ ≡ ⊥ᴮ, every
    -- condition forces ⊥ᴮ and this lemma is FALSE. Neither K4's three algebra
    -- records (K4/Algebra.agda:101, :132, :157) nor K2's carry a nontriviality
    -- field, so i-nonzero is where the exclusion happens, and it excludes the
    -- degenerate algebra exactly when a condition is in scope.

    ⊩ᴮ-⊥ : (p : Cond) → ⟨ p ⊩ᴮ ⊥ᴮ ⟩ → ⟨ ⊥ ⟩
    ⊩ᴮ-⊥ p h = i-nonzero p (≤⊥→≡⊥ (i p) (⊩ᴮ-elim p ⊥ᴮ h))

--------------------------------------------------------------------------------
-- The extension lemma
--------------------------------------------------------------------------------

    -- Every classical clause of Track B factors through this one lemma, and
    -- the lemma itself is FREE. Given a condition q whose image meets b
    -- nontrivially, some refinement of q forces b.
    --
    -- The route, and the trap it avoids. Density of the image gives a
    -- condition s whose image refines i q ⊓ᴮ b. It does NOT give s ≼ᶜ q:
    -- reading an order relation back off an inequality between images is
    -- order reflection, which is false for a nonseparative notion. What i s
    -- ≤ᴮ i q does give is that i s ⊓ᴮ i q is i s, which is nonzero, so
    -- i-compat← returns compatibility of s with q, and a common refinement r
    -- of the two is a condition that both refines q and, by monotonicity and
    -- transitivity of inclusion, forces b. No separativity and no order
    -- reflection anywhere.

    ⊩ᴮ-extend : (q : Cond) (b : Pt B)
              → (((i q ⊓ᴮ b) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩)
              → ⟨ ⋁ Cond (λ r → (fst r ≼ᶜ fst q) ⊓ (r ⊩ᴮ b)) ⟩
    ⊩ᴮ-extend q b nz =
      PT.rec (snd goal) fromDense (i-dense (i q ⊓ᴮ b) nz)
      where
        goal : Ω
        goal = ⋁ Cond (λ r → (fst r ≼ᶜ fst q) ⊓ (r ⊩ᴮ b))

        fromCommon : (s : Cond) → ⟨ i s ≤ᴮ b ⟩
                   → Σ[ r ∈ S ] ⟨ (r ∈ˢ carrier) ⊓ ((r ≼ᶜ fst s) ⊓ (r ≼ᶜ fst q)) ⟩
                   → ⟨ goal ⟩
        fromCommon s hsb (r , hrc , hrs , hrq) =
          ∣ (r , hrc)
          , ( hrq
            , ⊩ᴮ-intro (r , hrc) b
                (⊆ˢ-trans (i-mono s (r , hrc) hrs) hsb) ) ∣₁

        fromDense : Σ[ s ∈ Cond ] ⟨ i s ≤ᴮ (i q ⊓ᴮ b) ⟩ → ⟨ goal ⟩
        fromDense (s , hs) =
          PT.rec (snd goal) (fromCommon s hsb) (i-compat← s q nzs)
          where
            hsq : ⟨ i s ≤ᴮ i q ⟩
            hsq = ⊆ˢ-trans hs (⊓-lb₁ (i q) b)
            hsb : ⟨ i s ≤ᴮ b ⟩
            hsb = ⊆ˢ-trans hs (⊓-lb₂ (i q) b)
            nzs : ((i s ⊓ᴮ i q) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩
            nzs e = i-nonzero s (sym (≤→⊓ (i s) (i q) hsq) ∙ e)

--------------------------------------------------------------------------------
-- The non-claims this track is required to state beside its signatures
--------------------------------------------------------------------------------

-- O1. The atomic graph has no discharge at any ground. The record is at
-- K4/AtomicGraph.agda:411, the single route to it at :719-720, and its
-- TableSupply at :616-617 is uninhabited. Nothing in this file depends on it,
-- and no statement in this file may be read as discharging it.
--
-- O2. The coded and the host semantic agreement is conditional by design and
-- its two hypotheses, ReadsSup and ReadsInf (K4/HostSemantics.agda:895-900),
-- are unproved upstream. This file touches no host value at all. In
-- particular the sentence at K4/HostSemantics.agda:1205-1213, which says the
-- agreement is unconditional on the quantifier-free fragment, is refuted and
-- is not quoted anywhere here.
--
-- O6. No coded order graph of B exists, so isGeneric in K2's sense
-- (CodedCompletion.agda:1070-1074) cannot be stated of a subset of the
-- algebra. That is an unbuilt interface and not an unproved theorem. Track D
-- delivers a filter that reflects G and is an ultrafilter under LEM ℓ, and
-- says so; this file states nothing about genericity.
--
-- ORDER REFLECTION. ⟨ i p ≤ᴮ i q ⟩ → ⟨ fst p ≼ᶜ fst q ⟩ is FALSE, and it is
-- not assumed, derived or used anywhere above. K2 refutes it at
-- InstancesCompletion.agda:131-134, in the completion of its own two-condition
-- non-refined poset, where the two conditions have the same image and one does
-- not refine the other. That is why ⊩ᴮ-extend travels through i-compat← and a
-- common refinement and never reads an order relation back off an inequality
-- between images.
--
-- SEPARATIVITY is likewise not a field and not a hypothesis. It is additional
-- data (ForcingNotion.agda:276-278), and no lemma above needs it.
