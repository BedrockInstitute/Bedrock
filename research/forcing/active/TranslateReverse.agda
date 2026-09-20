{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track G: the reverse translation, from the Boolean presentation back to
-- the poset one.
--
-- Section 1.9 of the K3 architecture, reverse half. The question this file
-- answers is Bell's, read backwards. A B-valued name weights each of its
-- subnames by an element of the complete Boolean algebra. A P-name weights
-- each of its subnames by a condition. So a translation from the first to the
-- second must answer: given a subname carried at Boolean weight b, at WHICH
-- conditions should the translated name carry the translated subname?
--
-- THE ANSWER IS: AT ALL OF THEM, AND NEVER AT A CHOSEN ONE. The reverse
-- translation of a B-weighted entry ⟨x, b⟩ is the whole family of entries
-- ⟨trᴾ x, p⟩ for every condition p whose image refines b. That set is K2's
-- `below b` and it is a ground code, supplied by the completion certificate
-- (Certificate.agda:412-414) for exactly this purpose.
--
-- Four independent reasons, and the architecture's own decision paragraph
-- (section 1.9) collects them. The sharpest is concrete: below ⊤ᴮ = carrier,
-- so the non-selecting translation carries the Boolean check name {⟨y̌, ⊤ᴮ⟩}
-- exactly onto the poset check name {⟨y̌, p⟩ : p a condition}, while a
-- selecting version returns {⟨y̌, p₀⟩}, whose value is empty in every generic
-- extension that misses p₀. Next: i carries no injectivity field and never
-- will (Certificate.agda:406-410 lists i, i-mono, i-pos, i-compat→, i-compat←
-- and no i-inj), so "the condition whose image is b" is not even expressible.
-- Next: a singleton is not downward closed, so K5's "p forces φ iff i p ≤
-- value φ" fails at the filter. And last: a map El → Cond picking a condition
-- below each Boolean element IS a choice function on B, forbidden outright by
-- the K0 ledger row "Host AC, CC, DC, Zorn, BPI, new resizing axioms |
-- Forbidden" and named in the choice audit as K3's exact leak
-- (dev/literature/no-host-choice-audit-2026-09.md:33).
--
-- The prohibition is grep-checkable and it was run on this file before the
-- report was written. There is no El → Cond anywhere, no truncation
-- eliminated into Cond, no use of injectivity of i, and no round trip.
--
-- ---------------------------------------------------------------------------
-- WHAT THIS FILE DOES NOT CLAIM. Section 1.9's seven non-claims, verbatim in
-- substance, and each is repeated beside the signature it constrains.
--
--  1. No raw round trip, in either order. Raw names need not coincide
--     (roadmap:169). below (i q) is the REGULARIZED cone of q, not the set
--     {p : p ≼ q}: it is the set of conditions whose image refines i q, and
--     the image of a condition is a regular open set, not a cone. Nothing
--     below states trᴾ (trᴮ n) ≡ n or trᴮ (trᴾ n) ≡ n, and neither is true.
--  2. No denotational round trip. Those wait for K4 and K5 (roadmap:169).
--     K2's `recover` (Certificate.agda:420-421) is the fact those packages
--     will consume; this file neither restates nor reproves it.
--  3. No quotient of names, by Boolean equality or anything else.
--  4. No injectivity, surjectivity or order reflection for either
--     translation. trᴾ is in fact NOT injective: below ⊥ᴮ is empty, so a
--     bottom-weighted child emits no entry at all and two Boolean names
--     differing only in bottom-weighted entries have the same translation.
--  5. No normalization of weights to a function. The weight of a subname
--     stays a SET (Track B's weightsAt), here unioned over `below`.
--  6. No selector El → Cond, no truncation eliminated into Cond, no host
--     choice of any form.
--  7. The relabelling recursion is not the value recursion. Bell 1.15/1.16
--     recurses on PAIRS with both coordinates descending (fulltext:2013-2030);
--     that is Track A's RawPairRec and Track I's business, and it stays
--     separate. This file's recursion moves one coordinate.
--
-- ---------------------------------------------------------------------------
-- THE TIER THIS TRACK STANDS ON, DECIDED BEFORE THE FIRST LINE WAS WRITTEN.
--
-- Track D's keystone finding F8 puts the question to this track directly:
-- trᴾ is a host recursion whose step needs the image of a ground code under a
-- function the recursion is itself defining, and section 3's parameter list
-- for Track G carries nothing that supplies one. The finding is correct. The
-- answer is the same widening Track H took and it is named here in full:
--
--   * TIER 4, NameKernel.MemberImage, as the two flat parameters `image` and
--     `image-spec`. Not derivable from any first-order axiom: Collection
--     reads a Formula S 2 and trᴾ, at the moment the step runs, is a host
--     function with no formula (architecture N2).
--   * TIER 0, accessibility, in the form Track A already packages it, namely
--     child-wf : WellFounded Child. This track recurses on Child and NOT on
--     the ground's membership, which is the one structural difference from
--     Track H's check recursion: the object being taken apart is an existing
--     name, so its subnames are what descend.
--   * THE UNION HALF OF TIER 2, as `unionOf` and `unionOf-spec`. A single
--     B-weighted entry contributes a whole LAYER of poset entries, one per
--     refining condition, so the layers must be glued. This is charged twice,
--     once for the layer of a subname and once for the union of `below` over
--     the subname's weight set.
--   * TRACK B's SUPPORT AND WEIGHT FAMILY, as flat parameters. This is the
--     mathematically interesting one and it is what makes the construction
--     possible at all. The step must range over the SUBNAMES of n, and the
--     only way to see a subname of a ground code without decoding a
--     truncation is Track B's `support`, which is a Separation on ⋃²n and is
--     TOTAL. Its elimination rule support-out hands back the Child edge that
--     the well-founded recursion needs, with no name hypothesis. Track B's
--     Separation is therefore charged as well, through its interface.
--
-- WHAT IS NOT TAKEN: no Collection, no PowerSet, no Infinity, no Foundation
-- schema, no LEM at any level, no isZFModel, no isZFCModel, no L. import, no
-- V. import, no TransitiveClosure, no name rank, no set quotient, no Choice.
--
-- ---------------------------------------------------------------------------
-- CROSSING THE TWO WEIGHT CARRIERS. Track H measured, and told this track
-- before dispatch, that Track A's kernel at W = B and at W = carrier does not
-- share entry, Child, Entryᴺ or Shape definitionally, because entry is built
-- from a sealed pairOf; that removing the seal is not a repair, since the run
-- was killed without finishing and reproduced Track A's 761 s figure; and
-- that the affordable repair is a twenty-line extensionality bridge written
-- once (ProbeH2.agda). A translation crosses the carriers at EVERY entry, not
-- at one module boundary, so this file is built so that the crossing costs
-- nothing at all:
--
--   ONE `entry`, ONE `Child`, taken as parameters and used at both weights.
--
-- The kernel's entry and its Child relation do not mention W: an entry is a
-- Kuratowski pair and Child quantifies its weight over the whole of S
-- (NameKernel.agda:253, :368). Only Shape, IsName, Name and the support
-- depend on the weight carrier, and each of those enters here as its OWN
-- parameter, marked ᴮ or ᴾ. A consumer discharges the ᴮ ones from the kernel
-- at W = B and the ᴾ ones from the kernel at W = carrier, and supplies the
-- extensionality bridge exactly once at that seam, as ProbeH2.agda does. No
-- unfolding, no seal, no convertibility obligation inside this file.
--
-- ---------------------------------------------------------------------------
-- THE TWO PROJECT-LEVEL RULES, and how this file obeys them.
--
-- Seal every description-operator term with its specification. This file
-- contains NO description-operator term: every ground-code former it uses
-- (entry, image, unionOf, below, support, weightsAt) is a module parameter,
-- and a parameter is a variable with no unfolding at all, which seals more
-- tightly than an opaque block. The one term this file defines by recursion,
-- trᴾ, is a WFI.induction spine over the variable child-wf and is stuck for
-- the same reason.
--
-- Keep a construction of one layer applied to a term of another out of TYPES.
-- Every layer crossing that appears in a type below (below applied to a
-- weight, image applied to a support) is an application of a VARIABLE, which
-- is the remedy the correction banner prescribes: the composite is abstracted
-- into a variable and the specification is a hypothesis. Nothing here is a
-- meet of two constructed elements or a join of a constructed family.
--
-- The three mechanical lessons of section 3.0. Lesson 1, bare refl under a
-- truth-value operation, is avoided by producing every Ω-equality either by a
-- hypothesis handed over whole or by ⇔toPath with both directions named.
-- Lesson 2, the implicit class argument, cannot arise: there is no `the`.
-- Lesson 3, the lifted bottom, cannot arise: ⊥ does not occur.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module TranslateReverse {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import CodedVocabulary 𝒮 using ( isKPairΔ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

--------------------------------------------------------------------------------
-- Shared vocabulary, restated so that this file imports no K3 module
--------------------------------------------------------------------------------

-- A join over a proposition, at a family that does not read the witness, is a
-- meet. The tier-4 image specification joins over the membership witness
-- (NameKernel.agda:139-142, in the corrected form all three of Tracks A, D
-- and H arrived at independently), and every image taken below except the
-- recursion itself ignores that witness, so this one line converts the datum's
-- shape into the ⊓-shaped form the architecture writes.

∃-prop : (A Q : Ω) → ⋁ ⟨ A ⟩ (λ _ → Q) ≡ (A ⊓ Q)
∃-prop A Q = ⇔toPath (PT.rec (snd (A ⊓ Q)) (λ z → z)) (λ z → ∣ z ∣₁)

-- Track D's internalization contract (NameImage.agda:97), restated rather
-- than imported. A consumer receives an operation and its membership
-- specification and learns nothing about how the operation was obtained;
-- Track D's img-unique says that two internalizations of one function are one
-- operation, so no coherence obligation travels with it. The record sits at
-- Type (ℓ-suc ℓ) because img-spec is a path in Ω, exactly as Track D's F2
-- measured.

record InternalImage (f : S → S) : Type (ℓ-suc ℓ) where
  field
    img      : S → S
    img-spec : (a z : S) → (z ∈ˢ img a) ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))

-- Track C's coded closure predicate (NameSpace.agda:153-158), written out
-- rather than imported, and character for character the same expression: a
-- family C is entry-closed at weight carrier w when every member of every
-- member of C is a Kuratowski pair whose first coordinate is again in C and
-- whose second lies in w. Every quantifier is bounded, which is why Track C
-- can certify it Δ₀ and put it inside a Separation. This file needs it in
-- two directions and both are cheap: it CONSUMES closure at the Boolean
-- carrier, as a hypothesis, and it PRODUCES closure at the poset carrier, as
-- the closure theorem's conclusion.

closedΔ : S → S → Ω
closedΔ w C =
  ⋀ S (λ n → (n ∈ˢ C) ⇒
    (⋀ S (λ e → (e ∈ˢ n) ⇒
      (⋁ S (λ x → (x ∈ˢ C) ⊓
        (⋁ S (λ b → (b ∈ˢ w) ⊓ isKPairΔ e x b)))))))

--------------------------------------------------------------------------------
-- The cone of refining conditions
--------------------------------------------------------------------------------

-- Everything in this module is about ONE object: below b, the set of
-- conditions whose image refines the Boolean element b. K2 builds it and
-- certifies it (Certificate.agda:412-414); this track proves the four laws
-- the roadmap's phrase "prove its closure" (roadmap:169) actually names, and
-- the one identification that connects the two check names.
--
-- NON-CLAIM 1, stated where it belongs. below (i q) is the REGULARIZED cone.
-- below-i says q itself is in it and below-down says it is closed downward,
-- but it is in general strictly larger than {p : p ≼ q}: a condition
-- incompatible with nothing that q rules out lands in the regularization
-- without refining q. That is why no round trip is stated anywhere in this
-- file and why raw names need not coincide.
--
-- The completion data arrive as flat parameters, not as K2's Embedding
-- record, and not by importing CodedCompletion: Track H and Track I both
-- measured that El and Presentation are not reachable from this compile root,
-- and the architecture's own decision (section 1.0) is that K3 builds none of
-- these and takes them as parameters. El and Cond are written out in the
-- telescope because a module telescope cannot use the module's own
-- definitions; they are named inside the body and every later signature uses
-- the names.
--
-- The refinement relation enters as an abstract Ω-valued relation on
-- CONDITIONS rather than as the coded order on raw codes. The architecture
-- writes below-down with ⟨ q ≼ᴵ p ⟩ on bare codes; a consumer instantiating
-- from K2 has i-mono in the shape ⟨ q ≼ p ⟩ on Pt carrier
-- (Certificate.agda:405), so stating it on conditions is what makes the two
-- fit with no adapter.

module Cone
  (carrier B  : S)
  (_≤ᴮ_       : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → Ω)
  (≤ᴮ-refl    : (u : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → ⟨ u ≤ᴮ u ⟩)
  (≤ᴮ-trans   : (u v w : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩)
              → ⟨ u ≤ᴮ v ⟩ → ⟨ v ≤ᴮ w ⟩ → ⟨ u ≤ᴮ w ⟩)
  (positiveᴮ  : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → Ω)
  (_≼ᶜ_       : (Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩)
              → (Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩) → Ω)
  (i          : (Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩) → (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩))
  (i-mono     : (p q : Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩)
              → ⟨ q ≼ᶜ p ⟩ → ⟨ i q ≤ᴮ i p ⟩)
  (i-dense    : (b : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → ⟨ positiveᴮ b ⟩
              → ⟨ ⋁ (Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩) (λ p → i p ≤ᴮ b) ⟩)
  (below      : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → S)
  (below-sub  : (b : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → ⟨ below b ⊆ˢ carrier ⟩)
  (below-spec : (b : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) (p : Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩)
              → (fst p ∈ˢ below b) ≡ (i p ≤ᴮ b))
  (ext-path   : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  where

  Cond : Type ℓ
  Cond = Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩

  El : Type ℓ
  El = Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩

-- A condition lies in the cone of its own image. This is below-spec read at
-- reflexivity and it is the only place ≤ᴮ-refl is spent.

  below-i : (p : Cond) → ⟨ fst p ∈ˢ below (i p) ⟩
  below-i p = subst ⟨_⟩ (sym (below-spec (i p) p)) (≤ᴮ-refl (i p))

-- The cone grows with the weight. This is one transitivity step, and it is
-- what makes the reverse translation monotone in the Boolean order without
-- any statement about names.

  below-mono : (b c : El) → ⟨ b ≤ᴮ c ⟩ → ⟨ below b ⊆ˢ below c ⟩
  below-mono b c le p hp =
    subst ⟨_⟩ (sym (below-spec c pc))
      (≤ᴮ-trans (i pc) b c (subst ⟨_⟩ (below-spec b pc) hp) le)
    where
      pc : Cond
      pc = p , below-sub b p hp

-- The cone is closed downward in the order of conditions. This is the first
-- of the two statements the roadmap's "prove its closure" abbreviates, and it
-- is the reason a poset name built from `below b` is a legitimate P-name:
-- K5's forcing relation reads a downward-closed set of conditions and a
-- singleton is not one.

  below-down : (b : El) (p q : S) (hq : ⟨ q ∈ˢ carrier ⟩)
             → (hp : ⟨ p ∈ˢ below b ⟩)
             → ⟨ (q , hq) ≼ᶜ (p , below-sub b p hp) ⟩
             → ⟨ q ∈ˢ below b ⟩
  below-down b p q hq hp ref =
    subst ⟨_⟩ (sym (below-spec b (q , hq)))
      (≤ᴮ-trans (i (q , hq)) (i pc) b
        (i-mono pc (q , hq) ref)
        (subst ⟨_⟩ (below-spec b pc) hp))
    where
      pc : Cond
      pc = p , below-sub b p hp

-- The cone of a positive element is inhabited, and it is CONSTRUCTIVE. The
-- K2 architecture had predicted a LEM hypothesis here; there is none. K2's
-- i-dense (CodedCompletion.agda:609-627) is itself constructive, and this
-- theorem is i-dense followed by below-spec, with the pair discarded down to
-- its first coordinate. Nothing is eliminated out of the truncation: the
-- conclusion is a truncated existential too.
--
-- NON-CLAIM 6 lives here. A reader looking for a selector would look for a
-- function El → Cond, and this is the closest any signature in the file comes
-- to one. It is not one: it returns a TRUNCATED existential, and there is no
-- elimination of it into Cond anywhere below. Every use of below-pos in this
-- file eliminates into a proposition.

  below-pos : (b : El) → ⟨ positiveᴮ b ⟩ → ⟨ ⋁ S (λ p → p ∈ˢ below b) ⟩
  below-pos b pos =
    PT.map (λ { (p , le) → fst p , subst ⟨_⟩ (sym (below-spec b p)) le })
           (i-dense b pos)

-- And the identification that carries the whole non-selection decision. The
-- top of the completion IS the carrier (CodedCompletion.agda:511-512), and
-- every condition's image refines the top, so the cone of the top is the set
-- of ALL conditions. This is the step at which the Boolean check name's
-- single top-weighted entry becomes the poset check name's entry at every
-- condition, and Track H's checkᴾ-is-reverse is where it is spent.

  module Top (⊤ᴮ∈B   : ⟨ carrier ∈ˢ B ⟩)
             (⊤ᴮ-top : (u : El) → ⟨ u ≤ᴮ (carrier , ⊤ᴮ∈B) ⟩) where

    below-⊤ : below (carrier , ⊤ᴮ∈B) ≡ carrier
    below-⊤ = ext-path (λ x → ⇔toPath (below-sub (carrier , ⊤ᴮ∈B) x) (into x))
      where
        into : (x : S) → ⟨ x ∈ˢ carrier ⟩ → ⟨ x ∈ˢ below (carrier , ⊤ᴮ∈B) ⟩
        into x hx = subst ⟨_⟩ (sym (below-spec (carrier , ⊤ᴮ∈B) (x , hx)))
                              (⊤ᴮ-top (i (x , hx)))

--------------------------------------------------------------------------------
-- The kernel interface, taken once and used at both weight carriers
--------------------------------------------------------------------------------

-- Track A owns every parameter of this module and none of them mentions a
-- weight carrier. entry x b is the Kuratowski pair weighting the subname x by
-- b; entry-inj is its injectivity, proved once in Track A and spent here at
-- exactly three theorems; entry-isKPair is the object-language reading of the
-- same term, spent only in the closure theorem; Child is the subname
-- relation with its introduction and elimination rules; child-wf is the
-- accessibility that runs the recursion.
--
-- child-entry and child-elim are taken as parameters rather than read off
-- Track A's transparent definition, so this file still works if Track A ever
-- seals Child. Track B took the introduction half for that reason and Track H
-- took the elimination half; this file needs both.

module Names
  (entry         : S → S → S)
  (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
  (Child         : S → S → Type ℓ)
  (child-entry   : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-elim    : (x n : S) (Q : Ω) → Child x n
                 → ((b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ Q ⟩) → ⟨ Q ⟩)
  (child-wf      : WellFounded Child)
  (≈ˢ-paths      : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (ext-path      : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  where

-- The structure's equality in the two shapes the two layers use. Every
-- crossing below goes through one of these three lines.

  ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (≈ˢ-paths x y)

  ≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
  ≡→≈ˢ {x} {y} = subst ⟨_⟩ (sym (≈ˢ-paths x y))

  ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈ˢ-refl x = ≡→≈ˢ refl

--------------------------------------------------------------------------------
-- The two ground existence data the translation consumes
--------------------------------------------------------------------------------

-- Tier 4 and the union half of tier 2, flat. See the header for why neither
-- is derivable and why neither alone suffices.

  module Ground
    (image        : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S)
    (image-spec   : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
                  → (z ∈ˢ image a f)
                  ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))))
    (unionOf      : S → S)
    (unionOf-spec : (t z : S) → (z ∈ˢ unionOf t)
                  ≡ ⋁ S (λ u → (u ∈ˢ t) ⊓ (z ∈ˢ u)))
    where

-- The image of a HOST function over a code. Only the recursion itself reads
-- the membership witness, because only the recursive call needs it; every
-- other image below is an imageOn and its specification is the ⊓-shaped one.

    imageOn : S → (S → S) → S
    imageOn c f = image c (λ q → f (fst q))

    imageOn-spec : (c : S) (f : S → S) (z : S)
                 → (z ∈ˢ imageOn c f) ≡ ⋁ S (λ x → (x ∈ˢ c) ⊓ (z ≈ˢ f x))
    imageOn-spec c f z =
      image-spec c (λ q → f (fst q)) z
      ∙ cong (⋁ S) (funExt (λ x → ∃-prop (x ∈ˢ c) (z ≈ˢ f x)))

--------------------------------------------------------------------------------
-- The reverse translation
--------------------------------------------------------------------------------

-- Now the mathematics. Read the construction in three layers, innermost
-- first, because that is the order in which the ground sets are formed.
--
-- LAYER 1, belowAt n x. A subname x may occur in n at MANY Boolean weights;
-- Track B's weightsAt n x is the set of them and there is no function picking
-- one (K0's ruling, k0-representation-decision-2026-09.md:7). The conditions
-- that should carry the translated subname are those refining SOME weight at
-- which x occurs, so belowAt n x is the union of below over the weight set.
-- This is the first place where non-selection is visible in the term: two
-- unions, no choice, and the family is indexed by a ground code.
--
-- LAYER 2, layer n x t. Given the translated subname t, the poset entries it
-- contributes are ⟨t, p⟩ for every p in belowAt n x. That is one image.
--
-- LAYER 3, the recursion. trᴾ n is the union of the layers of the subnames of
-- n. The index is Track B's support n, whose elimination rule support-out
-- hands back the Child edge that justifies the recursive call. This is the
-- step that could not be taken without Track B: the members of n are entries,
-- decoding an entry into its coordinates is available only under a
-- truncation, and a truncation does not eliminate into S. The support turns
-- that truncated decoding into a Separation that was already done once.
--
-- WHY THE RECURSION IS ON Child AND NOT ON MEMBERSHIP. Track H's check
-- recursion descends in the ground's ∈ because it consumes an arbitrary
-- ground set. This one consumes a NAME and rebuilds it, so what descends is
-- the subname relation. Track A's child-wf is the accessibility for exactly
-- that, and it is derived from tier-0 accessibility through the chain
-- x ∈ {x} ∈ entry x b ∈ n once and for all (NameKernel.agda:392).
--
-- Track B's interface is taken flat, in the derived form each theorem
-- actually uses, rather than as the coded specifications support-spec and
-- weightsAt-spec. Three of the six are one-line consequences of Track B's
-- own exports and the derivations are recorded in REPORT-G.md; taking them
-- flat keeps this compile independent of Track B's seals and keeps the
-- isKPairΔ layer out of every proof below.

    module Over
      (carrier B       : S)
      (below           : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → S)
      (below-sub       : (b : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → ⟨ below b ⊆ˢ carrier ⟩)
      (supportᴮ        : S → S)
      (weightsAt       : S → S → S)
      (support-outᴮ    : (n x : S) → ⟨ x ∈ˢ supportᴮ n ⟩ → Child x n)
      (support-entryᴮ  : (n x b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ entry x b ∈ˢ n ⟩
                       → ⟨ x ∈ˢ supportᴮ n ⟩)
      (support-weightᴮ : (n x : S) → ⟨ x ∈ˢ supportᴮ n ⟩
                       → ⟨ ⋁ S (λ b → b ∈ˢ weightsAt n x) ⟩)
      (weightsAt-sub   : (n x b : S) → ⟨ b ∈ˢ weightsAt n x ⟩ → ⟨ b ∈ˢ B ⟩)
      (weightsAt-in    : (n x b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ entry x b ∈ˢ n ⟩
                       → ⟨ b ∈ˢ weightsAt n x ⟩)
      (weightsAt-out   : (n x b : S) → ⟨ b ∈ˢ weightsAt n x ⟩
                       → ⟨ entry x b ∈ˢ n ⟩)
      where

      El : Type ℓ
      El = Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩

-- Membership in B is a proposition, so which proof of it a weight carries
-- never matters. This one line is what lets a weight read off Track B's
-- weight family be handed to `below` and compared with a weight the caller
-- supplied with its own proof.

      below-irr : {b : S} (h h' : ⟨ b ∈ˢ B ⟩) → below (b , h) ≡ below (b , h')
      below-irr {b} h h' = cong below (Σ≡Prop (λ t → snd (t ∈ˢ B)) refl)

-- LAYER 1. The family of cones indexed by the weight set, and its union.

      belowFam : (n x : S) → (Σ[ b ∈ S ] ⟨ b ∈ˢ weightsAt n x ⟩) → S
      belowFam n x r = below (fst r , weightsAt-sub n x (fst r) (snd r))

      belowAt : S → S → S
      belowAt n x = unionOf (image (weightsAt n x) (belowFam n x))

      belowAt-spec : (n x p : S) → (p ∈ˢ belowAt n x)
                   ≡ ⋁ S (λ b → ⋁ ⟨ b ∈ˢ weightsAt n x ⟩
                         (λ hb → p ∈ˢ below (b , weightsAt-sub n x b hb)))
      belowAt-spec n x p =
          unionOf-spec (image (weightsAt n x) (belowFam n x)) p
        ∙ ⇔toPath to fro
        where
          target : Ω
          target = ⋁ S (λ b → ⋁ ⟨ b ∈ˢ weightsAt n x ⟩
                        (λ hb → p ∈ˢ below (b , weightsAt-sub n x b hb)))

          to : ⟨ ⋁ S (λ u → (u ∈ˢ image (weightsAt n x) (belowFam n x))
                            ⊓ (p ∈ˢ u)) ⟩
             → ⟨ target ⟩
          to = PT.rec (snd target) (λ { (u , hu , hp) →
                 PT.rec (snd target)
                   (λ { (b , inner) → PT.rec (snd target)
                          (λ { (hb , equ) →
                                 ∣ b , ∣ hb , subst (λ t → ⟨ p ∈ˢ t ⟩)
                                                    (≈ˢ→≡ equ) hp ∣₁ ∣₁ })
                          inner })
                   (subst ⟨_⟩ (image-spec (weightsAt n x) (belowFam n x) u) hu) })

          fro : ⟨ target ⟩
              → ⟨ ⋁ S (λ u → (u ∈ˢ image (weightsAt n x) (belowFam n x))
                             ⊓ (p ∈ˢ u)) ⟩
          fro = PT.rec PT.squash₁ (λ { (b , inner) →
                  PT.rec PT.squash₁
                    (λ { (hb , hp) →
                           ∣ belowFam n x (b , hb)
                           , subst ⟨_⟩ (sym (image-spec (weightsAt n x)
                                               (belowFam n x)
                                               (belowFam n x (b , hb))))
                               ∣ b , ∣ hb , ≈ˢ-refl (belowFam n x (b , hb)) ∣₁ ∣₁
                           , hp ∣₁ })
                    inner })

-- LAYER 2. One translated subname, spread over the conditions that refine one
-- of its weights. Compare Track H's `spread`, which spreads over a FIXED
-- weight set; here the weight set depends on the subname, and that dependence
-- is the whole difference between a check name and a translation.

      layer : S → S → S → S
      layer n x t = imageOn (belowAt n x) (λ p → entry t p)

      layer-spec : (n x t e : S) → (e ∈ˢ layer n x t)
                 ≡ ⋁ S (λ p → (p ∈ˢ belowAt n x) ⊓ (e ≈ˢ entry t p))
      layer-spec n x t e = imageOn-spec (belowAt n x) (λ p → entry t p) e

-- LAYER 3. The recursion. The computation law is PROPOSITIONAL, as every
-- well-founded recursion in the host is; nothing below expects trᴾ to reduce,
-- and every use rewrites along trᴾ-host or, far more often, along the entry
-- law.

      trStep : (n : S) → ((x : S) → Child x n → S) → S
      trStep n rec =
        unionOf (image (supportᴮ n)
          (λ q → layer n (fst q) (rec (fst q) (support-outᴮ n (fst q) (snd q)))))

      trᴾ : S → S
      trᴾ = WFI.induction child-wf {P = λ _ → S} trStep

      trᴾ-host : (n : S)
               → trᴾ n ≡ unionOf (imageOn (supportᴮ n) (λ x → layer n x (trᴾ x)))
      trᴾ-host = WFI.induction-compute child-wf {P = λ _ → S} trStep

-- The membership specification in its raw layered form. Every later theorem
-- goes through the entry law below instead; this is the one step that absorbs
-- the union and the outer image.

      trᴾ-layers : (n e : S) → (e ∈ˢ trᴾ n)
                 ≡ ⋁ S (λ x → (x ∈ˢ supportᴮ n) ⊓ (e ∈ˢ layer n x (trᴾ x)))
      trᴾ-layers n e =
          cong (e ∈ˢ_) (trᴾ-host n)
        ∙ unionOf-spec (imageOn (supportᴮ n) (λ x → layer n x (trᴾ x))) e
        ∙ ⇔toPath to fro
        where
          fam : S → S
          fam x = layer n x (trᴾ x)

          to : ⟨ ⋁ S (λ u → (u ∈ˢ imageOn (supportᴮ n) fam) ⊓ (e ∈ˢ u)) ⟩
             → ⟨ ⋁ S (λ x → (x ∈ˢ supportᴮ n) ⊓ (e ∈ˢ fam x)) ⟩
          to = PT.rec PT.squash₁ (λ { (u , hu , he) →
                 PT.rec PT.squash₁
                   (λ { (x , hx , equ) →
                          ∣ x , hx , subst (λ t → ⟨ e ∈ˢ t ⟩) (≈ˢ→≡ equ) he ∣₁ })
                   (subst ⟨_⟩ (imageOn-spec (supportᴮ n) fam u) hu) })

          fro : ⟨ ⋁ S (λ x → (x ∈ˢ supportᴮ n) ⊓ (e ∈ˢ fam x)) ⟩
              → ⟨ ⋁ S (λ u → (u ∈ˢ imageOn (supportᴮ n) fam) ⊓ (e ∈ˢ u)) ⟩
          fro = PT.rec PT.squash₁ (λ { (x , hx , he) →
                  ∣ fam x
                  , subst ⟨_⟩ (sym (imageOn-spec (supportᴮ n) fam (fam x)))
                      ∣ x , hx , ≈ˢ-refl (fam x) ∣₁
                  , he ∣₁ })

-- The introduction rule, and the sentence the whole track exists to make
-- true: a B-weighted entry of n produces a poset entry of trᴾ n at EVERY
-- condition refining its weight, not at one of them.

      trᴾ-in : (n x b p : S) (hb : ⟨ b ∈ˢ B ⟩)
             → ⟨ entry x b ∈ˢ n ⟩ → ⟨ p ∈ˢ below (b , hb) ⟩
             → ⟨ entry (trᴾ x) p ∈ˢ trᴾ n ⟩
      trᴾ-in n x b p hb he hp =
        subst ⟨_⟩ (sym (trᴾ-layers n (entry (trᴾ x) p)))
          ∣ x , support-entryᴮ n x b hb he
            , subst ⟨_⟩ (sym (layer-spec n x (trᴾ x) (entry (trᴾ x) p)))
                ∣ p , inLayer , ≈ˢ-refl (entry (trᴾ x) p) ∣₁ ∣₁
        where
          hw : ⟨ b ∈ˢ weightsAt n x ⟩
          hw = weightsAt-in n x b hb he

          inLayer : ⟨ p ∈ˢ belowAt n x ⟩
          inLayer = subst ⟨_⟩ (sym (belowAt-spec n x p))
            ∣ b , ∣ hw , subst (λ t → ⟨ p ∈ˢ t ⟩)
                               (below-irr hb (weightsAt-sub n x b hw)) hp ∣₁ ∣₁

-- The elimination rule. Every member of trᴾ n comes from an entry of n, a
-- proof that its weight is Boolean, and a condition refining that weight.
-- Note what is NOT recoverable and is not claimed: which of the possibly many
-- weights of x in n the condition came from is not determined by the entry,
-- because the weight set is a set and not a function.

      trᴾ-out : (n e : S) → ⟨ e ∈ˢ trᴾ n ⟩
              → ⟨ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                     (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                        ⊓ (e ≈ˢ entry (trᴾ x) p)))))) ⟩
      trᴾ-out n e he = PT.rec (snd target) fromLayer
        (subst ⟨_⟩ (trᴾ-layers n e) he)
        where
          target : Ω
          target = ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                       (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                          ⊓ (e ≈ˢ entry (trᴾ x) p))))))

          fromLayer : Σ[ x ∈ S ] (⟨ x ∈ˢ supportᴮ n ⟩
                                  × ⟨ e ∈ˢ layer n x (trᴾ x) ⟩)
                    → ⟨ target ⟩
          fromLayer (x , _ , hl) = PT.rec (snd target) atCondition
            (subst ⟨_⟩ (layer-spec n x (trᴾ x) e) hl)
            where
              atCondition : Σ[ p ∈ S ] (⟨ p ∈ˢ belowAt n x ⟩
                                        × ⟨ e ≈ˢ entry (trᴾ x) p ⟩)
                          → ⟨ target ⟩
              atCondition (p , hp , eq) = PT.rec (snd target) atWeight
                (subst ⟨_⟩ (belowAt-spec n x p) hp)
                where
                  atWeight : Σ[ b ∈ S ] ⟨ ⋁ ⟨ b ∈ˢ weightsAt n x ⟩
                               (λ hb → p ∈ˢ below (b , weightsAt-sub n x b hb)) ⟩
                           → ⟨ target ⟩
                  atWeight (b , inner) = PT.rec (snd target)
                    (λ { (hw , hpb) →
                           ∣ x , ∣ b , ∣ weightsAt-sub n x b hw
                             , ∣ p , weightsAt-out n x b hw , hpb , eq ∣₁
                             ∣₁ ∣₁ ∣₁ })
                    inner

-- The entry law of section 1.9, in the corrected form. The architecture writes
-- the membership proof of the weight as an underscore inside a join over S;
-- there is nothing to solve that underscore with, because the proof lives in
-- ⟨ b ∈ˢ B ⟩. The join is taken at that type instead, which is legal since ⋁
-- accepts an arbitrary Type ℓ index. Track H reports the same repair at the
-- same signature (REPORT-H.md, section 3.3), and it is the third occurrence
-- of one architecture-wide mistake. The statement below is character for
-- character Track H's module Reverse parameter, so that track's
-- checkᴾ-is-reverse applies to it with no adapter.

      trᴾ-entries : (n e : S) → (e ∈ˢ trᴾ n)
                  ≡ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                       (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                          ⊓ (e ≈ˢ entry (trᴾ x) p))))))
      trᴾ-entries n e = ⇔toPath (trᴾ-out n e) fro
        where
          fro : ⟨ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                     (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                        ⊓ (e ≈ˢ entry (trᴾ x) p)))))) ⟩
              → ⟨ e ∈ˢ trᴾ n ⟩
          fro = PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (x , i1) →
                  PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (b , i2) →
                    PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (hb , i3) →
                      PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (p , he , hp , eq) →
                        subst (λ t → ⟨ t ∈ˢ trᴾ n ⟩) (sym (≈ˢ→≡ eq))
                              (trᴾ-in n x b p hb he hp) })
                      i3 }) i2 }) i1 })

-- The same law in the architecture's own join order, so that no consumer of
-- either form needs an adapter. The two differ by a PERMUTATION of two joins
-- and by nothing else: the corrected architecture (section 1.9) puts the
-- condition's join outside the weight-membership join, while Track H's landed
-- module Reverse, written before that correction, puts it inside. Joins
-- commute, so the two statements are equivalent, but they are different terms
-- and neither is definitionally the other. Shipping both costs twenty lines
-- and removes the choice from every later track.

      trᴾ-entries′ : (n e : S) → (e ∈ˢ trᴾ n)
                   ≡ ⋁ S (λ x → ⋁ S (λ b → ⋁ S (λ p → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb →
                        (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                           ⊓ (e ≈ˢ entry (trᴾ x) p))))))
      trᴾ-entries′ n e = ⇔toPath to fro
        where
          target′ : Ω
          target′ = ⋁ S (λ x → ⋁ S (λ b → ⋁ S (λ p → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb →
                        (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                           ⊓ (e ≈ˢ entry (trᴾ x) p))))))

          to : ⟨ e ∈ˢ trᴾ n ⟩ → ⟨ target′ ⟩
          to he = PT.rec (snd target′) (λ { (x , i1) →
                    PT.rec (snd target′) (λ { (b , i2) →
                      PT.rec (snd target′) (λ { (hb , i3) →
                        PT.rec (snd target′) (λ { (p , hen , hp , eq) →
                          ∣ x , ∣ b , ∣ p , ∣ hb , hen , hp , eq ∣₁ ∣₁ ∣₁ ∣₁ })
                        i3 }) i2 }) i1 })
                  (trᴾ-out n e he)

          fro : ⟨ target′ ⟩ → ⟨ e ∈ˢ trᴾ n ⟩
          fro = PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (x , i1) →
                  PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (b , i2) →
                    PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (p , i3) →
                      PT.rec (snd (e ∈ˢ trᴾ n)) (λ { (hb , hen , hp , eq) →
                        subst (λ t → ⟨ t ∈ˢ trᴾ n ⟩) (sym (≈ˢ→≡ eq))
                              (trᴾ-in n x b p hb hen hp) })
                      i3 }) i2 }) i1 })

-- The internalization contract, at trᴾ itself. Track D's F6 records that once
-- the tier-4 datum is in hand the internal image of a function already
-- defined is free, and this is that sentence: the image of a ground code
-- under trᴾ is imageOn and nothing more. Track H's correction 3.2, that
-- check-internal is at the entry map rather than at check, does not apply
-- here: the architecture's consumer of this record is the support law, which
-- takes the image of a set of SUBNAMES under trᴾ, so InternalImage trᴾ is the
-- object wanted.

      trᴾ-internal : InternalImage trᴾ
      trᴾ-internal = record { img = λ a → imageOn a trᴾ
                            ; img-spec = λ a z → imageOn-spec a trᴾ z }

      trᴾ-img : S → S
      trᴾ-img a = imageOn a trᴾ

--------------------------------------------------------------------------------
-- Validity: the translation of a B-name is a P-name
--------------------------------------------------------------------------------

-- The four name-predicate parameters are the seam between the two weight
-- carriers and they are the ONLY place the seam appears. IsNameᴮ and
-- child-is-nameᴮ are Track A's kernel at W = B; IsNameᴾ and entries-nameᴾ are
-- Track H's one validity lemma at W = carrier (StandardNames.agda:216), which
-- is itself Track A's name-intro plus the shape introduction. A consumer
-- supplies the four from the two instantiations and pays the extensionality
-- bridge once, as ProbeH2.agda does; nothing inside this module asks the two
-- kernels to be convertible.

      module Valid
        (IsNameᴮ        : S → Ω)
        (child-is-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n
                        → ⟨ IsNameᴮ x ⟩)
        (IsNameᴾ        : S → Ω)
        (entries-nameᴾ  : (n : S)
                        → ((e : S) → ⟨ e ∈ˢ n ⟩
                           → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
                               ((e ≡ entry x p)
                                × (⟨ p ∈ˢ carrier ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
                        → ⟨ IsNameᴾ n ⟩)
        where

-- The induction is on Child, which is where this differs from every validity
-- proof in Track H: the children of trᴾ n are the trᴾ x for x a child of n,
-- and those descend in the subname relation and in nothing else. The two
-- clauses of a name are discharged together by the listing: each member of
-- trᴾ n is an entry whose weight is a condition, by below-sub, and whose
-- first coordinate is a name, by the inductive hypothesis.

        trᴾ-name : (n : S) → ⟨ IsNameᴮ n ⟩ → ⟨ IsNameᴾ (trᴾ n) ⟩
        trᴾ-name = WFI.induction child-wf
                     {P = λ n → ⟨ IsNameᴮ n ⟩ → ⟨ IsNameᴾ (trᴾ n) ⟩} step
          where
            step : (n : S)
                 → ((x : S) → Child x n → ⟨ IsNameᴮ x ⟩ → ⟨ IsNameᴾ (trᴾ x) ⟩)
                 → ⟨ IsNameᴮ n ⟩ → ⟨ IsNameᴾ (trᴾ n) ⟩
            step n ih hn = entries-nameᴾ (trᴾ n) listing
              where
                Listing : S → Type ℓ
                Listing e = Σ[ x ∈ S ] Σ[ p ∈ S ]
                              ((e ≡ entry x p)
                               × (⟨ p ∈ˢ carrier ⟩ × ⟨ IsNameᴾ x ⟩))

                listing : (e : S) → ⟨ e ∈ˢ trᴾ n ⟩ → ∥ Listing e ∥₁
                listing e he = PT.rec PT.squash₁ (λ { (x , i1) →
                    PT.rec PT.squash₁ (λ { (b , i2) →
                      PT.rec PT.squash₁ (λ { (hb , i3) →
                        PT.rec PT.squash₁ (λ { (p , hen , hp , eq) →
                          ∣ trᴾ x , p , ≈ˢ→≡ eq
                            , below-sub (b , hb) p hp
                            , ih x (child-entry x b n hen)
                                 (child-is-nameᴮ n hn x (child-entry x b n hen))
                          ∣₁ })
                        i3 }) i2 }) i1 })
                  (trᴾ-out n e he)

--------------------------------------------------------------------------------
-- The support law, and why it is an inclusion
--------------------------------------------------------------------------------

-- N10, as a signature. below ⊥ᴮ is empty, because every i p is positive
-- (Certificate.agda:408) and the bottom of the completion has no members
-- (CodedCompletion.agda:528-529), so a bottom-weighted child emits NO entry
-- and disappears from the translated name. Stating the support law as an
-- equality unconditionally is therefore a FALSE theorem, and the honest
-- statement is an inclusion, with the equality available under an explicit
-- positivity hypothesis.
--
-- That is correct mathematics rather than a defect: a child that can never be
-- forced in should not appear as a condition. It also proves NON-CLAIM 4 in
-- the strong direction: trᴾ is not injective on any presentation with a
-- bottom, and K4 inherits an inclusion here, not an equality.
--
-- The three parameters are Track B's support at the POSET carrier. Note that
-- support-entryᴾ is the same shape as support-entryᴮ with carrier in place of
-- B; taking both flat is what keeps this file free of the cross-carrier
-- convertibility question.

      module Support
        (supportᴾ       : S → S)
        (support-outᴾ   : (m y : S) → ⟨ y ∈ˢ supportᴾ m ⟩ → Child y m)
        (support-entryᴾ : (m y p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ entry y p ∈ˢ m ⟩
                        → ⟨ y ∈ˢ supportᴾ m ⟩)
        where

-- The inclusion, and it needs NO name hypothesis. The architecture states it
-- under ⟨ B.IsName n ⟩; the hypothesis is not used, because the entry law
-- already carries the clause b ∈ B that the bare Child relation lacks, and
-- Track B's coded support carries the same clause on the poset side. A
-- consumer that has the name proof may of course still pass it and ignore it.

        trᴾ-support : (n : S) → ⟨ supportᴾ (trᴾ n) ⊆ˢ trᴾ-img (supportᴮ n) ⟩
        trᴾ-support n y hy =
          child-elim y (trᴾ n) (y ∈ˢ trᴾ-img (supportᴮ n))
            (support-outᴾ (trᴾ n) y hy) viaEntry
          where
            Q : Ω
            Q = y ∈ˢ trᴾ-img (supportᴮ n)

            viaEntry : (p : S) → ⟨ entry y p ∈ˢ trᴾ n ⟩ → ⟨ Q ⟩
            viaEntry p hp = PT.rec (snd Q) (λ { (x , i1) →
                PT.rec (snd Q) (λ { (b , i2) →
                  PT.rec (snd Q) (λ { (hb , i3) →
                    PT.rec (snd Q) (λ { (p' , hen , _ , eq) →
                      subst ⟨_⟩ (sym (imageOn-spec (supportᴮ n) trᴾ y))
                        ∣ x , support-entryᴮ n x b hb hen
                          , ≡→≈ˢ (fst (entry-inj (≈ˢ→≡ eq))) ∣₁ })
                    i3 }) i2 }) i1 })
              (trᴾ-out n (entry y p) hp)

-- The equality, under positivity. The hypothesis is stated at the WEIGHTS
-- occurring in n, which is a correction: the architecture writes it as
-- "(b : S) → ⟨ b ∈ˢ Bˢ.support n ⟩ → ⟨ positiveᴮ (b , _) ⟩", but Bˢ.support n
-- is the set of SUBNAMES of n and its members are names, not Boolean
-- elements, so that hypothesis is about the wrong objects. The corrected form
-- says what the proof needs and what the mathematics means: no entry of n is
-- weighted by something that can never be forced.
--
-- below-pos is the Cone module's theorem, taken here as a parameter so that
-- this module does not import the completion's order. It is the only place
-- positivity is used, and it is used to produce a TRUNCATED condition, never
-- a chosen one.
--
-- A WARNING ABOUT THE ARCHITECTURE'S CORRECTED FORM, which is not the same
-- defect as the underscore and is not repaired by repairing it. The corrected
-- section 1.9 now binds the membership proof properly and reads
--
--   ((b : S) (hb : ⟨ b ∈ˢ B ⟩) → ⟨ b ∈ˢ Bˢ.support n ⟩ → ⟨ positiveᴮ (b , hb) ⟩)
--
-- That statement is well formed and it is NOT sufficient, so the theorem
-- under it is false. Bˢ.support n is the set of SUBNAMES of n; its members
-- are names, and asking that a member of it also lie in B constrains no
-- WEIGHT of n at all. The conclusion needs a positive weight at every
-- subname, and nothing connects the two. A name whose only entry is a
-- bottom-weighted one at a subname that does not happen to lie in B satisfies
-- the hypothesis vacuously, has an inhabited Boolean support, and has an
-- EMPTY translation, because below ⊥ᴮ is empty; so the two sides of the
-- conclusion differ. The form shipped below quantifies over the weights
-- occurring in n, which is both what the proof consumes and what the
-- mathematics means.

        module Positive
          (positiveᴮ : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → Ω)
          (below-pos : (b : Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → ⟨ positiveᴮ b ⟩
                     → ⟨ ⋁ S (λ p → p ∈ˢ below b) ⟩)
          where

          trᴾ-support-eq : (n : S)
                         → ((x b : S) (hb : ⟨ b ∈ˢ B ⟩) → ⟨ entry x b ∈ˢ n ⟩
                            → ⟨ positiveᴮ (b , hb) ⟩)
                         → supportᴾ (trᴾ n) ≡ trᴾ-img (supportᴮ n)
          trᴾ-support-eq n pos =
            ext-path (λ z → ⇔toPath (trᴾ-support n z) (back z))
            where
              back : (z : S) → ⟨ z ∈ˢ trᴾ-img (supportᴮ n) ⟩
                   → ⟨ z ∈ˢ supportᴾ (trᴾ n) ⟩
              back z hz = PT.rec (snd (z ∈ˢ supportᴾ (trᴾ n)))
                (λ { (x , hx , eq) →
                       subst (λ t → ⟨ t ∈ˢ supportᴾ (trᴾ n) ⟩)
                             (sym (≈ˢ→≡ eq)) (inSupport x hx) })
                (subst ⟨_⟩ (imageOn-spec (supportᴮ n) trᴾ z) hz)
                where
                  inSupport : (x : S) → ⟨ x ∈ˢ supportᴮ n ⟩
                            → ⟨ trᴾ x ∈ˢ supportᴾ (trᴾ n) ⟩
                  inSupport x hx = PT.rec (snd (trᴾ x ∈ˢ supportᴾ (trᴾ n)))
                    atWeight (support-weightᴮ n x hx)
                    where
                      atWeight : Σ[ b ∈ S ] ⟨ b ∈ˢ weightsAt n x ⟩
                               → ⟨ trᴾ x ∈ˢ supportᴾ (trᴾ n) ⟩
                      atWeight (b , hw) =
                        PT.rec (snd (trᴾ x ∈ˢ supportᴾ (trᴾ n)))
                          (λ { (p , hp) →
                                 support-entryᴾ (trᴾ n) (trᴾ x) p
                                   (below-sub (b , hb) p hp)
                                   (trᴾ-in n x b p hb hen hp) })
                          (below-pos (b , hb) (pos x b hb hen))
                        where
                          hb : ⟨ b ∈ˢ B ⟩
                          hb = weightsAt-sub n x b hw

                          hen : ⟨ entry x b ∈ˢ n ⟩
                          hen = weightsAt-out n x b hw

--------------------------------------------------------------------------------
-- Closure and the bound on the translated support
--------------------------------------------------------------------------------

-- The roadmap's "set-code closure and bounds for the whole translated
-- support" (roadmap:169), read hereditarily. The image of a Child-closed
-- family of B-names under trᴾ is a Child-closed family of P-names, and it
-- bounds the translated support. The proof is one pass of the entry law: a
-- member of a member of the image is an entry, its weight is a condition by
-- below-sub, and its first coordinate is the translation of a child of a
-- member of the family, which the family contains.
--
-- Track C's ClosedFamily n is exactly the three arguments below, taken flat
-- in this track's discipline: C, its coded closure, and the containment of n.
-- No record is imported and the `valid` field is not needed, because Track C
-- already proves that coded closure implies validity and this file never
-- reads it.

        module Closure
          (coded-closed : (C : S) → ⟨ closedΔ B C ⟩ → (m : S) → ⟨ m ∈ˢ C ⟩
                        → (x : S) → Child x m → ⟨ x ∈ˢ C ⟩)
          where

          trᴾ-closed : (C : S) → ⟨ closedΔ B C ⟩
                     → ⟨ closedΔ carrier (trᴾ-img C) ⟩
          trᴾ-closed C cl m hm e he = PT.rec (snd goal) fromMember
            (subst ⟨_⟩ (imageOn-spec C trᴾ m) hm)
            where
              goal : Ω
              goal = ⋁ S (λ x → (x ∈ˢ trᴾ-img C) ⊓
                       (⋁ S (λ b → (b ∈ˢ carrier) ⊓ isKPairΔ e x b)))

              fromMember : Σ[ c ∈ S ] (⟨ c ∈ˢ C ⟩ × ⟨ m ≈ˢ trᴾ c ⟩)
                         → ⟨ goal ⟩
              fromMember (c , hc , eqm) = PT.rec (snd goal) fromEntry
                (trᴾ-out c e (subst (λ t → ⟨ e ∈ˢ t ⟩) (≈ˢ→≡ eqm) he))
                where
                  fromEntry : Σ[ x ∈ S ] ⟨ ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb →
                                ⋁ S (λ p → (entry x b ∈ˢ c)
                                     ⊓ ((p ∈ˢ below (b , hb))
                                        ⊓ (e ≈ˢ entry (trᴾ x) p))))) ⟩
                            → ⟨ goal ⟩
                  fromEntry (x , i1) = PT.rec (snd goal) (λ { (b , i2) →
                    PT.rec (snd goal) (λ { (hb , i3) →
                      PT.rec (snd goal) (λ { (p , hen , hp , eq) →
                        ∣ trᴾ x
                        , subst ⟨_⟩ (sym (imageOn-spec C trᴾ (trᴾ x)))
                            ∣ x , coded-closed C cl c hc x (child-entry x b c hen)
                              , ≈ˢ-refl (trᴾ x) ∣₁
                        , ∣ p , below-sub (b , hb) p hp
                          , subst (λ t → ⟨ isKPairΔ t (trᴾ x) p ⟩)
                                  (sym (≈ˢ→≡ eq)) (entry-isKPair (trᴾ x) p) ∣₁
                        ∣₁ })
                      i3 }) i2 }) i1

          trᴾ-closure : (C n : S) → ⟨ closedΔ B C ⟩ → ⟨ n ∈ˢ C ⟩
                      → Σ[ D ∈ S ] (⟨ closedΔ carrier D ⟩ × ⟨ trᴾ n ∈ˢ D ⟩)
          trᴾ-closure C n cl hn =
            trᴾ-img C , trᴾ-closed C cl ,
            subst ⟨_⟩ (sym (imageOn-spec C trᴾ (trᴾ n)))
              ∣ n , hn , ≈ˢ-refl (trᴾ n) ∣₁

          trᴾ-bound : (C n : S) (cl : ⟨ closedΔ B C ⟩) (hn : ⟨ n ∈ˢ C ⟩)
                    → ⟨ supportᴾ (trᴾ n) ⊆ˢ fst (trᴾ-closure C n cl hn) ⟩
          trᴾ-bound C n cl hn y hy =
            PT.rec (snd (y ∈ˢ trᴾ-img C))
              (λ { (x , hx , eq) →
                     subst ⟨_⟩ (sym (imageOn-spec C trᴾ y))
                       ∣ x , coded-closed C cl n hn x (support-outᴮ n x hx)
                         , eq ∣₁ })
              (subst ⟨_⟩ (imageOn-spec (supportᴮ n) trᴾ y)
                         (trᴾ-support n y hy))
