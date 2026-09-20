{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track E: the Boolean weight of a subname, as a join.
--
-- Section 1.8 of the K3 architecture. The mathematical question is Bell's
-- Definition 1.4 read in the other direction. Bell writes a Boolean-valued
-- set as a function u whose value u(x) is "the weight of x", and in a
-- functional presentation that is a definition. In a material presentation a
-- name is a ground code whose members are Kuratowski entries, the same
-- subname may occur at many entries with many different weights, and nothing
-- in the theory chooses one of them. So there is no function from a subname
-- to a weight to be had, and the object that does exist is the SET of
-- weights, Track B's weightsAt n x.
--
-- This file answers: what is the weight of a subname, if the weights form a
-- set? The answer is the join of that set inside the completion, and the
-- whole of the file is the statement that the join exists, that it is
-- characterized by its universal property, and that it does not depend on how
-- the set of weights is presented.
--
-- WHY THIS IS NOT THE FORBIDDEN WEIGHT MAP. weightᴮ n x is a total function
-- of two ground codes and this is not the object K0 forbade. The forbidden
-- object selects: it picks one weight out of weightsAt n x and calls it the
-- weight of the child, and that is a choice function on B, named as K3's
-- exact leak in the choice audit. weightᴮ n x selects nothing. It is above
-- every member of weightsAt n x and below every common upper bound of them,
-- which determines it uniquely without touching any member. THE FILE PROVES
-- NO THEOREM PUTTING weightᴮ n x INSIDE weightsAt n x, and no such theorem is
-- true: a join of two incomparable regular opens is neither of them. The one
-- case where the join does return a member is weightᴮ-single, where the
-- weight set has exactly one member up to the structure equality, and that is
-- a theorem about that hypothesis and not about names in general.
--
-- Track B's `weight` and this file's `weightᴮ` are therefore two different
-- objects and both are needed. `weight τ i` is indexed by an ENTRY of τ and
-- is a genuine function, because an entry decodes uniquely into a subname and
-- a weight. `weightᴮ n x` is indexed by a SUBNAME and is a join. The theorem
-- tying the two presentations is weightᴮ-entry: the weight carried by any
-- entry of τ is below the weight of the subname that entry decodes to. Its
-- converse, weightᴮ-least, says nothing larger works. Collapsing the two
-- presentations into one would reintroduce the selector.
--
-- THE SEAL. weightᴮ is a description-operator term: supᴮ is a Separation
-- inside the ambient power set, applied to a code that is itself a
-- Separation. It is sealed opaque in one block together with its
-- specification, which for a supremum is the pair of its two universal
-- properties, weightᴮ-upper and weightᴮ-lub. This is the correction banner's
-- rule, applied a priori as Track B applied it, and nothing below the block
-- ever unfolds the term: every consumer, including the join identity itself,
-- goes through the two universal properties and antisymmetry.
--
-- THE INDEX OF THE JOIN. The architecture indexes the admitted family by
-- Supᴺ (fst τ), the subnames of τ. That index is the wrong one and the
-- architecture's own join equation is what shows it: an admitted family over
-- Supᴺ (fst τ) would join to an element depending on τ alone, while
-- weightᴮ-join asserts the join is weightᴮ (fst τ) x at a FIXED x. The
-- correct index is the membership proposition of the weight family,
-- Σ[ b ∈ S ] ⟨ b ∈ˢ weightsAt n x ⟩, which is section 3.0's correction banner
-- read at this site: the bound variable of the join is a membership witness
-- and lives in the carrier of that proposition, not in S and not in a
-- different membership proposition. See section E2 of the report.
--
-- THE HOST-INDEX RULE. K2 has no hostSup and this file adds none. Every join
-- below is supᴮ of a ground code, and the one bridge to a host-indexed family
-- is AdmittedFamily, whose attainment field is exactly the hypothesis that
-- the host family's values are the members of a code. weightᴮ-admitted
-- supplies that hypothesis rather than assuming it.
--
-- THE SIGNATURE RULE, AND THE ONE PLACE THIS FILE PAID FOR IT. K2's Track F
-- measured that a declaration whose TYPE mentions a composite of two
-- constructed elements can fail to elaborate in bounded time, and that the
-- cost is in the signature and not in the proof term. That happened here, at
-- the last declaration of the file as first drafted, and the measurement is
-- recorded where the declaration would have stood. Every type that survives
-- mentions at most one constructed element of the completion and that one is
-- sealed: weightᴮ under its opaque block, weightsAt under Track B's. Nothing
-- below writes a meet, a join of two joins, a projection out of a constructed
-- record, or any Boolean operation applied to two constructed elements inside
-- a type.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedCompletion
import NameKernel
import NameSupport

module NameWeight {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module CC = CodedCompletion 𝒮
module NK = NameKernel 𝒮
module NS = NameSupport 𝒮

open OP using ( Extensionality; PowerSet; Separation )
open NK using ( Core; Sets; Accessibility )

-- Transport of membership along a path in the left argument. Track B names
-- the same helper for the same reason: every crossing between a decoded entry
-- and a member of a code rewrites the member and not the set.

mem-substˡ : {u v : S} → u ≡ v → {z : S} → ⟨ u ∈ˢ z ⟩ → ⟨ v ∈ˢ z ⟩
mem-substˡ p {z} = subst (λ w → ⟨ w ∈ˢ z ⟩) p


-- ---------------------------------------------------------------------
-- The completion, applied
-- ---------------------------------------------------------------------

-- This is the architecture's module application, with one telescope
-- correction. The architecture writes the header as
--
--   module NameWeight … (𝔓) (laws) (𝔊 : NameGround.Sets 𝒮) (pow) (acc) where
--     module K2 = CodedCompletion.Core 𝒮 ext pow sep paths 𝔓 laws
--
-- and never says where ext, sep and paths come from. Three of K2's six
-- parameters are already fields of the Sets tier: Extensionality and the path
-- realization sit in Core, Separation sits in Sets, and only PowerSet is new.
-- The layering below makes that visible rather than restating the three.
-- Over takes the six completion parameters flat, so the file can be read and
-- compiled with no name apparatus at all, and Weights below discharges four
-- of them from one tier record.

module Over (ext   : Extensionality)
            (pow   : PowerSet)
            (sep   : Separation)
            (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
            (𝔓     : CC.Presentation)
            (laws  : CC.Coded.ForcingLaws 𝔓)
            where

  module K2 = CC.Core ext pow sep paths 𝔓 laws

  open K2 using ( B; El; _≤ᴮ_; ≤ᴮ-refl; ≤ᴮ-antisym
                ; supᴮ; sup-upper; sup-least; ⊥ᴮ; ⊥ᴮ-empty )

  -- The structure equality realized as a host path, and its reflexivity. Both
  -- are one line from the realization hypothesis and neither is imported,
  -- because K2's Core opens its own copy without re-exporting it and Track B's
  -- copy sits behind a tier record this module does not take.

  ≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

  ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈ˢ-refl x = subst ⟨_⟩ (sym (paths x x)) refl

  -- -------------------------------------------------------------------
  -- The join
  -- -------------------------------------------------------------------

  -- The interface, and it is the whole of what the weight layer consumes from
  -- the support layer. Track B reported that the entry index needs no ground
  -- axiom and the support needs Tier 2; this module needs neither, because it
  -- never builds a ground set of its own. It takes the weight family as a
  -- given operation with its two laws and joins it.
  --
  -- Nothing here mentions IsName, Child, accessibility, the kernel's entry,
  -- or a name. The weight of a subname is defined for arbitrary ground codes,
  -- exactly as Track B's support is, and for the same reason: the recognizer
  -- must be free to ask about malformed codes. The name-level statements are
  -- instances, delivered in module Weights below.

  module Join
    (weightsAt      : S → S → S)                            -- NameSupport:622
    (weightsAt-sub  : (n x : S) → ⟨ weightsAt n x ⊆ˢ B ⟩)   -- :633
    (weightsAt-spec : (n x b : S)
                    → (b ∈ˢ weightsAt n x)
                    ≡ ((b ∈ˢ B) ⊓ NS.weightΔ n x b))        -- :625
    where

    -- The index of the join, and the correction of the architecture's Supᴺ.
    -- A weight of x in n is a MEMBER of weightsAt n x, so the family is
    -- indexed by the pairs of a code with a proof that it is such a member,
    -- and its value at such a pair is that code seen as an element of the
    -- completion. The subset law is what makes the value well formed, and it
    -- is the only use of that law outside the supremum itself.

    Wtᴺ : S → S → Type ℓ
    Wtᴺ n x = Σ[ b ∈ S ] ⟨ b ∈ˢ weightsAt n x ⟩

    wtVal : (n x : S) → Wtᴺ n x → El
    wtVal n x k = fst k , weightsAt-sub n x (fst k) (snd k)

    -- THE DEFINITION, SEALED WITH ITS SPECIFICATION. For a supremum the
    -- specification is the universal property and not a membership law: the
    -- underlying code of supᴮ X h is a double pseudocomplement of a union and
    -- reading its members is a fact about the regular-open calculus that no
    -- consumer of this file needs. The two properties below are what K4 will
    -- call, and they determine the element uniquely by antisymmetry.

    opaque
      weightᴮ : (n x : S) → El
      weightᴮ n x = supᴮ (weightsAt n x) (weightsAt-sub n x)

      weightᴮ-upper : (n x : S) (u : El) → ⟨ fst u ∈ˢ weightsAt n x ⟩
                    → ⟨ u ≤ᴮ weightᴮ n x ⟩
      weightᴮ-upper n x = sup-upper (weightsAt n x) (weightsAt-sub n x)

      weightᴮ-lub : (n x : S) (v : El)
                  → ((u : El) → ⟨ fst u ∈ˢ weightsAt n x ⟩ → ⟨ u ≤ᴮ v ⟩)
                  → ⟨ weightᴮ n x ≤ᴮ v ⟩
      weightᴮ-lub n x = sup-least (weightsAt n x) (weightsAt-sub n x)

    -- The upper bound in the form the object language produces it. Track B's
    -- weightΔ says "some member of n is the Kuratowski pair of x with b", and
    -- that is how every consumer will present a weight, since a consumer that
    -- has an entry in hand has it as a member of a code and not as a member of
    -- the separated weight family. The subset clause of the specification is
    -- supplied by the caller, because b being in the completion is not implied
    -- by b being a weight: Child is blind to the weight carrier and only the
    -- shape clause of IsName puts a weight inside B.

    weightᴮ-upperΔ : (n x b : S) (hb : ⟨ b ∈ˢ B ⟩) → ⟨ NS.weightΔ n x b ⟩
                   → ⟨ (b , hb) ≤ᴮ weightᴮ n x ⟩
    weightᴮ-upperΔ n x b hb w =
      weightᴮ-upper n x (b , hb)
        (subst ⟨_⟩ (sym (weightsAt-spec n x b)) (hb , w))

    weightᴮ-weight : (n x b : S) → ⟨ b ∈ˢ weightsAt n x ⟩ → ⟨ NS.weightΔ n x b ⟩
    weightᴮ-weight n x b h = snd (subst ⟨_⟩ (weightsAt-spec n x b) h)

    -- -----------------------------------------------------------------
    -- The admitted family
    -- -----------------------------------------------------------------

    -- K2 has no supremum of a host-indexed family and this file adds none.
    -- AdmittedFamily is the one legal bridge, and its attainment field is the
    -- hypothesis that the host family's values are exactly the members of a
    -- ground code. Here the code is the weight family itself and the
    -- attainment is a tautology in both directions: a member b is the value at
    -- the index (b , its own membership proof), and a value is a member by
    -- construction. Both directions are written out; neither is refl, because
    -- the two sides are different Ω-valued expressions and lesson 1 forbids
    -- closing such a gap with a bare congruence.

    weightᴮ-admitted : (n x : S) → K2.AdmittedFamily (wtVal n x)
    weightᴮ-admitted n x = record
      { values     = weightsAt n x
      ; values-sub = weightsAt-sub n x
      ; attained   = att }
      where
        att : (b : S) → (b ∈ˢ weightsAt n x)
                      ≡ ⋁ (Wtᴺ n x) (λ k → b ≈ˢ fst (wtVal n x k))
        att b = ⇔toPath fwd bwd
          where
            tgt : Ω
            tgt = ⋁ (Wtᴺ n x) (λ k → b ≈ˢ fst (wtVal n x k))

            fwd : ⟨ b ∈ˢ weightsAt n x ⟩ → ⟨ tgt ⟩
            fwd h = ∣ (b , h) , ≈ˢ-refl b ∣₁

            bwd : ⟨ tgt ⟩ → ⟨ b ∈ˢ weightsAt n x ⟩
            bwd = PT.rec (snd (b ∈ˢ weightsAt n x))
                    (λ { ((c , hc) , e) → mem-substˡ (sym (≈→≡ e)) hc })

    -- INDEPENDENCE OF THE PRESENTATION, which is the point the architecture
    -- makes by citing admitted-unique. A consumer that arrives with its own
    -- host index and its own enumeration of the weights of x in n gets the
    -- same element, and it gets it without any comparison of the two index
    -- types: the only hypothesis is that the enumeration's values are the
    -- members of weightsAt n x, and both elements are then squeezed between
    -- the same upper bounds. This is the statement that makes the weight an
    -- invariant of the name rather than of a chosen presentation of it, and
    -- it is why the join survives any later quotient of the completion.

    weightᴮ-presented : {I : Type ℓ} {val : I → El} (n x : S)
                      → (a : K2.AdmittedFamily val)
                      → ((b : S) → (b ∈ˢ weightsAt n x) ≡ ⋁ I (λ k → b ≈ˢ fst (val k)))
                      → K2.AdmittedFamily.join a ≡ weightᴮ n x
    weightᴮ-presented {I} {val} n x a att =
      ≤ᴮ-antisym (K2.AdmittedFamily.join a) (weightᴮ n x) up down
      where
        inW : (k : I) → ⟨ fst (val k) ∈ˢ weightsAt n x ⟩
        inW k = subst ⟨_⟩ (sym (att (fst (val k))))
                  ∣ k , ≈ˢ-refl (fst (val k)) ∣₁

        up : ⟨ K2.AdmittedFamily.join a ≤ᴮ weightᴮ n x ⟩
        up = K2.admitted-transfer a (weightᴮ n x)
               (λ k → weightᴮ-upper n x (val k) (inW k))

        down : ⟨ weightᴮ n x ≤ᴮ K2.AdmittedFamily.join a ⟩
        down = weightᴮ-lub n x (K2.AdmittedFamily.join a) step
          where
            step : (u : El) → ⟨ fst u ∈ˢ weightsAt n x ⟩
                 → ⟨ u ≤ᴮ K2.AdmittedFamily.join a ⟩
            step u hu = PT.rec (snd (u ≤ᴮ K2.AdmittedFamily.join a))
              (λ { (k , e) →
                     subst (λ w → ⟨ w ⊆ˢ fst (K2.AdmittedFamily.join a) ⟩)
                           (sym (≈→≡ e)) (K2.admitted-upper a k) })
              (subst ⟨_⟩ (att (fst u)) hu)

    -- The architecture's join identity, as an instance of independence rather
    -- than as a definitional coincidence. Both are available: the two sides
    -- are the same term once the seal is opened, since AdmittedFamily.join is
    -- supᴮ of the values field and the values field is the weight family. The
    -- proof below is the one that does not open the seal, and it is the one
    -- that survives if a later revision of the completion changes how a join
    -- is built.

    weightᴮ-join : (n x : S)
                 → K2.AdmittedFamily.join (weightᴮ-admitted n x) ≡ weightᴮ n x
    weightᴮ-join n x =
      weightᴮ-presented n x (weightᴮ-admitted n x)
        (K2.AdmittedFamily.attained (weightᴮ-admitted n x))

    -- -----------------------------------------------------------------
    -- The two extreme cases
    -- -----------------------------------------------------------------

    -- A subname with no weights has weight zero. This is the material reading
    -- of Bell's convention that u(x) is the bottom of B for x outside the
    -- domain of u, and here it is a theorem rather than a convention, because
    -- the domain is not part of the datum: weightsAt n x is defined for every
    -- pair of codes and is simply empty when x occurs in no entry of n. It is
    -- also the fact behind measured negative N10, that a bottom-weighted child
    -- drops out of the reverse translation.
    --
    -- The negation is spelled with the algebra's own bottom, never with the
    -- library's, which is lesson 3 of the shared preamble.

    weightᴮ-zero : (n x : S) → ((b : S) → ⟨ b ∈ˢ weightsAt n x ⟩ → ⟨ ⊥ ⟩)
                 → weightᴮ n x ≡ ⊥ᴮ
    weightᴮ-zero n x empty =
      ≤ᴮ-antisym (weightᴮ n x) ⊥ᴮ
        (weightᴮ-lub n x ⊥ᴮ (λ u hu → Empty.rec* (empty (fst u) hu)))
        (λ z hz → Empty.rec* (⊥ᴮ-empty z hz))

    -- A subname whose weights are all one code has that code as its weight.
    -- This is the only sense in which the join ever returns a member of the
    -- family, and the hypothesis is what does it: the uniqueness clause, not
    -- the existence clause. Check names are the consumer. A check name carries
    -- each of its children at the single weight ⊤ᴮ, so its weight family is a
    -- singleton up to the structure equality and this lemma computes the
    -- weight without opening the completion at all.

    weightᴮ-single : (n x : S) (u : El)
                   → ⟨ fst u ∈ˢ weightsAt n x ⟩
                   → ((c : S) → ⟨ c ∈ˢ weightsAt n x ⟩ → ⟨ c ≈ˢ fst u ⟩)
                   → weightᴮ n x ≡ u
    weightᴮ-single n x u hu uniq =
      ≤ᴮ-antisym (weightᴮ n x) u
        (weightᴮ-lub n x u
          (λ w hw → subst (λ z → ⟨ z ⊆ˢ fst u ⟩)
                          (sym (≈→≡ (uniq (fst w) hw))) (≤ᴮ-refl u)))
        (weightᴮ-upper n x u hu)


-- ---------------------------------------------------------------------
-- The name layer
-- ---------------------------------------------------------------------

-- Everything above is about codes. This module instantiates the weight
-- carrier at the completion, W := B, which is the only instantiation section
-- 1.8 asks for, and states the name-level facts.
--
-- The accessibility datum appears here and nowhere above, and it appears for
-- the reason Track B recorded: it is needed to BUILD the kernel, not to build
-- a support and not to build a join. Nothing in this file recurses on Child.
-- The architecture's permitted-hypothesis list for this track reads "B
-- interface plus K2.Core", and the audit of the telescope is that the
-- mathematics of module Join needs neither accessibility nor Pairing nor
-- Union; those three enter only through the instantiation, which exists so
-- that the weight of a subname is stated against Track A's names and Track B's
-- support rather than against a restatement of them.

module Weights (𝔊    : Sets)
               (pow  : PowerSet)
               (acc∈ : Accessibility)
               (𝔓    : CC.Presentation)
               (laws : CC.Coded.ForcingLaws 𝔓)
               where

  open Sets 𝔊 using ( core; hasSeparation )
  open Core core using ( extensional; ≈ˢ-paths )

  module O  = Over extensional pow hasSeparation ≈ˢ-paths 𝔓 laws
  module K2 = O.K2

  -- The weight carrier is the completion. This one line is the whole of
  -- "only at W = B" in section 1.8, and it is why the weight family's subset
  -- law has exactly the type supᴮ demands, with no coercion anywhere.

  module NSI = NS.Instantiate 𝔊 acc∈ K2.B
  module J   = O.Join NSI.BG.weightsAt NSI.BG.weightsAt-sub NSI.BG.weightsAt-spec

  open NSI.K  using ( entry; entry-isKPair )
  open NSI.B  using ( Name; Index; child; weight; represents )
  open NSI.BG using ( support; support-is-join; kpair-unique; weightsAt )

  open J public using
    ( Wtᴺ; wtVal; weightᴮ; weightᴮ-upper; weightᴮ-lub; weightᴮ-upperΔ
    ; weightᴮ-weight; weightᴮ-admitted; weightᴮ-presented; weightᴮ-join
    ; weightᴮ-zero; weightᴮ-single )

  -- The upper bound in the architecture's own form, with a literal entry of
  -- the code in place of the coded weight predicate. One step: the kernel's
  -- entry satisfies the Kuratowski predicate, which is Track A's entry-isKPair
  -- and the same fact Track B spends twice.

  weightᴮ-ub : (n x b : S) → ⟨ entry x b ∈ˢ n ⟩ → (hb : ⟨ b ∈ˢ K2.B ⟩)
             → ⟨ (b , hb) K2.≤ᴮ J.weightᴮ n x ⟩
  weightᴮ-ub n x b h hb =
    J.weightᴮ-upperΔ n x b hb ∣ entry x b , (h , entry-isKPair x b) ∣₁

  -- Its converse, and the pair is a complete characterization of the weight
  -- in entry terms: weightᴮ n x is the least element of the completion above
  -- every b for which entry x b is a member of n. Going back from the coded
  -- weight predicate to a literal entry is where extensionality is spent, via
  -- Track B's kpair-unique; a Δ₀ formula can say that some member of n is the
  -- Kuratowski pair of x with b, and only uniqueness turns that member into
  -- the kernel's term.

  weightᴮ-least : (n x : S) (v : K2.El)
                → ((b : S) (hb : ⟨ b ∈ˢ K2.B ⟩) → ⟨ entry x b ∈ˢ n ⟩
                   → ⟨ (b , hb) K2.≤ᴮ v ⟩)
                → ⟨ J.weightᴮ n x K2.≤ᴮ v ⟩
  weightᴮ-least n x v ub = J.weightᴮ-lub n x v step
    where
      step : (u : K2.El) → ⟨ fst u ∈ˢ weightsAt n x ⟩ → ⟨ u K2.≤ᴮ v ⟩
      step u hu = PT.rec (snd (u K2.≤ᴮ v))
        (λ { (e , he , hk) →
               ub (fst u) (snd u)
                 (mem-substˡ (kpair-unique e x (fst u) hk) he) })
        (J.weightᴮ-weight n x (fst u) hu)

  -- THE THEOREM TYING THE TWO PRESENTATIONS, and the reason both may exist
  -- without one being a selector. Track B's weight is a function on the ENTRY
  -- index: an entry of τ decodes uniquely into a subname and a weight, and
  -- that decoding is injectivity of the kernel's entry with no choice in it.
  -- This file's weightᴮ is a function on SUBNAMES and is a join. The theorem
  -- is that the first is always below the second, at the subname the entry
  -- decodes to.
  --
  -- Read the other way it says what would go wrong with a selector. If some
  -- map sent a subname to one of its entry weights, then by this theorem and
  -- weightᴮ-least the selected weight would have to be the join, hence a
  -- greatest element of the weight family; a name with two incomparable
  -- weights on one subname has no such element, so the selector cannot exist.
  -- Two entries carrying the same subname at different weights are exactly the
  -- configuration that separates the two presentations, and nothing in the
  -- theory rules that configuration out.

  weightᴮ-entry : (τ : Name) (i : Index τ)
                → ⟨ weight τ i K2.≤ᴮ J.weightᴮ (fst τ) (fst (child τ i)) ⟩
  weightᴮ-entry τ i =
    weightᴮ-ub (fst τ) (fst (child τ i)) (fst (weight τ i))
      (mem-substˡ (represents τ i) (snd i)) (snd (weight τ i))

  -- The support, and the zero weight outside it. Track B's support-is-join
  -- says a subname is in the support exactly when its weight family is
  -- inhabited, so a code outside the support has an empty weight family and
  -- weightᴮ-zero applies. This is the material statement of "a name assigns
  -- weight zero to everything it does not mention", with no domain field and
  -- no convention.

  weightᴮ-out : (n x : S) → (⟨ x ∈ˢ support n ⟩ → ⟨ ⊥ ⟩)
              → J.weightᴮ n x ≡ K2.⊥ᴮ
  weightᴮ-out n x out =
    J.weightᴮ-zero n x
      (λ b hb → out (subst ⟨_⟩ (sym (support-is-join n x)) ∣ b , hb ∣₁))

  -- THE ONE DECLARATION THIS TRACK COULD NOT WRITE, MEASURED.
  --
  -- Section 1.8 states the admitted family and the join identity at a name,
  --
  --   weightᴮ-admitted : (τ : Name) (x : S) → AdmittedFamily {I = …} …
  --   weightᴮ-join     : (τ : Name) (x : S)
  --                    → AdmittedFamily.join (weightᴮ-admitted τ x)
  --                    ≡ weightᴮ (fst τ) x
  --
  -- and the second of those two declarations does not elaborate in bounded
  -- time at this layer. Its TYPE mentions AdmittedFamily.join applied to a
  -- constructed record whose values field is a constructed code, which is K2
  -- Track F's measured shape F9 exactly: a composite of two constructed
  -- elements in a signature rather than in a term. The figures are in the
  -- report; the same statement inside module Join, where the weight family is
  -- a module variable, is proved above and costs nothing.
  --
  -- K2's standing order is to abstract the composite into a variable together
  -- with a splitting hypothesis, and the abstracted form is already the more
  -- general theorem: weightᴮ-presented takes the family as a variable and the
  -- attainment as the hypothesis that ties its values to the weight family,
  -- and weightᴮ-join is its instance. Both are re-exported above, so a
  -- consumer holding a name τ calls them at fst τ. Nothing is lost: neither
  -- statement uses the name predicate for anything, since the weight of a
  -- subname is a fact about the code fst τ and not about its well-formedness,
  -- and the code-level form is strictly the more general of the two.
