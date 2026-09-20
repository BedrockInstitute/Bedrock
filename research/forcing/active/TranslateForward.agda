{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track F: the forward translation, from poset names to Boolean names.
--
-- Section 1.9 of the K3 architecture, forward half. The mathematical
-- question is Bell's relabelling read in a material presentation. A P-name
-- is a ground code whose members are weighted entries, each entry pairing a
-- subname code with a CONDITION; the completion embedding i carries a
-- condition to an element of the Boolean algebra; and the forward
-- translation trᴮ is the name obtained by relabelling every weight along i
-- and translating every subname recursively. Nothing is added and nothing is
-- dropped: one entry of n becomes exactly one entry of trᴮ n, because i is a
-- total function on conditions.
--
-- WHY THE TRANSLATION IS A RECURSION AND WHAT THAT COSTS. The relabelling
-- cannot be a Separation or an image of a single set, because the value at n
-- mentions the value at the subnames of n. It is a host recursion on the
-- subname relation Child, and its step must turn the values on the children
-- into a ground code. Track D measured exactly what that needs and its
-- finding F8 asks this track the question before it starts. The answer is
-- recorded in section 2 below and it is one datum: tier 4 MemberImage.
--
-- WHAT IS NOT CLAIMED, copied from the architecture's non-claims list of
-- section 1.9 and kept here because a reader of this file is the person most
-- likely to assume one of them.
--
--   1. No raw round trip in either order. trᴾ (trᴮ n) is not n and no
--      theorem here says otherwise. below (i q) is the regularized cone and
--      not the set of refinements of q.
--   2. No denotational round trip. That is K4 and K5 work and it consumes
--      K2's `recover`, which this file neither restates nor reproves.
--   3. No quotient of names, by Boolean equality or by anything else.
--   4. No injectivity, surjectivity or order reflection for trᴮ. The
--      embedding i carries no injectivity field and never will, so two
--      distinct conditions may receive the same Boolean weight and two
--      distinct P-names may translate to one B-name. The support law below
--      is an equality in spite of that, and section 4 says why.
--   5. No normalization of weights to a function. The weight of a subname
--      stays the SET weightsAt n x throughout, and the translated weight set
--      is its pointwise image under i.
--   6. No selector from the Boolean algebra back to the conditions, and no
--      truncation eliminated into the conditions. Nothing in this file needs
--      one, because the forward direction is the functional one.
--   7. The relabelling recursion is not the value recursion. Bell 1.15 and
--      1.16 recurse on PAIRS with both coordinates descending; that kernel is
--      Track A's RawPairRec and Track I's business, and it is not used here.
--
-- THE TWO PROJECT LEVEL RULES, and how this file obeys them.
--
-- The first rule seals every description operator term with its
-- specification. This file contains NO description operator term at all.
-- Every ground code former it uses (entry, image, unionOf, support,
-- weightsAt, supportᴮ, iCode) is a module parameter, and a parameter is a
-- variable with no unfolding, which is a tighter seal than an opaque block.
-- trᴮ itself is a WFI.induction spine over the variable child-wf and is
-- likewise stuck. This is Track H's section 4 situation reproduced, and it is
-- deliberate rather than accidental: it is the reason the parameter lists
-- below are long.
--
-- The second rule keeps a construction of one layer applied to a term of
-- another out of TYPES, and prescribes abstracting the composite into a
-- variable with a splitting hypothesis. Every type in this file is already in
-- the abstracted form, for the same reason: the K2 side enters only as the
-- variable iCode applied to a bound condition, and the K3 side enters only as
-- stuck spines. There is no meet, join or supremum of a constructed element
-- anywhere in a signature here, so the shape that was killed three times in
-- K2's completion track and twice in K3's weight track does not arise.
--
-- THE CROSS CARRIER MEASUREMENT, which is about this track specifically.
-- Track H measured that Track A's kernel at two weight carriers does not
-- share entry, Child, Entryᴺ or Shape definitionally, because entry is built
-- from the sealed pairOf and pairOf sits inside a module telescope carrying
-- W. Unsealing is not a repair: that run was killed, reproducing Track A's
-- own 761 s figure. Track H warned that a translation crosses the carriers at
-- every entry rather than at one module boundary, so the cost had to be
-- budgeted from the first line. It is budgeted here structurally: this file
-- takes ONE entry and ONE Child as parameters, because both are weight
-- independent, and lets the two carriers differ only where they genuinely
-- differ, in the name predicate, the support and the weight family. The
-- twenty line bridge of ProbeH2 is then paid once, in ProbeF.agda, at the
-- instantiation site, and it does not appear in any theorem below.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module TranslateForward {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

-- ---------------------------------------------------------------------
-- Track D's contract, restated
-- ---------------------------------------------------------------------

-- Track D's InternalImage is restated here rather than imported, for the
-- reason Track H gave when it restated the same record in eight lines: a
-- record TYPE is not an inhabitant, so importing the module buys nothing a
-- consumer can use, while it does buy a compile dependency. The text below
-- is Track D's own (NameImage.agda:86, :97) character for character, so that
-- a consumer holding one record holds the other; ProbeF.agda checks that by
-- transporting the inhabitant built here into Track D's record.

ImageClass : (S → S) → S → S → Ω
ImageClass f a z = ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))

record InternalImage (f : S → S) : Type (ℓ-suc ℓ) where
  field
    img      : S → S
    img-spec : (a z : S) → (z ∈ˢ img a) ≡ ImageClass f a z

-- A join over the proofs of a proposition, at a family that ignores the
-- proof, is the meet with that proposition. This is the only content of
-- Track D's member→image and it is the shape that turns tier 4's member
-- indexed image into an ordinary image. Preamble lesson 1 applies at exactly
-- this declaration and is met the preamble's way: the two endpoints of
-- ⇔toPath are named by the written out signature, so neither isProp half is
-- ever a metavariable.

∃-prop : (P Q : Ω) → (⋁ ⟨ P ⟩ (λ _ → Q)) ≡ (P ⊓ Q)
∃-prop P Q = ⇔toPath
  (PT.rec (snd (P ⊓ Q)) (λ { (h , q) → h , q }))
  (λ { (h , q) → ∣ h , q ∣₁ })

-- ---------------------------------------------------------------------
-- Track A's kernel, weight independent
-- ---------------------------------------------------------------------

-- Nine parameters, all of Track A's and all of them weight INDEPENDENT.
-- That independence is Track A's own design point, stated in its source: the
-- subname relation never mentions W, so a Boolean weighted name and a poset
-- weighted name have the same children, the same descent and the same
-- recursor. It is what lets this file take one entry and one Child rather
-- than two of each, and it is therefore what keeps Track H's cross carrier
-- cost out of the theorems.

module Kernel
  (entry          : S → S → S)                              -- NameKernel:253
  (entry-inj      : {x b y c : S} → entry x b ≡ entry y c
                  → (x ≡ y) × (b ≡ c))                                -- :321
  (Child          : S → S → Type ℓ)                                   -- :368
  (isPropChild    : (x n : S) → isProp (Child x n))                   -- :371
  (child-entry    : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)     -- :369
  (child-weight   : (x n : S) → Child x n
                  → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)               -- :369
  (child-wf       : WellFounded Child)                                -- :392
  (≈ˢ-paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (ext-path       : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  where

  -- The structure's own equality is a field into Ω and is not host path
  -- equality by definition. The realization hypothesis makes the two
  -- interchangeable, and every crossing below goes through one of these three
  -- lines. Extensionality enters only through ext-path and is spent at
  -- exactly one theorem, the support law of section 4.

  ≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈→≡ {x} {y} = subst ⟨_⟩ (≈ˢ-paths x y)

  ≡→≈ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
  ≡→≈ {x} {y} = subst ⟨_⟩ (sym (≈ˢ-paths x y))

  ≈-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈-refl x = ≡→≈ refl

  mem-subst : {u v : S} → u ≡ v → {z : S} → ⟨ z ∈ˢ u ⟩ → ⟨ z ∈ˢ v ⟩
  mem-subst p {z} = subst (λ w → ⟨ z ∈ˢ w ⟩) p

  -- ---------------------------------------------------------------------
  -- The two set existence data the translation consumes
  -- ---------------------------------------------------------------------

  -- Tier 4 and the Union half of tier 2. Section 2 of this track's report
  -- argues that the first is a genuine widening of the granted parameter list
  -- and that the second is not.

  module Weighted
    (image        : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S)
    (image-spec   : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
                  → (z ∈ˢ image a f)
                  ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))))
    (unionOf      : S → S)
    (unionOf-spec : (t z : S) → (z ∈ˢ unionOf t)
                  ≡ ⋁ S (λ u → (u ∈ˢ t) ⊓ (z ∈ˢ u)))
    where

    -- The one combination of the two data that the construction below needs.
    -- A member of the union of an image is a member of one of the image's
    -- values, and conversely, and the ≈ˢ that the image specification emits
    -- is discharged here once rather than at every use. Everything downstream
    -- reads the translated name through this lemma and through image-spec,
    -- and never through unionOf-spec directly.

    union-image : (a : S) (g : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
                → (z ∈ˢ unionOf (image a g))
                ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ∈ˢ g (x , h)))
    union-image a g z = unionOf-spec (image a g) z ∙ ⇔toPath fwd bwd
      where
        source : Ω
        source = ⋁ S (λ u → (u ∈ˢ image a g) ⊓ (z ∈ˢ u))

        target : Ω
        target = ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ∈ˢ g (x , h)))

        fwd : ⟨ source ⟩ → ⟨ target ⟩
        fwd = PT.rec (snd target)
          (λ { (u , hu , hz) → PT.rec (snd target)
            (λ { (x , inner) → PT.rec (snd target)
              (λ { (h , heq) → ∣ x , ∣ h , mem-subst (≈→≡ heq) hz ∣₁ ∣₁ })
              inner })
            (subst ⟨_⟩ (image-spec a g u) hu) })

        bwd : ⟨ target ⟩ → ⟨ source ⟩
        bwd = PT.rec (snd source)
          (λ { (x , inner) → PT.rec (snd source)
            (λ { (h , hz) →
                   ∣ g (x , h)
                   , subst ⟨_⟩ (sym (image-spec a g (g (x , h))))
                       ∣ x , ∣ h , ≈-refl (g (x , h)) ∣₁ ∣₁
                   , hz ∣₁ })
            inner })

    -- Tier 4 internalizes any host function on the carrier, because a host
    -- function on the carrier is in particular a host function on the members
    -- of a code. This is Track D's member→image, restated for the same reason
    -- the contract record is restated, and its only content is ∃-prop.

    internalize : (f : S → S) → InternalImage f
    internalize f = record
      { img      = λ a → image a (λ q → f (fst q))
      ; img-spec = λ a z → image-spec a (λ q → f (fst q)) z
                         ∙ cong (⋁ S) (funExt (λ x → ∃-prop (x ∈ˢ a) (z ≈ˢ f x))) }

    -- ---------------------------------------------------------------------
    -- The source layer: poset weighted names
    -- ---------------------------------------------------------------------

    -- Track B's support and weight family at W = carrier, together with
    -- Track A's name predicate at the same carrier. The four support and
    -- weight laws are stated in HOST form, as entry membership rather than as
    -- the coded readings childΔ and weightΔ, for two reasons. They are what
    -- the proofs below actually consume, so stating them this way makes the
    -- ledger exact; and they keep CodedVocabulary out of this file entirely,
    -- so no formula, no Δ₀ witness and no evaluator appears here.
    --
    -- Note which of Track A's name laws is ABSENT. The shape clause of
    -- IsNameᴾ is not a parameter, because nothing below ever asks what a
    -- member of the SOURCE name looks like: the construction reads the source
    -- only through support and weightsAt, both of which are total and both of
    -- which already carry the entry decomposition. Only the hereditary clause
    -- is needed, and only to feed the induction of section 3.

    module Source
      (carrier        : S)
      (IsNameᴾ        : S → Ω)
      (child-is-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n
                      → ⟨ IsNameᴾ x ⟩)
      (support        : S → S)
      (supp-in        : (n x p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ entry x p ∈ˢ n ⟩
                      → ⟨ x ∈ˢ support n ⟩)
      (supp-out       : (n x : S) → ⟨ x ∈ˢ support n ⟩
                      → ∥ Σ[ p ∈ S ] (⟨ p ∈ˢ carrier ⟩ × ⟨ entry x p ∈ˢ n ⟩) ∥₁)
      (weightsAt      : S → S → S)
      (weights-sub    : (n x p : S) → ⟨ p ∈ˢ weightsAt n x ⟩ → ⟨ p ∈ˢ carrier ⟩)
      (weights-in     : (n x p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ entry x p ∈ˢ n ⟩
                      → ⟨ p ∈ˢ weightsAt n x ⟩)
      (weights-out    : (n x p : S) → ⟨ p ∈ˢ weightsAt n x ⟩
                      → ⟨ entry x p ∈ˢ n ⟩)
      where

      -- A condition, spelled out. CodedCompletion is not read by this file,
      -- so Cond is written as the Σ-type it is; section 1.0's correction 2
      -- records that Pt carrier and Cond are the same type, so no coercion
      -- stands between this and K2's own signature for i.

      Cond : Type ℓ
      Cond = Σ[ p ∈ S ] ⟨ p ∈ˢ carrier ⟩

      -- Track B's support-out, derived rather than assumed. The entry that
      -- witnesses membership in the support is truncated, but the conclusion
      -- is a proposition, so the truncation may be removed. This is what the
      -- recursion below descends along, and it is the only place where the
      -- recursion learns that the members of the support really are children.

      support-child : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n
      support-child n x hx = PT.rec (isPropChild x n)
        (λ { (p , _ , hen) → child-entry x p n hen }) (supp-out n x hx)

      -- Closure of a ground code under subnames, in Track C's host sense.
      -- Track C's ClosedFamily carries a coded closure condition and derives
      -- this from it; this file takes the derived form, because it is the only
      -- part of a closed family the closure theorem of section 5 consumes.

      Closedᴴ : S → Type ℓ
      Closedᴴ C = (m : S) → ⟨ m ∈ˢ C ⟩ → (x : S) → Child x m → ⟨ x ∈ˢ C ⟩

      -- ---------------------------------------------------------------------
      -- The target layer and the embedding
      -- ---------------------------------------------------------------------

      -- The Boolean side of Track A and Track B, plus Track C's coded closure
      -- predicate at the Boolean carrier, plus the two components of K2's
      -- embedding i that the forward translation actually uses.
      --
      -- WHAT IS NOT TAKEN, and this is a measured over-declaration in the
      -- brief rather than a defect. Section 3 grants Track F "i, i-mono,
      -- i-pos". Monotonicity and positivity are used nowhere in the forward
      -- direction: relabelling a weight needs only that the relabelled weight
      -- is a Boolean element, and the entry law, the name law, the support law
      -- and the closure law all go through with i an arbitrary function from
      -- conditions to Boolean elements. They are Track G's, where below-pos is
      -- proved from i-dense and where below ⊥ᴮ being empty is what makes the
      -- reverse support law an inclusion. This is the same finding Track H
      -- reported for its own grant of i, at a different place.

      module Target
        (B             : S)
        (IsNameᴮ       : S → Ω)
        (name-introᴮ   : (n : S)
                       → ((e : S) → ⟨ e ∈ˢ n ⟩
                          → ∥ Σ[ y ∈ S ] Σ[ b ∈ S ]
                                (e ≡ entry y b) × ⟨ b ∈ˢ B ⟩ ∥₁)
                       → ((y : S) → Child y n → ⟨ IsNameᴮ y ⟩)
                       → ⟨ IsNameᴮ n ⟩)
        (supportᴮ      : S → S)
        (suppᴮ-in      : (n y b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ entry y b ∈ˢ n ⟩
                       → ⟨ y ∈ˢ supportᴮ n ⟩)
        (suppᴮ-out     : (n y : S) → ⟨ y ∈ˢ supportᴮ n ⟩
                       → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ entry y b ∈ˢ n ⟩) ∥₁)
        (closedᴮ       : S → Ω)
        (closedᴮ-intro : (D : S)
                       → ((m : S) → ⟨ m ∈ˢ D ⟩ → (e : S) → ⟨ e ∈ˢ m ⟩
                          → ∥ Σ[ y ∈ S ] Σ[ b ∈ S ]
                                (⟨ y ∈ˢ D ⟩ × ⟨ b ∈ˢ B ⟩ × (e ≡ entry y b)) ∥₁)
                       → ⟨ closedᴮ D ⟩)
        (iCode         : Cond → S)
        (i∈B           : (q : Cond) → ⟨ iCode q ∈ˢ B ⟩)
        where

        -- ---------------------------------------------------------------------
        -- 1. The host half: trᴮ as a total function
        -- ---------------------------------------------------------------------

        -- The translated entries carried by ONE subname. The weights of x in
        -- n form a set, never a single weight, so the subname contributes a
        -- LAYER rather than an entry: the pointwise image of weightsAt n x
        -- under i, paired with the translated subname. This is the point at
        -- which K0's ruling that there is no weight function is paid for, and
        -- it is why the step needs a union.
        --
        -- The membership proof that iCode demands is supplied by
        -- weights-sub, so the layer is a function of the pair (p , proof) and
        -- not of p alone. It does not depend on WHICH proof, since membership
        -- is a proposition, and the one place where that has to be said out
        -- loud is the backward half of the entry law below.

        layerAt : (n x y : S) → S
        layerAt n x y =
          image (weightsAt n x)
            (λ r → entry y (iCode (fst r , weights-sub n x (fst r) (snd r))))

        -- The recursion step. Take the support, translate each subname by the
        -- inductive hypothesis, spread it over its own translated weight set,
        -- and glue the layers. Nothing here asks whether n is a name: support
        -- and weightsAt are total, by Track B's design, so trᴮ is total and
        -- the entry law below carries no name hypothesis.

        trStep : (n : S) → ((x : S) → Child x n → S) → S
        trStep n IH =
          unionOf (image (support n)
            (λ q → layerAt n (fst q) (IH (fst q) (support-child n (fst q) (snd q)))))

        -- The recursion itself. Well-foundedness of Child is Track A's
        -- child-wf, which Track A derives from tier 0 accessibility of the
        -- ground's membership; taking it here is how tier 0 enters this
        -- track's ledger. The computation law is PROPOSITIONAL, as all host
        -- well-founded recursion is, so every consumer rewrites along
        -- trᴮ-host rather than expecting the term to compute.

        trᴮ : S → S
        trᴮ = WFI.induction child-wf {P = λ _ → S} trStep

        trᴮ-host : (n : S) → trᴮ n ≡ trStep n (λ x _ → trᴮ x)
        trᴮ-host = WFI.induction-compute child-wf {P = λ _ → S} trStep

        -- ---------------------------------------------------------------------
        -- 2. The entry law
        -- ---------------------------------------------------------------------

        -- The membership statement of the translated name, first in the shape
        -- the construction hands over and then in the shape the architecture
        -- asks for. Splitting it in two is not bookkeeping: the first half is
        -- three rewrites along specifications with no mathematical content,
        -- and the second half is the one genuine step, namely that ranging
        -- over the support and then over a weight of that subname is the same
        -- as ranging over the entries of n outright.

        RawClass : (n e : S) → Ω
        RawClass n e =
          ⋁ S (λ x → ⋁ ⟨ x ∈ˢ support n ⟩ (λ hx →
            ⋁ S (λ p → ⋁ ⟨ p ∈ˢ weightsAt n x ⟩ (λ hp →
              e ≈ˢ entry (trᴮ x) (iCode (p , weights-sub n x p hp))))))

        trᴮ-raw : (n e : S) → (e ∈ˢ trᴮ n) ≡ RawClass n e
        trᴮ-raw n e =
            cong (λ t → e ∈ˢ t) (trᴮ-host n)
          ∙ union-image (support n) (λ q → layerAt n (fst q) (trᴮ (fst q))) e
          ∙ cong (⋁ S) (funExt (λ x →
              cong (⋁ ⟨ x ∈ˢ support n ⟩) (funExt (λ hx → inner x))))
          where
            inner : (x : S)
                  → (e ∈ˢ layerAt n x (trᴮ x))
                  ≡ ⋁ S (λ p → ⋁ ⟨ p ∈ˢ weightsAt n x ⟩ (λ hp →
                      e ≈ˢ entry (trᴮ x) (iCode (p , weights-sub n x p hp))))
            inner x = image-spec (weightsAt n x)
              (λ r → entry (trᴮ x) (iCode (fst r , weights-sub n x (fst r) (snd r)))) e

        -- The architecture's trᴮ-entries, with the join over the membership
        -- witness that the correction banner mandates. The architecture writes
        -- `fst (i (p , _))` with the proof as an underscore inside a join over
        -- S, and there is nothing to solve that underscore with; this is the
        -- same defect Track A, Track D and Track H each met at a different
        -- signature, and the repair is the same one.
        --
        -- The statement has NO name hypothesis. Every quantifier is over the
        -- raw ground codes, and it holds for arbitrary n, which is the direct
        -- consequence of Track B making support total.

        EntryClass : (n e : S) → Ω
        EntryClass n e =
          ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ carrier ⟩ (λ hp →
            (entry x p ∈ˢ n) ⊓ (e ≈ˢ entry (trᴮ x) (iCode (p , hp))))))

        trᴮ-entries : (n e : S) → (e ∈ˢ trᴮ n) ≡ EntryClass n e
        trᴮ-entries n e = trᴮ-raw n e ∙ ⇔toPath fwd bwd
          where
            fwd : ⟨ RawClass n e ⟩ → ⟨ EntryClass n e ⟩
            fwd = PT.rec (snd (EntryClass n e))
              (λ { (x , t₁) → PT.rec (snd (EntryClass n e))
                (λ { (hx , t₂) → PT.rec (snd (EntryClass n e))
                  (λ { (p , t₃) → PT.rec (snd (EntryClass n e))
                    (λ { (hp , heq) →
                           ∣ x , ∣ p , ∣ weights-sub n x p hp
                                       , weights-out n x p hp
                                       , heq ∣₁ ∣₁ ∣₁ })
                    t₃ })
                  t₂ })
                t₁ })

            -- The one step where the proof irrelevance of membership is used.
            -- The witness the target supplies and the witness weights-sub
            -- recovers are two proofs of one proposition, so they are equal,
            -- and the translated weight is transported along that equality.
            bwd : ⟨ EntryClass n e ⟩ → ⟨ RawClass n e ⟩
            bwd = PT.rec (snd (RawClass n e))
              (λ { (x , t₁) → PT.rec (snd (RawClass n e))
                (λ { (p , t₂) → PT.rec (snd (RawClass n e))
                  (λ { (hp , hen , heq) →
                         ∣ x , ∣ supp-in n x p hp hen
                              , ∣ p , ∣ weights-in n x p hp hen
                                     , subst
                                         (λ h → ⟨ e ≈ˢ entry (trᴮ x) (iCode (p , h)) ⟩)
                                         (snd (p ∈ˢ carrier) hp
                                           (weights-sub n x p (weights-in n x p hp hen)))
                                         heq ∣₁ ∣₁ ∣₁ ∣₁ })
                  t₂ })
                t₁ })

        -- ---------------------------------------------------------------------
        -- 3. Validity
        -- ---------------------------------------------------------------------

        -- The shape clause holds for EVERY ground code, well formed or not,
        -- because the construction emits translated entries and nothing else.
        -- A malformed source simply contributes no layer at the members that
        -- are not entries, since support and weightsAt see only the entries.

        trᴮ-shape : (n e : S) → ⟨ e ∈ˢ trᴮ n ⟩
                  → ∥ Σ[ y ∈ S ] Σ[ b ∈ S ] (e ≡ entry y b) × ⟨ b ∈ˢ B ⟩ ∥₁
        trᴮ-shape n e he = PT.rec PT.squash₁
          (λ { (x , t₁) → PT.rec PT.squash₁
            (λ { (p , t₂) → PT.map
              (λ { (hp , _ , heq) →
                     trᴮ x , iCode (p , hp) , ≈→≡ heq , i∈B (p , hp) })
              t₂ })
            t₁ })
          (subst ⟨_⟩ (trᴮ-entries n e) he)

        -- The hereditary clause is where the source's name proof is spent,
        -- and it is spent once. A child of the translated name arrives with a
        -- Boolean weight; the entry law decomposes the entry that carries it;
        -- injectivity of the entry identifies the child with the translation
        -- of a child of n; and the inductive hypothesis applies there.
        -- Nothing in this argument mentions i beyond the fact that it landed
        -- the weight in B.

        trᴮ-name : (n : S) → ⟨ IsNameᴾ n ⟩ → ⟨ IsNameᴮ (trᴮ n) ⟩
        trᴮ-name =
          WFI.induction child-wf
            {P = λ n → ⟨ IsNameᴾ n ⟩ → ⟨ IsNameᴮ (trᴮ n) ⟩} step
          where
            step : (n : S)
                 → ((x : S) → Child x n → ⟨ IsNameᴾ x ⟩ → ⟨ IsNameᴮ (trᴮ x) ⟩)
                 → ⟨ IsNameᴾ n ⟩ → ⟨ IsNameᴮ (trᴮ n) ⟩
            step n IH hn = name-introᴮ (trᴮ n) (trᴮ-shape n) hered
              where
                hered : (y : S) → Child y (trᴮ n) → ⟨ IsNameᴮ y ⟩
                hered y edge = PT.rec (snd (IsNameᴮ y))
                  (λ { (b , hb) → PT.rec (snd (IsNameᴮ y))
                    (λ { (x , t₁) → PT.rec (snd (IsNameᴮ y))
                      (λ { (p , t₂) → PT.rec (snd (IsNameᴮ y))
                        (λ { (hp , hen , heq) →
                               subst (λ w → ⟨ IsNameᴮ w ⟩)
                                 (sym (fst (entry-inj (≈→≡ heq))))
                                 (IH x (child-entry x p n hen)
                                    (child-is-nameᴾ n hn x (child-entry x p n hen))) })
                        t₂ })
                      t₁ })
                    (subst ⟨_⟩ (trᴮ-entries n (entry y b)) hb) })
                  (child-weight y (trᴮ n) edge)

        -- ---------------------------------------------------------------------
        -- 4. The ground half: the internal image and the support law
        -- ---------------------------------------------------------------------

        -- Track D's contract, discharged by route I. Track D's finding F7
        -- says precisely what this costs and what it does not: the contract
        -- produces an image at a GIVEN function, and the content of a name
        -- valued recursion is that the function is built out of the image
        -- itself. That fixed point is not in the contract; it is in trᴮ-host,
        -- which is what the recursion datum buys. So trᴮ-internal here is
        -- free and trᴮ itself was not.

        trᴮ-internal : InternalImage trᴮ
        trᴮ-internal = internalize trᴮ

        trᴮ-img : S → S
        trᴮ-img = InternalImage.img trᴮ-internal

        trᴮ-img-spec : (a z : S) → (z ∈ˢ trᴮ-img a) ≡ ImageClass trᴮ a z
        trᴮ-img-spec = InternalImage.img-spec trᴮ-internal

        -- THE SUPPORT LAW, and it is an EQUALITY in the forward direction.
        -- The architecture explains the asymmetry with the reverse direction
        -- correctly: forward, every child of n contributes at least one entry
        -- to trᴮ n, because i is total on the conditions and emits one weight
        -- for each; reverse, a child weighted by ⊥ᴮ contributes nothing,
        -- because below ⊥ᴮ is empty, so the reverse law is an inclusion and
        -- writing it as an equality would be a false theorem.
        --
        -- Note what the equality does NOT need. It needs no injectivity of i:
        -- two conditions collapsing to one Boolean weight merges two entries
        -- into one but leaves the SET of first coordinates untouched, and the
        -- support is exactly that set. It also needs no name hypothesis,
        -- which is stronger than the architecture states it; the premised
        -- form the architecture writes is recorded immediately below so that
        -- a consumer reading section 1.9 finds what it expects.

        trᴮ-support : (n : S) → supportᴮ (trᴮ n) ≡ trᴮ-img (support n)
        trᴮ-support n = ext-path (λ y → ⇔toPath (into y) (outof y))
          where
            into : (y : S) → ⟨ y ∈ˢ supportᴮ (trᴮ n) ⟩
                 → ⟨ y ∈ˢ trᴮ-img (support n) ⟩
            into y hy = PT.rec (snd (y ∈ˢ trᴮ-img (support n)))
              (λ { (b , _ , hmem) → PT.rec (snd (y ∈ˢ trᴮ-img (support n)))
                (λ { (x , t₁) → PT.rec (snd (y ∈ˢ trᴮ-img (support n)))
                  (λ { (p , t₂) → PT.rec (snd (y ∈ˢ trᴮ-img (support n)))
                    (λ { (hp , hen , heq) →
                           subst ⟨_⟩ (sym (trᴮ-img-spec (support n) y))
                             ∣ x , supp-in n x p hp hen
                                 , ≡→≈ (fst (entry-inj (≈→≡ heq))) ∣₁ })
                    t₂ })
                  t₁ })
                (subst ⟨_⟩ (trᴮ-entries n (entry y b)) hmem) })
              (suppᴮ-out (trᴮ n) y hy)

            outof : (y : S) → ⟨ y ∈ˢ trᴮ-img (support n) ⟩
                  → ⟨ y ∈ˢ supportᴮ (trᴮ n) ⟩
            outof y hy = PT.rec (snd (y ∈ˢ supportᴮ (trᴮ n)))
              (λ { (x , hx , heq) → PT.rec (snd (y ∈ˢ supportᴮ (trᴮ n)))
                (λ { (p , hp , hen) →
                       suppᴮ-in (trᴮ n) y (iCode (p , hp)) (i∈B (p , hp))
                         (subst ⟨_⟩
                           (sym (trᴮ-entries n (entry y (iCode (p , hp)))))
                           ∣ x , ∣ p , ∣ hp , hen
                                , ≡→≈ (cong (λ w → entry w (iCode (p , hp)))
                                        (≈→≡ heq)) ∣₁ ∣₁ ∣₁) })
                (supp-out n x hx) })
              (subst ⟨_⟩ (trᴮ-img-spec (support n) y) hy)

        trᴮ-support-named : (n : S) → ⟨ IsNameᴾ n ⟩
                          → supportᴮ (trᴮ n) ≡ trᴮ-img (support n)
        trᴮ-support-named n _ = trᴮ-support n

        -- ---------------------------------------------------------------------
        -- 5. Closure and the bound on the translated support
        -- ---------------------------------------------------------------------

        -- The roadmap's "set-code closure and bounds for the whole translated
        -- support", read hereditarily. The image of a Child-closed ground set
        -- of poset names is a Child-closed ground set of Boolean names, and it
        -- bounds the translated support. Both are deliverables of this track
        -- and neither is a hypothesis.
        --
        -- The closed family arrives as Track C's data minus its coded field:
        -- a code C, a membership, and host closure. Track C's ClosedFamily
        -- derives exactly that from its coded field through coded→closed, so
        -- a consumer holding one of its records can call these directly.

        trᴮ-closed : (C : S) → Closedᴴ C → ⟨ closedᴮ (trᴮ-img C) ⟩
        trᴮ-closed C cl = closedᴮ-intro (trᴮ-img C) step
          where
            goal : (e : S) → Type ℓ
            goal e = ∥ Σ[ y ∈ S ] Σ[ b ∈ S ]
                       (⟨ y ∈ˢ trᴮ-img C ⟩ × ⟨ b ∈ˢ B ⟩ × (e ≡ entry y b)) ∥₁

            step : (m : S) → ⟨ m ∈ˢ trᴮ-img C ⟩ → (e : S) → ⟨ e ∈ˢ m ⟩ → goal e
            step m hm e he = PT.rec PT.squash₁
              (λ { (x , hx , heq) → PT.rec PT.squash₁
                (λ { (u , t₁) → PT.rec PT.squash₁
                  (λ { (p , t₂) → PT.map
                    (λ { (hp , hen , heq₂) →
                           trᴮ u
                         , iCode (p , hp)
                         , subst ⟨_⟩ (sym (trᴮ-img-spec C (trᴮ u)))
                             ∣ u , cl x hx u (child-entry u p x hen)
                                 , ≈-refl (trᴮ u) ∣₁
                         , i∈B (p , hp)
                         , ≈→≡ heq₂ })
                    t₂ })
                  t₁ })
                (subst ⟨_⟩ (trᴮ-entries x e) (mem-subst (≈→≡ heq) he)) })
              (subst ⟨_⟩ (trᴮ-img-spec C m) hm)

        trᴮ-in : (C n : S) → ⟨ n ∈ˢ C ⟩ → ⟨ trᴮ n ∈ˢ trᴮ-img C ⟩
        trᴮ-in C n hn = subst ⟨_⟩ (sym (trᴮ-img-spec C (trᴮ n)))
          ∣ n , hn , ≈-refl (trᴮ n) ∣₁

        trᴮ-closure : (C n : S) → ⟨ n ∈ˢ C ⟩ → Closedᴴ C
                    → Σ[ D ∈ S ] (⟨ closedᴮ D ⟩ × ⟨ trᴮ n ∈ˢ D ⟩)
        trᴮ-closure C n hn cl = trᴮ-img C , trᴮ-closed C cl , trᴮ-in C n hn

        -- The bound. The translated support is the image of the source
        -- support by section 4, the source support sits inside any closed
        -- family containing n, and the internal image is monotone, so the
        -- three facts compose. Monotonicity is not stated separately: it is
        -- one rewrite along the image specification in each direction.

        trᴮ-bound : (C n : S) → ⟨ n ∈ˢ C ⟩ → Closedᴴ C
                  → ⟨ supportᴮ (trᴮ n) ⊆ˢ trᴮ-img C ⟩
        trᴮ-bound C n hn cl y hy = PT.rec (snd (y ∈ˢ trᴮ-img C))
          (λ { (x , hx , heq) → subst ⟨_⟩ (sym (trᴮ-img-spec C y))
                 ∣ x , cl n hn x (support-child n x hx) , heq ∣₁ })
          (subst ⟨_⟩ (trᴮ-img-spec (support n) y)
            (mem-subst (trᴮ-support n) hy))
