{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track D: the Boolean atomic laws. Bell's Theorem 1.17, his (1.15) and
-- (1.16) read back as characterizations, and the bounded quantifier calculus
-- of Corollary 1.18, all for the two atomic values Track C defines.
--
-- WHAT THIS FILE PROVES AND WHAT IT ASSUMES. Track C builds the equality value
-- and the membership value by recursion on the kernel and ships them through
-- five universal properties and one symmetry, collected in its record
-- AtomicSemantics (K4/Atomic.agda:551-571). This file takes exactly those
-- eight fields, flat, and proves everything Bell's 1.17 asserts about them.
-- Nothing here inspects a definition: every proof below is an argument about
-- an arbitrary semantics satisfying the five universal properties, so it holds
-- of any other construction of the same interface as well.
--
-- WHY THE TELESCOPE IS FLAT RATHER THAN THE RECORD. AtomicSemantics is
-- declared inside K4.Atomic.Atomic, whose own telescope carries Track B's
-- value sets and four kernel operations that no law below mentions. Taking the
-- record would force all of those into this file's ledger to name one type.
-- The eight parameters of module Laws are that record field for field and in
-- its order, so a coordinator passes AtomicSemantics.eqᴬ as, AtomicSemantics
-- .memᴬ as, and so on, with no adaptation. Records are generative and this
-- file declares none: the three algebra records are Track A's, opened here by
-- one route and re-exported by none.
--
-- THE SHAPE OF EVERY STATEMENT. Project rule R3 says a declaration can fail to
-- elaborate in bounded time when its TYPE contains a construction of one layer
-- applied to a term of another. So no type below names a join or a meet of a
-- constructed set. The two theorems that do mention supᴮ and infᴮ, bell-1-15
-- and bell-1-16, apply them to a universally quantified ground code and a
-- universally quantified subset proof, which are variables and cannot unfold;
-- that is the same shape Track A's whole infinitary calculus carries. Every
-- other law is an order statement between values built from the parameters.
--
-- WHAT IS NOT SEALED, AND WHY NOTHING NEEDS TO BE. R2 seals description
-- operator terms. This file defines no value at all: its definitions are
-- proofs of order statements and of paths between values that are already
-- sealed inside Track C. There is nothing here that could unfold into a
-- separation or into a double pseudocomplement, so there is no opaque block.
--
-- SYMMETRY IS IMPORTED, NOT REPROVED. Architecture section 1.5 lists 1.17(iii)
-- as a Track D row and section 5.4.5 flags it as the one step with no K0 or K3
-- precedent. Track C proved it (REPORT-C.md section C1): under the expanded
-- symmetric equation the two families to be identified are the same operation
-- applied to pointwise equal families, so a funExt under a fixed operation
-- settles it, and it spends no infinitary law and no excluded middle. It
-- arrives here as the parameter ≈ᴮ-sym, which is therefore the deliverable
-- name for that row, and it is used in six proofs below.
--
-- THE ORDER OF THE ARGUMENT. Bell proves (i) by induction with (ii) at the
-- children; that is one induction with two conclusions and it is the first
-- block below. He proves (iv) by a second induction on the FIRST coordinate
-- with the other two names universally quantified inside the motive, which is
-- the shape Valuation.agda:385-391 uses for its own transitivity, and the four
-- lemmas that induction needs are stated first as standalone facts about an
-- arbitrary transitivity hypothesis so that the same text serves inside the
-- induction and outside it. (v) and (vi) then follow from (iv) with no further
-- induction, and 1.18 follows from (ii) and the congruences with none.
--
-- NO INFINITE DISTRIBUTIVE LAW AND NO RESIDUATION IS USED. Bell's proof takes
-- a supremum over a class four times; each of those steps is here a use of
-- Track C's memᴬ-lub, which IS the statement that the membership value is a
-- least upper bound, curried through Track A's implication adjunction. So the
-- replacement Track A shipped for the architecture's false inf-residual is not
-- needed on this track either: grep for sup-residual and inf-residual over
-- this file returns 0.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Infinitary
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K4.AtomicLaws {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

-- Track A's scope contract, observed. K4.Algebra is opened here for the three
-- record types and the point vocabulary and is NOT re-exported, because
-- re-exporting a record TYPE name makes its record module reachable twice and
-- a consumer that opens both routes fails with AmbiguousModule (REPORT-A.md
-- section 4). K4.Infinitary is opened inside Core, where B, L, Cm and Kc
-- exist, and it is not re-exported either.

open K4.Algebra 𝒮
  using ( Pt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans; Lattice; Complement; CodedComplete )

-- The two crossings between the structure's equality and the host path. They
-- are spent only in bell-1-15 and bell-1-16, where a value set is given by an
-- attainment law stated with ≈ˢ and the order must be transported along a
-- path between codes. Same two lines as K4/Atomic.agda:132-137.

≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
≈ˢ-refl x = subst ⟨_⟩ (sym (paths x x)) refl

≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

--------------------------------------------------------------------------------
-- The algebra and the name layer
--------------------------------------------------------------------------------

-- The telescope of Core is the algebra plus the part of K3 that the laws
-- actually touch. It is SMALLER than architecture section 1.4's list for
-- Track C and smaller than the Track D brief's permitted hypotheses:
--
--   * the kernel enters as Child and one raw induction principle, which is
--     NameKernel.agda:400-405's RawRec.result at ℓp := ℓ. The pair recursor is
--     not taken: no law below is proved by a two coordinate induction;
--   * the support enters outward only, NameSupport.agda:534, exactly as in
--     Track C. support-in carries ⟨ IsName n ⟩ and no statement here has one,
--     so IsName occurs in no signature of this file either and both values
--     stay total on raw codes;
--   * the weight enters as a bare operation with NO law. weightᴮ-upper,
--     weightᴮ-lub and weightᴮ-zero are all unused: Bell's 1.17(ii) is proved
--     from the membership value's own upper bound property together with
--     1.17(i) at the same code, which is Bell's own argument (∗) at
--     fulltext:2100-2103 and needs nothing about how the weight was built.

module Core
  (B  : S)
  (L  : Lattice B)
  (Cm : Complement B L)
  (Kc : CodedComplete B L)
  (Child       : S → S → Type ℓ)
  (rawRec      : (P : S → Type ℓ)
               → ((n : S) → ((x : S) → Child x n → P x) → P n)
               → (n : S) → P n)
  (support     : S → S)
  (support-out : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n)
  (weightᴮ     : (n x : S) → Pt B)
  where

  open K4.Infinitary 𝒮 ext paths B L Cm Kc

  ------------------------------------------------------------------------------
  -- A small order toolkit
  ------------------------------------------------------------------------------

  -- Every proof below is a chain of order steps, and the four moves it makes
  -- are these. They are named because the alternative is to inline ⊓-comm
  -- transports at thirty sites, and because R1's failure shape is a bare
  -- reflexivity standing in for an unchanged endpoint: here every endpoint is
  -- named and no metavariable is left for the propositionality component.

  ⊓-swap : (a b c : Pt B) → ⟨ (a ⊓ᴮ b) ≤ᴮ c ⟩ → ⟨ (b ⊓ᴮ a) ≤ᴮ c ⟩
  ⊓-swap a b c h = subst (λ z → ⟨ z ≤ᴮ c ⟩) (⊓-comm a b) h

  -- An order statement and its curried form against the top element. Bell
  -- writes 1.17(i) and (ii) as the two halves of one equation ⟦u = u⟧ = 1; the
  -- glb property produces the bound from the top element, so both halves live
  -- on this bridge.

  ≤→⊤⇒ : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → ⟨ ⊤ᴮ ≤ᴮ (u ⇒ᴮ v) ⟩
  ≤→⊤⇒ u v h = ⇒ᴮ-curry ⊤ᴮ u v (⊆ˢ-trans (⊓-lb₂ ⊤ᴮ u) h)

  ⊤⇒→≤ : (u v : Pt B) → ⟨ ⊤ᴮ ≤ᴮ (u ⇒ᴮ v) ⟩ → ⟨ u ≤ᴮ v ⟩
  ⊤⇒→≤ u v h =
    ⊆ˢ-trans (⊓-glb ⊤ᴮ u u (⊤-greatest u) (≤ᴮ-refl u))
             (⇒ᴮ-uncurry ⊤ᴮ u v h)

  ≡⊤ : (u : Pt B) → ⟨ ⊤ᴮ ≤ᴮ u ⟩ → u ≡ ⊤ᴮ
  ≡⊤ u h = ≤ᴮ-antisym (⊤-greatest u) h

  ------------------------------------------------------------------------------
  -- The laws
  ------------------------------------------------------------------------------

  -- The telescope of Laws is Track C's AtomicSemantics, field for field, in
  -- its order, with the operator spellings restored: a record field is brought
  -- into the enclosing scope as a projection, which is why Track C had to call
  -- them eqᴬ and memᴬ, and nothing takes those spellings here.

  module Laws
    (_≈ᴮ_ : S → S → Pt B)
    (_∈ᴮ_ : S → S → Pt B)
    (∈ᴮ-ub  : (m n x : S) → ⟨ x ∈ˢ support n ⟩
            → ⟨ ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x)) ≤ᴮ (m ∈ᴮ n) ⟩)
    (∈ᴮ-lub : (m n : S) (c : Pt B)
            → ((x : S) → ⟨ x ∈ˢ support n ⟩
               → ⟨ ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x)) ≤ᴮ c ⟩)
            → ⟨ (m ∈ᴮ n) ≤ᴮ c ⟩)
    (≈ᴮ-lbˡ : (m n x : S) → ⟨ x ∈ˢ support m ⟩
            → ⟨ (m ≈ᴮ n) ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ⟩)
    (≈ᴮ-lbʳ : (m n y : S) → ⟨ y ∈ˢ support n ⟩
            → ⟨ (m ≈ᴮ n) ≤ᴮ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ⟩)
    (≈ᴮ-glb : (m n : S) (c : Pt B)
            → ((x : S) → ⟨ x ∈ˢ support m ⟩
               → ⟨ c ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ⟩)
            → ((y : S) → ⟨ y ∈ˢ support n ⟩
               → ⟨ c ≤ᴮ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ⟩)
            → ⟨ c ≤ᴮ (m ≈ᴮ n) ⟩)
    (≈ᴮ-sym : (m n : S) → (m ≈ᴮ n) ≡ (n ≈ᴮ m))
    where

    ----------------------------------------------------------------------------
    -- Bell 1.17(iii), imported
    ----------------------------------------------------------------------------

    -- Restated under the architecture's name so that a consumer reading
    -- section 1.5's table finds every row of it in this module. The content is
    -- Track C's, and REPORT-C.md section C1 is its record.

    ≈ᴮ-symmetric : (m n : S) → (m ≈ᴮ n) ≡ (n ≈ᴮ m)
    ≈ᴮ-symmetric = ≈ᴮ-sym

    -- Transitivity read at exchanged endpoints. Bell's proof of (iv) uses this
    -- move once, where he says "using (iii), the inductive hypothesis implies"
    -- (fulltext, page 26, just before his (2)). It is pure symmetry: three
    -- rewrites and a commutation, no induction and no algebra beyond ⊓-comm.

    mirror : (a b c : S)
           → ⟨ ((a ≈ᴮ b) ⊓ᴮ (b ≈ᴮ c)) ≤ᴮ (a ≈ᴮ c) ⟩
           → ⟨ ((c ≈ᴮ b) ⊓ᴮ (b ≈ᴮ a)) ≤ᴮ (c ≈ᴮ a) ⟩
    mirror a b c h = ⊓-swap (b ≈ᴮ a) (c ≈ᴮ b) (c ≈ᴮ a) h₃
      where
      h₁ : ⟨ ((b ≈ᴮ a) ⊓ᴮ (b ≈ᴮ c)) ≤ᴮ (a ≈ᴮ c) ⟩
      h₁ = subst (λ z → ⟨ (z ⊓ᴮ (b ≈ᴮ c)) ≤ᴮ (a ≈ᴮ c) ⟩) (≈ᴮ-sym a b) h
      h₂ : ⟨ ((b ≈ᴮ a) ⊓ᴮ (c ≈ᴮ b)) ≤ᴮ (a ≈ᴮ c) ⟩
      h₂ = subst (λ z → ⟨ ((b ≈ᴮ a) ⊓ᴮ z) ≤ᴮ (a ≈ᴮ c) ⟩) (≈ᴮ-sym b c) h₁
      h₃ : ⟨ ((b ≈ᴮ a) ⊓ᴮ (c ≈ᴮ b)) ≤ᴮ (c ≈ᴮ a) ⟩
      h₃ = subst (λ z → ⟨ ((b ≈ᴮ a) ⊓ᴮ (c ≈ᴮ b)) ≤ᴮ z ⟩) (≈ᴮ-sym a c) h₂

    ----------------------------------------------------------------------------
    -- The two substitution steps, stated against a transitivity hypothesis
    ----------------------------------------------------------------------------

    -- These are the load bearing lemmas of the whole file. Bell uses each of
    -- them twice, once under the inductive hypothesis of (iv) and once with
    -- (iv) itself in hand, and stating them against a hypothesis rather than
    -- against a fixed theorem is what lets the same text serve both times.
    --
    -- mem-subst is Bell's step "taking the supremum over z" at fulltext:2117.
    -- It is NOT a distributive law and NOT a residuation: the membership value
    -- is a least upper bound by ∈ᴮ-lub, so bounding it against a value that
    -- has a fixed factor is one currying, one least upper bound, one
    -- uncurrying. Read it as: if equality at z composes with equality into
    -- anything the support of w holds, then equality at z substitutes into the
    -- LEFT argument of membership in w.

    mem-subst : (z w : S)
              → ((y x : S) → ⟨ x ∈ˢ support w ⟩
                 → ⟨ ((z ≈ᴮ y) ⊓ᴮ (y ≈ᴮ x)) ≤ᴮ (z ≈ᴮ x) ⟩)
              → (y : S) → ⟨ ((z ≈ᴮ y) ⊓ᴮ (y ∈ᴮ w)) ≤ᴮ (z ∈ᴮ w) ⟩
    mem-subst z w tr y =
      ⊓-swap (y ∈ᴮ w) (z ≈ᴮ y) (z ∈ᴮ w)
        (⇒ᴮ-uncurry (y ∈ᴮ w) (z ≈ᴮ y) (z ∈ᴮ w) curried)
      where
      inner : (x : S) → ⟨ x ∈ˢ support w ⟩
            → ⟨ ((((weightᴮ w x) ⊓ᴮ (y ≈ᴮ x))) ⊓ᴮ (z ≈ᴮ y)) ≤ᴮ (z ∈ᴮ w) ⟩
      inner x hx =
        ⊆ˢ-trans
          (⊓-glb (weightᴮ w x) (z ≈ᴮ x)
                 (((weightᴮ w x) ⊓ᴮ (y ≈ᴮ x)) ⊓ᴮ (z ≈ᴮ y))
            (⊆ˢ-trans (⊓-lb₁ ((weightᴮ w x) ⊓ᴮ (y ≈ᴮ x)) (z ≈ᴮ y))
                      (⊓-lb₁ (weightᴮ w x) (y ≈ᴮ x)))
            (⊆ˢ-trans
              (⊓-glb (z ≈ᴮ y) (y ≈ᴮ x)
                     (((weightᴮ w x) ⊓ᴮ (y ≈ᴮ x)) ⊓ᴮ (z ≈ᴮ y))
                (⊓-lb₂ ((weightᴮ w x) ⊓ᴮ (y ≈ᴮ x)) (z ≈ᴮ y))
                (⊆ˢ-trans (⊓-lb₁ ((weightᴮ w x) ⊓ᴮ (y ≈ᴮ x)) (z ≈ᴮ y))
                          (⊓-lb₂ (weightᴮ w x) (y ≈ᴮ x))))
              (tr y x hx)))
          (∈ᴮ-ub z w x hx)
      curried : ⟨ (y ∈ᴮ w) ≤ᴮ ((z ≈ᴮ y) ⇒ᴮ (z ∈ᴮ w)) ⟩
      curried = ∈ᴮ-lub y w ((z ≈ᴮ y) ⇒ᴮ (z ∈ᴮ w))
                  (λ x hx → ⇒ᴮ-curry ((weightᴮ w x) ⊓ᴮ (y ≈ᴮ x))
                                     (z ≈ᴮ y) (z ∈ᴮ w) (inner x hx))

    -- mem-mono is Bell's step "now take the supremum over y" at fulltext:2123,
    -- and it is the one place where an equality between two names is opened by
    -- its OWN universal property: ≈ᴮ-lbˡ says that the equality value lies
    -- below the implication from each weight of the left name to the
    -- corresponding membership. Read it as: once substitution into the left
    -- argument of membership in w is available for z, equality substitutes
    -- into the RIGHT argument as well.

    mem-mono : (z w : S)
             → ((y : S) → ⟨ ((z ≈ᴮ y) ⊓ᴮ (y ∈ᴮ w)) ≤ᴮ (z ∈ᴮ w) ⟩)
             → (v : S) → ⟨ ((z ∈ᴮ v) ⊓ᴮ (v ≈ᴮ w)) ≤ᴮ (z ∈ᴮ w) ⟩
    mem-mono z w sub v =
      ⇒ᴮ-uncurry (z ∈ᴮ v) (v ≈ᴮ w) (z ∈ᴮ w) curried
      where
      inner : (y : S) → ⟨ y ∈ˢ support v ⟩
            → ⟨ ((((weightᴮ v y) ⊓ᴮ (z ≈ᴮ y))) ⊓ᴮ (v ≈ᴮ w)) ≤ᴮ (z ∈ᴮ w) ⟩
      inner y hy =
        ⊆ˢ-trans
          (⊓-glb (z ≈ᴮ y) (y ∈ᴮ w)
                 (((weightᴮ v y) ⊓ᴮ (z ≈ᴮ y)) ⊓ᴮ (v ≈ᴮ w))
            (⊆ˢ-trans (⊓-lb₁ ((weightᴮ v y) ⊓ᴮ (z ≈ᴮ y)) (v ≈ᴮ w))
                      (⊓-lb₂ (weightᴮ v y) (z ≈ᴮ y)))
            (⊆ˢ-trans
              (⊓-glb (v ≈ᴮ w) (weightᴮ v y)
                     (((weightᴮ v y) ⊓ᴮ (z ≈ᴮ y)) ⊓ᴮ (v ≈ᴮ w))
                (⊓-lb₂ ((weightᴮ v y) ⊓ᴮ (z ≈ᴮ y)) (v ≈ᴮ w))
                (⊆ˢ-trans (⊓-lb₁ ((weightᴮ v y) ⊓ᴮ (z ≈ᴮ y)) (v ≈ᴮ w))
                          (⊓-lb₁ (weightᴮ v y) (z ≈ᴮ y))))
              (⇒ᴮ-uncurry (v ≈ᴮ w) (weightᴮ v y) (y ∈ᴮ w) (≈ᴮ-lbˡ v w y hy))))
          (sub y)
      curried : ⟨ (z ∈ᴮ v) ≤ᴮ ((v ≈ᴮ w) ⇒ᴮ (z ∈ᴮ w)) ⟩
      curried = ∈ᴮ-lub z v ((v ≈ᴮ w) ⇒ᴮ (z ∈ᴮ w))
                  (λ y hy → ⇒ᴮ-curry ((weightᴮ v y) ⊓ᴮ (z ≈ᴮ y))
                                     (v ≈ᴮ w) (z ∈ᴮ w) (inner y hy))

    ----------------------------------------------------------------------------
    -- Bell 1.17(i) and (ii): reflexivity and the weight bound
    ----------------------------------------------------------------------------

    -- Bell's (∗), fulltext:2100-2103. The membership value of x in n is above
    -- the term the support of n contributes at x itself, and that term is the
    -- weight met with the reflexivity value at x. So the weight bound at n is
    -- exactly reflexivity at x, and nothing else is needed: no law about the
    -- weight and no property of the support beyond membership.

    weight-≤-at : (n x : S) → ⟨ x ∈ˢ support n ⟩ → ((x ≈ᴮ x) ≡ ⊤ᴮ)
                → ⟨ (weightᴮ n x) ≤ᴮ (x ∈ᴮ n) ⟩
    weight-≤-at n x h r = ⊆ˢ-trans into (∈ᴮ-ub x n x h)
      where
      into : ⟨ (weightᴮ n x) ≤ᴮ ((weightᴮ n x) ⊓ᴮ (x ≈ᴮ x)) ⟩
      into = ⊓-glb (weightᴮ n x) (x ≈ᴮ x) (weightᴮ n x)
               (≤ᴮ-refl (weightᴮ n x))
               (subst (λ z → ⟨ (weightᴮ n x) ≤ᴮ z ⟩) (sym r)
                      (⊤-greatest (weightᴮ n x)))

    -- 1.17(i). One induction on the kernel with two conclusions, exactly as
    -- Valuation.agda:349 does for its own reflexivity: the greatest lower
    -- bound property reduces ⟦n = n⟧ = 1 to the weight bound at each member of
    -- the support of n, and the weight bound at a member x reduces by (∗) to
    -- reflexivity at x, which is a child of n and so is given by the inductive
    -- hypothesis. Both conjuncts of the greatest lower bound are literally the
    -- same statement here, since both coordinates are n.

    ≈ᴮ-refl : (n : S) → (n ≈ᴮ n) ≡ ⊤ᴮ
    ≈ᴮ-refl = rawRec (λ n → (n ≈ᴮ n) ≡ ⊤ᴮ) step
      where
      step : (n : S) → ((x : S) → Child x n → (x ≈ᴮ x) ≡ ⊤ᴮ) → (n ≈ᴮ n) ≡ ⊤ᴮ
      step n ih = ≡⊤ (n ≈ᴮ n) (≈ᴮ-glb n n ⊤ᴮ conj conj)
        where
        conj : (x : S) → ⟨ x ∈ˢ support n ⟩
             → ⟨ ⊤ᴮ ≤ᴮ ((weightᴮ n x) ⇒ᴮ (x ∈ᴮ n)) ⟩
        conj x h = ≤→⊤⇒ (weightᴮ n x) (x ∈ᴮ n)
                     (weight-≤-at n x h (ih x (support-out n x h)))

    -- 1.17(ii), now unconditional.

    weight-≤ : (n x : S) → ⟨ x ∈ˢ support n ⟩ → ⟨ (weightᴮ n x) ≤ᴮ (x ∈ᴮ n) ⟩
    weight-≤ n x h = weight-≤-at n x h (≈ᴮ-refl x)

    ----------------------------------------------------------------------------
    -- Bell 1.17(iv): transitivity
    ----------------------------------------------------------------------------

    -- The second induction, and the only place in the file where the shape of
    -- the motive matters. It runs on the FIRST coordinate with the other two
    -- names universally quantified INSIDE the motive, which is the shape
    -- Valuation.agda:385-391 uses; flattening it to a three way induction does
    -- not terminate, and the architecture's trap 3 says so.
    --
    -- Inside the step the inductive hypothesis is used three times and in two
    -- orientations. At a member x of the support of m it is used as printed,
    -- to substitute equality into the left argument of membership in the third
    -- name w, which is Bell's (1). At the same x it is used mirrored, to
    -- substitute equality into the left argument of membership in m itself,
    -- which is what Bell's (2) needs and is the step he justifies with "using
    -- (iii)". The mirrored use is why symmetry has to be in hand BEFORE
    -- transitivity, and it is the reason Track C's result moved this row.

    ≈ᴮ-trans : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (m ≈ᴮ p) ⟩
    ≈ᴮ-trans =
      rawRec (λ m → (n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (m ≈ᴮ p) ⟩) step
      where
      step : (m : S)
           → ((x : S) → Child x m
              → (n p : S) → ⟨ ((x ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (x ≈ᴮ p) ⟩)
           → (n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (m ≈ᴮ p) ⟩
      step m ih n p = ≈ᴮ-glb m p ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) left right
        where
        -- Substitution into membership in p, at a member of the support of m.
        -- Available only there, because it is the inductive hypothesis.
        subˡ : (x : S) → ⟨ x ∈ˢ support m ⟩
             → (y : S) → ⟨ ((x ≈ᴮ y) ⊓ᴮ (y ∈ᴮ p)) ≤ᴮ (x ∈ᴮ p) ⟩
        subˡ x hx = mem-subst x p (λ y z _ → ih x (support-out m x hx) y z)

        -- Substitution into membership in m, at an ARBITRARY code. Available
        -- because the descent happens at the support of m rather than at the
        -- code being substituted, and the inductive hypothesis is read
        -- mirrored to make the endpoints line up.
        subᵐ : (z : S) → (y : S) → ⟨ ((z ≈ᴮ y) ⊓ᴮ (y ∈ᴮ m)) ≤ᴮ (z ∈ᴮ m) ⟩
        subᵐ z = mem-subst z m
                   (λ y x hx → mirror x y z (ih x (support-out m x hx) y z))

        left : (x : S) → ⟨ x ∈ˢ support m ⟩
             → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ p)) ⟩
        left x hx =
          ⇒ᴮ-curry ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ m x) (x ∈ᴮ p)
            (⊆ˢ-trans
              (⊓-glb (x ∈ᴮ n) (n ≈ᴮ p) (((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ⊓ᴮ (weightᴮ m x))
                (⊆ˢ-trans
                  (⊓-glb (m ≈ᴮ n) (weightᴮ m x)
                         (((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ⊓ᴮ (weightᴮ m x))
                    (⊆ˢ-trans (⊓-lb₁ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ m x))
                              (⊓-lb₁ (m ≈ᴮ n) (n ≈ᴮ p)))
                    (⊓-lb₂ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ m x)))
                  (⇒ᴮ-uncurry (m ≈ᴮ n) (weightᴮ m x) (x ∈ᴮ n)
                              (≈ᴮ-lbˡ m n x hx)))
                (⊆ˢ-trans (⊓-lb₁ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ m x))
                          (⊓-lb₂ (m ≈ᴮ n) (n ≈ᴮ p))))
              (mem-mono x p (subˡ x hx) n))

        right : (z : S) → ⟨ z ∈ˢ support p ⟩
              → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ ((weightᴮ p z) ⇒ᴮ (z ∈ᴮ m)) ⟩
        right z hz =
          ⇒ᴮ-curry ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ p z) (z ∈ᴮ m)
            (⊆ˢ-trans
              (⊓-glb (z ∈ᴮ n) (n ≈ᴮ m) (((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ⊓ᴮ (weightᴮ p z))
                (⊆ˢ-trans
                  (⊓-glb (n ≈ᴮ p) (weightᴮ p z)
                         (((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ⊓ᴮ (weightᴮ p z))
                    (⊆ˢ-trans (⊓-lb₁ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ p z))
                              (⊓-lb₂ (m ≈ᴮ n) (n ≈ᴮ p)))
                    (⊓-lb₂ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ p z)))
                  (⇒ᴮ-uncurry (n ≈ᴮ p) (weightᴮ p z) (z ∈ᴮ n)
                              (≈ᴮ-lbʳ n p z hz)))
                (subst (λ c → ⟨ (((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ⊓ᴮ (weightᴮ p z)) ≤ᴮ c ⟩)
                       (≈ᴮ-sym m n)
                       (⊆ˢ-trans (⊓-lb₁ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) (weightᴮ p z))
                                 (⊓-lb₁ (m ≈ᴮ n) (n ≈ᴮ p)))))
              (mem-mono z m (subᵐ z) n))

    ----------------------------------------------------------------------------
    -- The substitution calculus for the two atomic relations
    ----------------------------------------------------------------------------

    -- Bell's 1.17(vii) says that equality substitutes into any formula. At the
    -- two ATOMIC relations that is the content of (v) and (vi), and these are
    -- the forms Track G will lift to compound formulas and Track H will spend
    -- on check names. Each of the four laws below is one instance of the two
    -- lemmas already proved, now with transitivity global rather than
    -- inductive, so none of them costs a further induction.

    -- Equality substitutes into the left argument of membership. This is the
    -- raw orientation, with the substituted code first.

    ∈ᴮ-substˡ : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ∈ᴮ p)) ≤ᴮ (m ∈ᴮ p) ⟩
    ∈ᴮ-substˡ m n p = mem-subst m p (λ y x _ → ≈ᴮ-trans m y x) n

    -- 1.17(v), fulltext:2094, in the architecture's orientation.

    ∈ᴮ-congˡ : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (m ∈ᴮ p)) ≤ᴮ (n ∈ᴮ p) ⟩
    ∈ᴮ-congˡ m n p =
      subst (λ c → ⟨ (c ⊓ᴮ (m ∈ᴮ p)) ≤ᴮ (n ∈ᴮ p) ⟩)
            (≈ᴮ-sym n m) (∈ᴮ-substˡ n m p)

    -- Equality substitutes into the right argument of membership, raw
    -- orientation.

    ∈ᴮ-substʳ : (m n p : S) → ⟨ ((m ∈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (m ∈ᴮ p) ⟩
    ∈ᴮ-substʳ m n p = mem-mono m p (λ y → ∈ᴮ-substˡ m y p) n

    -- 1.17(vi), fulltext:2095, in the architecture's orientation.

    ∈ᴮ-congʳ : (m n p : S) → ⟨ ((n ≈ᴮ p) ⊓ᴮ (m ∈ᴮ n)) ≤ᴮ (m ∈ᴮ p) ⟩
    ∈ᴮ-congʳ m n p = ⊓-swap (m ∈ᴮ n) (n ≈ᴮ p) (m ∈ᴮ p) (∈ᴮ-substʳ m n p)

    -- The same two facts for equality itself, which is (iv) read with symmetry
    -- at one endpoint. They are the atomic case of (vii) at the OTHER atomic
    -- relation and a compiler that treats the two relations uniformly wants
    -- both spellings.

    ≈ᴮ-congˡ : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (m ≈ᴮ p)) ≤ᴮ (n ≈ᴮ p) ⟩
    ≈ᴮ-congˡ m n p =
      subst (λ c → ⟨ (c ⊓ᴮ (m ≈ᴮ p)) ≤ᴮ (n ≈ᴮ p) ⟩)
            (≈ᴮ-sym n m) (≈ᴮ-trans n m p)

    ≈ᴮ-congʳ : (m n p : S) → ⟨ ((n ≈ᴮ p) ⊓ᴮ (m ≈ᴮ n)) ≤ᴮ (m ≈ᴮ p) ⟩
    ≈ᴮ-congʳ m n p = ⊓-swap (m ≈ᴮ n) (n ≈ᴮ p) (m ≈ᴮ p) (≈ᴮ-trans m n p)

    -- The curried readings. A compiler node that has to place a value under an
    -- implication wants the congruence already curried, and currying is where
    -- the complement record is spent, so these are stated once here rather
    -- than at each use.

    ≈ᴮ-mono-∈ : (m n p : S) → ⟨ (m ≈ᴮ n) ≤ᴮ ((m ∈ᴮ p) ⇒ᴮ (n ∈ᴮ p)) ⟩
    ≈ᴮ-mono-∈ m n p = ⇒ᴮ-curry (m ≈ᴮ n) (m ∈ᴮ p) (n ∈ᴮ p) (∈ᴮ-congˡ m n p)

    ≈ᴮ-mono-∈ʳ : (m n p : S) → ⟨ (n ≈ᴮ p) ≤ᴮ ((m ∈ᴮ n) ⇒ᴮ (m ∈ᴮ p)) ⟩
    ≈ᴮ-mono-∈ʳ m n p = ⇒ᴮ-curry (n ≈ᴮ p) (m ∈ᴮ n) (m ∈ᴮ p) (∈ᴮ-congʳ m n p)

    ≈ᴮ-mono-≈ : (m n p : S) → ⟨ (m ≈ᴮ n) ≤ᴮ ((m ≈ᴮ p) ⇒ᴮ (n ≈ᴮ p)) ⟩
    ≈ᴮ-mono-≈ m n p = ⇒ᴮ-curry (m ≈ᴮ n) (m ≈ᴮ p) (n ≈ᴮ p) (≈ᴮ-congˡ m n p)

    ----------------------------------------------------------------------------
    -- Bell (1.15) and (1.16) read back
    ----------------------------------------------------------------------------

    -- Track C defines the membership value as a join over the support and then
    -- hides the construction behind ∈ᴮ-ub and ∈ᴮ-lub. bell-1-15 says that
    -- those two properties recover Bell's equation: ANY ground code X whose
    -- members are exactly the values of the family has the membership value as
    -- its supremum. The set is universally quantified, so the code and its
    -- subset proof are variables, and R3 does not bite. The attainment
    -- hypothesis is written in the R4 corrected shape, a join over the carrier
    -- guarded by an inner join over the membership proposition, which is
    -- exactly K4.ValueSets.ValueSets.attain-spec, so a consumer passes that
    -- field with no adaptation.
    --
    -- Two consequences that are worth naming. First, this is the uniqueness
    -- statement for the membership value: two value sets with the same members
    -- give the same element, with no comparison of the two constructions.
    -- Second, it is the only place in the file where the path realization is
    -- spent, because attainment is stated with ≈ˢ while the order is a
    -- statement about codes.

    bell-1-15 : (m n X : S) (hX : ⟨ X ⊆ˢ B ⟩)
              → ((b : S) → (b ∈ˢ X)
                         ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ support n ⟩
                                  (λ h → b ≈ˢ fst ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x)))))
              → (m ∈ᴮ n) ≡ supᴮ X hX
    bell-1-15 m n X hX spec = ≤ᴮ-antisym below above
      where
      occurs : (x : S) (h : ⟨ x ∈ˢ support n ⟩)
             → ⟨ fst ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x)) ∈ˢ X ⟩
      occurs x h =
        subst ⟨_⟩ (sym (spec (fst ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x)))))
              ∣ x , ∣ h , ≈ˢ-refl (fst ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x))) ∣₁ ∣₁
      below : ⟨ (m ∈ᴮ n) ≤ᴮ supᴮ X hX ⟩
      below = ∈ᴮ-lub m n (supᴮ X hX)
                (λ x h → sup-ub X hX ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x)) (occurs x h))
      above : ⟨ supᴮ X hX ≤ᴮ (m ∈ᴮ n) ⟩
      above = sup-lub X hX (m ∈ᴮ n) elim
        where
        elim : (u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ (m ∈ᴮ n) ⟩
        elim u hu =
          PT.rec (snd (u ≤ᴮ (m ∈ᴮ n)))
            (λ { (x , guarded) → PT.rec (snd (u ≤ᴮ (m ∈ᴮ n)))
                   (λ { (h , e) →
                          subst (λ c → ⟨ c ⊆ˢ fst (m ∈ᴮ n) ⟩) (sym (≈→≡ e))
                                (∈ᴮ-ub m n x h) })
                   guarded })
            (subst ⟨_⟩ (spec (fst u)) hu)

    -- (1.16), fulltext:2021, in Bell's printed form. Track C's report records
    -- that this row is ungated: the second conjunct reads with the arguments
    -- exchanged relative to the recursion's own step, and symmetry is what
    -- licenses the exchange. Both value sets are universally quantified with
    -- their attainment laws, for the same reason as in bell-1-15.

    bell-1-16 : (m n Ym Yn : S) (hm : ⟨ Ym ⊆ˢ B ⟩) (hn : ⟨ Yn ⊆ˢ B ⟩)
              → ((b : S) → (b ∈ˢ Ym)
                         ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ support m ⟩
                                  (λ h → b ≈ˢ fst ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)))))
              → ((b : S) → (b ∈ˢ Yn)
                         ≡ ⋁ S (λ y → ⋁ ⟨ y ∈ˢ support n ⟩
                                  (λ h → b ≈ˢ fst ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)))))
              → (m ≈ᴮ n) ≡ ((infᴮ Ym hm) ⊓ᴮ (infᴮ Yn hn))
    bell-1-16 m n Ym Yn hm hn specM specN = ≤ᴮ-antisym below above
      where
      occursM : (x : S) (h : ⟨ x ∈ˢ support m ⟩)
              → ⟨ fst ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ∈ˢ Ym ⟩
      occursM x h =
        subst ⟨_⟩ (sym (specM (fst ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)))))
              ∣ x , ∣ h , ≈ˢ-refl (fst ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n))) ∣₁ ∣₁
      occursN : (y : S) (h : ⟨ y ∈ˢ support n ⟩)
              → ⟨ fst ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ∈ˢ Yn ⟩
      occursN y h =
        subst ⟨_⟩ (sym (specN (fst ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)))))
              ∣ y , ∣ h , ≈ˢ-refl (fst ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m))) ∣₁ ∣₁
      belowM : ⟨ (m ≈ᴮ n) ≤ᴮ infᴮ Ym hm ⟩
      belowM = inf-glb Ym hm (m ≈ᴮ n) elim
        where
        elim : (u : Pt B) → ⟨ fst u ∈ˢ Ym ⟩ → ⟨ (m ≈ᴮ n) ≤ᴮ u ⟩
        elim u hu =
          PT.rec (snd ((m ≈ᴮ n) ≤ᴮ u))
            (λ { (x , guarded) → PT.rec (snd ((m ≈ᴮ n) ≤ᴮ u))
                   (λ { (h , e) →
                          subst (λ c → ⟨ fst (m ≈ᴮ n) ⊆ˢ c ⟩) (sym (≈→≡ e))
                                (≈ᴮ-lbˡ m n x h) })
                   guarded })
            (subst ⟨_⟩ (specM (fst u)) hu)
      belowN : ⟨ (m ≈ᴮ n) ≤ᴮ infᴮ Yn hn ⟩
      belowN = inf-glb Yn hn (m ≈ᴮ n) elim
        where
        elim : (u : Pt B) → ⟨ fst u ∈ˢ Yn ⟩ → ⟨ (m ≈ᴮ n) ≤ᴮ u ⟩
        elim u hu =
          PT.rec (snd ((m ≈ᴮ n) ≤ᴮ u))
            (λ { (y , guarded) → PT.rec (snd ((m ≈ᴮ n) ≤ᴮ u))
                   (λ { (h , e) →
                          subst (λ c → ⟨ fst (m ≈ᴮ n) ⊆ˢ c ⟩) (sym (≈→≡ e))
                                (≈ᴮ-lbʳ m n y h) })
                   guarded })
            (subst ⟨_⟩ (specN (fst u)) hu)
      below : ⟨ (m ≈ᴮ n) ≤ᴮ ((infᴮ Ym hm) ⊓ᴮ (infᴮ Yn hn)) ⟩
      below = ⊓-glb (infᴮ Ym hm) (infᴮ Yn hn) (m ≈ᴮ n) belowM belowN
      above : ⟨ ((infᴮ Ym hm) ⊓ᴮ (infᴮ Yn hn)) ≤ᴮ (m ≈ᴮ n) ⟩
      above = ≈ᴮ-glb m n ((infᴮ Ym hm) ⊓ᴮ (infᴮ Yn hn)) leftPart rightPart
        where
        leftPart : (x : S) → ⟨ x ∈ˢ support m ⟩
                 → ⟨ ((infᴮ Ym hm) ⊓ᴮ (infᴮ Yn hn))
                     ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ⟩
        leftPart x h =
          ⊆ˢ-trans (⊓-lb₁ (infᴮ Ym hm) (infᴮ Yn hn))
                   (inf-lb Ym hm ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) (occursM x h))
        rightPart : (y : S) → ⟨ y ∈ˢ support n ⟩
                  → ⟨ ((infᴮ Ym hm) ⊓ᴮ (infᴮ Yn hn))
                      ≤ᴮ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ⟩
        rightPart y h =
          ⊆ˢ-trans (⊓-lb₂ (infᴮ Ym hm) (infᴮ Yn hn))
                   (inf-lb Yn hn ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) (occursN y h))

    ----------------------------------------------------------------------------
    -- Extensionality of the value, and the empty name
    ----------------------------------------------------------------------------

    -- If two names have the same membership value at every code, their
    -- equality value is top. This is the half of extensionality that the
    -- atomic layer can prove on its own, and it needs only the weight bound:
    -- the greatest lower bound property asks for the weight of each member of
    -- one support to lie below membership in the OTHER name, and 1.17(ii)
    -- supplies it for the same name. Valuation.agda:456-462 proves its own
    -- version the same way.

    ext-≈ᴮ : (m n : S) → ((r : S) → (r ∈ᴮ m) ≡ (r ∈ᴮ n)) → (m ≈ᴮ n) ≡ ⊤ᴮ
    ext-≈ᴮ m n agree = ≡⊤ (m ≈ᴮ n) (≈ᴮ-glb m n ⊤ᴮ leftPart rightPart)
      where
      leftPart : (x : S) → ⟨ x ∈ˢ support m ⟩
               → ⟨ ⊤ᴮ ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ⟩
      leftPart x h =
        ≤→⊤⇒ (weightᴮ m x) (x ∈ᴮ n)
          (subst (λ c → ⟨ (weightᴮ m x) ≤ᴮ c ⟩) (agree x) (weight-≤ m x h))
      rightPart : (y : S) → ⟨ y ∈ˢ support n ⟩
                → ⟨ ⊤ᴮ ≤ᴮ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ⟩
      rightPart y h =
        ≤→⊤⇒ (weightᴮ n y) (y ∈ᴮ m)
          (subst (λ c → ⟨ (weightᴮ n y) ≤ᴮ c ⟩) (sym (agree y)) (weight-≤ n y h))

    -- Nothing is a member of a name with empty support.
    --
    -- MEASURED CORRECTION TO THE ARCHITECTURE. Section 1.5 prints this row as
    -- ∈ᴮ-empty : (m : S) → (m ∈ᴮ ∅ᴺ) ≡ ⊥ᴮ, "via sup-empty". There is no ∅ᴺ in
    -- this track's telescope and there should not be: the empty name is a
    -- construction of the standard names layer, not of the atomic laws, and
    -- taking it as a parameter would force its support computation in as well.
    -- The hypothesis form below is strictly more general, it applies to ANY
    -- code with empty support, and it does not go through sup-empty at all:
    -- the membership value is a least upper bound of the empty family by
    -- ∈ᴮ-lub, so the bound against bottom is immediate. A consumer holding
    -- support ∅ᴺ empty gets the printed statement by one application.

    ∈ᴮ-empty : (m n : S) → ((x : S) → ⟨ x ∈ˢ support n ⟩ → ⟨ ⊥ ⟩)
             → (m ∈ᴮ n) ≡ ⊥ᴮ
    ∈ᴮ-empty m n e =
      ≤ᴮ-antisym (∈ᴮ-lub m n ⊥ᴮ (λ x h → Empty.rec* (e x h)))
                 (⊥-least (m ∈ᴮ n))

    ----------------------------------------------------------------------------
    -- Corollary 1.18: the bounded quantifiers
    ----------------------------------------------------------------------------

    -- Bell's 1.18 equates the value of a bounded quantification with a join or
    -- a meet over the support of the bound. His proof of (i) runs through the
    -- UNBOUNDED join over the whole class of names, which K4 does not have and
    -- must not pretend to have: there is no join indexed by a class here, only
    -- joins of families realized as ground sets (R5, and CodedCompletion.agda
    -- :899-913 takes a supremum only of a realized family).
    --
    -- What survives, and what the compiler of K4.5 actually consumes, is the
    -- comparison of the two families WITHOUT either join: the bounded family
    -- over the support of u and the unbounded family over every code have
    -- exactly the same upper bounds, and dually the same lower bounds. That is
    -- a universal property statement in the sense of R3, it is stronger than
    -- an equation between two constructed joins because it implies that
    -- equation whenever both joins exist, and it costs no infinitary law.
    --
    -- The hypothesis on the family is 1.17(vii) at the formula in question,
    -- which is the only thing Bell's proof uses about φ. Track F discharges it
    -- for a compiled formula by induction; Track D states it as a hypothesis
    -- because the atomic layer has no formulas.

    Congruent : (S → Pt B) → Type ℓ
    Congruent φ = (x y : S) → ⟨ ((x ≈ᴮ y) ⊓ᴮ φ x) ≤ᴮ φ y ⟩

    -- (i), the harder half: an upper bound of the bounded family bounds every
    -- term of the unbounded one. Bell's line is "using 1.17(vii)" at
    -- fulltext:2196; here the membership value's own least upper bound
    -- property does the work the unbounded join did for him.

    bounded-∃-ub : (u : S) (φ : S → Pt B) → Congruent φ → (c : Pt B)
                 → ((x : S) → ⟨ x ∈ˢ support u ⟩
                    → ⟨ ((weightᴮ u x) ⊓ᴮ φ x) ≤ᴮ c ⟩)
                 → (y : S) → ⟨ ((y ∈ᴮ u) ⊓ᴮ φ y) ≤ᴮ c ⟩
    bounded-∃-ub u φ cong c bound y =
      ⇒ᴮ-uncurry (y ∈ᴮ u) (φ y) c curried
      where
      inner : (x : S) → ⟨ x ∈ˢ support u ⟩
            → ⟨ ((((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x))) ⊓ᴮ φ y) ≤ᴮ c ⟩
      inner x hx =
        ⊆ˢ-trans
          (⊓-glb (weightᴮ u x) (φ x) (((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) ⊓ᴮ φ y)
            (⊆ˢ-trans (⊓-lb₁ ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) (φ y))
                      (⊓-lb₁ (weightᴮ u x) (y ≈ᴮ x)))
            (⊆ˢ-trans
              (⊓-glb (y ≈ᴮ x) (φ y) (((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) ⊓ᴮ φ y)
                (⊆ˢ-trans (⊓-lb₁ ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) (φ y))
                          (⊓-lb₂ (weightᴮ u x) (y ≈ᴮ x)))
                (⊓-lb₂ ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) (φ y)))
              (cong y x)))
          (bound x hx)
      curried : ⟨ (y ∈ᴮ u) ≤ᴮ (φ y ⇒ᴮ c) ⟩
      curried = ∈ᴮ-lub y u (φ y ⇒ᴮ c)
                  (λ x hx → ⇒ᴮ-curry ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) (φ y) c
                                     (inner x hx))

    -- (i), the easy half, and the reason the two families have the SAME upper
    -- bounds rather than merely comparable ones: 1.17(ii) puts each weight
    -- below the corresponding membership value.

    bounded-∃-lb : (u : S) (φ : S → Pt B) (c : Pt B)
                 → ((y : S) → ⟨ ((y ∈ᴮ u) ⊓ᴮ φ y) ≤ᴮ c ⟩)
                 → (x : S) → ⟨ x ∈ˢ support u ⟩
                 → ⟨ ((weightᴮ u x) ⊓ᴮ φ x) ≤ᴮ c ⟩
    bounded-∃-lb u φ c bound x hx =
      ⊆ˢ-trans (⊓ᴮ-mono (weightᴮ u x) (x ∈ᴮ u) (φ x) (φ x)
                        (weight-≤ u x hx) (≤ᴮ-refl (φ x)))
               (bound x)

    -- (ii), by the dual argument rather than by a duality principle: K4 has no
    -- De Morgan law for an indexed family and must not acquire one, so the
    -- infimum half is proved the same way as the supremum half with the
    -- implication in place of the meet.

    bounded-∀-lb : (u : S) (φ : S → Pt B) → Congruent φ → (c : Pt B)
                 → ((x : S) → ⟨ x ∈ˢ support u ⟩
                    → ⟨ c ≤ᴮ ((weightᴮ u x) ⇒ᴮ φ x) ⟩)
                 → (y : S) → ⟨ c ≤ᴮ ((y ∈ᴮ u) ⇒ᴮ φ y) ⟩
    bounded-∀-lb u φ cong c bound y =
      ⇒ᴮ-curry c (y ∈ᴮ u) (φ y)
        (⊓-swap (y ∈ᴮ u) c (φ y) (⇒ᴮ-uncurry (y ∈ᴮ u) c (φ y) curried))
      where
      inner : (x : S) → ⟨ x ∈ˢ support u ⟩
            → ⟨ ((((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x))) ⊓ᴮ c) ≤ᴮ φ y ⟩
      inner x hx =
        ⊆ˢ-trans
          (⊓-glb (x ≈ᴮ y) (φ x) (((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) ⊓ᴮ c)
            (subst (λ z → ⟨ (((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) ⊓ᴮ c) ≤ᴮ z ⟩)
                   (≈ᴮ-sym y x)
                   (⊆ˢ-trans (⊓-lb₁ ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) c)
                             (⊓-lb₂ (weightᴮ u x) (y ≈ᴮ x))))
            (⊆ˢ-trans
              (⊓-glb c (weightᴮ u x) (((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) ⊓ᴮ c)
                (⊓-lb₂ ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) c)
                (⊆ˢ-trans (⊓-lb₁ ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) c)
                          (⊓-lb₁ (weightᴮ u x) (y ≈ᴮ x))))
              (⇒ᴮ-uncurry c (weightᴮ u x) (φ x) (bound x hx))))
          (cong x y)
      curried : ⟨ (y ∈ᴮ u) ≤ᴮ (c ⇒ᴮ φ y) ⟩
      curried = ∈ᴮ-lub y u (c ⇒ᴮ φ y)
                  (λ x hx → ⇒ᴮ-curry ((weightᴮ u x) ⊓ᴮ (y ≈ᴮ x)) c (φ y)
                                     (inner x hx))

    bounded-∀-ub : (u : S) (φ : S → Pt B) (c : Pt B)
                 → ((y : S) → ⟨ c ≤ᴮ ((y ∈ᴮ u) ⇒ᴮ φ y) ⟩)
                 → (x : S) → ⟨ x ∈ˢ support u ⟩
                 → ⟨ c ≤ᴮ ((weightᴮ u x) ⇒ᴮ φ x) ⟩
    bounded-∀-ub u φ c bound x hx =
      ⇒ᴮ-curry c (weightᴮ u x) (φ x)
        (⊆ˢ-trans (⊓ᴮ-mono c c (weightᴮ u x) (x ∈ᴮ u)
                           (≤ᴮ-refl c) (weight-≤ u x hx))
                  (⇒ᴮ-uncurry c (x ∈ᴮ u) (φ x) (bound x)))
