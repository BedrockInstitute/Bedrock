{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track D, follow-up: Bell Theorem 1.20 and the ATOMIC HALF of Corollary
-- 1.21. The two Boolean atomic values computed in a complete subalgebra agree
-- with the same two values computed in the whole algebra.
--
-- WHY THIS IS K4'S AND NOT K6'S. The theorem is a simultaneous induction on the
-- ATOMIC values in two algebras, which is Track C's machinery and exists
-- nowhere else in the programme; K2's constraint is that a complete subalgebra
-- inclusion receives the JUSTIFIED atomic and bounded formula agreement rather
-- than arbitrary formula elementarity, so the justification is atomic. K6 keeps
-- the consequences. This file is deliberately SEPARATE from K4/AtomicLaws.agda
-- so that a failure here costs nothing already banked there.
--
-- WHAT IS PROVED AND WHAT IS NOT. Bell 1.20(ii) and (iii) in full, at
-- fulltext:2294-2304, for every pair of codes in a hereditary class carrying
-- the weight agreement. Bell 1.20(i), the inclusion of the two name classes,
-- is not a statement of this file: Track C's values are total on raw codes and
-- IsName appears in no signature, so there is no inclusion to prove, and the
-- class hypothesis below plays its role. Corollary 1.21 at fulltext:2305-2330
-- is delivered as its CLAUSE LIST and not as a formula induction: the atomic
-- clauses are 1.20, the connective clauses are the subalgebra record's own
-- fields, and the bounded quantifier clauses, which Bell names as the only
-- nontrivial step, are bounded-∃-ι and bounded-∀-ι below. There is no formula
-- type in this file and no induction on formula complexity; that induction is
-- Track G's and this file is what it will consume. Arbitrary formula
-- elementarity is not claimed by anyone.
--
-- THE HYPOTHESIS IS BELL'S, IN THE ONLY FORM K4 CAN STATE IT. Bell: "B′ is a
-- complete subalgebra of B if B′ is a subalgebra of B and, for any X ⊆ B′, the
-- join and the meet of X formed in B′ are the same as those formed in B"
-- (fulltext, the paragraph before 1.20). The subalgebra half is the record
-- Subalgebra, three equations. The completeness half is the record Complete,
-- and it is stated as a UNIVERSAL PROPERTY transfer rather than as an equation
-- between two constructed joins, which is project rule R3 applied by default:
-- no type in this file contains supᴮ or infᴮ at all, and CodedComplete is not
-- in the telescope. Read Complete as: a least upper bound formed in B′ is
-- still a least upper bound after inclusion, and dually.
--
-- WHY THAT HALF IS GENUINELY NEEDED, MEASURED BY WHERE IT IS SPENT. One
-- direction of each agreement is free and one is not. The inclusion of a bound
-- formed in B′ is always a bound in B, so the B-side universal property gives
-- one inequality with no hypothesis at all. The converse says the bound formed
-- in B lies in the image, and that is exactly what completeness of the
-- subalgebra asserts. Both are marked at their use sites below.
--
-- THE INDUCTION. Bell's hint carries THREE conclusions: for all y in dom(v)
-- and all u, the values of u ∈ y, u = y and y ∈ u agree. Under the expanded
-- symmetric equation, and with symmetry of the equality value available in
-- both algebras from Track C, ONE conclusion suffices: the equality agreement,
-- by a single coordinate induction with the second name universally quantified
-- inside the motive, and the two membership clauses are corollaries of the
-- join transfer. That is the same economy the transitivity proof in
-- K4/AtomicLaws.agda makes, and it is symmetry that pays for it there too.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import Cubical.Data.Sum as Sum

module K4.SubalgebraAgreement {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

-- Track A's scope contract. K4.Algebra is opened here for the record types and
-- the point vocabulary and is re-exported nowhere.
--
-- Note which names are taken once and serve BOTH algebras. Pt is indexed by
-- the carrier code, and _≤ᴮ_ is Certificate.agda's decision that the order is
-- inclusion of codes rather than a field of the lattice, so one order relation
-- covers both algebras and the inclusion below is order preserving and order
-- reflecting by definition rather than by proof. That single decision is what
-- makes this file short.

open K4.Algebra 𝒮
  using ( Pt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans; Lattice; Complement )

--------------------------------------------------------------------------------
-- Two algebras, one of them inside the other
--------------------------------------------------------------------------------

module Two
  (B' B : S)
  (sub  : ⟨ B' ⊆ˢ B ⟩)
  (L'   : Lattice B')   (Cm' : Complement B' L')
  (L    : Lattice B)    (Cm  : Complement B L)
  where

  -- The big algebra unqualified, the small one renamed. Neither module is
  -- re-exported. ≤ᴮ-antisym is taken once: its type is polymorphic in the
  -- carrier code and its proof consumes only ext and paths, never the lattice,
  -- so the copy obtained here serves the small algebra as well.

  open K4.Implication 𝒮 ext paths B L Cm
    using ( _⊓ᴮ_; _⊔ᴮ_; ¬ᴮ_; _⇒ᴮ_; ≤ᴮ-antisym )
  open K4.Implication 𝒮 ext paths B' L' Cm'
    using ()
    renaming ( _⊓ᴮ_ to _⊓'_ ; _⊔ᴮ_ to _⊔'_ ; ¬ᴮ_ to ¬'_ ; _⇒ᴮ_ to _⇒'_ )

  -- THE INCLUSION. A point of the small algebra is a code together with a
  -- proof that it is a member of the small carrier; the inclusion keeps the
  -- code and transports the membership proof. So fst (ι u) is fst u
  -- definitionally, and the two statements ⟨ u ≤ᴮ v ⟩ and ⟨ ι u ≤ᴮ ι v ⟩ are
  -- the SAME type. Both transfers below are the identity function, and they
  -- are written out rather than inlined because a reader has every right to
  -- expect a proof here and should be told there is none.

  ι : Pt B' → Pt B
  ι u = fst u , sub (fst u) (snd u)

  ≤-ι : (u v : Pt B') → ⟨ u ≤ᴮ v ⟩ → ⟨ (ι u) ≤ᴮ (ι v) ⟩
  ≤-ι u v h = h

  ≤-ι⁻ : (u v : Pt B') → ⟨ (ι u) ≤ᴮ (ι v) ⟩ → ⟨ u ≤ᴮ v ⟩
  ≤-ι⁻ u v h = h

  -- THE SUBALGEBRA HALF of Bell's hypothesis. Three equations, one per Boolean
  -- operation. The implication is NOT a field: K4/Implication.agda defines it
  -- as (¬ᴮ u) ⊔ᴮ v rather than declaring it, in both algebras, so its
  -- preservation is a theorem of the other three and is derived here once.

  record Subalgebra : Type ℓ where
    field
      ⊓-ι : (u v : Pt B') → ι (u ⊓' v) ≡ ((ι u) ⊓ᴮ (ι v))
      ⊔-ι : (u v : Pt B') → ι (u ⊔' v) ≡ ((ι u) ⊔ᴮ (ι v))
      ¬-ι : (u : Pt B') → ι (¬' u) ≡ (¬ᴮ (ι u))

    ⇒-ι : (u v : Pt B') → ι (u ⇒' v) ≡ ((ι u) ⇒ᴮ (ι v))
    ⇒-ι u v = ⊔-ι (¬' u) v ∙ cong (λ z → z ⊔ᴮ (ι v)) (¬-ι u)

  -- THE COMPLETENESS HALF. Bell asks that joins and meets of subsets of B′
  -- formed in B′ agree with those formed in B. Stated here as the transfer of
  -- the two universal properties, with the family indexed by an arbitrary
  -- small type: a least upper bound formed in the small algebra is still least
  -- among the upper bounds of the image, and dually.
  --
  -- This record lands at Type (ℓ-suc ℓ), because a field quantifies over
  -- I : Type ℓ. Architecture section 1.0's rule 1 therefore applies to it: it
  -- can never index a ⋀ or a ⋁. It never does; it is a hypothesis, exactly as
  -- Admits and Interp are.

  record Complete : Type (ℓ-suc ℓ) where
    field
      sup-ι : {I : Type ℓ} (f : I → Pt B') (c' : Pt B')
            → ((k : I) → ⟨ (f k) ≤ᴮ c' ⟩)
            → ((d : Pt B') → ((k : I) → ⟨ (f k) ≤ᴮ d ⟩) → ⟨ c' ≤ᴮ d ⟩)
            → (d : Pt B) → ((k : I) → ⟨ (ι (f k)) ≤ᴮ d ⟩) → ⟨ (ι c') ≤ᴮ d ⟩
      inf-ι : {I : Type ℓ} (f : I → Pt B') (c' : Pt B')
            → ((k : I) → ⟨ c' ≤ᴮ (f k) ⟩)
            → ((d : Pt B') → ((k : I) → ⟨ d ≤ᴮ (f k) ⟩) → ⟨ d ≤ᴮ c' ⟩)
            → (d : Pt B) → ((k : I) → ⟨ d ≤ᴮ (ι (f k)) ⟩) → ⟨ d ≤ᴮ (ι c') ⟩

  ------------------------------------------------------------------------------
  -- The agreement
  ------------------------------------------------------------------------------

  -- The telescope is the name layer once, the weights twice, and Track C's
  -- AtomicSemantics twice, field for field. That repetition is the content of
  -- the theorem: the SAME interface at two algebras, related only by the
  -- inclusion and by the weight agreement.
  --
  -- The class InB' is Bell's V (B′) and nothing more is asked of it than that
  -- it be hereditary along the support and that the weights of one of its
  -- members agree. An instance whose weight agreement is unconditional takes
  -- InB' to be the constantly true class and loses nothing.

  module Agreement
    (Child       : S → S → Type ℓ)
    (rawRec      : (P : S → Type ℓ)
                 → ((n : S) → ((x : S) → Child x n → P x) → P n)
                 → (n : S) → P n)
    (support     : S → S)
    (support-out : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n)
    (InB'        : S → Type ℓ)
    (InB'-child  : (n x : S) → InB' n → ⟨ x ∈ˢ support n ⟩ → InB' x)
    (weightᴮ'    : (n x : S) → Pt B')
    (weightᴮ     : (n x : S) → Pt B)
    (weight-ι    : (n x : S) → InB' n → ⟨ x ∈ˢ support n ⟩
                 → ι (weightᴮ' n x) ≡ weightᴮ n x)
    (sa : Subalgebra)
    (cp : Complete)
    -- Track C's AtomicSemantics at the SMALL algebra.
    (_≈'_ : S → S → Pt B')
    (_∈'_ : S → S → Pt B')
    (∈'-ub  : (m n x : S) → ⟨ x ∈ˢ support n ⟩
            → ⟨ ((weightᴮ' n x) ⊓' (m ≈' x)) ≤ᴮ (m ∈' n) ⟩)
    (∈'-lub : (m n : S) (c : Pt B')
            → ((x : S) → ⟨ x ∈ˢ support n ⟩
               → ⟨ ((weightᴮ' n x) ⊓' (m ≈' x)) ≤ᴮ c ⟩)
            → ⟨ (m ∈' n) ≤ᴮ c ⟩)
    (≈'-lbˡ : (m n x : S) → ⟨ x ∈ˢ support m ⟩
            → ⟨ (m ≈' n) ≤ᴮ ((weightᴮ' m x) ⇒' (x ∈' n)) ⟩)
    (≈'-lbʳ : (m n y : S) → ⟨ y ∈ˢ support n ⟩
            → ⟨ (m ≈' n) ≤ᴮ ((weightᴮ' n y) ⇒' (y ∈' m)) ⟩)
    (≈'-glb : (m n : S) (c : Pt B')
            → ((x : S) → ⟨ x ∈ˢ support m ⟩
               → ⟨ c ≤ᴮ ((weightᴮ' m x) ⇒' (x ∈' n)) ⟩)
            → ((y : S) → ⟨ y ∈ˢ support n ⟩
               → ⟨ c ≤ᴮ ((weightᴮ' n y) ⇒' (y ∈' m)) ⟩)
            → ⟨ c ≤ᴮ (m ≈' n) ⟩)
    (≈'-sym : (m n : S) → (m ≈' n) ≡ (n ≈' m))
    -- Track C's AtomicSemantics at the BIG algebra.
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

    open Subalgebra sa
    open Complete cp

    ----------------------------------------------------------------------------
    -- Transfer of one bound over a support
    ----------------------------------------------------------------------------

    -- Every agreement in this file is an instance of these two, and they are
    -- stated once with abstract families so that the atomic clauses and the
    -- bounded quantifier clauses of 1.21 are the same lemma twice.
    --
    -- Read join-ι as: if two families over the support of u correspond under
    -- the inclusion, and each has a least upper bound in its own algebra, then
    -- the two bounds correspond. The second inequality is the free one and the
    -- first is where completeness of the subalgebra is spent.

    join-ι : (u : S)
           → (f' : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B')
           → (f  : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B)
           → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ι (f' x hx) ≡ f x hx)
           → (c' : Pt B')
           → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ⟨ (f' x hx) ≤ᴮ c' ⟩)
           → ((d : Pt B') → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                             → ⟨ (f' x hx) ≤ᴮ d ⟩) → ⟨ c' ≤ᴮ d ⟩)
           → (c : Pt B)
           → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ⟨ (f x hx) ≤ᴮ c ⟩)
           → ((d : Pt B) → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                            → ⟨ (f x hx) ≤ᴮ d ⟩) → ⟨ c ≤ᴮ d ⟩)
           → ι c' ≡ c
    join-ι u f' f agree c' ub' lub' c ub lub = ≤ᴮ-antisym forward backward
      where
      -- The direction that needs Complete: the bound formed in the big algebra
      -- is reached from the small one only because the small bound stays least.
      forward : ⟨ (ι c') ≤ᴮ c ⟩
      forward = sup-ι {I = Pt (support u)}
                      (λ p → f' (fst p) (snd p)) c'
                      (λ p → ub' (fst p) (snd p))
                      (λ d hd → lub' d (λ x hx → hd (x , hx)))
                      c
                      (λ p → subst (λ z → ⟨ z ≤ᴮ c ⟩)
                                   (sym (agree (fst p) (snd p)))
                                   (ub (fst p) (snd p)))
      -- The free direction: the image of an upper bound is an upper bound.
      backward : ⟨ c ≤ᴮ (ι c') ⟩
      backward = lub (ι c')
                   (λ x hx → subst (λ z → ⟨ z ≤ᴮ (ι c') ⟩) (agree x hx)
                                   (≤-ι (f' x hx) c' (ub' x hx)))

    meet-ι : (u : S)
           → (f' : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B')
           → (f  : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B)
           → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ι (f' x hx) ≡ f x hx)
           → (c' : Pt B')
           → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ⟨ c' ≤ᴮ (f' x hx) ⟩)
           → ((d : Pt B') → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                             → ⟨ d ≤ᴮ (f' x hx) ⟩) → ⟨ d ≤ᴮ c' ⟩)
           → (c : Pt B)
           → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ⟨ c ≤ᴮ (f x hx) ⟩)
           → ((d : Pt B) → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                            → ⟨ d ≤ᴮ (f x hx) ⟩) → ⟨ d ≤ᴮ c ⟩)
           → ι c' ≡ c
    meet-ι u f' f agree c' lb' glb' c lb glb = ≤ᴮ-antisym forward backward
      where
      -- Here the FREE direction is the first one: the image of a lower bound
      -- is a lower bound, so the greatest lower bound in the big algebra is
      -- above it.
      forward : ⟨ (ι c') ≤ᴮ c ⟩
      forward = glb (ι c')
                  (λ x hx → subst (λ z → ⟨ (ι c') ≤ᴮ z ⟩) (agree x hx)
                                  (≤-ι c' (f' x hx) (lb' x hx)))
      backward : ⟨ c ≤ᴮ (ι c') ⟩
      backward = inf-ι {I = Pt (support u)}
                       (λ p → f' (fst p) (snd p)) c'
                       (λ p → lb' (fst p) (snd p))
                       (λ d hd → glb' d (λ x hx → hd (x , hx)))
                       c
                       (λ p → subst (λ z → ⟨ c ≤ᴮ z ⟩)
                                    (sym (agree (fst p) (snd p)))
                                    (lb (fst p) (snd p)))

    ----------------------------------------------------------------------------
    -- Membership agreement from local equality agreement
    ----------------------------------------------------------------------------

    -- Bell's (1.15) at the two algebras. The membership value is the least
    -- upper bound of the weighted equality family over the support, in each
    -- algebra separately, so the agreement of the two membership values needs
    -- the equality values to agree only at the members of that support.

    mem-ι : (m n : S) → InB' n
          → ((x : S) → ⟨ x ∈ˢ support n ⟩ → ι (m ≈' x) ≡ (m ≈ᴮ x))
          → ι (m ∈' n) ≡ (m ∈ᴮ n)
    mem-ι m n hn eqx =
      join-ι n (λ x _ → (weightᴮ' n x) ⊓' (m ≈' x))
               (λ x _ → (weightᴮ n x) ⊓ᴮ (m ≈ᴮ x))
               fam
               (m ∈' n) (λ x hx → ∈'-ub m n x hx)
                        (λ d hd → ∈'-lub m n d (λ x hx → hd x hx))
               (m ∈ᴮ n) (λ x hx → ∈ᴮ-ub m n x hx)
                        (λ d hd → ∈ᴮ-lub m n d (λ x hx → hd x hx))
      where
      fam : (x : S) (hx : ⟨ x ∈ˢ support n ⟩)
          → ι ((weightᴮ' n x) ⊓' (m ≈' x)) ≡ ((weightᴮ n x) ⊓ᴮ (m ≈ᴮ x))
      fam x hx = ⊓-ι (weightᴮ' n x) (m ≈' x)
               ∙ cong (λ z → z ⊓ᴮ (ι (m ≈' x))) (weight-ι n x hn hx)
               ∙ cong (λ z → (weightᴮ n x) ⊓ᴮ z) (eqx x hx)

    -- The exchange, as in the transitivity proof of K4/AtomicLaws.agda: an
    -- agreement read at swapped arguments, by the symmetry of the equality
    -- value in EACH algebra. This is what replaces the second and third
    -- conclusions of Bell's three part inductive hypothesis.

    mirror-ι : (x y : S) → ι (x ≈' y) ≡ (x ≈ᴮ y) → ι (y ≈' x) ≡ (y ≈ᴮ x)
    mirror-ι x y e = cong ι (≈'-sym y x) ∙ e ∙ sym (≈ᴮ-sym y x)

    ----------------------------------------------------------------------------
    -- Bell 1.20(iii): the equality values agree
    ----------------------------------------------------------------------------

    -- One single coordinate induction, the second name universally quantified
    -- inside the motive. Bell runs his on the second coordinate with three
    -- conclusions (fulltext:2301-2304); this runs on the first with one, and
    -- the membership clauses come back from mem-ι, the left one at a child of
    -- m and the right one at an arbitrary code through mirror-ι.

    eq-ι : (m : S) → InB' m → (n : S) → InB' n → ι (m ≈' n) ≡ (m ≈ᴮ n)
    eq-ι = rawRec (λ m → InB' m → (n : S) → InB' n → ι (m ≈' n) ≡ (m ≈ᴮ n)) step
      where
      step : (m : S)
           → ((x : S) → Child x m
              → InB' x → (n : S) → InB' n → ι (x ≈' n) ≡ (x ≈ᴮ n))
           → InB' m → (n : S) → InB' n → ι (m ≈' n) ≡ (m ≈ᴮ n)
      step m ih hm n hn = ≤ᴮ-antisym forward backward
        where
        ihx : (x : S) → ⟨ x ∈ˢ support m ⟩
            → (y : S) → InB' y → ι (x ≈' y) ≡ (x ≈ᴮ y)
        ihx x hx = ih x (support-out m x hx) (InB'-child m x hm hx)

        memL : (x : S) → ⟨ x ∈ˢ support m ⟩ → ι (x ∈' n) ≡ (x ∈ᴮ n)
        memL x hx = mem-ι x n hn
                      (λ y hy → ihx x hx y (InB'-child n y hn hy))

        memR : (y : S) → ⟨ y ∈ˢ support n ⟩ → ι (y ∈' m) ≡ (y ∈ᴮ m)
        memR y hy = mem-ι y m hm
                      (λ x hx → mirror-ι x y
                                  (ihx x hx y (InB'-child n y hn hy)))

        impL : (x : S) → ⟨ x ∈ˢ support m ⟩
             → ι ((weightᴮ' m x) ⇒' (x ∈' n))
             ≡ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n))
        impL x hx = ⇒-ι (weightᴮ' m x) (x ∈' n)
                  ∙ cong (λ z → z ⇒ᴮ (ι (x ∈' n))) (weight-ι m x hm hx)
                  ∙ cong (λ z → (weightᴮ m x) ⇒ᴮ z) (memL x hx)

        impR : (y : S) → ⟨ y ∈ˢ support n ⟩
             → ι ((weightᴮ' n y) ⇒' (y ∈' m))
             ≡ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m))
        impR y hy = ⇒-ι (weightᴮ' n y) (y ∈' m)
                  ∙ cong (λ z → z ⇒ᴮ (ι (y ∈' m))) (weight-ι n y hn hy)
                  ∙ cong (λ z → (weightᴮ n y) ⇒ᴮ z) (memR y hy)

        -- The free direction: the inclusion of a lower bound of the two
        -- families is a lower bound of their images, and the big algebra's
        -- equality value is the greatest such.
        forward : ⟨ (ι (m ≈' n)) ≤ᴮ (m ≈ᴮ n) ⟩
        forward = ≈ᴮ-glb m n (ι (m ≈' n)) fL fR
          where
          fL : (x : S) → ⟨ x ∈ˢ support m ⟩
             → ⟨ (ι (m ≈' n)) ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ⟩
          fL x hx = subst (λ z → ⟨ (ι (m ≈' n)) ≤ᴮ z ⟩) (impL x hx)
                          (≤-ι (m ≈' n) ((weightᴮ' m x) ⇒' (x ∈' n))
                               (≈'-lbˡ m n x hx))
          fR : (y : S) → ⟨ y ∈ˢ support n ⟩
             → ⟨ (ι (m ≈' n)) ≤ᴮ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ⟩
          fR y hy = subst (λ z → ⟨ (ι (m ≈' n)) ≤ᴮ z ⟩) (impR y hy)
                          (≤-ι (m ≈' n) ((weightᴮ' n y) ⇒' (y ∈' m))
                               (≈'-lbʳ m n y hy))

        -- The direction that spends Complete, and the one place where the two
        -- families of Bell's (1.16) have to be joined into one index: the
        -- equality value is the greatest lower bound of their UNION, so the
        -- transfer is applied at a sum type and not twice.
        Ix : Type ℓ
        Ix = (Pt (support m)) ⊎ (Pt (support n))

        fam : Ix → Pt B'
        fam (inl p) = (weightᴮ' m (fst p)) ⇒' ((fst p) ∈' n)
        fam (inr q) = (weightᴮ' n (fst q)) ⇒' ((fst q) ∈' m)

        lowerBound : (k : Ix) → ⟨ (m ≈' n) ≤ᴮ (fam k) ⟩
        lowerBound (inl p) = ≈'-lbˡ m n (fst p) (snd p)
        lowerBound (inr q) = ≈'-lbʳ m n (fst q) (snd q)

        greatest : (d : Pt B') → ((k : Ix) → ⟨ d ≤ᴮ (fam k) ⟩)
                 → ⟨ d ≤ᴮ (m ≈' n) ⟩
        greatest d hd = ≈'-glb m n d (λ x hx → hd (inl (x , hx)))
                                     (λ y hy → hd (inr (y , hy)))

        imageLower : (k : Ix) → ⟨ (m ≈ᴮ n) ≤ᴮ (ι (fam k)) ⟩
        imageLower (inl p) =
          subst (λ z → ⟨ (m ≈ᴮ n) ≤ᴮ z ⟩) (sym (impL (fst p) (snd p)))
                (≈ᴮ-lbˡ m n (fst p) (snd p))
        imageLower (inr q) =
          subst (λ z → ⟨ (m ≈ᴮ n) ≤ᴮ z ⟩) (sym (impR (fst q) (snd q)))
                (≈ᴮ-lbʳ m n (fst q) (snd q))

        backward : ⟨ (m ≈ᴮ n) ≤ᴮ (ι (m ≈' n)) ⟩
        backward = inf-ι {I = Ix} fam (m ≈' n) lowerBound greatest
                         (m ≈ᴮ n) imageLower

    ----------------------------------------------------------------------------
    -- Bell 1.20, as stated
    ----------------------------------------------------------------------------

    bell-1-20-iii : (m n : S) → InB' m → InB' n → ι (m ≈' n) ≡ (m ≈ᴮ n)
    bell-1-20-iii m n hm hn = eq-ι m hm n hn

    bell-1-20-ii : (m n : S) → InB' m → InB' n → ι (m ∈' n) ≡ (m ∈ᴮ n)
    bell-1-20-ii m n hm hn =
      mem-ι m n hn (λ x hx → eq-ι m hm x (InB'-child n x hn hx))

    ----------------------------------------------------------------------------
    -- Corollary 1.21, the atomic half: the clause list
    ----------------------------------------------------------------------------

    -- Bell proves 1.21 by induction on the complexity of φ and names exactly
    -- one nontrivial step, the bounded existential. There is no formula type in
    -- this file and no induction on one; what is delivered is every clause that
    -- induction consumes, so that the induction itself is arithmetic.
    --
    -- ATOMIC CLAUSES: bell-1-20-ii and bell-1-20-iii above.
    --
    -- CONNECTIVE CLAUSES: the three fields of Subalgebra and the derived ⇒-ι,
    -- restated here under names a formula induction will read off. They are
    -- hypotheses and not theorems, which is the correct status: they are what
    -- "subalgebra" means.

    clause-∧ : (a b : Pt B') → ι (a ⊓' b) ≡ ((ι a) ⊓ᴮ (ι b))
    clause-∧ = ⊓-ι

    clause-∨ : (a b : Pt B') → ι (a ⊔' b) ≡ ((ι a) ⊔ᴮ (ι b))
    clause-∨ = ⊔-ι

    clause-¬ : (a : Pt B') → ι (¬' a) ≡ (¬ᴮ (ι a))
    clause-¬ = ¬-ι

    clause-⇒ : (a b : Pt B') → ι (a ⇒' b) ≡ ((ι a) ⇒ᴮ (ι b))
    clause-⇒ = ⇒-ι

    -- BOUNDED QUANTIFIER CLAUSES, the step Bell calls the only nontrivial one.
    -- The value of a bounded quantification is not constructed here and must
    -- not be: it is Track F's node. What is taken instead is the node's own
    -- interface, the two universal properties at each algebra, which is
    -- exactly what Track F ships as the ∃-ub and ∃-lub clauses of InterpLaws
    -- (REPORT-B.md section 9). So this theorem is stated against Track F
    -- without waiting for it, and the coordinator wires the two by passing four
    -- projections.
    --
    -- The hypothesis on the two matrices is the agreement of the subformula's
    -- values at the members of the support, which is the inductive hypothesis
    -- of Bell's induction and nothing more.

    bounded-∃-ι : (u : S)
                → (ψ' : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B')
                → (ψ  : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B)
                → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ι (ψ' x hx) ≡ ψ x hx)
                → InB' u
                → (c' : Pt B')
                → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                   → ⟨ ((weightᴮ' u x) ⊓' (ψ' x hx)) ≤ᴮ c' ⟩)
                → ((d : Pt B') → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                     → ⟨ ((weightᴮ' u x) ⊓' (ψ' x hx)) ≤ᴮ d ⟩) → ⟨ c' ≤ᴮ d ⟩)
                → (c : Pt B)
                → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                   → ⟨ ((weightᴮ u x) ⊓ᴮ (ψ x hx)) ≤ᴮ c ⟩)
                → ((d : Pt B) → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                     → ⟨ ((weightᴮ u x) ⊓ᴮ (ψ x hx)) ≤ᴮ d ⟩) → ⟨ c ≤ᴮ d ⟩)
                → ι c' ≡ c
    bounded-∃-ι u ψ' ψ agree hu c' ub' lub' c ub lub =
      join-ι u (λ x hx → (weightᴮ' u x) ⊓' (ψ' x hx))
               (λ x hx → (weightᴮ u x) ⊓ᴮ (ψ x hx))
               fam c' ub' lub' c ub lub
      where
      fam : (x : S) (hx : ⟨ x ∈ˢ support u ⟩)
          → ι ((weightᴮ' u x) ⊓' (ψ' x hx)) ≡ ((weightᴮ u x) ⊓ᴮ (ψ x hx))
      fam x hx = ⊓-ι (weightᴮ' u x) (ψ' x hx)
               ∙ cong (λ z → z ⊓ᴮ (ι (ψ' x hx))) (weight-ι u x hu hx)
               ∙ cong (λ z → (weightᴮ u x) ⊓ᴮ z) (agree x hx)

    bounded-∀-ι : (u : S)
                → (ψ' : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B')
                → (ψ  : (x : S) → ⟨ x ∈ˢ support u ⟩ → Pt B)
                → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩) → ι (ψ' x hx) ≡ ψ x hx)
                → InB' u
                → (c' : Pt B')
                → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                   → ⟨ c' ≤ᴮ ((weightᴮ' u x) ⇒' (ψ' x hx)) ⟩)
                → ((d : Pt B') → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                     → ⟨ d ≤ᴮ ((weightᴮ' u x) ⇒' (ψ' x hx)) ⟩) → ⟨ d ≤ᴮ c' ⟩)
                → (c : Pt B)
                → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                   → ⟨ c ≤ᴮ ((weightᴮ u x) ⇒ᴮ (ψ x hx)) ⟩)
                → ((d : Pt B) → ((x : S) (hx : ⟨ x ∈ˢ support u ⟩)
                     → ⟨ d ≤ᴮ ((weightᴮ u x) ⇒ᴮ (ψ x hx)) ⟩) → ⟨ d ≤ᴮ c ⟩)
                → ι c' ≡ c
    bounded-∀-ι u ψ' ψ agree hu c' lb' glb' c lb glb =
      meet-ι u (λ x hx → (weightᴮ' u x) ⇒' (ψ' x hx))
               (λ x hx → (weightᴮ u x) ⇒ᴮ (ψ x hx))
               fam c' lb' glb' c lb glb
      where
      fam : (x : S) (hx : ⟨ x ∈ˢ support u ⟩)
          → ι ((weightᴮ' u x) ⇒' (ψ' x hx)) ≡ ((weightᴮ u x) ⇒ᴮ (ψ x hx))
      fam x hx = ⇒-ι (weightᴮ' u x) (ψ' x hx)
               ∙ cong (λ z → z ⇒ᴮ (ι (ψ' x hx))) (weight-ι u x hu hx)
               ∙ cong (λ z → (weightᴮ u x) ⇒ᴮ z) (agree x hx)
