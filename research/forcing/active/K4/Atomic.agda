{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track C: the two Boolean-valued atomic relations on K3's names.
--
-- Section 1.4 of the K4 architecture. The mathematical content is Bell's
-- (1.15) and (1.16), read on a MATERIAL name: a name is a ground code whose
-- members are Kuratowski entries, its domain is Track B's support, and the
-- weight of a subname is Track E's join weightᴮ. The file defines the equality
-- value _≈ᴮ_ by recursion on the kernel's pair recursor and the membership
-- value _∈ᴮ_ from it, and ships each of them only through universal
-- properties.
--
-- WHY THE EQUATION IS THE EXPANDED SYMMETRIC ONE, AND NOT BELL'S. Bell defines
-- the two values by recursion on the relation
--
--   <x, y> < <u, v>  iff  (x in dom u and y = v) or (x = u and y in dom v)
--
-- (fulltext:2026), which holds ONE coordinate fixed. The kernel's pair
-- recursor does not offer that. Its step type is
--
--   (x y : S) -> ((u v : S) -> Child u x -> Child v y -> P u v) -> P x y
--
-- (NameKernel.agda:414-416, verified here), so the recursive value is
-- available only where BOTH coordinates descend. Bell's second conjunct
-- [v(y) => value of y in u] therefore cannot be written as stated: it needs
-- the value of y in u, which by (1.15) is a join over dom u of terms
-- [u(x) and value of y = x], and that call has the two arguments EXCHANGED
-- relative to the first conjunct. The equation this file takes as the
-- definition expands both conjuncts and writes both recursive calls in the
-- SAME argument order:
--
--   value of m = n
--     = (meet over x in supp m) [ w m x => (join over y in supp n)
--                                          ( w n y and value of x = y ) ]
--     and
--       (meet over y in supp n) [ w n y => (join over x in supp m)
--                                          ( w m x and value of x = y ) ]
--
-- Every recursive call is at a child of m paired with a child of n, which is
-- exactly what the recursor supplies. Bell's (1.15) is then the DEFINITION of
-- _∈ᴮ_, and Bell's (1.16) is recovered as a theorem once symmetry is proved:
-- the first conjunct is already [w m x => value of x in n], and the second
-- becomes [w n y => value of y in m] only after the exchange is licensed.
-- Both forms are shipped here, the raw one unconditionally and Bell's after
-- ≈ᴮ-sym below.
--
-- WHY EVERY VALUE FACT IS A UNIVERSAL PROPERTY. Project rule R3: a
-- DECLARATION, not a term, can fail to elaborate in bounded time when its type
-- contains a construction of one layer applied to a term of another. Measured
-- kills at 19 min 35 s, about 11 min twice, 2 min 09 s and a 360 s wall. So no
-- exported type in this file names a join or a meet of a constructed set. The
-- exported interface of the two values is five order statements plus the two
-- mirror statements, and the only operations in them are the module's own
-- parameters.
--
-- WHY THE NAME LAYER IS FLAT AND THE ALGEBRA IS NOT. Project rule R2: a
-- module parameter is a tighter seal than an opaque block, being a variable
-- that cannot unfold. So the kernel, the support, the weight and the value
-- sets enter as bare operations with bare laws, and no K1, K2 or K3 module is
-- imported at all: the file compiles against SHAPES and Track B may finish
-- after it.
--
-- The Boolean algebra is the exception, and the reason is not elaboration but
-- composition. RECORDS ARE GENERATIVE: two structurally identical record
-- declarations are two incompatible types, so a track that declares its own
-- Lattice stops the package composing the moment a second one does. The three
-- algebra records therefore have exactly one home, Track A's K4/Algebra.agda,
-- and this file takes them as the parameters (B) (L) (Cm) (Kc) that
-- architecture section 1.4 prints. Nothing is lost to R2 by that: a field
-- projected out of a record VARIABLE is as rigid as a bare parameter.
--
-- WHAT IS SEALED. Two opaque blocks, each carrying its own specification at
-- the point of definition, which is the idiom of NameKernel.agda:203-208 and
-- NameWeight.agda:203-216. The first seals the indexed join and meet together
-- with their four universal properties; the second seals _≈ᴮ_, _∈ᴮ_ and the
-- mirrored membership together with everything that has to see them unfold.
-- Nothing outside the second block ever unfolds a value.
--
-- WHAT DOES NOT APPEAR. IsName occurs in no signature: support is total
-- (NameSupport.agda:514) and weightᴮ is total (NameWeight.agda:204), so both
-- values are defined on arbitrary ground codes, exactly as Valuation.agda:285
-- defines its own. There is no Separation, no Collection, no PowerSet, no LEM,
-- no filter and no genericity. The algebra's own negation ¬_ is hidden at the
-- open, so lesson 3 is mechanical rather than promised.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication

module K4.Atomic {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

-- ---------------------------------------------------------------------
-- The algebra layer, imported and never re-declared
-- ---------------------------------------------------------------------

-- RECORDS ARE GENERATIVE. Two structurally identical record declarations are
-- two incompatible types, so the three algebra records have exactly one home,
-- K4/Algebra.agda, and this file declares none of its own. The point type and
-- the order come from there as well, although those are plain definitions and
-- would have unfolded to the same types either way.
--
-- Track A's scope contract is observed: K4.Algebra is opened HERE for the
-- record types and the point vocabulary, K4.Implication is opened inside the
-- telescope below for the theory, and neither is re-exported. Re-exporting a
-- record TYPE name makes its record module reachable twice and a consumer
-- that opens both routes fails with AmbiguousModule.

open K4.Algebra 𝒮
  using ( Pt; _≤ᴮ_; ⊆ˢ-trans; Lattice; Complement; CodedComplete )

-- The two crossings between the structure equality and the host path. They
-- sit here rather than in the telescope because they depend on nothing but
-- the realization hypothesis, and they are spent in exactly two lemmas.

≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
≈ˢ-refl x = subst ⟨_⟩ (sym (paths x x)) refl

-- ---------------------------------------------------------------------
-- The atomic layer
-- ---------------------------------------------------------------------

-- The telescope is the whole ledger of this file. Reading it top to bottom:
-- five Boolean operations and six Boolean laws, three value set fields, one
-- path realization, four kernel fields, two support fields and one weight
-- field. Nothing else is consumed and nothing else may be added, because
-- every addition is a hypothesis the instance has to pay.

module Atomic
  -- The Boolean algebra, as Track A's records. Not as loose operations and
  -- not as records of this file's own: architecture section 1.4's telescope,
  -- (B) (L) (Cm) (Kc), verbatim.
  (B  : S)
  (L  : Lattice B)
  (Cm : Complement B L)
  (Kc : CodedComplete B L)
  -- Track B's ValueSets, field for field and flat. Flat rather than as the
  -- record because Track B has not reported as this file is written, and a
  -- flat field list creates no second type: the three parameters below are
  -- exactly K4.ValueSets.Core.ValueSets's three fields, with its ValueClass
  -- (a transparent definition) written out, so the coordinator passes
  -- ValueSets.attain vs, ValueSets.attain-sub vs, ValueSets.attain-spec vs
  -- with no adaptation.
  (attain      : (a : S) (f : Pt a → Pt B) → S)
  (attain-sub  : (a : S) (f : Pt a → Pt B) → ⟨ attain a f ⊆ˢ B ⟩)
  (attain-spec : (a : S) (f : Pt a → Pt B) (b : S)
               → (b ∈ˢ attain a f)
               ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → b ≈ˢ fst (f (x , h)))))
  -- The kernel, flat.
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (rawPairRec  : (P : S → S → Type ℓ)
               → ((x y : S) → ((u v : S) → Child u x → Child v y → P u v) → P x y)
               → (x y : S) → P x y)
  (rawPairComp : (P : S → S → Type ℓ)
               → (st : (x y : S)
                     → ((u v : S) → Child u x → Child v y → P u v) → P x y)
               → (x y : S)
               → rawPairRec P st x y ≡ st x y (λ u v _ _ → rawPairRec P st u v))
  -- The support, flat. Only the outward direction is taken: support-in needs
  -- ⟨ IsName n ⟩ and no statement below has one.
  (support     : S → S)
  (support-out : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n)
  -- The weight, flat. Its two universal properties are Track D's business,
  -- not this file's: nothing here reads a weight, it only places it.
  (weightᴮ : (n x : S) → Pt B)
  where

  -- The lattice operations and the two coded joins, and from Track A's
  -- theory module exactly two names: the implication, used with no law at
  -- all, and commutativity of the meet, used once. Neither module is
  -- re-exported.

  open Lattice L
  open CodedComplete Kc
  open K4.Implication 𝒮 ext paths B L Cm using ( _⇒ᴮ_; ⊓-comm )

  -- -------------------------------------------------------------------
  -- The index of a family over a support, and witness independence
  -- -------------------------------------------------------------------

  Supᴺ : S → Type ℓ
  Supᴺ n = Pt (support n)

  -- A member of the support is a child, and this is the only way an edge is
  -- ever obtained below. It is total: support-out carries no name premise.

  edge : (n : S) (p : Supᴺ n) → Child (fst p) n
  edge n p = support-out n (fst p) (snd p)

  Rec : S → S → Type ℓ
  Rec m n = (u v : S) → Child u m → Child v n → Pt B

  -- WITNESS INDEPENDENCE, named once. The step consumes the membership
  -- witness through support-out, so a value built from it could in principle
  -- depend on which witness was supplied. It does not, and Child being a
  -- proposition is the whole proof. Stated rather than inlined because it is
  -- the hypothesis under which ∃-prop (StandardNames.agda:120-123) applies to
  -- a family of this shape, and because closing the gap with a bare cong at
  -- the point of use is R1's failure shape.

  child-indep : (n x : S) (h h' : ⟨ x ∈ˢ support n ⟩)
              → support-out n x h ≡ support-out n x h'
  child-indep n x h h' = isPropChild x n (support-out n x h) (support-out n x h')

  step-indep : (m n : S) (r : Rec m n) (x y : S)
               (h h' : ⟨ x ∈ˢ support m ⟩) (k k' : ⟨ y ∈ˢ support n ⟩)
             → r x y (support-out m x h) (support-out n y k)
             ≡ r x y (support-out m x h') (support-out n y k')
  step-indep m n r x y h h' k k' =
      cong (λ e → r x y e (support-out n y k)) (child-indep m x h h')
    ∙ cong (λ e → r x y (support-out m x h') e) (child-indep n y k k')

  -- -------------------------------------------------------------------
  -- The indexed join and meet, sealed with their universal properties
  -- -------------------------------------------------------------------

  -- Track B hands over a value SET, a ground code whose members are exactly
  -- the values of the family. What the atomic layer needs is not that code
  -- but the element it joins to, characterized by its universal property.
  -- The two lemmas below are the whole bridge, and they are the only place
  -- where attain-spec and the path realization are spent.

  in-attain : (a : S) (f : Pt a → Pt B) (p : Pt a)
            → ⟨ fst (f p) ∈ˢ attain a f ⟩
  in-attain a f p =
    subst ⟨_⟩ (sym (attain-spec a f (fst (f p))))
      ∣ fst p , ∣ snd p , ≈ˢ-refl (fst (f p)) ∣₁ ∣₁

  from-attain : (a : S) (f : Pt a → Pt B) (c : Pt B)
              → ((p : Pt a) → ⟨ f p ≤ᴮ c ⟩)
              → (u : Pt B) → ⟨ fst u ∈ˢ attain a f ⟩ → ⟨ u ≤ᴮ c ⟩
  from-attain a f c hyp u hu =
    PT.rec (snd (u ≤ᴮ c))
      (λ { (x , inner) → PT.rec (snd (u ≤ᴮ c))
             (λ { (h , e) →
                    subst (λ z → ⟨ z ⊆ˢ fst c ⟩) (sym (≈→≡ e)) (hyp (x , h)) })
             inner })
      (subst ⟨_⟩ (attain-spec a f (fst u)) hu)

  from-attain⁻ : (a : S) (f : Pt a → Pt B) (c : Pt B)
               → ((p : Pt a) → ⟨ c ≤ᴮ f p ⟩)
               → (u : Pt B) → ⟨ fst u ∈ˢ attain a f ⟩ → ⟨ c ≤ᴮ u ⟩
  from-attain⁻ a f c hyp u hu =
    PT.rec (snd (c ≤ᴮ u))
      (λ { (x , inner) → PT.rec (snd (c ≤ᴮ u))
             (λ { (h , e) →
                    subst (λ z → ⟨ fst c ⊆ˢ z ⟩) (sym (≈→≡ e)) (hyp (x , h)) })
             inner })
      (subst ⟨_⟩ (attain-spec a f (fst u)) hu)

  -- THE SEAL, first block. joinOf and meetOf are description operator terms
  -- twice over: attain is a separation and supᴮ is a double pseudocomplement
  -- of a union. Nothing below ever needs either unfolding, because the four
  -- universal properties determine the element, so the block costs no proof
  -- and removes both spines from every conversion check in the file.

  opaque
    joinOf : (a : S) (f : Pt a → Pt B) → Pt B
    joinOf a f = supᴮ (attain a f) (attain-sub a f)

    meetOf : (a : S) (f : Pt a → Pt B) → Pt B
    meetOf a f = infᴮ (attain a f) (attain-sub a f)

    joinOf-ub : (a : S) (f : Pt a → Pt B) (p : Pt a)
              → ⟨ f p ≤ᴮ joinOf a f ⟩
    joinOf-ub a f p =
      sup-ub (attain a f) (attain-sub a f) (f p) (in-attain a f p)

    joinOf-lub : (a : S) (f : Pt a → Pt B) (c : Pt B)
               → ((p : Pt a) → ⟨ f p ≤ᴮ c ⟩)
               → ⟨ joinOf a f ≤ᴮ c ⟩
    joinOf-lub a f c hyp =
      sup-lub (attain a f) (attain-sub a f) c (from-attain a f c hyp)

    meetOf-lb : (a : S) (f : Pt a → Pt B) (p : Pt a)
              → ⟨ meetOf a f ≤ᴮ f p ⟩
    meetOf-lb a f p =
      inf-lb (attain a f) (attain-sub a f) (f p) (in-attain a f p)

    meetOf-glb : (a : S) (f : Pt a → Pt B) (c : Pt B)
               → ((p : Pt a) → ⟨ c ≤ᴮ f p ⟩)
               → ⟨ c ≤ᴮ meetOf a f ⟩
    meetOf-glb a f c hyp =
      inf-glb (attain a f) (attain-sub a f) c (from-attain⁻ a f c hyp)

  -- -------------------------------------------------------------------
  -- The step of the recursion
  -- -------------------------------------------------------------------

  -- The expanded symmetric equation. Both conjuncts call r at (first
  -- coordinate from m, second coordinate from n), in that order; writing the
  -- second conjunct with the arguments exchanged, as Bell's printed (1.16)
  -- has them, is the one silent failure mode of this track, because the
  -- exchanged form is not a legal recursive call at all.

  stepᴮ : (m n : S) → Rec m n → Pt B
  stepᴮ m n r =
    meetOf (support m)
      (λ p → weightᴮ m (fst p) ⇒ᴮ
             joinOf (support n)
               (λ q → weightᴮ n (fst q) ⊓ᴮ
                      r (fst p) (fst q) (edge m p) (edge n q)))
    ⊓ᴮ
    meetOf (support n)
      (λ q → weightᴮ n (fst q) ⇒ᴮ
             joinOf (support m)
               (λ p → weightᴮ m (fst p) ⊓ᴮ
                      r (fst p) (fst q) (edge m p) (edge n q)))

  -- -------------------------------------------------------------------
  -- The two values
  -- -------------------------------------------------------------------

  -- THE SEAL, second block. Everything that has to see a value unfold lives
  -- inside it, and nothing outside it does. The block is long on purpose: the
  -- alternative is an unfolding declaration in every consumer, which is the
  -- shape K0 measured as not compiling.

  opaque

    -- The equality value, by recursion on the pair kernel.

    _≈ᴮ_ : S → S → Pt B
    _≈ᴮ_ = rawPairRec (λ _ _ → Pt B) stepᴮ

    -- The membership value, DEFINED from equality and never mutually
    -- recursive with it. The dependency order is K0's
    -- (k0-material-names-value-sets:34) and the reason is structural: the
    -- pair kernel demands that both coordinates descend, and a mutual clause
    -- would call equality at (m, y) with m a child of nothing. This is
    -- Bell (1.15) taken as a definition; Valuation.agda:291-295 is the
    -- precedent on the Ω valued side.

    _∈ᴮ_ : S → S → Pt B
    m ∈ᴮ n = joinOf (support n) (λ q → weightᴮ n (fst q) ⊓ᴮ (m ≈ᴮ (fst q)))

    -- The MIRRORED membership value. It is the inner join of the second
    -- conjunct of the step, and it differs from _∈ᴮ_ only in the order of the
    -- two arguments of the recursive call. It is a separate definition rather
    -- than a use of _∈ᴮ_ because the two are equal only after symmetry, and
    -- asserting the identification at definition time would be a well typed
    -- false step of exactly the kind R4's repair note warns about.

    _∈ᴮᵒ_ : S → S → Pt B
    y ∈ᴮᵒ m = joinOf (support m) (λ p → weightᴮ m (fst p) ⊓ᴮ ((fst p) ≈ᴮ y))

    -- The two families of the step, named so that the unfolding statement and
    -- every characterization speak about the same two terms.

    famL : (m n : S) → Supᴺ m → Pt B
    famL m n p = weightᴮ m (fst p) ⇒ᴮ ((fst p) ∈ᴮ n)

    famR : (m n : S) → Supᴺ n → Pt B
    famR m n q = weightᴮ n (fst q) ⇒ᴮ ((fst q) ∈ᴮᵒ m)

    leftᴮ : (m n : S) → Pt B
    leftᴮ m n = meetOf (support m) (famL m n)

    rightᴮ : (m n : S) → Pt B
    rightᴮ m n = meetOf (support n) (famR m n)

    -- THE UNFOLDING. The computation law of a well founded recursion is
    -- propositional and never definitional, so this path is the only way into
    -- the value and every characterization below transports through it
    -- exactly once. After the five characterizations it is never used again,
    -- which is the discipline Valuation.agda:322-329 records.

    ≈ᴮ-step : (m n : S) → (m ≈ᴮ n) ≡ ((leftᴮ m n) ⊓ᴮ (rightᴮ m n))
    ≈ᴮ-step = rawPairComp (λ _ _ → Pt B) stepᴮ

    -- Bell (1.15) as a universal property. The value of m in n is the least
    -- upper bound of the weighted equality values over the support of n.

    ∈ᴮ-ub : (m n x : S) → ⟨ x ∈ˢ support n ⟩
          → ⟨ (weightᴮ n x ⊓ᴮ (m ≈ᴮ x)) ≤ᴮ (m ∈ᴮ n) ⟩
    ∈ᴮ-ub m n x h =
      joinOf-ub (support n) (λ q → weightᴮ n (fst q) ⊓ᴮ (m ≈ᴮ (fst q))) (x , h)

    ∈ᴮ-lub : (m n : S) (c : Pt B)
           → ((x : S) → ⟨ x ∈ˢ support n ⟩
              → ⟨ (weightᴮ n x ⊓ᴮ (m ≈ᴮ x)) ≤ᴮ c ⟩)
           → ⟨ (m ∈ᴮ n) ≤ᴮ c ⟩
    ∈ᴮ-lub m n c hyp =
      joinOf-lub (support n) (λ q → weightᴮ n (fst q) ⊓ᴮ (m ≈ᴮ (fst q))) c
        (λ q → hyp (fst q) (snd q))

    -- The same pair for the mirrored value.

    ∈ᴮᵒ-ub : (y m x : S) → ⟨ x ∈ˢ support m ⟩
           → ⟨ (weightᴮ m x ⊓ᴮ (x ≈ᴮ y)) ≤ᴮ (y ∈ᴮᵒ m) ⟩
    ∈ᴮᵒ-ub y m x h =
      joinOf-ub (support m) (λ p → weightᴮ m (fst p) ⊓ᴮ ((fst p) ≈ᴮ y)) (x , h)

    ∈ᴮᵒ-lub : (y m : S) (c : Pt B)
            → ((x : S) → ⟨ x ∈ˢ support m ⟩
               → ⟨ (weightᴮ m x ⊓ᴮ (x ≈ᴮ y)) ≤ᴮ c ⟩)
            → ⟨ (y ∈ᴮᵒ m) ≤ᴮ c ⟩
    ∈ᴮᵒ-lub y m c hyp =
      joinOf-lub (support m) (λ p → weightᴮ m (fst p) ⊓ᴮ ((fst p) ≈ᴮ y)) c
        (λ p → hyp (fst p) (snd p))

    -- The first conjunct of Bell (1.16), which needs no symmetry: the inner
    -- join of the left half IS the membership value, on the nose.

    ≈ᴮ-lbˡ : (m n x : S) → ⟨ x ∈ˢ support m ⟩
           → ⟨ (m ≈ᴮ n) ≤ᴮ (weightᴮ m x ⇒ᴮ (x ∈ᴮ n)) ⟩
    ≈ᴮ-lbˡ m n x h =
      subst (λ w → ⟨ w ≤ᴮ (weightᴮ m x ⇒ᴮ (x ∈ᴮ n)) ⟩) (sym (≈ᴮ-step m n))
        (⊆ˢ-trans
          (⊓-lb₁ (leftᴮ m n) (rightᴮ m n))
          (meetOf-lb (support m) (famL m n) (x , h)))

    -- The second conjunct, in the RAW form. This is what the recursion
    -- actually produces, and it is shipped unconditionally.

    ≈ᴮ-lbʳ-raw : (m n y : S) → ⟨ y ∈ˢ support n ⟩
               → ⟨ (m ≈ᴮ n) ≤ᴮ (weightᴮ n y ⇒ᴮ (y ∈ᴮᵒ m)) ⟩
    ≈ᴮ-lbʳ-raw m n y h =
      subst (λ w → ⟨ w ≤ᴮ (weightᴮ n y ⇒ᴮ (y ∈ᴮᵒ m)) ⟩) (sym (≈ᴮ-step m n))
        (⊆ˢ-trans
          (⊓-lb₂ (leftᴮ m n) (rightᴮ m n))
          (meetOf-lb (support n) (famR m n) (y , h)))

    ≈ᴮ-glb-raw : (m n : S) (c : Pt B)
               → ((x : S) → ⟨ x ∈ˢ support m ⟩
                  → ⟨ c ≤ᴮ (weightᴮ m x ⇒ᴮ (x ∈ᴮ n)) ⟩)
               → ((y : S) → ⟨ y ∈ˢ support n ⟩
                  → ⟨ c ≤ᴮ (weightᴮ n y ⇒ᴮ (y ∈ᴮᵒ m)) ⟩)
               → ⟨ c ≤ᴮ (m ≈ᴮ n) ⟩
    ≈ᴮ-glb-raw m n c h₁ h₂ =
      subst (λ w → ⟨ c ≤ᴮ w ⟩) (sym (≈ᴮ-step m n))
        (⊓-glb (leftᴮ m n) (rightᴮ m n) c
          (meetOf-glb (support m) (famL m n) c (λ p → h₁ (fst p) (snd p)))
          (meetOf-glb (support n) (famR m n) c (λ q → h₂ (fst q) (snd q))))

    -- -----------------------------------------------------------------
    -- Symmetry, and with it Bell (1.16) in its printed form
    -- -----------------------------------------------------------------

    -- Architecture item 5.4.5 asks whether symmetry can be had without an
    -- infinitary distributive law. It can, and the reason is the shape of the
    -- expanded equation rather than any property of the algebra: the two
    -- halves of the value at (m, n) are the two halves of the value at (n, m)
    -- in the other order, with the recursive calls exchanged, so the
    -- inductive hypothesis rewrites each family POINTWISE and the only
    -- algebraic fact spent is commutativity of the binary meet. No sup-cong,
    -- no inf-cong, no residuation, no distribution.

    -- The first half of that rewriting. Under the inductive hypothesis the
    -- membership value at a child of m agrees with its mirror.

    mirror : (m n : S)
           → ((u v : S) → Child u m → Child v n → (u ≈ᴮ v) ≡ (v ≈ᴮ u))
           → (x : S) → Child x m → (x ∈ᴮ n) ≡ (x ∈ᴮᵒ n)
    mirror m n ih x e =
      cong (joinOf (support n))
        (funExt (λ q → cong (weightᴮ n (fst q) ⊓ᴮ_)
                            (ih x (fst q) e (edge n q))))

    mirror⁻ : (m n : S)
            → ((u v : S) → Child u m → Child v n → (u ≈ᴮ v) ≡ (v ≈ᴮ u))
            → (y : S) → Child y n → (y ∈ᴮᵒ m) ≡ (y ∈ᴮ m)
    mirror⁻ m n ih y e =
      cong (joinOf (support m))
        (funExt (λ p → cong (weightᴮ m (fst p) ⊓ᴮ_)
                            (ih (fst p) y (edge m p) e)))

    symStep : (m n : S)
            → ((u v : S) → Child u m → Child v n → (u ≈ᴮ v) ≡ (v ≈ᴮ u))
            → (m ≈ᴮ n) ≡ (n ≈ᴮ m)
    symStep m n ih =
        ≈ᴮ-step m n
      ∙ cong (_⊓ᴮ (rightᴮ m n)) eqLeft
      ∙ cong ((rightᴮ n m) ⊓ᴮ_) eqRight
      ∙ ⊓-comm (rightᴮ n m) (leftᴮ n m)
      ∙ sym (≈ᴮ-step n m)
      where
        eqLeft : leftᴮ m n ≡ rightᴮ n m
        eqLeft =
          cong (meetOf (support m))
            (funExt (λ p → cong (weightᴮ m (fst p) ⇒ᴮ_)
                                (mirror m n ih (fst p) (edge m p))))

        eqRight : rightᴮ m n ≡ leftᴮ n m
        eqRight =
          cong (meetOf (support n))
            (funExt (λ q → cong (weightᴮ n (fst q) ⇒ᴮ_)
                                (mirror⁻ m n ih (fst q) (edge n q))))

    ≈ᴮ-sym : (m n : S) → (m ≈ᴮ n) ≡ (n ≈ᴮ m)
    ≈ᴮ-sym = rawPairRec (λ m n → (m ≈ᴮ n) ≡ (n ≈ᴮ m)) symStep

    -- The mirrored value collapses onto the real one, everywhere and with no
    -- hypothesis. This is the line that turns the raw second conjunct into
    -- Bell's printed one.

    ∈ᴮᵒ≡∈ᴮ : (y m : S) → (y ∈ᴮᵒ m) ≡ (y ∈ᴮ m)
    ∈ᴮᵒ≡∈ᴮ y m =
      cong (joinOf (support m))
        (funExt (λ p → cong (weightᴮ m (fst p) ⊓ᴮ_) (≈ᴮ-sym (fst p) y)))

    ≈ᴮ-lbʳ : (m n y : S) → ⟨ y ∈ˢ support n ⟩
           → ⟨ (m ≈ᴮ n) ≤ᴮ (weightᴮ n y ⇒ᴮ (y ∈ᴮ m)) ⟩
    ≈ᴮ-lbʳ m n y h =
      subst (λ w → ⟨ (m ≈ᴮ n) ≤ᴮ (weightᴮ n y ⇒ᴮ w) ⟩) (∈ᴮᵒ≡∈ᴮ y m)
        (≈ᴮ-lbʳ-raw m n y h)

    ≈ᴮ-glb : (m n : S) (c : Pt B)
           → ((x : S) → ⟨ x ∈ˢ support m ⟩
              → ⟨ c ≤ᴮ (weightᴮ m x ⇒ᴮ (x ∈ᴮ n)) ⟩)
           → ((y : S) → ⟨ y ∈ˢ support n ⟩
              → ⟨ c ≤ᴮ (weightᴮ n y ⇒ᴮ (y ∈ᴮ m)) ⟩)
           → ⟨ c ≤ᴮ (m ≈ᴮ n) ⟩
    ≈ᴮ-glb m n c h₁ h₂ =
      ≈ᴮ-glb-raw m n c h₁
        (λ y hy → subst (λ w → ⟨ c ≤ᴮ (weightᴮ n y ⇒ᴮ w) ⟩)
                        (sym (∈ᴮᵒ≡∈ᴮ y m)) (h₂ y hy))

  -- -------------------------------------------------------------------
  -- The contract the rest of K4 consumes
  -- -------------------------------------------------------------------

  -- Tracks D, F, H, I and J take this record and never this file, so none of
  -- them waits on the discharge of the telescope above. The field names carry
  -- a superscript A rather than the operator spellings, because a record
  -- field is brought into the enclosing scope as a projection and _≈ᴮ_ is
  -- already taken there.
  --
  -- The record lands at Type ℓ, not at Type (ℓ-suc ℓ) as section 1.4
  -- estimates: every field is a function into Pt B or into the carrier of a
  -- truth value, and both are Type ℓ. Nothing here is a path in Ω.

  record AtomicSemantics : Type ℓ where
    field
      eqᴬ  : S → S → Pt B
      memᴬ : S → S → Pt B
      memᴬ-ub  : (m n x : S) → ⟨ x ∈ˢ support n ⟩
               → ⟨ (weightᴮ n x ⊓ᴮ eqᴬ m x) ≤ᴮ memᴬ m n ⟩
      memᴬ-lub : (m n : S) (c : Pt B)
               → ((x : S) → ⟨ x ∈ˢ support n ⟩
                  → ⟨ (weightᴮ n x ⊓ᴮ eqᴬ m x) ≤ᴮ c ⟩)
               → ⟨ memᴬ m n ≤ᴮ c ⟩
      eqᴬ-lbˡ  : (m n x : S) → ⟨ x ∈ˢ support m ⟩
               → ⟨ eqᴬ m n ≤ᴮ (weightᴮ m x ⇒ᴮ memᴬ x n) ⟩
      eqᴬ-lbʳ  : (m n y : S) → ⟨ y ∈ˢ support n ⟩
               → ⟨ eqᴬ m n ≤ᴮ (weightᴮ n y ⇒ᴮ memᴬ y m) ⟩
      eqᴬ-glb  : (m n : S) (c : Pt B)
               → ((x : S) → ⟨ x ∈ˢ support m ⟩
                  → ⟨ c ≤ᴮ (weightᴮ m x ⇒ᴮ memᴬ x n) ⟩)
               → ((y : S) → ⟨ y ∈ˢ support n ⟩
                  → ⟨ c ≤ᴮ (weightᴮ n y ⇒ᴮ memᴬ y m) ⟩)
               → ⟨ c ≤ᴮ eqᴬ m n ⟩
      eqᴬ-sym  : (m n : S) → eqᴬ m n ≡ eqᴬ n m

  atomicSemantics : AtomicSemantics
  atomicSemantics = record
    { eqᴬ      = _≈ᴮ_
    ; memᴬ     = _∈ᴮ_
    ; memᴬ-ub  = ∈ᴮ-ub
    ; memᴬ-lub = ∈ᴮ-lub
    ; eqᴬ-lbˡ  = ≈ᴮ-lbˡ
    ; eqᴬ-lbʳ  = ≈ᴮ-lbʳ
    ; eqᴬ-glb  = ≈ᴮ-glb
    ; eqᴬ-sym  = ≈ᴮ-sym }

  -- The raw contract, for a consumer that would rather not carry symmetry as
  -- a standing fact: it is exactly what the recursion delivers before any
  -- exchange is licensed. Shipped so that a measured failure of the symmetry
  -- block would cost nothing downstream.

  record AtomicCore : Type ℓ where
    field
      eqᴬ   : S → S → Pt B
      memᴬ  : S → S → Pt B
      memᴬᵒ : S → S → Pt B
      memᴬ-ub   : (m n x : S) → ⟨ x ∈ˢ support n ⟩
                → ⟨ (weightᴮ n x ⊓ᴮ eqᴬ m x) ≤ᴮ memᴬ m n ⟩
      memᴬ-lub  : (m n : S) (c : Pt B)
                → ((x : S) → ⟨ x ∈ˢ support n ⟩
                   → ⟨ (weightᴮ n x ⊓ᴮ eqᴬ m x) ≤ᴮ c ⟩)
                → ⟨ memᴬ m n ≤ᴮ c ⟩
      memᴬᵒ-ub  : (y m x : S) → ⟨ x ∈ˢ support m ⟩
                → ⟨ (weightᴮ m x ⊓ᴮ eqᴬ x y) ≤ᴮ memᴬᵒ y m ⟩
      memᴬᵒ-lub : (y m : S) (c : Pt B)
                → ((x : S) → ⟨ x ∈ˢ support m ⟩
                   → ⟨ (weightᴮ m x ⊓ᴮ eqᴬ x y) ≤ᴮ c ⟩)
                → ⟨ memᴬᵒ y m ≤ᴮ c ⟩
      eqᴬ-lbˡ   : (m n x : S) → ⟨ x ∈ˢ support m ⟩
                → ⟨ eqᴬ m n ≤ᴮ (weightᴮ m x ⇒ᴮ memᴬ x n) ⟩
      eqᴬ-lbʳᵒ  : (m n y : S) → ⟨ y ∈ˢ support n ⟩
                → ⟨ eqᴬ m n ≤ᴮ (weightᴮ n y ⇒ᴮ memᴬᵒ y m) ⟩
      eqᴬ-glbᵒ  : (m n : S) (c : Pt B)
                → ((x : S) → ⟨ x ∈ˢ support m ⟩
                   → ⟨ c ≤ᴮ (weightᴮ m x ⇒ᴮ memᴬ x n) ⟩)
                → ((y : S) → ⟨ y ∈ˢ support n ⟩
                   → ⟨ c ≤ᴮ (weightᴮ n y ⇒ᴮ memᴬᵒ y m) ⟩)
                → ⟨ c ≤ᴮ eqᴬ m n ⟩

  atomicCore : AtomicCore
  atomicCore = record
    { eqᴬ       = _≈ᴮ_
    ; memᴬ      = _∈ᴮ_
    ; memᴬᵒ     = _∈ᴮᵒ_
    ; memᴬ-ub   = ∈ᴮ-ub
    ; memᴬ-lub  = ∈ᴮ-lub
    ; memᴬᵒ-ub  = ∈ᴮᵒ-ub
    ; memᴬᵒ-lub = ∈ᴮᵒ-lub
    ; eqᴬ-lbˡ   = ≈ᴮ-lbˡ
    ; eqᴬ-lbʳᵒ  = ≈ᴮ-lbʳ-raw
    ; eqᴬ-glbᵒ  = ≈ᴮ-glb-raw }
