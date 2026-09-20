{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track I: mixing, unique existence, and the FULLNESS CONTRACT.
--
-- Bell's Mixing Lemma 1.25 (fulltext:2484-2491, proof :2494-2520), Problem
-- 1.26(ii) (:2529-2540), the variant of the Maximum Principle without choice
-- that is Problem 1.29 (:2610-2617), and the boundary Problem 1.30 draws
-- (:2618-2640): THE MAXIMUM PRINCIPLE, UNIFORMLY OVER EVERY COMPLETE BOOLEAN
-- ALGEBRA, IS EQUIVALENT TO THE AXIOM OF CHOICE.
--
-- WHAT THIS FILE IS FOR, AND IT IS TWO THINGS AT ONCE.
--
-- First, the results that genuinely belong to K4. Mixing is a finite Boolean
-- argument about a family whose mixture is given by its universal property,
-- and it uses no choice and no completeness field. Unique existence is Bell's
-- Problem 1.29, which he sets precisely because it is the one case of the
-- Maximum Principle the axiom of choice is not needed for; here it is DATA
-- IN, DATA OUT, with no propositional truncation anywhere in the signature of
-- unique-witness, and that absence is the visible proof that nothing was
-- chosen.
--
-- Second, the CONTRACT for the results that do not belong here. Fullness and
-- the Maximum Principle are K12a's (roadmap:238). They are declared in this
-- file, they are never inhabited in this file, and the arrow K4 really does
-- own is proved: refinement→fullness discharges the WHOLE of Bell's proof of
-- Lemma 1.27 except its one appeal to choice, and MaximumPrincipleContract is
-- exactly that residue, isolated as a record with no inhabitant. In the other
-- direction fullness→element derives Bell's assertion Sigma(B) from fullness,
-- and Problem 1.30(ii) states that Sigma(B) for every complete Boolean
-- algebra is equivalent to the axiom of choice. So the two arrows fence the
-- gap on both sides and a typechecker enforces the fence: no function in this
-- file returns a Fullness, a MaximumPrinciple or a MaximumPrincipleContract
-- out of the algebra records alone.
--
-- THE ANSWER TO K7 IS NO, AND THIS COMMENT IS WHERE IT IS WRITTEN DOWN.
-- Architecture section 5.4.3 predicts that a K7 agent reading Bell will find
-- the Maximum Principle inside the source proof of 1.51(iv) (fulltext:3300)
-- and may ask K4 to export it. K4 does not export it and cannot: the
-- principle is not a consequence of Boolean completeness, it is a consequence
-- of choice, and exporting it from the completeness records would put the
-- axiom of choice into the ledger of every consumer of K4 without one of them
-- declaring it. The repair for 1.51(iv) named in that section is a truncated
-- elimination inside K7, because the goal there is that a Boolean value is
-- bottom, which is a proposition, with nonzero→positive
-- (CodedCompletion.agda:1314-1318) for the classical step. That repair needs
-- LEM and not choice, and it belongs to K7.
--
-- THE SECOND BOUNDARY, AND IT IS THE ONE A CONSUMER IS MOST LIKELY TO
-- MISREAD. The uniqueness hypothesis of Problem 1.29 is BOOLEAN equality of
-- names, never a path between names. BooleanUnique says the meet of two
-- values is below the Boolean equality value of the two names; it does not
-- say the names are equal. This file makes the distinction visible in the
-- TYPE and then measures it: raw-unique-collapses shows that reading
-- uniqueness raw at the canonical family IS the assertion that Boolean
-- equality implies a path, and boolean-unique-not-raw refutes that reading
-- outright from two names that are Boolean equal and raw distinct. The
-- intended supplier of those two names is Track H's zero-weight-boolean
-- together with K3's zero-distinct (NameKernel.agda:555-558), which K3
-- assigned to K4 by name as the checked statement that raw distinctness and
-- Boolean equality genuinely separate.
--
-- HYPOTHESIS LEDGER, AND THE TWO LISTS ARE DISJOINT WHERE THE MATHEMATICS
-- ALLOWS. The whole file runs on: the structure, ordinary Extensionality and
-- the path realization (spent on ≤ᴮ-antisym alone, exactly as in Tracks A, C
-- and D), Track A's Lattice and Complement through the implication
-- adjunction, four fields of Track C's AtomicSemantics and four of Track D's
-- laws. It takes NO Separation, NO Collection, NO PowerSet, NO LEM except as
-- an explicit argument of antichain→coherent and mixing-antichain, and NO
-- field of CodedComplete. That last one is not an oversight and it is worth
-- stating twice: mixing and unique existence are finite Boolean arguments
-- over universal properties, in the same way Track D measured the atomic laws
-- to be, so Boolean COMPLETENESS is not merely insufficient for the Maximum
-- Principle, it is not even used by the two theorems the principle would
-- generalize.
--
-- The architecture's permitted hypotheses for this track put Separation,
-- Collection and PowerSet on the unique existence half. Measured here: none
-- of the three is needed by unique-witness. They are needed to CONSTRUCT an
-- adequate domain and a witness name, and that construction is not proved
-- here either; see adequate-from-cover and the measured negative recorded
-- beside it.
--
-- NO INFINITE DISTRIBUTIVE LAW AND NO RESIDUATION. Bell's displayed proof of
-- 1.25 distributes a meet over an infinite join at fulltext:2510-2519.
-- Preamble rule R5 forbids that on Pt B. The replacement is the one the brief
-- names: the mixture's weight is given by its LEAST UPPER BOUND property, so
-- ⇒ᴮ-curry pushes the fixed factor across the bound and wt-lub discharges it
-- term by term. Neither of Track A's residual lemmas is used, so Track A's
-- refutation of the architecture's inf-residual (REPORT-A.md section 3) does
-- not touch this file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K4.Witnesses {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Data.Sum using ( inl; inr )
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

-- Track A's scope contract, observed. K4.Algebra is opened for the three
-- record types and the point vocabulary and is NOT re-exported: re-exporting
-- a record TYPE name makes its record module reachable by two routes and a
-- consumer that opens both fails with AmbiguousModule (REPORT-A.md section
-- 4). K4.Implication is opened inside Core, where B, L and Cm exist, and it
-- is not re-exported either. This file declares no algebra record of its own,
-- so the generativity hazard of REPORT-A.md section 8 does not arise.

open K4.Algebra 𝒮
  using ( Pt; isSetPt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

--------------------------------------------------------------------------------
-- The algebra and the name layer
--------------------------------------------------------------------------------

-- The algebra in architecture section 1.2's uniform shape, (B) (L) (Cm) (Kc),
-- so that the coordinator's application line reads the same for tracks C, D,
-- F and I. Kc is taken and never projected: measured, grep over the code
-- lines of this file returns 0 for each of supᴮ, infᴮ, sup-ub, sup-lub,
-- inf-lb and inf-glb. It is kept in the telescope for the uniform shape and
-- because a consumer holding the four records passes them positionally.
--
-- The name layer is FLAT and it is short. IsName is taken because Name is the
-- carrier of every statement below and because the fullness contract is
-- literally a truncated sigma over it; support and weightᴮ are taken because
-- Bell's mixture is specified by its domain and its weights. Nothing else of
-- K3 appears: no kernel, no recursor, no support-in, no weight law.

module Core
  (B  : S)
  (L  : Lattice B)
  (Cm : Complement B L)
  (Kc : CodedComplete B L)
  (IsName  : S → Ω)
  (support : S → S)
  (weightᴮ : (n x : S) → Pt B)
  where

  open Lattice L
  open K4.Implication 𝒮 ext paths B L Cm
    using ( ≤ᴮ-antisym; ⊓-comm; ⊓-idem; _⇒ᴮ_
          ; ⇒ᴮ-curry; ⇒ᴮ-uncurry; ⊓ᴮ-mono )

  -- A name is a code with the recogniser's certificate. The certificate is a
  -- proposition, so two names with the same code are equal, and Name is at
  -- Type ℓ: it can index a truncation and it can carry a family.

  Name : Type ℓ
  Name = Σ[ n ∈ S ] ⟨ IsName n ⟩

  -- Proof irrelevance is not definitional in this tree, and REPORT-B.md's
  -- trap T2 is the measured instance of it. A value family on names is
  -- applied here at two different certificates for the same code more than
  -- once, so the transport is named rather than inlined.

  name-irr : (v : Name → Pt B) (x : S) (h h' : ⟨ IsName x ⟩)
           → v (x , h) ≡ v (x , h')
  name-irr v x h h' = cong (λ q → v (x , q)) (snd (IsName x) h h')

  ------------------------------------------------------------------------------
  -- The atomic layer, flat
  ------------------------------------------------------------------------------

  -- Four of Track C's eight AtomicSemantics fields (K4/Atomic.agda:551-571)
  -- and four of Track D's laws. Not taken, and measured absent from every
  -- signature below: memᴬ-ub, memᴬ-lub, eqᴬ-lbˡ, eqᴬ-lbʳ, every congruence of
  -- the equality value, bell-1-15, bell-1-16 and the whole bounded quantifier
  -- calculus. The names carry the operator spellings rather than Track C's
  -- superscript A, exactly as Track D's Laws module does and for the same
  -- reason: a record field is brought into scope as a projection and nothing
  -- here takes those spellings.

  module Witness
    (_≈ᴮ_ : S → S → Pt B)
    (_∈ᴮ_ : S → S → Pt B)
    (≈ᴮ-glb : (m n : S) (c : Pt B)
            → ((x : S) → ⟨ x ∈ˢ support m ⟩
               → ⟨ c ≤ᴮ ((weightᴮ m x) ⇒ᴮ (x ∈ᴮ n)) ⟩)
            → ((y : S) → ⟨ y ∈ˢ support n ⟩
               → ⟨ c ≤ᴮ ((weightᴮ n y) ⇒ᴮ (y ∈ᴮ m)) ⟩)
            → ⟨ c ≤ᴮ (m ≈ᴮ n) ⟩)
    (≈ᴮ-sym   : (m n : S) → (m ≈ᴮ n) ≡ (n ≈ᴮ m))
    (≈ᴮ-refl  : (n : S) → (n ≈ᴮ n) ≡ ⊤ᴮ)
    (≈ᴮ-trans : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (m ≈ᴮ p) ⟩)
    (∈ᴮ-congʳ : (m n p : S) → ⟨ ((n ≈ᴮ p) ⊓ᴮ (m ∈ᴮ n)) ≤ᴮ (m ∈ᴮ p) ⟩)
    (weight-≤ : (n x : S) → ⟨ x ∈ˢ support n ⟩
              → ⟨ (weightᴮ n x) ≤ᴮ (x ∈ᴮ n) ⟩)
    where

    ----------------------------------------------------------------------------
    -- A small order toolkit
    ----------------------------------------------------------------------------

    -- The moves this file makes, named once rather than inlined at forty
    -- sites. Preamble rule R1's failure shape is a bare reflexivity standing
    -- in for an unchanged endpoint; every endpoint below is written out and
    -- no cong₂ occurs anywhere in this file.

    ⊓-swap : (a b c : Pt B) → ⟨ (a ⊓ᴮ b) ≤ᴮ c ⟩ → ⟨ (b ⊓ᴮ a) ≤ᴮ c ⟩
    ⊓-swap a b c h = subst (λ z → ⟨ z ≤ᴮ c ⟩) (⊓-comm a b) h

    ≡⊤ : (u : Pt B) → ⟨ ⊤ᴮ ≤ᴮ u ⟩ → u ≡ ⊤ᴮ
    ≡⊤ u h = ≤ᴮ-antisym (⊤-greatest u) h

    -- Two readings of transitivity that this file uses more often than
    -- transitivity itself. mediate closes from a common RIGHT endpoint,
    -- mediateˡ from a common LEFT one. Both are transitivity with one
    -- endpoint turned by ≈ᴮ-sym, and neither is an induction.

    mediate : (a b c : S) → ⟨ ((a ≈ᴮ c) ⊓ᴮ (b ≈ᴮ c)) ≤ᴮ (a ≈ᴮ b) ⟩
    mediate a b c =
      subst (λ z → ⟨ ((a ≈ᴮ c) ⊓ᴮ z) ≤ᴮ (a ≈ᴮ b) ⟩)
            (≈ᴮ-sym c b) (≈ᴮ-trans a c b)

    mediateˡ : (a b c : S) → ⟨ ((a ≈ᴮ b) ⊓ᴮ (a ≈ᴮ c)) ≤ᴮ (b ≈ᴮ c) ⟩
    mediateˡ a b c =
      subst (λ z → ⟨ (z ⊓ᴮ (a ≈ᴮ c)) ≤ᴮ (b ≈ᴮ c) ⟩) (≈ᴮ-sym b a)
        (subst (λ z → ⟨ ((b ≈ᴮ a) ⊓ᴮ z) ≤ᴮ (b ≈ᴮ c) ⟩) (≈ᴮ-sym c a)
          (mediate b c a))

    ----------------------------------------------------------------------------
    -- Mixtures, Bell fulltext:2459-2471
    ----------------------------------------------------------------------------

    -- Bell mixes a family of B-valued sets indexed by an ARBITRARY set I.
    -- K4's index is Pt I for a ground code I, never a host type: preamble
    -- rule R4 applies to the index of a family exactly as it applies to the
    -- index of a join, and a host-indexed family has no ground code behind it
    -- and could never be separated. Pt I is a sigma over a membership
    -- proposition, which is also why no statement below ever sees a bare
    -- membership witness.
    --
    -- The record carries the two things Bell's notation carries, the weights
    -- and the names, and nothing else. The architecture prints three further
    -- fields dom, dom-spec and dom-names here. They are moved into Mixture
    -- below, for two reasons. The union of the domains is a property of the
    -- MIXTURE and not of the family, which is how Bell states it; and
    -- dom-spec as a path in Ω would put this record at Type (ℓ-suc ℓ) and bar
    -- it from ever indexing a join, for no gain. That is the same correction
    -- Track C reports for AtomicSemantics and Track E for ValueTable.

    record CodedNameFamily (I : S) : Type ℓ where
      field
        at : Pt I → Name
        wt : Pt I → Pt B

    nm : {I : S} (F : CodedNameFamily I) → Pt I → S
    nm F j = fst (CodedNameFamily.at F j)

    wtOf : {I : S} (F : CodedNameFamily I) → Pt I → Pt B
    wtOf F j = CodedNameFamily.wt F j

    -- Bell's hypothesis (∗) at fulltext:2488, and it is COHERENCE and not an
    -- antichain. Bell says the antichain case is the one to remember; he does
    -- not prove the lemma from it, and neither does this file, because
    -- deriving (∗) from disjointness has to decide equality of two indices
    -- and that is where classical logic would enter.

    Coherent : {I : S} → CodedNameFamily I → Type ℓ
    Coherent {I} F = (j k : Pt I)
                   → ⟨ (wtOf F j ⊓ᴮ wtOf F k) ≤ᴮ (nm F j ≈ᴮ nm F k) ⟩

    -- The mixture, by its specification rather than by a construction. Bell
    -- writes dom(u) as the union of the dom(ui) and u(z) as the join of the
    -- ai meet [z in ui]. K4 can form neither: the union of a family of
    -- domains is Replacement's business and the join is over an index with no
    -- ground code. What the proof of 1.25 actually consumes is three facts,
    -- and they are the three fields. Two weakenings are deliberate and both
    -- are measured by the proof below rather than asserted.
    --
    --  * Only ONE HALF of Bell's domain equation is taken. covers-dom says
    --    every member of a domain of the family is a member of the mixture's
    --    domain. The converse, that the mixture's domain has no other
    --    members, is never used, so the lemma holds of any name whose domain
    --    is LARGE enough and not only of the exact union.
    --  * The weight is given by its UNIVERSAL PROPERTY and not by an equation
    --    naming a join. That is preamble rule R3 applied by default, and it
    --    is also exactly what makes Bell's two distributive steps
    --    unnecessary.

    record Mixture {I : S} (F : CodedNameFamily I) (mx : Name) : Type ℓ where
      field
        covers-dom : (j : Pt I) (z : S)
                   → ⟨ z ∈ˢ support (nm F j) ⟩
                   → ⟨ z ∈ˢ support (fst mx) ⟩
        wt-ub  : (z : S) → ⟨ z ∈ˢ support (fst mx) ⟩ → (j : Pt I)
               → ⟨ (wtOf F j ⊓ᴮ (z ∈ᴮ nm F j)) ≤ᴮ weightᴮ (fst mx) z ⟩
        wt-lub : (z : S) → ⟨ z ∈ˢ support (fst mx) ⟩ → (c : Pt B)
               → ((j : Pt I) → ⟨ (wtOf F j ⊓ᴮ (z ∈ᴮ nm F j)) ≤ᴮ c ⟩)
               → ⟨ weightᴮ (fst mx) z ≤ᴮ c ⟩

    ----------------------------------------------------------------------------
    -- Mixing Lemma 1.25, fulltext:2484-2491
    ----------------------------------------------------------------------------

    -- Bell's a, the half saying the mixture is included in ui. His proof is
    -- the displayed chain at fulltext:2500-2510, which distributes the fixed
    -- factor ai across the infinite join defining u(z). Here the fixed factor
    -- is pushed across the bound by the implication adjunction instead:
    -- wt-lub is the statement that u(z) is LEAST among the upper bounds, so
    -- it is enough to bound each term of the family by ak ⇒ᴮ [z in uk], and
    -- bounding one term is finite Boolean algebra plus (∗) plus one
    -- congruence of the membership value. No distributive law, finite or
    -- infinite, is used.

    mixing-left : {I : S} (F : CodedNameFamily I) (mx : Name)
                  (mix : Mixture F mx) → Coherent F → (k : Pt I)
                → (x : S) → ⟨ x ∈ˢ support (fst mx) ⟩
                → ⟨ wtOf F k ≤ᴮ (weightᴮ (fst mx) x ⇒ᴮ (x ∈ᴮ nm F k)) ⟩
    mixing-left {I} F mx mix coh k x hx =
      ⇒ᴮ-curry (wtOf F k) (weightᴮ (fst mx) x) (x ∈ᴮ nm F k) fin
      where
      inner : (j : Pt I)
            → ⟨ (wtOf F j ⊓ᴮ (x ∈ᴮ nm F j))
                ≤ᴮ (wtOf F k ⇒ᴮ (x ∈ᴮ nm F k)) ⟩
      inner j =
        ⇒ᴮ-curry (wtOf F j ⊓ᴮ (x ∈ᴮ nm F j)) (wtOf F k) (x ∈ᴮ nm F k) step
        where
        t : Pt B
        t = (wtOf F j ⊓ᴮ (x ∈ᴮ nm F j)) ⊓ᴮ wtOf F k
        t≤wj : ⟨ t ≤ᴮ wtOf F j ⟩
        t≤wj = ⊆ˢ-trans (⊓-lb₁ (wtOf F j ⊓ᴮ (x ∈ᴮ nm F j)) (wtOf F k))
                        (⊓-lb₁ (wtOf F j) (x ∈ᴮ nm F j))
        t≤mem : ⟨ t ≤ᴮ (x ∈ᴮ nm F j) ⟩
        t≤mem = ⊆ˢ-trans (⊓-lb₁ (wtOf F j ⊓ᴮ (x ∈ᴮ nm F j)) (wtOf F k))
                         (⊓-lb₂ (wtOf F j) (x ∈ᴮ nm F j))
        t≤wk : ⟨ t ≤ᴮ wtOf F k ⟩
        t≤wk = ⊓-lb₂ (wtOf F j ⊓ᴮ (x ∈ᴮ nm F j)) (wtOf F k)
        t≤eq : ⟨ t ≤ᴮ (nm F j ≈ᴮ nm F k) ⟩
        t≤eq = ⊆ˢ-trans (⊓-glb (wtOf F j) (wtOf F k) t t≤wj t≤wk) (coh j k)
        step : ⟨ t ≤ᴮ (x ∈ᴮ nm F k) ⟩
        step = ⊆ˢ-trans
                 (⊓-glb (nm F j ≈ᴮ nm F k) (x ∈ᴮ nm F j) t t≤eq t≤mem)
                 (∈ᴮ-congʳ x (nm F j) (nm F k))
      wLe : ⟨ weightᴮ (fst mx) x ≤ᴮ (wtOf F k ⇒ᴮ (x ∈ᴮ nm F k)) ⟩
      wLe = Mixture.wt-lub mix x hx (wtOf F k ⇒ᴮ (x ∈ᴮ nm F k)) inner
      fin : ⟨ (wtOf F k ⊓ᴮ weightᴮ (fst mx) x) ≤ᴮ (x ∈ᴮ nm F k) ⟩
      fin = ⊓-swap (weightᴮ (fst mx) x) (wtOf F k) (x ∈ᴮ nm F k)
              (⇒ᴮ-uncurry (weightᴮ (fst mx) x) (wtOf F k)
                          (x ∈ᴮ nm F k) wLe)

    -- Bell's b, the half saying ui is included in the mixture. His line is
    -- ai ∧ ui(z) ≤ ai ∧ [z in ui] ≤ u(z) ≤ [z in u] at fulltext:2515-2519,
    -- and it transcribes directly: 1.17(ii) at ui, then the mixture's upper
    -- bound property at the index k, then 1.17(ii) at the mixture. This is
    -- the only place covers-dom is spent.

    mixing-right : {I : S} (F : CodedNameFamily I) (mx : Name)
                   (mix : Mixture F mx) → (k : Pt I)
                 → (y : S) → ⟨ y ∈ˢ support (nm F k) ⟩
                 → ⟨ wtOf F k ≤ᴮ (weightᴮ (nm F k) y ⇒ᴮ (y ∈ᴮ fst mx)) ⟩
    mixing-right {I} F mx mix k y hy =
      ⇒ᴮ-curry (wtOf F k) (weightᴮ (nm F k) y) (y ∈ᴮ fst mx)
        (⊆ˢ-trans a₁ (⊆ˢ-trans a₂ a₃))
      where
      hy' : ⟨ y ∈ˢ support (fst mx) ⟩
      hy' = Mixture.covers-dom mix k y hy
      a₁ : ⟨ (wtOf F k ⊓ᴮ weightᴮ (nm F k) y)
             ≤ᴮ (wtOf F k ⊓ᴮ (y ∈ᴮ nm F k)) ⟩
      a₁ = ⊓ᴮ-mono (wtOf F k) (wtOf F k) (weightᴮ (nm F k) y) (y ∈ᴮ nm F k)
                   (≤ᴮ-refl (wtOf F k)) (weight-≤ (nm F k) y hy)
      a₂ : ⟨ (wtOf F k ⊓ᴮ (y ∈ᴮ nm F k)) ≤ᴮ weightᴮ (fst mx) y ⟩
      a₂ = Mixture.wt-ub mix y hy' k
      a₃ : ⟨ weightᴮ (fst mx) y ≤ᴮ (y ∈ᴮ fst mx) ⟩
      a₃ = weight-≤ (fst mx) y hy'

    -- Mixing Lemma 1.25, in the coherence form Bell states it in. The two
    -- halves are his a and b and the conclusion is his ai ≤ a ∧ b, which here
    -- is the greatest lower bound property of the equality value, Track C's
    -- eqᴬ-glb, applied once.

    mixing : {I : S} (F : CodedNameFamily I) (mx : Name) (mix : Mixture F mx)
           → Coherent F
           → (k : Pt I)
           → ⟨ wtOf F k ≤ᴮ (fst mx ≈ᴮ nm F k) ⟩
    mixing F mx mix coh k =
      ≈ᴮ-glb (fst mx) (nm F k) (wtOf F k)
        (mixing-left F mx mix coh k)
        (mixing-right F mx mix k)

    ----------------------------------------------------------------------------
    -- The antichain corollary, and this is where LEM enters and stays visible
    ----------------------------------------------------------------------------

    -- Bell's "in particular" clause at fulltext:2491. An antichain is a
    -- family whose distinct members meet at bottom, so turning it into the
    -- coherence hypothesis has to DECIDE whether two indices are distinct.
    -- Pt I is a set because S is, so the decision is a decision about a
    -- proposition and LEM ℓ is exactly what supplies it. It is an explicit
    -- argument of the theorem and never a module parameter, so every consumer
    -- of mixing-antichain carries the classical hypothesis on the face of its
    -- own statement while every consumer of mixing carries none.

    Antichain : {I : S} → CodedNameFamily I → Type ℓ
    Antichain {I} F = (j k : Pt I) → (j ≡ k → Empty.⊥)
                    → (wtOf F j ⊓ᴮ wtOf F k) ≡ ⊥ᴮ

    antichain→coherent : LEM ℓ → {I : S} (F : CodedNameFamily I)
                       → Antichain F → Coherent F
    antichain→coherent lem {I} F ac j k with lem ((j ≡ k) , isSetPt I j k)
    ... | inl same =
            subst (λ z → ⟨ (wtOf F j ⊓ᴮ wtOf F k) ≤ᴮ z ⟩) (sym top)
                  (⊤-greatest (wtOf F j ⊓ᴮ wtOf F k))
      where
      top : (nm F j ≈ᴮ nm F k) ≡ ⊤ᴮ
      top = sym (cong (λ q → nm F j ≈ᴮ nm F q) same) ∙ ≈ᴮ-refl (nm F j)
    ... | inr apart =
            subst (λ z → ⟨ z ≤ᴮ (nm F j ≈ᴮ nm F k) ⟩) (sym (ac j k apart))
                  (⊥-least (nm F j ≈ᴮ nm F k))

    mixing-antichain : LEM ℓ → {I : S} (F : CodedNameFamily I) (mx : Name)
                     → Mixture F mx → Antichain F
                     → (k : Pt I)
                     → ⟨ wtOf F k ≤ᴮ (fst mx ≈ᴮ nm F k) ⟩
    mixing-antichain lem F mx mix ac =
      mixing F mx mix (antichain→coherent lem F ac)

    ----------------------------------------------------------------------------
    -- Problem 1.26(ii), fulltext:2529-2540
    ----------------------------------------------------------------------------

    -- A partition of unity is an antichain whose join is the top element. K4
    -- may not name that join, so the hypothesis is its universal property:
    -- the top element is LEAST among the upper bounds of the weights. Stated
    -- this way the hypothesis is R3 clean, and it is also weaker than Bell's,
    -- since disjointness is never used.
    --
    -- Bell asks to show that any v satisfying ai ≤ [v = ui] for all i is
    -- Boolean equal to the mixture. Coherence is not a separate hypothesis
    -- here: it FOLLOWS from the hypothesis on v, because two values both
    -- below an equality with a common name are below the equality of the two
    -- names. That is mediateˡ, and it is why the theorem reads as a
    -- uniqueness statement rather than as a second mixing lemma.

    Unity : {I : S} → CodedNameFamily I → Type ℓ
    Unity {I} F = (c : Pt B) → ((j : Pt I) → ⟨ wtOf F j ≤ᴮ c ⟩)
                → ⟨ ⊤ᴮ ≤ᴮ c ⟩

    common→coherent : {I : S} (F : CodedNameFamily I) (v : Name)
                    → ((j : Pt I) → ⟨ wtOf F j ≤ᴮ (fst v ≈ᴮ nm F j) ⟩)
                    → Coherent F
    common→coherent {I} F v hv j k =
      ⊆ˢ-trans
        (⊓ᴮ-mono (wtOf F j) (fst v ≈ᴮ nm F j) (wtOf F k) (fst v ≈ᴮ nm F k)
                 (hv j) (hv k))
        (mediateˡ (fst v) (nm F j) (nm F k))

    mixture-unique : {I : S} (F : CodedNameFamily I) (mx : Name)
                     (mix : Mixture F mx) → Unity F
                   → (v : Name)
                   → ((j : Pt I) → ⟨ wtOf F j ≤ᴮ (fst v ≈ᴮ nm F j) ⟩)
                   → (fst v ≈ᴮ fst mx) ≡ ⊤ᴮ
    mixture-unique {I} F mx mix unity v hv =
      ≡⊤ (fst v ≈ᴮ fst mx) (unity (fst v ≈ᴮ fst mx) below)
      where
      coh : Coherent F
      coh = common→coherent F v hv
      below : (j : Pt I) → ⟨ wtOf F j ≤ᴮ (fst v ≈ᴮ fst mx) ⟩
      below j =
        ⊆ˢ-trans
          (⊓-glb (fst v ≈ᴮ nm F j) (fst mx ≈ᴮ nm F j) (wtOf F j)
                 (hv j) (mixing F mx mix coh j))
          (mediate (fst v) (fst mx) (nm F j))

    ----------------------------------------------------------------------------
    -- Boolean uniqueness, and the reading this track REFUTES
    ----------------------------------------------------------------------------

    -- A value family on names. Everything from here to the end of the file is
    -- stated about such a family and a value that is its least upper bound. A
    -- compiled formula with one free variable supplies exactly that, through
    -- Track F's Interp.val (interp φ) (σ ∷ ν) and its ∃-ub and ∃-lub clauses;
    -- module Formulas at the end of this file is that wiring, and nothing
    -- above it mentions a formula. Stating the mathematics at the family
    -- rather than at the formula is not only independence from Track F: it is
    -- what makes fullness→element a one liner, because Bell's Sigma(B) is
    -- fullness at the family that sends a name to its membership value, which
    -- no compiler is needed to write.

    record Lub (v : Name → Pt B) (E : Pt B) : Type ℓ where
      field
        ub  : (σ : Name) → ⟨ v σ ≤ᴮ E ⟩
        lub : (c : Pt B) → ((σ : Name) → ⟨ v σ ≤ᴮ c ⟩) → ⟨ E ≤ᴮ c ⟩

    -- Bell's 1.17(vii) at one free variable: the value of a formula is
    -- congruent for the Boolean equality of names. It is Track G's
    -- deliverable and it is taken as a hypothesis of the theorems that need
    -- it, never as a module parameter, because the two mixing theorems above
    -- do not need it and their ledger says so.

    Congruent : (Name → Pt B) → Type ℓ
    Congruent v = (σ τ : Name) → ⟨ ((fst σ ≈ᴮ fst τ) ⊓ᴮ v σ) ≤ᴮ v τ ⟩

    -- THE UNIQUENESS HYPOTHESIS, AND ITS UNIQUENESS IS BOOLEAN EQUALITY. This
    -- is the internal reading of unique existence: the meet of the values at
    -- two names is below the Boolean equality value of those names. It says
    -- nothing whatever about the two names being equal as codes.

    BooleanUnique : (Name → Pt B) → Type ℓ
    BooleanUnique v = (σ τ : Name) → ⟨ (v σ ⊓ᴮ v τ) ≤ᴮ (fst σ ≈ᴮ fst τ) ⟩

    -- THE READING K4 REFUTES, in the two forms a later consumer is most
    -- likely to write. Both replace the Boolean equality by a PATH between
    -- names.

    RawUnique : (Name → Pt B) → Type ℓ
    RawUnique v = (σ τ : Name) → v σ ≡ ⊤ᴮ → v τ ≡ ⊤ᴮ → σ ≡ τ

    RawUniquePositive : (Name → Pt B) → Type ℓ
    RawUniquePositive v =
      (σ τ : Name) → (((v σ ⊓ᴮ v τ) ≡ ⊥ᴮ) → ⟨ ⊥ ⟩) → σ ≡ τ

    -- The canonical coherent family: the value of "x is Boolean equal to the
    -- fixed name". It is BooleanUnique unconditionally, by transitivity and
    -- symmetry alone, and it is the family at which the two readings are
    -- furthest apart.

    eqFamily : Name → Name → Pt B
    eqFamily σ₀ τ = fst τ ≈ᴮ fst σ₀

    boolean-unique-eq : (σ₀ : Name) → BooleanUnique (eqFamily σ₀)
    boolean-unique-eq σ₀ σ τ = mediate (fst σ) (fst τ) (fst σ₀)

    -- THE UNCONDITIONAL HALF OF THE REFUTATION. At the canonical family the
    -- raw reading is not merely stronger than the Boolean one: it IS the
    -- assertion that Boolean equality to the fixed name implies a path to it.
    -- Nothing in the atomic layer proves that, and the whole point of a
    -- Boolean-valued model is that it fails.

    raw-unique-collapses : (σ₀ : Name) → RawUnique (eqFamily σ₀)
                         → (τ : Name) → (fst τ ≈ᴮ fst σ₀) ≡ ⊤ᴮ → τ ≡ σ₀
    raw-unique-collapses σ₀ ru τ h = ru τ σ₀ h (≈ᴮ-refl (fst σ₀))

    BooleanCollapse : Type ℓ
    BooleanCollapse = (σ τ : Name) → (fst σ ≈ᴮ fst τ) ≡ ⊤ᴮ → σ ≡ τ

    raw-unique→collapse : ((σ₀ : Name) → RawUnique (eqFamily σ₀))
                        → BooleanCollapse
    raw-unique→collapse ru σ τ h = raw-unique-collapses τ (ru τ) σ h

    -- THE CONDITIONAL HALF. Two names that are Boolean equal and raw
    -- distinct. The intended discharge is Track H's zero-weight-boolean
    -- beside K3's zero-distinct (NameKernel.agda:555-558): the name with one
    -- entry of weight bottom is Boolean equal to the empty name and is not
    -- the empty name. K4.7 owns that pair by the architecture's own
    -- assignment, so this track states the hypothesis and builds no witness
    -- for it.

    record Separated : Type ℓ where
      field
        n₀ n₁   : Name
        n-eq    : (fst n₀ ≈ᴮ fst n₁) ≡ ⊤ᴮ
        n-apart : n₀ ≡ n₁ → ⟨ ⊥ ⟩

    boolean-unique-not-raw : Separated
      → Σ[ v ∈ (Name → Pt B) ] (BooleanUnique v × (RawUnique v → ⟨ ⊥ ⟩))
    boolean-unique-not-raw sep =
      eqFamily n₀ , boolean-unique-eq n₀ , refute
      where
      open Separated sep
      turned : (fst n₁ ≈ᴮ fst n₀) ≡ ⊤ᴮ
      turned = sym (≈ᴮ-sym (fst n₀) (fst n₁)) ∙ n-eq
      refute : RawUnique (eqFamily n₀) → ⟨ ⊥ ⟩
      refute ru = n-apart (ru n₀ n₁ (≈ᴮ-refl (fst n₀)) turned)

    boolean-unique-not-raw-positive : Separated → ((⊥ᴮ ≡ ⊤ᴮ) → ⟨ ⊥ ⟩)
      → Σ[ v ∈ (Name → Pt B) ]
          (BooleanUnique v × (RawUniquePositive v → ⟨ ⊥ ⟩))
    boolean-unique-not-raw-positive sep nondeg =
      eqFamily n₀ , boolean-unique-eq n₀ , refute
      where
      open Separated sep
      q₀ : (fst n₀ ≈ᴮ fst n₀) ≡ ⊤ᴮ
      q₀ = ≈ᴮ-refl (fst n₀)
      q₁ : (fst n₁ ≈ᴮ fst n₀) ≡ ⊤ᴮ
      q₁ = sym (≈ᴮ-sym (fst n₀) (fst n₁)) ∙ n-eq
      meet⊤ : ((fst n₀ ≈ᴮ fst n₀) ⊓ᴮ (fst n₁ ≈ᴮ fst n₀)) ≡ ⊤ᴮ
      meet⊤ = cong (λ z → z ⊓ᴮ (fst n₁ ≈ᴮ fst n₀)) q₀
            ∙ cong (λ z → ⊤ᴮ ⊓ᴮ z) q₁
            ∙ ⊓-idem ⊤ᴮ
      refute : RawUniquePositive (eqFamily n₀) → ⟨ ⊥ ⟩
      refute rup = n-apart (rup n₀ n₁ (λ p → nondeg (sym p ∙ meet⊤)))

    ----------------------------------------------------------------------------
    -- The adequate domain, Bell's V(B) at stage alpha, fulltext:2612-2617
    ----------------------------------------------------------------------------

    -- Bell's hint for Problem 1.29 is to choose a sufficiently large ordinal
    -- alpha with 1 = [∃xφ(x)] already the join over V(B) at that stage, and
    -- then to define u by dom(u) = V(B) at that stage. Three things about
    -- that stage are used in his argument and they are the three fields: its
    -- members are names, it is closed under passing to a member of a domain,
    -- and the value of the existential is already attained on it. K3's
    -- analogue of V(B) at a stage is nameBound with nameBound-contains
    -- (NameSpace.agda:557-563).
    --
    -- The record is at Type ℓ, not at Type (ℓ-suc ℓ) as the architecture
    -- prints it: no field is a path in Ω, so section 1.0's rule 1 does not
    -- bar it from indexing a join.
    --
    -- The architecture's family : Admits field is not here. Its content is
    -- that the existential's value is a join of a separated value set, and
    -- what the proof uses is only that E is the least upper bound over the
    -- domain, which is the adequate field. Keeping Admits out also keeps supᴮ
    -- applied to a constructed set out of every type in this file, which is
    -- rule R3 applied by default. Track B's admits-ub and admits-lub
    -- (K4/ValueSets.agda:381, :387) supply Lub for a caller holding the
    -- record.

    record AdequateDomain (v : Name → Pt B) (E : Pt B) : Type ℓ where
      field
        dom        : S
        dom-names  : (x : S) → ⟨ x ∈ˢ dom ⟩ → ⟨ IsName x ⟩
        dom-closed : (n x : S) → ⟨ n ∈ˢ dom ⟩ → ⟨ x ∈ˢ support n ⟩
                   → ⟨ x ∈ˢ dom ⟩
        adequate   : (c : Pt B)
                   → ((p : Pt dom)
                      → ⟨ v (fst p , dom-names (fst p) (snd p)) ≤ᴮ c ⟩)
                   → ⟨ E ≤ᴮ c ⟩

    named : {v : Name → Pt B} {E : Pt B} (A : AdequateDomain v E)
          → Pt (AdequateDomain.dom A) → Name
    named A p = fst p , AdequateDomain.dom-names A (fst p) (snd p)

    -- The witness name of Problem 1.29, again by its specification. Bell's u
    -- has dom(u) = V(B) at the chosen stage and u(z) = [∃x (φ(x) ∧ z ∈ x)].
    -- The second is an unbounded join over names, so it is taken by its
    -- universal property; the first is taken in ONE direction only, because
    -- the proof never needs the witness's domain to be no larger than the
    -- adequate domain.

    record WitnessSpec (v : Name → Pt B) (D : S) (u : Name) : Type ℓ where
      field
        dom-covers : (x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ x ∈ˢ support (fst u) ⟩
        wt-ub  : (z : S) → ⟨ z ∈ˢ support (fst u) ⟩ → (τ : Name)
               → ⟨ (v τ ⊓ᴮ (z ∈ᴮ fst τ)) ≤ᴮ weightᴮ (fst u) z ⟩
        wt-lub : (z : S) → ⟨ z ∈ˢ support (fst u) ⟩ → (c : Pt B)
               → ((τ : Name) → ⟨ (v τ ⊓ᴮ (z ∈ᴮ fst τ)) ≤ᴮ c ⟩)
               → ⟨ weightᴮ (fst u) z ≤ᴮ c ⟩

    ----------------------------------------------------------------------------
    -- Unique existence, Bell Problem 1.29, WITHOUT THE AXIOM OF CHOICE
    ----------------------------------------------------------------------------

    -- The heart of the problem: at a name in the adequate domain, the value
    -- of φ is below the Boolean equality of that name with the witness. Bell
    -- does not display this step; it is the whole content of the hint. The
    -- two halves of (1.16) are proved separately and they use the hypotheses
    -- in completely different ways, which is worth stating because it is
    -- where both the domain closure and the uniqueness hypothesis are spent,
    -- and nowhere else.
    --
    --  * The left half needs the DOMAIN CLOSURE and 1.17(ii) twice. A member
    --    x of the domain of σ is a member of the adequate domain because σ is
    --    and the domain is closed, so x is in the witness's domain, so the
    --    witness's weight at x is above the term at σ.
    --  * The right half needs the UNIQUENESS hypothesis and one congruence of
    --    the membership value. The witness's weight at y is a least upper
    --    bound, so the fixed factor crosses it by the adjunction; bounding
    --    one term is BooleanUnique followed by ∈ᴮ-congʳ. THIS IS THE ONLY
    --    PLACE BooleanUnique IS USED, and it is used as a Boolean inequality
    --    and never as an equality of names.

    witness-value : (v : Name → Pt B) (E : Pt B) (A : AdequateDomain v E)
                  → BooleanUnique v
                  → (u : Name)
                  → WitnessSpec v (AdequateDomain.dom A) u
                  → (p : Pt (AdequateDomain.dom A))
                  → ⟨ v (named A p) ≤ᴮ (fst (named A p) ≈ᴮ fst u) ⟩
    witness-value v E A bu u W p =
      ≈ᴮ-glb s (fst u) (v σ) leftHalf rightHalf
      where
      σ : Name
      σ = named A p
      s : S
      s = fst σ
      leftHalf : (x : S) → ⟨ x ∈ˢ support s ⟩
               → ⟨ v σ ≤ᴮ (weightᴮ s x ⇒ᴮ (x ∈ᴮ fst u)) ⟩
      leftHalf x hx =
        ⇒ᴮ-curry (v σ) (weightᴮ s x) (x ∈ᴮ fst u)
          (⊆ˢ-trans b₁ (⊆ˢ-trans b₂ b₃))
        where
        hxD : ⟨ x ∈ˢ AdequateDomain.dom A ⟩
        hxD = AdequateDomain.dom-closed A s x (snd p) hx
        hxu : ⟨ x ∈ˢ support (fst u) ⟩
        hxu = WitnessSpec.dom-covers W x hxD
        b₁ : ⟨ (v σ ⊓ᴮ weightᴮ s x) ≤ᴮ (v σ ⊓ᴮ (x ∈ᴮ s)) ⟩
        b₁ = ⊓ᴮ-mono (v σ) (v σ) (weightᴮ s x) (x ∈ᴮ s)
                     (≤ᴮ-refl (v σ)) (weight-≤ s x hx)
        b₂ : ⟨ (v σ ⊓ᴮ (x ∈ᴮ s)) ≤ᴮ weightᴮ (fst u) x ⟩
        b₂ = WitnessSpec.wt-ub W x hxu σ
        b₃ : ⟨ weightᴮ (fst u) x ≤ᴮ (x ∈ᴮ fst u) ⟩
        b₃ = weight-≤ (fst u) x hxu
      rightHalf : (y : S) → ⟨ y ∈ˢ support (fst u) ⟩
                → ⟨ v σ ≤ᴮ (weightᴮ (fst u) y ⇒ᴮ (y ∈ᴮ s)) ⟩
      rightHalf y hy =
        ⇒ᴮ-curry (v σ) (weightᴮ (fst u) y) (y ∈ᴮ s) fin
        where
        inner : (τ : Name)
              → ⟨ (v τ ⊓ᴮ (y ∈ᴮ fst τ)) ≤ᴮ (v σ ⇒ᴮ (y ∈ᴮ s)) ⟩
        inner τ =
          ⇒ᴮ-curry (v τ ⊓ᴮ (y ∈ᴮ fst τ)) (v σ) (y ∈ᴮ s) step
          where
          t : Pt B
          t = (v τ ⊓ᴮ (y ∈ᴮ fst τ)) ⊓ᴮ v σ
          t≤vτ : ⟨ t ≤ᴮ v τ ⟩
          t≤vτ = ⊆ˢ-trans (⊓-lb₁ (v τ ⊓ᴮ (y ∈ᴮ fst τ)) (v σ))
                          (⊓-lb₁ (v τ) (y ∈ᴮ fst τ))
          t≤mem : ⟨ t ≤ᴮ (y ∈ᴮ fst τ) ⟩
          t≤mem = ⊆ˢ-trans (⊓-lb₁ (v τ ⊓ᴮ (y ∈ᴮ fst τ)) (v σ))
                           (⊓-lb₂ (v τ) (y ∈ᴮ fst τ))
          t≤vσ : ⟨ t ≤ᴮ v σ ⟩
          t≤vσ = ⊓-lb₂ (v τ ⊓ᴮ (y ∈ᴮ fst τ)) (v σ)
          t≤eq : ⟨ t ≤ᴮ (fst τ ≈ᴮ s) ⟩
          t≤eq = ⊆ˢ-trans (⊓-glb (v τ) (v σ) t t≤vτ t≤vσ) (bu τ σ)
          step : ⟨ t ≤ᴮ (y ∈ᴮ s) ⟩
          step = ⊆ˢ-trans (⊓-glb (fst τ ≈ᴮ s) (y ∈ᴮ fst τ) t t≤eq t≤mem)
                          (∈ᴮ-congʳ y (fst τ) s)
        wLe : ⟨ weightᴮ (fst u) y ≤ᴮ (v σ ⇒ᴮ (y ∈ᴮ s)) ⟩
        wLe = WitnessSpec.wt-lub W y hy (v σ ⇒ᴮ (y ∈ᴮ s)) inner
        fin : ⟨ (v σ ⊓ᴮ weightᴮ (fst u) y) ≤ᴮ (y ∈ᴮ s) ⟩
        fin = ⊓-swap (weightᴮ (fst u) y) (v σ) (y ∈ᴮ s)
                (⇒ᴮ-uncurry (weightᴮ (fst u) y) (v σ) (y ∈ᴮ s) wLe)

    -- DATA IN, DATA OUT. There is no propositional truncation in this
    -- signature, and that absence is the whole point: nothing is chosen, so
    -- nothing has to be eliminated out of a truncation. Compare Bell's Lemma
    -- 1.27, whose proof opens by invoking the axiom of choice to well order
    -- the set of values (fulltext:2560-2566). Problem 1.29 is set immediately
    -- afterwards precisely because this case escapes that.
    --
    -- Measured ledger of this theorem: Separation, Collection and PowerSet
    -- are all absent, against the architecture's permitted hypothesis list
    -- for the unique existence half. They are needed to BUILD an adequate
    -- domain and a witness name; they are not needed to prove that the
    -- witness works.

    unique-witness : (v : Name → Pt B) (E : Pt B) (lb : Lub v E)
                   → BooleanUnique v → Congruent v
                   → (A : AdequateDomain v E)
                   → (u : Name)
                   → WitnessSpec v (AdequateDomain.dom A) u
                   → v u ≡ E
    unique-witness v E lb bu cg A u W =
      ≤ᴮ-antisym (Lub.ub lb u) (AdequateDomain.adequate A (v u) below)
      where
      below : (p : Pt (AdequateDomain.dom A)) → ⟨ v (named A p) ≤ᴮ v u ⟩
      below p =
        ⊆ˢ-trans
          (⊓-glb (fst (named A p) ≈ᴮ fst u) (v (named A p)) (v (named A p))
                 (witness-value v E A bu u W p) (≤ᴮ-refl (v (named A p))))
          (cg (named A p) u)

    -- The truncated form Bell states at fulltext:2610-2611. The truncation is
    -- not in the mathematics, it is in the SUPPLY: K3's completeness result
    -- for closed name domains is truncated at both of its sites
    -- (NameSpace.agda:709, :865), so an adequate domain and a witness name
    -- arrive merely. Eliminating a truncation into another truncation is not
    -- a choice, and this is the only elimination in the file.

    unique-witness-merely : (v : Name → Pt B) (E : Pt B) (lb : Lub v E)
                          → BooleanUnique v → Congruent v
                          → ∥ Σ[ A ∈ AdequateDomain v E ]
                                (Σ[ u ∈ Name ]
                                   WitnessSpec v (AdequateDomain.dom A) u) ∥₁
                          → ∥ Σ[ τ ∈ Name ] (v τ ≡ E) ∥₁
    unique-witness-merely v E lb bu cg =
      PT.map (λ { (A , u , W) → u , unique-witness v E lb bu cg A u W })

    -- The reduction of the architecture's adequate-exists to the two things
    -- it really needs. A VALUE COVER is a set of names on which every value
    -- of the family is already bounded; Collection supplies one, given a
    -- ground formula reading the value, which for a FIXED source formula is
    -- Track F's Interp.code with its reading. A child closed superset of the
    -- cover then makes it an adequate domain, and that is all the adequate
    -- field ever asks for.
    --
    -- MEASURED NEGATIVE, and it is reported as one rather than designed
    -- around. adequate-exists, as architecture section 1.10 prints it, is NOT
    -- discharged on this track. Two inputs are missing and neither is K4.8's.
    -- The first is the ground formula for the compiled value, which is Track
    -- F's Interp.code, unavailable while Track F is open, and which may not
    -- be made uniform in φ because a reading uniform in φ is the forbidden
    -- object of architecture section 1.12 (fulltext:2043-2052). The second is
    -- a child closure of an arbitrary SET of names. K3 exports hereditary per
    -- name, truncated (NameSpace.agda:709, :865), and common for the
    -- INTERSECTION of two closed sets (:433, re-exported :872); Track E
    -- shipped closed-union for two sets and measured that a family indexed
    -- union closure exists in K3 only as the local where bound codedE inside
    -- Collect.hereditary (NameSpace.agda:757) and is not reachable
    -- (REPORT-E.md section 4, E1). So the gap is one exported lemma in K3
    -- plus one projection out of Track F, and adequate-from-cover is the
    -- exact interface between them and this file.

    record ValueCover (v : Name → Pt B) : Type ℓ where
      field
        cover       : S
        cover-names : (x : S) → ⟨ x ∈ˢ cover ⟩ → ⟨ IsName x ⟩
        covered     : (σ : Name) (c : Pt B)
                    → ((x : S) (h : ⟨ x ∈ˢ cover ⟩)
                       → ⟨ v (x , cover-names x h) ≤ᴮ c ⟩)
                    → ⟨ v σ ≤ᴮ c ⟩

    adequate-from-cover : (v : Name → Pt B) (E : Pt B) → Lub v E
                        → (C : ValueCover v)
                        → (D : S)
                        → (names : (x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ IsName x ⟩)
                        → ((n x : S) → ⟨ n ∈ˢ D ⟩ → ⟨ x ∈ˢ support n ⟩
                           → ⟨ x ∈ˢ D ⟩)
                        → ⟨ ValueCover.cover C ⊆ˢ D ⟩
                        → AdequateDomain v E
    adequate-from-cover v E lb C D names closed sub = record
      { dom        = D
      ; dom-names  = names
      ; dom-closed = closed
      ; adequate   = λ c bound →
          Lub.lub lb c (λ σ →
            ValueCover.covered C σ c (λ x h →
              subst (λ z → ⟨ z ≤ᴮ c ⟩)
                    (name-irr v x (names x (sub x h))
                                  (ValueCover.cover-names C x h))
                    (bound (x , sub x h))))
      }

    ----------------------------------------------------------------------------
    -- THE FULLNESS CONTRACT. NOTHING BELOW THIS LINE IS INHABITED IN K4.
    ----------------------------------------------------------------------------

    -- Fullness: the value of an existential is ATTAINED at some name. The
    -- truncation is mandatory, and it is the shape K0's representation ledger
    -- fixes in its quantifier contract paragraph, whose words are that
    -- collecting values does not choose a name per value. K4 ships the record
    -- and no inhabitant of it. K12a owns fullness (roadmap:238).

    record Fullness (v : Name → Pt B) (E : Pt B) : Type ℓ where
      field witness : ∥ Σ[ τ ∈ Name ] (v τ ≡ E) ∥₁

    -- The Maximum Principle, Bell's Lemma 1.27 (fulltext:2549-2585): fullness
    -- at EVERY value family. K4 ships the record and no inhabitant of it, and
    -- no function in this file returns one out of the algebra records alone.

    record MaximumPrinciple : Type ℓ where
      field
        attained : (v : Name → Pt B) (E : Pt B) → Lub v E → Congruent v
                 → Fullness v E

    mp→fullness : MaximumPrinciple
                → (v : Name → Pt B) (E : Pt B) → Lub v E → Congruent v
                → Fullness v E
    mp→fullness = MaximumPrinciple.attained

    -- WHAT K4 DOES OWN, AND IT IS ALL OF BELL'S PROOF EXCEPT ONE STEP.
    --
    -- Bell proves 1.27 like this. Take the family of values of φ. Use the
    -- axiom of choice to enumerate it by an ordinal, subtract the earlier
    -- values to get an ANTICHAIN below the corresponding values whose join is
    -- the existential's value, mix along it, and conclude by the Mixing Lemma
    -- and 1.17(vii).
    --
    -- Everything after the enumeration is K4's and is proved below. A
    -- REFINEMENT is exactly what the choice step produces: a coded family
    -- whose weights lie below the corresponding values and whose join is the
    -- existential's value, together with the coherence the Mixing Lemma
    -- needs. Given one, plus a mixture of it, fullness follows with no
    -- further hypothesis.
    --
    -- So the boundary is drawn at one record. MaximumPrincipleContract below
    -- is the residue, and Problem 1.30 (fulltext:2618-2640) is the reason it
    -- may not be discharged here: the assertion that the Maximum Principle
    -- holds in V(B) for EVERY complete Boolean algebra B is equivalent to the
    -- axiom of choice. A K4 module that returned an inhabitant of that record
    -- from the three algebra records would be asserting choice.

    record Refinement (v : Name → Pt B) (E : Pt B) : Type ℓ where
      field
        idx      : S
        fam      : CodedNameFamily idx
        below    : (j : Pt idx)
                 → ⟨ wtOf fam j ≤ᴮ v (CodedNameFamily.at fam j) ⟩
        covers   : (c : Pt B) → ((j : Pt idx) → ⟨ wtOf fam j ≤ᴮ c ⟩)
                 → ⟨ E ≤ᴮ c ⟩
        coherent : Coherent fam

    -- The name construction half, separated from the choice half on purpose.
    -- Forming the mixture of a coded family is ground machinery, Replacement
    -- and the name builder, and it is NOT choice. Keeping the two obligations
    -- in two records is what lets a later package see which of them costs the
    -- axiom of choice and which does not.

    MixtureSupply : Type ℓ
    MixtureSupply = {I : S} (F : CodedNameFamily I)
                  → ∥ Σ[ mx ∈ Name ] Mixture F mx ∥₁

    refinement→fullness : MixtureSupply
                        → (v : Name → Pt B) (E : Pt B)
                        → Lub v E → Congruent v
                        → ∥ Refinement v E ∥₁ → Fullness v E
    refinement→fullness supply v E lb cg ref = record
      { witness = PT.rec PT.squash₁ fromRefinement ref }
      where
      fromRefinement : Refinement v E → ∥ Σ[ τ ∈ Name ] (v τ ≡ E) ∥₁
      fromRefinement R = PT.map fromMixture (supply fam)
        where
        open Refinement R
        fromMixture : Σ[ mx ∈ Name ] Mixture fam mx
                    → Σ[ τ ∈ Name ] (v τ ≡ E)
        fromMixture (mx , mix) = mx , ≤ᴮ-antisym (Lub.ub lb mx) reach
          where
          step : (j : Pt idx) → ⟨ wtOf fam j ≤ᴮ v mx ⟩
          step j =
            ⊆ˢ-trans
              (⊓-glb (nm fam j ≈ᴮ fst mx) (v (CodedNameFamily.at fam j))
                     (wtOf fam j) turned (below j))
              (cg (CodedNameFamily.at fam j) mx)
            where
            turned : ⟨ wtOf fam j ≤ᴮ (nm fam j ≈ᴮ fst mx) ⟩
            turned = subst (λ z → ⟨ wtOf fam j ≤ᴮ z ⟩)
                           (≈ᴮ-sym (fst mx) (nm fam j))
                           (mixing fam mx mix coherent j)
          reach : ⟨ E ≤ᴮ v mx ⟩
          reach = covers (v mx) step

    -- THE CONTRACT ITSELF. This is what a later package must supply, stated
    -- so that the typechecker enforces it: there is no other route from this
    -- file to a MaximumPrinciple, and this file inhabits neither record.
    --
    -- What K12a may NOT assume: that the three algebra records give it. They
    -- do not, and the measurement in this file's ledger says how far they are
    -- from giving it. Not one field of CodedComplete is projected anywhere in
    -- this file, so Boolean completeness is not merely insufficient for the
    -- Maximum Principle, it is not used by either theorem the principle
    -- generalizes.

    record MaximumPrincipleContract : Type ℓ where
      field
        mixtures : MixtureSupply
        refine   : (v : Name → Pt B) (E : Pt B) → Lub v E → Congruent v
                 → ∥ Refinement v E ∥₁

    contract→mp : MaximumPrincipleContract → MaximumPrinciple
    contract→mp K = record
      { attained = λ v E lb cg →
          refinement→fullness (MaximumPrincipleContract.mixtures K) v E lb cg
            (MaximumPrincipleContract.refine K v E lb cg) }

    -- AND THE OTHER SIDE OF THE FENCE. Bell's Sigma(B) at fulltext:2628-2630:
    -- every B-valued set whose "is nonempty" value is top has an element
    -- whose membership value is top. It is fullness at the family sending a
    -- name to its membership value in a fixed code, which needs no compiler
    -- to write, so the derivation is one line. Problem 1.30(ii) proves that
    -- Sigma(B) for every complete Boolean algebra is equivalent to the axiom
    -- of choice, confining attention to the algebras P(X). So anything strong
    -- enough to give K4 fullness in general is strong enough to give choice,
    -- and that is the fence's far side.
    --
    -- This file does not prove Problem 1.30's equivalence. It proves the
    -- arrow that makes the citation bite, and states the rest as Bell's.

    memFamily : S → Name → Pt B
    memFamily n τ = fst τ ∈ᴮ n

    record ElementPrinciple : Type ℓ where
      field
        element : (n : S) (E : Pt B) → Lub (memFamily n) E → E ≡ ⊤ᴮ
                → ∥ Σ[ τ ∈ Name ] ((fst τ ∈ᴮ n) ≡ ⊤ᴮ) ∥₁

    -- The congruence hypothesis below is 1.17(v) read as a Boolean
    -- inequality, and Track D proves exactly it: ∈ᴮ-congˡ
    -- (K4/AtomicLaws.agda:461). It is a hypothesis here rather than a taken
    -- parameter so that the two mixing theorems keep the shorter ledger the
    -- brief asks for.

    fullness→element : ((v : Name → Pt B) (E : Pt B) → Lub v E → Congruent v
                        → Fullness v E)
                     → ((n : S) → Congruent (memFamily n))
                     → ElementPrinciple
    fullness→element full cg = record
      { element = λ n E lb top →
          PT.map (λ { (τ , p) → τ , (p ∙ top) })
                 (Fullness.witness (full (memFamily n) E lb (cg n))) }

    ----------------------------------------------------------------------------
    -- The wiring to Track F, with no dependency on Track F
    ----------------------------------------------------------------------------

    -- Everything above is stated about a value family on names. A compiled
    -- source formula with one free variable gives one, and this module
    -- restates the consumer facing results at the architecture's printed
    -- shape. Its telescope is abstract on purpose: the source type, the
    -- environment type, the cons of an environment, the value of a formula at
    -- an environment, the value of its existential closure, and the two
    -- quantifier clauses of Track F's InterpLaws. Track F fills all six with
    -- Formula (⊥* {ℓ}) k, Vec Name k, _∷_, the two projections of interp and
    -- its ∃-ub and ∃-lub.

    module Formulas
      (Src : ℕ → Type ℓ)
      (Env : ℕ → Type ℓ)
      (_∷ᵉ_  : {k : ℕ} → Name → Env k → Env (suc k))
      (val   : {k : ℕ} → Src k → Env k → Pt B)
      (exVal : {k : ℕ} → Src (suc k) → Env k → Pt B)
      (∃-ub  : {k : ℕ} (φ : Src (suc k)) (ν : Env k) (σ : Name)
             → ⟨ val φ (σ ∷ᵉ ν) ≤ᴮ exVal φ ν ⟩)
      (∃-lub : {k : ℕ} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
             → ((σ : Name) → ⟨ val φ (σ ∷ᵉ ν) ≤ᴮ c ⟩)
             → ⟨ exVal φ ν ≤ᴮ c ⟩)
      where

      family : {k : ℕ} → Src (suc k) → Env k → Name → Pt B
      family φ ν σ = val φ (σ ∷ᵉ ν)

      existential : {k : ℕ} (φ : Src (suc k)) (ν : Env k)
                  → Lub (family φ ν) (exVal φ ν)
      existential φ ν = record { ub = ∃-ub φ ν ; lub = ∃-lub φ ν }

      BooleanUniqueAt : {k : ℕ} → Src (suc k) → Env k → Type ℓ
      BooleanUniqueAt φ ν = BooleanUnique (family φ ν)

      RawUniqueAt : {k : ℕ} → Src (suc k) → Env k → Type ℓ
      RawUniqueAt φ ν = RawUnique (family φ ν)

      -- Bell Problem 1.29 at the architecture's printed signature. The
      -- conclusion is a path between the value of φ at the witness and the
      -- value of its existential closure, with no truncation in sight.

      unique-witness-at : {k : ℕ} (φ : Src (suc k)) (ν : Env k)
                        → BooleanUniqueAt φ ν
                        → Congruent (family φ ν)
                        → (A : AdequateDomain (family φ ν) (exVal φ ν))
                        → (u : Name)
                        → WitnessSpec (family φ ν) (AdequateDomain.dom A) u
                        → val φ (u ∷ᵉ ν) ≡ exVal φ ν
      unique-witness-at φ ν bu cg A u W =
        unique-witness (family φ ν) (exVal φ ν) (existential φ ν) bu cg A u W

      -- The fullness contract at the architecture's printed signature.
      -- SHIPPED WITH NO INHABITANT: the only function in this file whose
      -- result is a FullnessAt takes a MaximumPrincipleContract, and no
      -- function anywhere in this file returns one of those.

      record FullnessAt {k : ℕ} (φ : Src (suc k)) : Type ℓ where
        field
          witness : (ν : Env k)
                  → ∥ Σ[ τ ∈ Name ] (val φ (τ ∷ᵉ ν) ≡ exVal φ ν) ∥₁

      contract→fullness-at : MaximumPrincipleContract
                           → {k : ℕ} (φ : Src (suc k))
                           → ((ν : Env k) → Congruent (family φ ν))
                           → FullnessAt φ
      contract→fullness-at K φ cg = record
        { witness = λ ν →
            Fullness.witness
              (MaximumPrinciple.attained (contract→mp K)
                (family φ ν) (exVal φ ν) (existential φ ν) (cg ν)) }

-- WHAT IS NOT CLAIMED, and each absence is grep checkable over this file.
--
-- No inhabitant of Fullness, FullnessAt, MaximumPrinciple,
-- MaximumPrincipleContract, ElementPrinciple, MixtureSupply, Refinement,
-- Separated, ValueCover, Mixture, WitnessSpec or AdequateDomain out of the
-- algebra records alone. Every constructor application in this file is inside
-- a function that takes an inhabitant of a strictly stronger record as an
-- argument.
--
-- No construction of a mixture, no construction of a witness name, no
-- construction of an adequate domain, no enumeration of a value family. No
-- use of Separation, Collection, PowerSet, or any field of CodedComplete. No
-- elimination of a truncated sigma over Name into Name or into Pt B: the only
-- eliminations in the file are PT.map and one PT.rec whose target is itself a
-- truncation.
--
-- No claim that Problem 1.30's equivalence is formalized. What is formalized
-- is the two arrows that make the citation bite, contract→mp and
-- fullness→element, with Bell's equivalence cited and not proved.
--
-- No agreement with the host evaluator, no reads-sup or reads-inf, no atomic
-- graph, no compiled formula. Obstructions O1 and O2 are untouched.
