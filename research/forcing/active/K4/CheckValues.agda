{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track H: the Boolean values of the check names. Bell Definition 1.22 and
-- Theorem 1.23 (bell-2005-boolean-valued-models.fulltext.md:2335-2450).
--
-- WHAT THIS FILE IS ABOUT. K3 built the check name: a recursion on the ground's
-- membership sending a set a to the name whose entries pair the check name of
-- each member with the top weight (StandardNames.agda:492, :517). That is a
-- statement about CODES. This file asks the only question K3 could not: what
-- are the BOOLEAN VALUES of the two atomic relations at a pair of check names,
-- and how faithfully do they record the ground's own membership and equality.
--
-- Bell's answers are four. (i) The value of u ∈ ǎ is the join of the values of
-- u = y̌ over the members y of a, with no weight left over, because every weight
-- of a check name is the top. (ii) At a pair of check names the two atomic
-- values are the top exactly when the ground relation holds. (iii) The check map
-- is injective, which is K3's check-inj (StandardNames.agda:575) and is not
-- restated here. (iv) Every two valued name is the check name of a unique set;
-- the uniqueness half is proved below and the existence half is deferred with
-- its reason. (v) Truth of a restricted formula transfers in both directions.
--
-- THE ONE THING A READER SHOULD CARRY AWAY. Clause (ii) is FALSE at a degenerate
-- algebra and no amount of care in its proof can repair that: if the top and the
-- bottom of the algebra coincide then every value is the top, so the clause would
-- prove that every set is a member of every set. The refutation is machine
-- checked below (arch-check-∈-⊤-refuted) and it is why nontriviality appears in
-- the hypothesis list of module Classical. The architecture's section 1.9 prints
-- check-≈-⊤ and check-∈-⊤ with no such hypothesis.
--
-- ---------------------------------------------------------------------
-- The ledger, which is the module telescope and nothing else
-- ---------------------------------------------------------------------
--
-- Track A's three algebra records, opened by one route and re-exported by none,
-- per REPORT-A.md section 4's scope contract. Track A's implication theory for
-- _⇒ᴮ_ and the finite Boolean calculus. The name layer flat, in Track C's and
-- Track D's shape. K3's check flat: the function, its entry specification and
-- its validity. Track C's AtomicSemantics flat, field for field. Four of Track
-- D's laws, flat.
--
-- NOT taken, and each absence is part of the contract: no CodedComplete field
-- is projected, no supᴮ and no infᴮ occurs anywhere, no residual law of either
-- variance, no infinite distributive law, no Separation, no Collection, no
-- PowerSet, no Union, no value set, no name recogniser in any statement except
-- the one hypothesis support-in demands, no atomic graph, no compiler.
--
-- WHY THERE IS NO acc∈ AND NO WFI.induction, although clause (ii) is an
-- induction. The architecture's trap 1 for this track forbids both, on the
-- ground that check is a parameter and this track runs no recursion of its own.
-- Clause (ii) is nevertheless Bell's induction on rank and cannot be had without
-- one. The way out is measured rather than argued: the induction needed is over
-- the CHILDREN of a check name, and a child of check a is the check name of a
-- member of a (check-support-out below). So Track D's rawRec, which is already a
-- parameter of the atomic layer, carries the whole proof, and the ground's own
-- membership accessibility is not required. grep for acc∈ and WFI over this file
-- returns 0.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module K4.CheckValues {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Base.Classical using ( LEM )
open import Cubical.Data.Sigma using ( _×_ ; _,_ )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
open import Cubical.Foundations.Equiv using ( _≃_ ; propBiimpl→Equiv )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

open import OrdinaryProfile 𝒮 using ( iff )

open import FOL.Syntax
  using ( Term ; Formula ; con ; var
        ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ ; _⇒̇_ ; ⊥̇ ; ∃̇_ ; ∀̇_ ; ∀̇∈ ; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At ; _^_ )
open import FOL.LevyHierarchy
  using ( Δ₀ ; δ-∈ ; δ-≐ ; δ-∧ ; δ-∨ ; δ-⇒ ; δ-⊥ ; δ-∀∈ ; δ-∃∈ )
open import FOL.Manipulation.ConstantMapping using ( embed )
open At S id using ( _⊨_ )

open K4.Algebra 𝒮
  using ( Pt ; Pt≡ ; isSetPt ; _≤ᴮ_ ; ≤ᴮ-refl ; ⊆ˢ-trans
        ; Lattice ; Complement ; CodedComplete )

-- The two crossings between the structure's equality and the host path, the
-- same two lines as K4/Atomic.agda:132-137 and K4/AtomicLaws.agda:105-110.

≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
≈ˢ-refl x = subst ⟨_⟩ (sym (paths x x)) refl

-- The compiler's input alphabet, architecture section 1.7's own spelling and
-- Track F's (K4/Compile.agda:499-500). The constant domain is empty, so every
-- term of an input formula is a variable and the bound of a bounded quantifier
-- is always a slot of the environment; that is the fact the two bounded cases
-- of the Δ₀ induction at the foot of this file rely on, and it is why the two
-- `con` clauses there are absurd rather than argued.

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

--------------------------------------------------------------------------------
-- The algebra layer
--------------------------------------------------------------------------------

-- The uniform telescope of architecture section 1.2, (B) (L) (Cm) (Kc), kept
-- so that the coordinator's application reads the same as for tracks C, D, F
-- and I. MEASURED: this track projects no field of Kc at all. Track D projects
-- six of them, in bell-1-15 and bell-1-16 only; here not one, because every
-- value statement below is an order statement against the two atomic values
-- and no join of a coded family is ever formed or named.

module Core
  (B  : S)
  (L  : Lattice B)
  (Cm : Complement B L)
  (Kc : CodedComplete B L)
  where

  open Lattice L
  open K4.Implication 𝒮 ext paths B L Cm
    using ( ≤ᴮ-antisym ; _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry ; ⇒ᴮ-⊤ ; ⇒ᴮ-⊤ˡ
          ; ⊓-comm ; ⊓-idem ; ⊓-⊤ ; ⊓-⊥ ; ⊔-comm ; ⊔-⊥ˡ ; ⊔-⊤ ; ≤⊥→≡⊥ )

  ------------------------------------------------------------------------------
  -- A small order toolkit
  ------------------------------------------------------------------------------

  -- Four moves, named once rather than inlined at forty sites. R1's failure
  -- shape is a bare reflexivity standing in for an unchanged endpoint of a
  -- congruence over a truth value operation; here every endpoint is written out
  -- and the only equations proved are between elements of Pt B, whose equality
  -- has no propositionality component to leave as a metavariable.

  ≡⊤ : (u : Pt B) → ⟨ ⊤ᴮ ≤ᴮ u ⟩ → u ≡ ⊤ᴮ
  ≡⊤ u h = ≤ᴮ-antisym (⊤-greatest u) h

  ≡⊥ : (u : Pt B) → ⟨ u ≤ᴮ ⊥ᴮ ⟩ → u ≡ ⊥ᴮ
  ≡⊥ = ≤⊥→≡⊥

  ⊤≤ : (u : Pt B) → u ≡ ⊤ᴮ → ⟨ ⊤ᴮ ≤ᴮ u ⟩
  ⊤≤ u p = subst (λ z → ⟨ ⊤ᴮ ≤ᴮ z ⟩) (sym p) (≤ᴮ-refl ⊤ᴮ)

  ≤⊥ : (u : Pt B) → u ≡ ⊥ᴮ → ⟨ u ≤ᴮ ⊥ᴮ ⟩
  ≤⊥ u p = subst (λ z → ⟨ z ≤ᴮ ⊥ᴮ ⟩) (sym p) (≤ᴮ-refl ⊥ᴮ)

  -- An order statement and its curried form against the top, the same bridge
  -- Track D names at K4/AtomicLaws.agda:166-172 and for the same reason: a
  -- greatest lower bound property produces its bound from the top element, so
  -- every implication clause below crosses here.

  ≤→⊤⇒ : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → ⟨ ⊤ᴮ ≤ᴮ (u ⇒ᴮ v) ⟩
  ≤→⊤⇒ u v h = ⇒ᴮ-curry ⊤ᴮ u v (⊆ˢ-trans (⊓-lb₂ ⊤ᴮ u) h)

  -- The three finite identities the connective calculus needs and Track A's
  -- file states only in the mirrored orientation.

  ⊓-⊥ˡ : (u : Pt B) → (⊥ᴮ ⊓ᴮ u) ≡ ⊥ᴮ
  ⊓-⊥ˡ u = ⊓-comm ⊥ᴮ u ∙ ⊓-⊥ u

  ⊔-⊤ˡ : (u : Pt B) → (⊤ᴮ ⊔ᴮ u) ≡ ⊤ᴮ
  ⊔-⊤ˡ u = ⊔-comm ⊤ᴮ u ∙ ⊔-⊤ u

  -- Falsity implies anything, and this is the one place where the shape of
  -- _⇒ᴮ_ could have been unfolded and is not: the adjunction alone proves it,
  -- so no complement law is spent here and De Morgan is never reached.

  ⇒ᴮ-⊥ˡ : (v : Pt B) → (⊥ᴮ ⇒ᴮ v) ≡ ⊤ᴮ
  ⇒ᴮ-⊥ˡ v = ≡⊤ (⊥ᴮ ⇒ᴮ v)
    (⇒ᴮ-curry ⊤ᴮ ⊥ᴮ v (⊆ˢ-trans (⊓-lb₂ ⊤ᴮ ⊥ᴮ) (⊥-least v)))

  ------------------------------------------------------------------------------
  -- Reflection: the two valued bridge between a value and a truth value
  ------------------------------------------------------------------------------

  -- Bell states 1.23(ii) and (v) as biconditionals, and a biconditional is not
  -- enough to run either induction. The reason is the join. A join of Boolean
  -- values is the top only if SOME member is the top, and in a general Boolean
  -- algebra that inference fails: the join of p and its complement is the top
  -- with neither factor the top. What licenses it for check names is that their
  -- atomic values are two valued, and two valuedness is not a consequence of
  -- the biconditional. So the datum carried through both inductions is the
  -- STRONGER one: the value is the top and the proposition holds, or the value
  -- is the bottom and the proposition fails.
  --
  -- Reflects is DATA, not a proposition. That is deliberate and it is what makes
  -- the connective clauses below one line each: a sum is eliminated by a case
  -- split and no truncation has to be opened.

  Reflects : Pt B → Ω → Type ℓ
  Reflects u P = ((u ≡ ⊤ᴮ) × ⟨ P ⟩) ⊎ ((u ≡ ⊥ᴮ) × (⟨ P ⟩ → Empty.⊥))

  -- Its two projections, the ones a consumer that wants only Bell's
  -- biconditional will use. The forward one is where nontriviality is spent and
  -- it is therefore a parameter of the map rather than of the record.

  reflects-true : (u : Pt B) (P : Ω) → (⊤ᴮ ≡ ⊥ᴮ → Empty.⊥)
                → Reflects u P → u ≡ ⊤ᴮ → ⟨ P ⟩
  reflects-true u P nt (inl (_ , hp)) _ = hp
  reflects-true u P nt (inr (p , _))  q = Empty.rec (nt (sym q ∙ p))

  reflects-holds : (u : Pt B) (P : Ω) → Reflects u P → ⟨ P ⟩ → u ≡ ⊤ᴮ
  reflects-holds u P (inl (p , _))  _  = p
  reflects-holds u P (inr (_ , np)) hp = Empty.rec (np hp)

  reflects-two-valued : (u : Pt B) (P : Ω) → Reflects u P
                      → (u ≡ ⊤ᴮ) ⊎ (u ≡ ⊥ᴮ)
  reflects-two-valued u P (inl (p , _)) = inl p
  reflects-two-valued u P (inr (p , _)) = inr p

  reflects→equiv : (u : Pt B) (P : Ω) → (⊤ᴮ ≡ ⊥ᴮ → Empty.⊥)
                 → Reflects u P → (u ≡ ⊤ᴮ) ≃ ⟨ P ⟩
  reflects→equiv u P nt r =
    propBiimpl→Equiv (isSetPt B u ⊤ᴮ) (snd P)
      (reflects-true u P nt r) (reflects-holds u P r)

  ------------------------------------------------------------------------------
  -- The connective calculus of reflection
  ------------------------------------------------------------------------------

  -- These five lemmas are the whole content of the propositional half of Bell
  -- 1.23(v), and they are stated here, above every name layer hypothesis,
  -- because they are facts about a Boolean algebra and a truth algebra and
  -- about nothing else. The Δ₀ induction at the foot of the file consumes them
  -- verbatim; so would any other formula induction.
  --
  -- Note which of them needs two valuedness and which does not. The meet does
  -- not: a meet is the top exactly when both factors are. The join and the
  -- implication do, and that is exactly the place where a proof of 1.23(v) that
  -- carried only Bell's biconditional would stop.

  reflects-⊓ : (u v : Pt B) (P Q : Ω)
             → Reflects u P → Reflects v Q → Reflects (u ⊓ᴮ v) (P ⊓ Q)
  reflects-⊓ u v P Q (inl (pu , hp)) (inl (pv , hq)) =
    inl ( cong (λ z → u ⊓ᴮ z) pv ∙ cong (λ z → z ⊓ᴮ ⊤ᴮ) pu ∙ ⊓-⊤ ⊤ᴮ
        , (hp , hq) )
  reflects-⊓ u v P Q (inl (pu , hp)) (inr (pv , nq)) =
    inr ( cong (λ z → u ⊓ᴮ z) pv ∙ ⊓-⊥ u , (λ z → nq (snd z)) )
  reflects-⊓ u v P Q (inr (pu , np)) _ =
    inr ( cong (λ z → z ⊓ᴮ v) pu ∙ ⊓-⊥ˡ v , (λ z → np (fst z)) )

  reflects-⊔ : (u v : Pt B) (P Q : Ω)
             → Reflects u P → Reflects v Q → Reflects (u ⊔ᴮ v) (P ⊔ Q)
  reflects-⊔ u v P Q (inl (pu , hp)) _ =
    inl ( cong (λ z → z ⊔ᴮ v) pu ∙ ⊔-⊤ˡ v , ∣ inl hp ∣₁ )
  reflects-⊔ u v P Q (inr (pu , np)) (inl (pv , hq)) =
    inl ( cong (λ z → u ⊔ᴮ z) pv ∙ cong (λ z → z ⊔ᴮ ⊤ᴮ) pu ∙ ⊔-⊤ ⊥ᴮ
        , ∣ inr hq ∣₁ )
  reflects-⊔ u v P Q (inr (pu , np)) (inr (pv , nq)) =
    inr ( cong (λ z → u ⊔ᴮ z) pv ∙ cong (λ z → z ⊔ᴮ ⊥ᴮ) pu ∙ ⊔-⊥ˡ ⊥ᴮ
        , PT.rec Empty.isProp⊥ (λ { (inl hp) → np hp ; (inr hq) → nq hq }) )

  reflects-⇒ : (u v : Pt B) (P Q : Ω)
             → Reflects u P → Reflects v Q → Reflects (u ⇒ᴮ v) (P ⇒ Q)
  reflects-⇒ u v P Q (inl (pu , hp)) (inl (pv , hq)) =
    inl ( cong (λ z → u ⇒ᴮ z) pv ∙ ⇒ᴮ-⊤ u , (λ _ → hq) )
  reflects-⇒ u v P Q (inl (pu , hp)) (inr (pv , nq)) =
    inr ( cong (λ z → u ⇒ᴮ z) pv ∙ cong (λ z → z ⇒ᴮ ⊥ᴮ) pu ∙ ⇒ᴮ-⊤ˡ ⊥ᴮ
        , (λ f → nq (f hp)) )
  reflects-⇒ u v P Q (inr (pu , np)) r =
    inl ( cong (λ z → z ⇒ᴮ v) pu ∙ ⇒ᴮ-⊥ˡ v , (λ hp → Empty.rec (np hp)) )

  reflects-⊥ : Reflects ⊥ᴮ ⊥
  reflects-⊥ = inr ( refl , Empty.rec* )

  reflects-subst : (u v : Pt B) (P : Ω) → u ≡ v → Reflects u P → Reflects v P
  reflects-subst u v P p = subst (λ z → Reflects z P) p

  --------------------------------------------------------------------------------
  -- The name layer
  --------------------------------------------------------------------------------

  -- The telescope below is Track C's and Track D's name layer, plus the entry
  -- vocabulary of K3's kernel, plus K3's check. Every one of the K3 items is a
  -- flat parameter and therefore a variable, which is the tightest seal there
  -- is (preamble rule R2): nothing here can unfold a description operator,
  -- because there is none to unfold.
  --
  -- Reading the parameters in groups.
  --
  --  * Child, rawRec, support, support-out, weightᴮ: Track D's Core telescope,
  --    character for character (K4/AtomicLaws.agda:133-146). rawRec is
  --    NameKernel.agda:400-405's RawRec.result at ℓp := ℓ, and it is what runs
  --    Bell's induction for clause (ii).
  --  * entry, entry-inj, child-entry, child-elim: NameKernel.agda:253, :317,
  --    and the two halves of Child's own introduction and elimination. Child is
  --    ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁ (NameKernel.agda:369) and is
  --    transparent there, so both halves are one line at the instance. K3's
  --    Track H took child-elim on the same ground (REPORT-H.md section 6) and
  --    recorded the caveat: if the kernel ever seals Child, both halves must be
  --    exported.
  --  * IsName and support-in: NameSupport.agda:542. This is the ONE place a
  --    recogniser enters. The inward direction of the support genuinely needs
  --    it, because a bare child arrives with a weight that nothing places
  --    inside the carrier, and only the shape clause of IsName does. It is
  --    discharged at check a by K3's check-name and nowhere else, which is why
  --    check-name is on the architecture's permitted list.
  --  * weight-ub and weight-least: NameWeight.agda:412 and :425, with the pair
  --    (b , hb) reassembled into one Pt B argument so that a consumer passes an
  --    element rather than a code and a membership proof. At the instance each
  --    is one line.
  --  * check, check-spec, check-name: StandardNames.agda:492, :517, :564. The
  --    top weight of check-spec is written fst ⊤ᴮ, so the coordinator
  --    instantiates K3's module Standard at ⊤ᴮ := fst (Lattice.⊤ᴮ L). K3 takes
  --    its own ⊤ᴮ as an arbitrary member of B and never assumes it is the top
  --    (StandardNames.agda:455-459), so this identification is the instance's
  --    to make and it costs nothing here.

  module Names
    (Child       : S → S → Type ℓ)
    (rawRec      : (P : S → Type ℓ)
                 → ((n : S) → ((x : S) → Child x n → P x) → P n)
                 → (n : S) → P n)
    (support     : S → S)
    (support-out : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n)
    (weightᴮ     : (n x : S) → Pt B)
    (entry       : S → S → S)
    (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
    (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
    (child-elim  : (x n : S) → Child x n
                 → ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
    (IsName      : S → Ω)
    (support-in  : (n : S) → ⟨ IsName n ⟩ → (x : S) → Child x n
                 → ⟨ x ∈ˢ support n ⟩)
    (weight-ub   : (n x : S) (b : Pt B) → ⟨ entry x (fst b) ∈ˢ n ⟩
                 → ⟨ b ≤ᴮ weightᴮ n x ⟩)
    (weight-least : (n x : S) (v : Pt B)
                 → ((b : Pt B) → ⟨ entry x (fst b) ∈ˢ n ⟩ → ⟨ b ≤ᴮ v ⟩)
                 → ⟨ weightᴮ n x ≤ᴮ v ⟩)
    (check       : S → S)
    (check-spec  : (a e : S) → (e ∈ˢ check a)
                 ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (e ≈ˢ entry (check y) (fst ⊤ᴮ))))
    (check-name  : (a : S) → ⟨ IsName (check a) ⟩)
    where

    ----------------------------------------------------------------------------
    -- What a check name's domain and weights are
    ----------------------------------------------------------------------------

    -- Bell writes x̌ = { ⟨y̌ , 1⟩ : y ∈ x } and then uses two facts about it
    -- without naming them: that the domain is exactly the check names of the
    -- members, and that every weight is the top. Neither is available from
    -- check-spec alone, because check-spec is about the MEMBERS of the code and
    -- the support and the weight are separate constructions of K3 (a separation
    -- on ⋃² n, NameSupport.agda:517, and a supremum of a separated weight
    -- family, NameWeight.agda:204). The four lemmas below are the bridge, and
    -- they are the only place in this file where an entry is taken apart.

    check-entry : (a y : S) → ⟨ y ∈ˢ a ⟩
                → ⟨ entry (check y) (fst ⊤ᴮ) ∈ˢ check a ⟩
    check-entry a y h =
      subst ⟨_⟩ (sym (check-spec a (entry (check y) (fst ⊤ᴮ))))
        ∣ y , h , ≈ˢ-refl (entry (check y) (fst ⊤ᴮ)) ∣₁

    check-child : (a y : S) → ⟨ y ∈ˢ a ⟩ → Child (check y) (check a)
    check-child a y h =
      child-entry (check y) (fst ⊤ᴮ) (check a) (check-entry a y h)

    check-support : (a y : S) → ⟨ y ∈ˢ a ⟩ → ⟨ check y ∈ˢ support (check a) ⟩
    check-support a y h =
      support-in (check a) (check-name a) (check y) (check-child a y h)

    -- The weight is the top exactly, not merely above it. Above it is what the
    -- entry gives; the other half is ⊤-greatest, and the equation is what the
    -- implication steps of clause (ii) need, since ⇒ᴮ-⊤ˡ asks for the top on
    -- the nose.

    check-weight : (a y : S) → ⟨ y ∈ˢ a ⟩ → weightᴮ (check a) (check y) ≡ ⊤ᴮ
    check-weight a y h =
      ≡⊤ (weightᴮ (check a) (check y))
         (weight-ub (check a) (check y) ⊤ᴮ (check-entry a y h))

    -- And the converse of check-support, which is the lemma that makes Bell's
    -- induction run on Child rather than on the ground's membership: every
    -- child of a check name IS the check name of a member. The witness is
    -- truncated and stays truncated; nothing below ever chooses one.

    check-support-out : (a x : S) → ⟨ x ∈ˢ support (check a) ⟩
                      → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ a ⟩ × (x ≡ check y)) ∥₁
    check-support-out a x h =
      PT.rec PT.squash₁
        (λ { (b , hb) →
               PT.map (λ { (y , hy , eqn) →
                             y , hy , fst (entry-inj (≈→≡ eqn)) })
                      (subst ⟨_⟩ (check-spec a (entry x b)) hb) })
        (child-elim x (check a) (support-out (check a) x h))

    ----------------------------------------------------------------------------
    -- The check environment
    ----------------------------------------------------------------------------

    -- The compiler's environments are vectors of NAMES, so a formula about
    -- ground sets reaches it only after every parameter has been replaced by
    -- its check name. That replacement is this map, architecture section 1.7's
    -- checkEnv, and the two lemmas beside it are all that any consumer needs
    -- about it.
    --
    -- Name is written out as the Σ type rather than imported. A Σ type is not
    -- generative, so this is definitionally Track F's Name = Fib IsName
    -- (K4/Compile.agda:502-503) and no coercion is needed at the application.

    Name : Type ℓ
    Name = Σ[ n ∈ S ] ⟨ IsName n ⟩

    checkName : S → Name
    checkName a = check a , check-name a

    checkEnv : ∀ {k} → S ^ k → Vec Name k
    checkEnv []      = []
    checkEnv (a ∷ γ) = checkName a ∷ checkEnv γ

    -- Every slot of a check environment holds the check name of the same slot
    -- of the ground environment. Both sides compute, so each case is refl and
    -- the induction is on the slot rather than on anything mathematical; it is
    -- written out because the compiler's laws speak of the environment's names
    -- and every atomic clause below speaks of the ground's sets.

    lookup-check : ∀ {k} (i : Fin k) (γ : S ^ k)
                 → fst (lookup i (checkEnv γ)) ≡ check (lookup i γ)
    lookup-check zero    (a ∷ γ) = refl
    lookup-check (suc i) (a ∷ γ) = lookup-check i γ

    ----------------------------------------------------------------------------
    -- The atomic values
    ----------------------------------------------------------------------------

    -- Track C's AtomicSemantics, field for field and in its order, with the
    -- operator spellings restored, exactly as Track D takes it
    -- (K4/AtomicLaws.agda:186-205). Then four of Track D's laws. The glb field
    -- eqᴬ-glb is NOT taken: measured, nothing below needs it, because every
    -- statement here bounds a value from above or reads one that is already
    -- known to be the top.

    module Values
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
      (≈ᴮ-sym : (m n : S) → (m ≈ᴮ n) ≡ (n ≈ᴮ m))
      (≈ᴮ-refl : (n : S) → (n ≈ᴮ n) ≡ ⊤ᴮ)
      (≈ᴮ-trans : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (n ≈ᴮ p)) ≤ᴮ (m ≈ᴮ p) ⟩)
      (ext-≈ᴮ : (m n : S) → ((r : S) → (r ∈ᴮ m) ≡ (r ∈ᴮ n)) → (m ≈ᴮ n) ≡ ⊤ᴮ)
      (∈ᴮ-empty : (m n : S) → ((x : S) → ⟨ x ∈ˢ support n ⟩ → ⟨ ⊥ ⟩)
                → (m ∈ᴮ n) ≡ ⊥ᴮ)
      where

      --------------------------------------------------------------------------
      -- Bell 1.23(i)
      --------------------------------------------------------------------------

      -- Bell computes ⟦u ∈ x̌⟧ = ⋁_{v ∈ dom(x̌)} [x̌(v) ∧ ⟦u = v⟧] = ⋁_{y ∈ x}
      -- ⟦u = y̌⟧ (fulltext:2374-2385). The second step is the disappearance of
      -- the weight, and it is the whole content: the weight is the top, so the
      -- meet with it is inert.
      --
      -- SHIPPED AS A BOUND PAIR, not as the equation. R3 forbids a signature
      -- naming a join of a constructed set, and there is no join of a HOST
      -- family to name in any case: the family is indexed by the members of a,
      -- which is not a ground code, so the equation is not statable here at all.
      -- The pair says everything the equation does and is what a consumer
      -- calls; Track D's bell-1-15 turns it back into an equation against any
      -- ground code that realises the family.
      --
      -- Stated at a RAW CODE m, where architecture section 1.9 prints a Name τ
      -- and uses fst τ. The atomic layer is recogniser free (REPORT-C.md
      -- section C3), both values are total on raw codes, and nothing in either
      -- proof looks at a name proof, so the raw form is strictly more general
      -- and the architecture's form is fst applied to it. Measured: no statement
      -- of Bell 1.23(i), (ii) or (iv) below mentions IsName. The recogniser
      -- enters this file at exactly three places and each is unavoidable: the
      -- hypothesis of support-in, which is what check-name was put on the
      -- permitted list for; the statement of the deferred existence half of
      -- (iv), which is about names by definition; and the compiler's own Name
      -- type in the Δ₀ layer, whose environments are vectors of names.

      check-∈-ub : (a y m : S) → ⟨ y ∈ˢ a ⟩
                 → ⟨ (m ≈ᴮ check y) ≤ᴮ (m ∈ᴮ check a) ⟩
      check-∈-ub a y m h =
        ⊆ˢ-trans widen (∈ᴮ-ub m (check a) (check y) (check-support a y h))
        where
          top : ⟨ (m ≈ᴮ check y) ≤ᴮ weightᴮ (check a) (check y) ⟩
          top = subst (λ z → ⟨ (m ≈ᴮ check y) ≤ᴮ z ⟩)
                      (sym (check-weight a y h))
                      (⊤-greatest (m ≈ᴮ check y))

          widen : ⟨ (m ≈ᴮ check y)
                    ≤ᴮ ((weightᴮ (check a) (check y)) ⊓ᴮ (m ≈ᴮ check y)) ⟩
          widen = ⊓-glb (weightᴮ (check a) (check y)) (m ≈ᴮ check y)
                        (m ≈ᴮ check y) top (≤ᴮ-refl (m ≈ᴮ check y))

      check-∈-lub : (a m : S) (c : Pt B)
                  → ((y : S) → ⟨ y ∈ˢ a ⟩ → ⟨ (m ≈ᴮ check y) ≤ᴮ c ⟩)
                  → ⟨ (m ∈ᴮ check a) ≤ᴮ c ⟩
      check-∈-lub a m c hyp = ∈ᴮ-lub m (check a) c step
        where
          step : (x : S) → ⟨ x ∈ˢ support (check a) ⟩
               → ⟨ ((weightᴮ (check a) x) ⊓ᴮ (m ≈ᴮ x)) ≤ᴮ c ⟩
          step x hx =
            PT.rec (snd (((weightᴮ (check a) x) ⊓ᴮ (m ≈ᴮ x)) ≤ᴮ c))
              (λ { (y , hy , p) →
                     ⊆ˢ-trans (⊓-lb₂ (weightᴮ (check a) x) (m ≈ᴮ x))
                       (subst (λ z → ⟨ (m ≈ᴮ z) ≤ᴮ c ⟩) (sym p) (hyp y hy)) })
              (check-support-out a x hx)

      -- The one corollary of the pair that is used at every later step: the
      -- value of a check name in a check name is the top as soon as the ground
      -- membership holds. No classical hypothesis and no nontriviality.

      check-∈-top : (a b : S) → ⟨ a ∈ˢ b ⟩ → (check a ∈ᴮ check b) ≡ ⊤ᴮ
      check-∈-top a b h =
        ≡⊤ (check a ∈ᴮ check b)
           (subst (λ z → ⟨ z ≤ᴮ (check a ∈ᴮ check b) ⟩)
                  (≈ᴮ-refl (check a))
                  (check-∈-ub b a (check a) h))

      --------------------------------------------------------------------------
      -- The degenerate algebra, where Bell 1.23(ii) is FALSE
      --------------------------------------------------------------------------

      -- Architecture section 1.9 prints check-≈-⊤ and check-∈-⊤ as unconditional
      -- equivalences. They are not. At an algebra whose top and bottom coincide
      -- every element is the top, so the forward direction of the membership
      -- clause proves that any set belongs to any set. This is transcribed and
      -- refuted rather than asserted, on the pattern of Track A's treatment of
      -- the architecture's inf-residual (REPORT-A.md section 3).
      --
      -- The refutation is completed in module Zero, where an empty name is in
      -- the ledger and the conclusion can be driven to absurdity outright.

      ArchCheck∈⊤ : Type ℓ
      ArchCheck∈⊤ = (a b : S) → ((check a ∈ᴮ check b) ≡ ⊤ᴮ) → ⟨ a ∈ˢ b ⟩

      ArchCheck≈⊤ : Type ℓ
      ArchCheck≈⊤ = (a b : S) → ((check a ≈ᴮ check b) ≡ ⊤ᴮ) → ⟨ a ≈ˢ b ⟩

      degenerate-all-⊤ : ⊤ᴮ ≡ ⊥ᴮ → (u : Pt B) → u ≡ ⊤ᴮ
      degenerate-all-⊤ deg u =
        ≡⊤ u (subst (λ z → ⟨ z ≤ᴮ u ⟩) (sym deg) (⊥-least u))

      arch-check-∈-⊤-collapses : ⊤ᴮ ≡ ⊥ᴮ → ArchCheck∈⊤ → (a b : S) → ⟨ a ∈ˢ b ⟩
      arch-check-∈-⊤-collapses deg f a b =
        f a b (degenerate-all-⊤ deg (check a ∈ᴮ check b))

      arch-check-≈-⊤-collapses : ⊤ᴮ ≡ ⊥ᴮ → ArchCheck≈⊤ → (a b : S) → ⟨ a ≈ˢ b ⟩
      arch-check-≈-⊤-collapses deg f a b =
        f a b (degenerate-all-⊤ deg (check a ≈ᴮ check b))

      --------------------------------------------------------------------------
      -- Bell 1.23(ii), the induction
      --------------------------------------------------------------------------

      -- Bell leaves this one to the reader: "(ii) is established by induction on
      -- rank(y), the induction hypothesis being: for all z with rank(z) <
      -- rank(y) ... We leave the tedious but straightforward details to the
      -- reader" (fulltext:2390-2400). The details are not straightforward and
      -- three of them are worth stating before the code.
      --
      -- FIRST, the induction hypothesis carries THREE clauses and not one.
      -- Bell's own list is: for all x, x ∈ z iff ⟦x̌ ∈ ž⟧ = 1; x = z iff
      -- ⟦x̌ = ž⟧ = 1; z ∈ x iff ⟦ž ∈ x̌⟧ = 1. The third looks redundant beside
      -- the first and is not: the first is about the members of z, whose rank
      -- is controlled, while the third is about the members of an ARBITRARY x,
      -- whose rank is not. Both are needed to close the equality clause, and
      -- each is used at exactly one step below.
      --
      -- SECOND, the clauses are carried as Reflects and not as biconditionals,
      -- for the reason module Core's comment gives: the join step needs two
      -- valuedness.
      --
      -- THIRD, only two of the three clauses go into the motive. The first
      -- is derived INSIDE the step from the second clause of the inductive
      -- hypothesis, so carrying it would be carrying a consequence.
      --
      -- Hypotheses, both of them necessary and neither of them in the
      -- architecture's list for this track. LEM ℓ is spent at three decisions
      -- and at one classical extensionality step; nontriviality is spent at
      -- exactly one place, the passage from a reflection to Bell's own
      -- biconditional, and the refutation above shows the theorem is false
      -- without it. LEM sits on the module and not on the file, which is K2's
      -- pattern at CodedCompletion.agda:1282-1291.

      module Classical (lem : LEM ℓ) (nontrivial : ⊤ᴮ ≡ ⊥ᴮ → Empty.⊥) where

        -- One classical fact, used twice below and stated once. A bounded
        -- universal that fails has a counterexample among the members of the
        -- bound, merely. Constructively this is nothing; classically it is two
        -- applications of excluded middle, one to the truncated statement
        -- itself and one to the predicate at each member. The witness is never
        -- chosen: the conclusion is truncated and every consumer eliminates it
        -- into a proposition.

        witness-fail : (A : S) (R : S → Ω)
                     → (((x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ R x ⟩) → Empty.⊥)
                     → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ A ⟩ × (⟨ R y ⟩ → Empty.⊥)) ∥₁
        witness-fail A R nq
          with lem (∥ Σ[ y ∈ S ] (⟨ y ∈ˢ A ⟩ × (⟨ R y ⟩ → Empty.⊥)) ∥₁
                   , PT.squash₁)
        ... | inl t  = t
        ... | inr nt = Empty.rec (nq total)
          where
            total : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ R x ⟩
            total x hx with lem (R x)
            ... | inl h  = h
            ... | inr nh = Empty.rec (nt ∣ x , hx , nh ∣₁)

        -- The two clauses of the motive at one ground set.

        Clauses : S → Type ℓ
        Clauses y = ((x : S) → Reflects (check x ≈ᴮ check y) (x ≈ˢ y))
                  × ((x : S) → Reflects (check y ∈ᴮ check x) (y ∈ˢ x))

        -- The motive is over CODES, because rawRec inducts over codes, and it
        -- says: if this code is a check name, its own set satisfies the two
        -- clauses. The path argument is what lets a Child induction do the work
        -- of Bell's rank induction, and check-support-out is what feeds it.

        Motive : S → Type ℓ
        Motive n = (y : S) → n ≡ check y → Clauses y

        clauses-step : (n : S) → ((u : S) → Child u n → Motive u) → Motive n
        clauses-step n ih y eqn = (clause2 , clause3)
          where
            -- The inductive hypothesis, addressed by a MEMBER of y rather than
            -- by a child of the code. This is the step the architecture's trap 1
            -- makes necessary and check-child makes available.

            ihy : (z : S) → ⟨ z ∈ˢ y ⟩ → Clauses z
            ihy z hz =
              ih (check z)
                 (subst (λ w → Child (check z) w) (sym eqn) (check-child y z hz))
                 z refl

            -- Bell's first clause at y. Membership of an arbitrary check name
            -- in ǩ is decided by the members of y, each of which the inductive
            -- hypothesis already decides. This is the only place clause (i)'s
            -- least upper bound property is used with the bottom as the bound,
            -- and it is where two valuedness pays for itself.

            clause1 : (x : S) → Reflects (check x ∈ᴮ check y) (x ∈ˢ y)
            clause1 x with lem (x ∈ˢ y)
            ... | inl hx = inl (check-∈-top x y hx , hx)
            ... | inr nx = inr (≡⊥ (check x ∈ᴮ check y)
                                   (check-∈-lub y (check x) ⊥ᴮ bnd) , nx)
              where
                bnd : (z : S) → ⟨ z ∈ˢ y ⟩
                    → ⟨ (check x ≈ᴮ check z) ≤ᴮ ⊥ᴮ ⟩
                bnd z hz with fst (ihy z hz) x
                ... | inl (_ , hxz) =
                        Empty.rec (nx (subst (λ w → ⟨ w ∈ˢ y ⟩)
                                             (sym (≈→≡ hxz)) hz))
                ... | inr (p , _) = ≤⊥ (check x ≈ᴮ check z) p

            -- Bell's second clause at y. The interesting direction is the
            -- negative one: from a failure of ground equality, produce a member
            -- of exactly one of the two sets and drive the equality value to
            -- the bottom through the two lower bound properties of the atomic
            -- equality. Classical extensionality is what produces the member,
            -- and it is the only step of the file that needs LEM twice over.

            Disagree : S → S → Type ℓ
            Disagree x y' =
              Σ[ w ∈ S ] ((⟨ w ∈ˢ x ⟩ × (⟨ w ∈ˢ y' ⟩ → Empty.⊥))
                        ⊎ (⟨ w ∈ˢ y' ⟩ × (⟨ w ∈ˢ x ⟩ → Empty.⊥)))

            disagreement : (x y' : S) → (⟨ x ≈ˢ y' ⟩ → Empty.⊥)
                         → ∥ Disagree x y' ∥₁
            disagreement x y' nxy with lem (∥ Disagree x y' ∥₁ , PT.squash₁)
            ... | inl t = t
            ... | inr nt = Empty.rec (nxy (ext x y' agree))
              where
                agree : ⟨ ⋀ S (λ z → iff (z ∈ˢ x) (z ∈ˢ y')) ⟩
                agree z = (to , fro)
                  where
                    to : ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y' ⟩
                    to hzx with lem (z ∈ˢ y')
                    ... | inl h = h
                    ... | inr nh = Empty.rec (nt ∣ z , inl (hzx , nh) ∣₁)

                    fro : ⟨ z ∈ˢ y' ⟩ → ⟨ z ∈ˢ x ⟩
                    fro hzy with lem (z ∈ˢ x)
                    ... | inl h = h
                    ... | inr nh = Empty.rec (nt ∣ z , inr (hzy , nh) ∣₁)

            -- A member of the left set that is not in the right one. Bell's
            -- step reads the inductive hypothesis at the first conjunct of
            -- (1.16); here it is the left lower bound of the atomic equality,
            -- the weight rewritten to the top, and clause1 at that member.

            fromLeft : (x w : S) → ⟨ w ∈ˢ x ⟩ → (⟨ w ∈ˢ y ⟩ → Empty.⊥)
                     → ⟨ (check x ≈ᴮ check y) ≤ᴮ ⊥ᴮ ⟩
            fromLeft x w hwx nwy =
              ⊆ˢ-trans (≈ᴮ-lbˡ (check x) (check y) (check w)
                               (check-support x w hwx))
                       kill
              where
                botL : (check w ∈ᴮ check y) ≡ ⊥ᴮ
                botL with clause1 w
                ... | inl (_ , hwy) = Empty.rec (nwy hwy)
                ... | inr (p , _) = p

                plain : ⟨ (⊤ᴮ ⇒ᴮ (check w ∈ᴮ check y)) ≤ᴮ ⊥ᴮ ⟩
                plain = subst (λ z → ⟨ z ≤ᴮ ⊥ᴮ ⟩)
                              (sym (⇒ᴮ-⊤ˡ (check w ∈ᴮ check y)))
                              (≤⊥ (check w ∈ᴮ check y) botL)

                kill : ⟨ ((weightᴮ (check x) (check w))
                          ⇒ᴮ (check w ∈ᴮ check y)) ≤ᴮ ⊥ᴮ ⟩
                kill = subst (λ z → ⟨ (z ⇒ᴮ (check w ∈ᴮ check y)) ≤ᴮ ⊥ᴮ ⟩)
                             (sym (check-weight x w hwx)) plain

            -- A member of the right set that is not in the left one. Same shape
            -- through the right lower bound, and the decision comes from the
            -- inductive hypothesis' THIRD clause rather than from clause1,
            -- because the set it must decide membership in is arbitrary.

            fromRight : (x w : S) → ⟨ w ∈ˢ y ⟩ → (⟨ w ∈ˢ x ⟩ → Empty.⊥)
                      → ⟨ (check x ≈ᴮ check y) ≤ᴮ ⊥ᴮ ⟩
            fromRight x w hwy nwx =
              ⊆ˢ-trans (≈ᴮ-lbʳ (check x) (check y) (check w)
                               (check-support y w hwy))
                       kill
              where
                botR : (check w ∈ᴮ check x) ≡ ⊥ᴮ
                botR with snd (ihy w hwy) x
                ... | inl (_ , hwx) = Empty.rec (nwx hwx)
                ... | inr (p , _) = p

                plain : ⟨ (⊤ᴮ ⇒ᴮ (check w ∈ᴮ check x)) ≤ᴮ ⊥ᴮ ⟩
                plain = subst (λ z → ⟨ z ≤ᴮ ⊥ᴮ ⟩)
                              (sym (⇒ᴮ-⊤ˡ (check w ∈ᴮ check x)))
                              (≤⊥ (check w ∈ᴮ check x) botR)

                kill : ⟨ ((weightᴮ (check y) (check w))
                          ⇒ᴮ (check w ∈ᴮ check x)) ≤ᴮ ⊥ᴮ ⟩
                kill = subst (λ z → ⟨ (z ⇒ᴮ (check w ∈ᴮ check x)) ≤ᴮ ⊥ᴮ ⟩)
                             (sym (check-weight y w hwy)) plain

            clause2 : (x : S) → Reflects (check x ≈ᴮ check y) (x ≈ˢ y)
            clause2 x with lem (x ≈ˢ y)
            ... | inl hxy =
                    inl ( subst (λ w → (check x ≈ᴮ check w) ≡ ⊤ᴮ)
                                (≈→≡ hxy) (≈ᴮ-refl (check x))
                        , hxy )
            ... | inr nxy = inr (≡⊥ (check x ≈ᴮ check y) below , nxy)
              where
                below : ⟨ (check x ≈ᴮ check y) ≤ᴮ ⊥ᴮ ⟩
                below =
                  PT.rec (snd ((check x ≈ᴮ check y) ≤ᴮ ⊥ᴮ))
                    (λ { (w , inl (hwx , nwy)) → fromLeft x w hwx nwy
                       ; (w , inr (hwy , nwx)) → fromRight x w hwy nwx })
                    (disagreement x y nxy)

            -- Bell's third clause at y. It is clause (i)'s least upper bound
            -- again, but the family is now indexed by the members of an
            -- arbitrary set, and what decides each factor is clause2 at y read
            -- at exchanged endpoints. So symmetry of the atomic equality is
            -- load bearing here, and this is its fourth separate consumer after
            -- transitivity, Bell 1.16 and the subalgebra agreement
            -- (REPORT-C.md section C1, REPORT-D.md sections 5 and 13).

            clause3 : (x : S) → Reflects (check y ∈ᴮ check x) (y ∈ˢ x)
            clause3 x with lem (y ∈ˢ x)
            ... | inl h = inl (check-∈-top y x h , h)
            ... | inr nh = inr (≡⊥ (check y ∈ᴮ check x)
                                   (check-∈-lub x (check y) ⊥ᴮ bnd) , nh)
              where
                bnd : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ (check y ≈ᴮ check z) ≤ᴮ ⊥ᴮ ⟩
                bnd z hz with clause2 z
                ... | inl (_ , hzy) =
                        Empty.rec (nh (subst (λ w → ⟨ w ∈ˢ x ⟩)
                                             (≈→≡ hzy) hz))
                ... | inr (p , _) =
                        ≤⊥ (check y ≈ᴮ check z)
                           (sym (≈ᴮ-sym (check z) (check y)) ∙ p)

        clauses : (y : S) → Clauses y
        clauses y = rawRec Motive clauses-step (check y) y refl

        ------------------------------------------------------------------------
        -- Bell 1.23(ii), as shipped
        ------------------------------------------------------------------------

        -- The reflections first, because they carry more than the equivalences
        -- and every later induction wants the stronger form. Then the two
        -- equivalences the architecture prints, then two valuedness, which is
        -- the fact Bell notices right after Definition 1.22 when he writes
        -- ⟦x̌ ∈ y̌⟧ ∈ 2 (fulltext:2341-2343) and derives from Theorem 1.20.
        -- Here it comes out of the same induction and no subalgebra argument
        -- is needed.

        check-reflects-≈ : (a b : S) → Reflects (check a ≈ᴮ check b) (a ≈ˢ b)
        check-reflects-≈ a b = fst (clauses b) a

        check-reflects-∈ : (a b : S) → Reflects (check a ∈ᴮ check b) (a ∈ˢ b)
        check-reflects-∈ a b = snd (clauses a) b

        check-≈-⊤ : (a b : S) → ((check a ≈ᴮ check b) ≡ ⊤ᴮ) ≃ ⟨ a ≈ˢ b ⟩
        check-≈-⊤ a b =
          reflects→equiv (check a ≈ᴮ check b) (a ≈ˢ b) nontrivial
                         (check-reflects-≈ a b)

        check-∈-⊤ : (a b : S) → ((check a ∈ᴮ check b) ≡ ⊤ᴮ) ≃ ⟨ a ∈ˢ b ⟩
        check-∈-⊤ a b =
          reflects→equiv (check a ∈ᴮ check b) (a ∈ˢ b) nontrivial
                         (check-reflects-∈ a b)

        check-≈-two-valued : (a b : S)
                           → ((check a ≈ᴮ check b) ≡ ⊤ᴮ)
                           ⊎ ((check a ≈ᴮ check b) ≡ ⊥ᴮ)
        check-≈-two-valued a b =
          reflects-two-valued (check a ≈ᴮ check b) (a ≈ˢ b)
                              (check-reflects-≈ a b)

        check-∈-two-valued : (a b : S)
                           → ((check a ∈ᴮ check b) ≡ ⊤ᴮ)
                           ⊎ ((check a ∈ᴮ check b) ≡ ⊥ᴮ)
        check-∈-two-valued a b =
          reflects-two-valued (check a ∈ᴮ check b) (a ∈ˢ b)
                              (check-reflects-∈ a b)

        ------------------------------------------------------------------------
        -- Bell 1.23(iv): the uniqueness half, and the deferral of the other
        ------------------------------------------------------------------------

        -- Bell's (iv) says that for each u in the two valued universe there is a
        -- UNIQUE x with ⟦u = x̌⟧ = 1, and he proves uniqueness from (ii) and
        -- existence by an induction on x ∈ dom(u) that forms the set
        -- v = { y : ∃x ∈ dom(u)[u(x) = 1 ∧ ⟦x = y̌⟧ = 1] } (fulltext:2408-2425).
        --
        -- UNIQUENESS IS DELIVERED, at an arbitrary code u and with no two
        -- valuedness hypothesis on u at all, which is more than Bell states:
        -- his (iv) restricts to V(2) only because existence needs it.
        --
        -- EXISTENCE IS DEFERRED, and the reason is measured rather than
        -- stylistic. Bell forms v by Replacement over the class
        -- { y : ⟦x = y̌⟧ = 1 }, so the route needs (a) Collection, which is not
        -- in this track's ledger and which architecture section 1.3 measures
        -- cannot read a host function anyway, and (b) a GROUND FORMULA whose
        -- reading is the atomic value's being the top. That formula is exactly
        -- the atomic graph, and obstruction O1 says it does not exist at a
        -- general ground: K0's own record is that "the actual Boolean atomic
        -- step, its internal images, closed-name-domain adapters and
        -- general-ground portability remain open"
        -- (k0-bounded-table-recursion-2026-09.md:3), and Track E shipped the
        -- contract without a discharge at any ground (REPORT-E.md section 9).
        -- So the existence half is not a missing proof here, it is O1 wearing a
        -- different hat, and it belongs with whoever discharges AtomicGraph.
        --
        -- The statement is written out, so that a later track can read the
        -- obligation off this file rather than out of Bell. Nothing inhabits it
        -- and nothing here claims it does.

        StandardRepresentative : S → Type ℓ
        StandardRepresentative u = Σ[ x ∈ S ] ((u ≈ᴮ check x) ≡ ⊤ᴮ)

        standard-unique : (u a b : S)
                        → ((u ≈ᴮ check a) ≡ ⊤ᴮ) → ((u ≈ᴮ check b) ≡ ⊤ᴮ)
                        → ⟨ a ≈ˢ b ⟩
        standard-unique u a b pa pb =
          reflects-true (check a ≈ᴮ check b) (a ≈ˢ b) nontrivial
                        (check-reflects-≈ a b) top
          where
            left : (check a ≈ᴮ u) ≡ ⊤ᴮ
            left = sym (≈ᴮ-sym u (check a)) ∙ pa

            both : ⟨ ⊤ᴮ ≤ᴮ ((check a ≈ᴮ u) ⊓ᴮ (u ≈ᴮ check b)) ⟩
            both = ⊓-glb (check a ≈ᴮ u) (u ≈ᴮ check b) ⊤ᴮ
                         (⊤≤ (check a ≈ᴮ u) left) (⊤≤ (u ≈ᴮ check b) pb)

            top : (check a ≈ᴮ check b) ≡ ⊤ᴮ
            top = ≡⊤ (check a ≈ᴮ check b)
                     (⊆ˢ-trans both (≈ᴮ-trans (check a) u (check b)))

        -- The existence half as a type, uninhabited here, on the pattern Track I
        -- uses for the fullness record.

        StandardExistence : Type ℓ
        StandardExistence = (u : S) → ⟨ IsName u ⟩ → ∥ StandardRepresentative u ∥₁

        ------------------------------------------------------------------------
        -- Bell 1.23(v), the restricted half
        ------------------------------------------------------------------------

        -- Bell's (v) has two halves and only one of them is K4's. The first
        -- half, that EVERY formula transfers, is about the two element algebra
        -- V(2) and is proved by an induction whose existential step needs (iv)
        -- to replace an arbitrary two valued name by a check name
        -- (fulltext:2426-2440). The existence half of (iv) is deferred above,
        -- so that half is not claimed here and the architecture does not ask
        -- for it: section 1.9 prints check-Δ₀ with a Δ₀ argument on its face and
        -- names the unrestricted half as not K4's.
        --
        -- The restricted half is the one below. Bell derives it from the first
        -- half plus Corollary 1.21; this file does not, and the difference is
        -- worth stating because it is a simplification and not a gap. A
        -- restricted formula's quantifiers are bounded, and a bounded
        -- quantifier over a check name ranges, up to Boolean equality, over the
        -- check names of the members of the bound. That is Bell 1.23(i), which
        -- is proved above, so the induction closes at the two element algebra's
        -- own argument WITHOUT the subalgebra comparison. Track D's follow up
        -- K4/SubalgebraAgreement.agda proves 1.20 and the clause list of 1.21
        -- independently, and nothing here consumes it.
        --
        -- THE HYPOTHESES, and two of them are not on this track's permitted
        -- list. Track F's compiler enters as its value function and eleven of
        -- its InterpLaws fields, flat, exactly as the coordinator's instruction
        -- directs: an unfinished parallel track becomes an explicit telescope
        -- and nobody waits. Track G's substitution lemma at one variable enters
        -- as val-subst, whose type is Track G's own subst-head
        -- (K4/Substitution.agda:745-747) character for character and in its
        -- argument order, so the coordinator's wiring is a projection and not
        -- an adapter. THAT DEPENDENCY IS REAL AND THE ARCHITECTURE'S TRACK H
        -- BRIEF DOES NOT LIST IT. It is needed at exactly two steps,
        -- the forward direction of the bounded existential and the backward
        -- direction of the bounded universal, and in both the reason is the
        -- same: the quantifier's least upper bound property quantifies over
        -- EVERY name, while the induction hypothesis knows only about check
        -- names, and the only thing that carries a value from an arbitrary name
        -- to a check name it is Boolean-equal to is Bell 1.17(vii).
        --
        -- Four of Track F's fields are NOT taken and their absence is the scope
        -- limit: law-∃-ub, law-∃-lub, law-∀-lb, law-∀-glb, the UNBOUNDED
        -- quantifier clauses. A Δ₀ witness has no constructor for an unbounded
        -- quantifier, so those nodes are unreachable here, and that is exactly
        -- the sense in which this is the restricted half and not the whole of
        -- Bell's (v).

        module Delta0
          (value : ∀ {k} → Src k → Vec Name k → Pt B)
          (law-∈ : ∀ {k} (i j : Fin k) (ν : Vec Name k)
                 → value (var i ∈̇ var j) ν
                 ≡ (fst (lookup i ν) ∈ᴮ fst (lookup j ν)))
          (law-≐ : ∀ {k} (i j : Fin k) (ν : Vec Name k)
                 → value (var i ≐ var j) ν
                 ≡ (fst (lookup i ν) ≈ᴮ fst (lookup j ν)))
          (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Vec Name k)
                 → value (φ ∧̇ ψ) ν ≡ ((value φ ν) ⊓ᴮ (value ψ ν)))
          (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Vec Name k)
                 → value (φ ∨̇ ψ) ν ≡ ((value φ ν) ⊔ᴮ (value ψ ν)))
          (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Vec Name k)
                 → value (φ ⇒̇ ψ) ν ≡ ((value φ ν) ⇒ᴮ (value ψ ν)))
          (law-⊥ : ∀ {k} (ν : Vec Name k) → value {k} ⊥̇ ν ≡ ⊥ᴮ)
          (law-∃∈-ub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Vec Name k)
                       (σ : Name)
                     → ⟨ ((fst σ ∈ᴮ fst (lookup i ν)) ⊓ᴮ (value φ (σ ∷ ν)))
                         ≤ᴮ value (∃̇∈ (var i) φ) ν ⟩)
          (law-∃∈-lub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Vec Name k)
                        (c : Pt B)
                      → ((σ : Name)
                         → ⟨ ((fst σ ∈ᴮ fst (lookup i ν)) ⊓ᴮ (value φ (σ ∷ ν)))
                             ≤ᴮ c ⟩)
                      → ⟨ value (∃̇∈ (var i) φ) ν ≤ᴮ c ⟩)
          (law-∀∈-lb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Vec Name k)
                       (σ : Name)
                     → ⟨ value (∀̇∈ (var i) φ) ν
                         ≤ᴮ ((fst σ ∈ᴮ fst (lookup i ν)) ⇒ᴮ (value φ (σ ∷ ν))) ⟩)
          (law-∀∈-glb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Vec Name k)
                        (c : Pt B)
                      → ((σ : Name)
                         → ⟨ c ≤ᴮ ((fst σ ∈ᴮ fst (lookup i ν))
                                    ⇒ᴮ (value φ (σ ∷ ν))) ⟩)
                      → ⟨ c ≤ᴮ value (∀̇∈ (var i) φ) ν ⟩)
          (val-subst : ∀ {k} (φ : Src (suc k)) (ν : Vec Name k) (σ τ : Name)
                     → ⟨ (((fst σ) ≈ᴮ (fst τ)) ⊓ᴮ (value φ (σ ∷ ν)))
                         ≤ᴮ value φ (τ ∷ ν) ⟩)
          where

          -- THE INDUCTION. Its conclusion is the reflection and not Bell's
          -- biconditional, for the reason module Core's comment on Reflects
          -- gives: the disjunction, the implication and the bounded existential
          -- all need to know that a value that is not the top IS the bottom,
          -- and a biconditional does not say so.
          --
          -- Reading the cases. The two atomic ones are clause (ii), transported
          -- along the compiler's law and along lookup-check. The four
          -- propositional ones are module Core's connective calculus, which is
          -- pure Boolean algebra and mentions no name. The two unbounded
          -- quantifier nodes are unreachable, by absurd pattern on the Δ₀
          -- witness. The two bounded ones are the mathematics, and each splits
          -- on excluded middle at the ground proposition and then runs the
          -- quantifier's universal property in one direction and Bell 1.23(i)
          -- with the substitution lemma in the other.

          reflect : ∀ {k} (φ : Src k) → Δ₀ φ → (γ : S ^ k)
                  → Reflects (value φ (checkEnv γ)) (γ ⊨ embed φ)

          reflect (var i ∈̇ var j) δ-∈ γ =
            subst (λ u → Reflects u (lookup i γ ∈ˢ lookup j γ)) (sym atomic)
                  (check-reflects-∈ (lookup i γ) (lookup j γ))
            where
              atomic : value (var i ∈̇ var j) (checkEnv γ)
                     ≡ (check (lookup i γ) ∈ᴮ check (lookup j γ))
              atomic = law-∈ i j (checkEnv γ)
                     ∙ cong (λ w → w ∈ᴮ fst (lookup j (checkEnv γ)))
                            (lookup-check i γ)
                     ∙ cong (λ w → check (lookup i γ) ∈ᴮ w) (lookup-check j γ)
          reflect (var i ∈̇ con e) δ-∈ γ = Empty.rec* e
          reflect (con e ∈̇ u)     δ-∈ γ = Empty.rec* e

          reflect (var i ≐ var j) δ-≐ γ =
            subst (λ u → Reflects u (lookup i γ ≈ˢ lookup j γ)) (sym atomic)
                  (check-reflects-≈ (lookup i γ) (lookup j γ))
            where
              atomic : value (var i ≐ var j) (checkEnv γ)
                     ≡ (check (lookup i γ) ≈ᴮ check (lookup j γ))
              atomic = law-≐ i j (checkEnv γ)
                     ∙ cong (λ w → w ≈ᴮ fst (lookup j (checkEnv γ)))
                            (lookup-check i γ)
                     ∙ cong (λ w → check (lookup i γ) ≈ᴮ w) (lookup-check j γ)
          reflect (var i ≐ con e) δ-≐ γ = Empty.rec* e
          reflect (con e ≐ u)     δ-≐ γ = Empty.rec* e

          reflect (φ ∧̇ ψ) (δ-∧ dφ dψ) γ =
            reflects-subst ((value φ (checkEnv γ)) ⊓ᴮ (value ψ (checkEnv γ)))
                           (value (φ ∧̇ ψ) (checkEnv γ))
                           ((γ ⊨ embed φ) ⊓ (γ ⊨ embed ψ))
                           (sym (law-∧ φ ψ (checkEnv γ)))
              (reflects-⊓ (value φ (checkEnv γ)) (value ψ (checkEnv γ))
                          (γ ⊨ embed φ) (γ ⊨ embed ψ)
                          (reflect φ dφ γ) (reflect ψ dψ γ))

          reflect (φ ∨̇ ψ) (δ-∨ dφ dψ) γ =
            reflects-subst ((value φ (checkEnv γ)) ⊔ᴮ (value ψ (checkEnv γ)))
                           (value (φ ∨̇ ψ) (checkEnv γ))
                           ((γ ⊨ embed φ) ⊔ (γ ⊨ embed ψ))
                           (sym (law-∨ φ ψ (checkEnv γ)))
              (reflects-⊔ (value φ (checkEnv γ)) (value ψ (checkEnv γ))
                          (γ ⊨ embed φ) (γ ⊨ embed ψ)
                          (reflect φ dφ γ) (reflect ψ dψ γ))

          reflect (φ ⇒̇ ψ) (δ-⇒ dφ dψ) γ =
            reflects-subst ((value φ (checkEnv γ)) ⇒ᴮ (value ψ (checkEnv γ)))
                           (value (φ ⇒̇ ψ) (checkEnv γ))
                           ((γ ⊨ embed φ) ⇒ (γ ⊨ embed ψ))
                           (sym (law-⇒ φ ψ (checkEnv γ)))
              (reflects-⇒ (value φ (checkEnv γ)) (value ψ (checkEnv γ))
                          (γ ⊨ embed φ) (γ ⊨ embed ψ)
                          (reflect φ dφ γ) (reflect ψ dψ γ))

          reflect ⊥̇ δ-⊥ γ =
            reflects-subst ⊥ᴮ (value ⊥̇ (checkEnv γ)) ⊥
                           (sym (law-⊥ (checkEnv γ))) reflects-⊥

          reflect (∃̇ φ) () γ
          reflect (∀̇ φ) () γ

          reflect {k} (∃̇∈ (var i) ψ) (δ-∃∈ d) γ = go
            where
              A : S
              A = lookup i γ

              ν : Vec Name k
              ν = checkEnv γ

              Witness : Type ℓ
              Witness = Σ[ x ∈ S ] (⟨ x ∈ˢ A ⟩ × ⟨ (x ∷ γ) ⊨ embed ψ ⟩)

              hit : Witness → value (∃̇∈ (var i) ψ) ν ≡ ⊤ᴮ
              hit (x , hx , hψ) =
                ≡⊤ (value (∃̇∈ (var i) ψ) ν)
                   (⊆ˢ-trans raise (law-∃∈-ub i ψ ν (checkName x)))
                where
                  memtop : ((check x) ∈ᴮ fst (lookup i ν)) ≡ ⊤ᴮ
                  memtop = cong (λ w → (check x) ∈ᴮ w) (lookup-check i γ)
                         ∙ check-∈-top x A hx

                  valtop : value ψ (checkName x ∷ ν) ≡ ⊤ᴮ
                  valtop = reflects-holds (value ψ (checkName x ∷ ν))
                             ((x ∷ γ) ⊨ embed ψ) (reflect ψ d (x ∷ γ)) hψ

                  raise : ⟨ ⊤ᴮ ≤ᴮ (((check x) ∈ᴮ fst (lookup i ν))
                                    ⊓ᴮ (value ψ (checkName x ∷ ν))) ⟩
                  raise = ⊓-glb ((check x) ∈ᴮ fst (lookup i ν))
                                (value ψ (checkName x ∷ ν)) ⊤ᴮ
                                (⊤≤ ((check x) ∈ᴮ fst (lookup i ν)) memtop)
                                (⊤≤ (value ψ (checkName x ∷ ν)) valtop)

              go : Reflects (value (∃̇∈ (var i) ψ) ν)
                            (γ ⊨ embed (∃̇∈ (var i) ψ))
              go with lem (γ ⊨ embed (∃̇∈ (var i) ψ))
              ... | inl hP =
                      inl ( PT.rec (isSetPt B (value (∃̇∈ (var i) ψ) ν) ⊤ᴮ)
                                   hit hP
                          , hP )
              ... | inr nP =
                      inr ( ≡⊥ (value (∃̇∈ (var i) ψ) ν)
                               (law-∃∈-lub i ψ ν ⊥ᴮ step)
                          , nP )
                where
                  step : (σ : Name)
                       → ⟨ (((fst σ) ∈ᴮ fst (lookup i ν))
                            ⊓ᴮ (value ψ (σ ∷ ν))) ≤ᴮ ⊥ᴮ ⟩
                  step σ =
                    subst (λ w → ⟨ (((fst σ) ∈ᴮ w) ⊓ᴮ (value ψ (σ ∷ ν)))
                                   ≤ᴮ ⊥ᴮ ⟩)
                          (sym (lookup-check i γ)) core
                    where
                      miss : (y : S) → ⟨ y ∈ˢ A ⟩
                           → value ψ (checkName y ∷ ν) ≡ ⊥ᴮ
                      miss y hy with reflect ψ d (y ∷ γ)
                      ... | inl (_ , hψ) = Empty.rec (nP ∣ y , hy , hψ ∣₁)
                      ... | inr (p , _)  = p

                      inner : (y : S) → ⟨ y ∈ˢ A ⟩
                            → ⟨ (((fst σ) ≈ᴮ (check y)) ⊓ᴮ (value ψ (σ ∷ ν)))
                                ≤ᴮ ⊥ᴮ ⟩
                      inner y hy =
                        ⊆ˢ-trans (val-subst ψ ν σ (checkName y))
                                 (≤⊥ (value ψ (checkName y ∷ ν)) (miss y hy))

                      curried : ⟨ ((fst σ) ∈ᴮ (check A))
                                  ≤ᴮ ((value ψ (σ ∷ ν)) ⇒ᴮ ⊥ᴮ) ⟩
                      curried =
                        check-∈-lub A (fst σ) ((value ψ (σ ∷ ν)) ⇒ᴮ ⊥ᴮ)
                          (λ y hy → ⇒ᴮ-curry ((fst σ) ≈ᴮ (check y))
                                             (value ψ (σ ∷ ν)) ⊥ᴮ
                                             (inner y hy))

                      core : ⟨ (((fst σ) ∈ᴮ (check A)) ⊓ᴮ (value ψ (σ ∷ ν)))
                               ≤ᴮ ⊥ᴮ ⟩
                      core = ⇒ᴮ-uncurry ((fst σ) ∈ᴮ (check A))
                                        (value ψ (σ ∷ ν)) ⊥ᴮ curried
          reflect (∃̇∈ (con e) ψ) (δ-∃∈ d) γ = Empty.rec* e

          reflect {k} (∀̇∈ (var i) ψ) (δ-∀∈ d) γ = go
            where
              A : S
              A = lookup i γ

              ν : Vec Name k
              ν = checkEnv γ

              Counter : Type ℓ
              Counter = Σ[ y ∈ S ] (⟨ y ∈ˢ A ⟩
                                  × (⟨ (y ∷ γ) ⊨ embed ψ ⟩ → Empty.⊥))

              fail : Counter → value (∀̇∈ (var i) ψ) ν ≡ ⊥ᴮ
              fail (y , hy , nψ) =
                ≡⊥ (value (∀̇∈ (var i) ψ) ν)
                   (⊆ˢ-trans (law-∀∈-lb i ψ ν (checkName y)) kill)
                where
                  bot : value ψ (checkName y ∷ ν) ≡ ⊥ᴮ
                  bot with reflect ψ d (y ∷ γ)
                  ... | inl (_ , h) = Empty.rec (nψ h)
                  ... | inr (p , _) = p

                  memtop : ((check y) ∈ᴮ fst (lookup i ν)) ≡ ⊤ᴮ
                  memtop = cong (λ w → (check y) ∈ᴮ w) (lookup-check i γ)
                         ∙ check-∈-top y A hy

                  plain : ⟨ (⊤ᴮ ⇒ᴮ (value ψ (checkName y ∷ ν))) ≤ᴮ ⊥ᴮ ⟩
                  plain = subst (λ z → ⟨ z ≤ᴮ ⊥ᴮ ⟩)
                                (sym (⇒ᴮ-⊤ˡ (value ψ (checkName y ∷ ν))))
                                (≤⊥ (value ψ (checkName y ∷ ν)) bot)

                  kill : ⟨ ((((check y) ∈ᴮ fst (lookup i ν)))
                            ⇒ᴮ (value ψ (checkName y ∷ ν))) ≤ᴮ ⊥ᴮ ⟩
                  kill = subst (λ z → ⟨ (z ⇒ᴮ (value ψ (checkName y ∷ ν)))
                                        ≤ᴮ ⊥ᴮ ⟩)
                               (sym memtop) plain

              go : Reflects (value (∀̇∈ (var i) ψ) ν)
                            (γ ⊨ embed (∀̇∈ (var i) ψ))
              go with lem (γ ⊨ embed (∀̇∈ (var i) ψ))
              ... | inl hQ =
                      inl ( ≡⊤ (value (∀̇∈ (var i) ψ) ν)
                               (law-∀∈-glb i ψ ν ⊤ᴮ step)
                          , hQ )
                where
                  step : (σ : Name)
                       → ⟨ ⊤ᴮ ≤ᴮ (((fst σ) ∈ᴮ fst (lookup i ν))
                                   ⇒ᴮ (value ψ (σ ∷ ν))) ⟩
                  step σ =
                    subst (λ w → ⟨ ⊤ᴮ ≤ᴮ (((fst σ) ∈ᴮ w)
                                           ⇒ᴮ (value ψ (σ ∷ ν))) ⟩)
                          (sym (lookup-check i γ))
                          (≤→⊤⇒ ((fst σ) ∈ᴮ (check A)) (value ψ (σ ∷ ν)) below)
                    where
                      hits : (y : S) → ⟨ y ∈ˢ A ⟩
                           → value ψ (checkName y ∷ ν) ≡ ⊤ᴮ
                      hits y hy =
                        reflects-holds (value ψ (checkName y ∷ ν))
                          ((y ∷ γ) ⊨ embed ψ) (reflect ψ d (y ∷ γ)) (hQ y hy)

                      inner : (y : S) → ⟨ y ∈ˢ A ⟩
                            → ⟨ ((fst σ) ≈ᴮ (check y)) ≤ᴮ (value ψ (σ ∷ ν)) ⟩
                      inner y hy =
                        ⊆ˢ-trans widen (val-subst ψ ν (checkName y) σ)
                        where
                          swap : ⟨ ((fst σ) ≈ᴮ (check y))
                                   ≤ᴮ ((check y) ≈ᴮ (fst σ)) ⟩
                          swap = subst (λ z → ⟨ ((fst σ) ≈ᴮ (check y)) ≤ᴮ z ⟩)
                                       (≈ᴮ-sym (fst σ) (check y))
                                       (≤ᴮ-refl ((fst σ) ≈ᴮ (check y)))

                          up : ⟨ ((fst σ) ≈ᴮ (check y))
                                 ≤ᴮ (value ψ (checkName y ∷ ν)) ⟩
                          up = subst (λ z → ⟨ ((fst σ) ≈ᴮ (check y)) ≤ᴮ z ⟩)
                                     (sym (hits y hy))
                                     (⊤-greatest ((fst σ) ≈ᴮ (check y)))

                          widen : ⟨ ((fst σ) ≈ᴮ (check y))
                                    ≤ᴮ (((check y) ≈ᴮ (fst σ))
                                        ⊓ᴮ (value ψ (checkName y ∷ ν))) ⟩
                          widen = ⊓-glb ((check y) ≈ᴮ (fst σ))
                                        (value ψ (checkName y ∷ ν))
                                        ((fst σ) ≈ᴮ (check y)) swap up

                      below : ⟨ ((fst σ) ∈ᴮ (check A))
                                ≤ᴮ (value ψ (σ ∷ ν)) ⟩
                      below = check-∈-lub A (fst σ) (value ψ (σ ∷ ν)) inner
              ... | inr nQ =
                      inr ( PT.rec (isSetPt B (value (∀̇∈ (var i) ψ) ν) ⊥ᴮ)
                                   fail
                                   (witness-fail A (λ x → (x ∷ γ) ⊨ embed ψ) nQ)
                          , nQ )
          reflect (∀̇∈ (con e) ψ) (δ-∀∈ d) γ = Empty.rec* e

          ----------------------------------------------------------------------
          -- Bell 1.23(v) for restricted formulas, as the architecture prints it
          ----------------------------------------------------------------------

          check-Δ₀ : ∀ {k} (φ : Src k) → Δ₀ φ → (γ : S ^ k)
                   → (value φ (checkEnv γ) ≡ ⊤ᴮ) ≃ ⟨ γ ⊨ embed φ ⟩
          check-Δ₀ φ d γ =
            reflects→equiv (value φ (checkEnv γ)) (γ ⊨ embed φ) nontrivial
                           (reflect φ d γ)

          -- And the fact the equivalence hides, which is what a later track
          -- that wants to compose formulas will actually need: at a check
          -- environment a restricted formula's value is two valued. Bell states
          -- this only for the atomic case and derives it from Theorem 1.20
          -- (fulltext:2341-2343); here it is the induction's own output and no
          -- subalgebra comparison is used.

          check-Δ₀-two-valued : ∀ {k} (φ : Src k) → Δ₀ φ → (γ : S ^ k)
                              → (value φ (checkEnv γ) ≡ ⊤ᴮ)
                              ⊎ (value φ (checkEnv γ) ≡ ⊥ᴮ)
          check-Δ₀-two-valued φ d γ =
            reflects-two-valued (value φ (checkEnv γ)) (γ ⊨ embed φ)
                                (reflect φ d γ)

      --------------------------------------------------------------------------
      -- The zero weight name, and the completed refutation
      --------------------------------------------------------------------------

      -- K3 proved the raw half of the separation: a name with one entry at any
      -- weight has a member, the empty name has none, so their CODES differ
      -- (zero-distinct, NameKernel.agda:555-558). K3 assigned the Boolean half
      -- to K4 by name, and this is it: at the zero weight the two names have
      -- the same value, so raw distinctness and Boolean equality genuinely come
      -- apart. Without this the reader has no evidence that the value layer
      -- says anything the code layer does not.
      --
      -- Stated at a RAW code s where architecture section 1.9 prints a Name σ
      -- and a membership proof h for the zero weight. Both are discardable:
      -- fst (oneEntryName σ z h) is singleOf (entry (fst σ) z) by definition
      -- (NameKernel.agda:502-508), so the raw form covers the printed one, and
      -- the proof h is used by oneEntryName only to build the name's validity,
      -- which no statement below reads.

      module Zero
        (singleOf        : S → S)
        (singleOf-spec   : (a z : S) → ⟨ z ∈ˢ singleOf a ⟩ → z ≡ a)
        (singleOf-member : (a : S) → ⟨ a ∈ˢ singleOf a ⟩)
        (∅ᴺ              : S)
        (∅ᴺ-spec         : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
        where

        oneEntryZero : S → S
        oneEntryZero s = singleOf (entry s (fst ⊥ᴮ))

        -- The empty name has an empty support, hence a bottom membership value
        -- at every code. Track D's ∈ᴮ-empty is stated at exactly this
        -- hypothesis and deliberately mentions no ∅ᴺ (REPORT-D.md, D3).

        empty-support : (x : S) → ⟨ x ∈ˢ support ∅ᴺ ⟩ → ⟨ ⊥ ⟩
        empty-support x h =
          PT.rec (snd ⊥)
            (λ { (b , hb) → subst ⟨_⟩ (∅ᴺ-spec (entry x b)) hb })
            (child-elim x ∅ᴺ (support-out ∅ᴺ x h))

        ∈ᴮ-∅ᴺ : (m : S) → (m ∈ᴮ ∅ᴺ) ≡ ⊥ᴮ
        ∈ᴮ-∅ᴺ m = ∈ᴮ-empty m ∅ᴺ empty-support

        -- The one entry name's support is a singleton, but nothing below needs
        -- to know that: what is needed is that EVERY weight it carries is the
        -- bottom, and the least upper bound characterisation of the weight
        -- gives that with no support computation at all.

        zero-weight : (s x : S) → weightᴮ (oneEntryZero s) x ≡ ⊥ᴮ
        zero-weight s x =
          ≡⊥ (weightᴮ (oneEntryZero s) x)
             (weight-least (oneEntryZero s) x ⊥ᴮ bnd)
          where
            bnd : (b : Pt B) → ⟨ entry x (fst b) ∈ˢ oneEntryZero s ⟩
                → ⟨ b ≤ᴮ ⊥ᴮ ⟩
            bnd b hb =
              subst (λ z → ⟨ z ⊆ˢ fst ⊥ᴮ ⟩) (sym same) (≤ᴮ-refl ⊥ᴮ)
              where
                same : fst b ≡ fst ⊥ᴮ
                same = snd (entry-inj
                             (singleOf-spec (entry s (fst ⊥ᴮ))
                                            (entry x (fst b)) hb))

        ∈ᴮ-oneEntryZero : (m s : S) → (m ∈ᴮ oneEntryZero s) ≡ ⊥ᴮ
        ∈ᴮ-oneEntryZero m s =
          ≡⊥ (m ∈ᴮ oneEntryZero s) (∈ᴮ-lub m (oneEntryZero s) ⊥ᴮ step)
          where
            step : (x : S) → ⟨ x ∈ˢ support (oneEntryZero s) ⟩
                 → ⟨ ((weightᴮ (oneEntryZero s) x) ⊓ᴮ (m ≈ᴮ x)) ≤ᴮ ⊥ᴮ ⟩
            step x _ =
              ⊆ˢ-trans (⊓-lb₁ (weightᴮ (oneEntryZero s) x) (m ≈ᴮ x))
                       (≤⊥ (weightᴮ (oneEntryZero s) x) (zero-weight s x))

        zero-weight-boolean : (s : S) → (oneEntryZero s ≈ᴮ ∅ᴺ) ≡ ⊤ᴮ
        zero-weight-boolean s =
          ext-≈ᴮ (oneEntryZero s) ∅ᴺ
            (λ r → ∈ᴮ-oneEntryZero r s ∙ sym (∈ᴮ-∅ᴺ r))

        -- And the refutation of the architecture's unconditional clause (ii),
        -- driven all the way to absurdity now that a memberless set is in the
        -- ledger. This is the exact analogue of Track A's
        -- arch-inf-residual-degenerate and it is checked, not asserted.

        arch-check-∈-⊤-refuted : ⊤ᴮ ≡ ⊥ᴮ → ArchCheck∈⊤ → ⟨ ⊥ ⟩
        arch-check-∈-⊤-refuted deg f =
          subst ⟨_⟩ (∅ᴺ-spec ∅ᴺ) (arch-check-∈-⊤-collapses deg f ∅ᴺ ∅ᴺ)
