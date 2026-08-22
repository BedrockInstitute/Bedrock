{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.518]  The hypothesis that links the formula's order to the rank's.
--
-- The obligation is `ord-reads-Q`, section 2.  Section 1 is W3, the
-- WITNESS: the brief ordered it written first and typechecked alone,
-- because a hypothesis nothing satisfies is what [LJ-1.507] delivered.
-- That slice is kept at agents/tasks/LJ-1-518/runs/w3-slice.agda.txt.
--
-- THE LEVEL IN THE BRIEF CANNOT BE MET AND THE REASON IS STRUCTURAL.  The
-- brief writes `ord-reads-Q : (Q a : S) → IsOrd (fst a) → Type ℓ`.  The
-- hypothesis must constrain `Q` at ARBITRARY elements of the model and not
-- only at members of `a`, because `fnAt`'s domain clause is an unbounded
-- `∀̇` (agents/tasks/LJ-1-497/Probe497.agda:228).  `S` is
-- `Σ[ x ∈ V ℓ ] ⟨ isL x ⟩` and `V ℓ : Type (ℓ-suc ℓ)`, so a statement that
-- quantifies over `S` is at least `Type (ℓ-suc ℓ)`.  Section 1.0 records
-- what a `Type ℓ` statement CAN say and why it is not this one.
--
-- Rebuilds [LJ-1.515]'s `OrdSWO∈ₛ` in section 3.  Does not import a probe.
-- The adequacy is NOT built: AD12 gives this brief one obligation.
-- `rankFo` is NOT touched and `swo-rank′` is NOT changed.
-- Nothing lands in src/.  Does not postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-518.Probe518 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓ} using ( SWO; Tri; lt; eq; gt )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate; prʟ; prʟ-fst )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Foundations.HLevels using ( isPropΣ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open hPropStructure 𝒮ᵥ using ( _∈ᵗ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)

  -- membership transported along both components at once.  `subst2` is
  -- not in the Prelude's export list, so this is it written out.
  ∈-cong : {u u' v v' : V ℓ} → u ≡ u' → v ≡ v'
         → ⟨ u ∈ v ⟩ → ⟨ u' ∈ v' ⟩
  ∈-cong {u} {u'} {v} {v'} p q h =
    subst (λ w → ⟨ w ∈ v' ⟩) p (subst (λ w → ⟨ u ∈ w ⟩) q h)

-- =====================================================================
-- 1.  THE SITE.  `a` is a set of the model, `oa` says it is an ordinal,
--     and `_≺ₛ_` is the ∈-order on its members: [LJ-1.515]'s relation,
--     copied from agents/tasks/LJ-1-515/Probe515.agda:239-240.  Section 3
--     rebuilds the SWO around it and proves this IS that relation.
--
--     `ix` is the index of a member.  It exists because `fiber` is the
--     UNTRUNCATED fiber of the presentation's embedding
--     (src/V/Presentation.lagda.md:34), so a membership names an index
--     with no choice and no truncation to eliminate.
-- =====================================================================

module Site (a : S) (oa : IsOrd (fst a)) where

  α : V ℓ
  α = fst a

  _≺ₛ_ : ⟪ α ⟫ → ⟪ α ⟫ → Type ℓ
  m ≺ₛ n = ⟨ ⟪ α ⟫↪ m ∈ₛ ⟪ α ⟫↪ n ⟩

  -- `x` is EXPLICIT, and that is forced.  `fst x` is not a pattern, so an
  -- implicit `x` never solves.  Measured: runs/w3-implicit-meta.out line 5,
  -- "when checking that the expression x has type ⟨ fst _x_105 ∈ α ⟩".
  ix : (x : S) → ⟨ fst x ∈ α ⟩ → ⟪ α ⟫
  ix x h = fiber α h .fst

  ix-val : (x : S) (h : ⟨ fst x ∈ α ⟩) → ⟪ α ⟫↪ (ix x h) ≡ fst x
  ix-val x h = fiber α h .snd

  -- a member of `a`, as an element of the model.  `isL` is transitive
  -- (src/L/Constructible.lagda.md:379), so a member of a constructible
  -- set is constructible and no stage arithmetic is needed here.
  memS : ⟪ α ⟫ → S
  memS m = ⟪ α ⟫↪ m , isL-trans {x = α} {y = ⟪ α ⟫↪ m} (member α m) (snd a)

  memS-mem : (k : ⟪ α ⟫) → ⟨ fst (memS k) ∈ α ⟩
  memS-mem k = member α k

  -- and the index of a member read back is the index it came from
  memS-ix : (k : ⟪ α ⟫) → ix (memS k) (memS-mem k) ≡ k
  memS-ix k = ↪-inj {a = α} (ix-val (memS k) (memS-mem k))

  -- =====================================================================
  -- 1.0  D-10, IN AGDA.  `Q` is a SET and `_≺ₛ_` is a RELATION, and the
  --      tree turns one into the other through exactly one term: `appAt`.
  --
  --        appAt f x y = ∃̇∈ (var f) (prAtL zero (suc x) (suc y))
  --                                    (src/L/Coding/Model.lagda.md:161)
  --        appAt-adequate f x y γ
  --          : (γ ⊨ appAt f x y)
  --          ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ))
  --                                    (src/L/Coding/Model.lagda.md:163-165)
  --
  --      So `appAt Q x m` IS `pr x m ∈ Q`, at the Kuratowski pair of
  --      `V.Coding` (src/V/Coding.lagda.md, `pr`), and NOTHING ELSE.  The
  --      encoding is not chosen here: it is the one `rankFo` already reads
  --      and the one `pr-inj` already inverts.  `PairOf` below is that
  --      reading written once, and every clause of this file is stated
  --      against it.
  -- =====================================================================

  PairOf : (Q x m : S) → Type (ℓ-suc ℓ)
  PairOf Q x m = ⟨ pr (fst x) (fst m) ∈ fst Q ⟩

  -- and this is the same statement as the formula's, by that lemma alone.
  pairOf-appAt : ∀ {n} (f x y : Fin n) (γ : S ^ n)
               → (γ ⊨ appAt f x y)
               ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ))
  pairOf-appAt = appAt-adequate

  -- =====================================================================
  -- 1.1  THE HYPOTHESIS.  Two directions, and the SECOND ARGUMENT of each
  --      is the whole point: the pair-membership of `Q` is decided by the
  --      ∈-order `_≺ₛ_`, at the indices of the two components.
  --
  --      `ReadsOut` is the direction the adequacy spends.  It says three
  --      things at once and the first two are not decoration: a pair in
  --      `Q` has BOTH components in `a`.  Without them the domain clause
  --      of `fnAt` reads the Q-predecessors of `m` over the whole model
  --      and the rank reads them over `⟪ α ⟫` alone.
  -- =====================================================================

  ReadsOut : (Q : S) → Type (ℓ-suc ℓ)
  ReadsOut Q =
      (x m : S) → PairOf Q x m
    → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ] Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma)

  ReadsIn : (Q : S) → Type (ℓ-suc ℓ)
  ReadsIn Q =
      (x m : S) (xa : ⟨ fst x ∈ α ⟩) (ma : ⟨ fst m ∈ α ⟩)
    → ix x xa ≺ₛ ix m ma → PairOf Q x m

  Reads : (Q : S) → Type (ℓ-suc ℓ)
  Reads Q = ReadsOut Q × ReadsIn Q

  isPropReadsOut : (Q x m : S)
    → isProp (Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ]
              Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma))
  isPropReadsOut Q x m =
    isPropΣ (snd (fst x ∈ α)) (λ xa →
    isPropΣ (snd (fst m ∈ α)) (λ ma →
      snd (⟪ α ⟫↪ (ix x xa) ∈ₛ ⟪ α ⟫↪ (ix m ma))))

-- =====================================================================
-- 2.  THE OBLIGATION.
--
--     THE LEVEL IS `ℓ-suc ℓ` AND NOT THE BRIEF'S `ℓ`.  See the head of
--     this file.  The brief's own W3 type names `S` twice, so the brief's
--     two lines disagree with each other and this is the one that can be
--     written.
-- =====================================================================

ord-reads-Q : (Q a : S) → IsOrd (fst a) → Type (ℓ-suc ℓ)
ord-reads-Q Q a oa = Site.Reads a oa Q

-- =====================================================================
-- 3.  W3.  THE WITNESS.
--
--     The brief ordered this written FIRST and typechecked ALONE, because
--     `[LJ-1.507]` left the adequacy green against an antecedent nothing
--     satisfied.  Sections 1 and 2 above and this section are the slice
--     that was checked alone; it is kept at
--     agents/tasks/LJ-1-518/runs/w3-slice.agda.txt.
--
--     THE CONSTRUCTION IS THE ONE THE TREE ALREADY USES FOR AN ORDER AS A
--     SET, and it is not invented here.  `L.Choice.Limit`'s `codeOrder`
--     is a separation out of a `smallDom` bound over the pairs
--     (src/L/Choice/Limit.lagda.md:418-419,607-608).  Three lines change:
--     the index is `⟪ α ⟫ × ⟪ α ⟫` and not the pairs of `Lset ω`, the
--     condition's comparison is `∈` and not the naming order, and the
--     condition carries the two membership conjuncts that confine both
--     components to `a`.
-- =====================================================================

module Witness (a : S) (oa : IsOrd (fst a)) where

  open Site a oa

  -- THE BOUND.  `smallDom` (src/L/Recursion.lagda.md:133) confines any
  -- small family of elements of `L` in one stage.  `⟪ α ⟫ × ⟪ α ⟫` is a
  -- `Type ℓ` because `⟪_⟫` is, so the family is small.
  bnd : Σ[ D ∈ S ] ((p : ⟪ α ⟫ × ⟪ α ⟫)
                    → ⟨ prʟ (memS (fst p)) (memS (snd p)) ∈ˢ D ⟩)
  bnd = smallDom (⟪ α ⟫ × ⟪ α ⟫) (λ p → prʟ (memS (fst p)) (memS (snd p)))

  D : S
  D = bnd .fst

  inD : (x m : S) (xa : ⟨ fst x ∈ α ⟩) (ma : ⟨ fst m ∈ α ⟩)
      → ⟨ pr (fst x) (fst m) ∈ fst D ⟩
  inD x m xa ma =
    subst (λ t → ⟨ t ∈ fst D ⟩)
      (prʟ-fst (memS (ix x xa)) (memS (ix m ma))
        ∙ cong₂ pr (ix-val x xa) (ix-val m ma))
      (bnd .snd (ix x xa , ix m ma))

  -- THE CONDITION.  In the environment `(d ∷ c ∷ z ∷ [])`: `z` is the
  -- separated variable, `z` is the pair of `c` and `d`, both components
  -- are members of `a`, and `c ∈ d`.  The pairing is DESCRIBED by
  -- `prAtL` and not named, exactly as `Cond₀` does
  -- (src/L/Choice/Limit.lagda.md:604-606).
  CondBody : Formula S 3
  CondBody =
    prAtL (s2 zero) (suc zero) zero
    ∧̇ ( (var (suc zero) ∈̇ con a)
      ∧̇ ( (var zero ∈̇ con a)
        ∧̇ (var (suc zero) ∈̇ var zero) ) )

  Cond : Formula S 1
  Cond = ∃̇ ( ∃̇ CondBody )

  -- perf: the carve is sealed where it is built, which is the law
  -- `L.Choice.Limit` records at its own separation
  -- (src/L/Choice/Limit.lagda.md:604-605).
  opaque
    ordQ : S
    ordQ = hasSeparationL D Cond .fst .fst

    ordQ-mem : (z : S) → (z ∈ˢ ordQ) ≡ ((z ∈ˢ D) ⊓ ((z ∷ []) ⊨ Cond))
    ordQ-mem = hasSeparationL D Cond .fst .snd

  private
    Inner : S → S → S → Type (ℓ-suc ℓ)
    Inner z c d = ⟨ (d ∷ c ∷ z ∷ []) ⊨ CondBody ⟩

    Outer : S → Type (ℓ-suc ℓ)
    Outer z = Σ[ c ∈ S ] PT.∥ (Σ[ d ∈ S ] Inner z c d) ∥₁

    cond-in : (z c d : S) → Inner z c d → ⟨ (z ∷ []) ⊨ Cond ⟩
    cond-in z c d hi = PT.∣ c , PT.∣ d , hi ∣₁ ∣₁

    cond-out : (z : S) → ⟨ (z ∷ []) ⊨ Cond ⟩ → PT.∥ Outer z ∥₁
    cond-out z h = h

  -- THE `∈`-ORDER FILLS `Q`.
  fill : ReadsIn ordQ
  fill x m xa ma h =
    subst (λ t → ⟨ t ∈ fst ordQ ⟩) qz
      (subst ⟨_⟩ (sym (ordQ-mem (prʟ x m)))
        ( subst (λ t → ⟨ t ∈ fst D ⟩) (sym qz) (inD x m xa ma)
        , cond-in (prʟ x m) x m (hpr , (xa , (ma , x∈m))) ))
    where
    qz : fst (prʟ x m) ≡ pr (fst x) (fst m)
    qz = prʟ-fst x m

    hpr : ⟨ (m ∷ x ∷ prʟ x m ∷ []) ⊨ prAtL (s2 zero) (suc zero) zero ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate (s2 zero) (suc zero) zero
             (m ∷ x ∷ prʟ x m ∷ []))) qz

    x∈m : ⟨ fst x ∈ fst m ⟩
    x∈m = ∈-cong (ix-val x xa) (ix-val m ma)
      (∈∈ₛ {a = ⟪ α ⟫↪ (ix x xa)} {b = ⟪ α ⟫↪ (ix m ma)} .snd h)

  -- AND `Q` HOLDS NOTHING ELSE.
  rep : ReadsOut ordQ
  rep x m h = PT.rec (isPropReadsOut ordQ x m) atC
                (cond-out (prʟ x m) cnd)
    where
    qz : fst (prʟ x m) ≡ pr (fst x) (fst m)
    qz = prʟ-fst x m

    inSet : ⟨ fst (prʟ x m) ∈ fst ordQ ⟩
    inSet = subst (λ t → ⟨ t ∈ fst ordQ ⟩) (sym qz) h

    cnd : ⟨ (prʟ x m ∷ []) ⊨ Cond ⟩
    cnd = subst ⟨_⟩ (ordQ-mem (prʟ x m)) inSet .snd

    atD : (c d : S) → Inner (prʟ x m) c d
        → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ]
          Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma)
    atD c d (hpr , (ca , (da , c∈d))) = xa , (ma , below)
      where
      qcd : pr (fst x) (fst m) ≡ pr (fst c) (fst d)
      qcd = sym qz
          ∙ subst ⟨_⟩ (prAtL-adequate (s2 zero) (suc zero) zero
                        (d ∷ c ∷ prʟ x m ∷ [])) hpr

      split : (fst x ≡ fst c) × (fst m ≡ fst d)
      split = pr-inj qcd

      xa : ⟨ fst x ∈ α ⟩
      xa = subst (λ v → ⟨ v ∈ α ⟩) (sym (split .fst)) ca

      ma : ⟨ fst m ∈ α ⟩
      ma = subst (λ v → ⟨ v ∈ α ⟩) (sym (split .snd)) da

      x∈m : ⟨ fst x ∈ fst m ⟩
      x∈m = ∈-cong (sym (split .fst)) (sym (split .snd)) c∈d

      below : ix x xa ≺ₛ ix m ma
      below = ∈∈ₛ {a = ⟪ α ⟫↪ (ix x xa)} {b = ⟪ α ⟫↪ (ix m ma)} .fst
             (∈-cong (sym (ix-val x xa)) (sym (ix-val m ma)) x∈m)

    atC : Outer (prʟ x m)
        → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ]
          Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma)
    atC (c , hd) = PT.rec (isPropReadsOut ordQ x m)
      (λ { (d , hi) → atD c d hi }) hd

  reads : Reads ordQ
  reads = rep , fill

-- =====================================================================
-- 4.  W3, AS THE BRIEF STATES IT.  The hypothesis is INHABITED, at the
--     ∈-order, at every ordinal of the model.
-- =====================================================================

ord-set-witness : (a : S) (oa : IsOrd (fst a))
                → Σ[ Q ∈ S ] ord-reads-Q Q a oa
ord-set-witness a oa = Witness.ordQ a oa , Witness.reads a oa

-- =====================================================================
-- 5.  THE ORDER IS THE ONE THE RANK RUNS ON.
--
--     Section 1 states the hypothesis at `_≺ₛ_`.  That name has to be
--     the ∈-order the counting leg actually has, and not a relation that
--     merely looks like it, so [LJ-1.515]'s `OrdSWO∈ₛ` is rebuilt here
--     (agents/tasks/LJ-1-515/Probe515.agda:236-283) and `site-is-swo`
--     proves the two relations are ONE relation.  A probe does not import
--     a probe, so this is a rebuild and not a reference.
-- =====================================================================

module OrdSWO∈ₛ (α : V ℓ) (oα : IsOrd α) where

  _≺ₛ_ : ⟪ α ⟫ → ⟪ α ⟫ → Type ℓ
  m ≺ₛ n = ⟨ ⟪ α ⟫↪ m ∈ₛ ⟪ α ⟫↪ n ⟩

  to∈ : {m n : ⟪ α ⟫} → m ≺ₛ n → ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n
  to∈ {m} {n} = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = ⟪ α ⟫↪ n} .snd

  fr∈ : {m n : ⟪ α ⟫} → ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n → m ≺ₛ n
  fr∈ {m} {n} = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = ⟪ α ⟫↪ n} .fst

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺ₛ n) (m ≡ n) (n ≺ₛ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺ₛ n) (m ≡ n) (n ≺ₛ m)
    go (inl h)       = lt (fr∈ h)
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt (fr∈ h)

  irr₁ : (m : ⟪ α ⟫) → (m ≺ₛ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) (to∈ h)

  trans₁ : (m n k : ⟪ α ⟫) → m ≺ₛ n → n ≺ₛ k → m ≺ₛ k
  trans₁ m n k h h' = fr∈ (ord-inord k .fst (to∈ h) (to∈ h'))

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺ₛ_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) (to∈ n≺m)))

  wf₁ : WellFounded _≺ₛ_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = record
    { _<∙_   = _≺ₛ_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

-- THE HYPOTHESIS IS STATED AT THE RANK'S OWN ORDER.  `swo-rank′` takes an
-- `SWO` and reads its order from that record's `_<∙_`
-- (agents/tasks/LJ-1-515/Probe515.agda:112-113,84).  This is that field.
site-is-swo : (a : S) (oa : IsOrd (fst a))
            → Site._≺ₛ_ a oa ≡ SWO._<∙_ (OrdSWO∈ₛ.w (fst a) oa)
site-is-swo a oa = refl

-- =====================================================================
-- 6.  WHAT THE ADEQUACY WILL SPEND.  Not the adequacy: AD12 gives this
--     brief one obligation and the adequacy is the next task.  These are
--     the three readings of the hypothesis that task needs, and they are
--     here because a hypothesis nobody can USE is worth as little as one
--     nobody can satisfy.
-- =====================================================================

module Consumes (Q a : S) (oa : IsOrd (fst a)) (hQ : ord-reads-Q Q a oa) where

  open Site a oa

  -- 6.1  THE DOMAIN CLAUSE.  `fnAt f Q m` pins f's domain to
  --      `{ x : appAt Q x m }` (agents/tasks/LJ-1-497/Probe497.agda:228),
  --      which `appAt-adequate` reads as `{ x : pr x m ∈ Q }`.  These two
  --      say that set is the ∈-predecessors of `m` inside `a`, and
  --      nothing else.
  dom-out : (m : S) (ma : ⟨ fst m ∈ α ⟩) (x : S)
          → ⟨ pr (fst x) (fst m) ∈ fst Q ⟩
          → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma)
  dom-out m ma x h =
    got .fst , subst (λ k → ix x (got .fst) ≺ₛ k) e (got .snd .snd)
    where
    got = hQ .fst x m h
    -- `⟨ fst m ∈ α ⟩` is a proposition, so the membership the hypothesis
    -- returns and the one the caller holds are the same index.
    e : ix m (got .snd .fst) ≡ ix m ma
    e = cong (ix m) (snd (fst m ∈ α) (got .snd .fst) ma)

  dom-in : (m : S) (ma : ⟨ fst m ∈ α ⟩) (x : S) (xa : ⟨ fst x ∈ α ⟩)
         → ix x xa ≺ₛ ix m ma → ⟨ pr (fst x) (fst m) ∈ fst Q ⟩
  dom-in m ma x xa h = hQ .snd x m xa ma h

  -- 6.2  THE MINIMAL CASE, WHICH IS WHERE [LJ-1.497] REFUTED THE OLD
  --      ADEQUACY.  Its witness took `Q := ∅`, so every member of `a` was
  --      Q-minimal (agents/tasks/LJ-1-497/Probe497.agda:365-368), while
  --      `swo-rank` was ∅-free at every member.  With the hypothesis the
  --      two notions of minimal are ONE notion, and `swo-rank′-∅`
  --      (agents/tasks/LJ-1-515/Probe515.agda:218-221) is stated at
  --      exactly the right-hand side below.
  q-min→min : (m : S) (ma : ⟨ fst m ∈ α ⟩)
            → ((y : S) → ⟨ pr (fst y) (fst m) ∈ fst Q ⟩ → Empty.⊥)
            → (k : ⟪ α ⟫) → k ≺ₛ ix m ma → Empty.⊥
  q-min→min m ma qmin k h = qmin (memS k) (dom-in m ma (memS k) (memS-mem k) h')
    where
    h' : ix (memS k) (memS-mem k) ≺ₛ ix m ma
    h' = subst (λ j → j ≺ₛ ix m ma) (sym (memS-ix k)) h

  min→q-min : (m : S) (ma : ⟨ fst m ∈ α ⟩)
            → ((k : ⟪ α ⟫) → k ≺ₛ ix m ma → Empty.⊥)
            → (y : S) → ⟨ pr (fst y) (fst m) ∈ fst Q ⟩ → Empty.⊥
  min→q-min m ma min y h = min (ix y (got .fst)) (got .snd)
    where
    got = dom-out m ma y h

-- 6.3  THE HYPOTHESIS PINS `Q`.  Two sets that both satisfy it hold the
--      same pairs, so it is a description of one set and not a filter
--      that many sets pass.  `∅` passes it only when `a` has no member
--      below another, which is `q-min→min` read at every member.
reads-pins : (Q Q' a : S) (oa : IsOrd (fst a))
           → ord-reads-Q Q a oa → ord-reads-Q Q' a oa
           → (x m : S) → ⟨ pr (fst x) (fst m) ∈ fst Q ⟩
                       → ⟨ pr (fst x) (fst m) ∈ fst Q' ⟩
reads-pins Q Q' a oa hQ hQ' x m h = hQ' .snd x m (got .fst) (got .snd .fst)
                                      (got .snd .snd)
  where
  got = hQ .fst x m h
