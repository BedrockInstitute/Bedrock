{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.537]  THE APPROXIMATING FUNCTION, AS A SET OF THE MODEL.
--
-- The obligation is `approx-carve`, section 6.  Section 1 is W3, the
-- formula, written first and typechecked ALONE
-- (agents/tasks/LJ-1-537/runs/W3.agda, runs/w3-1.out to w3-3.out).
--
-- D-10 FIRST, AND IT CHANGES THE PRICE OF THE WHOLE TASK.  The brief
-- asks which generator will carve the graph of `swo-rank′` over the
-- ∈-predecessors of `m`, and what formula it will be given, and orders
-- a STOP if the rank's recursion cannot be said in the object language.
--
-- THE RECURSION NEVER HAS TO BE SAID, BECAUSE AT AN ORDINAL SITE THE
-- RANK IS THE MEMBER ITSELF.  `P521.swo-rank′ w k` is
-- `⋃ { sucV (swo-rank′ w j) : j ≺ k }` (Probe521.agda:237-244 for the
-- recursion, :290-313 for what `boundingOrd` holds), and at
-- `w = OrdSWO∈ₛ.w α oα` the order `≺` IS ∈ (Probe521.agda:176-177).  So
-- the recursion is `x ↦ ⋃ { sucV y : y ∈ x }`, which is the identity on
-- every transitive set, and every member of an ordinal is transitive
-- (src/L/Constructible.lagda.md:141-142, second component).  Section 2
-- proves it: `rank-at′-is-member`.
--
-- So the graph of `swo-rank′` over the ∈-predecessors of `m` is the
-- IDENTITY GRAPH on `m`, the generator is `hasSeparationL`
-- (src/L/Axioms/Full.lagda.md:144-146) out of a `smallDom` bound
-- (src/L/Recursion.lagda.md:133), and the formula is
--
--   Cond = ∃̇ ( prAtL (suc zero) zero zero ∧̇ (var zero ∈̇ con m) ).
--
-- ONE IMPORT OF A PREDECESSOR PROBE, and it is [LJ-1.531]'s necessity
-- verbatim (agents/tasks/LJ-1-531/Probe531.agda:20-37): `P521.swo-rank′`
-- is SEALED (Probe521.agda:380-403) and this file needs two of the five
-- names the seal exports, `rank-mem-out` and `rank-mem-in`.  It also
-- needs the FORMULA the obligation is stated at, `fnAt`, `assignAt` and
-- `supAt` (Probe521.agda:456-491), and the reader module `Env`
-- (:512-689).  A rebuild would be 1176 lines and the obligation's type
-- would no longer be the one [LJ-1.521] left.
--
-- `bedrock.agda-lib:2` lists `agents/tasks` as an include root, and the
-- tree already carries cross-task probe imports
-- (agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24).
--
-- `domAt-in` IS NOT BUILT.  `domAt` IS NOT TOUCHED.  Nothing lands in
-- src/.  Does not postulate.  [LJ-1.521]'s `Witness` is NOT imported:
-- section 1 carves its own set, and the two differ (`Witness` separates
-- pairs of DISTINCT members out of a square; section 1 separates
-- DIAGONAL pairs out of the carrier).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-537.Probe537 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.WellOrder.Base {ℓ} using ( SWO )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate; svAt; svAt-in
        ; inDomAt; inDomAt-adequate; extAt; extAt-in-both
        ; sucAtL; sucAtL-adequate; prʟ; prʟ-fst )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Induction.WellFounded using ( Acc; acc )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))
  s4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  s4 i = suc (suc (suc (suc i)))
  s5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  s5 i = suc (suc (suc (suc (suc i))))

  -- membership transported along both components.  [LJ-1.521]'s
  -- (Probe521.agda:100-104) at the SMALL membership as well.
  ∈-cong : {u u' v v' : V ℓ} → u ≡ u' → v ≡ v'
         → ⟨ u ∈ v ⟩ → ⟨ u' ∈ v' ⟩
  ∈-cong {u} {u'} {v} {v'} pu pv h =
    subst (λ t → ⟨ t ∈ v' ⟩) pu (subst (λ t → ⟨ u ∈ t ⟩) pv h)

  ∈ₛ-cong : {u u' v v' : V ℓ} → u ≡ u' → v ≡ v'
          → ⟨ u ∈ₛ v ⟩ → ⟨ u' ∈ₛ v' ⟩
  ∈ₛ-cong {u} {u'} {v} {v'} pu pv h =
    subst (λ t → ⟨ t ∈ₛ v' ⟩) pu (subst (λ t → ⟨ u ∈ₛ t ⟩) pv h)

-- =====================================================================
-- 1.  THE CARVE.  W3, and it is runs/W3.agda verbatim but for the three
--     names that would clash with [LJ-1.521]'s `Site` in section 3.
-- =====================================================================

module Carve (m : S) where

  μ : V ℓ
  μ = fst m

  -- A member of `m` is an element of the model.  [LJ-1.521]'s
  -- `Site.memS` (Probe521.agda:129-130) at `m` instead of at `a`.
  memM : ⟪ μ ⟫ → S
  memM k = ⟪ μ ⟫↪ k , isL-trans {x = μ} {y = ⟪ μ ⟫↪ k} (member μ k) (snd m)

  ixm : (x : S) → ⟨ fst x ∈ μ ⟩ → ⟪ μ ⟫
  ixm x h = fiber μ h .fst

  ixm-val : (x : S) (h : ⟨ fst x ∈ μ ⟩) → ⟪ μ ⟫↪ (ixm x h) ≡ fst x
  ixm-val x h = fiber μ h .snd

  -- THE BOUND.  [LJ-1.521]'s `Witness.bnd` (Probe521.agda:1046-1053)
  -- took the SQUARE of the carrier because its condition related two
  -- members.  This one relates a member to itself.
  bnd : Σ[ d ∈ S ] ((k : ⟪ μ ⟫) → ⟨ prʟ (memM k) (memM k) ∈ˢ d ⟩)
  bnd = smallDom ⟪ μ ⟫ (λ k → prʟ (memM k) (memM k))

  D : S
  D = bnd .fst

  inD : (x : S) (xm : ⟨ fst x ∈ μ ⟩) → ⟨ pr (fst x) (fst x) ∈ fst D ⟩
  inD x xm =
    subst (λ t → ⟨ t ∈ fst D ⟩)
      (prʟ-fst (memM (ixm x xm)) (memM (ixm x xm))
        ∙ cong₂ pr (ixm-val x xm) (ixm-val x xm))
      (bnd .snd (ixm x xm))

  -- THE FORMULA.  Variable 0 of `Body` is the carved member, variable 1
  -- is the candidate pair.
  Body : Formula S 2
  Body = prAtL (suc zero) zero zero ∧̇ (var zero ∈̇ con m)

  Cond : Formula S 1
  Cond = ∃̇ Body

  opaque
    G : S
    G = hasSeparationL D Cond .fst .fst

    G-mem : (z : S) → (z ∈ˢ G) ≡ ((z ∈ˢ D) ⊓ ((z ∷ []) ⊨ Cond))
    G-mem = hasSeparationL D Cond .fst .snd

  graph-in : (x : S) → ⟨ fst x ∈ μ ⟩ → ⟨ pr (fst x) (fst x) ∈ fst G ⟩
  graph-in x xm =
    subst (λ t → ⟨ t ∈ fst G ⟩) qz
      (subst ⟨_⟩ (sym (G-mem (prʟ x x)))
        ( subst (λ t → ⟨ t ∈ fst D ⟩) (sym qz) (inD x xm)
        , PT.∣ x , (hpr , xm) ∣₁ ))
    where
    qz : fst (prʟ x x) ≡ pr (fst x) (fst x)
    qz = prʟ-fst x x

    hpr : ⟨ (x ∷ prʟ x x ∷ []) ⊨ prAtL (suc zero) zero zero ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate (suc zero) zero zero (x ∷ prʟ x x ∷ []))) qz

  graph-out : (x v : S) → ⟨ pr (fst x) (fst v) ∈ fst G ⟩
            → ⟨ fst x ∈ μ ⟩ × (fst v ≡ fst x)
  graph-out x v h = PT.rec isPropTgt at cnd
    where
    isPropTgt : isProp (⟨ fst x ∈ μ ⟩ × (fst v ≡ fst x))
    isPropTgt = isProp× (snd (fst x ∈ μ)) (setIsSet (fst v) (fst x))

    qz : fst (prʟ x v) ≡ pr (fst x) (fst v)
    qz = prʟ-fst x v

    cnd : ⟨ (prʟ x v ∷ []) ⊨ Cond ⟩
    cnd = subst ⟨_⟩ (G-mem (prʟ x v))
            (subst (λ t → ⟨ t ∈ fst G ⟩) (sym qz) h) .snd

    at : Σ[ c ∈ S ] ⟨ (c ∷ prʟ x v ∷ []) ⊨ Body ⟩
       → ⟨ fst x ∈ μ ⟩ × (fst v ≡ fst x)
    at (c , (hpr , cm)) =
      subst (λ t → ⟨ t ∈ μ ⟩) (sym (split .fst)) cm
      , (split .snd ∙ sym (split .fst))
      where
      qcv : pr (fst x) (fst v) ≡ pr (fst c) (fst c)
      qcv = sym qz
          ∙ subst ⟨_⟩
              (prAtL-adequate (suc zero) zero zero (c ∷ prʟ x v ∷ [])) hpr

      split : (fst x ≡ fst c) × (fst v ≡ fst c)
      split = pr-inj qcv

  -- The graph at a value that is only PROPOSITIONALLY the member.
  graph-in′ : (x v : S) → ⟨ fst x ∈ μ ⟩ → fst v ≡ fst x
            → ⟨ pr (fst x) (fst v) ∈ fst G ⟩
  graph-in′ x v xm e =
    subst (λ t → ⟨ pr (fst x) t ∈ fst G ⟩) (sym e) (graph-in x xm)

-- =====================================================================
-- 2.  THE RANK IS THE MEMBER.  This is the D-10 answer, proved.
--
--     Nothing here unfolds the sealed recursion: the argument spends
--     exactly `rank-mem-out` and `rank-mem-in`, two of the five names
--     [LJ-1.521]'s seal exports (Probe521.agda:387-402).
-- =====================================================================

module Ident (α : V ℓ) (oα : IsOrd α) where

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = P521.OrdSWO∈ₛ.w α oα

  _≺_ : ⟪ α ⟫ → ⟪ α ⟫ → Type ℓ
  _≺_ = P521.OrdSWO∈ₛ._≺ₛ_ α oα

  rank-id-acc : (k : ⟪ α ⟫) → Acc _≺_ k → P521.swo-rank′ w k ≡ ⟪ α ⟫↪ k
  rank-id-acc k (acc rs) =
    extensionality (P521.swo-rank′ w k) κ (out , inn)
    where
    κ : V ℓ
    κ = ⟪ α ⟫↪ k

    κ∈α : ⟨ κ ∈ α ⟩
    κ∈α = member α k

    -- every member of an ordinal is transitive
    κ-trans = oα .snd κ κ∈α

    out : (u : V ℓ) → ⟨ u ∈ₛ P521.swo-rank′ w k ⟩ → ⟨ u ∈ₛ κ ⟩
    out u h = PT.rec (snd (u ∈ₛ κ)) step (P521.rank-mem-out w k u h)
      where
      step : Σ[ j ∈ ⟪ α ⟫ ]
               (SWO._<∙_ w j k × ⟨ u ∈ₛ sucV (P521.swo-rank′ w j) ⟩)
           → ⟨ u ∈ₛ κ ⟩
      step (j , (hj , hu)) =
        ∈∈ₛ {a = u} {b = κ} .fst
          (∈sucV-elim {A = ⟪ α ⟫↪ j} {x = u} (snd (u ∈ κ)) hu'
            (λ u∈j → κ-trans u∈j j∈κ)
            (λ u≡j → subst (λ t → ⟨ t ∈ κ ⟩) (sym u≡j) j∈κ))
        where
        j∈κ : ⟨ ⟪ α ⟫↪ j ∈ κ ⟩
        j∈κ = ∈∈ₛ {a = ⟪ α ⟫↪ j} {b = κ} .snd hj

        hu' : ⟨ u ∈ sucV (⟪ α ⟫↪ j) ⟩
        hu' = subst (λ t → ⟨ u ∈ sucV t ⟩) (rank-id-acc j (rs j hj))
                (∈∈ₛ {a = u} {b = sucV (P521.swo-rank′ w j)} .snd hu)

    inn : (u : V ℓ) → ⟨ u ∈ₛ κ ⟩ → ⟨ u ∈ₛ P521.swo-rank′ w k ⟩
    inn u h = P521.rank-mem-in w k u j hj hsuc
      where
      u∈α : ⟨ u ∈ α ⟩
      u∈α = oα .fst (∈∈ₛ {a = u} {b = κ} .snd h) κ∈α

      j : ⟪ α ⟫
      j = fiber α u∈α .fst

      jv : ⟪ α ⟫↪ j ≡ u
      jv = fiber α u∈α .snd

      hj : SWO._<∙_ w j k
      hj = subst (λ t → ⟨ t ∈ₛ κ ⟩) (sym jv) h

      hsuc : ⟨ u ∈ₛ sucV (P521.swo-rank′ w j) ⟩
      hsuc =
        subst (λ t → ⟨ u ∈ₛ sucV t ⟩) (sym (rank-id-acc j (rs j hj)))
          (subst (λ t → ⟨ u ∈ₛ sucV t ⟩) (sym jv)
            (∈∈ₛ {a = u} {b = sucV u} .fst (self∈sucV u)))

  rank-id : (k : ⟪ α ⟫) → P521.swo-rank′ w k ≡ ⟪ α ⟫↪ k
  rank-id k = rank-id-acc k (P521.OrdSWO∈ₛ.wf₁ α oα k)

-- THE EQUATION EVERY CONSUMER BELOW SPENDS.
rank-at′-is-member :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx) ≡ fst m
rank-at′-is-member a oa m mx =
    P521.rank-at′-val a oa m mx
  ∙ Ident.rank-id (fst a) oa (fiber (fst a) mx .fst)
  ∙ fiber (fst a) mx .snd

-- =====================================================================
-- 3.  THE SITE, AND WHAT `Q` READS.
--
--     `hQ` is the hypothesis [LJ-1.518] introduced and [LJ-1.521]
--     inhabited (Probe521.agda:1046-1164).  The two lemmas below are
--     the only use this file makes of it: a Q-pair IS an ∈-pair, both
--     ways, at members of `a`.
-- =====================================================================

module Build (a : S) (oa : IsOrd (fst a)) (Q : S)
             (hQ : P521.ord-reads-Q Q a oa)
             (m : S) (mx : ⟨ fst m ∈ fst a ⟩) where

  open P521.Site a oa using ( α ; ix ; ix-val ; PairOf )
  open Carve m

  r : S
  r = P521.rank-at′ a oa m mx

  -- THE RANK SLOT, IDENTIFIED.  Section 2 at this site.
  rv : fst r ≡ μ
  rv = rank-at′-is-member a oa m mx

  z : S
  z = prʟ m r

  open P521.Env z Q m r G

  -- transitivity, twice: `α` is transitive and every member of `α` is.
  μ-trans = oa .snd μ mx

  ∈μ→∈α : (x : S) → ⟨ fst x ∈ μ ⟩ → ⟨ fst x ∈ α ⟩
  ∈μ→∈α x h = oa .fst h mx

  memb-trans : (x : S) → ⟨ fst x ∈ μ ⟩
             → {u v : V ℓ} → ⟨ u ∈ v ⟩ → ⟨ v ∈ fst x ⟩ → ⟨ u ∈ fst x ⟩
  memb-trans x xm = oa .snd (fst x) (∈μ→∈α x xm)

  qp→∈ : (x n : S) → PairOf Q x n → ⟨ fst x ∈ fst n ⟩
  qp→∈ x n h = ∈∈ₛ {a = fst x} {b = fst n} .snd
    (∈ₛ-cong (ix-val x (hQ .fst x n h .fst))
             (ix-val n (hQ .fst x n h .snd .fst))
             (hQ .fst x n h .snd .snd))

  ∈→qp : (x n : S) (xa : ⟨ fst x ∈ α ⟩) (na : ⟨ fst n ∈ α ⟩)
       → ⟨ fst x ∈ fst n ⟩ → PairOf Q x n
  ∈→qp x n xa na h =
    hQ .snd x n xa na
      (∈ₛ-cong (sym (ix-val x xa)) (sym (ix-val n na))
        (∈∈ₛ {a = fst x} {b = fst n} .fst h))

  -- ===================================================================
  -- 4.  THE THREE SATISFACTION PROPERTIES.
  -- ===================================================================

  -- 4.1  `fnAt`.  `G` is single-valued because its only pairs are
  --      diagonal, and its domain is the ∈-predecessors of `m`, which
  --      is what `Q` reads at `m`.
  fn : Fn
  fn = sv , (λ x → fwd x , bwd x)
    where
    sv : ⟨ γ5 ⊨ svAt zero ⟩
    sv = svAt-in zero γ5
           (λ x y y' p q → graph-out x y p .snd ∙ sym (graph-out x y' q .snd))

    fwd : (x : S) → ⟨ (x ∷ γ5) ⊨ inDomAt (suc zero) zero ⟩
        → ⟨ (x ∷ γ5) ⊨ appAt (suc (s3 zero)) zero (suc (s2 zero)) ⟩
    fwd x hd = subst ⟨_⟩
      (sym (appAt-adequate (suc (s3 zero)) zero (suc (s2 zero)) (x ∷ γ5)))
      (PT.rec (snd (pr (fst x) (fst m) ∈ fst Q)) at
        (subst ⟨_⟩ (inDomAt-adequate (suc zero) zero (x ∷ γ5)) hd))
      where
      at : Σ[ v ∈ S ] Tab x v → PairOf Q x m
      at (v , tab) = ∈→qp x m (∈μ→∈α x xm) mx xm
        where
        xm : ⟨ fst x ∈ μ ⟩
        xm = graph-out x v tab .fst

    bwd : (x : S) → ⟨ (x ∷ γ5) ⊨ appAt (suc (s3 zero)) zero (suc (s2 zero)) ⟩
        → ⟨ (x ∷ γ5) ⊨ inDomAt (suc zero) zero ⟩
    bwd x hq = subst ⟨_⟩
      (sym (inDomAt-adequate (suc zero) zero (x ∷ γ5)))
      PT.∣ x , graph-in x xm ∣₁
      where
      xm : ⟨ fst x ∈ μ ⟩
      xm = qp→∈ x m
        (subst ⟨_⟩
          (appAt-adequate (suc (s3 zero)) zero (suc (s2 zero)) (x ∷ γ5)) hq)

  -- 4.2  `supAt`.  `r` holds exactly the members of the successors of
  --      `G`'s values, and that set is `m` itself, which is what
  --      section 2 says `r` is.
  sup : Sup
  sup = extAt-in-both (suc zero) (P521.supBody zero) γ5 sfwd sbwd
    where
    sfwd : (u : S) → ⟨ fst u ∈ fst r ⟩ → ⟨ (u ∷ γ5) ⊨ P521.supBody zero ⟩
    sfwd u hu = PT.∣ u , PT.∣ u , (hp , PT.∣ sucʟ u , (hsuc , hin) ∣₁) ∣₁ ∣₁
      where
      um : ⟨ fst u ∈ μ ⟩
      um = subst (λ t → ⟨ fst u ∈ t ⟩) rv hu

      hp = subst ⟨_⟩
             (sym (appAt-adequate (s3 zero) (suc zero) zero (u ∷ u ∷ u ∷ γ5)))
             (graph-in u um)

      hsuc = subst ⟨_⟩
               (sym (sucAtL-adequate (suc zero) zero
                      (sucʟ u ∷ u ∷ u ∷ u ∷ γ5)))
               (sucʟ-fst u)

      hin : ⟨ fst u ∈ fst (sucʟ u) ⟩
      hin = subst (λ t → ⟨ fst u ∈ t ⟩) (sym (sucʟ-fst u)) (self∈sucV (fst u))

    sbwd : (u : S) → ⟨ (u ∷ γ5) ⊨ P521.supBody zero ⟩ → ⟨ fst u ∈ fst r ⟩
    sbwd u hb = PT.rec (snd (fst u ∈ fst r)) at1 hb
      where
      atS : (x v : S) → Tab x v
          → Σ[ s ∈ S ]
              (⟨ (s ∷ v ∷ x ∷ u ∷ γ5) ⊨ sucAtL (suc zero) zero ⟩
               × ⟨ fst u ∈ fst s ⟩)
          → ⟨ fst u ∈ fst r ⟩
      atS x v tab (s , (hsuc , hin)) =
        subst (λ t → ⟨ fst u ∈ t ⟩) (sym rv)
          (∈sucV-elim {A = fst x} {x = fst u} (snd (fst u ∈ μ)) u∈sx
            (λ h → μ-trans h xm)
            (λ e → subst (λ t → ⟨ t ∈ μ ⟩) (sym e) xm))
        where
        xm : ⟨ fst x ∈ μ ⟩
        xm = graph-out x v tab .fst

        es : fst s ≡ sucV (fst v)
        es = subst ⟨_⟩
               (sucAtL-adequate (suc zero) zero (s ∷ v ∷ x ∷ u ∷ γ5)) hsuc

        u∈sx : ⟨ fst u ∈ sucV (fst x) ⟩
        u∈sx = subst (λ t → ⟨ fst u ∈ t ⟩)
                 (es ∙ cong sucV (graph-out x v tab .snd)) hin

      at2 : (x : S)
          → Σ[ v ∈ S ] ⟨ (v ∷ x ∷ u ∷ γ5) ⊨ P521.supB2 zero ⟩
          → ⟨ fst u ∈ fst r ⟩
      at2 x (v , (hp , hs)) =
        PT.rec (snd (fst u ∈ fst r)) (atS x v tab) hs
        where
        tab : Tab x v
        tab = subst ⟨_⟩
                (appAt-adequate (s3 zero) (suc zero) zero (v ∷ x ∷ u ∷ γ5)) hp

      at1 : Σ[ x ∈ S ] ⟨ (x ∷ u ∷ γ5) ⊨ P521.supB1 zero ⟩
          → ⟨ fst u ∈ fst r ⟩
      at1 (x , hx) = PT.rec (snd (fst u ∈ fst r)) (at2 x) hx

  -- 4.3  `assignAt`.  The value at a member `x` is the union of the
  --      successors of the values at `x`'s Q-predecessors.  Both sides
  --      are `x`: the left because `G` is the diagonal, the right
  --      because `x` is transitive.
  --
  --      `readψ` is [LJ-1.521]'s `asgRead` (Probe521.agda:615-649) with
  --      the `extAt-out` step removed, because the caller here is
  --      BUILDING the `extAt` and cannot consume it.
  readψ : (x' v' u : S)
        → ⟨ (u ∷ v' ∷ x' ∷ γ5) ⊨ P521.asgψ zero (s3 zero) ⟩
        → PT.∥ (Σ[ y ∈ S ] Σ[ u' ∈ S ]
                 (Qp y x' × Tab y u' × ⟨ fst u ∈ sucV (fst u') ⟩)) ∥₁
  readψ x' v' u hψ = PT.rec PT.squash₁ atY hψ
    where
    Out : Type (ℓ-suc ℓ)
    Out = Σ[ y ∈ S ] Σ[ u' ∈ S ]
            (Qp y x' × Tab y u' × ⟨ fst u ∈ sucV (fst u') ⟩)

    atY : Σ[ y ∈ S ] ⟨ (y ∷ u ∷ v' ∷ x' ∷ γ5) ⊨ P521.asgχ zero (s3 zero) ⟩
        → PT.∥ Out ∥₁
    atY (y , (hq , hu')) = PT.rec PT.squash₁ atU hu'
      where
      qy : Qp y x'
      qy = subst ⟨_⟩
             (appAt-adequate (s4 (s3 zero)) zero (s3 zero)
               (y ∷ u ∷ v' ∷ x' ∷ γ5)) hq

      atU : Σ[ u' ∈ S ] ⟨ (u' ∷ y ∷ u ∷ v' ∷ x' ∷ γ5) ⊨ P521.asgρ zero ⟩
          → PT.∥ Out ∥₁
      atU (u' , (hf' , hs)) = PT.map atS hs
        where
        tu : Tab y u'
        tu = subst ⟨_⟩
               (appAt-adequate (s5 zero) (suc zero) zero
                 (u' ∷ y ∷ u ∷ v' ∷ x' ∷ γ5)) hf'

        atS : Σ[ s ∈ S ]
                (⟨ (s ∷ u' ∷ y ∷ u ∷ v' ∷ x' ∷ γ5)
                   ⊨ sucAtL (suc zero) zero ⟩
                 × ⟨ fst u ∈ fst s ⟩)
            → Out
        atS (s , (hsuc , hin)) = y , (u' , (qy , (tu ,
          subst (λ t → ⟨ fst u ∈ t ⟩)
            (subst ⟨_⟩
              (sucAtL-adequate (suc zero) zero
                (s ∷ u' ∷ y ∷ u ∷ v' ∷ x' ∷ γ5)) hsuc)
            hin)))

  -- `fillψ` is the same shape written the other way: [LJ-1.521]'s
  -- `asgFill` (Probe521.agda:651-666) with the `extAt-in` step removed.
  fillψ : (x' v' u y u' s : S)
        → Qp y x' → Tab y u' → fst s ≡ sucV (fst u') → ⟨ fst u ∈ fst s ⟩
        → ⟨ (u ∷ v' ∷ x' ∷ γ5) ⊨ P521.asgψ zero (s3 zero) ⟩
  fillψ x' v' u y u' s qy tu es hin =
    PT.∣ y , (hq , PT.∣ u' , (hf' , PT.∣ s , (hsuc , hin) ∣₁) ∣₁) ∣₁
    where
    hq = subst ⟨_⟩
           (sym (appAt-adequate (s4 (s3 zero)) zero (s3 zero)
                  (y ∷ u ∷ v' ∷ x' ∷ γ5))) qy
    hf' = subst ⟨_⟩
            (sym (appAt-adequate (s5 zero) (suc zero) zero
                   (u' ∷ y ∷ u ∷ v' ∷ x' ∷ γ5))) tu
    hsuc = subst ⟨_⟩
             (sym (sucAtL-adequate (suc zero) zero
                    (s ∷ u' ∷ y ∷ u ∷ v' ∷ x' ∷ γ5))) es

  asg : Asg
  asg x hd = PT.rec PT.squash₁ mk
    (subst ⟨_⟩ (inDomAt-adequate (suc zero) zero (x ∷ γ5)) hd)
    where
    mk : Σ[ v ∈ S ] Tab x v
       → PT.∥ (Σ[ v' ∈ S ]
                (⟨ (v' ∷ x ∷ γ5) ⊨ appAt (s2 zero) (suc zero) zero ⟩
                 × AsgExt x v')) ∥₁
    mk (v , tab) = PT.∣ x , (hp , hext) ∣₁
      where
      xm : ⟨ fst x ∈ μ ⟩
      xm = graph-out x v tab .fst

      x-trans = memb-trans x xm

      hp = subst ⟨_⟩
             (sym (appAt-adequate (s2 zero) (suc zero) zero (x ∷ x ∷ γ5)))
             (graph-in x xm)

      afwd : (u : S) → ⟨ fst u ∈ fst x ⟩
           → ⟨ (u ∷ x ∷ x ∷ γ5) ⊨ P521.asgψ zero (s3 zero) ⟩
      afwd u hu = fillψ x x u u u (sucʟ u) qy (graph-in u um)
                    (sucʟ-fst u) hins
        where
        um : ⟨ fst u ∈ μ ⟩
        um = μ-trans hu xm

        qy : Qp u x
        qy = ∈→qp u x (∈μ→∈α u um) (∈μ→∈α x xm) hu

        hins : ⟨ fst u ∈ fst (sucʟ u) ⟩
        hins = subst (λ t → ⟨ fst u ∈ t ⟩) (sym (sucʟ-fst u))
                 (self∈sucV (fst u))

      abwd : (u : S) → ⟨ (u ∷ x ∷ x ∷ γ5) ⊨ P521.asgψ zero (s3 zero) ⟩
           → ⟨ fst u ∈ fst x ⟩
      abwd u hψ = PT.rec (snd (fst u ∈ fst x)) go (readψ x x u hψ)
        where
        go : Σ[ y ∈ S ] Σ[ u' ∈ S ]
               (Qp y x × Tab y u' × ⟨ fst u ∈ sucV (fst u') ⟩)
           → ⟨ fst u ∈ fst x ⟩
        go (y , (u' , (qy , (tu , hsu)))) =
          ∈sucV-elim {A = fst y} {x = fst u} (snd (fst u ∈ fst x)) u∈sy
            (λ h → x-trans h y∈x)
            (λ e → subst (λ t → ⟨ t ∈ fst x ⟩) (sym e) y∈x)
          where
          y∈x : ⟨ fst y ∈ fst x ⟩
          y∈x = qp→∈ y x qy

          u∈sy : ⟨ fst u ∈ sucV (fst y) ⟩
          u∈sy = subst (λ t → ⟨ fst u ∈ sucV t ⟩)
                   (graph-out y u' tu .snd) hsu

      hext : AsgExt x x
      hext = extAt-in-both zero (P521.asgψ zero (s3 zero)) (x ∷ x ∷ γ5)
               afwd abwd

-- =====================================================================
-- 5.  THE OBLIGATION'S TYPE.
--
--     "f satisfies fnAt, assignAt and supAt" is read at the environment
--     `rankFo` puts them in (Probe521.agda:493-501): five slots
--     `(f ∷ r ∷ m ∷ q ∷ z ∷ [])`, the rank slot `r` filled by
--     `rank-at′`, the order slot `q` by [LJ-1.521]'s own witness
--     (Probe521.agda:1162-1164), and the pair slot `z` by the pair the
--     converse will have to exhibit.  Slot `z` is read by no conjunct.
-- =====================================================================

Qwit : (a : S) → IsOrd (fst a) → S
Qwit a oa = P521.ord-set-witness a oa .fst

Zof : (a : S) (oa : IsOrd (fst a)) (m : S) → ⟨ fst m ∈ fst a ⟩ → S
Zof a oa m mx = prʟ m (P521.rank-at′ a oa m mx)

Approximates : (a : S) (oa : IsOrd (fst a)) (m : S)
               (mx : ⟨ fst m ∈ fst a ⟩) → S → Type (ℓ-suc ℓ)
Approximates a oa m mx f =
    P521.Env.Fn  (Zof a oa m mx) (Qwit a oa) m (P521.rank-at′ a oa m mx) f
  × P521.Env.Asg (Zof a oa m mx) (Qwit a oa) m (P521.rank-at′ a oa m mx) f
  × P521.Env.Sup (Zof a oa m mx) (Qwit a oa) m (P521.rank-at′ a oa m mx) f

-- =====================================================================
-- 6.  THE OBLIGATION.
-- =====================================================================

-- The general form.  Any `Q` the hypothesis reads will do; the brief's
-- type is this one at [LJ-1.521]'s witness.
approx-carve-at :
    (a : S) (oa : IsOrd (fst a)) (Q : S) (hQ : P521.ord-reads-Q Q a oa)
    (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → Σ[ f ∈ S ]
      ( P521.Env.Fn  (prʟ m (P521.rank-at′ a oa m mx)) Q m
                     (P521.rank-at′ a oa m mx) f
      × P521.Env.Asg (prʟ m (P521.rank-at′ a oa m mx)) Q m
                     (P521.rank-at′ a oa m mx) f
      × P521.Env.Sup (prʟ m (P521.rank-at′ a oa m mx)) Q m
                     (P521.rank-at′ a oa m mx) f )
approx-carve-at a oa Q hQ m mx =
    Carve.G m
  , ( Build.fn a oa Q hQ m mx
    , ( Build.asg a oa Q hQ m mx
      , Build.sup a oa Q hQ m mx ) )

approx-carve :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → Σ[ f ∈ S ] Approximates a oa m mx f
approx-carve a oa m mx =
  approx-carve-at a oa (Qwit a oa) (P521.ord-set-witness a oa .snd) m mx

-- THE APPROXIMATING FUNCTION IS THE GRAPH THE BRIEF NAMED, and this is
-- the sentence that says so rather than merely satisfying the three
-- conjuncts: the carved set holds exactly the pairs
-- `(x , swo-rank′ x)` for `x` an ∈-predecessor of `m`.
approx-is-the-rank-graph :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
    (x : S) (xm : ⟨ fst x ∈ fst m ⟩)
  → ⟨ pr (fst x) (fst (P521.rank-at′ a oa x (oa .fst xm mx)))
      ∈ fst (approx-carve a oa m mx .fst) ⟩
approx-is-the-rank-graph a oa m mx x xm =
  Carve.graph-in′ m x (P521.rank-at′ a oa x (oa .fst xm mx)) xm
    (rank-at′-is-member a oa x (oa .fst xm mx))
