{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.104] probe A: the Mem row in tied form, WITH arityK.
--
-- [LJ-1.102] measured that the row's out fails at EnvSet's second
-- component: the Chain tie (premise z ∈ E) leaves the second
-- component's z ∈ E unsolved, and the ChainZ tie (premise z ∈ K)
-- leaves the first component's z ∈ K unsolved.  The two are one
-- arityK step apart: z ∈ E and E ∈ K give z ∈ K.
--
-- This probe adds arityK to the row's telescope (KFacts field,
-- src/L/Condensation.lagda.md:5769-5770), states entryK in the
-- ChainZ tie (premise z ∈ K), and threads arityK plus the row's EK
-- and arK into a tied EnvSet copy.  Both EnvSet directions close,
-- and the row's out and back both elaborate.
--
-- The tmKeyK repair: [LJ-1.102]'s restated telescope carried the
-- tied keyValK (tag satisfaction -> k ∈ K) at the row's 11-slot
-- environment.  That form is REFUTED (module RefuteKeyValK below):
-- the code slot is a quantified variable, so the tag satisfaction
-- can be forced at the K-slot element X, and the conclusion is
-- X ∈ X.  The honest repair is a DERIVATION inside the tied AtomLeaf
-- copy: from the code slot's membership (aK or bK, supplied by
-- codesK in back and by the row's binders in out), arityK, and the
-- tag satisfaction, the key's membership k ∈ K follows by the
-- [LJ-1.99] pair chain.  keyValK is therefore not a telescope
-- hypothesis; it costs zero.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1104A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )
open import L.Coding.Model {ℓ}
  using ( envOverAt; envSetAt; extAt-in-both; appAt; appAt-adequate; prʟ
        ; prʟ-fst; domAt-intro; domAt-out; domAt-in
        ; svAt-in; svAt-out
        ; valuesInAt-in; valuesInAt-out
        ; tagAtL; tagAtL-adequate; prAtL-adequate; tmValAt; memClauseAt; atomBody
        ; arityTagPairAtL-adequate )
open import L.Condensation {ℓ} lem
  using ( envBndGen; envSetB; arTagPairB; envHypB2T; atomBodyB; tmValB
        ; extAt→extAtB; extAtB→extAt
        ; module Mem; module BinaryShape )
open import ProbeLJ199A {ℓ} lem using ( module ChainZ )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open AbsL using ( _^_ )

-- =====================================================================
-- THE keyValK REFUTATION, MEASURED.  [LJ-1.102]'s restated telescope
-- carried the tied tmKeyK repair:
--
--   keyValK : (E yc b a ar c w v z k : S)
--           → ⟨ (k ∷ w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
--                tagAtL (suc^7 zero) 1 zero ⟩ → ⟨ fst k ∈ fst (lookup K γ) ⟩
--
-- The code slot (position 7 = a) and the key k are BOTH quantified
-- variables.  At k = X (the K-slot element) and a = prʟ (numeralL 1)
-- X the tag satisfaction holds (tagAtL-adequate, prʟ-fst,
-- numeralL-fst), and the conclusion is X ∈ X, refuted by ∈-irrefl.
-- The tie is an empty type at the abstract frame (C-38): it cannot
-- sit in the row's telescope.
-- =====================================================================
module RefuteKeyValK {m : ℕ} (K : Fin m) (γ : S ^ m) where

  X : S
  X = lookup K γ

  A : V ℓ
  A = fst X

  -- The 11-slot environment with a := prʟ (numeralL 1) X and every
  -- other slot X.
  env : S ^ (11 + m)
  env = X ∷ X ∷ X ∷ X ∷ X ∷ X ∷ X ∷ prʟ (numeralL 1) X ∷ X ∷ X ∷ X ∷ γ

  tagEq : fst (lookup (suc (suc (suc (suc (suc (suc (suc zero))))))) env)
        ≡ pr (# 1) (fst (lookup zero env))
  tagEq = prʟ-fst (numeralL 1) X ∙ cong₂ pr (numeralL-fst 1) refl

  premise : ⟨ env ⊨ tagAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) 1 zero ⟩
  premise = transport (cong fst (sym
              (tagAtL-adequate (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                1 zero env))) tagEq

  keyValK-type : Type (ℓ-suc ℓ)
  keyValK-type = (E yc b a ar c w v z k : S)
               → ⟨ (k ∷ w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                    tagAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) 1 zero ⟩
               → ⟨ fst k ∈ fst (lookup K γ) ⟩

  keyValK-refutes : keyValK-type → Empty.⊥
  keyValK-refutes keyValK = ∈-irrefl A
    (keyValK X X X (prʟ (numeralL 1) X) X X X X X X premise)

-- =====================================================================
-- ENVSET, RESTATED WITH arityK.  Copy of
-- src/L/Condensation.lagda.md:2771-2874.  The tied entryK has the
-- ChainZ shape (premise z ∈ K).  The out direction's FIRST component
-- climbs z ∈ E to z ∈ K by arityK and E ∈ K; its SECOND component
-- has z ∈ K from envInK directly.  Both components close, and the
-- back direction closes the same way.  arSubK keeps the untied
-- shape at this telescope; the row supplies it as the tied
-- arSubK-tied applied to its arK binder.
-- =====================================================================
module EnvSetTied {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩)
  (entryK : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
          → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where

  φB : Formula S (suc n)
  φB = envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B)

  φ : Formula S (suc n)
  φ = envOverAt zero (suc ar) (suc B)

  -- The app formula at the three-binder frame is the pair membership.
  app3 : (z x y y' : S)
       → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
            appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero) ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app3 z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app3' : (z x y y' : S)
        → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
             appAt (suc (suc (suc zero))) (suc (suc zero)) zero ⟩
        ≡ ⟨ pr (fst x) (fst y') ∈ fst z ⟩
  app3' z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) zero
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app2 : (z x y : S)
       → ⟨ (y ∷ x ∷ z ∷ γ) ⊨ appAt (suc (suc zero)) (suc zero) zero ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app2 z x y =
    cong ⟨_⟩ (appAt-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ z ∷ γ))

  -- STORY TO MACHINE, TIED: the K-bounded condition gives the
  -- machine's unbounded condition, given z ∈ K.
  bnd→over-tied : (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
                → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  bnd→over-tied z zK hb =
      svAt-in zero (z ∷ γ)
        (λ x y y' p q →
          let xK = entryK z x y zK p .fst
              yK = entryK z x y zK p .snd
              y'K = entryK z x y' zK q .snd
          in hb .fst x xK y yK y' y'K
               (transport (sym (app3 z x y y')) p)
               (transport (sym (app3' z x y y')) q))
    , domAt-intro zero (suc ar) (z ∷ γ)
        (λ x →
            (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                      (λ { (y , p) →
                        hb .snd .fst x (entryK z x y zK p .fst) .fst
                          ∣ y , ( entryK z x y zK p .snd
                                , transport (sym (app2 z x y)) p ) ∣₁ })
                      hx)
          , (λ hxar → PT.map
                        (λ { (y , (yK , hp)) → y , transport (app2 z x y) hp })
                        (hb .snd .fst x (arSubK x hxar) .snd hxar)))
    , valuesInAt-in zero (suc B) (z ∷ γ)
        (λ x y p →
          hb .snd .snd .fst x (entryK z x y zK p .fst) y (entryK z x y zK p .snd)
            (transport (sym (app2 z x y)) p))
    , hb .snd .snd .snd

  -- MACHINE TO STORY, TIED: the machine's condition reaches the
  -- K-bounded one, given z ∈ K.
  over→bnd-tied : (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
                → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
  over→bnd-tied z zK h =
      (λ x xK y yK y' y'K p q →
        svAt-out zero (z ∷ γ) (h .fst) x y y'
          (transport (app3 z x y y') p) (transport (app3' z x y y') q))
    , (λ x xK →
          (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                    (λ { (y , (yK , hp)) →
                      domAt-out zero (suc ar) (z ∷ γ) (h .snd .fst) x y
                        (transport (app2 z x y) hp) })
                    hx)
        , (λ hxar → PT.rec squash₁
                      (λ { (y , p) →
                        ∣ y , ( entryK z x y zK p .snd
                              , transport (sym (app2 z x y)) p ) ∣₁ })
                      (domAt-in zero (suc ar) (z ∷ γ) (h .snd .fst) x hxar)))
    , (λ x xK y yK p →
        valuesInAt-out zero (suc B) (z ∷ γ) (h .snd .snd .fst) x y
          (transport (app2 z x y) p))
    , h .snd .snd .snd

  -- THE OUT DIRECTION, TIED: bounded -> machine.  The first
  -- component has z ∈ E and climbs to z ∈ K by arityK and E ∈ K;
  -- the second component has z ∈ K from envInK.
  out : ⟨ γ ⊨ envSetB E ar B K ⟩ → ⟨ γ ⊨ envSetAt E ar B ⟩
  out h = extAt-in-both E φ γ
    (λ z z∈ → bnd→over-tied z (arityK (lookup E γ) z z∈ E∈K) (h .fst z z∈))
    (λ z hz → h .snd z (envInK z hz) (over→bnd-tied z (envInK z hz) hz))

  -- THE BACK DIRECTION, TIED: machine -> bounded.  Same two
  -- supplies for z ∈ K.
  back : ⟨ γ ⊨ envSetAt E ar B ⟩ → ⟨ γ ⊨ envSetB E ar B K ⟩
  back h =
      (λ z z∈ → over→bnd-tied z (arityK (lookup E γ) z z∈ E∈K) (h .fst z z∈))
    , (λ z zK hz → h .snd z (bnd→over-tied z zK hz))

  -- Every member of the ambient set is an environment, and every
  -- environment lies in K.  From the bounded condition.
  memE-bnd : ⟨ γ ⊨ envSetB E ar B K ⟩
           → (z : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩
  memE-bnd h z zE = envInK z (bnd→over-tied z (arityK (lookup E γ) z zE E∈K) (h .fst z zE))

-- =====================================================================
-- TmVal, RESTATED WITH THE TIED keyK.  Copy of
-- src/L/Condensation.lagda.md:2884-2970.  The keyK parameter is the
-- tied shape (tag satisfaction -> k ∈ K) instead of the refuted
-- unconditional k ∈ K; the in' direction applies it at the bound ht.
-- =====================================================================
module TmValTied {m : ℕ} (t e v K t0 t1 : Fin m) (γ : S ^ m) where
  t0eq : Type (ℓ-suc ℓ)
  t0eq = fst (lookup t0 γ) ≡ fst (numeralL 0)

  t1eq : Type (ℓ-suc ℓ)
  t1eq = fst (lookup t1 γ) ≡ fst (numeralL 1)

  t0K : Type (ℓ-suc ℓ)
  t0K = ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩

  keyK : Type (ℓ-suc ℓ)
  keyK = (k : S) → ⟨ (k ∷ γ) ⊨ tagAtL (suc t) 1 zero ⟩
       → ⟨ fst k ∈ fst (lookup K γ) ⟩

  num1K : Type (ℓ-suc ℓ)
  num1K = ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩

  out : t0eq → t1eq → ⟨ γ ⊨ tmValB t e v K t0 t1 ⟩ → ⟨ γ ⊨ tmValAt t e v ⟩
  out t0e t1e h = PT.rec squash₁
    (λ { (inl h1) → PT.rec squash₁
           (λ { (k , (k∈ , hz)) → PT.rec squash₁
             (λ { (z , (z∈ , (zt0 , (zt , hk)))) →
               let zt' : fst (lookup (suc (suc t)) (z ∷ k ∷ γ))
                        ≡ pr (fst z) (fst k)
                   zt' = transport (cong fst (prAtL-adequate (suc (suc t)) zero (suc zero)
                           (z ∷ k ∷ γ))) zt
                   zeq : fst z ≡ fst (lookup t1 γ)
                   zeq = zt0
                   ht-path : fst (lookup (suc (suc t)) (z ∷ k ∷ γ))
                            ≡ pr (# 1) (fst k)
                   ht-path = zt' ∙ cong₂ pr (zeq ∙ t1e) refl
                            ∙ cong₂ pr (numeralL-fst 1) refl
                   ht-sat : ⟨ (k ∷ γ) ⊨ tagAtL (suc t) 1 zero ⟩
                   ht-sat = transport (cong fst (sym (tagAtL-adequate (suc t) 1 zero (k ∷ γ))))
                              ht-path
                   hm-mem : ⟨ pr (fst k) (fst (lookup (suc (suc v)) (z ∷ k ∷ γ)))
                              ∈ fst (lookup (suc (suc e)) (z ∷ k ∷ γ)) ⟩
                   hm-mem = subst ⟨_⟩ (appAt-adequate (suc (suc e)) (suc zero) (suc (suc v))
                              (z ∷ k ∷ γ)) hk
                   hm-sat : ⟨ (k ∷ γ) ⊨ appAt (suc e) zero (suc v) ⟩
                   hm-sat = subst ⟨_⟩ (sym (appAt-adequate (suc e) zero (suc v) (k ∷ γ))) hm-mem
               in ∣ inl ∣ k , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc t) 1 zero (k ∷ γ)))
                                  ht-path
                              , hm-sat ) ∣₁ ∣₁ }) hz })
           h1
       ; (inr h2) → PT.rec squash₁
           (λ { (k , (k∈ , (kt , hc))) →
             let hc' : fst (lookup (suc t) (k ∷ γ))
                      ≡ pr (fst k) (fst (lookup (suc v) (k ∷ γ)))
                 hc' = transport (cong fst (prAtL-adequate (suc t) zero (suc v) (k ∷ γ))) hc
             in
             ∣ inr (subst ⟨_⟩ (sym (tagAtL-adequate t 0 v γ))
                      (hc' ∙ cong₂ pr kt refl ∙ cong₂ pr t0e refl ∙ cong₂ pr (numeralL-fst 0) refl)) ∣₁ }) h2 })
    h

  in' : t0eq → t1eq → t0K → keyK → num1K
      → ⟨ γ ⊨ tmValAt t e v ⟩ → ⟨ γ ⊨ tmValB t e v K t0 t1 ⟩
  in' t0e t1e t0k kk n1k h = PT.rec squash₁
    (λ { (inl h) → PT.rec squash₁
           (λ { (k , (ht , hm)) →
             let ht' : fst (lookup (suc t) (k ∷ γ)) ≡ pr (# 1) (fst k)
                 ht' = transport (cong fst (tagAtL-adequate (suc t) 1 zero (k ∷ γ))) ht
                 hm' : ⟨ pr (fst k) (fst (lookup (suc v) (k ∷ γ)))
                         ∈ fst (lookup (suc e) (k ∷ γ)) ⟩
                 hm' = subst ⟨_⟩ (appAt-adequate (suc e) zero (suc v) (k ∷ γ)) hm
             in ∣ inl (∣ k , ( kk k ht
                            , ∣ numeralL 1
                              , ( n1k
                                , ( sym t1e
                                  , ( transport (cong fst (sym (prAtL-adequate (suc (suc t))
                                         zero (suc zero) (numeralL 1 ∷ k ∷ γ))))
                                      (ht' ∙ cong₂ pr (sym (numeralL-fst 1)) refl)
                                    , subst ⟨_⟩ (sym (appAt-adequate (suc (suc e)) (suc zero)
                                         (suc (suc v)) (numeralL 1 ∷ k ∷ γ))) hm' ) ) )
                              ∣₁ ) ∣₁) ∣₁ }) h
       ; (inr h) →
           let ht : fst (lookup t γ) ≡ pr (# 0) (fst (lookup v γ))
               ht = transport (cong fst (tagAtL-adequate t 0 v γ)) h
           in ∣ inr (∣ lookup t0 γ
                 , ( t0k
                   , ( refl
                     , transport (cong fst (sym (prAtL-adequate (suc t) zero (suc v)
                          (lookup t0 γ ∷ γ))))
                         (ht ∙ cong₂ pr (sym (numeralL-fst 0)) refl ∙ cong₂ pr (sym t0e) refl) ) )
                 ∣₁) ∣₁ })
    h

-- =====================================================================
-- AtomLeaf, RESTATED WITH THE TIED keyK DERIVED.  Copy of
-- src/L/Condensation.lagda.md:3979-4140.  The refuted tmKeyK
-- parameter is replaced by arityK, aK and bK; the key membership at
-- each tmVal use is DERIVED (keyK-of) from the code slot's
-- membership, arityK, and the tag satisfaction, by the [LJ-1.99]
-- pair chain.
-- =====================================================================
module AtomLeafTied {m : ℕ} (E yc b a ar c₀ : S) (γ : S ^ m)
  (t0 t1 K : Fin m)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (bK : ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (valK : (z v w : S)
          → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
               tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc zero))
                       (suc zero) ⟩
          → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                            (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩)
  (valW : (z v w : S)
          → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
               tmValAt (suc (suc (suc (suc (suc zero)))))
                       (suc (suc zero))
                       zero ⟩
          → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩)
  (cmp : Formula S (9 + m)) where

  bodyS : Formula S (7 + m)
  bodyS = atomBodyB t0 t1 K cmp

  bodyM : Formula S (7 + m)
  bodyM = atomBody cmp

  -- The V-level pair pieces, from pairing-ax alone (the pair
  -- encoding), copied from ProbeLJ199A.ChainZ.
  b∈pair : (a b : V ℓ) → ⟨ b ∈ ⁅ a , b ⁆ ⟩
  b∈pair a b = ∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .snd
    (pairing-ax a b b .snd ∣ inr refl ∣₁)

  pair∈pr : (a b : V ℓ) → ⟨ ⁅ a , b ⁆ ∈ pr a b ⟩
  pair∈pr a b = ∈∈ₛ {a = ⁅ a , b ⁆} {b = pr a b} .snd
    (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ .snd ∣ inr refl ∣₁)

  -- THE DERIVATION: from the code slot's membership, arityK, and the
  -- tag satisfaction (the code at slot c is pr (# 1) k), the key's
  -- membership k ∈ K follows by the [LJ-1.99] pair chain.
  keyK-of : (z v w : S) (c : Fin (9 + m))
          → ⟨ fst (lookup c (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ))
              ∈ fst (lookup K γ) ⟩
          → (k : S)
          → ⟨ (k ∷ w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
               tagAtL (suc c) 1 zero ⟩
          → ⟨ fst k ∈ fst (lookup K γ) ⟩
  keyK-of z v w c cK k ht =
    let γ' : S ^ (9 + m)
        γ' = w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ
        tagEq : fst (lookup c γ') ≡ pr (# 1) (fst k)
        tagEq = transport (cong fst (tagAtL-adequate (suc c) 1 zero (k ∷ γ'))) ht
        pʟ : fst (prʟ (numeralL 1) k) ≡ pr (# 1) (fst k)
        pʟ = prʟ-fst (numeralL 1) k ∙ cong₂ pr (numeralL-fst 1) refl
        pℓ : fst (pairʟ (numeralL 1) k) ≡ ⁅ # 1 , fst k ⁆
        pℓ = pairʟ-fst (numeralL 1) k ∙ cong₂ ⁅_,_⁆ (numeralL-fst 1) refl
        pair∈K : ⟨ fst (prʟ (numeralL 1) k) ∈ fst (lookup K γ) ⟩
        pair∈K = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (tagEq ∙ sym pʟ) cK
    in arityK (pairʟ (numeralL 1) k) k
         (subst (λ w → ⟨ fst k ∈ w ⟩) (sym pℓ) (b∈pair (# 1) (fst k)))
         (arityK (prʟ (numeralL 1) k) (pairʟ (numeralL 1) k)
           (subst (λ w → ⟨ fst (pairʟ (numeralL 1) k) ∈ w ⟩) (sym pʟ)
             (subst (λ w → ⟨ w ∈ pr (# 1) (fst k) ⟩) (sym pℓ)
               (pair∈pr (# 1) (fst k))))
           pair∈K)

  -- The innermost satisfaction types at the frame.
  vK : (z v : S) → Type (ℓ-suc ℓ)
  vK z v =
    ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                      (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩

  wK : (z v w : S) → Type (ℓ-suc ℓ)
  wK z v w =
    ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                      (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩

  cSat : (z v w : S) → Type (ℓ-suc ℓ)
  cSat z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ cmp ⟩

  tVS : (z v w : S) → Type (ℓ-suc ℓ)
  tVS z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc (suc zero))))))
               (suc (suc zero))
               (suc zero)
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tWS : (z v w : S) → Type (ℓ-suc ℓ)
  tWS z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc zero)))))
               (suc (suc zero))
               zero
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tVM : (z v w : S) → Type (ℓ-suc ℓ)
  tVM z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                (suc (suc zero))
                (suc zero) ⟩

  tWM : (z v w : S) → Type (ℓ-suc ℓ)
  tWM z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc zero)))))
                (suc (suc zero))
                zero ⟩

  -- The tmVal transfers at the innermost frame, per witness pair.
  tmV-out : (z v w : S) → tVS z v w → tVM z v w
  tmV-out z v w =
    TmValTied.out {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc zero))
      (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq

  tmW-out : (z v w : S) → tWS z v w → tWM z v w
  tmW-out z v w =
    TmValTied.out {m = 9 + m}
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero))
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq

  tmV-in : (z v w : S) → tVM z v w → tVS z v w
  tmV-in z v w =
    TmValTied.in' {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc zero))
      (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z v w (suc (suc (suc (suc (suc (suc zero)))))) aK k ht)
      num1K

  tmW-in : (z v w : S) → tWM z v w → tWS z v w
  tmW-in z v w =
    TmValTied.in' {m = 9 + m}
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero))
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z v w (suc (suc (suc (suc (suc zero))))) bK k ht)
      num1K

  -- STORY TO MACHINE: drop the K-memberships and bound the witnesses.
  drop-w : (z v : S) → Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w)))
                     → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁
  drop-w z v (w , (wK , (hv , (hw , hc)))) =
    ∣ w , (tmV-out z v w hv , (tmW-out z v w hw , hc)) ∣₁

  drop-v : (z : S)
         → Σ S (λ v → vK z v × ∥ Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁)
         → ∥ Σ S (λ v → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁) ∥₁
  drop-v z (v , (vK , h)) = ∣ v , PT.rec squash₁ (drop-w z v) h ∣₁

  fwd : (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyS ⟩
                → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyM ⟩
  fwd z h = h .fst , PT.rec squash₁ (drop-v z) (h .snd)

  -- MACHINE TO STORY: add the K-memberships from the site facts.
  lift-w : (z v : S) → Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w))
                     → ∥ Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁
  lift-w z v (w , (hv , (hw , hc))) =
    ∣ w , ( valW z v w hw
          , ( tmV-in z v w hv , ( tmW-in z v w hw , hc ) ) ) ∣₁

  vK-lift : (z v : S)
          → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁
          → vK z v
  vK-lift z v h = PT.rec
    (snd (fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                          (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ))))
    (λ { (w , (hv , _)) → valK z v w hv }) h

  lift-v : (z : S)
         → Σ S (λ v → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁)
         → ∥ Σ S (λ v → vK z v × ∥ Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁) ∥₁
  lift-v z (v , h) = ∣ v , (vK-lift z v h , PT.rec squash₁ (lift-w z v) h) ∣₁

  bwd : (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyM ⟩
                → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyS ⟩
  bwd z h = h .fst , PT.rec squash₁ (lift-v z) (h .snd)

-- =====================================================================
-- THE MEM ROW, RESTATED.  Copy of MemAgree's telescope
-- (src/L/Condensation.lagda.md:4142-4185) with arityK added (KFacts
-- field, :5769-5770), the refuted tmKeyK REMOVED (its uses are
-- derived inside AtomLeafTied from arityK plus the code slot's
-- membership), entryK in the ChainZ tie (premise z ∈ K), and
-- arSubK in the tied form (premise ar ∈ K).  out and back are the
-- master's bodies with the tied EnvSet and the tied AtomLeaf.
-- =====================================================================
module MemAgreeTied {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (envK : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (entryK : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
           → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (yc b a ar c x : S) → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                       (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
           → ⟨ fst (lookup (suc (suc (suc zero))) (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))
                ∈ fst (lookup K γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                           (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
         → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                           (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = Mem.memBndAt C T B N K t0 t1

    cmp : Formula S (9 + m)
    cmp = var (suc zero) ∈̇ var zero

  out : ⟨ γ ⊨ memClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc E EK henv →
    let shD = BinaryShape.out {m} N K 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq shB
        module E' = EnvSetTied {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK entryK
                       (λ x hx → arSubK yc b a ar c x hx arK)
                       (envInK yc b a ar c E)
        hE' = E'.out henv
        hbM = h c c∈ ar a b yc shD hc E hE'
        module L = AtomLeafTied E yc b a ar c γ t0 t1 K
                     arityK aK bK
                     t0eq t1eq t0K num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
    in extAt→extAtB (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ memClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc E hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 0 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , bK)) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq
        shB = BinaryShape.in' {m} N K 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        EK = envK yc b a ar c E hE
        module E' = EnvSetTied {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK entryK
                       (λ x hx → arSubK yc b a ar c x hx arK)
                       (envInK yc b a ar c E)
        henv = E'.back hE
        module L = AtomLeafTied E yc b a ar c γ t0 t1 K
                     arityK aK bK
                     t0eq t1eq t0K num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
        hb = h c c∈ ar arK a aK b bK yc ycK shB hc E EK henv
    in extAtB→extAt (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

-- =====================================================================
-- THE SUPPLY (C-38): every tied telescope hypothesis is constructible
-- from arityK alone, so a consumer that holds KFacts (arityK at
-- src/L/Condensation.lagda.md:5769-5770) supplies the whole tied
-- telescope.  entryK is ChainZ's four-step pair chain; arSubK-tied
-- is arityK once.
-- =====================================================================
module TiesSupply {m : ℕ} (K : Fin m) (γ : S ^ m)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  module Z = ChainZ {m} K γ arityK

  -- The row's entryK in the ChainZ tie, from arityK alone.
  entryK : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
         → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
         → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩
  entryK = Z.entryK-tied-zK

  -- The row's arSubK in the tied form, from arityK once.
  arSubK-tied : (ar x : S) → ⟨ fst x ∈ fst ar ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩
              → ⟨ fst x ∈ fst (lookup K γ) ⟩
  arSubK-tied ar x hxar arK = arityK ar x hxar arK
