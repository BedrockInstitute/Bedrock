{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.304] probe.  STEPAGREE AND APPROXAGREE AT THE AMBIENT CARRIER.
--
-- THE QUESTION: [LJ-1.302] left `StepAgree` and `ApproxAgree` as the
-- last unpriced terms on `q'`'s route, calling them "mathematics, not
-- site facts: the bounded ∀̇-closure of the approximation must become
-- the unbounded one, and the witnesses must survive the change of
-- leaf".  THIS FILE measures what they cost at the ambient carrier.
--
-- WHAT IS BUILT.  Both stems, as modules at the ambient class:
--   * `StepAgree.step-agree`: the bounded step implies the machine
--     step, `extAtB`-frame against `extAt`-frame, with the leaf bridge
--     (`leafFwd`/`leafBwd`, the leaf-stem's output at ambient) and
--     three in-K site facts as parameters.  The step-level surgery is
--     the wrapper: it re-spells `GenSequence`'s own `readBody`/`fill`
--     with the bounded payload and the K-bounds.
--   * `ApproxAgree.approx-agree`: the bounded approximation implies
--     the machine one.  The first conjunct is `DomainAgree.back`
--     (imported from [LJ-1.302], measured there).  The second conjunct
--     is the bounded-to-unbounded ∀̇-closure: the appAt satisfiers
--     land in K by `entryK` (the SAME tie [LJ-1.302] supplied), then
--     the bounded instance fires, then `StepAgree` runs at the
--     shifted env.
-- The concrete site reuses [LJ-1.302]'s environment and pair lemmas:
-- f := Lset beta, a := Lset gam, K := Lset lam.  `dK` (the Def-closure
-- of the bound) and the leaf bridge stay hypotheses; their status is
-- the report's business.
--
-- The Def-step trio and the leaf content ψ stay parameters, so the
-- wrappers hold for every coding, as [LJ-1.52]'s hypotheses did.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

module LJ-1-304.ProbeLJ1304A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒟ₒ; Lset; Lset-mono; layer-trans; Lset-layer )
open Inf using ( #_; sucV )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C
import LJ-1-302.ProbeLJ1302B {ℓ} lem as B
import LJ-1-238.GenSequence
import LJ-1-302.GenDomainAgree

module A = P184.Ambient
open P1297C using ( absFull )

SC : Type (ℓ-suc ℓ)
SC = A.R.SC

-- The ambient class, the eight GenModel parameters probe D used.
module GS = LJ-1-238.GenSequence {ℓ} lem P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

module GDA = LJ-1-302.GenDomainAgree {ℓ} P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

open GDA.GM using ( appAt; appAt-adequate )

-- The ambient-class reading, the one GenSequence carries internally.
module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

toAmb : ∀ {n} (φ : Formula SC n) (γ : Vec SC n)
      → ⟨ γ ⊨ φ ⟩ → ⟨ A.ambient γ φ ⟩
toAmb φ γ = subst ⟨_⟩ (absFull φ γ)

fromAmb : ∀ {n} (φ : Formula SC n) (γ : Vec SC n)
        → ⟨ A.ambient γ φ ⟩ → ⟨ γ ⊨ φ ⟩
fromAmb φ γ = subst ⟨_⟩ (sym (absFull φ γ))

-- The Def-step trio stays a hypothesis, as in probe D; everything
-- below holds for every Def-step coding.
module Supply
  (DefAt : ∀ {n} → Fin n → Fin n → Formula SC n)
  (DefAt-in : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n)
            → fst (lookup w γ) ≡ fst X
            → fst (lookup u γ) ≡ 𝒟ₒ (fst X)
            → ⟨ γ ⊨ DefAt u w ⟩)
  (DefAt-out : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n) → GS.DefOK X
             → fst (lookup w γ) ≡ fst X
             → ⟨ γ ⊨ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst X))
  where

  module Seq = GS.Body DefAt DefAt-in DefAt-out

  -- =================================================================
  -- THE AMBIENT COPIES OF THE BOUNDED MATRICES.  Verbatim from
  -- `src/L/Condensation.lagda.md:100-101` (extAtB), `:2403-2429`
  -- (StepB) and `:2471-2476` (ApproxB), with the carrier SC.  The
  -- Δ₀ certificates are dropped: the agreement direction needs none.
  -- =================================================================
  extAtB : ∀ {n} → Fin n → Fin n → Formula SC (suc n) → Formula SC n
  extAtB y K φ = ∀̇∈ (var y) φ
              ∧̇ ∀̇∈ (var K) (φ ⇒̇ (var zero ∈̇ var (suc y)))

  leafB : ∀ {m} → Formula SC (suc (suc (suc (4 + m)))) → Fin m
        → Formula SC (4 + m)
  leafB ψ K =
    extAtB zero (suc (suc (suc (suc K))))
      (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K))))))) ψ))

  bodyB : ∀ {m} → Formula SC (suc (suc (suc (4 + m)))) → Fin m → Fin m → Fin m
        → Formula SC (4 + m)
  bodyB ψ b f K =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc b)))))
    ∧̇ ( appAt (suc (suc (suc (suc f)))) (suc (suc zero)) (suc zero)
       ∧̇ ( leafB ψ K ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  witB : ∀ {m} → Formula SC (suc (suc (suc (4 + m)))) → Fin m → Fin m → Fin m
       → Formula SC (suc m)
  witB ψ b f K =
    ∃̇∈ (var (suc b))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          (bodyB ψ b f K)))

  stepBndAt : ∀ {m} → Formula SC (suc (suc (suc (4 + m))))
            → Fin m → Fin m → Fin m → Fin m → Formula SC m
  stepBndAt ψ v b f K = extAtB v K (witB ψ b f K)

  approxBndAt : ∀ {m} → Formula SC (suc (suc (suc (6 + m))))
              → Fin m → Fin m → Fin m → Formula SC m
  approxBndAt ψ' f a K =
    GDA.domB f a K
    ∧̇ ∀̇∈ (var K)
        (∀̇∈ (var (suc K))
          (appAt (suc (suc f)) (suc zero) zero
          ⇒̇ stepBndAt ψ' zero (suc zero) (suc (suc f)) (suc (suc K))))

  -- =================================================================
  -- STEPAGREE.  The bounded step implies the machine step, at the
  -- ambient class, at an arbitrary env.  The leaf bridge and three
  -- in-K site facts are parameters: WHAT A READER MUST SUPPLY.  The
  -- rest is the wrapper this probe prices.
  -- =================================================================
  module StepAgree {m : ℕ} (ψ : Formula SC (suc (suc (suc (4 + m)))))
                   (v b f K : Fin m) (γ : SC ^ m)
    (leafFwd : (d w c z : SC)
             → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ leafB ψ K ⟩
             → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ DefAt zero (suc zero) ⟩)
    (leafBwd : (d w c z : SC)
             → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ DefAt zero (suc zero) ⟩
             → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ leafB ψ K ⟩)
    (wK : (c w : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
        → ⟨ fst w ∈ fst (lookup K γ) ⟩)
    (dK : (c w : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
        → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩)
    (zK : (c w x : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
        → ⟨ fst x ∈ 𝒟ₒ (fst w) ⟩
        → ⟨ fst x ∈ fst (lookup K γ) ⟩)
    where

    ok : Seq.PowOK b f γ
    ok c w rec = tt*

    defok : (w : SC) → GS.DefOK w
    defok w x x∈ = tt*

    -- The payload bridge, bounded to machine: drop the K-bounds, run
    -- the leaf bridge, extract d = 𝒟ₒ w.  `readBody`'s shape.
    into : (z : SC) → ⟨ (z ∷ γ) ⊨ witB ψ b f K ⟩ → ∥ Seq.StepOf b f γ z ∥₁
    into z hwit = PT.rec squash₁ viaC hwit
      where
      viaC : Σ[ c ∈ SC ] ( ⟨ fst c ∈ fst (lookup b γ) ⟩
              × ∥ Σ[ w ∈ SC ] ( ⟨ fst w ∈ fst (lookup K γ) ⟩
              × ∥ Σ[ d ∈ SC ] ( ⟨ fst d ∈ fst (lookup K γ) ⟩
              × ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ bodyB ψ b f K ⟩ ) ∥₁ ) ∥₁ )
           → ∥ Seq.StepOf b f γ z ∥₁
      viaC (c , (_ , hc)) = PT.rec squash₁ (viaW c) hc
        where
        viaW : (c : SC) → Σ[ w ∈ SC ] ( ⟨ fst w ∈ fst (lookup K γ) ⟩
               × ∥ Σ[ d ∈ SC ] ( ⟨ fst d ∈ fst (lookup K γ) ⟩
               × ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ bodyB ψ b f K ⟩ ) ∥₁ )
             → ∥ Seq.StepOf b f γ z ∥₁
        viaW c (w , (_ , hw)) = PT.rec squash₁ (viaD c w) hw
          where
          viaD : (c w : SC) → Σ[ d ∈ SC ] ( ⟨ fst d ∈ fst (lookup K γ) ⟩
                 × ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ bodyB ψ b f K ⟩ )
               → ∥ Seq.StepOf b f γ z ∥₁
          viaD c w (d , _ , (hcb , (happ , (hleaf , hzin)))) =
            ∣ (c , (w , ((hcb , happr) , hzout))) ∣₁
            where
            happr : ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
            happr = subst ⟨_⟩ (appAt-adequate
              (suc (suc (suc (suc f)))) (suc (suc zero)) (suc zero)
              (d ∷ w ∷ c ∷ z ∷ γ)) happ

            qd : fst d ≡ 𝒟ₒ (fst w)
            qd = DefAt-out w zero (suc zero) (d ∷ w ∷ c ∷ z ∷ γ)
              (defok w) refl (leafFwd d w c z hleaf)

            hzout : ⟨ fst z ∈ 𝒟ₒ (fst w) ⟩
            hzout = subst (λ X → ⟨ fst z ∈ X ⟩) qd hzin

    -- The payload bridge, machine to bounded: rebuild the K-bounds
    -- from the site facts, run the leaf bridge backwards.  `fill`'s
    -- shape.
    fill : (z : SC) → Seq.StepOf b f γ z → ⟨ (z ∷ γ) ⊨ witB ψ b f K ⟩
    fill z (c , (w , ((hcb , hpair) , hzin))) =
      ∣ (c , (hcb , ∣ (w , (wK c w hpair ,
        ∣ (D , (dK c w hpair ,
          (hcb , (happ , (leafBwd D w c z hdef , hzinD))))) ∣₁)) ∣₁)) ∣₁
      where
      D : SC
      D = 𝒟ₒ (fst w) , tt*

      happ : ⟨ (D ∷ w ∷ c ∷ z ∷ γ) ⊨
                appAt (suc (suc (suc (suc f)))) (suc (suc zero)) (suc zero) ⟩
      happ = subst ⟨_⟩ (sym (appAt-adequate
        (suc (suc (suc (suc f)))) (suc (suc zero)) (suc zero)
        (D ∷ w ∷ c ∷ z ∷ γ))) hpair

      hdef : ⟨ (D ∷ w ∷ c ∷ z ∷ γ) ⊨ DefAt zero (suc zero) ⟩
      hdef = DefAt-in w zero (suc zero) (D ∷ w ∷ c ∷ z ∷ γ) refl refl

      hzinD : ⟨ fst z ∈ fst D ⟩
      hzinD = hzin

    -- THE STEM.  The bounded frame reaches the machine frame: the two
    -- outer halves are the bounded frame's own projections, with the
    -- payload bridges spliced in and zK closing the .snd direction.
    step-agree : ⟨ γ ⊨ stepBndAt ψ v b f K ⟩
               → ⟨ γ ⊨ Seq.StepAt v b f ⟩
    step-agree h = Seq.StepAt-in v b f γ ok
      (λ z z∈ → into z (h .fst z z∈))
      (λ z s → h .snd z (zK-step z s) (fill z s))
      where
      zK-step : (z : SC) → Seq.StepOf b f γ z
              → ⟨ fst z ∈ fst (lookup K γ) ⟩
      zK-step z (c , (w , ((_ , hpair) , hzin))) = zK c w z hpair hzin

  -- =================================================================
  -- APPROXAGREE.  The bounded approximation implies the machine one.
  -- The first conjunct is `DomainAgree.back`.  The second is the
  -- bounded-to-unbounded ∀̇-closure: entryK moves the appAt satisfiers
  -- into K, the bounded instance fires, StepAgree runs at the shifted
  -- env.  The leaf bridge and the in-K facts are stated AT THE SHIFTED
  -- ENV's slots, which is the base env's slots; they carry no binder
  -- dependence.
  -- =================================================================
  module ApproxAgree {m : ℕ} (ψ' : Formula SC (suc (suc (suc (6 + m)))))
                     (f a K : Fin m) (γ : SC ^ m)
    (leafFwd : (d w c z y x : SC)
             → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ γ) ⊨
                   leafB ψ' (suc (suc K)) ⟩
             → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ γ) ⊨ DefAt zero (suc zero) ⟩)
    (leafBwd : (d w c z y x : SC)
             → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ γ) ⊨ DefAt zero (suc zero) ⟩
             → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ γ) ⊨
                   leafB ψ' (suc (suc K)) ⟩)
    (wK : (c w : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
        → ⟨ fst w ∈ fst (lookup K γ) ⟩)
    (dK : (c w : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
        → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩)
    (zK : (c w x : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
        → ⟨ fst x ∈ 𝒟ₒ (fst w) ⟩
        → ⟨ fst x ∈ fst (lookup K γ) ⟩)
    (domAgree : ⟨ γ ⊨ GDA.domB f a K ⟩ → ⟨ γ ⊨ GDA.GM.domAt f a ⟩)
    (entryK : (c z : SC) → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
            → ⟨ fst c ∈ fst (lookup K γ) ⟩
              × ⟨ fst z ∈ fst (lookup K γ) ⟩)
    where

    -- THE ∀̇-CLOSURE.  Arbitrary c z with a recorded pair: entryK
    -- lands them in K, the bounded implication fires, StepAgree lifts.
    closure : (c z : SC) → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
            → ⟨ γ ⊨ approxBndAt ψ' f a K ⟩
            → ⟨ (z ∷ c ∷ γ) ⊨ Seq.StepAt zero (suc zero) (suc (suc f)) ⟩
    closure c z hpair h =
      StepAgree.step-agree ψ' zero (suc zero) (suc (suc f)) (suc (suc K))
        (z ∷ c ∷ γ)
        (λ d w c' z' → leafFwd d w c' z' z c)
        (λ d w c' z' → leafBwd d w c' z' z c)
        wK dK zK
        (h .snd c (entryK c z hpair .fst) z (entryK c z hpair .snd) happ)
      where
      happ : ⟨ (z ∷ c ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
      happ = subst ⟨_⟩ (sym (appAt-adequate
        (suc (suc f)) (suc zero) zero (z ∷ c ∷ γ))) hpair

    approx-agree : ⟨ γ ⊨ approxBndAt ψ' f a K ⟩
                 → ⟨ γ ⊨ Seq.ApproxAt f a ⟩
    approx-agree h = Seq.ApproxAt-in f a γ (domAgree (h .fst))
      (λ c z hpair → closure c z hpair h)

  -- =================================================================
  -- THE CONCRETE SITE.  [LJ-1.302]'s environment and pair lemmas,
  -- reused by import: f := Lset beta, a := Lset gam, K := Lset lam.
  -- entryK, wK and the domain conjunct are TERMS from the same
  -- delivered lemmas [LJ-1.302] measured.  dK and the leaf bridge
  -- stay hypotheses; zK derives from dK and the stage's transitivity.
  -- =================================================================
  two : Fin 5
  two = suc (suc zero)

  four : Fin 5
  four = suc (suc (suc (suc zero)))

  module Site (ψs : Formula SC (suc (suc (suc (6 + 3)))))
              (lam beta gam : V ℓ)
              (beta∈λ : ⟨ beta ∈ lam ⟩) (gam∈λ : ⟨ gam ∈ lam ⟩)
              (dK : (c w : SC) → ⟨ pr (fst c) (fst w) ∈ Lset beta ⟩
                  → ⟨ 𝒟ₒ (fst w) ∈ Lset lam ⟩)
              (leafFwd : (d w c z y x : SC)
                       → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷
                             (Lset beta , tt*) ∷ (Lset gam , tt*) ∷
                             (Lset lam , tt*) ∷ []) ⊨ leafB ψs four ⟩
                       → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷
                             (Lset beta , tt*) ∷ (Lset gam , tt*) ∷
                             (Lset lam , tt*) ∷ []) ⊨ DefAt zero (suc zero) ⟩)
              (leafBwd : (d w c z y x : SC)
                       → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷
                             (Lset beta , tt*) ∷ (Lset gam , tt*) ∷
                             (Lset lam , tt*) ∷ []) ⊨ DefAt zero (suc zero) ⟩
                       → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷
                             (Lset beta , tt*) ∷ (Lset gam , tt*) ∷
                             (Lset lam , tt*) ∷ []) ⊨ leafB ψs four ⟩)
    where

    module S302 = B.Supply lam beta gam beta∈λ gam∈λ

    env : SC ^ 3
    env = S302.env

    wK' : (c w : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup zero env) ⟩
        → ⟨ fst w ∈ fst (lookup (suc (suc zero)) env) ⟩
    wK' c w h = S302.entryK c w h .snd

    zK' : (c w x : SC) → ⟨ pr (fst c) (fst w) ∈ fst (lookup zero env) ⟩
        → ⟨ fst x ∈ 𝒟ₒ (fst w) ⟩
        → ⟨ fst x ∈ fst (lookup (suc (suc zero)) env) ⟩
    zK' c w x h hx =
      layer-trans (Lset-layer lam) hx (dK c w h)

    -- BOTH STEMS, AT THE SITE, WITH EVERY OBLIGATION A TERM OR A NAMED
    -- HYPOTHESIS.
    module Appr = ApproxAgree ψs zero (suc zero) (suc (suc zero)) env
      leafFwd leafBwd wK' dK zK' S302.DA.back S302.entryK

    -- The headlines, at the ambient reading.
    approx-agree-amb : ⟨ A.ambient env
                          (approxBndAt ψs zero (suc zero) (suc (suc zero))) ⟩
                     → ⟨ A.ambient env (Seq.ApproxAt zero (suc zero)) ⟩
    approx-agree-amb h = toAmb (Seq.ApproxAt zero (suc zero)) env
      (Appr.approx-agree
        (fromAmb (approxBndAt ψs zero (suc zero) (suc (suc zero))) env h))

    step-agree-amb : (z c : SC)
      → ⟨ A.ambient (z ∷ c ∷ env)
           (stepBndAt ψs zero (suc zero) two four) ⟩
      → ⟨ A.ambient (z ∷ c ∷ env) (Seq.StepAt zero (suc zero) two) ⟩
    step-agree-amb z c h =
      toAmb (Seq.StepAt zero (suc zero) two) (z ∷ c ∷ env)
        (StepAgree.step-agree ψs zero (suc zero) two four (z ∷ c ∷ env)
          (λ d w c' z' → leafFwd d w c' z' z c)
          (λ d w c' z' → leafBwd d w c' z' z c)
          wK' dK zK'
          (fromAmb (stepBndAt ψs zero (suc zero) two four) (z ∷ c ∷ env) h))
