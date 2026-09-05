{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.162 probe A.  LEG 3 OF `CrossOut`, WITH THE BOUNDED GRAPH.
--
-- [LJ-1.161] split `CrossOut` into three legs and measured two.  Leg 3
-- is Devlin's step (a): from the transferred AMBIENT reading, derive
-- `v ≡ Lset b`.  It was open because the delivered `Lset-only`
-- (src/L/Hierarchy.lagda.md:334) wants the INNER reading at the L class
-- of the UNBOUNDED graph, and no Levy witness for `LsetGraphAt` exists.
--
-- THE REPAIR THE BRIEF NAMES: the bounded graph `GraphB.graphBndAt`
-- with its `Δ₀` certificate, src/L/Condensation.lagda.md:2489-2493.
--
-- CRITERION, FIXED BEFORE THE RUN (D-1): GO at or below 60 in-fence
-- lines for LEG 3 ALONE; 20 minutes of wall time per agda invocation
-- under GHCRTS="-A64m -I0 -M8g", one process, cap never raised.
--
-- BLOCK 0 is the generic quantifier kit.  BLOCK 1 is the leg.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-162.ProbeLJ1162A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; Lset; IsOrd )
open import L.Coding.Model {ℓ} using ( extAt; appAt; appAt-adequate; domAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt; DefBody )
open import L.Coding.Sequence {ℓ} lem using
  ( StepAt; StepBody; ApproxAt; LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import L.Condensation {ℓ} lem using
  ( extAtB; extAtB→extAt; extAt→extAtB; domB
  ; module StepB; module StepAtB; module ApproxB; module GraphB
  ; module DomainAgree )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( map; lookup; _∷_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- BLOCK 0.  THE GENERIC QUANTIFIER KIT.  Template: no tower name.
-- A bounded existential reaches the unbounded one for free; the
-- unbounded one reaches the bounded one exactly when its witness is
-- shown to lie in the bound.
-- =====================================================================

∃∈-up : ∀ {n} (K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
      → ((x : S) → ⟨ (x ∷ γ) ⊨ φB ⟩ → ⟨ (x ∷ γ) ⊨ φ ⟩)
      → ⟨ γ ⊨ ∃̇∈ (var K) φB ⟩ → ⟨ γ ⊨ ∃̇ φ ⟩
∃∈-up K φB φ γ f = PT.map (λ { (x , (_ , h)) → x , f x h })

∃-down : ∀ {n} (K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
       → ((x : S) → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩)
       → ((x : S) → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ (x ∷ γ) ⊨ φB ⟩)
       → ⟨ γ ⊨ ∃̇ φ ⟩ → ⟨ γ ⊨ ∃̇∈ (var K) φB ⟩
∃-down K φB φ γ k f = PT.map (λ { (x , h) → x , (k x h , f x h) })

-- =====================================================================
-- BLOCK 1.  LEG 3.  THE BOUNDED GRAPH AGAINST THE DELIVERED ONE.
--
-- `extAt` is an EXTENSIONALITY ("the set at y is EXACTLY the satisfiers
-- of phi"), so the delivered `extAtB→extAt`
-- (src/L/Condensation.lagda.md:2511) consumes `fwd` AND `bwd` AND a
-- membership fact.  Every frame below therefore pays TWO directions.
-- =====================================================================

-- The leaf frame: `StepB.leafB` against the delivered `DefAt`.
module Leaf {m : ℕ} (ψ : Formula S (suc (suc (suc (4 + m)))))
  (v b f K : Fin m) (δ : S ^ (4 + m))
  (ψ-up : (x a d : S) → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ ψ ⟩
        → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩)
  (ψ-down : (x a d : S) → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
          → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ ψ ⟩)
  (envK : (x a : S) → ⟨ (a ∷ x ∷ δ) ⊨ ∃̇ (DefBody (suc zero)) ⟩
        → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc K)))) δ) ⟩)
  (codeK : (x a d : S) → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc (suc K)))) δ) ⟩)
  (memK : (x : S) → ⟨ (x ∷ δ) ⊨ ∃̇ (∃̇ (DefBody (suc zero))) ⟩
        → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc K)))) δ) ⟩)
  where
  module SB = StepB {m} ψ v b f K

  K₅ : Fin (suc (4 + m))
  K₅ = suc (suc (suc (suc (suc K))))
  K₆ : Fin (suc (suc (4 + m)))
  K₆ = suc K₅
  ΨB : Formula S (suc (suc (4 + m)))
  ΨB = ∃̇∈ (var K₆) ψ
  Ψ : Formula S (suc (suc (4 + m)))
  Ψ = ∃̇ (DefBody (suc zero))
  ΦB : Formula S (suc (4 + m))
  ΦB = ∃̇∈ (var K₅) ΨB
  Φ : Formula S (suc (4 + m))
  Φ = ∃̇ Ψ

  fwd : (x : S) → ⟨ (x ∷ δ) ⊨ ΦB ⟩ → ⟨ (x ∷ δ) ⊨ Φ ⟩
  fwd x = ∃∈-up K₅ ΨB Ψ (x ∷ δ)
            (λ a → ∃∈-up K₆ ψ (DefBody (suc zero)) (a ∷ x ∷ δ) (ψ-up x a))

  bwd : (x : S) → ⟨ (x ∷ δ) ⊨ Φ ⟩ → ⟨ (x ∷ δ) ⊨ ΦB ⟩
  bwd x = ∃-down K₅ ΨB Ψ (x ∷ δ) (envK x)
            (λ a → ∃-down K₆ ψ (DefBody (suc zero)) (a ∷ x ∷ δ)
                     (codeK x a) (ψ-down x a))

  up : ⟨ δ ⊨ SB.leafB ⟩ → ⟨ δ ⊨ DefAt zero (suc zero) ⟩
  up = extAtB→extAt zero (suc (suc (suc (suc K)))) ΦB Φ δ fwd bwd memK

  down : ⟨ δ ⊨ DefAt zero (suc zero) ⟩ → ⟨ δ ⊨ SB.leafB ⟩
  down = extAt→extAtB zero (suc (suc (suc (suc K)))) ΦB Φ δ fwd bwd

-- The step frame: `StepB.stepBndAt` against the delivered `StepAt`.
-- The three bounded existentials are the argument (bounded by b, free),
-- the recorded value (bounded by K) and its DEFINABLE POWER (bounded by
-- K).  The third bound is the one nothing in `src/` supplies.
module Step {m : ℕ} (ψ : Formula S (suc (suc (suc (4 + m)))))
  (v b f K : Fin m) (γ : S ^ m)
  (leaf-up : (δ : S ^ (4 + m)) → ⟨ δ ⊨ StepB.leafB {m} ψ v b f K ⟩
           → ⟨ δ ⊨ DefAt zero (suc zero) ⟩)
  (leaf-down : (δ : S ^ (4 + m)) → ⟨ δ ⊨ DefAt zero (suc zero) ⟩
             → ⟨ δ ⊨ StepB.leafB {m} ψ v b f K ⟩)
  (valK : (z c u : S) → ⟨ (u ∷ c ∷ z ∷ γ) ⊨ ∃̇ (StepBody b f) ⟩
        → ⟨ fst u ∈ fst (lookup K γ) ⟩)
  (powK : (z c u d : S) → ⟨ (d ∷ u ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩
        → ⟨ fst d ∈ fst (lookup K γ) ⟩)
  (stepK : (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody b f))) ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  module SB = StepB {m} ψ v b f K

  W₃ : Formula S (suc (suc (suc m)))
  W₃ = ∃̇∈ (var (suc (suc (suc K)))) SB.bodyB
  U₃ : Formula S (suc (suc (suc m)))
  U₃ = ∃̇ (StepBody b f)
  W₂ : Formula S (suc (suc m))
  W₂ = ∃̇∈ (var (suc (suc K))) W₃
  U₂ : Formula S (suc (suc m))
  U₂ = ∃̇ U₃
  U₁ : Formula S (suc m)
  U₁ = ∃̇ U₂

  bodyUp : (z c u d : S) → ⟨ (d ∷ u ∷ c ∷ z ∷ γ) ⊨ SB.bodyB ⟩
         → ⟨ (d ∷ u ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩
  bodyUp z c u d (hc , (ha , (hl , hz))) =
    hc , (ha , (leaf-up (d ∷ u ∷ c ∷ z ∷ γ) hl , hz))

  bodyDown : (z c u d : S) → ⟨ (d ∷ u ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩
           → ⟨ (d ∷ u ∷ c ∷ z ∷ γ) ⊨ SB.bodyB ⟩
  bodyDown z c u d (hc , (ha , (hl , hz))) =
    hc , (ha , (leaf-down (d ∷ u ∷ c ∷ z ∷ γ) hl , hz))

  argB : (z c : S) → ⟨ (c ∷ z ∷ γ) ⊨ U₂ ⟩ → ⟨ fst c ∈ fst (lookup b γ) ⟩
  argB z c = PT.rec (snd (fst c ∈ fst (lookup b γ)))
    (λ { (u , hu) → PT.rec (snd (fst c ∈ fst (lookup b γ)))
      (λ { (d , (hc , _)) → hc }) hu })

  witUp : (z : S) → ⟨ (z ∷ γ) ⊨ SB.witB ⟩ → ⟨ (z ∷ γ) ⊨ U₁ ⟩
  witUp z = ∃∈-up (suc b) W₂ U₂ (z ∷ γ)
    (λ c → ∃∈-up (suc (suc K)) W₃ U₃ (c ∷ z ∷ γ)
      (λ u → ∃∈-up (suc (suc (suc K))) SB.bodyB (StepBody b f)
               (u ∷ c ∷ z ∷ γ) (bodyUp z c u)))

  witDown : (z : S) → ⟨ (z ∷ γ) ⊨ U₁ ⟩ → ⟨ (z ∷ γ) ⊨ SB.witB ⟩
  witDown z = ∃-down (suc b) W₂ U₂ (z ∷ γ) (argB z)
    (λ c → ∃-down (suc (suc K)) W₃ U₃ (c ∷ z ∷ γ) (valK z c)
      (λ u → ∃-down (suc (suc (suc K))) SB.bodyB (StepBody b f)
               (u ∷ c ∷ z ∷ γ) (powK z c u) (bodyDown z c u)))

  up : ⟨ γ ⊨ SB.stepBndAt ⟩ → ⟨ γ ⊨ StepAt v b f ⟩
  up = extAtB→extAt v K SB.witB U₁ γ witUp witDown stepK

-- The approximation frame.  The two bounded universals reach the two
-- unbounded ones through the entry site fact; the domain conjunct is
-- the delivered `DomainAgree.back`.
module Approx {m : ℕ} (ψ' : Formula S (suc (suc (suc (6 + m)))))
  (f a K : Fin m) (γ : S ^ m)
  (step-up : (c z : S)
           → ⟨ (z ∷ c ∷ γ) ⊨ StepB.stepBndAt {2 + m} ψ' zero (suc zero)
                                (suc (suc f)) (suc (suc K)) ⟩
           → ⟨ (z ∷ c ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc f)) ⟩)
  (entryK : (c z : S) → ⟨ (z ∷ c ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
          → ⟨ fst c ∈ fst (lookup K γ) ⟩ × ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (dom-back : ⟨ γ ⊨ domB f a K ⟩ → ⟨ γ ⊨ domAt f a ⟩)
  where
  up : ⟨ γ ⊨ ApproxB.approxBndAt {m} ψ' f a K ⟩ → ⟨ γ ⊨ ApproxAt f a ⟩
  up (hd , hq) = dom-back hd
    , λ c z ap → step-up c z
        (hq c (entryK c z ap .fst) z (entryK c z ap .snd) ap)

-- The graph frame.  The bounded existential reaches the unbounded one
-- for free; the two conjuncts are the two frames above.
module Graph {m : ℕ} (ψs : Formula S (suc (suc (suc (5 + m)))))
  (ψa : Formula S (suc (suc (suc (7 + m)))))
  (w b K : Fin m) (γ : S ^ m)
  (approx-up : (h : S)
             → ⟨ (h ∷ γ) ⊨ ApproxB.approxBndAt {1 + m} ψa zero (suc b) (suc K) ⟩
             → ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩)
  (step-up : (h : S)
           → ⟨ (h ∷ γ) ⊨ StepB.stepBndAt {1 + m} ψs (suc w) (suc b) zero (suc K) ⟩
           → ⟨ (h ∷ γ) ⊨ StepAt (suc w) (suc b) zero ⟩)
  where
  up : ⟨ γ ⊨ GraphB.graphBndAt {m} ψs ψa w b K ⟩ → ⟨ γ ⊨ LsetGraphAt w b ⟩
  up = ∃∈-up K (ApproxB.approxBndAt {1 + m} ψa zero (suc b) (suc K)
               ∧̇ StepB.stepBndAt {1 + m} ψs (suc w) (suc b) zero (suc K))
              (ApproxAt zero (suc b) ∧̇ StepAt (suc w) (suc b) zero) γ
              (λ h hh → approx-up h (hh .fst) , step-up h (hh .snd))

-- LEG 3.  From the AMBIENT reading of the bounded graph to `v ≡ Lset b`.
-- The bounded graph is Δ₀, so `abs₀` carries the ambient reading back
-- into L for free, and the delivered `Lset-only` finishes.
module Leg3 {m : ℕ} (ψs : Formula S (suc (suc (suc (5 + m)))))
  (ψa : Formula S (suc (suc (suc (7 + m)))))
  (w b K : Fin m) (γ : S ^ m) (ds : Δ₀ ψs) (da : Δ₀ ψa)
  (graph-up : ⟨ γ ⊨ GraphB.graphBndAt {m} ψs ψa w b K ⟩
            → ⟨ γ ⊨ LsetGraphAt w b ⟩)
  where
  leg3 : ⟨ map fst γ ⊨ᵛ GraphB.graphBndAt {m} ψs ψa w b K ⟩
       → IsOrd (fst (lookup b γ))
       → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
  leg3 h = Lset-only w b γ (graph-up
    (subst ⟨_⟩ (sym (abs₀ (GraphB.Δ₀-graphBndAt {m} ψs ψa w b K ds da) γ)) h))

-- =====================================================================
-- BLOCK 2.  C-38.  THE FRAMES FEED EACH OTHER.  Nothing above is an
-- interface waiting for a supplier: the leaf frame supplies the step
-- frame's two leaf directions, and the step frame supplies the graph
-- frame's two step directions.
-- =====================================================================

module StepWired {m : ℕ} (ψ : Formula S (suc (suc (suc (4 + m)))))
  (v b f K : Fin m) (γ : S ^ m)
  (ψ-up : (δ : S ^ (4 + m)) (x a d : S) → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ ψ ⟩
        → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩)
  (ψ-down : (δ : S ^ (4 + m)) (x a d : S)
          → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
          → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ ψ ⟩)
  (envK : (δ : S ^ (4 + m)) (x a : S) → ⟨ (a ∷ x ∷ δ) ⊨ ∃̇ (DefBody (suc zero)) ⟩
        → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc K)))) δ) ⟩)
  (codeK : (δ : S ^ (4 + m)) (x a d : S)
         → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc (suc K)))) δ) ⟩)
  (memK : (δ : S ^ (4 + m)) (x : S) → ⟨ (x ∷ δ) ⊨ ∃̇ (∃̇ (DefBody (suc zero))) ⟩
        → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc K)))) δ) ⟩)
  (valK : (z c u : S) → ⟨ (u ∷ c ∷ z ∷ γ) ⊨ ∃̇ (StepBody b f) ⟩
        → ⟨ fst u ∈ fst (lookup K γ) ⟩)
  (powK : (z c u d : S) → ⟨ (d ∷ u ∷ c ∷ z ∷ γ) ⊨ StepBody b f ⟩
        → ⟨ fst d ∈ fst (lookup K γ) ⟩)
  (stepK : (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (StepBody b f))) ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  module LF (δ : S ^ (4 + m)) =
    Leaf {m} ψ v b f K δ (ψ-up δ) (ψ-down δ) (envK δ) (codeK δ) (memK δ)
  module ST = Step {m} ψ v b f K γ (λ δ → LF.up δ) (λ δ → LF.down δ)
                valK powK stepK

  up : ⟨ γ ⊨ StepB.stepBndAt {m} ψ v b f K ⟩ → ⟨ γ ⊨ StepAt v b f ⟩
  up = ST.up

-- C-38 AT THE REAL LEAF FORMULA.  `StepAtB`
-- (src/L/Condensation.lagda.md:2441-2454) fixes the leaf content to
-- `DefBodyB`.  `Leaf` accepts it at the same arity, so the two
-- directions it asks for are exactly `LeafAgree.back` and
-- `LeafAgree.out` (:7133-7145) at the same environment.
module LeafAtDefBody {n : ℕ} (v b f : Fin n)
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where
  module SA = StepAtB {n} v b f N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1

  module LD (δ : S ^ (4 + suc n))
    (ψ-up : (x a d : S) → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ SA.ψ ⟩
          → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩)
    (ψ-down : (x a d : S) → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
            → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ SA.ψ ⟩)
    (envK : (x a : S) → ⟨ (a ∷ x ∷ δ) ⊨ ∃̇ (DefBody (suc zero)) ⟩
          → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc zero)))) δ) ⟩)
    (codeK : (x a d : S) → ⟨ (d ∷ a ∷ x ∷ δ) ⊨ DefBody (suc zero) ⟩
           → ⟨ fst d ∈ fst (lookup (suc (suc (suc (suc zero)))) δ) ⟩)
    (memK : (x : S) → ⟨ (x ∷ δ) ⊨ ∃̇ (∃̇ (DefBody (suc zero))) ⟩
          → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc zero)))) δ) ⟩)
    = Leaf {suc n} SA.ψ (suc v) (suc b) (suc f) zero δ
        ψ-up ψ-down envK codeK memK
