{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.83] probe A: SUPPLY THE CODE SET AND THE DECOMPOSITION FACTS.
--
-- The chain's first unsupplied hypothesis was ShapesAgree's code-set
-- datum: the value C and the facts compK/unCompK
-- (L.Condensation.lagda.md:5816-5835).  This probe supplies all three
-- at the stage: C = K (the stage's own bound), and the facts by the
-- stage's transitivity.  It then instantiates the chain through
-- ClosedAgree and ShapedAgree, and stops at WitnessAgree, whose witK
-- fact no stage datum supplies.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ183A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; layer-trans; Lset-layer )
open import L.Condensation {ℓ} lem using
  ( module KFactsNS; KFactsCons; module ShapesAgree; module ShapedAgree
  ; module ClosedAgree; module WitnessAgree )
open import L.Coding.Base {ℓ} using ( ∈sgl-intro; ∈pair-introL; ∈pair-introR )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )
import FOL.Absoluteness
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ⁅_,_⁆; ⁅_⁆s )
open InfinitySet using ( ω; sucV; #_ )
open import V.Coding {ℓ} using ( pr )
import ProbeLJ180A

module P180 = ProbeLJ180A {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
open KFactsNS

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- =====================================================================
-- THE GENERIC CORE.  The code facts at ANY transitive set T: a code
-- (or a Kuratowski pair) whose members lie in T has its components in
-- T, because each component is a member of a member of ... of the
-- code, and T is transitive.  The stage instantiates T = fst K with
-- layer-trans (Lset-layer lam); the J tower instantiates with its own
-- stage's transitivity.  This is the DD4 shape: one core, both towers.
-- =====================================================================
module CodeFacts (T : V ℓ) (transT : {x y : V ℓ} → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ T ⟩ → ⟨ x ∈ˢ T ⟩) where

  sgl : (x : V ℓ) → ⟨ x ∈ˢ ⁅ x ⁆s ⟩
  sgl x = ∈sgl-intro refl

  pairL : (u v : V ℓ) → ⟨ u ∈ˢ ⁅ u , v ⁆ ⟩
  pairL u v = ∈pair-introL refl

  pairR : (u v : V ℓ) → ⟨ v ∈ˢ ⁅ u , v ⁆ ⟩
  pairR u v = ∈pair-introR refl

  -- c = pr N (pr #k (pr a b)):  N is two membership steps down from c
  -- ({N} between), a and b are six steps down.  Each step is one
  -- transitivity application.
  compK : (k : ℕ) (c' N a b : Sʟ)
        → ⟨ fst c' ∈ˢ T ⟩
        → fst c' ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
        → ⟨ fst N ∈ˢ T ⟩ × ⟨ fst a ∈ˢ T ⟩ × ⟨ fst b ∈ˢ T ⟩
  compK k c' N a b c'∈T shape = nK , aK , bK
    where
    n : V ℓ
    n = fst N
    aa : V ℓ
    aa = fst a
    bb : V ℓ
    bb = fst b
    kk : V ℓ
    kk = # k
    Y : V ℓ
    Y = pr aa bb
    X : V ℓ
    X = pr kk Y
    cK : ⟨ pr n X ∈ˢ T ⟩
    cK = subst (λ w → ⟨ w ∈ˢ T ⟩) shape c'∈T
    nK : ⟨ n ∈ˢ T ⟩
    nK = transT (sgl n) (transT (pairL (⁅ n ⁆s) (⁅ n , X ⁆)) cK)
    aK : ⟨ aa ∈ˢ T ⟩
    aK = transT (pairL aa bb)
           (transT (pairR (⁅ aa ⁆s) (⁅ aa , bb ⁆))
             (transT (pairR kk Y)
               (transT (pairR (⁅ kk ⁆s) (⁅ kk , Y ⁆))
                 (transT (pairR n X)
                   (transT (pairR (⁅ n ⁆s) (⁅ n , X ⁆)) cK)))))
    bK : ⟨ bb ∈ˢ T ⟩
    bK = transT (pairR aa bb)
           (transT (pairR (⁅ aa ⁆s) (⁅ aa , bb ⁆))
             (transT (pairR kk Y)
               (transT (pairR (⁅ kk ⁆s) (⁅ kk , Y ⁆))
                 (transT (pairR n X)
                   (transT (pairR (⁅ n ⁆s) (⁅ n , X ⁆)) cK)))))

  -- c = pr N (pr #k a):  N two steps down, a four steps down.
  unCompK : (k : ℕ) (c' N a : Sʟ)
          → ⟨ fst c' ∈ˢ T ⟩
          → fst c' ≡ pr (fst N) (pr (# k) (fst a))
          → ⟨ fst N ∈ˢ T ⟩ × ⟨ fst a ∈ˢ T ⟩
  unCompK k c' N a c'∈T shape = nK , aK
    where
    n : V ℓ
    n = fst N
    aa : V ℓ
    aa = fst a
    kk : V ℓ
    kk = # k
    X : V ℓ
    X = pr kk aa
    cK : ⟨ pr n X ∈ˢ T ⟩
    cK = subst (λ w → ⟨ w ∈ˢ T ⟩) shape c'∈T
    nK : ⟨ n ∈ˢ T ⟩
    nK = transT (sgl n) (transT (pairL (⁅ n ⁆s) (⁅ n , X ⁆)) cK)
    aK : ⟨ aa ∈ˢ T ⟩
    aK = transT (pairR kk aa)
           (transT (pairR (⁅ kk ⁆s) (⁅ kk , aa ⁆))
             (transT (pairR n X)
               (transT (pairR (⁅ n ⁆s) (⁅ n , X ⁆)) cK)))

  -- A pair in T has its components in T:  x ∈ {x} ∈ pr x y ∈ T,
  -- y ∈ {x,y} ∈ pr x y ∈ T.
  entryK : (x y : Sʟ) → ⟨ pr (fst x) (fst y) ∈ˢ T ⟩
         → ⟨ fst x ∈ˢ T ⟩ × ⟨ fst y ∈ˢ T ⟩
  entryK x y h =
    ( transT (sgl (fst x)) (transT (pairL (⁅ fst x ⁆s) (⁅ fst x , fst y ⁆)) h)
    , transT (pairR (fst x) (fst y))
        (transT (pairR (⁅ fst x ⁆s) (⁅ fst x , fst y ⁆)) h) )

-- =====================================================================
-- THE STAGE.  Same seven parameters as ProbeLJ180A.StageKFacts and
-- ProbeLJ182A.Stage.  The code set is the stage's own K.
-- =====================================================================
module Stage
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (α : S) (ordα : IsOrd α) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  where

  module SK = P180.StageKFacts lam ordλ succλ α ordα α∈λ α∉ω
  open SK using ( K; A; γ; A₀; K₀; Nk; kfacts )

  -- The twelve numeral slots of the frame (Fin 14, constructor form).
  N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin 14
  N0 = Nk zero
  N1 = Nk (suc zero)
  N2 = Nk (suc (suc zero))
  N3 = Nk (suc (suc (suc zero)))
  N4 = Nk (suc (suc (suc (suc zero))))
  N5 = Nk (suc (suc (suc (suc (suc zero)))))
  N6 = Nk (suc (suc (suc (suc (suc (suc zero))))))
  N7 = Nk (suc (suc (suc (suc (suc (suc (suc zero)))))))
  N8 = Nk (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  N9 = Nk (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  N10 = Nk (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  N11 = Nk (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

  -- THE CODE SET: the stage's own bound K.
  C : Sʟ
  C = K

  -- The facts, at T = fst K, by the stage's transitivity.
  module CF = CodeFacts (fst K)
    (λ {x} {y} → layer-trans (Lset-layer lam) {x = y} {y = x})
  open CF using ( compK; unCompK; entryK )

  -- The KFacts VALUE extends to the 15-element chain frame by
  -- KFactsCons (L.Condensation.lagda.md:5803-5814).
  f1 : (c : Sʟ) → KFacts {15} (suc A₀) (suc K₀)
         (suc N0) (suc N1) (suc N2) (suc N3)
         (suc N4) (suc N5) (suc N6) (suc N7)
         (suc N8) (suc N9) (suc N10) (suc N11) (c ∷ γ)
  f1 c = KFactsCons A₀ K₀ N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ c kfacts

  -- ShapesAgree, FULLY instantiated.  Its code set C is the stage's
  -- K; its compK/unCompK are the transitivity facts.  No hypothesis
  -- remains.
  module S1 (c : Sʟ) = ShapesAgree {14} C A₀ K₀
    N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
    (c ∷ γ) (f1 c) compK unCompK

  -- Force elaboration of the ShapesAgree application (P-w amendment).
  out-check : _
  out-check = S1.out

  -- The same facts at the 15-frame's slots: the code-set slot and the
  -- K slot are both suc K₀, whose value is the stage's K, so the facts
  -- are definitionally the generic ones.
  codesK15 : (c : Sʟ) → (k : ℕ) (c' ar a b : Sʟ)
           → ⟨ fst c' ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
           → fst c' ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
             × ⟨ fst a ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
             × ⟨ fst b ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
  codesK15 c = compK

  unCodesK15 : (c : Sʟ) → (k : ℕ) (c' ar a : Sʟ)
             → ⟨ fst c' ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
             → fst c' ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
               × ⟨ fst a ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
  unCodesK15 c = unCompK

  entryK15 : (c : Sʟ) (x y : Sʟ)
           → ⟨ pr (fst x) (fst y) ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
           → ⟨ fst x ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
             × ⟨ fst y ∈ˢ fst (lookup (suc K₀) (c ∷ γ)) ⟩
  entryK15 c = entryK

  -- ShapedAgree at the 15-frame, facts supplied.
  module SA (c : Sʟ) = ShapedAgree {15} (suc K₀) (suc A₀) (suc K₀)
    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11)
    (c ∷ γ) (f1 c) (codesK15 c) (unCodesK15 c)

  sa-out-check : _
  sa-out-check = SA.out

  -- ClosedAgree at the 15-frame, facts supplied.
  module CA (c : Sʟ) = ClosedAgree {15} (suc K₀) (suc K₀)
    (suc N2) (suc N3) (suc N4) (suc N5)
    (suc N8) (suc N9) (suc N10) (suc N11)
    (suc A₀) (suc N0) (suc N1) (suc N6) (suc N7)
    (c ∷ γ) (f1 c) (codesK15 c) (unCodesK15 c) (entryK15 c)

  ca-out-check : _
  ca-out-check = CA.out

  -- =================================================================
  -- THE NEXT BLOCKER: WitnessAgree's witK.  The witness w is bound
  -- inside hasWitnessAt; no stage datum concludes w ∈ K from the
  -- witness conditions.  See _build/lj-1.83-report.md section 4.
  -- =================================================================
