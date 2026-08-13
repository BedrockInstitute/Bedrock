{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ182A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Condensation {ℓ} lem using
  ( module KFactsNS; KFactsCons; module ShapesAgree; module ClosedAgree
  ; module ShapedAgree; module WitnessAgree; module SatGraphAgree
  ; module LeafAgree )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )
import FOL.Absoluteness
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open InfinitySet using ( ω; sucV; #_ )
open import V.Coding {ℓ} using ( pr )
import ProbeLJ180A

module P180 = ProbeLJ180A {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
open KFactsNS

module AbsL182 = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL182 using ( _^_ )

-- The stage: the same seven parameters as ProbeLJ180A.StageKFacts.
-- kfacts : KFacts {14} A₀ K₀ (Nk 0) ... (Nk 11) γ is the stage value
-- at K = LsetS lam, A = LsetS α (ProbeLJ180A:186-226).
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

  -- The KFacts VALUE extends to the chain frames' arities by
  -- KFactsCons (L.Condensation.lagda.md:5803-5814).  ShapesAgree's
  -- frame env is the stage env cons'd with the code-set carrier:
  -- c ∷ γ (15 elements, n = 14).
  f1 : (c : P180.Sʟ) → KFacts {15} (suc A₀) (suc K₀)
         (suc N0) (suc N1) (suc N2) (suc N3)
         (suc N4) (suc N5) (suc N6) (suc N7)
         (suc N8) (suc N9) (suc N10) (suc N11) (c ∷ γ)
  f1 c = KFactsCons A₀ K₀ N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ c kfacts

  -- The value at the SatGraphAgree/LeafAgree frame: three conses,
  -- 17 elements (n = 9 there).
  f3 : (c1 c2 c3 : P180.Sʟ) → KFacts {17} (suc (suc (suc A₀))) (suc (suc (suc K₀)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) (c3 ∷ c2 ∷ c1 ∷ γ)
  f3 c1 c2 c3 =
    KFactsCons (suc (suc A₀)) (suc (suc K₀))
      (suc (suc N0)) (suc (suc N1))
      (suc (suc N2)) (suc (suc N3))
      (suc (suc N4)) (suc (suc N5))
      (suc (suc N6)) (suc (suc N7))
      (suc (suc N8)) (suc (suc N9))
      (suc (suc N10)) (suc (suc N11))
      (c2 ∷ c1 ∷ γ) c3
      (KFactsCons (suc A₀) (suc K₀)
        (suc N0) (suc N1) (suc N2) (suc N3)
        (suc N4) (suc N5) (suc N6) (suc N7)
        (suc N8) (suc N9) (suc N10) (suc N11)
        (c1 ∷ γ) c2 (f1 c1))

  -- THE FIRST CHAIN MODULE, instantiated with the KFacts VALUE.
  -- The remaining parameters -- the code set C, its carrier c, and
  -- the code-decomposition facts compK/unCompK -- are UNSUPPLIED.
  -- KFacts' fields (L.Condensation.lagda.md:5739-5768) mention only
  -- A, K, N0..N11; none mentions a code set.  So this module is as
  -- far as the stage supply reaches: the KFacts slot of ShapesAgree
  -- receives the value, and the next hypothesis has no supplier.
  module First
    (C : P180.Sʟ) (c : P180.Sʟ)
    (compK : (k : ℕ) (c' N a b : P180.Sʟ) → ⟨ fst c' ∈ fst C ⟩
            → fst c' ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst N ∈ fst (lookup (suc K₀) (c ∷ γ)) ⟩
              × ⟨ fst a ∈ fst (lookup (suc K₀) (c ∷ γ)) ⟩
              × ⟨ fst b ∈ fst (lookup (suc K₀) (c ∷ γ)) ⟩)
    (unCompK : (k : ℕ) (c' N a : P180.Sʟ) → ⟨ fst c' ∈ fst C ⟩
              → fst c' ≡ pr (fst N) (pr (# k) (fst a))
              → ⟨ fst N ∈ fst (lookup (suc K₀) (c ∷ γ)) ⟩
                × ⟨ fst a ∈ fst (lookup (suc K₀) (c ∷ γ)) ⟩)
    where

    module S1 = ShapesAgree {14} C A₀ K₀
      N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
      (c ∷ γ) (f1 c) compK unCompK

    -- Force elaboration of the application (P-w amendment: an
    -- application that nothing uses costs nothing and proves nothing).
    out-check : _
    out-check = S1.out
