{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.145, probe B.  ONE question: is the master's dominant term the
-- MODULE APPLICATION (P-w), or the formula in the type (P-t)?
--
-- Probe A measured that `LeafAgree.out`'s exact TYPE elaborates in under
-- 1 ms, while the master bills that definition 9,267 ms.  So the cost is
-- the BODY, and the body is three projections out of module-application
-- copies.  This probe restates `LeafAgree`'s telescope, cut to what
-- `SatGraphAgree` needs, and uses `SatGraphAgree.out` TWICE:
--
--   useApp : through `module SG = SatGraphAgree ...`, today's spelling
--   useFun : the same definition applied directly, no module application
--
-- P-w class (a), fewer applications, predicts `useFun` is the cheap one.
-- Read with `agda --profile=definitions`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-145.ProbeLJ1145B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( appAt; closedAt; domAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Condensation {ℓ} lem using
  ( module KFactsNS; module SatGraphAgree; module SatGraphB )
open KFactsNS using ( KFacts )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Site {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (f : KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ)
  (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
  (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                            N6 N7 N8 N9 N10 N11 t0 t1 ⟩
               → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
  (gCodesK : (d e f : S) → (k : ℕ) → (c ar a b : S)
            → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (gUnCodesK : (d e f : S) → (k : ℕ) → (c ar a : S)
              → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (gEntryK : (d e f : S) → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
              → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
         → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (graphWitK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedAt (suc (suc zero))
                 ∧̇ (domAt (suc zero) (suc (suc zero))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                     ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  where

  -- Today's spelling: one module application, then a projection.
  module SG = SatGraphAgree {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ
                f twelve-out twelve-back
                gCodesK gUnCodesK gEntryK domEntryK domK graphWitK

  useApp : ⟨ γ ⊨ satGraphAt (suc (suc (suc w))) (suc zero) zero ⟩
         → ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  useApp h = SG.out h

  -- The same definition, applied.  No module application anywhere.
  useFun : ⟨ γ ⊨ satGraphAt (suc (suc (suc w))) (suc zero) zero ⟩
         → ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  useFun h = SatGraphAgree.out {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ
               f twelve-out twelve-back
               gCodesK gUnCodesK gEntryK domEntryK domK graphWitK h

  -- The floor: a telescope hypothesis used the same way, no module.
  useTel : (d e f' : S) → ⟨ (f' ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
         → ⟨ (f' ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                     N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  useTel d e f' h = twelve-out d e f' h
