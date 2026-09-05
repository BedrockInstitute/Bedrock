{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.145, probe C.  Probes A and B refuted both leads: the TYPE of
-- `LeafAgree.out` costs under 1 ms, and its module application costs
-- 10 ms.  The master bills the definition 9,267 ms.  So probe C
-- transplants the WHOLE module, verbatim, and asks whether the cost
-- follows the content or stays with the master.
--
-- If the copy reproduces the seconds, the cost is intrinsic to this
-- composition and can be bisected here.  If the copy is fast, the cost
-- is the SAME-FILE effect: a supplier read from an interface is not the
-- same price as the identical supplier written in the file that uses it.
--
-- Read with `agda --profile=definitions`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-145.ProbeLJ1145C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( appAt; closedAt; domAt; tagAtL )
open import L.Coding.Shape {ℓ} using ( shapedAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; envOneAt )
open import L.Condensation {ℓ} lem using
  ( module KFactsNS; module SatGraphAgree; module SatGraphB
  ; module WitnessAgree; module KeyAgree; module DefinesAgree
  ; isCodeBS; DefBodyB; DefinesBS )
open KFactsNS using ( KFacts )
open KFacts
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module LeafAgreeCopy {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (f : KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ)
  (witK : (w' : S) → ⟨ (w' ∷ γ) ⊨ ((var (suc (suc zero)) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w)))))) ⟩
         → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wCodesK : (w' : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wUnCodesK : (w' : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w' ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (wEntryK : (w' x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w' ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
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
  (keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc (suc zero)) 1 zero ⟩
            → ⟨ fst t ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (defPairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
             → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨ ((var zero ∈̇ var (suc (suc (suc (suc w)))))
             ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc zero))))) ⟩
         → ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  module WA = WitnessAgree {8 + n} (suc (suc (suc w))) (suc zero) (suc (suc (suc K)))
                (suc (suc (suc N0))) (suc (suc (suc N1)))
                (suc (suc (suc N2))) (suc (suc (suc N3)))
                (suc (suc (suc N4))) (suc (suc (suc N5)))
                (suc (suc (suc N6))) (suc (suc (suc N7)))
                (suc (suc (suc N8))) (suc (suc (suc N9)))
                (suc (suc (suc N10))) (suc (suc (suc N11))) γ
                f witK wCodesK wUnCodesK wEntryK

  module KA = KeyAgree {8 + n} (suc zero) (suc (suc (suc N1))) (suc (suc (suc K))) γ 1
                (f .tagEq1) (f .numK1) keyValK

  module SG = SatGraphAgree {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ
                f twelve-out twelve-back
                gCodesK gUnCodesK gEntryK domEntryK domK graphWitK

  module DA = DefinesAgree {8 + n} (suc (suc zero)) (suc (suc (suc w))) zero
                (suc (suc (suc K))) (suc (suc (suc N0))) γ
                (f .tagEq0) (f .numK0) envK defPairK satK

  ic-out : ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
         → ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
  ic-out (hk , hw) = (KA.out hk , WA.out hw)

  ic-back : ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
         → ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
  ic-back (hk , hw) = (KA.back hk , WA.back hw)

  out : ⟨ γ ⊨ DefBody {5 + n} w ⟩ → ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  out (hcode , (hgraph , hdef)) =
    ( ic-out hcode
    , ( SG.out hgraph
      , DA.out hdef ) )

  back : ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ DefBody {5 + n} w ⟩
  back (hcode , (hgraph , hdef)) =
    ( ic-back hcode
    , ( SG.back hgraph
      , DA.back hdef ) )

  -- ===================================================================
  -- THE BISECT.  `out` above is 3,857 ms for four lines.  Probe A
  -- measured its TYPE at under 1 ms and probe B measured its middle
  -- component at 10 ms.  So the seconds are in the composition.  These
  -- four definitions split the same body into its three components plus
  -- an identity control, each billed separately.
  -- ===================================================================

  ctrl : ⟨ γ ⊨ DefBody {5 + n} w ⟩ → ⟨ γ ⊨ DefBody {5 + n} w ⟩
  ctrl (a , (b , c)) = (a , (b , c))

  compIC : ⟨ γ ⊨ DefBody {5 + n} w ⟩
         → ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
  compIC (hcode , _) = ic-out hcode

  compSG : ⟨ γ ⊨ DefBody {5 + n} w ⟩
         → ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  compSG (_ , (hgraph , _)) = SG.out hgraph

  compDA : ⟨ γ ⊨ DefBody {5 + n} w ⟩
         → ⟨ γ ⊨ DefinesBS (suc (suc zero)) (suc (suc (suc w))) zero
                   (suc (suc (suc K))) (suc (suc (suc N0))) ⟩
  compDA (_ , (_ , hdef)) = DA.out hdef

  -- `compSG` is 2,573 ms; probe B measured the SAME `SG.out h` at 10 ms
  -- when `h` was a telescope hypothesis.  The only difference is where
  -- `h` comes from.  These two isolate that.

  -- (a) the supplier, called on a variable of its OWN stated type
  sgOnStated : ⟨ γ ⊨ satGraphAt (suc (suc (suc w))) (suc zero) zero ⟩
             → ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  sgOnStated h = SG.out h

  -- (b) the split component, coerced to that stated type and NOTHING else
  midOf : ⟨ γ ⊨ DefBody {5 + n} w ⟩
        → ⟨ γ ⊨ satGraphAt (suc (suc (suc w))) (suc zero) zero ⟩
  midOf (_ , (hgraph , _)) = hgraph
