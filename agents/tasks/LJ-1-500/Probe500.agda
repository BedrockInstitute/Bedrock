{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.500] The two code readers of TFacts, at KValue's frame.
--
-- A reader DECODES: it takes a code in the code set plus an equation
-- that takes the code apart, and returns memberships of the pieces.
-- It is not a closure fact.  The route is the code set's membership
-- C ∈ K, then transitivity (KFacts's arityK, which is TFacts's transK
-- with the binder roles swapped, src/L/Condensation/TwelveAgree.lagda.md
-- :347-353) walked down the Kuratowski pair.
--
-- W3 FIRST, obligation omitted: `ar-is-numeral`.  The truncation
-- ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁ is NOT a closure fact and it is not
-- arityK.  The tree names its source at
-- src/L/Condensation/TwelveAgree.lagda.md:303-306: arityNumAtL
-- (L.Coding.CodeSet) says the code's arity component is a numeral,
-- and pr-inj closes it against the decomposition equation.  NOTHING
-- AT THIS FRAME SUPPLIES IT, so it is a NAMED telescope hypothesis
-- and the three memberships are delivered separately without it.
--
-- Predecessor [LJ-1.495] is GO on the six-fold shift
-- (agents/tasks/LJ-1-495/lj-1.495-report.md:71).  Predecessor
-- [LJ-1.493] is GO and measured that codesK APPLIES at this frame
-- (agents/tasks/LJ-1-493/lj-1.493-report.md:74-76).  This task
-- supplies the field instead.  Do not import a probe.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-500.Probe500 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; pairʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Coding.CodeSet {ℓ} lem using ( arityNumAtL; arityNumAtL-out )
open import L.Condensation {ℓ} lem
  using ( module KValue; module KFactsNS; KFactsCons; module ChainZ )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  ar-is-numeral, obligation omitted.
--
--   The frame gives the code's MEMBERSHIP and the decomposition
--   EQUATION.  Neither says the arity component is a numeral, and
--   `ar` is a universally quantified S.  The one conjunct that says
--   it is `arityNumAtL` (src/L/Coding/CodeSet.lagda.md:185), read
--   back by `arityNumAtL-out` (:189).  It reads the slot the code
--   sits in, so the code is consed at zero.
--
--   `rest` is the second component, whatever it is: at codesK it is
--   prʟ (numeralL k) (prʟ a b) and at codesK-un it is
--   prʟ (numeralL k) a.  This term does not look at it, which is
--   why ONE copy serves both readers (W2).
-- =====================================================================

ar-is-numeral : {m : ℕ} (γ : S ^ m) (c ar rest : S)
              → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
              → fst c ≡ pr (fst ar) (fst rest)
              → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
ar-is-numeral γ c ar rest hnum shEq =
  PT.map (λ { (n , (z , e)) → n , pr-inj (sym shEq ∙ e) .fst })
    (arityNumAtL-out zero (c ∷ γ) hnum)

-- =====================================================================
-- W2.  The two field types, ONCE, at TFacts's own generic shape
--   (src/L/Condensation/TwelveAgree.lagda.md:129-131, :162-173).
--   Instantiated below at n = 9 against KValue's Fin 14.
-- =====================================================================

record CodesPair {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                 × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    codesK-un : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
                → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                  × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                 × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

-- =====================================================================
-- THE DECODER, at a generic carrier (W2).
--
--   ChainZ (src/L/Condensation.lagda.md:2820-2917) already climbs the
--   Kuratowski pair from a pair MEMBERSHIP pr x y ∈ z plus z ∈ K.  A
--   reader is one level shorter: the pair IS in K, because the code
--   is.  So this reuses ChainZ's four pair pieces and spends the last
--   two arityK steps only.  Nothing here is re-derived.
-- =====================================================================

module Split {m : ℕ} (K : Fin m) (γ : S ^ m)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  module Z = ChainZ {m} K γ arityK

  prK-split : (x y : S) → ⟨ fst (prʟ x y) ∈ fst (lookup K γ) ⟩
            → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩
  prK-split x y hp =
      arityK (pairʟ x x) x (Z.x∈pairʟxx x)
        (arityK (prʟ x y) (pairʟ x x) (Z.xsingl∈prxy x y) hp)
    , arityK (pairʟ x y) y (Z.y∈pairʟxy x y)
        (arityK (prʟ x y) (pairʟ x y) (Z.ysingl∈prxy x y) hp)

-- =====================================================================
-- THE MEMBERSHIPS, at a generic carrier (W2).
--
--   C∈K is the code set's membership.  It is the ONE thing that turns
--   a code's membership into a K-membership, and it is a hypothesis
--   because the C slot of TFacts's environment is a free variable.
--
--   THE NUMERAL IS NOT IN THIS TELESCOPE, and that is the point of
--   splitting the module in two.  Everything below is three of the
--   four components of codesK, and two of the three of codesK-un,
--   with NO numeral input anywhere in the stored type.
-- =====================================================================

module Mem {m : ℕ} (C K : Fin m) (γ : S ^ m)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (C∈K : ⟨ fst (lookup C γ) ∈ fst (lookup K γ) ⟩) where

  open Split {m} K γ arityK public

  -- The code is in K, one arityK through the code set's membership.
  codeK : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
        → ⟨ fst c ∈ fst (lookup K γ) ⟩
  codeK c c∈ = arityK (lookup C γ) c c∈ C∈K

  -- The shared core of both readers: the head of the pair and its
  -- tail.  Neither reader looks inside the tail here.
  read : (c ar rest : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (fst rest)
       → ⟨ fst ar ∈ fst (lookup K γ) ⟩
         × ⟨ fst rest ∈ fst (lookup K γ) ⟩
  read c ar rest c∈ eq =
    let pairEq : fst (prʟ ar rest) ≡ fst c
        pairEq = prʟ-fst ar rest ∙ sym eq
        wholeK : ⟨ fst (prʟ ar rest) ∈ fst (lookup K γ) ⟩
        wholeK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (sym pairEq)
                   (codeK c c∈)
    in prK-split ar rest wholeK

  -- THE THREE MEMBERSHIPS, WITHOUT THE NUMERAL.  This is the part the
  -- frame really pays for.  It is stated on its own so the report can
  -- say three of four honestly.
  codesK-mem : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩
               × ⟨ fst a ∈ fst (lookup K γ) ⟩
               × ⟨ fst b ∈ fst (lookup K γ) ⟩
  codesK-mem k c ar a b c∈ shEq =
    let inner2 = prʟ a b
        inner1 = prʟ (numeralL k) inner2
        inner1eq : fst inner1 ≡ pr (# k) (pr (fst a) (fst b))
        inner1eq = prʟ-fst (numeralL k) inner2
                 ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a b)
        pairEq : fst (prʟ ar inner1) ≡ fst c
        pairEq = prʟ-fst ar inner1
               ∙ cong (pr (fst ar)) inner1eq
               ∙ sym shEq
        wholeK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (sym pairEq)
                   (codeK c c∈)
        (arK , inner1K) = prK-split ar inner1 wholeK
        (_ , inner2K) = prK-split (numeralL k) inner2 inner1K
        (aK , bK) = prK-split a b inner2K
    in arK , (aK , bK)

  -- codesK-un's memberships: codesK-mem minus ONE prK-split.
  codesK-un-mem : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
                → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                → ⟨ fst ar ∈ fst (lookup K γ) ⟩
                  × ⟨ fst a ∈ fst (lookup K γ) ⟩
  codesK-un-mem k c ar a c∈ shEq =
    let inner1 = prʟ (numeralL k) a
        inner1eq : fst inner1 ≡ pr (# k) (fst a)
        inner1eq = prʟ-fst (numeralL k) a
                 ∙ cong₂ pr (numeralL-fst k) refl
        pairEq : fst (prʟ ar inner1) ≡ fst c
        pairEq = prʟ-fst ar inner1
               ∙ cong (pr (fst ar)) inner1eq
               ∙ sym shEq
        wholeK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (sym pairEq)
                   (codeK c c∈)
        (arK , inner1K) = prK-split ar inner1 wholeK
        (_ , aK) = prK-split (numeralL k) a inner1K
    in arK , aK

-- =====================================================================
-- THE NUMERAL HALF, in its OWN module because its input is not the
--   frame's.  arNumC is the numeral conjunct.  Section
--   `## WHERE THE NUMERAL COMES FROM` of the report says at file:line
--   where an instantiation gets it, and that nothing at this frame
--   does.
-- =====================================================================

module Num {m : ℕ} (C : Fin m) (γ : S ^ m)
  (arNumC : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
          → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩) where

  -- The numeral, at each reader's own tail.
  codesK-num : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  codesK-num k c ar a b c∈ shEq =
    let inner1 = prʟ (numeralL k) (prʟ a b)
        inner1eq : fst inner1 ≡ pr (# k) (pr (fst a) (fst b))
        inner1eq = prʟ-fst (numeralL k) (prʟ a b)
                 ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a b)
    in ar-is-numeral γ c ar inner1 (arNumC c c∈)
         (shEq ∙ cong (pr (fst ar)) (sym inner1eq))

  codesK-un-num : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
                → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  codesK-un-num k c ar a c∈ shEq =
    let inner1 = prʟ (numeralL k) a
        inner1eq : fst inner1 ≡ pr (# k) (fst a)
        inner1eq = prʟ-fst (numeralL k) a
                 ∙ cong₂ pr (numeralL-fst k) refl
    in ar-is-numeral γ c ar inner1 (arNumC c c∈)
         (shEq ∙ cong (pr (fst ar)) (sym inner1eq))

-- =====================================================================
-- THE FRAME.  KValue's telescope, six conses, and the obligation.
--   [LJ-1.495] measured that TFacts at n = 9 is KValue's KFacts under
--   six KFactsCons (lj-1.495-report.md:47-64).  KFacts carries arityK
--   (src/L/Condensation.lagda.md:6114); TFacts does not state it.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  six : (c1 c2 c3 c4 c5 c6 : S)
      → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
      → KFacts
          (suc (suc (suc (suc (suc (suc iA))))))
          (suc (suc (suc (suc (suc (suc iK))))))
          (suc (suc (suc (suc (suc (suc i0))))))
          (suc (suc (suc (suc (suc (suc i1))))))
          (suc (suc (suc (suc (suc (suc i2))))))
          (suc (suc (suc (suc (suc (suc i3))))))
          (suc (suc (suc (suc (suc (suc i4))))))
          (suc (suc (suc (suc (suc (suc i5))))))
          (suc (suc (suc (suc (suc (suc i6))))))
          (suc (suc (suc (suc (suc (suc i7))))))
          (suc (suc (suc (suc (suc (suc i8))))))
          (suc (suc (suc (suc (suc (suc i9))))))
          (suc (suc (suc (suc (suc (suc i10))))))
          (suc (suc (suc (suc (suc (suc i11))))))
          (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
  six c1 c2 c3 c4 c5 c6 f =
    KFactsCons
      (suc (suc (suc (suc (suc iA))))) (suc (suc (suc (suc (suc iK)))))
      (suc (suc (suc (suc (suc i0))))) (suc (suc (suc (suc (suc i1)))))
      (suc (suc (suc (suc (suc i2))))) (suc (suc (suc (suc (suc i3)))))
      (suc (suc (suc (suc (suc i4))))) (suc (suc (suc (suc (suc i5)))))
      (suc (suc (suc (suc (suc i6))))) (suc (suc (suc (suc (suc i7)))))
      (suc (suc (suc (suc (suc i8))))) (suc (suc (suc (suc (suc i9)))))
      (suc (suc (suc (suc (suc i10))))) (suc (suc (suc (suc (suc i11)))))
      (c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) c6
      (KFactsCons
        (suc (suc (suc (suc iA)))) (suc (suc (suc (suc iK))))
        (suc (suc (suc (suc i0)))) (suc (suc (suc (suc i1))))
        (suc (suc (suc (suc i2)))) (suc (suc (suc (suc i3))))
        (suc (suc (suc (suc i4)))) (suc (suc (suc (suc i5))))
        (suc (suc (suc (suc i6)))) (suc (suc (suc (suc i7))))
        (suc (suc (suc (suc i8)))) (suc (suc (suc (suc i9))))
        (suc (suc (suc (suc i10)))) (suc (suc (suc (suc i11))))
        (c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) c5
        (KFactsCons
          (suc (suc (suc iA))) (suc (suc (suc iK)))
          (suc (suc (suc i0))) (suc (suc (suc i1)))
          (suc (suc (suc i2))) (suc (suc (suc i3)))
          (suc (suc (suc i4))) (suc (suc (suc i5)))
          (suc (suc (suc i6))) (suc (suc (suc i7)))
          (suc (suc (suc i8))) (suc (suc (suc i9)))
          (suc (suc (suc i10))) (suc (suc (suc i11)))
          (c3 ∷ c2 ∷ c1 ∷ Kenv) c4
          (KFactsCons
            (suc (suc iA)) (suc (suc iK))
            (suc (suc i0)) (suc (suc i1)) (suc (suc i2)) (suc (suc i3))
            (suc (suc i4)) (suc (suc i5)) (suc (suc i6)) (suc (suc i7))
            (suc (suc i8)) (suc (suc i9)) (suc (suc i10)) (suc (suc i11))
            (c2 ∷ c1 ∷ Kenv) c3
            (KFactsCons
              (suc iA) (suc iK)
              (suc i0) (suc i1) (suc i2) (suc i3)
              (suc i4) (suc i5) (suc i6) (suc i7)
              (suc i8) (suc i9) (suc i10) (suc i11)
              (c1 ∷ Kenv) c2
              (KFactsCons iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
                 Kenv c1 f)))))

  -- MEASURED SIDE-FINDING, not the obligation's route.  The six-fold
  -- shift is DEFINITIONAL on arityK: lookup (suc^6 iK) over the six
  -- conses reduces to lookup iK Kenv, so the field projects straight
  -- through.  The obligation below still goes through `six`, which is
  -- the route [LJ-1.495] delivered; this says what a LATER reader or
  -- env field would have to pay for the same input, which is nothing.
  arityK-direct : (c1 c2 c3 c4 c5 c6 : S)
    → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
    → (N v : S) → ⟨ fst v ∈ fst N ⟩
    → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                       (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
    → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                       (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
  arityK-direct c1 c2 c3 c4 c5 c6 f = f .arityK

  module At (c1 c2 c3 c4 c5 c6 : S)
    (f : KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv)
    (C∈K : ⟨ fst (lookup (suc (suc zero))
                    (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                    (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩)
    (arNumC : (c : S)
            → ⟨ fst c ∈ fst (lookup (suc (suc zero))
                              (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
            → ⟨ (c ∷ c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
                 ⊨ arityNumAtL zero ⟩)
    where

    γ' : S ^ 20
    γ' = c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv

    module R = Mem {20} (suc (suc zero))
                 (suc (suc (suc (suc (suc (suc iK))))))
                 γ' (six c1 c2 c3 c4 c5 c6 f .arityK) C∈K

    module N = Num {20} (suc (suc zero)) γ' arNumC

    codesK-family : CodesPair {n = 9} iK γ'
    codesK-family = record
      { codesK = λ k c ar a b c∈ shEq →
          let (arK , (aK , bK)) = R.codesK-mem k c ar a b c∈ shEq
          in arK , (aK , (bK , N.codesK-num k c ar a b c∈ shEq))
      ; codesK-un = λ k c ar a c∈ shEq →
          let (arK , aK) = R.codesK-un-mem k c ar a c∈ shEq
          in arK , (aK , N.codesK-un-num k c ar a c∈ shEq) }

codesK-family = Frame.At.codesK-family
