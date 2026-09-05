{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.352] DOES THE SHAPEDNESS REPAIR SAVE THE TIE?  NO.  MEASURED.
--
-- [LJ-1.347] section 6 reads the missing bound as SHAPEDNESS and says:
-- 「A container that is shaped cannot be my ⁅ c , c ⁆, because
-- `shapedAt` forces every member to be a shape.」  That is
-- [LJ-1.344]'s reading again, which [LJ-1.348] measured false and
-- [LJ-1.349] upheld as false: the arity slot of a shape is FREE at
-- every one of the twelve tags, and six of the twelve relations are
-- ⊤̇, which asks nothing of the payload either.
--
-- THIS FILE MEASURES IT AT THIS TIE.  The tie under test is
-- `wCodesK` with the repair's own hypothesis ADDED to the telescope:
--
--   (wCodesK+ : (w' : S) -> < fst w' in K >
--             -> < (w' :: gamma) |= shapedAt zero (suc A) >     THE REPAIR
--             -> (k : N) (c ar a b : S) -> < fst c in fst w' >
--             -> fst c = pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
--             -> < fst ar in K > x < fst a in K > x < fst b in K >
--             x || Sigma[ n in N ] (fst ar = # n) ||
--
-- and the countermodel is [LJ-1.347]'s ROTATED ONE TAG: the arity is
-- still the singleton of the numeral one (not a numeral), and the code
-- carries tag THREE, whose relation `noneB` is ⊤̇
-- (src/L/Coding/Shape.lagda.md:175-176).  So the code IS a shape, the
-- container IS shaped, and the arity conjunct is still false.
--
-- Everything is REBUILT here, importing nothing from any task
-- directory: the numeral lemma, the countermodel, the wire at the
-- chapter's own `KValue` record.  The numeral split is written with
-- the library eliminator (C-58), never a pattern match.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅; ∅-empty; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.Data.Nat using ( ℕ; zero; suc; znots )
open import Cubical.Data.Nat.Order using ( zero-≤; suc-≤-suc )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Nat.Base as ℕB
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-352.Repair352 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #mono; #-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Shape {ℓ}
  using ( shapedAt; shaped-in; ShapeWit )

open import L.Condensation {ℓ} lem
  using ( module KFactsNS; module ChainZ; module KTies; module KValue )
open KFactsNS

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  THE NUMERAL LEMMA, REBUILT.  The split is the library
-- eliminator, never a pattern match (C-58).
-- =====================================================================

x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

pair-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
pair-only x d h = PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
  (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

zero-clause : ⁅ # 1 , # 1 ⁆ ≡ # 0 → Empty.⊥
zero-clause q =
  ∅-empty (# 1)
    (∈∈ₛ {a = # 1} {b = ∅} .fst
      (subst (λ s → ⟨ (# 1) ∈ s ⟩) q (x∈pair (# 1) (# 1))))

suc-clause : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # (suc m) → Empty.⊥
suc-clause m q = znots (#-inj 0 1 zero≡one)
  where
  zero∈ : ⟨ (# 0) ∈ ⁅ # 1 , # 1 ⁆ ⟩
  zero∈ = subst (λ s → ⟨ (# 0) ∈ s ⟩) (sym q)
    (#mono 0 (suc m) (suc-≤-suc zero-≤))

  zero≡one : (# 0) ≡ (# 1)
  zero≡one = pair-only (# 1) (# 0) zero∈

sgl1-not-numeral : (m : ℕ) → ⁅ # 1 , # 1 ⁆ ≡ # m → Empty.⊥
sgl1-not-numeral =
  ℕB.elim {A = λ k → ⁅ # 1 , # 1 ⁆ ≡ # k → Empty.⊥}
    zero-clause (λ m _ → suc-clause m)

-- =====================================================================
-- PART 1.  THE REPAIRED TIE, REFUTED AT A GENERIC FRAME.
--
-- The six closure parameters are `KFacts` fields and nothing else.
-- `u` and `hu` say the carrier slot has a MEMBER (C-45).
-- =====================================================================

module Refute {n : ℕ} (A K : Fin n) (γ : S ^ n)
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
            → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  module Z = ChainZ {n} K γ arityK

  open KTies A K γ numK0 pairK carrierK arityK using ( sgltK )

  private
    bnd : V ℓ
    bnd = fst (lookup K γ)

  sglS : S → S
  sglS a = ⁅ fst a , fst a ⁆
         , isL-trans {x = fst (prʟ a a)} {y = ⁅ fst a , fst a ⁆}
             (subst (λ v → ⟨ ⁅ fst a , fst a ⁆ ∈ v ⟩) (sym (prʟ-fst a a))
               (Z.pair∈pr (fst a) (fst a)))
             (snd (prʟ a a))

  sglS-fst : (a : S) → fst (sglS a) ≡ ⁅ fst a , fst a ⁆
  sglS-fst a = refl

  sglK : (a : S) → ⟨ fst a ∈ bnd ⟩ → ⟨ fst (sglS a) ∈ bnd ⟩
  sglK a ha = sgltK a (sglS a) refl ha

  module Point (u : S) (hu : ⟨ fst u ∈ fst (lookup A γ) ⟩) where

    -- THE ARITY SLOT: the singleton of the numeral one.  Not a numeral
    -- at ANY index, by PART 0.
    arS : S
    arS = sglS (numeralL 1)

    ar-fst : fst arS ≡ ⁅ # 1 , # 1 ⁆
    ar-fst = cong (λ w → ⁅ w , w ⁆) (numeralL-fst 1)

    arS∈K : ⟨ fst arS ∈ bnd ⟩
    arS∈K = sglK (numeralL 1) numK1

    -- THE CODE, AT TAG 3.  Its relation is `noneB`, which is ⊤̇
    -- (src/L/Coding/Shape.lagda.md:175-176): no condition on the
    -- payload and none on the arity.
    tag3 : S
    tag3 = prʟ (numeralL 3) (prʟ u u)

    tag3-fst : fst tag3 ≡ pr (# 3) (pr (fst u) (fst u))
    tag3-fst = prʟ-fst (numeralL 3) (prʟ u u)
      ∙ cong₂ pr (numeralL-fst 3) (prʟ-fst u u)

    cS : S
    cS = prʟ arS tag3

    uK : ⟨ fst u ∈ bnd ⟩
    uK = carrierK u hu

    tag3∈K : ⟨ fst tag3 ∈ bnd ⟩
    tag3∈K = pairK (numeralL 3) (prʟ u u) numK3 (pairK u u uK uK)

    cS∈K : ⟨ fst cS ∈ bnd ⟩
    cS∈K = pairK arS tag3 arS∈K tag3∈K

    wS : S
    wS = sglS cS

    wS∈K : ⟨ fst wS ∈ bnd ⟩
    wS∈K = sglK cS cS∈K

    cS∈wS : ⟨ fst cS ∈ fst wS ⟩
    cS∈wS = Z.b∈pair (fst cS) (fst cS)

    codeEq : fst cS ≡ pr (fst arS) (pr (# 3) (pr (fst u) (fst u)))
    codeEq = prʟ-fst arS tag3 ∙ cong (pr (fst arS)) tag3-fst

    only-cS : (e : S) → ⟨ fst e ∈ fst wS ⟩ → fst e ≡ fst cS
    only-cS e he = pair-only (fst cS) (fst e)
                     (subst (λ v → ⟨ fst e ∈ v ⟩) (sglS-fst cS) he)

    -- THE REPAIR'S OWN HYPOTHESIS HOLDS AT THE COUNTERMODEL.  Every
    -- member of `wS` is `cS`, and `cS` is a TAG-THREE shape: the
    -- fourth disjunct of `ShapeWit`, `BinWit 3 noneB`, whose relation
    -- slot is ⊤̇ and whose arity slot is `arS`.
    shaped-wS : ⟨ (wS ∷ γ) ⊨ shapedAt zero (suc A) ⟩
    shaped-wS = shaped-in zero (suc A) (wS ∷ γ) g
      where
      g : (e : S) → ⟨ fst e ∈ fst wS ⟩ → ∥ ShapeWit (suc A) (wS ∷ γ) e ∥₁
      g e he =
        ∣ inr (inr (inr (inl (arS , (u , (u , ((only-cS e he ∙ codeEq) , tt*))))))) ∣₁

    -- THE REPAIRED TIE: [LJ-1.347]'s repair hypothesis in the
    -- telescope, everything else as delivered at
    -- src/L/Condensation.lagda.md:7239-7245.
    WCodesK+ : Type (ℓ-suc ℓ)
    WCodesK+ = (w' : S) → ⟨ fst w' ∈ bnd ⟩
             → ⟨ (w' ∷ γ) ⊨ shapedAt zero (suc A) ⟩
             → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ fst ar ∈ bnd ⟩
               × ⟨ fst a ∈ bnd ⟩
               × ⟨ fst b ∈ bnd ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

    -- THE REPAIRED TIE IS FALSE.
    wCodesK+-false : WCodesK+ → Empty.⊥
    wCodesK+-false h = PT.rec Empty.isProp⊥
      (λ { (m , q) → sgl1-not-numeral m (sym ar-fst ∙ q) })
      (h wS wS∈K shaped-wS 3 cS arS u u cS∈wS codeEq .snd .snd .snd)

    -- And the three OTHER conclusions hold at these witnesses.
    other-conjuncts : ⟨ fst arS ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩ × ⟨ fst u ∈ bnd ⟩
    other-conjuncts = arS∈K , uK , uK

-- =====================================================================
-- PART 2.  AT THE DELIVERED RECORD.  Same wire as the target's, with
-- `numK3` taken from the same `KFacts` value.
-- =====================================================================

module Wire (lam : V ℓ) (ordλ : IsOrd lam)
            (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ lam ⟩)
            (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
            (#1∈γ : ⟨ (# 1) ∈ gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  open KFacts KV.facts using ( numK0; numK1; numK3; pairK; carrierK; arityK )

  module R = Refute KV.iA KV.iK KV.Kenv numK0 numK1 numK3 pairK carrierK arityK

  zero∈carrier : ⟨ fst (numeralL 0) ∈ fst (lookup KV.iA KV.Kenv) ⟩
  zero∈carrier = subst (λ u → ⟨ u ∈ Lset gam ⟩) (sym (numeralL-fst 0))
    (Lset-mono {α = gam} {β = # 1} #1∈γ
      {x = # 0} (ord∈Lset-suc (# 0) (numeral-ord 0)))

  module P = R.Point (numeralL 0) zero∈carrier

  -- THE REPAIRED TIE IS FALSE AT THE DELIVERED RECORD.
  tie+-false : P.WCodesK+ → Empty.⊥
  tie+-false = P.wCodesK+-false

  live-other : ⟨ fst P.arS ∈ Lset lam ⟩
             × ⟨ fst (numeralL 0) ∈ Lset lam ⟩
             × ⟨ fst (numeralL 0) ∈ Lset lam ⟩
  live-other = P.other-conjuncts
