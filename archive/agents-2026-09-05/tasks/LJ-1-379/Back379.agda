{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.379] THE BACK DIRECTION AT THE CHAIN, MEASURED BY A MINIATURE.
--
-- `[LJ-1.360]` priced the `hasWitnessAt` restatement and left ONE term
-- unmeasured: `WitnessAgree.back` must now also produce the new
-- conjunct, every member of the witness a key with a numeral arity.
-- Its closest candidate, the bounded form's own shapedness offered
-- where the arity is wanted, was refused (`MustFail360.agda`, exit 42).
--
-- THIS FILE MEASURES FOUR THINGS.
--
--   1. THE SUPPLY (PART 1).  `har` below takes exactly the facts the
--      bounded form binds at the witness frame, plus the site's own
--      telescope, and produces the new conjunct at every member.  The
--      chain is: `ShapedAgree.back` (delivered) walks the bounded
--      shapedness into the unbounded one at the witness; `shaped-out`
--      (delivered) flattens its twelve-clause disjunction into
--      `ShapeWit`; `codesK`/`unCodesK` (already in the telescope,
--      `[LJ-1.153]`) return the numeral arity for each member's
--      equation; `arityNumAtL-in` (delivered adequacy,
--      `CodeSet.lagda.md:201-207`) closes each member.  The
--      two-directional adequacy pays: the IN direction is the closer.
--
--   2. THE COMPOSITION (PART 2).  `back+` below is the landed shape:
--      from the bounded form's satisfaction to the restated
--      `hasWitnessAt+`, with the old three components the delivered
--      terms unchanged and the fourth the new `har`.
--
--   3. `witK` IS NOT NEEDED (PART 2 again).  The site below does not
--      even take `witK` as a parameter.  `[LJ-1.348]` measured `witK`
--      FALSE; the back leg runs on the bounded form's own bindings, so
--      that objection does not reach here.  MEASURED by the green.
--
--   4. THE CONTROL (PART 3).  `[LJ-1.360]`'s member-level control,
--      copied verbatim, refutes the conjunct at a member one argument
--      apart, so the type `har` produces is not vacuously green; and
--      `MustFail379.agda` measures that the walk WITHOUT `codesK`'s
--      numeral component does not typecheck, so the supply is not
--      free.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∀̇∈ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

module LJ-1-379.Back379 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( closedAt; prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Shape {ℓ} using ( shapedAt; shaped-out; ShapeWit )
open import L.Coding.CodeSet {ℓ} lem
  using ( arityNumAtL; arityNumAtL-in; arityNumAtL-out )

open import L.Condensation {ℓ} lem
  using ( KFactsCons; hasWitnessBS; shapedBS; closedBS
        ; module ChainZ; module KFactsNS; module ShapedAgree
        ; module ClosedAgree )

open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  THE RESTATED PREDICATE, COPIED FROM `Probe360.agda:96-99`.
-- The body is right-extended with one conjunct: every member of the
-- witness is a key with a numeral arity.
-- =====================================================================

hasWitnessAt+ : ∀ {n} → Fin n → Fin n → Formula S n
hasWitnessAt+ A x = ∃̇ ((var (suc x) ∈̇ var zero)
                        ∧̇ ((closedAt zero ∧̇ shapedAt zero (suc A))
                           ∧̇ ∀̇∈ (var zero) (arityNumAtL zero)))

-- =====================================================================
-- PART 1.  THE SUPPLY.  The site is `WitnessAgree.back`'s own telescope
-- (`src/L/Condensation.lagda.md:6680-6709`) with `witK` DELETED: the
-- back leg never calls it.  `har` is the unmeasured term, measured.
-- =====================================================================

module Site {n : ℕ} (A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (f : KFactsNS.KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
  (codesK : (w : S) → ⟨ fst w ∈ fst (lookup K γ) ⟩
           → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁)
  (unCodesK : (w : S) → ⟨ fst w ∈ fst (lookup K γ) ⟩
             → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩
               × ⟨ fst a ∈ fst (lookup K γ) ⟩
               × ∥ Σ[ m ∈ ℕ ] (fst ar ≡ # m) ∥₁)
  (entryK : (w : S) → ⟨ fst w ∈ fst (lookup K γ) ⟩
           → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w ⟩
           → ⟨ fst x' ∈ fst (lookup K γ) ⟩
             × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  -- THE TWO GENERIC HANDLERS.  Each takes the member equation the flat
  -- witness carries, feeds it to the telescope's own `codesK`/`unCodesK`
  -- at the witness, takes the FOURTH component (the numeral arity) and
  -- closes the member by the adequacy's IN direction.
  module Har (w : S) (wK : ⟨ fst w ∈ fst (lookup K γ) ⟩)
             (hsh : ⟨ (w ∷ γ) ⊨ shapedBS zero (suc A) (suc K)
                               (suc N0) (suc N1) (suc N2) (suc N3) (suc N4)
                               (suc N5) (suc N6) (suc N7) (suc N8) (suc N9)
                               (suc N10) (suc N11) ⟩) where

    module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                  (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                  (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11)
                  (w ∷ γ)
                  (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ w f)
                  (codesK w wK) (unCodesK w wK)

    z-eqB : (k : ℕ) (a b : S)
          → fst (prʟ (numeralL k) (prʟ a b)) ≡ pr (# k) (pr (fst a) (fst b))
    z-eqB k a b = prʟ-fst (numeralL k) (prʟ a b)
      ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a b)

    z-eqU : (k : ℕ) (a : S) → fst (prʟ (numeralL k) a) ≡ pr (# k) (fst a)
    z-eqU k a = prʟ-fst (numeralL k) a ∙ cong (λ u → pr u (fst a)) (numeralL-fst k)

    bin-arity : (k : ℕ) (c N a b : S) → ⟨ fst c ∈ fst w ⟩
             → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
    bin-arity k c N a b hc e = PT.rec
      (snd ((c ∷ w ∷ γ) ⊨ arityNumAtL zero))
      (λ { (m , eN) →
        arityNumAtL-in zero (c ∷ w ∷ γ) m (prʟ (numeralL k) (prʟ a b))
          (e ∙ cong (λ u → pr u (pr (# k) (pr (fst a) (fst b)))) eN
           ∙ cong (λ v → pr (# m) v) (sym (z-eqB k a b))) })
      (codesK w wK k c N a b hc e .snd .snd .snd)

    un-arity : (k : ℕ) (c N a : S) → ⟨ fst c ∈ fst w ⟩
             → fst c ≡ pr (fst N) (pr (# k) (fst a))
             → ⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
    un-arity k c N a hc e = PT.rec
      (snd ((c ∷ w ∷ γ) ⊨ arityNumAtL zero))
      (λ { (m , eN) →
        arityNumAtL-in zero (c ∷ w ∷ γ) m (prʟ (numeralL k) a)
          (e ∙ cong (λ u → pr u (pr (# k) (fst a))) eN
           ∙ cong (λ v → pr (# m) v) (sym (z-eqU k a))) })
      (unCodesK w wK k c N a hc e .snd .snd)

    -- THE NEW CONJUNCT, at every member of the witness.  The delivered
    -- `SA.back` walks the bounded shapedness into the unbounded one;
    -- the delivered `shaped-out` flattens the twelve clauses; each
    -- branch is one handler call.  This is the unmeasured term.
    har : (c : S) → ⟨ fst c ∈ fst w ⟩
       → ⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
    har c hc = PT.rec (snd ((c ∷ w ∷ γ) ⊨ arityNumAtL zero)) fill
      (shaped-out zero (suc A) (w ∷ γ) (SA.back hsh) c hc)
      where
      fill : ShapeWit (suc A) (w ∷ γ) c
           → ⟨ (c ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩
      fill (inl (N , (a , (b , (e , hr))))) =
        bin-arity 0 c N a b hc e
      fill (inr (inl (N , (a , (b , (e , hr)))))) =
        bin-arity 1 c N a b hc e
      fill (inr (inr (inl (N , (a , (b , (e , hr))))))) =
        bin-arity 2 c N a b hc e
      fill (inr (inr (inr (inl (N , (a , (b , (e , hr)))))))) =
        bin-arity 3 c N a b hc e
      fill (inr (inr (inr (inr (inl (N , (a , (b , (e , hr))))))))) =
        bin-arity 4 c N a b hc e
      fill (inr (inr (inr (inr (inr (inl (N , (a , (e , hr))))))))) =
        un-arity 5 c N a hc e
      fill (inr (inr (inr (inr (inr (inr (inl (N , (a , (e , hr)))))))))) =
        un-arity 6 c N a hc e
      fill (inr (inr (inr (inr (inr (inr (inr (inl (N , (a , (e , hr))))))))))) =
        un-arity 7 c N a hc e
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inl (N , (a , (e , hr)))))))))))) =
        un-arity 8 c N a hc e
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl (N , (a , (e , hr))))))))))))) =
        un-arity 9 c N a hc e
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inl (N , (a , (b , (e , hr))))))))))))))) =
        bin-arity 10 c N a b hc e
      fill (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (inr (N , (a , (b , (e , hr))))))))))))))) =
        bin-arity 11 c N a b hc e  -- ===================================================================
  -- PART 2.  THE LANDED SHAPE, `back` plus the fourth tuple slot.  The
  -- old three components are the delivered terms unchanged, exactly as
  -- `src/L/Condensation.lagda.md:6734-6752` computes them; the fourth
  -- is `har`.  NO `witK` anywhere.
  -- ===================================================================
  back+ : ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ hasWitnessAt+ A x ⟩
  back+ h = PT.rec squash₁ go h
    where
    go : Σ[ w ∈ S ] (⟨ fst w ∈ fst (lookup K γ) ⟩
                    × ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
                         ∧̇ (closedBS zero (suc K) (suc N2) (suc N3) (suc N4)
                               (suc N5) (suc N8) (suc N9) (suc N10) (suc N11)
                           ∧̇ shapedBS zero (suc A) (suc K)
                                (suc N0) (suc N1) (suc N2) (suc N3) (suc N4)
                                (suc N5) (suc N6) (suc N7) (suc N8) (suc N9)
                                (suc N10) (suc N11))) ⟩)
       → ⟨ γ ⊨ hasWitnessAt+ A x ⟩
    go (w , (wK , (hxw , (hcl , hsh)))) =
      ∣ w , ( hxw , ( (CA.back hcl , SA.back hsh) , H.har ) ) ∣₁
      where
      module H = Har w wK hsh
      module CA = ClosedAgree {1 + n} zero (suc K)
                    (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N8) (suc N9) (suc N10) (suc N11)
                    (suc A) (suc N0) (suc N1) (suc N6) (suc N7) (w ∷ γ)
                    (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ w f)
                    (codesK w wK) (unCodesK w wK) (entryK w wK)
      module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11)
                    (w ∷ γ)
                    (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ w f)
                    (codesK w wK) (unCodesK w wK)

-- =====================================================================
-- PART 3.  THE CONTROL, `[LJ-1.360]`'s standard, copied verbatim from
-- `Probe360.agda` PART 4 (its lines 247-268).  The type `har` produces
-- is REFUTED at a witness set whose only member carries a non-numeral
-- arity one argument apart from a good one, so the green above is not
-- vacuous.  `MustFail379.agda` measures the other half: without
-- `codesK`'s numeral component the walk does not typecheck.
-- =====================================================================

module Control {n : ℕ} (K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  module Z = ChainZ {n} K γ arityK

  sglS : S → S
  sglS a = ⁅ fst a , fst a ⁆
         , isL-trans {x = fst (prʟ a a)} {y = ⁅ fst a , fst a ⁆}
             (subst (λ v → ⟨ ⁅ fst a , fst a ⁆ ∈ v ⟩) (sym (prʟ-fst a a))
               (Z.pair∈pr (fst a) (fst a)))
             (snd (prʟ a a))

  private
    u : S
    u = numeralL 0

    gS : S
    gS = prʟ (numeralL 1) (prʟ (numeralL 2) (prʟ u u))

    arS : S
    arS = sglS (numeralL 1)

    cS : S
    cS = prʟ arS (prʟ (numeralL 2) (prʟ u u))

    cEq : fst cS ≡ pr (fst arS) (pr (# 2) (pr (fst u) (fst u)))
    cEq = prʟ-fst arS (prʟ (numeralL 2) (prʟ u u))
      ∙ cong (pr (fst arS))
          (prʟ-fst (numeralL 2) (prʟ u u)
            ∙ cong₂ pr (numeralL-fst 2) (prʟ-fst u u))

  W-bad : S
  W-bad = sglS cS

  cS∈W : ⟨ fst cS ∈ fst W-bad ⟩
  cS∈W = Z.b∈pair (fst cS) (fst cS)

  member-holds : ⟨ (gS ∷ γ) ⊨ arityNumAtL zero ⟩
  member-holds = arityNumAtL-in zero (gS ∷ γ) 1
    (prʟ (numeralL 2) (prʟ u u))
    (prʟ-fst (numeralL 1) (prʟ (numeralL 2) (prʟ u u))
      ∙ cong (λ w → pr w (fst (prʟ (numeralL 2) (prʟ u u))))
          (numeralL-fst 1))

  member-fails : ⟨ (cS ∷ γ) ⊨ arityNumAtL zero ⟩ → Empty.⊥
  member-fails h = PT.rec Empty.isProp⊥
    (λ { (m , (z , q)) → sgl1-not-numeral m
          (sym ar-fst ∙ pr-inj (sym cEq ∙ q) .fst) })
    (arityNumAtL-out zero (cS ∷ γ) h)
    where
    ar-fst : fst arS ≡ ⁅ # 1 , # 1 ⁆
    ar-fst = cong (λ w → ⁅ w , w ⁆) (numeralL-fst 1)

  -- The conjunct `har` produces, REFUTED as stated at a witness set.
  conjunct-fails : ⟨ (W-bad ∷ γ) ⊨ ∀̇∈ (var zero) (arityNumAtL zero) ⟩
                 → Empty.⊥
  conjunct-fails hmeet = member-fails (hmeet cS cS∈W)
