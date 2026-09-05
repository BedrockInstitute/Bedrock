{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.360] THE `hasWitnessAt` RESTATEMENT, PRICED BY A MINIATURE.
--
-- `[LJ-1.350]` priced the 28 repaired telescopes at about 43 insertions
-- ONCE THE WITNESS STEP SUPPLIES THE BOUND, and measured that nothing
-- at the chain's call site supplies it (`MustFail350.agda`, exit 42).
-- This file prices the witness step itself.
--
-- CANDIDATE 1, the honest restatement, is stated below as
-- `hasWitnessAt+`.  The witness is not any set carrying the body; it IS
-- the bounded set: every member of it is a key whose arity component is
-- a numeral.  That is Devlin's bounded-quantifier doctrine
-- (`dev/literature/devlin-II5.md:246-249`) ported onto the one
-- existential the port itself added, and it is the same conjunct
-- `arityNumAtL` already states (`src/L/Coding/CodeSet.lagda.md:185`).
--
-- THIS FILE MEASURES FOUR THINGS.
--
--   1. THE SUPPLY (PART 1).  From the restated satisfaction, the four
--      bindings `WitnessAgree.out.go` makes, with the arity bound IN
--      the fourth.  `MustFail350.agda`'s `no-supplier` type, supplied.
--   2. THE COMPOSITION (PART 2).  The supply plus `[LJ-1.350]`'s
--      five-line cure produces the 28 telescopes' LAST CONJUNCT at
--      every member of the witness.  No further hypothesis.
--   3. THE SUPPLIER (PART 3).  The closure still satisfies the
--      restated predicate, and the new conjunct costs five lines that
--      mirror `closureShaped`'s map over `closure-inv`
--      (`src/L/Coding/Shape.lagda.md:646-649`).  That is the price of
--      `witnessAt-in`'s restatement, MEASURED.
--   4. THE CONTROL (PART 4).  The new conjunct HOLDS at a witness set
--      whose only member has a numeral arity and FAILS at the same
--      witness with the arity one argument apart, the singleton of
--      that numeral.  `[LJ-1.350]`'s standard, one file.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∀̇∈; ⊤̇ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

module LJ-1-360.Probe360 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( closedAt; prʟ; prʟ-fst )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.InL {ℓ} using ( closure-inv; key∈closure )
open import L.Coding.Closed {ℓ} using ( clo; closureClosed )
open import L.Coding.Shape {ℓ} using ( shapedAt; closureShaped )
open import L.Coding.CodeSet {ℓ} lem
  using ( arityNumAtL; arityNumAtL-in; arityNumAtL-out
        ; codeS; keyS )

open import L.Condensation {ℓ} lem using ( module ChainZ )

open import LJ-1-347.Elim347 {ℓ} using ( sgl1-not-numeral )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  CANDIDATE 1, THE HONEST RESTATEMENT, AS A TYPE.
--
-- Today (`src/L/Coding/CodeSet.lagda.md:240-242`):
--
--   hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero)
--                         ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A)))
--
-- The restatement right-extends the body with ONE conjunct: the
-- witness is a set every member of which is a key with a numeral
-- arity.  Nothing else moves, so the destructuring patterns of the
-- delivered consumers gain one slot at the right end and no more.
-- =====================================================================

hasWitnessAt+ : ∀ {n} → Fin n → Fin n → Formula S n
hasWitnessAt+ A x = ∃̇ ((var (suc x) ∈̇ var zero)
                        ∧̇ ((closedAt zero ∧̇ shapedAt zero (suc A))
                           ∧̇ ∀̇∈ (var zero) (arityNumAtL zero)))

-- =====================================================================
-- PART 1.  THE SUPPLY.  `[LJ-1.350]`'s `MustFail350.agda` measured that
-- the site's own three bindings cannot supply the arity bound at any
-- member of the witness.  The restated predicate supplies it in the
-- fourth binding.  Generic in `n` and in the environment, so one copy
-- serves every site of the family.
-- =====================================================================

supply : ∀ {n} (A x : Fin n) (γ : S ^ n)
       → ⟨ γ ⊨ hasWitnessAt+ A x ⟩
       → ∥ Σ[ w ∈ S ] ( ⟨ fst (lookup x γ) ∈ fst w ⟩
          × ((cc : S) → ⟨ fst cc ∈ fst w ⟩
                → ⟨ (cc ∷ w ∷ γ) ⊨ arityNumAtL zero ⟩)) ∥₁
supply A x γ h = PT.rec squash₁
  (λ { (w , (hxw , (_ , har))) → ∣ w , (hxw , har) ∣₁ }) h

-- =====================================================================
-- PART 2.  THE COMPOSITION.  The supply plus `[LJ-1.350]`'s five-line
-- cure (its `arity-cure`, `Cure350.agda:81-88`, restated inline at the
-- member's frame) produces the 28 telescopes' last conjunct at EVERY
-- member of the witness, with no hypothesis beyond the telescope's own
-- membership and equation.  This is the repaired `compK` conclusion,
-- running on the destructed site.
-- =====================================================================

module Tie {n : ℕ} (γ : S ^ n) where

  arity-cure : (k : ℕ) (c N a b : S)
             → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
             → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
             → ∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁
  arity-cure k c N a b h e = PT.map
    (λ { (m , (z , q)) → m , pr-inj (sym e ∙ q) .fst })
    (arityNumAtL-out zero (c ∷ γ) h)

supply-tie : ∀ {n} (A x : Fin n) (γ : S ^ n)
           → ⟨ γ ⊨ hasWitnessAt+ A x ⟩
           → ∥ Σ[ w ∈ S ] ( ⟨ fst (lookup x γ) ∈ fst w ⟩
              × ((k : ℕ) (cc N a b : S) → ⟨ fst cc ∈ fst w ⟩
                 → fst cc ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
                 → ∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁)) ∥₁
supply-tie A x γ h = PT.rec squash₁
  (λ { (w , (hxw , (_ , har))) →
       ∣ w , (hxw , λ k cc N a b hcc e →
         Tie.arity-cure (w ∷ γ) k cc N a b (har cc hcc) e) ∣₁ }) h

-- =====================================================================
-- PART 3.  THE SUPPLIER, AND THE PRICE OF `witnessAt-in`'s
-- RESTATEMENT.  The closure of a formula still satisfies the restated
-- predicate.  The new conjunct is `clo-arity` below: FIVE lines, the
-- mirror of `closureShaped`'s map over `closure-inv`
-- (`src/L/Coding/Shape.lagda.md:646-649`), which walks the same
-- members and asks more of them.
--
-- The alphabet plumbing (`ι`, `ι∈`, `ιL`) is copied from
-- `src/L/Coding/CodeSet.lagda.md:256-271`; it is the supplier's own
-- frame and not part of the restatement's price.
-- =====================================================================

module Supplier (A : S) {n k : ℕ} (b c : Fin n) (γ : S ^ n)
                (φ : Formula ⟪ fst A ⟫ k)
                (qb : fst (lookup b γ) ≡ fst A)
                (qc : fst (lookup c γ) ≡ fst (keyS A φ)) where

  private
    ι : ⟪ fst A ⟫ → V ℓ
    ι = ⟪ fst A ⟫↪

    ι∈ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ fst A ⟩
    ι∈ m = ∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪_⟫↪_ (fst A) m)

    ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
    ιL m = isL-trans {x = fst A} {y = ι m} (ι∈ m) (A .snd)

  -- THE NEW CONJUNCT AT THE CLOSURE.  Five lines.  Every member of the
  -- closure is the key of some subformula (`closure-inv`), and a key's
  -- first component IS a numeral, which is what `arityNumAtL-in`
  -- takes.  No induction: the closure chapter did it.
  clo-arity : ⟨ (clo ι ιL φ ∷ γ) ⊨ ∀̇∈ (var zero) (arityNumAtL zero) ⟩
  clo-arity cc hc = PT.rec (snd ((cc ∷ clo ι ιL φ ∷ γ) ⊨ arityNumAtL zero))
    (λ { (m , (ψ , (q , _))) →
      arityNumAtL-in zero (cc ∷ clo ι ιL φ ∷ γ) m (codeS A ψ) q })
    (closure-inv ι ιL φ (fst cc) hc)

  -- THE RESTATED PRODUCER.  `witnessAt-in`
  -- (`src/L/Coding/CodeSet.lagda.md:365-373`) plus ONE tuple slot, the
  -- last.  Every other component is the delivered term unchanged.
  witnessAt-in+ : ⟨ γ ⊨ hasWitnessAt+ b c ⟩
  witnessAt-in+ = ∣ clo ι ιL φ
    , ( subst (λ w → ⟨ w ∈ fst (clo ι ιL φ) ⟩) (sym qc)
        (key∈closure ι ιL φ)
      , ( ( closureClosed ι ιL φ γ
          , closureShaped ι ιL φ b γ
              (λ m → subst (λ w → ⟨ ι m ∈ w ⟩) (sym qb) (ι∈ m)) )
        , clo-arity ) ) ∣₁

-- =====================================================================
-- PART 4.  THE CONTROL, `[LJ-1.350]`'s STANDARD.  The new conjunct
-- HOLDS at a witness set whose only member carries a numeral arity,
-- and FAILS at the same witness set with the arity component ONE
-- ARGUMENT apart: `numeralL 1` against `sglS (numeralL 1)`.
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

    -- THE TWO MEMBERS, ONE ARGUMENT APART IN THE ARITY COMPONENT.
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

  -- THE CONTROL, `[LJ-1.350]`'s STANDARD, at the member the conjunct
  -- reads.  `gS` and `cS` are ONE ARGUMENT apart in the arity
  -- component: `numeralL 1` against `sglS (numeralL 1)`.  The conjunct
  -- HOLDS at the good member and FAILS at the bad one.
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

  -- AND AT THE WITNESS-SET LEVEL, the refutation is not vacuous: the
  -- bad WITNESS SET really meets the meet's domain at its bad member,
  -- so the conjunct-as-stated is REFUTED there, not merely unmet.
  conjunct-fails : ⟨ (W-bad ∷ γ) ⊨ ∀̇∈ (var zero) (arityNumAtL zero) ⟩
                 → Empty.⊥
  conjunct-fails hmeet = member-fails (hmeet cS cS∈W)

-- =====================================================================
-- PART 5.  NON-VACUITY, CLOSED.  The restated predicate is INHABITED at
-- a real point: a real carrier, a real formula, the closure as the
-- witness.  `witnessAt-in`'s old three components are the delivered
-- terms; the fourth is `clo-arity`, five lines.
-- =====================================================================

module Live where

  A₀ : S
  A₀ = numeralL 0

  φ₀ : Formula ⟪ fst A₀ ⟫ 1
  φ₀ = ⊤̇

  module Sup = Supplier A₀ zero (suc zero) (A₀ ∷ keyS A₀ φ₀ ∷ []) φ₀
                   refl refl

  inhabited : ⟨ (A₀ ∷ keyS A₀ φ₀ ∷ []) ⊨ hasWitnessAt+ zero (suc zero) ⟩
  inhabited = Sup.witnessAt-in+
