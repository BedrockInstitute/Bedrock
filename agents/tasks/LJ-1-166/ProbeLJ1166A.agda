{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.166 probe A.  THE SUPPLY: one `KFacts` VALUE.
--
-- Six gates in this phase priced DERIVATIONS.  None priced a SUPPLY.
-- [LJ-1.165] MEASURED that `KFacts` is never CONSTRUCTED anywhere in
-- `src/`: the only thing shaped like a constructor builds a `KFacts`
-- from another `KFacts`, so there is no base case and no value.
--
-- Devlin's `K(u)` (`_build/literature/dev2.txt:600-612`) is the finite
-- sequences over the formula set, the variables and the members of `u`.
-- Its bound works because `K(u)` is a SET and it lies at the level.
--
-- THE ANALOGUE ON THIS CODING, and this probe tests it:
--   `K := Lset λ` for a limit `λ` above the carrier's ordinal.
-- `KFacts` asks for exactly four closure classes, and each is one of
-- Devlin's:
--   arityK     the bound is TRANSITIVE
--   numK0-11   the bound holds the twelve arity numerals (the formula set)
--   pairK      the bound is closed under the Kuratowski pair (the sequences)
--   carrierK   the bound holds the carrier (the members of `u`)
--
-- CRITERION, FIXED BEFORE THE RUN (D-1), and it is the report's:
--   20 minutes of wall time per agda invocation, GHCRTS="-A64m -I0 -M8g",
--   ONE process, cap NEVER raised.  Abort the value at 150 in-fence lines.
--
-- BLOCK 1  the three closure facts at an ARBITRARY limit, from the
--          three parameters `HullStage` already carries (`ordλ`,
--          `succλ`, `∅∈λ`).  The tree holds all three at `Lset ω` only
--          (`src/L/Choice/Name.lagda.md:120-138`); this block is the
--          same argument with the numeral recursion replaced by
--          `Lset-out` and ordinal trichotomy.
-- BLOCK 2  the `KFacts` VALUE itself.
--
-- P-i [F] is obeyed throughout: every lemma with an implicit set index
-- applied at a concrete argument gets the index EXPLICITLY.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-166.ProbeLJ1166A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; Lset-out; Lset-mono
        ; layer-trans; Lset-layer )
open import L.Axioms.Basic {ℓ}
  using ( LsetS; Lset-suc; pr∈Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; numeral-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Condensation {ℓ} lem using ( module KFactsNS; KFactsCons )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module CS = hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )
open KFactsNS using ( KFacts )

-- =====================================================================
-- BLOCK 1: THE BOUND, AT AN ARBITRARY LIMIT.
--
-- The three parameters are `HullStage`'s own, verbatim from
-- `src/L/BoundedSubset.lagda.md:903-906`.  Nothing new is assumed.
-- =====================================================================

module Bound (lam : S) (ordλ : IsOrd lam)
             (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  -- Every numeral is an ordinal of the limit, by the two parameters.
  #∈λ : (k : ℕ) → ⟨ (# k) ∈ˢ lam ⟩
  #∈λ zero    = ∅∈λ
  #∈λ (suc k) = succλ (# k) (#∈λ k)

  -- THE FORMULA SET.  Devlin's `𝓕 ∪ {vᵢ}`, here the numerals.
  num∈λ : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩
  num∈λ k = subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (numeralL-fst k))
    (Lset-mono {α = lam} {β = sucV (# k)} (#∈λ (suc k))
      {x = # k} (ord∈Lset-suc (# k) (numeral-ord k)))

  -- The stage decomposition, one side, with the successor named.
  private
    At : S → Type (ℓ-suc ℓ)
    At x = Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩)

    at : (x : S) → ⟨ x ∈ˢ Lset lam ⟩ → ∥ At x ∥₁
    at x hx = PT.map
      (λ { (δ , (δ∈ , h)) → δ , (δ∈ , subst (λ w → ⟨ x ∈ˢ w ⟩)
             (sym (Lset-suc δ)) h) })
      (Lset-out lam x hx)

  -- THE SEQUENCES.  Devlin's finite sequences; here the Kuratowski
  -- pair, which is what every code in this coding is built from.
  pr∈λ : (x y : S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ y ∈ˢ Lset lam ⟩
       → ⟨ pr x y ∈ˢ Lset lam ⟩
  pr∈λ x y hx hy = PT.rec (snd (pr x y ∈ˢ Lset lam))
    (λ px → PT.rec (snd (pr x y ∈ˢ Lset lam)) (both px) (at y hy))
    (at x hx)
    where
    climb : (σ : S) → ⟨ σ ∈ˢ lam ⟩ → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ y ∈ˢ Lset σ ⟩
          → ⟨ pr x y ∈ˢ Lset lam ⟩
    climb σ σ∈ hxσ hyσ =
      Lset-mono {α = lam} {β = sucV (sucV σ)}
        (succλ (sucV σ) (succλ σ σ∈)) {x = pr x y}
        (pr∈Lset-suc σ x y hxσ hyσ)
    both : At x → At y → ⟨ pr x y ∈ˢ Lset lam ⟩
    both (δ , (δ∈ , hxδ)) (ε , (ε∈ , hyε)) =
      Sum.rec
        (λ p → climb (sucV ε) (succλ ε ε∈)
                 (Lset-mono {α = sucV ε} {β = sucV δ} p {x = x} hxδ) hyε)
        (Sum.rec
          (λ q → climb (sucV ε) (succλ ε ε∈)
                   (subst (λ w → ⟨ x ∈ˢ Lset w ⟩) q hxδ) hyε)
          (λ r → climb (sucV δ) (succλ δ δ∈) hxδ
                   (Lset-mono {α = sucV δ} {β = sucV ε} r {x = y} hyε)))
        (ord-tri (sucV δ) (suc-ord {A = δ} (mem-ord {A = lam} ordλ δ δ∈))
                 (sucV ε) (suc-ord {A = ε} (mem-ord {A = lam} ordλ ε ε∈)))

  -- The same at the model's own pair.
  prʟ∈λ : (a b : CS.S) → ⟨ fst a ∈ˢ Lset lam ⟩ → ⟨ fst b ∈ˢ Lset lam ⟩
        → ⟨ fst (prʟ a b) ∈ˢ Lset lam ⟩
  prʟ∈λ a b ha hb = subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (prʟ-fst a b))
    (pr∈λ (fst a) (fst b) ha hb)

  -- THE CARRIER, and the TRANSITIVITY.  One lemma each, both delivered.
  trans∈λ : {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ y ∈ˢ Lset lam ⟩
  trans∈λ {x} {y} = layer-trans (Lset-layer lam) {x = x} {y = y}

-- =====================================================================
-- BLOCK 2: THE `KFacts` VALUE.
--
-- Fourteen slots: the carrier, the bound, and the twelve arity tags.
-- The carrier is a stage BELOW the bound, which is the real shape:
-- `KFacts`' `carrierK` asks the bound to hold the carrier, and Devlin's
-- `K(u)` holds `{x | x ∈ u}` for exactly the same reason.
-- =====================================================================

module Value (lam : S) (ordλ : IsOrd lam)
             (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
             (gam : S) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ˢ lam ⟩) where

  module B = Bound lam ordλ succλ ∅∈λ

  env : CS.S ^ 14
  env = LsetS gam ordγ ∷ LsetS lam ordλ
      ∷ numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
      ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
      ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ []

  iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Fin 14
  iA = zero
  iK = suc zero
  i0 = suc (suc zero)
  i1 = suc (suc (suc zero))
  i2 = suc (suc (suc (suc zero)))
  i3 = suc (suc (suc (suc (suc zero))))
  i4 = suc (suc (suc (suc (suc (suc zero)))))
  i5 = suc (suc (suc (suc (suc (suc (suc zero))))))
  i6 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  i7 = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  i8 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  i9 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  i10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
  i11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

  facts : KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 env
  facts = record
    { tagEq0 = refl ; tagEq1 = refl ; tagEq2 = refl ; tagEq3 = refl
    ; tagEq4 = refl ; tagEq5 = refl ; tagEq6 = refl ; tagEq7 = refl
    ; tagEq8 = refl ; tagEq9 = refl ; tagEq10 = refl ; tagEq11 = refl
    ; numK0 = B.num∈λ 0 ; numK1 = B.num∈λ 1 ; numK2 = B.num∈λ 2
    ; numK3 = B.num∈λ 3 ; numK4 = B.num∈λ 4 ; numK5 = B.num∈λ 5
    ; numK6 = B.num∈λ 6 ; numK7 = B.num∈λ 7 ; numK8 = B.num∈λ 8
    ; numK9 = B.num∈λ 9 ; numK10 = B.num∈λ 10 ; numK11 = B.num∈λ 11
    ; innerK = λ k a ha → B.prʟ∈λ (numeralL k) a (B.num∈λ k) ha
    ; innerPairK = λ k a b ha hb →
        B.prʟ∈λ (numeralL k) (prʟ a b) (B.num∈λ k) (B.prʟ∈λ a b ha hb)
    ; pairK = λ a b ha hb → B.prʟ∈λ a b ha hb
    ; carrierK = λ v hv → Lset-mono {α = lam} {β = gam} γ∈λ {x = fst v} hv
    ; arityK = λ N v v∈N N∈K → B.trans∈λ {x = fst N} {y = fst v} v∈N N∈K }

-- =====================================================================
-- BLOCK 3: THE VALUE IS A VALUE (C-38).
--
-- `KFactsCons` (`src/L/Condensation.lagda.md:6039-6046`) is the tree's
-- OWN consumer, the one [LJ-1.165] measured as the only thing shaped
-- like a constructor and having no base case.  Applying it to `facts`
-- gives it that base case, and it typechecks only if `facts` is a
-- genuine `KFacts` at the record's own indices.
-- =====================================================================

  consed : (c : CS.S)
         → KFacts (suc iA) (suc iK) (suc i0) (suc i1) (suc i2) (suc i3)
             (suc i4) (suc i5) (suc i6) (suc i7) (suc i8) (suc i9)
             (suc i10) (suc i11) (c ∷ env)
  consed c = KFactsCons iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
               env c facts
