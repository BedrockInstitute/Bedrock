{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.93] probe A: the association bridge, generic, and the
-- conjunct identity at the consumer's frame.
--
-- Two facts are established here, both machine-checked:
--
-- 1. Satisfaction of a conjunction is the product of satisfactions,
--    so a twelve-way conjunction associates freely.  The bridge
--    `to-left` / `to-right` below is generic in the twelve formulas
--    and in the environment; it is pure product reassociation.
--
-- 2. The consumer's SatGraphB.twelveB
--    (src/L/Condensation.lagda.md:2233-2254) is, definitionally, the
--    right-nested chain C0 ∧̇ (C1 ∧̇ ( ... C11)) whose conjuncts C0..C11
--    are written out below (consumerIsRight, by refl).  The
--    composer's twelveB (src/L/Condensation/TwelveAgree.lagda.md:270-271)
--    is the left-nested (p0b ∧̇ p1b) with p0b = LowerAgree.sixB
--    (:226-247) and p1b = UpperAgree.sixB (:216-235); those sixes are
--    the same C0..C11 texts, index for index, compared against the
--    source in the report.  The bridge instantiated at those texts
--    gives both directions at the consumer's environment.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ193A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Condensation {ℓ} lem
  using ( module SatGraphB; module Mem; module Eq; module And; module Or
        ; module Imp; module Neg; module Top; module Bot; module Exist
        ; module Forall; module AllIn; module ExIn )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The generic association bridge.  `γ ⊨ (φ ∧̇ ψ)` is definitionally
-- `(γ ⊨ φ) ⊓ (γ ⊨ ψ)`, and `⟨ A ⊓ B ⟩` is definitionally `⟨ A ⟩ × ⟨ B ⟩`
-- for the hProp algebra, so the bridge is pure product reassociation.
-- It is generic in the twelve formulas and in the environment; no
-- conjunct is named and no carrier enters.
module AssocBridge {n : ℕ} (γ : S ^ n)
  (C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ C₉ C₁₀ C₁₁ : Formula S n) where

  right-nested : Formula S n
  right-nested =
    C₀ ∧̇ (C₁ ∧̇ (C₂ ∧̇ (C₃ ∧̇ (C₄ ∧̇ (C₅ ∧̇ (C₆ ∧̇ (C₇ ∧̇ (C₈ ∧̇ (C₉ ∧̇ (C₁₀ ∧̇ C₁₁))))))))))

  left-nested : Formula S n
  left-nested =
    (C₀ ∧̇ (C₁ ∧̇ (C₂ ∧̇ (C₃ ∧̇ (C₄ ∧̇ C₅))))) ∧̇ (C₆ ∧̇ (C₇ ∧̇ (C₈ ∧̇ (C₉ ∧̇ (C₁₀ ∧̇ C₁₁)))))

  to-left : ⟨ γ ⊨ right-nested ⟩ → ⟨ γ ⊨ left-nested ⟩
  to-left h =
    ( ( h .fst
      , ( h .snd .fst
        , ( h .snd .snd .fst
          , ( h .snd .snd .snd .fst
            , ( h .snd .snd .snd .snd .fst
              , h .snd .snd .snd .snd .snd .fst )))))
    , ( h .snd .snd .snd .snd .snd .snd .fst
      , ( h .snd .snd .snd .snd .snd .snd .snd .fst
        , ( h .snd .snd .snd .snd .snd .snd .snd .snd .fst
          , ( h .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
            , ( h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
              , h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd ))))))

  to-right : ⟨ γ ⊨ left-nested ⟩ → ⟨ γ ⊨ right-nested ⟩
  to-right (a , b) =
    ( a .fst
    , ( a .snd .fst
      , ( a .snd .snd .fst
        , ( a .snd .snd .snd .fst
          , ( a .snd .snd .snd .snd .fst
            , ( a .snd .snd .snd .snd .snd
              , ( b .fst
                , ( b .snd .fst
                  , ( b .snd .snd .fst
                    , ( b .snd .snd .snd .fst
                      , ( b .snd .snd .snd .snd .fst
                        , b .snd .snd .snd .snd .snd )))))))))))

-- The consumer's twelve conjuncts, written out from
-- src/L/Condensation.lagda.md:2233-2254 (SatGraphB.twelveB).  K' in
-- the source is `suc (suc (suc (suc (suc (suc K)))))` (:2236-2238);
-- the texts below write that chain out, matching the composer's sixes.
module ConsumerSide (n : ℕ)
  (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where

  C₀ : Formula S (11 + n)
  C₀ = Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N0))))))
         (suc (suc (suc (suc (suc (suc K))))))
         (suc (suc (suc (suc (suc (suc t0))))))
         (suc (suc (suc (suc (suc (suc t1))))))

  C₁ : Formula S (11 + n)
  C₁ = Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N1))))))
         (suc (suc (suc (suc (suc (suc K))))))
         (suc (suc (suc (suc (suc (suc t0))))))
         (suc (suc (suc (suc (suc (suc t1))))))

  C₂ : Formula S (11 + n)
  C₂ = And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N2))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₃ : Formula S (11 + n)
  C₃ = Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N3))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₄ : Formula S (11 + n)
  C₄ = Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N4))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₅ : Formula S (11 + n)
  C₅ = Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N5))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₆ : Formula S (11 + n)
  C₆ = Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N6))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₇ : Formula S (11 + n)
  C₇ = Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N7))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₈ : Formula S (11 + n)
  C₈ = Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N8))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₉ : Formula S (11 + n)
  C₉ = Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
         (suc (suc (suc (suc (suc (suc N9))))))
         (suc (suc (suc (suc (suc (suc K))))))

  C₁₀ : Formula S (11 + n)
  C₁₀ = AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N10))))))
          (suc (suc (suc (suc (suc (suc K))))))
          (suc (suc (suc (suc (suc (suc t0))))))
          (suc (suc (suc (suc (suc (suc t1))))))

  C₁₁ : Formula S (11 + n)
  C₁₁ = ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
          (suc (suc (suc (suc (suc (suc N11))))))
          (suc (suc (suc (suc (suc (suc K))))))
          (suc (suc (suc (suc (suc (suc t0))))))
          (suc (suc (suc (suc (suc (suc t1))))))

  -- The consumer's formula is the right-nested chain of the twelve
  -- conjuncts, definitionally: the bridge's right-nested side IS
  -- SatGraphB.twelveB.
  consumerIsRight : SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                      N6 N7 N8 N9 N10 N11 t0 t1
                      ≡ C₀ ∧̇ (C₁ ∧̇ (C₂ ∧̇ (C₃ ∧̇ (C₄ ∧̇ (C₅ ∧̇ (C₆ ∧̇ (C₇ ∧̇ (C₈ ∧̇ (C₉ ∧̇ (C₁₀ ∧̇ C₁₁))))))))))
  consumerIsRight = refl

  -- The composer-side sixes are the same texts.  p0b-copy and p1b-copy
  -- transcribe LowerAgree.sixB (LowerAgree.lagda.md:226-247) and
  -- UpperAgree.sixB (UpperAgree.lagda.md:216-235) at the consumer's
  -- slots; the report compares the transcripts against the source.
  p0b-copy : Formula S (11 + n)
  p0b-copy = C₀ ∧̇ (C₁ ∧̇ (C₂ ∧̇ (C₃ ∧̇ (C₄ ∧̇ C₅))))

  p1b-copy : Formula S (11 + n)
  p1b-copy = C₆ ∧̇ (C₇ ∧̇ (C₈ ∧̇ (C₉ ∧̇ (C₁₀ ∧̇ C₁₁))))

-- The bridge instantiated at the consumer's environment, both
-- directions, at the real conjuncts and the real SatGraphB.twelveB.
-- This is the association half of the join; the pack half is probe B.
module ConsumerJoin (n : ℕ)
  (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n)) (d e f : S) where

  module CS = ConsumerSide n w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
  module B = AssocBridge {11 + n} (f ∷ e ∷ d ∷ γ)
              CS.C₀ CS.C₁ CS.C₂ CS.C₃ CS.C₄ CS.C₅ CS.C₆ CS.C₇ CS.C₈ CS.C₉ CS.C₁₀ CS.C₁₁

  -- twelve-out's association half: composer's left-nested side to the
  -- consumer's right-nested SatGraphB.twelveB.
  to-consumer : ⟨ (f ∷ e ∷ d ∷ γ) ⊨ (CS.p0b-copy ∧̇ CS.p1b-copy) ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  to-consumer = B.to-right

  -- twelve-back's association half: consumer's right-nested
  -- SatGraphB.twelveB to the composer's left-nested side.
  from-consumer : ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩
                → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ (CS.p0b-copy ∧̇ CS.p1b-copy) ⟩
  from-consumer = B.to-left
