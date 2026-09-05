{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.71] probe A: can SatGraphAgree's frame instantiate
-- TwelveAgree?
--
-- The dispatch wires SatGraphAgree (src/L/Condensation.lagda.md:6760)
-- to instantiate TwelveAgree (src/L/Condensation.lagda.md:6412) at the
-- graph frame (f ∷ e ∷ d ∷ γ), so that twelve-out and twelve-back leave
-- SatGraphAgree's telescope.  TwelveAgree's telescope is the forty-seven
-- fact union stated at the twelve frame.  This probe carries
-- SatGraphAgree's telescope EXACTLY (all thirty-five parameters,
-- including twelve-out and twelve-back, so the frame is the master's
-- frame) and asks whether the frame can supply the telescope.
--
-- The answer is NO, and the first telescope fact already fails:
-- tagEq-refutes below is a machine-checked proof that the telescope's
-- tagEq statement is INCONSISTENT with the frame's own tagEq0, so no
-- term of that type exists at the frame and the instantiation cannot
-- go through.  The dispatch stops here per its pre-fixed abort
-- criterion.  tagEq0' and numK0' show the lifts are definitional where
-- the frame DOES supply the row facts; the obstruction is the general
-- form of tagEq (and of numK), not the slot lifts.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ171A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; _∧̇_; _≐_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( closedAt; domAt; appAt; prʟ; numeralL-inj )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Condensation {ℓ} lem using
  ( module KFactsNS; module SatGraphB )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Nat using ( _+_; znots )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The suc^6 lift of a slot at the graph frame (11 + n = 6 + (5 + n)).
six : ∀ {n} → Fin n → Fin (6 + n)
six i = suc (suc (suc (suc (suc (suc i)))))

-- =====================================================================
-- SATGRAPHAGREE'S TELESCOPE, VERBATIM
-- (src/L/Condensation.lagda.md:6760-6806).  The twelve-out and
-- twelve-back parameters are KEPT, so this frame is exactly the
-- master's frame and nothing is hidden.
-- =====================================================================
module Frame {n : ℕ} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (facts : KFactsNS.KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
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
  (codesK : (d e f : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (unCodesK : (d e f : S) → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (closedEntryK : (d e f : S) → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
                  → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                    × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
               → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                 × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
          → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (witK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
             (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
             ∧̇ (closedAt (suc (suc zero))
               ∧̇ (domAt (suc zero) (suc (suc zero))
                 ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                   ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  -- The graph frame's twelve-row environment is (f ∷ e ∷ d ∷ γ), and
  -- the KFacts record's slots sit six deep in it.  These two checks
  -- show the lifts are definitional where the frame DOES supply a row
  -- fact: tagEq0 and numK0 of the frame are tagEq 0 (six N0) and
  -- numK 0 of the telescope, definitionally.
  tagEq0' : (d e f : S)
          → fst (lookup (six N0) (f ∷ e ∷ d ∷ γ)) ≡ fst (numeralL 0)
  tagEq0' d e f = facts .KFactsNS.KFacts.tagEq0

  numK0' : (d e f : S)
         → ⟨ fst (numeralL 0) ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
  numK0' d e f = facts .KFactsNS.KFacts.numK0

  -- The other facts the frame supplies are the same definitional
  -- lifts: innerK, pairK, numK1, codesK and codesK-un.
  innerK' : (d e f : S) (k : ℕ) (p : S)
          → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
  innerK' d e f = facts .KFactsNS.KFacts.innerK

  pairK' : (d e f : S) (a b : S)
         → ⟨ fst (prʟ a b) ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
  pairK' d e f = facts .KFactsNS.KFacts.pairK

  num1K' : (d e f : S) → ⟨ fst (numeralL 1) ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
  num1K' d e f = facts .KFactsNS.KFacts.numK1

  codesK' : (d e f : S) (k : ℕ) (c ar a b : S)
          → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst ar ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
            × ⟨ fst a ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
            × ⟨ fst b ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
  codesK' d e f = codesK d e f

  codesK-un' : (d e f : S) (k : ℕ) (c ar a : S)
             → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
               × ⟨ fst a ∈ fst (lookup (six K) (f ∷ e ∷ d ∷ γ)) ⟩
  codesK-un' d e f = unCodesK d e f

  -- fst (numeralL 0) ≠ fst (numeralL 1), via the delivered
  -- numeralL-inj (L.Coding.Model:370-372).
  numeral0≠numeral1 : fst (numeralL 0) ≡ fst (numeralL 1) → Empty.⊥
  numeral0≠numeral1 e = znots (numeralL-inj (Σ≡Prop (λ v → snd (isL v)) e))

  -- THE REFUTATION.  TwelveAgree's first telescope fact
  -- (src/L/Condensation.lagda.md:6415) is
  --
  --   tagEq : (k : ℕ) (N : Fin (11 + n)) → fst (lookup N γ) ≡ fst (numeralL k)
  --
  -- at the twelve frame γ.  At the graph frame the KFacts record forces
  -- fst (lookup (six N0) (f ∷ e ∷ d ∷ γ)) ≡ fst (numeralL 0) (tagEq0),
  -- while tagEq 1 (six N0) forces the same slot to equal
  -- fst (numeralL 1).  The two together refute numeralL 0 ≡ numeralL 1.
  -- So the frame proves the telescope's tagEq type uninhabited, and no
  -- term of it exists to feed the instantiation.
  tagEq-refutes : (d e f : S)
                → ((k : ℕ) (N : Fin (11 + n)) → fst (lookup N (f ∷ e ∷ d ∷ γ)) ≡ fst (numeralL k))
                → Empty.⊥
  tagEq-refutes d e f tagEq =
    numeral0≠numeral1 (sym (tagEq0' d e f) ∙ tagEq 1 (six N0))

  -- The remaining forty telescope facts are absent from the frame's
  -- telescope: the frame carries KFacts (twenty-nine fields,
  -- src/L/Condensation.lagda.md:5677-5706) plus codesK, unCodesK,
  -- closedEntryK, domEntryK, domK and witK (above), and nothing else.
  -- TwelveAgree additionally demands valK, valK-un, t0eq, t1eq, t0K,
  -- tmKeyK, envK-mem, envK-neg, envK-top, envK-imp, envK-allin,
  -- entryK, arSubK-mem, arSubK-neg, arSubK-top, arSubK-imp,
  -- envInK-mem, envInK-neg, envInK-top, envInK-imp, valV, valW,
  -- wKfact, transK, subK₁-and, subK₀-and, subK₁-imp, subK₀-imp,
  -- someEnv, subK-neg, keyK-neg, succK, keyK-un, subK-un,
  -- consK-exist, consK-forall, succK-allin, keyK-allin, subK-allin,
  -- consK-allin (src/L/Condensation.lagda.md:6419-6590).  No term of
  -- those types is in the frame's context, and none is derivable from
  -- the frame's hypotheses: they are site facts about arbitrary
  -- values in K, and the frame's hypotheses do not constrain those
  -- values.  That part is INFERRED (absence, not machine-checked);
  -- the tagEq obstruction above is MEASURED.  numK is supplyable at
  -- k = 0..11 only (numK0' checks k = 0); the telescope demands all
  -- k : ℕ, and the frame's hypotheses say nothing about numeralL k for
  -- k > 11, so numK is also not supplyable as stated: INFERRED.
