{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.306] COMPAT PROBE, owner's ruling 2026-08-15.  The generic port
-- REPLACES the class-specific original, so a consumer that names the
-- family at the class carrier must still be served.  This probe applies
-- `GenAgree` at the class (`isL`, the six `L.Axioms.Numerals` supplies,
-- the application [LJ-1.210] already measured for `GenModel` itself at
-- `ProbeLJ1210Inst.agda:47`) and checks, by `refl`, that the applied
-- names ARE the delivered chapter's names, term for term.
--
-- The names checked are the ones the EXTERNAL consumers reach:
--   `src/L/Condensation/LowerAgree.lagda.md:33-35`  (rows Mem Eq And Or
--     Imp Neg; MemAgree EqAgree AndAgree OrAgree ImpAgree NegAgree;
--     envHypB2)
--   `src/L/Condensation/UpperAgree.lagda.md:33-36`  (rows Top Bot Exist
--     Forall AllIn ExIn; the same six Agree; succU keyU)
--   `src/L/Condensation/TwelveAgree.lagda.md:31`    (succU keyU)
--   `src/L/Coding/EnvSupply.lagda.md:47`           (envSetB, EnvSet)
-- plus the ten re-stated `L.Coding.Shape` names, the internal-consumer
-- representatives `TagAgree` and `BotAgree`, and `tagBS`.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-306.ProbeCompat {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; envOverAt; tagAtL; botClauseAt; topClauseAt )
open import L.Coding.Shape {ℓ}
  using ( binForm; unForm; isTmAt; bothTm; fstTm; noneB; noneU; zeroPay
        ; shapes; shapedAt )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )

import L.Condensation
import LJ-1-210.GenModel
import LJ-1-306.GenAgree

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module Orig = L.Condensation {ℓ} lem
module Fam = LJ-1-306.GenAgree {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
module GMc = LJ-1-210.GenModel {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst

-- =====================================================================
-- 0.  THE FORMULA DELIVERIES THE FAMILY'S STATEMENTS NAME, generic
-- against delivered.  [LJ-1.210] measured nine of these; these are
-- the ones the `Agree` statements reach.
-- =====================================================================

chk-GMc-tagAtL : ∀ {n : ℕ} (s : Fin n) (k : ℕ) (x : Fin n)
               → GMc.tagAtL s k x ≡ tagAtL s k x
chk-GMc-tagAtL s k x = refl

chk-GMc-botClauseAt : ∀ {n : ℕ} (C T : Fin n)
                   → GMc.botClauseAt C T ≡ botClauseAt C T
chk-GMc-botClauseAt C T = refl

chk-GMc-topClauseAt : ∀ {n : ℕ} (C T : Fin n)
                   → GMc.topClauseAt C T ≡ topClauseAt C T
chk-GMc-topClauseAt C T = refl

chk-GMc-envOverAt : ∀ {n : ℕ} (e ar B : Fin n)
                  → GMc.envOverAt e ar B ≡ envOverAt e ar B
chk-GMc-envOverAt e ar B = refl

-- =====================================================================
-- 1.  THE TWELVE ROW MODULES.  First field of each, both sides.
-- =====================================================================

chk-Bot : ∀ {m : ℕ} (C T B N K : Fin m)
        → Orig.Bot.botBndAt C T B N K ≡ Fam.Bot.botBndAt C T B N K
chk-Bot C T B N K = refl

chk-Top : ∀ {m : ℕ} (C T B N K : Fin m)
        → Orig.Top.topBndAt C T B N K ≡ Fam.Top.topBndAt C T B N K
chk-Top C T B N K = refl

chk-Neg : ∀ {m : ℕ} (C T B N K : Fin m)
        → Orig.Neg.subN C T B N K ≡ Fam.Neg.subN C T B N K
chk-Neg C T B N K = refl

chk-Forall : ∀ {m : ℕ} (C T B N K : Fin m)
           → Orig.Forall.subF C T B N K ≡ Fam.Forall.subF C T B N K
chk-Forall C T B N K = refl

chk-And : ∀ {m : ℕ} (C T B N K : Fin m)
        → Orig.And.subA C T B N K ≡ Fam.And.subA C T B N K
chk-And C T B N K = refl

chk-Or : ∀ {m : ℕ} (C T B N K : Fin m)
       → Orig.Or.subO C T B N K ≡ Fam.Or.subO C T B N K
chk-Or C T B N K = refl

chk-Imp : ∀ {m : ℕ} (C T B N K : Fin m)
        → Orig.Imp.subI C T B N K ≡ Fam.Imp.subI C T B N K
chk-Imp C T B N K = refl

chk-Exist : ∀ {m : ℕ} (C T B N K : Fin m)
          → Orig.Exist.subE C T B N K ≡ Fam.Exist.subE C T B N K
chk-Exist C T B N K = refl

chk-Mem : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
        → Orig.Mem.bodyM C T B N K t0 t1 ≡ Fam.Mem.bodyM C T B N K t0 t1
chk-Mem C T B N K t0 t1 = refl

chk-Eq : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
       → Orig.Eq.bodyE C T B N K t0 t1 ≡ Fam.Eq.bodyE C T B N K t0 t1
chk-Eq C T B N K t0 t1 = refl

chk-AllIn : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
          → Orig.AllIn.subA C T B N K t0 t1
          ≡ Fam.AllIn.subA C T B N K t0 t1
chk-AllIn C T B N K t0 t1 = refl

chk-ExIn : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
         → Orig.ExIn.subE C T B N K t0 t1
         ≡ Fam.ExIn.subE C T B N K t0 t1
chk-ExIn C T B N K t0 t1 = refl

-- =====================================================================
-- 2.  THE SYNTAX THE EXTERNAL CONSUMERS NAME.
-- =====================================================================

chk-envHypB2 : ∀ {m : ℕ} (B K : Fin m)
             → Orig.envHypB2 B K ≡ Fam.envHypB2 B K
chk-envHypB2 B K = refl

chk-envSetB : ∀ {n : ℕ} (E ar B K : Fin n)
            → Orig.envSetB E ar B K ≡ Fam.envSetB E ar B K
chk-envSetB E ar B K = refl

chk-succU : ∀ {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
              (E ya yc a ar c : S)
          → Fam.succU C T B N K γ E ya yc a ar c
          ≡ Orig.succU C T B N K γ E ya yc a ar c
chk-succU C T B N K γ E ya yc a ar c = refl

chk-keyU : ∀ {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
             (E ya yc a ar c : S)
         → Fam.keyU C T B N K γ E ya yc a ar c
         ≡ Orig.keyU C T B N K γ E ya yc a ar c
chk-keyU C T B N K γ E ya yc a ar c = refl

chk-tagBS : ∀ {n : ℕ} (s tag x K : Fin n)
          → Orig.tagBS s tag x K ≡ Fam.tagBS s tag x K
chk-tagBS s tag x K = refl

-- =====================================================================
-- 3.  THE TEN RE-STATED `L.Coding.Shape` NAMES.
-- =====================================================================

chk-binForm : ∀ {n : ℕ} (k : ℕ) (rel : Formula S (4 + n))
            → Fam.binForm k rel ≡ binForm k rel
chk-binForm k rel = refl

chk-unForm : ∀ {n : ℕ} (k : ℕ) (rel : Formula S (3 + n))
           → Fam.unForm k rel ≡ unForm k rel
chk-unForm k rel = refl

chk-isTmAt : ∀ {n : ℕ} (t N A : Fin n)
           → Fam.isTmAt t N A ≡ isTmAt t N A
chk-isTmAt t N A = refl

chk-bothTm : ∀ {n : ℕ} (A : Fin n) → Fam.bothTm A ≡ bothTm A
chk-bothTm A = refl

chk-fstTm : ∀ {n : ℕ} (A : Fin n) → Fam.fstTm A ≡ fstTm A
chk-fstTm A = refl

chk-noneB : ∀ {n : ℕ} → Fam.noneB {n} ≡ noneB {n}
chk-noneB = refl

chk-noneU : ∀ {n : ℕ} → Fam.noneU {n} ≡ noneU {n}
chk-noneU = refl

chk-zeroPay : ∀ {n : ℕ} → Fam.zeroPay {n} ≡ zeroPay {n}
chk-zeroPay = refl

chk-shapes : ∀ {n : ℕ} (A : Fin n) → Fam.shapes A ≡ shapes A
chk-shapes A = refl

chk-shapedAt : ∀ {n : ℕ} (C A : Fin n) → Fam.shapedAt C A ≡ shapedAt C A
chk-shapedAt C A = refl

-- =====================================================================
-- 4.  THE `Agree` MODULES AS CONSUMERS SEE THEM.  On-the-nose term
-- identity FAILS at the adequacy layer (stuck `lookup-fst` neutrals,
-- recorded in the report), so the check here is the consumer's own
-- situation: the statement at the ORIGINAL names, the term from the
-- GENERIC module.  `TagAgree` is `EnvOneAgree`'s internal name,
-- `BotAgree` is `UpperAgree`'s external one.
-- =====================================================================

served-TagAgree-out : ∀ {n : ℕ} (s tag x K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (h : ⟨ γ ⊨ tagAtL s k x ⟩)
  → ⟨ γ ⊨ Orig.tagBS s tag x K ⟩
served-TagAgree-out s tag x K γ k tagEq numK h =
  Fam.TagAgree.out s tag x K γ k tagEq numK h

served-TagAgree-back : ∀ {n : ℕ} (s tag x K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (h : ⟨ γ ⊨ Orig.tagBS s tag x K ⟩)
  → ⟨ γ ⊨ tagAtL s k x ⟩
served-TagAgree-back s tag x K γ k tagEq numK h =
  Fam.TagAgree.back s tag x K γ k tagEq numK h

served-BotAgree-out : ∀ {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 7))
  (numK : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 7) a) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (h : ⟨ γ ⊨ botClauseAt C T ⟩)
  → ⟨ γ ⊨ Orig.Bot.botBndAt C T B N K ⟩
served-BotAgree-out C T B N K γ tagEq numK innerK codesK valK h =
  Fam.BotAgree.bot-out C T B N K γ tagEq numK innerK codesK valK h

served-BotAgree-in : ∀ {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 7))
  (numK : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 7) a) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (h : ⟨ γ ⊨ Orig.Bot.botBndAt C T B N K ⟩)
  → ⟨ γ ⊨ botClauseAt C T ⟩
served-BotAgree-in C T B N K γ tagEq numK innerK codesK valK h =
  Fam.BotAgree.bot-in C T B N K γ tagEq numK innerK codesK valK h

-- =====================================================================
-- 5.  `EnvSet`, the module `L.Coding.EnvSupply` reaches.  Both fields
-- are formula-valued, so the stronger `refl` form applies.
-- =====================================================================

chk-EnvSet-φB : ∀ {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩)
  (ar∈K : ⟨ fst (lookup ar γ) ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  → (Orig.EnvSet.φB E ar B K γ arityK E∈K ar∈K envInK)
    ≡ (Fam.EnvSet.φB E ar B K γ arityK E∈K ar∈K envInK)
chk-EnvSet-φB E ar B K γ arityK E∈K ar∈K envInK = refl

chk-EnvSet-φ : ∀ {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩)
  (ar∈K : ⟨ fst (lookup ar γ) ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  → (Orig.EnvSet.φ E ar B K γ arityK E∈K ar∈K envInK)
    ≡ (Fam.EnvSet.φ E ar B K γ arityK E∈K ar∈K envInK)
chk-EnvSet-φ E ar B K γ arityK E∈K ar∈K envInK = refl
