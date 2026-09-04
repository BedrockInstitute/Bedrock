# The row agreements, re-tied

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.LevelRows {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇∈; ∀̇∈; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )
open import L.Coding.Model {ℓ} using
  ( prAtL; prAtL-adequate; appAt; appAt-adequate; prʟ; prʟ-fst
  ; consAtL; envOverAt; envSetAt; extAt-out; extAt-in; tmValAt; tmValAt-out
  ; subValAt; subValAt-adequate; subValSuccAt; subValSuccAt-adequate
  ; memClauseAt; eqClauseAt; forallClauseAt; existClauseAt
  ; allInClauseAt; exInClauseAt; binClauseAt; propRel
  ; interAt; unionAt; extAt
  ; arityTagAtL; arityTagPairAtL
  ; arityTagAtL-adequate; arityTagPairAtL-adequate; tagAtL-adequate; tagAtL
  ; body∀; body∃; bodyAll; bodyEx; atomBody; bndRel; quantRel; unClauseAt )
open import L.Condensation {ℓ} lem using
  ( module Mem; module Eq; module And; module Or; module Exist; module Forall
  ; module AllIn; module ExIn; module EnvSet
  ; module UnaryShape; module BinaryShape; module GraphEntry; module ChainZ
  ; module TmVal; module SubValB2T; module SubValSuccB2T
  ; extAtB→extAt; extAtB
  ; arTagB; arTagPairB; subValB; subValSuccB; envHypU; envHypB2; envHypB2T
  ; propBodyB; binFullAt; tmValB; atomBodyB; unFullAt; interB; unionB )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( cong₂; transport )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )
open import V.Model {ℓ} using ( pair-singleton )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The class-carrier reading, as src/L/Condensation.lagda.md:76-77.
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module CS = hPropStructure 𝒮ʟ

-- The pair chain of src/L/Condensation.lagda.md `ChainZ`, at a value.
module Chain (Kv : V ℓ)
             (transK : (x y : V ℓ) → ⟨ x ∈ Kv ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ Kv ⟩) where

  -- pr x y = ⁅ ⁅ x ⁆s , ⁅ x , y ⁆ ⁆.
  sgl∈pr : (x y : V ℓ) → ⟨ ⁅ x ⁆s ∈ pr x y ⟩
  sgl∈pr x y = ∈∈ₛ {a = ⁅ x ⁆s} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x ⁆s .snd ∣ inl refl ∣₁)

  pair∈pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
  pair∈pr x y = ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)

  x∈sgl : (x : V ℓ) → ⟨ x ∈ ⁅ x ⁆s ⟩
  x∈sgl x = subst (λ u → ⟨ x ∈ u ⟩) (pair-singleton x)
    (∈∈ₛ {a = x} {b = ⁅ x , x ⁆} .snd (pairing-ax x x x .snd ∣ inl refl ∣₁))

  y∈pair : (x y : V ℓ) → ⟨ y ∈ ⁅ x , y ⁆ ⟩
  y∈pair x y = ∈∈ₛ {a = y} {b = ⁅ x , y ⁆} .snd
    (pairing-ax x y y .snd ∣ inr refl ∣₁)

  -- From pr x y ∈ z ∈ K, both components lie in K.
  fstK : (z x y : V ℓ) → ⟨ z ∈ Kv ⟩ → ⟨ pr x y ∈ z ⟩ → ⟨ x ∈ Kv ⟩
  fstK z x y zK p =
    transK ⁅ x ⁆s x (transK (pr x y) ⁅ x ⁆s (transK z (pr x y) zK p) (sgl∈pr x y))
      (x∈sgl x)

  sndK : (z x y : V ℓ) → ⟨ z ∈ Kv ⟩ → ⟨ pr x y ∈ z ⟩ → ⟨ y ∈ Kv ⟩
  sndK z x y zK p =
    transK ⁅ x , y ⁆ y (transK (pr x y) ⁅ x , y ⁆ (transK z (pr x y) zK p) (pair∈pr x y))
      (y∈pair x y)

  -- From pr x y ∈ K, both components lie in K.
  prK-fst : (x y : V ℓ) → ⟨ pr x y ∈ Kv ⟩ → ⟨ x ∈ Kv ⟩
  prK-fst x y p = transK ⁅ x ⁆s x (transK (pr x y) ⁅ x ⁆s p (sgl∈pr x y)) (x∈sgl x)

  prK-snd : (x y : V ℓ) → ⟨ pr x y ∈ Kv ⟩ → ⟨ y ∈ Kv ⟩
  prK-snd x y p = transK ⁅ x , y ⁆ y (transK (pr x y) ⁅ x , y ⁆ p (pair∈pr x y)) (y∈pair x y)


-- The value of a term in an environment lying in K lies in K: a
-- variable's value is an entry of the environment, a constant's is a
-- component of the term code.
tmVal-K : (Kv : V ℓ) (transK : (x y : V ℓ) → ⟨ x ∈ Kv ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ Kv ⟩)
        → ∀ {n} (γ : CS.S ^ n) (t e v : Fin n)
        → ⟨ fst (lookup t γ) ∈ Kv ⟩ → ⟨ fst (lookup e γ) ∈ Kv ⟩
        → ⟨ γ ⊨ tmValAt t e v ⟩ → ⟨ fst (lookup v γ) ∈ Kv ⟩
tmVal-K Kv transK γ t e v tK eK h =
  PT.rec (snd (fst (lookup v γ) ∈ Kv)) go (tmValAt-out t e v γ h)
  where
  module Z = Chain Kv transK
  go : (Σ[ k ∈ CS.S ] ((fst (lookup t γ) ≡ pr (# 1) (fst k))
          × ⟨ pr (fst k) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩))
     ⊎ (fst (lookup t γ) ≡ pr (# 0) (fst (lookup v γ)))
     → ⟨ fst (lookup v γ) ∈ Kv ⟩
  go (inl (k , (_ , mem))) = Z.sndK (fst (lookup e γ)) (fst k) (fst (lookup v γ)) eK mem
  go (inr q) = Z.prK-snd (# 0) (fst (lookup v γ)) (subst (λ u → ⟨ u ∈ Kv ⟩) q tK)


-- =====================================================================
-- THE EIGHT ROW AGREEMENTS RE-TIED.  src/L/Condensation.lagda.md
-- states its And, Or, Forall, Exist, Mem, Eq, AllIn and ExIn
-- agreements with ties that quantify over ARBITRARY sets (`someEnv`
-- over any arity, `consK` and the term-value ties over any set), and
-- no Δ₀ pin on a bound supplies those.  The story-to-machine
-- direction of each is copied here with the tie stated at the site
-- that holds it: the arity is a numeral, the environment is a member
-- of the row's environment set, the extended environment is an
-- environment.  The bodies are Condensation's; only the telescopes
-- and the threading of the site facts change.
-- =====================================================================

-- The atom leaf (Mem, Eq): the term values lie in K because the
-- environment does (it is a member of E ∈ K) and the term codes do.
module AtomLeaf′ {m : ℕ} (E yc b a ar c₀ : CS.S) (γ : CS.S ^ m)
  (t0 t1 K : Fin m)
  (transK : (x y : V ℓ) → ⟨ x ∈ fst (lookup K γ) ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (bK : ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (EK : ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (cmp : Formula CS.S (9 + m)) where

  arityK : (N v : CS.S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
         → ⟨ fst v ∈ fst (lookup K γ) ⟩
  arityK N v h hN = transK (fst N) (fst v) hN h

  bodyS : Formula CS.S (7 + m)
  bodyS = atomBodyB t0 t1 K cmp

  bodyM : Formula CS.S (7 + m)
  bodyM = atomBody cmp

  module Z = ChainZ {m} K γ arityK

  keyK-of : (z v w : CS.S) (c : Fin (9 + m))
          → ⟨ fst (lookup c (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ))
              ∈ fst (lookup K γ) ⟩
          → (k : CS.S)
          → ⟨ (k ∷ w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
               tagAtL (suc c) 1 zero ⟩
          → ⟨ fst k ∈ fst (lookup K γ) ⟩
  keyK-of z v w c cK k ht =
    let γ' : CS.S ^ (9 + m)
        γ' = w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ
        tagEq : fst (lookup c γ') ≡ pr (# 1) (fst k)
        tagEq = transport (cong fst (tagAtL-adequate (suc c) 1 zero (k ∷ γ'))) ht
        pʟ : fst (prʟ (numeralL 1) k) ≡ pr (# 1) (fst k)
        pʟ = prʟ-fst (numeralL 1) k ∙ cong₂ pr (numeralL-fst 1) refl
        pℓ : fst (pairʟ (numeralL 1) k) ≡ ⁅ # 1 , fst k ⁆
        pℓ = pairʟ-fst (numeralL 1) k ∙ cong₂ ⁅_,_⁆ (numeralL-fst 1) refl
        pair∈K : ⟨ fst (prʟ (numeralL 1) k) ∈ fst (lookup K γ) ⟩
        pair∈K = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (tagEq ∙ sym pʟ) cK
    in arityK (pairʟ (numeralL 1) k) k
         (subst (λ w → ⟨ fst k ∈ w ⟩) (sym pℓ) (Z.b∈pair (# 1) (fst k)))
         (arityK (prʟ (numeralL 1) k) (pairʟ (numeralL 1) k)
           (subst (λ w → ⟨ fst (pairʟ (numeralL 1) k) ∈ w ⟩) (sym pʟ)
             (subst (λ w → ⟨ w ∈ pr (# 1) (fst k) ⟩) (sym pℓ)
               (Z.pair∈pr (# 1) (fst k))))
           pair∈K)

  vK : (z v : CS.S) → Type (ℓ-suc ℓ)
  vK z v =
    ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                      (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩

  wK : (z v w : CS.S) → Type (ℓ-suc ℓ)
  wK z v w =
    ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                      (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩

  cSat : (z v w : CS.S) → Type (ℓ-suc ℓ)
  cSat z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ cmp ⟩

  tVS : (z v w : CS.S) → Type (ℓ-suc ℓ)
  tVS z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc (suc zero))))))
               (suc (suc zero))
               (suc zero)
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tWS : (z v w : CS.S) → Type (ℓ-suc ℓ)
  tWS z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc zero)))))
               (suc (suc zero))
               zero
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tVM : (z v w : CS.S) → Type (ℓ-suc ℓ)
  tVM z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                (suc (suc zero))
                (suc zero) ⟩

  tWM : (z v w : CS.S) → Type (ℓ-suc ℓ)
  tWM z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc zero)))))
                (suc (suc zero))
                zero ⟩

  -- THE TERM-VALUE TIES, DERIVED: the environment z is a member of E.
  valK : (z v w : CS.S) → ⟨ fst z ∈ fst E ⟩ → tVM z v w → vK z v
  valK z v w zE hv =
    tmVal-K (fst (lookup K γ)) transK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)
      (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) (suc zero)
      aK (transK (fst E) (fst z) EK zE) hv

  valW : (z v w : CS.S) → ⟨ fst z ∈ fst E ⟩ → tWM z v w → wK z v w
  valW z v w zE hw =
    tmVal-K (fst (lookup K γ)) transK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)
      (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) zero
      bK (transK (fst E) (fst z) EK zE) hw

  tmV-out : (z v w : CS.S) → tVS z v w → tVM z v w
  tmV-out z v w =
    TmVal.out {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc zero))
      (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq

  tmW-out : (z v w : CS.S) → tWS z v w → tWM z v w
  tmW-out z v w =
    TmVal.out {m = 9 + m}
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero))
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq

  tmV-in : (z v w : CS.S) → tVM z v w → tVS z v w
  tmV-in z v w =
    TmVal.in' {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc zero))
      (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z v w (suc (suc (suc (suc (suc (suc zero)))))) aK k ht)
      num1K

  tmW-in : (z v w : CS.S) → tWM z v w → tWS z v w
  tmW-in z v w =
    TmVal.in' {m = 9 + m}
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero))
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z v w (suc (suc (suc (suc (suc zero))))) bK k ht)
      num1K

  drop-w : (z v : CS.S) → Σ CS.S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w)))
                        → ∥ Σ CS.S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁
  drop-w z v (w , (wK , (hv , (hw , hc)))) =
    ∣ w , (tmV-out z v w hv , (tmW-out z v w hw , hc)) ∣₁

  drop-v : (z : CS.S)
         → Σ CS.S (λ v → vK z v × ∥ Σ CS.S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁)
         → ∥ Σ CS.S (λ v → ∥ Σ CS.S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁) ∥₁
  drop-v z (v , (vK , h)) = ∣ v , PT.rec squash₁ (drop-w z v) h ∣₁

  fwd : (z : CS.S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyS ⟩
                   → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyM ⟩
  fwd z h = h .fst , PT.rec squash₁ (drop-v z) (h .snd)

  lift-w : (z v : CS.S) → ⟨ fst z ∈ fst E ⟩
         → Σ CS.S (λ w → tVM z v w × (tWM z v w × cSat z v w))
         → ∥ Σ CS.S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁
  lift-w z v zE (w , (hv , (hw , hc))) =
    ∣ w , ( valW z v w zE hw
          , ( tmV-in z v w hv , ( tmW-in z v w hw , hc ) ) ) ∣₁

  vK-lift : (z v : CS.S) → ⟨ fst z ∈ fst E ⟩
          → ∥ Σ CS.S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁
          → vK z v
  vK-lift z v zE h = PT.rec
    (snd (fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                          (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ))))
    (λ { (w , (hv , _)) → valK z v w zE hv }) h

  lift-v : (z : CS.S) → ⟨ fst z ∈ fst E ⟩
         → Σ CS.S (λ v → ∥ Σ CS.S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁)
         → ∥ Σ CS.S (λ v → vK z v × ∥ Σ CS.S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁) ∥₁
  lift-v z zE (v , h) = ∣ v , (vK-lift z v zE h , PT.rec squash₁ (lift-w z v zE) h) ∣₁

  bwd : (z : CS.S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyM ⟩
                   → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyS ⟩
  bwd z h = h .fst , PT.rec squash₁ (lift-v z (h .fst)) (h .snd)


-- The Mem row, re-tied.
module MemAgree′ {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : CS.S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (transK : (x y : V ℓ) → ⟨ x ∈ fst (lookup K γ) ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (envK : (yc b a ar c E : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (yc b a ar c E : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : CS.S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  private
    φB : Formula CS.S m
    φB = Mem.memBndAt C T B N K t0 t1

    cmp : Formula CS.S (9 + m)
    cmp = var (suc zero) ∈̇ var zero

  arityK : (N' v : CS.S) → ⟨ fst v ∈ fst N' ⟩ → ⟨ fst N' ∈ fst (lookup K γ) ⟩
         → ⟨ fst v ∈ fst (lookup K γ) ⟩
  arityK N' v h hN = transK (fst N') (fst v) hN h

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ memClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc E hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 0 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        EK = envK yc b a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc b a ar c E arK arNum)
        henv = E'.back hE
        module L = AtomLeaf′ E yc b a ar c γ t0 t1 K
                     transK aK bK EK t0eq t1eq t0K num1K cmp
        hb = h c c∈ ar arK a aK b bK yc ycK shB hc E EK henv
    in extAtB→extAt (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

-- The Eq row, re-tied.
module EqAgree′ {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : CS.S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 1))
  (numK : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 1) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (transK : (x y : V ℓ) → ⟨ x ∈ fst (lookup K γ) ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 1) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 1) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (envK : (yc b a ar c E : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (yc b a ar c E : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : CS.S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  private
    φB : Formula CS.S m
    φB = Eq.eqBndAt C T B N K t0 t1

    cmp : Formula CS.S (9 + m)
    cmp = var (suc zero) ≐ var zero

  arityK : (N' v : CS.S) → ⟨ fst v ∈ fst N' ⟩ → ⟨ fst N' ∈ fst (lookup K γ) ⟩
         → ⟨ fst v ∈ fst (lookup K γ) ⟩
  arityK N' v h hN = transK (fst N') (fst v) hN h

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ eqClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc E hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 1 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K 1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        EK = envK yc b a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc b a ar c E arK arNum)
        henv = E'.back hE
        module L = AtomLeaf′ E yc b a ar c γ t0 t1 K
                     transK aK bK EK t0eq t1eq t0K num1K cmp
        hb = h c c∈ ar arK a aK b bK yc ycK shB hc E EK henv
    in extAtB→extAt (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb


-- The two bounded bodies, at the slots they read.
module BndBody {m : ℕ} (B t0 t1 K : Fin m) where

  bodyS : Formula CS.S (8 + m)
  bodyS =
    (var zero ∈̇ var (suc zero))
    ∧̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
        (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ⇒̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))
            ((var zero ∈̇ var (suc zero))
            ⇒̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))
                (consAtL zero (suc zero) (suc (suc (suc zero)))
                ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero)))))))))

  bodySx : Formula CS.S (8 + m)
  bodySx =
    (var zero ∈̇ var (suc zero))
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
        (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))
            ((var zero ∈̇ var (suc zero))
            ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))
                (consAtL zero (suc zero) (suc (suc (suc zero)))
                ∧̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero)))))))))


-- The bounded-quantifier leaf (AllIn, ExIn): the term value lies in K
-- because the environment does; the extended environment lies in K
-- because it is an environment of the next arity, which the site
-- supplies as `consK` from the tower.
module BndLeaf′ {m : ℕ} (B t0 t1 K : Fin m) (E ya yc b a ar c : CS.S) (γ : CS.S ^ m)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (transK : (x y : V ℓ) → ⟨ x ∈ fst (lookup K γ) ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (EK : ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (hE : ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
          envSetAt zero (suc (suc (suc (suc (suc zero)))))
                    (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩)
  (consK : (z w x e' : CS.S)
           → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
           → ⟨ fst x ∈ fst (lookup B γ) ⟩
           → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
           → ⟨ fst e' ∈ fst (lookup K γ) ⟩)
  where

  arityK : (N v : CS.S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
         → ⟨ fst v ∈ fst (lookup K γ) ⟩
  arityK N v h hN = transK (fst N) (fst v) hN h

  bodyS : Formula CS.S (8 + m)
  bodyS = BndBody.bodyS B t0 t1 K

  bodyM : Formula CS.S (8 + m)
  bodyM = bodyAll B

  module Z = ChainZ {m} K γ arityK

  -- The environment z, a member of E, is an environment.
  zOv : (z : CS.S) → ⟨ fst z ∈ fst E ⟩
      → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
          envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
  zOv z zE = extAt-out zero
    (envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                    (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))
    (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) hE z zE

  keyK-of : (z w : CS.S) (c₀ : Fin (9 + m))
          → ⟨ fst (lookup c₀ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))
              ∈ fst (lookup K γ) ⟩
          → (k : CS.S)
          → ⟨ (k ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               tagAtL (suc c₀) 1 zero ⟩
          → ⟨ fst k ∈ fst (lookup K γ) ⟩
  keyK-of z w c₀ cK k ht =
    let γ' : CS.S ^ (9 + m)
        γ' = w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ
        tagEq : fst (lookup c₀ γ') ≡ pr (# 1) (fst k)
        tagEq = transport (cong fst (tagAtL-adequate (suc c₀) 1 zero (k ∷ γ'))) ht
        pʟ : fst (prʟ (numeralL 1) k) ≡ pr (# 1) (fst k)
        pʟ = prʟ-fst (numeralL 1) k ∙ cong₂ pr (numeralL-fst 1) refl
        pℓ : fst (pairʟ (numeralL 1) k) ≡ ⁅ # 1 , fst k ⁆
        pℓ = pairʟ-fst (numeralL 1) k ∙ cong₂ ⁅_,_⁆ (numeralL-fst 1) refl
        pair∈K : ⟨ fst (prʟ (numeralL 1) k) ∈ fst (lookup K γ) ⟩
        pair∈K = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (tagEq ∙ sym pʟ) cK
    in arityK (pairʟ (numeralL 1) k) k
         (subst (λ w → ⟨ fst k ∈ w ⟩) (sym pℓ) (Z.b∈pair (# 1) (fst k)))
         (arityK (prʟ (numeralL 1) k) (pairʟ (numeralL 1) k)
           (subst (λ w → ⟨ fst (pairʟ (numeralL 1) k) ∈ w ⟩) (sym pʟ)
             (subst (λ w → ⟨ w ∈ pr (# 1) (fst k) ⟩) (sym pℓ)
               (Z.pair∈pr (# 1) (fst k))))
           pair∈K)

  wK' : (z w : CS.S) → Type (ℓ-suc ℓ)
  wK' z w =
    ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                      (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  xB : (z w x : CS.S) → Type (ℓ-suc ℓ)
  xB z w x =
    ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))
                      (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  xW : (z w x : CS.S) → Type (ℓ-suc ℓ)
  xW z w x = ⟨ fst x ∈ fst w ⟩

  eK : (z w x e' : CS.S) → Type (ℓ-suc ℓ)
  eK z w x e' =
    ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
                      (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  cSat : (z w x e' : CS.S) → Type (ℓ-suc ℓ)
  cSat z w x e' =
    ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
        consAtL zero (suc zero) (suc (suc (suc zero))) ⟩

  ySat : (z w x e' : CS.S) → Type (ℓ-suc ℓ)
  ySat z w x e' =
    ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc zero)))))
                      (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  tVS : (z w : CS.S) → Type (ℓ-suc ℓ)
  tVS z w =
    ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc (suc zero))))))
               (suc zero)
               zero
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tVM : (z w : CS.S) → Type (ℓ-suc ℓ)
  tVM z w =
    ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero ⟩

  -- THE TERM-VALUE TIE, DERIVED.
  wK : (z w : CS.S) → ⟨ fst z ∈ fst E ⟩ → tVM z w → wK' z w
  wK z w zE h =
    tmVal-K (fst (lookup K γ)) transK (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
      (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) zero
      aK (transK (fst E) (fst z) EK zE) h

  tmOut : (z w : CS.S) → tVS z w → tVM z w
  tmOut z w =
    TmVal.out {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc zero)
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) t0eq t1eq

  tmIn : (z w : CS.S) → tVM z w → tVS z w
  tmIn z w =
    TmVal.in' {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc zero)
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z w (suc (suc (suc (suc (suc (suc zero)))))) aK k ht) num1K

  -- THE UNIVERSAL SHAPE (AllIn).
  all-fwd : (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyS ⟩
                       → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyM ⟩
  all-fwd z h = h .fst , (λ w tmAt x x∈B x∈w e' cons →
    h .snd w (wK z w (h .fst) tmAt) (tmIn z w tmAt) x x∈B x∈w e'
      (consK z w x e' (zOv z (h .fst)) x∈B cons) cons)

  all-bwd : (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyM ⟩
                       → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyS ⟩
  all-bwd z h = h .fst , (λ w wK' tmB x x∈B x∈w e' e'K cons →
    h .snd w (tmOut z w tmB) x x∈B x∈w e' cons)

  -- THE EXISTENTIAL SHAPE (ExIn).
  bodySx : Formula CS.S (8 + m)
  bodySx = BndBody.bodySx B t0 t1 K

  bodyMx : Formula CS.S (8 + m)
  bodyMx = bodyEx B

  ex-drop-e : (z w x : CS.S) → Σ CS.S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e'))
                             → ∥ Σ CS.S (λ e' → cSat z w x e' × ySat z w x e') ∥₁
  ex-drop-e z w x (e' , (eK , (c , y))) = ∣ e' , (c , y) ∣₁

  ex-drop-x : (z w : CS.S) → Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁))
                          → ∥ Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → cSat z w x e' × ySat z w x e') ∥₁)) ∥₁
  ex-drop-x z w (x , (x∈B , (x∈w , h))) = ∣ x , (x∈B , (x∈w , PT.rec squash₁ (ex-drop-e z w x) h)) ∣₁

  ex-drop-w : (z : CS.S) → Σ CS.S (λ w → wK' z w × (tVS z w × ∥ Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁)) ∥₁))
                         → ∥ Σ CS.S (λ w → tVM z w × ∥ Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → cSat z w x e' × ySat z w x e') ∥₁)) ∥₁) ∥₁
  ex-drop-w z (w , (wK , (h , hx))) =
    ∣ w , (tmOut z w h , PT.rec squash₁ (ex-drop-x z w) hx) ∣₁

  ex-fwd : (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodySx ⟩
                      → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyMx ⟩
  ex-fwd z h = h .fst , PT.rec squash₁ (ex-drop-w z) (h .snd)

  ex-lift-e : (z w x : CS.S) → ⟨ fst z ∈ fst E ⟩ → xB z w x
            → Σ CS.S (λ e' → cSat z w x e' × ySat z w x e')
            → ∥ Σ CS.S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁
  ex-lift-e z w x zE x∈B (e' , (c , y)) = ∣ e' , (consK z w x e' (zOv z zE) x∈B c , (c , y)) ∣₁

  ex-lift-x : (z w : CS.S) → ⟨ fst z ∈ fst E ⟩
            → Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → cSat z w x e' × ySat z w x e') ∥₁))
            → ∥ Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁)) ∥₁
  ex-lift-x z w zE (x , (x∈B , (x∈w , h))) =
    ∣ x , (x∈B , (x∈w , PT.rec squash₁ (ex-lift-e z w x zE x∈B) h)) ∣₁

  ex-lift-w : (z : CS.S) → ⟨ fst z ∈ fst E ⟩
            → Σ CS.S (λ w → tVM z w × ∥ Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → cSat z w x e' × ySat z w x e') ∥₁)) ∥₁)
            → ∥ Σ CS.S (λ w → wK' z w × (tVS z w × ∥ Σ CS.S (λ x → xB z w x × (xW z w x × ∥ Σ CS.S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁)) ∥₁)) ∥₁
  ex-lift-w z zE (w , (h , hx)) =
    ∣ w , (wK z w zE h , (tmIn z w h , PT.rec squash₁ (ex-lift-x z w zE) hx)) ∣₁

  ex-bwd : (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyMx ⟩
                      → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodySx ⟩
  ex-bwd z h = h .fst , PT.rec squash₁ (ex-lift-w z (h .fst)) (h .snd)

-- The shared telescope of the two bounded-quantifier rows.
module BndAgree′ {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : CS.S ^ m) (k : ℕ)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (transK : (x y : V ℓ) → ⟨ x ∈ fst (lookup K γ) ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ fst (lookup K γ) ⟩)
  (sucK : (x : CS.S) → ⟨ fst x ∈ fst (lookup K γ) ⟩ → ⟨ sucV (fst x) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (subK : (E ya yc b a ar c : CS.S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc (suc T)))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (E ya yc b a ar c : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (E ya yc b a ar c : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (consK : (E ya yc b a ar c : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z w x e' : CS.S)
           → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
           → ⟨ fst x ∈ fst (lookup B γ) ⟩
           → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
           → ⟨ fst e' ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  where

  arityK : (N' v : CS.S) → ⟨ fst v ∈ fst N' ⟩ → ⟨ fst N' ∈ fst (lookup K γ) ⟩
         → ⟨ fst v ∈ fst (lookup K γ) ⟩
  arityK N' v h hN = transK (fst N') (fst v) hN h

  -- The successor key of the subformula, in K.
  succK' : (E ya yc b a ar c : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
         → ⟨ sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                         (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
  succK' E ya yc b a ar c arK = sucK ar arK

  keyK' : (E ya yc b a ar c : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
        → ⟨ fst b ∈ fst (lookup K γ) ⟩
        → ⟨ pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))))
               (fst (lookup (suc (suc (suc zero)))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                      (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
  keyK' E ya yc b a ar c arK bK =
    subst (λ u → ⟨ u ∈ fst (lookup K γ) ⟩) (prʟ-fst arS b)
      (pairK arS b (sucK ar arK) bK)
    where
    arS : CS.S
    arS = sucV (fst ar) , isL-trans {x = fst (lookup K γ)} {y = sucV (fst ar)}
                            (sucK ar arK) (snd (lookup K γ))

  -- The frame read, as far as both rows share it.
  module Site (body : Formula CS.S (8 + m))
              (h : ⟨ γ ⊨ binFullAt C T K (arTagPairB N K)
                       (subValSuccB (suc (suc (suc (suc (suc (suc (suc T)))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          (suc zero)
                          (suc (suc (suc (suc (suc (suc (suc K))))))))
                       (envHypB2 B K)
                       (extAtB (suc (suc zero))
                               (suc (suc (suc (suc (suc (suc (suc K)))))))
                               body) ⟩)
              (c : CS.S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩) (ar a b yc : CS.S)
              (shD : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                        arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                                        (suc (suc zero)) (suc zero) ⟩)
              (hc : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                        appAt (suc (suc (suc (suc (suc T)))))
                              (suc (suc (suc (suc zero)))) zero ⟩)
              (yb E : CS.S)
              (hb : ⟨ (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                        subValSuccAt (suc (suc (suc (suc (suc (suc (suc T)))))))
                                     (suc (suc (suc (suc (suc zero)))))
                                     (suc (suc (suc zero)))
                                     (suc zero) ⟩)
              (hE : ⟨ (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                        envSetAt zero (suc (suc (suc (suc (suc zero)))))
                                  (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩) where
    shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
               (suc (suc (suc zero))) k (suc (suc zero)) (suc zero)
               (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
    ck = codesK c ar a b c∈ shEq
    arK = ck .fst
    aK = ck .snd .fst
    bK = ck .snd .snd .fst
    arNum = ck .snd .snd .snd
    ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
    shB = BinaryShape.in' {m} N K k (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
            tagEq numK innerK pairK aK bK shD
    yaK = subK E yb yc b a ar c hb
    EK = envK E yb yc b a ar c arNum hE
    module E' = EnvSet {7 + m} zero (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc (suc (suc (suc B)))))))
                   (suc (suc (suc (suc (suc (suc (suc K)))))))
                   (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                   (envInK E yb yc b a ar c arK arNum)
    module L = BndLeaf′ B t0 t1 K E yb yc b a ar c γ
                 t0eq t1eq t0K transK aK EK num1K hE (consK E yb yc b a ar c arNum)
    henv = E'.back hE
    hsubA = SubValSuccB2T.out {m = 7 + m}
              (suc (suc (suc (suc (suc (suc (suc T)))))))
              (suc (suc (suc (suc (suc zero)))))
              (suc (suc (suc zero)))
              (suc zero)
              (suc (suc (suc (suc (suc (suc (suc K)))))))
              (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) (succK' E yb yc b a ar c arK)
              (keyK' E yb yc b a ar c arK bK) hb
    hb' = h c c∈ ar arK a aK b bK yc ycK shB hc yb yaK E EK hsubA henv


  -- THE TWO ROWS.  At k = 10 the machine clause is `allInClauseAt`,
  -- at k = 11 `exInClauseAt`, definitionally.
  back-all : ⟨ γ ⊨ binFullAt C T K (arTagPairB N K)
                 (subValSuccB (suc (suc (suc (suc (suc (suc (suc T)))))))
                    (suc (suc (suc (suc (suc zero)))))
                    (suc (suc (suc zero)))
                    (suc zero)
                    (suc (suc (suc (suc (suc (suc (suc K))))))))
                 (envHypB2 B K)
                 (extAtB (suc (suc zero))
                         (suc (suc (suc (suc (suc (suc (suc K)))))))
                         (BndBody.bodyS B t0 t1 K)) ⟩
           → ⟨ γ ⊨ binClauseAt C T k (bndRel T B (bodyAll B)) ⟩
  back-all h c c∈ ar a b yc shD hc yb E hb hE =
    extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc K)))))))
      St.L.bodyS St.L.bodyM (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) St.L.all-fwd St.L.all-bwd
      (λ z hz → St.E'.memE-bnd St.henv z (hz .fst)) St.hb'
    where
    module St = Site (BndBody.bodyS B t0 t1 K) h c c∈ ar a b yc shD hc yb E hb hE

  back-ex : ⟨ γ ⊨ binFullAt C T K (arTagPairB N K)
                (subValSuccB (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc zero)))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K))))))))
                (envHypB2 B K)
                (extAtB (suc (suc zero))
                        (suc (suc (suc (suc (suc (suc (suc K)))))))
                        (BndBody.bodySx B t0 t1 K)) ⟩
          → ⟨ γ ⊨ binClauseAt C T k (bndRel T B (bodyEx B)) ⟩
  back-ex h c c∈ ar a b yc shD hc yb E hb hE =
    extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc K)))))))
      St.L.bodySx St.L.bodyMx (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) St.L.ex-fwd St.L.ex-bwd
      (λ z hz → St.E'.memE-bnd St.henv z (hz .fst)) St.hb'
    where
    module St = Site (BndBody.bodySx B t0 t1 K) h c c∈ ar a b yc shD hc yb E hb hE

-- The Forall row, re-tied: the extended environment is an environment
-- of the next arity, supplied by the site.
module ForallAgree′ {m : ℕ} (C T B N K : Fin m) (γ : CS.S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 9))
  (numK : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 9) a) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (transK : (x y : V ℓ) → ⟨ x ∈ fst (lookup K γ) ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ fst (lookup K γ) ⟩)
  (sucK : (x : CS.S) → ⟨ fst x ∈ fst (lookup K γ) ⟩ → ⟨ sucV (fst x) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (subK : (ya yc a ar c E : CS.S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (ya yc a ar c E : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (ya yc a ar c E : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (consK : (ya yc a ar c E : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z x e' : CS.S)
           → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst x ∈ fst (lookup B γ) ⟩
           → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc zero)) ⟩
           → ⟨ fst e' ∈ fst (lookup K γ) ⟩)
  where
  private
    φB : Formula CS.S m
    φB = Forall.forallBndAt C T B N K

    bodyFφ : Formula CS.S (7 + m)
    bodyFφ = Forall.bodyFφ C T B N K

  arityK : (N' v : CS.S) → ⟨ fst v ∈ fst N' ⟩ → ⟨ fst N' ∈ fst (lookup K γ) ⟩
         → ⟨ fst v ∈ fst (lookup K γ) ⟩
  arityK N' v h hN = transK (fst N') (fst v) hN h

  keyK' : (E ya yc a ar c : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
        → ⟨ fst a ∈ fst (lookup K γ) ⟩
        → ⟨ pr (sucV (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ))))
               (fst (lookup (suc (suc (suc zero))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
  keyK' E ya yc a ar c arK aK =
    subst (λ u → ⟨ u ∈ fst (lookup K γ) ⟩) (prʟ-fst arS a)
      (pairK arS a (sucK ar arK) aK)
    where
    arS : CS.S
    arS = sucV (fst ar) , isL-trans {x = fst (lookup K γ)} {y = sucV (fst ar)}
                            (sucK ar arK) (snd (lookup K γ))

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ forallClauseAt C T B ⟩
  back h = λ c c∈ ar a yc shD hc ya E hya hE →
    let shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 9 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , arNum)) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq (GraphEntry.un {m} T γ c ar a yc hc)
        shB = UnaryShape.in' {m} N K 9 (yc ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK aK shD
        yaK = subK ya yc a ar c E hya
        EK = envK ya yc a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        henv = E'.back hE
        hsub = SubValSuccB2T.out {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (sucK ar arK)
                 (keyK' E ya yc a ar c arK aK) hya
        hb = h c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv
    in extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         bodyFφ (body∀ B) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)
         (λ z hz → hz .fst
                 , (λ x xB e' hc' → hz .snd x xB e'
                     (consK ya yc a ar c E arNum z x e'
                       (extAt-out zero
                         (envOverAt zero (suc (suc (suc (suc (suc zero)))))
                                    (suc (suc (suc (suc (suc (suc (suc B))))))))
                         (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) hE z (hz .fst))
                       xB hc')
                     hc'))
         (λ z hz → hz .fst , (λ x xB e' e'K → hz .snd x xB e'))
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

-- The Exist row, re-tied: the extended environment lies in the
-- subformula's value, which lies in K.
module ExistAgree′ {m : ℕ} (C T B N K : Fin m) (γ : CS.S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 8))
  (numK : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 8) a) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (transK : (x y : V ℓ) → ⟨ x ∈ fst (lookup K γ) ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ fst (lookup K γ) ⟩)
  (sucK : (x : CS.S) → ⟨ fst x ∈ fst (lookup K γ) ⟩ → ⟨ sucV (fst x) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (subK : (ya yc a ar c E : CS.S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (ya yc a ar c E : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (ya yc a ar c E : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  private
    φB : Formula CS.S m
    φB = Exist.existBndAt C T B N K

    bodyE : Formula CS.S (7 + m)
    bodyE = Exist.bodyE C T B N K

  arityK : (N' v : CS.S) → ⟨ fst v ∈ fst N' ⟩ → ⟨ fst N' ∈ fst (lookup K γ) ⟩
         → ⟨ fst v ∈ fst (lookup K γ) ⟩
  arityK N' v h hN = transK (fst N') (fst v) hN h

  keyK' : (E ya yc a ar c : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
        → ⟨ fst a ∈ fst (lookup K γ) ⟩
        → ⟨ pr (sucV (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ))))
               (fst (lookup (suc (suc (suc zero))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩
  keyK' E ya yc a ar c arK aK =
    subst (λ u → ⟨ u ∈ fst (lookup K γ) ⟩) (prʟ-fst arS a)
      (pairK arS a (sucK ar arK) aK)
    where
    arS : CS.S
    arS = sucV (fst ar) , isL-trans {x = fst (lookup K γ)} {y = sucV (fst ar)}
                            (sucK ar arK) (snd (lookup K γ))

  -- The existential leaf, with the subformula's value in K.
  module Leaf (E ya yc a ar c : CS.S) (yaK : ⟨ fst ya ∈ fst (lookup K γ) ⟩) where
    xB : (z x : CS.S) → Type (ℓ-suc ℓ)
    xB z x =
      ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc B)))))))
                        (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩

    bodyK : (z x e' : CS.S) → Type (ℓ-suc ℓ)
    bodyK z x e' =
      ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                        (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩

    bodyC : (z x e' : CS.S) → Type (ℓ-suc ℓ)
    bodyC z x e' =
      ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
          consAtL zero (suc zero) (suc (suc zero))
          ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩

    exist-drop-step : (z x : CS.S) → Σ CS.S (λ e' → bodyK z x e' × bodyC z x e')
                                   → ∥ Σ CS.S (λ e' → bodyC z x e') ∥₁
    exist-drop-step z x (e' , (e'K , hc)) = ∣ e' , hc ∣₁

    exist-drop : (z x : CS.S)
               → ∥ Σ CS.S (λ e' → bodyK z x e' × bodyC z x e') ∥₁
               → ∥ Σ CS.S (λ e' → bodyC z x e') ∥₁
    exist-drop z x hx = PT.rec squash₁ (exist-drop-step z x) hx

    drop-x : (z : CS.S)
           → Σ CS.S (λ x → xB z x × ∥ Σ CS.S (λ e' → bodyK z x e' × bodyC z x e') ∥₁)
           → ∥ Σ CS.S (λ x → xB z x × ∥ Σ CS.S (λ e' → bodyC z x e') ∥₁) ∥₁
    drop-x z (x , (x∈ , hx)) = ∣ x , (x∈ , exist-drop z x hx) ∣₁

    -- The extended environment lies in the subformula's value.
    exist-lift-step : (z x : CS.S) → Σ CS.S (λ e' → bodyC z x e')
                                   → ∥ Σ CS.S (λ e' → bodyK z x e' × bodyC z x e') ∥₁
    exist-lift-step z x (e' , hc) =
      ∣ e' , (transK (fst ya) (fst e') yaK (hc .snd) , hc) ∣₁

    exist-lift : (z x : CS.S)
               → ∥ Σ CS.S (λ e' → bodyC z x e') ∥₁
               → ∥ Σ CS.S (λ e' → bodyK z x e' × bodyC z x e') ∥₁
    exist-lift z x hx = PT.rec squash₁ (exist-lift-step z x) hx

    lift-x : (z : CS.S)
           → Σ CS.S (λ x → xB z x × ∥ Σ CS.S (λ e' → bodyC z x e') ∥₁)
           → ∥ Σ CS.S (λ x → xB z x × ∥ Σ CS.S (λ e' → bodyK z x e' × bodyC z x e') ∥₁) ∥₁
    lift-x z (x , (x∈ , hx)) = ∣ x , (x∈ , exist-lift z x hx) ∣₁

    fwd : (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyE ⟩
                     → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body∃ B ⟩
    fwd z h = h .fst , PT.rec squash₁ (drop-x z) (h .snd)

    bwd : (z : CS.S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body∃ B ⟩
                     → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyE ⟩
    bwd z h = h .fst , PT.rec squash₁ (lift-x z) (h .snd)

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ existClauseAt C T B ⟩
  back h = λ c c∈ ar a yc shD hc ya E hya hE →
    let shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 8 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , arNum)) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq (GraphEntry.un {m} T γ c ar a yc hc)
        shB = UnaryShape.in' {m} N K 8 (yc ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK aK shD
        yaK = subK ya yc a ar c E hya
        EK = envK ya yc a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        henv = E'.back hE
        module L = Leaf E ya yc a ar c yaK
        hsub = SubValSuccB2T.out {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (sucK ar arK)
                 (keyK' E ya yc a ar c arK aK) hya
        hb = h c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv
    in extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         bodyE (body∃ B) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

-- The binary propositional agreement (And, Or), re-tied: the
-- environment set the bounded frame binds is supplied by the site at
-- a NUMERAL arity, merely.
module PropAgree′ {m : ℕ} (C T B N K : Fin m) (γ : CS.S ^ m) (k : ℕ)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (transK : (x a : CS.S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (subK₁ : (x y yc b a ar c : CS.S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc zero))))
                         (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (subK₀ : (y ya yc b a ar c : CS.S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc zero)))
                         zero ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (someEnv : (ya yc b a ar c : CS.S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ∥ Σ CS.S (λ E → ⟨ fst E ∈ fst (lookup K γ) ⟩
                × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {m} B K ⟩) ∥₁)
  (subA : Formula CS.S (7 + m))
  (subAEq : subA ≡ subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
             (suc (suc (suc (suc (suc zero)))))
             (suc (suc (suc (suc zero))))
             (suc zero)
             (suc (suc (suc (suc (suc (suc (suc K))))))))
  (op₁ : Formula CS.S (7 + m))
  (op₂ : Formula CS.S (8 + m))
  (body₁ : Formula CS.S (suc (7 + m)))
  (body₂ : Formula CS.S (suc (8 + m)))
  (opEq₁ : op₁ ≡ extAt (suc (suc zero)) body₁)
  (opEq₂ : op₂ ≡ extAtB (suc (suc (suc zero)))
             (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) body₂)
  (fwd : (z yb E ya yc b a ar c : CS.S)
         → ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₁ ⟩
         → ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₂ ⟩)
  (bwd : (z yb E ya yc b a ar c : CS.S)
         → ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₂ ⟩
         → ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₁ ⟩)
  (inK : (z yb E ya yc b a ar c : CS.S)
         → ⟨ fst ya ∈ fst (lookup K γ) ⟩
         → ⟨ fst yb ∈ fst (lookup K γ) ⟩
         → ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₂ ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where

  keyK₀ : (ar a : CS.S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
        → ⟨ pr (fst ar) (fst a) ∈ fst (lookup K γ) ⟩
  keyK₀ ar a arK aK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (prʟ-fst ar a) (pairK ar a arK aK)

  coreS : Formula CS.S (9 + m)
  coreS =
    prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
              (suc (suc (suc (suc (suc zero)))))
    ∧̇ appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
            zero (suc zero)

  subB2T-back : (yb E ya yc b a ar c : CS.S)
    → ⟨ fst (prʟ ar b) ∈ fst (lookup K γ) ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  zero ⟩
    → ∥ Σ CS.S (λ z → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                                  (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
                × ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ coreS ⟩) ∥₁
  subB2T-back yb E ya yc b a ar c keyK₀' h = PT.rec squash₁
    (λ { (z , (p , a₁)) →
      let p' : ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero))))) ⟩
          p' = subst ⟨_⟩
            (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc zero))))
                              (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                              (suc (suc (suc (suc (suc zero)))))
                              (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            p
          zK : ⟨ fst z ∈ fst (lookup K γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩)
                 (prʟ-fst ar b
                  ∙ sym (subst ⟨_⟩ (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc zero))))
                              (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) p))
                 keyK₀'
          a₁' : ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                         zero (suc zero) ⟩
          a₁' = subst ⟨_⟩
            (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            a₁
      in ∣ z , (zK , (p' , a₁')) ∣₁ })
    h

  opBack : (yb E ya yc b a ar c : CS.S)
    → (yaK : ⟨ fst ya ∈ fst (lookup K γ) ⟩)
    → (ybK : ⟨ fst yb ∈ fst (lookup K γ) ⟩)
    → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         extAtB (suc (suc (suc zero)))
                (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) body₂ ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         extAt (suc (suc zero)) body₁ ⟩
  opBack yb E ya yc b a ar c yaK ybK h =
      ( λ z z∈ → bwd z yb E ya yc b a ar c (h .fst z z∈) )
    , ( λ z hz → h .snd z (inK z yb E ya yc b a ar c yaK ybK
                            (fwd z yb E ya yc b a ar c hz))
                    (fwd z yb E ya yc b a ar c hz) )

  back : ⟨ γ ⊨ binFullAt C T K (arTagPairB N K)
           subA (envHypB2 B K) (propBodyB T K op₂) ⟩
       → ⟨ γ ⊨ binClauseAt C T k (propRel T op₁) ⟩
  back h = λ c c∈ ar a b yc shD hc ya yb hya hyb →
    let shEq = transport (cong fst (arityTagPairAtL-adequate
                   (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                   (suc (suc zero)) (suc zero) (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K k (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        yaK = subK₁ yb ya yc b a ar c hya
        ybK = subK₀ yb ya yc b a ar c hyb
    in PT.rec (snd ((yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ op₁))
      (λ { (E , (EK , henvE)) →
        let hsubA' = SubValB2T.out {m = 7 + m}
                       (suc (suc (suc (suc (suc (suc (suc T)))))))
                       (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc zero))))
                       (suc zero)
                       (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                       (keyK₀ ar a arK aK)
                       hya
            hsubA'' = subst (λ ψ → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) (sym subAEq) hsubA'
            hsubB' = subB2T-back yb E ya yc b a ar c (pairK ar b arK bK) hyb
            hbody = h c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA'' henvE
            hop = hbody yb ybK hsubB'
        in subst (λ ψ → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) (sym opEq₁)
             (opBack yb E ya yc b a ar c yaK ybK
               (subst (λ ψ → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) opEq₂ hop)) })
      (someEnv ya yc b a ar c yaK ycK arK arNum)

-- The And row: the instantiation at tag 2 with intersection.
module AndAgree′ {m : ℕ} (C T B N K : Fin m) (γ : CS.S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 2))
  (numK : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 2) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 2) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 2) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (transK : (x a : CS.S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (subK₁ : (x y yc b a ar c : CS.S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc zero))))
                         (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (subK₀ : (y ya yc b a ar c : CS.S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc zero)))
                         zero ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (someEnv : (ya yc b a ar c : CS.S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ∥ Σ CS.S (λ E → ⟨ fst E ∈ fst (lookup K γ) ⟩
                × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {m} B K ⟩) ∥₁)
  where
  module P = PropAgree′ {m} C T B N K γ 2
    tagEq numK innerK pairK codesK valK transK subK₁ subK₀ someEnv
    (And.subA {m} C T B N K)
    refl
    (interAt (suc (suc zero)) (suc zero) zero)
    (And.opA {m} C T B N K)
    ((var zero ∈̇ var (suc (suc zero))) ∧̇ (var zero ∈̇ var (suc zero)))
    ((var zero ∈̇ var (suc (suc (suc zero)))) ∧̇ (var zero ∈̇ var (suc zero)))
    refl refl
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c yaK ybK hz →
       transK z (lookup (suc (suc (suc zero))) (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))
         (hz .fst) yaK)
  open P public

-- The Or row: the instantiation at tag 3 with union.
module OrAgree′ {m : ℕ} (C T B N K : Fin m) (γ : CS.S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 3))
  (numK : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 3) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : CS.S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 3) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : CS.S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 3) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (transK : (x a : CS.S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (subK₁ : (x y yc b a ar c : CS.S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc zero))))
                         (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (subK₀ : (y ya yc b a ar c : CS.S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc zero)))
                         zero ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (someEnv : (ya yc b a ar c : CS.S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ∥ Σ CS.S (λ E → ⟨ fst E ∈ fst (lookup K γ) ⟩
                × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {m} B K ⟩) ∥₁)
  where
  module P = PropAgree′ {m} C T B N K γ 3
    tagEq numK innerK pairK codesK valK transK subK₁ subK₀ someEnv
    (Or.subO {m} C T B N K)
    refl
    (unionAt (suc (suc zero)) (suc zero) zero)
    (Or.opO {m} C T B N K)
    ((var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ∈̇ var (suc zero)))
    ((var zero ∈̇ var (suc (suc (suc zero)))) ∨̇ (var zero ∈̇ var (suc zero)))
    refl refl
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c yaK ybK hz →
       PT.rec (snd (fst z ∈ fst (lookup K γ)))
         (λ { (inl p) →
                transK z (lookup (suc (suc (suc zero)))
                  (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) p yaK
            ; (inr p) →
                transK z (lookup (suc zero)
                  (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) p ybK })
         hz)
  open P public
```
