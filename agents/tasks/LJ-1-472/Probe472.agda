{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.472] PROBE.  Numerals as members of the condensation hull.
-- It runs in agents/tasks/LJ-1-472/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  zero-in-hull.  Route 1: wit at ∀̇∈ (var zero) ⊥̇.
--
--   STEP TWO            numerals-in-hull.  Route 1: wit at numeralFo.
--                       Formulas generic in K (W2).  Not in live src/.
--                       Archived at
--                       archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:367-373.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-472.Probe472 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ⊥̇; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( leastOf )
open import L.Coding.Bound {ℓ} lem using ( module Bound )

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
open import Cubical.Data.Sigma using ( Σ-syntax; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; extensionality; _∈ₛ_; _⊆_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- W2: formulas once, generic in the constant domain.  Instantiated at
-- ⊥* for wit.  Not a named term in live src/.

succFo : ∀ {ℓk} {K : Type ℓk} {n} (x y : Fin n) → Formula K n
succFo x y =
    (∀̇∈ (var y) ((var zero ∈̇ var (suc x)) ∨̇ (var zero ≐ var (suc x))))
  ∧̇ (∀̇∈ (var x) (var zero ∈̇ var (suc y)))
  ∧̇ (var x ∈̇ var y)

numeralFo : (n : ℕ) → ∀ {ℓk} {K : Type ℓk} {n'} (v : Fin (suc n'))
          → Formula K (suc n')
numeralFo zero v = ∀̇∈ (var v) ⊥̇
numeralFo (suc n) {ℓk} {K} {n'} v =
  ∃̇∈ (var v) (succFo zero (suc v) ∧̇ numeralFo n {K = K} {n' = suc n'} zero)

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- Nothing below module Condense is copied.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  open H.T using ( Code; val; wit; Sat; val-wit; inHull; _⊨₀_ )

  module Bd = Bound lam ordλ succλ ∅∈λ

  isSetSL : isSet ASt.SL
  isSetSL = isSetΣSndProp setIsSet (λ x → (x ∈ˢ Lset lam) .snd)

  nL : (k : ℕ) → ASt.SL
  nL k = # k , subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (numeralL-fst k) (Bd.num∈λ k)

  -- =====================================================================
  -- W3.  k = 0 alone.
  -- =====================================================================

  φ0 : Formula (⊥* {ℓ}) 1
  φ0 = ∀̇∈ (var zero) ⊥̇

  emptySL : ASt.SL
  emptySL = ∅ , H.∅∈Lsetα

  sat-empty : ⟨ (emptySL ∷ []) ⊨₀ φ0 ⟩
  sat-empty x hx =
    Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst hx))

  w0 : Sat 0 φ0 []
  w0 = ∣ emptySL , sat-empty ∣₁

  c0 : Code
  c0 = wit 0 φ0 []

  empty-unique : (a : ASt.SL) → ⟨ (a ∷ []) ⊨₀ φ0 ⟩ → fst a ≡ ∅
  empty-unique a ha = extensionality (fst a) ∅ (s1 , s2)
    where
    s1 : (z : S) → ⟨ z ∈ₛ fst a ⟩ → ⟨ z ∈ₛ ∅ ⟩
    s1 z hz = Empty.rec* {ℓ' = ℓ-suc ℓ}
      (ha (z , ASt.Ltr {x = fst a} {y = z}
                 (∈∈ₛ {a = z} {b = fst a} .snd hz)
                 (a .snd))
          (∈∈ₛ {a = z} {b = fst a} .snd hz))
    s2 : (z : S) → ⟨ z ∈ₛ ∅ ⟩ → ⟨ z ∈ₛ fst a ⟩
    s2 z hz = Empty.rec (∅-empty z hz)

  found0 : Σ[ a ∈ ASt.SL ] _
  found0 = leastOf ASt.wL {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ []) ⊨₀ φ0) w0

  zero-in-hull : ⟨ fst (numeralL 0) ∈ˢ H.T.Hull ⟩
  zero-in-hull =
    subst (λ z → ⟨ z ∈ˢ H.T.Hull ⟩)
      (cong fst (val-wit 0 φ0 [] w0)
        ∙ empty-unique (found0 .fst) (found0 .snd .fst)
        ∙ sym (numeralL-fst 0))
      (inHull c0)

  -- =====================================================================
  -- Obligation.  Route 1, by closure.  numeralFo at a general X.
  -- =====================================================================

  succ-sat : {n : ℕ} (u v : ASt.SL) (δ : Vec ASt.SL n)
           → fst v ≡ sucV (fst u)
           → ⟨ (u ∷ v ∷ δ) ⊨₀ (succFo zero (suc zero)) ⟩
  succ-sat {n} u v δ e = a , (b , c)
    where
    a : (z : ASt.SL) → ⟨ fst z ∈ˢ fst v ⟩
      → ∥ ⟨ fst z ∈ˢ fst u ⟩ ⊎ (fst z ≡ fst u) ∥₁
    a z hz = ∈sucV-elim squash₁ (subst (λ w → ⟨ fst z ∈ˢ w ⟩) e hz)
      (λ hzu → ∣ inl hzu ∣₁) (λ hz≡u → ∣ inr hz≡u ∣₁)
    b : (z : ASt.SL) → ⟨ fst z ∈ˢ fst u ⟩ → ⟨ fst z ∈ˢ fst v ⟩
    b z hzu = subst (λ w → ⟨ fst z ∈ˢ w ⟩) (sym e) (∈sucV-inl hzu)
    c : ⟨ fst u ∈ˢ fst v ⟩
    c = subst (λ w → ⟨ fst u ∈ˢ w ⟩) (sym e) (self∈sucV (fst u))

  succ-sat-bwd : {n : ℕ} (u v : ASt.SL) (δ : Vec ASt.SL n)
               → ⟨ (u ∷ v ∷ δ) ⊨₀ (succFo zero (suc zero)) ⟩
               → fst v ≡ sucV (fst u)
  succ-sat-bwd u v δ (a , (b , c)) = extensionality (fst v) (sucV (fst u)) (s1 , s2)
    where
    s1 : ⟨ fst v ⊆ sucV (fst u) ⟩
    s1 z hz = PT.rec (snd (z ∈ₛ sucV (fst u))) (s1' z)
      (a (z , ASt.Ltr {x = fst v} {y = z}
               (∈∈ₛ {a = z} {b = fst v} .snd hz)
               (v .snd))
         (∈∈ₛ {a = z} {b = fst v} .snd hz))
      where
      s1' : (z : S) → ⟨ z ∈ˢ fst u ⟩ ⊎ (z ≡ fst u) → ⟨ z ∈ₛ sucV (fst u) ⟩
      s1' z (inl hzu) = ∈∈ₛ {a = z} {b = sucV (fst u)} .fst (∈sucV-inl hzu)
      s1' z (inr hz≡u) = ∈∈ₛ {a = z} {b = sucV (fst u)} .fst
        (subst (λ w → ⟨ w ∈ˢ sucV (fst u) ⟩) (sym hz≡u) (self∈sucV (fst u)))
    s2 : ⟨ sucV (fst u) ⊆ fst v ⟩
    s2 z hz = ∈∈ₛ {a = z} {b = fst v} .fst (∈sucV-elim (snd (z ∈ˢ fst v))
        (∈∈ₛ {a = z} {b = sucV (fst u)} .snd hz)
        (λ hzu → b (z , ASt.Ltr {x = fst u} {y = z} hzu (u .snd)) hzu)
        (λ hz≡u → subst (λ w → ⟨ w ∈ˢ fst v ⟩) (sym hz≡u) c))

  numeral-sat : (k : ℕ) {n : ℕ} (δ : Vec ASt.SL n)
              → ⟨ (nL k ∷ δ) ⊨₀ (numeralFo k {n' = n} zero) ⟩
  numeral-sat zero {n} δ = λ x x∈ →
    Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst x∈))
  numeral-sat (suc k) {n} δ =
    ∣ nL k , (self∈sucV (# k) , (succ-sat (nL k) (nL (suc k)) δ refl
                                , numeral-sat k (nL (suc k) ∷ δ))) ∣₁

  numeral-unique : (k : ℕ) {n : ℕ} (a : ASt.SL) (δ : Vec ASt.SL n)
                 → ⟨ (a ∷ δ) ⊨₀ (numeralFo k {n' = n} zero) ⟩
                 → a ≡ nL k
  numeral-unique zero a δ ha = Σ≡Prop (λ z → (z ∈ˢ Lset lam) .snd)
    (extensionality (fst a) ∅ (s1 , s2))
    where
    s1 : ⟨ fst a ⊆ ∅ ⟩
    s1 z hz = Empty.rec* {ℓ' = ℓ-suc ℓ}
      (ha (z , ASt.Ltr {x = fst a} {y = z}
                 (∈∈ₛ {a = z} {b = fst a} .snd hz)
                 (a .snd))
          (∈∈ₛ {a = z} {b = fst a} .snd hz))
    s2 : ⟨ ∅ ⊆ fst a ⟩
    s2 z hz = Empty.rec (∅-empty z hz)
  numeral-unique (suc k) a δ ha =
    PT.rec (isSetSL a (nL (suc k)))
      (λ { (y , gy , (sat , hy)) →
        Σ≡Prop (λ z → (z ∈ˢ Lset lam) .snd)
          (succ-sat-bwd y a δ sat
            ∙ cong sucV (cong fst (numeral-unique k y (a ∷ δ) hy))) })
      ha

  φk : (k : ℕ) → Formula (⊥* {ℓ}) 1
  φk k = numeralFo k {n' = 0} zero

  sat-k : (k : ℕ) → Sat 0 (φk k) []
  sat-k k = ∣ nL k , numeral-sat k [] ∣₁

  ck : (k : ℕ) → Code
  ck k = wit 0 (φk k) []

  found : (k : ℕ) → Σ[ a ∈ ASt.SL ] _
  found k = leastOf ASt.wL {ℓ'' = ℓ-suc ℓ} lem
              (λ a → (a ∷ []) ⊨₀ φk k) (sat-k k)

  numerals-in-hull : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ H.T.Hull ⟩
  numerals-in-hull k =
    subst (λ z → ⟨ z ∈ˢ H.T.Hull ⟩)
      (cong fst (val-wit 0 (φk k) [] (sat-k k))
        ∙ cong fst (numeral-unique k (found k .fst) [] (found k .snd .fst))
        ∙ sym (numeralL-fst k))
      (inHull (ck k))

-- The witness meter reads `Target.numerals-in-hull` at this module
-- (`scripts/pod/witness.py:278`). A named parameterised module does not
-- lift the name. The term above is the one the brief wrote.

numerals-in-hull = HullStage.numerals-in-hull
