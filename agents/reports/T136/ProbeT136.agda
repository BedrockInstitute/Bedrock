{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeT136 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import FOL.Manipulation.Bounding using ( BoundedTm; BoundedFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Absoluteness {ℓ} using ( InL; liftFo; transferFo )
open import L.Coding.Base {ℓ}
  using ( tagAt; Δ₀-tagAt; tagAt-adequate; sglConAt; pairConAt
        ; ∈pair-elim; ∈pair-introL; ∈pair-introR; sgl-char )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )

open import Cubical.Data.FinData using ( Fin; zero; suc; toℕ )
open import Cubical.Data.Vec using ( lookup; map )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( #_ )
open import V.Coding {ℓ} using ( pr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Foundations.HLevels using ( isProp× )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The environment and extension readers from the master.
env : ∀ {n} → (Fin n → V ℓ) → V ℓ
env {n} g = sett (Lift {ℓ-zero} {ℓ} (Fin n))
                 (λ li → pr (# (toℕ (lower li))) (g (lower li)))

envOne : V ℓ → V ℓ
envOne y = env {1} (λ _ → y)

private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

extAt : ∀ {n} → Fin n → Formula S (suc n) → Formula S n
extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
         ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))

module _ {n : ℕ} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n) where
  extAt-out : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
            → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  extAt-out h = h .fst

  extAt-in : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
           → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩
  extAt-in h = h .snd

  extAt-in-both : ((z : S) → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
                → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩)
                → ⟨ γ ⊨ extAt y φ ⟩
  extAt-in-both f g = f , g

-- Support: the L-side Kuratowski pair and the key it builds.
private
  pair-singleton : (a : V ℓ) → ⁅ a , a ⁆ ≡ ⁅ a ⁆s
  pair-singleton a = sgl-char ⁅ a , a ⁆ a (∈pair-introL {u = a} {v = a} refl) hall
    where
    hall : (y : V ℓ) → ⟨ y ∈ ⁅ a , a ⁆ ⟩ → y ≡ a
    hall y y∈ = PT.rec (setIsSet y a) collapse
      (∈pair-elim {u = a} {v = a} {y = y} y∈)
      where
      collapse : (y ≡ a) ⊎ (y ≡ a) → y ≡ a
      collapse (inl e) = e
      collapse (inr e) = e

prʟ : S → S → S
prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)

prʟ-fst : (a b : S) → fst (prʟ a b) ≡ pr (fst a) (fst b)
prʟ-fst a b = pairʟ-fst (pairʟ a a) (pairʟ a b)
  ∙ cong₂ ⁅_,_⁆ (pairʟ-fst a a ∙ pair-singleton (fst a)) (pairʟ-fst a b)

keyOf : ℕ → S → S
keyOf n x = prʟ (numeralL n) x

keyOf-fst : (n : ℕ) (x : S) → fst (keyOf n x) ≡ pr (# n) (fst x)
keyOf-fst n x = prʟ-fst (numeralL n) x ∙ cong₂ pr (numeralL-fst n) refl

-- The tag atom, written fresh: the hierarchy's tag reader lifted into the
-- model's language.  The lift needs a certificate that its only constant, the
-- numeral # k, is constructible.
private
  lookup-fst : ∀ {n} (i : Fin n) (γ : S ^ n)
             → lookup i (map fst γ) ≡ fst (lookup i γ)
  lookup-fst zero    (m ∷ γ) = refl
  lookup-fst (suc i) (m ∷ γ) = lookup-fst i γ

  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

  numeral-inL : (k : ℕ) → InL (# k)
  numeral-inL k = subst (λ w → ⟨ isL w ⟩) (numeralL-fst k) (numeralL k .snd)

  certVar : ∀ {n} (i : Fin n) → BoundedTm InL (var i)
  certVar i = tt*

  certSgl : ∀ {n} (k : ℕ) → BoundedFo InL (sglConAt {n = suc n} zero (# k))
  certSgl {n} k = (numeral-inL k , certVar {suc n} zero)
                , (certVar {suc n} zero , (certVar {suc n} zero , numeral-inL k))

  certPair : ∀ {n} (k : ℕ) (x : Fin n)
           → BoundedFo InL (pairConAt {n = suc n} zero (# k) (suc x))
  certPair {n} k x = (numeral-inL k , certVar {suc n} zero)
                   , ( (certVar {suc n} (suc x) , certVar {suc n} zero)
                     , (certVar {suc n} zero
                       , ((certVar {suc n} zero , numeral-inL k)
                        , (certVar {suc n} zero
                          , certVar {suc (suc n)} (suc (suc x))))) )

  tagBounded : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n)
             → BoundedFo InL (tagAt s k x)
  tagBounded {n} s k x = (certVar {n} s , certSgl {n} k)
                       , ( (certVar {n} s , certPair {n} k x)
                         , (certVar {n} s , (certSgl {n} k , certPair {n} k x)) )

tagAtL : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
tagAtL s k x = liftFo (tagAt s k x) (tagBounded s k x)

tagAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n) (γ : S ^ n)
  → (γ ⊨ tagAtL s k x)
  ≡ PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))
tagAtL-adequate s k x γ =
    transferFo (tagAt s k x) (tagBounded s k x) (Δ₀-tagAt s k x) γ
  ∙ tagAt-adequate s k x (map fst γ)
  ∙ cong₂ PairIs (lookup-fst s γ)
      (cong₂ pr (refl {x = # k}) (lookup-fst x γ))

-- The key atom, one existential above the tag atom.
keyArityAtL : ∀ {n} → Fin n → ℕ → Formula S n
keyArityAtL c k = ∃̇ (tagAtL (suc c) k zero)

keyArityAtL-out : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n)
                → ⟨ γ ⊨ keyArityAtL c k ⟩
                → ∥ (Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# k) (fst z))) ∥₁
keyArityAtL-out c k γ = PT.map step
  where
  step : Σ[ z ∈ S ] ⟨ (z ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
       → Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# k) (fst z))
  step (z , hz) = z , subst ⟨_⟩ (tagAtL-adequate (suc c) k zero (z ∷ γ)) hz

keyArityAtL-in : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n) (z : S)
               → fst (lookup c γ) ≡ pr (# k) (fst z)
               → ⟨ γ ⊨ keyArityAtL c k ⟩
keyArityAtL-in c k γ z e =
  ∣ z , subst ⟨_⟩ (sym (tagAtL-adequate (suc c) k zero (z ∷ γ))) e ∣₁

-- The one-entry environment conjunct and its two directions.
envOneAt : ∀ {n} → Fin n → Fin n → Formula S n
envOneAt e y = extAt e (tagAtL zero 0 (suc y))

module _ {n : ℕ} (e y : Fin n) (γ : S ^ n) where
  private
    E : S
    E = lookup e γ

    v : V ℓ
    v = fst (lookup y γ)

    readEntry : (z : S) → ⟨ fst z ∈ envOne v ⟩ → fst z ≡ pr (# 0) v
    readEntry z = PT.rec (setIsSet (fst z) (pr (# 0) v)) step
      where
      step : Σ[ li ∈ Lift {ℓ-zero} {ℓ} (Fin 1) ]
               (pr (# (toℕ (lower li))) v ≡ fst z)
           → fst z ≡ pr (# 0) v
      step (lift zero , q) = sym q
      step (lift (suc ()) , _)

    entry∈ : (z : S) → fst z ≡ pr (# 0) v → ⟨ fst z ∈ envOne v ⟩
    entry∈ z q = ∣ lift zero , sym q ∣₁

  envOneAt-in : fst E ≡ envOne v → ⟨ γ ⊨ envOneAt e y ⟩
  envOneAt-in q = extAt-in-both e (tagAtL zero 0 (suc y)) γ fwd bwd
    where
    fwd : (z : S) → ⟨ fst z ∈ fst E ⟩ → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc y) ⟩
    fwd z z∈ = subst ⟨_⟩ (sym (tagAtL-adequate zero 0 (suc y) (z ∷ γ)))
      (readEntry z (subst (λ w → ⟨ fst z ∈ w ⟩) q z∈))

    bwd : (z : S) → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc y) ⟩ → ⟨ fst z ∈ fst E ⟩
    bwd z h = subst (λ w → ⟨ fst z ∈ w ⟩) (sym q)
      (entry∈ z (subst ⟨_⟩ (tagAtL-adequate zero 0 (suc y) (z ∷ γ)) h))

  envOneAt-out : ⟨ γ ⊨ envOneAt e y ⟩ → fst E ≡ envOne v
  envOneAt-out h = extensionality (fst E) (envOne v) (sub₁ , sub₂)
    where
    sub₁ : ⟨ fst E ⊆ envOne v ⟩
    sub₁ w w∈ₛ = ∈∈ₛ {a = w} {b = envOne v} .fst
      (entry∈ wS (subst ⟨_⟩
        (tagAtL-adequate zero 0 (suc y) (wS ∷ γ))
        (extAt-out e (tagAtL zero 0 (suc y)) γ h wS w∈)))
      where
      w∈ : ⟨ w ∈ fst E ⟩
      w∈ = ∈∈ₛ {a = w} {b = fst E} .snd w∈ₛ

      wS : S
      wS = w , isL-trans {x = fst E} {y = w} w∈ (snd E)

    sub₂ : ⟨ envOne v ⊆ fst E ⟩
    sub₂ w w∈ₛ = ∈∈ₛ {a = w} {b = fst E} .fst
      (PT.rec (snd (w ∈ fst E)) step₂
        (∈∈ₛ {a = w} {b = envOne v} .snd w∈ₛ))
      where
      hasKey : ⟨ fst (keyOf 0 (lookup y γ)) ∈ fst E ⟩
      hasKey = extAt-in e (tagAtL zero 0 (suc y)) γ h (keyOf 0 (lookup y γ))
        (subst ⟨_⟩
          (sym (tagAtL-adequate zero 0 (suc y) (keyOf 0 (lookup y γ) ∷ γ)))
          (keyOf-fst 0 (lookup y γ)))

      step₂ : Σ[ li ∈ Lift {ℓ-zero} {ℓ} (Fin 1) ]
                (pr (# (toℕ (lower li))) v ≡ w)
            → ⟨ w ∈ fst E ⟩
      step₂ (lift zero , q) =
        subst (λ u → ⟨ u ∈ fst E ⟩) (keyOf-fst 0 (lookup y γ) ∙ q) hasKey
      step₂ (lift (suc ()) , _)

-- The third conjunct, from the frame, and its three directions.
DefinesAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
DefinesAt x w v = extAt x ( (var zero ∈̇ var (suc w))
                          ∧̇ ∃̇ ( envOneAt zero (suc zero)
                               ∧̇ (var zero ∈̇ var (suc (suc v))) ) )

HoldsDef : ∀ {n} (w v : Fin n) (γ : S ^ n) (z : S) → Type (ℓ-suc ℓ)
HoldsDef w v γ z = ⟨ fst z ∈ fst (lookup w γ) ⟩
                   × ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩

module _ {n : ℕ} (x w v : Fin n) (γ : S ^ n) where
  private
    inner : Formula S (suc n)
    inner = ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))

    body : Formula S (suc n)
    body = (var zero ∈̇ var (suc w)) ∧̇ inner

    readInner : (z : S) → ⟨ (z ∷ γ) ⊨ inner ⟩
              → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
    readInner z = PT.rec (snd (envOne (fst z) ∈ fst (lookup v γ))) step
      where
      step : Σ[ E ∈ S ] ⟨ (E ∷ z ∷ γ)
               ⊨ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
           → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
      step (E , (hE , E∈)) = subst (λ u → ⟨ u ∈ fst (lookup v γ) ⟩)
        (envOneAt-out zero (suc zero) (E ∷ z ∷ γ) hE) E∈

    fillInner : (z : S) → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
              → ⟨ (z ∷ γ) ⊨ inner ⟩
    fillInner z h =
      ∣ E , (envOneAt-in zero (suc zero) (E ∷ z ∷ γ) refl , h) ∣₁
      where
      E : S
      E = envOne (fst z)
        , isL-trans {x = fst (lookup v γ)} {y = envOne (fst z)} h
            (snd (lookup v γ))

  DefinesAt-out : ⟨ γ ⊨ DefinesAt x w v ⟩
                → (z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → HoldsDef w v γ z
  DefinesAt-out h z z∈ = hz .fst , readInner z (hz .snd)
    where
    hz : ⟨ (z ∷ γ) ⊨ body ⟩
    hz = extAt-out x body γ h z z∈

  DefinesAt-in : ⟨ γ ⊨ DefinesAt x w v ⟩
               → (z : S) → HoldsDef w v γ z → ⟨ fst z ∈ fst (lookup x γ) ⟩
  DefinesAt-in h z (hw , hv) =
    extAt-in x body γ h z (hw , fillInner z hv)

  DefinesAt-both : ((z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → HoldsDef w v γ z)
                 → ((z : S) → HoldsDef w v γ z → ⟨ fst z ∈ fst (lookup x γ) ⟩)
                 → ⟨ γ ⊨ DefinesAt x w v ⟩
  DefinesAt-both f g = extAt-in-both x body γ
    (λ z z∈ → f z z∈ .fst , fillInner z (f z z∈ .snd))
    (λ z h → g z (h .fst , readInner z (h .snd)))
