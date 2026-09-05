{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.210] the VERBATIM fence extract of `src/L/Coding/Powerset.lagda.md`.
-- IT IS NOT PORTED.  Only the `module` line below is changed, so that the
-- file does not claim the delivered module's name on the include path.
-- The report reads this file for line numbers and it never typechecks it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-210.GenPowerset {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( 𝒟ₒ→isL; LsetS )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-out; extAt-in; extAt-in-both; tagAtL; tagAtL-adequate
        ; domAt; domAt-intro; domAt-out )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.Recover {ℓ} using ( keyOf; keyOf-fst )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyArityAtL; keyArityAtL-in; keyArityAtL-out; hasWitnessAt
        ; codeS; keyS; witnessAt-in; witnessAt-out )
open import L.Coding.Graph {ℓ} lem
  using ( satGraphAt; GraphWitAt; graphAt-in; graphAt-out )
open import L.Coding.Table {ℓ} lem
  using ( keyʟ; slot; satTable; total; inSlot; entry-in )
open import L.Coding.Slot {ℓ} lem using ( slotClosed )
open import L.Coding.Sound {ℓ} lem using ( soundness )
open import L.Coding.Unique {ℓ} lem using ( module Good )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Bridge {ℓ} lem using ( asConst; defSet-Sat )
open import L.Coding.Uniform {ℓ} lem using ( keyBridge )

open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
envOne : V ℓ → V ℓ
envOne y = env {1} (λ _ → y)

envOneAt : ∀ {n} → Fin n → Fin n → Formula S n
envOneAt e y = extAt e (tagAtL zero 0 (suc y))

module _ {n : ℕ} (e y : Fin n) (γ : S ^ n) where
  private
    E : S
    E = lookup e γ

    v : V ℓ
    v = fst (lookup y γ)

    readEntry : (z : S) → ⟨ fst z ∈ envOne v ⟩ → fst z ≡ pr (# 0) v
    readEntry z = PT.rec (setIsSet (fst z) (pr (# 0) v))
      (λ { (lift zero , q) → sym q ; (lift (suc ()) , _) })

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
      (PT.rec (snd (w ∈ fst E))
        (λ { (lift zero , q) →
               subst (λ u → ⟨ u ∈ fst E ⟩) (keyOf-fst 0 (lookup y γ) ∙ q) hasKey
           ; (lift (suc ()) , _) })
        (∈∈ₛ {a = w} {b = envOne v} .snd w∈ₛ))
      where
      hasKey : ⟨ fst (keyOf 0 (lookup y γ)) ∈ fst E ⟩
      hasKey = extAt-in e (tagAtL zero 0 (suc y)) γ h (keyOf 0 (lookup y γ))
        (subst ⟨_⟩
          (sym (tagAtL-adequate zero 0 (suc y) (keyOf 0 (lookup y γ) ∷ γ)))
          (keyOf-fst 0 (lookup y γ)))
DefinesAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
DefinesAt x w v = extAt x ( (var zero ∈̇ var (suc w))
                          ∧̇ ∃̇ ( envOneAt zero (suc zero)
                               ∧̇ (var zero ∈̇ var (suc (suc v))) ) )

module _ {n : ℕ} (x w v : Fin n) (γ : S ^ n) where
  private
    inner : Formula S (suc n)
    inner = ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))

    body : Formula S (suc n)
    body = (var zero ∈̇ var (suc w)) ∧̇ inner

    Holds : S → Type (ℓ-suc ℓ)
    Holds z = ⟨ fst z ∈ fst (lookup w γ) ⟩
              × ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩

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
                → (z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → Holds z
  DefinesAt-out h z z∈ = hz .fst , readInner z (hz .snd)
    where
    hz : ⟨ (z ∷ γ) ⊨ body ⟩
    hz = extAt-out x body γ h z z∈

  DefinesAt-in : ⟨ γ ⊨ DefinesAt x w v ⟩
               → (z : S) → Holds z → ⟨ fst z ∈ fst (lookup x γ) ⟩
  DefinesAt-in h z (hw , hv) =
    extAt-in x body γ h z (hw , fillInner z hv)

  DefinesAt-both : ((z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → Holds z)
                 → ((z : S) → Holds z → ⟨ fst z ∈ fst (lookup x γ) ⟩)
                 → ⟨ γ ⊨ DefinesAt x w v ⟩
  DefinesAt-both f g = extAt-in-both x body γ
    (λ z z∈ → f z z∈ .fst , fillInner z (f z z∈ .snd))
    (λ z h → g z (h .fst , readInner z (h .snd)))
isCodeAt : ∀ {n} → Fin n → Fin n → Formula S n
isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c

module _ (A : S) where
  codeAt-in : ∀ {n} (c w : Fin n) (γ : S ^ n)
            → fst (lookup w γ) ≡ fst A
            → (ψ : Formula ⟪ fst A ⟫ 1) → fst (lookup c γ) ≡ fst (keyS A ψ)
            → ⟨ γ ⊨ isCodeAt c w ⟩
  codeAt-in c w γ qw ψ qc =
    keyArityAtL-in c 1 γ (codeS A ψ) qc , witnessAt-in A w c γ ψ qw qc

  codeAt-out : ∀ {n} (c w : Fin n) (γ : S ^ n)
             → fst (lookup w γ) ≡ fst A
             → ⟨ γ ⊨ isCodeAt c w ⟩
             → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
                   (fst (lookup c γ) ≡ fst (keyS A ψ))) ∥₁
  codeAt-out c w γ qw (hk , hw) =
    PT.rec squash₁ step (keyArityAtL-out c 1 γ hk)
    where
    step : Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# 1) (fst z))
         → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
               (fst (lookup c γ) ≡ fst (keyS A ψ))) ∥₁
    step (z , qz) = witnessAt-out A w c γ qw hw 1 z qz
module _ (B : S) where
  private
    Ci Ti : ∀ {k} → Fin (suc (suc (suc k)))
    Ci = suc (suc zero)
    Ti = suc zero

  graphAt-holds : ∀ {m n} (φ : Formula S m) (w c v : Fin n) (γ : S ^ n)
                → fst (lookup w γ) ≡ fst B
                → fst (lookup c γ) ≡ fst (keyʟ φ)
                → fst (lookup v γ) ≡ fst (Sat B φ)
                → ⟨ γ ⊨ satGraphAt w c v ⟩
  graphAt-holds φ w c v γ qw qc qv = graphAt-in w c v γ
    ∣ slot B φ , (satTable B φ , (B , (sym qw
    , ( slotClosed B φ γ
    , ( hdom
    , ( entry
    , soundness B φ γ )))))) ∣₁
    where
    δ : S ^ (suc (suc (suc _)))
    δ = B ∷ satTable B φ ∷ slot B φ ∷ γ

    hdom : ⟨ δ ⊨ domAt Ti Ci ⟩
    hdom = domAt-intro Ti Ci δ
      (λ z → (λ h → PT.rec (snd (fst z ∈ fst (slot B φ)))
                  (λ { (u , hu) → inSlot B φ (fst z) (fst u) hu }) h)
           , (λ h → total B φ (fst z) h))

    entry : ⟨ pr (fst (lookup c γ)) (fst (lookup v γ)) ∈ fst (satTable B φ) ⟩
    entry = subst2 (λ a b → ⟨ pr a b ∈ fst (satTable B φ) ⟩)
      (sym qc) (sym qv) (entry-in B φ)

  graphAt-unique : ∀ {m n} (φ : Formula S m) (w c v : Fin n) (γ : S ^ n)
                 → fst (lookup w γ) ≡ fst B
                 → fst (lookup c γ) ≡ fst (keyʟ φ)
                 → ⟨ γ ⊨ satGraphAt w c v ⟩
                 → fst (lookup v γ) ≡ fst (Sat B φ)
  graphAt-unique φ w c v γ qw qc h =
    PT.rec (setIsSet (fst (lookup v γ)) (fst (Sat B φ))) step
      (graphAt-out w c v γ h)
    where
    step : GraphWitAt w c v γ → fst (lookup v γ) ≡ fst (Sat B φ)
    step (C , (T , (b , (eb , (hc , (hd , (ha , h12)))))))
      = Good.pinned (b ∷ T ∷ C ∷ γ) Ci Ti zero hc hd h12 φ
          (lookup c γ) (lookup v γ) qc
          (domAt-out Ti Ci (b ∷ T ∷ C ∷ γ) hd (lookup c γ) (lookup v γ) ha) ha
      ∙ cong (λ u → fst (Sat u φ)) (Σ≡Prop (λ u → snd (isL u)) (eb ∙ qw))
private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

DefBody : ∀ {n} → Fin n → Formula S (suc (suc (suc n)))
DefBody w = isCodeAt (suc zero) (sh3 w)
            ∧̇ ( satGraphAt (sh3 w) (suc zero) zero
              ∧̇ DefinesAt (suc (suc zero)) (sh3 w) zero )

DefAt : ∀ {n} → Fin n → Fin n → Formula S n
DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))

DefOK : S → Type (ℓ-suc ℓ)
DefOK A = (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (fst A) ⟩ → ⟨ isL x ⟩
module _ (A : S) where
  private
    module DA = DefOf (fst A)

    toS : Formula ⟪ fst A ⟫ 1 → Formula S 1
    toS ψ = mapFo (asConst A) ψ

    ιA : ⟪ fst A ⟫ → V ℓ
    ιA = ⟪ fst A ⟫↪

    ιA∈ : (m : ⟪ fst A ⟫) → ⟨ ιA m ∈ fst A ⟩
    ιA∈ m = ∈∈ₛ {a = ιA m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

    Fibre : Formula ⟪ fst A ⟫ 1 → V ℓ → Type (ℓ-suc ℓ)
    Fibre ψ y = Σ[ p ∈ Σ[ m ∈ ⟪ fst A ⟫ ] ⟨ DA.smallSat ψ m ⟩ ]
                  (ιA (p .fst) ≡ y)

    inSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
          → ⟨ ιA m ∈ DA.defSet ψ ⟩
          → ⟨ envOne (ιA m) ∈ fst (Sat A (toS ψ)) ⟩
    inSat ψ m h = subst ⟨_⟩ (defSet-Sat A ψ m) h

    outSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
           → ⟨ envOne (ιA m) ∈ fst (Sat A (toS ψ)) ⟩
           → ⟨ ιA m ∈ DA.defSet ψ ⟩
    outSat ψ m h = subst ⟨_⟩ (sym (defSet-Sat A ψ m)) h

  fill : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
       → (z : S) (ψ : Formula ⟪ fst A ⟫ 1) → DA.defSet ψ ≡ fst z
       → ⟨ (Sat A (toS ψ) ∷ keyS A ψ ∷ z ∷ γ) ⊨ DefBody w ⟩
  fill {n} w γ qw z ψ qz = hcode , (hgraph , hdef)
    where
    δ : S ^ (suc (suc (suc n)))
    δ = Sat A (toS ψ) ∷ keyS A ψ ∷ z ∷ γ

    hcode : ⟨ δ ⊨ isCodeAt (suc zero) (sh3 w) ⟩
    hcode = codeAt-in A (suc zero) (sh3 w) δ qw ψ refl

    hgraph : ⟨ δ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
    hgraph = graphAt-holds A (toS ψ) (sh3 w) (suc zero) zero δ qw
               (keyBridge A ψ) refl

    Holds : S → Type (ℓ-suc ℓ)
    Holds y = ⟨ fst y ∈ fst (lookup w γ) ⟩
              × ⟨ envOne (fst y) ∈ fst (Sat A (toS ψ)) ⟩

    into : (y : S) → ⟨ fst y ∈ fst z ⟩ → Holds y
    into y y∈ = PT.rec
      (isProp× (snd (fst y ∈ fst (lookup w γ)))
               (snd (envOne (fst y) ∈ fst (Sat A (toS ψ)))))
      step (subst (λ X → ⟨ fst y ∈ X ⟩) (sym qz) y∈)
      where
      step : Fibre ψ (fst y) → Holds y
      step ((m , hm) , qm) =
          subst (λ u → ⟨ u ∈ fst (lookup w γ) ⟩) qm
            (subst (λ X → ⟨ ιA m ∈ X ⟩) (sym qw) (ιA∈ m))
        , subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) qm
            (inSat ψ m ∣ (m , hm) , refl ∣₁)

    back : (y : S) → Holds y → ⟨ fst y ∈ fst z ⟩
    back y (yw , ys) = subst (λ X → ⟨ fst y ∈ X ⟩) qz
      (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
        (outSat ψ (fib .fst)
          (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩)
            (sym (fib .snd)) ys)))
      where
      fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ fst y)
      fib = ∈-asFiber {a = fst y} {b = fst A}
        (subst (λ X → ⟨ fst y ∈ X ⟩) qw yw)

    hdef : ⟨ δ ⊨ DefinesAt (suc (suc zero)) (sh3 w) zero ⟩
    hdef = DefinesAt-both (suc (suc zero)) (sh3 w) zero δ into back

  read : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
       → (z c v : S) → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩
       → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
  read {n} w γ qw z c v (hcode , (hgraph , hdef)) =
    PT.rec squash₁ step (codeAt-out A (suc zero) (sh3 w) δ qw hcode)
    where
    δ : S ^ (suc (suc (suc n)))
    δ = v ∷ c ∷ z ∷ γ

    step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (fst c ≡ fst (keyS A ψ))
         → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
    step (ψ , qc) = ∣ ψ , extensionality (DA.defSet ψ) (fst z) (sub₁ , sub₂) ∣₁
      where
      qv : fst v ≡ fst (Sat A (toS ψ))
      qv = graphAt-unique A (toS ψ) (sh3 w) (suc zero) zero δ qw
             (qc ∙ keyBridge A ψ) hgraph

      sub₁ : ⟨ DA.defSet ψ ⊆ fst z ⟩
      sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = fst z} .fst
        (PT.rec (snd (y ∈ fst z)) place
          (∈∈ₛ {a = y} {b = DA.defSet ψ} .snd y∈ₛ))
        where
        place : Fibre ψ y → ⟨ y ∈ fst z ⟩
        place ((m , hm) , qm) =
          DefinesAt-in (suc (suc zero)) (sh3 w) zero δ hdef
            (y , isL-trans {x = fst A} {y = y}
                   (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m)) (snd A))
            ( subst (λ X → ⟨ y ∈ X ⟩) (sym qw)
                (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m))
            , subst (λ X → ⟨ envOne y ∈ X ⟩) (sym qv)
                (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) qm
                  (inSat ψ m ∣ (m , hm) , refl ∣₁)) )

      sub₂ : ⟨ fst z ⊆ DA.defSet ψ ⟩
      sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DA.defSet ψ} .fst
        (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
          (outSat ψ (fib .fst)
            (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) (sym (fib .snd))
              (subst (λ X → ⟨ envOne y ∈ X ⟩) qv (cond .snd)))))
        where
        y∈ : ⟨ y ∈ fst z ⟩
        y∈ = ∈∈ₛ {a = y} {b = fst z} .snd y∈ₛ

        yS : S
        yS = y , isL-trans {x = fst z} {y = y} y∈ (snd z)

        cond : ⟨ y ∈ fst (lookup w γ) ⟩ × ⟨ envOne y ∈ fst v ⟩
        cond = DefinesAt-out (suc (suc zero)) (sh3 w) zero δ hdef yS y∈

        fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ y)
        fib = ∈-asFiber {a = y} {b = fst A}
          (subst (λ X → ⟨ y ∈ X ⟩) qw (cond .fst))
  private
    describe : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
             → (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
             → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
    describe w γ qw z = PT.rec squash₁ viaCode
      where
      Target : Type (ℓ-suc ℓ)
      Target = ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁

      viaValue : (c : S)
               → Σ[ v ∈ S ] ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩ → Target
      viaValue c (v , hv) = read w γ qw z c v hv

      viaCode : Σ[ c ∈ S ] ⟨ (c ∷ z ∷ γ) ⊨ ∃̇ (DefBody w) ⟩ → Target
      viaCode (c , hc) = PT.rec squash₁ (viaValue c) hc

    assemble : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
             → (z : S)
             → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
             → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
    assemble w γ qw z = PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)))) step
      where
      step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)
           → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
      step (ψ , qψ) = ∣ keyS A ψ , ∣ Sat A (toS ψ) , fill w γ qw z ψ qψ ∣₁ ∣₁

  DefAt-in : ∀ {n} (u w : Fin n) (γ : S ^ n)
           → fst (lookup w γ) ≡ fst A
           → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
           → ⟨ γ ⊨ DefAt u w ⟩
  DefAt-in {n} u w γ qw qu = extAt-in-both u Φ γ f g
    where
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (DefBody w))

    f : (z : S) → ⟨ fst z ∈ fst (lookup u γ) ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
    f z z∈ = assemble w γ qw z
      (𝒟ₒ-inv (fst A) (fst z) (subst (λ X → ⟨ fst z ∈ X ⟩) qu z∈))

    g : (z : S) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ fst (lookup u γ) ⟩
    g z hz = subst (λ X → ⟨ fst z ∈ X ⟩) (sym qu)
      (𝒟ₒ-intro (fst A) (fst z) (describe w γ qw z hz))

  DefAt-out : ∀ {n} (u w : Fin n) (γ : S ^ n) → DefOK A
            → fst (lookup w γ) ≡ fst A
            → ⟨ γ ⊨ DefAt u w ⟩
            → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
  DefAt-out {n} u w γ ok qw h =
    extensionality (fst (lookup u γ)) (𝒟ₒ (fst A)) (sub₁ , sub₂)
    where
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (DefBody w))

    sub₁ : ⟨ fst (lookup u γ) ⊆ 𝒟ₒ (fst A) ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .fst
      (𝒟ₒ-intro (fst A) y (describe w γ qw yS (extAt-out u Φ γ h yS y∈)))
      where
      y∈ : ⟨ y ∈ fst (lookup u γ) ⟩
      y∈ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .snd y∈ₛ

      yS : S
      yS = y , isL-trans {x = fst (lookup u γ)} {y = y} y∈ (snd (lookup u γ))

    sub₂ : ⟨ 𝒟ₒ (fst A) ⊆ fst (lookup u γ) ⟩
    sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .fst
      (extAt-in u Φ γ h yS
        (assemble w γ qw yS (𝒟ₒ-inv (fst A) y y∈)))
      where
      y∈ : ⟨ y ∈ 𝒟ₒ (fst A) ⟩
      y∈ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .snd y∈ₛ

      yS : S
      yS = y , ok y y∈
