# The successor cardinal injects into the power set

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SuccIntoPower {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∃̇_; ∃̇∈ )
import FOL.ZFModel
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; isL-trans; isTransV; isPropIsTransV )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.InjChain {ℓ} lem using ( appC; appC-adequate; module Relation )
open import L.Coding.Model {ℓ} using ( svAt-out; domAt-in )
open import L.Coding.Injection {ℓ} lem using ( injAt-out )
open import L.GCH {ℓ} lem using ( SuccCardL; InjL )
open import L.GCH.BelowSucc {ℓ} lem using ( below-succ-injects )
open import L.GCH.Assembly {ℓ} lem
  using ( SuccIntoPower; inclusion-coded; injl-trans )
open import L.GCH.Definable {ℓ} lem using ( module Inj )
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
import Cubical.Induction.WellFounded as WF
open WF using ( Acc; acc; WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

The V-carrier: the ambient membership lives here.

```agda
module SV = hPropStructure 𝒮ᵥ using ( S )
```

The L-carrier: `SuccCardL`, `InjL` and the model live here.

```agda
module SL = hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
```

The instance src/L/GCH.lagda.md names, at the same 𝒮ʟ.

```agda
module ModelL = FOL.ZFModel 𝒮ʟ using ( isZFModel; module isZFModel; ℩-spec )
```

Satisfaction, read exactly as `L.GCH.Definable` reads it.

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Two elements of L with the same underlying set are equal.

```agda
S≡ : {x y : SL.S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))
```

## Section 1. A subset of `κ` is a member of the model's power set

`𝒫 κ` IS `℩ (hasPower κ)` by definition, so `℩-spec` is the whole proof. This is
the converse of `z-strongest` (src/L/GCH/Assembly.lagda.md), which reads the
same equation in the other direction. `_⊆ˢ_` is the model's own subset relation
(src/FOL/ZFModel.lagda.md), so it quantifies over L-elements only, and that is
exactly what the caller can supply.

```agda
into-power :
    (zf : ModelL.isZFModel) (κ y : SL.S)
  → ((z : SL.S) → ⟨ fst z ∈ˢ fst y ⟩ → ⟨ fst z ∈ˢ fst κ ⟩)
  → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
into-power zf κ y sub =
  subst ⟨_⟩ (sym (ModelL.℩-spec (hasPower κ) y)) sub
  where open ModelL.isZFModel zf using ( hasPower )
```

## Section 2. Cantor, inside L

No set of L codes an injection of the model's power set of `κ` into `κ`. The
diagonal set is carved out of `κ` by `hasSeparationL`, at the formula "some `A`
in the power set is sent to `ξ` and does not hold `ξ`". The bound on `A` is the
power set itself, so the quantifier is bounded. Injectivity of the code forces
that `A` to be the diagonal set at the diagonal set's own value, and the two
readings of that one membership contradict each other.

```agda
module Cantor (zf : ModelL.isZFModel) (κ : SL.S) where

  open ModelL.isZFModel zf using ( 𝒫 )

  module Diag (F : SL.S) (code : InjCode F (𝒫 κ) κ) where

    γF : SL.S ^ 2
    γF = F ∷ 𝒫 κ ∷ []

    ranF : (x y : SL.S) → Holds F x y → ⟨ fst y ∈ fst κ ⟩
    ranF = code .snd .snd .snd

    valF : (x : SL.S) → ⟨ fst x ∈ fst (𝒫 κ) ⟩
         → ∥ Σ[ y ∈ SL.S ] Holds F x y ∥₁
    valF = domAt-in zero (suc zero) γF (code .snd .fst)

    injF : (y x x' : SL.S) → Holds F x y → Holds F x' y → fst x ≡ fst x'
    injF = injAt-out zero γF (code .snd .snd .fst)

    Diagonal : SL.S → Type (ℓ-suc ℓ)
    Diagonal ξ = ∥ Σ[ A ∈ SL.S ] ( ⟨ fst A ∈ fst (𝒫 κ) ⟩ × Holds F A ξ
                                 × (⟨ fst ξ ∈ fst A ⟩ → Empty.⊥) ) ∥₁

    private
      a1 : (ξ A : SL.S)
         → ⟨ (A ∷ ξ ∷ []) ⊨ appC F zero (suc zero) ⟩ ≡ Holds F A ξ
      a1 ξ A = cong ⟨_⟩ (appC-adequate F zero (suc zero) (A ∷ ξ ∷ []))
```

Inside the binder: `A` is 0 and `ξ` is 1.

```agda
    opaque
      φD : Formula SL.S 1
      φD = ∃̇∈ (con (𝒫 κ))
             (appC F zero (suc zero) ∧̇ ¬̇ (var (suc zero) ∈̇ var zero))

      φD-out : (ξ : SL.S) → ⟨ (ξ ∷ []) ⊨ φD ⟩ → Diagonal ξ
      φD-out ξ = PT.map (λ { (A , (mA , (h , n))) →
        A , mA , transport (a1 ξ A) h , (λ k → lower (n k)) })

      φD-in : (ξ A : SL.S) → ⟨ fst A ∈ fst (𝒫 κ) ⟩ → Holds F A ξ
            → (⟨ fst ξ ∈ fst A ⟩ → Empty.⊥) → ⟨ (ξ ∷ []) ⊨ φD ⟩
      φD-in ξ A mA h n =
        ∣ A , (mA , (transport (sym (a1 ξ A)) h , (λ k → lift (n k)))) ∣₁

    D₀ : SL.S
    D₀ = fst (fst (hasSeparationL κ φD))

    D₀-spec : (ξ : SL.S) → (ξ SL.∈ˢ D₀) ≡ ((ξ SL.∈ˢ κ) ⊓ ((ξ ∷ []) ⊨ φD))
    D₀-spec = snd (fst (hasSeparationL κ φD))

    D₀∈𝒫κ : ⟨ fst D₀ ∈ fst (𝒫 κ) ⟩
    D₀∈𝒫κ = into-power zf κ D₀ (λ z h → fst (subst ⟨_⟩ (D₀-spec z) h))

    absurd : Σ[ ξ ∈ SL.S ] Holds F D₀ ξ → Empty.⊥
    absurd (ξ , h₀) = out inside
      where
```

`ξ` in the diagonal set: the witness `A` is `D₀` by injectivity.

```agda
      out : ⟨ fst ξ ∈ fst D₀ ⟩ → Empty.⊥
      out hm = PT.rec Empty.isProp⊥
        (λ { (A , _ , hA , n) →
          n (subst (λ w → ⟨ fst ξ ∈ w ⟩) (injF ξ D₀ A h₀ hA) hm) })
        (φD-out ξ (snd (subst ⟨_⟩ (D₀-spec ξ) hm)))
```

`ξ` outside the diagonal set: `D₀` itself is the witness.

```agda
      inside : ⟨ fst ξ ∈ fst D₀ ⟩
      inside = subst ⟨_⟩ (sym (D₀-spec ξ))
        (ranF D₀ ξ h₀ , φD-in ξ D₀ D₀∈𝒫κ h₀ out)

  no-inj : InjL (𝒫 κ) κ → Empty.⊥
  no-inj = PT.rec Empty.isProp⊥ step
    where
    step : Σ[ F ∈ SL.S ] InjCode F (𝒫 κ) κ → Empty.⊥
    step (F , code) = PT.rec Empty.isProp⊥ D.absurd (D.valF D.D₀ D.D₀∈𝒫κ)
      where module D = Diag F code
```

## Section 3. The order type of the power set, and the two injections

src/L/GCH/Assembly.lagda.md pays `InjL (𝒫 κ) δ` out of the first two internal
hypotheses alone, before this one is consumed. Take a code `G` for it. The
relation "the value of `G` at `A` is a member of its value at `B`" is a set of L
by the shared bounded-relation construction, and it is well-founded, transitive and
trichotomous on the presentation of `𝒫 κ` because the values are ordinals below
`δ` and `G` is injective. So `OrderType.Code` applies: `colTable` codes
`𝒫 κ ↪ otL`, and the converse of `colTable` codes `otL ↪ 𝒫 κ`, the
inverse-collapse pattern of `Pairing`'s `Step.Inv`.

`otL` is an ordinal: its members are values of the collapse, each an ordinal,
and it is transitive because a member of `col b` is `col r` for some `r`.

Trichotomy against `δ` closes the argument. Below `δ`, `below-succ-injects`
injects `otL` into `κ`, and then the power set injects into `κ` against
section 2. At or above `δ`, `δ` is a subset of `otL`, and an inclusion composed
with the inverse collapse is the theorem.

```agda
module Build (zf : ModelL.isZFModel) (κ δ : SL.S) (sc : SuccCardL δ κ)
             (G : SL.S)
             (code : InjCode G (ModelL.isZFModel.𝒫 zf κ) δ) where

  open ModelL.isZFModel zf using ( 𝒫 )

  ordδ : IsOrd (fst δ)
  ordδ = sc .fst

  P : SL.S
  P = 𝒫 κ

  γG : SL.S ^ 2
  γG = G ∷ P ∷ []

  ranG : (x y : SL.S) → Holds G x y → ⟨ fst y ∈ fst δ ⟩
  ranG = code .snd .snd .snd

  svG : (x y y' : SL.S) → Holds G x y → Holds G x y' → fst y ≡ fst y'
  svG = svAt-out zero γG (code .fst)

  valG : (x : SL.S) → ⟨ fst x ∈ fst P ⟩ → ∥ Σ[ y ∈ SL.S ] Holds G x y ∥₁
  valG = domAt-in zero (suc zero) γG (code .snd .fst)

  injG : (y x x' : SL.S) → Holds G x y → Holds G x' y → fst x ≡ fst x'
  injG = injAt-out zero γG (code .snd .snd .fst)
```

Single-valuedness makes the fibre a proposition, so the value is read out of the
truncation as a function.

```agda
  isPropVal : (x : SL.S) → isProp (Σ[ y ∈ SL.S ] Holds G x y)
  isPropVal x (y , h) (y' , h') =
    Σ≡Prop (λ w → snd (pr (fst x) (fst w) ∈ fst G)) (S≡ (svG x y y' h h'))

  val : (x : SL.S) → ⟨ fst x ∈ fst P ⟩ → Σ[ y ∈ SL.S ] Holds G x y
  val x m = PT.rec (isPropVal x) (λ z → z) (valG x m)
```

### 3.1 The pullback order, as a set of L

```agda
  Read : SL.S → SL.S → Type (ℓ-suc ℓ)
  Read a b = ∥ Σ[ x ∈ SL.S ] Σ[ y ∈ SL.S ]
               ( ⟨ fst a ∈ fst P ⟩ × ⟨ fst b ∈ fst P ⟩
               × Holds G a x × Holds G b y × ⟨ fst x ∈ fst y ⟩ ) ∥₁

  private
    env5 : SL.S → SL.S → SL.S → SL.S → SL.S → SL.S ^ 5
    env5 p A B x y = y ∷ x ∷ B ∷ A ∷ p ∷ []

    b1 : (p A B x y : SL.S)
       → ⟨ env5 p A B x y ⊨ appC G (suc (suc (suc zero))) (suc zero) ⟩
       ≡ Holds G A x
    b1 p A B x y = cong ⟨_⟩
      (appC-adequate G (suc (suc (suc zero))) (suc zero) (env5 p A B x y))

    b2 : (p A B x y : SL.S)
       → ⟨ env5 p A B x y ⊨ appC G (suc (suc zero)) zero ⟩ ≡ Holds G B y
    b2 p A B x y = cong ⟨_⟩
      (appC-adequate G (suc (suc zero)) zero (env5 p A B x y))

```

The two endpoints belong to the power set, and their two values under `G`
are ordered by membership. `Relation` supplies the pair encoding and bound.
Inside the two value binders, `y` is 0, `x` is 1, `B` is 2, and `A` is 3.

```agda
  private
    opaque
      φR : Formula SL.S 3
      φR = (var (suc zero) ∈̇ con P) ∧̇ ((var zero ∈̇ con P) ∧̇ ∃̇ (∃̇
        (appC G (suc (suc (suc zero))) (suc zero)
          ∧̇ (appC G (suc (suc zero)) zero ∧̇ (var (suc zero) ∈̇ var zero)))))

      read : (a b p : SL.S) → ⟨ (b ∷ a ∷ p ∷ []) ⊨ φR ⟩ → Read a b
      read a b p (ma , mb , h) = PT.rec squash₁
        (λ { (x , hx) → PT.map (λ { (y , ha , hb , hxy) → x , y , ma , mb
          , transport (b1 p a b x y) ha , transport (b2 p a b x y) hb , hxy }) hx }) h

      fill : (a b p : SL.S) → Read a b → ⟨ (b ∷ a ∷ p ∷ []) ⊨ φR ⟩
      fill a b p = PT.rec (snd ((b ∷ a ∷ p ∷ []) ⊨ φR))
        (λ { (x , y , ma , mb , ha , hb , hxy) → ma , mb , ∣ x , ∣ y
          , transport (sym (b1 p a b x y)) ha
          , transport (sym (b2 p a b x y)) hb , hxy ∣₁ ∣₁ })

    module Pullback = Relation P P φR (λ a b → Read a b , squash₁) read fill

  R : SL.S
  R = Pullback.rel

  R-out : (a b : SL.S) → Holds R a b → Read a b
  R-out = Pullback.pair-out

  R-in : (a b x y : SL.S) → ⟨ fst a ∈ fst P ⟩ → ⟨ fst b ∈ fst P ⟩
       → Holds G a x → Holds G b y → ⟨ fst x ∈ fst y ⟩ → Holds R a b
  R-in a b x y ma mb ha hb hxy = Pullback.into a b ma mb ∣ x , y , ma , mb , ha , hb , hxy ∣₁

  Rsub : (a b : SL.S) → Holds R a b
       → ⟨ fst a ∈ fst P ⟩ × ⟨ fst b ∈ fst P ⟩
  Rsub a b h = PT.rec
    (isProp× (snd (fst a ∈ fst P)) (snd (fst b ∈ fst P)))
    (λ { (_ , _ , ma , mb , _) → ma , mb })
    (R-out a b h)
```

### 3.2 The collapse, at `(𝒫 κ, R)`

```agda
  module OT = Code P R Rsub
    using ( Dom; Dom≡; toDom; up; up-mem; up-toDom; ↪; _≺_; ≺-in; ≺-out
          ; module Conjuncts )

  v : OT.Dom → SL.S
  v b = fst (val (OT.up b) (OT.up-mem b))

  v-holds : (b : OT.Dom) → Holds G (OT.up b) (v b)
  v-holds b = snd (val (OT.up b) (OT.up-mem b))

  v∈δ : (b : OT.Dom) → ⟨ fst (v b) ∈ fst δ ⟩
  v∈δ b = ranG (OT.up b) (v b) (v-holds b)

  ord-v : (b : OT.Dom) → IsOrd (fst (v b))
  ord-v b = mem-ord {A = fst δ} ordδ (fst (v b)) (v∈δ b)

  ≺-fwd : (a b : OT.Dom) → a OT.≺ b → ⟨ fst (v a) ∈ fst (v b) ⟩
  ≺-fwd a b k = PT.rec (snd (fst (v a) ∈ fst (v b)))
    (λ { (x , y , _ , _ , ha , hb , hxy) →
      subst2 (λ s t → ⟨ s ∈ t ⟩)
        (svG (OT.up a) x (v a) ha (v-holds a))
        (svG (OT.up b) y (v b) hb (v-holds b)) hxy })
    (R-out (OT.up a) (OT.up b) (OT.≺-out a b k))

  ≺-bwd : (a b : OT.Dom) → ⟨ fst (v a) ∈ fst (v b) ⟩ → a OT.≺ b
  ≺-bwd a b h = OT.≺-in a b
    (R-in (OT.up a) (OT.up b) (v a) (v b)
      (OT.up-mem a) (OT.up-mem b) (v-holds a) (v-holds b) h)

  private
    Pacc : V ℓ → Type (ℓ-suc ℓ)
    Pacc u = (b : OT.Dom) → fst (v b) ≡ u → Acc OT._≺_ b

    accStep : (u : V ℓ) → (∀ u' → ⟨ u' ∈ˢ u ⟩ → Pacc u') → Pacc u
    accStep u IH b e = acc (λ a k →
      IH (fst (v a)) (subst (λ w → ⟨ fst (v a) ∈ˢ w ⟩) e (≺-fwd a b k))
         a refl)

    accAt : (u : V ℓ) → Pacc u
    accAt = WF.WFI.induction regularityV {P = Pacc} accStep

  wf : WellFounded OT._≺_
  wf b = accAt (fst (v b)) b refl

  ≺-trans : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
  ≺-trans {a} {b} {c} k k' = ≺-bwd a c
    (ordδ .snd (fst (v c)) (v∈δ c) (≺-fwd a b k) (≺-fwd b c k'))

  tri : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
  tri a b = go (ord-tri (fst (v a)) (ord-v a) (fst (v b)) (ord-v b))
    where
    go : Tri (fst (v a)) (fst (v b))
       → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
    go (inl h)       = inl (≺-bwd a b h)
    go (inr (inl e)) = inr (inl (OT.Dom≡
      (injG (v a) (OT.up a) (OT.up b) (v-holds a)
        (subst (λ w → ⟨ pr (OT.↪ b) w ∈ fst G ⟩) (sym e) (v-holds b)))))
    go (inr (inr h)) = inr (inr (≺-bwd b a h))

  module C = OT.Conjuncts wf ≺-trans
    using ( module Inj; col; col-ord; col-out; colTable; colTable-in
          ; colTable-pair; otL; otL-in; otL-out )
  module I = C.Inj tri using ( code; col-inj; module Inverse )

  power-into-ot : InjL P C.otL
  power-into-ot = ∣ C.colTable , I.code ∣₁
```

### 3.3 The order type is an ordinal

```agda
  ot-ord : IsOrd (fst C.otL)
  ot-ord = tr , mem
    where
    mem : (x : V ℓ) → ⟨ x ∈ˢ fst C.otL ⟩ → isTransV x
    mem x h = PT.rec (isPropIsTransV x)
      (λ { (b , e) → subst isTransV e (C.col-ord b .fst) })
      (C.otL-out x h)

    tr : isTransV (fst C.otL)
    tr {x} {y} y∈x x∈ot =
      PT.rec (snd (y ∈ˢ fst C.otL)) outer (C.otL-out x x∈ot)
      where
      outer : Σ[ b ∈ OT.Dom ] (C.col b ≡ x) → ⟨ y ∈ˢ fst C.otL ⟩
      outer (b , e) = PT.rec (snd (y ∈ˢ fst C.otL)) inner
        (C.col-out b y (subst (λ w → ⟨ y ∈ˢ w ⟩) (sym e) y∈x))
        where
        inner : Σ[ r ∈ OT.Dom ] ((r OT.≺ b) × (C.col r ≡ y))
              → ⟨ y ∈ˢ fst C.otL ⟩
        inner (r , _ , e2) =
          subst (λ w → ⟨ w ∈ˢ fst C.otL ⟩) e2 (C.otL-in r)
```

### 3.4 The inverse collapse, as a definable map into the power set

The graph is the converse of `colTable`, read by `appC`: the pattern of
`Pairing`'s `Step.Inv`.

```agda
  Fib : V ℓ → Type (ℓ-suc ℓ)
  Fib w = Σ[ b ∈ OT.Dom ] (C.col b ≡ w)

  isPropFib : (w : V ℓ) → isProp (Fib w)
  isPropFib w (b , e) (b' , e') =
    Σ≡Prop (λ _ → setIsSet _ _) (I.col-inj b b' (e ∙ sym e'))

  fib : (w : V ℓ) → ⟨ w ∈ˢ fst C.otL ⟩ → Fib w
  fib w h = PT.rec (isPropFib w) (λ z → z) (C.otL-out w h)

  module Back where
    open I.Inverse C.otL P (λ w mw → fib (fst w) mw)
      (λ w mw → OT.up-mem (fib (fst w) mw .fst)) public
      using ( fn; graph; at; only; M; inj; injL ) renaming ( SourceMem to Mem )
```

### 3.5 Trichotomy against `δ`

```agda
  result : InjL δ P
  result = go (ord-tri (fst C.otL) ot-ord (fst δ) ordδ)
    where
    from-sub : ((z : SV.S) → ⟨ z ∈ˢ fst δ ⟩ → ⟨ z ∈ˢ fst C.otL ⟩)
             → InjL δ P
    from-sub sub =
      injl-trans δ C.otL P (inclusion-coded δ C.otL sub) Back.injL

    go : Tri (fst C.otL) (fst δ) → InjL δ P
    go (inl ot∈δ)       = Empty.rec (Cantor.no-inj zf κ
      (injl-trans P C.otL κ power-into-ot
        (below-succ-injects κ δ sc C.otL ot-ord ot∈δ)))
    go (inr (inl e))    =
      from-sub (λ z h → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) h)
    go (inr (inr δ∈ot)) =
      from-sub (λ z h → ot-ord .fst h δ∈ot)
```

## Section 4. Hypothesis 3 of src/L/GCH/Assembly.lagda.md, discharged

```agda
succ-into-power : (zf : ModelL.isZFModel) → SuccIntoPower zf
succ-into-power zf κ δ κ∉ω sc =
  PT.rec squash₁ (λ { (G , code) → Build.result zf κ δ sc G code })
```
