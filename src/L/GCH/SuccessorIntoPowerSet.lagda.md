<!--en-->
# Injecting the successor cardinal into the power set

Cantor rules out an injection from the power set back into the base cardinal. By well-ordering the power set inside `L` and comparing its order type with the successor cardinal, this chapter constructs the injection in the other direction.
<!--zh-->
# 把后继基数单射到幂集

Cantor 定理排除了从幂集到原基数的单射。本章在 `L` 内部良序化幂集，并把其序型与后继基数比较，从而构造反方向的单射。
<!--ja-->
# 後続基数を冪集合へ単射する

Cantor の定理は、冪集合からもとの基数への単射を排除する。本章では `L` の内部で冪集合を整列し、その順序型を後続基数と比較して、逆向きの単射を構成する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SuccessorIntoPowerSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import L.Cardinal {ℓ} lem using ( InjCode; InjL; SuccCardL )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate; inclusion-coded; injl-trans; module Relation )
open import L.Coding.Model {ℓ} using ( svAt-out; domAt-in )
open import L.Coding.Injection {ℓ} lem using ( injAt-out )
open import L.GCH.BelowSuccessorCardinal {ℓ} lem using ( below-succ-injects )
open import L.GCH.Assembly {ℓ} lem using ( SuccIntoPower )
open import L.DefinableInjection {ℓ} lem using ( module Inj )
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

Satisfaction, read exactly as `L.DefinableInjection` reads it.

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Two elements of L with the same underlying set are equal.

```agda
S≡ : {x y : SL.S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))
```

<!--en-->
## Internal subsets belong to the model's power set

The model's power-set witness contains exactly its internal subsets. Unfolding that specification turns a proof of `y ⊆ˢ κ` directly into membership in `𝒫 κ`.
<!--zh-->
## 内部子集属于模型的幂集

模型的幂集见证恰好包含其内部子集。展开这一规格，`y ⊆ˢ κ` 的证明便直接给出 `y` 属于 `𝒫 κ`。
<!--ja-->
## 内部部分集合はモデルの冪集合に属する

モデルの冪集合の証人は、その内部部分集合をちょうど含む。この仕様を展開すると、`y ⊆ˢ κ` の証明から `y ∈ 𝒫 κ` が直接得られる。
<!--/-->

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

<!--en-->
## Cantor's diagonal argument inside L

No coded injection sends the model's power set of `κ` into `κ`. Separation forms the diagonal subset internally, and injectivity forces the usual contradiction at its own image.
<!--zh-->
## L 内部的 Cantor 对角论证

不存在把模型中的 `κ` 的幂集送入 `κ` 的编码单射。分离在内部形成对角子集，而单射性在该子集自身的像处引出通常的矛盾。
<!--ja-->
## L の内部での Cantor の対角線論法

モデルにおける `κ` の冪集合から `κ` への符号化された単射は存在しない。分出によって内部で対角部分集合を作ると、単射性からその像自身における通常の矛盾が生じる。
<!--/-->

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

<!--en-->
## Ordering the power set and comparing its order type

A coded injection of `𝒫 κ` into an ordinal pulls membership back to a strict well-order on the power set. Collapsing this relation yields an ordinal `μ` together with injections relating `𝒫 κ`, `μ`, and the comparison ordinal `δ`.
<!--zh-->
## 良序化幂集并比较其序型

把 `𝒫 κ` 编码单射到一个序数，可将隶属关系拉回为幂集上的严格良序。塌缩这个关系得到序数 `μ`，以及联系 `𝒫 κ`、`μ` 与比较序数 `δ` 的诸单射。
<!--ja-->
## 冪集合を整列してその順序型を比較する

`𝒫 κ` から順序数への符号化された単射に沿って所属を引き戻すと、冪集合上の狭義整列順序が得られる。この関係を崩壊すると、順序数 `μ` と、`𝒫 κ`、`μ`、比較対象の順序数 `δ` を結ぶ単射が得られる。
<!--/-->

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

<!--en-->
### The pullback order is a set of L

Two subsets are related when their coded ordinal images are ordered by membership. Bounded relation construction realizes this pullback relation as a set in `L`.
<!--zh-->
### 拉回序是 L 中的集合

当两个子集的编码序数像按隶属关系有序时，就令它们相关。有界关系构造把这一拉回关系实现为 `L` 中的集合。
<!--ja-->
### 引き戻した順序は L の集合である

二つの部分集合の符号化された順序数像が所属によって順序付けられるとき、それらを関係付ける。有界関係の構成により、この引き戻し関係は `L` の集合として実現される。
<!--/-->

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

<!--en-->
### Collapsing the ordered power set

The order-type construction applies to the power set with its pullback relation. Its collapse maps the power set bijectively onto a transitive set.
<!--zh-->
### 塌缩已排序的幂集

序型构造施于幂集及其拉回关系。它的塌缩把幂集双射到一个传递集。
<!--ja-->
### 順序付けた冪集合を崩壊する

冪集合とその引き戻し関係に順序型の構成を適用する。その崩壊は冪集合を推移的集合へ全単射で写す。
<!--/-->

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

<!--en-->
### The collapse image is an ordinal

Transitivity and trichotomy of the pullback order transfer across the collapse. The transitive collapse image is therefore an ordinal.
<!--zh-->
### 塌缩像是序数

拉回序的传递性与三歧性经塌缩保持不变，因而这个传递的塌缩像是序数。
<!--ja-->
### 崩壊像は順序数である

引き戻し順序の推移性と三分性は崩壊を通して移る。したがって、推移的な崩壊像は順序数である。
<!--/-->

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

<!--en-->
### The inverse collapse is definable

Reversing the collapse table defines a map from the collapse ordinal back into the power set. Its graph is a set of `L`, so the inverse is available internally as a coded injection.
<!--zh-->
### 逆塌缩是可定义的

反转塌缩表即可定义从塌缩序数回到幂集的映射。其图是 `L` 中的集合，因此这个逆映射在内部可用作编码单射。
<!--ja-->
### 崩壊の逆写像は定義可能である

崩壊表を逆に読むと、崩壊順序数から冪集合への写像が定義できる。そのグラフは `L` の集合なので、逆写像を内部で符号化された単射として利用できる。
<!--/-->

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

<!--en-->
### Comparing the collapse ordinal with `δ`

Ordinal trichotomy compares the collapse ordinal `μ` with `δ`. The cases `μ ∈ δ` and `μ ≡ δ` contradict Cantor after composing the available injections, leaving `δ ∈ μ`.
<!--zh-->
### 比较塌缩序数与 `δ`

序数三歧比较塌缩序数 `μ` 与 `δ`。`μ ∈ δ` 和 `μ ≡ δ` 两种情形都会在复合已有单射后违背 Cantor 定理，因此只剩 `δ ∈ μ`。
<!--ja-->
### 崩壊順序数を `δ` と比較する

順序数の三分性によって崩壊順序数 `μ` と `δ` を比較する。`μ ∈ δ` と `μ ≡ δ` は、得られた単射を合成すると Cantor の定理に反するので、`δ ∈ μ` だけが残る。
<!--/-->

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

<!--en-->
## The successor cardinal reaches the power set

Since `δ` lies below the order type `μ`, the collapse maps `δ` injectively into the power set. This supplies the third internal estimate required by the GCH assembly.
<!--zh-->
## 后继基数到达幂集

因为 `δ` 位于序型 `μ` 以下，塌缩便给出从 `δ` 到幂集的单射。这是证明 GCH 所需的第三条内部估计。
<!--ja-->
## 後続基数から冪集合へ到達する

`δ` は順序型 `μ` より小さいので、崩壊写像は `δ` を冪集合へ単射する。これで GCH の組み立てに必要な第三の内部評価が得られる。
<!--/-->

```agda
succ-into-power : (zf : ModelL.isZFModel) → SuccIntoPower zf
succ-into-power zf κ δ κ∉ω sc =
  PT.rec squash₁ (λ { (G , code) → Build.result zf κ δ sc G code })
```
