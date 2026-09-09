<!--en-->
# Composition and inclusion of coded injections

Injection graphs inside `L` can be composed by separating the pairs connected through an intermediate value, and an inclusion of sets can be represented by the graph of the identity map. The same infrastructure also proves that `ω` cannot inject into the square of a finite ordinal, which supplies the finite exclusion needed by cardinal arguments.
<!--zh-->
# 编码单射的复合与包含

`L` 内部的注入图可通过分离由中间值连接的有序对来复合，而集合包含可由恒等映射的图呈现。同一套工具还证明 `ω` 不能注入有限序数的平方，给出基数论证所需的有限排除。
<!--ja-->
# 符号化された単射の合成と包含

`L` 内部の単射グラフは、中間値で結ばれる順序対を分出することで合成できます。また集合の包含は恒等写像のグラフとして提示できます。同じ仕組みにより、`ω` から有限順序数の平方への単射が存在しないことも示し、基数の議論に必要な有限の場合の排除を与えます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.InjectionComposition {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Model {ℓ} using ( appC; appC-adequate ) public
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-out; injAt-in; module Small )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.DefinableInjection {ℓ} lem
  using ( DefinableMap ) renaming ( module Inj to DefinableInj )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Foundations.Equiv as Equiv
open Equiv using ( equivFun; invEq; retEq; _≃_ )
open import Cubical.Foundations.Univalence using ( pathToEquiv )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_; ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )


open FiniteBase using ( ω-mem→numeral; toFin; toFin-inj; fromFin; fromFin-inj )
open FiniteBase using ( module AbstractChase )
```

<!--en-->
## A common constructible bound

Every small family of elements of `L` lies in one constructible set. `StageBound`{.Agda} packages that set and its membership proof so the later graph constructions can separate ordered pairs inside a single bound.
<!--zh-->
## 共同的可构造界

`L` 中元素的每个小族都落在某个可构造集合中。`StageBound`{.Agda} 封装该集合及其隶属证明，使后续图构造可在一个共同界内分离有序对。
<!--ja-->
## 共通の構成可能な上界

`L` の要素からなる小さな族は、一つの構成可能集合に含まれます。`StageBound`{.Agda} はその集合と所属証明をまとめ、後のグラフ構成が一つの共通の上界の中で順序対を分出できるようにします。
<!--/-->

The shared bound is `Recursion.smallDom`: a small family of elements of L
lies in one stage. The bound and its membership reader stay sealed, since every
consumer uses the bound as an atom.

```agda
module StageBound (I : Type ℓ) (g : I → S) where

  opaque
    bnd : S
    bnd = smallDom I g .fst

    below : (i : I) → ⟨ fst (g i) ∈ fst bnd ⟩
    below = smallDom I g .snd
```

<!--en-->
## Excluding finite targets

Every finite ordinal embeds into `ω`, whereas `ω` cannot inject into the square of a finite ordinal. Replacing an ordinal below `ω` by its numeral presentation yields the finite-exclusion lemma used in the injection chain.
<!--zh-->
## 排除有限目标

每个有限序数都嵌入 `ω`，而 `ω` 不能注入有限序数的平方。把 `ω` 以下的序数换成其数码呈现，即得注入链所需的有限排除引理。
<!--ja-->
## 有限な終域の排除

各有限順序数は `ω` へ埋め込めますが、`ω` から有限順序数の平方への単射は存在しません。`ω` より小さい順序数をその数項の提示へ置き換えると、単射の連鎖で使う有限の場合の排除が得られます。
<!--/-->

Row 5. The pairing on `ω`, by the order route, zero arithmetic.

The argument at `ω` needs the successor closure and limit behavior of the
natural numbers directly. The finite exclusion lemma remains useful to the
injection-chain construction below, so these facts are proved at the precise
strength consumed here.

Successor closure at `ω`: every member of `ω` is a numeral.

```agda
ω-limit : (γ : V ℓ) → ⟨ γ ∈ ω ⟩ → ⟨ sucV γ ∈ ω ⟩
ω-limit γ γ∈ω = PT.rec (snd (sucV γ ∈ ω)) go (ω-mem→numeral γ γ∈ω)
  where
  go : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ ω ⟩
  go (n , p) = subst (λ w → ⟨ sucV w ∈ ω ⟩) (sym p) (#∈ω (suc n))
```

No member of `ω` contains `ω`.

The numeral-into-`ω` injection, without `ω ∈ ω`.

```agda
numeral-into-ω : (m : ℕ) → ⟪ # m ⟫ → ⟪ ω ⟫
numeral-into-ω m i = fiber ω (ω-ord .fst (member (# m) i) (#∈ω m)) .fst

numeral-into-ω-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                   → numeral-into-ω m i₁ ≡ numeral-into-ω m i₂ → i₁ ≡ i₂
numeral-into-ω-inj m i₁ i₂ e = ↪-inj {a = # m}
  (sym (fiber ω (ω-ord .fst (member (# m) i₁) (#∈ω m)) .snd)
    ∙ cong (⟪ ω ⟫↪) e
    ∙ fiber ω (ω-ord .fst (member (# m) i₂) (#∈ω m)) .snd)
```

No injection of `ω` into a finite square.

```agda
no-inj-finite-ω : (n : ℕ) → (f : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
no-inj-finite-ω n f finj =
  AbstractChase.NoInj.no-inj
    (λ n → ⟪ # n ⟫)
    toFin toFin-inj
    fromFin fromFin-inj
    (⟪ ω ⟫)
    (numeral-into-ω)
    (numeral-into-ω-inj)
    n f finj
```

The finite-exclusion clause at `ω`.

```agda
finite-excl-ω : (β : V ℓ) → IsOrd β → ⟨ β ∈ ω ⟩
              → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
finite-excl-ω β oβ β∈ω f finj =
  PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
  where
  go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (n , p) = no-inj-finite-ω n f' finj'
    where
    e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
    e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
    f' : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
    f' x = equivFun e (f x)
    finj' : (x y : ⟪ ω ⟫) → f' x ≡ f' y → x ≡ y
    finj' x y e' = finj x y
      (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))
```

<!--en-->
## Relations as bounded pair graphs

`PairBound`{.Agda} bounds all ordered pairs from a chosen domain and codomain. Within that bound, `Relation`{.Agda} uses separation to turn any definable binary predicate into a constructible pair graph, with introduction and elimination rules for membership.
<!--zh-->
## 有界有序对图所呈现的关系

`PairBound`{.Agda} 约束选定定义域与陪域中的所有有序对。在此界内，`Relation`{.Agda} 用分离把任意可定义二元谓词化为可构造的有序对图，并给出隶属的引入与消去规则。
<!--ja-->
## 有界な順序対グラフとしての関係

`PairBound`{.Agda} は、選んだ定義域と終域からなるすべての順序対を一つの集合で抑えます。その中で `Relation`{.Agda} は分出を用い、定義可能な二項述語を構成可能な順序対グラフへ変え、所属の導入則と除去則を与えます。
<!--/-->

Row 1. The composition of two injection graphs, by separation.

`appC` reads each graph at a constant. The shared bounded relation binds the
two endpoints; the composite condition binds their intermediate value.

The bound for row 1, as an instance of the shared device.  The index
type is the pairs of a domain member and a codomain member, and the
family sends each pair to its coded ordered pair.  Nothing here builds
a bound: `StageBound` builds it once, for every row and for A6.

```agda
module PairBound (D C : S) where

  Ix : Type ℓ
  Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫

  private
    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

    pw : Ix → S
    pw (m , k) = prʟ (toD m) (toC k)

    module SB = StageBound Ix pw
```

An alias of a SEALED name, so it is an atom here too.

```agda
  bnd : S
  bnd = SB.bnd

  below : (x z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
        → ⟨ pr (fst x) (fst z) ∈ fst bnd ⟩
  below x z mx mz = subst (λ w → ⟨ w ∈ fst bnd ⟩) pa (SB.below i)
    where
    fD : Σ[ m ∈ ⟪ fst D ⟫ ] (⟪ fst D ⟫↪ m ≡ fst x)
    fD = fiber (fst D) mx
    fC : Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst z)
    fC = fiber (fst C) mz
    i : Ix
    i = fD .fst , fC .fst
    pa : fst (pw i) ≡ pr (fst x) (fst z)
    pa = prʟ-fst (toD (fD .fst)) (toC (fC .fst))
       ∙ cong₂ pr (fD .snd) (fC .snd)
```

A bounded relation uses the same separation and pair-injectivity proof for
products, orders, and counting graphs. Its description reads over `(y, x, e)`;
the host predicate depends only on the two components.

```agda
module Relation (D C : S) (φ : Formula S 3) (P : S → S → hProp (ℓ-suc ℓ))
                (read : (x y e : S) → ⟨ (y ∷ x ∷ e ∷ []) ⊨ φ ⟩ → ⟨ P x y ⟩)
                (fill : (x y e : S) → ⟨ P x y ⟩ → ⟨ (y ∷ x ∷ e ∷ []) ⊨ φ ⟩) where

  opaque
    fo : Formula S 1
    fo = ∃̇ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ φ))

    rel : S
    rel = hasSeparationL (PairBound.bnd D C) fo .fst .fst

    out : (e : S) → ⟨ fst e ∈ fst rel ⟩
        → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ] ((fst e ≡ pr (fst x) (fst y)) × ⟨ P x y ⟩) ∥₁
    out e h = PT.rec squash₁ (λ { (x , hx) → PT.map
      (λ { (y , q , hy) → x , y
         , subst ⟨_⟩ (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ e ∷ [])) q
         , read x y e hy }) hx })
      (subst ⟨_⟩ (hasSeparationL (PairBound.bnd D C) fo .fst .snd e) h .snd)

    into : (x y : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst y ∈ fst C ⟩ → ⟨ P x y ⟩
         → ⟨ pr (fst x) (fst y) ∈ fst rel ⟩
    into x y mx my h = subst (λ w → ⟨ w ∈ fst rel ⟩) (prʟ-fst x y)
      (subst ⟨_⟩ (sym (hasSeparationL (PairBound.bnd D C) fo .fst .snd (prʟ x y)))
        ( subst (λ w → ⟨ w ∈ fst (PairBound.bnd D C) ⟩) (sym (prʟ-fst x y))
            (PairBound.below D C x y mx my)
        , ∣ x , ∣ y
          , subst ⟨_⟩ (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ prʟ x y ∷ [])))
              (prʟ-fst x y)
          , fill x y (prʟ x y) h ∣₁ ∣₁ ))

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst rel ⟩ → ⟨ P x y ⟩
  pair-out x y h = PT.rec (snd (P x y))
    (λ { (x' , y' , q , h') →
      subst2 (λ a b → ⟨ P a b ⟩)
        (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj (sym (prʟ-fst x y) ∙ q) .fst)))
        (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj (sym (prʟ-fst x y) ∙ q) .snd))) h' })
    (out (prʟ x y) (subst (λ w → ⟨ w ∈ fst rel ⟩) (sym (prʟ-fst x y)) h))
```

<!--en-->
## Composing coded injections

Given coded injections from `D` to `E` and from `E` to `C`, the composite graph relates `x` to `z` when an intermediate `y` connects the two graphs. Its single-valuedness, total domain, injectivity, and range condition follow from the corresponding four properties of the inputs.
<!--zh-->
## 复合编码单射

给定从 `D` 到 `E` 以及从 `E` 到 `C` 的编码单射，复合图在存在中间值 `y` 连接两个图时把 `x` 关联到 `z`。其单值性、全定义域、单射性与值域条件均由两个输入的相应四项性质得到。
<!--ja-->
## 符号化された単射の合成

`D` から `E`、`E` から `C` への符号化された単射があるとき、中間値 `y` が二つのグラフを結ぶ場合に `x` と `z` を関係付けて合成グラフを作ります。その一価性、定義域、単射性、値域の条件は入力の対応する四条件から従います。
<!--/-->

The composite. Two graphs, four conjuncts each, not one replacement.

```agda
module Comp (D E C F H : S)
            (svF : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
            (dmF : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijF : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
            (ranF : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst E ⟩)
            (svH : ⟨ (H ∷ E ∷ []) ⊨ svAt zero ⟩)
            (dmH : ⟨ (H ∷ E ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijH : ⟨ (H ∷ E ∷ []) ⊨ injAt zero ⟩)
            (ranH : (y z : S) → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
                  → ⟨ fst z ∈ fst C ⟩) where

  private
    γF : S ^ 2
    γF = F ∷ D ∷ []

    γH : S ^ 2
    γH = H ∷ E ∷ []
```

The composite condition has one intermediate witness. Its two readings only
interpret the two application atoms; `Relation` supplies the pair graph.

```agda
  private
    Chain : S → S → Type (ℓ-suc ℓ)
    Chain x z = ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                             × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁

    opaque
      body : Formula S 3
      body = ∃̇ (appC F (suc (suc zero)) zero ∧̇ appC H zero (suc zero))

      read : (x z p : S) → ⟨ (z ∷ x ∷ p ∷ []) ⊨ body ⟩ → Chain x z
      read x z p = PT.map (λ { (y , hf , hh) → y
        , subst ⟨_⟩ (appC-adequate F (suc (suc zero)) zero (y ∷ z ∷ x ∷ p ∷ [])) hf
        , subst ⟨_⟩ (appC-adequate H zero (suc zero) (y ∷ z ∷ x ∷ p ∷ [])) hh })

      fill : (x z p : S) → Chain x z → ⟨ (z ∷ x ∷ p ∷ []) ⊨ body ⟩
      fill x z p = PT.map (λ { (y , hf , hh) → y
        , subst ⟨_⟩ (sym (appC-adequate F (suc (suc zero)) zero (y ∷ z ∷ x ∷ p ∷ []))) hf
        , subst ⟨_⟩ (sym (appC-adequate H zero (suc zero) (y ∷ z ∷ x ∷ p ∷ []))) hh })

    module Composite = Relation D C body (λ x z → Chain x z , squash₁) read fill

  K : S
  K = Composite.rel

  K-out : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
        → ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                      × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁
  K-out = Composite.pair-out

  K-in : (x y z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
       → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
       → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
  K-in x y z mx mz hf hh = Composite.into x z mx mz ∣ y , hf , hh ∣₁
```

The four conjuncts, for the composite.

```agda
  γK : S ^ 2
  γK = K ∷ D ∷ []

  svK : ⟨ γK ⊨ svAt zero ⟩
  svK = svAt-in zero γK (λ x y y' p q →
    PT.rec (setIsSet (fst y) (fst y'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst y) (fst y'))
        (λ { (w' , (hf' , hh')) →
          svAt-out zero γH svH w y y' hh
            (subst (λ t → ⟨ pr t (fst y') ∈ fst H ⟩)
              (sym (svAt-out zero γF svF x w w' hf hf')) hh') })
        (K-out x y' q) })
      (K-out x y p))

  ijK : ⟨ γK ⊨ injAt zero ⟩
  ijK = injAt-in zero γK (λ y x x' p q →
    PT.rec (setIsSet (fst x) (fst x'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst x) (fst x'))
        (λ { (w' , (hf' , hh')) →
          injAt-out zero γF ijF w x x' hf
            (subst (λ t → ⟨ pr (fst x') t ∈ fst F ⟩)
              (sym (injAt-out zero γH ijH y w w' hh hh')) hf') })
        (K-out x' y q) })
      (K-out x y p))

  dmK : ⟨ γK ⊨ domAt zero (suc zero) ⟩
  dmK = domAt-intro zero (suc zero) γK (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
        (λ { (w , (hf , _)) → domAt-out zero (suc zero) γF dmF x w hf })
        (K-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
    bwd x mx = PT.rec squash₁
      (λ { (w , hf) → PT.rec squash₁
        (λ { (z , hh) → ∣ z , K-in x w z mx (ranH w z hh) hf hh ∣₁ })
        (domAt-in zero (suc zero) γH dmH w (ranF x w hf)) })
      (domAt-in zero (suc zero) γF dmF x mx)

  ranK : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩ → ⟨ fst z ∈ fst C ⟩
  ranK x z h = PT.rec (snd (fst z ∈ fst C))
    (λ { (w , (_ , hh)) → ranH w z hh }) (K-out x z h)
```

The composite, read back as an honest function. Sealed.

```agda
  private
    module Sm = Small K D C svK dmK ijK ranK
```

<!--en-->
## Coding inclusions

A subset inclusion `D ⊆ C` becomes a coded injection by taking the identity map on `D` and defining its graph by equality. The resulting constructible graph can be read back as an injection between the small presentations, with ordinal inclusions as the principal instance.
<!--zh-->
## 符号化包含

集合包含 `D ⊆ C` 可通过取 `D` 上的恒等映射并用相等定义其图，化为编码单射。所得可构造图可读回小呈现之间的注入，而序数包含是其主要实例。
<!--ja-->
## 包含の符号化

部分集合包含 `D ⊆ C` は、`D` 上の恒等写像を取り、等号でそのグラフを定義することで、符号化された単射になります。得られた構成可能グラフは小さな提示の間の単射として読み出せ、順序数の包含が主要な具体例です。
<!--/-->

Row 3. The inclusion of one set into another.

The identity function on the domain has the graph formula `y = x`. The shared
definable-injection construction collects its argument-value pairs and supplies
the four coded-injection conjuncts. Equality gives uniqueness and injectivity;
the given subset inclusion supplies the range proof.

```agda
module InclGraph (D C : S)
                 (sub : (z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩) where

  private
    M : DefinableMap
    M = record
      { dom = D ; cod = C
      ; fn = λ x _ → x
      ; into = λ x mx → sub (fst x) mx
      ; graph = var zero ≐ var (suc zero)
      ; defines = λ _ _ → refl
      ; only = λ _ _ _ h → Σ≡Prop (λ w → snd (isL w)) h }

    module I = DefinableInj M (λ _ _ _ _ e → e)
      using ( F; code )

  opaque
    G : S
    G = I.F

```

The shared construction packages the opaque graph with its four injection
conjuncts. The small presentation consumes that package without exposing the
replacement graph.

```agda
  opaque
    unfolding G
    code : InjCode G D C
    code = I.code
```

The small presentation reads the same identity graph. The value remains sealed:
an unsealed `Small` application at this site previously exhausted an 8g heap.

```agda
  private
    module Sm = Small G D C (code .fst) (code .snd .fst)
      (code .snd .snd .fst) (code .snd .snd .snd)

  opaque
    incl : ⟪ fst D ⟫ → ⟪ fst C ⟫
    incl = Sm.small
```

<!--en-->
## Inclusion and composition at the internal-existence level

The graph constructions lift through propositional truncation to the internal injection relation. Thus every inclusion gives an internal coded injection, and two internal coded injections compose without choosing either graph globally.
<!--zh-->
## 内部存在层面的包含与复合

图构造可穿过命题截断提升到内部单射关系。因此，每个包含都给出内部编码单射，而两个内部编码单射无需在全局选定各自的图便可复合。
<!--ja-->
## 内部存在の水準における包含と合成

グラフの構成は命題的切り詰めを通して内部の単射関係へ持ち上がります。したがって、各包含から内部の符号化された単射が得られ、二つのグラフを大域的に選ぶことなく内部の符号化された単射を合成できます。
<!--/-->

```agda
inclusion-coded : (a b : S)
                → ((z : V ℓ) → ⟨ z ∈ fst a ⟩ → ⟨ z ∈ fst b ⟩)
                → InjL a b
inclusion-coded a b sub = ∣ I.G , I.code ∣₁
  where module I = InclGraph a b sub

injl-trans : (a b c : S) → InjL a b → InjL b c → InjL a c
injl-trans a b c = PT.rec2 PT.squash₁ step
  where
  step : Σ[ F ∈ S ] InjCode F a b
       → Σ[ H ∈ S ] InjCode H b c
       → InjL a c
  step (F , svF , dmF , ijF , ranF) (H , svH , dmH , ijH , ranH) =
    ∣ K.K , (K.svK , K.dmK , K.ijK , K.ranK) ∣₁
    where
    module K = Comp a b c F H svF dmF ijF ranF svH dmH ijH ranH
```

The ordinal inclusion, which is A5's row-3 object. The module is generic in the
ordinal: nothing below names a stage, a numeral or `ω`. The ordinal supplies the
subset witness through its own transitivity, and that is all it supplies.

```agda
module OrdIncl (C : S) (oC : IsOrd (fst C))
               (D : S) (D∈C : ⟨ fst D ∈ fst C ⟩) where

  open InclGraph D C (λ _ z∈D → oC .fst z∈D D∈C) public
```

<!--en-->
## Recap

This chapter provides three operations used by internal cardinal arguments: it rules out injections from `ω` into finite squares, composes constructible injection graphs, and turns inclusions into coded injections. These operations let us build and compare cardinal bounds using graphs that remain inside the model.
<!--zh-->
## 小结

本章提供内部基数论证所用的三项操作：排除从 `ω` 到有限平方的注入，复合可构造注入图，并把包含化为编码单射。`InjectionComposition` 准确概括其核心构造，而包含与有限排除接口则是同一链条上的配套结果。
<!--ja-->
## まとめ

本章は内部の基数論で使う三つの操作を与えます。`ω` から有限な平方への単射を排除し、構成可能な単射グラフを合成し、包含を符号化された単射へ変えます。これらの操作により、モデルの内部にとどまるグラフを用いて基数の上界を構成し、比較できます。
<!--/-->
