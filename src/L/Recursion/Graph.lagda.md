<!--en-->
# Graphs of recursive definitions

A recursion internalized as a value table also has a graph in `L`: replacement collects the ordered pairs of each input with its uniquely determined value. The resulting set comes with membership directions, single-valuedness, and a formula describing its domain.
<!--zh-->
# 递归定义的图

已经内化为取值表的递归在 `L` 中也有图：替换把每个输入与其唯一确定的取值组成的有序对收集起来。所得集合附带两个隶属方向、单值性，以及描述其定义域的公式。
<!--ja-->
# 再帰的定義のグラフ

値の表として内部化された再帰は `L` 内にグラフも持ちます。置換公理が各入力と一意に定まる値との順序対を集め、得られた集合には二つの所属方向、単値性、定義域を記述する論理式が備わります。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.Recursion.Graph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( Recursion; module Of )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; svAt; svAt-in; domAt; domAt-intro )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isPropΣ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## A formula for ordered pairs

`PairFo`{.Agda} turns a binary value relation into a formula saying that one set is the ordered pair of an input and a related output. Its two readings connect satisfaction of that formula with the ambient pairing operation.
<!--zh-->
## 有序对的公式

`PairFo`{.Agda} 把二元取值关系变成一条公式，陈述某个集合是输入与相关输出组成的有序对。它的两条读式把该公式的满足关系与环境配对运算对应起来。
<!--ja-->
## 順序対を表す論理式

`PairFo`{.Agda} は二項の値関係を、ある集合が入力とそれに関係する出力との順序対であると述べる論理式へ変えます。二つの読みが、この論理式の充足と周囲の対演算を対応づけます。
<!--/-->

Renaming uses the model's satisfaction relation.

```agda
module Ren = Sat 𝒮ʟ id using ( Agrees; ⊨-rename )
```

The pair form of a graph, over `(e ∷ p ∷ [])`: "`e` is the pair of `p` and some
`z` with `φ z p`" (the shape src/L/Hierarchy.lagda.md pays for the hierarchy).
Inside the binder `z` is 0, `e` is 1, `p` is 2.

```agda
module PairFo (φ : Formula S 2) where

  ρ : Fin 2 → Fin 3
  ρ zero       = zero
  ρ (suc zero) = suc (suc zero)

  opaque
    pairFo : Formula S 2
    pairFo = ∃̇ (prAtL (suc zero) (suc (suc zero)) zero ∧̇ renameFo ρ φ)

    private
      ag : (z e p : S) → Ren.Agrees ρ (z ∷ e ∷ p ∷ []) (z ∷ p ∷ [])
      ag z e p zero       = refl
      ag z e p (suc zero) = refl

      at : (z e p : S)
         → ⟨ (z ∷ e ∷ p ∷ []) ⊨ prAtL (suc zero) (suc (suc zero)) zero ⟩
         ≡ (fst e ≡ pr (fst p) (fst z))
      at z e p = cong ⟨_⟩ (prAtL-adequate (suc zero) (suc (suc zero)) zero (z ∷ e ∷ p ∷ []))

      gr : (z e p : S)
         → ⟨ (z ∷ e ∷ p ∷ []) ⊨ renameFo ρ φ ⟩ ≡ ⟨ (z ∷ p ∷ []) ⊨ φ ⟩
      gr z e p = cong ⟨_⟩ (Ren.⊨-rename ρ φ (z ∷ e ∷ p ∷ []) (z ∷ p ∷ []) (ag z e p))

    pair-out : (e p : S) → ⟨ (e ∷ p ∷ []) ⊨ pairFo ⟩
             → ∥ Σ[ z ∈ S ] ((fst e ≡ pr (fst p) (fst z)) × ⟨ (z ∷ p ∷ []) ⊨ φ ⟩) ∥₁
    pair-out e p = PT.map (λ { (z , (q , h)) →
      z , (transport (at z e p) q , transport (gr z e p) h) })

    pair-in : (e p z : S) → fst e ≡ pr (fst p) (fst z) → ⟨ (z ∷ p ∷ []) ⊨ φ ⟩
            → ⟨ (e ∷ p ∷ []) ⊨ pairFo ⟩
    pair-in e p z q h = ∣ z , (transport (sym (at z e p)) q , transport (sym (gr z e p)) h) ∣₁
```

<!--en-->
## Domain and values

`Graph R` reads the domain and uniquely determined value function directly from the recursion record. Membership in the domain is kept as a proposition, so the selected value is independent of its membership proof.
<!--zh-->
## 定义域与取值

`Graph R` 直接从递归 record 读出定义域与唯一确定的取值函数。定义域中的隶属是命题，因此选出的值不依赖其隶属证明。
<!--ja-->
## 定義域と値

`Graph R` は再帰 record から定義域と一意に定まる値関数を直接読み出します。定義域への所属は命題なので、選ばれた値は所属証明に依存しません。
<!--/-->

```agda
module Graph (R₀ : Recursion) where
  open Of R₀ public using ( dom; graph; funct ) renaming ( val to fn )
```

Membership in the domain, as `fn` consumes it.

```agda
  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ fst dom ⟩

  isPropMem : (x : S) → isProp (Mem x)
  isPropMem x = snd (fst x ∈ fst dom)

  private
    defines : (x : S) (m : Mem x) → ⟨ (fn x m ∷ x ∷ []) ⊨ graph ⟩
    defines x m = funct x m .fst .snd

    only : (x : S) (m : Mem x) (y : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x m
    only x m y h = sym (cong fst (funct x m .snd (y , h)))

    module Fo = PairFo graph renaming ( pairFo to fo; pair-out to out; pair-in to into )

```

The value does not depend on which membership proof was given.

```agda
    fn-irr : (x : S) (m m' : Mem x) → fn x m ≡ fn x m'
    fn-irr x m m' = cong (fn x) (isPropMem x m m')
```

<!--en-->
## Collecting the graph

Replacement collects the ordered pairs into `F`{.Agda}. The membership theorems read a pair in either direction, while `sv`{.Agda} and `dm`{.Agda} state that the collected relation is single-valued and has exactly the recursion's domain.
<!--zh-->
## 收集图

替换把诸有序对收集为 `F`{.Agda}。隶属定理从两个方向读取一个对，而 `sv`{.Agda} 与 `dm`{.Agda} 说明所得关系单值，且其定义域恰是递归的定义域。
<!--ja-->
## グラフを集める

置換公理が順序対を `F`{.Agda} に集めます。所属定理が対を双方向に読み、`sv`{.Agda} と `dm`{.Agda} は得られた関係が単値で、その定義域が元の再帰の定義域と一致することを述べます。
<!--/-->

The pair, as an element of L.

```agda
    pairOf : (x : S) → Mem x → S
    pairOf x m = prʟ x (fn x m)

    uniq : (x : S) (m : Mem x) (p : S) → ⟨ (p ∷ x ∷ []) ⊨ Fo.fo ⟩ → p ≡ pairOf x m
    uniq x m p h = PT.rec (isSetS p (pairOf x m))
      (λ { (z , (e , g)) → Σ≡Prop (λ v → snd (isL v))
        (e ∙ cong (λ w → pr (fst x) (fst w)) (only x m z g) ∙ sym (prʟ-fst x (fn x m))) })
      (Fo.out p x h)

    R : Recursion
    R = record
      { dom   = dom
      ; graph = Fo.fo
      ; funct = λ x m →
          ( pairOf x m
          , Fo.into (pairOf x m) x (fn x m) (prʟ-fst x (fn x m)) (defines x m) )
        , λ { (p , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ Fo.fo)) (sym (uniq x m p h)) } }

    module T = Of R using ( table; table-in; table-out )

  F : S
  F = T.table

  F-in : (x : S) (m : Mem x) → ⟨ pr (fst x) (fst (fn x m)) ∈ fst F ⟩
  F-in x m = subst (λ w → ⟨ w ∈ fst F ⟩) (prʟ-fst x (fn x m))
    (T.table-in x (pairOf x m) m
      (Fo.into (pairOf x m) x (fn x m) (prʟ-fst x (fn x m)) (defines x m)))

  F-out : (p : V ℓ) → ⟨ p ∈ fst F ⟩
        → ∥ Σ[ x ∈ S ] Σ[ m ∈ Mem x ] (p ≡ pr (fst x) (fst (fn x m))) ∥₁
  F-out p h = PT.rec squash₁ step (T.table-out pS h)
    where
    pS : S
    pS = p , isL-trans {x = fst F} {y = p} h (snd F)

    step : Σ[ x ∈ S ] (Mem x × ⟨ (pS ∷ x ∷ []) ⊨ Fo.fo ⟩)
         → ∥ Σ[ x ∈ S ] Σ[ m ∈ Mem x ] (p ≡ pr (fst x) (fst (fn x m))) ∥₁
    step (x , (m , g)) = PT.map
      (λ { (z , (e , gz)) →
        x , m , (e ∙ cong (λ w → pr (fst x) (fst w)) (only x m z gz)) })
      (Fo.out pS x g)
```

A pair in `F`, read as a value of `fn`. The target is a proposition, so the
truncation comes off.

```agda
  Fib : S → S → Type (ℓ-suc ℓ)
  Fib x y = Σ[ m ∈ Mem x ] (fst y ≡ fst (fn x m))

  isPropFib : (x y : S) → isProp (Fib x y)
  isPropFib x y = isPropΣ (isPropMem x) (λ m → setIsSet (fst y) (fst (fn x m)))

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → Fib x y
  pair-out x y h = PT.rec (isPropFib x y) step (F-out (pr (fst x) (fst y)) h)
    where
    step : Σ[ x' ∈ S ] Σ[ m' ∈ Mem x' ] (pr (fst x) (fst y) ≡ pr (fst x') (fst (fn x' m')))
         → Fib x y
    step (x' , m' , e) = subst (λ z → Fib z y)
      (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj e .fst))) (m' , pr-inj e .snd)

```

THE CONJUNCTS.

```agda
  γ : S ^ 2
  γ = F ∷ dom ∷ []

  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ (λ x y y' p q →
    let (m , e)   = pair-out x y p
        (m' , e') = pair-out x y' q
    in e ∙ cong fst (fn-irr x m m') ∙ sym e')

  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → Mem x
    fwd x = PT.rec (isPropMem x) (λ { (y , p) → fst (pair-out x y p) })

    bwd : (x : S) → Mem x → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
    bwd x m = ∣ fn x m , F-in x m ∣₁

```
