# The existential frame

<!--en-->
The order descriptions bind several sets, and each binder is a truncated
existential. The satisfaction relation unfolds the binders into a nested
truncation tower. A chapter that reads or writes such a tower walks one layer at
a time. This chapter supplies that walk once, generic in the carrier.

The frame has two halves. The **elimination** half turns a nested tower into the
flat existential it describes. The **introduction** half turns the flat
existential back into the tower. The nested tower is never stored as a
structure; it is the satisfaction relation's own normal form, so a consumer that
uses the frame sees the same types it saw when the tower was written by hand.
The two halves are the same shape at every arity, and the wing's clauses can
instantiate them directly.
<!--zh-->
序的诸描述绑定若干集合，而每个绑定都是一个截断的存在。满足关系把绑定展开成一座嵌套的截断塔。一章若要读或写这样一座塔，就得一层一层地走。本章把那次行走提供一次，对载体保持通用。

框架有两半。**消去**半把嵌套的塔变回它所描述的那个平铺存在。**引入**半把平铺的存在变回塔。塔从不被存成一个结构；它就是满足关系自己的正规形，故使用框架的消费方所见到的类型，与手写塔时所见相同。两半在任何元数处都是同一个形状，而翼的各子句可以直接实例化它们。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

module L.Choice.Frame {ℓ : Level} (S : Type ℓ) where
```

<!--en-->
## Eliminating the tower
<!--zh-->
## 消去那座塔
<!--/-->

<!--en-->
The elimination of six plain layers is the pattern the naming chapter's `∃₆`
reads and writes. Each step peels one truncation, and the innermost layer
rebuilds the flat tuple. The site supplies the family; the tower's shape
decides the rest.
<!--zh-->
六层无谓词层的消去，正是命名一章的 `∃₆` 所读所写的那个模式。每步剥开一层截断，最内层重建平铺的元组。站点提供族；塔的形状决定其余。
<!--/-->

```agda
  unpack₆ : {B : S → S → S → S → S → S → Type ℓ}
          → Σ[ s₁ ∈ S ] ∥ Σ[ k₁ ∈ S ] ∥ Σ[ p₁ ∈ S ] ∥ Σ[ s₂ ∈ S ] ∥ Σ[ k₂ ∈ S ]
              ∥ Σ[ p₂ ∈ S ] B s₁ k₁ p₁ s₂ k₂ p₂ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
          → ∥ Σ[ s₁ ∈ S ] Σ[ k₁ ∈ S ] Σ[ p₁ ∈ S ] Σ[ s₂ ∈ S ] Σ[ k₂ ∈ S ]
               Σ[ p₂ ∈ S ] B s₁ k₁ p₁ s₂ k₂ p₂ ∥₁
  unpack₆ (s₁ , h) = PT.rec squash₁ (λ (k₁ , h) → PT.rec squash₁
    (λ (p₁ , h) → PT.rec squash₁ (λ (s₂ , h) → PT.rec squash₁
      (λ (k₂ , h) → PT.map (λ (p₂ , b) → s₁ , (k₁ , (p₁ , (s₂ , (k₂ , (p₂ , b)))))) h)
        h) h) h) h
```

<!--en-->
Three layers with a predicate on the first are the comparison's shape: an
index, its membership conjunct, and two plain layers under it. The flat form
bundles the predicate with the innermost body.
<!--zh-->
带一个首层谓词的三层，是那次比较的形状：一个序号、它的隶属合取项，以及其下的两个平铺层。平铺形式把谓词与最内层的体捆在一起。
<!--/-->

```agda
  unpack₃P : {P : S → Type ℓ} {B : S → S → S → Type ℓ}
           → Σ[ i ∈ S ] ( P i
               × ∥ Σ[ u ∈ S ] ∥ Σ[ v ∈ S ] B i u v ∥₁ ∥₁ )
           → ∥ Σ[ i ∈ S ] Σ[ u ∈ S ] Σ[ v ∈ S ] ( P i × B i u v ) ∥₁
  unpack₃P (i , (p , h)) = PT.rec squash₁
    (λ (u , h) → PT.map (λ (v , b) → i , (u , (v , (p , b)))) h) h
```

<!--en-->
Four layers with a predicate on each are the denotation's shape. The three
outer predicates and the innermost body each reach a satisfaction, and the flat
form keeps them in the same order.
<!--zh-->
每层各带一个谓词的四层，是指称的形状。三个外层谓词与最内层的体各抵达一个满足，而平铺形式保持它们的次序不变。
<!--/-->

```agda
  unpack₄P : {Pc : S → Type ℓ} {Pk : S → S → Type ℓ} {Pkey : S → S → S → Type ℓ}
             {Q : S → S → S → S → Type ℓ}
           → Σ[ c ∈ S ] ( Pc c
               × ∥ Σ[ k ∈ S ] ( Pk c k
                   × ∥ Σ[ key ∈ S ] ( Pkey c k key
                       × ∥ Σ[ v ∈ S ] Q c k key v ∥₁ ) ∥₁ ) ∥₁ )
           → ∥ Σ[ c ∈ S ] Σ[ k ∈ S ] Σ[ key ∈ S ] Σ[ v ∈ S ]
               ( Pc c × Pk c k × Pkey c k key × Q c k key v ) ∥₁
  unpack₄P (c , (pc , h)) = PT.rec squash₁
    (λ (k , (pk , h)) → PT.rec squash₁
      (λ (key , (pkey , h)) → PT.map
        (λ (v , q) → c , (k , (key , (v , (pc , (pk , (pkey , q))))))) h) h) h
```

<!--en-->
The two-layer elimination with a site-supplied innermost step is the shape a
chapter reads when the innermost content carries mathematics of its own. The
target must be a proposition, which every truncated reading is.
<!--zh-->
带站点自供最内层步骤的两层消去，是当最内层内容自带数学时一章所读到的形状。目标必须是命题，而每条截断的读法都是。
<!--/-->

```agda
  unpack₂E : {B : S → S → Type ℓ} {C : Type ℓ}
           → isProp C
           → ((c d : S) → B c d → C)
           → Σ[ c ∈ S ] ∥ Σ[ d ∈ S ] B c d ∥₁ → C
  unpack₂E pc f (c , h) = PT.rec pc (λ (d , b) → f c d b) h
```

<!--en-->
## Introducing the tower
<!--zh-->
## 引入那座塔
<!--/-->

<!--en-->
The introduction of six plain layers rebuilds the tower from the flat tuple.
One squash per layer returns the binder. The site adds the outermost squash,
which its own formula's first binder owns.
<!--zh-->
六层无谓词层的引入，从平铺的元组重建那座塔。每层一个截断把绑定送回。最外层那个截断由站点自加，因为它属于站点公式自己的第一个绑定。
<!--/-->

```agda
  pack₆ : {B : S → S → S → S → S → S → Type ℓ}
        → (s₁ k₁ p₁ s₂ k₂ p₂ : S) → B s₁ k₁ p₁ s₂ k₂ p₂
        → Σ[ s₁ ∈ S ] ∥ Σ[ k₁ ∈ S ] ∥ Σ[ p₁ ∈ S ] ∥ Σ[ s₂ ∈ S ] ∥ Σ[ k₂ ∈ S ]
            ∥ Σ[ p₂ ∈ S ] B s₁ k₁ p₁ s₂ k₂ p₂ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  pack₆ s₁ k₁ p₁ s₂ k₂ p₂ b =
    s₁ , ∣ k₁ , ∣ p₁ , ∣ s₂ , ∣ k₂ , ∣ p₂ , b ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
```

<!--en-->
The frame is the shape only. Every site keeps its own family, its own
predicates and its own innermost mathematics. The wing's clauses instantiate
the same four eliminators and the same pack, and they share nothing else.
<!--zh-->
框架只是形状。每个站点保留自己的族、自己的谓词、自己最内层的数学。翼的各子句实例化同四个消去子与同一次引入，此外不共享任何东西。
<!--/-->
