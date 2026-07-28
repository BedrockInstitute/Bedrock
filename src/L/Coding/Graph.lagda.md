# The graph

<!--en-->
What the recursion's graph says: there is an index set holding the subcodes of
its members, a table answering at every index and satisfying the twelve clauses,
and the value is what that table records at this index.

The carrier is bound rather than named, because every clause takes it as a slot
and none takes it as a term. Everything else is bound because a graph may not
name a table it has not been given, which is the one thing the internalization
theorem forbids: the recursion is what produces the table, so the graph that
defines it must quantify over tables rather than point at one.
<!--zh-->
递归的那个图说的是：存在一个含有其成员诸子码的索引集、一张在每个索引处作答且满足十二条子句的表，而那个取值就是该表在此索引处记录的东西。

载体是被绑定的、不是被点名的，因为每条子句都把它当作一个槽位、没有一条把它当作词项。其余一切被绑定，是因为**一个图不可以点名一张尚未交给它的表**，而那是内化定理唯一禁止的事：递归才是产出那张表的东西，故定义它的那个图必须对诸表作量化，而不能指着某一张。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Graph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( closedAt; domAt; appAt; appAt-adequate
        ; memClauseAt; eqClauseAt; andClauseAt; orClauseAt; impClauseAt
        ; negClauseAt; topClauseAt; botClauseAt; existClauseAt; forallClauseAt
        ; allInClauseAt; exInClauseAt )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The twelve, and the three that guard them
<!--zh-->
## 十二条，与守着它们的三条
<!--/-->

<!--en-->
The clauses conjoined at the slots the graph's binders put them in, and the three
hypotheses without which they say nothing: a table with one entry at a compound
code satisfies all twelve, so closedness and totality are not decoration.
<!--zh-->
诸子句在图的诸绑定所安置的槽位处合取起来，再加上「没有它们诸子句便什么也没说」的三条假设：一张在某个复合码处只有一个条目的表满足全部十二条，故封闭性与全性不是装饰。
<!--/-->

```agda
private
  Ci Ti Bi yi xi : Fin 5
  Ci = suc (suc zero)
  Ti = suc zero
  Bi = zero
  yi = suc (suc (suc zero))
  xi = suc (suc (suc (suc zero)))

twelveAt : Formula S 5
twelveAt =
  memClauseAt Ci Ti Bi ∧̇ (eqClauseAt Ci Ti Bi
  ∧̇ (andClauseAt Ci Ti ∧̇ (orClauseAt Ci Ti
  ∧̇ (impClauseAt Ci Ti Bi ∧̇ (negClauseAt Ci Ti Bi
  ∧̇ (topClauseAt Ci Ti Bi ∧̇ (botClauseAt Ci Ti
  ∧̇ (existClauseAt Ci Ti Bi ∧̇ (forallClauseAt Ci Ti Bi
  ∧̇ (allInClauseAt Ci Ti Bi ∧̇ exInClauseAt Ci Ti Bi))))))))))

satGraph : S → Formula S 2
satGraph B =
  ∃̇ (∃̇ (∃̇ ( (var Bi ≐ con B)
          ∧̇ ( closedAt Ci
          ∧̇ ( domAt Ti Ci
          ∧̇ ( appAt Ti xi yi
          ∧̇ twelveAt ))))))
```

<!--en-->
## What a witness is
<!--zh-->
## 一个见证是什么
<!--/-->

<!--en-->
Three nested existentials, read flat. The reading is stated at variable
arguments, which is what keeps a proof that supplies or consumes a witness from
substituting under three binders at concrete sets.
<!--zh-->
三层嵌套的存在，被摊平来读。这条读法陈述在变元自变量上，而正是它使「递出或消费一个见证」的证明不必在具体集合上钻过三层绑定作代换。
<!--/-->

```agda
GraphWit : (B x y : S) → Type (ℓ-suc ℓ)
GraphWit B x y = Σ[ C ∈ S ] (Σ[ T ∈ S ] (Σ[ b ∈ S ]
  ((fst b ≡ fst B)
   × (⟨ (b ∷ T ∷ C ∷ y ∷ x ∷ []) ⊨ closedAt Ci ⟩
      × (⟨ (b ∷ T ∷ C ∷ y ∷ x ∷ []) ⊨ domAt Ti Ci ⟩
         × (⟨ pr (fst x) (fst y) ∈ fst T ⟩
            × ⟨ (b ∷ T ∷ C ∷ y ∷ x ∷ []) ⊨ twelveAt ⟩))))))

graph-in : (B x y : S) → ∥ GraphWit B x y ∥₁ → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩
graph-in B x y = PT.map
  (λ { (C , (T , (b , (eb , (hc , (hd , (ha , h12))))))) → C
     , ∣ T , ∣ b , (eb , (hc , (hd
       , ( subst ⟨_⟩ (sym (appAt-adequate Ti xi yi (b ∷ T ∷ C ∷ y ∷ x ∷ []))) ha
         , h12 )))) ∣₁ ∣₁ })

graph-out : (B x y : S) → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩ → ∥ GraphWit B x y ∥₁
graph-out B x y = PT.rec squash₁
  (λ { (C , hT) → PT.rec squash₁
    (λ { (T , hb) → PT.map
      (λ { (b , (eb , (hc , (hd , (ha , h12))))) → C , (T , (b , (eb , (hc , (hd
         , ( subst ⟨_⟩ (appAt-adequate Ti xi yi (b ∷ T ∷ C ∷ y ∷ x ∷ [])) ha
           , h12 )))))) })
      hb })
    hT })
```
