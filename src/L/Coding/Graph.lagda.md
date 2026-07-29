# The graph

<!--en-->
What the recursion's graph says: there is an index set holding the subcodes of
its members, a table answering at every index and satisfying the twelve clauses,
and the value is what that table records at this index.

The index set and the table are bound because a graph may not name a table it has
not been given, which is the one thing the internalization theorem forbids: the
recursion is what produces the table, so the graph that defines it must quantify
over tables rather than point at one.

The carrier is bound for a different reason, and that reason is why the chapter
is one frame with two instances. Every clause takes the carrier as a slot and
none takes it as a term, so something has to occupy that slot, and what may
occupy it depends on the caller. A caller holding the carrier as a set of its own
pins a bound variable to a constant. A caller whose carrier is itself a bound
variable, which is exactly what a stage of the internal hierarchy is, has no
constant to pin it to, because a set enters a formula only by being named. So the
pinning clause is the frame's parameter, and the two instances are the two
clauses that fit it.
<!--zh-->
递归的那个图说的是：存在一个含有其成员诸子码的索引集、一张在每个索引处作答且满足十二条子句的表，而那个取值就是该表在此索引处记录的东西。

索引集与表被绑定，是因为**一个图不可以点名一张尚未交给它的表**，而那是内化定理唯一禁止的事：递归才是产出那张表的东西，故定义它的那个图必须对诸表作量化，而不能指着某一张。

载体被绑定则出于另一个理由，而正是那个理由使本章成为「一个框架带两个实例」。每条子句都把载体当作一个槽位、没有一条把它当作词项，故必须有什么东西占住那一位，而什么占得住取决于调用方。手里把载体握作自己一个集合的调用方，用一个常元钉住一个被绑定的变元。而载体本身就是一个被绑定变元的调用方 (内部层级的一个阶段正是如此) 没有可供钉住的常元，因为集合进入公式的唯一方式是被点名。于是那条用来钉住的子句就是框架的参数，而两个实例就是能填进它的那两条子句。
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
The clauses take their three slots as arguments, and conjoining them is the whole
of this section. The three hypotheses without which they say nothing come with
them: a table with one entry at a compound code satisfies all twelve, so
closedness and totality are not decoration.

The frame binds the index set, the table and the carrier, in that order, and
opens with whatever clause pins the last of them. Nothing below the pin varies
between the instances: the same three guards and the same twelve, at the same
three slots, with the two free slots shifted past the three binders.
<!--zh-->
诸子句把自己那三个槽位取作实参，而把它们合取起来就是本节的全部。「没有它们诸子句便什么也没说」的那三条假设随之而来：一张在某个复合码处只有一个条目的表满足全部十二条，故封闭性与全性不是装饰。

那个框架依次绑定索引集、表与载体，并以「钉住其中最后一个」的那条子句开头。在那条钉住之下，两个实例之间没有任何东西改变：同样三条守卫、同样十二条、落在同样三个槽位上，而那两个自由槽位越过那三个绑定作平移。
<!--/-->

```agda
private
  Ci Ti Bi : ∀ {n} → Fin (suc (suc (suc n)))
  Ci = suc (suc zero)
  Ti = suc zero
  Bi = zero

  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

twelveAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
twelveAt C T B =
  memClauseAt C T B ∧̇ (eqClauseAt C T B
  ∧̇ (andClauseAt C T ∧̇ (orClauseAt C T
  ∧̇ (impClauseAt C T B ∧̇ (negClauseAt C T B
  ∧̇ (topClauseAt C T B ∧̇ (botClauseAt C T
  ∧̇ (existClauseAt C T B ∧̇ (forallClauseAt C T B
  ∧̇ (allInClauseAt C T B ∧̇ exInClauseAt C T B))))))))))

private
  satGraphOn : ∀ {n} → Formula S (suc (suc (suc n)))
             → Fin n → Fin n → Formula S n
  satGraphOn pin x y =
    ∃̇ (∃̇ (∃̇ ( pin
            ∧̇ ( closedAt Ci
            ∧̇ ( domAt Ti Ci
            ∧̇ ( appAt Ti (sh3 x) (sh3 y)
            ∧̇ twelveAt Ci Ti Bi ))))))
```

<!--en-->
## What a witness is
<!--zh-->
## 一个见证是什么
<!--/-->

<!--en-->
Three nested existentials, read flat, at a variable environment and at a carrier
handed over as an element. The reading is stated at variable arguments, which is
what keeps a proof that supplies or consumes a witness from substituting under
three binders at concrete sets, and the environment is a variable for the same
reason: a consumer that wants the carrier as a slot has no concrete environment
to offer.

The pin is the one component the frame cannot read by itself, so it takes that
reading as a hypothesis, one direction per reading. At both instances the
hypothesis is the identity, because a variable equated to a constant and a
variable equated to a variable read as the same equation between underlying sets.
<!--zh-->
三层嵌套的存在，被摊平来读，落在一个变元环境上、也落在一个以元素形式递交的载体上。这条读法陈述在变元自变量上，而正是它使「递出或消费一个见证」的证明不必在具体集合上钻过三层绑定作代换；环境取作变元也出于同一理由：想把载体取作槽位的消费方，拿不出任何具体环境。

那条用来钉住的子句，是框架自己读不了的唯一一个分量，故它把那条读法取作假设，一个读法一个方向。在两个实例处那条假设都是恒等的，因为「变元等于常元」与「变元等于变元」读出来是底集之间的同一条等式。
<!--/-->

```agda
private
  GraphWitOn : ∀ {n} → S → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
  GraphWitOn W x y γ = Σ[ C ∈ S ] (Σ[ T ∈ S ] (Σ[ b ∈ S ]
    ((fst b ≡ fst W)
     × (⟨ (b ∷ T ∷ C ∷ γ) ⊨ closedAt Ci ⟩
        × (⟨ (b ∷ T ∷ C ∷ γ) ⊨ domAt Ti Ci ⟩
           × (⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst T ⟩
              × ⟨ (b ∷ T ∷ C ∷ γ) ⊨ twelveAt Ci Ti Bi ⟩))))))

  module _ {n : ℕ} (pin : Formula S (suc (suc (suc n)))) (W : S)
           (x y : Fin n) (γ : S ^ n) where

    graphOn-in : ((b T C : S) → fst b ≡ fst W → ⟨ (b ∷ T ∷ C ∷ γ) ⊨ pin ⟩)
               → ∥ GraphWitOn W x y γ ∥₁ → ⟨ γ ⊨ satGraphOn pin x y ⟩
    graphOn-in rd = PT.map
      (λ { (C , (T , (b , (eb , (hc , (hd , (ha , h12))))))) → C
         , ∣ T , ∣ b , (rd b T C eb , (hc , (hd
           , ( subst ⟨_⟩
                 (sym (appAt-adequate Ti (sh3 x) (sh3 y) (b ∷ T ∷ C ∷ γ))) ha
             , h12 )))) ∣₁ ∣₁ })

    graphOn-out : ((b T C : S) → ⟨ (b ∷ T ∷ C ∷ γ) ⊨ pin ⟩ → fst b ≡ fst W)
                → ⟨ γ ⊨ satGraphOn pin x y ⟩ → ∥ GraphWitOn W x y γ ∥₁
    graphOn-out rd = PT.rec squash₁
      (λ { (C , hT) → PT.rec squash₁
        (λ { (T , hb) → PT.map
          (λ { (b , (eb , (hc , (hd , (ha , h12))))) →
            C , (T , (b , (rd b T C eb , (hc , (hd
              , ( subst ⟨_⟩
                    (appAt-adequate Ti (sh3 x) (sh3 y) (b ∷ T ∷ C ∷ γ)) ha
                , h12 )))))) })
          hb })
        hT })
```

<!--en-->
## The carrier as a slot
<!--zh-->
## 载体取作槽位
<!--/-->

<!--en-->
The general instance, and the one the internal hierarchy will use. The pin
equates the graph's own bound carrier to whatever the ambient environment holds
at the given slot, and the witness says which set that is by looking the slot up.
Nothing here is a set the formula names, so a caller may put the graph under as
many binders as it likes.
<!--zh-->
一般的那个实例，也是内部层级将要用的那一个。那条钉住的子句，把图自己绑定的载体等同于周遭环境在给定槽位处所持有的东西，而那个见证靠查那一位说出那是哪个集合。此处没有任何东西是公式点了名的集合，故调用方爱把这个图放在多少层绑定之下都可以。
<!--/-->

```agda
satGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
satGraphAt B x y = satGraphOn (var Bi ≐ var (sh3 B)) x y

GraphWitAt : ∀ {n} → Fin n → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
GraphWitAt B x y γ = GraphWitOn (lookup B γ) x y γ

graphAt-in : ∀ {n} (B x y : Fin n) (γ : S ^ n)
           → ∥ GraphWitAt B x y γ ∥₁ → ⟨ γ ⊨ satGraphAt B x y ⟩
graphAt-in B x y γ =
  graphOn-in (var Bi ≐ var (sh3 B)) (lookup B γ) x y γ (λ _ _ _ e → e)

graphAt-out : ∀ {n} (B x y : Fin n) (γ : S ^ n)
            → ⟨ γ ⊨ satGraphAt B x y ⟩ → ∥ GraphWitAt B x y γ ∥₁
graphAt-out B x y γ =
  graphOn-out (var Bi ≐ var (sh3 B)) (lookup B γ) x y γ (λ _ _ _ h → h)
```

<!--en-->
## The carrier as a constant
<!--zh-->
## 载体取作常元
<!--/-->

<!--en-->
The same frame with the constant in place of the slot, at two free variables, and
this is the form the per-formula recursion and the recursion over a stage's codes
both consume. It is delivered at the types it had before the frame existed, and
its witness type is the same tuple in the same order at the same environment, so
nothing that builds or reads one has anything to notice.
<!--zh-->
同一个框架，只是把常元放到槽位的位置上，落在两个自由变元上；而这正是「按公式索引的那场递归」与「跑在某阶段诸码上的那场递归」共同消费的形式。它按框架尚未存在时的那些类型交付，其见证类型是同一个环境处、同样顺序的同一个元组，故凡是造它或读它的东西，都没有什么要留意的。
<!--/-->

```agda
satGraph : S → Formula S 2
satGraph B = satGraphOn (var Bi ≐ con B) (suc zero) zero

GraphWit : (B x y : S) → Type (ℓ-suc ℓ)
GraphWit B x y = GraphWitOn B (suc zero) zero (y ∷ x ∷ [])

graph-in : (B x y : S) → ∥ GraphWit B x y ∥₁ → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩
graph-in B x y =
  graphOn-in (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ e → e)

graph-out : (B x y : S) → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩ → ∥ GraphWit B x y ∥₁
graph-out B x y =
  graphOn-out (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ h → h)
```
