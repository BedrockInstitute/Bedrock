<!--en-->
# The satisfaction graph formula
<!--zh-->
# 满足关系图公式
<!--ja-->
# 充足関係のグラフを表す論理式
<!--/-->

<!--en-->
This chapter defines a first-order graph formula whose witnesses are a code set closed under subformulas and a total satisfaction table satisfying all ten recursive clauses. It provides versions in which the carrier is supplied by a variable or fixed as a constant.
<!--zh-->
本章定义一个一阶图公式，其见证是对子公式封闭的编码集，以及满足全部十条递归子句的全满足关系表。本章分别给出由变元提供载体和把载体固定为常元的版本。
<!--ja-->
本章では、部分式について閉じたコード集合と、十個の再帰条件をすべて満たす全域的な充足関係表を証人とする一階のグラフ論理式を定義します。台を変数で与える版と定数に固定する版の両方を用意します。
<!--/-->

<!--en-->
What the recursion's graph says: there is an index set holding the subcodes of
its members, a table answering at every index and satisfying the ten clauses,
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
递归的那个图说的是：存在一个含有其成员诸子码的索引集、一张在每个索引处作答且满足十条子句的表，而那个取值就是该表在此索引处记录的东西。

索引集与表被绑定，是因为**一个图不可以点名一张尚未交给它的表**，而那是内化定理唯一禁止的事：递归才是产出那张表的东西，故定义它的那个图必须对诸表作量化，而不能指着某一张。

载体被绑定则出于另一个理由，而正是那个理由使本章成为「一个框架带两个实例」。每条子句都把载体当作一个槽位、没有一条把它当作词项，故必须有什么东西占住那一位，而什么占得住取决于调用方。手里把载体握作自己一个集合的调用方，用一个常元钉住一个被绑定的变元。而载体本身就是一个被绑定变元的调用方 (内部层级的一个阶段正是如此) 没有可供钉住的常元，因为集合进入公式的唯一方式是被点名。于是那条用来钉住的子句就是框架的参数，而两个实例就是能填进它的那两条子句。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.SatisfactionGraph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( domAt; appAt; appAt-adequate )
open import L.Coding.Closure {ℓ} using ( closedAt )
open import L.Coding.Quantification {ℓ} using
  ( f0; f1; f2; f3; f4; f5; f6; f7; f8; f9; i0; i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; sh )
open import L.Coding.EnvironmentTower {ℓ} lem using ( nn; towerAt )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
open import L.Coding.SatisfactionClauses {ℓ} using ( tableAt )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Vec using ( _∷_; []; lookup )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The guarded recursion frame
<!--zh-->
## 带守卫的递归框架
<!--ja-->
## 再帰条件を守る枠組み
<!--/-->

<!--en-->
`satGraphOn` binds a carrier, code set, and table, then requires the code set to be closed, the table to be total on it, and every table value to share the stated domain. Under these three guards it conjoins the ten constructor clauses.
<!--zh-->
`satGraphOn` 依次绑定载体、编码集与满足关系表，再要求编码集封闭、表在其上为全的，并且表中每个值具有指定定义域。在这三条守卫之下，它合取十条构造子子句。
<!--ja-->
`satGraphOn` は台、コード集合、充足関係表を束縛し、コード集合の閉包性、表の全域性、各表値が指定された定義域をもつことを要求します。この三条件の下で十個の構成子条件を連言します。
<!--/-->

<!--en-->
The clauses take their three slots as arguments, and conjoining them is the whole
of this section. The three hypotheses without which they say nothing come with
them: a table with one entry at a compound code satisfies all ten, so
closedness and totality are not decoration.

The frame binds the index set, the table and the carrier, in that order, and
opens with whatever clause pins the last of them. Nothing below the pin varies
between the instances: the same three guards and the same ten, at the same
three slots, with the two free slots shifted past the three binders.
<!--zh-->
诸子句把自己那三个槽位取作实参，而把它们合取起来就是本节的全部。「没有它们诸子句便什么也没说」的那三条假设随之而来：一张在某个复合码处只有一个条目的表满足全部十条，故封闭性与全性不是装饰。

那个框架依次绑定索引集、表与载体，并以「钉住其中最后一个」的那条子句开头。在那条钉住之下，两个实例之间没有任何东西改变：同样三条守卫、同样十条、落在同样三个槽位上，而那两个自由槽位越过那三个绑定作平移。
<!--/-->

The frame. Fourteen bound sets: the ten numeral slots the Δ₀ clauses index
their tags by, the tower, the index set, the table and the carrier, innermost
last. The numerals are pinned to constants, which costs nothing under a binder
because a numeral is the same set wherever it is named; the tower is pinned by
its own Δ₀ description, which is why no caller has to hold a slot for it.

```agda
Bi Ti Ci Ei : ∀ {n} → Fin (14 + n)
Bi = i0
Ti = i1
Ci = i2
Ei = i3
```

The tag slots, innermost first: `N 0` at `i4` up to `N 9` at `i13`.

```agda
NN : ∀ {n} → Fin 10 → Fin (14 + n)
NN zero = i4
NN (suc zero) = i5
NN (suc (suc zero)) = i6
NN (suc (suc (suc zero))) = i7
NN (suc (suc (suc (suc zero)))) = i8
NN (suc (suc (suc (suc (suc zero))))) = i9
NN (suc (suc (suc (suc (suc (suc zero)))))) = i10
NN (suc (suc (suc (suc (suc (suc (suc zero))))))) = i11
NN (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = i12
NN (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = i13

sh14 : ∀ {n} → Fin n → Fin (14 + n)
sh14 i = sh 14 i
```

The frame environment of a witness.

```agda
ev : ∀ {n} → (Fin 10 → S) → S → S → S → S → S ^ n → S ^ (14 + n)
ev ν E C T b γ =
  b ∷ T ∷ C ∷ E ∷ ν f0 ∷ ν f1 ∷ ν f2 ∷ ν f3 ∷ ν f4 ∷ ν f5
    ∷ ν f6 ∷ ν f7 ∷ ν f8 ∷ ν f9 ∷ γ
```

The ten numerals themselves, and the tags they satisfy.

```agda
numν : Fin 10 → S
numν k = nn (toℕ k)

numTags : ∀ {n} (E C T b : S) (γ : S ^ n) → Tags (ev numν E C T b γ) NN
numTags E C T b γ zero = refl
numTags E C T b γ (suc zero) = refl
numTags E C T b γ (suc (suc zero)) = refl
numTags E C T b γ (suc (suc (suc zero))) = refl
numTags E C T b γ (suc (suc (suc (suc zero)))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc zero))))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc (suc zero)))))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
numTags E C T b γ (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl
```

The ten tags, pinned to the numerals they name.

```agda
numsAt : ∀ {n} → Formula S (14 + n)
numsAt =
  (var i4 ≐ con (nn 0)) ∧̇ ((var i5 ≐ con (nn 1)) ∧̇ ((var i6 ≐ con (nn 2)) ∧̇
  ((var i7 ≐ con (nn 3)) ∧̇ ((var i8 ≐ con (nn 4)) ∧̇ ((var i9 ≐ con (nn 5)) ∧̇
  ((var i10 ≐ con (nn 6)) ∧̇ ((var i11 ≐ con (nn 7)) ∧̇
  ((var i12 ≐ con (nn 8)) ∧̇ (var i13 ≐ con (nn 9))))))))))

nums-out : ∀ {n} (ν : Fin 10 → S) (E C T b : S) (γ : S ^ n)
         → ⟨ ev ν E C T b γ ⊨ numsAt ⟩ → Tags (ev ν E C T b γ) NN
nums-out ν E C T b γ h zero = h .fst
nums-out ν E C T b γ h (suc zero) = h .snd .fst
nums-out ν E C T b γ h (suc (suc zero)) = h .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc zero))) = h .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc zero)))) = h .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc zero))))) = h .snd .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc zero)))))) = h .snd .snd .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc (suc zero))))))) = h .snd .snd .snd .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = h .snd .snd .snd .snd .snd .snd .snd .snd .fst
nums-out ν E C T b γ h (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = h .snd .snd .snd .snd .snd .snd .snd .snd .snd

nums-in : ∀ {n} (ν : Fin 10 → S) (E C T b : S) (γ : S ^ n)
        → Tags (ev ν E C T b γ) NN → ⟨ ev ν E C T b γ ⊨ numsAt ⟩
nums-in ν E C T b γ tg =
    tg f0 , (tg f1 , (tg f2 , (tg f3 , (tg f4 , (tg f5
  , (tg f6 , (tg f7 , (tg f8 , tg f9))))))))

private
  satGraphOn : ∀ {n} → Formula S (14 + n)
             → Fin n → Fin n → Formula S n
  satGraphOn pin x y =
    ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (( pin
      ∧̇ ( numsAt
      ∧̇ ( towerAt Ei Bi (NN f0)
      ∧̇ ( closedAt Ci
      ∧̇ ( domAt Ti Ci
      ∧̇ ( appAt Ti (sh14 x) (sh14 y)
      ∧̇ tableAt Ti Bi Ci Ei NN ))))))))))))))))))))
```

<!--en-->
## Witnesses for the satisfaction graph
<!--zh-->
## 满足关系图的见证
<!--ja-->
## 充足関係グラフの証人
<!--/-->

<!--en-->
`GraphWitOn` records concrete choices for the bound carrier, code set, and table together with proofs of the pinning condition, the three guards, and all ten clauses. The lemmas `graphOn-in` and `graphOn-out` translate between this witness data and satisfaction of `satGraphOn`.
<!--zh-->
`GraphWitOn` 记录被绑定载体、编码集与满足关系表的具体选择，并附上固定条件、三条守卫及全部十条子句的证明。引理 `graphOn-in` 与 `graphOn-out` 在这些见证数据和满足 `satGraphOn` 之间转换。
<!--ja-->
`GraphWitOn` は束縛された台、コード集合、充足関係表の具体的な選択と、固定条件、三つの保護条件、十個の条件すべての証明を記録します。`graphOn-in` と `graphOn-out` はこの証人データと `satGraphOn` の充足を相互に移します。
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
  GraphWitOn W x y γ =
    Σ[ ν ∈ (Fin 10 → S) ] (Σ[ E ∈ S ] (Σ[ C ∈ S ] (Σ[ T ∈ S ] (Σ[ b ∈ S ] ((fst b ≡ fst W) × (Tags (ev ν E C T b γ) NN × (⟨ (ev ν E C T b γ) ⊨ towerAt Ei Bi (NN f0) ⟩ × (⟨ (ev ν E C T b γ) ⊨ closedAt Ci ⟩ × (⟨ (ev ν E C T b γ) ⊨ domAt Ti Ci ⟩ × (⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst T ⟩ × ⟨ (ev ν E C T b γ) ⊨ tableAt Ti Bi Ci Ei NN ⟩))))))))))

  module _ {n : ℕ} (pin : Formula S (14 + n)) (W : S)
           (x y : Fin n) (γ : S ^ n) where

    graphOn-in : ((ν : Fin 10 → S) (E C T b : S) → fst b ≡ fst W
                   → ⟨ ev ν E C T b γ ⊨ pin ⟩)
               → ∥ GraphWitOn W x y γ ∥₁ → ⟨ γ ⊨ satGraphOn pin x y ⟩
    graphOn-in rd = PT.map
      (λ { (ν , (E , (C , (T , (b , (eb , (tg , (hE , (hc , (hd , (ha , h12))))))))))) →
          ν f9
        , ∣ ν f8 , ∣ ν f7 , ∣ ν f6 , ∣ ν f5 , ∣ ν f4
        , ∣ ν f3 , ∣ ν f2 , ∣ ν f1 , ∣ ν f0 , ∣ E , ∣ C , ∣ T , ∣ b
        , ( rd ν E C T b eb
          , ( nums-in ν E C T b γ tg
          , ( hE
          , ( hc
          , ( hd
          , ( subst ⟨_⟩
                (sym (appAt-adequate Ti (sh14 x) (sh14 y) (ev ν E C T b γ))) ha
            , h12 ))))))
          ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ })

    graphOn-out : ((ν : Fin 10 → S) (E C T b : S)
                    → ⟨ ev ν E C T b γ ⊨ pin ⟩ → fst b ≡ fst W)
                → ⟨ γ ⊨ satGraphOn pin x y ⟩ → ∥ GraphWitOn W x y γ ∥₁
    graphOn-out rd h = PT.rec squash₁ (λ { (n9 , h9) →
      PT.rec squash₁ (λ { (n8 , h8) →
      PT.rec squash₁ (λ { (n7 , h7) →
      PT.rec squash₁ (λ { (n6 , h6) →
      PT.rec squash₁ (λ { (n5 , h5) →
      PT.rec squash₁ (λ { (n4 , h4) →
      PT.rec squash₁ (λ { (n3 , h3) →
      PT.rec squash₁ (λ { (n2 , h2) →
      PT.rec squash₁ (λ { (n1 , h1) →
      PT.rec squash₁ (λ { (n0 , h0) →
      PT.rec squash₁ (λ { (E , hE') →
      PT.rec squash₁ (λ { (C , hC') →
      PT.rec squash₁ (λ { (T , hT') →
      PT.map (λ { (b , (hpin , (hnum , (hE , (hc , (hd , (ha , h12))))))) →
        let ν : Fin 10 → S
            ν = ν' n0 n1 n2 n3 n4 n5 n6 n7 n8 n9
        in ν , (E , (C , (T , (b , (rd ν E C T b hpin
           , ( nums-out ν E C T b γ hnum
           , ( hE
           , ( hc
           , ( hd
           , ( subst ⟨_⟩
                 (appAt-adequate Ti (sh14 x) (sh14 y) (ev ν E C T b γ)) ha
             , h12 )))))))))) })
        hT' }) hC' }) hE' }) h0 }) h1 }) h2 }) h3 }) h4 }) h5 }) h6 })
        h7 }) h8 }) h9 }) h
      where
      ν' : S → S → S → S → S → S → S → S → S → S → Fin 10 → S
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 zero = a0
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc zero) = a1
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc zero)) = a2
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc zero))) = a3
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc zero)))) = a4
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc zero))))) = a5
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc zero)))))) = a6
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = a7
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = a8
      ν' a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = a9
```

<!--en-->
## The carrier supplied by a variable
<!--zh-->
## 由变元提供载体
<!--ja-->
## 変数で与える台
<!--/-->

<!--en-->
`satGraphAt B x y` instantiates the frame by equating its bound carrier with the value at slot `B`. Its witness type `GraphWitAt` and the two conversion lemmas expose exactly the graph relation between the values at `x` and `y` over that variable carrier.
<!--zh-->
`satGraphAt B x y` 通过把被绑定载体等同于槽位 `B` 处的值来实例化框架。见证类型 `GraphWitAt` 及两条转换引理精确揭示在该变元载体上，`x` 与 `y` 处取值之间的图关系。
<!--ja-->
`satGraphAt B x y` は、束縛された台をスロット `B` の値と等置して枠組みを具体化します。証人型 `GraphWitAt` と二つの変換補題は、その変数の台上で `x` と `y` の値の間に成り立つグラフ関係を正確に示します。
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
GraphWitAt : ∀ {n} → Fin n → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
GraphWitAt B x y γ = GraphWitOn (lookup B γ) x y γ
```

Sealed (P-t), and the reason is a measurement rather than a preference. This
formula is a conjunct of three larger ones, and every consumer of those splits
them. A split REDUCES the conjunct's type while the consumer's own signature
names it FOLDED, so the conversion checker walks the whole tree to see that the
two agree. Open, that one coercion cost 2,459 ms at the site this seal serves;
sealed, both sides are the same stuck head and the check is syntactic. The two
readers below are the official unfolding, so no consumer needs `unfolding` to
build or read a witness.

```agda
opaque
  satGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  satGraphAt B x y = satGraphOn (var Bi ≐ var (sh14 B)) x y

opaque
  unfolding satGraphAt

  graphAt-in : ∀ {n} (B x y : Fin n) (γ : S ^ n)
             → ∥ GraphWitAt B x y γ ∥₁ → ⟨ γ ⊨ satGraphAt B x y ⟩
  graphAt-in B x y γ =
    graphOn-in (var Bi ≐ var (sh14 B)) (lookup B γ) x y γ (λ _ _ _ _ _ e → e)

  graphAt-out : ∀ {n} (B x y : Fin n) (γ : S ^ n)
              → ⟨ γ ⊨ satGraphAt B x y ⟩ → ∥ GraphWitAt B x y γ ∥₁
  graphAt-out B x y γ =
    graphOn-out (var Bi ≐ var (sh14 B)) (lookup B γ) x y γ (λ _ _ _ _ _ h → h)
```

<!--en-->
## The carrier fixed as a constant
<!--zh-->
## 把载体固定为常元
<!--ja-->
## 台を定数に固定する
<!--/-->

<!--en-->
`satGraph B` instead pins the bound carrier to the constant `B`. The type `GraphWit B x y` and the lemmas `graph-in` and `graph-out` characterize this formula when a surrounding construction already has a fixed carrier.
<!--zh-->
`satGraph B` 则把被绑定载体固定为常元 `B`。当外围构造已有固定载体时，类型 `GraphWit B x y` 以及引理 `graph-in`、`graph-out` 刻画这一公式。
<!--ja-->
一方 `satGraph B` は束縛された台を定数 `B` に固定します。周囲の構成がすでに固定された台をもつ場合について、型 `GraphWit B x y` と補題 `graph-in`、`graph-out` がこの論理式を特徴づけます。
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
opaque
  satGraph : S → Formula S 2
  satGraph B = satGraphOn (var Bi ≐ con B) (suc zero) zero

GraphWit : (B x y : S) → Type (ℓ-suc ℓ)
GraphWit B x y = GraphWitOn B (suc zero) zero (y ∷ x ∷ [])

opaque
  unfolding satGraph

  graph-in : (B x y : S) → ∥ GraphWit B x y ∥₁ → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩
  graph-in B x y =
    graphOn-in (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ _ _ e → e)

  graph-out : (B x y : S) → ⟨ (y ∷ x ∷ []) ⊨ satGraph B ⟩ → ∥ GraphWit B x y ∥₁
  graph-out B x y =
    graphOn-out (var Bi ≐ con B) B (suc zero) zero (y ∷ x ∷ []) (λ _ _ _ _ _ h → h)
```
