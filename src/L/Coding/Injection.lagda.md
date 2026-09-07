<!--en-->
# Coded injections
<!--zh-->
# 编码单射
<!--ja-->
# 符号化された単射
<!--/-->

<!--en-->
Later cardinal arguments move repeatedly between two representations of an
injection: a graph that a formula can quantify over, and an actual function on
the small member types of sets. This chapter supplies that bridge. It assumes
the coding vocabulary for application, single-valuedness and domains, then adds
the missing injectivity formula and proves both readback layers used by the
Cantor-Bernstein and GCH constructions.
<!--zh-->
后续基数论证反复在单射的两种表示之间往返：一种是公式能够量化的图，另一种是集合的小成员类型之间的实际函数。本章连接这两种表示。它以应用、单值性与定义域的编码词汇为先修，再补上单射性公式，并证明 Cantor-Bernstein 与 GCH 构造所需的两层读回。
<!--ja-->
後の基数論では、対象言語が量化できるグラフと、集合の小さな要素型の間の実際の単射を往復する。本章は、適用、一価性、定義域のコード化に単射性の論理式を加え、Cantor-Bernstein の定理と GCH の議論が使う二段階の読み戻しを証明する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Injection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _≐_; _⇒̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; svAt; svAt-out; domAt; domAt-in )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Injectivity in the object language
<!--zh-->
## 对象语言中的单射性
<!--ja-->
## 対象言語における単射性
<!--/-->

<!--en-->
An injective graph, in the object language: the second component
determines the first.  The mirror of `svAt`.
<!--zh-->
对象语言中的单射图要求第二分量决定第一分量。这正是 `svAt`{.Agda} 的镜像：单值性固定输入后比较输出，而这里固定输出后比较输入。
<!--ja-->
対象言語でグラフが単射であるとは、第二成分が第一成分を決定することである。これは `svAt`{.Agda} の鏡像であり、一価性が同じ入力に対する出力を比較するのに対して、ここでは同じ出力に対する入力を比較する。
<!--/-->

```agda
injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))

module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds₀ : S → S → Type (ℓ-suc ℓ)
    Holds₀ x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at₁ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc zero) (suc (suc zero)))
        ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at₁ y x x' = appAt-adequate (suc (suc (suc f))) (suc zero) (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

    at₂ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) zero (suc (suc zero)))
        ≡ (pr (fst x') (fst y) ∈ fst (lookup f γ))
    at₂ y x x' = appAt-adequate (suc (suc (suc f))) zero (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

  injAt-out : ⟨ γ ⊨ injAt f ⟩
            → (y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x'
  injAt-out h y x x' p q = h y x x'
    (subst ⟨_⟩ (sym (at₁ y x x')) p) (subst ⟨_⟩ (sym (at₂ y x x')) q)

  injAt-in : ((y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x')
           → ⟨ γ ⊨ injAt f ⟩
  injAt-in h y x x' p q = h y x x'
    (subst ⟨_⟩ (at₁ y x x') p) (subst ⟨_⟩ (at₂ y x x') q)
```

<!--en-->
## Extracting an injection into the model
<!--zh-->
## 提取一个取值于模型的单射
<!--ja-->
## モデルに値を取る単射を取り出す
<!--/-->

<!--en-->
The readback, first half: from a member of the domain to its unique image
under the graph, with injectivity. `Extract` keeps values as elements of `L`;
this is the form used when later proofs still reason about the coded graph.
<!--zh-->
读回的第一层从定义域的一个成员取得它在图下的唯一像，并保留单射性。`Extract`{.Agda} 仍把取值保留为 `L` 的元素；后续证明仍需对编码图作推理时，使用的就是这种形式。
<!--ja-->
第一の読み戻しは、定義域の各要素からグラフ上の一意な像を選び、その写像が単射であることを示す。`Extract`{.Agda} は値を L の要素のまま保つので、後の証明がコード化されたグラフを引き続き参照するときに使える。
<!--/-->

```agda
module Extract (F D : S)
               (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
               (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

  γ : S ^ 2
  γ = F ∷ D ∷ []

  Holds : S → S → Type (ℓ-suc ℓ)
  Holds x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩

  Fib : S → Type (ℓ-suc ℓ)
  Fib x = Σ[ y ∈ S ] Holds x y

  isPropFib : (x : S) → isProp (Fib x)
  isPropFib x (y , p) (y' , q) =
    Σ≡Prop (λ w → snd (pr (fst x) (fst w) ∈ fst F))
      (Σ≡Prop (λ z → snd (isL z)) (svAt-out zero γ sv x y y' p q))

  toVal : (x : S) → ∥ Fib x ∥₁ → Fib x
  toVal x = PT.rec (isPropFib x) (λ z → z)

  Dom : Type (ℓ-suc ℓ)
  Dom = Σ[ x ∈ S ] ⟨ fst x ∈ fst D ⟩

  fib : (u : Dom) → Fib (fst u)
  fib (x , m) = toVal x (domAt-in zero (suc zero) γ dm x m)

  toFun : Dom → S
  toFun u = fst (fib u)

  toFun-graph : (u : Dom) → Holds (fst u) (toFun u)
  toFun-graph u = snd (fib u)

  module _ (ij : ⟨ γ ⊨ injAt zero ⟩) where

    toFun-inj : (u v : Dom) → fst (toFun u) ≡ fst (toFun v)
              → fst (fst u) ≡ fst (fst v)
    toFun-inj u v e = injAt-out zero γ ij (toFun v) (fst u) (fst v)
      (subst (λ w → ⟨ pr (fst (fst u)) w ∈ fst F ⟩) e (toFun-graph u))
      (toFun-graph v)
```

<!--en-->
## Restricting to the small carriers
<!--zh-->
## 限制到小载体
<!--ja-->
## 小さな台に制限する
<!--/-->

<!--en-->
The readback, second half: the honest injection between the small index
types, with the range supplied rather than assumed. This is the form consumed
by the generic Cantor-Bernstein interface and by the counting arguments in GCH.
<!--zh-->
读回的第二层给出小索引类型之间的实际单射，其值域由调用者供应而非预先假定。泛型 Cantor-Bernstein 接口与 GCH 的计数论证使用的就是这种形式。
<!--ja-->
第二の読み戻しは、L の要素として得た値を指定された値域の小さな台へ移し、二つの小さな添字型の間の単射を得る。この形を一般の Cantor-Bernstein インターフェースと GCH の濃度計算が直接使う。
<!--/-->

```agda
module Small (F D C : S)
             (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
             (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
             (ij : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
             (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst C ⟩) where

  module E = Extract F D sv dm

  toS : ⟪ fst D ⟫ → S
  toS m = ⟪ fst D ⟫↪ m
        , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

  at : ⟪ fst D ⟫ → E.Dom
  at m = toS m , member (fst D) m

  fib : (m : ⟪ fst D ⟫)
      → Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst (E.toFun (at m)))
  fib m = fiber (fst C)
    (ran (toS m) (E.toFun (at m)) (E.toFun-graph (at m)))

  small : ⟪ fst D ⟫ → ⟪ fst C ⟫
  small m = fst (fib m)

  small-inj : (m n : ⟪ fst D ⟫) → small m ≡ small n → m ≡ n
  small-inj m n e = ↪-inj {a = fst D} {m = m} {n = n}
    (E.toFun-inj ij (at m) (at n)
      (sym (snd (fib m)) ∙ cong ⟪ fst C ⟫↪ e ∙ snd (fib n)))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
`injAt`{.Agda} expresses injectivity of a coded graph inside the model.
`Extract.toFun`{.Agda} reads that graph as an injection whose values remain in
`L`, and `Small.small`{.Agda} transfers it to an injection between the small
member types of its stated domain and range.
<!--zh-->
`injAt`{.Agda} 在模型内部表达编码图的单射性。`Extract.toFun`{.Agda} 把该图读成一个取值仍在 `L` 中的单射，而 `Small.small`{.Agda} 再把它转成其指定定义域与值域的小成员类型之间的单射。
<!--ja-->
`injAt`{.Agda} はコード化されたグラフの単射性をモデル内部で表す。`Extract.toFun`{.Agda} はそのグラフを L に値を取る単射として読み、`Small.small`{.Agda} は指定された定義域と値域の小さな要素型の間の単射へ移す。
<!--/-->
