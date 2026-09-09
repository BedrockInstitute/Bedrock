<!--en-->
# Ordinals are linearly ordered by membership

Two ordinals are always comparable: one belongs to the other or they are equal. This chapter derives that trichotomy from transitivity and well-foundedness, then packages membership as the strict linear order used throughout the hierarchy.
<!--zh-->
# 序数由隶属关系线性排序

任意两个序数总可比较：一个属于另一个，或二者相等。本章从传递性与良基性推出这一三歧，并把隶属关系封装成层级各处使用的严格线性序。
<!--ja-->
# 順序数は所属によって線形に順序付けられる

任意の二つの順序数は比較でき、一方が他方に属するか、両者が等しい。本章では推移性と整礎性からこの三分性を導き、所属を階層全体で使う狭義線形順序としてまとめる。
<!--/-->

<!--en-->
Of any two ordinals, one belongs to the other or the two are equal. This is the
fact everyone expects from ordinals, and it is the last thing about them the
book has left to prove. It is also the first place where the constructible
universe uses classical logic, so it deserves to be said plainly why.

Everything about ordinals up to now has been closure: zero is one, successors
are, unions are, bounds exist. Closure statements build; they never have to
*decide* anything. Trichotomy decides. Given two ordinals with no relation
assumed between them, it returns which of three mutually exclusive cases holds,
and there is no construction that could produce that answer from the data: the
statement implies the excluded middle. So the chapter takes the excluded middle
as a module parameter, using the level-indexed packaging fixed in the foundations, and every later chapter
that uses it inherits the parameter visibly, at every import site.

Two ingredients from the ambient hierarchy make the proof shorter than the
textbook version. Regularity gives a well-founded induction, and it is used
twice over, once in each argument. Extensionality means that mutual inclusion
*is* equality, so the equal case needs no separate work. What the excluded
middle then supplies is exactly one thing: the decision whether one ordinal is
included in the other, and, when it is not, a member witnessing the failure.
<!--zh-->
任两个序数，或一者属于另一者，或二者相等。这是人人对序数的期待，也是本书关于它们最后要证的东西。这里同时是可构造宇宙第一次用到经典逻辑的地方，所以值得把原因说清楚。

迄今关于序数的一切都是闭包：零是序数，后继是，并也是，上界存在。闭包陈述关乎建造；它们从不需要**判定**任何东西。三歧要判定。给定两个彼此之间不假设任何关系的序数，它要回答三种互斥情形中的哪一种成立，而没有任何构造能从这些数据得出那个答案：该陈述蕴含排中律。所以本章把排中律取作模块参数，采用基础阶段定下的逐层级打包形式，而此后每个使用它的章节都在每个导入处以可见的方式继承这个参数。

来自环境层级的两样材料使证明比教科书版本更短。正则性给出良基归纳，而且要用两次，两个自变量各一次。外延性意味着互相包含**就是**相等，故相等那一情形无须另行处理。于是排中律所起的作用恰好只有一件事：判定一个序数是否包含于另一个，以及在不包含时，取出一个见证失败的成员。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.Linear {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import Cubical.Induction.WellFounded as WF

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Inclusion, and what fails it
<!--zh-->
## 包含，及其失败的见证
<!--ja-->
## 包含と、その失敗を示す証人
<!--/-->

<!--en-->
If one ordinal is not included in another, well-foundedness selects a least element witnessing the failure. Transitivity then shows that this witness contains exactly the common initial part of the two ordinals.
<!--zh-->
若一个序数不包含于另一个，良基性会选出见证这一失败的最小元素。随后由传递性可知，这个见证恰好包含两个序数共有的初始部分。
<!--ja-->
一方の順序数が他方に含まれないなら、整礎性によってその失敗を示す最小の要素を選べる。推移性から、この証人は二つの順序数に共通する最初の部分をちょうど含む。
<!--/-->

<!--en-->
Inclusion is written pointwise, and packaged as a proposition so that the
excluded middle can be applied to it directly: the carrier being
quantified over sits one universe up, which is why the foundational interface was stated levelwise.
Mutual inclusion gives equality, by the hierarchy's extensionality.
<!--zh-->
包含按元素逐点定义，并打包成命题，使排中律可以直接用于它。该定义量化的载体位于高一层宇宙，这正是基础阶段按层级陈述此接口的原因。由层级的外延性可知，互相包含蕴含相等。
<!--/-->

```agda
_⊆ᵇ_ : S → S → Type (ℓ-suc ℓ)
A ⊆ᵇ B = (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ B ⟩

⊆ᵇ-prop : (A B : S) → hProp (ℓ-suc ℓ)
⊆ᵇ-prop A B = (A ⊆ᵇ B) , isPropΠ (λ x → isPropΠ (λ _ → snd (x ∈ˢ B)))

ext-⊆ᵇ : {A B : S} → A ⊆ᵇ B → B ⊆ᵇ A → A ≡ B
ext-⊆ᵇ {A} {B} s₁ s₂ = extensionalV (λ x → ⇔toPath (s₁ x) (s₂ x))
```

<!--en-->
Here is the one genuinely classical step. From a *failure* of inclusion the
proof needs a member witnessing it, and passing from "not every member is in
`B`" to "some member is not in `B`" is not constructive. The excluded middle
decides the existence statement directly: were there no such witness, every
member would be in `B` after all, decided one member at a time.
<!--zh-->
这里是真正经典的那一步。从包含**失败**出发，证明需要一个见证它的成员，而从「并非每个成员都在 `B` 中」过渡到「某个成员不在 `B` 中」不构造。排中律直接判定那个存在陈述：若没有这样的见证，则逐个成员判定下来，每个成员终究都在 `B` 中。
<!--/-->

```agda
¬⊆ᵇ→witness : (A B : S) → (A ⊆ᵇ B → Empty.⊥)
            → ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × (⟨ a ∈ˢ B ⟩ → Empty.⊥)) ∥₁
¬⊆ᵇ→witness A B ¬sub = decide (lem Witness)
  where
  Witness : hProp (ℓ-suc ℓ)
  Witness = ∥ Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × (⟨ a ∈ˢ B ⟩ → Empty.⊥)) ∥₁
          , PT.isPropPropTrunc
  decide : ⟨ Witness ⟩ ⊎ (⟨ Witness ⟩ → Empty.⊥) → ⟨ Witness ⟩
  decide (inl wit)  = wit
  decide (inr ¬wit) = Empty.rec (¬sub sub)
    where
    sub : A ⊆ᵇ B
    sub x x∈A = at (lem (x ∈ˢ B))
      where
      at : ⟨ x ∈ˢ B ⟩ ⊎ (⟨ x ∈ˢ B ⟩ → Empty.⊥) → ⟨ x ∈ˢ B ⟩
      at (inl x∈B)  = x∈B
      at (inr ¬x∈B) = Empty.rec (¬wit ∣ x , (x∈A , ¬x∈B) ∣₁)
```

<!--en-->
## Trichotomy
<!--zh-->
## 三歧
<!--ja-->
## 順序数の三分性
<!--/-->

<!--en-->
Applying the least-witness argument in both directions leaves exactly three cases: `α ∈ β`, `α ≡ β`, or `β ∈ α`. Irreflexivity makes the cases exclusive and membership transitivity composes comparisons.
<!--zh-->
在两个方向使用最小见证论证，只留下三种情形：`α ∈ β`、`α ≡ β` 或 `β ∈ α`。非自反性使三者互斥，而隶属关系的传递性复合比较。
<!--ja-->
最小証人の議論を両方向に適用すると、`α ∈ β`、`α ≡ β`、`β ∈ α` の三つの場合だけが残る。非反射性により場合は排他的で、所属の推移性により比較を合成できる。
<!--/-->

<!--en-->
A double induction on membership, once in each argument, with the excluded
middle deciding the two inclusions at the leaves. If both hold, the ordinals are
equal. If `A` is included in `B` but not conversely, take a member `b` of `B`
outside `A`; the inner hypothesis compares `A` with `b`, and each of the three
outcomes makes `A` a member of `B`: below `b` and hence below `B` by transitivity,
equal to `b` and hence a member, or a member of `A`, which contradicts the
choice of `b`. The remaining case is the mirror image, decided by the outer
hypothesis.
<!--zh-->
沿成员关系对两个自变量各作一次归纳，在叶子处由排中律判定两个包含关系。若二者都成立，则两个序数相等。若 `A` 包含于 `B` 而反之不然，取 `B` 中一个不在 `A` 内的成员 `b`；内层归纳假设比较 `A` 与 `b`，三种结果都使 `A` 属于 `B`：若 `A` 在 `b` 之下，则由传递性可知 `A` 在 `B` 之下；若 `A` 等于 `b`，则它是 `B` 的成员；若 `b` 属于 `A`，则与 `b` 的选取矛盾。余下情形与此对称，由外层归纳假设判定。
<!--/-->

```agda
Tri : S → S → Type (ℓ-suc ℓ)
Tri A B = ⟨ A ∈ˢ B ⟩ ⊎ ((A ≡ B) ⊎ ⟨ B ∈ˢ A ⟩)

ord-tri : (A : S) → IsOrd A → (B : S) → IsOrd B → Tri A B
ord-tri = WF.WFI.induction regularityV {P = P} stepA
  where
  P : S → Type (ℓ-suc ℓ)
  P A = IsOrd A → (B : S) → IsOrd B → Tri A B

  stepA : (A : S) → (∀ A' → ⟨ A' ∈ˢ A ⟩ → P A') → P A
  stepA A IHA ordA =
    WF.WFI.induction regularityV {P = λ B → IsOrd B → Tri A B} stepB
    where
    stepB : (B : S) → (∀ B' → ⟨ B' ∈ˢ B ⟩ → IsOrd B' → Tri A B')
          → IsOrd B → Tri A B
    stepB B IHB ordB = decide (lem (⊆ᵇ-prop A B)) (lem (⊆ᵇ-prop B A))
      where
      fromB : Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × (⟨ b ∈ˢ A ⟩ → Empty.⊥)) → ⟨ A ∈ˢ B ⟩
      fromB (b , (b∈B , ¬b∈A)) = at (IHB b b∈B (mem-ord {A = B} ordB b b∈B))
        where
        at : Tri A b → ⟨ A ∈ˢ B ⟩
        at (inl A∈b)       = ordB .fst A∈b b∈B
        at (inr (inl A≡b)) = subst (λ w → ⟨ w ∈ˢ B ⟩) (sym A≡b) b∈B
        at (inr (inr b∈A)) = Empty.rec (¬b∈A b∈A)

      fromA : Σ[ a ∈ S ] (⟨ a ∈ˢ A ⟩ × (⟨ a ∈ˢ B ⟩ → Empty.⊥)) → ⟨ B ∈ˢ A ⟩
      fromA (a , (a∈A , ¬a∈B)) =
        at (IHA a a∈A (mem-ord {A = A} ordA a a∈A) B ordB)
        where
        at : Tri a B → ⟨ B ∈ˢ A ⟩
        at (inl a∈B)       = Empty.rec (¬a∈B a∈B)
        at (inr (inl a≡B)) = subst (λ w → ⟨ w ∈ˢ A ⟩) a≡B a∈A
        at (inr (inr B∈a)) = ordA .fst B∈a a∈A

      decide : (A ⊆ᵇ B) ⊎ ((A ⊆ᵇ B) → Empty.⊥)
             → (B ⊆ᵇ A) ⊎ ((B ⊆ᵇ A) → Empty.⊥) → Tri A B
      decide (inl A⊆B) (inl B⊆A) = inr (inl (ext-⊆ᵇ A⊆B B⊆A))
      decide (inl A⊆B) (inr ¬B⊆A) =
        inl (PT.rec (snd (A ∈ˢ B)) fromB (¬⊆ᵇ→witness B A ¬B⊆A))
      decide (inr ¬A⊆B) _ =
        inr (inr (PT.rec (snd (B ∈ˢ A)) fromA (¬⊆ᵇ→witness A B ¬A⊆B)))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
Ordinal membership now supplies trichotomy, irreflexivity, and transitivity. These comparison laws are the order-theoretic foundation for stage monotonicity and cardinal arguments later in the book.
<!--zh-->
序数隶属关系现在具有三歧性、非自反性与传递性。这些比较定律构成后续阶段单调性与基数论证的序论基础。
<!--ja-->
順序数の所属について、三分性、非反射性、推移性が得られた。これらの比較法則は、後の段階の単調性と基数の議論に必要な順序論的基礎となる。
<!--/-->

<!--en-->
`ord-tri`{.Agda} compares any two ordinals, and the book supplies one
instance of the excluded middle for it, taken as a module parameter and therefore
visible in the type of every chapter downstream. This is the boundary the
groundwork was built to make auditable: nothing is postulated, and a reader can
tell whether a theorem is classical by reading its imports. The next chapter
uses the comparison on the question it was needed for, which ordinals appear
at which stage of the tower.
<!--zh-->
`ord-tri`{.Agda} 比较任意两个序数，而本书为它提供一份排中律实例，取作模块参数，因而在下游每一章的类型中可见。这正是奠基部分为使其可审计而搭建的那道边界：无一处 postulate，读者读导入即可判断一条定理是否经典。下一章把这个比较用在它被需要的那个问题上：哪些序数出现在塔的哪个阶段。
<!--/-->
