<!--en-->
# Closure under subformulas
<!--zh-->
# 对子公式封闭
<!--ja-->
# 部分式についての閉包
<!--/-->

<!--en-->
A recursion over formula codes needs an index set containing the immediate
subformula keys required by each constructor. This chapter proves the seven
object-language closure conditions first for any set with the `Peel` property,
then for the actual subformula closure of a formula.
<!--zh-->
公式编码上的递归需要一个索引集，其中包含每个构造子所要求的直接子公式键。本章先对任意具有 `Peel` 性质的集合证明七条对象语言闭包条件，再把结果用于公式的实际子公式闭包。
<!--ja-->
論理式コード上の再帰には、各構成子が要求する直接の部分式の鍵を含む添字集合が必要です。本章では、まず `Peel` 性をもつ任意の集合について対象言語の七つの閉包条件を証明し、次に論理式の実際の部分式閉包へ適用します。
<!--/-->

<!--en-->
The proof is short because the two halves it needs were built to meet here. An
element of the closure is the key of a formula, and it brings a closure of its
own that sits inside; a key of a given constructor shape has known subkeys, and
which ones is computed from the shape's tag. So each of the seven clauses is the
same four moves: take the element apart, read its tag, ask what that tag demands,
and hand back what the formula's own closure already contains.
<!--zh-->
证明之所以短，是因为它所需的两个部分本就是为在此处结合而构造的。闭包的元素是某条公式的键，而该公式自身带有含于其中的闭包；给定构造子形状的键有已知的诸子键，具体是哪几个由该形状的标签算出。故七条子句里的每一条都是同样四步：把元素拆开、读出它的标签、由该标签确定需要什么，再给出该公式自己的闭包早已含有的那些键。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Coding.SubformulaClosure {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Closure {ℓ} using ( closedAt; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt; binSameClosed-in; unSameClosed-in; unSuccClosed-in; binSuccClosed-in )
open import L.Coding.CodeConstructibility {ℓ}
  using ( closure; closureL; closure-inv; byTag; Concl; key )

open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The closure as a model element
<!--zh-->
## 作为模型元素的闭包
<!--ja-->
## モデルの要素としての閉包
<!--/-->

<!--en-->
`clo φ` packages the externally constructed set `closure f h φ` with its
constructibility proof, making it an element of `L` against which `closedAt` can
be evaluated.
<!--zh-->
`clo φ` 把外部构造的集合 `closure f h φ` 与其可构造性证明封装起来，使其成为 `L` 的元素，因而可以在它上面求值 `closedAt`。
<!--ja-->
`clo φ` は外側で構成した集合 `closure f h φ` とその構成可能性の証明を組み合わせ、`closedAt` を評価できる `L` の要素にします。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where
  private
    Cl : ∀ {n} → Formula K n → V ℓ
    Cl = closure f h

  clo : ∀ {n} → Formula K n → S
  clo φ = closure f h φ , closureL f h φ
```

<!--en-->
## Recovering subformula keys
<!--zh-->
## 恢复子公式键
<!--ja-->
## 部分式の鍵を復元する
<!--/-->

<!--en-->
`Peel C` says that every member of `C` is the key of a formula whose own closure
is contained in `C`. This is exactly the information needed to recover the
immediate subformula keys demanded by a constructor tag.
<!--zh-->
`Peel C` 表示 `C` 的每个成员都是某个公式的键，而且该公式自身的闭包包含于 `C`。这恰是根据构造子标签恢复所需直接子公式键的信息。
<!--ja-->
`Peel C` は、`C` の各要素がある論理式の鍵であり、その論理式自身の閉包が `C` に含まれることを表します。これは構成子のタグが要求する直接の部分式の鍵を復元するために必要な情報そのものです。
<!--/-->

<!--en-->
Stating it separately is not tidiness. A later chapter cuts a set of codes out of
a stage and has to prove the same closedness for it, and that set is not a
closure of anything; what it has instead is a characterization of its members as
keys, and `Peel`{.Agda} is what a characterization turns into. So the seven
clauses are proved once, for any set that peels, and the closure is the first of
the two instances rather than the subject.
<!--zh-->
把它单独陈述出来不是为了整洁。后面有一章从一层里切出一个码集，须为它证同一条封闭性，而那个集合不是任何东西的闭包；它手上有的是「其诸成员即诸键」这条刻画，而 `Peel`{.Agda} 正是一条刻画所化成的东西。故七条子句只证一次，对任何可剥开的集合成立，而闭包是那两个实例中的头一个，不是主角。
<!--/-->

```agda
  Peel : V ℓ → Type (ℓ-suc ℓ)
  Peel C = (x : V ℓ) → ⟨ x ∈ C ⟩
         → ∥ (Σ[ m ∈ ℕ ] Σ[ ψ ∈ Formula K m ]
               ((x ≡ key f h ψ) × ((z : V ℓ) → ⟨ z ∈ Cl ψ ⟩ → ⟨ z ∈ C ⟩))) ∥₁
```

<!--en-->
## The seven closure conditions
<!--zh-->
## 七条闭包子句
<!--ja-->
## 七つの閉包節
<!--/-->

<!--en-->
The helpers `same`, `one`, `up`, and `sndUp` turn a peeled formula key into the
subkeys required by binary, unary, arity-raising, and bounded-quantifier
constructors. Their seven tag instances prove the seven closure conditions.
<!--zh-->
辅助构造 `same`、`one`、`up` 与 `sndUp` 把剥出的公式键转成二元、一元、提升元数及有界量词构造子所需的子键；它们在七个标签上的实例证明七条闭包条件。
<!--ja-->
補助構成 `same`、`one`、`up`、`sndUp` は、取り出した論理式の鍵を、二項、単項、アリティを増やす構成子、有界量化子が要求する部分鍵へ変換します。七つのタグへの適用が七つの閉包条件を証明します。
<!--/-->

<!--en-->
The truncation that peeling returns is eliminated straight away, which is allowed
because what is being produced is a membership, or a pair of them, and membership
is a proposition.
<!--zh-->
剥开所返回的那个截断当场消掉，这是允许的，因为要产出的是一条隶属、或一对隶属，而隶属是命题。
<!--/-->

```agda
  module _ (D : S) (peel : Peel (fst D)) where
    private
      C : V ℓ
      C = fst D

      viaKey : (k : ℕ) (c : S) (ar p : V ℓ)
             → ⟨ fst c ∈ C ⟩ → fst c ≡ pr ar (pr (# k) p)
             → (T : Type (ℓ-suc ℓ)) → isProp T
             → (Concl f h C k ar p → T) → T
      viaKey k c ar p c∈ sh T pT g = PT.rec pT
        (λ { (m , ψ , q , incl) →
          g (byTag f h C ψ k ar p incl (sym q ∙ sh)) })
        (peel (fst c) c∈)

      same : ∀ {m} (γ : S ^ m) (k : ℕ)
           → ((ar a b : V ℓ) → Concl f h C k ar (pr a b)
              → ⟨ pr ar a ∈ C ⟩ × ⟨ pr ar b ∈ C ⟩)
           → ⟨ (D ∷ γ) ⊨ binShapeAt zero k (bothSameAt zero) ⟩
      same γ k use = binSameClosed-in zero k (D ∷ γ)
        (λ c ar a b c∈ sh →
          viaKey k c (fst ar) (pr (fst a) (fst b)) c∈ sh _
            (isProp× (snd (pr (fst ar) (fst a) ∈ C))
                     (snd (pr (fst ar) (fst b) ∈ C)))
            (use (fst ar) (fst a) (fst b)))

      one : ∀ {m} (γ : S ^ m) (k : ℕ)
          → ((ar a : V ℓ) → Concl f h C k ar a → ⟨ pr ar a ∈ C ⟩)
          → ⟨ (D ∷ γ) ⊨ unShapeAt zero k (oneSameAt zero) ⟩
      one γ k use = unSameClosed-in zero k (D ∷ γ)
        (λ c ar a c∈ sh →
          viaKey k c (fst ar) (fst a) c∈ sh _
            (snd (pr (fst ar) (fst a) ∈ C)) (use (fst ar) (fst a)))

      up : ∀ {m} (γ : S ^ m) (k : ℕ)
         → ((ar a : V ℓ) → Concl f h C k ar a → ⟨ pr (sucV ar) a ∈ C ⟩)
         → ⟨ (D ∷ γ) ⊨ unShapeAt zero k (oneSuccAt zero) ⟩
      up γ k use = unSuccClosed-in zero k (D ∷ γ)
        (λ c ar a c∈ sh →
          viaKey k c (fst ar) (fst a) c∈ sh _
            (snd (pr (sucV (fst ar)) (fst a) ∈ C)) (use (fst ar) (fst a)))

      sndUp : ∀ {m} (γ : S ^ m) (k : ℕ)
            → ((ar a b : V ℓ) → Concl f h C k ar (pr a b)
               → ⟨ pr (sucV ar) b ∈ C ⟩)
            → ⟨ (D ∷ γ) ⊨ binShapeAt zero k (succSndAt zero) ⟩
      sndUp γ k use = binSuccClosed-in zero k (D ∷ γ)
        (λ c ar a b c∈ sh →
          viaKey k c (fst ar) (pr (fst a) (fst b)) c∈ sh _
            (snd (pr (sucV (fst ar)) (fst b) ∈ C))
            (use (fst ar) (fst a) (fst b)))
```

<!--en-->
## Combining the closure conditions
<!--zh-->
## 七条子句的合取
<!--ja-->
## 七つの節の連言
<!--/-->

<!--en-->
`closedOf` combines the seven tag instances into the conjunction `closedAt` for
any model element whose underlying set satisfies `Peel`; `closureClosed` supplies
`closure-inv` to obtain the result for `clo φ`.
<!--zh-->
`closedOf` 把七个标签实例合成任意底层集合满足 `Peel` 的模型元素的合取 `closedAt`；`closureClosed` 提供 `closure-inv`，得到 `clo φ` 的结论。
<!--ja-->
`closedOf` は七つのタグの適用を、台となる集合が `Peel` を満たす任意のモデル要素についての連言 `closedAt` にまとめます。`closureClosed` は `closure-inv` を渡して `clo φ` に対する結果を得ます。
<!--/-->

<!--en-->
`closureClosed`{.Agda} is then the instance at a closure, and its peeling is
`closure-inv`{.Agda} unchanged: the two statements are the same type, because
`Peel`{.Agda} was read off that lemma's conclusion.
<!--zh-->
`closureClosed`{.Agda} 于是就是落在闭包处的那个实例，而它的剥开就是原样的 `closure-inv`{.Agda}：两条陈述是同一个类型，因为 `Peel`{.Agda} 本就是照着那条引理的结论读出来的。
<!--/-->

```agda
    closedOf : ∀ {m} (γ : S ^ m) → ⟨ (D ∷ γ) ⊨ closedAt zero ⟩
    closedOf γ =
        same γ 2 (λ _ a b r → r a b refl)
      , ( same γ 3 (λ _ a b r → r a b refl)
      , ( same γ 4 (λ _ a b r → r a b refl)
      , ( up γ 6 (λ _ _ r → r)
      , ( up γ 7 (λ _ _ r → r)
      , ( sndUp γ 8 (λ _ a b r → r a b refl)
      , sndUp γ 9 (λ _ a b r → r a b refl) )))))

  closureClosed : ∀ {n m} (φ : Formula K n) (γ : S ^ m)
                → ⟨ (clo φ ∷ γ) ⊨ closedAt zero ⟩
  closureClosed φ γ = closedOf (clo φ) (closure-inv f h φ) γ
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
`closedOf`{.Agda} is the hypothesis a recursion over subcodes needs about its
index set, discharged for any set that peels; `closureClosed`{.Agda} is that
statement at a closure. Nothing in either is about satisfaction: the seven clauses
say only which keys a key of a given shape brings in, and a set that peels holds
exactly those.
<!--zh-->
`closedOf`{.Agda} 给出对子码递归的索引集所需的假设，并适用于任何可剥开的集合；`closureClosed`{.Agda} 则将该结论用于闭包。两者都不涉及满足关系：七条子句只说明给定形状的键会引入哪些键，而可剥开的集合恰好包含这些键。
<!--ja-->
任意の Peel 性を持つ集合について closedOf が部分式閉包条件を証明し、closureClosed がそれを論理式の実際の閉包に適用する。内容は満足関係の値ではなく、各コード形が要求する部分鍵の包含である。
<!--/-->

<!--en-->
What it cost is worth recording, because the same shape is what the satisfaction
instance will pay. Four readers, seven lines of instantiation, and one lemma per
reader; the content is in `byTag`{.Agda} one chapter earlier, where the ten
constructors were matched against the seven demands once and for all rather than
ten times seven. `byTag`{.Agda} was already written against an arbitrary target
set, which is why generality here is free: the closure was never the subject, only
the first thing handed in.
<!--zh-->
它的代价值得记下，因为满足关系那个实例要付的是同样的形状。四个读式、七行实例化、每个读式一条引理；内容在早一章的 `byTag`{.Agda} 里，那里把十个构造子与七项要求一次性对上，而不是对上十乘七次。`byTag`{.Agda} 本就是对着任意目标集写的，这正是此处的一般性免费的原因：闭包从来不是主角，只是头一个被递进来的东西。
<!--/-->
