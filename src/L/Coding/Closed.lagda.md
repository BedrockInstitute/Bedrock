# The closure is closed

<!--en-->
A recursion over codes is stated against an index set, and the index set has to
carry the subcodes of everything in it or the clauses constrain nothing. The
object language says so; this chapter says that the closure of a formula
satisfies what the object language says, which is the hypothesis the first
instance will discharge.

The proof is short because the two halves it needs were built to meet here. An
element of the closure is the key of a formula, and it brings a closure of its
own that sits inside; a key of a given constructor shape has known subkeys, and
which ones is computed from the shape's tag. So each of the seven clauses is the
same four moves: take the element apart, read its tag, ask what that tag demands,
and hand back what the formula's own closure already contains.
<!--zh-->
对码的递归是相对于一个索引集陈述的，而索引集必须携带其每个成员的诸子码，否则诸子句什么也约束不了。对象语言把这一点说出来了；本章说的是「一条公式的闭包满足对象语言所说的那件事」，而那正是第一个实例要交付的假设。

证明短，因为它所需的两半本就是为了在此处会合而造的。闭包的元素是某条公式的键，而它自带一个坐落于内的闭包；一个给定构造子形状的键有已知的诸子键，而是哪几个由那个形状的标签算出。故七条子句里的每一条都是同样四步：把元素拆开、读出它的标签、问那个标签索取什么，再把该公式自己的闭包早已含有的东西交回去。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Closed {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Closure {ℓ} using ( closedAt; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt; binSameClosed-in; unSameClosed-in; unSuccClosed-in; binSuccClosed-in )
open import L.Coding.InL {ℓ}
  using ( closure; closureL; closure-inv; byTag; Concl; key )

open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The closure, as an element of the model
<!--zh-->
## 作为模型元素的闭包
<!--/-->

<!--en-->
Two chapters ago the closure was a set of the hierarchy carrying a
constructibility certificate. Here it is one element of the model, which is what
an object-language formula can be evaluated against.
<!--zh-->
两章之前，闭包还是层级的一个集合，另带一份可构造性证书。此处它是模型的一个元素，而对象语言的公式正是相对于这样的东西求值的。
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
## What the proof actually uses
<!--zh-->
## 证明真正用到的东西
<!--/-->

<!--en-->
The clauses below never look at a formula. Each of them takes a member of the
set, asks which key it is, and hands back keys that the set already holds, so the
only thing about the closure that any of them consumes is that a member *peels*:
that it is merely the key of some formula whose own closure sits inside the set.
That is `Peel`{.Agda}, and it is exactly what `closure-inv`{.Agda} returns when
the set is a closure.

Stating it separately is not tidiness. A later chapter cuts a set of codes out of
a stage and has to prove the same closedness for it, and that set is not a
closure of anything; what it has instead is a characterization of its members as
keys, and `Peel`{.Agda} is what a characterization turns into. So the seven
clauses are proved once, for any set that peels, and the closure is the first of
the two instances rather than the subject.
<!--zh-->
下面那些子句从不看一条公式。每一条都取该集合的一个成员，问它是哪个键，再交回该集合早已持有的诸键；故任何一条所消费的、关于闭包的唯一一件事，就是「成员可**剥开**」：它仅仅是某条公式的键，而那条公式自己的闭包坐落于该集合之内。那就是 `Peel`{.Agda}，也正是当那个集合是一个闭包时 `closure-inv`{.Agda} 所返回的东西。

把它单独陈述出来不是为了整洁。后面有一章从一个阶段里切出一个码集，须为它证同一条封闭性，而那个集合不是任何东西的闭包；它手上有的是「其诸成员即诸键」这条刻画，而 `Peel`{.Agda} 正是一条刻画所化成的东西。故七条子句只证一次，对任何可剥开的集合成立，而闭包是那两个实例中的头一个，不是主角。
<!--/-->

```agda
  Peel : V ℓ → Type (ℓ-suc ℓ)
  Peel C = (x : V ℓ) → ⟨ x ∈ C ⟩
         → ∥ (Σ[ m ∈ ℕ ] Σ[ ψ ∈ Formula K m ]
               ((x ≡ key f h ψ) × ((z : V ℓ) → ⟨ z ∈ Cl ψ ⟩ → ⟨ z ∈ C ⟩))) ∥₁
```

<!--en-->
## The seven clauses
<!--zh-->
## 七条子句
<!--/-->

<!--en-->
Each is the introduction rule of its frame applied to one function, and that
function is the same four moves every time. The tag is the only thing that
changes between two clauses of the same shape, and the shape is what decides
which of the four readers is used.

The truncation that peeling returns is eliminated straight away, which is allowed
because what is being produced is a membership, or a pair of them, and membership
is a proposition.
<!--zh-->
每一条都是它那个框架的引入规则施于一个函数，而那个函数每次都是同样四步。形状相同的两条子句之间唯一变的是标签，而形状决定用四个读式中的哪一个。

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
## The conjunction
<!--zh-->
## 那个合取
<!--/-->

<!--en-->
Seven instances of four shapes, and the tag is the only argument that moves. The
continuation handed to each says what the demand at that tag *is*, and it is that
argument, not the shape, that makes the seven seven.

`closureClosed`{.Agda} is then the instance at a closure, and its peeling is
`closure-inv`{.Agda} unchanged: the two statements are the same type, because
`Peel`{.Agda} was read off that lemma's conclusion.
<!--zh-->
四种形状的七个实例，而唯一变动的参数是标签。交给每一个的那段后继说出那个标签处的要求**是什么**，而使这七条成其为七条的正是那个参数，不是形状。

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
<!--/-->

<!--en-->
`closedOf`{.Agda} is the hypothesis a recursion over subcodes needs about its
index set, discharged for any set that peels; `closureClosed`{.Agda} is that
statement at a closure. Nothing in either is about satisfaction: the seven clauses
say only which keys a key of a given shape drags in, and a set that peels holds
exactly those.

What it cost is worth recording, because the same shape is what the satisfaction
instance will pay. Four readers, seven lines of instantiation, and one lemma per
reader; the content is in `byTag`{.Agda} one chapter earlier, where the ten
constructors were matched against the seven demands once and for all rather than
ten times seven. `byTag`{.Agda} was already written against an arbitrary target
set, which is why generality here is free: the closure was never the subject, only
the first thing handed in.
<!--zh-->
`closedOf`{.Agda} 是「对诸子码作递归」关于其索引集所需的那条假设，对任何可剥开的集合交付；`closureClosed`{.Agda} 是那条陈述落在闭包处。两者里都没有任何关于满足关系的东西：七条子句只说一个给定形状的键会拖进哪些键，而一个可剥开的集合恰好持有那些。

它的代价值得记下，因为满足关系那个实例要付的是同样的形状。四个读式、七行实例化、每个读式一条引理；内容在早一章的 `byTag`{.Agda} 里，那里把十个构造子与七项要求一次性对上，而不是对上十乘七次。`byTag`{.Agda} 本就是对着任意目标集写的，这正是此处的一般性免费的原因：闭包从来不是主角，只是头一个被递进来的东西。
<!--/-->
