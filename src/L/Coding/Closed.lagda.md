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
which ones is computed from the shape's tag. So each of the eight clauses is the
same four moves: take the element apart, read its tag, ask what that tag demands,
and hand back what the formula's own closure already contains.
<!--zh-->
对码的递归是相对于一个索引集陈述的，而索引集必须携带其每个成员的诸子码，否则诸子句什么也约束不了。对象语言把这一点说出来了；本章说的是「一条公式的闭包满足对象语言所说的那件事」，而那正是第一个实例要交付的假设。

证明短，因为它所需的两半本就是为了在此处会合而造的。闭包的元素是某条公式的键，而它自带一个坐落于内的闭包；一个给定构造子形状的键有已知的诸子键，而是哪几个由那个形状的标签算出。故八条子句里的每一条都是同样四步：把元素拆开、读出它的标签、问那个标签索取什么，再把该公式自己的闭包早已含有的东西交回去。
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
open import L.Coding.Model {ℓ}
  using ( closedAt; binShapeAt; unShapeAt
        ; bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; binSameClosed-in; unSameClosed-in; unSuccClosed-in; binSuccClosed-in )
open import L.Coding.InL {ℓ} using ( closure; closureL; closure-inv; byTag; Concl )

open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
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
## The eight clauses
<!--zh-->
## 八条子句
<!--/-->

<!--en-->
Each is the introduction rule of its frame applied to one function, and that
function is the same four moves every time. The tag is the only thing that
changes between two clauses of the same shape, and the shape is what decides
which of the four readers is used.

The truncation that `closure-inv`{.Agda} returns is eliminated straight away,
which is allowed because what is being produced is a membership, or a pair of
them, and membership is a proposition.
<!--zh-->
每一条都是它那个框架的引入规则施于一个函数，而那个函数每次都是同样四步。形状相同的两条子句之间唯一变的是标签，而形状决定用四个读式中的哪一个。

`closure-inv`{.Agda} 返回的那个截断当场消掉，这是允许的，因为要产出的是一条隶属、或一对隶属，而隶属是命题。
<!--/-->

```agda
  private
    γφ : ∀ {n} → Formula K n → S ^ 1
    γφ φ = clo φ ∷ []

    viaKey : ∀ {n} (φ : Formula K n) (k : ℕ) (c : S) (ar p : V ℓ)
           → ⟨ fst c ∈ Cl φ ⟩ → fst c ≡ pr ar (pr (# k) p)
           → (T : Type (ℓ-suc ℓ)) → isProp T
           → (Concl f h (Cl φ) k ar p → T) → T
    viaKey φ k c ar p c∈ sh T pT g = PT.rec pT
      (λ { (m , ψ , q , incl) →
        g (byTag f h (Cl φ) ψ k ar p incl (sym q ∙ sh)) })
      (closure-inv f h φ (fst c) c∈)

    same : ∀ {n} (φ : Formula K n) (k : ℕ)
         → ((ar a b : V ℓ) → Concl f h (Cl φ) k ar (pr a b)
            → ⟨ pr ar a ∈ Cl φ ⟩ × ⟨ pr ar b ∈ Cl φ ⟩)
         → ⟨ γφ φ ⊨ binShapeAt zero k (bothSameAt zero) ⟩
    same φ k use = binSameClosed-in zero k (γφ φ)
      (λ c ar a b c∈ sh →
        viaKey φ k c (fst ar) (pr (fst a) (fst b)) c∈ sh _
          (isProp× (snd (pr (fst ar) (fst a) ∈ Cl φ))
                   (snd (pr (fst ar) (fst b) ∈ Cl φ)))
          (use (fst ar) (fst a) (fst b)))

    one : ∀ {n} (φ : Formula K n) (k : ℕ)
        → ((ar a : V ℓ) → Concl f h (Cl φ) k ar a → ⟨ pr ar a ∈ Cl φ ⟩)
        → ⟨ γφ φ ⊨ unShapeAt zero k (oneSameAt zero) ⟩
    one φ k use = unSameClosed-in zero k (γφ φ)
      (λ c ar a c∈ sh →
        viaKey φ k c (fst ar) (fst a) c∈ sh _
          (snd (pr (fst ar) (fst a) ∈ Cl φ)) (use (fst ar) (fst a)))

    up : ∀ {n} (φ : Formula K n) (k : ℕ)
       → ((ar a : V ℓ) → Concl f h (Cl φ) k ar a → ⟨ pr (sucV ar) a ∈ Cl φ ⟩)
       → ⟨ γφ φ ⊨ unShapeAt zero k (oneSuccAt zero) ⟩
    up φ k use = unSuccClosed-in zero k (γφ φ)
      (λ c ar a c∈ sh →
        viaKey φ k c (fst ar) (fst a) c∈ sh _
          (snd (pr (sucV (fst ar)) (fst a) ∈ Cl φ)) (use (fst ar) (fst a)))

    sndUp : ∀ {n} (φ : Formula K n) (k : ℕ)
          → ((ar a b : V ℓ) → Concl f h (Cl φ) k ar (pr a b)
             → ⟨ pr (sucV ar) b ∈ Cl φ ⟩)
          → ⟨ γφ φ ⊨ binShapeAt zero k (succSndAt zero) ⟩
    sndUp φ k use = binSuccClosed-in zero k (γφ φ)
      (λ c ar a b c∈ sh →
        viaKey φ k c (fst ar) (pr (fst a) (fst b)) c∈ sh _
          (snd (pr (sucV (fst ar)) (fst b) ∈ Cl φ))
          (use (fst ar) (fst a) (fst b)))
```

<!--en-->
## The conjunction
<!--zh-->
## 那个合取
<!--/-->

<!--en-->
Eight instances of four shapes, and the tag is the only argument that moves. The
continuation handed to each says what the demand at that tag *is*, and it is that
argument, not the shape, that makes the eight eight.
<!--zh-->
四种形状的八个实例，而唯一变动的参数是标签。交给每一个的那段后继说出那个标签处的要求**是什么**，而使这八条成其为八条的正是那个参数，不是形状。
<!--/-->

```agda
  closureClosed : ∀ {n} (φ : Formula K n) → ⟨ γφ φ ⊨ closedAt zero ⟩
  closureClosed φ =
      same φ 2 (λ _ a b r → r a b refl)
    , ( same φ 3 (λ _ a b r → r a b refl)
    , ( same φ 4 (λ _ a b r → r a b refl)
    , ( one φ 5 (λ _ _ r → r)
    , ( up φ 8 (λ _ _ r → r)
    , ( up φ 9 (λ _ _ r → r)
    , ( sndUp φ 10 (λ _ a b r → r a b refl)
    , sndUp φ 11 (λ _ a b r → r a b refl) ))))))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`closureClosed`{.Agda} is the hypothesis a recursion over the subcodes of a
formula needs about its index set, discharged for the closure. Nothing in it is
about satisfaction: the eight clauses say only which keys a key of a given shape
drags in, and the closure was built to drag in exactly those.

What it cost is worth recording, because the same shape is what the satisfaction
instance will pay. Four readers, eight lines of instantiation, and one lemma per
reader; the content is in `byTag`{.Agda} one chapter earlier, where the twelve
constructors were matched against the eight demands once and for all rather than
twelve times eight.
<!--zh-->
`closureClosed`{.Agda} 是「对一条公式的诸子码作递归」关于其索引集所需的那条假设，在闭包处交付。它里面没有任何关于满足关系的东西：八条子句只说一个给定形状的键会拖进哪些键，而闭包本就是为了恰好拖进那些而造的。

它的代价值得记下，因为满足关系那个实例要付的是同样的形状。四个读式、八行实例化、每个读式一条引理；内容在早一章的 `byTag`{.Agda} 里，那里把十二个构造子与八项要求一次性对上，而不是对上十二乘八次。
<!--/-->
