# Readers, quoted in the model

<!--en-->
The readers were written about the hierarchy and the bridge carries them into the
model. This chapter takes the bridge across, once, and states what a quoted
reader means on the far side.

There is one wrinkle and it is small. A reader's meaning was stated in terms of
the value of a variable in a hierarchy environment; on the far side the
environment holds elements of the model, and the hierarchy environment is the one
obtained by taking underlying sets. Looking up in the projected environment is
projecting the lookup, which is a two-line induction, and after it the quoted
reader says exactly what the original said about the underlying sets.

The first reader to cross is the one everything else is built from: the ordered
pair. Nothing above it needs a new argument, because the bridge is generic and
the readers' own characterizations were proved once already.
<!--zh-->
诸读式写的是关于层级的事，而那座桥把它们运进模型。本章把桥走一遍，并陈述一条被引用的读式在彼岸说的是什么。

有一处小小的皱褶。读式的含义当初是按「变元在层级环境中的取值」陈述的；而在彼岸，环境装的是模型的元素，那个层级环境是取底集得来的。在投影后的环境中查表就是把查表的结果投影，这是一次两行的归纳，之后被引用的读式所说的，恰是原读式关于诸底集所说的。

第一条过河的读式是此后一切所由构造的那条：有序对。它之上不再需要新的论证，因为那座桥是通用的，而诸读式自身的刻画早已证过一次。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Model {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Absoluteness {ℓ} using ( liftFo; transferFo )
open import L.Coding.Base {ℓ} using ( prAt; Δ₀-prAt; prAt-adequate )

open import Cubical.Data.Vec using ( map )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Looking up in a projected environment
<!--zh-->
## 在投影后的环境中查表
<!--/-->

<!--en-->
Two lines, and the only bookkeeping the crossing costs.
<!--zh-->
两行，也是这次过河所付的全部记账。
<!--/-->

```agda
lookup-fst : ∀ {n} (i : Fin n) (γ : S ^ n)
           → lookup i (map fst γ) ≡ fst (lookup i γ)
lookup-fst zero    (x ∷ γ) = refl
lookup-fst (suc i) (x ∷ γ) = lookup-fst i γ
```

<!--en-->
## The ordered pair
<!--zh-->
## 有序对
<!--/-->

<!--en-->
The quoted reader is the original lifted along the bridge, and the lift asks for
nothing: the reader names no constants, so there is nothing to be constructible
and the admissibility witness is empty.

Its meaning is three steps. The bridge equates satisfaction in the model with
satisfaction in the hierarchy at the projected environment; the reader's own
characterization says what that is; and the lookups are projected. What comes out
is the statement a consumer wants: the value of one variable is the Kuratowski
pair of the values of the other two, as sets.
<!--zh-->
被引用的读式就是原读式沿桥抬升，而抬升什么也不索取：该读式不点名任何常元，故没有东西需要可构造，合格性证书是空的。

它的含义分三步。桥把「在模型中满足」等同于「在层级中、于投影后的环境处满足」；读式自家的刻画说出那是什么；诸查表被投影。出来的正是消费方想要的陈述：一个变元的取值，是另两个变元取值的 Kuratowski 对，作为集合而言。
<!--/-->

```agda
private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

prAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
prAtL q u v = liftFo (prAt q u v) _

prAtL-adequate : ∀ {n} (q u v : Fin n) (γ : S ^ n)
  → (γ ⊨ prAtL q u v)
  ≡ PairIs (fst (lookup q γ)) (pr (fst (lookup u γ)) (fst (lookup v γ)))
prAtL-adequate q u v γ =
    transferFo (prAt q u v) _ (Δ₀-prAt q u v) γ
  ∙ prAt-adequate q u v (map fst γ)
  ∙ cong₂ PairIs (lookup-fst q γ)
      (cong₂ pr (lookup-fst u γ) (lookup-fst v γ))
```

<!--en-->
## Application
<!--zh-->
## 取值
<!--/-->

<!--en-->
A function in the object language is a set of ordered pairs, so the one thing
every use of one asks is whether a given pair belongs to it. That is a bounded
existential over the function, with the pair reader inside, and its meaning is
membership of the Kuratowski pair.

The backward direction is where the model earns its keep, and it is worth
noticing. To satisfy the existential one must produce an *element of the model*
whose underlying set is the pair; the hypothesis only supplies a set. It is
constructible because it belongs to something constructible, and the class is
transitive. That is the whole argument, and the same step will recur wherever a
witness has to be produced inside the model rather than merely in the hierarchy.
<!--zh-->
对象语言里的函数是有序对之集，故凡用到函数的地方，所问的唯一一件事就是某个给定的对是否属于它。那是在该函数上的一个有界存在，里面装着对读式，而它的含义是那个 Kuratowski 对的隶属关系。

反向是模型出力之处，值得留意。要满足那个存在量词，必须拿出一个**模型的元素**，其底集是那个对；而假设只给了一个集合。它可构造，因为它属于某个可构造之物，而这个类传递。全部论证仅此而已，而同一步将在此后每个「见证必须造在模型之内、而非仅在层级之内」的地方重现。
<!--/-->

```agda
appAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
appAt f x y = ∃̇∈ (var f) (prAtL zero (suc x) (suc y))

appAt-adequate : ∀ {n} (f x y : Fin n) (γ : S ^ n)
  → (γ ⊨ appAt f x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ))
appAt-adequate f x y γ = ⇔toPath fwd bwd
  where
  a = fst (lookup x γ)
  b = fst (lookup y γ)
  F = lookup f γ

  read : (z : S) → ⟨ (z ∷ γ) ⊨ prAtL zero (suc x) (suc y) ⟩ → fst z ≡ pr a b
  read z h = subst ⟨_⟩ (prAtL-adequate zero (suc x) (suc y) (z ∷ γ)) h

  fwd : ⟨ γ ⊨ appAt f x y ⟩ → ⟨ pr a b ∈ fst F ⟩
  fwd = PT.rec (snd (pr a b ∈ fst F))
    (λ { (z , (z∈F , h)) → subst (λ w → ⟨ w ∈ fst F ⟩) (read z h) z∈F })

  bwd : ⟨ pr a b ∈ fst F ⟩ → ⟨ γ ⊨ appAt f x y ⟩
  bwd h = ∣ zS , (h , subst ⟨_⟩
      (sym (prAtL-adequate zero (suc x) (suc y) (zS ∷ γ))) refl) ∣₁
    where
    zS : S
    zS = pr a b , isL-trans {x = fst F} {y = pr a b} h (F .snd)
```

<!--en-->
## Single-valuedness
<!--zh-->
## 单值性
<!--/-->

<!--en-->
The other half of being a function: a pair's first component determines its
second. Three unbounded quantifiers, which cost nothing here, and two
applications of the reader above.

Stated as two directions rather than a path, because that is how consumers use
it and because building the right-hand side as a proposition would say the same
thing at more length. Reading it out is the direction that matters: from the
object-language claim, an actual proof that two values recorded against the same
argument agree.
<!--zh-->
作为函数的另一半：一个对的第一分量决定它的第二分量。三个无界量词 (此处不费分文)，加上面那条读式的两次应用。

陈述为两个方向而非一条道路，因为消费方就是这么用的，也因为把右侧造成一个命题只会把同一句话说得更长。读出来的那个方向才要紧：从对象语言的断言，得到「记在同一自变量下的两个取值相等」的一份真凭实据。
<!--/-->

```agda
svAt : ∀ {n} → Fin n → Formula S n
svAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero)
  ⇒̇ (appAt (suc (suc (suc f))) (suc (suc zero)) zero
  ⇒̇ (var (suc zero) ≐ var zero)))))

module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds : S → S → Type (ℓ-suc ℓ)
    Holds x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at : (x y y' : S)
       → ((y' ∷ y ∷ x ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero))
       ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at x y y' = appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero)
                  (y' ∷ y ∷ x ∷ γ)

    at' : (x y y' : S)
        → ((y' ∷ y ∷ x ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc (suc zero)) zero)
        ≡ (pr (fst x) (fst y') ∈ fst (lookup f γ))
    at' x y y' = appAt-adequate (suc (suc (suc f))) (suc (suc zero)) zero
                   (y' ∷ y ∷ x ∷ γ)

  svAt-out : ⟨ γ ⊨ svAt f ⟩
           → (x y y' : S) → Holds x y → Holds x y' → fst y ≡ fst y'
  svAt-out h x y y' p q = h x y y'
    (subst ⟨_⟩ (sym (at x y y')) p) (subst ⟨_⟩ (sym (at' x y y')) q)

  svAt-in : ((x y y' : S) → Holds x y → Holds x y' → fst y ≡ fst y')
          → ⟨ γ ⊨ svAt f ⟩
  svAt-in h x y y' p q = h x y y'
    (subst ⟨_⟩ (at x y y') p) (subst ⟨_⟩ (at' x y y') q)
```

<!--en-->
## The domain
<!--zh-->
## 定义域
<!--/-->

<!--en-->
Being in the domain is having a value: one unbounded existential over the reader
above. The domain itself is then the set with exactly those members, said as two
implications, since the object language has no biconditional of its own and
spelling it out is shorter than adding one.

Both are used in one direction each, and only those directions are extracted. A
consumer holding a table asks either "this argument has an entry, so it is in the
domain" or "this argument is in the domain, so it has an entry"; nothing wants
the statement as a proposition.
<!--zh-->
落在定义域中就是有取值：在上面那条读式上作一个无界存在。定义域本身则是恰以那些东西为成员的集合，用两条蕴含说出，因为对象语言没有自带的双条件，而把它摊开来写比添一个更短。

两者各自只用一个方向，而被取出的也只有那两个方向。一个握着表的消费方，要么问「这个自变量有条目，故它在定义域中」，要么问「这个自变量在定义域中，故它有条目」；没有谁想要那句陈述本身作为命题。
<!--/-->

```agda
inDomAt : ∀ {n} → Fin n → Fin n → Formula S n
inDomAt f x = ∃̇ (appAt (suc f) (suc x) zero)

inDomAt-adequate : ∀ {n} (f x : Fin n) (γ : S ^ n)
  → (γ ⊨ inDomAt f x)
  ≡ (∃[ y ∶ S ] (pr (fst (lookup x γ)) (fst y) ∈ fst (lookup f γ)))
inDomAt-adequate f x γ =
  cong (⋁ S) (funExt (λ y → appAt-adequate (suc f) (suc x) zero (y ∷ γ)))

domAt : ∀ {n} → Fin n → Fin n → Formula S n
domAt f d = ∀̇ ( (inDomAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc d)))
             ∧̇ ((var zero ∈̇ var (suc d)) ⇒̇ inDomAt (suc f) zero) )

module _ {n : ℕ} (f d : Fin n) (γ : S ^ n) where
  private
    step : (x : S)
         → ((x ∷ γ) ⊨ inDomAt (suc f) zero)
         ≡ (∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)))
    step x = inDomAt-adequate (suc f) zero (x ∷ γ)

  domAt-out : ⟨ γ ⊨ domAt f d ⟩ → (x y : S)
            → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
            → ⟨ fst x ∈ fst (lookup d γ) ⟩
  domAt-out h x y p = h x .fst (subst ⟨_⟩ (sym (step x)) ∣ y , p ∣₁)

  domAt-in : ⟨ γ ⊨ domAt f d ⟩ → (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩
           → ∥ (Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩) ∥₁
  domAt-in h x m = subst ⟨_⟩ (step x) (h x .snd m)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`prAtL`{.Agda} says, in the object language of the model, that one set is the
ordered pair of two others, `appAt`{.Agda} that a function contains a given pair,
`svAt`{.Agda} that it contains at most one pair per argument, and
`domAt`{.Agda} that a given set is exactly the arguments it answers for. Together
they are what "function" means in the object language, and every recursion graph
is written through them. It was
obtained by quoting, not by re-proving: the reader and its characterization stay
where they were written, and the crossing cost one induction on environments.

That is the pattern for every reader that follows, and it is the reason the
coding chapters did not have to be re-based. What it does not cover is any
predicate that is not Δ₀, and those are to be written directly over the model
instead, since nothing in the model's comprehension asks them to be bounded.
<!--zh-->
`prAtL`{.Agda} 在模型的对象语言里说「这个集合是那两个的有序对」，`appAt`{.Agda} 说「某函数含有某个给定的对」，`svAt`{.Agda} 说「每个自变量至多含一个对」，而 `domAt`{.Agda} 说「某个给定集合恰是它作答的那些自变量」。它们合起来就是对象语言里「函数」的含义，而此后每条递归的图都经它们写出。它由引用得来，而非重新证得：读式与它的刻画留在写下它们的地方，而这次过河只花了一次关于环境的归纳。

这就是此后每条读式的套路，也是编码诸章无须换底的原因。它不覆盖的是任何非 Δ₀ 的谓词，那些应当直接在模型上写，因为模型的概括不要求它们有界。
<!--/-->
