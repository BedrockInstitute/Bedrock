# The object language over the model

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
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∀̇_; ∀̇∈; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import L.Absoluteness {ℓ} using ( InL; liftFo; transferFo )
open import L.Coding.Base {ℓ}
  using ( prAt; Δ₀-prAt; prAt-adequate; sglConAt; pairConAt; tagAt )
open import L.Coding.Environment {ℓ}
  using ( sucAt; Δ₀-sucAt; sucAt-adequate; consAt; Δ₀-consAt; consAt-adequate
        ; env; cons; shiftPairAt )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst; sucʟ; sucʟ-fst )

open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⁅_,_⁆ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

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
## The pair, inside the model
<!--zh-->
## 模型之内的对
<!--/-->

<!--en-->
Every code is built by pairing, so every construction below needs the ordered
pair of two elements of `L` to be one. It is, three applications of the model's
own pairing, and the projection equations of the numeral chapter say that reading
it through the underlying set gives the hierarchy's pair back. The singleton is
the two-element pair with equal components, which is the one small identity the
hierarchy supplies.
<!--zh-->
每个码都由配对造出，故下面每个构造都需要「`L` 两元素的有序对仍是 `L` 的元素」。确实如此，用模型自己的配对三次即可，而数码那一章的投影等式说：沿底层集合读出来就把层级的对还了回来。单点集是两分量相等的对，这是层级供给的那一条小小恒等式。
<!--/-->

```agda
prʟ : S → S → S
prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)

prʟ-fst : (a b : S) → fst (prʟ a b) ≡ pr (fst a) (fst b)
prʟ-fst a b =
    pairʟ-fst (pairʟ a a) (pairʟ a b)
  ∙ cong₂ ⁅_,_⁆ (pairʟ-fst a a ∙ pair-singleton (fst a)) (pairʟ-fst a b)
```

<!--en-->
## Environments
<!--zh-->
## 环境
<!--/-->

<!--en-->
An environment is a function whose values lie in a given set, so the last piece
of vocabulary is that constraint, and an environment over a set is then the
conjunction of the three: single-valued, with the given domain, and with values
where they belong.

Only the three projections are given, because that is all a consumer wants.
Whether a particular set *is* the set of all environments of a given length is a
different question, and a harder one; this says only what it means for a single
thing to be one.
<!--zh-->
一个环境是取值落在给定集合中的函数，故最后一件词汇就是那条约束；而「某集合之上的环境」于是是三者的合取：单值、定义域为给定者、取值落在该落的地方。

只给出三个投影，因为消费方想要的仅此而已。某个特定集合**是否就是**给定长度的全体环境之集，是另一个问题，而且更难；这里说的只是「单个东西是一个环境」是什么意思。
<!--/-->

```agda
valuesInAt : ∀ {n} → Fin n → Fin n → Formula S n
valuesInAt f B = ∀̇ (∀̇ ( appAt (suc (suc f)) (suc zero) zero
                     ⇒̇ (var zero ∈̇ var (suc (suc B))) ))

valuesInAt-out : ∀ {n} (f B : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ valuesInAt f B ⟩ → (x y : S)
               → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
               → ⟨ fst y ∈ fst (lookup B γ) ⟩
valuesInAt-out f B γ h x y p = h x y
  (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (y ∷ x ∷ γ))) p)

envOverAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envOverAt e d B = svAt e ∧̇ (domAt e d ∧̇ valuesInAt e B)

module _ {n : ℕ} (e d B : Fin n) (γ : S ^ n) (h : ⟨ γ ⊨ envOverAt e d B ⟩) where
  envOver-sv     : ⟨ γ ⊨ svAt e ⟩
  envOver-sv     = h .fst
  envOver-dom    : ⟨ γ ⊨ domAt e d ⟩
  envOver-dom    = h .snd .fst
  envOver-values : ⟨ γ ⊨ valuesInAt e B ⟩
  envOver-values = h .snd .snd
```

<!--en-->
## Tags
<!--zh-->
## 标签
<!--/-->

<!--en-->
A code carries its constructor as a numeral in the first component of a pair, so
reading a code's shape means reading a pair whose first component is a *given*
numeral. The reader for that could be quoted like the others, but it would cost
more than writing it: the hierarchy's version names the numeral as a constant of
the hierarchy, so the bridge would demand a constructibility witness threaded
through the whole shape of the formula.

Writing it takes the shorter road, and the road the bridge chapter recommends.
The numeral of `L` is already an element of the model, so it is already a legal
constant here; one unbounded existential says "there is something equal to it,
and the pair is built from that". Unbounded costs nothing, and the two readers
below reuse the pair reader unchanged rather than re-deriving anything.

The second is the one that does the work later. Every binary constructor of the
object language has a code of the same shape, tag applied to the pair of the two
subcodes, differing only in which numeral the tag is.
<!--zh-->
一个码把它的构造子作为数码放在一个对的第一分量里，故读一个码的形状，就是读一个第一分量为**给定**数码的对。那条读式本可以像别的一样被引用，但那样比直接写还贵：层级那边的版本把该数码作为层级的常元点名，于是桥会索取一份沿公式整个形状穿行的可构造性证书。

直接写走的是短路，也是桥那一章推荐的路。`L` 的数码本来就是模型的元素，故它在此处本来就是合法常元；一个无界存在说「有个东西等于它，而那个对由它造出」。无界不费分文，而下面两条读式原样复用对读式，什么也不必重推。

第二条是此后出力的那条。对象语言的每个二元构造子，其码都是同一个形状：标签施于两个子码之对，彼此只差标签是哪个数码。
<!--/-->

```agda
tagAtL : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
tagAtL s k x = ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))

tagAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n) (γ : S ^ n)
  → (γ ⊨ tagAtL s k x)
  ≡ PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))
tagAtL-adequate s k x γ = ⇔toPath fwd bwd
  where
  target = PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))

  fwd : ⟨ γ ⊨ tagAtL s k x ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (e , p)) →
      subst ⟨_⟩ (prAtL-adequate (suc s) zero (suc x) (z ∷ γ)) p
      ∙ cong (λ w → pr w (fst (lookup x γ))) (e ∙ numeralL-fst k) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ tagAtL s k x ⟩
  bwd q = ∣ numeralL k , (refl , subst ⟨_⟩
      (sym (prAtL-adequate (suc s) zero (suc x) (numeralL k ∷ γ)))
      (q ∙ cong (λ w → pr w (fst (lookup x γ))) (sym (numeralL-fst k)))) ∣₁

tagPairAtL : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula S n
tagPairAtL s k a b =
  ∃̇ (prAtL zero (suc a) (suc b) ∧̇ tagAtL (suc s) k zero)

tagPairAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ tagPairAtL s k a b)
  ≡ PairIs (fst (lookup s γ))
      (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ))))
tagPairAtL-adequate s k a b γ = ⇔toPath fwd bwd
  where
  A = fst (lookup a γ)
  B = fst (lookup b γ)
  target = PairIs (fst (lookup s γ)) (pr (# k) (pr A B))

  fwd : ⟨ γ ⊨ tagPairAtL s k a b ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , t)) →
      subst ⟨_⟩ (tagAtL-adequate (suc s) k zero (z ∷ γ)) t
      ∙ cong (pr (# k))
          (subst ⟨_⟩ (prAtL-adequate zero (suc a) (suc b) (z ∷ γ)) p) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ tagPairAtL s k a b ⟩
  bwd q = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate zero (suc a) (suc b) (zS ∷ γ))) e
      , subst ⟨_⟩ (sym (tagAtL-adequate (suc s) k zero (zS ∷ γ)))
          (q ∙ cong (pr (# k)) (sym e)) ) ∣₁
    where
    zS : S
    zS = prʟ (lookup a γ) (lookup b γ)
    e : fst zS ≡ pr A B
    e = prʟ-fst (lookup a γ) (lookup b γ)
```

<!--en-->
## Sets by extension
<!--zh-->
## 以外延给出集合
<!--/-->

<!--en-->
Every clause of a recursion whose values are sets says the same thing: this value
is the set of exactly those things satisfying such-and-such. Written once, with
the condition left as a parameter, it is two implications under one quantifier,
and its two readings are the two projections. Nothing is proved, which is the
point: after this the clauses of a recursion cost only their conditions.

The set operations follow immediately, each one condition long, and each with its
meaning already in hand. The rest of a clause's content is whatever the condition
says, and that is where the mathematics of a particular recursion lives.
<!--zh-->
凡取值为集合的递归，其每一条子句说的都是同一句话：这个取值恰是满足某某条件的那些东西之集。把它一次写出来，条件留作参数，那就是一个量词之下的两条蕴含，而它的两种读法就是两个投影。什么也没有证，而这正是要点：此后一条递归子句的代价，只剩它的条件。

诸集合运算随即而来，每个一条条件那么长，且含义都已在手。一条子句其余的内容全在它的条件里说，而那正是某个特定递归的数学之所在。
<!--/-->

```agda
extAt : ∀ {n} → Fin n → Formula S (suc n) → Formula S n
extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
         ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))

module _ {n : ℕ} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n) where
  extAt-out : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
            → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  extAt-out h = h .fst

  extAt-in : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
           → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩
  extAt-in h = h .snd

private
  memb : ∀ {n} → Fin n → Formula S (suc n)
  memb a = var zero ∈̇ var (suc a)

interAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
interAt y a b = extAt y (memb a ∧̇ memb b)

unionAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
unionAt y a b = extAt y (memb a ∨̇ memb b)

diffAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
diffAt y a b = extAt y (memb a ∧̇ ¬̇ memb b)

sameAt : ∀ {n} → Fin n → Fin n → Formula S n
sameAt y a = extAt y (memb a)

emptyAt : ∀ {n} → Fin n → Formula S n
emptyAt y = extAt y ⊥̇
```

<!--en-->
## Reading a key in two layers
<!--zh-->
## 分两层读一个键
<!--/-->

<!--en-->
The codes a recursion ranges over carry their arity: an entry is the arity's
numeral paired with the code proper, and the code proper is in turn a tag paired
with its payload. So a clause's hypothesis has to read *two* layers, not one, and
reading only the outer one is worse than incomplete. Pairing is injective, so a
one-layer reader silently matches the arity against the constructor tag and binds
the payload's own tag as though it were a subcode: the clause is then vacuous at
every arity but one, and wrong at that one. Nothing in Agda reports this, because
the reader is still true; it simply cannot be supplied.

Both layers are read by one existential over the inner code, with the pair reader
above pinning the outer layer and the tag reader the inner. The arity is left as
a variable, so a clause can speak of it, which the four constructors that change
arity need.
<!--zh-->
递归所遍历的诸码携带自己的元数：一个条目是「元数的数码」与「码本身」之对，而码本身又是「标签」与「载荷」之对。故一条子句的假设必须读**两**层，不是一层；而只读外层比不完整更糟。配对是单射的，于是一层的读式会悄悄把元数与构造子标签匹配起来，并把载荷自己的标签当作子码绑定：那条子句于是在除一个元数外的所有元数上空洞，而在那一个上是错的。Agda 不会报告这件事，因为那条读式仍然为真；它只是无法被供给。

两层由一个「对内层码作存在」读出，上面的对读式钉住外层，标签读式钉住内层。元数留作变元，好让子句能谈论它，而四个改变元数的构造子正需要这一点。
<!--/-->

```agda
arityTagPairAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Fin n → Formula S n
arityTagPairAtL c ar k a b =
  ∃̇ (prAtL (suc c) (suc ar) zero ∧̇ tagPairAtL zero k (suc a) (suc b))

arityTagPairAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagPairAtL c ar k a b)
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ))
        (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ)))))
arityTagPairAtL-adequate c ar k a b γ = ⇔toPath fwd bwd
  where
  N = fst (lookup ar γ)
  P = pr (fst (lookup a γ)) (fst (lookup b γ))
  target = PairIs (fst (lookup c γ)) (pr N (pr (# k) P))

  fwd : ⟨ γ ⊨ arityTagPairAtL c ar k a b ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , t)) →
      subst ⟨_⟩ (prAtL-adequate (suc c) (suc ar) zero (z ∷ γ)) p
      ∙ cong (pr N) (subst ⟨_⟩ (tagPairAtL-adequate zero k (suc a) (suc b) (z ∷ γ)) t) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ arityTagPairAtL c ar k a b ⟩
  bwd q = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate (suc c) (suc ar) zero (zS ∷ γ)))
          (q ∙ cong (pr N) (sym e))
      , subst ⟨_⟩ (sym (tagPairAtL-adequate zero k (suc a) (suc b) (zS ∷ γ))) e ) ∣₁
    where
    zS : S
    zS = prʟ (numeralL k) (prʟ (lookup a γ) (lookup b γ))
    e : fst zS ≡ pr (# k) P
    e = prʟ-fst (numeralL k) (prʟ (lookup a γ) (lookup b γ))
      ∙ cong₂ pr (numeralL-fst k) (prʟ-fst (lookup a γ) (lookup b γ))

arityTagAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Formula S n
arityTagAtL c ar k a =
  ∃̇ (prAtL (suc c) (suc ar) zero ∧̇ tagAtL zero k (suc a))

arityTagAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagAtL c ar k a)
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ)) (pr (# k) (fst (lookup a γ))))
arityTagAtL-adequate c ar k a γ = ⇔toPath fwd bwd
  where
  N = fst (lookup ar γ)
  A = fst (lookup a γ)
  target = PairIs (fst (lookup c γ)) (pr N (pr (# k) A))

  fwd : ⟨ γ ⊨ arityTagAtL c ar k a ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , t)) →
      subst ⟨_⟩ (prAtL-adequate (suc c) (suc ar) zero (z ∷ γ)) p
      ∙ cong (pr N) (subst ⟨_⟩ (tagAtL-adequate zero k (suc a) (z ∷ γ)) t) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ arityTagAtL c ar k a ⟩
  bwd q = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate (suc c) (suc ar) zero (zS ∷ γ)))
          (q ∙ cong (pr N) (sym e))
      , subst ⟨_⟩ (sym (tagAtL-adequate zero k (suc a) (zS ∷ γ))) e ) ∣₁
    where
    zS : S
    zS = prʟ (numeralL k) (lookup a γ)
    e : fst zS ≡ pr (# k) A
    e = prʟ-fst (numeralL k) (lookup a γ) ∙ cong₂ pr (numeralL-fst k) refl
```

<!--en-->
## Looking a subcode up in the table
<!--zh-->
## 在表中查一个子码
<!--/-->

<!--en-->
The frames bind a code's payload but never look the table up at it, because a
payload component may be a term code, at which the table has nothing. A relation
that does want the value must therefore build the key itself: pair the arity with
the component, and read the table there.

That is one existential over the key, and it is the piece four of the twelve
relations are built from. The two that speak of a subformula at the next arity
need the same thing with the arity bumped, which is this with one more layer.
<!--zh-->
诸框架绑定一个码的载荷，却从不在其上查表，因为载荷分量可能是词项码，而表在那里什么也没有。想要取值的关系于是必须自己造那个键：把元数与该分量配成对，再在那里读表。

那是对该键的一个存在量词，也是十二条关系中四条所由构造的部件。谈论下一元数处子公式的那两条，需要的是同一件事而元数加一，即此物再加一层。
<!--/-->

```agda
subValAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
subValAt T ar a y =
  ∃̇ (prAtL zero (suc ar) (suc a) ∧̇ appAt (suc T) zero (suc y))

subValAt-adequate : ∀ {n} (T ar a y : Fin n) (γ : S ^ n)
  → (γ ⊨ subValAt T ar a y)
  ≡ (pr (pr (fst (lookup ar γ)) (fst (lookup a γ))) (fst (lookup y γ))
      ∈ fst (lookup T γ))
subValAt-adequate T ar a y γ = ⇔toPath fwd bwd
  where
  K = pr (fst (lookup ar γ)) (fst (lookup a γ))
  target = pr K (fst (lookup y γ)) ∈ fst (lookup T γ)

  fwd : ⟨ γ ⊨ subValAt T ar a y ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , q)) →
      subst (λ w → ⟨ pr w (fst (lookup y γ)) ∈ fst (lookup T γ) ⟩)
        (subst ⟨_⟩ (prAtL-adequate zero (suc ar) (suc a) (z ∷ γ)) p)
        (subst ⟨_⟩ (appAt-adequate (suc T) zero (suc y) (z ∷ γ)) q) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ subValAt T ar a y ⟩
  bwd h = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate zero (suc ar) (suc a) (zS ∷ γ))) e
      , subst ⟨_⟩ (sym (appAt-adequate (suc T) zero (suc y) (zS ∷ γ)))
          (subst (λ w → ⟨ pr w (fst (lookup y γ)) ∈ fst (lookup T γ) ⟩) (sym e) h) ) ∣₁
    where
    zS : S
    zS = prʟ (lookup ar γ) (lookup a γ)
    e : fst zS ≡ K
    e = prʟ-fst (lookup ar γ) (lookup a γ)
```

<!--en-->
## The shape of a clause
<!--zh-->
## 一条子句的形状
<!--/-->

<!--en-->
A recursion on codes is stated by clauses, and the clauses come in a few shapes
rather than twelve. A binary constructor's clause says: for every code in the
index with this tag over these two subcodes, and for the values the table records
at the three of them, such-and-such holds. All of that is fixed except the
such-and-such, so it is written once with the relation as a parameter, and the
three binary constructors differ only in which relation they hand it.

Five things are bound, in the order a reader meets them: the code, its arity, its
two payload components, and the value the table records at the code. The values
at the payload components are **not** bound, and that is what makes the frame
general. A connective's payload is a pair of formula codes and its
clause does want them, but an atom's payload is a pair of *term* codes, at which
the table has no entries at all, and a bounded quantifier's payload mixes the
two. So the frame binds what every constructor has and leaves the lookups to the
relation, which may perform them freely.

Reading the clause back is one chain of substitutions along the readers'
adequacy, and it is stated in the direction a soundness proof consumes: given a
code of that shape in the index and the three recorded values, the relation
holds.
<!--zh-->
对码的递归由子句陈述，而子句只有几种形状，不是十二种。一个二元构造子的子句说：对索引中每个以此标签架在这两个子码之上的码，以及表在这三者处所记录的取值，某某成立。除了那个「某某」，其余全是固定的，故只写一次，把那条关系留作参数，而三个二元构造子只差交给它的是哪条关系。

被绑定的有五样，按读者遇到的次序：那个码、它的元数、它的两个载荷分量、以及表在该码处记录的取值。诸载荷分量处的取值**不**被绑定，而这正是使该框架通用之处。一个联结词的载荷是一对公式码，它的子句确实要它们；但一个原子的载荷是一对**词项**码，表在那里根本没有条目，而有界量词的载荷则两者混杂。故框架只绑定每个构造子都有的东西，把查表留给那条关系，由它自行执行。

把子句读回来是沿诸读式的适足性作一串代换，而它按可靠性证明所消费的方向陈述：给定索引中一个那种形状的码与三个被记录的取值，那条关系成立。
<!--/-->

```agda
module _ {n : ℕ} where
  private
    sh5 : Fin n → Fin (5 + n)
    sh5 i = suc (suc (suc (suc (suc i))))

    c5 n5 a5 b5 yc5 : Fin (5 + n)
    c5  = suc (suc (suc (suc zero)))
    n5  = suc (suc (suc zero))
    a5  = suc (suc zero)
    b5  = suc zero
    yc5 = zero

  binClauseAt : Fin n → Fin n → ℕ → Formula S (5 + n) → Formula S n
  binClauseAt C T k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ (∀̇ (∀̇
      ( arityTagPairAtL c5 n5 k a5 b5
      ⇒̇ ( appAt (sh5 T) c5 yc5
      ⇒̇ rel ))))))

  binClause-out : (C T : Fin n) (k : ℕ) (rel : Formula S (5 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ binClauseAt C T k rel ⟩
    → (c ar a b yc : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  binClause-out C T k rel γ h c ar a b yc c∈ shape hc =
    h c c∈ ar a b yc
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate c5 n5 k a5 b5 δ)) shape)
      (subst ⟨_⟩ (sym (appAt-adequate (sh5 T) c5 yc5 δ)) hc)
    where
    δ : S ^ (5 + n)
    δ = yc ∷ b ∷ a ∷ ar ∷ c ∷ γ
```

<!--en-->
Counting the shapes is worth a moment, because it says how much of the twelve is
really there, and because counting it wrong is easy: this paragraph has been
wrong twice.

The frames distinguish exactly one thing, whether the payload is a pair or a
single component. The pair frame covers the two atoms, the three connectives and
the two bounded quantifiers, which is seven; the single-component frame covers
negation, the two unbounded quantifiers, **and the two constants**, which is
five, since a constant's payload is a numeral and the frame does not care what a
component is. **Two** frames, then, and twelve relations above them.

What the frames must not distinguish is what the payload components *are*.
Grouping by that gives five kinds of relation, not five frames: term against
term, formula against formula, term against formula, one formula, and one
formula at the next arity. That is where the twelve actually divide, and it
divides them in the relations, where the lookups live.

The single-component frame is the pair frame with one binder fewer, and reads
back the same way.
<!--zh-->
数一数有几种形状是值得的，因为它说出那十二条里真正存在多少，也因为数错很容易：这一段已经错过两次。

诸框架只区分一件事：载荷是一个对，还是单个分量。对框架覆盖两个原子、三个联结词与两个有界量词，共七个；单分量框架覆盖否定、两个无界量词、**以及那两个常量**，共五个，因为常量的载荷是一个数码，而框架并不在意某个分量究竟是什么。故是**两**个框架，其上有十二条关系。

诸框架不可区分的，是那些载荷分量究竟**是什么**。按那个分组得到的是五种关系、而非五个框架：词项对词项、公式对公式、词项对公式、单个公式、以及处于下一元数的单个公式。那才是十二条真正分开的地方，而它们分在诸关系里，也就是查表所在之处。

单分量框架就是少一个绑定的对框架，读回来的方式相同。
<!--/-->

```agda
  private
    sh4 : Fin n → Fin (4 + n)
    sh4 i = suc (suc (suc (suc i)))

    c4 n4 a4 yc4 : Fin (4 + n)
    c4  = suc (suc (suc zero))
    n4  = suc (suc zero)
    a4  = suc zero
    yc4 = zero

  unClauseAt : Fin n → Fin n → ℕ → Formula S (4 + n) → Formula S n
  unClauseAt C T k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ (∀̇
      ( arityTagAtL c4 n4 k a4
      ⇒̇ ( appAt (sh4 T) c4 yc4
      ⇒̇ rel )))))

  unClause-out : (C T : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ unClauseAt C T k rel ⟩
    → (c ar a yc : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  unClause-out C T k rel γ h c ar a yc c∈ shape hc =
    h c c∈ ar a yc
      (subst ⟨_⟩ (sym (arityTagAtL-adequate c4 n4 k a4 δ)) shape)
      (subst ⟨_⟩ (sym (appAt-adequate (sh4 T) c4 yc4 δ)) hc)
    where
    δ : S ^ (4 + n)
    δ = yc ∷ a ∷ ar ∷ c ∷ γ
```

<!--en-->
## The positive connectives
<!--zh-->
## 正的联结词
<!--/-->

<!--en-->
Two of the twelve can be written now, and they are the two that need nothing the
chapter has not got. Conjunction and disjunction relate the value at a code to
the values at its two subcodes by intersection and union, at the same arity, and
that is the whole of their content.

The shared part is a relation that binds the two subvalues and guards them with
the table lookups; the operation is what is left over, and it speaks of the value
at the code and the two subvalues, at positions two, one and zero. So a
propositional clause is one line above the shared part.

Implication and negation want the complement, hence the set of all environments
at the code's arity, which the chapter does not yet name. They wait for it. The
split is not arbitrary: it is exactly the split between the connectives whose
truth is monotone in their parts and those whose truth is not.
<!--zh-->
十二条里有两条现在就能写，而它们正是不需要本章尚未拥有之物的那两条。合取与析取把某码处的取值与它两个子码处的取值以交与并相关联，元数相同，而这就是它们的全部内容。

共用的部分是一条关系，它绑定两个子取值，并以查表为它们设防；剩下的就是那个运算，它谈论该码处的取值与两个子取值，位于位置二、一、零。故一条命题子句在共用部分之上只有一行。

蕴含与否定要补集，因而要该码元数处的全体环境之集，而本章尚未为它命名。它们等着。这处分界并不随意：它恰是「真值随其部分单调」的联结词与「不单调」的联结词之间的分界。
<!--/-->

```agda
module _ {n : ℕ} where
  private
    sh7 : Fin n → Fin (7 + n)
    sh7 i = suc (suc (suc (suc (suc (suc (suc i))))))

  c7 ar7 a7 b7 yc7 ya7 yb7 : Fin (7 + n)
  c7  = suc (suc (suc (suc (suc (suc zero)))))
  ar7 = suc (suc (suc (suc (suc zero))))
  a7  = suc (suc (suc (suc zero)))
  b7  = suc (suc (suc zero))
  yc7 = suc (suc zero)
  ya7 = suc zero
  yb7 = zero

  propRel : Fin n → Formula S (7 + n) → Formula S (5 + n)
  propRel T op =
    ∀̇ (∀̇ ( subValAt (sh7 T) ar7 a7 ya7
         ⇒̇ ( subValAt (sh7 T) ar7 b7 yb7
         ⇒̇ op )))

  propClauseAt : Fin n → Fin n → ℕ → Formula S (7 + n) → Formula S n
  propClauseAt C T k op = binClauseAt C T k (propRel T op)

  propClause-out : (C T : Fin n) (k : ℕ) (op : Formula S (7 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ propClauseAt C T k op ⟩
    → (c ar a b yc ya yb : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (lookup T γ) ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ op ⟩
  propClause-out C T k op γ h c ar a b yc ya yb c∈ shape hc ha hb =
    binClause-out C T k (propRel T op) γ h c ar a b yc c∈ shape hc ya yb
      (subst ⟨_⟩ (sym (subValAt-adequate (sh7 T) ar7 a7 ya7 δ)) ha)
      (subst ⟨_⟩ (sym (subValAt-adequate (sh7 T) ar7 b7 yb7 δ)) hb)
    where
    δ : S ^ (7 + n)
    δ = yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  andClauseAt : Fin n → Fin n → Formula S n
  andClauseAt C T = propClauseAt C T 2 (interAt yc7 ya7 yb7)

  orClauseAt : Fin n → Fin n → Formula S n
  orClauseAt C T = propClauseAt C T 3 (unionAt yc7 ya7 yb7)
```

<!--en-->
## The negative connectives
<!--zh-->
## 负的联结词
<!--/-->

<!--en-->
Negation wants the complement, so it wants the set of all environments at the
code's arity, and the arity is a variable the frame bound. So the ambient set is
a variable too, constrained by saying what its members are, which is the
extension frame applied to the environment predicate. One line, and no new
machinery: what looked like an obligation to construct a set is, inside a clause,
an obligation to describe one.

That the set exists is a different matter and belongs to the chapter that builds
a table rather than the one that says what a table is. The clause only has to
say, of whatever the table records, that it stands in the right relation to the
ambient set; the construction has to produce an ambient set standing there.
<!--zh-->
否定要补集，故它要该码元数处的全体环境之集，而那个元数是框架绑定的一个变元。于是那个周遭集合也是一个变元，由「说出它的成员是什么」来约束，而那正是外延框架施于环境谓词。一行，无须新机件：看似「造出一个集合」的义务，在子句之内是「描述一个集合」的义务。

那个集合确实存在，是另一回事，属于「造出一张表」的那一章，而非「说清什么是一张表」的这一章。子句只须说：无论表记录了什么，它与那个周遭集合处于正确的关系；而构造则须拿出一个真的处在那里的周遭集合。
<!--/-->

```agda
envSetAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envSetAt E ar B = extAt E (envOverAt zero (suc ar) (suc B))

module _ {n : ℕ} where
  private
    sh6 : Fin n → Fin (6 + n)
    sh6 i = suc (suc (suc (suc (suc (suc i)))))

    c6 ar6 a6 yc6 ya6 E6 : Fin (6 + n)
    c6  = suc (suc (suc (suc (suc zero))))
    ar6 = suc (suc (suc (suc zero)))
    a6  = suc (suc (suc zero))
    yc6 = suc (suc zero)
    ya6 = suc zero
    E6  = zero

    negRel : Fin n → Fin n → Formula S (4 + n)
    negRel T B =
      ∀̇ (∀̇ ( subValAt (sh6 T) ar6 a6 ya6
           ⇒̇ ( envSetAt E6 ar6 (sh6 B)
           ⇒̇ diffAt yc6 E6 ya6 )))

  negClauseAt : Fin n → Fin n → Fin n → Formula S n
  negClauseAt C T B = unClauseAt C T 5 (negRel T B)

  negClause-out : (C T B : Fin n) (γ : S ^ n)
    → ⟨ γ ⊨ negClauseAt C T B ⟩
    → (c ar a yc ya E : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E6 ar6 (sh6 B) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ diffAt yc6 E6 ya6 ⟩
  negClause-out C T B γ h c ar a yc ya E c∈ shape hc ha hE =
    unClause-out C T 5 (negRel T B) γ h c ar a yc c∈ shape hc ya E
      (subst ⟨_⟩ (sym (subValAt-adequate (sh6 T) ar6 a6 ya6 δ)) ha) hE
    where
    δ : S ^ (6 + n)
    δ = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ
```

<!--en-->
## Implication, and the two constants
<!--zh-->
## 蕴含，与两个常量
<!--/-->

<!--en-->
Implication is the complement of the antecedent joined with the consequent, so it
wants both subvalues, the ambient set, and one temporary to hold the difference:
four bound values above the frame's five, and the longest relation of the twelve.
Nothing in it is new.

The constants are the shortest. Truth at an arity is the whole ambient set, and
falsity is empty, so one binds the ambient set and the other binds nothing. They
go through the single-component frame, since a constant's payload is a numeral
and the frame does not look at what a component is; their relations simply ignore
it.
<!--zh-->
蕴含是前件的补集与后件的并，故它要两个子取值、那个周遭集合、以及一个存放差集的临时变元：在框架的五个之上再绑四个取值，是十二条中最长的一条关系。其中没有任何新东西。

两个常量最短。某元数处的「真」就是整个周遭集合，而「假」为空，故一个绑定那个周遭集合，另一个什么也不绑。它们走单分量框架，因为常量的载荷是一个数码，而框架并不看某个分量是什么；它们的关系径直忽略它。
<!--/-->

```agda
module _ {n : ℕ} where
  private
    sh9 : Fin n → Fin (9 + n)
    sh9 i = suc (suc (suc (suc (suc (suc (suc (suc (suc i))))))))

    ar9 a9 b9 yc9 ya9 yb9 E9 d9 : Fin (9 + n)
    ar9 = suc (suc (suc (suc (suc (suc (suc zero))))))
    a9  = suc (suc (suc (suc (suc (suc zero)))))
    b9  = suc (suc (suc (suc (suc zero))))
    yc9 = suc (suc (suc (suc zero)))
    ya9 = suc (suc (suc zero))
    yb9 = suc (suc zero)
    E9  = suc zero
    d9  = zero

    impRel : Fin n → Fin n → Formula S (5 + n)
    impRel T B =
      ∀̇ (∀̇ (∀̇ (∀̇ ( subValAt (sh9 T) ar9 a9 ya9
                 ⇒̇ ( subValAt (sh9 T) ar9 b9 yb9
                 ⇒̇ ( envSetAt E9 ar9 (sh9 B)
                 ⇒̇ ( diffAt d9 E9 ya9
                 ⇒̇ unionAt yc9 d9 yb9 )))))))

    sh5 : Fin n → Fin (5 + n)
    sh5 i = suc (suc (suc (suc (suc i))))

    ar5 yc5 E5 : Fin (5 + n)
    ar5 = suc (suc (suc zero))
    yc5 = suc zero
    E5  = zero

    topRel : Fin n → Formula S (4 + n)
    topRel B = ∀̇ ( envSetAt E5 ar5 (sh5 B) ⇒̇ sameAt yc5 E5 )

  impClauseAt : Fin n → Fin n → Fin n → Formula S n
  impClauseAt C T B = binClauseAt C T 4 (impRel T B)

  topClauseAt : Fin n → Fin n → Fin n → Formula S n
  topClauseAt C T B = unClauseAt C T 6 (topRel B)

  botClauseAt : Fin n → Fin n → Formula S n
  botClauseAt C T = unClauseAt C T 7 (emptyAt zero)
```

<!--en-->
## The next arity
<!--zh-->
## 下一个元数
<!--/-->

<!--en-->
Four of the twelve bind a variable, so their subformula sits one arity higher and
the table has to be consulted there. The successor reader is already written on
the hierarchy side and names no constants, so it crosses by quoting, and the
lookup at the next arity is the lookup at a fresh arity constrained to be the
successor of the one the frame bound.

The backward direction needs the successor as an element of the model, and the
numeral chapter supplies it: the model's own successor, read through the
underlying set, is the hierarchy's.
<!--zh-->
十二条里有四条绑定一个变元，故它们的子公式高出一个元数，而表必须在那里被查询。后继读式在层级一侧已经写好，且不点名常元，故它经引用过河；而「下一元数处的查表」，就是「在一个新元数处的查表」加上「该元数是框架所绑元数的后继」这条约束。

反向需要那个后继作为模型的元素，而数码那一章供给它：模型自己的后继，沿底层集合读出来，就是层级的后继。
<!--/-->

```agda
sucAtL : ∀ {n} → Fin n → Fin n → Formula S n
sucAtL i j = liftFo (sucAt i j) _

sucAtL-adequate : ∀ {n} (i j : Fin n) (γ : S ^ n)
  → (γ ⊨ sucAtL i j) ≡ PairIs (fst (lookup j γ)) (sucV (fst (lookup i γ)))
sucAtL-adequate i j γ =
    transferFo (sucAt i j) _ (Δ₀-sucAt i j) γ
  ∙ sucAt-adequate i j (map fst γ)
  ∙ cong₂ PairIs (lookup-fst j γ) (cong sucV (lookup-fst i γ))

subValSuccAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
subValSuccAt T ar a y =
  ∃̇ (sucAtL (suc ar) zero ∧̇ subValAt (suc T) zero (suc a) (suc y))

subValSuccAt-adequate : ∀ {n} (T ar a y : Fin n) (γ : S ^ n)
  → (γ ⊨ subValSuccAt T ar a y)
  ≡ (pr (pr (sucV (fst (lookup ar γ))) (fst (lookup a γ))) (fst (lookup y γ))
      ∈ fst (lookup T γ))
subValSuccAt-adequate T ar a y γ = ⇔toPath fwd bwd
  where
  key : V ℓ → V ℓ
  key w = pr (pr w (fst (lookup a γ))) (fst (lookup y γ))
  target = key (sucV (fst (lookup ar γ))) ∈ fst (lookup T γ)

  fwd : ⟨ γ ⊨ subValSuccAt T ar a y ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (sz , v)) →
      subst (λ w → ⟨ key w ∈ fst (lookup T γ) ⟩)
        (subst ⟨_⟩ (sucAtL-adequate (suc ar) zero (z ∷ γ)) sz)
        (subst ⟨_⟩ (subValAt-adequate (suc T) zero (suc a) (suc y) (z ∷ γ)) v) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ subValSuccAt T ar a y ⟩
  bwd h = ∣ zS
    , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc ar) zero (zS ∷ γ))) e
      , subst ⟨_⟩ (sym (subValAt-adequate (suc T) zero (suc a) (suc y) (zS ∷ γ)))
          (subst (λ w → ⟨ key w ∈ fst (lookup T γ) ⟩) (sym e) h) ) ∣₁
    where
    zS : S
    zS = sucʟ (lookup ar γ)
    e : fst zS ≡ sucV (fst (lookup ar γ))
    e = sucʟ-fst (lookup ar γ)
```

<!--en-->
## Extending an environment
<!--zh-->
## 扩展一个环境
<!--/-->

<!--en-->
The other half of a quantifier clause: the environment the subformula is
evaluated in is the one at hand with a value pushed on the front. That reader is
already written on the hierarchy side, and its meaning there is stated against a
meta-level family, which is exactly the form a soundness proof will want. So it
is worth quoting rather than rewriting, even though quoting is not free here: it
names a numeral as a hierarchy constant, so the bridge asks for that numeral's
constructibility at every place the shape mentions it.

Those places are written out once, per reader, and then the whole extension
reader's admissibility is three of them. The numeral's own constructibility comes
from the numeral chapter, which is why it sits here rather than with the codes.
<!--zh-->
量词子句的另一半：子公式所在的环境，就是手上这个环境前面推入一个取值。那条读式在层级一侧已经写好，而它在那边的含义是按元层的族陈述的，恰是可靠性证明将要的形式。故它值得引用而非重写，尽管此处引用并不免费：它把一个数码点名为层级的常元，于是桥会在形状提到它的每一处索取该数码的可构造性。

那些位置逐条读式写一次，随后整条扩展读式的合格性就是其中三次。数码自身的可构造性来自数码那一章，这也是它住在此处而非与诸码同处的原因。
<!--/-->

```agda
numL : (k : ℕ) → InL (# k)
numL k = subst (λ w → ⟨ isL w ⟩) (numeralL-fst k) (numeralL k .snd)

private
  bddSglCon : ∀ {n} (k : Fin n) (j : ℕ) → BoundedFo InL (sglConAt k (# j))
  bddSglCon k j = (numL j , _) , (_ , (_ , numL j))

  bddPairCon : ∀ {n} (k : Fin n) (j : ℕ) (x : Fin n)
             → BoundedFo InL (pairConAt k (# j) x)
  bddPairCon k j x = (numL j , _) , ((_ , _) , (_ , ((_ , numL j) , (_ , _))))

  bddTag : ∀ {n} (s : Fin n) (j : ℕ) (x : Fin n) → BoundedFo InL (tagAt s j x)
  bddTag {n} s j x =
      (_ , bddSglCon {suc n} zero j)
    , ( (_ , bddPairCon {suc n} zero j (suc x))
      , (_ , (bddSglCon {suc n} zero j , bddPairCon {suc n} zero j (suc x))) )

  bddShift : ∀ {n} (p' p : Fin n) → BoundedFo InL (shiftPairAt p' p)
  bddShift p' p = _

  bddCons : ∀ {n} (e' m e : Fin n) → BoundedFo InL (consAt e' m e)
  bddCons {n} e' m e =
      (_ , bddTag {suc n} zero 0 (suc m))
    , ( (_ , (_ , bddShift {suc (suc n)} zero (suc zero)))
      , (_ , ( bddTag {suc n} zero 0 (suc m)
             , (_ , bddShift {suc (suc n)} (suc zero) zero) )) )

consAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
consAtL e' m e = liftFo (consAt e' m e) (bddCons e' m e)

consAtL-adequate : ∀ {n} (e' m e : Fin n) (γ : S ^ n)
  {k : ℕ} (g : Fin k → V ℓ)
  → fst (lookup e γ) ≡ env g
  → (γ ⊨ consAtL e' m e)
  ≡ PairIs (fst (lookup e' γ)) (env (cons (fst (lookup m γ)) g))
consAtL-adequate e' m e γ g hE =
    transferFo (consAt e' m e) (bddCons e' m e) (Δ₀-consAt e' m e) γ
  ∙ consAt-adequate e' m e (map fst γ) g
      (lookup-fst e γ ∙ hE)
  ∙ cong₂ PairIs (lookup-fst e' γ)
      (cong (λ w → env (cons w g)) (lookup-fst m γ))
```

<!--en-->
## The unbounded quantifiers
<!--zh-->
## 无界量词
<!--/-->

<!--en-->
An environment satisfies an existential exactly when some value from the
structure, pushed onto the front, gives an environment satisfying the body, and
the body's value is recorded one arity higher. So the clause binds the value at
the next arity, binds the ambient set at its own arity, and then describes its
own value by extension: the environments in the ambient set that can be extended
into the body's.

Nine things are in scope by the innermost point, which is the deepest the chapter
goes, and every one of them was needed: the code and its parts from the frame,
the two values, the environment being classified, the value pushed on, and the
extended environment. The universal clause turns the two innermost quantifiers
around, each taking the connective its form asks for: a conjunction under the
existential, an implication under the universal.

Nothing else moves, and the outermost conjunct in particular does not. The one
that puts the environment in the ambient set is a conjunction in **both**, as it
is in every clause written in this frame, and the reason is worth stating because
getting it wrong is not a wrong clause but an unsatisfiable one. `extAt`{.Agda}
makes a value the set of exactly what its condition holds of; a condition that
could hold outside the ambient set would be asking for a value that is not a set.
<!--zh-->
一个环境满足存在量词，恰当结构中的某个取值被推到它前面后，所得的环境满足主体，而主体的取值记录在高一个元数处。故该子句绑定下一元数处的取值，绑定它自己元数处的周遭集合，然后以外延描述自己的取值：周遭集合中那些能被扩展进主体取值里的环境。

到最内处共有九样在作用域中，那是本章所及的最深处，而每一样都是必需的：来自框架的那个码与它的诸部分、两个取值、被分类的那个环境、被推入的取值、以及扩展后的环境。全称子句把最内两个量词调转，每个都带上其形式所要的联结词：存在之下是合取，全称之下是蕴含。

除此之外别无变动，尤其是最外那个合取项不动。把环境放进周遭集合的那一项，在**两条**里都是合取，一如这个框架下写出的每一条子句；而这个理由值得说出来，因为弄错它得到的不是一条错的子句，而是一条无法满足的子句。`extAt`{.Agda} 使一个取值恰为「其条件所成立于的那些东西」之集；一个可能在周遭集合之外成立的条件，等于在索要一个并非集合的取值。
<!--/-->

```agda
module _ {n : ℕ} where
  private
    sh6' : Fin n → Fin (6 + n)
    sh6' i = suc (suc (suc (suc (suc (suc i)))))

    sh7' : Fin n → Fin (7 + n)
    sh7' i = suc (suc (suc (suc (suc (suc (suc i))))))

    ar6' a6' yc6' ya6' E6' : Fin (6 + n)
    ar6' = suc (suc (suc (suc zero)))
    a6'  = suc (suc (suc zero))
    yc6' = suc (suc zero)
    ya6' = suc zero
    E6'  = zero

    -- at the innermost point: e' = 0, m = 1, e = 2, E = 3, ya = 4
    body∃ body∀ : Fin n → Formula S (7 + n)
    body∃ B = (var zero ∈̇ var (suc zero))
            ∧̇ ∃̇∈ (var (sh7' B)) (∃̇
                ( consAtL zero (suc zero) (suc (suc zero))
                ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ))
    body∀ B = (var zero ∈̇ var (suc zero))
            ∧̇ ∀̇∈ (var (sh7' B)) (∀̇
                ( consAtL zero (suc zero) (suc (suc zero))
                ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ))

    quantRel : Fin n → Fin n → Formula S (7 + n) → Formula S (4 + n)
    quantRel T B body =
      ∀̇ (∀̇ ( subValSuccAt (sh6' T) ar6' a6' ya6'
           ⇒̇ ( envSetAt E6' ar6' (sh6' B)
           ⇒̇ extAt yc6' body )))

  existClauseAt : Fin n → Fin n → Fin n → Formula S n
  existClauseAt C T B = unClauseAt C T 8 (quantRel T B (body∃ B))

  forallClauseAt : Fin n → Fin n → Fin n → Formula S n
  forallClauseAt C T B = unClauseAt C T 9 (quantRel T B (body∀ B))
```

<!--en-->
## Evaluating a term, and the atoms
<!--zh-->
## 求一个词项的值，与两个原子
<!--/-->

<!--en-->
The last thing the chapter lacked. A term of a parameter-free formula is a
variable, so its code is the variable tag over a key, and its value in an
environment is what the environment records at that key. One existential over the
key, and the two readers already written do the rest.

The atoms then read both sides and compare them. Their payload is a pair of
*term* codes, at which the table has nothing, which is why the frame was made not
to look there; here is where that pays. The two atoms differ in one atom of the
object language, membership against equality, so they share everything else.
<!--zh-->
本章尚缺的最后一件。无参公式的一个词项是变元，故它的码是「变元标签架在一个键之上」，而它在某环境中的取值就是该环境在那个键处记录的东西。对该键作一个存在量词，其余由已写好的两条读式完成。

两个原子随后读出两侧并加以比较。它们的载荷是一对**词项**码，而表在那里什么也没有，这正是当初把框架做成不往那里看的原因；此处便是它的回报。两个原子只差对象语言的一个原子，隶属对相等，其余全部共享。
<!--/-->

```agda
tmValAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
tmValAt t e v = ∃̇ (tagAtL (suc t) 1 zero ∧̇ appAt (suc e) zero (suc v))

module _ {n : ℕ} where
  private
    sh6″ : Fin n → Fin (6 + n)
    sh6″ i = suc (suc (suc (suc (suc (suc i)))))

    ar6″ yc6″ E6″ : Fin (6 + n)
    ar6″ = suc (suc (suc (suc zero)))
    yc6″ = suc zero
    E6″  = zero

    -- at the innermost point: w = 0, v = 1, e = 2, E = 3, yc = 4, b = 5, a = 6
    a9″ b9″ e9″ v9″ w9″ : Fin (9 + n)
    a9″ = suc (suc (suc (suc (suc (suc zero)))))
    b9″ = suc (suc (suc (suc (suc zero))))
    e9″ = suc (suc zero)
    v9″ = suc zero
    w9″ = zero

    atomBody : Formula S (9 + n) → Formula S (7 + n)
    atomBody cmp =
      (var zero ∈̇ var (suc zero))
      ∧̇ ∃̇ (∃̇ ( tmValAt a9″ e9″ v9″
             ∧̇ ( tmValAt b9″ e9″ w9″
             ∧̇ cmp )))

    atomRel : Fin n → Formula S (9 + n) → Formula S (5 + n)
    atomRel B cmp =
      ∀̇ ( envSetAt E6″ ar6″ (sh6″ B) ⇒̇ extAt yc6″ (atomBody cmp) )

  memClauseAt : Fin n → Fin n → Fin n → Formula S n
  memClauseAt C T B = binClauseAt C T 0 (atomRel B (var v9″ ∈̇ var w9″))

  eqClauseAt : Fin n → Fin n → Fin n → Formula S n
  eqClauseAt C T B = binClauseAt C T 1 (atomRel B (var v9″ ≐ var w9″))
```

<!--en-->
## The bounded quantifiers
<!--zh-->
## 有界量词
<!--/-->

<!--en-->
The last two, and they need nothing new. A bounded quantifier's payload is a term
code paired with a formula code, so the bound is evaluated in the environment and
the body's value is read one arity higher; then the values from the bound are
pushed on and the extended environments are looked for in the body's value.

Every piece has appeared: the next-arity lookup for the body, the ambient set for
the extension frame, term evaluation for the bound, and environment extension for
the step. The two differ, as the unbounded pair did, only in which quantifier
each of the three innermost binders carries.
<!--zh-->
最后两条，而它们不需要任何新东西。有界量词的载荷是「词项码与公式码之对」，故那个界在环境中求值，而主体的取值高一个元数读出；随后把来自界的诸取值推入，并到主体的取值里去找扩展后的环境。

每一件都已登场：主体所需的下一元数查表、外延框架所需的周遭集合、界所需的词项求值、以及推入所需的环境扩展。两条之间的差别，与无界的那一对一样，只在最内三个绑定各自带的是哪个量词。
<!--/-->

```agda
module _ {n : ℕ} where
  private
    sh7B : Fin n → Fin (7 + n)
    sh7B i = suc (suc (suc (suc (suc (suc (suc i))))))

    -- at depth 7: E = 0, yb = 1, yc = 2, b = 3, a = 4, ar = 5, c = 6
    ar7B b7B yc7B yb7B E7B : Fin (7 + n)
    ar7B = suc (suc (suc (suc (suc zero))))
    b7B  = suc (suc (suc zero))
    yc7B = suc (suc zero)
    yb7B = suc zero
    E7B  = zero

    -- at depth 9: w = 0, e = 1, a = 6
    a9B e9B w9B : Fin (9 + n)
    a9B = suc (suc (suc (suc (suc (suc zero)))))
    e9B = suc zero
    w9B = zero

    -- at depth 11: e' = 0, m = 1, e = 3, yb = 5
    e'11 m11 e11 yb11 : Fin (11 + n)
    e'11 = zero
    m11  = suc zero
    e11  = suc (suc (suc zero))
    yb11 = suc (suc (suc (suc (suc zero))))

    bodyAll bodyEx : Formula S (8 + n)
    bodyAll = (var zero ∈̇ var (suc zero))
            ∧̇ ∀̇ ( tmValAt a9B e9B w9B
                ⇒̇ ∀̇∈ (var zero) (∀̇
                    ( consAtL e'11 m11 e11
                    ⇒̇ (var e'11 ∈̇ var yb11) )))
    bodyEx  = (var zero ∈̇ var (suc zero))
            ∧̇ ∃̇ ( tmValAt a9B e9B w9B
                ∧̇ ∃̇∈ (var zero) (∃̇
                    ( consAtL e'11 m11 e11
                    ∧̇ (var e'11 ∈̇ var yb11) )))

    bndRel : Fin n → Fin n → Formula S (8 + n) → Formula S (5 + n)
    bndRel T B body =
      ∀̇ (∀̇ ( subValSuccAt (sh7B T) ar7B b7B yb7B
           ⇒̇ ( envSetAt E7B ar7B (sh7B B)
           ⇒̇ extAt yc7B body )))

  allInClauseAt : Fin n → Fin n → Fin n → Formula S n
  allInClauseAt C T B = binClauseAt C T 10 (bndRel T B bodyAll)

  exInClauseAt : Fin n → Fin n → Fin n → Formula S n
  exInClauseAt C T B = binClauseAt C T 11 (bndRel T B bodyEx)
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
is written through them. `prʟ`{.Agda} is the pair on the value side, so a
construction can build a code as well as read one; and `tagAtL`{.Agda} and
`tagPairAtL`{.Agda} read a code's constructor, the second matching the shape
every binary constructor's code has. `envOverAt`{.Agda} then says what it is to
be an environment over a set.

`extAt`{.Agda} is the frame every set-valued clause is written in, the set
operations are its shortest instances, and the recursion's clauses are written in
**two** frames rather than twelve clauses: `binClauseAt`{.Agda} for the seven
constructors whose payload is a pair, `unClauseAt`{.Agda} for the five whose
payload is a single component, the constants included. Both read the key in two
layers, arity outside and tag within, and both leave every lookup on a payload
component to the relation handed to them, which performs it with
`subValAt`{.Agda}. **All twelve** are written out: the four
connectives, the two constants, the two atoms, and the four quantifiers. Two
frames, twelve relations, and five idioms among the relations. `envSetAt`{.Agda} is what the negative ones
needed, and it makes the point the chapter turns on: inside a clause, the ambient
set of environments is described rather than constructed.

Two roads were used and both belong here. A reader with no constants is quoted,
which costs a four-link chain and no thought. A reader naming a numeral is
written instead, because quoting it would thread a constructibility witness
through the whole shape of the formula while writing it needs one unbounded
existential, and unbounded is free. It was
obtained by quoting, not by re-proving: the reader and its characterization stay
where they were written, and the crossing cost one induction on environments.

That is the pattern for every reader that follows, and it is the reason the
coding chapters did not have to be re-based. What it does not cover is any
predicate that is not Δ₀, and those are to be written directly over the model
instead, since nothing in the model's comprehension asks them to be bounded.
<!--zh-->
`prAtL`{.Agda} 在模型的对象语言里说「这个集合是那两个的有序对」，`appAt`{.Agda} 说「某函数含有某个给定的对」，`svAt`{.Agda} 说「每个自变量至多含一个对」，而 `domAt`{.Agda} 说「某个给定集合恰是它作答的那些自变量」。它们合起来就是对象语言里「函数」的含义，而此后每条递归的图都经它们写出。`prʟ`{.Agda} 是取值一侧的对，使一个构造既能读码也能造码；而 `tagAtL`{.Agda} 与 `tagPairAtL`{.Agda} 读出一个码的构造子，后者匹配每个二元构造子的码所具有的形状。`envOverAt`{.Agda} 随后说出「作为某集合之上的环境」是什么意思。

`extAt`{.Agda} 是每条集值子句的写作框架，诸集合运算是它最短的实例，而这次递归的诸子句由**两**个框架写出、而非十二条：`binClauseAt`{.Agda} 管载荷为一个对的那七个构造子，`unClauseAt`{.Agda} 管载荷为单个分量的那五个，两个常量包含在内。两者都分两层读那个键，元数在外、标签在内，而两者都把载荷分量上的每一次查表留给交给自己的那条关系，由后者以 `subValAt`{.Agda} 执行。**十二条全部**写出：四个联结词、两个常量、两个原子，以及四个量词。两个框架、十二条关系，而诸关系之中有五种写法。`envSetAt`{.Agda} 正是负的那几条所需的那件，而它道出本章的关节：在子句之内，周遭的环境集合是被描述的，而非被构造的。

用了两条路，而两条都该在此处。无常元的读式被引用，代价是一条四环的链，不必动脑。点名数码的读式则改为直接写，因为引用它要把一份可构造性证书沿公式整个形状穿行，而直接写只需一个无界存在，且无界是免费的。它由引用得来，而非重新证得：读式与它的刻画留在写下它们的地方，而这次过河只花了一次关于环境的归纳。

这就是此后每条读式的套路，也是编码诸章无须换底的原因。它不覆盖的是任何非 Δ₀ 的谓词，那些应当直接在模型上写，因为模型的概括不要求它们有界。
<!--/-->
