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
open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∀̇_; ∀̇∈; ∃̇_; ∃̇∈ )
open import FOL.Manipulation.Mapping using ( mapTm; mapFo )
import FOL.Absoluteness
import FOL.Coding
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; module VCode )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Absoluteness {ℓ} using ( liftFo; transferFo )
open import L.Coding.Base {ℓ}
  using ( prAt; Δ₀-prAt; prAt-adequate; ∈pair-introL; ∈pair-introR )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⁅_,_⁆ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ ; ⟦_⟧ᵐ to ⟦_⟧ )
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
every use of one asks is whether a given pair belongs to it. The function can be
given by any term. The common reader is a bounded existential over that term,
with the pair reader inside, and its meaning is membership of the Kuratowski
pair. The public forms below specialize it to a variable and a constant.

The backward direction is where the model earns its keep, and it is worth
noticing. To satisfy the existential one must produce an *element of the model*
whose underlying set is the pair; the hypothesis only supplies a set. It is
constructible because it belongs to something constructible, and the class is
transitive. That is the whole argument, and the same step will recur wherever a
witness has to be produced inside the model rather than merely in the hierarchy.
<!--zh-->
对象语言里的函数是有序对之集，故凡用到函数的地方，所问的唯一一件事就是某个给定的对是否属于它。函数可由任意词项给出。共用的读式是在该词项上的一个有界存在，里面装着对读式，而其含义是那个 Kuratowski 对的隶属关系。下文两个公开形式分别把它特化到变元与常量。

反向是模型出力之处，值得留意。要满足那个存在量词，必须拿出一个**模型的元素**，其底集是那个对；而假设只给了一个集合。它可构造，因为它属于某个可构造之物，而这个类传递。全部论证仅此而已，而同一步将在此后每个「见证必须造在模型之内、而非仅在层级之内」的地方重现。
<!--/-->

```agda
private
  appTerm : ∀ {n} → Term S n → Fin n → Fin n → Formula S n
  appTerm F x y = ∃̇∈ F (prAtL zero (suc x) (suc y))

  appTerm-adequate : ∀ {n} (F : Term S n) (x y : Fin n) (γ : S ^ n)
    → (γ ⊨ appTerm F x y)
    ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (⟦ F ⟧ γ))
  appTerm-adequate F x y γ = ⇔toPath fwd bwd
    where
    a = fst (lookup x γ)
    b = fst (lookup y γ)
    G = ⟦ F ⟧ γ

    read : (z : S) → ⟨ (z ∷ γ) ⊨ prAtL zero (suc x) (suc y) ⟩ → fst z ≡ pr a b
    read z h = subst ⟨_⟩ (prAtL-adequate zero (suc x) (suc y) (z ∷ γ)) h

    fwd : ⟨ γ ⊨ appTerm F x y ⟩ → ⟨ pr a b ∈ fst G ⟩
    fwd = PT.rec (snd (pr a b ∈ fst G))
      (λ { (z , (z∈G , h)) → subst (λ w → ⟨ w ∈ fst G ⟩) (read z h) z∈G })

    bwd : ⟨ pr a b ∈ fst G ⟩ → ⟨ γ ⊨ appTerm F x y ⟩
    bwd h = ∣ zS , (h , subst ⟨_⟩
        (sym (prAtL-adequate zero (suc x) (suc y) (zS ∷ γ))) refl) ∣₁
      where
      zS : S
      zS = pr a b , isL-trans {x = fst G} {y = pr a b} h (G .snd)

appAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
appAt f = appTerm (var f)

appAt-adequate : ∀ {n} (f x y : Fin n) (γ : S ^ n)
  → (γ ⊨ appAt f x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ))
appAt-adequate f = appTerm-adequate (var f)
```

The same reader with the function held as a CONSTANT rather than in a slot.
`L.InjChain` and `L.Choice.Before` each wrote this out; it belongs beside
`appAt`.

```agda
appC : ∀ {n} → S → Fin n → Fin n → Formula S n
appC F = appTerm (con F)

appC-adequate : ∀ {n} (F : S) (x y : Fin n) (γ : S ^ n)
  → (γ ⊨ appC F x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst F)
appC-adequate F = appTerm-adequate (con F)
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

那两条都是消去，而名字没有说出这一点：`domAt-in`{.Agda} 朝「有条目」拆，`domAt-out`{.Agda} 朝「在定义域中」拆。引入 (那才是「必须**满足**这句陈述」的一张表所要的) 来得晚，于是取了第三个名字，而没有占用它们中的任何一个。
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

  domAt-intro : ((x : S)
                 → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
                    → ⟨ fst x ∈ fst (lookup d γ) ⟩)
                 × (⟨ fst x ∈ fst (lookup d γ) ⟩
                    → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩))
              → ⟨ γ ⊨ domAt f d ⟩
  domAt-intro g x = (λ h → g x .fst (subst ⟨_⟩ (step x) h))
                  , (λ m → subst ⟨_⟩ (sym (step x)) (g x .snd m))
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
## The coding, at the model
<!--zh-->
## 编码，在模型处
<!--/-->

<!--en-->
The pair and the numerals are injective, which is everything the coding chapter
asks of a structure, so the object language codes into `L` itself. Two things
follow and both are wanted. A code is an element of the model **by
construction**, with no constructibility certificate to carry or to prove. And
the code equation is injective at this arity, by the chapter's own theorem, which
is what a table indexed by codes needs: two occurrences of different subformulas
must not share a key, or the table is multi-valued and its existence fails.

The bridge says the two codings agree: reading a code of the model through the
underlying set gives the hierarchy's code of the relabelled formula. Ten
clauses and two, each one tag equation over the clause below it. It is what lets
the readers of this chapter, which are written on the hierarchy side, be applied
to codes built on the model side.
<!--zh-->
对与诸数码是单射的，而这就是编码那一章向一个结构索取的全部，故对象语言可以编码进 `L` 自身。由此得到两件事，而两件都是想要的。一个码**按构造**就是模型的元素，没有可构造性证书要扛、也没有要证。而码等式在该元数处是单射的，由那一章自己的定理给出，而这正是「以码为索引的表」所需要的：两处不同子公式的出现不可共用一个键，否则表就多值，而它的存在性会垮。

那座桥说两套编码一致：把模型的一个码沿底层集合读出来，得到的是层级为那条换名后的公式所给的码。十条子句加两条，每条都是「架在下面那条之上」的一条标签等式。正是它使本章那些写在层级一侧的读式，能施于造在模型一侧的诸码。
<!--/-->

```agda
prʟ-inj : {a b c d : S} → prʟ a b ≡ prʟ c d → (a ≡ c) × (b ≡ d)
prʟ-inj {a} {b} {c} {d} e =
    Σ≡Prop (λ v → snd (isL v)) (pr-inj q .fst)
  , Σ≡Prop (λ v → snd (isL v)) (pr-inj q .snd)
  where
  q : pr (fst a) (fst b) ≡ pr (fst c) (fst d)
  q = sym (prʟ-fst a b) ∙ cong fst e ∙ prʟ-fst c d

numeralL-inj : {j k : ℕ} → numeralL j ≡ numeralL k → j ≡ k
numeralL-inj {j} {k} e =
  #-inj′ (sym (numeralL-fst j) ∙ cong fst e ∙ numeralL-fst k)

module LCode = FOL.Coding {ℓ-suc ℓ} 𝒮ʟ prʟ prʟ-inj numeralL numeralL-inj

tagBridge : (k : ℕ) (x : S) → fst (LCode.mkTag k x) ≡ VCode.mkTag k (fst x)
tagBridge k x = prʟ-fst (numeralL k) x ∙ cong₂ pr (numeralL-fst k) refl

codeBridgeTm : ∀ {n} (t : Term S n) → fst LCode.⌜ t ⌝ᵗ ≡ VCode.⌜ mapTm fst t ⌝ᵗ
codeBridgeTm (con c) = tagBridge 0 c
codeBridgeTm (var i) =
  tagBridge 1 (numeralL (toℕ i)) ∙ cong (VCode.mkTag 1) (numeralL-fst (toℕ i))

codeBridge : ∀ {n} (φ : Formula S n) → fst LCode.⌜ φ ⌝ ≡ VCode.⌜ mapFo fst φ ⌝
codeBridge (t ∈̇ u) = tagBridge 0 _ ∙ cong (VCode.mkTag 0)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridgeTm u))
codeBridge (t ≐ u) = tagBridge 1 _ ∙ cong (VCode.mkTag 1)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridgeTm u))
codeBridge (a ∧̇ b) = tagBridge 2 _ ∙ cong (VCode.mkTag 2)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge (a ∨̇ b) = tagBridge 3 _ ∙ cong (VCode.mkTag 3)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge (a ⇒̇ b) = tagBridge 4 _ ∙ cong (VCode.mkTag 4)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge ⊥̇       = tagBridge 5 _ ∙ cong (VCode.mkTag 5) (numeralL-fst 0)
codeBridge (∃̇ a)   = tagBridge 6 _ ∙ cong (VCode.mkTag 6) (codeBridge a)
codeBridge (∀̇ a)   = tagBridge 7 _ ∙ cong (VCode.mkTag 7) (codeBridge a)
codeBridge (∀̇∈ t a) = tagBridge 8 _ ∙ cong (VCode.mkTag 8)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridge a))
codeBridge (∃̇∈ t a) = tagBridge 9 _ ∙ cong (VCode.mkTag 9)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridge a))

```

<!--en-->
## Environments
<!--zh-->
## 环境
<!--/-->

<!--en-->
An environment is a function whose values lie in a given set, so an environment
over a set is the conjunction of four things: single-valued, with the given
domain, with values where they belong, and *made of pairs*.

The fourth is easy to leave out and fatal to leave out. The other three all speak
about the pairs in a set and say nothing whatever about a member that is not one,
so without it a set could carry any amount of junk and still qualify. That costs
nothing where the predicate is only tested, but the frame that describes a set by
its members asserts both directions, so a value satisfying it would have to
contain every such junk-bearing set: a proper class, and a hypothesis no set can
discharge. The conjunct pins each member to a pair of an index and a value, which
makes an environment a subset of a product and the collection of them a set.

Only the four projections are given, because that is all a consumer wants.
Whether a particular set *is* the set of all environments of a given length is a
different question, and a harder one; this says only what it means for a single
thing to be one.
<!--zh-->
一个环境是取值落在给定集合中的函数，故「某集合之上的环境」是四者的合取：单值、定义域为给定者、取值落在该落的地方，以及**由诸对构成**。

第四条容易漏掉，而漏掉是致命的。另外三条谈的全是某集合中的诸对，对「不是对的成员」只字未提，故没有它，一个集合可以携带任意多的垃圾而仍然合格。若那条谓词只被检验，这不费分文；但「以成员描述集合」的那个框架断言双向，于是满足它的取值就得包含每一个带垃圾的集合：那是真类，是没有集合能兑现的假设。这一合取项把每个成员钉成「索引与取值之对」，从而使环境成为一个积的子集，而它们的全体成为一个集合。

只给出四个投影，因为消费方想要的仅此而已。某个特定集合**是否就是**给定长度的全体环境之集，是另一个问题，而且更难；这里说的只是「单个东西是一个环境」是什么意思。
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

pairsInAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
pairsInAt e d B =
  ∀̇∈ (var e) (∃̇∈ (var (suc d)) (∃̇∈ (var (suc (suc B)))
    (prAtL (suc (suc zero)) (suc zero) zero)))

pairsIn-out : ∀ {n} (e d B : Fin n) (γ : S ^ n) → ⟨ γ ⊨ pairsInAt e d B ⟩
            → (s : S) → ⟨ fst s ∈ fst (lookup e γ) ⟩
            → ∥ (Σ[ u ∈ S ] (Σ[ v ∈ S ]
                  (⟨ fst u ∈ fst (lookup d γ) ⟩
                   × (⟨ fst v ∈ fst (lookup B γ) ⟩
                      × (fst s ≡ pr (fst u) (fst v)))))) ∥₁
pairsIn-out e d B γ h s s∈ = PT.rec squash₁
  (λ { (u , (u∈ , hv)) → PT.map
    (λ { (v , (v∈ , hp)) → u , (v , (u∈ , (v∈ , subst ⟨_⟩
      (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ s ∷ γ)) hp))) })
    hv })
  (h s s∈)

pairsIn-in : ∀ {n} (e d B : Fin n) (γ : S ^ n)
           → ((s : S) → ⟨ fst s ∈ fst (lookup e γ) ⟩
              → ∥ (Σ[ u ∈ S ] (Σ[ v ∈ S ]
                    (⟨ fst u ∈ fst (lookup d γ) ⟩
                     × (⟨ fst v ∈ fst (lookup B γ) ⟩
                        × (fst s ≡ pr (fst u) (fst v)))))) ∥₁)
           → ⟨ γ ⊨ pairsInAt e d B ⟩
pairsIn-in e d B γ k s s∈ = PT.map
  (λ { (u , (v , (u∈ , (v∈ , eq)))) → u , (u∈ , ∣ v , (v∈ , subst ⟨_⟩
    (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ s ∷ γ))) eq) ∣₁) })
  (k s s∈)

envOverAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envOverAt e d B =
  svAt e ∧̇ (domAt e d ∧̇ (valuesInAt e B ∧̇ pairsInAt e d B))

module _ {n : ℕ} (e d B : Fin n) (γ : S ^ n) (h : ⟨ γ ⊨ envOverAt e d B ⟩) where
  envOver-sv     : ⟨ γ ⊨ svAt e ⟩
  envOver-sv     = h .fst
  envOver-dom    : ⟨ γ ⊨ domAt e d ⟩
  envOver-dom    = h .snd .fst
  envOver-values : ⟨ γ ⊨ valuesInAt e B ⟩
  envOver-values = h .snd .snd .fst
  envOver-pairs  : ⟨ γ ⊨ pairsInAt e d B ⟩
  envOver-pairs  = h .snd .snd .snd
```

<!--en-->
A description reads the same in any frame that puts the same three sets where it
looks. Every reader above is stated through `fst`{.Agda} of a lookup and nothing
else, so moving the description from one environment to another is four
transports and no thought. Seven of the ten clauses bind their own ambient
set, and this is what turns "the members of that set are the environments" back
into a statement about the set a construction actually built.
<!--zh-->
一条描述在任何「把同样三个集合放在它所看之处」的框架里读起来都一样。上面每条读式都只经一次查表的 `fst`{.Agda} 陈述，别无其他，故把那条描述从一个环境搬到另一个环境是四次搬运、不必动脑。十条子句里有七条绑定自己的周遭集合，而这就是把「那个集合的成员就是诸环境」变回「关于某个构造真正造出的集合」的那句话的东西。
<!--/-->

```agda
valuesInAt-in : ∀ {n} (f B : Fin n) (γ : S ^ n)
              → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
                 → ⟨ fst y ∈ fst (lookup B γ) ⟩)
              → ⟨ γ ⊨ valuesInAt f B ⟩
valuesInAt-in f B γ k x y hp = k x y
  (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (y ∷ x ∷ γ)) hp)

envOverAt-transport : ∀ {n n'} (γ : S ^ n) (γ' : S ^ n')
                      (e d B : Fin n) (e' d' B' : Fin n')
                    → fst (lookup e γ) ≡ fst (lookup e' γ')
                    → fst (lookup d γ) ≡ fst (lookup d' γ')
                    → fst (lookup B γ) ≡ fst (lookup B' γ')
                    → ⟨ γ ⊨ envOverAt e d B ⟩ → ⟨ γ' ⊨ envOverAt e' d' B' ⟩
envOverAt-transport γ γ' e d B e' d' B' qe qd qb h =
    svAt-in e' γ' (λ x y y' p q →
      svAt-out e γ (envOver-sv e d B γ h) x y y'
        (subst ⟨_⟩ (sym (at x y)) p) (subst ⟨_⟩ (sym (at x y')) q))
  , ( domAt-intro e' d' γ'
      (λ x → (λ m → subst (λ w → ⟨ fst x ∈ w ⟩) qd
                (PT.rec (snd (fst x ∈ fst (lookup d γ)))
                  (λ { (y , p) → domAt-out e d γ (envOver-dom e d B γ h) x y
                         (subst ⟨_⟩ (sym (at x y)) p) })
                  m))
            , (λ hx → PT.map (λ { (y , p) → y , subst ⟨_⟩ (at x y) p })
                (domAt-in e d γ (envOver-dom e d B γ h) x
                  (subst (λ w → ⟨ fst x ∈ w ⟩) (sym qd) hx))))
    , ( valuesInAt-in e' B' γ'
        (λ x y p → subst (λ w → ⟨ fst y ∈ w ⟩) qb
          (valuesInAt-out e B γ (envOver-values e d B γ h) x y
            (subst ⟨_⟩ (sym (at x y)) p)))
      , pairsIn-in e' d' B' γ'
        (λ s s∈ → PT.map
          (λ { (u , (v , (u∈ , (v∈ , eq)))) →
            u , (v , ( subst (λ w → ⟨ fst u ∈ w ⟩) qd u∈
                     , ( subst (λ w → ⟨ fst v ∈ w ⟩) qb v∈ , eq ) )) })
          (pairsIn-out e d B γ (envOver-pairs e d B γ h) s
            (subst (λ w → ⟨ fst s ∈ w ⟩) (sym qe) s∈))) ) )
  where
  at : (x y : S) → (pr (fst x) (fst y) ∈ fst (lookup e γ))
                 ≡ (pr (fst x) (fst y) ∈ fst (lookup e' γ'))
  at x y = cong (λ w → pr (fst x) (fst y) ∈ w) qe
```

<!--en-->
## A container for pair components
<!--zh-->
## 容纳配对分量
<!--/-->

<!--en-->
Reading a pair-shaped code will expose its two components as elements of one
constructible set. `Container` packages that set and the three membership facts.
The construction is opaque so later formula proofs use only this small interface.
<!--zh-->
读取配对形状的码时，要把两个分量呈现为同一个可构造集合的元素。`Container` 把该集合与三项隶属事实打包起来。这个构造保持不透明，使后续公式证明只使用这份小接口。
<!--/-->

```agda
Container : (x u v : S) → Type (ℓ-suc ℓ)
Container x u v = Σ[ s ∈ S ] (⟨ fst s ∈ fst x ⟩ × (⟨ fst u ∈ fst s ⟩ × ⟨ fst v ∈ fst s ⟩))

opaque
  container : (x u v : S) → fst x ≡ pr (fst u) (fst v) → Container x u v
  container x u v e = s , (s∈ , (∈pair-introL refl , ∈pair-introR refl))
    where
    s∈ : ⟨ ⁅ fst u , fst v ⁆ ∈ fst x ⟩
    s∈ = subst (λ w → ⟨ ⁅ fst u , fst v ⁆ ∈ w ⟩) (sym e) (∈pair-introR refl)
    s : S
    s = ⁅ fst u , fst v ⁆ , isL-trans s∈ (snd x)

```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The hierarchy readers now speak directly about the constructible model. The chapter provides the object-language dictionary for pairs, functions, domains, and environments, together with the opaque container used to read compound codes. The next chapter composes these entries into finite code expressions.
<!--zh-->
层级读式现在直接陈述关于可构造模型的性质。本章给出配对、函数、定义域与环境的对象语言词典，并给出读取复合码所用的不透明容器。下一章把这些词条组合成有穷码表达式。
<!--/-->
