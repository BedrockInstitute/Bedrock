# The definable powerset, at a carrier that is a slot

<!--en-->
This is the step the whole route exists for. Every chapter before it built a
piece of the machine at a carrier the caller *holds*: a set of `L`, named in a
formula as a constant. The internal hierarchy cannot hold its stage that way. Its
graph binds the stage, because a graph may not name the object it defines, and a
set enters a formula only by being named. So the description of the definable
powerset has to be speakable **under that binder**, with the carrier occupying a
slot of the ambient environment and nothing else.

What the description says is what the operator is. `u` is the definable powerset
of the carrier when its members are exactly the sets carved out of the carrier by
a formula: there merely is a code `c` over the carrier and a value `v`, the value
is what the satisfaction recursion records at that code, and `u`'s member is the
set of members of the carrier whose one-entry environment lies in `v`. Three
conjuncts, and each is a chapter already delivered, read at a slot rather than at
a constant.

One shape correction is forced and it is worth stating before the formula
appears. The code and the value are bound by **adjacent** existentials, with no
conjunct between them. Nested through an intervening conjunct the two hypotheses
land at different environments, and the route would acquire a weakening lemma it
otherwise never needs: the same formula, the same conjunct count, the same depth,
and a lemma's worth of difference.
<!--zh-->
这就是整条路线为之存在的那一步。在它之前的每一章，造的都是这台机器在「调用方**握**着的载体」上的一个零件：`L` 的一个集合，在公式里被点名为常元。内部层级没法那样握住自己的阶段。它的图把阶段绑定起来，因为一个图不可以点名它所定义的那个对象，而集合进入公式的唯一方式是被点名。故可定义幂集的描述必须能**在那层绑定之下**说出口，其载体只占周遭环境的一位，别无其他。

那条描述所说的，就是这个算子本身。`u` 是载体的可定义幂集，当其诸成员恰是「由一条公式从载体中刻出的那些集合」：仅仅存在载体之上的一个码 `c` 与一个取值 `v`，该取值就是满足关系那场递归在那个码处所记录的东西，而 `u` 的那个成员是「其单条目环境落在 `v` 中的载体诸成员」之集。三个合取项，而每一个都是一章早已交付的东西，只是读在一位上、不读在常元上。

有一处形状上的更正是被逼的，值得在公式出现之前先讲。码与取值由**相邻的**两个存在量词绑定，中间不隔任何合取项。若中间隔一个合取项而嵌套，那两条假设就落到不同的环境上，于是这条路线会平白背上一条它本来永远用不着的弱化引理：同一条公式、同样的合取项数目、同样的深度，差别恰好是一条引理。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Powerset {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( 𝒟ₒ→isL; 𝒟ₒS; LsetS )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-out; extAt-in; extAt-in-both; tagAtL; tagAtL-adequate
        ; domAt; domAt-intro; domAt-out )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.Recover {ℓ} using ( keyOf; keyOf-fst )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyArityAtL; keyArityAtL-in; keyArityAtL-out; hasWitnessAt
        ; codeS; keyS; witnessAt-in; witnessAt-out )
open import L.Coding.Graph {ℓ} lem
  using ( satGraphAt; GraphWitAt; graphAt-in; graphAt-out )
open import L.Coding.Table {ℓ} lem
  using ( keyʟ; slot; satTable; total; inSlot; entry-in )
open import L.Coding.Slot {ℓ} lem using ( slotClosed )
open import L.Coding.Sound {ℓ} lem using ( soundness )
open import L.Coding.Unique {ℓ} lem using ( module Good )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Bridge {ℓ} lem using ( asConst; defSet-Sat )
open import L.Coding.Uniform {ℓ} lem using ( keyBridge )

open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The environment with one entry
<!--zh-->
## 只有一个条目的环境
<!--/-->

<!--en-->
Definability at arity one asks whether a formula holds of a single member, and
the satisfaction recursion answers at *environments*, so the two are joined by
the environment that assigns that member to the only variable there is. An
environment is its graph, and a graph of length one is a single pair: the numeral
zero with the value.

That makes the reader one line. "The set at this slot has exactly the pairs
`(0, y)` as members" is `extAt`{.Agda} applied to the tag reader, and the tag
reader already delivers the equation between underlying sets, so nothing has to
be proved about pairs here at all.

Its two directions are hand-written over the one-element index type, and that is
a measurement rather than a taste. Reading a membership in a one-entry set back
is a two-case split, one case impossible; through a library round trip between
finite functions and vectors the same statement walled a chapter at over eight
minutes, and the chapter that met it wrote its two clauses by hand instead. This
one does the same.
<!--zh-->
元数一处的可定义性，问的是一条公式对单个成员是否成立，而满足关系那场递归是在**环境**处作答的；把两者接起来的，正是「把那个成员指派给仅有的那一个变元」的环境。环境就是它的图，而长度为一的图只是一个对：数码零配上那个取值。

于是读式只有一行。「这一位上的集合，其成员恰是诸对 `(0, y)`」就是 `extAt`{.Agda} 施于标签读式，而标签读式本来就交付底集之间的那条等式，故此处压根不必再证任何关于对的事。

它的两个方向手写在那个单元素索引类型上，而这是测量、不是口味。把「属于一个单条目集合」读回来，是一次两分支的情形分析，其中一支不可能；若走库里「有穷函数与向量」的往返，同一条陈述曾把某一章卡在八分钟以上，而遇上它的那一章改为手写两条子句。这一章照办。
<!--/-->

```agda
envOne : V ℓ → V ℓ
envOne y = env {1} (λ _ → y)

envOneAt : ∀ {n} → Fin n → Fin n → Formula S n
envOneAt e y = extAt e (tagAtL zero 0 (suc y))

module _ {n : ℕ} (e y : Fin n) (γ : S ^ n) where
  private
    E : S
    E = lookup e γ

    v : V ℓ
    v = fst (lookup y γ)

    readEntry : (z : S) → ⟨ fst z ∈ envOne v ⟩ → fst z ≡ pr (# 0) v
    readEntry z = PT.rec (setIsSet (fst z) (pr (# 0) v))
      (λ { (lift zero , q) → sym q ; (lift (suc ()) , _) })

    entry∈ : (z : S) → fst z ≡ pr (# 0) v → ⟨ fst z ∈ envOne v ⟩
    entry∈ z q = ∣ lift zero , sym q ∣₁

  envOneAt-in : fst E ≡ envOne v → ⟨ γ ⊨ envOneAt e y ⟩
  envOneAt-in q = extAt-in-both e (tagAtL zero 0 (suc y)) γ fwd bwd
    where
    fwd : (z : S) → ⟨ fst z ∈ fst E ⟩ → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc y) ⟩
    fwd z z∈ = subst ⟨_⟩ (sym (tagAtL-adequate zero 0 (suc y) (z ∷ γ)))
      (readEntry z (subst (λ w → ⟨ fst z ∈ w ⟩) q z∈))

    bwd : (z : S) → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc y) ⟩ → ⟨ fst z ∈ fst E ⟩
    bwd z h = subst (λ w → ⟨ fst z ∈ w ⟩) (sym q)
      (entry∈ z (subst ⟨_⟩ (tagAtL-adequate zero 0 (suc y) (z ∷ γ)) h))

  envOneAt-out : ⟨ γ ⊨ envOneAt e y ⟩ → fst E ≡ envOne v
  envOneAt-out h = extensionality (fst E) (envOne v) (sub₁ , sub₂)
    where
    sub₁ : ⟨ fst E ⊆ envOne v ⟩
    sub₁ w w∈ₛ = ∈∈ₛ {a = w} {b = envOne v} .fst
      (entry∈ wS (subst ⟨_⟩
        (tagAtL-adequate zero 0 (suc y) (wS ∷ γ))
        (extAt-out e (tagAtL zero 0 (suc y)) γ h wS w∈)))
      where
      w∈ : ⟨ w ∈ fst E ⟩
      w∈ = ∈∈ₛ {a = w} {b = fst E} .snd w∈ₛ

      wS : S
      wS = w , isL-trans {x = fst E} {y = w} w∈ (snd E)

    sub₂ : ⟨ envOne v ⊆ fst E ⟩
    sub₂ w w∈ₛ = ∈∈ₛ {a = w} {b = fst E} .fst
      (PT.rec (snd (w ∈ fst E))
        (λ { (lift zero , q) →
               subst (λ u → ⟨ u ∈ fst E ⟩) (keyOf-fst 0 (lookup y γ) ∙ q) hasKey
           ; (lift (suc ()) , _) })
        (∈∈ₛ {a = w} {b = envOne v} .snd w∈ₛ))
      where
      hasKey : ⟨ fst (keyOf 0 (lookup y γ)) ∈ fst E ⟩
      hasKey = extAt-in e (tagAtL zero 0 (suc y)) γ h (keyOf 0 (lookup y γ))
        (subst ⟨_⟩
          (sym (tagAtL-adequate zero 0 (suc y) (keyOf 0 (lookup y γ) ∷ γ)))
          (keyOf-fst 0 (lookup y γ)))
```

<!--en-->
## What it is for a value to be what a code defines
<!--zh-->
## 一个取值「是某个码所定义的东西」，是什么意思
<!--/-->

<!--en-->
The third conjunct, alone, at three slots: the member, the carrier and the value
the satisfaction recursion recorded. It says that the member is the set of those
members of the carrier whose one-entry environment lies in that value, which is
the definable subset spelled out with the recursion in the place of satisfaction.

The condition is a conjunction rather than one clause because the carrier's bound
is not implied by the rest. A member of the recursion's value is an environment,
not a set of the carrier, so the second half alone would say nothing about where
the member came from; the definable subset is cut out of the carrier and the
formula has to say so.

Its two directions are `extAt`{.Agda}'s own two, and the existential inside the
condition is read by the previous section. Nothing here inspects the value, which
is why this section knows nothing about codes.
<!--zh-->
第三个合取项，单独拿出来，落在三个槽位上：那个成员、载体，以及满足关系那场递归所记录的取值。它说的是：那个成员就是「其单条目环境落在该取值之中」的那些载体成员之集，也就是把可定义子集逐字写出来、只是用那场递归顶替了满足关系。

那个条件是一个合取而不是单独一条子句，因为「落在载体之内」这道界并不由其余部分蕴含。递归取值的成员是一个环境，不是载体的一个子集，故仅凭后半句，对「那个成员从哪里来」什么也没说；可定义子集是从载体中刻出来的，公式必须把这一点说出来。

它的两个方向就是 `extAt`{.Agda} 自己的那两个，而条件里面那个存在量词由上一节读出。此处没有任何东西去查看那个取值，这也是本节对码一无所知的原因。
<!--/-->

```agda
DefinesAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
DefinesAt x w v = extAt x ( (var zero ∈̇ var (suc w))
                          ∧̇ ∃̇ ( envOneAt zero (suc zero)
                               ∧̇ (var zero ∈̇ var (suc (suc v))) ) )

module _ {n : ℕ} (x w v : Fin n) (γ : S ^ n) where
  private
    inner : Formula S (suc n)
    inner = ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))

    body : Formula S (suc n)
    body = (var zero ∈̇ var (suc w)) ∧̇ inner

    Holds : S → Type (ℓ-suc ℓ)
    Holds z = ⟨ fst z ∈ fst (lookup w γ) ⟩
              × ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩

    readInner : (z : S) → ⟨ (z ∷ γ) ⊨ inner ⟩
              → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
    readInner z = PT.rec (snd (envOne (fst z) ∈ fst (lookup v γ))) step
      where
      step : Σ[ E ∈ S ] ⟨ (E ∷ z ∷ γ)
               ⊨ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
           → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
      step (E , (hE , E∈)) = subst (λ u → ⟨ u ∈ fst (lookup v γ) ⟩)
        (envOneAt-out zero (suc zero) (E ∷ z ∷ γ) hE) E∈

    fillInner : (z : S) → ⟨ envOne (fst z) ∈ fst (lookup v γ) ⟩
              → ⟨ (z ∷ γ) ⊨ inner ⟩
    fillInner z h =
      ∣ E , (envOneAt-in zero (suc zero) (E ∷ z ∷ γ) refl , h) ∣₁
      where
      E : S
      E = envOne (fst z)
        , isL-trans {x = fst (lookup v γ)} {y = envOne (fst z)} h
            (snd (lookup v γ))

  DefinesAt-out : ⟨ γ ⊨ DefinesAt x w v ⟩
                → (z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → Holds z
  DefinesAt-out h z z∈ = hz .fst , readInner z (hz .snd)
    where
    hz : ⟨ (z ∷ γ) ⊨ body ⟩
    hz = extAt-out x body γ h z z∈

  DefinesAt-in : ⟨ γ ⊨ DefinesAt x w v ⟩
               → (z : S) → Holds z → ⟨ fst z ∈ fst (lookup x γ) ⟩
  DefinesAt-in h z (hw , hv) =
    extAt-in x body γ h z (hw , fillInner z hv)

  DefinesAt-both : ((z : S) → ⟨ fst z ∈ fst (lookup x γ) ⟩ → Holds z)
                 → ((z : S) → Holds z → ⟨ fst z ∈ fst (lookup x γ) ⟩)
                 → ⟨ γ ⊨ DefinesAt x w v ⟩
  DefinesAt-both f g = extAt-in-both x body γ
    (λ z z∈ → f z z∈ .fst , fillInner z (f z z∈ .snd))
    (λ z h → g z (h .fst , readInner z (h .snd)))
```

<!--en-->
## Is a code over the carrier at that slot
<!--zh-->
## 是那一位上的载体之上的一个码
<!--/-->

<!--en-->
Two conjuncts, both already proved, and this is only where they meet: the
argument is a key at arity one, and it has a closed, shaped witness at the
carrier the slot holds. The first is what tells the decode which arity to answer
at; the second is what the decode runs on. Neither names a set, so the pair can
be spoken under any binder.

The pinned predicate of the code-set chapter is this same pair with one binder on
top, and that binder is the only thing separating a predicate a stage can hold
from a predicate a bound variable can carry.
<!--zh-->
两个合取项，都早已证好，而此处只是它们会合之处：那个实参是元数一处的一个键，且它在「那一位所持有的载体」上有一个既封闭又成形的见证。前者告诉解码该在哪个元数上作答；后者是解码跑在其上的东西。两者都不点名任何集合，故这一对可以在任意绑定之下说出口。

码集那一章那条被钉住的谓词，就是同一对再压上一层绑定，而那层绑定正是「一个阶段握得住的谓词」与「一个被绑定变元携带得了的谓词」之间唯一的差别。
<!--/-->

```agda
isCodeAt : ∀ {n} → Fin n → Fin n → Formula S n
isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c

module _ (A : S) where
  codeAt-in : ∀ {n} (c w : Fin n) (γ : S ^ n)
            → fst (lookup w γ) ≡ fst A
            → (ψ : Formula ⟪ fst A ⟫ 1) → fst (lookup c γ) ≡ fst (keyS A ψ)
            → ⟨ γ ⊨ isCodeAt c w ⟩
  codeAt-in c w γ qw ψ qc =
    keyArityAtL-in c 1 γ (codeS A ψ) qc , witnessAt-in A w c γ ψ qw qc

  codeAt-out : ∀ {n} (c w : Fin n) (γ : S ^ n)
             → fst (lookup w γ) ≡ fst A
             → ⟨ γ ⊨ isCodeAt c w ⟩
             → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
                   (fst (lookup c γ) ≡ fst (keyS A ψ))) ∥₁
  codeAt-out c w γ qw (hk , hw) =
    PT.rec squash₁ step (keyArityAtL-out c 1 γ hk)
    where
    step : Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# 1) (fst z))
         → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
               (fst (lookup c γ) ≡ fst (keyS A ψ))) ∥₁
    step (z , qz) = witnessAt-out A w c γ qw hw 1 z qz
```

<!--en-->
## The graph, at a carrier that is a slot
<!--zh-->
## 那个图，落在一个作为槽位的载体上
<!--/-->

<!--en-->
The satisfaction recursion's graph was generalized to take its carrier as a slot,
and its two halves are the existence and uniqueness the recursion was built from,
restated at that slot and at a variable environment. Nothing is proved here that
was not proved then: existence hands over the subformula slot, the table over it,
and the twelve clauses, all three of which take the ambient environment as an
argument already; uniqueness reads the graph's own bound index set and table back
and applies the pinning theorem at the carrier the graph bound.

Both are stated with the code and the value reached by equations rather than
named, which is the law the value theorems were written under: naming a key puts
its construction inside a satisfaction, and the same statement then costs minutes
instead of seconds.
<!--zh-->
满足关系那场递归的图已被推广为把载体取作一位，而它的两半就是那场递归据以建立的存在性与唯一性，只是重新陈述在那一位上、并落在一个变元环境上。此处没有证任何当时未证之事：存在性递出子公式槽、其上的那张表、以及十二条子句，而这三样本来就把周遭环境取作实参；唯一性把图自己绑定的索引集与表读回来，再在图所绑定的那个载体上施用钉住定理。

两者都把码与取值以等式抵达、而不是点名，这正是诸取值定理据以写下的那条规矩：点名一个键，就把它的构造塞进了一个满足关系里面，同一条陈述于是从几秒变成几分钟。
<!--/-->

```agda
module _ (B : S) where
  private
    Ci Ti : ∀ {k} → Fin (suc (suc (suc k)))
    Ci = suc (suc zero)
    Ti = suc zero

  graphAt-holds : ∀ {m n} (φ : Formula S m) (w c v : Fin n) (γ : S ^ n)
                → fst (lookup w γ) ≡ fst B
                → fst (lookup c γ) ≡ fst (keyʟ φ)
                → fst (lookup v γ) ≡ fst (Sat B φ)
                → ⟨ γ ⊨ satGraphAt w c v ⟩
  graphAt-holds φ w c v γ qw qc qv = graphAt-in w c v γ
    ∣ slot B φ , (satTable B φ , (B , (sym qw
    , ( slotClosed B φ γ
    , ( hdom
    , ( entry
    , soundness B φ γ )))))) ∣₁
    where
    δ : S ^ (suc (suc (suc _)))
    δ = B ∷ satTable B φ ∷ slot B φ ∷ γ

    hdom : ⟨ δ ⊨ domAt Ti Ci ⟩
    hdom = domAt-intro Ti Ci δ
      (λ z → (λ h → PT.rec (snd (fst z ∈ fst (slot B φ)))
                  (λ { (u , hu) → inSlot B φ (fst z) (fst u) hu }) h)
           , (λ h → total B φ (fst z) h))

    entry : ⟨ pr (fst (lookup c γ)) (fst (lookup v γ)) ∈ fst (satTable B φ) ⟩
    entry = subst2 (λ a b → ⟨ pr a b ∈ fst (satTable B φ) ⟩)
      (sym qc) (sym qv) (entry-in B φ)

  graphAt-unique : ∀ {m n} (φ : Formula S m) (w c v : Fin n) (γ : S ^ n)
                 → fst (lookup w γ) ≡ fst B
                 → fst (lookup c γ) ≡ fst (keyʟ φ)
                 → ⟨ γ ⊨ satGraphAt w c v ⟩
                 → fst (lookup v γ) ≡ fst (Sat B φ)
  graphAt-unique φ w c v γ qw qc h =
    PT.rec (setIsSet (fst (lookup v γ)) (fst (Sat B φ))) step
      (graphAt-out w c v γ h)
    where
    step : GraphWitAt w c v γ → fst (lookup v γ) ≡ fst (Sat B φ)
    step (C , (T , (b , (eb , (hc , (hd , (ha , h12)))))))
      = Good.pinned (b ∷ T ∷ C ∷ γ) Ci Ti zero hc hd h12 φ
          (lookup c γ) (lookup v γ) qc
          (domAt-out Ti Ci (b ∷ T ∷ C ∷ γ) hd (lookup c γ) (lookup v γ) ha) ha
      ∙ cong (λ u → fst (Sat u φ)) (Σ≡Prop (λ u → snd (isL u)) (eb ∙ qw))
```

<!--en-->
## The description, and the side condition it travels with
<!--zh-->
## 那条描述，以及随它一同旅行的旁条件
<!--/-->

<!--en-->
The three conjuncts, under two adjacent existentials, under one extension: `u` is
the set of exactly those `x` for which there merely are a code `c` over the
carrier and a value `v` such that the recursion records `v` at `c` and `x` is
what `v` defines. That is the definable powerset, said in the object language,
with the carrier at a slot throughout.

The side condition is about what an object-language quantifier can reach. Every
existential in the description ranges over `L`, so the set the description picks
out can only contain constructible sets. If some definable subset of the carrier
were not constructible, the description would still be satisfied, by the set of
the constructible ones, and it would then hold of something that is not the
definable powerset. `DefOK`{.Agda} is exactly the absence of that gap.

A carrier the caller holds needs no such condition **stated**, because a caller
that holds the carrier holds the theorem about it too. A carrier at a slot is
whatever the ambient environment puts there, and no theorem about it is available
under the binder, so the fact has to travel as a hypothesis and be discharged
where the slot is filled. It is a hypothesis of the elimination only: the
introduction is given that `u` **is** the definable powerset, and `u` is an
element of `L`, so its members are constructible already and the condition it
would have needed is implied by its own hypothesis.
<!--zh-->
三个合取项，压在两个相邻的存在量词之下，再压在一次外延之下：`u` 恰是那些 `x` 之集，对它们仅仅存在载体之上的一个码 `c` 与一个取值 `v`，使得那场递归在 `c` 处记录的是 `v`，而 `x` 就是 `v` 所定义的东西。这就是可定义幂集，用对象语言说出来，而载体自始至终待在一位上。

那个旁条件关乎对象语言的量词够得着什么。描述里的每个存在量词都在 `L` 上取值，故这条描述所挑出的集合只可能装着可构造集。若载体的某个可定义子集不可构造，这条描述仍会被满足，被「诸可构造者之集」满足，而那样它就对一个并非可定义幂集的东西成立了。`DefOK`{.Agda} 恰是「这道缝不存在」。

调用方握着的载体无须**写出**这样的条件，因为握着载体的调用方也握着关于它的定理。一位上的载体则是周遭环境往那里放的任何东西，在那层绑定之下没有任何关于它的定理可用，故这件事必须作为假设一路旅行，并在那一位被填上之处解除。它只是消去那一半的假设：引入被给定 `u` **就是**可定义幂集，而 `u` 是 `L` 的元素，故它的诸成员本就可构造，它本会需要的那个条件由它自己的假设蕴含。
<!--/-->

```agda
private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

DefBody : ∀ {n} → Fin n → Formula S (suc (suc (suc n)))
DefBody w = isCodeAt (suc zero) (sh3 w)
            ∧̇ ( satGraphAt (sh3 w) (suc zero) zero
              ∧̇ DefinesAt (suc (suc zero)) (sh3 w) zero )

DefAt : ∀ {n} → Fin n → Fin n → Formula S n
DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))

DefOK : S → Type (ℓ-suc ℓ)
DefOK A = (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (fst A) ⟩ → ⟨ isL x ⟩
```

<!--en-->
## One formula, both ways
<!--zh-->
## 一条公式，两个方向
<!--/-->

<!--en-->
The two halves of the description at a single formula, which is what the
adequacy is assembled from. Supplying the three conjuncts for a formula `ψ` is
supplying its key for the code and the recursion's value for the value; reading
them back is decoding the code to a formula, pinning the value to the recursion's
own, and then reading the third conjunct as a set identity.

Everything here is stated at a **variable** carrier reached by an equation, and
that is what keeps the stage out of the proof. The instantiation at a stage is an
equation the caller supplies, and neither `Lset`{.Agda} nor an ordinal appears
anywhere below.
<!--zh-->
描述的两半落在单独一条公式上，而充分性正是由它们装配起来的。为一条公式 `ψ` 供上那三个合取项，就是把它的键供给码、把递归的取值供给取值；把它们读回来，则是把码解码成一条公式、把取值钉在递归自己的取值上，然后把第三个合取项读作一条集合等式。

此处的一切都陈述在**变元**载体上、并经一条等式抵达，而正是这一点把阶段挡在证明之外。在某个阶段处的实例化是调用方供上的一条等式，而 `Lset`{.Agda} 与序数在下面任何地方都不出现。
<!--/-->

```agda
module _ (A : S) where
  private
    module DA = DefOf (fst A)

    toS : Formula ⟪ fst A ⟫ 1 → Formula S 1
    toS ψ = mapFo (asConst A) ψ

    ιA : ⟪ fst A ⟫ → V ℓ
    ιA = ⟪ fst A ⟫↪

    ιA∈ : (m : ⟪ fst A ⟫) → ⟨ ιA m ∈ fst A ⟩
    ιA∈ m = ∈∈ₛ {a = ιA m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

    Fibre : Formula ⟪ fst A ⟫ 1 → V ℓ → Type (ℓ-suc ℓ)
    Fibre ψ y = Σ[ p ∈ Σ[ m ∈ ⟪ fst A ⟫ ] ⟨ DA.smallSat ψ m ⟩ ]
                  (ιA (p .fst) ≡ y)

    inSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
          → ⟨ ιA m ∈ DA.defSet ψ ⟩
          → ⟨ envOne (ιA m) ∈ fst (Sat A (toS ψ)) ⟩
    inSat ψ m h = subst ⟨_⟩ (defSet-Sat A ψ m) h

    outSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
           → ⟨ envOne (ιA m) ∈ fst (Sat A (toS ψ)) ⟩
           → ⟨ ιA m ∈ DA.defSet ψ ⟩
    outSat ψ m h = subst ⟨_⟩ (sym (defSet-Sat A ψ m)) h

  fill : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
       → (z : S) (ψ : Formula ⟪ fst A ⟫ 1) → DA.defSet ψ ≡ fst z
       → ⟨ (Sat A (toS ψ) ∷ keyS A ψ ∷ z ∷ γ) ⊨ DefBody w ⟩
  fill {n} w γ qw z ψ qz = hcode , (hgraph , hdef)
    where
    δ : S ^ (suc (suc (suc n)))
    δ = Sat A (toS ψ) ∷ keyS A ψ ∷ z ∷ γ

    hcode : ⟨ δ ⊨ isCodeAt (suc zero) (sh3 w) ⟩
    hcode = codeAt-in A (suc zero) (sh3 w) δ qw ψ refl

    hgraph : ⟨ δ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
    hgraph = graphAt-holds A (toS ψ) (sh3 w) (suc zero) zero δ qw
               (keyBridge A ψ) refl

    Holds : S → Type (ℓ-suc ℓ)
    Holds y = ⟨ fst y ∈ fst (lookup w γ) ⟩
              × ⟨ envOne (fst y) ∈ fst (Sat A (toS ψ)) ⟩

    into : (y : S) → ⟨ fst y ∈ fst z ⟩ → Holds y
    into y y∈ = PT.rec
      (isProp× (snd (fst y ∈ fst (lookup w γ)))
               (snd (envOne (fst y) ∈ fst (Sat A (toS ψ)))))
      step (subst (λ X → ⟨ fst y ∈ X ⟩) (sym qz) y∈)
      where
      step : Fibre ψ (fst y) → Holds y
      step ((m , hm) , qm) =
          subst (λ u → ⟨ u ∈ fst (lookup w γ) ⟩) qm
            (subst (λ X → ⟨ ιA m ∈ X ⟩) (sym qw) (ιA∈ m))
        , subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) qm
            (inSat ψ m ∣ (m , hm) , refl ∣₁)

    back : (y : S) → Holds y → ⟨ fst y ∈ fst z ⟩
    back y (yw , ys) = subst (λ X → ⟨ fst y ∈ X ⟩) qz
      (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
        (outSat ψ (fib .fst)
          (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩)
            (sym (fib .snd)) ys)))
      where
      fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ fst y)
      fib = ∈-asFiber {a = fst y} {b = fst A}
        (subst (λ X → ⟨ fst y ∈ X ⟩) qw yw)

    hdef : ⟨ δ ⊨ DefinesAt (suc (suc zero)) (sh3 w) zero ⟩
    hdef = DefinesAt-both (suc (suc zero)) (sh3 w) zero δ into back

  read : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
       → (z c v : S) → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩
       → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
  read {n} w γ qw z c v (hcode , (hgraph , hdef)) =
    PT.rec squash₁ step (codeAt-out A (suc zero) (sh3 w) δ qw hcode)
    where
    δ : S ^ (suc (suc (suc n)))
    δ = v ∷ c ∷ z ∷ γ

    step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (fst c ≡ fst (keyS A ψ))
         → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
    step (ψ , qc) = ∣ ψ , extensionality (DA.defSet ψ) (fst z) (sub₁ , sub₂) ∣₁
      where
      qv : fst v ≡ fst (Sat A (toS ψ))
      qv = graphAt-unique A (toS ψ) (sh3 w) (suc zero) zero δ qw
             (qc ∙ keyBridge A ψ) hgraph

      sub₁ : ⟨ DA.defSet ψ ⊆ fst z ⟩
      sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = fst z} .fst
        (PT.rec (snd (y ∈ fst z)) place
          (∈∈ₛ {a = y} {b = DA.defSet ψ} .snd y∈ₛ))
        where
        place : Fibre ψ y → ⟨ y ∈ fst z ⟩
        place ((m , hm) , qm) =
          DefinesAt-in (suc (suc zero)) (sh3 w) zero δ hdef
            (y , isL-trans {x = fst A} {y = y}
                   (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m)) (snd A))
            ( subst (λ X → ⟨ y ∈ X ⟩) (sym qw)
                (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m))
            , subst (λ X → ⟨ envOne y ∈ X ⟩) (sym qv)
                (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) qm
                  (inSat ψ m ∣ (m , hm) , refl ∣₁)) )

      sub₂ : ⟨ fst z ⊆ DA.defSet ψ ⟩
      sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DA.defSet ψ} .fst
        (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
          (outSat ψ (fib .fst)
            (subst (λ u → ⟨ envOne u ∈ fst (Sat A (toS ψ)) ⟩) (sym (fib .snd))
              (subst (λ X → ⟨ envOne y ∈ X ⟩) qv (cond .snd)))))
        where
        y∈ : ⟨ y ∈ fst z ⟩
        y∈ = ∈∈ₛ {a = y} {b = fst z} .snd y∈ₛ

        yS : S
        yS = y , isL-trans {x = fst z} {y = y} y∈ (snd z)

        cond : ⟨ y ∈ fst (lookup w γ) ⟩ × ⟨ envOne y ∈ fst v ⟩
        cond = DefinesAt-out (suc (suc zero)) (sh3 w) zero δ hdef yS y∈

        fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ y)
        fib = ∈-asFiber {a = y} {b = fst A}
          (subst (λ X → ⟨ y ∈ X ⟩) qw (cond .fst))
```

<!--en-->
## Both readings of the description
<!--zh-->
## 那条描述的两种读法
<!--/-->

<!--en-->
Assembling and describing are the per-member halves, and the two readings are
those under `extAt`{.Agda}'s own two directions. The introduction says that the
definable powerset satisfies the description: every member of it is a definable
subset, and the three conjuncts are supplied for the formula that defines it.
The elimination says that nothing else does, and it is the direction the side
condition is for, since a set the description holds of has to be re-entered
member by member and a member arrives as an element of `L` or not at all.
<!--zh-->
装配与描述是逐成员的那两半，而两种读法就是它们置于 `extAt`{.Agda} 自己那两个方向之下。引入说的是可定义幂集满足这条描述：它的每个成员都是一个可定义子集，而那三个合取项为「定义它的那条公式」供上。消去说的是别的东西都不满足，而这正是那个旁条件所为的方向，因为一个「描述对之成立」的集合要被逐成员地重新进入，而一个成员要么以 `L` 的元素的形式到场，要么根本不到场。
<!--/-->

```agda
  private
    describe : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
             → (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
             → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
    describe w γ qw z = PT.rec squash₁ viaCode
      where
      Target : Type (ℓ-suc ℓ)
      Target = ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁

      viaValue : (c : S)
               → Σ[ v ∈ S ] ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩ → Target
      viaValue c (v , hv) = read w γ qw z c v hv

      viaCode : Σ[ c ∈ S ] ⟨ (c ∷ z ∷ γ) ⊨ ∃̇ (DefBody w) ⟩ → Target
      viaCode (c , hc) = PT.rec squash₁ (viaValue c) hc

    assemble : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
             → (z : S)
             → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
             → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
    assemble w γ qw z = PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)))) step
      where
      step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)
           → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (DefBody w)) ⟩
      step (ψ , qψ) = ∣ keyS A ψ , ∣ Sat A (toS ψ) , fill w γ qw z ψ qψ ∣₁ ∣₁

  DefAt-in : ∀ {n} (u w : Fin n) (γ : S ^ n)
           → fst (lookup w γ) ≡ fst A
           → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
           → ⟨ γ ⊨ DefAt u w ⟩
  DefAt-in {n} u w γ qw qu = extAt-in-both u Φ γ f g
    where
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (DefBody w))

    f : (z : S) → ⟨ fst z ∈ fst (lookup u γ) ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
    f z z∈ = assemble w γ qw z
      (𝒟ₒ-inv (fst A) (fst z) (subst (λ X → ⟨ fst z ∈ X ⟩) qu z∈))

    g : (z : S) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ fst (lookup u γ) ⟩
    g z hz = subst (λ X → ⟨ fst z ∈ X ⟩) (sym qu)
      (𝒟ₒ-intro (fst A) (fst z) (describe w γ qw z hz))

  DefAt-out : ∀ {n} (u w : Fin n) (γ : S ^ n) → DefOK A
            → fst (lookup w γ) ≡ fst A
            → ⟨ γ ⊨ DefAt u w ⟩
            → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
  DefAt-out {n} u w γ ok qw h =
    extensionality (fst (lookup u γ)) (𝒟ₒ (fst A)) (sub₁ , sub₂)
    where
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (DefBody w))

    sub₁ : ⟨ fst (lookup u γ) ⊆ 𝒟ₒ (fst A) ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .fst
      (𝒟ₒ-intro (fst A) y (describe w γ qw yS (extAt-out u Φ γ h yS y∈)))
      where
      y∈ : ⟨ y ∈ fst (lookup u γ) ⟩
      y∈ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .snd y∈ₛ

      yS : S
      yS = y , isL-trans {x = fst (lookup u γ)} {y = y} y∈ (snd (lookup u γ))

    sub₂ : ⟨ 𝒟ₒ (fst A) ⊆ fst (lookup u γ) ⟩
    sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .fst
      (extAt-in u Φ γ h yS
        (assemble w γ qw yS (𝒟ₒ-inv (fst A) y y∈)))
      where
      y∈ : ⟨ y ∈ 𝒟ₒ (fst A) ⟩
      y∈ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .snd y∈ₛ

      yS : S
      yS = y , ok y y∈
```

<!--en-->
## At a stage, and the side condition is gone
<!--zh-->
## 落在一个阶段上，那个旁条件随之消失
<!--/-->

<!--en-->
The instantiation, and the whole of it is one equation. A stage is an element of
`L`, its definable subsets are constructible because a stage is constructible one
stage later, and those two facts are what the successor identity delivers at
every stage at once. So the side condition is discharged for good, and what is
left is an equivalence of truth values: at a carrier holding a stage, the
description holds of a set exactly when that set **is** the definable powerset of
that stage. It holds of `𝒟ₒS`{.Agda} and of nothing else.

Neither statement mentions the stage as anything but the value of a slot, which
is what the internal hierarchy needs: the description will be spoken under a
binder, and the equation the caller supplies is the only thing that connects it
to a stage at all.
<!--zh-->
那次实例化，而它的全部就是一条等式。阶段是 `L` 的元素，它的诸可定义子集可构造 (因为阶段在下一阶段可构造)，而这两件事正是后继恒等式在每个阶段处一并交付的。故那个旁条件一劳永逸地被解除，剩下的是一条真值之间的等价：在一个持有阶段的载体上，这条描述对某个集合成立，恰当那个集合**就是**该阶段的可定义幂集。它对 `𝒟ₒS`{.Agda} 成立，对别的什么都不成立。

两条陈述都只把那个阶段当作某一位的取值来提，而这正是内部层级所需要的：那条描述将在一层绑定之下被说出，而调用方供上的那条等式，是唯一把它与某个阶段联系起来的东西。
<!--/-->

```agda
DefAt-stage : (β : V ℓ) (oβ : IsOrd β) → ∀ {n} (u w : Fin n) (γ : S ^ n)
            → fst (lookup w γ) ≡ Lset β
            → (γ ⊨ DefAt u w)
              ≡ ( (fst (lookup u γ) ≡ 𝒟ₒ (Lset β))
                , setIsSet (fst (lookup u γ)) (𝒟ₒ (Lset β)) )
DefAt-stage β oβ u w γ qw = ⇔toPath
  (DefAt-out (LsetS β oβ) u w γ (𝒟ₒ→isL β oβ) qw)
  (DefAt-in (LsetS β oβ) u w γ qw)

DefAt-𝒟ₒS : (β : V ℓ) (oβ : IsOrd β) → ∀ {n} (u w : Fin n) (γ : S ^ n)
          → lookup w γ ≡ LsetS β oβ → lookup u γ ≡ 𝒟ₒS β oβ
          → ⟨ γ ⊨ DefAt u w ⟩
DefAt-𝒟ₒS β oβ u w γ qw qu =
  DefAt-in (LsetS β oβ) u w γ (cong fst qw) (cong fst qu)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`DefAt`{.Agda} is the definable powerset described in the object language at a
carrier that is a slot, and `DefAt-in`{.Agda} and `DefAt-out`{.Agda} are its two
readings: the operator satisfies the description, and under `DefOK`{.Agda}
nothing else does. `DefAt-stage`{.Agda} spends both at a stage, where the side
condition is discharged once and for all and the description becomes an equation
between truth values.

Three chapters meet here and not one of them is re-proved. The code predicate is
read at a slot, the satisfaction graph is read at a slot, and the definable
subset is read through the bridge that says the recursion's value is satisfaction
over the carrier. What is new is only the joining: `envOneAt`{.Agda}, one line,
because an environment of length one is a single pair, and `DefinesAt`{.Agda},
which is `extAt`{.Agda} over a two-part condition.

Two measurements are worth keeping. The adjacency correction was adopted before
the first line was written and it cost nothing, so no weakening lemma exists
anywhere on this route. And the one wall met while writing was not in the
mathematics at all: the code predicate's elimination at a pinned carrier, with
the truncation's payload left to inference, ran past 140 seconds and was killed
there, while the same two lines with the payload type written out check in two.
Every `PT.rec`{.Agda} here names its payload, and that is why this chapter checks
in half a minute rather than not at all.
<!--zh-->
`DefAt`{.Agda} 是可定义幂集在对象语言中、落在一个作为槽位的载体上的描述，而 `DefAt-in`{.Agda} 与 `DefAt-out`{.Agda} 是它的两种读法：这个算子满足那条描述，且在 `DefOK`{.Agda} 之下别的东西都不满足。`DefAt-stage`{.Agda} 把两者花在一个阶段上，那里旁条件被一劳永逸地解除，而那条描述变成一条真值之间的等式。

三章在此会合，而没有一章被重证。码谓词读在一位上，满足关系的图读在一位上，而可定义子集经那座桥读出，那座桥说的是「递归的取值就是载体之上的满足关系」。新的只有接合处：`envOneAt`{.Agda}，一行，因为长度为一的环境只是一个对；以及 `DefinesAt`{.Agda}，它就是 `extAt`{.Agda} 施于一个两部分的条件。

有两次测量值得留存。相邻那处更正在第一行写下之前就已采纳，且分文未花，故这条路线上任何地方都不存在弱化引理。而写作期间遇上的唯一一堵墙，压根不在数学里：码谓词在被钉住的载体处的消去，若把截断的载荷交给推断，跑过 140 秒并在那里被杀掉；而同样两行，把载荷的类型写出来则两秒检查完毕。此处每一次 `PT.rec`{.Agda} 都为自己的载荷点名，而这正是本章能在半分钟内、而不是根本无法检查完的原因。
<!--/-->
