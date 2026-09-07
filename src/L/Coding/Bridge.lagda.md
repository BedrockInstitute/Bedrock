# What the recursion's value is

<!--en-->
The previous chapter built the value and characterized it by one membership
equation per constructor. That is enough to check the internal clauses against
it, and it is enough for nothing else: a recursion on formulas satisfying ten
equations of its own devising is an arbitrary recursion, and an internal `Def`
read off one would provably agree with nothing. This chapter says what the value
**is**. For an environment over the carrier, membership in `Sat B φ` is
satisfaction of `φ` in the world `(B, ∈)`, which is exactly the notion the
definable powerset is defined by.

The right-hand side is the **inner** semantics of the restricted structure, not
the ambient reading of the relativized formula, and the difference sits exactly
where the previous chapter's audit already looked. Relativization leaves a
bounded quantifier alone, so it guards the bound variable once, by the bounding
term. The condition guards it twice, by the carrier and by the term. The inner
semantics also guards it twice, once by its own carrier and once by the clause,
so it matches the condition constructor for constructor: no side condition on
the bound, no transitivity of the carrier, and no Δ₀ anywhere. The relativized
reading would have needed the bound contained in the carrier at every bounded
quantifier, threaded through the whole induction. Reading inner also lands the
theorem on the definable powerset's own notion instead of one step short of it.

One consequence of that choice is a restriction, and it is the same restriction
the code chapters already ruled: the formula's constants must be **members of
the carrier**. A constant outside the carrier has no value in the inner world,
so there is nothing for the two sides to agree about. The bridge therefore reads
a formula over the carrier's members and relabels it into the meta-language,
which is the alphabet the definable powerset indexes by anyway.
<!--zh-->
上一章造出了那个取值，并以「每个构造子一条成员等式」刻画了它。那足以拿内部诸子句去对照它，而除此之外什么也不够：一场沿公式的递归，若只满足十条自己拟定的等式，那就是一场任意的递归；从这样一场递归读出的内部 `Def`，可证地与任何东西都不相符。本章说出那个取值**是什么**。对载体之上的一个环境，「属于 `Sat B φ`」就是「`φ` 在世界 `(B, ∈)` 中被满足」，而后者恰是可定义幂集据以定义的那个概念。

右端取的是限制结构的**内层**语义，不是相对化公式在周遭的读法，而两者的差别恰好落在上一章那次审计已经看过的地方。相对化不动有界量词，故它对被绑变元只设一道防：由界项设防。而那个条件设两道：由载体、由界项。内层语义同样设两道：一道来自它自己的载体，一道来自那条子句；于是它与那个条件逐构造子相符：界上不加附加条件，不要载体的传递性，任何地方也不出现 Δ₀。若取相对化那种读法，则每个有界量词处都要求「界含于载体」，而这条要求得穿过整场归纳。取内层读法还有一个好处：定理直接落在可定义幂集自己的概念上，而不是差它一步。

这个选择带来一条限制，而它正是诸编码章早已裁定过的那条：公式的常元必须是**载体的成员**。载体之外的常元在内层世界里没有取值，两侧也就无从谈起相符。故这座桥读的是「载体诸成员之上的公式」，再把它重标进元语言，而那本来就是可定义幂集所用的字母表。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Bridge {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Mapping using ( mapTm; mapFo; mapFo-comp )
open import FOL.Manipulation.Relabelling using ( ⊨-map )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Environment {ℓ} using ( env; cons; lookup-spec )
open import L.Coding.Expressions {ℓ} using ( consAtL; consAtL-adequate )
open import L.Coding.EnvSet {ℓ} lem
  using ( Ix; envS; envSet; envSet-in; envSet-out )
open import L.Coding.Sat {ℓ} lem
  using ( tmIs; tmIs-var-in; tmIs-var-out; cond; Sat; Sat-mem
        ; cond∈-in; cond∈-out; cond≐-in; cond≐-out
        ; cond∃-in; cond∃-out; cond∀-in; cond∀-out
        ; cond∃∈-in; cond∃∈-out; cond∀∈-in; cond∀∈-out )

open import Cubical.Foundations.Prelude using ( subst2; funExt⁻ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The world the definable powerset means
<!--zh-->
## 可定义幂集所指的那个世界
<!--/-->

<!--en-->
The carrier is an element of `L`, so it is a set of the hierarchy, and the
definable powerset chapter takes exactly such a set. Instantiating it here is
what makes the two sides speak of the same world rather than of two worlds that
happen to be described alike: the restricted structure below, the satisfaction
opened over it, and the `defSet`{.Agda} this chapter ends at are all the **same
module application**, not a re-derivation.

The satisfaction is opened at the restricted carrier itself as constant domain,
because the bridge quantifies over formulas whose constants are members. Two
inclusions cross the layers. A member of a set of `L` is an element of `L`, since
the class is transitive, which is how a member becomes a constant of the
meta-language; and the definable powerset's own constant interpretation composes
with it, which is how one of its formulas becomes one of ours.
<!--zh-->
载体是 `L` 的元素，故它是层级的一个集合，而可定义幂集那一章要的正是这样一个集合。在此把它实例化，是为了让两侧谈论**同一个**世界，而不是两个恰好描述得相像的世界：下面的限制结构、在其上打开的满足关系，以及本章终点处的 `defSet`{.Agda}，都出自**同一次模块施用**，不是重新推导一遍。

满足关系以限制载体自身为常元域打开，因为这座桥量化的是「常元皆为成员」的那些公式。有两条包含跨越层次。`L` 的某集合的成员仍是 `L` 的元素，因为这个类传递，成员由此成为元语言的常元；而可定义幂集自己的常元解释与它复合，它的一条公式由此成为我们的一条公式。
<!--/-->

```agda
module _ (B : S) where
  module DB = DefOf (fst B)
  module SemB = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) DB.𝒮M
  open SemB.At DB.SM id using () renaming ( _⊨_ to _⊨ᴮ_ ; ⟦_⟧ to ⟦_⟧ᴮ )

  intoL : DB.SM → S
  intoL x = fst x , isL-trans {x = fst B} {y = fst x} (snd x) (snd B)

  asConst : ⟪ fst B ⟫ → S
  asConst m = intoL (DB.ι m)
```

<!--en-->
## The environment an inner assignment codes
<!--zh-->
## 一份内层赋值所编码的环境
<!--/-->

<!--en-->
The two sides hold an environment in two forms. The inner semantics holds a
vector of members; the recursion's value holds an element of `L` whose underlying
set is a graph. So the bridge is stated with the vector as a parameter and with
the equation saying the element **is** that vector's graph, and everything else
in the chapter is arranged so that this equation is the only thing that travels.

That is the choice that dissolves the risk this chapter was written to measure.
The ambient environment set recovers only *some* function whose graph a member
is, truncated, while the four quantifier clauses need the *same* function
extended by one entry. Indexed by the vector instead, extension is consing on the
underlying family, and consing a member onto the vector agrees with it index by
index, by `refl`{.Agda} in each of the two cases. The recovery is needed exactly
once, in the corollary saying every member is an environment, and it never enters
the induction at all.

Three small consequences follow at once. The element for a vector is the
environment set's own construction at the indices the members give, which reads
the fibres off the carrier untruncated. Its graph is the vector's graph. And
anything whose underlying set is a vector's graph already lies in the ambient
environment set, which is why membership in the value reduces to the condition
alone.
<!--zh-->
两侧以两种形式持有一个环境。内层语义持有一个成员向量；递归的取值持有 `L` 的一个元素，其底集是一张图。故这座桥把那个向量取作参数，并附上「该元素**就是**那个向量的图」这条等式，而本章其余一切都被安排成：只有这条等式会四处旅行。

正是这个选择把本章为之而写、要去测量的那份风险化解掉了。周遭环境集只恢复出「某个」以该成员为其图的函数，且带截断；而四条量词子句要的是把「同一个」函数扩张一个条目。改以向量为索引之后，扩张就是底族上的前置，而把一个成员前置到向量上与它逐序号相符，两种情形各由 `refl`{.Agda} 交割。恢复恰好只用一次，用在「每个成员都是一个环境」这条推论里，它压根不进入归纳。

随即有三个小推论。一个向量所对应的元素，就是环境集自己在「诸成员给出的诸索引」处的构造，而那些索引是从载体上不截断地读出的纤维。它的图就是那个向量的图。而凡底集为某向量之图者，本就落在周遭环境集之中，这也是「属于那个取值」何以化归为「只剩那个条件」的原因。
<!--/-->

```agda
  values : ∀ {n} → DB.SM ^ n → Fin n → V ℓ
  values δ i = fst (lookup i δ)

  graph : ∀ {n} → DB.SM ^ n → V ℓ
  graph δ = env (values δ)

  private
    cons-values : ∀ {n} (x : DB.SM) (δ : DB.SM ^ n)
                → cons (fst x) (values δ) ≡ values (x ∷ δ)
    cons-values x δ = funExt (λ { zero → refl ; (suc i) → refl })

    index : ∀ {n} (δ : DB.SM ^ n) → Ix B n
    index δ i = ∈-asFiber {a = values δ i} {b = fst B} (snd (lookup i δ)) .fst

    index-eq : ∀ {n} (δ : DB.SM ^ n) (i : Fin n)
             → ⟪ fst B ⟫↪ (index δ i) ≡ values δ i
    index-eq δ i = ∈-asFiber {a = values δ i} {b = fst B} (snd (lookup i δ)) .snd

  envFor : ∀ {n} → DB.SM ^ n → S
  envFor δ = envS B (index δ)

  envFor-graph : ∀ {n} (δ : DB.SM ^ n) → fst (envFor δ) ≡ graph δ
  envFor-graph δ = cong env (funExt (index-eq δ))

  graph-envSet : ∀ {n} (δ : DB.SM ^ n) (z : S)
               → fst z ≡ graph δ → ⟨ z ∈ˢ envSet B n ⟩
  graph-envSet {n} δ z q = subst (λ w → ⟨ w ∈ fst (envSet B n) ⟩)
    (envFor-graph δ ∙ sym q) (envSet-in B (index δ))

  Sat-cond : ∀ {n} (φ : Formula S n) (δ : DB.SM ^ n) (z : S)
           → fst z ≡ graph δ
           → (z ∈ˢ Sat B φ) ≡ ((z ∷ []) ⊨ cond B φ)
  Sat-cond φ δ z q =
    Sat-mem B φ z ∙ ⇔toPath snd (λ h → graph-envSet δ z q , h)
```

<!--en-->
## Two readings at variable arguments
<!--zh-->
## 两条在变元自变量处的读式
<!--/-->

<!--en-->
The condition reads a term's value and an environment's extension through two
formulas of the model's language, and the clauses below have to read them back.
Both readings are stated the way the environment set chapter's own recovery was,
and for the recorded reason: an adequacy substitution has to be discharged where
its arguments are **variables**, because at a concrete environment it drags the
absoluteness bridge through normalization. So the environment vector and the
three slots are parameters constrained by equations, and a clause supplies its
own frame's slots at the call site, where nothing substitutes any longer.

The term reading has one case per term constructor and the meta-language decides
which, so each is one line of bookkeeping. A constant's reading is the equation
itself. A variable's reading is the graph's functionality, which is the lemma the
environment chapter exists for.
<!--zh-->
那个条件经模型语言的两条公式去读「词项的取值」与「环境的扩张」，而下面诸子句必须把它们读回来。两条读式都按环境集那一章自己的恢复所用的方式陈述，理由也已记录在案：一次充分性代换必须在其自变量是**变元**之处交割，因为写在具体环境上，它会把整座绝对性之桥拖进归一化。故环境向量与三个槽位取作「由等式约束的参数」，而子句在调用点供上它自己那个框架的诸槽，那里已不再发生任何代换。

词项那条读式每个词项构造子一种情形，且由元语言决定是哪一种，故每种只是一行记账。常元的读法就是那条等式本身。变元的读法是那张图的函数性，而那正是环境那一章为之存在的引理。
<!--/-->

```agda
  tmIs-out : ∀ {n k} (t : Term DB.SM n) (δ : DB.SM ^ n) (γ : S ^ k) (vi ei : Fin k)
           → fst (lookup ei γ) ≡ graph δ
           → ⟨ γ ⊨ tmIs (mapTm intoL t) vi ei ⟩
           → fst (lookup vi γ) ≡ fst (⟦ t ⟧ᴮ δ)
  tmIs-out (con c) δ γ vi ei qe h = h
  tmIs-out (var i) δ γ vi ei qe h =
    subst ⟨_⟩ (lookup-spec (values δ) i (fst (lookup vi γ)))
      (subst (λ w → ⟨ pr (# (toℕ i)) (fst (lookup vi γ)) ∈ w ⟩) qe
        (tmIs-var-out i γ vi ei h))

  tmIs-in : ∀ {n k} (t : Term DB.SM n) (δ : DB.SM ^ n) (γ : S ^ k) (vi ei : Fin k)
          → fst (lookup ei γ) ≡ graph δ
          → fst (lookup vi γ) ≡ fst (⟦ t ⟧ᴮ δ)
          → ⟨ γ ⊨ tmIs (mapTm intoL t) vi ei ⟩
  tmIs-in (con c) δ γ vi ei qe q = q
  tmIs-in (var i) δ γ vi ei qe q = tmIs-var-in i γ vi ei
    (subst (λ w → ⟨ pr (# (toℕ i)) (fst (lookup vi γ)) ∈ w ⟩) (sym qe)
      (subst ⟨_⟩ (sym (lookup-spec (values δ) i (fst (lookup vi γ)))) q))

  consAtL-out : ∀ {n k} (δ : DB.SM ^ n) (x : DB.SM) (γ : S ^ k) (ei mi di : Fin k)
              → fst (lookup di γ) ≡ graph δ
              → fst (lookup mi γ) ≡ fst x
              → ⟨ γ ⊨ consAtL ei mi di ⟩
              → fst (lookup ei γ) ≡ graph (x ∷ δ)
  consAtL-out δ x γ ei mi di qd qm h =
      subst ⟨_⟩ (consAtL-adequate ei mi di γ (values δ) qd) h
    ∙ cong env (cong (λ w → cons w (values δ)) qm ∙ cons-values x δ)

  consAtL-in : ∀ {n k} (δ : DB.SM ^ n) (x : DB.SM) (γ : S ^ k) (ei mi di : Fin k)
             → fst (lookup di γ) ≡ graph δ
             → fst (lookup mi γ) ≡ fst x
             → fst (lookup ei γ) ≡ graph (x ∷ δ)
             → ⟨ γ ⊨ consAtL ei mi di ⟩
  consAtL-in δ x γ ei mi di qd qm q =
    subst ⟨_⟩ (sym (consAtL-adequate ei mi di γ (values δ) qd))
      (q ∙ sym (cong env (cong (λ w → cons w (values δ)) qm ∙ cons-values x δ)))
```

<!--en-->
## The bridge
<!--zh-->
## 那座桥
<!--/-->

<!--en-->
The statement, once, as a named property of a formula: at every inner
environment, and at every element of `L` whose underlying set is that
environment's graph, membership in the value is satisfaction. It is a **path of
truth values**, not an equivalence of types and not an identity of sets. A path
is the currency both sides are already stated in, so this one composes with the
value's membership equation on the left and with the definable powerset's
specification on the right by nothing but transitivity. A set identity is not
available as the primitive, because the set on the other side is not built
independently: constructing it is what the recursion does.

The ten clauses are then one step each, and taking each as a lemma over the
subformulas' properties rather than as a clause of the induction costs nothing
and lets each be measured on its own. The four propositional cases are congruences: the
condition names the subvalues as constants, and the object language's connective
is the truth algebra's, so there is no translation layer to cross.
<!--zh-->
陈述只写一次，作为一条公式的一项具名性质：在每个内层环境处，以及在每个「底集是该环境之图」的 `L` 的元素处，「属于那个取值」就是「满足」。它是一条**真值之间的道路**，不是类型之间的等价，也不是集合之间的等同。道路正是两侧本来就采用的通货，故这一条向左与那个取值的成员等式、向右与可定义幂集的规格，仅凭传递性即可接合。集合等同不能充当原语，因为另一侧那个集合并非独立造出：造它正是这场递归所做的事。

于是十条子句各是一步；把每一步取作「关于诸子公式之性质的引理」而非「归纳的一条子句」，不花任何代价，却让每一步都能被单独测量。命题的那四条是同余：那个条件把诸子取值以常元点名，而对象语言的联结词就是真值代数的联结词，中间没有翻译层要跨。
<!--/-->

```agda
  Adequate : ∀ {n} → Formula DB.SM n → Type (ℓ-suc (ℓ-suc ℓ))
  Adequate {n} φ = (δ : DB.SM ^ n) (z : S) → fst z ≡ graph δ
                 → (z ∈ˢ Sat B (mapFo intoL φ)) ≡ (δ ⊨ᴮ φ)


  step⊥ : ∀ {n} → Adequate {n} ⊥̇
  step⊥ δ z q = Sat-cond ⊥̇ δ z q

  step∧ : ∀ {n} (a b : Formula DB.SM n)
        → Adequate a → Adequate b → Adequate (a ∧̇ b)
  step∧ a b ia ib δ z q = Sat-cond (mapFo intoL (a ∧̇ b)) δ z q
    ∙ cong₂ _⊓_ (ia δ z q) (ib δ z q)

  step∨ : ∀ {n} (a b : Formula DB.SM n)
        → Adequate a → Adequate b → Adequate (a ∨̇ b)
  step∨ a b ia ib δ z q = Sat-cond (mapFo intoL (a ∨̇ b)) δ z q
    ∙ cong₂ _⊔_ (ia δ z q) (ib δ z q)

  step⇒ : ∀ {n} (a b : Formula DB.SM n)
        → Adequate a → Adequate b → Adequate (a ⇒̇ b)
  step⇒ a b ia ib δ z q = Sat-cond (mapFo intoL (a ⇒̇ b)) δ z q
    ∙ cong₂ _⇒_ (ia δ z q) (ib δ z q)

```

<!--en-->
### The atoms
<!--zh-->
### 两个原子
<!--/-->

<!--en-->
An atom's condition binds the two values and then relates them, so reading it
back is the term reading twice and a transport. The other direction has to
produce the two witnesses, and it produces the term's own value carried across
the class inclusion, which is why its two term obligations are `refl`{.Agda}: the
witness was chosen to have the value the reading asks for.
<!--zh-->
一个原子的条件先绑定那两个取值、再把它们关联起来，故把它读回来就是两次词项读式加一次搬运。另一方向必须交出那两个见证，而它交出的是词项自己的取值经类包含运过来的结果，故它那两项词项义务都是 `refl`{.Agda}：见证正是照读式所要的取值挑的。
<!--/-->

```agda
  step∈ : ∀ {n} (t u : Term DB.SM n) → Adequate (t ∈̇ u)
  step∈ t u δ z q = Sat-cond (mapFo intoL (t ∈̇ u)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
    U = ⟦ u ⟧ᴮ δ
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ∈̇ u)) ⟩ → ⟨ fst T ∈ fst U ⟩
    fwd h = PT.rec (snd (fst T ∈ fst U))
      (λ { (v , (w , (ht , (hu , r)))) → subst2 (λ p s → ⟨ p ∈ s ⟩)
        (tmIs-out t δ (w ∷ v ∷ z ∷ []) (suc zero) (suc (suc zero)) q ht)
        (tmIs-out u δ (w ∷ v ∷ z ∷ []) zero (suc (suc zero)) q hu)
        r })
      (cond∈-out B (mapTm intoL t) (mapTm intoL u) z h)
    bwd : ⟨ fst T ∈ fst U ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ∈̇ u)) ⟩
    bwd r = cond∈-in B (mapTm intoL t) (mapTm intoL u) z
      ∣ intoL T , (intoL U
      , ( tmIs-in t δ (intoL U ∷ intoL T ∷ z ∷ []) (suc zero) (suc (suc zero)) q refl
        , ( tmIs-in u δ (intoL U ∷ intoL T ∷ z ∷ []) zero (suc (suc zero)) q refl
          , r ))) ∣₁

  step≐ : ∀ {n} (t u : Term DB.SM n) → Adequate (t ≐ u)
  step≐ t u δ z q = Sat-cond (mapFo intoL (t ≐ u)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
    U = ⟦ u ⟧ᴮ δ
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ≐ u)) ⟩ → fst T ≡ fst U
    fwd h = PT.rec (snd (intoL T ≈ˢ intoL U))
      (λ { (v , (w , (ht , (hu , r)))) →
          sym (tmIs-out t δ (w ∷ v ∷ z ∷ []) (suc zero) (suc (suc zero)) q ht)
        ∙ r
        ∙ tmIs-out u δ (w ∷ v ∷ z ∷ []) zero (suc (suc zero)) q hu })
      (cond≐-out B (mapTm intoL t) (mapTm intoL u) z h)
    bwd : fst T ≡ fst U → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (t ≐ u)) ⟩
    bwd r = cond≐-in B (mapTm intoL t) (mapTm intoL u) z
      ∣ intoL T , (intoL U
      , ( tmIs-in t δ (intoL U ∷ intoL T ∷ z ∷ []) (suc zero) (suc (suc zero)) q refl
        , ( tmIs-in u δ (intoL U ∷ intoL T ∷ z ∷ []) zero (suc (suc zero)) q refl
          , r ))) ∣₁
```

<!--en-->
### The two unbounded quantifiers
<!--zh-->
### 两个无界量词
<!--/-->

<!--en-->
Here is where the two sides could have failed to meet, and where they meet for
free. The condition draws its witness from the carrier and asserts that the
subvalue holds at the extended environment; the inner semantics quantifies over
the restricted carrier, whose elements are exactly a member paired with its
membership. So each direction repackages one pair and applies the extension
reading, and the environment the subformula is evaluated in is the one this
chapter built for the extended vector. Nothing is truncated that was not already,
and no arity carries a side condition.
<!--zh-->
这里正是两侧本可能对不上的地方，而它们在此免费对上。那个条件从载体中取见证，并断言子取值在扩张后的环境处成立；内层语义则对限制载体作量化，而它的元素恰是「一个成员配上它的隶属证明」。故每个方向只是把一个对重新打包再施用那条扩张读式，而子公式求值所在的环境，就是本章为扩张后的向量造出的那一个。没有任何本来不截断的东西被截断，也没有哪个元数背上附加条件。
<!--/-->

```agda
  step∃ : ∀ {n} (a : Formula DB.SM (suc n)) → Adequate a → Adequate (∃̇ a)
  step∃ a ia δ z q = Sat-cond (mapFo intoL (∃̇ a)) δ z q ∙ ⇔toPath fwd bwd
    where
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇ a)) ⟩ → ⟨ δ ⊨ᴮ (∃̇ a) ⟩
    fwd h = PT.rec squash₁
      (λ { (x , (x∈B , (e , (hc , he)))) → ∣ (fst x , x∈B)
         , subst ⟨_⟩ (ia ((fst x , x∈B) ∷ δ) e
             (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ z ∷ [])
               zero (suc zero) (suc (suc zero)) q refl hc)) he ∣₁ })
      (cond∃-out B (mapFo intoL a) z h)
    bwd : ⟨ δ ⊨ᴮ (∃̇ a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇ a)) ⟩
    bwd h = cond∃-in B (mapFo intoL a) z (PT.map
      (λ { (x , ha) → intoL x , (snd x , (envFor (x ∷ δ)
         , ( consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ z ∷ [])
               zero (suc zero) (suc (suc zero)) q refl (envFor-graph (x ∷ δ))
           , subst ⟨_⟩ (sym (ia (x ∷ δ) (envFor (x ∷ δ))
               (envFor-graph (x ∷ δ)))) ha ))) })
      h)

  step∀ : ∀ {n} (a : Formula DB.SM (suc n)) → Adequate a → Adequate (∀̇ a)
  step∀ a ia δ z q = Sat-cond (mapFo intoL (∀̇ a)) δ z q ∙ ⇔toPath fwd bwd
    where
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇ a)) ⟩ → ⟨ δ ⊨ᴮ (∀̇ a) ⟩
    fwd h x = subst ⟨_⟩ (ia (x ∷ δ) (envFor (x ∷ δ)) (envFor-graph (x ∷ δ)))
      (cond∀-out B (mapFo intoL a) z h (intoL x) (envFor (x ∷ δ)) (snd x)
        (consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ z ∷ [])
          zero (suc zero) (suc (suc zero)) q refl (envFor-graph (x ∷ δ))))
    bwd : ⟨ δ ⊨ᴮ (∀̇ a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇ a)) ⟩
    bwd k = cond∀-in B (mapFo intoL a) z
      (λ x e x∈B hc → subst ⟨_⟩
        (sym (ia ((fst x , x∈B) ∷ δ) e
          (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ z ∷ [])
            zero (suc zero) (suc (suc zero)) q refl hc)))
        (k (fst x , x∈B)))
```

<!--en-->
### The two bounded quantifiers
<!--zh-->
### 两个有界量词
<!--/-->

<!--en-->
These two are the reason the right-hand side is the inner semantics. The
condition binds the bounding term's value and then guards the bound variable
twice, by the carrier and by that value. The inner semantics guards it twice as
well, and for the same two reasons, so the guards line up one for one and the
clause is the unbounded one plus a term reading. Against the relativized reading
there would be one guard on the left and two on the right, and closing that gap
needs the bound contained in the carrier: a hypothesis at every bounded
quantifier, at every arity, all the way down.
<!--zh-->
这两条正是右端取内层语义的理由。那个条件先绑定界项的取值，再对被绑变元设两道防：由载体、由那个取值。内层语义同样设两道，且理由相同，故两处设防一一对齐，这条子句便是无界那条再加一次词项读式。若对着相对化那种读法，左边一道防、右边两道，而补上这道缺口需要「界含于载体」：那是每个有界量词、每个元数、一路到底的一条前提。
<!--/-->

```agda
  step∃∈ : ∀ {n} (t : Term DB.SM n) (a : Formula DB.SM (suc n))
         → Adequate a → Adequate (∃̇∈ t a)
  step∃∈ t a ia δ z q = Sat-cond (mapFo intoL (∃̇∈ t a)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇∈ t a)) ⟩ → ⟨ δ ⊨ᴮ (∃̇∈ t a) ⟩
    fwd h = PT.rec squash₁
      (λ { (w , (hw , hb)) → PT.map
        (λ { (x , ((x∈B , x∈w) , (e , (hc , he)))) → (fst x , x∈B)
           , ( subst (λ s → ⟨ fst x ∈ s ⟩)
                 (tmIs-out t δ (w ∷ z ∷ []) zero (suc zero) q hw) x∈w
             , subst ⟨_⟩ (ia ((fst x , x∈B) ∷ δ) e
                 (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ w ∷ z ∷ [])
                   zero (suc zero) (suc (suc (suc zero))) q refl hc)) he ) })
        hb })
      (cond∃∈-out B (mapTm intoL t) (mapFo intoL a) z h)
    bwd : ⟨ δ ⊨ᴮ (∃̇∈ t a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∃̇∈ t a)) ⟩
    bwd h = cond∃∈-in B (mapTm intoL t) (mapFo intoL a) z (PT.map
      (λ { (x , (hx , ha)) → intoL T
         , ( tmIs-in t δ (intoL T ∷ z ∷ []) zero (suc zero) q refl
           , ∣ intoL x , ((snd x , hx) , (envFor (x ∷ δ)
             , ( consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ intoL T ∷ z ∷ [])
                   zero (suc zero) (suc (suc (suc zero))) q refl
                   (envFor-graph (x ∷ δ))
               , subst ⟨_⟩ (sym (ia (x ∷ δ) (envFor (x ∷ δ))
                   (envFor-graph (x ∷ δ)))) ha ))) ∣₁ ) })
      h)

  step∀∈ : ∀ {n} (t : Term DB.SM n) (a : Formula DB.SM (suc n))
         → Adequate a → Adequate (∀̇∈ t a)
  step∀∈ t a ia δ z q = Sat-cond (mapFo intoL (∀̇∈ t a)) δ z q ∙ ⇔toPath fwd bwd
    where
    T = ⟦ t ⟧ᴮ δ
    fwd : ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇∈ t a)) ⟩ → ⟨ δ ⊨ᴮ (∀̇∈ t a) ⟩
    fwd h x hx = subst ⟨_⟩ (ia (x ∷ δ) (envFor (x ∷ δ)) (envFor-graph (x ∷ δ)))
      (cond∀∈-out B (mapTm intoL t) (mapFo intoL a) z h (intoL T)
        (tmIs-in t δ (intoL T ∷ z ∷ []) zero (suc zero) q refl)
        (intoL x) (envFor (x ∷ δ)) (snd x) hx
        (consAtL-in δ x (envFor (x ∷ δ) ∷ intoL x ∷ intoL T ∷ z ∷ [])
          zero (suc zero) (suc (suc (suc zero))) q refl (envFor-graph (x ∷ δ))))
    bwd : ⟨ δ ⊨ᴮ (∀̇∈ t a) ⟩ → ⟨ (z ∷ []) ⊨ cond B (mapFo intoL (∀̇∈ t a)) ⟩
    bwd k = cond∀∈-in B (mapTm intoL t) (mapFo intoL a) z
      (λ w hw x e x∈B x∈w hc → subst ⟨_⟩
        (sym (ia ((fst x , x∈B) ∷ δ) e
          (consAtL-out δ (fst x , x∈B) (e ∷ x ∷ w ∷ z ∷ [])
            zero (suc zero) (suc (suc (suc zero))) q refl hc)))
        (k (fst x , x∈B) (subst (λ s → ⟨ fst x ∈ s ⟩)
          (tmIs-out t δ (w ∷ z ∷ []) zero (suc zero) q hw) x∈w)))
```

<!--en-->
### The induction
<!--zh-->
### 那次归纳
<!--/-->

<!--en-->
Ten steps, one line each, and the recursion is the formula's own.
<!--zh-->
十步，一步一行，而那场递归就是公式自己的递归。
<!--/-->

```agda
  Sat-spec : ∀ {n} (φ : Formula DB.SM n) → Adequate φ
  Sat-spec (t ∈̇ u)  = step∈ t u
  Sat-spec (t ≐ u)  = step≐ t u
  Sat-spec (a ∧̇ b)  = step∧ a b (Sat-spec a) (Sat-spec b)
  Sat-spec (a ∨̇ b)  = step∨ a b (Sat-spec a) (Sat-spec b)
  Sat-spec (a ⇒̇ b)  = step⇒ a b (Sat-spec a) (Sat-spec b)
  Sat-spec ⊥̇        = step⊥
  Sat-spec (∃̇ a)    = step∃ a (Sat-spec a)
  Sat-spec (∀̇ a)    = step∀ a (Sat-spec a)
  Sat-spec (∀̇∈ t a) = step∀∈ t a (Sat-spec a)
  Sat-spec (∃̇∈ t a) = step∃∈ t a (Sat-spec a)
```

<!--en-->
## And every member is one
<!--zh-->
## 而每个成员都是一个
<!--/-->

<!--en-->
The bridge above reads membership at an environment named in advance. The other
half of "is the set of the environments satisfying it" is that a member is
nothing else: the value sits inside the ambient environment set, so any member is
the graph of some function into the carrier's members, and turning that function
into a vector puts it back in the bridge's hands. The recovery is truncated and
stays so, which costs nothing here because the conclusion is an existence
statement anyway.

The vector is built by a recursion of two lines rather than by the library's
conversion between finite functions and vectors. That is a measurement, not a
preference: the library's round-trip identity walled the chapter at over eight
minutes, and the same statement written by hand costs no measurable time.
<!--zh-->
上面那座桥读的是「在事先点名的环境处」的隶属。而「它就是满足它的诸环境之集」的另一半是：一个成员再无别的可能。那个取值坐落在周遭环境集之内，故任一成员都是某个「到载体诸成员」的函数之图，而把那个函数变成向量，就又交回到桥的手里。那次恢复带截断，且保持带截断，此处不花代价，因为结论本来就是一句存在陈述。

那个向量由两行递归造出，而不是用库里「有穷函数与向量之间」的转换。这是一次测量而非偏好：库那条往返等式把本章卡在八分钟以上，而同一条陈述手写出来则快到测不出。
<!--/-->

```agda
  private
    inB : (m : ⟪ fst B ⟫) → ⟨ ⟪ fst B ⟫↪ m ∈ fst B ⟩
    inB m = ∈∈ₛ {a = ⟪ fst B ⟫↪ m} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ m)

    tab : ∀ {n} → Ix B n → DB.SM ^ n
    tab {zero} g = []
    tab {suc n} g = (⟪ fst B ⟫↪ (g zero) , inB (g zero)) ∷ tab (λ i → g (suc i))

    tab-values : ∀ {n} (g : Ix B n) → values (tab g) ≡ (λ i → ⟪ fst B ⟫↪ (g i))
    tab-values {zero} g = funExt (λ ())
    tab-values {suc n} g = funExt
      (λ { zero → refl
         ; (suc i) → funExt⁻ (tab-values (λ j → g (suc j))) i })

    tab-graph : ∀ {n} (g : Ix B n) → graph (tab g) ≡ fst (envS B g)
    tab-graph g = cong env (tab-values g)

  envSet-vectors : ∀ {n} (z : S) → ⟨ z ∈ˢ envSet B n ⟩
                 → ∥ Σ[ δ ∈ DB.SM ^ n ] (fst z ≡ graph δ) ∥₁
  envSet-vectors {n} z h = PT.map
    (λ { (g , qg) → tab g , qg ∙ sym (tab-graph g) }) (envSet-out B n z h)

  Sat-out : ∀ {n} (φ : Formula DB.SM n) (z : S)
          → ⟨ z ∈ˢ Sat B (mapFo intoL φ) ⟩
          → ∥ (Σ[ δ ∈ DB.SM ^ n ] ((fst z ≡ graph δ) × ⟨ δ ⊨ᴮ φ ⟩)) ∥₁
  Sat-out {n} φ z h = PT.map
    (λ { (g , qg) → tab g , (qg ∙ sym (tab-graph g)
       , subst ⟨_⟩ (Sat-spec φ (tab g) z (qg ∙ sym (tab-graph g))) h) })
    (envSet-out B n z (subst ⟨_⟩ (Sat-mem B (mapFo intoL φ) z) h .fst))
```

<!--en-->
## Against the definable powerset
<!--zh-->
## 对着可定义幂集
<!--/-->

<!--en-->
And the statement the goal exists for. A subset definable in the world `(B, ∈)`
by a formula with parameters from `B` collects exactly the members whose
one-entry environment lies in the recursion's value at the same formula,
relabelled into the meta-language. The proof is the three-step chain the definable
powerset chapter already runs for absoluteness, with this chapter's bridge in the
place absoluteness held: the specification of `defSet`{.Agda}, then the
relabelling, which moves meaning not at all, then the bridge.

Two pieces of bookkeeping, both syntactic. Relabelling twice in a row is
relabelling along the composite, which the relabelling chapter proves once for
every domain; and the one-entry environment named by a member is the graph of the
one-entry vector, which is the same equation at length one.
<!--zh-->
以及本目标为之存在的那条陈述。在世界 `(B, ∈)` 中由一条带 `B` 中参数的公式可定义的子集，收集的恰是那些成员：它们的单条目环境落在「同一条公式重标进元语言后」的递归取值之中。证明就是可定义幂集那一章为绝对性已经跑过的三步链，只是把本章这座桥放在当初绝对性所在的位置：`defSet`{.Agda} 的规格、然后重标 (它分毫不动含义)、然后这座桥。

两处记账，皆属句法。连续重标两次就是沿复合重标，而那件事重标那一章已为所有常量域一次证清；而由一个成员点名的单条目环境，就是单条目向量的图，那是同一条等式落在长度一处。
<!--/-->

```agda
  private
    mapFo-fuse : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n)
               → mapFo intoL (mapFo DB.ι ψ) ≡ mapFo asConst ψ
    mapFo-fuse = mapFo-comp DB.ι intoL

    graph-single : (m : ⟪ fst B ⟫)
                 → fst (envS B (λ _ → m)) ≡ graph (DB.ι m ∷ [])
    graph-single m = cong env (funExt (λ { zero → refl ; (suc ()) }))

  Sat-small-spec : ∀ {n} (ψ : Formula ⟪ fst B ⟫ n) (δ : DB.SM ^ n) (z : S)
                 → fst z ≡ graph δ
                 → (z ∈ˢ Sat B (mapFo asConst ψ)) ≡ (δ ⊨ᴮ mapFo DB.ι ψ)
  Sat-small-spec ψ δ z q = cong (λ χ → z ∈ˢ Sat B χ) (sym (mapFo-fuse ψ))
    ∙ Sat-spec (mapFo DB.ι ψ) δ z q

  defSet-Sat : (ψ : Formula ⟪ fst B ⟫ 1) (m : ⟪ fst B ⟫)
             → (⟪ fst B ⟫↪ m ∈ DB.defSet ψ)
             ≡ (envS B (λ _ → m) ∈ˢ Sat B (mapFo asConst ψ))
  defSet-Sat ψ m =
      DB.defSet-mem ψ m
    ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) DB.𝒮M DB.ι id ψ (DB.ι m ∷ []))
    ∙ sym (Sat-spec (mapFo DB.ι ψ) (DB.ι m ∷ []) (envS B (λ _ → m))
             (graph-single m))
    ∙ cong (λ χ → envS B (λ _ → m) ∈ˢ Sat B χ) (mapFo-fuse ψ)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`Sat-spec`{.Agda} is the adequacy the recursion was missing: at every environment
over the carrier, membership in the value is satisfaction in the world `(B, ∈)`,
as a path of truth values, and `Sat-out`{.Agda} adds that a member is nothing
else. `defSet-Sat`{.Agda} spends both on the definable powerset, which is why the
statement was owed: an internal definable powerset read off this recursion now
has something it provably agrees with.

Three measurements are worth keeping. The registered risk, the coherence between
the truncated recovery of an environment and the extension four clauses perform,
**did not fire, and the reason is a change of statement**: indexing the bridge by
the inner environment vector makes extension consing on the underlying family, so
the coherence is two `refl`{.Agda} branches under one `funExt`{.Agda}, shared by
all four quantifier clauses and paid at no arity. The recovery is confined to the
corollary. The whole chapter, ten steps and both corollaries, checks in about
two seconds. And the one wall this chapter met came from neither the recursion nor
the model: converting a finite function into a vector through the library's
round-trip identity ran past eight minutes, while the same two statements written
as a two-line recursion cost nothing at all.

What the bridge does **not** say, and which goal owes it: it is stated for
formulas whose constants are members of the carrier, so it does not compare the
value at a formula naming an arbitrary element of `L`. That is not a gap in the
proof but the shape of the statement, because a constant outside the carrier has
no value in the inner world; reading such a formula requires the ambient
relativized semantics instead, where the two bounded-quantifier clauses acquire
the hypothesis that the bound lies inside the carrier. No consumer wants that
reading today.
<!--zh-->
`Sat-spec`{.Agda} 就是那场递归先前欠着的充分性：在载体之上的每个环境处，「属于那个取值」就是「在世界 `(B, ∈)` 中被满足」，且是一条真值之间的道路；`Sat-out`{.Agda} 再补上「一个成员再无别的可能」。`defSet-Sat`{.Agda} 把两者花在可定义幂集上，而那正是这条陈述被欠着的理由：如今从这场递归读出的内部可定义幂集，有了一个可证与之相符的对象。

有三次测量值得留存。登记在案的那份风险，即「环境的截断式恢复」与「四条子句所作的扩张」之间的相干性，**没有引爆，而理由是换了陈述**：把这座桥以内层环境向量为索引之后，扩张就是底族上的前置，于是相干性只是一次 `funExt`{.Agda} 之下的两条 `refl`{.Agda} 分支，四条量词子句共享，且不在任何元数上付账。恢复被关进那条推论里。整章十步加两条推论，约两秒检查完毕。而本章遇到的唯一一堵墙，既不来自那场递归、也不来自模型：用库里「有穷函数与向量」的往返等式去作转换，跑过了八分钟；而把同样两条陈述写成两行递归，则分文不花。

这座桥**没有**说的，以及这笔账该记在哪个目标上：它是对「常元皆为载体成员」的那些公式陈述的，故它不比较「点名了 `L` 的任意元素」的公式处的取值。那不是证明的缺口，而是陈述的形状，因为载体之外的常元在内层世界里没有取值；读那样一条公式要改用周遭的相对化语义，而在那里，两条有界量词子句会背上「界落在载体之内」这条前提。今天没有任何消费者要那种读法。
<!--/-->
