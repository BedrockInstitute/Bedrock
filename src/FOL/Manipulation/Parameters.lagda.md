# Abstracting the parameters

<!--en-->
A constant is how an ambient set enters a formula, and the role it plays there is
that of a **parameter**. Every use the book makes of formulas as data has had to
work around them: constants are as many as there are sets, so a syntax with
constants can be neither counted nor coded, and the parameter-free formulas were
introduced for exactly that reason. This chapter builds the trade that turns one
into the other. A formula with parameters becomes a parameter-free formula of
higher arity together with a vector of the constants it mentioned, and
satisfaction is preserved when those constants are supplied in the **environment**
instead of in the syntax. Nothing is lost and nothing is added: the two formulas
say the same thing at the same points, and all that changes is where the
parameters sit.
<!--zh-->
常量是外部集合进入公式的通道，而它在那里扮演的角色叫作**参数**。本书凡把公式当数据用，都得绕开常量：常量与集合一样多，带常量的语法既数不得也编不得码，无参公式正是为此而设。本章造的就是把前者换成后者的那笔交易。带参数的公式变成一条元数更高的无参公式，外加一个向量装着它提到的那些常量；而当那些常量改由**环境**、而非语法供给时，满足关系保持不变。无一丢失，无一添加：两条公式在相同的点上说相同的话，变的只是参数坐在哪里。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.Parameters where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import FOL.Manipulation.Occurrences using
  ( countTm; countFo; constantsTm; constantsFo; padRight; padLeft
  ; lookup-padRight; lookup-padLeft; lookup-map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _++_; map )
import Cubical.Data.Empty as Empty
```

<!--en-->
## The abstraction
<!--zh-->
## 抽象
<!--/-->

<!--en-->
The abstraction is written once in a generic form and instantiated once. The
generic form takes a **placement**: a function `θ` assigning to each
constant-occurrence of the formula a variable of the target context, and it
returns the formula with every constant replaced by the variable `θ` names for
it. The target's arity is `n + k` for a `k` the placement is free to choose, so
the generic form abstracts into a context with room to spare.

Genericity here is not decoration; it is what keeps the two-part constructors from
needing a second pass. A conjunction's occurrences are its left operand's followed
by its right operand's, so the two operands are abstracted under the placements
`θ ∘ padRight` and `θ ∘ padLeft`, **composed before the traversal** rather than
recovered afterwards by renaming the two halves into the joined context. One pass
over the formula, no weakening lemma, and each of the ten clauses is the shape
the corresponding clause of every other structural recursion in this part has.
Under a binder the placement gains a `suc`, which is the parameter block riding one
index higher, and nothing else happens at all.
<!--zh-->
抽象以泛型形式写一遍，再实例化一次。泛型形式收一件**安置**：一个函数 `θ`，为公式的每次常量出现指派目标语境中的一个变量；它返回把每个常量换成 `θ` 为它点名的那个变量之后的公式。目标的元数是 `n + k`，其中 `k` 由安置自由选取，故泛型形式抽象进的语境留有余地。

此处的泛型不是装饰，而是让两部分的构造子免于第二趟遍历的关键。合取的诸次出现，是左合取项的诸次出现后接右合取项的诸次出现，于是两个合取项在安置 `θ ∘ padRight` 与 `θ ∘ padLeft` 之下被抽象，而这两件安置是在**遍历之前复合**的，不是事后把两半重标进合并语境再补回来。对公式只走一趟，不需要弱化引理，十条子句各自的形状就是本部其他每一场结构递归的对应子句的形状。约束子之下，安置多得一个 `suc`，那正是参数块整体高一个序号，除此之外什么也没发生。
<!--/-->

```agda
placeTm : ∀ {ℓz ℓc} {K : Type ℓc} {n k} (t : Term K n)
        → (Fin (countTm t) → Fin (n + k)) → Term (⊥* {ℓz}) (n + k)
placeTm         (con c) θ = var (θ zero)
placeTm {k = k} (var i) θ = var (padRight k i)

placeFo : ∀ {ℓz ℓc} {K : Type ℓc} {n k} (φ : Formula K n)
        → (Fin (countFo φ) → Fin (n + k)) → Formula (⊥* {ℓz}) (n + k)
placeFo (t ∈̇ u)  θ = placeTm t (λ i → θ (padRight (countTm u) i))
                   ∈̇ placeTm u (λ j → θ (padLeft (countTm t) j))
placeFo (t ≐ u)  θ = placeTm t (λ i → θ (padRight (countTm u) i))
                   ≐ placeTm u (λ j → θ (padLeft (countTm t) j))
placeFo (φ ∧̇ ψ)  θ = placeFo φ (λ i → θ (padRight (countFo ψ) i))
                   ∧̇ placeFo ψ (λ j → θ (padLeft (countFo φ) j))
placeFo (φ ∨̇ ψ)  θ = placeFo φ (λ i → θ (padRight (countFo ψ) i))
                   ∨̇ placeFo ψ (λ j → θ (padLeft (countFo φ) j))
placeFo (φ ⇒̇ ψ)  θ = placeFo φ (λ i → θ (padRight (countFo ψ) i))
                   ⇒̇ placeFo ψ (λ j → θ (padLeft (countFo φ) j))
placeFo ⊥̇        θ = ⊥̇
placeFo (∃̇ φ)    θ = ∃̇ placeFo φ (λ j → suc (θ j))
placeFo (∀̇ φ)    θ = ∀̇ placeFo φ (λ j → suc (θ j))
placeFo (∀̇∈ t φ) θ = ∀̇∈ (placeTm t (λ i → θ (padRight (countFo φ) i)))
                        (placeFo φ (λ j → suc (θ (padLeft (countTm t) j))))
placeFo (∃̇∈ t φ) θ = ∃̇∈ (placeTm t (λ i → θ (padRight (countFo φ) i)))
                        (placeFo φ (λ j → suc (θ (padLeft (countTm t) j))))
```

<!--en-->
The instance is the one the rest of the book will name: take the budget to be
exactly the occurrence count and the placement to be the block that follows the
variables. This is the abstraction proper, and its type is the chapter's headline:
a formula over `K` with `n` free variables becomes a parameter-free formula with
`n + countFo φ` of them.
<!--zh-->
实例就是本书余下部分要点名的那一个：预算取作恰好的出现次数，安置取作紧随变量之后的那一块。这才是名副其实的抽象，它的类型就是本章的标题句：`K` 上带 `n` 个自由变量的公式，变成带 `n + countFo φ` 个自由变量的无参公式。
<!--/-->

```agda
absFo : ∀ {ℓz ℓc} {K : Type ℓc} {n} (φ : Formula K n) → Formula (⊥* {ℓz}) (n + countFo φ)
absFo {n = n} φ = placeFo φ (padLeft n)
```

<!--en-->
## Adequacy
<!--zh-->
## 充分性
<!--/-->

<!--en-->
Meaning is checked against the generic semantics, at an arbitrary truth algebra, an
arbitrary structure, and an arbitrary constant interpretation. Two satisfactions
are in scope at once and are told apart by a mark: `⊨` is the original's, read at
the interpretation `ι`, and `⊨₀` is the abstraction's, read at the empty constant
domain, where the interpretation has nothing to do and the library's eliminator
says so.
<!--zh-->
含义对着泛型语义检验，真值代数、结构与常量解释都任意。两套满足关系同时在场，由标记区分：`⊨` 属于原公式，在解释 `ι` 处读；`⊨₀` 属于抽象，在空常量域处读，那里解释无事可做，库的消去子把这件事说了出来。
<!--/-->

```agda
module _ {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') (𝒮 : ZFStructure 𝕋) where

  open TruthAlgebra 𝕋
  open ZFStructure 𝒮

  private module Sem = FOL.Semantics 𝕋 𝒮
  open Sem using ( _^_ )

  module _ {ℓz ℓc} {K : Type ℓc} (ι : K → S) where

    open Sem.At K ι using ( _⊨_; ⟦_⟧ )
    open Sem.At (⊥* {ℓz}) Empty.rec* using ()
      renaming ( _⊨_ to _⊨₀_ ; ⟦_⟧ to ⟦_⟧₀ )
```

<!--en-->
The statement is generic in the placement, and it has to be, because the
recursion's placements are built at the recursive calls. It is stated at a
**variable** environment `γ` and a **variable** parameter environment `σ`,
constrained by one hypothesis: at every occurrence, the slot the placement names
holds the interpretation of the constant the collection recorded there. That
hypothesis is the whole content of "the constants are supplied in the environment",
and stating it as a hypothesis rather than substituting a concrete environment is
what keeps every clause from normalizing a vector.

Splitting the hypothesis is the only bookkeeping the two-part constructors need,
and each half is one composition with a pad law.
<!--zh-->
陈述对安置泛型，也必须如此，因为递归的诸安置是在递归调用处造出来的。它陈述在**变元**环境 `γ` 与**变元**参数环境 `σ` 处，受一条假设约束：在每次出现处，安置所点名的那个位装着收集在那里记下的常量的解释。这条假设就是「常量由环境供给」的全部内容，而把它取作假设、而不是代入一个具体环境，正是让每条子句都不必归一化一个向量的原因。

拆分这条假设是两部分的构造子唯一需要的记账，每一半都是一次与补位定律的复合。
<!--/-->

```agda
    private
      leftHalf : ∀ {n k a b} (θ : Fin (a + b) → Fin (n + k))
                 (γ : S ^ n) (σ : S ^ k) (p : Vec K a) (q : Vec K b)
               → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (p ++ q)))
               → (∀ i → lookup (θ (padRight b i)) (γ ++ σ) ≡ ι (lookup i p))
      leftHalf θ γ σ p q h i = h (padRight _ i) ∙ cong ι (lookup-padRight p q i)

      rightHalf : ∀ {n k} a {b} (θ : Fin (a + b) → Fin (n + k))
                  (γ : S ^ n) (σ : S ^ k) (p : Vec K a) (q : Vec K b)
                → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (p ++ q)))
                → (∀ j → lookup (θ (padLeft a j)) (γ ++ σ) ≡ ι (lookup j q))
      rightHalf a θ γ σ p q h j = h (padLeft a j) ∙ cong ι (lookup-padLeft a p q j)
```

<!--en-->
Terms first, two cases and both immediate. A constant's value is what the
hypothesis says the slot holds; a variable's value is untouched, and the pad law
finds it again in the extended environment.
<!--zh-->
先词项，两个情形，都是当即成立。常量的取值就是假设所说那个位装着的东西；变量的取值原封不动，而补位定律在扩张后的环境中重新找到它。
<!--/-->

```agda
    ⟦⟧-place : ∀ {n k} (t : Term K n) (θ : Fin (countTm t) → Fin (n + k))
               (γ : S ^ n) (σ : S ^ k)
             → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsTm t)))
             → ⟦ t ⟧ γ ≡ ⟦ placeTm t θ ⟧₀ (γ ++ σ)
    ⟦⟧-place (con c) θ γ σ h = sym (h zero)
    ⟦⟧-place (var i) θ γ σ h = sym (lookup-padRight γ σ i)
```

<!--en-->
Then the twelve cases of the induction, ten formula cases here and the two
term cases just discharged. Every primitive propositional clause is a congruence, because
the semantics assigns its constructor exactly the truth algebra's
operation and there is no translation layer to cross. The four binding clauses
push a value onto the environment and appeal to the induction hypothesis at the
extended one, and the hypothesis about the parameter slots travels **unchanged**:
consing on the left and shifting the placement by `suc` cancel each other by
computation, so the binders need no lemma of their own. The two bounded clauses
split, term on the left and body on the right, exactly as their constructors do.
<!--zh-->
然后是归纳的十二个情形，十个公式情形在此，两个词项情形刚已交割。命题的每条原语子句都是同余，因为语义给每个构造子指派的恰是真值代数的对应运算，中间没有翻译层要跨。四条约束子句向环境压入一个取值，并在扩张后的环境处援引归纳假设，而关于诸参数位的那条假设**原样**通行：左侧的前置与安置的 `suc` 移位靠计算互相抵消，于是约束子不需要自己的引理。两条有界子句照它们的构造子那样一分为二，词项在左，公式体在右。
<!--/-->

```agda
    ⊨-place : ∀ {n k} (φ : Formula K n) (θ : Fin (countFo φ) → Fin (n + k))
              (γ : S ^ n) (σ : S ^ k)
            → (∀ j → lookup (θ j) (γ ++ σ) ≡ ι (lookup j (constantsFo φ)))
            → (γ ⊨ φ) ≡ ((γ ++ σ) ⊨₀ placeFo φ θ)
    ⊨-place (t ∈̇ u) θ γ σ h = cong₂ _∈ˢ_
      (⟦⟧-place t (λ i → θ (padRight (countTm u) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsTm u) h))
      (⟦⟧-place u (λ j → θ (padLeft (countTm t) j)) γ σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsTm u) h))
    ⊨-place (t ≐ u) θ γ σ h = cong₂ _≈ˢ_
      (⟦⟧-place t (λ i → θ (padRight (countTm u) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsTm u) h))
      (⟦⟧-place u (λ j → θ (padLeft (countTm t) j)) γ σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsTm u) h))
    ⊨-place (φ ∧̇ ψ) θ γ σ h = cong₂ _⊓_
      (⊨-place φ (λ i → θ (padRight (countFo ψ) i)) γ σ
        (leftHalf θ γ σ (constantsFo φ) (constantsFo ψ) h))
      (⊨-place ψ (λ j → θ (padLeft (countFo φ) j)) γ σ
        (rightHalf (countFo φ) θ γ σ (constantsFo φ) (constantsFo ψ) h))
    ⊨-place (φ ∨̇ ψ) θ γ σ h = cong₂ _⊔_
      (⊨-place φ (λ i → θ (padRight (countFo ψ) i)) γ σ
        (leftHalf θ γ σ (constantsFo φ) (constantsFo ψ) h))
      (⊨-place ψ (λ j → θ (padLeft (countFo φ) j)) γ σ
        (rightHalf (countFo φ) θ γ σ (constantsFo φ) (constantsFo ψ) h))
    ⊨-place (φ ⇒̇ ψ) θ γ σ h = cong₂ _⇒_
      (⊨-place φ (λ i → θ (padRight (countFo ψ) i)) γ σ
        (leftHalf θ γ σ (constantsFo φ) (constantsFo ψ) h))
      (⊨-place ψ (λ j → θ (padLeft (countFo φ) j)) γ σ
        (rightHalf (countFo φ) θ γ σ (constantsFo φ) (constantsFo ψ) h))
    ⊨-place ⊥̇       θ γ σ h = refl
    ⊨-place (∃̇ φ)   θ γ σ h = cong (⋁ S) (funExt (λ x →
      ⊨-place φ (λ j → suc (θ j)) (x ∷ γ) σ h))
    ⊨-place (∀̇ φ)   θ γ σ h = cong (⋀ S) (funExt (λ x →
      ⊨-place φ (λ j → suc (θ j)) (x ∷ γ) σ h))
    ⊨-place (∀̇∈ t φ) θ γ σ h = cong (⋀ S) (funExt (λ x → cong₂ _⇒_
      (cong (x ∈ˢ_) (⟦⟧-place t (λ i → θ (padRight (countFo φ) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsFo φ) h)))
      (⊨-place φ (λ j → suc (θ (padLeft (countTm t) j))) (x ∷ γ) σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsFo φ) h))))
    ⊨-place (∃̇∈ t φ) θ γ σ h = cong (⋁ S) (funExt (λ x → cong₂ _⊓_
      (cong (x ∈ˢ_) (⟦⟧-place t (λ i → θ (padRight (countFo φ) i)) γ σ
        (leftHalf θ γ σ (constantsTm t) (constantsFo φ) h)))
      (⊨-place φ (λ j → suc (θ (padLeft (countTm t) j))) (x ∷ γ) σ
        (rightHalf (countTm t) θ γ σ (constantsTm t) (constantsFo φ) h))))
```

<!--en-->
The adequacy proper follows by choosing the placement the abstraction chose and
the parameter environment the collection prescribes: the constants themselves,
interpreted. Its hypothesis is then the two pad laws in sequence, and the theorem
reads exactly as promised. Satisfaction of the original at `γ` is satisfaction of
the abstraction at `γ` extended by the collected constants.
<!--zh-->
名副其实的充分性随之而来：安置取抽象所取的那一件，参数环境取收集所规定的那一个，即诸常量自身经解释之后的样子。它的假设便是两条补位定律的接续，而定理读起来一如所许：原公式在 `γ` 处的满足，就是抽象在「`γ` 被收集来的诸常量扩张之后」的满足。
<!--/-->

```agda
    ⊨-abs : ∀ {n} (φ : Formula K n) (γ : S ^ n)
          → (γ ⊨ φ) ≡ ((γ ++ map ι (constantsFo φ)) ⊨₀ absFo φ)
    ⊨-abs {n} φ γ = ⊨-place φ (padLeft n) γ (map ι (constantsFo φ)) hyp
      where
      hyp : ∀ j → lookup (padLeft n j) (γ ++ map ι (constantsFo φ))
                ≡ ι (lookup j (constantsFo φ))
      hyp j = lookup-padLeft n γ (map ι (constantsFo φ)) j
            ∙ lookup-map ι (constantsFo φ) j
```

<!--en-->
## What a definable subset is
<!--zh-->
## 可定义子集究竟是什么
<!--/-->

<!--en-->
The corollary the next chapter consumes lives at arity one, because that is the
arity a subset is carved by. A definable subset of a set `A` is carved by a
formula of one free variable with constants from `A`, and membership in it is
satisfaction of that formula in the world `(A, ∈)`. That world is a structure like
any other, and the development above was stated at an arbitrary one, so instantiating
it there is the entire argument: at the restricted structure and the definable
powerset's own constant interpretation, `⊨-abs₁` says the subset carved by `φ` is
the subset carved by the parameter-free `absFo φ` at the parameters `constantsFo φ`
supplied in the environment. The satisfaction on both sides is the **inner** one,
the notion the definable powerset is defined by, and not the ambient reading of a
relativized formula; the two differ, and it is the inner one that is owed.

One point of shape, and the reason the arity-one case is worth writing down: at
arity one the extended environment is `x ∷ map ι p`, a single member followed by
the parameters, which is the very shape a one-entry environment has everywhere
else in the book.
<!--zh-->
下一章要消费的推论住在元数一处，因为那正是子集被刻出时所用的元数。集合 `A` 的可定义子集由带 `A` 中常量的单变量公式刻出，而属于它就是该公式在世界 `(A, ∈)` 中被满足。那个世界与任何别的结构无异，而上文的开发陈述在任意结构处，故在那里实例化就是全部论证：在限制结构与可定义幂集自家的常量解释处，`⊨-abs₁` 说，由 `φ` 刻出的子集就是由无参的 `absFo φ` 在环境供给的参数 `constantsFo φ` 处刻出的子集。两侧的满足都是**内层**那一个，即可定义幂集据以定义的那个概念，而非相对化公式在环境层的读法；两者不同，而欠着的正是内层那一个。

还有一处形状，也是元数一的情形值得单写的理由：在元数一处，扩张后的环境是 `x ∷ map ι p`，一个成员后接诸参数，而那正是本书别处每一个单条目环境的形状。
<!--/-->

```agda
    ⊨-abs₁ : (φ : Formula K 1) (x : S)
           → ((x ∷ []) ⊨ φ) ≡ ((x ∷ map ι (constantsFo φ)) ⊨₀ absFo φ)
    ⊨-abs₁ φ x = ⊨-abs φ (x ∷ [])
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Constants counted by occurrence (`countFo`{.Agda}) and collected in that order
(`constantsFo`{.Agda}); one generic traversal `placeFo`{.Agda} that puts each
occurrence wherever a placement says, instantiated as the abstraction
`absFo`{.Agda}, which raises the arity by the occurrence count and returns a
parameter-free formula; and `⊨-abs`{.Agda}, which certifies that the trade costs
no meaning, with `⊨-abs₁`{.Agda} spending it at the arity a
subset is carved by. Parameters can now leave the syntax and live in the
environment, which is the one thing standing between a definable subset and a
formula that can be counted.
<!--zh-->
常量逐次出现地计数 (`countFo`{.Agda})、并按同一次序收集 (`constantsFo`{.Agda})；一趟泛型遍历 `placeFo`{.Agda} 把每次出现放到安置所指之处，实例化为抽象 `absFo`{.Agda}，它按出现次数抬高元数，交出一条无参公式；而 `⊨-abs`{.Agda} 认证这笔交易不花含义，`⊨-abs₁`{.Agda} 则在「子集被刻出时所用的元数」处把它花掉。参数从此可以离开语法、住进环境，而这正是横在可定义子集与「数得清的公式」之间的唯一一件事。
<!--/-->
