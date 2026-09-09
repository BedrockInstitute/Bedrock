<!--en-->
# The set of all formula codes

Using the closed code domain, this chapter separates one constructible set containing exactly the formula codes, across all arities, that carry the required shape and closure witnesses. Its membership theorems move between a code, its arity numeral, and the decoded formula.
<!--zh-->
# 全体公式码之集

本章利用封闭码定义域分离出一个可构造集合，其中恰好包含所有元数上携带所需形状与封闭见证的公式码。其隶属定理给出码、元数数码与解码公式三者之间的相互转换。
<!--ja-->
# すべての論理式の符号からなる集合

閉じた符号の定義域を用いて、必要な形と閉性の証人を持つすべてのアリティの論理式の符号をちょうど含む、一つの構成可能集合を分出します。所属定理は、符号、アリティの数項、復号された論理式を相互に結びます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.CodeSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate )
open import L.Coding.Expressions {ℓ} using ( tagAtL; tagAtL-adequate )
open import L.Coding.Closure {ℓ} using ( closedAt )
open import L.Coding.CodeConstructibility {ℓ} using ( key; keyL; codeL; key∈closure )
open import L.Coding.SubformulaClosure {ℓ} using ( clo; closureClosed )
open import L.Coding.CodeShape {ℓ} using ( shapedAt; closureShaped )
open import L.Coding.FormulaRecovery {ℓ} using ( keyOf-fst; module Decode )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Is a key at a stated arity

One reader, and it is the only new piece of object language the chapter needs. A
key at arity `k` is a pair whose first component is the numeral `k`, and the tag
reader already says exactly that of a *named* second component. What is wanted
here is the second component left unnamed, so the reader is the tag reader under
one existential, and its two directions are the existential's two directions with
the tag reader's adequacy equation discharged inside.
<!--zh-->
## 是某个已言明元数处的键

本节给出一条读式，也是本章唯一新增的对象语言陈述。元数 `k` 处的键是第一分量为数码 `k` 的对；已有的标签读式描述第二分量已被**点名**的情形。这里不指定第二分量，因此把标签读式置于一个存在量词之下。两个方向分别来自该存在量词的引入与消去，并在内部使用标签读式的充分性等式。
<!--ja-->
## 指定したアリティのキー

`keyArityAtL`{.Agda} は、与えられた集合が指定したアリティの論理式の構成子キーであることを表します。タグ読取式の妥当性を存在量化子の内側で使うことで、導入則と除去則が対象言語の充足関係と外部のキー証人を正確に対応させます。
<!--/-->

<!--en-->
The equation is discharged with the index, the numeral and the environment all
still variables; keeping them as variables is what avoids the extra
conversion-checking overhead that later instantiation would otherwise incur.
<!--zh-->
该等式在索引、数码与环境仍为变元时证明；保持这些参数为变元，才能避免后续实例化产生额外的转换检查开销。
<!--/-->

```agda
keyArityAtL : ∀ {n} → Fin n → ℕ → Formula S n
keyArityAtL c k = ∃̇ (tagAtL (suc c) k zero)

keyArityAtL-out : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n)
                → ⟨ γ ⊨ keyArityAtL c k ⟩
                → ∥ (Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# k) (fst z))) ∥₁
keyArityAtL-out c k γ = PT.map
  (λ { (z , hz) →
    z , subst ⟨_⟩ (tagAtL-adequate (suc c) k zero (z ∷ γ)) hz })

keyArityAtL-in : ∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n) (z : S)
               → fst (lookup c γ) ≡ pr (# k) (fst z)
               → ⟨ γ ⊨ keyArityAtL c k ⟩
keyArityAtL-in c k γ z e =
  ∣ z , subst ⟨_⟩ (sym (tagAtL-adequate (suc c) k zero (z ∷ γ))) e ∣₁
```

<!--en-->
## Is a key at some arity

The reader above names its arity as a metalevel numeral, which is what pins the
arity to one; a set that has to hold subcodes cannot do that, because a
quantifier's subformula lives one arity up. So the arity has to become a bound
set, and something has to say of that set what `# k`{.Agda} gives directly: that
it is a numeral.
<!--zh-->
## 是某个元数处的键

上一条读式把元数指定为一个元语言的数码，而正是这一点把元数固定为一；一个必须容纳诸子码的集合无法做到这一点，因为量词的子公式位于高一级的元数上。因此元数必须变成一个被绑定的集合，而还须有某个东西向那个集合说明 `# k`{.Agda} 直接给出的事实：它是一个数码。
<!--ja-->
## あるアリティのキー

アリティを指定せずに、ある自然数のアリティでキーとなることを存在量化します。`arityNumAtL`{.Agda} はそのアリティを有限数項として読み書きします。
<!--/-->

<!--en-->
Stating it takes one constant. `ωʟ`{.Agda} is an element of `L` whose members are
exactly the numerals, so "the arity component lies in `ωʟ`{.Agda}" *is* the
condition, written with the same unbounded membership the second conjunct already
uses. The whole formula has two existentials, one for the arity and one for the
payload, the pair reader between them, and the membership on the arity.

Reading it in the other direction is where the choice takes effect.
`ω-specL`{.Agda} is an equation between propositions, not an implication, so a
member of `ωʟ`{.Agda} *is* a truncated natural number, and one composition with the
chain's projection equation turns it into the metalevel `# m`{.Agda} that
`recover`{.Agda} takes as its arity argument. Neither direction needs induction;
the numeral chapter already did that work.
<!--zh-->
表达它只需一个常元。`ωʟ`{.Agda} 是 `L` 的元素，其成员恰是诸数码，故「元数分量属于 `ωʟ`{.Agda}」**就是**那个条件，而且写法与第二个合取项已经在用的那种无界隶属相同。全式共有两个存在量词，分别约束元数与载荷，中间是对读式，再加上落在元数上的那条隶属。

从反方向读时，这一选择的作用才显现出来。`ω-specL`{.Agda} 是命题之间的等式而非蕴含，故 `ωʟ`{.Agda} 的成员**就是**一个被截断的自然数；与链的投影等式复合一次，就把它变成 `recover`{.Agda} 作为元数实参所接受的那个 `# m`{.Agda}。两个方向都不需要归纳；数码那一章已经完成了。
<!--/-->

```agda
arityNumAtL : ∀ {n} → Fin n → Formula S n
arityNumAtL c = ∃̇ (∃̇ (prAtL (suc (suc c)) (suc zero) zero
                     ∧̇ (var (suc zero) ∈̇ con ωʟ)))

arityNumAtL-out : ∀ {n} (c : Fin n) (γ : S ^ n)
                → ⟨ γ ⊨ arityNumAtL c ⟩
                → ∥ (Σ[ m ∈ ℕ ] Σ[ z ∈ S ]
                      (fst (lookup c γ) ≡ pr (# m) (fst z))) ∥₁
arityNumAtL-out c γ = PT.rec squash₁ (λ { (ar , h) →
  PT.rec squash₁ (λ { (z , (hp , hω)) → PT.map
    (λ { (m , qm) → lower m , z
       , ( subst ⟨_⟩
             (prAtL-adequate (suc (suc c)) (suc zero) zero (z ∷ ar ∷ γ)) hp
         ∙ cong (λ w → pr w (fst z)) (qm ∙ numeralL-fst (lower m)) ) })
    (subst ⟨_⟩ (ω-specL ar) hω) }) h })

arityNumAtL-in : ∀ {n} (c : Fin n) (γ : S ^ n) (m : ℕ) (z : S)
               → fst (lookup c γ) ≡ pr (# m) (fst z)
               → ⟨ γ ⊨ arityNumAtL c ⟩
arityNumAtL-in c γ m z e = ∣ numeralL m , ∣ z
  , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc c)) (suc zero) zero
        (z ∷ numeralL m ∷ γ)))
        (e ∙ cong (λ w → pr w (fst z)) (sym (numeralL-fst m)))
    , subst ⟨_⟩ (sym (ω-specL (numeralL m))) ∣ lift m , refl ∣₁ ) ∣₁ ∣₁
```

<!--en-->
## The predicate

Two conjuncts, at one free variable. The first pins the arity from outside, which
is the conjunct the previous chapter asked for by name. The second is a witness
for the decode's two hypotheses: a set holding the argument, closed and shaped.
<!--zh-->
## 谓词

两个合取项都落在同一个自由变元上。第一项从外部固定元数，而这正是上一章明确要求的那一项。第二项是解码那两条假设的见证：一个装着实参、既封闭又成形的集合。
<!--ja-->
## 符号を選ぶ述語

全体の符号集合を定める述語は、候補があるアリティのキーであり、閉じた符号領域に対応する形と復号証人を持つことを要求します。これにより異なるアリティの符号を一つの式で扱えます。
<!--/-->

<!--en-->
Nothing in the second conjunct is bounded, and nothing has to be. The witness is
produced from a formula's own subformula closure in the introduction, and
consumed as a set of `L` in the elimination, and the class model is where both
readings happen.

The second conjunct is written twice: once at two slots, the carrier and the
argument, and once with the carrier pinned to a constant. The general one is a
single existential, for the set; the pinned one wraps it in the binder that names
`A`, and that binder is the entire difference between them.
<!--zh-->
第二项里没有任何东西是有界的，也不需要有。引入一方由一条公式自己的子公式闭包给出该见证，消去一方则把它作为 `L` 的一个集合来使用，两种读法都发生在类模型处。

第二个合取项有两种写法：一般形式使用载体与实参两个槽位；常元形式则把载体固定为常元。一般形式只用一个存在量词绑定相应集合；常元形式在外层再加入一个以 `A` 命名的绑定。这个额外绑定是两种写法的全部差别。
<!--/-->

```agda
hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n
hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero)
                      ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A)))

hasWitness : S → Formula S 1
hasWitness A = ∃̇ ((var zero ≐ con A) ∧̇ hasWitnessAt zero (suc zero))

isCodeAny : S → Formula S 1
isCodeAny A = arityNumAtL zero ∧̇ hasWitness A
```

<!--en-->
## The superset, and the set

The carrier is fixed, and the consumer will fix it at a stage. Its members are
the alphabet, exactly as the coding chapters' two parameters expect: the
embedding into the hierarchy, and the certificate that what it lands on is
constructible. The second is transitivity of `L` applied once, and the membership
it is applied to is named separately, because the shape predicate now asks for it
in its own right.
<!--zh-->
## 超集与集合

载体固定后，使用方会把它取为某个阶段。载体的成员构成字母表，正好提供编码章要求的两项参数：到层级的嵌入，以及该嵌入每个取值可构造的证明。后一项由 `L` 的传递性得到。相应的隶属关系单独命名，因为形状谓词直接以该关系为参数。
<!--ja-->
## 上位集合と分出された集合

まずすべての候補と証人を含む構成可能な上位集合を作り、その中で符号述語による分出を行います。結果として、すべてのアリティの論理式符号を含む一つの集合が得られます。
<!--/-->

<!--en-->
Then the superset. `smallDom`{.Agda} asks for a small family of elements of `L`
and returns a stage containing all of it; the family is indexed by the pairs of
an arity and a formula at it. The type is of the right size because syntax is an
inductive type at the alphabet's own level, and the arity is a natural number,
which costs no level at all. What comes back contains every key and much else,
and separation removes the else.

The set is sealed where it is built. Unsealed, every later type mentioning it
would carry the separation instrument's unfolding into conversion, and the facts
exported here are all any consumer needs. Only the ones that read a separation
are inside a seal; the directions back and the equations they compose into are
outside, since none of them needs to know what the set was cut out of.
<!--zh-->
接着构造所需超集。`smallDom`{.Agda} 接收 `L` 元素的小族，并返回包含该族所有元素的阶段。这里的小族以「一个元数及该元数处的一条公式」组成的对为索引。其尺寸满足要求，因为语法是字母表所在层级上的归纳类型，而自然数索引不会提高该尺寸。所得阶段含有每个键，也含有其他元素；最后用分离去除这些额外元素。

这个集合在构造处被封印。若不封印，此后每个提到它的类型都会把分离定义的展开带入转换检查，而这里导出的事实已经足够所有使用方使用。封印内部只保留读取分离结果所需的引理；由这些方向复合得到的等式放在封印外部，因为它们不依赖该集合从哪个超集中分离出来。
<!--/-->

```agda
module _ (A : S) where
  private
    ι : ⟪ fst A ⟫ → V ℓ
    ι = ⟪ fst A ⟫↪

    ι∈ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ fst A ⟩
    ι∈ m = ∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

    ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
    ιL m = isL-trans {x = fst A} {y = ι m} (ι∈ m) (A .snd)

  codeS : ∀ {n} → Formula ⟪ fst A ⟫ n → S
  codeS φ = VCode.⌜ mapFo ι φ ⌝ , codeL ι ιL φ

  keyS : ∀ {n} → Formula ⟪ fst A ⟫ n → S
  keyS φ = key ι ιL φ , keyL ι ιL φ

  private
    smallAny : Σ[ d ∈ S ] ((p : Σ[ n ∈ ℕ ] Formula ⟪ fst A ⟫ n)
                          → ⟨ keyS (snd p) ∈ˢ d ⟩)
    smallAny = smallDom (Σ[ n ∈ ℕ ] Formula ⟪ fst A ⟫ n) (λ p → keyS (snd p))

    sepAny : isContr
      (SetOf (λ x → (x ∈ˢ smallAny .fst) ⊓ ((x ∷ []) ⊨ isCodeAny A)))
    sepAny = hasSeparationL (smallAny .fst) (isCodeAny A)
```

<!--en-->
## The witness, in and out

Both halves of the second conjunct are proved here, once, at a variable arity, a
variable carrier slot and a variable environment, and everything below applies
them. The arity may be variable because the conjunct never mentions it: the
introduction produces a closed, shaped set for a formula of any arity, and the
elimination consumes one and calls the decode, which took the arity as an
argument from the start. The carrier and the environment may be variable because
every lemma the two halves are built from already takes them so.
<!--zh-->
## 见证的引入与消去

第二个合取项的两半都在此处证明，且是在变元元数、变元载体位与变元环境上一次证成，下面的一切只是把它们再应用一遍。元数可以是变元，因为那个合取项根本不提及它：引入为任意元数的一条公式产出一个既封闭又成形的集合，消去则接受这样的集合并调用解码，而解码从一开始就把元数作为实参。载体与环境可以是变元，则是因为两半所依赖的每条引理本来就是这样陈述的。
<!--ja-->
## 証人の導入と除去

符号集合への所属から、アリティ、論理式、形、閉性の証人を取り出せます。逆にこれらのデータから所属を構成できるため、内部集合は外部の符号概念を正確に表します。
<!--/-->

<!--en-->
Introduction is the half that adds nothing beyond what is given. The witness is the subformula
closure, whose three obligations are `key∈closure`{.Agda}, `closureClosed`{.Agda}
and `closureShaped`{.Agda}, one chapter each and all already discharged. The last
of them asks for one thing more, that every constant is a member of the carrier,
and at this alphabet that is the fact the alphabet was defined by, carried across
the slot's equation.

Elimination is the other half, and it starts from the member already in key form
at a stated arity, which is what `recover`{.Agda} demands and what nothing in the
second conjunct would supply. The carrier slot's equation turns a membership in
whatever that slot holds into a membership in `A`, which is what makes the
decode's hypothesis dischargeable: `A`'s members are exactly the image of
`⟪ A ⟫`, by the presentation of a set by its own members. Read the existential
and a closed, shaped set arrives with it. Then the decode runs, and its answer is
a formula over the carrier, at the arity it was handed.

The pinned pair is these two at the environment the naming binder makes, and
that is the whole of what pinning costs: introduction supplies `A` for the binder
and `refl`{.Agda} for its equation, elimination reads the binder off and hands
what it holds to the general form. **Reading it off is where the payload has to
be named.** Left to inference, the truncation's payload at a pinned carrier is a
metavariable standing for the satisfaction of a formula the elaborator has not
committed to, and the same two lines that check in two seconds with the type
written out ran past 140 seconds without it and were killed there. This is the
law the recursion's totality hypothesis recorded, met again in a different place:
it is not about the graph, it is about `PT.rec`{.Agda} at a concrete environment.
<!--zh-->
引入是其中不涉及额外内容的那一半。那个见证是子公式闭包，它的三个组成部分 `key∈closure`{.Agda}、`closureClosed`{.Agda} 与 `closureShaped`{.Agda} 各有一章专门处理，且都已完成。其中最后一条还多需要一件东西，即每个常元都是载体的成员；在这个字母表上，这正是当初据以定义字母表的那件事，沿那一位的等式搬过去即可。

消去是另一半。它从一个成员出发，这个成员以某个已言明元数处的键的形式给出，这正是 `recover`{.Agda} 所要求的，也是第二个合取项无法直接提供的。载体那一位的等式把「属于那一位所持有的东西」变成「属于 `A`」，解码那条假设因此得以应用：`A` 的诸成员恰是 `⟪ A ⟫` 的像，依据是「一个集合由其自身诸成员所呈现」。读出那个存在量词，就得到一个既封闭又成形的集合。随后运行解码，其答案是载体之上、落在所给定的那个元数处的一条公式。

这两个方向都应用于由外层具名绑定构造的环境，其中载体由等式固定。引入方向为该绑定提供 `A`，并用 `refl`{.Agda} 证明等式；消去方向读出该绑定，再把其中的数据传给一般形式。**读取绑定之处必须显式写出载荷类型。** 若让类型检查器推断，载体处的截断载荷会成为一个元变元，表示尚未确定公式的满足关系。同样两行代码，显式写出类型时两秒完成，不写时超过 140 秒后终止。该现象来自具体环境处的 `PT.rec`{.Agda}，与图本身无关。
<!--/-->

```agda
  witnessAt-in : ∀ {n k} (b c : Fin n) (γ : S ^ n) (φ : Formula ⟪ fst A ⟫ k)
               → fst (lookup b γ) ≡ fst A
               → fst (lookup c γ) ≡ fst (keyS φ)
               → ⟨ γ ⊨ hasWitnessAt b c ⟩
  witnessAt-in b c γ φ qb qc = ∣ clo ι ιL φ
    , ( subst (λ w → ⟨ w ∈ fst (clo ι ιL φ) ⟩) (sym qc) (key∈closure ι ιL φ)
      , ( closureClosed ι ιL φ γ
        , closureShaped ι ιL φ b γ
            (λ m → subst (λ w → ⟨ ι m ∈ w ⟩) (sym qb) (ι∈ m)) ) ) ∣₁

  witnessAt-out : ∀ {n} (b c : Fin n) (γ : S ^ n)
                → fst (lookup b γ) ≡ fst A
                → ⟨ γ ⊨ hasWitnessAt b c ⟩
                → (k : ℕ) (z : S) → fst (lookup c γ) ≡ pr (# k) (fst z)
                → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ]
                      (fst (lookup c γ) ≡ fst (keyS ψ))) ∥₁
  witnessAt-out b c γ qb hw k z qz = PT.rec squash₁ viaSlot hw
    where
    Target : Type (ℓ-suc ℓ)
    Target = ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ]
                 (fst (lookup c γ) ≡ fst (keyS ψ))) ∥₁

    onto : (y : V ℓ) → ⟨ y ∈ fst (lookup b γ) ⟩
         → ∥ Σ[ m ∈ ⟪ fst A ⟫ ] (ι m ≡ y) ∥₁
    onto y y∈ = ∣ ∈-asFiber {a = y} {b = fst A}
      (subst (λ w → ⟨ y ∈ w ⟩) qb y∈) ∣₁

    viaSlot : Σ[ C ∈ S ] ⟨ (C ∷ γ) ⊨ ((var (suc c) ∈̇ var zero)
                ∧̇ (closedAt zero ∧̇ shapedAt zero (suc b))) ⟩
            → Target
    viaSlot (C , (x∈C , (hcl , hsh))) = PT.map
      (λ { (ψ , qψ) → ψ , (qz ∙ cong (pr (# k)) (sym qψ)) })
      (Decode.recover ι zero (suc b) (C ∷ γ) onto hcl hsh k z
        (subst (λ w → ⟨ w ∈ fst C ⟩) (qz ∙ sym (keyOf-fst k z)) x∈C))

  private
    witness-in : ∀ {n} (φ : Formula ⟪ fst A ⟫ n)
               → ⟨ (keyS φ ∷ []) ⊨ hasWitness A ⟩
    witness-in φ = ∣ A , ( refl
      , witnessAt-in zero (suc zero) (A ∷ keyS φ ∷ []) φ refl refl ) ∣₁

    witness-out : (x : S) → ⟨ (x ∷ []) ⊨ hasWitness A ⟩
                → (k : ℕ) (z : S) → fst x ≡ pr (# k) (fst z)
                → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ] (fst x ≡ fst (keyS ψ))) ∥₁
    witness-out x hw k z qz = PT.rec squash₁ viaCarrier hw
      where
      viaCarrier : Σ[ B ∈ S ] ⟨ (B ∷ x ∷ [])
                     ⊨ ((var zero ≐ con A) ∧̇ hasWitnessAt zero (suc zero)) ⟩
                 → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ] (fst x ≡ fst (keyS ψ))) ∥₁
      viaCarrier (B , (qB , hB)) =
        witnessAt-out zero (suc zero) (B ∷ x ∷ []) qB hB k z qz
```

<!--en-->
## The set at every arity

What comes out is the class of keys of formulas over the carrier **at any
arity**, which is the class a recursion over subcodes has to be indexed by,
because a quantifier's subformula lives one arity up and the arity-one class does
not contain it.
<!--zh-->
## 每个元数上的集合

得到的是载体之上诸公式**在任意元数处**的诸键之类，而「对诸子码作递归」必须以这一类为索引，因为量词的子公式位于高一级的元数上，一元那一类容纳不下它。
<!--ja-->
## 各アリティでの符号集合

アリティ `n` を固定すると、`n` 変数のすべての論理式の符号が全体の符号集合に属します。また所属する `n`-項のキーから対応する論理式を復号できます。
<!--/-->

```agda
  IsKeyOverAny : S → Ω
  IsKeyOverAny x =
    ∥ (Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst A ⟫ n ] (fst x ≡ fst (keyS ψ))) ∥₁
    , squash₁

  opaque
    AllCodes : S
    AllCodes = sepAny .fst .fst

    key∈AllCodes : ∀ {n} (φ : Formula ⟪ fst A ⟫ n) → ⟨ keyS φ ∈ˢ AllCodes ⟩
    key∈AllCodes {n} φ = subst ⟨_⟩ (sym (sepAny .fst .snd (keyS φ)))
      ( smallAny .snd (n , φ)
      , ( arityNumAtL-in zero (keyS φ ∷ []) n (codeS φ) refl
        , witness-in φ ) )

    AllCodes-out : (x : S) → ⟨ x ∈ˢ AllCodes ⟩ → ⟨ IsKeyOverAny x ⟩
    AllCodes-out x x∈ = PT.rec squash₁
      (λ { (k , z , qz) → PT.map (λ { (ψ , q) → k , ψ , q })
        (witness-out x (sat .snd) k z qz) })
      (arityNumAtL-out zero (x ∷ []) (sat .fst))
      where
      sat : ⟨ (x ∷ []) ⊨ isCodeAny A ⟩
      sat = subst ⟨_⟩ (sepAny .fst .snd x) x∈ .snd

  AllCodes-in : (x : S) → ⟨ IsKeyOverAny x ⟩ → ⟨ x ∈ˢ AllCodes ⟩
  AllCodes-in x = PT.rec (snd (x ∈ˢ AllCodes))
    (λ { (n , ψ , q) →
      subst (λ w → ⟨ w ∈ fst AllCodes ⟩) (sym q) (key∈AllCodes ψ) })
```

<!--en-->
## Recap

One set, one predicate. `AllCodes`{.Agda} is an element of `L` whose members are
exactly the keys of the formulas over the carrier, at every arity, by
`AllCodes-out`{.Agda} and `AllCodes-in`{.Agda}.
<!--zh-->
## 小结

一个集合，一条谓词。`AllCodes`{.Agda} 是 `L` 的元素，凭 `AllCodes-out`{.Agda} 与 `AllCodes-in`{.Agda}，它的诸成员恰是载体之上诸公式在**每个**元数处的诸键。
<!--ja-->
## まとめ

一つの構成可能集合が、すべてのアリティの整形式な論理式符号を集めます。所属の導入・除去定理により、符号、有限数項としてのアリティ、復号された論理式を相互に移せます。
<!--/-->

<!--en-->
The whole content is in two conjuncts, and both are of the same kind. Closedness
and shapedness together recognize the *shape* of a code and say nothing about the
arity a key carries or the alphabet its constants come from, so a decode written
against them has to be handed both, and a set built from them has to state both.
`smallDom`{.Agda} and general-formula separation do the rest, and neither needed
anything the earlier chapters had not already established.

The set exists for the *class* it characterizes, not for a theorem about it. A
recursion over codes has to answer at a code's subcodes, a quantifier's
subformula lives one arity up, and the arity-one class does not contain it, so
the domain has to be the keys at every arity.
<!--zh-->
全部内容都在两个合取项里，而两者同类。封闭性与成形性合起来刻画的是码的**形状**，对一个键所携带的元数以及它的诸常元出自哪个字母表则完全未提，故一条针对它们写下的解码必须被给予这两样，而一个由它们造出的集合必须说明这两样。`smallDom`{.Agda} 与任意公式的分离处理其余，而两者所依赖的都只是前几章已经建立的结果。

这个集合的存在，是为了它所刻画的那**一类**，而不是为了某条关于它的定理。对码的递归必须在一个码的诸子码处给出答案，而量词的子公式位于高一级的元数上，一元那一类容纳不下它，故定义域只能是每个元数处的诸键。
<!--/-->
