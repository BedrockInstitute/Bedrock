<!--en-->
# Parameter abstraction

A formula with constants can be converted into a parameter-free formula by replacing each constant occurrence with a fresh variable and recording the constants in a vector. Supplying that vector through the environment preserves satisfaction, which makes formulas with parameters available to later coding arguments.
<!--zh-->
# 参数抽象

带常元的公式可通过将每次常元出现替换为新变量，并把这些常元记录在向量中，转成无参公式。通过环境供给该向量会保持满足关系，从而使带参数公式可用于后续符号化论证。
<!--ja-->
# パラメータ抽象

定数を含む論理式は、定数の各出現を新しい変数で置き換え、その定数をベクトルに記録することで、パラメータを持たない論理式へ変換できます。そのベクトルを環境から与えても充足関係は保存されるため、パラメータ付き論理式を後の符号化に利用できます。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module FOL.Manipulation.ParameterAbstraction where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import FOL.Manipulation.ConstantOccurrences using
  ( countTm; countFo; constantsTm; constantsFo; padRight; padLeft
  ; lookup-padRight; lookup-padLeft; lookup-map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _++_; map )
import Cubical.Data.Empty as Empty
```

<!--en-->
## The abstraction

A placement assigns each constant occurrence a variable in a larger context. `placeFo`{.Agda} performs this replacement structurally, and `absFo`{.Agda} chooses the consecutive block after the original free variables, whose length is the occurrence count.
<!--zh-->
## 抽象

安置为每次常元出现指派较大语境中的一个变量。`placeFo`{.Agda} 按结构执行替换，而 `absFo`{.Agda} 选择原自由变量之后的连续区块，其长度正是出现次数。
<!--ja-->
## 抽象化

配置は定数の各出現に、より大きな文脈の変数を割り当てます。`placeFo`{.Agda} はこの置換を構造的に行い、`absFo`{.Agda} は元の自由変数の直後にある、出現回数と同じ長さの連続した領域を選びます。
<!--/-->

<!--en-->
Genericity here is not decoration; it is what keeps the two-part constructors from
needing a second pass. A conjunction's occurrences are its left operand's followed
by its right operand's, so the two operands are abstracted under the placements
`θ ∘ padRight` and `θ ∘ padLeft`, **composed before the traversal** rather than
recovered afterwards by renaming the two halves into the joined context. One pass
over the formula, no weakening lemma, and each of the ten clauses has the shape
of the corresponding clause of every other structural recursion in this part.
Under a binder the placement gains one `suc`, because the parameter block's
indices all shift up by one, and nothing else changes.
<!--zh-->
此处的泛型并非装饰，而是让两部分的构造子免于第二次遍历的关键。合取的诸次出现，是左合取项的诸次出现后接右合取项的诸次出现；于是两个合取项分别在安置 `θ ∘ padRight` 与 `θ ∘ padLeft` 之下被抽象，而这两个安置是在**遍历之前复合**的，不是事后把两半重标到合并语境中再调整回来。对公式只需遍历一次，不需要弱化引理；十条子句各自的形状，就是本部其他每次结构递归中对应子句的形状。在约束子之下，安置多出一个 `suc`，这正是参数块的序号整体加一，除此之外没有任何变化。
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
The instance is the one the rest of the book will use: take the budget to be
exactly the occurrence count and the placement to be the block that follows the
variables. This is the required abstraction, and its type states the chapter's main result:
a formula over `K` with `n` free variables becomes a parameter-free formula with
`n + countFo φ` of them.
<!--zh-->
本书余下部分使用的实例取如下参数：参数位的数目恰好等于出现次数，安置则取紧随原变量之后的那一段。这就是所需的抽象，其类型可以概括为：`K` 上带 `n` 个自由变量的公式，变为带 `n + countFo φ` 个自由变量的无参公式。
<!--/-->

```agda
absFo : ∀ {ℓz ℓc} {K : Type ℓc} {n} (φ : Formula K n) → Formula (⊥* {ℓz}) (n + countFo φ)
absFo {n = n} φ = placeFo φ (padLeft n)
```

<!--en-->
## Adequacy

Adequacy compares the original formula under a constant interpretation with its abstraction under an extended variable environment. When each placed variable contains the interpretation of its recorded constant, term denotation and formula satisfaction agree by structural induction.
<!--zh-->
## 充分性

充分性比较常元解释下的原公式与扩展变量环境下的抽象公式。只要安置后的每个变量都带有其所记录常元的解释，词项释义与公式满足关系便依结构归纳相符。
<!--ja-->
## 妥当性

妥当性は、定数解釈の下にある元の論理式と、拡張した変数環境の下にある抽象化後の論理式を比較します。配置された各変数が記録済みの定数の解釈を持つなら、項の表示と論理式の充足関係は構造帰納法で一致します。
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
这一陈述对安置是泛型的，也必须如此，因为递归中的诸安置是在递归调用处产生的。它陈述在**变元**环境 `γ` 与**变元**参数环境 `σ` 处，受一条假设约束：在每次出现处，安置所指名的那个位置存放着在该处记录的诸常元的解释。这条假设就是「常元由环境供给」的全部内容；把它取作假设、而不是代入一个具体环境，正是让每条子句都不必归一化一个向量的原因。

对由两部分构成的构造子，唯一要做的处理就是拆分这条假设，拆出的每一半各与补位定律复合一次。
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
先看词项，两个情形都立即成立。常元的取值正是假设所述那个位置上的解释；变量的取值不变，补位定律保证它在扩张后的环境中仍取原值。
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
然后是归纳的十二个情形：十个公式情形在此处理，两个词项情形刚刚证毕。命题的每条原语子句都是同余，因为语义为每个构造子指派的恰是真值代数的对应运算，中间无须任何转换。四条约束子句向环境添加一个取值，并在扩张后的环境处援引归纳假设，而关于诸参数位的那条假设**原样**适用：左侧的前置与安置的 `suc` 移位由计算相互抵消，于是约束子不需要自己的引理。两条有界子句照它们的构造子那样一分为二，词项在左，公式体在右。
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
states exactly this. Satisfaction of the original at `γ` is satisfaction of
the abstraction at `γ` extended by the collected constants.
<!--zh-->
名副其实的充分性随之而来：安置取抽象所取的那一个，参数环境取收集所规定的那一个，即诸常元自身经解释之后的样子。它的假设正是两条补位定律的延续，而定理的内容也一如所述：原公式在 `γ` 处的满足，就是抽象在「`γ` 被收集来的诸常元扩张之后」的满足。
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

Parameter abstraction isolates the data behind a definable subset: a parameter-free formula, its finite vector of parameters, and the variable at which membership is tested. Adequacy shows that this presentation has exactly the same extension as the original formula with constants.
<!--zh-->
## 何谓可定义子集

参数抽象把可定义子集背后的数据拆开列出：一条无参公式、一个有限参数向量，以及用于检验成员关系的变量。充分性表明，这种呈现与原带常元公式具有完全相同的外延。
<!--ja-->
## 定義可能な部分集合とは何か

パラメータ抽象は、定義可能な部分集合を与えるデータを分離します。すなわち、パラメータを持たない論理式、有限なパラメータベクトル、そして所属を判定する変数です。妥当性により、この提示は元の定数付き論理式とまったく同じ外延を持ちます。
<!--/-->

<!--en-->
One point of shape, and the reason the arity-one case is worth writing down: at
arity one the extended environment is `x ∷ map ι p`, a single member followed by
the parameters, which is the very shape a one-entry environment has everywhere
else in the book.
<!--zh-->
还有一处形状，也是元数一的情形值得单写的理由：在元数一处，扩张后的环境是 `x ∷ map ι p`，一个成员后接诸参数，而那正是本书别处每一个单条目环境的形状。
<!--/-->

```agda
    ⊨-abs₁ : (φ : Formula K 1) (x : S)
           → ((x ∷ []) ⊨ φ) ≡ ((x ∷ map ι (constantsFo φ)) ⊨₀ absFo φ)
    ⊨-abs₁ φ x = ⊨-abs φ (x ∷ [])
```

<!--en-->
## Recap

`absFo`{.Agda} removes constants by adding one variable per occurrence, and `absFo-adequate`{.Agda} identifies satisfaction after the recorded constants are appended to the environment. This is the finite parameter presentation used when formulas themselves must be coded.
<!--zh-->
## 小结

`absFo`{.Agda} 为每次常元出现增加一个变量以消去常元，`absFo-adequate`{.Agda} 则在把记录的常元附加到环境后识别满足关系。这就是公式本身需要符号化时所用的有限参数呈现。
<!--ja-->
## まとめ

`absFo`{.Agda} は定数の出現ごとに変数を一つ加えて定数を除き、`absFo-adequate`{.Agda} は記録した定数を環境へ付け加えた後の充足関係を同定します。これは論理式そのものを符号化するときに使う有限パラメータの提示です。
<!--/-->
