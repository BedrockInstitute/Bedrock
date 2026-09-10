<!--en-->
# Coding inside the cumulative hierarchy

The generic coding construction of FOL.Coding needs exactly two injective operations on some carrier: an injective pairing, and an injective map from natural numbers. To code syntax over the cumulative hierarchy, both must be found among sets, and the hierarchy supplies them. For the naturals, its own von Neumann numerals serve. A smaller numeral belongs to a larger one, since each numeral sits inside its successor, and no set belongs to itself; so distinct indices, compared by the trichotomy on natural numbers, give distinct sets. For pairing, the Kuratowski encoding serves: the pair of `a`{.Agda} and `b`{.Agda} is the set whose members are the singleton `⁅ a ⁆s`{.Agda} and the unordered pair `⁅ a , b ⁆`{.Agda}, so the first component is recoverable as the common element and the second as the one that may differ.

Both arguments face one constraint from the type theory. Small membership in a hierarchy set is propositionally truncated, so a case analysis on it may eliminate only into propositions. Equality in `V`{.Agda} is propositional because `V`{.Agda} is an h-set, and the path propositions built from such equalities are exactly the targets the reasoning below needs. Working at that level of discipline, every step stays proposition-valued and no witness is ever extracted from a truncation.
<!--zh-->
# 累积层级内的符号化

FOL.Coding 中的通用编码构造只需要载体上的两个单射操作：单射的配对，以及从自然数出发的单射映射。要为累积层级上的语法编码，二者都必须在集合中找到，而层级本身提供了它们。自然数方面，层级自身的 von Neumann 数码即可胜任。较小的数码属于较大的，因为每个数码都在自己的后继之内，而没有集合属于自身；于是经自然数三歧性比较的相异序号给出相异的集合。配对方面，Kuratowski 编码即可胜任：`a`{.Agda} 与 `b`{.Agda} 的对，是以单点集 `⁅ a ⁆s`{.Agda} 与无序对 `⁅ a , b ⁆`{.Agda} 为成员的那个集合。于是第一分量可作为公共元素还原，第二分量则作为另一个 (可能相等的) 元素还原。

两个论证都受类型论的一条约束。层级集合中的小隶属是命题截断的，所以对它的分情形只能消去到命题。由于 `V`{.Agda} 是 h-集，`V`{.Agda} 中的等式是命题性的，而由这些等式构成的路径命题恰好是下文推理所需的目标。在这一消去限制下，每一步都取值于命题，从不从截断中提取任何见证。
<!--ja-->
# 累積階層の内部での符号化

FOL.Coding の一般的な符号化構成が要求するのは、台の上の 2 つの単射操作、すなわち単射な対の操作と自然数からの単射写像だけです。累積階層の上の構文を符号化するには、この 2 つを集合のうちに見つけなければならず、階層自身がそれを供給します。自然数には von Neumann 数項がそのまま使えます。各数項は自分の後続の内にあるので、小さい数項は大きい数項に属し、どの集合も自分自身には属しません。したがって、自然数の三分律で比較した異なる添字は異なる集合に写ります。対には Kuratowski 符号化が使えます。`a`{.Agda} と `b`{.Agda} の対とは、一元集合 `⁅ a ⁆s`{.Agda} と非順序対 `⁅ a , b ⁆`{.Agda} を元として持つ集合であり、第 1 成分は共通の元として、第 2 成分は (一致しうる) もう一方の元として復元できます。

どちらの議論にも、型理論からの 1 つの制約が関わります。階層の集合における小さい所属は命題の切り詰めを持つので、それに関する場合分けは命題へしか消去できません。`V`{.Agda} は h-集合なので `V`{.Agda} の等式は命題的であり、その等式から作られるパス命題が、以下の推論がまさに必要とするターゲットです。この規律のもとでは、すべてのステップが命題に値を取り、切り詰めから証拠を取り出すことは一度もありません。
<!--/-->

<!--en-->
The chapter is stated at a fixed universe level `ℓ`{.Agda}: the hierarchy's own structure `𝒮ᵥ`{.Agda} is the carrier that the codes will live over, and its membership relation is the one being analyzed. The truth values for the eventual coding instance come from the hProp truth algebra at level `ℓ-suc ℓ`{.Agda}, one level up; that is where the instance at the end of the chapter will be taken.
<!--zh-->
本章在固定的宇宙层级 `ℓ`{.Agda} 上陈述：层级的结构 `𝒮ᵥ`{.Agda} 是码所寄居的载体，其隶属关系正是被分析的对象。编码实例最终所用真值取自高一层级 `ℓ-suc ℓ`{.Agda} 的 hProp 真值代数；章末的实例即取在这一层级上。
<!--ja-->
この章は固定された宇宙レベル `ℓ`{.Agda} で述べられます。階層の構造 `𝒮ᵥ`{.Agda} が符号の載る台であり、その所属関係こそ分析の対象です。最終的な符号化インスタンスの真理値は、1 つ上のレベル `ℓ-suc ℓ`{.Agda} の hProp 真理値代数から取られ、章末のインスタンスはそのレベルで取られます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Coding {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
The numeral argument rests on two membership facts about successors in the hierarchy: a set always belongs to its own successor, and a member of a set belongs to that set's successor. Applied to the numerals, the first says `# n ∈ # (suc n)`{.Agda}, and the second says a member of `# n`{.Agda} survives into `# (suc n)`{.Agda}. The order on natural numbers then decides which numeral is smaller, with the trichotomy `m ≟ n`{.Agda} supplying the three cases the injectivity proof will separate.
<!--zh-->
数码的论证依赖层级中关于后继的两条隶属事实：一个集合总属于它自己的后继，而一个集合的成员属于该集合的后继。施于数码，第一条说 `# n ∈ # (suc n)`{.Agda}，第二条说 `# n`{.Agda} 的成员在 `# (suc n)`{.Agda} 中得以保留。自然数上的序随之判定哪个数码更小，三歧比较 `m ≟ n`{.Agda} 给出单射性证明将要分离的三种情形。
<!--ja-->
数項の議論は、階層の後続に関する 2 つの所属事実に依存します。任意の集合は自分自身の後続に属し、集合の元はその後続にも属するというものです。数項に適用すると、第 1 の事実は `# n ∈ # (suc n)`{.Agda} を、第 2 の事実は `# n`{.Agda} の元が `# (suc n)`{.Agda} にも残ることを述べます。自然数の順序がどちらの数項が小さいかを決め、三分律の比較 `m ≟ n`{.Agda} が単射性証明が分ける 3 つの場合を与えます。
<!--/-->

```agda
import FOL.Coding
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl )

open import Cubical.Data.Nat.Order using ( _<_; <-split; ¬-<-zero; _≟_; lt; eq; gt )
import Cubical.Data.Empty as Empty
```

<!--en-->
Here is the elimination restriction in its precise form. The small membership statement `⟨ x ∈ₛ s ⟩`{.Agda} is a proposition by truncation, so when a hypothesis gives a truncated disjunction of memberships, the eliminator must target a proposition. Because `V`{.Agda} is an h-set, certified by `setIsSet`{.Agda}, the path type `x ≡ y`{.Agda} between hierarchy sets is propositional; every case split below may therefore eliminate into such an equality path.
<!--zh-->
这一消去限制的精确形式如下。小隶属陈述 `⟨ x ∈ₛ s ⟩`{.Agda} 经截断后是命题，因此当假设给出隶属的截断析取时，消去的目标必须是命题。由于 `V`{.Agda} 是 h-集 (`setIsSet`{.Agda} 所证)，层级集合之间的路径类型 `x ≡ y`{.Agda} 是命题性的，所以下文每个分情形都可以消去到这种等式路径。
<!--ja-->
この消去制限を正確に述べます。小さい所属の主張 `⟨ x ∈ₛ s ⟩`{.Agda} は切り詰めによって命題なので、仮定が所属の切り詰められた選言を与えるとき、消去の行き先は命題でなければなりません。`V`{.Agda} は h-集合であり (`setIsSet`{.Agda} が証明します)、階層の集合の間のパス型 `x ≡ y`{.Agda} は命題的です。したがって以下のすべての場合分けはそのような等式パスへ消去できます。
<!--/-->

```agda
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
```

<!--en-->
The two set constructions the Kuratowski code needs come with their membership classifications attached. For an unordered pair `⁅ a , b ⁆`{.Agda}, the classification `pairing-ax`{.Agda} says that `x`{.Agda} belongs to it merely when `x ≡ a`{.Agda} or `x ≡ b`{.Agda}, in the truncated sense. The singleton `⁅ a ⁆s`{.Agda} carries the analogous classification through the singleton package, and `SetPackage.classification`{.Agda} extracts these records. Every argument about the codes below is therefore stated as membership reasoning rather than as unfolding of nested braces.
<!--zh-->
Kuratowski 码所需的两个集合构造都自带隶属分类。对无序对 `⁅ a , b ⁆`{.Agda}，分类 `pairing-ax`{.Agda} 说：在截断的意义下，`x`{.Agda} 属于它仅仅当 `x ≡ a`{.Agda} 或 `x ≡ b`{.Agda}。单点集 `⁅ a ⁆s`{.Agda} 经单点集包带有类似的分类，`SetPackage.classification`{.Agda} 负责提取这些记录。于是下文关于码的每个论证都表述为成员关系推理，而非展开嵌套花括号。
<!--ja-->
Kuratowski 符号が必要とする 2 つの集合の構成には、所属の分類が付いています。非順序対 `⁅ a , b ⁆`{.Agda} については、分類 `pairing-ax`{.Agda} は、切り詰められた意味で `x ≡ a`{.Agda} または `x ≡ b`{.Agda} のときに限り `x`{.Agda} が属することを述べます。一元集合 `⁅ a ⁆s`{.Agda} は一元集合パッケージを通して同様の分類を持ち、`SetPackage.classification`{.Agda} がこれらのレコードを取り出します。したがって、以下の符号に関するすべての議論は、入れ子の中括弧を展開するのではなく、所属の推論として述べられます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s; SingletonPackage; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( SetPackage )  -- lint-agda: keep (used qualified: SetPackage.classification)
```

<!--en-->
The numeral `# n`{.Agda}, written using `#_`{.Agda}, is the von Neumann ordinal representing the natural number `n`{.Agda} inside the hierarchy. With the two alphabets in hand, the truth algebra at level `ℓ-suc ℓ`{.Agda} and the hProp structure `𝒮ᵥ`{.Agda} are what the coding instance at the end will interpret the encoded syntax in; the injectivity proofs of this chapter use only the successor facts and the classifications just described.
<!--zh-->
数码 `# n`{.Agda} 以 `#_`{.Agda} 记之，是在层级中表示自然数 `n`{.Agda} 的 von Neumann 序数。两个字母表在手之后，层级 `ℓ-suc ℓ`{.Agda} 的真值代数与 hProp 结构 `𝒮ᵥ`{.Agda} 就是章末编码实例解释被编码语法之处；本章的单射性证明只使用前述的后继事实与分类。
<!--ja-->
数項 `# n`{.Agda} は `#_`{.Agda} と書かれ、階層の中で自然数 `n`{.Agda} を表す von Neumann 順序数です。2 つの字母が揃えば、レベル `ℓ-suc ℓ`{.Agda} の真理値代数と hProp 構造 `𝒮ᵥ`{.Agda} が、章末の符号化インスタンスが符号化された構文を解釈する場になります。この章の単射性証明は、前述の後続の事実と分類だけを使います。
<!--/-->

```agda
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Numerals are distinct

The first alphabet is the numeral map, and its injectivity splits into two statements. Monotonicity says a smaller numeral belongs to a larger one. The induction is on the *larger* index, so that each inductive step is the syntactic successor and no arithmetic on indices appears. The step case divides by the trichotomy on natural numbers into a strictly smaller index and an equal one, each settled by a successor membership fact; the base case is vacuous. Injectivity then follows: if the codes of two distinct indices agreed, monotonicity would place a numeral inside itself, which membership irreflexivity forbids.
<!--zh-->
## 数码两两相异

第一个字母表是数码映射，其单射性分成两个命题。单调性说较小的数码属于较大的。归纳沿**较大的**那个序号进行，使每个归纳步都是句法上的后继，索引上不出现任何算术。后继一步按自然数三歧性分成严格更小的序号与相等的序号，各由一条关于后继的隶属事实解决；基例则是空洞的。单射性随之得出：若两个相异序号的码相同，单调性会把某个数码放进它自身，而隶属的无自环性禁止这一点。
<!--ja-->
## 数項は互いに異なる

最初の字母は数項写像であり、その単射性は 2 つの主張に分かれます。単調性は、小さい数項が大きい数項に属すと言います。帰納は**大きい**ほうの添字に対して行い、各ステップが構文的な後続になるようにして、添字の算術を一切現れさせません。ステップの場合は自然数の三分律によって「真に小さい添字か等しい添字か」に分かれ、それぞれ後続の所属事実が解決します。基底の場合は空虚です。すると単射性が従います。異なる添字の符号が一致すれば、単調性がある数項をそれ自身の内に置くことになり、所属の反射なし性がこれを禁じます。
<!--/-->

<!--en-->
The stepping stone `#⊆suc`{.Agda} says that any member of `# n`{.Agda} is also a member of the next numeral; it is exactly the successor fact that a member of a set belongs to that set's successor. In the base case of `#mono`{.Agda} there is nothing to prove, since no index is strictly below zero and the hypothesis `m < 0`{.Agda} is refuted outright.
<!--zh-->
垫脚石 `#⊆suc`{.Agda} 说：`# n`{.Agda} 的任何成员也是下一个数码的成员；这正是「集合的成员属于该集合的后继」这条后继事实。`#mono`{.Agda} 的基例无事可证，因为没有序号严格小于零，假设 `m < 0`{.Agda} 被直接驳倒。
<!--ja-->
足場となる `#⊆suc`{.Agda} は、`# n`{.Agda} の任意の元が次の数項の元でもあることを述べます。これは「集合の元はその後続に属する」という後続の事実そのものです。`#mono`{.Agda} の基底の場合は証明すべきことがありません。ゼロより真に小さい添字は存在せず、仮定 `m < 0`{.Agda} はそのまま反証されます。
<!--/-->

```agda
#⊆suc : (n : ℕ) {x : S} → ⟨ x ∈ˢ (# n) ⟩ → ⟨ x ∈ˢ (# (suc n)) ⟩
#⊆suc n {x} = ∈sucV-inl {A = # n} {x = x}

#mono : (m n : ℕ) → m < n → ⟨ (# m) ∈ˢ (# n) ⟩
#mono m zero    m<0    = Empty.rec (¬-<-zero m<0)
#mono m (suc n) m<sucn = Sum.rec
```

<!--en-->
In the successor step, `<-split`{.Agda} merely says `m < suc n`{.Agda} splits into `m < n`{.Agda} or `m ≡ n`{.Agda}. In the first branch the induction hypothesis gives `# m ∈ # n`{.Agda}, and `#⊆suc`{.Agda} promotes it into the successor. In the second branch the two numerals coincide, and a set belongs to its own successor, so transporting along the reversal of `m ≡ n`{.Agda} turns the membership `# n ∈ # (suc n)`{.Agda} into the one wanted.
<!--zh-->
在后继一步，`<-split`{.Agda} 只是说 `m < suc n`{.Agda} 分裂为 `m < n`{.Agda} 或 `m ≡ n`{.Agda}。第一支中归纳假设给出 `# m ∈ # n`{.Agda}，再由 `#⊆suc`{.Agda} 提升到后继。第二支中两个数码重合，而一个集合属于它自己的后继，于是沿 `m ≡ n`{.Agda} 的逆向传输把隶属 `# n ∈ # (suc n)`{.Agda} 变成所要的那一个。
<!--ja-->
後続のステップでは、`<-split`{.Agda} は `m < suc n`{.Agda} が `m < n`{.Agda} か `m ≡ n`{.Agda} に分かれると言うだけです。第 1 の枝では帰納仮定が `# m ∈ # n`{.Agda} を与え、`#⊆suc`{.Agda} がそれを後続へ持ち上げます。第 2 の枝では 2 つの数項が一致しており、集合は自分自身の後続に属するので、`m ≡ n`{.Agda} の逆向きの輸送によって所属 `# n ∈ # (suc n)`{.Agda} が求めるものに変わります。
<!--/-->

```agda
  (λ m<n → #⊆suc n (#mono m n m<n))
  (λ m≡n → subst (λ M → ⟨ (# M) ∈ˢ (# (suc n)) ⟩) (sym m≡n) (self∈sucV (# n)))
  (<-split m<sucn)
```

<!--en-->
Injectivity follows by trichotomy on the indices. Equal indices are the conclusion. If `m < n`{.Agda}, monotonicity gives `# m ∈ # n`{.Agda}, and the assumed equation `# m ≡ # n`{.Agda} transports this membership into `# n ∈ # n`{.Agda}, which membership irreflexivity forbids. The remaining case `n < m`{.Agda} is the mirror image, with the transport run in the other direction.
<!--zh-->
单射性由序号上的三歧得出。序号相等即是结论。若 `m < n`{.Agda}，单调性给出 `# m ∈ # n`{.Agda}，而假设的等式 `# m ≡ # n`{.Agda} 把这个隶属传输为 `# n ∈ # n`{.Agda}，这与隶属的无自环性矛盾。剩下的情形 `n < m`{.Agda} 是镜像，传输沿另一方向进行。
<!--ja-->
単射性は添字の三分律から従います。添字が等しければそれが結論です。`m < n`{.Agda} なら単調性から `# m ∈ # n`{.Agda} が得られ、仮定の等式 `# m ≡ # n`{.Agda} がこの所属を `# n ∈ # n`{.Agda} へ輸送しますが、所属の反射なし性がこれを禁じます。残りの `n < m`{.Agda} の場合は鏡像で、輸送は逆向きに行われます。
<!--/-->

<!--en-->
The strictly-smaller case is the instructive one. The membership `# m ∈ # n`{.Agda} speaks about the numeral `# m`{.Agda}; rewriting its type along `# m ≡ # n`{.Agda} replaces that set by `# n`{.Agda} everywhere, producing an inhabitant of `# n ∈ # n`{.Agda}. Irreflexivity of membership consumes this inhabitant into an element of the empty type, so the case cannot arise.
<!--zh-->
严格更小的情形最具启发性。隶属 `# m ∈ # n`{.Agda} 说的是数码 `# m`{.Agda}；沿 `# m ≡ # n`{.Agda} 对其类型作重写后，那个集合处处被替换为 `# n`{.Agda}，得到 `# n ∈ # n`{.Agda} 的一个元素。隶属的无自环性把这个元素消去为空类型的元素，所以这种情形不可能出现。
<!--ja-->
真に小さい場合が示唆的です。所属 `# m ∈ # n`{.Agda} は数項 `# m`{.Agda} について述べていますが、`# m ≡ # n`{.Agda} に沿ってその型を書き換えると、その集合は至る所 `# n`{.Agda} に置き換えられ、`# n ∈ # n`{.Agda} の要素が得られます。所属の反射なし性はこの要素を空型の元へと送るので、この場合は生じえません。
<!--/-->

```agda
#-inj : (m n : ℕ) → # m ≡ # n → m ≡ n
#-inj m n #m≡#n with m ≟ n
... | eq m≡n = m≡n
... | lt m<n = Empty.rec (∈-irrefl (# n)
      (subst (λ z → ⟨ z ∈ˢ (# n) ⟩) #m≡#n (#mono m n m<n)))
```

<!--en-->
The greater case is identical with the roles of `m` and `n` exchanged: monotonicity puts `# n`{.Agda} inside `# m`{.Agda}, the equation transports in the opposite direction, and irreflexivity of `# m`{.Agda} refutes it. The variant `#-inj′`{.Agda} packages the same statement with the indices implicit, which is the shape the coding interface consumes.
<!--zh-->
更大的情形完全相同，只是交换 `m` 与 `n` 的角色：单调性把 `# n`{.Agda} 放进 `# m`{.Agda}，等式沿反方向传输，而 `# m`{.Agda} 的无自环性将它驳倒。变体 `#-inj′`{.Agda} 把同一个命题包装成序号隐式的形式，这正是编码接口所消耗的形状。
<!--ja-->
大きい場合は `m` と `n` の役割を入れ替えただけでまったく同じです。単調性が `# n`{.Agda} を `# m`{.Agda} の内に置き、等式が逆向きに輸送し、`# m`{.Agda} の反射なし性がこれを反証します。変種 `#-inj′`{.Agda} は同じ主張を添字を暗黙にした形でまとめたもので、符号化インターフェースが消費するのはこの形です。
<!--/-->

```agda
... | gt n<m = Empty.rec (∈-irrefl (# m)
      (subst (λ z → ⟨ z ∈ˢ (# m) ⟩) (sym #m≡#n) (#mono n m n<m)))

#-inj′ : ∀ {m n} → # m ≡ # n → m ≡ n
#-inj′ {m} {n} = #-inj m n
```

<!--en-->
## Kuratowski pairing

The second injective alphabet is the Kuratowski pair: the code of `a` and `b` is the set whose members are the singleton `⁅ a ⁆s`{.Agda} and the unordered pair `⁅ a , b ⁆`{.Agda}. Note the distinction between the outer ordered pair, which records order, and its inner unordered pair, which does not. Injectivity means both components are recoverable from the code, and this recovery is driven entirely by the classification specifications: membership in a singleton is equality to its element, and membership in an unordered pair merely means equality to one of the two.
<!--zh-->
## Kuratowski 配对

第二个单射字母表是 Kuratowski 对：`a` 与 `b` 的码是以单点集 `⁅ a ⁆s`{.Agda} 与无序对 `⁅ a , b ⁆`{.Agda} 为成员的那个集合。注意区分记录了次序的外层有序对与不记录次序的内层无序对。单射性意为两个分量都能从码中还原，而这种还原完全由分类规格驱动：属于单点集等于等于其唯一的元素，属于无序对仅仅意味着等于两个分量之一。
<!--ja-->
## Kuratowski 対

2 番目の単射な字母は Kuratowski 対です。`a` と `b` の符号は、一元集合 `⁅ a ⁆s`{.Agda} と非順序対 `⁅ a , b ⁆`{.Agda} を元として持つ集合です。順序を記録する外側の順序対と、順序を記録しない内側の非順序対を区別してください。単射性とは両成分が符号から復元できることであり、この復元は完全に分類仕様によって進められます。一元集合への所属はその唯一の元に等しいことであり、非順序対への所属は切り詰められた意味で 2 つの成分のどちらかに等しいことにすぎません。
<!--/-->

<!--en-->
The singleton classification is named once in both directions. `∈singl`{.Agda} says a member of `⁅ a ⁆s`{.Agda} must equal `a`{.Agda}, and `singl∈`{.Agda} says equality suffices to belong. Both are projections of the same classification record for the singleton package.
<!--zh-->
单点集分类在两个方向上各命名一次。`∈singl`{.Agda} 说 `⁅ a ⁆s`{.Agda} 的成员必等于 `a`{.Agda}，`singl∈`{.Agda} 说等式足以保证属于。二者都是单点集包同一分类记录的投影。
<!--ja-->
一元集合の分類は両方向に一度だけ名前を与えられます。`∈singl`{.Agda} は `⁅ a ⁆s`{.Agda} の元が `a`{.Agda} と等しいことを、`singl∈`{.Agda} は等しければ属することを述べます。どちらも一元集合パッケージの同じ分類レコードの射影です。
<!--/-->

```agda
private
  ∈singl : {a x : S} → ⟨ x ∈ₛ ⁅ a ⁆s ⟩ → x ≡ a
  ∈singl {a} {x} = SetPackage.classification (SingletonPackage a) x .fst

  singl∈ : {a x : S} → x ≡ a → ⟨ x ∈ₛ ⁅ a ⁆s ⟩
  singl∈ {a} {x} = SetPackage.classification (SingletonPackage a) x .snd
```

<!--en-->
For unordered pairs, the classification has the shape of a truncated disjunction: a member of `⁅ a , b ⁆`{.Agda} is, merely, equal to `a` or to `b`. The two introduction lemmas supply the left and right disjuncts as truncated witnesses, so membership can be produced from either equality without choosing anything.
<!--zh-->
对无序对，分类呈截断析取的形状：`⁅ a , b ⁆`{.Agda} 的成员仅仅等于 `a` 或等于 `b`。两条引入引理分别以截断的见证提供左右析取支，于是任一等式都能产生成员，而无需选择任何东西。
<!--ja-->
非順序対については、分類は切り詰められた選言の形を持ちます。`⁅ a , b ⁆`{.Agda} の元は、切り詰められた意味で `a` に等しいか `b` に等しい。2 つの導入補題は左右の選言支を切り詰められた証拠として供給するので、いずれかの等式から何も選ばずに所属を作れます。
<!--/-->

```agda

  self∈singl : (a : S) → ⟨ a ∈ₛ ⁅ a ⁆s ⟩
  self∈singl a = singl∈ refl

  inl∈⁅,⁆ : {a b x : S} → x ≡ a → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩
  inl∈⁅,⁆ {a} {b} {x} e = pairing-ax a b x .snd ∣ inl e ∣₁

  inr∈⁅,⁆ : {a b x : S} → x ≡ b → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩
```

<!--en-->
A singleton determines its element: if `⁅ a ⁆s ≡ ⁅ c ⁆s`{.Agda}, transport the membership `a ∈ ⁅ a ⁆s`{.Agda} along this path and classify the result; it must equal `c`{.Agda}. The elimination is into the path proposition `a ≡ c`{.Agda}, which is allowed since `V`{.Agda} is an h-set.
<!--zh-->
单点集决定其元素：若 `⁅ a ⁆s ≡ ⁅ c ⁆s`{.Agda}，沿这条路径传输隶属 `a ∈ ⁅ a ⁆s`{.Agda} 并对结果分类，结果必等于 `c`{.Agda}。消去指向路径命题 `a ≡ c`{.Agda}，由于 `V`{.Agda} 是 h-集，这是允许的。
<!--ja-->
一元集合はその元を決定します。`⁅ a ⁆s ≡ ⁅ c ⁆s`{.Agda} なら、所属 `a ∈ ⁅ a ⁆s`{.Agda} をこのパスに沿って輸送し、結果を分類すれば、それは `c`{.Agda} と等しくなければなりません。消去はパス命題 `a ≡ c`{.Agda} へ向かい、`V`{.Agda} が h-集合なのでこれは許されます。
<!--/-->

```agda
  inr∈⁅,⁆ {a} {b} {x} e = pairing-ax a b x .snd ∣ inr e ∣₁

  mem⁅,⁆ : {a b x : S} → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩ → ∥ (x ≡ a) ⊎ (x ≡ b) ∥₁
  mem⁅,⁆ {a} {b} {x} = pairing-ax a b x .fst

  singl-inj : {a c : S} → ⁅ a ⁆s ≡ ⁅ c ⁆s → a ≡ c
  singl-inj {a} {c} q = ∈singl (subst (λ s → ⟨ a ∈ₛ s ⟩) q (self∈singl a))
```

<!--en-->
A singleton that happens to equal an unordered pair forces both components down to its element. Each component belongs to the unordered pair merely, so transporting the membership across `sym q` and classifying yields a path from that component to `a`{.Agda}; both eliminations target the pair of path propositions `(c ≡ a) × (d ≡ a)`{.Agda}. This degenerate comparison is exactly the hard case of pair injectivity below.
<!--zh-->
若一个单点集恰好等于某个无序对，则无序对的两个分量都被压到该单点集的元素。每个分量仅仅属于该无序对，于是沿 `sym q` 传输其隶属再分类，得到从该分量到 `a`{.Agda} 的路径；两个消去都指向路径命题的对 `(c ≡ a) × (d ≡ a)`{.Agda}。这个退化比较正是下文配对单射性的难处所在。
<!--ja-->
一元集合がたまたま非順序対と等しいときは、非順序対の両成分がその一元集合の元へ押し下げられます。各成分は切り詰められた意味でその非順序対に属するので、所属を `sym q` の向きに輸送して分類すると、その成分から `a`{.Agda} へのパスが得られます。どちらの消去もパス命題の組 `(c ≡ a) × (d ≡ a)`{.Agda} をターゲットにします。この退化的な比較こそ、後の対の単射性の難所です。
<!--/-->

```agda

  singl≡pair : {a c d : S} → ⁅ a ⁆s ≡ ⁅ c , d ⁆ → (c ≡ a) × (d ≡ a)
  singl≡pair {a} {c} {d} q =
      ∈singl (subst (λ s → ⟨ c ∈ₛ s ⟩) (sym q) (inl∈⁅,⁆ {a = c} {b = d} refl))
    , ∈singl (subst (λ s → ⟨ d ∈ₛ s ⟩) (sym q) (inr∈⁅,⁆ {a = c} {b = d} refl))
```

<!--en-->
The injectivity proof of the pair is now assembled from the four comparison lemmas. Given `p : pr a b ≡ pr c d`{.Agda}, the singleton part of the code is a member of both sides, so transporting its membership forward along `p` and classifying yields, merely, `⁅ a ⁆s ≡ ⁅ c ⁆s` or `⁅ a ⁆s ≡ ⁅ c , d ⁆`; the first disjunct gives `a ≡ c` immediately and the second through the reversal of `singl≡pair`. The unordered-pair part is harder because its membership alone may not determine the second component: when the code collapses, `⁅ a , b ⁆`{.Agda} has matched a singleton on the left or the right, and knowing which side it matched is not enough. So two truncated records are kept, one transported forward along `p` from membership of `⁅ a , b ⁆`{.Agda} in `pr a b`{.Agda}, and one transported backward along the reversal of `p` from membership of `⁅ c , d ⁆`{.Agda} in `pr c d`{.Agda}. The backward record supplies exactly the information the degenerate branches lack, and under the temporary hypothesis `a ≡ b`{.Agda}, the case where the whole code collapses to a singleton of singletons, it converts a recovered `a ≡ b`{.Agda} into `d ≡ b`{.Agda}. Every elimination of a truncated disjunction in this proof targets a proposition built from paths in the h-set `V`{.Agda}, so no witness is ever chosen.
<!--zh-->
配对的单射性证明现在由四条比较引理组装而成。给定 `p : pr a b ≡ pr c d`{.Agda}，码的单点集部分同时属于两侧，于是沿 `p` 向前传输其隶属再分类，仅仅得到 `⁅ a ⁆s ≡ ⁅ c ⁆s` 或 `⁅ a ⁆s ≡ ⁅ c , d ⁆`；第一支立即给出 `a ≡ c`，第二支经 `singl≡pair` 的逆向给出。无序对部分更难，因为仅凭其隶属未必能确定第二分量：当码退化时，`⁅ a , b ⁆`{.Agda} 在左或右与一个单点集相配，而知道它配的是哪一侧并不够。于是保留两条截断记录：一条是 `⁅ a , b ⁆`{.Agda} 在 `pr a b`{.Agda} 中的隶属沿 `p` 向前传输所得，另一条是 `⁅ c , d ⁆`{.Agda} 在 `pr c d`{.Agda} 中的隶属沿 `p` 的逆向传输所得。向后那条记录恰好补上退化分支所缺的信息；在临时假设 `a ≡ b`{.Agda} 之下，即整个码退化为「单点集的单点集」的情形，它把还原出的 `a ≡ b`{.Agda} 转换为 `d ≡ b`{.Agda}。本证明中对截断析取的每次消去都指向由 h-集 `V`{.Agda} 中路径构成的命题，因此从不选出任何见证。
<!--ja-->
対の単射性の証明は、4 つの比較補題から組み上げられます。`p : pr a b ≡ pr c d`{.Agda} が与えられると、符号の一元集合の部分は両側に属するので、その所属を `p` に沿って前向きに輸送して分類すれば、切り詰められた意味で `⁅ a ⁆s ≡ ⁅ c ⁆s` か `⁅ a ⁆s ≡ ⁅ c , d ⁆` が得られます。第 1 の選言支は直ちに `a ≡ c` を与え、第 2 の選言支は `singl≡pair` の逆向きを通して与えます。非順序対の部分はより難しく、所属だけでは第 2 成分が決まらないことがあります。符号が潰れるとき、`⁅ a , b ⁆`{.Agda} は左か右で一元集合と一致しますが、どちら側と一致したかを知るだけでは足りません。そこで 2 つの切り詰められた記録を取っておきます。1 つは `⁅ a , b ⁆`{.Agda} が `pr a b`{.Agda} に属することから `p` に沿って前向きに輸送したもの、もう 1 つは `⁅ c , d ⁆`{.Agda} が `pr c d`{.Agda} に属することから `p` の逆向きに輸送したものです。後ろ向きの記録が、退化した枝に欠ける情報をまさに補います。一時的な仮定 `a ≡ b`{.Agda} のもと、すなわち符号全体が一元集合の一元集合に潰れる場合には、復元した `a ≡ b`{.Agda} を `d ≡ b`{.Agda} に変換します。この証明での切り詰められた選言の消去はすべて、h-集合 `V`{.Agda} のパスからできる命題をターゲットにするので、証拠が選び出されることはありません。
<!--/-->

<!--en-->
The code `pr a b`{.Agda} is the unordered pair whose two members are the singleton `⁅ a ⁆s`{.Agda} and the unordered pair `⁅ a , b ⁆`{.Agda}. The outer expression is the ordered Kuratowski code, and it should not be confused with its second ingredient: the inner `⁅ a , b ⁆`{.Agda} records no order, the whole code does. Injectivity is the claim that an equality of codes `pr a b ≡ pr c d` determines both inputs, that is, it yields paths `a ≡ c` and `b ≡ d`.
<!--zh-->
码 `pr a b`{.Agda} 是以单点集 `⁅ a ⁆s`{.Agda} 与无序对 `⁅ a , b ⁆`{.Agda} 为两个成员的无序对。外层表达式是有序的 Kuratowski 码，不要与它的第二个原料混淆：内层的 `⁅ a , b ⁆`{.Agda} 不记录次序，记录次序的是整个码。单射性是说码的等式 `pr a b ≡ pr c d` 决定两个输入，即给出路径 `a ≡ c` 与 `b ≡ d`。
<!--ja-->
符号 `pr a b`{.Agda} は、一元集合 `⁅ a ⁆s`{.Agda} と非順序対 `⁅ a , b ⁆`{.Agda} を 2 つの元として持つ非順序対です。外側の式が順序を記録する Kuratowski 符号であり、その 2 番目の材料である内側の `⁅ a , b ⁆`{.Agda} と混同しないでください。内側は順序を記録せず、順序を記録するのは符号全体です。単射性とは、符号の等式 `pr a b ≡ pr c d` が両方の入力を決定する、つまりパス `a ≡ c` と `b ≡ d` を与えるという主張です。
<!--/-->

```agda
pr : S → S → S
pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆

pr-inj : ∀ {a b c d} → pr a b ≡ pr c d → (a ≡ c) × (b ≡ d)
pr-inj {a} {b} {c} {d} p = a≡c , b≡d
  where
```

<!--en-->
First component. The singleton part `⁅ a ⁆s`{.Agda} belongs to `pr a b`{.Agda} by its right disjunct. Transporting this membership along `p` and classifying gives, merely, `⁅ a ⁆s ≡ ⁅ c ⁆s` or `⁅ a ⁆s ≡ ⁅ c , d ⁆` (this is `H₁`). In the first disjunct `singl-inj` yields `a ≡ c` directly. In the second, the comparison `singl≡pair` forces `c ≡ a`, and its reversal is what is wanted. The truncated disjunction is eliminated into the path proposition `a ≡ c`{.Agda}, which is permitted since `V`{.Agda} is an h-set.
<!--zh-->
第一分量。单点集部分 `⁅ a ⁆s` 经其右析取支属于 `pr a b`{.Agda}。把这个隶属沿 `p` 传输再分类，仅仅得到 `⁅ a ⁆s ≡ ⁅ c ⁆s` 或 `⁅ a ⁆s ≡ ⁅ c , d ⁆` (这就是 `H₁`)。第一支由 `singl-inj` 直接给出 `a ≡ c`。第二支中比较 `singl≡pair` 迫使 `c ≡ a`，取其逆向即所求。截断析取消去到路径命题 `a ≡ c`{.Agda}，由于 `V`{.Agda} 是 h-集，这是允许的。
<!--ja-->
第 1 成分。一元集合の部分 `⁅ a ⁆s` は右の選言支によって `pr a b`{.Agda} に属するので、この所属を `p` に沿って輸送して分類すると、切り詰められた意味で `⁅ a ⁆s ≡ ⁅ c ⁆s` か `⁅ a ⁆s ≡ ⁅ c , d ⁆` が得られます (これが `H₁` です)。第 1 の選言支では `singl-inj` が直接 `a ≡ c` を与えます。第 2 の選言支では比較 `singl≡pair` が `c ≡ a` を強制し、その逆向きが求めるものです。切り詰められた選言はパス命題 `a ≡ c`{.Agda} へ消去され、`V`{.Agda} が h-集合なのでこれは許されます。
<!--/-->

```agda
  H₁ : ∥ (⁅ a ⁆s ≡ ⁅ c ⁆s) ⊎ (⁅ a ⁆s ≡ ⁅ c , d ⁆) ∥₁
  H₁ = mem⁅,⁆ (subst (λ s → ⟨ ⁅ a ⁆s ∈ₛ s ⟩) p (inl∈⁅,⁆ {b = ⁅ a , b ⁆} refl))

  a≡c : a ≡ c
  a≡c = PT.rec (setIsSet a c)
    (Sum.rec singl-inj (λ e → sym (singl≡pair e .fst))) H₁
```

<!--en-->
Second component. Two truncated records are gathered. `H₂` comes from membership of the unordered-pair part in `pr a b`{.Agda}, transported forward along `p`: merely, `⁅ a , b ⁆`{.Agda} equals `⁅ c ⁆s` or `⁅ c , d ⁆`. `K` runs the same argument backwards, from membership of `⁅ c , d ⁆`{.Agda} in `pr c d`{.Agda} transported along `sym p`: merely, `⁅ c , d ⁆`{.Agda} equals `⁅ a ⁆s` or `⁅ a , b ⁆`. Both are needed because in the degenerate cases below each single record leaves a gap that only the other fills.
<!--zh-->
第二分量。这里收集两条截断的记录。`H₂` 来自无序对部分在 `pr a b`{.Agda} 中的成员，沿 `p` 向前传输：仅仅有 `⁅ a , b ⁆`{.Agda} 等于 `⁅ c ⁆s` 或 `⁅ c , d ⁆`。`K` 把同一论证反向运行，从 `⁅ c , d ⁆`{.Agda} 在 `pr c d`{.Agda} 中的成员沿 `sym p` 传输得到：仅仅有 `⁅ c , d ⁆`{.Agda} 等于 `⁅ a ⁆s` 或 `⁅ a , b ⁆`。两者都需要：在下文的退化情形中，每条单独的记录都留有缺口，只有另一条能补上。
<!--ja-->
第 2 成分。ここでは切り詰められた 2 つの記録を集めます。`H₂` は非順序対の部分が `pr a b`{.Agda} に属することから来ており、`p` に沿って前向きに輸送すると、切り詰められた意味で `⁅ a , b ⁆`{.Agda} が `⁅ c ⁆s` か `⁅ c , d ⁆` に等しいことが分かります。`K` は同じ議論を逆向きに実行し、`⁅ c , d ⁆`{.Agda} が `pr c d`{.Agda} に属することから `sym p` に沿って輸送して、切り詰められた意味で `⁅ c , d ⁆`{.Agda} が `⁅ a ⁆s` か `⁅ a , b ⁆` に等しいことを得ます。両方が必要なのは、後述の退化した場合では、1 つの記録だけでは残る隙間をもう 1 つの記録しか埋められないからです。
<!--/-->

```agda

  H₂ : ∥ (⁅ a , b ⁆ ≡ ⁅ c ⁆s) ⊎ (⁅ a , b ⁆ ≡ ⁅ c , d ⁆) ∥₁
  H₂ = mem⁅,⁆ (subst (λ s → ⟨ ⁅ a , b ⁆ ∈ₛ s ⟩) p (inr∈⁅,⁆ {a = ⁅ a ⁆s} refl))

  K : ∥ (⁅ c , d ⁆ ≡ ⁅ a ⁆s) ⊎ (⁅ c , d ⁆ ≡ ⁅ a , b ⁆) ∥₁
  K = mem⁅,⁆ (subst (λ s → ⟨ ⁅ c , d ⁆ ∈ₛ s ⟩) (sym p) (inr∈⁅,⁆ {a = ⁅ c ⁆s} refl))

  d≡b-from-K : a ≡ b → d ≡ b
```

<!--en-->
The helper `d≡b-from-K` handles the degenerate situation under the temporary hypothesis `a ≡ b`{.Agda}, where the two ingredients of the code coincide and `pr a b`{.Agda} collapses to the unordered pair `⁅ ⁅ a ⁆s , ⁅ a ⁆s ⁆`{.Agda}. Reading `K`: either `⁅ c , d ⁆`{.Agda} equals the singleton `⁅ a ⁆s`{.Agda}, whose classification forces `d ≡ a`, hence `d ≡ b`; or it equals `⁅ a , b ⁆`{.Agda}, in which case `d`{.Agda} is, merely, equal to `a` or to `b`, and both alternatives compose to `d ≡ b`. All eliminations land in the path proposition `d ≡ b`{.Agda}.
<!--zh-->
辅助引理 `d≡b-from-K` 在临时假设 `a ≡ b`{.Agda} 之下处理退化情形：码的两个原料重合，`pr a b`{.Agda} 退化为无序对 `⁅ ⁅ a ⁆s , ⁅ a ⁆s ⁆`{.Agda}。读 `K`：要么 `⁅ c , d ⁆`{.Agda} 等于单点集 `⁅ a ⁆s`{.Agda}，其分类迫使 `d ≡ a`，从而 `d ≡ b`；要么它等于 `⁅ a , b ⁆`{.Agda}，此时 `d`{.Agda} 仅仅等于 `a` 或 `b`，两种选择都能复合成 `d ≡ b`。所有消去都落入路径命题 `d ≡ b`{.Agda}。
<!--ja-->
補助補題 `d≡b-from-K` は、一時的な仮定 `a ≡ b`{.Agda} のもとで退化した状況を処理します。すなわち符号の 2 つの材料が一致し、`pr a b`{.Agda} が非順序対 `⁅ ⁅ a ⁆s , ⁅ a ⁆s ⁆`{.Agda} に退化する場合です。`K` を読むと、`⁅ c , d ⁆`{.Agda} が一元集合 `⁅ a ⁆s`{.Agda} と等しいなら、その分類から `d ≡ a`、したがって `d ≡ b` が得られます。`⁅ a , b ⁆`{.Agda} と等しいなら、`d`{.Agda} は切り詰められた意味で `a` か `b` に等しく、どちらの選択肢も合成して `d ≡ b` になります。すべての消去はパス命題 `d ≡ b`{.Agda} に着地します。
<!--/-->

```agda
  d≡b-from-K a≡b = PT.rec (setIsSet d b)
    (Sum.rec
      (λ e → singl≡pair (sym e) .snd ∙ a≡b)
      (λ e → PT.rec (setIsSet d b)
        (Sum.rec (λ d≡a → d≡a ∙ a≡b) (λ d≡b → d≡b))
```

<!--en-->
The main argument for `b ≡ d` runs through `H₂`. In its first disjunct, the inner unordered pair `⁅ a , b ⁆`{.Agda} equals the singleton `⁅ c ⁆s`{.Agda}; the comparison `singl≡pair` read backwards gives `b ≡ c`, and from `a ≡ c` and the reversal of `b ≡ c` the path `a ≡ b` follows, exactly the hypothesis the helper consumes. The helper then yields `d ≡ b`, whose reversal is the goal. This is where the backward record `K` enters: the helper is stated from `K`, so the forward classification alone does not reach this case.
<!--zh-->
`b ≡ d` 的主论证沿 `H₂` 进行。在其第一支中，内层无序对 `⁅ a , b ⁆`{.Agda} 等于单点集 `⁅ c ⁆s`{.Agda}；反向读取比较 `singl≡pair` 给出 `b ≡ c`，而由 `a ≡ c` 与 `b ≡ c` 的逆向复合得到路径 `a ≡ b`，恰好是辅助引理所消耗的假设。辅助引理随即给出 `d ≡ b`，取其逆向即目标。这正是反向记录 `K` 的用武之地：辅助引理以 `K` 为出发点，所以仅靠向前的分类到不了这个情形。
<!--ja-->
`b ≡ d` の主議論は `H₂` を通って進みます。第 1 の選言支では、内側の非順序対 `⁅ a , b ⁆`{.Agda} が一元集合 `⁅ c ⁆s`{.Agda} と等しく、比較 `singl≡pair` を逆向きに読むと `b ≡ c` が得られます。`a ≡ c` と `b ≡ c` の逆向きの合成からパス `a ≡ b` が従い、これは補助補題が消費する仮定そのものです。補助補題は次に `d ≡ b` を与え、その逆向きが目標です。ここで後ろ向きの記録 `K` が効きます。補助補題は `K` から述べられているので、前向きの分類だけではこの場合に届きません。
<!--/-->

```agda
        (mem⁅,⁆ (subst (λ s → ⟨ d ∈ₛ s ⟩) e (inr∈⁅,⁆ {a = c} refl)))))
    K

  b≡d : b ≡ d
  b≡d = PT.rec (setIsSet b d)
    (Sum.rec
```

<!--en-->
In the second disjunct of `H₂`, the two inner unordered pairs coincide, `⁅ a , b ⁆ ≡ ⁅ c , d ⁆`{.Agda}. Then `b`{.Agda} belongs to `⁅ c , d ⁆`{.Agda} merely, so classifying the membership of `b` gives `b ≡ c` or `b ≡ d`. The second alternative is already the goal; the first reduces to it through the same composition and helper as before.
<!--zh-->
在 `H₂` 的第二支中，两个内层无序对重合：`⁅ a , b ⁆ ≡ ⁅ c , d ⁆`{.Agda}。于是 `b`{.Agda} 仅仅属于 `⁅ c , d ⁆`{.Agda}，对 `b` 的成员作分类给出 `b ≡ c` 或 `b ≡ d`。第二种选择已是目标；第一种经与之前相同的复合和辅助引理也归结为它。
<!--ja-->
`H₂` の第 2 の選言支では、内側の 2 つの非順序対が一致します。`⁅ a , b ⁆ ≡ ⁅ c , d ⁆`{.Agda}。すると `b`{.Agda} は切り詰められた意味で `⁅ c , d ⁆`{.Agda} に属するので、`b` の所属を分類して `b ≡ c` か `b ≡ d` が得られます。後者はそのまま目標で、前者は前に示したのと同じ合成と補助補題を経て後者に帰着します。
<!--/-->

```agda
      (λ e → let b≡c = singl≡pair (sym e) .snd
             in sym (d≡b-from-K (a≡c ∙ sym b≡c)))
      (λ e → PT.rec (setIsSet b d)
        (Sum.rec
          (λ b≡c → sym (d≡b-from-K (a≡c ∙ sym b≡c)))
```

<!--en-->
The two branches combine into `b ≡ d`, completing `pr-inj`: both components of the Kuratowski code are recoverable from an equality of codes. Every branch eliminated a truncated disjunction into a proposition built from paths in the h-set `V`{.Agda}; no witness was ever chosen from a truncation.
<!--zh-->
两个分支合成为 `b ≡ d`，完成 `pr-inj`：Kuratowski 码的两个分量都可从码的等式中还原。每个分支都把一个截断析取消去到由 h-集 `V`{.Agda} 中路径构成的命题；从未从截断中选出任何见证。
<!--ja-->
2 つの枝が合わさって `b ≡ d` となり、`pr-inj` が完結します。Kuratowski 符号の両成分は符号の等式から復元できるということです。どの枝も、切り詰められた選言を h-集合 `V`{.Agda} のパスからできる命題へ消去したものであり、切り詰めから証拠を選び出した箇所はありません。
<!--/-->

```agda
          (λ b≡d → b≡d))
        (mem⁅,⁆ (subst (λ s → ⟨ b ∈ₛ s ⟩) e (inr∈⁅,⁆ {a = a} refl)))))
    H₂
```

<!--en-->
## The instance

With both injective alphabets in hand, the generic coding construction of FOL.Coding can be applied to the hierarchy: an injective pairing and an injective numeral map are its two parameters. The resulting `VCode`{.Agda} assigns to terms and formulas over the hierarchy's carrier codes that are themselves sets of the hierarchy. It does not make every set a code; it gives set-valued codes for the coded syntax.

Note the level: `VCode`{.Agda} is taken at `ℓ-suc ℓ`{.Agda}, the level of the truth algebra over which the structure `𝒮ᵥ`{.Agda} is a `ZFStructure`{.Agda}. This universe index is a type-theoretic level, not a stage of the hierarchy.
<!--zh-->
## 实例

有了两个单射字母表，FOL.Coding 的通用编码构造即可施于层级：单射的配对与单射的数码映射是它的两个参数。得到的 `VCode`{.Agda} 给层级载体上的词项与公式指派本身仍是层级集合的码。它并不把每个集合都变成码；它为被编码的语法提供取值为集合的码。

注意层级：`VCode`{.Agda} 取在 `ℓ-suc ℓ`{.Agda} 上，即结构 `𝒮ᵥ`{.Agda} 作为 `ZFStructure`{.Agda} 所处的真值代数的层级。这个宇宙指标是类型论意义上的层级，不是层级的阶段。
<!--ja-->
## 具体化

2 つの単射な字母がそろったので、FOL.Coding の一般的な符号化構成を階層に適用できます。単射な対の操作と単射な数項写像がその 2 つのパラメータです。得られる `VCode`{.Agda} は、階層の台の上の項と論理式に対して、それ自身が階層の集合である符号を割り当てます。すべての集合を符号にするのではなく、符号化された構文に対して集合値の符号を与えるものです。

レベルに注意してください。`VCode`{.Agda} はレベル `ℓ-suc ℓ`{.Agda} で取られます。これは、構造 `𝒮ᵥ`{.Agda} が `ZFStructure`{.Agda} となっている真理値代数のレベルです。この宇宙の指標は型理論のレベルであって、階層の段階ではありません。
<!--/-->

<!--en-->
The instantiation passes the level `ℓ-suc ℓ`{.Agda}, the structure `𝒮ᵥ`{.Agda}, and the four pieces established above: `pr`{.Agda} with `pr-inj`, and the numeral map `#_`{.Agda} with `#-inj′`. No classical axiom, resizing, or choice hypothesis enters; the instance rests on the classification specifications and the two injectivity proofs alone.
<!--zh-->
实例化传入层级 `ℓ-suc ℓ`{.Agda}、结构 `𝒮ᵥ`{.Agda}，以及上文确立的四份数据：`pr`{.Agda} 与 `pr-inj`，数码映射 `#_`{.Agda} 与 `#-inj′`。没有任何经典公理、resizing 或选择假设进入；该实例只依赖分类规格与两条单射性证明。
<!--ja-->
インスタンス化では、レベル `ℓ-suc ℓ`{.Agda}、構造 `𝒮ᵥ`{.Agda}、そして上で確立した 4 つのデータ、すなわち `pr-inj` を伴う `pr`{.Agda} と、`#-inj′` を伴う数項写像 `#_`{.Agda} を渡します。古典的公理・リサイズ・選択の仮定は一切使われず、このインスタンスは分類仕様と 2 つの単射性証明だけに依存します。
<!--/-->

```agda
module VCode = FOL.Coding {ℓ-suc ℓ} 𝒮ᵥ pr pr-inj #_ #-inj′
```

<!--en-->
## Recap

The two injective operations the generic coding needs were already available in the hierarchy. Numerals are injective: `#-inj`{.Agda} follows from monotonicity and membership irreflexivity under the natural-number trichotomy. Kuratowski pairs are injective: `pr-inj`{.Agda} recovers both components through the classification specifications for singletons and unordered pairs. The instantiation `VCode`{.Agda} therefore supplies the FOL.Coding construction over the hierarchy, at level `ℓ-suc ℓ`{.Agda} and without any classical hypothesis. Terms and formulas over the hierarchy's sets now have codes that are sets of `V`{.Agda}, and the `Codes`{.Agda} relation is available to reason about them.
<!--zh-->
## 小结

通用编码所需的两个单射操作原本就在层级之中。数码单射：`#-inj`{.Agda} 由单调性与隶属的无自环性、在自然数三歧性之下得出。Kuratowski 对单射：`pr-inj`{.Agda} 经单点集与无序对的分类规格还原两个分量。于是实例 `VCode`{.Agda} 在层级 `ℓ-suc ℓ`{.Agda} 上、且不带任何经典假设地供给了 FOL.Coding 的构造。层级集合上的词项与公式如今拥有本身是 `V`{.Agda} 中集合的码，`Codes`{.Agda} 关系可用于对它们推理。
<!--ja-->
## まとめ

一般的な符号化が必要とする 2 つの単射な操作は、もとから階層の中にありました。数項は単射です。`#-inj`{.Agda} は単調性と所属の反射なし性から、自然数の三分律のもとで従います。Kuratowski 対も単射です。`pr-inj`{.Agda} は一元集合と非順序対の分類仕様を通して両成分を復元します。したがってインスタンス `VCode`{.Agda} は、レベル `ℓ-suc ℓ`{.Agda} で、しかもいかなる古典的仮定もなしに、階層の上への FOL.Coding の構成を供給します。階層の集合上の項と論理式は今や `V`{.Agda} の集合である符号を持ち、`Codes`{.Agda} 関係でそれらについて推論できます。
<!--/-->
