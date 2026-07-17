# The classical boundary

<!--en-->
Set theory as most readers know it is classical: excluded middle is ambient air. The
host, however, is constructive, and this book keeps the boundary between the two
visible as a matter of law. The rule, fixed in the Charter, is that classical
principles enter as **explicit parameters**, never as global assumptions: a chapter
that reasons classically says so in its own interface, the type checker polices the
boundary, and there is not a single `postulate` in this book. This chapter states
the one classical principle everything later appeals to, and banks its two basic
dividends.
<!--zh-->
多数读者熟悉的集合论是经典的：排中律如空气般无处不在。然而宿主是构造性的，本书把两者之间的边界作为法条保持可见。纲领定下的规则是：经典原理一律作为**显式参数**进入，绝不作为全局假设。凡经典论证的章节都在自己的接口上言明，类型检查器守卫这条边界，全书没有一个 `postulate`。本章陈述后文一切经典论证所诉诸的那唯一原理，并存入它的两笔基本红利。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module Base.Classical where

open import Base.Prelude
open import Base.Truth
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.Equiv using ( _≃_; propBiimpl→Equiv )
open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
open import Cubical.Functions.Logic using ( ⇔toPath )
```

<!--en-->
## The statement
<!--zh-->
## 陈述
<!--/-->

```agda
LEM : ∀ ℓ → Type (ℓ-suc ℓ)
LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
```

<!--en-->
`LEM ℓ`{.Agda} says: every proposition at level `ℓ` is either true or false. Why
this particular form? In univalent foundations a type-level global choice or
excluded middle is inconsistent with univalence; what can consistently be assumed is
exactly this propositional form, quantified over `hProp`{.Agda}. The foundation
itself forces the honest phrasing.

A chapter that works classically takes `(lem : ∀ {ℓ} → LEM ℓ)`{.Agda} in its module
telescope and passes it along when importing other classical chapters. The
consequence is worth pausing on: **whether a theorem uses excluded middle is a
compile-time fact.** The classical debt is part of a chapter's type, visible at
every import site, instead of an invisible global axiom; and since nothing is
postulated, the whole book carries Agda's `--safe` seal.
<!--zh-->
`LEM ℓ`{.Agda} 说的是：层级 `ℓ` 上的每个命题要么真要么假。为什么取这个形式？在 univalent 基础中，类型层的全局选择或排中律与 univalence 不相容；能够一致地假设的恰是这个对 `hProp`{.Agda} 量化的命题形式。是基础本身逼出了这个诚实的措辞。

经典论证的章节在模块参数表中取 `(lem : ∀ {ℓ} → LEM ℓ)`{.Agda}，并在导入其他经典章节时把它传递下去。这带来一个值得停下体会的后果：**一条定理是否用了排中律，是编译期事实。**经典债务是章节类型的一部分，在每个导入处可见，而不是一条看不见的全局公理；又因为无一处 postulate，全书佩戴 Agda 的 `--safe` 印章。
<!--/-->

<!--en-->
## The first dividend: a small classifier
<!--zh-->
## 第一笔红利：小分类器
<!--/-->

<!--en-->
Classically a proposition has only two possible values, and that innocent remark has
universe-level teeth. First: the entire type of truth values collapses to a
two-element type, `Lift Bool ≃ hProp ℓ`{.Agda}, at **every** level `ℓ`. The construction is
arranged so that all the real work is constructive: the four helpers below take a
**decision** of a proposition (a proof, or a refutation) as an ordinary argument,
and excluded middle enters only at the final assembly, to supply those decisions.
<!--zh-->
经典地看，命题只有两个可能的值，而这句不起眼的话在宇宙层级上有实实在在的后果。第一笔：整个真值类型坍缩为二元类型，在**每一个**层级 `ℓ` 上都有 `Lift Bool ≃ hProp ℓ`{.Agda}。构造被刻意安排为：全部实际工作都是构造性的，下面四个助手把命题的**判定** (一个证明，或一个反驳) 当作普通参数接收；排中律只在最后的总装处出场，负责供应这些判定。
<!--/-->

<!--en-->
First the decoding direction, from Booleans to propositions. `decodeB`{.Agda} sends
`true`{.Agda} to the algebra's `⊤` and `false`{.Agda} to its `⊥`, each written by
qualified projection (`TruthAlg.⊤ hPropAlg`{.Agda}); by definitional transparency the `⊥`
here is the pair `(⊥* , isProp⊥*)`{.Agda} itself. The domain is `Lift {ℓ-zero} {ℓ} Bool`{.Agda} rather than
bare `Bool`{.Agda} because `Bool`{.Agda} lives at the bottom level while the
propositions live at `ℓ`: the lifted copy is what lets the two ends of the coming
equivalence share a universe.
<!--zh-->
先做解码方向，从布尔值到命题。`decodeB`{.Agda} 把 `true`{.Agda} 送到代数的 `⊤`、`false`{.Agda} 送到它的 `⊥`，均以限定投影写出 (`TruthAlg.⊤ hPropAlg`{.Agda})；由定义性透明，这里的 `⊥` 就是 `(⊥* , isProp⊥*)`{.Agda} 这个对本身。定义域取 `Lift {ℓ-zero} {ℓ} Bool`{.Agda} 而非裸 `Bool`{.Agda}，因为 `Bool`{.Agda} 住在最底层而命题住在 `ℓ` 层：正是这份提升的副本，让即将登场的等价两端住进同一个宇宙。
<!--/-->

```agda
private
  decodeB : ∀ {ℓ} → Lift {ℓ-zero} {ℓ} Bool → hProp ℓ
  decodeB (lift true)  = TruthAlg.⊤ hPropAlg
  decodeB (lift false) = TruthAlg.⊥ hPropAlg
```

<!--en-->
The encoding direction cannot be written outright: whether a proposition holds is
not something one can inspect. So `encodeB`{.Agda} asks to be **handed** a decision
`d` of `P`, and reads the answer off it: a proof gives `true`{.Agda}, a refutation
gives `false`{.Agda}. No excluded middle here; the decision is an input.
<!--zh-->
编码方向没法直接写出来：一个命题成不成立，不是能检视出来的东西。所以 `encodeB`{.Agda} 要求**递给**它一个 `P` 的判定 `d`，照着判定读出答案：有证明就是 `true`{.Agda}，有反驳就是 `false`{.Agda}。这里没有排中律；判定是输入。
<!--/-->

```agda
  encodeB : ∀ {ℓ} (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → Lift {ℓ-zero} {ℓ} Bool
  encodeB P (inl _) = lift true
  encodeB P (inr _) = lift false
```

<!--en-->
One round trip: decoding the encoding of `P` gives back `P` itself. The tool is
`⇔toPath`{.Agda}, the library's propositional extensionality: between propositions,
maps in both directions already make a path (in this book that principle is a
theorem, not an axiom). If the decision is a proof `p`, the goal is that the
algebra's `⊤` equals `P`, and both directions are trivial: from `⊤` to `P` the
answer `p` is already in hand, and back the other way everything maps to
`tt*`{.Agda}, the inhabitant of `⊤`. If the decision is a refutation `np`, the goal
is that the algebra's `⊥` equals `P`: out of `⊥*`{.Agda} nothing needs saying,
which is what the absurd pattern `λ ()` says, and any alleged proof `p` of `P` is
crushed by `np`, with `Empty.rec`{.Agda} eliminating the resulting absurdity.
<!--zh-->
第一趟往返：把 `P` 编码再解码，得回 `P` 自身。工具是 `⇔toPath`{.Agda}，即库的命题外延性：命题之间，两个方向的映射就足以给出一条路径 (在本书中，这条原理是定理而非公理)。若判定是证明 `p`，目标为代数的 `⊤` 等于 `P`，两个方向都平凡：从 `⊤` 到 `P`，答案 `p` 已在手上；反向则一切送到 `⊤` 的居民 `tt*`{.Agda}。若判定是反驳 `np`，目标为代数的 `⊥` 等于 `P`：从 `⊥*`{.Agda} 出发无话可说，荒谬模式 `λ ()` 说的正是这个；而任何声称的 `P` 之证明 `p` 都被 `np` 击碎，`Empty.rec`{.Agda} 消去随之而来的荒谬。
<!--/-->

```agda
  secB : ∀ {ℓ} (P : hProp ℓ) (d : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥))
       → decodeB (encodeB P d) ≡ P
  secB P (inl p)  = ⇔toPath (λ _ → p) (λ _ → tt*)
  secB P (inr np) = ⇔toPath (λ ()) (λ p → Empty.rec (np p))
```

<!--en-->
The other round trip: encoding the decoding of a Boolean `b` gives back `b`. One
subtlety deserves attention: at assembly time it is excluded middle that will decide
`decodeB b`{.Agda}, and nothing promises which decision it hands over. So `retrB`{.Agda}
proves the equation for **every** decision `d`, by four cases. `true`{.Agda} with a
proof: `refl`{.Agda}. `true`{.Agda} with an alleged refutation `n⊤`: impossible,
since `⊤` does hold, and `n⊤ tt*`{.Agda} is the absurdity. `false`{.Agda} with an alleged
proof: that proof is a term of `⊥*`{.Agda}, and the absurd pattern `()` closes the
case before any equation is owed. `false`{.Agda} with a refutation: `refl`{.Agda}.
<!--zh-->
另一趟往返：把布尔值 `b` 解码再编码，得回 `b`。有一处细微值得注意：总装时来判定 `decodeB b`{.Agda} 的将是排中律，而它递来哪个判定无从许诺。所以 `retrB`{.Agda} 对**每一个**判定 `d` 证明该等式，分四种情形。`true`{.Agda} 配证明：`refl`{.Agda}。`true`{.Agda} 配所谓反驳 `n⊤`：不可能，因为 `⊤` 明明成立，`n⊤ tt*`{.Agda} 即是荒谬。`false`{.Agda} 配所谓证明：该证明是 `⊥*`{.Agda} 的项，荒谬模式 `()` 在欠下任何等式之前就了结此案。`false`{.Agda} 配反驳：`refl`{.Agda}。
<!--/-->

```agda
  retrB : ∀ {ℓ} (b : Lift {ℓ-zero} {ℓ} Bool)
          (d : ⟨ decodeB b ⟩ ⊎ (⟨ decodeB b ⟩ → Empty.⊥))
        → encodeB (decodeB b) d ≡ b
  retrB (lift true)  (inl _)  = refl
  retrB (lift true)  (inr n⊤) = Empty.rec (n⊤ tt*)
  retrB (lift false) (inl ())
  retrB (lift false) (inr _)  = refl
```

<!--en-->
The assembly. `iso`{.Agda} packages the four pieces (decode; decide, then encode;
the two round trips), and `isoToEquiv`{.Agda} upgrades the isomorphism to an
equivalence. Count the occurrences of `lem`: three, and all three do the same job,
supplying the decisions the constructive helpers asked for as inputs. That is the
entire footprint of excluded middle in this dividend.
<!--zh-->
总装。`iso`{.Agda} 把四件套打包 (解码；先判定、再编码；两趟往返)，`isoToEquiv`{.Agda} 把同构升级为等价。数一数 `lem` 的出场：三次，且三次干的是同一件事，为构造性助手供应它们当作输入索要的判定。这就是排中律在这笔红利中的全部足迹。
<!--/-->

```agda
lem→smallΩ : ∀ {ℓ} → LEM ℓ → Lift {ℓ-zero} {ℓ} Bool ≃ hProp ℓ
lem→smallΩ lem = isoToEquiv (iso decodeB
  (λ P → encodeB P (lem P))
  (λ P → secB P (lem P))
  (λ b → retrB b (lem (decodeB b))))
```

<!--en-->
## The second dividend: propositional resizing
<!--zh-->
## 第二笔红利：命题降层
<!--/-->

<!--en-->
Second: a proposition living one universe up is equivalent to one living below.
Decide it: if it holds it is equivalent to `⊤`, if it fails it is equivalent to
`⊥`, and both are small. This is **propositional resizing**, and it is the precise
reason classical set theory never worries about which universe a proposition
inhabits.
<!--zh-->
第二笔：住在高一层宇宙的命题等价于住在低层的命题。判定它：若成立则等价于 `⊤`，若不成立则等价于 `⊥`，而两者都是小的。这就是**命题降层**，也正是经典集合论从不操心命题住在哪个宇宙的确切原因。
<!--/-->

<!--en-->
As before, the work is done from a handed-over decision, and `P .snd`{.Agda} (the
propositionality proof, as the Prelude promised) is used directly. If `P` holds,
the small stand-in is the algebra's `⊤` at level `ℓ`: between two propositions,
maps in both directions already form an **equivalence of underlying types**, which
is what `propBiimpl→Equiv`{.Agda} builds from the two propositionality proofs and
the two maps; from `P` to `⊤` everything goes to `tt*`{.Agda}, and back the other
way `p` is in hand. If `P` fails, the stand-in is the algebra's `⊥`, with the same
two absurdity moves as in `secB`{.Agda}. Note the shift against the first dividend: there the
output was a path between propositions (`⇔toPath`{.Agda}), here it is an
equivalence between their underlying types, so the same pair of maps is fed to
`propBiimpl→Equiv`{.Agda} instead.
<!--zh-->
与之前一样，工作从递来的判定做起，其中直接用到 `P .snd`{.Agda} (命题性证明，正如序章预告的那样)。若 `P` 成立，小替身取 `ℓ` 层的代数 `⊤`：命题之间，两个方向的映射就足以构成**底层类型的等价**，这正是 `propBiimpl→Equiv`{.Agda} 从两侧的命题性证明与两个映射装配出的东西；从 `P` 到 `⊤` 一切送到 `tt*`{.Agda}，反向则 `p` 已在手上。若 `P` 不成立，替身取代数的 `⊥`，两手荒谬招式与 `secB`{.Agda} 相同。留意与第一笔红利的差别：那里产出的是命题之间的路径 (`⇔toPath`{.Agda})，这里产出的是底层类型之间的等价，于是同样的一对映射改喂给 `propBiimpl→Equiv`{.Agda}。
<!--/-->

```agda
private
  resizeDec : ∀ {ℓ} (P : hProp (ℓ-suc ℓ)) → ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥)
            → Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
  resizeDec P (inl p)  = TruthAlg.⊤ hPropAlg ,
    propBiimpl→Equiv (P .snd) (TruthAlg.⊤ hPropAlg .snd) (λ _ → tt*) (λ _ → p)
  resizeDec P (inr np) = TruthAlg.⊥ hPropAlg ,
    propBiimpl→Equiv (P .snd) (TruthAlg.⊥ hPropAlg .snd)
      (λ p → Empty.rec (np p)) (λ ())
```

<!--en-->
The assembly is one line: decide `P` with excluded middle, hand the decision over.
The signature is the strength bookkeeping: this dividend consumes excluded middle
at the higher level `ℓ-suc ℓ`, once, and nothing more.
<!--zh-->
总装只有一行：用排中律判定 `P`，把判定递过去。签名就是强度记账：这笔红利在较高层级 `ℓ-suc ℓ` 上消费排中律，一次，仅此而已。
<!--/-->

```agda
lem→resize : ∀ {ℓ} → LEM (ℓ-suc ℓ) → (P : hProp (ℓ-suc ℓ)) → Σ[ Q ∈ hProp ℓ ] (⟨ P ⟩ ≃ ⟨ Q ⟩)
lem→resize lem P = resizeDec P (lem P)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Excluded middle is stated as the interface `LEM`{.Agda}, taken by chapters as a
parameter and never assumed globally; the boundary between constructive and
classical mathematics is therefore a compile-time fact. Two dividends are banked:
a small classifier of propositions (`lem→smallΩ`{.Agda}) and propositional resizing
(`lem→resize`{.Agda}). Part 3 will spend exactly these two coins: they redeem, for
the cumulative hierarchy `V`, the smallness assumptions behind full separation and
power set.
<!--zh-->
排中律以接口 `LEM`{.Agda} 的形式陈述，由章节作为参数领取，绝不全局假设；构造与经典数学的边界因此成为编译期事实。存入两笔红利：命题的小分类器 (`lem→smallΩ`{.Agda}) 与命题降层 (`lem→resize`{.Agda})。第三部将恰好花掉这两枚硬币：它们为累积层级 `V` 兑付全分离与幂集背后的小性假设。
<!--/-->
