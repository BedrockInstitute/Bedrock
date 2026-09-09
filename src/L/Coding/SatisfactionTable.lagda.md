<!--en-->
# Satisfaction tables over subformulas
<!--zh-->
# 子公式上的满足关系表
<!--ja-->
# 部分式上の充足関係表
<!--/-->

<!--en-->
For a formula `φ`, this chapter builds `satTable φ`, whose entries pair each subformula key with its recursively defined satisfaction value, and proves that a key determines the value recorded beside it.
<!--zh-->
给定公式 `φ`，本章构造 `satTable φ`；其中每个条目把一个子公式键与其递归定义的满足关系值配对，并证明键唯一确定旁边记录的值。
<!--ja-->
論理式 `φ` に対して、本章は `satTable φ` を構成します。その各項目は部分式の鍵と再帰的に定義された充足関係の値を対にし、さらに鍵が隣に記録された値を一意に定めることを示します。
<!--/-->

<!--en-->
The recursion's answer, assembled. For a formula of the meta-language, the finite
set of pairs of a key with the value at it, one pair for the formula and one for
each subformula, built exactly as the subformula closure was and for the same
reason: the meta level can name what it has already built.

Everything here is an element of the model by construction. The key is a pair of
a numeral with a code, and the code is taken in the model's own coding, so no
constructibility certificate is carried and none has to be proved. That is what
the coding chapter's second instantiation bought, and this is the chapter that
spends it.

What the recursion actually needs from the table is the other direction: any
value recorded against a key is *the* value at that key. That is where the code
equation has to be injective, and where a table that merely happened to record
two things at one key would not be a function at all.
<!--zh-->
递归的答案，装配起来。给定元语言的一条公式，这是「键与其处取值」之对构成的有穷集，公式自己一对、每条子公式各一对；造法与子公式闭包完全相同，理由也相同：元语言可以把自己已经造好的东西点名。

此处的一切按构造都是模型的元素。键是数码与码之对，而码取自模型自己的那套编码，故不携带可构造性证书，也不必去证。这是编码那一章的第二次实例化买下的东西，而本章正是花掉它的那一章。

递归真正向这张表索取的是另一个方向：任何被记录在某个键处的取值，就是那个键处的**那个**取值。正是在这里码等式必须单射，也正是在这里「碰巧在一个键处记了两样东西」的表根本不是一个函数。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.SatisfactionTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( module LCode; prʟ; prʟ-fst )
open import L.Coding.CodeConstructibility {ℓ}
  using ( tree; Of; tree-inv )
  renaming ( module Parts to TreeParts )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Prelude using ( J )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## Keys and entries
<!--zh-->
## 键与条目
<!--ja-->
## 鍵・項目・スロット
<!--/-->

<!--en-->
`keyʟ φ` pairs the arity of `φ` with its code, and `ent φ` pairs that key with `Sat B φ`. Applying the same subformula-tree construction to entries and keys yields `satTable φ` and its indexing `slot φ`.
<!--zh-->
`keyʟ φ` 把 `φ` 的元数与其编码配对，`ent φ` 再把该键与 `Sat B φ` 配对。对条目与键分别应用同一棵子公式树，便得到 `satTable φ` 及其索引槽位 `slot φ`。
<!--ja-->
`keyʟ φ` は `φ` のアリティとそのコードを対にし、`ent φ` はその鍵を `Sat B φ` と対にします。同じ部分式の木の構成を項目と鍵に適用して、`satTable φ` とその添字となる `slot φ` を得ます。
<!--/-->

<!--en-->
A key is the arity paired with the code, which is the shape every clause of the
internal recursion reads. An entry is a key paired with the value.

The shape both live in is the same, so it is written once and written
elsewhere. `tree`{.Agda} is the closure chapter's recursion: it gathers one
thing per subformula, and what that thing is is its parameter. With the entry it
gives the table, with the key it gives the **slot** the table is indexed by. The
recursion needs both and needs them to agree constructor for constructor, which
is why they come from one recursion rather than two.
<!--zh-->
一个键是元数与码的对，而那正是内部递归每条子句所读的形状。一个条目是键与取值的对。

两者所处的形状相同，故只写一次，且写在别处。`tree`{.Agda} 就是闭包那一章的那次递归：它为每条子公式收集一样东西，而那样东西是什么是它的参数。给它条目，得到那张表；给它键，得到表所索引的那个**槽**。递归两者都要，且要它们逐个构造子地一致，故两者出自同一次递归而非两次。
<!--/-->

```agda
keyʟ : ∀ {n} → Formula S n → S
keyʟ {n} φ = prʟ (numeralL n) LCode.⌜ φ ⌝

module _ (B : S) where
  ent : ∀ {n} → Formula S n → S
  ent φ = prʟ (keyʟ φ) (Sat B φ)

  satTable : ∀ {n} → Formula S n → S
  satTable = tree ent

  slot : ∀ {n} → Formula S n → S
  slot = tree keyʟ
```

<!--en-->
## Inverting tables and slots
<!--zh-->
## 反演满足关系表与槽位
<!--ja-->
## 充足関係表とスロットを反転する
<!--/-->

<!--en-->
The four inversion lemmas instantiate `tree-inv`: membership in a satisfaction table or slot identifies the subformula that contributed the member, while `slot-ent` and `ent-slot` move between an entry and its key.
<!--zh-->
四条反演引理都是 `tree-inv` 的实例：属于满足关系表或槽位会识别出贡献该成员的子公式，而 `slot-ent` 与 `ent-slot` 在条目及其键之间转换。
<!--ja-->
四つの反転補題は `tree-inv` の実例です。充足関係表またはスロットへの所属から、その要素を供給した部分式を特定し、`slot-ent` と `ent-slot` は項目とその鍵の間を移ります。
<!--/-->

<!--en-->
Every member is one of the things gathered. That is the inversion the closure
chapter proves, stated there against two collections at once, so the four
readings below are four instantiations of it and no induction runs here.
<!--zh-->
每个成员都是被收集之物之一。那正是闭包那一章所证的求逆，且它在那里是对着两个收集同时陈述的，故下面四条读式是它的四次实例化，此处不跑归纳。
<!--/-->

```agda
  module Parts (f : ∀ {m} → Formula S m → S) where
    open TreeParts f public

  satTable-inv : ∀ {n} (φ : Formula S n) (x : V ℓ)
               → ⟨ x ∈ fst (satTable φ) ⟩ → Of ent ent φ x
  satTable-inv = tree-inv ent ent

  slot-inv : ∀ {n} (φ : Formula S n) (x : V ℓ)
           → ⟨ x ∈ fst (slot φ) ⟩ → Of keyʟ keyʟ φ x
  slot-inv = tree-inv keyʟ keyʟ

  slot-ent : ∀ {n} (φ : Formula S n) (x : V ℓ)
           → ⟨ x ∈ fst (slot φ) ⟩ → Of keyʟ ent φ x
  slot-ent = tree-inv keyʟ ent

  ent-slot : ∀ {n} (φ : Formula S n) (x : V ℓ)
           → ⟨ x ∈ fst (satTable φ) ⟩ → Of ent keyʟ φ x
  ent-slot = tree-inv ent keyʟ
```

<!--en-->
## Uniqueness of the value at a key
<!--zh-->
## 键处取值的唯一性
<!--ja-->
## 鍵における値の一意性
<!--/-->

<!--en-->
If two table entries have the same arity-code key, injectivity of pairing and of formula coding identifies their formulas. The lemma `key-determines` therefore proves that both entries carry the same satisfaction value.
<!--zh-->
若两个满足关系表条目具有相同的「元数与公式编码」键，配对及公式编码的单射性便等同它们的公式。因此 `key-determines` 证明两个条目携带相同的满足关系值。
<!--ja-->
二つの充足関係表の項目が同じアリティ・論理式コードの鍵をもつなら、対と論理式の符号化の単射性により二つの論理式が同一になります。したがって `key-determines` は両項目が同じ充足関係の値をもつことを示します。
<!--/-->

<!--en-->
Two formulas with the same key have the same value, and that is where the code
equation's injectivity is used. The arities come out equal from the numeral
half of the key, and the code equation from the other half; the first is then
eliminated by path induction so that the second can be used at a single arity,
which is the only arity at which it is true.
<!--zh-->
两条键相同的公式取值相同，而码等式的单射性正是用在这里。诸元数由键的数码那一半得出相等，码等式由另一半得出；随后前者由道路归纳消掉，好让后者在单一元数处使用，而那也是它唯一为真的地方。
<!--/-->

```agda
  private
    same : ∀ {n} (ψ χ : Formula S n)
         → fst LCode.⌜ ψ ⌝ ≡ fst LCode.⌜ χ ⌝ → Sat B ψ ≡ Sat B χ
    same ψ χ e =
      cong (Sat B) (LCode.⌜⌝-inj ψ χ (Σ≡Prop (λ v → snd (isL v)) e))

    cross : ∀ {n m} (ψ : Formula S n) (χ : Formula S m) → n ≡ m
          → fst LCode.⌜ ψ ⌝ ≡ fst LCode.⌜ χ ⌝ → Sat B ψ ≡ Sat B χ
    cross {n} ψ χ p = J
      (λ m' p' → (χ' : Formula S m')
               → fst LCode.⌜ ψ ⌝ ≡ fst LCode.⌜ χ' ⌝ → Sat B ψ ≡ Sat B χ')
      (same ψ) p χ

  total : ∀ {n} (φ : Formula S n) (x : V ℓ) → ⟨ x ∈ fst (slot φ) ⟩
        → ∥ (Σ[ y ∈ S ] ⟨ pr x (fst y) ∈ fst (satTable φ) ⟩) ∥₁
  total φ x h = PT.map
    (λ { (m , χ , (q , incl)) → Sat B χ
       , subst (λ w → ⟨ pr w (fst (Sat B χ)) ∈ fst (satTable φ) ⟩) (sym q)
           (incl (pr (fst (keyʟ χ)) (fst (Sat B χ)))
             (subst (λ w → ⟨ w ∈ fst (tree ent χ) ⟩)
               (prʟ-fst (keyʟ χ) (Sat B χ)) (Parts.self ent χ))) })
    (slot-ent φ x h)

  inSlot : ∀ {n} (φ : Formula S n) (x y : V ℓ)
         → ⟨ pr x y ∈ fst (satTable φ) ⟩ → ⟨ x ∈ fst (slot φ) ⟩
  inSlot φ x y h = PT.rec (snd (x ∈ fst (slot φ)))
    (λ { (m , χ , (q , incl)) →
      subst (λ w → ⟨ w ∈ fst (slot φ) ⟩)
        (sym (pr-inj (q ∙ prʟ-fst (keyʟ χ) (Sat B χ)) .fst))
        (incl (fst (keyʟ χ)) (Parts.self keyʟ χ)) })
    (ent-slot φ (pr x y) h)

  key-determines : ∀ {n m} (ψ : Formula S n) (χ : Formula S m)
                 → fst (keyʟ ψ) ≡ fst (keyʟ χ) → Sat B ψ ≡ Sat B χ
  key-determines {n} {m} ψ χ e = cross ψ χ
    (#-inj′ (sym (numeralL-fst n) ∙ pr-inj q .fst ∙ numeralL-fst m))
    (pr-inj q .snd)
    where
    q : pr (fst (numeralL n)) (fst LCode.⌜ ψ ⌝)
      ≡ pr (fst (numeralL m)) (fst LCode.⌜ χ ⌝)
    q = sym (prʟ-fst (numeralL n) LCode.⌜ ψ ⌝)
      ∙ e ∙ prʟ-fst (numeralL m) LCode.⌜ χ ⌝

  entry-out : ∀ {n m} (φ : Formula S n) (ψ : Formula S m) (y : V ℓ)
            → ⟨ pr (fst (keyʟ ψ)) y ∈ fst (satTable φ) ⟩
            → y ≡ fst (Sat B ψ)
  entry-out φ ψ y h = PT.rec (setIsSet y (fst (Sat B ψ)))
    (λ { (m , χ , (q , _)) →
      let r = pr-inj (q ∙ prʟ-fst (keyʟ χ) (Sat B χ)) in
      r .snd ∙ cong fst (sym (key-determines ψ χ (r .fst))) })
    (satTable-inv φ (pr (fst (keyʟ ψ)) y) h)

  entry-in : ∀ {n} (φ : Formula S n)
           → ⟨ pr (fst (keyʟ φ)) (fst (Sat B φ)) ∈ fst (satTable φ) ⟩
  entry-in φ = subst (λ w → ⟨ w ∈ fst (satTable φ) ⟩)
    (prʟ-fst (keyʟ φ) (Sat B φ)) (Parts.self ent φ)
```

<!--en-->
## Subkeys determined by a constructor tag
<!--zh-->
## 构造子标签确定的子键
<!--ja-->
## 構成子タグが定める部分鍵
<!--/-->

<!--en-->
For a key whose formula code has a specified constructor tag, the final case analysis identifies the immediate subformula keys in its slot. Binary, unary, and quantifier constructors each return the arity-adjusted keys required by the recursion clauses.
<!--zh-->
对于公式编码带有指定构造子标签的键，最后的分类讨论识别其槽位中的直接子公式键。二元、一元与量词构造子分别给出递归子句所需的、元数经过相应调整的键。
<!--ja-->
論理式コードが指定された構成子タグをもつ鍵について、最後の場合分けはそのスロットにある直接の部分式の鍵を特定します。二項、単項、量化子の各構成子は、再帰条件が要求するようにアリティを調整した鍵を返します。
<!--/-->

<!--en-->
The dispatch a clause performs, and the last piece before the ten
verifications. A clause is stated at a tag and receives a key of that shape; the
formula the key names is recovered by the inversion above, and then its
constructor has to be matched against the tag. That match is the coding chapter's
own device, exported rather than rebuilt: the constructor is recoverable from the
tag, so the shape of a formula of a given tag is **computed** from the tag,
and the tag equation carries the formula's own case to it.

So one lemma serves all ten clauses, and it returns three things: what the
formula's constructor is, that the arity read is the formula's, and that the
payload read is the formula's.
<!--zh-->
子句所作的那次分派，是十次验证之前的最后一步。一条子句在某个标签处陈述，收到一个那种形状的键；由上面那次求逆恢复出该键所命名的公式，随后其构造子必须与那个标签一致。这一步使用编码一章已有的装置，只导出而不重造：构造子可从标签还原，故「带某个标签的公式是什么形状」可以从标签**算**出来，而那条标签等式处理的正是公式自身的情形。

一条引理同时用于全部十条子句，它给出三件信息：那条公式的构造子是什么、被读出的元数就是它的元数、被读出的载荷就是它的载荷。
<!--/-->

```agda

keyʟ-shape : ∀ {m} (ψ : Formula S m) (k : ℕ) (ar p : V ℓ)
           → fst (keyʟ ψ) ≡ pr ar (pr (# k) p)
           → LCode.Match k ψ
           × ((# m ≡ ar) × (fst (LCode.payOf ψ) ≡ p))
keyʟ-shape {m} ψ k ar p e =
    subst (λ j → LCode.Match j ψ) tag≡ (LCode.matches ψ)
  , ( sym (numeralL-fst m) ∙ pr-inj e' .fst
    , pr-inj inner .snd )
  where
  e' : pr (fst (numeralL m)) (fst LCode.⌜ ψ ⌝) ≡ pr ar (pr (# k) p)
  e' = sym (prʟ-fst (numeralL m) LCode.⌜ ψ ⌝) ∙ e

  inner : pr (fst (numeralL (LCode.tagOf ψ))) (fst (LCode.payOf ψ))
        ≡ pr (# k) p
  inner = sym (prʟ-fst (numeralL (LCode.tagOf ψ)) (LCode.payOf ψ))
        ∙ sym (cong fst (LCode.shape ψ))
        ∙ pr-inj e' .snd

  tag≡ : LCode.tagOf ψ ≡ k
  tag≡ = #-inj′ (sym (numeralL-fst (LCode.tagOf ψ)) ∙ pr-inj inner .fst)
```
