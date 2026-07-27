# The table, and what it records

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

module L.Coding.Table {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( module LCode; prʟ; prʟ-fst )
open import L.Coding.InL {ℓ}
  using ( sglʟ; cupʟ; sglʟ-in; sglʟ-out; cupʟ-inl; cupʟ-out )
open import L.Coding.Sat {ℓ} lem using ( Sat )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Foundations.Prelude using ( J )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
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
<!--/-->

<!--en-->
A key is the arity paired with the code, which is the shape every clause of the
internal recursion reads. An entry is a key paired with the value.

The shape both live in is the same, so it is written once. `tree`{.Agda} gathers
one thing per subformula, and what that thing is is its parameter: with the entry
it gives the table, with the key it gives the **slot** the table is indexed by.
The recursion needs both and needs them to agree constructor for constructor,
which is a reason to build them from one recursion rather than two.
<!--zh-->
一个键是元数与码之对，而那正是内部递归每条子句所读的形状。一个条目是键与取值之对。

两者所在的形状相同，故只写一次。`tree`{.Agda} 为每条子公式收集一样东西，而那样东西是什么是它的参数：给它条目，得到那张表；给它键，得到表所索引的那个**槽**。递归两者都要，且要它们逐个构造子地一致，而这正是「用一次递归而非两次造出它们」的理由。
<!--/-->

```agda
keyʟ : ∀ {n} → Formula S n → S
keyʟ {n} φ = prʟ (numeralL n) LCode.⌜ φ ⌝

module _ (B : S) where
  ent : ∀ {n} → Formula S n → S
  ent φ = prʟ (keyʟ φ) (Sat B φ)

  tree : (∀ {m} → Formula S m → S) → ∀ {n} → Formula S n → S
  tree f φ@(t ∈̇ u)  = sglʟ (f φ)
  tree f φ@(t ≐ u)  = sglʟ (f φ)
  tree f φ@⊤̇        = sglʟ (f φ)
  tree f φ@⊥̇        = sglʟ (f φ)
  tree f φ@(a ∧̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(a ∨̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(a ⇒̇ b)  = cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))
  tree f φ@(¬̇ a)    = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∃̇ a)    = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∀̇ a)    = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∀̇∈ t a) = cupʟ (sglʟ (f φ)) (tree f a)
  tree f φ@(∃̇∈ t a) = cupʟ (sglʟ (f φ)) (tree f a)

  satTable : ∀ {n} → Formula S n → S
  satTable = tree ent

  slot : ∀ {n} → Formula S n → S
  slot = tree keyʟ
```

<!--en-->
## Reading the table back
<!--zh-->
## 把表读回来
<!--/-->

<!--en-->
Every member is one of the things gathered, which is the inversion the closure
chapter needed in its own shape, and it is proved once for both. The two combinators take the inclusions rather than an equation
between the two constructions, which is the rule that chapter measured.
<!--zh-->
每个成员都是被收集的东西之一，而这正是闭包那一章以自己的形状所需的那次求逆，且为两者只证一次。两个组合子接受的是诸包含映射、而非两个构造之间的一条等式，那是那一章测量出来的规矩。
<!--/-->

```agda
  Of : (∀ {m} → Formula S m → S) → V ℓ → Type (ℓ-suc ℓ)
  Of f x = ∥ (Σ[ m ∈ ℕ ] Σ[ χ ∈ Formula S m ] (x ≡ fst (f χ))) ∥₁

  private
    module _ (f : ∀ {m} → Formula S m → S) where
      one : ∀ {n} (φ : Formula S n) (x : V ℓ) → ⟨ x ∈ fst (sglʟ (f φ)) ⟩ → Of f x
      one {n} φ x h = ∣ n , φ , sglʟ-out (f φ) x h ∣₁

      un : ∀ {n m} (φ : Formula S n) (a : Formula S m)
         → ((x : V ℓ) → ⟨ x ∈ fst (tree f a) ⟩ → Of f x)
         → (x : V ℓ) → ⟨ x ∈ fst (cupʟ (sglʟ (f φ)) (tree f a)) ⟩ → Of f x
      un φ a ra x h = PT.rec squash₁
        (λ { (inl e) → one φ x e ; (inr e) → ra x e })
        (cupʟ-out (sglʟ (f φ)) (tree f a) x h)

      bin : ∀ {n m} (φ : Formula S n) (a b : Formula S m)
          → ((x : V ℓ) → ⟨ x ∈ fst (tree f a) ⟩ → Of f x)
          → ((x : V ℓ) → ⟨ x ∈ fst (tree f b) ⟩ → Of f x)
          → (x : V ℓ)
          → ⟨ x ∈ fst (cupʟ (sglʟ (f φ)) (cupʟ (tree f a) (tree f b))) ⟩
          → Of f x
      bin φ a b ra rb x h = PT.rec squash₁
        (λ { (inl e) → one φ x e
           ; (inr e) → PT.rec squash₁
               (λ { (inl ea) → ra x ea ; (inr eb) → rb x eb })
               (cupʟ-out (tree f a) (tree f b) x e) })
        (cupʟ-out (sglʟ (f φ)) (cupʟ (tree f a) (tree f b)) x h)

  tree-inv : (f : ∀ {m} → Formula S m → S) → ∀ {n} (φ : Formula S n) (x : V ℓ)
           → ⟨ x ∈ fst (tree f φ) ⟩ → Of f x
  tree-inv f φ@(t ∈̇ u) = one f φ
  tree-inv f φ@(t ≐ u) = one f φ
  tree-inv f φ@⊤̇       = one f φ
  tree-inv f φ@⊥̇       = one f φ
  tree-inv f φ@(a ∧̇ b) = bin f φ a b (tree-inv f a) (tree-inv f b)
  tree-inv f φ@(a ∨̇ b) = bin f φ a b (tree-inv f a) (tree-inv f b)
  tree-inv f φ@(a ⇒̇ b) = bin f φ a b (tree-inv f a) (tree-inv f b)
  tree-inv f φ@(¬̇ a)    = un f φ a (tree-inv f a)
  tree-inv f φ@(∃̇ a)    = un f φ a (tree-inv f a)
  tree-inv f φ@(∀̇ a)    = un f φ a (tree-inv f a)
  tree-inv f φ@(∀̇∈ t a) = un f φ a (tree-inv f a)
  tree-inv f φ@(∃̇∈ t a) = un f φ a (tree-inv f a)

  satTable-inv : ∀ {n} (φ : Formula S n) (x : V ℓ)
               → ⟨ x ∈ fst (satTable φ) ⟩ → Of ent x
  satTable-inv = tree-inv ent

  slot-inv : ∀ {n} (φ : Formula S n) (x : V ℓ)
           → ⟨ x ∈ fst (slot φ) ⟩ → Of keyʟ x
  slot-inv = tree-inv keyʟ
```

<!--en-->
## A key determines its value
<!--zh-->
## 键决定它的取值
<!--/-->

<!--en-->
Two formulas with the same key have the same value, and that is where the code
equation's injectivity is spent. The arities come out equal from the numeral
half of the key, and the code equation from the other half; the first is then
eliminated by path induction so that the second can be used at a single arity,
which is the only arity at which it is true.
<!--zh-->
两条键相同的公式取值相同，而码等式的单射性正是花在这里。诸元数由键的数码那一半得出相等，码等式由另一半得出；随后前者由道路归纳消掉，好让后者在单一元数处使用，而那也是它唯一为真的地方。
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
    (λ { (m , χ , q) →
      let r = pr-inj (q ∙ prʟ-fst (keyʟ χ) (Sat B χ)) in
      r .snd ∙ cong fst (sym (key-determines ψ χ (r .fst))) })
    (satTable-inv φ (pr (fst (keyʟ ψ)) y) h)

  private
    top : ∀ {n} (φ : Formula S n)
        → ⟨ pr (fst (keyʟ φ)) (fst (Sat B φ)) ∈ fst (sglʟ (ent φ)) ⟩
    top φ = sglʟ-in (ent φ) _ (sym (prʟ-fst (keyʟ φ) (Sat B φ)))

  slot-in : ∀ {n} (φ : Formula S n) → ⟨ fst (keyʟ φ) ∈ fst (slot φ) ⟩
  slot-in φ@(t ∈̇ u)  = sglʟ-in (keyʟ φ) _ refl
  slot-in φ@(t ≐ u)  = sglʟ-in (keyʟ φ) _ refl
  slot-in φ@⊤̇        = sglʟ-in (keyʟ φ) _ refl
  slot-in φ@⊥̇        = sglʟ-in (keyʟ φ) _ refl
  slot-in φ@(a ∧̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)
  slot-in φ@(a ∨̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)
  slot-in φ@(a ⇒̇ b)  = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)
  slot-in φ@(¬̇ a)    = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)
  slot-in φ@(∃̇ a)    = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)
  slot-in φ@(∀̇ a)    = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)
  slot-in φ@(∀̇∈ t a) = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)
  slot-in φ@(∃̇∈ t a) = cupʟ-inl _ _ _ (sglʟ-in (keyʟ φ) _ refl)

  entry-in : ∀ {n} (φ : Formula S n)
           → ⟨ pr (fst (keyʟ φ)) (fst (Sat B φ)) ∈ fst (satTable φ) ⟩
  entry-in φ@(t ∈̇ u)  = top φ
  entry-in φ@(t ≐ u)  = top φ
  entry-in φ@⊤̇        = top φ
  entry-in φ@⊥̇        = top φ
  entry-in φ@(a ∧̇ b)  = cupʟ-inl _ _ _ (top φ)
  entry-in φ@(a ∨̇ b)  = cupʟ-inl _ _ _ (top φ)
  entry-in φ@(a ⇒̇ b)  = cupʟ-inl _ _ _ (top φ)
  entry-in φ@(¬̇ a)    = cupʟ-inl _ _ _ (top φ)
  entry-in φ@(∃̇ a)    = cupʟ-inl _ _ _ (top φ)
  entry-in φ@(∀̇ a)    = cupʟ-inl _ _ _ (top φ)
  entry-in φ@(∀̇∈ t a) = cupʟ-inl _ _ _ (top φ)
  entry-in φ@(∃̇∈ t a) = cupʟ-inl _ _ _ (top φ)
```

<!--en-->
## What a key of a given tag has under it
<!--zh-->
## 给定标签的键之下有什么
<!--/-->

<!--en-->
The dispatch a clause performs, and the last piece before the twelve
verifications. A clause is stated at a tag and receives a key of that shape; the
formula the key names is recovered by the inversion above, and then its
constructor has to be matched against the tag. That match is the coding chapter's
own device, exported rather than rebuilt: the constructor is recoverable from the
tag, so what a formula of a given tag looks like is **computed** from the tag,
and the tag equation carries the formula's own case to it.

So one lemma serves all twelve clauses, and it hands back three things: what the
formula's constructor is, that the arity read is the formula's, and that the
payload read is the formula's.
<!--zh-->
子句所作的那次分派，也是十二次验证之前的最后一块。一条子句在某个标签处陈述，收到一个那种形状的键；键所命名的公式由上面那次求逆恢复出来，随后它的构造子必须与那个标签对上。那次对上用的是编码那一章自己的装置，导出而非重造：构造子可从标签还原，故「带某个标签的公式长什么样」是从标签**算**出来的，而那条标签等式把公式自己的情形搬到它上面。

于是一条引理服务全部十二条子句，而它交回三件东西：那条公式的构造子是什么、被读出的元数就是它的元数、被读出的载荷就是它的载荷。
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
