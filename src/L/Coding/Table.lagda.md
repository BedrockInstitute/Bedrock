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
<!--zh-->
一个键是元数与码之对，而那正是内部递归每条子句所读的形状。一个条目是键与取值之对。
<!--/-->

```agda
keyʟ : ∀ {n} → Formula S n → S
keyʟ {n} φ = prʟ (numeralL n) LCode.⌜ φ ⌝

module _ (B : S) where
  ent : ∀ {n} → Formula S n → S
  ent φ = prʟ (keyʟ φ) (Sat B φ)

  satTable : ∀ {n} → Formula S n → S
  satTable φ@(t ∈̇ u)  = sglʟ (ent φ)
  satTable φ@(t ≐ u)  = sglʟ (ent φ)
  satTable φ@⊤̇        = sglʟ (ent φ)
  satTable φ@⊥̇        = sglʟ (ent φ)
  satTable φ@(a ∧̇ b)  = cupʟ (sglʟ (ent φ)) (cupʟ (satTable a) (satTable b))
  satTable φ@(a ∨̇ b)  = cupʟ (sglʟ (ent φ)) (cupʟ (satTable a) (satTable b))
  satTable φ@(a ⇒̇ b)  = cupʟ (sglʟ (ent φ)) (cupʟ (satTable a) (satTable b))
  satTable φ@(¬̇ a)    = cupʟ (sglʟ (ent φ)) (satTable a)
  satTable φ@(∃̇ a)    = cupʟ (sglʟ (ent φ)) (satTable a)
  satTable φ@(∀̇ a)    = cupʟ (sglʟ (ent φ)) (satTable a)
  satTable φ@(∀̇∈ t a) = cupʟ (sglʟ (ent φ)) (satTable a)
  satTable φ@(∃̇∈ t a) = cupʟ (sglʟ (ent φ)) (satTable a)
```

<!--en-->
## Reading the table back
<!--zh-->
## 把表读回来
<!--/-->

<!--en-->
Every member is an entry, which is the inversion the closure chapter needed in
its own shape. The two combinators take the inclusions rather than an equation
between the two constructions, which is the rule that chapter measured.
<!--zh-->
每个成员都是一个条目，而这正是闭包那一章以自己的形状所需的那次求逆。两个组合子接受的是诸包含映射、而非两个构造之间的一条等式，那是那一章测量出来的规矩。
<!--/-->

```agda
  Ent : V ℓ → Type (ℓ-suc ℓ)
  Ent x = ∥ (Σ[ m ∈ ℕ ] Σ[ χ ∈ Formula S m ] (x ≡ fst (ent χ))) ∥₁

  private
    one : ∀ {n} (φ : Formula S n) (x : V ℓ) → ⟨ x ∈ fst (sglʟ (ent φ)) ⟩ → Ent x
    one {n} φ x h = ∣ n , φ , sglʟ-out (ent φ) x h ∣₁

    un : ∀ {n m} (φ : Formula S n) (a : Formula S m)
       → ((x : V ℓ) → ⟨ x ∈ fst (satTable a) ⟩ → Ent x)
       → (x : V ℓ) → ⟨ x ∈ fst (cupʟ (sglʟ (ent φ)) (satTable a)) ⟩ → Ent x
    un φ a ra x h = PT.rec squash₁
      (λ { (inl e) → one φ x e ; (inr e) → ra x e })
      (cupʟ-out (sglʟ (ent φ)) (satTable a) x h)

    bin : ∀ {n m} (φ : Formula S n) (a b : Formula S m)
        → ((x : V ℓ) → ⟨ x ∈ fst (satTable a) ⟩ → Ent x)
        → ((x : V ℓ) → ⟨ x ∈ fst (satTable b) ⟩ → Ent x)
        → (x : V ℓ)
        → ⟨ x ∈ fst (cupʟ (sglʟ (ent φ)) (cupʟ (satTable a) (satTable b))) ⟩
        → Ent x
    bin φ a b ra rb x h = PT.rec squash₁
      (λ { (inl e) → one φ x e
         ; (inr e) → PT.rec squash₁
             (λ { (inl ea) → ra x ea ; (inr eb) → rb x eb })
             (cupʟ-out (satTable a) (satTable b) x e) })
      (cupʟ-out (sglʟ (ent φ)) (cupʟ (satTable a) (satTable b)) x h)

  satTable-inv : ∀ {n} (φ : Formula S n) (x : V ℓ)
               → ⟨ x ∈ fst (satTable φ) ⟩ → Ent x
  satTable-inv φ@(t ∈̇ u) = one φ
  satTable-inv φ@(t ≐ u) = one φ
  satTable-inv φ@⊤̇       = one φ
  satTable-inv φ@⊥̇       = one φ
  satTable-inv φ@(a ∧̇ b) = bin φ a b (satTable-inv a) (satTable-inv b)
  satTable-inv φ@(a ∨̇ b) = bin φ a b (satTable-inv a) (satTable-inv b)
  satTable-inv φ@(a ⇒̇ b) = bin φ a b (satTable-inv a) (satTable-inv b)
  satTable-inv φ@(¬̇ a)    = un φ a (satTable-inv a)
  satTable-inv φ@(∃̇ a)    = un φ a (satTable-inv a)
  satTable-inv φ@(∀̇ a)    = un φ a (satTable-inv a)
  satTable-inv φ@(∀̇∈ t a) = un φ a (satTable-inv a)
  satTable-inv φ@(∃̇∈ t a) = un φ a (satTable-inv a)
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
