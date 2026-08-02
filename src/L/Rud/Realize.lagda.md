# The realization induction

<!--en-->
This chapter prices the comprehension direction of the rud route's switch
theorem: every Δ₀-definable subset of a transitive set `u` is the value of a
finite composite of the abstract basis operations. Two telescopes carry the
abstraction (lesson P-h). The basis is a module telescope, so no concrete set
former ever unfolds; and the **satisfaction face** is a second telescope, so the
walk reads the object language only through the reads its twelve clauses spend,
and no concrete satisfaction can unfold inside the induction. The real face, the
tree's inner satisfaction and its definable subsets, is plugged in once at the
end, where memberships and equations flow but nothing normalizes.
<!--zh-->
本章为 rud 路线切换定理的领悟方向标价：传递集 `u` 的每个 Δ₀ 可定义子集，都是抽象基运算的某个有限复合之值。抽象由两个参数表承担 (法则 P-h)。基是一个模块参数表，因此没有任何具体造集算子展开；而**满足面孔**是第二个参数表，于是行走只经由十二条子句所花的那些读取来看对象语言，归纳内部也就没有任何具体满足关系能够展开。真正的面孔，即树的内层满足与其可定义子集，在最后一次性代入，其时成员关系与等式流动，但没有任何东西归一化。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Rud.Realize {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import Base.Classical using ( lowerLEM )
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import L.Definability {ℓ} using ( module DefOf )
open import Cubical.Foundations.Equiv using ( equivFun; invEquiv )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _++_; map )
import Cubical.Functions.Logic as Logic
open Logic using ( _⊓_; _⊔_; _⇒_; _⇔_; ¬_; ∃[]-syntax; ∀[]-syntax )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using ( Acc; acc; isPropAcc; WellFounded; wf→x≮x )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; elimProp; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; _∼_; _⊆_; ∈∈ₛ; extensionality; identityPrinciple; ∈-asFiber
        ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; isEmb⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
```

<!--en-->
## Explicit-level connectives
<!--zh-->
## 显式层级联结词
<!--/-->

<!--en-->
The library's hProp connectives carry an unsolved result level that fails in
type positions (lesson I-2); the signatures below pin the levels and use
`⟨_⟩` at hProp expressions.
<!--zh-->
库的 hProp 联结词带有无法在类型位置求解的结果层级 (法则 I-2)；下面这些签名把层级钉死，并在 hProp 表达式处使用 `⟨_⟩`。
<!--/-->

```agda
infixr 8 _⊓ₚ_ _⊔ₚ_ _⊓₂_
infixr 4 _⇔ₚ_ _⇒ₚ_

_⊓ₚ_ : hProp ℓ → hProp ℓ → hProp ℓ
A ⊓ₚ B = A ⊓ B

_⊓₂_ : hProp ℓ → hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ)
A ⊓₂ B = A ⊓ B

_⊔ₚ_ : {ℓ' : Level} → hProp ℓ' → hProp ℓ' → hProp ℓ'
A ⊔ₚ B = A ⊔ B

_⇒ₚ_ : hProp ℓ → hProp ℓ → hProp ℓ
A ⇒ₚ B = A ⇒ B

¬ₚ : hProp ℓ → hProp ℓ
¬ₚ A = ¬ A

_⇔ₚ_ : hProp ℓ → hProp ℓ → hProp ℓ
A ⇔ₚ B = A ⇔ B

_↔_ : Type ℓ → Type ℓ → Type ℓ
A ↔ B = (A → B) × (B → A)

∃ₚ : (V ℓ → hProp ℓ) → hProp (ℓ-suc ℓ)
∃ₚ P = ∃[]-syntax P

∃ₚ⁺ : (V ℓ → hProp (ℓ-suc ℓ)) → hProp (ℓ-suc ℓ)
∃ₚ⁺ P = ∃[]-syntax P
```

<!--en-->
## The abstract basis
<!--zh-->
## 抽象基
<!--/-->

<!--en-->
The basis is the probe's telescope, extended with the classical law as a
module parameter: the realization consumes difference, intersection, binary
union (pair plus union), collection, characteristic separation, equality
separation and images; product and the membership relation are carried so the
interface spans both candidate bases.
<!--zh-->
基是探针的参数表，另加经典律作为模块参数：领悟消费差、交、二元并 (配对加并)、收集、特征分离、等词分离与像；积与成员关系被携带，使接口覆盖两个候选基。
<!--/-->

```agda
module Basis
  (pairOp : V ℓ → V ℓ → V ℓ)
  (pairSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ pairOp a b ⟩ → ⟨ (y ≡ₕ a) ⊔ₚ (y ≡ₕ b) ⟩)
    × (⟨ (y ≡ₕ a) ⊔ₚ (y ≡ₕ b) ⟩ → ⟨ y ∈ₛ pairOp a b ⟩))
  (diffOp : V ℓ → V ℓ → V ℓ)
  (diffSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ diffOp a b ⟩ → ⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥))
    × ((⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥)) → ⟨ y ∈ₛ diffOp a b ⟩))
  (interOp : V ℓ → V ℓ → V ℓ)
  (interSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ interOp a b ⟩ → ⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩)
    × ((⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩) → ⟨ y ∈ₛ interOp a b ⟩))
  (prodOp : V ℓ → V ℓ → V ℓ)
  (prodSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ prodOp a b ⟩
       → ⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z))))) ⟩)
    × (⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z))))) ⟩
       → ⟨ y ∈ₛ prodOp a b ⟩))
  (memOp : V ℓ → V ℓ)
  (memSpec : (a y : V ℓ)
    → (⟨ y ∈ₛ memOp a ⟩
       → ⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂ ((x ∈ₛ z) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z)))))) ⟩)
    × (⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂ ((x ∈ₛ z) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z)))))) ⟩
       → ⟨ y ∈ₛ memOp a ⟩))
  (unionOp : V ℓ → V ℓ)
  (unionSpec : (a y : V ℓ)
    → (⟨ y ∈ₛ unionOp a ⟩ → ⟨ ∃ₚ (λ z → (z ∈ₛ a) ⊓ₚ (y ∈ₛ z)) ⟩)
    × (⟨ ∃ₚ (λ z → (z ∈ₛ a) ⊓ₚ (y ∈ₛ z)) ⟩ → ⟨ y ∈ₛ unionOp a ⟩))
  (colOp : V ℓ → V ℓ → V ℓ)
  (colSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ colOp a b ⟩ → ⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩)
    × ((⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩) → ⟨ y ∈ₛ colOp a b ⟩))
  (chSepOp : V ℓ → V ℓ → V ℓ → V ℓ)
  (chSepSpec : (a b c y : V ℓ)
    → (⟨ y ∈ₛ chSepOp a b c ⟩ → ⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩)
    × ((⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩) → ⟨ y ∈ₛ chSepOp a b c ⟩))
  (eqSepOp : V ℓ → V ℓ → V ℓ → V ℓ)
  (eqSepSpec : (a b c y : V ℓ)
    → (⟨ y ∈ₛ eqSepOp a b c ⟩ → ⟨ y ∈ₛ c ⟩ × ⟨ a ∼ b ⟩)
    × ((⟨ y ∈ₛ c ⟩ × ⟨ a ∼ b ⟩) → ⟨ y ∈ₛ eqSepOp a b c ⟩))
  where
```

<!--en-->
### Transitivity and regularity
<!--zh-->
### 传递与正则
<!--/-->

<!--en-->
Transitivity is stated in the small-membership form and carried for the
operations layer; the walk itself never spends it, because the inner
satisfaction already restricts its quantifiers to members of `u`. Regularity
refutes self-membership, which prices the diagonal atom `x ∈ x`.
<!--zh-->
传递以小成员形式陈述，为运算层携带；行走本身从不花它，因为内层满足已把量词限制在 `u` 的成员上。正则反驳自成员，为对角原子 `x ∈ x` 定价。
<!--/-->

```agda
  Trans : V ℓ → Type (ℓ-suc ℓ)
  Trans u = (x y : V ℓ) → ⟨ x ∈ₛ y ⟩ → ⟨ y ∈ₛ u ⟩ → ⟨ x ∈ₛ u ⟩

  ∈ₛ-wf : WellFounded (λ (x y : V ℓ) → ⟨ x ∈ y ⟩)
  ∈ₛ-wf = elimProp (λ s → isPropAcc s)
    (λ X ix rec → acc (λ y y∈ → PT.rec (isPropAcc y)
      (λ { (i , p) → subst (Acc (λ a b → ⟨ a ∈ b ⟩)) p (rec i) }) y∈))

  ∈ₛ-irrefl : (x : V ℓ) → ⟨ x ∈ₛ x ⟩ → Empty.⊥
  ∈ₛ-irrefl x h = wf→x≮x ∈ₛ-wf {x = x} (∈∈ₛ {a = x} {b = x} .snd h)
```

<!--en-->
### The composite syntax
<!--zh-->
### 复合语法
<!--/-->

<!--en-->
A composite of arity `k` has `k` free slots for the witness stack of `k` nested
bounded quantifiers, plus constants and the separated variable's container. The
image constructor takes a family one arity higher, and its evaluation needs the
ambient stack as well as the set being ranged over. The pure syntax lives here,
and the evaluation in an inner module whose parameter supplies the image
operation, so the interface stays abstract (lesson P-h).
<!--zh-->
元数为 `k` 的复合带有 `k` 个自由槽，装 `k` 层嵌套有界量词的见证栈，另加常量与被分离变量的容器。像构造子取一个高一元数的族，其求值除了被遍历的集合还需要环境栈。纯语法住在这里，求值住在以内层模块参数供应像运算的地方，接口由此保持抽象 (法则 P-h)。
<!--/-->

```agda
  data Comp : ℕ → Type (ℓ-suc ℓ) where
    conC   : {k : ℕ} → V ℓ → Comp k
    varC   : {k : ℕ} → Fin k → Comp k
    interC : {k : ℕ} → Comp k → Comp k → Comp k
    diffC  : {k : ℕ} → Comp k → Comp k → Comp k
    unionC : {k : ℕ} → Comp k → Comp k
    pairC  : {k : ℕ} → Comp k → Comp k → Comp k
    colC   : {k : ℕ} → Comp k → Comp k → Comp k
    chSepC : {k : ℕ} → Comp k → Comp k → Comp k → Comp k
    eqSepC : {k : ℕ} → Comp k → Comp k → Comp k → Comp k
    imgC   : {k : ℕ} → Comp (suc k) → Comp k → Comp k

  module Eval (imgOp : {k : ℕ} → Comp (suc k) → Vec (V ℓ) k → V ℓ → V ℓ) where

    opaque
      lemL : LEM ℓ
      lemL = lowerLEM lem

    eval : {k : ℕ} → Comp k → Vec (V ℓ) k → V ℓ
    eval (conC x) ws = x
    eval (varC i) ws = lookup i ws
    eval (interC a b) ws = interOp (eval a ws) (eval b ws)
    eval (diffC a b) ws = diffOp (eval a ws) (eval b ws)
    eval (unionC a) ws = unionOp (eval a ws)
    eval (pairC a b) ws = pairOp (eval a ws) (eval b ws)
    eval (colC a b) ws = colOp (eval a ws) (eval b ws)
    eval (chSepC a b c) ws = chSepOp (eval a ws) (eval b ws) (eval c ws)
    eval (eqSepC a b c) ws = eqSepOp (eval a ws) (eval b ws) (eval c ws)
    eval (imgC f a) ws = imgOp f ws (eval a ws)
```

<!--en-->
### Operation-level facts
<!--zh-->
### 运算层事实
<!--/-->

<!--en-->
Three facts about the abstract operations pay for the clause work: a binary
union is the union of a pair, a doubled pair is a singleton, and excluded middle
at the lower level discharges the two classical clauses (implication and the
bounded universal).
<!--zh-->
抽象运算的三条事实为子句工作买单：二元并是配对的并，重复的配对是单点集，而低层的排中律兑付两条经典子句 (蕴含与有界全称)。
<!--/-->

```agda
    dne : (P : hProp ℓ) → ((⟨ P ⟩ → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
    dne P nn = Sum.rec (λ p → p) (λ np → Empty.rec (nn np)) (lemL P)

    binUnion-mem : (a b x : V ℓ)
                 → ⟨ x ∈ₛ unionOp (pairOp a b) ⇔ₚ (x ∈ₛ a) ⊔ₚ (x ∈ₛ b) ⟩
    binUnion-mem a b x = fwd , bwd
      where
      fwd : ⟨ x ∈ₛ unionOp (pairOp a b) ⟩ → ⟨ (x ∈ₛ a) ⊔ₚ (x ∈ₛ b) ⟩
      fwd h = PT.rec (snd ((x ∈ₛ a) ⊔ₚ (x ∈ₛ b))) go
        (unionSpec (pairOp a b) x .fst h)
        where
        go : Σ[ z ∈ V ℓ ] (⟨ z ∈ₛ pairOp a b ⟩ × ⟨ x ∈ₛ z ⟩) → ⟨ (x ∈ₛ a) ⊔ₚ (x ∈ₛ b) ⟩
        go (z , z∈p , x∈z) = PT.rec (snd ((x ∈ₛ a) ⊔ₚ (x ∈ₛ b))) go₂
          (pairSpec a b z .fst z∈p)
          where
          go₂ : (⟨ z ≡ₕ a ⟩ ⊎ ⟨ z ≡ₕ b ⟩) → ⟨ (x ∈ₛ a) ⊔ₚ (x ∈ₛ b) ⟩
          go₂ (inl za) = ∣ inl (subst (λ w → ⟨ x ∈ₛ w ⟩) za x∈z) ∣₁
          go₂ (inr zb) = ∣ inr (subst (λ w → ⟨ x ∈ₛ w ⟩) zb x∈z) ∣₁
      bwd : ⟨ (x ∈ₛ a) ⊔ₚ (x ∈ₛ b) ⟩ → ⟨ x ∈ₛ unionOp (pairOp a b) ⟩
      bwd s = PT.rec (snd (x ∈ₛ unionOp (pairOp a b))) go s
        where
        go : (⟨ x ∈ₛ a ⟩ ⊎ ⟨ x ∈ₛ b ⟩) → ⟨ x ∈ₛ unionOp (pairOp a b) ⟩
        go (inl xa) = unionSpec (pairOp a b) x .snd
                        ∣ a , (pairSpec a b a .snd ∣ inl refl ∣₁ , xa) ∣₁
        go (inr xb) = unionSpec (pairOp a b) x .snd
                        ∣ b , (pairSpec a b b .snd ∣ inr refl ∣₁ , xb) ∣₁

    pair-singleton : (v x : V ℓ) → ⟨ x ∈ₛ pairOp v v ⇔ₚ x ∼ v ⟩
    pair-singleton v x = fwd , bwd
      where
      fwd : ⟨ x ∈ₛ pairOp v v ⟩ → ⟨ x ∼ v ⟩
      fwd h = PT.rec (snd (x ∼ v)) (λ
        { (inl p) → equivFun (invEquiv identityPrinciple) p
        ; (inr p) → equivFun (invEquiv identityPrinciple) p })
        (pairSpec v v x .fst h)
      bwd : ⟨ x ∼ v ⟩ → ⟨ x ∈ₛ pairOp v v ⟩
      bwd s = pairSpec v v x .snd ∣ inl (equivFun identityPrinciple s) ∣₁
```

<!--en-->
## The walk, relative to one transitive set
<!--zh-->
## 相对一个传递集的行走
<!--/-->

<!--en-->
Everything below is relative to one `u` and one image specification. The walk's
statement is member-indexed: a member of `u` arrives as an inhabitant of the
restricted carrier `SM`, which carries its own membership certificate, so the
"and it lies in `u`" conjunct of the paper statement never has to be written
down. Two small bridges keep every path operation at neutral endpoints (the
sister playbook's case-14 discipline): a membership transports along an equality
of elements or of containers, never in place.
<!--zh-->
以下一切相对于一个 `u` 与一份像规格。行走的陈述以成员为索引：`u` 的成员以受限载体 `SM` 的居民身份到场，自带成员证书，于是论文陈述里「且它属于 `u`」这一合取项根本不必写出。两座小桥把每次路径操作保持在中立端点上 (姊妹剧本的第十四例纪律)：成员关系沿元素或容器的等式搬运，绝不原地搬。
<!--/-->

```agda
    module Realize (u : V ℓ) (tu : Trans u)
                   (imgSpec : {k : ℕ} (f : Comp (suc k)) (vs : Vec (V ℓ) k) (p z : V ℓ)
                     → (⟨ z ∈ₛ imgOp f vs p ⟩ → ⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ eval f (y ∷ vs))) ⟩)
                     × (⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ eval f (y ∷ vs))) ⟩ → ⟨ z ∈ₛ imgOp f vs p ⟩))
      where

      module U = DefOf u
      open U using ( SM; ι; ⟦_⟧ᵐ; ⊨ᵐ-small )

      memU : (x : SM) → ⟨ fst x ∈ₛ u ⟩
      memU x = ∈∈ₛ {a = fst x} {b = u} .fst (snd x)

      mkSM : (y : V ℓ) → ⟨ y ∈ₛ u ⟩ → SM
      mkSM y h = y , ∈∈ₛ {a = y} {b = u} .snd h

      ⇔-trans : {A B C : Type ℓ} → A ↔ B → B ↔ C → A ↔ C
      ⇔-trans (f , g) (f' , g') = (λ a → f' (f a)) , (λ c → g (g' c))

      ⇔-sym : {A B : Type ℓ} → A ↔ B → B ↔ A
      ⇔-sym (f , g) = g , f

      ⇔-∈ₛ : {a a' b b' : V ℓ} → a ≡ a' → b ≡ b' → (⟨ a ∈ₛ b ⟩ ↔ ⟨ a' ∈ₛ b' ⟩)
      ⇔-∈ₛ {a} {a'} {b} {b'} p q =
          (λ h → subst (λ v → ⟨ v ∈ₛ b' ⟩) p (subst (λ v → ⟨ a ∈ₛ v ⟩) q h))
        , (λ h → subst (λ v → ⟨ v ∈ₛ b ⟩) (sym p) (subst (λ v → ⟨ a' ∈ₛ v ⟩) (sym q) h))

      ∈ₛ-elt : {a a' : V ℓ} (b : V ℓ) → a ≡ a' → ⟨ a ∈ₛ b ⟩ → ⟨ a' ∈ₛ b ⟩
      ∈ₛ-elt b p = ⇔-∈ₛ p (refl {x = b}) .fst

      ∈ₛ-set : (a : V ℓ) {b b' : V ℓ} → b ≡ b' → ⟨ a ∈ₛ b ⟩ → ⟨ a ∈ₛ b' ⟩
      ∈ₛ-set a p = ⇔-∈ₛ (refl {x = a}) p .fst

      ⇔-∼ : {a a' b b' : V ℓ} → a ≡ a' → b ≡ b' → (⟨ a ∼ b ⟩ ↔ ⟨ a' ∼ b' ⟩)
      ⇔-∼ {a} {a'} {b} {b'} p q =
          (λ h → subst (λ v → ⟨ a' ∼ v ⟩) q (subst (λ v → ⟨ v ∼ b ⟩) p h))
        , (λ h → subst (λ v → ⟨ a ∼ v ⟩) (sym q) (subst (λ v → ⟨ v ∼ b' ⟩) (sym p) h))

      ∼-refl : (a : V ℓ) → ⟨ a ∼ a ⟩
      ∼-refl a = equivFun (invEquiv (identityPrinciple {a = a} {b = a})) refl

      ∼-flip : (a b : V ℓ) → (⟨ a ∼ b ⟩ ↔ ⟨ b ∼ a ⟩)
      ∼-flip a b = to a b , to b a
        where
        to : (c d : V ℓ) → ⟨ c ∼ d ⟩ → ⟨ d ∼ c ⟩
        to c d s = equivFun (invEquiv (identityPrinciple {a = d} {b = c}))
                     (sym (equivFun (identityPrinciple {a = c} {b = d}) s))

      ∃ᵤ : (⟪ u ⟫ → hProp ℓ) → hProp ℓ
      ∃ᵤ P = ∃[]-syntax P

      ∀ᵤ : (⟪ u ⟫ → hProp ℓ) → hProp ℓ
      ∀ᵤ P = ∀[]-syntax P
```

<!--en-->
### Separation from `u`, and the two certificates
<!--zh-->
### 从 `u` 中的分离与两份证书
<!--/-->

<!--en-->
Every composite the walk builds separates a subset out of `u`, so each clause
owes two things: that its value stays inside `u`, and that a member of `u`
belongs to it exactly when the formula holds there. `uSepD` turns any
operation specification of separation shape into the member-indexed
characterization, discharging the `∈ u` conjunct once and for all.
<!--zh-->
行走造出的每个复合都从 `u` 中分离出一个子集，故每条子句欠两样东西：其值不出 `u`，以及 `u` 的成员属于它当且仅当公式在该处成立。`uSepD` 把任何分离形状的运算规格转成以成员为索引的刻画，一劳永逸地兑清 `∈ u` 合取项。
<!--/-->

```agda
      Sub : {k : ℕ} → Comp k → Type (ℓ-suc ℓ)
      Sub {k} c = (vs : Vec (V ℓ) k) (y : V ℓ) → ⟨ y ∈ₛ eval c vs ⟩ → ⟨ y ∈ₛ u ⟩

      ChrP : {k : ℕ} → Comp k → (Vec SM k → SM → hProp ℓ) → Type (ℓ-suc ℓ)
      ChrP {k} c P = (ws : Vec SM k) (x : SM)
                   → ⟨ fst x ∈ₛ eval c (map fst ws) ⇔ₚ P ws x ⟩

      uSepD : (s : V ℓ) (P : V ℓ → hProp ℓ)
            → ((y : V ℓ) → ⟨ y ∈ₛ s ⇔ₚ ((y ∈ₛ u) ⊓ₚ P y) ⟩)
            → (x : SM) → ⟨ fst x ∈ₛ s ⇔ₚ P (fst x) ⟩
      uSepD s P h x = (λ e → h (fst x) .fst e .snd)
                    , (λ p → h (fst x) .snd (memU x , p))
```

<!--en-->
### Term views
<!--zh-->
### 词项视图
<!--/-->

<!--en-->
A term of the walk's language is one of three things: a value that does not
depend on the separated variable (a constant or a parameter), a witness slot, or
the separated variable itself. The three-way view is a small inductive type at a
cheap codomain, which is what the sister playbook prescribes for a coverage grid
(lesson P-i [C′]); the first two cases share a composite, so the atom and
quantifier grids are two-by-two, not three-by-three.
<!--zh-->
行走语言的词项只有三种：不依赖被分离变量的值 (常量或参数)、见证槽，或被分离变量自身。这个三分视图是廉价陪域上的小归纳类型，这正是姊妹剧本对覆盖网格所开的方子 (法则 P-i [C′])；前两种共用一个复合，于是原子与量词网格是二乘二而非三乘三。
<!--/-->

```agda
      data TmF (k : ℕ) : Type (ℓ-suc ℓ) where
        fcon : V ℓ → TmF k
        fvar : Fin k → TmF k

      data TmC (k : ℕ) : Type (ℓ-suc ℓ) where
        free : TmF k → TmC k
        sep  : TmC k

      fcomp : {k : ℕ} → TmF k → Comp k
      fcomp (fcon v) = conC v
      fcomp (fvar j) = varC j

      tval : {k : ℕ} → TmC k → Vec SM k → SM → V ℓ
      tval (free a) ws x = eval (fcomp a) (map fst ws)
      tval sep ws x = fst x

      wk : {k : ℕ} → TmC k → TmC (suc k)
      wk (free (fcon v)) = free (fcon v)
      wk (free (fvar j)) = free (fvar (suc j))
      wk sep = sep

      wk-tval : {k : ℕ} (a : TmC k) (w : SM) (ws : Vec SM k) (x : SM)
              → tval (wk a) (w ∷ ws) x ≡ tval a ws x
      wk-tval (free (fcon v)) w ws x = refl
      wk-tval (free (fvar j)) w ws x = refl
      wk-tval sep w ws x = refl
```

<!--en-->
### The atom clauses
<!--zh-->
### 原子子句
<!--/-->

<!--en-->
Four shapes each for membership and equality, by which side the separated
variable falls on. Membership uses characteristic separation when neither side
is the variable, collection when the container is, plain intersection when the
element is, and the empty set on the diagonal, where regularity refutes the
atom. Equality uses equality separation, and the singleton `{v}` intersected
with `u` when one side is the variable.
<!--zh-->
成员与等词各四种形状，按被分离变量落在哪一侧划分。成员在两侧都不是该变量时用特征分离，容器是该变量时用收集，元素是该变量时用交，对角线上用空集，正则在那里反驳该原子。等词用等词分离，一侧是该变量时用单点集 `{v}` 与 `u` 的交。
<!--/-->

```agda
      memComp : {k : ℕ} → TmC k → TmC k → Comp k
      memComp (free a) (free b) = chSepC (fcomp a) (fcomp b) (conC u)
      memComp (free a) sep      = colC (fcomp a) (conC u)
      memComp sep      (free b) = interC (conC u) (fcomp b)
      memComp sep      sep      = diffC (conC u) (conC u)

      memSub : {k : ℕ} (a b : TmC k) → Sub (memComp a b)
      memSub (free a) (free b) vs y h =
        chSepSpec (eval (fcomp a) vs) (eval (fcomp b) vs) u y .fst h .fst
      memSub (free a) sep vs y h = colSpec (eval (fcomp a) vs) u y .fst h .fst
      memSub sep (free b) vs y h = interSpec u (eval (fcomp b) vs) y .fst h .fst
      memSub sep sep vs y h = diffSpec u u y .fst h .fst

      memChar : {k : ℕ} (a b : TmC k) (ws : Vec SM k) (x : SM)
              → ⟨ fst x ∈ₛ eval (memComp a b) (map fst ws)
                  ⇔ₚ (tval a ws x ∈ₛ tval b ws x) ⟩
      memChar (free a) (free b) ws x =
        uSepD (chSepOp (eval (fcomp a) (map fst ws)) (eval (fcomp b) (map fst ws)) u)
              (λ y → eval (fcomp a) (map fst ws) ∈ₛ eval (fcomp b) (map fst ws))
              (chSepSpec (eval (fcomp a) (map fst ws)) (eval (fcomp b) (map fst ws)) u) x
      memChar (free a) sep ws x =
        uSepD (colOp (eval (fcomp a) (map fst ws)) u)
              (λ y → eval (fcomp a) (map fst ws) ∈ₛ y)
              (colSpec (eval (fcomp a) (map fst ws)) u) x
      memChar sep (free b) ws x =
        uSepD (interOp u (eval (fcomp b) (map fst ws)))
              (λ y → y ∈ₛ eval (fcomp b) (map fst ws))
              (interSpec u (eval (fcomp b) (map fst ws))) x
      memChar sep sep ws x = fwd , bwd
        where
        fwd : ⟨ fst x ∈ₛ diffOp u u ⟩ → ⟨ fst x ∈ₛ fst x ⟩
        fwd h = Empty.rec (diffSpec u u (fst x) .fst h .snd
                            (diffSpec u u (fst x) .fst h .fst))
        bwd : ⟨ fst x ∈ₛ fst x ⟩ → ⟨ fst x ∈ₛ diffOp u u ⟩
        bwd h = Empty.rec (∈ₛ-irrefl (fst x) h)

      eqComp : {k : ℕ} → TmC k → TmC k → Comp k
      eqComp (free a) (free b) = eqSepC (fcomp a) (fcomp b) (conC u)
      eqComp (free a) sep      = interC (conC u) (pairC (fcomp a) (fcomp a))
      eqComp sep      (free b) = interC (conC u) (pairC (fcomp b) (fcomp b))
      eqComp sep      sep      = conC u

      eqSub : {k : ℕ} (a b : TmC k) → Sub (eqComp a b)
      eqSub (free a) (free b) vs y h =
        eqSepSpec (eval (fcomp a) vs) (eval (fcomp b) vs) u y .fst h .fst
      eqSub (free a) sep vs y h =
        interSpec u (pairOp (eval (fcomp a) vs) (eval (fcomp a) vs)) y .fst h .fst
      eqSub sep (free b) vs y h =
        interSpec u (pairOp (eval (fcomp b) vs) (eval (fcomp b) vs)) y .fst h .fst
      eqSub sep sep vs y h = h

      eqChar : {k : ℕ} (a b : TmC k) (ws : Vec SM k) (x : SM)
             → ⟨ fst x ∈ₛ eval (eqComp a b) (map fst ws)
                 ⇔ₚ (tval a ws x ∼ tval b ws x) ⟩
      eqChar (free a) (free b) ws x =
        uSepD (eqSepOp (eval (fcomp a) (map fst ws)) (eval (fcomp b) (map fst ws)) u)
              (λ y → eval (fcomp a) (map fst ws) ∼ eval (fcomp b) (map fst ws))
              (eqSepSpec (eval (fcomp a) (map fst ws)) (eval (fcomp b) (map fst ws)) u) x
      eqChar (free a) sep ws x =
        ⇔-trans (⇔-trans (uSepD (interOp u (pairOp (eval (fcomp a) (map fst ws))
                                                   (eval (fcomp a) (map fst ws))))
                                (λ y → y ∈ₛ pairOp (eval (fcomp a) (map fst ws))
                                                   (eval (fcomp a) (map fst ws)))
                                (interSpec u (pairOp (eval (fcomp a) (map fst ws))
                                                     (eval (fcomp a) (map fst ws)))) x)
                         (pair-singleton (eval (fcomp a) (map fst ws)) (fst x)))
                (∼-flip (fst x) (eval (fcomp a) (map fst ws)))
      eqChar sep (free b) ws x =
        ⇔-trans (uSepD (interOp u (pairOp (eval (fcomp b) (map fst ws))
                                          (eval (fcomp b) (map fst ws))))
                       (λ y → y ∈ₛ pairOp (eval (fcomp b) (map fst ws))
                                          (eval (fcomp b) (map fst ws)))
                       (interSpec u (pairOp (eval (fcomp b) (map fst ws))
                                            (eval (fcomp b) (map fst ws)))) x)
                (pair-singleton (eval (fcomp b) (map fst ws)) (fst x))
      eqChar sep sep ws x = (λ h → ∼-refl (fst x)) , (λ h → memU x)
```

<!--en-->
### The connective clauses
<!--zh-->
### 联结词子句
<!--/-->

<!--en-->
Each connective is a helper whose satisfaction argument is an abstract
predicate family, so the object language never enters these proofs: conjunction
is intersection, disjunction the union of a pair, negation the difference from
`u`, and implication the complement of `a ∖ b`, whose forward direction is the
first classical spend.
<!--zh-->
每个联结词是一个 helper，其满足参数是抽象谓词族，故对象语言从不进入这些证明：合取是交，析取是配对的并，否定是与 `u` 的差，蕴含是 `a ∖ b` 的补，其正向是第一笔经典支出。
<!--/-->

```agda
      andC : {k : ℕ} (a b : Comp k) (P Q : Vec SM k → SM → hProp ℓ)
           → Sub a → ChrP a P → ChrP b Q
           → Sub (interC a b) × ChrP (interC a b) (λ ws x → P ws x ⊓ₚ Q ws x)
      andC a b P Q sa ca cb = sub , chr
        where
        sub : Sub (interC a b)
        sub vs y h = sa vs y (interSpec (eval a vs) (eval b vs) y .fst h .fst)
        chr : ChrP (interC a b) (λ ws x → P ws x ⊓ₚ Q ws x)
        chr ws x = fwd , bwd
          where
          fwd : ⟨ fst x ∈ₛ interOp (eval a (map fst ws)) (eval b (map fst ws)) ⟩
              → ⟨ P ws x ⊓ₚ Q ws x ⟩
          fwd h = ca ws x .fst (m .fst) , cb ws x .fst (m .snd)
            where
            m = interSpec (eval a (map fst ws)) (eval b (map fst ws)) (fst x) .fst h
          bwd : ⟨ P ws x ⊓ₚ Q ws x ⟩
              → ⟨ fst x ∈ₛ interOp (eval a (map fst ws)) (eval b (map fst ws)) ⟩
          bwd (p , q) = interSpec (eval a (map fst ws)) (eval b (map fst ws)) (fst x) .snd
                          (ca ws x .snd p , cb ws x .snd q)

      orC : {k : ℕ} (a b : Comp k) (P Q : Vec SM k → SM → hProp ℓ)
          → Sub a → Sub b → ChrP a P → ChrP b Q
          → Sub (unionC (pairC a b)) × ChrP (unionC (pairC a b)) (λ ws x → P ws x ⊔ₚ Q ws x)
      orC a b P Q sa sb ca cb = sub , chr
        where
        sub : Sub (unionC (pairC a b))
        sub vs y h = PT.rec (snd (y ∈ₛ u)) go (binUnion-mem (eval a vs) (eval b vs) y .fst h)
          where
          go : (⟨ y ∈ₛ eval a vs ⟩ ⊎ ⟨ y ∈ₛ eval b vs ⟩) → ⟨ y ∈ₛ u ⟩
          go (inl h') = sa vs y h'
          go (inr h') = sb vs y h'
        chr : ChrP (unionC (pairC a b)) (λ ws x → P ws x ⊔ₚ Q ws x)
        chr ws x = fwd , bwd
          where
          fwd : ⟨ fst x ∈ₛ unionOp (pairOp (eval a (map fst ws)) (eval b (map fst ws))) ⟩
              → ⟨ P ws x ⊔ₚ Q ws x ⟩
          fwd h = PT.rec (snd (P ws x ⊔ₚ Q ws x)) go
            (binUnion-mem (eval a (map fst ws)) (eval b (map fst ws)) (fst x) .fst h)
            where
            go : (⟨ fst x ∈ₛ eval a (map fst ws) ⟩ ⊎ ⟨ fst x ∈ₛ eval b (map fst ws) ⟩)
               → ⟨ P ws x ⊔ₚ Q ws x ⟩
            go (inl h') = ∣ inl (ca ws x .fst h') ∣₁
            go (inr h') = ∣ inr (cb ws x .fst h') ∣₁
          bwd : ⟨ P ws x ⊔ₚ Q ws x ⟩
              → ⟨ fst x ∈ₛ unionOp (pairOp (eval a (map fst ws)) (eval b (map fst ws))) ⟩
          bwd s = PT.rec (snd (fst x ∈ₛ unionOp (pairOp (eval a (map fst ws))
                                                        (eval b (map fst ws))))) go s
            where
            go : (⟨ P ws x ⟩ ⊎ ⟨ Q ws x ⟩)
               → ⟨ fst x ∈ₛ unionOp (pairOp (eval a (map fst ws)) (eval b (map fst ws))) ⟩
            go (inl p) = binUnion-mem (eval a (map fst ws)) (eval b (map fst ws)) (fst x) .snd
                           ∣ inl (ca ws x .snd p) ∣₁
            go (inr q) = binUnion-mem (eval a (map fst ws)) (eval b (map fst ws)) (fst x) .snd
                           ∣ inr (cb ws x .snd q) ∣₁

      notC : {k : ℕ} (a : Comp k) (P : Vec SM k → SM → hProp ℓ) → ChrP a P
           → Sub (diffC (conC u) a) × ChrP (diffC (conC u) a) (λ ws x → ¬ₚ (P ws x))
      notC a P ca = sub , chr
        where
        sub : Sub (diffC (conC u) a)
        sub vs y h = diffSpec u (eval a vs) y .fst h .fst
        chr : ChrP (diffC (conC u) a) (λ ws x → ¬ₚ (P ws x))
        chr ws x = fwd , bwd
          where
          fwd : ⟨ fst x ∈ₛ diffOp u (eval a (map fst ws)) ⟩ → ⟨ ¬ₚ (P ws x) ⟩
          fwd h p = diffSpec u (eval a (map fst ws)) (fst x) .fst h .snd (ca ws x .snd p)
          bwd : ⟨ ¬ₚ (P ws x) ⟩ → ⟨ fst x ∈ₛ diffOp u (eval a (map fst ws)) ⟩
          bwd np = diffSpec u (eval a (map fst ws)) (fst x) .snd
                     (memU x , λ h → np (ca ws x .fst h))

      impC : {k : ℕ} (a b : Comp k) (P Q : Vec SM k → SM → hProp ℓ)
           → ChrP a P → ChrP b Q
           → Sub (diffC (conC u) (diffC a b))
           × ChrP (diffC (conC u) (diffC a b)) (λ ws x → P ws x ⇒ₚ Q ws x)
      impC a b P Q ca cb = sub , chr
        where
        sub : Sub (diffC (conC u) (diffC a b))
        sub vs y h = diffSpec u (diffOp (eval a vs) (eval b vs)) y .fst h .fst
        chr : ChrP (diffC (conC u) (diffC a b)) (λ ws x → P ws x ⇒ₚ Q ws x)
        chr ws x = fwd , bwd
          where
          A = eval a (map fst ws)
          B = eval b (map fst ws)
          fwd : ⟨ fst x ∈ₛ diffOp u (diffOp A B) ⟩ → ⟨ P ws x ⇒ₚ Q ws x ⟩
          fwd h p = dne (Q ws x) (λ nq →
            diffSpec u (diffOp A B) (fst x) .fst h .snd
              (diffSpec A B (fst x) .snd
                (ca ws x .snd p , λ hB → nq (cb ws x .fst hB))))
          bwd : ⟨ P ws x ⇒ₚ Q ws x ⟩ → ⟨ fst x ∈ₛ diffOp u (diffOp A B) ⟩
          bwd f = diffSpec u (diffOp A B) (fst x) .snd (memU x , step)
            where
            step : ⟨ fst x ∈ₛ diffOp A B ⟩ → Empty.⊥
            step hd = diffSpec A B (fst x) .fst hd .snd
                        (cb ws x .snd (f (ca ws x .fst (diffSpec A B (fst x) .fst hd .fst))))
```

<!--en-->
### The bounded-quantifier machinery
<!--zh-->
### 有界量词机件
<!--/-->

<!--en-->
The bounded existential is the union of an image, and the image ranges over `u`
itself rather than over the bound: the inner satisfaction already quantifies
over members of `u`, so the witness is drawn from `u` and the bound is applied
as a test inside the family. That choice is what makes the clause free of any
"the bound lies in `u`" obligation, and with it of the term-membership transport
the first pass walled on. `boundComp` is that test, one composite per term view.
<!--zh-->
有界存在是像的并，而像遍历 `u` 自身而非那个界：内层满足本就在 `u` 的成员上量化，故见证取自 `u`，界则作为族内的一次检验施加。正是这个取法使该子句不欠任何「界属于 `u`」的义务，连带地也不欠第一轮撞墙的那个词项成员搬运。`boundComp` 就是这次检验，每个词项视图一个复合。
<!--/-->

```agda
      boundComp : {k : ℕ} → TmC (suc k) → Comp (suc k)
      boundComp (free a) = chSepC (varC zero) (fcomp a) (conC u)
      boundComp sep      = colC (varC zero) (conC u)

      boundSub : {k : ℕ} (a : TmC (suc k)) → Sub (boundComp a)
      boundSub (free a) vs y h =
        chSepSpec (lookup zero vs) (eval (fcomp a) vs) u y .fst h .fst
      boundSub sep vs y h = colSpec (lookup zero vs) u y .fst h .fst

      boundChar : {k : ℕ} (a : TmC (suc k)) (ws : Vec SM k) (w x : SM)
                → ⟨ fst x ∈ₛ eval (boundComp a) (map fst (w ∷ ws))
                    ⇔ₚ (fst w ∈ₛ tval a (w ∷ ws) x) ⟩
      boundChar (free a) ws w x =
        uSepD (chSepOp (fst w) (eval (fcomp a) (fst w ∷ map fst ws)) u)
              (λ y → fst w ∈ₛ eval (fcomp a) (fst w ∷ map fst ws))
              (chSepSpec (fst w) (eval (fcomp a) (fst w ∷ map fst ws)) u) x
      boundChar sep ws w x =
        uSepD (colOp (fst w) u) (λ y → fst w ∈ₛ y) (colSpec (fst w) u) x
```

<!--en-->
## The satisfaction face
<!--zh-->
## 满足面孔
<!--/-->

<!--en-->
Here is the second abstraction layer. The satisfaction relation, the term
valuation, the member injection, the parameter environment and the
definable-subset former all enter as module parameters, together with exactly
the reads the clauses spend: one per formula constructor, the environment
congruence, and the two-direction membership specification of the former. Every
obligation of the walk below therefore sits at a stuck head; nothing about the
object language's semantics can unfold while the induction runs.
<!--zh-->
第二层抽象在此。满足关系、词项赋值、成员内射、参数环境与可定义子集算子全部作为模块参数进入，随之进入的恰是诸子句所花的读取：每个公式构造子一条，环境同余一条，算子的双向成员规格一条。因此下面行走的每个义务都坐在卡住的头上；归纳运行期间，对象语言语义的任何部分都无法展开。
<!--/-->

```agda
      module Face
        (Sat : {m : ℕ} → Formula ⟪ u ⟫ m → Vec SM m → hProp ℓ)
        (TmV : {m : ℕ} → Term ⟪ u ⟫ m → Vec SM m → V ℓ)
        (mem : ⟪ u ⟫ → SM)
        (envρ : {m : ℕ} → (Fin m → ⟪ u ⟫) → Vec SM m)
        (mem-fst : (i : ⟪ u ⟫) → fst (mem i) ≡ ⟪ u ⟫↪ i)
        (envρ-fst : {m : ℕ} (ρ : Fin m → ⟪ u ⟫) (j : Fin m)
                  → fst (lookup j (envρ ρ)) ≡ ⟪ u ⟫↪ (ρ j))
        (tm-con : {m : ℕ} (c : ⟪ u ⟫) (γ : Vec SM m) → TmV (con c) γ ≡ ⟪ u ⟫↪ c)
        (tm-var : {m : ℕ} (i : Fin m) (γ : Vec SM m) → TmV (var i) γ ≡ fst (lookup i γ))
        (sat-∈ : {m : ℕ} (t s : Term ⟪ u ⟫ m) (γ : Vec SM m)
               → ⟨ Sat (t ∈̇ s) γ ⇔ₚ (TmV t γ ∈ₛ TmV s γ) ⟩)
        (sat-≐ : {m : ℕ} (t s : Term ⟪ u ⟫ m) (γ : Vec SM m)
               → ⟨ Sat (t ≐ s) γ ⇔ₚ (TmV t γ ∼ TmV s γ) ⟩)
        (sat-∧ : {m : ℕ} (φ ψ : Formula ⟪ u ⟫ m) (γ : Vec SM m)
               → ⟨ Sat (φ ∧̇ ψ) γ ⇔ₚ (Sat φ γ ⊓ₚ Sat ψ γ) ⟩)
        (sat-∨ : {m : ℕ} (φ ψ : Formula ⟪ u ⟫ m) (γ : Vec SM m)
               → ⟨ Sat (φ ∨̇ ψ) γ ⇔ₚ (Sat φ γ ⊔ₚ Sat ψ γ) ⟩)
        (sat-⇒ : {m : ℕ} (φ ψ : Formula ⟪ u ⟫ m) (γ : Vec SM m)
               → ⟨ Sat (φ ⇒̇ ψ) γ ⇔ₚ (Sat φ γ ⇒ₚ Sat ψ γ) ⟩)
        (sat-¬ : {m : ℕ} (φ : Formula ⟪ u ⟫ m) (γ : Vec SM m)
               → ⟨ Sat (¬̇ φ) γ ⇔ₚ ¬ₚ (Sat φ γ) ⟩)
        (sat-⊤ : {m : ℕ} (γ : Vec SM m) → ⟨ Sat ⊤̇ γ ⟩)
        (sat-⊥ : {m : ℕ} (γ : Vec SM m) → ⟨ Sat {m} ⊥̇ γ ⟩ → Empty.⊥)
        (sat-∃∈ : {m : ℕ} (t : Term ⟪ u ⟫ m) (φ : Formula ⟪ u ⟫ (suc m)) (γ : Vec SM m)
                → ⟨ Sat (∃̇∈ t φ) γ
                    ⇔ₚ ∃ᵤ (λ i → (fst (mem i) ∈ₛ TmV t γ) ⊓ₚ Sat φ (mem i ∷ γ)) ⟩)
        (sat-∀∈ : {m : ℕ} (t : Term ⟪ u ⟫ m) (φ : Formula ⟪ u ⟫ (suc m)) (γ : Vec SM m)
                → ⟨ Sat (∀̇∈ t φ) γ
                    ⇔ₚ ∀ᵤ (λ i → (fst (mem i) ∈ₛ TmV t γ) ⇒ₚ Sat φ (mem i ∷ γ)) ⟩)
        (sat-resp : {m : ℕ} (φ : Formula ⟪ u ⟫ m) {γ γ' : Vec SM m}
                  → ((i : Fin m) → fst (lookup i γ) ≡ fst (lookup i γ'))
                  → ⟨ Sat φ γ ⟩ → ⟨ Sat φ γ' ⟩)
        (DSet : {k m : ℕ} → Formula ⟪ u ⟫ (k + suc m) → (Fin m → ⟪ u ⟫) → Vec SM k → V ℓ)
        (dset-mem : {k m : ℕ} (φ : Formula ⟪ u ⟫ (k + suc m)) (ρ : Fin m → ⟪ u ⟫)
                    (ws : Vec SM k) (i : ⟪ u ⟫)
                  → ⟨ ⟪ u ⟫↪ i ∈ₛ DSet φ ρ ws ⇔ₚ Sat φ (ws ++ mem i ∷ envρ ρ) ⟩)
        (dset-sub : {k m : ℕ} (φ : Formula ⟪ u ⟫ (k + suc m)) (ρ : Fin m → ⟪ u ⟫)
                    (ws : Vec SM k) (y : V ℓ)
                  → ⟨ y ∈ₛ DSet φ ρ ws ⟩ → ⟨ y ∈ₛ u ⟩)
        where
```

<!--en-->
The two quantifier clauses are the only ones that touch the member injection, so
they live here, above the induction. The bounded existential's family is
`{x ∈ u | w ∈ bound ∧ φ(x, w)}` with `w` the fresh slot; its image over `u`,
unioned, is the clause's value. The bounded universal is the complement of the
same construction on the negated body, and its forward direction is the second
classical spend.
<!--zh-->
两条量词子句是仅有的触碰成员内射者，故它们住在这里，在归纳之上。有界存在的族是 `{x ∈ u | w ∈ 界 ∧ φ(x, w)}`，其中 `w` 是新槽；其在 `u` 上的像取并即该子句之值。有界全称是同一构造在否定体上的补，其正向是第二笔经典支出。
<!--/-->

```agda
        bexFam : {k : ℕ} → TmC k → Comp (suc k) → Comp (suc k)
        bexFam a e = interC (boundComp (wk a)) e

        bexComp : {k : ℕ} → TmC k → Comp (suc k) → Comp k
        bexComp a e = unionC (imgC (bexFam a e) (conC u))

        bexSub : {k : ℕ} (a : TmC k) (e : Comp (suc k)) → Sub (bexComp a e)
        bexSub a e vs y h = PT.rec (snd (y ∈ₛ u)) step
          (unionSpec (imgOp (bexFam a e) vs u) y .fst h)
          where
          step : Σ[ W ∈ V ℓ ] (⟨ W ∈ₛ imgOp (bexFam a e) vs u ⟩ × ⟨ y ∈ₛ W ⟩) → ⟨ y ∈ₛ u ⟩
          step (W , W∈ , y∈W) = PT.rec (snd (y ∈ₛ u)) step₂
            (imgSpec (bexFam a e) vs u W .fst W∈)
            where
            step₂ : Σ[ z ∈ V ℓ ] (⟨ z ∈ₛ u ⟩ × (W ≡ eval (bexFam a e) (z ∷ vs))) → ⟨ y ∈ₛ u ⟩
            step₂ (z , z∈u , q) = boundSub (wk a) (z ∷ vs) y
              (interSpec (eval (boundComp (wk a)) (z ∷ vs)) (eval e (z ∷ vs)) y .fst
                (∈ₛ-set y q y∈W) .fst)

        bexChar : {k : ℕ} (a : TmC k) (e : Comp (suc k))
                  (B : Vec SM k → SM → V ℓ) (P : Vec SM (suc k) → SM → hProp ℓ)
                → ((ws : Vec SM k) (x : SM) → tval a ws x ≡ B ws x)
                → ((w w' : SM) (ws : Vec SM k) (x : SM) → fst w ≡ fst w'
                   → ⟨ P (w ∷ ws) x ⟩ → ⟨ P (w' ∷ ws) x ⟩)
                → ChrP e P
                → ChrP (bexComp a e) (λ ws x → ∃ᵤ (λ i → (fst (mem i) ∈ₛ B ws x)
                                                          ⊓ₚ P (mem i ∷ ws) x))
        bexChar {k} a e B P bB rP ce ws x = fwd , bwd
          where
          G : hProp ℓ
          G = ∃ᵤ (λ i → (fst (mem i) ∈ₛ B ws x) ⊓ₚ P (mem i ∷ ws) x)
          E : V ℓ
          E = imgOp (bexFam a e) (map fst ws) u
          fwd : ⟨ fst x ∈ₛ unionOp E ⟩ → ⟨ G ⟩
          fwd h = PT.rec (snd G) step (unionSpec E (fst x) .fst h)
            where
            step : Σ[ W ∈ V ℓ ] (⟨ W ∈ₛ E ⟩ × ⟨ fst x ∈ₛ W ⟩) → ⟨ G ⟩
            step (W , W∈ , x∈W) = PT.rec (snd G) step₂
              (imgSpec (bexFam a e) (map fst ws) u W .fst W∈)
              where
              step₂ : Σ[ z ∈ V ℓ ] (⟨ z ∈ₛ u ⟩ × (W ≡ eval (bexFam a e) (z ∷ map fst ws)))
                    → ⟨ G ⟩
              step₂ (z , z∈u , q) = ∣ i , (i∈B , iP) ∣₁
                where
                w : SM
                w = mkSM z z∈u
                parts = interSpec (eval (boundComp (wk a)) (fst w ∷ map fst ws))
                                  (eval e (fst w ∷ map fst ws)) (fst x) .fst
                                  (∈ₛ-set (fst x) q x∈W)
                w∈B : ⟨ fst w ∈ₛ B ws x ⟩
                w∈B = ∈ₛ-set (fst w) (wk-tval a w ws x ∙ bB ws x)
                        (boundChar (wk a) ws w x .fst (parts .fst))
                fib = ∈-asFiber {a = fst w} {b = u} (snd w)
                i : ⟪ u ⟫
                i = fib .fst
                back : fst w ≡ fst (mem i)
                back = sym (mem-fst i ∙ fib .snd)
                i∈B : ⟨ fst (mem i) ∈ₛ B ws x ⟩
                i∈B = ∈ₛ-elt (B ws x) back w∈B
                iP : ⟨ P (mem i ∷ ws) x ⟩
                iP = rP w (mem i) ws x back (ce (w ∷ ws) x .fst (parts .snd))
          bwd : ⟨ G ⟩ → ⟨ fst x ∈ₛ unionOp E ⟩
          bwd s = PT.rec (snd (fst x ∈ₛ unionOp E)) step s
            where
            step : Σ[ i ∈ ⟪ u ⟫ ] (⟨ fst (mem i) ∈ₛ B ws x ⟩ × ⟨ P (mem i ∷ ws) x ⟩)
                 → ⟨ fst x ∈ₛ unionOp E ⟩
            step (i , i∈B , iP) = unionSpec E (fst x) .snd ∣ Wᵢ , (W∈ , x∈W) ∣₁
              where
              w : SM
              w = mem i
              Wᵢ : V ℓ
              Wᵢ = eval (bexFam a e) (fst w ∷ map fst ws)
              W∈ : ⟨ Wᵢ ∈ₛ E ⟩
              W∈ = imgSpec (bexFam a e) (map fst ws) u Wᵢ .snd
                     ∣ fst w , (memU w , refl) ∣₁
              x∈W : ⟨ fst x ∈ₛ Wᵢ ⟩
              x∈W = interSpec (eval (boundComp (wk a)) (fst w ∷ map fst ws))
                              (eval e (fst w ∷ map fst ws)) (fst x) .snd
                      ( boundChar (wk a) ws w x .snd
                          (∈ₛ-set (fst w) (sym (wk-tval a w ws x ∙ bB ws x)) i∈B)
                      , ce (w ∷ ws) x .snd iP )

        ballComp : {k : ℕ} → TmC k → Comp (suc k) → Comp k
        ballComp a e = diffC (conC u) (bexComp a (diffC (conC u) e))

        ballSub : {k : ℕ} (a : TmC k) (e : Comp (suc k)) → Sub (ballComp a e)
        ballSub a e vs y h =
          diffSpec u (eval (bexComp a (diffC (conC u) e)) vs) y .fst h .fst

        ballChar : {k : ℕ} (a : TmC k) (e : Comp (suc k))
                   (B : Vec SM k → SM → V ℓ) (P : Vec SM (suc k) → SM → hProp ℓ)
                 → ((ws : Vec SM k) (x : SM) → tval a ws x ≡ B ws x)
                 → ((w w' : SM) (ws : Vec SM k) (x : SM) → fst w ≡ fst w'
                    → ⟨ P (w ∷ ws) x ⟩ → ⟨ P (w' ∷ ws) x ⟩)
                 → ChrP e P
                 → ChrP (ballComp a e) (λ ws x → ∀ᵤ (λ i → (fst (mem i) ∈ₛ B ws x)
                                                            ⇒ₚ P (mem i ∷ ws) x))
        ballChar {k} a e B P bB rP ce ws x = fwd , bwd
          where
          nP : Vec SM (suc k) → SM → hProp ℓ
          nP ws' x' = ¬ₚ (P ws' x')
          rnP : (w w' : SM) (ws' : Vec SM k) (x' : SM) → fst w ≡ fst w'
              → ⟨ nP (w ∷ ws') x' ⟩ → ⟨ nP (w' ∷ ws') x' ⟩
          rnP w w' ws' x' p n q = n (rP w' w ws' x' (sym p) q)
          nc : ChrP (diffC (conC u) e) nP
          nc = notC e P ce .snd
          bc : ChrP (bexComp a (diffC (conC u) e))
                    (λ ws' x' → ∃ᵤ (λ i → (fst (mem i) ∈ₛ B ws' x') ⊓ₚ nP (mem i ∷ ws') x'))
          bc = bexChar a (diffC (conC u) e) B nP bB rnP nc
          Eb : V ℓ
          Eb = eval (bexComp a (diffC (conC u) e)) (map fst ws)
          fwd : ⟨ fst x ∈ₛ diffOp u Eb ⟩
              → ⟨ ∀ᵤ (λ i → (fst (mem i) ∈ₛ B ws x) ⇒ₚ P (mem i ∷ ws) x) ⟩
          fwd h i i∈B = dne (P (mem i ∷ ws) x) (λ np →
            diffSpec u Eb (fst x) .fst h .snd (bc ws x .snd ∣ i , (i∈B , np) ∣₁))
          bwd : ⟨ ∀ᵤ (λ i → (fst (mem i) ∈ₛ B ws x) ⇒ₚ P (mem i ∷ ws) x) ⟩
              → ⟨ fst x ∈ₛ diffOp u Eb ⟩
          bwd f = diffSpec u Eb (fst x) .snd (memU x , step)
            where
            step : ⟨ fst x ∈ₛ Eb ⟩ → Empty.⊥
            step hE = PT.rec Empty.isProp⊥ go (bc ws x .fst hE)
              where
              go : Σ[ i ∈ ⟪ u ⟫ ] (⟨ fst (mem i) ∈ₛ B ws x ⟩ × ⟨ nP (mem i ∷ ws) x ⟩)
                 → Empty.⊥
              go (i , i∈B , np) = np (f i i∈B)
```

<!--en-->
## The induction
<!--zh-->
## 归纳
<!--/-->

<!--en-->
The parameters are fixed by a module, per lesson P-h, and the tree's de Bruijn
syntax makes variable permutation definitional: at depth `k` the formula reads
variable `k` as the separated `x`, variables below as the witness stack, and
variables above as parameters. `split` dispatches the index, `termC` turns each
term into its view, `tval-ok` is the one bridge between the object language's
term valuation and the view's value, and `consEq` is the pointwise equality of
environments the quantifier clauses hand to the face's congruence when a witness
drawn from `u` is repacked as the member the satisfaction quantifies over.
<!--zh-->
参数由一个模块钉住 (法则 P-h)，而树的 de Bruijn 语法把变量置换做成定义性的：深度 `k` 处公式把变量 `k` 读作被分离的 `x`，其下诸变量是见证栈，其上诸变量是参数。`split` 分派序号，`termC` 把每个词项变成它的视图，`tval-ok` 是对象语言的词项赋值与视图之值之间唯一的桥，而 `consEq` 是量词子句交给面孔同余的那条环境逐点等式，用在取自 `u` 的见证被重新打包成满足关系所量化的那个成员之时。
<!--/-->

```agda
        sucMap : {k m : ℕ} → Fin k ⊎ Fin (suc m) → Fin (suc k) ⊎ Fin (suc m)
        sucMap (inl j) = inl (suc j)
        sucMap (inr j) = inr j

        split : (k : ℕ) {m : ℕ} → Fin (k + suc m) → Fin k ⊎ Fin (suc m)
        split zero i = inr i
        split (suc k) zero = inl zero
        split (suc k) (suc i) = sucMap (split k i)

        consEq : {m : ℕ} (w w' : SM) (γ : Vec SM m) → fst w ≡ fst w'
               → (i : Fin (suc m)) → fst (lookup i (w ∷ γ)) ≡ fst (lookup i (w' ∷ γ))
        consEq w w' γ p zero = p
        consEq w w' γ p (suc i) = refl

        module Walk {n : ℕ} (ρ : Fin n → ⟪ u ⟫) where

          satAt : (k : ℕ) → Formula ⟪ u ⟫ (k + suc n) → Vec SM k → SM → hProp ℓ
          satAt k φ ws x = Sat φ (ws ++ x ∷ envρ ρ)

          tsplit : {k : ℕ} → Fin k ⊎ Fin (suc n) → TmC k
          tsplit (inl j) = free (fvar j)
          tsplit (inr zero) = sep
          tsplit (inr (suc j)) = free (fcon (⟪ u ⟫↪ (ρ j)))

          termC : (k : ℕ) → Term ⟪ u ⟫ (k + suc n) → TmC k
          termC k (con c) = free (fcon (⟪ u ⟫↪ c))
          termC k (var i) = tsplit (split k i)

          tsplit-suc : {k : ℕ} (s : Fin k ⊎ Fin (suc n)) (w : SM) (ws : Vec SM k) (x : SM)
                     → tval (tsplit (sucMap s)) (w ∷ ws) x ≡ tval (tsplit s) ws x
          tsplit-suc (inl j) w ws x = refl
          tsplit-suc (inr zero) w ws x = refl
          tsplit-suc (inr (suc j)) w ws x = refl

          lookup-split : (k : ℕ) (ws : Vec SM k) (x : SM) (i : Fin (k + suc n))
                       → fst (lookup i (ws ++ x ∷ envρ ρ)) ≡ tval (tsplit (split k i)) ws x
          lookup-split zero [] x zero = refl
          lookup-split zero [] x (suc j) = envρ-fst ρ j
          lookup-split (suc k) (w ∷ ws) x zero = refl
          lookup-split (suc k) (w ∷ ws) x (suc i) =
            lookup-split k ws x i ∙ sym (tsplit-suc (split k i) w ws x)

          tval-ok : (k : ℕ) (t : Term ⟪ u ⟫ (k + suc n)) (ws : Vec SM k) (x : SM)
                  → TmV t (ws ++ x ∷ envρ ρ) ≡ tval (termC k t) ws x
          tval-ok k (con c) ws x = tm-con c (ws ++ x ∷ envρ ρ)
          tval-ok k (var i) ws x = tm-var i (ws ++ x ∷ envρ ρ) ∙ lookup-split k ws x i
```

<!--en-->
The induction itself. Each clause names its composite, its subset certificate
and its characterization; the characterization is composed from the clause
helper above and the face read for that constructor, so the object language
appears in exactly one step per clause. The unbounded quantifiers have no Δ₀
witness, which is what the absent constructors of `Δ₀` say.
<!--zh-->
归纳本身。每条子句给出它的复合、子集证书与刻画；刻画由上面的子句 helper 与该构造子的面孔读取复合而成，故对象语言在每条子句里恰出现一步。无界量词没有 Δ₀ 见证，这正是 `Δ₀` 缺席的构造子所说的话。
<!--/-->

```agda
          walk : (k : ℕ) (φ : Formula ⟪ u ⟫ (k + suc n)) → Δ₀ φ
               → Σ[ c ∈ Comp k ] (Sub c × ChrP c (satAt k φ))
          walk k (t ∈̇ s) δ-∈ =
            memComp (termC k t) (termC k s) , memSub (termC k t) (termC k s)
            , λ ws x → ⇔-trans (memChar (termC k t) (termC k s) ws x)
                (⇔-trans (⇔-∈ₛ (sym (tval-ok k t ws x)) (sym (tval-ok k s ws x)))
                         (⇔-sym (sat-∈ t s (ws ++ x ∷ envρ ρ))))
          walk k (t ≐ s) δ-≐ =
            eqComp (termC k t) (termC k s) , eqSub (termC k t) (termC k s)
            , λ ws x → ⇔-trans (eqChar (termC k t) (termC k s) ws x)
                (⇔-trans (⇔-∼ (sym (tval-ok k t ws x)) (sym (tval-ok k s ws x)))
                         (⇔-sym (sat-≐ t s (ws ++ x ∷ envρ ρ))))
          walk k (φ ∧̇ ψ) (δ-∧ d₁ d₂) =
            interC (fst r₁) (fst r₂) , a .fst
            , λ ws x → ⇔-trans (a .snd ws x) (⇔-sym (sat-∧ φ ψ (ws ++ x ∷ envρ ρ)))
            where
            r₁ = walk k φ d₁
            r₂ = walk k ψ d₂
            a = andC (fst r₁) (fst r₂) (satAt k φ) (satAt k ψ)
                  (snd r₁ .fst) (snd r₁ .snd) (snd r₂ .snd)
          walk k (φ ∨̇ ψ) (δ-∨ d₁ d₂) =
            unionC (pairC (fst r₁) (fst r₂)) , o .fst
            , λ ws x → ⇔-trans (o .snd ws x) (⇔-sym (sat-∨ φ ψ (ws ++ x ∷ envρ ρ)))
            where
            r₁ = walk k φ d₁
            r₂ = walk k ψ d₂
            o = orC (fst r₁) (fst r₂) (satAt k φ) (satAt k ψ)
                  (snd r₁ .fst) (snd r₂ .fst) (snd r₁ .snd) (snd r₂ .snd)
          walk k (φ ⇒̇ ψ) (δ-⇒ d₁ d₂) =
            diffC (conC u) (diffC (fst r₁) (fst r₂)) , m .fst
            , λ ws x → ⇔-trans (m .snd ws x) (⇔-sym (sat-⇒ φ ψ (ws ++ x ∷ envρ ρ)))
            where
            r₁ = walk k φ d₁
            r₂ = walk k ψ d₂
            m = impC (fst r₁) (fst r₂) (satAt k φ) (satAt k ψ) (snd r₁ .snd) (snd r₂ .snd)
          walk k (¬̇ φ) (δ-¬ d) =
            diffC (conC u) (fst r) , nt .fst
            , λ ws x → ⇔-trans (nt .snd ws x) (⇔-sym (sat-¬ φ (ws ++ x ∷ envρ ρ)))
            where
            r = walk k φ d
            nt = notC (fst r) (satAt k φ) (snd r .snd)
          walk k ⊤̇ δ-⊤ =
            conC u , (λ vs y h → h)
            , λ ws x → (λ h → sat-⊤ (ws ++ x ∷ envρ ρ)) , (λ h → memU x)
          walk k ⊥̇ δ-⊥ =
            diffC (conC u) (conC u) , (λ vs y h → diffSpec u u y .fst h .fst)
            , λ ws x → (λ h → Empty.rec (diffSpec u u (fst x) .fst h .snd
                                          (diffSpec u u (fst x) .fst h .fst)))
                     , (λ h → Empty.rec (sat-⊥ (ws ++ x ∷ envρ ρ) h))
          walk k (∀̇∈ t φ) (δ-∀∈ d) =
            ballComp (termC k t) (fst r) , ballSub (termC k t) (fst r)
            , λ ws x → ⇔-trans
                (ballChar (termC k t) (fst r)
                  (λ ws' x' → TmV t (ws' ++ x' ∷ envρ ρ)) (satAt (suc k) φ)
                  (λ ws' x' → sym (tval-ok k t ws' x'))
                  (λ w w' ws' x' p h →
                    sat-resp φ (consEq w w' (ws' ++ x' ∷ envρ ρ) p) h)
                  (snd r .snd) ws x)
                (⇔-sym (sat-∀∈ t φ (ws ++ x ∷ envρ ρ)))
            where
            r = walk (suc k) φ d
          walk k (∃̇∈ t φ) (δ-∃∈ d) =
            bexComp (termC k t) (fst r) , bexSub (termC k t) (fst r)
            , λ ws x → ⇔-trans
                (bexChar (termC k t) (fst r)
                  (λ ws' x' → TmV t (ws' ++ x' ∷ envρ ρ)) (satAt (suc k) φ)
                  (λ ws' x' → sym (tval-ok k t ws' x'))
                  (λ w w' ws' x' p h →
                    sat-resp φ (consEq w w' (ws' ++ x' ∷ envρ ρ) p) h)
                  (snd r .snd) ws x)
                (⇔-sym (sat-∃∈ t φ (ws ++ x ∷ envρ ρ)))
            where
            r = walk (suc k) φ d
          walk k (∃̇ φ) ()
          walk k (∀̇ φ) ()
```

<!--en-->
The statement of record. The composite's value is extensionally the
definable-subset former's value: the two certificates plus the former's
membership specification give both inclusions, with the fibre of a member's
presentation as the only bookkeeping.
<!--zh-->
存档陈述。复合之值外延地等于可定义子集算子之值：两份证书加上算子的成员规格给出两侧包含，唯一的记账是成员表示的纤维。
<!--/-->

```agda
          realize : (φ : Formula ⟪ u ⟫ (suc n)) → Δ₀ φ
                  → Σ[ c ∈ Comp 0 ] (eval c [] ≡ DSet φ ρ [])
          realize φ d = fst r , extensionality (eval (fst r) []) (DSet φ ρ []) (sub₁ , sub₂)
            where
            r = walk 0 φ d
            sub₁ : ⟨ eval (fst r) [] ⊆ DSet φ ρ [] ⟩
            sub₁ y y∈ = ∈ₛ-elt (DSet φ ρ []) (fib .snd)
              (dset-mem φ ρ [] i .snd
                (snd r .snd [] (mem i) .fst
                  (∈ₛ-elt (eval (fst r) []) (sym (mem-fst i ∙ fib .snd)) y∈)))
              where
              fib = ∈-asFiber {a = y} {b = u}
                      (∈∈ₛ {a = y} {b = u} .snd (snd r .fst [] y y∈))
              i : ⟪ u ⟫
              i = fib .fst
            sub₂ : ⟨ DSet φ ρ [] ⊆ eval (fst r) [] ⟩
            sub₂ y y∈ = ∈ₛ-elt (eval (fst r) []) (mem-fst i ∙ fib .snd)
              (snd r .snd [] (mem i) .snd
                (dset-mem φ ρ [] i .fst
                  (∈ₛ-elt (DSet φ ρ []) (sym (fib .snd)) y∈)))
              where
              fib = ∈-asFiber {a = y} {b = u}
                      (∈∈ₛ {a = y} {b = u} .snd (dset-sub φ ρ [] y y∈))
              i : ⟪ u ⟫
              i = fib .fst
```

<!--en-->
## The real face
<!--zh-->
## 真实面孔
<!--/-->

<!--en-->
Now the instantiation. The tree's inner satisfaction, compressed one universe
down, is the face's `Sat`; the term valuation is the structure's own; the member
injection and the parameter environment are the ones `DefOf` uses; and the
definable-subset former is `DefOf.defSet` with `k` witness slots in front. Every
one of the twelve reads holds by definition, because the smallness recursion
computes on the formula's constructor, and the environment congruence is the
only one with a proof.
<!--zh-->
现在代入。树的内层满足压低一个宇宙即面孔的 `Sat`；词项赋值取结构自身的；成员内射与参数环境取 `DefOf` 所用的；可定义子集算子是前面多出 `k` 个见证槽的 `DefOf.defSet`。十二条读取无一不按定义成立，因为小性递归在公式的构造子上计算，唯有环境同余需要证明。
<!--/-->

```agda
      satN : {m : ℕ} (φ : Formula ⟪ u ⟫ m) → Vec SM m → hProp ℓ
      satN φ γ = ⊨ᵐ-small φ γ .fst

      tmN : {m : ℕ} (t : Term ⟪ u ⟫ m) → Vec SM m → V ℓ
      tmN t γ = fst (⟦ t ⟧ᵐ γ)

      ρV : {m : ℕ} → (Fin m → ⟪ u ⟫) → Vec SM m
      ρV {zero} ρ = []
      ρV {suc m} ρ = ι (ρ zero) ∷ ρV (ρ ∘ suc)

      ρV-fst : {m : ℕ} (ρ : Fin m → ⟪ u ⟫) (j : Fin m)
             → fst (lookup j (ρV ρ)) ≡ ⟪ u ⟫↪ (ρ j)
      ρV-fst {zero} ρ ()
      ρV-fst {suc m} ρ zero = refl
      ρV-fst {suc m} ρ (suc j) = ρV-fst (ρ ∘ suc) j

      tmN-eq : {m : ℕ} (t : Term ⟪ u ⟫ m) {γ γ' : Vec SM m}
             → ((i : Fin m) → fst (lookup i γ) ≡ fst (lookup i γ'))
             → tmN t γ ≡ tmN t γ'
      tmN-eq (con c) h = refl
      tmN-eq (var i) h = h i

      consN : {m : ℕ} {γ γ' : Vec SM m} (w : SM)
            → ((i : Fin m) → fst (lookup i γ) ≡ fst (lookup i γ'))
            → (i : Fin (suc m)) → fst (lookup i (w ∷ γ)) ≡ fst (lookup i (w ∷ γ'))
      consN w h zero = refl
      consN w h (suc i) = h i

      satN-eq : {m : ℕ} (φ : Formula ⟪ u ⟫ m) {γ γ' : Vec SM m}
              → ((i : Fin m) → fst (lookup i γ) ≡ fst (lookup i γ'))
              → satN φ γ ≡ satN φ γ'
      satN-eq (t ∈̇ s) h = cong₂ _∈ₛ_ (tmN-eq t h) (tmN-eq s h)
      satN-eq (t ≐ s) h = cong₂ _∼_ (tmN-eq t h) (tmN-eq s h)
      satN-eq (φ ∧̇ ψ) h = cong₂ _⊓_ (satN-eq φ h) (satN-eq ψ h)
      satN-eq (φ ∨̇ ψ) h = cong₂ _⊔_ (satN-eq φ h) (satN-eq ψ h)
      satN-eq (φ ⇒̇ ψ) h = cong₂ _⇒_ (satN-eq φ h) (satN-eq ψ h)
      satN-eq (¬̇ φ) h = cong ¬_ (satN-eq φ h)
      satN-eq ⊤̇ h = refl
      satN-eq ⊥̇ h = refl
      satN-eq (∃̇ φ) h = cong ∃[]-syntax (funExt λ i → satN-eq φ (consN (ι i) h))
      satN-eq (∀̇ φ) h = cong ∀[]-syntax (funExt λ i → satN-eq φ (consN (ι i) h))
      satN-eq (∃̇∈ t φ) h = cong ∃[]-syntax (funExt λ i →
          cong₂ _⊓_ (cong (λ v → ⟪ u ⟫↪ i ∈ₛ v) (tmN-eq t h))
                    (satN-eq φ (consN (ι i) h)))
      satN-eq (∀̇∈ t φ) h = cong ∀[]-syntax (funExt λ i →
          cong₂ _⇒_ (cong (λ v → ⟪ u ⟫↪ i ∈ₛ v) (tmN-eq t h))
                    (satN-eq φ (consN (ι i) h)))

      DefSetK : {k m : ℕ} (φ : Formula ⟪ u ⟫ (k + suc m)) (ρ : Fin m → ⟪ u ⟫)
              → Vec SM k → V ℓ
      DefSetK {k} {m} φ ρ ws =
        sett (Σ[ i ∈ ⟪ u ⟫ ] ⟨ satN φ (ws ++ ι i ∷ ρV ρ) ⟩) (λ p → ⟪ u ⟫↪ (p .fst))

      ⟪⟫↪-inj : {i j : ⟪ u ⟫} → ⟪ u ⟫↪ i ≡ ⟪ u ⟫↪ j → i ≡ j
      ⟪⟫↪-inj {i} {j} = isEmbedding→Inj isEmb⟪ u ⟫↪ i j

      defmemK : {k m : ℕ} (φ : Formula ⟪ u ⟫ (k + suc m)) (ρ : Fin m → ⟪ u ⟫)
              → (ws : Vec SM k) (i : ⟪ u ⟫)
              → ⟨ ⟪ u ⟫↪ i ∈ₛ DefSetK φ ρ ws ⇔ₚ satN φ (ws ++ ι i ∷ ρV ρ) ⟩
      defmemK {k} {m} φ ρ ws i = fwd , bwd
        where
        P : ⟪ u ⟫ → hProp ℓ
        P j = satN φ (ws ++ ι j ∷ ρV ρ)
        fwd : ⟨ ⟪ u ⟫↪ i ∈ₛ DefSetK φ ρ ws ⟩ → ⟨ P i ⟩
        fwd x∈ = PT.rec (snd (P i)) go
          (∈∈ₛ {a = ⟪ u ⟫↪ i} {b = DefSetK φ ρ ws} .snd x∈)
          where
          go : Σ[ p ∈ Σ[ j ∈ ⟪ u ⟫ ] ⟨ P j ⟩ ] (⟪ u ⟫↪ (p .fst) ≡ ⟪ u ⟫↪ i) → ⟨ P i ⟩
          go ((j , h) , q) = subst ⟨_⟩ (cong P (⟪⟫↪-inj q)) h
        bwd : ⟨ P i ⟩ → ⟨ ⟪ u ⟫↪ i ∈ₛ DefSetK φ ρ ws ⟩
        bwd h = ∈∈ₛ {a = ⟪ u ⟫↪ i} {b = DefSetK φ ρ ws} .fst ∣ (i , h) , refl ∣₁

      defsubK : {k m : ℕ} (φ : Formula ⟪ u ⟫ (k + suc m)) (ρ : Fin m → ⟪ u ⟫)
              → (ws : Vec SM k) (y : V ℓ) → ⟨ y ∈ₛ DefSetK φ ρ ws ⟩ → ⟨ y ∈ₛ u ⟩
      defsubK {k} {m} φ ρ ws y y∈ = PT.rec (snd (y ∈ₛ u)) go
        (∈∈ₛ {a = y} {b = DefSetK φ ρ ws} .snd y∈)
        where
        go : Σ[ p ∈ Σ[ j ∈ ⟪ u ⟫ ] ⟨ satN φ (ws ++ ι j ∷ ρV ρ) ⟩ ]
               (⟪ u ⟫↪ (p .fst) ≡ y) → ⟨ y ∈ₛ u ⟩
        go ((j , h) , q) = ∈ₛ-elt u q (∈ₛ⟪ u ⟫↪ j)

      module Real = Face satN tmN ι ρV
        (λ i → refl) ρV-fst (λ c γ → refl) (λ i γ → refl)
        (λ t s γ → (λ h → h) , (λ h → h))
        (λ t s γ → (λ h → h) , (λ h → h))
        (λ φ ψ γ → (λ h → h) , (λ h → h))
        (λ φ ψ γ → (λ h → h) , (λ h → h))
        (λ φ ψ γ → (λ h → h) , (λ h → h))
        (λ φ γ → (λ h → h) , (λ h → h))
        (λ γ → tt*)
        (λ γ h → Empty.rec* h)
        (λ t φ γ → (λ h → h) , (λ h → h))
        (λ t φ γ → (λ h → h) , (λ h → h))
        (λ φ h → subst ⟨_⟩ (satN-eq φ h))
        DefSetK defmemK defsubK

      open Real using ( module Walk )
```

<!--en-->
## The two endpoints
<!--zh-->
## 两个端点
<!--/-->

<!--en-->
The realization, at the definable-subset former with `k = 0`, and its corollary
at the tree's own `defSet`: with no witness slots and no parameters, the two
sets are the same by definition, so the corollary is the theorem read at the
face `DefOf` presents to the rest of the development.
<!--zh-->
领悟，在 `k = 0` 的可定义子集算子处，及其在树自身 `defSet` 处的推论：没有见证槽也没有参数时，两个集合按定义相同，故推论就是定理在 `DefOf` 向本书其余部分呈现的那个面孔上的读法。
<!--/-->

```agda
      realize : {n : ℕ} (ρ : Fin n → ⟪ u ⟫) (φ : Formula ⟪ u ⟫ (suc n)) → Δ₀ φ
              → Σ[ c ∈ Comp 0 ] (eval c [] ≡ DefSetK φ ρ [])
      realize ρ φ d = Walk.realize ρ φ d

      realize-defSet : (φ : Formula ⟪ u ⟫ 1) → Δ₀ φ
                     → Σ[ c ∈ Comp 0 ] (eval c [] ≡ U.defSet φ)
      realize-defSet φ d = realize (λ ()) φ d
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The comprehension direction is priced: given the basis operations with their
two-direction specifications and an image operation, every Δ₀ formula with
parameters from a transitive `u` is realized by a finite composite, and the
composite's value is the definable subset on the nose. Two classical spends
appear, at implication and at the bounded universal, both discharged by double
negation from the module's `lem`. The operations layer owes the basis: the
switch theorem's other direction, and the construction of the operations
themselves.
<!--zh-->
领悟方向已标价：给定带双向规格的基运算与一个像运算，传递集 `u` 上带参数的每个 Δ₀ 公式都被某个有限复合领悟，而该复合之值恰是那个可定义子集。经典支出出现两笔，在蕴含与有界全称处，都由模块的 `lem` 经双重否定兑付。运算层欠着这个基：切换定理的另一方向，以及诸运算自身的构造。
<!--/-->
