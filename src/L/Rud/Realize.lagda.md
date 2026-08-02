# The realization induction

<!--en-->
This chapter prices the comprehension direction of the rud route's switch
theorem: every Δ₀-definable subset of a transitive set `u` is the value of a
finite composite of the abstract basis operations. The basis is a module
telescope, so nothing concrete ever unfolds (lesson P-h); the induction walks
the tree's own `Formula` syntax and its `Δ₀` witnesses, and the statement is
an extensional equality against the tree's definable-subset face (`DefOf`).
The probe's miniature carried the design decisions; this chapter scales it to
the full fragment, with equality atoms, disjunction, implication, bounded
universal quantification, and nested bounded quantifiers as the new ground.
<!--zh-->
本章为 rud 路线切换定理的领悟方向标价：传递集 `u` 的每个 Δ₀ 可定义子集，都是抽象基运算的某个有限复合之值。基是一个模块参数表，因此没有任何具体对象展开 (法则 P-h)；归纳行走在树自身的 `Formula` 语法与其 `Δ₀` 见证上，陈述是对着树的可定义子集面孔 (`DefOf`) 的外延等式。探针的微型版承载了全部设计决定；本章把它放大到完整片段，新增地面是等词原子、析取、蕴含、有界全称与嵌套有界量词。
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
open import L.Definability {ℓ} using ( module DefOf )
open import Cubical.Foundations.Equiv using ( equivFun; invEquiv )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.Prelude using ( J )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _++_; map )
import Cubical.Functions.Logic as Logic
open Logic using ( _⊓_; _⊔_; _⇒_; _⇔_; ¬_; ∃[]-syntax; ∀[]-syntax )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt*; Unit* )
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using ( Acc; acc; isPropAcc; WellFounded; wf→x≮x )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; elimProp; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; _∼_; ∈∈ₛ; identityPrinciple; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
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
infixr 8 _⊓ₚ_ _⊔ₚ_ _⊓ₚ⁺_ _⊓₂_
infixr 4 _⇔ₚ_ _⇒ₚ_

_⊓ₚ_ : hProp ℓ → hProp ℓ → hProp ℓ
A ⊓ₚ B = A ⊓ B

_⊓ₚ⁺_ : hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ)
A ⊓ₚ⁺ B = A ⊓ B

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
union (pair plus union), collection, characteristic separation, images and
bounded union; product and the membership relation are carried so the
interface spans both candidate bases. The equality atom whose sides are both
x-free forces one classical spend, a constant-equality separation, which the
evaluation performs by excluded middle (reported in the LEM inventory).
<!--zh-->
基是探针的参数表，另加经典律作为模块参数：领悟消费差、交、二元并 (配对加并)、收集、特征分离、像与有界并；积与成员关系被携带，使接口覆盖两个候选基。两侧都不含 x 的等词原子迫使一笔经典支出，即常量等词分离，由求值经排中律执行 (记入 LEM 清点)。
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
Transitivity is stated in the small-membership form; it is consumed exactly
where the paper proof uses it, lifting bounded-quantifier witnesses from a
bound into `u`. Regularity refutes self-membership, which prices the diagonal
atom `x ∈ x`.
<!--zh-->
传递以小成员形式陈述；它恰在论文证明使用之处被消费，把有界量词见证从界内提升进 `u`。正则反驳自成员，为对角原子 `x ∈ x` 定价。
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
A composite of arity `k` has `k` free slots for the witness stack of `k`
nested bounded quantifiers, plus constants and the separated variable's
container. The image constructor takes a family one arity higher and a set;
the equality-separation constructor is decided at evaluation by excluded
middle. The pure syntax lives here, and the evaluation in an inner module
whose parameter supplies the image operation, so the interface stays abstract
(lesson P-h).
<!--zh-->
元数为 `k` 的复合带有 `k` 个自由槽，装 `k` 层嵌套有界量词的见证栈，另加常量与被分离变量的容器。像构造子取一个高一元数的族与一个集合；等词分离构造子在求值处由排中律判定。纯语法住在这里，求值住在以内层模块参数供应像运算的地方，接口由此保持抽象 (法则 P-h)。
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

  module Eval (imgOp : {k : ℕ} → Comp k → V ℓ → V ℓ) where

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
    eval (eqSepC a b c) ws =
      eqSepOp (eval a ws) (eval b ws) (eval c ws)
    eval (imgC f a) ws = imgOp f (eval a ws)
```

<!--en-->
### Operation-level facts
<!--zh-->
### 运算层事实
<!--/-->

<!--en-->
Three facts about the abstract operations pay for the clause work: a binary
union is the union of a pair, a doubled pair is a singleton, and the
classically decided equality-separation characterizes membership exactly as
membership in the container together with bisimilarity of the two sides.
<!--zh-->
抽象运算的三条事实为子句工作买单：二元并是配对的并，重复的配对是单点集，而由经典判定构造的等词分离把成员刻画为「属于容器且两侧双相似」。
<!--/-->

```agda
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

    eqSep-mem : {k : ℕ} (a b c : Comp k) (ws : Vec (V ℓ) k) (x : V ℓ)
              → ⟨ (x ∈ₛ eval (eqSepC a b c) ws)
                  ⇔ₚ ((x ∈ₛ eval c ws) ⊓ₚ (eval a ws ∼ eval b ws)) ⟩
    eqSep-mem a b c ws x = eqSepSpec (eval a ws) (eval b ws) (eval c ws) x
```

<!--en-->
## The definable-subset face
<!--zh-->
## 可定义子集面孔
<!--/-->

<!--en-->
Relative to one transitive `u`, the walk works over the tree's inner
satisfaction on the restricted structure: `satN` compresses it one universe
down, `ρV` turns a parameter environment into an environment of members, and
`DefSetK` separates the formula's extension from `u` exactly as `DefOf.defSet`
does, with `k` witness slots in front. The membership specification mirrors
`DefOf.defSet-mem`.
<!--zh-->
相对一个传递集 `u`，行走工作在树的内层满足 (限制结构上) 之上：`satN` 把它压低一个宇宙，`ρV` 把参数环境变成成员环境，`DefSetK` 与 `DefOf.defSet` 相同地从 `u` 中分离公式的外延，只是前面多出 `k` 个见证槽。成员规格照抄 `DefOf.defSet-mem`。
<!--/-->

```agda
    module Realize (u : V ℓ) (tu : Trans u)
                   (imgSpec : {k : ℕ} (f : Comp (suc k)) (p : V ℓ) (ws : Vec (V ℓ) k) (z : V ℓ)
                     → (⟨ z ∈ₛ imgOp f p ⟩ → ⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ eval f (y ∷ ws))) ⟩)
                     × (⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ eval f (y ∷ ws))) ⟩ → ⟨ z ∈ₛ imgOp f p ⟩))
      where

      module U = DefOf u
      open U using ( SM; ι; ⟦_⟧ᵐ; ⊨ᵐ-small )

      satN : {n : ℕ} (φ : Formula ⟪ u ⟫ n) → Vec SM n → hProp ℓ
      satN φ γ = ⊨ᵐ-small φ γ .fst

      ρV : {n : ℕ} → (Fin n → ⟪ u ⟫) → Vec SM n
      ρV {zero} ρ = []
      ρV {suc n} ρ = ι (ρ zero) ∷ ρV (ρ ∘ suc)

      DefSetK : {k n : ℕ} (φ : Formula ⟪ u ⟫ (k + suc n)) (ρ : Fin n → ⟪ u ⟫)
              → Vec SM k → V ℓ
      DefSetK {k} {n} φ ρ ws =
        sett (Σ[ m ∈ ⟪ u ⟫ ] ⟨ satN φ (ws ++ ι m ∷ ρV ρ) ⟩) (λ p → ⟪ u ⟫↪ (p .fst))

      ⟪⟫↪-inj : {m' m : ⟪ u ⟫} → ⟪ u ⟫↪ m' ≡ ⟪ u ⟫↪ m → m' ≡ m
      ⟪⟫↪-inj {m'} {m} = isEmbedding→Inj isEmb⟪ u ⟫↪ m' m

      defmemK : {k n : ℕ} (φ : Formula ⟪ u ⟫ (k + suc n)) (ρ : Fin n → ⟪ u ⟫)
              → (ws : Vec SM k) (m : ⟪ u ⟫)
              → ⟨ ⟪ u ⟫↪ m ∈ₛ DefSetK φ ρ ws ⇔ₚ satN φ (ws ++ ι m ∷ ρV ρ) ⟩
      defmemK {k} {n} φ ρ ws m = fwd , bwd
        where
        P : ⟪ u ⟫ → hProp ℓ
        P m' = satN φ (ws ++ ι m' ∷ ρV ρ)
        fwd : ⟨ ⟪ u ⟫↪ m ∈ₛ DefSetK φ ρ ws ⟩ → ⟨ P m ⟩
        fwd x∈ = PT.rec (snd (P m)) go (∈∈ₛ {a = ⟪ u ⟫↪ m} {b = DefSetK φ ρ ws} .snd x∈)
          where
          go : Σ[ p ∈ Σ[ m' ∈ ⟪ u ⟫ ] ⟨ P m' ⟩ ] (⟪ u ⟫↪ (p .fst) ≡ ⟪ u ⟫↪ m) → ⟨ P m ⟩
          go ((m' , h) , q) = subst ⟨_⟩ (cong P (⟪⟫↪-inj q)) h
        bwd : ⟨ P m ⟩ → ⟨ ⟪ u ⟫↪ m ∈ₛ DefSetK φ ρ ws ⟩
        bwd h = ∈∈ₛ {a = ⟪ u ⟫↪ m} {b = DefSetK φ ρ ws} .fst ∣ (m , h) , refl ∣₁
```

<!--en-->
### The satisfaction respects pointwise-equal environments
<!--zh-->
### 满足关系尊重逐点相等环境
<!--/-->

<!--en-->
The inner satisfaction only looks free variables up in the environment, so two
environments whose entries agree on first components give equal truth values.
This is the one congruence the bounded-quantifier clauses need when a witness
is repacked as a member of `u` (the fibre of its presentation).
<!--zh-->
内层满足只按环境查自由变量，故两个逐项第一分量一致的环境给出相等的真值。这是有界量词子句在把见证重新打包为 `u` 的成员 (其表示之纤维) 时所需的唯一同余。
<!--/-->

```agda
      tmVal : {n : ℕ} → Term ⟪ u ⟫ n → Vec SM n → V ℓ
      tmVal (con c) γ = ⟪ u ⟫↪ c
      tmVal (var i) γ = fst (lookup i γ)

      tmVal-eq : {n : ℕ} (t : Term ⟪ u ⟫ n) {γ γ' : Vec SM n}
               → ((i : Fin n) → fst (lookup i γ) ≡ fst (lookup i γ')) → tmVal t γ ≡ tmVal t γ'
      tmVal-eq (con c) h = refl
      tmVal-eq (var i) h = h i

      tmVal-ok : {n : ℕ} (t : Term ⟪ u ⟫ n) (γ : Vec SM n)
               → fst (⟦ t ⟧ᵐ γ) ≡ tmVal t γ
      tmVal-ok (con c) γ = refl
      tmVal-ok (var i) γ = refl

      cons-resp : {n : ℕ} {γ γ' : Vec SM n} (m : SM)
                → ((i : Fin n) → fst (lookup i γ) ≡ fst (lookup i γ'))
                → (i : Fin (suc n)) → fst (lookup i (m ∷ γ)) ≡ fst (lookup i (m ∷ γ'))
      cons-resp m h zero = refl
      cons-resp m h (suc i) = h i

      satN-resp : {n : ℕ} (φ : Formula ⟪ u ⟫ n) {γ γ' : Vec SM n}
                  → ((i : Fin n) → fst (lookup i γ) ≡ fst (lookup i γ'))
                  → satN φ γ ≡ satN φ γ'
      satN-resp (t ∈̇ u') {γ} {γ'} h =
        cong₂ _∈ₛ_ (tmVal-ok t γ ∙ tmVal-eq t h ∙ sym (tmVal-ok t γ'))
                   (tmVal-ok u' γ ∙ tmVal-eq u' h ∙ sym (tmVal-ok u' γ'))
      satN-resp (t ≐ u') {γ} {γ'} h =
        cong₂ _∼_ (tmVal-ok t γ ∙ tmVal-eq t h ∙ sym (tmVal-ok t γ'))
                  (tmVal-ok u' γ ∙ tmVal-eq u' h ∙ sym (tmVal-ok u' γ'))
      satN-resp (φ ∧̇ ψ) h = cong₂ _⊓_ (satN-resp φ h) (satN-resp ψ h)
      satN-resp (φ ∨̇ ψ) h = cong₂ _⊔_ (satN-resp φ h) (satN-resp ψ h)
      satN-resp (φ ⇒̇ ψ) h = cong₂ _⇒_ (satN-resp φ h) (satN-resp ψ h)
      satN-resp (¬̇ φ) h = cong ¬_ (satN-resp φ h)
      satN-resp ⊤̇ h = refl
      satN-resp ⊥̇ h = refl
      satN-resp (∃̇ φ) {γ} {γ'} h = cong ∃[]-syntax (funExt λ m → satN-resp φ (cons-resp (ι m) h))
      satN-resp (∀̇ φ) {γ} {γ'} h = cong ∀[]-syntax (funExt λ m → satN-resp φ (cons-resp (ι m) h))
      satN-resp (∃̇∈ t φ) {γ} {γ'} h = cong ∃[]-syntax (funExt λ m →
          cong₂ _⊓_ (cong (λ v → ⟪ u ⟫↪ m ∈ₛ v) (tmVal-ok t γ ∙ tmVal-eq t h ∙ sym (tmVal-ok t γ')))
                    (satN-resp φ (cons-resp (ι m) h)))
      satN-resp (∀̇∈ t φ) {γ} {γ'} h = cong ∀[]-syntax (funExt λ m →
          cong₂ _⇒_ (cong (λ v → ⟪ u ⟫↪ m ∈ₛ v) (tmVal-ok t γ ∙ tmVal-eq t h ∙ sym (tmVal-ok t γ')))
                    (satN-resp φ (cons-resp (ι m) h)))
  ```

  <!--en-->
  ### The variable plumbing
  <!--zh-->
  ### 变量机件
  <!--/-->

  <!--en-->
  The tree's de Bruijn syntax makes variable permutation definitional: the
  formula at depth `k` reads variable `k` as the separated `x`, variables below
  as the witness stack, variables above as parameters, and the split below
  dispatches the index. The term translation then turns each term into either a
  composite (a constant, a witness slot, or a parameter value) or the marker
  for the separated variable; its evaluation agrees with the tree's term
  evaluation on the nose.
  <!--zh-->
  树的 de Bruijn 语法把变量置换做成定义性的：深度 `k` 处把变量 `k` 读作被分离的 `x`，其下诸变量是见证栈，其上诸变量是参数，下面的分裂完成序号分派。词项翻译随即把每个词项变成复合 (常量、见证槽或参数值) 或「被分离变量」记号；其求值与树的词项求值分毫不差。
  <!--/-->

  ```agda
      inl-inj : {A : Type (ℓ-suc ℓ)} {B : Type ℓ} {x y : A}
              → (p : inl {A = A} {B = B} x ≡ inl y) → x ≡ y
      inl-inj {x = x} p = J (λ { (inl y) q → x ≡ y ; (inr y) q → Empty.⊥* {ℓ-suc ℓ} }) refl p

      inl-inr-disj : {A : Type (ℓ-suc ℓ)} {B : Type ℓ} {x : A} {y : B}
                   → (p : inl {A = A} {B = B} x ≡ inr y) → Empty.⊥* {ℓ}
      inl-inr-disj {x = x} p = subst (λ { (inl _) → Unit* {ℓ} ; (inr _) → Empty.⊥* {ℓ} }) p tt*

      lookup-map : {n : ℕ} {A B : Type (ℓ-suc ℓ)} (f : A → B) (v : Vec A n) (j : Fin n)
                 → lookup j (map f v) ≡ f (lookup j v)
      lookup-map f [] ()
      lookup-map f (x ∷ v) zero = refl
      lookup-map f (x ∷ v) (suc j) = lookup-map f v j

      eval-cong : {k : ℕ} {a b : Comp k} (p : a ≡ b) (ws : Vec (V ℓ) k)
                → eval a ws ≡ eval b ws
      eval-cong p ws = λ ι → eval (p ι) ws

      sucMap : {k n : ℕ} → Fin k ⊎ Fin (suc n) → Fin (suc k) ⊎ Fin (suc n)
      sucMap (inl j) = inl (suc j)
      sucMap (inr j) = inr j
      split : {k n : ℕ} → Fin (k + suc n) → Fin k ⊎ Fin (suc n)
      split {zero} {n} i = inr i
      split {suc k} {n} zero = inl zero
      split {suc k} {n} (suc i) = sucMap {k} {n} (split {k} {n} i)


      valSplit : {k n : ℕ} → Fin k ⊎ Fin (suc n) → (Fin n → ⟪ u ⟫) → Vec SM k → SM → V ℓ
      valSplit (inl j) ρ ws x = fst (lookup j ws)
      valSplit (inr zero) ρ ws x = fst x
      valSplit (inr (suc j)) ρ ws x = ⟪ u ⟫↪ (ρ j)

      valSplit-suc : {k n : ℕ} (s : Fin k ⊎ Fin (suc n)) (ρ : Fin n → ⟪ u ⟫)
                   → (w : SM) (ws : Vec SM k) (x : SM)
                   → valSplit (sucMap s) ρ (w ∷ ws) x ≡ valSplit s ρ ws x
      valSplit-suc (inl j) ρ w ws x = refl
      valSplit-suc (inr zero) ρ w ws x = refl
      valSplit-suc (inr (suc j)) ρ w ws x = refl

      semSplit : {k n : ℕ} → Fin k ⊎ Fin (suc n) → (Fin n → ⟪ u ⟫) → Comp k ⊎ Unit* {ℓ}
      semSplit (inl j) ρ = inl (varC j)
      semSplit (inr zero) ρ = inr tt*
      semSplit (inr (suc j)) ρ = inl (conC (⟪ u ⟫↪ (ρ j)))

      termC : {k n : ℕ} → Term ⟪ u ⟫ (k + suc n) → (Fin n → ⟪ u ⟫) → Comp k ⊎ Unit* {ℓ}
      termC (con c) ρ = inl (conC (⟪ u ⟫↪ c))
      termC (var i) ρ = semSplit (split i) ρ

      valSem : {k n : ℕ} → Comp k ⊎ Unit* {ℓ} → (Fin n → ⟪ u ⟫) → Vec SM k → SM → V ℓ
      valSem (inl c) ρ ws x = eval c (map fst ws)
      valSem (inr _) ρ ws x = fst x

      fstρV : {n : ℕ} (ρ : Fin n → ⟪ u ⟫) (j : Fin n) → fst (lookup j (ρV ρ)) ≡ ⟪ u ⟫↪ (ρ j)
      fstρV {n = zero} ρ ()
      fstρV {n = suc n} ρ zero = refl
      fstρV {n = suc n} ρ (suc j) = fstρV (ρ ∘ suc) j

      lookup-split : {k n : ℕ} (ws : Vec SM k) (x : SM) (ρ : Fin n → ⟪ u ⟫)
                   → (i : Fin (k + suc n))
                   → fst (lookup i (ws ++ x ∷ ρV ρ)) ≡ valSplit (split {k} {n} i) ρ ws x
      lookup-split {k = zero} [] x ρ i = lookup-tail x ρ i
        where
        lookup-tail : {n : ℕ} (x : SM) (ρ : Fin n → ⟪ u ⟫)
                    → (i : Fin (suc n))
                    → fst (lookup i (x ∷ ρV ρ)) ≡ valSplit (inr i) ρ [] x
        lookup-tail x ρ zero = refl
        lookup-tail x ρ (suc j) = fstρV ρ j
      lookup-split {k = suc k'} (w ∷ ws) x ρ zero = refl
      lookup-split {k = suc k'} (w ∷ ws) x ρ (suc i) =
        lookup-split {k = k'} ws x ρ i ∙ sym (valSplit-suc (split {k'} i) ρ w ws x)

      val≡ : {k n : ℕ} (t : Term ⟪ u ⟫ (k + suc n)) (ρ : Fin n → ⟪ u ⟫)
           → (ws : Vec SM k) (x : SM)
           → fst (⟦ t ⟧ᵐ (ws ++ x ∷ ρV ρ)) ≡ valSem (termC t ρ) ρ ws x
      val≡ (con c) ρ ws x = refl
      val≡ (var i) ρ ws x =
        lookup-split ws x ρ i ∙ sym (valSem-semSplit (split i) ρ ws x)
        where
        valSem-semSplit : {k n : ℕ} (s : Fin k ⊎ Fin (suc n)) (ρ : Fin n → ⟪ u ⟫)
                        → (ws : Vec SM k) (x : SM)
                        → valSem (semSplit s ρ) ρ ws x ≡ valSplit s ρ ws x
        valSem-semSplit (inl j) ρ ws x = lookup-map fst ws j
        valSem-semSplit (inr zero) ρ ws x = refl
        valSem-semSplit (inr (suc j)) ρ ws x = refl

```
