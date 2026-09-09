<!--en-->
# Quantifying over coded pairs and finite formula families
<!--zh-->
# 对码化有序对分量与有穷公式族量化
<!--ja-->
# 符号化された順序対の成分と有限論理式族を量化する
<!--/-->

<!--en-->
This chapter supplies the shared finite-slot machinery used by coded formulas.
It names deeply nested slots, folds finite families into conjunctions and
disjunctions, and defines bounded formulas that unpack coded pairs together with
readers that hide their container witnesses.
<!--zh-->
本章提供码化公式共用的有穷槽位工具：为深层嵌套的槽位命名，把有穷公式族折叠成合取与析取，并定义拆出码化有序对分量的有界公式及隐藏容器见证的读式。
<!--ja-->
本章では、符号化された論理式が共有する有限スロットの道具を整備する。深く入れ子になったスロットに名前を付け、有限論理式族を連言と選言へ畳み込み、符号化された順序対の成分を取り出す有界論理式と、容器の証人を隠す読み補題を与える。
<!--/-->

<!--en-->
Coded syntax repeatedly quantifies over the components of a pair. Building on
the coding vocabulary and pair expressions, this chapter develops the shared
slot arithmetic, bounded formulas and semantic readers for those quantifiers.
The tower specification uses these readers first; code-domain, satisfaction-clause
and coded-graph chapters then reuse the same readers. Each can state its
mathematics in terms of components without repeating the container witnesses
required by bounded syntax.
<!--zh-->
码化语法需要反复量化一个配对的分量。本章以码化词汇与配对表达式为基础，构造这些量词共用的槽位运算、有界公式与语义读式。塔规格最先使用这些读式，随后码域、满足子句与码化图诸章继续复用。它们都能按分量陈述数学内容，无须重复有界语法所需的容器见证。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Quantification {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∧̇_; _∨̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∧; δ-⇒; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.PairFormulas {ℓ} using ( Δ₀-prAt; ∈pair-introL; ∈pair-introR )
open import L.Coding.Environment {ℓ} using ( Δ₀-sucAt )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate )
open import L.Coding.Expressions {ℓ} using ( sucAtL; sucAtL-adequate )
open import L.Coding.Model {ℓ} using ( container )
import L.Coding.Expressions {ℓ} as CodingExpressions
module E = CodingExpressions.PairExpression

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Slot indices and primitive readers
<!--zh-->
## 槽位索引与基本读式
<!--ja-->
## スロット添字と基本的な読み
<!--/-->

<!--en-->
The shift operation and named inner slots organize deeply nested binders, while
the pair and successor readers turn their atomic formulas back into set
equalities.
<!--zh-->
移位运算与具名内部槽位组织深层嵌套的绑定，而有序对与后继读式把相应原子公式读回为集合等式。
<!--ja-->
シフト演算と名前の付いた内側のスロットが深く入れ子になった束縛子を整理し、順序対と後者の読み補題が対応する原子論理式を集合の等しさへ戻す。
<!--/-->

Slot arithmetic. `sh k` pushes an outer slot past `k` binders; the names `i0` ..
`i19` are the innermost slots at any arity.

```agda
i0 : ∀ {j} → Fin (suc j)
i0 = zero
i1 : ∀ {j} → Fin (2 + j)
i1 = suc i0
i2 : ∀ {j} → Fin (3 + j)
i2 = suc i1
i3 : ∀ {j} → Fin (4 + j)
i3 = suc i2

pr-out : ∀ {m} (q u v : Fin m) (γ : S ^ m) → ⟨ γ ⊨ prAtL q u v ⟩
       → fst (lookup q γ) ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
pr-out q u v γ h = subst ⟨_⟩ (prAtL-adequate q u v γ) h

pr-in : ∀ {m} (q u v : Fin m) (γ : S ^ m)
      → fst (lookup q γ) ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
      → ⟨ γ ⊨ prAtL q u v ⟩
pr-in q u v γ e = subst ⟨_⟩ (sym (prAtL-adequate q u v γ)) e

down : (x : S) (y : V ℓ) → ⟨ y ∈ fst x ⟩ → S
down x y h = y , isL-trans {x = fst x} {y = y} h (snd x)
```

The components of a pair held as an element of L, as elements of L.

```agda
fstS sndS : (x : S) (u v : V ℓ) → fst x ≡ pr u v → S
fstS x u v e = down (down x ⁅ u , v ⁆ (subst (λ z → ⟨ ⁅ u , v ⁆ ∈ z ⟩) (sym e) (∈pair-introR {u = ⁅ u ⁆s} {v = ⁅ u , v ⁆} refl))) u (∈pair-introL {u = u} {v = v} refl)
sndS x u v e = down (down x ⁅ u , v ⁆ (subst (λ z → ⟨ ⁅ u , v ⁆ ∈ z ⟩) (sym e) (∈pair-introR {u = ⁅ u ⁆s} {v = ⁅ u , v ⁆} refl))) v (∈pair-introR {u = u} {v = v} refl)
```

```agda

sh : ∀ {m} (k : ℕ) → Fin m → Fin (k + m)
sh zero i = i
sh (suc k) i = suc (sh k i)

i4 : ∀ {j} → Fin (5 + j)
i4 = suc i3
i5 : ∀ {j} → Fin (6 + j)
i5 = suc i4
i6 : ∀ {j} → Fin (7 + j)
i6 = suc i5
i7 : ∀ {j} → Fin (8 + j)
i7 = suc i6
i8 : ∀ {j} → Fin (9 + j)
i8 = suc i7
i9 : ∀ {j} → Fin (10 + j)
i9 = suc i8
i10 : ∀ {j} → Fin (11 + j)
i10 = suc i9
i11 : ∀ {j} → Fin (12 + j)
i11 = suc i10
i12 : ∀ {j} → Fin (13 + j)
i12 = suc i11
i13 : ∀ {j} → Fin (14 + j)
i13 = suc i12
i14 : ∀ {j} → Fin (15 + j)
i14 = suc i13
i15 : ∀ {j} → Fin (16 + j)
i15 = suc i14
i16 : ∀ {j} → Fin (17 + j)
i16 = suc i15
i17 : ∀ {j} → Fin (18 + j)
i17 = suc i16
i18 : ∀ {j} → Fin (19 + j)
i18 = suc i17
i19 : ∀ {j} → Fin (20 + j)
i19 = suc i18
```

<!--en-->
## Ten named slots and finite connective folds
<!--zh-->
## 十个具名槽位与有穷联结词折叠
<!--ja-->
## 十個の名前付きスロットと有限結合子の畳み込み
<!--/-->

<!--en-->
The patterns `f0` through `f9` name the ten positions used by constructor
families, while `bigOr` and `bigAnd` fold any nonempty finite family of formulas.
Their readers select one disjunct or recover every conjunct without depending on
any particular coding scheme.
<!--zh-->
模式 `f0` 至 `f9` 命名构造子族使用的十个位置，而 `bigOr` 与 `bigAnd` 把任意非空有穷公式族折叠起来。相应读式选出一个析取项或恢复每个合取项，并不依赖任何特定编码方案。
<!--ja-->
パターン `f0` から `f9` は構成子族が使う十個の位置を名付け、`bigOr` と `bigAnd` は任意の空でない有限論理式族を畳み込む。読み補題は、特定の符号化に依存せず、一つの選言肢を選び、またはすべての連言肢を復元する。
<!--/-->

```agda
pattern f0 = zero
pattern f1 = suc f0
pattern f2 = suc f1
pattern f3 = suc f2
pattern f4 = suc f3
pattern f5 = suc f4
pattern f6 = suc f5
pattern f7 = suc f6
pattern f8 = suc f7
pattern f9 = suc f8

bigOr bigAnd : ∀ {m} (n : ℕ) → (Fin (suc n) → Formula S m) → Formula S m
bigOr 0 φ = φ zero
bigOr (suc n) φ = φ zero ∨̇ bigOr n (λ k → φ (suc k))
bigAnd 0 φ = φ zero
bigAnd (suc n) φ = φ zero ∧̇ bigAnd n (λ k → φ (suc k))

module _ {m : ℕ} (γ : S ^ m) where
  bigOr-in : (n : ℕ) (φ : Fin (suc n) → Formula S m) (k : Fin (suc n))
           → ⟨ γ ⊨ φ k ⟩ → ⟨ γ ⊨ bigOr n φ ⟩
  bigOr-in 0 φ zero h = h
  bigOr-in (suc n) φ zero h = ∣ inl h ∣₁
  bigOr-in (suc n) φ (suc k) h = ∣ inr (bigOr-in n (λ j → φ (suc j)) k h) ∣₁

  bigOr-out : (n : ℕ) (φ : Fin (suc n) → Formula S m) → ⟨ γ ⊨ bigOr n φ ⟩
            → ∥ Σ[ k ∈ Fin (suc n) ] ⟨ γ ⊨ φ k ⟩ ∥₁
  bigOr-out 0 φ h = ∣ zero , h ∣₁
  bigOr-out (suc n) φ = PT.rec squash₁
    (λ { (inl h) → ∣ zero , h ∣₁
       ; (inr h) → PT.map (λ { (k , hk) → suc k , hk }) (bigOr-out n (λ j → φ (suc j)) h) })

  bigAnd-in : (n : ℕ) (φ : Fin (suc n) → Formula S m)
            → ((k : Fin (suc n)) → ⟨ γ ⊨ φ k ⟩) → ⟨ γ ⊨ bigAnd n φ ⟩
  bigAnd-in 0 φ h = h zero
  bigAnd-in (suc n) φ h = h zero , bigAnd-in n (λ j → φ (suc j)) (λ k → h (suc k))

  bigAnd-out : (n : ℕ) (φ : Fin (suc n) → Formula S m) → ⟨ γ ⊨ bigAnd n φ ⟩
             → (k : Fin (suc n)) → ⟨ γ ⊨ φ k ⟩
  bigAnd-out 0 φ h zero = h
  bigAnd-out (suc n) φ h zero = h .fst
  bigAnd-out (suc n) φ h (suc k) = bigAnd-out n (λ j → φ (suc j)) (h .snd) k
```

<!--en-->
## Bounded atoms and successor semantics
<!--zh-->
## 有界原子与后继语义
<!--ja-->
## 有界な原子と後者の意味
<!--/-->

<!--en-->
The pair and successor atoms receive Δ₀ witnesses, and `suc-out`{.Agda} with
`suc-in`{.Agda} gives the two semantic directions at a variable environment.
<!--zh-->
有序对与后继原子取得 Δ₀ 见证，而 `suc-out`{.Agda} 与 `suc-in`{.Agda} 给出变元环境处的两个语义方向。
<!--ja-->
順序対と後者の原子に Δ₀ の証人を与え、`suc-out`{.Agda} と `suc-in`{.Agda} が変数環境での二つの意味論的方向を与える。
<!--/-->

The atoms and their certificates.

```agda
Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)
```

The successor reader, both ways, at a variable environment.

```agda
suc-out : ∀ {m} (i j : Fin m) (γ : S ^ m) → ⟨ γ ⊨ sucAtL i j ⟩
        → fst (lookup j γ) ≡ sucV (fst (lookup i γ))
suc-out i j γ h = subst ⟨_⟩ (sucAtL-adequate i j γ) h

suc-in : ∀ {m} (i j : Fin m) (γ : S ^ m)
       → fst (lookup j γ) ≡ sucV (fst (lookup i γ)) → ⟨ γ ⊨ sucAtL i j ⟩
suc-in i j γ e = subst ⟨_⟩ (sym (sucAtL-adequate i j γ)) e
```

<!--en-->
## Bounded quantifiers over pair components
<!--zh-->
## 对有序对分量的有界量化
<!--ja-->
## 順序対の成分に対する有界量化
<!--/-->

<!--en-->
The four macros `sndEx`{.Agda}, `sndAll`{.Agda}, `bothEx`{.Agda}, and
`bothAll`{.Agda} bind pair components through an internal container, in
existential and universal forms that remain Δ₀.
<!--zh-->
四个宏 `sndEx`{.Agda}、`sndAll`{.Agda}、`bothEx`{.Agda} 与 `bothAll`{.Agda} 通过内部容器绑定有序对分量；它们给出的存在与全称形式均保持为 Δ₀。
<!--ja-->
四つのマクロ `sndEx`{.Agda}、`sndAll`{.Agda}、`bothEx`{.Agda}、`bothAll`{.Agda} は内部の容器を通して順序対の成分を束縛し、Δ₀ のままの存在形と全称形を与える。
<!--/-->

The pair as a container. Both components of `pr u v` lie in the member
`⁅ u , v ⁆` of it. This is what lets a Δ₀ formula bind the components of a pair
it holds, with no ambient bound at all.

The opaque pair container is supplied by `L.Coding.Model` and shared with
its structural pair-expression reader.

The destructors. Four macros bind the components of a pair held at a slot: the
second component alone (the first is a slot already), or both, each under an
existential or a universal. The body sits at `v ∷ s ∷ γ`, or at
`v ∷ u ∷ s ∷ γ`, with `s` the container. Every reader is at a variable
environment; the container is junk the reader supplies.

```agda
sndEx : ∀ {m} → Fin m → Fin m → Formula S (2 + m) → Formula S m
sndEx x u body =
  ∃̇∈ (var x) (∃̇∈ (var i0) (prAtL (sh 2 x) (sh 2 u) i0 ∧̇ body))

sndAll : ∀ {m} → Fin m → Fin m → Formula S (2 + m) → Formula S m
sndAll x u body =
  ∀̇∈ (var x) (∀̇∈ (var i0) (prAtL (sh 2 x) (sh 2 u) i0 ⇒̇ body))

bothEx : ∀ {m} → Fin m → Formula S (3 + m) → Formula S m
bothEx x body =
  ∃̇∈ (var x) (∃̇∈ (var i0) (∃̇∈ (var i1) (prAtL (sh 3 x) i1 i0 ∧̇ body)))

bothAll : ∀ {m} → Fin m → Formula S (3 + m) → Formula S m
bothAll x body =
  ∀̇∈ (var x) (∀̇∈ (var i0) (∀̇∈ (var i1) (prAtL (sh 3 x) i1 i0 ⇒̇ body)))

Δ₀-sndEx : ∀ {m} (x u : Fin m) (body : Formula S (2 + m)) → Δ₀ body → Δ₀ (sndEx x u body)
Δ₀-sndEx x u body d = δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL (sh 2 x) (sh 2 u) i0) d))

Δ₀-sndAll : ∀ {m} (x u : Fin m) (body : Formula S (2 + m)) → Δ₀ body → Δ₀ (sndAll x u body)
Δ₀-sndAll x u body d = δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-prAtL (sh 2 x) (sh 2 u) i0) d))

Δ₀-bothAll : ∀ {m} (x : Fin m) (body : Formula S (3 + m)) → Δ₀ body → Δ₀ (bothAll x body)
Δ₀-bothAll x body d = δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-prAtL (sh 3 x) i1 i0) d)))

module _ {m : ℕ} (x u : Fin m) (body : Formula S (2 + m)) (γ : S ^ m) where
  private
    X = fst (lookup x γ)
    U = fst (lookup u γ)
```

<!--en-->
## Reading the component quantifiers
<!--zh-->
## 读取分量量词
<!--ja-->
## 成分量化子を読む
<!--/-->

<!--en-->
The existential `out` lemmas return the propositional truncation of component
data, recording that suitable components merely exist; the universal readers
instead accept explicit components. The corresponding `in` lemmas rebuild
satisfaction from explicit data, using pair injectivity to pin the values.
<!--zh-->
存在式的 `out` 引理从满足关系返回分量数据的命题截断，只记录合适分量的仅仅存在性；全称式读引理则接收明确的分量。相应的 `in` 引理从明确的数据重建满足关系，并应用有序对的单射性得到相应的取值等式。
<!--ja-->
存在形の `out` 補題は充足関係から成分データの命題的切り詰めを返し、適切な成分が単に存在することだけを記録する。全称形の読み補題は明示された成分を受け取る。対応する `in` 補題は明示されたデータから充足関係を再構成し、順序対の単射性で値を確定する。
<!--/-->

Out: the witness's second component is pinned by pair injectivity.

```agda
  sndEx-out : ⟨ γ ⊨ sndEx x u body ⟩
            → ∥ Σ[ v ∈ S ] Σ[ s ∈ S ] ((X ≡ pr U (fst v)) × ⟨ (v ∷ s ∷ γ) ⊨ body ⟩) ∥₁
  sndEx-out = PT.rec squash₁ (λ { (s , (s∈ , h)) → PT.map
    (λ { (v , (v∈ , (e , hb))) → v , s , (pr-out (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e , hb) })
    h })

  sndEx-in : (v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst v ∈ fst s ⟩ → X ≡ pr U (fst v)
           → ⟨ (v ∷ s ∷ γ) ⊨ body ⟩ → ⟨ γ ⊨ sndEx x u body ⟩
  sndEx-in v s s∈ v∈ e hb = ∣ s , (s∈ , ∣ v , (v∈ , (pr-in (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e , hb)) ∣₁) ∣₁

  sndAll-out : ⟨ γ ⊨ sndAll x u body ⟩
             → (v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst v ∈ fst s ⟩ → X ≡ pr U (fst v)
             → ⟨ (v ∷ s ∷ γ) ⊨ body ⟩
  sndAll-out h v s s∈ v∈ e = h s s∈ v v∈ (pr-in (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e)

  sndAll-in : ((v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst v ∈ fst s ⟩ → X ≡ pr U (fst v)
               → ⟨ (v ∷ s ∷ γ) ⊨ body ⟩)
            → ⟨ γ ⊨ sndAll x u body ⟩
  sndAll-in k s s∈ v v∈ e = k v s s∈ v∈ (pr-out (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e)

module _ {m : ℕ} (x : Fin m) (body : Formula S (3 + m)) (γ : S ^ m) where
  private
    X = fst (lookup x γ)

  bothEx-out : ⟨ γ ⊨ bothEx x body ⟩
             → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ] Σ[ s ∈ S ]
                 ((X ≡ pr (fst u) (fst v)) × ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩) ∥₁
  bothEx-out = PT.rec squash₁ (λ { (s , (s∈ , h)) → PT.rec squash₁
    (λ { (u , (u∈ , h')) → PT.map
      (λ { (v , (v∈ , (e , hb))) → u , v , s , (pr-out (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e , hb) })
      h' })
    h })

  bothEx-in : (u v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst u ∈ fst s ⟩ → ⟨ fst v ∈ fst s ⟩
            → X ≡ pr (fst u) (fst v) → ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩ → ⟨ γ ⊨ bothEx x body ⟩
  bothEx-in u v s s∈ u∈ v∈ e hb =
    ∣ s , (s∈ , ∣ u , (u∈ , ∣ v , (v∈ , (pr-in (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e , hb)) ∣₁) ∣₁) ∣₁

  bothAll-out : ⟨ γ ⊨ bothAll x body ⟩
              → (u v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst u ∈ fst s ⟩ → ⟨ fst v ∈ fst s ⟩
              → X ≡ pr (fst u) (fst v) → ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩
  bothAll-out h u v s s∈ u∈ v∈ e = h s s∈ u u∈ v v∈ (pr-in (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e)

  bothAll-in : ((u v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst u ∈ fst s ⟩ → ⟨ fst v ∈ fst s ⟩
                → X ≡ pr (fst u) (fst v) → ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩)
             → ⟨ γ ⊨ bothAll x body ⟩
  bothAll-in k s s∈ u u∈ v v∈ e = k u v s s∈ u∈ v∈ (pr-out (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e)
```

<!--en-->
## Supplying the container witnesses
<!--zh-->
## 供应容器见证
<!--ja-->
## 容器の証人を与える
<!--/-->

<!--en-->
`fillSnd`{.Agda}, `fillBoth`{.Agda}, `useSnd`{.Agda}, and `useBoth`{.Agda}
construct the internal container automatically from a pair equality, leaving
callers to reason only about its components.
<!--zh-->
`fillSnd`{.Agda}、`fillBoth`{.Agda}、`useSnd`{.Agda} 与 `useBoth`{.Agda} 从有序对等式自动构造内部容器，使调用方只须推理其分量。
<!--ja-->
`fillSnd`{.Agda}、`fillBoth`{.Agda}、`useSnd`{.Agda}、`useBoth`{.Agda} は順序対の等式から内部容器を自動的に構成し、呼び出し側には成分についての推論だけを残す。
<!--/-->

Supplying the junk: a pair at a slot, with its components as
elements, fills any of the four.

```agda
module _ {m : ℕ} (x : Fin m) (γ : S ^ m) (u v : S)
         (e : fst (lookup x γ) ≡ pr (fst u) (fst v)) where
  private
    c = container (lookup x γ) u v e

  fillSnd : (body : Formula S (2 + m)) → ⟨ (v ∷ c .fst ∷ γ) ⊨ body ⟩
          → (ui : Fin m) → fst (lookup ui γ) ≡ fst u → ⟨ γ ⊨ sndEx x ui body ⟩
  fillSnd body hb ui qu = sndEx-in x ui body γ v (c .fst) (c .snd .fst) (c .snd .snd .snd)
    (e ∙ cong (λ w → pr w (fst v)) (sym qu)) hb

  fillBoth : (body : Formula S (3 + m)) → ⟨ (v ∷ u ∷ c .fst ∷ γ) ⊨ body ⟩
           → ⟨ γ ⊨ bothEx x body ⟩
  fillBoth body hb = bothEx-in x body γ u v (c .fst) (c .snd .fst) (c .snd .snd .fst)
    (c .snd .snd .snd) e hb

  useSnd : (body : Formula S (2 + m)) (ui : Fin m) → fst (lookup ui γ) ≡ fst u
         → ⟨ γ ⊨ sndAll x ui body ⟩ → ⟨ (v ∷ c .fst ∷ γ) ⊨ body ⟩
  useSnd body ui qu h = sndAll-out x ui body γ h v (c .fst) (c .snd .fst) (c .snd .snd .snd)
    (e ∙ cong (λ w → pr w (fst v)) (sym qu))

  useBoth : (body : Formula S (3 + m)) → ⟨ γ ⊨ bothAll x body ⟩
          → ⟨ (v ∷ u ∷ c .fst ∷ γ) ⊨ body ⟩
  useBoth body h = bothAll-out x body γ h u v (c .fst) (c .snd .fst) (c .snd .snd .fst)
    (c .snd .snd .snd) e
```

<!--en-->
## Recap
<!--zh-->
## 回顾
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The named slots and finite connective folds organize repeated formula families.
The bounded pair formulas expose one or both components of a coded pair, their
readers recover the component semantics, and the filling lemmas hide the
container witnesses needed when those readers are reused in larger formulas.
<!--zh-->
具名槽位与有穷联结词折叠组织反复出现的公式族。本章的有界配对公式揭示码化有序对的一个或两个分量，相应读式恢复这些分量的语义，而填充引理隐藏了在较大公式中复用这些读式时所需的容器见证。
<!--ja-->
名前付きスロットと有限結合子の畳み込みが、繰り返し現れる論理式族を整理する。有界な対の論理式は符号化された順序対の一方または両方の成分を取り出し、その読み補題が成分の意味を復元する。充填補題は、これらの読みを大きな論理式で再利用するときに必要な容器の証人を隠す。
<!--/-->
