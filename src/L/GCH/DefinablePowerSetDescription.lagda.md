<!--en-->
# A Δ₀ description of the definable power set

The definable subsets of a stage must themselves be recognizable inside `L`. This chapter gives a bounded formula for that collection and proves that its internal reading matches the external definition.
<!--zh-->
# 可定义幂集的 Δ₀ 描述

一个阶段的可定义子集必须也能在 `L` 内部被识别。本章为这一集合给出有界公式，并证明其内部读法与外部定义相符。
<!--ja-->
# 定義可能冪集合の Δ₀ 記述

ある段階の定義可能な部分集合は、`L` の内部でも認識できなければならない。本章ではその集まりを表す有界論理式を与え、内部での読みが外部の定義と一致することを示す。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.DefinablePowerSetDescription {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Model {ℓ} using ( prAtL; container )
open import L.Coding.SatisfactionBridge {ℓ} lem using ( asConst; defSet-Sat )
open import L.Coding.DefinablePowerSet {ℓ} lem using ( envOne )
open import L.Coding.CodeSet {ℓ} lem using ( keyS; key∈AllCodes )
open import L.Coding.UniformSatisfaction {ℓ} lem using ( module Table; val-at )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat )
open import L.Coding.Quantification {ℓ} using
  ( sh; i0; i1; i3; i6; f0; f1; down
  ; sndEx; sndAll; sndEx-out; sndAll-in; fillSnd; useSnd
  ; pr-out; pr-in; sndS )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
open import L.GCH.SatisfactionDescription {ℓ} lem using ( satAt; module SatRead; module Match )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Vec using ( _∷_; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

The formula. `v` is the definable power set of `w`, in the value polarity: every
member of `v` is the set the table `T` cuts from `w` at some arity-one code of
`C`, and every arity-one code of `C` cuts a member of `v` from `w`. The tower is
not needed: the one-entry environment of a member is bounded by the value it is
looked up in.

`e` is the one-entry environment `⁅ (N0, z) ⁆`.

```agda
singleOf : ∀ {j} → Fin j → Fin j → Fin j → Formula S j
singleOf e N0 z = ∀̇∈ (var e) (prAtL i0 (sh 1 N0) (sh 1 z)) ∧̇ ∃̇∈ (var e) (prAtL i0 (sh 1 N0) (sh 1 z))

```

`x` is the set of members of `w` whose one-entry environment lies in `y`.

```agda
definesB : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Formula S j
definesB x w y N0 =
    ∀̇∈ (var x) ((var i0 ∈̇ var (sh 1 w)) ∧̇ ∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1))
  ∧̇ ∀̇∈ (var w) (∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1) ⇒̇ (var i0 ∈̇ var (sh 1 x)))

```

Every member of `v` is cut by some arity-one code: at
`y ∷ s' ∷ e ∷ p ∷ s ∷ c ∷ x ∷ γ`, `x` at `i6`, `y` at `i0`.

```agda
memAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
memAt v w T C N =
  ∀̇∈ (var v) (∃̇∈ (var (sh 1 C)) (sndEx i0 (sh 2 (N f1))
    (∃̇∈ (var (sh 4 T)) (sndEx i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0)))))))
```

Every arity-one code cuts a member of `v`: at
`x ∷ y ∷ s' ∷ e ∷ p ∷ s ∷ c ∷ γ`, `x` at `i0`, `y` at `i1`.

```agda
allAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
allAt v w T C N =
  ∀̇∈ (var C) (sndAll i0 (sh 1 (N f1))
    (∃̇∈ (var (sh 3 T)) (sndEx i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0)))))))



opaque
  defAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
  defAt v w T C N = memAt v w T C N ∧̇ allAt v w T C N

opaque
  unfolding defAt

  Δ₀-defAt : ∀ {m} (v w T C : Fin m) (N : Fin 10 → Fin m) → Δ₀ (defAt v w T C N)
  Δ₀-defAt v w T C N = checkΔ₀ (defAt v w T C N) tt

  defAt-out : ∀ {m} (v w T C : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
            → ⟨ γ ⊨ defAt v w T C N ⟩ → ⟨ γ ⊨ memAt v w T C N ⟩ × ⟨ γ ⊨ allAt v w T C N ⟩
  defAt-out v w T C N γ h = h

  defAt-in : ∀ {m} (v w T C : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m)
           → ⟨ γ ⊨ memAt v w T C N ⟩ → ⟨ γ ⊨ allAt v w T C N ⟩ → ⟨ γ ⊨ defAt v w T C N ⟩
  defAt-in v w T C N γ h1 h2 = h1 , h2
```

The readers: the one-entry environment, the cut, and the two clauses, at
variable environments.

`⁅ (# 0, z) ⁆`, both ways.

```agda
module _ {j : ℕ} (e N0 z : Fin j) (δ : S ^ j) (q0 : fst (lookup N0 δ) ≡ # 0) where
  private
    E = fst (lookup e δ)
    Z = fst (lookup z δ)

  singleOf-out : ⟨ δ ⊨ singleOf e N0 z ⟩ → E ≡ envOne Z
  singleOf-out (hall , hex) = extensionalV (λ y → ⇔toPath (fwd y) (bwd y))
    where
    fwd : (y : V ℓ) → ⟨ y ∈ E ⟩ → ⟨ y ∈ envOne Z ⟩
    fwd y hy = ∣ lift zero , sym (pr-out i0 (sh 1 N0) (sh 1 z) (down (lookup e δ) y hy ∷ δ) (hall (down (lookup e δ) y hy) hy)
                                 ∙ cong (λ a → pr a Z) q0) ∣₁
    bwd : (y : V ℓ) → ⟨ y ∈ envOne Z ⟩ → ⟨ y ∈ E ⟩
    bwd y = PT.rec (snd (y ∈ E))
      (λ { (lift zero , qy) → PT.rec (snd (y ∈ E))
        (λ { (y' , (y'∈ , hy')) →
          subst (λ u → ⟨ u ∈ E ⟩)
            (pr-out i0 (sh 1 N0) (sh 1 z) (y' ∷ δ) hy' ∙ cong (λ a → pr a Z) q0 ∙ qy) y'∈ })
        hex
         ; (lift (suc ()) , _) })

  singleOf-in : E ≡ envOne Z → ⟨ δ ⊨ singleOf e N0 z ⟩
  singleOf-in q =
      (λ y hy → pr-in i0 (sh 1 N0) (sh 1 z) (y ∷ δ)
         (PT.rec (setIsSet (fst y) (pr (fst (lookup N0 δ)) Z))
           (λ { (lift zero , qy) → sym qy ∙ cong (λ a → pr a Z) (sym q0) ; (lift (suc ()) , _) })
           (subst (λ u → ⟨ fst y ∈ u ⟩) q hy)))
    , ∣ yS , ( subst (λ u → ⟨ pr (# 0) Z ∈ u ⟩) (sym q) ∣ lift zero , refl ∣₁
             , pr-in i0 (sh 1 N0) (sh 1 z) (yS ∷ δ) (cong (λ a → pr a Z) (sym q0)) ) ∣₁
    where
    yS : S
    yS = down (lookup e δ) (pr (# 0) Z) (subst (λ u → ⟨ pr (# 0) Z ∈ u ⟩) (sym q) ∣ lift zero , refl ∣₁)
```

The cut, both ways: `x` is exactly the members of `w` whose one-entry
environment lies in `y`.

```agda
Cuts : (X Wv Y : V ℓ) → Type (ℓ-suc ℓ)
Cuts X Wv Y = ((z : S) → ⟨ fst z ∈ X ⟩ → ⟨ fst z ∈ Wv ⟩ × ⟨ envOne (fst z) ∈ Y ⟩)
            × ((z : S) → ⟨ fst z ∈ Wv ⟩ → ⟨ envOne (fst z) ∈ Y ⟩ → ⟨ fst z ∈ X ⟩)

module _ {j : ℕ} (x w y N0 : Fin j) (δ : S ^ j) (q0 : fst (lookup N0 δ) ≡ # 0) where
  private
    X = fst (lookup x δ)
    Wv = fst (lookup w δ)
    Y = fst (lookup y δ)
    YS = lookup y δ

    one-out : (z : S) → ⟨ (z ∷ δ) ⊨ ∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1) ⟩ → ⟨ envOne (fst z) ∈ Y ⟩
    one-out z = PT.rec (snd (envOne (fst z) ∈ Y))
      (λ { (e , (e∈ , he)) → subst (λ u → ⟨ u ∈ Y ⟩) (singleOf-out i0 (sh 2 N0) i1 (e ∷ z ∷ δ) q0 he) e∈ })

    one-in : (z : S) → ⟨ envOne (fst z) ∈ Y ⟩ → ⟨ (z ∷ δ) ⊨ ∃̇∈ (var (sh 1 y)) (singleOf i0 (sh 2 N0) i1) ⟩
    one-in z h = ∣ down YS (envOne (fst z)) h , (h , singleOf-in i0 (sh 2 N0) i1 (down YS (envOne (fst z)) h ∷ z ∷ δ) q0 refl) ∣₁

  definesB-out : ⟨ δ ⊨ definesB x w y N0 ⟩ → Cuts X Wv Y
  definesB-out (h1 , h2) = (λ z hz → h1 z hz .fst , one-out z (h1 z hz .snd)) , (λ z hw he → h2 z hw (one-in z he))

  definesB-in : Cuts X Wv Y → ⟨ δ ⊨ definesB x w y N0 ⟩
  definesB-in (o , i) = (λ z hz → o z hz .fst , one-in z (o z hz .snd)) , (λ z hw he → i z hw (one-out z he))
```

The two clauses.

```agda
```

<!--en-->
## Reading the bounded subset clauses

The component formulas identify singleton environments, the formula that defines a subset, and membership in that subset. Their read lemmas reduce each syntactic clause to the intended statement about the carrier and its satisfaction table.
<!--zh-->
## 读取有界子集的诸子句

各分量公式分别识别单元素环境、定义子集的公式，以及该子集的隶属关系。相应读引理把每个语法子句化为关于载体及其满足关系表的预期陈述。
<!--ja-->
## 有界部分集合の各節を読む

各成分の論理式は、一要素環境、部分集合を定義する論理式、その部分集合への所属を特定する。読み補題により、各構文的な節は台とその充足関係表についての意図した主張へ還元される。
<!--/-->

```agda
module Read {m : ℕ} (v w T C : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Vv = fst (lookup v γ)
    Wv = fst (lookup w γ)
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    N1v = fst (lookup (N f1) γ)
```

A member of `v` is cut by an arity-one code with an entry.

```agda
  mem-out : ⟨ γ ⊨ memAt v w T C N ⟩ → (x : S) → ⟨ fst x ∈ Vv ⟩
          → ∥ Σ[ c ∈ S ] Σ[ p ∈ S ] Σ[ y ∈ S ]
              (⟨ fst c ∈ Cv ⟩ × ((fst c ≡ pr (# 1) (fst p)) × (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × Cuts (fst x) Wv (fst y)))) ∥₁
  mem-out h x x∈ = PT.rec squash₁
    (λ { (c , (c∈ , hc)) → PT.rec squash₁
      (λ { (p , s , (ec , he)) → PT.rec squash₁
        (λ { (e , (e∈ , hy)) → PT.map
          (λ { (y , s' , (ee , hd)) →
            c , p , y , ( c∈ , ( ec ∙ cong (λ a → pr a (fst p)) (tg f1)
                        , ( subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈
                          , definesB-out i6 (sh 7 w) i0 (sh 7 (N f0)) (y ∷ s' ∷ e ∷ p ∷ s ∷ c ∷ x ∷ γ) (tg f0) hd ) ) ) })
          (sndEx-out i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0))) (e ∷ p ∷ s ∷ c ∷ x ∷ γ) hy) })
        he })
      (sndEx-out i0 (sh 2 (N f1)) (∃̇∈ (var (sh 4 T)) (sndEx i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0))))) (c ∷ x ∷ γ) hc) })
    (h x x∈)

  mem-in : ((x : S) → ⟨ fst x ∈ Vv ⟩
            → ∥ Σ[ c ∈ S ] Σ[ p ∈ S ] Σ[ y ∈ S ]
                (⟨ fst c ∈ Cv ⟩ × ((fst c ≡ pr (# 1) (fst p)) × (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × Cuts (fst x) Wv (fst y)))) ∥₁)
         → ⟨ γ ⊨ memAt v w T C N ⟩
  mem-in g x x∈ = PT.map
    (λ { (c , p , y , (c∈ , (ec , (e∈ , cuts)))) →
      let ec' : fst c ≡ pr N1v (fst p)
          ec' = ec ∙ cong (λ a → pr a (fst p)) (sym (tg f1))
          δ4 = p ∷ container c (lookup (N f1) γ) p ec' .fst ∷ c ∷ x ∷ γ
          eS = down (lookup T γ) (pr (fst c) (fst y)) e∈
          δ7 = y ∷ container eS c y refl .fst ∷ eS ∷ δ4
      in c , ( c∈ , fillSnd i0 (c ∷ x ∷ γ) (lookup (N f1) γ) p ec'
                 (∃̇∈ (var (sh 4 T)) (sndEx i0 i3 (definesB i6 (sh 7 w) i0 (sh 7 (N f0)))))
                 ∣ eS , ( e∈ , fillSnd i0 (eS ∷ δ4) c y refl (definesB i6 (sh 7 w) i0 (sh 7 (N f0)))
                              (definesB-in i6 (sh 7 w) i0 (sh 7 (N f0)) δ7 (tg f0) cuts) i3 refl ) ∣₁
                 (sh 2 (N f1)) refl ) })
    (g x x∈)
```

An arity-one code has an entry and cuts a member of `v`.

```agda
  all-out : ⟨ γ ⊨ allAt v w T C N ⟩ → (c p : S) → ⟨ fst c ∈ Cv ⟩ → fst c ≡ pr (# 1) (fst p)
          → ∥ Σ[ y ∈ S ] Σ[ x ∈ S ] (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × (⟨ fst x ∈ Vv ⟩ × Cuts (fst x) Wv (fst y))) ∥₁
  all-out h c p c∈ ec = PT.rec squash₁
    (λ { (e , (e∈ , hy)) → PT.rec squash₁
      (λ { (y , s' , (ee , hx)) → PT.map
        (λ { (x , (x∈ , hd)) →
          y , x , ( subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈
                  , ( x∈ , definesB-out i0 (sh 7 w) i1 (sh 7 (N f0)) (x ∷ y ∷ s' ∷ e ∷ δ3) (tg f0) hd ) ) })
        hx })
      (sndEx-out i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0)))) (e ∷ δ3) hy) })
    (useSnd i0 (c ∷ γ) (lookup (N f1) γ) p ec'
      (∃̇∈ (var (sh 3 T)) (sndEx i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0))))))
      (sh 1 (N f1)) refl (h c c∈))
    where
    ec' : fst c ≡ pr N1v (fst p)
    ec' = ec ∙ cong (λ a → pr a (fst p)) (sym (tg f1))
    δ3 : S ^ (3 + m)
    δ3 = p ∷ container c (lookup (N f1) γ) p ec' .fst ∷ c ∷ γ

  all-in : ((c p : S) → ⟨ fst c ∈ Cv ⟩ → fst c ≡ pr (# 1) (fst p)
            → ∥ Σ[ y ∈ S ] Σ[ x ∈ S ] (⟨ pr (fst c) (fst y) ∈ Tv ⟩ × (⟨ fst x ∈ Vv ⟩ × Cuts (fst x) Wv (fst y))) ∥₁)
         → ⟨ γ ⊨ allAt v w T C N ⟩
  all-in g c c∈ = sndAll-in' (λ p s s∈ p∈ ec →
    PT.map (λ { (y , x , (e∈ , (x∈ , cuts))) →
      let eS = down (lookup T γ) (pr (fst c) (fst y)) e∈
          δ6 = y ∷ container eS c y refl .fst ∷ eS ∷ p ∷ s ∷ c ∷ γ
      in eS , ( e∈ , fillSnd i0 (eS ∷ p ∷ s ∷ c ∷ γ) c y refl (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0))))
                       ∣ x , (x∈ , definesB-in i0 (sh 7 w) i1 (sh 7 (N f0)) (x ∷ δ6) (tg f0) cuts) ∣₁ i3 refl ) })
      (g c p c∈ (ec ∙ cong (λ a → pr a (fst p)) (tg f1))))
    where
    sndAll-in' = sndAll-in i0 (sh 1 (N f1))
      (∃̇∈ (var (sh 3 T)) (sndEx i0 i3 (∃̇∈ (var (sh 6 v)) (definesB i0 (sh 7 w) i1 (sh 7 (N f0)))))) (c ∷ γ)
```

The two theorems. With `T`, `C` read by `satAt`: a reading of `defAt` at
`(v, w, T, C)` makes `v` the definable power set of `w`, and the definable power
set satisfies `defAt`.

```agda
```

<!--en-->
## The definable-power-set formula

The complete formula says that every member of the output is selected by some coded formula and parameter environment over the input, and conversely every such selected subset occurs in the output. The two directions prove exact agreement with the definable power set.
<!--zh-->
## 可定义幂集公式

完整公式说，输出的每个成员都由输入上的某条编码公式与参数环境选出；反过来，每个如此选出的子集都出现在输出中。两个方向共同证明它与可定义幂集准确一致。
<!--ja-->
## 定義可能冪集合の論理式

完全な論理式は、出力の各要素が入力上の符号化された論理式とパラメータ環境によって選ばれ、逆にそのように選ばれた各部分集合が出力に現れることを述べる。両方向から定義可能冪集合との正確な一致が得られる。
<!--/-->

```agda
module DefRead {m : ℕ} (v w T C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N) (hs : ⟨ γ ⊨ satAt T w C E N ⟩) where
  open Alphabet W
  open Match W
  private
    module SR = SatRead T w C E N γ W qw tg hs
    module RD = Read v w T C N γ tg
    module DA = DefOf (fst W)
    Vv = fst (lookup v γ)
    Wv = fst (lookup w γ)
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)

    toS : Formula Ab 1 → Formula S 1
    toS = mapFo (asConst W)
```

The value at the key of `ψ`, from an entry.

```agda
    valOf : (ψ : Formula Ab 1) (c y : S) → fst c ≡ fst (keyS W ψ) → ⟨ pr (fst c) (fst y) ∈ Tv ⟩
          → fst y ≡ fst (Sat W (toS ψ))
    valOf ψ c y qc h = SR.T-out c y h .snd ∙ cong fst (val-at W W ψ c (SR.T-out c y h .fst) qc)
```

A cut by the value at `ψ` is the definable subset of `ψ`.

```agda
    cut≡ : (ψ : Formula Ab 1) (x : S) → Cuts (fst x) Wv (fst (Sat W (toS ψ))) → DA.defSet ψ ≡ fst x
    cut≡ ψ x (o , i) = extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
      where
      fwd : (z : V ℓ) → ⟨ z ∈ DA.defSet ψ ⟩ → ⟨ z ∈ fst x ⟩
      fwd z = PT.rec (snd (z ∈ fst x))
        (λ { ((q , hq) , e) →
          i (down W z (subst (λ u → ⟨ u ∈ fst W ⟩) e (ι∈ q)))
            (subst (λ u → ⟨ z ∈ u ⟩) (sym qw) (subst (λ u → ⟨ u ∈ fst W ⟩) e (ι∈ q)))
            (subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) e
              (subst ⟨_⟩ (defSet-Sat W ψ q) ∣ (q , hq) , refl ∣₁)) })
      bwd : (z : V ℓ) → ⟨ z ∈ fst x ⟩ → ⟨ z ∈ DA.defSet ψ ⟩
      bwd z hz =
        let zS = down x z hz
            zW = subst (λ u → ⟨ z ∈ u ⟩) qw (o zS hz .fst)
            fib = ∈-asFiber {a = z} {b = fst W} zW
        in subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
             (subst ⟨_⟩ (sym (defSet-Sat W ψ (fib .fst)))
               (subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) (sym (fib .snd)) (o zS hz .snd)))

    cuts-of : (ψ : Formula Ab 1) (x : S) → DA.defSet ψ ≡ fst x → Cuts (fst x) Wv (fst (Sat W (toS ψ)))
    cuts-of ψ x e = o , i
      where
      o : (z : S) → ⟨ fst z ∈ fst x ⟩ → ⟨ fst z ∈ Wv ⟩ × ⟨ envOne (fst z) ∈ fst (Sat W (toS ψ)) ⟩
      o z hz = PT.rec (isProp× (snd (fst z ∈ Wv)) (snd (envOne (fst z) ∈ fst (Sat W (toS ψ)))))
        (λ { ((q , hq) , eq) →
            subst (λ u → ⟨ fst z ∈ u ⟩) (sym qw) (subst (λ u → ⟨ u ∈ fst W ⟩) eq (ι∈ q))
          , subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) eq (subst ⟨_⟩ (defSet-Sat W ψ q) ∣ (q , hq) , refl ∣₁) })
        (subst (λ u → ⟨ fst z ∈ u ⟩) (sym e) hz)
      i : (z : S) → ⟨ fst z ∈ Wv ⟩ → ⟨ envOne (fst z) ∈ fst (Sat W (toS ψ)) ⟩ → ⟨ fst z ∈ fst x ⟩
      i z hw he =
        let fib = ∈-asFiber {a = fst z} {b = fst W} (subst (λ u → ⟨ fst z ∈ u ⟩) qw hw)
        in subst (λ u → ⟨ fst z ∈ u ⟩) e
             (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
               (subst ⟨_⟩ (sym (defSet-Sat W ψ (fib .fst)))
                 (subst (λ u → ⟨ envOne u ∈ fst (Sat W (toS ψ)) ⟩) (sym (fib .snd)) he)))

  def-sound : ⟨ γ ⊨ defAt v w T C N ⟩ → Vv ≡ 𝒟ₒ (fst W)
  def-sound hd = extensionalV (λ x → ⇔toPath (fwd x) (bwd x))
    where
    hm = defAt-out v w T C N γ hd .fst
    ha = defAt-out v w T C N γ hd .snd

    fwd : (x : V ℓ) → ⟨ x ∈ Vv ⟩ → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
    fwd x hx = PT.rec (snd (x ∈ 𝒟ₒ (fst W)))
      (λ { (c , p , y , (c∈ , (ec , (e∈ , cuts)))) → PT.rec (snd (x ∈ 𝒟ₒ (fst W)))
        (λ { (ψ , qp) →
          𝒟ₒ-intro (fst W) x ∣ ψ , cut≡ ψ xS
            (subst (λ u → Cuts x Wv u) (valOf ψ c y (ec ∙ cong (pr (# 1)) qp) e∈) cuts) ∣₁ })
        (decodeAll c (SR.C-out c c∈) 1 (fst p) ec) })
      (RD.mem-out hm xS hx)
      where
      xS : S
      xS = down (lookup v γ) x hx

    bwd : (x : V ℓ) → ⟨ x ∈ 𝒟ₒ (fst W) ⟩ → ⟨ x ∈ Vv ⟩
    bwd x hx = PT.rec (snd (x ∈ Vv))
      (λ { (ψ , e) → PT.rec (snd (x ∈ Vv))
        (λ { (y , x' , (e∈ , (x'∈ , cuts))) →
          subst (λ u → ⟨ u ∈ Vv ⟩)
            (sym (cut≡ ψ x' (subst (λ u → Cuts (fst x') Wv u) (valOf ψ (keyS W ψ) y refl e∈) cuts)) ∙ e)
            x'∈ })
        (RD.all-out ha (keyS W ψ) (sndS (keyS W ψ) (# 1) (cd ψ) refl) (SR.C-in (keyS W ψ) (key∈AllCodes W ψ)) refl) })
      (𝒟ₒ-inv (fst W) x hx)

  def-complete : Vv ≡ 𝒟ₒ (fst W) → ⟨ γ ⊨ defAt v w T C N ⟩
  def-complete qv = defAt-in v w T C N γ mem all
    where
```

The entry at the key of `ψ`, and its value.

```agda
    entry : (ψ : Formula Ab 1) → Σ[ y ∈ S ] (⟨ pr (fst (keyS W ψ)) (fst y) ∈ Tv ⟩ × (fst y ≡ fst (Sat W (toS ψ))))
    entry ψ = Table.val W W (keyS W ψ) (key∈AllCodes W ψ)
            , ( SR.T-in (keyS W ψ) (key∈AllCodes W ψ)
              , cong fst (val-at W W ψ (keyS W ψ) (key∈AllCodes W ψ) refl) )

    mem : ⟨ γ ⊨ memAt v w T C N ⟩
    mem = RD.mem-in (λ x x∈ → PT.map
      (λ { (ψ , e) →
        keyS W ψ , sndS (keyS W ψ) (# 1) (cd ψ) refl , entry ψ .fst
        , ( SR.C-in (keyS W ψ) (key∈AllCodes W ψ)
          , ( refl
            , ( entry ψ .snd .fst
              , subst (λ u → Cuts (fst x) Wv u) (sym (entry ψ .snd .snd)) (cuts-of ψ x e) ) ) ) })
      (𝒟ₒ-inv (fst W) (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) qv x∈)))

    all : ⟨ γ ⊨ allAt v w T C N ⟩
    all = RD.all-in (λ c p c∈ ec → PT.map
      (λ { (ψ , qp) →
        let qc : fst c ≡ fst (keyS W ψ)
            qc = ec ∙ cong (pr (# 1)) qp
            xS : S
            xS = down (lookup v γ) (DA.defSet ψ)
                   (subst (λ u → ⟨ DA.defSet ψ ∈ u ⟩) (sym qv) (𝒟ₒ-intro (fst W) (DA.defSet ψ) ∣ ψ , refl ∣₁))
        in entry ψ .fst , xS
         , ( subst (λ u → ⟨ pr u (fst (entry ψ .fst)) ∈ Tv ⟩) (sym qc) (entry ψ .snd .fst)
           , ( subst (λ u → ⟨ DA.defSet ψ ∈ u ⟩) (sym qv) (𝒟ₒ-intro (fst W) (DA.defSet ψ) ∣ ψ , refl ∣₁)
             , subst (λ u → Cuts (DA.defSet ψ) Wv u) (sym (entry ψ .snd .snd)) (cuts-of ψ xS refl) ) ) })
      (decodeAll c (SR.C-out c c∈) 1 (fst p) ec))
```

The two theorems, at the seal.

```agda
def-sound : ∀ {m} (v w T C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
          → fst (lookup w γ) ≡ fst W → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
          → ⟨ γ ⊨ defAt v w T C N ⟩ → fst (lookup v γ) ≡ 𝒟ₒ (fst W)
def-sound v w T C E N γ W qw tg hs = DefRead.def-sound v w T C E N γ W qw tg hs

def-complete : ∀ {m} (v w T C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
             → fst (lookup w γ) ≡ fst W → Tags γ N → ⟨ γ ⊨ satAt T w C E N ⟩
             → fst (lookup v γ) ≡ 𝒟ₒ (fst W) → ⟨ γ ⊨ defAt v w T C N ⟩
def-complete v w T C E N γ W qw tg hs = DefRead.def-complete v w T C E N γ W qw tg hs
```
