# The cardinal chapter's theorem side

<!--en-->
The cardinal chapter's definitional layer fixed equinumerosity as the
existence of a bijection, and the counting side delivered Devlin 5.4's upper
half in the honest injection shape. This chapter pays the two obligations
that definition left standing. Cantor-Schroeder-Bernstein upgrades two
injections, one each way, to the bijection the predicate is; that is the
equality upgrade the scope gate named when it chose bijections over
injections-both-ways. Cantor's theorem then supplies the one genuinely
surjection-flavored fact of the cardinal arithmetic, no surjection onto a
set's power set, at the delivered carrier. And the chapter closes the
5.4 equality half at the hull: the lower bound, `X ⊆ M` and `ω ⊆ M`, with
the numerals in the hull as the new content, and the bijection form,
`HostEq M β` from the two injections, which is exactly the composition the
counting side's closing note promised.
<!--zh-->
基数章的定义层把等势钉为「存在双射」，计数侧以诚实的单射形状交付了 Devlin 5.4 的上半。本章偿付那条定义遗留的两笔义务。Cantor-Schroeder-Bernstein 把各走一趟的两条单射升级为谓词所取的双射；这正是作用域门当初在双射与「两边各有单射」之间选择时所点名的等势升级。Cantor 定理随即在已交付载体上供给基数算术中唯一名副其实的满射型事实：没有满射落到一个集合的幂集上。本章还在外壳处闭合 5.4 的等式半侧：下界 `X ⊆ M` 与 `ω ⊆ M`，其中数码落进外壳是全新内容；以及双射形态，由两条单射合成 `HostEq M β`，恰是计数侧收尾注记所许诺的复合。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lem→impredicativity; lowerLEM )
open import Base.Impredicativity using ( module Impredicativity )

module L.Cardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ∃̇∈; ∀̇∈; ⊥̇ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( fiber; member; ↪-inj )
open import V.Model {ℓ} using ( module Power; ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( isTransV; IsOrd; Lset; layer-trans; Lset-layer )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.CardinalPredicates {ℓ} using ( HostBij; HostEq )
import L.CardinalCount {ℓ} lem as CC

open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; extensionality; _⊆_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( ω; #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )

module Pow = Power (Impredicativity.hPropSmallness (lem→impredicativity lem))
```

<!--en-->
## Cantor-Schroeder-Bernstein
<!--zh-->
## Cantor-Schroeder-Bernstein
<!--/-->

<!--en-->
The classical proof runs on the index level. The "bad" elements of `a` are
those reachable by a finite alternating preimage chain starting outside the
image of `g`; the bijection sends a bad element through `f` and a good one
back through `g⁻¹`. The chain is a small predicate family `Cₙ`, and the one
structural fact the proof needs is that the map `x ↦ g (f x)` closes the
bad set. Excluded middle enters twice, to decide the bad set and to extract
`g⁻¹` from the truncated image statement, each at the level `ℓ` through the
downward transfer.
<!--zh-->
经典证明跑在索引层。`a` 中的「坏」元素，是那些能沿一条有穷的交替原像链、从 `g` 的像之外出发够到的元素；双射把坏元素经 `f` 送出、好元素经 `g⁻¹` 送回。链是小谓词族 `Cₙ`，证明唯一需要的结构事实是映射 `x ↦ g (f x)` 封闭坏集。排中律两次进场，一次判定坏集，一次从截断的像陈述里提取 `g⁻¹`，都在 `ℓ` 层经向下传递完成。
<!--/-->

```agda
module CSB (a b : S) (f : ⟪ a ⟫ → ⟪ b ⟫) (fi : (x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
           (g : ⟪ b ⟫ → ⟪ a ⟫) (gi : (x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y) where

  isSetA : isSet (⟪ a ⟫)
  isSetA = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

  imG : ⟪ a ⟫ → hProp ℓ
  imG x = (∥ Σ[ y ∈ ⟪ b ⟫ ] (g y ≡ x) ∥₁ , squash₁)

  C₀ : ⟪ a ⟫ → hProp ℓ
  C₀ x = ((⟨ imG x ⟩ → Empty.⊥) , isPropΠ (λ _ → isProp⊥))

  C₊ : (⟪ a ⟫ → hProp ℓ) → ⟪ a ⟫ → hProp ℓ
  C₊ C x = (∥ Σ[ y ∈ ⟪ b ⟫ ] Σ[ z ∈ ⟪ a ⟫ ] ((g y ≡ x) × ((f z ≡ y) × ⟨ C z ⟩)) ∥₁ , squash₁)

  Cₙ : ℕ → ⟪ a ⟫ → hProp ℓ
  Cₙ zero = C₀
  Cₙ (suc n) = C₊ (Cₙ n)

  C : ⟪ a ⟫ → hProp ℓ
  C x = (∥ Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ ∥₁ , squash₁)

  c-in : {x : ⟪ a ⟫} {n : ℕ} → ⟨ Cₙ n x ⟩ → ⟨ C x ⟩
  c-in {x} {n} h = ∣ n , h ∣₁

  gf-closed : {x : ⟪ a ⟫} → ⟨ C x ⟩ → ⟨ C (g (f x)) ⟩
  gf-closed {x} = PT.rec (snd (C (g (f x)))) go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ⟨ C (g (f x)) ⟩
    go (n , cx) = c-in {x = g (f x)} {n = suc n} ∣ f x , x , (refl , (refl , cx)) ∣₁

  C-view : {x : ⟪ a ⟫} → ⟨ C x ⟩
         → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ ⟪ a ⟫ ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
  C-view {x} = PT.rec squash₁ go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ ⟪ a ⟫ ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
    go (zero , c0) = ∣ inl c0 ∣₁
    go (suc n , cs) = PT.map inr (PT.map (λ { (y , z , gy , fz , cz) →
        z , ((cong g fz ∙ gy) , c-in {x = z} {n = n} cz) }) cs)

  notC→imG : {x : ⟪ a ⟫} → (⟨ C x ⟩ → Empty.⊥) → ⟨ imG x ⟩
  notC→imG {x} nC = Sum.rec {A = ⟨ imG x ⟩} {B = ⟨ imG x ⟩ → Empty.⊥} {C = ⟨ imG x ⟩}
    (λ h → h) (λ nC₀ → Empty.rec (nC (c-in {n = zero} nC₀)))
    (lowerLEM lem (imG x))

  fiberG-prop : (x : ⟪ a ⟫) → isProp (Σ[ y ∈ ⟪ b ⟫ ] (g y ≡ x))
  fiberG-prop x (y , p) (y' , p') = Σ≡Prop {A = ⟪ b ⟫} {B = λ y → g y ≡ x}
    (λ y → isSetA (g y) x) (gi y y' (p ∙ sym p'))

  fiberG : (x : ⟪ a ⟫) → ⟨ imG x ⟩ → Σ[ y ∈ ⟪ b ⟫ ] (g y ≡ x)
  fiberG x = PT.rec (fiberG-prop x) (λ w → w)

  ginv : {x : ⟪ a ⟫} → (⟨ C x ⟩ → Empty.⊥) → ⟪ b ⟫
  ginv {x} nC = fiberG x (notC→imG nC) .fst

  ginv-spec : {x : ⟪ a ⟫} (nC : ⟨ C x ⟩ → Empty.⊥) → g (ginv nC) ≡ x
  ginv-spec {x} nC = fiberG x (notC→imG nC) .snd

  h : (x : ⟪ a ⟫) → ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) → ⟪ b ⟫
  h x (inl _) = f x
  h x (inr nC) = ginv nC

  h-inj : (x x' : ⟪ a ⟫) (dx : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) (dx' : ⟨ C x' ⟩ ⊎ (⟨ C x' ⟩ → Empty.⊥))
        → h x dx ≡ h x' dx' → x ≡ x'
  h-inj x x' (inl cx) (inl cx') e = fi x x' e
  h-inj x x' (inl cx) (inr nCx') e =
    Empty.rec (nCx' (subst (λ w → ⟨ C w ⟩) (cong g e ∙ ginv-spec nCx') (gf-closed {x = x} cx)))
  h-inj x x' (inr nCx) (inl cx') e =
    Empty.rec (nCx (subst (λ w → ⟨ C w ⟩) (sym (cong g e) ∙ ginv-spec nCx) (gf-closed {x = x'} cx')))
  h-inj x x' (inr nCx) (inr nCx') e = sym (ginv-spec nCx) ∙ cong g e ∙ ginv-spec nCx'

  h-surj : (y : ⟪ b ⟫) (d : ⟨ C (g y) ⟩ ⊎ (⟨ C (g y) ⟩ → Empty.⊥))
         → ∥ Σ[ x ∈ ⟪ a ⟫ ] Σ[ dx ∈ ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) ] (h x dx ≡ y) ∥₁
  h-surj y (inr nCgy) = ∣ g y , inr nCgy , gi (ginv nCgy) y (ginv-spec nCgy) ∣₁
  h-surj y (inl cgy) = PT.rec squash₁
    (λ { (inl c0) → Empty.rec (c0 ∣ y , refl ∣₁) ; (inr (z , gfy , cz)) → ∣ z , inl cz , gi (f z) y gfy ∣₁ })
    (C-view {x = g y} cgy)

  h-cons : (x : ⟪ a ⟫) (dx dx' : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) → h x dx ≡ h x dx'
  h-cons x (inl cx) (inl cx') = refl
  h-cons x (inl cx) (inr nCx') = Empty.rec (nCx' cx)
  h-cons x (inr nCx) (inl cx) = Empty.rec (nCx cx)
  h-cons x (inr nCx) (inr nCx') = cong fst (fiberG-prop x (fiberG x (notC→imG nCx)) (fiberG x (notC→imG nCx')))

  ĥ : ⟪ a ⟫ → ⟪ b ⟫
  ĥ x = h x (lowerLEM lem (C x))

  ĥ-inj : (x x' : ⟪ a ⟫) → ĥ x ≡ ĥ x' → x ≡ x'
  ĥ-inj x x' e = h-inj x x' (lowerLEM lem (C x)) (lowerLEM lem (C x')) e

  ĥ-surj : (y : ⟪ b ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (ĥ x ≡ y) ∥₁
  ĥ-surj y = PT.map (λ { (x , dx , e) → x , sym (h-cons x dx (lowerLEM lem (C x))) ∙ e })
    (h-surj y (lowerLEM lem (C (g y))))

csb : (a b : S) (f : ⟪ a ⟫ → ⟪ b ⟫) → ((x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
    → (g : ⟪ b ⟫ → ⟪ a ⟫) → ((x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y)
    → Σ[ h ∈ (⟪ a ⟫ → ⟪ b ⟫) ] (((x y : ⟪ a ⟫) → h x ≡ h y → x ≡ y) × ((y : ⟪ b ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (h x ≡ y) ∥₁))
csb a b f fi g gi = h , (h-inj , h-surj)
  where
  module M = CSB a b f fi g gi
  h : ⟪ a ⟫ → ⟪ b ⟫
  h = M.ĥ
  h-inj = M.ĥ-inj
  h-surj = M.ĥ-surj
```

<!--en-->
## The bijection as a set of pairs
<!--zh-->
## 以对之集呈现的双射
<!--/-->

<!--en-->
The index-level bijection upgrades to the carrier-level predicate: the graph
of `h` as a set of Kuratowski pairs, with the five clauses read off the
injectivity and surjectivity of `h` and the pair-injectivity of the coding
chapter. This is the exact shape the scope gate chose for equinumerosity, and
it is what makes the CSB obligation payable once, centrally, instead of by
every consumer.
<!--zh-->
索引层双射升级到载体层的谓词：把 `h` 的图像写成 Kuratowski 对之集，五条子句由 `h` 的单射性与满射性、以及编码章的对单射性直接读出。这正是作用域门为等势选定的形状，也是让 CSB 义务得以一次性集中偿付、而非由每个消费方各自偿付的原因。
<!--/-->

```agda
module Graph (a b : S) (f : ⟪ a ⟫ → ⟪ b ⟫) (fi : (x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
             (g : ⟪ b ⟫ → ⟪ a ⟫) (gi : (x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y) where

  module M = CSB a b f fi g gi

  F : S
  F = sett (⟪ a ⟫) (λ x → pr (⟪ a ⟫↪ x) (⟪ b ⟫↪ (M.ĥ x)))

  pairs-cl : (p : S) → ⟨ p ∈ˢ F ⟩ → ∥ Σ[ x ∈ S ] (∥ Σ[ y ∈ S ] (p ≡ pr x y) ∥₁) ∥₁
  pairs-cl p p∈F = PT.map (λ { (x , e) → ⟪ a ⟫↪ x , ∣ ⟪ b ⟫↪ (M.ĥ x) , sym e ∣₁ }) p∈F

  sv-cl : (p : S) → ⟨ p ∈ˢ F ⟩ → (x y y' : S) → p ≡ pr x y → p ≡ pr x y' → y ≡ y'
  sv-cl p p∈F x y y' pxy pxy' = PT.rec (setIsSet y y') go p∈F
    where
    go : Σ[ x₀ ∈ ⟪ a ⟫ ] (pr (⟪ a ⟫↪ x₀) (⟪ b ⟫↪ (M.ĥ x₀)) ≡ p) → y ≡ y'
    go (x₀ , e) = sym (pr-inj (e ∙ pxy) .snd) ∙ pr-inj (e ∙ pxy') .snd

  total-cl : (x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ p ∈ S ] (⟨ p ∈ˢ F ⟩ × ∥ Σ[ y ∈ S ] (p ≡ pr x y) ∥₁) ∥₁
  total-cl x x∈a = ∣ p , (∣ m , p∈F ∣₁ , ∣ y , refl ∣₁) ∣₁
    where
    m = fiber a x∈a .fst
    y = ⟪ b ⟫↪ (M.ĥ m)
    p = pr x y
    p∈F = cong₂ pr (fiber a x∈a .snd) refl

  inj-cl : (p : S) → ⟨ p ∈ˢ F ⟩ → (q : S) → ⟨ q ∈ˢ F ⟩
         → (x x' y : S) → p ≡ pr x y → q ≡ pr x' y → x ≡ x'
  inj-cl p p∈F q q∈F x x' y pxy qxy =
    PT.rec {A = Σ[ x₀ ∈ ⟪ a ⟫ ] (pr (⟪ a ⟫↪ x₀) (⟪ b ⟫↪ (M.ĥ x₀)) ≡ p)}
      (setIsSet x x') go₀ p∈F
    where
    go₀ : Σ[ x₀ ∈ ⟪ a ⟫ ] (pr (⟪ a ⟫↪ x₀) (⟪ b ⟫↪ (M.ĥ x₀)) ≡ p) → x ≡ x'
    go₀ (x₀ , e₀) = PT.rec {A = Σ[ x₁ ∈ ⟪ a ⟫ ] (pr (⟪ a ⟫↪ x₁) (⟪ b ⟫↪ (M.ĥ x₁)) ≡ q)}
        (setIsSet x x') (go₁ x₀ e₀) q∈F
      where
      go₁ : (x₀ : ⟪ a ⟫) → pr (⟪ a ⟫↪ x₀) (⟪ b ⟫↪ (M.ĥ x₀)) ≡ p
          → Σ[ x₁ ∈ ⟪ a ⟫ ] (pr (⟪ a ⟫↪ x₁) (⟪ b ⟫↪ (M.ĥ x₁)) ≡ q) → x ≡ x'
      go₁ x₀ e₀ (x₁ , e₁) = c2
        where
        q0 : ⟪ a ⟫↪ x₀ ≡ x
        q0 = pr-inj {a = ⟪ a ⟫↪ x₀} {b = ⟪ b ⟫↪ (M.ĥ x₀)} {c = x} {d = y} (e₀ ∙ pxy) .fst
        q1 : ⟪ a ⟫↪ x₁ ≡ x'
        q1 = pr-inj {a = ⟪ a ⟫↪ x₁} {b = ⟪ b ⟫↪ (M.ĥ x₁)} {c = x'} {d = y} (e₁ ∙ qxy) .fst
        r0 : ⟪ b ⟫↪ (M.ĥ x₀) ≡ y
        r0 = pr-inj {a = ⟪ a ⟫↪ x₀} {b = ⟪ b ⟫↪ (M.ĥ x₀)} {c = x} {d = y} (e₀ ∙ pxy) .snd
        r1 : ⟪ b ⟫↪ (M.ĥ x₁) ≡ y
        r1 = pr-inj {a = ⟪ a ⟫↪ x₁} {b = ⟪ b ⟫↪ (M.ĥ x₁)} {c = x'} {d = y} (e₁ ∙ qxy) .snd
        xx : x₀ ≡ x₁
        xx = M.ĥ-inj x₀ x₁ (↪-inj {a = b} (r0 ∙ sym r1))
        c2 : x ≡ x'
        c2 = sym q0 ∙ (cong (⟪ a ⟫↪) xx ∙ q1)

  surj-cl : (y : S) → ⟨ y ∈ˢ b ⟩ → ∥ Σ[ p ∈ S ] (⟨ p ∈ˢ F ⟩ × ∥ Σ[ x ∈ S ] (p ≡ pr x y) ∥₁) ∥₁
  surj-cl y y∈b = go (fiber b y∈b)
    where
    go : Σ[ m ∈ ⟪ b ⟫ ] (⟪ b ⟫↪ m ≡ y) → ∥ Σ[ p ∈ S ] (⟨ p ∈ˢ F ⟩ × ∥ Σ[ x ∈ S ] (p ≡ pr x y) ∥₁) ∥₁
    go (m , e) = PT.map (λ { (x₀ , hx₀≡m) →
        pr (⟪ a ⟫↪ x₀) y ,
        (∣ x₀ , cong₂ pr refl (cong (⟪ b ⟫↪) hx₀≡m ∙ e) ∣₁ ,
         ∣ ⟪ a ⟫↪ x₀ , refl ∣₁) }) (M.ĥ-surj m)

  hostBij : HostBij F a b
  hostBij = pairs-cl , sv-cl , total-cl , inj-cl , surj-cl

csb-eq : (a b : S) (f : ⟪ a ⟫ → ⟪ b ⟫) → ((x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
       → (g : ⟪ b ⟫ → ⟪ a ⟫) → ((x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y)
       → HostEq a b
csb-eq a b f fi g gi = ∣ F , hostBij ∣₁
  where
  module G = Graph a b f fi g gi
  F = G.F
  hostBij = G.hostBij
```

<!--en-->
## Cantor's theorem
<!--zh-->
## Cantor 定理
<!--/-->

<!--en-->
The power set of `a` is the set of subsets of `a`, and the diagonal subset is
built by carving: the members of `a` that do not belong to the member of the
power set they are sent to. A surjection from the members of `a` onto the
members of the power set must hit the diagonal, and the diagonal's defining
property flips the membership of its own preimage. This is the 5.6
strictness fact, `|P(κ)| > κ`, in the honest surjection shape.
<!--zh-->
`a` 的幂集是 `a` 的子集之集，而对角子集由雕刻建成：取那些不属于自己像点的 `a` 的成员。从 `a` 的成员到幂集成员的满射必命中对角子集，而对角子集的定义性质恰翻动其自身原像的隶属。这就是 5.6 的严格性事实 `|P(κ)| > κ`，取诚实的满射形状。
<!--/-->

```agda
cantor : (a : S) → (Σ[ f ∈ (⟪ a ⟫ → ⟪ Pow.𝒫V a ⟫) ]
           ((y : ⟪ Pow.𝒫V a ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (f x ≡ y) ∥₁) → Empty.⊥)
cantor a (f , sur) = PT.rec isProp⊥ (λ { (x₀ , fx₀≡m₀) → final x₀ fx₀≡m₀ }) (sur m₀)
  where
  N : (k : ⟪ a ⟫) → Type ℓ
  N k = ⟨ ⟪ a ⟫↪ k ∈ₛ ⟪ Pow.𝒫V a ⟫↪ (f k) ⟩ → Empty.⊥

  D : S
  D = sett (Σ[ m ∈ ⟪ a ⟫ ] N m) (λ p → ⟪ a ⟫↪ (p .fst))

  D⊆a : (x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ x ∈ˢ a ⟩
  D⊆a x x∈D = PT.rec (snd (x ∈ˢ a)) (λ { ((m , n) , e) →
    subst (λ w → ⟨ w ∈ˢ a ⟩) e (member a m) }) x∈D

  D∈P : ⟨ D ∈ˢ Pow.𝒫V a ⟩
  D∈P = subst ⟨_⟩ (sym (Pow.power-spec a D)) D⊆a

  m₀ : ⟪ Pow.𝒫V a ⟫
  m₀ = fiber (Pow.𝒫V a) D∈P .fst

  m₀-spec : ⟪ Pow.𝒫V a ⟫↪ m₀ ≡ D
  m₀-spec = fiber (Pow.𝒫V a) D∈P .snd

  D-mem : (m : ⟪ a ⟫) → N m → ⟨ ⟪ a ⟫↪ m ∈ˢ D ⟩
  D-mem m n = ∣ (m , n) , refl ∣₁

  D-elim : (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ˢ D ⟩ → N m
  D-elim m x∈D = PT.rec (isPropΠ (λ _ → isProp⊥))
    (λ { ((m' , n) , e) → subst N (↪-inj {a = a} e) n }) x∈D

  final : (x₀ : ⟪ a ⟫) → f x₀ ≡ m₀ → Empty.⊥
  final x₀ fx₀≡m₀ = Sum.rec
    (λ x₀∈D → D-elim x₀ (∈∈ₛ {a = ⟪ a ⟫↪ x₀} {b = D} .snd x₀∈D)
                (subst (λ w → ⟨ ⟪ a ⟫↪ x₀ ∈ₛ w ⟩) (sym sₓ₀≡D) x₀∈D))
    (λ nx₀∈D → nx₀∈D (∈∈ₛ {a = ⟪ a ⟫↪ x₀} {b = D} .fst
      (D-mem x₀ (subst (λ w → ⟨ ⟪ a ⟫↪ x₀ ∈ₛ w ⟩ → Empty.⊥) (sym sₓ₀≡D) nx₀∈D))))
    (lowerLEM lem (⟪ a ⟫↪ x₀ ∈ₛ D))
    where
    sₓ₀≡D : ⟪ Pow.𝒫V a ⟫↪ (f x₀) ≡ D
    sₓ₀≡D = cong (⟪ Pow.𝒫V a ⟫↪) fx₀≡m₀ ∙ m₀-spec
```

<!--en-->
## The 5.4 equality half: the lower bound
<!--zh-->
## 5.4 等式半侧：下界
<!--/-->

<!--en-->
The lower bound is two injections into the hull, `X ⊆ M` and `ω ⊆ M`. The
first is delivered by the hull chapter (`X⊆M`); the second is the new
content. Every numeral is the least witness of its defining formula, the
empty set for zero and the successor relation for the step, so the numerals
are members of the hull. The formulas are written once, generic in the
position of the candidate, and the inner satisfaction of the successor
relation is the only new raw material: it says exactly that the second
argument is the successor of the first, in both directions.
<!--zh-->
下界是两条进入外壳的单射：`X ⊆ M` 与 `ω ⊆ M`。第一条由外壳章交付 (`X⊆M`)；第二条是全新内容。每个数码都是其定义公式的最小见证，零取空集、后继步取后继关系，故数码皆是外壳成员。公式一次性写成，对候选位置泛型，而后继关系的内层满足是唯一的新原料：它说的恰是第二实参是第一实参的后继，两个方向皆然。
<!--/-->

```agda
succFo : ∀ {ℓk} {K : Type ℓk} {n} (x y : Fin n) → Formula K n
succFo x y = (∀̇∈ (var y) ((var zero ∈̇ var (suc x)) ∨̇ (var zero ≐ var (suc x))))
  ∧̇ (∀̇∈ (var x) (var zero ∈̇ var (suc y))) ∧̇ (var x ∈̇ var y)

numeralFo : (n : ℕ) → ∀ {ℓk} {K : Type ℓk} {n'} (v : Fin (suc n')) → Formula K (suc n')
numeralFo zero v = ∀̇∈ (var v) ⊥̇
numeralFo (suc n) {ℓk} {K} {n'} v = ∃̇∈ (var v) (succFo zero (suc v) ∧̇ numeralFo n {K = K} {n' = suc n'} zero)

module AtHull (α : S) (ordα : IsOrd α) (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

  module A = CC.AtHull α ordα X X⊆L

  isSetSL : isSet A.H.SL
  isSetSL = isSetΣSndProp setIsSet (λ x → (x ∈ˢ Lset α) .snd)

  Ltr : isTransV (Lset α)
  Ltr = layer-trans (Lset-layer α)

  ω∈L : ⟨ ω ∈ˢ Lset α ⟩ → (k : ℕ) → ⟨ (# k) ∈ˢ Lset α ⟩
  ω∈L h k = Ltr {x = ω} {y = # k} (#∈ω k) h

  nL : (k : ℕ) → ⟨ ω ∈ˢ Lset α ⟩ → A.H.SL
  nL k h = (# k , ω∈L h k)

  succ-sat : {n : ℕ} (u v : A.H.SL) (δ : A.H.SL ^ n) → fst v ≡ sucV (fst u)
           → ⟨ (u ∷ v ∷ δ) A.HullX.Small.⊨ᵐ (succFo zero (suc zero)) ⟩
  succ-sat {n} u v δ e = a , (b , c)
    where
    a : (z : A.H.SL) → ⟨ fst z ∈ˢ fst v ⟩
       → ∥ ⟨ fst z ∈ˢ fst u ⟩ ⊎ (fst z ≡ fst u) ∥₁
    a z hz = ∈sucV-elim (squash₁) (subst (λ w → ⟨ fst z ∈ˢ w ⟩) e hz)
      (λ hzu → ∣ inl hzu ∣₁) (λ hz≡u → ∣ inr hz≡u ∣₁)
    b : (z : A.H.SL) → ⟨ fst z ∈ˢ fst u ⟩ → ⟨ fst z ∈ˢ fst v ⟩
    b z hzu = subst (λ w → ⟨ fst z ∈ˢ w ⟩) (sym e) (∈sucV-inl hzu)
    c : ⟨ fst u ∈ˢ fst v ⟩
    c = subst (λ w → ⟨ fst u ∈ˢ w ⟩) (sym e) (self∈sucV (fst u))

  succ-sat-bwd : {n : ℕ} (u v : A.H.SL) (δ : A.H.SL ^ n)
               → ⟨ (u ∷ v ∷ δ) A.HullX.Small.⊨ᵐ (succFo zero (suc zero)) ⟩ → fst v ≡ sucV (fst u)
  succ-sat-bwd u v δ (a , (b , c)) = extensionality (fst v) (sucV (fst u)) (s1 , s2)
    where
    s1 : ⟨ fst v ⊆ sucV (fst u) ⟩
    s1 z hz = PT.rec (snd (z ∈ₛ sucV (fst u))) (s1' z) (a (z , z∈L) (∈∈ₛ {a = z} {b = fst v} .snd hz))
      where
      z∈L : ⟨ z ∈ˢ Lset α ⟩
      z∈L = Ltr {x = fst v} {y = z} (∈∈ₛ {a = z} {b = fst v} .snd hz) (v .snd)
      s1' : (z : S) → ⟨ z ∈ˢ fst u ⟩ ⊎ (z ≡ fst u) → ⟨ z ∈ₛ sucV (fst u) ⟩
      s1' z (inl hzu) = ∈∈ₛ {a = z} {b = sucV (fst u)} .fst (∈sucV-inl hzu)
      s1' z (inr hz≡u) = ∈∈ₛ {a = z} {b = sucV (fst u)} .fst
        (subst (λ w → ⟨ w ∈ˢ sucV (fst u) ⟩) (sym hz≡u) (self∈sucV (fst u)))
    s2 : ⟨ sucV (fst u) ⊆ fst v ⟩
    s2 z hz = ∈∈ₛ {a = z} {b = fst v} .fst (∈sucV-elim (snd (z ∈ˢ fst v))
        (∈∈ₛ {a = z} {b = sucV (fst u)} .snd hz)
        (λ hzu → b (z , Ltr {x = fst u} {y = z} hzu (u .snd)) hzu)
        (λ hz≡u → subst (λ w → ⟨ w ∈ˢ fst v ⟩) (sym hz≡u) c))

  numeral-sat : (k : ℕ) (h : ⟨ ω ∈ˢ Lset α ⟩) {n : ℕ} (δ : A.H.SL ^ n)
              → ⟨ (nL k h ∷ δ) A.HullX.Small.⊨ᵐ (numeralFo k {n' = n} zero) ⟩
  numeral-sat zero h {n} δ = λ x x∈ → Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst x∈))
  numeral-sat (suc k) h {n} δ = ∣ nL k h , (gu , (succ-sat (nL k h) (nL (suc k) h) δ refl , numeral-sat k h (nL (suc k) h ∷ δ))) ∣₁
    where
    gu : ⟨ (# k) ∈ˢ (# (suc k)) ⟩
    gu = self∈sucV (# k)

  numeral-unique : (k : ℕ) (h : ⟨ ω ∈ˢ Lset α ⟩) {n : ℕ} (a : A.H.SL) (δ : A.H.SL ^ n)
                 → ⟨ (a ∷ δ) A.HullX.Small.⊨ᵐ (numeralFo k {n' = n} zero) ⟩ → a ≡ nL k h
  numeral-unique zero h a δ ha = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd)
    (extensionality (fst a) ∅ (s1 , s2))
    where
    s1 : ⟨ fst a ⊆ ∅ ⟩
    s1 z hz = Empty.rec* {ℓ' = ℓ-suc ℓ} (ha (z , Ltr {x = fst a} {y = z} (∈∈ₛ {a = z} {b = fst a} .snd hz) (a .snd))
      (∈∈ₛ {a = z} {b = fst a} .snd hz))
    s2 : ⟨ ∅ ⊆ fst a ⟩
    s2 z hz = Empty.rec (∅-empty z hz)
  numeral-unique (suc k) h a δ ha =
    PT.rec (isSetSL a (nL (suc k) h)) (λ { (y , gy , (sat , hy)) →
      Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd)
        (succ-sat-bwd y a δ sat ∙ cong sucV (cong fst (numeral-unique k h y (a ∷ δ) hy))) })
      ha

  inHull : (k : ℕ) (h : ⟨ ω ∈ˢ Lset α ⟩) → ⟨ (# k) ∈ˢ A.HullX.Hull ⟩
  inHull k h = ∣ (φk , wk) , (cong fst (numeral-unique k h (A.HullX.leastWit φk wk) [] (A.HullX.leastWit-spec φk wk .fst))) ∣₁
    where
    φk = numeralFo k {n' = 0} zero
    wk : A.HullX.Witnessed-small φk
    wk = A.HullX.big→small φk ∣ nL k h , numeral-sat k h [] ∣₁

  ω⊆M : ⟨ ω ∈ˢ Lset α ⟩ → (x : S) → ⟨ x ∈ˢ ω ⟩ → ⟨ x ∈ˢ A.HullX.Hull ⟩
  ω⊆M h x x∈ω = PT.rec (snd (x ∈ˢ A.HullX.Hull)) (λ { (k , e) → subst (λ w → ⟨ w ∈ˢ A.HullX.Hull ⟩) e (inHull (lower k) h) }) x∈ω
```

<!--en-->
## The 5.4 equality half: the bijection form
<!--zh-->
## 5.4 等式半侧：双射形态
<!--/-->

<!--en-->
The bijection form is the composition the counting side's closing note
promised: an injection from the hull into `β` and one back, upgraded by CSB
to `HostEq M β`. The statement takes the two injections as its hypotheses;
the upper one is the counting side's bound read at the presentation index of
the hull, and the lower one is what the 5.5-style consumer supplies from
`X ⊆ M` when `X` contains the stage. The report records where each
hypothesis is produced.
<!--zh-->
双射形态是计数侧收尾注记所许诺的复合：一条从外壳进入 `β` 的单射与一条返回的单射，经 CSB 升级为 `HostEq M β`。陈述把两条单射取作假设；上单射是计数侧之界在外壳呈现索引处的读法，下单射正是 5.5 式消费方在 `X` 包含该阶段时从 `X ⊆ M` 供应的假设。报告记录每条假设产自何处。
<!--/-->

```agda
module BijectionForm (α : S) (ordα : IsOrd α) (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

  module A = CC.AtHull α ordα X X⊆L

  bijection-form : (β : S)
                 → (upper : Σ[ f ∈ (⟪ A.HullX.Hull ⟫ → ⟪ β ⟫) ] ((x y : ⟪ A.HullX.Hull ⟫) → f x ≡ f y → x ≡ y))
                 → (h : Σ[ f ∈ (⟪ β ⟫ → ⟪ A.HullX.Hull ⟫) ] ((x y : ⟪ β ⟫) → f x ≡ f y → x ≡ y))
                 → HostEq A.HullX.Hull β
  bijection-form β upper h =
    csb-eq A.HullX.Hull β (fst upper) (snd upper) (fst h) (snd h)
```
