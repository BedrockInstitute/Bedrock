# Cantor-Schroeder-Bernstein, at the index types

<!--en-->
Two injections, one each way between the same pair, give one bijection. That
is Cantor-Schroeder-Bernstein, and the installed library does not ship it. The
two target theorems both want it as a reading, so this chapter proves it once
at the substrate, where both inherit it. The construction names no tower, no
stage and no satisfaction relation. It consumes the presentation's small
member types and one dose of excluded middle, taken at the level of those
types: a chapter holding the stronger `LEM (ℓ-suc ℓ)` redeems this dose
through `lowerLEM`{.Agda}.
<!--zh-->
同是一对、各走一趟的两条单射，决定一条双射。这就是 Cantor-Schroeder-Bernstein 定理，而随库并未提供。两大目标定理都要以它作读法，故本章在地基处把它证一次，两侧皆得继承。构造不点名任何塔、任何阶段、任何满足关系，消费的只有呈现的小成员类型，外加一剂这一层上的排中律：握有更强 `LEM (ℓ-suc ℓ)` 的章节，经 `lowerLEM`{.Agda} 即可兑付这剂药。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module V.CantorBernstein {ℓ : Level} (lem : LEM ℓ) where

open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
```

<!--en-->
## The construction
<!--zh-->
## 构造
<!--/-->

<!--en-->
The classical proof runs on the index level, and that is why it transfers so
cheaply. The "bad" elements of `A` are those reachable by a finite alternating
preimage chain starting outside the image of `g`; the bijection sends a bad
element through `f` and a good one back along `g⁻¹`. The chain is a small
predicate family `Cₙ`{.Agda}, and the one structural fact the proof needs is
that the map `x ↦ g (f x)` closes the bad set. Excluded middle enters twice,
to decide the bad set and to extract `g⁻¹` from the truncated image statement.
<!--zh-->
经典证明跑在索引层，这也正是它转移起来便宜的原因。`A` 中的「坏」元素，是那些能沿一条有穷的交替原像链、从 `g` 的像之外出发够到的元素；双射把坏元素经 `f` 送出、好元素经 `g⁻¹` 送回。链是一个小谓词族 `Cₙ`{.Agda}，证明唯一需要的结构事实是映射 `x ↦ g (f x)` 封闭坏集。排中律两次进场：一次判定坏集，一次从截断的像陈述里提取 `g⁻¹`。
<!--/-->

<!--en-->
The construction is stated at two abstract types. It needs one set-ness
hypothesis, on the type the chains climb, and nothing else that mentions sets:
no presentation, no membership, no carrier. That abstraction is the sharing
axis. Every consumer, ambient or internal, reads the theorem off at its own
pair of types, and the set form below is one such reading, with set-ness
supplied by the presentation embedding. No choice is used: the inverse of `g`
is extracted by `fiberG` from the propositionality of the fiber, which follows
from injectivity alone.
<!--zh-->
构造陈述在两个抽象类型上。它只要一条集合性假设，加在链攀升的那一侧，此外再无一物提及集合：没有呈现、没有隶属、没有载体。这条抽象就是共享轴。任何消费方，无论环境层还是内层，都在自己的那一对类型处读走定理，下面的集合形态便是其中一种读法，集合性由呈现嵌入供给。全程不用选择：`g` 的逆由 `fiberG` 从纤维的命题性提取，而命题性单凭单射性即得。
<!--/-->

```agda
module Bernstein {A B : Type ℓ} (setA : isSet A)
                 (f : A → B) (fi : (x y : A) → f x ≡ f y → x ≡ y)
                 (g : B → A) (gi : (x y : B) → g x ≡ g y → x ≡ y) where

  imG : A → hProp ℓ
  imG x = (∥ Σ[ y ∈ B ] (g y ≡ x) ∥₁ , squash₁)

  C₀ : A → hProp ℓ
  C₀ x = ((⟨ imG x ⟩ → Empty.⊥) , isPropΠ (λ _ → isProp⊥))

  C₊ : (A → hProp ℓ) → A → hProp ℓ
  C₊ C x = (∥ Σ[ y ∈ B ] Σ[ z ∈ A ] ((g y ≡ x) × ((f z ≡ y) × ⟨ C z ⟩)) ∥₁ , squash₁)

  Cₙ : ℕ → A → hProp ℓ
  Cₙ zero = C₀
  Cₙ (suc n) = C₊ (Cₙ n)

  C : A → hProp ℓ
  C x = (∥ Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ ∥₁ , squash₁)

  c-in : {x : A} {n : ℕ} → ⟨ Cₙ n x ⟩ → ⟨ C x ⟩
  c-in {x} {n} h = ∣ n , h ∣₁

  gf-closed : {x : A} → ⟨ C x ⟩ → ⟨ C (g (f x)) ⟩
  gf-closed {x} = PT.rec (snd (C (g (f x)))) go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ⟨ C (g (f x)) ⟩
    go (n , cx) = c-in {x = g (f x)} {n = suc n} ∣ f x , x , (refl , (refl , cx)) ∣₁

  C-view : {x : A} → ⟨ C x ⟩
         → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ A ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
  C-view {x} = PT.rec squash₁ go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ A ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
    go (zero , c0) = ∣ inl c0 ∣₁
    go (suc n , cs) = PT.map inr (PT.map (λ { (y , z , gy , fz , cz) →
        z , ((cong g fz ∙ gy) , c-in {x = z} {n = n} cz) }) cs)

  notC→imG : {x : A} → (⟨ C x ⟩ → Empty.⊥) → ⟨ imG x ⟩
  notC→imG {x} nC = Sum.rec {A = ⟨ imG x ⟩} {B = ⟨ imG x ⟩ → Empty.⊥} {C = ⟨ imG x ⟩}
    (λ h → h) (λ nC₀ → Empty.rec (nC (c-in {n = zero} nC₀)))
    (lem (imG x))

  fiberG-prop : (x : A) → isProp (Σ[ y ∈ B ] (g y ≡ x))
  fiberG-prop x (y , p) (y' , p') = Σ≡Prop {A = B} {B = λ y → g y ≡ x}
    (λ y → setA (g y) x) (gi y y' (p ∙ sym p'))

  fiberG : (x : A) → ⟨ imG x ⟩ → Σ[ y ∈ B ] (g y ≡ x)
  fiberG x = PT.rec (fiberG-prop x) (λ w → w)

  ginv : {x : A} → (⟨ C x ⟩ → Empty.⊥) → B
  ginv {x} nC = fiberG x (notC→imG nC) .fst

  ginv-spec : {x : A} (nC : ⟨ C x ⟩ → Empty.⊥) → g (ginv nC) ≡ x
  ginv-spec {x} nC = fiberG x (notC→imG nC) .snd

  h : (x : A) → ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) → B
  h x (inl _) = f x
  h x (inr nC) = ginv nC

  h-inj : (x x' : A) (dx : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) (dx' : ⟨ C x' ⟩ ⊎ (⟨ C x' ⟩ → Empty.⊥))
        → h x dx ≡ h x' dx' → x ≡ x'
  h-inj x x' (inl cx) (inl cx') e = fi x x' e
  h-inj x x' (inl cx) (inr nCx') e =
    Empty.rec (nCx' (subst (λ w → ⟨ C w ⟩) (cong g e ∙ ginv-spec nCx') (gf-closed {x = x} cx)))
  h-inj x x' (inr nCx) (inl cx') e =
    Empty.rec (nCx (subst (λ w → ⟨ C w ⟩) (sym (cong g e) ∙ ginv-spec nCx) (gf-closed {x = x'} cx')))
  h-inj x x' (inr nCx) (inr nCx') e = sym (ginv-spec nCx) ∙ cong g e ∙ ginv-spec nCx'

  h-surj : (y : B) (d : ⟨ C (g y) ⟩ ⊎ (⟨ C (g y) ⟩ → Empty.⊥))
         → ∥ Σ[ x ∈ A ] Σ[ dx ∈ ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) ] (h x dx ≡ y) ∥₁
  h-surj y (inr nCgy) = ∣ g y , inr nCgy , gi (ginv nCgy) y (ginv-spec nCgy) ∣₁
  h-surj y (inl cgy) = PT.rec squash₁
    (λ { (inl c0) → Empty.rec (c0 ∣ y , refl ∣₁) ; (inr (z , gfy , cz)) → ∣ z , inl cz , gi (f z) y gfy ∣₁ })
    (C-view {x = g y} cgy)

  h-cons : (x : A) (dx dx' : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) → h x dx ≡ h x dx'
  h-cons x (inl cx) (inl cx') = refl
  h-cons x (inl cx) (inr nCx') = Empty.rec (nCx' cx)
  h-cons x (inr nCx) (inl cx) = Empty.rec (nCx cx)
  h-cons x (inr nCx) (inr nCx') = cong fst (fiberG-prop x (fiberG x (notC→imG nCx)) (fiberG x (notC→imG nCx')))

  ĥ : A → B
  ĥ x = h x (lem (C x))

  ĥ-inj : (x x' : A) → ĥ x ≡ ĥ x' → x ≡ x'
  ĥ-inj x x' e = h-inj x x' (lem (C x)) (lem (C x')) e

  ĥ-surj : (y : B) → ∥ Σ[ x ∈ A ] (ĥ x ≡ y) ∥₁
  ĥ-surj y = PT.map (λ { (x , dx , e) → x , sym (h-cons x dx (lem (C x))) ∙ e })
    (h-surj y (lem (C (g y))))
```

<!--en-->
## At the sets
<!--zh-->
## 在集合处
<!--/-->

<!--en-->
Read at two sets, the theorem says: two injections between the small member
types of two sets give one bijection, an injection whose surjectivity stays a
truncation. Set-ness comes from the presentation embedding, exported here as
`small-set`{.Agda} so that consumers stating the corollary at their own
carriers do not re-derive it.
<!--zh-->
在两个集合处读，定理说的是：两个集合的小成员类型之间的两条单射给出一条双射，一条单射，其满射性保持截断。集合性出自呈现嵌入，并以 `small-set`{.Agda} 之名在此导出，好让在自己的载体上陈述推论的消费方不必重推。
<!--/-->

```agda
small-set : (a : V ℓ) → isSet (⟪ a ⟫)
small-set a = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

cantor-bernstein : (a b : V ℓ) (f : ⟪ a ⟫ → ⟪ b ⟫)
    → ((x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
    → (g : ⟪ b ⟫ → ⟪ a ⟫) → ((x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y)
    → Σ[ h ∈ (⟪ a ⟫ → ⟪ b ⟫) ]
        (((x y : ⟪ a ⟫) → h x ≡ h y → x ≡ y)
      × ((y : ⟪ b ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (h x ≡ y) ∥₁))
cantor-bernstein a b f fi g gi = M.ĥ , ( M.ĥ-inj , M.ĥ-surj )
  where
  module M = Bernstein {A = ⟪ a ⟫} {B = ⟪ b ⟫} (small-set a) f fi g gi
```

<!--en-->
## The corollary
<!--zh-->
## 推论
<!--/-->

<!--en-->
The corollary packages the step a set-theoretic reading of a two-injection
statement leaves to the reader. Suppose a notion of "`a` injects into `b`"
comes with a readback: a machine turning every witness into an honest function
between the small types, injective as a function. Then two witnesses, one each
way, give one ambient bijection between the small types. A target theorem
states its cardinal equality exactly as two internal injections, the delivered
readback turns each into a map between small member types, and this module
assembles Cantor-Schroeder-Bernstein once, generically, so no consumer
re-derives it.
<!--zh-->
推论打包的，是「两条单射式陈述」读成集合论时留给读者的那一步。设有一个「`a` 单射进 `b`」的概念，且配有读回：一台机器，把每个见证变成小类型之间一条诚实的函数，并且作为函数是单射。那么各持一条的两个见证，给出小类型之间一条环境层双射。目标定理把基数等式恰好陈述成两条内部单射，已交付的读回把每条变成小成员类型之间的映射，而本模块一次性、按通用形状装配 Cantor-Schroeder-Bernstein，消费方不必各自重推。
<!--/-->

<!--en-->
The surjectivity in the conclusion stays truncated, and that is no loss. The
hypotheses speak in truncated injections, so the bijection this corollary
returns is the same grade of object they speak in; the set theorist's "every
element of the codomain has a preimage" is exactly a truncation, and
untruncating it would claim more than the classical theorem ever states.

A witness notion, though, often arrives already truncated: the target
theorem's "`a` injects into `b`" is a truncated code existential, and no
truncation may be eliminated into the data a function is. So the corollary
also comes in the existential form: truncated witnesses in, truncated
bijection out, the two eliminations riding the propositionality of the
function type into a truncation.
<!--zh-->
结论里的满射性保持截断，这不是损失。假设所说的是截断的单射，本推论交还的双射便与其假设同属一个等级的对象；集合论学者口中的「值域的每个元素都有原像」恰恰就是一个截断，去掉截断反而主张了经典定理从未主张的东西。

然而见证概念常常本来就带着截断到来：目标定理的「`a` 单射进 `b`」就是一个截断的码存在式，而任何截断都不得消去成函数所是的数据。故推论另备存在形态：截断的见证进，截断的双射出，两次消去都骑行在「到截断的函数类型是命题」之上。
<!--/-->

```agda
module MutualInj {ℓ₁ ℓ₂ : Level} (C : Type ℓ₁) (P : C → Type ℓ)
    (R : (a b : C) → Type ℓ₂)
    (setP : (a : C) → isSet (P a))
    (read : (a b : C) → R a b
          → Σ[ f ∈ (P a → P b) ] ((x y : P a) → f x ≡ f y → x ≡ y)) where

  mutual→bijection : (a b : C) → R a b → R b a
    → Σ[ h ∈ (P a → P b) ]
        (((x y : P a) → h x ≡ h y → x ≡ y)
      × ((y : P b) → ∥ Σ[ x ∈ P a ] (h x ≡ y) ∥₁))
  mutual→bijection a b fwd bwd = M.ĥ , ( M.ĥ-inj , M.ĥ-surj )
    where
    module M = Bernstein {A = P a} {B = P b} (setP a)
      (read a b fwd .fst) (read a b fwd .snd)
      (read b a bwd .fst) (read b a bwd .snd)

  ∃bijection : (a b : C) → ∥ R a b ∥₁ → ∥ R b a ∥₁
    → ∥ Σ[ h ∈ (P a → P b) ]
        (((x y : P a) → h x ≡ h y → x ≡ y)
      × ((y : P b) → ∥ Σ[ x ∈ P a ] (h x ≡ y) ∥₁)) ∥₁
  ∃bijection a b fwd bwd = PT.rec squash₁
    (λ w → PT.rec squash₁ (λ w' → ∣ mutual→bijection a b w w' ∣₁) bwd)
    fwd
```
