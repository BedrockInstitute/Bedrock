# V ⊨ ZF(C)

<!--en-->
Time to settle the account. The model record demands twelve fields; two are
banked (extensionality and regularity, from the hierarchy chapter), and the
smallness chapter's free tier covers separation only for Δ₀ witnesses, while
the record wants it for **every** formula. This chapter delivers the rest: the
stock sets that the library simply has (empty, pair, union), replacement and
strong infinity, which turn out to cost nothing, and then the two genuine debts,
full separation and power set, whose exact price is a resizing assumption. With
that assumption paid, the record is assembled: **V is a model of ZF**, the
relative-consistency theorem this part exists to prove. Choice then enters as a
second, independent assumption, and upgrades the model to ZFC.
<!--zh-->
清账的时候到了。模型 record 要十二个字段；两个已入账 (外延与正则，层级章)，小性章的免费档又只覆盖带 Δ₀ 见证的分离，而 record 要的是**每条**公式。本章交付其余一切：库里现成的库存集合 (空集、配对、并)，成本意外为零的替换与强无穷，然后是两笔真正的欠账，全分离与幂集，其精确价格是一个降层假设。付讫，record 合龙：**V 是 ZF 的模型**，本部为之而生的相对一致性定理。随后选择公理作为第二个独立假设进场，把模型升级到 ZFC。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Model {ℓ : Level} where

open import Base.Classical using ( LEM; HPropSmallness; Impredicativity; lem→impredicativity )
open import Base.Choice using ( SetChoice; choice→lem; lowerSetChoice )
open import FOL.Structure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
import ZF
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import V.Smallness {ℓ} using ( separateFromSmall )

open import Cubical.Foundations.Equiv using ( equivFun; invEq; secEq )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Functions.Embedding
  using ( Embedding-into-isSet→isSet; isEmbedding→Inj )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber
        ; identityPrinciple; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; ⁅_⁆s; _∪_
        ; SingletonPackage; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( SetPackage )  -- lint-agda: keep (used qualified: SetPackage.classification)
open InfinitySet using ( sucV; #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ᵥ

module Model = ZF 𝒮ᵥ
open Model using ( SetOf; _⊆ˢ_; setOf-unique; isZFModel; isZFCModel )

module SemanticsV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemanticsV.At (λ (x : S) → x) using ( _⊨_ )
```

<!--en-->
## The stock sets
<!--zh-->
## 库存集合
<!--/-->

<!--en-->
Empty set, pair, and union sit in the library ready-made, each with its axiom.
Only the *shape* needs converting, and the recipe is the same three moves every
time: the library states its axiom in small form (`∈ₛ`), `∈∈ₛ`{.Agda} reshapes
membership pointwise, and `⇔toPath`{.Agda} lands the bi-implication as the path
the record's field wants. For the pair the fit is even closer: the library's
"equal to `a` or to `b`" *is* the field's `(x ≈ˢ a) ⊔ (x ≈ˢ b)` definitionally,
so the glue is one layer of `∈∈ₛ` and nothing else.
<!--zh-->
空集、配对、并在库里现成躺着，各带公理。要换的只是**形状**，而配方每次都是同样三步：库公理以小形式 (`∈ₛ`) 陈述，`∈∈ₛ`{.Agda} 逐点换形成员关系，`⇔toPath`{.Agda} 把双蕴含落成字段要的路径。配对甚至更严丝合缝：库的「等于 `a` 或等于 `b`」与字段的 `(x ≈ˢ a) ⊔ (x ≈ˢ b)` **定义性相同**，胶水只剩一层 `∈∈ₛ`。
<!--/-->

```agda
empty-spec : (x : S) → (x ∈ˢ ∅) ≡ ⊥
empty-spec x = ⇔toPath
  (λ x∈ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈)))
  (λ ())

pair-spec : (a b x : S) → (x ∈ˢ ⁅ a , b ⁆) ≡ ((x ≈ˢ a) ⊔ (x ≈ˢ b))
pair-spec a b x = ⇔toPath
  (λ x∈ → pairing-ax a b x .fst (∈∈ₛ {a = x} {b = ⁅ a , b ⁆} .fst x∈))
  (λ h → ∈∈ₛ {a = x} {b = ⁅ a , b ⁆} .snd (pairing-ax a b x .snd h))

union-spec : (a x : S) → (x ∈ˢ (⋃ a)) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))
union-spec a x = ⇔toPath
  (λ x∈ → PT.map
    (λ { (v , va , xv) → v , ∈∈ₛ {a = v} {b = a} .snd va
                           , ∈∈ₛ {a = x} {b = v} .snd xv })
    (union-ax a x .fst (∈∈ₛ {a = x} {b = ⋃ a} .fst x∈)))
  (λ h → ∈∈ₛ {a = x} {b = ⋃ a} .snd (union-ax a x .snd (PT.map
    (λ { (v , va , xv) → v , ∈∈ₛ {a = v} {b = a} .fst va
                           , ∈∈ₛ {a = x} {b = v} .fst xv })
    h)))
```

<!--en-->
## Replacement, for free
<!--zh-->
## 替换，免费
<!--/-->

<!--en-->
Replacement is the first surprise of the chapter: a *schema* that costs nothing.
The reason is `sett`{.Agda} itself. Given `φ` functional on `a`, index the image
by the small member type `⟪ a ⟫` and write the image set down directly; no
axiom is consulted. The delicate direction is recovering an index from a
membership fact, and it is the smallness chapter's refrain once more: the fibers
of `∈-asFiber`{.Agda} are untruncated, so "member to index" is a function, not a
choice.
<!--zh-->
替换是本章第一个意外：一条**模式**公理，成本为零。原因就是 `sett`{.Agda} 本身。给定在 `a` 上函数性的 `φ`，以小成员类型 `⟪ a ⟫` 为索引，把像集直接写下来，全程不问任何公理。娇贵的方向是从成员资格回收索引，而这又是小性章的老调重弹：`∈-asFiber`{.Agda} 的纤维不加截断，「从成员到索引」是函数，不是选择。
<!--/-->

```agda
private
  memb : (a : S) (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ˢ a ⟩
  memb a m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

module _ (a : S) (φ : Formula S 2)
         (fc : (x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)) where

  replaceImage : S
  replaceImage = sett ⟪ a ⟫ (λ m → fc (⟪ a ⟫↪ m) (memb a m) .fst .fst)

  replaceImage-spec : ∀ y → (y ∈ˢ replaceImage)
                    ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))
  replaceImage-spec y = ⇔toPath fwd bwd
    where
    fwd : ⟨ y ∈ˢ replaceImage ⟩ → ⟨ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩
    fwd = PT.map λ { (m , q) →
        ⟪ a ⟫↪ m , memb a m
      , subst (λ v → ⟨ (v ∷ ⟪ a ⟫↪ m ∷ []) ⊨ φ ⟩) q
              (fc (⟪ a ⟫↪ m) (memb a m) .fst .snd) }
    bwd : ⟨ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩ → ⟨ y ∈ˢ replaceImage ⟩
    bwd = PT.map λ { (x , x∈a , hφ) →
      let mf = ∈-asFiber {a = x} {b = a} x∈a
          hφ' = subst (λ v → ⟨ (y ∷ v ∷ []) ⊨ φ ⟩) (sym (mf .snd)) hφ
      in mf .fst
       , cong fst (fc (⟪ a ⟫↪ (mf .fst)) (memb a (mf .fst)) .snd (y , hφ')) }
```

<!--en-->
## The numeral chain and ω
<!--zh-->
## 数码链与 ω
<!--/-->

<!--en-->
The library's `ω` is `sett` over `Lift ℕ` with the library numerals `#` as the
family, so its membership is **definitionally** "merely hit by some `#`": strong
infinity in exactly the record's sense, before any proof is written. What remains
is bookkeeping in two steps. First, the model's chain must align with the
library's: `numeralV`{.Agda} steps by `a ∪ ⁅ a , a ⁆` while `#`{.Agda} steps by
`sucV a = a ∪ ⁅ a ⁆s`, and the only genuine gap is `⁅ a , a ⁆ ≡ ⁅ a ⁆s`, one
appeal to extensionality (the two families differ only in index type).
<!--zh-->
库的 `ω` 是以库数码 `#` 为族、在 `Lift ℕ` 上的 `sett`，于是它的成员关系**按定义**就是「仅仅被某个 `#` 命中」：恰是 record 意义上的强无穷，一笔证明未写就已成立。剩下的是两步记账。第一步，模型的链要与库的链对齐：`numeralV`{.Agda} 按 `a ∪ ⁅ a , a ⁆` 走步，`#`{.Agda} 按 `sucV a = a ∪ ⁅ a ⁆s` 走步，唯一的真实间隙是 `⁅ a , a ⁆ ≡ ⁅ a ⁆s`，一次外延性 (两个族只差索引类型)。
<!--/-->

```agda
pair-singleton : (a : S) → ⁅ a , a ⁆ ≡ ⁅ a ⁆s
pair-singleton a = extensionality ⁅ a , a ⁆ ⁅ a ⁆s (s1 , s2)
  where
  singl-cls = SetPackage.classification (SingletonPackage a)
  s1 : ⟨ ⁅ a , a ⁆ ⊆ ⁅ a ⁆s ⟩
  s1 x x∈ₛ = singl-cls x .snd
    (PT.rec (setIsSet x a)
            (λ { (Sum.inl e) → e ; (Sum.inr e) → e })
            (pairing-ax a a x .fst x∈ₛ))
  s2 : ⟨ ⁅ a ⁆s ⊆ ⁅ a , a ⁆ ⟩
  s2 x x∈ₛ = pairing-ax a a x .snd ∣ Sum.inl (singl-cls x .fst x∈ₛ) ∣₁

numeralV : ℕ → S
numeralV zero    = ∅
numeralV (suc n) = numeralV n ∪ ⁅ numeralV n , numeralV n ⁆

numeralV≡# : (n : ℕ) → numeralV n ≡ # n
numeralV≡# zero    = refl
numeralV≡# (suc n) = cong₂ (λ u v → ⋃ ⁅ u , v ⁆) (numeralV≡# n)
  (cong (λ u → ⁅ u , u ⁆) (numeralV≡# n) ∙ pair-singleton (# n))

ω-specV : (x : S)
        → (x ∈ˢ ω) ≡ ⋁ (Lift {ℓ-zero} {ℓ-suc ℓ} ℕ) (λ n → x ≈ˢ numeralV (lower n))
ω-specV x = ⇔toPath
  (PT.map (λ { (i , p) → lift (lower i)
             , sym p ∙ sym (numeralV≡# (lower i)) }))
  (PT.map (λ { (n , q) → lift (lower n)
             , sym (q ∙ numeralV≡# (lower n)) }))
```

<!--en-->
Second, the record's two pinning equations speak of membership in a successor,
so the chapter needs the case analysis for `sucV`: a member of `sucV A` is
merely a member of `A` or equal to `A`, and both inclusions back. The proofs
unfold `sucV` through the union and pairing axioms once, with the singleton's
classification closing the second disjunct.
<!--zh-->
第二步，record 的两条钉死方程说的是「后继的成员」，所以本章需要 `sucV` 的分情形装置：`sucV A` 的成员仅仅要么是 `A` 的成员、要么等于 `A`，外加两个方向的收纳。证明把 `sucV` 沿并与配对公理展开一次，单点集的分类收掉第二个析取支。
<!--/-->

```agda
private
  singl≡ : (A x : S) → ⟨ x ∈ₛ ⁅ A ⁆s ⟩ → x ≡ A
  singl≡ A x = SetPackage.classification (SingletonPackage A) x .fst

∈sucV-elim : {A x : S} {P : Type (ℓ-suc ℓ)} → isProp P → ⟨ x ∈ˢ sucV A ⟩
           → (⟨ x ∈ˢ A ⟩ → P) → (x ≡ A → P) → P
∈sucV-elim {A} {x} pP x∈ kA k≡ =
  PT.rec pP
    (λ { (v , (v∈₂ , x∈v)) → PT.rec pP
      (λ { (Sum.inl v≡A) →
             kA (∈∈ₛ {a = x} {b = A} .snd (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡A x∈v))
         ; (Sum.inr v≡s) →
             k≡ (singl≡ A x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡s x∈v)) })
      (pairing-ax A ⁅ A ⁆s v .fst v∈₂) })
    (union-ax ⁅ A , ⁅ A ⁆s ⁆ x .fst (∈∈ₛ {a = x} {b = sucV A} .fst x∈))

∈sucV-inl : {A x : S} → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ sucV A ⟩
∈sucV-inl {A} {x} x∈A = ∈∈ₛ {a = x} {b = sucV A} .snd
  (union-ax ⁅ A , ⁅ A ⁆s ⁆ x .snd
    ∣ A , (pairing-ax A ⁅ A ⁆s A .snd ∣ Sum.inl refl ∣₁
         , ∈∈ₛ {a = x} {b = A} .fst x∈A) ∣₁)

self∈sucV : (a : S) → ⟨ a ∈ˢ sucV a ⟩
self∈sucV a = ∈∈ₛ {a = a} {b = sucV a} .snd
  (union-ax ⁅ a , ⁅ a ⁆s ⁆ a .snd
    ∣ ⁅ a ⁆s , (pairing-ax a ⁅ a ⁆s ⁅ a ⁆s .snd ∣ Sum.inr refl ∣₁
              , SetPackage.classification (SingletonPackage a) a .snd refl) ∣₁)
```

<!--en-->
## The price of the rest
<!--zh-->
## 其余部分的价格
<!--/-->

<!--en-->
Two fields remain, full separation and power set, and neither is free: both need
truth values brought down a universe with no Δ₀ witness to pay the fare. The
price is exactly Part 0's impredicativity packing: `resizing`{.Agda} compresses
any proposition, and `hPropSmallness`{.Agda} is the small classifier the power
set will be indexed by. Nothing here is an axiom; the assembly takes the
packing as a parameter, and the classical reader rides free through
`lem→impredicativity`{.Agda}, which is what the dividends were saved for.
<!--zh-->
还剩两个字段，全分离与幂集，都不免费：两者都要把真值降下一层宇宙，却没有 Δ₀ 见证替它们买票。价格恰是第零部打包好的非直谓性接口：`resizing`{.Agda} 压缩任意命题，`hPropSmallness`{.Agda} 是幂集将用作索引的小分类器。此处无一是公理；合龙以这份打包为参数，经典读者则经 `lem→impredicativity`{.Agda} 免票，当初存下红利，等的就是今天。
<!--/-->

<!--en-->
## Power set
<!--zh-->
## 幂集
<!--/-->

<!--en-->
The power set is the one construction the library's own header disclaims, and the
small classifier is precisely what builds it. Index the candidate subsets by
**small characteristic functions** `⟪ a ⟫ → Ω'`; realizing one as a set is a
`sett` over the members it selects. The delicate direction again runs through
untruncated fibers: from an actual subset `s`, the characteristic function
`m ↦ encode (⟪ a ⟫↪ m ∈ₛ s)` is recovered as a function, and extensionality
closes the loop.
<!--zh-->
幂集是库文件头亲口否认的那一件构造，而小分类器恰好把它造出来。以**小特征函数** `⟪ a ⟫ → Ω'` 为候选子集的索引；把一个特征函数实现为集合，就是在它选中的成员上做一次 `sett`。娇贵的方向又一次流经不加截断的纤维：从真实的子集 `s` 回收特征函数 `m ↦ encode (⟪ a ⟫↪ m ∈ₛ s)` 是函数操作，外延性收口。
<!--/-->

```agda
module Power (sΩ : HPropSmallness ℓ) where

  private
    decode : sΩ .fst → hProp ℓ
    decode = equivFun (sΩ .snd)

    encode : hProp ℓ → sΩ .fst
    encode = invEq (sΩ .snd)

    decode∘encode : (P : hProp ℓ) → decode (encode P) ≡ P
    decode∘encode = secEq (sΩ .snd)

    F : (a : S) → (⟪ a ⟫ → sΩ .fst) → S
    F a χ = sett (Σ[ m ∈ ⟪ a ⟫ ] ⟨ decode (χ m) ⟩) (λ p → ⟪ a ⟫↪ (p .fst))

  𝒫V : S → S
  𝒫V a = sett (⟪ a ⟫ → sΩ .fst) (F a)

  private
    fwd : (a x : S) → ⟨ x ∈ˢ 𝒫V a ⟩ → ⟨ x ⊆ a ⟩
    fwd a x = PT.rec ((x ⊆ a) .snd) λ { (χ , p) y y∈ₛx →
      PT.rec ((y ∈ₛ a) .snd)
             (λ { ((m , _) , q) → subst (λ v → ⟨ v ∈ₛ a ⟩) q (∈ₛ⟪ a ⟫↪ m) })
             (∈∈ₛ {a = y} {b = F a χ} .snd
               (subst (λ v → ⟨ y ∈ₛ v ⟩) (sym p) y∈ₛx)) }

    bwd : (a x : S) → ⟨ x ⊆ a ⟩ → ⟨ x ∈ˢ 𝒫V a ⟩
    bwd a x sub = ∣ χₓ , extensionality (F a χₓ) x (s1 , s2) ∣₁
      where
      χₓ : ⟪ a ⟫ → sΩ .fst
      χₓ m = encode (⟪ a ⟫↪ m ∈ₛ x)
      s1 : ⟨ F a χₓ ⊆ x ⟩
      s1 y y∈ₛF = PT.rec ((y ∈ₛ x) .snd)
        (λ { ((m , h) , q) →
          subst (λ v → ⟨ v ∈ₛ x ⟩) q
            (subst ⟨_⟩ (decode∘encode (⟪ a ⟫↪ m ∈ₛ x)) h) })
        (∈∈ₛ {a = y} {b = F a χₓ} .snd y∈ₛF)
      s2 : ⟨ x ⊆ F a χₓ ⟩
      s2 y y∈ₛx = ∈∈ₛ {a = y} {b = F a χₓ} .fst ∣ (m₀ , h) , q ∣₁
        where
        m₀ = sub y y∈ₛx .fst
        q : ⟪ a ⟫↪ m₀ ≡ y
        q = equivFun identityPrinciple (sub y y∈ₛx .snd)
        h : ⟨ decode (χₓ m₀) ⟩
        h = subst ⟨_⟩ (sym (decode∘encode (⟪ a ⟫↪ m₀ ∈ₛ x)))
                  (subst (λ v → ⟨ v ∈ₛ x ⟩) (sym q) y∈ₛx)

  power-spec : (a x : S) → (x ∈ˢ 𝒫V a) ≡ (x ⊆ˢ a)
  power-spec a x =
    ⇔toPath {P = x ∈ˢ 𝒫V a} {Q = x ⊆ a} (fwd a x) (bwd a x)
    ∙ ⇔toPath {P = x ⊆ a} {Q = x ⊆ˢ a}
      (λ s y y∈x → ∈∈ₛ {a = y} {b = a} .snd (s y (∈∈ₛ {a = y} {b = x} .fst y∈x)))
      (λ f y y∈ₛx → ∈∈ₛ {a = y} {b = a} .fst (f y (∈∈ₛ {a = y} {b = x} .snd y∈ₛx)))
```

<!--en-->
## Assembly: V ⊨ ZF
<!--zh-->
## 合龙：V ⊨ ZF
<!--/-->

<!--en-->
Given the impredicativity parameter, full separation is the smallness chapter's
pipe with the fare paid by `resizing`{.Agda} instead of a witness, and every field
is on the table. One discipline governs the assembly: each unique-existence field
takes a **library set as its centre**, so that the description operator's
projections compute back to the stock sets by definition. The two pinning
equations for the numeral chain are discharged through the `sucV` case analysis,
riding `numeralV≡#`{.Agda} between the model's chain and the library's.
<!--zh-->
非直谓性参数在手，全分离就是小性章那根水管，票钱由 `resizing`{.Agda} 代替见证付讫，十二个字段至此凑齐。合龙由一条纪律统辖：每个唯一存在字段都以**库存集合为中心**，让摹状词算子的投影按定义算回库存。数码链的两条钉死方程经 `sucV` 分情形装置兑现，其间靠 `numeralV≡#`{.Agda} 在模型链与库链之间往返。
<!--/-->

```agda
module VModel (imp : Impredicativity ℓ) where
  open Impredicativity imp
  open Power hPropSmallness public

  separateFull : (a : S) (φ : Formula S 1)
               → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ ((y ∷ []) ⊨ φ)))
  separateFull a φ =
    separateFromSmall a (λ y → (y ∷ []) ⊨ φ) (λ y → resizing ((y ∷ []) ⊨ φ))

  V⊨ZF-impredicative : isZFModel
  V⊨ZF-impredicative = record
    { extensional    = extensionalV
    ; regularity     = regularityV
    ; hasEmpty       = one _ (∅ , empty-spec)
    ; hasPair        = λ a b → one _ (⁅ a , b ⁆ , pair-spec a b)
    ; hasUnion       = λ a → one _ (⋃ a , union-spec a)
    ; hasSeparation  = λ a φ → one _ (separateFull a φ)
    ; hasReplacement = λ a φ fc → one _ (replaceImage a φ fc , replaceImage-spec a φ fc)
    ; hasPower       = λ a → one _ (𝒫V a , power-spec a)
    ; numeral        = numeralV
    ; numeral-zero   = pin0
    ; numeral-suc    = pinS
    ; hasInfinity    = one _ (ω , ω-specV) }
    where
    pin0 : (z : S) → ⟨ z ∈ˢ numeralV zero ⟩ → Empty.⊥
    pin0 z z∈ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈)
    pinS : (n : ℕ) (z : S)
         → (⟨ z ∈ˢ numeralV (suc n) ⟩ → ⟨ (z ∈ˢ numeralV n) ⊔ (z ≈ˢ numeralV n) ⟩)
         × (⟨ (z ∈ˢ numeralV n) ⊔ (z ≈ˢ numeralV n) ⟩ → ⟨ z ∈ˢ numeralV (suc n) ⟩)
    pinS n z = fwd , bwd
      where
      fwd : ⟨ z ∈ˢ numeralV (suc n) ⟩ → ⟨ (z ∈ˢ numeralV n) ⊔ (z ≈ˢ numeralV n) ⟩
      fwd z∈ = ∈sucV-elim {A = # n} {x = z}
        (snd ((z ∈ˢ numeralV n) ⊔ (z ≈ˢ numeralV n)))
        (subst (λ w → ⟨ z ∈ˢ w ⟩) (numeralV≡# (suc n)) z∈)
        (λ z∈#n → ∣ Sum.inl (subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (numeralV≡# n)) z∈#n) ∣₁)
        (λ z≡#n → ∣ Sum.inr (z≡#n ∙ sym (numeralV≡# n)) ∣₁)
      bwd : ⟨ (z ∈ˢ numeralV n) ⊔ (z ≈ˢ numeralV n) ⟩ → ⟨ z ∈ˢ numeralV (suc n) ⟩
      bwd = PT.rec (snd (z ∈ˢ numeralV (suc n)))
        (λ { (Sum.inl z∈n) → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (numeralV≡# (suc n)))
               (∈sucV-inl {A = # n}
                 (subst (λ w → ⟨ z ∈ˢ w ⟩) (numeralV≡# n) z∈n))
           ; (Sum.inr z≡n) → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (numeralV≡# (suc n)))
               (subst (λ w → ⟨ w ∈ˢ sucV (# n) ⟩) (sym (z≡n ∙ numeralV≡# n))
                 (self∈sucV (# n))) })
    one : (Q : S → hProp (ℓ-suc ℓ)) → SetOf Q → isContr (SetOf Q)
    one = setOf-unique extensionalV
```

<!--en-->
**This is the semantic relative-consistency theorem this part promised**: within
cubical Agda and its universes, granted impredicativity, the cumulative
hierarchy is a model of ZF. The schemas are honoured for **all** formulas at
once; the deep embedding of Part 1 takes its first full load here. The name
carries the exact hypothesis as a suffix, and the unsuffixed headline is the
classical redemption:
<!--zh-->
**这就是本部许诺的语义版相对一致性定理**：在 cubical Agda 及其宇宙之内，给定非直谓性，累积层级是 ZF 的模型。两条模式公理对**所有**公式一次性履约；第一部的深嵌入语法在此第一次满载。定理名以后缀携带精确假设，不带后缀的主打名则是经典赎回版：
<!--/-->

```agda
V⊨ZF : LEM (ℓ-suc ℓ) → isZFModel
V⊨ZF lem = VModel.V⊨ZF-impredicative (lem→impredicativity lem)
```

<!--en-->
## Choice, independently
<!--zh-->
## 选择，另立门户
<!--/-->

<!--en-->
The excluded middle does not prove choice, so upgrading to ZFC costs a genuinely
new assumption: the choice chapter's `SetChoice`{.Agda}. (Recall that the
dependence runs the *other* way, `choice→lem`{.Agda}; the section after this one
cashes exactly that.) Choice is applied only at small member
types, asserting the choice of *indices*, the lowest level at which the
statement makes sense. From it, the model's choice-set axiom follows for **any**
ZF model on this carrier, not just the one assembled above: the proof consumes
nothing about how the model was built, only its `∩` and extensionality, which is
worth savouring, choice here is a structural fact about ZF models on V, not a
constructional accident. The choice set is `sett` over the chosen indices, and
disjointness plus the embedding property pin its intersection with each member
to exactly one point.
<!--zh-->
排中律推不出选择，于是升级到 ZFC 要花一笔真正新的假设：选择章的 `SetChoice`{.Agda}。(请记得依赖关系走的是**另一个**方向，`choice→lem`{.Agda}；下一节兑现的正是它。) 选择只施加在小成员类型上，断言的是**索引**的选择，是这句话有意义的最低层级。由它可得本载体上**任意** ZF 模型的选择集公理，而不只是上面装配的那一个：证明不消费模型的任何构造细节，只用它的 `∩` 与外延性。这一点值得玩味，选择在此是 V 上 ZF 模型的结构性事实，不是构造的偶然。选择集是选中索引上的一次 `sett`，不交性加嵌入性把它与每个成员的交钉死在恰好一点。
<!--/-->

```agda
private
  isSet⟪_⟫ : (a : S) → isSet ⟪ a ⟫
  isSet⟪ a ⟫ = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

  isContrΣ-fromCenter : {P : S → hProp (ℓ-suc ℓ)} (z₀ : S) (p₀ : ⟨ P z₀ ⟩)
                      → ((z : S) → ⟨ P z ⟩ → z₀ ≡ z)
                      → isContr (Σ[ z ∈ S ] ⟨ P z ⟩)
  isContrΣ-fromCenter {P} z₀ p₀ u =
    (z₀ , p₀) , λ w → Σ≡Prop (λ v → snd (P v)) (u (w .fst) (w .snd))

module ChoiceLemma (zf : isZFModel) (ac : SetChoice ℓ) where
  open Model.isZFModel zf using ( _∩_; ∩-spec )

  choice : (a : S)
         → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
         → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
              → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
         → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
              → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
  choice a inh disj = PT.map mk (ac ⟪ a ⟫ isSet⟪ a ⟫ (λ m → ⟪ ⟪ a ⟫↪ m ⟫) pick)
      where
      pick : (m : ⟪ a ⟫) → ∥ ⟪ ⟪ a ⟫↪ m ⟫ ∥₁
      pick m = PT.map
        (λ { (y , y∈) → ∈-asFiber {a = y} {b = ⟪ a ⟫↪ m} y∈ .fst })
        (inh (⟪ a ⟫↪ m) (memb a m))
      mk : ((m : ⟪ a ⟫) → ⟪ ⟪ a ⟫↪ m ⟫)
         → Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
              → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩))
      mk g = c , uniq
        where
        chosen : ⟪ a ⟫ → S
        chosen m = ⟪ ⟪ a ⟫↪ m ⟫↪ (g m)
        c : S
        c = sett ⟪ a ⟫ chosen
        chosen∈ : (m : ⟪ a ⟫) → ⟨ chosen m ∈ˢ ⟪ a ⟫↪ m ⟩
        chosen∈ m = ∈∈ₛ {a = chosen m} {b = ⟪ a ⟫↪ m} .snd (∈ₛ⟪ ⟪ a ⟫↪ m ⟫↪ (g m))
        uniq : (x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)
        uniq x x∈a = isContrΣ-fromCenter {P = λ z → z ∈ˢ (c ∩ x)} z₀ pf₀ uniqz
          where
          mf = ∈-asFiber {a = x} {b = a} x∈a
          m₀ = mf .fst
          z₀ = chosen m₀
          pf₀ : ⟨ z₀ ∈ˢ (c ∩ x) ⟩
          pf₀ = subst ⟨_⟩ (sym (∩-spec c x z₀))
                  ( ∣ m₀ , refl ∣₁
                  , subst (λ w → ⟨ z₀ ∈ˢ w ⟩) (mf .snd) (chosen∈ m₀) )
          uniqz : (z : S) → ⟨ z ∈ˢ (c ∩ x) ⟩ → z₀ ≡ z
          uniqz z pf = PT.rec (setIsSet z₀ z)
              (λ { (m , q) →
                let z∈m : ⟨ z ∈ˢ ⟪ a ⟫↪ m ⟩
                    z∈m = subst (λ w → ⟨ w ∈ˢ ⟪ a ⟫↪ m ⟩) q (chosen∈ m)
                    x≡m : x ≡ ⟪ a ⟫↪ m
                    x≡m = disj x (⟪ a ⟫↪ m) x∈a (memb a m)
                            ∣ z , zcx .snd , z∈m ∣₁
                    m≡m₀ : m ≡ m₀
                    m≡m₀ = isEmbedding→Inj isEmb⟪ a ⟫↪ m m₀
                             (sym x≡m ∙ sym (mf .snd))
                in sym (cong chosen m≡m₀) ∙ q })
              (zcx .fst)
            where
            zcx : ⟨ z ∈ˢ c ⟩ × ⟨ z ∈ˢ x ⟩
            zcx = subst ⟨_⟩ (∩-spec c x z) pf

```

<!--en-->
## V ⊨ ZFC, on choice alone
<!--zh-->
## V ⊨ ZFC：单凭选择
<!--/-->

<!--en-->
The ZFC theorem now assembles from one hypothesis, one instance, with
Diaconescu's theorem paying every other bill. Choice at the truth level
`ℓ-suc ℓ` decides that level's propositions, funding the whole impredicativity
packing; and the same instance, lowered one universe, feeds the choice set. One
choice, at the model's own truth level, is the entire price of `V ⊨ ZFC`. (The
finer accounting stays visible in the pieces: `VModel`{.Agda} charges exactly
impredicativity, `ChoiceLemma`{.Agda} exactly one level of choice; only their
sum is stated here.)
<!--zh-->
ZFC 定理现在由单一假设、单个实例合龙，其余账单全由 Diaconescu 定理代付。真值层 `ℓ-suc ℓ` 上的选择判定该层的命题，付得起整份非直谓性打包；同一份实例降一层宇宙，再喂给选择集。模型自己真值层上的一份选择，就是 `V ⊨ ZFC` 的全部价格。(更细的账目在零件上仍然可见：`VModel`{.Agda} 恰收非直谓性，`ChoiceLemma`{.Agda} 恰收一层选择；此处陈述的只是它们的总和。)
<!--/-->

```agda
V⊨ZFC : SetChoice (ℓ-suc ℓ) → isZFCModel
V⊨ZFC ac = record
  { zf = base ; hasChoice = ChoiceLemma.choice base (lowerSetChoice ac) }
  where
  base : isZFModel
  base = V⊨ZF (choice→lem ac)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The account closes balanced. Empty set, pair, and union were library stock
reshaped by `∈∈ₛ` and `⇔toPath`{.Agda}; replacement came free through `sett`
over untruncated fibers; strong infinity was `ω`'s definition plus one chain
alignment (`numeralV≡#`{.Agda}). The two debts, full separation and power set,
cost exactly Part 0's `Impredicativity`{.Agda} packing: assembly gives
`V⊨ZF-impredicative`{.Agda} at that exact price, the excluded middle redeems it
into the headline `V⊨ZF`{.Agda}, and by Diaconescu the choice interface alone
funds `V⊨ZFC`{.Agda}. The universe that Part 4 will dig inside now exists.
<!--zh-->
账本轧平。空集、配对、并是库存经 `∈∈ₛ` 与 `⇔toPath`{.Agda} 换形；替换沿不加截断的纤维经 `sett` 白得；强无穷是 `ω` 的定义加一次链对齐 (`numeralV≡#`{.Agda})。两笔欠账，全分离与幂集，价格恰为第零部打包的 `Impredicativity`{.Agda}：合龙以此精确价格给出 `V⊨ZF-impredicative`{.Agda}，排中律把它赎回成主打的 `V⊨ZF`{.Agda}，经 Diaconescu 更是单凭选择接口就资助了 `V⊨ZFC`{.Agda}。第四部将要向内开凿的那个宇宙，现在存在了。
<!--/-->
