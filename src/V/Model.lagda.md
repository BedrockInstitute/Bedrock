<!--en-->
# The cumulative hierarchy models ZF and ZFC

The cumulative hierarchy satisfies ZF once propositional resizing supplies full separation and a small classifier for propositions supplies power set. Its remaining axioms follow from the hierarchy constructors; an independent set-level choice assumption then upgrades the model to ZFC.
<!--zh-->
# 累积层级是 ZF 与 ZFC 的模型

命题降层提供全分离、命题的小分类器提供幂集后，累积层级满足 ZF。其余公理由层级构造得到；再加入独立的集合层选择假设，模型便升级为 ZFC。
<!--ja-->
# 累積階層は ZF と ZFC のモデル

命題リサイズが完全な分出を、小分類子が冪集合を与えると、累積階層は ZF を満たします。残りの公理は階層の構成から従い、独立な集合レベルの選択の仮定を加えると ZFC のモデルになります。
<!--/-->



```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module V.Model {ℓ : Level} where

open import Base.Impredicativity using ( HPropSmallness; Impredicativity )
open import Base.Classical using ( LEM; lem→impredicativity )
open import Base.Choice using ( SetChoice; choice→lem; lowerSetChoice )
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
import FOL.ZFModel
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

module Model = FOL.ZFModel 𝒮ᵥ
open Model using ( SetOf; _⊆ˢ_; setOf-unique; isZFModel; isZFCModel )

module SemanticsV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemanticsV.At S id using ( _⊨_ )
```

<!--en-->
## The stock sets

Empty set, pair, and union are already available in the library, each with its
axiom. Only the *shape* needs converting, and the same three steps apply every
time: the library states its axiom in small form (`∈ₛ`), `∈∈ₛ`{.Agda} replaces
membership pointwise, and `⇔toPath`{.Agda} rewrites the bi-implication into the path
the record's field requires. For the pair the correspondence is the most direct:
the library's
"equal to `a` or to `b`" *is* the field's `(x ≈ˢ a) ⊔ (x ≈ˢ b)` definitionally,
so the only conversion needed is one layer of `∈∈ₛ`.
<!--zh-->
## 库存集合

空集、配对、并的公理在库中都已具备。需要转换的只是**形状**，而每次都是同样三步：库公理以小形式 (`∈ₛ`) 陈述，`∈∈ₛ`{.Agda} 逐点替换为成员关系，`⇔toPath`{.Agda} 把双蕴含改写成字段所需的路径。配对最为直接：库的「等于 `a` 或等于 `b`」与字段的 `(x ≈ˢ a) ⊔ (x ≈ˢ b)` **定义性相同**，所需的转换只剩一层 `∈∈ₛ`。
<!--ja-->
## 基本的な集合

空集合、対、和集合は階層のライブラリ構成から得られます。小さな所属の特徴付けを通常の所属へ移すと、モデル構造体が要求する仕様になります。
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
For an indexed union, membership reduces to membership in one family member.
These two readings hide the intermediate set and its indexing fiber.
<!--zh-->
对于索引并，成员关系归结为属于某个族元。这两条读式承担中间集合及其索引纤维的转换。
<!--/-->

```agda
union-family-in : (X : Type ℓ) (f : X → S) (i : X) (x : S)
                → ⟨ x ∈ˢ f i ⟩ → ⟨ x ∈ˢ (⋃ (sett X f)) ⟩
union-family-in X f i x h = subst ⟨_⟩ (sym (union-spec (sett X f) x))
  ∣ f i , ∣ i , refl ∣₁ , h ∣₁

union-family-out : (X : Type ℓ) (f : X → S) (x : S)
                 → ⟨ x ∈ˢ (⋃ (sett X f)) ⟩ → ∥ Σ[ i ∈ X ] ⟨ x ∈ˢ f i ⟩ ∥₁
union-family-out X f x h = PT.rec PT.squash₁
  (λ { (v , hv , hx) → PT.map
    (λ { (i , q) → i , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym q) hx }) hv })
  (subst ⟨_⟩ (union-spec (sett X f) x) h)
```

<!--en-->
## Replacement, for free

Replacement is the first surprise of the chapter: a *schema* obtained at no
extra cost. The reason is `sett`{.Agda} itself. Given `φ` functional on `a`, index the
image by the small member type `⟪ a ⟫` and write the image set down directly; no
axiom is used. The delicate direction is recovering an index from a
membership fact, and it uses the method of the smallness chapter once more: the
fibers of `∈-asFiber`{.Agda} are untruncated, so "member to index" is a function,
not a choice.
<!--zh-->
## 替换，免费

替换是本章第一个出人意料的情形：一条**模式**公理，无需付出额外代价。原因就在 `sett`{.Agda} 本身。给定在 `a` 上函数性的 `φ`，以小成员类型 `⟪ a ⟫` 为索引，可以直接写出像集，全程不调用任何公理。较困难的方向是从成员资格回收索引，而这又一次用到小性章的方法：`∈-asFiber`{.Agda} 的纤维不加截断，「从成员到索引」是函数，无需选择。
<!--ja-->
## 置換

関数的な論理式の像は、元の集合の小さな提示で添字付けた `sett`{.Agda} として直接作れます。要素から添字への復元には埋め込みの切り詰められていないファイバーを使うため、選択公理は不要です。
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

The library's `ω` is `sett` over `Lift ℕ` with the library numerals `#` as the
family, so its membership is **definitionally** "merely hit by some `#`": strong
infinity in exactly the record's sense, before any proof is written. What remains
is a check in two steps. First, the model's chain must align with the
library's: `numeralV`{.Agda} steps by `a ∪ ⁅ a , a ⁆` while `#`{.Agda} steps by
`sucV a = a ∪ ⁅ a ⁆s`, and the only genuine gap is `⁅ a , a ⁆ ≡ ⁅ a ⁆s`, one
appeal to extensionality (the two families differ only in index type).
<!--zh-->
## 数码链与 ω

库中的 `ω` 是以库数码 `#` 为族、在 `Lift ℕ` 上构造的 `sett`，所以其成员关系**按定义**就是「仅仅被某个 `#` 命中」；这正是 record 所要求的强无穷，无需另证。剩下两步核对。第一步把模型数码链与库数码链对齐：`numeralV`{.Agda} 按 `a ∪ ⁅ a , a ⁆` 取后继，`#`{.Agda} 按 `sucV a = a ∪ ⁅ a ⁆s` 取后继；唯一差别是 `⁅ a , a ⁆ ≡ ⁅ a ⁆s`，由一次外延性证明，因为两个族只差索引类型。
<!--ja-->
## 数項の列と ω

モデルの後続操作による数項列をライブラリの数項 `#` と同定します。ライブラリの `ω` の所属仕様と合わせることで、強い無限公理に必要な零、後続閉包、有限数項の特徴付けが得られます。
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
第二步，record 的两条固定方程描述的是「后继的成员」，所以本章需要 `sucV` 的分情形分析：`sucV A` 的成员要么是 `A` 的成员、要么等于 `A`，外加两个方向的收纳。证明把 `sucV` 沿并与配对公理展开一次，再用单点集的分类处理第二个析取支。
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

The two pinning equations, for any chain that aligns with the library's.

```agda
module NumPin (a : ℕ → S) (q : (n : ℕ) → a n ≡ # n) where
  pinZero : (z : S) → ⟨ z ∈ˢ a zero ⟩ → Empty.⊥
  pinZero z z∈ = ∅-empty z
    (∈∈ₛ {a = z} {b = ∅} .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (q zero) z∈))

  pinSuc : (n : ℕ) (z : S)
         → (⟨ z ∈ˢ a (suc n) ⟩ → ⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩)
         × (⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩ → ⟨ z ∈ˢ a (suc n) ⟩)
  pinSuc n z = fwd , bwd
    where
    fwd : ⟨ z ∈ˢ a (suc n) ⟩ → ⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩
    fwd z∈ = ∈sucV-elim {A = # n} {x = z}
      (snd ((z ∈ˢ a n) ⊔ (z ≈ˢ a n)))
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (q (suc n)) z∈)
      (λ z∈#n → ∣ Sum.inl (subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (q n)) z∈#n) ∣₁)
      (λ z≡#n → ∣ Sum.inr (z≡#n ∙ sym (q n)) ∣₁)
    bwd : ⟨ (z ∈ˢ a n) ⊔ (z ≈ˢ a n) ⟩ → ⟨ z ∈ˢ a (suc n) ⟩
    bwd = PT.rec (snd (z ∈ˢ a (suc n)))
      (λ { (Sum.inl z∈n) → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (q (suc n)))
             (∈sucV-inl {A = # n} (subst (λ w → ⟨ z ∈ˢ w ⟩) (q n) z∈n))
         ; (Sum.inr z≡n) → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (q (suc n)))
             (subst (λ w → ⟨ w ∈ˢ sucV (# n) ⟩) (sym (z≡n ∙ q n))
               (self∈sucV (# n))) })
```

<!--en-->
## The price of the rest

Two fields remain, full separation and power set, and neither is free: both need
truth values brought down a universe, with no Δ₀ witness available. The required
assumption is exactly the impredicativity packing of `Base.Impredicativity`:
`resizing`{.Agda} compresses
any proposition, and `hPropSmallness`{.Agda} is the small classifier the power
set will be indexed by. None of this is an axiom; the assembly takes the
packing as a parameter, and in the classical case it follows through
`lem→impredicativity`{.Agda}.
<!--zh-->
## 其余部分的价格

还剩两个字段，即全分离与幂集；两者都要求把真值降低一个宇宙层级，而没有 Δ₀ 见证可用。所需假设正是 `Base.Impredicativity` 打包的非直谓性接口：`resizing`{.Agda} 压缩任意命题，`hPropSmallness`{.Agda} 提供幂集用作索引的小分类器。这些都以参数形式给出，并非新增公理；经典情形则通过 `lem→impredicativity`{.Agda} 获得该接口。
<!--ja-->
## 残る公理に必要な仮定

完全な分出と冪集合では、任意の真理値を一段低い宇宙へ移す必要があります。命題リサイズと小分類子をまとめた非可述性の仮定が、ちょうどこの二つを構成するために使われます。
<!--/-->



<!--en-->
## Power set

The power set is the one construction the library's own header disclaims, and the
small classifier is precisely what builds it. Index the candidate subsets by
**small characteristic functions** `⟪ a ⟫ → Ω'`; realizing one as a set is a
`sett` over the members it selects. The delicate direction again runs through
untruncated fibers: from an actual subset `s`, the characteristic function
`m ↦ encode (⟪ a ⟫↪ m ∈ₛ s)` is recovered as a function, and extensionality
closes the loop.
<!--zh-->
## 幂集

幂集是库文件头明确声明不提供的那一件构造，而小分类器恰好能把它构造出来。以**小特征函数** `⟪ a ⟫ → Ω'` 为候选子集的索引；把一个特征函数实现为集合，就是在它选中的成员上做一次 `sett`。较困难的方向又一次经过不加截断的纤维：从真实的子集 `s` 回收特征函数 `m ↦ encode (⟪ a ⟫↪ m ∈ₛ s)` 是函数操作，再由外延性收尾。
<!--ja-->
## 冪集合

小分類子の値を持つ特性関数で、与えられた集合の部分集合を添字付けます。各特性関数を `sett`{.Agda} で実現し、外延性によってすべての部分集合がこの形で得られることを示します。
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

Given the impredicativity parameter, full separation is the construction from the
smallness chapter that builds a set from a small predicate, with
`resizing`{.Agda} supplying the required smallness instead of a Δ₀ witness.
With this, every field is in place. One discipline governs the assembly: each
unique-existence field takes a **library set as its centre**, so that the
description operator's projections compute back to the stock sets by
definition. The two pinning equations for the numeral chain are discharged
through the `sucV` case analysis, with `numeralV≡#`{.Agda} mediating between
the model's chain and the library's.
<!--zh-->
## 合龙：V ⊨ ZF

给定非直谓性参数后，全分离使用小性一章从小谓词构造集合的结果；此处由 `resizing`{.Agda} 提供所需的小性，而不要求 Δ₀ 见证。至此十二个字段齐备。装配遵循同一规则：每个唯一存在字段都以**库存集合为中心**，使摹状词算子的投影按定义回到该集合。数码链的两条固定方程通过 `sucV` 的分情形结果验证，并用 `numeralV≡#`{.Agda} 对应模型数码链与库数码链。
<!--ja-->
## 組み立て：V ⊨ ZF

非可述性の仮定から完全な分出と冪集合を得ると、既に構成した集合と定理が `isZFModel`{.Agda} の全欄を満たします。その結果、累積階層が ZF を満たすことが得られます。
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
    ; numeral-zero   = NumPin.pinZero numeralV numeralV≡#
    ; numeral-suc    = NumPin.pinSuc numeralV numeralV≡#
    ; hasInfinity    = one _ (ω , ω-specV) }
    where
    one : (Q : S → hProp (ℓ-suc ℓ)) → SetOf Q → isContr (SetOf Q)
    one = setOf-unique extensionalV
```

<!--en-->
**This is the semantic relative-consistency theorem this part promised**: within
cubical Agda and its universes, granted impredicativity, the cumulative
hierarchy is a model of ZF. The schemas hold for **all** formulas at once;
the deep embedding of the first-order logic chapters here first comes fully into
play. The name carries the exact hypothesis as a suffix, and the unsuffixed
headline name is the classical version:
<!--zh-->
**这就是本部给出的语义版相对一致性定理**：在 cubical Agda 及其宇宙之内，给定非直谓性，累积层级是 ZF 的模型。两条模式公理对**所有**公式一次成立；一阶逻辑诸章的深嵌入语法在此首次充分发挥作用。定理名以后缀标明精确假设，不带后缀的主打名则是经典版本：
<!--/-->

```agda
V⊨ZF : LEM (ℓ-suc ℓ) → isZFModel
V⊨ZF lem = VModel.V⊨ZF-impredicative (lem→impredicativity lem)
```

<!--en-->
## Choice, independently

The excluded middle does not prove choice, so upgrading to ZFC requires a
genuinely new assumption: the choice chapter's `SetChoice`{.Agda}. (Recall that
the dependence runs the *other* way, `choice→lem`{.Agda}; it is exactly this
result that the section after this one uses.) Choice is applied only at small
member types, asserting the choice of *indices*, the lowest level at which the
statement makes sense. From it, the choice-set axiom follows for **any**
ZF model on this carrier, not just the one assembled above: the proof
uses only the model's `∩` and extensionality, and nothing about how the model
was built. This is worth noting: choice here is a structural fact about
ZF models on V, not an accident of the construction. The choice set is
`sett` over the chosen indices, and disjointness plus the embedding property
pin its intersection with each member to exactly one point.
<!--zh-->
## 选择，另立门户

排中律不能推出选择；要得到 ZFC，还需新的假设 `SetChoice`{.Agda}(选择章)。依赖的另一方向由 `choice→lem`{.Agda} 给出，下一节使用的正是这一结果。选择只作用于小成员类型，断言对**索引**作选择，这是该陈述有意义的最低层级。由此可以证明本载体上**任意** ZF 模型的选择集公理，而不限于前面构造的模型：证明只用模型的 `∩` 与外延性，不依赖其他构造细节。因此，选择在这里是 V 上 ZF 模型的结构性事实。选择集由被选索引上的一次 `sett` 构成；不交性与嵌入性证明它与每个成员的交恰有一点。
<!--ja-->
## 独立な選択

排中律だけでは選択は導けないため、ZFC への拡張では集合レベルの選択を独立に仮定します。階層での選択集合は、各ファイバーから代表を同時に選ぶ関数を用いて構成されます。
<!--/-->



```agda
private
  isSet⟪_⟫ : (a : S) → isSet ⟪ a ⟫
  isSet⟪ a ⟫ = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

  isContrΣ-fromCenter : {P : S → hProp (ℓ-suc ℓ)} (z₀ : S) (p₀ : z₀ ∈ᶜ P)
                      → ((z : S) → z ∈ᶜ P → z₀ ≡ z)
                      → isContr (Σ[ z ∈ S ] (z ∈ᶜ P))
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

The ZFC theorem now assembles from one hypothesis and one instance; everything
else follows from Diaconescu's theorem. Choice at the truth level
`ℓ-suc ℓ` decides that level's propositions, which suffices for the whole
impredicativity packing; and the same instance, lowered one universe, supplies the
choice set. One choice, at the model's own truth level, is all that
`V ⊨ ZFC` requires. (The finer breakdown stays visible in the components:
`VModel`{.Agda} requires exactly impredicativity, `ChoiceLemma`{.Agda} exactly one
level of choice; only their sum is stated here.)
<!--zh-->
## V ⊨ ZFC：单凭选择

至此，ZFC 定理由单一假设、单个实例得到，其余工作由 Diaconescu 定理完成。真值层 `ℓ-suc ℓ` 上的选择判定该层的命题，足以承担整份非直谓性打包；同一实例下降一层宇宙后，又可供选择集使用。模型自身真值层上的一份选择，就是 `V ⊨ ZFC` 所需的全部。(更细的分解在组件层面仍然可见：`VModel`{.Agda} 只需非直谓性，`ChoiceLemma`{.Agda} 只需一层选择；此处陈述的只是二者的总和。)
<!--ja-->
## 選択だけから V ⊨ ZFC

一段高い宇宙での選択は排中律を導き、そこから命題リサイズが得られます。同じ選択仮定が階層の選択公理も与えるため、追加の仮定なしで ZFC のモデルが組み上がります。
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

With this, all the arguments are in place. Empty set, pair, and union were
converted from existing constructions by `∈∈ₛ` and `⇔toPath`{.Agda};
replacement follows directly through `sett` over untruncated fibers; strong
infinity is `ω`'s definition plus one chain alignment
(`numeralV≡#`{.Agda}). The two remaining fields, full separation and power set,
need exactly the `Impredicativity`{.Agda} packing of `Base.Impredicativity`:
assembly gives `V⊨ZF-impredicative`{.Agda} at that exact cost, the excluded middle
upgrades it to the headline `V⊨ZF`{.Agda}, and by Diaconescu the choice
interface alone yields `V⊨ZFC`{.Agda}. The universe that the
constructible-universe chapters will examine from within now exists.
<!--zh-->
## 小结

至此各项论证齐备。空集、配对与并经由 `∈∈ₛ` 和 `⇔toPath`{.Agda} 从既有构造转换而来；替换沿未加截断的纤维经 `sett` 直接得到；强无穷是 `ω` 的定义再加一次链对齐 (`numeralV≡#`{.Agda})。剩下两条，全分离与幂集，所需的恰是基础章节打包的 `Impredicativity`{.Agda}：合龙以此精确代价给出 `V⊨ZF-impredicative`{.Agda}，排中律把它提升为主要的 `V⊨ZF`{.Agda}，再经 Diaconescu，仅凭选择接口便得到 `V⊨ZFC`{.Agda}。可构造宇宙诸章将要向内考察的那个宇宙，至此已经构造完成。
<!--ja-->
## まとめ

命題リサイズから ZF のモデルが得られ、排中律はそのリサイズを導きます。選択からは階層内の選択公理と排中律の両方が得られるため、一つの高い宇宙での選択仮定だけで `V⊨ZFC`{.Agda} が従います。
<!--/-->
