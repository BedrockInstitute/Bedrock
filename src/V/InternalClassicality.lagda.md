<!--en-->
# Internal classicality of the cumulative hierarchy

This chapter isolates the classical principle actually visible to the deeply
embedded language. It assumes excluded middle only for satisfaction judgments
in the cumulative hierarchy and reconstructs the two formerly impredicative
fields, full separation and power set, from Boolean characteristic functions.
<!--zh-->
# 累积层级的内部经典性

本章分离出深嵌入语言实际可见的经典原理。我们只假设累积层级中的满足判断满足排中律，再用布尔特征函数重建先前依赖非直谓性的完整分离与幂集。
<!--ja-->
# 累積階層の内部古典性

本章では、深く埋め込まれた言語から実際に見える古典原理を切り分ける。累積階層における充足判定についてのみ排中律を仮定し、ブール特性関数から完全な分出と冪集合を再構成する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module V.InternalClassicality {ℓ : Level} where

open import Base.Impredicativity using ( hasSize )
open import FOL.Syntax using ( Formula; con; _∈̇_; _∨̇_; ¬̇_ )
open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Semantics
import FOL.ZFModel

open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Bool.Properties using ( isSetBool; false≢true )
open import Cubical.Foundations.Equiv using ( equivFun )
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
open import Cubical.Functions.Logic using ( ⊔-elim; Decₚ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; identityPrinciple; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅; ⁅_,_⁆; ⋃_; ω )

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; regularityV )
open import V.Smallness {ℓ} using ( separateFromSmall )
open hPropStructure 𝒮ᵥ
module Model = FOL.ZFModel 𝒮ᵥ
open Model using ( SetOf; _⊆ˢ_; setOf-unique; isZFModel )
module SemanticsV = FOL.Semantics 𝒮ᵥ
open SemanticsV using ( _^_ )
open SemanticsV.At S id using ( _⊨_ )
```

<!--en-->
Internal excluded middle is stated entirely in the object-language syntax:
every environment satisfies `φ ∨̇ ¬̇ φ`. Its disjunction semantics is
propositionally truncated. Decisions of a proposition are themselves a
proposition, so the truncation may be eliminated into a decision without
strengthening the assumption.
<!--zh-->
内部排中律完全用对象语言语法陈述：每个环境都满足 `φ ∨̇ ¬̇ φ`。析取的语义带命题截断；而一个命题的判定本身仍是命题，所以可以把该截断消去到判定中，并未加强假设。
<!--ja-->
内部排中律は対象言語の構文だけで述べる。すなわち、各環境が `φ ∨̇ ¬̇ φ` を満たすと仮定する。選言の意味論は命題的に切り詰められているが、命題の判定はそれ自体が命題なので、仮定を強めずにその切り詰めを判定へ消去できる。
<!--/-->

```agda
InternalLEMᵥ : Type (ℓ-suc ℓ)
InternalLEMᵥ =
  ∀ {n} (φ : Formula S n) (γ : S ^ n) → ⟨ γ ⊨ (φ ∨̇ ¬̇ φ) ⟩

module InternalModel (classical : InternalLEMᵥ) where

  satisfaction-decide : ∀ {n} (φ : Formula S n) (γ : S ^ n)
                      → Dec ⟨ γ ⊨ φ ⟩
  satisfaction-decide φ γ =
    ⊔-elim (γ ⊨ φ) (γ ⊨ ¬̇ φ) (λ _ → Decₚ (γ ⊨ φ))
      yes (λ np → no (λ p → lower (np p))) (classical φ γ)
```

<!--en-->
A decided proposition has a small representative: truth when the decision is
positive and falsity when it is negative. This supplies precisely the pointwise
smallness required by the existing separation adapter.
<!--zh-->
已判定的命题有一个小代表：肯定支取真，否定支取假。这正好给出现有分离适配器所需的逐点小性。
<!--ja-->
判定された命題は、肯定の場合は真、否定の場合は偽という小さな代表を持つ。これが既存の分出アダプタの必要とする各点での小さを与える。
<!--/-->

```agda
  decided-size : (P : hProp (ℓ-suc ℓ)) → Dec ⟨ P ⟩ → hasSize ℓ P
  decided-size P (yes p) = ⊤ , isoToEquiv (iso (λ _ → tt*) (λ _ → p)
    (λ _ → refl) (λ q → ⟨ P ⟩isProp _ q))
  decided-size P (no np) = (⊥* , isProp⊥*) , isoToEquiv (iso (λ p → lift (np p)) ⊥*-rec
    (λ b → ⊥*-rec b) (λ p → ⊥₀-rec (np p)))

  separateFull : (a : S) (φ : Formula S 1)
               → Σ[ s ∈ S ] (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ a) ⊓ ((y ∷ []) ⊨ φ)))
  separateFull a φ = separateFromSmall a (λ y → (y ∷ []) ⊨ φ)
    (λ y → decided-size ((y ∷ []) ⊨ φ) (satisfaction-decide φ (y ∷ [])))
```

<!--en-->
For power set, a bit records whether a presented element belongs to a candidate
subset. Atomic internal excluded middle decides the corresponding membership,
and the small-membership bridge transfers that decision to the presentation.
<!--zh-->
对幂集而言，一个位记录被呈现元素是否属于候选子集。内部排中律判定相应的原子成员公式，小成员桥再把判定转到呈现上。
<!--ja-->
冪集合では、一つのビットが、呈示された要素が候補の部分集合に属するかを記録する。内部排中律が対応する原子的帰属論理式を判定し、小所属の橋がその判定を呈示へ移す。
<!--/-->

```agda
  bit : (P : hProp ℓ) → Dec ⟨ P ⟩ → Bool
  bit P (yes _) = true
  bit P (no _)  = false

  bit-sound : (P : hProp ℓ) (d : Dec ⟨ P ⟩)
            → (Lift {j = ℓ} (bit P d ≡ true) ,
               isOfHLevelLift 1 (isSetBool (bit P d) true)) ≡ P
  bit-sound P (yes p) = ⇔toPath (λ _ → p) (λ _ → lift refl)
  bit-sound P (no np) = ⇔toPath
    (λ e → ⊥₀-rec (false≢true (lower e)))
    (λ p → ⊥₀-rec (np p))

  member-decide : (a x : S) (m : ⟪ a ⟫) → Dec ⟨ ⟪ a ⟫↪ m ∈ₛ x ⟩
  member-decide a x m with satisfaction-decide (con (⟪ a ⟫↪ m) ∈̇ con x) []
  ... | yes h = yes (∈∈ₛ .fst h)
  ... | no nh = no (λ h → nh (∈∈ₛ .snd h))

  decode : Bool → hProp ℓ
  decode b = Lift (b ≡ true) , isOfHLevelLift 1 (isSetBool b true)

  F : (a : S) → (⟪ a ⟫ → Bool) → S
  F a χ = sett (Σ[ m ∈ ⟪ a ⟫ ] ⟨ decode (χ m) ⟩) (λ p → ⟪ a ⟫↪ (p .fst))

  powerV : S → S
  powerV a = sett (⟪ a ⟫ → Bool) (F a)
```

<!--en-->
Every Boolean-selected set is a subset of `a`. Conversely, a subset supplies
its characteristic function by the atomic decisions above; extensionality then
identifies the selected set with the original subset.
<!--zh-->
每个由布尔函数选出的集合都是 `a` 的子集。反过来，一个子集经上述原子判定给出它的特征函数；外延性随即把被选集合与原子集等同。
<!--ja-->
ブール関数で選ばれた集合はすべて `a` の部分集合である。逆に、部分集合は上の原子的判定から特性関数を与え、外延性により選択された集合と元の部分集合が同一視される。
<!--/-->

```agda
  power-fwd : (a x : S) → ⟨ x ∈ˢ powerV a ⟩ → ⟨ x ⊆ a ⟩
  power-fwd a x = rec₁ (⟨ x ⊆ a ⟩isProp) λ { (χ , p) y y∈ₛx →
    rec₁ (⟨ y ∈ₛ a ⟩isProp)
      (λ { ((m , _) , q) → subst (λ v → ⟨ v ∈ₛ a ⟩) q (∈ₛ⟪ a ⟫↪ m) })
      (∈∈ₛ {a = y} {b = F a χ} .snd
        (subst (λ v → ⟨ y ∈ₛ v ⟩) (sym p) y∈ₛx)) }

  power-bwd : (a x : S) → ⟨ x ⊆ a ⟩ → ⟨ x ∈ˢ powerV a ⟩
  power-bwd a x sub = ∣ χ , extensionality (F a χ) x (left , right) ∣₁
    where
    χ : ⟪ a ⟫ → Bool
    χ m = bit (⟪ a ⟫↪ m ∈ₛ x) (member-decide a x m)

    left : ⟨ F a χ ⊆ x ⟩
    left y h = rec₁ (⟨ y ∈ₛ x ⟩isProp)
      (λ { ((m , e) , q) → subst (λ v → ⟨ v ∈ₛ x ⟩) q
        (subst ⟨_⟩ (bit-sound (⟪ a ⟫↪ m ∈ₛ x) (member-decide a x m)) e) })
      (∈∈ₛ {a = y} {b = F a χ} .snd h)

    right : ⟨ x ⊆ F a χ ⟩
    right y h = ∈∈ₛ {a = y} {b = F a χ} .fst ∣ (m , e) , q ∣₁
      where
      m = sub y h .fst
      q = equivFun identityPrinciple (sub y h .snd)
      e : ⟨ decode (χ m) ⟩
      e = subst ⟨_⟩ (sym (bit-sound (⟪ a ⟫↪ m ∈ₛ x) (member-decide a x m)))
        (subst (λ v → ⟨ v ∈ₛ x ⟩) (sym q) h)

  power-spec : (a x : S) → (x ∈ˢ powerV a) ≡ (x ⊆ˢ a)
  power-spec a x =
    ⇔toPath {P = x ∈ˢ powerV a} {Q = x ⊆ a} (power-fwd a x) (power-bwd a x)
    ∙ ⇔toPath {P = x ⊆ a} {Q = x ⊆ˢ a}
      (λ s y h → ∈∈ₛ {a = y} {b = a} .snd
        (s y (∈∈ₛ {a = y} {b = x} .fst h)))
      (λ f y h → ∈∈ₛ {a = y} {b = a} .fst
        (f y (∈∈ₛ {a = y} {b = x} .snd h)))
```

<!--en-->
The remaining ZF fields reuse their constructive witnesses. Thus the final
record consumes only internal excluded middle.
<!--zh-->
余下的 ZF 字段复用它们的构造性见证。因而最终 record 只消耗内部排中律。
<!--ja-->
残りの ZF の欄は構成的な証拠を再利用する。したがって最終的な record が消費するのは内部排中律だけである。
<!--/-->

```agda
  open import V.Model {ℓ}
    using ( empty-spec; pair-spec; union-spec; replaceImage; replaceImage-spec
          ; numeralV; numeralV≡#; ω-specV; module NumPin )

  V⊨ZF-internal : isZFModel
  V⊨ZF-internal = record
    { extensional    = extensionalV
    ; regularity     = regularityV
    ; hasEmpty       = one _ (∅ , empty-spec)
    ; hasPair        = λ a b → one _ (⁅ a , b ⁆ , pair-spec a b)
    ; hasUnion       = λ a → one _ (⋃ a , union-spec a)
    ; hasSeparation  = λ a φ → one _ (separateFull a φ)
    ; hasReplacement = λ a φ fc → one _ (replaceImage a φ fc , replaceImage-spec a φ fc)
    ; hasPower       = λ a → one _ (powerV a , power-spec a)
    ; numeral        = numeralV
    ; numeral-zero   = NumPin.pinZero numeralV numeralV≡#
    ; numeral-suc    = NumPin.pinSuc numeralV numeralV≡#
    ; hasInfinity    = one _ (ω , ω-specV) }
    where
    one : (Q : S → hProp (ℓ-suc ℓ)) → SetOf Q → isContr (SetOf Q)
    one = setOf-unique extensionalV

V⊨ZF : InternalLEMᵥ → isZFModel
V⊨ZF classical = InternalModel.V⊨ZF-internal classical
```
