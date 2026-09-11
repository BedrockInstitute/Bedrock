<!--en-->
# Separation and replacement, in full
<!--zh-->
# 完整的分离与替换
<!--ja-->
# 完全な分出公理と置換公理
<!--/-->

<!--en-->
This chapter derives separation and replacement for arbitrary formulas by
reflecting them to a suitable constructible stage and applying the bounded
constructions already available there.
<!--zh-->
本章把任意公式反射到合适的可构造层，再施用已有的有界构造，从而导出任意公式的分离与替换。
<!--ja-->
本章では任意の論理式を適切な構成可能段階へ反映し、そこで既に得られている有界な構成を適用して、任意の論理式に対する分出公理と置換公理を導く。
<!--/-->

<!--en-->
The separation chapter works with bounded formulas, and the reflection chapters
turn an arbitrary formula into a bounded one at the cost of choosing a stage.
Combining the two completes the two remaining comprehension fields of the
model, for formulas of any complexity.

Separation chooses a stage that reflects the formula and contains its argument. It
applies the bounded tool to the relativized formula, then transports the
answer along reflection inside that stage.

Replacement takes a shorter route through separation. Functionality bounds all
values of the relation in one stage. Full separation then separates out from
that stage the elements related to some member of the argument. The remaining
work is only the exchange of the source and image variables required by the
model field.
<!--zh-->
分离那一章处理的是有界公式；反射诸章则以选定一层为代价，把任意公式化成有界公式。二者结合，即可补全模型剩下的两条概括字段，且对任意复杂度的公式成立。

分离选定一个反射公式和一个装得下实参的层，把有界工具用于相对化后的公式，再沿反射在该层内把结论转移到所需之处。

替换则经分离走一条更短的路：函数性把关系的所有值界在同一层中，完整分离随即从该层分离出那些与实参某个成员相关的元素，剩下的工作只是交换模型字段所要求的来源变元与像变元。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Full {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( con; Formula; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.Relativization using ( relativize; Δ₀-relativize )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset-layer; layer-trans; Lset-mono )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Separation {ℓ} lem
  using ( module FunctionalImage; separateΔ₀ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.FormulaReflection {ℓ} lem using ( mkReflect )

open import Cubical.Data.Unit using ( tt* )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id
```

<!--en-->
## Two small tools
<!--zh-->
## 两件小工具
<!--ja-->
## 二つの補助道具
<!--/-->

<!--en-->
Stage transitivity keeps members inside a chosen level, while the two-variable
renaming swaps source and image positions to match the model record's convention.
<!--zh-->
层的传递性使成员留在所选的层之内，而二元改名交换源与像的位置，以符合模型 record 的约定。
<!--ja-->
段階の推移性により要素は選んだ層に留まり、二変数の改名が始域と像の位置を交換してモデルの record の規約に合わせる。
<!--/-->

<!--en-->
A stage is a transitive set, so membership in the argument puts an element in the
stage as soon as the argument is there. This is the guard used by separation's
reflection transport.

The variable calculus is also needed once. The model states replacement with the
image first and the source second, while the bounded existential binds its source
first. Exchanging two variables is an instance of renaming, and the correctness
theorem says the environments agree, which for a transposition is two
`refl`{.Agda}s.
<!--zh-->
层是传递集，故只要实参落在层里，属于实参的元素也就落在层里；分离沿反射推理时依靠的正是这一点。

此外，还需要用到一次变量演算。模型陈述替换时像在前、源在后，而有界存在先绑定来源。交换两个变量是改名的一个特例，而正确性定理说两个环境彼此一致，对一次对换而言那就是两条 `refl`{.Agda}。
<!--/-->

```agda
private
  transIn : (β : V ℓ) {x y : V ℓ} → ⟨ x ∈ y ⟩ → ⟨ y ∈ Lset β ⟩ → ⟨ x ∈ Lset β ⟩
  transIn β = layer-trans (Lset-layer β)

  swap : Fin 2 → Fin 2
  swap zero    = suc zero
  swap (suc _) = zero

  swapFo : Formula S 2 → Formula S 2
  swapFo = renameFo swap

  swapAgrees : (x z : S) → Ren.Agrees swap (x ∷ z ∷ []) (z ∷ x ∷ [])
  swapAgrees x z zero       = refl
  swapAgrees x z (suc zero) = refl

  ⊨-swap : (φ : Formula S 2) (x z : S)
         → ((x ∷ z ∷ []) ⊨ swapFo φ) ≡ ((z ∷ x ∷ []) ⊨ φ)
  ⊨-swap φ x z = Ren.⊨-rename swap φ (x ∷ z ∷ []) (z ∷ x ∷ []) (swapAgrees x z)
```

<!--en-->
## Separation
<!--zh-->
## 分离
<!--ja-->
## 分出公理
<!--/-->

<!--en-->
`hasSeparationL`{.Agda} reflects an arbitrary unary formula at a stage containing
its argument, separates with the relativized Δ₀ formula, and transports the
result back to the original satisfaction predicate.
<!--zh-->
`hasSeparationL`{.Agda} 在包含其实参的层反射任意一元公式，以相对化后的 Δ₀ 公式分离，再把结果搬回原满足关系谓词。
<!--ja-->
`hasSeparationL`{.Agda} は任意の一変数論理式をその引数を含む段階で反映し、相対化された Δ₀ 論理式で分出した後、結果を元の充足関係の述語へ戻す。
<!--/-->

<!--en-->
Reflect the formula at a stage containing the argument's own earliest stage, so
that the argument is in the stage and, by transitivity, so is every element of
it. Separate with the relativized formula, which is Δ₀ by construction. Then the
two predicates agree pointwise: on the left the membership conjunct is in hand,
so the element is in the stage, so the reflection applies and converts the second
conjunct; on the right the same, backwards.

Predicates are what `SetOf`{.Agda} depends on, so the pointwise agreement is
turned into a path of predicates by function extensionality and transported.
The whole field is that transport applied to the bounded tool.
<!--zh-->
在一个包含实参自身最早层的层上反射那条公式，于是实参落在层里，而经传递性，它的每个元素也落在层里。用相对化后的公式作分离，那按构造是 Δ₀ 的。随后两个谓词逐点一致：左边那个隶属合取项在手，故元素落在层里，故反射适用，把第二个合取项转过去；右边同理，方向相反。

`SetOf`{.Agda} 依赖的正是谓词，故逐点的一致经函数外延性给出谓词的相等，再据此搬运过去；整条字段就是把这次搬运施于那件有界工具。
<!--/-->

```agda
hasSeparationL : (a : S) (φ : Formula S 1)
               → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
hasSeparationL a φ =
  subst (λ Q → isContr (SetOf Q)) (sym Q≡)
    (separateΔ₀ a (relativize c φ) (Δ₀-relativize c φ))
  where
  sa  = stage (fst a) (a .snd)
  R   = mkReflect φ sa (stage-ord (fst a) (a .snd))
  β   = R .fst
  oβ  = R .snd .fst
  c   = LsetS β oβ

  fa∈β : ⟨ fst a ∈ Lset β ⟩
  fa∈β = Lset-mono {α = β} {β = sa} (R .snd .snd .fst)
           (stage-mem (fst a) (a .snd))

  bridge : (x : S) → ⟨ x ∈ˢ a ⟩
         → ((x ∷ []) ⊨ φ) ≡ ((x ∷ []) ⊨ relativize c φ)
  bridge x x∈a = R .snd .snd .snd (x ∷ []) (transIn β x∈a fa∈β , tt*)

  Q≡ : (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ))
     ≡ (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ relativize c φ))
  Q≡ = funExt (λ x → ⇔toPath
    (λ { (x∈a , h) → x∈a , subst ⟨_⟩ (bridge x x∈a) h })
    (λ { (x∈a , h) → x∈a , subst ⟨_⟩ (sym (bridge x x∈a)) h }))
```

<!--en-->
## Where the images live
<!--zh-->
## 诸像所在的层
<!--ja-->
## 像を収める段階
<!--/-->

<!--en-->
Functionality chooses one image for each member of the source set, and the
bounded-image construction supplies a single stage containing all those images.
<!--zh-->
函数性为源集合的每个成员选出唯一的像，而有界像构造给出一个包含全部这些像的单一层。
<!--ja-->
関数性により始集合の各要素に一つの像を選び、有界像の構成がそれらすべての像を含む一つの段階を与える。
<!--/-->

<!--en-->
Replacement's stage has to contain the images too, and functionality is what
makes that possible: each member of the argument has exactly one image, so the
images form a family indexed by the argument's member type, and the bounding
lemma bounds their stages.

The generic functional-image module from the separation chapter performs the
choice, bounds the chosen values, and uses uniqueness to put every related value
under that same bound. This chapter specializes its relation to the variable order
used by the model field.
<!--zh-->
替换的层还须装下诸像，而使之可能的正是函数性：实参的每个成员恰有一个像，故诸像构成一个由实参的成员类型索引的族，而界层引理界住它们的层。

分离一章的通用函数像模块完成选取，并界住所选的诸值；再由唯一性，每个相关值都落在同一个界之下。本章只把这个关系特化为模型字段所用的变元顺序。
<!--/-->

```agda
module Images (a : S) (φ : Formula S 2)
              (fc : (x : S) → ⟨ x ∈ˢ a ⟩
                  → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)) where
  open FunctionalImage a (λ x y → (y ∷ x ∷ []) ⊨ φ) fc public
```

<!--en-->
## Replacement
<!--zh-->
## 替换
<!--ja-->
## 置換公理
<!--/-->

<!--en-->
`hasReplacementL`{.Agda} separates the common image stage by a bounded
existential over the source set and uses the variable swap to match the required
image-first relation.
<!--zh-->
`hasReplacementL`{.Agda} 以源集合上的有界存在式在公共像层上分离，并用变元交换匹配所需的像在前关系。
<!--ja-->
`hasReplacementL`{.Agda} は始集合上の有界存在量化で共通の像段階を分出し、変数交換によって要求される像を先に置く関係へ合わせる。
<!--/-->

<!--en-->
The functional image lies in one stage by the bound above. Separate that stage
by the unary formula saying that some member of `a` is related to the candidate.
The formula uses the transposed matrix because its bound variable comes first in
the environment. Renaming correctness converts it back to the model field's
image-first order.

The two predicates agree directly. A separated member supplies its source
witness after the stage conjunct is discarded. Conversely, a genuine image lies
in the bounding stage, and the same source witnesses the unary formula. Thus full
replacement is a consequence of full separation and the mathematical fact that
a functional image of a set is stage-bounded.

The theorem is sealed at this boundary. Downstream uses need only the replacement
field; unfolding its range bound and nested separation during conversion exhausts
the build's 8 GB heap without exposing any additional mathematical content.
<!--zh-->
由上面的界可知，函数像落在同一层。用一元公式「`a` 的某个成员与候选者相关」在该层上作分离。因为受约束变元在环境中居首，公式使用转置后的矩阵；改名的正确性再把它换回模型字段所用的「像在前」次序。

两个谓词直接相等。分离所得的成员丢开层合取项后，就给出它的来源见证；反过来，一个真正的像落在那个界层中，而同一个来源也见证那条一元公式。因此，完整替换是完整分离与「集合的函数像受一层所界」这条数学事实的推论。

这条定理在此边界封印。下游只需要替换字段；若在转换检查中展开其值域之界与嵌套的分离，会耗尽构建所限的 8 GB 堆，却不显露更多数学内容。
<!--/-->

```agda
opaque
  hasReplacementL : (a : S) (φ : Formula S 2)
                → ((x : S) → ⟨ x ∈ˢ a ⟩
                     → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
                → isContr (SetOf (λ y → ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))
  hasReplacementL a φ fc =
    subst (λ Q → isContr (SetOf Q)) (sym Q≡)
      (hasSeparationL (LsetS βimg βimg-ord) imageFo)
    where
    open Images a φ fc

    Image : S → Ω
    Image y = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))

    imageFo : Formula S 1
    imageFo = ∃̇∈ (con a) (swapFo φ)

    BoundedImage : S → Ω
    BoundedImage y = (y ∈ˢ LsetS βimg βimg-ord) ⊓ ((y ∷ []) ⊨ imageFo)

    Q≡ : Image ≡ BoundedImage
    Q≡ = funExt (λ y → ⇔toPath (into y) (out y))
      where
      into : (y : S) → ⟨ Image y ⟩ → ⟨ BoundedImage y ⟩
      into y = PT.rec (snd (BoundedImage y)) λ { (x , (x∈a , h)) →
        range∈βimg x x∈a y h
        , ∣ x , (x∈a , subst ⟨_⟩ (sym (⊨-swap φ x y)) h) ∣₁ }

      out : (y : S) → ⟨ BoundedImage y ⟩ → ⟨ Image y ⟩
      out y (_ , h) = PT.map (λ { (x , (x∈a , h')) →
        x , (x∈a , subst ⟨_⟩ (⊨-swap φ x y) h') }) h
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
Reflection upgrades the bounded separation and replacement engines to
`hasSeparationL`{.Agda} and `hasReplacementL`{.Agda} for arbitrary formulas.
<!--zh-->
反射把有界分离与替换引擎提升为适用于任意公式的 `hasSeparationL`{.Agda} 与 `hasReplacementL`{.Agda}。
<!--ja-->
反映により有界な分出公理と置換公理の構成を、任意の論理式に対する `hasSeparationL`{.Agda} と `hasReplacementL`{.Agda} へ拡張する。
<!--/-->

<!--en-->
`hasSeparationL`{.Agda} and `hasReplacementL`{.Agda} are the model's two
comprehension fields at `𝒮ʟ`, for arbitrary formulas, with no hypothesis beyond
the excluded middle. Two of the four frontier fields are now established;
the remaining fields are the power set and choice.

Separation reflects an arbitrary formula and applies bounded separation.
Replacement first bounds the range of its functional relation, then applies full
separation to the formula defining that image. Functionality is used exactly in
the range bound; the final collection step is ordinary separation.
<!--zh-->
`hasSeparationL`{.Agda} 与 `hasReplacementL`{.Agda} 是模型在 `𝒮ʟ` 处的两条概括字段，对任意公式成立，除排中律外别无假设。前沿的四项至此完成两项，剩下的是幂集与选择。

分离反射任意公式，再施以有界手段。替换先界住函数关系的值域，再对定义该像的公式施用完整分离。函数性只用于给出值域之界；最后的收集步骤只是普通分离。
<!--/-->
