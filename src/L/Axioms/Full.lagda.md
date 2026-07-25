# Separation and replacement, in full

<!--en-->
The separation chapter carved with bounded formulas, and the reflection chapters
turned an arbitrary formula into a bounded one at the price of naming a stage.
Putting the two together pays the two remaining comprehension fields of the
model, for formulas of any complexity.

The pattern is the same for both. Name a stage that reflects the formula and
contains everything the field will run on. Apply the bounded instrument to the
relativized formula, which is Δ₀. Then transport the answer along the reflection,
which is only valid inside the stage, and so has to be guarded: the guard is the
field's own hypothesis that the element lies in the argument, and the argument
lies in the stage.

Replacement needs one thing more. Its predicate quantifies over an image element
that nothing confines, and the relativized formula, having lost its unbounded
quantifiers, is free to be satisfied by elements outside the stage where the
reflection says nothing. The cure is to confine it explicitly: conjoin to the
matrix the atom saying the image lies in the stage. True images satisfy it
automatically, because the stage was chosen to contain them, so the conjunction
changes no answer while removing every answer the reflection could not certify.
<!--zh-->
分离那一章用有界公式来雕，而反射诸章以点名一个阶段为代价，把任意公式变成有界公式。二者合于一处，就偿付了模型剩下的两条概括字段，且对任意复杂度的公式成立。

两者的套路相同。点名一个阶段，它反射那条公式，并装下该字段将要作用其上的一切。把有界的器械施于相对化后的公式，那是 Δ₀ 的。然后沿反射把答案搬运回来，而反射只在阶段之内成立，故搬运必须设防：防具就是该字段自己的假设，即那个元素属于实参，而实参落在阶段里。

替换还多要一样。它的谓词对一个无人约束的像元作量化，而相对化后的公式既已失去无界量词，就可以被阶段之外的元素满足，而反射在那里什么也没说。补救是显式地把它关起来：给矩阵合取上「像落在该阶段里」这个原子。真正的像自动满足它，因为那个阶段本就选得装下它们，故这次合取不改变任何答案，却删去了反射无法背书的一切答案。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Axioms.Full {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( con; var; Formula; _∈̇_; _∧̇_ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.Relativize using ( relativize; Δ₀-relativize )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd; bound2 )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Separation {ℓ} lem
  using ( ReplImage; separateΔ₀; replaceΔ₀ )
open import L.ReflectFo {ℓ} lem using ( LsetS; mkReflect )

open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )

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
<!--/-->

<!--en-->
A stage is a transitive set, so membership in the argument puts an element in the
stage as soon as the argument is there. That is the guard, and it is used at
every transport below.

And the variable calculus is needed once. The model states replacement with the
image first and the source second; the bounded instrument was written the other
way round, since that is the order in which the recursion produces them.
Exchanging two variables is an instance of renaming, and the correctness theorem
says the environments agree, which for a transposition is two `refl`{.Agda}s.
<!--zh-->
阶段是传递集，故只要实参落在阶段里，属于实参的元素也就落在阶段里。这就是那道防，下面每一次搬运都用它。

以及，变量演算要用一次。模型陈述替换时像在前、源在后，而有界的器械写成了相反的顺序，因为递归正是按那个顺序产出它们的。交换两个变量是变量变换的一个特例，而正确性定理说两个环境彼此一致，对一次对换而言那就是两条 `refl`{.Agda}。
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
<!--/-->

<!--en-->
Reflect the formula at a stage containing the argument's own earliest stage, so
that the argument is in the stage and, by transitivity, so is every element of
it. Separate with the relativized formula, which is Δ₀ by construction. Then the
two predicates agree pointwise: on the left the membership conjunct is in hand,
so the element is in the stage, so the reflection applies and converts the second
conjunct; on the right the same, backwards.

Predicates are what `SetOf`{.Agda} depends on, so the pointwise agreement is
turned into a path of predicates by function extensionality and transported. The
whole field is that transport applied to the bounded instrument.
<!--zh-->
在一个包含实参自身最早阶段的阶段上反射那条公式，于是实参落在阶段里，而经传递性，它的每个元素也落在阶段里。用相对化后的公式作分离，那按构造是 Δ₀ 的。随后两个谓词逐点一致：左边那个隶属合取项在手，故元素落在阶段里，故反射适用，把第二个合取项转过去；右边同理，方向相反。

`SetOf`{.Agda} 依赖的正是谓词，故逐点的一致经函数外延性变成谓词的一条道路，再搬运过去。整条字段就是这次搬运施于那件有界器械。
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
## 诸像住在哪里
<!--/-->

<!--en-->
Replacement's stage has to contain the images too, and functionality is what
makes that possible: each member of the argument has exactly one image, so the
images form a family indexed by the argument's member type, and the bounding
lemma bounds their stages.

The image of a member is read off the centre of the contractible type
functionality provides. It depends on the membership proof as well as the
element, but only apparently: membership is a proposition, so equal elements have
equal images, and the congruence lemma below is what lets an arbitrary element of
the argument be identified with the indexed one that the bound was computed for.
<!--zh-->
替换的阶段还须装下诸像，而使之可能的正是函数性：实参的每个成员恰有一个像，故诸像构成一个由实参的成员类型索引的族，而界层引理界住它们的阶段。

一个成员的像，是从函数性所提供的可缩类型的中心读出来的。它既依赖元素也依赖那份隶属证明，但那只是表面：隶属是命题，故相等的元素有相等的像，而下面这条同余引理，正是使实参的任意元素能与「上界为之算出的」那个带索引的元素认同起来的东西。
<!--/-->

```agda
module Images (a : S) (φ : Formula S 2)
              (fc : (x : S) → ⟨ x ∈ˢ a ⟩
                  → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)) where

  Mem : Type (ℓ-suc ℓ)
  Mem = Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩

  img : Mem → S
  img p = fc (p .fst) (p .snd) .fst .fst

  img-sat : (p : Mem) → ⟨ (img p ∷ p .fst ∷ []) ⊨ φ ⟩
  img-sat p = fc (p .fst) (p .snd) .fst .snd

  img-cong : {p q : Mem} → p .fst ≡ q .fst → img p ≡ img q
  img-cong e = cong img (Σ≡Prop (λ w → snd (w ∈ˢ a)) e)

  img-uniq : (p : Mem) (y : S) → ⟨ (y ∷ p .fst ∷ []) ⊨ φ ⟩ → img p ≡ y
  img-uniq p y h = cong fst (fc (p .fst) (p .snd) .snd (y , h))

  memS : ⟪ fst a ⟫ → Mem
  memS m = (⟪ fst a ⟫↪ m , isL-trans {x = fst a} {y = ⟪ fst a ⟫↪ m} fm∈fa (a .snd))
         , fm∈fa
    where
    fm∈fa : ⟨ ⟪ fst a ⟫↪ m ∈ fst a ⟩
    fm∈fa = ∈∈ₛ {a = ⟪ fst a ⟫↪ m} {b = fst a} .snd (∈ₛ⟪ fst a ⟫↪ m)

  private
    bImg = boundingOrd ⟪ fst a ⟫ (λ m → stage (fst (img (memS m))) (img (memS m) .snd))
             (λ m → stage-ord (fst (img (memS m))) (img (memS m) .snd))

  βimg : V ℓ
  βimg = bImg .fst

  βimg-ord : IsOrd βimg
  βimg-ord = bImg .snd .fst

  img∈βimg : (p : Mem) → ⟨ fst (img p) ∈ Lset βimg ⟩
  img∈βimg p = subst (λ w → ⟨ fst w ∈ Lset βimg ⟩) (img-cong fib)
    (Lset-mono {α = βimg} {β = stage (fst (img (memS m))) (img (memS m) .snd)}
      (bImg .snd .snd m)
      (stage-mem (fst (img (memS m))) (img (memS m) .snd)))
    where
    m : ⟪ fst a ⟫
    m = ∈-asFiber {a = fst (p .fst)} {b = fst a} (p .snd) .fst
    fib : memS m .fst ≡ p .fst
    fib = Σ≡Prop (λ w → (isL w) .snd)
            (∈-asFiber {a = fst (p .fst)} {b = fst a} (p .snd) .snd)
```

<!--en-->
## Replacement
<!--zh-->
## 替换
<!--/-->

<!--en-->
The stage is asked to contain the argument's own stage and the bound on the
images, and the reflection is taken for the transposed formula, since that is the
order the instrument wants. The matrix handed over is the relativized transpose
conjoined with the confinement atom, which is Δ₀ on both sides.

Functionality for that matrix then holds with no residue. Its centre is the image
that functionality already provided, which satisfies the confinement because the
stage contains it; and any other solution satisfies the confinement by
assumption, hence lies in the stage, hence is a genuine solution of the original
formula, hence is the same image. That is exactly what the confinement was added
for: without it a solution outside the stage could not be ruled out, and
uniqueness would fail.

The final transport is the same pointwise argument as for separation, now under
the existential over members: forwards the image is confined by the bound,
backwards it is confined by hypothesis, and in both directions the reflection and
the transposition compose to carry the matrix across.
<!--zh-->
所求的阶段须装下实参自身的阶段与诸像的上界，而反射是对转置后的公式取的，因为那才是器械要的顺序。交出去的矩阵是相对化后的转置式再合取上那个禁闭原子，两侧都是 Δ₀ 的。

对该矩阵的函数性于是毫无余项地成立。它的中心就是函数性早已提供的那个像，它满足禁闭，因为阶段装着它；而任何别的解按假设满足禁闭，因而落在阶段里，因而是原公式的一个真解，因而就是同一个像。这正是当初添上禁闭的用意：没有它，阶段之外的解无法排除，唯一性便会失败。

最后的搬运与分离处的逐点论证相同，只是如今置于对诸成员的存在量词之下：正向由那个上界禁闭，反向由假设禁闭，而两个方向上，反射与转置复合起来把矩阵搬过去。
<!--/-->

```agda
hasReplacementL : (a : S) (φ : Formula S 2)
                → ((x : S) → ⟨ x ∈ˢ a ⟩
                     → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
                → isContr (SetOf (λ y → ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))
hasReplacementL a φ fc =
  subst (λ Q → isContr (SetOf Q)) (sym Q≡) (replaceΔ₀ a ψ dψ fc′)
  where
  open Images a φ fc

  sa  = stage (fst a) (a .snd)
  bδ  = bound2 sa βimg (stage-ord (fst a) (a .snd)) βimg-ord
  R   = mkReflect (swapFo φ) (bδ .fst) (bδ .snd .fst)
  β   = R .fst
  oβ  = R .snd .fst
  δ∈β = R .snd .snd .fst
  c   = LsetS β oβ

  fa∈β : ⟨ fst a ∈ Lset β ⟩
  fa∈β = Lset-mono {α = β} {β = sa}
           (oβ .fst {x = bδ .fst} {y = sa} (bδ .snd .snd .fst) δ∈β)
           (stage-mem (fst a) (a .snd))

  imgβ : (p : Mem) → ⟨ fst (img p) ∈ Lset β ⟩
  imgβ p = Lset-mono {α = β} {β = βimg}
             (oβ .fst {x = bδ .fst} {y = βimg} (bδ .snd .snd .snd) δ∈β)
             (img∈βimg p)

  ψ : Formula S 2
  ψ = relativize c (swapFo φ) ∧̇ (var (suc zero) ∈̇ con c)

  dψ : Δ₀ ψ
  dψ = δ-∧ (Δ₀-relativize c (swapFo φ)) δ-∈

  bridge : (x z : S) → ⟨ x ∈ˢ a ⟩ → ⟨ fst z ∈ Lset β ⟩
         → ((z ∷ x ∷ []) ⊨ φ) ≡ ((x ∷ z ∷ []) ⊨ relativize c (swapFo φ))
  bridge x z x∈a fz∈β =
    sym (⊨-swap φ x z)
    ∙ R .snd .snd .snd (x ∷ z ∷ []) (transIn β x∈a fa∈β , (fz∈β , tt*))

  fc′ : (x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ z ∈ S ] ⟨ (x ∷ z ∷ []) ⊨ ψ ⟩)
  fc′ x x∈a = (img p , centre) , uniq
    where
    p : Mem
    p = x , x∈a
    centre : ⟨ (x ∷ img p ∷ []) ⊨ ψ ⟩
    centre = subst ⟨_⟩ (bridge x (img p) x∈a (imgβ p)) (img-sat p) , imgβ p
    uniq : (r : Σ[ z ∈ S ] ⟨ (x ∷ z ∷ []) ⊨ ψ ⟩) → (img p , centre) ≡ r
    uniq (z , (hrel , fz∈β)) =
      Σ≡Prop (λ w → snd ((x ∷ w ∷ []) ⊨ ψ))
        (img-uniq p z (subst ⟨_⟩ (sym (bridge x z x∈a fz∈β)) hrel))

  Q≡ : (λ y → ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))) ≡ ReplImage a ψ
  Q≡ = funExt (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : S) → ⟨ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((z ∷ x ∷ []) ⊨ φ)) ⟩
        → ⟨ ReplImage a ψ z ⟩
    fwd z = PT.map (λ { (x , (x∈a , h)) →
      let zβ = subst (λ w → ⟨ fst w ∈ Lset β ⟩) (img-uniq (x , x∈a) z h)
                 (imgβ (x , x∈a))
      in x , (x∈a , (subst ⟨_⟩ (bridge x z x∈a zβ) h , zβ)) })
    bwd : (z : S) → ⟨ ReplImage a ψ z ⟩
        → ⟨ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((z ∷ x ∷ []) ⊨ φ)) ⟩
    bwd z = PT.map (λ { (x , (x∈a , (hrel , fz∈β))) →
      x , (x∈a , subst ⟨_⟩ (sym (bridge x z x∈a fz∈β)) hrel) })
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`hasSeparationL`{.Agda} and `hasReplacementL`{.Agda} are the model's two
comprehension fields at `𝒮ʟ`, for arbitrary formulas, with no hypothesis beyond
the excluded middle. The frontier loses two of its four debts, and what remains
is the power set and choice.

Both proofs are one shape: reflect, apply the bounded instrument, transport under
a guard. The only asymmetry is the confinement atom, and the reason for it is
worth remembering, because it is the one place where relativization is not
harmless. Relativizing a formula weakens what it says about anything outside the
stage, so a predicate that quantifies over an unconfined element must say where
that element lives, or it will admit solutions the reflection never promised.
<!--zh-->
`hasSeparationL`{.Agda} 与 `hasReplacementL`{.Agda} 是模型在 `𝒮ʟ` 处的两条概括字段，对任意公式成立，除排中律外别无假设。前沿的四笔债去掉两笔，剩下的是幂集与选择。

两个证明是同一个形状：反射、施以有界器械、设防搬运。唯一的不对称是那个禁闭原子，而它的理由值得记住，因为那是相对化并非无害的唯一之处。把一条公式相对化，就削弱了它对阶段之外任何东西所说的话，故凡对一个不受禁闭的元素作量化的谓词，都必须说清那个元素住在哪里，否则它会准入反射从未承诺过的解。
<!--/-->
