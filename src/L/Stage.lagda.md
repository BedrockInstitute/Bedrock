<!--en-->
# The index of the least constructible stage

Every constructible set `x` belongs to `Lset α`{.Agda} for a least ordinal α. Here α is the index, `Lset α` is the stage, and the entire ordinal-indexed family is the constructible hierarchy. Well-founded descent produces the least index from any witness, ordinal comparison proves it unique, and `stage x hx`{.Agda} names the resulting α.
<!--zh-->
# 最小可构造阶段的索引

每个可构造集合 `x` 都属于某个 `Lset α`{.Agda}，且这样的序数 α 中有一个最小者。这里 α 是索引，`Lset α` 是阶段，而由所有序数索引的整族才是可构造层级。良基下降从任意见证得到最小索引，序数比较证明其唯一，而 `stage x hx`{.Agda} 为所得的 α 命名。
<!--ja-->
# 最小の構成可能段階の添字

各構成可能集合 `x` は、ある最小の順序数 α に対する `Lset α`{.Agda} に属します。ここで α は添字、`Lset α` は段階であり、順序数で添字付けられた族全体が構成可能階層です。整礎的な降下が任意の証人から最小の添字を与え、順序数の比較がその一意性を示し、`stage x hx`{.Agda} が得られた α を名付けます。
<!--/-->

<!--en-->
Two things have to be shown. That a least stage exists, which is a descent: start
from any stage that works and ask whether a smaller one also works; if so recurse,
and membership is well founded so the recursion stops. And that it is unique,
which is trichotomy: two least stages cannot be strictly ordered either way, so
they are equal.

Neither argument looks at what the property says. So the chapter proves them for
an arbitrary property of ordinals and reads the stage function off as the
instance, which costs nothing here and pays later: a canonical *choice* of
ordinal is a thing several constructions want, and each one that gets it this way
is one that does not need a well-ordering of L to get it.

Both are classical, for reasons already seen. The descent asks, at each step, a
question about an arbitrary set, and uniqueness is comparison. So the least
ordinal joins the classical cone, and the chapter is the third and last place
the excluded middle enters the L-side machinery.
<!--zh-->
要证的有两件。最小阶段存在，那是一次下降：从任何合用的阶段出发，问是否有更小的也合用；若有则递归，而成员关系良基，故递归会停。以及它唯一，那是三歧：两个最小阶段无论哪个方向都不能严格相比，故它们相等。

两个论证都不看那条性质说了什么。故本章对任意的序数性质来证，再把阶段函数作为实例读出：此处不费分文，而日后有偿：序数的一个典范**选取**是若干构造都想要的东西，而每个由此获得它的构造，即一个无须 L 的良序即可得到它的构造。

两件都是经典的，理由前面已经见过。下降在每一步问的是关于任意集合的问题，而唯一性是比较。于是最小序数加入经典锥，本章是排中律进入 L 侧机器的第三处、也是最后一处。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Stage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd; Lset; isL )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The least ordinal satisfying a property

For a property `P` of ordinals, `LeastOrd P`{.Agda} packages an ordinal α satisfying `P` together with the proof that no smaller ordinal satisfies it. This definition concerns the ordinal index itself; only the later specialization `P σ = (x ∈ Lset σ)` turns such an index into the index of a constructible stage.
<!--zh-->
## 满足性质的最小序数

对于序数性质 `P`，`LeastOrd P`{.Agda} 把满足 `P` 的序数 α 与「没有更小序数满足 `P`」的证明组成一包。这个定义谈的是序数索引本身；直到稍后取 `P σ = (x ∈ Lset σ)`，这样的索引才成为某个可构造阶段的索引。
<!--ja-->
## 性質を満たす最小の順序数

順序数の性質 `P` に対して、`LeastOrd P`{.Agda} は `P` を満たす順序数 α と、それより小さい順序数は `P` を満たさないという証明を組にします。この定義が扱うのは順序数の添字そのものであり、後で `P σ = (x ∈ Lset σ)` と特殊化して初めて構成可能段階の添字になります。
<!--/-->

<!--en-->
Uniqueness is where the property's being an `hProp`{.Agda} earns its keep: the
two candidates are compared by trichotomy, each strict direction is refuted by
the other's minimality, and the remaining components are propositions, so the
equality of the ordinals is the equality of the packages.
<!--zh-->
唯一性正是那条性质取值于 `hProp`{.Agda} 的用武之处：两个候选由三歧比较，每个严格方向都被对方的极小性反驳，而其余分量都是命题，故序数相等即是整包相等。
<!--/-->

```agda
module _ (P : S → Ω) where

  isLeastOrd : S → Type (ℓ-suc ℓ)
  isLeastOrd α = (γ : S) → IsOrd γ → ⟨ P γ ⟩ → ⟨ γ ∈ˢ α ⟩ → Empty.⊥

  LeastOrd : Type (ℓ-suc ℓ)
  LeastOrd = Σ[ α ∈ S ] (IsOrd α × ⟨ P α ⟩ × isLeastOrd α)

  isPropLeastOrd : isProp LeastOrd
  isPropLeastOrd (α , ordα , pα , leastα) (α' , ordα' , pα' , leastα') =
    Σ≡Prop propRest α≡α'
    where
    decide : (⟨ α ∈ˢ α' ⟩ ⊎ ((α ≡ α') ⊎ ⟨ α' ∈ˢ α ⟩)) → α ≡ α'
    decide (inl α∈α')       = Empty.rec (leastα' α ordα pα α∈α')
    decide (inr (inl e))    = e
    decide (inr (inr α'∈α)) = Empty.rec (leastα α' ordα' pα' α'∈α)
    α≡α' : α ≡ α'
    α≡α' = decide (ord-tri α ordα α' ordα')
    propRest : (β : S) → isProp (IsOrd β × ⟨ P β ⟩ × isLeastOrd β)
    propRest β = isProp× (isPropIsOrd β)
      (isProp× (snd (P β))
        (isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Empty.isProp⊥))
```

<!--en-->
## Descent to the least ordinal

Starting from any ordinal satisfying `P`, `leastOrdBelow`{.Agda} asks whether a strictly smaller ordinal also satisfies `P` and recurses when one does. Well-foundedness of membership makes this descent terminate at the least ordinal satisfying `P`, before the construction is specialized to constructible stages.
<!--zh-->
## 下降到最小序数

从任一满足 `P` 的序数出发，`leastOrdBelow`{.Agda} 询问是否有严格更小的序数也满足 `P`，若有便递归下降。成员关系的良基性使下降终止于满足 `P` 的最小序数；此时构造尚未特化到可构造阶段。
<!--ja-->
## 最小の順序数への降下

`P` を満たす任意の順序数から始め、`leastOrdBelow`{.Agda} は、それより小さく `P` を満たす順序数があれば再帰的にそこへ降ります。所属関係の整礎性により、この降下は `P` を満たす最小の順序数で停止します。この時点ではまだ構成可能段階への特殊化は行いません。
<!--/-->

<!--en-->
The result being a proposition, the starting ordinal may be given truncated, and
that is the form the callers have: they know a suitable ordinal exists without
having chosen one.
<!--zh-->
结果既是命题，起始序数便可以截断的形式给出，而这正是诸调用方手上的形式：它们知道合用的序数存在，却未曾选定一个。
<!--/-->

```agda
  leastOrdBelow : (α : S) → IsOrd α → ⟨ P α ⟩ → LeastOrd
  leastOrdBelow = ∈-induction step
    where
    step : (α : S) → (∀ β → ⟨ β ∈ˢ α ⟩ → IsOrd β → ⟨ P β ⟩ → LeastOrd)
         → IsOrd α → ⟨ P α ⟩ → LeastOrd
    step α IH ordα pα = decide (lem Smaller)
      where
      Smaller : hProp (ℓ-suc ℓ)
      Smaller = ∃[ β ∶ S ] ((β ∈ˢ α) ⊓ ((IsOrd β , isPropIsOrd β) ⊓ P β))
      decide : (⟨ Smaller ⟩ ⊎ (⟨ Smaller ⟩ → Empty.⊥)) → LeastOrd
      decide (inl ∃β) = PT.rec isPropLeastOrd
        (λ { (β , (β∈α , (ordβ , pβ))) → IH β β∈α ordβ pβ }) ∃β
      decide (inr ¬∃β) = α , ordα , pα , leastProof
        where
        leastProof : isLeastOrd α
        leastProof γ ordγ pγ γ∈α = ¬∃β ∣ γ , (γ∈α , (ordγ , pγ)) ∣₁

  leastOrd : ∥ (Σ[ α ∈ S ] (IsOrd α × ⟨ P α ⟩)) ∥₁ → LeastOrd
  leastOrd = PT.rec isPropLeastOrd
    (λ { (α , (ordα , pα)) → leastOrdBelow α ordα pα })
```

<!--en-->
## The stage-index function

For `P σ = (x ∈ Lset σ)`, the descent returns the least ordinal index α whose stage `Lset α`{.Agda} contains `x`. The function `stage`{.Agda} selects α, `stage-ord`{.Agda} proves that it is an ordinal, and `stage-mem`{.Agda} and `stage-earliest`{.Agda} relate that index to its stage.
<!--zh-->
## 阶段索引函数

取 `P σ = (x ∈ Lset σ)` 后，下降得到最小序数索引 α，使阶段 `Lset α`{.Agda} 包含 `x`。函数 `stage`{.Agda} 选出 α，`stage-ord`{.Agda} 证明它是序数，`stage-mem`{.Agda} 与 `stage-earliest`{.Agda} 则把这个索引与相应阶段联系起来。
<!--ja-->
## 段階の添字を返す関数

`P σ = (x ∈ Lset σ)` とすると、降下は `x` を含む段階 `Lset α`{.Agda} の最小の順序数添字 α を返します。関数 `stage`{.Agda} が α を選び、`stage-ord`{.Agda} はそれが順序数であることを、`stage-mem`{.Agda} と `stage-earliest`{.Agda} はその添字と対応する段階との関係を示します。
<!--/-->

<!--en-->
The function is sealed. It unfolds to a well-founded recursion whose steps
mention the tower, and every later type mentioning a stage would otherwise drag
that unfolding into conversion; the three projections open the seal exactly once
each, and no consumer needs it open again.
<!--zh-->
这个函数被封印。它的展开是一次良基递归，其步进提到那座塔，而此后每个提到阶段的类型都会把那次展开拖进转换检查；三个投影各开封一次，而没有任何消费方需要再开封。
<!--/-->

```agda
theEarliest : (x : S) → ⟨ isL x ⟩ → LeastOrd (λ σ → x ∈ˢ Lset σ)
theEarliest x = leastOrd (λ σ → x ∈ˢ Lset σ)

opaque
  stage : (x : S) → ⟨ isL x ⟩ → S
  stage x p = theEarliest x p .fst

opaque
  unfolding stage
  stage-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (stage x p)
  stage-ord x p = theEarliest x p .snd .fst

  stage-mem : (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset (stage x p) ⟩
  stage-mem x p = theEarliest x p .snd .snd .fst

  stage-earliest : (x : S) (p : ⟨ isL x ⟩)
                 → isLeastOrd (λ σ → x ∈ˢ Lset σ) (stage x p)
  stage-earliest x p = theEarliest x p .snd .snd .snd
```

<!--en-->
## Recap

`leastOrd`{.Agda} extracts the least ordinal satisfying a property from a truncated existence witness. Its specialization `stage x hx`{.Agda} returns the ordinal index α of the least `Lset α`{.Agda} containing `x`; `stage-ord`{.Agda}, `stage-mem`{.Agda}, and `stage-earliest`{.Agda} state exactly those facts. Later arguments can therefore compare or bound these ordinal indices and then use the corresponding constructible stages.
<!--zh-->
## 小结

`leastOrd`{.Agda} 从截断的存在见证中提取满足某条性质的最小序数。其特例 `stage x hx`{.Agda} 返回包含 `x` 的最小 `Lset α`{.Agda} 的序数索引 α；`stage-ord`{.Agda}、`stage-mem`{.Agda} 与 `stage-earliest`{.Agda} 精确陈述这些事实。后续论证因而可以比较或约束这些序数索引，再使用对应的可构造阶段。
<!--ja-->
## まとめ

`leastOrd`{.Agda} は、ある性質を満たす順序数が存在するという切り詰められた証人から、その最小の順序数を取り出します。その特殊化 `stage x hx`{.Agda} は `x` を含む最小の `Lset α`{.Agda} の順序数添字 α を返し、`stage-ord`{.Agda}、`stage-mem`{.Agda}、`stage-earliest`{.Agda} がその事実を正確に述べます。後の議論では、これらの順序数添字を比較または上から抑えてから、対応する構成可能段階を使えます。
<!--/-->
