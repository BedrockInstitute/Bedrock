<!--en-->
# Constant bounding

A formula is bounded by a predicate when every constant occurrence satisfies that predicate. These structural certificates support weakening along predicate implication and allow a partially defined constant map to relabel exactly the formulas on which it is defined.
<!--zh-->
# 常元有界性

当公式中每次出现的常元都满足一个谓词时，称该公式受此谓词约束。这些结构化证书可随谓词的蕴含而放宽，并使部分定义的常元映射恰好能对其定义域内的公式作常元改名。
<!--ja-->
# 定数の有界性

論理式に現れる定数がすべて与えられた述語を満たすとき、その論理式はその述語で有界です。この構造的な証明書は述語の含意に沿って弱められ、部分的に定義された定数写像を、その定義域に収まる論理式へ適用できるようにします。
<!--/-->

<!--en-->
This chapter is that certificate. `BoundedFo P φ` records, occurrence by
occurrence, that every constant appearing in `φ` satisfies `P`. It is defined by
the same case analysis as the formula it inspects, so it splits automatically
under pattern matching, and no proof ever has to reason about a list of the
constants of a formula. Being pure syntax, the chapter mentions neither
hierarchies nor stages, and costs nothing.

The companion is monotonicity. A certificate for a narrower predicate is one for
a wider predicate, which is how certificates written against different stages are
brought to a common stage before being used together.
<!--zh-->
本章就是那份证书。`BoundedFo P φ` 逐次出现地记录：`φ` 中出现的每个常元都满足 `P`。它按被检查公式所用的同一套分情形定义，故在模式匹配下自动拆开，任何证明都不必对「公式的常元列表」作推理。由于是纯语法，本章既不提层级也不提阶段，且分文不花。

配套的是单调性。窄谓词的证书就是宽谓词的证书，而这正是把针对不同阶段写下的证书带到公共阶段、以便一并使用的办法。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module FOL.Manipulation.ConstantBounding where

open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo )

open import Cubical.Data.Unit using ( Unit )
```

<!--en-->
## The certificate

`BoundedTm P`{.Agda} and `BoundedFo P`{.Agda} mirror the syntax: constants carry proofs of `P`, variables carry trivial data, and compound formulas pair the certificates of their parts. Pattern matching therefore exposes precisely the evidence needed at each constant occurrence.
<!--zh-->
## 证书

`BoundedTm P`{.Agda} 与 `BoundedFo P`{.Agda} 映照语法：常元携带 `P` 的证明，变量携带平凡数据，复合公式则配对各部分的证书。因此，模式匹配会在每次常元出现处恰好给出所需证据。
<!--ja-->
## 証明書

`BoundedTm P`{.Agda} と `BoundedFo P`{.Agda} は構文をそのまま映します。定数は `P` の証明を持ち、変数は自明なデータを持ち、複合論理式は各部分の証明書を組にします。そのため、パターン照合によって各定数の出現箇所で必要な証拠だけが得られます。
<!--/-->



```agda
BoundedTm : ∀ {ℓk ℓp} {K : Type ℓk} (P : K → Type ℓp) {n} → Term K n → Type ℓp
BoundedTm P (con c) = P c
BoundedTm P (var i) = Lift Unit

BoundedFo : ∀ {ℓk ℓp} {K : Type ℓk} (P : K → Type ℓp) {n} → Formula K n → Type ℓp
BoundedFo P (t ∈̇ u)  = BoundedTm P t × BoundedTm P u
BoundedFo P (t ≐ u)  = BoundedTm P t × BoundedTm P u
BoundedFo P (φ ∧̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P (φ ∨̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P (φ ⇒̇ ψ)  = BoundedFo P φ × BoundedFo P ψ
BoundedFo P ⊥̇        = Lift Unit
BoundedFo P (∃̇ φ)    = BoundedFo P φ
BoundedFo P (∀̇ φ)    = BoundedFo P φ
BoundedFo P (∀̇∈ t φ) = BoundedTm P t × BoundedFo P φ
BoundedFo P (∃̇∈ t φ) = BoundedTm P t × BoundedFo P φ
```

<!--en-->
## Monotonicity

If `P` implies `Q`, every `P`-bounded term or formula is also `Q`-bounded. The proof follows the certificate structure and later lets bounds established at smaller stages be reused at larger stages.
<!--zh-->
## 单调性

若 `P` 蕴含 `Q`，则每个受 `P` 约束的词项或公式也受 `Q` 约束。证明沿证书结构进行，随后可将在较小阶段建立的界复用于较大阶段。
<!--ja-->
## 単調性

`P` が `Q` を含意するなら、`P` で有界な項や論理式は `Q` でも有界です。証明は証明書の構造に従い、後には小さい段階で得た有界性を大きい段階で再利用できます。
<!--/-->



```agda
module _ {ℓk ℓp ℓq} {K : Type ℓk} {P : K → Type ℓp} {Q : K → Type ℓq}
         (P⊆Q : (c : K) → P c → Q c) where

  BoundedTm-mono : ∀ {n} (t : Term K n) → BoundedTm P t → BoundedTm Q t
  BoundedTm-mono (con c) p = P⊆Q c p
  BoundedTm-mono (var i) _ = _

  BoundedFo-mono : ∀ {n} (φ : Formula K n) → BoundedFo P φ → BoundedFo Q φ
  BoundedFo-mono (t ∈̇ u)  (ht , hu) = BoundedTm-mono t ht , BoundedTm-mono u hu
  BoundedFo-mono (t ≐ u)  (ht , hu) = BoundedTm-mono t ht , BoundedTm-mono u hu
  BoundedFo-mono (φ ∧̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono (φ ∨̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono (φ ⇒̇ ψ)  (hφ , hψ) = BoundedFo-mono φ hφ , BoundedFo-mono ψ hψ
  BoundedFo-mono ⊥̇        _         = _
  BoundedFo-mono (∃̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono (∀̇ φ)    hφ        = BoundedFo-mono φ hφ
  BoundedFo-mono (∀̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
  BoundedFo-mono (∃̇∈ t φ) (ht , hφ) = BoundedTm-mono t ht , BoundedFo-mono φ hφ
```

<!--en-->
## Relabelling, partially

A partial map can relabel a bounded formula because its certificate supplies the domain proof at every constant occurrence. The resulting formula agrees after both source and target are mapped into a common type, and its Lévy witness is preserved.
<!--zh-->
## 部分常元改名

部分映射能为有界公式作常元改名，因为证书在每次常元出现处提供定义域证明。将源与目标都映入同一类型后，所得公式与原式相符，并且其 Lévy 见证得以保持。
<!--ja-->
## 部分的な定数の改名

部分写像は、有界性の証明書から各定数の出現箇所で定義域の証明を受け取り、有界な論理式の定数を改名できます。始域と終域を共通の型へ写せば結果は元の論理式と一致し、Lévy の証人も保存されます。
<!--/-->

<!--en-->
The interface is stated in the generality its user needs. Two domains, a common
world they both map into, a predicate on the source, a partial map defined under
it, and the equation saying the partial map agrees with the two projections. In
the intended instance the source is the model's carrier, the target is a stage's
member type, the world is the hierarchy, and the equation is the fact that a
member of a stage, viewed as a set, is the set it was.
<!--zh-->
接口按其使用者所需的一般性陈述：两个域、它们共同映入的一个世界、源上的一个谓词、在该谓词之下有定义的一个部分映射，以及说明该部分映射与两个投影相符的等式。在预期的实例中，源是模型的载体，目标是某个阶段的成员类型，世界是层级，而那条等式就是「阶段的成员作为集合来看，仍是它原本那个集合」这一事实。
<!--/-->

```agda
module Relabel
  {ℓk ℓk' ℓv ℓp : Level}
  {K  : Type ℓk}
  {K' : Type ℓk'}
  {W  : Type ℓv}
  (proj : K → W)
  (up   : K' → W)
  (P    : K → Type ℓp)
  (down : (c : K) → P c → K')
  (down-correct : (c : K) (p : P c) → up (down c p) ≡ proj c)
  where

  liftTm : ∀ {n} (t : Term K n) → BoundedTm P t → Term K' n
  liftTm (con c) p = con (down c p)
  liftTm (var i) _ = var i

  liftFo : ∀ {n} (φ : Formula K n) → BoundedFo P φ → Formula K' n
  liftFo (t ∈̇ u)  (ht , hu) = liftTm t ht ∈̇ liftTm u hu
  liftFo (t ≐ u)  (ht , hu) = liftTm t ht ≐ liftTm u hu
  liftFo (φ ∧̇ ψ)  (hφ , hψ) = liftFo φ hφ ∧̇ liftFo ψ hψ
  liftFo (φ ∨̇ ψ)  (hφ , hψ) = liftFo φ hφ ∨̇ liftFo ψ hψ
  liftFo (φ ⇒̇ ψ)  (hφ , hψ) = liftFo φ hφ ⇒̇ liftFo ψ hψ
  liftFo ⊥̇        _         = ⊥̇
  liftFo (∃̇ φ)    hφ        = ∃̇ liftFo φ hφ
  liftFo (∀̇ φ)    hφ        = ∀̇ liftFo φ hφ
  liftFo (∀̇∈ t φ) (ht , hφ) = ∀̇∈ (liftTm t ht) (liftFo φ hφ)
  liftFo (∃̇∈ t φ) (ht , hφ) = ∃̇∈ (liftTm t ht) (liftFo φ hφ)
```

<!--en-->
Correctness says the relabelling changed nothing that matters: pushing the result
into the common world along one map gives the same formula as pushing the
original along the other. That is the equation the two legs of an absoluteness
argument meet at, and it holds occurrence by occurrence for the reason the
interface demanded.

The Levy witness survives too, since relabelling touches constants and the
witness never looks at them.
<!--zh-->
正确性说这次重标没有改变任何要紧的东西：沿一个映射把结果推进那个共同世界，与沿另一个映射把原式推进去，得到的是同一条公式。那正是绝对性论证的两条腿会合之处的等式，而它逐次出现地成立，理由正是接口所索取的那一条。

Lévy 见证也存活下来，因为重标动的是常元，而见证从不看它们。
<!--/-->

```agda
  liftTm-correct : ∀ {n} (t : Term K n) (h : BoundedTm P t)
                 → mapTm up (liftTm t h) ≡ mapTm proj t
  liftTm-correct (con c) p = cong con (down-correct c p)
  liftTm-correct (var i) _ = refl

  liftFo-correct : ∀ {n} (φ : Formula K n) (h : BoundedFo P φ)
                 → mapFo up (liftFo φ h) ≡ mapFo proj φ
  liftFo-correct (t ∈̇ u) (ht , hu) =
    cong₂ _∈̇_ (liftTm-correct t ht) (liftTm-correct u hu)
  liftFo-correct (t ≐ u) (ht , hu) =
    cong₂ _≐_ (liftTm-correct t ht) (liftTm-correct u hu)
  liftFo-correct (φ ∧̇ ψ) (hφ , hψ) =
    cong₂ _∧̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct (φ ∨̇ ψ) (hφ , hψ) =
    cong₂ _∨̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct (φ ⇒̇ ψ) (hφ , hψ) =
    cong₂ _⇒̇_ (liftFo-correct φ hφ) (liftFo-correct ψ hψ)
  liftFo-correct ⊥̇ _ = refl
  liftFo-correct (∃̇ φ) hφ = cong ∃̇_ (liftFo-correct φ hφ)
  liftFo-correct (∀̇ φ) hφ = cong ∀̇_ (liftFo-correct φ hφ)
  liftFo-correct (∀̇∈ t φ) (ht , hφ) =
    cong₂ ∀̇∈ (liftTm-correct t ht) (liftFo-correct φ hφ)
  liftFo-correct (∃̇∈ t φ) (ht , hφ) =
    cong₂ ∃̇∈ (liftTm-correct t ht) (liftFo-correct φ hφ)

  Δ₀-liftFo : ∀ {n} {φ : Formula K n} (h : BoundedFo P φ) → Δ₀ φ → Δ₀ (liftFo φ h)
  Δ₀-liftFo (ht , hu) δ-∈       = δ-∈
  Δ₀-liftFo (ht , hu) δ-≐       = δ-≐
  Δ₀-liftFo (hφ , hψ) (δ-∧ c d) = δ-∧ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo (hφ , hψ) (δ-∨ c d) = δ-∨ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo (hφ , hψ) (δ-⇒ c d) = δ-⇒ (Δ₀-liftFo hφ c) (Δ₀-liftFo hψ d)
  Δ₀-liftFo _         δ-⊥       = δ-⊥
  Δ₀-liftFo (ht , hφ) (δ-∀∈ c)  = δ-∀∈ (Δ₀-liftFo hφ c)
  Δ₀-liftFo (ht , hφ) (δ-∃∈ c)  = δ-∃∈ (Δ₀-liftFo hφ c)
```

<!--en-->
## Recap

Constant-bounded syntax packages the hypotheses needed by a partial constant map. Monotonicity transports those hypotheses, while `mapFoPartial`{.Agda}, its agreement theorem, and the Lévy preservation lemma perform the certified relabelling.
<!--zh-->
## 小结

常元有界语法封装部分常元映射所需的假设。单调性搬运这些假设，而 `mapFoPartial`{.Agda}、其相符定理与 Lévy 保持引理执行带证书的常元改名。
<!--ja-->
## まとめ

定数の有界性は、部分的な定数写像に必要な仮定をまとめます。単調性がその仮定を移し、`mapFoPartial`{.Agda}、その一致定理、Lévy 保存補題が証明書付きの定数改名を実行します。
<!--/-->
