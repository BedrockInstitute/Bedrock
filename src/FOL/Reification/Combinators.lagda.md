# Combinators

<!--en-->
The factory floor: one combinator per constructor of the object language. Each does
two jobs, gluing the syntax together and composing the input certificates into the
output certificate. The second job costs one line each, and this is the semantics
chapter's faithfulness paying out: `γ ⊨ (φ ∧̇ ψ)` **is**, by definition,
`(γ ⊨ φ) ⊓ (γ ⊨ ψ)`, so the certificate part is a congruence and nothing more. The
whole chapter is generic in the truth algebra, cashing the promise made when
`TruthAlg`{.Agda} was declared law-free: not one algebraic fact is used.
<!--zh-->
车间开工：对象语言一构造子一个组合子。每个组合子做两件事，把语法拼起来，并把输入证书复合成输出证书。第二件事每处只花一行，兑现的正是语义章的忠实性：`γ ⊨ (φ ∧̇ ψ)` **按定义就是** `(γ ⊨ φ) ⊓ (γ ⊨ ψ)`，于是证书部分只剩同余，分毫不多。整章对真值代数泛型，兑现 `TruthAlg`{.Agda} 立为零定律时的许诺：没有用到任何一条代数事实。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.Structure using ( ZFStructure; _^_ )

module FOL.Reification.Combinators {ℓ ℓ'} (𝕋 : TruthAlg ℓ ℓ') (𝒮 : ZFStructure 𝕋)
                                   {ℓc} (K : Type ℓc) (ι : K → ZFStructure.S 𝒮) where

open import FOL.Syntax using
  ( con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Reification.Base 𝕋 𝒮 K ι public
  using ( RepP; RepS; translate; adequacy )

open TruthAlg 𝕋
open ZFStructure 𝒮
```

<!--en-->
## Atoms
<!--zh-->
## 原子
<!--/-->

<!--en-->
Variables and constants are represented by themselves, certificates by
`refl`{.Agda}; the two atomic predicates take term representations on both sides
and compose their certificates by congruence. Note the represented thing of
`≐-rep`{.Agda} is the structure equality `≈ˢ`, exactly as the atom's semantics
prescribes.
<!--zh-->
变量与常量由自身表示，证书是 `refl`{.Agda}；两个原子谓词各吃两侧的词项表示，证书按同余复合。注意 `≐-rep`{.Agda} 的被表示者是结构等词 `≈ˢ`，与原子的语义子句严丝合缝。
<!--/-->

```agda
var-rep : ∀ {n} (i : Fin n) → RepS n (lookup i)
var-rep i = var i , λ γ → refl

const-rep : ∀ {n} (k : K) → RepS n (λ _ → ι k)
const-rep k = con k , λ γ → refl

∈-rep : ∀ {n} {a b : S ^ n → S} → RepS n a → RepS n b
      → RepP n (λ γ → a γ ∈ˢ b γ)
∈-rep (t , h) (u , g) = (t ∈̇ u) , λ γ → cong₂ _∈ˢ_ (h γ) (g γ)

≐-rep : ∀ {n} {a b : S ^ n → S} → RepS n a → RepS n b
      → RepP n (λ γ → a γ ≈ˢ b γ)
≐-rep (t , h) (u , g) = (t ≐ u) , λ γ → cong₂ _≈ˢ_ (h γ) (g γ)
```

<!--en-->
## Connectives
<!--zh-->
## 联结词
<!--/-->

<!--en-->
Six combinators, six congruences. Had the object language derived `∀`, `∨`, `⇒`
classically instead of keeping them primitive, each of the corresponding
combinators would owe an excluded-middle bill here; the primitive constructor set,
chosen back in the syntax chapter, is what keeps this section free.
<!--zh-->
六个组合子，六次同余。若对象语言当初不设 `∀`、`∨`、`⇒` 为原语而走经典派生，此处相应的组合子将各欠一张排中律的账单；语法章选定的全原语构造子集，正是本节免单的原因。
<!--/-->

```agda
∧-rep : ∀ {n} {P Q : S ^ n → Ω} → RepP n P → RepP n Q
      → RepP n (λ γ → P γ ⊓ Q γ)
∧-rep (φ , a) (ψ , b) = (φ ∧̇ ψ) , λ γ → cong₂ _⊓_ (a γ) (b γ)

∨-rep : ∀ {n} {P Q : S ^ n → Ω} → RepP n P → RepP n Q
      → RepP n (λ γ → P γ ⊔ Q γ)
∨-rep (φ , a) (ψ , b) = (φ ∨̇ ψ) , λ γ → cong₂ _⊔_ (a γ) (b γ)

⇒-rep : ∀ {n} {P Q : S ^ n → Ω} → RepP n P → RepP n Q
      → RepP n (λ γ → P γ ⇒ Q γ)
⇒-rep (φ , a) (ψ , b) = (φ ⇒̇ ψ) , λ γ → cong₂ _⇒_ (a γ) (b γ)

¬-rep : ∀ {n} {P : S ^ n → Ω} → RepP n P → RepP n (λ γ → ¬ P γ)
¬-rep (φ , a) = (¬̇ φ) , λ γ → cong ¬_ (a γ)

⊤-rep : ∀ {n} → RepP n (λ _ → ⊤)
⊤-rep = ⊤̇ , λ γ → refl

⊥-rep : ∀ {n} → RepP n (λ _ → ⊥)
⊥-rep = ⊥̇ , λ γ → refl
```

<!--en-->
## Quantifiers
<!--zh-->
## 量词
<!--/-->

<!--en-->
The quantifier combinators demand a body that **already lives in the extended
context**: `RepP (suc n)`. Nothing gets lifted from a shallower context, because
nothing needs to: the atoms are polymorphic in `n`, so every leaf is simply built
at its final depth from the start. The reification workflow makes this free, since
the target predicate is fully known before assembly begins, and with it the depth
of every leaf. This signature is what keeps weakening machinery out of the whole
framework. (`funExt`{.Agda}, a theorem of the host, glues the pointwise
certificates.)
<!--zh-->
量词组合子索要**已经生活在扩展语境**中的公式体：`RepP (suc n)`。没有任何东西要从浅层被提升，因为不需要：原子对 `n` 多态，每片叶子从一开始就在其最终深度构造。reification 的工作流让这一切免费，因为目标谓词在装配开工前完整已知，每片叶子的深度随之确定。正是这个签名把弱化机器挡在了整个框架之外。(宿主的定理 `funExt`{.Agda} 负责把逐点证书粘合起来。)
<!--/-->

```agda
∃-rep : ∀ {n} {P : S ^ suc n → Ω}
      → RepP (suc n) P → RepP n (λ γ → ⋁ S (λ x → P (x ∷ γ)))
∃-rep (φ , a) = (∃̇ φ) , λ γ → cong (⋁ S) (funExt (λ x → a (x ∷ γ)))

∀-rep : ∀ {n} {P : S ^ suc n → Ω}
      → RepP (suc n) P → RepP n (λ γ → ⋀ S (λ x → P (x ∷ γ)))
∀-rep (φ , a) = (∀̇ φ) , λ γ → cong (⋀ S) (funExt (λ x → a (x ∷ γ)))
```

<!--en-->
## Bounded quantifiers
<!--zh-->
## 有界量词
<!--/-->

<!--en-->
The bounded pair additionally eats a term representation for the bound; the
certificate is the bound's congruence plus the body's pointwise certificate. Their
real weight arrives in the next two chapters, where certificates will single these
two constructors out.
<!--zh-->
有界的一对额外吃一份界词项的表示；证书 = 界的同余 + 公式体的逐点证书。它们的真正分量在随后两章到账，那里的证书将把这两个构造子单独挑出来。
<!--/-->

```agda
∀∈-rep : ∀ {n} {a : S ^ n → S} {P : S ^ suc n → Ω}
       → RepS n a → RepP (suc n) P
       → RepP n (λ γ → ⋀ S (λ x → (x ∈ˢ a γ) ⇒ P (x ∷ γ)))
∀∈-rep (t , h) (φ , b) = ∀̇∈ t φ , λ γ → cong (⋀ S) (funExt (λ x →
  cong₂ _⇒_ (cong (x ∈ˢ_) (h γ)) (b (x ∷ γ))))

∃∈-rep : ∀ {n} {a : S ^ n → S} {P : S ^ suc n → Ω}
       → RepS n a → RepP (suc n) P
       → RepP n (λ γ → ⋁ S (λ x → (x ∈ˢ a γ) ⊓ P (x ∷ γ)))
∃∈-rep (t , h) (φ , b) = ∃̇∈ t φ , λ γ → cong (⋁ S) (funExt (λ x →
  cong₂ _⊓_ (cong (x ∈ˢ_) (h γ)) (b (x ∷ γ))))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Twelve constructors, twelve combinators, every certificate a congruence: the
bridge between predicates and formulas promised in the semantics chapter now
stands, and crossing it costs `refl`{.Agda} and `cong`{.Agda}. Not an axiom, not a
law, not a lifting lemma anywhere in sight.
<!--zh-->
十二个构造子，十二个组合子，每张证书一次同余：语义章许诺的谓词与公式之间的桥就此立起，过桥的花费是 `refl`{.Agda} 与 `cong`{.Agda}。目力所及，没有公理，没有定律，没有提升引理。
<!--/-->
