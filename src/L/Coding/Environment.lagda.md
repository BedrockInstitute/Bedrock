# Environments as sets

<!--en-->
A certificate that talks about satisfaction has to talk about environments, and
an environment is a function from variable indices to sets. Functions are not
sets of the hierarchy, so this chapter encodes them: an environment becomes its
graph, the set of pairs of an index with the value there.

The encoding pays off immediately, because the index side is a numeral and the
previous chapter already made numerals injective. So the graph really is a
function graph: at the key for `i` there sits exactly the value at `i`, and
nothing else. That lemma is the whole point of the chapter, and the atomic clause
of a satisfaction certificate is where it gets spent.

Two more readers follow, for the two things a certificate does with an
environment: look a value up, and extend the environment when it goes under a
quantifier. Extension is von Neumann successor at the index side, so the second
reader characterizes the successor. The chapter closes with the set of *all*
finite sequences over a given set, which is the canonical place an environment
lives when a certificate has to quantify over environments rather than exhibit
one.
<!--zh-->
谈论满足关系的证书必须谈论环境，而环境是从变元序号到集合的函数。函数不是层级中的集合，故本章把它们编码：环境成为它的图，即序号与该处取值配成的对之集。

编码立刻有回报，因为序号那一侧是数码，而上一章已经使数码单射。于是这个图确实是函数图：在 `i` 的键处恰好坐着 `i` 处的值，别无他物。那条引理就是本章的全部要点，而满足证书的原子子句正是花掉它的地方。

随后还有两条读式，对应证书对环境所做的两件事：查出一个值，以及在进入量词之下时扩张环境。扩张在序号一侧就是 von Neumann 后继，故第二条读式刻画后继。本章以「给定集合上全体有穷序列」之集收尾，那是证书需要对环境作量化 (而非拿出某一个) 时，环境的典范居所。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Environment {ℓ : Level} where

open import FOL.Syntax using ( var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Coding.Base {ℓ} using ( prAt; Δ₀-prAt; prAt-adequate )

import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## The graph of an environment
<!--zh-->
## 环境的图
<!--/-->

<!--en-->
An environment of length `n` becomes the set of pairs of the numeral for an index
with the value there. The index type is finite, hence small, so the gathering is
legitimate; membership is definitional.
<!--zh-->
长度为 `n` 的环境成为「序号的数码与该处取值」之对的集合。索引类型有穷，故小，这次汇集合法；隶属关系按定义成立。
<!--/-->

```agda
env : ∀ {n} → (Fin n → V ℓ) → V ℓ
env {n} g = sett (Lift {ℓ-zero} {ℓ} (Fin n))
                 (λ li → pr (# (toℕ (lower li))) (g (lower li)))

envOf : ∀ {n} → (V ℓ) ^ n → V ℓ
envOf γ = env (λ i → lookup i γ)

env-spec : ∀ {n} (g : Fin n → V ℓ) (s : V ℓ)
  → ⟨ s ∈ env g ⟩
  ≡ ∥ Σ[ li ∈ Lift {ℓ-zero} {ℓ} (Fin n) ]
      (pr (# (toℕ (lower li))) (g (lower li)) ≡ s) ∥₁
env-spec g s = refl
```

<!--en-->
And the lemma the chapter exists for: the graph is *functional*. A pair sits in
it at key `i` exactly when its second component is the value at `i`. Forwards,
the Kuratowski pair is injective, so the key of the witnessing entry equals the
key asked about; numerals are injective, so the indices agree; and the index type
embeds in the naturals, so the two indices are the same. Backwards is the entry
itself.
<!--zh-->
然后是本章为之存在的那条引理：这个图是**函数性的**。一个对在键 `i` 处属于它，恰当其第二分量是 `i` 处的值。正向：Kuratowski 对单射，故作证条目的键等于所问的键；数码单射，故序号相符；而索引类型嵌入自然数，故两个序号相同。反向就是那个条目本身。
<!--/-->

```agda
lookup-spec : ∀ {n} (g : Fin n → V ℓ) (i : Fin n) (v : V ℓ)
  → (pr (# (toℕ i)) v ∈ env g) ≡ ((v ≡ g i) , setIsSet v (g i))
lookup-spec {n} g i v = ⇔toPath fwd bwd
  where
  step : (lj : Lift {ℓ-zero} {ℓ} (Fin n))
       → pr (# (toℕ (lower lj))) (g (lower lj)) ≡ pr (# (toℕ i)) v
       → v ≡ g i
  step lj e = sym (ps .snd) ∙ cong g (inj-toℕ (#-inj′ (ps .fst)))
    where
    ps : (# (toℕ (lower lj)) ≡ # (toℕ i)) × (g (lower lj) ≡ v)
    ps = pr-inj e
  fwd : ⟨ pr (# (toℕ i)) v ∈ env g ⟩ → v ≡ g i
  fwd = PT.rec (setIsSet v (g i)) (λ { (lj , e) → step lj e })
  bwd : v ≡ g i → ⟨ pr (# (toℕ i)) v ∈ env g ⟩
  bwd e = ∣ lift i , cong (pr (# (toℕ i))) (sym e) ∣₁
```

<!--en-->
## Looking a value up
<!--zh-->
## 查出一个值
<!--/-->

<!--en-->
The object-language form: some member of the environment is the pair of these
two. One bounded existential over the previous chapter's Kuratowski reader, so Δ₀
and adequate at once.
<!--zh-->
对象语言的形式：环境的某个成员是这两者的对。上一章 Kuratowski 读式之上的一个有界存在，故 Δ₀ 与适足性一并到手。
<!--/-->

```agda
memPairAt : ∀ {n} → Fin n → Fin n → Fin n → Formula (V ℓ) n
memPairAt e i v = ∃̇∈ (var e) (prAt zero (suc i) (suc v))

Δ₀-memPairAt : ∀ {n} (e i v : Fin n) → Δ₀ (memPairAt e i v)
Δ₀-memPairAt e i v = δ-∃∈ (Δ₀-prAt zero (suc i) (suc v))

memPairAt-adequate : ∀ {n} (e i v : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ memPairAt e i v) ≡ (pr (⟦ var i ⟧ γ) (⟦ var v ⟧ γ) ∈ ⟦ var e ⟧ γ)
memPairAt-adequate e i v γ = ⇔toPath fwd bwd
  where
  I = ⟦ var i ⟧ γ
  Vv = ⟦ var v ⟧ γ
  E = ⟦ var e ⟧ γ
  fwd : ⟨ γ ⊨ memPairAt e i v ⟩ → ⟨ pr I Vv ∈ E ⟩
  fwd = PT.rec ((pr I Vv ∈ E) .snd)
    (λ { (q , q∈E , sat) →
      subst (λ z → ⟨ z ∈ E ⟩)
            (subst ⟨_⟩ (prAt-adequate zero (suc i) (suc v) (q ∷ γ)) sat)
            q∈E })
  bwd : ⟨ pr I Vv ∈ E ⟩ → ⟨ γ ⊨ memPairAt e i v ⟩
  bwd h = ∣ pr I Vv , h
          , subst ⟨_⟩ (sym (prAt-adequate zero (suc i) (suc v) (pr I Vv ∷ γ))) refl ∣₁
```

<!--en-->
## Going under a quantifier
<!--zh-->
## 进入量词之下
<!--/-->

<!--en-->
Extending an environment shifts every index up by one, and on numerals that is
the von Neumann successor. So a certificate that descends under a binder needs to
say "this index is the successor of that one", which is three clauses: the
smaller belongs to the larger, everything below the smaller is below the larger,
and everything below the larger is below the smaller or equal to it.
<!--zh-->
扩张环境把每个序号上移一位，而在数码上那就是 von Neumann 后继。故下降到约束之下的证书需要说「这个序号是那个的后继」，即三条子句：小者属于大者；小者之下的一切都在大者之下；而大者之下的一切，或在小者之下、或与小者相等。
<!--/-->

```agda
sucAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
sucAt i j = (var i ∈̇ var j)
         ∧̇ ((∀̇∈ (var i) (var zero ∈̇ var (suc j)))
         ∧̇ (∀̇∈ (var j) ((var zero ∈̇ var (suc i)) ∨̇ (var zero ≐ var (suc i)))))

Δ₀-sucAt : ∀ {n} (i j : Fin n) → Δ₀ (sucAt i j)
Δ₀-sucAt i j = δ-∧ δ-∈ (δ-∧ (δ-∀∈ δ-∈) (δ-∀∈ (δ-∨ δ-∈ δ-≐)))

private
  suc-char : (I J : V ℓ)
    → ⟨ I ∈ J ⟩
    → ((z : V ℓ) → ⟨ z ∈ I ⟩ → ⟨ z ∈ J ⟩)
    → ((z : V ℓ) → ⟨ z ∈ J ⟩ → ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁)
    → J ≡ sucV I
  suc-char I J hIJ mono cover = extensionality J (sucV I) (sub₁ , sub₂)
    where
    sub₁ : ⟨ J ⊆ sucV I ⟩
    sub₁ z z∈ₛJ = PT.rec ((z ∈ₛ sucV I) .snd)
      (Sum.rec
        (λ h → ∈∈ₛ {a = z} {b = sucV I} .fst (∈sucV-inl {A = I} {x = z} h))
        (λ e → subst (λ w → ⟨ w ∈ₛ sucV I ⟩) (sym e)
                 (∈∈ₛ {a = I} {b = sucV I} .fst (self∈sucV I))))
      (cover z (∈∈ₛ {a = z} {b = J} .snd z∈ₛJ))
    sub₂ : ⟨ sucV I ⊆ J ⟩
    sub₂ z z∈ₛs = ∈∈ₛ {a = z} {b = J} .fst
      (∈sucV-elim {A = I} {x = z} {P = ⟨ z ∈ J ⟩} ((z ∈ J) .snd)
        (∈∈ₛ {a = z} {b = sucV I} .snd z∈ₛs)
        (λ h → mono z h)
        (λ e → subst (λ w → ⟨ w ∈ J ⟩) (sym e) hIJ))

  suc-intro : (I J : V ℓ) → J ≡ sucV I
    → ⟨ I ∈ J ⟩
    × (((z : V ℓ) → ⟨ z ∈ I ⟩ → ⟨ z ∈ J ⟩)
    × ((z : V ℓ) → ⟨ z ∈ J ⟩ → ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁))
  suc-intro I J e =
      subst (λ w → ⟨ I ∈ w ⟩) (sym e) (self∈sucV I)
    , (λ z h → subst (λ w → ⟨ z ∈ w ⟩) (sym e) (∈sucV-inl {A = I} {x = z} h))
    , (λ z z∈J → ∈sucV-elim {A = I} {x = z} {P = ∥ ⟨ z ∈ I ⟩ ⊎ (z ≡ I) ∥₁} squash₁
        (subst (λ w → ⟨ z ∈ w ⟩) e z∈J)
        (λ h → ∣ inl h ∣₁)
        (λ q → ∣ inr q ∣₁))

sucAt-adequate : ∀ {n} (i j : Fin n) (γ : (V ℓ) ^ n)
  → (γ ⊨ sucAt i j) ≡ ((⟦ var j ⟧ γ ≡ sucV (⟦ var i ⟧ γ)) , setIsSet _ _)
sucAt-adequate i j γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → suc-char (⟦ var i ⟧ γ) (⟦ var j ⟧ γ) h₁ h₂ h₃ })
  (suc-intro (⟦ var i ⟧ γ) (⟦ var j ⟧ γ))
```

<!--en-->
## All sequences over a set
<!--zh-->
## 一个集合上的全部序列
<!--/-->

<!--en-->
Finally, every finite sequence of members of a given set, encoded and gathered.
The index is the length paired with a function into the set's small member type,
which is small again, so this is another harvest of the smallness that has been
paying for everything since Part 3. A certificate that must quantify over
environments quantifies over this.
<!--zh-->
最后是给定集合的成员构成的全部有穷序列，编码并汇集起来。索引是长度与一个到该集合的小成员类型的函数配成的对，而那又是小的，故这是自第三部起一直在买单的那份小性的又一次收割。必须对环境作量化的证书，量化的就是它。
<!--/-->

```agda
envIn : (A : V ℓ) {n : ℕ} → (Fin n → ⟪ A ⟫) → V ℓ
envIn A g = env (λ i → ⟪ A ⟫↪ (g i))

cons : ∀ {ℓ'} {X : Type ℓ'} {n : ℕ} → X → (Fin n → X) → Fin (suc n) → X
cons m g zero    = m
cons m g (suc i) = g i

seqSet : V ℓ → V ℓ
seqSet A = sett (Σ[ n ∈ ℕ ] (Fin n → ⟪ A ⟫)) (λ p → envIn A (p .snd))

seqSet-spec : (A s : V ℓ)
  → ⟨ s ∈ seqSet A ⟩
  ≡ ∥ Σ[ p ∈ (Σ[ n ∈ ℕ ] (Fin n → ⟪ A ⟫)) ]
      (env (λ i → ⟪ A ⟫↪ (p .snd i)) ≡ s) ∥₁
seqSet-spec A s = refl

seqSet-mem : {A : V ℓ} {n : ℕ} (f : Fin n → ⟪ A ⟫)
           → ⟨ env (λ i → ⟪ A ⟫↪ (f i)) ∈ seqSet A ⟩
seqSet-mem {A} {n} f = ∣ (n , f) , refl ∣₁
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
An environment is its graph (`env`{.Agda}), and the graph is functional
(`lookup-spec`{.Agda}), which is what makes the encoding usable rather than
merely definable. `memPairAt`{.Agda} reads a value out of it and
`sucAt`{.Agda} recognizes the index shift that going under a quantifier
performs, both Δ₀ and adequate. `seqSet`{.Agda} collects all finite sequences
over a set, for the certificates that quantify over environments instead of
naming one.
<!--zh-->
环境就是它的图 (`env`{.Agda})，而图是函数性的 (`lookup-spec`{.Agda})，正是这一点使这套编码可用而不只是可定义。`memPairAt`{.Agda} 从中查出一个值，`sucAt`{.Agda} 认出进入量词之下所作的序号移位，二者皆 Δ₀ 且适足。`seqSet`{.Agda} 汇集一个集合上的全部有穷序列，供那些对环境作量化而非点名某一个的证书使用。
<!--/-->
