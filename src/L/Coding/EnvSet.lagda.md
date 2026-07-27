# The environments over a set form a set

<!--en-->
The chapter that wrote the twelve clauses said what it means for one thing to be
an environment over a set, and disowned the question of whether all of them
together form a set. This chapter answers it, and the answer is owed: the clause
for negation takes a complement, and a complement is taken inside something.

The route is the one the axioms already sell. Environments over a set of `L` at a
fixed length are indexed by a small type, each is an element of `L`, so they all
lie below one stage; carving that stage by the description gives exactly them.
Nothing here needs replacement, and nothing here needs a recursion.
<!--zh-->
写下十二条子句的那一章说了「单个东西是某集合之上的环境」是什么意思，却把「它们全体是否构成一个集合」这个问题推开了。本章回答它，而这份回答是欠着的：否定那条子句取补集，而补集总是在某个东西之内取的。

路线是诸公理早已卖给我们的那条。给定长度、落在 `L` 的某集合之上的诸环境，由一个小类型索引，每个都是 `L` 的元素，故它们全部落在同一个阶段之下；用那条描述雕出那个阶段，得到的恰是它们。此处不需要替换，也不需要任何递归。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.EnvSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #-inj′ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd; ∈#-elim )
open import V.Coding {ℓ} using ( #mono; pr-inj )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.InL {ℓ} using ( envL )
open import L.Coding.Model {ℓ}
  using ( envOverAt; svAt; domAt; valuesInAt; pairsInAt; inDomAt
        ; prʟ; prʟ-fst; numL; svAt-in; inDomAt-adequate; prAtL
        ; appAt-adequate; prAtL-adequate )

open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## A stage under a small family
<!--zh-->
## 小族之下的一个阶段
<!--/-->

<!--en-->
The move `smallDom`{.Agda} makes, with the ordinal kept rather than hidden,
because what wants it here is a lemma stated about stages rather than about a set
of the model.
<!--zh-->
`smallDom`{.Agda} 所作的那个动作，但把那个序数留着而非藏起，因为此处要它的是一条关于阶段、而非关于模型某集合的引理。
<!--/-->

```agda
stageFor : (X : Type ℓ) (f : X → S)
         → Σ[ β ∈ V ℓ ] (IsOrd β × ((x : X) → ⟨ fst (f x) ∈ Lset β ⟩))
stageFor X f = β , (oβ , mem)
  where
  b = boundingOrd X (λ x → stage (fst (f x)) (f x .snd))
        (λ x → stage-ord (fst (f x)) (f x .snd))
  β = b .fst
  oβ : IsOrd β
  oβ = b .snd .fst
  mem : (x : X) → ⟨ fst (f x) ∈ Lset β ⟩
  mem x = Lset-mono {α = β} {β = stage (fst (f x)) (f x .snd)} (b .snd .snd x)
            (stage-mem (fst (f x)) (f x .snd))
```

<!--en-->
## One environment, as an element of the model
<!--zh-->
## 单个环境，作为模型的元素
<!--/-->

<!--en-->
An environment over a set of `L` is a finite set of pairs of a numeral with a
member, and a member of an element of `L` is an element of `L`, so the pairs are
too and the stage lemma above closes it.
<!--zh-->
落在 `L` 的某集合之上的环境，是「数码与某成员」之对构成的有穷集；而 `L` 元素的成员是 `L` 的元素，故那些对也是，于是上面那条阶段引理把它封上。
<!--/-->

```agda
module _ (B : S) where
  private
    ix : ⟪ fst B ⟫ → S
    ix m = ⟪ fst B ⟫↪ m
         , isL-trans (∈∈ₛ {a = ⟪ fst B ⟫↪ m} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ m))
             (snd B)

  Ix : ℕ → Type ℓ
  Ix n = Fin n → ⟪ fst B ⟫

  opaque
    envSL : {n : ℕ} (g : Ix n) → ⟨ isL (env (λ i → fst (ix (g i)))) ⟩
    envSL {n} g = envL β oβ (λ i → fst (ix (g i))) mem
      where
      pairs : Lift {ℓ-zero} {ℓ} (Fin n) → S
      pairs i = prʟ (numeralL (toℕ (lower i))) (ix (g (lower i)))

      sf : Σ[ b ∈ V ℓ ] (IsOrd b
         × ((i : Lift {ℓ-zero} {ℓ} (Fin n)) → ⟨ fst (pairs i) ∈ Lset b ⟩))
      sf = stageFor (Lift {ℓ-zero} {ℓ} (Fin n)) pairs

      β : V ℓ
      β = sf .fst

      oβ : IsOrd β
      oβ = sf .snd .fst

      mem : (i : Fin n) → ⟨ pr (# (toℕ i)) (fst (ix (g i))) ∈ Lset β ⟩
      mem i = subst (λ w → ⟨ w ∈ Lset β ⟩)
        (prʟ-fst (numeralL (toℕ i)) (ix (g i))
          ∙ cong₂ pr (numeralL-fst (toℕ i)) refl)
        (sf .snd .snd (lift i))

  envS : {n : ℕ} → Ix n → S
  envS g = env (λ i → fst (ix (g i))) , envSL g
```

<!--en-->
## The set
<!--zh-->
## 那个集合
<!--/-->

<!--en-->
The description takes three arguments and separation offers one variable, so the
other two are bound and pinned to constants. That is three lines and it keeps the
description as the chapter wrote it, which is worth more than saving them.
<!--zh-->
那条描述要三个自变量，而分离只给一个变元，故另外两个被绑定并钉在常元上。这花三行，而它让那条描述保持本章当初写下的样子，这比省下那三行值钱。
<!--/-->

```agda
  private
    nn : ℕ → S
    nn k = # k , numL k

  envFo : (n : ℕ) → Formula S 1
  envFo n = ∃̇ (∃̇ ( (var (suc zero) ≐ con (nn n))
                 ∧̇ ((var zero ≐ con B)
                 ∧̇ envOverAt (suc (suc zero)) (suc zero) zero) ))

  private
    sf : (n : ℕ) → Σ[ β ∈ V ℓ ] (IsOrd β × ((g : Ix n) → ⟨ fst (envS g) ∈ Lset β ⟩))
    sf n = stageFor (Ix n) envS

    amb : (n : ℕ) → S
    amb n = LsetS (sf n .fst) (sf n .snd .fst)

  envSet : (n : ℕ) → S
  envSet n = hasSeparationL (amb n) (envFo n) .fst .fst
```

<!--en-->
## Every environment is in it
<!--zh-->
## 每个环境都在其中
<!--/-->

<!--en-->
Four conjuncts, and each is the description read against what an environment
actually is. Single-valuedness and the two containments come straight off the
membership specification, which is `refl`{.Agda}; the domain is the only one that
does arithmetic, because saying the domain is the numeral `n` means saying that
the indices below `n` are exactly the numerals below `n`.
<!--zh-->
四个合取项，而每一条都是把那条描述对着「环境究竟是什么」读一遍。单值性与那两条包含关系直接落自成员规格，而后者是 `refl`{.Agda}；只有定义域那一条要算术，因为「定义域是数码 `n`」这句话，说的就是「`n` 以下的诸序号恰是 `n` 以下的诸数码」。
<!--/-->

```agda
  private
    prAt3 : {m : ℕ} (a b c : S) (γ' : S ^ m) → fst a ≡ pr (fst b) (fst c)
          → ⟨ (c ∷ b ∷ a ∷ γ') ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
    prAt3 a b c γ' e = subst ⟨_⟩
      (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (c ∷ b ∷ a ∷ γ'))) e

    pairsIn : {m : ℕ} (γ' : S ^ m) (e d Bv : Fin m)
            → ((s : S) → ⟨ fst s ∈ fst (lookup e γ') ⟩
               → ∥ (Σ[ u ∈ S ] (Σ[ v ∈ S ]
                     (⟨ fst u ∈ fst (lookup d γ') ⟩
                      × (⟨ fst v ∈ fst (lookup Bv γ') ⟩
                         × (fst s ≡ pr (fst u) (fst v)))))) ∥₁)
            → ⟨ γ' ⊨ pairsInAt e d Bv ⟩
    pairsIn γ' e d Bv k s s∈ = PT.map
      (λ { (u , (v , (u∈ , (v∈ , eq)))) →
        u , (u∈ , ∣ v , (v∈ , prAt3 s u v γ' eq) ∣₁) })
      (k s s∈)

    module _ {n : ℕ} (g : Ix n) where
      private
        out : (s : V ℓ) → ⟨ s ∈ fst (envS g) ⟩
            → ∥ (Σ[ i ∈ Fin n ] (pr (# (toℕ i)) (fst (ix (g i))) ≡ s)) ∥₁
        out s = PT.map (λ { (li , e) → lower li , e })

        into : (i : Fin n) → ⟨ pr (# (toℕ i)) (fst (ix (g i))) ∈ fst (envS g) ⟩
        into i = ∣ lift i , refl ∣₁

        val∈ : (i : Fin n) → ⟨ fst (ix (g i)) ∈ fst B ⟩
        val∈ i = ∈∈ₛ {a = ⟪ fst B ⟫↪ (g i)} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ (g i))

        δ : S ^ 3
        δ = B ∷ nn n ∷ envS g ∷ []

        E : Fin 3
        E = suc (suc zero)

      envOver : ⟨ δ ⊨ envOverAt E (suc zero) zero ⟩
      envOver = sv , (dom , (vals , pairs))
        where
        sv : ⟨ δ ⊨ svAt E ⟩
        sv = svAt-in E δ (λ x y y' p q →
          PT.rec (setIsSet (fst y) (fst y'))
            (λ { (i , ei) → PT.rec (setIsSet (fst y) (fst y'))
              (λ { (j , ej) → sym (pr-inj ei .snd)
                 ∙ cong (λ k → fst (ix (g k)))
                     (inj-toℕ (#-inj′ (pr-inj ei .fst ∙ sym (pr-inj ej .fst))))
                 ∙ pr-inj ej .snd })
              (out (pr (fst x) (fst y')) q) })
            (out (pr (fst x) (fst y)) p))

        dom : ⟨ δ ⊨ domAt E (suc zero) ⟩
        dom x = fwd , bwd
          where
          fwd : ⟨ (x ∷ δ) ⊨ inDomAt (suc E) zero ⟩ → ⟨ fst x ∈ (# n) ⟩
          fwd hd = PT.rec (snd (fst x ∈ (# n)))
            (λ { (y , p) → PT.rec (snd (fst x ∈ (# n)))
              (λ { (i , ei) → subst (λ w → ⟨ w ∈ (# n) ⟩) (pr-inj ei .fst)
                     (#mono (toℕ i) n (toℕ<n i)) })
              (out (pr (fst x) (fst y)) p) })
            (subst ⟨_⟩ (inDomAt-adequate (suc E) zero (x ∷ δ)) hd)

          bwd : ⟨ fst x ∈ (# n) ⟩ → ⟨ (x ∷ δ) ⊨ inDomAt (suc E) zero ⟩
          bwd hx = subst ⟨_⟩ (sym (inDomAt-adequate (suc E) zero (x ∷ δ)))
            (PT.map
              (λ { (m , m<n , e) →
                ix (g (fromℕ' n m m<n))
                , subst (λ w → ⟨ pr w (fst (ix (g (fromℕ' n m m<n))))
                                   ∈ fst (envS g) ⟩)
                    (cong #_ (toFromId' n m m<n) ∙ sym e) (into (fromℕ' n m m<n)) })
              (∈#-elim n (fst x) hx))

        vals : ⟨ δ ⊨ valuesInAt E zero ⟩
        vals x y hp = PT.rec (snd (fst y ∈ fst B))
          (λ { (i , ei) → subst (λ w → ⟨ w ∈ fst B ⟩) (pr-inj ei .snd) (val∈ i) })
          (out (pr (fst x) (fst y))
            (subst ⟨_⟩ (appAt-adequate (suc (suc E)) (suc zero) zero (y ∷ x ∷ δ))
              hp))

        pairs : ⟨ δ ⊨ pairsInAt E (suc zero) zero ⟩
        pairs = pairsIn δ E (suc zero) zero
          (λ s s∈ → PT.map
            (λ { (i , ei) → nn (toℕ i)
               , ( ix (g i)
                 , ( #mono (toℕ i) n (toℕ<n i) , (val∈ i , sym ei) ) ) })
            (out (fst s) s∈))

      envSetIn : ⟨ (envS g ∷ []) ⊨ envFo n ⟩
      envSetIn = ∣ nn n , ∣ B , (refl , (refl , envOver)) ∣₁ ∣₁
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`envSet`{.Agda} is the ambient set the negative clauses take their complements
in, and `envSetIn`{.Agda} says every environment over the carrier is in it. What
is still owed is the other direction, that every member is one, which four
clauses will want when they read a bound variable off an environment.

One measurement, and it is a sharper form of a rule the development already had.
Proving the fourth conjunct with the environment written out **did not finish in
ten minutes**; proving the same thing as a lemma whose environment is a
*variable*, then applying it, takes no measurable time. A satisfaction
substitution along an adequacy equation must be discharged where the arguments
are variables. Written at concrete elements it drags the whole absoluteness
bridge through normalization, and the elements' constructibility certificates
with it.
<!--zh-->
`envSet`{.Agda} 是诸负子句取补集所在的那个周遭集合，而 `envSetIn`{.Agda} 说载体之上的每个环境都在其中。仍然欠着的是另一个方向，即它的每个成员都是一个环境；有四条子句在从环境读出被绑变元时会要这一条。

一次测量，而它是本书早已有的一条规矩的更锐形式。把环境写死来证第四个合取项，**十分钟没跑完**；把同一件事证成一条「环境是**变元**」的引理再施用，则快到测不出来。沿适足性等式作的满足关系代换，必须在自变量是变元之处交割。写在具体元素上，它会把整座绝对性之桥拖进归一化，连同那些元素的可构造性证书。
<!--/-->
