# A good table has only one value

<!--en-->
The uniqueness half. A table that satisfies the twelve clauses over a
subcode-closed index set, and answers at every key in it, records at each key the
value the meta-level recursion built there, and nothing else. That is what makes
the graph single-valued.

It is stated against the canonical value rather than between two arbitrary
tables. The two forms are the same induction, and the pinned one is shorter and
is the one a recursion consumes: what `funct`{.Agda} needs is that the value at
an index is determined, and the meta-level recursion is where a determined value
comes from.

The statement's shape is not a matter of taste. The index and the value are
**variables** and the key is reached by an equation, exactly as every clause
reader is written; stating a case at a key already substituted in puts two
concrete set constructions inside a satisfaction, and that does not typecheck in
any reasonable time. This chapter learned that at its first case.
<!--zh-->
唯一性那一半。一张在子码封闭的索引集上满足十二条子句、且在其中每个键处都作答的表，在每个键处记录的就是元语言递归在那里造出的取值，别无其他。正是这一点使那个图单值。

它是**对着那个典范取值**陈述的，不是在两张任意的表之间。两种形式是同一次归纳，而钉住一侧的那种更短，也是递归所消费的那种：`funct`{.Agda} 需要的是「某索引处的取值被决定」，而被决定的取值来自元语言的递归。

这条陈述的形状不是口味问题。索引与取值都是**变元**，而那个键经一条等式抵达，与每条子句读式的写法完全一致；把某一情形陈述在「键已经代入」的形式上，就等于把两个具体的集合构造塞进一个满足关系里，而那在任何合理时间内都不会通过类型检查。本章在它的第一个情形上学到了这一点。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Unique {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; ⊤̇; ⊥̇ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( closedAt; domAt; domAt-in; botClauseAt; botClause-out; topClauseAt
        ; topClause-out; andClauseAt; propClause-out; interAt; yc7; ya7; yb7
        ; binSameClosed-out; prʟ-fst; module LCode; numL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Sat {ℓ} lem using ( Sat; Sat-mem )
open import L.Coding.Table {ℓ} lem using ( keyʟ; keyʟ-shape-in )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.Sound {ℓ} lem using ( module AmbientHolds )

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  nn : ℕ → S
  nn k = # k , numL k
```

<!--en-->
## What a good table is
<!--zh-->
## 什么叫一张好表
<!--/-->

<!--en-->
Three things, in the order the graph will state them: the index set holds the
subcodes of its members, the table answers at every index, and the twelve clauses
hold. The first two are what the existence half had to *build*; here they are
hypotheses, because the table is now arbitrary.
<!--zh-->
三件，按那个图将要陈述它们的次序：索引集含有其成员的诸子码、表在每个索引处作答、以及十二条子句成立。前两件是存在性那一半必须**造出来**的东西；此处它们是假设，因为那张表如今是任意的。
<!--/-->

```agda
module Good (B C T : S) where
  private
    γ : S ^ 3
    γ = B ∷ T ∷ C ∷ []

  Ci Ti Bi : Fin 3
  Ci = suc (suc zero)
  Ti = suc zero
  Bi = zero

  Closed : Type (ℓ-suc ℓ)
  Closed = ⟨ γ ⊨ closedAt Ci ⟩

  Total : Type (ℓ-suc ℓ)
  Total = ⟨ γ ⊨ domAt Ti Ci ⟩

  Bot : Type (ℓ-suc ℓ)
  Bot = ⟨ γ ⊨ botClauseAt Ci Ti ⟩

  Top : Type (ℓ-suc ℓ)
  Top = ⟨ γ ⊨ topClauseAt Ci Ti Bi ⟩

  And : Type (ℓ-suc ℓ)
  And = ⟨ γ ⊨ andClauseAt Ci Ti ⟩

  Pinned : ∀ {m} → Formula S m → Type (ℓ-suc ℓ)
  Pinned {m} ψ = (c y : S) → fst c ≡ fst (keyʟ ψ)
               → ⟨ fst c ∈ fst C ⟩
               → ⟨ pr (fst c) (fst y) ∈ fst T ⟩
               → fst y ≡ fst (Sat B ψ)
```

<!--en-->
## The constant that pins itself
<!--zh-->
## 自己钉住自己的那个常量
<!--/-->

<!--en-->
The first case, and the one that needs nothing: the clause for `⊥̇` says the
value is empty, the recursion cut its value out of the ambient set by a condition
nothing satisfies, and two empty sets are equal. No ambient set has to be
supplied, no subvalue exists to replace, and no induction hypothesis is used.
<!--zh-->
第一种情形，也是什么都不需要的那一种：`⊥̇` 的子句说那个取值为空，而递归当初是用「没有东西满足的条件」从周遭集合把它的取值雕出来的，而两个空集相等。不必递周遭集合进去，没有子取值要替换，也用不上归纳假设。
<!--/-->

```agda
  bot : Bot → ∀ {m} → Pinned (⊥̇ {n = m})
  bot hbot {m} c y q c∈ hy = extensionalV (λ w → ⇔toPath
    (λ hw → Empty.rec* (empty (w , isL-trans hw (snd y)) hw))
    (λ hw → Empty.rec* (subst ⟨_⟩
      (Sat-mem B (⊥̇ {n = m}) (w , isL-trans hw (snd (Sat B (⊥̇ {n = m})))))
      hw .snd)))
    where
    empty = botClause-out Ci Ti γ hbot c (nn m) (numeralL 0) y c∈
              (q ∙ keyʟ-shape-in (⊥̇ {n = m})) hy .fst
```

<!--en-->
## The constant the ambient set pins
<!--zh-->
## 由周遭集合钉住的那个常量
<!--/-->

<!--en-->
The second constant, and the first case that has to **supply** an ambient set
rather than consume one. The clause says the value is the set of environments;
the recursion cut its value out of that set by a condition everything satisfies,
so the value is that set again. The supplying is one application of the
agreement, and the arities and the carrier match by `refl`{.Agda} because the
frame put them where the clause looks.
<!--zh-->
第二个常量，也是第一条必须**递出**一个周遭集合、而非消费一个的情形。子句说那个取值就是诸环境之集；递归当初用「一切都满足的条件」从那个集合把它的取值雕出来，故那个取值又是那个集合。递出只是把那份一致性施用一次，而诸元数与载体由 `refl`{.Agda} 对上，因为框架把它们放在子句所看之处。
<!--/-->

```agda
  top : Top → ∀ {m} → Pinned (⊤̇ {n = m})
  top htop {m} c y q c∈ hy = extensionalV (λ w → ⇔toPath
    (λ hw → subst ⟨_⟩ (sym (Sat-mem B (⊤̇ {n = m}) (sw w hw)))
      (e .fst (sw w hw) hw , tt*))
    (λ hw → e .snd (sw' w hw)
      (subst ⟨_⟩ (Sat-mem B (⊤̇ {n = m}) (sw' w hw)) hw .fst)))
    where
    δ' : S ^ 8
    δ' = envSet B m ∷ y ∷ numeralL 0 ∷ nn m ∷ c ∷ γ

    hE = AmbientHolds.holds B δ' zero (suc (suc (suc zero)))
           (suc (suc (suc (suc (suc Bi))))) m refl refl refl

    e = topClause-out Ci Ti Bi γ htop c (nn m) (numeralL 0) y (envSet B m) c∈
          (q ∙ keyʟ-shape-in (⊤̇ {n = m})) hy hE

    sw : (w : V ℓ) → ⟨ w ∈ fst y ⟩ → S
    sw w hw = w , isL-trans hw (snd y)

    sw' : (w : V ℓ) → ⟨ w ∈ fst (Sat B (⊤̇ {n = m})) ⟩ → S
    sw' w hw = w , isL-trans hw (snd (Sat B (⊤̇ {n = m})))
```

<!--en-->
## The first case with an induction hypothesis
<!--zh-->
## 第一条用上归纳假设的情形
<!--/-->

<!--en-->
Conjunction, and with it the shape the remaining ten follow. Closedness puts the
subkeys in the index, totality gives the table an entry at each of them, the
induction hypothesis says those entries are the recursion's values, the clause
says the value at the key is their intersection, and the recursion cut its value
out by the same condition. The entries arrive merely, which costs nothing,
because the goal is an equation between sets.
<!--zh-->
合取，以及随之而来、余下十条都要走的那个形状。封闭性把诸子键放进索引，全性使表在每个子键处都有条目，归纳假设说那些条目就是递归的诸取值，子句说键处的取值是它们的交，而递归当初正是用同一个条件把它的取值雕出来的。那些条目是**仅仅**到手的，而这不花分文，因为目标是一条集合之间的等式。
<!--/-->

```agda
  and : Closed → Total → And
      → ∀ {m} (a' b' : Formula S m) → Pinned a' → Pinned b' → Pinned (a' ∧̇ b')
  and hcl hdom hand {m} a' b' ia ib c y q c∈ hy =
    PT.rec (setIsSet (fst y) (fst (Sat B (a' ∧̇ b'))))
      (λ { (ya , hya) → PT.rec (setIsSet (fst y) (fst (Sat B (a' ∧̇ b'))))
        (λ { (yb , hyb) →
          let ea = ia (keyʟ a') ya refl (ka .fst) hya
              eb = ib (keyʟ b') yb refl (ka .snd) hyb
              e  = propClause-out Ci Ti 2 (interAt yc7 ya7 yb7) γ hand
                     c (nn m) ca cb y ya yb c∈ shape hy (up a' ya hya) (up b' yb hyb)
          in extensionalV (λ w → ⇔toPath
               (λ hw → subst ⟨_⟩ (sym (Sat-mem B (a' ∧̇ b') (sy w hw)))
                 ( subst ⟨_⟩ (Sat-mem B a' (sy w hw))
                     (subst (λ v → ⟨ w ∈ v ⟩) ea (e .fst (sy w hw) hw .fst)) .fst
                 , ( subst (λ v → ⟨ w ∈ v ⟩) ea (e .fst (sy w hw) hw .fst)
                   , subst (λ v → ⟨ w ∈ v ⟩) eb (e .fst (sy w hw) hw .snd) ) ))
               (λ hw →
                 let r = subst ⟨_⟩ (Sat-mem B (a' ∧̇ b') (ss w hw)) hw in
                 e .snd (ss w hw)
                   ( subst (λ v → ⟨ w ∈ v ⟩) (sym ea) (r .snd .fst)
                   , subst (λ v → ⟨ w ∈ v ⟩) (sym eb) (r .snd .snd) ))) })
        (domAt-in Ti Ci γ hdom (keyʟ b') (ka .snd)) })
      (domAt-in Ti Ci γ hdom (keyʟ a') (ka .fst))
    where
    ca cb : S
    ca = LCode.⌜ a' ⌝
    cb = LCode.⌜ b' ⌝

    shape : fst c ≡ pr (fst (nn m)) (pr (# 2) (pr (fst ca) (fst cb)))
    shape = q ∙ keyʟ-shape-in (a' ∧̇ b')
          ∙ cong (λ w → pr (# m) (pr (# 2) w)) (prʟ-fst ca cb)

    kkey : ∀ {j} (χ : Formula S j) → pr (# j) (fst LCode.⌜ χ ⌝) ≡ fst (keyʟ χ)
    kkey {j} χ = cong (λ w → pr w (fst LCode.⌜ χ ⌝)) (sym (numeralL-fst j))
               ∙ sym (prʟ-fst (numeralL j) LCode.⌜ χ ⌝)

    ka : ⟨ fst (keyʟ a') ∈ fst C ⟩ × ⟨ fst (keyʟ b') ∈ fst C ⟩
    ka = subst (λ w → ⟨ w ∈ fst C ⟩) (kkey a') (r .fst)
       , subst (λ w → ⟨ w ∈ fst C ⟩) (kkey b') (r .snd)
      where r = binSameClosed-out Ci 2 γ (hcl .fst) c (nn m) ca cb c∈ shape

    up : ∀ {j} (χ : Formula S j) (v : S)
       → ⟨ pr (fst (keyʟ χ)) (fst v) ∈ fst T ⟩
       → ⟨ pr (pr (# j) (fst LCode.⌜ χ ⌝)) (fst v) ∈ fst T ⟩
    up χ v h = subst (λ w → ⟨ pr w (fst v) ∈ fst T ⟩) (sym (kkey χ)) h

    sy : (w : V ℓ) → ⟨ w ∈ fst y ⟩ → S
    sy w hw = w , isL-trans hw (snd y)

    ss : (w : V ℓ) → ⟨ w ∈ fst (Sat B (a' ∧̇ b')) ⟩ → S
    ss w hw = w , isL-trans hw (snd (Sat B (a' ∧̇ b')))
```
