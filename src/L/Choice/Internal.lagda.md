# The order, described in the object language

<!--en-->
The previous chapters built the order this part turns on, and built all of it in
the meta-language: a family of well-orders, one at every ordinal, comparing two
sets by their births and, at a common birth, by their least names. None of that
is speakable inside `L`. What the argument ahead needs is a **formula**: the same
comparison described in the object language, so that the model's own separation
can carve the order out as a set and the choosing can be written down inside.

This chapter writes that description. It has three parts, and each is the reading
of one meta-level part. A **name at slots** says what a skeleton, a parameter
sequence and a denotation are; the **order formula** compares two names by the
three keys the naming chapter compared them by; and the **step** says what one
step of the family does. The chapter closes with the two halves that make a
description a description: at a variable environment, the order formula holds of
two names' data exactly when the naming chapter's comparison holds of the names.

Two decisions shape everything below. The two conditions that say a formula is a
skeleton are each **one membership atom**, one in the limit stage and one in the
code set at the empty alphabet, and neither is a recursion; and the order formula
runs **no recursion of its own**. Both are explained where they are used, because
both are the reason this chapter is short.
<!--zh-->
前几章造出了本部所系的那个序，而且全部造在元语言中：一族良序，每个序数处一个，先按两个集合的诞生阶段比较它们，诞生阶段相同时再按它们的最小名字比较。这一切在 `L` 内部都说不出口。后续论证所需的是一条**公式**：用对象语言把同一次比较描述出来，使模型自家的分离能把那个序雕成集合，也使选取得以在内部写下。

本章写下那条描述。它有三个部分，每一部分都是某个元层面部分的读法。**落在诸位上的名字**说清什么是骨架、什么是参数序列、什么是指称；**序公式**按命名那一章比较两个名字所用的三个键来比较它们；而**步进**说清这一族的一步做了什么。本章以「使描述成其为描述」的那两半收尾：在变元环境上，序公式对两个名字的数据成立，当且仅当命名那一章的比较对那两个名字成立。

有两项决定塑造了以下的一切。「一条公式是骨架」的那两个条件各是**一个隶属原子**，一个落在极限阶段、一个落在空字母表处的码集，两者都不是递归；而序公式**不跑自己的任何递归**。两者都在用到它们之处解释，因为两者正是本章之所以短的原因。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.Internal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import FOL.Manipulation.Relabelling using ( mapFo; mapFo-comp; embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; #-inj′; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans; Lset )
open import L.Ordinal {ℓ} using ( ω-ord; ∈#-elim; #∈#-elim )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Coding.Environment {ℓ} using ( env; lookup-spec )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-in-both
        ; prAtL; prAtL-adequate; appAt; appAt-adequate
        ; domAt; domAt-in; domAt-out; domAt-intro; numL
        ; sucAtL; sucAtL-adequate; envOverAt; consAtL )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Table {ℓ} lem
  using ( slot; satTable; total; inSlot; entry-in )
open import L.Coding.Slot {ℓ} lem using ( slotClosed )
open import L.Coding.Sound {ℓ} lem using ( soundness )
open import L.Coding.Unique {ℓ} lem using ( module Good )
open import L.Coding.Bridge {ℓ} lem using ( asConst )
open import L.Coding.CodeSet {ℓ} lem
  using ( keyS; AllCodes; AllCodes-out; key∈AllCodes )
open import L.Coding.Uniform {ℓ} lem using ( keyBridge )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; graphAt-in; graphAt-out )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-defines )
open import L.Choice.Name {ℓ} lem using ( module Naming; limitCode )
open import L.Choice.Finite {ℓ} lem using ( Limit; limitOrder )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )

open import Cubical.Data.Nat.Order
  using ( _<_; zero-≤; suc-≤-suc; pred-≤-pred; ¬-<-zero; <-trans )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( subst2; J; substRefl )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( #_; ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = suc (suc (suc (suc i)))

  sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  sh5 i = suc (suc (suc (suc (suc i))))
```

<!--en-->
## A skeleton, said as one atom

A name's formula carries no parameters: the parameters left the syntax two
chapters ago and arrived as an environment. Saying so inside the model looks, at
first, like a demand for a recursion. "No constant tag occurs anywhere in this
code" is a statement about every subcode, and a statement about every subcode is
a descent, which would have to be internalized with its own graph, its own table
and its own uniqueness theorem.

The descent is not needed, and this is the chapter's cheapest line. A
parameter-free code is built from numerals and Kuratowski pairs and from nothing
else, so it is hereditarily finite, and the naming chapter proved exactly that:
the code lies in `Lset ω`{.Agda}. Membership is **one atom**. So the first
condition the description carries is that the skeleton belongs to the limit
stage, and the sequence chapter already says inside what the limit stage is, as
the value its graph assigns at the constant `ωʟ`{.Agda}. What that atom does not
say is constant-freeness itself, and the next section says it, with a second atom
rather than a recursion.

The graph is discharged at a **variable** pair of slots reached by two equations,
which is the law the tower chapters were written under, and the two elements the
description is satisfied at are sealed for the reason the marker records.
<!--zh-->
## 骨架，说成一个原子

一个名字的公式不带参数：两章之前，参数已经离开语法、以环境的身份到场。要在模型内部把这句话说出来，乍看像是在索要一场递归。「这个码里任何地方都不出现常量标签」是一句关于每个子码的陈述，而关于每个子码的陈述就是一次下降，那得连同它自己的图、自己的表、自己的唯一性定理一并内化。

那次下降其实不需要，而这是本章最便宜的一行。无参的码由数码与 Kuratowski 对造成、别无他物，故它是遗传有穷的，而命名那一章证的恰是这一条：该码落在 `Lset ω`{.Agda} 中。隶属是**一个原子**。于是这条描述所携带的第一个条件就是「骨架属于极限阶段」，而序列那一章已经在内部说清了极限阶段是什么，即它的图在常元 `ωʟ`{.Agda} 处所指派的取值。那个原子没有说出的，正是无参性本身，而下一节把它说出来，靠的是第二个原子、不是一场递归。

那个图在经两条等式抵达的**一对变元位**上解除，这正是塔诸章据以写下的规矩；而描述在其上被满足的那两个元素被封印，理由记在标记里。
<!--/-->

```agda
-- perf: the limit stage's two elements are sealed; unsealed, checking any term
-- at a satisfaction of the tower graph over them runs 77 s instead of 1.6 s
opaque
  ωAt : S
  ωAt = ωʟ

  ωStage : S
  ωStage = LsetS ω ω-ord

  ωAt-fst : fst ωAt ≡ ω
  ωAt-fst = refl

  ωStage-fst : fst ωStage ≡ Lset ω
  ωStage-fst = refl

limitGraph : ∀ {n} (v o : Fin n) (γ : S ^ n)
           → fst (lookup o γ) ≡ ω → fst (lookup v γ) ≡ Lset ω
           → ⟨ γ ⊨ LsetGraphAt v o ⟩
limitGraph v o γ qo qv =
  Lset-defines v o γ (subst IsOrd (sym qo) ω-ord) (qv ∙ cong Lset (sym qo))

InLimitAt : ∀ {n} → Fin n → Formula S n
InLimitAt s = ∃̇ (∃̇ ( (var zero ≐ con ωʟ)
                    ∧̇ ( LsetGraphAt (suc zero) zero
                      ∧̇ (var (sh2 s) ∈̇ var (suc zero)) ) ))

module _ {n : ℕ} (s : Fin n) (γ : S ^ n) where
  InLimitAt-in : ⟨ fst (lookup s γ) ∈ Lset ω ⟩ → ⟨ γ ⊨ InLimitAt s ⟩
  InLimitAt-in h = ∣ ωStage , ∣ ωAt , (ωAt-fst , (gr , held)) ∣₁ ∣₁
    where
    gr : ⟨ (ωAt ∷ ωStage ∷ γ) ⊨ LsetGraphAt (suc zero) zero ⟩
    gr = limitGraph (suc zero) zero (ωAt ∷ ωStage ∷ γ) ωAt-fst ωStage-fst
    held : ⟨ fst (lookup s γ) ∈ fst ωStage ⟩
    held = subst (λ u → ⟨ fst (lookup s γ) ∈ u ⟩) (sym ωStage-fst) h
```

<!--en-->
## The same code at the empty alphabet

That condition puts the code where the order of codes lives, and it is not the
condition the meta-language imposes. A member of the limit stage is a
hereditarily finite set, and a hereditarily finite set can be the code of a
formula whose constants are hereditarily finite; over a carrier containing the
limit stage those constants are members of the carrier, so the skeleton
condition alone admits skeletons the meta `Name`{.Agda} excludes, and a least
name inside would not have to be a least name outside. The description has to
say the other thing as well: the skeleton carries **no** constants.

It costs one more membership atom, and it reuses a set the coding chapters
already build. `AllCodes A`{.Agda} holds exactly the keys of the formulas over
the alphabet `⟪ A ⟫`{.Agda}; take the alphabet **empty** and it holds exactly
the keys of the parameter-free formulas. So the second code set reaches the
description as a slot, like the first, and the atom says that the key made from
the arity and the skeleton lies in it.

One thing had to be checked before writing that down, and it holds: a
parameter-free formula has the **same code at either alphabet**. Both readings
of its constants are functions out of an empty type, any two such agree, and
relabelling composes, so the two codes are the same set, four lines in each
direction. Nothing has to be satisfied at the empty alphabet, because the
conjunct is an atom and the separation the code set was cut out by was proved
generic in its carrier where it was built.

The bridge is then the code set's own two directions read at that alphabet, with
the arity moved along the equality of numerals by path induction, once, in the
direction that leaves the code alone.
<!--zh-->
## 同一个码，落在空字母表上

那个条件把码放到了诸码之序所在之处，而它并不是元语言所加的条件。极限阶段的成员是遗传有穷集，而遗传有穷集可以是某条「常量为遗传有穷」的公式之码；在一个含有极限阶段的载体之上，那些常量正是载体的成员，故单凭骨架条件，这条描述放进了元层面 `Name`{.Agda} 所排除的骨架，于是内部的最小名字未必得是外部的最小名字。这条描述还得把另一件事说出来：那个骨架**不带**常量。

代价是再来一个隶属原子，而它复用编码诸章早已造好的一个集合。`AllCodes A`{.Agda} 恰好持有字母表 `⟪ A ⟫`{.Agda} 之上诸公式的诸键；把字母表取作**空的**，它持有的就恰好是诸无参公式的诸键。于是第二个码集像第一个一样，以一个位的身份抵达这条描述，而那个原子说：由元数与骨架造出的那个键落在其中。

写下它之前有一件事必须核查，而它成立：一条无参公式在两个字母表上**有同一个码**。它的常量的两种读法都是从空类型出发的函数，任何两个这样的函数都相符，而变换又可复合，故那两个码是同一个集合，每个方向四行。空字母表处无须满足任何东西，因为那个合取项是原子，而码集据以切出的那次分离，在它被造出之处就已对它的载体证成通用。

于是那座桥就是码集自家的两个方向，读在那个字母表上；其中元数经一次路径归纳沿数码的等式挪过去，只挪一次，且挪的方向不动那条码。
<!--/-->

```agda
private
  noAlpha : ⟪ ∅ {ℓ} ⟫ → Empty.⊥
  noAlpha m = ∅-empty (⟪ ∅ ⟫↪ m) (∈ₛ⟪ ∅ ⟫↪ m)

  Fo∅ : ℕ → Type ℓ
  Fo∅ = Formula ⟪ ∅ {ℓ} ⟫

  ε : ⟪ ∅ {ℓ} ⟫ → ⊥* {ℓ}
  ε m = Empty.rec (noAlpha m)

  sameCode : ∀ {n} (ψ : Fo∅ n) → mapFo ⟪ ∅ ⟫↪ ψ ≡ embed (mapFo ε ψ)
  sameCode ψ = cong (λ f → mapFo f ψ) (funExt (λ m → Empty.rec (noAlpha m)))
             ∙ sym (mapFo-comp ε Empty.rec* ψ)

  sameCode' : ∀ {n} (χ : Formula (⊥* {ℓ}) n)
            → mapFo ⟪ ∅ {ℓ} ⟫↪ (embed χ) ≡ embed χ
  sameCode' χ = mapFo-comp Empty.rec* ⟪ ∅ ⟫↪ χ
              ∙ cong (λ f → mapFo f χ) (funExt (λ b → Empty.rec* b))

  codeShift : {i j : ℕ} (e : i ≡ j) (ψ : Fo∅ i)
            → VCode.⌜ mapFo ⟪ ∅ ⟫↪ (subst Fo∅ e ψ) ⌝
            ≡ VCode.⌜ mapFo ⟪ ∅ ⟫↪ ψ ⌝
  codeShift {i} e ψ =
    J (λ j' e' → VCode.⌜ mapFo ⟪ ∅ ⟫↪ (subst Fo∅ e' ψ) ⌝
               ≡ VCode.⌜ mapFo ⟪ ∅ ⟫↪ ψ ⌝)
      (cong (λ u → VCode.⌜ mapFo ⟪ ∅ ⟫↪ u ⌝) (substRefl {B = Fo∅} ψ)) e

freeCode-in : (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
            → ⟨ pr (# k) (fst (limitCode χ)) ∈ fst (AllCodes ∅ʟ) ⟩
freeCode-in k χ =
  subst (λ u → ⟨ pr (# k) VCode.⌜ u ⌝ ∈ fst (AllCodes ∅ʟ) ⟩) (sameCode' χ)
    (key∈AllCodes ∅ʟ (embed χ))

freeCode-out : (k : ℕ) (c : V ℓ) → ⟨ pr (# k) c ∈ fst (AllCodes ∅ʟ) ⟩
             → ∥ Σ[ χ ∈ Formula (⊥* {ℓ}) k ] (c ≡ fst (limitCode χ)) ∥₁
freeCode-out k c h = PT.map read (AllCodes-out ∅ʟ (pr (# k) c , cL) h)
  where
  cL : ⟨ isL (pr (# k) c) ⟩
  cL = isL-trans h (AllCodes ∅ʟ .snd)

  read : Σ[ n ∈ ℕ ] Σ[ ψ ∈ Fo∅ n ] (pr (# k) c ≡ fst (keyS ∅ʟ ψ))
       → Σ[ χ ∈ Formula (⊥* {ℓ}) k ] (c ≡ fst (limitCode χ))
  read (n , (ψ , q)) = mapFo ε ψ' , (pr-inj q .snd ∙ step)
    where
    e : n ≡ k
    e = sym (#-inj′ (pr-inj q .fst))
    ψ' : Fo∅ k
    ψ' = subst Fo∅ e ψ
    step : VCode.⌜ mapFo ⟪ ∅ ⟫↪ ψ ⌝ ≡ VCode.⌜ embed (mapFo ε ψ') ⌝
    step = sym (codeShift e ψ) ∙ cong VCode.⌜_⌝ (sameCode ψ')
```

<!--en-->
## Constant-freeness, said as one atom

The atom itself binds two values before it can be stated. The arity slot holds
the name's arity, and the key a formula is filed under carries **one more**,
because the formula is the one a subset is carved by; so the atom binds the
successor of the arity, which the sequence chapter's reader already says, then
the pair of that successor with the skeleton, and then asserts that pair to be a
member of the second code set.

Both readings are at a **variable** arity reached by an equation, and both are
the binders packed and unpacked with the two readers' adequacy equations
discharged inside. With the slot filled, the two halves compose into the
statement the gap asked for: the skeleton slot holds exactly the codes of the
parameter-free formulas of one more variable than the arity, which is exactly
what a meta name's formula is. The membership in the limit stage falls out of it
for free, since a parameter-free code is hereditarily finite, so the skeleton
condition of the previous section is derivable rather than assumed, and the
description keeps both conjuncts until the derivable one is retired on purpose.
<!--zh-->
## 无参性，说成一个原子

那个原子本身在能被说出之前，先要绑定两个取值。元数那一位持有名字的元数，而一条公式被归档所用的键携带的是**多一个**的元数，因为那条公式正是子集据以被雕出的那一条；故那个原子先绑定元数的后继，这一点序列那一章的读式早已说清，再绑定那个后继与骨架之对，然后断言那个对是第二个码集的成员。

两条读法都落在经一条等式抵达的**变元**元数上，而两条都是把诸绑定装起来、又拆开来，两条读式的适足等式在里面交付。那一位一经填上，两半便复合成那道缝所索取的陈述：骨架那一位所持有的，恰是「比元数多一个变量的诸无参公式」的诸码，而那正是元层面一个名字的公式。「属于极限阶段」由它白得，因为无参的码是遗传有穷的，故上一节那条骨架条件如今是可推出的、而非假设的，而在那条可推出的合取项被有意退役之前，这条描述两个合取项都留着。
<!--/-->

```agda
FreeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
FreeAt C₀ s a =
  ∃̇ ( sucAtL (suc a) zero
    ∧̇ ∃̇ ( prAtL zero (suc zero) (sh2 s)
         ∧̇ (var zero ∈̇ var (sh2 C₀)) ) )

module _ {n : ℕ} (C₀ s a : Fin n) (γ : S ^ n) (k : ℕ)
         (qa : fst (lookup a γ) ≡ # k) where

  FreeAt-in : ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ fst (lookup C₀ γ) ⟩
            → ⟨ γ ⊨ FreeAt C₀ s a ⟩
  FreeAt-in h = ∣ numAt , ( hsuc , ∣ keyAt , ( hpr , h ) ∣₁ ) ∣₁
    where
    numAt : S
    numAt = # (suc k) , numL (suc k)
    keyAt : S
    keyAt = pr (# (suc k)) (fst (lookup s γ)) , isL-trans h (lookup C₀ γ .snd)
    hsuc : ⟨ (numAt ∷ γ) ⊨ sucAtL (suc a) zero ⟩
    hsuc = subst ⟨_⟩ (sym (sucAtL-adequate (suc a) zero (numAt ∷ γ)))
      (cong sucV (sym qa))
    hpr : ⟨ (keyAt ∷ numAt ∷ γ) ⊨ prAtL zero (suc zero) (sh2 s) ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate zero (suc zero) (sh2 s) (keyAt ∷ numAt ∷ γ))) refl

  FreeAt-out : ⟨ γ ⊨ FreeAt C₀ s a ⟩
             → ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ fst (lookup C₀ γ) ⟩
  FreeAt-out = PT.rec (snd (pr (# (suc k)) (fst (lookup s γ))
                            ∈ fst (lookup C₀ γ))) atNum
    where
    Target : Type (ℓ-suc ℓ)
    Target = ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ fst (lookup C₀ γ) ⟩

    atKey : (z : S) → fst z ≡ sucV (fst (lookup a γ))
          → Σ[ y ∈ S ] ( ⟨ (y ∷ z ∷ γ) ⊨ prAtL zero (suc zero) (sh2 s) ⟩
                       × ⟨ fst y ∈ fst (lookup C₀ γ) ⟩ )
          → Target
    atKey z qz (y , (hp , hy)) =
      subst (λ u → ⟨ u ∈ fst (lookup C₀ γ) ⟩)
        (subst ⟨_⟩ (prAtL-adequate zero (suc zero) (sh2 s) (y ∷ z ∷ γ)) hp
         ∙ cong (λ u → pr u (fst (lookup s γ))) (qz ∙ cong sucV qa)) hy

    atNum : Σ[ z ∈ S ] ( ⟨ (z ∷ γ) ⊨ sucAtL (suc a) zero ⟩
                       × ⟨ (z ∷ γ) ⊨ ∃̇ ( prAtL zero (suc zero) (sh2 s)
                                       ∧̇ (var zero ∈̇ var (sh2 C₀)) ) ⟩ )
          → Target
    atNum (z , (hs , hk)) = PT.rec (snd (pr (# (suc k)) (fst (lookup s γ))
                                         ∈ fst (lookup C₀ γ)))
      (atKey z (subst ⟨_⟩ (sucAtL-adequate (suc a) zero (z ∷ γ)) hs)) hk

module _ {n : ℕ} (C₀ s a : Fin n) (γ : S ^ n) (k : ℕ)
         (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ))
         (qa : fst (lookup a γ) ≡ # k) where

  codeFree-out : ⟨ γ ⊨ FreeAt C₀ s a ⟩
               → ∥ Σ[ χ ∈ Formula (⊥* {ℓ}) (suc k) ]
                     (fst (lookup s γ) ≡ fst (limitCode χ)) ∥₁
  codeFree-out h = freeCode-out (suc k) (fst (lookup s γ))
    (subst (λ u → ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ u ⟩) q₀
      (FreeAt-out C₀ s a γ k qa h))

  codeFree-in : (χ : Formula (⊥* {ℓ}) (suc k))
              → fst (lookup s γ) ≡ fst (limitCode χ) → ⟨ γ ⊨ FreeAt C₀ s a ⟩
  codeFree-in χ q = FreeAt-in C₀ s a γ k qa
    (subst (λ u → ⟨ pr (# (suc k)) (fst (lookup s γ)) ∈ u ⟩) (sym q₀)
      (subst (λ u → ⟨ pr (# (suc k)) u ∈ fst (AllCodes ∅ʟ) ⟩) (sym q)
        (freeCode-in (suc k) χ)))

```

<!--en-->
## How long a sequence is

The parameter sequence is a function, and how long it is is what its domain says.
One fact is wanted, in both directions, and it is used twice below: the domain of
an environment of length `k` is the numeral of `k`. Forwards, an entry is a pair
whose first component is the numeral of an index, and an index is smaller than
the length. Backwards, a member of the numeral is the numeral of a smaller
number, that number is an index, and the environment has an entry there.

The statement stands at a **variable** environment reached by an equation saying
which family it is the graph of, and the family's values are supplied with their
constructibility, because an object-language function must hand back an element
of the model when it is applied.
<!--zh-->
## 一个序列有多长

参数序列是一个函数，而它有多长，就是它的定义域所说的事。要用的事实只有一条，两个方向都要，且下文用它两次：长度为 `k` 的环境，其定义域是 `k` 的数码。正向：一个条目是一个对，其第一分量是某个序号的数码，而序号小于长度。反向：数码的成员是更小的数的数码，那个数是一个序号，而环境在那里有条目。

这条陈述站在一个**变元**环境上，经一条「它是哪个族的图」的等式抵达；而该族的诸取值连同它们的可构造性一并供上，因为对象语言的函数被施用时必须交回模型的一个元素。
<!--/-->

```agda
private
  memberOf : (k : ℕ) (g : Fin k → V ℓ) (x y : V ℓ) → ⟨ pr x y ∈ env g ⟩
           → ∥ Σ[ i ∈ Fin k ] ((x ≡ # (toℕ i)) × (y ≡ g i)) ∥₁
  memberOf k g x y = PT.map
    (λ { (li , e) → lower li
       , (sym (pr-inj e .fst) , sym (pr-inj e .snd)) })

  entryOf : (k : ℕ) (g : Fin k → V ℓ) (i : Fin k)
          → ⟨ pr (# (toℕ i)) (g i) ∈ env g ⟩
  entryOf k g i = ∣ lift i , refl ∣₁

  dom-into : (k : ℕ) (g : Fin k → V ℓ) (x : V ℓ)
           → ⟨ ⋁ S (λ y → pr x (fst y) ∈ env g) ⟩ → ⟨ x ∈ # k ⟩
  dom-into k g x = PT.rec (snd (x ∈ # k)) atEntry
    where
    atIndex : (u : V ℓ) → Σ[ i ∈ Fin k ] ((x ≡ # (toℕ i)) × (u ≡ g i))
            → ⟨ x ∈ # k ⟩
    atIndex u (i , (qx , _)) = subst (λ v → ⟨ v ∈ # k ⟩) (sym qx)
      (#mono (toℕ i) k (toℕ<n i))
    atEntry : Σ[ y ∈ S ] ⟨ pr x (fst y) ∈ env g ⟩ → ⟨ x ∈ # k ⟩
    atEntry (y , p) = PT.rec (snd (x ∈ # k)) (atIndex (fst y))
      (memberOf k g x (fst y) p)

  dom-from : (k : ℕ) (g : Fin k → V ℓ) → ((i : Fin k) → ⟨ isL (g i) ⟩)
           → (x : V ℓ) → ⟨ x ∈ # k ⟩ → ⟨ ⋁ S (λ y → pr x (fst y) ∈ env g) ⟩
  dom-from k g cg x h = PT.map atNumeral (∈#-elim k x h)
    where
    atNumeral : Σ[ m ∈ ℕ ] ((m < k) × (x ≡ # m))
              → Σ[ y ∈ S ] ⟨ pr x (fst y) ∈ env g ⟩
    atNumeral (m , (p , qx)) = (g i , cg i)
      , subst (λ u → ⟨ pr u (g i) ∈ env g ⟩) (sym qi) (entryOf k g i)
      where
      i : Fin k
      i = fromℕ' k m p
      qi : x ≡ # (toℕ i)
      qi = qx ∙ cong #_ (sym (toFromId' k m p))

module _ {n : ℕ} (e d : Fin n) (γ : S ^ n)
         (k : ℕ) (g : Fin k → V ℓ) (cg : (i : Fin k) → ⟨ isL (g i) ⟩)
         (qe : fst (lookup e γ) ≡ env g) where

  domAt-numeral : ⟨ γ ⊨ domAt e d ⟩ → fst (lookup d γ) ≡ # k
  domAt-numeral h = extensionalV {a = fst (lookup d γ)} {b = # k} pt
    where
    fwd : (x : V ℓ) → ⟨ x ∈ fst (lookup d γ) ⟩ → ⟨ x ∈ # k ⟩
    fwd x hx = dom-into k g x
      (subst (λ u → ⟨ ⋁ S (λ y → pr x (fst y) ∈ u) ⟩) qe
        (domAt-in e d γ h (x , isL-trans hx (lookup d γ .snd)) hx))
    bwd : (x : V ℓ) → ⟨ x ∈ # k ⟩ → ⟨ x ∈ fst (lookup d γ) ⟩
    bwd x hx = PT.rec (snd (x ∈ fst (lookup d γ))) put (dom-from k g cg x hx)
      where
      xS : S
      xS = x , isL-trans hx (numL k)
      put : Σ[ y ∈ S ] ⟨ pr x (fst y) ∈ env g ⟩ → ⟨ x ∈ fst (lookup d γ) ⟩
      put (y , p) = domAt-out e d γ h xS y
        (subst (λ u → ⟨ pr x (fst y) ∈ u ⟩) (sym qe) p)
    pt : (x : V ℓ) → (x ∈ fst (lookup d γ)) ≡ (x ∈ # k)
    pt x = ⇔toPath (fwd x) (bwd x)

  domAt-fill : fst (lookup d γ) ≡ # k → ⟨ γ ⊨ domAt e d ⟩
  domAt-fill qd = domAt-intro e d γ step
    where
    step : (x : S)
         → (⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ fst (lookup e γ)) ⟩
            → ⟨ fst x ∈ fst (lookup d γ) ⟩)
         × (⟨ fst x ∈ fst (lookup d γ) ⟩
            → ⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ fst (lookup e γ)) ⟩)
    step x =
        (λ hy → subst (λ u → ⟨ fst x ∈ u ⟩) (sym qd) (dom-into k g (fst x)
          (subst (λ u → ⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ u) ⟩) qe hy)))
      , (λ hx → subst (λ u → ⟨ ⋁ S (λ y → pr (fst x) (fst y) ∈ u) ⟩) (sym qe)
          (dom-from k g cg (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) qd hx)))
```

<!--en-->
## What the satisfaction graph assigns

The denotation is what a name's formula selects, and inside the model the
selecting is done by the satisfaction table. The uniform-satisfaction chapter
built that table as a recursion and proved its two halves against the model's own
two-place graph. What is needed here is the same two halves at a **carrier held
in a slot** and at a variable ambient environment, because the description below
puts the graph under five binders.

Nothing is re-proved. The index set, the table, its closedness, its totality and
the twelve clauses are the chapters that built them, applied at this environment;
the key is carried from the hierarchy's coding to the model's by the bridge
written for exactly that. So the two readings are the existence and the
uniqueness halves transplanted, and they say what a consumer wants: the value the
graph assigns at the key of a formula is that formula's satisfaction set, and
nothing else satisfies the graph there.
<!--zh-->
## 满足关系的图所指派的取值

指称就是一个名字的公式所选中的东西，而在模型内部，作选中的是那张满足关系表。一致满足那一章把那张表造成一场递归，并对着模型自家的二元图证出了它的两半。此处所需的是同样两半，但落在**握在一位上的载体**上、落在变元的周遭环境上，因为下面那条描述把那个图放在五层绑定之下。

此处没有重证任何东西。索引集、表、它的封闭性、它的全性以及那十二条子句，都是造出它们的那几章的东西，施用在这个环境上；而那个键，由专为此写下的那座桥从层级的编码搬到模型的编码。故这两条读法就是存在性与唯一性两半的移植，而它们说出了消费方想要的话：图在某条公式之键处所指派的取值，就是该公式的满足集合，而在那里别无他物满足该图。
<!--/-->

```agda
module _ {n : ℕ} (B x y : Fin n) (γ : S ^ n) where
  private
    Ci Ti : Fin (suc (suc (suc n)))
    Ci = suc (suc zero)
    Ti = suc zero

    Bs : S
    Bs = lookup B γ

    δ : ∀ {m} (φ : Formula S m) → S ^ (suc (suc (suc n)))
    δ φ = Bs ∷ satTable Bs φ ∷ slot Bs φ ∷ γ

    hdom : ∀ {m} (φ : Formula S m) → ⟨ δ φ ⊨ domAt Ti Ci ⟩
    hdom φ = domAt-intro Ti Ci (δ φ)
      (λ z → (λ h → PT.rec (snd (fst z ∈ fst (slot Bs φ)))
                 (λ { (w , hw) → inSlot Bs φ (fst z) (fst w) hw }) h)
           , (λ h → total Bs φ (fst z) h))

  graphAt-value : ∀ {m} (ψ : Formula ⟪ fst Bs ⟫ m)
                → fst (lookup x γ) ≡ fst (keyS Bs ψ)
                → fst (lookup y γ) ≡ fst (Sat Bs (mapFo (asConst Bs) ψ))
                → ⟨ γ ⊨ satGraphAt B x y ⟩
  graphAt-value ψ qx qy = graphAt-in B x y γ
    ∣ slot Bs φ , (satTable Bs φ , (Bs , (refl
    , ( slotClosed Bs φ γ
    , ( hdom φ
    , ( subst2 (λ u v → ⟨ pr u v ∈ fst (satTable Bs φ) ⟩)
          (sym (qx ∙ keyBridge Bs ψ)) (sym qy) (entry-in Bs φ)
    , soundness Bs φ γ )))))) ∣₁
    where
    φ : Formula S _
    φ = mapFo (asConst Bs) ψ

  graphAt-only : ∀ {m} (ψ : Formula ⟪ fst Bs ⟫ m)
               → fst (lookup x γ) ≡ fst (keyS Bs ψ)
               → ⟨ γ ⊨ satGraphAt B x y ⟩
               → fst (lookup y γ) ≡ fst (Sat Bs (mapFo (asConst Bs) ψ))
  graphAt-only ψ qx h = PT.rec (setIsSet _ _) read (graphAt-out B x y γ h)
    where
    φ : Formula S _
    φ = mapFo (asConst Bs) ψ

    read : _ → fst (lookup y γ) ≡ fst (Sat Bs φ)
    read (C , (T , (b , (eb , (hc , (hd , (ha , h12))))))) =
        Good.pinned (b ∷ T ∷ C ∷ γ) Ci Ti zero hc hd h12 φ
          (lookup x γ) (lookup y γ) (qx ∙ keyBridge Bs ψ)
          (domAt-out Ti Ci (b ∷ T ∷ C ∷ γ) hd (lookup x γ) (lookup y γ) ha) ha
      ∙ cong (λ w → fst (Sat w φ)) (Σ≡Prop (λ v → snd (isL v)) eb)
```

<!--en-->
## A name, described at slots

A name is three things, and the description carries them at three slots: the
**skeleton**, the code of the parameter-free formula; the **parameter sequence**,
an environment over the carrier; and the **denotation**, the set the name names.
A fourth slot holds the arity, which is not a fourth part but the sequence's own
domain, pinned by the same conjunct that says the sequence is an environment over
the carrier.

The denotation is the one conjunct with mathematics in it, and it is written as
**one** extension, for the reason every set-valued clause on this route is: a
value is the set of exactly the things meeting a condition, and writing that as a
pair of inclusions would say the condition twice. A member of the carrier belongs
to the denotation exactly when the environment got by pushing that member onto
the parameters satisfies the skeleton, and satisfying is read off the value the
graph assigns. So the body binds, in order, the extended environment, its length,
the key that length and the skeleton make, and the value at that key.

One conjunct is easy to miss and the description says nothing without it: the key
must lie in the **code set**. The graph binds its table existentially, so at a key
that is nobody's code a table may record anything at all; the code set is what
makes the value determinate, and it reaches the description as a slot, like the
carrier.

Both readings are the extension's own two directions with the four binders packed
and unpacked, and every payload is named. The key equation is handed back
decoded, because a consumer wants the equation and not the syntax that carries it.
<!--zh-->
## 名字，描述在诸位上

一个名字是三样东西，而这条描述把它们携带在三个位上：**骨架**，即那条无参公式的码；**参数序列**，即载体之上的一个环境；以及**指称**，即该名字所命名的集合。第四个位持有元数，而元数并非第四个部分，它就是那个序列自己的定义域，由「该序列是载体之上的环境」这同一个合取项钉住。

指称是唯一装着数学的那个合取项，而它写成**一次**外延，理由与这条路线上每一条取值为集合的子句相同：一个取值恰是满足某条件的那些东西之集，而若写成一对包含，那个条件就要说两遍。载体的一个成员属于该指称，当且仅当「把该成员推到诸参数前面所得的环境」满足那个骨架，而「满足」是从图所指派的取值上读出的。故它的体依次绑定：扩展后的环境、它的长度、由那个长度与那个骨架造出的键，以及那个键处的取值。

有一个合取项容易漏掉，而没有它这条描述什么也没说：那个键必须落在**码集**中。图把自己的表作存在绑定，故在「不是任何人的码」的键处，一张表爱记什么就记什么；码集才是使那个取值确定的东西，而它像载体一样，以一个位的身份抵达这条描述。

两条读法就是那次外延自家的两个方向，把四层绑定装起来、又拆开来，而每一份载荷都被点名。键的等式是解码之后交回的，因为消费方要的是那条等式，不是承载它的语法。
<!--/-->

```agda
DenoteBody : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S (suc n)
DenoteBody B C s e =
  (var zero ∈̇ var (suc B))
  ∧̇ ∃̇ ( consAtL zero (suc zero) (sh2 e)
       ∧̇ ∃̇ ( domAt (suc zero) zero
            ∧̇ ∃̇ ( (var zero ∈̇ var (sh4 C))
                 ∧̇ ( prAtL zero (suc zero) (sh4 s)
                   ∧̇ ∃̇ ( satGraphAt (sh5 B) (suc zero) zero
                        ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) ) ) ) )

NameAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
       → Formula S n
NameAt B C C₀ s a e d =
  InLimitAt s ∧̇ ( FreeAt C₀ s a
                ∧̇ ( (var a ∈̇ con ωʟ)
                  ∧̇ ( envOverAt e a B ∧̇ extAt d (DenoteBody B C s e) ) ) )

module _ {n : ℕ} (B C s e : Fin n) (γ : S ^ n) where
  AtValue : (z c k key : S) → Type (ℓ-suc ℓ)
  AtValue z c k key = Σ[ v ∈ S ]
    ( ⟨ (v ∷ key ∷ k ∷ c ∷ z ∷ γ) ⊨ satGraphAt (sh5 B) (suc zero) zero ⟩
    × ⟨ fst c ∈ fst v ⟩ )

  AtKey : (z c k : S) → Type (ℓ-suc ℓ)
  AtKey z c k = Σ[ key ∈ S ]
    ( ⟨ fst key ∈ fst (lookup C γ) ⟩
    × ( ⟨ (key ∷ k ∷ c ∷ z ∷ γ) ⊨ prAtL zero (suc zero) (sh4 s) ⟩
      × ∥ AtValue z c k key ∥₁ ) )

  AtArity : (z c : S) → Type (ℓ-suc ℓ)
  AtArity z c = Σ[ k ∈ S ]
    ( ⟨ (k ∷ c ∷ z ∷ γ) ⊨ domAt (suc zero) zero ⟩ × ∥ AtKey z c k ∥₁ )

  AtCons : (z : S) → Type (ℓ-suc ℓ)
  AtCons z = Σ[ c ∈ S ]
    ( ⟨ (c ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩ × ∥ AtArity z c ∥₁ )

  DenoteOf : (z : S) → Type (ℓ-suc ℓ)
  DenoteOf z = Σ[ c ∈ S ] Σ[ k ∈ S ] Σ[ key ∈ S ] Σ[ v ∈ S ]
    ( ⟨ (c ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩
    × ( ⟨ (k ∷ c ∷ z ∷ γ) ⊨ domAt (suc zero) zero ⟩
      × ( ⟨ fst key ∈ fst (lookup C γ) ⟩
        × ( (fst key ≡ pr (fst k) (fst (lookup s γ)))
          × ( ⟨ (v ∷ key ∷ k ∷ c ∷ z ∷ γ) ⊨ satGraphAt (sh5 B) (suc zero) zero ⟩
            × ⟨ fst c ∈ fst v ⟩ ) ) ) ) )

  DenoteBody-in : (z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩ → DenoteOf z
                → ⟨ (z ∷ γ) ⊨ DenoteBody B C s e ⟩
  DenoteBody-in z hz (c , (k , (key , (v , (hc , (hk , (hi , (hp , (hg , hm)))))))))
    = hz , ∣ c , (hc , ∣ k , (hk , ∣ key , (hi
    , ( subst ⟨_⟩ (sym (prAtL-adequate zero (suc zero) (sh4 s) (key ∷ k ∷ c ∷ z ∷ γ))) hp
      , ∣ v , (hg , hm) ∣₁ )) ∣₁) ∣₁) ∣₁

  DenoteBody-out : (z : S) → ⟨ (z ∷ γ) ⊨ DenoteBody B C s e ⟩
                 → ⟨ fst z ∈ fst (lookup B γ) ⟩ × ∥ DenoteOf z ∥₁
  DenoteBody-out z (hz , hc) = hz , PT.rec squash₁ (atCons z) hc
    where
    atValue : (z c k key : S) → ⟨ (c ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩
            → ⟨ (k ∷ c ∷ z ∷ γ) ⊨ domAt (suc zero) zero ⟩
            → ⟨ fst key ∈ fst (lookup C γ) ⟩
            → ⟨ (key ∷ k ∷ c ∷ z ∷ γ) ⊨ prAtL zero (suc zero) (sh4 s) ⟩
            → AtValue z c k key → ∥ DenoteOf z ∥₁
    atValue z c k key hc hk hi hp (v , (hg , hm)) =
      ∣ c , (k , (key , (v , (hc , (hk , (hi
      , ( subst ⟨_⟩ (prAtL-adequate zero (suc zero) (sh4 s) (key ∷ k ∷ c ∷ z ∷ γ)) hp
        , (hg , hm) ))))))) ∣₁

    atKey : (z c k : S) → ⟨ (c ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩
          → ⟨ (k ∷ c ∷ z ∷ γ) ⊨ domAt (suc zero) zero ⟩
          → AtKey z c k → ∥ DenoteOf z ∥₁
    atKey z c k hc hk (key , (hi , (hp , hv))) =
      PT.rec squash₁ (atValue z c k key hc hk hi hp) hv

    atArity : (z c : S) → ⟨ (c ∷ z ∷ γ) ⊨ consAtL zero (suc zero) (sh2 e) ⟩
            → AtArity z c → ∥ DenoteOf z ∥₁
    atArity z c hc (k , (hk , hkey)) =
      PT.rec squash₁ (atKey z c k hc hk) hkey

    atCons : (z : S) → AtCons z → ∥ DenoteOf z ∥₁
    atCons z (c , (hc , ha)) = PT.rec squash₁ (atArity z c hc) ha

module _ {n : ℕ} (B C C₀ s a e d : Fin n) (γ : S ^ n) where
  NameAt-in : ⟨ fst (lookup s γ) ∈ Lset ω ⟩
            → ⟨ γ ⊨ FreeAt C₀ s a ⟩
            → ⟨ fst (lookup a γ) ∈ ω ⟩
            → ⟨ γ ⊨ envOverAt e a B ⟩
            → ((z : S) → ⟨ fst z ∈ fst (lookup d γ) ⟩
               → ⟨ fst z ∈ fst (lookup B γ) ⟩ × DenoteOf B C s e γ z)
            → ((z : S) → ⟨ fst z ∈ fst (lookup B γ) ⟩ → DenoteOf B C s e γ z
               → ⟨ fst z ∈ fst (lookup d γ) ⟩)
            → ⟨ γ ⊨ NameAt B C C₀ s a e d ⟩
  NameAt-in hs hf ha he into back =
    InLimitAt-in s γ hs , (hf , (ha , (he , extAt-in-both d (DenoteBody B C s e) γ
      (λ z hz → DenoteBody-in B C s e γ z (into z hz .fst) (into z hz .snd))
      (λ z h → PT.rec (snd (fst z ∈ fst (lookup d γ)))
                 (back z (DenoteBody-out B C s e γ z h .fst))
                 (DenoteBody-out B C s e γ z h .snd)))))

```

<!--en-->
## The order, with no recursion of its own

The naming chapter compared two names by three keys: the code, by the well-order
of the limit stage; the arity, by the order of the numerals; and the parameters,
at the first place they differ. Every one of the three is available inside without
a recursion, and that is the fact worth stating plainly, because a second
internalized recursion is the largest cost this route has ever paid.

The first key is a **membership atom**. The order the codes are compared by is a
relation, a relation is a set of pairs, and "this code comes before that one" is
"the pair of them belongs to that set". The relation reaches the description as a
slot: the description is a frame, and what fills the slot is the caller's
business, which is also why nothing here has to know how that order was built.

The second key is a membership atom as well, because an arity is a numeral and a
numeral is the set of the smaller numerals.

The third key is a **bounded quantification**, not a descent. Two sequences of the
same length differ first somewhere, and below that index they agree. Written out,
that is one bounded existential over the index, two applications reading the two
values there, one membership atom against the parameter order, and one bounded
universal saying the two sequences agree below. Nothing recurses, nothing is
defined by cases on a code, and no second table is wanted.
<!--zh-->
## 那个序，不跑自己的递归

命名那一章按三个键比较两个名字：码，按极限阶段的良序；元数，按诸数码的序；参数，则在它们首次相异之处。这三者在内部都无须递归即可得到，而这件事值得直说，因为第二场已内化的递归，是这条路线迄今付过的最大一笔代价。

第一个键是一个**隶属原子**。诸码据以比较的那个序是一个关系，而关系是对之集，于是「这个码排在那个之前」就是「它们的对属于那个集合」。那个关系以一个位的身份抵达这条描述：描述是一个框架，而填那一位是调用方的事，这也正是此处无须知道那个序是怎么造出来的原因。

第二个键同样是一个隶属原子，因为元数是数码，而数码就是更小的诸数码之集。

第三个键是一次**有界量化**，不是一次下降。同长的两个序列首次相异于某处，而在那个序号以下它们相符。写开了，那就是：对序号的一个有界存在、读出那里两个取值的两次取值、对着参数序的一个隶属原子，以及一个说「两个序列在以下相符」的有界全称。什么也不递归，什么也不按码分情形定义，也不需要第二张表。
<!--/-->

```agda
private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

  sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
  sh6 i = suc (suc (suc (suc (suc (suc i)))))

LexAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
LexAt P a e₁ e₂ =
  ∃̇∈ (var a) (
    ∃̇ ( ∃̇ ( appAt (sh3 e₁) (suc (suc zero)) (suc zero)
           ∧̇ ( appAt (sh3 e₂) (suc (suc zero)) zero
             ∧̇ ( appAt (sh3 P) (suc zero) zero
               ∧̇ ∀̇∈ (var (suc (suc zero))) (
                    ∃̇ ( appAt (sh5 e₁) (suc zero) zero
                      ∧̇ appAt (sh5 e₂) (suc zero) zero ) ) ) ) ) ) )

≺At : ∀ {n} → Fin n → Fin n
    → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
≺At R P s₁ a₁ e₁ s₂ a₂ e₂ =
      appAt R s₁ s₂
  ∨̇ ( (var s₂ ≐ var s₁)
    ∧̇ ( (var a₁ ∈̇ var a₂)
      ∨̇ ( (var a₂ ≐ var a₁) ∧̇ LexAt P a₁ e₁ e₂ ) ) )

module _ {n : ℕ} (P a e₁ e₂ : Fin n) (γ : S ^ n) where
  private
    Body : Formula S (suc (suc (suc (suc (suc n)))))
    Body = appAt (sh5 e₁) (suc zero) zero ∧̇ appAt (sh5 e₂) (suc zero) zero

    Inner : (i u v : S) → Type (ℓ-suc ℓ)
    Inner i u v =
      ⟨ (v ∷ u ∷ i ∷ γ) ⊨ appAt (sh3 e₁) (suc (suc zero)) (suc zero) ⟩
      × ( ⟨ (v ∷ u ∷ i ∷ γ) ⊨ appAt (sh3 e₂) (suc (suc zero)) zero ⟩
        × ( ⟨ (v ∷ u ∷ i ∷ γ) ⊨ appAt (sh3 P) (suc zero) zero ⟩
          × ((j : S) → ⟨ fst j ∈ fst i ⟩
             → ⟨ ⋁ S (λ x → (x ∷ j ∷ v ∷ u ∷ i ∷ γ) ⊨ Body) ⟩) ) )

  Agrees : (i : S) → Type (ℓ-suc ℓ)
  Agrees i = (j : S) → ⟨ fst j ∈ fst i ⟩
           → ∥ Σ[ x ∈ S ] ( ⟨ pr (fst j) (fst x) ∈ fst (lookup e₁ γ) ⟩
                          × ⟨ pr (fst j) (fst x) ∈ fst (lookup e₂ γ) ⟩ ) ∥₁

  Differs : Type (ℓ-suc ℓ)
  Differs = Σ[ i ∈ S ] Σ[ u ∈ S ] Σ[ v ∈ S ]
    ( ⟨ fst i ∈ fst (lookup a γ) ⟩
    × ( ⟨ pr (fst i) (fst u) ∈ fst (lookup e₁ γ) ⟩
      × ( ⟨ pr (fst i) (fst v) ∈ fst (lookup e₂ γ) ⟩
        × ( ⟨ pr (fst u) (fst v) ∈ fst (lookup P γ) ⟩ × Agrees i ) ) ) )

  private
    pack : (i u v : S) → Inner i u v → Agrees i
    pack i u v (_ , (_ , (_ , hj))) j hj' = PT.map
      (λ { (x , (p₁ , p₂)) → x
         , ( subst ⟨_⟩
               (appAt-adequate (sh5 e₁) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ)) p₁
           , subst ⟨_⟩
               (appAt-adequate (sh5 e₂) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ)) p₂ ) })
      (hj j hj')

    unpack : (i u v : S) → Agrees i
           → (j : S) → ⟨ fst j ∈ fst i ⟩
           → ⟨ ⋁ S (λ x → (x ∷ j ∷ v ∷ u ∷ i ∷ γ) ⊨ Body) ⟩
    unpack i u v hj j hj' = PT.map
      (λ { (x , (p₁ , p₂)) → x
         , ( subst ⟨_⟩
               (sym (appAt-adequate (sh5 e₁) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ))) p₁
           , subst ⟨_⟩
               (sym (appAt-adequate (sh5 e₂) (suc zero) zero (x ∷ j ∷ v ∷ u ∷ i ∷ γ))) p₂ ) })
      (hj j hj')

  LexAt-in : Differs → ⟨ γ ⊨ LexAt P a e₁ e₂ ⟩
  LexAt-in (i , (u , (v , (hi , (h₁ , (h₂ , (hp , hj)))))))
    = ∣ i , (hi , ∣ u , ∣ v
    , ( subst ⟨_⟩ (sym (appAt-adequate (sh3 e₁) (suc (suc zero)) (suc zero) γ₃)) h₁
      , ( subst ⟨_⟩ (sym (appAt-adequate (sh3 e₂) (suc (suc zero)) zero γ₃)) h₂
        , ( subst ⟨_⟩ (sym (appAt-adequate (sh3 P) (suc zero) zero γ₃)) hp
          , unpack i u v hj ) ) ) ∣₁ ∣₁) ∣₁
    where
    γ₃ : S ^ (suc (suc (suc n)))
    γ₃ = v ∷ u ∷ i ∷ γ

  LexAt-out : ⟨ γ ⊨ LexAt P a e₁ e₂ ⟩ → ∥ Differs ∥₁
  LexAt-out = PT.rec squash₁ atIndex
    where
    atValue : (i u v : S) → ⟨ fst i ∈ fst (lookup a γ) ⟩ → Inner i u v → Differs
    atValue i u v hi h@(h₁ , (h₂ , (hp , _))) = i , (u , (v
      , ( hi
        , ( subst ⟨_⟩
              (appAt-adequate (sh3 e₁) (suc (suc zero)) (suc zero) (v ∷ u ∷ i ∷ γ)) h₁
          , ( subst ⟨_⟩
                (appAt-adequate (sh3 e₂) (suc (suc zero)) zero (v ∷ u ∷ i ∷ γ)) h₂
            , ( subst ⟨_⟩
                  (appAt-adequate (sh3 P) (suc zero) zero (v ∷ u ∷ i ∷ γ)) hp
              , pack i u v h ) ) ) ) ))

    atSecond : (i u : S) → ⟨ fst i ∈ fst (lookup a γ) ⟩
             → Σ[ v ∈ S ] Inner i u v → ∥ Differs ∥₁
    atSecond i u hi (v , h) = ∣ atValue i u v hi h ∣₁

    atFirst : (i : S) → ⟨ fst i ∈ fst (lookup a γ) ⟩
            → Σ[ u ∈ S ] ∥ Σ[ v ∈ S ] Inner i u v ∥₁ → ∥ Differs ∥₁
    atFirst i hi (u , h) = PT.rec squash₁ (atSecond i u hi) h

    atIndex : Σ[ i ∈ S ] ( ⟨ fst i ∈ fst (lookup a γ) ⟩
                         × ∥ Σ[ u ∈ S ] ∥ Σ[ v ∈ S ] Inner i u v ∥₁ ∥₁ )
            → ∥ Differs ∥₁
    atIndex (i , (hi , h)) = PT.rec squash₁ (atFirst i hi) h
```

<!--en-->
## Reading the comparison, and one step of the family

The comparison's reading is its three cases sorted. The object language's
disjunctions are truncated, so the elimination lands in a truncation and the
introduction does not, and the payload is written out rather than inferred.

The step is the family's own step, described. One member of the new stage comes
before another when the least name of the first comes before the least name of
the second, and "least" is said the way it is always said: this is a name of that
set, and no name of that set comes before it. The meta step has **one** branch
since the surplus one was deleted, so this description has one too; the
min-difference formula the plan once wanted to guard a second branch with is not
written, because there is no second branch.

Six binders carry the two names, and they are a **frame** generic in the body
under them. Read directly, packing or unpacking a six-fold existential puts the
whole description under it into normal form, and the description under it reaches
the tower; generic in the body nothing unfolds, and the two readings are one line
each. This is the same law the previous chapters met on a sentence and on a
constructor, met again on a block of binders.
<!--zh-->
## 读那次比较，以及族的一步

比较的读法就是把它的三种情形归类。对象语言的析取是截断的，故消去落在一个截断里、而引入不落，而载荷是写出来的、不是推断出来的。

步进就是这一族自己的那一步，被描述出来。新阶段的一个成员排在另一个之前，当第一个的最小名字排在第二个的最小名字之前；而「最小」按它一贯的说法说出：这是那个集合的一个名字，且那个集合的任何名字都不排在它之前。多余的那一支删除之后，元层面的步进只有**一支**，故这条描述也只有一支；计划当初想用来守卫第二支的最小差公式没有写下，因为没有第二支。

六层绑定承载那两个名字，而它们是一个对其下的体保持通用的**框架**。若直接读，装配或拆解一个六重存在会把它下面的整条描述化为正规形，而它下面那条描述够得到那座塔；对体保持通用则什么也不展开，两条读法各一行。这与前几章在一个句子上、在一个构造子上遇到的是同一条规矩，此番在一整块绑定上再度遇到。
<!--/-->

```agda
module _ {n : ℕ} (R P s₁ a₁ e₁ s₂ a₂ e₂ : Fin n) (γ : S ^ n) where
  Below : Type (ℓ-suc ℓ)
  Below = ⟨ pr (fst (lookup s₁ γ)) (fst (lookup s₂ γ)) ∈ fst (lookup R γ) ⟩
        ⊎ ( (fst (lookup s₂ γ) ≡ fst (lookup s₁ γ))
          × ( ⟨ fst (lookup a₁ γ) ∈ fst (lookup a₂ γ) ⟩
            ⊎ ( (fst (lookup a₂ γ) ≡ fst (lookup a₁ γ))
              × Differs P a₁ e₁ e₂ γ ) ) )

  ≺At-in : Below → ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩
  ≺At-in (inl h) =
    ∣ inl (subst ⟨_⟩ (sym (appAt-adequate R s₁ s₂ γ)) h) ∣₁
  ≺At-in (inr (q , inl h)) = ∣ inr (q , ∣ inl h ∣₁) ∣₁
  ≺At-in (inr (q , inr (q' , h))) =
    ∣ inr (q , ∣ inr (q' , LexAt-in P a₁ e₁ e₂ γ h) ∣₁) ∣₁

  ≺At-out : ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩ → ∥ Below ∥₁
  ≺At-out = PT.rec squash₁ outer
    where
    inner : (fst (lookup s₂ γ) ≡ fst (lookup s₁ γ))
          → ⟨ fst (lookup a₁ γ) ∈ fst (lookup a₂ γ) ⟩
          ⊎ ( (fst (lookup a₂ γ) ≡ fst (lookup a₁ γ))
            × ⟨ γ ⊨ LexAt P a₁ e₁ e₂ ⟩ )
          → ∥ Below ∥₁
    inner q (inl h) = ∣ inr (q , inl h) ∣₁
    inner q (inr (q' , h)) =
      PT.map (λ u → inr (q , inr (q' , u))) (LexAt-out P a₁ e₁ e₂ γ h)

    outer : ⟨ γ ⊨ appAt R s₁ s₂ ⟩
          ⊎ ( (fst (lookup s₂ γ) ≡ fst (lookup s₁ γ))
            × ⟨ γ ⊨ ( (var a₁ ∈̇ var a₂)
                    ∨̇ ( (var a₂ ≐ var a₁) ∧̇ LexAt P a₁ e₁ e₂ ) ) ⟩ )
          → ∥ Below ∥₁
    outer (inl h) = ∣ inl (subst ⟨_⟩ (appAt-adequate R s₁ s₂ γ) h) ∣₁
    outer (inr (q , h)) = PT.rec squash₁ (inner q) h

private
  s6a a6a e6a s6b a6b e6b : ∀ {n} → Fin (suc (suc (suc (suc (suc (suc n))))))
  s6a = suc (suc (suc (suc (suc zero))))
  a6a = suc (suc (suc (suc zero)))
  e6a = suc (suc (suc zero))
  s6b = suc (suc zero)
  a6b = suc zero
  e6b = zero

LeastNameAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n
            → Fin n → Fin n → Fin n → Fin n → Formula S n
LeastNameAt R P B C C₀ s a e d =
  NameAt B C C₀ s a e d
  ∧̇ ∀̇ (∀̇ (∀̇ ( NameAt (sh3 B) (sh3 C) (sh3 C₀)
                      (suc (suc zero)) (suc zero) zero (sh3 d)
             ⇒̇ ¬̇ (≺At (sh3 R) (sh3 P) (suc (suc zero)) (suc zero) zero
                        (sh3 s) (sh3 a) (sh3 e)) )))


∃₆ : ∀ {n} → Formula S (suc (suc (suc (suc (suc (suc n)))))) → Formula S n
∃₆ φ = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ φ)))))

module _ {n : ℕ} (φ : Formula S (suc (suc (suc (suc (suc (suc n))))))) (γ : S ^ n)
         where
  Six : Type (ℓ-suc ℓ)
  Six = Σ[ s₁ ∈ S ] Σ[ k₁ ∈ S ] Σ[ p₁ ∈ S ] Σ[ s₂ ∈ S ] Σ[ k₂ ∈ S ] Σ[ p₂ ∈ S ]
          ⟨ (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) ⊨ φ ⟩

  ∃₆-in : Six → ⟨ γ ⊨ ∃₆ φ ⟩
  ∃₆-in (s₁ , (k₁ , (p₁ , (s₂ , (k₂ , (p₂ , h)))))) =
    ∣ s₁ , ∣ k₁ , ∣ p₁ , ∣ s₂ , ∣ k₂ , ∣ p₂ , h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

  ∃₆-out : ⟨ γ ⊨ ∃₆ φ ⟩ → ∥ Six ∥₁
  ∃₆-out = PT.rec squash₁ at₁
    where
    Body : (s₁ k₁ p₁ s₂ k₂ p₂ : S) → Type (ℓ-suc ℓ)
    Body s₁ k₁ p₁ s₂ k₂ p₂ = ⟨ (p₂ ∷ k₂ ∷ s₂ ∷ p₁ ∷ k₁ ∷ s₁ ∷ γ) ⊨ φ ⟩

    at₆ : (s₁ k₁ p₁ s₂ k₂ : S)
        → Σ[ p₂ ∈ S ] Body s₁ k₁ p₁ s₂ k₂ p₂ → ∥ Six ∥₁
    at₆ s₁ k₁ p₁ s₂ k₂ (p₂ , h) = ∣ s₁ , (k₁ , (p₁ , (s₂ , (k₂ , (p₂ , h))))) ∣₁

    at₅ : (s₁ k₁ p₁ s₂ : S)
        → Σ[ k₂ ∈ S ] ∥ Σ[ p₂ ∈ S ] Body s₁ k₁ p₁ s₂ k₂ p₂ ∥₁ → ∥ Six ∥₁
    at₅ s₁ k₁ p₁ s₂ (k₂ , h) = PT.rec squash₁ (at₆ s₁ k₁ p₁ s₂ k₂) h

    at₄ : (s₁ k₁ p₁ : S)
        → Σ[ s₂ ∈ S ] ∥ Σ[ k₂ ∈ S ]
            ∥ Σ[ p₂ ∈ S ] Body s₁ k₁ p₁ s₂ k₂ p₂ ∥₁ ∥₁ → ∥ Six ∥₁
    at₄ s₁ k₁ p₁ (s₂ , h) = PT.rec squash₁ (at₅ s₁ k₁ p₁ s₂) h

    at₃ : (s₁ k₁ : S)
        → Σ[ p₁ ∈ S ] ∥ Σ[ s₂ ∈ S ] ∥ Σ[ k₂ ∈ S ]
            ∥ Σ[ p₂ ∈ S ] Body s₁ k₁ p₁ s₂ k₂ p₂ ∥₁ ∥₁ ∥₁ → ∥ Six ∥₁
    at₃ s₁ k₁ (p₁ , h) = PT.rec squash₁ (at₄ s₁ k₁ p₁) h

    at₂ : (s₁ : S)
        → Σ[ k₁ ∈ S ] ∥ Σ[ p₁ ∈ S ] ∥ Σ[ s₂ ∈ S ] ∥ Σ[ k₂ ∈ S ]
            ∥ Σ[ p₂ ∈ S ] Body s₁ k₁ p₁ s₂ k₂ p₂ ∥₁ ∥₁ ∥₁ ∥₁ → ∥ Six ∥₁
    at₂ s₁ (k₁ , h) = PT.rec squash₁ (at₃ s₁ k₁) h

    at₁ : Σ[ s₁ ∈ S ] ∥ Σ[ k₁ ∈ S ] ∥ Σ[ p₁ ∈ S ] ∥ Σ[ s₂ ∈ S ] ∥ Σ[ k₂ ∈ S ]
            ∥ Σ[ p₂ ∈ S ] Body s₁ k₁ p₁ s₂ k₂ p₂ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ → ∥ Six ∥₁
    at₁ (s₁ , h) = PT.rec squash₁ (at₂ s₁) h

StepBody : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
         → Formula S (suc (suc (suc (suc (suc (suc n))))))
StepBody R P B C C₀ x y =
    LeastNameAt (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀) s6a a6a e6a (sh6 x)
  ∧̇ ( LeastNameAt (sh6 R) (sh6 P) (sh6 B) (sh6 C) (sh6 C₀) s6b a6b e6b (sh6 y)
    ∧̇ ≺At (sh6 R) (sh6 P) s6a a6a e6a s6b a6b e6b )

StepAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
       → Formula S n
StepAt R P B C C₀ x y = ∃₆ (StepBody R P B C C₀ x y)

module _ {n : ℕ} (R P B C C₀ x y : Fin n) (γ : S ^ n) where
  StepOf : Type (ℓ-suc ℓ)
  StepOf = Six (StepBody R P B C C₀ x y) γ

  StepAt-in : StepOf → ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩
  StepAt-in = ∃₆-in (StepBody R P B C C₀ x y) γ

  StepAt-out : ⟨ γ ⊨ StepAt R P B C C₀ x y ⟩ → ∥ StepOf ∥₁
  StepAt-out = ∃₆-out (StepBody R P B C C₀ x y) γ
```

<!--en-->
## Against the names the meta-language built

A description is a description only if it says what it was meant to say, and
saying so means comparing it with the naming chapter's own comparison. That
comparison decides two of its three keys by orders it was **handed**: the limit
stage's, for the codes, and the carrier's, for the parameters. Those two are what
the description's two relation slots stand for, so the adequacy is stated with
each slot carrying the hypothesis that says which order it holds, in both
directions. Nothing is constructed here; the chapter that has those relations as
sets of the model supplies them.

Between the two comparisons of parameters there is one gap, and closing it is the
whole of the next two sections. Inside, the comparison is a **first difference**:
an index, with agreement below it. Outside, it is a recursion on the two vectors.
They are the same relation, and saying so is an induction on the length, written
once, in both directions.
<!--zh-->
## 对着元语言造出的诸名字

一条描述唯有说出了它本该说的话，才成其为描述；而要说明这一点，就得把它与命名那一章自己的那次比较相比。那次比较的三个键里有两个，是由**交给**它的序来裁决的：诸码由极限阶段的序，诸参数由载体的序。那两个序正是这条描述的两个关系位所代表的东西，故充分性陈述时，每个位都带着「它持有的是哪个序」这条假设，且两个方向都带。此处什么也不造；持有这些关系 (作为模型的集合) 的那一章会供上它们。

参数的那两次比较之间有一道缝，而填平它就是接下来两节的全部。在内部，比较是一次**首次相异**：一个序号，其以下两者相符。在外部，它是对两个向量的一场递归。两者是同一个关系，而把这句话说出来，就是对长度的一次归纳，写一遍，两个方向。
<!--/-->

```agda
module Adequacy (A : V ℓ) (pA : ⟨ isL A ⟩) (w : SWO ⟪ A ⟫) where
  private
    module NM = Naming A w

  open NM using ( Name; arity; params; codeOf; _≺ᵥ_; _≺ₙ_ )
  open SWO w using () renaming ( _<∙_ to _≺ₚ_ )

  Lex : ∀ {k} → Vec ⟪ A ⟫ k → Vec ⟪ A ⟫ k → Type (ℓ-suc ℓ)
  Lex {k} p q = Σ[ i ∈ Fin k ]
    ( (lookup i p ≺ₚ lookup i q)
    × ((j : Fin k) → toℕ j < toℕ i → lookup j p ≡ lookup j q) )

  lex-vec : ∀ {k} (p q : Vec ⟪ A ⟫ k) → Lex p q → p ≺ᵥ q
  lex-vec (x ∷ p) (y ∷ q) (zero  , (h , _)) = inl h
  lex-vec (x ∷ p) (y ∷ q) (suc i , (h , ag)) =
    inr (ag zero (suc-≤-suc zero-≤) , lex-vec p q (i , (h , λ j hj → ag (suc j) (suc-≤-suc hj))))

  vec-lex : ∀ {k} (p q : Vec ⟪ A ⟫ k) → p ≺ᵥ q → Lex p q
  vec-lex []      []      h = Empty.rec* h
  vec-lex (x ∷ p) (y ∷ q) (inl h) = zero , (h , λ j hj → Empty.rec (¬-<-zero hj))
  vec-lex (x ∷ p) (y ∷ q) (inr (e , h)) = suc (vec-lex p q h .fst)
    , ( vec-lex p q h .snd .fst
      , step )
    where
    step : (j : Fin (suc _)) → toℕ j < suc (toℕ (vec-lex p q h .fst))
         → lookup j (x ∷ p) ≡ lookup j (y ∷ q)
    step zero    _  = e
    step (suc j) hj = vec-lex p q h .snd .snd j (pred-≤-pred hj)
```

<!--en-->
## The parameters, on both sides

The parameter key is where the two languages are furthest apart, so it is bridged
on its own. An index inside is a member of the arity numeral; an index outside is
an element of a finite index type; the numerals chapter turns each into the other.
A value inside is read by application, and the environment chapter's lookup
equation says the value read is the value the family has there. The parameter
order's slot then decides the comparison, and the agreement below the index is the
same translation again, under a bounded universal, with the injectivity of the
carrier's index map turning an equality of sets back into an equality of members.

Both directions are written because both are used: one turns a first difference
between the two vectors into a satisfaction of the bounded quantification, and the
other turns a satisfaction back into a first difference. The second vector arrives
at the first's length, moved there by the equality of arities the second key has
just pronounced, which is why the two sequences can be compared at all.
<!--zh-->
## 参数，两边各说一遍

参数这个键是两种语言相隔最远之处，故它单独架桥。内部的序号是元数数码的成员；外部的序号是有穷索引类型的元素；数码那一章把两者互相转换。内部的取值靠取值读出，而环境那一章的查表等式说：读出的取值就是那个族在那里的取值。随后由参数序的那一位裁决比较，而序号以下的相符是同一次翻译再来一遍、置于一个有界全称之下，并由载体索引映射的单射性把集合之间的等式换回成员之间的等式。

两个方向都写，因为两个方向都要用：一个把两个向量之间的首次相异变成对那次有界量化的满足，另一个把满足变回首次相异。第二个向量到场时已在第一个的长度上，是由第二个键刚刚宣布的元数等式挪过去的，而这正是那两个序列根本谈得上比较的原因。
<!--/-->

```agda
  open SWO limitOrder using () renaming ( _<∙_ to _≺ˡ_ )

  ix : ⟪ A ⟫ → V ℓ
  ix m = ⟪ A ⟫↪ m

  ixL : ⟪ A ⟫ → S
  ixL m = ix m , isL-trans (∈∈ₛ {a = ix m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)) pA

  pfam : (t : Name) → Fin (arity t) → V ℓ
  pfam t i = ix (lookup i (params t))

  ix-inj : (u v : ⟪ A ⟫) → ix u ≡ ix v → u ≡ v
  ix-inj u v = isEmbedding→Inj isEmb⟪ A ⟫↪ u v

  module Keys (Rs Ps : S)
              (Rrep : (u v : Limit) → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩ → u ≺ˡ v)
              (Rfill : (u v : Limit) → u ≺ˡ v → ⟨ pr (fst u) (fst v) ∈ fst Rs ⟩)
              (Prep : (u v : ⟪ A ⟫) → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩ → u ≺ₚ v)
              (Pfill : (u v : ⟪ A ⟫) → u ≺ₚ v → ⟨ pr (ix u) (ix v) ∈ fst Ps ⟩)
              where

    module _ {n : ℕ} (P a₁ e₁ e₂ : Fin n) (γ : S ^ n) (t₁ t₂ : Name)
             (qP : fst (lookup P γ) ≡ fst Ps)
             (qa : fst (lookup a₁ γ) ≡ # (arity t₁))
             (qk : arity t₂ ≡ arity t₁)
             (q₁ : fst (lookup e₁ γ) ≡ env (pfam t₁))
             (q₂ : fst (lookup e₂ γ)
                 ≡ env (λ i → ix (lookup i (subst (Vec ⟪ A ⟫) qk (params t₂)))))
             where
      private
        pr₁ : Fin (arity t₁) → ⟪ A ⟫
        pr₁ i = lookup i (params t₁)

        pr₂ : Fin (arity t₁) → ⟪ A ⟫
        pr₂ i = lookup i (subst (Vec ⟪ A ⟫) qk (params t₂))

        at₁ : (i : Fin (arity t₁)) (u : S)
            → ⟨ pr (# (toℕ i)) (fst u) ∈ fst (lookup e₁ γ) ⟩ → fst u ≡ ix (pr₁ i)
        at₁ i u h = subst ⟨_⟩ (lookup-spec (pfam t₁) i (fst u))
          (subst (λ z → ⟨ pr (# (toℕ i)) (fst u) ∈ z ⟩) q₁ h)

        at₂ : (i : Fin (arity t₁)) (u : S)
            → ⟨ pr (# (toℕ i)) (fst u) ∈ fst (lookup e₂ γ) ⟩ → fst u ≡ ix (pr₂ i)
        at₂ i u h = subst ⟨_⟩ (lookup-spec (λ j → ix (pr₂ j)) i (fst u))
          (subst (λ z → ⟨ pr (# (toℕ i)) (fst u) ∈ z ⟩) q₂ h)

        put₁ : (i : Fin (arity t₁))
             → ⟨ pr (# (toℕ i)) (ix (pr₁ i)) ∈ fst (lookup e₁ γ) ⟩
        put₁ i = subst (λ z → ⟨ pr (# (toℕ i)) (ix (pr₁ i)) ∈ z ⟩) (sym q₁)
          (subst ⟨_⟩ (sym (lookup-spec (pfam t₁) i (ix (pr₁ i)))) refl)

        put₂ : (i : Fin (arity t₁))
             → ⟨ pr (# (toℕ i)) (ix (pr₂ i)) ∈ fst (lookup e₂ γ) ⟩
        put₂ i = subst (λ z → ⟨ pr (# (toℕ i)) (ix (pr₂ i)) ∈ z ⟩) (sym q₂)
          (subst ⟨_⟩ (sym (lookup-spec (λ j → ix (pr₂ j)) i (ix (pr₂ i)))) refl)

        numAt : (m : ℕ) → S
        numAt m = # m , numL m

      lex-fill : Lex (params t₁) (subst (Vec ⟪ A ⟫) qk (params t₂))
               → Differs P a₁ e₁ e₂ γ
      lex-fill (i , (hlt , agree)) = numAt (toℕ i)
        , ( ixL (pr₁ i) , ( ixL (pr₂ i)
        , ( subst (λ z → ⟨ # (toℕ i) ∈ z ⟩) (sym qa)
              (#mono (toℕ i) (arity t₁) (toℕ<n i))
          , ( put₁ i
            , ( put₂ i
              , ( subst (λ z → ⟨ pr (ix (pr₁ i)) (ix (pr₂ i)) ∈ z ⟩) (sym qP)
                    (Pfill (pr₁ i) (pr₂ i) hlt)
                , agrees ) ) ) ) ) )
        where
        agrees : Agrees P a₁ e₁ e₂ γ (numAt (toℕ i))
        agrees j hj = PT.map step (∈#-elim (toℕ i) (fst j) hj)
          where
          step : Σ[ m ∈ ℕ ] ((m < toℕ i) × (fst j ≡ # m))
               → Σ[ x ∈ S ] ( ⟨ pr (fst j) (fst x) ∈ fst (lookup e₁ γ) ⟩
                            × ⟨ pr (fst j) (fst x) ∈ fst (lookup e₂ γ) ⟩ )
          step (m , (hm , qj)) = ixL (pr₁ jx)
            , ( subst (λ z → ⟨ pr z (ix (pr₁ jx)) ∈ fst (lookup e₁ γ) ⟩)
                  (sym qjx) (put₁ jx)
              , subst (λ z → ⟨ pr z (ix (pr₁ jx)) ∈ fst (lookup e₂ γ) ⟩) (sym qjx)
                  (subst (λ y → ⟨ pr (# (toℕ jx)) (ix y) ∈ fst (lookup e₂ γ) ⟩)
                    (sym (agree jx (subst (_< toℕ i) (sym qm) hm))) (put₂ jx)) )
            where
            jx : Fin (arity t₁)
            jx = fromℕ' (arity t₁) m (<-trans hm (toℕ<n i))
            qm : toℕ jx ≡ m
            qm = toFromId' (arity t₁) m (<-trans hm (toℕ<n i))
            qjx : fst j ≡ # (toℕ jx)
            qjx = qj ∙ cong #_ (sym qm)

      lex-read : Differs P a₁ e₁ e₂ γ
               → ∥ Lex (params t₁) (subst (Vec ⟪ A ⟫) qk (params t₂)) ∥₁
      lex-read (i , (u , (v , (hi , (h₁ , (h₂ , (hp , ag))))))) =
        PT.map atIndex (∈#-elim (arity t₁) (fst i)
          (subst (λ z → ⟨ fst i ∈ z ⟩) qa hi))
        where
        atIndex : Σ[ m ∈ ℕ ] ((m < arity t₁) × (fst i ≡ # m))
                → Lex (params t₁) (subst (Vec ⟪ A ⟫) qk (params t₂))
        atIndex (m , (hm , qi)) = ι , (below , agrees)
          where
          ι : Fin (arity t₁)
          ι = fromℕ' (arity t₁) m hm
          qι : fst i ≡ # (toℕ ι)
          qι = qi ∙ cong #_ (sym (toFromId' (arity t₁) m hm))
          qu : fst u ≡ ix (pr₁ ι)
          qu = at₁ ι u (subst (λ z → ⟨ pr z (fst u) ∈ fst (lookup e₁ γ) ⟩) qι h₁)
          qv : fst v ≡ ix (pr₂ ι)
          qv = at₂ ι v (subst (λ z → ⟨ pr z (fst v) ∈ fst (lookup e₂ γ) ⟩) qι h₂)
          below : pr₁ ι ≺ₚ pr₂ ι
          below = Prep (pr₁ ι) (pr₂ ι)
            (subst2 (λ y z → ⟨ pr y z ∈ fst Ps ⟩) qu qv
              (subst (λ z → ⟨ pr (fst u) (fst v) ∈ z ⟩) qP hp))
          agrees : (j : Fin (arity t₁)) → toℕ j < toℕ ι → pr₁ j ≡ pr₂ j
          agrees j hj = ix-inj (pr₁ j) (pr₂ j)
            (PT.rec (setIsSet (ix (pr₁ j)) (ix (pr₂ j))) same
              (ag (numAt (toℕ j))
                (subst (λ z → ⟨ # (toℕ j) ∈ z ⟩) (sym qι) (#mono (toℕ j) (toℕ ι) hj))))
            where
            same : Σ[ x ∈ S ] ( ⟨ pr (# (toℕ j)) (fst x) ∈ fst (lookup e₁ γ) ⟩
                              × ⟨ pr (# (toℕ j)) (fst x) ∈ fst (lookup e₂ γ) ⟩ )
                 → ix (pr₁ j) ≡ ix (pr₂ j)
            same (x , (k₁ , k₂)) = sym (at₁ j x k₁) ∙ at₂ j x k₂
```

<!--en-->
## Both halves

With the three keys bridged, each half is the three cases sorted. The equality of
codes is an equality of underlying sets, because membership in the limit stage is
a proposition; the equality of arities is an equality of numerals, and numerals
are injective; and the parameters pass through the first-difference bridge, moved
along the equality of arities exactly once in each direction, by path induction.

What comes out is the chapter's theorem, at **variable** slots in a variable
environment, with every slot reached by an equation: the order formula holds of
two names' data exactly when the naming chapter's comparison holds of the two
names. The description is a description, and the next chapter can separate with
it.

## Recap

`InLimitAt`{.Agda} is the skeleton's **stage** condition, one membership atom in
the limit stage said through the sequence chapter's graph at the constant
`ωʟ`{.Agda}. It is not constant-freeness, and saying so is this chapter's own
correction: a hereditarily finite code may name hereditarily finite constants,
and over a carrier containing the limit stage those are members of the carrier.

`FreeAt`{.Agda} is constant-freeness, and it is one membership atom as well: the
key made from the arity and the skeleton lies in the code set **at the empty
alphabet**. `freeCode-in`{.Agda} and `freeCode-out`{.Agda} are that set's two
directions at that alphabet, resting on the fact that a parameter-free formula
has the same code at either alphabet; `codeFree-in`{.Agda} and
`codeFree-out`{.Agda} read them at slots, so the skeleton slot holds exactly the
codes of the parameter-free formulas of one more variable than the arity, which
is exactly a meta name's formula. `domAt-numeral`{.Agda} says how long a
sequence is, and
`graphAt-value`{.Agda}/`graphAt-only`{.Agda} are the satisfaction table's two
halves at a carrier held in a slot.

`NameAt`{.Agda} is a name described at slots: a skeleton in the limit stage and
free of constants, a parameter sequence over the carrier whose domain is the
arity, and a denotation written as one `extAt`{.Agda} whose condition reads the
value `satGraphAt`{.Agda} assigns at the key the arity and the skeleton make.
Two code sets reach it as slots: the one at the carrier, without which the
graph's existentially bound table pins nothing, and the one at the empty
alphabet, without which the skeleton is not a meta name's.

`≺At`{.Agda} is the comparison, and it runs **no recursion**: one membership atom
against the order-so-far, a membership atom between numerals for the arity, and a
bounded lexicographic quantification for the parameters. `StepAt`{.Agda} is one
step of the family, with **one** branch, said by least names.

`order-in`{.Agda} and `order-out`{.Agda} are the two adequacy halves, at variable
slots in a variable environment: with each relation slot carrying the hypothesis
that says which order it holds, the formula holds of two names' data exactly when
`_≺ₙ_`{.Agda} holds of the names.

What is not here yet is the adequacy of `StepAt`{.Agda} against the step order
itself. With the skeleton pinned, the description's names are the meta ones on
the key the gap was about; a full statement still wants the parameter sequence
read back as a vector, the denotation identified with the meta name's, and the
least of the description's names identified with the least of the meta ones.
Those are bookkeeping against chapters that already exist, and they are the next
chapter's first job.
<!--zh-->
## 两半

三个键架好桥之后，每一半都是把三种情形归类。诸码的等式是底集之间的等式，因为「属于极限阶段」是命题；诸元数的等式是数码之间的等式，而数码单射；诸参数则经首次相异那座桥通过，并由路径归纳沿元数的等式在每个方向各挪一次。

出来的就是本章的定理，落在变元环境的**变元**位上，每个位都经一条等式抵达：序公式对两个名字的数据成立，当且仅当命名那一章的比较对那两个名字成立。描述成其为描述，而下一章可以拿它去作分离。

## 小结

`InLimitAt`{.Agda} 是骨架的**阶段**条件，即经序列那一章的图在常元 `ωʟ`{.Agda} 处说出的、一个「属于极限阶段」的隶属原子。它不是无参性，而把这句话说出来正是本章对自己的更正：遗传有穷的码可以点名遗传有穷的常量，而在一个含有极限阶段的载体之上，那些常量正是载体的成员。

`FreeAt`{.Agda} 才是无参性，而它同样是一个隶属原子：由元数与骨架造出的那个键，落在**空字母表处**的码集中。`freeCode-in`{.Agda} 与 `freeCode-out`{.Agda} 是那个集合在那个字母表处的两个方向，所倚的事实是一条无参公式在两个字母表上有同一个码；`codeFree-in`{.Agda} 与 `codeFree-out`{.Agda} 把它们读在诸位上，于是骨架那一位所持有的，恰是「比元数多一个变量的诸无参公式」的诸码，而那正是元层面一个名字的公式。`domAt-numeral`{.Agda} 说清一个序列有多长，而 `graphAt-value`{.Agda} 与 `graphAt-only`{.Agda} 是满足关系表的两半，落在握于一位上的载体处。

`NameAt`{.Agda} 是描述在诸位上的名字：一个落在极限阶段且不带常量的骨架、一个定义域为元数的载体之上参数序列，以及一个写成单次 `extAt`{.Agda} 的指称，其条件读的是 `satGraphAt`{.Agda} 在「由元数与骨架造出的键」处所指派的取值。有两个码集以位的身份抵达它：载体处那一个，没有它，图那张作存在绑定的表什么也钉不住；以及空字母表处那一个，没有它，那个骨架就不是元层面某个名字的骨架。

`≺At`{.Agda} 是那次比较，而它**不跑递归**：一个对着既有之序的隶属原子、一个数码之间的隶属原子作元数之用，以及一次为参数所设的有界字典序量化。`StepAt`{.Agda} 是这一族的一步，只有**一**支，按最小名字说出。

`order-in`{.Agda} 与 `order-out`{.Agda} 是那两半充分性，落在变元环境的变元位上：只要每个关系位都带着「它持有的是哪个序」这条假设，那条公式对两个名字的数据成立，当且仅当 `_≺ₙ_`{.Agda} 对那两个名字成立。

尚未在此的，是 `StepAt`{.Agda} 对着步进序本身的充分性。骨架钉住之后，在那道缝所关乎的那个键上，这条描述的诸名字就是元层面的诸名字；而一条完整的陈述还要：把参数序列读回成向量、把指称与元层面名字的指称认同，以及把这条描述诸名字中的最小者与元层面诸名字中的最小者认同。那些是对着早已存在的诸章记账，而它们是下一章的头一件事。
<!--/-->

```agda
    private
      envShift : (t : Name) {k : ℕ} (e : arity t ≡ k)
               → env (λ i → ix (lookup i (subst (Vec ⟪ A ⟫) e (params t))))
               ≡ env (pfam t)
      envShift t = J
        (λ k' e' → env (λ i → ix (lookup i (subst (Vec ⟪ A ⟫) e' (params t))))
                 ≡ env (pfam t))
        (cong (λ v → env (λ i → ix (lookup i v)))
          (substRefl {B = Vec ⟪ A ⟫} (params t)))

      vecShift : {i j k : ℕ} (e : i ≡ j) (p : Vec ⟪ A ⟫ k) (q : Vec ⟪ A ⟫ i)
               → (p ≺ᵥ subst (Vec ⟪ A ⟫) e q) ≡ (p ≺ᵥ q)
      vecShift {i} e p q =
        J (λ j' e' → (p ≺ᵥ subst (Vec ⟪ A ⟫) e' q) ≡ (p ≺ᵥ q))
          (cong (λ v → p ≺ᵥ v) (substRefl {B = Vec ⟪ A ⟫} q)) e

    module _ {n : ℕ} (R P s₁ a₁ e₁ s₂ a₂ e₂ : Fin n) (γ : S ^ n) (t₁ t₂ : Name)
             (qR : fst (lookup R γ) ≡ fst Rs) (qP : fst (lookup P γ) ≡ fst Ps)
             (qs₁ : fst (lookup s₁ γ) ≡ fst (codeOf t₁))
             (qs₂ : fst (lookup s₂ γ) ≡ fst (codeOf t₂))
             (qa₁ : fst (lookup a₁ γ) ≡ # (arity t₁))
             (qa₂ : fst (lookup a₂ γ) ≡ # (arity t₂))
             (qe₁ : fst (lookup e₁ γ) ≡ env (pfam t₁))
             (qe₂ : fst (lookup e₂ γ) ≡ env (pfam t₂)) where
      private
        codeSame : fst (lookup s₂ γ) ≡ fst (lookup s₁ γ) → codeOf t₂ ≡ codeOf t₁
        codeSame q = Σ≡Prop (λ x → snd (x ∈ Lset ω)) (sym qs₂ ∙ q ∙ qs₁)

        codeBack : codeOf t₂ ≡ codeOf t₁ → fst (lookup s₂ γ) ≡ fst (lookup s₁ γ)
        codeBack ec = qs₂ ∙ cong fst ec ∙ sym qs₁

        shiftEnv : (ek : arity t₂ ≡ arity t₁)
                 → fst (lookup e₂ γ)
                 ≡ env (λ i → ix (lookup i (subst (Vec ⟪ A ⟫) ek (params t₂))))
        shiftEnv ek = qe₂ ∙ sym (envShift t₂ ek)

      order-in : t₁ ≺ₙ t₂ → ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩
      order-in (inl h) = ≺At-in R P s₁ a₁ e₁ s₂ a₂ e₂ γ
        (inl (subst (λ z → ⟨ pr (fst (lookup s₁ γ)) (fst (lookup s₂ γ)) ∈ z ⟩)
                (sym qR)
                (subst2 (λ y z → ⟨ pr y z ∈ fst Rs ⟩) (sym qs₁) (sym qs₂)
                  (Rfill (codeOf t₁) (codeOf t₂) h))))
      order-in (inr (ec , inl h)) = ≺At-in R P s₁ a₁ e₁ s₂ a₂ e₂ γ
        (inr (codeBack ec , inl
          (subst2 (λ y z → ⟨ y ∈ z ⟩) (sym qa₁) (sym qa₂)
            (#mono (arity t₁) (arity t₂) h))))
      order-in (inr (ec , inr (ek , hv))) = ≺At-in R P s₁ a₁ e₁ s₂ a₂ e₂ γ
        (inr (codeBack ec , inr (qa₂ ∙ cong #_ ek ∙ sym qa₁
          , lex-fill P a₁ e₁ e₂ γ t₁ t₂ qP qa₁ ek qe₁ (shiftEnv ek)
              (vec-lex (params t₁) (subst (Vec ⟪ A ⟫) ek (params t₂))
                (transport (sym (vecShift ek (params t₁) (params t₂))) hv)))))

      order-out : ⟨ γ ⊨ ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ ⟩ → ∥ t₁ ≺ₙ t₂ ∥₁
      order-out h = PT.rec squash₁ read (≺At-out R P s₁ a₁ e₁ s₂ a₂ e₂ γ h)
        where
        read : Below R P s₁ a₁ e₁ s₂ a₂ e₂ γ → ∥ t₁ ≺ₙ t₂ ∥₁
        read (inl k) = ∣ inl (Rrep (codeOf t₁) (codeOf t₂)
          (subst2 (λ y z → ⟨ pr y z ∈ fst Rs ⟩) qs₁ qs₂
            (subst (λ z → ⟨ pr (fst (lookup s₁ γ)) (fst (lookup s₂ γ)) ∈ z ⟩)
              qR k))) ∣₁
        read (inr (q , inl k)) = ∣ inr (codeSame q , inl
          (#∈#-elim (arity t₁) (arity t₂)
            (subst2 (λ y z → ⟨ y ∈ z ⟩) qa₁ qa₂ k))) ∣₁
        read (inr (q , inr (q' , dif))) = PT.map atLex
          (lex-read P a₁ e₁ e₂ γ t₁ t₂ qP qa₁ ek qe₁ (shiftEnv ek) dif)
          where
          ek : arity t₂ ≡ arity t₁
          ek = #-inj′ (sym qa₂ ∙ q' ∙ qa₁)
          atLex : Lex (params t₁) (subst (Vec ⟪ A ⟫) ek (params t₂)) → t₁ ≺ₙ t₂
          atLex lx = inr (codeSame q , inr (ek
            , transport (vecShift ek (params t₁) (params t₂))
                (lex-vec (params t₁) (subst (Vec ⟪ A ⟫) ek (params t₂)) lx)))
```
