# The description is faithful

<!--en-->
The previous chapter turned the order at every stage into an object of `L`, and
left that construction standing on two hypotheses saying what the step condition
means. Filling them is not one obligation but three: the adequacy of the step
description against the meta step, the birth stage said in the object language,
which nothing said yet, and the code set at a carrier that moves with the birth.
This chapter settles the second and the third, and turns the two hypotheses into
**one**, which is the step at a single carrier.

The reduction is what the chapter is for, so it is worth stating exactly. The
order family is birth-primary: two members of a stage are compared by the moments
they were carved at, and only two carved at the same moment are compared by the
machinery of that moment. So the condition the previous chapter asked for splits,
and the birth half is the larger one. Written down, it needs no successor
operation: a set's birth is the ordinal whose tower does not hold the set while
the definable powerset of that tower does, and both of those are membership atoms
over descriptions that already exist.

What does not close is the step itself. The chapter says so with a named
parameter carrying its own meaning as a hypothesis, and never with an
approximation.
<!--zh-->
上一章把每个阶段处的序变成了 `L` 的一个对象，而那个构造是撑在两条假设上的，它们说清那条步进条件是什么意思。填它们不是一笔债、而是三笔：步进描述对着元层面那一步的充分性；诞生阶段在对象语言里的说法，至今无人说过；以及在一个随诞生阶段移动的载体上的码集。本章了结第二笔与第三笔，并把那两条假设变成**一**条，即单个载体处的那一步。

这次归约正是本章的用意所在，故值得说准。序之族以诞生阶段为主键：一个阶段的两个成员，按它们各自被雕出的时刻比较，只有在同一时刻被雕出的两个，才由那个时刻的机器来比较。于是上一章所索取的那条条件裂开了，而诞生阶段那一半是较大的一半。写下来，它不需要后继运算：一个集合的诞生阶段，是这样的序数，它的塔不装这个集合、而那座塔的可定义幂集装它；这两件事都是原子，且都架在早已存在的描述之上。

不能了结的是那一步自身。本章以一个具名参数把这句话说出来，参数自带它的含义作为假设，而绝不用近似物顶替。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Choice.Faithful {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd; isPropIsOrd; Lset-mono; Lset→isL; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; LsetS; 𝒟ₒS; extensionalL )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem; stage-earliest )
open import L.Choice.Stage {ℓ} lem using ( ord-suc-inj )
open import L.Choice.Step {ℓ} lem
  using ( birth; birth-ord; birth-suc; birth-mem; birth-stage; birth-proof
        ; Mem; New; relOf; carry; Under; stepAt
        ; orderAt; orderAt-step; module Family )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-in; extAt-out; extAt-in-both; prAtL; prAtL-adequate )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Powerset {ℓ} lem using ( DefAt; DefAt-stage )
open import L.Coding.CodeSet {ℓ} lem
  using ( arityNumAtL; arityNumAtL-in; arityNumAtL-out; hasWitnessAt
        ; witnessAt-in; witnessAt-out; keyS; codeS
        ; AllCodes; AllCodes-in; AllCodes-out; IsKeyOverAny )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Choice.Table {ℓ} lem
  using ( Ordering; strict; Related; IsRel; Values; Entries
        ; related-in; module Described )
open import V.Coding {ℓ} using ( pr )

import FOL.Absoluteness
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ ; ⟦_⟧ᵐ to ⟦_⟧ )

sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
sh2 i = suc (suc i)

sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
sh3 i = suc (suc (suc i))

private
  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = suc (suc (suc (suc i)))

  tm4 : ∀ {n} → Term S n → Term S (suc (suc (suc (suc n))))
  tm4 (con k) = con k
  tm4 (var i) = var (sh4 i)

  tm4-val : ∀ {n} (t : Term S n) (a b c d : S) (γ : S ^ n)
          → ⟦ tm4 t ⟧ (d ∷ c ∷ b ∷ a ∷ γ) ≡ ⟦ t ⟧ γ
  tm4-val (con k) a b c d γ = refl
  tm4-val (var i) a b c d γ = refl
```

Perf: the two witnesses the birth description is satisfied at are sealed;
unsealed, the chapter's first section alone runs 178 s instead of 2 s.

```agda
opaque
  towerS : (β : V ℓ) → IsOrd β → S
  towerS β ob = LsetS β ob

  towerS-fst : (β : V ℓ) (ob : IsOrd β) → fst (towerS β ob) ≡ Lset β
  towerS-fst β ob = refl

  powS : (β : V ℓ) → IsOrd β → S
  powS β ob = 𝒟ₒS β ob

  powS-fst : (β : V ℓ) (ob : IsOrd β) → fst (powS β ob) ≡ 𝒟ₒ (Lset β)
  powS-fst β ob = refl
```

<!--en-->
## The birth stage, said inside

The description binds two sets and names no constant. There is a `c` which is the
tower at `b`; `x` does not belong to it; and there is a `d` which is the definable
powerset of `c`, to which `x` does belong. `Lset-suc`{.Agda} is what makes those
two conditions equivalent to "`b` is one below the least stage containing `x`",
and it is spent only on the meta side. That is why the sentence needs no successor
operation of its own, and why the tower graph is used at the slot `b` itself
rather than at a successor of it.

Both readings stand at **variable** slots in a variable environment, with
ordinality at the `b` slot as the only hypothesis. Soundness is a trichotomy
against the least stage, and it is a named helper with its conclusion written
down: the first branch is refuted by `stage-earliest`{.Agda}, the second is
`ord-suc-inj`{.Agda} against `birth-suc`{.Agda}, and the third is
`∈sucV-elim`{.Agda} into two contradictions with the non-membership. Completeness
is shorter, because `Lset-defines`{.Agda} and `DefAt-stage`{.Agda} each run one
line the other way.

The two elements the description is satisfied at are **sealed**, and the marker
records the measurement rather than a preference: unsealed, this section alone
runs 178 s where sealed it runs 2 s. `Lset`{.Agda} and `𝒟ₒ`{.Agda} are already
sealed where they are built, but the pairs that carry their constructibility
proofs are not, and it is the pair that reaches the slot.
<!--zh-->
## 诞生阶段，在内部说出

这条描述绑定两个集合，且不点名任何常元。存在一个 `c`，它是 `b` 处的塔；`x` 不属于它；并且存在一个 `d`，它是 `c` 的可定义幂集，而 `x` 属于它。使这两条条件等价于「`b` 比包含 `x` 的最小阶段低一级」的，是 `Lset-suc`{.Agda}，而它只花在元层面这一侧。这正是那个句子不需要自备后继运算的原因，也是塔之图用在 `b` 那一位自身、而不是用在它的一个后继上的原因。

两条读式都站在变元环境的**变元**位上，唯一的假设是 `b` 那一位的序数性。可靠性是一次对着最小阶段的三歧分情形，而它是一个把结论写出来的具名辅助：第一支由 `stage-earliest`{.Agda} 驳倒，第二支是 `ord-suc-inj`{.Agda} 对着 `birth-suc`{.Agda}，第三支是 `∈sucV-elim`{.Agda} 分成两条与非隶属相冲的矛盾。完备性更短，因为 `Lset-defines`{.Agda} 与 `DefAt-stage`{.Agda} 各自反着跑一行。

这条描述所满足于其上的那两个元素被**封印**，而那条标记记录的是实测、不是偏好：不封印，仅这一节就跑 178 秒，封印后是 2 秒。`Lset`{.Agda} 与 `𝒟ₒ`{.Agda} 在它们被造出之处早已封印，但携带它们可构造性证明的那两个对没有，而抵达槽位的正是那个对。
<!--/-->

```agda
BirthAt : ∀ {n} → Fin n → Fin n → Formula S n
BirthAt b x =
  ∃̇ ( LsetGraphAt zero (suc b)
    ∧̇ ( ¬̇ (var (suc x) ∈̇ var zero)
      ∧̇ ∃̇ ( DefAt zero (suc zero) ∧̇ (var (sh2 x) ∈̇ var zero) ) ) )

module _ {n : ℕ} (b x : Fin n) (γ : S ^ n) where
  private
    β : V ℓ
    β = fst (lookup b γ)

    z : S
    z = lookup x γ

    Inner : S → Type (ℓ-suc ℓ)
    Inner c = Σ[ d ∈ S ]
      ( ⟨ (d ∷ c ∷ γ) ⊨ DefAt zero (suc zero) ⟩ × ⟨ fst z ∈ fst d ⟩ )

    Outer : S → Type (ℓ-suc ℓ)
    Outer c = ⟨ (c ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
            × ( (⟨ fst z ∈ fst c ⟩ → Lift {j = ℓ-suc ℓ} Empty.⊥) × ∥ Inner c ∥₁ )

    decideBirth : IsOrd β → ⟨ fst z ∈ 𝒟ₒ (Lset β) ⟩
                → (⟨ fst z ∈ Lset β ⟩ → Empty.⊥)
                → β ≡ birth (fst z) (snd z)
    decideBirth ob hin hout = go (ord-tri (sucV β) (suc-ord ob)
                                          (stage (fst z) (snd z))
                                          (stage-ord (fst z) (snd z)))
      where
      mem : ⟨ fst z ∈ Lset (sucV β) ⟩
      mem = subst (λ u → ⟨ fst z ∈ u ⟩) (sym (Lset-suc β)) hin

      early : ⟨ stage (fst z) (snd z) ∈ sucV β ⟩ → Empty.⊥
      early h = Empty.rec* (∈sucV-elim {A = β} {x = stage (fst z) (snd z)}
        Empty.isProp⊥* h below same)
        where
        below : ⟨ stage (fst z) (snd z) ∈ β ⟩ → Empty.⊥*
        below k = Empty.rec (hout
          (Lset-mono {α = β} {β = stage (fst z) (snd z)} k
            {x = fst z} (stage-mem (fst z) (snd z))))
        same : stage (fst z) (snd z) ≡ β → Empty.⊥*
        same e = Empty.rec (hout (subst (λ u → ⟨ fst z ∈ Lset u ⟩) e
          (stage-mem (fst z) (snd z))))

      go : ⟨ sucV β ∈ stage (fst z) (snd z) ⟩
         ⊎ ((sucV β ≡ stage (fst z) (snd z)) ⊎ ⟨ stage (fst z) (snd z) ∈ sucV β ⟩)
         → β ≡ birth (fst z) (snd z)
      go (inl h) = Empty.rec
        (stage-earliest (fst z) (snd z) (sucV β) (suc-ord ob) mem h)
      go (inr (inl e)) = ord-suc-inj β (birth (fst z) (snd z)) ob
        (e ∙ sym (birth-suc (fst z) (snd z)))
      go (inr (inr h)) = Empty.rec (early h)

  BirthAt-out : ⟨ γ ⊨ BirthAt b x ⟩ → IsOrd β → β ≡ birth (fst z) (snd z)
  BirthAt-out h ob =
    PT.rec (setIsSet β (birth (fst z) (snd z))) atCarrier h
    where
    atInner : (c : S) → ⟨ (c ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
            → (⟨ fst z ∈ fst c ⟩ → Empty.⊥)
            → Inner c → β ≡ birth (fst z) (snd z)
    atInner c hg hn (d , (hd , hm)) = decideBirth ob
      (subst (λ u → ⟨ fst z ∈ u ⟩) qd hm)
      (λ k → hn (subst (λ u → ⟨ fst z ∈ u ⟩) (sym qc) k))
      where
      qc : fst c ≡ Lset β
      qc = Lset-only zero (suc b) (c ∷ γ) hg ob
      qd : fst d ≡ 𝒟ₒ (Lset β)
      qd = subst ⟨_⟩ (DefAt-stage β ob zero (suc zero) (d ∷ c ∷ γ) qc) hd

    atCarrier : Σ[ c ∈ S ] Outer c → β ≡ birth (fst z) (snd z)
    atCarrier (c , (hg , (hn , hi))) =
      PT.rec (setIsSet β (birth (fst z) (snd z)))
        (atInner c hg (λ k → lower (hn k))) hi

  BirthAt-in : IsOrd β → β ≡ birth (fst z) (snd z) → ⟨ γ ⊨ BirthAt b x ⟩
  BirthAt-in ob e = ∣ towerS β ob
    , (hg , (hn , ∣ powS β ob , (hd , hm) ∣₁)) ∣₁
    where
    hg : ⟨ (towerS β ob ∷ γ) ⊨ LsetGraphAt zero (suc b) ⟩
    hg = Lset-defines zero (suc b) (towerS β ob ∷ γ) ob (towerS-fst β ob)

    hn : ⟨ fst z ∈ fst (towerS β ob) ⟩ → Lift {j = ℓ-suc ℓ} Empty.⊥
    hn k = lift (stage-earliest (fst z) (snd z) β ob
      (subst (λ u → ⟨ fst z ∈ u ⟩) (towerS-fst β ob) k)
      (subst (λ u → ⟨ u ∈ stage (fst z) (snd z) ⟩) (sym e)
        (birth-stage (fst z) (snd z))))

    hd : ⟨ (powS β ob ∷ towerS β ob ∷ γ) ⊨ DefAt zero (suc zero) ⟩
    hd = subst ⟨_⟩
      (sym (DefAt-stage β ob zero (suc zero)
              (powS β ob ∷ towerS β ob ∷ γ) (towerS-fst β ob)))
      (powS-fst β ob)

    hm : ⟨ fst z ∈ fst (powS β ob) ⟩
    hm = subst (λ u → ⟨ fst z ∈ u ⟩) (sym (powS-fst β ob))
      (subst (λ u → ⟨ fst z ∈ u ⟩) (Lset-suc β)
        (subst (λ u → ⟨ fst z ∈ Lset (sucV u) ⟩) (sym e)
          (birth-mem (fst z) (snd z))))
```

<!--en-->
## The codes at any arity, at a carrier that is a slot

The third obligation asked for the code set at a carrier that moves with the
birth. It is an **instantiation and not a construction**, and saying which is
worth the paragraph. The powerset chapter already wrote the code predicate at a
carrier held in a slot, `isCodeAt`{.Agda}, as two conjuncts: the argument is a key
at arity one, and it has a closed and shaped witness over the slot. The code set
chapter already wrote the arity-**bound** variant of the first conjunct,
`arityNumAtL`{.Agda}, because a recursion over subcodes has to be indexed by keys
at every arity. Nothing else differs between the two.

So the predicate wanted here is the second conjunct joined to the arity-bound
first, and its two readings are the existing two read at a slot: the arity
conjunct hands over a numeral and a code, and the witness conjunct turns that pair
into a formula over the carrier. No new machinery, no new side condition, and the
carrier is a slot throughout.
<!--zh-->
## 任意元数处的诸码，落在一个作为槽位的载体上

第三笔债索取的是「在一个随诞生阶段移动的载体上的码集」。它是**实例化、不是构造**，而把这句话说出来值这一段。幂集那一章早已把「载体握在一位上」的码谓词 `isCodeAt`{.Agda} 写成两个合取项：实参是元数一处的一个键，且它在那一位所持有的载体上有一个既封闭又成形的见证。码集那一章也早已写下第一个合取项的元数**绑定**变体 `arityNumAtL`{.Agda}，因为对诸子码的递归必须以每个元数处的诸键为索引。两者之间再无别的差异。

于是此处所要的谓词，就是第二个合取项接上元数绑定的第一个，而它的两条读式就是现成的那两条读在一位上：元数那一项交出一个数码与一条码，见证那一项把这一对变成载体之上的一条公式。没有新机器，没有新的旁条件，而载体自始至终是一位。
<!--/-->

```agda
isCodeAnyAt : ∀ {n} → Fin n → Fin n → Formula S n
isCodeAnyAt c w = arityNumAtL c ∧̇ hasWitnessAt w c

module _ (A : S) where
  codeAnyAt-in : ∀ {n k} (c w : Fin n) (γ : S ^ n)
               → fst (lookup w γ) ≡ fst A
               → (ψ : Formula ⟪ fst A ⟫ k) → fst (lookup c γ) ≡ fst (keyS A ψ)
               → ⟨ γ ⊨ isCodeAnyAt c w ⟩
  codeAnyAt-in {k = k} c w γ qw ψ qc =
    arityNumAtL-in c γ k (codeS A ψ) qc , witnessAt-in A w c γ ψ qw qc

  codeAnyAt-out : ∀ {n} (c w : Fin n) (γ : S ^ n)
                → fst (lookup w γ) ≡ fst A
                → ⟨ γ ⊨ isCodeAnyAt c w ⟩
                → ⟨ IsKeyOverAny A (lookup c γ) ⟩
  codeAnyAt-out c w γ qw (hk , hw) =
    PT.rec squash₁ step (arityNumAtL-out c γ hk)
    where
    step : Σ[ m ∈ ℕ ] Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# m) (fst z))
         → ⟨ IsKeyOverAny A (lookup c γ) ⟩
    step (m , (z , qz)) = PT.map (λ { (ψ , q) → m , (ψ , q) })
      (witnessAt-out A w c γ qw hw m z qz)
```

<!--en-->
## The set, in one extension

The set is one `extAt`{.Agda}, for the reason every set-valued clause on this
route is one: a value is the set of exactly the things meeting a condition, and
writing that as a pair of inclusions would say the condition twice. Its two
readings join the predicate's to the code set's own membership equivalence, and
what comes out is an equality of **elements**: at a carrier reached by an
equation, the slot holds the code set over that carrier and nothing else.

That is what "moves with the birth" was asking for. The naming description takes
its code set as a slot pinned by an equation supplied from outside; with this
conjunct beside it the slot is pinned by the description instead, so a caller may
bind the carrier first and let the code set follow it.
<!--zh-->
## 那个集合，一次外延

那个集合是一次 `extAt`{.Agda}，理由与这条路线上每一条取值为集合的子句相同：一个取值恰是满足某条件的那些东西之集，而若写成一对包含，那个条件就要说两遍。它的两条读式把谓词那两条接到码集自家的隶属等价上，出来的是一条**元素之间**的等式：在一个经等式抵达的载体上，那一位所持有的就是该载体之上的码集、别无他物。

这正是「随诞生阶段移动」所索取的东西。命名那条描述把它的码集取作一位，由外部供来的一条等式钉住；有了这个合取项在旁，那一位改由描述自己钉住，于是调用方可以先绑定载体，再让码集跟着它走。
<!--/-->

```agda
CodesAt : ∀ {n} → Fin n → Fin n → Formula S n
CodesAt c w = extAt c (isCodeAnyAt zero (suc w))

module _ (A : S) {n : ℕ} (c w : Fin n) (γ : S ^ n)
         (qw : fst (lookup w γ) ≡ fst A) where
  CodesAt-out : ⟨ γ ⊨ CodesAt c w ⟩ → lookup c γ ≡ AllCodes A
  CodesAt-out h = extensionalL step
    where
    step : (x : S) → (x ∈ˢ lookup c γ) ≡ (x ∈ˢ AllCodes A)
    step x = ⇔toPath
      (λ hx → AllCodes-in A x
        (codeAnyAt-out A zero (suc w) (x ∷ γ) qw
          (extAt-out c (isCodeAnyAt zero (suc w)) γ h x hx)))
      (λ hx → extAt-in c (isCodeAnyAt zero (suc w)) γ h x
        (PT.rec (snd ((x ∷ γ) ⊨ isCodeAnyAt zero (suc w)))
          (λ { (k , (ψ , q)) →
                 codeAnyAt-in A {k = k} zero (suc w) (x ∷ γ) qw ψ q })
          (AllCodes-out A x hx)))

  CodesAt-in : lookup c γ ≡ AllCodes A → ⟨ γ ⊨ CodesAt c w ⟩
  CodesAt-in q = extAt-in-both c (isCodeAnyAt zero (suc w)) γ into back
    where
    into : (x : S) → ⟨ fst x ∈ fst (lookup c γ) ⟩
         → ⟨ (x ∷ γ) ⊨ isCodeAnyAt zero (suc w) ⟩
    into x hx = PT.rec (snd ((x ∷ γ) ⊨ isCodeAnyAt zero (suc w)))
      (λ { (k , (ψ , qk)) →
             codeAnyAt-in A {k = k} zero (suc w) (x ∷ γ) qw ψ qk })
      (AllCodes-out A x (subst (λ u → ⟨ fst x ∈ fst u ⟩) q hx))

    back : (x : S) → ⟨ (x ∷ γ) ⊨ isCodeAnyAt zero (suc w) ⟩
         → ⟨ fst x ∈ fst (lookup c γ) ⟩
    back x hx = subst (λ u → ⟨ fst x ∈ fst u ⟩) (sym q)
      (AllCodes-in A x (codeAnyAt-out A zero (suc w) (x ∷ γ) qw hx))
```

<!--en-->
## The order at a stage, unfolded once

Three meta-language definitions, and one of them is the chapter's pivot.
`order-unfold`{.Agda} is the family's defining equation read at a stage: the
comparison of two members is their births compared, or, at a shared birth, the
step there. It is one `cong`{.Agda} over the recursion's computation rule, and
everything the object language has to match now stands on its right-hand side.

`bornIn`{.Agda} is the converse of `birth-in`{.Agda}: a set whose birth lies below
an ordinal lies in the tower at that ordinal. It is what lets the description drop
the condition "both compared sets belong to the stage" and keep only "both births
lie below it", which is two membership atoms at slots that are bound anyway, and
one binder cheaper.

`stepMoved`{.Agda} moves a step comparison along an equality of carriers.
Proof irrelevance extends that equality to the carriers paired with their
ordinality proofs; transport along this single equality then moves the comparison.
<!--zh-->
## 阶段处的序，展开一次

三个元语言的定义，其中之一是本章的支点。`order-unfold`{.Agda} 是那一族的定义方程读在一个阶段处：两个成员的比较，就是它们诞生阶段之间的比较，或者，在同一诞生阶段处，就是那里的那一步。它是在递归的计算规则上作的一次 `cong`{.Agda}，而对象语言要对上的一切，如今都站在它的右边。

`bornIn`{.Agda} 是 `birth-in`{.Agda} 的逆：诞生阶段落在某个序数以下的集合，落在那个序数处的塔中。正是它使这条描述得以丢掉「被比较的两个集合都属于这个阶段」那条条件，只留下「两个诞生阶段都落在它以下」，而那是落在反正要绑定的两位上的两个隶属原子，还省下一层绑定。

`stepMoved`{.Agda} 沿载体之间的一条等式搬运一次步进比较。证明无关性把这条等式扩展到「载体与其序数性证明」所成的对，再沿这一条等式运输比较。
<!--/-->

```agda
stepOrder : (δ : V ℓ) → IsOrd δ → SWO (New δ)
stepOrder δ oδ = stepAt δ (carry (Lset δ) (orderAt δ oδ))

stepMoved : (δ δ' : V ℓ) (e : δ ≡ δ') (o : IsOrd δ) (o' : IsOrd δ') (x y : V ℓ)
          → Under δ (stepOrder δ o) x y → Under δ' (stepOrder δ' o') x y
stepMoved δ δ' e o o' x y =
  subst (λ p → Under (fst p) (stepOrder (fst p) (snd p)) x y)
    (Σ≡Prop isPropIsOrd {u = δ , o} {v = δ' , o'} e)

bornIn : (α : V ℓ) → IsOrd α → (x : V ℓ) (p : ⟨ isL x ⟩)
       → ⟨ birth x p ∈ α ⟩ → ⟨ x ∈ Lset α ⟩
bornIn α oα x p h = reach (suc∈or≡ (birth x p) α (birth-ord x p) oα h)
  where
  reach : ⟨ sucV (birth x p) ∈ α ⟩ ⊎ (sucV (birth x p) ≡ α) → ⟨ x ∈ Lset α ⟩
  reach (inl k) = Lset-mono {α = α} {β = sucV (birth x p)} k
    {x = x} (birth-mem x p)
  reach (inr e) = subst (λ w → ⟨ x ∈ Lset w ⟩) e (birth-mem x p)

module _ (α : V ℓ) (oα : IsOrd α) where
  private
    module Fam = Family α (λ δ _ → orderAt δ) oα

  memberL : (a : Mem (Lset α)) → ⟨ isL (fst a) ⟩
  memberL a = Lset→isL α oα (fst a) (snd a)

  bornOf : (a : Mem (Lset α)) → V ℓ
  bornOf a = birth (fst a) (memberL a)

  bornMem : (a : Mem (Lset α)) → ⟨ bornOf a ∈ α ⟩
  bornMem a = Fam.bornAt a .snd

  order-unfold : (a b : Mem (Lset α))
               → relOf (orderAt α oα) a b
               ≡ ( ⟨ bornOf a ∈ bornOf b ⟩
                 ⊎ ( (bornOf b ≡ bornOf a)
                   × Under (bornOf a) (stepOrder (bornOf a)
                       (mem-ord {A = α} oα (bornOf a) (bornMem a)))
                       (fst a) (fst b) ) )
  order-unfold a b = cong (λ z → relOf (z oα) a b) (orderAt-step α)
```

<!--en-->
Four more elements reach slots inside a satisfaction, and they are sealed for the
same measured reason. The equations the seal exposes are exactly the three the
description consumes: the underlying set of a member, the underlying set of a
birth, and the one that says a birth **is** the birth of the member beside it, so
that the birth description is discharged by `refl`{.Agda} at each call site.
<!--zh-->
另有四个元素抵达满足关系内部的诸位，它们出于同一条实测理由被封印。封印所暴露的诸等式，恰是这条描述要消费的那三条：一个成员的底集、一个诞生阶段的底集，以及那条说「某个诞生阶段**就是**它旁边那个成员的诞生阶段」的等式，于是诞生描述在每个调用点由 `refl`{.Agda} 解除。
<!--/-->

Perf: the four elements the order description is satisfied at are sealed;
unsealed, the reading back into the object language runs past 400 s.

```agda
opaque
  memS : (α : V ℓ) (oα : IsOrd α) → Mem (Lset α) → S
  memS α oα a = fst a , memberL α oα a

  memS-fst : (α : V ℓ) (oα : IsOrd α) (a : Mem (Lset α))
           → fst (memS α oα a) ≡ fst a
  memS-fst α oα a = refl

  bornS : (α : V ℓ) (oα : IsOrd α) → ⟨ isL α ⟩ → Mem (Lset α) → S
  bornS α oα pα a = bornOf α oα a
                  , isL-trans {x = α} {y = bornOf α oα a} (bornMem α oα a) pα

  bornS-fst : (α : V ℓ) (oα : IsOrd α) (pα : ⟨ isL α ⟩) (a : Mem (Lset α))
            → fst (bornS α oα pα a) ≡ bornOf α oα a
  bornS-fst α oα pα a = refl

  bornS-birth : (α : V ℓ) (oα : IsOrd α) (pα : ⟨ isL α ⟩) (a : Mem (Lset α))
              → fst (bornS α oα pα a)
              ≡ birth (fst (memS α oα a)) (snd (memS α oα a))
  bornS-birth α oα pα a = refl
```

<!--en-->
## The order described, with the step as a parameter

Everything from here is generic in the step condition, which enters as a
parameter with its meaning stated in both directions: at a carrier reached by a
slot, with the table's value there in hand, the condition holds of two sets
exactly when the step order at that carrier relates them. That parameter is the
whole of what this chapter still owes, and it is deliberately one thing and not
three.

The two directions take the table's value at that carrier differently, and the
difference is not cosmetic. Completeness is handed **a** value, with the
hypothesis that it realizes the order there, because that is what it has to put
into the condition. Soundness is handed the hypothesis at **every** value the
table records there, because the condition it is reading may have bound a value
of its own, and only a supplier that can realize whatever it finds can say what
that value is. Either side is what the frame above hands over, `Values`{.Agda}
read at one argument.

The body binds four sets and no more. Two of them are the compared members, whose
pair is the argument, and two are their births. Then five conditions: each birth
is the birth of its member, each birth lies below the stage, and the comparison
itself, which is one membership atom between the two births, or, at a shared
birth, the step. The stage arrives as a **term** rather than a slot, and that is
not decoration: the separation the next chapter runs wants the whole condition at
constants, and a term takes a constant without a binder, where a slot would cost
one. Measured, that binder is the difference between 3 s and 160 s.
<!--zh-->
## 那个序，被描述出来，而那一步取作参数

自此往下的一切都对那条步进条件保持通用，它以参数身份进场，含义两个方向都说清：在一个经一位抵达的载体上，手里握着表在那里的取值时，该条件对两个集合成立，当且仅当那个载体处的步进序把它们关联起来。那个参数就是本章仍然欠着的全部，而它是有意做成一件事、而不是三件。

两个方向取用表在那个载体处的取值的方式不同，而这个不同不是装点。完备性被交到手上的是**某一个**取值，附带「它实现那里的序」这条假设，因为那正是它要塞进那条条件里去的东西。可靠性被交到手上的，是对表在那里所记录的**每一个**取值都成立的那条假设，因为它所读的那条条件可能自己绑定了一个取值，而只有「无论找到哪一个都能证其实现」的供给方，才说得清那个取值是什么。两边都是上面那个框架交出来的东西，即 `Values`{.Agda} 读在单个实参上。

主体只绑定四个集合，不多。其中两个是被比较的成员，它们的对就是那个实参，另外两个是它们的诞生阶段。然后是五条条件：每个诞生阶段都是它那个成员的诞生阶段，每个诞生阶段都落在该阶段以下，以及比较自身，即两个诞生阶段之间的一个隶属原子，或者，在同一诞生阶段处，就是那一步。阶段是以**词项**、而不是以槽位的身份到场的，而这不是装饰：下一章要跑的那次分离，要的是整条条件落在诸常元上，而词项无须绑定就能接住一个常元，槽位则要花掉一层。实测下来，那一层绑定就是 3 秒与 160 秒之差。
<!--/-->

```agda
StpFo : Type (ℓ-suc ℓ)
StpFo = ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n

StpOut StpIn : StpFo → Type (ℓ-suc ℓ)
StpOut Stp = ∀ {n} (d f u v : Fin n) (γ : S ^ n) (od : IsOrd (fst (lookup d γ)))
           → ((r : S) → ⟨ pr (fst (lookup d γ)) (fst r) ∈ fst (lookup f γ) ⟩
              → IsRel (fst (lookup d γ)) r)
           → ⟨ γ ⊨ Stp d f u v ⟩
           → ∥ Under (fst (lookup d γ)) (stepOrder (fst (lookup d γ)) od)
                 (fst (lookup u γ)) (fst (lookup v γ)) ∥₁
StpIn Stp = ∀ {n} (d f u v : Fin n) (γ : S ^ n) (od : IsOrd (fst (lookup d γ)))
          → (r : S) → ⟨ pr (fst (lookup d γ)) (fst r) ∈ fst (lookup f γ) ⟩
          → IsRel (fst (lookup d γ)) r
          → Under (fst (lookup d γ)) (stepOrder (fst (lookup d γ)) od)
              (fst (lookup u γ)) (fst (lookup v γ))
          → ⟨ γ ⊨ Stp d f u v ⟩

module Ordered (Stp : StpFo) (stp-out : StpOut Stp) (stp-in : StpIn Stp) where

  OrdBody : ∀ {n} → Term S n → Fin n → Formula S (suc (suc (suc (suc n))))
  OrdBody tb f =
      BirthAt (suc zero) (sh3 zero)
    ∧̇ ( BirthAt zero (sh2 zero)
      ∧̇ ( (var (suc zero) ∈̇ tm4 tb)
        ∧̇ ( (var zero ∈̇ tm4 tb)
          ∧̇ ( (var (suc zero) ∈̇ var zero)
            ∨̇ ( (var zero ≐ var (suc zero))
              ∧̇ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ) ) ) ) )
```

Perf: the order description is sealed where it is built; unsealed, its two
readings at the constants the separation wants run 160 s each instead of 2 s.

```agda
  opaque
    CondCore : ∀ {n} → Fin n → Term S n → Fin n → Formula S n
    CondCore z tb f =
      ∃̇ ( ∃̇ ( prAtL (sh2 z) (suc zero) zero ∧̇ ∃̇ (∃̇ (OrdBody tb f)) ) )
```

<!--en-->
## What the description says, both ways

The reading takes the stage's ordinality and the table's two correctness
conditions below it, which is exactly what the frame it feeds hands over. They
are spent apart. Soundness spends correctness alone, at the birth of the compared
member, and hands it to the step parameter as it stands. Completeness spends both
through `value`{.Agda}: at a birth below the stage the table has a value, merely,
and that value realizes the order there, so the parameter can be filled.
Uniqueness is never wanted, because the step condition is a proposition and a
merely-existing value may be opened into it.
<!--zh-->
## 这条描述说了什么，两个方向

这条读式取用阶段的序数性，以及表在它以下的两条正确性条件，而那恰是它所供养的那个框架交出来的东西。二者是分开花掉的。可靠性只花正确性那一条，花在被比较成员的诞生阶段处，并原样把它递给步进参数。完备性经 `value`{.Agda} 把两条一并花掉：在阶段以下的一个诞生阶段处，表「仅仅」有一个取值，而那个取值实现那里的序，于是那个参数可以被填上。单值性自始至终用不上，因为步进条件是命题，而一个「仅仅存在」的取值可以在其中被打开。
<!--/-->

```agda
  module _ {n : ℕ} (z : Fin n) (tb : Term S n) (f : Fin n) (γ : S ^ n)
           (oα : IsOrd (fst (⟦ tb ⟧ γ)))
           (vals : Values (lookup f γ) (fst (⟦ tb ⟧ γ)))
           (ents : Entries (lookup f γ) (fst (⟦ tb ⟧ γ))) where
    private
      α : V ℓ
      α = fst (⟦ tb ⟧ γ)

      shift : (u v du dv : S) → ⟦ tm4 tb ⟧ (dv ∷ du ∷ v ∷ u ∷ γ) ≡ ⟦ tb ⟧ γ
      shift u v du dv = tm4-val tb u v du dv γ

      value : (d : S) → ⟨ fst d ∈ α ⟩ → (P : Ω)
            → ((r : S) → ⟨ pr (fst d) (fst r) ∈ fst (lookup f γ) ⟩
               → IsRel (fst d) r → ⟨ P ⟩)
            → ⟨ P ⟩
      value d hd P k = PT.rec (snd P)
        (λ { (r , hr) → k r hr (vals d r hd hr) }) (ents d hd)

      Deep : (u v du : S) → S → Type (ℓ-suc ℓ)
      Deep u v du dv = ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ OrdBody tb f ⟩

```

<!--en-->
Soundness reads the four bound sets back. The pair equation identifies the
argument; the two birth readings pin the two bound ordinals to the two members'
births; `bornIn`{.Agda} turns the two memberships below the stage into membership
in the stage, which is what the class quantifies over; and the comparison is then
the family's own, along `order-unfold`{.Agda}. The description is sealed here, so
nothing in this proof normalizes the sentence it is about.
<!--zh-->
可靠性把那四个被绑定的集合读回来。对的等式认定那个实参；两条诞生读式把两个被绑定的序数钉在两个成员的诞生阶段上；`bornIn`{.Agda} 把「落在该阶段以下」的两条隶属变成「属于该阶段」，而那正是那个类所量化的东西；随后那次比较就是那一族自家的比较，沿 `order-unfold`{.Agda} 而来。这条描述在此处是封印着的，故这份证明里没有任何东西去归一化它所谈论的那个句子。
<!--/-->

```agda
    opaque
     unfolding CondCore

     CondCore-out : ⟨ γ ⊨ CondCore z tb f ⟩ → ⟨ Related α (fst (lookup z γ)) ⟩
     CondCore-out = PT.rec (snd (Related α (fst (lookup z γ))))
       (λ { (u , hv) → PT.rec (snd (Related α (fst (lookup z γ))))
         (λ { (v , (hp , hdu)) → PT.rec (snd (Related α (fst (lookup z γ))))
           (λ { (du , hdv) → PT.rec (snd (Related α (fst (lookup z γ))))
             (λ { (dv , hd) → atDeep u v du dv hp hd }) hdv }) hdu }) hv })
       where
       Goal : Type (ℓ-suc ℓ)
       Goal = ⟨ Related α (fst (lookup z γ)) ⟩

       atDeep : (u v du dv : S)
              → ⟨ (v ∷ u ∷ γ) ⊨ prAtL (sh2 z) (suc zero) zero ⟩
              → Deep u v du dv → Goal
       atDeep u v du dv hp (hbu , (hbv , (hmu₀ , (hmv₀ , hcmp)))) =
         subst (λ w → ⟨ Related α w ⟩) (sym qz)
           (PT.rec (snd (Related α (pr (fst u) (fst v)))) atCase hcmp)
         where
         qz : fst (lookup z γ) ≡ pr (fst u) (fst v)
         qz = subst ⟨_⟩ (prAtL-adequate (sh2 z) (suc zero) zero (v ∷ u ∷ γ)) hp

         hmu : ⟨ fst du ∈ α ⟩
         hmu = subst (λ w → ⟨ fst du ∈ fst w ⟩) (shift u v du dv) hmu₀

         hmv : ⟨ fst dv ∈ α ⟩
         hmv = subst (λ w → ⟨ fst dv ∈ fst w ⟩) (shift u v du dv) hmv₀

         odu : IsOrd (fst du)
         odu = mem-ord {A = α} oα (fst du) hmu

         odv : IsOrd (fst dv)
         odv = mem-ord {A = α} oα (fst dv) hmv

         qu : fst du ≡ birth (fst u) (snd u)
         qu = BirthAt-out (suc zero) (sh3 zero) ((dv ∷ du ∷ v ∷ u ∷ γ)) hbu odu

         qv : fst dv ≡ birth (fst v) (snd v)
         qv = BirthAt-out zero (sh2 zero) ((dv ∷ du ∷ v ∷ u ∷ γ)) hbv odv

         a : Mem (Lset α)
         a = fst u , bornIn α oα (fst u) (snd u)
               (subst (λ w → ⟨ w ∈ α ⟩) qu hmu)

         c : Mem (Lset α)
         c = fst v , bornIn α oα (fst v) (snd v)
               (subst (λ w → ⟨ w ∈ α ⟩) qv hmv)

         qa : bornOf α oα a ≡ fst du
         qa = birth-proof (fst u) (memberL α oα a) (snd u) ∙ sym qu

         qc : bornOf α oα c ≡ fst dv
         qc = birth-proof (fst v) (memberL α oα c) (snd v) ∙ sym qv

         fill : relOf (orderAt α oα) a c → ⟨ Related α (pr (fst u) (fst v)) ⟩
         fill = related-in α oα a c

         atCase : ⟨ fst du ∈ fst dv ⟩
                ⊎ ( (fst dv ≡ fst du)
                  × ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ⟩ )
                → ⟨ Related α (pr (fst u) (fst v)) ⟩
         atCase (inl h) = fill (transport (sym (order-unfold α oα a c))
           (inl (subst2 (λ p q → ⟨ p ∈ q ⟩) (sym qa) (sym qc) h)))
         atCase (inr (e , hs)) = PT.rec
           (snd (Related α (pr (fst u) (fst v)))) atUnder
           (stp-out (suc zero) (sh4 f) (sh3 zero) (sh2 zero)
             ((dv ∷ du ∷ v ∷ u ∷ γ)) odu (λ r hr → vals du r hmu hr) hs)
           where
           atUnder : Under (fst du) (stepOrder (fst du) odu) (fst u) (fst v)
                   → ⟨ Related α (pr (fst u) (fst v)) ⟩
           atUnder und = fill (transport (sym (order-unfold α oα a c))
             (inr (qc ∙ e ∙ sym qa
               , stepMoved (fst du) (bornOf α oα a) (sym qa) odu
                   (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a))
                   (fst u) (fst v) und)))

```

<!--en-->
Completeness fills them in. The class is unpacked to a pair of members and a
comparison, the comparison is untruncated by `strict`{.Agda}, and the four
witnesses are the two members and their two births, each sealed. The two-way split
on the comparison is a **named helper** and never a `with`{.Agda}: as a `with`{.Agda}
this one split alone runs past 300 s, because the abstraction it performs is over
a satisfaction and the satisfaction is the largest term in the chapter.
<!--zh-->
完备性把它们填回去。那个类被拆成一对成员加一次比较，比较由 `strict`{.Agda} 脱去截断，而那四个见证就是两个成员与它们的两个诞生阶段，各自封印。对那次比较的两路分情形是一个**具名辅助**，绝不是 `with`{.Agda}：写成 `with`{.Agda}，仅这一次分情形就跑过 300 秒，因为它所作的抽象是对着一个满足关系的，而那个满足关系是全章最大的词项。
<!--/-->

```agda
     private
       Pairs : IsOrd α → Type (ℓ-suc ℓ)
       Pairs o = Σ[ a ∈ Mem (Lset α) ] ∥ (Σ[ c ∈ Mem (Lset α) ]
         ( (fst (lookup z γ) ≡ pr (fst a) (fst c)) × ⟨ Ordering α o a c ⟩ )) ∥₁

     CondCore-in : ⟨ Related α (fst (lookup z γ)) ⟩ → ⟨ γ ⊨ CondCore z tb f ⟩
     CondCore-in = PT.rec (snd (γ ⊨ CondCore z tb f)) atOrd
       where
       atRel : (o : IsOrd α) (a c : Mem (Lset α))
             → fst (lookup z γ) ≡ pr (fst a) (fst c)
             → ⟨ Ordering α o a c ⟩ → ⟨ γ ⊨ CondCore z tb f ⟩
       atRel o a c q hord =
         value (bornS α oα pα a) hmu (γ ⊨ CondCore z tb f) atValue
         where
         pα : ⟨ isL α ⟩
         pα = snd (⟦ tb ⟧ γ)

         u v du dv : S
         u = memS α oα a
         v = memS α oα c
         du = bornS α oα pα a
         dv = bornS α oα pα c

         hmu : ⟨ fst du ∈ α ⟩
         hmu = subst (λ w → ⟨ w ∈ α ⟩) (sym (bornS-fst α oα pα a))
           (bornMem α oα a)

         hmv : ⟨ fst dv ∈ α ⟩
         hmv = subst (λ w → ⟨ w ∈ α ⟩) (sym (bornS-fst α oα pα c))
           (bornMem α oα c)

         odu : IsOrd (fst du)
         odu = mem-ord {A = α} oα (fst du) hmu

         odv : IsOrd (fst dv)
         odv = mem-ord {A = α} oα (fst dv) hmv

         cmp : ⟨ bornOf α oα a ∈ bornOf α oα c ⟩
             ⊎ ( (bornOf α oα c ≡ bornOf α oα a)
               × Under (bornOf α oα a) (stepOrder (bornOf α oα a)
                   (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)))
                   (fst a) (fst c) )
         cmp = transport (order-unfold α oα a c)
           (strict α oα a c (subst (λ o' → ⟨ Ordering α o' a c ⟩)
             (isPropIsOrd α o oα) hord))

         hp : ⟨ (v ∷ u ∷ γ) ⊨ prAtL (sh2 z) (suc zero) zero ⟩
         hp = subst ⟨_⟩
           (sym (prAtL-adequate (sh2 z) (suc zero) zero (v ∷ u ∷ γ)))
           (q ∙ cong₂ pr (sym (memS-fst α oα a)) (sym (memS-fst α oα c)))

         hbu : ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ BirthAt (suc zero) (sh3 zero) ⟩
         hbu = BirthAt-in (suc zero) (sh3 zero) (dv ∷ du ∷ v ∷ u ∷ γ) odu
           (bornS-birth α oα pα a)

         hbv : ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ BirthAt zero (sh2 zero) ⟩
         hbv = BirthAt-in zero (sh2 zero) (dv ∷ du ∷ v ∷ u ∷ γ) odv
           (bornS-birth α oα pα c)

         moved : Under (bornOf α oα a) (stepOrder (bornOf α oα a)
                   (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)))
                   (fst a) (fst c)
               → Under (fst du) (stepOrder (fst du) odu) (fst u) (fst v)
         moved und = subst2 (λ p r → Under (fst du) (stepOrder (fst du) odu) p r)
           (sym (memS-fst α oα a)) (sym (memS-fst α oα c))
           (stepMoved (bornOf α oα a) (fst du) (sym (bornS-fst α oα pα a))
             (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)) odu
             (fst a) (fst c) und)

         atValue : (r : S) → ⟨ pr (fst du) (fst r) ∈ fst (lookup f γ) ⟩
                 → IsRel (fst du) r → ⟨ γ ⊨ CondCore z tb f ⟩
         atValue r hr hrel = ∣ u , ∣ v , (hp , ∣ du , ∣ dv
           , (hbu , (hbv , (hmu₀ , (hmv₀ , side)))) ∣₁ ∣₁) ∣₁ ∣₁
           where
           hmu₀ : ⟨ fst du ∈ fst (⟦ tm4 tb ⟧ (dv ∷ du ∷ v ∷ u ∷ γ)) ⟩
           hmu₀ = subst (λ w → ⟨ fst du ∈ fst w ⟩) (sym (shift u v du dv)) hmu

           hmv₀ : ⟨ fst dv ∈ fst (⟦ tm4 tb ⟧ (dv ∷ du ∷ v ∷ u ∷ γ)) ⟩
           hmv₀ = subst (λ w → ⟨ fst dv ∈ fst w ⟩) (sym (shift u v du dv)) hmv
```

Perf: law of the route: a two-way split concluding in a satisfaction is a
named helper, never a `with`; as a `with` this one alone runs past 300 s.

```agda
           atCmp : ⟨ bornOf α oα a ∈ bornOf α oα c ⟩
                 ⊎ ( (bornOf α oα c ≡ bornOf α oα a)
                   × Under (bornOf α oα a) (stepOrder (bornOf α oα a)
                       (mem-ord {A = α} oα (bornOf α oα a) (bornMem α oα a)))
                       (fst a) (fst c) )
                 → ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ ( (var (suc zero) ∈̇ var zero)
                     ∨̇ ( (var zero ≐ var (suc zero))
                       ∧̇ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ) ) ⟩
           atCmp (inl h) = ∣ inl (subst2 (λ p q → ⟨ p ∈ q ⟩)
             (sym (bornS-fst α oα pα a)) (sym (bornS-fst α oα pα c)) h) ∣₁
           atCmp (inr (e , und)) = ∣ inr
             ( bornS-fst α oα pα c ∙ e ∙ sym (bornS-fst α oα pα a)
             , stp-in (suc zero) (sh4 f) (sh3 zero) (sh2 zero)
                 (dv ∷ du ∷ v ∷ u ∷ γ) odu r hr hrel (moved und) ) ∣₁

           side : ⟨ (dv ∷ du ∷ v ∷ u ∷ γ) ⊨ ( (var (suc zero) ∈̇ var zero)
                     ∨̇ ( (var zero ≐ var (suc zero))
                       ∧̇ Stp (suc zero) (sh4 f) (sh3 zero) (sh2 zero) ) ) ⟩
           side = atCmp cmp

       atPairs : (o : IsOrd α) → Pairs o → ⟨ γ ⊨ CondCore z tb f ⟩
       atPairs o (a , h) = PT.rec (snd (γ ⊨ CondCore z tb f))
         (λ { (c , (q , hord)) → atRel o a c q hord }) h

       atOrd : Σ[ o ∈ IsOrd α ] ∥ Pairs o ∥₁ → ⟨ γ ⊨ CondCore z tb f ⟩
       atOrd (o , h) = PT.rec (snd (γ ⊨ CondCore z tb f)) (atPairs o) h

     CondCore-spec : (γ ⊨ CondCore z tb f) ≡ Related α (fst (lookup z γ))
     CondCore-spec = ⇔toPath CondCore-out CondCore-in
```

<!--en-->
## The frame's two hypotheses, discharged

The previous chapter asked for the condition in two forms with one meaning: at
slots, because the graph must bind the table it consults, and at constants,
because separation carves with a formula of one free variable. Both are the same
body. At slots the stage is the term `var b`{.Agda} and nothing is bound; at
constants the stage is the term `con B`{.Agda} and only the table is bound, by one
existential, which the equation at that binder pins.

With those two filled, `Described`{.Agda} applies, and everything it proves is
available here: the approximation, the graph, the table at every ordinal, the
relation at every stage as an element of `L`, and its membership read at both
shapes a member of a stage comes in. All of it is **conditional on the step
parameter**, and on nothing else.
<!--zh-->
## 那个框架的两条假设，已解除

上一章索取的是同一含义的两种形式：落在诸位上，因为图必须绑定它所查阅的那张表；以及落在诸常元上，因为分离是用单自由变量的公式去雕的。两者是同一个主体。落在诸位上时，阶段是词项 `var b`{.Agda}，什么也不绑定；落在诸常元上时，阶段是词项 `con B`{.Agda}，只有表被绑定，用一个存在量词，由那层绑定处的等式钉住。

这两条一填上，`Described`{.Agda} 便可施用，而它所证的一切在此处都可取用：逼近、图、每个序数处的表、每个阶段处作为 `L` 之元素的那个关系，以及它的隶属读在「阶段的成员到场时的两种形状」上。这一切都**以那个步进参数为条件**，且再无其他条件。
<!--/-->

```agda
  Cond : ∀ {n} → Fin n → Fin n → Formula S (suc n)
  Cond b f = CondCore zero (var (suc b)) (suc f)

  Cond₀ : S → S → Formula S 1
  Cond₀ B F =
    ∃̇ ( (var zero ≐ con F) ∧̇ CondCore (suc zero) (con B) zero )

  cond-spec : ∀ {n} (b f : Fin n) (γ : S ^ n) → IsOrd (fst (lookup b γ))
            → Values (lookup f γ) (fst (lookup b γ))
            → Entries (lookup f γ) (fst (lookup b γ))
            → (z : S) → ((z ∷ γ) ⊨ Cond b f) ≡ Related (fst (lookup b γ)) (fst z)
  cond-spec b f γ ob vals ents z =
    CondCore-spec zero (var (suc b)) (suc f) (z ∷ γ) ob vals ents

  module _ (B F : S) (oB : IsOrd (fst B))
           (vals : Values F (fst B)) (ents : Entries F (fst B)) (z : S) where
    private
      Held : S → Type (ℓ-suc ℓ)
      Held c = (fst c ≡ fst F)
             × ⟨ (c ∷ z ∷ []) ⊨ CondCore (suc zero) (con B) zero ⟩

    cond₀-out : ⟨ (z ∷ []) ⊨ Cond₀ B F ⟩ → ⟨ Related (fst B) (fst z) ⟩
    cond₀-out = PT.rec (snd (Related (fst B) (fst z))) atHeld
      where
      atHeld : Σ[ c ∈ S ] Held c → ⟨ Related (fst B) (fst z) ⟩
      atHeld (c , (qc , hc)) =
        CondCore-out (suc zero) (con B) zero (c ∷ z ∷ []) oB
          (λ x r hx hp → vals x r hx
            (subst (λ w → ⟨ pr (fst x) (fst r) ∈ w ⟩) qc hp))
          (λ x hx → PT.map (λ { (r , hr) → r
              , subst (λ w → ⟨ pr (fst x) (fst r) ∈ w ⟩) (sym qc) hr })
            (ents x hx))
          hc

    cond₀-in : ⟨ Related (fst B) (fst z) ⟩ → ⟨ (z ∷ []) ⊨ Cond₀ B F ⟩
    cond₀-in h = ∣ F , (refl
      , CondCore-in (suc zero) (con B) zero (F ∷ z ∷ []) oB vals ents h) ∣₁

  cond₀-spec : (B F : S) → IsOrd (fst B)
             → Values F (fst B) → Entries F (fst B)
             → (z : S) → ((z ∷ []) ⊨ Cond₀ B F) ≡ Related (fst B) (fst z)
  cond₀-spec B F oB vals ents z =
    ⇔toPath (cond₀-out B F oB vals ents z) (cond₀-in B F oB vals ents z)

  open Described Cond Cond₀ cond-spec cond₀-spec public
```

<!--en-->
## Recap

`BirthAt`{.Agda} is the birth stage described in the object language, with no
successor operation and no constant named: the tower at the slot does not hold the
set, and the definable powerset of that tower does. `BirthAt-out`{.Agda} and
`BirthAt-in`{.Agda} are its two readings at variable slots, ordinality at the
ordinal slot being the only hypothesis, and the two elements it is satisfied at
are sealed, at a measured 178 s against 2 s.

`isCodeAnyAt`{.Agda} is the code predicate at **any** arity over a carrier held in
a slot, and it is an instantiation rather than a construction: the arity-bound
conjunct and the witness conjunct both already existed, one in the code set
chapter and one in the powerset chapter, and only their meeting is new.
`CodesAt`{.Agda} is the set they cut out, one `extAt`{.Agda}, and
`CodesAt-out`{.Agda} and `CodesAt-in`{.Agda} pin the slot to the code set over the
carrier in both directions, so the naming description's code-set slot can be
pinned by description instead of by an outside equation. That is the third
obligation.

`order-unfold`{.Agda} is the order family's defining equation at a stage, one
`cong`{.Agda} over the recursion's computation rule; `bornIn`{.Agda} is the
converse of `birth-in`{.Agda}, and it is what buys the description one binder less;
`stepMoved`{.Agda} carries a step comparison along an equality of carriers, rebuilt
here rather than reached for.

`CondCore`{.Agda} is the order at a stage described in full, birth-primary, generic
in the step condition. It binds four sets, takes the stage as a **term** so that
the constant form costs no binder, and it is **sealed where it is built**: unsealed,
each of its two readings at constants runs 160 s. `CondCore-out`{.Agda} and
`CondCore-in`{.Agda} are its two halves, and `Cond`{.Agda}, `Cond₀`{.Agda},
`cond-spec`{.Agda} and `cond₀-spec`{.Agda} are the two forms the previous chapter's
frame asked for, together with their meanings. With them, `Described`{.Agda}
applies.

What is not here is the step's own adequacy: `L.Choice.Internal`{.Agda}'s
`StepAt`{.Agda} against `stepAt`{.Agda}. It enters as the parameter `Stp`{.Agda}
with `stp-out`{.Agda} and `stp-in`{.Agda} as its meaning, the first taking the
table's correctness at **every** value recorded at the carrier and the second a
single value that realizes the order there, and it is a chapter of
bookkeeping against chapters that exist: the parameter sequence read back as a
vector, the denotation identified with the meta name's, the least of the
description's names identified with the least of the meta ones. The frame's two
hypotheses are gone; this one is what stands between the construction and an
unconditional theorem.
<!--zh-->
## 小结

`BirthAt`{.Agda} 是诞生阶段在对象语言中的描述，不含后继运算，也不点名任何常元：那一位处的塔不装这个集合，而那座塔的可定义幂集装它。`BirthAt-out`{.Agda} 与 `BirthAt-in`{.Agda} 是它落在变元位上的两条读式，唯一的假设是序数位处的序数性，而它所满足于其上的那两个元素被封印，实测为 178 秒对 2 秒。

`isCodeAnyAt`{.Agda} 是**任意**元数处、落在一位所持载体上的码谓词，而它是实例化、不是构造：元数绑定那个合取项与见证那个合取项都早已存在，一个在码集那一章、一个在幂集那一章，新的只是它们的会合。`CodesAt`{.Agda} 是它们雕出的那个集合，一次 `extAt`{.Agda}，而 `CodesAt-out`{.Agda} 与 `CodesAt-in`{.Agda} 在两个方向上把那一位钉在该载体之上的码集上，于是命名描述的码集那一位可以由描述钉住、而不必由外部的一条等式钉住。这就是第三笔债。

`order-unfold`{.Agda} 是序之族在一个阶段处的定义方程，即在递归的计算规则上作的一次 `cong`{.Agda}；`bornIn`{.Agda} 是 `birth-in`{.Agda} 的逆，正是它为这条描述省下一层绑定；`stepMoved`{.Agda} 沿载体之间的一条等式搬运一次步进比较，此处是重建、而不是伸手去够。

`CondCore`{.Agda} 是阶段处的序被完整描述出来，以诞生阶段为主键，对步进条件保持通用。它绑定四个集合，把阶段取作**词项**，使得常元那一形式不花绑定；而它**在被造出之处封印**：不封印，它落在诸常元上的两条读式各跑 160 秒。`CondCore-out`{.Agda} 与 `CondCore-in`{.Agda} 是它的两半，而 `Cond`{.Agda}、`Cond₀`{.Agda}、`cond-spec`{.Agda} 与 `cond₀-spec`{.Agda} 是上一章那个框架所索取的两种形式连同它们的含义。有了它们，`Described`{.Agda} 便可施用。

不在此处的，是那一步自身的充分性，即 `L.Choice.Internal`{.Agda} 的 `StepAt`{.Agda} 对着 `stepAt`{.Agda}。它以参数 `Stp`{.Agda} 的身份进场，`stp-out`{.Agda} 与 `stp-in`{.Agda} 是它的含义，前者取用表在该载体处所记录的**每一个**取值上的正确性，后者取用「实现那里的序」的单个取值；而它是对着早已存在的诸章记账的一整章：把参数序列读回成向量、把指称与元层面名字的指称认同、把这条描述诸名字中的最小者与元层面诸名字中的最小者认同。那个框架的两条假设已经没了；剩下这一条，就是横在这个构造与一条无条件定理之间的东西。
<!--/-->
