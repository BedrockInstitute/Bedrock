# Well-formed keys

<!--en-->
The half of "is a code" that closedness does not say.

`closedAt`{.Agda} is seven implications keyed by tag: *if* a member has this tag,
*then* its parts are members too. Nothing there rules out a member with no
recognized tag at all, and such a member satisfies all seven vacuously. So a
closed set may hold junk, and the predicate that says otherwise is this one:
every member is an arity-tagged pair whose tag is one of the ten, with a
payload of the shape that tag calls for.

The four leaf tags are delegated to a parameter. Their payloads mention term
codes and a numeral, never a formula code, so nothing about them descends and
nothing about them belongs in the same induction; they are written once,
elsewhere, and handed in.

Shapedness is stated at two slots, not one: the set, and a carrier the terms
inside it draw their constants from. The second slot is what makes a member the
key of a formula **over that carrier** rather than over the whole model, and it
is the conjunct the code set was caught between two statements without. Written
at a slot rather than as a constant, it is threaded through everything below and
re-indexes nothing.
<!--zh-->
「是一个码」中封闭性没有说出的那一半。

`closedAt`{.Agda} 是七条以标签为键的蕴含：**若**某个成员带这个标签，**则**它的诸部件也是成员。那里没有任何东西排除掉「压根没有可辨标签」的成员，而这样的成员平凡地满足全部七条。故一个封闭集可以含有垃圾，而说出相反之事的谓词就是这一条：每个成员都是一个带元数标签的对，其标签属于那十个之一，且载荷具有该标签所要求的形状。

四个叶子标签交给一个参数。它们的载荷提到的是词项码与一个数码、从不提公式码，故它们身上没有任何东西会下降，也没有任何东西属于同一场归纳；它们在别处写一次，然后递进来。

成形性是在两位上陈述的，不是一位：那个集合，以及其中诸词项从中取常元的一个载体。第二位使一个成员成为**该载体之上**某条公式的键、而非整个模型之上的，而它正是码集当初被两条陈述夹住时所缺的那个合取项。它写作一位、而非一个常元，于是被穿过下面的一切，且不重新索引任何东西。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Shape {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Mapping using ( mapTm; mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #mono; module VCode )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Expressions {ℓ} using ( tagAtL; tagAtL-adequate; arityTagAtL; arityTagAtL-adequate; arityTagPairAtL; arityTagPairAtL-adequate; numL )
open import L.Coding.Closure {ℓ} using ( closedAt; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt; binSameClosed-out; unSameClosed-out; unSuccClosed-out; binSuccClosed-out )
open import L.Coding.InL {ℓ} using ( closure-inv; key; codeL; codeTmL )
open import L.Coding.Closed {ℓ} using ( clo )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( ∈#-elim )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId'; toℕ<n )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The two payload frames

<!--zh-->
## 两个载荷框架
<!--/-->

<!--en-->
A tag whose payload is a pair, and a tag whose payload is a single code. Ten
tags, two shapes: which one a tag takes is the only thing that varies, and the
rest of what a tag demands of its payload is a relation the frame carries. That
is the same division the closedness predicate makes, and for the same reason.
<!--zh-->
一类标签的载荷是一个对，另一类的载荷是单个码。十个标签，两种形状：标签取哪一种是唯一变动的东西，而它对载荷的其余要求，是框架所携带的一条关系。这与封闭性谓词所作的划分相同，理由也相同。
<!--/-->

```agda
module _ {n : ℕ} where
  binForm : ℕ → Formula S (4 + n) → Formula S (suc n)
  binForm k rel = ∃̇ (∃̇ (∃̇ (arityTagPairAtL
    (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero ∧̇ rel)))

  unForm : ℕ → Formula S (3 + n) → Formula S (suc n)
  unForm k rel = ∃̇ (∃̇ (arityTagAtL (suc (suc zero)) (suc zero) k zero ∧̇ rel))
```

<!--en-->
## Term codes
<!--zh-->
## 词项码
<!--/-->

<!--en-->
The four tags whose payloads reach outside the formula codes need one predicate,
and it is not recursive: a term is a constant or a variable, and neither has a
part. Both alternatives are bounded, and by different things.

A variable's index must lie below the arity, which is what makes the formula the
code of a term *at that arity* rather than at some larger one. A constant must be
a member of the carrier, which is what makes it the code of a term *over that
alphabet* rather than over the whole model. This second conjunct is the one the
code set was caught between two statements without: with no bound on a constant,
a payload read back as one is an arbitrary element of `L`, and the class the
decode lands in is wider than the class the introduction starts from.

Both bounds are memberships at a slot, and both slots are named by the caller.
The carrier is a slot rather than a constant on purpose. A constant would pin
every predicate below this line to one carrier, and everything indexed by them
would be re-indexed at the pair; a slot is threaded, and threading is free.
<!--zh-->
那四个载荷伸到公式码之外的标签，需要一条谓词，而它不是递归的：词项要么是常元、要么是变元，二者都没有部件。两支都有界，而界住它们的不是同一样东西。

变元的序号必须落在元数之下，正是这一点使那条公式成为**在该元数上**的词项之码、而非在某个更大的元数上。常元则必须是载体的成员，正是这一点使它成为**在该字母表之上**的词项之码、而非在整个模型之上。第二个合取项，正是码集当初被两条陈述夹住时所缺的那一个：常元一旦不受界，一个被读回作常元的载荷就是 `L` 的任意元素，而解码落进的那一类，就比引入出发的那一类更宽。

两道界都是「某一位上的成员关系」，两位都由调用方点名。载体取一位、而不取一个常元，是有意为之。常元会把这条线以下的每条谓词钉死在一个载体上，而以它们为索引的一切都将在那个对上重新索引；一位是被穿过去的，而穿过去不花钱。
<!--/-->

```agda
isTmAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
isTmAt t N A = ∃̇ (tagAtL (suc t) 0 zero ∧̇ (var zero ∈̇ var (suc A)))
            ∨̇ ∃̇ (tagAtL (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N)))
```

<!--en-->
## The ten, as one predicate
<!--zh-->
## 十条，作为一条谓词
<!--/-->

<!--en-->
Every member is a well-formed key: an arity-tagged pair carrying one of the
ten tags, with the payload that tag calls for. The relations say what
closedness does not: that an atom's two parts are term codes, that a bounded
quantifier's first part is one, and that a constant's payload is zero. The
formula parts are left to closedness, which is where they belong, since they are
the only parts anything descends into.

Being shaped is therefore relative to two slots and not one: the set, and the
carrier its terms name their constants from. Only the four relations that mention
a term look at the second, and they are the only four that could.
<!--zh-->
每个成员都是一个良构的键：一个带元数标签的对，携带那十个标签之一，且载荷是该标签所要求的那种。诸关系说出封闭性没有说的事：原子的两个部件是词项码、有界量词的第一个部件是词项码、常元的载荷是零。公式部件留给封闭性，那也正是它们该在的地方，因为它们是唯一有东西会下降进去的部件。

于是「成形」相对的是两位、而非一位：那个集合，以及它的诸词项从中点名常元的那个载体。只有那四条提到词项的关系去看第二位，而它们也是仅有的四条能去看的。
<!--/-->

```agda
module _ {n : ℕ} where
  bothTm fstTm : Fin n → Formula S (4 + n)
  bothTm A = isTmAt (suc zero) (suc (suc zero)) (suc (suc (suc (suc A))))
          ∧̇ isTmAt zero (suc (suc zero)) (suc (suc (suc (suc A))))
  fstTm  A = isTmAt (suc zero) (suc (suc zero)) (suc (suc (suc (suc A))))

  noneB : Formula S (4 + n)
  noneB = ⊤̇ {n = 4 + n}

  zeroPay noneU : Formula S (3 + n)
  zeroPay = var zero ≐ con (numeralL 0)
  noneU   = ⊤̇ {n = 3 + n}

  shapes : Fin n → Formula S (suc n)
  shapes A = binForm 0 (bothTm A) ∨̇ (binForm 1 (bothTm A)
           ∨̇ (binForm 2 noneB ∨̇ (binForm 3 noneB ∨̇ (binForm 4 noneB
           ∨̇ (unForm 5 zeroPay ∨̇ (unForm 6 noneU ∨̇ (unForm 7 noneU
           ∨̇ (binForm 8 (fstTm A) ∨̇ binForm 9 (fstTm A)))))))))

  shapedAt : Fin n → Fin n → Formula S n
  shapedAt C A = ∀̇∈ (var C) (shapes A)
```

<!--en-->
## What a member is, read flat
<!--zh-->
## 一个成员是什么，摊平来读
<!--/-->

<!--en-->
Ten alternatives. The two frames are read once each, generically in the
relation they carry, so that the walk over the disjunction below is ten
applications of two readers rather than ten copies of the same unnesting.
<!--zh-->
十个可能。两个框架各读一次，且对它们所携带的关系泛型，好让下面那趟走过析取的路是两条读式的十次施用，而不是同一段解嵌套的十份拷贝。
<!--/-->

```agda
BinWit : ∀ {n} → ℕ → Formula S (4 + n) → S ^ n → S → Type (ℓ-suc ℓ)
BinWit k rel γ c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (Σ[ b ∈ S ]
  ((fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b))))
   × ⟨ (b ∷ a ∷ N ∷ c ∷ γ) ⊨ rel ⟩)))

UnWit : ∀ {n} → ℕ → Formula S (3 + n) → S ^ n → S → Type (ℓ-suc ℓ)
UnWit k rel γ c = Σ[ N ∈ S ] (Σ[ a ∈ S ]
  ((fst c ≡ pr (fst N) (pr (# k) (fst a))) × ⟨ (a ∷ N ∷ c ∷ γ) ⊨ rel ⟩))

binForm-out : ∀ {n} (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n) (c : S)
            → ⟨ (c ∷ γ) ⊨ binForm k rel ⟩ → ∥ BinWit k rel γ c ∥₁
binForm-out k rel γ c = PT.rec squash₁ (λ { (N , hN) →
  PT.rec squash₁ (λ { (a , ha) → PT.map
    (λ { (b , (hb , hr)) → N , (a , (b , (subst ⟨_⟩
       (arityTagPairAtL-adequate (suc (suc (suc zero))) (suc (suc zero)) k
          (suc zero) zero (b ∷ a ∷ N ∷ c ∷ γ)) hb , hr))) })
    ha }) hN })

unForm-out : ∀ {n} (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n) (c : S)
           → ⟨ (c ∷ γ) ⊨ unForm k rel ⟩ → ∥ UnWit k rel γ c ∥₁
unForm-out k rel γ c = PT.rec squash₁ (λ { (N , hN) → PT.map
  (λ { (a , (ha , hr)) → N , (a , (subst ⟨_⟩
     (arityTagAtL-adequate (suc (suc zero)) (suc zero) k zero
        (a ∷ N ∷ c ∷ γ)) ha , hr)) })
  hN })

ShapeWit : ∀ {n} → Fin n → S ^ n → S → Type (ℓ-suc ℓ)
ShapeWit A γ c =
    BinWit 0 (bothTm A) γ c ⊎ (BinWit 1 (bothTm A) γ c
  ⊎ (BinWit 2 noneB γ c ⊎ (BinWit 3 noneB γ c ⊎ (BinWit 4 noneB γ c
  ⊎ (UnWit 5 zeroPay γ c ⊎ (UnWit 6 noneU γ c ⊎ (UnWit 7 noneU γ c
  ⊎ (BinWit 8 (fstTm A) γ c ⊎ BinWit 9 (fstTm A) γ c))))))))

private
  sum-out : {A B C D : Type (ℓ-suc ℓ)}
          → (A → ∥ C ∥₁) → (B → ∥ D ∥₁) → ∥ A ⊎ B ∥₁ → ∥ C ⊎ D ∥₁
  sum-out f g = PT.rec squash₁
    (Sum.rec (λ x → PT.map inl (f x)) (λ y → PT.map inr (g y)))

  sum-in : {A B C D : Type (ℓ-suc ℓ)}
         → (A → C) → (B → D) → A ⊎ B → ∥ C ⊎ D ∥₁
  sum-in f g x = ∣ Sum.map f g x ∣₁

shaped-out : ∀ {n} (C A : Fin n) (γ : S ^ n) → ⟨ γ ⊨ shapedAt C A ⟩
           → (c : S) → ⟨ c ∈ˢ lookup C γ ⟩ → ∥ ShapeWit A γ c ∥₁
shaped-out C A γ h c c∈ = read (h c c∈)
  where
  read : ⟨ (c ∷ γ) ⊨ shapes A ⟩ → ∥ ShapeWit A γ c ∥₁
  read =
    sum-out (binForm-out 0 (bothTm A) γ c)
    (sum-out (binForm-out 1 (bothTm A) γ c)
    (sum-out (binForm-out 2 noneB γ c)
    (sum-out (binForm-out 3 noneB γ c)
    (sum-out (binForm-out 4 noneB γ c)
    (sum-out (unForm-out 5 zeroPay γ c)
    (sum-out (unForm-out 6 noneU γ c)
    (sum-out (unForm-out 7 noneU γ c)
    (sum-out (binForm-out 8 (fstTm A) γ c)
    (binForm-out 9 (fstTm A) γ c)))))))))

```

<!--en-->
## The same ten, written
<!--zh-->
## 同样的十条，写出来
<!--/-->

<!--en-->
A predicate written to be consumed proves nothing until something satisfies it.
The decode takes a shaped set as a hypothesis, so whoever supplies the set owes
that hypothesis, and owing it means building: an existential frame has its
witnesses to produce and a disjunct to choose, where the elimination had only to
take them apart.

The two frames are introduced once each, generically in the relation, for the
reason that decided the elimination and for one more. The adequacy equation each
frame carries is discharged here, with the tag, the relation and the environment
all still variables. Discharged at a named tag instead, it would be ten
unfoldings of a formula three quantifiers deep, and that is the difference
between a second and an afternoon.
<!--zh-->
一条为了被消费而写下的谓词，在有东西满足它之前什么也没证明。解码把「成形的集合」作为假设收下，故供给那个集合的人欠着那条假设，而欠着它意味着要造：存在式的框架有它的诸见证要产出、一个析取支要选定，而消去那边只需把它们拆开。

两个框架各引入一次，且对关系泛型，理由与决定消去的那个相同，另加一个。每个框架所携带的适足等式在此处交付，其时标签、关系与环境都还是变元。若改在一个点了名的标签处交付，那就是把一条嵌套三层量词的公式展开十遍，而那是一秒与一下午的差别。
<!--/-->

```agda
binForm-in : ∀ {n} (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n) (c : S)
           → BinWit k rel γ c → ⟨ (c ∷ γ) ⊨ binForm k rel ⟩
binForm-in k rel γ c (N , (a , (b , (e , hr)))) =
  ∣ N , ∣ a , ∣ b , (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
     (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
     (b ∷ a ∷ N ∷ c ∷ γ))) e , hr) ∣₁ ∣₁ ∣₁

unForm-in : ∀ {n} (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n) (c : S)
          → UnWit k rel γ c → ⟨ (c ∷ γ) ⊨ unForm k rel ⟩
unForm-in k rel γ c (N , (a , (e , hr))) =
  ∣ N , ∣ a , (subst ⟨_⟩ (sym (arityTagAtL-adequate
     (suc (suc zero)) (suc zero) k zero (a ∷ N ∷ c ∷ γ))) e , hr) ∣₁ ∣₁
```

<!--en-->
The walk over the disjunction mirrors its reading: each level injects one
summand and carries its own truncation. The shared maps operate on semantic
types, with each constructor's reader supplied explicitly. They never recover
a formula from its meaning. The caller supplies exactly one thing per member:
which of the ten shapes that member has.
<!--zh-->
走过那个析取的路与读它的路互为镜像：每层注入一个和项，并各自携带截断。共用映射作用于语义类型，各构造子的读式由调用方显式提供，无须从含义反推公式。调用者为每个成员提供的，恰是它属于十种形状中的哪一种。
<!--/-->

```agda
shaped-in : ∀ {n} (C A : Fin n) (γ : S ^ n)
          → ((c : S) → ⟨ c ∈ˢ lookup C γ ⟩ → ∥ ShapeWit A γ c ∥₁)
          → ⟨ γ ⊨ shapedAt C A ⟩
shaped-in C A γ g c c∈ = PT.rec (snd ((c ∷ γ) ⊨ shapes A)) fill (g c c∈)
  where
  fill : ShapeWit A γ c → ⟨ (c ∷ γ) ⊨ shapes A ⟩
  fill =
    sum-in (binForm-in 0 (bothTm A) γ c)
    (sum-in (binForm-in 1 (bothTm A) γ c)
    (sum-in (binForm-in 2 noneB γ c)
    (sum-in (binForm-in 3 noneB γ c)
    (sum-in (binForm-in 4 noneB γ c)
    (sum-in (unForm-in 5 zeroPay γ c)
    (sum-in (unForm-in 6 noneU γ c)
    (sum-in (unForm-in 7 noneU γ c)
    (sum-in (binForm-in 8 (fstTm A) γ c)
    (binForm-in 9 (fstTm A) γ c)))))))))

```

<!--en-->
## Terms, recovered
<!--zh-->
## 词项，被还原
<!--/-->

<!--en-->
The first decode, and the only one that needs no induction. A term is a constant
or a variable: the constant case reads its payload back as a constant of the
alphabet, and the variable case reads an index out of the arity numeral. Each
case spends exactly the bound its disjunct carries, and neither could be written
without one. Nothing here descends, which is why it is separable from the
recursion that follows and why it is written first.

What the term is produced *over* is a parameter, and it is what the chapter is
for. The alphabet is any type with an embedding into the hierarchy, and the
constant case needs one thing the shape predicate cannot supply: that the
carrier's members are the alphabet's image. That is a hypothesis, because it is
a fact about the pair (alphabet, carrier) and not about the code. At the one
instantiation that matters, the alphabet is the carrier's own member type and
the hypothesis is the presentation of a set by its members, so it costs a
discharge rather than a construction.

The two disjuncts are read by two named lemmas and the reader is their case
split, which is not a matter of taste. Written as two clauses of one function,
each carrying its own truncation under a disjunction that also carries one, the
chapter did not finish in ten minutes; with each disjunct's reading given a
written type of its own it checks in under two seconds. The rule is the
elaborator's, not the mathematics': a branch whose type is written is solved
against that type, and a branch whose type is inferred is solved against the
whole disjunction.
<!--zh-->
第一个解码，也是唯一一个不需要归纳的。词项要么是常元、要么是变元：常元那支把载荷读回作字母表的一个常元，变元那支从元数数码里读出一个序号。每一支恰好花掉它那个析取项所携带的那道界，而两支都不能在没有界的情况下写出来。此处没有任何东西下降，这既是它可以从随后那场递归里分离出来的原因，也是它被先写下来的原因。

词项是**在什么之上**被造出来的，这是一个参数，而这正是本章的用处所在。字母表是任何带有到层级之嵌入的类型，而常元那支需要一样形状谓词供不出的东西：载体的诸成员就是字母表的像。那是一条假设，因为它是关于「字母表与载体」这一对的事实，而不是关于码的事实。在唯一要紧的那个实例处，字母表就是载体自己的成员类型，而这条假设就是「一个集合由其诸成员的呈现」，故它的代价是一次交付、而非一次构造。

两个析取支由两条点了名的引理去读，而那条读式就是它们的分情形，这不是趣味问题。写成一个函数的两条子句时，每支各带一个截断、而它们所在的析取自己也带一个，本章十分钟内没跑完；把每支的读法各给一个写出来的类型之后，两秒不到就查完。这条规矩是归约器的、不是数学的：类型被写出来的分支对着那个类型求解，类型靠推断的分支对着整个析取求解。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) where

  TmWit : ℕ → V ℓ → Type (ℓ-suc ℓ)
  TmWit n x = Σ[ t ∈ Term K n ] (VCode.⌜ mapTm f t ⌝ᵗ ≡ x)

  Onto : ∀ {m} → Fin m → S ^ m → Type (ℓ-suc ℓ)
  Onto A γ = (y : V ℓ) → ⟨ y ∈ fst (lookup A γ) ⟩ → ∥ Σ[ c ∈ K ] (f c ≡ y) ∥₁

  tmCon : ∀ {m} (t N A : Fin m) (γ : S ^ m) (n : ℕ) → Onto A γ
        → ⟨ γ ⊨ ∃̇ (tagAtL (suc t) 0 zero ∧̇ (var zero ∈̇ var (suc A))) ⟩
        → ∥ TmWit n (fst (lookup t γ)) ∥₁
  tmCon t N A γ n onto = PT.rec squash₁
    (λ { (y , (hy , y∈)) → PT.map
         (λ { (c , qc) → con c
            , ( cong (VCode.mkTag 0) qc ∙ sym
                (subst ⟨_⟩ (tagAtL-adequate (suc t) 0 zero (y ∷ γ)) hy) ) })
         (onto (fst y) y∈) })

  tmVar : ∀ {m} (t N A : Fin m) (γ : S ^ m) (n : ℕ)
        → fst (lookup N γ) ≡ # n
        → ⟨ γ ⊨ ∃̇ (tagAtL (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N))) ⟩
        → ∥ TmWit n (fst (lookup t γ)) ∥₁
  tmVar t N A γ n qN = PT.rec squash₁
    (λ { (z , (hz , z∈)) → PT.map
         (λ { (j , (j<n , ez)) →
           var (fromℕ' n j j<n)
           , ( cong (VCode.mkTag 1) (cong #_ (toFromId' n j j<n) ∙ sym ez)
             ∙ sym (subst ⟨_⟩ (tagAtL-adequate (suc t) 1 zero (z ∷ γ)) hz) ) })
         (∈#-elim n (fst z) (subst (λ w → ⟨ fst z ∈ w ⟩) qN z∈)) })

  isTmAt-decode : ∀ {m} (t N A : Fin m) (γ : S ^ m) (n : ℕ)
                → fst (lookup N γ) ≡ # n → Onto A γ
                → ⟨ γ ⊨ isTmAt t N A ⟩ → ∥ TmWit n (fst (lookup t γ)) ∥₁
  isTmAt-decode t N A γ n qN onto = PT.rec squash₁
    (λ { (inl h) → tmCon t N A γ n onto h
       ; (inr h) → tmVar t N A γ n qN h })
```

<!--en-->
## Terms, encoded
<!--zh-->
## 词项，被编码
<!--/-->

<!--en-->
The same two clauses read backwards, and the only place in the introduction half
where anything has to be computed rather than repackaged. Each clause now owes
its own bound as well as its tag equation, and the two are owed to different
parties. A constant is its own code, so its tag equation is nothing at all, and
what it owes is that the constant is a member of the carrier: a hypothesis here,
because only the caller knows which carrier it meant. A variable has to put its
index *inside* the arity numeral, which is the other bound working in the
direction it was designed for: the decode read an index out of a numeral, and
here a numeral is shown to hold one. That second fact was already on hand, since
a smaller numeral belonging to a larger one is exactly what made distinct
numerals distinct.
<!--zh-->
同样的两支反过来读，也是引入这一半里唯一需要算点什么、而不只是重新包装的地方。如今每一支除标签等式外还欠着自己那道界，而两笔债欠给不同的人。常元就是自己的码，故它的标签等式什么也不是，它所欠的是「该常元是载体的成员」：此处这是一条假设，因为只有调用方知道它指的是哪个载体。变元则要把它的序号放**进**元数数码里，这是另一道界朝着它被设计的方向出力：解码从一个数码里读出一个序号，此处则表明一个数码含有一个序号。第二件事早已在手，因为「较小的数码属于较大的」正是使相异的数码成其为相异的那件事。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where

  isTmAt-in : ∀ {m} (t N A : Fin m) (γ : S ^ m) (n : ℕ)
            → fst (lookup N γ) ≡ # n
            → ((c : K) → ⟨ f c ∈ fst (lookup A γ) ⟩)
            → TmWit f n (fst (lookup t γ)) → ⟨ γ ⊨ isTmAt t N A ⟩
  isTmAt-in t N A γ n qN into (con c , e) = ∣ inl ∣ y
    , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc t) 0 zero (y ∷ γ))) (sym e)
      , into c ) ∣₁ ∣₁
    where
    y : S
    y = f c , h c
  isTmAt-in t N A γ n qN into (var i , e) = ∣ inr ∣ z
    , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc t) 1 zero (z ∷ γ)))
          (sym e ∙ cong (VCode.mkTag 1) (sym (numeralL-fst (toℕ i))))
      , subst (λ w → ⟨ fst z ∈ w ⟩) (sym qN)
          (subst (λ w → ⟨ w ∈ (# n) ⟩) (sym (numeralL-fst (toℕ i)))
            (#mono (toℕ i) n (toℕ<n i))) ) ∣₁ ∣₁
    where
    z : S
    z = numeralL (toℕ i)
```

<!--en-->
## One layer off
<!--zh-->
## 剥掉一层
<!--/-->

<!--en-->
The two halves meet. Shapedness says which of the ten a member is and hands
back its parts; closedness says those parts are members too, at the arity the
tag calls for. Neither half alone gives a step of a recursion, and together they
give exactly one.

The equation shapedness produces is, letter for letter, the one closedness
consumes, so the two compose with nothing in between. That is not luck: both
were written against the same reading of an arity-tagged pair.
<!--zh-->
两半会合。形状说出一个成员是十者中的哪一个，并把它的部件交回；封闭性说那些部件也是成员，且在该标签所要求的元数上。两半各自都给不出递归的一步，合起来恰好给出一步。

形状产出的那条等式，正是封闭性所消费的那一条，逐字相同，故二者之间无需任何东西即可复合。这不是运气：两者都是对着「带元数标签的对」的同一条读法写下的。
<!--/-->

```agda
module Peel {m : ℕ} (C A : Fin m) (γ : S ^ m)
            (hcl : ⟨ γ ⊨ closedAt C ⟩) (hsh : ⟨ γ ⊨ shapedAt C A ⟩) where
  private
    D : V ℓ
    D = fst (lookup C γ)

  BinSame BinSucc : ℕ → S → Type (ℓ-suc ℓ)
  BinSame k c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (Σ[ b ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b))))
     × (⟨ pr (fst N) (fst a) ∈ D ⟩ × ⟨ pr (fst N) (fst b) ∈ D ⟩))))
  BinSucc k c = Σ[ N ∈ S ] (Σ[ a ∈ S ] (Σ[ b ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b))))
     × (⟨ (a ∷ N ∷ c ∷ γ) ⊨ isTmAt zero (suc zero) (suc (suc (suc A))) ⟩
        × ⟨ pr (sucV (fst N)) (fst b) ∈ D ⟩))))

  UnSame UnSucc : ℕ → S → Type (ℓ-suc ℓ)
  UnSame k c = Σ[ N ∈ S ] (Σ[ a ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (fst a))) × ⟨ pr (fst N) (fst a) ∈ D ⟩))
  UnSucc k c = Σ[ N ∈ S ] (Σ[ a ∈ S ]
    ((fst c ≡ pr (fst N) (pr (# k) (fst a))) × ⟨ pr (sucV (fst N)) (fst a) ∈ D ⟩))

  PeelWit : S → Type (ℓ-suc ℓ)
  PeelWit c =
      BinWit 0 (bothTm A) γ c ⊎ (BinWit 1 (bothTm A) γ c
    ⊎ (BinSame 2 c ⊎ (BinSame 3 c ⊎ (BinSame 4 c
    ⊎ (UnWit 5 zeroPay γ c ⊎ (UnSucc 6 c ⊎ (UnSucc 7 c
    ⊎ (BinSucc 8 c ⊎ BinSucc 9 c))))))))

  peel : (c : S) → ⟨ c ∈ˢ lookup C γ ⟩ → ∥ PeelWit c ∥₁
  peel c c∈ = PT.map fill (shaped-out C A γ hsh c c∈)
    where
    bs : (k : ℕ) → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩ → BinWit k noneB γ c
       → BinSame k c
    bs k h (N , (a , (b , (e , _)))) =
      N , (a , (b , (e , binSameClosed-out C k γ h c N a b c∈ e)))

    us : (k : ℕ) → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩ → UnWit k noneU γ c
       → UnSame k c
    us k h (N , (a , (e , _))) =
      N , (a , (e , unSameClosed-out C k γ h c N a c∈ e))

    uz : (k : ℕ) → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩ → UnWit k noneU γ c
       → UnSucc k c
    uz k h (N , (a , (e , _))) =
      N , (a , (e , unSuccClosed-out C k γ h c N a c∈ e))

    bz : (k : ℕ) → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩ → BinWit k (fstTm A) γ c
       → BinSucc k c
    bz k h (N , (a , (b , (e , hr)))) =
      N , (a , (b , (e , (hr , binSuccClosed-out C k γ h c N a b c∈ e))))

    fill : ShapeWit A γ c → PeelWit c
    fill =
      Sum.map id
      (Sum.map id
      (Sum.map (bs 2 (hcl .fst))
      (Sum.map (bs 3 (hcl .snd .fst))
      (Sum.map (bs 4 (hcl .snd .snd .fst))
      (Sum.map id
      (Sum.map (uz 6 (hcl .snd .snd .snd .fst))
      (Sum.map (uz 7 (hcl .snd .snd .snd .snd .fst))
      (Sum.map (bz 8 (hcl .snd .snd .snd .snd .snd .fst))
      (bz 9 (hcl .snd .snd .snd .snd .snd .snd))))))))))

```

<!--en-->
## The closure is shaped
<!--zh-->
## 闭包是成形的
<!--/-->

<!--en-->
What the predicate is for. A recursion over codes is handed an index set, and
that set has to be closed or the clauses constrain nothing, and shaped or they
admit junk. Closedness was discharged for the closure a chapter ago; this is the
other half, and it is the shorter one, because shapedness asks nothing about
what a member drags in with it. Half of what the inversion returns is therefore
dropped on the floor.

The analysis is on the constructor alone. The tag is not a second index to be
matched against: it is computed from the constructor, exactly as
`byTag`{.Agda} computes the closedness demand from it, so the table is ten
lines and not ten times ten. Nothing here recurses either, because the key
of a named constructor already computes to the arity-tagged pair the witness
type asks for, and no transport is needed anywhere in the ten tuples.

The one thing a tuple cannot compute is the term witness: a payload slot holding
a term code must be certified as one, and the certificate is the encoder above
applied to the term the constructor carries. That certificate now has a second
half, and the caller pays it: every constant of the alphabet is a member of the
carrier. It is one hypothesis, discharged once per call rather than once per
constructor, because the alphabet is fixed before the formula is.

The first half, on the other hand, got cheaper. The witness a term owes is that
its code is the code of *some* term, and over the alphabet the code of a term
already is that: the encoder is the identity with `refl`{.Agda} beside it. On the
model's own coding it had to bridge two codings first.
<!--zh-->
这条谓词是干什么用的。对码的递归收到一个索引集，而那个集合必须封闭，否则诸子句什么也约束不了；也必须成形，否则它们放垃圾进来。封闭性在一章之前已为闭包交付；这里是另一半，而且是较短的那一半，因为成形性对「一个成员随身拖进什么」不作任何要求。于是那个反演返回的东西有一半被丢在地上。

分情形只对构造子进行。标签不是要与之对上的第二个索引：它由构造子算出，正如 `byTag`{.Agda} 从构造子算出封闭性的要求，故这张表是十行、而不是十乘十。此处也没有任何递归，因为一个点了名的构造子之键，已经算成了见证类型所索取的那个带元数标签的对，而那十个元组里任何地方都不需要搬运。

元组唯一算不出来的是词项见证：载荷位上放着的词项码必须被认证为词项码，而那份认证就是上面那条编码式施于该构造子所携的词项。这份认证如今有了第二半，而由调用方支付：字母表的每个常元都是载体的成员。它是一条假设，每次调用交付一次、而不是每个构造子交付一次，因为字母表是在公式之前就固定下来的。

另一方面，第一半变便宜了。一个词项所欠的见证是「它的码是**某个**词项的码」，而在字母表之上，一个词项的码本来就是这个：编码式就是恒等，旁边配一个 `refl`{.Agda}。在模型自己的编码上，它先得把两套编码搭起桥来。
<!--/-->

```agda
module _ {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where
  private
    cd : ∀ {n} → Formula K n → S
    cd φ = VCode.⌜ mapFo f φ ⌝ , codeL f h φ

    ct : ∀ {n} → Term K n → S
    ct t = VCode.⌜ mapTm f t ⌝ᵗ , codeTmL f h t

    nn : ℕ → S
    nn n = # n , numL n

    tw : ∀ {n} (t : Term K n) → TmWit f n (fst (ct t))
    tw t = t , refl

  closureShaped : ∀ {n m} (φ : Formula K n) (A : Fin m) (γ : S ^ m)
                → ((k : K) → ⟨ f k ∈ fst (lookup A γ) ⟩)
                → ⟨ (clo f h φ ∷ γ) ⊨ shapedAt zero (suc A) ⟩
  closureShaped φ A γ into = shaped-in zero (suc A) (clo f h φ ∷ γ)
    (λ c c∈ → PT.map (λ { (_ , ψ , q , _) → go ψ c q })
      (closure-inv f h φ (fst c) c∈))
    where
    tm1 : ∀ {k} (t : Term K k) (b c : S)
        → ⟨ (b ∷ ct t ∷ nn k ∷ c ∷ clo f h φ ∷ γ)
            ⊨ isTmAt (suc zero) (suc (suc zero))
                (suc (suc (suc (suc (suc A))))) ⟩
    tm1 {k} t b c = isTmAt-in f h (suc zero) (suc (suc zero))
      (suc (suc (suc (suc (suc A)))))
      (b ∷ ct t ∷ nn k ∷ c ∷ clo f h φ ∷ γ) k refl into (tw t)

    tm0 : ∀ {k} (u : Term K k) (a c : S)
        → ⟨ (ct u ∷ a ∷ nn k ∷ c ∷ clo f h φ ∷ γ)
            ⊨ isTmAt zero (suc (suc zero))
                (suc (suc (suc (suc (suc A))))) ⟩
    tm0 {k} u a c = isTmAt-in f h zero (suc (suc zero))
      (suc (suc (suc (suc (suc A)))))
      (ct u ∷ a ∷ nn k ∷ c ∷ clo f h φ ∷ γ) k refl into (tw u)

    go : ∀ {k} (ψ : Formula K k) (c : S) → fst c ≡ key f h ψ
       → ShapeWit (suc A) (clo f h φ ∷ γ) c
    go {k} (t ∈̇ u) c q =
      inl (nn k , (ct t , (ct u , (q , (tm1 t (ct u) c , tm0 u (ct t) c)))))
    go {k} (t ≐ u) c q =
      inr (inl
        (nn k , (ct t , (ct u , (q , (tm1 t (ct u) c , tm0 u (ct t) c))))))
    go {k} (a ∧̇ b) c q = inr (inr (inl (nn k , (cd a , (cd b , (q , (λ z → z)))))))
    go {k} (a ∨̇ b) c q =
      inr (inr (inr (inl (nn k , (cd a , (cd b , (q , (λ z → z))))))))
    go {k} (a ⇒̇ b) c q =
      inr (inr (inr (inr (inl (nn k , (cd a , (cd b , (q , (λ z → z)))))))))
    go {k} ⊥̇ c q =
      inr (inr (inr (inr (inr (inl (nn k , (nn 0 , (q , sym (numeralL-fst 0)))))))))
    go {k} (∃̇ a) c q =
      inr (inr (inr (inr (inr (inr (inl (nn k , (cd a , (q , (λ z → z))))))))))
    go {k} (∀̇ a) c q =
      inr (inr (inr (inr (inr (inr (inr (inl (nn k , (cd a , (q , (λ z → z)))))))))))
    go {k} (∀̇∈ t a) c q =
      inr (inr (inr (inr (inr (inr (inr (inr (inl
        (nn k , (ct t , (cd a , (q , tm1 t (cd a) c))))))))))))
    go {k} (∃̇∈ t a) c q =
      inr (inr (inr (inr (inr (inr (inr (inr (inr
        (nn k , (ct t , (cd a , (q , tm1 t (cd a) c))))))))))))
```
