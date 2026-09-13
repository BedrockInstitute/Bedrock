<!--en-->
# Recognizing well-formed constructor keys

A code is well formed when it has one of the term or formula constructor shapes and its payloads occupy the expected frames. This chapter defines the ten-way shape predicate, proves its flat witness characterization in both directions, and recovers or constructs term codes and immediate subcodes.
<!--zh-->
# 良构构造子键的识别

一个码若具有某种词项或公式构造子的形状，且其载荷位于预期框架中，就是良构的。本章定义十路形状谓词，双向证明其平铺见证的刻画，并恢复或构造词项码与直接子码。
<!--ja-->
# 整形式な構成子キーの認識

符号が整形式であるとは、項または論理式のいずれかの構成子の形を持ち、そのペイロードが所定の枠に収まることです。十通りの形の述語を定義し、その平坦な証人による特徴付けを双方向で示し、項の符号と直下の部分符号を復元または構成します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Coding.CodeShape {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.ConstantMapping using ( mapTm; mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #mono; module VCode )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Expressions {ℓ} using ( tagAtL; tagAtL-adequate; arityTagAtL; arityTagAtL-adequate; arityTagPairAtL; arityTagPairAtL-adequate; numL )
open import L.Coding.Closure {ℓ} using ( closedAt; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt; binSameClosed-out; unSameClosed-out; unSuccClosed-out; binSuccClosed-out )
open import L.Coding.CodeConstructibility {ℓ} using ( closure-inv; key; codeL; codeTmL )
open import L.Coding.SubformulaClosure {ℓ} using ( clo )
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

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The two payload frames

A tag whose payload is a pair, and a tag whose payload is a single code. Ten
tags, two shapes: which one a tag takes is the only thing that varies, and the
rest of what a tag demands of its payload is a relation the frame carries. That
is the same division the closedness predicate makes, and for the same reason.
<!--zh-->
## 两个载荷框架

一类标签的载荷是一个对，另一类的载荷是单个码。十个标签，两种形状：其中变动的只有标签取哪一种，而载荷须满足的其余条件，是框架所携带的一条关系。这一划分与封闭性谓词所作的划分相同，理由也相同。
<!--ja-->
## 二つのペイロード枠

単項構成子と二項構成子では、キーに格納する部分符号の数が異なります。二つの枠はタグ、アリティ、項または論理式の部分符号を所定の位置に配置します。
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

The four tags whose payloads reach outside the formula codes need one predicate,
and it is not recursive: a term is a constant or a variable, and neither has a
part. Both alternatives are bounded, and by different things.
<!--zh-->
## 词项码

那四个载荷超出公式码范围的标签，需要一条谓词，而这条谓词不是递归的：词项要么是常元，要么是变元，二者都没有部件。两支各有一道界，但两道界的性质不同。
<!--ja-->
## 項の符号

定数項と変数項のキーを、それぞれタグとペイロードの形で認識します。`isTmAt`{.Agda} は二つの場合を一つの対象言語の述語にまとめます。
<!--/-->

<!--en-->
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
变元的序号必须落在元数之下，正是这一点使那条公式成为**在该元数上**的词项之码，而非在某个更大的元数上。常元则必须是载体的成员，正是这一点使它成为**在该字母表之上**的词项之码，而非在整个模型之上。第二个合取项，正是当初以两条陈述界住码集时所缺的那一条：常元一旦不受界，一个被读回作常元的载荷就可能是 `L` 的任意元素，而解码所落进的那一类，便比引入时所出发的那一类更宽。

两道界都是「在某一位上的成员关系」，而这两位都由调用方指定。载体取一位而不取一个常元，是有意为之：常元会把这条线以下的每条谓词固定到一个载体上，而以它们为索引的一切也都要在那个对上重新索引；一位则只是被传递下去，传递本身不增加代价。
<!--/-->

```agda
isTmAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
isTmAt t N A = ∃̇ (tagAtL (suc t) 0 zero ∧̇ (var zero ∈̇ var (suc A)))
            ∨̇ ∃̇ (tagAtL (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N)))
```

<!--en-->
## The ten, as one predicate

Every member is a well-formed key: an arity-tagged pair carrying one of the
ten tags, with the payload that tag calls for. The relations say what
closedness does not: that an atom's two parts are term codes, that a bounded
quantifier's first part is one, and that a constant's payload is zero. The
formula parts are left to closedness, which is where they belong, since they are
the only parts anything descends into.
<!--zh-->
## 十路合为一个谓词

每个成员都是一个良构的键：一个带元数标签的对，携带那十个标签之一，且载荷是该标签所要求的那种。诸关系说出封闭性没有说的事：原子的两个部件是词项码，有界量词的第一个部件是词项码，常元的载荷是零。公式部件留给封闭性，那也正是它们该在的地方，因为它们是唯一有东西会下降进去的部件。
<!--ja-->
## 十個の形を一つの述語にする

原子、二項結合子、偽、量化子、有界量化子の十個の論理式構成子を一つの選言的な形の述語にまとめます。各枝は対応するタグとペイロード枠を検査します。
<!--/-->

<!--en-->
Being shaped is therefore relative to two slots and not one: the set, and the
carrier its terms name their constants from. Only the four relations that mention
a term look at the second, and they are the only four that could.
<!--zh-->
于是「成形」相对的是两位，而非一位：那个集合，以及它的诸词项从中点名常元的那个载体。只有那四条提到词项的关系去看第二位，而它们也是仅有的四条能去看的。
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

Ten alternatives. The two frames are read once each, generically in the
relation they carry, so that the reading along the disjunction below is ten
applications of two readers rather than ten copies of the same unnesting.
<!--zh-->
## 成员的平铺读取

共十种可能。两个框架各提供一条读式，且对它们所携带的关系是泛型的，这样，下文沿析取进行的读取便是两条读式的十次施用，而不是同一段解嵌套的十份拷贝。
<!--ja-->
## 要素を平坦に読み出す

形の述語を満たすキーから、どの構成子であるか、そのタグ、アリティ、直下の部分符号を平坦な証人として取り出します。この除去形式は後の閉性証明で使いやすい形です。
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

A predicate written to be consumed proves nothing until something satisfies it.
The decode takes a shaped set as a hypothesis, so whoever supplies the set owes
that hypothesis, and owing it means building: an existential frame has its
witnesses to produce and a disjunct to choose, where the elimination had only to
take them apart.
<!--zh-->
## 同样十路的写入

谓词只有在证明某个对象满足它之后才产生结论。解码以「集合成形」为假设，因此构造供解码使用的集合时，必须同时证明这一假设。对存在式框架，引入方向需要给出各个见证并选定一个析取分支；消去方向则从已有证明中取出这些数据。
<!--ja-->
## 同じ十個の形を書き込む

各構成子に必要なタグとペイロードの等式が与えられれば、対応する形の述語を満たすことを示せます。これは平坦な証人から対象言語の充足関係への逆向きです。
<!--/-->

<!--en-->
The two frames are introduced once each, generically in the relation, for the
reason that decided the elimination and for one more. The adequacy equation each
frame carries is discharged here, with the tag, the relation and the environment
all still variables. Discharged at a named tag instead, it would be ten
unfoldings of a formula three quantifiers deep, and that is the difference
between a second and an afternoon.
<!--zh-->
两个框架各引入一次，且对关系泛型，理由与决定消去的那个相同，此外还有一个。每个框架所携带的充分性等式在此处给出，其时标签、关系与环境都还是变元。若改在标签已被具体指名的位置才给出，就等于把一条嵌套三层量词的公式展开十遍，那是一秒与一下午的差别。
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

The first decode, and the only one that needs no induction. A term is a constant
or a variable: the constant case reads its payload back as a constant of the
alphabet, and the variable case reads an index out of the arity numeral. Each
case uses exactly the bound its disjunct carries, and neither could be written
without one. No case here descends into a subcode, which is why this decode is
separable from the recursion that follows and why it is written first.
<!--zh-->
## 词项的恢复

这是第一个解码，也是唯一不需要归纳的解码。词项分为常元与变元：常元分支把载荷解释为字母表中的常元，变元分支从元数数码中恢复序号。两个分支分别使用对应析取项携带的边界证明；没有这些边界，两个分支都无法构造。这里不递归进入任何子码，因此可以与后续递归分开并先行定义。
<!--ja-->
## 項の復元

項の形を持つキーから、対応する実際の項と、その符号が元のキーに等しいという証明を復元します。定数と変数の二つの場合をタグの単射性で区別します。
<!--/-->

<!--en-->
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
词项相对于哪个字母表构造，是本章的一个参数。字母表可以是任何带有到层级嵌入的类型；常元分支还需要一项形状谓词无法提供的假设：载体成员恰好是字母表嵌入的像。这是关于字母表与载体的假设，而不是关于码的性质。在后文所需的实例中，字母表取载体自身的成员类型，这项假设正是「一个集合由其成员呈现」。因此，该事实由调用方提供，无需在词项解码中重新构造。

两个析取支由两条点了名的引理去读，那条读式就是它们的分情形，这里并无选择余地。写成一个函数的两条子句时，每支各带一个截断，而它们所在的析取自己也带一个，本章十分钟内没跑完；把每支的读法各给一个写出来的类型之后，两秒不到就查完。这条规矩是归约器的，不是数学的：类型被写出来的分支对着那个类型求解，类型靠推断的分支对着整个析取求解。
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

The same two clauses read backwards, and the only place in the introduction half
where anything has to be computed rather than repackaged. Each clause now needs
its own bound as well as its tag equation, and the two bounds are different.
A constant is its own code, so its tag equation is nothing at all, and
what it needs is that the constant is a member of the carrier: a hypothesis here,
because only the caller knows which carrier it meant. A variable has to put its
index *inside* the arity numeral, which is the other bound working in the
direction it was designed for: the decode read an index out of a numeral, and
here a numeral is shown to hold one. That second fact was already available, since
a smaller numeral belonging to a larger one is exactly what made distinct
numerals distinct.
<!--zh-->
## 词项的符号化

同样的两支反过来读，也是引入这一半里唯一需要真正计算、而不只是重新包装的地方。如今每一支除标签等式外还各需要一道界，而两支所需的界并不相同。常元就是自己的码，故它的标签等式没有内容，它真正需要的是「该常元是载体的成员」：在这里这是一条假设，因为只有调用方知道它指的是哪个载体。变元则要把它的序号放**进**元数数码里，这正是另一道界按其设计发挥功用之处：解码从一个数码里读出一个序号，而此处则表明一个数码里含有一个序号。至于第二件事，早已成立，因为「较小的数码属于较大的」正是使相异的数码彼此相异的那一点。
<!--ja-->
## 項の符号化

逆に、任意の項の符号は項の形の述語を満たします。項の二つの構成子を調べ、対応するタグとペイロードの証人を直接与えます。
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

The two halves meet. Shapedness says which of the ten a member is and hands
back its parts; closedness says those parts are members too, at the arity the
tag calls for. Neither half alone gives a step of a recursion, and together they
give exactly one.
<!--zh-->
## 剥去一层

这里结合形状与封闭性。形状判定一个成员属于十种构造中的哪一种，并给出它的各个部件；封闭性证明这些部件也是成员，且位于该标签要求的元数处。任一性质单独都不足以建立递归步骤，二者合用则恰好满足该步骤的条件。
<!--ja-->
## 一層分の部分符号

論理式の符号から、その最外構成子が指す直下の項と論理式の符号を取り出します。これは構文木を一層だけ進む操作で、閉性述語が要求する部分符号を与えます。
<!--/-->

<!--en-->
The equation shapedness produces is, letter for letter, the one closedness
consumes, so the two compose with nothing in between. That is not luck: both
were written against the same reading of an arity-tagged pair.
<!--zh-->
形状所给出的那条等式，正是封闭性所需要的那一条，二者逐字相同，故中间无需任何东西即可衔接。这不是巧合：两者都是对「带元数标签的对」按同一条读法写下的。
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

What the predicate is for. A recursion over codes is handed an index set, and
that set has to be closed or the clauses constrain nothing, and shaped or they
admit junk. Closedness was discharged for the closure a chapter ago; this is the
other half, and it is the shorter one, because shapedness asks nothing about
what a member drags in with it. Half of what the inversion returns is therefore
dropped on the floor.
<!--zh-->
## 闭包具有形状

这条谓词有什么用。对码的递归得到一个索引集，而那个集合必须封闭，否则诸子句什么也约束不了；也必须成形，否则它们会把垃圾放进来。封闭性已在一章之前为闭包给出；这里是另一半，而且较短，因为成形性对「一个成员含有哪些子成员」不作任何要求。于是那个反演所返回的东西有一半被弃置不用。
<!--ja-->
## 閉じた領域の符号は整形式である

閉じた符号領域の各要素には、十個の構成子のいずれかに対応する形の証人があります。この定理が領域の所属から実際の論理式の復号へ進む入口になります。
<!--/-->

<!--en-->
The analysis is on the constructor alone. The tag is not a second index to be
matched against: it is computed from the constructor, exactly as
`byTag`{.Agda} computes the closedness demand from it, so the table is ten
lines and not ten times ten. Nothing here recurses either, because the key
of a named constructor already computes to the arity-tagged pair the witness
type asks for, and no transport is needed anywhere in the ten tuples.

The one thing a tuple cannot compute is the term witness: a payload slot holding
a term code must be certified as one, and the certificate is the encoder above
applied to the term the constructor carries. That certificate now has a second
half, supplied by the caller: every constant of the alphabet is a member of the
carrier. It is one hypothesis, discharged once per call rather than once per
constructor, because the alphabet is fixed before the formula is.

The first half, on the other hand, becomes easier. The witness a term owes is that
its code is the code of *some* term, and over the alphabet the code of a term
already is that: the encoder is the identity with `refl`{.Agda} beside it. On the
model's own coding it must first establish a correspondence between the two codings.
<!--zh-->
这里只需按构造子分情形。标签不是另一个需要匹配的索引；它由构造子计算，正如 `byTag`{.Agda} 从构造子计算封闭性要求。因此，这张表只有十行，而非十乘十。这里也没有递归：指定构造子后，其键已经计算为见证类型要求的带元数标签的对，十个元组中都不需要任何搬运。

元组唯一算不出来的是词项见证：载荷位上放着的词项码必须被认证为词项码，而那份认证正是上面的编码式施于该构造子所携的词项。这份认证如今有了第二半，由调用方提供：字母表的每个常元都是载体的成员。它是一条假设，每次调用提供一次，而不是每个构造子提供一次，因为字母表早在公式之前就已固定。

另一方面，第一半变得更容易了。一个词项所需的见证是「它的码是**某个**词项的码」，而在字母表之上，一个词项的码本来就是这个：编码式就是恒等，旁边配一个 `refl`{.Agda}。若在模型自己的编码上，则它还得先在两套编码之间建立对应。
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
