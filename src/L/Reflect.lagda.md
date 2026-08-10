# Reflecting an existential into a stage

<!--en-->
The separation chapter carved subsets of a stage using formulas whose quantifiers
were already bounded, and that sufficed because a bounded formula asks only about
what a stage already contains. An unbounded existential does not: it asks whether
*somewhere in L* there is a witness, and L is a proper class. To carve with such
a formula, the class-sized question has to be answered inside a set.

It can be, and the argument is Montague's. Fix a matrix and an environment of
parameters. If a witness exists at all, there is a least stage containing one,
and that stage is a set-sized answer to a class-sized question. Run over all
tuples of parameters drawn from one stage, bound the answers, and the result is a
single stage that answers for every tuple from the stage below. Iterate that step
through the natural numbers and take the union: the limit answers for its own
parameters, because any finite tuple from the limit already lies in some finite
layer, whose answers were bounded at the next.

Two things are done differently here than they usually are. The choice of witness
is where a well-ordering of L is normally invoked, and it is not needed: what the
argument wants is a canonical *ordinal*, not a canonical element, and the
ordinals are already well-ordered by membership. So the least stage that holds a
witness is taken directly, by the descent of the stage chapter, and which witness
lives there is never decided. And the parameters are a tuple from the start.
Writing the one-parameter case first and generalizing later would mean writing
the whole construction twice, since every step of it is indifferent to how many
parameters there are; the only place the tuple is felt at all is in locating it,
where finitely many layers have to be merged into one.
<!--zh-->
分离那一章用量词已然有界的公式雕出阶段的子集，而那是够用的，因为有界公式只问阶段已经装下的东西。无界的存在量词不然：它问的是**在 L 的某处**是否有见证，而 L 是真类。要用这样的公式来雕，就得在一个集合之内回答一个真类大小的问题。

回答得了，而论证出自 Montague。固定一个矩阵与一个参数环境。若见证根本存在，则有一个包含见证的最小阶段，而那个阶段是对真类大小之问题的集合大小的回答。取遍某一阶段中的全部参数元组，把诸回答界住，所得便是单一阶段，它为下方那个阶段的每个元组作答。沿自然数迭代这一步并取并：极限为它自己的参数作答，因为极限中的任何有穷元组早已落在某个有穷层里，而那一层的回答在下一层被界住。

此处有两件事与通常做法不同。见证的选取正是通常召唤 L 的良序之处，而它并不需要：论证想要的是典范的**序数**，而非典范的元素，而序数早已被成员关系良序化。故装有见证的最小阶段被直接取用，经阶段那一章的下降，而住在那里的究竟是哪个见证，从未被决定。以及，参数自始就是元组。先写单参数情形、日后再推广，等于把整个构造写两遍，因为它的每一步都对参数有几个漠不关心；元组唯一被感受到的地方是为它定位，那里有穷多个层要合并成一个。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Reflect {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-in; Lset-out
        ; Lset→isL )
open import L.Ordinal {ℓ} using ( ∅-ord; boundingOrd; bound2; setUnion-ord )
open import L.Stage {ℓ} lem using ( LeastOrd; leastOrd )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( _+_; +-comm )
open import Cubical.Data.Unit using ( Unit*; tt* )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⋃_; union-ax )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Environments drawn from a stage
<!--zh-->
## 取自一个阶段的环境
<!--/-->

<!--en-->
An element of a stage becomes an element of the class model by the tower's
membership criterion, so a stage's index set is a supply of parameters, and a
tuple of indices is a supply of environments. That is what makes the bounding
lemma applicable below: the tuples form a type of the ambient size, being a
vector over one.

An environment *lies below* a stage when each of its entries does. Reading the
tuple of indices back off such an environment is the inverse operation, and it
returns the equation as well, since the construction will need to know that the
environment it bounded is the one it was given. The equation is where
constructibility being a proposition is used: two elements of the model agree as
soon as their underlying sets do.
<!--zh-->
阶段的一个元素经塔的隶属判据成为类模型的一个元素，故阶段的索引集是参数的供给，而索引元组是环境的供给。正是这一点使下面的界层引理得以适用：诸元组构成周遭大小的类型，因为它是其上的向量。

一个环境**落在**某阶段之下，指它的每一项都落在其下。从这样的环境把索引元组读回来是逆向的操作，而它连等式一并交还，因为构造需要知道：它界住的那个环境，正是交给它的那一个。等式正是用到「可构造性是命题」之处：模型的两个元素，只要底集相同就相等。
<!--/-->

```agda
LsetElt : (σ : V ℓ) → IsOrd σ → ⟪ Lset σ ⟫ → S
LsetElt σ oσ m = ⟪ Lset σ ⟫↪ m
               , Lset→isL σ oσ (⟪ Lset σ ⟫↪ m)
                   (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))

LsetEnv : (σ : V ℓ) (oσ : IsOrd σ) {k : ℕ} → ⟪ Lset σ ⟫ ^ k → S ^ k
LsetEnv σ oσ []       = []
LsetEnv σ oσ (m ∷ ms) = LsetElt σ oσ m ∷ LsetEnv σ oσ ms

Below : (σ : V ℓ) {k : ℕ} → S ^ k → Type (ℓ-suc ℓ)
Below σ []      = Unit*
Below σ (p ∷ ρ) = ⟨ fst p ∈ Lset σ ⟩ × Below σ ρ

Below-mono : {σ τ : V ℓ} → ⟨ σ ∈ τ ⟩ → {k : ℕ} {ρ : S ^ k}
           → Below σ ρ → Below τ ρ
Below-mono σ∈τ {ρ = []}    _         = tt*
Below-mono σ∈τ {ρ = p ∷ ρ} (h , hs) =
  Lset-mono σ∈τ h , Below-mono σ∈τ hs

indexEnv : (σ : V ℓ) (oσ : IsOrd σ) {k : ℕ} (ρ : S ^ k) → Below σ ρ
         → Σ[ ms ∈ ⟪ Lset σ ⟫ ^ k ] (LsetEnv σ oσ ms ≡ ρ)
indexEnv σ oσ []      _        = [] , refl
indexEnv σ oσ (p ∷ ρ) (h , hs) = (m ∷ fst rest) , cong₂ _∷_ eltEq (snd rest)
  where
  fib = ∈-asFiber {a = fst p} {b = Lset σ} h
  m   = fib .fst
  eltEq : LsetElt σ oσ m ≡ p
  eltEq = Σ≡Prop (λ x → (isL x) .snd) (fib .snd)
  rest = indexEnv σ oσ ρ hs
```

<!--en-->
## The answering stage
<!--zh-->
## 作答的阶段
<!--/-->

<!--en-->
Fix a matrix in one witness variable and `k` parameters. "Some witness for this
environment lives in this stage" is a property of ordinals, so the stage
chapter's descent applies to it directly. Its premise is that some ordinal has
the property, which follows from satisfiability alone: a witness is an element of
L, and an element of L lies in some stage by definition.

Totality then wants a value even when no witness exists, and the excluded middle
supplies the case distinction. As in the stage chapter, the distinction is made
by an explicit auxiliary rather than by a `with`, because the load-bearing lemma
below has to name the very same decision value and match on it.
<!--zh-->
固定一个矩阵，含一个见证变元与 `k` 个参数。「这个环境的某个见证住在这个阶段里」是序数的一条性质，故阶段那一章的下降直接适用于它。它的前提是某个序数具有该性质，而这仅凭可满足性即得：见证是 L 的元素，而 L 的元素按定义落在某个阶段里。

其次，全函数性要求即便见证不存在也得有个值，而排中律给出分情形。一如阶段那一章，分情形由显式的辅助函数而非 `with` 作出，因为下面那条承重引理必须点名同一个判定值并在其上匹配。
<!--/-->

```agda
Sat : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k) → S → Ω
Sat ψ ρ q = (q ∷ ρ) ⊨ ψ

SatEx : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k) → Ω
SatEx ψ ρ = ∃[ q ∶ S ] Sat ψ ρ q

Wit : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k) → V ℓ → Ω
Wit ψ ρ σ = ∃[ q ∶ S ] ((fst q ∈ Lset σ) ⊓ Sat ψ ρ q)

witnessed : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k) → ⟨ SatEx ψ ρ ⟩
          → ∥ (Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ Wit ψ ρ α ⟩)) ∥₁
witnessed ψ ρ = PT.rec squash₁
  (λ { (q , satq) → PT.map
      (λ { (α , (oα , q∈Lα)) → α , (oα , ∣ q , (q∈Lα , satq) ∣₁) })
      (q .snd) })

pick : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k) → ⟨ SatEx ψ ρ ⟩
     → LeastOrd (Wit ψ ρ)
pick ψ ρ sat = leastOrd (Wit ψ ρ) (witnessed ψ ρ sat)

decideStage : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
            → ⟨ SatEx ψ ρ ⟩ ⊎ (⟨ SatEx ψ ρ ⟩ → Empty.⊥) → V ℓ
decideStage ψ ρ (inl sat) = pick ψ ρ sat .fst
decideStage ψ ρ (inr _)   = ∅

pickStage : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k) → V ℓ
pickStage ψ ρ = decideStage ψ ρ (lem (SatEx ψ ρ))

decideStage-ord : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
                  (d : ⟨ SatEx ψ ρ ⟩ ⊎ (⟨ SatEx ψ ρ ⟩ → Empty.⊥))
                → IsOrd (decideStage ψ ρ d)
decideStage-ord ψ ρ (inl sat) = pick ψ ρ sat .snd .fst
decideStage-ord ψ ρ (inr _)   = ∅-ord

pickStage-ord : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k)
              → IsOrd (pickStage ψ ρ)
pickStage-ord ψ ρ = decideStage-ord ψ ρ (lem (SatEx ψ ρ))
```

<!--en-->
And the property the whole construction rests on: if the environment is
satisfiable at all, its answering stage really does hold a witness. The proof has
to know which branch the decision took, and it cannot ask, because the decision
is a value of the excluded middle and nothing computes it. So it does the
standard thing: quantify over the branch, remember the equation that the branch
*is* the decision, and transport along it. In the false branch the hypothesis
refutes itself.
<!--zh-->
以及整个构造所倚赖的那条性质：若环境根本可满足，则它的作答阶段确实装着一个见证。证明必须知道判定走的是哪一支，而它问不出来，因为判定是排中律的一个值，没有东西算得出它。于是它做那件标准的事：对分支作量化，记住「该分支**就是**那个判定」这条等式，并沿之搬运。在假分支上，假设自我反驳。
<!--/-->

```agda
pickWitness : {k : ℕ} (ψ : Formula S (suc k)) (ρ : S ^ k) → ⟨ SatEx ψ ρ ⟩
            → ⟨ Wit ψ ρ (pickStage ψ ρ) ⟩
pickWitness ψ ρ sat = go (lem (SatEx ψ ρ)) refl
  where
  go : (d : ⟨ SatEx ψ ρ ⟩ ⊎ (⟨ SatEx ψ ρ ⟩ → Empty.⊥))
     → lem (SatEx ψ ρ) ≡ d → ⟨ Wit ψ ρ (pickStage ψ ρ) ⟩
  go (inl s) e = subst (λ d → ⟨ Wit ψ ρ (decideStage ψ ρ d) ⟩) (sym e)
                   (pick ψ ρ s .snd .snd .fst)
  go (inr ¬s) e = Empty.rec (¬s sat)
```

<!--en-->
## Ladders and their limits
<!--zh-->
## 梯与其极限
<!--/-->

<!--en-->
What the argument actually needs is not one particular tower but a **ladder**: an
ascending chain of ordinals indexed by the naturals. Its limit is the union, an
ordinal because the union of a family of ordinals is; each rung belongs to the
limit, since it belongs to its own successor and the successor is one of the sets
being unioned; and the chain reaches forward, a rung belonging to every strictly
later one, by composing one step with the transitivity of the later rung.

Stating the reach with the gap as an explicit summand, rather than through an
order relation, is what makes two rungs mergeable by addition alone. That matters
because merging rungs is the only thing a tuple of parameters costs, and it is
worth not paying for arithmetic to do it.

Separating the ladder from the tower is worth a moment's care, because the next
chapter needs a ladder built differently: one whose single step closes *all* the
matrices of a formula at once. Everything below is proved of the ladder, so that
chapter builds its ladder and gets the argument, rather than running it again.
<!--zh-->
论证真正需要的不是某座特定的塔，而是一架**梯**：由自然数索引的、上升的序数链。它的极限是并，且是序数，因为序数族之并是序数；每一级都属于极限，因为它属于自己的后继，而后继是被取并的集合之一；而这条链向前够得着，一级属于此后每个严格更晚的级，只需把一步与更晚那级的传递性复合。

把「够得着」的间隔写成显式的加项、而非诉诸序关系，正是使两级仅凭加法即可合并的原因。这要紧，因为合并诸级是参数元组所付的唯一代价，而不必为此额外买一套算术。

把梯与塔分开值得费些心思，因为下一章需要一架造法不同的梯：其单步一举闭合一条公式的**全部**矩阵。以下一切都是关于梯来证的，于是那一章只须造它的梯，便可得到这套论证，而不必重跑一遍。
<!--/-->

```agda
ClosedFor : (β : V ℓ) {k : ℕ} (ψ : Formula S (suc k)) → Type (ℓ-suc ℓ)
ClosedFor β {k} ψ = (ρ : S ^ k) → Below β ρ → ⟨ SatEx ψ ρ ⟩ → ⟨ Wit ψ ρ β ⟩

module Ladder (G : ℕ → V ℓ) (G-ord : (n : ℕ) → IsOrd (G n))
              (G-up : (n : ℕ) → ⟨ G n ∈ G (suc n) ⟩) where

  reach : (n d : ℕ) → ⟨ G n ∈ G (suc (d + n)) ⟩
  reach n zero    = G-up n
  reach n (suc d) =
    G-ord (suc (suc (d + n))) .fst {x = G (suc (d + n))} {y = G n}
      (reach n d) (G-up (suc (d + n)))

  fam : Lift {ℓ-zero} {ℓ} ℕ → V ℓ
  fam i = G (lower i)

  top : V ℓ
  top = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) fam)

  top-ord : IsOrd top
  top-ord = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) fam (λ i → G-ord (lower i))

  G∈top : (n : ℕ) → ⟨ G n ∈ top ⟩
  G∈top n = ∈∈ₛ {a = G n} {b = top} .snd
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) fam) (G n) .snd
      ∣ G (suc n)
      , ( ∈∈ₛ {a = G (suc n)} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) fam} .fst
            ∣ lift (suc n) , refl ∣₁
        , ∈∈ₛ {a = G n} {b = G (suc n)} .fst (G-up n) ) ∣₁)
```

<!--en-->
The closure argument needs its parameters on a rung, not merely under the limit.
For one parameter, two inversions get it there: an ordinal in the limit belongs
to one of the sets being unioned, hence to a rung; and a set in the stage of the
limit belongs, by the tower's characterization, to the operator applied to the
stage of some smaller ordinal, so locating that ordinal and going back in places
the set in that rung's stage.

For a tuple, the rungs found for the entries have to be merged, and the reach
lemma merges two of them: from rungs `n` and `m`, both reach rung `suc (n + m)`,
one of them directly and the other after commuting the sum. Recursion on the
tuple merges all of them, and monotonicity carries the earlier entries up.
<!--zh-->
闭包论证要它的参数落在某一级上，而不只是落在极限之下。对单个参数，两次反演把它送到那里：极限中的序数属于被取并的集合之一，因而属于某一级；而极限之阶段中的集合，按塔的刻画，属于某个更小序数之阶段上的算子，故把那个序数定位、再走「进去」，就把该集合放进了那一级的阶段。

对元组，为各项找到的诸级必须合并，而「够得着」引理合并其中两个：自级 `n` 与级 `m`，二者都够得着级 `suc (n + m)`，一个直接够到，另一个交换加法之后够到。沿元组递归把它们全部合并，而单调性把靠前的诸项抬上去。
<!--/-->

```agda
  δ∈top→fin : (δ : V ℓ) → ⟨ δ ∈ top ⟩ → ∥ (Σ[ N ∈ ℕ ] ⟨ δ ∈ G N ⟩) ∥₁
  δ∈top→fin δ δ∈ = PT.rec squash₁
    (λ { (v , (v∈ₛsett , δ∈ₛv)) → PT.map
        (λ { (i , Gi≡v) → lower i
           , ∈∈ₛ {a = δ} {b = G (lower i)} .snd
               (subst (λ w → ⟨ δ ∈ₛ w ⟩) (sym Gi≡v) δ∈ₛv) })
        (∈∈ₛ {a = v} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) fam} .snd v∈ₛsett) })
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) fam) δ .fst
      (∈∈ₛ {a = δ} {b = top} .fst δ∈))

  localize₁ : (e : V ℓ) → ⟨ e ∈ Lset top ⟩ → ∥ (Σ[ N ∈ ℕ ] ⟨ e ∈ Lset (G N) ⟩) ∥₁
  localize₁ e e∈ = PT.rec squash₁
    (λ { (δ , (δ∈top , e∈𝒟ₒδ)) → PT.map
        (λ { (N , δ∈GN) → N , Lset-in (G N) δ e δ∈GN e∈𝒟ₒδ })
        (δ∈top→fin δ δ∈top) })
    (Lset-out top e e∈)

  localize : {j : ℕ} (ρ : S ^ j) → Below top ρ → ∥ (Σ[ N ∈ ℕ ] Below (G N) ρ) ∥₁
  localize []      _        = ∣ zero , tt* ∣₁
  localize (p ∷ ρ) (h , hs) = PT.rec squash₁
    (λ { (N , h') → PT.map (merge N h') (localize ρ hs) })
    (localize₁ (fst p) h)
    where
    merge : (N : ℕ) → ⟨ fst p ∈ Lset (G N) ⟩
          → Σ[ M ∈ ℕ ] Below (G M) ρ
          → Σ[ M ∈ ℕ ] Below (G M) (p ∷ ρ)
    merge N h' (M , hs') = suc (M + N)
      , ( Lset-mono (reach N M) h'
        , Below-mono (subst (λ n → ⟨ G M ∈ G (suc n) ⟩) (+-comm N M)
                        (reach M N)) hs' )

  land : (q : S) (σ τ : V ℓ)
       → ⟨ fst q ∈ Lset σ ⟩ → ⟨ σ ∈ τ ⟩ → ⟨ τ ∈ top ⟩ → ⟨ fst q ∈ Lset top ⟩
  land q σ τ fq∈σ σ∈τ τ∈top =
    Lset-mono {α = top} {β = τ} τ∈top (Lset-mono {α = τ} {β = σ} σ∈τ fq∈σ)
```

<!--en-->
## Closure
<!--zh-->
## 闭包
<!--/-->

<!--en-->
A ladder **answers** for a matrix when every environment indexed from a rung has
its answering stage on the next rung. That one hypothesis is all the closure
argument uses about how the ladder was built, and it is what the next section and
the next chapter each supply in their own way.

Given it, the limit is closed for the matrix. Locate the environment on a rung
and name it there: it is the image of some tuple of indices of that rung's stage,
up to an equality that the reading lemma returns along with the tuple. Its
answering stage is on the next rung, so whatever lives in the answering stage
lives in that rung's stage, hence under the limit; two applications of
monotonicity, and the equation transported back.
<!--zh-->
一架梯对某矩阵**作答**，指凡由某级索引出的环境，其作答阶段都落在下一级上。关于梯是怎么造的，闭包论证用到的仅此一条假设，而下一节与下一章各以自己的方式供给它。

有了它，极限对该矩阵闭合。把环境定位到某一级，并在那里为它命名：它是那一级之阶段的某个索引元组的像，至多相差一个等式，而读取引理连同元组一并交还了它。它的作答阶段落在下一级上，故住在作答阶段里的东西便住在那一级的阶段里，因而落在极限之下；两次单调性，再把那个等式搬回去。
<!--/-->

```agda
  module _ {k : ℕ} (ψ : Formula S (suc k))
           (answers : (n : ℕ) (ms : ⟪ Lset (G n) ⟫ ^ k)
                    → ⟨ pickStage ψ (LsetEnv (G n) (G-ord n) ms) ∈ G (suc n) ⟩)
           where

    closure : ClosedFor top ψ
    closure ρ below sat = PT.rec squash₁ atRung (localize ρ below)
      where
      atRung : Σ[ N ∈ ℕ ] Below (G N) ρ → ⟨ Wit ψ ρ top ⟩
      atRung (N , belowN) = PT.map found (pickWitness ψ ρₘ satₘ)
        where
        idx = indexEnv (G N) (G-ord N) ρ belowN
        ρₘ : S ^ k
        ρₘ = LsetEnv (G N) (G-ord N) (idx .fst)
        e : ρₘ ≡ ρ
        e = idx .snd
        satₘ : ⟨ SatEx ψ ρₘ ⟩
        satₘ = subst (λ r → ⟨ SatEx ψ r ⟩) (sym e) sat
        found : Σ[ q ∈ S ] (⟨ fst q ∈ Lset (pickStage ψ ρₘ) ⟩ × ⟨ Sat ψ ρₘ q ⟩)
              → Σ[ q ∈ S ] (⟨ fst q ∈ Lset top ⟩ × ⟨ Sat ψ ρ q ⟩)
        found (q , (fq∈pick , satq)) = q
          , ( land q (pickStage ψ ρₘ) (G (suc N))
                fq∈pick (answers N (idx .fst)) (G∈top (suc N))
            , subst (λ r → ⟨ Sat ψ r q ⟩) e satq )
```

<!--en-->
Which gives the theorem the later chapters consume. For an environment under the
limit, the class model satisfies the existential exactly when a witness lies in
the limit's stage. Forwards is closure; backwards is forgetting where the witness
lives.

The forward direction needs no translation step, because the two sides are the
same proposition already: the semantics of an existential quantifier is the
truncated sum over the carrier, and that is what `SatEx`{.Agda} was defined to
be. So the theorem is closure with its statement rewritten, and nothing is paid
to cross between syntax and the meta-level.
<!--zh-->
于是有了后续诸章将要消费的定理。对落在极限之下的环境，类模型满足那个存在量词，恰当极限之阶段中有一个见证。正向是闭包，反向是忘掉见证住在哪里。

正向不需要翻译的一步，因为两侧本已是同一个命题：存在量词的语义是沿载体的截断和，而 `SatEx`{.Agda} 当初就是照这个定义的。故定理是闭包换了个说法，而在语法与元层之间往返，分文未付。
<!--/-->

```agda
    reflect-bwd : (ρ : S ^ k) → ⟨ Wit ψ ρ top ⟩ → ⟨ ρ ⊨ (∃̇ ψ) ⟩
    reflect-bwd ρ = PT.map (λ { (q , (_ , satq)) → q , satq })

    reflect : (ρ : S ^ k) → Below top ρ → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ top
    reflect ρ below = ⇔toPath (closure ρ below) (reflect-bwd ρ)
```

<!--en-->
## The ladder for a single matrix
<!--zh-->
## 单矩阵的梯
<!--/-->

<!--en-->
And the first ladder. A stage's index set is a type of the ambient size, and so
is any tuple over it, so the bounding lemma applies: the answering stages of all
the environments drawn from one stage have a common bound. Merging that bound
with the stage itself gives the step, which therefore both contains its argument,
so that iterating it climbs, and contains every answer for the argument's
environments, which is exactly the answering hypothesis.

The step is sealed. Unfolded, it is a bound built from a bound built from the
excluded middle, and the closure argument matches on rungs repeatedly; a
transparent definition would push that whole tower into every conversion check.
The three properties open the seal once each, and the last of them is the one
place transitivity is used, so the chain from the answer through the bound into
the step is closed inside the seal and the caller sees only its conclusion.
<!--zh-->
以及第一架梯。阶段的索引集是周遭大小的类型，其上的元组也是，故界层引理适用：取自同一阶段的全部环境，其作答阶段有公共上界。把那个上界与该阶段本身合并，就得到步进，它因而既包含自己的自变量，使迭代得以攀升，又包含自变量的诸环境的每个回答，而后者恰是那条作答假设。

步进被封印。展开来，它是由排中律所造之界再造之界，而闭包论证反复在诸级上匹配；透明的定义会把那整座塔推进每一次转换检查。三条性质各开封一次，其中最后一条是唯一用到传递性之处，故从回答经上界进入步进的这条链封在印内，调用方只见其结论。
<!--/-->

```agda
module Single {k : ℕ} (ψ : Formula S (suc k)) where

  Fbnd : (σ : V ℓ) (oσ : IsOrd σ)
       → Σ[ β ∈ V ℓ ] (IsOrd β × ((ms : ⟪ Lset σ ⟫ ^ k)
                                 → ⟨ pickStage ψ (LsetEnv σ oσ ms) ∈ β ⟩))
  Fbnd σ oσ = boundingOrd (⟪ Lset σ ⟫ ^ k)
                (λ ms → pickStage ψ (LsetEnv σ oσ ms))
                (λ ms → pickStage-ord ψ (LsetEnv σ oσ ms))

  opaque
    Fstep : (σ : V ℓ) → IsOrd σ → V ℓ
    Fstep σ oσ = bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .fst

  opaque
    unfolding Fstep

    Fstep-ord : (σ : V ℓ) (oσ : IsOrd σ) → IsOrd (Fstep σ oσ)
    Fstep-ord σ oσ = bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .fst

    σ∈Fstep : (σ : V ℓ) (oσ : IsOrd σ) → ⟨ σ ∈ Fstep σ oσ ⟩
    σ∈Fstep σ oσ =
      bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .snd .snd

    pickLand : (σ : V ℓ) (oσ : IsOrd σ) (ms : ⟪ Lset σ ⟫ ^ k)
             → ⟨ pickStage ψ (LsetEnv σ oσ ms) ∈ Fstep σ oσ ⟩
    pickLand σ oσ ms =
      Fstep-ord σ oσ .fst {x = Fbnd σ oσ .fst}
                          {y = pickStage ψ (LsetEnv σ oσ ms)}
        (Fbnd σ oσ .snd .snd ms)
        (bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .snd .fst)

  βₙ : ℕ → V ℓ
  βₙ-ord : (n : ℕ) → IsOrd (βₙ n)
  βₙ zero        = ∅
  βₙ (suc n)     = Fstep (βₙ n) (βₙ-ord n)
  βₙ-ord zero    = ∅-ord
  βₙ-ord (suc n) = Fstep-ord (βₙ n) (βₙ-ord n)

  βₙ-step : (n : ℕ) → ⟨ βₙ n ∈ βₙ (suc n) ⟩
  βₙ-step n = σ∈Fstep (βₙ n) (βₙ-ord n)

  module L = Ladder βₙ βₙ-ord βₙ-step

  βω : V ℓ
  βω = L.top

  answers : (n : ℕ) (ms : ⟪ Lset (βₙ n) ⟫ ^ k)
          → ⟨ pickStage ψ (LsetEnv (βₙ n) (βₙ-ord n) ms) ∈ βₙ (suc n) ⟩
  answers n = pickLand (βₙ n) (βₙ-ord n)

  closed : ClosedFor βω ψ
  closed = L.closure ψ answers

  reflect : (ρ : S ^ k) → Below βω ρ → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ βω
  reflect = L.reflect ψ answers
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
A **ladder** is an ascending chain of ordinals; it **answers** for a matrix when
each rung's environments have their answering stages on the next rung; and when
it does, its limit is closed for that matrix, which `reflect`{.Agda} restates as
the reflection of an existential. `Single`{.Agda} builds the ladder for one
matrix, by bounding a stage's answers and merging with the stage.

The construction used the excluded middle twice, once to decide satisfiability
and once inside the descent, and used the axiom of choice not at all. That is the
point of taking the least *stage* rather than the least *witness*: the ordinals
come well-ordered, and nothing here has to ask for a well-ordering of L.

What is delivered is one quantifier, at any number of parameters. An arbitrary
formula has many quantifiers, hence many matrices, and no single-matrix limit
serves them all; the next chapter builds a ladder whose step closes all of them
at once, and gets everything above for it without rerunning any of it.
<!--zh-->
一架**梯**是上升的序数链；它对某矩阵**作答**，指每一级的环境其作答阶段都落在下一级上；而当它作答时，它的极限对该矩阵闭合，`reflect`{.Agda} 把这一点重述为存在量词的反射。`Single`{.Agda} 造出单矩阵的梯，办法是界住一个阶段的诸回答，再与该阶段合并。

这个构造用了两次排中律，一次判定可满足性，一次在下降之内，而选择公理一次也没用。这正是取最小**阶段**而非最小**见证**的用意：序数自带良序，而此处没有任何东西需要索取 L 的良序。

交付的是一个量词，参数任意多。任意公式有许多量词，因而有许多矩阵，而没有哪个单矩阵极限能同时服务全部；下一章将造一架梯，其步进一举闭合它们全部，并因此白得上面的一切，无须重跑其中任何一步。
<!--/-->
