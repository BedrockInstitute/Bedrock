<!--en-->
# Existential reflection into a constructible stage

For one existential formula and parameters from a constructible stage, this chapter builds a larger ordinal stage that contains witnesses whenever the ambient constructible universe does. Iterating the witness-selection step and taking an ordinal limit makes the stage closed under answers to that formula.
<!--zh-->
# 存在公式到可构造层的反射

对一条存在公式以及来自某个可构造层的参数，本章构造一个更大的序数层：只要环境可构造宇宙中存在见证，该层也包含见证。迭代见证选择步骤并取序数极限，可使这一层包含该公式对其中参数所需的见证。
<!--ja-->
# 存在論理式の構成可能段階への反映

一つの存在論理式と構成可能段階から取ったパラメータに対し、周囲の構成可能宇宙に証人があればそれを含む、より大きな順序数段階を構成します。証人を選ぶ操作を反復して順序数極限を取ると、その論理式への解答について閉じた段階が得られます。
<!--/-->

<!--en-->
It can be done, and the argument is Montague's. Fix a matrix and an environment of
parameters. If a witness exists at all, there is a least stage containing one,
and that stage is a set-sized answer to a class-sized question. Range over all
tuples of parameters drawn from one stage, bound the answers, and the result is a
single stage that answers for every tuple from the stage below. Iterate that step
through the natural numbers and take the union: the limit answers for its own
parameters, because any finite tuple from the limit already lies in some finite
layer, whose answers were bounded at the next.

Two departures from the usual practice occur here. The choice of witness is where a
well-ordering of L is normally invoked, and it is not needed: what the
argument requires is a canonical *ordinal*, not a canonical element, and the
ordinals are already well-ordered by membership. So the least stage that holds a
witness is taken directly, by the descent of the stage chapter, without deciding
which witness is there. And the parameters are a tuple from the start. Writing the
one-parameter case first and generalizing later would mean writing the whole
construction twice, since every step of it is indifferent to how many parameters
there are; the only place the tuple matters is in locating it, where finitely many
layers have to be merged into one.
<!--zh-->
这一构造可以完成，其论证出自 Montague。固定一个矩阵与一个参数环境。若见证存在，就有一个包含见证的最小层，从而以一个集合大小的层控制原本涉及真类的搜索。取遍某一层中的全部参数元组，并为所得各层取一个共同上界，便得到单一层，其中包含下方层每个元组所需的见证。沿自然数迭代这一步并取并，所得极限也具有相同性质：极限中的任何有穷元组早已属于某个有穷层，而该层所需见证的层在下一层已被界住。

此处有两点与通常做法不同。通常会在选择见证时使用 L 的良序，而这里并不需要：论证所需的是典范的**序数**，而非典范的元素，并且序数已经由成员关系良序化。因此，可由讨论层的一章的下降论证直接取包含见证的最小层，而不指定其中究竟是哪一个见证。此外，参数从一开始就是元组。若先处理单参数情形再作推广，就要把整个构造写两遍，因为构造的每一步都不依赖参数的个数；只有在定位元组时需要考虑这一点，并把有穷多个层合并成一个。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.ExistentialReflection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( union-family-in; union-family-out )
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
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⋃_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Environments drawn from a stage

An element of a stage becomes an element of the class model by the tower's
membership criterion, so a stage's index set is a supply of parameters, and a
tuple of indices is a supply of environments. That is what makes the bounding
lemma applicable below: the tuples form a type of the ambient size, being a
vector over one.
<!--zh-->
## 取自一层的环境

参数取自层的索引集，索引元组则给出环境：层的一个元素经塔的隶属判据成为类模型的一个元素。正是这一点使下面的界层引理得以适用：诸元组构成周遭大小的类型，因为它正是其上的向量。
<!--ja-->
## 環境を一つの段階から取る

`LsetEnv`{.Agda} は段階の小さな提示からパラメータ環境を作り、`Below σ ρ`{.Agda} は環境の全成分が `Lset σ`{.Agda} に属することを表します。この条件は段階を大きくすると保存されます。
<!--/-->

<!--en-->
An environment *lies below* a stage when each of its entries does. Reading the
tuple of indices back off such an environment is the inverse operation, and it
returns the equation as well, since the construction will need to know that the
environment it bounded is the one it was given. The equation is where
constructibility being a proposition is used: two elements of the model agree as
soon as their underlying sets do.
<!--zh-->
一个环境**落在**某层之下，指它的每一项都落在其下。从这样的环境读回索引元组是逆向的操作，且同时给出等式，因为构造需要知道：它所界定的环境正是输入的那一个。等式正是用到「可构造性是命题」之处：模型的两个元素，只要底集相同就相等。
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

Fix a matrix in one witness variable and `k` parameters. "Some witness for this
environment lives in this stage" is a property of ordinals, so the stage
chapter's descent applies to it directly. Its premise is that some ordinal has
the property, which follows from satisfiability alone: a witness is an element of
L, and an element of L lies in some stage by definition.
<!--zh-->
## 作答层

固定一个矩阵，其中含一个见证变元与 `k` 个参数。「这个环境的某个见证落在该层里」是序数的一条性质，故讨论层的那一章的下降直接适用于它。它的前提是某个序数具有该性质，而这仅凭可满足性即得：见证是 L 的元素，而 L 的元素按定义落在某一层里。
<!--ja-->
## 解答を含む段階

存在論理式が真なら、その証人は構成可能なので最小の段階を持ちます。選択した証人とその段階を一つの順序数上界へ集めることで、与えられた環境への解答を含む段階を得ます。
<!--/-->

<!--en-->
Totality then wants a value even when no witness exists, and the excluded middle
supplies the case distinction. As in the stage chapter, the distinction is made
by an explicit auxiliary rather than by a `with`, because the load-bearing lemma
below has to name the very same decision value and match on it.
<!--zh-->
其次，全函数性要求即便见证不存在也得有个值，而排中律给出分情形。一如讨论层的那一章，分情形由显式的辅助函数而非 `with` 作出，因为下面那条承重引理必须点名同一个判定值并在其上匹配。
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
最后是整个构造所倚赖的那条性质：若环境根本可满足，则它的作答层确实装着一个见证。证明必须知道判定走的是哪一支，而它问不出来，因为判定是排中律的一个值，没有东西算得出它。于是它做那件标准的事：对分支作量化，记住「该分支**就是**那个判定」这条等式，并沿之搬运。在假分支上，假设自我反驳。
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

What the argument actually needs is not one particular tower but a **ladder**: an
ascending chain of ordinals indexed by the naturals. Its limit is the union, an
ordinal because the union of a family of ordinals is; each rung belongs to the
limit, since it belongs to its own successor and the successor is one of the sets
being unioned; and the chain reaches forward, a rung belonging to every strictly
later one, by composing one step with the transitivity of the later rung.
<!--zh-->
## 梯与其极限

论证真正需要的不是某座特定的塔，而是一架**梯**：由自然数索引的、上升的序数链。它的极限是并，且是序数，因为序数族之并是序数；每一级都属于极限，因为它属于自己的后继，而后继是被取并的集合之一；而这条链向前够得着，一级属于此后每个严格更晚的级，只需把一步与更晚那级的传递性复合。
<!--ja-->
## 梯子とその極限

解答を含む段階を取る操作を自然数に沿って反復し、その順序数上界を極限とします。各有限段階は次へ含まれるため、極限段階は一回の解答操作で外へ出ません。
<!--/-->

<!--en-->
Stating the reach with the gap as an explicit summand, rather than through an
order relation, is what makes two rungs mergeable by addition alone. That matters
because merging rungs is the only thing a tuple of parameters costs, and it is
worth not paying for arithmetic to do it.

Separating the ladder from the tower is worth a moment's care, because the next
chapter needs a ladder built differently: one whose single step closes *all* the
matrices of a formula at once. Everything below is proved of the ladder, so that
chapter builds its ladder and gets the argument, rather than running it again.
<!--zh-->
把「够得着」的间隔写成显式的加项而非诉诸序关系，正是使两级仅凭加法即可合并的原因。这要紧，因为合并诸级是参数元组所付的唯一代价，而不必为此额外买一套算术。

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
  G∈top n = union-family-in (Lift {ℓ-zero} {ℓ} ℕ) fam (lift (suc n)) (G n) (G-up n)
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
闭包论证要它的参数落在某一级上，而不只是落在极限之下。对单个参数，两次反演把它送到那里：极限中的序数属于被取并的集合之一，因而属于某一级；而极限之层中的集合，按塔的刻画，属于某个更小序数之层上的算子，故把那个序数定位，再走「进去」，就把该集合放进了那一级的层。

对元组，为各项找到的诸级必须合并，而「够得着」引理合并其中两个：自级 `n` 与级 `m` 都够得着级 `suc (n + m)`，一个直接够到，另一个在交换加法之后够到。沿元组递归把它们全部合并，而单调性把靠前的诸项抬高。
<!--/-->

```agda
  δ∈top→fin : (δ : V ℓ) → ⟨ δ ∈ top ⟩ → ∥ (Σ[ N ∈ ℕ ] ⟨ δ ∈ G N ⟩) ∥₁
  δ∈top→fin δ δ∈ = PT.map (λ { (i , h) → lower i , h })
    (union-family-out (Lift {ℓ-zero} {ℓ} ℕ) fam δ δ∈)

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

A ladder **answers** for a matrix when every environment indexed from a rung has
its answering stage on the next rung. That one hypothesis is all the closure
argument uses about how the ladder was built, and it is what the next section and
the next chapter each supply in their own way.
<!--zh-->
## 封闭性

一架梯对某矩阵**作答**，指凡由某级索引出的环境，其作答层都落在下一级上。关于梯如何构造，闭包论证用到的假设仅此一条，而下一节与下一章各以自己的方式给出它。
<!--ja-->
## 閉性

`ClosedFor β ψ`{.Agda} は、`β` より前の段階から取ったパラメータに対する `ψ` の証人を `Lset β`{.Agda} が含むことを表します。梯子の極限はこの条件を満たし、より大きな順序数へも移せます。
<!--/-->

<!--en-->
Given it, the limit is closed for the matrix. Locate the environment on a rung
and name it there: it is the image of some tuple of indices of that rung's stage,
up to an equality that the reading lemma returns along with the tuple. Its
answering stage is on the next rung, so whatever lives in the answering stage
lives in that rung's stage, hence under the limit; two applications of
monotonicity, and the equation transported back.
<!--zh-->
有了它，极限对该矩阵闭合。把环境定位到某一级：它是那一级之层的某个索引元组的像，至多相差一个等式，而读取引理把它连同元组一并给出。它的作答层落在下一级上，故落在作答层里的东西便落在那一级的层里，因而落在极限之下；再用两次单调性，把那个等式移回去。
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
This gives the theorem that later chapters use. For an environment under the
limit, the class model satisfies the existential exactly when a witness lies in
the limit's stage. Forwards is closure; backwards is forgetting where the witness
lives.

The forward direction needs no translation step, because the two sides are the
same proposition already: the semantics of an existential quantifier is the
truncated sum over the carrier, and that is what `SatEx`{.Agda} was defined to
be. So the theorem is closure with its statement rewritten, and moving between
syntax and the meta-level requires no further work.
<!--zh-->
于是有了后续诸章将要使用的定理。对落在极限之下的环境，类模型满足那个存在量词，恰当极限之层中有一个见证。正向就是闭包，反向则不再追问见证落在哪一级。

正向不需要翻译的一步，因为两侧本已是同一个命题：存在量词的语义是沿载体的截断和，而 `SatEx`{.Agda} 当初正是照这个定义写的。故定理只是闭包换了个说法，在语法与元层之间往返不需任何额外代价。
<!--/-->

```agda
    reflect-bwd : (ρ : S ^ k) → ⟨ Wit ψ ρ top ⟩ → ⟨ ρ ⊨ (∃̇ ψ) ⟩
    reflect-bwd ρ = PT.map (λ { (q , (_ , satq)) → q , satq })

    reflect : (ρ : S ^ k) → Below top ρ → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ top
    reflect ρ below = ⇔toPath (closure ρ below) (reflect-bwd ρ)
```

<!--en-->
## The step for a single matrix

And the step. A stage's index set is a type of the ambient size, and so
is any tuple over it, so the bounding lemma applies: the answering stages of all
the environments drawn from one stage have a common bound. Merging that bound
with the stage itself gives the step, which therefore both contains its argument,
so that iterating it climbs, and contains every answer for the argument's
environments, which is exactly the answering hypothesis.
<!--zh-->
## 单个母式的步骤

最后是那一步。层的索引集是周遭大小的类型，其上的元组也是，故界层引理适用：取自同一层的全部环境，其作答层有公共上界。把那个上界与该层本身合并，就得到步进，它因而既包含自己的自变量而使迭代得以攀升，又包含自变量的诸环境的每个回答，而后者恰是那条作答假设。
<!--ja-->
## 一つの母式に対する段階

一つの存在母式と出発段階に対し、順序数の段階を一つ進め、出発段階を含み、その母式へのすべての必要な解答について閉じた新しい段階を返します。
<!--/-->

<!--en-->
The step is sealed. Unfolded, it is a bound built from a bound built from the
excluded middle, and the closure argument matches on rungs repeatedly; a
transparent definition would push that whole tower into every conversion check.
The three properties open the seal once each, and the last of them is the one
place transitivity is used, so the chain from the answer through the bound into
the step is closed inside the seal and the caller sees only its conclusion.
<!--zh-->
步进被封印。展开来，它是由排中律所造的界再造出的界，而闭包论证反复在诸级上匹配；透明的定义会把那整座塔推进每一次转换检查。三条性质各开封一次，其中最后一条是唯一用到传递性之处，故从回答经上界进入步进的这条链封在印内，调用方只见其结论。
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

    pickLand : (σ : V ℓ) (oσ : IsOrd σ) (ms : ⟪ Lset σ ⟫ ^ k)
             → ⟨ pickStage ψ (LsetEnv σ oσ ms) ∈ Fstep σ oσ ⟩
    pickLand σ oσ ms =
      Fstep-ord σ oσ .fst {x = Fbnd σ oσ .fst}
                          {y = pickStage ψ (LsetEnv σ oσ ms)}
        (Fbnd σ oσ .snd .snd ms)
        (bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .snd .fst)
```

<!--en-->
## Recap

A **ladder** is an ascending chain of ordinals; it **answers** for a matrix when
each rung's environments have their answering stages on the next rung; and when
it does, its limit is closed for that matrix, which `reflect`{.Agda} restates as
the reflection of an existential. `Single`{.Agda} builds the step for one
matrix, by bounding a stage's answers and merging with the stage.
<!--zh-->
## 小结

一架**梯**是上升的序数链；它对某矩阵**作答**，指每一级的环境，其作答层都落在下一级上；而当它作答时，它的极限对该矩阵闭合，`reflect`{.Agda} 把这一点重述为存在量词的反射。`Single`{.Agda} 造出单矩阵的步进，办法是界住一层的诸回答，再与该层合并。
<!--ja-->
## まとめ

一つの存在論理式について、パラメータを含む段階から始め、証人の段階を反復して順序数極限を取ります。得られた段階は元の段階を含み、その論理式の存在証人について反映します。
<!--/-->

<!--en-->
The construction used the excluded middle twice, once to decide satisfiability
and once inside the descent, and used the axiom of choice not at all. That is the
point of taking the least *stage* rather than the least *witness*: the ordinals
come well-ordered, and nothing here has to ask for a well-ordering of L.

What this chapter achieves is one quantifier, with any number of parameters. An
arbitrary formula may contain many quantifiers, hence many matrices, and no
limit taken for a single matrix covers them all; the next chapter builds a
ladder whose step closes all of them at once, and thereby obtains everything
above directly, without redoing any of the individual arguments.
<!--zh-->
这个构造用了两次排中律，一次判定可满足性，一次在下降之内，而选择公理一次也没用。这正是取最小**层**而非最小**见证**的用意：序数自带良序，而此处无须用到 L 的良序。

本章的成果是一个量词，可带任意多个参数。任意公式可以含有许多量词，因而有许多矩阵，而没有哪个针对单一矩阵的极限能同时覆盖全部；下一章将构造一架梯，其一次步进同时闭合所有矩阵，并随之直接得到上面的一切，无须对其中任何一步重做论证。
<!--/-->
