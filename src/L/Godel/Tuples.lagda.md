# Tuples as graphs

<!--en-->
The assignments the operations will push around, as sets. An assignment of
length `n` valued in a carrier is coded by its graph: the set of Kuratowski
pairs of a numeral key with the value at that key. The coding is the
environment chapter's, and nothing about it is new here; what this chapter
proves is its **algebra against the operations**: extending an assignment by
one value is the graph extension, dropping the first value is the shift, the
empty assignment is the empty set, and the set of all assignments over the
carrier steps by the family extension. One numeral lemma funds the whole
file: the von Neumann successor is injective at a numeral, which is what lets
a shifted key be read back.

Every statement here holds its assignments **valued in the carrier**, which
is the form every consumer arrives in: satisfaction sets, the closure, and
the orders all speak about assignments drawn from a fixed set, never about
bare hierarchy values.
<!--zh-->
运算即将推动的诸赋值，作为集合。取值于载体的长度 `n` 赋值由它的图编码：即「数码键与该键处取值」的 Kuratowski 对之集。这套编码是环境那一章的，此处没有任何新东西；本章要证的是它**对着运算的代数**：把赋值扩张一个取值就是图扩张，弃掉首个取值就是移位，空赋值是空集，而载体之上全体赋值之集按族扩张走步。一条数码引理资助全文：冯·诺伊曼后继在数码处单射，正是它使被移位的键能被读回。

此处每条陈述都把赋值**取值于载体**，而那正是每个消费方到场时的形态：满足集、闭包与诸序谈论的都是取自某个固定集合的赋值，从不谈论裸层级取值。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Godel.Tuples {ℓ : Level} where

open import V.Hierarchy {ℓ} using ( extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( pair-spec; self∈sucV; ∈sucV-elim )
open import L.Ordinal {ℓ} using ( ∈#-elim; #∈#-elim )
open import L.Coding.Environment {ℓ} using ( env; cons; lookup-spec )
open import L.Godel.Operations {ℓ}
  using ( extendGraph; extendGraph-zero; extendGraph-suc; extendGraph-out
        ; tailGraph; tailGraph-in; tailGraph-out
        ; extendFamily; extendFamily-in; extendFamily-out )

open import Cubical.Data.FinData using ( toℕ; ¬Fin0 )
open import Cubical.Data.Nat.Order using ( ¬m<m; <≤-trans; pred-≤-pred )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( sucV; #_ )
```

<!--en-->
## The successor is injective at a numeral

If two von Neumann successors agree and one is taken at a numeral, the
arguments agree. The numeral is essential: the general statement would decide
membership, but at a numeral the members below are numerals with smaller
indices, and a numeral cannot sit strictly below itself. This is the only
place the file argues about ordinals, and everything the shift equation owes
to renumbering is paid here.
<!--zh-->
## 后继在数码处单射

两个冯·诺伊曼后继相等而其中一个取在数码处，则实参相等。数码是本质的：一般形式的陈述会判定隶属，而在数码处，其下的成员是更小指标的数码，而数码不能严格坐在自己之下。这是本文唯一一处谈论序数的地方，移位等式欠重编号的一切都在此付清。
<!--/-->

```agda
suc#-inj : (k : ℕ) (a : V ℓ) → sucV (# k) ≡ sucV a → # k ≡ a
suc#-inj k a e = ∈sucV-elim {A = a} {x = # k} (setIsSet (# k) a)
  (subst (λ z → ⟨ # k ∈ z ⟩) e (self∈sucV (# k)))
  (λ k∈a → PT.rec (setIsSet (# k) a)
    (λ { (m , m<sk , a≡#m) → Empty.rec (¬m<m
      (<≤-trans
        (#∈#-elim k m (subst (λ z → ⟨ # k ∈ z ⟩) a≡#m k∈a))
        (pred-≤-pred m<sk))) })
    (∈#-elim (suc k) a
      (subst (λ z → ⟨ a ∈ z ⟩) (sym e) (self∈sucV a))))
  (λ q → q)
```

<!--en-->
## The graph of an assignment, against extension and shift

Everything below fixes the carrier and values its assignments in it; the
graph of an assignment is the environment coding applied under the carrier's
embedding.

Three equations, all by extensionality. A nonempty assignment's graph **is**
the extension of its tail's graph by its head: one direction sends the entry
at zero to the new-key case and every later entry along the renumbering, the
other splits a member of the extension back into the two cases, reading the
keys off with the pair injectivity. Shifting the graph down recovers the
tail's graph: the entry at zero cannot survive the shift, because the empty
set is no successor, and every other entry comes back through the successor's
injectivity at its numeral key. The empty assignment's graph has no entries
at all.
<!--zh-->
## 赋值的图，对着扩张与移位

以下全部固定载体并令赋值取值其中；赋值的图就是环境编码接在载体嵌入之后。

三条等式，全由外延性。非空赋值的图**就是**其尾图被其首取值的扩张：一个方向把零处条目送进新键情形、把之后每个条目沿重编号送过去，另一个方向把扩张的成员拆回两种情形，用对的单射把键读出。把图下移恢复尾图：零处条目过不了移位，因为空集不是任何后继，而其余每个条目都经「后继在其数码键处的单射」回来。空赋值的图没有任何条目。
<!--/-->

```agda
module _ (A : V ℓ) where
  private
    κ : ⟪ A ⟫ → V ℓ
    κ = ⟪ A ⟫↪

    memb : (m : ⟪ A ⟫) → ⟨ κ m ∈ A ⟩
    memb m = ∈∈ₛ {a = κ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)

  tuple : {n : ℕ} → (Fin n → ⟪ A ⟫) → V ℓ
  tuple g = env (λ i → κ (g i))

  tuple-extend : {n : ℕ} (g : Fin (suc n) → ⟪ A ⟫)
               → tuple g ≡ extendGraph (κ (g zero)) (tuple (λ i → g (suc i)))
  tuple-extend {n} g = extensionalV λ w → ⇔toPath (fwd w) (bwd w)
    where
    tl : Fin n → ⟪ A ⟫
    tl i = g (suc i)
    R : V ℓ
    R = extendGraph (κ (g zero)) (tuple tl)
    fwd : (w : V ℓ) → ⟨ w ∈ tuple g ⟩ → ⟨ w ∈ R ⟩
    fwd w = PT.rec (snd (w ∈ R)) go
      where
      go : Σ[ li ∈ Lift (Fin (suc n)) ]
             (pr (# (toℕ (lower li))) (κ (g (lower li))) ≡ w)
         → ⟨ w ∈ R ⟩
      go (lift zero , e) =
        subst (λ q → ⟨ q ∈ R ⟩) e
          (extendGraph-zero {y = κ (g zero)} {γ = tuple tl})
      go (lift (suc i) , e) =
        subst (λ q → ⟨ q ∈ R ⟩) e
          (extendGraph-suc {y = κ (g zero)} {γ = tuple tl}
            {a = # (toℕ i)} {v = κ (tl i)}
            ∣ lift i , refl ∣₁)
    bwd : (w : V ℓ) → ⟨ w ∈ R ⟩ → ⟨ w ∈ tuple g ⟩
    bwd w h = PT.rec (snd (w ∈ tuple g))
      (Sum.rec
        (λ e → ∣ lift zero , sym e ∣₁)
        (λ { (a , v , hav , e) → PT.rec (snd (w ∈ tuple g))
          (λ { (lift i , eig) →
            ∣ lift (suc i)
            , sym (e ∙ cong₂ (λ p q → pr (sucV p) q)
                     (sym (pr-inj eig .fst)) (sym (pr-inj eig .snd))) ∣₁ })
          hav }))
      (extendGraph-out {y = κ (g zero)} {γ = tuple tl} h)

  tupleTail : {n : ℕ} (g : Fin (suc n) → ⟪ A ⟫)
            → tailGraph (tuple g) ≡ tuple (λ i → g (suc i))
  tupleTail {n} g = extensionalV λ z → ⇔toPath (fwd z) (bwd z)
    where
    tl : Fin n → ⟪ A ⟫
    tl i = g (suc i)
    fwd : (z : V ℓ) → ⟨ z ∈ tailGraph (tuple g) ⟩ → ⟨ z ∈ tuple tl ⟩
    fwd z h = PT.rec (snd (z ∈ tuple tl)) go (tailGraph-out {w = tuple g} h)
      where
      go : Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
             (⟨ pr (sucV a) v ∈ tuple g ⟩ × (z ≡ pr a v))
         → ⟨ z ∈ tuple tl ⟩
      go (a , v , hav , e) = PT.rec (snd (z ∈ tuple tl))
        (λ { (lift zero , eig) →
              Empty.rec (∅-empty a (∈∈ₛ {a = a} {b = ∅} .fst
                (subst (λ q → ⟨ a ∈ q ⟩) (sym (pr-inj eig .fst))
                  (self∈sucV a))))
           ; (lift (suc i) , eig) →
              ∣ lift i
              , sym (e ∙ cong₂ pr
                       (sym (suc#-inj (toℕ i) a (pr-inj eig .fst)))
                       (sym (pr-inj eig .snd))) ∣₁ })
        hav
    bwd : (z : V ℓ) → ⟨ z ∈ tuple tl ⟩ → ⟨ z ∈ tailGraph (tuple g) ⟩
    bwd z = PT.rec (snd (z ∈ tailGraph (tuple g)))
      (λ { (lift i , e) →
        subst (λ q → ⟨ q ∈ tailGraph (tuple g) ⟩) e
          (tailGraph-in {w = tuple g} {a = # (toℕ i)} {v = κ (tl i)}
            ∣ lift (suc i) , refl ∣₁) })

  tuple-empty : (g : Fin 0 → ⟪ A ⟫) → tuple g ≡ ∅
  tuple-empty g = extensionalV λ w → ⇔toPath
    (PT.rec (snd (w ∈ ∅)) (λ { (li , _) → Empty.rec (¬Fin0 (lower li)) }))
    (λ h → Empty.rec (∅-empty w (∈∈ₛ {a = w} {b = ∅} .fst h)))
```

<!--en-->
Two assignments with the same graph record the same value at every key: the
entry of the one graph at a key is read against the other graph's lookup
specification. This is the injectivity every binary case downstream leans on
when two memberships hand back two assignments for one set.
<!--zh-->
图相同的两个赋值在每个键处记录相同的取值：一个图在某键处的条目，对着另一个图的查值规格去读。下游每个二元情形在两份隶属交回同一集合的两个赋值时，倚靠的就是这条单射性。
<!--/-->

```agda
  tuple-entry : {n : ℕ} {g h : Fin n → ⟪ A ⟫}
              → tuple g ≡ tuple h → (i : Fin n) → κ (g i) ≡ κ (h i)
  tuple-entry {n} {g} {h} e i =
    subst ⟨_⟩ (lookup-spec (λ x → κ (h x)) i (κ (g i)))
      (subst (λ q → ⟨ pr (# (toℕ i)) (κ (g i)) ∈ q ⟩) e
        ∣ lift i , refl ∣₁)
```

<!--en-->
## All assignments over the carrier

The set of graphs of all length-`n` assignments valued in the carrier, and
its own two equations: at length zero it is the pair of the empty set with
itself, and each length up is the family extension of the previous by the
carrier, which is the graph equation above lifted memberwise. This set is
what a satisfaction set will be cut from, and the stepping equation is what
will make it reachable.
<!--zh-->
## 载体之上的全体赋值

取值于载体的全体长度 `n` 赋值之图所成的集合，连同它自己的两条等式：长度零处它是空集与自身之对，而每升一级长度，它是前一级被载体所作的族扩张，即上面那条图等式逐成员提升。满足关系的集合将从这个集合上切出，而走步等式将使它可达。
<!--/-->

```agda
  allTuples : ℕ → V ℓ
  allTuples n = sett (Fin n → ⟪ A ⟫) tuple

  allTuples-zero : allTuples 0 ≡ ⁅ ∅ , ∅ ⁆
  allTuples-zero = extensionalV λ w → ⇔toPath
    (PT.rec (snd (w ∈ ⁅ ∅ , ∅ ⁆))
      (λ { (g , e) → subst ⟨_⟩ (sym (pair-spec ∅ ∅ w))
             ∣ Sum.inl (sym e ∙ tuple-empty g) ∣₁ }))
    (λ h → PT.rec (snd (w ∈ allTuples 0))
      (Sum.rec
        (λ e → ∣ (λ ()) , tuple-empty (λ ()) ∙ sym e ∣₁)
        (λ e → ∣ (λ ()) , tuple-empty (λ ()) ∙ sym e ∣₁))
      (subst ⟨_⟩ (pair-spec ∅ ∅ w) h))

  allTuples-suc : (n : ℕ) → allTuples (suc n) ≡ extendFamily (allTuples n) A
  allTuples-suc n = extensionalV λ w → ⇔toPath (fwd w) (bwd w)
    where
    fwd : (w : V ℓ) → ⟨ w ∈ allTuples (suc n) ⟩
        → ⟨ w ∈ extendFamily (allTuples n) A ⟩
    fwd w = PT.rec (snd (w ∈ extendFamily (allTuples n) A))
      λ { (g , e) →
        subst (λ z → ⟨ z ∈ extendFamily (allTuples n) A ⟩)
          (sym (tuple-extend g) ∙ e)
          (extendFamily-in {X = allTuples n} {Y = A}
            {γ = tuple (λ i → g (suc i))} {y = κ (g zero)}
            ∣ (λ i → g (suc i)) , refl ∣₁
            (memb (g zero))) }
    bwd : (w : V ℓ) → ⟨ w ∈ extendFamily (allTuples n) A ⟩
        → ⟨ w ∈ allTuples (suc n) ⟩
    bwd w h = PT.rec (snd (w ∈ allTuples (suc n)))
      (λ { (γ , y , hγ , hy , e) → PT.rec (snd (w ∈ allTuples (suc n)))
        (λ { (g , eg) →
          ∣ cons (∈-asFiber {a = y} {b = A} hy .fst) g
          , tuple-extend (cons (∈-asFiber {a = y} {b = A} hy .fst) g)
            ∙ cong₂ extendGraph (∈-asFiber {a = y} {b = A} hy .snd) eg
            ∙ sym e ∣₁ })
        hγ })
      (extendFamily-out {X = allTuples n} {Y = A} h)
```

<!--en-->
## Recap

One numeral lemma, `suc#-inj`{.Agda}; the carrier-valued tuple coding
`tuple`{.Agda} with three graph equations, `tuple-extend`{.Agda},
`tupleTail`{.Agda} and `tuple-empty`{.Agda}, aligning an assignment's graph
with the extension and shift operations, plus the entrywise injectivity
`tuple-entry`{.Agda}; and the family `allTuples`{.Agda} of all assignments
over the carrier with its zero and successor equations.
Nothing here mentions a formula: this is the pure algebra of coded tuples,
and the chapter that relates satisfaction to the operations spends it
wholesale.
<!--zh-->
## 小结

一条数码引理 `suc#-inj`{.Agda}；载体值的元组编码 `tuple`{.Agda} 与三条图等式 `tuple-extend`{.Agda}、`tupleTail`{.Agda}、`tuple-empty`{.Agda}，把赋值的图与扩张、移位两个运算对齐，外加逐条目单射性 `tuple-entry`{.Agda}；以及载体之上全体赋值的族 `allTuples`{.Agda} 连同它的零与后继等式。此处无一提及公式：这是被编码元组的纯代数，而把满足关系与运算联系起来的那一章将整批花掉它。
<!--/-->
