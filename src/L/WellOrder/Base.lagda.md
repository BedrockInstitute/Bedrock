# Strict well-orders, and least elements

<!--en-->
One construction ahead needs to *choose*: the axiom of choice, at the end of the
book, has to pick an element out of each cell of a family, and the classical way
to make that choice is to well-order the candidates and take the least one that
qualifies.

The reflection argument was expected to be a second consumer and is not. It was
delivered with no order at all, as a ladder whose limit answers for every matrix
at once, built jointly rather than selected from. So this vocabulary has one
consumer rather than two, and it is `L.Choice.Transversal`{.Agda}, the last
chapter of the book: the search below is what picks a point out of each cell of a
disjoint family.

This chapter provides the vocabulary. A strict well-order on a type is a
relation that is trichotomous, irreflexive, transitive and well founded, bundled
as a record so that later chapters can carry one around as data. The bundle is
level-generic in a way worth one remark: the carrier and the relation take
*separate* universe levels, because the order that Part 4 eventually builds
compares formulas, which are small, by data that mentions ordinals, which are
not.

The theorem is that a non-empty subset has a least element, and it is unique.
Uniqueness is free from trichotomy. Existence is not: deciding, at each step,
whether anything smaller still qualifies is exactly a decision about an
arbitrary predicate, so this is the second place the book spends the excluded
middle. Unlike the first, here the cost buys a genuine choice function rather
than a comparison.

The assumption sits on that one theorem rather than on the chapter, which is
worth doing wherever it can be done: the bundle, the uniqueness of least
elements, and everything a later chapter needs in order to *state* an order are
constructive, and only the search is not.
<!--zh-->
接下来有一个构造需要**选取**：本书末尾的选择公理要从一个族的每一格里挑出一个元素，而作出这个选取的经典方式，是把候选者良序化，再取合格者中最小的那个。

反射论证本来预期是第二个消费方，结果不是。它交付时根本没有用到任何序，而是一道阶梯，其极限一举为每个母式作答，是合起来造出来的、不是从中挑出来的。故这套词汇只有一个消费方、不是两个，那就是本书的最后一章 `L.Choice.Transversal`{.Agda}：下文那场搜索，正是从不交族的每一格里挑出一个点的那件东西。

本章提供相应的词汇。类型上的严格良序，是一个三歧、非自反、传递且良基的关系，打成 record，好让后续章节把它当数据携带。这个束的层级泛型有一点值得说明：载体与关系取**各自独立**的宇宙层级，因为第四部最终造出的那个序比较的是公式 (小的)，而据以比较的数据要提到序数 (不小)。

定理是：非空子集有极小元，且唯一。唯一性由三歧免费得到。存在性则不然：每一步都要判定「是否还有更小的合格者」，那恰是关于任意谓词的一次判定，故这是本书第二次花费排中律。与第一次不同，这里的代价换来的是一个真正的选择函数，而不是一次比较。

这个假设落在那一条定理上，而非落在整章上，而这件事只要做得到就值得做：束、极小元的唯一性，以及后续章节**陈述**一个序所需的一切，都是构造性的，唯有搜索不是。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.WellOrder.Base {ℓₚ : Level} where

open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.Relation.Nullary using ( ¬_; isProp¬ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Data.List using ( List; []; _∷_; length )
open import Cubical.Data.Nat using ( znots; snotz; injSuc; +-suc )
open import Cubical.Data.Nat.Order
  using ( _<_; _≤_; ≤-refl; ≤-trans; suc-≤-suc; pred-≤-pred; ¬-<-zero
        ; ≤-suc; isProp≤; zero-≤; <-trans; ¬m<m; <-wellfounded; Trichotomy; _≟_ )
open Trichotomy
```

<!--en-->
## Trichotomy, as data
<!--zh-->
## 作为数据的三歧
<!--/-->

<!--en-->
Three mutually exclusive alternatives, carried as an inductive type rather than
a nested sum, so that a proof can name the case it is in.
<!--zh-->
三个互斥的可能，以归纳类型而非嵌套的和类型携带，好让证明能点名自己所处的情形。
<!--/-->

```agda
data Tri {ℓ₁ ℓ₂ ℓ₃ : Level} (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃)
       : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)) where
  lt : A → Tri A B C
  eq : B → Tri A B C
  gt : C → Tri A B C
```

<!--en-->
## The bundle
<!--zh-->
## 束
<!--/-->

<!--en-->
The four laws, packaged. Well-foundedness is the library's accessibility
predicate, which is what makes the least-element search below terminate.
<!--zh-->
四条定律，打包起来。良基性取库的可及性谓词，正是它使下文取极小元的搜索得以终止。
<!--/-->

```agda
record SWO {ℓc : Level} (A : Type ℓc) : Type (ℓ-max ℓc (ℓ-suc ℓₚ)) where
  field
    _<∙_   : A → A → Type ℓₚ
    tri∙   : (a b : A) → Tri (a <∙ b) (a ≡ b) (b <∙ a)
    irr∙   : (a : A) → ¬ a <∙ a
    trans∙ : (a b c : A) → a <∙ b → b <∙ c → a <∙ c
    wf∙    : WellFounded _<∙_
```

<!--en-->
## Least elements
<!--zh-->
## 极小元
<!--/-->

<!--en-->
Being least for a predicate is satisfying it while nothing satisfying it is
strictly smaller. That is a proposition, and so is being *a* least element:
given two, trichotomy rules out both strict cases and leaves equality. This is
what lets the search below deliver an honest element out of a merely truncated
non-emptiness, since a proposition-valued goal absorbs the truncation.
<!--zh-->
对谓词而言的极小，指自身满足它，且没有满足它者严格更小。这是一个命题，而「是一个极小元」也是：给定两个，三歧排除两个严格情形，只留下相等。正是这一点使下面的搜索能从仅仅截断的非空性中交出一个诚实的元素，因为命题值的目标吸收截断。
<!--/-->

```agda
module _ {ℓc : Level} {A : Type ℓc} (w : SWO {ℓc} A) where
  open SWO w

  IsLeast : {ℓ'' : Level} → (A → hProp ℓ'') → A → Type (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
  IsLeast P a = ⟨ P a ⟩ × ((b : A) → ⟨ P b ⟩ → ¬ b <∙ a)

  isPropIsLeast : {ℓ'' : Level} (P : A → hProp ℓ'') (a : A) → isProp (IsLeast P a)
  isPropIsLeast P a = isProp× (snd (P a)) (isPropΠ λ b → isPropΠ λ _ → isProp¬ _)

  isPropLeastOf : {ℓ'' : Level} (P : A → hProp ℓ'')
                → isProp (Σ[ a ∈ A ] IsLeast P a)
  isPropLeastOf P (m , pm , minm) (m' , pm' , minm') =
    Σ≡Prop (isPropIsLeast P) (decide (tri∙ m m'))
    where
    decide : Tri (m <∙ m') (m ≡ m') (m' <∙ m) → m ≡ m'
    decide (lt m<m') = Empty.rec (minm' m pm m<m')
    decide (eq e)    = e
    decide (gt m'<m) = Empty.rec (minm m' pm' m'<m)
```

<!--en-->
And the search. Start anywhere in the subset and descend: ask whether some
smaller element still satisfies the predicate; if one does, recurse into it,
which terminates because the relation is well founded; if none does, the current
element is least by definition. The question asked at each step is about an
arbitrary predicate, and that is where the excluded middle enters.
<!--zh-->
然后是搜索。从子集中任意一点出发向下走：问是否有更小的元素仍满足该谓词；若有，就递归进去，而这会终止，因为关系良基；若无，当前元素按定义即为极小。每一步所问的问题关乎任意谓词，排中律正是从那里进入的。
<!--/-->

```agda
  leastOf : {ℓ'' : Level} → LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
          → (P : A → hProp ℓ'')
          → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ A ] IsLeast P a
  leastOf {ℓ''} lem P =
    PT.rec (isPropLeastOf P) (λ { (a₀ , pa₀) → go a₀ (wf∙ a₀) pa₀ })
    where
    go : (a : A) → Acc _<∙_ a → ⟨ P a ⟩ → Σ[ m ∈ A ] IsLeast P m
    go a (acc rs) pa = decide (lem (Smaller , squash₁))
      where
      Smaller : Type (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
      Smaller = ∥ Σ[ b ∈ A ] ((b <∙ a) × ⟨ P b ⟩) ∥₁
      decide : Smaller ⊎ (Smaller → Empty.⊥) → Σ[ m ∈ A ] IsLeast P m
      decide (inl q) = PT.rec (isPropLeastOf P)
        (λ { (b , (b<a , pb)) → go b (rs b b<a) pb }) q
      decide (inr ¬q) = a , (pa , λ b pb b<a → ¬q ∣ b , (b<a , pb) ∣₁)
```

<!--en-->
## Combinators
<!--zh-->
## 组合子
<!--/-->

<!--en-->
Later chapters assemble their orders rather than invent them: an order on a
structured type is built from orders on its ingredients, layer by layer. This
section is the kit. Its first piece is a consequence of trichotomy: a
refutation in each direction is already an equality. It is stated once for the
bundle, because the lexicographic product below leans on it twice.
<!--zh-->
后续章节是在组装序，而不是从无到有地发明序：结构化类型上的序由其成分上的序一层层造出。本节就是那套配件。第一件是三歧的一个推论：两个方向各一个反驳，就已经是一个相等。它对束只陈述一次，因为下文的字典积要两次倚仗它。
<!--/-->

```agda
connex : {ℓc : Level} {A : Type ℓc} (w : SWO A) (a b : A)
       → ¬ SWO._<∙_ w a b → ¬ SWO._<∙_ w b a → a ≡ b
connex w a b ¬ab ¬ba with SWO.tri∙ w a b
... | lt h = Empty.rec (¬ab h)
... | eq p = p
... | gt h = Empty.rec (¬ba h)
```

<!--en-->
The ground orders. The numbers carry their usual order, with the relation
lifted to this chapter's relation level; the one-point type carries the empty
order. For the former, trichotomy and well-foundedness are library facts,
lifted; for the latter there is nothing to compare, and the four laws hold
vacuously.
<!--zh-->
两个地面序。自然数带其通常的序，关系提升到本章的关系层级；单点类型带空序。前者的三歧与良基是库中现成的事实，提升即得；后者无物可比，四条定律皆空洞成立。
<!--/-->

```agda
natSWO : SWO ℕ
natSWO = record
  { _<∙_   = _≺ᴺ_
  ; tri∙   = triᴺ
  ; irr∙   = λ m h → ¬m<m (lower h)
  ; trans∙ = λ m n k h h' → lift (<-trans (lower h) (lower h'))
  ; wf∙    = wfᴺ }
  where
  _≺ᴺ_ : ℕ → ℕ → Type ℓₚ
  m ≺ᴺ n = Lift {ℓ-zero} {ℓₚ} (m < n)

  triᴺ : (m n : ℕ) → Tri (m ≺ᴺ n) (m ≡ n) (n ≺ᴺ m)
  triᴺ m n with m ≟ n
  ... | lt h = lt (lift h)
  ... | eq p = eq p
  ... | gt h = gt (lift h)

  wfᴺ : WellFounded _≺ᴺ_
  wfᴺ n = go n (<-wellfounded n)
    where
    go : (m : ℕ) → Acc _<_ m → Acc _≺ᴺ_ m
    go m (acc r) = acc λ k h → go k (r k (lower h))

unitSWO : {ℓc : Level} → SWO (Unit* {ℓc})
unitSWO = record
  { _<∙_   = λ _ _ → ⊥* {ℓₚ}
  ; tri∙   = λ a b → eq refl
  ; irr∙   = λ a h → Empty.rec* h
  ; trans∙ = λ a b c h _ → Empty.rec* h
  ; wf∙    = λ a → acc (λ b h → Empty.rec* h) }
```

<!--en-->
Two ways of stacking. A sum puts everything on the left below everything on the
right, and each summand keeps its own order. A product compares
lexicographically, first component first. One point of care: the bundle fixes
its relation's level, and an equality of first components lives at the
carrier's level instead, which the statement cannot afford; so the second
clause of the lexicographic relation carries two refutations rather than the
equality, and `connex`{.Agda} converts whenever the equality itself is owed.
Well-foundedness of the product is a nested descent: an outer induction on the
first accessibility, an inner induction on the second, with the equal-keys case
transported along the recovered path rather than descended into.
<!--zh-->
两种叠放方式。和把左侧的一切放在右侧的一切之下，两个加项各保各的序。积按字典序比较，先比第一分量。有一处要小心：束固定了关系的层级，而第一分量的相等落在载体的层级上，陈述负担不起；于是字典关系的第二支携带两个反驳而非那个相等，等到确实欠下相等时由 `connex`{.Agda} 兑换。积的良基性是一场嵌套下降：外层对第一个可及性归纳，内层对第二个归纳，键相等的情形沿兑换出的道路搬运结果、而不递归进去。
<!--/-->

```agda
module _ {ℓx ℓy : Level} {X : Type ℓx} {Y : Type ℓy} (u : SWO X) (v : SWO Y) where
  private
    module U = SWO u
    module V = SWO v

    _≺⊎_ : X ⊎ Y → X ⊎ Y → Type ℓₚ
    inl a ≺⊎ inl b = a U.<∙ b
    inl a ≺⊎ inr b = Unit* {ℓₚ}
    inr a ≺⊎ inl b = ⊥* {ℓₚ}
    inr a ≺⊎ inr b = a V.<∙ b

    tri⊎ : (s t : X ⊎ Y) → Tri (s ≺⊎ t) (s ≡ t) (t ≺⊎ s)
    tri⊎ (inl a) (inl b) with U.tri∙ a b
    ... | lt h = lt h
    ... | eq p = eq (cong inl p)
    ... | gt h = gt h
    tri⊎ (inl a) (inr b) = lt tt*
    tri⊎ (inr a) (inl b) = gt tt*
    tri⊎ (inr a) (inr b) with V.tri∙ a b
    ... | lt h = lt h
    ... | eq p = eq (cong inr p)
    ... | gt h = gt h

    irr⊎ : (s : X ⊎ Y) → ¬ s ≺⊎ s
    irr⊎ (inl a) h = U.irr∙ a h
    irr⊎ (inr a) h = V.irr∙ a h

    trans⊎ : (s t r : X ⊎ Y) → s ≺⊎ t → t ≺⊎ r → s ≺⊎ r
    trans⊎ (inl a) (inl b) (inl c) h h' = U.trans∙ a b c h h'
    trans⊎ (inl a) (inl b) (inr c) h h' = tt*
    trans⊎ (inl a) (inr b) (inl c) h h' = Empty.rec* h'
    trans⊎ (inl a) (inr b) (inr c) h h' = tt*
    trans⊎ (inr a) (inl b) r h h' = Empty.rec* h
    trans⊎ (inr a) (inr b) (inl c) h h' = Empty.rec* h'
    trans⊎ (inr a) (inr b) (inr c) h h' = V.trans∙ a b c h h'

    accInl : (a : X) → Acc U._<∙_ a → Acc _≺⊎_ (inl a)
    accInl a (acc r) = acc λ where
      (inl b) h → accInl b (r b h)
      (inr b) h → Empty.rec* h

    accInr : (b : Y) → Acc V._<∙_ b → Acc _≺⊎_ (inr b)
    accInr b (acc r) = acc λ where
      (inl a) h → accInl a (U.wf∙ a)
      (inr b') h → accInr b' (r b' h)

  sumSWO : SWO (X ⊎ Y)
  sumSWO = record
    { _<∙_   = _≺⊎_
    ; tri∙   = tri⊎
    ; irr∙   = irr⊎
    ; trans∙ = trans⊎
    ; wf∙    = λ where
        (inl a) → accInl a (U.wf∙ a)
        (inr b) → accInr b (V.wf∙ b) }
```

```agda
  private
    _≺×_ : X × Y → X × Y → Type ℓₚ
    (a , x) ≺× (b , y) =
      (a U.<∙ b) ⊎ ((¬ (a U.<∙ b)) × (¬ (b U.<∙ a)) × (x V.<∙ y))

    stall : {a b : X} → a ≡ b → (¬ (a U.<∙ b)) × (¬ (b U.<∙ a))
    stall {a} {b} p =
        (λ h → U.irr∙ b (subst (λ z → z U.<∙ b) p h))
      , (λ h → U.irr∙ b (subst (λ z → b U.<∙ z) p h))

    tri× : (s t : X × Y) → Tri (s ≺× t) (s ≡ t) (t ≺× s)
    tri× (a , x) (b , y) with U.tri∙ a b
    ... | lt h = lt (inl h)
    ... | gt h = gt (inl h)
    ... | eq p with V.tri∙ x y
    ... | lt h = lt (inr (fst (stall p) , snd (stall p) , h))
    ... | eq q = eq (cong₂ _,_ p q)
    ... | gt h = gt (inr (fst (stall (sym p)) , snd (stall (sym p)) , h))

    irr× : (s : X × Y) → ¬ s ≺× s
    irr× (a , x) (inl h) = U.irr∙ a h
    irr× (a , x) (inr (_ , _ , h)) = V.irr∙ x h

    trans× : (s t r : X × Y) → s ≺× t → t ≺× r → s ≺× r
    trans× (a , x) (b , y) (c , z) (inl h) (inl h') =
      inl (U.trans∙ a b c h h')
    trans× (a , x) (b , y) (c , z) (inl h) (inr (¬bc , ¬cb , _)) =
      inl (subst (λ z' → a U.<∙ z') (connex u b c ¬bc ¬cb) h)
    trans× (a , x) (b , y) (c , z) (inr (¬ab , ¬ba , _)) (inl h') =
      inl (subst (λ z' → z' U.<∙ c) (sym (connex u a b ¬ab ¬ba)) h')
    trans× (a , x) (b , y) (c , z) (inr (¬ab , ¬ba , h)) (inr (¬bc , ¬cb , h')) =
      inr ( (λ k → ¬bc (subst (λ z' → z' U.<∙ c) (connex u a b ¬ab ¬ba) k))
          , (λ k → ¬cb (subst (λ z' → c U.<∙ z') (connex u a b ¬ab ¬ba) k))
          , V.trans∙ x y z h h' )

    accProd : (a : X) → Acc U._<∙_ a → (x : Y) → Acc V._<∙_ x → Acc _≺×_ (a , x)
    accProd a (acc ru) = inner
      where
      inner : (x : Y) → Acc V._<∙_ x → Acc _≺×_ (a , x)
      inner x (acc rv) = acc λ where
        (b , y) (inl h) → accProd b (ru b h) y (V.wf∙ y)
        (b , y) (inr (¬ba , ¬ab , h)) →
          subst (λ z → Acc _≺×_ (z , y)) (sym (connex u b a ¬ba ¬ab))
            (inner y (rv y h))

  prodSWO : SWO (X × Y)
  prodSWO = record
    { _<∙_   = _≺×_
    ; tri∙   = tri×
    ; irr∙   = irr×
    ; trans∙ = trans×
    ; wf∙    = λ where (a , x) → accProd a (U.wf∙ a) x (V.wf∙ x) }
```

<!--en-->
Lists, length-gated. The list order compares by length first, and only lists of
equal length are compared pointwise, head first, with the same two-refutations
discipline the product uses for equal first components. The length gate is
plain equality rather than a lifted pair of refutations, for a level reason:
the gate here is an equation in `ℕ`, whose paths are small, so the conjunction
of the gate with the pointwise order already lives at the relation's level,
whereas `prodSWO`{.Agda}'s first components live at the carrier's level and
cannot afford the equation. Well-foundedness is the same nested descent as the
product's, with the length playing the role of the outer accessibility: strong
induction on length, and inside each length class an induction on the head's
accessibility around an induction on the tail's, transporting the finished
accessibility along the recovered head equation rather than descending into it.
<!--zh-->
表，以长度作门。表的序先比长度，仅等长的表再逐点比较，头先行，等头的情形沿用积为相等第一分量所用的「两个反驳」纪律。长度门取普通的相等、而非一对提升的反驳，原因是层级的：这里的门是 `ℕ` 中的等式，其路径是小的，故门与逐点序的合取已落在关系的层级上；而 `prodSWO`{.Agda} 的第一分量住在载体的层级上，负担不起那条等式。良基性是与积相同的嵌套下降，只是长度扮演外层的可及性：对长度作强归纳，每个长度类内部，先对头的可及性归纳，再在其中对尾的可及性归纳，把做完的可及性沿还原出的头等式搬运、而不递归进去。
<!--/-->

```agda
module _ {ℓx : Level} {X : Type ℓx} (u : SWO X) where
  private
    module U = SWO u

    stall : {a b : X} → a ≡ b → (¬ (a U.<∙ b)) × (¬ (b U.<∙ a))
    stall {a} {b} p =
        (λ h → U.irr∙ b (subst (λ z → z U.<∙ b) p h))
      , (λ h → U.irr∙ b (subst (λ z → b U.<∙ z) p h))

    _≺ᵖ_ : List X → List X → Type ℓₚ
    [] ≺ᵖ _ = ⊥* {ℓₚ}
    (x ∷ xs) ≺ᵖ [] = ⊥* {ℓₚ}
    (x ∷ xs) ≺ᵖ (y ∷ ys) = (x U.<∙ y)
                          ⊎ ((¬ (x U.<∙ y)) × (¬ (y U.<∙ x)) × (xs ≺ᵖ ys))

    triP : (xs ys : List X) → length xs ≡ length ys
         → Tri (xs ≺ᵖ ys) (xs ≡ ys) (ys ≺ᵖ xs)
    triP [] [] _ = eq refl
    triP [] (y ∷ ys) q = Empty.rec (znots q)
    triP (x ∷ xs) [] q = Empty.rec (snotz q)
    triP (x ∷ xs) (y ∷ ys) q with U.tri∙ x y
    ... | lt h = lt (inl h)
    ... | gt h = gt (inl h)
    ... | eq e with triP xs ys (injSuc q)
    ...   | lt r = lt (inr (fst (stall e) , snd (stall e) , r))
    ...   | gt r = gt (inr (fst (stall (sym e)) , snd (stall (sym e)) , r))
    ...   | eq r = eq (cong₂ _∷_ e r)

    irrP : (xs : List X) → ¬ xs ≺ᵖ xs
    irrP [] p = Empty.rec* p
    irrP (x ∷ xs) (inl h) = U.irr∙ x h
    irrP (x ∷ xs) (inr (_ , _ , h)) = irrP xs h

    transP : (xs ys zs : List X) → xs ≺ᵖ ys → ys ≺ᵖ zs → xs ≺ᵖ zs
    transP [] ys zs p q = Empty.rec* p
    transP (x ∷ xs) [] zs p q = Empty.rec* p
    transP (x ∷ xs) (y ∷ ys) [] p q = Empty.rec* q
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inl p) (inl q) =
      inl (U.trans∙ x y z p q)
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inl p) (inr (¬yz , ¬zy , _)) =
      inl (subst (λ v → x U.<∙ v) (connex u y z ¬yz ¬zy) p)
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inr (¬xy , ¬yx , _)) (inl q) =
      inl (subst (λ v → v U.<∙ z) (sym (connex u x y ¬xy ¬yx)) q)
    transP (x ∷ xs) (y ∷ ys) (z ∷ zs) (inr (¬xy , ¬yx , p)) (inr (¬yz , ¬zy , q)) =
      inr ( (λ h → ¬yz (subst (λ v → v U.<∙ z) (connex u x y ¬xy ¬yx) h))
          , (λ h → ¬zy (subst (λ v → z U.<∙ v) (connex u x y ¬xy ¬yx) h))
          , transP xs ys zs p q )

    _≺ᴸ_ : List X → List X → Type ℓₚ
    xs ≺ᴸ ys = Lift {ℓ-zero} {ℓₚ} (length xs < length ys)
              ⊎ ((length xs ≡ length ys) × (xs ≺ᵖ ys))

    triL : (xs ys : List X) → Tri (xs ≺ᴸ ys) (xs ≡ ys) (ys ≺ᴸ xs)
    triL xs ys with length xs ≟ length ys
    ... | lt h = lt (inl (lift h))
    ... | gt h = gt (inl (lift h))
    ... | eq p with triP xs ys p
    ...   | lt r = lt (inr (p , r))
    ...   | eq r = eq r
    ...   | gt r = gt (inr (sym p , r))

    irrL : (xs : List X) → ¬ xs ≺ᴸ xs
    irrL xs (inl h) = ¬m<m (lower h)
    irrL xs (inr (_ , p)) = irrP xs p

    transL : (xs ys zs : List X) → xs ≺ᴸ ys → ys ≺ᴸ zs → xs ≺ᴸ zs
    transL xs ys zs (inl p) (inl q) = inl (lift (<-trans (lower p) (lower q)))
    transL xs ys zs (inl p) (inr (q , _)) =
      inl (lift (subst (λ k → length xs < k) q (lower p)))
    transL xs ys zs (inr (p , _)) (inl q) =
      inl (lift (subst (λ k → k < length zs) (sym p) (lower q)))
    transL xs ys zs (inr (p , r)) (inr (q , s)) =
      inr (p ∙ q , transP xs ys zs r s)

    <≤ : {m n : ℕ} → m < n → m ≤ n
    <≤ {zero} {n} h = zero-≤
    <≤ {suc m} {zero} h = Empty.rec (¬-<-zero h)
    <≤ {suc m} {suc n} h = suc-≤-suc (<≤ (pred-≤-pred h))

    module Class (n : ℕ) (below : (us : List X) → length us < n → Acc _≺ᴸ_ us) where

      BL : Type ℓx
      BL = Σ[ us ∈ List X ] (length us ≤ n)

      _≺ᵉ_ : BL → BL → Type ℓₚ
      p ≺ᵉ q = (length (p .fst) ≡ length (q .fst)) × (p .fst ≺ᵖ q .fst)

      tailB : (n : ℕ) (x : X) (xs : List X) → length (x ∷ xs) ≤ n → length xs ≤ n
      tailB zero    x xs (k , p) =
        Empty.rec (snotz (sym (+-suc k (length xs)) ∙ p))
      tailB (suc m) x xs (k , p) =
        ≤-suc (k , injSuc (sym (+-suc k (length xs)) ∙ p))

      accE : (k : ℕ) (p : BL) → length (p .fst) ≡ k → Acc _≺ᵉ_ p
      goE : (k : ℕ) (x : X) → Acc U._<∙_ x → (xs : List X) → length xs ≡ k
          → (b : length (x ∷ xs) ≤ n) → Acc _≺ᵉ_ (xs , tailB n x xs b)
          → Acc _≺ᵉ_ (x ∷ xs , b)

      accE zero ([] , b) q = acc λ where
        ([] , _) (le , p) → Empty.rec* p
        (y ∷ ys , _) (le , p) → Empty.rec* p
      accE zero (x ∷ xs , b) q = Empty.rec (snotz q)
      accE (suc k) ([] , b) q = acc λ where
        ([] , _) (le , p) → Empty.rec* p
        (y ∷ ys , _) (le , p) → Empty.rec* p
      accE (suc k) (x ∷ xs , b) q =
        goE k x (U.wf∙ x) xs (injSuc q) b
          (accE k (xs , tailB n x xs b) (injSuc q))

      goE k x (acc r) = inner
        where
        inner : (xs : List X) → length xs ≡ k
              → (b : length (x ∷ xs) ≤ n) → Acc _≺ᵉ_ (xs , tailB n x xs b)
              → Acc _≺ᵉ_ (x ∷ xs , b)
        inner xs lq b (acc rs) = acc (λ where
          ([] , _) (le , p) → Empty.rec* p
          (y ∷ ys , by) (le , inl x<y) →
            goE k y (r y x<y) ys (injSuc le ∙ lq) by
              (accE k (ys , tailB n y ys by) (injSuc le ∙ lq))
          (y ∷ ys , by) (le , inr (¬yx , ¬xy , tailp)) →
            let e = connex u x y ¬xy ¬yx
                by' = subst (λ z → length (z ∷ ys) ≤ n) e by
            in subst (λ q → Acc _≺ᵉ_ (y ∷ ys , q))
                 (isProp≤ by' by)
                 (subst (λ z → Acc _≺ᵉ_ (z ∷ ys , by')) e
                   (inner ys (injSuc le ∙ lq) by'
                     (rs (ys , tailB n x ys by')
                       (injSuc le , tailp)))))

      accL : (k : ℕ) (p : BL) → length (p .fst) < k → Acc _≺ᴸ_ (p .fst)
      accL zero p q = Empty.rec (¬-<-zero q)
      accL (suc k) p q = inner p (accE (length (p .fst)) p refl) q
        where
        inner : (p' : BL) → Acc _≺ᵉ_ p' → length (p' .fst) < suc k → Acc _≺ᴸ_ (p' .fst)
        inner p' (acc re) q' = acc step
          where
          step : (p'' : List X) → p'' ≺ᴸ p' .fst → Acc _≺ᴸ_ p''
          step p'' (inl len<) = below p'' (≤-trans (lower len<) (p' .snd))
          step p'' (inr (len≡ , edesc)) =
            inner (p'' , subst (λ m → m ≤ n) (sym len≡) (p' .snd))
              (re (p'' , subst (λ m → m ≤ n) (sym len≡) (p' .snd))
                 (len≡ , edesc))
              (subst (λ m → m < suc k) (sym len≡) q')

    accList : (n : ℕ) → (xs : List X) → length xs ≤ n → Acc _≺ᴸ_ xs
    accList = WFI.induction <-wellfounded outer
      where
      outer : (n : ℕ) → ((k : ℕ) → k < n → (xs : List X) → length xs ≤ k → Acc _≺ᴸ_ xs)
            → (xs : List X) → length xs ≤ n → Acc _≺ᴸ_ xs
      outer n ih xs b = C.accL (suc n) (xs , b) (suc-≤-suc b)
        where
        module C = Class n (λ us len< → ih (length us) len< us ≤-refl)

  listSWO : SWO (List X)
  listSWO = record
    { _<∙_   = _≺ᴸ_
    ; tri∙   = triL
    ; irr∙   = irrL
    ; trans∙ = transL
    ; wf∙    = λ xs → accList (length xs) xs ≤-refl }
```

<!--en-->
And pulling back. An injection into an ordered type induces an order on its
source: compare the images. Trichotomy's equality case is the one place
injectivity is spent, and accessibility transports backwards along the map with
no further argument.
<!--zh-->
最后是拉回。一个到带序型的单射在其源上诱导出一个序：比较像即可。三歧的相等情形是单射性唯一被花费的地方，而可及性沿映射向后搬运，无需更多论证。
<!--/-->

```agda
module _ {ℓx ℓy : Level} {X : Type ℓx} {Y : Type ℓy}
         (v : SWO Y) (f : X → Y) (inj : (a b : X) → f a ≡ f b → a ≡ b) where
  private
    module V = SWO v

    _≺ᶠ_ : X → X → Type ℓₚ
    a ≺ᶠ b = f a V.<∙ f b

    triᶠ : (a b : X) → Tri (a ≺ᶠ b) (a ≡ b) (b ≺ᶠ a)
    triᶠ a b with V.tri∙ (f a) (f b)
    ... | lt h = lt h
    ... | eq p = eq (inj a b p)
    ... | gt h = gt h

    accPull : (a : X) → Acc V._<∙_ (f a) → Acc _≺ᶠ_ a
    accPull a (acc r) = acc λ b h → accPull b (r (f b) h)

  pullSWO : SWO X
  pullSWO = record
    { _<∙_   = _≺ᶠ_
    ; tri∙   = triᶠ
    ; irr∙   = λ a h → V.irr∙ (f a) h
    ; trans∙ = λ a b c h h' → V.trans∙ (f a) (f b) (f c) h h'
    ; wf∙    = λ a → accPull a (V.wf∙ (f a)) }
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`SWO`{.Agda} bundles a strict well-order, and `leastOf`{.Agda} extracts the least
element of any non-empty subset, uniquely (`isPropLeastOf`{.Agda}). The bundle
is the interface the choice construction takes; it does not care which order it
is handed, which is why the chapter is generic. The excluded middle is spent
once, on the decision at each descent step, and the
level discipline (carrier and relation separately generic) is what will let the
order of Part 4 compare small things by large data. The combinator kit
(`natSWO`{.Agda}, `unitSWO`{.Agda}, `sumSWO`{.Agda}, `prodSWO`{.Agda},
`listSWO`{.Agda}, `pullSWO`{.Agda}, with `connex`{.Agda} as the exchange
lemma) closes the chapter: ground orders, the three ways of stacking (sum,
product, and the length-gated pointwise order on lists), and pull-back along an
injection, which is how a later chapter orders one type by picturing it inside
another.
<!--zh-->
`SWO`{.Agda} 把严格良序打成束，`leastOf`{.Agda} 取出任一非空子集的极小元，且唯一 (`isPropLeastOf`{.Agda})。这个束是选择构造取用的接口；它不在乎拿到的是哪个序，这正是本章泛型的原因。排中律花在一处，即每一步下降时的那次判定，且只记在那一条定理账上：此处其余一切都是构造性的。而层级纪律 (载体与关系各自泛型) 将使第四部的那个序能以大的数据去比较小的东西。组合子配件 (`natSWO`{.Agda}、`unitSWO`{.Agda}、`sumSWO`{.Agda}、`prodSWO`{.Agda}、`listSWO`{.Agda}、`pullSWO`{.Agda}，外加兑换引理 `connex`{.Agda}) 为本章收尾：地面序、三种叠放 (和、积，以及以长度为门的逐点表序)，以及沿单射的拉回，后者正是后面某章「把一个类型画进另一个类型里」为其排序的方式。
<!--/-->
