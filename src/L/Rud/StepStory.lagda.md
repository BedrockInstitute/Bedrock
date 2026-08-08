# The S-story's successor clause, generic

<!--en-->
The level-story kit hosts the shared clauses of the tower story at any
transitive carrier, and the level-sigma chapter supplies the strengthened
story at a rud carrier, with the one-way successor-value clause reading the
powerset relation. The S-story's own successor clause is different: at an
S-stage the successor value is not a powerset but the rudimentary step, the
sixteen-operation closure of the preceding value, and its object formula must
be written against the sixteen-operation graphs. The graph layer is a second
telescope here, not a fixed import, so the clause is independent of how the
graphs are supplied: the clause is generic over the carrier, its
transitivity, the step closure into the carrier, and the graph layer
(`L.Rud.StepGraph`{.Agda} is the tree's supplier), and any instantiator
that supplies those four pieces receives the successor clause, its object
formula, and the two-way decode. This is the shape the first-limit carve
consumes.
<!--zh-->
层故事子句套件在任何传递载体处托管塔故事的共享子句，层 sigma 章则在 rud 载体处交付加锐故事，其中单向后继值子句读的是幂集关系。S-故事自己的后继子句不同：在 S-阶段处，后继值不是幂集，而是初步函数步，即前一个值的十六运算闭包，于是其对象公式必须写在十六运算图之上。此处图层是第二重望远镜而非固定 import，故子句与诸图如何供给无关：子句对载体、载体传递性、进入载体的步闭包以及图层全部泛型化 (树中的供给方是 `L.Rud.StepGraph`{.Agda})，任何供齐这四件的实例化者都得到后继子句、其对象公式与双向解码。这正是第一个极限刻划所消费的形状。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible using ( isTransV )

module L.Rud.StepStory {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ)
  (C : V ℓ) (Ctr : isTransV C) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ∃̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Rud.Step {ℓ} lem A using ( Op16; Fof; step; step-out; step-in; step-in-self
  ; step-in-img; StepArm; arm-member; arm-self; arm-image; u'; u'-in; u-self-in )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module Kit = LevelKit C Ctr
open Kit public

-- perf: the embedded graph disjunction decodes through the book's renaming theorem
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ C)) {ℓ} {⟪ C ⟫} ι
```

<!--en-->
The clause module's telescope is the graph layer, exactly: the step closure
`stepSub` places step members in the carrier (the instantiator derives it
from the delivered values read, as the first-limit probe measured), the
sixteen-operation graphs `graphOf` with their two-way decodes, the
disjunction `bigOr` they fold into with its two-way decode, and the equality
frame `eqFrame` with its two-way decode, the layer the graphs are built
from. Nothing here mentions which carrier the layer is assembled at: the
formulas and the readers consume only the parameters, and the instantiation
happens at the consumer's carrier. The step membership of the clause is read
by the four floor-and-image disjuncts of the step atom, and the successor
pair is read by the bounded successor atom against the pair atom of the kit.
<!--zh-->
子句模块的望远镜就是图层本身，分毫不差：步闭包 `stepSub` 把 step 的成员放进载体 (实例化者从已交付的值读式导出它，正如第一个极限探针所测)，十六运算图 `graphOf` 连同双向解码，由它们折叠出的析取 `bigOr` 连同双向解码，以及图所由造的等词框架 `eqFrame` 连同双向解码。此处没有任何内容提及图层在哪个载体处装配：公式与读式只消费参数，实例化发生在消费方的载体处。子句的 step 隶属由步原子的四条地板与像析取读出，后继对则由有界后继原子配合套件的对原子读出。
<!--/-->

```agda
module Clause
  (stepSub : (c : S) → ⟨ c ∈ˢ C ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ C ⟩)
  (graphOf : Op16 → Formula ⟪ C ⟫ 3)
  (graph-out : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
               (y∈ : ⟨ y ∈ˢ C ⟩) → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → ⟨ ((b , b∈) ∷ (a , a∈) ∷ (y , y∈) ∷ []) ⊨ᵐ graphOf i ⟩
             → y ≡ Fof i a b)
  (graph-in : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩) → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
            → y ≡ Fof i a b
            → ⟨ ((b , b∈) ∷ (a , a∈) ∷ (y , y∈) ∷ []) ⊨ᵐ graphOf i ⟩)
  (bigOr : Formula ⟪ C ⟫ 3)
  (bigOr-in : (i : Op16) (δ : Vec SM 3) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ δ ⊨ᵐ bigOr ⟩)
  (bigOr-out : (δ : Vec SM 3) (R : hProp (ℓ-suc ℓ))
             → ((i : Op16) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ R ⟩)
             → ⟨ δ ⊨ᵐ bigOr ⟩ → ⟨ R ⟩)
  (eqFrame : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n) → Formula ⟪ C ⟫ n)
  (eqFrame-ok : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
                (δ : Vec SM n) (W : S)
              → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩ → ⟨ v ∈ˢ W ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
                 → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩)
              → ⟨ δ ⊨ᵐ eqFrame k M ⟩ ⟷ fst (lookup k δ) ≡ W)
  where

```

<!--en-->
The bounded successor atom is the kit's carrier-generic content: `k = sucV a`
means that `a` lies in `k`, that `a` is a subset of `k`, and that every
member of `k` is a member of `a` or `a` itself, all read boundedly. The kit
hosts the atom and its decode once; this chapter consumes them.
<!--zh-->
有界后继原子是套件的载体泛型内容：`k = sucV a` 意为 `a` 落在 `k` 里、`a` 是 `k` 的子集、且 `k` 的每个成员都是 `a` 的成员或 `a` 本身，全部有界地读出。套件一次托管该原子及其解码；本章消费它们。
<!--/-->

<!--en-->
The step atom reads membership in the step of a variable: variable zero is a
member of the step of the set at `c` when it is a member of that set, equal
to it, or an image value of two arguments each drawn from the set or the set
itself, the three arms of the delivered step characterization. The
sixteen-way graph disjunction enters at the first three variable slots, so
the embedding is the identity renaming and the book's renaming theorem is
its decode. The membership direction is the step's three arms read back
through the graph decodes, and the reverse direction is the same three arms
read forward, each truncated branch a named function with a written type.
<!--zh-->
步原子读「属于某变量的 step」：变量零属于 `c` 处集合的 step，当它属于该集合、等于该集合、或是由两个各取自该集合或该集合自身的实参造出的像值，即已交付 step 刻画的三臂。十六路图析取恰好落在前三个变量槽，于是嵌入就是恒等改名，本书的改名定理就是它的解码。隶属方向把 step 的三臂经图解码读回，反向把同一三臂向前读，每条截断分支都是带书面类型的具名函数。
<!--/-->

```agda
  emb : (n : ℕ) → Fin 3 → Fin (suc (suc (suc n)))
  emb n zero = zero
  emb n (suc zero) = suc zero
  emb n (suc (suc zero)) = suc (suc zero)

  bigOr-ren : {n : ℕ} → Formula ⟪ C ⟫ (suc (suc (suc n)))
  bigOr-ren {n} = renameFo (emb n) bigOr

  bigOr-ren-ok : {n : ℕ} (bm am vm : SM) (δ : Vec SM n)
               → ⟨ (bm ∷ am ∷ vm ∷ δ) ⊨ᵐ bigOr-ren {n} ⟩
               ⟷ ⟨ (bm ∷ am ∷ vm ∷ []) ⊨ᵐ bigOr ⟩
  bigOr-ren-ok {n} bm am vm δ = (out , bwd)
    where
    ag : Ren.Agrees (emb n) (bm ∷ am ∷ vm ∷ δ) (bm ∷ am ∷ vm ∷ [])
    ag zero = refl
    ag (suc zero) = refl
    ag (suc (suc zero)) = refl
    out : ⟨ (bm ∷ am ∷ vm ∷ δ) ⊨ᵐ bigOr-ren {n} ⟩ → ⟨ (bm ∷ am ∷ vm ∷ []) ⊨ᵐ bigOr ⟩
    out h = subst (λ R → ⟨ R ⟩)
      (Ren.⊨-rename (emb n) bigOr (bm ∷ am ∷ vm ∷ δ) (bm ∷ am ∷ vm ∷ []) ag) h
    bwd : ⟨ (bm ∷ am ∷ vm ∷ []) ⊨ᵐ bigOr ⟩ → ⟨ (bm ∷ am ∷ vm ∷ δ) ⊨ᵐ bigOr-ren {n} ⟩
    bwd h = subst (λ R → ⟨ R ⟩)
      (sym (Ren.⊨-rename (emb n) bigOr (bm ∷ am ∷ vm ∷ δ) (bm ∷ am ∷ vm ∷ []) ag)) h

  inU : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  inU j t = (var t ∈̇ var j) ∨̇ (var t ≐ var j)

  inU-in : {n : ℕ} (j t : Fin n) (δ : Vec SM n)
         → (⟨ fst (lookup t δ) ∈ˢ fst (lookup j δ) ⟩ ⊎ (fst (lookup t δ) ≡ fst (lookup j δ)))
         → ⟨ δ ⊨ᵐ inU j t ⟩
  inU-in j t δ (inl m) = ∣ inl m ∣₁
  inU-in j t δ (inr e) = ∣ inr e ∣₁

  inU-out : {n : ℕ} (j t : Fin n) (δ : Vec SM n)
          → ⟨ δ ⊨ᵐ inU j t ⟩ → ∥ (⟨ fst (lookup t δ) ∈ˢ fst (lookup j δ) ⟩
               ⊎ (fst (lookup t δ) ≡ fst (lookup j δ))) ∥₁
  inU-out j t δ h = h

  imgBody : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc (suc (suc n)))
  imgBody {n} c = inU (suc (suc (suc c))) (suc zero)
               ∧̇ (inU (suc (suc (suc c))) zero ∧̇ bigOr-ren {n})

  imgForm : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n)
  imgForm {n} c = ∃̇ (∃̇ (imgBody {n} c))

  stepMem : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n)
  stepMem {n} c = inU (suc c) zero ∨̇ imgForm {n} c

  stepMem-ok : {n : ℕ} (c : Fin n) (δ : Vec SM (suc n))
             → ⟨ δ ⊨ᵐ stepMem c ⟩
             ⟷ ⟨ fst (lookup zero δ) ∈ˢ step (fst (lookup (suc c) δ)) ⟩
  stepMem-ok {n} c (vm ∷ δₙ) = (out , bwd)
    where
    v u : S
    v = fst vm
    u = fst (lookup c δₙ)
    u∈C : ⟨ u ∈ˢ C ⟩
    u∈C = snd (lookup c δₙ)
    argIn : (x : S) → (⟨ x ∈ˢ u ⟩ ⊎ (x ≡ u)) → ⟨ x ∈ˢ C ⟩
    argIn x (inl h) = Ctr {x = u} {y = x} h u∈C
    argIn x (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) u∈C
    argIn' : (x : S) → (⟨ x ∈ˢ u ⟩ ⊎ (x ≡ u)) → ⟨ x ∈ˢ u' u ⟩
    argIn' x (inl h) = u'-in u x h
    argIn' x (inr e) = subst (λ w → ⟨ w ∈ˢ u' u ⟩) (sym e) (u-self-in u)
    valueSub : (i : Op16) (a b : S) → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u))
             → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u)) → (w : S) → ⟨ w ∈ˢ Fof i a b ⟩ → ⟨ w ∈ˢ C ⟩
    valueSub i a b sa sb w hw = Ctr {x = Fof i a b} {y = w} hw (stepSub u u∈C
      (Fof i a b) (step-in-img u (Fof i a b) i a b (argIn' a sa) (argIn' b sb) refl))
    out : ⟨ (vm ∷ δₙ) ⊨ᵐ stepMem c ⟩ → ⟨ v ∈ˢ step u ⟩
    out h = PT.rec (snd (v ∈ˢ step u)) branch h
      where
      img : ⟨ (vm ∷ δₙ) ⊨ᵐ imgForm {n} c ⟩ → ⟨ v ∈ˢ step u ⟩
      img hi = PT.rec (snd (v ∈ˢ step u)) k0 hi
        where
        k0 : Σ[ am ∈ SM ] ⟨ (am ∷ vm ∷ δₙ) ⊨ᵐ ∃̇ (imgBody {n} c) ⟩ → ⟨ v ∈ˢ step u ⟩
        k0 (am , h1) = PT.rec (snd (v ∈ˢ step u)) k1 h1
          where
          k1 : Σ[ bm ∈ SM ] ⟨ (bm ∷ am ∷ vm ∷ δₙ) ⊨ᵐ imgBody {n} c ⟩ → ⟨ v ∈ˢ step u ⟩
          k1 (bm , (ha , (hb , hor))) =
            PT.rec (snd (v ∈ˢ step u)) k2
              (inU-out (suc (suc (suc c))) (suc zero) (bm ∷ am ∷ vm ∷ δₙ) ha)
            where
            k2 : (⟨ fst am ∈ˢ u ⟩ ⊎ (fst am ≡ u)) → ⟨ v ∈ˢ step u ⟩
            k2 sa = PT.rec (snd (v ∈ˢ step u)) k3
              (inU-out (suc (suc (suc c))) zero (bm ∷ am ∷ vm ∷ δₙ) hb)
              where
              k3 : (⟨ fst bm ∈ˢ u ⟩ ⊎ (fst bm ≡ u)) → ⟨ v ∈ˢ step u ⟩
              k3 sb = bigOr-out (bm ∷ am ∷ vm ∷ []) (v ∈ˢ step u) k4
                (bigOr-ren-ok {n} bm am vm δₙ .fst hor)
                where
                k4 : (i : Op16) → ⟨ (bm ∷ am ∷ vm ∷ []) ⊨ᵐ graphOf i ⟩ → ⟨ v ∈ˢ step u ⟩
                k4 i hg = step-in-img u v i (fst am) (fst bm) (argIn' (fst am) sa)
                  (argIn' (fst bm) sb) (graph-out i (fst bm) (fst am) v (snd bm) (snd am)
                    (snd vm) (valueSub i (fst am) (fst bm) sa sb) hg)
      branch : (⟨ (vm ∷ δₙ) ⊨ᵐ inU (suc c) zero ⟩ ⊎ ⟨ (vm ∷ δₙ) ⊨ᵐ imgForm {n} c ⟩)
             → ⟨ v ∈ˢ step u ⟩
      branch (inl hf) = PT.rec (snd (v ∈ˢ step u)) floor (inU-out (suc c) zero (vm ∷ δₙ) hf)
        where
        floor : (⟨ v ∈ˢ u ⟩ ⊎ (v ≡ u)) → ⟨ v ∈ˢ step u ⟩
        floor (inl m) = step-in u v m
        floor (inr e) = subst (λ w → ⟨ w ∈ˢ step u ⟩) (sym e) (step-in-self u)
      branch (inr hb) = img hb
    bwd : ⟨ v ∈ˢ step u ⟩ → ⟨ (vm ∷ δₙ) ⊨ᵐ stepMem c ⟩
    bwd h = PT.rec (snd ((vm ∷ δₙ) ⊨ᵐ stepMem c)) go (step-out u v h)
      where
      go : StepArm u v → ⟨ (vm ∷ δₙ) ⊨ᵐ stepMem c ⟩
      go (arm-member m) = ∣ inl (inU-in (suc c) zero (vm ∷ δₙ) (inl m)) ∣₁
      go (arm-self e) = ∣ inl (inU-in (suc c) zero (vm ∷ δₙ) (inr e)) ∣₁
      go (arm-image i a b sa sb e) = ∣ inr ∣ am , ∣ bm , (ha , (hb , hor)) ∣₁ ∣₁ ∣₁
        where
        am bm : SM
        am = PK.pt a (argIn a sa)
        bm = PK.pt b (argIn b sb)
        ha : ⟨ (bm ∷ am ∷ vm ∷ δₙ) ⊨ᵐ inU (suc (suc (suc c))) (suc zero) ⟩
        ha = inU-in (suc (suc (suc c))) (suc zero) (bm ∷ am ∷ vm ∷ δₙ) sa
        hb : ⟨ (bm ∷ am ∷ vm ∷ δₙ) ⊨ᵐ inU (suc (suc (suc c))) zero ⟩
        hb = inU-in (suc (suc (suc c))) zero (bm ∷ am ∷ vm ∷ δₙ) sb
        hor : ⟨ (bm ∷ am ∷ vm ∷ δₙ) ⊨ᵐ bigOr-ren {n} ⟩
        hor = bigOr-ren-ok {n} bm am vm δₙ .snd
          (bigOr-in i (bm ∷ am ∷ vm ∷ [])
            (graph-in i (fst bm) (fst am) v (snd bm) (snd am) (snd vm)
              (valueSub i (fst am) (fst bm) sa sb) e))
```

<!--en-->
The clause's conclusion reads `b ≡ step c` as the equality frame: `b` is
the set of exactly the members of the step of `c`, and the frame's two-way
decode together with the step atom's two-way decode give the equality both
ways.
<!--zh-->
子句的结论把 `b ≡ step c` 读作等词框架：`b` 恰好是 `c` 之 step 的成员之集，框架的双向解码连同步原子的双向解码两头给出等式。
<!--/-->

```agda
  stepEq : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  stepEq k c = eqFrame k (stepMem c)

  stepEq-ok : {n : ℕ} (k c : Fin n) (δ : Vec SM n)
            → ⟨ δ ⊨ᵐ stepEq k c ⟩
            ⟷ (fst (lookup k δ) ≡ step (fst (lookup c δ)))
  stepEq-ok {n} k c δ = (out , bwd)
    where
    B U : S
    B = fst (lookup k δ)
    U = fst (lookup c δ)
    U∈C : ⟨ U ∈ˢ C ⟩
    U∈C = snd (lookup c δ)
    mout : (v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ stepMem c ⟩ → ⟨ v ∈ˢ step U ⟩
    mout v v∈ m = stepMem-ok c ((v , v∈) ∷ δ) .fst m
    min : (v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ step U ⟩ → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ stepMem c ⟩
    min v v∈ s = stepMem-ok c ((v , v∈) ∷ δ) .snd s
    out : ⟨ δ ⊨ᵐ stepEq k c ⟩ → B ≡ step U
    out h = (eqFrame-ok k (stepMem c) δ (step U) (stepSub U U∈C) mout min) .fst h
    bwd : B ≡ step U → ⟨ δ ⊨ᵐ stepEq k c ⟩
    bwd e = (eqFrame-ok k (stepMem c) δ (step U) (stepSub U U∈C) mout min) .snd e
```

<!--en-->
The clause itself is the one-way successor-value clause, values for present
pairs only: if `pr a c` lies in `f` and `pr (sucV a) b` lies in `f`, then
`b` is the rud step of `c`. The kit hosts this clause once: the module
`OneWaySucc` takes the conclusion relation, its object formula and its
decode, and this chapter instantiates it at the step equality atom. The
object formula binds the three quantifiers around the antecedent pair read
and the conclusion, with the successor pair read through the kit's bounded
successor atom against the kit's pair atom, exactly the shape the level-sigma
chapter's one-way clause uses with the powerset atom in place of the step
equality. The decode walks the three quantifiers in each direction.
<!--zh-->
子句本身就是单向后继值子句，只为已现之对给值：若 `pr a c` 落在 `f` 里且 `pr (sucV a) b` 落在 `f` 里，则 `b` 是 `c` 的初步函数步。套件一次托管这条子句：模块 `OneWaySucc` 取结论关系、其对象公式及其解码，本章在步等式原子处实例化它。对象公式把三个量词绕前件对读与结论装配起来，后继对经套件的有界后继原子配合套件的对原子读出，恰是层 sigma 章单向子句以幂集原子替下步等式所用的形状。解码在两个方向各走过三个量词。
<!--/-->

```agda
  -- The shared one-way clause at the step equality conclusion.
  module OneWay = Kit.OneWaySucc (λ b c → b ≡ step c) stepEq stepEq-ok

  succClause : S → Type (ℓ-suc ℓ)
  succClause = OneWay.succClause

  succConc : Formula ⟪ C ⟫ 5
  succConc = OneWay.succConc

  succBody : Formula ⟪ C ⟫ 5
  succBody = OneWay.succBody

  succForm : Formula ⟪ C ⟫ 2
  succForm = OneWay.succForm

  -- The one-way clause decodes both ways, through the step equality decode.
  succ-ok : (f : SM) (x : ⟪ C ⟫)
          → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ succForm ⟩ ⟷ succClause (fst f)
  succ-ok = OneWay.succ-ok
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the S-story's successor clause as an object formula
with its two-way decode, generic over the carrier, its transitivity, the
step closure and the graph layer. The bounded successor atom is the
kit's carrier-generic content, the step atom reads the step membership
through the embedded sixteen-way graph disjunction, and the clause
reassembles the one-way successor value shape the first-limit carve consumes.
The instantiator supplies the graphs, their disjunction and the equality
frame from the surviving step content, and the step closure from the values
read; nothing here names a concrete stage or graph body.
<!--zh-->
本章把 S-故事的后继子句作为对象公式连同双向解码交付，对载体、载体传递性、步闭包与图层全部泛型。有界后继原子是套件的载体泛型内容，步原子经嵌入的十六路图析取读 step 隶属，子句重新装配成第一个极限刻划所消费的单向后继值形状。实例化者从存活的步内容供给图、图的析取与等词框架，从值读式供给步闭包；此处没有任何内容点名具体的阶段或图体。
<!--/-->
