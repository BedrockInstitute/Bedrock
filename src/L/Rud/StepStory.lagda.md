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
open import L.Constructible using ( isTransV; IsOrd )

module L.Rud.StepStory {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ)
  (C : V ℓ) (Ctr : isTransV C) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Rud.Step {ℓ} lem A using ( Op16; Fof; step; step-out; step-in; step-in-self
  ; step-in-img; StepArm; arm-member; arm-self; arm-image; u'; u'-in; u-self-in )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ∈∈ₛ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; isLimit-not-zero; isLimit-not-succ; isSucc; predecessor-mem )
open import L.Rud.OrdBlocks {ℓ} lem using ( suc-⊆ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

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
The limit clause is the sixth clause of the S-story, the sibling of the
successor clause. The clause module takes no telescope: the meta-level
limit clause is defined here once, its statement names no carrier, and
the formulas and the decodes consume only the carrier, its transitivity
and the kit. The consumer instantiates the module at the witness carrier
and receives the limit clause, the limit atom, the union reading, the
clause formula and the two-way decode.
<!--zh-->
极限子句是 S-故事的第六条子句，是后继子句的姊妹。子句模块不取望远镜：元层极限子句在此只定义一次，其陈述不点名任何载体；公式与解码只消费载体、载体传递性与套件。实例化者在见证载体处实例化模块，便得到极限子句、极限原子、并读式、子句公式与双向解码。
<!--/-->

```agda
module Limit
  where

  -- The sixth clause, the limit clause: the value at a limit index is the
  -- pointwise union of the values below.  T128's meta statement, ported;
  -- nothing in it names a concrete carrier (src/ProbeT128.agda:143-147).
  limitClause : S → Type (ℓ-suc ℓ)
  limitClause f = (a b : S) → ⟨ isLimit a ⟩ → ⟨ pr a b ∈ˢ f ⟩
    → (z : S) → ⟨ z ∈ˢ b ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁

  -- The limit atom: the ordinal predicate, a member, and no successor
  -- top, the delivered limit predicate read at the small index (R-35).
  limAt : Formula ⟪ C ⟫ 4
  limAt = isOrdAt (suc zero)
       ∧̇ (∃̇∈ (var (suc zero)) (var zero ≐ var zero))
       ∧̇ (∀̇∈ (var (suc zero))
             (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero)))

  pairIn : Formula ⟪ C ⟫ 4
  pairIn = ∃̇∈ (var (suc (suc zero)))
             (PK.prAt zero (suc (suc zero)) (suc zero))

  inner7 : Formula ⟪ C ⟫ 7
  inner7 = ∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
             (PK.prAt zero (suc (suc zero)) (suc zero)
                ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero)))

  unionRHS : Formula ⟪ C ⟫ 5
  unionRHS = ∃̇∈ (var (suc (suc zero))) (∃̇ inner7)

  limitConc : Formula ⟪ C ⟫ 4
  limitConc = ∀̇ ( (var zero ∈̇ var (suc zero) ⇒̇ unionRHS)
               ∧̇ (unionRHS ⇒̇ var zero ∈̇ var (suc zero)) )

  limitBody : Formula ⟪ C ⟫ 4
  limitBody = (limAt ∧̇ pairIn) ⇒̇ limitConc

  limitForm : Formula ⟪ C ⟫ 2
  limitForm = ∀̇ (∀̇ limitBody)

  _⊆_ : S → S → Type (ℓ-suc ℓ)
  u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

  ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
  ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

  -- The limit characterization the atom decode rests on (T128's, ported):
  -- for an ordinal a, "every member has a member above it" is the
  -- not-a-successor half of the delivered limit predicate.
  noAbove→succ : (a ξ : S) → IsOrd a → ⟨ ξ ∈ˢ a ⟩
               → ((η : S) → ⟨ η ∈ˢ a ⟩ → ⟨ ξ ∈ˢ η ⟩ → Empty.⊥)
               → ⟨ isSucc a ⟩
  noAbove→succ a ξ ordA ξ∈a noAbove = (ξ , (mem-ord {A = a} ordA ξ ξ∈a , a≡sucξ))
    where
    a≡sucξ : sucV ξ ≡ a
    a≡sucξ = sym (ext-⊆ {a} {sucV ξ} a⊆suc sucξ⊆a)
      where
      a⊆suc : a ⊆ sucV ξ
      a⊆suc x x∈a = go (ord-tri x (mem-ord {A = a} ordA x x∈a)
                         ξ (mem-ord {A = a} ordA ξ ξ∈a))
        where
        go : Tri x ξ → ⟨ x ∈ˢ sucV ξ ⟩
        go (inl x∈ξ) = ∈sucV-inl {A = ξ} {x = x} x∈ξ
        go (inr (inl x≡ξ)) = subst (λ w → ⟨ w ∈ˢ sucV ξ ⟩) (sym x≡ξ) (self∈sucV ξ)
        go (inr (inr ξ∈x)) = Empty.rec (noAbove x x∈a ξ∈x)
      sucξ⊆a : sucV ξ ⊆ a
      sucξ⊆a = suc-⊆ {A = a} {x = ξ} ordA ξ∈a

  closedFromLim : (a : S) → ⟨ isLimit a ⟩
                → (ξ : S) → ⟨ ξ ∈ˢ a ⟩
                → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩ × ⟨ ξ ∈ˢ η ⟩) ∥₁
  closedFromLim a lim ξ ξ∈a = decide (lem (∥ P ∥₁ , squash₁))
    where
    P : Type (ℓ-suc ℓ)
    P = Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩ × ⟨ ξ ∈ˢ η ⟩)
    decide : ∥ P ∥₁ ⊎ (∥ P ∥₁ → Empty.⊥) → ∥ P ∥₁
    decide (inl h) = h
    decide (inr np) = Empty.rec
      (isLimit-not-succ a lim
        (noAbove→succ a ξ (isLimit-ord a lim) ξ∈a noAbove))
      where
      noAbove : (η : S) → ⟨ η ∈ˢ a ⟩ → ⟨ ξ ∈ˢ η ⟩ → Empty.⊥
      noAbove η η∈a ξ∈η = np ∣ η , (η∈a , ξ∈η) ∣₁

  nonemptyFromLim : (a : S) → ⟨ isLimit a ⟩ → ∥ Σ[ ξ ∈ S ] ⟨ ξ ∈ˢ a ⟩ ∥₁
  nonemptyFromLim a lim = decide (lem (∥ P ∥₁ , squash₁))
    where
    P : Type (ℓ-suc ℓ)
    P = Σ[ ξ ∈ S ] ⟨ ξ ∈ˢ a ⟩
    decide : ∥ P ∥₁ ⊎ (∥ P ∥₁ → Empty.⊥) → ∥ P ∥₁
    decide (inl h) = h
    decide (inr np) = Empty.rec
      (isLimit-not-zero a lim (empty→∅ (λ ξ ξ∈a → np ∣ ξ , ξ∈a ∣₁)))
      where
      empty→∅ : ((ξ : S) → ⟨ ξ ∈ˢ a ⟩ → Empty.⊥) → a ≡ ∅
      empty→∅ ne = ext-⊆ {a} {∅} subs sup
        where
        subs : (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ ∅ ⟩
        subs x x∈a = Empty.rec (ne x x∈a)
        sup : (x : S) → ⟨ x ∈ˢ ∅ ⟩ → ⟨ x ∈ˢ a ⟩
        sup x x∈∅ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))

  -- The limit atom's two-way decode at the carrier.
  limAt-ok : (δ : Vec SM 4) → ⟨ δ ⊨ᵐ limAt ⟩
           ⟷ ⟨ isLimit (fst (lookup (suc zero) δ)) ⟩
  limAt-ok δ = (out , bwd)
    where
    valA : S
    valA = fst (lookup (suc zero) δ)

    out : ⟨ δ ⊨ᵐ limAt ⟩ → ⟨ isLimit valA ⟩
    out (ord-sat , (ne-sat , cl-sat)) = ( ordA , nz , ns )
      where
      ordA : IsOrd valA
      ordA = isOrd-out (suc zero) δ ord-sat
      nz : (valA ≡ ∅) → Empty.⊥
      nz e = PT.rec Empty.isProp⊥ nzGo ne-sat
        where
        nzGo : Σ[ ξm ∈ SM ] (⟨ fst ξm ∈ˢ valA ⟩
                            × ⟨ (ξm ∷ δ) ⊨ᵐ (var zero ≐ var zero) ⟩)
             → Empty.⊥
        nzGo (ξm , (ξ∈A , _)) =
          ∅-empty (fst ξm)
            (∈∈ₛ {a = fst ξm} {b = ∅} .fst
              (subst (λ w → ⟨ fst ξm ∈ˢ w ⟩) e ξ∈A))
      ns : ⟨ isSucc valA ⟩ → Empty.⊥
      ns (β , ordβ , eq) = PT.rec Empty.isProp⊥ nsGo (cl-sat βm β∈a)
        where
        β∈a : ⟨ β ∈ˢ valA ⟩
        β∈a = predecessor-mem β valA eq
        β∈C : ⟨ β ∈ˢ C ⟩
        β∈C = Ctr {x = valA} {y = β} β∈a (snd (lookup (suc zero) δ))
        βm : SM
        βm = PK.pt β β∈C
        nsGo : Σ[ ηm ∈ SM ] (⟨ fst ηm ∈ˢ valA ⟩ × ⟨ β ∈ˢ fst ηm ⟩)
             → Empty.⊥
        nsGo (ηm , (η∈a , β∈η)) = Empty.rec* {A = Empty.⊥}
          (∈sucV-elim {A = β} {x = fst ηm} {P = Empty.⊥* {ℓ-suc ℓ}}
            (Empty.isProp⊥* {ℓ-suc ℓ})
            (subst (λ w → ⟨ fst ηm ∈ˢ w ⟩) (sym eq) η∈a) inβ inEq)
          where
          inβ : ⟨ fst ηm ∈ˢ β ⟩ → Empty.⊥* {ℓ-suc ℓ}
          inβ η∈β = lift (∈-irrefl β (ordβ .fst {x = fst ηm} {y = β} β∈η η∈β))
          inEq : fst ηm ≡ β → Empty.⊥* {ℓ-suc ℓ}
          inEq e' = lift (∈-irrefl β (subst (λ w → ⟨ β ∈ˢ w ⟩) e' β∈η))

    bwd : ⟨ isLimit valA ⟩ → ⟨ δ ⊨ᵐ limAt ⟩
    bwd lim = ( ord-sat , (ne-sat , cl-sat) )
      where
      ordA : IsOrd valA
      ordA = isLimit-ord valA lim
      ord-sat : ⟨ δ ⊨ᵐ isOrdAt (suc zero) ⟩
      ord-sat = isOrd-in (suc zero) δ ordA
      ne-sat : ⟨ δ ⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero) ⟩
      ne-sat = PT.rec (snd (δ ⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero)))
        go (nonemptyFromLim valA lim)
        where
        go : Σ[ ξ ∈ S ] ⟨ ξ ∈ˢ valA ⟩
           → ⟨ δ ⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero) ⟩
        go (ξ , ξ∈a) = ∣ ξm , (ξ∈a , refl) ∣₁
          where
          ξm : SM
          ξm = PK.pt ξ (Ctr {x = valA} {y = ξ} ξ∈a (snd (lookup (suc zero) δ)))
      cl-sat : ⟨ δ ⊨ᵐ ∀̇∈ (var (suc zero))
                  (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero)) ⟩
      cl-sat ξm ξ∈a = PT.rec
        (snd ((ξm ∷ δ) ⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                   (var (suc zero) ∈̇ var zero)))
        go (closedFromLim valA lim (fst ξm) ξ∈a)
        where
        go : Σ[ η ∈ S ] (⟨ η ∈ˢ valA ⟩ × ⟨ fst ξm ∈ˢ η ⟩)
           → ⟨ (ξm ∷ δ) ⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                 (var (suc zero) ∈̇ var zero) ⟩
        go (η , (η∈a , ξ∈η)) = ∣ ηm , (η∈a , ξ∈η) ∣₁
          where
          ηm : SM
          ηm = PK.pt η (Ctr {x = valA} {y = η} η∈a (snd (lookup (suc zero) δ)))

  -- The union reading's two-way decode at arity 5 (T128's, ported).
  unionRHS-ok : (δ : Vec SM 5) → ⟨ δ ⊨ᵐ unionRHS ⟩
    ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ fst (lookup (suc (suc zero)) δ) ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst (lookup (suc (suc (suc zero))) δ) ⟩
             × ⟨ fst (lookup zero δ) ∈ˢ w ⟩) ∥₁) ∥₁
  unionRHS-ok δ = (out , bwd)
    where
    valZ : S
    valZ = fst (lookup zero δ)
    valA : S
    valA = fst (lookup (suc (suc zero)) δ)
    valF : S
    valF = fst (lookup (suc (suc (suc zero))) δ)

    out : ⟨ δ ⊨ᵐ unionRHS ⟩
        → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
    out sat = PT.rec squash₁ step₁ sat
      where
      step₁ : Σ[ ξm ∈ SM ] (⟨ fst ξm ∈ˢ valA ⟩
            × ⟨ (ξm ∷ δ) ⊨ᵐ ∃̇ inner7 ⟩)
            → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                 × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
      step₁ (ξm , (ξ∈a , rest)) = PT.rec squash₁ step₂ rest
        where
        step₂ : Σ[ wm ∈ SM ] ⟨ (wm ∷ ξm ∷ δ) ⊨ᵐ inner7 ⟩
              → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                   × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
        step₂ (wm , wm-sat) = PT.rec squash₁ step₃ wm-sat
          where
          step₃ : Σ[ pm ∈ SM ] (⟨ fst pm ∈ˢ valF ⟩
                × ⟨ (pm ∷ wm ∷ ξm ∷ δ) ⊨ᵐ
                     (PK.prAt zero (suc (suc zero)) (suc zero)
                        ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero))) ⟩)
                → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                     × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
          step₃ (pm , (pm∈f , (pr-sat , z∈w-sat))) =
            ∣ fst ξm , ( ξ∈a , ∣ fst wm , ( prξw∈f , z∈w ) ∣₁ ) ∣₁
            where
            p≡prξw : fst pm ≡ pr (fst ξm) (fst wm)
            p≡prξw = PK.prAt-out zero (suc (suc zero)) (suc zero)
              (pm ∷ wm ∷ ξm ∷ δ) pr-sat
            prξw∈f : ⟨ pr (fst ξm) (fst wm) ∈ˢ valF ⟩
            prξw∈f = subst (λ t → ⟨ t ∈ˢ valF ⟩) p≡prξw pm∈f
            z∈w : ⟨ valZ ∈ˢ fst wm ⟩
            z∈w = z∈w-sat

    bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
        → ⟨ δ ⊨ᵐ unionRHS ⟩
    bwd h = PT.rec (snd (δ ⊨ᵐ unionRHS)) step₁ h
      where
      step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁)
            → ⟨ δ ⊨ᵐ unionRHS ⟩
      step₁ (ξ , (ξ∈a , rest)) = PT.rec (snd (δ ⊨ᵐ unionRHS)) step₂ rest
        where
        ξm : SM
        ξm = PK.pt ξ (Ctr {x = valA} {y = ξ} ξ∈a
          (snd (lookup (suc (suc zero)) δ)))
        step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩)
              → ⟨ δ ⊨ᵐ unionRHS ⟩
        step₂ (w , (pw∈f , z∈w)) = ∣ ξm , (ξ∈a , inner∃) ∣₁
          where
          w∈C : ⟨ w ∈ˢ C ⟩
          w∈C = PM.pair-right {a = ξ} {b = w}
            (Ctr {x = valF} {y = pr ξ w} pw∈f
              (snd (lookup (suc (suc (suc zero))) δ)))
          wm : SM
          wm = PK.pt w w∈C
          pr∈C : ⟨ pr ξ w ∈ˢ C ⟩
          pr∈C = Ctr {x = valF} {y = pr ξ w} pw∈f
            (snd (lookup (suc (suc (suc zero))) δ))
          pm : SM
          pm = PK.pt (pr ξ w) pr∈C
          pr-sat : ⟨ (pm ∷ wm ∷ ξm ∷ δ) ⊨ᵐ
                     PK.prAt zero (suc (suc zero)) (suc zero) ⟩
          pr-sat = PK.prAt-in zero (suc (suc zero)) (suc zero)
            (pm ∷ wm ∷ ξm ∷ δ) refl
          z∈w-sat : ⟨ (pm ∷ wm ∷ ξm ∷ δ) ⊨ᵐ
                      (var (suc (suc (suc zero))) ∈̇ var (suc zero)) ⟩
          z∈w-sat = z∈w
          inner : ⟨ (wm ∷ ξm ∷ δ) ⊨ᵐ inner7 ⟩
          inner = ∣ pm , (pw∈f , (pr-sat , z∈w-sat)) ∣₁
          inner∃ : ⟨ (ξm ∷ δ) ⊨ᵐ ∃̇ inner7 ⟩
          inner∃ = ∣ wm , inner ∣₁

  -- The sixth clause's two-way decode at the standing arity (T128's,
  -- ported): the object formula is satisfied exactly when the meta-level
  -- limit clause holds at the witness.
  limit-ok : (f : SM) (x : ⟪ C ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ limitForm ⟩
           ⟷ limitClause (fst f)
  limit-ok f x = (out , bwd)
    where
    δ₂ : Vec SM 2
    δ₂ = f ∷ ι x ∷ []

    out : ⟨ δ₂ ⊨ᵐ limitForm ⟩ → limitClause (fst f)
    out h a b lim ab∈f z = (fwd , bwd)
      where
      a∈C : ⟨ a ∈ˢ C ⟩
      a∈C = PM.pair-left {a = a} {b = b}
        (Ctr {x = fst f} {y = pr a b} ab∈f (snd f))
      b∈C : ⟨ b ∈ˢ C ⟩
      b∈C = PM.pair-right {a = a} {b = b}
        (Ctr {x = fst f} {y = pr a b} ab∈f (snd f))
      am : SM
      am = PK.pt a a∈C
      bm : SM
      bm = PK.pt b b∈C
      body-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitBody ⟩
      body-sat = h am bm
      conc-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitConc ⟩
      conc-sat = body-sat (limAt-sat , pairIn-sat)
        where
        limAt-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limAt ⟩
        limAt-sat = limAt-ok (bm ∷ am ∷ f ∷ ι x ∷ []) .snd lim
        pairIn-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ pairIn ⟩
        pairIn-sat = pair∈ (suc (suc zero)) (suc zero) zero
          (bm ∷ am ∷ f ∷ ι x ∷ []) .snd ab∈f
      fwd : ⟨ z ∈ˢ b ⟩
          → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
               × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
      fwd z∈b = unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .fst
        (conc-sat zm .fst z∈b)
        where
        z∈C : ⟨ z ∈ˢ C ⟩
        z∈C = Ctr {x = b} {y = z} z∈b b∈C
        zm : SM
        zm = PK.pt z z∈C
      bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
              × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
          → ⟨ z ∈ˢ b ⟩
      bwd hz = conc-sat zm .snd
        (unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .snd hz)
        where
        z∈C : ⟨ z ∈ˢ C ⟩
        z∈C = PT.rec (snd (z ∈ˢ C)) step₁ hz
          where
          step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                → ⟨ z ∈ˢ C ⟩
          step₁ (ξ , (ξ∈a , rest)) = PT.rec (snd (z ∈ˢ C)) step₂ rest
            where
            step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) → ⟨ z ∈ˢ C ⟩
            step₂ (w , (pw∈f , z∈w)) = Ctr {x = w} {y = z} z∈w w∈C
              where
              w∈C : ⟨ w ∈ˢ C ⟩
              w∈C = PM.pair-right {a = ξ} {b = w}
                (Ctr {x = fst f} {y = pr ξ w} pw∈f (snd f))
        zm : SM
        zm = PK.pt z z∈C

    bwd : limitClause (fst f) → ⟨ δ₂ ⊨ᵐ limitForm ⟩
    bwd lc am bm = body-sat
      where
      body-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitBody ⟩
      body-sat (limAt-sat , pairIn-sat) = conc-sat
        where
        lim : ⟨ isLimit (fst am) ⟩
        lim = limAt-ok (bm ∷ am ∷ f ∷ ι x ∷ []) .fst limAt-sat
        ab∈f : ⟨ pr (fst am) (fst bm) ∈ˢ fst f ⟩
        ab∈f = pair∈ (suc (suc zero)) (suc zero) zero
          (bm ∷ am ∷ f ∷ ι x ∷ []) .fst pairIn-sat
        conc-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitConc ⟩
        conc-sat zm = ( fwd , back )
          where
          fwd : ⟨ fst zm ∈ˢ fst bm ⟩
              → ⟨ (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ unionRHS ⟩
          fwd z∈b = unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .snd
            (lc (fst am) (fst bm) lim ab∈f (fst zm) .fst z∈b)
          back : ⟨ (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ unionRHS ⟩
               → ⟨ fst zm ∈ˢ fst bm ⟩
          back rhssat = lc (fst am) (fst bm) lim ab∈f (fst zm) .snd
            (unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .fst rhssat)

  limit-out : (f : SM) (x : ⟪ C ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ limitForm ⟩
            → limitClause (fst f)
  limit-out f x = limit-ok f x .fst

  limit-in : (f : SM) (x : ⟪ C ⟫) → limitClause (fst f)
           → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ limitForm ⟩
  limit-in f x = limit-ok f x .snd
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
read; nothing here names a concrete stage or graph body. The limit clause
is its sibling: the sixth clause's formula and its two-way decode live in
the same module shape, generic over the carrier, with the meta-level
clause defined once inside.
<!--zh-->
本章把 S-故事的后继子句作为对象公式连同双向解码交付，对载体、载体传递性、步闭包与图层全部泛型。有界后继原子是套件的载体泛型内容，步原子经嵌入的十六路图析取读 step 隶属，子句重新装配成第一个极限刻划所消费的单向后继值形状。实例化者从存活的步内容供给图、图的析取与等词框架，从值读式供给步闭包；此处没有任何内容点名具体的阶段或图体。极限子句是它的姊妹：第六条子句的公式与双向解码住在同一种模块形状里，对载体泛型，元层子句在模块内部只定义一次。
<!--/-->
