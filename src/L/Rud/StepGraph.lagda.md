# The graph layer of the rud step

<!--en-->
This is the fresh surviving home for the graph layer the rud step's consumers
read: the equality frame, the projection and slice frames, the sixteen
membership formulas at bound argument variables, and the sixteen-way
disjunction with its two-way decode. This block delivers the foundation only.
The decodes of the membership formulas, the dispatchers and the graphs arrive
in later blocks, and this chapter leaves their landing sites natural: every
name the consumers wire (`eqFrame`, `leftMem`, `sliceMem`, `bigOr`,
`mem0` to `mem15`) is delivered here in its final shape. Nothing here imports
the archived `StepInL`; every supplier survives (`L.Rud.Step`, `L.Rud.Images`,
`L.PairAtoms`, `L.LevelKit`, the `Base` hubs, and the `Cubical` hierarchy).
<!--zh-->
这是 rud step 诸消费者所读的图层的新存活家园：等词框架、投影与切片框架、受约束实参变量处的十六条隶属公式、以及带双向解码的十六路析取。本块只交付地基。隶属公式的解码、分派器与诸图在后续诸块到达，本章为它们留下自然的落点：消费者所接线的每个名字 (`eqFrame`、`leftMem`、`sliceMem`、`bigOr`、`mem0` 至 `mem15`) 都以此处的最终形状交付。此处不导入任何已归档的`StepInL`；每个供给方都存活 (`L.Rud.Step`、`L.Rud.Images`、`L.PairAtoms`、`L.LevelKit`、`Base` 枢纽、`Cubical` 层级)。
<!--ja-->
これは、rud step の消費者が読むグラフレイヤーの、存続する新しい家である。すなわち、等号フレーム、射影フレームとスライスフレーム、束縛された引数変数における十六個の帰属論理式、そして双方向復号を備えた十六路の論理和である。このブロックは土台のみを届ける。帰属論理式の復号、ディスパッチャ、そしてグラフは後のブロックで到着し、本章はそれらの着地点を自然なまま残す。消費者が結線する名前 (`eqFrame`、`leftMem`、`sliceMem`、`bigOr`、`mem0` から `mem15`) は、すべてここで最終形のまま届けられる。ここではアーカイブ済みの `StepInL` を何もインポートしない。供給者はすべて存続モジュールである
(`L.Rud.Step`、`L.Rud.Images`、`L.PairAtoms`、`L.LevelKit`、`Base` ハブ、`Cubical` 階層)。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module L.Rud.StepGraph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using
  ( isTransV; Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ; 𝒟ₒ-intro )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
open import L.PairAtoms {ℓ} using ( module PairMem )
open import L.Rud.Images {ℓ} using
  ( left; left-compute; right; ⋂; ⋂-member-in-all; right-nonpair
  ; F8; F8-spec; F10; F10-spec; F11; F12; F13; F14; left-spec; left-⋂-collapse
  ; left-⋂-empty; module F15Of )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12
  ; op13; op14; op15; Fof; Fof-f0; Fof-f1; Fof-f2; Fof-f3; Fof-f4; Fof-f5
  ; Fof-f6; Fof-f7; Fof-f8; Fof-f9; Fof-f10; Fof-f11; Fof-f12; Fof-f13
  ; Fof-f14; Fof-f15; F15A; isPair; right-at-pair; singl≡pair
  ; step; step-out; StepArm; arm-member; arm-self; arm-image
  ; step-in; step-in-self; step-in-img; u'; u'-in; u-self-in )
open import L.Rud.Ops {ℓ} using
  ( F0; F1; F2; F3; F4; F5; F6; F7; F9; F0-spec; F1-spec; F5-spec
  ; F2-read; F3-read; F4-read; F6-read; F7-read
  ; F2-write; F3-write; F4-write; F6-write; F7-write )
open import L.TowerKit {ℓ} lem A using
  ( ext-⊆; empty-⊆; Ltr; 𝒟ₒ⊆Lsuc; Lpair; ValuesInU; suc⁴; module F0Arm )
open import L.Rud.Describe {ℓ} using ( module F10Desc )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import Cubical.Data.FinData.Base using ( Fin )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr; rec )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Functions.Logic using ( ∃[]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The inner world, read directly

A definable subset of a stage is carved by a formula whose quantifiers range
over the stage itself, and that is the only reading used from here on.
Nothing below is Δ₀: the operator takes any formula at all, so the
descriptions may quantify without a bound, and the absoluteness machinery
never enters. What the reading needs is one frame, "this formula carves
exactly this set", stated with the environment spelled out and the membership
certificate carried beside the element.
<!--zh-->
## 直接读内层世界

一个阶段的可定义子集由一条公式刻出，其量词遍历该阶段自身，而自此以下只用这一种读法。以下没有任何 Δ₀ 的要求：算子接纳任意公式，故诸描述可以无界量化，绝对性机制一步也不进场。这套读法所需的只有一个框架，即「此公式恰好刻出此集」，其中环境逐项写明，隶属证书与元素并肩携带。
<!--ja-->
## 内部世界を直接読む

ある段階の可定義部分集合は、その量詞が段階自身を渡り歩く式によって刻まれる。以後は、その読みだけを使う。以下には Δ₀ の要請は一切ない。演算子は任意の式を受け入れるので、記述は束縛なしに量化でき、絶対性の機構は一歩も入らない。この読みが要るのはただ一つのフレーム、すなわち「この式がちょうどこの集合を刻む」であり、環境を明記し、帰属の証明書を要素のそばに携える。
<!--/-->

```agda
module Desc (C : S) (Ctr : isTransV C) where

  module K = LevelKit C Ctr
  open K public

  described : (Φ : Formula ⟪ C ⟫ 1) (W : S)
            → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
               → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ Φ ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ Φ ⟩
               → ⟨ v ∈ˢ W ⟩)
            → DefOf.defSet C Φ ≡ W
  described Φ W wsub din dout = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ DefOf.defSet C Φ ⟩ → ⟨ x ∈ˢ W ⟩
    sub x h = dout x x∈ sat
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = DefOf.defSet⊆A C Φ x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈
      sat : ⟨ (PK.pt x x∈ ∷ []) ⊨ᵐ Φ ⟩
      sat = subst (λ e → ⟨ (e ∷ []) ⊨ᵐ Φ ⟩)
        (Σ≡Prop (λ w → snd (w ∈ˢ C)) (fib .snd))
        (subst ⟨_⟩ (DefOf.defSet-mem C Φ (fib .fst))
          (subst (λ w → ⟨ w ∈ˢ DefOf.defSet C Φ ⟩) (sym (fib .snd)) h))
    sup : (x : S) → ⟨ x ∈ˢ W ⟩ → ⟨ x ∈ˢ DefOf.defSet C Φ ⟩
    sup x h = subst (λ w → ⟨ w ∈ˢ DefOf.defSet C Φ ⟩) (fib .snd)
      (subst ⟨_⟩ (sym (DefOf.defSet-mem C Φ (fib .fst)))
        (subst (λ e → ⟨ (e ∷ []) ⊨ᵐ Φ ⟩)
          (sym (Σ≡Prop (λ w → snd (w ∈ˢ C)) (fib .snd)))
          (din x x∈ h)))
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = wsub x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈
```

<!--en-->
## The layer, at a transitive carrier

The layer is assembled at a generic transitive carrier `C`, exactly the
telescope the probe and the archived `Slot` use. The slot `A` enters only
through the certificate `qA`; the empty-set membership `∅∈C` serves the later
blocks and sits here so the telescope never changes. The inner world at the
carrier is the level kit's (`SM` and `⊨ᵐ`), and the pair kit supplies the
point and the entry certificate.

The equality frame is the single place the layer argues extensionality:
`eqFrame k M` says the set at slot `k` is the set of exactly the members the
formula `M` describes, and the two directions of its decode are the two
inclusions. Every later frame and graph is this frame applied once.
<!--zh-->
## 图层，在传递载体处

图层在泛型传递载体 `C` 处装配，其望远镜与探针及已归档的 `Slot` 分毫不差。槽 `A` 只经证书 `qA` 进入；空集成员 `∅∈C` 供后续诸块使用，放在此处使望远镜永不再变。载体处的内层世界来自层级套件 (`SM` 与 `⊨ᵐ`)，对套件供给点与入口证书。

等词框架是图层唯一一处论证外延性：`eqFrame k M` 说 `k` 槽处的集合恰好是公式 `M` 所描述的那些成员之集，其解码的两个方向就是两条包含。其后的每个框架与图都是此框架应用一次。
<!--ja-->
## グラフレイヤー、推移的台において

グラフレイヤーは汎用の推移的台 `C` で組み立てられる。そのテレスコープは、プローブとアーカイブ済みの `Slot` が使うものと分毫も違わない。スロット `A`は証明書 `qA` を通してのみ入る。空集合の帰属 `∅∈C` は後続のブロックに備え、テレスコープが二度と変わらないようにここに置かれる。台における内部世界はレベルキットのもの (`SM` と `⊨ᵐ`) であり、ペアキットが点と入口証明書を供給する。

等号フレームは、グラフレイヤーが外延性を論じる唯一の場所である。`eqFrame k M` は、スロット `k` の集合が式 `M` の記述するメンバーからなる集合とちょうど一致することを言い、その復号の二つの方向は二つの包含である。後のフレームとグラフはすべて、このフレームを一度適用したものである。
<!--/-->

```agda
module Layer (C : S) (Ctr : isTransV C) (mA : ⟪ C ⟫)
             (qA : ⟪ C ⟫↪ mA ≡ A) (∅∈C : ⟨ ∅ ∈ˢ C ⟩) where

  module K = LevelKit C Ctr
  open K public

  private
    f0 : {n : ℕ} → Fin (suc n)
    f0 = zero
    f1 : {n : ℕ} → Fin (suc (suc n))
    f1 = suc f0
    f2 : {n : ℕ} → Fin (suc (suc (suc n)))
    f2 = suc f1
    f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
    f3 = suc f2
    f4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
    f4 = suc f3
    f5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
    f5 = suc f4

  mem : (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
  mem x y y∈x x∈C = Ctr {x = x} {y = y} y∈x x∈C

  eqFrame : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n) → Formula ⟪ C ⟫ n
  eqFrame k M = (∀̇∈ (var k) M) ∧̇ (∀̇ (M ⇒̇ (var f0 ∈̇ var (suc k))))

  eqFrame-out : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
                (δ : Vec SM n) (W : S)
              → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩
                 → ⟨ v ∈ˢ W ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
                 → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩)
              → ⟨ δ ⊨ᵐ eqFrame k M ⟩ → fst (lookup k δ) ≡ W
  eqFrame-out k M δ W wsub mout min (h₁ , h₂) = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ fst (lookup k δ) ⟩ → ⟨ x ∈ˢ W ⟩
    sub x h = mout x (PK.entry∈ k δ x h) (h₁ (PK.pt x (PK.entry∈ k δ x h)) h)
    sup : (x : S) → ⟨ x ∈ˢ W ⟩ → ⟨ x ∈ˢ fst (lookup k δ) ⟩
    sup x h = h₂ (PK.pt x (wsub x h)) (min x (wsub x h) h)

  eqFrame-in : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
               (δ : Vec SM n) (W : S)
             → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩
                → ⟨ v ∈ˢ W ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
                → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩)
             → fst (lookup k δ) ≡ W → ⟨ δ ⊨ᵐ eqFrame k M ⟩
  eqFrame-in k M δ W wsub mout min e = (part₁ , part₂)
    where
    part₁ : (xm : SM) → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
          → ⟨ (xm ∷ δ) ⊨ᵐ M ⟩
    part₁ xm h = min (fst xm) (snd xm)
      (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) e h)
    part₂ : (xm : SM) → ⟨ (xm ∷ δ) ⊨ᵐ M ⟩
          → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
    part₂ xm h = subst (λ t → ⟨ fst xm ∈ˢ t ⟩) (sym e)
      (mout (fst xm) (snd xm) h)

  eqFrame-ok : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
               (δ : Vec SM n) (W : S)
             → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩
                → ⟨ v ∈ˢ W ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
                → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩)
             → ⟨ δ ⊨ᵐ eqFrame k M ⟩ ⟷ fst (lookup k δ) ≡ W
  eqFrame-ok k M δ W wsub mout min =
    ( eqFrame-out k M δ W wsub mout min
    , eqFrame-in k M δ W wsub mout min )
```

<!--en-->
## The intersection, the union, and the two projections

The four tuple operations reach their arguments through the projections, which
are total: on a pair they are the two components, and off a pair they are junk.
The junk has to be described as exactly as the rest, and the left projection is
where the description is prettiest: `left b` is the union of the intersection
of `b` at **every** `b`, so one equality frame describes it with no case
analysis and no classical step. The intersection's own membership unfolds to
two clauses, "the candidate is the union of some member" and "the candidate
lies in every member", which is what the frame's body says. The right
projection keeps a case split, because off a pair it is the empty set by a
separate reading.
<!--zh-->
## 交、并，与两个投影

四个三元组运算经投影够到实参，而投影是全函数：在对上它们是两个分量，不在对上则是垃圾。垃圾必须描述得与其余部分一样精确，而左投影正是描述最漂亮之处：`left b` 在**每个** `b` 处都是 `b` 之交的并，故一个等词框架即可描述它，无须情形分析，也无须经典一步。交自身的隶属展开为两条子句，「候选者是某个成员之并」与「候选者落在每个成员之中」，这正是框架体所说的。右投影保留情形分裂，因为不在对上时它由另一条读引理给出空集。
<!--ja-->
## 交わり、合併、そして二つの射影

四つの三つ組演算は射影を通して引数に届く。射影は全関数である。対の上では二つの成分になり、対の外ではジャンクになる。ジャンクも他と同じくらい正確に記述しなければならない。左射影が最も美しい記述を持つ。`left b` は**すべての**`b` について、`b` の交わりの合併である。したがって、一つの等号フレームで場合分けも古典的一歩もなしに記述できる。交わり自身の所属は二つの節に展開される。「候補はあるメンバーの合併である」と「候補はすべてのメンバーの中にある」、それがフレームの本体の言うことである。右射影は場合分けを保つ。対の外では、別の読み補題によって空集合になるからである。
<!--/-->

```agda
  isPairF : {n : ℕ} → Fin n → Formula ⟪ C ⟫ n
  isPairF bk = ∃̇ (∃̇ (PK.prAt (suc (suc bk)) f1 f0))

  unionMem : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n)
  unionMem wk = ∃̇∈ (var (suc wk)) (var f1 ∈̇ var f0)

  unionEq : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  unionEq ck wk = eqFrame ck (unionMem wk)

  capF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  capF bk ck = (∃̇∈ (var bk) (unionEq (suc ck) f0))
             ∧̇ (∀̇∈ (var bk) (var (suc ck) ∈̇ var f0))

  leftMem : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n)
  leftMem bk = ∃̇ (capF (suc (suc bk)) f0 ∧̇ (var f1 ∈̇ var f0))

  leftEqF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  leftEqF lk bk = eqFrame lk (leftMem bk)

  rightEqF : {n : ℕ} → Fin n → Fin n → Formula ⟪ C ⟫ n
  rightEqF rk bk =
    (∃̇ (∃̇ (PK.prAt (suc (suc bk)) f1 f0 ∧̇ (var (suc (suc rk)) ≐ var f0))))
    ∨̇ ((¬̇ isPairF bk) ∧̇ (∀̇∈ (var rk) ⊥̇))

  cap-out : (b c : S) → ⟨ c ∈ˢ ⋂ b ⟩
          → ∥ Σ[ w ∈ S ] (⟨ w ∈ˢ b ⟩ × (c ≡ ⋃ w)) ∥₁
  cap-out b c h = PT.map go h
    where
    go : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ] ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
           (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
       → Σ[ w ∈ S ] (⟨ w ∈ˢ b ⟩ × (c ≡ ⋃ w))
    go (p , q) = ⟪ b ⟫↪ (p .fst)
      , (∈∈ₛ {a = ⟪ b ⟫↪ (p .fst)} {b = b} .snd (∈ₛ⟪ b ⟫↪ (p .fst)) , sym q)

  cap-all : (b c : S) → ⟨ c ∈ˢ ⋂ b ⟩ → (w : S) → ⟨ w ∈ˢ b ⟩ → ⟨ c ∈ˢ w ⟩
  cap-all b c h w w∈b = ∈∈ₛ {a = c} {b = w} .snd
    (⋂-member-in-all b c w (∈∈ₛ {a = c} {b = ⋂ b} .fst h)
      (∈∈ₛ {a = w} {b = b} .fst w∈b))

  cap-in : (b c w : S) → ⟨ w ∈ˢ b ⟩ → (c ≡ ⋃ w)
         → ((v : S) → ⟨ v ∈ˢ b ⟩ → ⟨ c ∈ˢ v ⟩) → ⟨ c ∈ˢ ⋂ b ⟩
  cap-in b c w w∈b e all = ∣ (fib .fst , cond) , path ∣₁
    where
    fib : Σ[ m ∈ ⟪ b ⟫ ] (⟪ b ⟫↪ m ≡ w)
    fib = ∈-asFiber {a = w} {b = b} w∈b
    path : ⋃ (⟪ b ⟫↪ (fib .fst)) ≡ c
    path = cong ⋃_ (fib .snd) ∙ sym e
    cond : (k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ (fib .fst)) ∈ₛ ⟪ b ⟫↪ k ⟩
    cond k = ∈∈ₛ {a = ⋃ (⟪ b ⟫↪ (fib .fst))} {b = ⟪ b ⟫↪ k} .fst
      (subst (λ t → ⟨ t ∈ˢ ⟪ b ⟫↪ k ⟩) (sym path)
        (all (⟪ b ⟫↪ k) (∈∈ₛ {a = ⟪ b ⟫↪ k} {b = b} .snd (∈ₛ⟪ b ⟫↪ k))))
```

<!--en-->
## The frames' two-way decodes

Each frame's decode is the same extensionality argument as the equality
frame's, run at the frame's own body: the membership of the projection value is
read into the inner world, and the inner reading is lifted back into the
carrier through the transitivity certificate. The right projection is the empty
set off a pair, which the operations layer reads separately, so its description
keeps one case split; the split is faithful because a pair inside the carrier
has both components inside the carrier, so a decomposition anywhere is a
decomposition here.
<!--zh-->
## 诸框架的双向解码

每个框架的解码都与等词框架的外延性论证同形，只把论证跑在框架自己的体上：投影值的隶属读进内层世界，内层读式经传递性证书抬回载体。右投影在非对上取空集，运算层为此另有读引理，故其描述保留一次情形分裂；该分裂忠实，因为载体内的一个对，两个分量都在载体内，故任何地方的分解都是此处的分解。
<!--ja-->
## 各フレームの双方向復号

各フレームの復号は、等号フレームの外延性の議論と同形であり、それをフレーム自身の本体で走らせる。射影値の帰属は内部世界に読み込まれ、内部の読みは推移性証明書を通して台へ持ち上げられる。右射影は対の外では空集合であり、演算層がそれを別の読み補題で読む。したがって、その記述は一度の場合分けを保つ。その場合分けは忠実である。台の中の対は、その二つの成分も台の中にあるから、どこでの分解もここでの分解になる。
<!--/-->

```agda
  cap∈ : (b c : S) → ⟨ b ∈ˢ C ⟩ → ⟨ c ∈ˢ ⋂ b ⟩ → ⟨ c ∈ˢ C ⟩
  cap∈ b c b∈ h = PT.rec (snd (c ∈ˢ C)) go (cap-out b c h)
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ˢ b ⟩ × (c ≡ ⋃ w)) → ⟨ c ∈ˢ C ⟩
    go (w , (w∈b , _)) = mem w c (cap-all b c h w w∈b) (mem b w w∈b b∈)

  unionSub : (w v : S) → ⟨ w ∈ˢ C ⟩ → ⟨ v ∈ˢ (⋃ w) ⟩ → ⟨ v ∈ˢ C ⟩
  unionSub w v w∈ h = PT.rec (snd (v ∈ˢ C)) go
    (union-ax w v .fst (∈∈ₛ {a = v} {b = ⋃ w} .fst h))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ w ⟩ × ⟨ v ∈ₛ t ⟩) → ⟨ v ∈ˢ C ⟩
    go (t , (t∈w , v∈t)) = mem t v (∈∈ₛ {a = v} {b = t} .snd v∈t)
      (mem w t (∈∈ₛ {a = t} {b = w} .snd t∈w) w∈)

  unionMem-out : {n : ℕ} (wk : Fin n) (δ : Vec SM n) (v : S)
                 (v∈ : ⟨ v ∈ˢ C ⟩)
               → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ unionMem wk ⟩
               → ⟨ v ∈ˢ (⋃ (fst (lookup wk δ))) ⟩
  unionMem-out wk δ v v∈ h = ∈∈ₛ {a = v} {b = ⋃ (fst (lookup wk δ))} .snd
    (union-ax (fst (lookup wk δ)) v .snd (PT.map go h))
    where
    go : Σ[ tm ∈ SM ] ⟨ (fst tm ∈ˢ fst (lookup wk δ)) ⊓ (v ∈ˢ fst tm) ⟩
       → Σ[ t ∈ S ] (⟨ t ∈ₛ fst (lookup wk δ) ⟩ × ⟨ v ∈ₛ t ⟩)
    go (tm , (t∈w , v∈t)) = fst tm
      , (∈∈ₛ {a = fst tm} {b = fst (lookup wk δ)} .fst t∈w
        , ∈∈ₛ {a = v} {b = fst tm} .fst v∈t)

  unionMem-in : {n : ℕ} (wk : Fin n) (δ : Vec SM n) (v : S)
                (v∈ : ⟨ v ∈ˢ C ⟩)
              → ⟨ v ∈ˢ (⋃ (fst (lookup wk δ))) ⟩
              → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ unionMem wk ⟩
  unionMem-in wk δ v v∈ h = PT.map go
    (union-ax (fst (lookup wk δ)) v .fst
      (∈∈ₛ {a = v} {b = ⋃ (fst (lookup wk δ))} .fst h))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ fst (lookup wk δ) ⟩ × ⟨ v ∈ₛ t ⟩)
       → Σ[ tm ∈ SM ] ⟨ (fst tm ∈ˢ fst (lookup wk δ)) ⊓ (v ∈ˢ fst tm) ⟩
    go (t , (t∈w , v∈t)) = PK.pt t (mem (fst (lookup wk δ)) t
        (∈∈ₛ {a = t} {b = fst (lookup wk δ)} .snd t∈w) (snd (lookup wk δ)))
      , (∈∈ₛ {a = t} {b = fst (lookup wk δ)} .snd t∈w
        , ∈∈ₛ {a = v} {b = t} .snd v∈t)

  unionEq-out : {n : ℕ} (ck wk : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ unionEq ck wk ⟩
              → fst (lookup ck δ) ≡ ⋃ (fst (lookup wk δ))
  unionEq-out ck wk δ h = eqFrame-out ck (unionMem wk) δ
    (⋃ (fst (lookup wk δ)))
    (λ v k → unionSub (fst (lookup wk δ)) v (snd (lookup wk δ)) k)
    (λ v v∈ k → unionMem-out wk δ v v∈ k)
    (λ v v∈ k → unionMem-in wk δ v v∈ k) h

  unionEq-in : {n : ℕ} (ck wk : Fin n) (δ : Vec SM n)
             → fst (lookup ck δ) ≡ ⋃ (fst (lookup wk δ))
             → ⟨ δ ⊨ᵐ unionEq ck wk ⟩
  unionEq-in ck wk δ e = eqFrame-in ck (unionMem wk) δ
    (⋃ (fst (lookup wk δ)))
    (λ v k → unionSub (fst (lookup wk δ)) v (snd (lookup wk δ)) k)
    (λ v v∈ k → unionMem-out wk δ v v∈ k)
    (λ v v∈ k → unionMem-in wk δ v v∈ k) e

  capF-out : {n : ℕ} (bk ck : Fin n) (δ : Vec SM n)
           → ⟨ δ ⊨ᵐ capF bk ck ⟩
           → ⟨ fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)) ⟩
  capF-out bk ck δ (h₁ , h₂) =
    PT.rec (snd (fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)))) go h₁
    where
    all : (v : S) → ⟨ v ∈ˢ fst (lookup bk δ) ⟩ → ⟨ fst (lookup ck δ) ∈ˢ v ⟩
    all v v∈ = h₂ (PK.pt v (PK.entry∈ bk δ v v∈)) v∈
    go : Σ[ wm ∈ SM ] ⟨ (fst wm ∈ˢ fst (lookup bk δ))
           ⊓ ((wm ∷ δ) ⊨ᵐ unionEq (suc ck) f0) ⟩
       → ⟨ fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)) ⟩
    go (wm , (w∈b , e)) = cap-in (fst (lookup bk δ)) (fst (lookup ck δ))
      (fst wm) w∈b (unionEq-out (suc ck) f0 (wm ∷ δ) e) all

  capF-in : {n : ℕ} (bk ck : Fin n) (δ : Vec SM n)
          → ⟨ fst (lookup ck δ) ∈ˢ ⋂ (fst (lookup bk δ)) ⟩
          → ⟨ δ ⊨ᵐ capF bk ck ⟩
  capF-in bk ck δ h = (part₁ , part₂)
    where
    part₁ : ⟨ δ ⊨ᵐ (∃̇∈ (var bk) (unionEq (suc ck) f0)) ⟩
    part₁ = PT.map go (cap-out (fst (lookup bk δ)) (fst (lookup ck δ)) h)
      where
      go : Σ[ w ∈ S ] (⟨ w ∈ˢ fst (lookup bk δ) ⟩ × (fst (lookup ck δ) ≡ ⋃ w))
         → Σ[ wm ∈ SM ] ⟨ (fst wm ∈ˢ fst (lookup bk δ))
             ⊓ ((wm ∷ δ) ⊨ᵐ unionEq (suc ck) f0) ⟩
      go (w , (w∈b , e)) = PK.pt w (PK.entry∈ bk δ w w∈b)
        , (w∈b , unionEq-in (suc ck) f0 (PK.pt w (PK.entry∈ bk δ w w∈b) ∷ δ) e)
    part₂ : (wm : SM) → ⟨ fst wm ∈ˢ fst (lookup bk δ) ⟩
          → ⟨ fst (lookup ck δ) ∈ˢ fst wm ⟩
    part₂ wm w∈ = cap-all (fst (lookup bk δ)) (fst (lookup ck δ)) h (fst wm) w∈

  leftMem-out : {n : ℕ} (bk : Fin n) (δ : Vec SM n) (v : S)
                (v∈ : ⟨ v ∈ˢ C ⟩)
              → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ leftMem bk ⟩
              → ⟨ v ∈ˢ left (fst (lookup bk δ)) ⟩
  leftMem-out bk δ v v∈ h = subst (λ t → ⟨ v ∈ˢ t ⟩)
    (sym (left-compute (fst (lookup bk δ))))
    (∈∈ₛ {a = v} {b = ⋃ (⋂ (fst (lookup bk δ)))} .snd
      (union-ax (⋂ (fst (lookup bk δ))) v .snd (PT.map go h)))
    where
    go : Σ[ cm ∈ SM ]
           ⟨ ((cm ∷ PK.pt v v∈ ∷ δ) ⊨ᵐ capF (suc (suc bk)) f0)
             ⊓ (v ∈ˢ fst cm) ⟩
       → Σ[ t ∈ S ] (⟨ t ∈ₛ ⋂ (fst (lookup bk δ)) ⟩ × ⟨ v ∈ₛ t ⟩)
    go (cm , (hc , v∈c)) = fst cm
      , (∈∈ₛ {a = fst cm} {b = ⋂ (fst (lookup bk δ))} .fst
          (capF-out (suc (suc bk)) f0 (cm ∷ PK.pt v v∈ ∷ δ) hc)
        , ∈∈ₛ {a = v} {b = fst cm} .fst v∈c)

  leftMem-in : {n : ℕ} (bk : Fin n) (δ : Vec SM n) (v : S)
               (v∈ : ⟨ v ∈ˢ C ⟩)
             → ⟨ v ∈ˢ left (fst (lookup bk δ)) ⟩
             → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ leftMem bk ⟩
  leftMem-in bk δ v v∈ h = PT.map go
    (union-ax (⋂ (fst (lookup bk δ))) v .fst
      (∈∈ₛ {a = v} {b = ⋃ (⋂ (fst (lookup bk δ)))} .fst
        (subst (λ t → ⟨ v ∈ˢ t ⟩) (left-compute (fst (lookup bk δ))) h)))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ ⋂ (fst (lookup bk δ)) ⟩ × ⟨ v ∈ₛ t ⟩)
       → Σ[ cm ∈ SM ]
           ⟨ ((cm ∷ PK.pt v v∈ ∷ δ) ⊨ᵐ capF (suc (suc bk)) f0)
             ⊓ (v ∈ˢ fst cm) ⟩
    go (t , (t∈⋂ , v∈t)) = PK.pt t t∈C
      , (capF-in (suc (suc bk)) f0 (PK.pt t t∈C ∷ PK.pt v v∈ ∷ δ)
          (∈∈ₛ {a = t} {b = ⋂ (fst (lookup bk δ))} .snd t∈⋂)
        , ∈∈ₛ {a = v} {b = t} .snd v∈t)
      where
      t∈C : ⟨ t ∈ˢ C ⟩
      t∈C = cap∈ (fst (lookup bk δ)) t (snd (lookup bk δ))
        (∈∈ₛ {a = t} {b = ⋂ (fst (lookup bk δ))} .snd t∈⋂)

  leftSub : (b v : S) → ⟨ b ∈ˢ C ⟩ → ⟨ v ∈ˢ left b ⟩ → ⟨ v ∈ˢ C ⟩
  leftSub b v b∈ h = PT.rec (snd (v ∈ˢ C)) go
    (union-ax (⋂ b) v .fst (∈∈ₛ {a = v} {b = ⋃ (⋂ b)} .fst
      (subst (λ t → ⟨ v ∈ˢ t ⟩) (left-compute b) h)))
    where
    go : Σ[ t ∈ S ] (⟨ t ∈ₛ ⋂ b ⟩ × ⟨ v ∈ₛ t ⟩) → ⟨ v ∈ˢ C ⟩
    go (t , (t∈⋂ , v∈t)) = mem t v (∈∈ₛ {a = v} {b = t} .snd v∈t)
      (cap∈ b t b∈ (∈∈ₛ {a = t} {b = ⋂ b} .snd t∈⋂))

  leftEqF-out : {n : ℕ} (lk bk : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ leftEqF lk bk ⟩
              → fst (lookup lk δ) ≡ left (fst (lookup bk δ))
  leftEqF-out lk bk δ h = eqFrame-out lk (leftMem bk) δ
    (left (fst (lookup bk δ)))
    (λ v k → leftSub (fst (lookup bk δ)) v (snd (lookup bk δ)) k)
    (λ v v∈ k → leftMem-out bk δ v v∈ k)
    (λ v v∈ k → leftMem-in bk δ v v∈ k) h

  leftEqF-in : {n : ℕ} (lk bk : Fin n) (δ : Vec SM n)
             → fst (lookup lk δ) ≡ left (fst (lookup bk δ))
             → ⟨ δ ⊨ᵐ leftEqF lk bk ⟩
  leftEqF-in lk bk δ e = eqFrame-in lk (leftMem bk) δ
    (left (fst (lookup bk δ)))
    (λ v k → leftSub (fst (lookup bk δ)) v (snd (lookup bk δ)) k)
    (λ v v∈ k → leftMem-out bk δ v v∈ k)
    (λ v v∈ k → leftMem-in bk δ v v∈ k) e

  isPairF-in : {n : ℕ} (bk : Fin n) (δ : Vec SM n) (p q : S)
             → fst (lookup bk δ) ≡ pr p q → ⟨ δ ⊨ᵐ isPairF bk ⟩
  isPairF-in bk δ p q e = ∣ PK.pt p p∈C , ∣ PK.pt q q∈C
    , PK.prAt-in (suc (suc bk)) f1 f0 (PK.pt q q∈C ∷ PK.pt p p∈C ∷ δ) e ∣₁ ∣₁
    where
    pr∈C : ⟨ pr p q ∈ˢ C ⟩
    pr∈C = subst (λ t → ⟨ t ∈ˢ C ⟩) e (snd (lookup bk δ))
    p∈C : ⟨ p ∈ˢ C ⟩
    p∈C = PM.pair-left {a = p} {b = q} pr∈C
    q∈C : ⟨ q ∈ˢ C ⟩
    q∈C = PM.pair-right {a = p} {b = q} pr∈C

  isPairF-out : {n : ℕ} (bk : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ isPairF bk ⟩ → ⟨ isPair (fst (lookup bk δ)) ⟩
  isPairF-out bk δ h = PT.rec (snd (isPair (fst (lookup bk δ)))) k0 h
    where
    k0 : Σ[ pm ∈ SM ] ⟨ (pm ∷ δ) ⊨ᵐ (∃̇ (PK.prAt (suc (suc bk)) f1 f0)) ⟩
       → ⟨ isPair (fst (lookup bk δ)) ⟩
    k0 (pm , h1) = PT.map k1 h1
      where
      k1 : Σ[ qm ∈ SM ]
             ⟨ (qm ∷ pm ∷ δ) ⊨ᵐ PK.prAt (suc (suc bk)) f1 f0 ⟩
         → Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ fst (lookup bk δ) ≡ₕ pr p q ⟩
      k1 (qm , e) = fst pm , (fst qm
        , PK.prAt-out (suc (suc bk)) f1 f0 (qm ∷ pm ∷ δ) e)

  rightEqF-out : {n : ℕ} (rk bk : Fin n) (δ : Vec SM n)
               → ⟨ δ ⊨ᵐ rightEqF rk bk ⟩
               → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
  rightEqF-out rk bk δ h = PT.rec
    (setIsSet (fst (lookup rk δ)) (right (fst (lookup bk δ)))) branch h
    where
    atPair : Σ[ pm ∈ SM ]
               ⟨ (pm ∷ δ) ⊨ᵐ (∃̇ (PK.prAt (suc (suc bk)) f1 f0
                   ∧̇ (var (suc (suc rk)) ≐ var f0))) ⟩
           → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
    atPair (pm , h1) = PT.rec
      (setIsSet (fst (lookup rk δ)) (right (fst (lookup bk δ)))) k1 h1
      where
      k1 : Σ[ qm ∈ SM ]
             ⟨ ((qm ∷ pm ∷ δ) ⊨ᵐ PK.prAt (suc (suc bk)) f1 f0)
               ⊓ (fst (lookup rk δ) ≡ₕ fst qm) ⟩
         → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
      k1 (qm , (e , r≡q)) = r≡q ∙ sym
        (right-at-pair (fst (lookup bk δ)) (fst pm) (fst qm) b≡)
        where
        b≡ : fst (lookup bk δ) ≡ pr (fst pm) (fst qm)
        b≡ = PK.prAt-out (suc (suc bk)) f1 f0 (qm ∷ pm ∷ δ) e
    noPair : ⟨ ((¬ (δ ⊨ᵐ isPairF bk))
             ⊓ (δ ⊨ᵐ (∀̇∈ (var rk) ⊥̇))) ⟩
           → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
    noPair (nb , empty) = r≡∅ ∙ sym right≡∅
      where
      r≡∅ : fst (lookup rk δ) ≡ ∅
      r≡∅ = empty-⊆ (fst (lookup rk δ))
        (λ x h' → Empty.rec* (empty (PK.pt x (PK.entry∈ rk δ x h')) h'))
      right≡∅ : right (fst (lookup bk δ)) ≡ ∅
      right≡∅ = right-nonpair (fst (lookup bk δ))
        (λ p q e → nb (isPairF-in bk δ p q e))
    branch : ⟨ δ ⊨ᵐ (∃̇ (∃̇ (PK.prAt (suc (suc bk)) f1 f0
               ∧̇ (var (suc (suc rk)) ≐ var f0)))) ⟩
           ⊎ ⟨ (¬ (δ ⊨ᵐ isPairF bk))
               ⊓ (δ ⊨ᵐ (∀̇∈ (var rk) ⊥̇)) ⟩
           → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
    branch (inl h1) = PT.rec
      (setIsSet (fst (lookup rk δ)) (right (fst (lookup bk δ)))) atPair h1
    branch (inr h1) = noPair h1

  rightEqF-in : {n : ℕ} (rk bk : Fin n) (δ : Vec SM n)
              → fst (lookup rk δ) ≡ right (fst (lookup bk δ))
              → ⟨ δ ⊨ᵐ rightEqF rk bk ⟩
  rightEqF-in rk bk δ e = go (lem (isPair (fst (lookup bk δ))))
    where
    go : ⟨ isPair (fst (lookup bk δ)) ⟩
       ⊎ (⟨ isPair (fst (lookup bk δ)) ⟩ → Empty.⊥)
       → ⟨ δ ⊨ᵐ rightEqF rk bk ⟩
    go (inl h) = PT.rec (snd (δ ⊨ᵐ rightEqF rk bk)) k h
      where
      k : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ fst (lookup bk δ) ≡ₕ pr p q ⟩
        → ⟨ δ ⊨ᵐ rightEqF rk bk ⟩
      k (p , q , b≡) = ∣ inl ∣ PK.pt p p∈C , ∣ PK.pt q q∈C
        , (PK.prAt-in (suc (suc bk)) f1 f0
            (PK.pt q q∈C ∷ PK.pt p p∈C ∷ δ) b≡
          , e ∙ right≡q) ∣₁ ∣₁ ∣₁
        where
        pr∈C : ⟨ pr p q ∈ˢ C ⟩
        pr∈C = subst (λ t → ⟨ t ∈ˢ C ⟩) b≡ (snd (lookup bk δ))
        p∈C : ⟨ p ∈ˢ C ⟩
        p∈C = PM.pair-left {a = p} {b = q} pr∈C
        q∈C : ⟨ q ∈ˢ C ⟩
        q∈C = PM.pair-right {a = p} {b = q} pr∈C
        right≡q : right (fst (lookup bk δ)) ≡ q
        right≡q = right-at-pair (fst (lookup bk δ)) p q b≡
    go (inr nb) = ∣ inr (nb' , empty) ∣₁
      where
      nb' : ⟨ δ ⊨ᵐ isPairF bk ⟩ → Empty.⊥
      nb' k = nb (isPairF-out bk δ k)
      right≡∅ : right (fst (lookup bk δ)) ≡ ∅
      right≡∅ = right-nonpair (fst (lookup bk δ))
        (λ p q k → nb ∣ p , (q , k) ∣₁)
      empty : (xm : SM) → ⟨ fst xm ∈ˢ fst (lookup rk δ) ⟩ → ⟨ ⊥ ⟩
      empty xm k = Empty.rec (∅-empty (fst xm)
        (∈∈ₛ {a = fst xm} {b = ∅} .fst
          (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) (e ∙ right≡∅) k)))
```

<!--en-->
## The sixteen memberships, at bound arguments

Here is the difference between this chapter and the description chapter: there
the two arguments of an operation were constants, one formula per pair of
arguments; here they are **variables**, because the step quantifies over them.
Each formula below says "the first variable is a member of the value of this
operation at the third and second variables", with the fourth variable reserved
for the value itself. The readings of the operations chapter are consumed
directly, one per clause. The tuple and slice bodies and the four shapes are
the formula scaffolding the later decodes read, written once here so every
decode reads the same text.
<!--zh-->
## 十六条隶属，在受约束的实参上

本章与描述章的分别在此：那里一个运算的两个实参是常量，一对实参一条公式；此处它们是**变量**，因为 step 对它们量化。以下每条公式都说「第一个变量属于本运算在第三、第二个变量处的值」，第四个变量留给该值自身。运算章的诸读引理逐子句直接消费。三元组与切片体以及四条形状是后续解码所读的公式脚手架，一次写在此处，使每条解码都读同一份文本。
<!--ja-->
## 十六個の帰属論理式、束縛された引数において

本章と記述の章の違いはここにある。あちらでは演算の二つの引数は定数であり、引数の対ごとに一つの式があった。こちらではそれらは**変数**である。step がそれらを量化するからである。以下の各式は「第一の変数は、第三と第二の変数におけるこの演算の値のメンバーである」と言い、第四の変数は値自身のために残される。演算の章の読み補題が節ごとに直接消費される。三つ組とスライスの本体、および四つの形状は、後の復号が読む式の足場であり、すべての復号が同じ文面を読むようにここに一度だけ書かれる。
<!--/-->

```agda
  tuple3L4 tuple4L4 : Formula ⟪ C ⟫ 9
  tuple3L4 = PK.prAt f4 f3 f2 ∧̇ (PK.prAt f0 f1 f2 ∧̇ PK.prAt f5 f3 f0)
  tuple4L4 = PK.prAt f4 f3 f2 ∧̇ (PK.prAt f0 f2 f1 ∧̇ PK.prAt f5 f3 f0)

  tuple3L3 tuple4L3 : Formula ⟪ C ⟫ 8
  tuple3L3 = ∃̇ tuple3L4
  tuple4L3 = ∃̇ tuple4L4

  tuple3L2 tuple4L2 : Formula ⟪ C ⟫ 7
  tuple3L2 = ∃̇∈ (var f5) tuple3L3
  tuple4L2 = ∃̇∈ (var f5) tuple4L3

  tuple3L1 tuple4L1 : Formula ⟪ C ⟫ 6
  tuple3L1 = ∃̇ tuple3L2
  tuple4L1 = ∃̇ tuple4L2

  tuple3L0 tuple4L0 : Formula ⟪ C ⟫ 5
  tuple3L0 = ∃̇ tuple3L1
  tuple4L0 = ∃̇ tuple4L1

  sliceMem : Formula ⟪ C ⟫ 6
  sliceMem = ∃̇ (PK.prAt f0 f2 f1 ∧̇ (var f0 ∈̇ var f5))

  shape11 shape12 shape13 shape14 : Formula ⟪ C ⟫ 6
  shape11 = PK.sglAt f2 f1 ∨̇ (∃̇ (PK.prAt f0 f5 f1 ∧̇ PK.pairAt f3 f2 f0))
  shape12 = PK.sglAt f2 f1 ∨̇ (∃̇ (PK.prAt f0 f1 f5 ∧̇ PK.pairAt f3 f2 f0))
  shape13 = (var f2 ≐ var f1) ∨̇ PK.prAt f2 f0 f4
  shape14 = (var f2 ≐ var f1) ∨̇ PK.prAt f2 f4 f0

  mem0 mem1 mem2 mem3 mem4 mem5 mem6 mem7 : Formula ⟪ C ⟫ 4
  mem8 mem9 mem10 mem11 mem12 mem13 mem14 mem15 : Formula ⟪ C ⟫ 4
  mem0 = (var f0 ≐ var f2) ∨̇ (var f0 ≐ var f1)
  mem1 = (var f0 ∈̇ var f2) ∧̇ (¬̇ (var f0 ∈̇ var f1))
  mem2 = ∃̇∈ (var f2) (∃̇∈ (var f2) (PK.prAt f2 f1 f0))
  mem3 = ∃̇∈ (var f1) tuple3L0
  mem4 = ∃̇∈ (var f1) tuple4L0
  mem5 = ∃̇∈ (var f2) (var f1 ∈̇ var f0)
  mem6 = ∃̇∈ (var f2) (∃̇ (PK.prAt f1 f2 f0))
  mem7 = ∃̇∈ (var f2) (∃̇∈ (var f3) ((var f1 ∈̇ var f0) ∧̇ PK.prAt f2 f1 f0))
  mem8 = ∃̇∈ (var f1) (eqFrame f1 sliceMem)
  mem9 = PK.sglAt f0 f2 ∨̇ PK.pairAt f0 f2 f1
  mem10 = ∃̇ (PK.prAt f0 f2 f1 ∧̇ (var f0 ∈̇ var f3))
  mem11 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape11)))
  mem12 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape12)))
  mem13 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape13)))
  mem14 = ∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape14)))
  mem15 = (var f0 ∈̇ var f2) ∧̇ (var f0 ∈̇ con mA)
```

<!--en-->
## The two-way decodes, operations zero through seven

Each decode reads the operation's membership formula against the surviving
specification of its image. The outward direction turns the inner reading of
the formula into a membership in `Fof opN a b`; the inward direction turns
such a membership back into the inner reading. The quantifier witnesses are
placed in the carrier by transitivity. The sealed images hand out their
decompositions through the read lemmas and the write lemmas; the three plain
images read through their specifications. The environment holds the four
bound arguments, the value first.
<!--zh-->
## 双向解码，运算零至七

每条解码都把该运算的隶属公式对着其像的存活规格读。向外方向把公式的内层读式变成 `Fof opN a b` 中的隶属；向内方向把这样的隶属送回内层读式。量词的见证由传递性安放进载体。被封起的像经读引理与写引理交出拆解；三个裸像经各自的规格读取。环境持有四个受约束实参，值居首。
<!--ja-->
## 双方向復号、演算ゼロから七

各復号は、その演算の帰属論理式を像の存続する仕様に対して読む。外向きの方向は、式の内部世界での読みを `Fof opN a b` への帰属へ変える。内向きの方向は、そのような帰属を内部世界の読みへ戻す。量化子の証人は推移性によって台に置かれる。封じられた像は読み補題と書き補題を通して分解を渡す。三つの裸の像は、それらの仕様を通して読まれる。環境は四つの束縛された引数を保持し、値が先頭にある。
<!--/-->

```agda
  mem0-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem0 ⟩
           → ⟨ z ∈ˢ Fof op0 a b ⟩
  mem0-out z b a y z∈ b∈ a∈ y∈ h =
    subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f0 a b)) (F0-spec a b z .snd h)

  mem0-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op0 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem0 ⟩
  mem0-in z b a y z∈ b∈ a∈ y∈ h =
    F0-spec a b z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f0 a b) h)

  mem1-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem1 ⟩
           → ⟨ z ∈ˢ Fof op1 a b ⟩
  mem1-out z b a y z∈ b∈ a∈ y∈ h =
    subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f1 a b)) (F1-spec a b z .snd h)

  mem1-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op1 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem1 ⟩
  mem1-in z b a y z∈ b∈ a∈ y∈ h =
    F1-spec a b z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f1 a b) h)

  mem2-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem2 ⟩
           → ⟨ z ∈ˢ Fof op2 a b ⟩
  mem2-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f2 a b))
    (F2-write a b z (PT.rec PT.squash₁ outer h))
    where
    outer : Σ[ pm ∈ SM ] ⟨ (fst pm ∈ˢ a)
              ⊓ ((pm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                 ⊨ᵐ (∃̇∈ (var f2) (PK.prAt f2 f1 f0))) ⟩
          → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p q ⟩) ∥₁
    outer (pm , (p∈a , hin)) = PT.map inner hin
      where
      inner : Σ[ qm ∈ SM ] ⟨ (fst qm ∈ˢ b)
                ⊓ ((qm ∷ pm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                    ∷ PK.pt y y∈ ∷ []) ⊨ᵐ PK.prAt f2 f1 f0) ⟩
            → Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p q ⟩)
      inner (qm , (q∈b , e)) = fst pm , (fst qm , (p∈a , (q∈b ,
        PK.prAt-out f2 f1 f0
          (qm ∷ pm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) e)))

  mem2-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op2 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem2 ⟩
  mem2-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem2)) go
    (F2-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f2 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p q ⟩)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem2 ⟩
    go (p , q , p∈a , q∈b , e) =
      ∣ PK.pt p (mem a p p∈a a∈)
      , (p∈a , ∣ PK.pt q (mem b q q∈b b∈)
        , (q∈b , PK.prAt-in f2 f1 f0
            (PK.pt q (mem b q q∈b b∈) ∷ PK.pt p (mem a p p∈a a∈)
             ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) ∣₁) ∣₁

  mem5-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem5 ⟩
           → ⟨ z ∈ˢ Fof op5 a b ⟩
  mem5-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f5 a b))
    (F5-spec a b z .snd (PT.map go h))
    where
    go : Σ[ wm ∈ SM ] ⟨ (fst wm ∈ˢ a) ⊓ (z ∈ˢ fst wm) ⟩
       → Σ[ w ∈ S ] ⟨ (w ∈ˢ a) ⊓ (z ∈ˢ w) ⟩
    go (wm , k) = fst wm , k

  mem5-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op5 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem5 ⟩
  mem5-in z b a y z∈ b∈ a∈ y∈ h = PT.map go
    (F5-spec a b z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f5 a b) h))
    where
    go : Σ[ w ∈ S ] ⟨ (w ∈ˢ a) ⊓ (z ∈ˢ w) ⟩
       → Σ[ wm ∈ SM ] ⟨ (fst wm ∈ˢ a) ⊓ (z ∈ˢ fst wm) ⟩
    go (w , (w∈a , z∈w)) = PK.pt w (mem a w w∈a a∈) , (w∈a , z∈w)

  mem6-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem6 ⟩
           → ⟨ z ∈ˢ Fof op6 a b ⟩
  mem6-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f6 a b))
    (F6-write a b z (PT.rec PT.squash₁ outer h))
    where
    outer : Σ[ sm ∈ SM ] ⟨ (fst sm ∈ˢ a)
              ⊓ ((sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                 ⊨ᵐ (∃̇ (PK.prAt f1 f2 f0))) ⟩
          → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ z ≡ₕ p ⟩) ∥₁
    outer (sm , (s∈a , hin)) = PT.map inner hin
      where
      inner : Σ[ vm ∈ SM ]
                ⟨ (vm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                   ∷ PK.pt y y∈ ∷ []) ⊨ᵐ PK.prAt f1 f2 f0 ⟩
            → Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ z ≡ₕ p ⟩)
      inner (vm , e) = z , (fst vm
        , (subst (λ w → ⟨ w ∈ˢ a ⟩)
            (PK.prAt-out f1 f2 f0
              (vm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
               ∷ PK.pt y y∈ ∷ []) e) s∈a
          , refl))

  mem6-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op6 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem6 ⟩
  mem6-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem6)) go
    (F6-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f6 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ z ≡ₕ p ⟩)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem6 ⟩
    go (p , q , pq∈a , e) =
      ∣ PK.pt (pr z q) s∈C , (s∈a , ∣ PK.pt q q∈C
        , PK.prAt-in f1 f2 f0
            (PK.pt q q∈C ∷ PK.pt (pr z q) s∈C
             ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) refl ∣₁) ∣₁
      where
      s∈a : ⟨ pr z q ∈ˢ a ⟩
      s∈a = subst (λ w → ⟨ pr w q ∈ˢ a ⟩) (sym e) pq∈a
      s∈C : ⟨ pr z q ∈ˢ C ⟩
      s∈C = mem a (pr z q) s∈a a∈
      q∈C : ⟨ q ∈ˢ C ⟩
      q∈C = PM.pair-right {a = z} {b = q} s∈C

  mem7-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem7 ⟩
           → ⟨ z ∈ˢ Fof op7 a b ⟩
  mem7-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f7 a b))
    (F7-write a b z (PT.rec PT.squash₁ outer h))
    where
    outer : Σ[ pm ∈ SM ] ⟨ (fst pm ∈ˢ a)
              ⊓ ((pm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                 ⊨ᵐ (∃̇∈ (var f3) ((var f1 ∈̇ var f0) ∧̇ PK.prAt f2 f1 f0))) ⟩
          → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ z ≡ₕ pr p q ⟩) ∥₁
    outer (pm , (p∈a , hin)) = PT.map inner hin
      where
      inner : Σ[ qm ∈ SM ] ⟨ (fst qm ∈ˢ a)
                ⊓ ((qm ∷ pm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                    ∷ PK.pt y y∈ ∷ []) ⊨ᵐ ((var f1 ∈̇ var f0) ∧̇ PK.prAt f2 f1 f0)) ⟩
            → Σ[ p ∈ S ] Σ[ q ∈ S ]
                (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ z ≡ₕ pr p q ⟩)
      inner (qm , (q∈a , (p∈q , e))) = fst pm , (fst qm , (p∈a , (q∈a , (p∈q ,
        PK.prAt-out f2 f1 f0
          (qm ∷ pm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) e))))

  mem7-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op7 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem7 ⟩
  mem7-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem7)) go
    (F7-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f7 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ]
           (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ z ≡ₕ pr p q ⟩)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem7 ⟩
    go (p , q , p∈a , q∈a , p∈q , e) =
      ∣ PK.pt p (mem a p p∈a a∈)
      , (p∈a , ∣ PK.pt q (mem a q q∈a a∈)
        , (q∈a , (p∈q , PK.prAt-in f2 f1 f0
            (PK.pt q (mem a q q∈a a∈) ∷ PK.pt p (mem a p p∈a a∈)
             ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e)) ∣₁) ∣₁

  mem3-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem3 ⟩
           → ⟨ z ∈ˢ Fof op3 a b ⟩
  mem3-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f3 a b))
    (F3-write a b z (PT.rec PT.squash₁ k0 h))
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ p ∈ S ] Σ[ w ∈ S ] Σ[ q ∈ S ]
             (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr w q) ⟩) ∥₁
    k0 : Σ[ sm ∈ SM ] ⟨ (fst sm ∈ˢ b)
           ⊓ ((sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
              ⊨ᵐ tuple3L0) ⟩
       → Goal
    k0 (sm , (s∈b , h1)) = PT.rec PT.squash₁ k1 h1
      where
      k1 : Σ[ pm ∈ SM ]
             ⟨ (pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple3L1 ⟩
         → Goal
      k1 (pm , h2) = PT.rec PT.squash₁ k2 h2
        where
        k2 : Σ[ qm ∈ SM ]
               ⟨ (qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                  ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple3L2 ⟩
           → Goal
        k2 (qm , h3) = PT.rec PT.squash₁ k3 h3
          where
          k3 : Σ[ wm ∈ SM ] ⟨ (fst wm ∈ˢ a)
                 ⊓ ((wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                     ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple3L3) ⟩
             → Goal
          k3 (wm , (w∈a , h4)) = PT.map k4 h4
            where
            k4 : Σ[ tm ∈ SM ]
                   ⟨ (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                      ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple3L4 ⟩
               → Σ[ p ∈ S ] Σ[ w ∈ S ] Σ[ q ∈ S ]
                   (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr w q) ⟩)
            k4 (tm , (e1 , (e2 , e3))) =
              fst pm , (fst wm , (fst qm , (w∈a , (pq∈b , zeq))))
              where
              pq∈b : ⟨ pr (fst pm) (fst qm) ∈ˢ b ⟩
              pq∈b = subst (λ v → ⟨ v ∈ˢ b ⟩)
                (PK.prAt-out f4 f3 f2
                  (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                   ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e1) s∈b
              zeq : z ≡ pr (fst pm) (pr (fst wm) (fst qm))
              zeq = PK.prAt-out f5 f3 f0
                (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                 ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e3
                ∙ cong (pr (fst pm)) (PK.prAt-out f0 f1 f2
                    (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                     ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e2)

  mem3-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op3 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem3 ⟩
  mem3-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem3)) go
    (F3-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f3 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ w ∈ S ] Σ[ q ∈ S ]
           (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr w q) ⟩)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem3 ⟩
    go (p , w , q , w∈a , pq∈b , e) =
      ∣ PK.pt (pr p q) s∈C , (pq∈b , ∣ PK.pt p p∈C , ∣ PK.pt q q∈C
        , ∣ PK.pt w (mem a w w∈a a∈) , (w∈a , ∣ PK.pt (pr w q) t∈C
          , (PK.prAt-in f4 f3 f2 env₉ refl
            , (PK.prAt-in f0 f1 f2 env₉ refl , PK.prAt-in f5 f3 f0 env₉ e)) ∣₁) ∣₁ ∣₁ ∣₁) ∣₁
      where
      s∈C : ⟨ pr p q ∈ˢ C ⟩
      s∈C = mem b (pr p q) pq∈b b∈
      p∈C : ⟨ p ∈ˢ C ⟩
      p∈C = PM.pair-left {a = p} {b = q} s∈C
      q∈C : ⟨ q ∈ˢ C ⟩
      q∈C = PM.pair-right {a = p} {b = q} s∈C
      t∈C : ⟨ pr w q ∈ˢ C ⟩
      t∈C = PM.pair-right {a = p} {b = pr w q} (subst (λ v → ⟨ v ∈ˢ C ⟩) e z∈)
      env₉ : Vec SM 9
      env₉ = PK.pt (pr w q) t∈C ∷ PK.pt w (mem a w w∈a a∈) ∷ PK.pt q q∈C
           ∷ PK.pt p p∈C ∷ PK.pt (pr p q) s∈C ∷ PK.pt z z∈ ∷ PK.pt b b∈
           ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []

  mem4-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem4 ⟩
           → ⟨ z ∈ˢ Fof op4 a b ⟩
  mem4-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f4 a b))
    (F4-write a b z (PT.rec PT.squash₁ k0 h))
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ w ∈ S ]
             (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr q w) ⟩) ∥₁
    k0 : Σ[ sm ∈ SM ] ⟨ (fst sm ∈ˢ b)
           ⊓ ((sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
              ⊨ᵐ tuple4L0) ⟩
       → Goal
    k0 (sm , (s∈b , h1)) = PT.rec PT.squash₁ k1 h1
      where
      k1 : Σ[ pm ∈ SM ]
             ⟨ (pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple4L1 ⟩
         → Goal
      k1 (pm , h2) = PT.rec PT.squash₁ k2 h2
        where
        k2 : Σ[ qm ∈ SM ]
               ⟨ (qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                  ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple4L2 ⟩
           → Goal
        k2 (qm , h3) = PT.rec PT.squash₁ k3 h3
          where
          k3 : Σ[ wm ∈ SM ] ⟨ (fst wm ∈ˢ a)
                 ⊓ ((wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                     ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple4L3) ⟩
             → Goal
          k3 (wm , (w∈a , h4)) = PT.map k4 h4
            where
            k4 : Σ[ tm ∈ SM ]
                   ⟨ (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                      ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ tuple4L4 ⟩
               → Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ w ∈ S ]
                   (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr q w) ⟩)
            k4 (tm , (e1 , (e2 , e3))) =
              fst pm , (fst qm , (fst wm , (w∈a , (pq∈b , zeq))))
              where
              pq∈b : ⟨ pr (fst pm) (fst qm) ∈ˢ b ⟩
              pq∈b = subst (λ v → ⟨ v ∈ˢ b ⟩)
                (PK.prAt-out f4 f3 f2
                  (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                   ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e1) s∈b
              zeq : z ≡ pr (fst pm) (pr (fst qm) (fst wm))
              zeq = PK.prAt-out f5 f3 f0
                (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                 ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e3
                ∙ cong (pr (fst pm)) (PK.prAt-out f0 f2 f1
                    (tm ∷ wm ∷ qm ∷ pm ∷ sm ∷ PK.pt z z∈ ∷ PK.pt b b∈
                     ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e2)

  mem4-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op4 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem4 ⟩
  mem4-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem4)) go
    (F4-read a b z (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f4 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ w ∈ S ]
           (⟨ w ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ z ≡ₕ pr p (pr q w) ⟩)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem4 ⟩
    go (p , q , w , w∈a , pq∈b , e) =
      ∣ PK.pt (pr p q) s∈C , (pq∈b , ∣ PK.pt p p∈C , ∣ PK.pt q q∈C
        , ∣ PK.pt w (mem a w w∈a a∈) , (w∈a , ∣ PK.pt (pr q w) t∈C
          , (PK.prAt-in f4 f3 f2 env₉ refl
            , (PK.prAt-in f0 f2 f1 env₉ refl , PK.prAt-in f5 f3 f0 env₉ e)) ∣₁) ∣₁ ∣₁ ∣₁) ∣₁
      where
      s∈C : ⟨ pr p q ∈ˢ C ⟩
      s∈C = mem b (pr p q) pq∈b b∈
      p∈C : ⟨ p ∈ˢ C ⟩
      p∈C = PM.pair-left {a = p} {b = q} s∈C
      q∈C : ⟨ q ∈ˢ C ⟩
      q∈C = PM.pair-right {a = p} {b = q} s∈C
      t∈C : ⟨ pr q w ∈ˢ C ⟩
      t∈C = PM.pair-right {a = p} {b = pr q w} (subst (λ v → ⟨ v ∈ˢ C ⟩) e z∈)
      env₉ : Vec SM 9
      env₉ = PK.pt (pr q w) t∈C ∷ PK.pt w (mem a w w∈a a∈) ∷ PK.pt q q∈C
           ∷ PK.pt p p∈C ∷ PK.pt (pr p q) s∈C ∷ PK.pt z z∈ ∷ PK.pt b b∈
           ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []
```

<!--en-->
## The two-way decodes, operations eight through fifteen

The second half of the decodes reads through the surviving specifications of
the remaining images. The ninth formula is the disjunction of the singleton
and the unordered pair, which the pair kit's own atoms read; the tenth is the
image slice, read through `F10-spec`; and the fifteenth is the relativization
slot, read through `F15Of` at the certificate `qA`, which is the only place
the slot `A` enters a decode. The eighth formula quantifies over the members
of the second argument and reads one slice of the first argument at each, so
its decode first proves that a slice is a subset of the carrier whenever its
argument is a member of the carrier. Every witness is placed in the carrier by
transitivity, exactly as in the first half.
<!--zh-->
## 双向解码，运算八至十五

后一半的解码经其余诸像的存活规格读取。第九条公式是单点集与无序对的析取，由对器材自己的原子读取；第十条是像切片，经 `F10-spec` 读取；第十五条是相对化槽，经 `F15Of` 在证书 `qA` 处读取，这也是槽 `A` 唯一进入解码之处。第八条公式对第二实参的诸成员量化，在每一处读取第一实参的一个切片，故其解码先证：只要实参是载体的成员，切片就是载体的子集。每个见证都由传递性安放进载体，与前一半分毫不差。
<!--ja-->
## 双方向復号、演算八から十五

後半の復号は、残りの像の存続する仕様を通して読まれる。第九の式は単点集合と非順序対の論理和であり、対のキット自身の原子が読む。第十は像のスライスであり、`F10-spec` を通して読まれる。第十五は相対化スロットであり、証明書 `qA` のところで `F15Of` を通して読まれる。ここが、スロット `A` が復号に入る唯一の場所である。第八の式は第二の引数のメンバーを量化し、各メンバーにおいて第一の引数のスライスを一つ読む。したがって、その復号はまず次を証明する。引数が台のメンバーなら、スライスは台の部分集合である。すべての証人は前半とまったく同じように、推移性によって台に置かれる。
<!--/-->

```agda
  mem9-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem9 ⟩
           → ⟨ z ∈ˢ Fof op9 a b ⟩
  mem9-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f9 a b))
    (F0-spec (⁅ a ⁆s) (⁅ a , b ⁆) z .snd (PT.map go h))
    where
    go : ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
           ⊨ᵐ PK.sglAt f0 f2 ⟩
       ⊎ ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
           ⊨ᵐ PK.pairAt f0 f2 f1 ⟩
       → (z ≡ ⁅ a ⁆s) ⊎ (z ≡ ⁅ a , b ⁆)
    go (inl s) = inl
      (PK.sglAt-out f0 f2
        (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) s)
    go (inr s) = inr
      (PK.pairAt-out f0 f2 f1
        (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) s)

  mem9-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op9 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem9 ⟩
  mem9-in z b a y z∈ b∈ a∈ y∈ h = PT.map go
    (F0-spec (⁅ a ⁆s) (⁅ a , b ⁆) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f9 a b) h))
    where
    go : (z ≡ ⁅ a ⁆s) ⊎ (z ≡ ⁅ a , b ⁆)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
           ⊨ᵐ PK.sglAt f0 f2 ⟩
       ⊎ ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
           ⊨ᵐ PK.pairAt f0 f2 f1 ⟩
    go (inl e) = inl
      (PK.sglAt-in f0 f2
        (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e)
    go (inr e) = inr
      (PK.pairAt-in f0 f2 f1
        (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e)

  mem10-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem10 ⟩
            → ⟨ z ∈ˢ Fof op10 a b ⟩
  mem10-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f10 a b))
    (PT.rec (snd (z ∈ˢ F10 a b)) go h)
    where
    go : Σ[ sm ∈ SM ]
           ⟨ (sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
             ⊨ᵐ (PK.prAt f0 f2 f1 ∧̇ (var f0 ∈̇ var f3)) ⟩
       → ⟨ z ∈ˢ F10 a b ⟩
    go (sm , (e , s∈a)) = subst ⟨_⟩ (sym (F10-spec a b z))
      (subst (λ w → ⟨ w ∈ˢ a ⟩)
        (PK.prAt-out f0 f2 f1
          (sm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) s∈a)

  mem10-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op10 a b ⟩
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem10 ⟩
  mem10-in z b a y z∈ b∈ a∈ y∈ h =
    ∣ PK.pt (pr b z) s∈C , (PK.prAt-in f0 f2 f1
        (PK.pt (pr b z) s∈C ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
         ∷ PK.pt y y∈ ∷ []) refl
      , s∈a) ∣₁
    where
    s∈a : ⟨ pr b z ∈ˢ a ⟩
    s∈a = subst ⟨_⟩ (F10-spec a b z)
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f10 a b) h)
    s∈C : ⟨ pr b z ∈ˢ C ⟩
    s∈C = mem a (pr b z) s∈a a∈

  mem15-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem15 ⟩
            → ⟨ z ∈ˢ Fof op15 a b ⟩
  mem15-out z b a y z∈ b∈ a∈ y∈ (z∈a , z∈mA) =
    subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f15 a b))
      (subst ⟨_⟩ (sym (F15C.F15-spec a z))
        (z∈a , subst (λ w → ⟨ z ∈ˢ w ⟩) qA z∈mA))
    where
    module F15C = F15Of A

  mem15-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op15 a b ⟩
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem15 ⟩
  mem15-in z b a y z∈ b∈ a∈ y∈ h =
    (parts .fst , subst (λ w → ⟨ z ∈ˢ w ⟩) (sym qA) (parts .snd))
    where
    module F15C = F15Of A
    parts : ⟨ (z ∈ˢ a) ⊓ (z ∈ˢ A) ⟩
    parts = subst ⟨_⟩ (F15C.F15-spec a z)
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f15 a b) h)

  sliceMem-out : (z b a y c v : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
                 (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩) (c∈ : ⟨ c ∈ˢ C ⟩)
                 (v∈ : ⟨ v ∈ˢ C ⟩)
               → ⟨ (PK.pt v v∈ ∷ PK.pt c c∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
                    ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ sliceMem ⟩
               → ⟨ v ∈ˢ F10 a c ⟩
  sliceMem-out z b a y c v z∈ b∈ a∈ y∈ c∈ v∈ h =
    PT.rec (snd (v ∈ˢ F10 a c)) go h
    where
    go : Σ[ sm ∈ SM ]
           ⟨ ((sm ∷ PK.pt v v∈ ∷ PK.pt c c∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
               ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ PK.prAt f0 f2 f1)
             ⊓ (fst sm ∈ˢ a) ⟩
       → ⟨ v ∈ˢ F10 a c ⟩
    go (sm , (e , s∈a)) = subst ⟨_⟩ (sym (F10-spec a c v))
      (subst (λ w → ⟨ w ∈ˢ a ⟩)
        (PK.prAt-out f0 f2 f1
          (sm ∷ PK.pt v v∈ ∷ PK.pt c c∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
           ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) s∈a)

  sliceMem-in : (z b a y c v : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
                (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩) (c∈ : ⟨ c ∈ˢ C ⟩)
                (v∈ : ⟨ v ∈ˢ C ⟩)
              → ⟨ v ∈ˢ F10 a c ⟩
              → ⟨ (PK.pt v v∈ ∷ PK.pt c c∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
                   ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ sliceMem ⟩
  sliceMem-in z b a y c v z∈ b∈ a∈ y∈ c∈ v∈ h =
    ∣ PK.pt (pr c v) s∈C
    , (PK.prAt-in f0 f2 f1
        (PK.pt (pr c v) s∈C ∷ PK.pt v v∈ ∷ PK.pt c c∈ ∷ PK.pt z z∈
         ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) refl
      , s∈a) ∣₁
    where
    s∈a : ⟨ pr c v ∈ˢ a ⟩
    s∈a = subst ⟨_⟩ (F10-spec a c v) h
    s∈C : ⟨ pr c v ∈ˢ C ⟩
    s∈C = mem a (pr c v) s∈a a∈

  sliceSub : (a c : S) → ⟨ a ∈ˢ C ⟩ → (v : S) → ⟨ v ∈ˢ F10 a c ⟩ → ⟨ v ∈ˢ C ⟩
  sliceSub a c a∈ v h = PM.pair-right {a = c} {b = v}
    (mem a (pr c v) (subst ⟨_⟩ (F10-spec a c v) h) a∈)

  mem8-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem8 ⟩
           → ⟨ z ∈ˢ Fof op8 a b ⟩
  mem8-out z b a y z∈ b∈ a∈ y∈ h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f8 a b))
    (PT.rec (snd (z ∈ˢ F8 a b)) go h)
    where
    go : Σ[ cm ∈ SM ] ⟨ (fst cm ∈ˢ b)
           ⊓ ((cm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
              ⊨ᵐ eqFrame f1 sliceMem) ⟩
       → ⟨ z ∈ˢ F8 a b ⟩
    go (cm , (c∈b , hf)) = subst ⟨_⟩ (sym (F8-spec a b z))
      ∣ fib .fst , (cong (F10 a) (fib .snd) ∙ sym zeq) ∣₁
      where
      c∈C : ⟨ fst cm ∈ˢ C ⟩
      c∈C = snd cm
      fib : Σ[ m ∈ ⟪ b ⟫ ] (⟪ b ⟫↪ m ≡ fst cm)
      fib = ∈-asFiber {a = fst cm} {b = b} c∈b
      zeq : z ≡ F10 a (fst cm)
      zeq = eqFrame-out f1 sliceMem
        (cm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
        (F10 a (fst cm))
        (sliceSub a (fst cm) a∈)
        (λ v v∈ k → sliceMem-out z b a y (fst cm) v z∈ b∈ a∈ y∈ c∈C v∈ k)
        (λ v v∈ k → sliceMem-in z b a y (fst cm) v z∈ b∈ a∈ y∈ c∈C v∈ k) hf

  mem8-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ z ∈ˢ Fof op8 a b ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem8 ⟩
  mem8-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem8)) go
    (subst ⟨_⟩ (F8-spec a b z) (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f8 a b) h))
    where
    go : Σ[ m ∈ ⟪ b ⟫ ] (F10 a (⟪ b ⟫↪ m) ≡ z)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem8 ⟩
    go (m , e) = ∣ PK.pt (⟪ b ⟫↪ m) c∈C , (c∈b , frame) ∣₁
      where
      c∈b : ⟨ ⟪ b ⟫↪ m ∈ˢ b ⟩
      c∈b = ∈∈ₛ {a = ⟪ b ⟫↪ m} {b = b} .snd (∈ₛ⟪ b ⟫↪ m)
      c∈C : ⟨ ⟪ b ⟫↪ m ∈ˢ C ⟩
      c∈C = mem b (⟪ b ⟫↪ m) c∈b b∈
      frame : ⟨ (PK.pt (⟪ b ⟫↪ m) c∈C ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                 ∷ PK.pt y y∈ ∷ []) ⊨ᵐ eqFrame f1 sliceMem ⟩
      frame = eqFrame-in f1 sliceMem
        (PK.pt (⟪ b ⟫↪ m) c∈C ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
         ∷ PK.pt y y∈ ∷ [])
        (F10 a (⟪ b ⟫↪ m)) (sliceSub a (⟪ b ⟫↪ m) a∈)
        (λ v v∈ k → sliceMem-out z b a y (⟪ b ⟫↪ m) v z∈ b∈ a∈ y∈ c∈C v∈ k)
        (λ v v∈ k → sliceMem-in z b a y (⟪ b ⟫↪ m) v z∈ b∈ a∈ y∈ c∈C v∈ k)
        (sym e)
```

<!--en-->
## The four tuple insertions, over one frame

The four operations that shuffle a pair's components share a frame: bind the
two projections, pin them to the second argument, and let the arm say only how
the value is built from them. The frame is where the projections enter and
leave; the four arms below differ only in the shape of the value, and each is
two readings of the unordered pair. The projections are members of the carrier
whenever their argument is: on a pair by the pair reading, and off a pair by
the empty set.
<!--zh-->
## 四个三元组运算，同用一个框架

搬运对之分量的四个运算共用一个框架：约束两个投影，把它们钉在第二实参上，臂只说该值如何由它们造出。投影在框架处进场与退场；以下四条臂只在值的形状上有别，每条都是无序对的两次读取。只要实参是载体的成员，两个投影就是载体的成员：在对上由对读式给出，不在对上由空集给出。
<!--ja-->
## 四つの三つ組演算、一つのフレームの上で

対の成分を並べ替える四つの演算は、一つのフレームを共有する。二つの射影を束縛し、それらを第二の引数に固定し、腕は値がそれらからどう作られるかだけを言う。射影がフレームで入り、フレームから出る。以下の四つの腕は値の形だけが異なり、それぞれ非順序対の二回の読みである。引数が台のメンバーなら、二つの射影も台のメンバーである。対の上では対の読みが与え、対の外では空集合が与える。
<!--/-->

```agda
  left-read : (b : S) → ⟨ b ∈ˢ C ⟩ → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
  left-read b b∈ = atPair (lem (isPair b))
    where
    atPair : ⟨ isPair b ⟩ ⊎ (⟨ isPair b ⟩ → Empty.⊥)
           → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
    atPair (inl h) = inl (PT.rec (snd (left b ∈ˢ C)) go h)
      where
      go : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ left b ∈ˢ C ⟩
      go (p , q , b≡) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym left≡p)
        (PM.pair-left {a = p} {b = q} (subst (λ w → ⟨ w ∈ˢ C ⟩) b≡ b∈))
        where
        left≡p : left b ≡ p
        left≡p = subst (λ w → left w ≡ p) (sym b≡) (left-spec p q)
    atPair (inr _) = atCap (lem (∃[ c ] (c ∈ₛ ⋂ b)))
      where
      atCap : ⟨ ∃[ c ] (c ∈ₛ ⋂ b) ⟩ ⊎ (⟨ ∃[ c ] (c ∈ₛ ⋂ b) ⟩ → Empty.⊥)
            → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
      atCap (inl e) = inl (PT.rec (snd (left b ∈ˢ C)) go e)
        where
        go : Σ[ c ∈ S ] ⟨ c ∈ₛ ⋂ b ⟩ → ⟨ left b ∈ˢ C ⟩
        go (c , c∈⋂) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym (left-⋂-collapse b c c∈⋂))
          (PT.rec (snd (c ∈ˢ C)) inC (∈∈ₛ {a = c} {b = ⋂ b} .snd c∈⋂))
          where
          inC : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ]
                      ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
                  (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
              → ⟨ c ∈ˢ C ⟩
          inC (p , _) = mem w c c∈w w∈C
            where
            w : S
            w = ⟪ b ⟫↪ (p .fst)
            w∈C : ⟨ w ∈ˢ C ⟩
            w∈C = mem b w (∈∈ₛ {a = w} {b = b} .snd (∈ₛ⟪ b ⟫↪ (p .fst))) b∈
            c∈w : ⟨ c ∈ˢ w ⟩
            c∈w = ∈∈ₛ {a = c} {b = w} .snd
              (⋂-member-in-all b c w c∈⋂ (∈ₛ⟪ b ⟫↪ (p .fst)))
      atCap (inr no) = inr (left-⋂-empty b (λ c h → no ∣ c , h ∣₁))

  right-read : (b : S) → ⟨ b ∈ˢ C ⟩ → (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅))
  right-read b b∈ = atPair (lem (isPair b))
    where
    atPair : ⟨ isPair b ⟩ ⊎ (⟨ isPair b ⟩ → Empty.⊥)
           → (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅))
    atPair (inl h) = inl (PT.rec (snd (right b ∈ˢ C)) go h)
      where
      go : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ right b ∈ˢ C ⟩
      go (p , q , b≡) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym (right-at-pair b p q b≡))
        (PM.pair-right {a = p} {b = q} (subst (λ w → ⟨ w ∈ˢ C ⟩) b≡ b∈))
    atPair (inr nb) = inr (right-nonpair b (λ p q e → nb ∣ p , q , e ∣₁))

  left∈C : (b : S) → ⟨ b ∈ˢ C ⟩ → ⟨ left b ∈ˢ C ⟩
  left∈C b b∈ = go (left-read b b∈)
    where
    go : (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅)) → ⟨ left b ∈ˢ C ⟩
    go (inl h) = h
    go (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) ∅∈C

  right∈C : (b : S) → ⟨ b ∈ˢ C ⟩ → ⟨ right b ∈ˢ C ⟩
  right∈C b b∈ = go (right-read b b∈)
    where
    go : (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅)) → ⟨ right b ∈ˢ C ⟩
    go (inl h) = h
    go (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) ∅∈C

  tupleOut : (shape : Formula ⟪ C ⟫ 6) (z b a y : S)
             (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩) (R : hProp (ℓ-suc ℓ))
           → ((l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
              → l ≡ left b → r ≡ right b
              → ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
                   ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ shape ⟩
              → ⟨ R ⟩)
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
               ⊨ᵐ (∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape)))) ⟩
           → ⟨ R ⟩
  tupleOut shape z b a y z∈ b∈ a∈ y∈ R k h = PT.rec (snd R) k0 h
    where
    k0 : Σ[ lm ∈ SM ]
           ⟨ (lm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
             ⊨ᵐ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape))) ⟩
       → ⟨ R ⟩
    k0 (lm , h1) = PT.rec (snd R) k1 h1
      where
      k1 : Σ[ rm ∈ SM ]
             ⟨ ((rm ∷ lm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                 ∷ PK.pt y y∈ ∷ []) ⊨ᵐ leftEqF f1 f3)
               ⊓ (((rm ∷ lm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                    ∷ PK.pt y y∈ ∷ []) ⊨ᵐ rightEqF f0 f3)
                 ⊓ ((rm ∷ lm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
                     ∷ PK.pt y y∈ ∷ []) ⊨ᵐ shape)) ⟩
         → ⟨ R ⟩
      k1 (rm , (hl , (hr , hs))) = k (fst lm) (fst rm) (snd lm) (snd rm)
        (leftEqF-out f1 f3
          (rm ∷ lm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) hl)
        (rightEqF-out f0 f3
          (rm ∷ lm ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) hr)
        hs

  tupleIn : (shape : Formula ⟪ C ⟫ 6) (z b a y : S)
            (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
            (y∈ : ⟨ y ∈ˢ C ⟩)
          → ⟨ (PK.pt (right b) (right∈C b b∈) ∷ PK.pt (left b) (left∈C b b∈)
               ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
              ⊨ᵐ shape ⟩
          → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
              ⊨ᵐ (∃̇ (∃̇ (leftEqF f1 f3 ∧̇ (rightEqF f0 f3 ∧̇ shape)))) ⟩
  tupleIn shape z b a y z∈ b∈ a∈ y∈ hs =
    ∣ PK.pt (left b) (left∈C b b∈)
    , ∣ PK.pt (right b) (right∈C b b∈)
      , (leftEqF-in f1 f3
          (PK.pt (right b) (right∈C b b∈) ∷ PK.pt (left b) (left∈C b b∈)
           ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) refl
        , (rightEqF-in f0 f3
            (PK.pt (right b) (right∈C b b∈) ∷ PK.pt (left b) (left∈C b b∈)
             ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) refl
          , hs)) ∣₁ ∣₁

  mem11-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem11 ⟩
            → ⟨ z ∈ˢ Fof op11 a b ⟩
  mem11-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape11 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op11 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) ⊨ᵐ shape11 ⟩
      → ⟨ z ∈ˢ Fof op11 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f11 a b))
      (F0-spec (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆) z .snd
        (PT.rec (snd ((z ≡ₕ ⁅ left b ⁆s)
          ⊔ (z ≡ₕ ⁅ left b , pr a (right b) ⁆))) go hs))
      where
      go : ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
              ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ PK.sglAt f2 f1 ⟩
         ⊎ ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
              ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
             ⊨ᵐ (∃̇ (PK.prAt f0 f5 f1 ∧̇ PK.pairAt f3 f2 f0)) ⟩
         → ⟨ (z ≡ₕ ⁅ left b ⁆s) ⊔ (z ≡ₕ ⁅ left b , pr a (right b) ⁆) ⟩
      go (inl s) = ∣ inl (subst (λ w → z ≡ ⁅ w ⁆s) el
        (PK.sglAt-out f2 f1
          (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
           ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) s)) ∣₁
      go (inr s) = PT.map inner s
        where
        inner : Σ[ tm ∈ SM ]
                  ⟨ ((tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                      ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                     ⊨ᵐ PK.prAt f0 f5 f1)
                    ⊓ ((tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                        ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                       ⊨ᵐ PK.pairAt f3 f2 f0) ⟩
              → (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr a (right b) ⁆)
        inner (tm , (e1 , e2)) = inr
          (subst (λ w → z ≡ ⁅ w , pr a (right b) ⁆) el
            (subst (λ w → z ≡ ⁅ l , pr a w ⁆) er
              (subst (λ w → z ≡ ⁅ l , w ⁆)
                (PK.prAt-out f0 f5 f1
                  (tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                   ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e1)
                (PK.pairAt-out f3 f2 f0
                  (tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                   ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e2))))

  mem11-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op11 a b ⟩
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem11 ⟩
  mem11-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem11)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f11 a b) h))
    where
    go : (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr a (right b) ⁆)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem11 ⟩
    go (inl e) = tupleIn shape11 z b a y z∈ b∈ a∈ y∈
      ∣ inl (PK.sglAt-in f2 f1
        (PK.pt (right b) (right∈C b b∈) ∷ PK.pt (left b) (left∈C b b∈)
         ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) ∣₁
    go (inr e) = tupleIn shape11 z b a y z∈ b∈ a∈ y∈
      ∣ inr ∣ PK.pt (pr a (right b)) t∈C
        , (PK.prAt-in f0 f5 f1
            (PK.pt (pr a (right b)) t∈C ∷ PK.pt (right b) (right∈C b b∈)
             ∷ PK.pt (left b) (left∈C b b∈) ∷ PK.pt z z∈ ∷ PK.pt b b∈
             ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) refl
          , PK.pairAt-in f3 f2 f0
              (PK.pt (pr a (right b)) t∈C ∷ PK.pt (right b) (right∈C b b∈)
               ∷ PK.pt (left b) (left∈C b b∈) ∷ PK.pt z z∈ ∷ PK.pt b b∈
               ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) ∣₁ ∣₁
      where
      t∈C : ⟨ pr a (right b) ∈ˢ C ⟩
      t∈C = mem z (pr a (right b))
        (subst (λ w → ⟨ pr a (right b) ∈ˢ w ⟩) (sym e)
          (F0-spec (left b) (pr a (right b)) (pr a (right b)) .snd
            ∣ inr refl ∣₁)) z∈

  mem12-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem12 ⟩
            → ⟨ z ∈ˢ Fof op12 a b ⟩
  mem12-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape12 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op12 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) ⊨ᵐ shape12 ⟩
      → ⟨ z ∈ˢ Fof op12 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f12 a b))
      (F0-spec (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆) z .snd
        (PT.rec (snd ((z ≡ₕ ⁅ left b ⁆s)
          ⊔ (z ≡ₕ ⁅ left b , pr (right b) a ⁆))) go hs))
      where
      go : ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
              ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ PK.sglAt f2 f1 ⟩
         ⊎ ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
              ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
             ⊨ᵐ (∃̇ (PK.prAt f0 f1 f5 ∧̇ PK.pairAt f3 f2 f0)) ⟩
         → ⟨ (z ≡ₕ ⁅ left b ⁆s) ⊔ (z ≡ₕ ⁅ left b , pr (right b) a ⁆) ⟩
      go (inl s) = ∣ inl (subst (λ w → z ≡ ⁅ w ⁆s) el
        (PK.sglAt-out f2 f1
          (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
           ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) s)) ∣₁
      go (inr s) = PT.map inner s
        where
        inner : Σ[ tm ∈ SM ]
                  ⟨ ((tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                      ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                     ⊨ᵐ PK.prAt f0 f1 f5)
                    ⊓ ((tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                        ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                       ⊨ᵐ PK.pairAt f3 f2 f0) ⟩
              → (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr (right b) a ⁆)
        inner (tm , (e1 , e2)) = inr
          (subst (λ w → z ≡ ⁅ w , pr (right b) a ⁆) el
            (subst (λ w → z ≡ ⁅ l , pr w a ⁆) er
              (subst (λ w → z ≡ ⁅ l , w ⁆)
                (PK.prAt-out f0 f1 f5
                  (tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                   ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e1)
                (PK.pairAt-out f3 f2 f0
                  (tm ∷ PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈
                   ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e2))))

  mem12-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op12 a b ⟩
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem12 ⟩
  mem12-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem12)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f12 a b) h))
    where
    go : (z ≡ ⁅ left b ⁆s) ⊎ (z ≡ ⁅ left b , pr (right b) a ⁆)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem12 ⟩
    go (inl e) = tupleIn shape12 z b a y z∈ b∈ a∈ y∈
      ∣ inl (PK.sglAt-in f2 f1
        (PK.pt (right b) (right∈C b b∈) ∷ PK.pt (left b) (left∈C b b∈)
         ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) ∣₁
    go (inr e) = tupleIn shape12 z b a y z∈ b∈ a∈ y∈
      ∣ inr ∣ PK.pt (pr (right b) a) t∈C
        , (PK.prAt-in f0 f1 f5
            (PK.pt (pr (right b) a) t∈C ∷ PK.pt (right b) (right∈C b b∈)
             ∷ PK.pt (left b) (left∈C b b∈) ∷ PK.pt z z∈ ∷ PK.pt b b∈
             ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) refl
          , PK.pairAt-in f3 f2 f0
              (PK.pt (pr (right b) a) t∈C ∷ PK.pt (right b) (right∈C b b∈)
               ∷ PK.pt (left b) (left∈C b b∈) ∷ PK.pt z z∈ ∷ PK.pt b b∈
               ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) ∣₁ ∣₁
      where
      t∈C : ⟨ pr (right b) a ∈ˢ C ⟩
      t∈C = mem z (pr (right b) a)
        (subst (λ w → ⟨ pr (right b) a ∈ˢ w ⟩) (sym e)
          (F0-spec (left b) (pr (right b) a) (pr (right b) a) .snd
            ∣ inr refl ∣₁)) z∈

  mem13-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem13 ⟩
            → ⟨ z ∈ˢ Fof op13 a b ⟩
  mem13-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape13 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op13 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) ⊨ᵐ shape13 ⟩
      → ⟨ z ∈ˢ Fof op13 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f13 a b))
      (F0-spec (left b) (pr (right b) a) z .snd (PT.map go hs))
      where
      go : (z ≡ l)
         ⊎ ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
              ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ PK.prAt f2 f0 f4 ⟩
         → (z ≡ left b) ⊎ (z ≡ pr (right b) a)
      go (inl e) = inl (subst (λ w → z ≡ w) el e)
      go (inr s) = inr (subst (λ w → z ≡ pr w a) er
        (PK.prAt-out f2 f0 f4
          (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
           ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) s))

  mem13-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op13 a b ⟩
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem13 ⟩
  mem13-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem13)) go
    (F0-spec (left b) (pr (right b) a) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f13 a b) h))
    where
    go : (z ≡ left b) ⊎ (z ≡ pr (right b) a)
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem13 ⟩
    go (inl e) = tupleIn shape13 z b a y z∈ b∈ a∈ y∈ ∣ inl e ∣₁
    go (inr e) = tupleIn shape13 z b a y z∈ b∈ a∈ y∈
      ∣ inr (PK.prAt-in f2 f0 f4
        (PK.pt (right b) (right∈C b b∈) ∷ PK.pt (left b) (left∈C b b∈)
         ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) ∣₁

  mem14-out : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem14 ⟩
            → ⟨ z ∈ˢ Fof op14 a b ⟩
  mem14-out z b a y z∈ b∈ a∈ y∈ h =
    tupleOut shape14 z b a y z∈ b∈ a∈ y∈ (z ∈ˢ Fof op14 a b) k h
    where
    k : (l r : S) (l∈ : ⟨ l ∈ˢ C ⟩) (r∈ : ⟨ r ∈ˢ C ⟩)
      → l ≡ left b → r ≡ right b
      → ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈
           ∷ PK.pt y y∈ ∷ []) ⊨ᵐ shape14 ⟩
      → ⟨ z ∈ˢ Fof op14 a b ⟩
    k l r l∈ r∈ el er hs = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (Fof-f14 a b))
      (F0-spec (left b) (pr a (right b)) z .snd (PT.map go hs))
      where
      go : (z ≡ l)
         ⊎ ⟨ (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
              ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ PK.prAt f2 f4 f0 ⟩
         → (z ≡ left b) ⊎ (z ≡ pr a (right b))
      go (inl e) = inl (subst (λ w → z ≡ w) el e)
      go (inr s) = inr (subst (λ w → z ≡ pr a w) er
        (PK.prAt-out f2 f4 f0
          (PK.pt r r∈ ∷ PK.pt l l∈ ∷ PK.pt z z∈ ∷ PK.pt b b∈
           ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) s))

  mem14-in : (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ⟨ z ∈ˢ Fof op14 a b ⟩
           → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem14 ⟩
  mem14-in z b a y z∈ b∈ a∈ y∈ h = PT.rec
    (snd ((PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem14)) go
    (F0-spec (left b) (pr a (right b)) z .fst
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (Fof-f14 a b) h))
    where
    go : (z ≡ left b) ⊎ (z ≡ pr a (right b))
       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ mem14 ⟩
    go (inl e) = tupleIn shape14 z b a y z∈ b∈ a∈ y∈ ∣ inl e ∣₁
    go (inr e) = tupleIn shape14 z b a y z∈ b∈ a∈ y∈
      ∣ inr (PK.prAt-in f2 f4 f0
        (PK.pt (right b) (right∈C b b∈) ∷ PK.pt (left b) (left∈C b b∈)
         ∷ PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) e) ∣₁
```

<!--en-->
## The dispatchers, and the graphs

Each membership formula becomes a graph by the equality frame: the value of the
operation at the two bound arguments is exactly the set the fourth variable
names, provided the value is a subset of the carrier, which the consumer always
has. The dispatchers `memOf`, `memOut` and `memIn` hand each operation its own
formula and its own two-way decode, and `graphOf` is the equality frame at
`memOf i`. The graph argument feeds the disjunction module below, whose
telescope this block closes.
<!--zh-->
## 分派器与诸图

每条隶属公式经等词框架成为一个图：该运算在两个受约束实参处的值恰是第四个变量所指的集合，前提是该值为载体的子集，而消费者总是持有这一条。分派器 `memOf`、`memOut` 与 `memIn` 把每条公式及其双向解码交给对应的运算，`graphOf` 就是在 `memOf i` 处的等词框架。诸图实参送入下文的析取模块，本块封上该模块的望远镜。
<!--ja-->
## ディスパッチャとグラフ

各帰属論理式は、等号フレームによってグラフになる。演算が二つの束縛された引数で取る値は、第四の変数が指す集合とちょうど一致する。ただし、その値が台の部分集合であることが条件であり、消費者は常にそれを持つ。ディスパッチャ `memOf`、`memOut`、`memIn` は、各演算に自分の式と双方向復号を渡す。`graphOf` は `memOf i` における等号フレームである。グラフの引数は後続の論理和モジュールに渡り、このブロックがそのモジュールのテレスコープを閉じる。
<!--/-->

```agda
  memOf : Op16 → Formula ⟪ C ⟫ 4
  memOf op0 = mem0
  memOf op1 = mem1
  memOf op2 = mem2
  memOf op3 = mem3
  memOf op4 = mem4
  memOf op5 = mem5
  memOf op6 = mem6
  memOf op7 = mem7
  memOf op8 = mem8
  memOf op9 = mem9
  memOf op10 = mem10
  memOf op11 = mem11
  memOf op12 = mem12
  memOf op13 = mem13
  memOf op14 = mem14
  memOf op15 = mem15

  memOut : (i : Op16) (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
           (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩)
         → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
             ⊨ᵐ memOf i ⟩
         → ⟨ z ∈ˢ Fof i a b ⟩
  memOut op0 = mem0-out
  memOut op1 = mem1-out
  memOut op2 = mem2-out
  memOut op3 = mem3-out
  memOut op4 = mem4-out
  memOut op5 = mem5-out
  memOut op6 = mem6-out
  memOut op7 = mem7-out
  memOut op8 = mem8-out
  memOut op9 = mem9-out
  memOut op10 = mem10-out
  memOut op11 = mem11-out
  memOut op12 = mem12-out
  memOut op13 = mem13-out
  memOut op14 = mem14-out
  memOut op15 = mem15-out

  memIn : (i : Op16) (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩)
          (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩)
        → ⟨ z ∈ˢ Fof i a b ⟩
        → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
            ⊨ᵐ memOf i ⟩
  memIn op0 = mem0-in
  memIn op1 = mem1-in
  memIn op2 = mem2-in
  memIn op3 = mem3-in
  memIn op4 = mem4-in
  memIn op5 = mem5-in
  memIn op6 = mem6-in
  memIn op7 = mem7-in
  memIn op8 = mem8-in
  memIn op9 = mem9-in
  memIn op10 = mem10-in
  memIn op11 = mem11-in
  memIn op12 = mem12-in
  memIn op13 = mem13-in
  memIn op14 = mem14-in
  memIn op15 = mem15-in

  graphOf : Op16 → Formula ⟪ C ⟫ 3
  graphOf i = eqFrame f2 (memOf i)

  graph-out : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩)
            → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
            → ⟨ (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ graphOf i ⟩
            → y ≡ Fof i a b
  graph-out i b a y b∈ a∈ y∈ sub h = eqFrame-out f2 (memOf i)
    (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) (Fof i a b) sub
    (λ v v∈ k → memOut i v b a y v∈ b∈ a∈ y∈ k)
    (λ v v∈ k → memIn i v b a y v∈ b∈ a∈ y∈ k) h

  graph-in : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
             (y∈ : ⟨ y ∈ˢ C ⟩)
           → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
           → y ≡ Fof i a b
           → ⟨ (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ graphOf i ⟩
  graph-in i b a y b∈ a∈ y∈ sub e = eqFrame-in f2 (memOf i)
    (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) (Fof i a b) sub
    (λ v v∈ k → memOut i v b a y v∈ b∈ a∈ y∈ k)
    (λ v v∈ k → memIn i v b a y v∈ b∈ a∈ y∈ k) e
```

<!--en-->
## The sixteen-way disjunction

The disjunction is assembled from the graphs, one branch per operation, and the
fold is the flat right-nested chain `graphOf op0 ∨̇ ... ∨̇ graphOf op15`. Its
decode is the two-way dispatch over the sixteen: the inward direction places a
graph reading at its branch, and the outward direction eliminates a branch by
the reading it carries. The graph argument stays abstract here, because the
graphs themselves arrive in a later block; this module is the landing site that
block instantiates.
<!--zh-->
## 十六路析取

析取由诸图装配，每个运算一支，折叠就是右嵌套的平链`graphOf op0 ∨̇ ... ∨̇ graphOf op15`。其解码是对十六支的双向分派：向内方向把图读式放进它的分支，向外方向按分支所携带的读式消去该分支。图实参此处保持抽象，因为诸图本身在后续块到达；本模块就是那个块所实例化的落点。
<!--ja-->
## 十六路の論理和

論理和はグラフから組み立てられ、演算ごとに一つの枝を持ち、折り畳みは右入れ子の平らな連鎖 `graphOf op0 ∨̇ ... ∨̇ graphOf op15` である。その復号は十六枝に対する双方向のディスパッチである。内向きの方向はグラフの読みをその枝に置き、外向きの方向は枝が運ぶ読みによってその枝を消去する。グラフ引数はここでは抽象のままである。グラフ自身は後のブロックで到着し、このモジュールがそのブロックのインスタンス化先である。
<!--/-->

```agda
  module BigOr (graphOf : Op16 → Formula ⟪ C ⟫ 3) where

    orTail0 orTail1 orTail2 orTail3 orTail4 orTail5 orTail6 orTail7 :
      Formula ⟪ C ⟫ 3
    orTail8 orTail9 orTail10 orTail11 orTail12 orTail13 orTail14 orTail15 :
      Formula ⟪ C ⟫ 3
    orTail0 = graphOf op0 ∨̇ orTail1
    orTail1 = graphOf op1 ∨̇ orTail2
    orTail2 = graphOf op2 ∨̇ orTail3
    orTail3 = graphOf op3 ∨̇ orTail4
    orTail4 = graphOf op4 ∨̇ orTail5
    orTail5 = graphOf op5 ∨̇ orTail6
    orTail6 = graphOf op6 ∨̇ orTail7
    orTail7 = graphOf op7 ∨̇ orTail8
    orTail8 = graphOf op8 ∨̇ orTail9
    orTail9 = graphOf op9 ∨̇ orTail10
    orTail10 = graphOf op10 ∨̇ orTail11
    orTail11 = graphOf op11 ∨̇ orTail12
    orTail12 = graphOf op12 ∨̇ orTail13
    orTail13 = graphOf op13 ∨̇ orTail14
    orTail14 = graphOf op14 ∨̇ orTail15
    orTail15 = graphOf op15

    bigOr : Formula ⟪ C ⟫ 3
    bigOr = orTail0

    bigOr-in : (i : Op16) (δ : Vec SM 3) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ δ ⊨ᵐ bigOr ⟩
    bigOr-in op0 δ h = ∣ inl h ∣₁
    bigOr-in op1 δ h = ∣ inr ∣ inl h ∣₁ ∣₁
    bigOr-in op2 δ h = ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁
    bigOr-in op3 δ h = ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op4 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op5 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op6 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op7 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op8 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op9 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op10 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op11 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op12 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op13 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op14 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op15 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

    orStep : (φ ψ : Formula ⟪ C ⟫ 3) (δ : Vec SM 3) (R : hProp (ℓ-suc ℓ))
           → (⟨ δ ⊨ᵐ φ ⟩ → ⟨ R ⟩) → (⟨ δ ⊨ᵐ ψ ⟩ → ⟨ R ⟩)
           → ⟨ δ ⊨ᵐ (φ ∨̇ ψ) ⟩ → ⟨ R ⟩
    orStep φ ψ δ R f g = PT.rec (snd R) (rec f g)

    bigOr-out : (δ : Vec SM 3) (R : hProp (ℓ-suc ℓ))
              → ((i : Op16) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ R ⟩)
              → ⟨ δ ⊨ᵐ bigOr ⟩ → ⟨ R ⟩
    bigOr-out δ R k = go0
      where
      go15 : ⟨ δ ⊨ᵐ orTail15 ⟩ → ⟨ R ⟩
      go15 = k op15
      go14 : ⟨ δ ⊨ᵐ orTail14 ⟩ → ⟨ R ⟩
      go14 h = orStep (graphOf op14) orTail15 δ R (k op14) go15 h
      go13 : ⟨ δ ⊨ᵐ orTail13 ⟩ → ⟨ R ⟩
      go13 h = orStep (graphOf op13) orTail14 δ R (k op13) go14 h
      go12 : ⟨ δ ⊨ᵐ orTail12 ⟩ → ⟨ R ⟩
      go12 h = orStep (graphOf op12) orTail13 δ R (k op12) go13 h
      go11 : ⟨ δ ⊨ᵐ orTail11 ⟩ → ⟨ R ⟩
      go11 h = orStep (graphOf op11) orTail12 δ R (k op11) go12 h
      go10 : ⟨ δ ⊨ᵐ orTail10 ⟩ → ⟨ R ⟩
      go10 h = orStep (graphOf op10) orTail11 δ R (k op10) go11 h
      go9 : ⟨ δ ⊨ᵐ orTail9 ⟩ → ⟨ R ⟩
      go9 h = orStep (graphOf op9) orTail10 δ R (k op9) go10 h
      go8 : ⟨ δ ⊨ᵐ orTail8 ⟩ → ⟨ R ⟩
      go8 h = orStep (graphOf op8) orTail9 δ R (k op8) go9 h
      go7 : ⟨ δ ⊨ᵐ orTail7 ⟩ → ⟨ R ⟩
      go7 h = orStep (graphOf op7) orTail8 δ R (k op7) go8 h
      go6 : ⟨ δ ⊨ᵐ orTail6 ⟩ → ⟨ R ⟩
      go6 h = orStep (graphOf op6) orTail7 δ R (k op6) go7 h
      go5 : ⟨ δ ⊨ᵐ orTail5 ⟩ → ⟨ R ⟩
      go5 h = orStep (graphOf op5) orTail6 δ R (k op5) go6 h
      go4 : ⟨ δ ⊨ᵐ orTail4 ⟩ → ⟨ R ⟩
      go4 h = orStep (graphOf op4) orTail5 δ R (k op4) go5 h
      go3 : ⟨ δ ⊨ᵐ orTail3 ⟩ → ⟨ R ⟩
      go3 h = orStep (graphOf op3) orTail4 δ R (k op3) go4 h
      go2 : ⟨ δ ⊨ᵐ orTail2 ⟩ → ⟨ R ⟩
      go2 h = orStep (graphOf op2) orTail3 δ R (k op2) go3 h
      go1 : ⟨ δ ⊨ᵐ orTail1 ⟩ → ⟨ R ⟩
      go1 h = orStep (graphOf op1) orTail2 δ R (k op1) go2 h
      go0 : ⟨ δ ⊨ᵐ orTail0 ⟩ → ⟨ R ⟩
      go0 h = orStep (graphOf op0) orTail1 δ R (k op0) go1 h
```

<!--en-->
## The step formula, and the theorem

The formula is assembled at the argument of the step: the two floor clauses
take the set as a constant, and the image clause binds the two arguments,
tests each against the set and itself, and hands them to the sixteen graphs.
Both directions of the description are the step's own membership
characterization read off arm by arm; nothing else enters. The theorem then
places the step in the next stage, because a definable subset of a stage is a
member of the stage above it.
<!--zh-->
## step 公式，与定理

公式在 step 的实参处装配：两条地板子句把该集合取作常量，像子句约束两个实参、分别对该集合及其自身作检验，再交给十六个图。描述的两个方向都是 step 自身的隶属刻画逐臂读出，别无其他。定理随之把该步安放进下一阶段，因为一个阶段的可定义子集是其上一阶段的成员。
<!--ja-->
## step の式、そして定理

式は step の実引数のところで組み立てられる。二つの床の節がその集合を定数として取り、像の節が二つの実引数を束縛し、それぞれをその集合とそれ自身に対して検査し、十六個のグラフへ渡す。記述の二つの方向は、step 自身の帰属の特徴づけを腕ごとに読み出したものであり、他には何も入らない。定理はその step を次の段階に置く。ある段階の可定義部分集合は、その上の段階のメンバーだからである。
<!--/-->

```agda
  module AtStep (u : S) (mu : ⟪ C ⟫) (qu : ⟪ C ⟫↪ mu ≡ u)
                (stepSub : (v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ C ⟩) where

    module B = BigOr graphOf
    module D = Desc C Ctr

    u∈C : ⟨ u ∈ˢ C ⟩
    u∈C = stepSub u (step-in-self u)

    argIn : (c : S) → (⟨ c ∈ˢ u ⟩ ⊎ (c ≡ u)) → ⟨ c ∈ˢ C ⟩
    argIn c (inl h) = mem u c h u∈C
    argIn c (inr e) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym e) u∈C

    argIn' : (c : S) → (⟨ c ∈ˢ u ⟩ ⊎ (c ≡ u)) → ⟨ c ∈ˢ u' u ⟩
    argIn' c (inl h) = u'-in u c h
    argIn' c (inr e) = subst (λ w → ⟨ w ∈ˢ u' u ⟩) (sym e) (u-self-in u)

    inU : {n : ℕ} → Fin n → Formula ⟪ C ⟫ n
    inU k = (var k ∈̇ con mu) ∨̇ (var k ≐ con mu)

    inU-out : {n : ℕ} (k : Fin n) (δ : Vec SM n)
            → ⟨ δ ⊨ᵐ inU k ⟩
            → ∥ (⟨ fst (lookup k δ) ∈ˢ u ⟩ ⊎ (fst (lookup k δ) ≡ u)) ∥₁
    inU-out k δ h = PT.map go h
      where
      go : ⟨ fst (lookup k δ) ∈ˢ ⟪ C ⟫↪ mu ⟩
           ⊎ (fst (lookup k δ) ≡ ⟪ C ⟫↪ mu)
         → ⟨ fst (lookup k δ) ∈ˢ u ⟩ ⊎ (fst (lookup k δ) ≡ u)
      go (inl m) = inl (subst (λ w → ⟨ fst (lookup k δ) ∈ˢ w ⟩) qu m)
      go (inr e) = inr (e ∙ qu)

    inU-in : {n : ℕ} (k : Fin n) (δ : Vec SM n)
           → (⟨ fst (lookup k δ) ∈ˢ u ⟩ ⊎ (fst (lookup k δ) ≡ u))
           → ⟨ δ ⊨ᵐ inU k ⟩
    inU-in k δ (inl m) =
      ∣ inl (subst (λ w → ⟨ fst (lookup k δ) ∈ˢ w ⟩) (sym qu) m) ∣₁
    inU-in k δ (inr e) = ∣ inr (e ∙ sym qu) ∣₁

    imgForm : Formula ⟪ C ⟫ 1
    imgForm = ∃̇ (∃̇ (inU f1 ∧̇ (inU f0 ∧̇ B.bigOr)))

    stepForm : Formula ⟪ C ⟫ 1
    stepForm = inU f0 ∨̇ imgForm

    valueSub : (i : Op16) (a b v : S) → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u))
             → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u)) → (w : S) → ⟨ w ∈ˢ Fof i a b ⟩
             → ⟨ w ∈ˢ C ⟩
    valueSub i a b v sa sb w hw = mem (Fof i a b) w hw
      (stepSub (Fof i a b)
        (step-in-img u (Fof i a b) i a b (argIn' a sa) (argIn' b sb) refl))

    din : (v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ step u ⟩
        → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ stepForm ⟩
    din v v∈ h = PT.rec (snd ((PK.pt v v∈ ∷ []) ⊨ᵐ stepForm)) go
      (step-out u v h)
      where
      go : StepArm u v → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ stepForm ⟩
      go (arm-member m) = ∣ inl (inU-in f0 (PK.pt v v∈ ∷ []) (inl m)) ∣₁
      go (arm-self e) = ∣ inl (inU-in f0 (PK.pt v v∈ ∷ []) (inr e)) ∣₁
      go (arm-image i a b sa sb e) =
        ∣ inr ∣ PK.pt a (argIn a sa) , ∣ PK.pt b (argIn b sb)
          , (inU-in f1
              (PK.pt b (argIn b sb) ∷ PK.pt a (argIn a sa) ∷ PK.pt v v∈ ∷ [])
              sa
            , (inU-in f0
                (PK.pt b (argIn b sb) ∷ PK.pt a (argIn a sa) ∷ PK.pt v v∈
                 ∷ []) sb
              , B.bigOr-in i
                  (PK.pt b (argIn b sb) ∷ PK.pt a (argIn a sa)
                   ∷ PK.pt v v∈ ∷ [])
                  (graph-in i b a v (argIn b sb) (argIn a sa) v∈
                    (valueSub i a b v sa sb) e))) ∣₁ ∣₁ ∣₁

    dout : (v : S) (v∈ : ⟨ v ∈ˢ C ⟩)
         → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ stepForm ⟩ → ⟨ v ∈ˢ step u ⟩
    dout v v∈ h = PT.rec (snd (v ∈ˢ step u)) branch h
      where
      floor : ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ inU f0 ⟩ → ⟨ v ∈ˢ step u ⟩
      floor hf = PT.rec (snd (v ∈ˢ step u)) go
        (inU-out f0 (PK.pt v v∈ ∷ []) hf)
        where
        go : (⟨ v ∈ˢ u ⟩ ⊎ (v ≡ u)) → ⟨ v ∈ˢ step u ⟩
        go (inl m) = step-in u v m
        go (inr e) =
          subst (λ w → ⟨ w ∈ˢ step u ⟩) (sym e) (step-in-self u)
      img : ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ imgForm ⟩ → ⟨ v ∈ˢ step u ⟩
      img hi = PT.rec (snd (v ∈ˢ step u)) k0 hi
        where
        k0 : Σ[ am ∈ SM ]
               ⟨ (am ∷ PK.pt v v∈ ∷ []) ⊨ᵐ
                 (∃̇ (inU f1 ∧̇ (inU f0 ∧̇ B.bigOr))) ⟩
           → ⟨ v ∈ˢ step u ⟩
        k0 (am , h1) = PT.rec (snd (v ∈ˢ step u)) k1 h1
          where
          k1 : Σ[ bm ∈ SM ]
                 ⟨ ((bm ∷ am ∷ PK.pt v v∈ ∷ []) ⊨ᵐ inU f1)
                   ⊓ (((bm ∷ am ∷ PK.pt v v∈ ∷ []) ⊨ᵐ inU f0)
                     ⊓ ((bm ∷ am ∷ PK.pt v v∈ ∷ []) ⊨ᵐ B.bigOr)) ⟩
             → ⟨ v ∈ˢ step u ⟩
          k1 (bm , (ha , (hb , hor))) =
            PT.rec (snd (v ∈ˢ step u)) k2
              (inU-out f1 (bm ∷ am ∷ PK.pt v v∈ ∷ []) ha)
            where
            k2 : (⟨ fst am ∈ˢ u ⟩ ⊎ (fst am ≡ u)) → ⟨ v ∈ˢ step u ⟩
            k2 sa = PT.rec (snd (v ∈ˢ step u)) k3
              (inU-out f0 (bm ∷ am ∷ PK.pt v v∈ ∷ []) hb)
              where
              k3 : (⟨ fst bm ∈ˢ u ⟩ ⊎ (fst bm ≡ u)) → ⟨ v ∈ˢ step u ⟩
              k3 sb = B.bigOr-out (bm ∷ am ∷ PK.pt v v∈ ∷ [])
                        (v ∈ˢ step u) k4 hor
                where
                k4 : (i : Op16)
                   → ⟨ (bm ∷ am ∷ PK.pt v v∈ ∷ []) ⊨ᵐ graphOf i ⟩
                   → ⟨ v ∈ˢ step u ⟩
                k4 i hg = step-in-img u v i (fst am) (fst bm)
                  (argIn' (fst am) sa) (argIn' (fst bm) sb)
                  (graph-out i (fst bm) (fst am) v (snd bm) (snd am) v∈
                    (valueSub i (fst am) (fst bm) v sa sb) hg)
      branch : ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ inU f0 ⟩
             ⊎ ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ imgForm ⟩
             → ⟨ v ∈ˢ step u ⟩
      branch (inl hf) = floor hf
      branch (inr hi) = img hi

    stepSet-desc : DefOf.defSet C stepForm ≡ step u
    stepSet-desc = D.described stepForm (step u) stepSub din dout
```

<!--en-->
## The description reading of the graph layer

The layer's membership formulas also read as descriptions. Take the formula
`memOf i` at the four-slot environment; fix its second argument slot to the
carrier's fiber of `b` and its first argument slot to the carrier's fiber of
`a`; re-connect the member slot to the free tail variable; and bind the
member and the two arguments by three existentials. The resulting formula
carves exactly the value `Fof i a b`, on the premise that every member of
that value lies in the carrier: the caller's subset certificate is that
premise, passed through unchanged. The frame is generic in the operation,
so the sixteen equations are one generic statement and sixteen instances,
each closing through the operation's own read lemma. The pairing arm is the
one exception. Its membership formula is an equality disjunction, so its
equation needs no layer at all; it lives below the layer in `L.TowerKit`,
where the tower's pairing fact reads it.
<!--zh-->
## 图层的描述读法

图层的隶属公式也可以当作描述来读。取四槽环境处的公式 `memOf i`；把第二个实参槽固定到载体中 `b` 的纤维，把第一个实参槽固定到载体中 `a` 的纤维；把成员槽重新接到自由的尾部变量；再用三个存在量词把成员与两个实参绑起。所得公式恰好刻出值 `Fof i a b`，前提是那个值的每个成员都落在载体里：调用方的子集证书就是该前提，原样穿过。框架对运算泛型，故十六条等式是一条泛型陈述加十六条实例，每条都经该运算自己的读引理收口。配对臂是唯一的例外。它的隶属公式是一道等式析取，故其等式完全不需要图层；它住在图层之下的 `L.TowerKit` 里，塔的配对事实在那里读它。
<!--ja-->
## グラフレイヤーの記述としての読み

グラフレイヤーの帰属論理式は、記述としても読める。四スロット環境における式 `memOf i` を取り、第二引数スロットを台における `b` のファイバーに固定し、第一引数スロットを台における `a` のファイバーに固定し、メンバースロットを自由な末尾変数に結び直し、三つの存在量化子でメンバーと二つの引数を束縛する。得られる式は値 `Fof i a b` をちょうど刻む。ただし、その値のすべてのメンバーが台にあることを前提とする。呼び出し側の部分集合証明書がその前提であり、そのまま通される。フレームは演算について汎用である。したがって、十六個の等式は一つの汎用ステートメントと十六個のインスタンスからなり、各インスタンスはその演算自身の読み補題で閉じる。対の腕が唯一の例外である。その帰属論理式は等号の論理和なので、その等式はレイヤーをまったく必要としない。それはレイヤーの下の `L.TowerKit` にあり、塔の対の事実がそこでそれを読む。
<!--/-->

```agda
module PinFrame (C : S) (Ctr : isTransV C) (mA : ⟪ C ⟫)
                (qA : ⟪ C ⟫↪ mA ≡ A) (∅∈C : ⟨ ∅ ∈ˢ C ⟩)
                (a b : S) (a∈ : ⟨ a ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) where

  module L = Layer C Ctr mA qA ∅∈C
  module D = Desc C Ctr
  open L public

  private
    f0 : {n : ℕ} → Fin (suc n)
    f0 = zero
    f1 : {n : ℕ} → Fin (suc (suc n))
    f1 = suc f0
    f2 : {n : ℕ} → Fin (suc (suc (suc n)))
    f2 = suc f1
    f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
    f3 = suc f2

  mₐ : ⟪ C ⟫
  mₐ = ∈-asFiber {a = a} {b = C} a∈ .fst
  qₐ : ⟪ C ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = C} a∈ .snd
  m_b : ⟪ C ⟫
  m_b = ∈-asFiber {a = b} {b = C} b∈ .fst
  q_b : ⟪ C ⟫↪ m_b ≡ b
  q_b = ∈-asFiber {a = b} {b = C} b∈ .snd

  body : (i : Op16) → Formula ⟪ C ⟫ 4
  body i = (var f0 ≐ var f3) ∧̇
    ((var f1 ≐ con m_b) ∧̇ ((var f2 ≐ con mₐ) ∧̇ L.memOf i))

  pinned : (i : Op16) → Formula ⟪ C ⟫ 1
  pinned i = ∃̇ (∃̇ (∃̇ body i))

  pinned-out : (i : Op16) (v : S) (v∈ : ⟨ v ∈ˢ C ⟩)
             → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ pinned i ⟩ → ⟨ v ∈ˢ Fof i a b ⟩
  pinned-out i v v∈ h = PT.rec (snd (v ∈ˢ Fof i a b)) k2 h
    where
    k2 : Σ[ x₂ ∈ SM ] ⟨ (x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ (∃̇ (∃̇ body i)) ⟩
       → ⟨ v ∈ˢ Fof i a b ⟩
    k2 (x₂ , h₂) = PT.rec (snd (v ∈ˢ Fof i a b)) k1 h₂
      where
      k1 : Σ[ x₁ ∈ SM ] ⟨ (x₁ ∷ x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ (∃̇ body i) ⟩
         → ⟨ v ∈ˢ Fof i a b ⟩
      k1 (x₁ , h₁) = PT.rec (snd (v ∈ˢ Fof i a b)) k0 h₁
        where
        k0 : Σ[ x₀ ∈ SM ] ⟨ (x₀ ∷ x₁ ∷ x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ body i ⟩
           → ⟨ v ∈ˢ Fof i a b ⟩
        k0 (x₀ , h₀) = subst (λ w → ⟨ w ∈ˢ Fof i a b ⟩) p0
          (subst (λ t → ⟨ fst x₀ ∈ˢ Fof i a t ⟩) (p1 ∙ q_b)
            (subst (λ t → ⟨ fst x₀ ∈ˢ Fof i t (fst x₁) ⟩) (p2 ∙ qₐ) z∈F))
          where
          p0 : fst x₀ ≡ v
          p0 = h₀ .fst
          p1 : fst x₁ ≡ ⟪ C ⟫↪ m_b
          p1 = h₀ .snd .fst
          p2 : fst x₂ ≡ ⟪ C ⟫↪ mₐ
          p2 = h₀ .snd .snd .fst
          ms : ⟨ (x₀ ∷ x₁ ∷ x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ L.memOf i ⟩
          ms = h₀ .snd .snd .snd
          z∈F : ⟨ fst x₀ ∈ˢ Fof i (fst x₂) (fst x₁) ⟩
          z∈F = L.memOut i (fst x₀) (fst x₁) (fst x₂) v
            (snd x₀) (snd x₁) (snd x₂) v∈ ms

  pinned-in : (i : Op16) (v : S) (v∈ : ⟨ v ∈ˢ C ⟩)
            → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ pinned i ⟩
  pinned-in i v v∈ h =
    ∣ PK.pt a a∈ , (∣ PK.pt b b∈ , (∣ PK.pt v v∈ , (pin₀ , (pin₁ , (pin₂ , ms))) ∣₁) ∣₁) ∣₁
    where
    pin₀ : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
             ⊨ᵐ (var f0 ≐ var f3) ⟩
    pin₀ = refl
    pin₁ : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
             ⊨ᵐ (var f1 ≐ con m_b) ⟩
    pin₁ = sym q_b
    pin₂ : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
             ⊨ᵐ (var f2 ≐ con mₐ) ⟩
    pin₂ = sym qₐ
    ms : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
           ⊨ᵐ L.memOf i ⟩
    ms = L.memIn i v b a v v∈ b∈ a∈ v∈ h

  -- The generic equation, in Bridge's Arm shape: the caller's subset
  -- certificate is the wsub input, so no per-op membership analysis enters
  -- the frame.
  Fof-defSet≡ : (i : Op16) (sub : (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
              → L.defSet (pinned i) ≡ Fof i a b
  Fof-defSet≡ i sub = D.described (pinned i) (Fof i a b) sub
    (λ v v∈ h → pinned-in i v v∈ h)
    (λ v v∈ h → pinned-out i v v∈ h)

  -- The pairing arm: layer-free (L.TowerKit), because the pairing fact
  -- below the layer cannot instantiate Layer.  Its formula matches
  -- pinned op0 definitionally, so the home's equation is the instance.
  module FA = F0Arm C Ctr a b a∈ b∈
  F0-defSet≡ : L.defSet (pinned op0) ≡ F0 a b
  F0-defSet≡ = FA.F0-defSet≡

  -- The closed arms: the membership analysis reads back through the
  -- operation's specification, and the carrier's transitivity places the
  -- member.  F1 and F5 read through their specifications, F6 through its
  -- read lemma's left projection, F10 through its ordered-pair projection,
  -- and F15 through the relativization slot's own membership.
  wsub1 : (v : S) → ⟨ v ∈ˢ Fof op1 a b ⟩ → ⟨ v ∈ˢ C ⟩
  wsub1 v h = Ctr {x = a} {y = v} v∈a a∈
    where
    v∈a : ⟨ v ∈ˢ a ⟩
    v∈a = F1-spec a b v .fst (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f1 a b) h) .fst

  F1-defSet≡ : L.defSet (pinned op1) ≡ F1 a b
  F1-defSet≡ = Fof-defSet≡ op1 wsub1 ∙ Fof-f1 a b

  wsub5 : (v : S) → ⟨ v ∈ˢ Fof op5 a b ⟩ → ⟨ v ∈ˢ C ⟩
  wsub5 v h = PT.rec (snd (v ∈ˢ C)) go
    (F5-spec a b v .fst (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f5 a b) h))
    where
    go : Σ[ w ∈ S ] ⟨ (w ∈ˢ a) ⊓ (v ∈ˢ w) ⟩ → ⟨ v ∈ˢ C ⟩
    go (w , w∈a , v∈w) = Ctr {x = w} {y = v} v∈w (Ctr {x = a} {y = w} w∈a a∈)

  F5-defSet≡ : L.defSet (pinned op5) ≡ F5 a b
  F5-defSet≡ = Fof-defSet≡ op5 wsub5 ∙ Fof-f5 a b

  wsub6 : (v : S) → ⟨ v ∈ˢ Fof op6 a b ⟩ → ⟨ v ∈ˢ C ⟩
  wsub6 v h = PT.rec (snd (v ∈ˢ C)) go
    (F6-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f6 a b) h))
    where
    go : Σ[ u ∈ S ] Σ[ w ∈ S ] (⟨ pr u w ∈ˢ a ⟩ × ⟨ v ≡ₕ u ⟩) → ⟨ v ∈ˢ C ⟩
    go (u , w , pr∈a , e) = subst (λ t → ⟨ t ∈ˢ C ⟩) (sym e)
      (PM.pair-left {a = u} {b = w} (Ctr {x = a} {y = pr u w} pr∈a a∈))

  F6-defSet≡ : L.defSet (pinned op6) ≡ F6 a b
  F6-defSet≡ = Fof-defSet≡ op6 wsub6 ∙ Fof-f6 a b

  wsub10 : (v : S) → ⟨ v ∈ˢ Fof op10 a b ⟩ → ⟨ v ∈ˢ C ⟩
  wsub10 v h = PM.pair-right {a = b} {b = v} (Ctr {x = a} {y = pr b v}
    (subst ⟨_⟩ (F10-spec a b v)
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f10 a b) h)) a∈)

  F10-defSet≡ : L.defSet (pinned op10) ≡ F10 a b
  F10-defSet≡ = Fof-defSet≡ op10 wsub10 ∙ Fof-f10 a b

  module F15C = F15Of A

  wsub15 : (v : S) → ⟨ v ∈ˢ Fof op15 a b ⟩ → ⟨ v ∈ˢ C ⟩
  wsub15 v h = Ctr {x = a} {y = v} v∈a a∈
    where
    v∈a : ⟨ v ∈ˢ a ⟩
    v∈a = subst ⟨_⟩ (F15C.F15-spec a v)
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f15 a b) h) .fst

  F15-defSet≡ : L.defSet (pinned op15) ≡ F15A a
  F15-defSet≡ = Fof-defSet≡ op15 wsub15 ∙ Fof-f15 a b

  -- The open arms: a member of the value is not in the carrier by the
  -- specification alone (a pair, a singleton, a projection, a slice, or an
  -- ordered-pair value needs the carrier's own closure), so the caller's
  -- subset certificate is an argument of the instance and passes through.
  F2-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op2 a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → L.defSet (pinned op2) ≡ F2 a b
  F2-defSet≡ sub = Fof-defSet≡ op2 sub ∙ Fof-f2 a b

  F3-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op3 a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → L.defSet (pinned op3) ≡ F3 a b
  F3-defSet≡ sub = Fof-defSet≡ op3 sub ∙ Fof-f3 a b

  F4-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op4 a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → L.defSet (pinned op4) ≡ F4 a b
  F4-defSet≡ sub = Fof-defSet≡ op4 sub ∙ Fof-f4 a b

  F7-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op7 a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → L.defSet (pinned op7) ≡ F7 a b
  F7-defSet≡ sub = Fof-defSet≡ op7 sub ∙ Fof-f7 a b

  F8-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op8 a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → L.defSet (pinned op8) ≡ F8 a b
  F8-defSet≡ sub = Fof-defSet≡ op8 sub ∙ Fof-f8 a b

  F9-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op9 a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → L.defSet (pinned op9) ≡ F9 a b
  F9-defSet≡ sub = Fof-defSet≡ op9 sub ∙ Fof-f9 a b

  F11-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op11 a b ⟩ → ⟨ v ∈ˢ C ⟩)
              → L.defSet (pinned op11) ≡ F11 a b
  F11-defSet≡ sub = Fof-defSet≡ op11 sub ∙ Fof-f11 a b

  F12-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op12 a b ⟩ → ⟨ v ∈ˢ C ⟩)
              → L.defSet (pinned op12) ≡ F12 a b
  F12-defSet≡ sub = Fof-defSet≡ op12 sub ∙ Fof-f12 a b

  F13-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op13 a b ⟩ → ⟨ v ∈ˢ C ⟩)
              → L.defSet (pinned op13) ≡ F13 a b
  F13-defSet≡ sub = Fof-defSet≡ op13 sub ∙ Fof-f13 a b

  F14-defSet≡ : ((v : S) → ⟨ v ∈ˢ Fof op14 a b ⟩ → ⟨ v ∈ˢ C ⟩)
              → L.defSet (pinned op14) ≡ F14 a b
  F14-defSet≡ sub = Fof-defSet≡ op14 sub ∙ Fof-f14 a b
```

<!--en-->
## The sixteen values, over an abstract offset

The members of a one-step value are read operation by operation, and every
read lands in one of five shapes: a member of the carrier, an unordered pair
of two members, a Kuratowski pair, a Kuratowski pair nested once, and one
image slice. The offsets are therefore stated abstractly, as a telescope of
closure facts over three carriers, and instantiated once at the tower.
Nothing in this module mentions a stage, which is what keeps the sixteen
goal types free of the successor tower.
<!--zh-->
## 十六个值，在抽象偏移之上

单步值的诸成员逐运算读出，而每次读取都落进五种形状之一：载体的一个成员、两个成员的无序对、一个 Kuratowski 对、一次嵌套的 Kuratowski 对，以及一个切片。故偏移抽象地陈述，作为三个载体之上若干闭包事实的望远镜，只在塔处实例化一次。本模块不提及任何阶段，这正是让十六个目标类型不沾后继塔的办法。
<!--ja-->
## 十六個の値、抽象的なオフセットの上で

単段階の値のメンバーは演算ごとに読み出され、その読みは常に五つの形のいずれかに落ちる。すなわち、台のメンバー、二つのメンバーの非順序対、クーラトフスキー対、一度入れ子になったクーラトフスキー対、そして一つの像スライスである。したがってオフセットは抽象的に述べられる。すなわち、三つの台にわたる閉包事実のテレスコープとして述べられ、塔のところで一度だけインスタンス化される。このモジュールは段階を一切言及しない。それが、十六個の目標型を後継の塔から遠ざけておく方法である。
<!--/-->

```agda
module Values (C P T : S)
  (Ctr : isTransV C)
  (sub : (x : S) → ⟨ x ∈ˢ C ⟩ → ⟨ x ∈ˢ P ⟩)
  (up : (x : S) → ⟨ x ∈ˢ P ⟩ → ⟨ x ∈ˢ T ⟩)
  (pairIn : (p q : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩ → ⟨ F0 p q ∈ˢ T ⟩)
  (prIn : (p q : S) → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩ → ⟨ pr p q ∈ˢ T ⟩)
  (prIn₂ : (p q r : S) → ⟨ p ∈ˢ C ⟩ → ⟨ q ∈ˢ C ⟩ → ⟨ r ∈ˢ C ⟩
         → ⟨ pr p (pr q r) ∈ˢ T ⟩)
  (pairPrIn : (l p q : S) → ⟨ l ∈ˢ P ⟩ → ⟨ p ∈ˢ P ⟩ → ⟨ q ∈ˢ P ⟩
            → ⟨ F0 l (pr p q) ∈ˢ T ⟩)
  (sliceIn : (x y : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → ⟨ F10 x y ∈ˢ T ⟩)
  (∅∈P : ⟨ ∅ ∈ˢ P ⟩)
  where

  module PM = PairMem C Ctr

  mem : (x y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
  mem x y y∈x x∈C = Ctr {x = x} {y = y} y∈x x∈C

  left-read : (b : S) → ⟨ b ∈ˢ C ⟩ → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
  left-read b b∈ = atPair (lem (isPair b))
    where
    atPair : ⟨ isPair b ⟩ ⊎ (⟨ isPair b ⟩ → Empty.⊥)
           → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
    atPair (inl h) = inl (PT.rec (snd (left b ∈ˢ C)) go h)
      where
      go : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ left b ∈ˢ C ⟩
      go (p , q , b≡) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym left≡p)
        (PM.pair-left {a = p} {b = q} (subst (λ w → ⟨ w ∈ˢ C ⟩) b≡ b∈))
        where
        left≡p : left b ≡ p
        left≡p = subst (λ w → left w ≡ p) (sym b≡) (left-spec p q)
    atPair (inr _) = atCap (lem (∃[ c ] (c ∈ₛ ⋂ b)))
      where
      atCap : ⟨ ∃[ c ] (c ∈ₛ ⋂ b) ⟩ ⊎ (⟨ ∃[ c ] (c ∈ₛ ⋂ b) ⟩ → Empty.⊥)
            → (⟨ left b ∈ˢ C ⟩ ⊎ (left b ≡ ∅))
      atCap (inl e) = inl (PT.rec (snd (left b ∈ˢ C)) go e)
        where
        go : Σ[ c ∈ S ] ⟨ c ∈ₛ ⋂ b ⟩ → ⟨ left b ∈ˢ C ⟩
        go (c , c∈⋂) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym (left-⋂-collapse b c c∈⋂))
          (PT.rec (snd (c ∈ˢ C)) inC (∈∈ₛ {a = c} {b = ⋂ b} .snd c∈⋂))
          where
          inC : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ]
                      ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
                  (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
              → ⟨ c ∈ˢ C ⟩
          inC (p , _) = mem w c c∈w w∈C
            where
            w : S
            w = ⟪ b ⟫↪ (p .fst)
            w∈C : ⟨ w ∈ˢ C ⟩
            w∈C = mem b w (∈∈ₛ {a = w} {b = b} .snd (∈ₛ⟪ b ⟫↪ (p .fst))) b∈
            c∈w : ⟨ c ∈ˢ w ⟩
            c∈w = ∈∈ₛ {a = c} {b = w} .snd
              (⋂-member-in-all b c w c∈⋂ (∈ₛ⟪ b ⟫↪ (p .fst)))
      atCap (inr no) = inr (left-⋂-empty b (λ c h → no ∣ c , h ∣₁))

  right-read : (b : S) → ⟨ b ∈ˢ C ⟩ → (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅))
  right-read b b∈ = atPair (lem (isPair b))
    where
    atPair : ⟨ isPair b ⟩ ⊎ (⟨ isPair b ⟩ → Empty.⊥)
           → (⟨ right b ∈ˢ C ⟩ ⊎ (right b ≡ ∅))
    atPair (inl h) = inl (PT.rec (snd (right b ∈ˢ C)) go h)
      where
      go : Σ[ p ∈ S ] Σ[ q ∈ S ] ⟨ b ≡ₕ pr p q ⟩ → ⟨ right b ∈ˢ C ⟩
      go (p , q , b≡) = subst (λ w → ⟨ w ∈ˢ C ⟩) (sym (right-at-pair b p q b≡))
        (PM.pair-right {a = p} {b = q} (subst (λ w → ⟨ w ∈ˢ C ⟩) b≡ b∈))
    atPair (inr nb) = inr (right-nonpair b (λ p q e → nb ∣ p , q , e ∣₁))

  inP : (b : S) → (⟨ b ∈ˢ C ⟩ ⊎ (b ≡ ∅)) → ⟨ b ∈ˢ P ⟩
  inP b (inl h) = sub b h
  inP b (inr e) = subst (λ w → ⟨ w ∈ˢ P ⟩) (sym e) ∅∈P

  module F15C = F15Of A

  valueMem : (i : Op16) (a b : S) → ⟨ a ∈ˢ C ⟩ → ⟨ b ∈ˢ C ⟩
           → (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ T ⟩
  valueMem op0 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec a b v .fst (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f0 a b) h))
    where
    go : (v ≡ a) ⊎ (v ≡ b) → ⟨ v ∈ˢ T ⟩
    go (inl e) = up v (subst (λ w → ⟨ w ∈ˢ P ⟩) (sym e) (sub a a∈))
    go (inr e) = up v (subst (λ w → ⟨ w ∈ˢ P ⟩) (sym e) (sub b b∈))
  valueMem op1 a b a∈ b∈ v h = up v (sub v
    (mem a v (F1-spec a b v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f1 a b) h) .fst) a∈))
  valueMem op2 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F2-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f2 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p q ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , q , p∈a , q∈b , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn p q (sub p (mem a p p∈a a∈)) (sub q (mem b q q∈b b∈)))
  valueMem op3 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F3-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f3 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ z ∈ S ] Σ[ q ∈ S ]
           (⟨ z ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p (pr z q) ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , z , q , z∈a , pq∈b , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn₂ p z q (PM.pair-left {a = p} {b = q}
        (mem b (pr p q) pq∈b b∈))
        (mem a z z∈a a∈) (PM.pair-right {a = p} {b = q}
          (mem b (pr p q) pq∈b b∈)))
  valueMem op4 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F4-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f4 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] Σ[ z ∈ S ]
           (⟨ z ∈ˢ a ⟩ × ⟨ pr p q ∈ˢ b ⟩ × ⟨ v ≡ₕ pr p (pr q z) ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , q , z , z∈a , pq∈b , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn₂ p q z (PM.pair-left {a = p} {b = q}
        (mem b (pr p q) pq∈b b∈))
        (PM.pair-right {a = p} {b = q}
          (mem b (pr p q) pq∈b b∈)) (mem a z z∈a a∈))
  valueMem op5 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F5-spec a b v .fst (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f5 a b) h))
    where
    go : Σ[ w ∈ S ] ⟨ (w ∈ˢ a) ⊓ (v ∈ˢ w) ⟩ → ⟨ v ∈ˢ T ⟩
    go (w , w∈a , v∈w) = up v (sub v (mem w v v∈w (mem a w w∈a a∈)))
  valueMem op6 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F6-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f6 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ] (⟨ pr p q ∈ˢ a ⟩ × ⟨ v ≡ₕ p ⟩) → ⟨ v ∈ˢ T ⟩
    go (p , q , pq∈a , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (up p (sub p (PM.pair-left {a = p} {b = q}
        (mem a (pr p q) pq∈a a∈))))
  valueMem op7 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F7-read a b v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f7 a b) h))
    where
    go : Σ[ p ∈ S ] Σ[ q ∈ S ]
           (⟨ p ∈ˢ a ⟩ × ⟨ q ∈ˢ a ⟩ × ⟨ p ∈ˢ q ⟩ × ⟨ v ≡ₕ pr p q ⟩)
       → ⟨ v ∈ˢ T ⟩
    go (p , q , p∈a , q∈a , _ , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn p q (sub p (mem a p p∈a a∈)) (sub q (mem a q q∈a a∈)))
  valueMem op8 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (subst ⟨_⟩ (F8-spec a b v) (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f8 a b) h))
    where
    go : Σ[ m ∈ ⟪ b ⟫ ] (F10 a (⟪ b ⟫↪ m) ≡ v) → ⟨ v ∈ˢ T ⟩
    go (m , e) = subst (λ w → ⟨ w ∈ˢ T ⟩) e
      (sliceIn a (⟪ b ⟫↪ m) a∈
        (mem b (⟪ b ⟫↪ m) (∈∈ₛ {a = ⟪ b ⟫↪ m} {b = b} .snd
          (∈ₛ⟪ b ⟫↪ m)) b∈))
  valueMem op9 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (⁅ a ⁆s) (⁅ a , b ⁆) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f9 a b) h))
    where
    go : (v ≡ ⁅ a ⁆s) ⊎ (v ≡ ⁅ a , b ⁆) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym (e ∙ singl≡pair a))
      (pairIn a a (sub a a∈) (sub a a∈))
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (pairIn a b (sub a a∈) (sub b b∈))
  valueMem op10 a b a∈ b∈ v h = up v (sub v
    (PM.pair-right {a = b} {b = v} (mem a (pr b v)
      (subst ⟨_⟩ (F10-spec a b v)
        (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f10 a b) h)) a∈)))
  valueMem op11 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr a (right b) ⁆) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f11 a b) h))
    where
    l∈ : ⟨ left b ∈ˢ P ⟩
    l∈ = inP (left b) (left-read b b∈)
    r∈ : ⟨ right b ∈ˢ P ⟩
    r∈ = inP (right b) (right-read b b∈)
    go : (v ≡ ⁅ left b ⁆s) ⊎ (v ≡ ⁅ left b , pr a (right b) ⁆)
       → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym (e ∙ singl≡pair (left b)))
      (pairIn (left b) (left b) l∈ l∈)
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (pairPrIn (left b) a (right b) l∈ (sub a a∈) r∈)
  valueMem op12 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (⁅ left b ⁆s) (⁅ left b , pr (right b) a ⁆) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f12 a b) h))
    where
    l∈ : ⟨ left b ∈ˢ P ⟩
    l∈ = inP (left b) (left-read b b∈)
    r∈ : ⟨ right b ∈ˢ P ⟩
    r∈ = inP (right b) (right-read b b∈)
    go : (v ≡ ⁅ left b ⁆s) ⊎ (v ≡ ⁅ left b , pr (right b) a ⁆)
       → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym (e ∙ singl≡pair (left b)))
      (pairIn (left b) (left b) l∈ l∈)
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (pairPrIn (left b) (right b) a l∈ r∈ (sub a a∈))
  valueMem op13 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (left b) (pr (right b) a) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f13 a b) h))
    where
    go : (v ≡ left b) ⊎ (v ≡ pr (right b) a) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (up (left b) (inP (left b) (left-read b b∈)))
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn (right b) a (inP (right b) (right-read b b∈)) (sub a a∈))
  valueMem op14 a b a∈ b∈ v h = PT.rec (snd (v ∈ˢ T)) go
    (F0-spec (left b) (pr a (right b)) v .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f14 a b) h))
    where
    go : (v ≡ left b) ⊎ (v ≡ pr a (right b)) → ⟨ v ∈ˢ T ⟩
    go (inl e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (up (left b) (inP (left b) (left-read b b∈)))
    go (inr e) = subst (λ w → ⟨ w ∈ˢ T ⟩) (sym e)
      (prIn a (right b) (sub a a∈) (inP (right b) (right-read b b∈)))
  valueMem op15 a b a∈ b∈ v h = up v (sub v (mem a v
    (subst ⟨_⟩ (F15C.F15-spec a v)
      (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f15 a b) h) .fst) a∈))
```

<!--en-->
## The offsets at the tower

Four stages above the stage that holds the argument, and no more. The count is
forced by the nested pair of the two tuple operations: a Kuratowski pair of
two members of a stage costs two stages, and the middle insertion pairs twice.
The closure facts are discharged here by pairing alone, plus one image slice,
which is a definable subset of the stage its two arguments live in, and the
empty set, which is the definable subset carved by the false formula.
<!--zh-->
## 塔处的偏移

在收下实参的阶段之上四个阶段，不多不少。这个计数由两个三元组运算的嵌套对逼出：一个阶段的两个成员之 Kuratowski 对花费两个阶段，而中间插入配对两次。诸闭包事实在此仅由配对兑现，外加一个切片 (它是其两个实参所在阶段的一个可定义子集) 与空集 (它是假公式刻出的可定义子集)。
<!--ja-->
## 塔におけるオフセット

実引数を受け取る段階の四つ上、それ以上でもそれ以下でもない。この数は、二つの三つ組演算の入れ子になった対によって強制される。ある段階の二つのメンバーのクーラトフスキー対は二つの段階を要し、中央の挿入は二度対にする。閉包事実はここでは対にするだけで解消され、それに一つの像スライスが加わる。像スライスは、その二つの実引数の住む段階の可定義部分集合であり、空集合は、偽の式が刻む可定義部分集合である。
<!--/-->

```agda
defSet⊥≡∅ : (D : S) → DefOf.defSet D ⊥̇ ≡ ∅
defSet⊥≡∅ D = empty-⊆ (DefOf.defSet D ⊥̇) no
  where
  no : (x : S) → ⟨ x ∈ˢ DefOf.defSet D ⊥̇ ⟩ → Empty.⊥
  no x h = Empty.rec* (subst ⟨_⟩ (DefOf.defSet-mem D ⊥̇ (fib .fst))
    (subst (λ w → ⟨ w ∈ˢ DefOf.defSet D ⊥̇ ⟩) (sym (fib .snd)) h))
    where
    fib : Σ[ m ∈ ⟪ D ⟫ ] (⟪ D ⟫↪ m ≡ x)
    fib = ∈-asFiber {a = x} {b = D} (DefOf.defSet⊆A D ⊥̇ x h)

∅∈Lsuc : (ξ : S) → ⟨ ∅ ∈ˢ Lset (sucV ξ) ⟩
∅∈Lsuc ξ = subst (λ w → ⟨ w ∈ˢ Lset (sucV ξ) ⟩) (defSet⊥≡∅ (Lset ξ))
  (𝒟ₒ⊆Lsuc ξ (DefOf.defSet (Lset ξ) ⊥̇)
    (𝒟ₒ-intro (Lset ξ) (DefOf.defSet (Lset ξ) ⊥̇) ∣ ⊥̇ , refl ∣₁))

sliceInLsuc : (ξ x y : S) → ⟨ x ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset ξ ⟩
            → ⟨ F10 x y ∈ˢ Lset (sucV ξ) ⟩
sliceInLsuc ξ x y x∈ y∈ = 𝒟ₒ⊆Lsuc ξ (F10 x y)
  (𝒟ₒ-intro (Lset ξ) (F10 x y) ∣ D.Φ₁₀ , D.F10-defSet≡ ∣₁)
  where
  module D = F10Desc (Lset ξ) x y x∈ y∈ (Ltr ξ)

opaque
  unfolding suc⁴
  -- perf: P-i layer cap; the four exposed successor layers stay in this block
  values∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ValuesInU u (suc⁴ ζ)
  values∈L u ζ u∈ i a b sa sb v h =
    Val.valueMem i a b (split a sa) (split b sb) v h
    where
    ζ₁ ζ₂ ζ₃ ζ₄ : S
    ζ₁ = sucV ζ
    ζ₂ = sucV ζ₁
    ζ₃ = sucV ζ₂
    ζ₄ = sucV ζ₃
    up₁ : (ξ y : S) → ⟨ y ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset (sucV ξ) ⟩
    up₁ ξ y k = Lset-mono {α = sucV ξ} {β = ξ} (self∈sucV ξ) k
    subFn : (x : S) → ⟨ x ∈ˢ Lset ζ ⟩ → ⟨ x ∈ˢ Lset ζ₁ ⟩
    subFn = up₁ ζ
    upFn : (x : S) → ⟨ x ∈ˢ Lset ζ₁ ⟩ → ⟨ x ∈ˢ Lset ζ₄ ⟩
    upFn x k = up₁ ζ₃ x (up₁ ζ₂ x (up₁ ζ₁ x k))
    pairFn : (p q : S) → ⟨ p ∈ˢ Lset ζ₁ ⟩ → ⟨ q ∈ˢ Lset ζ₁ ⟩
           → ⟨ F0 p q ∈ˢ Lset ζ₄ ⟩
    pairFn p q p∈ q∈ = up₁ ζ₃ (F0 p q) (up₁ ζ₂ (F0 p q) (Lpair ζ₁ p q p∈ q∈))
    prFn : (p q : S) → ⟨ p ∈ˢ Lset ζ₁ ⟩ → ⟨ q ∈ˢ Lset ζ₁ ⟩
         → ⟨ pr p q ∈ˢ Lset ζ₄ ⟩
    prFn p q p∈ q∈ = up₁ ζ₃ (pr p q)
      (Lpair ζ₂ (⁅ p ⁆s) (⁅ p , q ⁆) sgl∈ pair∈)
      where
      sgl∈ : ⟨ ⁅ p ⁆s ∈ˢ Lset ζ₂ ⟩
      sgl∈ = subst (λ w → ⟨ w ∈ˢ Lset ζ₂ ⟩) (sym (singl≡pair p))
        (Lpair ζ₁ p p p∈ p∈)
      pair∈ : ⟨ ⁅ p , q ⁆ ∈ˢ Lset ζ₂ ⟩
      pair∈ = Lpair ζ₁ p q p∈ q∈
    prFn₂ : (p q r : S) → ⟨ p ∈ˢ Lset ζ ⟩ → ⟨ q ∈ˢ Lset ζ ⟩ → ⟨ r ∈ˢ Lset ζ ⟩
          → ⟨ pr p (pr q r) ∈ˢ Lset ζ₄ ⟩
    prFn₂ p q r p∈ q∈ r∈ = Lpair ζ₃ (⁅ p ⁆s) (⁅ p , pr q r ⁆) sgl∈ pair∈
      where
      inner : ⟨ pr q r ∈ˢ Lset ζ₂ ⟩
      inner = Lpair ζ₁ (⁅ q ⁆s) (⁅ q , r ⁆)
        (subst (λ w → ⟨ w ∈ˢ Lset ζ₁ ⟩) (sym (singl≡pair q))
          (Lpair ζ q q q∈ q∈))
        (Lpair ζ q r q∈ r∈)
      p∈₂ : ⟨ p ∈ˢ Lset ζ₂ ⟩
      p∈₂ = up₁ ζ₁ p (up₁ ζ p p∈)
      sgl∈ : ⟨ ⁅ p ⁆s ∈ˢ Lset ζ₃ ⟩
      sgl∈ = subst (λ w → ⟨ w ∈ˢ Lset ζ₃ ⟩) (sym (singl≡pair p))
        (Lpair ζ₂ p p p∈₂ p∈₂)
      pair∈ : ⟨ ⁅ p , pr q r ⁆ ∈ˢ Lset ζ₃ ⟩
      pair∈ = Lpair ζ₂ p (pr q r) p∈₂ inner
    pairPrFn : (l p q : S) → ⟨ l ∈ˢ Lset ζ₁ ⟩ → ⟨ p ∈ˢ Lset ζ₁ ⟩
             → ⟨ q ∈ˢ Lset ζ₁ ⟩ → ⟨ F0 l (pr p q) ∈ˢ Lset ζ₄ ⟩
    pairPrFn l p q l∈ p∈ q∈ =
      Lpair ζ₃ l (pr p q) (up₁ ζ₂ l (up₁ ζ₁ l l∈)) inner
      where
      inner : ⟨ pr p q ∈ˢ Lset ζ₃ ⟩
      inner = Lpair ζ₂ (⁅ p ⁆s) (⁅ p , q ⁆)
        (subst (λ w → ⟨ w ∈ˢ Lset ζ₂ ⟩) (sym (singl≡pair p))
          (Lpair ζ₁ p p p∈ p∈))
        (Lpair ζ₁ p q p∈ q∈)
    sliceFn : (x y : S) → ⟨ x ∈ˢ Lset ζ ⟩ → ⟨ y ∈ˢ Lset ζ ⟩
            → ⟨ F10 x y ∈ˢ Lset ζ₄ ⟩
    sliceFn x y x∈ y∈ = upFn (F10 x y) (sliceInLsuc ζ x y x∈ y∈)
    module Val = Values (Lset ζ) (Lset ζ₁) (Lset ζ₄) (Ltr ζ) subFn upFn
                 pairFn prFn prFn₂ pairPrFn sliceFn (∅∈Lsuc ζ)
    split : (c : S) → (⟨ c ∈ˢ u ⟩ ⊎ (c ≡ u)) → ⟨ c ∈ˢ Lset ζ ⟩
    split c (inl c∈u) = Ltr ζ {x = u} {y = c} c∈u u∈
    split c (inr c≡u) = subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym c≡u) u∈
```

<!--en-->
## The empty set, and the theorem

The empty set is a definable subset of every stage below a stage that already
holds something, which is what places the relativization slot of the plain
trunk and, with it, the last hypothesis the description needs. The theorem
then places the step in the next stage: once the step's formula describes the
step exactly, the definable-subset principle hands the step to the stage
above.
<!--zh-->
## 空集，与定理

空集是任何阶段的可定义子集，只要该阶段之下已有一个阶段收下了什么，这既安放了非相对化主干的相对化槽，也随之安放了描述所需的最后一条假设。定理随之把该步安放进下一阶段：一旦 step 的公式恰好描述出该步，可定义子集原则就把该步交给上一阶段。
<!--ja-->
## 空集合、そして定理

空集合は、その段階の下に何かを受け入れた段階が既にある限り、どの段階の可定義部分集合でもある。これが非相対化の幹の相対化スロットを置き、それとともに記述が必要とする最後の仮説を置く。定理はその step を次の段階に置く。step の式が step をちょうど記述しさえすれば、可定義部分集合の原理が step を上の段階へ渡すからである。
<!--/-->

```agda
∅∈Lset : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ⟨ ∅ ∈ˢ Lset ζ ⟩
∅∈Lset u ζ u∈ = PT.rec (snd (∅ ∈ˢ Lset ζ)) go (Lset-out ζ u u∈)
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ζ ⟩ × ⟨ u ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ ∅ ∈ˢ Lset ζ ⟩
  go (δ , δ∈ζ , _) = Lset-in ζ δ ∅ δ∈ζ
    (subst (λ w → ⟨ w ∈ˢ 𝒟ₒ (Lset δ) ⟩) (defSet⊥≡∅ (Lset δ))
      (𝒟ₒ-intro (Lset δ) (DefOf.defSet (Lset δ) ⊥̇) ∣ ⊥̇ , refl ∣₁))

stepSet∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ⟨ A ∈ˢ Lset ζ ⟩
          → ((v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
          → ⟨ step u ∈ˢ Lset (sucV ζ) ⟩
stepSet∈L u ζ u∈ A∈ sub = 𝒟ₒ⊆Lsuc ζ (step u)
  (𝒟ₒ-intro (Lset ζ) (step u) ∣ St.stepForm , St.stepSet-desc ∣₁)
  where
  fibA : Σ[ m ∈ ⟪ Lset ζ ⟫ ] (⟪ Lset ζ ⟫↪ m ≡ A)
  fibA = ∈-asFiber {a = A} {b = Lset ζ} A∈
  fibu : Σ[ m ∈ ⟪ Lset ζ ⟫ ] (⟪ Lset ζ ⟫↪ m ≡ u)
  fibu = ∈-asFiber {a = u} {b = Lset ζ} u∈
  module Sl = Layer (Lset ζ) (Ltr ζ) (fibA .fst) (fibA .snd)
    (∅∈Lset u ζ u∈)
  module St = Sl.AtStep u (fibu .fst) (fibu .snd) sub
```
