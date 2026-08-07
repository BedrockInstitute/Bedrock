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
これは、rud step の消費者が読むグラフ層の新しい生存ホームである。すなわち、等号フレーム、射影フレームとスライスフレーム、束縛された引数変数における十六個の所属式、そして双方向復号を備えた十六路の論理和である。このブロックは土台のみを届ける。所属式の復号、ディスパッチャ、そしてグラフは後のブロックで到着し、本章はそれらの着地点を自然なまま残す。消費者が結線する名前 (`eqFrame`、`leftMem`、`sliceMem`、`bigOr`、`mem0` から `mem15`) は、すべてここで最終形のまま届けられる。ここではアーカイブ済みの `StepInL` を何もインポートしない。供給者はすべて生存モジュールである
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
open import L.Constructible {ℓ} using ( isTransV )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Rud.Images {ℓ} using
  ( left; left-compute; right; ⋂; ⋂-member-in-all; right-nonpair )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11; op12
  ; op13; op14; op15; isPair; right-at-pair )
open import L.Rud.Bridge {ℓ} lem A using ( ext-⊆; empty-⊆ )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import Cubical.Data.FinData.Base using ( Fin )
open import Cubical.Data.Sum using ( _⊎_; inl; inr; rec )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _≡ₕ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
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
## グラフ層、推移的な台において

グラフ層は汎用の推移的な台 `C` で組み立てられる。そのテレスコープは、プローブとアーカイブ済みの `Slot` が使うものと分毫も違わない。スロット `A`は証明書 `qA` を通してのみ入る。空集合の所属 `∅∈C` は後続のブロックに備え、テレスコープが二度と変わらないようにここに置かれる。台における内部世界はレベルキットのもの (`SM` と `⊨ᵐ`) であり、ペアキットが点と入口証明書を供給する。

等号フレームは、グラフ層が外延性を論じる唯一の場所である。`eqFrame k M` は、スロット `k` の集合が式 `M` の記述するメンバーからなる集合とちょうど一致することを言い、その復号の二つの方向は二つの包含である。後のフレームとグラフはすべて、このフレームを一度適用したものである。
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

各フレームの復号は、等号フレームの外延性の議論と同形であり、それをフレーム自身の本体で走らせる。射影値の所属は内部世界に読み込まれ、内部の読みは推移性証明書を通して台へ持ち上げられる。右射影は対の外では空集合であり、演算層がそれを別の読み補題で読む。したがって、その記述は一度の場合分けを保つ。その場合分けは忠実である。台の中の対は、その二つの成分も台の中にあるから、どこでの分解もここでの分解になる。
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
## 十六個の所属式、束縛された引数において

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
