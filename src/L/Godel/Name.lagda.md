# Names, as terms

<!--en-->
The step of the choice construction consumes names: for each stage, a type that
denotes the members of the next stage, carries a strict well-order, and yields
a least name for every denoted member. The route through internalized
satisfaction built that type from formulas, and the building was the bulk of
two chapters: parameters had to leave the syntax, and the order had to open a
limit construction every time two codes were compared.

This chapter delivers the same interface from the terms. A name is an arity-one
term over the members of the stage, exactly what the tower already quantifies;
it denotes the set of values of its evaluation, and completeness is the banked
equivalence of the terms chapter, spent as one transport. The order is bought
generically: a term is pictured as a finite labelled tree, and the picture
separates the name's parameter-free **skeleton** from its **parameter list**.
The skeleton is coded as a hereditarily finite set and ordered by the finite
chapter's generic earliest-disagreement order on the limit stage; the
parameter list is ordered length-gated pointwise by the stage order; and the
name order is the product of the two pulled back along the joint picture. The
only fact the pull-back demands is that the joint picture is injective, and
that is not a case matrix: the picture has a left inverse (strip, then graft
the parameters back), and a map with a left inverse is injective for free.
<!--zh-->
选择构造的步进消费名字：对每个阶段，要有一个类型，指称下一个阶段的成员，携带一个严格良序，并为每个被指称的成员交出一个最小的名字。经由内化满足的路线用公式造出了那个类型，而造它是两章的主体：参数必须离开语法，而序在每次比较两个码时都要撬开一个极限构造。

本章从诸项交付同一接口。名字就是阶段成员上的元数一的项，恰是塔已经在量化的那种东西；它指称其求值的取值之集，而完备性是项那一章已入账的等价，一次搬运即花掉。序则是泛型地买来的：把项画成一棵有穷带标签树，这幅画把名字的无参**骨架**与**参数表**分开。骨架编码为遗传有穷集，按有穷那一章的极限阶段上的泛型最先分歧序排序；参数表按给定阶段序作以长度为门的逐点比较；名字的序就是两把键序的积，沿联合的画拉回。拉回唯一索要的事实是联合的画单射，而那不是一张情形矩阵：这幅画有左逆 (剥下，再把参数回植回去)，而有左逆的映射免费单射。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Godel.Name {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒟ₒ; 𝒟ₒ-inv; Lset; Lset-mono )
open import L.Godel.Operations {ℓ} using ( values )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK
        ; shiftK; ⟦_⟧ᴷ; module WithLEM )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; prodSWO; listSWO; pullSWO )
open import L.WellOrder.Tree {ℓ} using ( Tree; node )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Choice.Finite {ℓ} lem using ( Limit; inSome; limitOrder )
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( pr∈Lset-suc )

open import Cubical.Data.FinData using ( toℕ; ¬Fin0 )
open import Cubical.Data.List using ( List; []; _∷_; _++_ )
open import Cubical.Data.List.Properties using ( ++-assoc; ++-unit-r )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Data.Nat using ( _+_; +-comm; znots; snotz )
open import Cubical.Relation.Nullary using ( ¬_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; _∈ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet using ( #_; ω )
import Cubical.Functions.Logic as L
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ
```

<!--en-->
## The names, and completeness

The interface takes membership of the definable powerset as the completeness
hypothesis, and the terms chapter has already identified the definable powerset
with the values of the arity-one terms. So a name is such a term, denotation is
evaluation followed by `values`{.Agda}, and completeness is the identification
transported backwards: membership on either side is definitionally the
truncated fiber the statement asks for, so nothing remains to prove. The one
seal on the way is that the tower keeps `𝒟ₒ`{.Agda} opaque, and
`𝒟ₒ-inv`{.Agda} is its sanctioned opening.
<!--zh-->
## 诸名字，与完备性

接口以可定义幂集的成员性为完备性的前提，而项那一章已把可定义幂集与元数一诸项的取值等同。于是名字就是这样一个项，指称就是求值后接 `values`{.Agda}，完备性就是那次等同向后搬运：两侧的成员性按定义都是陈述所要的截断纤维，无事可证。路上唯一的封印是塔把 `𝒟ₒ`{.Agda} 保持 opaque，而 `𝒟ₒ-inv`{.Agda} 是它获准的开封。
<!--/-->

```agda
module Naming (A : S) (w : SWO ⟪ A ⟫) where
  Name : Type ℓ
  Name = KT ⟪ A ⟫ 1

  denote : Name → S
  denote t = values (⟦_⟧ᴷ A t)

  private
    module TW = WithLEM A lem

  names-complete : (x : S) → ⟨ x ∈ˢ 𝒟ₒ A ⟩
                 → ∥ Σ[ a ∈ Name ] (denote a ≡ x) ∥₁
  names-complete x h =
    subst (λ z → ⟨ x ∈ˢ z ⟩) (sym TW.termDef≡Def) (𝒟ₒ-inv A x h)
```

<!--en-->
## The picture

Each constructor contributes one node. The label carries the constructor's tag,
the selector indices when there are any, read off as numbers, and the parameter
when there is one; the children are the pictures of the subterms. The labels
carry no arities: the comparison only ever holds two terms of the same arity
side by side, and the subterm arities then agree position by position.
<!--zh-->
## 那幅画

每个构造子贡献一个节点。标签携带构造子的标记、有选择子指标时读成数字的指标、有参数时的那个参数；孩子是子项的画。标签不携带元数：比较从来只把两个同元数的项并排，而此时子项的元数逐位置一致。
<!--/-->

```agda
  private
    Lab : Type ℓ
    Lab = (ℕ × ℕ × ℕ) × (Unit* {ℓ} ⊎ ⟪ A ⟫)

    toTree : {n : ℕ} → KT ⟪ A ⟫ n → Tree Lab
    toTree allK            = node ((0 , 0 , 0) , inl tt*) []
    toTree (selMemK i j)   = node ((1 , toℕ i , toℕ j) , inl tt*) []
    toTree (selEqK i j)    = node ((2 , toℕ i , toℕ j) , inl tt*) []
    toTree (selEqConK i a) = node ((3 , toℕ i , 0) , inr a) []
    toTree (interK s t)    = node ((4 , 0 , 0) , inl tt*) (toTree s ∷ toTree t ∷ [])
    toTree (unionK s t)    = node ((5 , 0 , 0) , inl tt*) (toTree s ∷ toTree t ∷ [])
    toTree (complK t)      = node ((6 , 0 , 0) , inl tt*) (toTree t ∷ [])
    toTree (shiftK t)      = node ((7 , 0 , 0) , inl tt*) (toTree t ∷ [])
```

<!--en-->
## The left inverse

Injectivity is proved by exhibiting a left inverse, term by term. Reading a
label's numbers back as selector indices needs a conversion from numbers to
`Fin`{.Agda} that never fails, so the conversion clamps: on the image of
`toℕ`{.Agda} it is exact, and that is the only place the left inverse is
evaluated. Off the image the reading returns a harmless default, and coverage
is bought by one catch-all clause. The clauses that do inspect the arity are
quarantined in their own helpers, so that the reading itself never splits on
it: a round trip at a neutral arity then still computes, constructor by
constructor.
<!--zh-->
## 左逆

单射性靠逐项给出左逆来证。把标签上的数字读回选择子指标，需要一个从数字到 `Fin`{.Agda} 的永不失败的转换，于是转换取钳制：在 `toℕ`{.Agda} 的像上它精确，而左逆只在那里被求值。像之外，读取返回无害的缺省值，覆盖由一条兜底从句买单。确需检视元数的从句被隔离进各自的辅助函数，使读取本身从不按元数分裂：中立元数下的一次往返仍逐构造子计算。
<!--/-->

```agda
    mkFin : {n : ℕ} → ℕ → Fin (suc n)
    mkFin zero            = zero
    mkFin {zero}  (suc k) = zero
    mkFin {suc n} (suc k) = suc (mkFin k)

    mkFin-toℕ : {n : ℕ} (i : Fin (suc n)) → mkFin (toℕ i) ≡ i
    mkFin-toℕ zero            = refl
    mkFin-toℕ {zero}  (suc i) = Empty.rec (¬Fin0 i)
    mkFin-toℕ {suc n} (suc i) = cong suc (mkFin-toℕ i)

    selM : (n : ℕ) → ℕ → ℕ → KT ⟪ A ⟫ n
    selM zero    i j = allK
    selM (suc m) i j = selMemK (mkFin i) (mkFin j)

    selE : (n : ℕ) → ℕ → ℕ → KT ⟪ A ⟫ n
    selE zero    i j = allK
    selE (suc m) i j = selEqK (mkFin i) (mkFin j)

    selC : (n : ℕ) → ℕ → Unit* {ℓ} ⊎ ⟪ A ⟫ → KT ⟪ A ⟫ n
    selC zero    i p       = allK
    selC (suc m) i (inl u) = allK
    selC (suc m) i (inr a) = selEqConK (mkFin i) a

    fromTree : (n : ℕ) → Tree Lab → KT ⟪ A ⟫ n
    fromTree n (node ((0 , _ , _) , _) _) = allK
    fromTree n (node ((1 , i , j) , _) _) = selM n i j
    fromTree n (node ((2 , i , j) , _) _) = selE n i j
    fromTree n (node ((3 , i , _) , p) _) = selC n i p
    fromTree n (node ((4 , _ , _) , _) (c₁ ∷ c₂ ∷ [])) =
      interK (fromTree n c₁) (fromTree n c₂)
    fromTree n (node ((5 , _ , _) , _) (c₁ ∷ c₂ ∷ [])) =
      unionK (fromTree n c₁) (fromTree n c₂)
    fromTree n (node ((6 , _ , _) , _) (c ∷ [])) = complK (fromTree n c)
    fromTree n (node ((7 , _ , _) , _) (c ∷ [])) = shiftK (fromTree (suc n) c)
    fromTree n t = allK

    retractK : {n : ℕ} (t : KT ⟪ A ⟫ n) → fromTree n (toTree t) ≡ t
    retractK allK = refl
    retractK {zero}  (selMemK i j)   = Empty.rec (¬Fin0 i)
    retractK {suc m} (selMemK i j)   = cong₂ selMemK (mkFin-toℕ i) (mkFin-toℕ j)
    retractK {zero}  (selEqK i j)    = Empty.rec (¬Fin0 i)
    retractK {suc m} (selEqK i j)    = cong₂ selEqK (mkFin-toℕ i) (mkFin-toℕ j)
    retractK {zero}  (selEqConK i a) = Empty.rec (¬Fin0 i)
    retractK {suc m} (selEqConK i a) = cong (λ z → selEqConK z a) (mkFin-toℕ i)
    retractK (interK s t) = cong₂ interK (retractK s) (retractK t)
    retractK (unionK s t) = cong₂ unionK (retractK s) (retractK t)
    retractK (complK t)   = cong complK (retractK t)
    retractK (shiftK t)   = cong shiftK (retractK t)

    toTree-inj : (s t : KT ⟪ A ⟫ 1) → toTree s ≡ toTree t → s ≡ t
    toTree-inj s t q = sym (retractK s) ∙ cong (fromTree 1) q ∙ retractK t
```

<!--en-->
## The order

The order now compares a name by two keys. The first key is the name's
parameter-free **skeleton**: the picture with every parameter slot left as an
unfilled marker, coded as a hereditarily finite set and ordered by the finite
chapter's generic earliest-disagreement order on the limit stage. The second
key is the **parameter list**, read off the picture in preorder, ordered
length-gated pointwise by the given stage order. The name order is the product
of the two key orders pulled back along the joint map, and the pull-back's
injectivity is the left-inverse discipline of the picture, one level up: strip
and collect, then graft the parameters back, and the round trip is the
identity. The internal side ahead describes exactly these two keys, which is
the point of the re-cut: the tree order steps aside, and the trees keep only
their role as the injectivity picture.
<!--zh-->
## 序

序现在用两个键比较一个名字。第一个键是名字的无参**骨架**：把画里每个参数槽都留成未填的标记，编码为遗传有穷集，并按有穷那一章的极限阶段上的泛型最先分歧序来排序。第二个键是**参数表**：按先序遍历从画中读出，按给定阶段序作以长度为门的逐点比较。名字的序是两把键序的积，沿联合映射拉回；拉回的单射性就是那幅画的左逆纪律上移一层：剥下并收集，再把参数回植回去，往返是恒等。前方的内部侧恰恰要描述这两个键，这正是这次重切的意义：树的序让位，树只保留其作为单射性图画的作用。
<!--/-->

<!--en-->
Two readings of the same picture give the two keys. The skeleton drops the
parameters and keeps the slot discipline: every parameter slot is left as an
unfilled marker, and the shape survives. The parameter list walks the picture
in preorder and collects the parameters in order. Together the readings
determine the tree: the graft reads a skeleton and consumes the parameter
list, one parameter at each marker slot, with the leftovers threaded through
the children; the round trip is the identity, the same left-inverse discipline
as the picture's, one level up.
<!--zh-->
同一幅画的两种读法给出两把键。骨架把参数丢掉、留下槽位纪律：每个参数槽都留作未填的标记，形状幸存。参数表按先序遍历这幅画，依序收集参数。两种读法合起来决定这棵树：回植读一棵骨架并消费参数表，在每个标记槽处消耗一个参数，余量穿给孩子；往返是恒等，与那幅画的左逆纪律同出一辙，只是上移一层。
<!--/-->

```agda
  private
    Lab₀ : Type ℓ
    Lab₀ = (ℕ × ℕ × ℕ) × (Unit* {ℓ} ⊎ Unit* {ℓ})

    stripT : Tree Lab → Tree Lab₀
    stripL : List (Tree Lab) → List (Tree Lab₀)
    stripT (node ((i , j , k) , inl u) cs) =
      node ((i , j , k) , inl tt*) (stripL cs)
    stripT (node ((i , j , k) , inr a) cs) =
      node ((i , j , k) , inr tt*) (stripL cs)
    stripL [] = []
    stripL (t ∷ ts) = stripT t ∷ stripL ts

    parT : Tree Lab → List ⟪ A ⟫
    parL : List (Tree Lab) → List ⟪ A ⟫
    parT (node ((i , j , k) , inl u) cs) = parL cs
    parT (node ((i , j , k) , inr a) cs) = a ∷ parL cs
    parL [] = []
    parL (t ∷ ts) = parT t ++ parL ts

    junk : Tree Lab
    junk = node ((0 , 0 , 0) , inl tt*) []

    graftT : Tree Lab₀ → List ⟪ A ⟫ → Tree Lab × List ⟪ A ⟫
    graftL : List (Tree Lab₀) → List ⟪ A ⟫ → List (Tree Lab) × List ⟪ A ⟫
    graftT (node ((i , j , k) , inl _) cs) ps =
      (node ((i , j , k) , inl tt*) (fst (graftL cs ps))) , snd (graftL cs ps)
    graftT (node ((i , j , k) , inr _) cs) [] = (junk , [])
    graftT (node ((i , j , k) , inr _) cs) (a ∷ ps) =
      (node ((i , j , k) , inr a) (fst (graftL cs ps))) , snd (graftL cs ps)
    graftL [] ps = ([] , ps)
    graftL (t ∷ ts) ps =
      (fst (graftT t ps) ∷ fst (graftL ts (snd (graftT t ps))))
      , snd (graftL ts (snd (graftT t ps)))

    graftT-strip : (u : Tree Lab) (rest : List ⟪ A ⟫)
                 → graftT (stripT u) (parT u ++ rest) ≡ (u , rest)
    graftL-strip : (us : List (Tree Lab)) (rest : List ⟪ A ⟫)
                 → graftL (stripL us) (parL us ++ rest) ≡ (us , rest)
    graftT-strip (node ((i , j , k) , inl tt*) cs) rest =
      λ ι → let p = graftL-strip cs rest ι
            in (node ((i , j , k) , inl tt*) (fst p)) , snd p
    graftT-strip (node ((i , j , k) , inr a) cs) rest =
      λ ι → let p = graftL-strip cs rest ι
            in (node ((i , j , k) , inr a) (fst p)) , snd p
    graftL-strip [] rest = refl
    graftL-strip (u ∷ us) rest = step₁ ∙ step₂
      where
      step₁ : graftL (stripT u ∷ stripL us) ((parT u ++ parL us) ++ rest)
            ≡ graftL (stripT u ∷ stripL us) (parT u ++ (parL us ++ rest))
      step₁ = λ ι → graftL (stripT u ∷ stripL us) (++-assoc (parT u) (parL us) rest ι)

      step₂ : graftL (stripT u ∷ stripL us) (parT u ++ (parL us ++ rest))
            ≡ (u ∷ us , rest)
      step₂ =
        (λ ι → let p = graftT-strip u (parL us ++ rest) ι
               in (fst p ∷ fst (graftL (stripL us) (snd p)))
                , snd (graftL (stripL us) (snd p)))
        ∙ (λ ι → let q = graftL-strip us rest ι
                 in (u ∷ fst q) , snd q)

    strip-par-inj : (u v : Tree Lab)
                  → stripT u ≡ stripT v → parT u ≡ parT v → u ≡ v
    strip-par-inj u v su sv = λ ι → fst (chain ι)
      where
      chain : (u , []) ≡ (v , [])
      chain = sym (graftT-strip u [])
            ∙ (λ ι → graftT (stripT u) (++-unit-r (parT u) ι))
            ∙ (λ ι → graftT (su ι) (sv ι))
            ∙ (λ ι → graftT (stripT v) (sym (++-unit-r (parT v)) ι))
            ∙ graftT-strip v []
```

<!--en-->
The skeleton codes into the hierarchy as a hereditarily finite set. A marker
with its three numerals codes as a nested pair, the two markers distinguished
by the innermost code, the numerals zero and one; a node codes as a pair of
its label's code and its children's code; and the empty child list codes as
the numeral zero. Codes are injective: pairs and numerals both are, and a node
never equals the empty code because a pair has a member. Membership in the
limit stage is then a closure induction: numerals are in the limit, pairs of
members of the limit are in the limit, and the tree and list codes close under
these two.
<!--zh-->
骨架编码进层级，成为遗传有穷集。一个标记连同它的三个数字编码成嵌套对，两个标记靠最内层的码 (数码零与一) 区分；节点编码为「标签之码与孩子表之码」的对；空孩子表编码为数码零。码是单射的：对与数码都单射，而节点永不等于空码，因为对总有一个成员。极限阶段的成员资格随后是一场封闭性归纳：数码在极限中，极限成员的对仍在极限中，树码与表码在这两个形成子下封闭。
<!--/-->

```agda
  private
    slot-code : Bool → S
    slot-code false = # 0
    slot-code true  = # 1

    labCode : Lab₀ → S
    labCode ((i , j , k) , inl tt*) =
      pr (# i) (pr (# j) (pr (# k) (# 0)))
    labCode ((i , j , k) , inr tt*) =
      pr (# i) (pr (# j) (pr (# k) (# 1)))

    codeT : Tree Lab₀ → S
    codeL : List (Tree Lab₀) → S
    codeT (node l cs) = pr (labCode l) (codeL cs)
    codeL [] = # 0
    codeL (c ∷ cs) = pr (codeT c) (codeL cs)

    pr≢∅ : {x y : S} → ¬ (pr x y ≡ ∅)
    pr≢∅ {x} {y} q =
      ∅-empty (⁅ x ⁆s)
        (subst (λ z → ⟨ ⁅ x ⁆s ∈ₛ z ⟩) q
          (pairing-ax (⁅ x ⁆s) (⁅ x , y ⁆) (⁅ x ⁆s) .snd
            (L.inl refl)))

    -- perf: law P-a, explicit pr-inj and #-inj′ implicits at concrete numerals
    nums-inj : (b : Bool) (i j k i' j' k' : ℕ)
             → pr (# i) (pr (# j) (pr (# k) (slot-code b)))
               ≡ pr (# i') (pr (# j') (pr (# k') (slot-code b)))
             → (i , j , k) ≡ (i' , j' , k')
    nums-inj b i j k i' j' k' q =
      cong₂ _,_ i≡ (cong₂ _,_ j≡ k≡)
      where
      q₁ = pr-inj {a = # i} {b = pr (# j) (pr (# k) (slot-code b))}
                  {c = # i'} {d = pr (# j') (pr (# k') (slot-code b))} q
      q₂ = pr-inj {a = # j} {b = pr (# k) (slot-code b)}
                  {c = # j'} {d = pr (# k') (slot-code b)} (q₁ .snd)
      q₃ = pr-inj {a = # k} {b = slot-code b}
                  {c = # k'} {d = slot-code b} (q₂ .snd)
      i≡ : i ≡ i'
      i≡ = #-inj′ (q₁ .fst)
      j≡ : j ≡ j'
      j≡ = #-inj′ (q₂ .fst)
      k≡ : k ≡ k'
      k≡ = #-inj′ (q₃ .fst)

    strip-pr-1 : {s s' : S} {i j k i' j' k' : ℕ}
               → pr (# i) (pr (# j) (pr (# k) s))
                 ≡ pr (# i') (pr (# j') (pr (# k') s'))
               → pr (# j) (pr (# k) s) ≡ pr (# j') (pr (# k') s')
    strip-pr-1 {s} {s'} {i} {j} {k} {i'} {j'} {k'} q =
      pr-inj {a = # i} {b = pr (# j) (pr (# k) s)}
             {c = # i'} {d = pr (# j') (pr (# k') s')} q .snd

    strip-pr-2 : {s s' : S} {j k j' k' : ℕ}
               → pr (# j) (pr (# k) s) ≡ pr (# j') (pr (# k') s')
               → pr (# k) s ≡ pr (# k') s'
    strip-pr-2 {s} {s'} {j} {k} {j'} {k'} q =
      pr-inj {a = # j} {b = pr (# k) s}
             {c = # j'} {d = pr (# k') s'} q .snd

    slot-codes : {i j k i' j' k' : ℕ}
              → pr (# i) (pr (# j) (pr (# k) (# 0)))
                ≡ pr (# i') (pr (# j') (pr (# k') (# 1)))
              → 0 ≡ 1
    slot-codes {i} {j} {k} {i'} {j'} {k'} q' =
      #-inj′ (pr-inj {a = # k} {b = # 0} {c = # k'} {d = # 1}
        (strip-pr-2 (strip-pr-1 q')) .snd)

    labCode-inj : (l l' : Lab₀) → labCode l ≡ labCode l' → l ≡ l'
    labCode-inj ((i , j , k) , inl tt*) ((i' , j' , k') , inl tt*) q =
      cong (λ t → (fst t , fst (snd t) , snd (snd t)) , inl tt*)
           (nums-inj false i j k i' j' k' q)
    labCode-inj ((i , j , k) , inl tt*) ((i' , j' , k') , inr tt*) q =
      Empty.rec (znots (slot-codes q))
    labCode-inj ((i , j , k) , inr tt*) ((i' , j' , k') , inl tt*) q =
      Empty.rec (snotz (slot-codes-r q))
      where
      slot-codes-r : pr (# i) (pr (# j) (pr (# k) (# 1)))
                   ≡ pr (# i') (pr (# j') (pr (# k') (# 0)))
                   → 1 ≡ 0
      slot-codes-r q' = #-inj′ (pr-inj {a = # k} {b = # 1} {c = # k'} {d = # 0}
        (strip-pr-2 (strip-pr-1 q')) .snd)
    labCode-inj ((i , j , k) , inr tt*) ((i' , j' , k') , inr tt*) q =
      cong (λ t → (fst t , fst (snd t) , snd (snd t)) , inr tt*)
           (nums-inj true i j k i' j' k' q)

    codeT-inj : (t u : Tree Lab₀) → codeT t ≡ codeT u → t ≡ u
    codeL-inj : (ts us : List (Tree Lab₀)) → codeL ts ≡ codeL us → ts ≡ us
    codeT-inj (node l cs) (node l' cs') q =
      cong₂ node (labCode-inj l l' (pr-inj q .fst)) (codeL-inj cs cs' (pr-inj q .snd))
    codeL-inj [] [] q = refl
    codeL-inj [] (c ∷ cs) q = Empty.rec (pr≢∅ (sym q))
    codeL-inj (c ∷ cs) [] q = Empty.rec (pr≢∅ q)
    codeL-inj (c ∷ cs) (c' ∷ cs') q =
      cong₂ _∷_ (codeT-inj c c' (pr-inj q .fst)) (codeL-inj cs cs' (pr-inj q .snd))
```

<!--en-->
Membership in the limit stage is a closure induction: the empty code is a
numeral, a pair of members of the limit is a member by the finite chapter's
arithmetic (`pr∈limit` below), and the tree and list codes close under the two
formers. The `pr∈limit`{.Agda} lemma is the choice chapter's, transplanted: a
member of the limit has appeared at some finite stage, two stages can be raised
to a common one, and the pair appears two stages later, so it is in the limit.
<!--zh-->
极限阶段中的成员资格是一场封闭性归纳：空码是数码，极限成员的对仍是成员，靠有穷那一章的算术 (下方的 `pr∈limit`)，树码与表码在这两个形成子下封闭。`pr∈limit`{.Agda} 引理移植自选择那一章：极限成员已在某个有穷阶段现身，两个阶段可抬到共同一个，而对出现在两阶之后，故它在极限中。
<!--/-->

```agda
  private
    AtStage : S → Type (ℓ-suc ℓ)
    AtStage x = Σ[ k ∈ ℕ ] ⟨ x ∈ˢ Lset (# k) ⟩

    raiseTo : (x : S) (d k : ℕ) → ⟨ x ∈ˢ Lset (# k) ⟩ → ⟨ x ∈ˢ Lset (# (d + k)) ⟩
    raiseTo x zero    k h = h
    raiseTo x (suc d) k h = Lset-mono (self∈sucV (# (d + k))) (raiseTo x d k h)

    numeral∈limit : (k : ℕ) → ⟨ (# k) ∈ˢ Lset ω ⟩
    numeral∈limit k = Lset-mono (#∈ω (suc k)) (ord∈Lset-suc (# k) (numeral-ord k))

    pr∈limit : (x y : S) → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ y ∈ˢ Lset ω ⟩
             → ⟨ pr x y ∈ˢ Lset ω ⟩
    pr∈limit x y hx hy = PT.rec (snd (pr x y ∈ˢ Lset ω))
      (λ atX → PT.rec (snd (pr x y ∈ˢ Lset ω)) (both atX) (inSome y hy))
      (inSome x hx)
      where
      both : AtStage x → AtStage y → ⟨ pr x y ∈ˢ Lset ω ⟩
      both (j , hj) (k , hk) = Lset-mono (#∈ω (suc (suc (k + j))))
        (pr∈Lset-suc (# (k + j)) x y (raiseTo x k j hj)
          (subst (λ n → ⟨ y ∈ˢ Lset (# n) ⟩) (+-comm j k) (raiseTo y j k hk)))

    codeT∈ω : (t : Tree Lab₀) → ⟨ codeT t ∈ˢ Lset ω ⟩
    codeL∈ω : (ts : List (Tree Lab₀)) → ⟨ codeL ts ∈ˢ Lset ω ⟩
    codeT∈ω (node l cs) = pr∈limit (labCode l) (codeL cs)
      (labCode∈ω l) (codeL∈ω cs)
      where
      labCode∈ω : (l : Lab₀) → ⟨ labCode l ∈ˢ Lset ω ⟩
      labCode∈ω ((i , j , k) , inl tt*) =
        pr∈limit (# i) (pr (# j) (pr (# k) (# 0)))
          (numeral∈limit i)
          (pr∈limit (# j) (pr (# k) (# 0))
            (numeral∈limit j)
            (pr∈limit (# k) (# 0)
              (numeral∈limit k) (numeral∈limit 0)))
      labCode∈ω ((i , j , k) , inr tt*) =
        pr∈limit (# i) (pr (# j) (pr (# k) (# 1)))
          (numeral∈limit i)
          (pr∈limit (# j) (pr (# k) (# 1))
            (numeral∈limit j)
            (pr∈limit (# k) (# 1)
              (numeral∈limit k) (numeral∈limit 1)))
    codeL∈ω [] = numeral∈limit 0
    codeL∈ω (c ∷ cs) = pr∈limit (codeT c) (codeL cs) (codeT∈ω c) (codeL∈ω cs)
```

<!--en-->
## The order, assembled

The two keys bundle into one order: the product of the limit order and the
list order, pulled back along the joint skeleton-and-parameters map. Equal keys
give equal codes and equal parameter lists; the code's injectivity, the
strip-and-graft retraction, and the picture's own injectivity then chain into
the joint map's injectivity, which is all the pull-back needs.
<!--zh-->
## 序，组装

两把键合成一个序：极限序与表序的积，沿「骨架与参数」的联合映射拉回。键相等给出码相等与参数表相等；码的单射性、剥取与回植的收缩，以及图画自身的单射性，串成联合映射的单射性，而拉回只需这一点。
<!--/-->

```agda
  private
    skel : Name → Limit
    skel t = codeT (stripT (toTree t)) , codeT∈ω (stripT (toTree t))

    pars : Name → List ⟪ A ⟫
    pars t = parT (toTree t)

    keyOrder : SWO (Limit × List ⟪ A ⟫)
    keyOrder = prodSWO limitOrder (listSWO w)

    key-inj : (s t : Name) → (skel s , pars s) ≡ (skel t , pars t) → s ≡ t
    key-inj s t q =
      toTree-inj s t (strip-par-inj (toTree s) (toTree t)
        (codeT-inj (stripT (toTree s)) (stripT (toTree t))
          (cong fst (cong fst q)))
        (cong snd q))

  nameOrder : SWO Name
  nameOrder = pullSWO keyOrder (λ t → skel t , pars t) key-inj

  _≺ₙ_ : Name → Name → Type (ℓ-suc ℓ)
  _≺ₙ_ = SWO._<∙_ nameOrder
```

<!--en-->
## The bundle, and the least name

The bundle is the interface the choosing device takes, and the least-name
search is the well-order chapter's search applied to it. The exported names
match the internalized route's chapter, member for member, which is what lets
the step chapter change routes by re-pointing one import.
<!--zh-->
## 束，与最小的名字

这个束就是选取装置取用的接口，而最小名字的搜索就是良序那一章的搜索施于其上。导出的名字与内化路线那一章逐一对应，这正是使步进章只改一个导入即可换路的原因。
<!--/-->

```agda
  leastName : (P : Name → hProp (ℓ-suc ℓ))
            → ∥ Σ[ a ∈ Name ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ Name ] IsLeast nameOrder P a
  leastName = leastOf nameOrder lem
```

<!--en-->
## Recap

A `Name`{.Agda} is an arity-one term; `denote`{.Agda} evaluates it and takes
values; `names-complete`{.Agda} spends the terms chapter's identification as
one transport. The order is assembled, not invented: the skeleton codes into
the limit and orders by the finite chapter's earliest-disagreement order, the
parameter list orders length-gated pointwise by the stage order, and the
product of the two key orders is pulled back along a joint picture whose
injectivity is a left inverse rather than a discrimination matrix.
`leastName`{.Agda} closes the interface, and the step chapter can consume it in
place of the internalized one.
<!--zh-->
## 小结

`Name`{.Agda} 是元数一的项；`denote`{.Agda} 对它求值并取值；`names-complete`{.Agda} 把项那一章的等同当作一次搬运花掉。序是组装而非发明的：骨架编码进极限，按有穷那一章的最先分歧序排序；参数表按给定阶段序作以长度为门的逐点比较；两把键序的积沿联合的画拉回，其单射性是一个左逆、而非一张判别矩阵。`leastName`{.Agda} 合上接口，步进章可以用它顶替内化的那一个。
<!--/-->
