# The initial-segment story

<!--en-->
Part 4 builds the constructible tower level by level with the `Def` step.
This chapter asks what the tower's own story looks like told inside a carrier,
and writes the answer once, generic in the carrier. Devlin's initial-segment
characterization says a set `x` sits in a level exactly when some L-tower
initial segment `f` reaches it: `f` is a function whose domain is an ordinal in
the carrier, starts at the empty set, applies `Def` at each successor stage and
takes unions at each limit stage, and `x` lies in `f`'s range. As one
object-language formula, `σ(x) := ∃ f ∈ K(u) [ Ap(f) ∧ Cl(f,x) ∧ Rg(f,x) ]`:
one conjunct for the approximation, one for the Def-step at each stage, one for
the range read, with the witness `f` bound to the carrier's own binding set
`K(u)`.

The chapter proves the statement layer of that sentence at the generic carrier:
the two readings, in and out, and the two-way adequacy against the delivered
`defSet` face. The tower content enters only as the adequacy telescope, four
named entries that every consumer supplies; the instantiations (the wing's own
`W2`, the bridge's `L-sigma`, the condensation crossing) are consumers' work
and are not built here.
<!--zh-->
第四部用 `Def` 步一级级建成可构造之塔。本章追问：这座塔自己的故事，在载体内部讲出来是什么样，并把这个答案一次写成、以载体为参数。Devlin 的初始段刻画说：集合 `x` 落在某一层，当且仅当某个 L 塔初始段 `f` 够到它，其中 `f` 是定义域为载体内序数的函数，从空集出发，在每个后继处施以 `Def`、在每个极限处取并，而 `x` 落在 `f` 的像内。写成一条对象语言公式就是 `σ(x) := ∃ f ∈ K(u) [ Ap(f) ∧ Cl(f,x) ∧ Rg(f,x) ]`：一个合取项管近似，一个管每一阶段的 Def 步，一个管像的读取，见证 `f` 被绑定到载体自己的绑定集 `K(u)` 上。

本章在通用载体处证明这句话的陈述层：两条读式 (进与出)，以及对照已交付 `defSet` 面孔的双向充分性。塔的内容只以充分性望远镜的形式进入，四项具名条目由每个消费方供给；各类实例化 (翼自己的 `W2`、桥的 `L-sigma`、凝聚跨越) 是消费方的事，不在本章建造。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.InitialSegment {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_; _∧̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The meta-level reads
<!--zh-->
## 元层读式
<!--/-->

<!--en-->
Three clauses make up the story. Two of their meta-level readings are cheap
enough for the face to own, stated once and concrete. The range read `x ∈ran f`
says some coded pair `pr a x` lies in `f`, using the pair coding of the V
chapter. The Def-step read `DefStep u f` says `f` is a definable set at some
member `w` of the carrier, the successor clause of Devlin's formula, using only
the delivered `defSet`. The third read, the approximation, is different in
kind: "f is an L-tower initial segment" means functionhood, the zero step, the
limit step and the domain bound, which is the tower story itself and cannot
mean anything at an arbitrary carrier. It therefore enters as a telescope entry
of the adequacy interface rather than as a definition here. Finally the one
combinator the adequacy needs, the carrier-level bidirectional claim `_⟷_`, is
pinned: stated over types, never through content-of, so every implicit in the
proofs is solved from a path or a Π type.
<!--zh-->
故事由三个子句组成，其中两个的元层读式便宜到面孔可以自己拥有，一次写成、保持具体。像的读式 `x ∈ran f` 说某个编码对 `pr a x` 落在 `f` 里，用的是 V 章的对编码。Def 步读式 `DefStep u f` 说 `f` 是载体某成员 `w` 处的可定义集，即 Devlin 公式的后继子句，只消费已交付的 `defSet`。第三个读式，近似，性质不同：「`f` 是 L 塔初始段」意味着函数性、零步、极限步与定义域界，这本身就是塔的故事，在任意载体处没有意义。所以它不作为本章的定义，而以望远镜条目的身份进入充分性接口。最后钉下充分性唯一需要的那个组合子，载体级的双向断言 `_⟷_`：在类型上陈述，绝不穿过 content-of，于是证明里的每个隐式参数都从一条路径或一个 Π 型解出。
<!--/-->

```agda
infix 1 _⟷_
_⟷_ : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
A ⟷ B = (A → B) × (B → A)

infix 5 _∈ran_

-- The range read, at the meta level: x ∈ ran f iff some a has pr a x ∈ f.
_∈ran_ : V ℓ → V ℓ → Type (ℓ-suc ℓ)
x ∈ran f = ∥ Σ[ a ∈ V ℓ ] ⟨ pr a x ∈ˢ f ⟩ ∥₁

-- The Def-step at each stage, at the meta level: f is a definable set at some
-- member w of the carrier (the successor clause of Devlin's initial-segment
-- formula, dev6.txt:1665-1678).
DefStep : V ℓ → V ℓ → Type (ℓ-suc ℓ)
DefStep u f = ∥ Σ[ w ∈ V ℓ ] Σ[ φ ∈ Formula ⟪ w ⟫ 1 ]
                ( ⟨ w ∈ˢ u ⟩ × (DefOf.defSet w φ ≡ f) ) ∥₁
```

<!--en-->
## The face, written once
<!--zh-->
## 面孔，只写一次
<!--/-->

<!--en-->
The face is one module, `Face u K Ap Cl Rg`, with the carrier, the binding set
and the three object-language clauses as module parameters that stay abstract
through the walk (P-h at full strength). `σ` is the bounded existential over
the constant `con K`; its two free variables are the witness `f` and the read
member `x`, and by convention every conjunct has arity two, `Ap` and `Cl`
speaking only about `f` and `Rg` about both. The two readings are the whole
statement layer: `σ-in` packs the K-binding and the three clause satisfactions
into a satisfied σ, `σ-out` unpacks a satisfied σ into the truncated payload,
and both are definitional identities under the hPropAlgebra clauses (the
bounded existential's `⋁` is a truncated sigma, the `⊓` a dependent pair). The
paper statement's "f lies in the carrier" conjunct is carried by the
inner-world carrier `SM` itself and never written down (the D-16 working
face).
<!--zh-->
面孔是一个模块 `Face u K Ap Cl Rg`，载体、绑定集与三条对象语言子句都是模块参数，贯穿全篇保持抽象 (P-h 满强度)。`σ` 是常量 `con K` 上的有界存在；两个自由变量分别是见证 `f` 与被读成员 `x`，约定每个合取项都有二元数，`Ap`、`Cl` 只谈 `f`，`Rg` 两者都谈。两条读式就是整个陈述层：`σ-in` 把 K 绑定与三条子句的满足打包进一个被满足的 σ，`σ-out` 把被满足的 σ 拆成截断载荷，二者在 hPropAlgebra 子句下都是定义性同一 (有界存在的 `⋁` 是截断 sigma，`⊓` 是依赖对)。论文陈述里「f 落在载体中」的合取项由内层载体 `SM` 自己携带，从不写下来 (D-16 工作面)。
<!--/-->

```agda
module Face (u : V ℓ) (K : ⟪ u ⟫)
            (Ap Cl Rg : Formula ⟪ u ⟫ 2) where

  module U = DefOf u
  open U using ( SM; ι; _⊨ᵐ_; defSet; defSet-mem )

  -- The initial-segment story as one Σ₁ formula: some L-tower initial
  -- segment f from the binding set K(u) approximates the tower, applies
  -- the Def-step at each stage, and ranges over x.  Variable 0 is the
  -- witness f, variable 1 the read member x; Ap and Cl speak only about
  -- f, Rg about both.
  σ : Formula ⟪ u ⟫ 1
  σ = ∃̇∈ (con K) (Ap ∧̇ (Cl ∧̇ Rg))

  Payload : ⟪ u ⟫ → Type (ℓ-suc ℓ)
  Payload x = Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                          × ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩
                          × ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩
                          × ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩ )

  -- The two readings, at the generic carrier: a satisfied bounded
  -- existential IS the truncated sigma of the K-binding, the
  -- approximation, the Def-step clause and the range read (hPropAlgebra
  -- clauses: ⋁ = ∃[]-syntax, ⊓ = dependent pair).
  σ-in : (x : ⟪ u ⟫) (f : SM)
       → ⟨ fst f ∈ˢ fst (ι K) ⟩ → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
       → ⟨ (ι x ∷ []) ⊨ᵐ σ ⟩
  σ-in x f hK hAp hCl hRg = ∣ f , (hK , (hAp , (hCl , hRg))) ∣₁

  σ-out : (x : ⟪ u ⟫) → ⟨ (ι x ∷ []) ⊨ᵐ σ ⟩ → ∥ Payload x ∥₁
  σ-out x h = h
```

<!--en-->
## The adequacy interface
<!--zh-->
## 充分性接口
<!--/-->

<!--en-->
To instantiate, a consumer supplies exactly the four entries of `Adequacy`'s
telescope. First the meta-level approximation read `Approx u f`, the tower
story (functionhood, the zero step, the limit step, the domain bound) as the
consumer's tower means it; the face records it as a parameter because a generic
carrier has no tower. Then the three adequacies, each an object clause's
satisfaction read against its meta-level read: `a-ok` for the approximation,
`c-ok` for the Def-step, `r-ok` for the range read. Every hypothesis is a named
parameter at its consumption site, and nothing else is assumed: no transitivity,
no rud closure, no LEM.

With the telescope filled, `Elem x` is the external reading, "x is in the range
of some L-tower initial segment lying in the carrier", read at the meta level.
`face-in` and `face-out` prove it equivalent, in both directions, to membership
in the delivered `defSet σ`: membership, then `defSet-mem`, then the σ-out
reading, then the three parameter adequacies, and back. `face-iff` packages the
two-way adequacy.
<!--zh-->
要实例化，消费方恰好供给 `Adequacy` 望远镜的四项。第一项是元层近似读式 `Approx u f`，即消费方自己的塔所意味的塔故事 (函数性、零步、极限步、定义域界)；面孔把它记为参数，因为通用载体没有塔。然后三条充分性，每条都是对象子句的满足对照其元层读式：`a-ok` 管近似，`c-ok` 管 Def 步，`r-ok` 管像的读取。每个前提都是在消费现场具名的参数，此外一无所取：不要传递性，不要 rud 闭包，不要 LEM。

望远镜填满后，`Elem x` 就是外部读式，「x 落在某个位于载体内的 L 塔初始段的像里」，在元层读出。`face-in` 与 `face-out` 证明它与已交付 `defSet σ` 的隶属双向等价：隶属，经 `defSet-mem`，经 σ-out 读式，再经三条参数充分性，再原路返回。`face-iff` 把双向充分性打包。
<!--/-->

```agda
  module Adequacy (Approx : V ℓ → V ℓ → Type (ℓ-suc ℓ))
                  (a-ok : (f : SM) (x : ⟪ u ⟫)
                          → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩ ⟷ Approx u (fst f))
                  (c-ok : (f : SM) (x : ⟪ u ⟫)
                          → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ ⟷ DefStep u (fst f))
                  (r-ok : (f : SM) (x : ⟪ u ⟫)
                          → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩ ⟷ (⟪ u ⟫↪ x) ∈ran (fst f)) where

    -- The external reading: x is in the range of some L-tower initial
    -- segment lying in the carrier, with the tower content read at the
    -- meta level (Approx), the Def-step at each stage (DefStep) and the
    -- range read (∈ran).
    Elem : ⟪ u ⟫ → Type (ℓ-suc ℓ)
    Elem x = ∥ Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                           × Approx u (fst f)
                           × DefStep u (fst f)
                           × ((⟪ u ⟫↪ x) ∈ran fst f) ) ∥₁

    -- The two-way adequacy against the delivered defSet face.  The tower
    -- content enters here and ONLY here, through the three recorded
    -- adequacies; everything else is hypothesis-free (no transitivity,
    -- no rud-closure, no LEM).
    face-in : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩ → Elem m
    face-in m h = PT.map step (σ-out m (subst ⟨_⟩ (defSet-mem σ m) h))
      where
      step : Payload m
           → Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                          × Approx u (fst f)
                          × DefStep u (fst f)
                          × ((⟪ u ⟫↪ m) ∈ran fst f) )
      step (f , hK , hAp , hCl , hRg) =
        f , ( hK , (a-ok f m .fst hAp , (c-ok f m .fst hCl , r-ok f m .fst hRg)) )

    face-out : (m : ⟪ u ⟫) → Elem m → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩
    face-out m = PT.rec (snd (⟪ u ⟫↪ m ∈ˢ defSet σ)) go
      where
      go : Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                        × Approx u (fst f)
                        × DefStep u (fst f)
                        × ((⟪ u ⟫↪ m) ∈ran fst f) )
         → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩
      go (f , hK , hAp , hDef , hRan) =
        subst ⟨_⟩ (sym (defSet-mem σ m))
          (σ-in m f hK (a-ok f m .snd hAp) (c-ok f m .snd hDef) (r-ok f m .snd hRan))

    face-iff : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩ ⟷ Elem m
    face-iff m = face-in m , face-out m
```

<!--en-->
## The face is content-free
<!--zh-->
## 面孔与内容无关
<!--/-->

<!--en-->
The statement layer provably depends on nothing in the tower content. At the
generic carrier the same module checks for a garbage triple of atomic formulas
(each a distinct variable pattern), so neither `σ-in` nor `σ-out` ever mentions
the approximation, the Def-step, or the range content. The negative controls
were run during development and removed: `σ-out` claimed at a swapped conjunct
order, `σ-in` dropping the K-binding conjunct, and the adequacy direction with
`a-ok` or `r-ok` missing are all rejected by the typechecker.
<!--zh-->
陈述层可证地不依赖塔内容的任何部分。在通用载体处，同一个模块对一组垃圾原子公式三元组 (三条各异的变量模式) 照样通过，于是 `σ-in` 与 `σ-out` 从不用到近似、Def 步或像的内容。负向对照在开发时跑过即删：在调换合取顺序处声称 `σ-out`、丢掉 K 绑定合取项声称 `σ-in`、缺 `a-ok` 或缺 `r-ok` 声称充分性方向，都会被类型检查器拒绝。
<!--/-->

```agda
module Perturb (u : V ℓ) (K : ⟪ u ⟫) where

  module U = DefOf u
  open U using ( ι; _⊨ᵐ_ )

  junk1 junk2 junk3 : Formula ⟪ u ⟫ 2
  junk1 = var zero ∈̇ var zero
  junk2 = var (suc zero) ∈̇ var zero
  junk3 = var zero ∈̇ var (suc zero)

  module J = Face u K junk1 junk2 junk3

  ctl-in : (x : ⟪ u ⟫) (f : U.SM) → ⟨ fst f ∈ˢ fst (ι K) ⟩
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ junk1 ⟩ → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ junk2 ⟩
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ junk3 ⟩ → ⟨ (ι x ∷ []) ⊨ᵐ J.σ ⟩
  ctl-in x f hK h1 h2 h3 = J.σ-in x f hK h1 h2 h3

  ctl-out : (x : ⟪ u ⟫) → ⟨ (ι x ∷ []) ⊨ᵐ J.σ ⟩ → ∥ J.Payload x ∥₁
  ctl-out x h = J.σ-out x h
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the reusable core of the face: the concrete meta-level
reads (the range read and the Def-step) with the approximation read recorded in
the telescope, the σ-form with its two readings at the generic carrier, and the
two-way adequacy against the delivered `defSet` face consuming exactly the four
telescope entries. The instantiations belong to the consumers: the wing's `W2`,
the bridge's `L-sigma` at a rud carrier, and the condensation crossing each
supply the carrier, the formulas, and the adequacies, and the orchestrator
wires this chapter into `Everything`.
<!--zh-->
本章交付面孔的可复用核心：具体的元层读式 (像、Def 步) 连同记入望远镜的近似读式，通用载体处的 σ 公式与它的两条读式，以及恰好消费望远镜四项的、对照已交付 `defSet` 面孔的双向充分性。实例化属于消费方：翼的 `W2`、rud 载体上的桥 `L-sigma` 与凝聚跨越，各自供给载体、公式与充分性；编排者把本章接入 `Everything`。
<!--/-->
