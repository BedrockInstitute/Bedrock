# The level formula

<!--en-->
The initial-segment chapter wrote the face once, generic in the carrier, and
the level-story clause kit wrote the shared tower-story clauses once, generic
in a transitive carrier. This chapter supplies the first instantiation, the
wing's own `W2`, at the real tower: the carrier is a level `Lset α`, the kit
opens at that carrier with the delivered stage theorem as its transitivity,
and the approximation entry, which the face deliberately left as a telescope
slot, is now filled with the tower story itself. The result is the level
formula, the object-language sentence saying that a member of the level is
one of the constructible levels, with its two-way adequacy.

The tower story has five clauses here, four of them the kit's. Functionhood
(pairhood and single-valuedness), the zero clause and the exact domain bound
come from the kit with their formulas and decodes; the limit clause is this
chapter's carrier-specific piece, the constructive form of the classical
union step, and its limit-ordinal premise consumes the kit's ordinal decode.
The successor step, the clause the initial-segment chapter read as its own
Def-step entry, collapses at a level by the theorem that every member of a
stage is definable at a member of that stage. Each clause is written twice,
once at the meta level over the graph and once as an object-language
formula, and the two-way decodes make the object-language sentence mean the
story: the kit's decodes for the shared clauses, and the limit decodes here
for the limit clause.
<!--zh-->
初始段章把面孔一次写成、以载体为参数，层故事子句套件把共享的塔故事子句一次写成、以传递载体为参数。本章交付第一个实例化，即翼自己的 `W2`，落在真实塔上：载体是层 `Lset α`，套件以已交付的阶段定理为传递性在该载体处打开，而面孔刻意留作望远镜槽位的近似条目，现在由塔故事本身填满。成果就是层公式，那条说「载体的某个成员是可构造层之一」的对象语言句子，连同它的双向充分性。

塔故事在此有五条子句，其中四条来自套件。函数性 (成对性与单值性)、零子句与精确定义域界连同各自的公式与解码来自套件；极限子句是本章的载体专属件，即经典并步的构造形式，其极限序数前提消费套件的序数解码。后继步，即初始段章读作自己的 Def 步条目、并经「层的每个成员都在该层的某成员处可定义」这条定理在层处坍缩的那一条。每条子句写两遍，一遍在元层跑在图关系上，一遍是对象语言公式，双向解码使对象语言句子意指这个故事：共享子句用套件的解码，极限子句用本章的极限解码。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.LevelFormula {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ⊤̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using
  ( Lset; Lset-layer; layer-trans; Lset-in; Lset-out
  ; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; isTransV; IsOrd )
open import L.Definability {ℓ} using ( module DefOf )
open import L.InitialSegment {ℓ} using ( _⟷_; DefStep; module Face )
open import L.LevelKit {ℓ} using ( module LevelKit )

open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The limit clause and the approximation at the meta level
<!--zh-->
## 元层的极限子句与近似条目
<!--/-->

<!--en-->
Everything below is relative to one level `u = Lset α` and its binding set
`K`, a member of that level. The level's transitivity, the kit's second
parameter, is the delivered stage theorem, and the kit's pair atoms open at
the carrier. The shared clauses, functionhood, the zero clause and the exact
domain bound, are the kit's meta-level reads over the graph: the pairs
`pr a b` lying in the witness `f`.

The carrier-specific piece is the limit clause. A limit ordinal is an
ordinal that is nonempty and has no greatest member, the honest reading that
needs no dichotomy. At a limit point `(a, y)` of the graph, where `pr a y`
lies in `f` and `a` is such a limit ordinal, the value `y` is exactly the
union of the values below `a`, stated as two graph inclusions: every member
of `y` comes from some pair `pr b z` with `b` in `a`, and every value `z`
reached below `a` lands back in `y`. The approximation entry is the
conjunction of the kit's four clauses and the limit clause, the whole tower
story.
<!--zh-->
以下一切都相对于某一层 `u = Lset α` 及其绑定集 `K`，即该层的一个成员。层的传递性，套件的第二个参数，就是已交付的阶段定理，而套件的对原子在载体处打开。共享子句，函数性、零子句与精确定义域界，就是套件在图关系上的元层读式：落在见证 `f` 里的对 `pr a b`。

载体专属件是极限子句。极限序数是没有最大成员且非空的序数，这个诚实读法不需要两分法。在图关系的极限点 `(a, y)` 处，即 `pr a y` 落在 `f` 里且 `a` 是那样的极限序数时，值 `y` 恰是 `a` 之下诸值之并，写成两条图包含：`y` 的每个成员都来自某个 `b` 在 `a` 里的对 `pr b z`，而在 `a` 之下够到的每个值 `z` 都落回 `y`。近似条目是套件四条子句与极限子句的合取，即完整的塔故事。
<!--/-->

```agda
-- The tower story at the real tower, at the level of the graph.
module LevelAt (α : S) (K : ⟪ Lset α ⟫) where

  u : S
  u = Lset α

  utr : isTransV u
  utr = layer-trans (Lset-layer α)

  module Kit = LevelKit u utr
  open Kit public

  -- The limit-ordinal premise, constructively honest: an ordinal that is
  -- nonempty and has no greatest member.
  isLimit : S → Type (ℓ-suc ℓ)
  isLimit a = IsOrd a × ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ a ⟩ ∥₁
            × ((z : S) → ⟨ z ∈ˢ a ⟩ → ∥ Σ[ w ∈ S ] (⟨ z ∈ˢ w ⟩ × ⟨ w ∈ˢ a ⟩) ∥₁)

  -- The limit clause: at a limit point (a, y) of the graph, y is exactly
  -- the union of the values below a, as two graph inclusions.
  limitClause : S → Type (ℓ-suc ℓ)
  limitClause f = (a y : S) → ⟨ pr a y ∈ˢ f ⟩ → isLimit a
                → ( (z : S) → ⟨ z ∈ˢ y ⟩ → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ a ⟩ × ⟨ pr b z ∈ˢ f ⟩) ∥₁ )
                × ( (z : S) → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ a ⟩ × ⟨ pr b z ∈ˢ f ⟩) ∥₁ → ⟨ z ∈ˢ y ⟩ )

  -- The approximation entry: the whole tower story.
  Approx : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Approx _ f = pairhood f × singleValued f × zeroClause f × exactDom f × limitClause f
```

<!--en-->
## The limit clause at the object level
<!--zh-->
## 对象语言半边的极限子句
<!--/-->

<!--en-->
Each clause gets an object-language formula, in de Bruijn shape with the
bounded quantifiers binding variable zero, so that a formula of arity two
speaks with the witness `f` at variable zero and the read member `x` at
variable one. The kit supplies the shared formulas: `pairForm`, `singleForm`,
`zeroForm`, the ordinal predicate `isOrdAt k` and the exact domain formula
`exactDomForm`, the latter reading the exactness both ways through the two
named inclusions. The pair memberships are written with the kit's pair atom
under a bounded existential, exactly the shape the shared decode reads.

The limit clause is written here with the same discipline. The limit-ordinal
predicate `isLimitAt k` is the kit's ordinal predicate plus the two honest
clauses, nonempty and no-greatest-member, under the same bounded quantifiers.
The clause `limitForm` walks the pairs of the graph: whenever a pair `(a, y)`
lies in `f` with `a` a limit ordinal, the two inclusions that make `y` the
union below `a` follow, written over the bounded memberships the shared
decode reads. The approximation `Ap` is the conjunction of the kit's four
formulas and the limit formula.
<!--zh-->
每条子句都配一条对象语言公式，采用 de Bruijn 形状，有界量词绑定变量零，于是二元公式以见证 `f` 在变量零、被读成员 `x` 在变量一处说话。套件供给共享公式：`pairForm`、`singleForm`、`zeroForm`、序数谓词 `isOrdAt k` 与精确定义域公式 `exactDomForm`，后者经两条具名包含把精确性两头读出。对隶属用套件的对原子配一个有界存在写出，正是共享解码所读的形状。

极限子句用同一纪律在此写出。极限序数谓词 `isLimitAt k` 是套件的序数谓词加上两条诚实子句，非空与无最大成员，在同样的有界量词下。子句 `limitForm` 走过图关系的诸对：每当对 `(a, y)` 落在 `f` 里且 `a` 是极限序数，使 `y` 成为 `a` 之下诸值之并的两条包含便随之而来，写在那条共享解码所读的有界隶属之上。近似 `Ap` 是套件四条公式与极限公式的合取。
<!--/-->

```agda
  -- The limit-ordinal predicate at a variable: an ordinal, nonempty, with
  -- no greatest member.
  isLimitAt : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  isLimitAt k = isOrdAt k ∧̇ (∃̇ (var zero ∈̇ var (suc k)))
             ∧̇ (∀̇∈ (var k)
                  (∃̇ ((var (suc zero) ∈̇ var zero)
                     ∧̇ (var zero ∈̇ var (suc (suc k))))))

  -- The graph atom "pr a y lies in f", the union inclusions and the limit
  -- clause, at the arity-4 environment (y, a, f, x).
  limPr : Formula ⟪ u ⟫ 4
  limPr = ∃̇∈ (var (suc (suc zero)))
            (PK.prAt zero (suc (suc zero)) (suc zero))

  limIn : Formula ⟪ u ⟫ 4
  limIn = ∀̇ ( (var zero ∈̇ var (suc zero))
           ⇒̇ ∃̇∈ (var (suc (suc zero)))
                (∃̇∈ (var (suc (suc (suc (suc zero)))))
                     (PK.prAt zero (suc zero) (suc (suc zero)))) )

  limOut : Formula ⟪ u ⟫ 4
  limOut = ∀̇ ( ∃̇∈ (var (suc (suc zero)))
                (∃̇∈ (var (suc (suc (suc (suc zero)))))
                     (PK.prAt zero (suc zero) (suc (suc zero))))
           ⇒̇ (var zero ∈̇ var (suc zero)) )

  -- The limit clause: at a limit point (a, y) of the graph, y is the
  -- union of the values below a, as two inclusions.
  limitForm : Formula ⟪ u ⟫ 2
  limitForm = ∀̇ ( ∀̇ ( isLimitAt (suc zero) ⇒̇ (limPr ⇒̇ (limIn ∧̇ limOut)) ) )

  -- The approximation, the Def-step (collapsed at a level) and the range
  -- read, at the object level.
  Ap : Formula ⟪ u ⟫ 2
  Ap = pairForm ∧̇ singleForm ∧̇ zeroForm ∧̇ exactDomForm ∧̇ limitForm
```

<!--en-->
## The limit decodes
<!--zh-->
## 极限解码
<!--/-->

<!--en-->
The approximation entry's adequacy is one two-way decode: a satisfied object
clause is the corresponding meta-level read, and conversely. The kit already
decodes the shared clauses: the innermost pair membership `pair∈`, the
pairhood, single-valuedness, zero and exact-domain decodes, the ordinal
decode `isOrd-out`/`isOrd-in` and the range read. What remains here is the
limit clause. The limit-ordinal decode `isLimit-out`/`isLimit-in` is the
kit's ordinal decode plus the two honest clauses, nonempty and
no-greatest-member, each a truncated walk. The union decode `limit-out`/
`limit-in` walks the graph's pairs, reading the premises through `pair∈` and
assembling the two inclusions from the limit premise. The pattern is the
chapter's standing discipline: every truncated branch is a named `where`
function with a written type, so the inner satisfaction machinery elaborates
once per branch.
<!--zh-->
近似条目的充分性是一条双向解码：被满足的对象子句就是对应的元层读式，反之亦然。套件已解码共享子句：最内层的对隶属 `pair∈`，成对性、单值性、零子句与精确定义域的解码，序数解码 `isOrd-out`/`isOrd-in` 与像的读式。此处所余是极限子句。极限序数解码 `isLimit-out`/`isLimit-in` 是套件的序数解码加上两条诚实子句，非空与无最大成员，各是一次截断行走。并解码 `limit-out`/`limit-in` 走过图关系的诸对，经 `pair∈` 读取前提，从极限前提装配两条包含。模式是本章的一贯纪律：每个截断分支都是带书面类型的具名 `where` 函数，于是内层满足机器每个分支只展开一次。
<!--/-->

```agda
  -- The limit-ordinal predicate: satisfaction is a limit ordinal.
  isLimit-out : {n : ℕ} (k : Fin n) (δ : Vec SM n)
              → ⟨ δ ⊨ᵐ isLimitAt k ⟩ → isLimit (fst (lookup k δ))
  isLimit-out k δ (h₁ , (h₂ , h₃)) = (isOrd-out k δ h₁ , nonempty , nogreat)
    where
    A = fst (lookup k δ)
    nonempty : ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ A ⟩ ∥₁
    nonempty = PT.rec squash₁ go h₂
      where
      go : Σ[ zm ∈ SM ] ⟨ (zm ∷ δ) ⊨ᵐ (var zero ∈̇ var (suc k)) ⟩
         → ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ A ⟩ ∥₁
      go (zm , sat) = ∣ fst zm , sat ∣₁
    nogreat : (z : S) → ⟨ z ∈ˢ A ⟩ → ∥ Σ[ w ∈ S ] (⟨ z ∈ˢ w ⟩ × ⟨ w ∈ˢ A ⟩) ∥₁
    nogreat z z∈A = PT.rec squash₁ go (h₃ zm z∈A)
      where
      zm : SM
      zm = PK.pt z (utr {x = A} {y = z} z∈A (snd (lookup k δ)))
      go : Σ[ wm ∈ SM ]
             ⟨ (wm ∷ zm ∷ δ)
               ⊨ᵐ ((var (suc zero) ∈̇ var zero)
                 ∧̇ (var zero ∈̇ var (suc (suc k)))) ⟩
         → ∥ Σ[ w ∈ S ] (⟨ z ∈ˢ w ⟩ × ⟨ w ∈ˢ A ⟩) ∥₁
      go (wm , (z∈w , w∈A)) = ∣ fst wm , (z∈w , w∈A) ∣₁

  isLimit-in : {n : ℕ} (k : Fin n) (δ : Vec SM n) → isLimit (fst (lookup k δ))
             → ⟨ δ ⊨ᵐ isLimitAt k ⟩
  isLimit-in k δ (ord , nonempty , nogreat) = (isOrd-in k δ ord , ne-sat , ng-sat)
    where
    A = fst (lookup k δ)
    ne-sat : ⟨ δ ⊨ᵐ ∃̇ (var zero ∈̇ var (suc k)) ⟩
    ne-sat = PT.rec squash₁ go nonempty
      where
      go : Σ[ z ∈ S ] ⟨ z ∈ˢ A ⟩ → ⟨ δ ⊨ᵐ ∃̇ (var zero ∈̇ var (suc k)) ⟩
      go (z , z∈A) = ∣ zm , z∈A ∣₁
        where
        zm : SM
        zm = PK.pt z (utr {x = A} {y = z} z∈A (snd (lookup k δ)))
    ng-sat : ⟨ δ ⊨ᵐ ∀̇∈ (var k)
               (∃̇ ((var (suc zero) ∈̇ var zero)
                  ∧̇ (var zero ∈̇ var (suc (suc k))))) ⟩
    ng-sat zm z∈A = PT.rec squash₁ go (nogreat (fst zm) z∈A)
      where
      go : Σ[ w ∈ S ] (⟨ fst zm ∈ˢ w ⟩ × ⟨ w ∈ˢ A ⟩)
         → ⟨ (zm ∷ δ) ⊨ᵐ ∃̇ ((var (suc zero) ∈̇ var zero)
                          ∧̇ (var zero ∈̇ var (suc (suc k)))) ⟩
      go (w , (z∈w , w∈A)) = ∣ wm , (z∈w , w∈A) ∣₁
        where
        wm : SM
        wm = PK.pt w (utr {x = A} {y = w} w∈A (snd (lookup k δ)))

  -- The limit clause: satisfaction is the union condition at limit points.
  limit-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ limitForm ⟩
            → limitClause (fst f)
  limit-out f x h a y ay∈f limA = (in-part , out-part)
    where
    pr∈u : ⟨ pr a y ∈ˢ u ⟩
    pr∈u = utr {x = fst f} {y = pr a y} ay∈f (snd f)
    am : SM
    am = PK.pt a (PM.pair-left {a = a} {b = y} pr∈u)
    ym : SM
    ym = PK.pt y (PM.pair-right {a = a} {b = y} pr∈u)
    premise-sat : ⟨ (ym ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ isLimitAt (suc zero) ⟩
    premise-sat = isLimit-in (suc zero) (ym ∷ am ∷ f ∷ ι x ∷ []) limA
    body : ⟨ (ym ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ (limIn ∧̇ limOut) ⟩
    body = h am ym premise-sat
      (pair∈ (suc (suc zero)) (suc zero) zero
        (ym ∷ am ∷ f ∷ ι x ∷ []) .snd ay∈f)
    in-part : (z : S) → ⟨ z ∈ˢ y ⟩ → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ a ⟩ × ⟨ pr b z ∈ˢ fst f ⟩) ∥₁
    in-part z z∈y = PT.rec squash₁ go (body .fst zm z∈y)
      where
      zm : SM
      zm = PK.pt z (utr {x = y} {y = z} z∈y (PM.pair-right {a = a} {b = y} pr∈u))
      go : Σ[ bm ∈ SM ] ( ⟨ fst bm ∈ˢ a ⟩
               × ⟨ (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ [])
                   ⊨ᵐ (∃̇∈ (var (suc (suc (suc (suc zero)))))
                        (PK.prAt zero (suc zero) (suc (suc zero)))) ⟩ )
         → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ a ⟩ × ⟨ pr b z ∈ˢ fst f ⟩) ∥₁
      go (bm , (b∈a , sat)) = ∣ fst bm , (b∈a ,
        pair∈ (suc (suc (suc (suc zero)))) zero (suc zero)
          (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ []) .fst sat) ∣₁
    out-part : (z : S) → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ a ⟩ × ⟨ pr b z ∈ˢ fst f ⟩) ∥₁
             → ⟨ z ∈ˢ y ⟩
    out-part z = PT.rec (snd (z ∈ˢ y)) go
      where
      go : Σ[ b ∈ S ] (⟨ b ∈ˢ a ⟩ × ⟨ pr b z ∈ˢ fst f ⟩) → ⟨ z ∈ˢ y ⟩
      go (b , (b∈a , bz∈f)) = body .snd zm (∣ bm , (b∈a , sat) ∣₁)
        where
        bz∈u : ⟨ pr b z ∈ˢ u ⟩
        bz∈u = utr {x = fst f} {y = pr b z} bz∈f (snd f)
        bm : SM
        bm = PK.pt b (PM.pair-left {a = b} {b = z} bz∈u)
        zm : SM
        zm = PK.pt z (PM.pair-right {a = b} {b = z} bz∈u)
        sat : ⟨ (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ [])
                ⊨ᵐ (∃̇∈ (var (suc (suc (suc (suc zero)))))
                     (PK.prAt zero (suc zero) (suc (suc zero)))) ⟩
        sat = pair∈ (suc (suc (suc (suc zero)))) zero (suc zero)
                (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ []) .snd bz∈f

  limit-in : (f : SM) (x : ⟪ u ⟫) → limitClause (fst f)
           → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ limitForm ⟩
  limit-in f x lc am ym prem prSat = (in-sat , out-sat)
    where
    ay∈f : ⟨ pr (fst am) (fst ym) ∈ˢ fst f ⟩
    ay∈f = pair∈ (suc (suc zero)) (suc zero) zero
      (ym ∷ am ∷ f ∷ ι x ∷ []) .fst prSat
    cond : ( (z : S) → ⟨ z ∈ˢ fst ym ⟩ → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ fst am ⟩ × ⟨ pr b z ∈ˢ fst f ⟩) ∥₁ )
          × ( (z : S) → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ fst am ⟩ × ⟨ pr b z ∈ˢ fst f ⟩) ∥₁ → ⟨ z ∈ˢ fst ym ⟩ )
    cond = lc (fst am) (fst ym) ay∈f
      (isLimit-out (suc zero) (ym ∷ am ∷ f ∷ ι x ∷ []) prem)
    in-sat : ⟨ (ym ∷ am ∷ f ∷ ι x ∷ [])
               ⊨ᵐ ∀̇ ((var zero ∈̇ var (suc zero))
                   ⇒̇ ∃̇∈ (var (suc (suc zero)))
                        (∃̇∈ (var (suc (suc (suc (suc zero)))))
                             (PK.prAt zero (suc zero) (suc (suc zero))))) ⟩
    in-sat zm z∈y = PT.rec squash₁ go (cond .fst (fst zm) z∈y)
      where
      go : Σ[ b ∈ S ] (⟨ b ∈ˢ fst am ⟩ × ⟨ pr b (fst zm) ∈ˢ fst f ⟩)
         → ⟨ (zm ∷ ym ∷ am ∷ f ∷ ι x ∷ [])
              ⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                   (∃̇∈ (var (suc (suc (suc (suc zero)))))
                        (PK.prAt zero (suc zero) (suc (suc zero)))) ⟩
      go (b , (b∈a , bz∈f)) = ∣ bm , (b∈a , sat) ∣₁
        where
        bz∈u : ⟨ pr b (fst zm) ∈ˢ u ⟩
        bz∈u = utr {x = fst f} {y = pr b (fst zm)} bz∈f (snd f)
        bm : SM
        bm = PK.pt b (PM.pair-left {a = b} {b = fst zm} bz∈u)
        sat : ⟨ (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ [])
                ⊨ᵐ (∃̇∈ (var (suc (suc (suc (suc zero)))))
                     (PK.prAt zero (suc zero) (suc (suc zero)))) ⟩
        sat = pair∈ (suc (suc (suc (suc zero)))) zero (suc zero)
                (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ []) .snd bz∈f
    out-sat : ⟨ (ym ∷ am ∷ f ∷ ι x ∷ [])
                ⊨ᵐ ∀̇ ( ∃̇∈ (var (suc (suc zero)))
                       (∃̇∈ (var (suc (suc (suc (suc zero)))))
                            (PK.prAt zero (suc zero) (suc (suc zero))))
                    ⇒̇ (var zero ∈̇ var (suc zero)) ) ⟩
    out-sat zm = PT.rec (snd (fst zm ∈ˢ fst ym)) go
      where
      go : Σ[ bm ∈ SM ] ( ⟨ fst bm ∈ˢ fst am ⟩
               × ⟨ (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ [])
                   ⊨ᵐ (∃̇∈ (var (suc (suc (suc (suc zero)))))
                        (PK.prAt zero (suc zero) (suc (suc zero)))) ⟩ )
         → ⟨ fst zm ∈ˢ fst ym ⟩
      go (bm , (b∈a , sat)) = cond .snd (fst zm) ∣ fst bm , (b∈a ,
        pair∈ (suc (suc (suc (suc zero)))) zero (suc zero)
          (bm ∷ zm ∷ ym ∷ am ∷ f ∷ ι x ∷ []) .fst sat) ∣₁
```

<!--en-->
With the limit decodes in hand, the approximation adequacy assembles the
kit's four decodes and the limit decode: the satisfaction of `Ap` is the
tower story, and the tower story builds the satisfaction, conjunct by
conjunct.
<!--zh-->
极限解码在手，近似充分性随即把套件的四条解码与极限解码装配起来：`Ap` 的满足就是塔故事，塔故事也逐合取项建回满足。
<!--/-->

```agda
  -- The approximation adequacy, both directions, walking the five conjuncts.
  ap-out : (f : SM) (x : ⟪ u ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩
         → Approx u (fst f)
  ap-out f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-out f x h₁
    , ( single-out f x h₂
      , ( zero-out f x h₃ , ( exactDom-out f x h₄ , limit-out f x h₅ ) ) ) )

  ap-in : (f : SM) (x : ⟪ u ⟫) → Approx u (fst f)
        → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩
  ap-in f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-in f x h₁
    , ( single-in f x h₂
      , ( zero-in f x h₃ , ( exactDom-in f x h₄ , limit-in f x h₅ ) ) ) )

  a-ok : (f : SM) (x : ⟪ u ⟫)
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Ap ⟩ ⟷ Approx u (fst f)
  a-ok f x = ap-out f x , ap-in f x
```

<!--en-->
## The Def-step and the range
<!--zh-->
## Def 步与像
<!--/-->

<!--en-->
The Def-step clause is the successor clause of the tower story, and at a level
it collapses. The collapse theorem, that every member of a stage is definable
at a member of that stage, unfolds the union at the carrier once: a member of
`Lset α` sits in `𝒟ₒ (Lset δ)` for some `δ ∈ α`, the definable-power inverse
names a formula, and `Lset δ` itself belongs to the carrier by the tower's
entry lemma applied to the fact that every set is definable in itself. So the
clause `Cl = ⊤̇`, the kit's truth clause, decodes to the delivered Def-step
read in the forward direction, and the reverse direction is the truth clause
itself.

The range read is the graph's second-component projection: `x` lies in the
range of `f` when some `a` has `pr a x` in `f`. The kit hosts the object
clause `Rg`, a bounded existential over the members of `f` naming a pair
whose second component is `x`, and its two-way decode `r-ok`.
<!--zh-->
Def 步子句就是塔故事的后继子句，而在层处它坍缩。坍缩定理，「层的每个成员都在该层的某成员处可定义」，把载体处的并展开一次：`Lset α` 的成员对某 `δ ∈ α` 落在 `𝒟ₒ (Lset δ)` 里，可定义幂的逆点名一条公式，而 `Lset δ` 自身经塔的进入引理施于「每个集合都在自身中可定义」而属于载体。于是子句 `Cl = ⊤̇`，即套件的真子句，在前进方向解码到已交付的 Def 步读式，反向就是真子句本身。

像的读式是图关系的第二分量投影：当某 `a` 使 `pr a x` 落在 `f` 里，`x` 就落在 `f` 的像中。套件托管对象子句 `Rg`，即对 `f` 成员的有界存在，点名一个以 `x` 为第二分量的对，连同它的双向解码 `r-ok`。
<!--/-->

```agda
  collapse : (g : S) → ⟨ g ∈ˢ u ⟩ → DefStep u g
  collapse g g∈u = PT.rec squash₁ step (Lset-out α g g∈u)
    where
    step : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ g ∈ˢ 𝒟ₒ (Lset δ) ⟩) → DefStep u g
    step (δ , (δ∈α , g∈𝒟ₒ)) = PT.rec squash₁ go (𝒟ₒ-inv (Lset δ) g g∈𝒟ₒ)
      where
      go : Σ[ φ ∈ Formula ⟪ Lset δ ⟫ 1 ] (DefOf.defSet (Lset δ) φ ≡ g)
         → DefStep u g
      go (φ , e) = ∣ Lset δ , (φ , (w∈u , e)) ∣₁
        where
        w∈u : ⟨ Lset δ ∈ˢ u ⟩
        w∈u = Lset-in α δ (Lset δ) δ∈α
          (𝒟ₒ-intro (Lset δ) (Lset δ)
            ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset δ) ∣₁)

  c-ok : (f : SM) (x : ⟪ u ⟫)
       → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ ⟷ DefStep u (fst f)
  c-ok f x = (λ _ → collapse (fst f) (snd f)) , (λ _ → tt*)
```

<!--en-->
## The read-off
<!--zh-->
## 读出
<!--/-->

<!--en-->
The four telescope entries are now filled at the real tower, and the face's
adequacy module assembles them into the level formula's two-way adequacy: a
member `m` of the level lies in the definable set carved by the formula exactly
when some initial segment of the tower, a member of the binding set, lies in
the carrier, approximates the tower, applies the definable step, and ranges
over `m`. `read-off` is the delivered object, the consumer's take-away, with
the carrier `u`, the binding set `K` and the level index `α` as parameters.
<!--zh-->
望远镜的四项如今在真实塔处填满，面孔的充分性模块把它们装配成层公式的双向充分性：层的成员 `m` 落在公式刻出的可定义集里，当且仅当某条塔的初始段，绑定集的成员，落在载体内、近似整座塔、施以可定义步并以 `m` 为像。`read-off` 就是交付对象，消费方的所得，以载体 `u`、绑定集 `K` 与层索引 `α` 为参数。
<!--/-->

```agda
  module F = Face u K Ap Cl Rg
  module A = F.Adequacy Approx a-ok c-ok r-ok

  -- The two-way adequacy at the real tower.
  read-off : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet F.σ ⟩ ⟷ A.Elem m
  read-off = A.face-iff
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the wing's level formula at the real tower: the
approximation entry of the initial-segment face is now the tower story itself,
the kit's four clauses (pairhood, single-valuedness, the zero clause and the
exact domain bound) with their shared decodes, plus this chapter's limit
clause with its limit decodes, and the Def-step collapse and the range read
completing the four entries, with the two-way adequacy `read-off` against the
delivered `defSet` face. The shared kit is consumed, not re-derived; the
remaining carrier-specific content is the limit clause and the collapse. The
face's other two consumers, the bridge's `L-sigma` at a rud carrier and the
condensation crossing, reuse the same kit and the same instantiation recipe:
the carrier, the clause formulas, and the decode discipline, each at its own
tower. The orchestrator wires this chapter into `Everything`.
<!--zh-->
本章在真实塔处交付翼的层公式：初始段面孔的近似条目如今就是塔故事本身，套件的四条子句 (成对性、单值性、零子句与精确定义域界) 连同它们的共享解码，加上本章的极限子句与极限解码，而 Def 步坍缩与像的读式补全四项，以及对照已交付 `defSet` 面孔的双向充分性 `read-off`。共享套件被消费，而非重推；所余的载体专属内容是极限子句与坍缩。面孔的另两个消费方，rud 载体上的桥 `L-sigma` 与凝聚跨越，复用同一套件与同一条实例化配方：载体、子句公式与解码纪律，各在自己的塔处。编排者把本章接入 `Everything`。
<!--/-->
