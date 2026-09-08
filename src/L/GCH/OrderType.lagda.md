<!--en-->
# Constructing order types inside L

A well-founded, transitive relation coded in `L` can be collapsed internally. This chapter builds the collapse tables, proves that their range is an ordinal of `L`, and extracts the collapse graph as a coded injection.
<!--zh-->
# 在 L 内部构造序型

在 `L` 中编码的良基传递关系可以在内部塌缩。本章构造塌缩表，证明其值域是 `L` 中的序数，并把塌缩图提取为编码单射。
<!--ja-->
# L の内部で順序型を構成する

`L` で符号化された整礎的で推移的な関係は、内部で崩壊できる。本章では崩壊表を構成し、その値域が `L` の順序数であることを示し、崩壊グラフを符号化された単射として取り出す。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.OrderType {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Recursion.Graph {ℓ} lem
  using () renaming ( module Graph to RecursionGraph )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate; appC; appC-adequate; prʟ; prʟ-fst; svAt; domAt )
open import L.Coding.Expressions {ℓ} using ( module PairExpression )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap ) renaming ( module Inj to DefinableInj )
open import L.Mostowski {ℓ} using ( module Mostowski )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ; isPropΣ; isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Equality of elements of the model is equality of their underlying sets, since
constructibility is a proposition.

```agda
isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))
```

"The pair `(x, y)` is a member of `F`", the shape every clause below reads.

```agda
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩
```

Section 1. The setting, and the host-level collapse.

`D` is a set of L, `R` is a set of L of pairs of members of `D`, and the relation
"`pr x y ∈ R`" is well-founded and transitive on the members of `D`. `col` is the
Mostowski collapse, taken from `L.Mostowski`, the
one recursion `Hartogs.Col` there also instantiates.

```agda
module Collapse (D R : S)
                (Rsub : (y x : S) → Holds R y x
                      → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ fst D ⟩

  isPropMem : (x : S) → isProp (Mem x)
  isPropMem x = snd (fst x ∈ fst D)
```

The members of `D`, as the small type that presents `D`. The index of a `sett`
must be small, so the relation is read through the small membership `_∈ₛ_` (as
`Hartogs` reads a Bool-valued one).

```agda
  Dom : Type ℓ
  Dom = ⟪ fst D ⟫

  ↪ : Dom → V ℓ
  ↪ = ⟪ fst D ⟫↪

  up : Dom → S
  up m = ↪ m , isL-trans {x = fst D} {y = ↪ m} (member (fst D) m) (snd D)

  up-mem : (m : Dom) → Mem (up m)
  up-mem m = member (fst D) m

  Dom≡ : {a b : Dom} → ↪ a ≡ ↪ b → a ≡ b
  Dom≡ {a} {b} e = ↪-inj {a = fst D} {m = a} {n = b} e

  toDom : (x : S) → Mem x → Dom
  toDom x mx = fst (fiber (fst D) mx)

  toDom-val : (x : S) (mx : Mem x) → ↪ (toDom x mx) ≡ fst x
  toDom-val x mx = snd (fiber (fst D) mx)
```

Sealed: `_∈ₛ_` unfolds the presentation, and an unsealed relation exhausts an 8g
heap at the first check.

```agda
  opaque
    _≺_ : Dom → Dom → Type ℓ
    a ≺ b = ⟨ pr (↪ a) (↪ b) ∈ₛ fst R ⟩

    isProp≺ : (a b : Dom) → isProp (a ≺ b)
    isProp≺ a b = snd (pr (↪ a) (↪ b) ∈ₛ fst R)

    ≺-in : (a b : Dom) → Holds R (up a) (up b) → a ≺ b
    ≺-in a b = ∈∈ₛ {a = pr (↪ a) (↪ b)} {b = fst R} .fst

    ≺-out : (a b : Dom) → a ≺ b → Holds R (up a) (up b)
    ≺-out a b = ∈∈ₛ {a = pr (↪ a) (↪ b)} {b = fst R} .snd

  module Col (wf : WellFounded _≺_)
             (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where
```

`L.Mostowski` holds the recursion; this site and `Hartogs.Col`
there are its two instances.

```agda
    open Mostowski Dom _≺_ wf ≺-trans public
      using ( module W; col; col-eq; col-in; col-out; col-ord )
```

An ordinal is constructible: it appears at the stage after itself. Sealed: a
proof of a proposition, and unsealed it is normalised at every conversion of a
`colʟ` pair (measured: one transport of the graph formula along an index
equation exceeds 100 s).

```agda
    opaque
      col-isL : (p : Dom) → ⟨ isL (col p) ⟩
      col-isL p = Lset→isL (sucV (col p)) (suc-ord (col-ord p)) (col p)
                    (ord∈Lset-suc (col p) (col-ord p))

    colʟ : Dom → S
    colʟ p = col p , col-isL p

```

<!--en-->
## The formulas
<!--zh-->
## 诸公式
<!--ja-->
## 崩壊表を記述する論理式
<!--/-->

<!--en-->
The formulas say when a set of ordered pairs correctly records the collapse below one relation element. Completeness supplies entries for every predecessor, and correctness identifies each value with the set of preceding values.
<!--zh-->
这些公式描述一个有序对集合何时正确记录某个关系元素以下的塌缩。完备性为每个前驱提供表项，而正确性把每个值识别为全部前驱值之集。
<!--ja-->
これらの論理式は、順序対の集合が一つの関係要素より下の崩壊を正しく記録する条件を述べる。完全性が各前者の項目を与え、正しさが各値をそれ以前の値全体の集合と同定する。
<!--/-->

Section 2. The object-language formulas, and how to read them.

A set `F` of pairs is CORRECT for `R` when every entry `(x, v)` of `F` is
complete (every `R`-predecessor of `x` has an entry) and its value is right
relative to `F` (`v` is exactly the set of values recorded at the
`R`-predecessors of `x`). No domain clause: a correct set may record more than a
segment, and section 3 shows every entry is the collapse.

Every formula is sealed with its two reading lemmas inside the seal, so a later
renaming or replacement never unfolds it.

Host-level readings.

```agda
Complete : S → S → S → Type (ℓ-suc ℓ)
Complete F R x = (y : S) → Holds R y x → ∥ Σ[ u ∈ S ] Holds F y u ∥₁

Src : S → S → S → S → Type (ℓ-suc ℓ)
Src F R x w = ∥ Σ[ y ∈ S ] (Holds R y x × Holds F y w) ∥₁

ValueIs : S → S → S → S → Type (ℓ-suc ℓ)
ValueIs F R x v = (w : S) → (⟨ fst w ∈ fst v ⟩ → Src F R x w)
                          × (Src F R x w → ⟨ fst w ∈ fst v ⟩)

Correct : S → S → Type (ℓ-suc ℓ)
Correct F R = (x v : S) → Holds F x v → Complete F R x × ValueIs F R x v
```

"Every `R`-predecessor `y` of `x` has an entry in `f`." Inside: `y` is 0, then
`u` is 0 and `y` is 1.

```agda
opaque
  completeAt : ∀ {n} → Fin n → S → Fin n → Formula S n
  completeAt f R x =
    ∀̇ ( appC R zero (suc x)
      ⇒̇ ∃̇ (appAt (suc (suc f)) (suc zero) zero) )

  complete-out : ∀ {n} (f : Fin n) (R : S) (x : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ completeAt f R x ⟩
               → Complete (lookup f γ) R (lookup x γ)
  complete-out f R x γ h y p = PT.map
    (λ { (u , q) → u , subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (u ∷ y ∷ γ)) q })
    (h y (subst ⟨_⟩ (sym (appC-adequate R zero (suc x) (y ∷ γ))) p))

  complete-in : ∀ {n} (f : Fin n) (R : S) (x : Fin n) (γ : S ^ n)
              → Complete (lookup f γ) R (lookup x γ)
              → ⟨ γ ⊨ completeAt f R x ⟩
  complete-in f R x γ h y p = PT.map
    (λ { (u , q) → u , subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (u ∷ y ∷ γ))) q })
    (h y (subst ⟨_⟩ (appC-adequate R zero (suc x) (y ∷ γ)) p))
```

"`w` is in `v` iff `w` is recorded in `f` at some `R`-predecessor of `x`."
Inside: `w` is 0; then `y` is 0 and `w` is 1.

```agda
opaque
  srcAt : ∀ {n} → Fin n → S → Fin n → Fin n → Formula S n
  srcAt f R x w = ∃̇ ( appC R zero (suc x) ∧̇ appAt (suc f) zero (suc w) )

  src-out : ∀ {n} (f : Fin n) (R : S) (x w : Fin n) (γ : S ^ n)
          → ⟨ γ ⊨ srcAt f R x w ⟩
          → Src (lookup f γ) R (lookup x γ) (lookup w γ)
  src-out f R x w γ = PT.map (λ { (y , (p , q)) → y
    , ( subst ⟨_⟩ (appC-adequate R zero (suc x) (y ∷ γ)) p
      , subst ⟨_⟩ (appAt-adequate (suc f) zero (suc w) (y ∷ γ)) q ) })

  src-in : ∀ {n} (f : Fin n) (R : S) (x w : Fin n) (γ : S ^ n)
         → Src (lookup f γ) R (lookup x γ) (lookup w γ)
         → ⟨ γ ⊨ srcAt f R x w ⟩
  src-in f R x w γ = PT.map (λ { (y , (p , q)) → y
    , ( subst ⟨_⟩ (sym (appC-adequate R zero (suc x) (y ∷ γ))) p
      , subst ⟨_⟩ (sym (appAt-adequate (suc f) zero (suc w) (y ∷ γ))) q ) })

opaque
  unfolding srcAt
  valueAt : ∀ {n} → Fin n → S → Fin n → Fin n → Formula S n
  valueAt f R x v =
    ∀̇ ( ((var zero ∈̇ var (suc v)) ⇒̇ srcAt (suc f) R (suc x) zero)
      ∧̇ (srcAt (suc f) R (suc x) zero ⇒̇ (var zero ∈̇ var (suc v))) )

  value-out : ∀ {n} (f : Fin n) (R : S) (x v : Fin n) (γ : S ^ n)
            → ⟨ γ ⊨ valueAt f R x v ⟩
            → ValueIs (lookup f γ) R (lookup x γ) (lookup v γ)
  value-out f R x v γ h w =
      (λ w∈ → src-out (suc f) R (suc x) zero (w ∷ γ) (h w .fst w∈))
    , (λ s → h w .snd (src-in (suc f) R (suc x) zero (w ∷ γ) s))

  value-in : ∀ {n} (f : Fin n) (R : S) (x v : Fin n) (γ : S ^ n)
           → ValueIs (lookup f γ) R (lookup x γ) (lookup v γ)
           → ⟨ γ ⊨ valueAt f R x v ⟩
  value-in f R x v γ h w =
      (λ w∈ → src-in (suc f) R (suc x) zero (w ∷ γ) (h w .fst w∈))
    , (λ s → h w .snd (src-out (suc f) R (suc x) zero (w ∷ γ) s))
```

Inside: `x` is 1 and `v` is 0.

```agda
opaque
  unfolding completeAt valueAt
  correctAt : ∀ {n} → Fin n → S → Formula S n
  correctAt f R =
    ∀̇ (∀̇ ( appAt (suc (suc f)) (suc zero) zero
          ⇒̇ ( completeAt (suc (suc f)) R (suc zero)
            ∧̇ valueAt (suc (suc f)) R (suc zero) zero ) ))

  correct-out : ∀ {n} (f : Fin n) (R : S) (γ : S ^ n)
              → ⟨ γ ⊨ correctAt f R ⟩ → Correct (lookup f γ) R
  correct-out f R γ h x v p =
    let (c , w) = h x v (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ))) p)
    in complete-out (suc (suc f)) R (suc zero) (v ∷ x ∷ γ) c
     , value-out (suc (suc f)) R (suc zero) zero (v ∷ x ∷ γ) w

  correct-in : ∀ {n} (f : Fin n) (R : S) (γ : S ^ n)
             → Correct (lookup f γ) R → ⟨ γ ⊨ correctAt f R ⟩
  correct-in f R γ h x v p =
    let (c , w) = h x v (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ)) p)
    in complete-in (suc (suc f)) R (suc zero) (v ∷ x ∷ γ) c
     , value-in (suc (suc f)) R (suc zero) zero (v ∷ x ∷ γ) w
```

The graph formula, over `(z ∷ p ∷ [])`: "`z` is recorded at `p` by some set
correct for `R`". Inside the binder, `f` is 0, `z` is 1 and `p` is 2; `R`
enters directly as a constant.

```agda
module ColFo (R : S) where

  opaque
    unfolding correctAt
    colFo : Formula S 2
    colFo = ∃̇ ( correctAt zero R
              ∧̇ appAt zero (suc (suc zero)) (suc zero) )

    colFo-out : (z p : S) → ⟨ (z ∷ p ∷ []) ⊨ colFo ⟩
              → ∥ Σ[ F ∈ S ] (Correct F R × Holds F p z) ∥₁
    colFo-out z p = PT.map (λ { (F , (hc , ha)) → F
      , ( correct-out zero R (F ∷ z ∷ p ∷ []) hc
        , subst ⟨_⟩ (appAt-adequate zero (suc (suc zero)) (suc zero)
            (F ∷ z ∷ p ∷ [])) ha ) })

    colFo-in : (z p F : S) → Correct F R → Holds F p z
             → ⟨ (z ∷ p ∷ []) ⊨ colFo ⟩
    colFo-in z p F hc hp = ∣ F
      , ( correct-in zero R (F ∷ z ∷ p ∷ []) hc
        , subst ⟨_⟩ (sym (appAt-adequate zero (suc (suc zero)) (suc zero)
            (F ∷ z ∷ p ∷ []))) hp ) ∣₁
```

The pair form of a graph is the generic construction from `L.Recursion`.
The compatibility export keeps its existing qualified name.

```agda
open import L.Recursion.Graph {ℓ} lem public using ( module PairFo )
```

<!--en-->
## Uniqueness, existence, and the tables
<!--zh-->
## 唯一性、存在性与诸表
<!--ja-->
## 一意性、存在、崩壊表
<!--/-->

<!--en-->
Well-founded induction proves that any two correct tables agree on their common domain. Replacement constructs a correct table below each element, and uniqueness lets the local tables assemble into one collapse function.
<!--zh-->
良基归纳证明任意两张正确的表在公共定义域上一致。替换在每个元素以下构造正确表，而唯一性使这些局部表装配成一个塌缩函数。
<!--ja-->
整礎帰納法により、任意の二つの正しい表は共通の定義域で一致する。置換が各要素より下に正しい表を構成し、一意性によって局所的な表を一つの崩壊関数へ組み立てられる。
<!--/-->

Section 3. Every correct set records the collapse, and one exists.

Uniqueness is one well-founded induction on the entry's index. Existence at `a`
is one replacement over `D`: the set of the pairs `(q, col q)` for `q R a`, with
the pair `(a, col a)` as the value at every other `q`, so no separation and no
union is needed. Its graph is decided by `lem`, inside `mereFunct`, where a
proposition is proved.

```agda
module Internal (D R : S)
                (Rsub : (y x : S) → Holds R y x
                      → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

  open Collapse D R Rsub public
  module CF = ColFo R using ( colFo; colFo-in; colFo-out )
  module PF = PairFo CF.colFo using ( pair-in; pair-out; pairFo )

  up-toDom : (q : S) (mq : Mem q) → up (toDom q mq) ≡ q
  up-toDom q mq = Σ≡Prop (λ v → snd (isL v)) (toDom-val q mq)
```

Transport of the graph formula along an equation of the index.

```agda
  colFo-at : (v : S) {x y : S} → x ≡ y
           → ⟨ (v ∷ x ∷ []) ⊨ CF.colFo ⟩ → ⟨ (v ∷ y ∷ []) ⊨ CF.colFo ⟩
  colFo-at v e = subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ CF.colFo ⟩) e

  module Graph (wf : WellFounded _≺_)
               (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where

    open Col wf ≺-trans public

    ≺-irrefl : (a : Dom) → a ≺ a → Empty.⊥
    ≺-irrefl = W.induction {P = λ a → a ≺ a → Empty.⊥} (λ a rec h → rec a h h)
```

UNIQUENESS: a value a correct set records at a member of `D` is the collapse
there.

```agda
    correct-val : (F : S) → Correct F R → (a : Dom) (v : S)
                → Holds F (up a) v → fst v ≡ col a
    correct-val F hc = W.induction {P = λ a → (v : S) → Holds F (up a) v → fst v ≡ col a} go
      where
      go : (a : Dom) → ((b : Dom) → b ≺ a → (v : S) → Holds F (up b) v → fst v ≡ col b)
         → (v : S) → Holds F (up a) v → fst v ≡ col a
      go a IH v hv = extensionalV {a = fst v} {b = col a} (λ w → ⇔toPath (fwd w) (bwd w))
        where
        cmp : Complete F R (up a)
        cmp = hc (up a) v hv .fst
        val : ValueIs F R (up a) v
        val = hc (up a) v hv .snd

        fwd : (w : V ℓ) → ⟨ w ∈ fst v ⟩ → ⟨ w ∈ col a ⟩
        fwd w w∈ = PT.rec (snd (w ∈ col a)) read (val wS .fst w∈)
          where
          wS : S
          wS = w , isL-trans {x = fst v} {y = w} w∈ (snd v)
          read : Σ[ y ∈ S ] (Holds R y (up a) × Holds F y wS) → ⟨ w ∈ col a ⟩
          read (y , (ry , fy)) = subst (λ t → ⟨ t ∈ col a ⟩) (sym e) (col-in a b b≺a)
            where
            my : Mem y
            my = Rsub y (up a) ry .fst
            b : Dom
            b = toDom y my
            b≺a : b ≺ a
            b≺a = ≺-in b a (subst (λ t → ⟨ pr t (↪ a) ∈ fst R ⟩) (sym (toDom-val y my)) ry)
            e : w ≡ col b
            e = IH b b≺a wS (subst (λ t → ⟨ pr t w ∈ fst F ⟩) (sym (toDom-val y my)) fy)

        bwd : (w : V ℓ) → ⟨ w ∈ col a ⟩ → ⟨ w ∈ fst v ⟩
        bwd w w∈ = PT.rec (snd (w ∈ fst v)) read (col-out a w w∈)
          where
          wS : S
          wS = w , isL-trans {x = col a} {y = w} w∈ (col-isL a)
          read : Σ[ r ∈ Dom ] ((r ≺ a) × (col r ≡ w)) → ⟨ w ∈ fst v ⟩
          read (r , (ra , e)) = PT.rec (snd (w ∈ fst v)) inner (cmp (up r) (≺-out r a ra))
            where
            inner : Σ[ u ∈ S ] Holds F (up r) u → ⟨ w ∈ fst v ⟩
            inner (u , fu) = val wS .snd
              ∣ up r , (≺-out r a ra , subst (λ t → ⟨ pr (↪ r) t ∈ fst F ⟩) (IH r ra u fu ∙ e) fu) ∣₁
```

The graph formula, read at a member of `D` given as an element.

```agda
    colFo-val : (q : S) (mq : Mem q) (v : S) → ⟨ (v ∷ q ∷ []) ⊨ CF.colFo ⟩
              → fst v ≡ col (toDom q mq)
    colFo-val q mq v h = PT.rec (setIsSet (fst v) (col (toDom q mq)))
      (λ { (F , (hc , hv)) → correct-val F hc (toDom q mq) v
             (subst (λ t → ⟨ pr t (fst v) ∈ fst F ⟩) (sym (toDom-val q mq)) hv) })
      (CF.colFo-out v q h)
```

EXISTENCE, at one `a`, from the graph formula below `a`.

```agda
    module Approx (a : Dom)
                  (IH : (b : Dom) → b ≺ a → ⟨ (colʟ b ∷ up b ∷ []) ⊨ CF.colFo ⟩) where
```

The default entry.

```agda
      ea : S
      ea = prʟ (up a) (colʟ a)

```

The graph, read: at `q R a` the pair of `q` and the value the graph formula
gives there; elsewhere the default entry.

```agda
      Body : S → S → Type (ℓ-suc ℓ)
      Body z q =
          (Holds R q (up a)
             × ∥ Σ[ v ∈ S ] ((fst z ≡ pr (fst q) (fst v)) × ⟨ (v ∷ q ∷ []) ⊨ CF.colFo ⟩) ∥₁)
        ⊎ ((Holds R q (up a) → Empty.⊥) × (fst z ≡ fst ea))
```

The relation is the constant carrier of membership, and the upper endpoint is a
literal leaf of the pair expression. Thus the graph is already a formula in the
two slots `z` and `q`.

```agda
      module PE = PairExpression

      image : PE.Expr 2
      image = PE.pair (PE.slot (suc zero)) (PE.literal (up a))

      opaque
        ψ : Formula S 2
        ψ = (PE.member image (con R) ∧̇ PF.pairFo)
          ∨̇ ((¬̇ PE.member image (con R)) ∧̇ (var zero ≐ con ea))

        ψ-out : (z q : S) → ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩ → ∥ Body z q ∥₁
        ψ-out z q = PT.map
          (λ { (inl (h1 , h2)) → inl (PE.member-out image (con R) (z ∷ q ∷ []) h1
                                         , PF.pair-out z q h2)
             ; (inr (h1 , h2)) → inr
                 ((λ k → lower (h1 (PE.member-in image (con R) (z ∷ q ∷ []) k))) , h2) })

        ψ-in : (z q : S) → Body z q → ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩
        ψ-in z q (inl (h1 , hv)) = PT.rec (snd ((z ∷ q ∷ []) ⊨ ψ))
          (λ { (v , (e , hc)) → ∣ inl (PE.member-in image (con R) (z ∷ q ∷ []) h1
                                     , PF.pair-in z q v e hc) ∣₁ }) hv
        ψ-in z q (inr (h1 , e)) =
          ∣ inr ((λ k → lift (h1 (PE.member-out image (con R) (z ∷ q ∷ []) k))) , e) ∣₁

      private
        b≺a-of : (q : S) (mq : Mem q) → Holds R q (up a) → toDom q mq ≺ a
        b≺a-of q mq h = ≺-in (toDom q mq) a
          (subst (λ t → ⟨ pr t (↪ a) ∈ fst R ⟩) (sym (toDom-val q mq)) h)

        IHq : (q : S) (mq : Mem q) → toDom q mq ≺ a
            → ⟨ (colʟ (toDom q mq) ∷ q ∷ []) ⊨ CF.colFo ⟩
        IHq q mq k = colFo-at (colʟ (toDom q mq)) (up-toDom q mq) (IH (toDom q mq) k)

        fc : (q : S) → ⟨ q ∈ˢ D ⟩ → isContr (Σ[ z ∈ S ] ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩)
        fc q mq = mereFunct ψ q (decide (lem (pr (fst q) (↪ a) ∈ fst R)))
          where
          b : Dom
          b = toDom q mq
          zb : S
          zb = prʟ q (colʟ b)
          decide : Holds R q (up a) ⊎ (Holds R q (up a) → Empty.⊥)
                 → ∥ Σ[ z ∈ S ] (⟨ (z ∷ q ∷ []) ⊨ ψ ⟩
                                × ((z' : S) → ⟨ (z' ∷ q ∷ []) ⊨ ψ ⟩ → z' ≡ z)) ∥₁
          decide (inl h) = ∣ zb
            , ( ψ-in zb q (inl (h , ∣ colʟ b , (prʟ-fst q (colʟ b) , IHq q mq (b≺a-of q mq h)) ∣₁))
              , λ z' hz' → PT.rec (isSetS z' zb)
                  (λ { (inl (_ , hv)) → PT.rec (isSetS z' zb)
                         (λ { (v , (e , hcol)) → Σ≡Prop (λ w → snd (isL w))
                                (e ∙ cong (pr (fst q)) (colFo-val q mq v hcol) ∙ sym (prʟ-fst q (colʟ b))) })
                         hv
                     ; (inr (nh , _)) → Empty.rec (nh h) })
                  (ψ-out z' q hz') ) ∣₁
          decide (inr nh) = ∣ ea
            , ( ψ-in ea q (inr (nh , refl))
              , λ z' hz' → PT.rec (isSetS z' ea)
                  (λ { (inl (h , _)) → Empty.rec (nh h)
                     ; (inr (_ , e)) → Σ≡Prop (λ w → snd (isL w)) e })
                  (ψ-out z' q hz') ) ∣₁

        module T = Of (record { dom = D ; graph = ψ ; funct = fc }) using ( table; table-in; table-out )

      Fa : S
      Fa = T.table

      Below : Dom → Type ℓ
      Below b = (b ≺ a) ⊎ (b ≡ a)

      Fa-in : (b : Dom) → Below b → Holds Fa (up b) (colʟ b)
      Fa-in b k = subst (λ w → ⟨ w ∈ fst Fa ⟩) (prʟ-fst (up b) (colʟ b))
        (T.table-in (up b) (prʟ (up b) (colʟ b)) (up-mem b) (ψ-in _ (up b) (bodyOf k)))
        where
        bodyOf : Below b → Body (prʟ (up b) (colʟ b)) (up b)
        bodyOf (inl k) = inl (≺-out b a k , ∣ colʟ b , (prʟ-fst (up b) (colʟ b) , IH b k) ∣₁)
        bodyOf (inr e) = inr
          ( (λ h → ≺-irrefl a (≺-in a a (subst (λ t → Holds R (up t) (up a)) e h)))
          , prʟ-fst (up b) (colʟ b) ∙ cong (λ t → pr (↪ t) (col t)) e ∙ sym (prʟ-fst (up a) (colʟ a)) )

      Fa-out : (y : S) → ⟨ y ∈ˢ Fa ⟩
             → ∥ Σ[ b ∈ Dom ] (Below b × (fst y ≡ pr (↪ b) (col b))) ∥₁
      Fa-out y hy = PT.rec squash₁
        (λ { (q , (mq , hψ)) → PT.rec squash₁
          (λ { (inl (h , hv)) → PT.map
                 (λ { (v , (e , hcol)) → toDom q mq
                    , (inl (b≺a-of q mq h)
                      , e ∙ cong₂ pr (sym (toDom-val q mq)) (colFo-val q mq v hcol)) })
                 hv
             ; (inr (_ , e)) → ∣ a , (inr refl , e ∙ prʟ-fst (up a) (colʟ a)) ∣₁ })
          (ψ-out y q hψ) })
        (T.table-out y hy)

      Fa-pair : (x v : S) → Holds Fa x v
              → ∥ Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v)) ∥₁
      Fa-pair x v h = PT.map step
        (Fa-out (prʟ x v) (subst (λ w → ⟨ w ∈ fst Fa ⟩) (sym (prʟ-fst x v)) h))
        where
        step : Σ[ b ∈ Dom ] (Below b × (fst (prʟ x v) ≡ pr (↪ b) (col b)))
             → Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v))
        step (b , (k , e)) = b , (k , sym (fst q) , sym (snd q))
          where
          q : (fst x ≡ ↪ b) × (fst v ≡ col b)
          q = pr-inj (sym (prʟ-fst x v) ∙ e)

      below-trans : {c b : Dom} → c ≺ b → Below b → c ≺ a
      below-trans cb (inl k) = ≺-trans cb k
      below-trans {c} cb (inr e) = subst (c ≺_) e cb

      Fa-correct : Correct Fa R
      Fa-correct x v hxv = PT.rec
        (isProp× (isPropΠ (λ _ → isPropΠ (λ _ → squash₁)))
                 (isPropΠ (λ w → isProp× (isPropΠ (λ _ → squash₁))
                                          (isPropΠ (λ _ → snd (fst w ∈ fst v))))))
        build (Fa-pair x v hxv)
        where
        build : Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v))
              → Complete Fa R x × ValueIs Fa R x v
        build (b , (k , ex , ev)) = cmp , (λ w → fwd w , bwd w)
          where
```

An `R`-predecessor of `x`, as a member below `b`.

```agda
          pred : (y : S) → Holds R y x → Σ[ c ∈ Dom ] ((c ≺ b) × (↪ c ≡ fst y))
          pred y hy = c , (≺-in c b (subst2 (λ s t → ⟨ pr s t ∈ fst R ⟩)
                              (sym (toDom-val y my)) (sym ex) hy) , toDom-val y my)
            where
            my : Mem y
            my = Rsub y x hy .fst
            c : Dom
            c = toDom y my

          cmp : Complete Fa R x
          cmp y hy = ∣ colʟ c , subst (λ t → ⟨ pr t (col c) ∈ fst Fa ⟩) ec
                                 (Fa-in c (inl (below-trans cb k))) ∣₁
            where
            c = pred y hy .fst
            cb = pred y hy .snd .fst
            ec = pred y hy .snd .snd

          fwd : (w : S) → ⟨ fst w ∈ fst v ⟩ → Src Fa R x w
          fwd w w∈ = PT.map read (col-out b (fst w) (subst (λ t → ⟨ fst w ∈ t ⟩) (sym ev) w∈))
            where
            read : Σ[ r ∈ Dom ] ((r ≺ b) × (col r ≡ fst w)) → Σ[ y ∈ S ] (Holds R y x × Holds Fa y w)
            read (r , (rb , er)) = up r
              , ( subst (λ t → ⟨ pr (↪ r) t ∈ fst R ⟩) ex (≺-out r b rb)
                , subst (λ t → ⟨ pr (↪ r) t ∈ fst Fa ⟩) er (Fa-in r (inl (below-trans rb k))) )

          bwd : (w : S) → Src Fa R x w → ⟨ fst w ∈ fst v ⟩
          bwd w = PT.rec (snd (fst w ∈ fst v)) (λ { (y , (hy , fy)) →
            PT.rec (snd (fst w ∈ fst v)) (read y hy) (Fa-pair y w fy) })
            where
            read : (y : S) → Holds R y x
                 → Σ[ c ∈ Dom ] (Below c × (↪ c ≡ fst y) × (col c ≡ fst w))
                 → ⟨ fst w ∈ fst v ⟩
            read y hy (c , (_ , ey , ew)) =
              subst2 (λ s t → ⟨ s ∈ t ⟩) ew ev (col-in b c cb)
              where
              cb : c ≺ b
              cb = ≺-in c b (subst2 (λ s t → ⟨ pr s t ∈ fst R ⟩) (sym ey) (sym ex) hy)

      approx-step : ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩
      approx-step = CF.colFo-in (colʟ a) (up a) Fa Fa-correct (Fa-in a (inr refl))
```

THE GRAPH FORMULA HOLDS OF THE COLLAPSE, everywhere on `D`.

```agda
    approx : (a : Dom) → ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩
    approx = W.induction {P = λ a → ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩}
      (λ a IH → Approx.approx-step a IH)

    approx-at : (q : S) (mq : Mem q) → ⟨ (colʟ (toDom q mq) ∷ q ∷ []) ⊨ CF.colFo ⟩
    approx-at q mq = colFo-at (colʟ (toDom q mq)) (up-toDom q mq) (approx (toDom q mq))
```

SECTION 4. THE TABLES: THE ORDER TYPE AND THE GRAPH, IN L.

```agda
    private
      otR : Recursion
      otR = record
        { dom   = D
        ; graph = CF.colFo
        ; funct = λ q mq → (colʟ (toDom q mq) , approx-at q mq)
            , λ { (v , hv) → Σ≡Prop (λ w → snd ((w ∷ q ∷ []) ⊨ CF.colFo))
                (sym (Σ≡Prop (λ w → snd (isL w)) (colFo-val q mq v hv))) } }

      module OT = Of otR using ( table; table-in; table-out )

    otL : S
    otL = OT.table

    otL-in : (b : Dom) → ⟨ col b ∈ fst otL ⟩
    otL-in b = OT.table-in (up b) (colʟ b) (up-mem b) (approx b)

    otL-out : (y : V ℓ) → ⟨ y ∈ fst otL ⟩ → ∥ Σ[ b ∈ Dom ] (col b ≡ y) ∥₁
    otL-out y hy = PT.map (λ { (q , (mq , h)) → toDom q mq , sym (colFo-val q mq yS h) })
      (OT.table-out yS hy)
      where
      yS : S
      yS = y , isL-trans {x = fst otL} {y = y} hy (snd otL)

    module CT = RecursionGraph otR using ( F; F-in; F-out; pair-out; sv; dm )

    colTable : S
    colTable = CT.F

    colTable-in : (b : Dom) → ⟨ pr (↪ b) (col b) ∈ fst colTable ⟩
    colTable-in b = subst (λ t → ⟨ pr (↪ b) t ∈ fst colTable ⟩)
      (cong col (Dom≡ (toDom-val (up b) (up-mem b)))) (CT.F-in (up b) (up-mem b))

    colTable-out : (y : S) → ⟨ y ∈ˢ colTable ⟩
                 → ∥ Σ[ b ∈ Dom ] (fst y ≡ pr (↪ b) (col b)) ∥₁
    colTable-out y hy = PT.map (λ { (q , mq , e) → toDom q mq
      , e ∙ cong (λ t → pr t (col (toDom q mq))) (sym (toDom-val q mq)) }) (CT.F-out (fst y) hy)
```

A pair in the table is read by the shared recursion graph. Its membership fibre
has a unique value.

```agda
    Fib : S → S → Type (ℓ-suc ℓ)
    Fib x v = Σ[ mx ∈ Mem x ] (fst v ≡ col (toDom x mx))

    isPropFib : (x v : S) → isProp (Fib x v)
    isPropFib x v = isPropΣ (isPropMem x) (λ mx → setIsSet (fst v) (col (toDom x mx)))

    colTable-pair : (x v : S) → Holds colTable x v → Fib x v
    colTable-pair = CT.pair-out
```

<!--en-->
## The graph as a coded injection
<!--zh-->
## 作为编码单射的图
<!--ja-->
## 符号化された単射としてのグラフ
<!--/-->

<!--en-->
The assembled table is total and single-valued on the relation's domain. When the relation is linear, distinct inputs have distinct collapse values, so the graph satisfies the internal coded-injection predicate.
<!--zh-->
装配后的表在关系的定义域上全域且单值。当关系是线性的，不同输入具有不同塌缩值，因此其图满足内部的编码单射谓词。
<!--ja-->
組み立てた表は、関係の定義域上で全域かつ一価である。関係が線形なら異なる入力は異なる崩壊値をもつので、グラフは内部の符号化された単射の述語を満たす。
<!--/-->

Section 5. The four conjuncts, in the shape `InjCode` consumes.

Single-valuedness, the domain and the range come from the table's pair reading
alone. Injectivity needs the relation to be linear: trichotomy is a hypothesis
of this section only.

```agda
module Code (D R : S)
            (Rsub : (y x : S) → Holds R y x
                  → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

  open Internal D R Rsub public

  module Conjuncts (wf : WellFounded _≺_)
                   (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where

    open Graph wf ≺-trans public

    γ : S ^ 2
    γ = colTable ∷ D ∷ []

    sv : ⟨ γ ⊨ svAt zero ⟩
    sv = CT.sv

    dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
    dm = CT.dm

    ran : (x y : S) → Holds colTable x y → ⟨ fst y ∈ fst otL ⟩
    ran x y h = subst (λ t → ⟨ t ∈ fst otL ⟩) (sym (snd (colTable-pair x y h)))
      (otL-in (toDom x (fst (colTable-pair x y h))))
```

Injectivity, under trichotomy.

```agda
    module Inj (tri : (a b : Dom) → (a ≺ b) ⊎ ((a ≡ b) ⊎ (b ≺ a))) where

      col-inj : (a b : Dom) → col a ≡ col b → a ≡ b
      col-inj a b e = go (tri a b)
        where
        go : (a ≺ b) ⊎ ((a ≡ b) ⊎ (b ≺ a)) → a ≡ b
        go (inl k)       = Empty.rec (∈-irrefl (col b)
          (subst (λ t → ⟨ t ∈ col b ⟩) e (col-in b a k)))
        go (inr (inl q)) = q
        go (inr (inr k)) = Empty.rec (∈-irrefl (col a)
          (subst (λ t → ⟨ t ∈ col a ⟩) (sym e) (col-in a b k)))

      ij : ⟨ γ ⊨ injAt zero ⟩
      ij = injAt-in zero γ (λ y x x' p q →
        let (m , e)   = colTable-pair x y p
            (m' , e') = colTable-pair x' y q
        in sym (toDom-val x m)
         ∙ cong ↪ (col-inj (toDom x m) (toDom x' m') (sym e ∙ e'))
         ∙ toDom-val x' m')

      code : InjCode colTable D otL
      code = sv , dm , ij , ran
```

A chosen preimage of each point defines the inverse collapse on any subdomain.
Only the bound on those preimages depends on the chosen codomain; the converse
graph and its uniqueness and injectivity proofs are shared.

```agda
      module Inverse (X Y : S)
        (pre : (x : S) → ⟨ fst x ∈ fst X ⟩ → Σ[ b ∈ Dom ] (col b ≡ fst x))
        (bound : (x : S) (mx : ⟨ fst x ∈ fst X ⟩) → ⟨ ↪ (pre x mx .fst) ∈ fst Y ⟩) where

        SourceMem : S → Type (ℓ-suc ℓ)
        SourceMem x = ⟨ fst x ∈ fst X ⟩

        fn : (x : S) → SourceMem x → S
        fn x mx = up (pre x mx .fst)

        opaque
          graph : Formula S 2
          graph = appC colTable zero (suc zero)

          at : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ ≡ Holds colTable y x
          at y x = cong ⟨_⟩ (appC-adequate colTable zero (suc zero) (y ∷ x ∷ []))

        only : (x : S) (mx : SourceMem x) (y : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x mx
        only x mx y hy = sym (up-toDom y my)
          ∙ cong up (col-inj (toDom y my) (pre x mx .fst) (sym (f .snd) ∙ sym (pre x mx .snd)))
          where
          f = colTable-pair y x (transport (at y x) hy)
          my = f .fst

        M : DefinableMap
        M = record
          { dom = X ; cod = Y ; fn = fn ; into = bound ; graph = graph
          ; defines = λ x mx → transport (sym (at (fn x mx) x))
              (subst (λ w → ⟨ pr (↪ (pre x mx .fst)) w ∈ fst colTable ⟩)
                (pre x mx .snd)
                (colTable-in (pre x mx .fst)))
          ; only = only }

        inj : (x : S) (mx : SourceMem x) (x' : S) (mx' : SourceMem x')
            → fst (fn x mx) ≡ fst (fn x' mx') → fst x ≡ fst x'
        inj x mx x' mx' e = sym (pre x mx .snd) ∙ cong col (Dom≡ e) ∙ pre x' mx' .snd

        injL : InjL X Y
        injL = DefinableInj.injL M inj
```
