# The below-lim residue: the shell, the story, the carried sequence

<!--en-->
The bridge's below-lim residue proves that at every limit ordinal γ the
S-level `Sset γ` lands in the constructible stage above it. This master
delivers the residue's foundation, block 1 of the build: the theorem as the
`∈-induction` closure of the STEP (T185's binding shape), the six-clause
story predicate at a generic transitive carrier, and the carried-sequence
machinery at a generic limit index. The carrier, the graph layer, the pair
family below the limit, and the STEP are module parameters; the instantiation
happens at the consumer's carrier, and the content block 2 owes is stated in
the build report.
<!--zh-->
桥的 below-lim 残差证明：在每个极限序数 γ 处，S 层 `Sset γ` 落在其上方的可构造阶段里。本主章交付该残差的地基，即本次构建的第一块：以 STEP 之 `∈-induction` 闭包陈述的定理 (T185 的约束形状)、通用传递载体处的六子句故事谓词、以及通用极限索引处的载运序列机制。载体、图层、极限之下的对族与 STEP 都是模块参数；实例化发生在消费方的载体处，第二块所欠的内容写在构建报告里。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import L.Constructible using ( isTransV )

module L.Rud.BelowLim {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (C : V ℓ) (Ctr : isTransV C) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl; ∈-induction )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Ordinal {ℓ} using ( ∅-ord; numeral-mem; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord; isLimit-not-zero )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( +ω; +ω-limit; +ω-in; +ω-out; +ω-ord; sucIter )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import L.Rud.Step {ℓ} lem ∅ using
  ( Op16; Fof; Sset; Sset-suc; Sset-zero; Sset-mono; step; step-in-self
  ; limit-succ-mem )
open import L.Rud.Ops {ℓ} using ( F0; F5; F0-spec; F5-spec )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( BelowLim; Sset-union-limit; Sset-union-in )
open import L.TowerKit {ℓ} lem ∅ using ( Lpair )
import L.Rud.StepStory {ℓ} lem ∅ C Ctr as StepStory
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.FinData.Base using ( Fin )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Functions.Logic as Logic
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ∈∈ₛ; _≡ₕ_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module K = LevelKit C Ctr
open K public

-- The first limit ordinal: +ω ∅ is the first limit, ω.  The chain and the
-- walls below use it; it is delivered content (OrdBlocks), not carrier
-- content, so it stays concrete at every scale of the induction.
a₀ : S
a₀ = +ω ∅

a₀-ord : IsOrd a₀
a₀-ord = +ω-ord ∅ ∅-ord

a₀-lim : ⟨ isLimit a₀ ⟩
a₀-lim = +ω-limit ∅ ∅-ord
```

<!--en-->
## The shell
<!--zh-->
## 外壳
<!--/-->

<!--en-->
The theorem is stated in T185's induction shape, which is binding. It is the
`∈-induction` closure of the STEP, so at a general limit γ the fact at every
smaller limit is the induction hypothesis. The STEP is a module parameter;
its content, the carried-sequence construction that lands `Sset γ`, is
block 2's. Stating the theorem per-carrier would re-create the 269-350-line
term the probe removed.
<!--zh-->
定理以 T185 的归纳形状陈述，该形状具有约束力。它就是 STEP 的 `∈-induction` 闭包，故在一般极限 γ 处，每个更小极限处的事实都是归纳假设。STEP 是模块参数；其内容，即让 `Sset γ` 落地的载运序列构造，属于第二块。逐载体陈述定理会重新造出探针已移除的 269 至 350 行术语。
<!--/-->

```agda
module Assembly
  (stepHyp : (γ : S) → ⟨ isLimit γ ⟩
           → ((β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩)
           → ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩)
  where

  below-lim : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩
  below-lim = ∈-induction {P = P} indStep
    where
    P : S → Type (ℓ-suc ℓ)
    P γ = ⟨ isLimit γ ⟩ → ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩

    -- The induction step, named indStep so the rud step of the story stays
    -- the imported `step` in scope here.
    indStep : (γ : S) → ((β : S) → β ∈ᵗ γ → P β) → P γ
    indStep γ IH limγ = stepHyp γ limγ ih
      where
      ih : (β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩
      ih β β∈γ limβ = IH β β∈γ limβ

      -- The top pair at a smaller limit: the first component by the
      -- ordinal step, the second by the induction hypothesis.  This is
      -- T182's wall discharged from the frame.
      topPair : (β : S) → ⟨ isLimit β ⟩ → β ∈ᵗ γ
              → ⟨ F0 β (Sset β) ∈ˢ Lset (sucV (sucV β)) ⟩
      topPair β limβ β∈γ = Lpair (sucV β) β (Sset β)
        (ord∈Lset-suc β (isLimit-ord β limβ)) (IH β β∈γ limβ)

  -- The bridge's residue, derived from the induction shape: at a limit γ,
  -- a smaller limit β's S-level lands in Lset γ by the theorem at β plus
  -- the successor closure and monotonicity.  This supplies the bridge's
  -- Reduce parameter (src/L/Rud/Bridge.lagda.md:1040).
  below-lim-old : BelowLim
  below-lim-old γ limγ β ordβ limβ β∈γ =
    Lset-mono {α = γ} {β = sucV β} (limit-succ-mem γ β limγ β∈γ)
      (below-lim β limβ)

  -- The first two limits, and the walls the old probe priced: under the
  -- induction shape each wall is an application of the theorem.
  wall₁ : ⟨ Sset a₀ ∈ˢ Lset (sucV a₀) ⟩
  wall₁ = below-lim a₀ a₀-lim

  β₀ : S
  β₀ = +ω a₀

  β₀-ord : IsOrd β₀
  β₀-ord = +ω-ord a₀ a₀-ord

  β₀-lim : ⟨ isLimit β₀ ⟩
  β₀-lim = +ω-limit a₀ a₀-ord

  wall₂ : ⟨ Sset β₀ ∈ˢ Lset (sucV β₀) ⟩
  wall₂ = below-lim β₀ β₀-lim

  topPair₂ : ⟨ F0 β₀ (Sset β₀) ∈ˢ Lset (sucV (sucV β₀)) ⟩
  topPair₂ = Lpair (sucV β₀) β₀ (Sset β₀) β₀∈Lsucβ₀ wall₂
    where
    β₀∈Lsucβ₀ : ⟨ β₀ ∈ˢ Lset (sucV β₀) ⟩
    β₀∈Lsucβ₀ = ord∈Lset-suc β₀ β₀-ord
```

<!--en-->
## The story predicate at the generic carrier
<!--zh-->
## 通用载体处的故事谓词
<!--/-->

<!--en-->
The story is the conjunction of six clauses, written once at the generic
carrier. The kit supplies pairhood, single-valuedness, the zero clause and
the exact domain. The Clause telescope of `L.Rud.StepStory` supplies the
one-way successor clause, and the sixth clause is the limit clause T128
gated EXPRESSIBLE: the value at a limit index is the pointwise union of the
values below. The clause reads at the meta level, so the object-language
expressibility gate is already delivered; the master states the clause and
consumes it.
<!--zh-->
故事是六条子句的合取，在通用载体处只写一次。套件供应成对性、单值性、零子句与精确定义域。`L.Rud.StepStory` 的 Clause 望远镜供应单向后继子句，第六条是 T128 已门控为可表达的极限子句：极限索引处的值是其下诸值的逐点并。子句在元层读出，故对象语言的表达性门已经交付；本主章陈述并消费该子句。
<!--/-->

```agda
-- The carried-sequence content lives here: the story predicate, the chain,
-- and the segment machinery.  The module telescope is exactly the Clause
-- telescope of L.Rud.StepStory (the graph layer plus the step closure), so
-- the consumer wires the delivered graph layer of L.Rud.StepGraph into it.
module Story
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

  module Cl = StepStory.Clause stepSub graphOf graph-out graph-in bigOr
    bigOr-in bigOr-out eqFrame eqFrame-ok

  -- The one-way successor clause, from the Clause telescope.
  succClause : S → Type (ℓ-suc ℓ)
  succClause = Cl.succClause

  -- The sixth clause, the limit clause: the value at a limit index is the
  -- pointwise union of the values below.  T128's meta statement, ported;
  -- nothing in it names a concrete carrier (src/ProbeT128.agda:143-147).
  limitClause : S → Type (ℓ-suc ℓ)
  limitClause f = (a b : S) → ⟨ isLimit a ⟩ → ⟨ pr a b ∈ˢ f ⟩
    → (z : S) → ⟨ z ∈ˢ b ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁

  -- The story predicate: the kit's four shared clauses, the one-way
  -- successor clause, and the sixth limit clause.
  story : S → Type (ℓ-suc ℓ)
  story f = K.pairhood f × K.singleValued f × K.zeroClause f × K.exactDom f
          × succClause f × limitClause f

  _⊆_ : S → S → Type (ℓ-suc ℓ)
  u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

  ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
  ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

  -- The numeral chain: the finite iterates of successor from ∅ are the
  -- numerals, so a₀ = +ω ∅ is ω and every member of a₀ is a numeral.
  nk : ℕ → S
  nk k = # k

  sucIter-∅≡# : (n : ℕ) → sucIter n ∅ ≡ # n
  sucIter-∅≡# zero = refl
  sucIter-∅≡# (suc n) = cong sucV (sucIter-∅≡# n)

  a₀≡ω : a₀ ≡ ω
  a₀≡ω = ext-⊆ {a₀} {ω} a₀⊆ω ω⊆a₀
    where
    a₀⊆ω : a₀ ⊆ ω
    a₀⊆ω x x∈a₀ = PT.rec (snd (x ∈ˢ ω)) go (+ω-out ∅ x x∈a₀)
      where
      go : Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) ∅ ⟩ → ⟨ x ∈ˢ ω ⟩
      go (n , h) = numeral-mem (suc n) x
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (sucIter-∅≡# (suc n)) h)
    ω⊆a₀ : ω ⊆ a₀
    ω⊆a₀ x x∈ω = PT.rec (snd (x ∈ˢ a₀)) go x∈ω
      where
      go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower m) ≡ x) → ⟨ x ∈ˢ a₀ ⟩
      go (m , q) = subst (λ w → ⟨ w ∈ˢ a₀ ⟩) q
        (+ω-in ∅ (nk (lower m)) (lower m)
          (subst (λ w → ⟨ nk (lower m) ∈ˢ w ⟩)
            (sym (sucIter-∅≡# (suc (lower m)))) (self∈sucV (nk (lower m)))))

  -- The chain at the first limit: a six-clause story's value at a numeral
  -- is forced to the S-level, by the zero clause, single-valuedness and
  -- the successor clause.
  chainValue : (f : S) → story f → (a x : S) → ⟨ a ∈ˢ ω ⟩
             → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Sset a
  chainValue f st a x a∈ω ax∈f = PT.rec (setIsSet x (Sset a)) go a∈ω
    where
    h4 : K.exactDom f
    h4 = st .snd .snd .snd .fst
    chainNum : (n : ℕ) (x : S) → ⟨ pr (# n) x ∈ˢ f ⟩ → x ≡ Sset (# n)
    chainNum zero x px = x≡∅ ∙ sym Sset-zero
      where
      x≡∅ : x ≡ ∅
      x≡∅ = PT.rec (setIsSet x ∅) zStep (st .snd .snd .fst)
        where
        zStep : Σ[ a ∈ S ]
                 ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ f ⟩ ) → x ≡ ∅
        zStep (a , (emp , aa∈f)) = st .snd .fst ∅ x ∅ px pr∅∅
          where
          a≡∅ : a ≡ ∅
          a≡∅ = extensionalV (λ z → ⇔toPath
            (λ z∈a → Empty.rec (emp z z∈a))
            (λ z∈∅ → Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅))))
          pr∅∅ : ⟨ pr ∅ ∅ ∈ˢ f ⟩
          pr∅∅ = subst (λ w → ⟨ pr w w ∈ˢ f ⟩) a≡∅ aa∈f
    chainNum (suc n) x px = PT.rec (setIsSet x (Sset (# (suc n)))) δStep h4
      where
      δStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ C ⟩ × IsOrd δ
               × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
               × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
            → x ≡ Sset (# (suc n))
      δStep (δ , (δ∈u , ordδ , in-dir , out-dir)) = x≡stepS#n ∙ step≡Sset
        where
        suc∈δ : ⟨ sucV (# n) ∈ˢ δ ⟩
        suc∈δ = out-dir (sucV (# n)) ∣ x , px ∣₁
        n∈δ : ⟨ nk n ∈ˢ δ ⟩
        n∈δ = ordδ .fst {x = sucV (# n)} {y = # n} (self∈sucV (# n)) suc∈δ
        x≡stepS#n : x ≡ step (Sset (# n))
        x≡stepS#n = PT.rec (setIsSet x (step (Sset (# n)))) cStep
          (in-dir (# n) n∈δ)
          where
          cStep : Σ[ c ∈ S ] ⟨ pr (# n) c ∈ˢ f ⟩ → x ≡ step (Sset (# n))
          cStep (c , prnc) = st .snd .snd .snd .snd .fst
            (# n) (Sset (# n)) x prn px
            where
            prn : ⟨ pr (# n) (Sset (# n)) ∈ˢ f ⟩
            prn = subst (λ w → ⟨ pr (# n) w ∈ˢ f ⟩) (chainNum n c prnc) prnc
        step≡Sset : step (Sset (# n)) ≡ Sset (# (suc n))
        step≡Sset = sym (Sset-suc (# n))
    go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower m) ≡ a) → x ≡ Sset a
    go (m , q) = subst (λ w → x ≡ Sset w) q
      (chainNum (lower m) x ax∈f')
      where
      ax∈f' : ⟨ pr (# (lower m)) x ∈ˢ f ⟩
      ax∈f' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) (sym q) ax∈f

  -- The chain step at the first limit index: the value at a₀ is forced to
  -- Sset a₀.  The limit clause reads the value as the pointwise union of
  -- the values below; the values below are forced to Sset ξ by the
  -- numeral chain; the tower's own limit union identifies Sset a₀ with
  -- that union.
  chainLimit : (f : S) → story f → (x : S) → ⟨ pr a₀ x ∈ˢ f ⟩ → x ≡ Sset a₀
  chainLimit f st x ax∈f = ext-⊆ {x} {Sset a₀} x⊆S Sa₀⊆x
    where
    h4 : K.exactDom f
    h4 = st .snd .snd .snd .fst
    lc : (a b : S) → ⟨ isLimit a ⟩ → ⟨ pr a b ∈ˢ f ⟩
       → (z : S) → ⟨ z ∈ˢ b ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
    lc = st .snd .snd .snd .snd .snd
    x⊆S : x ⊆ Sset a₀
    x⊆S z z∈x = PT.rec (snd (z ∈ˢ Sset a₀)) step₁
      (lc a₀ x a₀-lim ax∈f z .fst z∈x)
      where
      step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
            → ⟨ z ∈ˢ Sset a₀ ⟩
      step₁ (ξ , (ξ∈a₀ , rest)) = PT.rec (snd (z ∈ˢ Sset a₀)) step₂ rest
        where
        ξ∈ω : ⟨ ξ ∈ˢ ω ⟩
        ξ∈ω = subst (λ w → ⟨ ξ ∈ˢ w ⟩) a₀≡ω ξ∈a₀
        step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩)
              → ⟨ z ∈ˢ Sset a₀ ⟩
        step₂ (w , (pw∈f , z∈w)) =
          Sset-mono {α = a₀} {β = ξ} ξ∈a₀ z
            (subst (λ w' → ⟨ z ∈ˢ w' ⟩)
              (chainValue f st ξ w ξ∈ω pw∈f) z∈w)
    Sa₀⊆x : Sset a₀ ⊆ x
    Sa₀⊆x z z∈Sa₀ = PT.rec (snd (z ∈ˢ x)) step₁
      (Sset-union-limit a₀ a₀-lim z z∈Sa₀)
      where
      step₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ a₀ ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
            → ⟨ z ∈ˢ x ⟩
      step₁ (δ , (δ∈a₀ , z∈Sδ')) = PT.rec (snd (z ∈ˢ x)) step₂ h4
        where
        δ'∈a₀ : ⟨ sucV δ ∈ˢ a₀ ⟩
        δ'∈a₀ = limit-succ-mem a₀ δ a₀-lim δ∈a₀
        step₂ : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ C ⟩ × IsOrd δ₀
                 × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
                 × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ₀ ⟩) )
              → ⟨ z ∈ˢ x ⟩
        step₂ (δ₀ , (δ₀∈C , ordδ₀ , in-dir , out-dir)) =
          PT.rec (snd (z ∈ˢ x)) step₃ (in-dir (sucV δ) δ'∈δ₀)
          where
          a₀∈δ₀ : ⟨ a₀ ∈ˢ δ₀ ⟩
          a₀∈δ₀ = out-dir a₀ ∣ x , ax∈f ∣₁
          δ'∈δ₀ : ⟨ sucV δ ∈ˢ δ₀ ⟩
          δ'∈δ₀ = ordδ₀ .fst {x = a₀} {y = sucV δ} δ'∈a₀ a₀∈δ₀
          step₃ : Σ[ b ∈ S ] ⟨ pr (sucV δ) b ∈ˢ f ⟩ → ⟨ z ∈ˢ x ⟩
          step₃ (b , pδ'b) = lc a₀ x a₀-lim ax∈f z .snd
            ∣ sucV δ , ( δ'∈a₀ , ∣ Sset (sucV δ) , ( pδ'b' , z∈Sδ' ) ∣₁ ) ∣₁
            where
            b≡Sδ' : b ≡ Sset (sucV δ)
            b≡Sδ' = chainValue f st (sucV δ) b
              (subst (λ w → ⟨ sucV δ ∈ˢ w ⟩) a₀≡ω δ'∈a₀) pδ'b
            pδ'b' : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ f ⟩
            pδ'b' = subst (λ w → ⟨ pr (sucV δ) w ∈ˢ f ⟩) b≡Sδ' pδ'b
```

<!--en-->
## The carried sequence at a limit index
<!--zh-->
## 极限索引处的载运序列
<!--/-->

<!--en-->
The carried sequence at a limit index is the segment: the family of pairs
below the limit plus the top pair `pr δ₀ (Sset δ₀)`. The pair family `P` and
its two-way decode are parameters; at the first limit the probe builds them
from the story at `Lset ω`, and at a general limit the STEP builds them from
the below facts, so the construction is block 2's content and the machinery
here is carrier-generic. The machinery proves the segment's membership, its
exact domain, its limit clause, and the four clauses the story needs.
<!--zh-->
极限索引处的载运序列就是段：极限之下的对族加上顶对 `pr δ₀ (Sset δ₀)`。对族 `P` 及其双向解码是参数；在第一个极限处，探针从 `Lset ω` 处的故事建出它们，而在一般极限处，STEP 从下方诸事实建出它们，故该构造属第二块，此处的机制对载体泛型。该机制证明段的隶属、其精确定义域、其极限子句、以及故事所需的四条子句。
<!--/-->

```agda
  module Segment
    (δ₀ : S) (limδ₀ : ⟨ isLimit δ₀ ⟩)
    (P : S)
    (P∈ : (p : S) → ⟨ p ∈ˢ P ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩
            × (p ≡ pr ξ (Sset ξ))) ∥₁)
    (sucδ₀∈C : ⟨ sucV δ₀ ∈ˢ C ⟩)
    where

    δ₀-ord : IsOrd δ₀
    δ₀-ord = isLimit-ord δ₀ limδ₀

    -- The empty set lies below every limit: by ordinal trichotomy, with
    -- the nonempty half of the limit predicate.
    ∅∈δ₀ : ⟨ ∅ ∈ˢ δ₀ ⟩
    ∅∈δ₀ = go (ord-tri ∅ ∅-ord δ₀ δ₀-ord)
      where
      go : ⟨ ∅ ∈ˢ δ₀ ⟩ ⊎ ((∅ ≡ δ₀) ⊎ ⟨ δ₀ ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ δ₀ ⟩
      go (inl h) = h
      go (inr (inl e)) = Empty.rec (isLimit-not-zero δ₀ limδ₀ (sym e))
      go (inr (inr h)) = Empty.rec (∅-empty δ₀ (∈∈ₛ {a = δ₀} {b = ∅} .fst h))

    -- The top pair: the value at the limit index itself.
    T : S
    T = pr δ₀ (Sset δ₀)

    -- The segment: P ∪ {T}, as the rud union of the two-element family.
    seg : S
    seg = F5 (F0 P (F0 T T)) T

    segRHS : S → hProp (ℓ-suc ℓ)
    segRHS x = Logic._⊔_ (x ∈ˢ P) ((x ≡ T) , setIsSet x T)

    -- The segment's membership is the disjunction, by the delivered F0/F5
    -- specifications.
    seg∈ : (x : S) → ⟨ x ∈ˢ seg ⟩ ⟷ ⟨ segRHS x ⟩
    seg∈ x = (out , bwd)
      where
      out : ⟨ x ∈ˢ seg ⟩ → ⟨ segRHS x ⟩
      out h = PT.rec (snd (segRHS x)) o₂ (F5-spec (F0 P (F0 T T)) T x .fst h)
        where
        o₂ : Σ[ v ∈ S ] ⟨ v ∈ˢ F0 P (F0 T T) ⊓ x ∈ˢ v ⟩ → ⟨ segRHS x ⟩
        o₂ (v , (v∈F0 , x∈v)) = PT.rec (snd (segRHS x)) o₃
          (F0-spec P (F0 T T) v .fst v∈F0)
          where
          o₃ : ⟨ v ≡ₕ P ⟩ ⊎ ⟨ v ≡ₕ F0 T T ⟩ → ⟨ segRHS x ⟩
          o₃ (inl v≡P) = ∣ inl (subst (λ w → ⟨ x ∈ˢ w ⟩) v≡P x∈v) ∣₁
          o₃ (inr v≡T) = ∣ inr (PT.rec (setIsSet x T) o₅
            (F0-spec T T x .fst (subst (λ w → ⟨ x ∈ˢ w ⟩) v≡T x∈v))) ∣₁
            where
            o₅ : ⟨ x ≡ₕ T ⟩ ⊎ ⟨ x ≡ₕ T ⟩ → x ≡ T
            o₅ (inl e) = e
            o₅ (inr e) = e
      bwd : ⟨ segRHS x ⟩ → ⟨ x ∈ˢ seg ⟩
      bwd h = PT.rec (snd (x ∈ˢ seg)) b' h
        where
        b' : ⟨ x ∈ˢ P ⟩ ⊎ (x ≡ T) → ⟨ x ∈ˢ seg ⟩
        b' (inl x∈P) = F5-spec (F0 P (F0 T T)) T x .snd
          ∣ P
            , ( F0-spec P (F0 T T) P .snd
                ∣ inl refl ∣₁
              , x∈P ) ∣₁
        b' (inr x≡T) = F5-spec (F0 P (F0 T T)) T x .snd
          ∣ F0 T T
            , ( F0-spec P (F0 T T) (F0 T T) .snd
                ∣ inr refl ∣₁
              , F0-spec T T x .snd ∣ inl x≡T ∣₁ ) ∣₁

    -- The pair family's two directions, read from the parameter.
    P∈-in : (ξ : S) → ⟨ ξ ∈ˢ δ₀ ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ P ⟩
    P∈-in ξ ξ∈δ₀ = P∈ (pr ξ (Sset ξ)) .snd ∣ ξ , (ξ∈δ₀ , refl) ∣₁

    P∈-out : (p : S) → ⟨ p ∈ˢ P ⟩
           → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
    P∈-out p p∈ = P∈ p .fst p∈

    -- The value at the limit index is in the segment, by the right
    -- disjunct; the values below are in the segment, by the left disjunct.
    T∈seg : ⟨ T ∈ˢ seg ⟩
    T∈seg = seg∈ T .snd ∣ inr refl ∣₁

    prξSξ∈seg : (ξ : S) → ⟨ ξ ∈ˢ δ₀ ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ seg ⟩
    prξSξ∈seg ξ ξ∈δ₀ = seg∈ (pr ξ (Sset ξ)) .snd ∣ inl (P∈-in ξ ξ∈δ₀) ∣₁

    -- The exact domain of the segment: sucV δ₀.  Every member of the
    -- domain has a pair (the values below via P, the top via T), and every
    -- pair's first component lies in the domain.  The in-direction's two
    -- branches are named functions with written types (I-5); the T138
    -- shape with two inline lambdas walls past 7.5 minutes.
    segDom-in-below : (a : S) → ⟨ a ∈ˢ δ₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg ⟩ ∥₁
    segDom-in-below a a∈δ₀ = ∣ Sset a , prξSξ∈seg a a∈δ₀ ∣₁

    segDom-in-top : (a : S) → a ≡ δ₀ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg ⟩ ∥₁
    segDom-in-top a a≡δ₀ =
      ∣ Sset δ₀ , subst (λ w → ⟨ pr w (Sset δ₀) ∈ˢ seg ⟩) (sym a≡δ₀) T∈seg ∣₁

    segDom-in : (a : S) → ⟨ a ∈ˢ sucV δ₀ ⟩
             → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg ⟩ ∥₁
    segDom-in a a∈suc = ∈sucV-elim {A = δ₀} {x = a} squash₁ a∈suc
      (segDom-in-below a) (segDom-in-top a)

    segDom-out : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg ⟩ ∥₁ → ⟨ a ∈ˢ sucV δ₀ ⟩
    segDom-out a = PT.rec (snd (a ∈ˢ sucV δ₀)) go
      where
      go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg ⟩ → ⟨ a ∈ˢ sucV δ₀ ⟩
      go (b , pr∈) = PT.rec (snd (a ∈ˢ sucV δ₀)) d (seg∈ (pr a b) .fst pr∈)
        where
        d : ⟨ pr a b ∈ˢ P ⟩ ⊎ (pr a b ≡ T) → ⟨ a ∈ˢ sucV δ₀ ⟩
        d (inl p∈P) = PT.rec (snd (a ∈ˢ sucV δ₀)) pgo (P∈-out (pr a b) p∈P)
          where
          pgo : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩ × (pr a b ≡ pr ξ (Sset ξ)))
              → ⟨ a ∈ˢ sucV δ₀ ⟩
          pgo (ξ , (ξ∈δ₀ , q)) =
            subst (λ w → ⟨ w ∈ˢ sucV δ₀ ⟩) (sym (pr-inj q .fst))
              (∈sucV-inl {A = δ₀} {x = ξ} ξ∈δ₀)
        d (inr q) = subst (λ w → ⟨ w ∈ˢ sucV δ₀ ⟩) (pr-inj (sym q) .fst)
          (self∈sucV δ₀)

    segDom₀ : K.exactDom seg
    segDom₀ = ∣ sucV δ₀ , ( sucδ₀∈C , suc-ord δ₀-ord , segDom-in , segDom-out ) ∣₁

    -- The limit clause on the segment: the value at the limit index,
    -- Sset δ₀, is the union of the values below, read through the
    -- segment's membership.
    segLimit₀ : (z : S) → ⟨ z ∈ˢ Sset δ₀ ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
    segLimit₀ z = (fwd , bwd)
      where
      fwd : ⟨ z ∈ˢ Sset δ₀ ⟩
          → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩
               × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
      fwd z∈S = PT.rec squash₁ s₁ (Sset-union-limit δ₀ limδ₀ z z∈S)
        where
        s₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ δ₀ ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
           → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩
                × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
        s₁ (δ , (δ∈δ₀ , z∈Sδ')) = ∣ sucV δ , (δ'∈δ₀ , ∣ Sset (sucV δ) , (pr∈ , z∈Sδ') ∣₁) ∣₁
          where
          δ'∈δ₀ : ⟨ sucV δ ∈ˢ δ₀ ⟩
          δ'∈δ₀ = limit-succ-mem δ₀ δ limδ₀ δ∈δ₀
          pr∈ : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ seg ⟩
          pr∈ = prξSξ∈seg (sucV δ) δ'∈δ₀
      bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩
               × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
          → ⟨ z ∈ˢ Sset δ₀ ⟩
      bwd h = PT.rec (snd (z ∈ˢ Sset δ₀)) s₁ h
        where
        s₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
            → ⟨ z ∈ˢ Sset δ₀ ⟩
        s₁ (ξ , (ξ∈δ₀ , rest)) = PT.rec (snd (z ∈ˢ Sset δ₀)) s₂ rest
          where
          s₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg ⟩ × ⟨ z ∈ˢ w ⟩) → ⟨ z ∈ˢ Sset δ₀ ⟩
          s₂ (w , (pr∈ , z∈w)) = PT.rec (snd (z ∈ˢ Sset δ₀)) d
            (seg∈ (pr ξ w) .fst pr∈)
            where
            d : ⟨ pr ξ w ∈ˢ P ⟩ ⊎ (pr ξ w ≡ T) → ⟨ z ∈ˢ Sset δ₀ ⟩
            d (inl p∈P) = PT.rec (snd (z ∈ˢ Sset δ₀)) pgo (P∈-out (pr ξ w) p∈P)
              where
              pgo : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ δ₀ ⟩ × (pr ξ w ≡ pr ξ' (Sset ξ')))
                  → ⟨ z ∈ˢ Sset δ₀ ⟩
              pgo (ξ' , (ξ'∈δ₀ , q)) = Sset-mono {α = δ₀} {β = ξ} ξ∈δ₀ z z∈Sξ
                where
                w≡Sξ : w ≡ Sset ξ
                w≡Sξ = subst (λ t → w ≡ Sset t) (sym (pr-inj q .fst))
                  (pr-inj q .snd)
                z∈Sξ : ⟨ z ∈ˢ Sset ξ ⟩
                z∈Sξ = subst (λ t → ⟨ z ∈ˢ t ⟩) (w≡Sξ) z∈w
            d (inr q) = Empty.rec {A = ⟨ z ∈ˢ Sset δ₀ ⟩}
              (∈-irrefl δ₀ (subst (λ t → ⟨ t ∈ˢ δ₀ ⟩)
                (sym (pr-inj (sym q) .fst)) ξ∈δ₀))

    -- Exercises at a member of the top value: the limit clause reads both
    -- ways, and the exact domain reads at the top index.
    top∈Ssetδ₀ : ⟨ Sset ∅ ∈ˢ Sset δ₀ ⟩
    top∈Ssetδ₀ = Sset-union-in δ₀ limδ₀ ∅ (Sset ∅) ∅∈δ₀
      (subst (λ w → ⟨ Sset ∅ ∈ˢ w ⟩) (sym (Sset-suc ∅)) (step-in-self (Sset ∅)))

    lim-read : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg ⟩ × ⟨ Sset ∅ ∈ˢ w ⟩) ∥₁) ∥₁
    lim-read = segLimit₀ (Sset ∅) .fst top∈Ssetδ₀

    lim-read-back : ⟨ Sset ∅ ∈ˢ Sset δ₀ ⟩
    lim-read-back = segLimit₀ (Sset ∅) .snd lim-read

    dom-read : ∥ Σ[ b ∈ S ] ⟨ pr δ₀ b ∈ˢ seg ⟩ ∥₁
    dom-read = segDom-in δ₀ (self∈sucV δ₀)

    -- Pairhood: every member of the segment is a Kuratowski pair.
    segPairhood : K.pairhood seg
    segPairhood z z∈ = PT.rec squash₁ go (seg∈ z .fst z∈)
      where
      go : ⟨ z ∈ˢ P ⟩ ⊎ (z ≡ T) → isPair z
      go (inl z∈P) = PT.rec squash₁ pgo (P∈-out z z∈P)
        where
        pgo : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩ × (z ≡ pr ξ (Sset ξ))) → isPair z
        pgo (ξ , (ξ∈δ₀ , q)) = ∣ ξ , (Sset ξ , q) ∣₁
      go (inr q) = ∣ δ₀ , (Sset δ₀ , q) ∣₁

    -- Single-valuedness: two pairs in the segment with the same first
    -- component agree on the second.
    segSingleValued : K.singleValued seg
    segSingleValued a b c ab∈ ac∈ = PT.rec (setIsSet b c) go₁ (seg∈ (pr a b) .fst ab∈)
      where
      go₁ : ⟨ pr a b ∈ˢ P ⟩ ⊎ (pr a b ≡ T) → b ≡ c
      go₁ (inl p₁) = PT.rec (setIsSet b c) p₁go (P∈-out (pr a b) p₁)
        where
        p₁go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩ × (pr a b ≡ pr ξ (Sset ξ))) → b ≡ c
        p₁go (ξ , (ξ∈δ₀ , q₁)) = PT.rec (setIsSet b c) go₂ (seg∈ (pr a c) .fst ac∈)
          where
          a≡ξ : a ≡ ξ
          a≡ξ = pr-inj q₁ .fst
          b≡Sξ : b ≡ Sset ξ
          b≡Sξ = pr-inj q₁ .snd
          go₂ : ⟨ pr a c ∈ˢ P ⟩ ⊎ (pr a c ≡ T) → b ≡ c
          go₂ (inl p₂) = PT.rec (setIsSet b c) p₂go (P∈-out (pr a c) p₂)
            where
            p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ δ₀ ⟩ × (pr a c ≡ pr ξ' (Sset ξ'))) → b ≡ c
            p₂go (ξ' , (ξ'∈δ₀ , q₂)) =
              b≡Sξ ∙ cong Sset ξ≡ξ' ∙ sym (pr-inj q₂ .snd)
              where
              ξ≡ξ' : ξ ≡ ξ'
              ξ≡ξ' = sym a≡ξ ∙ pr-inj q₂ .fst
          go₂ (inr q₂) = Empty.rec (∈-irrefl δ₀ a₀∈a₀)
            where
            a₀∈a₀ : ⟨ δ₀ ∈ˢ δ₀ ⟩
            a₀∈a₀ = subst (λ w → ⟨ w ∈ˢ δ₀ ⟩) ξ≡δ₀ ξ∈δ₀
              where
              ξ≡δ₀ : ξ ≡ δ₀
              ξ≡δ₀ = sym a≡ξ ∙ pr-inj q₂ .fst
      go₁ (inr q₁) = PT.rec (setIsSet b c) go₃ (seg∈ (pr a c) .fst ac∈)
        where
        a≡δ₀ : a ≡ δ₀
        a≡δ₀ = pr-inj q₁ .fst
        b≡Sδ₀ : b ≡ Sset δ₀
        b≡Sδ₀ = pr-inj q₁ .snd
        go₃ : ⟨ pr a c ∈ˢ P ⟩ ⊎ (pr a c ≡ T) → b ≡ c
        go₃ (inl p₂) = PT.rec (setIsSet b c) p₂go (P∈-out (pr a c) p₂)
          where
          p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ δ₀ ⟩ × (pr a c ≡ pr ξ' (Sset ξ'))) → b ≡ c
          p₂go (ξ' , (ξ'∈δ₀ , q₂)) = Empty.rec (∈-irrefl δ₀ a₀∈a₀)
            where
            a₀∈a₀ : ⟨ δ₀ ∈ˢ δ₀ ⟩
            a₀∈a₀ = subst (λ w → ⟨ w ∈ˢ δ₀ ⟩) (sym a₀≡ξ') ξ'∈δ₀
              where
              a₀≡ξ' : δ₀ ≡ ξ'
              a₀≡ξ' = sym a≡δ₀ ∙ pr-inj q₂ .fst
        go₃ (inr q₂) = b≡Sδ₀ ∙ sym (pr-inj q₂ .snd)

    -- The zero clause: ∅ is a memberless witness, and pr ∅ ∅ lies in the
    -- segment through the pair (∅, Sset ∅) = (∅, ∅) below the limit.
    segZeroClause : K.zeroClause seg
    segZeroClause = ∣ ∅ , (empt , pair) ∣₁
      where
      empt : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → Empty.⊥
      empt z z∈∅ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅)
      pair : ⟨ pr ∅ ∅ ∈ˢ seg ⟩
      pair = subst (λ w → ⟨ w ∈ˢ seg ⟩) (cong₂ pr refl Sset-zero) pr∅S∈
        where
        pr∅S∈ : ⟨ pr ∅ (Sset ∅) ∈ˢ seg ⟩
        pr∅S∈ = seg∈ (pr ∅ (Sset ∅)) .snd ∣ inl (P∈-in ∅ ∅∈δ₀) ∣₁

    -- The one-way successor clause: a present pair at a and at sucV a
    -- forces the value at sucV a to be the step of the value at a.  Below
    -- the limit the pairs read pr ξ (Sset ξ) and pr (sucV ξ) (Sset (sucV ξ));
    -- Sset-suc identifies Sset (sucV ξ) with step (Sset ξ).  The top-pair
    -- cases are empty: sucV δ₀ is neither below the limit nor the limit.
    segSuccClause : succClause seg
    segSuccClause a c b ac∈ ab∈ = PT.rec (setIsSet b (step c)) go₁
      (seg∈ (pr a c) .fst ac∈)
      where
      go₁ : ⟨ pr a c ∈ˢ P ⟩ ⊎ (pr a c ≡ T) → b ≡ step c
      go₁ (inl p₁) = PT.rec (setIsSet b (step c)) p₁go (P∈-out (pr a c) p₁)
        where
        p₁go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ δ₀ ⟩ × (pr a c ≡ pr ξ (Sset ξ)))
             → b ≡ step c
        p₁go (ξ , (ξ∈δ₀ , q₁)) = PT.rec (setIsSet b (step c)) go₂
          (seg∈ (pr (sucV a) b) .fst ab∈)
          where
          a≡ξ : a ≡ ξ
          a≡ξ = pr-inj q₁ .fst
          c≡Sξ : c ≡ Sset ξ
          c≡Sξ = pr-inj q₁ .snd
          sucξ∈δ₀ : ⟨ sucV ξ ∈ˢ δ₀ ⟩
          sucξ∈δ₀ = limit-succ-mem δ₀ ξ limδ₀ ξ∈δ₀
          go₂ : ⟨ pr (sucV a) b ∈ˢ P ⟩ ⊎ (pr (sucV a) b ≡ T) → b ≡ step c
          go₂ (inl p₂) = PT.rec (setIsSet b (step c)) p₂go
            (P∈-out (pr (sucV a) b) p₂)
            where
            p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ δ₀ ⟩
                 × (pr (sucV a) b ≡ pr ξ' (Sset ξ'))) → b ≡ step c
            p₂go (ξ' , (ξ'∈δ₀ , q₂)) =
              pr-inj q₂ .snd ∙ cong Sset ξ'≡sucξ ∙ Sset-suc ξ
              ∙ cong step (sym c≡Sξ)
              where
              ξ'≡sucξ : ξ' ≡ sucV ξ
              ξ'≡sucξ = sym (pr-inj q₂ .fst) ∙ cong sucV a≡ξ
          go₂ (inr q₂) = Empty.rec (∈-irrefl δ₀ bad)
            where
            bad : ⟨ δ₀ ∈ˢ δ₀ ⟩
            bad = subst (λ w → ⟨ w ∈ˢ δ₀ ⟩) sucξ≡δ₀ sucξ∈δ₀
              where
              sucξ≡δ₀ : sucV ξ ≡ δ₀
              sucξ≡δ₀ = cong sucV (sym a≡ξ) ∙ pr-inj q₂ .fst
      go₁ (inr q₁) = PT.rec (setIsSet b (step c)) go₃
        (seg∈ (pr (sucV a) b) .fst ab∈)
        where
        a≡δ₀ : a ≡ δ₀
        a≡δ₀ = pr-inj q₁ .fst
        go₃ : ⟨ pr (sucV a) b ∈ˢ P ⟩ ⊎ (pr (sucV a) b ≡ T) → b ≡ step c
        go₃ (inl p₂) = PT.rec (setIsSet b (step c)) p₂go
          (P∈-out (pr (sucV a) b) p₂)
          where
          p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ δ₀ ⟩
               × (pr (sucV a) b ≡ pr ξ' (Sset ξ'))) → b ≡ step c
          p₂go (ξ' , (ξ'∈δ₀ , q₂)) = Empty.rec (∈-irrefl δ₀ bad)
            where
            bad : ⟨ δ₀ ∈ˢ δ₀ ⟩
            bad = δ₀-ord .fst {x = sucV δ₀} {y = δ₀} (self∈sucV δ₀)
              sucδ₀∈δ₀
              where
              sucδ₀∈δ₀ : ⟨ sucV δ₀ ∈ˢ δ₀ ⟩
              sucδ₀∈δ₀ = subst (λ w → ⟨ w ∈ˢ δ₀ ⟩) ξ'≡sucδ₀ ξ'∈δ₀
                where
                ξ'≡sucδ₀ : ξ' ≡ sucV δ₀
                ξ'≡sucδ₀ = sym (pr-inj q₂ .fst) ∙ cong sucV a≡δ₀
        go₃ (inr q₂) = Empty.rec (∈-irrefl δ₀ bad)
          where
          bad : ⟨ δ₀ ∈ˢ δ₀ ⟩
          bad = subst (λ w → ⟨ δ₀ ∈ˢ w ⟩) sucδ₀≡δ₀ (self∈sucV δ₀)
            where
            sucδ₀≡δ₀ : sucV δ₀ ≡ δ₀
            sucδ₀≡δ₀ = sym (cong sucV a≡δ₀) ∙ pr-inj q₂ .fst
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Block 1 delivers the residue's foundation. The shell states the theorem in
T185's induction shape. The story predicate states the six clauses once at
the generic carrier. The carried-sequence machinery proves the segment's
membership, its exact domain, its limit clause and the four story clauses at
a generic limit index, given the pair family and its decode. Block 2
instantiates the machinery at each carrier, builds the pair family from the
below facts, lands the segment, and supplies the STEP.
<!--zh-->
第一块交付残差的地基。外壳以 T185 的归纳形状陈述定理。故事谓词在通用载体处一次陈述六条子句。载运序列机制在给定对族及其解码时，证明段在通用极限索引处的隶属、精确定义域、极限子句与四条故事子句。第二块在每处载体实例化该机制，从下方诸事实建出对族，让段落地，并供应 STEP。
<!--/-->
