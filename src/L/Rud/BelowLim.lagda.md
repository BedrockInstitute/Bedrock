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

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; _∧̇_; _⇒̇_; _≐_; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈; _∈̇_; var; con )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl; ∈-induction )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl; pair-singleton )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; Lset-layer; layer-trans; 𝒟ₒ; 𝒟ₒ-intro )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using
  ( ∅-ord; numeral-mem; numeral-ord; suc-ord; #∈ω; ω-ord; ∈#-elim; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; isLimit-not-zero; isLimit-not-succ; isSucc
  ; limit-mem-ord; ord-case; predecessor-mem )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( +ω; +ω-limit; +ω-in; +ω-out; +ω-ord; sucIter; suc-⊆ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; ⋃_; union-ax; ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import L.Rud.Step {ℓ} lem ∅ using
  ( Op16; Fof; Sset; Sset-suc; Sset-zero; Sset-mono; step; step-in-self
  ; limit-succ-mem; step-out; StepArm; arm-member; arm-self
  ; arm-image; Fof-f5; f5 )
open import L.Rud.Ops {ℓ} using ( F0; F5; F0-spec; F5-spec )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( BelowLim; Sset-union-limit; Sset-union-in; Lpair-limit; Lpr-limit
  ; Lstage; Lstage₂; Lval; Lstep⊆; suc⁴∈; suc⁴-up; ∅∈Lset; module Below )
open import L.TowerKit {ℓ} lem ∅ using ( Lpair; Ltr; 𝒟ₒ⊆Lsuc; suc⁴ )
import L.Rud.StepGraph {ℓ} lem ∅ as StepGraph
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out; finSet0∅; finSetSuc )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.FinData.Base using ( Fin; toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Nat.Order using ( _<_; ≤-refl )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Functions.Logic as Logic
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Foundations.Prelude using ( isProp→PathP; PathP )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈-asFiber; _∈ₛ_; _≡ₕ_; extensionality )
  renaming ( _⊆_ to _⊆ₛ_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module K = LevelKit C Ctr
open K public

-- C2: the carrier-relative telescope names at a variable carrier.  The
-- Story module's carrier is an inner parameter A, and its graph-layer
-- telescope must be stateable at A (C-21).  The kit's SM and satisfaction
-- live inside DefOf at the carrier; these aliases put the same types in
-- scope before the module, definitionally equal to the kit's names.
SM-at : (u : S) → Type (ℓ-suc ℓ)
SM-at u = Σ[ x ∈ S ] ⟨ x ∈ˢ u ⟩

⊨ᵐ-at : (u : S) {n : ℕ} → Vec (SM-at u) n → Formula ⟪ u ⟫ n → hProp (ℓ-suc ℓ)
⊨ᵐ-at u = go
  where
  module D = DefOf u
  go : {n : ℕ} → Vec (SM-at u) n → Formula ⟪ u ⟫ n → hProp (ℓ-suc ℓ)
  go = D._⊨ᵐ_

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
-- and the segment machinery.  The carrier is an inner parameter A (the C2
-- telescope); the consumer instantiates it at C or at the witness stage
-- Lset γ.  The module telescope is exactly the Clause telescope of
-- L.Rud.StepStory (the graph layer plus the step closure), so the consumer
-- wires the delivered graph layer of L.Rud.StepGraph into it.
module Story
  (A : S) (Atr : isTransV A)
  (stepSub : (c : S) → ⟨ c ∈ˢ A ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ A ⟩)
  (graphOf : Op16 → Formula ⟪ A ⟫ 3)
  (graph-out : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ A ⟩) (a∈ : ⟨ a ∈ˢ A ⟩)
               (y∈ : ⟨ y ∈ˢ A ⟩) → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ A ⟩)
             → ⟨ ⊨ᵐ-at A ((b , b∈) ∷ (a , a∈) ∷ (y , y∈) ∷ []) (graphOf i) ⟩
             → y ≡ Fof i a b)
  (graph-in : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ A ⟩) (a∈ : ⟨ a ∈ˢ A ⟩)
              (y∈ : ⟨ y ∈ˢ A ⟩) → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ A ⟩)
            → y ≡ Fof i a b
            → ⟨ ⊨ᵐ-at A ((b , b∈) ∷ (a , a∈) ∷ (y , y∈) ∷ []) (graphOf i) ⟩)
  (bigOr : Formula ⟪ A ⟫ 3)
  (bigOr-in : (i : Op16) (δ : Vec (SM-at A) 3)
            → ⟨ ⊨ᵐ-at A δ (graphOf i) ⟩ → ⟨ ⊨ᵐ-at A δ bigOr ⟩)
  (bigOr-out : (δ : Vec (SM-at A) 3) (R : hProp (ℓ-suc ℓ))
             → ((i : Op16) → ⟨ ⊨ᵐ-at A δ (graphOf i) ⟩ → ⟨ R ⟩)
             → ⟨ ⊨ᵐ-at A δ bigOr ⟩ → ⟨ R ⟩)
  (eqFrame : {n : ℕ} → Fin n → Formula ⟪ A ⟫ (suc n) → Formula ⟪ A ⟫ n)
  (eqFrame-ok : {n : ℕ} (k : Fin n) (M : Formula ⟪ A ⟫ (suc n))
                (δ : Vec (SM-at A) n) (W : S)
              → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ A ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ A ⟩) → ⟨ ⊨ᵐ-at A ((v , v∈) ∷ δ) M ⟩ → ⟨ v ∈ˢ W ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ A ⟩) → ⟨ v ∈ˢ W ⟩
                 → ⟨ ⊨ᵐ-at A ((v , v∈) ∷ δ) M ⟩)
              → ⟨ ⊨ᵐ-at A δ (eqFrame k M) ⟩ ⟷ fst (lookup k δ) ≡ W)
  where

  module KA = LevelKit A Atr

  import L.Rud.StepStory {ℓ} lem ∅ A Atr as StepStoryA
  module Cl = StepStoryA.Clause stepSub graphOf graph-out graph-in bigOr
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
  story f = KA.pairhood f × KA.singleValued f × KA.zeroClause f × KA.exactDom f
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
    h4 : KA.exactDom f
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
      δStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ A ⟩ × IsOrd δ
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
    h4 : KA.exactDom f
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
        step₂ : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ A ⟩ × IsOrd δ₀
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
    (sucδ₀∈A : ⟨ sucV δ₀ ∈ˢ A ⟩)
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

    segDom₀ : KA.exactDom seg
    segDom₀ = ∣ sucV δ₀ , ( sucδ₀∈A , suc-ord δ₀-ord , segDom-in , segDom-out ) ∣₁

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
    segPairhood : KA.pairhood seg
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
    segSingleValued : KA.singleValued seg
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
    segZeroClause : KA.zeroClause seg
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
## The STEP at the first limit
<!--zh-->
## 第一个极限处的 STEP
<!--/-->

<!--en-->
The STEP is the carried-sequence construction that lands `Sset γ`. This
block delivers the STEP's first instantiation, at the first limit `a₀`,
rebuilt on survivors: the memberships of the S-levels below `a₀`, the
story at the witness stage `Lset a₀`, the finite segments, the pair
family `P` and its decode, the carve that lands the target set, and the
segment's six-clause story. The carrier stays a parameter: the STEP
takes the graph layer at `C` and the carrier geometry that places the
construction's pieces into `C`. The landing is the carve's own: the
story's carve clause `defSet (Lset a₀) ψ ≡ Sset a₀` suffices, and
neither the identification `Sset a₀ ≡ Lset a₀` nor the retired
`L.Rud.HF`/`L.Rud.Finite` enters.
<!--zh-->
STEP 就是让 `Sset γ` 落地的载运序列构造。本块交付 STEP 的第一次实例化，位于第一个极限 `a₀` 处，全部建立在存活件之上：`a₀` 之下各 S 层的隶属、见证阶段 `Lset a₀` 处的故事、有限段、对族 `P` 及其解码、让目标集落地的刻划、以及段的六子句故事。载体仍是参数：STEP 取 `C` 处的图层与把构造各件放进 `C` 的载体几何。落地是刻划自身的：故事的刻划子句 `defSet (Lset a₀) ψ ≡ Sset a₀` 足够，既不需要识别 `Sset a₀ ≡ Lset a₀`，也不引入已归档的 `L.Rud.HF`/`L.Rud.Finite`。
<!--/-->

```agda
module Step
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
  (Tgeom : ⟨ Lset (sucV (sucV (sucV a₀))) ∈ˢ C ⟩)
  (segGeom : ⟨ Lset (sucV (sucV (sucV (sucV (sucV (sucV a₀)))))) ∈ˢ C ⟩)
  where

  -- The story at the carrier, instantiated with the graph layer.
  module St = Story C Ctr stepSub graphOf graph-out graph-in bigOr bigOr-in
    bigOr-out eqFrame eqFrame-ok

  ∅∈a₀ : ⟨ ∅ ∈ˢ a₀ ⟩
  ∅∈a₀ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym St.a₀≡ω) (#∈ω 0)

  ∅∈La₀ : ⟨ ∅ ∈ˢ Lset a₀ ⟩
  ∅∈La₀ = ∅∈Lset a₀ a₀-lim ∅∈a₀

  -- Every numeral lies in the first limit: a₀ is ω.
  nk∈a₀ : (n : ℕ) → ⟨ St.nk n ∈ˢ a₀ ⟩
  nk∈a₀ n = subst (λ w → ⟨ St.nk n ∈ˢ w ⟩) (sym St.a₀≡ω) (#∈ω n)

  -- Numerals land in the stage: the ordinal step, then the limit.
  numeral∈La₀ : (n : ℕ) → ⟨ St.nk n ∈ˢ Lset a₀ ⟩
  numeral∈La₀ n = Lset-mono {α = a₀} {β = sucV (St.nk n)}
    (limit-succ-mem a₀ (St.nk n) a₀-lim (nk∈a₀ n))
    (ord∈Lset-suc (St.nk n) (numeral-ord n))

  -- The memberships: S-levels below the first limit, by the tower's
  -- successor read on the surviving StepGraph values.
  sucStep : (δ : S) → ⟨ δ ∈ˢ a₀ ⟩ → ⟨ Sset δ ∈ˢ Lset a₀ ⟩
          → ⟨ Sset (sucV δ) ∈ˢ Lset a₀ ⟩
  sucStep δ δ∈a₀ u∈ = PT.rec (snd (Sset (sucV δ) ∈ˢ Lset a₀)) atStage
    (Lstage₂ a₀ a₀-lim (Sset δ) ∅ u∈ ∅∈La₀)
    where
    atStage : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ a₀ ⟩ × ⟨ Sset δ ∈ˢ Lset ζ ⟩ × ⟨ ∅ ∈ˢ Lset ζ ⟩)
            → ⟨ Sset (sucV δ) ∈ˢ Lset a₀ ⟩
    atStage (ζ , (ζ∈a₀ , u∈ζ , A∈ζ)) =
      subst (λ w → ⟨ w ∈ˢ Lset a₀ ⟩) (sym (Sset-suc δ))
        (Lset-mono {α = a₀} {β = ζ₆} ζ₆∈a₀
          (StepGraph.stepSet∈L (Sset δ) ζ₅ u∈₅ (up₁ ζ₄ ∅ A∈₄) stepSubW))
      where
      ζ₄ ζ₅ ζ₆ : S
      ζ₄ = suc⁴ ζ
      ζ₅ = sucV ζ₄
      ζ₆ = sucV ζ₅
      up₁ : (ξ y : S) → ⟨ y ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset (sucV ξ) ⟩
      up₁ ξ y h = Lset-mono {α = sucV ξ} {β = ξ} (self∈sucV ξ) h
      ζ₄∈a₀ : ⟨ ζ₄ ∈ˢ a₀ ⟩
      ζ₄∈a₀ = suc⁴∈ a₀ ζ a₀-lim ζ∈a₀
      ζ₅∈a₀ : ⟨ ζ₅ ∈ˢ a₀ ⟩
      ζ₅∈a₀ = limit-succ-mem a₀ ζ₄ a₀-lim ζ₄∈a₀
      ζ₆∈a₀ : ⟨ ζ₆ ∈ˢ a₀ ⟩
      ζ₆∈a₀ = limit-succ-mem a₀ ζ₅ a₀-lim ζ₅∈a₀
      u∈₄ : ⟨ Sset δ ∈ˢ Lset ζ₄ ⟩
      u∈₄ = suc⁴-up ζ (Sset δ) u∈ζ
      A∈₄ : ⟨ ∅ ∈ˢ Lset ζ₄ ⟩
      A∈₄ = suc⁴-up ζ ∅ A∈ζ
      stepSubW : (v : S) → ⟨ v ∈ˢ step (Sset δ) ⟩ → ⟨ v ∈ˢ Lset ζ₅ ⟩
      stepSubW = Lstep⊆ (Sset δ) ζ₄ A∈₄ u∈₄
        (StepGraph.values∈L (Sset δ) ζ u∈ζ)
      u∈₅ : ⟨ Sset δ ∈ˢ Lset ζ₅ ⟩
      u∈₅ = up₁ ζ₄ (Sset δ) u∈₄

  memberAt : (n : ℕ) → ⟨ Sset (St.nk n) ∈ˢ Lset a₀ ⟩
  memberAt zero = subst (λ w → ⟨ w ∈ˢ Lset a₀ ⟩) (sym Sset-zero) ∅∈La₀
  memberAt (suc n) = sucStep (St.nk n) (nk∈a₀ n) (memberAt n)

  -- The T193 input: S-levels of the first limit's members.
  seg∈L : (ξ : S) → ⟨ ξ ∈ˢ a₀ ⟩ → ⟨ Sset ξ ∈ˢ Lset a₀ ⟩
  seg∈L ξ ξ∈a₀ = PT.rec (snd (Sset ξ ∈ˢ Lset a₀)) go
    (subst (λ w → ⟨ ξ ∈ˢ w ⟩) St.a₀≡ω ξ∈a₀)
    where
    go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower m) ≡ ξ)
       → ⟨ Sset ξ ∈ˢ Lset a₀ ⟩
    go (m , q) = subst (λ w → ⟨ Sset w ∈ˢ Lset a₀ ⟩) q (memberAt (lower m))

  -- The witness carrier: the stage at the first limit.  The kit is
  -- qualified.
  W : S
  W = Lset a₀

  Wtr : isTransV W
  Wtr = layer-trans (Lset-layer a₀)

  module KW = LevelKit W Wtr

  -- The step closure at the witness carrier.
  stepInL : (c : S) → ⟨ c ∈ˢ W ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ W ⟩
  stepInL c c∈ v v∈step = PT.rec (snd (v ∈ˢ W)) go (step-out c v v∈step)
    where
    go : StepArm c v → ⟨ v ∈ˢ W ⟩
    go (arm-member v∈c) = Ltr a₀ {x = c} {y = v} v∈c c∈
    go (arm-self e) = subst (λ w → ⟨ w ∈ˢ W ⟩) (sym e) c∈
    go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ W)) both
      (Lstage₂ a₀ a₀-lim c ∅ c∈ ∅∈La₀)
      where
      both : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ c ∈ˢ Lset ξ ⟩ × ⟨ ∅ ∈ˢ Lset ξ ⟩)
           → ⟨ v ∈ˢ W ⟩
      both (ξ , (ξ∈a₀ , c∈ξ , A∈ξ)) =
        Lset-mono {α = a₀} {β = sucV (suc⁴ ξ)}
          (limit-succ-mem a₀ (suc⁴ ξ) a₀-lim (suc⁴∈ a₀ ξ a₀-lim ξ∈a₀))
          (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ξ)) ⟩) (sym e)
            (Lval (suc⁴ ξ) (suc⁴-up ξ ∅ A∈ξ) i a b a∈ b∈
              (StepGraph.values∈L c ξ c∈ξ i a b sa sb)))
        where
        argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ξ ⟩
        argIn x (inl h) = Ltr ξ h c∈ξ
        argIn x (inr e') = subst (λ w → ⟨ w ∈ˢ Lset ξ ⟩) (sym e') c∈ξ
        a∈ : ⟨ a ∈ˢ Lset (suc⁴ ξ) ⟩
        a∈ = suc⁴-up ξ a (argIn a sa)
        b∈ : ⟨ b ∈ˢ Lset (suc⁴ ξ) ⟩
        b∈ = suc⁴-up ξ b (argIn b sb)

  -- The graph layer at the witness carrier.
  mA₀ : ⟪ W ⟫
  mA₀ = ∈-asFiber {a = ∅} {b = W} ∅∈La₀ .fst

  qA₀ : ⟪ W ⟫↪ mA₀ ≡ ∅
  qA₀ = ∈-asFiber {a = ∅} {b = W} ∅∈La₀ .snd

  module WL = StepGraph.Layer W Wtr mA₀ qA₀ ∅∈La₀
  module WB = WL.BigOr WL.graphOf

  import L.Rud.StepStory {ℓ} lem ∅ W Wtr as StepStoryW
  module WCl = StepStoryW.Clause stepInL WL.graphOf WL.graph-out WL.graph-in
    WB.bigOr WB.bigOr-in WB.bigOr-out WL.eqFrame WL.eqFrame-ok

  -- The five-clause story at the witness carrier.
  storyW : S → Type (ℓ-suc ℓ)
  storyW f = KW.pairhood f × KW.singleValued f × KW.zeroClause f
           × KW.exactDom f × WCl.succClause f

  storyFormW : Formula ⟪ W ⟫ 2
  storyFormW = KW.pairForm ∧̇ KW.singleForm ∧̇ KW.zeroForm
             ∧̇ KW.exactDomForm ∧̇ WCl.succForm

  storyW-out : (f : KW.SM) (x : ⟪ W ⟫)
             → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW ⟩ → storyW (fst f)
  storyW-out f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( KW.pairhood-out f x h₁
    , ( KW.single-out f x h₂
      , ( KW.zero-out f x h₃
        , ( KW.exactDom-out f x h₄ , WCl.succ-ok f x .fst h₅ ) ) ) )

  storyW-in : (f : KW.SM) (x : ⟪ W ⟫)
            → storyW (fst f) → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW ⟩
  storyW-in f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( KW.pairhood-in f x h₁
    , ( KW.single-in f x h₂
      , ( KW.zero-in f x h₃
        , ( KW.exactDom-in f x h₄ , WCl.succ-ok f x .snd h₅ ) ) ) )

  storyW-ok : (f : KW.SM) (x : ⟪ W ⟫)
            → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW ⟩ ⟷ storyW (fst f)
  storyW-ok f x = storyW-out f x , storyW-in f x

  -- The numeral chain (T127's O7).
  chainValueW : (f : S) → storyW f → (a x : S) → ⟨ a ∈ˢ ω ⟩
              → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Sset a
  chainValueW f st a x a∈ω ax∈f = PT.rec (setIsSet x (Sset a)) go a∈ω
    where
    h4 : KW.exactDom f
    h4 = st .snd .snd .snd .fst
    chainNum : (n : ℕ) (x : S) → ⟨ pr (St.nk n) x ∈ˢ f ⟩ → x ≡ Sset (St.nk n)
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
    chainNum (suc n) x px = PT.rec (setIsSet x (Sset (St.nk (suc n)))) δStep h4
      where
      δStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ W ⟩ × IsOrd δ
               × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
               × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
            → x ≡ Sset (St.nk (suc n))
      δStep (δ , (δ∈u , ordδ , in-dir , out-dir)) = x≡stepS#n ∙ step≡Sset
        where
        suc∈δ : ⟨ sucV (St.nk n) ∈ˢ δ ⟩
        suc∈δ = out-dir (sucV (St.nk n)) ∣ x , px ∣₁
        n∈δ : ⟨ St.nk n ∈ˢ δ ⟩
        n∈δ = ordδ .fst {x = sucV (St.nk n)} {y = St.nk n}
          (self∈sucV (St.nk n)) suc∈δ
        x≡stepS#n : x ≡ step (Sset (St.nk n))
        x≡stepS#n = PT.rec (setIsSet x (step (Sset (St.nk n)))) cStep
          (in-dir (St.nk n) n∈δ)
          where
          cStep : Σ[ c ∈ S ] ⟨ pr (St.nk n) c ∈ˢ f ⟩
                → x ≡ step (Sset (St.nk n))
          cStep (c , prnc) = st .snd .snd .snd .snd
            (St.nk n) (Sset (St.nk n)) x prn px
            where
            prn : ⟨ pr (St.nk n) (Sset (St.nk n)) ∈ˢ f ⟩
            prn = subst (λ w → ⟨ pr (St.nk n) w ∈ˢ f ⟩)
              (chainNum n c prnc) prnc
        step≡Sset : step (Sset (St.nk n)) ≡ Sset (St.nk (suc n))
        step≡Sset = sym (Sset-suc (St.nk n))
    go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower m) ≡ a) → x ≡ Sset a
    go (m , q) = subst (λ w → x ≡ Sset w) q
      (chainNum (lower m) x ax∈f')
      where
      ax∈f' : ⟨ pr (St.nk (lower m)) x ∈ˢ f ⟩
      ax∈f' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) (sym q) ax∈f

  -- The finite segments (T127's O6).
  Lstage₃ : (x y z : S) → ⟨ x ∈ˢ W ⟩ → ⟨ y ∈ˢ W ⟩ → ⟨ z ∈ˢ W ⟩
          → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩
               × ⟨ z ∈ˢ Lset ξ ⟩) ∥₁
  Lstage₃ x y z x∈ y∈ z∈ = PT.rec squash₁ s₁ (Lstage₂ a₀ a₀-lim x y x∈ y∈)
    where
    s₁ : Σ[ ξ₁ ∈ S ] (⟨ ξ₁ ∈ˢ a₀ ⟩ × ⟨ x ∈ˢ Lset ξ₁ ⟩ × ⟨ y ∈ˢ Lset ξ₁ ⟩)
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩
            × ⟨ z ∈ˢ Lset ξ ⟩) ∥₁
    s₁ (ξ₁ , (ξ₁∈a₀ , x∈₁ , y∈₁)) = PT.rec squash₁ s₂ (Lstage a₀ a₀-lim z z∈)
      where
      s₂ : Σ[ ξ₂ ∈ S ] (⟨ ξ₂ ∈ˢ a₀ ⟩ × ⟨ z ∈ˢ Lset ξ₂ ⟩)
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩
              × ⟨ z ∈ˢ Lset ξ ⟩) ∥₁
      s₂ (ξ₂ , (ξ₂∈a₀ , z∈₂)) = ∣ go tri ∣₁
        where
        tri : Tri ξ₁ ξ₂
        tri = ord-tri ξ₁ (limit-mem-ord a₀ a₀-lim ξ₁ ξ₁∈a₀)
                   ξ₂ (limit-mem-ord a₀ a₀-lim ξ₂ ξ₂∈a₀)
        go : Tri ξ₁ ξ₂ → Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩
             × ⟨ y ∈ˢ Lset ξ ⟩ × ⟨ z ∈ˢ Lset ξ ⟩)
        go (inl ξ₁∈ξ₂) = ξ₂ , (ξ₂∈a₀
          , Lset-mono {α = ξ₂} {β = ξ₁} ξ₁∈ξ₂ x∈₁
          , Lset-mono {α = ξ₂} {β = ξ₁} ξ₁∈ξ₂ y∈₁ , z∈₂)
        go (inr (inl ξ₁≡ξ₂)) = ξ₂ , (ξ₂∈a₀
          , subst (λ w → ⟨ x ∈ˢ Lset w ⟩) ξ₁≡ξ₂ x∈₁
          , subst (λ w → ⟨ y ∈ˢ Lset w ⟩) ξ₁≡ξ₂ y∈₁ , z∈₂)
        go (inr (inr ξ₂∈ξ₁)) = ξ₁ , (ξ₁∈a₀
          , x∈₁ , y∈₁ , Lset-mono {α = ξ₁} {β = ξ₂} ξ₂∈ξ₁ z∈₂)

  -- The binary union closes inside the stage.
  Fof-f5-limit : (a b : S) → ⟨ a ∈ˢ W ⟩ → ⟨ b ∈ˢ W ⟩
               → ⟨ Fof f5 a b ∈ˢ W ⟩
  Fof-f5-limit a b a∈ b∈ = PT.rec (snd (Fof f5 a b ∈ˢ W)) atStage
    (Lstage₃ a b ∅ a∈ b∈ ∅∈La₀)
    where
    atStage : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ a ∈ˢ Lset ξ ⟩ × ⟨ b ∈ˢ Lset ξ ⟩
               × ⟨ ∅ ∈ˢ Lset ξ ⟩)
            → ⟨ Fof f5 a b ∈ˢ W ⟩
    atStage (ξ , (ξ∈a₀ , a∈ξ , b∈ξ , A∈ξ)) =
      Lset-mono {α = a₀} {β = sucV ξ} (limit-succ-mem a₀ ξ a₀-lim ξ∈a₀)
        (Lval ξ A∈ξ f5 a b a∈ξ b∈ξ sub)
      where
      sub : (v : S) → ⟨ v ∈ˢ Fof f5 a b ⟩ → ⟨ v ∈ˢ Lset ξ ⟩
      sub v v∈ = PT.rec (snd (v ∈ˢ Lset ξ)) go
        (union-ax a v .fst (∈∈ₛ {a = v} {b = ⋃ a} .fst
          (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f5 a b) v∈)))
        where
        go : Σ[ u ∈ S ] (⟨ u ∈ₛ a ⟩ × ⟨ v ∈ₛ u ⟩) → ⟨ v ∈ˢ Lset ξ ⟩
        go (u , (u∈ₛa , v∈ₛu)) = Ltr ξ {x = u} {y = v}
          (∈∈ₛ {a = v} {b = u} .snd v∈ₛu)
          (Ltr ξ {x = a} {y = u} (∈∈ₛ {a = u} {b = a} .snd u∈ₛa) a∈ξ)

  -- A finite family of members of W is a member of W.
  finSet∈W : (n : ℕ) (h : Fin n → S)
           → ((i : Fin n) → ⟨ h i ∈ˢ W ⟩) → ⟨ finSet n h ∈ˢ W ⟩
  finSet∈W zero h hin = subst (λ w → ⟨ w ∈ˢ W ⟩) (sym (finSet0∅ h)) ∅∈La₀
  finSet∈W (suc n) h hin =
    subst (λ w → ⟨ w ∈ˢ W ⟩) (sym (finSetSuc n h)) big
    where
    S1 : S
    S1 = F0 (h zero) (h zero)
    X : S
    X = finSet n (h ∘ suc)
    P : S
    P = F0 S1 X
    S1∈ : ⟨ S1 ∈ˢ W ⟩
    S1∈ = Lpair-limit a₀ a₀-lim (h zero) (h zero) (hin zero) (hin zero)
    X∈ : ⟨ X ∈ˢ W ⟩
    X∈ = finSet∈W n (h ∘ suc) (λ i → hin (suc i))
    P∈ : ⟨ P ∈ˢ W ⟩
    P∈ = Lpair-limit a₀ a₀-lim S1 X S1∈ X∈
    big : ⟨ F5 P (h zero) ∈ˢ W ⟩
    big = subst (λ w → ⟨ w ∈ˢ W ⟩) (Fof-f5 P (h zero))
      (Fof-f5-limit P (h zero) P∈ (hin zero))

  -- The segment of length n: the pairs (k, Sset k), k ≤ n.
  seg : (n : ℕ) → S
  seg n = finSet (suc n) (λ i → pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i))))

  seg∈W : (n : ℕ) → ⟨ seg n ∈ˢ W ⟩
  seg∈W n = finSet∈W (suc n) h pairs∈
    where
    h : Fin (suc n) → S
    h i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
    pairs∈ : (i : Fin (suc n)) → ⟨ h i ∈ˢ W ⟩
    pairs∈ i = Lpr-limit a₀ a₀-lim (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
      (numeral∈La₀ (toℕ i)) (memberAt (toℕ i))

  -- Pairhood on the segment.
  segPair : (n : ℕ) (z : S) → ⟨ z ∈ˢ seg n ⟩ → isPair z
  segPair n z z∈ = PT.rec squash₁ go (finSet-out (suc n) h z z∈)
    where
    h : Fin (suc n) → S
    h i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
    go : Σ[ i ∈ Fin (suc n) ] (h i ≡ z) → isPair z
    go (i , q) = ∣ St.nk (toℕ i) , (Sset (St.nk (toℕ i)) , sym q) ∣₁

  -- Single-valuedness on the segment.
  segSingle : (n : ℕ) → KW.singleValued (seg n)
  segSingle n a b c ab∈ ac∈ = PT.rec (setIsSet b c) go₁
    (finSet-out (suc n) h (pr a b) ab∈)
    where
    h : Fin (suc n) → S
    h i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
    go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a b) → b ≡ c
    go₁ (i , q₁) = PT.rec (setIsSet b c) go₂
      (finSet-out (suc n) h (pr a c) ac∈)
      where
      a≡#i : a ≡ St.nk (toℕ i)
      a≡#i = pr-inj (sym q₁) .fst
      b≡S#i : b ≡ Sset (St.nk (toℕ i))
      b≡S#i = pr-inj (sym q₁) .snd
      go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr a c) → b ≡ c
      go₂ (j , q₂) =
        b≡S#i ∙ cong Sset (cong St.nk (#-inj′ {toℕ i} {toℕ j} #i≡#j))
        ∙ sym (pr-inj (sym q₂) .snd)
        where
        #i≡#j : St.nk (toℕ i) ≡ St.nk (toℕ j)
        #i≡#j = sym a≡#i ∙ pr-inj (sym q₂) .fst

  -- The zero clause on the segment.
  segZero : (n : ℕ) → KW.zeroClause (seg n)
  segZero n = ∣ ∅ , (empt , pair) ∣₁
    where
    h : Fin (suc n) → S
    h i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
    idx : Fin (suc n)
    idx = zero
    h-idx : h idx ≡ pr ∅ ∅
    h-idx = cong₂ pr refl Sset-zero
    empt : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → Empty.⊥
    empt z z∈∅ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅)
    pair : ⟨ pr ∅ ∅ ∈ˢ seg n ⟩
    pair = finSet-in (suc n) h (pr ∅ ∅) ∣ idx , h-idx ∣₁

  -- The exact domain: # (suc n).
  segDom : (n : ℕ) → KW.exactDom (seg n)
  segDom n = ∣ St.nk (suc n) , ( numeral∈La₀ (suc n) , numeral-ord (suc n)
    , in-dir , out-dir ) ∣₁
    where
    h : Fin (suc n) → S
    h i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
    in-dir : (a : S) → ⟨ a ∈ˢ St.nk (suc n) ⟩
           → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
    in-dir a a∈ = PT.rec squash₁ go (∈#-elim (suc n) a a∈)
      where
      go : Σ[ m ∈ ℕ ] ((m < suc n) × (a ≡ St.nk m))
         → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
      go (m , (p , q)) = ∣ Sset (St.nk m) , pr-in ∣₁
        where
        idx : Fin (suc n)
        idx = fromℕ' (suc n) m p
        e : toℕ idx ≡ m
        e = toFromId' (suc n) m p
        h-idx : h idx ≡ pr (St.nk m) (Sset (St.nk m))
        h-idx = cong₂ pr (cong St.nk e) (cong Sset (cong St.nk e))
        pr-in : ⟨ pr a (Sset (St.nk m)) ∈ˢ seg n ⟩
        pr-in = finSet-in (suc n) h (pr a (Sset (St.nk m)))
          ∣ idx , (h-idx ∙ cong₂ pr (sym q) refl) ∣₁
    out-dir : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
            → ⟨ a ∈ˢ St.nk (suc n) ⟩
    out-dir a = PT.rec (snd (a ∈ˢ St.nk (suc n))) go
      where
      go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ → ⟨ a ∈ˢ St.nk (suc n) ⟩
      go (b , ab∈) = PT.rec (snd (a ∈ˢ St.nk (suc n))) go₂
        (finSet-out (suc n) h (pr a b) ab∈)
        where
        go₂ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a b) → ⟨ a ∈ˢ St.nk (suc n) ⟩
        go₂ (i , q) = subst (λ w → ⟨ w ∈ˢ St.nk (suc n) ⟩)
          (sym (pr-inj (sym q) .fst)) (#mono (toℕ i) (suc n) (toℕ<n i))

  -- The one-way successor clause on the segment.
  segSucc1 : (n : ℕ) → WCl.succClause (seg n)
  segSucc1 n a c b ac∈ ab∈ = PT.rec (setIsSet b (step c)) go₁
    (finSet-out (suc n) h (pr a c) ac∈)
    where
    h : Fin (suc n) → S
    h i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
    go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a c) → b ≡ step c
    go₁ (i , q₁) = PT.rec (setIsSet b (step c)) go₂
      (finSet-out (suc n) h (pr (sucV a) b) ab∈)
      where
      a≡#i : a ≡ St.nk (toℕ i)
      a≡#i = pr-inj (sym q₁) .fst
      c≡Sseta : c ≡ Sset a
      c≡Sseta = pr-inj (sym q₁) .snd ∙ cong Sset (sym a≡#i)
      go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr (sucV a) b) → b ≡ step c
      go₂ (j , q₂) = b≡SsetSucA ∙ Sset-suc a ∙ cong step (sym c≡Sseta)
        where
        sucA≡#j : sucV a ≡ St.nk (toℕ j)
        sucA≡#j = pr-inj (sym q₂) .fst
        b≡SsetSucA : b ≡ Sset (sucV a)
        b≡SsetSucA = pr-inj (sym q₂) .snd ∙ cong Sset (sym sucA≡#j)

  -- The top pair pr (# m) (Sset (# m)) lies in seg m.
  segTopPair : (m : ℕ) → ⟨ pr (St.nk m) (Sset (St.nk m)) ∈ˢ seg m ⟩
  segTopPair m = finSet-in (suc m) h (pr (St.nk m) (Sset (St.nk m)))
    ∣ idx , h-idx ∣₁
    where
    h : Fin (suc m) → S
    h i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
    idx : Fin (suc m)
    idx = fromℕ' (suc m) m (≤-refl {suc m})
    e : toℕ idx ≡ m
    e = toFromId' (suc m) m (≤-refl {suc m})
    h-idx : h idx ≡ pr (St.nk m) (Sset (St.nk m))
    h-idx = cong₂ pr (cong St.nk e) (cong Sset (cong St.nk e))

  -- The segment satisfies the one-way story.
  segStory : (n : ℕ) → storyW (seg n)
  segStory n = segPair n , (segSingle n , (segZero n , (segDom n , segSucc1 n)))

  -- The pairs below the first limit lie in the witness stage.
  prξSξ∈W : (ξ : S) → ⟨ ξ ∈ˢ a₀ ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ W ⟩
  prξSξ∈W ξ ξ∈a₀ = PT.rec (snd (pr ξ (Sset ξ) ∈ˢ W)) go
    (subst (λ w → ⟨ ξ ∈ˢ w ⟩) St.a₀≡ω ξ∈a₀)
    where
    go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower m) ≡ ξ)
       → ⟨ pr ξ (Sset ξ) ∈ˢ W ⟩
    go (m , q) = subst (λ w → ⟨ pr w (Sset w) ∈ˢ W ⟩) q
      (Lpr-limit a₀ a₀-lim (St.nk (lower m)) (Sset (St.nk (lower m)))
        (numeral∈La₀ (lower m)) (memberAt (lower m)))

  -- The pair family formula (T159's segForm).
  smEta : (x : KW.SM) → x ≡ KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst)
  smEta x = ΣPathP (p , q)
    where
    p : fst x ≡ fst (KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst))
    p = sym (∈-asFiber {a = fst x} {b = W} (snd x) .snd)
    q : PathP (λ i → ⟨ p i ∈ˢ W ⟩) (snd x)
           (snd (KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst)))
    q = isProp→PathP (λ i → snd (p i ∈ˢ W))
      (snd x) (snd (KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst)))

  -- The story formula renamed into the arity-4 environment.
  embStory : Fin 2 → Fin 4
  embStory zero = suc (suc zero)
  embStory (suc zero) = suc zero

  storyRen : Formula ⟪ W ⟫ 4
  storyRen = renameFo embStory storyFormW

  module RenS = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ W))
    {ℓ} {⟪ W ⟫} KW.ι

  storyRen-ok : (δ : Vec KW.SM 4)
              → ⟨ δ KW.⊨ᵐ storyRen ⟩ ⟷ storyW (fst (lookup (suc (suc zero)) δ))
  storyRen-ok δ = (out , bwd)
    where
    sm ym : KW.SM
    sm = lookup (suc (suc zero)) δ
    ym = lookup (suc zero) δ
    fibY : ⟪ W ⟫
    fibY = ∈-asFiber {a = fst ym} {b = W} (snd ym) .fst
    ag : RenS.Agrees embStory δ (sm ∷ ym ∷ [])
    ag zero = refl
    ag (suc zero) = refl
    out : ⟨ δ KW.⊨ᵐ storyRen ⟩ → storyW (fst sm)
    out h = storyW-ok sm fibY .fst
      (subst (λ w → ⟨ (sm ∷ w ∷ []) KW.⊨ᵐ storyFormW ⟩) (smEta ym)
        (subst ⟨_⟩ (sym (RenS.⊨-rename embStory storyFormW δ (sm ∷ ym ∷ []) ag)) h))
    bwd : storyW (fst sm) → ⟨ δ KW.⊨ᵐ storyRen ⟩
    bwd st = subst ⟨_⟩
      (RenS.⊨-rename embStory storyFormW δ (sm ∷ ym ∷ []) ag)
      (subst (λ w → ⟨ (sm ∷ w ∷ []) KW.⊨ᵐ storyFormW ⟩) (sym (smEta ym))
        (storyW-ok sm fibY .snd st))

  -- The segment's defining formula.
  segBody : Formula ⟪ W ⟫ 4
  segBody = (KW.PK.prAt (suc (suc (suc zero))) zero (suc zero))
        ∧̇ (KW.isOrdAt zero)
        ∧̇ storyRen
        ∧̇ (∃̇∈ (var (suc (suc zero)))
              (KW.PK.prAt zero (suc zero) (suc (suc zero))))

  segForm : Formula ⟪ W ⟫ 1
  segForm = ∃̇ (∃̇ (∃̇ segBody))

  -- The decode: the extension is exactly the pairs (ξ, Sset ξ), ξ ∈ ω.
  -- The index bound reads through the delivered strengthened ordinal
  -- reading, shared with the carve decode.
  exactDom-ξ∈ω : (f : S) (ξ y : S) → KW.exactDom f → ⟨ pr ξ y ∈ˢ f ⟩
               → ⟨ ξ ∈ˢ ω ⟩
  exactDom-ξ∈ω f ξ y h4 pr∈ = PT.rec (snd (ξ ∈ˢ ω)) dStep h4
    where
    dStep : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ W ⟩ × IsOrd δ₀
             × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩
                → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
             × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁
                → ⟨ a ∈ˢ δ₀ ⟩) )
          → ⟨ ξ ∈ˢ ω ⟩
    dStep (δ₀ , (δ₀∈u , ordδ₀ , _ , out-d)) =
      ω-ord .fst {x = δ₀} {y = ξ} ξ∈δ₀ δ₀∈ω
      where
      ξ∈δ₀ : ⟨ ξ ∈ˢ δ₀ ⟩
      ξ∈δ₀ = out-d ξ ∣ y , pr∈ ∣₁
      δ₀∈ω : ⟨ δ₀ ∈ˢ ω ⟩
      δ₀∈ω = ord∈Lset→∈ ω ω-ord δ₀ ordδ₀
        (subst (λ w → ⟨ δ₀ ∈ˢ Lset w ⟩) St.a₀≡ω δ₀∈u)

  segForm-ok : (m : ⟪ W ⟫)
             → ⟨ (KW.ι m ∷ []) KW.⊨ᵐ segForm ⟩
             ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
  segForm-ok m = (out , bwd)
    where
    δ₁ : Vec KW.SM 1
    δ₁ = KW.ι m ∷ []
    out : ⟨ δ₁ KW.⊨ᵐ segForm ⟩
        → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
    out sat = PT.rec squash₁ s₁ sat
      where
      s₁ : Σ[ sm ∈ KW.SM ] ⟨ (sm ∷ δ₁) KW.⊨ᵐ ∃̇ (∃̇ segBody) ⟩
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
      s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
        where
        s₂ : Σ[ ym ∈ KW.SM ] ⟨ (ym ∷ sm ∷ δ₁) KW.⊨ᵐ ∃̇ segBody ⟩
           → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
        s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
          where
          s₃ : Σ[ ξm ∈ KW.SM ] ⟨ (ξm ∷ ym ∷ sm ∷ δ₁) KW.⊨ᵐ segBody ⟩
             → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
          s₃ (ξm , (pr-sat , (ord-sat , (st-sat , pr∈-sat)))) =
            ∣ fst ξm , (ξ∈ω , x≡prξSξ) ∣₁
            where
            δ₄ : Vec KW.SM 4
            δ₄ = ξm ∷ ym ∷ sm ∷ δ₁
            x≡prξy : ⟪ W ⟫↪ m ≡ pr (fst ξm) (fst ym)
            x≡prξy = KW.PK.prAt-out (suc (suc (suc zero))) zero (suc zero)
              δ₄ pr-sat
            st : storyW (fst sm)
            st = storyRen-ok δ₄ .fst st-sat
            h4 : KW.exactDom (fst sm)
            h4 = st .snd .snd .snd .fst
            prξy∈s : ⟨ pr (fst ξm) (fst ym) ∈ˢ fst sm ⟩
            prξy∈s = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
            ξ∈ω : ⟨ fst ξm ∈ˢ ω ⟩
            ξ∈ω = exactDom-ξ∈ω (fst sm) (fst ξm) (fst ym) h4 prξy∈s
            y≡Ssetξ : fst ym ≡ Sset (fst ξm)
            y≡Ssetξ = chainValueW (fst sm) st (fst ξm) (fst ym) ξ∈ω prξy∈s
            x≡prξSξ : ⟪ W ⟫↪ m ≡ pr (fst ξm) (Sset (fst ξm))
            x≡prξSξ = x≡prξy ∙ cong₂ pr refl y≡Ssetξ
    bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
        → ⟨ δ₁ KW.⊨ᵐ segForm ⟩
    bwd h = PT.rec (snd (δ₁ KW.⊨ᵐ segForm)) step₀ h
      where
      step₀ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ)))
            → ⟨ δ₁ KW.⊨ᵐ segForm ⟩
      step₀ (ξ , (ξ∈ω , x≡prξSξ)) = PT.rec (snd (δ₁ KW.⊨ᵐ segForm)) num ξ∈ω
        where
        num : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower k) ≡ ξ)
            → ⟨ δ₁ KW.⊨ᵐ segForm ⟩
        num (k , #k≡ξ) = ∣ sm , (∣ ym , (∣ ξm , body-sat ∣₁) ∣₁) ∣₁
          where
          ξ∈W : ⟨ ξ ∈ˢ W ⟩
          ξ∈W = subst (λ w → ⟨ w ∈ˢ W ⟩) #k≡ξ (numeral∈La₀ (lower k))
          Sξ∈W : ⟨ Sset ξ ∈ˢ W ⟩
          Sξ∈W = subst (λ w → ⟨ Sset w ∈ˢ W ⟩) #k≡ξ (memberAt (lower k))
          sm ym ξm : KW.SM
          sm = KW.PK.pt (seg (lower k)) (seg∈W (lower k))
          ym = KW.PK.pt (Sset ξ) Sξ∈W
          ξm = KW.PK.pt ξ ξ∈W
          δ₄ : Vec KW.SM 4
          δ₄ = ξm ∷ ym ∷ sm ∷ δ₁
          body-sat : ⟨ δ₄ KW.⊨ᵐ segBody ⟩
          body-sat = ( pr-sat , (ord-sat , (st-sat , pr∈-sat)) )
            where
            pr-sat : ⟨ δ₄ KW.⊨ᵐ KW.PK.prAt (suc (suc (suc zero))) zero (suc zero) ⟩
            pr-sat = KW.PK.prAt-in (suc (suc (suc zero))) zero (suc zero) δ₄
              x≡prξSξ
            ord-sat : ⟨ δ₄ KW.⊨ᵐ KW.isOrdAt zero ⟩
            ord-sat = KW.isOrd-in zero δ₄
              (subst IsOrd #k≡ξ (numeral-ord (lower k)))
            st-sat : ⟨ δ₄ KW.⊨ᵐ storyRen ⟩
            st-sat = storyRen-ok δ₄ .snd (segStory (lower k))
            prξSξ∈s : ⟨ pr ξ (Sset ξ) ∈ˢ seg (lower k) ⟩
            prξSξ∈s = finSet-in (suc (lower k)) hseg (pr ξ (Sset ξ)) ∣ idx , eq ∣₁
              where
              hseg : Fin (suc (lower k)) → S
              hseg i = pr (St.nk (toℕ i)) (Sset (St.nk (toℕ i)))
              idx : Fin (suc (lower k))
              idx = fromℕ' (suc (lower k)) (lower k) (≤-refl {suc (lower k)})
              e : toℕ idx ≡ lower k
              e = toFromId' (suc (lower k)) (lower k) (≤-refl {suc (lower k)})
              eq : hseg idx ≡ pr ξ (Sset ξ)
              eq = cong₂ pr (cong St.nk e) (cong Sset (cong St.nk e))
                 ∙ cong₂ pr #k≡ξ (cong Sset #k≡ξ)
            pr∈-sat : ⟨ δ₄ KW.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                         (KW.PK.prAt zero (suc zero) (suc (suc zero))) ⟩
            pr∈-sat = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd prξSξ∈s

  -- P: the definable family of pairs below the first limit.
  module D = DefOf W

  P : S
  P = D.defSet segForm

  -- The decode at the first limit, in the Segment shape.
  P∈ : (p : S) → ⟨ p ∈ˢ P ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
         × (p ≡ pr ξ (Sset ξ))) ∥₁
  P∈ p = (out , bwd)
    where
    out : ⟨ p ∈ˢ P ⟩ → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
    out p∈ = PT.rec squash₁ go (segForm-ok m .fst sat)
      where
      m : ⟪ W ⟫
      m = ∈-asFiber {a = p} {b = W} (D.defSet⊆A segForm p p∈) .fst
      sat : ⟨ (KW.ι m ∷ []) KW.⊨ᵐ segForm ⟩
      sat = subst ⟨_⟩ (D.defSet-mem segForm m)
        (subst (λ w → ⟨ w ∈ˢ P ⟩) (sym (∈-asFiber {a = p} {b = W}
          (D.defSet⊆A segForm p p∈) .snd)) p∈)
      go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ W ⟫↪ m ≡ pr ξ (Sset ξ)))
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
      go (ξ , (ξ∈ω , q)) = ∣ ξ
        , ( subst (λ w → ⟨ ξ ∈ˢ w ⟩) (sym St.a₀≡ω) ξ∈ω
          , sym (∈-asFiber {a = p} {b = W} (D.defSet⊆A segForm p p∈) .snd) ∙ q ) ∣₁
    bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
        → ⟨ p ∈ˢ P ⟩
    bwd = PT.rec (snd (p ∈ˢ P)) go
      where
      go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × (p ≡ pr ξ (Sset ξ))) → ⟨ p ∈ˢ P ⟩
      go (ξ , (ξ∈a₀ , q)) = subst (λ w → ⟨ w ∈ˢ P ⟩) (sym q)
        (PT.rec (snd (pr ξ (Sset ξ) ∈ˢ P)) g
          (subst (λ w → ⟨ ξ ∈ˢ w ⟩) St.a₀≡ω ξ∈a₀))
        where
        g : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower k) ≡ ξ)
           → ⟨ pr ξ (Sset ξ) ∈ˢ P ⟩
        g (k , q') = subst (λ w → ⟨ w ∈ˢ P ⟩) (cong₂ pr q' (cong Sset q'))
          (subst (λ w → ⟨ w ∈ˢ P ⟩) (fib .snd)
            (subst ⟨_⟩ (sym (D.defSet-mem segForm m))
              (segForm-ok m .snd ∣ St.nk (lower k) , ( #∈ω (lower k) , fib .snd ) ∣₁)))
          where
          fib : Σ[ m ∈ ⟪ W ⟫ ]
                  (⟪ W ⟫↪ m ≡ pr (St.nk (lower k)) (Sset (St.nk (lower k))))
          fib = ∈-asFiber {a = pr (St.nk (lower k)) (Sset (St.nk (lower k)))}
            {b = W} (prξSξ∈W (St.nk (lower k)) (nk∈a₀ (lower k)))
          m : ⟪ W ⟫
          m = fib .fst

  -- The carve (T193's landing shape).  No identification, no HF.
  sucV-# : (n : ℕ) → sucV (St.nk n) ≡ St.nk (suc n)
  sucV-# n = sym (St.sucIter-∅≡# (suc n)) ∙ cong sucV (St.sucIter-∅≡# n)

  ψBody : Formula ⟪ W ⟫ 4
  ψBody = storyRen
       ∧̇ (∃̇∈ (var (suc (suc zero)))
             (KW.PK.prAt zero (suc zero) (suc (suc zero))))
       ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero))

  ψ : Formula ⟪ W ⟫ 1
  ψ = ∃̇ (∃̇ (∃̇ ψBody))

  ψ-out : (x : ⟪ W ⟫) → ⟨ (KW.ι x ∷ []) KW.⊨ᵐ ψ ⟩
        → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset ξ ⟩) ∥₁
  ψ-out x = PT.rec squash₁ s₁
    where
    s₁ : Σ[ sm ∈ KW.SM ] ⟨ (sm ∷ KW.ι x ∷ []) KW.⊨ᵐ ∃̇ (∃̇ ψBody) ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset ξ ⟩) ∥₁
    s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
      where
      s₂ : Σ[ ym ∈ KW.SM ] ⟨ (ym ∷ sm ∷ KW.ι x ∷ []) KW.⊨ᵐ ∃̇ ψBody ⟩
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset ξ ⟩) ∥₁
      s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
        where
        s₃ : Σ[ ξm ∈ KW.SM ] ⟨ (ξm ∷ ym ∷ sm ∷ KW.ι x ∷ []) KW.⊨ᵐ ψBody ⟩
           → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset ξ ⟩) ∥₁
        s₃ (ξm , (st-sat , (pr∈-sat , x∈y-sat))) = ∣ fst ξm , (ξ∈a₀ , y∈Sξ) ∣₁
          where
          δ₄ : Vec KW.SM 4
          δ₄ = ξm ∷ ym ∷ sm ∷ KW.ι x ∷ []
          st : storyW (fst sm)
          st = storyRen-ok δ₄ .fst st-sat
          h4 : KW.exactDom (fst sm)
          h4 = st .snd .snd .snd .fst
          prξy∈s : ⟨ pr (fst ξm) (fst ym) ∈ˢ fst sm ⟩
          prξy∈s = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
          x∈y : ⟨ ⟪ W ⟫↪ x ∈ˢ fst ym ⟩
          x∈y = x∈y-sat
          ξ∈ω : ⟨ fst ξm ∈ˢ ω ⟩
          ξ∈ω = exactDom-ξ∈ω (fst sm) (fst ξm) (fst ym) h4 prξy∈s
          y≡Ssetξ : fst ym ≡ Sset (fst ξm)
          y≡Ssetξ = chainValueW (fst sm) st (fst ξm) (fst ym) ξ∈ω prξy∈s
          ξ∈a₀ : ⟨ fst ξm ∈ˢ a₀ ⟩
          ξ∈a₀ = subst (λ w → ⟨ fst ξm ∈ˢ w ⟩) (sym St.a₀≡ω) ξ∈ω
          y∈Sξ : ⟨ ⟪ W ⟫↪ x ∈ˢ Sset (fst ξm) ⟩
          y∈Sξ = subst (λ w → ⟨ ⟪ W ⟫↪ x ∈ˢ w ⟩) y≡Ssetξ x∈y

  ψ-in : (x : ⟪ W ⟫)
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset ξ ⟩) ∥₁
       → ⟨ (KW.ι x ∷ []) KW.⊨ᵐ ψ ⟩
  ψ-in x = PT.rec (snd ((KW.ι x ∷ []) KW.⊨ᵐ ψ)) go
    where
    go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset ξ ⟩)
       → ⟨ (KW.ι x ∷ []) KW.⊨ᵐ ψ ⟩
    go (ξ , (ξ∈a₀ , x∈Sξ)) = PT.rec (snd ((KW.ι x ∷ []) KW.⊨ᵐ ψ)) num
      (subst (λ w → ⟨ ξ ∈ˢ w ⟩) St.a₀≡ω ξ∈a₀)
      where
      num : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower m) ≡ ξ)
          → ⟨ (KW.ι x ∷ []) KW.⊨ᵐ ψ ⟩
      num (m , q) = ∣ sm , (∣ ym , (∣ ξm , body-sat ∣₁) ∣₁) ∣₁
        where
        Sξ∈W : ⟨ Sset ξ ∈ˢ W ⟩
        Sξ∈W = subst (λ w → ⟨ Sset w ∈ˢ W ⟩) q (memberAt (lower m))
        ξ∈W : ⟨ ξ ∈ˢ W ⟩
        ξ∈W = subst (λ w → ⟨ w ∈ˢ W ⟩) q (numeral∈La₀ (lower m))
        sm ym ξm : KW.SM
        sm = KW.PK.pt (seg (lower m)) (seg∈W (lower m))
        ym = KW.PK.pt (Sset ξ) Sξ∈W
        ξm = KW.PK.pt ξ ξ∈W
        δ₄ : Vec KW.SM 4
        δ₄ = ξm ∷ ym ∷ sm ∷ KW.ι x ∷ []
        body-sat : ⟨ δ₄ KW.⊨ᵐ ψBody ⟩
        body-sat = ( st-sat , (pr∈-sat , x∈y-sat) )
          where
          st-sat : ⟨ δ₄ KW.⊨ᵐ storyRen ⟩
          st-sat = storyRen-ok δ₄ .snd (segStory (lower m))
          prξSξ∈s : ⟨ pr ξ (Sset ξ) ∈ˢ seg (lower m) ⟩
          prξSξ∈s = subst (λ w → ⟨ pr w (Sset w) ∈ˢ seg (lower m) ⟩) q
            (segTopPair (lower m))
          pr∈-sat : ⟨ δ₄ KW.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                       (KW.PK.prAt zero (suc zero) (suc (suc zero))) ⟩
          pr∈-sat = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd prξSξ∈s
          x∈y-sat : ⟨ δ₄ KW.⊨ᵐ (var (suc (suc (suc zero))) ∈̇ var (suc zero)) ⟩
          x∈y-sat = x∈Sξ

  -- The carve clause against the tower's limit union.
  carve-out : (y : S) → ⟨ y ∈ˢ D.defSet ψ ⟩ → ⟨ y ∈ˢ Sset a₀ ⟩
  carve-out y y∈ = PT.rec (snd (y ∈ˢ Sset a₀)) aStep (ψ-out m sat)
    where
    m : ⟪ W ⟫
    m = ∈-asFiber {a = y} {b = W} (D.defSet⊆A ψ y y∈) .fst
    q : ⟪ W ⟫↪ m ≡ y
    q = ∈-asFiber {a = y} {b = W} (D.defSet⊆A ψ y y∈) .snd
    sat : ⟨ (KW.ι m ∷ []) KW.⊨ᵐ ψ ⟩
    sat = subst ⟨_⟩ (D.defSet-mem ψ m)
      (subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (sym q) y∈)
    aStep : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × ⟨ ⟪ W ⟫↪ m ∈ˢ Sset ξ ⟩)
          → ⟨ y ∈ˢ Sset a₀ ⟩
    aStep (ξ , (ξ∈a₀ , x∈Sξ)) = Sset-mono {α = a₀} {β = ξ} ξ∈a₀
      y (subst (λ w → ⟨ w ∈ˢ Sset ξ ⟩) q x∈Sξ)

  carve-in : (y : S) → ⟨ y ∈ˢ Sset a₀ ⟩ → ⟨ y ∈ˢ D.defSet ψ ⟩
  carve-in y y∈S = PT.rec (snd (y ∈ˢ D.defSet ψ)) step₁
    (Sset-union-limit a₀ a₀-lim y y∈S)
    where
    step₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ a₀ ⟩ × ⟨ y ∈ˢ Sset (sucV δ) ⟩)
          → ⟨ y ∈ˢ D.defSet ψ ⟩
    step₁ (δ , (δ∈a₀ , y∈Sδ')) = PT.rec (snd (y ∈ˢ D.defSet ψ)) δNum
      (subst (λ w → ⟨ δ ∈ˢ w ⟩) St.a₀≡ω δ∈a₀)
      where
      δNum : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower m) ≡ δ)
           → ⟨ y ∈ˢ D.defSet ψ ⟩
      δNum (m , q) = subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (fib .snd)
        (subst ⟨_⟩ (sym (D.defSet-mem ψ (fib .fst)))
          (ψ-in (fib .fst) ∣ St.nk (suc (lower m))
            , ( nk∈a₀ (suc (lower m)) , y∈Sξ' ) ∣₁))
        where
        y∈W : ⟨ y ∈ˢ W ⟩
        y∈W = Ltr a₀ {x = Sset (sucV δ)} {y = y} y∈Sδ'
          (seg∈L (sucV δ) (limit-succ-mem a₀ δ a₀-lim δ∈a₀))
        fib : Σ[ x ∈ ⟪ W ⟫ ] (⟪ W ⟫↪ x ≡ y)
        fib = ∈-asFiber {a = y} {b = W} y∈W
        y∈Sξ' : ⟨ ⟪ W ⟫↪ (fib .fst) ∈ˢ Sset (St.nk (suc (lower m))) ⟩
        y∈Sξ' = subst (λ w → ⟨ ⟪ W ⟫↪ (fib .fst) ∈ˢ w ⟩)
          (cong Sset (sucV-# (lower m)))
          (subst (λ w → ⟨ ⟪ W ⟫↪ (fib .fst) ∈ˢ Sset w ⟩)
            (sym (cong sucV q))
            (subst (λ w → ⟨ w ∈ˢ Sset (sucV δ) ⟩) (sym (fib .snd)) y∈Sδ'))

  carveClause : D.defSet ψ ≡ Sset a₀
  carveClause = extensionalV (λ x → ⇔toPath (carve-out x) (carve-in x))

  carve∈𝒟ₒ : ⟨ Sset a₀ ∈ˢ 𝒟ₒ W ⟩
  carve∈𝒟ₒ = 𝒟ₒ-intro W (Sset a₀) ∣ ψ , carveClause ∣₁

  -- The landing, one stage up.
  landing : ⟨ Sset a₀ ∈ˢ Lset (sucV a₀) ⟩
  landing = 𝒟ₒ⊆Lsuc a₀ (Sset a₀) carve∈𝒟ₒ

  -- The placements through the geometry and transitivity.
  δ₀ : S
  δ₀ = sucV (sucV (sucV a₀))

  δ₀-ord : IsOrd δ₀
  δ₀-ord = suc-ord (suc-ord (suc-ord a₀-ord))

  sucVa₀∈δ₀ : ⟨ sucV a₀ ∈ˢ δ₀ ⟩
  sucVa₀∈δ₀ = δ₀-ord .fst {x = sucV (sucV a₀)} {y = sucV a₀}
    (self∈sucV (sucV a₀)) (self∈sucV (sucV (sucV a₀)))

  sucVa₀∈C : ⟨ sucV a₀ ∈ˢ C ⟩
  sucVa₀∈C = Ctr {x = Lset δ₀} {y = sucV a₀}
    (Lset-mono {α = δ₀} {β = sucV (sucV a₀)} (self∈sucV (sucV (sucV a₀)))
      (ord∈Lset-suc (sucV a₀) (suc-ord a₀-ord))) Tgeom

  P∈C : ⟨ P ∈ˢ C ⟩
  P∈C = Ctr {x = Lset δ₀} {y = P}
    (Lset-mono {α = δ₀} {β = sucV a₀} sucVa₀∈δ₀
      (𝒟ₒ⊆Lsuc a₀ P (𝒟ₒ-intro W P ∣ segForm , refl ∣₁))) Tgeom

  -- The top pair through the Kuratowski coding.
  T : S
  T = pr a₀ (Sset a₀)

  T∈Lδ₀ : ⟨ T ∈ˢ Lset δ₀ ⟩
  T∈Lδ₀ = subst (λ w → ⟨ w ∈ˢ Lset δ₀ ⟩) (sym pr≡F0)
    (Lpair (sucV (sucV a₀)) (F0 a₀ a₀) (F0 a₀ (Sset a₀)) F0aa∈L F0aS∈L)
    where
    a₀∈Lsuca₀ : ⟨ a₀ ∈ˢ Lset (sucV a₀) ⟩
    a₀∈Lsuca₀ = ord∈Lset-suc a₀ a₀-ord
    F0aa∈L : ⟨ F0 a₀ a₀ ∈ˢ Lset (sucV (sucV a₀)) ⟩
    F0aa∈L = Lpair (sucV a₀) a₀ a₀ a₀∈Lsuca₀ a₀∈Lsuca₀
    F0aS∈L : ⟨ F0 a₀ (Sset a₀) ∈ˢ Lset (sucV (sucV a₀)) ⟩
    F0aS∈L = Lpair (sucV a₀) a₀ (Sset a₀) a₀∈Lsuca₀ landing
    pr≡F0 : pr a₀ (Sset a₀) ≡ F0 (F0 a₀ a₀) (F0 a₀ (Sset a₀))
    pr≡F0 = sym (cong (λ w → ⁅ w , ⁅ a₀ , Sset a₀ ⁆ ⁆) (pair-singleton a₀))

  T∈C : ⟨ T ∈ˢ C ⟩
  T∈C = Ctr {x = Lset δ₀} {y = T} T∈Lδ₀ Tgeom

  -- The union of a stage member lands one step up.
  module UnionClosure (σ : S) (oσ : IsOrd σ) (a : S)
    (a∈ : ⟨ a ∈ˢ Lset σ ⟩) where

    union∈Lsuc : ⟨ (⋃ a) ∈ˢ Lset (sucV σ) ⟩
    union∈Lsuc = 𝒟ₒ⊆Lsuc σ (⋃ a) (𝒟ₒ-intro (Lset σ) (⋃ a) ∣ φ , defSet≡ ∣₁)
      where
      module Dσ = DefOf (Lset σ)
      Atr : isTransV (Lset σ)
      Atr = layer-trans (Lset-layer σ)
      mₐ : ⟪ Lset σ ⟫
      mₐ = ∈-asFiber {a = a} {b = Lset σ} a∈ .fst
      qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ a
      qₐ = ∈-asFiber {a = a} {b = Lset σ} a∈ .snd
      φ : Formula ⟪ Lset σ ⟫ 1
      φ = ∃̇∈ (con mₐ) (var (suc zero) ∈̇ var zero)
      defSet≡ : Dσ.defSet φ ≡ ⋃ a
      defSet≡ = extensionality (Dσ.defSet φ) (⋃ a) (sub₁ , sub₂)
        where
        sub₁ : ⟨ Dσ.defSet φ ⊆ₛ (⋃ a) ⟩
        sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ (⋃ a)))
          (λ { ((m , h) , q) →
            subst (λ w → ⟨ w ∈ₛ (⋃ a) ⟩) q
              (PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ₛ (⋃ a)))
                (λ { (v , (fv∈a , m∈ₛv)) →
                  union-ax a (⟪ Lset σ ⟫↪ m) .snd
                    ∣ fst v
                      , ( ∈∈ₛ {a = fst v} {b = a} .fst
                            (subst (λ w → ⟨ fst v ∈ˢ w ⟩) qₐ fv∈a)
                        , ∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = fst v} .fst m∈ₛv ) ∣₁ })
                (subst ⟨_⟩ (Dσ.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
          (∈∈ₛ {a = y} {b = Dσ.defSet φ} .snd y∈ₛ)
        sub₂ : ⟨ (⋃ a) ⊆ₛ Dσ.defSet φ ⟩
        sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ Dσ.defSet φ))
          (λ { (v , (v∈ₛa , y∈ₛv)) → memOf v v∈ₛa y∈ₛv })
          (union-ax a y .fst y∈ₛ)
          where
          memOf : (v : S) → ⟨ v ∈ₛ a ⟩ → ⟨ y ∈ₛ v ⟩ → ⟨ y ∈ₛ Dσ.defSet φ ⟩
          memOf v v∈ₛa y∈ₛv =
            subst (λ w → ⟨ w ∈ₛ Dσ.defSet φ ⟩) q'
              (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = Dσ.defSet φ} .fst
                (subst ⟨_⟩ (sym (Dσ.defSet-mem φ m')) sat))
            where
            v∈a = ∈∈ₛ {a = v} {b = a} .snd v∈ₛa
            y∈v = ∈∈ₛ {a = y} {b = v} .snd y∈ₛv
            v∈A = Atr {x = a} {y = v} v∈a a∈
            y∈A = Atr {x = v} {y = y} y∈v v∈A
            m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
            q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
            sat : ⟨ (Dσ.ι m' ∷ []) Dσ.⊨ᵐ φ ⟩
            sat = ∣ (v , v∈A)
                  , ( subst (λ w → ⟨ v ∈ˢ w ⟩) (sym qₐ) v∈a
                    , subst (λ w → ⟨ w ∈ˢ v ⟩) (sym q') y∈v ) ∣₁

  -- The segment P ∪ {T} in the carrier.
  seg₀ : S
  seg₀ = F5 (F0 P (F0 T T)) T

  seg∈C : ⟨ seg₀ ∈ˢ C ⟩
  seg∈C = Ctr {x = Lset (sucV (sucV (sucV δ₀)))}
    {y = seg₀} seg∈Lδ' segGeom
    where
    F0TT∈L : ⟨ F0 T T ∈ˢ Lset (sucV δ₀) ⟩
    F0TT∈L = Lpair δ₀ T T T∈Lδ₀ T∈Lδ₀
    F0PTT∈L : ⟨ F0 P (F0 T T) ∈ˢ Lset (sucV (sucV δ₀)) ⟩
    F0PTT∈L = Lpair (sucV δ₀) P (F0 T T)
      (Lset-mono {α = sucV δ₀} {β = δ₀} (self∈sucV δ₀) P∈Lδ₀) F0TT∈L
      where
      P∈Lδ₀ : ⟨ P ∈ˢ Lset δ₀ ⟩
      P∈Lδ₀ = Lset-mono {α = δ₀} {β = sucV a₀} sucVa₀∈δ₀
        (𝒟ₒ⊆Lsuc a₀ P (𝒟ₒ-intro W P ∣ segForm , refl ∣₁))
    module UC = UnionClosure (sucV (sucV δ₀)) (suc-ord (suc-ord δ₀-ord))
      (F0 P (F0 T T)) F0PTT∈L
    seg∈Lδ' : ⟨ seg₀ ∈ˢ Lset (sucV (sucV (sucV δ₀))) ⟩
    seg∈Lδ' = UC.union∈Lsuc

  -- The STEP's instantiation and the six-clause story at the segment.
  module Seg = St.Segment a₀ a₀-lim P P∈ sucVa₀∈C

  -- No member of the first limit is a limit.
  member-a₀-not-limit : (a : S) → ⟨ a ∈ˢ a₀ ⟩ → ⟨ isLimit a ⟩ → Empty.⊥
  member-a₀-not-limit a a∈a₀ lima = PT.rec Empty.isProp⊥ go
    (subst (λ w → ⟨ a ∈ˢ w ⟩) St.a₀≡ω a∈a₀)
    where
    go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (St.nk (lower m) ≡ a) → Empty.⊥
    go (m , q) = subst (λ w → ⟨ isLimit w ⟩ → Empty.⊥) q (numLim (lower m)) lima
      where
      numLim : (n : ℕ) → ⟨ isLimit (St.nk n) ⟩ → Empty.⊥
      numLim zero lima = isLimit-not-zero (St.nk zero) lima refl
      numLim (suc n) lima = isLimit-not-succ (St.nk (suc n))
        lima (St.nk n , (numeral-ord n , sucV-# n))

  -- The sixth clause: the top reading plus the empty other cases.
  segLimitClause : St.limitClause Seg.seg
  segLimitClause a b lima pr∈ z = PT.rec isPropRhsa go
    (Seg.seg∈ (pr a b) .fst pr∈)
    where
    rhs : S → Type (ℓ-suc ℓ)
    rhs i = ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ i ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
    isPropRhsa : isProp (⟨ z ∈ˢ b ⟩ ⟷ rhs a)
    isPropRhsa = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → snd (z ∈ˢ b)))
    go : ⟨ pr a b ∈ˢ P ⟩ ⊎ (pr a b ≡ T) → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
    go (inl p∈P) = Empty.rec {A = ⟨ z ∈ˢ b ⟩ ⟷ rhs a} noLimit
      where
      noLimit : Empty.⊥
      noLimit = PT.rec Empty.isProp⊥ aStep (P∈ (pr a b) .fst p∈P)
        where
        aStep : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩ × (pr a b ≡ pr ξ (Sset ξ))) → Empty.⊥
        aStep (ξ , (ξ∈a₀ , q)) = member-a₀-not-limit a a∈a₀ lima
          where
          a∈a₀ : ⟨ a ∈ˢ a₀ ⟩
          a∈a₀ = subst (λ w → ⟨ w ∈ˢ a₀ ⟩) (sym (pr-inj q .fst)) ξ∈a₀
    go (inr q) = (fwd , bwd)
      where
      a≡a₀ : a ≡ a₀
      a≡a₀ = pr-inj q .fst
      b≡Sa₀ : b ≡ Sset a₀
      b≡Sa₀ = pr-inj q .snd
      fwd : ⟨ z ∈ˢ b ⟩ → rhs a
      fwd z∈b = PT.map go' (Seg.segLimit₀ z .fst
        (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Sa₀ z∈b))
        where
        go' : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
            → Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                 × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
        go' (ξ , (ξ∈a₀ , rest)) = ξ , (subst (λ w → ⟨ ξ ∈ˢ w ⟩) (sym a≡a₀) ξ∈a₀ , rest)
      bwd : rhs a → ⟨ z ∈ˢ b ⟩
      bwd = PT.rec (snd (z ∈ˢ b)) go'
        where
        go' : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
            → ⟨ z ∈ˢ b ⟩
        go' (ξ , (ξ∈a , rest)) = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Sa₀)
          (Seg.segLimit₀ z .snd (PT.map rest' rest))
          where
          rest' : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩)
                → Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ a₀ ⟩
                     × ∥ Σ[ w ∈ S ] (⟨ pr ξ' w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
          rest' (w , (pr∈ , z∈w)) =
            ξ , (subst (λ w' → ⟨ ξ ∈ˢ w' ⟩) a≡a₀ ξ∈a , ∣ w , (pr∈ , z∈w) ∣₁)

  segmentStory : St.story Seg.seg
  segmentStory = ( Seg.segPairhood , ( Seg.segSingleValued
    , ( Seg.segZeroClause , ( Seg.segDom₀
      , ( Seg.segSuccClause , segLimitClause ) ) ) ) )

  -- The STEP's conclusion at the first limit.
  firstStep : ⟨ Sset a₀ ∈ˢ Lset (sucV a₀) ⟩
  firstStep = landing
```

<!--en-->
## The general STEP at a variable limit
<!--zh-->
## 变量极限处的通用 STEP
<!--/-->

<!--en-->
Block A writes the STEP once at a variable limit γ, with the induction
hypothesis as a module parameter. The memberships row comes from Bridge's
lifted `Below` module (T232/T233); the witness layer is the T222 slice at
`Lset γ`; the sixth clause is T128's gate ported to the witness carrier;
the story assembly is the T226 clause list; the general chain is T204's
shape on the S-side. The carried sequence, the decode and the carve land
in this module as the pieces check.
<!--zh-->
A 块把 STEP 在变量极限 γ 处一次写出，归纳假设是模块参数。隶属行来自 Bridge 已提升的 `Below` 模块 (T232/T233)；见证层是 `Lset γ` 处的 T222 切片；第六子句是移植到见证载体处的 T128 门；故事装配是 T226 的子句表；通用链是 S 侧的 T204 形状。载运序列、解码与刻划随各件通过检查逐件落入本模块。
<!--/-->

```agda
module Stepγ
  (γ : S) (limγ : ⟨ isLimit γ ⟩)
  (IH : (β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩)
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
  (Tgeom : ⟨ Lset (sucV (sucV (sucV γ))) ∈ˢ C ⟩)
  (segGeom : ⟨ Lset (sucV (sucV (sucV (sucV (sucV (sucV γ)))))) ∈ˢ C ⟩)
  where

  -- The empty set lies below every limit ordinal, by ordinal trichotomy.
  ∅∈γ : ⟨ ∅ ∈ˢ γ ⟩
  ∅∈γ = go (ord-tri ∅ ∅-ord γ (isLimit-ord γ limγ))
    where
    go : ⟨ ∅ ∈ˢ γ ⟩ ⊎ ((∅ ≡ γ) ⊎ ⟨ γ ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ γ ⟩
    go (inl h) = h
    go (inr (inl e)) = Empty.rec (isLimit-not-zero γ limγ (sym e))
    go (inr (inr h)) = Empty.rec (∅-empty γ (∈∈ₛ {a = γ} {b = ∅} .fst h))

  -- The memberships row at γ, through Bridge's lifted Below module
  -- (T232/T233): Sset ξ ∈ Lset γ for every ξ ∈ γ.  The slot discharges
  -- the ∅ ∈ Lset γ parameter of the row's induction.
  slot∈L : (α : S) → ⟨ isLimit α ⟩ → ⟨ ∅ ∈ˢ Lset α ⟩
  slot∈L α limα = ∅∈Lset α limα (∅∈at α limα)
    where
    ∅∈at : (α : S) → ⟨ isLimit α ⟩ → ⟨ ∅ ∈ˢ α ⟩
    ∅∈at α limα = go (ord-tri ∅ ∅-ord α (isLimit-ord α limα))
      where
      go : ⟨ ∅ ∈ˢ α ⟩ ⊎ ((∅ ≡ α) ⊎ ⟨ α ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ α ⟩
      go (inl h) = h
      go (inr (inl e)) = Empty.rec (isLimit-not-zero α limα (sym e))
      go (inr (inr h)) = Empty.rec (∅-empty α (∈∈ₛ {a = α} {b = ∅} .fst h))

  below-limγ : (β : S) → IsOrd β → ⟨ isLimit β ⟩ → ⟨ β ∈ˢ γ ⟩
             → ⟨ Sset β ∈ˢ Lset γ ⟩
  below-limγ β ordβ limβ β∈γ =
    Lset-mono {α = γ} {β = sucV β} (limit-succ-mem γ β limγ β∈γ) (IH β β∈γ limβ)

  module B = Below γ limγ StepGraph.stepSet∈L StepGraph.values∈L slot∈L below-limγ

  mem∈L : (ξ : S) → ⟨ ξ ∈ˢ γ ⟩ → ⟨ Sset ξ ∈ˢ Lset γ ⟩
  mem∈L ξ ξ∈γ = B.rudBelow ξ (limit-mem-ord γ limγ ξ ξ∈γ) ξ∈γ .snd

  -- The witness carrier: the stage at the limit.
  W : S
  W = Lset γ

  Wtr : isTransV W
  Wtr = layer-trans (Lset-layer γ)

  ∅∈W : ⟨ ∅ ∈ˢ W ⟩
  ∅∈W = ∅∈Lset γ limγ ∅∈γ

  mA : ⟪ W ⟫
  mA = ∈-asFiber {a = ∅} {b = W} ∅∈W .fst

  qA : ⟪ W ⟫↪ mA ≡ ∅
  qA = ∈-asFiber {a = ∅} {b = W} ∅∈W .snd

  -- The step closure at the witness carrier (the T222 slice).
  stepInW : (c : S) → ⟨ c ∈ˢ W ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ W ⟩
  stepInW c c∈ v v∈step = PT.rec (snd (v ∈ˢ W)) go (step-out c v v∈step)
    where
    go : StepArm c v → ⟨ v ∈ˢ W ⟩
    go (arm-member v∈c) = Ltr γ {x = c} {y = v} v∈c c∈
    go (arm-self e) = subst (λ w → ⟨ w ∈ˢ W ⟩) (sym e) c∈
    go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ W)) both
      (Lstage₂ γ limγ c ∅ c∈ ∅∈W)
      where
      both : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ c ∈ˢ Lset ξ ⟩ × ⟨ ∅ ∈ˢ Lset ξ ⟩)
           → ⟨ v ∈ˢ W ⟩
      both (ξ , (ξ∈γ , c∈ξ , A∈ξ)) =
        Lset-mono {α = γ} {β = sucV (suc⁴ ξ)}
          (limit-succ-mem γ (suc⁴ ξ) limγ (suc⁴∈ γ ξ limγ ξ∈γ))
          (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ξ)) ⟩) (sym e)
            (Lval (suc⁴ ξ) (suc⁴-up ξ ∅ A∈ξ) i a b a∈ b∈
              (StepGraph.values∈L c ξ c∈ξ i a b sa sb)))
        where
        argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ξ ⟩
        argIn x (inl h) = Ltr ξ h c∈ξ
        argIn x (inr e') = subst (λ w → ⟨ w ∈ˢ Lset ξ ⟩) (sym e') c∈ξ
        a∈ : ⟨ a ∈ˢ Lset (suc⁴ ξ) ⟩
        a∈ = suc⁴-up ξ a (argIn a sa)
        b∈ : ⟨ b ∈ˢ Lset (suc⁴ ξ) ⟩
        b∈ = suc⁴-up ξ b (argIn b sb)

  -- The graph layer and the step clause at the witness carrier.
  module WL = StepGraph.Layer W Wtr mA qA ∅∈W
  module WB = WL.BigOr WL.graphOf

  import L.Rud.StepStory {ℓ} lem ∅ W Wtr as StepStoryW
  module WCl = StepStoryW.Clause stepInW WL.graphOf WL.graph-out WL.graph-in
    WB.bigOr WB.bigOr-in WB.bigOr-out WL.eqFrame WL.eqFrame-ok

  -- The story at the witness carrier, instantiated with the graph layer.
  module St = Story W Wtr stepInW WL.graphOf WL.graph-out WL.graph-in
    WB.bigOr WB.bigOr-in WB.bigOr-out WL.eqFrame WL.eqFrame-ok

  module KW = LevelKit W Wtr

  -- The sixth clause, T128's gate ported to W: the value at a limit index
  -- is the pointwise union of the values below, stated at the small index
  -- (R-35).  The formula and the two-way decode are T128's, stated at the
  -- witness carrier; the level-formula tower's limit clause is the
  -- element-valued form and does not match the set-valued story here.
  limAt : Formula ⟪ W ⟫ 4
  limAt = KW.isOrdAt (suc zero)
       ∧̇ (∃̇∈ (var (suc zero)) (var zero ≐ var zero))
       ∧̇ (∀̇∈ (var (suc zero))
             (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero)))

  pairIn : Formula ⟪ W ⟫ 4
  pairIn = ∃̇∈ (var (suc (suc zero)))
             (KW.PK.prAt zero (suc (suc zero)) (suc zero))

  inner7 : Formula ⟪ W ⟫ 7
  inner7 = ∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
             (KW.PK.prAt zero (suc (suc zero)) (suc zero)
                ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero)))

  unionRHS : Formula ⟪ W ⟫ 5
  unionRHS = ∃̇∈ (var (suc (suc zero))) (∃̇ inner7)

  limitConc : Formula ⟪ W ⟫ 4
  limitConc = ∀̇ ( (var zero ∈̇ var (suc zero) ⇒̇ unionRHS)
               ∧̇ (unionRHS ⇒̇ var zero ∈̇ var (suc zero)) )

  limitBody : Formula ⟪ W ⟫ 4
  limitBody = (limAt ∧̇ pairIn) ⇒̇ limitConc

  limitForm : Formula ⟪ W ⟫ 2
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

  -- The limit atom's two-way decode at the witness carrier.
  limAt-ok : (δ : Vec KW.SM 4) → ⟨ δ KW.⊨ᵐ limAt ⟩
           ⟷ ⟨ isLimit (fst (lookup (suc zero) δ)) ⟩
  limAt-ok δ = (out , bwd)
    where
    valA : S
    valA = fst (lookup (suc zero) δ)

    out : ⟨ δ KW.⊨ᵐ limAt ⟩ → ⟨ isLimit valA ⟩
    out (ord-sat , (ne-sat , cl-sat)) = ( ordA , nz , ns )
      where
      ordA : IsOrd valA
      ordA = KW.isOrd-out (suc zero) δ ord-sat
      nz : (valA ≡ ∅) → Empty.⊥
      nz e = PT.rec Empty.isProp⊥ nzGo ne-sat
        where
        nzGo : Σ[ ξm ∈ KW.SM ] (⟨ fst ξm ∈ˢ valA ⟩
                            × ⟨ (ξm ∷ δ) KW.⊨ᵐ (var zero ≐ var zero) ⟩)
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
        β∈W : ⟨ β ∈ˢ W ⟩
        β∈W = Wtr {x = valA} {y = β} β∈a (snd (lookup (suc zero) δ))
        βm : KW.SM
        βm = KW.PK.pt β β∈W
        nsGo : Σ[ ηm ∈ KW.SM ] (⟨ fst ηm ∈ˢ valA ⟩ × ⟨ β ∈ˢ fst ηm ⟩)
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

    bwd : ⟨ isLimit valA ⟩ → ⟨ δ KW.⊨ᵐ limAt ⟩
    bwd lim = ( ord-sat , (ne-sat , cl-sat) )
      where
      ordA : IsOrd valA
      ordA = isLimit-ord valA lim
      ord-sat : ⟨ δ KW.⊨ᵐ KW.isOrdAt (suc zero) ⟩
      ord-sat = KW.isOrd-in (suc zero) δ ordA
      ne-sat : ⟨ δ KW.⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero) ⟩
      ne-sat = PT.rec (snd (δ KW.⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero)))
        go (nonemptyFromLim valA lim)
        where
        go : Σ[ ξ ∈ S ] ⟨ ξ ∈ˢ valA ⟩
           → ⟨ δ KW.⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero) ⟩
        go (ξ , ξ∈a) = ∣ ξm , (ξ∈a , refl) ∣₁
          where
          ξm : KW.SM
          ξm = KW.PK.pt ξ (Wtr {x = valA} {y = ξ} ξ∈a (snd (lookup (suc zero) δ)))
      cl-sat : ⟨ δ KW.⊨ᵐ ∀̇∈ (var (suc zero))
                  (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero)) ⟩
      cl-sat ξm ξ∈a = PT.rec
        (snd ((ξm ∷ δ) KW.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                   (var (suc zero) ∈̇ var zero)))
        go (closedFromLim valA lim (fst ξm) ξ∈a)
        where
        go : Σ[ η ∈ S ] (⟨ η ∈ˢ valA ⟩ × ⟨ fst ξm ∈ˢ η ⟩)
           → ⟨ (ξm ∷ δ) KW.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                 (var (suc zero) ∈̇ var zero) ⟩
        go (η , (η∈a , ξ∈η)) = ∣ ηm , (η∈a , ξ∈η) ∣₁
          where
          ηm : KW.SM
          ηm = KW.PK.pt η (Wtr {x = valA} {y = η} η∈a (snd (lookup (suc zero) δ)))

  -- The union reading's two-way decode at arity 5 (T128's, ported).
  unionRHS-ok : (δ : Vec KW.SM 5) → ⟨ δ KW.⊨ᵐ unionRHS ⟩
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

    out : ⟨ δ KW.⊨ᵐ unionRHS ⟩
        → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
    out sat = PT.rec squash₁ step₁ sat
      where
      step₁ : Σ[ ξm ∈ KW.SM ] (⟨ fst ξm ∈ˢ valA ⟩
            × ⟨ (ξm ∷ δ) KW.⊨ᵐ ∃̇ inner7 ⟩)
            → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                 × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
      step₁ (ξm , (ξ∈a , rest)) = PT.rec squash₁ step₂ rest
        where
        step₂ : Σ[ wm ∈ KW.SM ] ⟨ (wm ∷ ξm ∷ δ) KW.⊨ᵐ inner7 ⟩
              → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                   × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
        step₂ (wm , wm-sat) = PT.rec squash₁ step₃ wm-sat
          where
          step₃ : Σ[ pm ∈ KW.SM ] (⟨ fst pm ∈ˢ valF ⟩
                × ⟨ (pm ∷ wm ∷ ξm ∷ δ) KW.⊨ᵐ
                     (KW.PK.prAt zero (suc (suc zero)) (suc zero)
                        ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero))) ⟩)
                → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                     × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
          step₃ (pm , (pm∈f , (pr-sat , z∈w-sat))) =
            ∣ fst ξm , ( ξ∈a , ∣ fst wm , ( prξw∈f , z∈w ) ∣₁ ) ∣₁
            where
            p≡prξw : fst pm ≡ pr (fst ξm) (fst wm)
            p≡prξw = KW.PK.prAt-out zero (suc (suc zero)) (suc zero)
              (pm ∷ wm ∷ ξm ∷ δ) pr-sat
            prξw∈f : ⟨ pr (fst ξm) (fst wm) ∈ˢ valF ⟩
            prξw∈f = subst (λ t → ⟨ t ∈ˢ valF ⟩) p≡prξw pm∈f
            z∈w : ⟨ valZ ∈ˢ fst wm ⟩
            z∈w = z∈w-sat

    bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
        → ⟨ δ KW.⊨ᵐ unionRHS ⟩
    bwd h = PT.rec (snd (δ KW.⊨ᵐ unionRHS)) step₁ h
      where
      step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁)
            → ⟨ δ KW.⊨ᵐ unionRHS ⟩
      step₁ (ξ , (ξ∈a , rest)) = PT.rec (snd (δ KW.⊨ᵐ unionRHS)) step₂ rest
        where
        ξm : KW.SM
        ξm = KW.PK.pt ξ (Wtr {x = valA} {y = ξ} ξ∈a
          (snd (lookup (suc (suc zero)) δ)))
        step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩)
              → ⟨ δ KW.⊨ᵐ unionRHS ⟩
        step₂ (w , (pw∈f , z∈w)) = ∣ ξm , (ξ∈a , inner∃) ∣₁
          where
          w∈W : ⟨ w ∈ˢ W ⟩
          w∈W = KW.PM.pair-right {a = ξ} {b = w}
            (Wtr {x = valF} {y = pr ξ w} pw∈f
              (snd (lookup (suc (suc (suc zero))) δ)))
          wm : KW.SM
          wm = KW.PK.pt w w∈W
          pr∈W : ⟨ pr ξ w ∈ˢ W ⟩
          pr∈W = Wtr {x = valF} {y = pr ξ w} pw∈f
            (snd (lookup (suc (suc (suc zero))) δ))
          pm : KW.SM
          pm = KW.PK.pt (pr ξ w) pr∈W
          pr-sat : ⟨ (pm ∷ wm ∷ ξm ∷ δ) KW.⊨ᵐ
                     KW.PK.prAt zero (suc (suc zero)) (suc zero) ⟩
          pr-sat = KW.PK.prAt-in zero (suc (suc zero)) (suc zero)
            (pm ∷ wm ∷ ξm ∷ δ) refl
          z∈w-sat : ⟨ (pm ∷ wm ∷ ξm ∷ δ) KW.⊨ᵐ
                      (var (suc (suc (suc zero))) ∈̇ var (suc zero)) ⟩
          z∈w-sat = z∈w
          inner : ⟨ (wm ∷ ξm ∷ δ) KW.⊨ᵐ inner7 ⟩
          inner = ∣ pm , (pw∈f , (pr-sat , z∈w-sat)) ∣₁
          inner∃ : ⟨ (ξm ∷ δ) KW.⊨ᵐ ∃̇ inner7 ⟩
          inner∃ = ∣ wm , inner ∣₁

  -- The sixth clause's two-way decode at the standing arity (T128's,
  -- ported): the object formula is satisfied exactly when the meta-level
  -- limit clause holds at the witness.
  limit-ok : (f : KW.SM) (x : ⟪ W ⟫) → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ limitForm ⟩
           ⟷ St.limitClause (fst f)
  limit-ok f x = (out , bwd)
    where
    δ₂ : Vec KW.SM 2
    δ₂ = f ∷ KW.ι x ∷ []

    out : ⟨ δ₂ KW.⊨ᵐ limitForm ⟩ → St.limitClause (fst f)
    out h a b lim ab∈f z = (fwd , bwd)
      where
      a∈W : ⟨ a ∈ˢ W ⟩
      a∈W = KW.PM.pair-left {a = a} {b = b}
        (Wtr {x = fst f} {y = pr a b} ab∈f (snd f))
      b∈W : ⟨ b ∈ˢ W ⟩
      b∈W = KW.PM.pair-right {a = a} {b = b}
        (Wtr {x = fst f} {y = pr a b} ab∈f (snd f))
      am : KW.SM
      am = KW.PK.pt a a∈W
      bm : KW.SM
      bm = KW.PK.pt b b∈W
      body-sat : ⟨ (bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ limitBody ⟩
      body-sat = h am bm
      conc-sat : ⟨ (bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ limitConc ⟩
      conc-sat = body-sat (limAt-sat , pairIn-sat)
        where
        limAt-sat : ⟨ (bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ limAt ⟩
        limAt-sat = limAt-ok (bm ∷ am ∷ f ∷ KW.ι x ∷ []) .snd lim
        pairIn-sat : ⟨ (bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ pairIn ⟩
        pairIn-sat = KW.pair∈ (suc (suc zero)) (suc zero) zero
          (bm ∷ am ∷ f ∷ KW.ι x ∷ []) .snd ab∈f
      fwd : ⟨ z ∈ˢ b ⟩
          → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
               × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
      fwd z∈b = unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ KW.ι x ∷ []) .fst
        (conc-sat zm .fst z∈b)
        where
        z∈W : ⟨ z ∈ˢ W ⟩
        z∈W = Wtr {x = b} {y = z} z∈b b∈W
        zm : KW.SM
        zm = KW.PK.pt z z∈W
      bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
              × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
          → ⟨ z ∈ˢ b ⟩
      bwd hz = conc-sat zm .snd
        (unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ KW.ι x ∷ []) .snd hz)
        where
        z∈W : ⟨ z ∈ˢ W ⟩
        z∈W = PT.rec (snd (z ∈ˢ W)) step₁ hz
          where
          step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                → ⟨ z ∈ˢ W ⟩
          step₁ (ξ , (ξ∈a , rest)) = PT.rec (snd (z ∈ˢ W)) step₂ rest
            where
            step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) → ⟨ z ∈ˢ W ⟩
            step₂ (w , (pw∈f , z∈w)) = Wtr {x = w} {y = z} z∈w w∈W
              where
              w∈W : ⟨ w ∈ˢ W ⟩
              w∈W = KW.PM.pair-right {a = ξ} {b = w}
                (Wtr {x = fst f} {y = pr ξ w} pw∈f (snd f))
        zm : KW.SM
        zm = KW.PK.pt z z∈W

    bwd : St.limitClause (fst f) → ⟨ δ₂ KW.⊨ᵐ limitForm ⟩
    bwd lc am bm = body-sat
      where
      body-sat : ⟨ (bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ limitBody ⟩
      body-sat (limAt-sat , pairIn-sat) = conc-sat
        where
        lim : ⟨ isLimit (fst am) ⟩
        lim = limAt-ok (bm ∷ am ∷ f ∷ KW.ι x ∷ []) .fst limAt-sat
        ab∈f : ⟨ pr (fst am) (fst bm) ∈ˢ fst f ⟩
        ab∈f = KW.pair∈ (suc (suc zero)) (suc zero) zero
          (bm ∷ am ∷ f ∷ KW.ι x ∷ []) .fst pairIn-sat
        conc-sat : ⟨ (bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ limitConc ⟩
        conc-sat zm = ( fwd , back )
          where
          fwd : ⟨ fst zm ∈ˢ fst bm ⟩
              → ⟨ (zm ∷ bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ unionRHS ⟩
          fwd z∈b = unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ KW.ι x ∷ []) .snd
            (lc (fst am) (fst bm) lim ab∈f (fst zm) .fst z∈b)
          back : ⟨ (zm ∷ bm ∷ am ∷ f ∷ KW.ι x ∷ []) KW.⊨ᵐ unionRHS ⟩
               → ⟨ fst zm ∈ˢ fst bm ⟩
          back rhssat = lc (fst am) (fst bm) lim ab∈f (fst zm) .snd
            (unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ KW.ι x ∷ []) .fst rhssat)

  limit-out : (f : KW.SM) (x : ⟪ W ⟫) → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ limitForm ⟩
            → St.limitClause (fst f)
  limit-out f x = limit-ok f x .fst

  limit-in : (f : KW.SM) (x : ⟪ W ⟫) → St.limitClause (fst f)
           → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ limitForm ⟩
  limit-in f x = limit-ok f x .snd

  -- The six-clause story at the witness carrier, assembled from the kit,
  -- the step clause and the sixth limit clause (T226's clause list; the
  -- sixth clause is T128's gate, not the level-formula tower's).
  storyWClauses : KW.StoryClauses
  storyWClauses = KW.mkClause KW.pairhood KW.pairForm KW.pairhood-out KW.pairhood-in KW.∷₊
                  KW.mkClause KW.singleValued KW.singleForm KW.single-out KW.single-in KW.∷₊
                  KW.mkClause KW.zeroClause KW.zeroForm KW.zero-out KW.zero-in KW.∷₊
                  KW.mkClause KW.exactDom KW.exactDomForm KW.exactDom-out KW.exactDom-in KW.∷₊
                  KW.clauseOk WCl.succClause WCl.succForm WCl.succ-ok KW.∷₊
                  KW.clauseOk St.limitClause limitForm limit-ok KW.∷₊ KW.end

  storyW : S → Type (ℓ-suc ℓ)
  storyW = KW.storyCl storyWClauses

  storyFormW : Formula ⟪ W ⟫ 2
  storyFormW = KW.storyForm storyWClauses

  storyW-out : (f : KW.SM) (x : ⟪ W ⟫)
             → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW ⟩ → storyW (fst f)
  storyW-out = KW.story-out storyWClauses

  storyW-in : (f : KW.SM) (x : ⟪ W ⟫)
            → storyW (fst f) → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW ⟩
  storyW-in = KW.story-in storyWClauses

  storyW-ok : (f : KW.SM) (x : ⟪ W ⟫)
            → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW ⟩ ⟷ storyW (fst f)
  storyW-ok = KW.story-ok storyWClauses

  -- The general chain (T204's shape, S-side): a six-clause story's value
  -- at an index a ∈ γ is forced to Sset a, by ordinal induction on a.
  chain : (f : S) → storyW f → (a x : S) → ⟨ a ∈ˢ γ ⟩
        → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Sset a
  chain f st a x a∈γ ax∈f = ∈-induction {P = P} indStep a a∈γ x ax∈f
    where
    P : S → Type (ℓ-suc ℓ)
    P b = ⟨ b ∈ˢ γ ⟩ → (x : S) → ⟨ pr b x ∈ˢ f ⟩ → x ≡ Sset b
    indStep : (b : S) → ((y : S) → y ∈ᵗ b → P y) → P b
    indStep b IH b∈γ x bx∈f = go (ord-case b (limit-mem-ord γ limγ b b∈γ)) x bx∈f
      where
      go : (b ≡ ∅) ⊎ (⟨ isSucc b ⟩ ⊎ ⟨ isLimit b ⟩) → (x : S)
         → ⟨ pr b x ∈ˢ f ⟩ → x ≡ Sset b
      go (inl z) x px = subst (λ w → x ≡ Sset w) (sym z) (x≡∅ ∙ sym Sset-zero)
        where
        px' : ⟨ pr ∅ x ∈ˢ f ⟩
        px' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) z px
        x≡∅ : x ≡ ∅
        x≡∅ = PT.rec (setIsSet x ∅) zStep (st .snd .snd .fst)
          where
          zStep : Σ[ a ∈ S ]
                   ( ((y : S) → ⟨ y ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ f ⟩ ) → x ≡ ∅
          zStep (a , (emp , aa∈f)) = st .snd .fst ∅ x ∅ px' pr∅∅
            where
            a≡∅ : a ≡ ∅
            a≡∅ = extensionalV (λ z → ⇔toPath
              (λ z∈a → Empty.rec (emp z z∈a))
              (λ z∈∅ → Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅))))
            pr∅∅ : ⟨ pr ∅ ∅ ∈ˢ f ⟩
            pr∅∅ = subst (λ w → ⟨ pr w w ∈ˢ f ⟩) a≡∅ aa∈f
      go (inr (inl (c , ordC , sc≡b))) x px = subst (λ w → x ≡ Sset w) sc≡b
        (succX ∙ sym (Sset-suc c))
        where
        c∈b : ⟨ c ∈ˢ b ⟩
        c∈b = subst (λ w → ⟨ c ∈ˢ w ⟩) sc≡b (self∈sucV c)
        c∈γ : ⟨ c ∈ˢ γ ⟩
        c∈γ = isLimit-ord γ limγ .fst {x = b} {y = c} c∈b b∈γ
        px' : ⟨ pr (sucV c) x ∈ˢ f ⟩
        px' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) (sym sc≡b) px
        succX : x ≡ step (Sset c)
        succX = PT.rec (setIsSet x (step (Sset c))) δStep
          (st .snd .snd .snd .fst)
          where
          δStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ W ⟩ × IsOrd δ
                   × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
                   × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
                → x ≡ step (Sset c)
          δStep (δ , (δ∈u , ordδ , in-dir , out-dir)) =
            PT.rec (setIsSet x (step (Sset c))) cStep (in-dir c c∈δ)
            where
            suc∈δ : ⟨ sucV c ∈ˢ δ ⟩
            suc∈δ = out-dir (sucV c) ∣ x , px' ∣₁
            c∈δ : ⟨ c ∈ˢ δ ⟩
            c∈δ = ordδ .fst {x = sucV c} {y = c} (self∈sucV c) suc∈δ
            cStep : Σ[ w ∈ S ] ⟨ pr c w ∈ˢ f ⟩ → x ≡ step (Sset c)
            cStep (w , pcw) = st .snd .snd .snd .snd .fst c (Sset c) x prcL px'
              where
              prcL : ⟨ pr c (Sset c) ∈ˢ f ⟩
              prcL = subst (λ w' → ⟨ pr c w' ∈ˢ f ⟩) (IH c c∈b c∈γ w pcw) pcw
      go (inr (inr limB)) x px = ext-⊆ x⊆S S⊆x
        where
        x⊆S : x ⊆ Sset b
        x⊆S z z∈x = PT.rec (snd (z ∈ˢ Sset b)) step₁
          (st .snd .snd .snd .snd .snd b x limB px z .fst z∈x)
          where
          step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ b ⟩
                × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                → ⟨ z ∈ˢ Sset b ⟩
          step₁ (ξ , (ξ∈b , rest)) = PT.rec (snd (z ∈ˢ Sset b)) step₂ rest
            where
            ξ∈γ : ⟨ ξ ∈ˢ γ ⟩
            ξ∈γ = isLimit-ord γ limγ .fst {x = b} {y = ξ} ξ∈b b∈γ
            step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩)
                  → ⟨ z ∈ˢ Sset b ⟩
            step₂ (w , (pw , z∈w)) = Sset-mono {α = b} {β = ξ} ξ∈b z
              (subst (λ w' → ⟨ z ∈ˢ w' ⟩) (IH ξ ξ∈b ξ∈γ w pw) z∈w)
        S⊆x : Sset b ⊆ x
        S⊆x z z∈S = PT.rec (snd (z ∈ˢ x)) step₁
          (Sset-union-limit b limB z z∈S)
          where
          step₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ b ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
                → ⟨ z ∈ˢ x ⟩
          step₁ (δ , (δ∈b , z∈Ssucδ)) =
            PT.rec (snd (z ∈ˢ x)) step₂ (st .snd .snd .snd .fst)
            where
            δ'∈b : ⟨ sucV δ ∈ˢ b ⟩
            δ'∈b = limit-succ-mem b δ limB δ∈b
            step₂ : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ W ⟩ × IsOrd δ₀
                     × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩
                          → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
                     × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁
                          → ⟨ a ∈ˢ δ₀ ⟩) ) → ⟨ z ∈ˢ x ⟩
            step₂ (δ₀ , (δ₀∈u , ordδ₀ , in-dir , out-dir)) =
              PT.rec (snd (z ∈ˢ x)) step₃ (in-dir (sucV δ) δ'∈δ₀)
              where
              b∈δ₀ : ⟨ b ∈ˢ δ₀ ⟩
              b∈δ₀ = out-dir b ∣ x , px ∣₁
              δ'∈δ₀ : ⟨ sucV δ ∈ˢ δ₀ ⟩
              δ'∈δ₀ = ordδ₀ .fst {x = b} {y = sucV δ} δ'∈b b∈δ₀
              step₃ : Σ[ w ∈ S ] ⟨ pr (sucV δ) w ∈ˢ f ⟩ → ⟨ z ∈ˢ x ⟩
              step₃ (w , pδ'w) =
                st .snd .snd .snd .snd .snd b x limB px z .snd
                ∣ sucV δ , (δ'∈b , ∣ Sset (sucV δ) , (pδ'L , z∈Ssucδ) ∣₁) ∣₁
                where
                δ'∈γ : ⟨ sucV δ ∈ˢ γ ⟩
                δ'∈γ = isLimit-ord γ limγ .fst {x = b} {y = sucV δ} δ'∈b b∈γ
                pδ'L : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ f ⟩
                pδ'L = subst (λ w' → ⟨ pr (sucV δ) w' ∈ˢ f ⟩)
                  (IH (sucV δ) δ'∈b δ'∈γ w pδ'w) pδ'w
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
