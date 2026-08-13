{-# OPTIONS --cubical --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import L.Constructible using ( isTransV )

module ProbeT258NoConv {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (C : V ℓ) (Ctr : isTransV C) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; _∧̇_; ∃̇_; ∃̇∈; _∈̇_; var; con )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl; ∈-induction )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl; pair-singleton )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; Lset-layer; layer-trans; 𝒟ₒ; 𝒟ₒ-intro )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using
  ( ∅-ord; numeral-mem; suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; isLimit-not-zero; isSucc; limit-mem-ord; ord-case )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( +ω; +ω-limit; +ω-in; +ω-out; +ω-ord; sucIter )
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
  ; Lstage; Lstage₂; Lval; suc⁴∈; suc⁴-up; ∅∈Lset; module Below )
open import L.TowerKit {ℓ} lem ∅ using ( Lpair; Ltr; 𝒟ₒ⊆Lsuc; suc⁴ )
import L.Rud.StepGraph {ℓ} lem ∅ as StepGraph
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.FinData.Base using ( Fin )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Functions.Logic as Logic
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Foundations.Prelude using ( isProp→PathP; PathP )
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

  -- The STEP's conclusion at the first limit: the theorem's application
  -- at a₀, the same content as wall₁.  The type survives the retirement
  -- of the a₀ Step module.
  firstStep : ⟨ Sset a₀ ∈ˢ Lset (sucV a₀) ⟩
  firstStep = wall₁

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
  -- the shared Limit module of L.Rud.StepStory defines it once; nothing
  -- in it names a concrete carrier (src/ProbeT128.agda:143-147).
  module Lim = StepStoryA.Limit
  limitClause : S → Type (ℓ-suc ℓ)
  limitClause = Lim.limitClause

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

  -- The sixth clause, T128's gate ported to W, instantiated from the
  -- carrier-generic Limit module of L.Rud.StepStory.  The meta-level
  -- clause is the shared module's, re-exported by the Story module; the
  -- formula and the two-way decode are the shared module's, stated at the
  -- witness carrier.  The open keeps the exported names and shapes the
  -- hand-written port had.
  module Lim = StepStoryW.Limit
  open Lim public

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

  -- The segment membership disjunction, carrier-free: a member of
  -- F5 (F0 P (F0 T T)) T is a member of P or the top pair.
  seg∈gen : (P T x : S) → ⟨ x ∈ˢ F5 (F0 P (F0 T T)) T ⟩
          ⟷ ∥ (⟨ x ∈ˢ P ⟩ ⊎ (x ≡ T)) ∥₁
  seg∈gen P T x = (out , bwd)
    where
    RHS : Type (ℓ-suc ℓ)
    RHS = ∥ (⟨ x ∈ˢ P ⟩ ⊎ (x ≡ T)) ∥₁
    out : ⟨ x ∈ˢ F5 (F0 P (F0 T T)) T ⟩ → RHS
    out h = PT.rec squash₁ o₂ (F5-spec (F0 P (F0 T T)) T x .fst h)
      where
      o₂ : Σ[ v ∈ S ] ⟨ v ∈ˢ F0 P (F0 T T) ⊓ x ∈ˢ v ⟩ → RHS
      o₂ (v , (v∈F0 , x∈v)) = PT.rec squash₁ o₃
        (F0-spec P (F0 T T) v .fst v∈F0)
        where
        o₃ : ⟨ v ≡ₕ P ⟩ ⊎ ⟨ v ≡ₕ F0 T T ⟩ → RHS
        o₃ (inl v≡P) = ∣ inl (subst (λ w → ⟨ x ∈ˢ w ⟩) v≡P x∈v) ∣₁
        o₃ (inr v≡T) = ∣ inr (PT.rec (setIsSet x T) o₅
          (F0-spec T T x .fst (subst (λ w → ⟨ x ∈ˢ w ⟩) v≡T x∈v))) ∣₁
          where
          o₅ : ⟨ x ≡ₕ T ⟩ ⊎ ⟨ x ≡ₕ T ⟩ → x ≡ T
          o₅ (inl e) = e
          o₅ (inr e) = e
    bwd : RHS → ⟨ x ∈ˢ F5 (F0 P (F0 T T)) T ⟩
    bwd h = PT.rec (snd (x ∈ˢ F5 (F0 P (F0 T T)) T)) b' h
      where
      b' : ⟨ x ∈ˢ P ⟩ ⊎ (x ≡ T) → ⟨ x ∈ˢ F5 (F0 P (F0 T T)) T ⟩
      b' (inl x∈P) = F5-spec (F0 P (F0 T T)) T x .snd
        ∣ P
          , ( F0-spec P (F0 T T) P .snd ∣ inl refl ∣₁
            , x∈P ) ∣₁
      b' (inr x≡T) = F5-spec (F0 P (F0 T T)) T x .snd
        ∣ F0 T T
          , ( F0-spec P (F0 T T) (F0 T T) .snd ∣ inr refl ∣₁
            , F0-spec T T x .snd ∣ inl x≡T ∣₁ ) ∣₁

  -- The recursion's value at an ordinal η ∈ γ: the pair family at η, its
  -- decode, the segment at η, and the witnesses the parent carriers need.
  -- The shape is a right-nested Σ (P-o): a record whose field has a
  -- carrier-indexed type hangs Agda 2.8.0's elaborator; the Σ checks.
  -- The accessors descend .fst/.snd/.fst/.snd/.snd/.snd/.snd/.snd at each
  -- depth, in the order P, P∈, seg, seg∈, top∈, story, seg∈W, nest.
  Rec : S → Type (ℓ-suc ℓ)
  Rec η = Σ[ P ∈ S ]
            ( (p : S) → ⟨ p ∈ˢ P ⟩ ⟷ ∥ Σ[ ζ ∈ S ]
                (⟨ ζ ∈ˢ η ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁ )
        × ( Σ[ seg ∈ S ]
            ( ( (x : S) → ⟨ x ∈ˢ seg ⟩
                   ⟷ ∥ (⟨ x ∈ˢ P ⟩ ⊎ (x ≡ pr η (Sset η))) ∥₁ )
            × ⟨ pr η (Sset η) ∈ˢ seg ⟩
            × storyW seg
            × ⟨ seg ∈ˢ W ⟩
            × ( (σ : S) → ⟨ σ ∈ˢ γ ⟩ → ⟨ isLimit σ ⟩ → ⟨ η ∈ˢ σ ⟩
                 → ⟨ seg ∈ˢ Lset σ ⟩ ) ) )

  -- The named accessors of the recursion's value, so the consumers do
  -- not read the nested Σ positionally.
  rec-P : {η : S} → Rec η → S
  rec-P R = R .fst

  rec-P∈ : {η : S} (R : Rec η) (p : S)
         → ⟨ p ∈ˢ rec-P R ⟩ ⟷ ∥ Σ[ ζ ∈ S ]
             (⟨ ζ ∈ˢ η ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
  rec-P∈ R p = R .snd .fst p

  rec-seg : {η : S} → Rec η → S
  rec-seg R = R .snd .snd .fst

  rec-seg∈ : {η : S} (R : Rec η) (x : S)
           → ⟨ x ∈ˢ rec-seg R ⟩
           ⟷ ∥ (⟨ x ∈ˢ rec-P R ⟩ ⊎ (x ≡ pr η (Sset η))) ∥₁
  rec-seg∈ R x = R .snd .snd .snd .fst x

  rec-top∈ : {η : S} (R : Rec η) → ⟨ pr η (Sset η) ∈ˢ rec-seg R ⟩
  rec-top∈ R = R .snd .snd .snd .snd .fst

  rec-story : {η : S} (R : Rec η) → storyW (rec-seg R)
  rec-story R = R .snd .snd .snd .snd .snd .fst

  rec-seg∈W : {η : S} (R : Rec η) → ⟨ rec-seg R ∈ˢ W ⟩
  rec-seg∈W R = R .snd .snd .snd .snd .snd .snd .fst

  rec-nest : {η : S} (R : Rec η) (σ : S) → ⟨ σ ∈ˢ γ ⟩ → ⟨ isLimit σ ⟩
           → ⟨ η ∈ˢ σ ⟩ → ⟨ rec-seg R ∈ˢ Lset σ ⟩
  rec-nest R σ σ∈γ limσ η∈σ = R .snd .snd .snd .snd .snd .snd .snd σ σ∈γ limσ η∈σ

  -- The memberships row at any limit member σ of γ: Sset δ ∈ Lset σ for
  -- every δ ∈ σ, by the same Below construction as the row at γ, with the
  -- STEP's induction hypothesis at σ.
  below-limσ : (σ : S) → ⟨ σ ∈ˢ γ ⟩ → ⟨ isLimit σ ⟩
             → (β : S) → IsOrd β → ⟨ isLimit β ⟩ → ⟨ β ∈ˢ σ ⟩
             → ⟨ Sset β ∈ˢ Lset σ ⟩
  below-limσ σ σ∈γ limσ β ordβ limβ β∈σ =
    Lset-mono {α = σ} {β = sucV β} (limit-succ-mem σ β limσ β∈σ)
      (IH β (isLimit-ord γ limγ .fst {x = σ} {y = β} β∈σ σ∈γ) limβ)

  memAt : (σ : S) → ⟨ σ ∈ˢ γ ⟩ → ⟨ isLimit σ ⟩
        → (δ : S) → ⟨ δ ∈ˢ σ ⟩ → ⟨ Sset δ ∈ˢ Lset σ ⟩
  memAt σ σ∈γ limσ = go
    where
    module Bσ = Below σ limσ StepGraph.stepSet∈L StepGraph.values∈L slot∈L
      (below-limσ σ σ∈γ limσ)
    go : (δ : S) → ⟨ δ ∈ˢ σ ⟩ → ⟨ Sset δ ∈ˢ Lset σ ⟩
    go δ δ∈σ = Bσ.rudBelow δ (limit-mem-ord σ limσ δ δ∈σ) δ∈σ .snd

  -- The stage-closure helpers at a limit carrier Lset σ: three members
  -- share a stage, the pair closes inside the limit, and the binary union
  -- closes inside the limit.  These are the a₀ module's
  -- Lstage₃/Fof-f5-limit shapes at a variable limit σ.
  module UnionClosureLimit (σ : S) (limσ : ⟨ isLimit σ ⟩) where

    ∅∈σ : ⟨ ∅ ∈ˢ σ ⟩
    ∅∈σ = go (ord-tri ∅ ∅-ord σ (isLimit-ord σ limσ))
      where
      go : ⟨ ∅ ∈ˢ σ ⟩ ⊎ ((∅ ≡ σ) ⊎ ⟨ σ ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ σ ⟩
      go (inl h) = h
      go (inr (inl e)) = Empty.rec (isLimit-not-zero σ limσ (sym e))
      go (inr (inr h)) = Empty.rec (∅-empty σ (∈∈ₛ {a = σ} {b = ∅} .fst h))

    ∅∈Lσ : ⟨ ∅ ∈ˢ Lset σ ⟩
    ∅∈Lσ = ∅∈Lset σ limσ ∅∈σ

    Lstage₃ : (x y z : S) → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ y ∈ˢ Lset σ ⟩
            → ⟨ z ∈ˢ Lset σ ⟩
            → ∥ Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ σ ⟩ × ⟨ x ∈ˢ Lset ζ ⟩ × ⟨ y ∈ˢ Lset ζ ⟩
                 × ⟨ z ∈ˢ Lset ζ ⟩) ∥₁
    Lstage₃ x y z x∈ y∈ z∈ = PT.rec squash₁ s₁ (Lstage₂ σ limσ x y x∈ y∈)
      where
      s₁ : Σ[ ζ₁ ∈ S ] (⟨ ζ₁ ∈ˢ σ ⟩ × ⟨ x ∈ˢ Lset ζ₁ ⟩ × ⟨ y ∈ˢ Lset ζ₁ ⟩)
         → ∥ Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ σ ⟩ × ⟨ x ∈ˢ Lset ζ ⟩ × ⟨ y ∈ˢ Lset ζ ⟩
              × ⟨ z ∈ˢ Lset ζ ⟩) ∥₁
      s₁ (ζ₁ , (ζ₁∈σ , x∈₁ , y∈₁)) = PT.rec squash₁ s₂ (Lstage σ limσ z z∈)
        where
        s₂ : Σ[ ζ₂ ∈ S ] (⟨ ζ₂ ∈ˢ σ ⟩ × ⟨ z ∈ˢ Lset ζ₂ ⟩)
           → ∥ Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ σ ⟩ × ⟨ x ∈ˢ Lset ζ ⟩ × ⟨ y ∈ˢ Lset ζ ⟩
                × ⟨ z ∈ˢ Lset ζ ⟩) ∥₁
        s₂ (ζ₂ , (ζ₂∈σ , z∈₂)) = ∣ go tri ∣₁
          where
          tri : Tri ζ₁ ζ₂
          tri = ord-tri ζ₁ (limit-mem-ord σ limσ ζ₁ ζ₁∈σ)
                     ζ₂ (limit-mem-ord σ limσ ζ₂ ζ₂∈σ)
          go : Tri ζ₁ ζ₂ → Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ σ ⟩ × ⟨ x ∈ˢ Lset ζ ⟩
               × ⟨ y ∈ˢ Lset ζ ⟩ × ⟨ z ∈ˢ Lset ζ ⟩)
          go (inl ζ₁∈ζ₂) = ζ₂ , (ζ₂∈σ
            , Lset-mono {α = ζ₂} {β = ζ₁} ζ₁∈ζ₂ x∈₁
            , Lset-mono {α = ζ₂} {β = ζ₁} ζ₁∈ζ₂ y∈₁ , z∈₂)
          go (inr (inl ζ₁≡ζ₂)) = ζ₂ , (ζ₂∈σ
            , subst (λ w → ⟨ x ∈ˢ Lset w ⟩) ζ₁≡ζ₂ x∈₁
            , subst (λ w → ⟨ y ∈ˢ Lset w ⟩) ζ₁≡ζ₂ y∈₁ , z∈₂)
          go (inr (inr ζ₂∈ζ₁)) = ζ₁ , (ζ₁∈σ
            , x∈₁ , y∈₁ , Lset-mono {α = ζ₁} {β = ζ₂} ζ₂∈ζ₁ z∈₂)

    F0∈L : (a b : S) → ⟨ a ∈ˢ Lset σ ⟩ → ⟨ b ∈ˢ Lset σ ⟩
         → ⟨ F0 a b ∈ˢ Lset σ ⟩
    F0∈L a b a∈ b∈ = Lpair-limit σ limσ a b a∈ b∈

    -- The binary union closes inside the limit: a common stage ζ places
    -- the union one stage up, and the limit closes the gap.
    Fof-f5-limit : (a b : S) → ⟨ a ∈ˢ Lset σ ⟩ → ⟨ b ∈ˢ Lset σ ⟩
                 → ⟨ Fof f5 a b ∈ˢ Lset σ ⟩
    Fof-f5-limit a b a∈ b∈ = PT.rec (snd (Fof f5 a b ∈ˢ Lset σ)) atStage
      (Lstage₃ a b ∅ a∈ b∈ ∅∈Lσ)
      where
      atStage : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ σ ⟩ × ⟨ a ∈ˢ Lset ζ ⟩ × ⟨ b ∈ˢ Lset ζ ⟩
                 × ⟨ ∅ ∈ˢ Lset ζ ⟩)
              → ⟨ Fof f5 a b ∈ˢ Lset σ ⟩
      atStage (ζ , (ζ∈σ , a∈ζ , b∈ζ , A∈ζ)) =
        Lset-mono {α = σ} {β = sucV ζ} (limit-succ-mem σ ζ limσ ζ∈σ)
          (Lval ζ A∈ζ f5 a b a∈ζ b∈ζ sub)
        where
        sub : (v : S) → ⟨ v ∈ˢ Fof f5 a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩
        sub v v∈ = PT.rec (snd (v ∈ˢ Lset ζ)) go
          (union-ax a v .fst (∈∈ₛ {a = v} {b = ⋃ a} .fst
            (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f5 a b) v∈)))
          where
          go : Σ[ u ∈ S ] (⟨ u ∈ₛ a ⟩ × ⟨ v ∈ₛ u ⟩) → ⟨ v ∈ˢ Lset ζ ⟩
          go (u , (u∈ₛa , v∈ₛu)) = Ltr ζ {x = u} {y = v}
            (∈∈ₛ {a = v} {b = u} .snd v∈ₛu)
            (Ltr ζ {x = a} {y = u} (∈∈ₛ {a = u} {b = a} .snd u∈ₛa) a∈ζ)

  -- The carried sequence's limit case at a limit member ξ of γ: the
  -- nested layer at Lset ξ, the six-clause story there, and the pair
  -- family Pξ built from the recursion's witnesses below ξ.  This is
  -- T240's measured miniature (src/ProbeT240.agda:102-654), with the
  -- outer Stepγ names in place of the probe's S module.
  module Nested
    (ξ : S) (ξ∈γ : ⟨ ξ ∈ˢ γ ⟩) (limξ : ⟨ isLimit ξ ⟩)
    where

    -- The nested carrier at xi: the witness carrier of the segment at xi.
    Wξ : S
    Wξ = Lset ξ

    Wtrξ : isTransV Wξ
    Wtrξ = layer-trans (Lset-layer ξ)

    ∅∈ξ : ⟨ ∅ ∈ˢ ξ ⟩
    ∅∈ξ = go (ord-tri ∅ ∅-ord ξ (isLimit-ord ξ limξ))
      where
      go : ⟨ ∅ ∈ˢ ξ ⟩ ⊎ ((∅ ≡ ξ) ⊎ ⟨ ξ ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ ξ ⟩
      go (inl h) = h
      go (inr (inl e)) = Empty.rec (isLimit-not-zero ξ limξ (sym e))
      go (inr (inr h)) = Empty.rec (∅-empty ξ (∈∈ₛ {a = ξ} {b = ∅} .fst h))

    ∅∈Wξ : ⟨ ∅ ∈ˢ Wξ ⟩
    ∅∈Wξ = ∅∈Lset ξ limξ ∅∈ξ

    mAξ : ⟪ Wξ ⟫
    mAξ = ∈-asFiber {a = ∅} {b = Wξ} ∅∈Wξ .fst

    qAξ : ⟪ Wξ ⟫↪ mAξ ≡ ∅
    qAξ = ∈-asFiber {a = ∅} {b = Wξ} ∅∈Wξ .snd

    -- The step closure at the nested carrier, the T222 slice at Lset xi.
    stepInWξ : (c : S) → ⟨ c ∈ˢ Wξ ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ Wξ ⟩
    stepInWξ c c∈ v v∈step = PT.rec (snd (v ∈ˢ Wξ)) go (step-out c v v∈step)
      where
      go : StepArm c v → ⟨ v ∈ˢ Wξ ⟩
      go (arm-member v∈c) = Ltr ξ {x = c} {y = v} v∈c c∈
      go (arm-self e) = subst (λ w → ⟨ w ∈ˢ Wξ ⟩) (sym e) c∈
      go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ Wξ)) both
        (Lstage₂ ξ limξ c ∅ c∈ ∅∈Wξ)
        where
        both : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ ξ ⟩ × ⟨ c ∈ˢ Lset ζ ⟩ × ⟨ ∅ ∈ˢ Lset ζ ⟩)
             → ⟨ v ∈ˢ Wξ ⟩
        both (ζ , (ζ∈ξ , c∈ζ , A∈ζ)) =
          Lset-mono {α = ξ} {β = sucV (suc⁴ ζ)}
            (limit-succ-mem ξ (suc⁴ ζ) limξ (suc⁴∈ ξ ζ limξ ζ∈ξ))
            (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ζ)) ⟩) (sym e)
              (Lval (suc⁴ ζ) (suc⁴-up ζ ∅ A∈ζ) i a b a∈ b∈
                (StepGraph.values∈L c ζ c∈ζ i a b sa sb)))
          where
          argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ζ ⟩
          argIn x (inl h) = Ltr ζ h c∈ζ
          argIn x (inr e') = subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym e') c∈ζ
          a∈ : ⟨ a ∈ˢ Lset (suc⁴ ζ) ⟩
          a∈ = suc⁴-up ζ a (argIn a sa)
          b∈ : ⟨ b ∈ˢ Lset (suc⁴ ζ) ⟩
          b∈ = suc⁴-up ζ b (argIn b sb)

    -- The graph layer and the step clause at the nested carrier.
    module WLξ = StepGraph.Layer Wξ Wtrξ mAξ qAξ ∅∈Wξ
    module WBξ = WLξ.BigOr WLξ.graphOf

    import L.Rud.StepStory {ℓ} lem ∅ Wξ Wtrξ as StepStoryWξ
    module WClξ = StepStoryWξ.Clause stepInWξ WLξ.graphOf WLξ.graph-out WLξ.graph-in
      WBξ.bigOr WBξ.bigOr-in WBξ.bigOr-out WLξ.eqFrame WLξ.eqFrame-ok

    -- The story at the nested carrier, instantiated with the graph layer.
    module Stξ = Story Wξ Wtrξ stepInWξ WLξ.graphOf WLξ.graph-out
      WLξ.graph-in WBξ.bigOr WBξ.bigOr-in WBξ.bigOr-out WLξ.eqFrame WLξ.eqFrame-ok

    module KWξ = LevelKit Wξ Wtrξ

    -- The sixth clause, from the carrier-generic Limit module of
    -- L.Rud.StepStory (T239 section 4's glue).
    module Limξ = StepStoryWξ.Limit

    -- The six-clause story at the nested carrier, assembled from the kit,
    -- the step clause and the sixth limit clause.
    storyWClausesξ : KWξ.StoryClauses
    storyWClausesξ = KWξ.mkClause KWξ.pairhood KWξ.pairForm KWξ.pairhood-out KWξ.pairhood-in KWξ.∷₊
                     KWξ.mkClause KWξ.singleValued KWξ.singleForm KWξ.single-out KWξ.single-in KWξ.∷₊
                     KWξ.mkClause KWξ.zeroClause KWξ.zeroForm KWξ.zero-out KWξ.zero-in KWξ.∷₊
                     KWξ.mkClause KWξ.exactDom KWξ.exactDomForm KWξ.exactDom-out KWξ.exactDom-in KWξ.∷₊
                     KWξ.clauseOk WClξ.succClause WClξ.succForm WClξ.succ-ok KWξ.∷₊
                     KWξ.clauseOk Stξ.limitClause Limξ.limitForm Limξ.limit-ok KWξ.∷₊ KWξ.end

    storyWξ : S → Type (ℓ-suc ℓ)
    storyWξ = KWξ.storyCl storyWClausesξ

    storyFormWξ : Formula ⟪ Wξ ⟫ 2
    storyFormWξ = KWξ.storyForm storyWClausesξ

    storyWξ-out : (f : KWξ.SM) (x : ⟪ Wξ ⟫)
                → ⟨ (f ∷ KWξ.ι x ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩ → storyWξ (fst f)
    storyWξ-out = KWξ.story-out storyWClausesξ

    storyWξ-in : (f : KWξ.SM) (x : ⟪ Wξ ⟫)
               → storyWξ (fst f) → ⟨ (f ∷ KWξ.ι x ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩
    storyWξ-in = KWξ.story-in storyWClausesξ

    storyWξ-ok : (f : KWξ.SM) (x : ⟪ Wξ ⟫)
               → ⟨ (f ∷ KWξ.ι x ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩ ⟷ storyWξ (fst f)
    storyWξ-ok = KWξ.story-ok storyWClausesξ

    -- The story at the nested carrier implies the story at gamma: every
    -- clause is carrier-free except the exact domain, whose witness lies
    -- in Lset xi.
    storyWξ→storyW : (f : S) → storyWξ f → storyW f
    storyWξ→storyW f st = ( st .fst , ( st .snd .fst , ( st .snd .snd .fst
      , ( exactDomW , ( st .snd .snd .snd .snd .fst
        , st .snd .snd .snd .snd .snd ) ) ) ) )
      where
      exactDomW : KW.exactDom f
      exactDomW = PT.rec squash₁ go (st .snd .snd .snd .fst)
        where
        go : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ Wξ ⟩ × IsOrd δ
               × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
               × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
            → KW.exactDom f
        go (δ , (δ∈Wξ , ordδ , in-dir , out-dir)) =
          ∣ δ , ( Lset-mono {α = γ} {β = ξ} ξ∈γ δ∈Wξ , ordδ , in-dir , out-dir ) ∣₁

    -- The story formula renamed into the arity-4 environment.
    embStoryξ : Fin 2 → Fin 4
    embStoryξ zero = suc (suc zero)
    embStoryξ (suc zero) = suc zero

    storyRenξ : Formula ⟪ Wξ ⟫ 4
    storyRenξ = renameFo embStoryξ storyFormWξ

    module RenSξ = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ Wξ))
      {ℓ} {⟪ Wξ ⟫} KWξ.ι

    smEtaξ : (x : KWξ.SM) → x ≡ KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst)
    smEtaξ x = ΣPathP (p , q)
      where
      p : fst x ≡ fst (KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst))
      p = sym (∈-asFiber {a = fst x} {b = Wξ} (snd x) .snd)
      q : PathP (λ i → ⟨ p i ∈ˢ Wξ ⟩) (snd x)
             (snd (KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst)))
      q = isProp→PathP (λ i → snd (p i ∈ˢ Wξ))
        (snd x) (snd (KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst)))

    storyRen-okξ : (δ : Vec KWξ.SM 4)
                 → ⟨ δ KWξ.⊨ᵐ storyRenξ ⟩ ⟷ storyWξ (fst (lookup (suc (suc zero)) δ))
    storyRen-okξ δ = (out , bwd)
      where
      sm ym : KWξ.SM
      sm = lookup (suc (suc zero)) δ
      ym = lookup (suc zero) δ
      fibY : ⟪ Wξ ⟫
      fibY = ∈-asFiber {a = fst ym} {b = Wξ} (snd ym) .fst
      ag : RenSξ.Agrees embStoryξ δ (sm ∷ ym ∷ [])
      ag zero = refl
      ag (suc zero) = refl
      out : ⟨ δ KWξ.⊨ᵐ storyRenξ ⟩ → storyWξ (fst sm)
      out h = storyWξ-ok sm fibY .fst
        (subst (λ w → ⟨ (sm ∷ w ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩) (smEtaξ ym)
          (subst ⟨_⟩ (sym (RenSξ.⊨-rename embStoryξ storyFormWξ δ (sm ∷ ym ∷ []) ag)) h))
      bwd : storyWξ (fst sm) → ⟨ δ KWξ.⊨ᵐ storyRenξ ⟩
      bwd st = subst ⟨_⟩
        (RenSξ.⊨-rename embStoryξ storyFormWξ δ (sm ∷ ym ∷ []) ag)
        (subst (λ w → ⟨ (sm ∷ w ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩) (sym (smEtaξ ym))
          (storyWξ-ok sm fibY .snd st))

    -- The pair family at the nested carrier, its decode at bound xi, and
    -- the segment with its six-clause story at gamma.  The witnesses below
    -- xi (the recursion) and the memberships at xi are parameters, the
    -- smallest decisive miniature of the general limit case.
    module Carried
      (memLξ : (δ : S) → ⟨ δ ∈ˢ ξ ⟩ → ⟨ Sset δ ∈ˢ Lset ξ ⟩)
      (below : (η : S) → ⟨ η ∈ˢ ξ ⟩
             → Σ[ s ∈ S ] (⟨ s ∈ˢ Wξ ⟩ × storyWξ s × ⟨ pr η (Sset η) ∈ˢ s ⟩))
      where

      -- The pair family's defining formula at the nested carrier (T159's,
      -- with the bound read from the exact domain at xi, not from the
      -- carrier).
      segBodyξ : Formula ⟪ Wξ ⟫ 4
      segBodyξ = (KWξ.PK.prAt (suc (suc (suc zero))) zero (suc zero))
              ∧̇ (KWξ.isOrdAt zero)
              ∧̇ storyRenξ
              ∧̇ (∃̇∈ (var (suc (suc zero)))
                    (KWξ.PK.prAt zero (suc zero) (suc (suc zero))))

      segFormξ : Formula ⟪ Wξ ⟫ 1
      segFormξ = ∃̇ (∃̇ (∃̇ segBodyξ))

      module Dξ = DefOf Wξ

      Pξ : S
      Pξ = Dξ.defSet segFormξ

      -- The bound read: an exact-domain witness of a story at Lset xi is
      -- an ordinal member of xi, so its pairs' first components lie below
      -- xi.
      exactDom-ξ∈ξ : (f : S) (η y : S) → storyWξ f → ⟨ pr η y ∈ˢ f ⟩ → ⟨ η ∈ˢ ξ ⟩
      exactDom-ξ∈ξ f η y h4 pr∈ = PT.rec (snd (η ∈ˢ ξ)) dStep (h4 .snd .snd .snd .fst)
        where
        dStep : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ Wξ ⟩ × IsOrd δ₀
                 × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
                 × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ₀ ⟩) )
              → ⟨ η ∈ˢ ξ ⟩
        dStep (δ₀ , (δ₀∈u , ordδ₀ , _ , out-d)) =
          isLimit-ord ξ limξ .fst {x = δ₀} {y = η} η∈δ₀ δ₀∈ξ
          where
          η∈δ₀ : ⟨ η ∈ˢ δ₀ ⟩
          η∈δ₀ = out-d η ∣ y , pr∈ ∣₁
          δ₀∈ξ : ⟨ δ₀ ∈ˢ ξ ⟩
          δ₀∈ξ = ord∈Lset→∈ ξ (isLimit-ord ξ limξ) δ₀ ordδ₀ δ₀∈u

      -- The decode at the nested carrier: the extension is exactly the
      -- pairs (eta, Sset eta) with eta below xi.
      segForm-okξ : (m : ⟪ Wξ ⟫)
                  → ⟨ (KWξ.ι m ∷ []) KWξ.⊨ᵐ segFormξ ⟩
                  ⟷ ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
      segForm-okξ m = (out , bwd)
        where
        δ₁ : Vec KWξ.SM 1
        δ₁ = KWξ.ι m ∷ []
        out : ⟨ δ₁ KWξ.⊨ᵐ segFormξ ⟩
            → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
        out sat = PT.rec squash₁ s₁ sat
          where
          s₁ : Σ[ sm ∈ KWξ.SM ] ⟨ (sm ∷ δ₁) KWξ.⊨ᵐ ∃̇ (∃̇ segBodyξ) ⟩
             → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
          s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
            where
            s₂ : Σ[ ym ∈ KWξ.SM ] ⟨ (ym ∷ sm ∷ δ₁) KWξ.⊨ᵐ ∃̇ segBodyξ ⟩
               → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
            s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
              where
              s₃ : Σ[ ηm ∈ KWξ.SM ] ⟨ (ηm ∷ ym ∷ sm ∷ δ₁) KWξ.⊨ᵐ segBodyξ ⟩
                 → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
              s₃ (ηm , (pr-sat , (ord-sat , (st-sat , pr∈-sat)))) =
                ∣ fst ηm , (η∈ξ , x≡prηSη) ∣₁
                where
                δ₄ : Vec KWξ.SM 4
                δ₄ = ηm ∷ ym ∷ sm ∷ δ₁
                x≡prηy : ⟪ Wξ ⟫↪ m ≡ pr (fst ηm) (fst ym)
                x≡prηy = KWξ.PK.prAt-out (suc (suc (suc zero))) zero (suc zero)
                  δ₄ pr-sat
                stξ : storyWξ (fst sm)
                stξ = storyRen-okξ δ₄ .fst st-sat
                prηy∈s : ⟨ pr (fst ηm) (fst ym) ∈ˢ fst sm ⟩
                prηy∈s = KWξ.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
                η∈ξ : ⟨ fst ηm ∈ˢ ξ ⟩
                η∈ξ = exactDom-ξ∈ξ (fst sm) (fst ηm) (fst ym) stξ prηy∈s
                η∈γ : ⟨ fst ηm ∈ˢ γ ⟩
                η∈γ = isLimit-ord γ limγ .fst {x = ξ} {y = fst ηm} η∈ξ ξ∈γ
                y≡Ssetη : fst ym ≡ Sset (fst ηm)
                y≡Ssetη = chain (fst sm) (storyWξ→storyW (fst sm) stξ)
                  (fst ηm) (fst ym) η∈γ prηy∈s
                x≡prηSη : ⟪ Wξ ⟫↪ m ≡ pr (fst ηm) (Sset (fst ηm))
                x≡prηSη = x≡prηy ∙ cong₂ pr refl y≡Ssetη
        bwd : ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
            → ⟨ δ₁ KWξ.⊨ᵐ segFormξ ⟩
        bwd h = PT.rec (snd (δ₁ KWξ.⊨ᵐ segFormξ)) step₀ h
          where
          step₀ : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η)))
                → ⟨ δ₁ KWξ.⊨ᵐ segFormξ ⟩
          step₀ (η , (η∈ξ , x≡prηSη)) = ∣ sm , (∣ ym , (∣ ηm , body-sat ∣₁) ∣₁) ∣₁
            where
            w : Σ[ s ∈ S ] (⟨ s ∈ˢ Wξ ⟩ × storyWξ s × ⟨ pr η (Sset η) ∈ˢ s ⟩)
            w = below η η∈ξ
            η∈W : ⟨ η ∈ˢ Wξ ⟩
            η∈W = Lset-mono {α = ξ} {β = sucV η} (limit-succ-mem ξ η limξ η∈ξ)
              (ord∈Lset-suc η (mem-ord {A = ξ} (isLimit-ord ξ limξ) η η∈ξ))
            sm ym ηm : KWξ.SM
            sm = KWξ.PK.pt (fst w) (w .snd .fst)
            ym = KWξ.PK.pt (Sset η) (memLξ η η∈ξ)
            ηm = KWξ.PK.pt η η∈W
            δ₄ : Vec KWξ.SM 4
            δ₄ = ηm ∷ ym ∷ sm ∷ δ₁
            body-sat : ⟨ δ₄ KWξ.⊨ᵐ segBodyξ ⟩
            body-sat = ( pr-sat , (ord-sat , (st-sat , pr∈-sat)) )
              where
              pr-sat : ⟨ δ₄ KWξ.⊨ᵐ KWξ.PK.prAt (suc (suc (suc zero))) zero (suc zero) ⟩
              pr-sat = KWξ.PK.prAt-in (suc (suc (suc zero))) zero (suc zero) δ₄
                x≡prηSη
              ord-sat : ⟨ δ₄ KWξ.⊨ᵐ KWξ.isOrdAt zero ⟩
              ord-sat = KWξ.isOrd-in zero δ₄
                (mem-ord {A = ξ} (isLimit-ord ξ limξ) η η∈ξ)
              st-sat : ⟨ δ₄ KWξ.⊨ᵐ storyRenξ ⟩
              st-sat = storyRen-okξ δ₄ .snd (w .snd .snd .fst)
              pr∈-sat : ⟨ δ₄ KWξ.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                           (KWξ.PK.prAt zero (suc zero) (suc (suc zero))) ⟩
              pr∈-sat = KWξ.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd
                (w .snd .snd .snd)

      -- The pair family's decode at bound xi, in the Segment shape.
      P∈ξ : (p : S) → ⟨ p ∈ˢ Pξ ⟩ ⟷ ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩
              × (p ≡ pr η (Sset η))) ∥₁
      P∈ξ p = (out , bwd)
        where
        out : ⟨ p ∈ˢ Pξ ⟩ → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) ∥₁
        out p∈ = PT.rec squash₁ go (segForm-okξ m .fst sat)
          where
          m : ⟪ Wξ ⟫
          m = ∈-asFiber {a = p} {b = Wξ} (Dξ.defSet⊆A segFormξ p p∈) .fst
          sat : ⟨ (KWξ.ι m ∷ []) KWξ.⊨ᵐ segFormξ ⟩
          sat = subst ⟨_⟩ (Dξ.defSet-mem segFormξ m)
            (subst (λ w → ⟨ w ∈ˢ Pξ ⟩) (sym (∈-asFiber {a = p} {b = Wξ}
              (Dξ.defSet⊆A segFormξ p p∈) .snd)) p∈)
          go : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η)))
             → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) ∥₁
          go (η , (η∈ξ , q)) = ∣ η
            , ( η∈ξ , sym (∈-asFiber {a = p} {b = Wξ} (Dξ.defSet⊆A segFormξ p p∈) .snd) ∙ q ) ∣₁
        bwd : ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) ∥₁
            → ⟨ p ∈ˢ Pξ ⟩
        bwd = PT.rec (snd (p ∈ˢ Pξ)) go
          where
          go : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) → ⟨ p ∈ˢ Pξ ⟩
          go (η , (η∈ξ , q)) = subst (λ w → ⟨ w ∈ˢ Pξ ⟩) (sym q)
            (subst (λ w → ⟨ w ∈ˢ Pξ ⟩) (fib .snd)
              (subst ⟨_⟩ (sym (Dξ.defSet-mem segFormξ m))
                (segForm-okξ m .snd ∣ η , (η∈ξ , fib .snd) ∣₁)))
            where
            w : Σ[ s ∈ S ] (⟨ s ∈ˢ Wξ ⟩ × storyWξ s × ⟨ pr η (Sset η) ∈ˢ s ⟩)
            w = below η η∈ξ
            pr∈W : ⟨ pr η (Sset η) ∈ˢ Wξ ⟩
            pr∈W = Wtrξ {x = fst w} {y = pr η (Sset η)} (w .snd .snd .snd) (w .snd .fst)
            fib : Σ[ m ∈ ⟪ Wξ ⟫ ] (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))
            fib = ∈-asFiber {a = pr η (Sset η)} {b = Wξ} pr∈W
            m : ⟪ Wξ ⟫
            m = fib .fst

      -- The top pair and the segment at xi, placed below gamma.
      Tξ : S
      Tξ = pr ξ (Sset ξ)

      segξ : S
      segξ = F5 (F0 Pξ (F0 Tξ Tξ)) Tξ

      sucVξ∈W : ⟨ sucV ξ ∈ˢ W ⟩
      sucVξ∈W = Lset-mono {α = γ} {β = sucV (sucV ξ)}
        (limit-succ-mem γ (sucV ξ) limγ (limit-succ-mem γ ξ limγ ξ∈γ))
        (ord∈Lset-suc (sucV ξ) (suc-ord (isLimit-ord ξ limξ)))

      module Segξ = St.Segment ξ limξ Pξ P∈ξ sucVξ∈W

      -- The sixth clause at the segment at xi: at a limit member a the
      -- decode reads the value below, and the top case is the machinery's
      -- own limit clause (T229's structure).
      segLimitClauseξ : St.limitClause segξ
      segLimitClauseξ a b lima pr∈ z = PT.rec isPropRhsa go
        (Segξ.seg∈ (pr a b) .fst pr∈)
        where
        rhs : S → Type (ℓ-suc ℓ)
        rhs i = ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ i ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
        isPropRhsa : isProp (⟨ z ∈ˢ b ⟩ ⟷ rhs a)
        isPropRhsa = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → snd (z ∈ˢ b)))
        go : ⟨ pr a b ∈ˢ Pξ ⟩ ⊎ (pr a b ≡ Tξ) → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
        go (inl p∈P) = PT.rec isPropRhsa aStep (P∈ξ (pr a b) .fst p∈P)
          where
          aStep : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (pr a b ≡ pr η (Sset η)))
                → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
          aStep (η , (η∈ξ , q)) = (fwd , bwd)
            where
            a≡η : a ≡ η
            a≡η = pr-inj q .fst
            b≡Sη : b ≡ Sset η
            b≡Sη = pr-inj q .snd
            a∈ξ : ⟨ a ∈ˢ ξ ⟩
            a∈ξ = subst (λ w → ⟨ w ∈ˢ ξ ⟩) (sym a≡η) η∈ξ
            b≡Sa : b ≡ Sset a
            b≡Sa = b≡Sη ∙ cong Sset (sym a≡η)
            fwd : ⟨ z ∈ˢ b ⟩ → rhs a
            fwd z∈b = PT.map go' (Sset-union-limit a lima z
              (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Sa z∈b))
              where
              go' : Σ[ δ ∈ S ] (⟨ δ ∈ˢ a ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
                  → Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩
                       × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
              go' (δ , (δ∈a , z∈Sδ')) = sucV δ , ( δ'∈a
                , ∣ Sset (sucV δ) , ( prδ'∈ , z∈Sδ' ) ∣₁ )
                where
                δ'∈a : ⟨ sucV δ ∈ˢ a ⟩
                δ'∈a = limit-succ-mem a δ lima δ∈a
                δ'∈ξ : ⟨ sucV δ ∈ˢ ξ ⟩
                δ'∈ξ = isLimit-ord ξ limξ .fst {x = a} {y = sucV δ} δ'∈a a∈ξ
                prδ'∈ : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ segξ ⟩
                prδ'∈ = Segξ.prξSξ∈seg (sucV δ) δ'∈ξ
            bwd : rhs a → ⟨ z ∈ˢ b ⟩
            bwd = PT.rec (snd (z ∈ˢ b)) go'
              where
              go' : Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩
                   × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                  → ⟨ z ∈ˢ b ⟩
              go' (η , (η∈a , rest)) = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Sa)
                (PT.rec (snd (z ∈ˢ Sset a)) s₂ rest)
                where
                s₂ : Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩)
                   → ⟨ z ∈ˢ Sset a ⟩
                s₂ (w , (pr∈ , z∈w)) = PT.rec (snd (z ∈ˢ Sset a)) d
                  (Segξ.seg∈ (pr η w) .fst pr∈)
                  where
                  d : ⟨ pr η w ∈ˢ Pξ ⟩ ⊎ (pr η w ≡ Tξ) → ⟨ z ∈ˢ Sset a ⟩
                  d (inl p∈P) = PT.rec (snd (z ∈ˢ Sset a)) pgo (P∈ξ (pr η w) .fst p∈P)
                    where
                    pgo : Σ[ η' ∈ S ] (⟨ η' ∈ˢ ξ ⟩ × (pr η w ≡ pr η' (Sset η')))
                        → ⟨ z ∈ˢ Sset a ⟩
                    pgo (η' , (η'∈ξ , q)) = Sset-mono {α = a} {β = η} η∈a z z∈Sη
                      where
                      w≡Sη : w ≡ Sset η
                      w≡Sη = subst (λ t → w ≡ Sset t) (sym (pr-inj q .fst))
                        (pr-inj q .snd)
                      z∈Sη : ⟨ z ∈ˢ Sset η ⟩
                      z∈Sη = subst (λ t → ⟨ z ∈ˢ t ⟩) (w≡Sη) z∈w
                  d (inr q) = Empty.rec {A = ⟨ z ∈ˢ Sset a ⟩} (∈-irrefl ξ ξ∈ξ)
                    where
                    η≡ξ : η ≡ ξ
                    η≡ξ = pr-inj q .fst
                    ξ∈a : ⟨ ξ ∈ˢ a ⟩
                    ξ∈a = subst (λ t → ⟨ t ∈ˢ a ⟩) η≡ξ η∈a
                    ξ∈ξ : ⟨ ξ ∈ˢ ξ ⟩
                    ξ∈ξ = isLimit-ord ξ limξ .fst {x = a} {y = ξ} ξ∈a a∈ξ
        go (inr q) = (fwd , bwd)
          where
          a≡ξ : a ≡ ξ
          a≡ξ = pr-inj q .fst
          b≡Sξ : b ≡ Sset ξ
          b≡Sξ = pr-inj q .snd
          fwd : ⟨ z ∈ˢ b ⟩ → rhs a
          fwd z∈b = subst rhs (sym a≡ξ)
            (Segξ.segLimit₀ z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Sξ z∈b))
          bwd : rhs a → ⟨ z ∈ˢ b ⟩
          bwd h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Sξ)
            (Segξ.segLimit₀ z .snd (subst rhs a≡ξ h))

      -- The six-clause story at the segment at xi, at the gamma carrier.
      segmentStory : storyW segξ
      segmentStory = ( Segξ.segPairhood , ( Segξ.segSingleValued
        , ( Segξ.segZeroClause , ( Segξ.segDom₀
          , ( Segξ.segSuccClause , segLimitClauseξ ) ) ) ) )

      -- The placements: the family, the top pair, and the segment, all
      -- below gamma.
      Pξ∈Lsucξ : ⟨ Pξ ∈ˢ Lset (sucV ξ) ⟩
      Pξ∈Lsucξ = 𝒟ₒ⊆Lsuc ξ Pξ (𝒟ₒ-intro Wξ Pξ ∣ segFormξ , refl ∣₁)

      ξ∈Lsucξ : ⟨ ξ ∈ˢ Lset (sucV ξ) ⟩
      ξ∈Lsucξ = ord∈Lset-suc ξ (isLimit-ord ξ limξ)

      Sξ∈Lsucξ : ⟨ Sset ξ ∈ˢ Lset (sucV ξ) ⟩
      Sξ∈Lsucξ = IH ξ ξ∈γ limξ

      F0ξξ∈L : ⟨ F0 ξ ξ ∈ˢ Lset (sucV (sucV ξ)) ⟩
      F0ξξ∈L = Lpair (sucV ξ) ξ ξ ξ∈Lsucξ ξ∈Lsucξ

      F0ξSξ∈L : ⟨ F0 ξ (Sset ξ) ∈ˢ Lset (sucV (sucV ξ)) ⟩
      F0ξSξ∈L = Lpair (sucV ξ) ξ (Sset ξ) ξ∈Lsucξ Sξ∈Lsucξ

      pr≡F0 : pr ξ (Sset ξ) ≡ F0 (F0 ξ ξ) (F0 ξ (Sset ξ))
      pr≡F0 = sym (cong (λ w → ⁅ w , ⁅ ξ , Sset ξ ⁆ ⁆) (pair-singleton ξ))

      Tξ∈L : ⟨ Tξ ∈ˢ Lset (sucV (sucV (sucV ξ))) ⟩
      Tξ∈L = subst (λ w → ⟨ w ∈ˢ Lset (sucV (sucV (sucV ξ))) ⟩) (sym pr≡F0)
        (Lpair (sucV (sucV ξ)) (F0 ξ ξ) (F0 ξ (Sset ξ)) F0ξξ∈L F0ξSξ∈L)

      F0TT∈L : ⟨ F0 Tξ Tξ ∈ˢ Lset (sucV (sucV (sucV (sucV ξ)))) ⟩
      F0TT∈L = Lpair (sucV (sucV (sucV ξ))) Tξ Tξ Tξ∈L Tξ∈L

      oξ⁴ : IsOrd (sucV (sucV (sucV (sucV ξ))))
      oξ⁴ = suc-ord (suc-ord (suc-ord (suc-ord (isLimit-ord ξ limξ))))

      sucVξ∈sucV⁴ξ : ⟨ sucV ξ ∈ˢ sucV (sucV (sucV (sucV ξ))) ⟩
      sucVξ∈sucV⁴ξ = oξ⁴ .fst {x = sucV (sucV ξ)} {y = sucV ξ}
        (self∈sucV (sucV ξ))
        (oξ⁴ .fst {x = sucV (sucV (sucV ξ))} {y = sucV (sucV ξ)}
          (self∈sucV (sucV (sucV ξ))) (self∈sucV (sucV (sucV (sucV ξ)))))

      Pξ∈L⁴ : ⟨ Pξ ∈ˢ Lset (sucV (sucV (sucV (sucV ξ)))) ⟩
      Pξ∈L⁴ = Lset-mono {α = sucV (sucV (sucV (sucV ξ)))} {β = sucV ξ}
        sucVξ∈sucV⁴ξ Pξ∈Lsucξ

      F0PTT∈L : ⟨ F0 Pξ (F0 Tξ Tξ) ∈ˢ Lset (sucV (sucV (sucV (sucV (sucV ξ))))) ⟩
      F0PTT∈L = Lpair (sucV (sucV (sucV (sucV ξ)))) Pξ (F0 Tξ Tξ)
        Pξ∈L⁴ F0TT∈L

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

      module UC = UnionClosure (sucV (sucV (sucV (sucV (sucV ξ)))))
        (suc-ord oξ⁴) (F0 Pξ (F0 Tξ Tξ)) F0PTT∈L

      segξ∈L⁶ : ⟨ segξ ∈ˢ Lset (sucV (sucV (sucV (sucV (sucV (sucV ξ)))))) ⟩
      segξ∈L⁶ = UC.union∈Lsuc

      sucV⁶ξ∈γ : ⟨ sucV (sucV (sucV (sucV (sucV (sucV ξ))))) ∈ˢ γ ⟩
      sucV⁶ξ∈γ = limit-succ-mem γ (sucV (sucV (sucV (sucV (sucV ξ))))) limγ
        (limit-succ-mem γ (sucV (sucV (sucV (sucV ξ)))) limγ
          (limit-succ-mem γ (sucV (sucV (sucV ξ))) limγ
            (limit-succ-mem γ (sucV (sucV ξ)) limγ
              (limit-succ-mem γ (sucV ξ) limγ (limit-succ-mem γ ξ limγ ξ∈γ)))))

      segξ∈W : ⟨ segξ ∈ˢ W ⟩
      segξ∈W = Lset-mono {α = γ} {β = sucV (sucV (sucV (sucV (sucV (sucV ξ)))))}
          sucV⁶ξ∈γ segξ∈L⁶

      prξSξ∈segξ : ⟨ pr ξ (Sset ξ) ∈ˢ segξ ⟩
      prξSξ∈segξ = Segξ.seg∈ (pr ξ (Sset ξ)) .snd ∣ inr refl ∣₁

      -- The recursion's value at the limit xi: the pair family, the
      -- segment, and the placements at every parent limit.
      record-value : Rec ξ
      record-value = ( Pξ
        , ( P∈ξ
          , ( segξ
            , ( Segξ.seg∈
              , ( prξSξ∈segξ
                , ( segmentStory
                  , ( segξ∈W , nest ) ) ) ) ) ) )
        where
        nest : (σ : S) → ⟨ σ ∈ˢ γ ⟩ → ⟨ isLimit σ ⟩ → ⟨ ξ ∈ˢ σ ⟩
             → ⟨ segξ ∈ˢ Lset σ ⟩
        nest σ σ∈γ limσ ξ∈σ =
          Lset-mono {α = σ} {β = sucV (sucV (sucV (sucV (sucV (sucV ξ)))))}
            (suc⁶ξ∈σ limσ ξ∈σ) segξ∈L⁶
          where
          suc⁶ξ∈σ : ⟨ isLimit σ ⟩ → ⟨ ξ ∈ˢ σ ⟩
                  → ⟨ sucV (sucV (sucV (sucV (sucV (sucV ξ))))) ∈ˢ σ ⟩
          suc⁶ξ∈σ limσ ξ∈σ = limit-succ-mem σ (sucV (sucV (sucV (sucV (sucV ξ))))) limσ
            (limit-succ-mem σ (sucV (sucV (sucV (sucV ξ)))) limσ
              (limit-succ-mem σ (sucV (sucV (sucV ξ))) limσ
                (limit-succ-mem σ (sucV (sucV ξ)) limσ
                  (limit-succ-mem σ (sucV ξ) limσ (limit-succ-mem σ ξ limσ ξ∈σ)))))

  -- The carried sequence's zero case: the pair family at ∅ is empty, and
  -- the segment is the single top pair pr ∅ (Sset ∅).
  zeroRec : Rec ∅
  zeroRec = ( ∅ , ( P∈∅ , ( seg∅ , ( seg∈gen ∅ T∅ , ( top∈∅ , ( story∅ , ( seg∅∈W , nest∅ ) ) ) ) ) ) )
    where
    T∅ : S
    T∅ = pr ∅ (Sset ∅)

    seg∅ : S
    seg∅ = F5 (F0 ∅ (F0 T∅ T∅)) T∅

    P∈∅ : (p : S) → ⟨ p ∈ˢ ∅ ⟩ ⟷ ∥ Σ[ ζ ∈ S ]
             (⟨ ζ ∈ˢ ∅ ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
    P∈∅ p = ( out , bwd )
      where
      out : ⟨ p ∈ˢ ∅ ⟩ → ∥ Σ[ ζ ∈ S ]
               (⟨ ζ ∈ˢ ∅ ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
      out p∈ = Empty.rec (∅-empty p (∈∈ₛ {a = p} {b = ∅} .fst p∈))
      bwd : ∥ Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ ∅ ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
          → ⟨ p ∈ˢ ∅ ⟩
      bwd = PT.rec (snd (p ∈ˢ ∅)) go
        where
        go : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ ∅ ⟩ × (p ≡ pr ζ (Sset ζ))) → ⟨ p ∈ˢ ∅ ⟩
        go (ζ , (ζ∈∅ , q)) = Empty.rec (∅-empty ζ (∈∈ₛ {a = ζ} {b = ∅} .fst ζ∈∅))

    top∈∅ : ⟨ T∅ ∈ˢ seg∅ ⟩
    top∈∅ = seg∈gen ∅ T∅ T∅ .snd ∣ inr refl ∣₁

    story∅ : storyW seg∅
    story∅ = ( pairhood∅ , ( single∅ , ( zero∅ , ( dom∅ , ( succ∅ , limit∅ ) ) ) ) )
      where
      pairhood∅ : KW.pairhood seg∅
      pairhood∅ z z∈ = PT.rec squash₁ go (seg∈gen ∅ T∅ z .fst z∈)
        where
        go : ⟨ z ∈ˢ ∅ ⟩ ⊎ (z ≡ T∅) → isPair z
        go (inl h) = Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst h))
        go (inr q) = ∣ ∅ , (Sset ∅ , q) ∣₁

      single∅ : KW.singleValued seg∅
      single∅ a b c ab∈ ac∈ = PT.rec (setIsSet b c) go₁
        (seg∈gen ∅ T∅ (pr a b) .fst ab∈)
        where
        go₁ : ⟨ pr a b ∈ˢ ∅ ⟩ ⊎ (pr a b ≡ T∅) → b ≡ c
        go₁ (inl h) = Empty.rec
          (∅-empty (pr a b) (∈∈ₛ {a = pr a b} {b = ∅} .fst h))
        go₁ (inr q₁) = PT.rec (setIsSet b c) go₂
          (seg∈gen ∅ T∅ (pr a c) .fst ac∈)
          where
          b≡S∅ : b ≡ Sset ∅
          b≡S∅ = pr-inj q₁ .snd
          go₂ : ⟨ pr a c ∈ˢ ∅ ⟩ ⊎ (pr a c ≡ T∅) → b ≡ c
          go₂ (inl h) = Empty.rec
            (∅-empty (pr a c) (∈∈ₛ {a = pr a c} {b = ∅} .fst h))
          go₂ (inr q₂) = b≡S∅ ∙ sym (pr-inj q₂ .snd)

      zero∅ : KW.zeroClause seg∅
      zero∅ = ∣ ∅ , (empt , pair) ∣₁
        where
        empt : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → Empty.⊥
        empt z z∈∅ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅)
        pair : ⟨ pr ∅ ∅ ∈ˢ seg∅ ⟩
        pair = subst (λ w → ⟨ w ∈ˢ seg∅ ⟩) (cong₂ pr refl Sset-zero)
          (seg∈gen ∅ T∅ (pr ∅ (Sset ∅)) .snd ∣ inr refl ∣₁)

      dom∅ : KW.exactDom seg∅
      dom∅ = ∣ sucV ∅ , ( sucV∅∈W , suc-ord ∅-ord , in-dir , out-dir ) ∣₁
        where
        sucV∅∈W : ⟨ sucV ∅ ∈ˢ W ⟩
        sucV∅∈W = Lset-mono {α = γ} {β = sucV (sucV ∅)}
          (limit-succ-mem γ (sucV ∅) limγ (limit-succ-mem γ ∅ limγ ∅∈γ))
          (ord∈Lset-suc (sucV ∅) (suc-ord ∅-ord))
        in-dir : (a : S) → ⟨ a ∈ˢ sucV ∅ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg∅ ⟩ ∥₁
        in-dir a a∈suc = ∈sucV-elim {A = ∅} {x = a} squash₁ a∈suc below top
          where
          below : ⟨ a ∈ˢ ∅ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg∅ ⟩ ∥₁
          below a∈∅ = Empty.rec (∅-empty a (∈∈ₛ {a = a} {b = ∅} .fst a∈∅))
          top : a ≡ ∅ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg∅ ⟩ ∥₁
          top a≡∅ = ∣ Sset ∅
            , subst (λ w → ⟨ pr w (Sset ∅) ∈ˢ seg∅ ⟩) (sym a≡∅) top∈∅ ∣₁
        out-dir : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg∅ ⟩ ∥₁
                → ⟨ a ∈ˢ sucV ∅ ⟩
        out-dir a = PT.rec (snd (a ∈ˢ sucV ∅)) go
          where
          go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg∅ ⟩ → ⟨ a ∈ˢ sucV ∅ ⟩
          go (b , pr∈) = PT.rec (snd (a ∈ˢ sucV ∅)) d
            (seg∈gen ∅ T∅ (pr a b) .fst pr∈)
            where
            d : ⟨ pr a b ∈ˢ ∅ ⟩ ⊎ (pr a b ≡ T∅) → ⟨ a ∈ˢ sucV ∅ ⟩
            d (inl h) = Empty.rec
              (∅-empty (pr a b) (∈∈ₛ {a = pr a b} {b = ∅} .fst h))
            d (inr q) = subst (λ w → ⟨ w ∈ˢ sucV ∅ ⟩) (pr-inj (sym q) .fst)
              (self∈sucV ∅)

      succ∅ : WCl.succClause seg∅
      succ∅ a c b ac∈ ab∈ = PT.rec (setIsSet b (step c)) go₁
        (seg∈gen ∅ T∅ (pr a c) .fst ac∈)
        where
        go₁ : ⟨ pr a c ∈ˢ ∅ ⟩ ⊎ (pr a c ≡ T∅) → b ≡ step c
        go₁ (inl h) = Empty.rec
          (∅-empty (pr a c) (∈∈ₛ {a = pr a c} {b = ∅} .fst h))
        go₁ (inr q₁) = PT.rec (setIsSet b (step c)) go₂
          (seg∈gen ∅ T∅ (pr (sucV a) b) .fst ab∈)
          where
          a≡∅ : a ≡ ∅
          a≡∅ = pr-inj q₁ .fst
          go₂ : ⟨ pr (sucV a) b ∈ˢ ∅ ⟩ ⊎ (pr (sucV a) b ≡ T∅) → b ≡ step c
          go₂ (inl h) = Empty.rec
            (∅-empty (pr (sucV a) b) (∈∈ₛ {a = pr (sucV a) b} {b = ∅} .fst h))
          go₂ (inr q₂) = Empty.rec {A = b ≡ step c} (∈-irrefl ∅ bad)
            where
            sucA≡∅ : sucV a ≡ ∅
            sucA≡∅ = pr-inj q₂ .fst
            a∈∅ : ⟨ a ∈ˢ ∅ ⟩
            a∈∅ = subst (λ w → ⟨ a ∈ˢ w ⟩) sucA≡∅ (self∈sucV a)
            bad : ⟨ ∅ ∈ˢ ∅ ⟩
            bad = subst (λ w → ⟨ w ∈ˢ ∅ ⟩) a≡∅ a∈∅

      limit∅ : St.limitClause seg∅
      limit∅ a b lima pr∈ z = PT.rec isPropRhsa go
        (seg∈gen ∅ T∅ (pr a b) .fst pr∈)
        where
        rhs : S → Type (ℓ-suc ℓ)
        rhs i = ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ i ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg∅ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
        isPropRhsa : isProp (⟨ z ∈ˢ b ⟩ ⟷ rhs a)
        isPropRhsa = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → snd (z ∈ˢ b)))
        go : ⟨ pr a b ∈ˢ ∅ ⟩ ⊎ (pr a b ≡ T∅) → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
        go (inl h) = Empty.rec {A = ⟨ z ∈ˢ b ⟩ ⟷ rhs a}
          (∅-empty (pr a b) (∈∈ₛ {a = pr a b} {b = ∅} .fst h))
        go (inr q) = Empty.rec {A = ⟨ z ∈ˢ b ⟩ ⟷ rhs a}
          (isLimit-not-zero a lima a≡∅)
          where
          a≡∅ : a ≡ ∅
          a≡∅ = pr-inj q .fst

    -- The segment at ∅ closes inside every limit carrier: the top pair
    -- lies in Lset σ by the limit pair read, and the union closes by the
    -- stage machinery.
    seg∅∈W : ⟨ seg∅ ∈ˢ W ⟩
    seg∅∈W = subst (λ w → ⟨ w ∈ˢ W ⟩) (Fof-f5 (F0 ∅ (F0 T∅ T∅)) T∅) result
      where
      module Uγ = UnionClosureLimit γ limγ
      T∅∈W : ⟨ T∅ ∈ˢ W ⟩
      T∅∈W = Lpr-limit γ limγ ∅ (Sset ∅) Uγ.∅∈Lσ (mem∈L ∅ ∅∈γ)
      F0T∅T∅∈W : ⟨ F0 T∅ T∅ ∈ˢ W ⟩
      F0T∅T∅∈W = Uγ.F0∈L T∅ T∅ T∅∈W T∅∈W
      F0∅TT∈W : ⟨ F0 ∅ (F0 T∅ T∅) ∈ˢ W ⟩
      F0∅TT∈W = Uγ.F0∈L ∅ (F0 T∅ T∅) Uγ.∅∈Lσ F0T∅T∅∈W
      result : ⟨ Fof f5 (F0 ∅ (F0 T∅ T∅)) T∅ ∈ˢ W ⟩
      result = Uγ.Fof-f5-limit (F0 ∅ (F0 T∅ T∅)) T∅ F0∅TT∈W T∅∈W

    nest∅ : (σ : S) → ⟨ σ ∈ˢ γ ⟩ → ⟨ isLimit σ ⟩ → ⟨ ∅ ∈ˢ σ ⟩
          → ⟨ seg∅ ∈ˢ Lset σ ⟩
    nest∅ σ σ∈γ limσ ∅∈σ = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩)
      (Fof-f5 (F0 ∅ (F0 T∅ T∅)) T∅) result
      where
      module Uσ = UnionClosureLimit σ limσ
      T∅∈Lσ : ⟨ T∅ ∈ˢ Lset σ ⟩
      T∅∈Lσ = Lpr-limit σ limσ ∅ (Sset ∅) Uσ.∅∈Lσ (memAt σ σ∈γ limσ ∅ ∅∈σ)
      F0T∅T∅∈Lσ : ⟨ F0 T∅ T∅ ∈ˢ Lset σ ⟩
      F0T∅T∅∈Lσ = Uσ.F0∈L T∅ T∅ T∅∈Lσ T∅∈Lσ
      F0∅TT∈Lσ : ⟨ F0 ∅ (F0 T∅ T∅) ∈ˢ Lset σ ⟩
      F0∅TT∈Lσ = Uσ.F0∈L ∅ (F0 T∅ T∅) Uσ.∅∈Lσ F0T∅T∅∈Lσ
      result : ⟨ Fof f5 (F0 ∅ (F0 T∅ T∅)) T∅ ∈ˢ Lset σ ⟩
      result = Uσ.Fof-f5-limit (F0 ∅ (F0 T∅ T∅)) T∅ F0∅TT∈Lσ T∅∈Lσ

  -- The carried sequence's successor case: the pair family at sucV c is
  -- the segment at c, and the segment at sucV c extends it by the top
  -- pair (T213's segment-extension lemma).
  succRec : (c : S) → ⟨ c ∈ˢ γ ⟩ → Rec c → Rec (sucV c)
  succRec c c∈γ Rc = ( rec-seg Rc
    , ( P∈suc , ( segs , ( seg∈gen (rec-seg Rc) Ts , ( top∈s , ( storys , ( segs∈W , nests ) ) ) ) ) ) )
    where
    Ts : S
    Ts = pr (sucV c) (Sset (sucV c))

    segs : S
    segs = F5 (F0 (rec-seg Rc) (F0 Ts Ts)) Ts

    P∈suc : (p : S) → ⟨ p ∈ˢ rec-seg Rc ⟩ ⟷ ∥ Σ[ ζ ∈ S ]
              (⟨ ζ ∈ˢ sucV c ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
    P∈suc p = (out , bwd)
      where
      out : ⟨ p ∈ˢ rec-seg Rc ⟩ → ∥ Σ[ ζ ∈ S ]
               (⟨ ζ ∈ˢ sucV c ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
      out p∈ = PT.rec squash₁ go (rec-seg∈ Rc p .fst p∈)
        where
        go : ⟨ p ∈ˢ rec-P Rc ⟩ ⊎ (p ≡ pr c (Sset c)) → ∥ Σ[ ζ ∈ S ]
               (⟨ ζ ∈ˢ sucV c ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
        go (inl p∈Pc) = PT.map add (rec-P∈ Rc p .fst p∈Pc)
          where
          add : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ c ⟩ × (p ≡ pr ζ (Sset ζ)))
              → Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ sucV c ⟩ × (p ≡ pr ζ (Sset ζ)))
          add (ζ , (ζ∈c , q)) = ζ , (∈sucV-inl {A = c} {x = ζ} ζ∈c , q)
        go (inr p≡Tc) = ∣ c , ( self∈sucV c , p≡Tc ) ∣₁
      bwd : ∥ Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ sucV c ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁
          → ⟨ p ∈ˢ rec-seg Rc ⟩
      bwd = PT.rec (snd (p ∈ˢ rec-seg Rc)) go
        where
        go : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ sucV c ⟩ × (p ≡ pr ζ (Sset ζ)))
           → ⟨ p ∈ˢ rec-seg Rc ⟩
        go (ζ , (ζ∈suc , q)) = ∈sucV-elim {A = c} {x = ζ}
          (snd (p ∈ˢ rec-seg Rc)) ζ∈suc below top
          where
          below : ⟨ ζ ∈ˢ c ⟩ → ⟨ p ∈ˢ rec-seg Rc ⟩
          below ζ∈c = rec-seg∈ Rc p .snd ∣ inl (rec-P∈ Rc p .snd ∣ ζ , (ζ∈c , q) ∣₁) ∣₁
          top : ζ ≡ c → ⟨ p ∈ˢ rec-seg Rc ⟩
          top ζ≡c = rec-seg∈ Rc p .snd ∣ inr (subst (λ w → p ≡ pr w (Sset w)) ζ≡c q) ∣₁

    top∈s : ⟨ pr (sucV c) (Sset (sucV c)) ∈ˢ segs ⟩
    top∈s = seg∈gen (rec-seg Rc) Ts (pr (sucV c) (Sset (sucV c))) .snd ∣ inr refl ∣₁

    -- The first components of the segment at c lie below sucV c.
    fst∈suc : (a b : S) → ⟨ pr a b ∈ˢ rec-seg Rc ⟩ → ⟨ a ∈ˢ sucV c ⟩
    fst∈suc a b ab∈ = PT.rec (snd (a ∈ˢ sucV c)) go (rec-seg∈ Rc (pr a b) .fst ab∈)
      where
      go : ⟨ pr a b ∈ˢ rec-P Rc ⟩ ⊎ (pr a b ≡ pr c (Sset c)) → ⟨ a ∈ˢ sucV c ⟩
      go (inl p∈P) = PT.rec (snd (a ∈ˢ sucV c)) pgo (rec-P∈ Rc (pr a b) .fst p∈P)
        where
        pgo : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ c ⟩ × (pr a b ≡ pr ζ (Sset ζ)))
            → ⟨ a ∈ˢ sucV c ⟩
        pgo (ζ , (ζ∈c , q)) = subst (λ w → ⟨ w ∈ˢ sucV c ⟩) (sym (pr-inj q .fst))
          (∈sucV-inl {A = c} {x = ζ} ζ∈c)
      go (inr q) = subst (λ w → ⟨ w ∈ˢ sucV c ⟩) (pr-inj (sym q) .fst)
        (self∈sucV c)

    -- Every member of sucV c has its S-pair in the segment at c.
    pairBelow : (a : S) → ⟨ a ∈ˢ sucV c ⟩ → ⟨ pr a (Sset a) ∈ˢ rec-seg Rc ⟩
    pairBelow a a∈suc = ∈sucV-elim {A = c} {x = a} (snd (pr a (Sset a) ∈ˢ rec-seg Rc))
      a∈suc below top
      where
      below : ⟨ a ∈ˢ c ⟩ → ⟨ pr a (Sset a) ∈ˢ rec-seg Rc ⟩
      below a∈c = rec-seg∈ Rc (pr a (Sset a)) .snd
        ∣ inl (rec-P∈ Rc (pr a (Sset a)) .snd ∣ a , (a∈c , refl) ∣₁) ∣₁
      top : a ≡ c → ⟨ pr a (Sset a) ∈ˢ rec-seg Rc ⟩
      top a≡c = subst (λ w → ⟨ pr w (Sset w) ∈ˢ rec-seg Rc ⟩) (sym a≡c) (rec-top∈ Rc)

    storys : storyW segs
    storys = ( pairhoods , ( singles , ( zeros , ( doms , ( succs , limits ) ) ) ) )
      where
      pairhoods : KW.pairhood segs
      pairhoods z z∈ = PT.rec squash₁ go (seg∈gen (rec-seg Rc) Ts z .fst z∈)
        where
        go : ⟨ z ∈ˢ rec-seg Rc ⟩ ⊎ (z ≡ Ts) → isPair z
        go (inl z∈segc) = rec-story Rc .fst z z∈segc
        go (inr q) = ∣ sucV c , (Sset (sucV c) , q) ∣₁

      singles : KW.singleValued segs
      singles a b c' ab∈ ac∈ = PT.rec (setIsSet b c') go₁
        (seg∈gen (rec-seg Rc) Ts (pr a b) .fst ab∈)
        where
        go₁ : ⟨ pr a b ∈ˢ rec-seg Rc ⟩ ⊎ (pr a b ≡ Ts) → b ≡ c'
        go₁ (inl ab∈segc) = PT.rec (setIsSet b c') go₂
          (seg∈gen (rec-seg Rc) Ts (pr a c') .fst ac∈)
          where
          go₂ : ⟨ pr a c' ∈ˢ rec-seg Rc ⟩ ⊎ (pr a c' ≡ Ts) → b ≡ c'
          go₂ (inl ac∈segc) = rec-story Rc .snd .fst a b c' ab∈segc ac∈segc
          go₂ (inr q₂) = Empty.rec {A = b ≡ c'} (∈-irrefl (sucV c) bad)
            where
            a≡sc : a ≡ sucV c
            a≡sc = pr-inj q₂ .fst
            a∈sc : ⟨ a ∈ˢ sucV c ⟩
            a∈sc = fst∈suc a b ab∈segc
            bad : ⟨ sucV c ∈ˢ sucV c ⟩
            bad = subst (λ w → ⟨ w ∈ˢ sucV c ⟩) a≡sc a∈sc
        go₁ (inr q₁) = PT.rec (setIsSet b c') go₃
          (seg∈gen (rec-seg Rc) Ts (pr a c') .fst ac∈)
          where
          a≡sc : a ≡ sucV c
          a≡sc = pr-inj q₁ .fst
          go₃ : ⟨ pr a c' ∈ˢ rec-seg Rc ⟩ ⊎ (pr a c' ≡ Ts) → b ≡ c'
          go₃ (inl ac∈segc) = Empty.rec {A = b ≡ c'} (∈-irrefl (sucV c) bad)
            where
            a∈sc : ⟨ a ∈ˢ sucV c ⟩
            a∈sc = fst∈suc a c' ac∈segc
            bad : ⟨ sucV c ∈ˢ sucV c ⟩
            bad = subst (λ w → ⟨ w ∈ˢ sucV c ⟩) a≡sc a∈sc
          go₃ (inr q₂) = pr-inj q₁ .snd ∙ sym (pr-inj q₂ .snd)

      zeros : KW.zeroClause segs
      zeros = PT.map lift₀ (rec-story Rc .snd .snd .fst)
        where
        lift₀ : Σ[ a ∈ S ] ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ rec-seg Rc ⟩ )
              → Σ[ a ∈ S ] ( ((z : S) → ⟨ z ∈ˢ a ⟩ → Empty.⊥) × ⟨ pr a a ∈ˢ segs ⟩ )
        lift₀ (a , (empt , pr∈)) = a , (empt , seg∈gen (rec-seg Rc) Ts (pr a a) .snd ∣ inl pr∈ ∣₁)

      doms : KW.exactDom segs
      doms = ∣ sucV (sucV c)
        , ( scc∈W , suc-ord (suc-ord (mem-ord {A = γ} (isLimit-ord γ limγ) c c∈γ)) , in-dir , out-dir ) ∣₁
        where
        scc∈W : ⟨ sucV (sucV c) ∈ˢ W ⟩
        scc∈W = Lset-mono {α = γ} {β = sucV (sucV (sucV c))}
          (limit-succ-mem γ (sucV (sucV c)) limγ
            (limit-succ-mem γ (sucV c) limγ (limit-succ-mem γ c limγ c∈γ)))
          (ord∈Lset-suc (sucV (sucV c))
            (suc-ord (suc-ord (mem-ord {A = γ} (isLimit-ord γ limγ) c c∈γ))))
        in-dir : (a : S) → ⟨ a ∈ˢ sucV (sucV c) ⟩
               → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ segs ⟩ ∥₁
        in-dir a a∈scc = ∈sucV-elim {A = sucV c} {x = a} squash₁ a∈scc below top
          where
          below : ⟨ a ∈ˢ sucV c ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ segs ⟩ ∥₁
          below a∈sc = ∣ Sset a
            , ( seg∈gen (rec-seg Rc) Ts (pr a (Sset a)) .snd ∣ inl (pairBelow a a∈sc) ∣₁ ) ∣₁
          top : a ≡ sucV c → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ segs ⟩ ∥₁
          top a≡sc = ∣ Sset (sucV c)
            , subst (λ w → ⟨ pr w (Sset (sucV c)) ∈ˢ segs ⟩) (sym a≡sc) top∈s ∣₁
        out-dir : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ segs ⟩ ∥₁
                → ⟨ a ∈ˢ sucV (sucV c) ⟩
        out-dir a = PT.rec (snd (a ∈ˢ sucV (sucV c))) go
          where
          go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ segs ⟩ → ⟨ a ∈ˢ sucV (sucV c) ⟩
          go (b , pr∈) = PT.rec (snd (a ∈ˢ sucV (sucV c))) d
            (seg∈gen (rec-seg Rc) Ts (pr a b) .fst pr∈)
            where
            d : ⟨ pr a b ∈ˢ rec-seg Rc ⟩ ⊎ (pr a b ≡ Ts) → ⟨ a ∈ˢ sucV (sucV c) ⟩
            d (inl ab∈segc) = ∈sucV-inl {A = sucV c} {x = a} (fst∈suc a b ab∈segc)
            d (inr q) = subst (λ w → ⟨ w ∈ˢ sucV (sucV c) ⟩) (pr-inj (sym q) .fst)
              (self∈sucV (sucV c))

      succs : WCl.succClause segs
      succs a c' b ac∈ ab∈ = PT.rec (setIsSet b (step c')) go₁
        (seg∈gen (rec-seg Rc) Ts (pr a c') .fst ac∈)
        where
        go₁ : ⟨ pr a c' ∈ˢ rec-seg Rc ⟩ ⊎ (pr a c' ≡ Ts) → b ≡ step c'
        go₁ (inl ac∈segc) = PT.rec (setIsSet b (step c')) go₂
          (seg∈gen (rec-seg Rc) Ts (pr (sucV a) b) .fst ab∈)
          where
          c'≡Sa : c' ≡ Sset a
          c'≡Sa = PT.rec (setIsSet c' (Sset a)) cgo (rec-seg∈ Rc (pr a c') .fst ac∈segc)
            where
            cgo : ⟨ pr a c' ∈ˢ rec-P Rc ⟩ ⊎ (pr a c' ≡ pr c (Sset c)) → c' ≡ Sset a
            cgo (inl p∈Pc) = PT.rec (setIsSet c' (Sset a)) pgo
              (rec-P∈ Rc (pr a c') .fst p∈Pc)
              where
              pgo : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ c ⟩ × (pr a c' ≡ pr ζ (Sset ζ)))
                  → c' ≡ Sset a
              pgo (ζ , (ζ∈c , q)) = pr-inj q .snd
                ∙ cong Sset (sym (pr-inj q .fst))
            cgo (inr q) = pr-inj q .snd ∙ cong Sset (sym (pr-inj q .fst))
          go₂ : ⟨ pr (sucV a) b ∈ˢ rec-seg Rc ⟩ ⊎ (pr (sucV a) b ≡ Ts)
              → b ≡ step c'
          go₂ (inl sab∈segc) = rec-story Rc .snd .snd .snd .snd .fst a c' b ac∈segc sab∈segc
          go₂ (inr q₂) = pr-inj q₂ .snd ∙ cong Sset (sym (pr-inj q₂ .fst))
            ∙ Sset-suc a ∙ cong step (sym c'≡Sa)
        go₁ (inr q₁) = PT.rec (setIsSet b (step c')) go₃
          (seg∈gen (rec-seg Rc) Ts (pr (sucV a) b) .fst ab∈)
          where
          go₃ : ⟨ pr (sucV a) b ∈ˢ rec-seg Rc ⟩ ⊎ (pr (sucV a) b ≡ Ts)
              → b ≡ step c'
          go₃ (inl sab∈segc) = Empty.rec {A = b ≡ step c'} (∈-irrefl a bad)
            where
            a∈sc : ⟨ a ∈ˢ sucV c ⟩
            a∈sc = suc-ord (mem-ord {A = γ} (isLimit-ord γ limγ) c c∈γ) .fst
              {x = sucV a} {y = a} (self∈sucV a) (fst∈suc (sucV a) b sab∈segc)
            bad : ⟨ a ∈ˢ a ⟩
            bad = subst (λ w → ⟨ a ∈ˢ w ⟩) (sym (pr-inj q₁ .fst)) a∈sc
          go₃ (inr q₂) = Empty.rec {A = b ≡ step c'} (∈-irrefl a bad)
            where
            a≡sucA : a ≡ sucV a
            a≡sucA = pr-inj q₁ .fst ∙ sym (pr-inj q₂ .fst)
            bad : ⟨ a ∈ˢ a ⟩
            bad = subst (λ w → ⟨ a ∈ˢ w ⟩) (sym a≡sucA) (self∈sucV a)

      limits : St.limitClause segs
      limits a b lima pr∈ z = PT.rec isPropRhsa go
        (seg∈gen (rec-seg Rc) Ts (pr a b) .fst pr∈)
        where
        rhs : S → Type (ℓ-suc ℓ)
        rhs i = ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ i ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
        isPropRhsa : isProp (⟨ z ∈ˢ b ⟩ ⟷ rhs a)
        isPropRhsa = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → snd (z ∈ˢ b)))
        go : ⟨ pr a b ∈ˢ rec-seg Rc ⟩ ⊎ (pr a b ≡ Ts) → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
        go (inl ab∈segc) = (fwd , bwd)
          where
          base : ⟨ z ∈ˢ b ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
               × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ rec-seg Rc ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
          base = rec-story Rc .snd .snd .snd .snd .snd a b lima ab∈segc z
          fwd : ⟨ z ∈ˢ b ⟩ → rhs a
          fwd z∈b = PT.map lift₀ (base .fst z∈b)
            where
            lift₀ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                      × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ rec-seg Rc ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                  → Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                       × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
            lift₀ (ξ , (ξ∈a , rest)) = ξ , (ξ∈a , PT.map lift' rest)
              where
              lift' : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ rec-seg Rc ⟩ × ⟨ z ∈ˢ w ⟩)
                    → Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩)
              lift' (w , (pr∈ , z∈w)) = w
                , ( seg∈gen (rec-seg Rc) Ts (pr ξ w) .snd ∣ inl pr∈ ∣₁ , z∈w )
          bwd : rhs a → ⟨ z ∈ˢ b ⟩
          bwd = PT.rec (snd (z ∈ˢ b)) go'
            where
            go' : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                 × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                → ⟨ z ∈ˢ b ⟩
            go' (ξ , (ξ∈a , rest)) = PT.rec (snd (z ∈ˢ b)) s₂ rest
              where
              s₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩) → ⟨ z ∈ˢ b ⟩
              s₂ (w , (pr∈ , z∈w)) = PT.rec (snd (z ∈ˢ b)) d
                (seg∈gen (rec-seg Rc) Ts (pr ξ w) .fst pr∈)
                where
                d : ⟨ pr ξ w ∈ˢ rec-seg Rc ⟩ ⊎ (pr ξ w ≡ Ts) → ⟨ z ∈ˢ b ⟩
                d (inl pr∈segc) = base .snd ∣ ξ , (ξ∈a , ∣ w , (pr∈segc , z∈w) ∣₁) ∣₁
                d (inr q) = Empty.rec {A = ⟨ z ∈ˢ b ⟩} (∈-irrefl (sucV c) bad)
                  where
                  ξ≡sc : ξ ≡ sucV c
                  ξ≡sc = pr-inj q .fst
                  a∈sc : ⟨ a ∈ˢ sucV c ⟩
                  a∈sc = fst∈suc a b ab∈segc
                  sc∈a : ⟨ sucV c ∈ˢ a ⟩
                  sc∈a = subst (λ w → ⟨ w ∈ˢ a ⟩) ξ≡sc ξ∈a
                  bad : ⟨ sucV c ∈ˢ sucV c ⟩
                  bad = suc-ord (mem-ord {A = γ} (isLimit-ord γ limγ) c c∈γ) .fst
                    {x = a} {y = sucV c} sc∈a a∈sc
        go (inr q) = (fwd , bwd)
          where
          a≡sc : a ≡ sucV c
          a≡sc = pr-inj q .fst
          b≡Ssc : b ≡ Sset (sucV c)
          b≡Ssc = pr-inj q .snd
          fwd : ⟨ z ∈ˢ b ⟩ → rhs a
          fwd z∈b = PT.map go' (Sset-union-limit (sucV c) (subst (λ w → ⟨ isLimit w ⟩) a≡sc lima) z
            (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Ssc z∈b))
            where
            go' : Σ[ δ ∈ S ] (⟨ δ ∈ˢ sucV c ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
                → Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                     × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
            go' (δ , (δ∈sc , z∈Sδ')) = sucV δ , ( δ'∈a
              , ∣ Sset (sucV δ) , ( prδ'∈ , z∈Sδ' ) ∣₁ )
              where
              δ'∈sc : ⟨ sucV δ ∈ˢ sucV c ⟩
              δ'∈sc = limit-succ-mem (sucV c) δ
                (subst (λ w → ⟨ isLimit w ⟩) a≡sc lima) δ∈sc
              δ'∈a : ⟨ sucV δ ∈ˢ a ⟩
              δ'∈a = subst (λ w → ⟨ sucV δ ∈ˢ w ⟩) (sym a≡sc) δ'∈sc
              prδ'∈ : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ segs ⟩
              prδ'∈ = seg∈gen (rec-seg Rc) Ts (pr (sucV δ) (Sset (sucV δ)))
                .snd ∣ inl (pairBelow (sucV δ) δ'∈sc) ∣₁
          bwd : rhs a → ⟨ z ∈ˢ b ⟩
          bwd = PT.rec (snd (z ∈ˢ b)) go'
            where
            go' : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
                 × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                → ⟨ z ∈ˢ b ⟩
            go' (ξ , (ξ∈a , rest)) = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Ssc)
              (PT.rec (snd (z ∈ˢ Sset (sucV c))) s₂ rest)
              where
              ξ∈sc : ⟨ ξ ∈ˢ sucV c ⟩
              ξ∈sc = subst (λ w → ⟨ ξ ∈ˢ w ⟩) a≡sc ξ∈a
              s₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ segs ⟩ × ⟨ z ∈ˢ w ⟩)
                 → ⟨ z ∈ˢ Sset (sucV c) ⟩
              s₂ (w , (pr∈ , z∈w)) = PT.rec (snd (z ∈ˢ Sset (sucV c))) d
                (seg∈gen (rec-seg Rc) Ts (pr ξ w) .fst pr∈)
                where
                d : ⟨ pr ξ w ∈ˢ rec-seg Rc ⟩ ⊎ (pr ξ w ≡ Ts) → ⟨ z ∈ˢ Sset (sucV c) ⟩
                d (inl pr∈segc) = Sset-mono {α = sucV c} {β = ξ} ξ∈sc z
                  (subst (λ t → ⟨ z ∈ˢ t ⟩)
                    (chain (rec-seg Rc) (rec-story Rc) ξ w ξ∈γ pr∈segc) z∈w)
                  where
                  ξ∈γ : ⟨ ξ ∈ˢ γ ⟩
                  ξ∈γ = isLimit-ord γ limγ .fst {x = sucV c} {y = ξ} ξ∈sc
                    (limit-succ-mem γ c limγ c∈γ)
                d (inr q) = Empty.rec {A = ⟨ z ∈ˢ Sset (sucV c) ⟩} (∈-irrefl (sucV c) bad)
                  where
                  ξ≡sc : ξ ≡ sucV c
                  ξ≡sc = pr-inj q .fst
                  bad : ⟨ sucV c ∈ˢ sucV c ⟩
                  bad = subst (λ w → ⟨ w ∈ˢ sucV c ⟩) ξ≡sc ξ∈sc

    -- The segment at sucV c closes inside the top carrier and inside
    -- every parent limit carrier.
    segs∈W : ⟨ segs ∈ˢ W ⟩
    segs∈W = subst (λ w → ⟨ w ∈ˢ W ⟩) (Fof-f5 (F0 (rec-seg Rc) (F0 Ts Ts)) Ts)
      (Uγ.Fof-f5-limit (F0 (rec-seg Rc) (F0 Ts Ts)) Ts F0segcTs∈W Ts∈W)
      where
      module Uγ = UnionClosureLimit γ limγ
      sucVc∈γ : ⟨ sucV c ∈ˢ γ ⟩
      sucVc∈γ = limit-succ-mem γ c limγ c∈γ
      sucVc∈W : ⟨ sucV c ∈ˢ W ⟩
      sucVc∈W = Lset-mono {α = γ} {β = sucV (sucV c)}
        (limit-succ-mem γ (sucV c) limγ sucVc∈γ)
        (ord∈Lset-suc (sucV c) (suc-ord (mem-ord {A = γ} (isLimit-ord γ limγ) c c∈γ)))
      Ts∈W : ⟨ Ts ∈ˢ W ⟩
      Ts∈W = Lpr-limit γ limγ (sucV c) (Sset (sucV c)) sucVc∈W (mem∈L (sucV c) sucVc∈γ)
      F0TsTs∈W : ⟨ F0 Ts Ts ∈ˢ W ⟩
      F0TsTs∈W = Uγ.F0∈L Ts Ts Ts∈W Ts∈W
      F0segcTs∈W : ⟨ F0 (rec-seg Rc) (F0 Ts Ts) ∈ˢ W ⟩
      F0segcTs∈W = Uγ.F0∈L (rec-seg Rc) (F0 Ts Ts) (rec-seg∈W Rc) F0TsTs∈W

    nests : (σ : S) → ⟨ σ ∈ˢ γ ⟩ → ⟨ isLimit σ ⟩ → ⟨ sucV c ∈ˢ σ ⟩
          → ⟨ segs ∈ˢ Lset σ ⟩
    nests σ σ∈γ limσ sucVc∈σ = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩)
      (Fof-f5 (F0 (rec-seg Rc) (F0 Ts Ts)) Ts) result
      where
      module Uσ = UnionClosureLimit σ limσ
      c∈σ : ⟨ c ∈ˢ σ ⟩
      c∈σ = isLimit-ord σ limσ .fst {x = sucV c} {y = c} (self∈sucV c) sucVc∈σ
      segc∈Lσ : ⟨ rec-seg Rc ∈ˢ Lset σ ⟩
      segc∈Lσ = rec-nest Rc σ σ∈γ limσ c∈σ
      sucVc∈Lσ : ⟨ sucV c ∈ˢ Lset σ ⟩
      sucVc∈Lσ = Lset-mono {α = σ} {β = sucV (sucV c)}
        (limit-succ-mem σ (sucV c) limσ sucVc∈σ)
        (ord∈Lset-suc (sucV c) (mem-ord {A = σ} (isLimit-ord σ limσ) (sucV c) sucVc∈σ))
      Ts∈Lσ : ⟨ Ts ∈ˢ Lset σ ⟩
      Ts∈Lσ = Lpr-limit σ limσ (sucV c) (Sset (sucV c)) sucVc∈Lσ
        (memAt σ σ∈γ limσ (sucV c) sucVc∈σ)
      F0TsTs∈Lσ : ⟨ F0 Ts Ts ∈ˢ Lset σ ⟩
      F0TsTs∈Lσ = Uσ.F0∈L Ts Ts Ts∈Lσ Ts∈Lσ
      F0segcTs∈Lσ : ⟨ F0 (rec-seg Rc) (F0 Ts Ts) ∈ˢ Lset σ ⟩
      F0segcTs∈Lσ = Uσ.F0∈L (rec-seg Rc) (F0 Ts Ts) segc∈Lσ F0TsTs∈Lσ
      result : ⟨ Fof f5 (F0 (rec-seg Rc) (F0 Ts Ts)) Ts ∈ˢ Lset σ ⟩
      result = Uσ.Fof-f5-limit (F0 (rec-seg Rc) (F0 Ts Ts)) Ts F0segcTs∈Lσ Ts∈Lσ

  -- The recursion's value at a member η of γ, with the membership in γ
  -- threaded through the induction.
  Rec' : S → Type (ℓ-suc ℓ)
  Rec' η = ⟨ η ∈ˢ γ ⟩ → Rec η

  -- The recursion's limit case at a limit ξ: the witnesses below xi are
  -- the recursion's segments placed into Lset xi, and the pair family at
  -- xi is the nested limit-case machinery (Nested.Carried).
  limitRec : (ξ : S) → ⟨ ξ ∈ˢ γ ⟩ → ⟨ isLimit ξ ⟩
           → ((δ : S) → δ ∈ᵗ ξ → Rec' δ) → Rec ξ
  limitRec ξ ξ∈γ limξ recIH = C.record-value
    where
    module N = Nested ξ ξ∈γ limξ
    belowAt : (δ : S) → ⟨ δ ∈ˢ ξ ⟩
            → Σ[ s ∈ S ] (⟨ s ∈ˢ N.Wξ ⟩ × N.storyWξ s × ⟨ pr δ (Sset δ) ∈ˢ s ⟩)
    belowAt δ δ∈ξ = ( rec-seg Rδ
      , ( rec-nest Rδ ξ ξ∈γ limξ δ∈ξ , storyξ Rδ , rec-top∈ Rδ ) )
      where
      Rδ : Rec δ
      Rδ = recIH δ δ∈ξ (isLimit-ord γ limγ .fst {x = ξ} {y = δ} δ∈ξ ξ∈γ)
      storyξ : (R : Rec δ) → N.storyWξ (rec-seg R)
      storyξ R = ( rec-story R .fst
        , ( rec-story R .snd .fst
          , ( rec-story R .snd .snd .fst
            , ( ed , ( rec-story R .snd .snd .snd .snd .fst
              , rec-story R .snd .snd .snd .snd .snd ) ) ) ) )
        where
        sucVδ∈Wξ : ⟨ sucV δ ∈ˢ N.Wξ ⟩
        sucVδ∈Wξ = Lset-mono {α = ξ} {β = sucV (sucV δ)}
          (limit-succ-mem ξ (sucV δ) limξ (limit-succ-mem ξ δ limξ δ∈ξ))
          (ord∈Lset-suc (sucV δ) (suc-ord (mem-ord {A = ξ} (isLimit-ord ξ limξ) δ δ∈ξ)))
        in-dir : (a : S) → ⟨ a ∈ˢ sucV δ ⟩
               → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ rec-seg R ⟩ ∥₁
        in-dir a a∈suc = ∈sucV-elim {A = δ} {x = a} squash₁ a∈suc below top
          where
          below : ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ rec-seg R ⟩ ∥₁
          below a∈δ = ∣ Sset a
            , ( rec-seg∈ R (pr a (Sset a)) .snd
                ∣ inl (rec-P∈ R (pr a (Sset a)) .snd ∣ a , (a∈δ , refl) ∣₁) ∣₁ ) ∣₁
          top : a ≡ δ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ rec-seg R ⟩ ∥₁
          top a≡δ = ∣ Sset δ
            , subst (λ w → ⟨ pr w (Sset δ) ∈ˢ rec-seg R ⟩) (sym a≡δ) (rec-top∈ R) ∣₁
        out-dir : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ rec-seg R ⟩ ∥₁
                → ⟨ a ∈ˢ sucV δ ⟩
        out-dir a = PT.rec (snd (a ∈ˢ sucV δ)) go
          where
          go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ rec-seg R ⟩ → ⟨ a ∈ˢ sucV δ ⟩
          go (b , pr∈) = PT.rec (snd (a ∈ˢ sucV δ)) d
            (rec-seg∈ R (pr a b) .fst pr∈)
            where
            d : ⟨ pr a b ∈ˢ rec-P R ⟩ ⊎ (pr a b ≡ pr δ (Sset δ))
              → ⟨ a ∈ˢ sucV δ ⟩
            d (inl p∈P) = PT.rec (snd (a ∈ˢ sucV δ)) pgo
              (rec-P∈ R (pr a b) .fst p∈P)
              where
              pgo : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ δ ⟩ × (pr a b ≡ pr ζ (Sset ζ)))
                  → ⟨ a ∈ˢ sucV δ ⟩
              pgo (ζ , (ζ∈δ , q)) =
                subst (λ w → ⟨ w ∈ˢ sucV δ ⟩) (sym (pr-inj q .fst))
                  (∈sucV-inl {A = δ} {x = ζ} ζ∈δ)
            d (inr q) = subst (λ w → ⟨ w ∈ˢ sucV δ ⟩) (pr-inj (sym q) .fst)
              (self∈sucV δ)
        ed : N.KWξ.exactDom (rec-seg R)
        ed = ∣ sucV δ , ( sucVδ∈Wξ
          , suc-ord (mem-ord {A = ξ} (isLimit-ord ξ limξ) δ δ∈ξ)
          , in-dir , out-dir ) ∣₁
    module C = N.Carried (memAt ξ ξ∈γ limξ) belowAt

  recInd : (η : S) → ((δ : S) → δ ∈ᵗ η → Rec' δ) → Rec' η
  recInd η recIH η∈γ = go (ord-case η (limit-mem-ord γ limγ η η∈γ))
    where
    go : (η ≡ ∅) ⊎ (⟨ isSucc η ⟩ ⊎ ⟨ isLimit η ⟩) → Rec η
    go (inl z) = subst (λ w → Rec w) (sym z) zeroRec
    go (inr (inl (c , ordC , sη≡c))) = subst (λ w → Rec w) sη≡c
      (succRec c c∈γ (recIH c c∈η c∈γ))
      where
      c∈η : ⟨ c ∈ˢ η ⟩
      c∈η = subst (λ w → ⟨ c ∈ˢ w ⟩) sη≡c (self∈sucV c)
      c∈γ : ⟨ c ∈ˢ γ ⟩
      c∈γ = isLimit-ord γ limγ .fst {x = η} {y = c} c∈η η∈γ
    go (inr (inr limη)) = limitRec η η∈γ limη recIH

  rec : (η : S) → ⟨ η ∈ˢ γ ⟩ → Rec η
  rec η η∈γ = ∈-induction {P = Rec'} recInd η η∈γ

  -- The story formula renamed into the arity-4 environment, at the
  -- witness carrier W.
  embStory : Fin 2 → Fin 4
  embStory zero = suc (suc zero)
  embStory (suc zero) = suc zero

  storyRen : Formula ⟪ W ⟫ 4
  storyRen = renameFo embStory storyFormW

  module RenS = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ W))
    {ℓ} {⟪ W ⟫} KW.ι

  smEta : (x : KW.SM) → x ≡ KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst)
  smEta x = ΣPathP (p , q)
    where
    p : fst x ≡ fst (KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst))
    p = sym (∈-asFiber {a = fst x} {b = W} (snd x) .snd)
    q : PathP (λ i → ⟨ p i ∈ˢ W ⟩) (snd x)
           (snd (KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst)))
    q = isProp→PathP (λ i → snd (p i ∈ˢ W))
      (snd x) (snd (KW.ι (∈-asFiber {a = fst x} {b = W} (snd x) .fst)))

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

  -- The bounded family formula and its decode at the witness carrier W:
  -- the extension is exactly the pairs (η, Sset η) with η ∈ γ, witnessed
  -- by the carried sequence's segments below γ.
  segBody : Formula ⟪ W ⟫ 4
  segBody = (KW.PK.prAt (suc (suc (suc zero))) zero (suc zero))
         ∧̇ (KW.isOrdAt zero)
         ∧̇ storyRen
         ∧̇ (∃̇∈ (var (suc (suc zero)))
               (KW.PK.prAt zero (suc zero) (suc (suc zero))))

  segForm : Formula ⟪ W ⟫ 1
  segForm = ∃̇ (∃̇ (∃̇ segBody))

  -- The bound read: an exact-domain witness of a story at W is an ordinal
  -- member of γ, so its pairs' first components lie below γ.
  exactDom-ξ∈γ : (f : S) (η y : S) → storyW f → ⟨ pr η y ∈ˢ f ⟩ → ⟨ η ∈ˢ γ ⟩
  exactDom-ξ∈γ f η y h4 pr∈ = PT.rec (snd (η ∈ˢ γ)) dStep (h4 .snd .snd .snd .fst)
    where
    dStep : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ W ⟩ × IsOrd δ₀
             × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
             × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ₀ ⟩) )
          → ⟨ η ∈ˢ γ ⟩
    dStep (δ₀ , (δ₀∈u , ordδ₀ , _ , out-d)) =
      isLimit-ord γ limγ .fst {x = δ₀} {y = η} η∈δ₀ δ₀∈γ
      where
      η∈δ₀ : ⟨ η ∈ˢ δ₀ ⟩
      η∈δ₀ = out-d η ∣ y , pr∈ ∣₁
      δ₀∈γ : ⟨ δ₀ ∈ˢ γ ⟩
      δ₀∈γ = ord∈Lset→∈ γ (isLimit-ord γ limγ) δ₀ ordδ₀ δ₀∈u

  segForm-ok : (m : ⟪ W ⟫)
             → ⟨ (KW.ι m ∷ []) KW.⊨ᵐ segForm ⟩
             ⟷ ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η))) ∥₁
  segForm-ok m = (out , bwd)
    where
    δ₁ : Vec KW.SM 1
    δ₁ = KW.ι m ∷ []
    out : ⟨ δ₁ KW.⊨ᵐ segForm ⟩
        → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η))) ∥₁
    out sat = PT.rec squash₁ s₁ sat
      where
      s₁ : Σ[ sm ∈ KW.SM ] ⟨ (sm ∷ δ₁) KW.⊨ᵐ ∃̇ (∃̇ segBody) ⟩
         → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η))) ∥₁
      s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
        where
        s₂ : Σ[ ym ∈ KW.SM ] ⟨ (ym ∷ sm ∷ δ₁) KW.⊨ᵐ ∃̇ segBody ⟩
           → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η))) ∥₁
        s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
          where
          s₃ : Σ[ ηm ∈ KW.SM ] ⟨ (ηm ∷ ym ∷ sm ∷ δ₁) KW.⊨ᵐ segBody ⟩
             → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η))) ∥₁
          s₃ (ηm , (pr-sat , (ord-sat , (st-sat , pr∈-sat)))) =
            ∣ fst ηm , (η∈γ , x≡prηSη) ∣₁
            where
            δ₄ : Vec KW.SM 4
            δ₄ = ηm ∷ ym ∷ sm ∷ δ₁
            x≡prηy : ⟪ W ⟫↪ m ≡ pr (fst ηm) (fst ym)
            x≡prηy = KW.PK.prAt-out (suc (suc (suc zero))) zero (suc zero)
              δ₄ pr-sat
            st : storyW (fst sm)
            st = storyRen-ok δ₄ .fst st-sat
            prηy∈s : ⟨ pr (fst ηm) (fst ym) ∈ˢ fst sm ⟩
            prηy∈s = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
            η∈γ : ⟨ fst ηm ∈ˢ γ ⟩
            η∈γ = exactDom-ξ∈γ (fst sm) (fst ηm) (fst ym) st prηy∈s
            y≡Ssetη : fst ym ≡ Sset (fst ηm)
            y≡Ssetη = chain (fst sm) st (fst ηm) (fst ym) η∈γ prηy∈s
            x≡prηSη : ⟪ W ⟫↪ m ≡ pr (fst ηm) (Sset (fst ηm))
            x≡prηSη = x≡prηy ∙ cong₂ pr refl y≡Ssetη
    bwd : ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η))) ∥₁
        → ⟨ δ₁ KW.⊨ᵐ segForm ⟩
    bwd h = PT.rec (snd (δ₁ KW.⊨ᵐ segForm)) step₀ h
      where
      step₀ : Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η)))
            → ⟨ δ₁ KW.⊨ᵐ segForm ⟩
      step₀ (η , (η∈γ , x≡prηSη)) = ∣ sm , (∣ ym , (∣ ηm , body-sat ∣₁) ∣₁) ∣₁
        where
        w : Rec η
        w = rec η η∈γ
        η∈W : ⟨ η ∈ˢ W ⟩
        η∈W = Lset-mono {α = γ} {β = sucV η} (limit-succ-mem γ η limγ η∈γ)
          (ord∈Lset-suc η (mem-ord {A = γ} (isLimit-ord γ limγ) η η∈γ))
        sm ym ηm : KW.SM
        sm = KW.PK.pt (rec-seg w) (rec-seg∈W w)
        ym = KW.PK.pt (Sset η) (mem∈L η η∈γ)
        ηm = KW.PK.pt η η∈W
        δ₄ : Vec KW.SM 4
        δ₄ = ηm ∷ ym ∷ sm ∷ δ₁
        body-sat : ⟨ δ₄ KW.⊨ᵐ segBody ⟩
        body-sat = ( pr-sat , (ord-sat , (st-sat , pr∈-sat)) )
          where
          pr-sat : ⟨ δ₄ KW.⊨ᵐ KW.PK.prAt (suc (suc (suc zero))) zero (suc zero) ⟩
          pr-sat = KW.PK.prAt-in (suc (suc (suc zero))) zero (suc zero) δ₄
            x≡prηSη
          ord-sat : ⟨ δ₄ KW.⊨ᵐ KW.isOrdAt zero ⟩
          ord-sat = KW.isOrd-in zero δ₄
            (mem-ord {A = γ} (isLimit-ord γ limγ) η η∈γ)
          st-sat : ⟨ δ₄ KW.⊨ᵐ storyRen ⟩
          st-sat = storyRen-ok δ₄ .snd (rec-story w)
          pr∈-sat : ⟨ δ₄ KW.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                       (KW.PK.prAt zero (suc zero) (suc (suc zero))) ⟩
          pr∈-sat = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd
            (rec-top∈ w)

  -- P: the definable family of pairs below γ.
  module D = DefOf W

  P : S
  P = D.defSet segForm

  -- The decode at γ, in the Segment shape.
  P∈ : (p : S) → ⟨ p ∈ˢ P ⟩ ⟷ ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩
         × (p ≡ pr η (Sset η))) ∥₁
  P∈ p = (out , bwd)
    where
    out : ⟨ p ∈ˢ P ⟩ → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (p ≡ pr η (Sset η))) ∥₁
    out p∈ = PT.rec squash₁ go (segForm-ok m .fst sat)
      where
      m : ⟪ W ⟫
      m = ∈-asFiber {a = p} {b = W} (D.defSet⊆A segForm p p∈) .fst
      sat : ⟨ (KW.ι m ∷ []) KW.⊨ᵐ segForm ⟩
      sat = subst ⟨_⟩ (D.defSet-mem segForm m)
        (subst (λ w → ⟨ w ∈ˢ P ⟩) (sym (∈-asFiber {a = p} {b = W}
          (D.defSet⊆A segForm p p∈) .snd)) p∈)
      go : Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (⟪ W ⟫↪ m ≡ pr η (Sset η)))
         → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (p ≡ pr η (Sset η))) ∥₁
      go (η , (η∈γ , q)) = ∣ η
        , ( η∈γ , sym (∈-asFiber {a = p} {b = W} (D.defSet⊆A segForm p p∈) .snd) ∙ q ) ∣₁
    bwd : ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (p ≡ pr η (Sset η))) ∥₁
        → ⟨ p ∈ˢ P ⟩
    bwd = PT.rec (snd (p ∈ˢ P)) go
      where
      go : Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (p ≡ pr η (Sset η))) → ⟨ p ∈ˢ P ⟩
      go (η , (η∈γ , q)) = subst (λ w → ⟨ w ∈ˢ P ⟩) (sym q)
        (subst (λ w → ⟨ w ∈ˢ P ⟩) (fib .snd)
          (subst ⟨_⟩ (sym (D.defSet-mem segForm m))
            (segForm-ok m .snd ∣ η , (η∈γ , fib .snd) ∣₁)))
        where
        w : Rec η
        w = rec η η∈γ
        pr∈W : ⟨ pr η (Sset η) ∈ˢ W ⟩
        pr∈W = Wtr {x = rec-seg w} {y = pr η (Sset η)} (rec-top∈ w) (rec-seg∈W w)
        fib : Σ[ m ∈ ⟪ W ⟫ ] (⟪ W ⟫↪ m ≡ pr η (Sset η))
        fib = ∈-asFiber {a = pr η (Sset η)} {b = W} pr∈W
        m : ⟪ W ⟫
        m = fib .fst

  -- The carve (T193's landing shape).  No identification, no HF.
  ψBody : Formula ⟪ W ⟫ 4
  ψBody = storyRen
       ∧̇ (∃̇∈ (var (suc (suc zero)))
             (KW.PK.prAt zero (suc zero) (suc (suc zero))))
       ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero))

  ψ : Formula ⟪ W ⟫ 1
  ψ = ∃̇ (∃̇ (∃̇ ψBody))

  ψ-out : (x : ⟪ W ⟫) → ⟨ (KW.ι x ∷ []) KW.⊨ᵐ ψ ⟩
        → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset η ⟩) ∥₁
  ψ-out x = PT.rec squash₁ s₁
    where
    s₁ : Σ[ sm ∈ KW.SM ] ⟨ (sm ∷ KW.ι x ∷ []) KW.⊨ᵐ ∃̇ (∃̇ ψBody) ⟩
       → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset η ⟩) ∥₁
    s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
      where
      s₂ : Σ[ ym ∈ KW.SM ] ⟨ (ym ∷ sm ∷ KW.ι x ∷ []) KW.⊨ᵐ ∃̇ ψBody ⟩
         → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset η ⟩) ∥₁
      s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
        where
        s₃ : Σ[ ηm ∈ KW.SM ] ⟨ (ηm ∷ ym ∷ sm ∷ KW.ι x ∷ []) KW.⊨ᵐ ψBody ⟩
           → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset η ⟩) ∥₁
        s₃ (ηm , (st-sat , (pr∈-sat , x∈y-sat))) = ∣ fst ηm , (η∈γ , y∈Sη) ∣₁
          where
          δ₄ : Vec KW.SM 4
          δ₄ = ηm ∷ ym ∷ sm ∷ KW.ι x ∷ []
          st : storyW (fst sm)
          st = storyRen-ok δ₄ .fst st-sat
          prηy∈s : ⟨ pr (fst ηm) (fst ym) ∈ˢ fst sm ⟩
          prηy∈s = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
          x∈y : ⟨ ⟪ W ⟫↪ x ∈ˢ fst ym ⟩
          x∈y = x∈y-sat
          η∈γ : ⟨ fst ηm ∈ˢ γ ⟩
          η∈γ = exactDom-ξ∈γ (fst sm) (fst ηm) (fst ym) st prηy∈s
          y≡Ssetη : fst ym ≡ Sset (fst ηm)
          y≡Ssetη = chain (fst sm) st (fst ηm) (fst ym) η∈γ prηy∈s
          y∈Sη : ⟨ ⟪ W ⟫↪ x ∈ˢ Sset (fst ηm) ⟩
          y∈Sη = subst (λ w → ⟨ ⟪ W ⟫↪ x ∈ˢ w ⟩) y≡Ssetη x∈y

  ψ-in : (x : ⟪ W ⟫)
       → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset η ⟩) ∥₁
       → ⟨ (KW.ι x ∷ []) KW.⊨ᵐ ψ ⟩
  ψ-in x = PT.rec (snd ((KW.ι x ∷ []) KW.⊨ᵐ ψ)) go
    where
    go : Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × ⟨ ⟪ W ⟫↪ x ∈ˢ Sset η ⟩)
       → ⟨ (KW.ι x ∷ []) KW.⊨ᵐ ψ ⟩
    go (η , (η∈γ , x∈Sη)) = ∣ sm , (∣ ym , (∣ ηm , body-sat ∣₁) ∣₁) ∣₁
      where
      w : Rec η
      w = rec η η∈γ
      Sη∈W : ⟨ Sset η ∈ˢ W ⟩
      Sη∈W = mem∈L η η∈γ
      η∈W : ⟨ η ∈ˢ W ⟩
      η∈W = Lset-mono {α = γ} {β = sucV η} (limit-succ-mem γ η limγ η∈γ)
        (ord∈Lset-suc η (mem-ord {A = γ} (isLimit-ord γ limγ) η η∈γ))
      sm ym ηm : KW.SM
      sm = KW.PK.pt (rec-seg w) (rec-seg∈W w)
      ym = KW.PK.pt (Sset η) Sη∈W
      ηm = KW.PK.pt η η∈W
      δ₄ : Vec KW.SM 4
      δ₄ = ηm ∷ ym ∷ sm ∷ KW.ι x ∷ []
      body-sat : ⟨ δ₄ KW.⊨ᵐ ψBody ⟩
      body-sat = ( st-sat , (pr∈-sat , x∈y-sat) )
        where
        st-sat : ⟨ δ₄ KW.⊨ᵐ storyRen ⟩
        st-sat = storyRen-ok δ₄ .snd (rec-story w)
        pr∈-sat : ⟨ δ₄ KW.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                     (KW.PK.prAt zero (suc zero) (suc (suc zero))) ⟩
        pr∈-sat = KW.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd (rec-top∈ w)
        x∈y-sat : ⟨ δ₄ KW.⊨ᵐ (var (suc (suc (suc zero))) ∈̇ var (suc zero)) ⟩
        x∈y-sat = x∈Sη

  -- The carve clause against the tower's limit union.
  carve-out : (y : S) → ⟨ y ∈ˢ D.defSet ψ ⟩ → ⟨ y ∈ˢ Sset γ ⟩
  carve-out y y∈ = PT.rec (snd (y ∈ˢ Sset γ)) aStep (ψ-out m sat)
    where
    m : ⟪ W ⟫
    m = ∈-asFiber {a = y} {b = W} (D.defSet⊆A ψ y y∈) .fst
    q : ⟪ W ⟫↪ m ≡ y
    q = ∈-asFiber {a = y} {b = W} (D.defSet⊆A ψ y y∈) .snd
    sat : ⟨ (KW.ι m ∷ []) KW.⊨ᵐ ψ ⟩
    sat = subst ⟨_⟩ (D.defSet-mem ψ m)
      (subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (sym q) y∈)
    aStep : Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × ⟨ ⟪ W ⟫↪ m ∈ˢ Sset η ⟩)
          → ⟨ y ∈ˢ Sset γ ⟩
    aStep (η , (η∈γ , x∈Sη)) = Sset-mono {α = γ} {β = η} η∈γ
      y (subst (λ w → ⟨ w ∈ˢ Sset η ⟩) q x∈Sη)

  carve-in : (y : S) → ⟨ y ∈ˢ Sset γ ⟩ → ⟨ y ∈ˢ D.defSet ψ ⟩
  carve-in y y∈S = PT.rec (snd (y ∈ˢ D.defSet ψ)) step₁
    (Sset-union-limit γ limγ y y∈S)
    where
    step₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ y ∈ˢ Sset (sucV δ) ⟩)
          → ⟨ y ∈ˢ D.defSet ψ ⟩
    step₁ (δ , (δ∈γ , y∈Sδ')) = subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (fib .snd)
      (subst ⟨_⟩ (sym (D.defSet-mem ψ (fib .fst)))
        (ψ-in (fib .fst) ∣ sucV δ , ( sucVδ∈γ , y∈Sξ' ) ∣₁))
      where
      sucVδ∈γ : ⟨ sucV δ ∈ˢ γ ⟩
      sucVδ∈γ = limit-succ-mem γ δ limγ δ∈γ
      y∈W : ⟨ y ∈ˢ W ⟩
      y∈W = Ltr γ {x = Sset (sucV δ)} {y = y} y∈Sδ'
        (mem∈L (sucV δ) sucVδ∈γ)
      fib : Σ[ x ∈ ⟪ W ⟫ ] (⟪ W ⟫↪ x ≡ y)
      fib = ∈-asFiber {a = y} {b = W} y∈W
      y∈Sξ' : ⟨ ⟪ W ⟫↪ (fib .fst) ∈ˢ Sset (sucV δ) ⟩
      y∈Sξ' = subst (λ w → ⟨ w ∈ˢ Sset (sucV δ) ⟩) (sym (fib .snd)) y∈Sδ'

  carveClause : D.defSet ψ ≡ Sset γ
  carveClause = extensionalV (λ x → ⇔toPath (carve-out x) (carve-in x))

  carve∈𝒟ₒ : ⟨ Sset γ ∈ˢ 𝒟ₒ W ⟩
  carve∈𝒟ₒ = 𝒟ₒ-intro W (Sset γ) ∣ ψ , carveClause ∣₁

  -- The landing, one stage up: the STEP's conclusion at the limit.
  landing : ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩
  landing = 𝒟ₒ⊆Lsuc γ (Sset γ) carve∈𝒟ₒ

  -- The placements through the geometry and transitivity.
  δγ : S
  δγ = sucV (sucV (sucV γ))

  δγ-ord : IsOrd δγ
  δγ-ord = suc-ord (suc-ord (suc-ord (isLimit-ord γ limγ)))

  sucVγ∈δγ : ⟨ sucV γ ∈ˢ δγ ⟩
  sucVγ∈δγ = δγ-ord .fst {x = sucV (sucV γ)} {y = sucV γ}
    (self∈sucV (sucV γ)) (self∈sucV (sucV (sucV γ)))

  sucVγ∈C : ⟨ sucV γ ∈ˢ C ⟩
  sucVγ∈C = Ctr {x = Lset δγ} {y = sucV γ}
    (Lset-mono {α = δγ} {β = sucV (sucV γ)} (self∈sucV (sucV (sucV γ)))
      (ord∈Lset-suc (sucV γ) (suc-ord (isLimit-ord γ limγ)))) Tgeom

  P∈C : ⟨ P ∈ˢ C ⟩
  P∈C = Ctr {x = Lset δγ} {y = P}
    (Lset-mono {α = δγ} {β = sucV γ} sucVγ∈δγ
      (𝒟ₒ⊆Lsuc γ P (𝒟ₒ-intro W P ∣ segForm , refl ∣₁))) Tgeom

  -- The top pair through the Kuratowski coding.
  Tγ : S
  Tγ = pr γ (Sset γ)

  Tγ∈Lδγ : ⟨ Tγ ∈ˢ Lset δγ ⟩
  Tγ∈Lδγ = subst (λ w → ⟨ w ∈ˢ Lset δγ ⟩) (sym pr≡F0)
    (Lpair (sucV (sucV γ)) (F0 γ γ) (F0 γ (Sset γ)) F0γγ∈L F0γSγ∈L)
    where
    γ∈Lsucγ : ⟨ γ ∈ˢ Lset (sucV γ) ⟩
    γ∈Lsucγ = ord∈Lset-suc γ (isLimit-ord γ limγ)
    F0γγ∈L : ⟨ F0 γ γ ∈ˢ Lset (sucV (sucV γ)) ⟩
    F0γγ∈L = Lpair (sucV γ) γ γ γ∈Lsucγ γ∈Lsucγ
    F0γSγ∈L : ⟨ F0 γ (Sset γ) ∈ˢ Lset (sucV (sucV γ)) ⟩
    F0γSγ∈L = Lpair (sucV γ) γ (Sset γ) γ∈Lsucγ landing
    pr≡F0 : pr γ (Sset γ) ≡ F0 (F0 γ γ) (F0 γ (Sset γ))
    pr≡F0 = sym (cong (λ w → ⁅ w , ⁅ γ , Sset γ ⁆ ⁆) (pair-singleton γ))

  Tγ∈C : ⟨ Tγ ∈ˢ C ⟩
  Tγ∈C = Ctr {x = Lset δγ} {y = Tγ} Tγ∈Lδγ Tgeom

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

  -- The segment P ∪ {Tγ} in the carrier.
  segγ : S
  segγ = F5 (F0 P (F0 Tγ Tγ)) Tγ

  segγ∈C : ⟨ segγ ∈ˢ C ⟩
  segγ∈C = Ctr {x = Lset (sucV (sucV (sucV δγ)))}
    {y = segγ} segγ∈Lδ' segGeom'
    where
    F0TγTγ∈L : ⟨ F0 Tγ Tγ ∈ˢ Lset (sucV δγ) ⟩
    F0TγTγ∈L = Lpair δγ Tγ Tγ Tγ∈Lδγ Tγ∈Lδγ
    F0PTγTγ∈L : ⟨ F0 P (F0 Tγ Tγ) ∈ˢ Lset (sucV (sucV δγ)) ⟩
    F0PTγTγ∈L = Lpair (sucV δγ) P (F0 Tγ Tγ)
      (Lset-mono {α = sucV δγ} {β = δγ} (self∈sucV δγ) P∈Lδγ) F0TγTγ∈L
      where
      P∈Lδγ : ⟨ P ∈ˢ Lset δγ ⟩
      P∈Lδγ = Lset-mono {α = δγ} {β = sucV γ} sucVγ∈δγ
        (𝒟ₒ⊆Lsuc γ P (𝒟ₒ-intro W P ∣ segForm , refl ∣₁))
    postulate
      segγ∈Lδ' : ⟨ segγ ∈ˢ Lset (sucV (sucV (sucV δγ))) ⟩
      segGeom' : ⟨ Lset (sucV (sucV (sucV δγ))) ∈ˢ C ⟩

  -- The STEP's segment at γ, its six-clause story at the carrier C.
  module StC = Story C Ctr stepSub graphOf graph-out graph-in bigOr bigOr-in
    bigOr-out eqFrame eqFrame-ok

  module Seg = StC.Segment γ limγ P P∈ sucVγ∈C

  -- The sixth clause at the segment at γ: at a limit member a the decode
  -- reads the value below, and the top case is the machinery's own limit
  -- clause (T229's structure).
  segLimitClause : StC.limitClause Seg.seg
  segLimitClause a b lima pr∈ z = PT.rec isPropRhsa go
    (Seg.seg∈ (pr a b) .fst pr∈)
    where
    rhs : S → Type (ℓ-suc ℓ)
    rhs i = ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ i ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
    isPropRhsa : isProp (⟨ z ∈ˢ b ⟩ ⟷ rhs a)
    isPropRhsa = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → snd (z ∈ˢ b)))
    go : ⟨ pr a b ∈ˢ P ⟩ ⊎ (pr a b ≡ Tγ) → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
    go (inl p∈P) = PT.rec isPropRhsa aStep (P∈ (pr a b) .fst p∈P)
      where
      aStep : Σ[ η ∈ S ] (⟨ η ∈ˢ γ ⟩ × (pr a b ≡ pr η (Sset η)))
            → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
      aStep (η , (η∈γ , q)) = (fwd , bwd)
        where
        a≡η : a ≡ η
        a≡η = pr-inj q .fst
        b≡Sη : b ≡ Sset η
        b≡Sη = pr-inj q .snd
        a∈γ : ⟨ a ∈ˢ γ ⟩
        a∈γ = subst (λ w → ⟨ w ∈ˢ γ ⟩) (sym a≡η) η∈γ
        b≡Sa : b ≡ Sset a
        b≡Sa = b≡Sη ∙ cong Sset (sym a≡η)
        fwd : ⟨ z ∈ˢ b ⟩ → rhs a
        fwd z∈b = PT.map go' (Sset-union-limit a lima z
          (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Sa z∈b))
          where
          go' : Σ[ δ ∈ S ] (⟨ δ ∈ˢ a ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
              → Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩
                   × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
          go' (δ , (δ∈a , z∈Sδ')) = sucV δ , ( δ'∈a
            , ∣ Sset (sucV δ) , ( prδ'∈ , z∈Sδ' ) ∣₁ )
            where
            δ'∈a : ⟨ sucV δ ∈ˢ a ⟩
            δ'∈a = limit-succ-mem a δ lima δ∈a
            δ'∈γ : ⟨ sucV δ ∈ˢ γ ⟩
            δ'∈γ = isLimit-ord γ limγ .fst {x = a} {y = sucV δ} δ'∈a a∈γ
            prδ'∈ : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ Seg.seg ⟩
            prδ'∈ = Seg.prξSξ∈seg (sucV δ) δ'∈γ
        bwd : rhs a → ⟨ z ∈ˢ b ⟩
        bwd = PT.rec (snd (z ∈ˢ b)) go'
          where
          go' : Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩
               × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
              → ⟨ z ∈ˢ b ⟩
          go' (η , (η∈a , rest)) = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Sa)
            (PT.rec (snd (z ∈ˢ Sset a)) s₂ rest)
            where
            s₂ : Σ[ w ∈ S ] (⟨ pr η w ∈ˢ Seg.seg ⟩ × ⟨ z ∈ˢ w ⟩)
               → ⟨ z ∈ˢ Sset a ⟩
            s₂ (w , (pr∈ , z∈w)) = PT.rec (snd (z ∈ˢ Sset a)) d
              (Seg.seg∈ (pr η w) .fst pr∈)
              where
              d : ⟨ pr η w ∈ˢ P ⟩ ⊎ (pr η w ≡ Tγ) → ⟨ z ∈ˢ Sset a ⟩
              d (inl p∈P) = PT.rec (snd (z ∈ˢ Sset a)) pgo (P∈ (pr η w) .fst p∈P)
                where
                pgo : Σ[ η' ∈ S ] (⟨ η' ∈ˢ γ ⟩ × (pr η w ≡ pr η' (Sset η')))
                    → ⟨ z ∈ˢ Sset a ⟩
                pgo (η' , (η'∈γ , q)) = Sset-mono {α = a} {β = η} η∈a z z∈Sη
                  where
                  w≡Sη : w ≡ Sset η
                  w≡Sη = subst (λ t → w ≡ Sset t) (sym (pr-inj q .fst))
                    (pr-inj q .snd)
                  z∈Sη : ⟨ z ∈ˢ Sset η ⟩
                  z∈Sη = subst (λ t → ⟨ z ∈ˢ t ⟩) (w≡Sη) z∈w
              d (inr q) = Empty.rec {A = ⟨ z ∈ˢ Sset a ⟩} (∈-irrefl γ γ∈γ)
                where
                η≡γ : η ≡ γ
                η≡γ = pr-inj q .fst
                γ∈a : ⟨ γ ∈ˢ a ⟩
                γ∈a = subst (λ t → ⟨ t ∈ˢ a ⟩) η≡γ η∈a
                γ∈γ : ⟨ γ ∈ˢ γ ⟩
                γ∈γ = isLimit-ord γ limγ .fst {x = a} {y = γ} γ∈a a∈γ
    go (inr q) = (fwd , bwd)
      where
      a≡γ : a ≡ γ
      a≡γ = pr-inj q .fst
      b≡Sγ : b ≡ Sset γ
      b≡Sγ = pr-inj q .snd
      fwd : ⟨ z ∈ˢ b ⟩ → rhs a
      fwd z∈b = subst rhs (sym a≡γ)
        (Seg.segLimit₀ z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Sγ z∈b))
      bwd : rhs a → ⟨ z ∈ˢ b ⟩
      bwd h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Sγ)
        (Seg.segLimit₀ z .snd (subst rhs a≡γ h))

  -- The six-clause story at the segment at γ.
  segmentStory : StC.story Seg.seg
  segmentStory = ( Seg.segPairhood , ( Seg.segSingleValued
    , ( Seg.segZeroClause , ( Seg.segDom₀
      , ( Seg.segSuccClause , segLimitClause ) ) ) ) )
