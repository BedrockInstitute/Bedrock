{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T182] The D22 gate: instantiate the below-lim first instance
-- (T159, verified whole at 57.8 s) at the SECOND limit carrier
-- β₁ = +ω β₀, and measure the delta only.  The first instance's carrier
-- β₀ = +ω a₀ contains the first limit ordinal a₀ = +ω ∅ below it; the
-- second instance's carrier β₁ contains the limit ordinal β₀ below it,
-- which the first instance never tested.  Untracked probe, no git, no
-- master, Everything untouched, T159's file untouched.  The graph layer
-- is consumed only through the delivered probes T126/T127 (via the
-- patched scratch tree /tmp/t182-scratch.*, whose StepInL import of
-- Bridge's ext-⊆/empty-⊆ was repointed at L.TowerKit after T180's
-- in-flight Bridge rebuild moved those names).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT182 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl; pair-singleton )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import Cubical.Data.FinData.Base using ( Fin; toℕ; zero; suc )
open import Cubical.Data.FinData.Properties
  using ( fromℕ'; toFromId' )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Order using ( ≤-refl )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Functions.Logic as Logic
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2 )
open import Cubical.Data.Sigma.Properties using ( Σ≡Prop; ΣPathP )
open import Cubical.Foundations.Prelude using ( isProp→PathP )
open import Cubical.Foundations.Prelude using ( PathP )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈-asFiber; _∈ₛ_; _≡ₕ_; extensionality )
  renaming ( _⊆_ to _⊆ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; ⋃_; union-ax; ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; Lset-layer; layer-trans; isTransV; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using
  ( ∅-ord; numeral-ord; numeral-mem; #∈ω; ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( +ω; +ω-limit; +ω-iter; +ω-in; +ω-out; +ω-mem; +ω-ord; sucIter; sucIter-ord )
open import L.Rud.Step {ℓ} lem ∅
  using ( Sset; Sset-suc; Sset-zero; Sset-mono; limit-succ-mem; step-in-self
        ; Op16; Fof; StepArm; arm-member; arm-self; arm-image; step-out )
  renaming ( step to rudStep )
open import L.TowerKit {ℓ} lem ∅ using ( 𝒟ₒ⊆Lsuc; Lpair; Ltr; suc⁴ )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( Lset∈Lsuc; Lpr-limit; ∅∈Lset; Sset-union-limit; Sset-union-in
  ; Lstage₂; Lval; suc⁴-up; suc⁴∈ )
open import L.Rud.StepInL {ℓ} lem ∅ using ( module Slot; module Desc; values∈L )
open import L.Rud.Finite {ℓ} lem ∅ using ( limω )
open import L.Rud.HF {ℓ} lem ∅ using ( numeral∈Lsetω )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in )
open import L.Rud.Ops {ℓ} using ( F0; F5; F0-spec; F5-spec; F5-RHS )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
import ProbeT128 {ℓ} lem as PT128
import ProbeT127 {ℓ} lem ∅ as PT127
import ProbeBelowLim {ℓ} lem ∅ as PB125

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open PT128 using ( a₀; β₀; a₀-ord; firstLimit; β₀-lim; limitClause; C; utr; a₀∈C )

open import L.Rud.StepStory {ℓ} lem ∅ (Lset β₀) (layer-trans (Lset-layer β₀))
  using ( module Clause )

-- ---------------------------------------------------------------------------
-- The second limit carrier β₁ = +ω β₀ and its certificates.  β₁ is a limit
-- ordinal, and β₀ (itself a limit ordinal, the first instance's carrier
-- index) sits strictly below it: this is exactly the configuration the
-- first instance never tested.
-- ---------------------------------------------------------------------------

β₁ : S
β₁ = +ω β₀

β₀-ord : IsOrd β₀
β₀-ord = β₀-lim .fst

β₁-ord : IsOrd β₁
β₁-ord = +ω-ord β₀ β₀-ord

β₁-lim : ⟨ isLimit β₁ ⟩
β₁-lim = +ω-limit β₀ β₀-ord

β₀∈β₁ : ⟨ β₀ ∈ˢ β₁ ⟩
β₀∈β₁ = +ω-mem β₀

-- The kits: K0 at the WITNESS carrier Lset β₀ (the first instance's
-- carrier; its story serves the pairs-below-β₀ formula and the copied
-- segment construction), KT at the TARGET carrier Lset β₁ (the second
-- instance's story), Kω at Lset ω (the formula layer; opened because the
-- formula machinery (SM, ι, PK, isOrdAt, pair∈, ...) is used at Lset ω).
module K0 = LevelKit C utr
module KT = LevelKit (Lset β₁) (layer-trans (Lset-layer β₁))
module Kω = LevelKit (Lset ω) (layer-trans (Lset-layer ω))
open Kω public

-- ---------------------------------------------------------------------------
-- Copied from T159 (Part A): the numeral alias, extensionality, a₀ = ω, the
-- one-way successor clause, the six-clause story at the witness carrier K0,
-- and the two chain theorems (numeral chain, first-limit chain).  All of
-- these are carrier-generic in effect: nothing names the target carrier.
-- ---------------------------------------------------------------------------

nk : ℕ → S
nk k = # k

_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

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

-- The one-way successor clause (T159's, the meta-level shape of
-- StepStory's clause, carrier-independent).
succClause : S → Type (ℓ-suc ℓ)
succClause f = (a : S) (c : S) (b : S) → ⟨ pr a c ∈ˢ f ⟩
             → ⟨ pr (sucV a) b ∈ˢ f ⟩ → (b ≡ rudStep c)

-- The six-clause story at the WITNESS carrier (T159's story, verbatim):
-- the kit's four shared clauses at Lset β₀, the one-way successor clause,
-- and T128's limit clause.
story : S → Type (ℓ-suc ℓ)
story f = K0.pairhood f × K0.singleValued f × K0.zeroClause f × K0.exactDom f
        × succClause f × limitClause f

-- The six-clause story at the TARGET carrier Lset β₁: the same shape at
-- KT.  This is the second instance's story predicate.
story₁ : S → Type (ℓ-suc ℓ)
story₁ f = KT.pairhood f × KT.singleValued f × KT.zeroClause f × KT.exactDom f
         × succClause f × limitClause f

-- The numeral chain (T159's, verbatim): a witness story's value at a
-- numeral index is forced to Sset of the index.
chainValue : (f : S) → story f → (a x : S) → ⟨ a ∈ˢ ω ⟩
           → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Sset a
chainValue f st a x a∈ω ax∈f = PT.rec (setIsSet x (Sset a)) go a∈ω
  where
  h4 : K0.exactDom f
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
      x≡stepS#n : x ≡ rudStep (Sset (# n))
      x≡stepS#n = PT.rec (setIsSet x (rudStep (Sset (# n)))) cStep
        (in-dir (# n) n∈δ)
        where
        cStep : Σ[ c ∈ S ] ⟨ pr (# n) c ∈ˢ f ⟩ → x ≡ rudStep (Sset (# n))
        cStep (c , prnc) = st .snd .snd .snd .snd .fst
          (# n) (Sset (# n)) x prn px
          where
          prn : ⟨ pr (# n) (Sset (# n)) ∈ˢ f ⟩
          prn = subst (λ w → ⟨ pr (# n) w ∈ˢ f ⟩) (chainNum n c prnc) prnc
      step≡Sset : rudStep (Sset (# n)) ≡ Sset (# (suc n))
      step≡Sset = sym (Sset-suc (# n))
  go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower m) ≡ a) → x ≡ Sset a
  go (m , q) = subst (λ w → x ≡ Sset w) q
    (chainNum (lower m) x ax∈f')
    where
    ax∈f' : ⟨ pr (# (lower m)) x ∈ˢ f ⟩
    ax∈f' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) (sym q) ax∈f

-- The chain step at the first limit index a₀ (T159's, verbatim): a
-- witness story's value at a₀ is forced to Sset a₀, through the limit
-- clause's union reading and the numeral chain.
chainLimit : (f : S) → story f → (x : S) → ⟨ pr a₀ x ∈ˢ f ⟩ → x ≡ Sset a₀
chainLimit f st x ax∈f = ext-⊆ {x} {Sset a₀} x⊆S Sa₀⊆x
  where
  h4 : K0.exactDom f
  h4 = st .snd .snd .snd .fst
  lc : (a b : S) → ⟨ isLimit a ⟩ → ⟨ pr a b ∈ˢ f ⟩
     → (z : S) → ⟨ z ∈ˢ b ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
          × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
  lc = st .snd .snd .snd .snd .snd
  x⊆S : x ⊆ Sset a₀
  x⊆S z z∈x = PT.rec (snd (z ∈ˢ Sset a₀)) step₁
    (lc a₀ x firstLimit ax∈f z .fst z∈x)
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
    (Sset-union-limit a₀ firstLimit z z∈Sa₀)
    where
    step₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ a₀ ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
          → ⟨ z ∈ˢ x ⟩
    step₁ (δ , (δ∈a₀ , z∈Sδ')) = PT.rec (snd (z ∈ˢ x)) step₂ h4
      where
      δ'∈a₀ : ⟨ sucV δ ∈ˢ a₀ ⟩
      δ'∈a₀ = limit-succ-mem a₀ δ firstLimit δ∈a₀
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
        step₃ (b , pδ'b) = lc a₀ x firstLimit ax∈f z .snd
          ∣ sucV δ , ( δ'∈a₀ , ∣ Sset (sucV δ) , ( pδ'b' , z∈Sδ' ) ∣₁ ) ∣₁
          where
          b≡Sδ' : b ≡ Sset (sucV δ)
          b≡Sδ' = chainValue f st (sucV δ) b
            (subst (λ w → ⟨ sucV δ ∈ˢ w ⟩) a₀≡ω δ'∈a₀) pδ'b
          pδ'b' : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ f ⟩
          pδ'b' = subst (λ w → ⟨ pr (sucV δ) w ∈ˢ f ⟩) b≡Sδ' pδ'b

-- ---------------------------------------------------------------------------
-- NEW CONTENT (the first new obligation above the first limit): the chain
-- over β₀ = +ω a₀.  The first instance's chain forced values at the
-- members of a₀ (numerals, chainValue) and at a₀ itself (chainLimit); the
-- second instance's segment domain is sucV β₀, whose members above a₀ are
-- the finite iterates sucIter m a₀.  Their values are forced one successor
-- step per iterate (chainIter), and a general membership a ∈ β₀ splits on
-- the +ω-out iterate (chainAbove).  The first instance never needed this:
-- its witness stories' domains were sucV a₀, and every domain member was
-- covered by the numeral chain plus the single first-limit step.
-- ---------------------------------------------------------------------------

chainIter : (f : S) → story f → (m : ℕ) (x : S)
          → ⟨ pr (sucIter m a₀) x ∈ˢ f ⟩ → x ≡ Sset (sucIter m a₀)
chainIter f st zero x px = chainLimit f st x px
chainIter f st (suc k) x px = PT.rec (setIsSet x (Sset (sucIter (suc k) a₀))) dStep h4
  where
  h4 : K0.exactDom f
  h4 = st .snd .snd .snd .fst
  dStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ C ⟩ × IsOrd δ
           × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
           × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
        → x ≡ Sset (sucIter (suc k) a₀)
  dStep (δ , (δ∈u , ordδ , in-dir , out-dir)) =
    PT.rec (setIsSet x (Sset (sucIter (suc k) a₀))) cStep
      (in-dir (sucIter k a₀) η∈δ)
    where
    sucη∈δ : ⟨ sucV (sucIter k a₀) ∈ˢ δ ⟩
    sucη∈δ = out-dir (sucV (sucIter k a₀)) ∣ x , px ∣₁
    η∈δ : ⟨ sucIter k a₀ ∈ˢ δ ⟩
    η∈δ = ordδ .fst {x = sucV (sucIter k a₀)} {y = sucIter k a₀}
      (self∈sucV (sucIter k a₀)) sucη∈δ
    cStep : Σ[ c ∈ S ] ⟨ pr (sucIter k a₀) c ∈ˢ f ⟩
          → x ≡ Sset (sucIter (suc k) a₀)
    cStep (c , prηc) =
      succ ∙ cong rudStep c≡Sη ∙ sym (Sset-suc (sucIter k a₀))
      where
      succ : x ≡ rudStep c
      succ = st .snd .snd .snd .snd .fst (sucIter k a₀) c x prηc px
      c≡Sη : c ≡ Sset (sucIter k a₀)
      c≡Sη = chainIter f st k c prηc

chainAbove : (f : S) → story f → (n : ℕ) → (a x : S)
           → ⟨ a ∈ˢ sucIter (suc n) a₀ ⟩ → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Sset a
chainAbove f st zero a x a∈suca₀ ax∈f =
  ∈sucV-elim (setIsSet x (Sset a)) a∈suca₀ below top
  where
  below : ⟨ a ∈ˢ a₀ ⟩ → x ≡ Sset a
  below a∈a₀ = chainValue f st a x (subst (λ w → ⟨ a ∈ˢ w ⟩) a₀≡ω a∈a₀) ax∈f
  top : a ≡ a₀ → x ≡ Sset a
  top a≡a₀ = subst (λ w → x ≡ Sset w) (sym a≡a₀)
    (chainLimit f st x (subst (λ w → ⟨ pr w x ∈ˢ f ⟩) a≡a₀ ax∈f))
chainAbove f st (suc k) a x a∈iter ax∈f =
  ∈sucV-elim (setIsSet x (Sset a)) a∈iter below top
  where
  below : ⟨ a ∈ˢ sucIter (suc k) a₀ ⟩ → x ≡ Sset a
  below a∈k = chainAbove f st k a x a∈k ax∈f
  top : a ≡ sucIter (suc k) a₀ → x ≡ Sset a
  top a≡iter = subst (λ w → x ≡ Sset w) (sym a≡iter)
    (chainIter f st (suc k) x
      (subst (λ w → ⟨ pr w x ∈ˢ f ⟩) a≡iter ax∈f))

-- The chain at the second limit index: every domain member of a witness
-- story at Lset β₀ has its value forced to Sset of itself.
chainβ₀ : (f : S) → story f → (a x : S) → ⟨ a ∈ˢ β₀ ⟩
        → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Sset a
chainβ₀ f st a x a∈β₀ ax∈f = PT.rec (setIsSet x (Sset a)) go (+ω-out a₀ a a∈β₀)
  where
  go : Σ[ n ∈ ℕ ] ⟨ a ∈ˢ sucIter (suc n) a₀ ⟩ → x ≡ Sset a
  go (n , a∈iter) = chainAbove f st n a x a∈iter ax∈f

-- ---------------------------------------------------------------------------
-- The top pair at the second limit index: T' = pr β₀ (Sset β₀).  The
-- first component sits in the next L-stage by the ordinal step (delivered);
-- the second component Sset β₀ ∈ Lset (sucV β₀) is the below-lim residue
-- at the new limit pair.  It is NOT delivered: Bridge's BelowLim is a
-- Reduce-module hypothesis (src/L/Rud/Bridge.lagda.md:1040), the successor
-- case of RudBelow needs a limit γ (sucV β₀ is not a limit), and the
-- first-limit identification Ssetω≡Lsetω (ProbeBelowLim.agda:282) holds
-- only at ω — it is false at general limits (recorded at
-- src/L/Rud/Bridge.lagda.md:475).  The honest second instance is blocked
-- here until that residue is discharged at (γ = β₁, β = β₀).
-- ---------------------------------------------------------------------------

T' : S
T' = pr β₀ (Sset β₀)

β₀∈Lsucβ₀ : ⟨ β₀ ∈ˢ Lset (sucV β₀) ⟩
β₀∈Lsucβ₀ = ord∈Lset-suc β₀ β₀-ord

F0β₀β₀∈L : ⟨ F0 β₀ β₀ ∈ˢ Lset (sucV (sucV β₀)) ⟩
F0β₀β₀∈L = Lpair (sucV β₀) β₀ β₀ β₀∈Lsucβ₀ β₀∈Lsucβ₀

-- The R-40 climb for the eventual placement of T' (and the segment) in
-- Lset β₁: the union closure lands at Lset (sucV (sucV (sucV β₀))), so the
-- ordinal witness climbs by small closures from +ω-iter 3 β₀, exactly the
-- T154/T159 shape.
δ₁ : S
δ₁ = sucV (sucV (sucV β₀))

δ₁-ord : IsOrd δ₁
δ₁-ord = suc-ord (suc-ord (suc-ord β₀-ord))

δ₁∈β₁ : ⟨ δ₁ ∈ˢ β₁ ⟩
δ₁∈β₁ = +ω-iter 3 β₀

-- ---------------------------------------------------------------------------
-- The witness-carrier machinery the pairs-below-β₀ formula needs: the
-- graph layer at Lset β₀ (the second instance's successor clause), and the
-- six-clause story formula with its two-way decode at Lset β₀.  T126
-- assembled this layer at Lset ω; here it is re-assembled at Lset β₀, the
-- witness carrier of the second instance.
-- ---------------------------------------------------------------------------

∅∈β₀ : ⟨ ∅ ∈ˢ β₀ ⟩
∅∈β₀ = β₀-ord .fst {x = a₀} {y = ∅} ∅∈a₀ a₀∈β₀
  where
  ∅∈a₀ : ⟨ ∅ ∈ˢ a₀ ⟩
  ∅∈a₀ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym a₀≡ω) (#∈ω 0)
  a₀∈β₀ : ⟨ a₀ ∈ˢ β₀ ⟩
  a₀∈β₀ = +ω-mem a₀

∅∈Lβ₀ : ⟨ ∅ ∈ˢ Lset β₀ ⟩
∅∈Lβ₀ = ∅∈Lset β₀ β₀-lim ∅∈β₀

module Sl₂ = Slot (Lset β₀) (Ltr β₀)
  (∈-asFiber {a = ∅} {b = Lset β₀} ∅∈Lβ₀ .fst)
  (∈-asFiber {a = ∅} {b = Lset β₀} ∅∈Lβ₀ .snd)
  (∅∈Lset β₀ β₀-lim ∅∈β₀)

module Dc₂ = Desc (Lset β₀) (Ltr β₀)

-- The step closure into the carrier, T126's stepInL at Lset β₀: the
-- delivered values read places every step member in the stage above the
-- argument's stage, and the limit closure brings it into Lset β₀.
stepInL₂ : (c : S) → ⟨ c ∈ˢ Lset β₀ ⟩ → (v : S) → ⟨ v ∈ˢ rudStep c ⟩
         → ⟨ v ∈ˢ Lset β₀ ⟩
stepInL₂ c c∈ v v∈step = PT.rec (snd (v ∈ˢ Lset β₀)) go (step-out c v v∈step)
  where
  go : StepArm c v → ⟨ v ∈ˢ Lset β₀ ⟩
  go (arm-member v∈c) = Ltr β₀ {x = c} {y = v} v∈c c∈
  go (arm-self e) = subst (λ w → ⟨ w ∈ˢ Lset β₀ ⟩) (sym e) c∈
  go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ Lset β₀)) both
    (Lstage₂ β₀ β₀-lim c ∅ c∈ ∅∈Lβ₀)
    where
    both : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ β₀ ⟩ × ⟨ c ∈ˢ Lset ξ ⟩ × ⟨ ∅ ∈ˢ Lset ξ ⟩)
         → ⟨ v ∈ˢ Lset β₀ ⟩
    both (ξ , ξ∈β₀ , c∈ξ , A∈ξ) =
      Lset-mono {α = β₀} {β = sucV (suc⁴ ξ)}
        (limit-succ-mem β₀ (suc⁴ ξ) β₀-lim (suc⁴∈ β₀ ξ β₀-lim ξ∈β₀))
        (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ξ)) ⟩) (sym e)
          (Lval (suc⁴ ξ) (suc⁴-up ξ ∅ A∈ξ) i a b a∈ b∈
            (values∈L c ξ c∈ξ i a b sa sb)))
      where
      argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ξ ⟩
      argIn x (inl h) = Ltr ξ h c∈ξ
      argIn x (inr e) = subst (λ w → ⟨ w ∈ˢ Lset ξ ⟩) (sym e) c∈ξ
      a∈ : ⟨ a ∈ˢ Lset (suc⁴ ξ) ⟩
      a∈ = suc⁴-up ξ a (argIn a sa)
      b∈ : ⟨ b ∈ˢ Lset (suc⁴ ξ) ⟩
      b∈ = suc⁴-up ξ b (argIn b sb)

-- The equality frame's two directions, combined into the Clause module's
-- single bidirectional parameter (T126's eqFrame-ok at Lset β₀).
eqFrame-ok₂ : {n : ℕ} (k : Fin n) (M : Formula ⟪ Lset β₀ ⟫ (suc n))
              (δ : Vec K0.SM n) (W : S)
            → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ Lset β₀ ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ Lset β₀ ⟩)
               → ⟨ ((v , v∈) ∷ δ) K0.⊨ᵐ M ⟩ → ⟨ v ∈ˢ W ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ Lset β₀ ⟩) → ⟨ v ∈ˢ W ⟩
               → ⟨ ((v , v∈) ∷ δ) K0.⊨ᵐ M ⟩)
            → ⟨ δ K0.⊨ᵐ Dc₂.eqFrame k M ⟩ ⟷ fst (lookup k δ) ≡ W
eqFrame-ok₂ k M δ W wsub mout min =
  ( Dc₂.eqFrame-out k M δ W wsub mout min
  , Dc₂.eqFrame-in k M δ W wsub mout min )

-- The successor-clause module at the witness carrier, the whole Clause
-- telescope unchanged.
module O4₂ = Clause stepInL₂ Sl₂.graphOf Sl₂.graph-out Sl₂.graph-in Sl₂.bigOr
  Sl₂.bigOr-in Sl₂.bigOr-out Dc₂.eqFrame eqFrame-ok₂

-- The six-clause story formula at Lset β₀: the kit's four shared clauses at
-- the witness carrier, O4₂'s successor clause, and T128's limit clause
-- (T128's carrier IS Lset β₀, so its limitForm and limit-ok are consumed
-- verbatim).
storyForm₂ : Formula ⟪ Lset β₀ ⟫ 2
storyForm₂ = K0.pairForm ∧̇ K0.singleForm ∧̇ K0.zeroForm ∧̇ K0.exactDomForm
           ∧̇ O4₂.succForm ∧̇ PT128.limitForm

story-out₂ : (f : K0.SM) (x : ⟪ Lset β₀ ⟫)
           → ⟨ (f ∷ K0.ι x ∷ []) K0.⊨ᵐ storyForm₂ ⟩ → story (fst f)
story-out₂ f x (h₁ , (h₂ , (h₃ , (h₄ , (h₅ , h₆))))) =
  ( K0.pairhood-out f x h₁
  , ( K0.single-out f x h₂
    , ( K0.zero-out f x h₃ , ( K0.exactDom-out f x h₄
      , ( O4₂.succ-ok f x .fst h₅ , PT128.limit-ok f x .fst h₆ ) ) ) ) )

story-in₂ : (f : K0.SM) (x : ⟪ Lset β₀ ⟫)
          → story (fst f) → ⟨ (f ∷ K0.ι x ∷ []) K0.⊨ᵐ storyForm₂ ⟩
story-in₂ f x (h₁ , (h₂ , (h₃ , (h₄ , (h₅ , h₆))))) =
  ( K0.pairhood-in f x h₁
  , ( K0.single-in f x h₂
    , ( K0.zero-in f x h₃ , ( K0.exactDom-in f x h₄
      , ( O4₂.succ-ok f x .snd h₅ , PT128.limit-ok f x .snd h₆ ) ) ) ) )

story-ok₂ : (f : K0.SM) (x : ⟪ Lset β₀ ⟫)
          → ⟨ (f ∷ K0.ι x ∷ []) K0.⊨ᵐ storyForm₂ ⟩ ⟷ story (fst f)
story-ok₂ f x = story-out₂ f x , story-in₂ f x
