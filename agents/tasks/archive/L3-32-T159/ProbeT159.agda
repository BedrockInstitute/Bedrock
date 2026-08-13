{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T159] Close the below-lim probe end to end, for the first
-- time ever.  A copy of T151 with T154's measured cure (R-40: the
-- depth-6 +ω-iter 6 witness replaced by the limit-succ-mem climb)
-- and T154's five latent tail repairs (the four inverted subst
-- directions and the dom-read dStep).  The first whole-file
-- elaboration of the below-lim first instance.  Untracked probe, no
-- git, no master, Everything untouched.  The graph layer is consumed
-- only through the delivered probes T126/T127; no StepInL content is
-- re-built here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT159 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
  ( +ω; +ω-limit; +ω-iter; +ω-in; +ω-out; sucIter )
open import L.Rud.Step {ℓ} lem ∅
  using ( Sset; Sset-suc; Sset-zero; Sset-mono; limit-succ-mem; step-in-self )
  renaming ( step to rudStep )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( 𝒟ₒ⊆Lsuc; Lset∈Lsuc; Lpair; Lpr-limit; ∅∈Lset; Sset-union-limit; Sset-union-in )
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

-- The T128 carrier and the meta limit clause, reused: a₀ = +ω ∅ is the first
-- limit ordinal, β₀ = +ω a₀ is the carrier's index, and the limit clause is
-- carrier-generic (T128's).  T128's carrier setup (C, utr, a₀∈C) is reused
-- as well.
open PT128 using ( a₀; β₀; a₀-ord; firstLimit; β₀-lim; limitClause; C; utr; a₀∈C )

-- The kits: K0 at the target carrier Lset β₀ (the six-clause story's
-- carrier), Kω at Lset ω (the segment formula's carrier).  Kω is opened
-- because the formula layer (SM, ι, PK, isOrdAt, pair∈, ...) is used at
-- Lset ω; K0 stays qualified.
module K0 = LevelKit C utr
module Kω = LevelKit (Lset ω) (layer-trans (Lset-layer ω))
open Kω public

-- The numeral for k, named (the `#` prefix does not parse inside ⟨_⟩).
nk : ℕ → S
nk k = # k

_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

-- a₀ = +ω ∅ is ω: the finite iterates of successor from ∅ are exactly the
-- numerals, so both sides are the set of numerals.  (Prose in OrdBlocks and
-- Bridge: "γ ∅ = +ω ∅ = ω"; the equation itself is not delivered, so it is
-- proved here by the numeral characterizations on both sides.)
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

-- The six-clause story at the target carrier: the kit's four shared clauses,
-- the one-way successor clause (the meta-level shape of StepStory's clause,
-- carrier-independent), and T128's limit clause (value at a limit index =
-- pointwise union of the values below).
succClause : S → Type (ℓ-suc ℓ)
succClause f = (a : S) (c : S) (b : S) → ⟨ pr a c ∈ˢ f ⟩
             → ⟨ pr (sucV a) b ∈ˢ f ⟩ → (b ≡ rudStep c)

story : S → Type (ℓ-suc ℓ)
story f = K0.pairhood f × K0.singleValued f × K0.zeroClause f × K0.exactDom f
        × succClause f × limitClause f

-- The numeral chain, ported from T127's chainValue to the six-clause story
-- (the limit clause is vacuous below ω; the proof is T127's, the tuple
-- projections shifted by one).
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

-- The chain step at the limit index a₀: a six-clause story's value at the
-- first limit below the carrier is forced to Sset a₀.  The limit clause
-- reads the value as the pointwise union of the values below; the values
-- below are forced to Sset ξ by the numeral chain; the tower's own limit
-- union (Sset-limit) identifies Sset a₀ with that union.  This is what
-- replaces the numeral induction at a general limit index.
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
-- Part B: the honest segment at the limit index a₀.
-- ---------------------------------------------------------------------------

-- The delivered first-limit machinery at Lset ω, reused as the internal
-- witness condition of the segment's defining formula: T127's five-clause
-- story (story/storyForm/story-ok, with the successor clause instantiated
-- with the graph layer), its chainValue, and its finite segments with their
-- story checks (seg/segStory/segRan).  The segment's defining formula says:
-- x is a pair (ξ, y) with ξ an ordinal, and some story-checked witness s
-- carries the pair pr ξ y.  The story's exact domain and the value chain
-- then force y = Sset ξ and ξ ∈ ω, so the formula's extension is exactly
-- {(ξ, Sset ξ) : ξ ∈ ω} — the pairs below the first limit, definable over
-- Lset ω by the story at the smaller scale (T90's O6 description).
module G127 = PT127.Gate (∅∈Lset ω limω (#∈ω 0))

-- The SM eta: the certificate in an SM is proof-irrelevant, so every small
-- member is the ι of its own fiber.
smEta : (x : SM) → x ≡ ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst)
smEta x = ΣPathP (p , q)
  where
  p : fst x ≡ fst (ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst))
  p = sym (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .snd)
  q : PathP (λ i → ⟨ p i ∈ˢ Lset ω ⟩) (snd x)
         (snd (ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst)))
  q = isProp→PathP (λ i → snd (p i ∈ˢ Lset ω))
    (snd x) (snd (ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst)))

-- The story formula renamed from arity 2 into the segment formula's arity-4
-- environment (s, y, ξ, x): the story's witness slot lands on s (index 2),
-- the read-member slot on y (index 1).
embStory : Fin 2 → Fin 4
embStory zero = suc (suc zero)
embStory (suc zero) = suc zero

storyRen : Formula ⟪ Lset ω ⟫ 4
storyRen = renameFo embStory G127.storyForm

module RenS = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ Lset ω))
  {ℓ} {⟪ Lset ω ⟫} Kω.ι

-- hmm: the kit at Lset ω needs to be opened for ι/SM here; T127's K is the
-- same kit.  Use PT127's K (the kit at Lset ω).
storyRen-ok : (δ : Vec SM 4)
            → ⟨ δ ⊨ᵐ storyRen ⟩ ⟷ G127.story (fst (lookup (suc (suc zero)) δ))
storyRen-ok δ = (out , bwd)
  where
  sm ym : SM
  sm = lookup (suc (suc zero)) δ
  ym = lookup (suc zero) δ
  fibY : ⟪ Lset ω ⟫
  fibY = ∈-asFiber {a = fst ym} {b = Lset ω} (snd ym) .fst
  ag : RenS.Agrees embStory δ (sm ∷ ym ∷ [])
  ag zero = refl
  ag (suc zero) = refl
  out : ⟨ δ ⊨ᵐ storyRen ⟩ → G127.story (fst sm)
  out h = G127.story-ok sm fibY .fst
    (subst (λ w → ⟨ (sm ∷ w ∷ []) ⊨ᵐ G127.storyForm ⟩) (smEta ym)
      (subst ⟨_⟩ (sym (RenS.⊨-rename embStory G127.storyForm δ (sm ∷ ym ∷ []) ag)) h))
  bwd : G127.story (fst sm) → ⟨ δ ⊨ᵐ storyRen ⟩
  bwd st = subst ⟨_⟩
    (RenS.⊨-rename embStory G127.storyForm δ (sm ∷ ym ∷ []) ag)
    (subst (λ w → ⟨ (sm ∷ w ∷ []) ⊨ᵐ G127.storyForm ⟩) (sym (smEta ym))
      (G127.story-ok sm fibY .snd st))

-- The segment's defining formula at arity 1, env (x): ∃s, ∃y, ∃ξ,
-- x = pr ξ y ∧ ξ is an ordinal ∧ s satisfies the story ∧ pr ξ y ∈ s.
segBody : Formula ⟪ Lset ω ⟫ 4
segBody = (PK.prAt (suc (suc (suc zero))) zero (suc zero))
      ∧̇ (isOrdAt zero)
      ∧̇ storyRen
      ∧̇ (∃̇∈ (var (suc (suc zero)))
            (PK.prAt zero (suc zero) (suc (suc zero))))

segForm : Formula ⟪ Lset ω ⟫ 1
segForm = ∃̇ (∃̇ (∃̇ segBody))

-- The two-way decode: the formula's extension is exactly the pairs
-- (ξ, Sset ξ) for ξ ∈ ω.
segForm-ok : (m : ⟪ Lset ω ⟫)
           → ⟨ (ι m ∷ []) ⊨ᵐ segForm ⟩
           ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
segForm-ok m = (out , bwd)
  where
  δ₁ : Vec SM 1
  δ₁ = ι m ∷ []
  out : ⟨ δ₁ ⊨ᵐ segForm ⟩
      → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
  out sat = PT.rec squash₁ s₁ sat
    where
    s₁ : Σ[ sm ∈ SM ] ⟨ (sm ∷ δ₁) ⊨ᵐ ∃̇ (∃̇ segBody) ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
    s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
      where
      s₂ : Σ[ ym ∈ SM ] ⟨ (ym ∷ sm ∷ δ₁) ⊨ᵐ ∃̇ segBody ⟩
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
      s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
        where
        s₃ : Σ[ ξm ∈ SM ] ⟨ (ξm ∷ ym ∷ sm ∷ δ₁) ⊨ᵐ segBody ⟩
           → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
        s₃ (ξm , (pr-sat , (ord-sat , (st-sat , pr∈-sat)))) =
          ∣ fst ξm , (ξ∈ω , x≡prξSξ) ∣₁
          where
          δ₄ : Vec SM 4
          δ₄ = ξm ∷ ym ∷ sm ∷ δ₁
          x≡prξy : ⟪ Lset ω ⟫↪ m ≡ pr (fst ξm) (fst ym)
          x≡prξy = PK.prAt-out (suc (suc (suc zero))) zero (suc zero) δ₄ pr-sat
          st : G127.story (fst sm)
          st = storyRen-ok δ₄ .fst st-sat
          h4 : exactDom (fst sm)
          h4 = st .snd .snd .snd .fst
          prξy∈s : ⟨ pr (fst ξm) (fst ym) ∈ˢ fst sm ⟩
          prξy∈s = pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
          ξ∈ω : ⟨ fst ξm ∈ˢ ω ⟩
          ξ∈ω = PT.rec (snd (fst ξm ∈ˢ ω)) dStep h4
            where
            dStep : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ Lset ω ⟩ × IsOrd δ₀
                     × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst sm ⟩ ∥₁)
                     × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst sm ⟩ ∥₁ → ⟨ a ∈ˢ δ₀ ⟩) )
                  → ⟨ fst ξm ∈ˢ ω ⟩
            dStep (δ₀ , (δ₀∈u , ordδ₀ , _ , out-d)) =
              ω-ord .fst {x = δ₀} {y = fst ξm} ξ∈δ₀ δ₀∈ω
              where
              ξ∈δ₀ : ⟨ fst ξm ∈ˢ δ₀ ⟩
              ξ∈δ₀ = out-d (fst ξm) ∣ fst ym , prξy∈s ∣₁
              δ₀∈ω : ⟨ δ₀ ∈ˢ ω ⟩
              δ₀∈ω = ord∈Lset→∈ ω ω-ord δ₀ ordδ₀ δ₀∈u
          y≡Ssetξ : fst ym ≡ Sset (fst ξm)
          y≡Ssetξ = G127.chainValue (fst sm) st (fst ξm) (fst ym) ξ∈ω prξy∈s
          x≡prξSξ : ⟪ Lset ω ⟫↪ m ≡ pr (fst ξm) (Sset (fst ξm))
          x≡prξSξ = x≡prξy ∙ cong₂ pr refl y≡Ssetξ
  bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
      → ⟨ δ₁ ⊨ᵐ segForm ⟩
  bwd h = PT.rec (snd (δ₁ ⊨ᵐ segForm)) step₀ h
    where
    step₀ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ)))
          → ⟨ δ₁ ⊨ᵐ segForm ⟩
    step₀ (ξ , (ξ∈ω , x≡prξSξ)) = PT.rec (snd (δ₁ ⊨ᵐ segForm)) num ξ∈ω
      where
      num : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower k) ≡ ξ)
          → ⟨ δ₁ ⊨ᵐ segForm ⟩
      num (k , #k≡ξ) = ∣ sm , (∣ ym , (∣ ξm , body-sat ∣₁) ∣₁) ∣₁
        where
        ξ∈L : ⟨ ξ ∈ˢ Lset ω ⟩
        ξ∈L = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) #k≡ξ (numeral∈Lsetω (lower k))
        Sξ∈L : ⟨ Sset ξ ∈ˢ Lset ω ⟩
        Sξ∈L = subst (λ w → ⟨ Sset w ∈ˢ Lset ω ⟩) #k≡ξ
          (G127.G125.memberAt (lower k) .snd)
        sm : SM
        sm = PK.pt (G127.seg (lower k)) (G127.seg∈Lsetω (lower k))
        ym : SM
        ym = PK.pt (Sset ξ) Sξ∈L
        ξm : SM
        ξm = PK.pt ξ ξ∈L
        δ₄ : Vec SM 4
        δ₄ = ξm ∷ ym ∷ sm ∷ δ₁
        body-sat : ⟨ δ₄ ⊨ᵐ segBody ⟩
        body-sat = ( pr-sat , (ord-sat , (st-sat , pr∈-sat)) )
          where
          pr-sat : ⟨ δ₄ ⊨ᵐ PK.prAt (suc (suc (suc zero))) zero (suc zero) ⟩
          pr-sat = PK.prAt-in (suc (suc (suc zero))) zero (suc zero) δ₄
            x≡prξSξ
          ord-sat : ⟨ δ₄ ⊨ᵐ isOrdAt zero ⟩
          ord-sat = isOrd-in zero δ₄ (subst IsOrd #k≡ξ (numeral-ord (lower k)))
          st-sat : ⟨ δ₄ ⊨ᵐ storyRen ⟩
          st-sat = storyRen-ok δ₄ .snd (G127.segStory (lower k))
          prξSξ∈s : ⟨ pr ξ (Sset ξ) ∈ˢ G127.seg (lower k) ⟩
          prξSξ∈s = finSet-in (suc (lower k)) hseg (pr ξ (Sset ξ)) ∣ idx , eq ∣₁
            where
            hseg : Fin (suc (lower k)) → S
            hseg i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
            idx : Fin (suc (lower k))
            idx = fromℕ' (suc (lower k)) (lower k) (≤-refl {suc (lower k)})
            e : toℕ idx ≡ lower k
            e = toFromId' (suc (lower k)) (lower k) (≤-refl {suc (lower k)})
            eq : hseg idx ≡ pr ξ (Sset ξ)
            eq = cong₂ pr (cong nk e) (cong Sset (cong nk e))
               ∙ cong₂ pr #k≡ξ (cong Sset #k≡ξ)
          pr∈-sat : ⟨ δ₄ ⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                       (PK.prAt zero (suc zero) (suc (suc zero))) ⟩
          pr∈-sat = pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd prξSξ∈s

-- P, the pairs below the first limit: the definable family
-- {(ξ, Sset ξ) : ξ ∈ ω}, a member of Lset β₀ via the definable-power step
-- at Lset ω and the +1 slack.
P : S
P = defSet segForm

module Dω = DefOf (Lset ω)

P∈𝒟ₒω : ⟨ P ∈ˢ 𝒟ₒ (Lset ω) ⟩
P∈𝒟ₒω = 𝒟ₒ-intro (Lset ω) P ∣ segForm , refl ∣₁

P∈Lsucω : ⟨ P ∈ˢ Lset (sucV ω) ⟩
P∈Lsucω = 𝒟ₒ⊆Lsuc ω P P∈𝒟ₒω

P∈Lβ₀ : ⟨ P ∈ˢ C ⟩
P∈Lβ₀ = Lset-mono {α = β₀} {β = sucV a₀} (+ω-iter 1 a₀)
  (subst (λ w → ⟨ P ∈ˢ Lset (sucV w) ⟩) (sym a₀≡ω) P∈Lsucω)

-- The two directions of P's membership: in, from a numeral index (the
-- story-checked finite segment as witness); out, back to the numeral index
-- and the S-stage value (the story's chain).
prξSξ∈Lω : (ξ : S) → ⟨ ξ ∈ˢ ω ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ Lset ω ⟩
prξSξ∈Lω ξ ξ∈ω = PT.rec (snd (pr ξ (Sset ξ) ∈ˢ Lset ω)) go ξ∈ω
  where
  go : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower k) ≡ ξ)
     → ⟨ pr ξ (Sset ξ) ∈ˢ Lset ω ⟩
  go (k , q) = subst (λ w → ⟨ pr w (Sset w) ∈ˢ Lset ω ⟩) q
    (Lpr-limit ω limω (nk (lower k)) (Sset (nk (lower k)))
      (numeral∈Lsetω (lower k)) (G127.G125.memberAt (lower k) .snd))

P∈-out : (p : S) → ⟨ p ∈ˢ P ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
P∈-out p p∈ = out' sat
  where
  m : ⟪ Lset ω ⟫
  m = ∈-asFiber {a = p} {b = Lset ω} (Dω.defSet⊆A segForm p p∈) .fst
  p∈m : ⟨ ⟪ Lset ω ⟫↪ m ∈ˢ P ⟩
  p∈m = subst (λ w → ⟨ w ∈ˢ P ⟩) (sym (∈-asFiber {a = p} {b = Lset ω}
    (Dω.defSet⊆A segForm p p∈) .snd)) p∈
  sat : ⟨ (ι m ∷ []) ⊨ᵐ segForm ⟩
  sat = subst ⟨_⟩ (Dω.defSet-mem segForm m) p∈m
  out' : ⟨ (ι m ∷ []) ⊨ᵐ segForm ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
  out' h = PT.rec squash₁ go (segForm-ok m .fst h)
    where
    go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ)))
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
    go (ξ , (ξ∈ω , q)) = ∣ ξ , (ξ∈ω , p≡m ∙ q) ∣₁
      where
      p≡m : p ≡ ⟪ Lset ω ⟫↪ m
      p≡m = sym (∈-asFiber {a = p} {b = Lset ω} (Dω.defSet⊆A segForm p p∈) .snd)

P∈-in : (ξ : S) → ⟨ ξ ∈ˢ ω ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ P ⟩
P∈-in ξ ξ∈ω = PT.rec (snd (pr ξ (Sset ξ) ∈ˢ P)) go ξ∈ω
  where
  go : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower k) ≡ ξ)
     → ⟨ pr ξ (Sset ξ) ∈ˢ P ⟩
  go (k , q) = subst (λ w → ⟨ w ∈ˢ P ⟩) (cong₂ pr q (cong Sset q))
    (subst (λ w → ⟨ w ∈ˢ P ⟩) (fib .snd)
      (subst ⟨_⟩ (sym (Dω.defSet-mem segForm m))
        (segForm-ok m .snd ∣ nk (lower k) , ( #∈ω (lower k) , fib .snd ) ∣₁)))
    where
    fib : Σ[ m ∈ ⟪ Lset ω ⟫ ]
            (⟪ Lset ω ⟫↪ m ≡ pr (nk (lower k)) (Sset (nk (lower k))))
    fib = ∈-asFiber {a = pr (nk (lower k)) (Sset (nk (lower k)))}
      {b = Lset ω} (prξSξ∈Lω (nk (lower k)) (#∈ω (lower k)))
    m : ⟪ Lset ω ⟫
    m = fib .fst

-- The top pair: the value at the limit index a₀ itself, pr a₀ (Sset a₀).
-- Both components sit in Lset (sucV a₀) (the ordinal's own successor stage
-- and the stage's own stage, via the first-limit identification
-- Sset ω = Lset ω), and the Kuratowski pair lands two steps up.
module G125₀ = PB125.Gate (∅∈Lset ω limω (#∈ω 0))

T : S
T = pr a₀ (Sset a₀)

a₀∈Lsuca₀ : ⟨ a₀ ∈ˢ Lset (sucV a₀) ⟩
a₀∈Lsuca₀ = ord∈Lset-suc a₀ a₀-ord

Sseta₀∈Lsuca₀ : ⟨ Sset a₀ ∈ˢ Lset (sucV a₀) ⟩
Sseta₀∈Lsuca₀ = subst (λ w → ⟨ Sset w ∈ˢ Lset (sucV w) ⟩) (sym a₀≡ω) Ssetω∈Lsucω
  where
  Ssetω∈Lsucω : ⟨ Sset ω ∈ˢ Lset (sucV ω) ⟩
  Ssetω∈Lsucω = subst (λ w → ⟨ w ∈ˢ Lset (sucV ω) ⟩)
    (sym G125₀.Ssetω≡Lsetω) (Lset∈Lsuc ω)

δ₀ : S
δ₀ = sucV (sucV (sucV a₀))

δ₀-ord : IsOrd δ₀
δ₀-ord = suc-ord (suc-ord (suc-ord a₀-ord))

ω∈δ₀ : ⟨ ω ∈ˢ δ₀ ⟩
ω∈δ₀ = subst (λ w → ⟨ w ∈ˢ δ₀ ⟩) a₀≡ω a₀∈δ₀
  where
  a₀∈δ₀ : ⟨ a₀ ∈ˢ δ₀ ⟩
  a₀∈δ₀ = δ₀-ord .fst {x = sucV (sucV a₀)} {y = a₀} a₀∈sucsuc
    (self∈sucV (sucV (sucV a₀)))
    where
    a₀∈sucsuc : ⟨ a₀ ∈ˢ sucV (sucV a₀) ⟩
    a₀∈sucsuc = suc-ord (suc-ord a₀-ord) .fst {x = sucV a₀} {y = a₀}
      (self∈sucV a₀) (self∈sucV (sucV a₀))

T∈Lδ₀ : ⟨ T ∈ˢ Lset δ₀ ⟩
T∈Lδ₀ = subst (λ w → ⟨ w ∈ˢ Lset δ₀ ⟩) (sym pr≡F0)
  (Lpair (sucV (sucV a₀)) (F0 a₀ a₀) (F0 a₀ (Sset a₀)) F0aa∈L F0aS∈L)
  where
  F0aa∈L : ⟨ F0 a₀ a₀ ∈ˢ Lset (sucV (sucV a₀)) ⟩
  F0aa∈L = Lpair (sucV a₀) a₀ a₀ a₀∈Lsuca₀ a₀∈Lsuca₀
  F0aS∈L : ⟨ F0 a₀ (Sset a₀) ∈ˢ Lset (sucV (sucV a₀)) ⟩
  F0aS∈L = Lpair (sucV a₀) a₀ (Sset a₀) a₀∈Lsuca₀ Sseta₀∈Lsuca₀
  pr≡F0 : pr a₀ (Sset a₀) ≡ F0 (F0 a₀ a₀) (F0 a₀ (Sset a₀))
  pr≡F0 = sym (cong (λ w → ⁅ w , ⁅ a₀ , Sset a₀ ⁆ ⁆) (pair-singleton a₀))

P∈Lδ₀ : ⟨ P ∈ˢ Lset δ₀ ⟩
P∈Lδ₀ = Lset-mono {α = δ₀} {β = sucV a₀}
  suca₀∈δ₀ (subst (λ w → ⟨ P ∈ˢ Lset (sucV w) ⟩) (sym a₀≡ω) P∈Lsucω)
  where
  suca₀∈δ₀ : ⟨ sucV a₀ ∈ˢ δ₀ ⟩
  suca₀∈δ₀ = δ₀-ord .fst {x = sucV (sucV a₀)} {y = sucV a₀}
    (self∈sucV (sucV a₀)) (self∈sucV (sucV (sucV a₀)))

-- The segment at the limit index: the pairs below (P) plus the top pair,
-- as a definable subset of Lset δ₀ (the disjunction x ∈ P ∨ x = T).
-- The union closure at a successor stage: the union of a member of Lset σ
-- is definable over Lset σ (a bounded existential), so it lands one step up.
-- The Basic UnionOf pattern, restated at the stage-membership conclusion.
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

-- The segment at the limit index: P ∪ {T}, as the rud union of the
-- two-element family {P, {T}} — a member of Lset β₀ by the union closure.
seg₀ : S
seg₀ = F5 (F0 P (F0 T T)) T

segRHS : S → hProp (ℓ-suc ℓ)
segRHS x = Logic._⊔_ (x ∈ˢ P) ((x ≡ T) , setIsSet x T)

-- The segment's membership is the disjunction, by the delivered F0/F5
-- specifications (the union reads a member of a member, the pair reads the
-- two members).
seg∈ : (x : S) → ⟨ x ∈ˢ seg₀ ⟩ ⟷ ⟨ segRHS x ⟩
seg∈ x = (out , bwd)
  where
  out : ⟨ x ∈ˢ seg₀ ⟩ → ⟨ segRHS x ⟩
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
  bwd : ⟨ segRHS x ⟩ → ⟨ x ∈ˢ seg₀ ⟩
  bwd h = PT.rec (snd (x ∈ˢ seg₀)) b' h
    where
    b' : ⟨ x ∈ˢ P ⟩ ⊎ (x ≡ T) → ⟨ x ∈ˢ seg₀ ⟩
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

δ₀∈β₀ : ⟨ δ₀ ∈ˢ β₀ ⟩
δ₀∈β₀ = +ω-iter 3 a₀

sucδ₀∈β₀ : ⟨ sucV δ₀ ∈ˢ β₀ ⟩
sucδ₀∈β₀ = limit-succ-mem β₀ δ₀ β₀-lim δ₀∈β₀

sucsucδ₀∈β₀ : ⟨ sucV (sucV δ₀) ∈ˢ β₀ ⟩
sucsucδ₀∈β₀ = limit-succ-mem β₀ (sucV δ₀) β₀-lim sucδ₀∈β₀

ordWit : ⟨ sucV (sucV (sucV δ₀)) ∈ˢ β₀ ⟩
ordWit = limit-succ-mem β₀ (sucV (sucV δ₀)) β₀-lim sucsucδ₀∈β₀

seg₀∈Lβ₀ : ⟨ seg₀ ∈ˢ C ⟩
seg₀∈Lβ₀ = Lset-mono {α = β₀} {β = sucV (sucV (sucV δ₀))} ordWit
  UC.union∈Lsuc
  where
  F0TT∈L : ⟨ F0 T T ∈ˢ Lset (sucV δ₀) ⟩
  F0TT∈L = Lpair δ₀ T T T∈Lδ₀ T∈Lδ₀
  F0PTT∈L : ⟨ F0 P (F0 T T) ∈ˢ Lset (sucV (sucV δ₀)) ⟩
  F0PTT∈L = Lpair (sucV δ₀) P (F0 T T)
    (Lset-mono {α = sucV δ₀} {β = δ₀} (self∈sucV δ₀) P∈Lδ₀) F0TT∈L
  module UC = UnionClosure (sucV (sucV δ₀)) (suc-ord (suc-ord δ₀-ord))
    (F0 P (F0 T T)) F0PTT∈L

-- The value at the limit index is in the segment: the top pair, by the
-- right disjunct.
T∈seg₀ : ⟨ T ∈ˢ seg₀ ⟩
T∈seg₀ = seg∈ T .snd ∣ inr refl ∣₁

-- The values below the limit are in the segment, by the left disjunct.
prξSξ∈seg₀ : (ξ : S) → ⟨ ξ ∈ˢ a₀ ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ seg₀ ⟩
prξSξ∈seg₀ ξ ξ∈a₀ = seg∈ (pr ξ (Sset ξ)) .snd ∣ inl (P∈-in ξ ξ∈ω) ∣₁
  where
  ξ∈ω : ⟨ ξ ∈ˢ ω ⟩
  ξ∈ω = subst (λ w → ⟨ ξ ∈ˢ w ⟩) a₀≡ω ξ∈a₀

-- The exact domain of the segment: sucV a₀.  Every member of the domain has
-- a pair (the values below via P, the top via T), and every pair's first
-- component lies in the domain.  The in-direction's two branches are named
-- top-level functions with written types (I-5); the T138 shape with two
-- inline lambdas walls past 7.5 minutes.  The out-direction's pgo moves
-- ξ ∈ a₀ to ξ ∈ sucV a₀ through ∈sucV-inl before the transport; the T138
-- shape omits that step and does not typecheck.
segDom-in-below : (a : S) → ⟨ a ∈ˢ a₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁
segDom-in-below a a∈a₀ = ∣ Sset a , prξSξ∈seg₀ a a∈a₀ ∣₁

segDom-in-top : (a : S) → a ≡ a₀ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁
segDom-in-top a a≡a₀ = ∣ Sset a₀ , subst (λ w → ⟨ pr w (Sset a₀) ∈ˢ seg₀ ⟩) (sym a≡a₀) T∈seg₀ ∣₁

segDom-in : (a : S) → ⟨ a ∈ˢ sucV a₀ ⟩
         → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁
segDom-in a a∈suc = ∈sucV-elim {A = a₀} {x = a} squash₁ a∈suc
  (segDom-in-below a) (segDom-in-top a)

segDom-out : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁ → ⟨ a ∈ˢ sucV a₀ ⟩
segDom-out a = PT.rec (snd (a ∈ˢ sucV a₀)) go
  where
  go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ → ⟨ a ∈ˢ sucV a₀ ⟩
  go (b , pr∈) = PT.rec (snd (a ∈ˢ sucV a₀)) d (seg∈ (pr a b) .fst pr∈)
    where
    d : ⟨ pr a b ∈ˢ P ⟩ ⊎ (pr a b ≡ T) → ⟨ a ∈ˢ sucV a₀ ⟩
    d (inl p∈P) = PT.rec (snd (a ∈ˢ sucV a₀)) pgo (P∈-out (pr a b) p∈P)
      where
      pgo : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (pr a b ≡ pr ξ (Sset ξ)))
          → ⟨ a ∈ˢ sucV a₀ ⟩
      pgo (ξ , (ξ∈ω , q)) = subst (λ w → ⟨ w ∈ˢ sucV a₀ ⟩) (sym (pr-inj q .fst))
        (∈sucV-inl {A = a₀} {x = ξ} (subst (λ w → ⟨ ξ ∈ˢ w ⟩) (sym a₀≡ω) ξ∈ω))
    d (inr q) = subst (λ w → ⟨ w ∈ˢ sucV a₀ ⟩) (pr-inj (sym q) .fst)
      (self∈sucV a₀)

segDom₀ : K0.exactDom seg₀
segDom₀ = ∣ sucV a₀ , ( suca₀∈C , suc-ord a₀-ord , segDom-in , segDom-out ) ∣₁
  where
  suca₀∈C : ⟨ sucV a₀ ∈ˢ C ⟩
  suca₀∈C = Lset-mono {α = β₀} {β = sucV (sucV a₀)} (+ω-iter 2 a₀)
    (ord∈Lset-suc (sucV a₀) (suc-ord a₀-ord))

-- The limit clause on the segment at a₀: the value at the limit index,
-- Sset a₀ (the top pair's value), is the union of the values below — the
-- tower's own limit union, read through the segment's membership.
segLimit₀ : (z : S) → ⟨ z ∈ˢ Sset a₀ ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
     × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg₀ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
segLimit₀ z = (fwd , bwd)
  where
  fwd : ⟨ z ∈ˢ Sset a₀ ⟩
      → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
           × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg₀ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
  fwd z∈S = PT.rec squash₁ s₁ (Sset-union-limit a₀ firstLimit z z∈S)
    where
    s₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ a₀ ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg₀ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
    s₁ (δ , (δ∈a₀ , z∈Sδ')) = ∣ sucV δ , (δ'∈a₀ , ∣ Sset (sucV δ) , (pr∈ , z∈Sδ') ∣₁) ∣₁
      where
      δ'∈a₀ : ⟨ sucV δ ∈ˢ a₀ ⟩
      δ'∈a₀ = limit-succ-mem a₀ δ firstLimit δ∈a₀
      pr∈ : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ seg₀ ⟩
      pr∈ = prξSξ∈seg₀ (sucV δ) δ'∈a₀
  bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
           × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg₀ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
      → ⟨ z ∈ˢ Sset a₀ ⟩
  bwd h = PT.rec (snd (z ∈ˢ Sset a₀)) s₁ h
    where
    s₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg₀ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
        → ⟨ z ∈ˢ Sset a₀ ⟩
    s₁ (ξ , (ξ∈a₀ , rest)) = PT.rec (snd (z ∈ˢ Sset a₀)) s₂ rest
      where
      ξ∈ω : ⟨ ξ ∈ˢ ω ⟩
      ξ∈ω = subst (λ w → ⟨ ξ ∈ˢ w ⟩) a₀≡ω ξ∈a₀
      s₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg₀ ⟩ × ⟨ z ∈ˢ w ⟩) → ⟨ z ∈ˢ Sset a₀ ⟩
      s₂ (w , (pr∈ , z∈w)) = PT.rec (snd (z ∈ˢ Sset a₀)) d
        (seg∈ (pr ξ w) .fst pr∈)
        where
        d : ⟨ pr ξ w ∈ˢ P ⟩ ⊎ (pr ξ w ≡ T) → ⟨ z ∈ˢ Sset a₀ ⟩
        d (inl p∈P) = PT.rec (snd (z ∈ˢ Sset a₀)) pgo (P∈-out (pr ξ w) p∈P)
          where
          pgo : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ ω ⟩ × (pr ξ w ≡ pr ξ' (Sset ξ')))
              → ⟨ z ∈ˢ Sset a₀ ⟩
          pgo (ξ' , (ξ'∈ω , q)) = Sset-mono {α = a₀} {β = ξ} ξ∈a₀ z z∈Sξ
            where
            w≡Sξ : w ≡ Sset ξ
            w≡Sξ = subst (λ t → w ≡ Sset t) (sym (pr-inj q .fst))
              (pr-inj q .snd)
            z∈Sξ : ⟨ z ∈ˢ Sset ξ ⟩
            z∈Sξ = subst (λ t → ⟨ z ∈ˢ t ⟩) (w≡Sξ) z∈w
        d (inr q) = Empty.rec {A = ⟨ z ∈ˢ Sset a₀ ⟩}
          (∈-irrefl a₀ (subst (λ t → ⟨ t ∈ˢ a₀ ⟩) (sym (pr-inj (sym q) .fst)) ξ∈a₀))

-- Exercises at the concrete points: the limit clause read both ways at a
-- member of the top value, and the segment's exact domain read at the top
-- index.
top∈Sseta₀ : ⟨ Sset ∅ ∈ˢ Sset a₀ ⟩
top∈Sseta₀ = Sset-union-in a₀ firstLimit ∅ (Sset ∅) ∅∈a₀
  (subst (λ w → ⟨ Sset ∅ ∈ˢ w ⟩) (sym (Sset-suc ∅)) (step-in-self (Sset ∅)))
  where
  ∅∈a₀ : ⟨ ∅ ∈ˢ a₀ ⟩
  ∅∈a₀ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym a₀≡ω) (#∈ω 0)

lim-read : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a₀ ⟩
         × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ seg₀ ⟩ × ⟨ Sset ∅ ∈ˢ w ⟩) ∥₁) ∥₁
lim-read = segLimit₀ (Sset ∅) .fst top∈Sseta₀

lim-read-back : ⟨ Sset ∅ ∈ˢ Sset a₀ ⟩
lim-read-back = segLimit₀ (Sset ∅) .snd lim-read

dom-read : ∥ Σ[ b ∈ S ] ⟨ pr a₀ b ∈ˢ seg₀ ⟩ ∥₁
dom-read = segDom-in a₀ (self∈sucV a₀)

-- ---------------------------------------------------------------------------
-- Part C: the four unbuilt story clauses on the segment at the limit index.
-- T127's shapes ported to seg₀ = P ∪ {T}: the pairs below the limit decode
-- as pr ξ (Sset ξ) for ξ ∈ ω; the top pair T = pr a₀ (Sset a₀) is the value
-- at the limit index itself.
-- ---------------------------------------------------------------------------

-- Pairhood: every member of the segment is a Kuratowski pair.
segPairhood : K0.pairhood seg₀
segPairhood z z∈ = PT.rec squash₁ go (seg∈ z .fst z∈)
  where
  go : ⟨ z ∈ˢ P ⟩ ⊎ (z ≡ T) → isPair z
  go (inl z∈P) = PT.rec squash₁ pgo (P∈-out z z∈P)
    where
    pgo : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (z ≡ pr ξ (Sset ξ))) → isPair z
    pgo (ξ , (ξ∈ω , q)) = ∣ ξ , (Sset ξ , q) ∣₁
  go (inr q) = ∣ a₀ , (Sset a₀ , q) ∣₁

-- Single-valuedness: two pairs in the segment with the same first component
-- agree on the second component.
segSingleValued : K0.singleValued seg₀
segSingleValued a b c ab∈ ac∈ = PT.rec (setIsSet b c) go₁ (seg∈ (pr a b) .fst ab∈)
  where
  go₁ : ⟨ pr a b ∈ˢ P ⟩ ⊎ (pr a b ≡ T) → b ≡ c
  go₁ (inl p₁) = PT.rec (setIsSet b c) p₁go (P∈-out (pr a b) p₁)
    where
    p₁go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (pr a b ≡ pr ξ (Sset ξ))) → b ≡ c
    p₁go (ξ , (ξ∈ω , q₁)) = PT.rec (setIsSet b c) go₂ (seg∈ (pr a c) .fst ac∈)
      where
      a≡ξ : a ≡ ξ
      a≡ξ = pr-inj q₁ .fst
      b≡Sξ : b ≡ Sset ξ
      b≡Sξ = pr-inj q₁ .snd
      go₂ : ⟨ pr a c ∈ˢ P ⟩ ⊎ (pr a c ≡ T) → b ≡ c
      go₂ (inl p₂) = PT.rec (setIsSet b c) p₂go (P∈-out (pr a c) p₂)
        where
        p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ ω ⟩ × (pr a c ≡ pr ξ' (Sset ξ'))) → b ≡ c
        p₂go (ξ' , (ξ'∈ω , q₂)) =
          b≡Sξ ∙ cong Sset ξ≡ξ' ∙ sym (pr-inj q₂ .snd)
          where
          ξ≡ξ' : ξ ≡ ξ'
          ξ≡ξ' = sym a≡ξ ∙ pr-inj q₂ .fst
      go₂ (inr q₂) = Empty.rec (∈-irrefl a₀ a₀∈a₀)
        where
        a₀∈a₀ : ⟨ a₀ ∈ˢ a₀ ⟩
        a₀∈a₀ = subst (λ w → ⟨ w ∈ˢ a₀ ⟩) ξ≡a₀
          (subst (λ w → ⟨ ξ ∈ˢ w ⟩) (sym a₀≡ω) ξ∈ω)
          where
          ξ≡a₀ : ξ ≡ a₀
          ξ≡a₀ = sym a≡ξ ∙ pr-inj q₂ .fst
  go₁ (inr q₁) = PT.rec (setIsSet b c) go₃ (seg∈ (pr a c) .fst ac∈)
    where
    a≡a₀ : a ≡ a₀
    a≡a₀ = pr-inj q₁ .fst
    b≡Sa₀ : b ≡ Sset a₀
    b≡Sa₀ = pr-inj q₁ .snd
    go₃ : ⟨ pr a c ∈ˢ P ⟩ ⊎ (pr a c ≡ T) → b ≡ c
    go₃ (inl p₂) = PT.rec (setIsSet b c) p₂go (P∈-out (pr a c) p₂)
      where
      p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ ω ⟩ × (pr a c ≡ pr ξ' (Sset ξ'))) → b ≡ c
      p₂go (ξ' , (ξ'∈ω , q₂)) = Empty.rec (∈-irrefl a₀ a₀∈a₀)
        where
        a₀∈a₀ : ⟨ a₀ ∈ˢ a₀ ⟩
        a₀∈a₀ = subst (λ w → ⟨ w ∈ˢ a₀ ⟩) (sym a₀≡ξ')
          (subst (λ w → ⟨ ξ' ∈ˢ w ⟩) (sym a₀≡ω) ξ'∈ω)
          where
          a₀≡ξ' : a₀ ≡ ξ'
          a₀≡ξ' = sym a≡a₀ ∙ pr-inj q₂ .fst
    go₃ (inr q₂) = b≡Sa₀ ∙ sym (pr-inj q₂ .snd)

-- The zero clause: ∅ is a memberless witness, and pr ∅ ∅ lies in the
-- segment through the pair (∅, Sset ∅) = (∅, ∅) below the limit.
segZeroClause : K0.zeroClause seg₀
segZeroClause = ∣ ∅ , (empt , pair) ∣₁
  where
  empt : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → Empty.⊥
  empt z z∈∅ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅)
  pair : ⟨ pr ∅ ∅ ∈ˢ seg₀ ⟩
  pair = subst (λ w → ⟨ w ∈ˢ seg₀ ⟩) (cong₂ pr refl Sset-zero) pr∅S∈
    where
    pr∅S∈ : ⟨ pr ∅ (Sset ∅) ∈ˢ seg₀ ⟩
    pr∅S∈ = seg∈ (pr ∅ (Sset ∅)) .snd ∣ inl (P∈-in ∅ (#∈ω 0)) ∣₁

-- The one-way successor clause (G126.O4's instantiation at Lset ω, applied
-- to the segment): a present pair at a and at sucV a forces the value at
-- sucV a to be the step of the value at a.  Below the limit the pair at ξ
-- reads pr ξ (Sset ξ) and the successor pair at sucV ξ reads
-- pr (sucV ξ) (Sset (sucV ξ)); Sset-suc identifies Sset (sucV ξ) with
-- step (Sset ξ).  The top-pair cases are empty: sucV a₀ is neither below
-- the limit nor the limit itself.
segSuccClause : G127.G126.O4.succClause seg₀
segSuccClause a c b ac∈ ab∈ = PT.rec (setIsSet b (rudStep c)) go₁
  (seg∈ (pr a c) .fst ac∈)
  where
  go₁ : ⟨ pr a c ∈ˢ P ⟩ ⊎ (pr a c ≡ T) → b ≡ rudStep c
  go₁ (inl p₁) = PT.rec (setIsSet b (rudStep c)) p₁go (P∈-out (pr a c) p₁)
    where
    p₁go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (pr a c ≡ pr ξ (Sset ξ))) → b ≡ rudStep c
    p₁go (ξ , (ξ∈ω , q₁)) = PT.rec (setIsSet b (rudStep c)) go₂
      (seg∈ (pr (sucV a) b) .fst ab∈)
      where
      a≡ξ : a ≡ ξ
      a≡ξ = pr-inj q₁ .fst
      c≡Sξ : c ≡ Sset ξ
      c≡Sξ = pr-inj q₁ .snd
      sucξ∈a₀ : ⟨ sucV ξ ∈ˢ a₀ ⟩
      sucξ∈a₀ = limit-succ-mem a₀ ξ firstLimit
        (subst (λ w → ⟨ ξ ∈ˢ w ⟩) (sym a₀≡ω) ξ∈ω)
      go₂ : ⟨ pr (sucV a) b ∈ˢ P ⟩ ⊎ (pr (sucV a) b ≡ T) → b ≡ rudStep c
      go₂ (inl p₂) = PT.rec (setIsSet b (rudStep c)) p₂go
        (P∈-out (pr (sucV a) b) p₂)
        where
        p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ ω ⟩
             × (pr (sucV a) b ≡ pr ξ' (Sset ξ'))) → b ≡ rudStep c
        p₂go (ξ' , (ξ'∈ω , q₂)) =
          pr-inj q₂ .snd ∙ cong Sset ξ'≡sucξ ∙ Sset-suc ξ
          ∙ cong rudStep (sym c≡Sξ)
          where
          ξ'≡sucξ : ξ' ≡ sucV ξ
          ξ'≡sucξ = sym (pr-inj q₂ .fst) ∙ cong sucV a≡ξ
      go₂ (inr q₂) = Empty.rec (∈-irrefl a₀ bad)
        where
        bad : ⟨ a₀ ∈ˢ a₀ ⟩
        bad = subst (λ w → ⟨ w ∈ˢ a₀ ⟩) sucξ≡a₀ sucξ∈a₀
          where
          sucξ≡a₀ : sucV ξ ≡ a₀
          sucξ≡a₀ = cong sucV (sym a≡ξ) ∙ pr-inj q₂ .fst
  go₁ (inr q₁) = PT.rec (setIsSet b (rudStep c)) go₃
    (seg∈ (pr (sucV a) b) .fst ab∈)
    where
    a≡a₀ : a ≡ a₀
    a≡a₀ = pr-inj q₁ .fst
    go₃ : ⟨ pr (sucV a) b ∈ˢ P ⟩ ⊎ (pr (sucV a) b ≡ T) → b ≡ rudStep c
    go₃ (inl p₂) = PT.rec (setIsSet b (rudStep c)) p₂go
      (P∈-out (pr (sucV a) b) p₂)
      where
      p₂go : Σ[ ξ' ∈ S ] (⟨ ξ' ∈ˢ ω ⟩
           × (pr (sucV a) b ≡ pr ξ' (Sset ξ'))) → b ≡ rudStep c
      p₂go (ξ' , (ξ'∈ω , q₂)) = Empty.rec (∈-irrefl a₀ bad)
        where
        bad : ⟨ a₀ ∈ˢ a₀ ⟩
        bad = a₀-ord .fst {x = sucV a₀} {y = a₀} (self∈sucV a₀)
          sucVa₀∈a₀
          where
          sucVa₀∈a₀ : ⟨ sucV a₀ ∈ˢ a₀ ⟩
          sucVa₀∈a₀ = subst (λ w → ⟨ w ∈ˢ a₀ ⟩) ξ'≡suca₀
            (subst (λ w → ⟨ ξ' ∈ˢ w ⟩) (sym a₀≡ω) ξ'∈ω)
            where
            ξ'≡suca₀ : ξ' ≡ sucV a₀
            ξ'≡suca₀ = sym (pr-inj q₂ .fst) ∙ cong sucV a≡a₀
    go₃ (inr q₂) = Empty.rec (∈-irrefl a₀ bad)
      where
      bad : ⟨ a₀ ∈ˢ a₀ ⟩
      bad = subst (λ w → ⟨ a₀ ∈ˢ w ⟩) sucVa₀≡a₀ (self∈sucV a₀)
        where
        sucVa₀≡a₀ : sucV a₀ ≡ a₀
        sucVa₀≡a₀ = sym (cong sucV a≡a₀) ∙ pr-inj q₂ .fst
