{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T127] The B4 gate at the first limit: O6 the segments, O7 the value
-- chain, O8 the family equality at the L-stage carrier Lset ω, consuming
-- T126's StepStory instantiation (ProbeT126.Gate.O4, the successor clause)
-- and T125's memberships (ProbeBelowLim.Gate.memberAt).  Untracked probe,
-- no git, no master.  The archived StepInL is served from the scratch tree
-- /tmp/t125-scratch with T121's left-compute bridge (D-25 route), exactly
-- as T125 and T126 did.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT127 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_; _∧̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; Lset-layer; layer-trans; isTransV )
open import L.Ordinal {ℓ} using
  ( ∅-ord; ∈#-elim; #∈ω; numeral-mem; numeral-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord; limit-mem-ord )
open import L.InitialSegment {ℓ} using ( _∈ran_; _⟷_ )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-suc; Sset-zero; step; limit-succ-mem; Fof; Fof-f5; f5 )
open import L.Rud.Ops {ℓ} using ( F0; F5 )
open import L.TowerKit {ℓ} lem A using ( Ltr )
open import L.Rud.Bridge {ℓ} lem A using
  ( Lval; Lpair-limit; Lpr-limit; Lstage; Lstage₂; ∅∈Lset )
open import L.Rud.Finite {ℓ} lem A using ( limω; finSet0∅; finSetSuc )
open import L.Rud.HF {ℓ} lem A using ( numeral∈Lsetω )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
import ProbeT126 {ℓ} lem A as PT126
import ProbeBelowLim {ℓ} lem A as PB125
open import Cubical.Data.FinData.Base using ( Fin; toℕ; zero )
open import Cubical.Data.FinData.Properties
  using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Order using ( _<_; ≤-refl )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2 )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ∈∈ₛ; _∈ₛ_; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The kit at the L-stage carrier (T125's D-10 check 2, RUN not read) and the
-- carrier's definable-subset frame (the defSet the carve reads).
module K = LevelKit (Lset ω) (layer-trans (Lset-layer ω))
open K public

module D = DefOf (Lset ω)

-- The numeral for k, named (the # prefix does not parse inside ⟨_⟩).
nk : ℕ → S
nk k = # k

∅∈ω : ⟨ ∅ ∈ˢ ω ⟩
∅∈ω = #∈ω 0

-- The gate proper, under the relativization-slot hypothesis A ∈ Lset ω
-- (Reduce's slot∈L at the first limit; the trunk discharges it at A = ∅).
-- G126 is T126's unchanged StepStory instantiation (the graph layer, the
-- step closure, the equality frame, and O4 = the successor clause module);
-- G125 is T125's memberships (RudBelow-ω, memberAt, memberAtOrd).
module Gate (A∈ω : ⟨ A ∈ˢ Lset ω ⟩) where

  module G126 = PT126.Gate A∈ω
  module G125 = PB125.Gate A∈ω

  -- The one-way story at the L-carrier: the kit's four shared clauses plus
  -- T126's successor clause, and its object formula with the two-way decode
  -- (the LevelSigma aSt1 assembly pattern, with succForm in place of
  -- succValForm1).
  story : S → Type (ℓ-suc ℓ)
  story f = pairhood f × singleValued f × zeroClause f × exactDom f
          × G126.O4.succClause f

  storyForm : Formula ⟪ Lset ω ⟫ 2
  storyForm = pairForm ∧̇ singleForm ∧̇ zeroForm ∧̇ exactDomForm
            ∧̇ G126.O4.succForm

  story-out : (f : SM) (x : ⟪ Lset ω ⟫)
            → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ storyForm ⟩ → story (fst f)
  story-out f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-out f x h₁
    , ( single-out f x h₂
      , ( zero-out f x h₃ , ( exactDom-out f x h₄ , G126.O4.succ-ok f x .fst h₅ ) ) ) )

  story-in : (f : SM) (x : ⟪ Lset ω ⟫)
           → story (fst f) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ storyForm ⟩
  story-in f x (h₁ , (h₂ , (h₃ , (h₄ , h₅)))) =
    ( pairhood-in f x h₁
    , ( single-in f x h₂
      , ( zero-in f x h₃ , ( exactDom-in f x h₄ , G126.O4.succ-ok f x .snd h₅ ) ) ) )

  story-ok : (f : SM) (x : ⟪ Lset ω ⟫)
           → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ storyForm ⟩ ⟷ story (fst f)
  story-ok f x = story-out f x , story-in f x

  -- O7, the value chain: a witness of the one-way story is honest, a present
  -- pair's value at an index in ω is the S-stage at that index, by induction
  -- on the numeral.  The base is the zero clause with Sset ∅ ≡ ∅; the step
  -- is the one-way successor clause with the tower's successor equation
  -- Sset (sucV β) ≡ step (Sset β).  (The HF chainValue shape, with the
  -- over-HF identification's step replaced by Sset-suc.)
  chainValue : (f : S) → story f → (a x : S) → ⟨ a ∈ˢ ω ⟩
             → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Sset a
  chainValue f st a x a∈ω ax∈f = PT.rec (setIsSet x (Sset a)) go a∈ω
    where
    h4 : exactDom f
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
      δStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ Lset ω ⟩ × IsOrd δ
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
          cStep (c , prnc) = st .snd .snd .snd .snd (# n) (Sset (# n)) x prn px
            where
            prn : ⟨ pr (# n) (Sset (# n)) ∈ˢ f ⟩
            prn = subst (λ w → ⟨ pr (# n) w ∈ˢ f ⟩) (chainNum n c prnc) prnc
        step≡Sset : step (Sset (# n)) ≡ Sset (# (suc n))
        step≡Sset = sym (Sset-suc (# n))
    go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ a) → x ≡ Sset a
    go (m , q) = subst (λ w → x ≡ Sset w) q (chainNum (lower m) x ax∈f')
      where
      ax∈f' : ⟨ pr (# (lower m)) x ∈ˢ f ⟩
      ax∈f' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) (sym q) ax∈f

  -- A common stage below ω for three members of Lset ω: pair the first two,
  -- stage the third, take the larger stage by the ordinal trichotomy.
  Lstage₃ : (x y z : S) → ⟨ x ∈ˢ Lset ω ⟩ → ⟨ y ∈ˢ Lset ω ⟩ → ⟨ z ∈ˢ Lset ω ⟩
          → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩
               × ⟨ z ∈ˢ Lset ξ ⟩) ∥₁
  Lstage₃ x y z x∈ y∈ z∈ = PT.rec squash₁ s₁ (Lstage₂ ω limω x y x∈ y∈)
    where
    s₁ : Σ[ ξ₁ ∈ S ] (⟨ ξ₁ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Lset ξ₁ ⟩ × ⟨ y ∈ˢ Lset ξ₁ ⟩)
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩
            × ⟨ z ∈ˢ Lset ξ ⟩) ∥₁
    s₁ (ξ₁ , ξ₁∈ω , x∈₁ , y∈₁) = PT.rec squash₁ s₂ (Lstage ω limω z z∈)
      where
      s₂ : Σ[ ξ₂ ∈ S ] (⟨ ξ₂ ∈ˢ ω ⟩ × ⟨ z ∈ˢ Lset ξ₂ ⟩)
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩
              × ⟨ z ∈ˢ Lset ξ ⟩) ∥₁
      s₂ (ξ₂ , ξ₂∈ω , z∈₂) = ∣ go tri ∣₁
        where
        tri : Tri ξ₁ ξ₂
        tri = ord-tri ξ₁ (limit-mem-ord ω limω ξ₁ ξ₁∈ω)
                   ξ₂ (limit-mem-ord ω limω ξ₂ ξ₂∈ω)
        go : Tri ξ₁ ξ₂ → Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Lset ξ ⟩
             × ⟨ y ∈ˢ Lset ξ ⟩ × ⟨ z ∈ˢ Lset ξ ⟩)
        go (inl ξ₁∈ξ₂) = ξ₂ , (ξ₂∈ω
          , Lset-mono {α = ξ₂} {β = ξ₁} ξ₁∈ξ₂ x∈₁
          , Lset-mono {α = ξ₂} {β = ξ₁} ξ₁∈ξ₂ y∈₁ , z∈₂)
        go (inr (inl ξ₁≡ξ₂)) = ξ₂ , (ξ₂∈ω
          , subst (λ w → ⟨ x ∈ˢ Lset w ⟩) ξ₁≡ξ₂ x∈₁
          , subst (λ w → ⟨ y ∈ˢ Lset w ⟩) ξ₁≡ξ₂ y∈₁ , z∈₂)
        go (inr (inr ξ₂∈ξ₁)) = ξ₁ , (ξ₁∈ω
          , x∈₁ , y∈₁ , Lset-mono {α = ξ₁} {β = ξ₂} ξ₂∈ξ₁ z∈₂)

  -- The binary-union operation closes inside the limit stage: Fof f5 a b is
  -- in Lset ω for a, b ∈ Lset ω, by the common-stage lemma and the
  -- sixteen-value read at that stage (the F5 arm of the finite-table
  -- closure; the F0 arm is the delivered Lpair-limit).
  Fof-f5-limit : (a b : S) → ⟨ a ∈ˢ Lset ω ⟩ → ⟨ b ∈ˢ Lset ω ⟩
               → ⟨ Fof f5 a b ∈ˢ Lset ω ⟩
  Fof-f5-limit a b a∈ b∈ = PT.rec (snd (Fof f5 a b ∈ˢ Lset ω)) atStage
    (Lstage₃ a b A a∈ b∈ A∈ω)
    where
    atStage : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × ⟨ a ∈ˢ Lset ξ ⟩ × ⟨ b ∈ˢ Lset ξ ⟩
               × ⟨ A ∈ˢ Lset ξ ⟩)
            → ⟨ Fof f5 a b ∈ˢ Lset ω ⟩
    atStage (ξ , ξ∈ω , a∈ξ , b∈ξ , A∈ξ) =
      Lset-mono {α = ω} {β = sucV ξ} (limit-succ-mem ω ξ limω ξ∈ω)
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

  -- O6, the finite-table closure: a finite family of members of Lset ω is a
  -- member of Lset ω, by the F0/F5 limit closures (the L-side analog of
  -- HF's finSetMem, which used the rud closure of Sset ω instead).
  finSet∈Lsetω : (n : ℕ) (h : Fin n → S)
               → ((i : Fin n) → ⟨ h i ∈ˢ Lset ω ⟩) → ⟨ finSet n h ∈ˢ Lset ω ⟩
  finSet∈Lsetω zero h hin = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (finSet0∅ h))
    (∅∈Lset ω limω ∅∈ω)
  finSet∈Lsetω (suc n) h hin =
    subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (finSetSuc n h)) big
    where
    S1 : S
    S1 = F0 (h zero) (h zero)
    X : S
    X = finSet n (h ∘ suc)
    P : S
    P = F0 S1 X
    S1∈ : ⟨ S1 ∈ˢ Lset ω ⟩
    S1∈ = Lpair-limit ω limω (h zero) (h zero) (hin zero) (hin zero)
    X∈ : ⟨ X ∈ˢ Lset ω ⟩
    X∈ = finSet∈Lsetω n (h ∘ suc) (λ i → hin (suc i))
    P∈ : ⟨ P ∈ˢ Lset ω ⟩
    P∈ = Lpair-limit ω limω S1 X S1∈ X∈
    big : ⟨ F5 P (h zero) ∈ˢ Lset ω ⟩
    big = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (Fof-f5 P (h zero))
      (Fof-f5-limit P (h zero) P∈ (hin zero))

  -- The honest segment of length n: the pairs (k, Sset k) for k ≤ n.
  seg : (n : ℕ) → S
  seg n = finSet (suc n) (λ i → pr (nk (toℕ i)) (Sset (nk (toℕ i))))

  seg∈Lsetω : (n : ℕ) → ⟨ seg n ∈ˢ Lset ω ⟩
  seg∈Lsetω n = finSet∈Lsetω (suc n) h pairs∈
    where
    h : Fin (suc n) → S
    h i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
    pairs∈ : (i : Fin (suc n)) → ⟨ h i ∈ˢ Lset ω ⟩
    pairs∈ i = Lpr-limit ω limω (nk (toℕ i)) (Sset (nk (toℕ i)))
      (numeral∈Lsetω (toℕ i)) (G125.memberAt (toℕ i) .snd)

  -- Pairhood: every segment member is a Kuratowski pair.
  segPair : (n : ℕ) (z : S) → ⟨ z ∈ˢ seg n ⟩ → isPair z
  segPair n z z∈ = PT.rec squash₁ go (finSet-out (suc n) h z z∈)
    where
    h : Fin (suc n) → S
    h i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
    go : Σ[ i ∈ Fin (suc n) ] (pr (nk (toℕ i)) (Sset (nk (toℕ i))) ≡ z)
       → isPair z
    go (i , q) = ∣ nk (toℕ i) , (Sset (nk (toℕ i)) , sym q) ∣₁

  -- Single-valuedness: equal first components force equal values.
  segSingle : (n : ℕ) → singleValued (seg n)
  segSingle n a b c ab∈ ac∈ = PT.rec (setIsSet b c) go₁
    (finSet-out (suc n) h (pr a b) ab∈)
    where
    h : Fin (suc n) → S
    h i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
    go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a b) → b ≡ c
    go₁ (i , q₁) = PT.rec (setIsSet b c) go₂
      (finSet-out (suc n) h (pr a c) ac∈)
      where
      a≡#i : a ≡ nk (toℕ i)
      a≡#i = pr-inj (sym q₁) .fst
      b≡ : b ≡ Sset (nk (toℕ i))
      b≡ = pr-inj (sym q₁) .snd
      go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr a c) → b ≡ c
      go₂ (j , q₂) = b≡ ∙ cong Sset (cong nk (#-inj′ {toℕ i} {toℕ j} #i≡#j))
                   ∙ sym (pr-inj (sym q₂) .snd)
        where
        #i≡#j : nk (toℕ i) ≡ nk (toℕ j)
        #i≡#j = sym a≡#i ∙ pr-inj (sym q₂) .fst

  -- The zero clause: the segment maps the empty set to itself.
  segZero : (n : ℕ) → zeroClause (seg n)
  segZero n = ∣ ∅ , (empt , pair) ∣₁
    where
    h : Fin (suc n) → S
    h i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
    idx : Fin (suc n)
    idx = zero
    h-idx : h idx ≡ pr ∅ ∅
    h-idx = cong₂ pr refl Sset-zero
    empt : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → Empty.⊥
    empt z z∈∅ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅)
    pair : ⟨ pr ∅ ∅ ∈ˢ seg n ⟩
    pair = finSet-in (suc n) h (pr ∅ ∅) ∣ idx , h-idx ∣₁

  -- The exact domain of the segment: the ordinal # (suc n).
  segDom : (n : ℕ) → exactDom (seg n)
  segDom n = ∣ nk (suc n) , ( numeral∈Lsetω (suc n) , numeral-ord (suc n)
    , in-dir , out-dir ) ∣₁
    where
    h : Fin (suc n) → S
    h i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
    in-dir : (a : S) → ⟨ a ∈ˢ nk (suc n) ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
    in-dir a a∈ = PT.rec squash₁ go (∈#-elim (suc n) a a∈)
      where
      go : Σ[ m ∈ ℕ ] ((m < suc n) × (a ≡ nk m)) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
      go (m , (p , q)) = ∣ Sset (nk m) , pr-in ∣₁
        where
        idx : Fin (suc n)
        idx = fromℕ' (suc n) m p
        e : toℕ idx ≡ m
        e = toFromId' (suc n) m p
        h-idx : h idx ≡ pr (nk m) (Sset (nk m))
        h-idx = cong₂ pr (cong nk e) (cong Sset (cong nk e))
        pr-in : ⟨ pr a (Sset (nk m)) ∈ˢ seg n ⟩
        pr-in = finSet-in (suc n) h (pr a (Sset (nk m)))
          ∣ idx , (h-idx ∙ cong₂ pr (sym q) refl) ∣₁
    out-dir : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁ → ⟨ a ∈ˢ nk (suc n) ⟩
    out-dir a = PT.rec (snd (a ∈ˢ nk (suc n))) go
      where
      go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ → ⟨ a ∈ˢ nk (suc n) ⟩
      go (b , ab∈) = PT.rec (snd (a ∈ˢ nk (suc n))) go₂
        (finSet-out (suc n) h (pr a b) ab∈)
        where
        go₂ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a b) → ⟨ a ∈ˢ nk (suc n) ⟩
        go₂ (i , q) = subst (λ w → ⟨ w ∈ˢ nk (suc n) ⟩)
          (sym (pr-inj (sym q) .fst)) (#mono (toℕ i) (suc n) (toℕ<n i))

  -- The one-way successor clause holds on the segment, by the tower's
  -- successor equation Sset (sucV a) ≡ step (Sset a).
  segSucc1 : (n : ℕ) → G126.O4.succClause (seg n)
  segSucc1 n a c b ac∈ ab∈ = PT.rec (setIsSet b (step c)) go₁
    (finSet-out (suc n) h (pr a c) ac∈)
    where
    h : Fin (suc n) → S
    h i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
    go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a c) → b ≡ step c
    go₁ (i , q₁) = PT.rec (setIsSet b (step c)) go₂
      (finSet-out (suc n) h (pr (sucV a) b) ab∈)
      where
      a≡#i : a ≡ nk (toℕ i)
      a≡#i = pr-inj (sym q₁) .fst
      c≡Sseta : c ≡ Sset a
      c≡Sseta = pr-inj (sym q₁) .snd ∙ cong Sset (sym a≡#i)
      go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr (sucV a) b) → b ≡ step c
      go₂ (j , q₂) = b≡SsetSucA ∙ Sset-suc a ∙ cong step (sym c≡Sseta)
        where
        sucA≡#j : sucV a ≡ nk (toℕ j)
        sucA≡#j = pr-inj (sym q₂) .fst
        b≡SsetSucA : b ≡ Sset (sucV a)
        b≡SsetSucA = pr-inj (sym q₂) .snd ∙ cong Sset (sym sucA≡#j)

  -- The value Sset (# m) lies in the range of its own segment.
  segRan : (m : ℕ) → Sset (nk m) ∈ran seg m
  segRan m = ∣ nk m , pair ∣₁
    where
    h : Fin (suc m) → S
    h i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
    idx : Fin (suc m)
    idx = fromℕ' (suc m) m (≤-refl {suc m})
    e : toℕ idx ≡ m
    e = toFromId' (suc m) m (≤-refl {suc m})
    h-idx : h idx ≡ pr (nk m) (Sset (nk m))
    h-idx = cong₂ pr (cong nk e) (cong Sset (cong nk e))
    pair : ⟨ pr (nk m) (Sset (nk m)) ∈ˢ seg m ⟩
    pair = finSet-in (suc m) h (pr (nk m) (Sset (nk m))) ∣ idx , h-idx ∣₁

  -- The segment satisfies the one-way story.
  segStory : (n : ℕ) → story (seg n)
  segStory n = segPair n , (segSingle n , (segZero n , (segDom n , segSucc1 n)))

  -- The family formula: a carrier member satisfies the one-way story and
  -- ranges over x.
  ψ : Formula ⟪ Lset ω ⟫ 1
  ψ = ∃̇ (storyForm ∧̇ Rg)

  -- Satisfaction of ψ decodes to the meta story, with the range read.
  ψ-out : (x : ⟪ Lset ω ⟫) → ⟨ (ι x ∷ []) ⊨ᵐ ψ ⟩
        → ∥ Σ[ f ∈ SM ] (story (fst f) × (⟪ Lset ω ⟫↪ x ∈ran fst f)) ∥₁
  ψ-out x = PT.map go
    where
    go : Σ[ f ∈ SM ] ⟨ (f ∷ ι x ∷ []) ⊨ᵐ (storyForm ∧̇ Rg) ⟩
       → Σ[ f ∈ SM ] (story (fst f) × (⟪ Lset ω ⟫↪ x ∈ran fst f))
    go (f , (st , rg)) = f , (story-ok f x .fst st , r-ok f x .fst rg)

  -- The satisfaction of ψ is built from the meta story.
  ψ-in : (x : ⟪ Lset ω ⟫)
       → ∥ Σ[ f ∈ SM ] (story (fst f) × (⟪ Lset ω ⟫↪ x ∈ran fst f)) ∥₁
       → ⟨ (ι x ∷ []) ⊨ᵐ ψ ⟩
  ψ-in x = PT.rec (snd ((ι x ∷ []) ⊨ᵐ ψ)) go
    where
    go : Σ[ f ∈ SM ] (story (fst f) × (⟪ Lset ω ⟫↪ x ∈ran fst f))
       → ⟨ (ι x ∷ []) ⊨ᵐ ψ ⟩
    go (f , (st , rg)) = ∣ f , (story-ok f x .snd st , r-ok f x .snd rg) ∣₁

  -- O8, the non-overshoot direction: every carved member is an S-stage below
  -- ω, through the chain (O7), the exact domain and the strengthened bound.
  carve-⊇ : (y : S) → ⟨ y ∈ˢ D.defSet ψ ⟩
          → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) ∥₁
  carve-⊇ y y∈ = fStep
    (∈-asFiber {a = y} {b = Lset ω} (D.defSet⊆A ψ y y∈))
    where
    fStep : Σ[ m ∈ ⟪ Lset ω ⟫ ] (⟪ Lset ω ⟫↪ m ≡ y)
          → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) ∥₁
    fStep (m , q) = PT.rec squash₁ wStep (ψ-out m sat)
      where
      sat : ⟨ (ι m ∷ []) ⊨ᵐ ψ ⟩
      sat = subst ⟨_⟩ (D.defSet-mem ψ m)
        (subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (sym q) y∈)
      wStep : Σ[ f ∈ SM ] (story (fst f) × (⟪ Lset ω ⟫↪ m ∈ran fst f))
            → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) ∥₁
      wStep (f , (st , r)) = PT.rec squash₁ aStep r
        where
        aStep : Σ[ a ∈ S ] ⟨ pr a (⟪ Lset ω ⟫↪ m) ∈ˢ fst f ⟩
              → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) ∥₁
        aStep (a , pr∈) = PT.rec squash₁ dStep (st .snd .snd .snd .fst)
          where
          dStep : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ Lset ω ⟩ × IsOrd δ
                   × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁)
                   × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
                → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) ∥₁
          dStep (δ , (δ∈u , ordδ , _ , out-d)) = ∣ a , (a∈ω , y≡Sseta) ∣₁
            where
            a∈δ : ⟨ a ∈ˢ δ ⟩
            a∈δ = out-d a ∣ ⟪ Lset ω ⟫↪ m , pr∈ ∣₁
            δ∈ω : ⟨ δ ∈ˢ ω ⟩
            δ∈ω = ord∈Lset→∈ ω ω-ord δ ordδ δ∈u
            a∈ω : ⟨ a ∈ˢ ω ⟩
            a∈ω = ω-ord .fst {x = δ} {y = a} a∈δ δ∈ω
            y≡Sseta : y ≡ Sset a
            y≡Sseta = sym q ∙ chainValue (fst f) st a (⟪ Lset ω ⟫↪ m) a∈ω pr∈

  -- O8, the overshoot-blocked direction: every S-stage below ω is carved,
  -- through the honest segment of the right length, its story check (O6)
  -- and the range read.
  carve-⊆ : (y : S) → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) ∥₁
          → ⟨ y ∈ˢ D.defSet ψ ⟩
  carve-⊆ y = PT.rec (snd (y ∈ˢ D.defSet ψ)) go
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) → ⟨ y ∈ˢ D.defSet ψ ⟩
    go (δ , (δ∈ω , y≡)) = subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (sym y≡)
      (carve δ δ∈ω)
      where
      carve : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟨ Sset δ ∈ˢ D.defSet ψ ⟩
      carve δ δ∈ω = PT.rec (snd (Sset δ ∈ˢ D.defSet ψ)) g δ∈ω
        where
        carve# : (m : ℕ) → ⟨ Sset (nk m) ∈ˢ D.defSet ψ ⟩
        carve# m = subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (fm .snd)
          (subst ⟨_⟩ (sym (D.defSet-mem ψ (fm .fst)))
            (ψ-in (fm .fst) ∣ (seg m , seg∈Lsetω m)
              , (segStory m , subst (λ w → w ∈ran seg m) (sym (fm .snd))
                  (segRan m)) ∣₁))
          where
          fm : Σ[ x ∈ ⟪ Lset ω ⟫ ] (⟪ Lset ω ⟫↪ x ≡ Sset (nk m))
          fm = ∈-asFiber {a = Sset (nk m)} {b = Lset ω} (G125.memberAt m .snd)
        g : Σ[ m ∈ Lift ℕ ] (nk (lower m) ≡ δ) → ⟨ Sset δ ∈ˢ D.defSet ψ ⟩
        g (m , q) = subst (λ w → ⟨ w ∈ˢ D.defSet ψ ⟩) (cong Sset q)
          (carve# (lower m))

  -- The family equality, membership-wise: the carve is exactly the S-stages
  -- below ω, in both directions.
  family-char : (y : S) → ⟨ y ∈ˢ D.defSet ψ ⟩
              ⟷ ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Sset δ)) ∥₁
  family-char y = carve-⊇ y , carve-⊆ y

  -- Exercise: the family equality at the first stage, both directions on
  -- one concrete point, y = Sset ∅.
  eq∅ : ⟨ Sset ∅ ∈ˢ D.defSet ψ ⟩
  eq∅ = carve-⊆ (Sset ∅) ∣ ∅ , (∅∈ω , refl) ∣₁

  round∅ : ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (Sset ∅ ≡ Sset δ)) ∥₁
  round∅ = carve-⊇ (Sset ∅) eq∅
