{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.279 re-run (C-45).  Imports the landed master L.InjChain and
-- instantiates its row-1 composition at [LJ-1.134]'s concrete
-- non-degenerate graph {⟨a,a⟩} over {a}, composed WITH ITSELF, and shows
-- the composite is inhabited and runs.  This is the C-38 guard: nothing
-- above is vacuously true.  It also re-asserts row 5's squareω.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-279.ReRun {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( pair-spec )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( svAt; svAt-in; domAt; domAt-intro; prʟ; prʟ-fst )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst; numeralL )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.InjChain {ℓ} lem using ( module Comp; pairω; pairω-inj; squareω )

open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( ω )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The concrete graph, from ProbeLJ1134A, re-derived at this site.
module Concrete (a : S) where

  G : S
  G = pairʟ (prʟ a a) (prʟ a a)

  Dm : S
  Dm = pairʟ a a

  p₀ : V ℓ
  p₀ = pr (fst a) (fst a)

  G-fst : fst G ≡ ⁅ p₀ , p₀ ⁆
  G-fst = pairʟ-fst (prʟ a a) (prʟ a a)
        ∙ cong₂ ⁅_,_⁆ (prʟ-fst a a) (prʟ-fst a a)

  D-fst : fst Dm ≡ ⁅ fst a , fst a ⁆
  D-fst = pairʟ-fst a a

  memG : (z : V ℓ) → ⟨ z ∈ fst G ⟩ → z ≡ p₀
  memG z h = PT.rec (setIsSet z p₀) (λ { (inl e) → e ; (inr e) → e })
    (subst ⟨_⟩ (pair-spec p₀ p₀ z) (subst (λ w → ⟨ z ∈ w ⟩) G-fst h))

  inG : ⟨ p₀ ∈ fst G ⟩
  inG = subst (λ w → ⟨ p₀ ∈ w ⟩) (sym G-fst)
          (subst ⟨_⟩ (sym (pair-spec p₀ p₀ p₀)) ∣ inl refl ∣₁)

  memD : (z : V ℓ) → ⟨ z ∈ fst Dm ⟩ → z ≡ fst a
  memD z h = PT.rec (setIsSet z (fst a)) (λ { (inl e) → e ; (inr e) → e })
    (subst ⟨_⟩ (pair-spec (fst a) (fst a) z) (subst (λ w → ⟨ z ∈ w ⟩) D-fst h))

  inD : ⟨ fst a ∈ fst Dm ⟩
  inD = subst (λ w → ⟨ fst a ∈ w ⟩) (sym D-fst)
          (subst ⟨_⟩ (sym (pair-spec (fst a) (fst a) (fst a))) ∣ inl refl ∣₁)

  γ : S ^ 2
  γ = G ∷ Dm ∷ []

  split : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
        → (fst x ≡ fst a) × (fst y ≡ fst a)
  split x y h = pr-inj (memG (pr (fst x) (fst y)) h)

  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ
    (λ x y y' p q → snd (split x y p) ∙ sym (snd (split x y' q)))

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ
    (λ y x x' p q → fst (split x y p) ∙ sym (fst (split x' y q)))

  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
        → ⟨ fst x ∈ fst Dm ⟩
    fwd x = PT.rec (snd (fst x ∈ fst Dm))
      (λ { (y , p) →
        subst (λ w → ⟨ w ∈ fst Dm ⟩) (sym (fst (split x y p))) inD })

    bwd : (x : S) → ⟨ fst x ∈ fst Dm ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ a , subst (λ w → ⟨ pr w (fst a) ∈ fst G ⟩)
                     (sym (memD (fst x) m)) inG ∣₁

module Witness (a : S) where

  module Cc = Concrete a

  ranC : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst Cc.G ⟩ → ⟨ fst y ∈ fst Cc.Dm ⟩
  ranC x y h = subst (λ w → ⟨ w ∈ fst Cc.Dm ⟩)
                 (sym (snd (Cc.split x y h))) Cc.inD

  module Co = Comp Cc.Dm Cc.Dm Cc.Dm Cc.G Cc.G
                   Cc.sv Cc.dm Cc.ij ranC
                   Cc.sv Cc.dm Cc.ij ranC

  -- The composite is NOT empty: the pair ⟨a,a⟩ is in it.
  inK : ⟨ pr (fst a) (fst a) ∈ fst Co.K ⟩
  inK = Co.K-in a a a Cc.inD Cc.inD Cc.inG Cc.inG

  -- The composite runs: an honest injection out of the domain.
  theComposite : ⟪ fst Cc.Dm ⟫ → ⟪ fst Cc.Dm ⟫
  theComposite = Co.compFun

  theComposite-inj : (m n : ⟪ fst Cc.Dm ⟫)
                   → theComposite m ≡ theComposite n → m ≡ n
  theComposite-inj = Co.compFun-inj

-- A fully concrete instance, at the numeral zero.
module WitnessZero = Witness (numeralL 0)

-- Row 5, re-asserted: the square law at ω, from the landed master.
squareω-again : sq ω
squareω-again = squareω

pairω-runs : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
pairω-runs = pairω

pairω-inj-again : (p q : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω p ≡ pairω q → p ≡ q
pairω-inj-again = pairω-inj
