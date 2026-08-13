{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT68 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_; _∧̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ∋⊆; Lset-out; Lset-mono )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Ordinal {ℓ} using ( #∈ω; numeral-ord; ω-ord; ∈#-elim )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; finSet; finSet-in; finSet-out )
open import L.Rud.Step {ℓ} lem A using ( Sset; Sset-trans; f9; Fof-f9 )
open import L.Rud.Bridge {ℓ} lem A using ( Lset-zero )
open import L.Rud.BaseBlock {ℓ} lem A using
  ( limω; ∅∈Ssetω; baseStage∈J; op-in-J; finSetMem )
open import L.Rud.LevelSigma {ℓ} lem A using ( module LevelAt )
open import L.Rud.HF {ℓ} lem A
open import L.Definability {ℓ} using ( module DefOf )
open import L.InitialSegment {ℓ} using ( _∈ran_; _⟷_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Order using ( _<_; ≤-refl )
open import Cubical.Data.FinData.Base using ( toℕ; zero )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2; isPropΠ3 )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Numerals are members of HF: via Lset ω, then Lset ω ⊆ Sset ω.
numeral∈Lsetω : (k : ℕ) → ⟨ nk k ∈ˢ Lset ω ⟩
numeral∈Lsetω k = Lset-mono {α = ω} {β = sucV (nk k)} (#∈ω (suc k))
  (ord∈Lset-suc (nk k) (numeral-ord k))

Lsetω⊆Ssetω : Lset ω ⊆ Sset ω
Lsetω⊆Ssetω x x∈L = PT.rec (snd (x ∈ˢ Sset ω)) go (Lset-out ω x x∈L)
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ x ∈ˢ Sset ω ⟩
  go (δ , δ∈ω , x∈𝒟) = Sset-trans ω
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟)
    (baseStage∈J δ δ∈ω (stage∈HF δ δ∈ω))

numeral∈HF : (k : ℕ) → ⟨ nk k ∈ˢ Sset ω ⟩
numeral∈HF k = Lsetω⊆Ssetω (nk k) (numeral∈Lsetω k)

-- Pairing closes in HF.
pr-in-HF : (a b : S) → ⟨ a ∈ˢ Sset ω ⟩ → ⟨ b ∈ˢ Sset ω ⟩ → ⟨ pr a b ∈ˢ Sset ω ⟩
pr-in-HF a b a∈ b∈ = subst (λ w → ⟨ w ∈ˢ Sset ω ⟩) (Fof-f9 a b) (op-in-J f9 a b a∈ b∈)

-- The honest segment of length n: the pairs (k, Lset k) for k ≤ n.
seg : (n : ℕ) → S
seg n = finSet (suc n) (λ i → pr (nk (toℕ i)) (Lset (nk (toℕ i))))

seg∈HF : (n : ℕ) → ⟨ seg n ∈ˢ Sset ω ⟩
seg∈HF n = finSetMem (suc n) h (λ i → pr-in-HF (nk (toℕ i)) (Lset (nk (toℕ i)))
  (numeral∈HF (toℕ i)) (stage∈HF (nk (toℕ i)) (#∈ω (toℕ i))))
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))

-- Pairhood: every segment member is a Kuratowski pair.
segPair : (n : ℕ) (z : S) → ⟨ z ∈ˢ seg n ⟩ → isPair z
segPair n z z∈ = PT.rec squash₁ go (finSet-out (suc n) h z z∈)
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  go : Σ[ i ∈ Fin (suc n) ] (pr (nk (toℕ i)) (Lset (nk (toℕ i))) ≡ z) → isPair z
  go (i , q) = ∣ nk (toℕ i) , (Lset (nk (toℕ i)) , sym q) ∣₁

-- Single-valuedness: equal first components force equal values.
segSingle : (n : ℕ) → LA.singleValued (seg n)
segSingle n a b c ab∈ ac∈ = PT.rec (setIsSet b c) go₁
  (finSet-out (suc n) h (pr a b) ab∈)
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a b) → b ≡ c
  go₁ (i , q₁) = PT.rec (setIsSet b c) go₂
    (finSet-out (suc n) h (pr a c) ac∈)
    where
    a≡#i : a ≡ nk (toℕ i)
    a≡#i = pr-inj (sym q₁) .fst
    b≡ : b ≡ Lset (nk (toℕ i))
    b≡ = pr-inj (sym q₁) .snd
    go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr a c) → b ≡ c
    go₂ (j , q₂) = b≡ ∙ cong Lset (cong nk (#-inj′ {toℕ i} {toℕ j} #i≡#j))
                 ∙ sym (pr-inj (sym q₂) .snd)
      where
      #i≡#j : nk (toℕ i) ≡ nk (toℕ j)
      #i≡#j = sym a≡#i ∙ pr-inj (sym q₂) .fst

-- The zero clause: the segment maps the empty set to itself.
segZero : (n : ℕ) → LA.zeroClause (seg n)
segZero n = ∣ ∅ , (empt , pair) ∣₁
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  idx : Fin (suc n)
  idx = zero
  h-idx : h idx ≡ pr ∅ ∅
  h-idx = cong₂ pr refl Lset-zero
  empt : (z : S) → ⟨ z ∈ˢ ∅ ⟩ → Empty.⊥
  empt z z∈∅ = ∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅)
  pair : ⟨ pr ∅ ∅ ∈ˢ seg n ⟩
  pair = finSet-in (suc n) h (pr ∅ ∅) ∣ idx , h-idx ∣₁

-- The exact domain of the segment: the ordinal # (suc n).
segDom : (n : ℕ) → LA.exactDom (seg n)
segDom n = ∣ nk (suc n) , ( numeral∈HF (suc n) , numeral-ord (suc n)
  , in-dir , out-dir ) ∣₁
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  in-dir : (a : S) → ⟨ a ∈ˢ nk (suc n) ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
  in-dir a a∈ = PT.rec squash₁ go (∈#-elim (suc n) a a∈)
    where
    go : Σ[ m ∈ ℕ ] ((m < suc n) × (a ≡ nk m)) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg n ⟩ ∥₁
    go (m , (p , q)) = ∣ Lset (nk m) , pair∈ ∣₁
      where
      idx : Fin (suc n)
      idx = fromℕ' (suc n) m p
      e : toℕ idx ≡ m
      e = toFromId' (suc n) m p
      h-idx : h idx ≡ pr (nk m) (Lset (nk m))
      h-idx = cong₂ pr (cong nk e) (cong Lset (cong nk e))
      pair∈ : ⟨ pr a (Lset (nk m)) ∈ˢ seg n ⟩
      pair∈ = finSet-in (suc n) h (pr a (Lset (nk m)))
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

-- The one-way successor clause holds on the segment.
segSucc1 : (n : ℕ) → LA.succValClause1 (seg n)
segSucc1 n a c b ac∈ ab∈ = PT.rec (powRelProp c b) go₁
  (finSet-out (suc n) h (pr a c) ac∈)
  where
  h : Fin (suc n) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  go₁ : Σ[ i ∈ Fin (suc n) ] (h i ≡ pr a c) → LA.powRel c b
  go₁ (i , q₁) = PT.rec (powRelProp c b) go₂
    (finSet-out (suc n) h (pr (sucV a) b) ab∈)
    where
    a≡#i : a ≡ nk (toℕ i)
    a≡#i = pr-inj (sym q₁) .fst
    c≡Lseta : c ≡ Lset a
    c≡Lseta = pr-inj (sym q₁) .snd ∙ cong Lset (sym a≡#i)
    a∈ω : ⟨ a ∈ˢ ω ⟩
    a∈ω = subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym a≡#i) (#∈ω (toℕ i))
    go₂ : Σ[ j ∈ Fin (suc n) ] (h j ≡ pr (sucV a) b) → LA.powRel c b
    go₂ (j , q₂) = subst (λ w → LA.powRel c w) (sym b≡)
      (subst (λ w → LA.powRel w (Lset (sucV a))) (sym c≡Lseta)
        (powRel-Lset-suc a a∈ω))
      where
      sucV-a≡#i' : sucV a ≡ nk (suc (toℕ i))
      sucV-a≡#i' = cong sucV a≡#i
      #i'≡#j : nk (suc (toℕ i)) ≡ nk (toℕ j)
      #i'≡#j = sym sucV-a≡#i' ∙ pr-inj (sym q₂) .fst
      b≡ : b ≡ Lset (sucV a)
      b≡ = pr-inj (sym q₂) .snd
         ∙ sym (cong Lset (cong nk (#-inj′ {suc (toℕ i)} {toℕ j} #i'≡#j)))
         ∙ cong Lset (cong sucV (sym a≡#i))

-- The value Lset (# m) lies in the range of its own segment.
segRan : (m : ℕ) → Lset (nk m) ∈ran seg m
segRan m = ∣ nk m , pair ∣₁
  where
  h : Fin (suc m) → S
  h i = pr (nk (toℕ i)) (Lset (nk (toℕ i)))
  idx : Fin (suc m)
  idx = fromℕ' (suc m) m (≤-refl {suc m})
  e : toℕ idx ≡ m
  e = toFromId' (suc m) m (≤-refl {suc m})
  h-idx : h idx ≡ pr (nk m) (Lset (nk m))
  h-idx = cong₂ pr (cong nk e) (cong Lset (cong nk e))
  pair : ⟨ pr (nk m) (Lset (nk m)) ∈ˢ seg m ⟩
  pair = finSet-in (suc m) h (pr (nk m) (Lset (nk m))) ∣ idx , h-idx ∣₁

-- The segment satisfies the one-way story.
segStory : (n : ℕ) → LA.aSt1 (seg n)
segStory n = segPair n , (segSingle n , (segZero n , (segDom n , segSucc1 n)))

-- The satisfaction of ψ is built from the meta story.
ψ-in : (x : ⟪ Sset ω ⟫)
     → ∥ Σ[ f ∈ LA.U.SM ] (LA.aSt1 (fst f) × (⟪ Sset ω ⟫↪ x ∈ran fst f)) ∥₁
     → ⟨ (LA.U.ι x ∷ []) LA.U.⊨ᵐ ψ ⟩
ψ-in x = PT.rec (snd ((LA.U.ι x ∷ []) LA.U.⊨ᵐ ψ)) go
  where
  go : Σ[ f ∈ LA.U.SM ] (LA.aSt1 (fst f) × (⟪ Sset ω ⟫↪ x ∈ran fst f))
     → ⟨ (LA.U.ι x ∷ []) LA.U.⊨ᵐ ψ ⟩
  go (f , (st , rg)) = ∣ f , (LA.aSt1-ok f x .snd st , LA.r-ok f x .snd rg) ∣₁

-- Every L-stage below ω is carved.
carve-⊆ : (y : S) → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
        → ⟨ y ∈ˢ LA.U.defSet ψ ⟩
carve-⊆ y = PT.rec (snd (y ∈ˢ LA.U.defSet ψ)) go
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) → ⟨ y ∈ˢ LA.U.defSet ψ ⟩
  go (δ , (δ∈ω , y≡)) = subst (λ w → ⟨ w ∈ˢ LA.U.defSet ψ ⟩) (sym y≡) (carve δ δ∈ω)
    where
    carve : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟨ Lset δ ∈ˢ LA.U.defSet ψ ⟩
    carve δ δ∈ω = PT.rec (snd (Lset δ ∈ˢ LA.U.defSet ψ)) g δ∈ω
      where
      carve# : (m : ℕ) → ⟨ Lset (nk m) ∈ˢ LA.U.defSet ψ ⟩
      carve# m = subst (λ w → ⟨ w ∈ˢ LA.U.defSet ψ ⟩) (fm .snd)
        (subst ⟨_⟩ (sym (LA.U.defSet-mem ψ (fm .fst)))
          (ψ-in (fm .fst) ∣ (seg m , seg∈HF m)
            , (segStory m , subst (λ w → w ∈ran seg m) (sym (fm .snd)) (segRan m)) ∣₁))
        where
        fm : Σ[ x ∈ ⟪ Sset ω ⟫ ] (⟪ Sset ω ⟫↪ x ≡ Lset (nk m))
        fm = ∈-asFiber {a = Lset (nk m)} {b = Sset ω} (stage∈HF (nk m) (#∈ω m))
      g : Σ[ m ∈ Lift ℕ ] (nk (lower m) ≡ δ) → ⟨ Lset δ ∈ˢ LA.U.defSet ψ ⟩
      g (m , q) = subst (λ w → ⟨ w ∈ˢ LA.U.defSet ψ ⟩) (cong Lset q) (carve# (lower m))

-- The family equality, membership-wise: the carve is exactly the stages
-- below ω, in both directions.
family-char : (y : S) → ⟨ y ∈ˢ LA.U.defSet ψ ⟩
            ⟷ ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × (y ≡ Lset δ)) ∥₁
family-char y = carve-⊇ y , carve-⊆ y
