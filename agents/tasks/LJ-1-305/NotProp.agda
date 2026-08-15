{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.305] PROBE A.  Is `sq ω` an hProp?  NO, MEASURED.
--
-- Build two provably distinct elements of `sq ω`.  The first is the
-- delivered base `squareω` (L.InjChain:184-185).  The second composes
-- it with the transposition of the two numeral points of `⟪ ω ⟫`.
-- The transposition is definable because `lem` decides paths in V:
-- `setIsSet` (Cubical.HITs.CumulativeHierarchy.Base:40) makes each
-- path type `x ≡ y` a proposition, so `LEM (ℓ-suc ℓ)` applies to it.
--
-- This closes route 1 of the brief.  A `∥_∥₁` over `sq α` cannot be
-- stripped by `PT.rec` at any site where two numerals are members,
-- because the motive is not propositional.  The term below is the
-- countermodel the abort criterion demands.
--
-- Tracked probe.  ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-305.NotProp {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( fiber; ↪-inj )
open import V.Coding {ℓ} using ( #-inj′ )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.InjChain {ℓ} lem using ( squareω )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_; ΣPathP )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Properties using ( znots )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- Paths in V are propositions, so `lem` decides them.  The positive
-- side carries the path as data.  This is the one classical input.
decV : (x y : V ℓ) → (x ≡ y) ⊎ ((x ≡ y) → Empty.⊥)
decV x y = lem ((x ≡ y) , setIsSet x y)

-- The two numeral points of `⟪ ω ⟫`, with their member readings.
n₀ n₁ : ⟪ ω ⟫
n₀ = fiber ω (#∈ω zero) .fst
n₁ = fiber ω (#∈ω (suc zero)) .fst

mem₀ : ⟪ ω ⟫↪ n₀ ≡ # zero
mem₀ = fiber ω (#∈ω zero) .snd

mem₁ : ⟪ ω ⟫↪ n₁ ≡ # suc zero
mem₁ = fiber ω (#∈ω (suc zero)) .snd

#₀≢#₁ : (# zero ≡ # suc zero) → Empty.⊥
#₀≢#₁ e = znots (#-inj′ {zero} {suc zero} e)

#₁≢#₀ : (# suc zero ≡ # zero) → Empty.⊥
#₁≢#₀ e = #₀≢#₁ (sym e)

mem-inj : (m n : ⟪ ω ⟫) → (⟪ ω ⟫↪ m ≡ ⟪ ω ⟫↪ n) → m ≡ n
mem-inj m n p = ↪-inj {a = ω} p

-- Distinct numerals give distinct points, and a point whose member is
-- a numeral cannot be fixed by the transposition.
n₁≢n₀ : (n₁ ≡ n₀) → Empty.⊥
n₁≢n₀ u = #₁≢#₀ (sym mem₁ ∙ cong ⟪ ω ⟫↪ u ∙ mem₀)

n₀≢n₁ : (n₀ ≡ n₁) → Empty.⊥
n₀≢n₁ u = #₀≢#₁ (sym mem₀ ∙ cong ⟪ ω ⟫↪ u ∙ mem₁)

n₁≢other : (m : ⟪ ω ⟫) → (n₁ ≡ m)
         → ((⟪ ω ⟫↪ m ≡ # suc zero) → Empty.⊥) → Empty.⊥
n₁≢other m u ¬₁ = ¬₁ (cong ⟪ ω ⟫↪ (sym u) ∙ mem₁)

other≢n₁ : (m : ⟪ ω ⟫) → (m ≡ n₁)
         → ((⟪ ω ⟫↪ m ≡ # suc zero) → Empty.⊥) → Empty.⊥
other≢n₁ m u ¬₁ = ¬₁ (cong ⟪ ω ⟫↪ u ∙ mem₁)

n₀≢other : (m : ⟪ ω ⟫) → (n₀ ≡ m)
         → ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥) → Empty.⊥
n₀≢other m u ¬₀ = ¬₀ (cong ⟪ ω ⟫↪ (sym u) ∙ mem₀)

other≢n₀ : (m : ⟪ ω ⟫) → (m ≡ n₀)
         → ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥) → Empty.⊥
other≢n₀ m u ¬₀ = ¬₀ (cong ⟪ ω ⟫↪ u ∙ mem₀)

-- THE TRANSPOSITION.  Swap the two numeral points, fix everything
-- else.  The helper takes its decisions as arguments so that every
-- case below reduces on constructors.
swapBy : (m : ⟪ ω ⟫)
       → ((⟪ ω ⟫↪ m ≡ # zero) ⊎ ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥))
       → ((⟪ ω ⟫↪ m ≡ # suc zero) ⊎ ((⟪ ω ⟫↪ m ≡ # suc zero) → Empty.⊥))
       → ⟪ ω ⟫
swapBy m (inl _) _ = n₁
swapBy m (inr _) (inl _) = n₀
swapBy m (inr _) (inr _) = m

swap : ⟪ ω ⟫ → ⟪ ω ⟫
swap m = swapBy m (decV (⟪ ω ⟫↪ m) (# zero)) (decV (⟪ ω ⟫↪ m) (# suc zero))

-- Where the transposition sends each kind of point.  Each helper
-- takes its decisions as ARGUMENTS and matches on constructors, so no
-- clause normalizes a V-path: the with-abstraction form of these
-- lemmas exhausted an 8 GB heap (P-i, measured at this probe).
swap-at₀ : (m : ⟪ ω ⟫) → (⟪ ω ⟫↪ m ≡ # zero) → swap m ≡ n₁
swap-at₀ m e = go (decV (⟪ ω ⟫↪ m) (# zero))
  where
  go : (d : (⟪ ω ⟫↪ m ≡ # zero) ⊎ ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥))
     → swapBy m d (decV (⟪ ω ⟫↪ m) (# suc zero)) ≡ n₁
  go (inl _) = refl
  go (inr nx) = Empty.rec (nx e)

swap-at₁ : (m : ⟪ ω ⟫) → (⟪ ω ⟫↪ m ≡ # suc zero) → swap m ≡ n₀
swap-at₁ m e =
  go (decV (⟪ ω ⟫↪ m) (# zero)) (decV (⟪ ω ⟫↪ m) (# suc zero))
  where
  go : (d₀ : (⟪ ω ⟫↪ m ≡ # zero) ⊎ ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥))
     → (d₁ : (⟪ ω ⟫↪ m ≡ # suc zero) ⊎ ((⟪ ω ⟫↪ m ≡ # suc zero) → Empty.⊥))
     → swapBy m d₀ d₁ ≡ n₀
  go (inl p) _ = Empty.rec (#₁≢#₀ (sym e ∙ p))
  go (inr _) (inl _) = refl
  go (inr _) (inr nx) = Empty.rec (nx e)

swap-fix : (m : ⟪ ω ⟫)
         → ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥)
         → ((⟪ ω ⟫↪ m ≡ # suc zero) → Empty.⊥)
         → swap m ≡ m
swap-fix m ¬₀ ¬₁ =
  go (decV (⟪ ω ⟫↪ m) (# zero)) (decV (⟪ ω ⟫↪ m) (# suc zero))
  where
  go : (d₀ : (⟪ ω ⟫↪ m ≡ # zero) ⊎ ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥))
     → (d₁ : (⟪ ω ⟫↪ m ≡ # suc zero) ⊎ ((⟪ ω ⟫↪ m ≡ # suc zero) → Empty.⊥))
     → swapBy m d₀ d₁ ≡ m
  go (inl p) _ = Empty.rec (¬₀ p)
  go (inr _) (inl p) = Empty.rec (¬₁ p)
  go (inr _) (inr _) = refl

swap-inj : (m n : ⟪ ω ⟫) → swap m ≡ swap n → m ≡ n
swap-inj m n e =
  go (decV (⟪ ω ⟫↪ m) (# zero)) (decV (⟪ ω ⟫↪ n) (# zero))
     (decV (⟪ ω ⟫↪ m) (# suc zero)) (decV (⟪ ω ⟫↪ n) (# suc zero)) e
  where
  go : (dm₀ : (⟪ ω ⟫↪ m ≡ # zero) ⊎ ((⟪ ω ⟫↪ m ≡ # zero) → Empty.⊥))
     → (dn₀ : (⟪ ω ⟫↪ n ≡ # zero) ⊎ ((⟪ ω ⟫↪ n ≡ # zero) → Empty.⊥))
     → (dm₁ : (⟪ ω ⟫↪ m ≡ # suc zero) ⊎ ((⟪ ω ⟫↪ m ≡ # suc zero) → Empty.⊥))
     → (dn₁ : (⟪ ω ⟫↪ n ≡ # suc zero) ⊎ ((⟪ ω ⟫↪ n ≡ # suc zero) → Empty.⊥))
     → swapBy m dm₀ dm₁ ≡ swapBy n dn₀ dn₁ → m ≡ n
  go (inl p) (inl q) _ _ _ = mem-inj m n (p ∙ sym q)
  go (inl _) (inr _) _ (inl _) eq = Empty.rec (n₁≢n₀ eq)
  go (inl _) (inr _) _ (inr nq₁) eq = Empty.rec (n₁≢other n eq nq₁)
  go (inr _) (inl _) (inl _) _ eq = Empty.rec (n₀≢n₁ eq)
  go (inr _) (inl _) (inr np₁) _ eq = Empty.rec (other≢n₁ m eq np₁)
  go (inr _) (inr _) (inl p) (inl q) _ = mem-inj m n (p ∙ sym q)
  go (inr _) (inr nq₀) (inl _) (inr _) eq = Empty.rec (n₀≢other n eq nq₀)
  go (inr np₀) (inr _) (inr _) (inl _) eq = Empty.rec (other≢n₀ m eq np₀)
  go (inr _) (inr _) (inr _) (inr _) eq = eq

-- THE SECOND PAIRING.  Transpose the first coordinate, then pair by
-- the delivered base.  An injection, because both factors are.
twisted : sq ω
twisted = (λ p → squareω .fst (swap (fst p) , snd p)) , inj
  where
  inj : (p q : ⟪ ω ⟫ × ⟪ ω ⟫)
      → squareω .fst (swap (fst p) , snd p) ≡ squareω .fst (swap (fst q) , snd q)
      → p ≡ q
  inj (a , b) (c , d) eq = ΣPathP (swap-inj a c (cong fst pq) , cong snd pq)
    where
    pq : (swap a , b) ≡ (swap c , d)
    pq = squareω .snd (swap a , b) (swap c , d) eq

-- THE REFUTATION.  Any path between the two pairings forces the two
-- numerals to coincide.
twisted≢square : (twisted ≡ squareω) → Empty.⊥
twisted≢square e = znots (sym (#-inj′ {suc zero} {zero} mempath))
  where
  step : squareω .fst (swap n₀ , n₀) ≡ squareω .fst (n₁ , n₀)
  step = cong (λ x → squareω .fst (x , n₀)) (swap-at₀ n₀ mem₀)

  val : twisted .fst (n₀ , n₀) ≡ squareω .fst (n₀ , n₀)
  val = cong (λ g → g (n₀ , n₀)) (cong fst e)

  eq : squareω .fst (n₁ , n₀) ≡ squareω .fst (n₀ , n₀)
  eq = sym step ∙ val

  pq : (n₁ , n₀) ≡ (n₀ , n₀)
  pq = squareω .snd (n₁ , n₀) (n₀ , n₀) eq

  mempath : # suc zero ≡ # zero
  mempath = sym mem₁ ∙ cong ⟪ ω ⟫↪ (cong fst pq) ∙ mem₀

-- THE COUNTERMODEL.  `sq ω` is not a proposition: two elements, no
-- path between them.  Route 1 of the brief is closed at every ordinal
-- that holds both numerals, which is every ordinal the descent visits.
sq-not-prop : ((g h : sq ω) → g ≡ h) → Empty.⊥
sq-not-prop all = twisted≢square (all twisted squareω)
