{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.677] PROBE.  Describes at a member that is not a stage.
-- It runs in agents/tasks/LJ-1-677/ and lands nothing in src/.
--
-- THE OBLIGATION the brief names is describes-nonstage: Describes σ y
-- at y = ⁅ sucV ∅ ⁆s (the first non-stage member of L) and
-- σ = sucV³ ∅ (the stage that first holds it).  𝒟ₒ y is the pair
-- {∅, y}, a proper subset of that stage.  The formula is pair∈𝒟ₒ's
-- (src/L/Axioms/Basic.lagda.md:547-549), not the tautology.
--
-- WHAT IS SETTLED.
--   1. Describes, copied from
--      agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82.
--   2. dee-singleton (W2): 𝒟ₒ of a singleton is {∅, the singleton}.
--      Needs LEM to classify an arbitrary member of 𝒟ₒ.
--   3. describes-sgl (W2): Describes σ (⁅ a ⁆s) from ∅ ∈ Lset σ and
--      ⁅ a ⁆s ∈ Lset σ, spending pair∈𝒟ₒ, not rewriting it.
--   4. describes-nonstage: instantiate at a = sucV ∅, σ = sucV³ ∅.
--
-- WHAT IS NOT SETTLED.
--   Describes at an arbitrary non-stage member.  This file pays one
--   singleton.  PowIter still owes a supplier at a member whose
--   definable powerset is not a pairing of ∅ with the member.
--   A Formula Code 1 for 𝒟ₒ stays a second debt.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-677.Probe677 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇; ⊥̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV; ∈sucV-inl )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; 𝒟ₒ∋⊆; Lset-mono )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; ∅∈𝒟ₒ; pair∈𝒟ₒ; sgl∈Lset-suc )

open import Cubical.Data.Sigma using ( Σ-syntax; _,_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality; ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax
        ; SingletonPackage; SetPackage  -- lint-agda: keep (SetPackage via record projection)
        ; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- D-10.  THE FIRST NON-STAGE.
--
-- Describes is [LJ-1.169]'s type.  The tautology carves a whole stage
-- ([LJ-1.674]).  A singleton's definable powerset is the pair {∅, the
-- singleton}, and pair∈𝒟ₒ carves that pair from any stage that holds
-- both members.
-- =====================================================================

Describes : S → S → Type (ℓ-suc ℓ)
Describes σ y =
  ∥ Σ[ ψ ∈ Formula ⟪ Lset σ ⟫ 1 ] (DefOf.defSet (Lset σ) ψ ≡ 𝒟ₒ y) ∥₁

∈sgl : {a z : S} → ⟨ z ∈ˢ ⁅ a ⁆s ⟩ → z ≡ a
∈sgl {a} {z} h =
  SetPackage.classification (SingletonPackage a) z .fst
    (∈∈ₛ {a = z} {b = ⁅ a ⁆s} .fst h)

sgl∈ : {a z : S} → z ≡ a → ⟨ z ∈ˢ ⁅ a ⁆s ⟩
sgl∈ {a} {z} e = ∈∈ₛ {a = z} {b = ⁅ a ⁆s} .snd
  (SetPackage.classification (SingletonPackage a) z .snd e)

-- W2: falsehood carves ∅ from an arbitrary carrier.  One fact, then
-- instantiate.  Copied from ∅∈𝒟ₒ's local identity
-- (src/L/Axioms/Basic.lagda.md:494-502) at a generic A.
empty∈dee : (A : S) → ⟨ ∅ ∈ˢ 𝒟ₒ A ⟩
empty∈dee A = 𝒟ₒ-intro A ∅ ∣ ⊥̇ , defSet⊥≡∅ ∣₁
  where
  module DefA = DefOf A
  defSet⊥≡∅ : DefA.defSet ⊥̇ ≡ ∅
  defSet⊥≡∅ = extensionality (DefA.defSet ⊥̇) ∅ (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet ⊥̇ ⊆ ∅ ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ∅))
      (λ { ((m , h) , q) → Empty.rec* h })
      (∈∈ₛ {a = y} {b = DefA.defSet ⊥̇} .snd y∈ₛ)
    sub₂ : ⟨ ∅ ⊆ DefA.defSet ⊥̇ ⟩
    sub₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

-- W2: the tautology puts every carrier in its own definable powerset.
-- Copied from agents/tasks/LJ-1-668/Probe668.agda:79-80.
A∈𝒟ₒ : (A : S) → ⟨ A ∈ˢ 𝒟ₒ A ⟩
A∈𝒟ₒ A = 𝒟ₒ-intro A A ∣ ⊤̇ , DefOf.defSet⊤≡A A ∣₁

-- W2: 𝒟ₒ of a singleton is {∅, the singleton}.  LEM decides whether
-- the singleton's element belongs to an arbitrary member of 𝒟ₒ.
dee-singleton : (a : S) → 𝒟ₒ (⁅ a ⁆s) ≡ ⁅ ∅ , ⁅ a ⁆s ⁆
dee-singleton a = extensionality (𝒟ₒ (⁅ a ⁆s)) ⁅ ∅ , ⁅ a ⁆s ⁆ (sub₁ , sub₂)
  where
  sub₁ : ⟨ 𝒟ₒ (⁅ a ⁆s) ⊆ ⁅ ∅ , ⁅ a ⁆s ⁆ ⟩
  sub₁ x x∈ₛ = ∈∈ₛ {a = x} {b = ⁅ ∅ , ⁅ a ⁆s ⁆} .fst (from (lem (a ∈ˢ x)))
    where
    x∈dee : ⟨ x ∈ˢ 𝒟ₒ (⁅ a ⁆s) ⟩
    x∈dee = ∈∈ₛ {a = x} {b = 𝒟ₒ (⁅ a ⁆s)} .snd x∈ₛ
    x⊆sgl : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ ⁅ a ⁆s ⟩
    x⊆sgl = 𝒟ₒ∋⊆ (⁅ a ⁆s) x x∈dee
    from : ⟨ a ∈ˢ x ⟩ ⊎ (⟨ a ∈ˢ x ⟩ → Empty.⊥) → ⟨ x ∈ˢ ⁅ ∅ , ⁅ a ⁆s ⁆ ⟩
    from (inl a∈x) = subst (λ w → ⟨ w ∈ˢ ⁅ ∅ , ⁅ a ⁆s ⁆ ⟩) (sym x≡sgl)
      (∈∈ₛ {a = ⁅ a ⁆s} {b = ⁅ ∅ , ⁅ a ⁆s ⁆} .snd
        (pairing-ax ∅ (⁅ a ⁆s) (⁅ a ⁆s) .snd ∣ inr refl ∣₁))
      where
      x≡sgl : x ≡ ⁅ a ⁆s
      x≡sgl = extensionality x (⁅ a ⁆s) (xs₁ , xs₂)
        where
        xs₁ : ⟨ x ⊆ ⁅ a ⁆s ⟩
        xs₁ y y∈ₛ = ∈∈ₛ {a = y} {b = ⁅ a ⁆s} .fst
          (x⊆sgl y (∈∈ₛ {a = y} {b = x} .snd y∈ₛ))
        xs₂ : ⟨ ⁅ a ⁆s ⊆ x ⟩
        xs₂ y y∈ₛ = subst (λ w → ⟨ w ∈ₛ x ⟩) (sym (∈sgl (∈∈ₛ {a = y} {b = ⁅ a ⁆s} .snd y∈ₛ)))
          (∈∈ₛ {a = a} {b = x} .fst a∈x)
    from (inr a∉x) = subst (λ w → ⟨ w ∈ˢ ⁅ ∅ , ⁅ a ⁆s ⁆ ⟩) (sym x≡∅)
      (∈∈ₛ {a = ∅} {b = ⁅ ∅ , ⁅ a ⁆s ⁆} .snd
        (pairing-ax ∅ (⁅ a ⁆s) ∅ .snd ∣ inl refl ∣₁))
      where
      x≡∅ : x ≡ ∅
      x≡∅ = extensionality x ∅ (xe₁ , xe₂)
        where
        xe₁ : ⟨ x ⊆ ∅ ⟩
        xe₁ y y∈ₛ = Empty.rec (a∉x a∈x)
          where
          y∈x : ⟨ y ∈ˢ x ⟩
          y∈x = ∈∈ₛ {a = y} {b = x} .snd y∈ₛ
          a∈x : ⟨ a ∈ˢ x ⟩
          a∈x = subst (λ w → ⟨ w ∈ˢ x ⟩) (∈sgl (x⊆sgl y y∈x)) y∈x
        xe₂ : ⟨ ∅ ⊆ x ⟩
        xe₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

  sub₂ : ⟨ ⁅ ∅ , ⁅ a ⁆s ⁆ ⊆ 𝒟ₒ (⁅ a ⁆s) ⟩
  sub₂ x x∈ₛ = PT.rec (snd (x ∈ₛ 𝒟ₒ (⁅ a ⁆s)))
    (λ { (inl p) → subst (λ w → ⟨ w ∈ₛ 𝒟ₒ (⁅ a ⁆s) ⟩) (sym p)
                     (∈∈ₛ {a = ∅} {b = 𝒟ₒ (⁅ a ⁆s)} .fst (empty∈dee (⁅ a ⁆s)))
       ; (inr p) → subst (λ w → ⟨ w ∈ₛ 𝒟ₒ (⁅ a ⁆s) ⟩) (sym p)
                     (∈∈ₛ {a = ⁅ a ⁆s} {b = 𝒟ₒ (⁅ a ⁆s)} .fst (A∈𝒟ₒ (⁅ a ⁆s))) })
    (pairing-ax ∅ (⁅ a ⁆s) x .fst x∈ₛ)

-- W2: Describes at a singleton, from a stage that already holds ∅ and
-- the singleton.  pair∈𝒟ₒ supplies the formula; dee-singleton rewrites
-- the carved pair to 𝒟ₒ.
describes-sgl : (σ a : S)
              → ⟨ ∅ ∈ˢ Lset σ ⟩ → ⟨ ⁅ a ⁆s ∈ˢ Lset σ ⟩
              → Describes σ (⁅ a ⁆s)
describes-sgl σ a ∅∈ y∈ =
  PT.map (λ { (ψ , q) → ψ , q ∙ sym (dee-singleton a) })
    (𝒟ₒ-inv (Lset σ) ⁅ ∅ , ⁅ a ⁆s ⁆ (pair∈𝒟ₒ σ ∅ (⁅ a ⁆s) ∅∈ y∈))

-- The concrete pair.  sucV ∅ is {∅}; its singleton is {{∅}}.
sucV∅≡sgl : sucV ∅ ≡ ⁅ ∅ ⁆s
sucV∅≡sgl = extensionality (sucV ∅) (⁅ ∅ ⁆s) (s1 , s2)
  where
  s1 : ⟨ sucV ∅ ⊆ ⁅ ∅ ⁆s ⟩
  s1 x x∈ₛ = ∈∈ₛ {a = x} {b = ⁅ ∅ ⁆s} .fst
    (∈sucV-elim {A = ∅} {x = x} (snd (x ∈ˢ ⁅ ∅ ⁆s))
      (∈∈ₛ {a = x} {b = sucV ∅} .snd x∈ₛ)
      (λ x∈∅ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅)))
      (λ x≡∅ → sgl∈ x≡∅))
  s2 : ⟨ ⁅ ∅ ⁆s ⊆ sucV ∅ ⟩
  s2 x x∈ₛ = ∈∈ₛ {a = x} {b = sucV ∅} .fst
    (subst (λ w → ⟨ w ∈ˢ sucV ∅ ⟩)
      (sym (∈sgl (∈∈ₛ {a = x} {b = ⁅ ∅ ⁆s} .snd x∈ₛ)))
      (self∈sucV ∅))

∅∈Lset1 : ⟨ ∅ ∈ˢ Lset (sucV ∅) ⟩
∅∈Lset1 = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Lset-suc ∅)) (∅∈𝒟ₒ ∅)

σ₃ : S
σ₃ = sucV (sucV (sucV ∅))

y₀ : S
y₀ = ⁅ sucV ∅ ⁆s

∅∈σ₃ : ⟨ ∅ ∈ˢ Lset σ₃ ⟩
∅∈σ₃ = Lset-mono {α = σ₃} {β = sucV ∅}
  (∈sucV-inl {A = sucV (sucV ∅)} {x = sucV ∅} (self∈sucV (sucV ∅)))
  ∅∈Lset1

y₀∈σ₃ : ⟨ y₀ ∈ˢ Lset σ₃ ⟩
y₀∈σ₃ = subst (λ w → ⟨ ⁅ w ⁆s ∈ˢ Lset σ₃ ⟩) (sym sucV∅≡sgl)
  (sgl∈Lset-suc (sucV (sucV ∅)) (⁅ ∅ ⁆s)
    (sgl∈Lset-suc (sucV ∅) ∅ ∅∈Lset1))

-- THE OBLIGATION.  y₀ is {{∅}}, not a stage: stages are transitive
-- and {{∅}} is not.  𝒟ₒ y₀ is {∅, y₀}, a proper subset of L₃.
describes-nonstage : Describes σ₃ y₀
describes-nonstage = describes-sgl σ₃ (sucV ∅) ∅∈σ₃ y₀∈σ₃
