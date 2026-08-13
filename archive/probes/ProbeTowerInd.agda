{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeTowerInd {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber; ↪-inj; member )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; Lset-mono; Lset-in; Lset-out; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; numeral-ord )
open import L.Ordinal.SquareLaw {ℓ} lem
  using ( module InitialCore; module CoreAtω; module FiniteBase; Init; sq )
open import L.Ordinal.Pairing {ℓ} lem using ( col→τ; col→τ-inj; τ )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- D-10 checks.

Initω-false : Init ω → Empty.⊥
Initω-false i = ∈-irrefl ω (i .snd .fst)

-- The negative control: ω ⊆ Lset ω, at the index level.
-- Each member of ω is a numeral # n; ord∈Lset-suc places it at the stage
-- after itself, and Lset-mono lifts it into Lset ω because sucV (# n) ∈ ω.

numeral∈Lsetω : (m : ⟪ ω ⟫) → ⟨ ⟪ ω ⟫↪ m ∈ˢ Lset ω ⟩
numeral∈Lsetω m =
  PT.rec (snd (⟪ ω ⟫↪ m ∈ˢ Lset ω)) go
    (FiniteBase.ω-mem→numeral (⟪ ω ⟫↪ m) (member ω m))
  where
  go : Σ[ n ∈ ℕ ] (⟪ ω ⟫↪ m ≡ # n) → ⟨ ⟪ ω ⟫↪ m ∈ˢ Lset ω ⟩
  go (n , p) = Lset-mono {α = ω} {β = sucV (⟪ ω ⟫↪ m)} s∈ω {x = ⟪ ω ⟫↪ m}
    (subst (λ w → ⟨ w ∈ˢ Lset (sucV w) ⟩) (sym p)
      (ord∈Lset-suc (# n) (numeral-ord n)))
    where
    s∈ω : ⟨ sucV (⟪ ω ⟫↪ m) ∈ˢ ω ⟩
    s∈ω = subst (λ w → ⟨ sucV w ∈ˢ ω ⟩) (sym p) (#∈ω (suc n))

ω↪Lsetω : ⟪ ω ⟫ → ⟪ Lset ω ⟫
ω↪Lsetω m = fiber (Lset ω) (numeral∈Lsetω m) .fst

ω↪Lsetω-inj : (m n : ⟪ ω ⟫) → ω↪Lsetω m ≡ ω↪Lsetω n → m ≡ n
ω↪Lsetω-inj m n e = ↪-inj {a = ω}
  (sym (fiber (Lset ω) (numeral∈Lsetω m) .snd)
    ∙ cong (⟪ Lset ω ⟫↪) e
    ∙ fiber (Lset ω) (numeral∈Lsetω n) .snd)

-- The honest square law at ω, re-derived: T47 exports the bound only at
-- Init α with ω ∈ α, and Init ω is uninhabited (Initω-false), so the
-- InitialCore instantiation with CoreAtω's pieces is the delivered shape.

noinj²ω : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩ → ⟨ ω ∈ˢ β ⟩
        → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
        → ((m n : ⟪ ω ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
noinj²ω β oβ β∈ω ω∈β f finj = Empty.rec (CoreAtω.ω∉β β β∈ω ω∈β)

module Bω = InitialCore ω ω-ord CoreAtω.ω-limit noinj²ω CoreAtω.finite-excl-ω

-- The pairing is built at an ABSTRACT ordinal and sealed opaque: at the
-- concrete ω, the transparent col→τ (a union fiber) normalizes in every
-- unification of the injectivity proof (R-35/R-38 class); the abstract
-- definitions check once at a variable ordinal, and the application is
-- cheap because the proof bodies are sealed.

module PairAt (α : S) (oα : IsOrd α)
  (α-limit : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
  (noinj² : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
  (finite-excl : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥) where

  module C = InitialCore α oα α-limit noinj² finite-excl

  opaque
    bound₀ : ⟪ τ α oα ⟫ → ⟪ α ⟫
    bound₀ = C.bound

    bound₀-inj : {m n : ⟪ τ α oα ⟫} → bound₀ m ≡ bound₀ n → m ≡ n
    bound₀-inj = C.bound-inj

    pair : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
    pair a b = bound₀ (col→τ α oα (a , b))

    -- pair-inj (the injectivity of the re-derived pairing) is a WALL:
    -- applying bound₀-inj to the composed equality normalizes col→τ's
    -- union fiber under the opaque bound's spine; >3.5 min at both the
    -- concrete and the abstract shape, alias-seal included (R-35/R-38
    -- class; the same shape as SquareLaw.Initial.pair-inj, whose cost is
    -- hidden in the delivered interface). Recorded; not forced.

module Pω = PairAt ω ω-ord CoreAtω.ω-limit noinj²ω CoreAtω.finite-excl-ω

-- The negative control (ω↪Lsetω, ω↪Lsetω-inj) is the GREEN arm.
-- The successor and limit arms are RED at the D-10 premise level; see
-- _build/l3.32-t59-report.md section 1.
