{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.254] probe: build step 6, the supply for the 28 fields.
--
-- The join that stopped [LJ-1.199] is measured open by [LJ-1.252]:
-- `ω∈λ-from-α` typechecks.  This probe builds the supply at the
-- concrete site (`K = Lset lam`, carrier `LsetS gam`), field by
-- field.  ONE agda process, GHCRTS="-A64m -I0 -M8g", cap never
-- raised.  Never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-254.ProbeLJ1254 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ∃̇∈; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-mono; Lset→isL; Lset-layer
        ; layer-trans; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pair∈Lset-suc; sgl∈Lset-suc; LsetS )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord; numeral-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import L.Coding.Bound {ℓ} lem using ( module Bound; Lset-out′ )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )
open import L.Coding.Sound {ℓ} lem using ( module NumeralFromGeneric )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; module Generic )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; pair-singleton )
open import Cubical.Data.Sigma using ( _,_; Σ≡Prop )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⋃_; union-ax; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; #_; ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; extensionality; _⊆_; _∈ₛ_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- THE SUPPLY AT THE CONCRETE SITE.  K = Lset lam, carrier B₀ =
-- LsetS gam ordγ.  The new hypothesis is ω∈γ : ⟨ ω ∈ sucV gam ⟩,
-- [LJ-1.252]'s cheaper form, which matches envSetNumeral∈'s ω ∈ σ at
-- σ = sucV gam and avoids the two-ordinal merge below the limit.
-- =====================================================================

module Supply (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : S) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  module B = Bound lam ordλ succλ ∅∈λ

  σ : S
  σ = sucV gam

  oσ : IsOrd σ
  oσ = suc-ord ordγ

  σ∈λ : ⟨ σ ∈ lam ⟩
  σ∈λ = succλ gam γ∈λ

  B₀ : CS.S
  B₀ = LsetS gam ordγ

  -- The carrier lies one stage above its own index.
  B₀∈σ : ⟨ fst B₀ ∈ Lset σ ⟩
  B₀∈σ = subst (λ w → ⟨ Lset gam ∈ w ⟩) (sym (Lset-suc gam))
    (𝒟ₒ-intro (Lset gam) (Lset gam) ∣ ⊤̇ , DefA.defSet⊤≡A ∣₁)
    where
    module DefA = DefOf (Lset gam)

  -- ===================================================================
  -- L9, envSetK, THE JOIN.  [LJ-1.199] stopped here at ZERO lines;
  -- [LJ-1.252] reopened it.  The chain is
  --   ar ≡ # n  ⇒  ar ≡ nn n
  --   ⇒  Generic.envSetGen B₀ ar ≡ Generic.envSetGen B₀ (nn n)
  --   ≡  envSet B₀ n                        (NumeralFromGeneric.derived)
  --   ∈  Lset (sucIter 4 σ)                 (envSetNumeral∈)
  --   ⊆  Lset lam                           (succλ climb)
  -- ===================================================================

  genEq : (ar : CS.S) (n : ℕ) → fst ar ≡ # n
        → fst (Generic.envSetGen B₀ ar) ≡ fst (envSet B₀ n)
  genEq ar n arNum =
    cong (λ ar' → fst (Generic.envSetGen B₀ ar'))
      (Σ≡Prop (λ x → (isL x) .snd) arNum)
    ∙ sym (NumeralFromGeneric.derived B₀ n)

  envSetK : (ar : CS.S) (n : ℕ) → fst ar ≡ # n
          → ⟨ fst ar ∈ Lset lam ⟩
          → ⟨ fst (Generic.envSetGen B₀ ar) ∈ Lset lam ⟩
  envSetK ar n arNum ar∈λ =
    Lset-mono {α = lam} {β = sucIter 4 σ} (B.suc^∈λ 4 σ σ∈λ)
      (subst (λ w → ⟨ w ∈ Lset (sucIter 4 σ) ⟩) (sym (genEq ar n arNum))
        (envSetNumeral∈ σ oσ ω∈γ B₀ n B₀∈σ))

  -- ===================================================================
  -- sucK, THE NAMED WALL.  Lset lam closed under V-successor, the
  -- union closure plus a climb.  sucV a = ⋃ ⁅ a , ⁅ a ⁆s ⁆, so one
  -- union step above a pairing step above a singleton step, then
  -- succλ four times.
  -- ===================================================================

  union∈Lset-suc : (σ x : S) → ⟨ x ∈ Lset σ ⟩ → ⟨ ⋃ x ∈ Lset (sucV σ) ⟩
  union∈Lset-suc σ x x∈ =
    subst (λ w → ⟨ ⋃ x ∈ w ⟩) (sym (Lset-suc σ)) union∈𝒟ₒ
    where
    module DefA = DefOf (Lset σ)
    Atrans = layer-trans (Lset-layer σ)
    mₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
    qₓ : ⟪ Lset σ ⟫↪ mₓ ≡ x
    qₓ = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd

    φ : Formula ⟪ Lset σ ⟫ 1
    φ = ∃̇∈ (con mₓ) (var (suc zero) ∈̇ var zero)

    defSet≡ : DefA.defSet φ ≡ ⋃ x
    defSet≡ = extensionality (DefA.defSet φ) (⋃ x) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet φ ⊆ ⋃ x ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⋃ x))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ ⋃ x ⟩) q
            (PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ₛ ⋃ x))
              (λ { (v , (fstv∈mₓ , m∈fstv)) →
                union-ax x (⟪ Lset σ ⟫↪ m) .snd
                  ∣ fst v
                  , ( ∈∈ₛ {a = fst v} {b = x} .fst
                        (subst (λ w → ⟨ fst v ∈ w ⟩) qₓ fstv∈mₓ)
                    , ∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = fst v} .fst m∈fstv ) ∣₁ })
              (subst ⟨_⟩ (DefA.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ)
      sub₂ : ⟨ ⋃ x ⊆ DefA.defSet φ ⟩
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet φ))
        (λ { (v , (v∈ₛx , y∈ₛv)) → member v v∈ₛx y∈ₛv })
        (union-ax x y .fst y∈ₛ)
        where
        member : (v : S) → ⟨ v ∈ₛ x ⟩ → ⟨ y ∈ₛ v ⟩
               → ⟨ y ∈ₛ DefA.defSet φ ⟩
        member v v∈ₛx y∈ₛv =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet φ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = DefA.defSet φ} .fst
              (subst ⟨_⟩ (sym (DefA.defSet-mem φ m')) sat))
          where
          v∈x = ∈∈ₛ {a = v} {b = x} .snd v∈ₛx
          y∈v = ∈∈ₛ {a = y} {b = v} .snd y∈ₛv
          v∈A = Atrans {x = x} {y = v} v∈x x∈
          y∈A = Atrans {x = v} {y = y} y∈v v∈A
          fib = ∈-asFiber {a = y} {b = Lset σ} y∈A
          m' = fib .fst
          q' = fib .snd
          sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ φ ⟩
          sat = ∣ (v , v∈A)
                , ( subst (λ w → ⟨ v ∈ w ⟩) (sym qₓ) v∈x
                  , subst (λ w → ⟨ w ∈ v ⟩) (sym q') y∈v ) ∣₁

    union∈𝒟ₒ : ⟨ ⋃ x ∈ 𝒟ₒ (Lset σ) ⟩
    union∈𝒟ₒ = 𝒟ₒ-intro (Lset σ) (⋃ x) ∣ φ , defSet≡ ∣₁

  sucK : (a : S) → ⟨ a ∈ Lset lam ⟩ → ⟨ sucV a ∈ Lset lam ⟩
  sucK a a∈ = PT.rec (snd (sucV a ∈ Lset lam)) step (Lset-out′ lam a a∈)
    where
    step : Σ[ δ ∈ S ] (⟨ δ ∈ lam ⟩ × ⟨ a ∈ Lset (sucV δ) ⟩)
         → ⟨ sucV a ∈ Lset lam ⟩
    step (δ , δ∈ , a∈δ₁) =
      Lset-mono {α = lam} {β = sucIter 4 δ}
        (B.suc^∈λ 4 δ δ∈)
        sucV∈
      where
      δ₁ = sucV δ
      δ₂ = sucV (sucV δ)
      δ₃ = sucV (sucV (sucV δ))
      a∈δ₂ : ⟨ a ∈ Lset δ₂ ⟩
      a∈δ₂ = Lset-mono {α = δ₂} {β = δ₁} (self∈sucV δ₁) a∈δ₁
      sgl∈δ₂ : ⟨ ⁅ a ⁆s ∈ Lset δ₂ ⟩
      sgl∈δ₂ = sgl∈Lset-suc δ₁ a a∈δ₁
      pair∈δ₃ : ⟨ ⁅ a , ⁅ a ⁆s ⁆ ∈ Lset δ₃ ⟩
      pair∈δ₃ = pair∈Lset-suc δ₂ a ⁅ a ⁆s a∈δ₂ sgl∈δ₂
      sucV∈ : ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
      sucV∈ = union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃
