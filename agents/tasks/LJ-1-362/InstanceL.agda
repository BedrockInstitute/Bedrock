{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.362] instantiation probe at L.  The structure hypothesis at
-- S_ʟ is NOT definitional: the restricted structure's ≈ˢ compares
-- underlying V-sets (fst a ≡ fst b), so the bridge goes through
-- Σ≡Prop in both directions.  MEASURES the glue price and the check
-- cost at the second delivered model (P-m's instantiation class).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )

module LJ-1-362.InstanceL {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Model {ℓ} lem using ( L⊨ZF )
import FOL.Bernstein

private
  Sʟ = ZFStructure.S 𝒮ʟ

  ≈ˢʟ-is-path : (x y : Sʟ)
    → (ZFStructure._≈ˢ_ 𝒮ʟ x y)
    ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮ʟ x y)
  ≈ˢʟ-is-path x y = ⇔toPath
    (λ h → Σ≡Prop (λ z → snd (isL z)) h)
    (λ h → cong fst h)

module B = FOL.Bernstein lem 𝒮ʟ ≈ˢʟ-is-path

CSBʟ : Type (ℓ-suc ℓ)
CSBʟ = B.CSB L⊨ZF

module T = B.Tarski L⊨ZF
