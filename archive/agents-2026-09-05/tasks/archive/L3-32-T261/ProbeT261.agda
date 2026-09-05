{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

-- [L3.32-T261] The condensation limit case, L-native.
--
-- Probe per [T260] section 5. FIRST pass: build `Condenses` from the face
-- hypotheses with the wing's own suppliers. No L.Rud.* import and no
-- S-tower name. The witness beta is the separated set of ordinals of M.
-- The theorem closes L-native or a wall is typed below it.

module ProbeT261 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Smallness {ℓ} using ( separateFromSmall; module Δ₀Small )
open import L.Constructible {ℓ} using
  ( isTransV; IsOrd; Lset; 𝒟ₒ; Lset-out; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Condensation {ℓ} lem using ( module AtCarrier )

open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemP = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemP.At (⊥* {ℓ}) Empty.rec* using () renaming ( _⊨_ to _⊨ₚ_ )

module D0 = Δ₀Small {K = ⊥* {ℓ}} Empty.rec*

module _ (M : S) (Mtr : isTransV M) where

  module FC = AtCarrier M Mtr

  open FC using
    ( Sᴹ; Believes; CrossOut; HasLevels; Covered; SucClosed; Condenses
    ; isOrdAt; isOrdAtΔ₀; isOrdAt-out; isOrdAt-in; f0 )

  -- beta = the set of ordinals in M, separated by the Delta-0 ordinal
  -- predicate. This is the L-native supremum the limit case needs.
  β-sep : Σ[ s ∈ S ]
            (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ M) ⊓ ((y ∷ []) ⊨ₚ isOrdAt f0)))
  β-sep = separateFromSmall M (λ y → (y ∷ []) ⊨ₚ isOrdAt f0)
    (λ y → D0.Δ₀-small (isOrdAtΔ₀ f0) (y ∷ []))

  β : S
  β = β-sep .fst

  β-spec : (y : S) → (y ∈ˢ β) ≡ ((y ∈ˢ M) ⊓ ((y ∷ []) ⊨ₚ isOrdAt f0))
  β-spec = β-sep .snd

  β∈M : (δ : S) → ⟨ δ ∈ˢ β ⟩ → ⟨ δ ∈ˢ M ⟩
  β∈M δ δ∈β = subst ⟨_⟩ (β-spec δ) δ∈β .fst

  β-ord : (δ : S) → ⟨ δ ∈ˢ β ⟩ → IsOrd δ
  β-ord δ δ∈β = isOrdAt-out f0 (δ ∷ []) (subst ⟨_⟩ (β-spec δ) δ∈β .snd)

  ord∈β : (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ → ⟨ δ ∈ˢ β ⟩
  ord∈β δ δ∈M oδ = subst ⟨_⟩ (sym (β-spec δ)) (δ∈M , isOrdAt-in f0 (δ ∷ []) oδ)

  β-isOrd : IsOrd β
  β-isOrd = β-trans , β-mem
    where
    β-trans : isTransV β
    β-trans {x = x} {y = z} z∈x x∈β =
      subst ⟨_⟩ (sym (β-spec z))
        ( Mtr {x = x} {y = z} z∈x (β∈M x x∈β)
        , isOrdAt-in f0 (z ∷ [])
            (mem-ord {A = x} (β-ord x x∈β) z z∈x) )
    β-mem : (x : S) → ⟨ x ∈ˢ β ⟩ → isTransV x
    β-mem x x∈β = β-ord x x∈β .fst

  -- The limit case: the identification M = Lset beta from the face.
  -- No bridge row and no S-tower fact enters.
  limit-case : (φ : Formula Sᴹ 2) (co : CrossOut φ) (hl : HasLevels φ)
             → (cv : Covered φ) (sc : SucClosed) → Condenses
  limit-case φ co hl cv sc = β , β-isOrd , ext
    where
    module A = FC.Assembly φ co

    M⊆Lβ : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ x ∈ˢ Lset β ⟩
    M⊆Lβ x x∈M = PT.rec (snd (x ∈ˢ Lset β)) go (cv (x , x∈M))
      where
      go : Σ[ b ∈ Sᴹ ] Σ[ v ∈ Sᴹ ]
             (IsOrd (fst b) × Believes φ v b × ⟨ x ∈ˢ fst v ⟩)
         → ⟨ x ∈ˢ Lset β ⟩
      go (b , v , ob , hv , x∈v) =
        Lset-mono {α = β} {β = fst b} (ord∈β (fst b) (snd b) ob)
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (co v b ob hv) x∈v)

    Lβ⊆M : (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ M ⟩
    Lβ⊆M x x∈Lβ = PT.rec (snd (x ∈ˢ M)) go (Lset-out β x x∈Lβ)
      where
      go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ x ∈ˢ M ⟩
      go (δ , δ∈β , x∈𝒟ₒδ) =
        Mtr {x = Lset (sucV δ)} {y = x}
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟ₒδ)
          (A.level-in hl (sucV δ) (sc (δ , β∈M δ δ∈β) (β-ord δ δ∈β))
            (suc-ord (β-ord δ δ∈β)))

    ext : M ≡ Lset β
    ext = extensionality M (Lset β) (sub , sup)
      where
      sub : (x : S) → ⟨ x ∈ₛ M ⟩ → ⟨ x ∈ₛ Lset β ⟩
      sub x x∈ₛM = ∈∈ₛ {a = x} {b = Lset β} .fst
        (M⊆Lβ x (∈∈ₛ {a = x} {b = M} .snd x∈ₛM))
      sup : (x : S) → ⟨ x ∈ₛ Lset β ⟩ → ⟨ x ∈ₛ M ⟩
      sup x x∈ₛLβ = ∈∈ₛ {a = x} {b = M} .fst
        (Lβ⊆M x (∈∈ₛ {a = x} {b = Lset β} .snd x∈ₛLβ))
