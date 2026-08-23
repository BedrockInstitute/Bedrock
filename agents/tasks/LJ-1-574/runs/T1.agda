{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.574] T1.  THE UNIFORM STAGE.  Slice, run alone.
--
-- W3 said the reflection step APPLIES.  T1 spends it: the pointwise
-- code of [LJ-1.557] becomes a code IN ONE STAGE, uniformly over the
-- members of δ.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-574.runs.T1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer
        ; layer-trans; isPropIsOrd )
open import L.Ordinal {ℓ} using ( bound2 )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL; SuccCardL )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in; injAt-out )
open import L.Reflect {ℓ} lem
  using ( Below; Wit; Sat; SatEx; ClosedFor; LsetEnv; pickStage
        ; module Ladder; module Single )

open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.FinData using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

import LJ-1-557.Probe557 {ℓ} lem as P557


-- SECTION 1.  THE FORMULA (W3, restated).

valFo : Formula S 3
valFo = ∀̇ (∀̇ ( appAt (fsuc (fsuc fzero)) (fsuc fzero) fzero
             ⇒̇ (var fzero ∈̇ var (fsuc (fsuc (fsuc (fsuc fzero))))) ))

codeFo : Formula S 3
codeFo = svAt fzero ∧̇ (domAt fzero (fsuc fzero) ∧̇ (injAt fzero ∧̇ valFo))

valFo-adequate : (F a c : S)
  → ⟨ (F ∷ a ∷ c ∷ []) ⊨ valFo ⟩
  ≡ ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst c ⟩)
valFo-adequate F a c i =
  (x y : S)
  → ⟨ appAt-adequate (fsuc (fsuc fzero)) (fsuc fzero) fzero
        (y ∷ x ∷ F ∷ a ∷ c ∷ []) i ⟩
  → ⟨ fst y ∈ fst c ⟩

code→sat : (F a c : S) → InjCode F a c → ⟨ (F ∷ a ∷ c ∷ []) ⊨ codeFo ⟩
code→sat F a c (sv , dm , ij , vl) =
    svAt-in fzero (F ∷ a ∷ c ∷ []) (svAt-out fzero (F ∷ a ∷ []) sv)
  , ( domAt-intro fzero (fsuc fzero) (F ∷ a ∷ c ∷ []) dom
    , ( injAt-in fzero (F ∷ a ∷ c ∷ []) (injAt-out fzero (F ∷ a ∷ []) ij)
      , transport (sym (valFo-adequate F a c)) vl ) )
  where
  dom : (x : S)
      → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩)
      × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩)
  dom x =
      PT.rec (snd (fst x ∈ fst a))
        (λ { (y , p) → domAt-out fzero (fsuc fzero) (F ∷ a ∷ []) dm x y p })
    , domAt-in fzero (fsuc fzero) (F ∷ a ∷ []) dm x

sat→code : (F a c : S) → ⟨ (F ∷ a ∷ c ∷ []) ⊨ codeFo ⟩ → InjCode F a c
sat→code F a c (sv , (dm , (ij , vl))) =
    svAt-in fzero (F ∷ a ∷ []) (svAt-out fzero (F ∷ a ∷ c ∷ []) sv)
  , ( domAt-intro fzero (fsuc fzero) (F ∷ a ∷ []) dom
    , ( injAt-in fzero (F ∷ a ∷ []) (injAt-out fzero (F ∷ a ∷ c ∷ []) ij)
      , transport (valFo-adequate F a c) vl ) )
  where
  dom : (x : S)
      → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩)
      × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩)
  dom x =
      PT.rec (snd (fst x ∈ fst a))
        (λ { (y , p) → domAt-out fzero (fsuc fzero) (F ∷ a ∷ c ∷ []) dm x y p })
    , domAt-in fzero (fsuc fzero) (F ∷ a ∷ c ∷ []) dm x


-- SECTION 2.  THE LADDER, STARTED WHERE THE CALLER SAYS.
--
--   `L.Reflect.Single` starts its ladder at ∅ (src/L/Reflect.lagda.md:
--   479), so its `βω` is fixed by ψ alone and cannot hold a caller's
--   δ.  `Ladder` is generic and `Single`'s step is public, so the same
--   ladder started at σ₀ costs six lines and keeps the matrix
--   UNRELATIVIZED, which `mkReflect` does not.

module Start {k : ℕ} (ψ : Formula S (suc k)) (σ₀ : V ℓ) (oσ₀ : IsOrd σ₀) where

  private
    module Sg = Single ψ

  γₙ : ℕ → V ℓ
  γₙ-ord : (n : ℕ) → IsOrd (γₙ n)
  γₙ zero        = σ₀
  γₙ (suc n)     = Sg.Fstep (γₙ n) (γₙ-ord n)
  γₙ-ord zero    = oσ₀
  γₙ-ord (suc n) = Sg.Fstep-ord (γₙ n) (γₙ-ord n)

  γₙ-step : (n : ℕ) → ⟨ γₙ n ∈ γₙ (suc n) ⟩
  γₙ-step n = Sg.σ∈Fstep (γₙ n) (γₙ-ord n)

  module Lad = Ladder γₙ γₙ-ord γₙ-step

  top : V ℓ
  top = Lad.top

  top-ord : IsOrd top
  top-ord = Lad.top-ord

  σ₀∈top : ⟨ σ₀ ∈ top ⟩
  σ₀∈top = Lad.G∈top 0

  answers : (n : ℕ) (ms : ⟪ Lset (γₙ n) ⟫ ^ k)
          → ⟨ pickStage ψ (LsetEnv (γₙ n) (γₙ-ord n) ms) ∈ γₙ (suc n) ⟩
  answers n = Sg.pickLand (γₙ n) (γₙ-ord n)

  closed : ClosedFor top ψ
  closed = Lad.closure ψ answers

  reflect : (ρ : S ^ k) → Below top ρ → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ top
  reflect = Lad.reflect ψ answers


-- SECTION 3.  THE UNIFORM STAGE.

-- A stage holding two given L-elements.
two-in-a-stage : (u v : S)
  → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ fst u ∈ Lset σ ⟩ × ⟨ fst v ∈ Lset σ ⟩) ∥₁
two-in-a-stage u v = PT.rec squash₁
  (λ { (α , (oα , u∈)) → PT.map
    (λ { (β , (oβ , v∈)) →
        bound2 α β oα oβ .fst
      , ( bound2 α β oα oβ .snd .fst
        , ( Lset-mono {α = bound2 α β oα oβ .fst} {β = α}
              (bound2 α β oα oβ .snd .snd .fst) u∈
          , Lset-mono {α = bound2 α β oα oβ .fst} {β = β}
              (bound2 α β oα oβ .snd .snd .snd) v∈ ) ) })
    (snd v) })
  (snd u)

-- THE RESULT.  Every member of δ has its code IN ONE STAGE.
codes-at-one-stage : (δ κ : S) → SuccCardL δ κ
  → ∥ Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
        ( ⟨ fst δ ∈ Lset β ⟩
        × ⟨ fst κ ∈ Lset β ⟩
        × ((a : S) → ⟨ fst a ∈ fst δ ⟩
           → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁) ) ∥₁
codes-at-one-stage δ κ sc = PT.map go (two-in-a-stage δ κ)
  where
  go : Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ fst δ ∈ Lset σ ⟩ × ⟨ fst κ ∈ Lset σ ⟩)
     → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
         ( ⟨ fst δ ∈ Lset β ⟩
         × ⟨ fst κ ∈ Lset β ⟩
         × ((a : S) → ⟨ fst a ∈ fst δ ⟩
            → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁) )
  go (σ , (oσ , (δ∈ , κ∈))) = St.top , (St.top-ord , (δ∈β , (κ∈β , codes)))
    where
    module St = Start codeFo σ oσ

    δ∈β : ⟨ fst δ ∈ Lset St.top ⟩
    δ∈β = Lset-mono {α = St.top} {β = σ} St.σ₀∈top δ∈

    κ∈β : ⟨ fst κ ∈ Lset St.top ⟩
    κ∈β = Lset-mono {α = St.top} {β = σ} St.σ₀∈top κ∈

    codes : (a : S) → ⟨ fst a ∈ fst δ ⟩
          → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset St.top ⟩ × InjCode F a κ) ∥₁
    codes a a∈δ = PT.map unpack (St.closed (a ∷ κ ∷ []) below sat)
      where
      a∈β : ⟨ fst a ∈ Lset St.top ⟩
      a∈β = layer-trans (Lset-layer St.top) {x = fst δ} {y = fst a} a∈δ δ∈β

      below : Below St.top (a ∷ κ ∷ [])
      below = a∈β , (κ∈β , tt*)

      sat : ⟨ SatEx codeFo (a ∷ κ ∷ []) ⟩
      sat = PT.map (λ { (F , h) → F , code→sat F a κ h })
              (P557.member-code-into-kappa δ κ sc a a∈δ)

      unpack : Σ[ q ∈ S ] (⟨ fst q ∈ Lset St.top ⟩ × ⟨ Sat codeFo (a ∷ κ ∷ []) q ⟩)
             → Σ[ F ∈ S ] (⟨ fst F ∈ Lset St.top ⟩ × InjCode F a κ)
      unpack (q , (q∈ , s)) = q , (q∈ , sat→code q a κ s)
