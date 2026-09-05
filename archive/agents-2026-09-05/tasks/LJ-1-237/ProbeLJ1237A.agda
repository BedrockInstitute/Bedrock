{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1237A: assemble `sl` (StageLevels) and `sc` (StageCovered), the
-- two stage facts that [LJ-1.178]'s module Whole takes as hypotheses.
--
-- Both consume ONE shared object: the stage-carrier level-hood
-- instantiation, the decode-in direction -- the stage believes v is the
-- level at b whenever fst v = Lset (fst b) and b is an ordinal.
--
--   SECTION 1  the generic pieces: the ordinal atom at a slot, the
--              cover sentence, the renaming lemmas
--   SECTION 2  the shared object, parameterized over the stage
--   SECTION 3  sl and sc at the site, on top of the shared object
--
-- DD4: SECTION 2 takes the stage (alpha, ordalpha) as parameters, and the
-- level-hood formula and its decode enter as structure parameters.  The J
-- tower re-instantiates with its own level operation and level-hood.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, and it lives beside its report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-237.ProbeLJ1237A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∀∈ )
open import FOL.Manipulation.Relabelling using
  ( mapFo; mapTm; embed; mapΔ₀; embed-⊨ )
open import FOL.Manipulation.Renaming using
  ( renameFo; renameTm; liftρ; module Sat )
import FOL.Semantics
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-out; Lset-mono )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.BoundedSubset {ℓ} lem using ( isOrdAt; Δ₀-isOrdAt; module Amb )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈; Lset-cumul; ord∈Lset-suc )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Foundations.Prelude using ( funExt )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ

-- =====================================================================
-- SECTION 1: THE GENERIC PIECES.
--
-- The ordinal atom at any slot of any arity (the delivered isOrdAt at
-- slot zero, restated uniformly), the cover sentence, and the renaming
-- that lets a two-variable level-hood be read at a three-variable env.
-- All parameter-free; all tower-free (DD4).
-- =====================================================================

isOrdSlot : ∀ {n : ℕ} → Fin n → Formula (⊥* {ℓ-suc ℓ}) n
isOrdSlot i =
  (∀̇∈ (var i) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc i)))))
  ∧̇ (∀̇∈ (var i)
       (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-isOrdSlot : ∀ {n : ℕ} (i : Fin n) → Δ₀ (isOrdSlot i)
Δ₀-isOrdSlot i = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

-- relabelling and renaming commute (constants vs variables)
mapTm-ren : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} {n m}
            (f : K → K') (ρ : Fin n → Fin m) (t : Term K n)
          → mapTm f (renameTm ρ t) ≡ renameTm ρ (mapTm f t)
mapTm-ren f ρ (con k) = refl
mapTm-ren f ρ (var i) = refl

mapFo-ren : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} {n m}
            (f : K → K') (ρ : Fin n → Fin m) (φ : Formula K n)
          → mapFo f (renameFo ρ φ) ≡ renameFo ρ (mapFo f φ)
mapFo-ren f ρ (t ∈̇ u)  = cong₂ _∈̇_ (mapTm-ren f ρ t) (mapTm-ren f ρ u)
mapFo-ren f ρ (t ≐ u)  = cong₂ _≐_ (mapTm-ren f ρ t) (mapTm-ren f ρ u)
mapFo-ren f ρ (φ ∧̇ ψ)  = cong₂ _∧̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
mapFo-ren f ρ (φ ∨̇ ψ)  = cong₂ _∨̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
mapFo-ren f ρ (φ ⇒̇ ψ)  = cong₂ _⇒̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
mapFo-ren f ρ (¬̇ φ)    = cong ¬̇_ (mapFo-ren f ρ φ)
mapFo-ren f ρ ⊤̇        = refl
mapFo-ren f ρ ⊥̇        = refl
mapFo-ren f ρ (∃̇ φ)    = cong ∃̇_ (mapFo-ren f (liftρ ρ) φ)
mapFo-ren f ρ (∀̇ φ)    = cong ∀̇_ (mapFo-ren f (liftρ ρ) φ)
mapFo-ren f ρ (∀̇∈ t φ) =
  cong₂ ∀̇∈ (mapTm-ren f ρ t) (mapFo-ren f (liftρ ρ) φ)
mapFo-ren f ρ (∃̇∈ t φ) =
  cong₂ ∃̇∈ (mapTm-ren f ρ t) (mapFo-ren f (liftρ ρ) φ)

-- the weakening that reads a two-variable formula at three variables
wk23 : Fin 2 → Fin 3
wk23 zero = zero
wk23 (suc zero) = suc zero

-- the cover sentence at env x ∷ []: there is an ordinal b and a value v
-- with the level-hood of v at b, and x is a member of v.
coverForm : Formula (⊥* {ℓ-suc ℓ}) 2 → Formula (⊥* {ℓ-suc ℓ}) 1
coverForm φ₀ =
  ∃̇ (∃̇ ( isOrdSlot (suc zero)
        ∧̇ ( renameFo wk23 φ₀
          ∧̇ (var (suc (suc zero)) ∈̇ var zero) ) ))

-- =====================================================================
-- SECTION 2: THE SHARED OBJECT, parameterized over the stage.
--
-- StageLH takes the stage (alpha, ordalpha) and the level-hood formula
-- φ₀ together with its decode-in lh, and gives the two consumer-facing
-- facts: the ordinal read-off and the level-hood witness at the stage.
-- =====================================================================

module StageLH (α : S) (ordα : IsOrd α)
               (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
               where

  module ASt = AtStage α ordα
  open ASt
  open AbsL

  module SatM = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ z → z ∈ˢ Lset α)) {K = SL} id

  -- the stage's outer reading of a parameter-free formula equals the
  -- ambient reading at the empty constant domain (both directions)
  embAmb : ∀ {n} (γ : Vec S n) (χ : Formula (⊥* {ℓ-suc ℓ}) n)
         → ⟨ γ AbsL.⊨ᵛ embed χ ⟩ → ⟨ γ Amb.⊨ₚ χ ⟩
  embAmb γ χ h =
    subst (λ j → ⟨ Sem.At._⊨_ (⊥* {ℓ-suc ℓ}) j γ χ ⟩)
      (funExt (λ b → Empty.rec* b))
      (subst ⟨_⟩ (embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst χ γ) h)

  embAmb⁻¹ : ∀ {n} (γ : Vec S n) (χ : Formula (⊥* {ℓ-suc ℓ}) n)
           → ⟨ γ Amb.⊨ₚ χ ⟩ → ⟨ γ AbsL.⊨ᵛ embed χ ⟩
  embAmb⁻¹ γ χ h =
    subst ⟨_⟩ (sym (embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst χ γ))
      (subst (λ j → ⟨ Sem.At._⊨_ (⊥* {ℓ-suc ℓ}) j γ χ ⟩)
         (sym (funExt (λ b → Empty.rec* b))) h)

  -- the ordinal read-off: the stage believes b is an ordinal iff it is
  ord-out : (b : SL) → ⟨ (b ∷ []) AbsL.⊨ᵐ embed isOrdAt ⟩ → IsOrd (fst b)
  ord-out b h = Amb.isOrdAt-out (fst b)
    (embAmb (fst b ∷ []) isOrdAt
      (subst ⟨_⟩ (abs₀ (mapΔ₀ Empty.rec* Δ₀-isOrdAt) (b ∷ [])) h))

  ord-in : (b : SL) → IsOrd (fst b) → ⟨ (b ∷ []) AbsL.⊨ᵐ embed isOrdAt ⟩
  ord-in b ob = subst ⟨_⟩ (sym (abs₀ (mapΔ₀ Empty.rec* Δ₀-isOrdAt) (b ∷ [])))
    (embAmb⁻¹ (fst b ∷ []) isOrdAt (Amb.isOrdAt-in (fst b) ob))

  -- the shared decode-in (the structure parameter; the L tower
  -- supplies this at instantiation)

  -- the ordinal atom at slot suc zero, at a three-variable environment
  ord-slot-in : (v b x : SL) → IsOrd (fst b)
              → ⟨ (v ∷ b ∷ x ∷ []) AbsL.⊨ᵐ embed (isOrdSlot (suc zero)) ⟩
  ord-slot-in v b x ob =
    ( λ a a∈b c c∈a → ob .fst {fst a} {fst c} c∈a a∈b )
    , ( λ a a∈b c c∈a d d∈c → ob .snd (fst a) a∈b {fst c} {fst d} d∈c c∈a )

  -- ===================================================================
  -- SECTION 3: sl and sc, on top of the shared object (the decode-in
  -- lh enters as a parameter, so the assembly is tower-free).
  -- ===================================================================

  module Build
    (lh : (v b : SL) → IsOrd (fst b) → fst v ≡ Lset (fst b)
        → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ embed φ₀ ⟩)
    where

    -- the level closure: Lset b ∈ Lset α from sucV b ∈ α, for b an ordinal
    Lset∈suc : (b : S) → ⟨ Lset b ∈ˢ Lset (sucV b) ⟩
    Lset∈suc b = subst (λ w → ⟨ Lset b ∈ˢ w ⟩) (sym (Lset-suc b))
      (𝒟ₒ-intro (Lset b) (Lset b) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset b) ∣₁)

    sl : (succα : (d : S) → ⟨ d ∈ˢ α ⟩ → ⟨ sucV d ∈ˢ α ⟩)
       → (b : SL) → ⟨ (b ∷ []) AbsL.⊨ᵐ embed isOrdAt ⟩
       → ⟨ (b ∷ []) AbsL.⊨ᵐ embed (∃̇ φ₀) ⟩
    sl succα b hb = ∣ v , lh v b ob refl ∣₁
      where
      ob : IsOrd (fst b)
      ob = ord-out b hb
      b∈α : ⟨ fst b ∈ˢ α ⟩
      b∈α = ord∈Lset→∈ α ordα (fst b) ob (snd b)
      sucb∈α : ⟨ sucV (fst b) ∈ˢ α ⟩
      sucb∈α = succα (fst b) b∈α
      v : SL
      v = Lset (fst b) , Lset-mono {α = α} {β = sucV (fst b)} sucb∈α
            {x = Lset (fst b)} (Lset∈suc (fst b))

    sc : (succα : (d : S) → ⟨ d ∈ˢ α ⟩ → ⟨ sucV d ∈ˢ α ⟩)
       → (x : SL) → ⟨ (x ∷ []) AbsL.⊨ᵐ embed (coverForm φ₀) ⟩
    sc succα x = PT.rec (snd ((x ∷ []) AbsL.⊨ᵐ embed (coverForm φ₀))) go
      (Lset-out α (fst x) (snd x))
      where
      go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ fst x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
         → ⟨ (x ∷ []) AbsL.⊨ᵐ embed (coverForm φ₀) ⟩
      go (δ , δ∈α , x∈𝒟ₒδ) = ∣ b , ∣ v , (ordIn , (belConj , x∈v)) ∣₁ ∣₁
        where
        oδ : IsOrd δ
        oδ = mem-ord {A = α} ordα δ δ∈α
        osδ : IsOrd (sucV δ)
        osδ = suc-ord oδ
        sδ∈α : ⟨ sucV δ ∈ˢ α ⟩
        sδ∈α = succα δ δ∈α
        ssδ∈α : ⟨ sucV (sucV δ) ∈ˢ α ⟩
        ssδ∈α = succα (sucV δ) sδ∈α

        b : SL
        b = sucV δ , Lset-cumul (sucV δ) α osδ ordα sδ∈α (ord∈Lset-suc (sucV δ) osδ)
        v : SL
        v = Lset (sucV δ) , Lset-mono {α = α} {β = sucV (sucV δ)} ssδ∈α
              {x = Lset (sucV δ)} (Lset∈suc (sucV δ))

        ordIn : ⟨ (v ∷ b ∷ x ∷ []) AbsL.⊨ᵐ embed (isOrdSlot (suc zero)) ⟩
        ordIn = ord-slot-in v b x osδ

        belIn : ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ embed φ₀ ⟩
        belIn = lh v b osδ refl

        ag : SatM.Agrees wk23 (v ∷ b ∷ x ∷ []) (v ∷ b ∷ [])
        ag zero = refl
        ag (suc zero) = refl

        belRen : ⟨ (v ∷ b ∷ x ∷ []) AbsL.⊨ᵐ renameFo wk23 (embed φ₀) ⟩
        belRen = subst ⟨_⟩ (sym (SatM.⊨-rename wk23 (embed φ₀)
                 (v ∷ b ∷ x ∷ []) (v ∷ b ∷ []) ag)) belIn

        belConj : ⟨ (v ∷ b ∷ x ∷ []) AbsL.⊨ᵐ embed (renameFo wk23 φ₀) ⟩
        belConj = subst (λ ψ → ⟨ (v ∷ b ∷ x ∷ []) AbsL.⊨ᵐ ψ ⟩)
          (sym (mapFo-ren Empty.rec* wk23 φ₀)) belRen

        x∈v : ⟨ fst x ∈ˢ fst v ⟩
        x∈v = subst (λ w → ⟨ fst x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟ₒδ

    -- sl and sc, assembled at a concrete limit stage
    module At (succα : (d : S) → ⟨ d ∈ˢ α ⟩ → ⟨ sucV d ∈ˢ α ⟩) where
      stageLevels : (b : SL) → ⟨ (b ∷ []) AbsL.⊨ᵐ embed isOrdAt ⟩
                  → ⟨ (b ∷ []) AbsL.⊨ᵐ embed (∃̇ φ₀) ⟩
      stageLevels = sl succα

      stageCovered : (x : SL) → ⟨ (x ∷ []) AbsL.⊨ᵐ embed (coverForm φ₀) ⟩
      stageCovered = sc succα
