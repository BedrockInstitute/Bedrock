{-# OPTIONS --cubical --safe --guardedness #-}
-- ProbeGround: the [L3.31-GLp] POC 2, the GEOLOGY STATEMENT LAYER.
--
-- Geology works INSIDE V looking down: W ⊆ V a transitive class, G ∈ V generic
-- over W, V = W[G].  Measured here, piece by piece, at a CLASS carrier:
--   (a) "W ⊨ ZFC"   -- which delivered satisfaction face states it?
--   (b) "G generic over W"
--   (c) "V = W[G]"
-- plus the mantle layer, and the trivial-forcing positive control.
-- Probe-local, untracked. No postulates, no holes, no TERMINATING pragmas.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeGround {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; Transitive; _↾_ )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; isL-trans; 𝒮ʟ )
import L.Model
open import ProbeForce {ℓ} using ( Poset; Filter; module Force; singl∈ )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⁅_⁆s )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------
-- (a) "W ⊨ ZFC" AT A TRANSITIVE CLASS.
--
-- FINDING: free.  ZFStructure's carrier is a bare Type, `_↾_` turns ANY class
-- predicate into a carrier with no smallness/set-hood demand, and FOL.ZFModel
-- is generic in the structure.  The R2p monomorphism tax (the 6,219-line
-- 𝒮ʟ-bound cone) does NOT reach this layer: it is a tax on L/Coding, not on
-- the satisfaction face.
------------------------------------------------------------------------

Class : Type (ℓ-suc (ℓ-suc ℓ))
Class = S → hProp (ℓ-suc ℓ)

_⊨ZFC : Class → Type (ℓ-suc (ℓ-suc ℓ))
W ⊨ZFC = FOL.ZFModel.isZFCModel (𝒮ᵥ ↾ W)

_⊨ZF : Class → Type (ℓ-suc (ℓ-suc ℓ))
W ⊨ZF = FOL.ZFModel.isZFModel (𝒮ᵥ ↾ W)

-- MACHINE-CHECKED (1): at W = isL the geology statement is DEFINITIONALLY the
-- delivered L-side face.  `refl` is the whole proof.
_ : (isL ⊨ZFC) ≡ FOL.ZFModel.isZFCModel 𝒮ʟ
_ = refl

-- MACHINE-CHECKED (2): and the tree already PROVES it, at a proper class.
-- The geology carrier's hardest-looking clause has a delivered witness today.
groundL : LEM (ℓ-suc ℓ) → isL ⊨ZFC
groundL lem = L.Model.L⊨ZFC {ℓ} lem

-- Transitivity is NOT consumed by the statement; it is consumed only by
-- absoluteness.  Recorded as a separate field below.
transL : Transitive 𝒮ᵥ isL
transL = isL-trans

------------------------------------------------------------------------
-- (b), (c) AND THE GROUND PREDICATE
------------------------------------------------------------------------

module Geology (𝔓 : Poset) (𝔊 : Filter 𝔓) where

  open Poset 𝔓
  open Filter 𝔊
  open Force 𝔓 𝔊 using ( chk; val; val-chk; isName )

  Dense : S → Type (ℓ-suc ℓ)
  Dense D = ((q : S) → ⟨ q ∈ˢ D ⟩ → ⟨ q ∈ˢ ∣P∣ ⟩)
          × ((p : S) → ⟨ p ∈ˢ ∣P∣ ⟩
             → ∥ Σ[ q ∈ S ] ((⟨ q ∈ˢ D ⟩) × ⟨ q ≼ p ⟩) ∥₁)

  -- (b) G meets every dense subset of P lying in W
  Generic : Class → Type (ℓ-suc ℓ)
  Generic W = (D : S) → ⟨ W D ⟩ → Dense D
            → ∥ Σ[ q ∈ S ] ((⟨ q ∈ˢ ∣G∣ ⟩) × ⟨ q ∈ˢ D ⟩) ∥₁

  -- (c) V = W[G]: every set is the value of a W-name
  IsExtension : Class → Type (ℓ-suc ℓ)
  IsExtension W = (x : S)
    → ∥ Σ[ τ ∈ S ] ((⟨ W τ ⟩) × (⟨ isName τ ⟩) × (val τ ≡ x)) ∥₁

  record IsGround (W : Class) : Type (ℓ-suc (ℓ-suc ℓ)) where
    field
      wTrans : Transitive 𝒮ᵥ W
      wZFC   : W ⊨ZFC
      wGen   : Generic W
      wExt   : IsExtension W

  ----------------------------------------------------------------------
  -- THE MANTLE, and the size wall that is the real remainder.
  --
  -- The mantle is the intersection of all grounds.  Writing it in the ambient
  -- logic costs ONE LINE -- but the result is one universe too big to be a
  -- `Class`, so `𝒮ᵥ ↾ Mantle` does not typecheck and "𝕄 ⊨ ZFC" is NOT
  -- STATEABLE by the delivered restriction operator.  That size gap IS the
  -- Laver-Woodin definability theorem's job; `MantleIsClass` states the debt.
  ----------------------------------------------------------------------

  Mantle : S → Type (ℓ-suc (ℓ-suc ℓ))
  Mantle x = (W : Class) → IsGround W → ⟨ W x ⟩

  MantleIsClass : Type (ℓ-suc (ℓ-suc ℓ))
  MantleIsClass = Σ[ M ∈ Class ]
    ((x : S) → (⟨ M x ⟩ → Mantle x) × (Mantle x → ⟨ M x ⟩))

  -- with the debt discharged, the mantle rejoins the delivered face:
  mantle⊨ : MantleIsClass → Type (ℓ-suc (ℓ-suc ℓ))
  mantle⊨ (M , _) = M ⊨ZFC

------------------------------------------------------------------------
-- POSITIVE CONTROL (C-6): the trivial forcing.  P = G = {𝟙}.  Both the
-- poset-side pieces are green, and (b) holds for EVERY class W.
------------------------------------------------------------------------

module Trivial (𝟙 : S) where

  t∈ : ⟨ 𝟙 ∈ˢ ⁅ 𝟙 ⁆s ⟩
  t∈ = ∈∈ₛ {a = 𝟙} {b = ⁅ 𝟙 ⁆s} .snd (singl∈ refl)

  P₁ : Poset
  P₁ = record
    { ∣P∣ = ⁅ 𝟙 ⁆s ; _≼_ = λ p _ → p ∈ˢ ⁅ 𝟙 ⁆s ; top = 𝟙 ; top∈P = t∈
    ; ≼-refl = λ _ h → h ; ≼-trans = λ _ _ _ h _ → h ; ≼-top = λ _ h → h }

  G₁ : Filter P₁
  G₁ = record
    { ∣G∣ = ⁅ 𝟙 ⁆s ; G⊆P = λ _ h → h ; top∈G = t∈
    ; upward = λ _ _ _ hq _ → hq
    ; directed = λ _ _ _ _ → ∣ 𝟙 , t∈ , t∈ , t∈ ∣₁ }

  open Geology P₁ G₁
  open Force P₁ G₁ using ( chk; val; val-chk; isName )

  -- (b) GREEN.  Note W is never used: over the trivial poset every class is
  -- met, which is exactly why this is a positive control and not a theorem.
  trivGeneric : (W : Class) → Generic W
  trivGeneric W D _ (_ , Ddense) = PT.map mk (Ddense 𝟙 t∈)
    where
    mk : Σ[ q ∈ S ] ((⟨ q ∈ˢ D ⟩) × ⟨ q ∈ˢ ⁅ 𝟙 ⁆s ⟩)
       → Σ[ q ∈ S ] ((⟨ q ∈ˢ ⁅ 𝟙 ⁆s ⟩) × ⟨ q ∈ˢ D ⟩)
    mk (q , qD , q≼) = q , q≼ , qD

  -- (c) GREEN on its value half, by POC 1's baby lemma.
  Wall : Class
  Wall x = x ≈ˢ x

  -- The one clause POC 2 does NOT pay: "the check name is a name".
  NameRemainder : Type (ℓ-suc ℓ)
  NameRemainder = (x : S) → ⟨ isName (chk x) ⟩

  trivExt : NameRemainder → IsExtension Wall
  trivExt nm x = ∣ chk x , refl , nm x , val-chk x ∣₁
