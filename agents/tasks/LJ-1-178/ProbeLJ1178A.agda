{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.178] probe A.  THE BUILD OF `levelIn` AND `cover`, and the
-- term the build stops at.
--
-- [LJ-1.160] measured that the wall `π (Lset m') ≡ Lset (π m')` is an
-- artifact of WHERE the argument runs, and that both hypotheses follow
-- from ONE crossing face at the collapse image.  It left three facts
-- open: CrossOut, HasLevels and Covered.
--
-- This probe supplies as much of that face as the delivered tree
-- allows, and names what is left.  Everything is generic in the
-- carrier and in the level-hood formula (DD4): the J tower supplies a
-- different formula and re-instantiates.
--
--   SECTION 1  the face, and levelIn / cover from it       ([LJ-1.160])
--   SECTION 2  CrossOut from the AMBIENT read-off             (NEW)
--   SECTION 3  the two transports: stage -> hull -> image     (NEW)
--   SECTION 4  HasLevels and Covered from stage facts         (NEW)
--
-- L.BoundedSubset is NOT imported: a sibling holds src/L/Condensation
-- red (2026-08-14 08:34), and every path to the site runs through it.
-- The delivered objects the probe would take from there are named as
-- hypotheses with their delivered types, at their file:line.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, and it lives beside its report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-178.ProbeLJ1178A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∀∈; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Relabelling using
  ( mapFo; mapTm; mapFo-comp; embed; mapΔ₀ )
open import FOL.Manipulation.Renaming using
  ( renameFo; renameTm; liftρ; module Sat )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans; module Collapse )
open import L.Constructible {ℓ} using ( Lset; IsOrd )
open import L.Hull {ℓ} lem using ( module AtStage )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( _×_; _,_; Σ≡Prop )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- ---------------------------------------------------------------------
-- A parameter-free formula survives every relabelling.  One line, and
-- it is what lets ONE formula be read at the stage, at the hull and at
-- the collapse image without three copies.
-- ---------------------------------------------------------------------

embed-stable : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} {n : ℕ}
               (f : K → K') (χ : Formula (⊥* {ℓ-suc ℓ}) n)
             → mapFo f (embed χ) ≡ embed χ
embed-stable f χ =
  mapFo-comp Empty.rec* f χ
  ∙ cong (λ g → mapFo g χ) (funExt (λ b → Empty.rec* b))

-- The Sigma-1 witness rides a relabelling, exactly as the Delta-0
-- witness does.  MEASURED MISSING: `mapΔ₀` is delivered
-- (src/FOL/Manipulation/Relabelling.lagda.md:209) and `mapΣ₁` is NOT.
-- Two clauses close it, so the certificate at any carrier is free.

mapΣ₁ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        {n : ℕ} {φ : Formula K n} → Σ₁ φ → Σ₁ (mapFo f φ)
mapΣ₁ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
mapΣ₁ f (σ-∃ s)  = σ-∃ (mapΣ₁ f s)

embed-Σ₁ : ∀ {ℓc} {K : Type ℓc} {n : ℕ} {χ : Formula (⊥* {ℓ-suc ℓ}) n}
         → Σ₁ χ → Σ₁ (embed {K = K} χ)
embed-Σ₁ = mapΣ₁ Empty.rec*

-- ---------------------------------------------------------------------
-- "x is an ordinal", parameter-free.  The spelling is the delivered one
-- (src/L/BoundedSubset.lagda.md:795-803); the two readings are restated
-- here GENERIC IN THE INTERPRETATION, so the same pair serves the
-- ambient axis and every carrier's axis.  The delivered pair
-- (src/L/BoundedSubset.lagda.md:813-821) is fixed at one interpretation.
-- ---------------------------------------------------------------------

isOrdAt : Formula (⊥* {ℓ-suc ℓ}) 1
isOrdAt =
  (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero)))))
  ∧̇ (∀̇∈ (var zero)
       (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-isOrdAt : Δ₀ isOrdAt
Δ₀-isOrdAt = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

module OrdRead {ℓc : Level} {K : Type ℓc} (ι : K → S) where
  module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open Sem.At K ι using ( _⊨_ )

  ord-in : (x : S) → IsOrd x → ⟨ (x ∷ []) ⊨ embed isOrdAt ⟩
  ord-in x o = ( λ a a∈x b hb → o .fst {a} {b} hb a∈x )
             , ( λ a a∈x b b∈a c hc → o .snd a a∈x {b} {c} hc b∈a )

  ord-out : (x : S) → ⟨ (x ∷ []) ⊨ embed isOrdAt ⟩ → IsOrd x
  ord-out x h = ( λ {u} {y} y∈u u∈x → h .fst u u∈x y y∈u )
              , ( λ a a∈x {u} {y} y∈u u∈a → h .snd a a∈x u u∈a y y∈u )

-- =====================================================================
-- SECTION 1: THE CROSSING FACE AT A TRANSITIVE CARRIER, and the two
-- delivered hypotheses derived from it.  This is [LJ-1.160]'s argument,
-- restated at ONE parameter-free formula so that the same statement
-- reads at every carrier below.
-- =====================================================================

module Crossing (P : S) (Ptr : isTrans P)
                (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) where

  module AbsP = FOL.Absoluteness.Single 𝒮ᵥ (λ z → z ∈ˢ P) Ptr

  SP : Type (ℓ-suc ℓ)
  SP = AbsP.SM

  φP : Formula SP 2
  φP = embed φ₀

  -- "the inner world of P believes that v is the level at b"
  Bel : SP → SP → Type (ℓ-suc ℓ)
  Bel v b = ⟨ (v ∷ b ∷ []) AbsP.⊨ᵐ φP ⟩

  CrossOut : Type (ℓ-suc ℓ)
  CrossOut = (v b : SP) → IsOrd (fst b) → Bel v b → fst v ≡ Lset (fst b)

  HasLevels : Type (ℓ-suc ℓ)
  HasLevels = (b : SP) → IsOrd (fst b) → ∥ Σ[ v ∈ SP ] Bel v b ∥₁

  Covered : Type (ℓ-suc ℓ)
  Covered = (x : SP)
          → ∥ Σ[ b ∈ SP ] Σ[ v ∈ SP ]
                (IsOrd (fst b) × Bel v b × ⟨ fst x ∈ˢ fst v ⟩) ∥₁

  -- THE ASSEMBLY.  M is the hull, pi the collapse; both delivered.
  module Assembly (M : S) (pi : S → S)
    (piIntro : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ pi y ∈ˢ P ⟩)
    (co : CrossOut) where

    -- src/L/BoundedSubset.lagda.md:917, verbatim at P = C.πX.
    levelIn : HasLevels → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ P ⟩ → ⟨ Lset δ ∈ˢ P ⟩
    levelIn hl δ oδ δ∈ = PT.rec (snd (Lset δ ∈ˢ P)) go (hl (δ , δ∈) oδ)
      where
      go : Σ[ v ∈ SP ] Bel v (δ , δ∈) → ⟨ Lset δ ∈ˢ P ⟩
      go (v , bel) = subst (λ w → ⟨ w ∈ˢ P ⟩) (co v (δ , δ∈) oδ bel) (snd v)

    -- src/L/BoundedSubset.lagda.md:918-919, verbatim at P = C.πX.
    cover : Covered → (y : S) → ⟨ y ∈ˢ M ⟩
          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ P ⟩ × ⟨ pi y ∈ˢ Lset γ ⟩) ∥₁
    cover cv y y∈M = PT.rec squash₁ go (cv (pi y , piIntro y y∈M))
      where
      go : Σ[ b ∈ SP ] Σ[ v ∈ SP ]
             (IsOrd (fst b) × Bel v b × ⟨ pi y ∈ˢ fst v ⟩)
         → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ P ⟩ × ⟨ pi y ∈ˢ Lset γ ⟩) ∥₁
      go (b , v , ob , bel , y∈v) =
        ∣ fst b , ( ob , snd b
                  , subst (λ w → ⟨ pi y ∈ˢ w ⟩) (co v b ob bel) y∈v ) ∣₁

-- =====================================================================
-- SECTION 2: CrossOut FROM THE AMBIENT READ-OFF.
--
-- Devlin's (a) is `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]`, and it is a statement
-- of the AMBIENT universe (dev/literature/devlin-II5.md:93-96, :102-106).
-- With that fact, CrossOut is ONE line at any transitive carrier: the
-- inner belief goes up by σ₁-up, and the ambient read-off finishes.
--
-- THIS IS [LJ-1.160] SECTION 3.3's FIRST OPEN ROW, REDUCED.
-- =====================================================================

module AmbientCross (P : S) (Ptr : isTrans P)
                    (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) where

  module Cr = Crossing P Ptr φ₀

  -- Devlin (a), at the ambient carrier, for THIS formula.
  AmbientRead : Type (ℓ-suc ℓ)
  AmbientRead = (v b : S) → IsOrd b
              → ⟨ (v ∷ b ∷ []) Cr.AbsP.⊨ᵛ Cr.φP ⟩ → v ≡ Lset b

  crossOut : Σ₁ Cr.φP → AmbientRead → Cr.CrossOut
  crossOut s amb v b ob bel =
    amb (fst v) (fst b) ob (Cr.AbsP.σ₁-up s (v ∷ b ∷ []) bel)

-- =====================================================================
-- SECTION 5: Covered FROM ONE STAGE FACT.
--
-- The stage believes that every set lies in a level below.  The same
-- two transports carry it to the image.  The statement needs three
-- bound variables, so it needs the ordinal atom at a SLOT and a
-- weakening of the level-hood formula; both are written generic, and
-- the weakening rides the delivered `⊨-rename`.
-- =====================================================================

-- The ordinal atom at any slot of any arity.  `isOrdAt = isOrdSlot zero`.
isOrdSlot : ∀ {n : ℕ} → Fin n → Formula (⊥* {ℓ-suc ℓ}) n
isOrdSlot i =
  (∀̇∈ (var i) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc i)))))
  ∧̇ (∀̇∈ (var i)
       (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-isOrdSlot : ∀ {n : ℕ} (i : Fin n) → Δ₀ (isOrdSlot i)
Δ₀-isOrdSlot i = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

module OrdSlotRead {ℓc : Level} {K : Type ℓc} (ι : K → S) where
  module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  open Sem.At K ι using ( _⊨_ )

  slot-out : ∀ {n : ℕ} (i : Fin n) (γ : Vec S n)
           → ⟨ γ ⊨ embed (isOrdSlot i) ⟩ → IsOrd (lookup i γ)
  slot-out i γ h = ( λ {u} {y} y∈u u∈x → h .fst u u∈x y y∈u )
                 , ( λ a a∈x {u} {y} y∈u u∈a → h .snd a a∈x u u∈a y y∈u )

-- Relabelling and renaming commute: the first touches constants only,
-- the second variables only.
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

-- The weakening that puts a two-variable formula into a three-variable
-- environment without moving either variable.
wk23 : Fin 2 → Fin 3
wk23 zero = zero
wk23 (suc zero) = suc zero

-- The cover sentence at env `x ∷ []`: there is an ordinal b and a value
-- v with the level-hood of v at b, and x is a member of v.
coverForm : Formula (⊥* {ℓ-suc ℓ}) 2 → Formula (⊥* {ℓ-suc ℓ}) 1
coverForm φ₀ =
  ∃̇ (∃̇ ( isOrdSlot (suc zero)
        ∧̇ ( renameFo wk23 φ₀
          ∧̇ (var (suc (suc zero)) ∈̇ var zero) ) ))

-- The membership atom, as a formula, so the collapse's iso carries it.
memAtom : Formula (⊥* {ℓ-suc ℓ}) 2
memAtom = var (suc zero) ∈̇ var zero

-- =====================================================================
-- SECTION 3: THE TWO TRANSPORTS, stage -> hull -> image.
--
-- Both are DELIVERED.  The stage-to-hull leg is the hull's elementarity
-- (src/L/Hull.lagda.md:174-176), supplied at the real site by
-- `HEDC.elem` (src/L/BoundedSubset.lagda.md:759-760, wired :1544).  The
-- hull-to-image leg is the collapse's satisfaction iso-invariance
-- (src/L/BoundedSubset.lagda.md:195-318, at `CollapseIso` :321).
--
-- A sibling holds src/L/Condensation red, so the import path to
-- BoundedSubset is closed and the two legs enter as named hypotheses
-- with their delivered types.
-- =====================================================================

module Site (α : S) (ordα : IsOrd α)
  (M : S) (M⊆L : (z : S) → ⟨ z ∈ˢ M ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (P : S) (Ptr : isTrans P)
  (pi : S → S)
  (piIntro : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ pi y ∈ˢ P ⟩)
  (piMember : (z : S) → ⟨ z ∈ˢ P ⟩
            → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (pi y ≡ z)) ∥₁)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) where

  module ASt = AtStage α ordα
  module A = ASt.AtM M M⊆L
  module Cr = Crossing P Ptr φ₀

  module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ z → z ∈ˢ M))
  open SemM.At A.SM id renaming ( _⊨_ to _⊨ᴹ_ )

  g : A.SM → Cr.SP
  g q = pi (fst q) , piIntro (fst q) (snd q)

  IsoFwd : Type (ℓ-suc ℓ)
  IsoFwd = (n : ℕ) (χ : Formula A.SM n) (δ : Vec A.SM n)
         → ⟨ δ ⊨ᴹ χ ⟩ → ⟨ map g δ Cr.AbsP.⊨ᵐ mapFo g χ ⟩

  IsoBwd : Type (ℓ-suc ℓ)
  IsoBwd = (n : ℕ) (χ : Formula A.SM n) (δ : Vec A.SM n)
         → ⟨ map g δ Cr.AbsP.⊨ᵐ mapFo g χ ⟩ → ⟨ δ ⊨ᴹ χ ⟩

  -- The four legs, each one line, all at ONE parameter-free formula.
  fromStage : A.Elementary → (n : ℕ) (χ : Formula (⊥* {ℓ-suc ℓ}) n)
              (δ : Vec A.SM n)
            → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ embed χ ⟩ → ⟨ δ ⊨ᴹ embed χ ⟩
  fromStage el n χ δ h =
    subst ⟨_⟩ (sym (el n (embed χ) δ))
      (subst (λ ψ → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ ψ ⟩)
             (sym (embed-stable A.inL χ)) h)

  toStage : A.Elementary → (n : ℕ) (χ : Formula (⊥* {ℓ-suc ℓ}) n)
            (δ : Vec A.SM n)
          → ⟨ δ ⊨ᴹ embed χ ⟩ → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ embed χ ⟩
  toStage el n χ δ h =
    subst (λ ψ → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ ψ ⟩) (embed-stable A.inL χ)
      (subst ⟨_⟩ (el n (embed χ) δ) h)

  toImage : IsoFwd → (n : ℕ) (χ : Formula (⊥* {ℓ-suc ℓ}) n) (δ : Vec A.SM n)
          → ⟨ δ ⊨ᴹ embed χ ⟩ → ⟨ map g δ Cr.AbsP.⊨ᵐ embed χ ⟩
  toImage iso n χ δ h =
    subst (λ ψ → ⟨ map g δ Cr.AbsP.⊨ᵐ ψ ⟩) (embed-stable g χ)
      (iso n (embed χ) δ h)

  fromImage : IsoBwd → (n : ℕ) (χ : Formula (⊥* {ℓ-suc ℓ}) n) (δ : Vec A.SM n)
            → ⟨ map g δ Cr.AbsP.⊨ᵐ embed χ ⟩ → ⟨ δ ⊨ᴹ embed χ ⟩
  fromImage iso n χ δ h =
    iso n (embed χ) δ
      (subst (λ ψ → ⟨ map g δ Cr.AbsP.⊨ᵐ ψ ⟩) (sym (embed-stable g χ)) h)

  -- The ordinal premise, moved from the meta level onto the image's
  -- own axis: abs₀ at the transitive image, then the ambient reader.
  ιP : Cr.SP → S
  ιP = fst

  ordP-in : (b : Cr.SP) → IsOrd (fst b)
          → ⟨ (b ∷ []) Cr.AbsP.⊨ᵐ embed isOrdAt ⟩
  ordP-in b ob =
    subst ⟨_⟩ (sym (Cr.AbsP.abs₀ (mapΔ₀ Empty.rec* Δ₀-isOrdAt) (b ∷ [])))
      (OrdRead.ord-in ιP (fst b) ob)

-- =====================================================================
-- SECTION 4: HasLevels FROM ONE STAGE FACT.
--
-- The stage believes that every ordinal has a level.  The hull believes
-- it because the hull is elementary; the image believes it because the
-- collapse is an isomorphism.  Nothing here mentions the collapse of a
-- level, so [LJ-1.51]'s wall does not appear.
-- =====================================================================

  StageLevels : Type (ℓ-suc ℓ)
  StageLevels = (b : ASt.SL) → ⟨ (b ∷ []) ASt.AbsL.⊨ᵐ embed isOrdAt ⟩
              → ⟨ (b ∷ []) ASt.AbsL.⊨ᵐ embed (∃̇ φ₀) ⟩

  hasLevels : A.Elementary → IsoFwd → IsoBwd → StageLevels → Cr.HasLevels
  hasLevels el fwd bwd sl b ob = PT.rec squash₁ go (piMember (fst b) (snd b))
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (pi y ≡ fst b))
       → ∥ Σ[ v ∈ Cr.SP ] Cr.Bel v b ∥₁
    go (y , y∈M , e) = PT.map mk hullSide
      where
      bM : A.SM
      bM = y , y∈M

      gb≡b : g bM ≡ b
      gb≡b = Σ≡Prop (λ z → (z ∈ˢ P) .snd) e

      ordImage : ⟨ (g bM ∷ []) Cr.AbsP.⊨ᵐ embed isOrdAt ⟩
      ordImage = subst (λ q → ⟨ (q ∷ []) Cr.AbsP.⊨ᵐ embed isOrdAt ⟩)
                       (sym gb≡b) (ordP-in b ob)

      ordHull : ⟨ (bM ∷ []) ⊨ᴹ embed isOrdAt ⟩
      ordHull = fromImage bwd 1 isOrdAt (bM ∷ []) ordImage

      hullSide : ∥ Σ[ v ∈ A.SM ] ⟨ (v ∷ bM ∷ []) ⊨ᴹ embed φ₀ ⟩ ∥₁
      hullSide = fromStage el 1 (∃̇ φ₀) (bM ∷ [])
                   (sl (A.inL bM) (toStage el 1 isOrdAt (bM ∷ []) ordHull))

      mk : Σ[ v ∈ A.SM ] ⟨ (v ∷ bM ∷ []) ⊨ᴹ embed φ₀ ⟩
         → Σ[ v ∈ Cr.SP ] Cr.Bel v b
      mk (v , h) = g v
                 , subst (λ q → Cr.Bel (g v) q) gb≡b
                     (toImage fwd 2 φ₀ (v ∷ bM ∷ []) h)

  -- ===================================================================
  -- Covered FROM ONE STAGE FACT, by the same two transports.
  -- ===================================================================

  module SatM = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ z → z ∈ˢ M))
                    {K = A.SM} id

  agM : (v b x : A.SM) → SatM.Agrees wk23 (v ∷ b ∷ x ∷ []) (v ∷ b ∷ [])
  agM v b x zero = refl
  agM v b x (suc zero) = refl

  StageCovered : Type (ℓ-suc ℓ)
  StageCovered = (x : ASt.SL)
               → ⟨ (x ∷ []) ASt.AbsL.⊨ᵐ embed (coverForm φ₀) ⟩

  covered : A.Elementary → IsoFwd → StageCovered → Cr.Covered
  covered el fwd sc x = PT.rec squash₁ go (piMember (fst x) (snd x))
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (pi y ≡ fst x))
       → ∥ Σ[ b ∈ Cr.SP ] Σ[ v ∈ Cr.SP ]
             (IsOrd (fst b) × Cr.Bel v b × ⟨ fst x ∈ˢ fst v ⟩) ∥₁
    go (y , y∈M , e) = PT.rec squash₁ outer hullSide
      where
      xM : A.SM
      xM = y , y∈M

      gx≡x : g xM ≡ x
      gx≡x = Σ≡Prop (λ z → (z ∈ˢ P) .snd) e

      hullSide : ⟨ (xM ∷ []) ⊨ᴹ embed (coverForm φ₀) ⟩
      hullSide = fromStage el 1 (coverForm φ₀) (xM ∷ []) (sc (A.inL xM))

      inner : (b : A.SM)
            → Σ[ v ∈ A.SM ]
                ( ⟨ (v ∷ b ∷ xM ∷ []) ⊨ᴹ embed (isOrdSlot (suc zero)) ⟩
                × ( ⟨ (v ∷ b ∷ xM ∷ [])
                      ⊨ᴹ mapFo Empty.rec* (renameFo wk23 φ₀) ⟩
                  × ⟨ fst xM ∈ˢ fst v ⟩ ) )
            → Σ[ b' ∈ Cr.SP ] Σ[ v' ∈ Cr.SP ]
                (IsOrd (fst b') × Cr.Bel v' b' × ⟨ fst x ∈ˢ fst v' ⟩)
      inner b (v , (ordSat , (belSat , memSat))) = g b , g v , ord , bel , mem
        where
        ordImage : ⟨ map g (v ∷ b ∷ xM ∷ []) Cr.AbsP.⊨ᵐ
                       embed (isOrdSlot (suc zero)) ⟩
        ordImage = toImage fwd 3 (isOrdSlot (suc zero)) (v ∷ b ∷ xM ∷ []) ordSat

        ord : IsOrd (fst (g b))
        ord = OrdSlotRead.slot-out ιP (suc zero)
                (map fst (map g (v ∷ b ∷ xM ∷ [])))
                (subst ⟨_⟩
                  (Cr.AbsP.abs₀ (mapΔ₀ Empty.rec* (Δ₀-isOrdSlot (suc zero)))
                                (map g (v ∷ b ∷ xM ∷ [])))
                  ordImage)

        belRen : ⟨ (v ∷ b ∷ xM ∷ []) ⊨ᴹ renameFo wk23 (embed φ₀) ⟩
        belRen = subst (λ ψ → ⟨ (v ∷ b ∷ xM ∷ []) ⊨ᴹ ψ ⟩)
                       (mapFo-ren Empty.rec* wk23 φ₀) belSat

        belHull : ⟨ (v ∷ b ∷ []) ⊨ᴹ embed φ₀ ⟩
        belHull = subst ⟨_⟩
                    (SatM.⊨-rename wk23 (embed φ₀)
                       (v ∷ b ∷ xM ∷ []) (v ∷ b ∷ []) (agM v b xM))
                    belRen

        bel : Cr.Bel (g v) (g b)
        bel = toImage fwd 2 φ₀ (v ∷ b ∷ []) belHull

        memImage : ⟨ map g (v ∷ xM ∷ []) Cr.AbsP.⊨ᵐ embed memAtom ⟩
        memImage = toImage fwd 2 memAtom (v ∷ xM ∷ []) memSat

        mem : ⟨ fst x ∈ˢ fst (g v) ⟩
        mem = subst (λ q → ⟨ fst q ∈ˢ fst (g v) ⟩) gx≡x memImage

      outer : Σ[ b ∈ A.SM ]
                ⟨ (b ∷ xM ∷ [])
                  ⊨ᴹ (∃̇ ( embed (isOrdSlot (suc zero))
                        ∧̇ ( mapFo Empty.rec* (renameFo wk23 φ₀)
                          ∧̇ (var (suc (suc zero)) ∈̇ var zero) ) )) ⟩
            → ∥ Σ[ b ∈ Cr.SP ] Σ[ v ∈ Cr.SP ]
                  (IsOrd (fst b) × Cr.Bel v b × ⟨ fst x ∈ˢ fst v ⟩) ∥₁
      outer (b , h2) = PT.map (inner b) h2

  -- ===================================================================
  -- SECTION 6: THE WHOLE CHAIN, END TO END.
  --
  -- `levelIn` and `cover` at the collapse image, from seven inputs.
  -- FIVE ARE DELIVERED OR PRICED:
  --   el         the hull's elementarity        DELIVERED (:759, :1544)
  --   fwd, bwd   the collapse's satisfaction iso DELIVERED (:195-:318)
  --   s₁         the Sigma-1 certificate         DELIVERED shape (:145)
  --   sl, sc     the two stage facts             the priced residue
  -- ONE IS NOT:
  --   amb        Devlin (a) at the AMBIENT carrier
  -- ===================================================================

  module Whole
    (el : A.Elementary) (fwd : IsoFwd) (bwd : IsoBwd)
    (sl : StageLevels) (sc : StageCovered)
    (s₁ : Σ₁ Cr.φP)
    (amb : AmbientCross.AmbientRead P Ptr φ₀) where

    co : Cr.CrossOut
    co = AmbientCross.crossOut P Ptr φ₀ s₁ amb

    module Asm = Cr.Assembly M pi piIntro co

    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ P ⟩ → ⟨ Lset δ ∈ˢ P ⟩
    levelIn = Asm.levelIn (hasLevels el fwd bwd sl)

    cover : (y : S) → ⟨ y ∈ˢ M ⟩
          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ P ⟩ × ⟨ pi y ∈ˢ Lset γ ⟩) ∥₁
    cover = Asm.cover (covered el fwd sc)
