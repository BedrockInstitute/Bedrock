# The condensation transfer at a superadequate hull stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Condense {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Relabelling using ( mapFo; embed )
open import FOL.Manipulation.Renaming using ( renameFo; liftρ; module Sat )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans )
open import L.Constructible {ℓ} using
  ( IsOrd; isL; Lset; Lset-out; Lset-mono; Lset→isL; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.BoundedSubset {ℓ} lem using
  ( module HullStage; isOrdAt; Δ₀-isOrdAt; module Amb )
open import L.GCH.Frame {ℓ} lem using
  ( module Frame; module Unpack; module HullConvert; _⊨ₚ_
  ; embed-map; lemma; isOrd-at-p )
open import L.GCH.Level {ℓ} lem using ( levelFo; Δ₀-levelFo; level-sound )
open import L.GCH.Complete {ℓ} lem using
  ( Superadequate; Adequate; level-complete; Lset∈suc )

open import Cubical.Data.Vec using ( map; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemVᵃ using ( _^_ )

-- =====================================================================
-- SECTION 1.  RENAMING, AT THE Δ₀ CERTIFICATE AND AT THE AMBIENT
-- READING.  The level formula has its value slot first and its
-- witness slot last; `hull-closed` frees the LAST slot of a one-slot
-- formula, so the slot that must come out of the hull is moved to
-- the end by a renaming.
-- =====================================================================

Δ₀-rename : {ℓc : Level} {K : Type ℓc} {n m : ℕ} (ρ : Fin n → Fin m)
            {φ : Formula K n} → Δ₀ φ → Δ₀ (renameFo ρ φ)
Δ₀-rename ρ δ-∈ = δ-∈
Δ₀-rename ρ δ-≐ = δ-≐
Δ₀-rename ρ (δ-∧ d e) = δ-∧ (Δ₀-rename ρ d) (Δ₀-rename ρ e)
Δ₀-rename ρ (δ-∨ d e) = δ-∨ (Δ₀-rename ρ d) (Δ₀-rename ρ e)
Δ₀-rename ρ (δ-⇒ d e) = δ-⇒ (Δ₀-rename ρ d) (Δ₀-rename ρ e)
Δ₀-rename ρ (δ-¬ d) = δ-¬ (Δ₀-rename ρ d)
Δ₀-rename ρ δ-⊤ = δ-⊤
Δ₀-rename ρ δ-⊥ = δ-⊥
Δ₀-rename ρ (δ-∀∈ d) = δ-∀∈ (Δ₀-rename (liftρ ρ) d)
Δ₀-rename ρ (δ-∃∈ d) = δ-∃∈ (Δ₀-rename (liftρ ρ) d)

-- The ambient reading is `Sat` at the empty constant domain, the same
-- reading `_⊨ₚ_` names.
module RS = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = ⊥* {ℓ-suc ℓ}}
               (λ b → Empty.rec* b) using (Agrees; ⊨-rename)

-- SHAPE A: the value slot last.  The inner environment reads
-- (p ∷ z ∷ a ∷ []).
ρa : Fin 3 → Fin 3
ρa zero = suc (suc zero)
ρa (suc zero) = zero
ρa (suc (suc zero)) = suc zero

levelA : Formula (⊥* {ℓ-suc ℓ}) 3
levelA = renameFo ρa levelFo

Δ₀-levelA : Δ₀ levelA
Δ₀-levelA = Δ₀-rename ρa Δ₀-levelFo

agA : (p z a : S) → RS.Agrees ρa (p ∷ z ∷ a ∷ []) (a ∷ p ∷ z ∷ [])
agA p z a zero = refl
agA p z a (suc zero) = refl
agA p z a (suc (suc zero)) = refl

readA : (p z a : S)
      → ((p ∷ z ∷ a ∷ []) ⊨ₚ levelA) ≡ ((a ∷ p ∷ z ∷ []) ⊨ₚ levelFo)
readA p z a = RS.⊨-rename ρa levelFo (p ∷ z ∷ a ∷ []) (a ∷ p ∷ z ∷ []) (agA p z a)

-- SHAPE P: the parameter slot last.  The inner environment reads
-- (a ∷ z ∷ p ∷ []).
ρp : Fin 3 → Fin 3
ρp zero = zero
ρp (suc zero) = suc (suc zero)
ρp (suc (suc zero)) = suc zero

levelP : Formula (⊥* {ℓ-suc ℓ}) 3
levelP = renameFo ρp levelFo

Δ₀-levelP : Δ₀ levelP
Δ₀-levelP = Δ₀-rename ρp Δ₀-levelFo

agP : (a z p : S) → RS.Agrees ρp (a ∷ z ∷ p ∷ []) (a ∷ p ∷ z ∷ [])
agP a z p zero = refl
agP a z p (suc zero) = refl
agP a z p (suc (suc zero)) = refl

readP : (a z p : S)
      → ((a ∷ z ∷ p ∷ []) ⊨ₚ levelP) ≡ ((a ∷ p ∷ z ∷ []) ⊨ₚ levelFo)
readP a z p = RS.⊨-rename ρp levelFo (a ∷ z ∷ p ∷ []) (a ∷ p ∷ z ∷ []) (agP a z p)

-- The parameter conjunct of the level formula, read off.
isOrd-at-p-out : (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ isOrd-at-p ⟩ → IsOrd p
isOrd-at-p-out a p z h =
    ( λ {x₁} {y} y∈x₁ x₁∈p → h .fst x₁ x₁∈p y y∈x₁ )
  , ( λ b b∈p {x₁} {y} y∈x₁ x₁∈b → h .snd b b∈p x₁ x₁∈b y y∈x₁ )

-- =====================================================================
-- SECTION 2.  THE TWO ONE-PIN SHAPES.  Two existentials bind the first
-- two slots; one conjunct pins the parameter to a constant (shape A)
-- or asks the value to hold a constant (shape P); the last slot is
-- free, and `hull-closed` produces it.
-- =====================================================================

pinP : {ℓc : Level} {K : Type ℓc} → Formula K 3 → K → Formula K 1
pinP ψ c = ∃̇ (∃̇ (ψ ∧̇ (var zero ≐ con c)))

pinY : {ℓc : Level} {K : Type ℓc} → Formula K 3 → K → Formula K 1
pinY ψ c = ∃̇ (∃̇ (ψ ∧̇ (con c ∈̇ var zero)))

pinP-map : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd}
           (f : K → K') (ψ : Formula K 3) (c : K)
         → mapFo f (pinP ψ c) ≡ pinP (mapFo f ψ) (f c)
pinP-map f ψ c = refl

pinY-map : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd}
           (f : K → K') (ψ : Formula K 3) (c : K)
         → mapFo f (pinY ψ c) ≡ pinY (mapFo f ψ) (f c)
pinY-map f ψ c = refl

module Pin (U : S) (Utr : isTrans U) where

  module Un = Unpack U Utr using (Ab; module Ab; read)
  module Ab = Un.Ab using (SM; _⊨ᵐ_)

  unpack₂ : (ψ χ : Formula Ab.SM 3) (a : Ab.SM)
          → ⟨ (a ∷ []) Ab.⊨ᵐ (∃̇ (∃̇ (ψ ∧̇ χ))) ⟩
          → ∥ Σ[ x0 ∈ Ab.SM ] Σ[ x1 ∈ Ab.SM ]
               ( ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ ψ ⟩
               × ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ χ ⟩ ) ∥₁
  unpack₂ ψ χ a h = PT.rec squash₁ outer h
    where
    outer : Σ[ x1 ∈ Ab.SM ] ⟨ (x1 ∷ a ∷ []) Ab.⊨ᵐ (∃̇ (ψ ∧̇ χ)) ⟩
          → ∥ Σ[ x0 ∈ Ab.SM ] Σ[ x1 ∈ Ab.SM ]
               ( ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ ψ ⟩
               × ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ χ ⟩ ) ∥₁
    outer (x1 , h1) = PT.rec squash₁ inner h1
      where
      inner : Σ[ x0 ∈ Ab.SM ] ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ (ψ ∧̇ χ) ⟩
            → ∥ Σ[ x0 ∈ Ab.SM ] Σ[ x1 ∈ Ab.SM ]
                 ( ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ ψ ⟩
                 × ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ χ ⟩ ) ∥₁
      inner (x0 , h0) = ∣ x0 , x1 , h0 .fst , h0 .snd ∣₁

  -- SHAPE A, CONVERTED: a is the value, c the parameter, and the
  -- witness is bound.
  convA : (c a : Ab.SM)
        → ⟨ (a ∷ []) Ab.⊨ᵐ pinP (embed levelA) c ⟩
        → ∥ Σ[ z ∈ Ab.SM ] ⟨ (fst a ∷ fst c ∷ fst z ∷ []) ⊨ₚ levelFo ⟩ ∥₁
  convA c a h = PT.map go (unpack₂ (embed levelA) (var zero ≐ con c) a h)
    where
    go : Σ[ x0 ∈ Ab.SM ] Σ[ x1 ∈ Ab.SM ]
           ( ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ embed levelA ⟩ × (fst x0 ≡ fst c) )
       → Σ[ z ∈ Ab.SM ] ⟨ (fst a ∷ fst c ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
    go (x0 , x1 , hψ , e) =
      x1 , subst (λ p → ⟨ (fst a ∷ p ∷ fst x1 ∷ []) ⊨ₚ levelFo ⟩) e
             (subst ⟨_⟩ (readA (fst x0) (fst x1) (fst a))
               (subst ⟨_⟩ (Un.read Δ₀-levelA (x0 ∷ x1 ∷ a ∷ [])) hψ))

  -- SHAPE P, CONVERTED: a is the parameter, the value holds c, and
  -- the witness is bound.
  convP : (c a : Ab.SM)
        → ⟨ (a ∷ []) Ab.⊨ᵐ pinY (embed levelP) c ⟩
        → ∥ Σ[ u ∈ Ab.SM ] Σ[ z ∈ Ab.SM ]
             ( ⟨ (fst u ∷ fst a ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
             × ⟨ fst c ∈ˢ fst u ⟩ ) ∥₁
  convP c a h = PT.map go (unpack₂ (embed levelP) (con c ∈̇ var zero) a h)
    where
    go : Σ[ x0 ∈ Ab.SM ] Σ[ x1 ∈ Ab.SM ]
           ( ⟨ (x0 ∷ x1 ∷ a ∷ []) Ab.⊨ᵐ embed levelP ⟩ × ⟨ fst c ∈ˢ fst x0 ⟩ )
       → Σ[ u ∈ Ab.SM ] Σ[ z ∈ Ab.SM ]
           ( ⟨ (fst u ∷ fst a ∷ fst z ∷ []) ⊨ₚ levelFo ⟩ × ⟨ fst c ∈ˢ fst u ⟩ )
    go (x0 , x1 , hψ , m) =
      x0 , x1
      , subst ⟨_⟩ (readP (fst x0) (fst x1) (fst a))
          (subst ⟨_⟩ (Un.read Δ₀-levelP (x0 ∷ x1 ∷ a ∷ [])) hψ)
      , m

-- =====================================================================
-- SECTION 3.  THE TRANSFER.  One hull stage at `HullStage`'s telescope,
-- elementary (`elem`), superadequate (`sup`), and with its collapse
-- image inside L (`pixL`).  `pixL` is NOT derived here: the tree's
-- `pix-in-L` (src/L/GCH/Stages.lagda.md) takes `Site.Cover`, which is
-- `cover` itself, and `level-sound` (src/L/GCH/Level.lagda.md) reads
-- its three slots in L, so the collapse values must be known in L
-- before the level formula is sound at them.
-- =====================================================================

module Condense (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
  (sup : Superadequate lam)
  (pixL : (x : S) → ⟨ x ∈ˢ HullStage.C.πX lam ordλ succλ X X⊆L ∅∈λ ⟩
        → ⟨ isL x ⟩)
  where

  module F = Frame lam ordλ succλ X X⊆L ∅∈λ using (module A; module Carry; module HS)
  module HS = F.HS using (module ASt; module C; module Condense; module H; M)
  module Cy = F.Carry elem using (module CIso; at; atM; atπ; push)
  module P = Pin (Lset lam) HS.ASt.Ltr using (module Un; convA; convP)
  module HC = HullConvert (Lset lam) HS.ASt.Ltr using (hull-convert; inBound)

  open HS.H.T using ( Code; val )
  open HS.H using ( hull-closed; hull-member; Hull⊆L )

  M : S
  M = HS.M

  π : S → S
  π = HS.C.π

  slide : ⊥* {ℓ-suc ℓ} → Code
  slide b = Empty.rec* b

  -- The three lifted formulas over the stage carrier, each equal to
  -- its embedding.
  LA : Formula HS.ASt.SL 3
  LA = mapFo val (mapFo slide levelA)

  eqA : LA ≡ embed levelA
  eqA = lemma levelA slide val

  LP : Formula HS.ASt.SL 3
  LP = mapFo val (mapFo slide levelP)

  eqP : LP ≡ embed levelP
  eqP = lemma levelP slide val

  LF : Formula HS.ASt.SL 3
  LF = mapFo val (mapFo slide levelFo)

  eqF : LF ≡ embed levelFo
  eqF = lemma levelFo slide val

  -- Stage memberships.
  isLλ : (x : S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ isL x ⟩
  isLλ = Lset→isL lam ordλ

  Lset∈Lλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ Lset d ∈ˢ Lset lam ⟩
  Lset∈Lλ d d∈λ = Lset-mono {α = lam} {β = sucV d} (succλ d d∈λ) (Lset∈suc d)

  ord∈Lλ : (d : S) → IsOrd d → ⟨ d ∈ˢ lam ⟩ → ⟨ d ∈ˢ Lset lam ⟩
  ord∈Lλ d od d∈λ =
    Lset-mono {α = lam} {β = sucV d} (succλ d d∈λ) (ord∈Lset-suc d od)

  -- THE PULL: the mirror of `Carry.push`, by `iso-inv-bwd`.
  pull : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : F.A.SM ^ n)
       → ⟨ map fst (map Cy.CIso.I.g δ) ⊨ₚ φ ⟩
       → ⟨ map fst δ ⊨ₚ φ ⟩
  pull {n} {φ} dφ δ h =
    subst ⟨_⟩ (Cy.atM dφ δ)
      (Cy.CIso.I.iso-inv-bwd n (embed φ) δ
        (subst (λ ψ → ⟨ map Cy.CIso.I.g δ Cy.CIso.I.⊨ᵖᵐ ψ ⟩)
               (sym (embed-map Cy.CIso.I.g φ))
               (subst ⟨_⟩ (sym (Cy.atπ dφ (map Cy.CIso.I.g δ))) h)))

  -- Ordinality crosses the collapse in both directions.
  ord-push : (d : S) (d∈M : ⟨ d ∈ˢ M ⟩) → IsOrd d → IsOrd (π d)
  ord-push d d∈M od =
    Amb.isOrdAt-out (π d)
      (Cy.push Δ₀-isOrdAt ((d , d∈M) ∷ []) (Amb.isOrdAt-in d od))

  ord-pull : (d : S) (d∈M : ⟨ d ∈ˢ M ⟩) → IsOrd (π d) → IsOrd d
  ord-pull d d∈M oπd =
    Amb.isOrdAt-out d
      (pull Δ₀-isOrdAt ((d , d∈M) ∷ []) (Amb.isOrdAt-in (π d) oπd))

  -- THE STAGE EXISTENTIALS, from `level-complete` at an adequate
  -- stage.  Shape A at the parameter's code.
  stageA : (d γ : S) (od : IsOrd d) (adγ : Adequate γ) (d∈γ : ⟨ d ∈ˢ γ ⟩)
         → (cd : Code) → fst (val cd) ≡ d
         → ⟨ d ∈ˢ Lset lam ⟩ → ⟨ Lset d ∈ˢ Lset lam ⟩ → ⟨ Lset γ ∈ˢ Lset lam ⟩
         → ⟨ [] HS.ASt.AbsL.⊨ᵐ (∃̇ (mapFo val (pinP (mapFo slide levelA) cd))) ⟩
  stageA d γ od adγ d∈γ cd ed d∈ Ld∈ Lγ∈ =
    ∣ (Lset d , Ld∈) , ∣ (Lset γ , Lγ∈) , ∣ (d , d∈) , (sat , sym ed) ∣₁ ∣₁ ∣₁
    where
    δ : HS.ASt.SL ^ 3
    δ = (d , d∈) ∷ (Lset γ , Lγ∈) ∷ (Lset d , Ld∈) ∷ []

    amb : ⟨ (d ∷ Lset γ ∷ Lset d ∷ []) ⊨ₚ levelA ⟩
    amb = subst ⟨_⟩ (sym (readA d (Lset γ) (Lset d)))
            (level-complete γ adγ d od d∈γ)

    sat : ⟨ δ HS.ASt.AbsL.⊨ᵐ LA ⟩
    sat = subst (λ ψ → ⟨ δ HS.ASt.AbsL.⊨ᵐ ψ ⟩) (sym eqA)
            (subst ⟨_⟩ (sym (P.Un.read Δ₀-levelA δ)) amb)

  -- Shape P at the member's code.
  stageP : (y p γ : S) (op : IsOrd p) (adγ : Adequate γ) (p∈γ : ⟨ p ∈ˢ γ ⟩)
         → (cy : Code) → fst (val cy) ≡ y → ⟨ y ∈ˢ Lset p ⟩
         → ⟨ p ∈ˢ Lset lam ⟩ → ⟨ Lset p ∈ˢ Lset lam ⟩ → ⟨ Lset γ ∈ˢ Lset lam ⟩
         → ⟨ [] HS.ASt.AbsL.⊨ᵐ (∃̇ (mapFo val (pinY (mapFo slide levelP) cy))) ⟩
  stageP y p γ op adγ p∈γ cy ey y∈Lp p∈ Lp∈ Lγ∈ =
    ∣ (p , p∈) , ∣ (Lset γ , Lγ∈) , ∣ (Lset p , Lp∈) , (sat , mem) ∣₁ ∣₁ ∣₁
    where
    δ : HS.ASt.SL ^ 3
    δ = (Lset p , Lp∈) ∷ (Lset γ , Lγ∈) ∷ (p , p∈) ∷ []

    amb : ⟨ (Lset p ∷ Lset γ ∷ p ∷ []) ⊨ₚ levelP ⟩
    amb = subst ⟨_⟩ (sym (readP (Lset p) (Lset γ) p))
            (level-complete γ adγ p op p∈γ)

    sat : ⟨ δ HS.ASt.AbsL.⊨ᵐ LP ⟩
    sat = subst (λ ψ → ⟨ δ HS.ASt.AbsL.⊨ᵐ ψ ⟩) (sym eqP)
            (subst ⟨_⟩ (sym (P.Un.read Δ₀-levelP δ)) amb)

    mem : ⟨ fst (val cy) ∈ˢ Lset p ⟩
    mem = subst (λ w → ⟨ w ∈ˢ Lset p ⟩) (sym ey) y∈Lp

  -- Devlin's own shape, both the value and the parameter pinned, the
  -- witness free (`HullConvert.inBound`).
  stageF : (d γ : S) (od : IsOrd d) (adγ : Adequate γ) (d∈γ : ⟨ d ∈ˢ γ ⟩)
         → (ca cd : Code) → fst (val ca) ≡ Lset d → fst (val cd) ≡ d
         → ⟨ d ∈ˢ Lset lam ⟩ → ⟨ Lset d ∈ˢ Lset lam ⟩ → ⟨ Lset γ ∈ˢ Lset lam ⟩
         → ⟨ [] HS.ASt.AbsL.⊨ᵐ (∃̇ (mapFo val (HC.inBound levelFo slide ca cd))) ⟩
  stageF d γ od adγ d∈γ ca cd ea ed d∈ Ld∈ Lγ∈ =
    ∣ (Lset γ , Lγ∈) , ∣ (d , d∈) , ∣ (Lset d , Ld∈) , (sat , (sym ea , sym ed)) ∣₁ ∣₁ ∣₁
    where
    δ : HS.ASt.SL ^ 3
    δ = (Lset d , Ld∈) ∷ (d , d∈) ∷ (Lset γ , Lγ∈) ∷ []

    sat : ⟨ δ HS.ASt.AbsL.⊨ᵐ LF ⟩
    sat = subst (λ ψ → ⟨ δ HS.ASt.AbsL.⊨ᵐ ψ ⟩) (sym eqF)
            (subst ⟨_⟩ (sym (P.Un.read Δ₀-levelFo δ))
              (level-complete γ adγ d od d∈γ))

  -- The conversion at Devlin's shape, its codomain inferred (the
  -- measured-green shape of src/L/GCH/Frame.lagda.md `Build.conv0`).
  convF : (ca cd : Code) (a : HS.ASt.SL)
        → ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ (mapFo val (HC.inBound levelFo slide ca cd)) ⟩
        → _
  convF = HC.hull-convert {φ = levelFo} Δ₀-levelFo slide val eqF

  -- =====================================================================
  -- THE WITNESS.  At an ordinal of the hull: its level is in the hull,
  -- and a hull witness reads the level formula at (Lset d, d, z).
  -- =====================================================================

  Witness : S → Type (ℓ-suc ℓ)
  Witness d = ∥ Σ[ z ∈ S ] ( ⟨ z ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                           × ⟨ (Lset d ∷ d ∷ z ∷ []) ⊨ₚ levelFo ⟩ ) ∥₁

  witness : (d : S) → IsOrd d → ⟨ d ∈ˢ M ⟩ → Witness d
  witness d od d∈M = PT.rec squash₁ step1 (sup d d∈λ)
    where
    d∈Lλ : ⟨ d ∈ˢ Lset lam ⟩
    d∈Lλ = Hull⊆L d d∈M

    d∈λ : ⟨ d ∈ˢ lam ⟩
    d∈λ = ord∈Lset→∈ lam ordλ d od d∈Lλ

    Ld∈Lλ : ⟨ Lset d ∈ˢ Lset lam ⟩
    Ld∈Lλ = Lset∈Lλ d d∈λ

    step1 : Σ[ γ ∈ S ] (⟨ γ ∈ˢ lam ⟩ × ⟨ d ∈ˢ γ ⟩ × Adequate γ) → Witness d
    step1 (γ , γ∈λ , d∈γ , adγ) = PT.rec squash₁ step2 (hull-member d d∈M)
      where
      Lγ∈Lλ : ⟨ Lset γ ∈ˢ Lset lam ⟩
      Lγ∈Lλ = Lset∈Lλ γ γ∈λ

      step2 : Σ[ cd ∈ Code ] (fst (val cd) ≡ d) → Witness d
      step2 (cd , ed) =
        PT.rec squash₁ step3
          (hull-closed (pinP (mapFo slide levelA) cd)
            (stageA d γ od adγ d∈γ cd ed d∈Lλ Ld∈Lλ Lγ∈Lλ))
        where
        step3 : Σ[ a ∈ HS.ASt.SL ]
                  ( ⟨ fst a ∈ˢ M ⟩
                  × ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ
                        (mapFo val (pinP (mapFo slide levelA) cd)) ⟩ )
              → Witness d
        step3 (a , a∈M , sat) = PT.rec squash₁ step4 (P.convA (val cd) a sat')
          where
          sat' : ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ pinP (embed levelA) (val cd) ⟩
          sat' = subst (λ ψ → ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ pinP ψ (val cd) ⟩) eqA
                   (subst (λ ψ → ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ ψ ⟩)
                          (pinP-map val (mapFo slide levelA) cd) sat)

          step4 : Σ[ z ∈ HS.ASt.SL ]
                    ⟨ (fst a ∷ fst (val cd) ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
                → Witness d
          step4 (z , amb) = PT.rec squash₁ step5 (hull-member (Lset d) Ld∈M)
            where
            a≡ : fst a ≡ Lset (fst (val cd))
            a≡ = level-sound (fst a) (fst (val cd)) (fst z)
                   (isLλ (fst a) (snd a)) (isLλ (fst (val cd)) (snd (val cd)))
                   (isLλ (fst z) (snd z)) amb

            Ld∈M : ⟨ Lset d ∈ˢ M ⟩
            Ld∈M = subst (λ w → ⟨ w ∈ˢ M ⟩) (a≡ ∙ cong Lset ed) a∈M

            step5 : Σ[ ca ∈ Code ] (fst (val ca) ≡ Lset d) → Witness d
            step5 (ca , ea) =
              PT.map step6
                (hull-closed (HC.inBound levelFo slide ca cd)
                  (stageF d γ od adγ d∈γ ca cd ea ed d∈Lλ Ld∈Lλ Lγ∈Lλ))
              where
              step6 : Σ[ w ∈ HS.ASt.SL ]
                        ( ⟨ fst w ∈ˢ M ⟩
                        × ⟨ (w ∷ []) HS.ASt.AbsL.⊨ᵐ
                              (mapFo val (HC.inBound levelFo slide ca cd)) ⟩ )
                    → Σ[ z ∈ S ] ( ⟨ z ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                                 × ⟨ (Lset d ∷ d ∷ z ∷ []) ⊨ₚ levelFo ⟩ )
              step6 (w , w∈M , satw) =
                fst w , w∈M , Ld∈M
                , subst (λ v → ⟨ (v ∷ d ∷ fst w ∷ []) ⊨ₚ levelFo ⟩) ea
                    (subst (λ p → ⟨ (fst (val ca) ∷ p ∷ fst w ∷ []) ⊨ₚ levelFo ⟩) ed
                      (convF ca cd w satw))

  -- THE COMMUTATION.  The collapse of the level at a hull ordinal is
  -- the level at the collapsed ordinal; `pixL` places the pushed
  -- triple in L for `level-sound`.
  commute : (d : S) → IsOrd d → (d∈M : ⟨ d ∈ˢ M ⟩)
          → ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
  commute d od d∈M =
    PT.rec (isProp× (snd (Lset d ∈ˢ M)) (isSetS (π (Lset d)) (Lset (π d))))
           go (witness d od d∈M)
    where
    go : Σ[ z ∈ S ] ( ⟨ z ∈ˢ M ⟩ × ⟨ Lset d ∈ˢ M ⟩
                    × ⟨ (Lset d ∷ d ∷ z ∷ []) ⊨ₚ levelFo ⟩ )
       → ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
    go (z , z∈M , Ld∈M , amb) = Ld∈M , eq
      where
      pushed : ⟨ (π (Lset d) ∷ π d ∷ π z ∷ []) ⊨ₚ levelFo ⟩
      pushed = Cy.push Δ₀-levelFo ((Lset d , Ld∈M) ∷ (d , d∈M) ∷ (z , z∈M) ∷ []) amb

      eq : π (Lset d) ≡ Lset (π d)
      eq = level-sound (π (Lset d)) (π d) (π z)
             (pixL (π (Lset d)) (HS.C.πX-intro (Lset d) Ld∈M))
             (pixL (π d) (HS.C.πX-intro d d∈M))
             (pixL (π z) (HS.C.πX-intro z z∈M))
             pushed

  -- =====================================================================
  -- THE TWO HYPOTHESES OF `HullStage.Condense`.
  -- =====================================================================

  levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩
  levelIn δ oδ δ∈πX =
    PT.rec (snd (Lset δ ∈ˢ HS.C.πX)) go (HS.C.πX-member δ δ∈πX)
    where
    go : Σ[ d ∈ S ] (⟨ d ∈ˢ M ⟩ × (π d ≡ δ)) → ⟨ Lset δ ∈ˢ HS.C.πX ⟩
    go (d , d∈M , e) =
      subst (λ w → ⟨ w ∈ˢ HS.C.πX ⟩) (cm .snd ∙ cong Lset e)
            (HS.C.πX-intro (Lset d) (cm .fst))
      where
      od : IsOrd d
      od = ord-pull d d∈M (subst IsOrd (sym e) oδ)

      cm : ⟨ Lset d ∈ˢ M ⟩ × (π (Lset d) ≡ Lset (π d))
      cm = commute d od d∈M

  cover : (y : S) → ⟨ y ∈ˢ M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁
  cover y y∈M = PT.rec squash₁ go (Lset-out lam y (Hull⊆L y y∈M))
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁

    go : Σ[ c ∈ S ] (⟨ c ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset c) ⟩) → Goal
    go (c , c∈λ , y∈D) = PT.rec squash₁ go₂ (sup p p∈λ)
      where
      p : S
      p = sucV c

      p∈λ : ⟨ p ∈ˢ lam ⟩
      p∈λ = succλ c c∈λ

      op : IsOrd p
      op = suc-ord (mem-ord {A = lam} ordλ c c∈λ)

      y∈Lp : ⟨ y ∈ˢ Lset p ⟩
      y∈Lp = subst (λ w → ⟨ y ∈ˢ w ⟩) (sym (Lset-suc c)) y∈D

      go₂ : Σ[ γ ∈ S ] (⟨ γ ∈ˢ lam ⟩ × ⟨ p ∈ˢ γ ⟩ × Adequate γ) → Goal
      go₂ (γ , γ∈λ , p∈γ , adγ) = PT.rec squash₁ go₃ (hull-member y y∈M)
        where
        go₃ : Σ[ cy ∈ Code ] (fst (val cy) ≡ y) → Goal
        go₃ (cy , ey) =
          PT.rec squash₁ go₄
            (hull-closed (pinY (mapFo slide levelP) cy)
              (stageP y p γ op adγ p∈γ cy ey y∈Lp
                (ord∈Lλ p op p∈λ) (Lset∈Lλ p p∈λ) (Lset∈Lλ γ γ∈λ)))
          where
          go₄ : Σ[ a ∈ HS.ASt.SL ]
                  ( ⟨ fst a ∈ˢ M ⟩
                  × ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ
                        (mapFo val (pinY (mapFo slide levelP) cy)) ⟩ )
              → Goal
          go₄ (a , a∈M , sat) = PT.rec squash₁ go₅ (P.convP (val cy) a sat')
            where
            sat' : ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ pinY (embed levelP) (val cy) ⟩
            sat' = subst (λ ψ → ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ pinY ψ (val cy) ⟩) eqP
                     (subst (λ ψ → ⟨ (a ∷ []) HS.ASt.AbsL.⊨ᵐ ψ ⟩)
                            (pinY-map val (mapFo slide levelP) cy) sat)

            go₅ : Σ[ u ∈ HS.ASt.SL ] Σ[ z ∈ HS.ASt.SL ]
                    ( ⟨ (fst u ∷ fst a ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
                    × ⟨ fst (val cy) ∈ˢ fst u ⟩ )
                → Goal
            go₅ (u , z , amb , y'∈u) =
              ∣ π p′ , ord-push p′ a∈M op′ , HS.C.πX-intro p′ a∈M , πy∈ ∣₁
              where
              p′ : S
              p′ = fst a

              op′ : IsOrd p′
              op′ = isOrd-at-p-out (fst u) p′ (fst z) (amb .fst)

              u≡ : fst u ≡ Lset p′
              u≡ = level-sound (fst u) p′ (fst z)
                     (isLλ (fst u) (snd u)) (isLλ p′ (snd a)) (isLλ (fst z) (snd z))
                     amb

              y∈Lp′ : ⟨ y ∈ˢ Lset p′ ⟩
              y∈Lp′ = subst (λ v → ⟨ y ∈ˢ v ⟩) u≡
                        (subst (λ w → ⟨ w ∈ˢ fst u ⟩) ey y'∈u)

              cm : ⟨ Lset p′ ∈ˢ M ⟩ × (π (Lset p′) ≡ Lset (π p′))
              cm = commute p′ op′ a∈M

              πy∈ : ⟨ π y ∈ˢ Lset (π p′) ⟩
              πy∈ = subst (λ w → ⟨ π y ∈ˢ w ⟩) (cm .snd)
                      (Cy.CIso.iso-fwd (Lset p′) y (cm .fst) y∈M y∈Lp′)

  -- =====================================================================
  -- THE THEOREM.  The collapse of the hull is a level.
  -- =====================================================================

  module Cn = HS.Condense levelIn cover using (condenses)

  condenses : Σ[ β ∈ S ] (IsOrd β × (HS.C.πX ≡ Lset β))
  condenses = Cn.condenses
```
