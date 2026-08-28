{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.741] PROBE.  defSet-in-carrier-lim:  the definable subset fill
-- pins to z sits in the carrier's stage, under closedomega gamma.
-- Lands nothing in src/.
--
--   DELIVERED   defSet-in-carrier-lim, INHABITED.  The route is the
--               carrier-to-stage definability transfer, built fresh
--               here (nothing landed compares the carrier's inner
--               semantics with any stage reading for a NON-Delta0
--               carrier formula; the Bridge chapter's own prose names
--               exactly this as what it does NOT say):
--               relativize the carrier formula to the stage alphabet,
--               bounding every quantifier by the fiber of the carrier
--               and guarding the bounded ones too (the double guard
--               the Bridge prose warns about), transfer satisfaction
--               by induction on the formula, turn the transfer into
--               one extensional equation between the stage carve and
--               DefOf.defSet, then D-o-intro + Lset-suc + closedomega
--               absorb.  The transfer is stated as a PAIR of
--               functions, not as a path of truth values: the path
--               form made the elaborator unify the two reduced Omega
--               terms whole and that is the wall this shape routes
--               around.  No omega hypothesis is needed; the wide
--               alphabet is never entered, so the 736 defect does not
--               apply.
--   NOT HERE    Sat-in-carrier-lim (736, priced FALSE there), the
--               Sat-at-asConst bound (the unruled neighbour), and the
--               landed unbounded fill are not stated, not inhabited,
--               and no postulate stands under them.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and never touched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-741.Probe741 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( Transitive; module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∃∈; δ-∀∈ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono; Lset-out
        ; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.StageArith {ℓ} lem using ( +ω; +ω-iter; closedω )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )

open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Vec using ( Vec; []; _∷_; lookup )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr; map )
open import Cubical.Foundations.Equiv using ( invEq )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
-- The brief's hypothesis glyph (A : S) reads at the L structure, whose
-- carrier pairs a set with its constructibility; everything below
-- works on the underlying raw sets, so only S is taken here.
open hPropStructure 𝒮ʟ using ( S )
open hPropStructure 𝒮ᵥ using () renaming ( _≈ˢ_ to _≈ˢᵥ_ )

-- Environments: vectors, the book's `S ^ n` glyph, defined locally
-- (the FOL.Semantics one is raised over that module's parameters).
infixl 30 _^_
_^_ : ∀ {ℓ''} → Type ℓ'' → ℕ → Type ℓ''
A ^ n = Vec A n

-- =====================================================================
-- THE TRANSFER, AT ONE CARRIER AND ONE TRANSITIVE STAGE HOLDING IT.
-- =====================================================================

module Carrier (a : V ℓ) (σ : V ℓ) (oσ : IsOrd σ) (a∈σ : ⟨ a ∈ Lset σ ⟩) where
  module DA = DefOf a
  module DS = DefOf (Lset σ)

  DA-in : (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ a ⟩
  DA-in m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

  Atr : Transitive 𝒮ᵥ DS.M
  Atr = layer-trans (Lset-layer σ)

  -- The fiber of a carrier member in the stage.
  κ : ⟪ a ⟫ → ⟪ Lset σ ⟫
  κ m = ∈-asFiber {a = ⟪ a ⟫↪ m} {b = Lset σ} (Atr (DA-in m) a∈σ) .fst

  κEq : (m : ⟪ a ⟫) → ⟪ Lset σ ⟫↪ (κ m) ≡ ⟪ a ⟫↪ m
  κEq m = ∈-asFiber {a = ⟪ a ⟫↪ m} {b = Lset σ} (Atr (DA-in m) a∈σ) .snd

  -- The fiber of the carrier itself in the stage: the bound constant.
  mA : ⟪ Lset σ ⟫
  mA = ∈-asFiber {a = a} {b = Lset σ} a∈σ .fst

  mAEq : ⟪ Lset σ ⟫↪ mA ≡ a
  mAEq = ∈-asFiber {a = a} {b = Lset σ} a∈σ .snd

  -- Environment entries: a member of a sits in the transitive stage.
  repack : DA.SM → DS.SM
  repack p = fst p , Atr (snd p) a∈σ

  repV : ∀ {n} → DA.SM ^ n → DS.SM ^ n
  repV [] = []
  repV (x ∷ δ) = repack x ∷ repV δ

  rep-fst : ∀ {n} (i : Fin n) (δ : DA.SM ^ n)
          → fst (lookup i (repV δ)) ≡ fst (lookup i δ)
  rep-fst zero (x ∷ δ) = refl
  rep-fst (suc i) (x ∷ δ) = rep-fst i δ

  -- Constants and variables evaluate to the same raw set on both
  -- sides: the fiber names the member back, the entry repacks to
  -- itself.
  tm-fst : ∀ {n} (t : Term ⟪ a ⟫ n) (δ : DA.SM ^ n)
         → fst (DS.⟦ mapTm κ t ⟧ᵐ (repV δ)) ≡ fst (DA.⟦ t ⟧ᵐ δ)
  tm-fst (con m) δ = κEq m
  tm-fst (var i) δ = rep-fst i δ

  -- The bounded-quantifier guard reads its bound term one variable
  -- up (the new var 0 is the bound one), so the term shifts arity.
  tmSuc : ∀ {n} → Term ⟪ a ⟫ n → Term ⟪ Lset σ ⟫ (suc n)
  tmSuc (con m) = con (κ m)
  tmSuc (var i) = var (suc i)

  tm-fst1 : ∀ {n} (t : Term ⟪ a ⟫ n) (x : DS.SM) (δ : DA.SM ^ n)
          → fst (DS.⟦ tmSuc t ⟧ᵐ (x ∷ repV δ)) ≡ fst (DA.⟦ t ⟧ᵐ δ)
  tm-fst1 (con m) x δ = κEq m
  tm-fst1 (var i) x δ = rep-fst i δ

  -- THE RELATIVIZED IMAGE.  Atoms pass through mapFo kappa; the
  -- unbounded quantifiers are bounded by the carrier's fiber; the
  -- bounded quantifiers keep their bound AND gain the carrier guard,
  -- the double guard the inner semantics reads (Bridge chapter, the
  -- clause on what the bridge does not say).
  cnd : ∀ {n} → Formula ⟪ a ⟫ n → Formula ⟪ Lset σ ⟫ n
  cnd (t ∈̇ u)  = mapFo κ (t ∈̇ u)
  cnd (t ≐ u)  = mapFo κ (t ≐ u)
  cnd (φ ∧̇ χ)  = cnd φ ∧̇ cnd χ
  cnd (φ ∨̇ χ)  = cnd φ ∨̇ cnd χ
  cnd (φ ⇒̇ χ)  = cnd φ ⇒̇ cnd χ
  cnd (¬̇ φ)    = ¬̇ cnd φ
  cnd ⊤̇        = ⊤̇
  cnd ⊥̇        = ⊥̇
  cnd (∃̇ φ)    = ∃̇∈ (con mA) (cnd φ)
  cnd (∀̇ φ)    = ∀̇∈ (con mA) (cnd φ)
  cnd (∀̇∈ t φ) = ∀̇∈ (con mA) (var zero ∈̇ tmSuc t ⇒̇ cnd φ)
  cnd (∃̇∈ t φ) = ∃̇∈ (con mA) (var zero ∈̇ tmSuc t ∧̇ cnd φ)

  Δ₀-cnd : ∀ {n} (ψ : Formula ⟪ a ⟫ n) → Δ₀ (cnd ψ)
  Δ₀-cnd (t ∈̇ u)  = δ-∈
  Δ₀-cnd (t ≐ u)  = δ-≐
  Δ₀-cnd (φ ∧̇ χ)  = δ-∧ (Δ₀-cnd φ) (Δ₀-cnd χ)
  Δ₀-cnd (φ ∨̇ χ)  = δ-∨ (Δ₀-cnd φ) (Δ₀-cnd χ)
  Δ₀-cnd (φ ⇒̇ χ)  = δ-⇒ (Δ₀-cnd φ) (Δ₀-cnd χ)
  Δ₀-cnd (¬̇ φ)    = δ-¬ (Δ₀-cnd φ)
  Δ₀-cnd ⊤̇        = δ-⊤
  Δ₀-cnd ⊥̇        = δ-⊥
  Δ₀-cnd (∃̇ φ)    = δ-∃∈ (Δ₀-cnd φ)
  Δ₀-cnd (∀̇ φ)    = δ-∀∈ (Δ₀-cnd φ)
  Δ₀-cnd (∀̇∈ t φ) = δ-∀∈ (δ-⇒ δ-∈ (Δ₀-cnd φ))
  Δ₀-cnd (∃̇∈ t φ) = δ-∃∈ (δ-∧ δ-∈ (Δ₀-cnd φ))

  bnd : Formula ⟪ a ⟫ 1 → Formula ⟪ Lset σ ⟫ 1
  bnd ψ = (var zero ∈̇ con mA) ∧̇ cnd ψ

  Δ₀-bnd : (ψ : Formula ⟪ a ⟫ 1) → Δ₀ (bnd ψ)
  Δ₀-bnd ψ = δ-∧ δ-∈ (Δ₀-cnd ψ)

  -- THE TRANSFER.  Satisfaction of psi over the carrier's inner
  -- world transfers to satisfaction of its relativized image over
  -- the stage's inner world, at environments that agree on raw
  -- sets.  Stated as two functions, not as a path of truth values:
  -- the path form made the elaborator unify the two reduced Omega
  -- terms whole and that is the wall this shape routes around.
  sat≈ : ∀ {n} (ψ : Formula ⟪ a ⟫ n) (δ : DA.SM ^ n)
       → (⟨ (δ DA.⊨ᵐ ψ) ⟩
           → ⟨ (repV δ) DS.⊨ᵐ (cnd ψ) ⟩)
       × (⟨ (repV δ) DS.⊨ᵐ (cnd ψ) ⟩
           → ⟨ (δ DA.⊨ᵐ ψ) ⟩)
  sat≈ (t ∈̇ u) δ =
    ( λ h →
        subst (λ W → ⟨ fst (DS.⟦ mapTm κ t ⟧ᵐ (repV δ)) ∈ W ⟩)
          (sym (tm-fst u δ))
          (subst (λ W → ⟨ W ∈ fst (DA.⟦ u ⟧ᵐ δ) ⟩)
            (sym (tm-fst t δ)) h) )
    , ( λ h →
        subst (λ W → ⟨ W ∈ fst (DA.⟦ u ⟧ᵐ δ) ⟩)
          (tm-fst t δ)
          (subst (λ W → ⟨ fst (DS.⟦ mapTm κ t ⟧ᵐ (repV δ)) ∈ W ⟩)
            (tm-fst u δ) h) )
  sat≈ (t ≐ u) δ =
    ( λ h → tm-fst t δ ∙ h ∙ sym (tm-fst u δ) )
    , ( λ h → sym (tm-fst t δ) ∙ h ∙ tm-fst u δ )
  sat≈ (φ ∧̇ χ) δ =
    ( λ { (h , h′) → sat≈ φ δ .fst h , sat≈ χ δ .fst h′ } )
    , ( λ { (h , h′) → sat≈ φ δ .snd h , sat≈ χ δ .snd h′ } )
  sat≈ (φ ∨̇ χ) δ =
    ( PT.map (map (sat≈ φ δ .fst) (sat≈ χ δ .fst)) )
    , ( PT.map (map (sat≈ φ δ .snd) (sat≈ χ δ .snd)) )
  sat≈ (φ ⇒̇ χ) δ =
    ( λ f → sat≈ χ δ .fst ∘ f ∘ sat≈ φ δ .snd )
    , ( λ f → sat≈ χ δ .snd ∘ f ∘ sat≈ φ δ .fst )
  sat≈ (¬̇ φ)    δ =
    ( λ f → f ∘ sat≈ φ δ .snd )
    , ( λ f → f ∘ sat≈ φ δ .fst )
  sat≈ ⊤̇       δ = (λ _ → tt*) , (λ h → h)
  sat≈ ⊥̇       δ = (λ h → h) , (λ h → h)
  sat≈ (∃̇ φ)   δ =
    ( PT.map λ { (xm , hxm) →
        repack xm
        , ( subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm)
          , sat≈ φ (xm ∷ δ) .fst hxm ) } )
    , ( PT.map λ { (x , (gx , hx)) →
        ( fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx )
        , ( sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .snd
              (subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
                (sym (cong (λ E → E ∷ repV δ)
                  (Σ≡Prop (λ y → snd (DS.M y)) refl)))
                hx) ) } )
  sat≈ (∀̇ φ)   δ =
    ( λ f x gx →
        subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
          (cong (λ E → E ∷ repV δ) (Σ≡Prop (λ y → snd (DS.M y)) refl))
          (sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .fst
            (f (fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx))) )
    , ( λ f xm →
        sat≈ φ (xm ∷ δ) .snd
          (f (repack xm) (subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm))) )
  sat≈ (∃̇∈ t φ) δ =
    ( PT.map λ { (xm , (g , hxm)) →
        repack xm
        , ( subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm)
          , ( subst (λ W → ⟨ fst xm ∈ W ⟩) (sym (tm-fst1 t (repack xm) δ)) g
            , sat≈ φ (xm ∷ δ) .fst hxm ) ) } )
    , ( PT.map λ { (x , (gx , (g , hx))) →
        ( fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx )
        , ( subst (λ W → ⟨ fst x ∈ W ⟩) (tm-fst1 t x δ) g
          , sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .snd
              (subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
                (sym (cong (λ E → E ∷ repV δ)
                  (Σ≡Prop (λ y → snd (DS.M y)) refl)))
                hx) ) } )
  sat≈ (∀̇∈ t φ) δ =
    ( λ f x gx g →
        subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
          (cong (λ E → E ∷ repV δ) (Σ≡Prop (λ y → snd (DS.M y)) refl))
          (sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .fst
            (f (fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx)
              (subst (λ W → ⟨ fst x ∈ W ⟩) (tm-fst1 t x δ) g))) )
    , ( λ f xm g →
        sat≈ φ (xm ∷ δ) .snd
          (f (repack xm) (subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm))
            (subst (λ W → ⟨ fst xm ∈ W ⟩) (sym (tm-fst1 t (repack xm) δ)) g)) )

  -- One environment entry, two namings: the repacked carrier entry
  -- and the stage fiber of the same member.
  repκ : (m : ⟪ a ⟫) → repack (DA.ι m) ≡ DS.ι (κ m)
  repκ m = Σ≡Prop (λ y → snd (DS.M y)) (sym (κEq m))

  -- THE TWO CARVES ARE ONE SET.
  bnd≡ : (ψ : Formula ⟪ a ⟫ 1) → DS.defSet (bnd ψ) ≡ DA.defSet ψ
  bnd≡ ψ = extensionality (DS.defSet (bnd ψ)) (DA.defSet ψ) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DS.defSet (bnd ψ) ⊆ DA.defSet ψ ⟩
    sub₁ y y∈ =
      ∈∈ₛ {a = y} {b = DA.defSet ψ} .fst
        (PT.rec (snd (y ∈ DA.defSet ψ)) fromFib
          (∈∈ₛ {a = y} {b = DS.defSet (bnd ψ)} .snd y∈))
      where
      fromFib : Σ[ p ∈ Σ[ k ∈ ⟪ Lset σ ⟫ ] (⟨ DS.smallSat (bnd ψ) k ⟩) ]
                (⟪ Lset σ ⟫↪ (p .fst) ≡ y)
              → ⟨ y ∈ DA.defSet ψ ⟩
      fromFib ((k , hk) , q) = goal
        where
        hb : ⟨ (DS.ι k ∷ []) DS.⊨ᵐ (bnd ψ) ⟩
        hb = invEq (DS.⊨ᵐ-small (bnd ψ) (DS.ι k ∷ []) .snd) hk
        guard : ⟨ ⟪ Lset σ ⟫↪ k ∈ a ⟩
        guard = subst (λ w → ⟨ ⟪ Lset σ ⟫↪ k ∈ w ⟩) mAEq (fst hb)
        y∈a : ⟨ y ∈ a ⟩
        y∈a = subst (λ u → ⟨ u ∈ a ⟩) q guard
        fib = ∈-asFiber {a = y} {b = a} y∈a
        m₀ = fib .fst
        q₀ = fib .snd
        entryEq : DS.ι k ≡ DS.ι (κ m₀)
        entryEq = Σ≡Prop (λ z → snd (DS.M z))
          (q ∙ sym q₀ ∙ sym (κEq m₀))
        bodyκ : ⟨ (DS.ι (κ m₀) ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        bodyκ = subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd ψ) ⟩)
                  (cong (λ E → E ∷ []) entryEq) (snd hb)
        bodyEnv : ⟨ repV (DA.ι m₀ ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        bodyEnv =
          subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd ψ) ⟩)
            (cong (λ E → E ∷ []) (sym (repκ m₀))) bodyκ
        satA : ⟨ (DA.ι m₀ ∷ []) DA.⊨ᵐ ψ ⟩
        satA = sat≈ ψ (DA.ι m₀ ∷ []) .snd bodyEnv
        goal : ⟨ y ∈ DA.defSet ψ ⟩
        goal = subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) q₀
          (subst ⟨_⟩ (sym (DA.defSet-mem ψ m₀)) satA)

    sub₂ : ⟨ DA.defSet ψ ⊆ DS.defSet (bnd ψ) ⟩
    sub₂ y y∈ =
      ∈∈ₛ {a = y} {b = DS.defSet (bnd ψ)} .fst
        (PT.rec (snd (y ∈ DS.defSet (bnd ψ))) fromFib
          (∈∈ₛ {a = y} {b = DA.defSet ψ} .snd y∈))
      where
      fromFib : Σ[ p ∈ Σ[ m ∈ ⟪ a ⟫ ] (⟨ DA.smallSat ψ m ⟩) ]
                (⟪ a ⟫↪ (p .fst) ≡ y)
              → ⟨ y ∈ DS.defSet (bnd ψ) ⟩
      fromFib ((m , hm) , q) = goal
        where
        hs : ⟨ (DA.ι m ∷ []) DA.⊨ᵐ ψ ⟩
        hs = invEq (DA.⊨ᵐ-small ψ (DA.ι m ∷ []) .snd) hm
        hsκ : ⟨ repV (DA.ι m ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        hsκ = sat≈ ψ (DA.ι m ∷ []) .fst hs
        hsκ′ : ⟨ (DS.ι (κ m) ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        hsκ′ = subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd ψ) ⟩)
                 (cong (λ E → E ∷ []) (repκ m)) hsκ
        guard : ⟨ ⟪ Lset σ ⟫↪ (κ m) ∈ ⟪ Lset σ ⟫↪ mA ⟩
        guard = subst (λ w → ⟨ ⟪ Lset σ ⟫↪ (κ m) ∈ w ⟩) (sym mAEq)
                  (subst (λ u → ⟨ u ∈ a ⟩) (sym (κEq m)) (DA-in m))
        hband : ⟨ (DS.ι (κ m) ∷ []) DS.⊨ᵐ (bnd ψ) ⟩
        hband = guard , hsκ′
        goal : ⟨ y ∈ DS.defSet (bnd ψ) ⟩
        goal = subst (λ u → ⟨ u ∈ DS.defSet (bnd ψ) ⟩) (κEq m ∙ q)
          (subst ⟨_⟩ (sym (DS.defSet-mem (bnd ψ) (κ m))) hband)

-- =====================================================================
-- THE OBLIGATION, INHABITED.
-- =====================================================================

landing : (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        → (A : S) (ψ : Formula ⟪ fst A ⟫ 1)
        → (δ : V ℓ) → ⟨ δ ∈ γ ⟩ → ⟨ fst A ∈ 𝒟ₒ (Lset δ) ⟩
        → ⟨ DefOf.defSet (fst A) ψ ∈ Lset γ ⟩
landing γ oγ clγ A ψ δ δ∈γ A∈𝒟δ =
  Lset-mono {α = γ} {β = +ω δ} (clγ δ δ∈γ)
    (Lset-mono {α = +ω δ} {β = sucV (sucV δ)} (+ω-iter 2 δ)
      (subst (λ w → ⟨ DefOf.defSet (fst A) ψ ∈ w ⟩) (sym (Lset-suc σ)) d∈𝒟σ))
  where
  σ : V ℓ
  σ = sucV δ
  oδ : IsOrd δ
  oδ = mem-ord {A = γ} oγ δ δ∈γ
  oσ : IsOrd σ
  oσ = suc-ord oδ
  A∈Lσ : ⟨ fst A ∈ Lset σ ⟩
  A∈Lσ = subst (λ w → ⟨ fst A ∈ w ⟩) (sym (Lset-suc δ)) A∈𝒟δ
  module X = Carrier (fst A) σ oσ A∈Lσ
  d∈𝒟σ : ⟨ DefOf.defSet (fst A) ψ ∈ 𝒟ₒ (Lset σ) ⟩
  d∈𝒟σ = 𝒟ₒ-intro (Lset σ) (DefOf.defSet (fst A) ψ)
           ∣ X.bnd ψ , X.bnd≡ ψ ∣₁

defSet-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → (ψ : Formula ⟪ fst A ⟫ 1)
    → ⟨ DefOf.defSet (fst A) ψ ∈ Lset γ ⟩
defSet-in-carrier-lim γ oγ clγ A hA ψ =
  PT.rec (snd (DefOf.defSet (fst A) ψ ∈ Lset γ))
    (λ { (δ , (δ∈γ , A∈𝒟δ)) → landing γ oγ clγ A ψ δ δ∈γ A∈𝒟δ })
    (Lset-out γ (fst A) hA)
