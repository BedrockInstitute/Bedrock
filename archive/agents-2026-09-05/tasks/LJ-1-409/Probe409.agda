{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.409] W3 PROBE, then the obligation.  `place-code` is
-- `[LJ-1.397]`'s `code-lands` with the `Placement` hypothesis removed.
-- The given code is not placed.  It is replaced by a trim that fits.
--
-- W3 FIRST: `trim-conj4`, conjunct 4 of `InjCode` for the trimmed code
-- alone.  The other three conjuncts and the placement follow it.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-409.Probe409 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in; injAt-out )
open import L.InjChain {ℓ} lem using ( module PairBound )
open import L.Cardinal {ℓ} lem
  using ( InjCode; module SiteBound )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- Membership in a given code, as a one-place formula.  Separation
-- carves the trim with this formula, exactly as Comp carves with
-- `compFo` (src/L/InjChain.lagda.md:339).
inFo : S → Formula S 1
inFo F = var zero ∈̇ con F

-- =====================================================================
-- THE TRIM.  Generic in the two carriers and the given code.
-- =====================================================================

module Trim (a c F : S) where

  private
    module PB = PairBound a c

  opaque
    F′ : S
    F′ = fst (fst (hasSeparationL PB.bnd (inFo F)))

    F′-spec : (p : S) → (p ∈ˢ F′)
            ≡ ((p ∈ˢ PB.bnd) ⊓ ((p ∷ []) ⊨ inFo F))
    F′-spec = snd (fst (hasSeparationL PB.bnd (inFo F)))

  -- Downward: a pair in the trim is a pair in the given code.
  -- The bound is not read.  This is the only direction conjunct 4 needs.
  F′-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F′ ⟩
         → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
  F′-out x y h = subst (λ w → ⟨ w ∈ fst F ⟩) (prʟ-fst x y)
    (snd (subst ⟨_⟩ (F′-spec q) h′))
    where
    q : S
    q = prʟ x y
    h′ : ⟨ q ∈ˢ F′ ⟩
    h′ = subst (λ w → ⟨ w ∈ fst F′ ⟩) (sym (prʟ-fst x y)) h

  -- Upward: a pair over `a` and `c` that the given code holds is in the
  -- trim.  The bound is read here, by `PairBound.below`.
  F′-in : (x y : S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst y ∈ fst c ⟩
        → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
        → ⟨ pr (fst x) (fst y) ∈ fst F′ ⟩
  F′-in x y mx my hf =
    subst (λ w → ⟨ w ∈ fst F′ ⟩) (prʟ-fst x y)
      (subst ⟨_⟩ (sym (F′-spec q))
        ( subst (λ w → ⟨ w ∈ fst PB.bnd ⟩) (sym (prʟ-fst x y))
            (PB.below x y mx my)
        , subst (λ w → ⟨ w ∈ fst F ⟩) (sym (prʟ-fst x y)) hf ))
    where
    q : S
    q = prʟ x y

-- W3.  Conjunct 4 of `InjCode` for the trim, given conjunct 4 for F
-- and the separation spec.  Stated alone and run FIRST.
trim-conj4 :
    (a c F : S)
  → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst c ⟩)
  → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (Trim.F′ a c F) ⟩
  → ⟨ fst y ∈ fst c ⟩
trim-conj4 a c F ran x y h = ran x y (Trim.F′-out a c F x y h)

-- =====================================================================
-- THE FOUR CONJUNCTS, for the trim.  svAt and injAt transfer DOWN.
-- domAt's "pair is in the code" transfers UP, and that is where the
-- bound is read.
-- =====================================================================

module TrimCode (a c F : S) (code : InjCode F a c) where

  open Trim a c F public

  private
    svF = code .fst
    dmF = code .snd .fst
    ijF = code .snd .snd .fst
    ranF = code .snd .snd .snd

    γF : S ^ 2
    γF = F ∷ a ∷ []

    γF′ : S ^ 2
    γF′ = F′ ∷ a ∷ []

  svF′ : ⟨ γF′ ⊨ svAt zero ⟩
  svF′ = svAt-in zero γF′ (λ x y y' p q →
    svAt-out zero γF svF x y y' (F′-out x y p) (F′-out x y' q))

  ijF′ : ⟨ γF′ ⊨ injAt zero ⟩
  ijF′ = injAt-in zero γF′ (λ y x x' p q →
    injAt-out zero γF ijF y x x' (F′-out x y p) (F′-out x' y q))

  dmF′ : ⟨ γF′ ⊨ domAt zero (suc zero) ⟩
  dmF′ = domAt-intro zero (suc zero) γF′ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F′) ⟩
        → ⟨ fst x ∈ fst a ⟩
    fwd x = PT.rec (snd (fst x ∈ fst a))
      (λ { (y , p) → domAt-out zero (suc zero) γF dmF x y (F′-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst a ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F′) ⟩
    bwd x mx = PT.rec squash₁
      (λ { (y , hf) → ∣ y , F′-in x y mx (ranF x y hf) hf ∣₁ })
      (domAt-in zero (suc zero) γF dmF x mx)

  ranF′ : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F′ ⟩ → ⟨ fst y ∈ fst c ⟩
  ranF′ = trim-conj4 a c F ranF

  trimmed : InjCode F′ a c
  trimmed = svF′ , (dmF′ , (ijF′ , ranF′))

-- The trim, as a packaged replacement.  The four conjuncts close.  The
-- placement of `F′` in `Lset (SiteBound.β a)` does not; see
-- `review-of-place-code.md`.
trimmed-code :
    (a c : S)
  → Σ[ F ∈ S ] InjCode F a c
  → Σ[ G ∈ S ] InjCode G a c
trimmed-code a c (F , code) = F′ , trimmed
  where
  open TrimCode a c F code

-- THE OBLIGATION.  Same shape as `code-lands`
-- (agents/tasks/LJ-1-397/CodeLands.agda:46-62), with the given code
-- replaced by the trim.  The membership `p` is the residue: no delivered
-- lemma places the trim in `Lset (SiteBound.β a)`, and no finite
-- successor count of that ordinal does so at this generality.
place-code :
    (a c : S)
  → ∥ Σ[ F ∈ S ] InjCode F a c ∥₁
  → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
          InjCode (SiteBound.up a F) a c ∥₁
place-code a c h = PT.map into h
  where
  open SiteBound a renaming ( up to upβ )

  into : Σ[ F ∈ S ] InjCode F a c
       → Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
           InjCode (upβ F) a c
  into (F , code) = (fst G , p) , transported
    where
    G = trimmed-code a c (F , code) .fst
    gcode = trimmed-code a c (F , code) .snd
    p : ⟨ fst G ∈ Lset (SiteBound.β a) ⟩
    p = {!!}
    upβG≡G : upβ (fst G , p) ≡ G
    upβG≡G = Σ≡Prop (λ v → snd (isL v)) refl
    transported : InjCode (upβ (fst G , p)) a c
    transported = subst (λ H → InjCode H a c) (sym upβG≡G) gcode
