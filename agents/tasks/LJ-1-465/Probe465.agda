{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.465] W3 FIRST, then the obligation.  Does [LJ-1.460]'s shift
-- code inhabit [LJ-1.446]'s CodedInjP' at d, the index of γ.
-- Nothing lands in src/.
--
--   W3 FIRST  `fits-446`.  [LJ-1.460]'s code as a module hypothesis
--             at its delivered type (Probe460.agda:73-76).  446's
--             selection rebuilt as Probe446.agda:117-160 carries it.
--             Obligation omitted.  Typechecked ALONE.
--
--   TERM      omitted.  W3 is UnequalTerms at :158.  See the review.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-465.Probe465 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( bound2; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Cardinal {ℓ} lem using ( InjCode; module SiteBound )
open import L.InjChain {ℓ} lem using ( module InclGraph )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  Rebuild [LJ-1.446]'s selection bound (Probe446.agda:117-160)
-- at a = sucʟ γ.  Take [LJ-1.460]'s code as a module hypothesis at
-- Probe460.agda:73-76.  Ask whether that code inhabits CodedInjP' at
-- d, the index of γ in 446's carrier.  Obligation omitted.
-- =====================================================================

module W3 (γ : S) (oγ : IsOrd (fst γ))
          (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
          (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
          (shift-coded : ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁) where

  a : S
  a = sucʟ γ

  -- Named packing, the same one Probe464.agda:67-68 records.
  -- suc-ord oγ : IsOrd (sucV (fst γ)).  SiteBound and InclGraph want
  -- IsOrd (fst (sucʟ γ)).  sucʟ-fst moves the presentation.
  oa : IsOrd (fst a)
  oa = subst IsOrd (sym (sucʟ-fst γ)) (suc-ord oγ)

  -- [LJ-1.446] bound, rebuilt.  Probe446.agda:119-136.
  open SiteBound a

  module IG = InclGraph a a (λ _ h → h)

  G : S
  G = IG.G

  stgG : V ℓ
  stgG = stage (fst G) (snd G)

  oStg : IsOrd stgG
  oStg = stage-ord (fst G) (snd G)

  pair : Σ[ γB ∈ V ℓ ] (IsOrd γB × ⟨ β ∈ˢ γB ⟩ × ⟨ sucV stgG ∈ˢ γB ⟩)
  pair = bound2 β (sucV stgG) oβ (suc-ord oStg)

  γB : V ℓ
  γB = pair .fst

  oγB : IsOrd γB
  oγB = pair .snd .fst

  upγ : Mem (Lset γB) → S
  upγ (x , m) = x , Lset→isL γB oγB x m

  -- LeastCardInjL's crossing, rebuilt.  Probe446.agda:149-155.
  hSucα : ⟨ isL (sucV (fst a)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
            (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upα : ⟪ sucV (fst a) ⟫ → S
  upα m = ⟪ sucV (fst a) ⟫↪ m
        , isL-trans (member (sucV (fst a)) m) hSucα

  -- [LJ-1.446] spelling.  Probe446.agda:158-160.
  CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  CodedInjP' d =
    ∥ Σ[ F ∈ Mem (Lset γB) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

  -- d is the index of γ in sucV (fst (sucʟ γ)).
  -- Probe464.agda:111-122, at 446's carrier (the same sucV (fst a)).
  γ∈suc² : ⟨ fst γ ∈ˢ sucV (sucV (fst γ)) ⟩
  γ∈suc² = suc-ord (suc-ord oγ) .fst (self∈sucV (fst γ))
             (self∈sucV (sucV (fst γ)))

  γ∈suc-a : ⟨ fst γ ∈ˢ sucV (fst a) ⟩
  γ∈suc-a = subst (λ v → ⟨ fst γ ∈ˢ sucV v ⟩) (sym (sucʟ-fst γ)) γ∈suc²

  d : ⟪ sucV (fst a) ⟫
  d = fiber (sucV (fst a)) γ∈suc-a .fst

  d-eq : ⟪ sucV (fst a) ⟫↪ d ≡ fst γ
  d-eq = fiber (sucV (fst a)) γ∈suc-a .snd

  -- 438 W3, rebuilt.  Probe438.agda:108-112 / Probe464.agda:126-133.
  code-target-swap :
      (H b b' : S) → fst b ≡ fst b'
    → InjCode H a b → InjCode H a b'
  code-target-swap H b b' e (sv , dm , ij , ran) =
    sv , dm , ij , λ x y p → subst (λ v → ⟨ fst y ∈ v ⟩) e (ran x y p)

  -- THE W3 TERM.  Spend 460's truncation into 446's hProp.  The pack
  -- must place F in Lset γB, then swap the range along d-eq, then
  -- move the graph along upγ Fg ≡ F.  The last two are 464's devices.
  -- The first is the bound crossing.  I do not add a hypothesis for
  -- it and I do not rebuild the carve.
  fits-446 : ⟨ CodedInjP' d ⟩
  fits-446 = PT.rec (snd (CodedInjP' d)) pack shift-coded
    where
    pack : Σ[ F ∈ S ] InjCode F a γ → ⟨ CodedInjP' d ⟩
    pack (F , code) = ∣ Fg , movedγ ∣₁
      where
      stgF : V ℓ
      stgF = stage (fst F) (snd F)

      -- 438 places G: Lset-mono along stgG ∈ γB, then stage-mem G.
      -- Probe438.agda:81-93.  The same lines at F need stgF ∈ γB.
      -- γB contains β and sucV stgG (pair .snd .snd).  It does not
      -- name stgF.  The next line is the crossing.  It does not
      -- typecheck: stage-mem F lands in Lset stgF, not Lset stgG.
      mF : ⟨ fst F ∈ˢ Lset γB ⟩
      mF = Lset-mono {α = γB} {β = stgG}
             (oγB .fst (self∈sucV stgG) (pair .snd .snd .snd))
             (stage-mem (fst F) (snd F))

      Fg : Mem (Lset γB)
      Fg = fst F , mF

      moved : InjCode F a (upα d)
      moved = code-target-swap F γ (upα d) (sym d-eq) code

      upγFg≡F : upγ Fg ≡ F
      upγFg≡F = Σ≡Prop (λ x → snd (isL x)) refl

      movedγ : InjCode (upγ Fg) a (upα d)
      movedγ = subst (λ H → InjCode H a (upα d)) (sym upγFg≡F) moved

-- THE OBLIGATION is not a term.  W3 failed at Probe465.agda:156-158:
-- 438's placement of G, applied to 460's F, is UnequalTerms
-- `fst F != fst IG.G`.  446's κC is selected only after a nonempty
-- at that bound (Probe446.agda:164-195).  Without fits-446 there is
-- no κC (sucʟ γ) (suc-ord oγ) to inhabit.  I do not add a hypothesis.
-- I do not rebuild the carve.  See review-of-residue-at-successor-446.md.
