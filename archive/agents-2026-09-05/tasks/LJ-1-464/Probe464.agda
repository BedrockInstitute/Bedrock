{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.464] W3 FIRST, then the obligation.  Residue at a successor,
-- from [LJ-1.460]'s shift code.  Nothing lands in src/.
--
--   W3 FIRST  `fits`.  [LJ-1.460]'s code as a module hypothesis, at
--             d the index of γ in the successor carrier.  Obligation
--             omitted.  Typechecked ALONE.
--
--   TERM      `residue-at-successor`.  Written after W3 is green.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-464.Probe464 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; IsLeast; leastOf )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Cardinal {ℓ} lem using ( InjCode )

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
-- W3.  Does 460's code inhabit CodedInjP' at d, the index of γ.
-- 460 as module hypothesis at the INNER of its delivered Σ, so the
-- bound that hosts F can be F's own stage.  Obligation omitted.
-- =====================================================================

module W3 (γ : S) (oγ : IsOrd (fst γ))
          (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
          (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
          (F : S) (code : InjCode F (sucʟ γ) γ) where

  a : S
  a = sucʟ γ

  oa : IsOrd (fst a)
  oa = subst IsOrd (sym (sucʟ-fst γ)) (suc-ord oγ)

  -- Bound that hosts F.  438's device, at this F, not at InclGraph.
  -- Probe438.agda:67-93, applied to the hypothesis rather than to G.
  stgF : V ℓ
  stgF = stage (fst F) (snd F)

  oStg : IsOrd stgF
  oStg = stage-ord (fst F) (snd F)

  γb : V ℓ
  γb = sucV stgF

  oγb : IsOrd γb
  oγb = suc-ord oStg

  upγ : Mem (Lset γb) → S
  upγ (x , mx) = x , Lset→isL γb oγb x mx

  mF : ⟨ fst F ∈ˢ Lset γb ⟩
  mF = Lset-mono {α = γb} {β = stgF} (self∈sucV stgF)
         (stage-mem (fst F) (snd F))

  Fg : Mem (Lset γb)
  Fg = fst F , mF

  -- LeastCardInjL's crossing, rebuilt at the call site.
  -- Probe446.agda:149-155 / Probe430.agda:60-66.
  hSucα : ⟨ isL (sucV (fst a)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
            (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upα : ⟪ sucV (fst a) ⟫ → S
  upα m = ⟪ sucV (fst a) ⟫↪ m
        , isL-trans (member (sucV (fst a)) m) hSucα

  -- [LJ-1.430] spelling.  Probe430.agda:82-84.
  CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  CodedInjP' d =
    ∥ Σ[ G ∈ Mem (Lset γb) ] InjCode (upγ G) a (upα d) ∥₁ , squash₁

  -- d is the index of γ in sucV (fst (sucʟ γ)).
  -- γ ∈ suc (suc γ) by transitivity, then sucʟ-fst moves the carrier.
  γ∈suc² : ⟨ fst γ ∈ˢ sucV (sucV (fst γ)) ⟩
  γ∈suc² = suc-ord (suc-ord oγ) .fst (self∈sucV (fst γ))
             (self∈sucV (sucV (fst γ)))

  γ∈suc-a : ⟨ fst γ ∈ˢ sucV (fst a) ⟩
  γ∈suc-a = subst (λ v → ⟨ fst γ ∈ˢ sucV v ⟩) (sym (sucʟ-fst γ)) γ∈suc²

  d : ⟪ sucV (fst a) ⟫
  d = fiber (sucV (fst a)) γ∈suc-a .fst

  d-eq : ⟪ sucV (fst a) ⟫↪ d ≡ fst γ
  d-eq = fiber (sucV (fst a)) γ∈suc-a .snd

  -- 438 W3, rebuilt.  Probe438.agda:108-112.  First three conjuncts
  -- copy.  The fourth substs on fst of the third argument.
  code-target-swap :
      (H b b' : S) → fst b ≡ fst b'
    → InjCode H a b → InjCode H a b'
  code-target-swap H b b' e (sv , dm , ij , ran) =
    sv , dm , ij , λ x y p → subst (λ v → ⟨ fst y ∈ v ⟩) e (ran x y p)

  moved : InjCode F a (upα d)
  moved = code-target-swap F γ (upα d) (sym d-eq) code

  -- upγ Fg and F agree on fst; isL is a proposition.
  upγFg≡F : upγ Fg ≡ F
  upγFg≡F = Σ≡Prop (λ x → snd (isL x)) refl

  movedγ : InjCode (upγ Fg) a (upα d)
  movedγ = subst (λ H → InjCode H a (upα d)) (sym upγFg≡F) moved

  -- THE W3 TERM.  Named packing, not a hidden subst of the predicate:
  -- stage-mem + Lset-mono (F as Mem), fiber (d as index),
  -- code-target-swap (range), Σ≡Prop (upγ Fg ≡ F).
  fits : ⟨ CodedInjP' d ⟩
  fits = ∣ Fg , movedγ ∣₁

  -- Sealed well-order, same seal as Probe446.agda:185-187 and
  -- src/L/Cardinal.lagda.md:90-92.
  opaque
    w : SWO (⟪ sucV (fst a) ⟫)
    w = ordSWO (sucV (fst a)) (suc-ord oa)

  opaque
    unfolding w
    w-lt : (m n : ⟪ sucV (fst a) ⟫)
         → SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst a) ⟫↪ m ∈ˢ ⟪ sucV (fst a) ⟫↪ n ⟩
    w-lt m n = refl

  nonempty : ∥ Σ[ e ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodedInjP' e ⟩ ∥₁
  nonempty = ∣ d , fits ∣₁

  selected : Σ[ e ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w CodedInjP' e
  selected = leastOf w lem CodedInjP' nonempty

  κC : S
  κC = upα (fst selected)

  γ∈a : ⟨ fst γ ∈ˢ fst a ⟩
  γ∈a = subst (λ v → ⟨ fst γ ∈ˢ v ⟩) (sym (sucʟ-fst γ)) (self∈sucV (fst γ))

  -- THE OBLIGATION, at this F.  Least among coded-injection ordinals
  -- in sucV (fst a), and d is one of them, so selected ≤ d, so
  -- fst κC is a member of sucʟ γ.
  residue-at-successor : ⟨ fst κC ∈ˢ fst a ⟩
  residue-at-successor = by-tri (SWO.tri∙ w (fst selected) d)
    where
    ¬d<κ : SWO._<∙_ w d (fst selected) → Empty.⊥
    ¬d<κ = snd (snd selected) d fits

    by-tri : Tri (SWO._<∙_ w (fst selected) d)
                 (fst selected ≡ d)
                 (SWO._<∙_ w d (fst selected))
           → ⟨ fst κC ∈ˢ fst a ⟩
    by-tri (lt sel<d) = oa .fst {x = fst γ} {y = fst κC} κC∈γ γ∈a
      where
      κC∈γ : ⟨ fst κC ∈ˢ fst γ ⟩
      κC∈γ = subst (λ z → ⟨ fst κC ∈ˢ z ⟩) d-eq
               (transport (w-lt (fst selected) d) sel<d)
    by-tri (eq e) = subst (λ z → ⟨ z ∈ˢ fst a ⟩) (sym κC≡γ) γ∈a
      where
      κC≡γ : fst κC ≡ fst γ
      κC≡γ = cong (⟪ sucV (fst a) ⟫↪) e ∙ d-eq
    by-tri (gt d<κ) = Empty.rec (¬d<κ d<κ)

-- Top-level name the witness meter asks for.  Telescope packages
-- [LJ-1.460]'s inner pair as the two extra arguments; the truncation
-- is not spent, because the bound that hosts F is F's stage.
residue-at-successor :
    (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
    (F : S) (code : InjCode F (sucʟ γ) γ)
  → ⟨ fst (W3.κC γ oγ γ∉ω numerals F code) ∈ˢ fst (sucʟ γ) ⟩
residue-at-successor = W3.residue-at-successor
