{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.386] PROBE.  Leg 1 of the coded-witness route, measured at ONE
-- band ordinal.  It runs in agents/tasks/LJ-1-386/ and lands nothing.
--
-- The brief asks for the internal existence
--
--     ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁
--
-- at `+ω ω`, for the `Good` of src/L/Cardinal.lagda.md:187-190, and for
-- either an inhabitant or the obstruction.  This file gives the
-- inhabitant AND measures what it is worth.
--
--   PART 1  THE IDENTITY GRAPH.  For EVERY L-element D, replacement
--           builds the set { ⟨x,x⟩ : x ∈ D }, and it satisfies all FOUR
--           of `InjCode`'s conjuncts at source D and target D.
--
--   PART 2  `Good`-EXISTENCE REDUCES TO PLACEMENT ALONE.  The three
--           conjuncts cost nothing at any D and at any site.
--
--   PART 3  THE BRIEF'S STATEMENT, DISCHARGED at `+ω ω`.
--
--   PART 4  WHAT THE CODE READS BACK TO: the identity on ⟪ δ ⟫.
--           `Good` never mentions a target, so it buys no descent.
--
--   PART 5  LEG 1, STATED IN FULL, and the route assembled from it
--           UNTRUNCATED.  This is the part `Good` does not state.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-386.Probe386 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL; Lset-mono )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.StageArith {ℓ} lem using ( +ω; +ω-ord )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Stage {ℓ} lem using ( stage; stage-mem )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )
open import L.Coding.Model {ℓ}
  using ( svAt; svAt-in; domAt; domAt-intro
        ; prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in; module Small )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module SiteBound; module Canonical )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- PART 0.  The band ordinal, as an L-element.
-- =====================================================================

isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- `+ω ω` is ω + ω, the tree's named band candidate
-- (src/L/Ordinal/StageArith.lagda.md:41-42).
δ : S
δ = +ω ω , isL-ord (+ω ω) (+ω-ord ω ω-ord)

-- =====================================================================
-- PART 1.  The identity graph on an arbitrary L-element D.
-- =====================================================================

module IdGraph (D : S) where

  -- The graph formula:  y = ⟨x,x⟩,  read at the environment (y ∷ x ∷ []).
  φ : Formula S 2
  φ = prAtL zero (suc zero) (suc zero)

  φ-out : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩ → fst y ≡ pr (fst x) (fst x)
  φ-out x y = subst ⟨_⟩ (prAtL-adequate zero (suc zero) (suc zero) (y ∷ x ∷ []))

  φ-in : (x y : S) → fst y ≡ pr (fst x) (fst x) → ⟨ (y ∷ x ∷ []) ⊨ φ ⟩
  φ-in x y =
    subst ⟨_⟩ (sym (prAtL-adequate zero (suc zero) (suc zero) (y ∷ x ∷ [])))

  fc : (x : S) → ⟨ x ∈ˢ D ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩)
  fc x _ = ctr , uniq
    where
    ctr : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩
    ctr = prʟ x x , φ-in x (prʟ x x) (prʟ-fst x x)
    uniq : (r : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩) → ctr ≡ r
    uniq (y , h) = Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ φ))
      (Σ≡Prop (λ v → snd (isL v)) (prʟ-fst x x ∙ sym (φ-out x y h)))

  rep : SetOf (λ y → ⋁ S (λ x → (x ∈ˢ D) ⊓ ((y ∷ x ∷ []) ⊨ φ)))
  rep = hasReplacementL D φ fc .fst

  G : S
  G = rep .fst

  -- Reading a pair out of the graph: both coordinates are one member of D.
  Diag : S → S → Type (ℓ-suc ℓ)
  Diag u v = Σ[ x ∈ S ] (⟨ x ∈ˢ D ⟩ × ((fst u ≡ fst x) × (fst v ≡ fst x)))

  inG-out : (u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩ → ∥ Diag u v ∥₁
  inG-out u v h = PT.map read
    (subst ⟨_⟩ (rep .snd (prʟ u v))
      (subst (λ z → ⟨ z ∈ fst G ⟩) (sym (prʟ-fst u v)) h))
    where
    read : Σ[ x ∈ S ] (⟨ x ∈ˢ D ⟩ × ⟨ (prʟ u v ∷ x ∷ []) ⊨ φ ⟩) → Diag u v
    read (x , (x∈D , hx)) = x , (x∈D , (pr-inj q .fst , pr-inj q .snd))
      where
      q : pr (fst u) (fst v) ≡ pr (fst x) (fst x)
      q = sym (prʟ-fst u v) ∙ φ-out x (prʟ u v) hx

  inG-in : (u : S) → ⟨ u ∈ˢ D ⟩ → ⟨ pr (fst u) (fst u) ∈ fst G ⟩
  inG-in u u∈D = subst (λ z → ⟨ z ∈ fst G ⟩) (prʟ-fst u u)
    (subst ⟨_⟩ (sym (rep .snd (prʟ u u)))
      ∣ u , (u∈D , φ-in u (prʟ u u) (prʟ-fst u u)) ∣₁)

  -- The three conjuncts of `Good`, at the environment (G ∷ D ∷ []).
  sv : ⟨ (G ∷ D ∷ []) ⊨ svAt zero ⟩
  sv = svAt-in zero (G ∷ D ∷ []) step
    where
    step : (x y y' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
         → ⟨ pr (fst x) (fst y') ∈ fst G ⟩ → fst y ≡ fst y'
    step x y y' p q = PT.rec (setIsSet (fst y) (fst y'))
      (λ { (a , (_ , (xa , ya))) → PT.rec (setIsSet (fst y) (fst y'))
        (λ { (b , (_ , (xb , y'b))) →
             ya ∙ sym xa ∙ xb ∙ sym y'b }) (inG-out x y' q) })
      (inG-out x y p)

  ij : ⟨ (G ∷ D ∷ []) ⊨ injAt zero ⟩
  ij = injAt-in zero (G ∷ D ∷ []) step
    where
    step : (y x x' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
         → ⟨ pr (fst x') (fst y) ∈ fst G ⟩ → fst x ≡ fst x'
    step y x x' p q = PT.rec (setIsSet (fst x) (fst x'))
      (λ { (a , (_ , (xa , ya))) → PT.rec (setIsSet (fst x) (fst x'))
        (λ { (b , (_ , (x'b , yb))) →
             xa ∙ sym ya ∙ yb ∙ sym x'b }) (inG-out x' y q) })
      (inG-out x y p)

  dm : ⟨ (G ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) (G ∷ D ∷ []) (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ⋁ S (λ y → (pr (fst x) (fst y) ∈ fst G)) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
        (λ { (a , (a∈D , (xa , _))) →
             subst (λ z → ⟨ z ∈ fst D ⟩) (sym xa) a∈D }) (inG-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ⋁ S (λ y → (pr (fst x) (fst y) ∈ fst G)) ⟩
    bwd x m = ∣ x , inG-in x m ∣₁

  -- The FOURTH conjunct, with the target taken to be D itself.
  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst D ⟩
  ran x y p = PT.rec (snd (fst y ∈ fst D))
    (λ { (a , (a∈D , (_ , ya))) →
         subst (λ z → ⟨ z ∈ fst D ⟩) (sym ya) a∈D }) (inG-out x y p)

  -- So the identity graph is a FULL `InjCode` at source D and target D.
  idCode : InjCode G D D
  idCode = sv , (dm , (ij , ran))

  -- And it is a member of the tower at its own stage bound.
  G∈ : ⟨ fst G ∈ Lset (SiteBound.β G) ⟩
  G∈ = Lset-mono (stageBound (fst G) (snd G) .snd .snd .snd)
         (stage-mem (fst G) (snd G))

-- =====================================================================
-- PART 2.  `Good`-existence reduces to PLACEMENT, at every D and site.
-- =====================================================================

module _ (a D : S) where
  open SiteBound a using ( β; oβ; up )
  open Canonical a D using ( Good )
  open IdGraph D using ( G; sv; dm; ij )

  good-from-placement : (h : ⟨ fst G ∈ Lset β ⟩)
                      → ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁
  good-from-placement h = ∣ (fst G , h) , transported ∣₁
    where
    upG : up (fst G , h) ≡ G
    upG = Σ≡Prop (λ v → snd (isL v)) refl
    transported : ⟨ Good (fst G , h) ⟩
    transported = subst
      (λ F → ⟨ ((F ∷ D ∷ []) ⊨ svAt zero)
             ⊓ (((F ∷ D ∷ []) ⊨ domAt zero (suc zero))
             ⊓  ((F ∷ D ∷ []) ⊨ injAt zero)) ⟩)
      (sym upG) (sv , (dm , ij))

-- =====================================================================
-- PART 3.  THE BRIEF'S STATEMENT, at the band ordinal `+ω ω`.
--
--   The site `a` of `Canonical a D` is a free parameter, and the graph
--   is placed at its own bound, so the placement obligation is
--   discharged where the statement lets it be.
-- =====================================================================

Site : S
Site = IdGraph.G δ

code-exists : ∥ Σ[ A ∈ Mem (Lset (SiteBound.β Site)) ]
                ⟨ Canonical.Good Site δ A ⟩ ∥₁
code-exists = good-from-placement Site δ (IdGraph.G∈ δ)

-- =====================================================================
-- PART 4.  WHAT IT READS BACK TO.
--
--   `Good` names no target, so the readback of the witness it admits is
--   the identity on ⟪ δ ⟫.  No descent is bought.
-- =====================================================================

code-inj : ⟪ fst δ ⟫ ↪ ⟪ fst δ ⟫
code-inj = Sm.small , Sm.small-inj
  where
  module I = IdGraph δ
  module Sm = Small I.G δ δ I.sv I.dm I.ij I.ran

-- =====================================================================
-- PART 5.  LEG 1, STATED IN FULL, and the route assembled from it.
--
--   What the coded-witness route needs at the band is NOT `Good` at δ.
--   It is a code whose DOMAIN is the internal square of δ and whose
--   VALUES lie in δ, plus the ambient bridge from the product type into
--   the internal square's index type.  `Good` carries neither.
-- =====================================================================

isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b = isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
  (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
      (isPropΠ (λ x → isPropΠ (λ y → isPropΠ (λ _ → snd (fst y ∈ fst b)))))))

-- THE DOOR, MEASURED.  A code that merely EXISTS yields an ambient
-- injection AS DATA.  `leastOf` under LEM does the untruncation, with
-- no choice principle, and `Small` reads the chosen code out.  This
-- generalises `agents/tasks/LJ-1-299/NoInj2.agda:107-110`, whose
-- readback consumed the code as data.
code-untruncates : (a b : S)
                 → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β a)) ]
                       InjCode (SiteBound.up a A) a b ∥₁
                 → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
code-untruncates a b h = Sm.small , Sm.small-inj
  where
  open SiteBound a using ( β; oβ; up )

  Good4 : Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good4 A = InjCode (up A) a b , isPropInjCode (up A) a b

  chosen : Σ[ A ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good4 A
  chosen = leastOf (orderAt β oβ) lem Good4 h

  code : InjCode (up (fst chosen)) a b
  code = fst (snd chosen)

  module Sm = Small (up (fst chosen)) a b
                (fst code) (fst (snd code)) (fst (snd (snd code)))
                (snd (snd (snd code)))

-- LEG 1 IN FULL.  P is the internal square of δ: an L-set whose index
-- type receives the ambient product.  `Good` names neither conjunct.
Leg1 : S → Type (ℓ-suc ℓ)
Leg1 P = ((⟪ fst δ ⟫ × ⟪ fst δ ⟫) ↪ ⟪ fst P ⟫)
       × ∥ Σ[ A ∈ Mem (Lset (SiteBound.β P)) ]
             InjCode (SiteBound.up P A) P δ ∥₁

-- THE PAYOFF, UNTRUNCATED.  Nothing here is truncated at the end, and
-- no axiom beyond the `lem` the whole tree already carries.
leg1-gives-sq : (P : S) → Leg1 P → sq (fst δ)
leg1-gives-sq P (bridge , h) = (λ p → fst read (fst bridge p)) , inj
  where
  read : ⟪ fst P ⟫ ↪ ⟪ fst δ ⟫
  read = code-untruncates P δ h

  inj : (p q : ⟪ fst δ ⟫ × ⟪ fst δ ⟫)
      → fst read (fst bridge p) ≡ fst read (fst bridge q) → p ≡ q
  inj p q e = snd bridge p q (snd read (fst bridge p) (fst bridge q) e)
