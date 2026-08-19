{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.388] PROBE.  The internal product of two L-elements, built at
-- GENERIC `a` and `b`, and the ambient bridge into it.  It runs in
-- agents/tasks/LJ-1-388/ and lands nothing.
--
-- The brief asks for one object and one bridge:
--
--     prodL       : (a b : S) → S
--     prod-bridge : (a b : S) → (⟪ fst a ⟫ × ⟪ fst b ⟫) ↪ ⟪ fst (prodL a b) ⟫
--
-- and for a price for the L-membership half, which is the part the
-- archived rud route's `F2` gives no help with.
--
--   PART 1  THE BOUND.  Every Kuratowski pair of a member of `a` with a
--           member of `b` lands two stages above a stage that holds
--           both.  `pr∈Lset-suc` is delivered and this is its use.
--
--   PART 2  THE FORMULA, and its reading in both directions.  One
--           bounded existential over `a`, one over `b`, and the
--           delivered pair atom `prAtL` inside.
--
--   PART 3  THE OBJECT.  `prodL a b` is ONE separation over the stage
--           of PART 1, so it is an L-element by construction and the
--           L-membership half costs nothing past the bound.
--
--   PART 4  THE MEMBERSHIP READING, both directions, at generic `a`
--           and `b`.  This is `F2-spec`'s statement for the L form.
--
--   PART 5  THE BRIDGE, and its injectivity.
--
--   PART 6  LEG 1'S FIRST CONJUNCT, as one application.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-388.Probe388 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( bound2; suc-ord )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS; pr∈Lset-suc )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _⊆_; ∈∈ₛ; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Sigma using ( ≡-× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE ARCHIVED AMBIENT PRODUCT, PORTED.
--
--   Two lines, verbatim from the retired rud route at
--   archive/src/2026-08-09-rud-route/L/Rud/Ops.lagda.md:210-211, with
--   the `opaque` seal dropped because this file has no consumer to
--   protect.  It is the AMBIENT object only: nothing here says it is an
--   L-element, and PART 7 is where that is paid.
-- =====================================================================

F2 : V ℓ → V ℓ → V ℓ
F2 x y = sett (⟪ x ⟫ × ⟪ y ⟫) (λ p → pr (⟪ x ⟫↪ (p .fst)) (⟪ y ⟫↪ (p .snd)))

-- =====================================================================
-- The construction, at GENERIC `a` and `b`.
--
--   Nothing below names an ordinal, a stage or a site.  A product of
--   two L-sets is generic by nature (DD4), and the fixed form would be
--   a defect here rather than a shortcut.
-- =====================================================================

module Prod (a b : S) where

  -- ===================================================================
  -- PART 1.  THE BOUND.
  -- ===================================================================

  -- A stage that holds both arguments: the two earliest stages, merged.
  private
    sa = stage (fst a) (a .snd)
    sb = stage (fst b) (b .snd)
    bb = bound2 sa sb (stage-ord (fst a) (a .snd)) (stage-ord (fst b) (b .snd))

  σ : V ℓ
  σ = bb .fst

  oσ : IsOrd σ
  oσ = bb .snd .fst

  fa∈σ : ⟨ fst a ∈ Lset σ ⟩
  fa∈σ = Lset-mono {α = σ} {β = sa} (bb .snd .snd .fst)
           (stage-mem (fst a) (a .snd))

  fb∈σ : ⟨ fst b ∈ Lset σ ⟩
  fb∈σ = Lset-mono {α = σ} {β = sb} (bb .snd .snd .snd)
           (stage-mem (fst b) (b .snd))

  -- Two stages up, because Kuratowski's pair is two unordered pairs
  -- deep.  `pr∈Lset-suc` is the delivered form of exactly that count,
  -- and src/L/Axioms/Basic.lagda.md:529-533 says it was stated for this.
  τ : V ℓ
  τ = sucV (sucV σ)

  oτ : IsOrd τ
  oτ = suc-ord (suc-ord oσ)

  Lτ : S
  Lτ = LsetS τ oτ

  -- The stage is transitive, so a member of `a` is a member of the
  -- stage, and the pair of two of them lands in `Lset τ`.
  pr∈τ : (u v : S) → ⟨ fst u ∈ fst a ⟩ → ⟨ fst v ∈ fst b ⟩
       → ⟨ pr (fst u) (fst v) ∈ Lset τ ⟩
  pr∈τ u v u∈a v∈b = pr∈Lset-suc σ (fst u) (fst v)
    (layer-trans (Lset-layer σ) u∈a fa∈σ)
    (layer-trans (Lset-layer σ) v∈b fb∈σ)

  -- ===================================================================
  -- PART 2.  THE FORMULA.
  --
  --   Φ(t) reads "t is the Kuratowski pair of a member of `a` with a
  --   member of `b`".  Both quantifiers are bounded by a parameter, so
  --   the whole of it is Δ₀, and `prAtL` is the delivered pair atom.
  -- ===================================================================

  Φ : Formula S 1
  Φ = ∃̇∈ (con a) (∃̇∈ (con b) (prAtL (suc (suc zero)) (suc zero) zero))

  -- The environment under both binders is (v ∷ u ∷ t ∷ []).
  private
    read : (t u v : S)
         → ⟨ (v ∷ u ∷ t ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
         → fst t ≡ pr (fst u) (fst v)
    read t u v = subst ⟨_⟩
      (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ t ∷ []))

    write : (t u v : S) → fst t ≡ pr (fst u) (fst v)
          → ⟨ (v ∷ u ∷ t ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
    write t u v = subst ⟨_⟩
      (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ t ∷ [])))

  -- What a member of `a` and a member of `b` say about the pair.
  Pair : S → Type (ℓ-suc ℓ)
  Pair t = Σ[ u ∈ S ] Σ[ v ∈ S ]
             (⟨ u ∈ˢ a ⟩ × ⟨ v ∈ˢ b ⟩ × (fst t ≡ pr (fst u) (fst v)))

  Φ-out : (t : S) → ⟨ (t ∷ []) ⊨ Φ ⟩ → ∥ Pair t ∥₁
  Φ-out t = PT.rec squash₁
    (λ { (u , (u∈a , h)) → PT.map
      (λ { (v , (v∈b , k)) → u , (v , (u∈a , (v∈b , read t u v k))) }) h })

  Φ-in : (u v : S) → ⟨ u ∈ˢ a ⟩ → ⟨ v ∈ˢ b ⟩ → ⟨ (prʟ u v ∷ []) ⊨ Φ ⟩
  Φ-in u v u∈a v∈b =
    ∣ u , (u∈a , ∣ v , (v∈b , write (prʟ u v) u v (prʟ-fst u v)) ∣₁) ∣₁

  -- ===================================================================
  -- PART 3.  THE OBJECT.
  --
  --   ONE separation, over the stage of PART 1 taken as an L-element.
  --   `hasSeparationL` returns an element of the L-carrier, so `isL` is
  --   discharged by construction and never proved.
  -- ===================================================================

  sep : SetOf (λ x → (x ∈ˢ Lτ) ⊓ ((x ∷ []) ⊨ Φ))
  sep = hasSeparationL Lτ Φ .fst

  P : S
  P = sep .fst

  P-mem : (x : S) → (x ∈ˢ P) ≡ ((x ∈ˢ Lτ) ⊓ ((x ∷ []) ⊨ Φ))
  P-mem = sep .snd

  -- ===================================================================
  -- PART 4.  THE MEMBERSHIP READING.
  --
  --   `F2-spec`'s statement, for the L form.  The archived ambient one
  --   is archive/src/2026-08-09-rud-route/L/Rud/Ops.lagda.md:213-221.
  -- ===================================================================

  prod-in : (u v : S) → ⟨ u ∈ˢ a ⟩ → ⟨ v ∈ˢ b ⟩
          → ⟨ pr (fst u) (fst v) ∈ fst P ⟩
  prod-in u v u∈a v∈b = subst (λ w → ⟨ w ∈ fst P ⟩) (prʟ-fst u v)
    (subst ⟨_⟩ (sym (P-mem (prʟ u v)))
      ( subst (λ w → ⟨ w ∈ Lset τ ⟩) (sym (prʟ-fst u v))
          (pr∈τ u v u∈a v∈b)
      , Φ-in u v u∈a v∈b ))

  prod-out : (t : S) → ⟨ t ∈ˢ P ⟩ → ∥ Pair t ∥₁
  prod-out t h = Φ-out t (snd (subst ⟨_⟩ (P-mem t) h))

  -- ===================================================================
  -- PART 5.  THE BRIDGE.
  -- ===================================================================

  -- A member index, lifted to an element of the L-carrier.
  memA : ⟪ fst a ⟫ → S
  memA m = ⟪ fst a ⟫↪ m
         , isL-trans {x = fst a} {y = ⟪ fst a ⟫↪ m} (member (fst a) m) (snd a)

  memB : ⟪ fst b ⟫ → S
  memB n = ⟪ fst b ⟫↪ n
         , isL-trans {x = fst b} {y = ⟪ fst b ⟫↪ n} (member (fst b) n) (snd b)

  private
    fibP : (m : ⟪ fst a ⟫) (n : ⟪ fst b ⟫)
         → Σ[ k ∈ ⟪ fst P ⟫ ]
             (⟪ fst P ⟫↪ k ≡ pr (⟪ fst a ⟫↪ m) (⟪ fst b ⟫↪ n))
    fibP m n = fiber (fst P)
      (prod-in (memA m) (memB n) (member (fst a) m) (member (fst b) n))

  toP : ⟪ fst a ⟫ × ⟪ fst b ⟫ → ⟪ fst P ⟫
  toP (m , n) = fibP m n .fst

  -- The pair is injective ambiently (src/V/Coding.lagda.md:178-179) and
  -- a member index is recovered from its value (`↪-inj`), so the two
  -- coordinates come back one at a time.
  toP-inj : (p q : ⟪ fst a ⟫ × ⟪ fst b ⟫) → toP p ≡ toP q → p ≡ q
  toP-inj (m , n) (m' , n') e =
    ≡-× (↪-inj {a = fst a} {m = m} {n = m'} (pr-inj eq .fst))
        (↪-inj {a = fst b} {m = n} {n = n'} (pr-inj eq .snd))
    where
    eq : pr (⟪ fst a ⟫↪ m) (⟪ fst b ⟫↪ n)
       ≡ pr (⟪ fst a ⟫↪ m') (⟪ fst b ⟫↪ n')
    eq = sym (fibP m n .snd) ∙ cong ⟪ fst P ⟫↪ e ∙ fibP m' n' .snd

  -- ===================================================================
  -- PART 7.  WHAT THE ARCHIVE PORTS.
  --
  --   The archived `F2` and this separation are THE SAME SET.  So the
  --   archived construction ports whole as the ambient object, and what
  --   it never carried, `isL`, is what the separation supplies.  The
  --   two inclusions are the membership reading of PART 4 read against
  --   `sett`'s own membership, which asks for a preimage merely
  --   (src/V/Hierarchy.lagda.md:45-49).
  -- ===================================================================

  private
    F2ab : V ℓ
    F2ab = F2 (fst a) (fst b)

    F2⊆P : ⟨ F2ab ⊆ fst P ⟩
    F2⊆P w w∈ₛ = ∈∈ₛ {a = w} {b = fst P} .fst
      (PT.rec (snd (w ∈ fst P))
        (λ { ((m , n) , q) → subst (λ z → ⟨ z ∈ fst P ⟩) q
               (prod-in (memA m) (memB n)
                 (member (fst a) m) (member (fst b) n)) })
        (∈∈ₛ {a = w} {b = F2ab} .snd w∈ₛ))

    P⊆F2 : ⟨ fst P ⊆ F2ab ⟩
    P⊆F2 w w∈ₛ = ∈∈ₛ {a = w} {b = F2ab} .fst
      (PT.rec (snd (w ∈ F2ab)) step (prod-out wS w∈))
      where
      w∈ : ⟨ w ∈ fst P ⟩
      w∈ = ∈∈ₛ {a = w} {b = fst P} .snd w∈ₛ

      wS : S
      wS = w , isL-trans {x = fst P} {y = w} w∈ (snd P)

      step : Pair wS → ⟨ w ∈ F2ab ⟩
      step (u , (v , (u∈a , (v∈b , e)))) =
        ∣ (fiber (fst a) u∈a .fst , fiber (fst b) v∈b .fst)
        , (cong₂ pr (fiber (fst a) u∈a .snd) (fiber (fst b) v∈b .snd)
            ∙ sym e) ∣₁

  F2≡ : F2 (fst a) (fst b) ≡ fst P
  F2≡ = extensionality F2ab (fst P) (F2⊆P , P⊆F2)

-- =====================================================================
-- THE TWO OBLIGATIONS.
-- =====================================================================

prodL : (a b : S) → S
prodL a b = Prod.P a b

prod-bridge : (a b : S) → (⟪ fst a ⟫ × ⟪ fst b ⟫) ↪ ⟪ fst (prodL a b) ⟫
prod-bridge a b = Prod.toP a b , Prod.toP-inj a b

-- The membership reading, at the top level, in both directions.
prodL-in : (a b u v : S) → ⟨ u ∈ˢ a ⟩ → ⟨ v ∈ˢ b ⟩
         → ⟨ pr (fst u) (fst v) ∈ fst (prodL a b) ⟩
prodL-in a b = Prod.prod-in a b

prodL-out : (a b t : S) → ⟨ t ∈ˢ prodL a b ⟩ → ∥ Prod.Pair a b t ∥₁
prodL-out a b = Prod.prod-out a b

-- AND WHAT THE ARCHIVE PORTS: the retired route's ambient `F2` is this
-- object.  The port is the two lines above `module Prod`; the content
-- is that the separation supplies the `isL` those two lines never had.
prodL-is-F2 : (a b : S) → F2 (fst a) (fst b) ≡ fst (prodL a b)
prodL-is-F2 a b = Prod.F2≡ a b

-- =====================================================================
-- PART 6.  LEG 1'S FIRST CONJUNCT.
--
--   `Leg1 P` of agents/tasks/LJ-1-386/Probe386.agda:287-290 is the
--   conjunction of an ambient injection into ⟪ fst P ⟫ with a truncated
--   coded injection.  Its FIRST conjunct, at ANY `c` and with
--   `P := prodL c c`, is one application of the bridge.  The site is
--   not fixed here: `[LJ-1.386]` measured that nothing certifies
--   `+ω ω` as a band ordinal, so the ordinal enters only when the
--   route names it (agents/tasks/LJ-1-386/lj-1.386-report.md:207-232).
-- =====================================================================

leg1-fst : (c : S) → (⟪ fst c ⟫ × ⟪ fst c ⟫) ↪ ⟪ fst (prodL c c) ⟫
leg1-fst c = prod-bridge c c
