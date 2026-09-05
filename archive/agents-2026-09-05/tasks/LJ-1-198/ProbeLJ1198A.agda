{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.198] Probe A.  DOES A6's OBJECT, THE SUCCESSOR ABSORPTION,
-- CARVE BY SEPARATION OR BY REPLACEMENT?
--
-- A6 owns `ShiftAbs` and `Shiftω` (agents/tasks/LJ-1-176/lj-1.176-report.md
-- section 8; [LJ-1.107] measured them at 103 lines and 2.83 s ambient).
-- The open charge is what building them INTO L costs over and above those
-- 103 ambient lines.
--
-- THE GATE (DD8).  The widest unmeasured term: does `ShiftAbs` built into L
-- need a `hasReplacementL`?  [LJ-1.152] measured one replacement at 259 to
-- 269 s and one separation under 0.1 s, a ratio of at least 2,500 to 1.
--
-- THE COMPARABLE, NOT THE PRICE (P-l).  [LJ-1.176] measured an A5 object
-- (the inclusion) built into L: ONE `hasSeparationL`, NO `hasReplacementL`,
-- 112 lines for the inclusion, 1.72 s cold.  This file re-runs the same
-- carve device at the shift, which is a THREE-CASE graph, not an identity.
--
-- WHAT IS BUILT.
--   Part 1  `Ambient`: `ShiftAbs` and `Shiftω`, copied from [LJ-1.156]
--           (agents/tasks/LJ-1-156/ProbeLJ1156A.agda:250-366).  These are
--           A6's own 103 ambient lines; they are the base, not the charge.
--   Part 2  `shiftFo`, the description.  One place, three cases, and every
--           atom of it is DELIVERED: `prAtL`, `sucAtL`, `∈̇`, `≐`, the
--           connectives.
--   Part 3  `StageBound`, from [LJ-1.176] verbatim.
--   Part 4  `Carve`, THE GRAPH, with the four conjuncts.
--   Part 5  `ShiftGraph`, the L instantiation.
--   Part 6  the C-38 guard, at the concrete ordinal ω.
--
-- ABORT CRITERION, fixed in agents/tasks/LJ-1-198/lj-1.198-report.md
-- section 1 BEFORE this file was written:
--   PRICED               the shift carves with `hasSeparationL` alone.
--   THE CHARGE IS ZERO   A5's machinery already builds it.  Closes at 150.
--   REPLACEMENT REQUIRED the shift needs a `hasReplacementL`.
--   WALLED               name the term nothing supplies.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g"; never
-- committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-198.ProbeLJ1198A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

-- ---------------------------------------------------------------------
-- PART 1.  THE AMBIENT SHIFT.  A6's own object, over the hierarchy.
-- ---------------------------------------------------------------------

module Ambient where

  import L.Ordinal.SquareLaw {ℓ} lem as SQ
  open SQ using ( module FiniteBase )
  import L.Ordinal {ℓ} as Ord
  open Ord using ( ω-ord; #∈ω )
  open import L.Constructible {ℓ} using ( IsOrd )
  import L.Choice.Finite {ℓ} lem as LF
  open LF using ( natOrder )
  import V.Hierarchy {ℓ} as Hier
  open Hier using ( 𝒮ᵥ; ∈-irrefl )
  import V.Model {ℓ} as VModel
  open VModel using ( ∈sucV-elim )
  import V.Presentation {ℓ} as VPres
  open VPres using ( member; fiber; ↪-inj )
  import V.Coding {ℓ} as VCoding
  open VCoding using ( #-inj′ )
  import FOL.ZFStructure as ZF
  open ZF using ( module hPropStructure )
  import Cubical.HITs.CumulativeHierarchy.Base as CHB
  open CHB using ( setIsSet )
  import Cubical.HITs.CumulativeHierarchy.Properties as CH
  open CH using ( ⟪_⟫; ⟪_⟫↪ )
  import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
  open CHC using ( module InfinitySet )
  open InfinitySet {ℓ} using ( ω; sucV; #_ )
  import Cubical.Data.Sigma as Sig
  open Sig using ( ΣPathP; Σ≡Prop )
  import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} as WOBase
  open WOBase using ( leastOf )
  import Cubical.Data.Nat as Nat
  open Nat using ( ℕ; zero; suc )
  import Cubical.Data.Nat.Properties as NatProp
  open NatProp using ( injSuc; znots; snotz )
  import Cubical.Data.Sum as Sum
  open Sum using ( _⊎_; inl; inr )
  import Cubical.Data.Empty as Empty
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

  open hPropStructure 𝒮ᵥ

  _↪_ : Type ℓ → Type ℓ → Type ℓ
  X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

  module ShiftAbs (γ : S) (oγ : IsOrd γ)
                  (γ∉ω : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
                  (numerals : (k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩) where

    NP : (v : S) → ℕ → hProp (ℓ-suc ℓ)
    NP v k = (v ≡ # k) , isSetS v (# k)

    numeralOf : (v : S) → ⟨ v ∈ˢ ω ⟩ → ℕ
    numeralOf v v∈ω = fst (leastOf natOrder lem (NP v) (FiniteBase.ω-mem→numeral v v∈ω))

    numeralOf-spec : (v : S) (v∈ω : ⟨ v ∈ˢ ω ⟩) → v ≡ # (numeralOf v v∈ω)
    numeralOf-spec v v∈ω = fst (snd (leastOf natOrder lem (NP v) (FiniteBase.ω-mem→numeral v v∈ω)))

    numeralOf-uniq : (v : S) (p q : ⟨ v ∈ˢ ω ⟩) → numeralOf v p ≡ numeralOf v q
    numeralOf-uniq v p q = #-inj′ (sym (numeralOf-spec v p) ∙ numeralOf-spec v q)

    v-of : ⟪ sucV γ ⟫ → S
    v-of m = ⟪ sucV γ ⟫↪ m

    v-in-γ : (m : ⟪ sucV γ ⟫) → (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥) → ((v-of m ≡ γ) → Empty.⊥)
           → ⟨ v-of m ∈ˢ γ ⟩
    v-in-γ m ¬ω ¬γ = ∈sucV-elim (snd (v-of m ∈ˢ γ)) (member (sucV γ) m)
      (λ q → q) (λ q → Empty.rec (¬γ q))

    shift-dec : (m : ⟪ sucV γ ⟫)
              → ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
              → (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥) → ⟪ γ ⟫
    shift-dec m (inl v∈ω) _ = fiber γ (numerals (suc (numeralOf (v-of m) v∈ω))) .fst
    shift-dec m (inr _) (inl v≡γ) = fiber γ (numerals 0) .fst
    shift-dec m (inr ¬v∈ω) (inr ¬v≡γ) = fiber γ (v-in-γ m ¬v∈ω ¬v≡γ) .fst

    shift : ⟪ sucV γ ⟫ → ⟪ γ ⟫
    shift m = shift-dec m (lem (v-of m ∈ˢ ω))
      (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))

    shift-top : (m : ⟪ sucV γ ⟫) → (v-of m ≡ γ) → ⟪ γ ⟫↪ (shift m) ≡ # 0
    shift-top m v≡γ = go (lem (v-of m ∈ˢ ω))
      (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
      where
      go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
         → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
         → ⟪ γ ⟫↪ (shift-dec m d e) ≡ # 0
      go (inl v∈ω) _ = Empty.rec (γ∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) v≡γ v∈ω))
      go (inr _) (inl _) = fiber γ (numerals 0) .snd
      go (inr ¬v∈ω) (inr ¬v≡γ) = Empty.rec (¬v≡γ v≡γ)

    shift-num : (m : ⟪ sucV γ ⟫) (v∈ω : ⟨ v-of m ∈ˢ ω ⟩)
              → ⟪ γ ⟫↪ (shift m) ≡ # (suc (numeralOf (v-of m) v∈ω))
    shift-num m v∈ω = go (lem (v-of m ∈ˢ ω))
      (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
      where
      go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
         → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
         → ⟪ γ ⟫↪ (shift-dec m d e) ≡ # (suc (numeralOf (v-of m) v∈ω))
      go (inl v∈ω') _ =
        fiber γ (numerals (suc (numeralOf (v-of m) v∈ω'))) .snd
          ∙ cong (λ k → # (suc k)) (numeralOf-uniq (v-of m) v∈ω' v∈ω)
      go (inr ¬v∈ω) _ = Empty.rec (¬v∈ω v∈ω)

    shift-other : (m : ⟪ sucV γ ⟫) (¬v∈ω : ⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
                (¬v≡γ : (v-of m ≡ γ) → Empty.⊥)
              → ⟪ γ ⟫↪ (shift m) ≡ v-of m
    shift-other m ¬v∈ω ¬v≡γ = go (lem (v-of m ∈ˢ ω))
      (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
      where
      go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
         → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
         → ⟪ γ ⟫↪ (shift-dec m d e) ≡ v-of m
      go (inl v∈ω) _ = Empty.rec (¬v∈ω v∈ω)
      go (inr _) (inl v≡γ) = Empty.rec (¬v≡γ v≡γ)
      go (inr x₁) (inr x) = fiber γ (v-in-γ m x₁ x) .snd

    shift-inj : (m₁ m₂ : ⟪ sucV γ ⟫) → shift m₁ ≡ shift m₂ → m₁ ≡ m₂
    shift-inj m₁ m₂ e = go (lem (v₁ ∈ˢ ω)) (lem ((v₁ ≡ γ) , isSetS v₁ γ))
                            (lem (v₂ ∈ˢ ω)) (lem ((v₂ ≡ γ) , isSetS v₂ γ))
      where
      v₁ : S
      v₁ = v-of m₁
      v₂ : S
      v₂ = v-of m₂
      eqv : ⟪ γ ⟫↪ (shift m₁) ≡ ⟪ γ ⟫↪ (shift m₂)
      eqv = cong (⟪ γ ⟫↪) e
      v₁≡v₂ : v₁ ≡ v₂ → m₁ ≡ m₂
      v₁≡v₂ q = ↪-inj {a = sucV γ} q
      go : ⟨ v₁ ∈ˢ ω ⟩ ⊎ (⟨ v₁ ∈ˢ ω ⟩ → Empty.⊥)
         → (v₁ ≡ γ) ⊎ ((v₁ ≡ γ) → Empty.⊥)
         → ⟨ v₂ ∈ˢ ω ⟩ ⊎ (⟨ v₂ ∈ˢ ω ⟩ → Empty.⊥)
         → (v₂ ≡ γ) ⊎ ((v₂ ≡ γ) → Empty.⊥) → m₁ ≡ m₂
      go (inl a₁) _ (inl a₂) _ = v₁≡v₂
        (numeralOf-spec v₁ a₁ ∙ cong (λ k → # k) (injSuc (#-inj′
          (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-num m₂ a₂))) ∙ sym (numeralOf-spec v₂ a₂))
      go (inl a₁) _ (inr ¬a₂) (inl p₂) = Empty.rec
        (snotz (#-inj′ (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-top m₂ p₂)))
      go (inl a₁) _ (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
        (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
          (#∈ω (suc (numeralOf v₁ a₁)))))
      go (inr ¬a₁) (inl p₁) (inl a₂) _ = Empty.rec
        (znots (#-inj′ (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-num m₂ a₂)))
      go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inl p₂) = v₁≡v₂ (p₁ ∙ sym p₂)
      go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
        (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂) (#∈ω 0)))
      go (inr ¬a₁) (inr ¬p₁) (inl a₂) _ = Empty.rec (¬a₁
        (subst (λ w → ⟨ w ∈ˢ ω ⟩)
          (sym (shift-num m₂ a₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁)
          (#∈ω (suc (numeralOf v₂ a₂)))))
      go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inl p₂) = Empty.rec (¬a₁
        (subst (λ w → ⟨ w ∈ˢ ω ⟩)
          (sym (shift-top m₂ p₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁) (#∈ω 0)))
      go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inr ¬p₂) = v₁≡v₂
        (sym (shift-other m₁ ¬a₁ ¬p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)

    shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
    shift↪ = shift , shift-inj

  module Shiftω = ShiftAbs ω ω-ord (∈-irrefl ω) (λ k → #∈ω k)

-- ---------------------------------------------------------------------
-- L-side imports and vocabulary.
-- ---------------------------------------------------------------------

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; con; var; ∃̇∈; ∃̇_; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd; suc-ord; ω-ord; #∈ω )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; numeralL-suc; sucʟ; sucʟ-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro; sucAtL; sucAtL-adequate )
open import ProbeLJ1134A {ℓ} lem
  using ( injAt; injAt-in; module Small )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The hierarchy numeral successor is the von Neumann successor.  The
-- library's `#` steps by `sucV`, so this is definitional.
sucV-# : (n : ℕ) → sucV (# n) ≡ # (suc n)
sucV-# n = refl

-- The shift value at a member x ∈ˢ D, as a V-set.
val : (D C : S) (sh : ⟪ fst D ⟫ → ⟪ fst C ⟫) (x : S) (m : ⟨ x ∈ˢ D ⟩) → V ℓ
val D C sh x m = ⟪ fst C ⟫↪ (sh (fiber (fst D) m .fst))

-- ---------------------------------------------------------------------
-- PART 2.  THE DESCRIPTION, AND IT TAKES ONE PLACE.
--
-- The graph of the shift is { <x, sh x> : x ∈ sucV γ }.  The value sh x
-- is three cases: a numeral maps to its successor, the top maps to zero,
-- every other member of γ maps to itself.  Every atom is DELIVERED:
-- `prAtL` (the pair reader), `sucAtL` (the successor reader, from
-- src/L/Coding/Environment.lagda.md:136-141), membership, equality and
-- the connectives.  Nothing here is new vocabulary; that is the whole
-- reason the carve needs no `hasReplacementL`.
--
-- De Bruijn: inside `∃̇∈ (con D)`, the bound x is 0 and p is 1.  Inside
-- the inner `∃̇`, the bound y is 0, x is 1, p is 2.
-- ---------------------------------------------------------------------

shiftCase1 : S → Formula S 3
shiftCase1 ω = (var (suc zero) ∈̇ con ω) ∧̇ sucAtL (suc zero) zero

shiftCase2 : S → S → Formula S 3
shiftCase2 γ z = (var (suc zero) ≐ con γ) ∧̇ (var zero ≐ con z)

shiftCase3 : S → S → Formula S 3
shiftCase3 γ ω = (var (suc zero) ∈̇ con γ) ∧̇ ¬̇ (var (suc zero) ∈̇ con ω)
               ∧̇ (var zero ≐ var (suc zero))

shiftRel : S → S → S → Formula S 3
shiftRel γ ω z = shiftCase1 ω ∨̇ (shiftCase2 γ z ∨̇ shiftCase3 γ ω)

shiftFo : S → S → S → S → Formula S 1
shiftFo D γ ω z =
  ∃̇∈ (con D) (∃̇ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ shiftRel γ ω z))

-- The reading, and it matches the ambient shift case for case.
module ShiftFo (D C γ ω z : S)
               (sh : ⟪ fst D ⟫ → ⟪ fst C ⟫)
               (shInj : (m n : ⟪ fst D ⟫) → sh m ≡ sh n → m ≡ n)
               (shNum : (m : ⟪ fst D ⟫) (v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩)
                      → ⟪ fst C ⟫↪ (sh m) ≡ sucV (⟪ fst D ⟫↪ m))
               (shTop : (m : ⟪ fst D ⟫) (v≡γ : ⟪ fst D ⟫↪ m ≡ fst γ)
                      → ⟪ fst C ⟫↪ (sh m) ≡ fst z)
               (shOther : (m : ⟪ fst D ⟫) (¬v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩ → Empty.⊥)
                        (¬v≡γ : (⟪ fst D ⟫↪ m ≡ fst γ) → Empty.⊥)
                        → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m)
               (D-in-dec : (x : S) → ⟨ x ∈ˢ D ⟩ → ((fst x ≡ fst γ) → Empty.⊥)
                         → ⟨ fst x ∈ fst γ ⟩) where

  private
    fb : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟪ fst D ⟫
    fb x m = fiber (fst D) m .fst

    fb-eq : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟪ fst D ⟫↪ (fb x m) ≡ fst x
    fb-eq x m = fiber (fst D) m .snd

    prAtRead : (p x y : S) → ⟨ (y ∷ x ∷ p ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
             ≡ (fst p ≡ pr (fst x) (fst y))
    prAtRead p x y = cong ⟨_⟩ (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ p ∷ []))

    sucAtRead : (p x y : S) → ⟨ (y ∷ x ∷ p ∷ []) ⊨ sucAtL (suc zero) zero ⟩
              ≡ (fst y ≡ sucV (fst x))
    sucAtRead p x y = cong ⟨_⟩ (sucAtL-adequate (suc zero) zero (y ∷ x ∷ p ∷ []))

  val-irrel : (x : S) (m m' : ⟨ x ∈ˢ D ⟩) → val D C sh x m ≡ val D C sh x m'
  val-irrel x m m' = cong (⟪ fst C ⟫↪) (cong sh (↪-inj {a = fst D} (fb-eq x m ∙ sym (fb-eq x m'))))

  private
    case1-val : (x y : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ x ∈ˢ ω ⟩ → fst y ≡ sucV (fst x)
              → fst y ≡ val D C sh x m
    case1-val x y m x∈ω y≡sx =
      y≡sx ∙ sym (shNum (fb x m) v∈ω' ∙ cong sucV (fb-eq x m))
      where
      v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩
      v∈ω' = subst (λ w → ⟨ w ∈ fst ω ⟩) (sym (fb-eq x m)) x∈ω

    case2-val : (x y : S) (m : ⟨ x ∈ˢ D ⟩) → fst x ≡ fst γ → fst y ≡ fst z
              → fst y ≡ val D C sh x m
    case2-val x y m x≡γ y≡z = y≡z ∙ sym (shTop (fb x m) (fb-eq x m ∙ x≡γ))

    case3-val : (x y : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ x ∈ˢ γ ⟩
              → (⟨ x ∈ˢ ω ⟩ → Empty.⊥) → fst y ≡ fst x → fst y ≡ val D C sh x m
    case3-val x y m x∈γ ¬x∈ω y≡x =
      y≡x ∙ sym (shOther (fb x m) ¬v∈ω' ¬v≡γ' ∙ fb-eq x m)
      where
      ¬v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩ → Empty.⊥
      ¬v∈ω' h = ¬x∈ω (subst (λ w → ⟨ w ∈ fst ω ⟩) (fb-eq x m) h)
      ¬v≡γ' : (⟪ fst D ⟫↪ (fb x m) ≡ fst γ) → Empty.⊥
      ¬v≡γ' h = ∈-irrefl (fst γ) (subst (λ w → ⟨ w ∈ fst γ ⟩) (sym (fb-eq x m) ∙ h) x∈γ)

    relVal : (p x y : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftRel γ ω z ⟩
           → fst y ≡ val D C sh x m
    relVal p x y m rel = PT.rec (setIsSet (fst y) (val D C sh x m)) go rel
      where
      go : ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase1 ω ⟩ ⊎
           ∥ ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase2 γ z ⟩ ⊎
             ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase3 γ ω ⟩ ∥₁
         → fst y ≡ val D C sh x m
      go (inl c1) = case1-val x y m (fst c1) (subst (λ T → T) (sucAtRead p x y) (snd c1))
      go (inr c23) = PT.rec (setIsSet (fst y) (val D C sh x m)) go23 c23
        where
        go23 : ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase2 γ z ⟩ ⊎
               ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase3 γ ω ⟩
             → fst y ≡ val D C sh x m
        go23 (inl c2) = case2-val x y m (fst c2) (snd c2)
        go23 (inr c3) = case3-val x y m (fst c3) (fst (snd c3)) (snd (snd c3))

  out : (p : S) → ⟨ (p ∷ []) ⊨ shiftFo D γ ω z ⟩
      → ∥ Σ[ x ∈ S ] Σ[ k ∈ ⟪ fst D ⟫ ]
          ((⟪ fst D ⟫↪ k ≡ fst x) × (fst p ≡ pr (fst x) (⟪ fst C ⟫↪ (sh k)))) ∥₁
  out p h = PT.map step h
    where
    step : Σ[ x ∈ S ] (⟨ x ∈ˢ D ⟩ × ⟨ (x ∷ p ∷ []) ⊨ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ shiftRel γ ω z)) ⟩)
         → Σ[ x ∈ S ] Σ[ k ∈ ⟪ fst D ⟫ ]
             ((⟪ fst D ⟫↪ k ≡ fst x) × (fst p ≡ pr (fst x) (⟪ fst C ⟫↪ (sh k))))
    step (x , (m , hy)) = x , fiber (fst D) m .fst ,
      ( snd (fiber (fst D) m)
      , PT.rec (setIsSet (fst p) (pr (fst x) (⟪ fst C ⟫↪ (sh (fiber (fst D) m .fst))))) go hy )
      where
      go : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ p ∷ []) ⊨ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ shiftRel γ ω z) ⟩
         → fst p ≡ pr (fst x) (⟪ fst C ⟫↪ (sh (fiber (fst D) m .fst)))
      go (y , (prAtH , relH)) = subst (λ T → T) (prAtRead p x y) prAtH
        ∙ cong (pr (fst x)) (relVal p x y m relH)

  into : (p x : S) (m : ⟨ x ∈ˢ D ⟩) → fst p ≡ pr (fst x) (val D C sh x m)
       → ⟨ (p ∷ []) ⊨ shiftFo D γ ω z ⟩
  into p x m e = ∣ x , (m , ∣ y , (prAtPf , relPf) ∣₁) ∣₁
    where
    y : S
    y = val D C sh x m
      , isL-trans {x = fst C} {y = val D C sh x m}
          (member (fst C) (sh (fiber (fst D) m .fst))) (snd C)

    prAtPf : ⟨ (y ∷ x ∷ p ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
    prAtPf = subst (λ T → T) (sym (prAtRead p x y)) e

    relPf : ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftRel γ ω z ⟩
    relPf = go (lem (fst x ∈ fst ω)) (lem ((fst x ≡ fst γ) , setIsSet (fst x) (fst γ)))
      where
      x∈γPf : ((fst x ≡ fst γ) → Empty.⊥) → ⟨ fst x ∈ fst γ ⟩
      x∈γPf ¬v≡γ = D-in-dec x m ¬v≡γ

      sucPf : ⟨ fst x ∈ fst ω ⟩ → ⟨ (y ∷ x ∷ p ∷ []) ⊨ sucAtL (suc zero) zero ⟩
      sucPf x∈ω = subst (λ T → T) (sym (sucAtRead p x y))
        (shNum (fb x m) v∈ω' ∙ cong sucV (fb-eq x m))
        where
        v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩
        v∈ω' = subst (λ w → ⟨ w ∈ fst ω ⟩) (sym (fb-eq x m)) x∈ω

      topPf : (fst x ≡ fst γ) → ⟨ (y ∷ x ∷ p ∷ []) ⊨ (var zero ≐ con z) ⟩
      topPf x≡γ = shTop (fb x m) (fb-eq x m ∙ x≡γ)

      idPf : (⟨ fst x ∈ fst ω ⟩ → Empty.⊥) → ((fst x ≡ fst γ) → Empty.⊥)
           → ⟨ (y ∷ x ∷ p ∷ []) ⊨ (var zero ≐ var (suc zero)) ⟩
      idPf ¬v∈ω ¬v≡γ = shOther (fb x m) ¬v∈ω' ¬v≡γ' ∙ fb-eq x m
        where
        ¬v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩ → Empty.⊥
        ¬v∈ω' h = ¬v∈ω (subst (λ w → ⟨ w ∈ fst ω ⟩) (fb-eq x m) h)
        ¬v≡γ' : (⟪ fst D ⟫↪ (fb x m) ≡ fst γ) → Empty.⊥
        ¬v≡γ' h = ¬v≡γ (sym (fb-eq x m) ∙ h)

      go : ⟨ fst x ∈ fst ω ⟩ ⊎ (⟨ fst x ∈ fst ω ⟩ → Empty.⊥)
         → (fst x ≡ fst γ) ⊎ ((fst x ≡ fst γ) → Empty.⊥)
         → ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftRel γ ω z ⟩
      go (inl x∈ω) _ = ∣ inl ( x∈ω , sucPf x∈ω ) ∣₁
      go (inr ¬x∈ω) (inl x≡γ) = ∣ inr ∣ inl ( x≡γ , topPf x≡γ ) ∣₁ ∣₁
      go (inr ¬x∈ω) (inr ¬x≡γ) = ∣ inr ∣ inr ( x∈γPf ¬x≡γ , ¬x∈ω , idPf ¬x∈ω ¬x≡γ ) ∣₁ ∣₁

-- ---------------------------------------------------------------------
-- PART 3.  THE BOUND, GENERIC IN THE INDEX TYPE AND THE FAMILY.
-- [LJ-1.176] verbatim.
-- ---------------------------------------------------------------------

module StageBound (I : Type ℓ) (g : I → S) where

  private
    stg : I → V ℓ
    stg i = stage (fst (g i)) (snd (g i))

    b : Σ[ β ∈ V ℓ ] (IsOrd β × ((i : I) → ⟨ stg i ∈ β ⟩))
    b = boundingOrd I stg (λ i → stage-ord (fst (g i)) (snd (g i)))

  opaque
    β : V ℓ
    β = b .fst

    oβ : IsOrd β
    oβ = b .snd .fst

    bnd : S
    bnd = LsetS β oβ

    below : (i : I) → ⟨ fst (g i) ∈ fst bnd ⟩
    below i = Lset-mono {α = β} {β = stg i} (b .snd .snd i)
                (stage-mem (fst (g i)) (snd (g i)))

-- ---------------------------------------------------------------------
-- PART 4.  THE GRAPH, CARVED.  NOT ONE `hasReplacementL`.
-- ---------------------------------------------------------------------

module Carve (D C γ ω z : S)
             (sh : ⟪ fst D ⟫ → ⟪ fst C ⟫)
             (shInj : (m n : ⟪ fst D ⟫) → sh m ≡ sh n → m ≡ n)
             (shNum : (m : ⟪ fst D ⟫) (v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩)
                    → ⟪ fst C ⟫↪ (sh m) ≡ sucV (⟪ fst D ⟫↪ m))
             (shTop : (m : ⟪ fst D ⟫) (v≡γ : ⟪ fst D ⟫↪ m ≡ fst γ)
                    → ⟪ fst C ⟫↪ (sh m) ≡ fst z)
             (shOther : (m : ⟪ fst D ⟫) (¬v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩ → Empty.⊥)
                      (¬v≡γ : (⟪ fst D ⟫↪ m ≡ fst γ) → Empty.⊥)
                      → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m)
             (D-in-dec : (x : S) → ⟨ x ∈ˢ D ⟩ → ((fst x ≡ fst γ) → Empty.⊥)
                       → ⟨ fst x ∈ fst γ ⟩)
             (bnd : S)
             (below : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ pr (fst x) (val D C sh x m) ∈ fst bnd ⟩)
             (sep : (b : S) (φ : Formula S 1)
                  → isContr (SetOf (λ z → (z ∈ˢ b) ⊓ ((z ∷ []) ⊨ φ)))) where

  module Fo = ShiftFo D C γ ω z sh shInj shNum shTop shOther D-in-dec

  private
    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

  opaque
    G : S
    G = fst (fst (sep bnd (shiftFo D γ ω z)))

    G-spec : (w : S) → (w ∈ˢ G) ≡ ((w ∈ˢ bnd) ⊓ ((w ∷ []) ⊨ shiftFo D γ ω z))
    G-spec = snd (fst (sep bnd (shiftFo D γ ω z)))

  G-out : (z : S) → ⟨ z ∈ˢ G ⟩
        → ∥ Σ[ x ∈ S ] Σ[ k ∈ ⟪ fst D ⟫ ]
            ((⟪ fst D ⟫↪ k ≡ fst x) × (fst z ≡ pr (fst x) (⟪ fst C ⟫↪ (sh k)))) ∥₁
  G-out z h = Fo.out z (snd (subst ⟨_⟩ (G-spec z) h))

  G-in : (z x : S) (m : ⟨ x ∈ˢ D ⟩) → fst z ≡ pr (fst x) (val D C sh x m) → ⟨ z ∈ˢ G ⟩
  G-in z x m e = subst ⟨_⟩ (sym (G-spec z))
    ( subst (λ w → ⟨ w ∈ fst bnd ⟩) (sym e) (below x m)
    , Fo.into z x m e )

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
           → ∥ Σ[ k ∈ ⟪ fst D ⟫ ] ((⟪ fst D ⟫↪ k ≡ fst x) × (fst y ≡ ⟪ fst C ⟫↪ (sh k))) ∥₁
  pair-out x y h = PT.map step (G-out (prʟ x y) h')
    where
    h' : ⟨ prʟ x y ∈ˢ G ⟩
    h' = subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst x y)) h
    step : Σ[ u ∈ S ] Σ[ k ∈ ⟪ fst D ⟫ ]
             ((⟪ fst D ⟫↪ k ≡ fst u) × (fst (prʟ x y) ≡ pr (fst u) (⟪ fst C ⟫↪ (sh k))))
         → Σ[ k ∈ ⟪ fst D ⟫ ] ((⟪ fst D ⟫↪ k ≡ fst x) × (fst y ≡ ⟪ fst C ⟫↪ (sh k)))
    step (u , (k , (kEq , e))) = k , ( kEq ∙ sym xu , yu )
      where
      q : (fst x ≡ fst u) × (fst y ≡ ⟪ fst C ⟫↪ (sh k))
      q = pr-inj (sym (prʟ-fst x y) ∙ e)
      xu = fst q
      yu = snd q

  pair-in : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ pr (fst x) (val D C sh x m) ∈ fst G ⟩
  pair-in x m = subst (λ w → ⟨ w ∈ fst G ⟩) (prʟ-fst x y) (G-in (prʟ x y) x m (prʟ-fst x y))
    where
    y : S
    y = toC (sh (fiber (fst D) m .fst))

  -- THE FOUR CONJUNCTS.
  γ2 : S ^ 2
  γ2 = G ∷ D ∷ []

  sv : ⟨ γ2 ⊨ svAt zero ⟩
  sv = svAt-in zero γ2 go
    where
    go : (x y y' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ pr (fst x) (fst y') ∈ fst G ⟩ → fst y ≡ fst y'
    go x y y' p q = PT.rec (setIsSet (fst y) (fst y'))
      (λ r → PT.rec (setIsSet (fst y) (fst y'))
        (λ r' → sym (snd r)
          ∙ cong (⟪ fst C ⟫↪) (cong sh (↪-inj {a = fst D} (fst r ∙ sym (fst r'))))
          ∙ snd r')
        (pair-out x y' q))
      (pair-out x y p)

  ij : ⟨ γ2 ⊨ injAt zero ⟩
  ij = injAt-in zero γ2 go
    where
    go : (y x x' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ pr (fst x') (fst y) ∈ fst G ⟩ → fst x ≡ fst x'
    go y x x' p q = PT.rec (setIsSet (fst x) (fst x'))
      (λ r → PT.rec (setIsSet (fst x) (fst x'))
        (λ r' → sym (fst r)
          ∙ cong ⟪ fst D ⟫↪ (shInj (r .fst) (r' .fst) (↪-inj {a = fst C} (snd r ∙ sym (snd r'))))
          ∙ fst r')
        (pair-out x' y q))
      (pair-out x y p)

  dm : ⟨ γ2 ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ2 (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩ → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
          (λ r → subst (λ w → ⟨ w ∈ fst D ⟩) (fst r) (member (fst D) (r .fst)))
          (pair-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ toC (sh (fiber (fst D) m .fst)) , pair-in x m ∣₁

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst C ⟩
  ran x y h = PT.rec (snd (fst y ∈ fst C))
    (λ r → subst (λ w → ⟨ w ∈ fst C ⟩) (snd r) (member (fst C) (sh (r .fst))))
    (pair-out x y h)

  -- THE READBACK, and it is the shift.  C-38.
  private
    module Sm = Small G D C sv dm ij ran

  opaque
    shiftFun : ⟪ fst D ⟫ → ⟪ fst C ⟫
    shiftFun = Sm.small

    shiftFun-inj : (m n : ⟪ fst D ⟫) → shiftFun m ≡ shiftFun n → m ≡ n
    shiftFun-inj = Sm.small-inj

    shiftFun-val : (m : ⟪ fst D ⟫) → shiftFun m ≡ sh m
    shiftFun-val m = ↪-inj {a = fst C} (snd (Sm.fib m) ∙ val')
      where
      val' : fst (Sm.E.toFun (Sm.at m)) ≡ ⟪ fst C ⟫↪ (sh m)
      val' = PT.rec (setIsSet (fst (Sm.E.toFun (Sm.at m))) (⟪ fst C ⟫↪ (sh m)))
        (λ r → snd r ∙ cong (⟪ fst C ⟫↪) (cong sh (↪-inj {a = fst D} (fst r))))
        (pair-out (Sm.toS m) (Sm.E.toFun (Sm.at m)) (Sm.E.toFun-graph (Sm.at m)))

-- ---------------------------------------------------------------------
-- PART 5.  THE L INSTANTIATION.  Supplies the bound, the three-case
-- adequacy of the ambient shift, and `hasSeparationL`.
-- ---------------------------------------------------------------------

module ShiftGraph (γ : S) (oγ : IsOrd (fst γ))
                  (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
                  (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩) where

  module SA = Ambient.ShiftAbs (fst γ) oγ γ∉ω numerals

  D : S
  D = sucV (fst γ) , subst isL (sym (sucʟ-fst γ)) (snd (sucʟ γ))

  C : S
  C = γ

  sh : ⟪ fst D ⟫ → ⟪ fst C ⟫
  sh = SA.shift

  private
    shInj : (m n : ⟪ fst D ⟫) → sh m ≡ sh n → m ≡ n
    shInj = SA.shift-inj

    shNum : (m : ⟪ fst D ⟫) (v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ωʟ ⟩)
          → ⟪ fst C ⟫↪ (sh m) ≡ sucV (⟪ fst D ⟫↪ m)
    shNum m v∈ω = SA.shift-num m v∈ω
      ∙ sym (sucV-# (SA.numeralOf (SA.v-of m) v∈ω))
      ∙ cong sucV (sym (SA.numeralOf-spec (SA.v-of m) v∈ω))

    shTop : (m : ⟪ fst D ⟫) (v≡γ : ⟪ fst D ⟫↪ m ≡ fst γ)
          → ⟪ fst C ⟫↪ (sh m) ≡ fst ∅ʟ
    shTop m v≡γ = SA.shift-top m v≡γ

    shOther : (m : ⟪ fst D ⟫) (¬v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ωʟ ⟩ → Empty.⊥)
            (¬v≡γ : (⟪ fst D ⟫↪ m ≡ fst γ) → Empty.⊥)
            → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m
    shOther = SA.shift-other

    D-in-dec : (x : S) → ⟨ x ∈ˢ D ⟩ → ((fst x ≡ fst γ) → Empty.⊥) → ⟨ fst x ∈ fst γ ⟩
    D-in-dec x m ¬v≡γ = ∈sucV-elim {A = fst γ} {x = fst x} (snd (fst x ∈ fst γ)) m
      (λ q → q) (λ q → Empty.rec (¬v≡γ q))

    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

    dg : ⟪ fst D ⟫ → S
    dg m = prʟ (toD m) (toC (sh m))

    module SB = StageBound ⟪ fst D ⟫ dg

    bel : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ pr (fst x) (val D C sh x m) ∈ fst SB.bnd ⟩
    bel x m = subst (λ w → ⟨ w ∈ fst SB.bnd ⟩) pa (SB.below (fiber (fst D) m .fst))
      where
      pa : fst (dg (fiber (fst D) m .fst)) ≡ pr (fst x) (val D C sh x m)
      pa = prʟ-fst (toD (fiber (fst D) m .fst)) (toC (sh (fiber (fst D) m .fst)))
         ∙ cong₂ pr (snd (fiber (fst D) m)) refl

  open Carve D C γ ωʟ ∅ʟ sh shInj shNum shTop shOther D-in-dec SB.bnd bel hasSeparationL public

-- ---------------------------------------------------------------------
-- PART 6.  THE C-38 GUARD, at the concrete ordinal ω.
-- ---------------------------------------------------------------------

module Witness where

  module SG = ShiftGraph ωʟ ω-ord (∈-irrefl (fst ωʟ)) (λ k → #∈ω k)

  -- The domain is sucV ω, which is inhabited (0 ∈ sucV ω).
  zero∈D : ⟨ fst (numeralL 0) ∈ fst SG.D ⟩
  zero∈D = ∈sucV-inl {A = fst ωʟ} {x = fst (numeralL 0)} (#∈ω 0)

  -- The graph HOLDS the pair <0, 1>.  Not vacuous.
  inG : ⟨ pr (fst (numeralL 0)) (fst (numeralL 1)) ∈ fst SG.G ⟩
  inG = SG.pair-in (numeralL 0) zero∈D

  -- The graph RUNS: an honest injection ⟪sucV ω⟫ ↪ ⟪ω⟫.
  theShift : ⟪ fst SG.D ⟫ → ⟪ fst SG.C ⟫
  theShift = SG.shiftFun

  theShift-inj : (m n : ⟪ fst SG.D ⟫) → theShift m ≡ theShift n → m ≡ n
  theShift-inj = SG.shiftFun-inj

  -- AND IT IS THE SHIFT.  The value at 0 is the numeral 1.
  theShift-val0 : theShift (fiber (fst SG.D) zero∈D .fst)
                ≡ SG.sh (fiber (fst SG.D) zero∈D .fst)
  theShift-val0 = SG.shiftFun-val (fiber (fst SG.D) zero∈D .fst)
