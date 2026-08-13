{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.156] Probe A.  DOES A5 NEED `CSB` AT ALL?
--
-- [LJ-1.107] states leastness over BIJECTIONS.  Its `LeastCard` picks the
-- least `γ ∈ sucV α` with `∥ ⟪ γ ⟫ ≃ ⟪ α ⟫ ∥₁`
-- (agents/tasks/LJ-1-107/ProbeLJ1107A.agda:219-226).  Every refutation must
-- therefore MANUFACTURE an equivalence out of two injections, and that is
-- what `CSB` does, at three sites (`:490`, `:519`, `:530`).
--
-- [LJ-1.136] section 9.1 INFERRED that the bijection is the ONLY reason
-- `CSB` is in the chain, and that leastness over INJECTIONS refutes all
-- three sites directly (agents/tasks/LJ-1-136/lj-1.136-report.md:504-526).
-- The claim was never tested.  This file tests it.
--
-- WHAT IS BUILT.
--   Part 1  `NumeralPresentation`, the pairing on `ω`.  From [LJ-1.106],
--           so the base case is REAL and not a parameter.
--   Part 2  `LeastCardInj`.  THE ONE DESIGN CHANGE: the predicate is
--           `∥ ⟪ α ⟫ ↪ ⟪ γ ⟫ ∥₁`, an INJECTION, not an equivalence.
--   Part 3  `ShiftAbs` and `Shiftω`, from [LJ-1.107] verbatim.  They give
--           the REAL injection `⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`.
--   Part 4  `InitialCase`.  SITE 1 (`noinj²`) and SITE 2 (`succ-closure`).
--   Part 5  `NonInitial`.  SITE 3.
--   Part 6  `Chain`, assembled.
--   Part 7  THE C-38 GUARD, at a concrete pair of ordinals.
--
-- WHAT IS NOT BUILT, and that is the finding: there is no `CSB` module,
-- there is no `Cn` recursion, there is no `≃` anywhere in this file, and
-- `Cubical.Foundations.Equiv` is not imported.  `Base.Classical.lowerLEM`
-- is not imported either; [LJ-1.107] needed it only inside `CSB`.
--
-- ABORT CRITERION, fixed in agents/tasks/LJ-1-156/lj-1.156-report.md
-- section 1 BEFORE this file was written:
--   DISSOLVED  the file elaborates, `--safe`, exit 0, no `CSB`, no
--              manufactured equivalence, all three sites close.
--   NEEDED, CHEAP      a site wants an object `CSB` gives, but it carves.
--   NEEDED, EXPENSIVE  a site forces the back-and-forth graph.
--   WALL       a heap exhaustion under -M8g.  The cap is never raised.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-156.ProbeLJ1156A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase; ordSWO )
import L.Ordinal {ℓ} as Ord
open Ord using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Constructible {ℓ} using ( IsOrd )
import L.Ordinal.Linear {ℓ} lem as Lin
open Lin using ( ord-tri )
import FOL.Count {ℓ} as Count
import L.Choice.Finite {ℓ} lem as LF
open LF using ( natOrder )
import V.Hierarchy {ℓ} as Hier
open Hier using ( 𝒮ᵥ; ∈-irrefl; ∈-induction )
import V.Model {ℓ} as VModel
open VModel using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
import V.Presentation {ℓ} as VPres
open VPres using ( member; fiber; ↪-inj )
import V.Coding {ℓ} as VCoding
open VCoding using ( #-inj′ )
import FOL.ZFStructure as ZF
open ZF using ( module hPropStructure )
import Cubical.HITs.CumulativeHierarchy.Base as CHB
open CHB using ( setIsSet )
import Cubical.HITs.CumulativeHierarchy.Properties as CH
open CH using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
open CHC using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Functions.Embedding as Emb
open Emb using ( isEmbedding→hasPropFibers; Embedding-into-isSet→isSet )
import Cubical.Data.Sigma as Sig
open Sig using ( ΣPathP; Σ≡Prop )
import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} as WOBase
open WOBase using ( SWO; IsLeast; leastOf; module SWO )
import Cubical.Data.Nat as Nat
open Nat using ( ℕ; zero; suc )
import Cubical.Data.Nat.Properties as NatProp
open NatProp using ( injSuc; znots; snotz )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum.Properties as SumProp
open SumProp using ( isProp⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ

-- The injection type.  [LJ-1.107] took this from ProbeLJ194A; it is three
-- tokens and it stays local, so this file depends on no other probe.
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

isSet⟪_⟫ : (a : S) → isSet ⟪ a ⟫
isSet⟪ a ⟫ = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

-- =====================================================================
-- PART 1.  The pairing on omega.  [LJ-1.106], verbatim, minus `ω≃ℕ`.
--   The base case of the chain.  It is REAL rather than a parameter, so
--   that no step of the induction rests on an interface nothing
--   satisfies (C-38).
-- =====================================================================
module NumeralPresentation where

  open FiniteBase

  numeralω : ℕ → ⟪ ω ⟫
  numeralω k = fiber ω {x = # k} (#∈ω k) .fst

  numeralω-inj : (k k' : ℕ) → numeralω k ≡ numeralω k' → k ≡ k'
  numeralω-inj k k' e = #-inj′ (sym (fiber ω {x = # k} (#∈ω k) .snd)
    ∙ cong (⟪ ω ⟫↪) e ∙ fiber ω {x = # k'} (#∈ω k') .snd)

  isPropNumeralWit : (δ : S) → isProp (Σ[ n ∈ ℕ ] (# n ≡ δ))
  isPropNumeralWit δ (n , p) (n' , p') =
    Σ≡Prop (λ k → isSetS (# k) δ) (#-inj′ (p ∙ sym p'))

  to-wit : (m : ⟪ ω ⟫) → Σ[ n ∈ ℕ ] (# n ≡ ⟪ ω ⟫↪ m)
  to-wit m = PT.rec (isPropNumeralWit (⟪ ω ⟫↪ m)) hit
    (ω-mem→numeral (⟪ ω ⟫↪ m)
      (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ω} .snd (∈ₛ⟪ ω ⟫↪ m)))
    where
    hit : Σ[ n ∈ ℕ ] (⟪ ω ⟫↪ m ≡ # n) → Σ[ n ∈ ℕ ] (# n ≡ ⟪ ω ⟫↪ m)
    hit (n , p) = n , sym p

  to : ⟪ ω ⟫ → ℕ
  to m = to-wit m .fst

  to∘numeralω : (k : ℕ) → to (numeralω k) ≡ k
  to∘numeralω k = #-inj′ (to-wit (numeralω k) .snd
    ∙ fiber ω {x = # k} (#∈ω k) .snd)

  numeralω∘to : (m : ⟪ ω ⟫) → numeralω (to m) ≡ m
  numeralω∘to m = cong fst (isEmbedding→hasPropFibers isEmb⟪ ω ⟫↪ (⟪ ω ⟫↪ m)
    (numeralω (to m) , fiber ω {x = # (to m)} (#∈ω (to m)) .snd ∙ to-wit m .snd)
    (m , refl))

  to-inj : (m n : ⟪ ω ⟫) → to m ≡ to n → m ≡ n
  to-inj m n e = sym (numeralω∘to m) ∙ cong numeralω e ∙ numeralω∘to n

  pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
  pairω (m , n) = numeralω (Count.pair (to m) (to n))

  pairω-inj : (x y : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω x ≡ pairω y → x ≡ y
  pairω-inj (m , n) (m' , n') e =
    ΣPathP ( to-inj m m' (fst (Count.pair-inj (to m) (to n) (to m') (to n') nm))
           , to-inj n n' (snd (Count.pair-inj (to m) (to n) (to m') (to n') nm)) )
    where
    nm : Count.pair (to m) (to n) ≡ Count.pair (to m') (to n')
    nm = numeralω-inj (Count.pair (to m) (to n)) (Count.pair (to m') (to n')) e

-- =====================================================================
-- PART 2.  THE ONE DESIGN CHANGE.
--
--   [LJ-1.107]:  Eq  γ = ⟪ γ ⟫ ≃ ⟪ α ⟫        an EQUIVALENCE
--   here:        Inj γ = ⟪ α ⟫ ↪ ⟪ γ ⟫        an INJECTION
--
--   Everything else in this module is [LJ-1.107]'s `LeastCard` with the
--   predicate swapped.  Non-emptiness is the IDENTITY injection at α
--   itself, where [LJ-1.107] used `idEquiv`.  `κ-min-at` is the same
--   three-line transport.
--
--   The direction matters and is not free.  `⟪ α ⟫ ↪ ⟪ γ ⟫` says "α is no
--   bigger than γ", so the LEAST such γ is the cardinal.  The opposite
--   direction, `⟪ γ ⟫ ↪ ⟪ α ⟫`, is satisfied by every member of α and its
--   least element is 0.
-- =====================================================================
module LeastCardInj (α : S) (oα : IsOrd α) where

  Inj : S → Type ℓ
  Inj γ = ⟪ α ⟫ ↪ ⟪ γ ⟫

  InjP : S → hProp ℓ
  InjP γ = ∥ Inj γ ∥₁ , squash₁

  InjP' : ⟪ sucV α ⟫ → hProp ℓ
  InjP' γ = InjP (⟪ sucV α ⟫↪ γ)

  w : SWO (⟪ sucV α ⟫)
  w = ordSWO (sucV α) (suc-ord oα)

  -- the identity injection at α itself; [LJ-1.107] used `idEquiv` here
  self : ⟪ sucV α ⟫
  self = fiber (sucV α) (self∈sucV α) .fst

  self-eq : ⟪ sucV α ⟫↪ self ≡ α
  self-eq = fiber (sucV α) (self∈sucV α) .snd

  idInj : ⟪ α ⟫ ↪ ⟪ α ⟫
  idInj = (λ x → x) , (λ x y e → e)

  nonempty : ∥ Σ[ b ∈ ⟪ sucV α ⟫ ] ⟨ InjP' b ⟩ ∥₁
  nonempty = ∣ self , subst (λ v → ∥ ⟪ α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym self-eq) ∣ idInj ∣₁ ∣₁

  least : Σ[ γ ∈ ⟪ sucV α ⟫ ] IsLeast w InjP' γ
  least = leastOf w lem InjP' nonempty

  γ-card : ⟪ sucV α ⟫
  γ-card = fst least

  κ : S
  κ = ⟪ sucV α ⟫↪ γ-card

  oκ : IsOrd κ
  oκ = mem-ord {A = sucV α} (suc-ord oα) κ (member (sucV α) γ-card)

  κ∈sα : ⟨ κ ∈ˢ sucV α ⟩
  κ∈sα = member (sucV α) γ-card

  -- the witness, and it is an INJECTION, not a truncated equivalence
  κ-inj : ∥ ⟪ α ⟫ ↪ ⟪ κ ⟫ ∥₁
  κ-inj = fst (snd least)

  κ-min : (b : ⟪ sucV α ⟫) → ⟨ InjP' b ⟩ → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

  -- the leastness at a member δ of κ: δ < κ with α ↪ δ is absurd
  κ-min-at : (δ : S) → ⟨ δ ∈ˢ κ ⟩ → ∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁ → Empty.⊥
  κ-min-at δ δ∈κ α↪δ = κ-min b bInjP b<γ
    where
    δ∈sα : ⟨ δ ∈ˢ sucV α ⟩
    δ∈sα = suc-ord oα .fst {x = κ} {y = δ} δ∈κ (member (sucV α) γ-card)
    b : ⟪ sucV α ⟫
    b = fiber (sucV α) δ∈sα .fst
    bδ : ⟪ sucV α ⟫↪ b ≡ δ
    bδ = fiber (sucV α) δ∈sα .snd
    bInjP : ⟨ InjP' b ⟩
    bInjP = subst (λ v → ∥ ⟪ α ⟫ ↪ ⟪ v ⟫ ∥₁) (sym bδ) α↪δ
    b<γ : SWO._<∙_ w b γ-card
    b<γ = subst (λ z → ⟨ z ∈ˢ κ ⟩) (sym bδ) δ∈κ

-- =====================================================================
-- PART 3.  The successor absorption, from [LJ-1.107] verbatim.
--   For infinite γ, sucV γ injects into γ: the numerals inside γ shift
--   up by one, the top maps to the numeral zero, and every other member
--   maps to itself.
--
--   [LJ-1.107] then fed this to `CSB` together with the inclusion
--   γ ↪ sucV γ, to get an EQUIVALENCE.  Here the shift is used raw, and
--   the inclusion is never built.
-- =====================================================================
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

  -- THE INJECTION, raw.  [LJ-1.107] never used this form: it fed
  -- `shift` and `shift-inj` to `CSB` together with the inclusion.
  shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
  shift↪ = shift , shift-inj

module Shiftω = ShiftAbs ω ω-ord (∈-irrefl ω) (λ k → #∈ω k)

-- =====================================================================
-- PART 4.  THE INITIAL CASE.  SITES 1 AND 2.
--
--   `leastα` is now stated over INJECTIONS.  Compare
--   agents/tasks/LJ-1-107/ProbeLJ1107A.agda:465, which reads
--     leastα : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁ → Empty.⊥
--   and forced both sites through `CSB`.
-- =====================================================================
module InitialCase (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩)
                   (leastα : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁ → Empty.⊥)
                   (ih : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β
                       → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq β) where

  -- SITE 1, the square clause.  [LJ-1.107]:490 built `h`, then `j` (the
  -- inclusion β ↪ α), then `CSB.csb`, then `invEquiv`, then `leastα`.
  -- Here `h` IS the injection `leastα` wants.  `j`, `j-inj` and `CSB` are
  -- all dead, so this site loses three constructions, not one.
  noinj² : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
         → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
         → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
  noinj² β oβ β∈α ω∈β f f-inj = leastα β β∈α ∣ h , h-inj ∣₁
    where
    β∉ω : ⟨ β ∈ˢ ω ⟩ → Empty.⊥
    β∉ω β∈ω = ∈-irrefl ω (ω-ord .fst ω∈β β∈ω)
    sqβ : SQ.sq β
    sqβ = ih β β∈α oβ β∉ω
    h : ⟪ α ⟫ → ⟪ β ⟫
    h m = sqβ .fst (f m)
    h-inj : (m n : ⟪ α ⟫) → h m ≡ h n → m ≡ n
    h-inj m n e = f-inj m n (sqβ .snd (f m) (f n) e)

  -- SITE 2, the successor closure.  [LJ-1.107]:514-531 built the
  -- inclusion `Incl`, then `CSB.csb`, twice: once at ω and once at a
  -- general infinite γ.  Here `shift↪` IS the injection, both times, and
  -- `Incl` is dead.
  succ-closure : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩
  succ-closure γ γ∈α =
    go (ord-tri (sucV γ) (suc-ord (mem-ord {A = α} oα γ γ∈α)) α oα)
    where
    oγ : IsOrd γ
    oγ = mem-ord {A = α} oα γ γ∈α
    go : (⟨ sucV γ ∈ˢ α ⟩ ⊎ ((sucV γ ≡ α) ⊎ ⟨ α ∈ˢ sucV γ ⟩)) → ⟨ sucV γ ∈ˢ α ⟩
    go (inl h) = h
    go (inr (inr h)) = ∈sucV-elim {A = γ} {x = α} {P = ⟨ sucV γ ∈ˢ α ⟩}
      (snd (sucV γ ∈ˢ α)) h
      (λ α∈γ → Empty.rec (∈-irrefl α (oα .fst {x = γ} {y = α} α∈γ γ∈α)))
      (λ α≡γ → Empty.rec (∈-irrefl γ (subst (λ w → ⟨ γ ∈ˢ w ⟩) α≡γ γ∈α)))
    go (inr (inl sγ≡α)) = go2 (ord-tri γ oγ ω ω-ord)
      where
      go2 : (⟨ γ ∈ˢ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ˢ γ ⟩)) → ⟨ sucV γ ∈ˢ α ⟩
      go2 (inl γ∈ω) = PT.rec (snd (sucV γ ∈ˢ α)) go3 (FiniteBase.ω-mem→numeral γ γ∈ω)
        where
        go3 : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ˢ α ⟩
        go3 (n , q) = Empty.rec (∈-irrefl ω (ω-ord .fst ω∈α α∈ω))
          where
          α∈ω : ⟨ α ∈ˢ ω ⟩
          α∈ω = subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (cong sucV q) ∙ sγ≡α) (#∈ω (suc n))
      -- γ = ω.  α is sucV ω, and Shiftω.shift IS ⟪ α ⟫ ↪ ⟪ ω ⟫.
      go2 (inr (inl γ≡ω)) = Empty.rec (leastα ω ω∈α ∣ shiftα ∣₁)
        where
        α≡sucω : α ≡ sucV ω
        α≡sucω = sym sγ≡α ∙ cong sucV γ≡ω
        shiftα : ⟪ α ⟫ ↪ ⟪ ω ⟫
        shiftα = subst (λ v → ⟪ v ⟫ ↪ ⟪ ω ⟫) (sym α≡sucω) Shiftω.shift↪
      -- ω ∈ γ.  α is sucV γ, and ShiftAbs.shift IS ⟪ α ⟫ ↪ ⟪ γ ⟫.
      go2 (inr (inr ω∈γ)) = Empty.rec (leastα γ γ∈α ∣ shiftα ∣₁)
        where
        γ∉ω' : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
        γ∉ω' h = ∈-irrefl ω (ω-ord .fst ω∈γ h)
        module SA = ShiftAbs γ oγ γ∉ω' (λ k → oγ .fst {x = ω} {y = # k} (#∈ω k) ω∈γ)
        shiftα : ⟪ α ⟫ ↪ ⟪ γ ⟫
        shiftα = subst (λ v → ⟪ v ⟫ ↪ ⟪ γ ⟫) sγ≡α SA.shift↪

  initα : SQ.Init α
  initα = oα , ω∈α , succ-closure , noinj²

  sqα : SQ.sq α
  sqα = SQ.via-col-square α initα

-- =====================================================================
-- PART 5.  THE NON-INITIAL CASE.  SITE 3.
--
--   [LJ-1.107]:549-554 took the injection `α↪κ` as a parameter because
--   its `κ-eqα` was a truncated EQUIVALENCE and `↪` is not an hProp.
--   The parameter stays here, and [LJ-1.136] Probe B is what discharges
--   it.  What changes is `κ∉ω`: [LJ-1.107]:562-587 had to INVERT the
--   equivalence and compose with an embedding of ω into α.  The
--   injection is already the right way round, so eleven lines go.
-- =====================================================================
module NonInitial (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                  (κ : S) (oκ : IsOrd κ) (κ-inj : ∥ ⟪ α ⟫ ↪ ⟪ κ ⟫ ∥₁)
                  (κ∈α : ⟨ κ ∈ˢ α ⟩)
                  (α↪κ : ⟪ α ⟫ ↪ ⟪ κ ⟫)
                  (ih : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β
                      → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq β) where

  κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥
  κ∉ω κ∈ω = PT.rec Empty.isProp⊥ go3 (FiniteBase.ω-mem→numeral κ κ∈ω)
    where
    go3 : Σ[ n ∈ ℕ ] (κ ≡ # n) → Empty.⊥
    go3 (n , q) = PT.rec Empty.isProp⊥ go5 κ-inj
      where
      go5 : ⟪ α ⟫ ↪ ⟪ κ ⟫ → Empty.⊥
      go5 g = FiniteBase.no-inj-finite α oα ω∈α n
                (λ x → g' .fst x , g' .fst x) inj
        where
        -- the injection is ALREADY the right way round.  [LJ-1.107] had
        -- to invert an equivalence here (`:576-583`).
        g' : ⟪ α ⟫ ↪ ⟪ # n ⟫
        g' = subst (λ v → ⟪ α ⟫ ↪ ⟪ v ⟫) q g
        inj : (x y : ⟪ α ⟫) → (g' .fst x , g' .fst x) ≡ (g' .fst y , g' .fst y) → x ≡ y
        inj x y p = g' .snd x y (cong fst p)

  j : ⟪ κ ⟫ → ⟪ α ⟫
  j m = fiber α {x = ⟪ κ ⟫↪ m} (oα .fst (member κ m) κ∈α) .fst

  j-inj : (m n : ⟪ κ ⟫) → j m ≡ j n → m ≡ n
  j-inj m n e = ↪-inj {a = κ}
    (sym (fiber α {x = ⟪ κ ⟫↪ m} (oα .fst (member κ m) κ∈α) .snd)
      ∙ cong (⟪ α ⟫↪) e
      ∙ fiber α {x = ⟪ κ ⟫↪ n} (oα .fst (member κ n) κ∈α) .snd)

  sqκ : SQ.sq κ
  sqκ = ih κ κ∈α oκ κ∉ω

  pair : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  pair (x , y) = j (sqκ .fst (α↪κ .fst x , α↪κ .fst y))

  pair-inj : (p q : ⟪ α ⟫ × ⟪ α ⟫) → pair p ≡ pair q → p ≡ q
  pair-inj (x , y) (x' , y') e = ΣPathP (x≡x' , y≡y')
    where
    pq : (α↪κ .fst x , α↪κ .fst y) ≡ (α↪κ .fst x' , α↪κ .fst y')
    pq = sqκ .snd (α↪κ .fst x , α↪κ .fst y) (α↪κ .fst x' , α↪κ .fst y')
      (j-inj (sqκ .fst (α↪κ .fst x , α↪κ .fst y))
             (sqκ .fst (α↪κ .fst x' , α↪κ .fst y')) e)
    x≡x' : x ≡ x'
    x≡x' = α↪κ .snd x x' (cong fst pq)
    y≡y' : y ≡ y'
    y≡y' = α↪κ .snd y y' (cong snd pq)

  sqα : SQ.sq α
  sqα = pair , pair-inj

-- =====================================================================
-- PART 6.  THE CHAIN.
--   [LJ-1.107]:630-666 with `LeastCard` replaced by `LeastCardInj`.
--   No other line of the assembly changes.
-- =====================================================================
module Chain (inj : (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) (κ : S)
                    (κ∈α : ⟨ κ ∈ˢ α ⟩) → ⟪ α ⟫ ↪ ⟪ κ ⟫) where

  P : S → Type (ℓ-suc ℓ)
  P α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq α

  sqω : SQ.sq ω
  sqω = NumeralPresentation.pairω , NumeralPresentation.pairω-inj

  step : (α : S) → ((β : S) → β ∈ᵗ α → P β) → P α
  step α ih oα α∉ω = go (ord-tri ω ω-ord α oα)
    where
    go : (⟨ ω ∈ˢ α ⟩ ⊎ ((ω ≡ α) ⊎ ⟨ α ∈ˢ ω ⟩)) → SQ.sq α
    go (inr (inl ω≡α)) = subst (λ w → SQ.sq w) ω≡α sqω
    go (inr (inr α∈ω)) = Empty.rec (α∉ω α∈ω)
    go (inl ω∈α) = split (∈sucV-elim {A = α} {x = LC0.κ}
      {P = ⟨ LC0.κ ∈ˢ α ⟩ ⊎ (LC0.κ ≡ α)}
      (isProp⊎ (snd (LC0.κ ∈ˢ α)) (isSetS LC0.κ α)
        (λ m e → ∈-irrefl α (subst (λ w → ⟨ w ∈ˢ α ⟩) e m)))
      LC0.κ∈sα (λ q → inl q) (λ q → inr q))
      where
      module LC0 = LeastCardInj α oα
      ih' : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq β
      ih' β β∈α = ih β β∈α
      split : (⟨ LC0.κ ∈ˢ α ⟩ ⊎ (LC0.κ ≡ α)) → SQ.sq α
      split (inr κ≡α) = InitialCase.sqα α oα ω∈α leastα ih'
        where
        leastα : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁ → Empty.⊥
        leastα δ δ∈α α↪δ = LC0.κ-min-at δ δ∈κ α↪δ
          where
          δ∈κ : ⟨ δ ∈ˢ LC0.κ ⟩
          δ∈κ = subst (λ w → ⟨ δ ∈ˢ w ⟩) (sym κ≡α) δ∈α
      split (inl κ∈α) = NonInitial.sqα α oα ω∈α α∉ω LC0.κ LC0.oκ LC0.κ-inj κ∈α
                          (inj α oα ω∈α LC0.κ κ∈α) ih'

  theorem : (α : S) → P α
  theorem = ∈-induction step

-- =====================================================================
-- PART 7.  THE C-38 GUARD.
--
--   "An interface nothing satisfies is a restatement, not a supply."
--   dev/LESSONS.md:3427.  A DISSOLVED verdict must show each refutation
--   CLOSING at a real site, not argue that it would.
--
--   Three witnesses, and NONE of them rests on the `inj` parameter.
-- =====================================================================
module Guard where

  -- (a) A REAL injection between two DIFFERENT presentations.  It is not
  --     the identity and it is not vacuous: sucV ω has a member, ω, that
  --     ω does not have.
  shiftω↪ : ⟪ sucV ω ⟫ ↪ ⟪ ω ⟫
  shiftω↪ = Shiftω.shift↪

  sucω-ord : IsOrd (sucV ω)
  sucω-ord = suc-ord ω-ord

  sucω∉ω : ⟨ sucV ω ∈ˢ ω ⟩ → Empty.⊥
  sucω∉ω h = ∈-irrefl ω (ω-ord .fst (self∈sucV ω) h)

  module LCω = LeastCardInj (sucV ω) sucω-ord

  -- (b) SITE 2's refutation FIRING, at a concrete pair of ordinals.
  --     If the least injectable δ were sucV ω itself, then `κ-min-at`
  --     applied to ω and `shiftω↪` gives ⊥.  So κ ∈ sucV ω, MEASURED at
  --     this site, with no equivalence and no `CSB`.
  κ-not-sucω : (LCω.κ ≡ sucV ω) → Empty.⊥
  κ-not-sucω κ≡α = LCω.κ-min-at ω ω∈κ ∣ shiftω↪ ∣₁
    where
    ω∈κ : ⟨ ω ∈ˢ LCω.κ ⟩
    ω∈κ = subst (λ w → ⟨ ω ∈ˢ w ⟩) (sym κ≡α) (self∈sucV ω)

  -- (c) SITE 1's composite, as a standalone term.  Given the induction
  --     hypothesis at β and an injection of ⟪ α ⟫ into the square of
  --     ⟪ β ⟫, the composite IS an injection ⟪ α ⟫ ↪ ⟪ β ⟫.  This is the
  --     term `noinj²` hands to `leastα`, and it needs no `CSB`.
  compose↪ : (α β : S) → SQ.sq β
           → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
           → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n)
           → ⟪ α ⟫ ↪ ⟪ β ⟫
  compose↪ α β sqβ f f-inj =
    (λ m → sqβ .fst (f m)) , (λ m n e → f-inj m n (sqβ .snd (f m) (f n) e))

  -- (d) The chain applied at a REAL infinite ordinal.  This one DOES
  --     rest on `inj`, and it is here to show the assembly runs through
  --     the non-initial branch rather than only typechecking.
  module Runs (inj : (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) (κ : S)
                     (κ∈α : ⟨ κ ∈ˢ α ⟩) → ⟪ α ⟫ ↪ ⟪ κ ⟫) where
    module C = Chain inj

    sq-sucω : SQ.sq (sucV ω)
    sq-sucω = C.theorem (sucV ω) sucω-ord sucω∉ω
