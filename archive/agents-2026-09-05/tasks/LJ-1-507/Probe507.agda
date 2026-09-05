{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.507] someEnv at the frame: does `arNumC` pay `[LJ-1.504]`'s gap?
--
-- W3 FIRST, and alone: DO THE TWO FRAMES AGREE, SLOT FOR SLOT?  The
-- obligation is omitted from this stage and added only if W3 lands.
--
-- REBUILT, NOT IMPORTED.  `[LJ-1.500]`'s `ar-is-numeral` and `module
-- Num` and `[LJ-1.504]`'s `Frame`, `gam'`, `K6` and `someEnvDef-gap`
-- are all probe-local at their own tasks.  Every one of them is
-- restated here at the type its own report delivered.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-507.Probe507 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Ordinal {ℓ} using ( numeral-ord )
open import L.Coding.CodeSet {ℓ} lem using ( arityNumAtL; arityNumAtL-out )
open import L.Condensation {ℓ} lem
  using ( module KValue; module KFactsNS )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ⁅_,_⁆; ⁅_⁆s; pairing-ax
        ; SingletonPackage; SetPackage )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open InfinitySet {ℓ} using ( #_; sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- `[LJ-1.500]`'s `ar-is-numeral`, REBUILT at the type its probe
-- delivered (`agents/tasks/LJ-1-500/Probe500.agda:78-84`, GO at
-- `agents/tasks/LJ-1-500/lj-1.500-report.md:145`).  Not imported.
-- =====================================================================

ar-is-numeral : {m : ℕ} (γ : S ^ m) (c ar rest : S)
              → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
              → fst c ≡ pr (fst ar) (fst rest)
              → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
ar-is-numeral γ c ar rest hnum shEq =
  PT.map (λ { (n , (z , e)) → n , pr-inj (sym shEq ∙ e) .fst })
    (arityNumAtL-out zero (c ∷ γ) hnum)

-- =====================================================================
-- `[LJ-1.500]`'s `module Num`, REBUILT at its delivered telescope
-- (`agents/tasks/LJ-1-500/Probe500.agda:225-239`).  `arNumC` is THE
-- frame hypothesis the mathematician ruled, and this is its type.
-- =====================================================================

module Num {m : ℕ} (C : Fin m) (γ : S ^ m)
  (arNumC : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
          → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩) where

  codesK-num : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  codesK-num k c ar a b c∈ shEq =
    let inner1 = prʟ (numeralL k) (prʟ a b)
        inner1eq : fst inner1 ≡ pr (# k) (pr (fst a) (fst b))
        inner1eq = prʟ-fst (numeralL k) (prʟ a b)
                 ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a b)
    in ar-is-numeral γ c ar inner1 (arNumC c c∈)
         (shEq ∙ cong (pr (fst ar)) (sym inner1eq))

-- =====================================================================
-- A SELF-PAIR IS NOT A NUMERAL.  Three library classification steps and
-- one irreflexivity.  `V.Coding` keeps its own copies of the first
-- three `private` (`src/V/Coding.lagda.md:136`), so they are rebuilt
-- here from `pairing-ax` and `SingletonPackage` directly.
-- =====================================================================

self∈singlV : (a : V ℓ) → ⟨ a ∈ ⁅ a ⁆s ⟩
self∈singlV a = ∈∈ₛ {a = a} {b = ⁅ a ⁆s} .snd
  (SetPackage.classification (SingletonPackage a) a .snd refl)

self∈pairV : (a b : V ℓ) → ⟨ a ∈ ⁅ a , b ⁆ ⟩
self∈pairV a b = ∈∈ₛ {a = a} {b = ⁅ a , b ⁆} .snd
  (pairing-ax a b a .snd PT.∣ Sum.inl refl ∣₁)

singl∈prV : (a b : V ℓ) → ⟨ ⁅ a ⁆s ∈ pr a b ⟩
singl∈prV a b = ∈∈ₛ {a = ⁅ a ⁆s} {b = pr a b} .snd
  (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s .snd PT.∣ Sum.inl refl ∣₁)

mem-prV : (a b x : V ℓ) → ⟨ x ∈ pr a b ⟩
        → ∥ (x ≡ ⁅ a ⁆s) Sum.⊎ (x ≡ ⁅ a , b ⁆) ∥₁
mem-prV a b x h =
  pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ x .fst (∈∈ₛ {a = x} {b = pr a b} .fst h)

-- Transitivity walks `a ∈ ⁅ a ⁆s ∈ pr a a` down to `a ∈ pr a a`, and
-- either brace then puts `a` inside itself.
pr-self-not-ord : (a : V ℓ) → IsOrd (pr a a) → Empty.⊥
pr-self-not-ord a (tr , _) =
  PT.rec Empty.isProp⊥
    (Sum.rec
      (λ e → ∈-irrefl a (subst (λ w → ⟨ a ∈ w ⟩) (sym e) (self∈singlV a)))
      (λ e → ∈-irrefl a (subst (λ w → ⟨ a ∈ w ⟩) (sym e) (self∈pairV a a))))
    (mem-prV a a a (tr (self∈singlV a) (singl∈prV a a)))

pr-self-not-numeral : (a : V ℓ) (n : ℕ) → pr a a ≡ (# n) → Empty.⊥
pr-self-not-numeral a n p =
  pr-self-not-ord a (subst IsOrd (sym p) (numeral-ord n))

-- =====================================================================
-- `[LJ-1.504]`'s FRAME, REBUILT verbatim
-- (`agents/tasks/LJ-1-504/Probe504.agda:47-60`, GO on all three of its
-- terms at `agents/tasks/LJ-1-504/lj-1.504-report.md:44-46`).  It is
-- `[LJ-1.499]`'s telescope plus `SupplyEnv`'s own gate.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  gam' : (g1 g2 g3 g4 g5 : S) → S ^ 20
  gam' g1 g2 g3 g4 g5 = SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv

  -- `[LJ-1.504]`'s K index (`Probe504.agda:91-92`), and the code slot
  -- `codesK` reads (`src/L/Condensation/LowerAgree.lagda.md:120`).
  K6 : Fin 20
  K6 = suc (suc (suc (suc (suc (suc KV.iK)))))

  iC : Fin 20
  iC = suc (suc zero)

  -- ===================================================================
  -- W3.  `arNumC`, STATED AT `[LJ-1.504]`'s FRAME.
  --
  -- The brief's type, with the five free slots bound.  `[LJ-1.500]`
  -- states it at `c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv`
  -- (`Probe500.agda:349-353`, `:357`); `[LJ-1.504]` states its results
  -- at `SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv` (`Probe504.agda:60`).
  -- Both are `S ^ 20`, both put `Kenv` after six conses, and both read
  -- the code set at `suc (suc zero)` and K at `suc⁶ iK`.
  -- ===================================================================
  arNumC-at-504-frame : (g1 g2 g3 g4 g5 : S) → Type (ℓ-suc ℓ)
  arNumC-at-504-frame g1 g2 g3 g4 g5 =
      (c : S) → ⟨ fst c ∈ fst (lookup iC (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ (c ∷ gam' g1 g2 g3 g4 g5) ⊨ arityNumAtL zero ⟩

  -- AND IT IS `[LJ-1.500]`'s OWN TELESCOPE ENTRY, not a look-alike.
  -- A type that merely FORMS proves nothing, so this term FEEDS the
  -- stated hypothesis into the rebuilt `Num` at `[LJ-1.504]`'s vector
  -- and returns `[LJ-1.500]`'s delivered conclusion.  If the two frames
  -- disagreed at any of the twenty slots, this application would not
  -- elaborate.
  frames-agree : (g1 g2 g3 g4 g5 : S)
               → arNumC-at-504-frame g1 g2 g3 g4 g5
               → (k : ℕ) (c ar a b : S)
               → ⟨ fst c ∈ fst (lookup iC (gam' g1 g2 g3 g4 g5)) ⟩
               → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  frames-agree g1 g2 g3 g4 g5 arNumC =
    Num.codesK-num {20} iC (gam' g1 g2 g3 g4 g5) arNumC

  -- ===================================================================
  -- `[LJ-1.504]`'s GAP, REBUILT (`Probe504.agda:120-126`).  This is the
  -- one input `gap-suffices` (`:133-138`) asks for, and its telescope is
  -- copied here unchanged.
  -- ===================================================================
  someEnvDef-gap : Type (ℓ-suc ℓ)
  someEnvDef-gap =
      (g1 g2 g3 g4 g5 : S) (ya yc b a ar c : S)
    → ⟨ fst ya ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst yc ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst ar ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

  -- ===================================================================
  -- THE JOIN, ATTEMPTED AND RECORDED.  `runs/attempt-0.out`, exit 42.
  -- The body was
  --
  --   frames-agree g1 g2 g3 g4 g5 (arNumC g1 g2 g3 g4 g5) 0 c ar a b arK refl
  --
  -- and Agda answered `(fst ar) != (fst c) of type (V ℓ)` at the slot
  -- `arNumC`'s consumer reads: the gap hands a member of K where a
  -- member of the CODE SET is wanted.
  --
  -- THIS TERM SAYS THE SAME THING CONSTRUCTIVELY.  It is the gap's
  -- telescope plus THREE arguments, and with them `arNumC` does pay.
  -- The three are exactly what `someEnvDef`, and so the gap, omits.
  -- ===================================================================
  gap-with-code :
      ((g1 g2 g3 g4 g5 : S) → arNumC-at-504-frame g1 g2 g3 g4 g5)
    → (g1 g2 g3 g4 g5 : S) (ya yc b a ar c : S)
    → ⟨ fst ya ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst yc ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → ⟨ fst ar ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
    → (k : ℕ) (a' b' : S)                                     -- MISSING 1
    → ⟨ fst c ∈ fst (lookup iC (gam' g1 g2 g3 g4 g5)) ⟩       -- MISSING 2
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a') (fst b')))   -- MISSING 3
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  gap-with-code arNumC g1 g2 g3 g4 g5 ya yc b a ar c yaK ycK arK k a' b' c∈ shEq =
    frames-agree g1 g2 g3 g4 g5 (arNumC g1 g2 g3 g4 g5) k c ar a' b' c∈ shEq

  -- ===================================================================
  -- AND THE GAP IS NOT MERELY UNPAID BY `arNumC`.  IT IS FALSE.
  --
  -- `KValue` DELIVERS a `KFacts` VALUE at this very frame
  -- (`src/L/Condensation.lagda.md:7415-7431`), and two of its fields
  -- are all this needs: `numK0` puts the numeral zero in K, and
  -- `pairK` closes K under the L-pair.  So `prʟ (numeralL 0)
  -- (numeralL 0)` is a member of K, and the gap would call it a
  -- numeral.
  --
  -- IT IS NOT ONE.  `pr a a` is `⁅ ⁅ a ⁆s , ⁅ a , a ⁆ ⁆`
  -- (`src/V/Coding.lagda.md:175-176`), and its only members are the two
  -- braces, each of which holds `a`.  An ordinal is transitive
  -- (`src/L/Constructible.lagda.md:141-142`), so `a` would belong to
  -- `pr a a`, hence be one of the two braces, hence belong to itself.
  -- `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`) forbids that, and every
  -- numeral IS an ordinal (`src/L/Ordinal.lagda.md:244`).
  --
  -- THE HYPOTHESIS IS NOT WEAKENED ANYWHERE.  Nothing below is
  -- postulated and nothing below is assumed about `lam` or `gam` beyond
  -- this frame's own telescope.
  -- ===================================================================
  badAr : S
  badAr = prʟ (numeralL 0) (numeralL 0)

  badAr∈K : (g1 g2 g3 g4 g5 : S)
          → ⟨ fst badAr ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
  badAr∈K g1 g2 g3 g4 g5 =
    KV.facts .pairK (numeralL 0) (numeralL 0)
      (KV.facts .numK0) (KV.facts .numK0)

  gap-is-false : someEnvDef-gap → Empty.⊥
  gap-is-false gap =
    PT.rec Empty.isProp⊥
      (λ { (n , e) →
        pr-self-not-numeral (fst (numeralL 0)) n
          (sym (prʟ-fst (numeralL 0) (numeralL 0)) ∙ e) })
      -- g1..g5, then ya yc b a ar c: `badAr` sits at the `ar` slot.
      (gap z z z z z  z z z z badAr z
        (KV.facts .numK0) (KV.facts .numK0) (badAr∈K z z z z z))
    where
    z : S
    z = numeralL 0

  -- THE CONSEQUENCE, IN ONE SENTENCE.  `[LJ-1.504]`'s `gap-suffices`
  -- (`agents/tasks/LJ-1-504/Probe504.agda:133-138`) is a true
  -- implication out of a FALSE antecedent, so it inhabits nothing.
  -- That is why the obligation name `someEnv-at-frame` is DELIBERATELY
  -- ABSENT from this file.  See `review-of-someEnv-at-frame.md`.

arNumC-at-504-frame = Frame.arNumC-at-504-frame
frames-agree        = Frame.frames-agree
gap-with-code       = Frame.gap-with-code
gap-is-false        = Frame.gap-is-false
