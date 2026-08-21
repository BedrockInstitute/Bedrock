{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.506] The one hypothesis eleven fields consume: is the arity of a
-- decomposed code member a numeral?
--
-- W3 FIRST, and alone: WHERE THE CODE SET COMES FROM.  The obligation is
-- added only after W3 lands.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-506.Probe506 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.CodeSet {ℓ} lem
  using ( AllCodes; AllCodes-out; IsKeyOverAny; keyS; codeS )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  THE CODE SET AS A DEFINITION, NOT AS A SLOT.
--
-- `AllCodes A` (src/L/Coding/CodeSet.lagda.md:411) is the code set the
-- tree actually BUILDS: separation over `smallDom`'s superset by the
-- object-language predicate `isCodeAny A` (:248).  Its load-bearing
-- conjunct is `arityNumAtL` (:185), which says from OUTSIDE that a
-- member is a pair whose first component lies in `ωʟ`.
--
-- `AllCodes-out` (:419) is that conjunct spent.  What it returns names
-- a formula; the ARITY of that formula is the numeral, and
-- `key {n} φ = pr (# n) ⌜ mapFo f φ ⌝` (src/L/Coding/InL.lagda.md:253)
-- puts it in the first component BY DEFINITION.  So the step below is
-- `PT.map` and nothing else: no `subst`, no equation, no lemma.
-- =====================================================================

codeset-numeral : (A x : S) → ⟨ fst x ∈ fst (AllCodes A) ⟩
                → ∥ (Σ[ n ∈ ℕ ] Σ[ z ∈ S ] (fst x ≡ pr (# n) (fst z))) ∥₁
codeset-numeral A x h =
  PT.map (λ { (n , (ψ , q)) → n , (codeS A ψ , q) }) (AllCodes-out A x h)

-- =====================================================================
-- THE OBLIGATION.
--
-- The brief's type verbatim, plus ONE hypothesis: the identity of the
-- code set.  That hypothesis is not a numeral hypothesis and it does not
-- weaken the truncation; it is the code set's OWN CONSTRUCTION, which is
-- what the brief asked the term to be built from.  With `C` left a bare
-- `S` the statement is not a theorem at all: nothing then connects `C`
-- to codes, and a set holding one pair with a non-numeral first
-- component refutes it.  `src/L/Coding/CodeSet.lagda.md:23-27` says the
-- same thing about `closedAt`/`shapedAt`, and that debt is exactly what
-- `arityNumAtL` was written to pay.
--
-- `pr-inj` (src/V/Coding.lagda.md:178) is the whole of the step: the
-- brief's shape equation and the code set's own equation are two
-- readings of `fst c`, so their first components agree.
-- =====================================================================

ar-is-numeral : (A C : S) → fst C ≡ fst (AllCodes A)
              → (k : ℕ) (c ar a b : S)
              → ⟨ fst c ∈ fst C ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
              → ∥ (Σ[ n ∈ ℕ ] (fst ar ≡ # n)) ∥₁
ar-is-numeral A C qC k c ar a b c∈ shEq =
  PT.map (λ { (n , (z , q)) → n , pr-inj (sym shEq ∙ q) .fst })
    (codeset-numeral A c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))

-- The unary form.  `codesK-un` (src/L/Condensation/TwelveAgree.lagda.md
-- :172) decomposes one pair less and asks for the same truncation, so it
-- is the same two lines at a shorter shape equation.
ar-is-numeral-un : (A C : S) → fst C ≡ fst (AllCodes A)
                 → (k : ℕ) (c ar a : S)
                 → ⟨ fst c ∈ fst C ⟩
                 → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                 → ∥ (Σ[ n ∈ ℕ ] (fst ar ≡ # n)) ∥₁
ar-is-numeral-un A C qC k c ar a c∈ shEq =
  PT.map (λ { (n , (z , q)) → n , pr-inj (sym shEq ∙ q) .fst })
    (codeset-numeral A c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))

-- =====================================================================
-- THE HYPOTHESIS IS NECESSARY, AND THIS MEASURES IT RATHER THAN ARGUING
-- IT.
--
-- The brief's type with `C` left a bare `S` is NOT A THEOREM.  One
-- counterexample settles it: `sucʟ` of a pair whose first component is
-- `ωʟ`.  `ω` is not a numeral, because `# n ∈ ω` and `ω ∉ ω`.
--
-- So `codesK`'s fourth component is not a fact that a frame may simply
-- take about an arbitrary slot.  It is a theorem ABOUT A CONSTRUCTED
-- SET, and the frame has to say WHICH set.
-- =====================================================================

open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open InfinitySet {ℓ} using ( sucV; ω )
open import V.Model {ℓ} using ( self∈sucV )
import Cubical.Data.Empty as Empty

badPair : S
badPair = prʟ ωʟ (prʟ (numeralL 0) (prʟ ωʟ ωʟ))

badSet : S
badSet = sucʟ badPair

bad∈ : ⟨ fst badPair ∈ fst badSet ⟩
bad∈ = subst (λ u → ⟨ fst badPair ∈ u ⟩) (sym (sucʟ-fst badPair))
         (self∈sucV (fst badPair))

bad-shape : fst badPair ≡ pr (fst ωʟ) (pr (# 0) (pr (fst ωʟ) (fst ωʟ)))
bad-shape =
    prʟ-fst ωʟ (prʟ (numeralL 0) (prʟ ωʟ ωʟ))
  ∙ cong (pr (fst ωʟ))
      ( prʟ-fst (numeralL 0) (prʟ ωʟ ωʟ)
      ∙ cong₂ pr (numeralL-fst 0) (prʟ-fst ωʟ ωʟ) )

ω-not-numeral : ∥ (Σ[ n ∈ ℕ ] (fst ωʟ ≡ # n)) ∥₁ → Empty.⊥
ω-not-numeral = PT.rec Empty.isProp⊥
  (λ { (n , p) → ∈-irrefl ω (subst (λ w → ⟨ w ∈ ω ⟩) (sym p) (#∈ω n)) })

bare-C-is-not-a-theorem :
    ( (C : S) (k : ℕ) (c ar a b : S)
    → ⟨ fst c ∈ fst C ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ∥ (Σ[ n ∈ ℕ ] (fst ar ≡ # n)) ∥₁ )
  → Empty.⊥
bare-C-is-not-a-theorem h =
  ω-not-numeral (h badSet 0 badPair ωʟ ωʟ ωʟ bad∈ bad-shape)

-- =====================================================================
-- THE FRAME FORM.  `codesK`'s fourth component reads its code set out of
-- a SLOT (`lookup (suc (suc zero)) γ'`, src/L/Condensation/TwelveAgree
-- .lagda.md:162), so this is the same term with the set reached through
-- `lookup`.  It is what a `TFacts`-carrying frame would prove instead of
-- assuming, and the added telescope entry is exactly one equation.
-- =====================================================================

module AtSlot {n : ℕ} (A : S) (C : Fin n) (γ' : S ^ n)
              (qC : fst (lookup C γ') ≡ fst (AllCodes A)) where

  codesK-numeral : (k : ℕ) (c ar a b : S)
                 → ⟨ fst c ∈ fst (lookup C γ') ⟩
                 → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
                 → ∥ (Σ[ n' ∈ ℕ ] (fst ar ≡ # n')) ∥₁
  codesK-numeral = ar-is-numeral A (lookup C γ') qC

  codesK-un-numeral : (k : ℕ) (c ar a : S)
                    → ⟨ fst c ∈ fst (lookup C γ') ⟩
                    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                    → ∥ (Σ[ n' ∈ ℕ ] (fst ar ≡ # n')) ∥₁
  codesK-un-numeral = ar-is-numeral-un A (lookup C γ') qC

-- =====================================================================
-- AND THE EQUATION NEED NOT COME FROM OUTSIDE.  `CodesAt`
-- (src/L/Choice/Faithful.lagda.md:335) is the OBJECT-LANGUAGE pin: one
-- `extAt` over `isCodeAnyAt`, whose `out` direction returns the very
-- equation the module above takes as a hypothesis.  So the frame can
-- carry a FORMULA at the code slot, in the same register as every other
-- clause of the description, and derive the identity.
--
-- IT LIVES ON THE CHOICE WING.  W2 (DD4) applies: if the condensation
-- frame wants it, it moves down beside `AllCodes` in
-- `L.Coding.CodeSet`, and both wings share the one copy.  Nothing here
-- copies it.
-- =====================================================================

open import L.Choice.Faithful {ℓ} lem using ( CodesAt; CodesAt-out )

module Pinned {n : ℕ} (A : S) (C W : Fin n) (γ' : S ^ n)
              (qw : fst (lookup W γ') ≡ fst A)
              (pin : ⟨ γ' ⊨ CodesAt C W ⟩) where

  qC : fst (lookup C γ') ≡ fst (AllCodes A)
  qC = cong fst (CodesAt-out A C W γ' qw pin)

  codesK-numeral : (k : ℕ) (c ar a b : S)
                 → ⟨ fst c ∈ fst (lookup C γ') ⟩
                 → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
                 → ∥ (Σ[ n' ∈ ℕ ] (fst ar ≡ # n')) ∥₁
  codesK-numeral = ar-is-numeral A (lookup C γ') qC
