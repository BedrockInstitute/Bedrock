{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

-- [L3.32-T142] The code block gate.
--
-- The question: can `hasWitnessAt`'s text be stated fresh against the
-- surviving interface, and can `codeAt-in`/`codeAt-out` then close, without
-- the retiring shape machinery (Closed, InL, Recover, Descent, Shape and the
-- shape side of Model)?
--
-- The probe states `hasWitnessAt`'s text fresh (the three-line formula below,
-- matching the delivered text at CodeSet.lagda.md:250-252). Its two support
-- atoms `closedAt` and `shapedAt` enter as module parameters, exactly as the
-- frame's other atoms do: their text lives in the shape side under test
-- (Model.lagda.md:2197, Shape.lagda.md:189), which this probe must not
-- import and must not copy. The probe then states `codeAt-in` and
-- `codeAt-out` exactly as `L.TowerGraph.Readings` declares them
-- (src/L/TowerGraph.lagda.md:357-365), and proves the assembly from three
-- obligations stated as types below.
--
-- The probe imports no retiring module. The surviving interface
-- (`L.Definability`, in scope) exports `smallSat`, `defSet`, `Def`,
-- `Def-spec`, `defSet⊆A`, `defSet-mem` and `Refine` (Definability.lagda.md:
-- 107-113, :136, :140, :145, :217): it carves subsets of `⟪ fst A ⟫` by
-- meta-formulas. It never constructs a closed, shaped set of keys from a
-- formula, and it never decodes one back. None of the obligations has an
-- inhabitant in scope.

module ProbeT142 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Definability {ℓ} using ( module DefOf )
open import L.TowerGraph {ℓ} lem
  using ( keyArityAtL; keyArityAtL-in; keyArityAtL-out )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Vec using ( lookup )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The carrier is a module parameter, exactly as in `L.TowerGraph`
-- (`module _ (A : S) where`, TowerGraph.lagda.md:299). The frame's fresh
-- support (`ι`, `ι∈`, `ιL`) is restated from the master's own lines 301-308.
module _ (A : S) where
  ι : ⟪ fst A ⟫ → V ℓ
  ι = ⟪ fst A ⟫↪

  ι∈ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ fst A ⟩
  ι∈ m = ∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

  ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
  ιL m = isL-trans {x = fst A} {y = ι m} (ι∈ m) (A .snd)

  module Frame
    (closedAt : ∀ {n} → Fin n → Formula S n)
    (shapedAt : ∀ {n} → Fin n → Fin n → Formula S n)
    (keyS : Formula ⟪ fst A ⟫ 1 → S)
    where

    -- The witness atom's text, stated fresh.  Delivered text at
    -- CodeSet.lagda.md:250-252.  `closedAt` and `shapedAt` are delivered
    -- inputs: their text is the shape side under test (homes Model.lagda.md:
    -- 2197 and Shape.lagda.md:189), which the probe may not import or copy.
    hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n
    hasWitnessAt w c = ∃̇ ((var (suc c) ∈̇ var zero)
                        ∧̇ (closedAt zero ∧̇ shapedAt zero (suc w)))

    -- The code conjunct, copied from the frame's own `isCodeAt`
    -- (TowerGraph.lagda.md:326).
    isCodeAt : ∀ {n} → Fin n → Fin n → Formula S n
    isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c

    -- Obligation 1, the witness introduction's reduction target.  The
    -- delivered proof builds the existential witness as the subformula
    -- closure: `clo ι ιL φ` holds the key of `φ`, satisfies `closedAt`, and
    -- satisfies `shapedAt` at the carrier slot (CodeSet.lagda.md:337-341).
    -- The three facts are the shape machinery's own theorems, one chapter
    -- each: `key∈closure` (InL.lagda.md:497-509), `closureClosed`
    -- (Closed.lagda.md:228-230) and `closureShaped` (Shape.lagda.md:646-649).
    -- The surviving interface supplies no construction of such a set.
    ClosureObligation : Type (ℓ-suc ℓ)
    ClosureObligation =
      ∀ {n} (w c : Fin n) (γ : S ^ n) (φ : Formula ⟪ fst A ⟫ 1)
      → fst (lookup w γ) ≡ fst A
      → fst (lookup c γ) ≡ fst (keyS φ)
      → ∥ Σ[ C ∈ S ]
          ( ⟨ fst (lookup c γ) ∈ fst C ⟩
            × ⟨ (C ∷ γ) ⊨ closedAt zero ⟩
            × ⟨ (C ∷ γ) ⊨ shapedAt zero (suc w) ⟩ ) ∥₁

    -- Obligation 2, the arity half's reduction target.  The frame's `keyS`
    -- is abstract, so `fst (lookup c γ) ≡ fst (keyS φ)` gives no arity-one
    -- shape.  The delivered `keyS` is concrete: `fst (keyS φ) ≡
    -- pr (# 1) (fst (codeS φ))` with `codeS φ` the code (CodeSet.lagda.md:
    -- 311-315; `key` at InL.lagda.md:257-261).  The delivered `codeAt-in`
    -- feeds exactly this fact to `keyArityAtL-in` (Powerset.lagda.md:311).
    KeyShapeObligation : Type (ℓ-suc ℓ)
    KeyShapeObligation =
      (φ : Formula ⟪ fst A ⟫ 1)
      → Σ[ z ∈ S ] (fst (keyS φ) ≡ pr (# 1) (fst z))

    -- Obligation 3, the elimination's reduction target.  The delivered
    -- `witnessAt-out` runs `Decode.recover` on the closed, shaped witness
    -- (CodeSet.lagda.md:344-353; `recover` at Recover.lagda.md:146-155,
    -- built on `Descent` and Shape's term decode), then bridges the code it
    -- returns to `keyS` by the concrete definition.  The surviving interface
    -- supplies no decode from a closed, shaped set to a formula.
    DecodeObligation : Type (ℓ-suc ℓ)
    DecodeObligation =
      ∀ {n} (w c : Fin n) (γ : S ^ n)
      → fst (lookup w γ) ≡ fst A
      → ⟨ γ ⊨ hasWitnessAt w c ⟩
      → (z : S) → fst (lookup c γ) ≡ pr (# 1) (fst z)
      → ∥ Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (fst (lookup c γ) ≡ fst (keyS ψ)) ∥₁

    -- The assembly, measured.  Given Obligation 1, the witness half of the
    -- code conjunct closes: the existential witness is the obligation's set.
    witness-in : ClosureObligation
               → ∀ {n} (w c : Fin n) (γ : S ^ n)
               → fst (lookup w γ) ≡ fst A
               → (φ : Formula ⟪ fst A ⟫ 1) → fst (lookup c γ) ≡ fst (keyS φ)
               → ⟨ γ ⊨ hasWitnessAt w c ⟩
    witness-in obl w c γ qw φ qc = PT.rec (snd (γ ⊨ hasWitnessAt w c)) step
      (obl w c γ φ qw qc)
      where
      step : Σ[ C ∈ S ]
               ( ⟨ fst (lookup c γ) ∈ fst C ⟩
                 × ⟨ (C ∷ γ) ⊨ closedAt zero ⟩
                 × ⟨ (C ∷ γ) ⊨ shapedAt zero (suc w) ⟩ )
           → ⟨ γ ⊨ hasWitnessAt w c ⟩
      step (C , (x∈ , hcl , hsh)) = ∣ C , (x∈ , (hcl , hsh)) ∣₁

    -- Given Obligations 1 and 2, target 1 closes: the arity half is
    -- `keyArityAtL-in` at the code the concrete keyS supplies, the witness
    -- half is `witness-in`.
    codeAt-in : ClosureObligation → KeyShapeObligation
              → ∀ {n} (c w : Fin n) (γ : S ^ n)
              → fst (lookup w γ) ≡ fst A
              → (ψ : Formula ⟪ fst A ⟫ 1) → fst (lookup c γ) ≡ fst (keyS ψ)
              → ⟨ γ ⊨ isCodeAt c w ⟩
    codeAt-in o1 o2 c w γ qw ψ qc =
      keyArityAtL-in c 1 γ (fst (o2 ψ)) (qc ∙ snd (o2 ψ))
      , witness-in o1 w c γ qw ψ qc

    -- Given Obligation 3, target 2 closes: `keyArityAtL-out` reads the
    -- arity-one shape off the code slot, and the decode obligation hands the
    -- shape to the formula over the carrier.
    codeAt-out : DecodeObligation
               → ∀ {n} (c w : Fin n) (γ : S ^ n)
               → fst (lookup w γ) ≡ fst A
               → ⟨ γ ⊨ isCodeAt c w ⟩
               → ∥ Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
                   (fst (lookup c γ) ≡ fst (keyS ψ)) ∥₁
    codeAt-out o3 c w γ qw (hk , hw) =
      PT.rec squash₁ step (keyArityAtL-out c 1 γ hk)
      where
      step : Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# 1) (fst z))
           → ∥ Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ]
               (fst (lookup c γ) ≡ fst (keyS ψ)) ∥₁
      step (z , qz) = o3 w c γ qw hw z qz
