{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.683] PROBE.  Describes at a generic non-stage member.
-- It runs in agents/tasks/LJ-1-683/ and lands nothing in src/.
--
-- THE OBLIGATION the brief names is describes-generic: Describes σ y
-- at an arbitrary member y of Lset σ, not at one named pair.
-- This file does NOT inhabit that type as a closed term.  It does not
-- inhabit its negation.  D-10 is the job: the generic formula is the
-- subset formula, and it carves 𝒟ₒ y exactly when two named
-- hypotheses hold.
--
-- WHAT IS SETTLED.
--   1. Describes, copied from
--      agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82.
--   2. subsetFo (W2): the formula "x ⊆ y" over ⟪ Lset σ ⟫, y a
--      constant from the stage.
--   3. from-hyps: Describes from Dee⊆stage and StagePowDef, spending
--      subsetFo, not a Formula Code 1.
--
-- WHAT IS NOT SETTLED.
--   describes-generic as a closed term.  The pairing formula carves
--   {∅, y} and that equals 𝒟ₒ y only at a singleton ([LJ-1.677]).
--   The tautology carves the whole stage and that equals 𝒟ₒ y only
--   at the tower pair ([LJ-1.674]).  The subset formula carves the
--   members of the stage that are subsets of y.  That equals 𝒟ₒ y
--   only when every such member is definable over y, and when 𝒟ₒ y
--   itself sits in the stage.  Nothing in src/ supplies either
--   hypothesis at a generic y.  A Formula Code 1 for 𝒟ₒ stays a
--   second debt.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth

module LJ-1-683.Probe683 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; ∀̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ∋⊆; Lset-layer; layer-trans )

open import Cubical.Foundations.HLevels using ( isPropΠ )
open import Cubical.Data.Sigma using ( Σ-syntax; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- D-10.  THE GENERIC FORMULA.
--
-- Describes is [LJ-1.169]'s type.  The tautology carves a whole stage
-- ([LJ-1.674]).  The pairing formula carves {∅, y} ([LJ-1.677]).  The
-- formula that mentions y as a constant and does not list y's members
-- is "x ⊆ y".  It is written once, then consumed.
-- =====================================================================

Describes : S → S → Type (ℓ-suc ℓ)
Describes σ y =
  ∥ Σ[ ψ ∈ Formula ⟪ Lset σ ⟫ 1 ] (DefOf.defSet (Lset σ) ψ ≡ 𝒟ₒ y) ∥₁

-- W2: the subset formula at a generic member of a generic stage.
subsetFo : (σ y : S) → ⟨ y ∈ˢ Lset σ ⟩ → Formula ⟪ Lset σ ⟫ 1
subsetFo σ y y∈ = ∀̇∈ (var zero) (var zero ∈̇ con (∈-asFiber {a = y} {b = Lset σ} y∈ .fst))

-- 𝒟ₒ y is a subset of the stage, as a collection of members.
Dee⊆stage : (σ y : S) → Type (ℓ-suc ℓ)
Dee⊆stage σ y = (x : S) → ⟨ x ∈ˢ 𝒟ₒ y ⟩ → ⟨ x ∈ˢ Lset σ ⟩

-- Every subset of y that already sits in the stage is definable over y.
StagePowDef : (σ y : S) → Type (ℓ-suc ℓ)
StagePowDef σ y =
  (x : S) → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ x ⊆ y ⟩ → ⟨ x ∈ˢ 𝒟ₒ y ⟩

-- The subset formula's defSet contains exactly the members of the
-- stage that are subsets of y.  Two directions, then the consumer.
module Carve (σ y : S) (y∈ : ⟨ y ∈ˢ Lset σ ⟩) where
  module DefC = DefOf (Lset σ)
  Atrans = layer-trans (Lset-layer σ)
  mᵧ = ∈-asFiber {a = y} {b = Lset σ} y∈ .fst
  qᵧ : ⟪ Lset σ ⟫↪ mᵧ ≡ y
  qᵧ = ∈-asFiber {a = y} {b = Lset σ} y∈ .snd
  φ = subsetFo σ y y∈

  -- fst of the inner constant is the stage member, by construction of ι.
  ιfst : (k : ⟪ Lset σ ⟫) → fst (DefC.ι k) ≡ ⟪ Lset σ ⟫↪ k
  ιfst k = refl

  -- Inner satisfaction of φ at m is "every inner member of
  -- ⟪ Lset σ ⟫↪ m is a member of y".
  sat→⊆ : (m : ⟪ Lset σ ⟫)
        → ⟨ (DefC.ι m ∷ []) DefC.⊨ᵐ φ ⟩
        → ⟨ ⟪ Lset σ ⟫↪ m ⊆ y ⟩
  sat→⊆ m sat z z∈ₛ =
    ∈∈ₛ {a = z} {b = y} .fst (fromInner z∈A)
    where
    z∈x : ⟨ z ∈ˢ ⟪ Lset σ ⟫↪ m ⟩
    z∈x = ∈∈ₛ {a = z} {b = ⟪ Lset σ ⟫↪ m} .snd z∈ₛ
    m∈A : ⟨ ⟪ Lset σ ⟫↪ m ∈ˢ Lset σ ⟩
    m∈A = ∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m)
    z∈A : ⟨ z ∈ˢ Lset σ ⟩
    z∈A = Atrans {x = ⟪ Lset σ ⟫↪ m} {y = z} z∈x m∈A
    xm : DefC.SM
    xm = z , z∈A
    inner-mem : ⟨ fst xm ∈ˢ fst (DefC.ι m) ⟩
    inner-mem = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (ιfst m)) z∈x
    inner-out : ⟨ fst xm ∈ˢ fst (DefC.ι mᵧ) ⟩
    inner-out = sat xm inner-mem
    fromInner : ⟨ z ∈ˢ Lset σ ⟩ → ⟨ z ∈ˢ y ⟩
    fromInner _ = subst (λ w → ⟨ z ∈ˢ w ⟩) qᵧ
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (ιfst mᵧ) inner-out)

  ⊆→sat : (m : ⟪ Lset σ ⟫)
        → ⟨ ⟪ Lset σ ⟫↪ m ⊆ y ⟩
        → ⟨ (DefC.ι m ∷ []) DefC.⊨ᵐ φ ⟩
  ⊆→sat m sub xm xm∈ =
    subst (λ w → ⟨ fst xm ∈ˢ w ⟩) (sym (ιfst mᵧ))
      (subst (λ w → ⟨ fst xm ∈ˢ w ⟩) (sym qᵧ)
        (∈∈ₛ {a = fst xm} {b = y} .snd
          (sub (fst xm)
            (∈∈ₛ {a = fst xm} {b = ⟪ Lset σ ⟫↪ m} .fst
              (subst (λ w → ⟨ fst xm ∈ˢ w ⟩) (ιfst m) xm∈)))))

  mem→subseteq : (x : S) → ⟨ x ∈ˢ DefC.defSet φ ⟩ → ⟨ x ⊆ y ⟩
  mem→subseteq x x∈ = PT.rec (isPropΠ λ z → isPropΠ λ _ → snd (z ∈ₛ y))
    (λ { ((m , h) , q) → subst (λ w → ⟨ w ⊆ y ⟩) q
           (sat→⊆ m (subst ⟨_⟩ (DefC.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
    x∈

  subseteq→mem : (x : S) → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ x ⊆ y ⟩ → ⟨ x ∈ˢ DefC.defSet φ ⟩
  subseteq→mem x x∈ sub =
    let (m , q) = ∈-asFiber {a = x} {b = Lset σ} x∈
    in subst (λ w → ⟨ w ∈ˢ DefC.defSet φ ⟩) q
         (subst ⟨_⟩ (sym (DefC.defSet-mem φ m))
           (⊆→sat m (subst (λ w → ⟨ w ⊆ y ⟩) (sym q) sub)))

-- THE CONSUMER.  W2: one formula, two hypotheses, then Describes.
-- IT IS NOT THE OBLIGATION: the obligation has no extra hypotheses.
from-hyps : (σ y : S) → ⟨ y ∈ˢ Lset σ ⟩
          → Dee⊆stage σ y → StagePowDef σ y
          → Describes σ y
from-hyps σ y y∈ dee⊆ spd = ∣ C.φ , eq ∣₁
  where
  module C = Carve σ y y∈
  sub₁ : ⟨ C.DefC.defSet C.φ ⊆ 𝒟ₒ y ⟩
  sub₁ x x∈ₛ = ∈∈ₛ {a = x} {b = 𝒟ₒ y} .fst
    (spd x
      (DefOf.defSet⊆A (Lset σ) C.φ x
        (∈∈ₛ {a = x} {b = C.DefC.defSet C.φ} .snd x∈ₛ))
      (C.mem→subseteq x (∈∈ₛ {a = x} {b = C.DefC.defSet C.φ} .snd x∈ₛ)))
  sub₂ : ⟨ 𝒟ₒ y ⊆ C.DefC.defSet C.φ ⟩
  sub₂ x x∈ₛ = ∈∈ₛ {a = x} {b = C.DefC.defSet C.φ} .fst
    (C.subseteq→mem x
      (dee⊆ x (∈∈ₛ {a = x} {b = 𝒟ₒ y} .snd x∈ₛ))
      λ z z∈ₛ → ∈∈ₛ {a = z} {b = y} .fst
        (𝒟ₒ∋⊆ y x (∈∈ₛ {a = x} {b = 𝒟ₒ y} .snd x∈ₛ) z
          (∈∈ₛ {a = z} {b = x} .snd z∈ₛ)))
  eq : C.DefC.defSet C.φ ≡ 𝒟ₒ y
  eq = extensionality (C.DefC.defSet C.φ) (𝒟ₒ y) (sub₁ , sub₂)

-- The brief's type, named here so the search can point at it, and
-- NOT lifted to the probe module.  The witness reads
-- Target.describes-generic at the probe module
-- (scripts/pod/witness.py:278).  Leaving the name inside At is the
-- stated NO-GO: the closed term the brief asked for is not built,
-- and no refutation at a member the frame admits is built either.
module At (σ : S) where
  describes-generic : Type (ℓ-suc ℓ)
  describes-generic = (y : S) → ⟨ y ∈ˢ Lset σ ⟩ → Describes σ y

-- describes-generic is not lifted.  The witness meter reads
-- Target.describes-generic at this module (scripts/pod/witness.py:278)
-- and will not find it.
