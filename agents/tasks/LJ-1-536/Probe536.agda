{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.536] PROBE.  StageHigh, which four routes have arrived at.
-- It runs in agents/tasks/LJ-1-536/ and lands nothing in src/.
--
--   D-10, FIRST    what `𝒟ₒ-intro` wants, and whether [LJ-1.520]'s
--                  graded formula is that formula.  Sections 1 and 2.
--   W3, SECOND     runs/W3.agda, written and typechecked ALONE before
--                  this file existed.  Sections 1 to 3 rerun its terms
--                  so that the finding and the obligation stand in one
--                  file.
--   OBLIGATION     StageHigh.  Section 6 states it.  Section 5 reduces
--                  it, GREEN and total in γ, to one statement about the
--                  sequence BELOW γ.  Section 7 says what is left.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-536.Probe536 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∨̇_; ⊤̇ )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans
        ; Lset-mono; Lset→isL; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pr∈Lset-suc )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; IsHier; Recorded )
open import LJ-1-520.Probe520 {ℓ} lem using ( levelFo-Σ₁ )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; extensionality; _⊆_; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- ===================================================================
-- SECTION 1.  D-10, BEFORE ANY AGDA: WHAT THE DOOR WANTS.
--
-- The brief's premise 9 and 10 name the route into a stage: `Lset-in`
-- (src/L/Constructible.lagda.md:319) through `𝒟ₒ-intro` (:301-304).
-- `Door` writes that premise out, and `door` is the only admissible
-- evidence that it is that premise and not a paraphrase: the
-- ascription typechecks exactly when the two types agree.
--
-- THE DOOR WANTS THREE THINGS AT ONCE, and each is a separate demand:
--   (a) the constant domain is `⟪ A ⟫`, the MEMBERS OF THE STAGE, not
--       the class carrier `S`;
--   (b) the arity is exactly 1;
--   (c) the equation is `defSet A φ ≡ x`, and `defSet`
--       (src/L/Definability.lagda.md:111-112) reads `φ` under the
--       INNER satisfaction of the world `(A , ∈)`, whose quantifiers
--       range over `⟪ A ⟫` and over nothing else.
-- ===================================================================

Door : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Door A x = ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁

door : (A x : V ℓ) → Door A x → ⟨ x ∈ 𝒟ₒ A ⟩
door = 𝒟ₒ-intro


-- ===================================================================
-- SECTION 2.  AND THE ANSWER IS THAT [LJ-1.520]'S FORMULA IS ADJACENT.
--
-- `graded` re-ascribes what that task delivered, imported from its own
-- probe so nothing can drift (agents/tasks/LJ-1-520/Probe520.agda:171,
-- and the audit rule at dev/pod/audit-2026-08-20.md:34).  It is a
-- formula at the CLASS carrier `S`, at arity `n`, with a `Σ₁` grade.
-- Against the door's three demands it misses (a) and (b) as syntax and
-- (c) as meaning.
--
-- (a) AND (b) ARE NOT THE FINDING.  `[LJ-1.520]` proved the formula
-- carries no constant (`countFo ≡ 0` by `refl`,
-- agents/tasks/LJ-1-520/runs/CountCheck.agda:18-19), so `erase` then
-- `embed` (src/FOL/Manipulation/Relabelling.lagda.md:117) move it to
-- ANY constant domain, and two binders fix the arity.  Syntax is not
-- what blocks.
--
-- (c) IS THE FINDING, AND IT IS A REFUTATION.  The tree has exactly
-- one delivered bridge that turns an EXTERNAL formula into the door's
-- inner reading: `L.Axioms.Separation.AtStage`
-- (src/L/Axioms/Separation.lagda.md:119-231), re-ascribed in
-- runs/W3.agda.  Its hypothesis is `Δ₀`.  `levelFo` has no `Δ₀`
-- witness and cannot acquire one: `Δ₀` has no constructor indexed by
-- an unbounded existential (src/FOL/LevyHierarchy.lagda.md:47-57) and
-- `levelFo` is thirteen of them
-- (agents/tasks/LJ-1-520/Probe520.agda:167-169).  Agda checks it by
-- absurd pattern.
-- ===================================================================

graded : {n : ℕ} (w b : Fin n) → Σ[ ψ ∈ Formula S n ] Σ₁ ψ
graded = levelFo-Σ₁

no-Δ₀-levelFo : {n : ℕ} (w b : Fin n) → Δ₀ (fst (levelFo-Σ₁ w b)) → Empty.⊥
no-Δ₀-levelFo w b ()


-- ===================================================================
-- SECTION 3.  THE VOCABULARY, TAKEN FROM [LJ-1.519]'S PROBE.
--
-- `step` and `seq` are that task's, verbatim, except that they are
-- written at the TOP LEVEL here and not inside a module parameterised
-- by a limit `α`: neither definition ever used α, which is exactly the
-- brief's point (agents/tasks/LJ-1-519/Probe519.agda:198-199, :137).
-- ===================================================================

step : ℕ → V ℓ → V ℓ
step zero    γ = γ
step (suc n) γ = sucV (step n γ)

-- An ordinal is an element of L, because it appears at the stage after
-- itself (src/L/Ordinal/Stages.lagda.md:434) and stages are inside L
-- (src/L/Constructible.lagda.md:395).
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

-- Devlin's (L_δ | δ ≤ γ): the internal hierarchy at sucV γ, because
-- sucV γ is exactly the ordinals δ ≤ γ.
-- agents/tasks/LJ-1-519/Probe519.agda:137.
seq : (γ : V ℓ) → IsOrd γ → S
seq γ oγ = hierL (sucV γ) (isL-ord (sucV γ) (suc-ord oγ)) (suc-ord oγ)

seq-spec : (γ : V ℓ) (oγ : IsOrd γ) → IsHier (sucV γ) (seq γ oγ)
seq-spec γ oγ = hierL-spec (sucV γ) (isL-ord (sucV γ) (suc-ord oγ)) (suc-ord oγ)


-- ===================================================================
-- SECTION 4.  WHERE ONE RECORDED PAIR LIVES.
--
-- A stage is a member of the next stage, and an ordinal is too, so the
-- Kuratowski pair of the two is a member two stages further up
-- (src/L/Axioms/Basic.lagda.md:596-599).  THREE STAGES ABOVE ITS OWN
-- INDEX, and that is where Devlin's four comes from: the sequence at
-- δ ≤ γ has its largest entry at γ, hence inside `Lset (step 3 γ)`,
-- hence the sequence itself one stage above that.
-- ===================================================================

Lset∈suc : (β : V ℓ) → ⟨ Lset β ∈ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

pr-at : (δ : V ℓ) → IsOrd δ → ⟨ pr δ (Lset δ) ∈ Lset (step 3 δ) ⟩
pr-at δ oδ = pr∈Lset-suc (sucV δ) δ (Lset δ) (ord∈Lset-suc δ oδ) (Lset∈suc δ)


-- ===================================================================
-- SECTION 5a.  THE REDUCTION.  StageHigh, from the sequence BELOW γ.
--
-- `HierBelow γ` says the internal hierarchy at γ itself, which records
-- the pairs at δ ∈ γ, is a member of `Lset (step 3 γ)`.  Given that,
-- the sequence at δ ≤ γ is that set with ONE pair adjoined, and the
-- adjunction is a two-constant definable subset of the same stage:
--
--     φ(z)  :=  z ∈ ḣ  ∨  z ≐ q̇
--
-- with `ḣ` the hierarchy below γ and `q̇` the pair at γ.  Both constants
-- are members of `Lset (step 3 γ)`: `q̇` by section 4, `ḣ` by the
-- hypothesis.  Nothing here is a quantifier, so the formula is the
-- cheapest shape the door admits.
--
-- THIS IS THE SUCCESSOR STEP OF THE INDUCTION AS WELL AS THE
-- REDUCTION, because `HierBelow (sucV α)` IS `StageHigh` at α.
-- ===================================================================

HierBelow : (γ : V ℓ) → IsOrd γ → Type (ℓ-suc ℓ)
HierBelow γ oγ = ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset (step 3 γ) ⟩

module AdjoinAt (σ : V ℓ) (oσ : IsOrd σ)
                (h q : V ℓ) (h∈ : ⟨ h ∈ Lset σ ⟩) (q∈ : ⟨ q ∈ Lset σ ⟩)
                (T : S)
                (out : (x : S) → (⟨ fst x ∈ h ⟩ ⊎ (fst x ≡ q))
                     → ⟨ fst x ∈ fst T ⟩)
                (into : (x : S) → ⟨ fst x ∈ fst T ⟩
                      → ∥ ⟨ fst x ∈ h ⟩ ⊎ (fst x ≡ q) ∥₁)
                where
  private
    module DefA = DefOf (Lset σ)

    mₕ : ⟪ Lset σ ⟫
    mₕ = ∈-asFiber {a = h} {b = Lset σ} h∈ .fst

    qₕ : ⟪ Lset σ ⟫↪ mₕ ≡ h
    qₕ = ∈-asFiber {a = h} {b = Lset σ} h∈ .snd

    mQ : ⟪ Lset σ ⟫
    mQ = ∈-asFiber {a = q} {b = Lset σ} q∈ .fst

    qQ : ⟪ Lset σ ⟫↪ mQ ≡ q
    qQ = ∈-asFiber {a = q} {b = Lset σ} q∈ .snd

    φ : Formula ⟪ Lset σ ⟫ 1
    φ = (var zero ∈̇ con mₕ) ∨̇ (var zero ≐ con mQ)

    Atrans = layer-trans (Lset-layer σ)

    defSet≡ : DefA.defSet φ ≡ fst T
    defSet≡ = extensionality (DefA.defSet φ) (fst T) (sub₁ , sub₂)
      where
      fromSat : (m : ⟪ Lset σ ⟫) → ⟨ (DefA.ι m ∷ []) DefA.⊨ᵐ φ ⟩
              → ⟨ ⟪ Lset σ ⟫↪ m ∈ fst T ⟩
      fromSat m sat = PT.rec (snd (x ∈ fst T)) branch sat
        where
        x : V ℓ
        x = ⟪ Lset σ ⟫↪ m

        xS : S
        xS = x , Lset→isL σ oσ x
                   (∈∈ₛ {a = x} {b = Lset σ} .snd (∈ₛ⟪ Lset σ ⟫↪ m))

        branch : ⟨ x ∈ ⟪ Lset σ ⟫↪ mₕ ⟩ ⊎ (x ≡ ⟪ Lset σ ⟫↪ mQ)
               → ⟨ x ∈ fst T ⟩
        branch (inl x∈h) = out xS (inl (subst (λ w → ⟨ x ∈ w ⟩) qₕ x∈h))
        branch (inr p)   = out xS (inr (p ∙ qQ))

      sub₁ : ⟨ DefA.defSet φ ⊆ fst T ⟩
      sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = fst T} .fst
        (PT.rec (snd (y ∈ fst T))
          (λ { ((m , hm) , qm) →
            subst (λ w → ⟨ w ∈ fst T ⟩) qm
              (fromSat m
                (subst ⟨_⟩ (DefA.defSet-mem φ m) ∣ (m , hm) , refl ∣₁)) })
          (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ))

      sub₂ : ⟨ fst T ⊆ DefA.defSet φ ⟩
      sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DefA.defSet φ} .fst
        (PT.rec (snd (y ∈ DefA.defSet φ)) fromDisj (into yS y∈))
        where
        y∈ : ⟨ y ∈ fst T ⟩
        y∈ = ∈∈ₛ {a = y} {b = fst T} .snd y∈ₛ

        yS : S
        yS = y , isL-trans {x = fst T} {y = y} y∈ (snd T)

        place : ⟨ y ∈ Lset σ ⟩ → (⟨ y ∈ h ⟩ ⊎ (y ≡ q))
              → ⟨ y ∈ DefA.defSet φ ⟩
        place y∈σ d =
          subst (λ w → ⟨ w ∈ DefA.defSet φ ⟩) q'
            (subst ⟨_⟩ (sym (DefA.defSet-mem φ m')) (sat d))
          where
          m' : ⟪ Lset σ ⟫
          m' = ∈-asFiber {a = y} {b = Lset σ} y∈σ .fst

          q' : ⟪ Lset σ ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset σ} y∈σ .snd

          sat : (⟨ y ∈ h ⟩ ⊎ (y ≡ q)) → ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ φ ⟩
          sat (inl y∈h) =
            ∣ inl (subst (λ w → ⟨ w ∈ ⟪ Lset σ ⟫↪ mₕ ⟩) (sym q')
                     (subst (λ w → ⟨ y ∈ w ⟩) (sym qₕ) y∈h)) ∣₁
          sat (inr y≡q) = ∣ inr (q' ∙ y≡q ∙ sym qQ) ∣₁

        fromDisj : ⟨ y ∈ h ⟩ ⊎ (y ≡ q) → ⟨ y ∈ DefA.defSet φ ⟩
        fromDisj (inl y∈h) = place (Atrans {x = h} {y = y} y∈h h∈) (inl y∈h)
        fromDisj (inr y≡q) =
          place (subst (λ w → ⟨ w ∈ Lset σ ⟩) (sym y≡q) q∈) (inr y≡q)

  adjoin∈ : ⟨ fst T ∈ Lset (sucV σ) ⟩
  adjoin∈ = subst (λ w → ⟨ fst T ∈ w ⟩) (sym (Lset-suc σ))
    (𝒟ₒ-intro (Lset σ) (fst T) ∣ φ , defSet≡ ∣₁)


-- ===================================================================
-- SECTION 5b.  THE INSTANTIATION.  `AdjoinAt` at the stage `step 3 γ`,
-- with the sequence as the described set.
--
-- P-l IS WHY SECTION 5a IS ABSTRACT AND THIS SECTION IS THIN.  The
-- first form of this probe carved at `step 3 γ` directly, so the types
-- of the two constants and of the formula named
-- `⟪ Lset (sucV (sucV (sucV γ))) ⟫`, and `sucV` is transparent.  IT
-- EXHAUSTED 8 GB (runs/full-1.time).  The same mathematics, stated at
-- a variable stage, checks in 1.00 s and 299 MB
-- (runs/Control536.agda, runs/ctl-0.time).  A controlled pair inside
-- one task, and dev/LESSONS.md:2357 is where the law lives.
-- ===================================================================

module Adjoin (γ : V ℓ) (oγ : IsOrd γ) (hyp : HierBelow γ oγ) where
  private
    H : S
    H = hierL γ (isL-ord γ oγ) oγ

    Q : V ℓ
    Q = pr γ (Lset γ)

    spH : IsHier γ H
    spH = hierL-spec γ (isL-ord γ oγ) oγ

    sp : IsHier (sucV γ) (seq γ oγ)
    sp = seq-spec γ oγ

    -- A pair recorded below γ, or the pair AT γ, is recorded at δ ≤ γ.
    out : (x : S) → (⟨ fst x ∈ fst H ⟩ ⊎ (fst x ≡ Q))
        → ⟨ fst x ∈ fst (seq γ oγ) ⟩
    out x (inl x∈H) = subst ⟨_⟩ (sym (sp x))
      (PT.map (λ { (c , (c∈γ , eq)) →
                   c , (∈sucV-inl {A = γ} {x = fst c} c∈γ , eq) })
        (subst ⟨_⟩ (spH x) x∈H))
    out x (inr p) = subst ⟨_⟩ (sym (sp x))
      ∣ (γ , isL-ord γ oγ) , (self∈sucV γ , p) ∣₁

    -- And nothing else is.  `sucV γ` splits at its own successor step.
    into : (x : S) → ⟨ fst x ∈ fst (seq γ oγ) ⟩
         → ∥ ⟨ fst x ∈ fst H ⟩ ⊎ (fst x ≡ Q) ∥₁
    into x x∈ = PT.rec PT.squash₁ pick (subst ⟨_⟩ (sp x) x∈)
      where
      pick : Σ[ c ∈ S ] (⟨ fst c ∈ sucV γ ⟩
               × (fst x ≡ pr (fst c) (Lset (fst c))))
           → ∥ ⟨ fst x ∈ fst H ⟩ ⊎ (fst x ≡ Q) ∥₁
      pick (c , (c∈ , eq)) = ∈sucV-elim {A = γ} {x = fst c} PT.squash₁ c∈
        (λ c∈γ → ∣ inl (subst ⟨_⟩ (sym (spH x)) ∣ c , (c∈γ , eq) ∣₁) ∣₁)
        (λ c≡γ → ∣ inr (eq ∙ cong (λ w → pr w (Lset w)) c≡γ) ∣₁)

  -- THE PAYOFF.  The sequence at δ ≤ γ is a member of the stage after
  -- `step 3 γ`, which is `step 4 γ`.
  seq∈ : ⟨ fst (seq γ oγ) ∈ Lset (step 4 γ) ⟩
  seq∈ = AdjoinAt.adjoin∈ (step 3 γ) (suc-ord (suc-ord (suc-ord oγ)))
           (fst H) Q hyp (pr-at γ oγ) (seq γ oγ) out into


-- ===================================================================
-- SECTION 6.  THE OBLIGATION, AND WHAT IT NOW COSTS.
--
-- `StageHigh` is [LJ-1.519]'s type, verbatim
-- (agents/tasks/LJ-1-519/Probe519.agda:218-220).  It is NOT inhabited
-- below and no postulate stands in for it.  What IS delivered is the
-- reduction: total in γ, with no limit hypothesis, no α and no use of
-- `ω ∈ γ`.
-- ===================================================================

StageHigh : Type (ℓ-suc ℓ)
StageHigh = (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ γ ⟩
          → ⟨ fst (seq γ oγ) ∈ Lset (step 4 γ) ⟩

HierBelowAll : Type (ℓ-suc ℓ)
HierBelowAll = (γ : V ℓ) (oγ : IsOrd γ) → HierBelow γ oγ

reduction : HierBelowAll → StageHigh
reduction hb γ oγ _ = Adjoin.seq∈ γ oγ (hb γ oγ)

-- AND IT DOES NOT NEED THE WHOLE CLASS.  The reduction is pointwise:
-- one ordinal's hypothesis pays that ordinal's obligation.
reduction-at : (γ : V ℓ) (oγ : IsOrd γ) → HierBelow γ oγ
             → ⟨ fst (seq γ oγ) ∈ Lset (step 4 γ) ⟩
reduction-at = Adjoin.seq∈

-- THE STEP, READ THE OTHER WAY, IS NOT WRITTEN HERE AND THE REASON IS
-- MEASURED.  `HierBelow (sucV α) (suc-ord oα)` and the conclusion of
-- `reduction-at` at α unfold to the SAME term, so the row
--
--     successor-step : (α : V ℓ) (oα : IsOrd α) → HierBelow α oα
--                    → HierBelow (sucV α) (suc-ord oα)
--     successor-step α oα h = Adjoin.seq∈ α oα h
--
-- asks Agda for nothing but a conversion.  IT EXHAUSTS 8 GB.
--
-- THE COST IS LOCATED AND IT IS NOT THE HIERARCHY.  runs/Control536f
-- .agda is thirty lines, imports no chapter of src/, and states one
-- obligation: `refl : step 4 α ≡ step 3 (sucV α)`.  It costs 417.18 s
-- (runs/ctlf-0.time).  With `Lset` and `∈` added back the same row
-- costs 425.73 s (runs/Control536e.agda, runs/ctle-0.time), so the
-- tower contributes about eight seconds of four hundred and twenty six.
-- `sucV N = N ∪ ⁅ N ⁆s` is transparent
-- (Cubical.HITs.CumulativeHierarchy.Constructions:156-157, :160-161),
-- so two spellings of four successors normalize eight set layers twice.
-- This is law P-l (dev/LESSONS.md:2357) with the tower taken out of the
-- experiment.  The identity is real and the report states it in prose;
-- the term that would witness it is priced above the caliber.


-- ===================================================================
-- SECTION 7.  THE RESIDUE, STATED AND NOT INHABITED.
--
-- What is left is `HierBelow` at an ordinal that is NOT a successor.
-- `IsLimit` is [LJ-1.519]'s spelling of the tree's own two witnesses
-- (agents/tasks/LJ-1-519/Probe519.agda:57-58, :63, :72).
--
-- THE LIMIT DID NOT LEAVE.  [LJ-1.519] split Devlin's proof so that
-- Part B, this task's `StageHigh`, names no limit in its TYPE.  It
-- does not: the reduction above is total in γ.  But the induction that
-- pays `HierBelow` has exactly one case the adjunction cannot reach,
-- and that case is a limit.  The split moved the limit out of the
-- statement and into the induction; it did not remove it.
-- ===================================================================

IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = (δ : V ℓ) → ⟨ δ ∈ α ⟩ → ⟨ sucV δ ∈ α ⟩

HierBelowLimit : Type (ℓ-suc ℓ)
HierBelowLimit = (γ : V ℓ) (oγ : IsOrd γ) → IsLimit γ → HierBelow γ oγ
