{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.525] PROBE.  The leaf conversion: the bounded leaf `leafB`
-- becomes the machine's own unbounded leaf `DefAt`, by the delivered
-- `extAtB→extAt` with its `inK` hypothesis supplied from [LJ-1.522]'s
-- `defPow-closed-noCode`.  It runs in agents/tasks/LJ-1-525/ and lands
-- nothing in src/.
--
--   W3, FIRST      the match between the two leaf formulas, written
--                  alone in runs/W3.agda and typechecked before this
--                  file existed.  THEY MEET.
--   DELIVERED      leaf-unbounds, the briefed obligation, at the site
--                  `StepB.leafB` (src/L/Condensation.lagda.md:2398).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-525.Probe525 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Coding.Model {ℓ} using ( extAt; appAt )
open import L.Coding.Powerset {ℓ} lem using ( DefBody; DefAt )
open import L.Coding.Sequence {ℓ} lem using ( StepBody )
open import L.Condensation {ℓ} lem
  using ( extAtB; extAtB→extAt; module StepB; module StepAtB )

open import LJ-1-522.Probe522 {ℓ} lem using ( IsLimit; defPow-closed-noCode )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- SECTION 1.  THE TWO LEAF FORMULAS AT ONE FRAME, AND W3.
--
-- D-10 IS ANSWERED IN THE TYPES.  The machine's leaf is the third
-- conjunct of `StepBody` (src/L/Coding/Sequence.lagda.md:116),
-- `DefAt zero (suc zero)`, and `DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))`
-- (src/L/Coding/Powerset.lagda.md:443).  So the unbounded leaf's `φ` is
-- NOT `DefBody w`: it is two existentials over it, and those two
-- existentials produce exactly the environment `(v ∷ c ∷ z ∷ γ)` that
-- `defPow-closed-noCode` reads (agents/tasks/LJ-1-522/Probe522.agda:363).
-- The bounded leaf `leafB` (src/L/Condensation.lagda.md:2399-2402) is
-- `extAtB` over the SAME two existentials, each bounded by K.
-- ---------------------------------------------------------------------

-- The machine's leaf condition: `DefAt`'s own body.
leafFo : ∀ {n} → Fin n → Formula S (suc n)
leafFo w = ∃̇ (∃̇ (DefBody w))

-- The bounded leaf's condition: the shape `leafB` puts under `extAtB`.
leafBFo : ∀ {n} → Fin n → Formula S (suc (suc (suc n))) → Formula S (suc n)
leafBFo K ψB = ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) ψB)

-- THE MATCH (W3).  `extAtB→extAt`'s third argument, at the leaf's own
-- φ, built from [LJ-1.522].
--
-- MEASURED, AND IT IS THE FINDING OF THIS TASK: the unbounded leaf does
-- NOT carry the recorded value's membership in K, which is
-- `defPow-closed-noCode`'s eighth argument.  What carries it is `bwd`,
-- the machine-to-story direction, which `extAtB→extAt` ALREADY asks
-- for.  So `inK` costs this conversion no hypothesis of its own.
leaf-inK :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (w K : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩ → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
  → ⟨ fst x ∈ fst (lookup K γ) ⟩
leaf-inK α lim w K ψB γ qK W∈K leafFwd bwd x hx =
  PT.rec (snd (fst x ∈ fst (lookup K γ)))
    (λ { (c , (cK , hc)) → PT.rec (snd (fst x ∈ fst (lookup K γ)))
      (λ { (v , (vK , hv)) →
        defPow-closed-noCode α lim w K γ qK W∈K x c v vK
          (leafFwd x c v hv) })
      hc })
    (bwd x hx)

-- The story-to-machine direction of the leaf condition.  It is the
-- bounded existentials forgetting their bounds, over the ψ-level leaf
-- agreement.  `LeafAgree.back` (src/L/Condensation.lagda.md:7353-7358)
-- is what supplies that agreement, given its own telescope; this file
-- takes it as a hypothesis and builds nothing of it.
leaf-fwd :
    ∀ {n} (w K : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩ → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
leaf-fwd w K ψB γ leafFwd x =
  PT.rec (snd ((x ∷ γ) ⊨ leafFo w))
    (λ { (c , (_ , hc)) →
      PT.rec (snd ((x ∷ γ) ⊨ leafFo w))
        (λ { (v , (_ , hv)) → ∣ c , ∣ v , leafFwd x c v hv ∣₁ ∣₁ })
        hc })

-- ---------------------------------------------------------------------
-- SECTION 2.  THE CONVERSION, AT A GENERIC CARRIER (W2).
--
-- Nothing below is written at a fixed arity or a fixed slot.  The site
-- instances of sections 3 and 4 are instantiations of this one term and
-- add no content.
-- ---------------------------------------------------------------------
leaf-unbounds-gen :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (y K w : Fin n) (ψB : Formula S (suc (suc (suc n)))) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψB ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩ → ⟨ (x ∷ γ) ⊨ leafBFo K ψB ⟩)
  → ⟨ γ ⊨ extAtB y K (leafBFo K ψB) ⟩
  → ⟨ γ ⊨ DefAt y w ⟩
leaf-unbounds-gen α lim y K w ψB γ qK W∈K leafFwd bwd =
  extAtB→extAt y K (leafBFo K ψB) (leafFo w) γ
    (leaf-fwd w K ψB γ leafFwd)
    bwd
    (leaf-inK α lim w K ψB γ qK W∈K leafFwd bwd)

-- ---------------------------------------------------------------------
-- SECTION 3.  THE OBLIGATION, AT THE SITE.
--
-- `StepB.leafB` (src/L/Condensation.lagda.md:2398-2402) is the bounded
-- leaf, at the body environment d ∷ w ∷ c ∷ z ∷ γ.  Its slot zero is
-- the definable powerset d and its carrier is the step's w at slot one,
-- which is why the conclusion below is `DefAt zero (suc zero)`: the
-- THIRD CONJUNCT OF THE MACHINE'S OWN `StepBody`
-- (src/L/Coding/Sequence.lagda.md:116), at the same environment and the
-- same two slots.  Nothing is restated and no adapter is written: the
-- two sides meet by unfolding.
-- ---------------------------------------------------------------------
leaf-unbounds :
    (α : V ℓ) → IsLimit α
  → ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (sv b sf K : Fin m)
  → (γ : S ^ (4 + m))
  → fst (lookup (suc (suc (suc (suc K)))) γ) ≡ Lset α
  → ⟨ fst (lookup (suc zero) γ)
      ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψ ⟩
                 → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody (suc zero) ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo (suc zero) ⟩
             → ⟨ (x ∷ γ) ⊨ leafBFo (suc (suc (suc (suc K)))) ψ ⟩)
  → ⟨ γ ⊨ StepB.leafB {m} ψ sv b sf K ⟩
  → ⟨ γ ⊨ DefAt zero (suc zero) ⟩
leaf-unbounds α lim ψ sv b sf K γ qK W∈K leafFwd bwd =
  leaf-unbounds-gen α lim zero (suc (suc (suc (suc K)))) (suc zero) ψ γ
    qK W∈K leafFwd bwd

-- ---------------------------------------------------------------------
-- SECTION 4.  THE SAME TERM AT THE CLASS CARRIER.
--
-- `StepAtB` (src/L/Condensation.lagda.md:2444-2452) is the concrete
-- step matrix: the bound is the class carrier at slot zero of γ, so the
-- leaf's bound slot is `suc (suc (suc (suc zero)))`, and the leaf
-- content is `DefBodyB` at the step's carrier.  This instance pins both
-- and adds nothing.
-- ---------------------------------------------------------------------
leafB-at-class :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (sv b sf : Fin n)
  → (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  → (γ : S ^ (5 + n))
  → fst (lookup (suc (suc (suc (suc zero)))) γ) ≡ Lset α
  → ⟨ fst (lookup (suc zero) γ)
      ∈ fst (lookup (suc (suc (suc (suc zero)))) γ) ⟩
  → ((x c v : S)
     → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ StepAtB.ψ sv b sf
                              N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
     → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody (suc zero) ⟩)
  → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo (suc zero) ⟩
             → ⟨ (x ∷ γ) ⊨ leafBFo (suc (suc (suc (suc zero))))
                              (StepAtB.ψ sv b sf
                                N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1) ⟩)
  → ⟨ γ ⊨ StepB.leafB {suc n}
            (StepAtB.ψ sv b sf N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)
            (suc sv) (suc b) (suc sf) zero ⟩
  → ⟨ γ ⊨ DefAt zero (suc zero) ⟩
leafB-at-class α lim sv b sf N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ =
  leaf-unbounds α lim
    (StepAtB.ψ sv b sf N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)
    (suc sv) (suc b) (suc sf) zero γ

-- ---------------------------------------------------------------------
-- SECTION 5.  THE PRICE OF `inK` WITHOUT `bwd`, MEASURED AND NOT USED.
--
-- The delivered conversion above pays nothing for `inK`, because `bwd`
-- is in `extAtB→extAt`'s own telescope.  A consumer that wants `inK`
-- alone, without the machine-to-story direction, buys instead the
-- hypothesis below: the recorded satisfaction set of an unbounded leaf
-- witness lies in K.  That is one of [LJ-1.520]'s five open rows
-- (agents/tasks/LJ-1-522/lj-1.522-report.md:180-184), and it is stated
-- here so the next brief can compare the two telescopes.  NOT USED by
-- the obligation.
-- ---------------------------------------------------------------------
leaf-inK-valK :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (w K : Fin n) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩
                 → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  → (x : S) → ⟨ (x ∷ γ) ⊨ leafFo w ⟩
  → ⟨ fst x ∈ fst (lookup K γ) ⟩
leaf-inK-valK α lim w K γ qK W∈K valK x =
  PT.rec (snd (fst x ∈ fst (lookup K γ)))
    (λ { (c , hc) → PT.rec (snd (fst x ∈ fst (lookup K γ)))
      (λ { (v , hv) →
        defPow-closed-noCode α lim w K γ qK W∈K x c v (valK x c v hv) hv })
      hc })

-- ---------------------------------------------------------------------
-- SECTION 6.  WHAT THE NEXT LINK COSTS, MEASURED AND NOT BUILT.
--
-- The leaf sits inside a body, and the body is the next link.  The two
-- bodies are `StepB.bodyB` (src/L/Condensation.lagda.md:2404-2408) and
-- the machine's `StepBody` (src/L/Coding/Sequence.lagda.md:113-117).
-- Both are written below as ONE frame applied to ONE leaf, and both
-- equations are `refl`.
--
-- SO THE OTHER THREE CONJUNCTS ARE THE SAME FORMULA, NOT AGREEING
-- FORMULAS: the membership atom, the `appAt` application and the
-- payload atom coincide on the nose.  The next link is one congruence
-- over `stepFrame` and the leaf conversion above, and it buys no
-- further row.  This file does NOT build it: it prices it.
-- ---------------------------------------------------------------------
stepFrame : ∀ {m} (b f : Fin m) → Formula S (4 + m) → Formula S (4 + m)
stepFrame b f leaf =
  (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc b)))))
  ∧̇ ( appAt (suc (suc (suc (suc f)))) (suc (suc zero)) (suc zero)
     ∧̇ ( leaf ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

bodyB-is-frame :
    ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (sv b sf K : Fin m)
  → StepB.bodyB {m} ψ sv b sf K
    ≡ stepFrame b sf (StepB.leafB {m} ψ sv b sf K)
bodyB-is-frame ψ sv b sf K = refl

stepBody-is-frame :
    ∀ {m} (b f : Fin m)
  → StepBody b f ≡ stepFrame b f (DefAt zero (suc zero))
stepBody-is-frame b f = refl
