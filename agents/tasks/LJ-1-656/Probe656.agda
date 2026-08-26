{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.656] PROBE.  The level formula, which is Devlin's own object.
--
--   THE OBLIGATION  `level-formula : LevelFormula`, [LJ-1.650]'s type
--                   (agents/tasks/LJ-1-650/Probe650.agda:322-328):
--                   ONE `Formula Code 2`, PLUS soundness at the stage,
--                   PLUS completeness at every ordinal of the stage.
--
--   src/ ONLY, and no cross-task import.  [LJ-1.650] measured that
--   importing a predecessor probe two or more links down the LJ chain
--   EXHAUSTS the wide caliber on the frame ALONE
--   (agents/tasks/LJ-1-650/lj-1.650-report.md:59-67).  Every type taken
--   from a predecessor is RESTATED here and cited at the line it was
--   read.
--
--   PART A OF TWO.  `runs/Probe656B.agda` holds section 6, the passage
--   between the stage and the class carrier, and it imports this file.
--   THE SPLIT IS A MEASURED RESTRUCTURING, NOT A STYLE CHOICE: with
--   section 6 in this file Agda was KILLED BY THE OPERATING SYSTEM
--   (runs/p-13.out, runs/p-14.out, runs/p-15.out, EXIT=137, SIGKILL)
--   while system-wide free memory read 4 percent and `omlx-server` held
--   15.7 GB.  The probe's own peak is about 1 GB against a 2 GB
--   caliber, so this is a SHARED-MACHINE resource fact and not a fact
--   about any term.  Split, each half elaborates in a smaller window and
--   the interface of this half survives a kill of the other.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-656.Probe656 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ⊤̇; ∃̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; Σ₁; σ-Δ₀; σ-∃; δ-∧; δ-∈; δ-∀∈ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling
  using ( mapFo; embed; embed-⊨; mapΔ₀ )
import FOL.Semantics
open import FOL.Count using ( module Count )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-in; Lset-out )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( 𝒟ₒ→isL )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module LevelHood0; module Amb; erase-Δ₀ )
open import L.Condensation {ℓ} lem using ( extAtB )
open import L.Coding.Model {ℓ} using ( extAt; extAt-in )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec; _∷_; []; lookup; map )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ
module AbsLC = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsLC using ( _^_ )
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 3.  THE FORMULA.  COMPONENT ONE OF THREE, AND IT IS BUILT.
--
--   [LJ-1.651] built the two-slot reading of the tree's own Sigma-0
--   level-hood matrix and instantiated it at the hull's code alphabet
--   (agents/tasks/LJ-1-651/Probe651.agda:141-142).  ITS SLOT ORDER IS
--   NOT THIS OBLIGATION'S.  [LJ-1.651] ends with one more `renameFo`,
--   `swap` (Probe651.agda:106-111), which puts the ORDINAL at slot 0
--   for [LJ-1.642]'s consumers.  `LevelFormula` reads the environment
--   `v ∷ γ ∷ []`, VALUE first (Probe650.agda:325).  So the term this
--   obligation wants is [LJ-1.651]'s `step3` (Probe651.agda:100-101),
--   one rename EARLIER, and the swap is not applied.
--
--   Steps 1 to 3 are [LJ-1.651]'s, restated at the line each was read.
-- =====================================================================

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- Probe651.agda:73-74.  The matrix carries no constant.
count-matrix : countFo LH0.matrix ≡ 0
count-matrix = refl

module Cnt = Count {ℓ = ℓ-suc ℓ} CS.S

-- AND THE ERASE IS TAKEN AT THE MATRIX, NOT AT THE END.  [LJ-1.651]
-- carried the class alphabet all the way and slid it to `Code` with one
-- `mapFo` (Probe651.agda:128-129, :141-142).  This probe erases FIRST, so
-- every later step is built parameter-free and `embed` enters ANY
-- alphabet with the meaning unmoved (`embed-⊨`,
-- src/FOL/Manipulation/Relabelling.lagda.md:188-190).  Section 6 is why:
-- the same formula has to be read at THREE alphabets, and a
-- parameter-free core makes that free instead of a proof obligation.
-- SEALED AT BIRTH, AND THE SEAL IS MEASURED, NOT DECORATION.  `erase`
-- of the level-hood matrix is a TRANSPARENT construction over a formula
-- tree with a fourteen-slot `DefBodyB` inside it, and law P-l says a
-- statement may be ABOUT such a thing without dragging its PRESENTATION
-- into its type.  Left transparent, every type in part B that mentions
-- it invites Agda to unfold `erase` over the whole tree again; part B
-- was KILLED that way (runs/pb-2.out, 262.99 s, 985,792,512 bytes of
-- resident set, terminated by signal).  `opaque` makes it an ATOM and the two read
-- lemmas below are the only places it opens.  Same idiom, same reason,
-- as `leastSearch` at src/L/Hull.lagda.md:388-392.
opaque
  matrix₀ : Formula (⊥* {ℓ-suc ℓ}) 4
  matrix₀ = Cnt.erase LH0.matrix count-matrix

opaque
  unfolding matrix₀
  Δ₀-matrix₀ : Δ₀ matrix₀
  Δ₀-matrix₀ = erase-Δ₀ LH0.matrix count-matrix LH0.Δ₀-matrix

  -- src/L/BoundedSubset.lagda.md:840-852 read back: the erased matrix
  -- embedded at the class alphabet IS the tree's own matrix.
  matrix₀-inv : embed matrix₀ ≡ LH0.matrix
  matrix₀-inv = Cnt.erase-inv LH0.matrix count-matrix

-- Probe651.agda:81-82.  Close the unused `u` slot: env v ∷ γ ∷ K.
step1 : Formula (⊥* {ℓ-suc ℓ}) 3
step1 = ∃̇ matrix₀

-- Probe651.agda:87-88.  The grade certificate for the first closure.
Σ₁-step1 : Σ₁ step1
Σ₁-step1 = σ-∃ (σ-Δ₀ Δ₀-matrix₀)

-- Probe651.agda:91-97.  Rotate the bound K to the front: env K ∷ v ∷ γ.
rot : Fin 3 → Fin 3
rot zero             = suc zero
rot (suc zero)       = suc (suc zero)
rot (suc (suc zero)) = zero

step2 : Formula (⊥* {ℓ-suc ℓ}) 3
step2 = renameFo rot step1

-- Probe651.agda:100-101.  Close the bound K: env v ∷ γ.  THE OBLIGATION'S
-- OWN SLOT ORDER, and [LJ-1.651] stops one rename past it.
step3 : Formula (⊥* {ℓ-suc ℓ}) 2
step3 = ∃̇ step2

-- THE SAME THREE STEPS, AS ONE CONSTRUCTOR, GENERIC IN THE ALPHABET.
-- `step3` above is `levelFo matrix₀`.  Building the closure at the
-- TARGET alphabet, rather than embedding the closed formula, keeps the
-- tree's commuting law for `mapFo` against `renameFo` off this probe's
-- bill: the tree delivers `mapFo-comp` but no `mapFo`/`renameFo`
-- commutation, and section 6 would need one.
levelFo : ∀ {ℓc} {K : Type ℓc} → Formula K 4 → Formula K 2
levelFo m = ∃̇ (renameFo rot (∃̇ m))

step3-is-levelFo : step3 ≡ levelFo matrix₀
step3-is-levelFo = refl

-- =====================================================================
-- SECTION 3B.  THE ORDINALITY CONJUNCT, AND WHY THE OBLIGATION FORCES
--              IT INTO THE FORMULA.
--
--   `LevelFormula`'s soundness half quantifies over EVERY pair of stage
--   members and carries NO ordinality hypothesis
--   (agents/tasks/LJ-1-650/Probe650.agda:325).  The bounded matrix does
--   not decide it, and the tree's ONLY delivered landing demands it:
--   `ride-only` takes `IsOrd (fst (lookup b γ))`
--   (src/L/Condensation.lagda.md:422-425).  So on the route the tree
--   delivers, the formula has to SAY it, at slot 1.  A route that
--   proves soundness some other way is not measured here.
--
--   `isOrdAt` (src/L/BoundedSubset.lagda.md:74-78) says it at slot 0 of
--   a one-slot environment.  A `renameFo` would move it, but the tree
--   carries no grade-preservation theorem for `renameFo`
--   (agents/tasks/LJ-1-651/lj-1.651-report.md, section 4's open note),
--   so the two-slot reading is written out instead and its Δ₀ witness
--   is the same four constructors.
-- =====================================================================

-- env v ∷ x: "x is transitive and every member of x is transitive".
ordAt1 : Formula (⊥* {ℓ-suc ℓ}) 2
ordAt1 =
  (∀̇∈ (var (suc zero))
    (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc (suc zero))))))
  ∧̇ (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-ordAt1 : Δ₀ ordAt1
Δ₀-ordAt1 =
  δ-∧ (δ-∀∈ (δ-∀∈ δ-∈))
      (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

-- src/L/BoundedSubset.lagda.md:813-820, at the shifted slot.
ordAt1-out : (a b : SV.S) → ⟨ (a ∷ b ∷ []) Amb.⊨ₚ ordAt1 ⟩ → IsOrd b
ordAt1-out a b h =
    ( λ {x₁} {y} y∈x₁ x₁∈b → h .fst x₁ x₁∈b y y∈x₁ )
  , ( λ c c∈b {x₁} {y} y∈x₁ x₁∈c → h .snd c c∈b x₁ x₁∈c y y∈x₁ )

ordAt1-in : (a b : SV.S) → IsOrd b → ⟨ (a ∷ b ∷ []) Amb.⊨ₚ ordAt1 ⟩
ordAt1-in a b o =
    ( λ c c∈b d hd → o .fst {c} {d} hd c∈b )
  , ( λ c c∈b d d∈c e he → o .snd c c∈b {d} {e} he d∈c )

-- =====================================================================
-- SECTION 6.1.  READING ONE PARAMETER-FREE FORMULA AT TWO ALPHABETS IS
--               FREE, AT ANY STRUCTURE.
--
--   `embed-⊨` says a formula's meaning does not move when it enters a
--   constant domain.  Composed with itself it says the meaning does not
--   depend on WHICH domain, because both readings are the reading at the
--   empty domain and any two maps out of `⊥*` agree.  This probe needs
--   it three times over two structures, so it is stated once.
-- =====================================================================

module Alphabet (𝒮 : ZFStructure (hPropAlgebra (ℓ-suc ℓ))) where
  private module Sm = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮
  open ZFStructure 𝒮 using () renaming ( S to S𝒮 )

  -- The reading at ANY alphabet is the reading at the empty one.
  toAmb : ∀ {ℓa} {K : Type ℓa} (ι : K → S𝒮) {n : ℕ}
          (ψ : Formula (⊥* {ℓ-suc ℓ}) n) (γ : Vec S𝒮 n)
        → Sm.At._⊨_ K ι γ (embed ψ)
          ≡ Sm.At._⊨_ (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b) γ ψ
  toAmb ι ψ γ =
      embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮 ι ψ γ
    ∙ cong (λ h → Sm.At._⊨_ (⊥* {ℓ-suc ℓ}) h γ ψ)
           (funExt (λ b → Empty.rec* b))

  irrel : ∀ {ℓa ℓb} {K : Type ℓa} {K' : Type ℓb}
          (ι : K → S𝒮) (ι' : K' → S𝒮) {n : ℕ}
          (ψ : Formula (⊥* {ℓ-suc ℓ}) n) (γ : Vec S𝒮 n)
        → Sm.At._⊨_ K ι γ (embed ψ) ≡ Sm.At._⊨_ K' ι' γ (embed ψ)
  irrel ι ι' ψ γ = toAmb ι ψ γ ∙ sym (toAmb ι' ψ γ)

-- =====================================================================
-- SECTION 5.  WHY THE SOUNDNESS ROW CANNOT BE PAID AT THIS SHAPE.
--
--   THE TWO EXTENSION FRAMES DIFFER IN EXACTLY ONE PLACE, AND THE
--   DIFFERENCE IS THE WHOLE OBSTRUCTION.
--
--     extAt  y   φ = ∀̇ (z ∈ y ⇒ φ) ∧̇ ∀̇ (φ ⇒ z ∈ y)
--                    src/L/Coding/Model.lagda.md:662-664
--     extAtB y K φ = ∀̇∈ y φ        ∧̇ ∀̇∈ K (φ ⇒ z ∈ y)
--                    src/L/Condensation.lagda.md:103-105
--
--   The FIRST conjuncts say the same thing.  The SECOND does not: the
--   machine frame pins the value against EVERY satisfier of `φ`, and the
--   bounded frame pins it only against the satisfiers that lie in `K`.
--   So a `K` that catches no satisfier leaves the value FREE, and the
--   two terms below are that sentence, checked.
--
--   `graphBndAt` reaches its value slot through `extAtB` and through
--   nothing else (src/L/Condensation.lagda.md:2418 `stepBndAt = extAtB
--   v K witB`, and :2493 `graphBndAt = ∃̇∈ (var K) (approxBndAt ∧̇
--   stepBndAt)`).  `LsetGraphAt` reaches its value slot through `extAt`
--   (src/L/Coding/Sequence.lagda.md:119 `StepAt v b f = extAt v (...)`).
--   THIS IS WHY `GraphAgree` CARRIES A SITE-FACT PRICE and cannot be a
--   free row.  `extAtB→extAt` (src/L/Condensation.lagda.md:2514-2521)
--   states that price in the tree's own words: its third argument is
--   `(z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩`, "every
--   satisfier lies in K", and NOTHING in `levelHoodB` says it.
-- =====================================================================

-- THE SLACK, CHECKED.  An empty value slot and a bound that catches no
-- satisfier satisfy the bounded frame, whatever `φ` is.
extAtB-junk : ∀ {n} (y K : Fin n) (φ : Formula CS.S (suc n)) (δ : CS.S ^ n)
  → ((z : CS.S) → ⟨ fst z ∈ fst (lookup y δ) ⟩ → Empty.⊥)
  → ((z : CS.S) → ⟨ fst z ∈ fst (lookup K δ) ⟩
     → ⟨ (z ∷ δ) AbsLC.⊨ᵐ φ ⟩ → Empty.⊥)
  → ⟨ δ AbsLC.⊨ᵐ extAtB y K φ ⟩
extAtB-junk y K φ δ empty noSat =
    (λ z z∈ → Empty.rec (empty z z∈))
  , (λ z z∈K hz → Empty.rec (noSat z z∈K hz))

-- AND THE MACHINE FRAME HAS NO SUCH SLACK: it pins the value against
-- every satisfier there is, in or out of any bound.  This is the
-- delivered `extAt-in` (src/L/Coding/Model.lagda.md:671-673), named
-- here so the contrast is one file's two lines and not two files'.
extAt-pins : ∀ {n} (y : Fin n) (φ : Formula CS.S (suc n)) (δ : CS.S ^ n)
  → ⟨ δ AbsLC.⊨ᵐ extAt y φ ⟩
  → (z : CS.S) → ⟨ (z ∷ δ) AbsLC.⊨ᵐ φ ⟩ → ⟨ fst z ∈ fst (lookup y δ) ⟩
extAt-pins y φ δ = extAt-in y φ δ

-- =====================================================================
-- SECTION 1.  THE OBLIGATION'S TYPE, AND THE FRAME IT LIVES IN.
--
--   The telescope is `HullStage`'s (src/L/BoundedSubset.lagda.md:903-906)
--   and `LevelFormula` is [LJ-1.650]'s type, restated word for word.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  open T using ( Code; val; wit; _⊨c_ )

  -- agents/tasks/LJ-1-650/Probe650.agda:322-328, verbatim.
  LevelFormula : Type (ℓ-suc ℓ)
  LevelFormula =
    Σ[ lv ∈ Formula Code 2 ]
      ( ((v γ : HS.ASt.SL) → ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩ → fst v ≡ Lset (fst γ))
      × ((γ : HS.ASt.SL) → IsOrd (fst γ)
         → ∥ Σ[ v ∈ HS.ASt.SL ]
              ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩) ∥₁) )

  -- ===================================================================
  -- SECTION 2.  THE COMPLETENESS HALF'S *SET*, AND IT IS FREE.
  --
  --   Completeness asks for a `v` OF THE STAGE whose value is
  --   `Lset (fst γ)`.  That half owes nothing to any formula: the stage
  --   is closed under the level of each of its own ordinals, because
  --   `lam` is closed under successor.  Three delivered facts and one
  --   line of the definability chapter:
  --     `ord∈Lset→∈`  src/L/Ordinal/Stages.lagda.md:265
  --     `Lset-in`     src/L/Constructible.lagda.md:329
  --     `𝒟ₒ-intro`    src/L/Constructible.lagda.md:301
  --     `defSet⊤≡A`   src/L/Definability.lagda.md:178
  --   The last is the sentence "the whole carrier is one of its own
  --   definable subsets", which is what puts `Lset δ` inside `𝒟ₒ (Lset δ)`.
  -- ===================================================================

  self∈𝒟ₒ : (δ : SV.S) → ⟨ Lset δ ∈ˢ 𝒟ₒ (Lset δ) ⟩
  self∈𝒟ₒ δ =
    𝒟ₒ-intro (Lset δ) (Lset δ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset δ) ∣₁

  -- AND `succλ` IS NOT SPENT.  The level of an ordinal of the stage is
  -- already at the stage indexed by that ordinal itself, because the
  -- level IS one of its own definable subsets.  Successor closure buys
  -- nothing here, and the report says so.
  lset-in-stage : (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ Lset lam ⟩
                → ⟨ Lset δ ∈ˢ Lset lam ⟩
  lset-in-stage δ oδ δ∈ =
    Lset-in lam δ (Lset δ) (ord∈Lset→∈ lam ordλ δ oδ δ∈) (self∈𝒟ₒ δ)

  -- SEALED, AND THE SEAL IS THE SECOND MEASUREMENT OF LAW P-l IN THIS
  -- TASK.  `levelOf` is a PAIR whose second component is a proof built
  -- from `Lset-in`, `ord∈Lset→∈`, `𝒟ₒ-intro` and `defSet⊤≡A`.  Left
  -- transparent, ONE `subst` in part B that carried it -- the same
  -- `subst` that costs 4.46 s when the value slot is a plain variable --
  -- ran 229.22 s to 1,532,526,592 bytes and was killed
  -- (runs/pb-8.out).  Nothing about the term changed; only whether the
  -- elaborator could see inside the pair.  `levelOf-fst` is the read.
  opaque
    levelOf : (γ : HS.ASt.SL) → IsOrd (fst γ) → HS.ASt.SL
    levelOf γ oγ = Lset (fst γ) , lset-in-stage (fst γ) oγ (snd γ)

  opaque
    unfolding levelOf
    levelOf-fst : (γ : HS.ASt.SL) (oγ : IsOrd (fst γ))
                → fst (levelOf γ oγ) ≡ Lset (fst γ)
    levelOf-fst γ oγ = refl

  -- ===================================================================
  -- SECTION 3 (continued).  THE FORMULA AT THE HULL'S ALPHABET.
  --
  --   The core is parameter-free, so `embed` is the whole instantiation
  --   and it needs no code at all.  [LJ-1.651] went through a `slide`
  --   into `wit 0 ⊤̇ []` (Probe651.agda:125-129) because it carried the
  --   class alphabet to the end; erasing at the matrix removes that step
  --   and, with it, the only place this formula would have touched the
  --   hull's own constructors.
  -- ===================================================================

  -- COMPONENT ONE OF THREE, DELIVERED.  Two conjuncts: the level-hood
  -- Sigma-1 closure at the obligation's own slot order, and the
  -- ordinality of slot 1, which section 3B says the obligation forces.
  lv : Formula Code 2
  lv = levelFo (embed matrix₀) ∧̇ (embed ordAt1)

  -- ===================================================================
  -- SECTION 4.  WHAT THE OTHER TWO COMPONENTS STILL OWE, EXACTLY.
  --
  --   The assembly is free and section 2 pays the set half of
  --   completeness.  What is left is TWO SATISFACTION ROWS and nothing
  --   else: the truncation, the witness and the equation are all
  --   discharged here.
  -- ===================================================================

  StageSound : Type (ℓ-suc ℓ)
  StageSound = (v γ : HS.ASt.SL) → ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩
             → fst v ≡ Lset (fst γ)

  StageComplete : Type (ℓ-suc ℓ)
  StageComplete = (γ : HS.ASt.SL) (oγ : IsOrd (fst γ))
                → ⟨ (levelOf γ oγ ∷ γ ∷ []) ⊨c lv ⟩

  level-formula-from-rows : StageSound → StageComplete → LevelFormula
  level-formula-from-rows s c =
    lv , ( s
         , (λ γ oγ → ∣ levelOf γ oγ , (levelOf-fst γ oγ , c γ oγ) ∣₁) )

