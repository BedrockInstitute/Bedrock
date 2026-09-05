{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.574]  THE ASSIGNMENT AND ITS FORMULA, IN ONE TASK.
--
-- W3 IS agents/tasks/LJ-1-574/runs/W3.agda AND IT WAS WRITTEN FIRST
-- AND TYPECHECKED ALONE.  Three cold runs, exit 0, runs/w3-1.out to
-- w3-3.out.  Its finding is section 1 below and it is GO.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every reduction in it
-- is a measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552], [LJ-1.554], [LJ-1.557], [LJ-1.561] and
-- [LJ-1.568]).  Nothing lands in `src/`.
--
-- THE BRIEF'S OBLIGATION IS NOT INHABITED HERE, AND THE STOP IS
-- agents/tasks/LJ-1-574/review-of-succ-assignment-definable.md.  The
-- reason is one sentence of a predecessor that the brief's premises do
-- not carry: agents/tasks/LJ-1-552/review-of-succ-assignment.md:185-190
-- prices this obligation at THREE steps, and step 2, "the square law
-- INSIDE L", is "a chapter and not a task".  This brief funds step 1's
-- consequence and forbids the rows that would fund step 2.
--
-- WHAT IS DELIVERED INSTEAD IS NOT A HALF-TASK.  Section 5 inhabits
-- `[LJ-1.549]`'s `Residue` AT A STAGE: the assignment AND its formula,
-- in ONE term, with `κ` replaced by `LsetS β oβ` and NOTHING else
-- changed.  Section 6 writes the obligation's own type and the one
-- implication that separates the two.
--
--   Section 0.  D-10, BEFORE ANY OTHER AGDA, AND IT IS THE FORMULA
--               FIRST, as the brief orders.
--   Section 1.  W3.  `InjCode` IS the ⊨ of a formula, so [LJ-1.560]'s
--               reflection step applies to `leastOf`'s search.  GO.
--   Section 2.  THE LADDER, STARTED WHERE THE CALLER SAYS, and the
--               UNIFORM STAGE it buys: one stage holds a code for
--               EVERY member of δ.
--   Section 3.  THE SELECTION at that stage, and its injectivity.
--   Section 4.  THE DESCRIPTION, and its two readings.
--   Section 5.  `Residue δ (LsetS β oβ)`, INHABITED.
--   Section 6.  THE OBLIGATION'S TYPE, AND THE ONE STEP MISSING.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-574.runs.T6 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ¬̇_; ∀̇_; ∃̇_ )
open import FOL.Manipulation.Relativize using ( relativize )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; Lset-mono
        ; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( bound2; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL; SuccCardL )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in; injAt-out )
open import L.InjChain {ℓ} lem using ( appC; appC-adequate )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; isPropLeastOf )
open import L.Choice.Step {ℓ} lem using ( Mem; relOf; orderAt )
open import L.Choice.Order {ℓ} lem using ( relL; relL-fill; relL-rep )
open import L.Reflect {ℓ} lem
  using ( Below; Wit; Sat; SatEx; ClosedFor; LsetEnv; pickStage
        ; module Ladder; module Single )
open import L.ReflectFo {ℓ} lem using ( mkReflect )

open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.FinData using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫↪; isEmb⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.Foundations.Prelude using ( funExt )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax; ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- THE PREDECESSORS THIS FILE STANDS ON.  Each is GO, each probe is
-- green and carries no hole, so every type below is IMPORTED from the
-- file that typechecked and none is transcribed.
import LJ-1-549.Probe549 {ℓ} lem as P549
import LJ-1-554.Probe554 {ℓ} lem as P554
import LJ-1-557.Probe557 {ℓ} lem as P557
import LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sq as P561
import LJ-1-568.Probe568 {ℓ} lem α₀ oα₀ sq as P568


-- A path of the L-carrier is a path of its first component.
S-path : (u v : S) → fst u ≡ fst v → u ≡ v
S-path u v = Σ≡Prop (λ x → snd (isL x))

-- The L-element of a member of an L-set.
upS : (b : S) → ⟪ fst b ⟫ → S
upS b m = ⟪ fst b ⟫↪ m , isL-trans (member (fst b) m) (snd b)


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA, AND IT IS THE FORMULA
--             FIRST.
--
--   THE BRIEF ORDERS IT: "`[LJ-1.552]` measured that the set enters L
--   only through a generator and both generators take a formula.  So
--   write the formula before the function, and say at file:line what
--   it says."
--
--   `Def` (agents/tasks/LJ-1-568/Probe568.agda:189) IS a formula
--   already: it is `[LJ-1.554]`'s `LinkAt` at the assignment.  So the
--   question the D-10 has to answer is not "which formula" but "what
--   does the SELECTION look like as syntax", and the answer is section
--   4's `Fo`.  Section 1 is the step that makes such a formula
--   possible at all, and it is written first because if it fails
--   nothing else in this file can be stated.
-- ===================================================================


-- ===================================================================
-- SECTION 1.  W3.  `InjCode` IS THE ⊨ OF A FORMULA.
--
--   `leastOf`'s predicate at [LJ-1.557] is `Good`
--   (agents/tasks/LJ-1-557/Probe557.agda:204-205), which is `Code`
--   (Probe557.agda:82-83), which is `L.GCH.InjL` (src/L/GCH.lagda.md:38):
--   a truncated Σ over the WHOLE L-carrier.  [LJ-1.557] measured that
--   as "a quantifier over the whole L-carrier and not over a stage".
--
--   [LJ-1.560]'s reflection step bounds an unbounded existential OF A
--   FORMULA.  So "does it apply" is ONE question: is that quantifier
--   the ⊨ of a formula?  IT IS, and the two rows below are the proof.
--
--   THE ONLY CONJUNCT OF `InjCode` THE TREE DOES NOT ALREADY CARRY AS
--   SYNTAX IS THE FOURTH.  `L.Coding.Injection` has that sentence as a
--   formula, `ranAt` (src/L/Coding/Injection.lagda.md:230), but `ranAt`
--   is under the `private` at src/L/Coding/Injection.lagda.md:156 and
--   it states the range EXACTLY rather than as a subset.  `valFoAt` is
--   the one implication `InjCode` asks for, from the exported `appAt`.
-- ===================================================================

valFoAt : {n : ℕ} → Fin n → S → Formula S n
valFoAt f c = ∀̇ (∀̇ ( appAt (fsuc (fsuc f)) (fsuc fzero) fzero
                   ⇒̇ (var fzero ∈̇ con c) ))

valFoAt-adequate : {n : ℕ} (f : Fin n) (c : S) (γ : S ^ n)
  → ⟨ γ ⊨ valFoAt f c ⟩
  ≡ ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩ → ⟨ fst y ∈ fst c ⟩)
valFoAt-adequate f c γ i =
  (x y : S)
  → ⟨ appAt-adequate (fsuc (fsuc f)) (fsuc fzero) fzero (y ∷ x ∷ γ) i ⟩
  → ⟨ fst y ∈ fst c ⟩

-- `InjCode` AS A FORMULA, AT ANY TWO SLOTS AND A CONSTANT TARGET.  The
-- slots are free because section 4's description reads the same
-- condition twice, once at the value and once under a quantifier where
-- every index has shifted.
codeFoAt : {n : ℕ} → Fin n → Fin n → S → Formula S n
codeFoAt f d c = svAt f ∧̇ (domAt f d ∧̇ (injAt f ∧̇ valFoAt f c))

private
  domBoth : {n : ℕ} (f d : Fin n) (γ : S ^ n) (F a : S)
          → (F ≡ lookup f γ) → (a ≡ lookup d γ)
          → ⟨ (F ∷ a ∷ []) ⊨ domAt fzero (fsuc fzero) ⟩
          → (x : S)
          → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
             → ⟨ fst x ∈ fst (lookup d γ) ⟩)
          × (⟨ fst x ∈ fst (lookup d γ) ⟩
             → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩)
  domBoth f d γ F a ef ea dm x =
      PT.rec (snd (fst x ∈ fst (lookup d γ)))
        (λ { (y , p) → subst (λ t → ⟨ fst x ∈ fst t ⟩) ea
               (domAt-out fzero (fsuc fzero) (F ∷ a ∷ []) dm x y
                 (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)) })
    , (λ h → PT.map (λ { (y , p) →
               y , subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p })
        (domAt-in fzero (fsuc fzero) (F ∷ a ∷ []) dm x
          (subst (λ t → ⟨ fst x ∈ fst t ⟩) (sym ea) h)))

codeFoAt-in : {n : ℕ} (f d : Fin n) (c : S) (γ : S ^ n) (F a : S)
            → (F ≡ lookup f γ) → (a ≡ lookup d γ)
            → InjCode F a c → ⟨ γ ⊨ codeFoAt f d c ⟩
codeFoAt-in f d c γ F a ef ea (sv , dm , ij , vl) =
    svAt-in f γ (λ x y y' p q →
      svAt-out fzero (F ∷ a ∷ []) sv x y y'
        (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)
        (subst (λ t → ⟨ pr (fst x) (fst y') ∈ fst t ⟩) (sym ef) q))
  , ( domAt-intro f d γ (domBoth f d γ F a ef ea dm)
    , ( injAt-in f γ (λ y x x' p q →
          injAt-out fzero (F ∷ a ∷ []) ij y x x'
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)
            (subst (λ t → ⟨ pr (fst x') (fst y) ∈ fst t ⟩) (sym ef) q))
      , transport (sym (valFoAt-adequate f c γ))
          (λ x y p → vl x y
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)) ) )

codeFoAt-out : {n : ℕ} (f d : Fin n) (c : S) (γ : S ^ n) (F a : S)
             → (F ≡ lookup f γ) → (a ≡ lookup d γ)
             → ⟨ γ ⊨ codeFoAt f d c ⟩ → InjCode F a c
codeFoAt-out f d c γ F a ef ea (sv , (dm , (ij , vl))) =
    svAt-in fzero (F ∷ a ∷ []) (λ x y y' p q →
      svAt-out f γ sv x y y'
        (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)
        (subst (λ t → ⟨ pr (fst x) (fst y') ∈ fst t ⟩) ef q))
  , ( domAt-intro fzero (fsuc fzero) (F ∷ a ∷ []) dom₀
    , ( injAt-in fzero (F ∷ a ∷ []) (λ y x x' p q →
          injAt-out f γ ij y x x'
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)
            (subst (λ t → ⟨ pr (fst x') (fst y) ∈ fst t ⟩) ef q))
      , (λ x y p → transport (valFoAt-adequate f c γ) vl x y
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)) ) )
  where
  dom₀ : (x : S)
       → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩)
       × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩)
  dom₀ x =
      PT.rec (snd (fst x ∈ fst a))
        (λ { (y , p) → subst (λ t → ⟨ fst x ∈ fst t ⟩) (sym ea)
               (domAt-out f d γ dm x y
                 (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)) })
    , (λ h → PT.map (λ { (y , p) →
               y , subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p })
        (domAt-in f d γ dm x (subst (λ t → ⟨ fst x ∈ fst t ⟩) ea h)))

-- W3, THE ANSWER, IN ONE ROW EACH.  `InjL` IS the object language's own
-- unbounded existential, so both reflection steps the tree carries
-- apply to `leastOf`'s search with nothing paid to cross.
-- runs/W3.agda states the arity-3 form with the target a VARIABLE.
-- `codeFoAt` takes a constant, so the variable form is written out
-- once here; the search below spends the constant form, because κ is
-- fixed by the site.
valFoVar : Fin 3 → Fin 3 → Formula S 3
valFoVar f t = ∀̇ (∀̇ ( appAt (fsuc (fsuc f)) (fsuc fzero) fzero
                    ⇒̇ (var fzero ∈̇ var (fsuc (fsuc t))) ))

codeFoVar : Formula S 3
codeFoVar = svAt fzero
          ∧̇ ( domAt fzero (fsuc fzero)
            ∧̇ ( injAt fzero ∧̇ valFoVar fzero (fsuc (fsuc fzero)) ) )

-- The search this file actually bounds is at a CONSTANT target, since
-- κ is fixed by the site; both forms are the same formula shape and
-- the constant one is the one section 2 spends.
searchFo : S → Formula S 2
searchFo κ = codeFoAt fzero (fsuc fzero) κ

injL-is-search : (a κ : S) → InjL a κ → ⟨ (a ∷ []) ⊨ (∃̇ searchFo κ) ⟩
injL-is-search a κ = PT.map
  (λ { (F , h) → F , codeFoAt-in fzero (fsuc fzero) κ (F ∷ a ∷ []) F a
                       refl refl h })

search-is-injL : (a κ : S) → ⟨ (a ∷ []) ⊨ (∃̇ searchFo κ) ⟩ → InjL a κ
search-is-injL a κ = PT.map
  (λ { (F , h) → F , codeFoAt-out fzero (fsuc fzero) κ (F ∷ a ∷ []) F a
                       refl refl h })

-- AND [LJ-1.560]'s OWN OBLIGATION, RE-ASCRIBED AT IT.  Neither term is
-- written here: both are the library's, at this formula.
w3-single : (κ : S) (ρ : S ^ 1) → Below (Single.βω (searchFo κ)) ρ
          → (ρ ⊨ (∃̇ searchFo κ)) ≡ Wit (searchFo κ) ρ (Single.βω (searchFo κ))
w3-single κ = Single.reflect (searchFo κ)

w3-full : (κ : S) (μ : V ℓ) (oμ : IsOrd μ)
        → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
            ( ⟨ μ ∈ β ⟩
            × ((γ : S ^ 1) → Below β γ
               → (γ ⊨ (∃̇ searchFo κ))
               ≡ (γ ⊨ relativize (LsetS β oβ) (∃̇ searchFo κ))) )
w3-full κ = mkReflect (∃̇ searchFo κ)


-- ===================================================================
-- SECTION 2.  THE LADDER, STARTED WHERE THE CALLER SAYS.
--
--   `Single` starts its ladder at ∅ (src/L/Reflect.lagda.md:479), so
--   `βω` is fixed by the matrix alone and cannot hold a caller's δ.
--   `mkReflect` takes a caller's ordinal but RELATIVIZES the matrix.
--   Neither is what this site wants: it wants the caller's δ inside the
--   stage AND the matrix untouched, because the witness has to come
--   back out as an `InjCode` and not as a relativized one.
--
--   `Ladder` is generic and `Single`'s step is public, so the same
--   ladder started at σ₀ costs six lines.  NOTHING NEW IS PROVED: the
--   closure argument is `Ladder.closure`, unchanged.
-- ===================================================================

module Start {k : ℕ} (ψ : Formula S (suc k)) (σ₀ : V ℓ) (oσ₀ : IsOrd σ₀) where

  private
    module Sg = Single ψ

  γₙ : ℕ → V ℓ
  γₙ-ord : (n : ℕ) → IsOrd (γₙ n)
  γₙ zero        = σ₀
  γₙ (suc n)     = Sg.Fstep (γₙ n) (γₙ-ord n)
  γₙ-ord zero    = oσ₀
  γₙ-ord (suc n) = Sg.Fstep-ord (γₙ n) (γₙ-ord n)

  γₙ-step : (n : ℕ) → ⟨ γₙ n ∈ γₙ (suc n) ⟩
  γₙ-step n = Sg.σ∈Fstep (γₙ n) (γₙ-ord n)

  module Lad = Ladder γₙ γₙ-ord γₙ-step

  top : V ℓ
  top = Lad.top

  top-ord : IsOrd top
  top-ord = Lad.top-ord

  σ₀∈top : ⟨ σ₀ ∈ top ⟩
  σ₀∈top = Lad.G∈top 0

  answers : (n : ℕ) (ms : ⟪ Lset (γₙ n) ⟫ ^ k)
          → ⟨ pickStage ψ (LsetEnv (γₙ n) (γₙ-ord n) ms) ∈ γₙ (suc n) ⟩
  answers n = Sg.pickLand (γₙ n) (γₙ-ord n)

  closed : ClosedFor top ψ
  closed = Lad.closure ψ answers

  reflect : (ρ : S ^ k) → Below top ρ → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ top
  reflect = Lad.reflect ψ answers


-- A stage holding two given L-elements.
two-in-a-stage : (u v : S)
  → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ fst u ∈ Lset σ ⟩ × ⟨ fst v ∈ Lset σ ⟩) ∥₁
two-in-a-stage u v = PT.rec squash₁
  (λ { (α , (oα , u∈)) → PT.map
    (λ { (β , (oβ , v∈)) →
        bound2 α β oα oβ .fst
      , ( bound2 α β oα oβ .snd .fst
        , ( Lset-mono {α = bound2 α β oα oβ .fst} {β = α}
              (bound2 α β oα oβ .snd .snd .fst) u∈
          , Lset-mono {α = bound2 α β oα oβ .fst} {β = β}
              (bound2 α β oα oβ .snd .snd .snd) v∈ ) ) })
    (snd v) })
  (snd u)

-- THE UNIFORM STAGE.  This is what [LJ-1.557] said its pointwise code
-- could not reach, and it is reached by section 1 and nothing else.
codes-at-one-stage : (δ κ : S) → SuccCardL δ κ
  → ∥ Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
        ( ⟨ fst δ ∈ Lset β ⟩
        × ⟨ fst κ ∈ Lset β ⟩
        × ((a : S) → ⟨ fst a ∈ fst δ ⟩
           → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁) ) ∥₁
codes-at-one-stage δ κ sc = PT.map go (two-in-a-stage δ κ)
  where
  go : Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ fst δ ∈ Lset σ ⟩ × ⟨ fst κ ∈ Lset σ ⟩)
     → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
         ( ⟨ fst δ ∈ Lset β ⟩
         × ⟨ fst κ ∈ Lset β ⟩
         × ((a : S) → ⟨ fst a ∈ fst δ ⟩
            → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁) )
  go (σ , (oσ , (δ∈ , κ∈))) = St.top , (St.top-ord , (δ∈β , (κ∈β , codes)))
    where
    module St = Start (searchFo κ) σ oσ

    δ∈β : ⟨ fst δ ∈ Lset St.top ⟩
    δ∈β = Lset-mono {α = St.top} {β = σ} St.σ₀∈top δ∈

    κ∈β : ⟨ fst κ ∈ Lset St.top ⟩
    κ∈β = Lset-mono {α = St.top} {β = σ} St.σ₀∈top κ∈

    codes : (a : S) → ⟨ fst a ∈ fst δ ⟩
          → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset St.top ⟩ × InjCode F a κ) ∥₁
    codes a a∈δ = PT.map unpack (St.closed (a ∷ []) below sat)
      where
      a∈β : ⟨ fst a ∈ Lset St.top ⟩
      a∈β = layer-trans (Lset-layer St.top) {x = fst δ} {y = fst a} a∈δ δ∈β

      below : Below St.top (a ∷ [])
      below = a∈β , tt*

      sat : ⟨ SatEx (searchFo κ) (a ∷ []) ⟩
      sat = PT.map (λ { (F , h) → F ,
              codeFoAt-in fzero (fsuc fzero) κ (F ∷ a ∷ []) F a refl refl h })
              (P557.member-code-into-kappa δ κ sc a a∈δ)

      unpack : Σ[ q ∈ S ]
                 (⟨ fst q ∈ Lset St.top ⟩ × ⟨ Sat (searchFo κ) (a ∷ []) q ⟩)
             → Σ[ F ∈ S ] (⟨ fst F ∈ Lset St.top ⟩ × InjCode F a κ)
      unpack (q , (q∈ , s)) = q , (q∈ ,
        codeFoAt-out fzero (fsuc fzero) κ (q ∷ a ∷ []) q a refl refl s)


-- ===================================================================
-- SECTION 3.  THE SELECTION AT THAT STAGE.
--
--   `leastOf` now runs over `Mem (Lset β)`, a SET, and no longer over
--   the whole L-carrier.  That is the whole gain of section 2.
-- ===================================================================

module Select (δ κ : S)
              (β : V ℓ) (oβ : IsOrd β)
              (codes : (a : S) → ⟨ fst a ∈ fst δ ⟩
                     → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁)
              where

  upM : Mem (Lset β) → S
  upM m = fst m , Lset→isL β oβ (fst m) (snd m)

  memD : ⟪ fst δ ⟫ → S
  memD = upS δ

  -- THE PREDICATE.  Truncated, because `InjCode` is a Σ and the search
  -- takes an hProp.  Nothing is lost: the conclusion is truncated too.
  Good : ⟪ fst δ ⟫ → Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good k F = ∥ InjCode (upM F) (memD k) κ ∥₁ , squash₁

  nonempty : (k : ⟪ fst δ ⟫) → ∥ Σ[ F ∈ Mem (Lset β) ] ⟨ Good k F ⟩ ∥₁
  nonempty k = PT.map
    (λ { (F , (F∈β , code)) →
         (fst F , F∈β)
       , ∣ subst (λ u → InjCode u (memD k) κ) (S-path F (upM (fst F , F∈β)) refl)
             code ∣₁ })
    (codes (memD k) (member (fst δ) k))

  least : (k : ⟪ fst δ ⟫)
        → Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) (Good k) F
  least k = leastOf (orderAt β oβ) lem (Good k) (nonempty k)

  gm : ⟪ fst δ ⟫ → Mem (Lset β)
  gm k = fst (least k)

  s : ⟪ fst δ ⟫ → S
  s k = upM (gm k)

  s-good : (k : ⟪ fst δ ⟫) → ∥ InjCode (s k) (memD k) κ ∥₁
  s-good k = fst (snd (least k))

  s-min : (k : ⟪ fst δ ⟫) (F : Mem (Lset β)) → ⟨ Good k F ⟩
        → relOf (orderAt β oβ) F (gm k) → Empty.⊥
  s-min k = snd (snd (least k))

  s-in-stage : (k : ⟪ fst δ ⟫) → ⟨ fst (s k) ∈ Lset β ⟩
  s-in-stage k = snd (gm k)

  -- The same, in the stage's own presentation.
  g : ⟪ fst δ ⟫ → ⟪ fst (LsetS β oβ) ⟫
  g k = P549.ixOf (LsetS β oβ) (s k) (s-in-stage k)

  g-val : (k : ⟪ fst δ ⟫) → ⟪ fst (LsetS β oβ) ⟫↪ (g k) ≡ fst (s k)
  g-val k = P549.ixOf-val (LsetS β oβ) (s k) (s-in-stage k)

  -- INJECTIVITY, AND IT IS FREE.  A code determines its DOMAIN, by
  -- `domAt` read in both directions (src/L/Coding/Model.lagda.md:289,
  -- :294), and the domain of the code at `k` is the k-th member of δ.
  -- So two members of δ carrying the same code have the same members,
  -- hence are equal by extensionality, hence have the same index.
  private
    dom-eq : (k k' : ⟪ fst δ ⟫) → s k ≡ s k'
           → InjCode (s k) (memD k) κ → InjCode (s k') (memD k') κ
           → fst (memD k) ≡ fst (memD k')
    dom-eq k k' e ck ck' =
      extensionalV {a = fst (memD k)} {b = fst (memD k')}
        (λ z → ⇔toPath (fwd z) (bwd z))
      where
      Fk = s k
      dmk = fst (snd ck)
      dmk' = fst (snd ck')

      toS : (z : V ℓ) (u : S) → ⟨ z ∈ fst u ⟩ → S
      toS z u h = z , isL-trans {x = fst u} {y = z} h (snd u)

      fwd : (z : V ℓ) → ⟨ z ∈ fst (memD k) ⟩ → ⟨ z ∈ fst (memD k') ⟩
      fwd z hz = PT.rec (snd (z ∈ fst (memD k')))
        (λ { (y , p) → domAt-out fzero (fsuc fzero) (s k' ∷ memD k' ∷ []) dmk'
                         (toS z (memD k) hz) y
                         (subst (λ t → ⟨ pr z (fst y) ∈ fst t ⟩) e p) })
        (domAt-in fzero (fsuc fzero) (Fk ∷ memD k ∷ []) dmk
           (toS z (memD k) hz) hz)

      bwd : (z : V ℓ) → ⟨ z ∈ fst (memD k') ⟩ → ⟨ z ∈ fst (memD k) ⟩
      bwd z hz = PT.rec (snd (z ∈ fst (memD k)))
        (λ { (y , p) → domAt-out fzero (fsuc fzero) (Fk ∷ memD k ∷ []) dmk
                         (toS z (memD k') hz) y
                         (subst (λ t → ⟨ pr z (fst y) ∈ fst t ⟩) (sym e) p) })
        (domAt-in fzero (fsuc fzero) (s k' ∷ memD k' ∷ []) dmk'
           (toS z (memD k') hz) hz)

  isSet⟪δ⟫ : isSet ⟪ fst δ ⟫
  isSet⟪δ⟫ = Embedding-into-isSet→isSet
               (⟪ fst δ ⟫↪ , isEmb⟪ fst δ ⟫↪) setIsSet

  sinj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k'
  sinj k k' e = PT.rec (isSet⟪δ⟫ k k')
    (λ ck → PT.rec (isSet⟪δ⟫ k k') (λ ck' → step ck ck') (s-good k'))
    (s-good k)
    where
    step : InjCode (s k) (memD k) κ → InjCode (s k') (memD k') κ → k ≡ k'
    step ck ck' =
      ↪-inj {a = fst δ} (dom-eq k k' (S-path (s k) (s k') e) ck ck')

  ginj : (k k' : ⟪ fst δ ⟫) → g k ≡ g k' → k ≡ k'
  ginj k k' e = sinj k k' (sym (g-val k) ∙ cong (⟪ fst (LsetS β oβ) ⟫↪) e
                          ∙ g-val k')

  -- And the values are subsets of the stage, because a stage is
  -- transitive (src/L/Constructible.lagda.md:183).
  s-sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ LsetS β oβ ⟩
  s-sub k x hx = layer-trans (Lset-layer β) {x = fst (s k)} {y = fst x}
                   hx (s-in-stage k)


-- ===================================================================
-- SECTION 4.  THE DESCRIPTION, AND ITS TWO READINGS.
--
--   THE SHAPE IS `L.Choice.Transversal.Pick`
--   (src/L/Choice/Transversal.lagda.md:116-123) AND NOT A NEW IDEA: a
--   member of the stage, a condition on it, and nothing before it in
--   the stage's own order, with that order pinned as a CONSTANT
--   because `L.Choice.Order` delivers it as an ELEMENT OF THE MODEL
--   (src/L/Choice/Order.lagda.md:693).  Only the condition is new, and
--   section 1 is what makes the condition sayable.
-- ===================================================================

module Link (δ κ : S) (β : V ℓ) (oβ : IsOrd β)
            (codes : (a : S) → ⟨ fst a ∈ fst δ ⟩
                   → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁)
            where

  module Sel = Select δ κ β oβ codes

  βisL : ⟨ isL β ⟩
  βisL = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

  c : S
  c = LsetS β oβ

  r : S
  r = relL β βisL oβ

  w : SWO (Mem (Lset β))
  w = orderAt β oβ

  -- THE DESCRIPTION.  Environment (y ∷ x ∷ z ∷ []); `z` is `LinkAt`'s
  -- third slot and no conjunct reads it.
  Fo : Formula S 3
  Fo = (var fzero ∈̇ con c)
     ∧̇ ( codeFoAt fzero (fsuc fzero) κ
       ∧̇ (¬̇ ∃̇ ( (var fzero ∈̇ con c)
               ∧̇ ( codeFoAt fzero (fsuc (fsuc fzero)) κ
                 ∧̇ appC r fzero (fsuc fzero) ) )) )

  private
    memOf : (y : S) → ⟨ fst y ∈ Lset β ⟩ → Mem (Lset β)
    memOf y h = fst y , h

    upEq : (y : S) (h : ⟨ fst y ∈ Lset β ⟩) → Sel.upM (memOf y h) ≡ y
    upEq y h = S-path (Sel.upM (memOf y h)) y refl

  -- READING ONE.  The selected value satisfies the description.
  lin : (x y z : S) (m : ⟨ fst x ∈ fst δ ⟩)
      → fst y ≡ fst (Sel.s (P549.ixOf δ x m))
      → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Fo ⟩
  lin x y z m e = c1 , (c2 , c3)
    where
    k : ⟪ fst δ ⟫
    k = P549.ixOf δ x m

    xk : x ≡ Sel.memD k
    xk = S-path x (Sel.memD k) (sym (P549.ixOf-val δ x m))

    yk : y ≡ Sel.s k
    yk = S-path y (Sel.s k) e

    c1 : ⟨ fst y ∈ Lset β ⟩
    c1 = subst (λ t → ⟨ t ∈ Lset β ⟩) (sym e) (Sel.s-in-stage k)

    c2 : ⟨ (y ∷ x ∷ z ∷ []) ⊨ codeFoAt fzero (fsuc fzero) κ ⟩
    c2 = PT.rec (snd ((y ∷ x ∷ z ∷ []) ⊨ codeFoAt fzero (fsuc fzero) κ))
           (λ code → codeFoAt-in fzero (fsuc fzero) κ (y ∷ x ∷ z ∷ []) y x
                       refl refl
                       (subst (λ u → InjCode u x κ) (sym yk)
                         (subst (λ v → InjCode (Sel.s k) v κ) (sym xk) code)))
           (Sel.s-good k)

    c3 : ⟨ (y ∷ x ∷ z ∷ []) ⊨
            (¬̇ ∃̇ ( (var fzero ∈̇ con c)
                  ∧̇ ( codeFoAt fzero (fsuc (fsuc fzero)) κ
                    ∧̇ appC r fzero (fsuc fzero) ) )) ⟩
    c3 = PT.rec Empty.isProp⊥ bad
      where
      bad : Σ[ y' ∈ S ]
              ( ⟨ fst y' ∈ Lset β ⟩
              × ( ⟨ (y' ∷ y ∷ x ∷ z ∷ []) ⊨ codeFoAt fzero (fsuc (fsuc fzero)) κ ⟩
                × ⟨ (y' ∷ y ∷ x ∷ z ∷ []) ⊨ appC r fzero (fsuc fzero) ⟩ ) )
          → Empty.⊥
      bad (y' , (y'∈ , (cod , rel))) = Sel.s-min k F' good below
        where
        F' : Mem (Lset β)
        F' = memOf y' y'∈

        good : ⟨ Sel.Good k F' ⟩
        good = ∣ subst (λ u → InjCode u (Sel.memD k) κ) (sym (upEq y' y'∈))
                 (subst (λ v → InjCode y' v κ) xk
                   (codeFoAt-out fzero (fsuc (fsuc fzero)) κ
                     (y' ∷ y ∷ x ∷ z ∷ []) y' x refl refl cod)) ∣₁

        below : relOf w F' (Sel.gm k)
        below = relL-rep β βisL oβ F' (Sel.gm k)
          (subst (λ t → ⟨ pr (fst y') t ∈ fst r ⟩) e
            (subst ⟨_⟩ (appC-adequate r fzero (fsuc fzero)
                         (y' ∷ y ∷ x ∷ z ∷ [])) rel))

  -- READING TWO.  Only the selected value satisfies it.  Leastness in
  -- a well-order is unique by trichotomy alone: `isPropLeastOf`
  -- (src/L/WellOrder/Base.lagda.md:136).
  lout : (x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Fo ⟩
       → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (Sel.s (P549.ixOf δ x m))
  lout x y z (c1 , (c2 , c3)) m =
    cong fst (cong fst (isPropLeastOf w (Sel.Good k) (Fy , leastFy)
                                        (Sel.gm k , snd (Sel.least k))))
    where
    k : ⟪ fst δ ⟫
    k = P549.ixOf δ x m

    xk : x ≡ Sel.memD k
    xk = S-path x (Sel.memD k) (sym (P549.ixOf-val δ x m))

    Fy : Mem (Lset β)
    Fy = memOf y c1

    codeY : InjCode y x κ
    codeY = codeFoAt-out fzero (fsuc fzero) κ (y ∷ x ∷ z ∷ []) y x refl refl c2

    goodY : ⟨ Sel.Good k Fy ⟩
    goodY = ∣ subst (λ u → InjCode u (Sel.memD k) κ) (sym (upEq y c1))
              (subst (λ v → InjCode y v κ) xk codeY) ∣₁

    minY : (b : Mem (Lset β)) → ⟨ Sel.Good k b ⟩ → relOf w b Fy → Empty.⊥
    minY b gb rb = c3 ∣ Sel.upM b , (snd b , (codB , relB)) ∣₁
      where
      codB : ⟨ (Sel.upM b ∷ y ∷ x ∷ z ∷ [])
                 ⊨ codeFoAt fzero (fsuc (fsuc fzero)) κ ⟩
      codB = PT.rec (snd ((Sel.upM b ∷ y ∷ x ∷ z ∷ [])
                            ⊨ codeFoAt fzero (fsuc (fsuc fzero)) κ))
        (λ code → codeFoAt-in fzero (fsuc (fsuc fzero)) κ
                    (Sel.upM b ∷ y ∷ x ∷ z ∷ []) (Sel.upM b) x refl refl
                    (subst (λ v → InjCode (Sel.upM b) v κ) (sym xk) code))
        gb

      relB : ⟨ (Sel.upM b ∷ y ∷ x ∷ z ∷ []) ⊨ appC r fzero (fsuc fzero) ⟩
      relB = subst ⟨_⟩ (sym (appC-adequate r fzero (fsuc fzero)
                              (Sel.upM b ∷ y ∷ x ∷ z ∷ [])))
               (relL-fill β βisL oβ b Fy rb)

    leastFy : IsLeast w (Sel.Good k) Fy
    leastFy = goodY , minY

  -- AND THE LINK, IN [LJ-1.554]'s OWN TYPE.
  link : P554.LinkAt δ Sel.s
  link = Fo , (lin , lout)


-- ===================================================================
-- SECTION 5.  `Residue` AT THE STAGE, INHABITED.
--
--   `[LJ-1.549]`'s `Residue δ b` (agents/tasks/LJ-1-549/Probe549.agda:
--   668-679) is the assignment AND its formula in ONE type.  The row
--   below inhabits it at `b := LsetS β oβ`.  THIS IS NOT HALF THE
--   TASK: both halves are here and they are in one term.  What is not
--   here is `b := κ`.
-- ===================================================================

residue-at-stage : (δ κ : S) → SuccCardL δ κ
  → ∥ Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ] P549.Residue δ (LsetS β oβ) ∥₁
residue-at-stage δ κ sc = PT.map go (codes-at-one-stage δ κ sc)
  where
  go : Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
         ( ⟨ fst δ ∈ Lset β ⟩
         × ⟨ fst κ ∈ Lset β ⟩
         × ((a : S) → ⟨ fst a ∈ fst δ ⟩
            → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁) )
     → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ] P549.Residue δ (LsetS β oβ)
  go (β , (oβ , (_ , (_ , codes)))) =
    β , (oβ , (Lk.Sel.s , (Lk.Sel.s-sub , (Lk.Sel.sinj , Lk.link))))
    where
    module Lk = Link δ κ β oβ codes

-- THE SAME, IN THE BRIEF'S OWN SHAPE, with `[LJ-1.568]`'s `Def`
-- (agents/tasks/LJ-1-568/Probe568.agda:189) and `powL κ` replaced by
-- the stage.  Every other symbol is the brief's.
stage-assignment-definable : (δ κ : S) → SuccCardL δ κ
  → ∥ Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
       Σ[ g ∈ (⟪ fst δ ⟫ → ⟪ fst (LsetS β oβ) ⟫) ]
         ( ((k k' : ⟪ fst δ ⟫) → g k ≡ g k' → k ≡ k')
         × P568.Def δ (LsetS β oβ) g ) ∥₁
stage-assignment-definable δ κ sc = PT.map go (codes-at-one-stage δ κ sc)
  where
  go : Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
         ( ⟨ fst δ ∈ Lset β ⟩
         × ⟨ fst κ ∈ Lset β ⟩
         × ((a : S) → ⟨ fst a ∈ fst δ ⟩
            → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁) )
     → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
         Σ[ g ∈ (⟪ fst δ ⟫ → ⟪ fst (LsetS β oβ) ⟫) ]
           ( ((k k' : ⟪ fst δ ⟫) → g k ≡ g k' → k ≡ k')
           × P568.Def δ (LsetS β oβ) g )
  go (β , (oβ , (_ , (_ , codes)))) =
    β , (oβ , (Lk.Sel.g , (Lk.Sel.ginj , def)))
    where
    module Lk = Link δ κ β oβ codes

    valEq : Lk.Sel.s ≡ (λ k → P561.up (LsetS β oβ) (Lk.Sel.g k))
    valEq = funExt (λ k → S-path (Lk.Sel.s k)
                            (P561.up (LsetS β oβ) (Lk.Sel.g k))
                            (sym (Lk.Sel.g-val k)))

    def : P568.Def δ (LsetS β oβ) Lk.Sel.g
    def = subst (P554.LinkAt δ) valEq Lk.link


