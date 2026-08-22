{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.561]  ARE THE FIVE WALLS ONE WALL?
--
-- W3 IS runs/W3.agda AND IT WAS WRITTEN FIRST AND TYPECHECKED ALONE.
-- Three cold runs, exit 0, runs/w3-1.out to w3-3.out, 1.73 s.  Its one
-- finding is the FRAME: the five statements DO sit in one file, and the
-- price is that the file takes `L.StageCardinal`'s three parameters,
-- which four of the five statements never mention.
--
-- THE OBLIGATION IS INHABITED.  `one-wall` is section 6.
-- This file carries NO hole and NO postulate, so every reduction in it
-- is a measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552], [LJ-1.554] and [LJ-1.557]).  Nothing lands
-- in src/.
--
-- THE ANSWER IN ONE LINE.  THE FIVE ARE THREE PLUS TWO.  One statement
-- `W` covers B9, B7 and `Link`, and it covers them from BOTH legs.  It
-- does NOT cover the assignment and it does NOT cover `StageHigh`, and
-- section 5 measures why in each case rather than reporting a failed
-- search.
--
--   Section 0.  THE FIVE, AND THE TWO REDUCTIONS THAT MAKE THREE OF
--               THEM ONE.
--   Section 1.  `W`, STATED, AND WHAT IT IS THE CONVERSE OF.
--   Section 2.  `W` BUYS A CODE.  This is B9 and B7 together.
--   Section 3.  `W` BUYS `Link`.  This is the GCH leg.
--   Section 4.  THE TWO SITE INSTANCES, at their own hypotheses.
--   Section 5.  THE TWO `W` DOES NOT REACH, MEASURED.
--   Section 6.  THE OBLIGATION.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-561.Probe561 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Cardinal {ℓ} lem using ( InjCode; _↪_ )
open import L.GCH {ℓ} lem using ( InjL; SuccCardL )
open import L.Coding.Model {ℓ}
  using ( svAt; svAt-in; domAt; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
import L.StageCardinal
import L.CantorBernstein

open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open InfinitySet {ℓ} using ( sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The delivered chapters, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
module CB = L.CantorBernstein {ℓ} lem

-- THE FOUR PREDECESSORS THAT ARE GREEN AND CARRY NO HOLE.  Their types
-- are IMPORTED and not transcribed, so nothing below can have drifted
-- from the file that typechecked.
import LJ-1-549.Probe549
import LJ-1-552.Probe552
import LJ-1-554.Probe554
import LJ-1-557.Probe557
module P549 = LJ-1-549.Probe549 {ℓ} lem
module P552 = LJ-1-552.Probe552 {ℓ} lem
module P554 = LJ-1-554.Probe554 {ℓ} lem
module P557 = LJ-1-557.Probe557 {ℓ} lem

-- [LJ-1.536] defines this in three lines and does not export it from
-- src/; re-typed rather than imported, because importing Probe536 costs
-- its whole adjunction and this file needs one line of it.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

-- The L-element of a member of an L-set.  One line, from transitivity.
up : (b : S) → ⟪ fst b ⟫ → S
up b m = ⟪ fst b ⟫↪ m , isL-trans (member (fst b) m) (snd b)


-- ===================================================================
-- SECTION 0.  THE FIVE, AND THE TWO REDUCTIONS THAT MAKE THREE OF THEM
--             ONE.
--
--   D-10 ORDERED THIS BEFORE ANY OTHER AGDA: what carrier and what
--   arity does each missing piece live at?  runs/W3.agda answers it by
--   writing all five down together.  The two rows below are the part
--   that is NOT a restatement: they are the identifications that make
--   B9, B7 and `Link` instances of ONE statement.
-- ===================================================================

-- 0.1  THE ASSIGNMENT TYPE, [LJ-1.552]'s, IMPORTED.
Assignment : (δ κ : S) → Type (ℓ-suc ℓ)
Assignment = P552.Assignment

-- 0.2  `powL`, [LJ-1.549]'s, IMPORTED.  It is the model's own power
--      set and carries no `zf` (agents/tasks/LJ-1-549/Probe549.agda:121-136).
powL : S → S
powL = P549.powL


-- ===================================================================
-- SECTION 1.  `W`, STATED.
--
--   IT NAMES NO FORMULA, NO LEVY GRADE AND NO STAGE.  Its hypothesis
--   is an ambient injection between the members of two sets of L; its
--   conclusion is that the GRAPH of that injection is a set of L.
-- ===================================================================

GraphIn : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) (G : S) → Type (ℓ-suc ℓ)
GraphIn a b g G =
  (k : ⟪ fst a ⟫) → ⟨ pr (⟪ fst a ⟫↪ k) (⟪ fst b ⟫↪ (g k)) ∈ fst G ⟩

GraphOut : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) (G : S) → Type (ℓ-suc ℓ)
GraphOut a b g G =
  (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
    → ∥ Σ[ k ∈ ⟪ fst a ⟫ ]
          ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k))) ∥₁

IsGraph : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) (G : S) → Type (ℓ-suc ℓ)
IsGraph a b g G = GraphIn a b g G × GraphOut a b g G

W : Type (ℓ-suc ℓ)
W = (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
  → ((k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
  → ∥ Σ[ G ∈ S ] IsGraph a b g G ∥₁

-- 1.1  `W` IS EXACTLY [LJ-1.554]'s OWN MISSING INPUT, AND NOT A
--      NEIGHBOUR OF IT.  That task measured that the graph is ALREADY
--      an ambient set with no hypothesis, and that "what is missing is
--      `isL` of this set" (agents/tasks/LJ-1-554/Probe554.agda:150-170).
--      `grV` is ITS set, imported; `isL` of it gives `W`'s conclusion
--      with nothing else added.
ambient-graph-isL :
    (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
  → ⟨ isL (P554.grV a (λ k → up b (g k))) ⟩
  → Σ[ G ∈ S ] IsGraph a b g G
ambient-graph-isL a b g h = (Gr , h) , (gin , gout)
  where
  s : ⟪ fst a ⟫ → S
  s k = up b (g k)
  Gr : V ℓ
  Gr = P554.grV a s
  gin : GraphIn a b g (Gr , h)
  gin k = P554.grV-in a s k
  gout : GraphOut a b g (Gr , h)
  gout x y p = PT.map go (P554.grV-out a s (pr (fst x) (fst y)) p)
    where
    go : Σ[ k ∈ ⟪ fst a ⟫ ] (pr (⟪ fst a ⟫↪ k) (fst (s k)) ≡ pr (fst x) (fst y))
       → Σ[ k ∈ ⟪ fst a ⟫ ]
            ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k)))
    go (k , e) = k , (sym (pr-inj e .fst) , sym (pr-inj e .snd))

-- 1.2  AND THE CEILING, MEASURED.  `V = L` gives `W` outright.  So `W`
--      is not `Empty`, and the obligation below is not vacuous; and
--      `W` is at most as strong as `V = L`.  THE CONVERSE IS NOT
--      MEASURED HERE and this file does not claim it.
vl→w : ((x : V ℓ) → ⟨ isL x ⟩) → W
vl→w vl a b g _ = ∣ ambient-graph-isL a b g (vl _) ∣₁

-- 1.3  `W` IS THE CONVERSE OF A DELIVERED TERM, AND THIS IS THAT TERM.
--      `readL` (src/L/CantorBernstein.lagda.md:33-38) turns a code into
--      an ambient injection.  Nothing in the tree goes the other way.
delivered-converse : (a b : S) → InjL a b → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
delivered-converse a b = PT.map (CB.readL a b)


-- ===================================================================
-- SECTION 2.  `W` BUYS A CODE.
--
--   This is B9 ([LJ-1.533]) and B7 ([LJ-1.535]) TOGETHER, and their
--   being together is the finding: both stopped for "a code out of a
--   bare Σ", and `_↪_` IS that bare Σ (src/L/Cardinal.lagda.md:47-48).
--
--   NOTHING HERE IS NEW MATHEMATICS.  The four conjuncts of `InjCode`
--   are read off the graph by the tree's own adequacy lemmas:
--   `svAt-in` and `domAt-intro` (src/L/Coding/Model.lagda.md:238,:298)
--   and `injAt-in` (src/L/Coding/Injection.lagda.md:72).
-- ===================================================================

module Code (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
            (ginj : (k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
            (G : S) (gin : GraphIn a b g G)
            (gout : GraphOut a b g G) where

  private
    γ : S ^ 2
    γ = G ∷ a ∷ []

  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ h
    where
    h : (x y y' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
      → ⟨ pr (fst x) (fst y') ∈ fst G ⟩ → fst y ≡ fst y'
    h x y y' p q = PT.rec2 (setIsSet (fst y) (fst y')) go (gout x y p) (gout x y' q)
      where
      go : Σ[ k ∈ ⟪ fst a ⟫ ] ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k)))
         → Σ[ k ∈ ⟪ fst a ⟫ ] ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y' ≡ ⟪ fst b ⟫↪ (g k)))
         → fst y ≡ fst y'
      go (k , (ex , ey)) (k' , (ex' , ey')) =
        ey ∙ cong (λ w → ⟪ fst b ⟫↪ (g w)) (↪-inj {a = fst a} (sym ex ∙ ex'))
           ∙ sym ey'

  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ h
    where
    into : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
         → ⟨ fst x ∈ fst a ⟩
    into x = PT.rec (snd (fst x ∈ fst a)) λ { (y , p) →
      PT.rec (snd (fst x ∈ fst a))
        (λ { (k , (ex , _)) →
             subst (λ v → ⟨ v ∈ fst a ⟩) (sym ex) (member (fst a) k) })
        (gout x y p) }
    from : (x : S) → ⟨ fst x ∈ fst a ⟩
         → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    from x m = ∣ up b (g k) , subst (λ v → ⟨ pr v (⟪ fst b ⟫↪ (g k)) ∈ fst G ⟩)
                                (fiber (fst a) m .snd) (gin k) ∣₁
      where
      k : ⟪ fst a ⟫
      k = fiber (fst a) m .fst
    h : (x : S)
      → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩ → ⟨ fst x ∈ fst a ⟩)
      × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩)
    h x = into x , from x

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ h
    where
    h : (y x x' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
      → ⟨ pr (fst x') (fst y) ∈ fst G ⟩ → fst x ≡ fst x'
    h y x x' p q = PT.rec2 (setIsSet (fst x) (fst x')) go (gout x y p) (gout x' y q)
      where
      go : Σ[ k ∈ ⟪ fst a ⟫ ] ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k)))
         → Σ[ k ∈ ⟪ fst a ⟫ ] ((fst x' ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k)))
         → fst x ≡ fst x'
      go (k , (ex , ey)) (k' , (ex' , ey')) =
        ex ∙ cong (⟪ fst a ⟫↪) (ginj k k' (↪-inj {a = fst b} (sym ey ∙ ey')))
           ∙ sym ex'

  vals : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst b ⟩
  vals x y p = PT.rec (snd (fst y ∈ fst b))
    (λ { (k , (_ , ey)) →
         subst (λ v → ⟨ v ∈ fst b ⟩) (sym ey) (member (fst b) (g k)) })
    (gout x y p)

  code : InjCode G a b
  code = sv , (dm , (ij , vals))

-- THE IMPLICATION, AND IT IS B7 VERBATIM: "a code out of a bare Σ".
w→code : W → (a b : S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ → InjL a b
w→code w a b (g , ginj) =
  PT.map (λ { (G , (gin , gout)) → G , Code.code a b g ginj G gin gout })
         (w a b g ginj)


-- ===================================================================
-- SECTION 3.  `W` BUYS `Link`, AND THIS IS THE OTHER LEG.
--
--   [LJ-1.554] measured that `Link` and the CODED GRAPH are the same
--   request (agents/tasks/LJ-1-554/Probe554.agda:198-265), and that
--   what is missing is `isL` of one ambient set that already exists
--   (:160-170).  `W` supplies exactly that `isL`, at
--   `b := powL κ`, and the conversion needs no size condition.
-- ===================================================================

module Link (δ κ : S) (s : ⟪ fst δ ⟫ → S)
            (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
            (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
            where

  -- THE ASSIGNMENT IS AN AMBIENT INJECTION INTO `powL κ`, WITH NO
  -- CHOICE.  `ixOf` is a FIBER of an embedding and therefore untruncated
  -- (agents/tasks/LJ-1-549/Probe549.agda:262-266).
  g : ⟪ fst δ ⟫ → ⟪ fst (powL κ) ⟫
  g k = P549.ixOf (powL κ) (s k) (P549.powL-in κ (s k) (sub k))

  g-val : (k : ⟪ fst δ ⟫) → ⟪ fst (powL κ) ⟫↪ (g k) ≡ fst (s k)
  g-val k = P549.ixOf-val (powL κ) (s k) (P549.powL-in κ (s k) (sub k))

  ginj : (k k' : ⟪ fst δ ⟫) → g k ≡ g k' → k ≡ k'
  ginj k k' e = inj k k' (sym (g-val k) ∙ cong (⟪ fst (powL κ) ⟫↪) e ∙ g-val k')

  -- AND `IsGraph` AT THAT INJECTION IS [LJ-1.554]'s `IsGraphOf` AT `s`.
  convert : (G : S) → IsGraph δ (powL κ) g G → P554.IsGraphOf δ s G
  convert G (gin , gout) = into , out
    where
    into : (x y : S) (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
         → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
    into x y m e =
      subst (λ v → ⟨ pr v (fst y) ∈ fst G ⟩) (P549.ixOf-val δ x m)
        (subst (λ v → ⟨ pr (⟪ fst δ ⟫↪ k) v ∈ fst G ⟩)
          (sym (e ∙ sym (g-val k))) (gin k))
      where
      k : ⟪ fst δ ⟫
      k = P549.ixOf δ x m
    out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
        → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (s (P549.ixOf δ x m))
    out x y p m = PT.rec (setIsSet (fst y) (fst (s (P549.ixOf δ x m)))) go (gout x y p)
      where
      go : Σ[ k ∈ ⟪ fst δ ⟫ ] ((fst x ≡ ⟪ fst δ ⟫↪ k) × (fst y ≡ ⟪ fst (powL κ) ⟫↪ (g k)))
         → fst y ≡ fst (s (P549.ixOf δ x m))
      go (k , (ex , ey)) =
        ey ∙ g-val k
           ∙ cong (λ w → fst (s w))
               (sym (↪-inj {a = fst δ} (P549.ixOf-val δ x m ∙ ex)))

-- THE IMPLICATION.  `graph→link` is [LJ-1.554]'s and is not rebuilt.
w→link : W → (δ κ : S) (s : ⟪ fst δ ⟫ → S)
       → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
       → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
       → ∥ P554.LinkAt δ s ∥₁
w→link w δ κ s sub inj =
  PT.map (λ { (G , h) → P554.graph→link δ s G (L.convert G h) })
         (w δ (powL κ) L.g L.ginj)
  where
  module L = Link δ κ s sub inj

-- AND IT PAYS [LJ-1.549]'s RESIDUE OUTRIGHT, which is what the fourth
-- component was for.
w→residue : W → (δ κ : S) (s : ⟪ fst δ ⟫ → S)
          → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
          → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
          → ∥ P549.Residue δ κ ∥₁
w→residue w δ κ s sub inj =
  PT.map (λ l → s , (sub , (inj , l))) (w→link w δ κ s sub inj)


-- ===================================================================
-- SECTION 4.  THE TWO SITE INSTANCES, AT THEIR OWN HYPOTHESES.
--
--   Section 2's implication is general.  These two put it at the two
--   sites that stopped, with the ambient half taken from the tree.
-- ===================================================================

-- 4.1  B9, [LJ-1.533].  AT ITS CORRECTED TARGET AND NOT AT THE BRIEF'S:
--      agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:22-52
--      refuted the unrestricted form.  The two extra hypotheses are
--      `stage-card-upper`'s own (src/L/StageCardinal.lagda.md:564-565).
w→B9 : W → (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
     → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
     → InjL (LsetS δ oδ) (δ , isL-ord δ oδ)
w→B9 w δ oδ δ∈suc infδ =
  w→code w (LsetS δ oδ) (δ , isL-ord δ oδ)
    (SC.Upper.stage-card-upper δ oδ δ∈suc infδ)

-- 4.2  B7, [LJ-1.535].  ITS SITE IS THE SAME PAIR, and that identity is
--      the reason this task exists.  The counting site's bare Σ is
--      `stage-card-upper`'s value
--      (agents/tasks/LJ-1-535/Probe535.agda:144-146 names it
--      `delivered`), so B7 and B9 are ONE instance of `w→code`.
w→B7 : W → (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
     → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
     → InjL (LsetS δ oδ) (δ , isL-ord δ oδ)
w→B7 = w→B9


-- ===================================================================
-- SECTION 5.  THE TWO `W` DOES NOT REACH, AND WHY.  MEASURED.
-- ===================================================================

-- 5.1  THE ASSIGNMENT, [LJ-1.552].  `W` DOES NOT REACH IT, AND THE
--      REASON IS NOT A GAP IN THE IMPLICATION.  IT IS THAT `W`'s
--      HYPOTHESIS AT THAT SITE **IS** THAT SITE'S CONCLUSION.
--
--      Both directions below typecheck, so the identification is the
--      elaborator's and not mine.
assignment→hypothesis :
    (δ κ : S)
  → Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
      ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
      × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') )
  → ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫
assignment→hypothesis δ κ (s , (sub , inj)) = L.g , L.ginj
  where
  module L = Link δ κ s sub inj

hypothesis→assignment :
    (δ κ : S)
  → ⟪ fst δ ⟫ ↪ ⟪ fst (powL κ) ⟫
  → Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
      ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
      × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') )
hypothesis→assignment δ κ (f , finj) = s , (sub , inj)
  where
  s : ⟪ fst δ ⟫ → S
  s k = up (powL κ) (f k)
  sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩
  sub k = P549.powL-sub κ (s k) (member (fst (powL κ)) (f k))
  inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k'
  inj k k' e = finj k k' (↪-inj {a = fst (powL κ)} e)

-- AND WHAT `W` DOES BUY AT THAT SITE IS ALREADY DELIVERED WITHOUT IT.
-- [LJ-1.552]'s `member-into-kappa` gives the ambient injection at each
-- member of δ, so `W` gives the code at each member.
w-at-assignment : W → (δ κ : S) → SuccCardL δ κ
                → (a : S) → ⟨ fst a ∈ fst δ ⟩ → InjL a κ
w-at-assignment w δ κ sc a a∈δ =
  PT.rec PT.squash₁ (w→code w a κ) (P552.member-into-kappa δ κ sc a a∈δ)

-- THE SAME TYPE, WITH NO `W` AT ALL: [LJ-1.557] is GO and delivers it
-- (agents/tasks/LJ-1-557/Probe557.agda:275-277).
already-at-assignment : (δ κ : S) → SuccCardL δ κ
                      → (a : S) → ⟨ fst a ∈ fst δ ⟩ → InjL a κ
already-at-assignment = P557.member-code-into-kappa

-- 5.2  `StageHigh`, [LJ-1.536].  `W` DOES NOT REACH IT, AND THE REASON
--      IS THAT `W`'s CONCLUSION IS FREE THERE ALREADY.  What the site
--      wants placed is `hierL γ`, which is a term of `S`: it is in L
--      before anything is proved.  The site's demand is a NAMED STAGE,
--      and no instance of `W` mentions a stage.
site5-subject-is-already-L :
    (γ : V ℓ) (oγ : IsOrd γ) → ⟨ isL (fst (hierL γ (isL-ord γ oγ) oγ)) ⟩
site5-subject-is-already-L γ oγ = snd (hierL γ (isL-ord γ oγ) oγ)

Missing-StageHigh : Type (ℓ-suc ℓ)
Missing-StageHigh =
    (γ : V ℓ) (oγ : IsOrd γ) → ((δ : V ℓ) → ⟨ δ ∈ γ ⟩ → ⟨ sucV δ ∈ γ ⟩)
  → ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset (sucV (sucV (sucV γ))) ⟩


-- ===================================================================
-- SECTION 6.  THE OBLIGATION.
--
--   `W`, TOGETHER WITH A PROOF THAT IT IMPLIES EACH OF THE SITES IT
--   REACHES.  Three of the five, and they are not three of a kind:
--   the first two are the condensation leg and the third is the GCH
--   leg.  The two it does not reach are section 5, measured there.
-- ===================================================================

one-wall :
    (W → (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
       → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
       → InjL (LsetS δ oδ) (δ , isL-ord δ oδ))
  × ( (W → (a b : S) → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ → InjL a b)
    × (W → (δ κ : S) (s : ⟪ fst δ ⟫ → S)
         → ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
         → ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
         → ∥ P549.Residue δ κ ∥₁) )
one-wall = w→B9 , (w→code , w→residue)
