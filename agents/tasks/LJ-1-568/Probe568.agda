{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.568]  THE WEAKEST `g` UNDER WHICH `W` STILL PAYS THREE SITES.
--
-- W3 IS agents/tasks/LJ-1-568/runs/W3.agda AND IT WAS WRITTEN FIRST
-- AND TYPECHECKED ALONE.  Three runs, exit 0, runs/w3-1.out to
-- w3-3.out.  Its finding is section 0.4 below.
--
-- THE OBLIGATION IS INHABITED.  `W-restricted` is section 6.  This
-- file carries NO hole and NO postulate, so every reduction in it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552], [LJ-1.554], [LJ-1.557] and [LJ-1.561]).
-- Nothing lands in `src/`.
--
-- THE ANSWER IN ONE LINE.  THE WEAKEST SUFFICIENT HYPOTHESIS ON `g` IS
-- [LJ-1.554]'s `LinkAt` TRANSPLANTED TO `g`, AND THAT IS NOT A CHOICE
-- I MADE: section 4 proves that EVERY sufficient hypothesis implies it.
-- Under it the statement stops being a residue and becomes a THEOREM
-- (section 2).  AND NONE OF THE THREE SITES SUPPLIES IT: section 5
-- proves, at a quantified `H` and not at my `Def`, that a site which
-- supplies ANY sufficient hypothesis has thereby closed itself.
--
--   Section 0.  D-10, BEFORE ANY OTHER AGDA.  `W` as stated is not
--               refuted, and the reason is a typechecked row.
--   Section 1.  `Restrict H`: `W` with an extra hypothesis on `g`,
--               generic in the hypothesis.  And `Def`, mine.
--   Section 2.  `Restrict Def` IS A THEOREM.  No residue is left.
--   Section 3.  THE THREE SITES, at a quantified `H`.
--   Section 4.  `Def` IS THE WEAKEST: every sufficient `H` implies it.
--   Section 5.  SO NO SITE SUPPLIES IT.  Measured, site by site.
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

module LJ-1-568.Probe568 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Axioms.Basic {ℓ} using ( LsetS; hasUnionL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.Reflect {ℓ} lem using ( Below; Wit )
open import L.GCH {ℓ} lem using ( InjL )
import L.StageCardinal

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( funExt )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( ℩; ℩-spec; _⊆ˢ_; SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- THE FOUR PREDECESSORS THIS FILE STANDS ON.  Each is GO and each
-- probe is green and carries no hole, so every type below is IMPORTED
-- from the file that typechecked and none is transcribed.
import LJ-1-549.Probe549 {ℓ} lem as P549
import LJ-1-554.Probe554 {ℓ} lem as P554
import LJ-1-560.Probe560 {ℓ} lem as P560
import LJ-1-561.Probe561 {ℓ} lem α₀ oα₀ sq as P561

-- An ordinal as an L-element, [LJ-1.536]'s one-liner through
-- [LJ-1.561]'s `isL-ord` (Probe561.agda:110-111).  Named once because
-- the bare pair carries no expected type outside an application.
ordS : (δ : V ℓ) → IsOrd δ → S
ordS δ oδ = δ , P561.isL-ord δ oδ


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA.
--
--   THE BRIEF ORDERS THIS FIRST: try to refute `W` as [LJ-1.561]
--   states it.  I DID NOT REFUTE IT, and the reason is not that I ran
--   out of budget.  The reason is a row that typechecks.
-- ===================================================================

-- 0.1  A REFUTATION OF `W` IS A REFUTATION OF `V = L`.  [LJ-1.561]
--      already proved `V = L → W` (Probe561.agda:195-196), so this is
--      that term contraposed and nothing more.  The tree is the study
--      of what holds INSIDE L; it carries no non-constructible set,
--      and a term of this type would produce the refutation of `V = L`
--      that no chapter of `src/` has.
refuting-W-refutes-V=L : (P561.W → Empty.⊥) → ((x : V ℓ) → ⟨ isL x ⟩) → Empty.⊥
refuting-W-refutes-V=L nw vl = nw (P561.vl→w vl)

-- 0.2  AND `W` IS NOT VACUOUS EITHER, by the same row read forwards.
--      So `W` sits strictly between: not provable here (it is `V = L`'s
--      consequence and nothing weaker is known to give it) and not
--      refutable here.  THIS IS WHY THE TASK IS THE RESTRICTION.
V=L→W : ((x : V ℓ) → ⟨ isL x ⟩) → P561.W
V=L→W = P561.vl→w

-- 0.3  WHAT I DO NOT BELIEVE, STATED SO IT IS NOT LOST.  `W` quantifies
--      over EVERY ambient injection between the members of two L-sets.
--      Section 4 makes the disbelief precise instead of leaving it as
--      an opinion: `W` at `(a , b , g)` is EQUIVALENT to the graph of
--      `g` being definable over L, and an arbitrary ambient `g` carries
--      no formula.

-- 0.4  W3's FINDING, AND IT IS ABOUT THE B9 SITE'S OWN `g`.
--      `runs/W3.agda:98-102` ascribes that `g`: it is
--      `SC.Upper.stage-card-upper δ oδ δ∈suc infδ`, a
--      `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫`.  AND IT IS A TERM OF A MODULE THAT TAKES
--      `sq` AS A PARAMETER (src/L/StageCardinal.lagda.md:15-19): an
--      ARBITRARY ambient pairing injection at every infinite δ ≤ α₀.
--      Re-ascribed here so the fact is checked and not quoted.
B9-g : (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
     → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
     → ⟪ fst (LsetS δ oδ) ⟫ ↪ ⟪ fst (ordS δ oδ) ⟫
B9-g = SC.Upper.stage-card-upper


-- ===================================================================
-- SECTION 1.  `Restrict H`, AND `Def`.
--
--   `Restrict H` is [LJ-1.561]'s `W` with ONE extra hypothesis on the
--   triple `(a , b , g)`.  IT IS GENERIC IN THAT HYPOTHESIS, on
--   purpose: every claim of weakness in this file is then a claim
--   about ALL hypotheses and not about the one I happened to pick.
-- ===================================================================

Hyp : Type (ℓ-suc (ℓ-suc ℓ))
Hyp = (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) → Type (ℓ-suc ℓ)

Restrict : Hyp → Type (ℓ-suc ℓ)
Restrict H =
    (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
  → ((k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
  → H a b g
  → ∥ Σ[ G ∈ S ] P561.IsGraph a b g G ∥₁

-- 1.1  EVERY `Restrict H` IS A WEAKENING OF `W`, whatever `H` is.  So
--      "the restricted form" is the right name for all of them.
W→Restrict : (H : Hyp) → P561.W → Restrict H
W→Restrict H w a b g ginj _ = w a b g ginj

-- 1.2  THE VALUES OF `g`, AS L-ELEMENTS.  `up` is [LJ-1.561]'s
--      (Probe561.agda:114-115) and the transitivity is its, not mine.
val : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) → ⟪ fst a ⟫ → S
val a b g k = P561.up b (g k)

-- 1.3  `Def`, THE HYPOTHESIS.  IT IS NOT NEW: it is [LJ-1.554]'s
--      `LinkAt` (Probe554.agda:80-89), imported, at the assignment
--      `k ↦ g k`.  In words: SOME formula of the object language, with
--      L-sets as constants, describes `g` on the members of `a`, in
--      both directions.
--
--      NO LEVY GRADE IS ASKED FOR, AND THAT IS [LJ-1.560]'s GIFT: the
--      separation this hypothesis is spent through is `hasSeparationL`
--      (src/L/Axioms/Full.lagda.md:144), which takes an ARBITRARY
--      formula.  Section 5.3 measures that.
Def : Hyp
Def a b g = P554.LinkAt a (val a b g)


-- ===================================================================
-- SECTION 2.  `Restrict Def` IS A THEOREM.
--
--   THIS IS THE HALF THAT MAKES THE RESTRICTION WORTH ANYTHING.  Under
--   `Def` the statement is not a residue that a later task must pay:
--   it is discharged here, from [LJ-1.549]'s `module Table` and the
--   union axiom of L, with nothing postulated.
--
--   `Table` (Probe549.agda:268-438) wants a `κ` with every value a
--   SUBSET of κ.  THAT COSTS NOTHING AND IT IS NOT A SECOND
--   HYPOTHESIS: `⋃ b` inside L serves for every `b`, because every
--   member of `b` is a subset of `⋃ b`.
-- ===================================================================

module Build (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
             (ginj : (k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
             (D : Def a b g) where

  s : ⟪ fst a ⟫ → S
  s = val a b g

  -- THE BOUND, AND IT IS FREE.  `hasUnionL` is src/L/Axioms/Basic.lagda.md:731.
  κ : S
  κ = ℩ (hasUnionL b)

  sub : (k : ⟪ fst a ⟫) → ⟨ s k ⊆ˢ κ ⟩
  sub k z hz = subst ⟨_⟩ (sym (℩-spec (hasUnionL b) z))
                 ∣ s k , (member (fst b) (g k) , hz) ∣₁

  sinj : (k k' : ⟪ fst a ⟫) → fst (s k) ≡ fst (s k') → k ≡ k'
  sinj k k' e = ginj k k' (↪-inj {a = fst b} e)

  module T = P549.Table a κ s sub sinj (fst D) (fst (snd D)) (snd (snd D))

  -- The index of a member, and that it is the index we started from.
  private
    ix : (k : ⟪ fst a ⟫) → ⟪ fst a ⟫
    ix k = P549.ixOf a (P561.up a k) (member (fst a) k)

    ix-id : (k : ⟪ fst a ⟫) → ix k ≡ k
    ix-id k = ↪-inj {a = fst a}
      (P549.ixOf-val a (P561.up a k) (member (fst a) k))

  gin : P561.GraphIn a b g T.G
  gin k = subst (λ t → ⟨ pr (⟪ fst a ⟫↪ k) (fst (s t)) ∈ fst T.G ⟩) (ix-id k)
            (T.graph-in (P561.up a k) (member (fst a) k))

  gout : P561.GraphOut a b g T.G
  gout x y h = ∣ k , (sym (P549.ixOf-val a x m) , T.graph-val x y h m) ∣₁
    where
    m : ⟨ fst x ∈ fst a ⟩
    m = fst (T.graph-mem x y h)
    k : ⟪ fst a ⟫
    k = P549.ixOf a x m

  graph : Σ[ G ∈ S ] P561.IsGraph a b g G
  graph = T.G , (gin , gout)

-- THE THEOREM.
def-restricted : Restrict Def
def-restricted a b g ginj D = ∣ Build.graph a b g ginj D ∣₁

-- AND THE TRUNCATED FORM, which is what section 6 states, because the
-- conclusion is truncated already and nothing is gained by asking for
-- the formula untruncated.
Def∥ : Hyp
Def∥ a b g = ∥ Def a b g ∥₁

def∥-restricted : Restrict Def∥
def∥-restricted a b g ginj = PT.rec PT.squash₁ (def-restricted a b g ginj)


-- ===================================================================
-- SECTION 3.  THE THREE SITES, AT A QUANTIFIED `H`.
--
--   Nothing below mentions `Def`.  Each row is [LJ-1.561]'s own
--   implication with `W` replaced by `Restrict H`, and the site's
--   `g` carrying `H`.  Instantiating `H := Def∥` gives section 6;
--   instantiating it at anybody else's hypothesis gives section 5's
--   theorem, and that is why they are stated here once.
-- ===================================================================

-- 3.0  A CODE OUT OF A BARE Σ, which is [LJ-1.535]'s missing piece.
--      `Code.code` is [LJ-1.561]'s (Probe561.agda:218-284), not rebuilt.
restrict→code : (H : Hyp) → Restrict H
              → (a b : S) (e : ⟪ fst a ⟫ ↪ ⟪ fst b ⟫)
              → H a b (fst e) → InjL a b
restrict→code H r a b (g , ginj) h =
  PT.map (λ { (G , (gi , go)) → G , P561.Code.code a b g ginj G gi go })
         (r a b g ginj h)

-- 3.1  B9, [LJ-1.533], at its CORRECTED target (Probe561.agda:372-381).
restrict→B9 : (H : Hyp) → Restrict H
            → (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ SV.∈ˢ sucV α₀ ⟩)
            → (infδ : ⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
            → H (LsetS δ oδ) (ordS δ oδ) (fst (B9-g δ oδ δ∈suc infδ))
            → InjL (LsetS δ oδ) (ordS δ oδ)
restrict→B9 H r δ oδ δ∈suc infδ =
  restrict→code H r (LsetS δ oδ) (ordS δ oδ) (B9-g δ oδ δ∈suc infδ)

-- 3.2  B7, [LJ-1.535].  IT IS THE SAME TERM, exactly as [LJ-1.561]
--      measured (Probe561.agda:388-391).  The restriction does not
--      separate the two rows either.
restrict→B7 : (H : Hyp) → Restrict H
            → (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ SV.∈ˢ sucV α₀ ⟩)
            → (infδ : ⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
            → H (LsetS δ oδ) (ordS δ oδ) (fst (B9-g δ oδ δ∈suc infδ))
            → InjL (LsetS δ oδ) (ordS δ oδ)
restrict→B7 = restrict→B9

-- 3.3  `Link`, the fourth conjunct of [LJ-1.549]'s `Residue`.
--      `Link.g` and `Link.convert` are [LJ-1.561]'s (Probe561.agda:303-342)
--      and `graph→link` is [LJ-1.554]'s (Probe554.agda:232-235).
restrict→link : (H : Hyp) → Restrict H
              → (δ κ : S) (s : ⟪ fst δ ⟫ → S)
              → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
              → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
              → H δ (P549.powL κ) (P561.Link.g δ κ s sub inj)
              → ∥ P554.LinkAt δ s ∥₁
restrict→link H r δ κ s sub inj h =
  PT.map (λ { (G , q) → P554.graph→link δ s G (P561.Link.convert δ κ s sub inj G q) })
         (r δ (P549.powL κ) (P561.Link.g δ κ s sub inj)
            (P561.Link.ginj δ κ s sub inj) h)

-- 3.4  AND THE WHOLE `Residue`, as [LJ-1.561]'s `w→residue` does.
restrict→residue : (H : Hyp) → Restrict H
                 → (δ κ : S) (s : ⟪ fst δ ⟫ → S)
                 → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
                 → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
                 → H δ (P549.powL κ) (P561.Link.g δ κ s sub inj)
                 → ∥ P549.Residue δ κ ∥₁
restrict→residue H r δ κ s sub inj h =
  PT.map (λ l → s , (sub , (inj , l))) (restrict→link H r δ κ s sub inj h)


-- ===================================================================
-- SECTION 4.  `Def` IS THE WEAKEST, AND THAT IS A THEOREM.
--
--   I DID NOT SEARCH FOR THE WEAKEST HYPOTHESIS AND THEN STOP.  The
--   rows below prove that no search could do better: `Def` is implied
--   by EVERY hypothesis that is sufficient, so any hypothesis strictly
--   weaker than `Def` is not sufficient.
--
--   The engine is [LJ-1.554] section 2B, which needs no κ, no `⊆ˢ`
--   and no injectivity (Probe554.agda:232-265).
-- ===================================================================

-- 4.1  A GRAPH IN L IS [LJ-1.554]'s `IsGraphOf` AT THE SAME `s`.  This
--      is the converse of [LJ-1.561]'s `Link.convert`, at the general
--      pair rather than at `powL κ`.
isGraph→isGraphOf : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫) (G : S)
                  → P561.IsGraph a b g G → P554.IsGraphOf a (val a b g) G
isGraph→isGraphOf a b g G (gin , gout) = into , out
  where
  into : (x y : S) (m : ⟨ fst x ∈ fst a ⟩)
       → fst y ≡ fst (val a b g (P549.ixOf a x m))
       → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
  into x y m e =
    subst (λ t → ⟨ pr t (fst y) ∈ fst G ⟩) (P549.ixOf-val a x m)
      (subst (λ t → ⟨ pr (⟪ fst a ⟫↪ (P549.ixOf a x m)) t ∈ fst G ⟩)
        (sym e) (gin (P549.ixOf a x m)))

  out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
      → (m : ⟨ fst x ∈ fst a ⟩) → fst y ≡ fst (val a b g (P549.ixOf a x m))
  out x y h m =
    PT.rec (setIsSet (fst y) (fst (val a b g (P549.ixOf a x m)))) go (gout x y h)
    where
    go : Σ[ k ∈ ⟪ fst a ⟫ ]
           ((fst x ≡ ⟪ fst a ⟫↪ k) × (fst y ≡ ⟪ fst b ⟫↪ (g k)))
       → fst y ≡ fst (val a b g (P549.ixOf a x m))
    go (k , (ex , ey)) =
      ey ∙ cong (λ t → fst (val a b g t))
             (sym (↪-inj {a = fst a} (P549.ixOf-val a x m ∙ ex)))

-- 4.2  SO THE CONCLUSION GIVES `Def` BACK.  `Def` is NECESSARY.
graph→def : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
          → Σ[ G ∈ S ] P561.IsGraph a b g G → Def a b g
graph→def a b g (G , q) =
  P554.graph→link a (val a b g) G (isGraph→isGraphOf a b g G q)

-- 4.3  THE WEAKNESS THEOREM.  Any `H` that is sufficient implies `Def∥`.
--      Read the other way: `Def∥` is the weakest sufficient hypothesis
--      on `g` that exists, up to the truncation the conclusion already
--      carries.
weakest : (H : Hyp) → Restrict H
        → (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
        → ((k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
        → H a b g → Def∥ a b g
weakest H r a b g ginj h = PT.map (graph→def a b g) (r a b g ginj h)

-- 4.4  AND THE TWO HALVES TOGETHER: `Def∥` IS EQUIVALENT TO THE
--      CONCLUSION, at every injective `g`.  So `W` restricted to `Def`
--      is not a weaker assumption that buys the same thing.  It is the
--      thing itself, written as a hypothesis.
def∥↔conclusion : (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
                → ((k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
                → (Def∥ a b g → ∥ Σ[ G ∈ S ] P561.IsGraph a b g G ∥₁)
                × (∥ Σ[ G ∈ S ] P561.IsGraph a b g G ∥₁ → Def∥ a b g)
def∥↔conclusion a b g ginj =
    def∥-restricted a b g ginj
  , PT.map (graph→def a b g)


-- ===================================================================
-- SECTION 5.  SO NO SITE SUPPLIES IT.  MEASURED, SITE BY SITE.
--
--   THIS IS THE FINDING THE NEXT BRIEF NEEDS, and it is stated at a
--   QUANTIFIED `H`, so it is not a remark about my choice of `Def`.
--   A site that can supply a sufficient hypothesis has already paid
--   its own obligation, whatever that hypothesis is.
-- ===================================================================

-- 5.1  SITE `Link`.  IF THE SITE SUPPLIES `H`, THE SITE'S RESIDUE IS
--      CLOSED.  This is section 3.3 read as a statement about the
--      site: the antecedent is the site supplying `H` at its own `g`,
--      the consequent is [LJ-1.549]'s whole `Residue`.
no-free-lunch-at-link :
    (H : Hyp) → Restrict H
  → ((δ κ : S) (s : ⟪ fst δ ⟫ → S)
     → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
     → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
     → H δ (P549.powL κ) (P561.Link.g δ κ s sub inj))
  → (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → ∥ P549.Residue δ κ ∥₁
no-free-lunch-at-link H r supply δ κ s sub inj =
  restrict→residue H r δ κ s sub inj (supply δ κ s sub inj)

-- 5.2  AND AT THIS SITE IT IS SHARPER THAN THAT: `Def` AT THE SITE'S
--      `g` **IS** THE SITE'S OWN RESIDUE, not merely stronger than it.
--      Both directions, so the identification is the elaborator's.
--      The one step is that the site's `g` has [LJ-1.554]'s `s` as its
--      values, `Link.g-val` (Probe561.agda:314-315).
link-val : (δ κ : S) (s : ⟪ fst δ ⟫ → S)
         → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
         → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
         → val δ (P549.powL κ) (P561.Link.g δ κ s sub inj) ≡ s
link-val δ κ s sub inj =
  funExt (λ k → Σ≡Prop (λ x → snd (isL x)) (P561.Link.g-val δ κ s sub inj k))

def-at-link→residue :
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → Def δ (P549.powL κ) (P561.Link.g δ κ s sub inj) → P554.LinkAt δ s
def-at-link→residue δ κ s sub inj =
  subst (P554.LinkAt δ) (link-val δ κ s sub inj)

residue→def-at-link :
    (δ κ : S) (s : ⟪ fst δ ⟫ → S)
  → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
  → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
  → P554.LinkAt δ s → Def δ (P549.powL κ) (P561.Link.g δ κ s sub inj)
residue→def-at-link δ κ s sub inj =
  subst (P554.LinkAt δ) (sym (link-val δ κ s sub inj))

-- 5.3  SITE B9 AND SITE B7.  THE SAME SHAPE, AND THE SAME ANSWER: a
--      supply closes the site.  [LJ-1.533]'s and [LJ-1.535]'s
--      obligation is `InjL (LsetS δ oδ) (δ , _)` and this row hands it
--      over from the supply alone.
no-free-lunch-at-B9 :
    (H : Hyp) → Restrict H
  → ((δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ SV.∈ˢ sucV α₀ ⟩)
     → (infδ : ⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
     → H (LsetS δ oδ) (ordS δ oδ) (fst (B9-g δ oδ δ∈suc infδ)))
  → (δ : V ℓ) (oδ : IsOrd δ) → ⟨ δ SV.∈ˢ sucV α₀ ⟩
  → (⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
  → InjL (LsetS δ oδ) (ordS δ oδ)
no-free-lunch-at-B9 H r supply δ oδ δ∈suc infδ =
  restrict→B9 H r δ oδ δ∈suc infδ (supply δ oδ δ∈suc infδ)

-- 5.3a  BUT SITE B9 IS FREE TO CHANGE ITS `g`, AND SITE `Link` IS NOT.
--       B9's obligation is `InjL (LsetS δ oδ) (ordS δ oδ)`, which names
--       NO function: it asks for SOME code at that pair.  So the
--       hypothesis does not have to hold of `stage-card-upper`'s own
--       `g`.  It is enough that it holds of ONE injection there.
--
--       AND THE TWO SIDE CONDITIONS DISAPPEAR WHEN IT DOES.  `δ ∈ sucV α₀`
--       and `δ ∉ ω` are `stage-card-upper`'s hypotheses
--       (src/L/StageCardinal.lagda.md:564-565), and the only work they
--       did at this site was to produce the ambient injection.  Below
--       they are absorbed into the Σ.  THIS IS NOT A ROUTE PAST
--       [LJ-1.533], AND IT DOES NOT CLAIM WHAT [LJ-1.533] REFUSED TO
--       CLAIM.  That review says in its own words that it "did not
--       prove `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` false in Agda at any named finite δ"
--       (agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54-55).
--       What it measured is that the delivered chapter does not reach
--       the pair at a finite δ.  The row below says nothing at a δ
--       where the Σ has no inhabitant: it CONSUMES the injection and
--       never produces one.
--
--       THIS IS THE ROW A NEXT BRIEF SHOULD READ FIRST.  The classical
--       route does not use an arbitrary ambient injection at this site
--       at all: it uses the `<ʟ`-least-witness map of a DEFINABLE
--       well-order (dev/literature/devlin-II5.md:259-270), whose graph
--       carries a formula by construction.
B9-any-g : (H : Hyp) → Restrict H
         → (δ : V ℓ) (oδ : IsOrd δ)
         → Σ[ e ∈ (⟪ fst (LsetS δ oδ) ⟫ ↪ ⟪ fst (ordS δ oδ) ⟫) ]
             H (LsetS δ oδ) (ordS δ oδ) (fst e)
         → InjL (LsetS δ oδ) (ordS δ oδ)
B9-any-g H r δ oδ (e , h) = restrict→code H r (LsetS δ oδ) (ordS δ oδ) e h

-- 5.4  WHAT [LJ-1.560] SUPPLIES, MEASURED, BECAUSE THE BRIEF NAMES IT
--      AS THE MOST LIKELY SOURCE.
--
--      IT DOES NOT SUPPLY THE HYPOTHESIS AT ANY OF THE THREE SITES,
--      AND THE TYPE SAYS WHY: `search-bounds` TAKES a formula and
--      RETURNS a stage (Probe560.agda:165-176).  A site that has no
--      formula gets no formula from it.  Re-ascribed, TYPE ONLY.
p560-consumes-a-formula :
    {k : ℕ} (ψ : Formula S (suc k))
  → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
      ( ((ρ : S ^ k) → Below β ρ → ⟨ ρ ⊨ (∃̇ ψ) ⟩ → ⟨ Wit ψ ρ β ⟩)
      × ((ρ : S ^ k) → Below β ρ → (ρ ⊨ (∃̇ ψ)) ≡ (ρ ⊨ P560.boundAt ψ β oβ))
      × (Δ₀ ψ → Δ₀ (P560.boundAt ψ β oβ)) )
p560-consumes-a-formula = P560.search-bounds

--      WHAT IT DOES BUY IS REAL AND IT IS WHY `Def` ASKS FOR NO GRADE.
--      [LJ-1.560] section 5c is `hasSeparationL`, separation in L at an
--      ARBITRARY formula (Probe560.agda:223-225,
--      src/L/Axioms/Full.lagda.md:144).  `Table`'s carve runs through
--      exactly that, so `Def` carries no Δ₀ side condition and section
--      2 pays no price for its absence.
p560-removes-the-grade :
    (a : S) (φ : Formula S 1)
  → isContr (SetOf (λ x → (x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))
p560-removes-the-grade = hasSeparationL


-- ===================================================================
-- SECTION 6.  THE OBLIGATION.
--
--   `W` WITH THE WEAKEST EXTRA HYPOTHESIS ON `g`, TOGETHER WITH THE
--   THREE IMPLICATIONS.  Four components:
--
--     1.  the restricted form, PROVED, not assumed;
--     2.  B9, from it;
--     3.  B7, from it, and it is component 2's term;
--     4.  `Link`, from it.
--
--   THE WEAKENING IS STATED AND NOT HIDDEN.  Components 2 to 4 carry
--   the hypothesis AT THE SITE'S OWN `g` as a premise.  Section 5
--   proves that this is not an artefact of `Def`: no sufficient
--   hypothesis can be dropped from those rows, because a site that
--   discharges one has closed itself.
-- ===================================================================

W-restricted :
    Restrict Def∥
  × ( ( (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ SV.∈ˢ sucV α₀ ⟩)
        → (infδ : ⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
        → Def∥ (LsetS δ oδ) (ordS δ oδ) (fst (B9-g δ oδ δ∈suc infδ))
        → InjL (LsetS δ oδ) (ordS δ oδ) )
    × ( ( (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ SV.∈ˢ sucV α₀ ⟩)
          → (infδ : ⟨ δ SV.∈ˢ ω ⟩ → Empty.⊥)
          → Def∥ (LsetS δ oδ) (ordS δ oδ) (fst (B9-g δ oδ δ∈suc infδ))
          → InjL (LsetS δ oδ) (ordS δ oδ) )
      × ( (δ κ : S) (s : ⟪ fst δ ⟫ → S)
          → (sub : (k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
          → (inj : (k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k')
          → Def∥ δ (P549.powL κ) (P561.Link.g δ κ s sub inj)
          → ∥ P554.LinkAt δ s ∥₁ ) ) )
W-restricted =
    def∥-restricted
  , ( restrict→B9 Def∥ def∥-restricted
    , ( restrict→B7 Def∥ def∥-restricted
      , restrict→link Def∥ def∥-restricted ) )
