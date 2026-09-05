{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.532] PROBE.  Row six's one membership: the approximation
-- function itself in `K`.  It runs in agents/tasks/LJ-1-532/ and lands
-- nothing in src/.
--
--   W3, FIRST      runs/W3.agda, typechecked before this file existed.
--                  It measured that `ApproxAt` is BLIND to a member of
--                  the approximation that is not a Kuratowski pair.
--   NOT DELIVERED  `approx-in-K`, the briefed obligation, IS NOT
--                  INHABITED HERE AND CANNOT BE: section 2 refutes it.
--                  The brief's own stop condition is met and this file
--                  is the evidence.  review-of-approx-in-K.md states it.
--   DELIVERED      the refutation, and the two facts that say what to
--                  put in its place: every approximation on an ordinal
--                  carries EXACTLY the pairs `hierL` carries
--                  (section 3), so the ∀-form fails only on junk and
--                  the corrected statement quantifies over the
--                  CANONICAL witness (section 4).
--
-- THE FINDING IN ONE SENTENCE.  `LsetGraphAt`'s existential is over the
-- whole class carrier and `ApproxAt` constrains only the pair members
-- of its witness, so an arbitrary witness may carry a member of any
-- level whatever; and once the witness is canonicalised, what is left
-- to prove is `hierL β ∈ Lset α`, which is [LJ-1.494]'s and
-- [LJ-1.230]'s recorded gap and not a new one.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-532.Probe532 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( ω-ord; ∅-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( ord∈Lset→∈; ord∈Lset-suc; Lset-cumul )
open import L.Axioms.Basic {ℓ} using ( ∅∈L; LsetS )
open import L.Axioms.Infinity {ℓ} lem using ( ω∈L )
open import L.Coding.InL {ℓ} using ( sgl-in; sglʟ; sglʟ-fst; sglʟ-out )
open import L.Coding.Model {ℓ} using ( domAt; domAt-intro )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; ApproxAt; ApproxAt-in; ApproxAt-dom; ApproxAt-value
        ; LsetGraphAt )
open import L.Hierarchy {ℓ} lem
  using ( Values; Entries; Domain; IsHier; hierL; hierL-spec
        ; hier-in; hier-out; approx-val; step-table )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Vec using ( lookup; _∷_; [] )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; pairing-ax; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; ω; ω-empty; ω-next )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ ) using ( _^_ )

-- ---------------------------------------------------------------------
-- SECTION 1.  THE FRAME, AND THE BRIEF'S STATEMENT AS A TYPE.
--
-- Every line of this section is runs/W3.agda's, which typechecked alone
-- before this file existed.
-- ---------------------------------------------------------------------

-- Verbatim from [LJ-1.522] (agents/tasks/LJ-1-522/Probe522.agda:75-79),
-- through [LJ-1.530] (agents/tasks/LJ-1-530/Probe530.agda:77-82).
IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ α ⟩
          × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

-- NOT VACUOUS, and here it does a second job: the refutation instance
-- is AT ω, so this witness is what makes the refutation concrete.
-- Verbatim from [LJ-1.530] (agents/tasks/LJ-1-530/Probe530.agda:86-91).
ω-IsLimit : IsLimit ω
ω-IsLimit =
    ω-ord
  , ( ∈∈ₛ {a = ∅} {b = ω} .snd ω-empty
    , (λ β β∈ω → ∈∈ₛ {a = sucV β} {b = ω} .snd
        (ω-next β (∈∈ₛ {a = β} {b = ω} .fst β∈ω))) )

-- THE BRIEF'S STATEMENT.  The spelling is the site's own: `LsetGraphAt
-- w b` puts the approximation at slot `zero` of the extended
-- environment and its domain bound at `suc b`
-- (src/L/Coding/Sequence.lagda.md:291-292), so the brief's
-- `⟨ γ ⊨ ApproxAt-at-g ⟩` is `⟨ (g ∷ γ) ⊨ ApproxAt zero (suc b) ⟩`.
--
-- EVERY FRAME FACT THE CHAIN HAS EVER CARRIED IS A HYPOTHESIS HERE, so
-- nobody can say the refutation won by dropping one: K is a LIMIT
-- level, the bound is an ORDINAL, and the bound lies IN K.
ApproxInK : Type (ℓ-suc ℓ)
ApproxInK =
    (α : V ℓ) → IsLimit α
  → ∀ {n} (b K : Fin n) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → IsOrd (fst (lookup b γ))
  → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
  → (g : S)
  → ⟨ (g ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
  → ⟨ fst g ∈ fst (lookup K γ) ⟩

-- AN ORDINAL IS NOT A KURATOWSKI PAIR.  `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆`
-- (src/V/Coding.lagda.md:175-176), so a transitive `pr a b` pulls `a`
-- down into itself and `∈-irrefl` (src/V/Hierarchy.lagda.md:155-156)
-- closes it.  Transitivity is `IsOrd`'s first component
-- (src/L/Constructible.lagda.md:141-142 with :83).
private
  inPair : (u v x : V ℓ) → ∥ (x ≡ u) ⊎ (x ≡ v) ∥₁ → ⟨ x ∈ ⁅ u , v ⁆ ⟩
  inPair u v x h = ∈∈ₛ {a = x} {b = ⁅ u , v ⁆} .snd (pairing-ax u v x .snd h)

  outPair : (u v x : V ℓ) → ⟨ x ∈ ⁅ u , v ⁆ ⟩ → ∥ (x ≡ u) ⊎ (x ≡ v) ∥₁
  outPair u v x h = pairing-ax u v x .fst (∈∈ₛ {a = x} {b = ⁅ u , v ⁆} .fst h)

ord-not-pr : (A : V ℓ) → IsOrd A → (a b : V ℓ) → A ≡ pr a b → Empty.⊥
ord-not-pr A oA a b q =
  PT.rec Empty.isProp⊥ close (outPair ⁅ a ⁆s ⁅ a , b ⁆ a a∈pr)
  where
  trans-pr : {x y : V ℓ} → ⟨ y ∈ x ⟩ → ⟨ x ∈ pr a b ⟩ → ⟨ y ∈ pr a b ⟩
  trans-pr {x} {y} y∈x x∈ = subst (λ u → ⟨ y ∈ u ⟩) q
    (oA .fst y∈x (subst (λ u → ⟨ x ∈ u ⟩) (sym q) x∈))

  a∈sgl : ⟨ a ∈ ⁅ a ⁆s ⟩
  a∈sgl = sgl-in a a refl

  a∈pair : ⟨ a ∈ ⁅ a , b ⁆ ⟩
  a∈pair = inPair a b a ∣ inl refl ∣₁

  sgl∈pr : ⟨ ⁅ a ⁆s ∈ pr a b ⟩
  sgl∈pr = inPair ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s ∣ inl refl ∣₁

  a∈pr : ⟨ a ∈ pr a b ⟩
  a∈pr = trans-pr a∈sgl sgl∈pr

  close : (a ≡ ⁅ a ⁆s) ⊎ (a ≡ ⁅ a , b ⁆) → Empty.⊥
  close (inl e) = ∈-irrefl a (subst (λ u → ⟨ a ∈ u ⟩) (sym e) a∈sgl)
  close (inr e) = ∈-irrefl a (subst (λ u → ⟨ a ∈ u ⟩) (sym e) a∈pair)

-- ---------------------------------------------------------------------
-- SECTION 2.  THE REFUTATION.
--
-- The instance is the cheapest one the frame admits and nothing about
-- it is degenerate on the frame's own terms: `K` is `Lset ω`, a limit
-- level; the domain bound is `∅`, an ordinal, and it lies in `K`; and
-- the approximation is `⁅ ω ⁆s`, an element of the class carrier.
--
-- `domAt`'s two halves and the step condition are ALL vacuous, and each
-- for a reason named here: no member of `⁅ ω ⁆s` is a Kuratowski pair,
-- and no set is a member of `∅`.  So `⁅ ω ⁆s` IS an approximation on
-- `∅`, and it is not in `Lset ω`, because `Lset ω` is transitive and
-- `ω ∉ Lset ω`.
-- ---------------------------------------------------------------------

∅ʟ ωʟ Lωʟ gʟ : S
∅ʟ = ∅ , ∅∈L
ωʟ = ω , ω∈L
Lωʟ = LsetS ω ω-ord
gʟ = sglʟ ωʟ

γ₀ : S ^ 2
γ₀ = ∅ʟ ∷ Lωʟ ∷ []

no-pair-in-g : (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst gʟ ⟩ → Empty.⊥
no-pair-in-g c z p = ord-not-pr ω ω-ord (fst c) (fst z)
  (sym (sglʟ-out ωʟ (pr (fst c) (fst z)) p))

dom-blind : ⟨ (gʟ ∷ γ₀) ⊨ domAt zero (suc zero) ⟩
dom-blind = domAt-intro zero (suc zero) (gʟ ∷ γ₀)
  (λ x → (λ h → PT.rec (snd (fst x ∈ ∅))
                  (λ { (y , p) → Empty.rec (no-pair-in-g x y p) }) h)
       , (λ m → Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst m))))

-- THE MEASUREMENT OF W3, MOVED HERE UNCHANGED.  `ApproxAt` holds of a
-- set whose one member is `ω`.
blind : ⟨ (gʟ ∷ γ₀) ⊨ ApproxAt zero (suc zero) ⟩
blind = ApproxAt-in zero (suc zero) (gʟ ∷ γ₀) dom-blind
  (λ c z p → Empty.rec (no-pair-in-g c z p))

∅∈Lω : ⟨ ∅ ∈ Lset ω ⟩
∅∈Lω = Lset-cumul ∅ ω ∅-ord ω-ord (∈∈ₛ {a = ∅} {b = ω} .snd ω-empty)
  (ord∈Lset-suc ∅ ∅-ord)

ω∉Lω : ⟨ ω ∈ Lset ω ⟩ → Empty.⊥
ω∉Lω h = ∈-irrefl ω (ord∈Lset→∈ ω ω-ord ω ω-ord h)

sgl-ω∉Lω : ⟨ ⁅ ω ⁆s ∈ Lset ω ⟩ → Empty.⊥
sgl-ω∉Lω h = ω∉Lω (layer-trans (Lset-layer ω) (sgl-in ω ω refl) h)

-- THE OBLIGATION IS FALSE.
ApproxInK-is-false : ApproxInK → Empty.⊥
ApproxInK-is-false k = sgl-ω∉Lω
  (subst (λ u → ⟨ u ∈ Lset ω ⟩) (sglʟ-fst ωʟ)
    (k ω ω-IsLimit zero (suc zero) γ₀ refl ∅-ord ∅∈Lω gʟ blind))

-- ---------------------------------------------------------------------
-- SECTION 3.  WHAT SURVIVES, AND IT IS THE WHOLE OF THE REPAIR.
--
-- The refutation is not an accident of `∅`.  An approximation on an
-- ordinal is pinned EXACTLY on its pair members and nowhere else, and
-- this section proves both directions against `hierL`, the tree's own
-- canonical table (src/L/Hierarchy.lagda.md:621-626).  So two
-- approximations on one ordinal differ only in members that are not
-- pairs, and the refutation says that difference is unbounded.
--
-- NOTHING HERE IS NEW MATHEMATICS.  Forward is `approx-val`
-- (src/L/Hierarchy.lagda.md:274-278) with `hier-in` (:527-534);
-- backward is `hier-out` (:511-525) with `ApproxAt-value`
-- (src/L/Coding/Sequence.lagda.md:298-301) and `approx-val` again.
-- ---------------------------------------------------------------------

module _ {n : ℕ} (f b : Fin n) (γ : S ^ n) (ob : IsOrd (fst (lookup b γ))) where
  private
    B : V ℓ
    B = fst (lookup b γ)

    H : S
    H = hierL B (lookup b γ .snd) ob

    sp : IsHier B H
    sp = hierL-spec B (lookup b γ .snd) ob

  pairs-into-hier : ⟨ γ ⊨ ApproxAt f b ⟩ → (c z : S)
                  → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                  → ⟨ pr (fst c) (fst z) ∈ fst H ⟩
  pairs-into-hier h c z p =
    subst (λ t → ⟨ pr (fst c) t ∈ fst H ⟩)
      (sym (approx-val f b γ h ob c z p))
      (hier-in B ob H sp c (ApproxAt-dom f b γ h c z p))

  pairs-from-hier : ⟨ γ ⊨ ApproxAt f b ⟩ → (c z : S)
                  → ⟨ pr (fst c) (fst z) ∈ fst H ⟩
                  → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
  pairs-from-hier h c z p =
    PT.rec (snd (pr (fst c) (fst z) ∈ fst (lookup f γ))) go
      (ApproxAt-value f b γ h c (hier-out B ob H sp c z p .fst))
    where
    go : Σ[ y ∈ S ] ⟨ pr (fst c) (fst y) ∈ fst (lookup f γ) ⟩
       → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
    go (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst (lookup f γ) ⟩)
      (approx-val f b γ h ob c y q ∙ sym (hier-out B ob H sp c z p .snd)) q

-- ---------------------------------------------------------------------
-- SECTION 4.  THE CORRECTED STATEMENT, AND IT IS NOT A NEW GAP.
--
-- Section 3 says the canonical table `hierL` is the only approximation
-- worth quantifying over, so row six's membership, correctly stated, is
-- about `hierL` and not about an arbitrary witness.  Written out, that
-- is the statement below.
--
-- IT IS NOT INHABITED HERE AND NOTHING IN THE TREE INHABITS IT.
-- [LJ-1.494] measured exactly this and reported NO-GO
-- (agents/tasks/LJ-1-494/lj-1.494-report.md:66-68: "Is `hierL δ` a
-- member of `Lset α` when `δ` is?  The tree does not bound `hierL δ` by
-- `α`"), and [LJ-1.230] recorded the same gap before it.
--
-- SO THE TWO CARRIERS SHARE ONE OBSTRUCTION AND NOT TWO.  This is the
-- brief's own question, and the answer is ONE.
HierInK : Type (ℓ-suc ℓ)
HierInK = (α : V ℓ) → IsLimit α
        → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
        → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩

-- AND THE REDUCTION IS NOT VACUOUS: the machine's row six is about
-- `LsetGraphAt`, whose witness is exactly an `ApproxAt` on the bound.
-- The name is used here only so no reader has to take the report's word
-- for which formula this task was about.
row-six-machine : ∀ {n} → Fin n → Fin n → _
row-six-machine w b = LsetGraphAt w b

-- ---------------------------------------------------------------------
-- SECTION 5.  THE CORRECTED STATEMENT IS NOT VACUOUS: THE CANONICAL
-- WITNESS IS AN APPROXIMATION.
--
-- Section 4 would be worth nothing if `hierL B` failed to satisfy
-- `ApproxAt`, because then the ∃-form would have no candidate and the
-- repair would be empty.  It does satisfy it, and this section says so.
--
-- THIS IS `graph-table`'s OWN `approx` BLOCK (src/L/Hierarchy.lagda.md:
-- 417-419, with its two `where` helpers at :390-401 and :403-415),
-- RE-MEASURED HERE.
-- It is re-measured and not cited because `src/` keeps it private
-- inside a term that also builds the OUTER step, and row six needs the
-- approximation alone.  The three tables it consumes are `hier-out`
-- and `hier-in` (src/L/Hierarchy.lagda.md:511-534), exactly as
-- `Lset-defines` (:645-655) consumes them.
-- ---------------------------------------------------------------------

module _ {n : ℕ} (b : Fin n) (γ : S ^ n) (ob : IsOrd (fst (lookup b γ))) where
  private
    B : V ℓ
    B = fst (lookup b γ)

    H : S
    H = hierL B (lookup b γ .snd) ob

    sp : IsHier B H
    sp = hierL-spec B (lookup b γ .snd) ob

    vals : Values H B
    vals c z _ p = hier-out B ob H sp c z p .snd

    ents : Entries H B
    ents = hier-in B ob H sp

    dom : Domain H B
    dom c z p = hier-out B ob H sp c z p .fst

    onDom : (c : S)
          → (⟨ ⋁ S (λ y → pr (fst c) (fst y) ∈ fst H) ⟩ → ⟨ fst c ∈ B ⟩)
          × (⟨ fst c ∈ B ⟩ → ⟨ ⋁ S (λ y → pr (fst c) (fst y) ∈ fst H) ⟩)
    onDom c = (λ hy → PT.rec (snd (fst c ∈ B))
                        (λ { (y , p) → dom c y p }) hy)
            , (λ c∈ → ∣ LsetS (fst c) (mem-ord {A = B} ob (fst c) c∈)
                     , ents c c∈ ∣₁)

    onStep : (c y : S) → ⟨ pr (fst c) (fst y) ∈ fst H ⟩
           → ⟨ (y ∷ c ∷ H ∷ γ) ⊨ StepAt zero (suc zero) (suc (suc zero)) ⟩
    onStep c y p = step-table zero (suc zero) (suc (suc zero)) (y ∷ c ∷ H ∷ γ)
      oc vals' ents' (vals c y c∈ p)
      where
      c∈ : ⟨ fst c ∈ B ⟩
      c∈ = dom c y p
      oc : IsOrd (fst c)
      oc = mem-ord {A = B} ob (fst c) c∈
      vals' : Values H (fst c)
      vals' e t _ r = vals e t (dom e t r) r
      ents' : Entries H (fst c)
      ents' e e∈ = ents e (ob .fst {x = fst c} {y = fst e} e∈ c∈)

  hier-is-approx : ⟨ (hierL (fst (lookup b γ)) (lookup b γ .snd) ob ∷ γ)
                     ⊨ ApproxAt zero (suc b) ⟩
  hier-is-approx = ApproxAt-in zero (suc b) (H ∷ γ)
    (domAt-intro zero (suc b) (H ∷ γ) onDom) onStep
