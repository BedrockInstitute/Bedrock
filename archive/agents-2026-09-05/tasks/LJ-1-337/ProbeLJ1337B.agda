{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.337 probe B.  It lands nothing.  It runs in agents/tasks/LJ-1-337/.
--
-- THE ASSEMBLY.  `[LJ-1.335]` section 4.1 stated `sq-below`: the lemma that
-- turns the unsupplied FAMILY of src/L/StageCardinal.lagda.md:17-19 into
-- ONE unsupplied BAND.  This file builds it on the dichotomy of
-- ProbeLJ1337A.agda.  It imports `L.Absorption` and `L.InjChain`, which
-- the dichotomy does not, so probe A carries the dichotomy's own seconds
-- and this file carries the assembly's.
--
-- PART 1 restates the two transports with the RAW SIGMA SHAPE.  The brief
--        orders this: the probes spell them with `_↪_` from `L.Cardinal`,
--        and `L.Cardinal` imports `L.Ordinal.SquareLaw` at
--        src/L/Cardinal.lagda.md:22, so the reverse edge is a cycle.  The
--        shape is the one `sq` itself uses at
--        src/L/Ordinal/SquareLaw.lagda.md:686-687.
-- PART 2 is the successor step, from `[LJ-1.330]`.
-- PART 3 states `SqBelow` and `LimitBand`, from `[LJ-1.335]` section 4.1.
-- PART 4 assembles `sq-below` by `∈-induction` over the ordinal.
-- PART 5 records the negative controls.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-337.ProbeLJ1337B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Absorption {ℓ} lem using ( module ShiftAbs )
open import LJ-1-337.ProbeLJ1337A {ℓ} lem
  using ( Closed; IsSuc; Split; ord-split; isPropInit )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  THE TRANSPORTS, IN THE RAW SIGMA SHAPE.
--
--   `Inj X Y` is written out rather than imported.  `ShiftAbs.shift↪`
--   (src/L/Absorption.lagda.md:189-190) is stated with `L.Cardinal`'s
--   `_↪_` (src/L/Cardinal.lagda.md:47-48), and PART 2 feeds it to a
--   function that asks for `Inj`.  THAT IS THE TEST: if the two are not
--   definitionally the same, this file fails, and the brief's rewrite is
--   not free after all.
-- =====================================================================

Inj : Type ℓ → Type ℓ → Type ℓ
Inj X Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

comp-inj : {A B C : Type ℓ} → Inj A B → Inj B C → Inj A C
comp-inj (f , finj) (g , ginj) =
  (λ x → g (f x)) , (λ x y e → finj x y (ginj (f x) (f y) e))

transport-sq : (α δ : S) → Inj ⟪ α ⟫ ⟪ δ ⟫ → Inj ⟪ δ ⟫ ⟪ α ⟫ → sq δ → sq α
transport-sq α δ (f , finj) (g , ginj) (p , pinj) = h , hinj
  where
  h : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  h (x , y) = g (p (f x , f y))

  hinj : (u v : ⟪ α ⟫ × ⟪ α ⟫) → h u ≡ h v → u ≡ v
  hinj (x , y) (x' , y') e i =
    finj x x' (cong fst r) i , finj y y' (cong snd r) i
    where
    r : (f x , f y) ≡ (f x' , f y')
    r = pinj (f x , f y) (f x' , f y')
          (ginj (p (f x , f y)) (p (f x' , f y')) e)

ord-emb : (a b : S) → IsOrd b → ⟨ a ∈ˢ b ⟩ → Inj ⟪ a ⟫ ⟪ b ⟫
ord-emb a b ob a∈b = f , inj
  where
  f : ⟪ a ⟫ → ⟪ b ⟫
  f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst

  inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = a}
    (sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
      ∙ cong (⟪ b ⟫↪) e
      ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd)

-- =====================================================================
-- PART 2.  THE SUCCESSOR STEP, from `[LJ-1.330]`.
--   agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-127, restated on `Inj`.
-- =====================================================================

sq-suc : (γ : S) → IsOrd γ → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
       → ((k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩)
       → sq γ → sq (sucV γ)
sq-suc γ oγ γ∉ω numerals s =
  transport-sq (sucV γ) γ SA.shift↪
    (ord-emb γ (sucV γ) (suc-ord oγ) (self∈sucV γ)) s
  where
  module SA = ShiftAbs γ oγ γ∉ω numerals

-- =====================================================================
-- PART 3.  THE TWO STATEMENTS, from `[LJ-1.335]` section 4.1.
--
--   `SqBelow α` IS the module parameter of `L.StageCardinal`
--   (src/L/StageCardinal.lagda.md:17-19), written out.  `LimitBand` is
--   `limit-truncated` (agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204)
--   with the truncation removed.
-- =====================================================================

SqBelow : S → Type (ℓ-suc ℓ)
SqBelow α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

LimitBand : Type (ℓ-suc ℓ)
LimitBand = (δ : S) → IsOrd δ → ⟨ ω ∈ˢ δ ⟩
          → Closed δ
          → (Init δ → Empty.⊥)
          → ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)
          → sq δ

-- =====================================================================
-- PART 4.  THE ASSEMBLY.
--
--   `∈-induction` over δ, with FOUR branches and no bound.  The bound of
--   `SqBelow` is never used, so the core is stated at every infinite
--   ordinal and `sq-below` reads it at the members of `sucV α`.
--
--     δ ∈ ω            refuted by the hypothesis
--     δ ≡ ω            `squareω`, src/L/InjChain.lagda.md:184-185
--     δ closed, Init   `via-col-square`, SquareLaw:960-961
--     δ closed, not    the band
--     δ successor      `sq-suc` on the induction hypothesis
--
--   The dichotomy decides the last two, and `isPropInit` decides the two
--   before them.
-- =====================================================================

Below : S → Type (ℓ-suc ℓ)
Below δ = IsOrd δ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

step : LimitBand → (δ : S) → ((β : S) → ⟨ β ∈ˢ δ ⟩ → Below β) → Below δ
step lb δ IH oδ δ∉ω = main (ord-tri δ oδ ω ω-ord)
  where
  main : Tri δ ω → sq δ
  main (inl δ∈ω)       = Empty.rec (δ∉ω δ∈ω)
  main (inr (inl δ≡ω)) = subst sq (sym δ≡ω) squareω
  main (inr (inr ω∈δ)) = at (ord-split δ oδ)
    where
    -- The induction hypothesis in the descent form the band reads.  A
    -- member with omega inside it is outside omega, by irreflexivity.
    ih : (β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β
    ih β β∈δ oβ ω∈β = IH β β∈δ oβ (λ β∈ω → ∈-irrefl ω (ω-ord .fst ω∈β β∈ω))

    limit : Closed δ → sq δ
    limit closed = decide (lem (Init δ , isPropInit δ))
      where
      decide : Init δ ⊎ (Init δ → Empty.⊥) → sq δ
      decide (inl i)  = via-col-square δ i
      decide (inr ni) = lb δ oδ ω∈δ closed ni ih

    successor : IsSuc δ → sq δ
    successor (γ , (oγ , (γ∈δ , δ≡sγ))) = subst sq (sym δ≡sγ) stepped
      where
      ω∈sγ : ⟨ ω ∈ˢ sucV γ ⟩
      ω∈sγ = subst (λ w → ⟨ ω ∈ˢ w ⟩) δ≡sγ ω∈δ

      -- The two hypotheses `ShiftAbs` takes, read off ONE elimination.
      -- The predecessor may BE omega, and that branch is real: control 3
      -- of probe A measures that `[LJ-1.332]`'s shape has no room for it.
      Gate : Type (ℓ-suc ℓ)
      Gate = (⟨ γ ∈ˢ ω ⟩ → Empty.⊥) × ((k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩)

      isPropGate : isProp Gate
      isPropGate = isProp× (isPropΠ (λ _ → Empty.isProp⊥))
                     (isPropΠ (λ k → snd ((# k) ∈ˢ γ)))

      gate : Gate
      gate = ∈sucV-elim {A = γ} {x = ω} {P = Gate} isPropGate ω∈sγ
        (λ ω∈γ → (λ γ∈ω → ∈-irrefl ω (ω-ord .fst ω∈γ γ∈ω))
                , (λ k → oγ .fst (#∈ω k) ω∈γ))
        (λ ω≡γ → (λ γ∈ω → ∈-irrefl ω
                    (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym ω≡γ) γ∈ω))
                , (λ k → subst (λ w → ⟨ (# k) ∈ˢ w ⟩) ω≡γ (#∈ω k)))

      stepped : sq (sucV γ)
      stepped = sq-suc γ oγ (gate .fst) (gate .snd)
                  (IH γ γ∈δ oγ (gate .fst))

    at : Split δ → sq δ
    at (inl c) = limit c
    at (inr s) = successor s

sq-core : LimitBand → (δ : S) → IsOrd δ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ
sq-core lb = ∈-induction (step lb)

sq-below : (α : S) → IsOrd α → LimitBand → SqBelow α
sq-below α oα lb δ δ∈sα δ∉ω = sq-core lb δ oδ δ∉ω
  where
  oδ : IsOrd δ
  oδ = mem-ord {A = sucV α} (suc-ord oα) δ δ∈sα

-- =====================================================================
-- PART 5.  THE NEGATIVE CONTROLS.  Each one was applied, run and
-- reverted.  They are recorded here because nothing typechecks this file
-- once the task closes.  Every one MEASURES.
--
--   CONTROL B1, ON `isProp (Init δ)`.  Give `lem` the `Init` decision
--   with `refl` in place of the propositionality:
--
--     limit closed = decide (lem (Init δ , (λ x y → refl)))
--
--   Agda refused, 1.8 s, 0 agda slots before the run, and it printed the
--   whole predicate:
--     error: [UnequalTerms]
--     x != y of type
--     Σ (IsOrd δ)
--     (λ _ → ⟨ ω ∈ˢ δ ⟩ ×
--        ((γ : S) → ⟨ γ ∈ˢ δ ⟩ → ⟨ sucV γ ∈ˢ δ ⟩) ×
--        ((β : S) → IsOrd β → ⟨ β ∈ˢ δ ⟩ → ⟨ ω ∈ˢ β ⟩ →
--         (f : ⟪ δ ⟫ → ⟪ β ⟫ × ⟪ β ⟫) →
--         ((m n : ⟪ δ ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥))
--     when checking that the expression refl has type x ≡ y
--
--   So `isPropInit` is not a convenience.  Without it the initial band
--   cannot be decided, and the machine names all four rows.
--
--   CONTROL B2, ON THE ONE OPEN BAND.  Drop the band and try the
--   delivered collapse at a non-initial limit:
--
--     decide (inr ni) = via-col-square δ ni
--
--   Agda refused, 2.4 s, 0 slots before the run:
--     error: [UnequalTerms]
--     (Init δ → Empty.⊥) !=< (Σ (IsOrd δ) (λ _ → ...four rows...))
--     when checking that the expression ni has type Init δ
--
--   MEASURED: the ONLY branch the delivered chapter cannot serve is the
--   non-initial limit, and the gap is exactly one negation.
--
--   CONTROL B3, ON THE TRUNCATION, AT THIS SITE (P-l).  `[LJ-1.332]`'s
--   `limit-truncated` (ProbeLJ1332A.agda:196-204) returns `∥ sq δ ∥₁`.
--   Offer it where `LimitBand` takes `sq δ`:
--
--     controlB3 : ((δ : S) → IsOrd δ → ⟨ ω ∈ˢ δ ⟩ → Closed δ
--                → (Init δ → Empty.⊥)
--                → ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)
--                → ∥ sq δ ∥₁)
--               → LimitBand
--     controlB3 t = t
--
--   Agda refused, 2.5 s, 0 slots before the run:
--     error: [UnequalTerms]
--     ∥ sq δ ∥₁ !=<
--     Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
--     (λ f → (x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)
--
--   THAT IS THE WHOLE REMAINING DISTANCE OF THIS LEG, IN ONE ERROR
--   MESSAGE.  One truncation bar at one band is what is left.
-- =====================================================================
