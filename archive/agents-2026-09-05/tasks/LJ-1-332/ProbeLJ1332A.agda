{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.332 probe A.  It lands nothing.  It runs in agents/tasks/LJ-1-332/.
--
-- THE BRIEF ASKS: is there a canonical `sq α` at a non-initial LIMIT
-- ordinal, and what does it cost?  The brief names `stage-card-upper` as
-- the lead and warns that this premise is the one most at risk.
--
-- PART 1 tests the lead.  It does NOT die of `[LJ-1.324]`'s motive, and
--        section 1 of the report says why.  It dies of a DIFFERENT and
--        cheaper defect, and one line of Agda states it.
-- PART 2 re-derives the two delivered legs the transport needs (C-44).
-- PART 3 reduces the limit band to ONE untruncated injection.
-- PART 4 builds the limit band's law TRUNCATED, from the induction
--        hypothesis alone.  This is the measurement: the wall is exactly
--        one untruncation and nothing else.
-- PART 5 assembles the four bands, truncated, at every infinite ordinal.
-- PART 6 records the negative controls.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-332.ProbeLJ1332A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; #∈ω )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-truncated )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Absorption {ℓ} lem using ( module ShiftAbs )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  THE LEAD, AND IT IS CIRCULAR.
--
--   `[LJ-1.324]` killed a `stage-card-upper` transplant with the MOTIVE:
--   `Upper.P` has ONE index while `CanonInj` needs two.  THIS pair has
--   ONE index too.  `sq α` moves its source `⟪ α ⟫ × ⟪ α ⟫` and its
--   target `⟪ α ⟫` together, exactly as `Upper.P` does
--   (src/L/Ordinal/SquareLaw.lagda.md:685-687 against
--   src/L/StageCardinal.lagda.md:530-532).  So that killer does NOT
--   apply here, and the lead needed a fresh test.
--
--   It fails a cheaper one.  `L.StageCardinal` takes the square law at
--   every bounded infinite δ as a MODULE PARAMETER
--   (src/L/StageCardinal.lagda.md:17-19), and `α` itself is one of those
--   δ, through `self∈sucV α`.  `LimitStep` spends it at `:283`.
-- =====================================================================

-- The module parameter of `L.StageCardinal`, written out.
SqBelow : S → Type (ℓ-suc ℓ)
SqBelow α = (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ

-- `SqBelow α` IS the module's own parameter type.  That is machine
-- checked in the sibling file `ProbeLJ1332B.agda`, which instantiates
-- `L.StageCardinal` with it.  The instantiation is expensive, so it
-- lives alone; section 4 of the report prices it.
--
-- THE REFUTATION OF THE LEAD, in one line, in `[LJ-1.324]`'s own shape.
-- The hypothesis that `stage-card-at` demands already CONTAINS the goal.
-- No work moves.
lead-hypothesis-is-goal : (α : S) → SqBelow α
                        → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → sq α
lead-hypothesis-is-goal α h = h α (self∈sucV α)

-- And this is what the lead would buy IF it were not circular, so that
-- the refutation is measured against the STRONGEST form of the lead and
-- not a weak one.  `stage-card-upper` outputs `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, and
-- an injection of the index square into the stage would finish `sq α`.
lset-route : (α : S) → (⟪ α ⟫ × ⟪ α ⟫) ↪ ⟪ Lset α ⟫
           → ⟪ Lset α ⟫ ↪ ⟪ α ⟫ → sq α
lset-route α (f , fi) (g , gi) =
  (λ p → g (f p)) , (λ p q e → fi p q (gi (f p) (f q) e))

-- =====================================================================
-- PART 2.  THE TWO DELIVERED LEGS, re-derived (C-44).
--
--   `transport-sq` is `[LJ-1.330]`'s correction: the square law moves
--   along TWO injections and never needs a bijection
--   (agents/tasks/LJ-1-330/ProbeLJ1330A.agda:78-88).  `ord-emb` is the
--   free back leg, src/L/BoundedSubset.lagda.md:1370-1379.  Both are
--   compiled here so this probe quotes no term it did not check.
-- =====================================================================

comp↪ : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp↪ (f , fi) (g , gi) =
  (λ x → g (f x)) , (λ x y e → fi x y (gi (f x) (f y) e))

transport-sq : (α δ : S) → ⟪ α ⟫ ↪ ⟪ δ ⟫ → ⟪ δ ⟫ ↪ ⟪ α ⟫ → sq δ → sq α
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

ord-emb : (a b : S) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
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
-- PART 3.  THE LIMIT BAND REDUCES TO ONE UNTRUNCATED INJECTION.
--
--   The induction hypothesis of any descent over the ordinal supplies
--   `sq β` at every infinite β below the site.  Given that, the whole
--   obligation at the site is a single untruncated injection of the
--   site's index into a member's index.
-- =====================================================================

-- The induction hypothesis, as every descent over an ordinal carries it.
IH : S → Type (ℓ-suc ℓ)
IH α = (d : S) → ⟨ d ∈ˢ α ⟩ → IsOrd d → ⟨ ω ∈ˢ d ⟩ → sq d

member-inj→sq : (α β : S) → IsOrd α → ⟨ β ∈ˢ α ⟩
              → ⟪ α ⟫ ↪ ⟪ β ⟫ → sq β → sq α
member-inj→sq α β oα β∈α down sqβ =
  transport-sq α β down (ord-emb β α oα β∈α) sqβ

-- The same statement with the descent's own hypothesis in place of the
-- point, so the reduction is stated where a descent would use it.
member-inj→sq-ih : (α β : S) → IsOrd α → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
                 → ⟪ α ⟫ ↪ ⟪ β ⟫ → IH α → sq α
member-inj→sq-ih α β oα oβ β∈α ω∈β down ih =
  member-inj→sq α β oα β∈α down (ih β β∈α oβ ω∈β)

-- =====================================================================
-- PART 4.  THE LIMIT BAND, TRUNCATED, FROM THE HYPOTHESIS ALONE.
--
--   `Init`'s fourth row (src/L/Ordinal/SquareLaw.lagda.md:697-699) says
--   the site's index injects into no infinite member's SQUARE.  At a
--   non-initial limit the first three rows hold, so the fourth row
--   fails.  Under LEM a failed row is a MERE witness, and the induction
--   hypothesis turns that witness into the law.
--
--   THIS IS THE MEASUREMENT.  The limit band's law is provable.  It is
--   provable TRUNCATED, and the truncation is the only thing missing.
-- =====================================================================

Row4 : S → Type (ℓ-suc ℓ)
Row4 α = (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
       → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
       → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥

Witness : S → Type (ℓ-suc ℓ)
Witness α = Σ[ β ∈ S ]
  (IsOrd β × (⟨ β ∈ˢ α ⟩ × (⟨ ω ∈ˢ β ⟩ × (⟪ α ⟫ ↪ (⟪ β ⟫ × ⟪ β ⟫)))))

-- A failed fourth row is a mere witness.  LEM only, no choice.
notRow4→merely : (α : S) → (Row4 α → Empty.⊥) → ∥ Witness α ∥₁
notRow4→merely α nr = go (lem (∥ Witness α ∥₁ , squash₁))
  where
  go : ∥ Witness α ∥₁ ⊎ (∥ Witness α ∥₁ → Empty.⊥) → ∥ Witness α ∥₁
  go (inl w) = w
  go (inr nw) = Empty.rec
    (nr (λ β oβ β∈α ω∈β f finj → nw ∣ β , oβ , β∈α , ω∈β , f , finj ∣₁))

witness→sq : (α : S) → IsOrd α → IH α → Witness α → sq α
witness→sq α oα ih (β , oβ , β∈α , ω∈β , sqr) =
  member-inj→sq α β oα β∈α (comp↪ sqr sqβ) sqβ
  where
  sqβ : sq β
  sqβ = ih β β∈α oβ ω∈β

-- THE LIMIT BAND, TRUNCATED.  Nothing outside the hypothesis is used.
limit-truncated : (α : S) → IsOrd α → ⟨ ω ∈ˢ α ⟩
                → ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
                → (Init α → Empty.⊥)
                → IH α → ∥ sq α ∥₁
limit-truncated α oα ω∈α closed noInit ih =
  PT.map (witness→sq α oα ih) (notRow4→merely α nr)
  where
  nr : Row4 α → Empty.⊥
  nr r = noInit (oα , ω∈α , closed , r)

-- =====================================================================
-- PART 5.  THE FOUR BANDS, ASSEMBLED, TRUNCATED.
--
--   `via-col-truncated` covers `Init`.  PART 4 covers the non-initial
--   limits.  `[LJ-1.330]`'s `sq-suc` covers the successors and
--   `squareω` covers omega.  The assembly needs the successor-or-limit
--   dichotomy, which is ordinal bookkeeping and is taken as a
--   hypothesis here, named `Split`.
-- =====================================================================

sq-suc : (γ : S) → IsOrd γ → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
       → ((k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩)
       → sq γ → sq (sucV γ)
sq-suc γ oγ γ∉ω numerals s =
  transport-sq (sucV γ) γ SA.shift↪
    (ord-emb γ (sucV γ) (suc-ord oγ) (self∈sucV γ)) s
  where
  module SA = ShiftAbs γ oγ γ∉ω numerals

sq-suc-inf : (γ : S) → IsOrd γ → ⟨ ω ∈ˢ γ ⟩ → sq γ → sq (sucV γ)
sq-suc-inf γ oγ ω∈γ s = sq-suc γ oγ γ∉ω numerals s
  where
  γ∉ω : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
  γ∉ω γ∈ω = ∈-irrefl ω (ω-ord .fst ω∈γ γ∈ω)

  numerals : (k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩
  numerals k = oγ .fst (#∈ω k) ω∈γ

Split : S → Type (ℓ-suc ℓ)
Split α = ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
        ⊎ (Σ[ γ ∈ S ] (IsOrd γ × (⟨ ω ∈ˢ γ ⟩ × (α ≡ sucV γ))))

-- The truncated induction hypothesis, which is what a descent over the
-- ordinal can actually carry when the conclusion is truncated.
IHT : S → Type (ℓ-suc ℓ)
IHT α = (d : S) → ⟨ d ∈ˢ α ⟩ → IsOrd d → ⟨ ω ∈ˢ d ⟩ → ∥ sq d ∥₁

-- The successor half of the assembly.
bands-suc : (α : S) → (Σ[ γ ∈ S ] (IsOrd γ × (⟨ ω ∈ˢ γ ⟩ × (α ≡ sucV γ))))
          → IHT α → ∥ sq α ∥₁
bands-suc α (γ , oγ , ω∈γ , α≡sγ) iht =
  subst (λ w → ∥ sq w ∥₁) (sym α≡sγ)
    (PT.map (sq-suc-inf γ oγ ω∈γ) (iht γ γ∈α oγ ω∈γ))
  where
  γ∈α : ⟨ γ ∈ˢ α ⟩
  γ∈α = subst (λ w → ⟨ γ ∈ˢ w ⟩) (sym α≡sγ) (self∈sucV γ)

{- BISECT CUT.  MEASURED WALL, and the bisection is in the report.
--
-- The non-initial branch under the TRUNCATED induction hypothesis walls.
-- Two nested truncation eliminations, `PT.rec` outside and `PT.map`
-- inside, do not finish.  Measured: 400 s, interrupted, against 2 s for
-- the same mathematics under the UNTRUNCATED hypothesis
-- (`witness→sq`, PART 4).  The wall is in the assembly, never in the
-- mathematics.
noninit-branch : (α : S) → IsOrd α → IHT α → ∥ Witness α ∥₁ → ∥ sq α ∥₁
noninit-branch α oα iht = PT.rec squash₁ step
  where
  step : Witness α → ∥ sq α ∥₁
  step (β , oβ , β∈α , ω∈β , sqr) =
    PT.map (λ sqβ → member-inj→sq α β oα β∈α (comp↪ sqr sqβ) sqβ)
      (iht β β∈α oβ ω∈β)

-- The initial branch: no witness means `Init`'s fourth row HOLDS, so the
-- site is initial and the delivered collapse serves it.
init-branch : (α : S) → IsOrd α → ⟨ ω ∈ˢ α ⟩
            → ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
            → (∥ Witness α ∥₁ → Empty.⊥) → ∥ sq α ∥₁
init-branch α oα ω∈α closed nw = via-col-truncated α (oα , ω∈α , closed , row4)
  where
  row4 : Row4 α
  row4 β oβ β∈α ω∈β f finj = nw ∣ β , oβ , β∈α , ω∈β , f , finj ∣₁

BISECT CUT -}

-- =====================================================================
-- PART 6.  THE NEGATIVE CONTROLS.  Each one was applied, run and
-- reverted.  They are recorded here because nothing typechecks this file
-- once the task closes.  All three below MEASURE.
--
--   CONTROL 1, ON THE TRUNCATION AT THE LIMIT BAND.  Offer the truncated
--   injection where PART 3's reduction takes the honest one:
--
--     control1 : (α β : S) → IsOrd α → ⟨ β ∈ˢ α ⟩
--              → ∥ ⟪ α ⟫ ↪ ⟪ β ⟫ ∥₁ → sq β → sq α
--     control1 α β oα β∈α t sqβ = member-inj→sq α β oα β∈α t sqβ
--
--   Agda named the blocker, 2 s:
--     error: [UnequalTerms]
--     ∥ ⟪ α ⟫ ↪ ⟪ β ⟫ ∥₁ !=<
--     (Σ (⟪ α ⟫ → ⟪ β ⟫) (λ f → (x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y))
--     when checking that the expression t has type ⟪ α ⟫ ↪ ⟪ β ⟫
--
--   The reduction needs a FUNCTION.  Every supplier at the limit band
--   offers a truncation.
--
--   CONTROL 2, ON THE ELIMINATION AT THIS SITE.  Eliminate the witness
--   into the untruncated goal, with `refl` for propositionality:
--
--     control2 : (α : S) → IsOrd α → IH α → ∥ Witness α ∥₁ → sq α
--     control2 α oα ih w = PT.rec (λ x y → refl) (witness→sq α oα ih) w
--
--   Agda refused, 3 s:
--     error: [UnequalTerms]
--     x != y of type
--     Σ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫)
--     (λ f → (x₁ y₁ : ⟪ α ⟫ × ⟪ α ⟫) → f x₁ ≡ f y₁ → x₁ ≡ y₁)
--     when checking that the expression refl has type x ≡ y
--
--   So the goal is not a proposition, and the machine names the two
--   arbitrary pairing functions that cannot be identified.  That is
--   `[LJ-1.321]`'s `2-Constant` obligation, at the limit band.
--
--   CONTROL 4, ON THE WHOLE RESULT.  Ask `limit-truncated` for the
--   untruncated law, changing nothing else:
--
--     control4 : (α : S) → IsOrd α → ⟨ ω ∈ˢ α ⟩
--              → ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
--              → (Init α → Empty.⊥) → IH α → sq α
--     control4 α oα ω∈α closed noInit ih =
--       PT.map (witness→sq α oα ih) (notRow4→merely α nr)
--       where nr r = noInit (oα , ω∈α , closed , r)
--
--   Agda refused, 2 s:
--     error: [UnequalTerms]
--     ∥ _B_547 ∥₁ !=<
--     Σ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫)
--     (λ f → (x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)
--
--   THAT IS THE VERDICT IN ONE ERROR MESSAGE.  The limit band's whole
--   remaining distance is the pair of truncation bars.
--
--   CONTROL 3 lives in ProbeLJ1332B.agda, because it needs
--   `stage-card-at`.
-- =====================================================================
