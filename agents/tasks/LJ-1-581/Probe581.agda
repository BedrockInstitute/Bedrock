{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.581]  An L-set injection code for the pairs of kappa into kappa.
--
-- THE OBLIGATION IS NOT INHABITED, AND THIS FILE MEASURES WHY: THE
-- BRIEF'S TYPE IS FALSE.  No term of this file is named
-- `pairs-into-kappa-coded`.  The stop is
-- agents/tasks/LJ-1-581/review-of-pairs-into-kappa.md.  This file
-- carries NO hole and NO postulate, so every reduction in it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552], [LJ-1.556] and [LJ-1.574]).  Nothing lands
-- in src/.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  W3 IS GO.  The pairs of kappa are an L-set with two
--               projections, and it is [LJ-1.556]'s section 1 object.
--   Section 2.  THE BRIEF'S TYPE, WRITTEN OUT AND NOT INHABITED, and
--               TWO IDENTITY FUNCTIONS showing it IS [LJ-1.556]'s
--               `BriefTarget`, which that task returned NO-GO.
--   Section 3.  THE READBACK.  A code for the pairs of kappa into
--               kappa IS the ambient square injection at kappa.
--   Section 4.  THE SITE.  kappa := 2 is an L-ordinal and an L-cardinal.
--   Section 5.  THE REFUTATION.  The brief's type is FALSE, and so is
--               [LJ-1.556]'s corrected target `SquareStep`.
--   Section 6.  THE CORRECTED TARGET (D-10), carrying the infinity
--               hypothesis that the tree's own laws carry.  NOT
--               inhabited: naming it is the deliverable.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-581.Probe581 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj; #mono; #-inj )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode; _↪_ )
open import L.CantorBernstein {ℓ} lem using ( readL; setPL )
open import L.Coding.Model {ℓ} using ( prʟ-fst )

import LJ-1-556.Probe556 {ℓ} lem as P556

open import Cubical.Data.Nat using ( znots )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- SECTION 1.  W3, AND IT IS GO.
--
--   The slice is agents/tasks/LJ-1-581/runs/W3.agda, run runs/w3-1.out
--   (202.25 s, everything cold) and runs/w3-2.out (1.85 s, own
--   interface deleted, the import warm), exit 0 both, green on the
--   FIRST run.  There is no red predecessor.
--
--   The type is stated at the AMBIENT pair `pr` with both components
--   as INDICES; [LJ-1.556]'s section 1 states its two readings at the
--   L-pair `prʟ`.  The one thing that had to be checked is the bridge
--   `prʟ-fst` (src/L/Coding/Model.lagda.md:329).  It is the same
--   object.
-- =====================================================================

PairsOf : S → Type (ℓ-suc ℓ)
PairsOf κ =
  Σ[ P ∈ S ]
    ( ((m n : ⟪ fst κ ⟫) → ⟨ pr (⟪ fst κ ⟫↪ m) (⟪ fst κ ⟫↪ n) ∈ fst P ⟩)
    × ((z : S) → ⟨ fst z ∈ fst P ⟩
       → Σ[ p ∈ (⟪ fst κ ⟫ × ⟪ fst κ ⟫) ]
           (fst z ≡ pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p)))) )

same-object : (κ : S) → PairsOf κ
same-object κ = Sq.sqL , inward , outward
  where
  module Sq = P556.Square κ

  inward : (m n : ⟪ fst κ ⟫)
         → ⟨ pr (⟪ fst κ ⟫↪ m) (⟪ fst κ ⟫↪ n) ∈ fst Sq.sqL ⟩
  inward m n = subst (λ w → ⟨ w ∈ fst Sq.sqL ⟩)
                 (prʟ-fst (Sq.toκ m) (Sq.toκ n)) (Sq.sqL-in m n)

  outward : (z : S) → ⟨ fst z ∈ fst Sq.sqL ⟩
          → Σ[ p ∈ (⟪ fst κ ⟫ × ⟪ fst κ ⟫) ]
              (fst z ≡ pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p)))
  outward z h = Sq.sqL-out z h .fst
              , Sq.sqL-out z h .snd
              ∙ prʟ-fst (Sq.toκ (Sq.sqL-out z h .fst .fst))
                        (Sq.toκ (Sq.sqL-out z h .fst .snd))

-- =====================================================================
-- SECTION 2.  THE BRIEF'S TYPE, WRITTEN OUT AND NOT INHABITED.
--
--   `InjCode F a b` (src/L/Cardinal.lagda.md:223) is what a CODED
--   injection means here: four conjuncts, single-valued, domain `a`,
--   injective, values in `b`.  So "an L-set injection CODE from the
--   pairs of kappa into kappa" is `InjCode F (sqL kappa) kappa`, with
--   the domain object delivered by section 1.
--
--   THE BRIEF SAYS "This brief does not re-dispatch that type"
--   (agents/tasks/LJ-1-581/LJ-1.581.md, `## THE OBLIGATION`).  The two
--   identity functions below say it does.  Neither has a proof term:
--   both are `λ x → x`, so the two types are the same type.
-- =====================================================================

Coded : S → Type (ℓ-suc ℓ)
Coded κ = ∥ Σ[ F ∈ S ] InjCode F (P556.Square.sqL κ) κ ∥₁

Obligation : Type (ℓ-suc ℓ)
Obligation = (κ : S) → IsOrd (fst κ) → IsCardinalL κ → Coded κ

obligation-is-556-brieftarget : Obligation → P556.BriefTarget
obligation-is-556-brieftarget x = x

brieftarget-556-is-obligation : P556.BriefTarget → Obligation
brieftarget-556-is-obligation x = x

-- =====================================================================
-- SECTION 3.  THE READBACK.
--
--   A code for the pairs of kappa into kappa IS the ambient square
--   injection at kappa, and the tree already carries every step of the
--   reading: `readL` (src/L/CantorBernstein.lagda.md:33) turns the four
--   conjuncts into an honest injection of the small member types, and
--   section 1's `sqL-in` puts each pair of indices inside the domain.
--
--   This is the direction the tree calls AMBIENT at
--   src/L/Cardinal.lagda.md:46.  Nothing here internalizes anything:
--   it reads a code DOWN, which is the cheap direction.
-- =====================================================================

module Read (κ : S) where

  module Sq = P556.Square κ

  Ix : Type ℓ
  Ix = ⟪ fst κ ⟫ × ⟪ fst κ ⟫

  -- NOT SEALED, AND THE SEAL WAS TRIED AND MEASURED USELESS.  Sealing
  -- these two moved the file from 202.45 s to 178.45 s
  -- (runs/s6-1.out, runs/s6-2.out) and left `ix→mem-inj` at
  -- 173,465 ms of 175,278 ms (runs/price-4.out).  The price was never
  -- here.  P-i is not the law that applies to this term.
  ix→mem : Ix → ⟪ fst Sq.sqL ⟫
  ix→mem (m , n) = fiber (fst Sq.sqL) (Sq.sqL-in m n) .fst

  ix→mem-val : (p : Ix)
             → ⟪ fst Sq.sqL ⟫↪ (ix→mem p)
             ≡ pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p))
  ix→mem-val (m , n) = fiber (fst Sq.sqL) (Sq.sqL-in m n) .snd
                     ∙ prʟ-fst (Sq.toκ m) (Sq.toκ n)

  -- WRITTEN AS AN INTERVAL ABSTRACTION AND NOT AS `ΣPathP`, AND THAT
  -- IS THE WHOLE PRICE OF THIS FILE.  Measured at this site:
  -- `ΣPathP` 160,042 ms, `cong₂ _,_` 161,723 ms, this form below the
  -- profiler's reporting threshold, one profiled run,
  -- agents/tasks/LJ-1-581/runs/bisect-4.out.  [LJ-1.556] writes the
  -- `ΣPathP` form at agents/tasks/LJ-1-556/Probe556.agda:178.
  ix→mem-inj : (p q : Ix) → ix→mem p ≡ ix→mem q → p ≡ q
  ix→mem-inj p q e i = ( ↪-inj {a = fst κ} (fst split) i
                       , ↪-inj {a = fst κ} (snd split) i )
    where
    raw : pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p))
        ≡ pr (⟪ fst κ ⟫↪ (fst q)) (⟪ fst κ ⟫↪ (snd q))
    raw = sym (ix→mem-val p) ∙ cong ⟪ fst Sq.sqL ⟫↪ e ∙ ix→mem-val q

    split : (⟪ fst κ ⟫↪ (fst p) ≡ ⟪ fst κ ⟫↪ (fst q))
          × (⟪ fst κ ⟫↪ (snd p) ≡ ⟪ fst κ ⟫↪ (snd q))
    split = pr-inj raw

  -- THE READING.  A code gives the ambient square injection.
  square-from-code : Σ[ F ∈ S ] InjCode F Sq.sqL κ → (Ix ↪ ⟪ fst κ ⟫)
  square-from-code c = (λ p → f (ix→mem p))
                     , (λ p q e → ix→mem-inj p q (f-inj (ix→mem p) (ix→mem q) e))
    where
    f : ⟪ fst Sq.sqL ⟫ → ⟪ fst κ ⟫
    f = readL Sq.sqL κ c .fst

    f-inj : (x y : ⟪ fst Sq.sqL ⟫) → f x ≡ f y → x ≡ y
    f-inj = readL Sq.sqL κ c .snd

  square-from-coded : Coded κ → ∥ Ix ↪ ⟪ fst κ ⟫ ∥₁
  square-from-coded = PT.map square-from-code

-- =====================================================================
-- SECTION 4.  THE SITE.  kappa := 2.
-- =====================================================================

-- Every member of `# 1` is `# 0`.
mem-one : (x : V ℓ) → ⟨ x ∈ (# 1) ⟩ → x ≡ # 0
mem-one x h = ∈sucV-elim (setIsSet x (# 0)) h
  (λ x∈0 → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = # 0} .fst x∈0)))
  (λ e → e)

-- Every member of `# 2` is `# 0` or `# 1`.
mem-two : (x : V ℓ) → ⟨ x ∈ (# 2) ⟩ → ∥ (x ≡ # 0) ⊎ (x ≡ # 1) ∥₁
mem-two x h = ∈sucV-elim squash₁ h
  (λ x∈1 → ∣ inl (mem-one x x∈1) ∣₁)
  (λ e → ∣ inr e ∣₁)

zero≢one : # 0 ≡ # 1 → Empty.⊥
zero≢one e = znots (#-inj 0 1 e)

-- A member of `# 2` has at most one element.
thin : (δ : S) → ⟨ fst δ ∈ (# 2) ⟩ → (p q : ⟪ fst δ ⟫) → p ≡ q
thin δ h p q = PT.rec (setPL δ p q) go (mem-two (fst δ) h)
  where
  val : (r : ⟪ fst δ ⟫) → ⟨ ⟪ fst δ ⟫↪ r ∈ fst δ ⟩
  val r = member (fst δ) r

  go : (fst δ ≡ # 0) ⊎ (fst δ ≡ # 1) → p ≡ q
  go (inl e) = Empty.rec
    (∅-empty (⟪ fst δ ⟫↪ p)
      (∈∈ₛ {a = ⟪ fst δ ⟫↪ p} {b = # 0} .fst
        (subst (λ w → ⟨ ⟪ fst δ ⟫↪ p ∈ w ⟩) e (val p))))
  go (inr e) = ↪-inj {a = fst δ}
    ( mem-one (⟪ fst δ ⟫↪ p) (subst (λ w → ⟨ ⟪ fst δ ⟫↪ p ∈ w ⟩) e (val p))
    ∙ sym (mem-one (⟪ fst δ ⟫↪ q)
             (subst (λ w → ⟨ ⟪ fst δ ⟫↪ q ∈ w ⟩) e (val q))) )

κ₀ κ₁ κ₂ : S
κ₀ = numeralL 0
κ₁ = numeralL 1
κ₂ = numeralL 2

κ₀-fst : fst κ₀ ≡ # 0
κ₀-fst = numeralL-fst 0

κ₁-fst : fst κ₁ ≡ # 1
κ₁-fst = numeralL-fst 1

κ₂-fst : fst κ₂ ≡ # 2
κ₂-fst = numeralL-fst 2

κ₀-ord : IsOrd (fst κ₀)
κ₀-ord = subst IsOrd (sym κ₀-fst) (numeral-ord 0)

κ₁-ord : IsOrd (fst κ₁)
κ₁-ord = subst IsOrd (sym κ₁-fst) (numeral-ord 1)

κ₂-ord : IsOrd (fst κ₂)
κ₂-ord = subst IsOrd (sym κ₂-fst) (numeral-ord 2)

0∈κ₁ : ⟨ (# 0) ∈ fst κ₁ ⟩
0∈κ₁ = subst (λ w → ⟨ (# 0) ∈ w ⟩) (sym κ₁-fst) (#mono 0 1 (0 , refl))

0∈κ₂ : ⟨ (# 0) ∈ fst κ₂ ⟩
0∈κ₂ = subst (λ w → ⟨ (# 0) ∈ w ⟩) (sym κ₂-fst) (#mono 0 2 (1 , refl))

1∈κ₂ : ⟨ (# 1) ∈ fst κ₂ ⟩
1∈κ₂ = subst (λ w → ⟨ (# 1) ∈ w ⟩) (sym κ₂-fst) (#mono 1 2 (0 , refl))

m₀ m₁ : ⟪ fst κ₂ ⟫
m₀ = fiber (fst κ₂) 0∈κ₂ .fst
m₁ = fiber (fst κ₂) 1∈κ₂ .fst

m₀-val : ⟪ fst κ₂ ⟫↪ m₀ ≡ # 0
m₀-val = fiber (fst κ₂) 0∈κ₂ .snd

m₁-val : ⟪ fst κ₂ ⟫↪ m₁ ≡ # 1
m₁-val = fiber (fst κ₂) 1∈κ₂ .snd

m₀≢m₁ : m₀ ≡ m₁ → Empty.⊥
m₀≢m₁ e = zero≢one (sym m₀-val ∙ cong ⟪ fst κ₂ ⟫↪ e ∙ m₁-val)

-- kappa := 2 has exactly the two elements above.
κ₂-two : (m : ⟪ fst κ₂ ⟫) → ∥ (m ≡ m₀) ⊎ (m ≡ m₁) ∥₁
κ₂-two m = PT.map go
  (mem-two (⟪ fst κ₂ ⟫↪ m)
    (subst (λ w → ⟨ ⟪ fst κ₂ ⟫↪ m ∈ w ⟩) κ₂-fst (member (fst κ₂) m)))
  where
  go : (⟪ fst κ₂ ⟫↪ m ≡ # 0) ⊎ (⟪ fst κ₂ ⟫↪ m ≡ # 1) → (m ≡ m₀) ⊎ (m ≡ m₁)
  go (inl e) = inl (↪-inj {a = fst κ₂} (e ∙ sym m₀-val))
  go (inr e) = inr (↪-inj {a = fst κ₂} (e ∙ sym m₁-val))

-- THE THREE CARDINALS.  Nothing here is an assumption: each is the
-- refusal of a code, read down by `readL` and closed by a member count.
κ₀-card : IsCardinalL κ₀
κ₀-card δ δ∈ = Empty.rec
  (∅-empty (fst δ)
    (∈∈ₛ {a = fst δ} {b = # 0} .fst
      (subst (λ w → ⟨ fst δ ∈ w ⟩) κ₀-fst δ∈)))

κ₁-card : IsCardinalL κ₁
κ₁-card δ δ∈ = PT.rec isProp⊥ step
  where
  δ≡0 : fst δ ≡ # 0
  δ≡0 = mem-one (fst δ) (subst (λ w → ⟨ fst δ ∈ w ⟩) κ₁-fst δ∈)

  e₀ : ⟪ fst κ₁ ⟫
  e₀ = fiber (fst κ₁) 0∈κ₁ .fst

  step : Σ[ F ∈ S ] InjCode F κ₁ δ → Empty.⊥
  step c = ∅-empty (⟪ fst δ ⟫↪ (f e₀))
    (∈∈ₛ {a = ⟪ fst δ ⟫↪ (f e₀)} {b = # 0} .fst
      (subst (λ w → ⟨ ⟪ fst δ ⟫↪ (f e₀) ∈ w ⟩) δ≡0 (member (fst δ) (f e₀))))
    where
    f : ⟪ fst κ₁ ⟫ → ⟪ fst δ ⟫
    f = readL κ₁ δ c .fst

κ₂-card : IsCardinalL κ₂
κ₂-card δ δ∈ = PT.rec isProp⊥ step
  where
  δ∈' : ⟨ fst δ ∈ (# 2) ⟩
  δ∈' = subst (λ w → ⟨ fst δ ∈ w ⟩) κ₂-fst δ∈

  step : Σ[ F ∈ S ] InjCode F κ₂ δ → Empty.⊥
  step c = m₀≢m₁ (readL κ₂ δ c .snd m₀ m₁
                   (thin δ δ∈' (readL κ₂ δ c .fst m₀) (readL κ₂ δ c .fst m₁)))

-- =====================================================================
-- SECTION 5.  THE REFUTATION.
-- =====================================================================

-- Three pairwise distinct things do not fit in two places.
pigeon : {X : Type ℓ} (a b x y z : X)
       → (x ≡ y → Empty.⊥) → (x ≡ z → Empty.⊥) → (y ≡ z → Empty.⊥)
       → ∥ (x ≡ a) ⊎ (x ≡ b) ∥₁ → ∥ (y ≡ a) ⊎ (y ≡ b) ∥₁
       → ∥ (z ≡ a) ⊎ (z ≡ b) ∥₁ → Empty.⊥
pigeon a b x y z x≢y x≢z y≢z hx hy hz =
  PT.rec isProp⊥ (λ px → PT.rec isProp⊥ (λ py → PT.rec isProp⊥
    (λ pz → go px py pz) hz) hy) hx
  where
  go : ((x ≡ a) ⊎ (x ≡ b)) → ((y ≡ a) ⊎ (y ≡ b)) → ((z ≡ a) ⊎ (z ≡ b))
     → Empty.⊥
  go (inl px) (inl py) _         = x≢y (px ∙ sym py)
  go (inl px) (inr py) (inl pz)  = x≢z (px ∙ sym pz)
  go (inl px) (inr py) (inr pz)  = y≢z (py ∙ sym pz)
  go (inr px) (inl py) (inl pz)  = y≢z (py ∙ sym pz)
  go (inr px) (inl py) (inr pz)  = x≢z (px ∙ sym pz)
  go (inr px) (inr py) _         = x≢y (px ∙ sym py)

-- FOUR PAIRS DO NOT INJECT INTO TWO PLACES.  Three of the four are
-- enough, and the third is not needed.
no-square-at-two : (Read.Ix κ₂ ↪ ⟪ fst κ₂ ⟫) → Empty.⊥
no-square-at-two (g , g-inj) =
  pigeon m₀ m₁ (g p₀₀) (g p₀₁) (g p₁₀) d₁ d₂ d₃
    (κ₂-two (g p₀₀)) (κ₂-two (g p₀₁)) (κ₂-two (g p₁₀))
  where
  p₀₀ p₀₁ p₁₀ : Read.Ix κ₂
  p₀₀ = (m₀ , m₀)
  p₀₁ = (m₀ , m₁)
  p₁₀ = (m₁ , m₀)

  d₁ : g p₀₀ ≡ g p₀₁ → Empty.⊥
  d₁ e = m₀≢m₁ (cong snd (g-inj p₀₀ p₀₁ e))

  d₂ : g p₀₀ ≡ g p₁₀ → Empty.⊥
  d₂ e = m₀≢m₁ (cong fst (g-inj p₀₀ p₁₀ e))

  d₃ : g p₀₁ ≡ g p₁₀ → Empty.⊥
  d₃ e = m₀≢m₁ (cong fst (g-inj p₀₁ p₁₀ e))

-- THE BRIEF'S TYPE IS FALSE.
obligation-false : Obligation → Empty.⊥
obligation-false ob = PT.rec isProp⊥
  (λ c → no-square-at-two (Read.square-from-code κ₂ c))
  (ob κ₂ κ₂-ord κ₂-card)

-- AND SO IS [LJ-1.556]'s CORRECTED TARGET.  No code is built below:
-- the induction hypothesis at 2 is supplied by the SAME assumption,
-- used at 0 and at 1 first.
brieftarget-false : P556.BriefTarget → Empty.⊥
brieftarget-false = obligation-false

squarestep-false : P556.SquareStep → Empty.⊥
squarestep-false ss = PT.rec isProp⊥
  (λ c → no-square-at-two (Read.square-from-code κ₂ c))
  (ss κ₂ κ₂-ord κ₂-card ih₂)
  where
  ih₀ : (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ₀ ⟩ → Coded β
  ih₀ β _ β∈ = Empty.rec
    (∅-empty (fst β)
      (∈∈ₛ {a = fst β} {b = # 0} .fst
        (subst (λ w → ⟨ fst β ∈ w ⟩) κ₀-fst β∈)))

  coded₀ : Coded κ₀
  coded₀ = ss κ₀ κ₀-ord κ₀-card ih₀

  ih₁ : (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ₁ ⟩ → Coded β
  ih₁ β _ β∈ = subst Coded (sym β≡κ₀) coded₀
    where
    β≡κ₀ : β ≡ κ₀
    β≡κ₀ = Σ≡Prop (λ x → snd (isL x))
      (mem-one (fst β) (subst (λ w → ⟨ fst β ∈ w ⟩) κ₁-fst β∈) ∙ sym κ₀-fst)

  coded₁ : Coded κ₁
  coded₁ = ss κ₁ κ₁-ord κ₁-card ih₁

  ih₂ : (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ₂ ⟩ → Coded β
  ih₂ β _ β∈ = PT.rec squash₁ go
    (mem-two (fst β) (subst (λ w → ⟨ fst β ∈ w ⟩) κ₂-fst β∈))
    where
    go : (fst β ≡ # 0) ⊎ (fst β ≡ # 1) → Coded β
    go (inl e) = subst Coded
      (sym (Σ≡Prop (λ x → snd (isL x)) (e ∙ sym κ₀-fst))) coded₀
    go (inr e) = subst Coded
      (sym (Σ≡Prop (λ x → snd (isL x)) (e ∙ sym κ₁-fst))) coded₁

-- =====================================================================
-- SECTION 6.  THE CORRECTED TARGET (D-10).
-- =====================================================================

-- The clause the tree's OWN square law carries and both refuted types
-- drop: `Init`'s second conjunct, src/L/Ordinal/SquareLaw.lagda.md:694.
SquareStepInf : Type (ℓ-suc ℓ)
SquareStepInf =
    (κ : S) → IsOrd (fst κ) → ⟨ ω ∈ fst κ ⟩ → IsCardinalL κ
  → ( (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩ → ⟨ ω ∈ fst β ⟩
      → Coded β )
  → Coded κ

-- AND THE COUNTEREXAMPLE ABOVE DOES NOT REACH IT.
two-not-infinite : ⟨ ω ∈ fst κ₂ ⟩ → Empty.⊥
two-not-infinite h = PT.rec isProp⊥ go
  (mem-two ω (subst (λ w → ⟨ ω ∈ w ⟩) κ₂-fst h))
  where
  go : (ω ≡ # 0) ⊎ (ω ≡ # 1) → Empty.⊥
  go (inl e) = ∈-irrefl (# 0) (subst (λ w → ⟨ (# 0) ∈ w ⟩) e (#∈ω 0))
  go (inr e) = ∈-irrefl (# 1) (subst (λ w → ⟨ (# 1) ∈ w ⟩) e (#∈ω 1))
