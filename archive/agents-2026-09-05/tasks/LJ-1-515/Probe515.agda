{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.515]  The replacement rank, on the re-based order.
--
-- The obligation is `swo-rank′`, section 2.  Section 1 is W3, the
-- recursion alone: it was typechecked with sections 2 to 5 omitted, and
-- that slice is kept at agents/tasks/LJ-1-515/runs/w3-slice.agda.txt.
-- Section 3 answers the question [LJ-1.497]'s refutation demands: the
-- rank is `∅` at a minimal element.  Section 4 puts the generic rank at
-- the re-based ordinal order, which is the order the counting leg has.
--
-- THE PADDING IS DELETED.  [LJ-1.490]'s `predAt` and `pred`
-- (agents/tasks/LJ-1-490/Probe490.agda:129-138) do not appear here and no
-- term replaces them.  They exist only to pad the family over the whole of
-- `A`, and [LJ-1.513] ruled they go with it
-- (agents/tasks/LJ-1-513/lj-1.513-report.md:288-290).
--
-- The adequacy is NOT attempted and `rankFo` is NOT touched: AD12 gives
-- this brief one obligation, and [LJ-1.497] measured that the adequacy
-- needs a second hypothesis this task does not supply
-- (agents/tasks/LJ-1-497/lj-1.497-report.md:211).
--
-- Rebuilds [LJ-1.513]'s `OrdSWO∈ₛ` in section 4.  Does not import a probe.
-- Nothing lands in src/.  Does not postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-515.Probe515 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( boundingOrd; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
-- ℓₚ = ℓ.  THE RE-BASED ORDER, [LJ-1.513]'s line
-- (agents/tasks/LJ-1-513/Probe513.agda:32).  [LJ-1.490] took ℓ-suc ℓ
-- (agents/tasks/LJ-1-490/Probe490.agda:34) and that is the level the
-- predecessor index cannot pay.
open import L.WellOrder.Base {ℓ} using ( SWO; Tri; lt; eq; gt )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded; isPropAcc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ᵗ_ )

-- =====================================================================
-- 1.  W3.  THE RECURSION, ON THE RE-BASED ORDER.
--
--     `Rank.go` reads today (agents/tasks/LJ-1-490/Probe490.agda:145):
--
--       bnd = boundingOrd A (λ x → pred a ih x .fst) (λ x → pred a ih x .snd)
--
--     The index is the WHOLE carrier `A`, and `pred` pads it: at an `x`
--     not below `a` it returns `∅ , ∅-ord` (Probe490.agda:134-135).  It
--     must read instead
--
--       bnd = boundingOrd (Pred a) (λ p → ih (p .fst) (p .snd) .fst)
--                                  (λ p → ih (p .fst) (p .snd) .snd)
--
--     with `Pred a = Σ[ x ∈ A ] (x <∙ a)`.  There is nothing to pad, so
--     `ih` is applied at its own proof and nothing else.  That line is
--     [LJ-1.513]'s `viaRankFamily` (Probe513.agda:190-196), which took
--     `ih` as a hypothesis.  Here `ih` is computed.
--
--     `step` is named rather than inlined into `go`'s `where`, because
--     section 3 must state a law about the bounding ordinal `go` forms,
--     and a `where`-bound `bnd` cannot be named from outside `go`.
-- =====================================================================

module Rank′ {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w

  RankAt : A → Type (ℓ-suc ℓ)
  RankAt _ = Σ[ ρ ∈ V ℓ ] IsOrd ρ

  -- The predecessor index.  `A : Type ℓ` and `_<∙_` lands in `Type ℓₚ`
  -- (src/L/WellOrder/Base.lagda.md:103) with `ℓₚ = ℓ`, so this Σ is a
  -- `Type ℓ` and `boundingOrd` accepts it (src/L/Ordinal.lagda.md:154).
  Pred : A → Type ℓ
  Pred a = Σ[ x ∈ A ] (x <∙ a)

  step : (a : A) → ((x : A) → x <∙ a → RankAt x) → RankAt a
  step a ih = bnd .fst , bnd .snd .fst
    where
    bnd = boundingOrd (Pred a) (λ p → ih (p .fst) (p .snd) .fst)
                               (λ p → ih (p .fst) (p .snd) .snd)

  go : (a : A) → Acc _<∙_ a → RankAt a
  go a (acc rs) = step a (λ x h → go x (rs x h))

  swo-rank′ : A → V ℓ
  swo-rank′ a = go a (wf∙ a) .fst

  swo-rank′-ord : (a : A) → IsOrd (swo-rank′ a)
  swo-rank′-ord a = go a (wf∙ a) .snd

-- =====================================================================
-- 2.  THE OBLIGATION.
-- =====================================================================

swo-rank′ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ
swo-rank′ w = Rank′.swo-rank′ w

swo-rank′-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
              → IsOrd (swo-rank′ w a)
swo-rank′-ord w = Rank′.swo-rank′-ord w

-- =====================================================================
-- 3.  IS IT `∅` AT A MINIMAL ELEMENT.
--
--     [LJ-1.497] refuted the adequacy of `rankFo` to `swo-rank` because
--     `swo-rank` is never `∅` (agents/tasks/LJ-1-497/Probe497.agda:435-451).
--     That is a consequence of the padding: the old family runs over the
--     whole of `A`, which contains `a` itself, so `boundingOrd` always
--     unions at least one successor and the result is never empty.
--
--     Removing the padding is exactly what makes the empty case empty.
--     `boundingOrd-empty` is the general fact, and it is stated about
--     `boundingOrd` rather than about the rank, so nothing about the
--     recursion enters it.
-- =====================================================================

boundingOrd-empty :
    (X : Type ℓ) (f : X → V ℓ) (hf : (x : X) → IsOrd (f x))
  → (X → Empty.⊥)
  → boundingOrd X f hf .fst ≡ ∅
boundingOrd-empty X f hf noX =
  extensionality (boundingOrd X f hf .fst) ∅ (out , inn)
  where
  -- `boundingOrd` unions the SUCCESSORS of the family
  -- (src/L/Ordinal.lagda.md:158-161).  This is that family.
  g : X → V ℓ
  g x = sucV (f x)

  out : (u : V ℓ) → ⟨ u ∈ₛ boundingOrd X f hf .fst ⟩ → ⟨ u ∈ₛ ∅ ⟩
  out u h = PT.rec (snd (u ∈ₛ ∅)) k (union-ax (sett X g) u .fst h)
    where
    k : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ sett X g ⟩ × ⟨ u ∈ₛ v ⟩) → ⟨ u ∈ₛ ∅ ⟩
    k (v , v∈ , _) = PT.rec (snd (u ∈ₛ ∅))
      (λ q → Empty.rec (noX (q .fst)))
      (∈∈ₛ {a = v} {b = sett X g} .snd v∈)

  inn : (u : V ℓ) → ⟨ u ∈ₛ ∅ ⟩ → ⟨ u ∈ₛ boundingOrd X f hf .fst ⟩
  inn u h = Empty.rec (∅-empty u h)

module Rank′∅ {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w
  open Rank′ w using ( RankAt; Pred; step; go )

  step-∅ : (a : A) (ih : (x : A) → x <∙ a → RankAt x)
         → ((x : A) → x <∙ a → Empty.⊥)
         → step a ih .fst ≡ ∅
  step-∅ a ih min =
    boundingOrd-empty (Pred a)
      (λ p → ih (p .fst) (p .snd) .fst)
      (λ p → ih (p .fst) (p .snd) .snd)
      (λ p → min (p .fst) (p .snd))

  go-∅ : (a : A) (ac : Acc _<∙_ a)
       → ((x : A) → x <∙ a → Empty.⊥)
       → go a ac .fst ≡ ∅
  go-∅ a (acc rs) min = step-∅ a (λ x h → go x (rs x h)) min

  rank-∅ : (a : A) → ((x : A) → x <∙ a → Empty.⊥) → swo-rank′ w a ≡ ∅
  rank-∅ a min = go-∅ a (wf∙ a) min

  -- THE OTHER HALF, AND IT IS WHAT MAKES THE ANSWER SHARP.  The `∅` law
  -- alone would also hold of the constant `∅`, which is not a rank.  The
  -- bounding property `boundingOrd` carries says the value at a
  -- predecessor is a MEMBER of the value at `a`, so the rank is `∅` at a
  -- minimal element AND NOWHERE ELSE.  This is [LJ-1.490]'s
  -- `swo-rank-mono`, which that probe did not rebuild
  -- (agents/tasks/LJ-1-490/Probe490.agda:119-120).
  step-mem : (a : A) (ih : (x : A) → x <∙ a → RankAt x) (p : Pred a)
           → ih (p .fst) (p .snd) .fst ∈ᵗ step a ih .fst
  step-mem a ih =
    boundingOrd (Pred a) (λ q → ih (q .fst) (q .snd) .fst)
                         (λ q → ih (q .fst) (q .snd) .snd) .snd .snd

  -- Which accessibility proof `go` ran on does not matter: `Acc` is a
  -- proposition (Cubical/Induction/WellFounded.agda:19).
  go-irr : (a : A) (ac ac' : Acc _<∙_ a) → go a ac .fst ≡ go a ac' .fst
  go-irr a ac ac' = cong (λ c → go a c .fst) (isPropAcc a ac ac')

  go-mem : (a : A) (ac : Acc _<∙_ a) (x : A) → x <∙ a
         → swo-rank′ w x ∈ᵗ go a ac .fst
  go-mem a (acc rs) x h =
    subst (λ ρ → ρ ∈ᵗ step a ih .fst)
          (go-irr x (rs x h) (wf∙ x))
          (step-mem a ih (x , h))
    where
    ih : (y : A) → y <∙ a → RankAt y
    ih y k = go y (rs y k)

  rank-mem : (a x : A) → x <∙ a → swo-rank′ w x ∈ᵗ swo-rank′ w a
  rank-mem a x h = go-mem a (wf∙ a) x h

  -- and so the rank is NOT `∅` wherever a predecessor exists.
  rank-∅-only : (a x : A) → x <∙ a → swo-rank′ w a ≡ ∅ → Empty.⊥
  rank-∅-only a x h e =
    ∅-empty (swo-rank′ w x)
      (∈∈ₛ {a = swo-rank′ w x} {b = ∅} .fst
        (subst (λ v → swo-rank′ w x ∈ᵗ v) e (rank-mem a x h)))

-- THE PROPERTY THE REFUTATION DEMANDS, at the type [LJ-1.513] named
-- (agents/tasks/LJ-1-513/lj-1.513-report.md:304-306).
swo-rank′-∅ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
            → ((x : A) → SWO._<∙_ w x a → Empty.⊥)
            → swo-rank′ w a ≡ ∅
swo-rank′-∅ w = Rank′∅.rank-∅ w

-- THE CONVERSE, so that `∅` at a minimal element is not `∅` everywhere.
swo-rank′-mem : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a x : A)
              → SWO._<∙_ w x a → swo-rank′ w x ∈ᵗ swo-rank′ w a
swo-rank′-mem w = Rank′∅.rank-mem w

swo-rank′-∅-only : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a x : A)
                 → SWO._<∙_ w x a → swo-rank′ w a ≡ ∅ → Empty.⊥
swo-rank′-∅-only w = Rank′∅.rank-∅-only w

-- =====================================================================
-- 4.  AT THE RE-BASED ORDINAL ORDER.
--
--     Sections 1 to 3 are generic in `w`, which is clause W2.  This
--     section instantiates them at the one order the counting leg has,
--     rebuilt from [LJ-1.513] (agents/tasks/LJ-1-513/Probe513.agda:113-155).
--     It shows two things and no more: that the replacement rank applies
--     where `swo-rank` applied (agents/tasks/LJ-1-490/Probe490.agda:213),
--     and that the `∅` law is NOT VACUOUS there, because the ∈-least
--     member of an ordinal is a minimal element of the re-based order.
-- =====================================================================

module OrdSWO∈ₛ (α : V ℓ) (oα : IsOrd α) where

  _≺ₛ_ : ⟪ α ⟫ → ⟪ α ⟫ → Type ℓ
  m ≺ₛ n = ⟨ ⟪ α ⟫↪ m ∈ₛ ⟪ α ⟫↪ n ⟩

  to∈ : {m n : ⟪ α ⟫} → m ≺ₛ n → ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n
  to∈ {m} {n} = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = ⟪ α ⟫↪ n} .snd

  fr∈ : {m n : ⟪ α ⟫} → ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n → m ≺ₛ n
  fr∈ {m} {n} = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = ⟪ α ⟫↪ n} .fst

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺ₛ n) (m ≡ n) (n ≺ₛ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺ₛ n) (m ≡ n) (n ≺ₛ m)
    go (inl h)       = lt (fr∈ h)
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt (fr∈ h)

  irr₁ : (m : ⟪ α ⟫) → (m ≺ₛ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) (to∈ h)

  trans₁ : (m n k : ⟪ α ⟫) → m ≺ₛ n → n ≺ₛ k → m ≺ₛ k
  trans₁ m n k h h' = fr∈ (ord-inord k .fst (to∈ h) (to∈ h'))

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺ₛ_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) (to∈ n≺m)))

  wf₁ : WellFounded _≺ₛ_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = record
    { _<∙_   = _≺ₛ_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

module AtOrd (α : V ℓ) (oα : IsOrd α) where

  open OrdSWO∈ₛ α oα using ( _≺ₛ_; w )

  -- The rank at the site.  `[LJ-1.490]`'s `Bound.pack`
  -- (agents/tasks/LJ-1-490/Probe490.agda:213) is this line with
  -- `swo-rank` in place of `swo-rank′`.  The bound itself is NOT rebuilt:
  -- that is [LJ-1.513]'s item 3 and not this task.
  pack : Σ[ β ∈ V ℓ ] (IsOrd β × ((m : ⟪ α ⟫) → swo-rank′ w m ∈ᵗ β))
  pack = boundingOrd ⟪ α ⟫ (swo-rank′ w) (swo-rank′-ord w)

  -- THE `∅` LAW IS NOT VACUOUS HERE.  Nothing is a member of `∅`, so an
  -- index of `∅` in `α` has no predecessor in the re-based order.
  ∅-min : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ≡ ∅ → (x : ⟪ α ⟫) → x ≺ₛ m → Empty.⊥
  ∅-min m e x h = ∅-empty (⟪ α ⟫↪ x) (subst (λ v → ⟨ ⟪ α ⟫↪ x ∈ₛ v ⟩) e h)

  -- and there the replacement rank IS `∅`, which is what [LJ-1.497]
  -- refuted of `swo-rank`.
  rank-at-∅ : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ≡ ∅ → swo-rank′ w m ≡ ∅
  rank-at-∅ m e = swo-rank′-∅ w m (∅-min m e)
