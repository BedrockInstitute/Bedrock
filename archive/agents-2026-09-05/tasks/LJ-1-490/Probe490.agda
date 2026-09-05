{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.490]  W3 FIRST: the range clause, the fourth InjCode conjunct, at
-- the bound [LJ-1.486] delivered.  The other three conjuncts and the
-- obligation are omitted here; this file is the W3 alone.
--
--   W3   `from-out`, the reading: a pair in the carve is a pair in the
--        bound, with satisfaction of rankFo.  Then `range-clause`, the
--        fourth conjunct, asks for the SECOND component in the codomain.
--
-- Rebuilds [LJ-1.478]'s carve and [LJ-1.486]'s bound at their delivered
-- types.  Does not import a probe.  The bound's bounding ordinal C is the
-- codomain the range clause takes.  Nothing lands in src/.
-- Do not postulate.  Do not add a hypothesis to close a conjunct.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-490.Probe490 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( boundingOrd; ∅-ord; mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.InjChain {ℓ} lem using ( module PairBound )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; svAt; inDomAt; extAt; sucAtL; prʟ; prʟ-fst )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open hPropStructure 𝒮ᵥ using ( _∈ᵗ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))
  s4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  s4 i = suc (suc (suc (suc i)))
  s5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  s5 i = suc (suc (suc (suc (suc i))))

-- =====================================================================
-- The carve, rebuilt at [LJ-1.478]'s delivered constructors.  bnd stays a
-- parameter of rank-graph; the W3 feeds it the delivered bound.
-- =====================================================================

fnAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
fnAt f Q m =
  svAt f
  ∧̇ ∀̇ ( (inDomAt (suc f) zero ⇒̇ appAt (suc Q) zero (suc m))
      ∧̇ (appAt (suc Q) zero (suc m) ⇒̇ inDomAt (suc f) zero) )

assignAt : ∀ {n} → Fin n → Fin n → Formula S n
assignAt f Q =
  ∀̇ ( inDomAt (suc f) zero
    ⇒̇ ∃̇ ( appAt (s2 f) (suc zero) zero
        ∧̇ extAt zero (
            ∃̇ ( appAt (s4 Q) zero (s3 zero)
              ∧̇ ∃̇ ( appAt (s5 f) (suc zero) zero
                  ∧̇ ∃̇ ( sucAtL (suc zero) zero
                      ∧̇ (var (s3 zero) ∈̇ var zero) ) ) ) ) ) )

supAt : ∀ {n} → Fin n → Fin n → Formula S n
supAt f r =
  extAt r (
    ∃̇ ( ∃̇ ( appAt (s3 f) (suc zero) zero
          ∧̇ ∃̇ ( sucAtL (suc zero) zero
              ∧̇ (var (s3 zero) ∈̇ var zero) ) ) ) )

rankFo : (Q a : S) → Formula S 1
rankFo Q a =
  ∃̇ ( (var zero ≐ con Q)
    ∧̇ ∃̇ ( ∃̇ (
        prAtL (s3 zero) (suc zero) zero
        ∧̇ (var (suc zero) ∈̇ con a)
        ∧̇ ∃̇ ( fnAt zero (s3 zero) (s2 zero)
            ∧̇ assignAt zero (s3 zero)
            ∧̇ supAt zero (suc zero) ) ) ) )

rank-graph :
    (Q a bnd : S)
  → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G)
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ rankFo Q a)))
rank-graph Q a bnd = hasSeparationL bnd (rankFo Q a) .fst

rank-graph-out :
    (Q a bnd z : S)
  → ⟨ z ∈ˢ fst (rank-graph Q a bnd) ⟩
  → ⟨ z ∈ˢ bnd ⟩ × ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
rank-graph-out Q a bnd z h =
  subst ⟨_⟩ (snd (rank-graph Q a bnd) z) h

-- =====================================================================
-- The rank, rebuilt at [LJ-1.416]'s delivered type.  swo-rank-mono is not
-- rebuilt: boundingOrd wants the family and IsOrd, not the monotonicity.
-- =====================================================================

module Rank {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w

  RankAt : A → Type (ℓ-suc ℓ)
  RankAt _ = Σ[ ρ ∈ V ℓ ] IsOrd ρ

  predAt : (a b : A)
         → Tri (b <∙ a) (b ≡ a) (a <∙ b)
         → ((x : A) → x <∙ a → RankAt x)
         → RankAt b
  predAt a b (lt h) ih = ih b h
  predAt a b (eq _) _  = ∅ , ∅-ord
  predAt a b (gt _) _  = ∅ , ∅-ord

  pred : (a : A) → ((b : A) → b <∙ a → RankAt b) → (b : A) → RankAt b
  pred a ih b = predAt a b (tri∙ b a) ih

  go : (a : A) → Acc _<∙_ a → RankAt a
  go a (acc rs) = bnd .fst , bnd .snd .fst
    where
    ih : (x : A) → x <∙ a → RankAt x
    ih x h = go x (rs x h)
    bnd = boundingOrd A (λ x → pred a ih x .fst) (λ x → pred a ih x .snd)

  swo-rank : A → V ℓ
  swo-rank a = go a (wf∙ a) .fst

  swo-rank-ord : (a : A) → IsOrd (swo-rank a)
  swo-rank-ord a = go a (wf∙ a) .snd

swo-rank : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ
swo-rank w = Rank.swo-rank w

swo-rank-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A) → IsOrd (swo-rank w a)
swo-rank-ord w = Rank.swo-rank-ord w

-- The wrap PairBound wants and the rank does not supply.  Rebuilt, opaque.
opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- The ordinal well-order, rebuilt at StageCardinal's OrdSWO.  oa supplies w.
module OrdSWO (α : V ℓ) (oα : IsOrd α) where

  _≺_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≺ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺ n) (m ≡ n) (n ≺ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺ n) (m ≡ n) (n ≺ m)
    go (inl h)       = lt h
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt h

  irr₁ : (m : ⟪ α ⟫) → (m ≺ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) h

  trans₁ : (m n k : ⟪ α ⟫) → m ≺ n → n ≺ k → m ≺ k
  trans₁ m n k h h' = ord-inord k .fst h h'

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) n≺m))

  wf₁ : WellFounded _≺_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = record
    { _<∙_   = _≺_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

-- =====================================================================
-- The bound, rebuilt at [LJ-1.486]'s delivered body, with the pieces made
-- public.  `bnd` is the delivered bound, `fst (rank-bound a oa)`; `C` is
-- the bounding ordinal the range clause takes as its codomain.  They share
-- one `boundingOrd` on the rebuilt rank, so C is exactly the ordinal
-- rank-bound seals behind PB.
-- =====================================================================

module Bound (a : S) (oa : IsOrd (fst a)) where
  w = OrdSWO.w (fst a) oa
  pack = boundingOrd ⟪ fst a ⟫ (swo-rank w) (swo-rank-ord w)
  β = pack .fst
  oβ = pack .snd .fst
  C : S
  C = β , isL-ord β oβ
  module PB = PairBound a C
  bnd : S
  bnd = PB.bnd
  below : (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (swo-rank w (fiber (fst a) mx .fst)) ∈ fst bnd ⟩
  below m mx = PB.below m z mx r∈β
    where
    k = fiber (fst a) mx .fst
    r = swo-rank w k
    r∈β : ⟨ r ∈ β ⟩
    r∈β = pack .snd .snd k
    z : S
    z = r , isL-trans {x = β} {y = r} r∈β (snd C)

-- The delivered bound, at [LJ-1.486]'s type.  bnd is fst of this Sigma.
rank-bound :
    (a : S) (oa : IsOrd (fst a))
  → Σ[ bnd ∈ S ]
      ((m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (swo-rank (OrdSWO.w (fst a) oa)
                                 (fiber (fst a) mx .fst))
            ∈ fst bnd ⟩)
rank-bound a oa = Rb.bnd , Rb.below
  where
  module Rb = Bound a oa

-- =====================================================================
-- W3.  The range clause, the fourth InjCode conjunct, at the delivered
-- bound.  The other three conjuncts and the obligation are omitted.
--
-- bnd is the delivered bound, fst (rank-bound a oa).  C is the bounding
-- ordinal of the rank, the codomain the clause wants.  from-out is the
-- reading: a pair in the carve is a pair in the bound, with sat.  The
-- clause wants the SECOND component in C.
-- =====================================================================

module W3 (Q a : S) (oa : IsOrd (fst a)) where

  module B = Bound a oa
  bnd : S
  bnd = B.bnd
  G : S
  G = fst (rank-graph Q a bnd)

  from-out :
      (x y : S)
    → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
    → ⟨ prʟ x y ∈ˢ bnd ⟩ × ⟨ (prʟ x y ∷ []) ⊨ rankFo Q a ⟩
  from-out x y h = rank-graph-out Q a bnd (prʟ x y) h'
    where
    h' : ⟨ prʟ x y ∈ˢ G ⟩
    h' = subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst x y)) h

  -- The fourth conjunct, at the delivered bound.  The codomain is C, the
  -- bounding ordinal of the rank: b is determined by a and oa, not free.
  -- No term here.  The reading from-out supplies in-bnd and sat; the gap
  -- to the second component in C is the adequacy of rankFo to swo-rank,
  -- left by [LJ-1.475].  The failed close is in runs/w3-false-close.out.
  range-clause : Type (ℓ-suc ℓ)
  range-clause =
      (x y : S)
    → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
    → ⟨ fst y ∈ fst B.C ⟩

-- =====================================================================
-- THE OBLIGATION, as a type.  No term named rank-coded.  The bound is the
-- delivered rank-bound; b is free as the brief sketched.  The W3 found the
-- range clause wants b = C (the bounding ordinal), so the telescope changes
-- when the adequacy lands.  D-10: the fourth conjunct has no supplier.
-- =====================================================================

RankCoded : Type (ℓ-suc ℓ)
RankCoded =
    (Q a : S) (oa : IsOrd (fst a)) (b : S)
  → InjCode (fst (rank-graph Q a (fst (rank-bound a oa)))) a b
