{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.528]  CardAboveL: SOME ordinal L-cardinal above κ.
--
-- `[LJ-1.526]` delivered `reduction : CardAboveL → SuccCardExists`
-- (agents/tasks/LJ-1-526/Probe526.agda:285-292).  This file attacks the
-- one input that reduction still wants.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-528.Probe528 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; isL; isL-trans; Lset; Lset→isL; isTransV
        ; isPropIsTransV )
open import L.Ordinal {ℓ} using ( ∅-ord; ω-ord; mem-ord; suc-ord; setUnion-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55 )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )

open Devlin55 using ( comp-inj; ord-emb )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; _∈ₛ_; _⊆_; extensionality; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; module SeparationSet; ⋃_; union-ax )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isPropΠ; isProp×; isPropΣ )
open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; module WFI )
open import Cubical.Functions.Embedding
  using ( isEmbedding; injEmbedding; isEmbedding→hasPropFibers
        ; Embedding-into-isSet→isSet )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 0.  THE OBLIGATION, at `[LJ-1.526]`'s own binding
-- (agents/tasks/LJ-1-526/Probe526.agda:178-183).
-- =====================================================================

-- The type, named apart so that the reductions can quantify over it.
-- THE OBLIGATION ITSELF IS THE TERM `CardAboveL` AT THE FOOT OF THIS
-- FILE, and its type is written out there in the brief's own words.
CardAboveLᵀ : Type (ℓ-suc ℓ)
CardAboveLᵀ =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ θ ∈ SL.S ]
       (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

-- =====================================================================
-- SECTION 1.  EVERY ORDINAL IS AN L-ELEMENT, AND IT IS ONE LINE.
--
--   `[LJ-1.526]`'s report lists "the construction must produce an
--   L-ELEMENT θ, so whatever set is collected must be shown
--   constructible" as one of the two things it could not price
--   (agents/tasks/LJ-1-526/lj-1.526-report.md, `## What CardAboveL is`).
--
--   FOR AN ORDINAL THAT DEMAND IS FREE.  `ord∈Lset-suc`
--   (src/L/Ordinal/Stages.lagda.md:434) puts an ordinal at the stage
--   after itself, and `Lset→isL` (src/L/Constructible.lagda.md:395)
--   reads membership of a stage as level-hood.  The pair is already
--   written inside `LeastCardInjL` (src/L/Cardinal.lagda.md:70-74) for
--   ONE ordinal; nothing in the tree names it generally.
-- =====================================================================

ordL : (x : SV.S) → IsOrd x → SL.S
ordL x ox = x , Lset→isL (sucV x) (suc-ord ox) x (ord∈Lset-suc x ox)

-- =====================================================================
-- SECTION 2.  THE BRIDGE, re-derived.  `[LJ-1.526]` built it at
-- agents/tasks/LJ-1-526/Probe526.agda:105-107; three lines, so this
-- file states its own rather than importing a 14 s module.
-- =====================================================================

ambient→internal : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ
ambient→internal κ c δ δ∈κ h =
  PT.rec Empty.isProp⊥ (λ w → c (fst δ) δ∈κ (readL κ δ w)) h

-- =====================================================================
-- SECTION 3.  THE AMBIENT CARDINAL, BY SEPARATION.
--
--   Fix an ordinal `a` and an ordinal `β`.  Separate out of β the
--   members that inject into a.  THE PREDICATE IS ALREADY SMALL:
--   `⟪ x ⟫` and `⟪ a ⟫` both live in `Type ℓ`, so the cubical
--   library's `SeparationSet` takes it with no resizing and no
--   impredicativity parameter.
-- =====================================================================

module Sep (a : SV.S) (β : SV.S) (oβ : IsOrd β) where

  ϕ : SV.S → hProp ℓ
  ϕ x = ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ , squash₁

  open SeparationSet β ϕ using ( SEPAREE; separation-ax )

  θ : SV.S
  θ = SEPAREE

  θ-in : (x : SV.S) → ⟨ x ∈ˢ β ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁ → ⟨ x ∈ˢ θ ⟩
  θ-in x x∈β h =
    ∈∈ₛ {a = x} {b = θ} .snd
      (separation-ax x .snd (∈∈ₛ {a = x} {b = β} .fst x∈β , h))

  θ⊆β : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ⟨ x ∈ˢ β ⟩
  θ⊆β x x∈θ =
    ∈∈ₛ {a = x} {b = β} .snd
      (separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .fst)

  θ-inj : (x : SV.S) → ⟨ x ∈ˢ θ ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁
  θ-inj x x∈θ = separation-ax x .fst (∈∈ₛ {a = x} {b = θ} .fst x∈θ) .snd

  -- θ IS AN ORDINAL.  Its members are members of β, so they are
  -- transitive; and it is transitive itself because a member of a
  -- member of θ embeds into that member (`ord-emb`) and so into a
  -- (`comp-inj`), both delivered at src/L/BoundedSubset.lagda.md.
  θ-ord : IsOrd θ
  θ-ord = trans , (λ x x∈θ → oβ .snd x (θ⊆β x x∈θ))
    where
    trans : isTransV θ
    trans {x} {y} y∈x x∈θ =
      θ-in y (oβ .fst y∈x (θ⊆β x x∈θ))
        (PT.map
          (comp-inj (ord-emb y x (mem-ord {A = β} oβ x (θ⊆β x x∈θ)) y∈x))
          (θ-inj x x∈θ))

  -- a ∈ θ, as soon as a is inside the ambient bound.
  a∈θ : ⟨ a ∈ˢ β ⟩ → ⟨ a ∈ˢ θ ⟩
  a∈θ a∈β = θ-in a a∈β ∣ (λ m → m) , (λ m n e → e) ∣₁

  -- THE CARDINAL CLAUSE, and it is the one place the bound is spent.
  -- If θ is itself a member of β, then an injection of θ into one of
  -- its own members would put θ into θ.
  θ-card : ⟨ θ ∈ˢ β ⟩ → IsCardinal θ
  θ-card θ∈β δ δ∈θ f =
    ∈-irrefl θ (θ-in θ θ∈β (PT.map (comp-inj f) (θ-inj δ δ∈θ)))

  -- AND THE BOUND IS SPENT BY ONE WITNESS: any member of β that does
  -- NOT inject into a forces θ ∈ β through trichotomy.
  θ∈β : (γ : SV.S) → ⟨ γ ∈ˢ β ⟩ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥)
      → ⟨ θ ∈ˢ β ⟩
  θ∈β γ γ∈β noinj = go (ord-tri θ θ-ord β oβ)
    where
    go : Tri θ β → ⟨ θ ∈ˢ β ⟩
    go (inl θ∈β')      = θ∈β'
    go (inr (inl e))   =
      Empty.rec (PT.rec Empty.isProp⊥ noinj
        (θ-inj γ (subst (λ v → ⟨ γ ∈ˢ v ⟩) (sym e) γ∈β)))
    go (inr (inr β∈θ)) = Empty.rec (∈-irrefl β (θ⊆β β β∈θ))

-- =====================================================================
-- SECTION 4.  THE REDUCTION.  `CardAboveL` FROM ONE AMBIENT STATEMENT.
--
--   `NoInjOrd` carries NO constructibility, NO code, NO cardinal
--   predicate and NO leastness: for every ordinal, some ordinal does
--   not inject into it.  That is the Hartogs fact in its weakest form.
-- =====================================================================

NoInjOrd : Type (ℓ-suc ℓ)
NoInjOrd = (x : SV.S) → IsOrd x
         → ∥ Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ x ⟫ → Empty.⊥)) ∥₁

-- An ordinal that does not inject into `a` is automatically ABOVE `a`:
-- the other two legs of trichotomy each hand back an injection.
above : (a γ : SV.S) → IsOrd a → IsOrd γ → (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥)
      → ⟨ a ∈ˢ γ ⟩
above a γ oa oγ noinj = go (ord-tri γ oγ a oa)
  where
  idInj : ⟪ γ ⟫ ↪ ⟪ γ ⟫
  idInj = (λ m → m) , (λ m n e → e)
  go : Tri γ a → ⟨ a ∈ˢ γ ⟩
  go (inl γ∈a)      = Empty.rec (noinj (ord-emb γ a oa γ∈a))
  go (inr (inl e))  =
    Empty.rec (noinj (subst (λ v → ⟪ γ ⟫ ↪ ⟪ v ⟫) e idInj))
  go (inr (inr a∈γ)) = a∈γ

-- THE AMBIENT HALF AT ONE ORDINAL, UNTRUNCATED.  This is the whole
-- construction; everything after it is plumbing.
cardAboveAt : (a : SV.S) → IsOrd a
  → Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥))
  → Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩)
cardAboveAt a oa (γ , oγ , noinj) =
  S.θ , S.θ-ord , S.θ-card θ∈sγ , S.a∈θ a∈sγ
  where
  module S = Sep a (sucV γ) (suc-ord oγ)
  γ∈sγ : ⟨ γ ∈ˢ sucV γ ⟩
  γ∈sγ = self∈sucV γ
  a∈sγ : ⟨ a ∈ˢ sucV γ ⟩
  a∈sγ = suc-ord oγ .fst (above a γ oa oγ noinj) γ∈sγ
  θ∈sγ : ⟨ S.θ ∈ˢ sucV γ ⟩
  θ∈sγ = S.θ∈β γ γ∈sγ noinj

ambientCardAbove : NoInjOrd → (a : SV.S) → IsOrd a
  → ∥ Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁
ambientCardAbove ni a oa = PT.map (cardAboveAt a oa) (ni a oa)

-- THE WHOLE OBLIGATION, GIVEN `NoInjOrd`.  GREEN, NO HOLES.
--
-- NEITHER `IsCardinalL κ` NOR `κ ∉ ω` IS CONSUMED.  Both hypotheses of
-- `CardAboveL` are dead on this route, and the report says so.
noInjOrd→CardAboveLᵀ : NoInjOrd → CardAboveLᵀ
noInjOrd→CardAboveLᵀ ni κ oκ cκ κ∉ω =
  PT.map build (ambientCardAbove ni (fst κ) oκ)
  where
  build : Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ fst κ ∈ˢ θ ⟩)
        → Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
  build (θ , oθ , cθ , κ∈θ) =
    ordL θ oθ , oθ , ambient→internal (ordL θ oθ) cθ , κ∈θ

-- =====================================================================
-- SECTION 5.  W3, AT THE ONE CONCRETE κ = ωʟ.
--
--   The brief's W3 type, and what it reduces to: ONE uncountable
--   ordinal.  Nothing about L survives the reduction.
-- =====================================================================

someCardinalL-above : Type (ℓ-suc ℓ)
someCardinalL-above =
  ∥ Σ[ θ ∈ SL.S ]
     (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst ωʟ ∈ˢ fst θ ⟩) ∥₁

Uncountable : Type (ℓ-suc ℓ)
Uncountable = ∥ Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ ω ⟫ → Empty.⊥)) ∥₁

w3 : Uncountable → someCardinalL-above
w3 u = PT.map (λ z → build (cardAboveAt ω ω-ord z)) u
  where
  build : Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ ω ∈ˢ θ ⟩)
        → Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst ωʟ ∈ˢ fst θ ⟩)
  build (θ , oθ , cθ , ω∈θ) =
    ordL θ oθ , oθ , ambient→internal (ordL θ oθ) cθ , ω∈θ

-- =====================================================================
-- SECTION 6.  THE REDUCTION IS EXACT, NOT A WEAKENING.
--
--   `NoInjOrd` is not a cheaper thing that happens to be enough: it is
--   the ambient half itself, read back.  An ambient cardinal above `a`
--   REFUTES an injection into `a` by its own defining clause, so the
--   two statements imply each other.  A next brief cannot buy the
--   obligation for less by asking for less.
-- =====================================================================

AmbientCardAbove : Type (ℓ-suc ℓ)
AmbientCardAbove = (a : SV.S) → IsOrd a
  → ∥ Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁

forward : NoInjOrd → AmbientCardAbove
forward = ambientCardAbove

backward : AmbientCardAbove → NoInjOrd
backward ca a oa = PT.map build (ca a oa)
  where
  build : Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩)
        → Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥))
  build (θ , oθ , cθ , a∈θ) = θ , oθ , cθ a a∈θ

-- =====================================================================
-- SECTION 7.  THE RESIDUE, STATED AND NOT INHABITED.
--
--   `NoInjOrd` is the Hartogs fact and it is NOT built here.  The
--   report's `## THE ESTIMATE` section prices it and names the port,
--   BEFORE any of that Agda was written; none of it was written.
--   Nothing below is postulated: the type is stated, and the only
--   terms in this file that mention it take it as a hypothesis.
-- =====================================================================

-- =====================================================================
-- SECTION 8.  `NoInjOrd`, BUILT.  THE HARTOGS ORDINAL WITHOUT ORDER
-- TYPES.
--
--   `[LJ-1.94]` built the ambient Hartogs at ω in 1058 lines
--   (archive/dev/LJ-dispatch-index.md:170) through order types: the
--   collapse of a well-order, its uniqueness under isomorphism, and
--   initial segments.  NONE OF THAT IS NEEDED HERE, and the reason is
--   section 6's contradiction shape.
--
--   The classical construction wants `ot w ≡ μ`, which forces
--   uniqueness-under-isomorphism.  THIS ONE WANTS ONLY `μ ⊆ ot w`,
--   because `ot w ∈ μ` already holds by construction and the two
--   together give `ot w ∈ ot w`.  A subset claim needs no order
--   isomorphism, so trichotomy, initial segments and the uniqueness
--   theorem all drop out, and the relation may be an arbitrary
--   TRANSITIVE WELL-FOUNDED one rather than a well-order.
--
--   THE INDEX IS `Bool`-VALUED AND SO IT IS ALREADY SMALL.
--   `⟪ a ⟫ → ⟪ a ⟫ → Bool` lives in `Type ℓ`, so this file needs no
--   small classifier `Ω'`, no `HPropSmallness` and no `Impredicativity`
--   parameter.  `[LJ-1.94]` paid for that classifier
--   (agents/tasks/LJ-1-94/ProbeLJ194A.agda:29); this does not.
-- =====================================================================

module Hartogs (a : SV.S) where

  Rel : Type ℓ
  Rel = ⟪ a ⟫ → ⟪ a ⟫ → Bool

  Holds : Rel → ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ-zero
  Holds R x y = R x y ≡ true

  -- A transitive well-founded relation on ⟪ a ⟫.  NOT a well-order:
  -- no trichotomy, no irreflexivity clause.
  WFR : Type ℓ
  WFR = Σ[ R ∈ Rel ]
          ( ({x y z : ⟪ a ⟫} → Holds R x y → Holds R y z → Holds R x z)
          × WellFounded (λ x y → Holds R x y) )

  module Col (w : WFR) where

    R : Rel
    R = fst w

    _≺_ : ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ-zero
    x ≺ y = Holds R x y

    ≺-trans : {x y z : ⟪ a ⟫} → x ≺ y → y ≺ z → x ≺ z
    ≺-trans = fst (snd w)

    ≺-wf : WellFounded _≺_
    ≺-wf = snd (snd w)

    module W = WFI ≺-wf

    step : (p : ⟪ a ⟫) → (∀ r → r ≺ p → SV.S) → SV.S
    step p rec = sett (Σ[ r ∈ ⟪ a ⟫ ] (r ≺ p)) (λ z → rec (fst z) (snd z))

    opaque
      col : ⟪ a ⟫ → SV.S
      col = W.induction {P = λ _ → SV.S} step

      col-eq : (p : ⟪ a ⟫)
             → col p ≡ sett (Σ[ r ∈ ⟪ a ⟫ ] (r ≺ p)) (λ z → col (fst z))
      col-eq = W.induction-compute step

    col-in : (p r : ⟪ a ⟫) → r ≺ p → ⟨ col r ∈ˢ col p ⟩
    col-in p r rp =
      subst (λ v → ⟨ col r ∈ˢ v ⟩) (sym (col-eq p)) ∣ (r , rp) , refl ∣₁

    col-out : (p : ⟪ a ⟫) (b : SV.S) → ⟨ b ∈ˢ col p ⟩
            → ∥ Σ[ r ∈ ⟪ a ⟫ ] ((r ≺ p) × (col r ≡ b)) ∥₁
    col-out p b b∈ =
      PT.map (λ z → fst (fst z) , snd (fst z) , snd z)
        (subst (λ v → ⟨ b ∈ˢ v ⟩) (col-eq p) b∈)

    col-ord : (p : ⟪ a ⟫) → IsOrd (col p)
    col-ord = W.induction {P = λ p → IsOrd (col p)} ih
      where
      ih : (p : ⟪ a ⟫) → (∀ r → r ≺ p → IsOrd (col r)) → IsOrd (col p)
      ih p rec = tr , mem
        where
        mem : (x : SV.S) → ⟨ x ∈ˢ col p ⟩ → isTransV x
        mem x x∈ = PT.rec (isPropIsTransV x)
          (λ z → subst isTransV (snd (snd z)) (rec (fst z) (fst (snd z)) .fst))
          (col-out p x x∈)
        tr : isTransV (col p)
        tr {x} {y} y∈x x∈col = PT.rec (snd (y ∈ˢ col p)) outer (col-out p x x∈col)
          where
          outer : Σ[ r ∈ ⟪ a ⟫ ] ((r ≺ p) × (col r ≡ x)) → ⟨ y ∈ˢ col p ⟩
          outer (r , rp , e) =
            PT.rec (snd (y ∈ˢ col p)) inner
              (col-out r y (subst (λ v → ⟨ y ∈ˢ v ⟩) (sym e) y∈x))
            where
            inner : Σ[ s ∈ ⟪ a ⟫ ] ((s ≺ r) × (col s ≡ y)) → ⟨ y ∈ˢ col p ⟩
            inner (s , sr , e2) =
              subst (λ v → ⟨ v ∈ˢ col p ⟩) e2 (col-in p s (≺-trans sr rp))

    -- The order type, as a bare image.  No union, no successor.
    ot : SV.S
    ot = sett ⟪ a ⟫ col

    ot-in : (p : ⟪ a ⟫) → ⟨ col p ∈ˢ ot ⟩
    ot-in p = ∣ p , refl ∣₁

    ot-ord : IsOrd ot
    ot-ord = tr , mem
      where
      mem : (x : SV.S) → ⟨ x ∈ˢ ot ⟩ → isTransV x
      mem x x∈ = PT.rec (isPropIsTransV x)
        (λ z → subst isTransV (snd z) (col-ord (fst z) .fst)) x∈
      tr : isTransV ot
      tr {x} {y} y∈x x∈ot = PT.rec (snd (y ∈ˢ ot)) outer x∈ot
        where
        outer : Σ[ p ∈ ⟪ a ⟫ ] (col p ≡ x) → ⟨ y ∈ˢ ot ⟩
        outer (p , e) =
          PT.rec (snd (y ∈ˢ ot))
            (λ z → subst (λ v → ⟨ v ∈ˢ ot ⟩) (snd (snd z)) (ot-in (fst z)))
            (col-out p y (subst (λ v → ⟨ y ∈ˢ v ⟩) (sym e) y∈x))

  -- THE CANDIDATE: the sup of every order type this family reaches.
  μ : SV.S
  μ = ⋃ (sett WFR (λ w → sucV (Col.ot w)))

  μ-ord : IsOrd μ
  μ-ord = setUnion-ord WFR (λ w → sucV (Col.ot w))
            (λ w → suc-ord (Col.ot-ord w))

  ot∈μ : (w : WFR) → ⟨ Col.ot w ∈ˢ μ ⟩
  ot∈μ w = ∈∈ₛ {a = Col.ot w} {b = μ} .snd
    (union-ax (sett WFR (λ v → sucV (Col.ot v))) (Col.ot w) .snd
      ∣ sucV (Col.ot w) , (inSett , inSuc) ∣₁)
    where
    inSett : ⟨ sucV (Col.ot w) ∈ₛ sett WFR (λ v → sucV (Col.ot v)) ⟩
    inSett = ∈∈ₛ {a = sucV (Col.ot w)}
                 {b = sett WFR (λ v → sucV (Col.ot v))} .fst ∣ w , refl ∣₁
    inSuc : ⟨ Col.ot w ∈ₛ sucV (Col.ot w) ⟩
    inSuc = ∈∈ₛ {a = Col.ot w} {b = sucV (Col.ot w)} .fst
              (self∈sucV (Col.ot w))

  -- ⟪ x ⟫ is a set: it embeds into `V ℓ`, which is one.
  isSet⟪⟫ : (x : SV.S) → isSet ⟪ x ⟫
  isSet⟪⟫ x = Embedding-into-isSet→isSet (⟪ x ⟫↪ , isEmb⟪ x ⟫↪) setIsSet

  decB : {A : Type ℓ} → (A ⊎ (A → Empty.⊥)) → Bool
  decB (inl _) = true
  decB (inr _) = false

  lemℓ : LEM ℓ
  lemℓ = lowerLEM lem

  -- =================================================================
  -- Suppose μ DID inject into a.  Pull the membership order on ⟪ μ ⟫
  -- back along the injection, and the pullback is one of the relations
  -- μ was built from.
  -- =================================================================

  module NoInj (f : ⟪ μ ⟫ ↪ ⟪ a ⟫) where

    F : ⟪ μ ⟫ → ⟪ a ⟫
    F = fst f

    F-emb : isEmbedding F
    F-emb = injEmbedding (isSet⟪⟫ a) (λ {x} {y} e → snd f x y e)

    Fib : ⟪ a ⟫ → Type ℓ
    Fib x = Σ[ m ∈ ⟪ μ ⟫ ] (F m ≡ x)

    isPropFib : (x : ⟪ a ⟫) → isProp (Fib x)
    isPropFib = isEmbedding→hasPropFibers F-emb

    PreT : ⟪ a ⟫ → ⟪ a ⟫ → Type ℓ
    PreT x y = Σ[ p ∈ Fib x ] Σ[ q ∈ Fib y ]
                 ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q) ⟩

    isPropPreT : (x y : ⟪ a ⟫) → isProp (PreT x y)
    isPropPreT x y = isPropΣ (isPropFib x) λ p →
                     isPropΣ (isPropFib y) λ q →
                       snd (⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q))

    R : Rel
    R x y = decB (lemℓ (PreT x y , isPropPreT x y))

    R→Pre : (x y : ⟪ a ⟫) → Holds R x y → PreT x y
    R→Pre x y e = go (lemℓ (PreT x y , isPropPreT x y)) e
      where
      go : (d : PreT x y ⊎ (PreT x y → Empty.⊥)) → decB d ≡ true → PreT x y
      go (inl h) _  = h
      go (inr _) e' = Empty.rec (false≢true e')

    Pre→R : (x y : ⟪ a ⟫) → PreT x y → Holds R x y
    Pre→R x y h = go (lemℓ (PreT x y , isPropPreT x y))
      where
      go : (d : PreT x y ⊎ (PreT x y → Empty.⊥)) → decB d ≡ true
      go (inl _) = refl
      go (inr n) = Empty.rec (n h)

    -- Transitivity comes from the members of μ being transitive sets.
    R-trans : {x y z : ⟪ a ⟫} → Holds R x y → Holds R y z → Holds R x z
    R-trans {x} {y} {z} e1 e2 = Pre→R x z (p , r , goal)
      where
      d1 : PreT x y
      d1 = R→Pre x y e1
      d2 : PreT y z
      d2 = R→Pre y z e2
      p  = fst d1
      q  = fst (snd d1)
      q' = fst d2
      r  = fst (snd d2)
      h1' : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst q') ⟩
      h1' = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
              (isPropFib y q q') (snd (snd d1))
      rTr : isTransV (⟪ μ ⟫↪ (fst r))
      rTr = μ-ord .snd (⟪ μ ⟫↪ (fst r)) (member μ (fst r))
      goal : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst r) ⟩
      goal = ∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ (fst r)} .fst
        (rTr (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ (fst q')} .snd h1')
             (∈∈ₛ {a = ⟪ μ ⟫↪ (fst q')} {b = ⟪ μ ⟫↪ (fst r)} .snd (snd (snd d2))))

    -- Well-foundedness is regularity, transported along the injection.
    -- A point outside the image has no predecessor at all.
    wfAux : (v : SV.S) → Acc SV._∈ᵗ_ v → (m : ⟪ μ ⟫) → ⟪ μ ⟫↪ m ≡ v
          → Acc (λ x y → Holds R x y) (F m)
    wfAux v (acc rec) m e = acc go
      where
      go : (r : ⟪ a ⟫) → Holds R r (F m) → Acc (λ x y → Holds R x y) r
      go r rr = subst (Acc (λ x y → Holds R x y)) (snd p)
                  (wfAux (⟪ μ ⟫↪ (fst p)) (rec (⟪ μ ⟫↪ (fst p)) below)
                     (fst p) refl)
        where
        d : PreT r (F m)
        d = R→Pre r (F m) rr
        p = fst d
        q = fst (snd d)
        h : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ m ⟩
        h = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
              (isPropFib (F m) q (m , refl)) (snd (snd d))
        below : ⟪ μ ⟫↪ (fst p) SV.∈ᵗ v
        below = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ˢ t ⟩) e
                  (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ m} .snd h)

    R-wf : WellFounded (λ x y → Holds R x y)
    R-wf x = acc go
      where
      go : (r : ⟪ a ⟫) → Holds R r x → Acc (λ u v → Holds R u v) r
      go r rr = subst (Acc (λ u v → Holds R u v)) (snd p)
                  (wfAux (⟪ μ ⟫↪ (fst p)) (regularityV (⟪ μ ⟫↪ (fst p)))
                     (fst p) refl)
        where
        p = fst (R→Pre r x rr)

    w : WFR
    w = R , R-trans , R-wf

    open Col w using ( col; col-in; col-out; ot; ot-in )

    -- THE ONE INDUCTION.  The collapse of the pullback REPRODUCES the
    -- members of μ.  This is where `[LJ-1.94]` needed the order type
    -- of an ordinal's own membership order plus uniqueness under
    -- isomorphism; here it is one ∈-induction, because the target is a
    -- set equality proved by extensionality and not an order iso.
    key : (v : SV.S) → Acc SV._∈ᵗ_ v → (m : ⟪ μ ⟫) → ⟪ μ ⟫↪ m ≡ v
        → col (F m) ≡ ⟪ μ ⟫↪ m
    key v (acc rec) m e =
      extensionality (col (F m)) (⟪ μ ⟫↪ m) (fwd , bwd)
      where
      fwd : (b : SV.S) → ⟨ b ∈ₛ col (F m) ⟩ → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩
      fwd b b∈ = PT.rec (snd (b ∈ₛ ⟪ μ ⟫↪ m)) go
                   (col-out (F m) b (∈∈ₛ {a = b} {b = col (F m)} .snd b∈))
        where
        go : Σ[ r ∈ ⟪ a ⟫ ] ((Holds R r (F m)) × (col r ≡ b))
           → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩
        go (r , rr , cr) = subst (λ t → ⟨ t ∈ₛ ⟪ μ ⟫↪ m ⟩) (cpr ∙ cr) hh
          where
          d = R→Pre r (F m) rr
          p = fst d
          q = fst (snd d)
          hh : ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ m ⟩
          hh = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ₛ ⟪ μ ⟫↪ (fst t) ⟩)
                 (isPropFib (F m) q (m , refl)) (snd (snd d))
          below : ⟪ μ ⟫↪ (fst p) SV.∈ᵗ v
          below = subst (λ t → ⟨ ⟪ μ ⟫↪ (fst p) ∈ˢ t ⟩) e
                    (∈∈ₛ {a = ⟪ μ ⟫↪ (fst p)} {b = ⟪ μ ⟫↪ m} .snd hh)
          ih : col (F (fst p)) ≡ ⟪ μ ⟫↪ (fst p)
          ih = key (⟪ μ ⟫↪ (fst p)) (rec (⟪ μ ⟫↪ (fst p)) below) (fst p) refl
          cpr : ⟪ μ ⟫↪ (fst p) ≡ col r
          cpr = sym ih ∙ cong col (snd p)

      bwd : (b : SV.S) → ⟨ b ∈ₛ ⟪ μ ⟫↪ m ⟩ → ⟨ b ∈ₛ col (F m) ⟩
      bwd b b∈ = ∈∈ₛ {a = b} {b = col (F m)} .fst
                   (subst (λ t → ⟨ t ∈ˢ col (F m) ⟩) (ihk ∙ ek) inCol)
        where
        b∈ˢ : ⟨ b ∈ˢ ⟪ μ ⟫↪ m ⟩
        b∈ˢ = ∈∈ₛ {a = b} {b = ⟪ μ ⟫↪ m} .snd b∈
        b∈μ : ⟨ b ∈ˢ μ ⟩
        b∈μ = μ-ord .fst b∈ˢ (member μ m)
        fb = fiber μ b∈μ
        k = fst fb
        ek : ⟪ μ ⟫↪ k ≡ b
        ek = snd fb
        k∈m : ⟨ ⟪ μ ⟫↪ k ∈ₛ ⟪ μ ⟫↪ m ⟩
        k∈m = subst (λ t → ⟨ t ∈ₛ ⟪ μ ⟫↪ m ⟩) (sym ek) b∈
        pre : PreT (F k) (F m)
        pre = (k , refl) , ((m , refl) , k∈m)
        inCol : ⟨ col (F k) ∈ˢ col (F m) ⟩
        inCol = col-in (F m) (F k) (Pre→R (F k) (F m) pre)
        below : ⟪ μ ⟫↪ k SV.∈ᵗ v
        below = subst (λ t → ⟨ ⟪ μ ⟫↪ k ∈ˢ t ⟩) e
                  (∈∈ₛ {a = ⟪ μ ⟫↪ k} {b = ⟪ μ ⟫↪ m} .snd k∈m)
        ihk : col (F k) ≡ ⟪ μ ⟫↪ k
        ihk = key (⟪ μ ⟫↪ k) (rec (⟪ μ ⟫↪ k) below) k refl

    key' : (m : ⟪ μ ⟫) → col (F m) ≡ ⟪ μ ⟫↪ m
    key' m = key (⟪ μ ⟫↪ m) (regularityV (⟪ μ ⟫↪ m)) m refl

    -- μ ⊆ ot w.  THE SUBSET IS ALL THE ARGUMENT NEEDS.  Nothing here
    -- claims `ot w ≡ μ`, and that is why no uniqueness theorem appears
    -- in this file.
    μ⊆ot : (b : SV.S) → ⟨ b ∈ˢ μ ⟩ → ⟨ b ∈ˢ ot ⟩
    μ⊆ot b b∈μ =
      subst (λ t → ⟨ t ∈ˢ ot ⟩) (key' (fst fb) ∙ snd fb)
        (ot-in (F (fst fb)))
      where
      fb = fiber μ b∈μ

    -- `ot w ∈ μ` by construction, `μ ⊆ ot w` by the induction.
    absurd : Empty.⊥
    absurd = ∈-irrefl ot (μ⊆ot ot (ot∈μ w))

  -- THE HARTOGS FACT AT `a`.
  noInj : (⟪ μ ⟫ ↪ ⟪ a ⟫) → Empty.⊥
  noInj f = NoInj.absurd f

-- =====================================================================
-- SECTION 9.  THE OBLIGATION, INHABITED.
-- =====================================================================

noInjOrd : NoInjOrd
noInjOrd x ox = ∣ Hartogs.μ x , Hartogs.μ-ord x , Hartogs.noInj x ∣₁

-- THE BRIEF'S OBLIGATION, AT THE BRIEF'S OWN TYPE.
-- GREEN, NO HOLES, NO POSTULATE, NO CHOICE.
CardAboveL :
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ θ ∈ SL.S ]
       (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁
CardAboveL = noInjOrd→CardAboveLᵀ noInjOrd

-- AND W3, AT THE ONE CONCRETE κ = ωʟ.  `ω-card` is `[LJ-1.526]`'s
-- four-line term (agents/tasks/LJ-1-526/Probe526.agda:130-133),
-- re-typed so this file states its own.
ω-card : IsCardinal ω
ω-card δ δ∈ω (f , finj) =
  finite-excl-ω δ (mem-ord {A = ω} ω-ord δ δ∈ω) δ∈ω
    (λ x → f x , f x) (λ x y e → finj x y (cong fst e))

someCardinalL-above-ω : someCardinalL-above
someCardinalL-above-ω =
  CardAboveL ωʟ ω-ord (ambient→internal ωʟ ω-card) (∈-irrefl ω)

-- AND THE UNCOUNTABLE ORDINAL W3 ASKED ABOUT, EXHIBITED.
uncountable : Uncountable
uncountable = ∣ Hartogs.μ ω , Hartogs.μ-ord ω , Hartogs.noInj ω ∣₁

-- =====================================================================
-- SECTION 10.  WHAT THE ROUTE PROVES BEYOND THE OBLIGATION.
-- =====================================================================

-- STRONGER THAN THE OBLIGATION, AND IT COSTS NOTHING.  Neither
-- `IsCardinalL κ` nor `κ ∉ ω` is consumed anywhere on this route:
-- `noInjOrd→CardAboveLᵀ` binds both and uses neither.  So an ordinal
-- L-cardinal sits above EVERY ordinal, cardinal or not, finite or not.
cardAboveAnyOrd : (x : SV.S) → IsOrd x
  → ∥ Σ[ θ ∈ SL.S ]
       (IsOrd (fst θ) × IsCardinalL θ × ⟨ x ∈ˢ fst θ ⟩) ∥₁
cardAboveAnyOrd x ox = PT.map build (ambientCardAbove noInjOrd x ox)
  where
  build : Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ x ∈ˢ θ ⟩)
        → Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ x ∈ˢ fst θ ⟩)
  build (θ , oθ , cθ , x∈θ) =
    ordL θ oθ , oθ , ambient→internal (ordL θ oθ) cθ , x∈θ

-- =====================================================================
-- SECTION 11.  THE CHAIN CLOSES.  `[LJ-1.526]`'s REDUCTION, CONSUMED.
--
--   `CardAboveLᵀ` above was RE-TYPED by hand from
--   agents/tasks/LJ-1-526/Probe526.agda:178-183, so the two could have
--   drifted.  This section imports that probe and feeds this file's
--   term to its `reduction`.  If the two types differed in any detail
--   this would not typecheck.
--
--   THE RESULT IS `[LJ-1.523]`'s ROW B4, GREEN: the successor L-cardinal
--   exists for every infinite ordinal L-cardinal κ.
-- =====================================================================

import LJ-1-526.Probe526
module P526 = LJ-1-526.Probe526 {ℓ} lem

succCardExists : P526.SuccCardExists
succCardExists = P526.reduction CardAboveL
