{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.622]  PART 4 of 4: the Hartogs construction.  Probe section 8
-- plus the single line that feeds it to the obligation.
-- The pullback argument that no ordinal injects into the sup of all
-- its order types; this is the largest part and the one the brief
-- suspects of carrying the wall.
-- The header is the same eleven-module set as Part 1; Part 3 is
-- imported, and with it Parts 1 and 2, warm, as a single fresh master
-- holds them here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-622.Part4 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55 )
open import L.CantorBernstein {ℓ} lem using ( readL )

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

open import LJ-1-622.Part3 {ℓ} lem using ( NoInjOrd )
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
