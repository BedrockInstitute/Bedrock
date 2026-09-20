{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 module M1 (Track A): the host structural poset layer.
--
-- Zero hypotheses. This module takes no ZFStructure, no model, no set
-- existence, and no impredicativity. LEM appears exactly once, as an explicit
-- first argument of no-host-generic, and nowhere else. Nothing here is a
-- module parameter except the universe level.
--
-- Notation rules inherited from K2 section 1.0 and respected throughout:
--
--  1. The cubical powerset membership renamed by Base.Prelude:178-179 never
--     appears anywhere below, not even in type position. It is Type-valued
--     (Cubical/Foundations/Powerset.agda:15-16, x ∈ A = ⟨ A x ⟩) while the
--     algebra's connectives are monomorphic on Ω (Base/Truth.lagda.md:69,72).
--     Host subsets of conditions are read through the marked projection
--     _∈ᴾ_ below, and ⟨ _ ⟩ is applied where a type is wanted.
--
--  2. Every negation is spelled _ ⇒ ⊥ with the algebra's own bottom. The
--     algebra's ⊥ is ⊥* , isProp⊥* (Base/Truth.lagda.md:126) whereas its ¬_
--     is the library's on the unlifted bottom (:128). ¬_ is in scope here
--     because the record is opened wholesale, and it is never used.
--     Consequently this module never needs CardinalBridge.¬-as-⇒⊥, which it
--     could not import anyway: CardinalBridge is parameterized by a
--     ZFStructure (CardinalBridge.agda:23) and Track A takes no structure.
--
--  3. Compatibility used inside any ⋀ or ⋁ is the truncated ⋁-form. The
--     untruncated Σ-form ships beside it under the separate name
--     compatibleData, with the one-way map `witness` into the truncation.
--
-- The order convention: p ≼ q reads "p refines q", equivalently "p is
-- stronger than q". Bell states it in exactly those words at printed p. 55
-- (bell-2005-boolean-valued-models.fulltext.md:3425-3426) and his Cohen poset
-- is ordered by reverse inclusion (:3551).
--
-- Antisymmetry, a largest element, separativity and atomlessness are all
-- additional data and never fields, following
-- dev/literature/forcing-geology-design-2026-09.md:163.

open import Base.Prelude
open import Base.Truth

module ForcingNotion {ℓ : Level} where

open import Base.Classical using ( LEM )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- The record
--------------------------------------------------------------------------------

-- A forcing notion is a set of conditions with an Ω-valued preorder that is
-- reflexive and transitive, and which is merely inhabited. Nothing else. The
-- order is Ω-valued rather than Type-valued so that it can be fed directly to
-- ⋀ and ⋁ without a truncation step, and so that the later coded reading of
-- the same relation has the same shape.

record ForcingNotion : Type (ℓ-suc ℓ) where
  field
    Cond     : Type ℓ
    isSetC   : isSet Cond
    _≼_      : Cond → Cond → Ω
    ≼-refl   : (p : Cond) → ⟨ p ≼ p ⟩
    ≼-trans  : {p q r : Cond} → ⟨ p ≼ q ⟩ → ⟨ q ≼ r ⟩ → ⟨ p ≼ r ⟩
    nonempty : ∥ Cond ∥₁

  infix 20 _≼_

--------------------------------------------------------------------------------
-- The structural vocabulary over one forcing notion
--------------------------------------------------------------------------------

module Structure (𝔓 : ForcingNotion) where

  -- Re-exported so that a downstream module needs only `open Structure 𝔓`.
  open ForcingNotion 𝔓 public

  -- A host subset of conditions is an Ω-valued predicate, which is large:
  -- Ω = hProp ℓ lives in Type (ℓ-suc ℓ). Every statement quantifying over Sub
  -- is therefore large, and that is exactly what separates hostGeneric below
  -- from the small internal genericity of M7.

  Sub : Type (ℓ-suc ℓ)
  Sub = Cond → Ω

  infix 20 _∈ᴾ_
  _∈ᴾ_ : Cond → Sub → Ω
  p ∈ᴾ D = D p

  --------------------------------------------------------------------------
  -- Compatibility, in both of its forms
  --------------------------------------------------------------------------

  -- Two conditions are compatible when some condition refines both. The
  -- truth-value form truncates, because ⋁ is the propositionally truncated
  -- existential; this is the only form that may appear inside ⋀, ⋁ or a
  -- coded formula.

  compatible : Cond → Cond → Ω
  compatible p q = ⋁ Cond (λ r → (r ≼ p) ⊓ (r ≼ q))

  -- The data form, kept separate. It is not an hProp, so it can never be the
  -- value of a formula, but K8's delta-system argument needs the witness.

  compatibleData : Cond → Cond → Type ℓ
  compatibleData p q = Σ[ r ∈ Cond ] (⟨ r ≼ p ⟩ × ⟨ r ≼ q ⟩)

  -- The map goes one way only, and this is the whole content of decision one.

  witness : {p q : Cond} → compatibleData p q → ⟨ compatible p q ⟩
  witness d = ∣ d ∣₁

  incompatible : Cond → Cond → Ω
  incompatible p q = compatible p q ⇒ ⊥

  --------------------------------------------------------------------------
  -- Subsets, closure, density
  --------------------------------------------------------------------------

  infix 20 _⊆ᴾ_
  _⊆ᴾ_ : Sub → Sub → Ω
  D ⊆ᴾ E = ⋀ Cond (λ p → (p ∈ᴾ D) ⇒ (p ∈ᴾ E))

  infix 25 ↓_
  ↓_ : Sub → Sub
  ↓ D = λ q → ⋁ Cond (λ p → (p ∈ᴾ D) ⊓ (q ≼ p))

  -- Bell's O_p, the principal down-set of a single condition
  -- (bell-2005-boolean-valued-models.fulltext.md:3433-3434).

  infix 25 ↓ᶜ_
  ↓ᶜ_ : Cond → Sub
  ↓ᶜ p = λ q → q ≼ p

  dense : Sub → Ω
  dense D = ⋀ Cond (λ q → ⋁ Cond (λ p → (p ∈ᴾ D) ⊓ (p ≼ q)))

  denseBelow : Cond → Sub → Ω
  denseBelow r D = ⋀ Cond (λ q → (q ≼ r) ⇒ ⋁ Cond (λ p → (p ∈ᴾ D) ⊓ (p ≼ q)))

  predense : Sub → Ω
  predense D = ⋀ Cond (λ q → ⋁ Cond (λ p → (p ∈ᴾ D) ⊓ compatible p q))

  -- The equality in an antichain is host path equality packaged as a truth
  -- value by isSetC. That is the only use of isSetC in this module, and it is
  -- why isSetC is a field rather than additional data.

  antichain : Sub → Ω
  antichain A = ⋀ Cond (λ p → ⋀ Cond (λ q →
    ((p ∈ᴾ A) ⊓ ((q ∈ᴾ A) ⊓ compatible p q)) ⇒ ((p ≡ q) , isSetC p q)))

  -- Inhabitedness is primitive here, and the classical "nonzero" is derived
  -- later in the Boolean layer, per section 1.4.

  positive : Sub → Ω
  positive U = ⋁ Cond (λ q → q ∈ᴾ U)

  --------------------------------------------------------------------------
  -- Filters
  --------------------------------------------------------------------------

  -- Bell's M-generic clauses (a) and (b) at fulltext:5684-5685. Note that
  -- `directed` demands the refining condition lie in G, not merely in Cond.
  -- Bell states no inhabitedness clause there; `inhabited` is added here
  -- because K2 needs a filter to be positive before it can be generic, and
  -- because `positive` is the primitive of section 1.4. Bell's clause (c),
  -- genericity itself, is at :5686 and is NOT part of this record: the host
  -- reading of it is hostGeneric below, which is refutable.

  record isFilter (G : Sub) : Type ℓ where
    field
      inhabited : ⟨ positive G ⟩
      upward    : (p q : Cond) → ⟨ p ∈ᴾ G ⟩ → ⟨ p ≼ q ⟩ → ⟨ q ∈ᴾ G ⟩
      directed  : (p q : Cond) → ⟨ p ∈ᴾ G ⟩ → ⟨ q ∈ᴾ G ⟩
                → ⟨ ⋁ Cond (λ r → (r ∈ᴾ G) ⊓ ((r ≼ p) ⊓ (r ≼ q))) ⟩

  --------------------------------------------------------------------------
  -- Derived theorems. All constructive, all hypothesis free.
  --------------------------------------------------------------------------

  compatible-refl : (p : Cond) → ⟨ compatible p p ⟩
  compatible-refl p = ∣ p , ≼-refl p , ≼-refl p ∣₁

  compatible-sym : (p q : Cond) → ⟨ compatible p q ⟩ → ⟨ compatible q p ⟩
  compatible-sym p q = PT.map swap
    where
    swap : compatibleData p q → compatibleData q p
    swap (r , r≼p , r≼q) = r , r≼q , r≼p

  ≼-compatible : (p q : Cond) → ⟨ p ≼ q ⟩ → ⟨ compatible p q ⟩
  ≼-compatible p q p≼q = ∣ p , ≼-refl p , p≼q ∣₁

  -- Compatibility is monotone upward in both arguments: a common refinement
  -- of p and q refines anything p and q refine.

  compatible-mono : {p p' q q' : Cond} → ⟨ p ≼ p' ⟩ → ⟨ q ≼ q' ⟩
                  → ⟨ compatible p q ⟩ → ⟨ compatible p' q' ⟩
  compatible-mono {p} {p'} {q} {q'} p≼p' q≼q' = PT.map step
    where
    step : compatibleData p q → compatibleData p' q'
    step (r , r≼p , r≼q) = r , ≼-trans r≼p p≼p' , ≼-trans r≼q q≼q'

  dense-predense : (D : Sub) → ⟨ dense D ⟩ → ⟨ predense D ⟩
  dense-predense D dns q = PT.map step (dns q)
    where
    step : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ D ⟩ × ⟨ p ≼ q ⟩)
         → Σ[ p ∈ Cond ] (⟨ p ∈ᴾ D ⟩ × ⟨ compatible p q ⟩)
    step (p , hp , p≼q) = p , hp , ≼-compatible p q p≼q

  -- Predensity of D is exactly density of its downward closure. Both
  -- directions are constructive: a common refinement r of some p in D and of
  -- q is itself a member of ↓ D lying below q, and conversely.

  predense-closure : (D : Sub) → ⟨ predense D ⟩ → ⟨ dense (↓ D) ⟩
  predense-closure D pd q = PT.rec PT.isPropPropTrunc step (pd q)
    where
    step : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ D ⟩ × ⟨ compatible p q ⟩)
         → ⟨ ⋁ Cond (λ s → (s ∈ᴾ (↓ D)) ⊓ (s ≼ q)) ⟩
    step (p , hp , cpq) = PT.map inner cpq
      where
      inner : compatibleData p q
            → Σ[ s ∈ Cond ] (⟨ s ∈ᴾ (↓ D) ⟩ × ⟨ s ≼ q ⟩)
      inner (r , r≼p , r≼q) = r , ∣ p , hp , r≼p ∣₁ , r≼q

  closure-predense : (D : Sub) → ⟨ dense (↓ D) ⟩ → ⟨ predense D ⟩
  closure-predense D dns q = PT.rec PT.isPropPropTrunc step (dns q)
    where
    step : Σ[ s ∈ Cond ] (⟨ s ∈ᴾ (↓ D) ⟩ × ⟨ s ≼ q ⟩)
         → ⟨ ⋁ Cond (λ p → (p ∈ᴾ D) ⊓ compatible p q) ⟩
    step (s , hs , s≼q) = PT.map inner hs
      where
      inner : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ D ⟩ × ⟨ s ≼ p ⟩)
            → Σ[ p ∈ Cond ] (⟨ p ∈ᴾ D ⟩ × ⟨ compatible p q ⟩)
      inner (p , hp , s≼p) = p , hp , ∣ s , s≼p , s≼q ∣₁

  dense-mono : (D E : Sub) → ⟨ D ⊆ᴾ E ⟩ → ⟨ dense D ⟩ → ⟨ dense E ⟩
  dense-mono D E sub dns q = PT.map step (dns q)
    where
    step : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ D ⟩ × ⟨ p ≼ q ⟩)
         → Σ[ p ∈ Cond ] (⟨ p ∈ᴾ E ⟩ × ⟨ p ≼ q ⟩)
    step (p , hp , p≼q) = p , sub p hp , p≼q

  denseBelow-dense : (r : Cond) (D : Sub) → ⟨ dense D ⟩ → ⟨ denseBelow r D ⟩
  denseBelow-dense r D dns q _ = dns q

  -- Any two members of a filter are compatible, because the filter supplies a
  -- common refinement that happens to lie in the filter as well.

  filter-compatible : (G : Sub) → isFilter G → (p q : Cond)
                    → ⟨ p ∈ᴾ G ⟩ → ⟨ q ∈ᴾ G ⟩ → ⟨ compatible p q ⟩
  filter-compatible G fil p q hp hq =
    PT.map step (isFilter.directed fil p q hp hq)
    where
    step : Σ[ r ∈ Cond ] (⟨ r ∈ᴾ G ⟩ × (⟨ r ≼ p ⟩ × ⟨ r ≼ q ⟩))
         → compatibleData p q
    step (r , _ , r≼p , r≼q) = r , r≼p , r≼q

  --------------------------------------------------------------------------
  -- Additional data. Never fields.
  --------------------------------------------------------------------------

  Top : Type ℓ
  Top = Σ[ u ∈ Cond ] ((p : Cond) → ⟨ p ≼ u ⟩)

  antisymmetric : Type ℓ
  antisymmetric = (p q : Cond) → ⟨ p ≼ q ⟩ → ⟨ q ≼ p ⟩ → p ≡ q

  -- Bell calls this "refined" (fulltext:3429-3430): whenever q does not
  -- refine p, some refinement of q is incompatible with p.

  separative : Type ℓ
  separative = (p q : Cond) → (⟨ q ≼ p ⟩ → ⟨ ⊥ ⟩)
             → ⟨ ⋁ Cond (λ r → (r ≼ q) ⊓ incompatible r p) ⟩

  atomless : Type ℓ
  atomless = (p : Cond) → ⟨ ⋁ Cond (λ q → ⋁ Cond (λ r →
               (q ≼ p) ⊓ ((r ≼ p) ⊓ incompatible q r))) ⟩

  -- Bell Problem 2.4(i) (fulltext:3538-3539): p and q are separatively equal
  -- when they are compatible with exactly the same conditions.

  separativelyEqual : Cond → Cond → Ω
  separativelyEqual p q = ⋀ Cond (λ r →
    (compatible r p ⇒ compatible r q) ⊓ (compatible r q ⇒ compatible r p))

  --------------------------------------------------------------------------
  -- The measured negative: host genericity is refutable
  --------------------------------------------------------------------------

  -- hostGeneric quantifies over Sub, which is large, so the statement lives
  -- in Type (ℓ-suc ℓ). That level is the type-level tell that this is not the
  -- notion M7 will use: isGeneric there quantifies over coded dense sets and
  -- stays in Type ℓ.

  hostGeneric : Sub → Type (ℓ-suc ℓ)
  hostGeneric G = (D : Sub) → ⟨ dense D ⟩
                → ⟨ ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (p ∈ᴾ D)) ⟩

  -- No filter on an atomless notion meets every dense host subset. The
  -- complement of G is itself a host subset, and on an atomless notion it is
  -- dense: below any q pick an incompatible pair, and at most one of the two
  -- can lie in G, since filter-compatible would otherwise make them
  -- compatible. LEM turns "at most one" into a choice of which one, and that
  -- is the only place LEM is used. G then meets its own complement.
  --
  -- Note that no case split on whether q itself lies in G is needed: the
  -- argument runs below an arbitrary q, because filter-compatible constrains
  -- members of G without reference to q.

  no-host-generic : LEM ℓ → atomless → (G : Sub) → isFilter G
                  → hostGeneric G → ⟨ ⊥ ⟩
  no-host-generic lem atl G fil gen = PT.rec (⊥ .snd) collide (gen out dense-out)
    where
    -- The complement of G, spelled with the algebra's own bottom.
    out : Sub
    out p = (p ∈ᴾ G) ⇒ ⊥

    -- Given an incompatible pair below q, produce a member of out below q.
    -- The decision is made by LEM on the left member of the pair.
    pick : (q a b : Cond) → ⟨ a ≼ q ⟩ → ⟨ b ≼ q ⟩ → ⟨ incompatible a b ⟩
         → ⟨ a ∈ᴾ G ⟩ ⊎ (⟨ a ∈ᴾ G ⟩ → Empty.⊥)
         → ⟨ ⋁ Cond (λ p → (p ∈ᴾ out) ⊓ (p ≼ q)) ⟩
    pick q a b a≼q b≼q inc (inr aout) =
      ∣ a , (λ h → Empty.rec (aout h)) , a≼q ∣₁
    pick q a b a≼q b≼q inc (inl ain) =
      ∣ b , (λ h → inc (filter-compatible G fil a b ain h)) , b≼q ∣₁

    dense-out : ⟨ dense out ⟩
    dense-out q = PT.rec PT.isPropPropTrunc step₁ (atl q)
      where
      step₂ : (a : Cond)
            → Σ[ b ∈ Cond ] (⟨ a ≼ q ⟩ × (⟨ b ≼ q ⟩ × ⟨ incompatible a b ⟩))
            → ⟨ ⋁ Cond (λ p → (p ∈ᴾ out) ⊓ (p ≼ q)) ⟩
      step₂ a (b , a≼q , b≼q , inc) = pick q a b a≼q b≼q inc (lem (a ∈ᴾ G))

      step₁ : Σ[ a ∈ Cond ]
                ⟨ ⋁ Cond (λ b → (a ≼ q) ⊓ ((b ≼ q) ⊓ incompatible a b)) ⟩
            → ⟨ ⋁ Cond (λ p → (p ∈ᴾ out) ⊓ (p ≼ q)) ⟩
      step₁ (a , hb) = PT.rec PT.isPropPropTrunc (step₂ a) hb

    collide : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ G ⟩ × ⟨ p ∈ᴾ out ⟩) → ⟨ ⊥ ⟩
    collide (p , hg , hn) = hn hg
