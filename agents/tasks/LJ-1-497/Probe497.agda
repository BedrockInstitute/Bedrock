{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.497]  W3 FIRST: the rank at a member.  The obligation is omitted
-- here; this file is the W3 alone.
--
--   W3   `rank-at`, the value `swo-rank` assigns to a member of `a`, as an
--        `S`.  Then the reduction question the brief names: does the
--        well-founded recursion reduce at a slot the formula can name?
--
-- Rebuilds [LJ-1.416]'s rank at the type [LJ-1.490] delivered, and
-- [LJ-1.490]'s `OrdSWO` and `isL-ord`.  Does not import a probe.
-- Nothing lands in src/.  Do not postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-497.Probe497 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( boundingOrd; ∅-ord; mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate; svAt; svAt-in
        ; inDomAt; inDomAt-adequate; extAt; extAt-out; extAt-in-both
        ; sucAtL; prʟ; prʟ-fst )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
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
-- The rank, rebuilt at [LJ-1.416]'s delivered type, as [LJ-1.490] carries
-- it (Probe490.agda:123-157).  ONE change, and it is definitional only:
-- the body of `go` is factored into `step`, so that `boundingOrd`'s own
-- membership at the recursion's own carrier is nameable.  `step a ih` is
-- the very pair [LJ-1.490] writes in `go`'s where clause, so `swo-rank`
-- keeps its delivered type AND its delivered value.
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

  -- [LJ-1.490]'s `go a (acc rs) = bnd .fst , bnd .snd .fst`, with `bnd`
  -- named instead of hidden in a where clause.
  step : (a : A) → ((b : A) → b <∙ a → RankAt b) → RankAt a
  step a ih = bnd .fst , bnd .snd .fst
    where
    bnd = boundingOrd A (λ x → pred a ih x .fst) (λ x → pred a ih x .snd)

  step-mem : (a : A) (ih : (b : A) → b <∙ a → RankAt b) (x : A)
           → ⟨ pred a ih x .fst ∈ step a ih .fst ⟩
  step-mem a ih x =
    boundingOrd A (λ y → pred a ih y .fst) (λ y → pred a ih y .snd)
      .snd .snd x

  go : (a : A) → Acc _<∙_ a → RankAt a
  go a (acc rs) = step a (λ x h → go x (rs x h))

  swo-rank : A → V ℓ
  swo-rank a = go a (wf∙ a) .fst

  swo-rank-ord : (a : A) → IsOrd (swo-rank a)
  swo-rank-ord a = go a (wf∙ a) .snd

  -- THE REDUCTION THE BRIEF ASKS ABOUT.  `pred a ih a` is the recursion's
  -- own carrier read at its own point: trichotomy at `a` against `a` is
  -- never `lt` and never `gt`, so the value is ∅ whatever `tri∙` computes
  -- to.  This is the one place the recursion reduces without an `Acc`.
  pred-self : (a : A) (ih : (b : A) → b <∙ a → RankAt b)
            → pred a ih a .fst ≡ ∅
  pred-self a ih with tri∙ a a
  ... | lt h = Empty.rec (irr∙ a h)
  ... | eq _ = refl
  ... | gt h = Empty.rec (irr∙ a h)

  -- The measurement.  ∅ is a member of EVERY value of the recursion,
  -- because `boundingOrd` is taken over the WHOLE carrier `A` and the
  -- point `a` itself contributes ∅ to that family.
  go-has-∅ : (a : A) (ac : Acc _<∙_ a) → ⟨ ∅ ∈ go a ac .fst ⟩
  go-has-∅ a (acc rs) =
    subst (λ v → ⟨ v ∈ step a ih .fst ⟩) (pred-self a ih) (step-mem a ih a)
    where
    ih : (b : A) → b <∙ a → RankAt b
    ih x h = go x (rs x h)

  swo-rank-has-∅ : (a : A) → ⟨ ∅ ∈ swo-rank a ⟩
  swo-rank-has-∅ a = go-has-∅ a (wf∙ a)

swo-rank : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ
swo-rank w = Rank.swo-rank w

swo-rank-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A) → IsOrd (swo-rank w a)
swo-rank-ord w = Rank.swo-rank-ord w

swo-rank-has-∅ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
               → ⟨ ∅ ∈ swo-rank w a ⟩
swo-rank-has-∅ w = Rank.swo-rank-has-∅ w

-- The wrap the rank does not supply, rebuilt opaque (Probe490.agda:160).
opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- The ordinal well-order, rebuilt at [LJ-1.490]'s OrdSWO
-- (Probe490.agda:165-201).  `oa` supplies `w`; the set `Q` does not.
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
-- W3.  `rank-at`: the value `swo-rank` assigns to a member of `a`, as an
-- `S`.  The brief's obligation is omitted from this file.
--
-- NOTE the telescope.  `swo-rank` wants an `SWO`, and the only delivered
-- route to one at `a` is `OrdSWO.w (fst a) oa`, which wants
-- `oa : IsOrd (fst a)`.  The brief's obligation names `(Q a z : S)` and
-- no `oa`, so the obligation as written cannot be STATED.  `oa` here is
-- the predecessor's delivered hypothesis (Probe490.agda:211).
-- =====================================================================

rank-at : (a : S) (oa : IsOrd (fst a)) (m : S) → ⟨ fst m ∈ fst a ⟩ → S
rank-at a oa m mx = r , isL-ord r (swo-rank-ord w k)
  where
  w = OrdSWO.w (fst a) oa
  k = fiber (fst a) mx .fst
  r = swo-rank w k

-- The recursion DOES reduce at the slot the formula can name, and the
-- value it reduces to is the measurement:  ∅ is a member of the rank of
-- EVERY member of `a`.  So `swo-rank` never takes the value ∅.
rank-at-has-∅ : (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
              → ⟨ ∅ ∈ fst (rank-at a oa m mx) ⟩
rank-at-has-∅ a oa m mx =
  swo-rank-has-∅ (OrdSWO.w (fst a) oa) (fiber (fst a) mx .fst)

-- =====================================================================
-- The formula, rebuilt at [LJ-1.490]'s delivered clauses
-- (Probe490.agda:72-103).  ONE change, and it is naming only: the body of
-- `supAt` is split into `supB2`/`supB1`/`supBody`, so that `extAt-out` can
-- be applied at a NAMED φ.  `supAt f r` is the same formula.
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

supB2 : ∀ {n} → Fin n → Formula S (suc (suc (suc n)))
supB2 f =
  appAt (s3 f) (suc zero) zero
  ∧̇ ∃̇ ( sucAtL (suc zero) zero ∧̇ (var (s3 zero) ∈̇ var zero) )

supB1 : ∀ {n} → Fin n → Formula S (suc (suc n))
supB1 f = ∃̇ (supB2 f)

supBody : ∀ {n} → Fin n → Formula S (suc n)
supBody f = ∃̇ (supB1 f)

supAt : ∀ {n} → Fin n → Fin n → Formula S n
supAt f r = extAt r (supBody f)

rankFo : (Q a : S) → Formula S 1
rankFo Q a =
  ∃̇ ( (var zero ≐ con Q)
    ∧̇ ∃̇ ( ∃̇ (
        prAtL (s3 zero) (suc zero) zero
        ∧̇ (var (suc zero) ∈̇ con a)
        ∧̇ ∃̇ ( fnAt zero (s3 zero) (s2 zero)
            ∧̇ assignAt zero (s3 zero)
            ∧̇ supAt zero (suc zero) ) ) ) )

-- =====================================================================
-- THE OBLIGATION, as a type.  No term named rankFo-adequate.
--
-- The brief writes the telescope `(Q a z : S)`.  That telescope cannot be
-- STATED: `swo-rank` wants an `SWO`, and the only delivered route to one
-- at `a` is `OrdSWO.w (fst a) oa` (Probe490.agda:211-213), which wants
-- `oa : IsOrd (fst a)`.  `oa` below is the predecessor's delivered
-- hypothesis, not a hypothesis I chose to close a conjunct.
-- =====================================================================

RankFoAdequate : Type (ℓ-suc ℓ)
RankFoAdequate =
    (Q a : S) (oa : IsOrd (fst a)) (z : S)
  → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (fst z ≡ pr (fst m) (fst (rank-at a oa m mx)))

-- =====================================================================
-- THE FORMULA SIDE, measured.  Env is the one `rankFo`'s innermost body
-- uses:  (f ∷ r ∷ m ∷ q ∷ z ∷ []), five slots, `Formula S 5`.
--
-- `extAt` is a BICONDITIONAL (src/L/Coding/Model.lagda.md:662-664), so
-- `supAt f r` PINS `r` to the union of the successors of f's values.  A
-- pair-free `f` therefore pins `r` to a set with NO member at all.
-- =====================================================================

module Fml (f r m q z : S) where

  γ : S ^ 5
  γ = f ∷ r ∷ m ∷ q ∷ z ∷ []

  -- `fnAt f q m` reads f's domain as the q-predecessors of m.  So a
  -- q-minimal m gives a pair-free f.  This is the link that makes the
  -- hypothesis one about Q, not one about the witness f.
  fn-no-pairs :
      ⟨ γ ⊨ fnAt zero (s3 zero) (s2 zero) ⟩
    → ((y : S) → ⟨ pr (fst y) (fst m) ∈ fst q ⟩ → Empty.⊥)
    → (x v : S) → ⟨ pr (fst x) (fst v) ∈ fst f ⟩ → Empty.⊥
  fn-no-pairs hfn qmin x v hxv = qmin x inq
    where
    indom : ⟨ (x ∷ γ) ⊨ inDomAt (suc zero) zero ⟩
    indom =
      subst ⟨_⟩ (sym (inDomAt-adequate (suc zero) zero (x ∷ γ))) PT.∣ v , hxv ∣₁
    inq : ⟨ pr (fst x) (fst m) ∈ fst q ⟩
    inq =
      subst ⟨_⟩
        (appAt-adequate (suc (s3 zero)) zero (suc (s2 zero)) (x ∷ γ))
        (hfn .snd x .fst indom)

  -- The ext-condition of `supAt` is unsatisfiable at a pair-free f.
  body-absurd :
      ((x v : S) → ⟨ pr (fst x) (fst v) ∈ fst f ⟩ → Empty.⊥)
    → (w : S) → ⟨ (w ∷ γ) ⊨ supBody zero ⟩ → Empty.⊥
  body-absurd nof w hb = PT.rec Empty.isProp⊥ at1 hb
    where
    at2 : (x : S) → Σ[ v ∈ S ] ⟨ (v ∷ x ∷ w ∷ γ) ⊨ supB2 zero ⟩ → Empty.⊥
    at2 x (v , (hp , _)) =
      nof x v
        (subst ⟨_⟩
          (appAt-adequate (s3 zero) (suc zero) zero (v ∷ x ∷ w ∷ γ)) hp)
    at1 : Σ[ x ∈ S ] ⟨ (x ∷ w ∷ γ) ⊨ supB1 zero ⟩ → Empty.⊥
    at1 (x , hx) = PT.rec Empty.isProp⊥ (at2 x) hx

  -- `supAt f r` at a pair-free f: r has no member.
  sup-no-member :
      ((x v : S) → ⟨ pr (fst x) (fst v) ∈ fst f ⟩ → Empty.⊥)
    → ⟨ γ ⊨ supAt zero (suc zero) ⟩
    → (w : S) → ⟨ fst w ∈ fst r ⟩ → Empty.⊥
  sup-no-member nof hsup w hw =
    body-absurd nof w (extAt-out (suc zero) (supBody zero) γ hsup w hw)

-- ∅ as an element of the model, so it can be fed to `sup-no-member`.
∅ˢ : S
∅ˢ = ∅ , isL-ord ∅ ∅-ord

-- =====================================================================
-- THE DIVERGENCE.  The two sides do not correspond, and the slot is the
-- THIRD existential of `rankFo` (`r`), the one `prAtL` puts as the second
-- component of the pair and `supAt` pins.  It is the very slot the range
-- clause reads.
--
-- The formula pins that slot EMPTY at a q-minimal member.  `swo-rank`
-- puts ∅ INSIDE it at every member.  So no term of `RankFoAdequate` can
-- exist over a q-minimal member.
-- =====================================================================

divergence :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
    (f r q z : S)
  → ⟨ Fml.γ f r m q z ⊨ fnAt zero (s3 zero) (s2 zero) ⟩
  → ⟨ Fml.γ f r m q z ⊨ supAt zero (suc zero) ⟩
  → ((y : S) → ⟨ pr (fst y) (fst m) ∈ fst q ⟩ → Empty.⊥)
  → (fst r ≡ fst (rank-at a oa m mx))
  → Empty.⊥
divergence a oa m mx f r q z hfn hsup qmin req =
  Fml.sup-no-member f r m q z
    (Fml.fn-no-pairs f r m q z hfn qmin) hsup ∅ˢ
    (subst (λ v → ⟨ ∅ ∈ v ⟩) (sym req) (rank-at-has-∅ a oa m mx))

-- The q-minimal hypothesis is not vacuous: at q = ∅ every m is q-minimal.
empty-is-minimal : (y m : S) → ⟨ pr (fst y) (fst m) ∈ fst ∅ˢ ⟩ → Empty.⊥
empty-is-minimal y m h =
  ∅-empty (pr (fst y) (fst m))
    (∈∈ₛ {a = pr (fst y) (fst m)} {b = ∅} .fst h)

∉∅ : (x : V ℓ) → ⟨ x ∈ ∅ ⟩ → Empty.⊥
∉∅ x h = ∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h)

-- =====================================================================
-- THE WITNESS.  Take Q := ∅.  Then every member of `a` is Q-minimal, the
-- approximating function is ∅, and the formula's rank slot is ∅.  This
-- is what makes the divergence UNCONDITIONAL: `rankFo ∅ a` is satisfied,
-- and it is satisfied at a pair whose second component is ∅.
-- =====================================================================

module Sat (a m : S) (mx : ⟨ fst m ∈ fst a ⟩) where

  zz : S
  zz = prʟ m ∅ˢ

  γ5 : S ^ 5
  γ5 = ∅ˢ ∷ ∅ˢ ∷ m ∷ ∅ˢ ∷ zz ∷ []

  nof : (x v : S) → ⟨ pr (fst x) (fst v) ∈ fst ∅ˢ ⟩ → Empty.⊥
  nof x v h = ∉∅ (pr (fst x) (fst v)) h

  dom-absurd : (x : S) → ⟨ (x ∷ γ5) ⊨ inDomAt (suc zero) zero ⟩ → Empty.⊥
  dom-absurd x h =
    PT.rec Empty.isProp⊥ (λ { (v , hv) → nof x v hv })
      (subst ⟨_⟩ (inDomAt-adequate (suc zero) zero (x ∷ γ5)) h)

  app-absurd : (x : S)
             → ⟨ (x ∷ γ5) ⊨ appAt (suc (s3 zero)) zero (suc (s2 zero)) ⟩
             → Empty.⊥
  app-absurd x h =
    nof x m
      (subst ⟨_⟩
        (appAt-adequate (suc (s3 zero)) zero (suc (s2 zero)) (x ∷ γ5)) h)

  fn : ⟨ γ5 ⊨ fnAt zero (s3 zero) (s2 zero) ⟩
  fn = svAt-in zero γ5 (λ x y _ p _ → Empty.rec (nof x y p))
     , (λ x → (λ hd → Empty.rec (dom-absurd x hd))
             , (λ ha → Empty.rec (app-absurd x ha)))

  asg : ⟨ γ5 ⊨ assignAt zero (s3 zero) ⟩
  asg x hd = Empty.rec (dom-absurd x hd)

  sup : ⟨ γ5 ⊨ supAt zero (suc zero) ⟩
  sup = extAt-in-both (suc zero) (supBody zero) γ5
          (λ w hw → Empty.rec (∉∅ (fst w) hw))
          (λ w hb → Empty.rec (Fml.body-absurd ∅ˢ ∅ˢ m ∅ˢ zz nof w hb))

  γ4 : S ^ 4
  γ4 = ∅ˢ ∷ m ∷ ∅ˢ ∷ zz ∷ []

  hpr : ⟨ γ4 ⊨ prAtL (s3 zero) (suc zero) zero ⟩
  hpr =
    subst ⟨_⟩ (sym (prAtL-adequate (s3 zero) (suc zero) zero γ4))
      (prʟ-fst m ∅ˢ)

  sat : ⟨ (zz ∷ []) ⊨ rankFo ∅ˢ a ⟩
  sat = PT.∣ ∅ˢ , (refl
      , PT.∣ m , PT.∣ ∅ˢ , (hpr , (mx , PT.∣ ∅ˢ , (fn , (asg , sup)) ∣₁))
        ∣₁ ∣₁) ∣₁

-- =====================================================================
-- THE REFUTATION.  Unconditional, given only that SOME ordinal of L has
-- a member.  `RankFoAdequate` has no term.
-- =====================================================================

no-adequacy :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → RankFoAdequate → Empty.⊥
no-adequacy a oa m mx adq = ∉∅ ∅ (subst (λ v → ⟨ ∅ ∈ v ⟩) (sym second) has∅)
  where
  open Sat a m mx
  got = adq ∅ˢ a oa zz sat
  m'  = got .fst
  mx' = got .snd .fst
  zeq : fst zz ≡ pr (fst m') (fst (rank-at a oa m' mx'))
  zeq = got .snd .snd
  pp  : pr (fst m) ∅ ≡ pr (fst m') (fst (rank-at a oa m' mx'))
  pp  = sym (prʟ-fst m ∅ˢ) ∙ zeq
  second : ∅ ≡ fst (rank-at a oa m' mx')
  second = pr-inj pp .snd
  has∅ : ⟨ ∅ ∈ fst (rank-at a oa m' mx') ⟩
  has∅ = rank-at-has-∅ a oa m' mx'
