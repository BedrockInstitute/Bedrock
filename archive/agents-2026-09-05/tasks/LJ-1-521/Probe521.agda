{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.521]  The adequacy of `rankFo`, on the replacement rank.
--
-- The obligation is `rankFo-adequate′`, section 9.  Section 8 is W3: the
-- adequacy at a Q-MINIMAL member of `a`, alone.  That is the site
-- [LJ-1.497] refuted (agents/tasks/LJ-1-497/Probe497.agda:435-451), and it
-- was written first and typechecked alone; that slice is kept at
-- agents/tasks/LJ-1-521/runs/w3-slice.agda.txt.
--
-- REBUILDS, because a probe does not import a probe:
--   * [LJ-1.518]'s `Site` and `ord-reads-Q` (Probe518.agda:84-185), section 2;
--   * [LJ-1.515]'s `OrdSWO∈ₛ` (Probe515.agda:244-286), section 3;
--   * [LJ-1.515]'s `Rank′`, `swo-rank′`, `swo-rank′-ord` and the `∅` laws
--     (Probe515.agda:81-230), sections 4 and 5;
--   * [LJ-1.497]'s `isL-ord` and the formula `rankFo`
--     (Probe497.agda:148-150,225-263), sections 6 and 7.
--
-- NEW HERE, and nothing else is:
--   * section 5.2, the membership characterization of `swo-rank′`.  It is
--     what the extensional argument spends and [LJ-1.515] did not state it.
--   * section 6.1, `rank-at′`, the eleventh input, written out by
--     [LJ-1.518] (agents/tasks/LJ-1-518/lj-1.518-report.md, "ONE INPUT IS
--     NOT DELIVERED").  Five lines, `swo-rank′` where [LJ-1.497]'s
--     `rank-at` (Probe497.agda:203-207) has the refuted `swo-rank`.
--   * sections 8 and 9, the obligation.
--
-- ONE NAMING-ONLY CHANGE to [LJ-1.497]'s formula, and it is the change
-- [LJ-1.497] itself made to `supAt`: the body of `assignAt` is split into
-- `asgσ`/`asgρ`/`asgχ`/`asgψ`, so that `extAt-out` and `extAt-in` can be
-- applied at a NAMED φ.  `assignAt f Q` is the same formula.
--
-- Nothing lands in src/.  Does not postulate.  `swo-rank` is NOT restored.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-521.Probe521 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; ↾-reflects )
open import FOL.Syntax
  using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL )
open import L.Ordinal {ℓ} using ( boundingOrd; mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.WellOrder.Base {ℓ} using ( SWO; Tri; lt; eq; gt )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate; svAt; svAt-out
        ; inDomAt; inDomAt-adequate; extAt; extAt-out; extAt-in
        ; sucAtL; sucAtL-adequate; prʟ; prʟ-fst )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Sigma using ( ΣPathP )
open import Cubical.Foundations.HLevels using ( isPropΣ )
open import Cubical.Foundations.Prelude using ( PathP; isProp→PathP; J )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded
  using ( Acc; acc; WellFounded; isPropAcc )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open hPropStructure 𝒮ᵥ using ( _∈ᵗ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- 1.  SHIFTS.  [LJ-1.497]'s (Probe497.agda:55-63), unchanged.
-- =====================================================================

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))
  s4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  s4 i = suc (suc (suc (suc i)))
  s5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  s5 i = suc (suc (suc (suc (suc i))))

  -- membership transported along both components at once.  [LJ-1.518]'s
  -- (agents/tasks/LJ-1-518/Probe518.agda:67-70).
  ∈-cong : {u u' v v' : V ℓ} → u ≡ u' → v ≡ v'
         → ⟨ u ∈ v ⟩ → ⟨ u' ∈ v' ⟩
  ∈-cong {u} {u'} {v} {v'} pu pv h =
    subst (λ t → ⟨ t ∈ v' ⟩) pu (subst (λ t → ⟨ u ∈ t ⟩) pv h)

-- =====================================================================
-- 2.  THE SITE AND THE HYPOTHESIS.  [LJ-1.518]'s section 1 and section 2
--     rebuilt verbatim (agents/tasks/LJ-1-518/Probe518.agda:84-185).  The
--     level is `ℓ-suc ℓ` and NOT the brief's `ℓ`, for the reason
--     [LJ-1.518] measured and recorded at its own file head: the
--     hypothesis quantifies over `S`.
-- =====================================================================

module Site (a : S) (oa : IsOrd (fst a)) where

  α : V ℓ
  α = fst a

  _≺ₛ_ : ⟪ α ⟫ → ⟪ α ⟫ → Type ℓ
  m ≺ₛ n = ⟨ ⟪ α ⟫↪ m ∈ₛ ⟪ α ⟫↪ n ⟩

  -- `x` is EXPLICIT and that is forced: `fst x` is not a pattern.
  -- Measured by [LJ-1.518] (agents/tasks/LJ-1-518/runs/w3-implicit-meta.out).
  ix : (x : S) → ⟨ fst x ∈ α ⟩ → ⟪ α ⟫
  ix x h = fiber α h .fst

  ix-val : (x : S) (h : ⟨ fst x ∈ α ⟩) → ⟪ α ⟫↪ (ix x h) ≡ fst x
  ix-val x h = fiber α h .snd

  memS : ⟪ α ⟫ → S
  memS m = ⟪ α ⟫↪ m , isL-trans {x = α} {y = ⟪ α ⟫↪ m} (member α m) (snd a)

  memS-mem : (k : ⟪ α ⟫) → ⟨ fst (memS k) ∈ α ⟩
  memS-mem k = member α k

  memS-ix : (k : ⟪ α ⟫) → ix (memS k) (memS-mem k) ≡ k
  memS-ix k = ↪-inj {a = α} (ix-val (memS k) (memS-mem k))

  PairOf : (Q x m : S) → Type (ℓ-suc ℓ)
  PairOf Q x m = ⟨ pr (fst x) (fst m) ∈ fst Q ⟩

  ReadsOut : (Q : S) → Type (ℓ-suc ℓ)
  ReadsOut Q =
      (x m : S) → PairOf Q x m
    → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ] Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma)

  ReadsIn : (Q : S) → Type (ℓ-suc ℓ)
  ReadsIn Q =
      (x m : S) (xa : ⟨ fst x ∈ α ⟩) (ma : ⟨ fst m ∈ α ⟩)
    → ix x xa ≺ₛ ix m ma → PairOf Q x m

  Reads : (Q : S) → Type (ℓ-suc ℓ)
  Reads Q = ReadsOut Q × ReadsIn Q

  isPropReadsOut : (Q x m : S)
    → isProp (Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ]
              Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma))
  isPropReadsOut Q x m =
    isPropΣ (snd (fst x ∈ α)) (λ xa →
    isPropΣ (snd (fst m ∈ α)) (λ ma →
      snd (⟪ α ⟫↪ (ix x xa) ∈ₛ ⟪ α ⟫↪ (ix m ma))))

ord-reads-Q : (Q a : S) → IsOrd (fst a) → Type (ℓ-suc ℓ)
ord-reads-Q Q a oa = Site.Reads a oa Q

-- =====================================================================
-- 3.  THE ORDER.  [LJ-1.515]'s `OrdSWO∈ₛ`
--     (agents/tasks/LJ-1-515/Probe515.agda:244-286), rebuilt.
--     `site-is-swo` below is [LJ-1.518]'s `refl`
--     (agents/tasks/LJ-1-518/Probe518.agda:402-404): the relation the
--     hypothesis is stated at and the relation the rank runs on are ONE
--     relation, definitionally.
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

site-is-swo : (a : S) (oa : IsOrd (fst a))
            → Site._≺ₛ_ a oa ≡ SWO._<∙_ (OrdSWO∈ₛ.w (fst a) oa)
site-is-swo a oa = refl

-- =====================================================================
-- 4.  THE REPLACEMENT RANK.  [LJ-1.515]'s section 1 and section 2
--     (agents/tasks/LJ-1-515/Probe515.agda:81-117), rebuilt.  The padding
--     is NOT restored: the index is `Pred a` and not the whole carrier.
-- =====================================================================

module Rank′ {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w

  RankAt : A → Type (ℓ-suc ℓ)
  RankAt _ = Σ[ ρ ∈ V ℓ ] IsOrd ρ

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
-- 5.  WHAT THE RANK HOLDS.
--
--     5.1 is [LJ-1.515]'s `∅` law (Probe515.agda:134-230), rebuilt.  It
--     is the answer to [LJ-1.497]'s refutation and section 8 spends it.
--
--     5.2 IS NEW.  [LJ-1.515] proved the rank is `∅` at a minimal element
--     and that a predecessor's rank is a MEMBER; it never said what the
--     members of a rank ARE.  The adequacy is an extensional identity
--     between a set the formula pins and a set the recursion forms, so it
--     spends exactly that, in both directions.
-- =====================================================================

boundingOrd-empty :
    (X : Type ℓ) (f : X → V ℓ) (hf : (x : X) → IsOrd (f x))
  → (X → Empty.⊥)
  → boundingOrd X f hf .fst ≡ ∅
boundingOrd-empty X f hf noX =
  extensionality (boundingOrd X f hf .fst) ∅ (out , inn)
  where
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

-- 5.2  `boundingOrd` holds exactly the members of the SUCCESSORS of its
--      family.  Both directions, and neither is in src/: `boundingOrd`
--      exports only the membership of `f x` itself
--      (src/L/Ordinal.lagda.md:155).
bnd-out : (X : Type ℓ) (g : X → V ℓ) (hg : (x : X) → IsOrd (g x)) (u : V ℓ)
        → ⟨ u ∈ₛ boundingOrd X g hg .fst ⟩
        → PT.∥ (Σ[ x ∈ X ] ⟨ u ∈ₛ sucV (g x) ⟩) ∥₁
bnd-out X g hg u h = PT.rec PT.squash₁ atV (union-ax (sett X G) u .fst h)
  where
  G : X → V ℓ
  G x = sucV (g x)
  atV : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ sett X G ⟩ × ⟨ u ∈ₛ v ⟩)
      → PT.∥ (Σ[ x ∈ X ] ⟨ u ∈ₛ sucV (g x) ⟩) ∥₁
  atV (v , (v∈ , u∈)) =
    PT.map (λ q → q .fst , subst (λ t → ⟨ u ∈ₛ t ⟩) (sym (q .snd)) u∈)
      (∈∈ₛ {a = v} {b = sett X G} .snd v∈)

bnd-in : (X : Type ℓ) (g : X → V ℓ) (hg : (x : X) → IsOrd (g x))
         (u : V ℓ) (x : X)
       → ⟨ u ∈ₛ sucV (g x) ⟩ → ⟨ u ∈ₛ boundingOrd X g hg .fst ⟩
bnd-in X g hg u x h =
  union-ax (sett X G) u .snd PT.∣ sucV (g x) , (s∈ , h) ∣₁
  where
  G : X → V ℓ
  G y = sucV (g y)
  s∈ : ⟨ sucV (g x) ∈ₛ sett X G ⟩
  s∈ = ∈∈ₛ {a = sucV (g x)} {b = sett X G} .fst PT.∣ x , refl ∣₁

module Rank′Laws {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w
  open Rank′ w using ( RankAt; Pred; step; go; swo-rank′; swo-rank′-ord )

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

  rank-∅ : (a : A) → ((x : A) → x <∙ a → Empty.⊥) → swo-rank′ a ≡ ∅
  rank-∅ a min = go-∅ a (wf∙ a) min

  -- Which accessibility proof `go` ran on does not matter.
  go-irr : (a : A) (ac ac' : Acc _<∙_ a) → go a ac .fst ≡ go a ac' .fst
  go-irr a ac ac' = cong (λ c → go a c .fst) (isPropAcc a ac ac')

  go-mem-out : (a : A) (ac : Acc _<∙_ a) (u : V ℓ)
             → ⟨ u ∈ₛ go a ac .fst ⟩
             → PT.∥ (Σ[ j ∈ A ] (j <∙ a × ⟨ u ∈ₛ sucV (swo-rank′ j) ⟩)) ∥₁
  go-mem-out a (acc rs) u h =
    PT.map fix (bnd-out (Pred a)
                  (λ p → go (p .fst) (rs (p .fst) (p .snd)) .fst)
                  (λ p → go (p .fst) (rs (p .fst) (p .snd)) .snd) u h)
    where
    fix : Σ[ p ∈ Pred a ] ⟨ u ∈ₛ sucV (go (p .fst) (rs (p .fst) (p .snd)) .fst) ⟩
        → Σ[ j ∈ A ] (j <∙ a × ⟨ u ∈ₛ sucV (swo-rank′ j) ⟩)
    fix (p , hu) = p .fst , (p .snd ,
      subst (λ ρ → ⟨ u ∈ₛ sucV ρ ⟩)
        (go-irr (p .fst) (rs (p .fst) (p .snd)) (wf∙ (p .fst))) hu)

  go-mem-in : (a : A) (ac : Acc _<∙_ a) (u : V ℓ) (j : A) → j <∙ a
            → ⟨ u ∈ₛ sucV (swo-rank′ j) ⟩ → ⟨ u ∈ₛ go a ac .fst ⟩
  go-mem-in a (acc rs) u j hj h =
    bnd-in (Pred a)
      (λ p → go (p .fst) (rs (p .fst) (p .snd)) .fst)
      (λ p → go (p .fst) (rs (p .fst) (p .snd)) .snd) u (j , hj)
      (subst (λ ρ → ⟨ u ∈ₛ sucV ρ ⟩)
        (sym (go-irr j (rs j hj) (wf∙ j))) h)

-- 5.3  THE RANK IS SEALED HERE, AND THE REASON IS MEASURED.
--
--      `swo-rank′` is a well-founded recursion whose `Acc` comes, at the
--      site, from a CONCRETE record (`OrdSWO∈ₛ.w`), so `SWO.wf∙ w k`
--      reduces to `acc₁ k (regularityV …)` and the whole recursion is
--      exposed to the elaborator.  Section 9.1 transports along a path
--      whose family names this term.  MEASURED: unsealed, the file was
--      still running at 571.93 s when the machine's shared watchdog took
--      it (agents/tasks/LJ-1-521/runs/full-try2.out), while everything
--      through section 9's `concl` cost 3.59 s
--      (agents/tasks/LJ-1-521/runs/bisect-top.out).  Sealing this alone
--      cut the unfinished run to 239.41 s
--      (agents/tasks/LJ-1-521/runs/full-try3.out) and did not close it;
--      section 9.1's own change did.
--
--      The five names below are the whole interface: nothing outside this
--      block ever needs the recursion to unfold.

opaque
  swo-rank′ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ
  swo-rank′ w = Rank′.swo-rank′ w

  swo-rank′-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
                → IsOrd (swo-rank′ w a)
  swo-rank′-ord w = Rank′.swo-rank′-ord w

  swo-rank′-∅ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
              → ((x : A) → SWO._<∙_ w x a → Empty.⊥)
              → swo-rank′ w a ≡ ∅
  swo-rank′-∅ w = Rank′Laws.rank-∅ w

  rank-mem-out : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A) (u : V ℓ)
               → ⟨ u ∈ₛ swo-rank′ w a ⟩
               → PT.∥ (Σ[ j ∈ A ]
                        (SWO._<∙_ w j a × ⟨ u ∈ₛ sucV (swo-rank′ w j) ⟩)) ∥₁
  rank-mem-out w a = Rank′Laws.go-mem-out w a (SWO.wf∙ w a)

  rank-mem-in : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A) (u : V ℓ) (j : A)
              → SWO._<∙_ w j a
              → ⟨ u ∈ₛ sucV (swo-rank′ w j) ⟩ → ⟨ u ∈ₛ swo-rank′ w a ⟩
  rank-mem-in w a = Rank′Laws.go-mem-in w a (SWO.wf∙ w a)


-- =====================================================================
-- 6.  THE RANK AS AN ELEMENT OF THE MODEL.
--
--     6.1 IS THE ELEVENTH INPUT.  [LJ-1.518] wrote it out and did not
--     build it.  It is [LJ-1.497]'s `rank-at` (Probe497.agda:203-207)
--     with `swo-rank′` in place of the refuted `swo-rank`.
-- =====================================================================

opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- SEALED, for the same measured reason section 5.3 records.  Section 9.1
-- transports along a path whose family names this term at a varying
-- endpoint, and `fiber` (src/V/Presentation.lagda.md:34) is
-- `∈-asFiber`, which is a `subst` through the presentation's
-- representation lemma.  Under a `transp` that unfolds and does not
-- stop.  `rank-at′-val` is the one equation every consumer needs, and
-- with it nothing outside this block ever unfolds the definition.
opaque
  -- [LJ-1.518]'s five lines.  The three signatures are the ONE thing it
  -- did not write: inside an `opaque` block Agda never infers the type of
  -- a definition, `where` bindings included.
  rank-at′ : (a : S) (oa : IsOrd (fst a)) (m : S) → ⟨ fst m ∈ fst a ⟩ → S
  rank-at′ a oa m mx = r , isL-ord r (swo-rank′-ord w k)
    where
    w : SWO {ℓc = ℓ} ⟪ fst a ⟫
    w = OrdSWO∈ₛ.w (fst a) oa
    k : ⟪ fst a ⟫
    k = fiber (fst a) mx .fst
    r : V ℓ
    r = swo-rank′ w k

  rank-at′-val :
      (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
    → fst (rank-at′ a oa m mx)
      ≡ swo-rank′ (OrdSWO∈ₛ.w (fst a) oa) (fiber (fst a) mx .fst)
  rank-at′-val a oa m mx = refl

-- A member of an element of the model is an element of the model.
memL : (s : S) (u : V ℓ) → ⟨ u ∈ₛ fst s ⟩ → S
memL s u h =
  u , isL-trans {x = fst s} {y = u} (∈∈ₛ {a = u} {b = fst s} .snd h) (snd s)

-- =====================================================================
-- 7.  THE FORMULA.  [LJ-1.497]'s (Probe497.agda:225-263), rebuilt.  ONE
--     change and it is naming only: `assignAt`'s body is split, exactly
--     as [LJ-1.497] split `supAt`'s, so `extAt` can be applied at a NAMED
--     φ.  Every de Bruijn index below is [LJ-1.497]'s.
-- =====================================================================

fnAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
fnAt f Q m =
  svAt f
  ∧̇ ∀̇ ( (inDomAt (suc f) zero ⇒̇ appAt (suc Q) zero (suc m))
      ∧̇ (appAt (suc Q) zero (suc m) ⇒̇ inDomAt (suc f) zero) )

asgσ : ∀ {n} → Formula S (suc (suc (suc (suc (suc (suc n))))))
asgσ = sucAtL (suc zero) zero ∧̇ (var (s3 zero) ∈̇ var zero)

asgρ : ∀ {n} → Fin n → Formula S (suc (suc (suc (suc (suc n)))))
asgρ {n} f = appAt (s5 f) (suc zero) zero ∧̇ ∃̇ (asgσ {n})

asgχ : ∀ {n} → Fin n → Fin n → Formula S (suc (suc (suc (suc n))))
asgχ f Q = appAt (s4 Q) zero (s3 zero) ∧̇ ∃̇ (asgρ f)

asgψ : ∀ {n} → Fin n → Fin n → Formula S (suc (suc (suc n)))
asgψ f Q = ∃̇ (asgχ f Q)

assignAt : ∀ {n} → Fin n → Fin n → Formula S n
assignAt f Q =
  ∀̇ ( inDomAt (suc f) zero
    ⇒̇ ∃̇ ( appAt (s2 f) (suc zero) zero ∧̇ extAt zero (asgψ f Q) ) )

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
-- 7.1  THE ENVIRONMENT, READ.  Env is [LJ-1.497]'s
--      (Probe497.agda:291-294): five slots, `(f ∷ r ∷ m ∷ q ∷ z ∷ [])`.
--      Every reader below is one application of a `*-adequate` lemma of
--      src/L/Coding/Model.lagda.md and nothing else.  `q` and not `Q`:
--      the formula's first existential carries its own `q`, and the
--      caller supplies `fst q ≡ fst Q`.
-- =====================================================================

module Env (z q m r f : S) where

  γ5 : S ^ 5
  γ5 = f ∷ r ∷ m ∷ q ∷ z ∷ []

  Tab : S → S → Type (ℓ-suc ℓ)
  Tab x v = ⟨ pr (fst x) (fst v) ∈ fst f ⟩

  Qp : S → S → Type (ℓ-suc ℓ)
  Qp x y = ⟨ pr (fst x) (fst y) ∈ fst q ⟩

  Fn : Type (ℓ-suc ℓ)
  Fn = ⟨ γ5 ⊨ fnAt zero (s3 zero) (s2 zero) ⟩

  Asg : Type (ℓ-suc ℓ)
  Asg = ⟨ γ5 ⊨ assignAt zero (s3 zero) ⟩

  Sup : Type (ℓ-suc ℓ)
  Sup = ⟨ γ5 ⊨ supAt zero (suc zero) ⟩

  -- 7.1.1  `fnAt`: f's domain is the q-predecessors of m.
  domOut : Fn → (x v : S) → Tab x v → Qp x m
  domOut hfn x v h =
    subst ⟨_⟩ (appAt-adequate (suc (s3 zero)) zero (suc (s2 zero)) (x ∷ γ5))
      (hfn .snd x .fst
        (subst ⟨_⟩ (sym (inDomAt-adequate (suc zero) zero (x ∷ γ5)))
          PT.∣ v , h ∣₁))

  domIn : Fn → (x : S) → Qp x m → PT.∥ (Σ[ v ∈ S ] Tab x v) ∥₁
  domIn hfn x h =
    subst ⟨_⟩ (inDomAt-adequate (suc zero) zero (x ∷ γ5))
      (hfn .snd x .snd
        (subst ⟨_⟩
          (sym (appAt-adequate (suc (s3 zero)) zero (suc (s2 zero)) (x ∷ γ5)))
          h))

  svf : Fn → (x v v' : S) → Tab x v → Tab x v' → fst v ≡ fst v'
  svf hfn = svAt-out zero γ5 (hfn .fst)

  -- 7.1.2  `supAt`: r holds exactly the members of the successors of f's
  --        values.  This is the slot the range clause reads.
  supOut : Sup → (u : S) → ⟨ fst u ∈ fst r ⟩
         → PT.∥ (Σ[ x ∈ S ] Σ[ v ∈ S ]
                  (Tab x v × ⟨ fst u ∈ sucV (fst v) ⟩)) ∥₁
  supOut hsup u hu = PT.rec PT.squash₁ at1
                       (extAt-out (suc zero) (supBody zero) γ5 hsup u hu)
    where
    at2 : (x : S) → Σ[ v ∈ S ] ⟨ (v ∷ x ∷ u ∷ γ5) ⊨ supB2 zero ⟩
        → PT.∥ (Σ[ x' ∈ S ] Σ[ v ∈ S ]
                 (Tab x' v × ⟨ fst u ∈ sucV (fst v) ⟩)) ∥₁
    at2 x (v , (hp , hs)) = PT.map fin hs
      where
      tab : Tab x v
      tab = subst ⟨_⟩
              (appAt-adequate (s3 zero) (suc zero) zero (v ∷ x ∷ u ∷ γ5)) hp
      fin : Σ[ s ∈ S ]
              (⟨ (s ∷ v ∷ x ∷ u ∷ γ5) ⊨ sucAtL (suc zero) zero ⟩
               × ⟨ fst u ∈ fst s ⟩)
          → Σ[ x' ∈ S ] Σ[ v' ∈ S ]
              (Tab x' v' × ⟨ fst u ∈ sucV (fst v') ⟩)
      fin (s , (hsuc , hin)) = x , (v , (tab ,
        subst (λ t → ⟨ fst u ∈ t ⟩)
          (subst ⟨_⟩
            (sucAtL-adequate (suc zero) zero (s ∷ v ∷ x ∷ u ∷ γ5)) hsuc)
          hin))
    at1 : Σ[ x ∈ S ] ⟨ (x ∷ u ∷ γ5) ⊨ supB1 zero ⟩
        → PT.∥ (Σ[ x' ∈ S ] Σ[ v ∈ S ]
                 (Tab x' v × ⟨ fst u ∈ sucV (fst v) ⟩)) ∥₁
    at1 (x , hx) = PT.rec PT.squash₁ (at2 x) hx

  supIn : Sup → (u x v s : S) → Tab x v → fst s ≡ sucV (fst v)
        → ⟨ fst u ∈ fst s ⟩ → ⟨ fst u ∈ fst r ⟩
  supIn hsup u x v s tab es hin =
    extAt-in (suc zero) (supBody zero) γ5 hsup u
      PT.∣ x , PT.∣ v , (hp , PT.∣ s , (hsuc , hin) ∣₁) ∣₁ ∣₁
    where
    hp = subst ⟨_⟩
           (sym (appAt-adequate (s3 zero) (suc zero) zero (v ∷ x ∷ u ∷ γ5)))
           tab
    hsuc = subst ⟨_⟩
             (sym (sucAtL-adequate (suc zero) zero (s ∷ v ∷ x ∷ u ∷ γ5))) es

  -- 7.1.3  `assignAt`: the value at x is the union of the successors of
  --        the values at the q-predecessors of x.
  AsgExt : S → S → Type (ℓ-suc ℓ)
  AsgExt x v = ⟨ (v ∷ x ∷ γ5) ⊨ extAt zero (asgψ zero (s3 zero)) ⟩

  asgAt : Asg → (x v : S) → Tab x v
        → PT.∥ (Σ[ v' ∈ S ] (Tab x v' × AsgExt x v')) ∥₁
  asgAt hasg x v tab = PT.map conv (hasg x hd)
    where
    hd : ⟨ (x ∷ γ5) ⊨ inDomAt (suc zero) zero ⟩
    hd = subst ⟨_⟩ (sym (inDomAt-adequate (suc zero) zero (x ∷ γ5)))
           PT.∣ v , tab ∣₁
    conv : Σ[ v' ∈ S ]
             (⟨ (v' ∷ x ∷ γ5) ⊨ appAt (s2 zero) (suc zero) zero ⟩
              × AsgExt x v')
         → Σ[ v' ∈ S ] (Tab x v' × AsgExt x v')
    conv (v' , (hp , he)) =
      v' , (subst ⟨_⟩
              (appAt-adequate (s2 zero) (suc zero) zero (v' ∷ x ∷ γ5)) hp
           , he)

  asgRead : (x v u : S) → AsgExt x v → ⟨ fst u ∈ fst v ⟩
          → PT.∥ (Σ[ y ∈ S ] Σ[ u' ∈ S ]
                   (Qp y x × Tab y u' × ⟨ fst u ∈ sucV (fst u') ⟩)) ∥₁
  asgRead x v u hext hu = PT.rec PT.squash₁ atY
    (extAt-out zero (asgψ zero (s3 zero)) (v ∷ x ∷ γ5) hext u hu)
    where
    Out : Type (ℓ-suc ℓ)
    Out = Σ[ y ∈ S ] Σ[ u' ∈ S ]
            (Qp y x × Tab y u' × ⟨ fst u ∈ sucV (fst u') ⟩)
    atY : Σ[ y ∈ S ] ⟨ (y ∷ u ∷ v ∷ x ∷ γ5) ⊨ asgχ zero (s3 zero) ⟩
        → PT.∥ Out ∥₁
    atY (y , (hq , hu')) = PT.rec PT.squash₁ atU hu'
      where
      qy : Qp y x
      qy = subst ⟨_⟩
             (appAt-adequate (s4 (s3 zero)) zero (s3 zero)
               (y ∷ u ∷ v ∷ x ∷ γ5)) hq
      atU : Σ[ u' ∈ S ] ⟨ (u' ∷ y ∷ u ∷ v ∷ x ∷ γ5) ⊨ asgρ zero ⟩
          → PT.∥ Out ∥₁
      atU (u' , (hf' , hs)) = PT.map atS hs
        where
        tu : Tab y u'
        tu = subst ⟨_⟩
               (appAt-adequate (s5 zero) (suc zero) zero
                 (u' ∷ y ∷ u ∷ v ∷ x ∷ γ5)) hf'
        atS : Σ[ s ∈ S ]
                (⟨ (s ∷ u' ∷ y ∷ u ∷ v ∷ x ∷ γ5) ⊨ sucAtL (suc zero) zero ⟩
                 × ⟨ fst u ∈ fst s ⟩)
            → Out
        atS (s , (hsuc , hin)) = y , (u' , (qy , (tu ,
          subst (λ t → ⟨ fst u ∈ t ⟩)
            (subst ⟨_⟩
              (sucAtL-adequate (suc zero) zero
                (s ∷ u' ∷ y ∷ u ∷ v ∷ x ∷ γ5)) hsuc)
            hin)))

  asgFill : (x v u y u' s : S) → AsgExt x v
          → Qp y x → Tab y u' → fst s ≡ sucV (fst u') → ⟨ fst u ∈ fst s ⟩
          → ⟨ fst u ∈ fst v ⟩
  asgFill x v u y u' s hext qy tu es hin =
    extAt-in zero (asgψ zero (s3 zero)) (v ∷ x ∷ γ5) hext u
      PT.∣ y , (hq , PT.∣ u' , (hf' , PT.∣ s , (hsuc , hin) ∣₁) ∣₁) ∣₁
    where
    hq = subst ⟨_⟩
           (sym (appAt-adequate (s4 (s3 zero)) zero (s3 zero)
                  (y ∷ u ∷ v ∷ x ∷ γ5))) qy
    hf' = subst ⟨_⟩
            (sym (appAt-adequate (s5 zero) (suc zero) zero
                   (u' ∷ y ∷ u ∷ v ∷ x ∷ γ5))) tu
    hsuc = subst ⟨_⟩
             (sym (sucAtL-adequate (suc zero) zero
                    (s ∷ u' ∷ y ∷ u ∷ v ∷ x ∷ γ5))) es

  -- 7.1.4  [LJ-1.497]'s two measurements of the pair-free case
  --        (Probe497.agda:299-334), which section 8 spends.
  fn-no-pairs : Fn → ((y : S) → Qp y m → Empty.⊥)
              → (x v : S) → Tab x v → Empty.⊥
  fn-no-pairs hfn qmin x v h = qmin x (domOut hfn x v h)

  body-absurd : ((x v : S) → Tab x v → Empty.⊥)
              → (u : S) → ⟨ (u ∷ γ5) ⊨ supBody zero ⟩ → Empty.⊥
  body-absurd nof u hb = PT.rec Empty.isProp⊥ at1 hb
    where
    at2 : (x : S) → Σ[ v ∈ S ] ⟨ (v ∷ x ∷ u ∷ γ5) ⊨ supB2 zero ⟩ → Empty.⊥
    at2 x (v , (hp , _)) =
      nof x v
        (subst ⟨_⟩
          (appAt-adequate (s3 zero) (suc zero) zero (v ∷ x ∷ u ∷ γ5)) hp)
    at1 : Σ[ x ∈ S ] ⟨ (x ∷ u ∷ γ5) ⊨ supB1 zero ⟩ → Empty.⊥
    at1 (x , hx) = PT.rec Empty.isProp⊥ (at2 x) hx

  sup-no-member : Sup → ((x v : S) → Tab x v → Empty.⊥)
                → (u : S) → ⟨ fst u ∈ fst r ⟩ → Empty.⊥
  sup-no-member hsup nof u hu =
    body-absurd nof u (extAt-out (suc zero) (supBody zero) γ5 hsup u hu)

-- =====================================================================
-- 8.  W3.  THE ADEQUACY AT A Q-MINIMAL MEMBER, ALONE.
--
--     THIS IS THE SITE [LJ-1.497] REFUTED.  There the formula pinned the
--     rank slot EMPTY at a q-minimal member (Probe497.agda:328-334) while
--     `swo-rank` had ∅ as a member at every member of `a`
--     (Probe497.agda:210-216), so no term of the old adequacy could
--     exist.  Two things have changed and both are needed: the hypothesis
--     `ord-reads-Q` makes q-minimal and ∈-minimal ONE notion, and
--     `swo-rank′` IS ∅ at an ∈-minimal member.
--
--     The general case is section 9 and it is a recursion; this case is
--     not a case of it, it is the case the recursion bottoms out at.
-- =====================================================================

module Min (Q a : S) (oa : IsOrd (fst a)) (hQ : ord-reads-Q Q a oa) where

  open Site a oa

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = OrdSWO∈ₛ.w α oa

  -- [LJ-1.518]'s `q-min→min` (Probe518.agda:446-452), inlined at `hQ`.
  qmin→min : (mm : S) (ma : ⟨ fst mm ∈ α ⟩)
           → ((y : S) → PairOf Q y mm → Empty.⊥)
           → (k : ⟪ α ⟫) → k ≺ₛ ix mm ma → Empty.⊥
  qmin→min mm ma qmin k h =
    qmin (memS k)
      (hQ .snd (memS k) mm (memS-mem k) ma
        (subst (λ t → t ≺ₛ ix mm ma) (sym (memS-ix k)) h))

  adequate-min :
      (z q m r f : S) (mx : ⟨ fst m ∈ α ⟩) → fst q ≡ fst Q
    → ((y : S) → PairOf Q y m → Empty.⊥)
    → Env.Fn z q m r f
    → Env.Sup z q m r f
    → fst r ≡ fst (rank-at′ a oa m mx)
  adequate-min z q m r f mx qQ qmin hfn hsup =
    rEmpty ∙ sym (swo-rank′-∅ w (ix m mx) (qmin→min m mx qmin))
           ∙ sym (rank-at′-val a oa m mx)
    where
    open Env z q m r f

    qminq : (y : S) → Qp y m → Empty.⊥
    qminq y h = qmin y (subst (λ t → ⟨ pr (fst y) (fst m) ∈ t ⟩) qQ h)

    nof : (x v : S) → Tab x v → Empty.⊥
    nof = fn-no-pairs hfn qminq

    rEmpty : fst r ≡ ∅
    rEmpty = extensionality (fst r) ∅ (outr , innr)
      where
      outr : (u : V ℓ) → ⟨ u ∈ₛ fst r ⟩ → ⟨ u ∈ₛ ∅ ⟩
      outr u hu = Empty.rec
        (sup-no-member hsup nof (memL r u hu)
          (∈∈ₛ {a = u} {b = fst r} .snd hu))
      innr : (u : V ℓ) → ⟨ u ∈ₛ ∅ ⟩ → ⟨ u ∈ₛ fst r ⟩
      innr u hu = Empty.rec (∅-empty u hu)

-- =====================================================================
-- 9.  THE OBLIGATION.
--
--     The general case is a recursion and section 8 is where it bottoms
--     out.  The shape: `assignAt` says f's value at a member is the union
--     of the successors of f's values at that member's q-predecessors,
--     and `swo-rank′` says the rank at an index is the union of the
--     successors of the ranks at that index's ≺-predecessors.  The
--     hypothesis `ord-reads-Q` is what makes those two families the SAME
--     family, so `key` below is one well-founded induction and both
--     directions of one extensional identity.
--
--     `keyStep` takes its induction hypothesis EXPLICITLY, so the
--     recursion is one line and the termination is on the `Acc` and
--     nothing else.
-- =====================================================================

module Adq (Q a : S) (oa : IsOrd (fst a)) (hQ : ord-reads-Q Q a oa) where

  open Site a oa

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = OrdSWO∈ₛ.w α oa

  tr : (i j k : ⟪ α ⟫) → i ≺ₛ j → j ≺ₛ k → i ≺ₛ k
  tr = OrdSWO∈ₛ.trans₁ α oa

  rk : ⟪ α ⟫ → V ℓ
  rk k = swo-rank′ w k

  -- a rank is an ordinal, so it is an element of the model.
  rkS : ⟪ α ⟫ → S
  rkS k = rk k , isL-ord (rk k) (swo-rank′-ord w k)

  module At (z q m r f : S) (mx : ⟨ fst m ∈ α ⟩) (qQ : fst q ≡ fst Q)
            (hfn : Env.Fn z q m r f) (hasg : Env.Asg z q m r f)
            (hsup : Env.Sup z q m r f) where

    open Env z q m r f

    k₀ : ⟪ α ⟫
    k₀ = ix m mx

    -- the hypothesis, in both directions, transported to the formula's
    -- own `q`.  Nothing else in this section touches `Q`.
    q→≺ : (x y : S) → Qp x y
        → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ] Σ[ ya ∈ ⟨ fst y ∈ α ⟩ ]
            (ix x xa ≺ₛ ix y ya)
    q→≺ x y h = hQ .fst x y (subst (λ t → ⟨ pr (fst x) (fst y) ∈ t ⟩) qQ h)

    ≺→q : (x y : S) (xa : ⟨ fst x ∈ α ⟩) (ya : ⟨ fst y ∈ α ⟩)
        → ix x xa ≺ₛ ix y ya → Qp x y
    ≺→q x y xa ya h =
      subst (λ t → ⟨ pr (fst x) (fst y) ∈ t ⟩) (sym qQ) (hQ .snd x y xa ya h)

    -- ONE STEP.  Below `k₀`, f's value at a member IS the rank at that
    -- member's index.  `ih` is the same statement at every ≺-predecessor.
    keyStep : (k : ⟪ α ⟫) → k ≺ₛ k₀
            → ((j : ⟪ α ⟫) → j ≺ₛ k
               → (v : S) → Tab (memS j) v → fst v ≡ rk j)
            → (v : S) → Tab (memS k) v → fst v ≡ rk k
    keyStep k k≺ ih v tab =
      PT.rec (setIsSet (fst v) (rk k)) use (asgAt hasg (memS k) v tab)
      where
      xk : S
      xk = memS k

      use : Σ[ v' ∈ S ] (Tab xk v' × AsgExt xk v') → fst v ≡ rk k
      use (v' , (tab' , hext)) =
        svf hfn xk v v' tab tab' ∙ extensionality (fst v') (rk k) (out , inn)
        where
        out : (u : V ℓ) → ⟨ u ∈ₛ fst v' ⟩ → ⟨ u ∈ₛ rk k ⟩
        out u hu = PT.rec (snd (u ∈ₛ rk k)) g1
          (asgRead xk v' (memL v' u hu) hext (∈∈ₛ {a = u} {b = fst v'} .snd hu))
          where
          g1 : Σ[ y ∈ S ] Σ[ u' ∈ S ]
                 (Qp y xk × Tab y u' × ⟨ u ∈ sucV (fst u') ⟩)
             → ⟨ u ∈ₛ rk k ⟩
          g1 (y , (u' , (qy , (tu , hin)))) =
            rank-mem-in w k u j j≺k
              (∈∈ₛ {a = u} {b = sucV (rk j)} .fst
                (subst (λ t → ⟨ u ∈ sucV t ⟩) eqv hin))
            where
            got = q→≺ y xk qy
            j : ⟪ α ⟫
            j = ix y (got .fst)
            -- the membership the hypothesis returns and the one `memS`
            -- carries are the same index: `⟨ fst xk ∈ α ⟩` is a prop.
            j≺k : j ≺ₛ k
            j≺k = subst (λ t → j ≺ₛ t)
                    (cong (ix xk)
                       (snd (fst xk ∈ α) (got .snd .fst) (memS-mem k))
                     ∙ memS-ix k)
                    (got .snd .snd)
            eqv : fst u' ≡ rk j
            eqv = ih j j≺k u'
                    (subst (λ t → ⟨ pr t (fst u') ∈ fst f ⟩)
                      (sym (ix-val y (got .fst))) tu)

        inn : (u : V ℓ) → ⟨ u ∈ₛ rk k ⟩ → ⟨ u ∈ₛ fst v' ⟩
        inn u hu = PT.rec (snd (u ∈ₛ fst v')) g2 (rank-mem-out w k u hu)
          where
          uS : S
          uS = memL (rkS k) u hu
          g2 : Σ[ j ∈ ⟪ α ⟫ ] (j ≺ₛ k × ⟨ u ∈ₛ sucV (rk j) ⟩)
             → ⟨ u ∈ₛ fst v' ⟩
          g2 (j , (j≺k , hin)) =
            PT.rec (snd (u ∈ₛ fst v')) g3 (domIn hfn (memS j) qjm)
            where
            qjm : Qp (memS j) m
            qjm = ≺→q (memS j) m (memS-mem j) mx
                    (subst (λ t → t ≺ₛ k₀) (sym (memS-ix j))
                      (tr j k k₀ j≺k k≺))
            g3 : Σ[ u' ∈ S ] Tab (memS j) u' → ⟨ u ∈ₛ fst v' ⟩
            g3 (u' , tu) =
              ∈∈ₛ {a = u} {b = fst v'} .fst
                (asgFill xk v' uS (memS j) u' sS hext qjxk tu refl hin')
              where
              eqv : fst u' ≡ rk j
              eqv = ih j j≺k u' tu
              sS : S
              sS = sucV (fst u')
                 , isL-ord (sucV (fst u'))
                     (suc-ord (subst IsOrd (sym eqv) (swo-rank′-ord w j)))
              hin' : ⟨ fst uS ∈ fst sS ⟩
              hin' = ∈∈ₛ {a = u} {b = sucV (fst u')} .snd
                       (subst (λ t → ⟨ u ∈ₛ sucV t ⟩) (sym eqv) hin)
              qjxk : Qp (memS j) xk
              qjxk = ≺→q (memS j) xk (memS-mem j) (memS-mem k)
                       (subst (λ t → ix (memS j) (memS-mem j) ≺ₛ t)
                          (sym (memS-ix k))
                          (subst (λ s → s ≺ₛ k) (sym (memS-ix j)) j≺k))

    key : (k : ⟪ α ⟫) → Acc _≺ₛ_ k → k ≺ₛ k₀
        → (v : S) → Tab (memS k) v → fst v ≡ rk k
    key k (acc rs) k≺ =
      keyStep k k≺ (λ j j≺k → key j (rs j j≺k) (tr j k k₀ j≺k k≺))

    keyAll : (k : ⟪ α ⟫) → k ≺ₛ k₀ → (v : S) → Tab (memS k) v → fst v ≡ rk k
    keyAll k = key k (SWO.wf∙ w k)

    -- THE SLOT THE RANGE CLAUSE READS.  `supAt` pins `r` to the union of
    -- the successors of f's values; `key` says those values are the
    -- ranks; and `rank-mem-out`/`rank-mem-in` say the rank at `k₀` is
    -- that same union.
    top : fst r ≡ rk k₀
    top = extensionality (fst r) (rk k₀) (rout , rinn)
      where
      rout : (u : V ℓ) → ⟨ u ∈ₛ fst r ⟩ → ⟨ u ∈ₛ rk k₀ ⟩
      rout u hu = PT.rec (snd (u ∈ₛ rk k₀)) g1
        (supOut hsup (memL r u hu) (∈∈ₛ {a = u} {b = fst r} .snd hu))
        where
        g1 : Σ[ x ∈ S ] Σ[ v ∈ S ] (Tab x v × ⟨ u ∈ sucV (fst v) ⟩)
           → ⟨ u ∈ₛ rk k₀ ⟩
        g1 (x , (v , (tab , hin))) =
          rank-mem-in w k₀ u j j≺
            (∈∈ₛ {a = u} {b = sucV (rk j)} .fst
              (subst (λ t → ⟨ u ∈ sucV t ⟩) eqv hin))
          where
          got = q→≺ x m (domOut hfn x v tab)
          j : ⟪ α ⟫
          j = ix x (got .fst)
          j≺ : j ≺ₛ k₀
          j≺ = subst (λ t → j ≺ₛ t)
                 (cong (ix m) (snd (fst m ∈ α) (got .snd .fst) mx))
                 (got .snd .snd)
          eqv : fst v ≡ rk j
          eqv = keyAll j j≺ v
                  (subst (λ t → ⟨ pr t (fst v) ∈ fst f ⟩)
                    (sym (ix-val x (got .fst))) tab)

      rinn : (u : V ℓ) → ⟨ u ∈ₛ rk k₀ ⟩ → ⟨ u ∈ₛ fst r ⟩
      rinn u hu = PT.rec (snd (u ∈ₛ fst r)) g2 (rank-mem-out w k₀ u hu)
        where
        uS : S
        uS = memL (rkS k₀) u hu
        g2 : Σ[ j ∈ ⟪ α ⟫ ] (j ≺ₛ k₀ × ⟨ u ∈ₛ sucV (rk j) ⟩) → ⟨ u ∈ₛ fst r ⟩
        g2 (j , (j≺ , hin)) =
          PT.rec (snd (u ∈ₛ fst r)) g3 (domIn hfn (memS j) qjm)
          where
          qjm : Qp (memS j) m
          qjm = ≺→q (memS j) m (memS-mem j) mx
                  (subst (λ t → t ≺ₛ k₀) (sym (memS-ix j)) j≺)
          g3 : Σ[ v ∈ S ] Tab (memS j) v → ⟨ u ∈ₛ fst r ⟩
          g3 (v , tv) =
            ∈∈ₛ {a = u} {b = fst r} .fst
              (supIn hsup uS (memS j) v sS tv refl hin')
            where
            eqv : fst v ≡ rk j
            eqv = keyAll j j≺ v tv
            sS : S
            sS = sucV (fst v)
               , isL-ord (sucV (fst v))
                   (suc-ord (subst IsOrd (sym eqv) (swo-rank′-ord w j)))
            hin' : ⟨ fst uS ∈ fst sS ⟩
            hin' = ∈∈ₛ {a = u} {b = sucV (fst v)} .snd
                     (subst (λ t → ⟨ u ∈ₛ sucV t ⟩) (sym eqv) hin)

    concl : fst z ≡ pr (fst m) (fst r)
          → fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx))
    concl hpr = hpr ∙ cong (pr (fst m)) (top ∙ sym (rank-at′-val a oa m mx))

-- =====================================================================
-- 9.1  THE CONCLUSION IS A PROPOSITION, which is what lets the three
--      existentials of `rankFo` be eliminated.  `pr-inj` pins the member
--      and `↾-reflects` (src/FOL/ZFStructure.lagda.md:157) lifts that to
--      the model's element, because `isL` is proof-irrelevant.
-- =====================================================================

Tgt : (a : S) (oa : IsOrd (fst a)) (z : S) → Type (ℓ-suc ℓ)
Tgt a oa z =
  Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
    (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))

isPropTgt : (a : S) (oa : IsOrd (fst a)) (z : S) → isProp (Tgt a oa z)
isPropTgt a oa z (m , (mx , e)) (m' , (mx' , e')) =
  atSame (↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} (pr-inj (sym e ∙ e') .fst)) mx mx' e e'
  where
  -- THE MOTIVE DOES NOT NAME THE PATH, and that is the whole design.
  -- Writing this as `ΣPathP (pm , …)` puts `pm` inside a type family, so
  -- the elaborator normalizes `pr-inj … .fst` at a path argument, and
  -- that unfolds the Kuratowski pair through `⟪_⟫`.  MEASURED: with
  -- section 5.3 and section 6.1 both sealed, that form was still running
  -- when it was stopped after ten minutes; the run's own record carries
  -- the started line and no completion line
  -- (agents/tasks/LJ-1-521/runs/full-try4.out), and the same shape with
  -- section 9 removed entirely behaved the same
  -- (agents/tasks/LJ-1-521/runs/bisect-isprop.out).  Under `J` the path
  -- is applied and never normalized, and the only family left is at a
  -- FIXED `m`, where `⟨ fst m ∈ fst a ⟩` is stuck and `rank-at′` is
  -- sealed.  The whole file is then seconds, not minutes:
  -- agents/tasks/LJ-1-521/runs/full-1.out to full-3.out.
  Mot : (m'' : S) → m ≡ m'' → Type (ℓ-suc ℓ)
  Mot m'' _ =
      (u : ⟨ fst m ∈ fst a ⟩) (u' : ⟨ fst m'' ∈ fst a ⟩)
      (p : fst z ≡ pr (fst m) (fst (rank-at′ a oa m u)))
      (p' : fst z ≡ pr (fst m'') (fst (rank-at′ a oa m'' u')))
    → (m , (u , p)) ≡ (m'' , (u' , p'))

  base : Mot m refl
  base u u' p p' i = m , (mxp i , ep i)
    where
    mxp : u ≡ u'
    mxp = snd (fst m ∈ fst a) u u'
    ep : PathP (λ i → fst z ≡ pr (fst m) (fst (rank-at′ a oa m (mxp i)))) p p'
    ep = isProp→PathP
           (λ i → setIsSet (fst z)
                    (pr (fst m) (fst (rank-at′ a oa m (mxp i))))) p p'

  atSame : {m'' : S} (q : m ≡ m'') → Mot m'' q
  atSame = J Mot base

-- =====================================================================
-- 9.2  THE OBLIGATION, as [LJ-1.518] restated it, with no holes.
-- =====================================================================

rankFo-adequate′ :
    (Q a : S) (oa : IsOrd (fst a)) (z : S)
  → ord-reads-Q Q a oa
  → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))
rankFo-adequate′ Q a oa z hQ hsat =
  PT.rec (isPropTgt a oa z)
    (λ { (q , (qQ , hm)) →
      PT.rec (isPropTgt a oa z)
        (λ { (m , hr) →
          PT.rec (isPropTgt a oa z)
            (λ { (r , (hpr , (mx , hf))) →
              PT.rec (isPropTgt a oa z)
                (λ { (f , (hfn , (hasg , hsup))) →
                  m , (mx ,
                    Adq.At.concl Q a oa hQ z q m r f mx qQ hfn hasg hsup
                      (subst ⟨_⟩
                        (prAtL-adequate (s3 zero) (suc zero) zero
                          (r ∷ m ∷ q ∷ z ∷ [])) hpr)) })
                hf })
            hr })
        hm })
    hsat

-- =====================================================================
-- 10.  THE ANTECEDENT IS NOT EMPTY, AND IT IS PROVED HERE.
--
--      [LJ-1.507] left an adequacy green against a hypothesis nothing
--      satisfied.  A citation across files does not settle that, because
--      a rebuilt statement could differ from the one that was inhabited.
--      So [LJ-1.518]'s witness (Probe518.agda:206-342) is rebuilt in this
--      file, against THIS file's `ord-reads-Q`, and `rankFo-adequate′`
--      above is applied to it at the end.
--
--      The construction is `L.Choice.Limit`'s `codeOrder`: a separation
--      out of a `smallDom` bound over the pairs
--      (src/L/Choice/Limit.lagda.md:418-419,607-608).
-- =====================================================================

module Witness (a : S) (oa : IsOrd (fst a)) where

  open Site a oa

  bnd : Σ[ D ∈ S ] ((p : ⟪ α ⟫ × ⟪ α ⟫)
                    → ⟨ prʟ (memS (fst p)) (memS (snd p)) ∈ˢ D ⟩)
  bnd = smallDom (⟪ α ⟫ × ⟪ α ⟫) (λ p → prʟ (memS (fst p)) (memS (snd p)))

  D : S
  D = bnd .fst

  inD : (x m : S) (xa : ⟨ fst x ∈ α ⟩) (ma : ⟨ fst m ∈ α ⟩)
      → ⟨ pr (fst x) (fst m) ∈ fst D ⟩
  inD x m xa ma =
    subst (λ t → ⟨ t ∈ fst D ⟩)
      (prʟ-fst (memS (ix x xa)) (memS (ix m ma))
        ∙ cong₂ pr (ix-val x xa) (ix-val m ma))
      (bnd .snd (ix x xa , ix m ma))

  CondBody : Formula S 3
  CondBody =
    prAtL (s2 zero) (suc zero) zero
    ∧̇ ( (var (suc zero) ∈̇ con a)
      ∧̇ ( (var zero ∈̇ con a)
        ∧̇ (var (suc zero) ∈̇ var zero) ) )

  Cond : Formula S 1
  Cond = ∃̇ ( ∃̇ CondBody )

  opaque
    ordQ : S
    ordQ = hasSeparationL D Cond .fst .fst

    ordQ-mem : (z : S) → (z ∈ˢ ordQ) ≡ ((z ∈ˢ D) ⊓ ((z ∷ []) ⊨ Cond))
    ordQ-mem = hasSeparationL D Cond .fst .snd

  private
    Inner : S → S → S → Type (ℓ-suc ℓ)
    Inner z c d = ⟨ (d ∷ c ∷ z ∷ []) ⊨ CondBody ⟩

    Outer : S → Type (ℓ-suc ℓ)
    Outer z = Σ[ c ∈ S ] PT.∥ (Σ[ d ∈ S ] Inner z c d) ∥₁

    cond-in : (z c d : S) → Inner z c d → ⟨ (z ∷ []) ⊨ Cond ⟩
    cond-in z c d hi = PT.∣ c , PT.∣ d , hi ∣₁ ∣₁

    cond-out : (z : S) → ⟨ (z ∷ []) ⊨ Cond ⟩ → PT.∥ Outer z ∥₁
    cond-out z h = h

  fill : ReadsIn ordQ
  fill x m xa ma h =
    subst (λ t → ⟨ t ∈ fst ordQ ⟩) qz
      (subst ⟨_⟩ (sym (ordQ-mem (prʟ x m)))
        ( subst (λ t → ⟨ t ∈ fst D ⟩) (sym qz) (inD x m xa ma)
        , cond-in (prʟ x m) x m (hpr , (xa , (ma , x∈m))) ))
    where
    qz : fst (prʟ x m) ≡ pr (fst x) (fst m)
    qz = prʟ-fst x m

    hpr : ⟨ (m ∷ x ∷ prʟ x m ∷ []) ⊨ prAtL (s2 zero) (suc zero) zero ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate (s2 zero) (suc zero) zero
             (m ∷ x ∷ prʟ x m ∷ []))) qz

    x∈m : ⟨ fst x ∈ fst m ⟩
    x∈m = ∈-cong (ix-val x xa) (ix-val m ma)
      (∈∈ₛ {a = ⟪ α ⟫↪ (ix x xa)} {b = ⟪ α ⟫↪ (ix m ma)} .snd h)

  rep : ReadsOut ordQ
  rep x m h = PT.rec (isPropReadsOut ordQ x m) atC
                (cond-out (prʟ x m) cnd)
    where
    qz : fst (prʟ x m) ≡ pr (fst x) (fst m)
    qz = prʟ-fst x m

    inSet : ⟨ fst (prʟ x m) ∈ fst ordQ ⟩
    inSet = subst (λ t → ⟨ t ∈ fst ordQ ⟩) (sym qz) h

    cnd : ⟨ (prʟ x m ∷ []) ⊨ Cond ⟩
    cnd = subst ⟨_⟩ (ordQ-mem (prʟ x m)) inSet .snd

    atD : (c d : S) → Inner (prʟ x m) c d
        → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ]
          Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma)
    atD c d (hpr , (ca , (da , c∈d))) = xa , (ma , below)
      where
      qcd : pr (fst x) (fst m) ≡ pr (fst c) (fst d)
      qcd = sym qz
          ∙ subst ⟨_⟩ (prAtL-adequate (s2 zero) (suc zero) zero
                        (d ∷ c ∷ prʟ x m ∷ [])) hpr

      split : (fst x ≡ fst c) × (fst m ≡ fst d)
      split = pr-inj qcd

      xa : ⟨ fst x ∈ α ⟩
      xa = subst (λ v → ⟨ v ∈ α ⟩) (sym (split .fst)) ca

      ma : ⟨ fst m ∈ α ⟩
      ma = subst (λ v → ⟨ v ∈ α ⟩) (sym (split .snd)) da

      x∈m : ⟨ fst x ∈ fst m ⟩
      x∈m = ∈-cong (sym (split .fst)) (sym (split .snd)) c∈d

      below : ix x xa ≺ₛ ix m ma
      below = ∈∈ₛ {a = ⟪ α ⟫↪ (ix x xa)} {b = ⟪ α ⟫↪ (ix m ma)} .fst
             (∈-cong (sym (ix-val x xa)) (sym (ix-val m ma)) x∈m)

    atC : Outer (prʟ x m)
        → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ]
          Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ] (ix x xa ≺ₛ ix m ma)
    atC (c , hd) = PT.rec (isPropReadsOut ordQ x m)
      (λ { (d , hi) → atD c d hi }) hd

  reads : Reads ordQ
  reads = rep , fill

ord-set-witness : (a : S) (oa : IsOrd (fst a))
                → Σ[ Q ∈ S ] ord-reads-Q Q a oa
ord-set-witness a oa = Witness.ordQ a oa , Witness.reads a oa

-- THE OBLIGATION IS NOT VACUOUS.  This is `rankFo-adequate′` applied at
-- the witness above and nothing else: the antecedent it consumes is
-- INHABITED at every ordinal of the model, at the ∈-order, in this file.
rankFo-adequate′-nonvacuous :
    (a : S) (oa : IsOrd (fst a)) (z : S)
  → ⟨ (z ∷ []) ⊨ rankFo (ord-set-witness a oa .fst) a ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))
rankFo-adequate′-nonvacuous a oa z =
  rankFo-adequate′ (ord-set-witness a oa .fst) a oa z
    (ord-set-witness a oa .snd)
