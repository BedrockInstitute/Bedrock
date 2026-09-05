{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.398] PROBE.  The BAND RECURSION on the two selections, and
-- the residue it leaves.  It runs in agents/tasks/LJ-1-398/ and lands
-- nothing in src/.
--
--   TERM 1  `band-owes-2`.  The residue: the untruncated AMBIENT
--            arrow at an L-cardinal that is not its own ambient least
--            cardinal.  Every other case has a supplier.
--
--   TERM 2  `sq-band-2`.  The recursion, by `∈-induction`, split by
--            `lem` on `IsCardinalL` (a proposition), then by
--            `kappa-decides` on whether the site is its own ambient
--            least cardinal:
--
--     case                                   supplier
--     x ≡ ω                                 `squareω`, delivered
--     ¬ IsCardinalL x                       `coded-arrow`, then
--                                           `descent-core`
--     IsCardinalL x, x its own least card   `amb-card-at-kappa`,
--                                           `kappa-is-limit`,
--                                           `amb-init'`,
--                                           `via-col-square`
--     IsCardinalL x, x not its own least    `band-owes-2` (residue),
--                                           then `descent-core`
--
--   The suppliers are taken as hypotheses of a nested module, so the
--   witness meter sees a clean top-level telescope; `coded-arrow` and
--   `amb-card-at-kappa` name `L.Cardinal`'s `IsCardinalL` and
--   `LeastCardInjL.κ`, which live behind `lem` and cannot be opened
--   above the header.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-398.Probe398 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( ∈-induction; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( isPropIsOrd; 𝒮ʟ; isL; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω; finite-excl-ω )
open import L.Cardinal {ℓ} lem
  using ( _↪_; IsCardinalL; module LeastCardInjL )
open import Cubical.Foundations.HLevels using ( isPropΠ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ; Σ-syntax )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 0.  SMALL DELIVERED-FACT HELPERS, rebuilt from src/ primitives.
-- =====================================================================

-- Every ordinal is an L-element ([LJ-1.386]'s `isL-ord`, one line).
-- Sealed (opaque): its body reduces to an `∈-induction` via
-- `ord∈Lset-suc`, and leaving it transparent forces that recursion
-- inside every conversion check on `(α , isL-ord α oα)` (P-i, R-36).
opaque
  isL-ord : (α : V ℓ) → IsOrd α → ⟨ isL α ⟩
  isL-ord α oα = Lset→isL (sucV α) (suc-ord oα) α (ord∈Lset-suc α oα)

-- A member of an ordinal injects its index into the ordinal
-- ([LJ-1.390]'s `mem-incl`, from `member`, `fiber`, `↪-inj`).
mem-incl : (d k : V ℓ) → IsOrd d → ⟨ k ∈ d ⟩ → ⟪ k ⟫ ↪ ⟪ d ⟫
mem-incl d k od k∈d = ι , ι-inj
  where
  raise : (m : ⟪ k ⟫) → ⟨ ⟪ k ⟫↪ m ∈ d ⟩
  raise m = fst od (member k m) k∈d

  ι : ⟪ k ⟫ → ⟪ d ⟫
  ι m = fst (fiber d (raise m))

  ι-inj : (m n : ⟪ k ⟫) → ι m ≡ ι n → m ≡ n
  ι-inj m n e = ↪-inj {a = k}
    (sym (snd (fiber d (raise m)))
     ∙ cong (⟪ d ⟫↪) e
     ∙ snd (fiber d (raise n)))

-- Composition of two ambient injections.
comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- [LJ-1.393]'s ambient cardinality notion.
AmbCard : V ℓ → Type (ℓ-suc ℓ)
AmbCard α = (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
          → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥

-- `IsCardinalL` is a proposition: a function into `Empty.⊥`.
isPropCardL : (a : S) → isProp (IsCardinalL a)
isPropCardL a = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Empty.isProp⊥

-- An ordinal that contains ω is not below ω.
inf-member : (b : V ℓ) → ⟨ ω ∈ b ⟩ → (⟨ b ∈ ω ⟩ → Empty.⊥)
inf-member b ω∈b h = ∈-irrefl ω (ω-ord .fst ω∈b h)

-- =====================================================================
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- `fst (LeastCardInjL.κ a oa)` reduces through `leastOf`'s body to a
-- large stuck term; left transparent, every conversion check between
-- two spellings of `fst κ` re-runs that reduction and explodes.  The
-- seal makes `fst (κL a oa)` a small atom.
-- =====================================================================
opaque
  κL : (a : S) (oa : IsOrd (fst a)) → S
  κL a oa = LeastCardInjL.κ a oa

  κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa))
  κoL a oa = LeastCardInjL.oκ a oa

  κ∈sucL : (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κL a oa) ∈ sucV (fst a) ⟩
  κ∈sucL a oa = LeastCardInjL.κ∈sα a oa

-- =====================================================================
-- PART 1.  W3, THE PROBE.  The second positive split: decide whether a
-- site is its own ambient least cardinal.  `κL` is data, so the decision
-- is `ord-tri` on `fst κ` against `fst a`.
-- =====================================================================

kappa-decides : (a : S) (oa : IsOrd (fst a))
  → (fst (κL a oa) ≡ fst a)
  ⊎ ⟨ fst (κL a oa) ∈ fst a ⟩
kappa-decides a oa = go (ord-tri (fst κ) oκ (fst a) oa)
  where
  κ : S
  κ = κL a oa
  oκ : IsOrd (fst κ)
  oκ = κoL a oa
  κ∈sα : ⟨ fst κ ∈ sucV (fst a) ⟩
  κ∈sα = κ∈sucL a oa

  go : ⟨ fst κ ∈ fst a ⟩ ⊎ ((fst κ ≡ fst a) ⊎ ⟨ fst a ∈ fst κ ⟩)
     → (fst κ ≡ fst a) ⊎ ⟨ fst κ ∈ fst a ⟩
  go (inl κ∈a) = inr κ∈a
  go (inr (inl κ≡a)) = inl κ≡a
  go (inr (inr a∈κ)) = Empty.rec*
    (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* κ∈sα cycle self)
    where
    cycle : ⟨ fst κ ∈ fst a ⟩ → Empty.⊥* {ℓ-suc ℓ}
    cycle κ∈a = lift (∈-irrefl (fst a) (oa .fst a∈κ κ∈a))
    self : fst κ ≡ fst a → Empty.⊥* {ℓ-suc ℓ}
    self κ≡a = lift (∈-irrefl (fst a) (subst (λ w → ⟨ fst a ∈ w ⟩) κ≡a a∈κ))

-- =====================================================================
-- PART 2.  TERM 1.  THE RESIDUE.
--
--   `band-owes-2` is owed at exactly one class of ordinal: an infinite
--   L-cardinal `a` that is NOT its own ambient least cardinal, i.e.
--   `fst κ ∈ a` for `κ = κL (a , isL a) oa`.  It owes the untruncated
--   ambient arrow `⟪ a ⟫ ↪ ⟪ fst κ ⟫`.  The target's ordinality is
--   `κoL`, its membership is the hypothesis itself, and its infinitude
--   follows from the arrow by `finite-excl-ω` (PART 3, `by-residue`),
--   so no other conjunct is owed.  The band membership does not appear,
--   exactly as [LJ-1.395]'s `band-owes` omitted it: the band is the
--   recursion's context, not the residue's.
-- =====================================================================

band-owes-2 : Type (ℓ-suc ℓ)
band-owes-2 =
  (a : V ℓ) (oa : IsOrd a) → ⟨ ω ∈ a ⟩
  → IsCardinalL (a , isL-ord a oa)
  → ⟨ fst (κL (a , isL-ord a oa) oa) ∈ a ⟩
  → (⟪ a ⟫ ↪ ⟪ fst (κL (a , isL-ord a oa) oa) ⟫)

-- =====================================================================
-- PART 3.  TERM 2.  THE RECURSION, with every supplier as a hypothesis
-- of this nested module.
-- =====================================================================

module _
  (coded-arrow : (a : S) (oa : IsOrd (fst a)) → (IsCardinalL a → Empty.⊥)
               → Σ[ b ∈ S ] (⟨ fst b ∈ fst a ⟩ × (⟪ fst a ⟫ ↪ ⟪ fst b ⟫)))
  (amb-card-at-kappa : (a : S) (oa : IsOrd (fst a))
                     → AmbCard (fst (κL a oa)))
  (kappa-is-limit : (a : S) (oa : IsOrd (fst a)) → (γ : V ℓ)
                  → ⟨ γ ∈ fst (κL a oa) ⟩
                  → ⟨ sucV γ ∈ fst (κL a oa) ⟩)
  (amb-init' : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → ⟨ sucV ω ∈ α ⟩ → AmbCard α
             → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
             → Init α)
  (descent-core : (δ κ : S) → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫ → sq (fst κ)
                → ⟪ fst δ ⟫ ↪ ⟪ fst κ ⟫ → sq (fst δ))
  where

  -- The motive carries the ordinal certificate and the infinitude, and
  -- no band membership (no supplier reads one at a member).
  Goal : V ℓ → Type (ℓ-suc ℓ)
  Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

  -- No infinite ordinal injects into a finite one: shared by the two
  -- descent sites, and derived from the delivered `finite-excl-ω`.
  no-fin-descent : (x : V ℓ) → IsOrd x → ⟨ ω ∈ x ⟩
                 → (b : V ℓ) → ⟨ b ∈ x ⟩ → (⟪ x ⟫ ↪ ⟪ b ⟫)
                 → ⟨ b ∈ ω ⟩ → Empty.⊥
  no-fin-descent x ox ω∈x b b∈x down b∈ω =
    let ω↪b : ⟪ ω ⟫ ↪ ⟪ b ⟫
        ω↪b = comp-inj (mem-incl x ω ox ω∈x) down
    in finite-excl-ω b (mem-ord {A = x} ox b b∈x) b∈ω
         (λ t → fst ω↪b t , fst ω↪b t)
         (λ t u e → snd ω↪b t u (cong fst e))

  step : band-owes-2
       → (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
  step owes x ih ox infx = go (ord-tri x ox ω ω-ord)
    where
    a : S
    a = x , isL-ord x ox

    go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → sq x
    go (inl x∈ω) = Empty.rec (infx x∈ω)
    go (inr (inl x≡ω)) = subst sq (sym x≡ω) squareω
    go (inr (inr ω∈x)) = splitCard (lem (IsCardinalL a , isPropCardL a))
      where
      κ : S
      κ = κL a ox
      oκ : IsOrd (fst κ)
      oκ = κoL a ox

      -- the NEGATIVE case: `coded-arrow` hands the arrow over as data.
      by-coded : Σ[ b ∈ S ] (⟨ fst b ∈ x ⟩ × (⟪ x ⟫ ↪ ⟪ fst b ⟫)) → sq x
      by-coded (b , b∈x , down) =
        descent-core a b (mem-incl x (fst b) ox b∈x)
          (ih (fst b) b∈x (mem-ord {A = x} ox (fst b) b∈x)
             (no-fin-descent x ox ω∈x (fst b) b∈x down))
          down

      ω∈κ : fst κ ≡ x → ⟨ ω ∈ fst κ ⟩
      ω∈κ κ≡x = subst (λ w → ⟨ ω ∈ w ⟩) (sym κ≡x) ω∈x

      sω∈κ : fst κ ≡ x → ⟨ sucV ω ∈ fst κ ⟩
      sω∈κ κ≡x = kappa-is-limit a ox ω (ω∈κ κ≡x)

      membersq : fst κ ≡ x → (β : V ℓ) → IsOrd β → ⟨ β ∈ fst κ ⟩ → ⟨ ω ∈ β ⟩ → sq β
      membersq κ≡x β oβ β∈κ ω∈β =
        ih β (subst (λ w → ⟨ β ∈ w ⟩) κ≡x β∈κ) oβ (inf-member β ω∈β)

      -- the RESIDUE case: the arrow `band-owes-2` owes, then descent.
      by-residue : ⟪ x ⟫ ↪ ⟪ fst κ ⟫ → ⟨ fst κ ∈ x ⟩ → sq x
      by-residue down κ∈x =
        descent-core a κ (mem-incl x (fst κ) ox κ∈x)
          (ih (fst κ) κ∈x oκ (no-fin-descent x ox ω∈x (fst κ) κ∈x down))
          down

      -- the POSITIVE split: x is its own ambient least cardinal or not.
      splitOwn : IsCardinalL a → (fst κ ≡ x) ⊎ ⟨ fst κ ∈ x ⟩ → sq x
      splitOwn card (inl κ≡x) =
        subst sq κ≡x
          (via-col-square (fst κ)
            (amb-init' (fst κ) oκ (ω∈κ κ≡x) (sω∈κ κ≡x)
              (amb-card-at-kappa a ox) (membersq κ≡x)))
      splitOwn card (inr κ∈x) = by-residue (owes x ox ω∈x card κ∈x) κ∈x

      splitCard : IsCardinalL a ⊎ (IsCardinalL a → Empty.⊥) → sq x
      splitCard (inr nac) = by-coded (coded-arrow a ox nac)
      splitCard (inl card) = splitOwn card (kappa-decides a ox)

  sq-band-2 : band-owes-2
            → (x : V ℓ) → IsOrd x → ⟨ x ∈ sucV α₀ ⟩ → (⟨ x ∈ ω ⟩ → Empty.⊥)
            → sq x
  sq-band-2 owes x ox x∈suc infx = ∈-induction {P = Goal} (step owes) x ox infx

  -- ===================================================================
  -- PART 4.  THE CONSUMER MATCH, CHECKED MECHANICALLY.
  -- ===================================================================

  band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
  band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
    (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
    (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

  ConsumerShape : Type (ℓ-suc ℓ)
  ConsumerShape =
    (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
    → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
        ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)

  plugs-in : band-owes-2 → ConsumerShape
  plugs-in owes δ δ∈ infδ = sq-band-2 owes δ (band-ord δ δ∈) δ∈ infδ
