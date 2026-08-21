{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.436] PROBE.  Stage-cardinal induction at a TRUNCATED conclusion.
-- It runs in agents/tasks/LJ-1-436/ and lands nothing in src/.
--
--   W3 FIRST  `branch-trunc`.  The chapter's `branch`
--             (src/L/StageCardinal.lagda.md:534-536) with the motive
--             truncated and NOTHING else changed.  Stated alone, with
--             the obligation omitted, and run before anything else.
--
--   The finite case of `go` does not use the motive.  The ω case and
--   the infinite case apply the induction hypothesis.  With P! that
--   application is a truncation, and `comp-inj` wants an injection as
--   data.  `open-ih` is the one untruncation those two cases spend.
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
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-436.Probe436 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( #-inj′ )
open import L.Constructible {ℓ} using ( Lset )
open import L.Ordinal {ℓ}
  using ( #∈ω; mem-ord; ω-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Choice.Finite {ℓ} lem
  using ( Tally; StageOrder; stageOrder; finiteStage; natOrder )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( leastOf )
open InfinitySet using ( ω; sucV; #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma.Properties using ( Σ≡Prop )
open import Cubical.Data.FinData.Base using ( Fin; toℕ )
open import Cubical.Data.FinData.Properties using ( inj-toℕ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE MOTIVE, the chapter's P (src/L/StageCardinal.lagda.md:530-532)
-- with ONE truncation around its Sigma and nothing else changed.
-- =====================================================================

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

P! : S → Type (ℓ-suc ℓ)
P! α = IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
     → ∥ Σ[ f ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ]
           ((u v : ⟪ Lset α ⟫) → f u ≡ f v → u ≡ v) ∥₁

-- =====================================================================
-- PLUMBING from the chapter that does not mention the motive:
-- `comp-inj` (:500), `Emb` (:504), `WOEmb` (:518), `fin-inj` (:488).
-- Copied, not imported: opening `L.StageCardinal` demands the
-- untruncated pairing as a module parameter
-- (src/L/StageCardinal.lagda.md:17-19), and this probe takes no
-- pairing as data.
-- =====================================================================

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

module Emb (α : S) (oα : IsOrd α) where

  emb : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ⟪ δ ⟫ ↪ ⟪ α ⟫
  emb δ δ∈α = f , inj
    where
    f : ⟪ δ ⟫ → ⟪ α ⟫
    f m = fiber α {x = ⟪ δ ⟫↪ m} (oα .fst (member δ m) δ∈α) .fst
    inj : (m n : ⟪ δ ⟫) → f m ≡ f n → m ≡ n
    inj m n e = ↪-inj {a = δ}
      (sym (fiber α {x = ⟪ δ ⟫↪ m} (oα .fst (member δ m) δ∈α) .snd)
        ∙ cong (⟪ α ⟫↪) e
        ∙ fiber α {x = ⟪ δ ⟫↪ n} (oα .fst (member δ n) δ∈α) .snd)

module WOEmb (α : S) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  id-inj : ⟪ ω ⟫ ↪ ⟪ ω ⟫
  id-inj = (λ x → x) , λ x y p → p

  ω-inj : ⟪ ω ⟫ ↪ ⟪ α ⟫
  ω-inj = go (ord-tri ω ω-ord α oα)
    where
    go : ⟨ ω ∈ˢ α ⟩ ⊎ ((ω ≡ α) ⊎ ⟨ α ∈ˢ ω ⟩) → ⟪ ω ⟫ ↪ ⟪ α ⟫
    go (inl ω∈α) = Emb.emb α oα ω ω∈α
    go (inr (inl e)) = subst (λ A → ⟪ ω ⟫ ↪ ⟪ A ⟫) e id-inj
    go (inr (inr α∈ω)) = Empty.rec (infα α∈ω)

dne : (P : hProp (ℓ-suc ℓ)) → (((⟨ P ⟩) → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
dne P h = Sum.rec (λ p → p) (λ np → Empty.rec (h np)) (lem P)

extract : {A : Type (ℓ-suc ℓ)} (pA : isProp A) → ∥ A ∥₁ → A
extract {A} pA h = dne (A , pA) λ nA → PT.rec Empty.isProp⊥ nA h

ω-mem→numeral : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ∥ Σ[ n ∈ ℕ ] (# n ≡ δ) ∥₁
ω-mem→numeral δ δ∈ω = PT.map (λ { (k , q) → lower k , q }) δ∈ω

isPropNumeralWit : (δ : S) → isProp (Σ[ n ∈ ℕ ] (# n ≡ δ))
isPropNumeralWit δ (n , p) (n' , p') =
  Σ≡Prop (λ k → isSetS (# k) δ) (#-inj′ (p ∙ sym p'))

numeral-wit : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → Σ[ n ∈ ℕ ] (# n ≡ δ)
numeral-wit δ δ∈ω = extract (isPropNumeralWit δ) (ω-mem→numeral δ δ∈ω)

numeralω : ℕ → ⟪ ω ⟫
numeralω k = fiber ω {x = # k} (#∈ω k) .fst

numeralω-inj : (k k' : ℕ) → numeralω k ≡ numeralω k' → k ≡ k'
numeralω-inj k k' e = #-inj′ (sym (fiber ω {x = # k} (#∈ω k) .snd)
  ∙ cong (⟪ ω ⟫↪) e ∙ fiber ω {x = # k'} (#∈ω k') .snd)

module FinInj (n : ℕ) (t : Tally (finiteStage n)) where

  open Tally t

  P : S → ℕ → hProp (ℓ-suc ℓ)
  P x k = ( ∥ Σ[ i ∈ Fin size ] ((toℕ i ≡ k) × (item i ≡ x)) ∥₁
          , squash₁ )

  nonempty : (x : S) → ⟨ x ∈ˢ finiteStage n ⟩
           → ∥ Σ[ k ∈ ℕ ] ⟨ P x k ⟩ ∥₁
  nonempty x x∈ = PT.map (λ { (i , q) → toℕ i , ∣ i , (refl , q) ∣₁ })
                          (onto x x∈)

  least : (x : S) → ⟨ x ∈ˢ finiteStage n ⟩ → ℕ
  least x x∈ = fst (leastOf natOrder lem (P x) (nonempty x x∈))

  least-wit : (x : S) (x∈ : ⟨ x ∈ˢ finiteStage n ⟩) → ⟨ P x (least x x∈) ⟩
  least-wit x x∈ = leastOf natOrder lem (P x) (nonempty x x∈) .snd .fst

  h : (x : S) → ⟨ x ∈ˢ finiteStage n ⟩ → ⟪ ω ⟫
  h x x∈ = numeralω (least x x∈)

  h-inj : (x y : S) (x∈ : ⟨ x ∈ˢ finiteStage n ⟩) (y∈ : ⟨ y ∈ˢ finiteStage n ⟩)
        → h x x∈ ≡ h y y∈ → x ≡ y
  h-inj x y x∈ y∈ e =
    PT.rec (isSetS x y) (λ wx → PT.rec (isSetS x y) (go wx) (least-wit y y∈))
      (least-wit x x∈)
    where
    ek : least x x∈ ≡ least y y∈
    ek = numeralω-inj (least x x∈) (least y y∈) e
    go : Σ[ i ∈ Fin size ] ((toℕ i ≡ least x x∈) × (item i ≡ x))
       → Σ[ j ∈ Fin size ] ((toℕ j ≡ least y y∈) × (item j ≡ y))
       → x ≡ y
    go (i , pi , qi) (j , pj , qj) =
      sym qi ∙ cong item (inj-toℕ (pi ∙ ek ∙ sym pj)) ∙ qj

  stage-inj : ⟪ finiteStage n ⟫ ↪ ⟪ ω ⟫
  stage-inj = f , inj
    where
    f : ⟪ finiteStage n ⟫ → ⟪ ω ⟫
    f m = h (⟪ finiteStage n ⟫↪ m) (member (finiteStage n) m)
    inj : (m m' : ⟪ finiteStage n ⟫) → f m ≡ f m' → m ≡ m'
    inj m m' e = ↪-inj {a = finiteStage n}
      (h-inj (⟪ finiteStage n ⟫↪ m) (⟪ finiteStage n ⟫↪ m')
        (member (finiteStage n) m) (member (finiteStage n) m') e)

finite-stage-inj : (n : ℕ) → ⟪ Lset (# n) ⟫ ↪ ⟪ ω ⟫
finite-stage-inj n = FinInj.stage-inj n (StageOrder.tally (stageOrder n))

fin-inj : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫
fin-inj δ δ∈ω = subst (λ w → ⟪ Lset w ⟫ ↪ ⟪ ω ⟫)
  (numeral-wit δ δ∈ω .snd) (finite-stage-inj (numeral-wit δ δ∈ω .fst))

-- =====================================================================
-- W3.  `branch-trunc`, the chapter's `branch` with P replaced by P!.
--
-- The finite case (`go (inl _)`) spends `fin-inj` and does not read
-- the induction hypothesis.  The other two cases read it.  With P!
-- that reading is a truncation.  `open-ih` is the untruncation those
-- two cases need, and it is the hole.  `PT.rec` would fill it iff
-- `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` were an hProp.  It is a Sigma of a function.
-- =====================================================================

open-ih :
    {δ : S}
  → ∥ Σ[ f ∈ (⟪ Lset δ ⟫ → ⟪ δ ⟫) ]
         ((u v : ⟪ Lset δ ⟫) → f u ≡ f v → u ≡ v) ∥₁
  → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
open-ih {δ} h = PT.rec {A = ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫} goal (λ x → x) h
  where
  goal : isProp (⟪ Lset δ ⟫ ↪ ⟪ δ ⟫)
  goal = {!!}

branch-trunc :
    (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P! δ)
  → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
branch-trunc α oα α∈suc infα IH m = go (ord-tri δ oδ ω ω-ord)
  where
  δ : S
  δ = ⟪ α ⟫↪ m
  δ∈α : ⟨ δ ∈ˢ α ⟩
  δ∈α = member α m
  oδ : IsOrd δ
  oδ = mem-ord {A = α} oα δ δ∈α
  δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩
  δ∈suc = suc-ord oα₀ .fst {x = α} {y = δ} δ∈α α∈suc
  go : ⟨ δ ∈ˢ ω ⟩ ⊎ ((δ ≡ ω) ⊎ ⟨ ω ∈ˢ δ ⟩) → ⟪ Lset δ ⟫ ↪ ⟪ α ⟫
  go (inl δ∈ω) = comp-inj (fin-inj δ δ∈ω) (WOEmb.ω-inj α oα infα)
  go (inr (inl e)) = subst (λ w → ⟪ Lset w ⟫ ↪ ⟪ α ⟫) (sym e)
    (comp-inj (open-ih (IH ω (subst (λ w → ⟨ w ∈ˢ α ⟩) e δ∈α) ω-ord ω∈suc (∈-irrefl ω)))
              (WOEmb.ω-inj α oα infα))
    where
    ω∈suc : ⟨ ω ∈ˢ sucV α₀ ⟩
    ω∈suc = subst (λ w → ⟨ w ∈ˢ sucV α₀ ⟩) e δ∈suc
  go (inr (inr ω∈δ)) =
    comp-inj (open-ih (IH δ δ∈α oδ δ∈suc infδ)) (Emb.emb α oα δ δ∈α)
    where
    infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥
    infδ h = ∈-irrefl ω (ω-ord .fst ω∈δ h)

-- The swap of a Pi and a truncation over the members of an ordinal.
-- HoTT Book 3.8.1 at this index (dev/literature/truncation-and-selection.md:226).
-- Named, not postulated, not inhabited.  This is the type a NO-GO
-- delivers to [LJ-2.5].  It does not inhabit `branch-trunc`: that
-- term wants the untruncated Pi.  It would serve `step-trunc` if
-- `limit-step` ran under `PT.rec`, because `P! α` is an hProp.
PiTruncSwap : Type (ℓ-suc ℓ)
PiTruncSwap =
  (α : S) (Y : ⟪ α ⟫ → Type ℓ)
  → ((m : ⟪ α ⟫) → ∥ Y m ∥₁)
  → ∥ ((m : ⟪ α ⟫) → Y m) ∥₁

-- THE OBLIGATION.  W3 did not close.  The body is a hole.  The repair
-- is a limit step that consumes a pointwise truncated branch family,
-- owed at [LJ-1.435], whose report is not in this tree.
step-trunc :
    (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P! δ) → P! α
step-trunc = {!!}
