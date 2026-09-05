{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.349] MY OWN REBUILD OF THE [LJ-1.348] COUNTERMODEL.
--
-- I am the DD25 adversarial reviewer. The sibling standard ([LJ-1.345])
-- is to rebuild the countermodel rather than take the transcription.
-- This file transcribes BOTH tie types from src/L/Condensation.lagda.md
-- myself (WitnessAgree at :6683-6685, LeafAgree at :7233-7235, read
-- directly), rebuilds the countermodel from the frames I read in
-- src/L/Coding/Shape.lagda.md:182-187 and src/L/Coding/Model.lagda.md:2182-2195,
-- and inhabits the environment hypothesis independently.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.Induction.WellFounded using ( Acc; acc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit; tt )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

module LJ-1-349.Refute349 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM using ( prʟ; prʟ-fst; closedAt; binShapeAt; unShapeAt
             ; bothSameAt; oneSameAt; oneSuccAt; succSndAt
             ; binShape-in; unShape-in )
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Shape {ℓ}
  using ( shapedAt; shaped-in; ShapeWit; UnWit; zeroPay )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt )

open hPropStructure 𝒮ʟ using ( S )
module HV = hPropStructure 𝒮ᵥ

-- ====================================================================
-- PART 0. MY OWN CYCLE REFUTATION, ROTATED.
--
-- The target recursed on the accessibility of the FIRST element of the
-- chain. I recurse on the LAST, so the term is mine and not a copy: a
-- four step cycle d <- c <- b <- a <- d read backwards.
-- ====================================================================

cyc4 : (d : V ℓ) → Acc HV._∈ᵗ_ d → (a b c : V ℓ)
     → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ d ⟩ → ⟨ d ∈ a ⟩ → Empty.⊥
cyc4 d (acc rec) a b c ab bc cd da = cyc4 c (rec c cd) d a b da ab bc cd

-- The three ambient pair memberships, written from the axioms.
mem-pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
mem-pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

mem-pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
mem-pr x y =
  ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)

mem-only : (x d : V ℓ) → ⟨ d ∈ ⁅ x , x ⁆ ⟩ → d ≡ x
mem-only x d h =
  PT.rec (setIsSet d x) (λ { (inl p) → p ; (inr p) → p })
    (pairing-ax x x d .fst (∈∈ₛ {a = d} {b = ⁅ x , x ⁆} .fst h))

-- ====================================================================
-- PART 1. THE COUNTERMODEL, BUILT FROM MY OWN READING.
--
-- shapes (Shape.lagda.md:182-187), twelve disjuncts, read and counted:
--   tag 0  binForm 0 (bothTm A)   payload two term codes at A
--   tag 1  binForm 1 (bothTm A)   payload two term codes at A
--   tag 2  binForm 2 noneB        no constraint
--   tag 3  binForm 3 noneB        no constraint
--   tag 4  binForm 4 noneB        no constraint
--   tag 5  unForm 5 noneU         no constraint
--   tag 6  unForm 6 zeroPay       payload is # 0, ARITY FREE
--   tag 7  unForm 7 zeroPay       payload is # 0, ARITY FREE
--   tag 8  unForm 8 noneU         no constraint
--   tag 9  unForm 9 noneU         no constraint
--   tag 10 binForm 10 (fstTm A)   first payload a term code at A
--   tag 11 binForm 11 (fstTm A)   first payload a term code at A
-- No relation mentions the arity binder N. Tags 0, 1, 6 and 7 have no
-- closedAt clause (Model.lagda.md:2182-2195 speaks at 2, 3, 4, 5, 8,
-- 9, 10, 11 only). So tag 6 gives a shape with a FREE arity and no
-- closure demand, and the bound itself can occupy the slot.
-- ====================================================================

module Mine {n : ℕ} (A Ki xi : Fin n) (γ : S ^ n)
  (hx : fst (lookup xi γ) ≡ pr (fst (lookup Ki γ)) (pr (# 6) (# 0))) where

  bound : S
  bound = lookup Ki γ

  bb : V ℓ
  bb = fst bound

  -- the tag 6 shape, arity the bound, payload # 0
  shape : S
  shape = prʟ bound (prʟ (numeralL 6) (numeralL 0))

  flat : fst shape ≡ pr bb (pr (# 6) (# 0))
  flat = prʟ-fst bound (prʟ (numeralL 6) (numeralL 0))
       ∙ cong (λ u → pr bb u)
           (prʟ-fst (numeralL 6) (numeralL 0)
            ∙ cong₂ pr (numeralL-fst 6) (numeralL-fst 0))

  -- the witness set, the singleton of that one shape
  W : S
  W = pairʟ shape shape

  W-flat : fst W ≡ ⁅ fst shape , fst shape ⁆
  W-flat = pairʟ-fst shape shape

  shape∈W : ⟨ fst shape ∈ fst W ⟩
  shape∈W = subst (λ u → ⟨ fst shape ∈ u ⟩) (sym W-flat) (mem-pair _ _)

  only-shape : (e : S) → ⟨ fst e ∈ fst W ⟩ → fst e ≡ fst shape
  only-shape e h = mem-only (fst shape) (fst e)
                     (subst (λ u → ⟨ fst e ∈ u ⟩) W-flat h)

  -- every member of W is tag 6, so a tag k clause with k <> 6 is empty
  wrongTag : (e ar : S) (k : ℕ) (rest : V ℓ)
           → ⟨ fst e ∈ fst W ⟩
           → fst e ≡ pr (fst ar) (pr (# k) rest) → 6 ≡ k
  wrongTag e ar k rest he q =
    #-inj 6 k (pr-inj (pr-inj (sym (only-shape e he ∙ flat) ∙ q) .snd) .fst)

  No6 : ℕ → Type
  No6 6 = Empty.⊥
  No6 _ = Unit

  refuse : (k : ℕ) → No6 k → (e ar : S) (rest : V ℓ)
         → ⟨ fst e ∈ fst W ⟩ → fst e ≡ pr (fst ar) (pr (# k) rest)
         → Empty.⊥
  refuse k nk e ar rest he q =
    subst No6 (sym (wrongTag e ar k rest he q)) nk

  -- closedness: all eight clauses, each refused at its own tag
  closedW : ⟨ (W ∷ γ) ⊨ closedAt zero ⟩
  closedW =
    ( binShape-in zero 2 (bothSameAt zero) (W ∷ γ)
        (λ e ar a b he q → Empty.rec (refuse 2 tt e ar (pr (fst a) (fst b)) he q))
    , ( binShape-in zero 3 (bothSameAt zero) (W ∷ γ)
        (λ e ar a b he q → Empty.rec (refuse 3 tt e ar (pr (fst a) (fst b)) he q))
    , ( binShape-in zero 4 (bothSameAt zero) (W ∷ γ)
        (λ e ar a b he q → Empty.rec (refuse 4 tt e ar (pr (fst a) (fst b)) he q))
    , ( unShape-in zero 5 (oneSameAt zero) (W ∷ γ)
        (λ e ar a he q → Empty.rec (refuse 5 tt e ar (fst a) he q))
    , ( unShape-in zero 8 (oneSuccAt zero) (W ∷ γ)
        (λ e ar a he q → Empty.rec (refuse 8 tt e ar (fst a) he q))
    , ( unShape-in zero 9 (oneSuccAt zero) (W ∷ γ)
        (λ e ar a he q → Empty.rec (refuse 9 tt e ar (fst a) he q))
    , ( binShape-in zero 10 (succSndAt zero) (W ∷ γ)
        (λ e ar a b he q → Empty.rec (refuse 10 tt e ar (pr (fst a) (fst b)) he q))
    , binShape-in zero 11 (succSndAt zero) (W ∷ γ)
        (λ e ar a b he q → Empty.rec (refuse 11 tt e ar (pr (fst a) (fst b)) he q))
    ) ) ) ) ) ) )

  -- shapedness: the sixth disjunct, and A is never used
  shapedW : ⟨ (W ∷ γ) ⊨ shapedAt zero (suc A) ⟩
  shapedW = shaped-in zero (suc A) (W ∷ γ) fill
    where
    sixth : (e : S) → ⟨ fst e ∈ fst W ⟩ → UnWit 6 zeroPay (W ∷ γ) e
    sixth e he = bound , ( numeralL 0
        , ( only-shape e he ∙ flat
            ∙ cong (λ u → pr bb (pr (# 6) u)) (sym (numeralL-fst 0))
          , refl ) )
    fill : (e : S) → ⟨ fst e ∈ fst W ⟩ → ∥ ShapeWit (suc A) (W ∷ γ) e ∥₁
    fill e he =
      ∣ inr (inr (inr (inr (inr (inr (inl (sixth e he))))))) ∣₁

  -- the premise, as one term, at W
  read∈W : ⟨ fst (lookup xi γ) ∈ fst W ⟩
  read∈W = subst (λ u → ⟨ u ∈ fst W ⟩) (sym (hx ∙ sym flat)) shape∈W

  premiseW : ⟨ (W ∷ γ) ⊨ ((var (suc xi) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
  premiseW = read∈W , ( closedW , shapedW )

  Tie : Type (ℓ-suc ℓ)
  Tie = (u : S) → ⟨ (u ∷ γ) ⊨ ((var (suc xi) ∈̇ var zero)
              ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
       → ⟨ fst u ∈ fst (lookup Ki γ) ⟩

  -- the refutation: bb in {bb, pr 6 0} in fst shape in fst W in bb
  tie-broken : Tie → Empty.⊥
  tie-broken h = cyc4 (fst W) (regularityV (fst W)) bb ⁅ bb , pr (# 6) (# 0) ⁆
    (fst shape)
    (mem-pair bb (pr (# 6) (# 0)))
    (subst (λ u → ⟨ ⁅ bb , pr (# 6) (# 0) ⁆ ∈ u ⟩) (sym flat)
       (mem-pr bb (pr (# 6) (# 0))))
    shape∈W
    (h W premiseW)

-- ====================================================================
-- PART 2. NON-VACUITY, MY OWN ENVIRONMENT.
--
-- hx asks the read slot to hold the shape. I build a two slot
-- environment from an ARBITRARY carrier element: slot 0 the shape,
-- slot 1 the bound. The carrier slot can be either; tag 6 does not
-- read it.
-- ====================================================================

module Live349 (Any : S) where

  shp : S
  shp = prʟ Any (prʟ (numeralL 6) (numeralL 0))

  env : S ^ 2
  env = shp ∷ Any ∷ []

  hx-live : fst (lookup zero env) ≡ pr (fst (lookup (suc zero) env)) (pr (# 6) (# 0))
  hx-live = prʟ-fst Any (prʟ (numeralL 6) (numeralL 0))
          ∙ cong (λ u → pr (fst Any) u)
              (prʟ-fst (numeralL 6) (numeralL 0)
               ∙ cong₂ pr (numeralL-fst 6) (numeralL-fst 0))

  module M = Mine {2} (suc zero) (suc zero) zero env hx-live

  empty-here : M.Tie → Empty.⊥
  empty-here = M.tie-broken

  -- THE STRONGER FACT, and it is the one that closes the last escape:
  -- the countermodel environment is INSIDE the chapter's intended
  -- premise class, because `WitnessAgree.out` consumes exactly
  -- `hasWitnessAt A x` and my W is one of its witnesses.
  intended : ⟨ env ⊨ hasWitnessAt (suc zero) zero ⟩
  intended = ∣ M.W , M.premiseW ∣₁

-- ====================================================================
-- PART 3. THE CHAPTER'S OWN TWO INDEX FORMS, TRANSCRIBED BY ME.
--
-- WitnessAgree (src/L/Condensation.lagda.md:6683-6685) and LeafAgree
-- (:7233-7235), copied from the source I read, not from [LJ-1.348].
-- ====================================================================

module Forms {n : ℕ} where

  WForm : (A x K : Fin n) (γ : S ^ n) → Type (ℓ-suc ℓ)
  WForm A x K γ =
    (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
                 ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
    → ⟨ fst w ∈ fst (lookup K γ) ⟩

  wform-false : (A x K : Fin n) (γ : S ^ n)
    → fst (lookup x γ) ≡ pr (fst (lookup K γ)) (pr (# 6) (# 0))
    → WForm A x K γ → Empty.⊥
  wform-false A x K γ hx = Mine.tie-broken A K x γ hx

  LForm : (w K : Fin (5 + n)) (γ : S ^ (8 + n)) → Type (ℓ-suc ℓ)
  LForm w K γ =
    (w' : S) → ⟨ (w' ∷ γ) ⊨ ((var (suc (suc zero)) ∈̇ var zero)
                 ∧̇ (closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w)))))) ⟩
    → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩

  lform-false : (w K : Fin (5 + n)) (γ : S ^ (8 + n))
    → fst (lookup (suc zero) γ)
      ≡ pr (fst (lookup (suc (suc (suc K))) γ)) (pr (# 6) (# 0))
    → LForm w K γ → Empty.⊥
  lform-false w K γ hx =
    Mine.tie-broken (suc (suc (suc w))) (suc (suc (suc K))) (suc zero) γ hx
