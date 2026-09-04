# The internal table inside a stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.TableIn {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim; pair-singleton )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset→isL; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; Recorded )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; sucIter-ord; +ω; +ω-mem; +ω-iter; +ω-sup; +ω-ord; closedω )
open import L.Axioms.Basic {ℓ}
  using ( LsetS; Lset-suc; pair∈Lset-suc; sgl∈Lset-suc; pr∈Lset-suc )
open import L.Coding.Bound {ℓ} lem using ( Lset-out′ )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈; union∈Lset-suc )
open import L.GCH.Placement {ℓ} lem using ( sucIter-in-γ )

open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; _⊆_; ∈∈ₛ; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax; ⋃_; union-ax
        ; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
-- `_∈ˢ_` below is the V structure's membership; `SL` is the L carrier.
open hPropStructure 𝒮ᵥ hiding ( S )
open hPropStructure 𝒮ʟ using () renaming ( S to SL )

-- =====================================================================
-- SECTION 0.  A stage is a member of the next stage.
--
--   `Lset β` is the definable subset of itself that `⊤̇` carves out, so
--   it lies in `𝒟ₒ (Lset β)`, and that operator is the next stage.
-- =====================================================================

Lset∈suc : (β : V ℓ) → ⟨ Lset β ∈ˢ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ˢ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

-- =====================================================================
-- SECTION 1.  The ω-block above p, and what lands in Lset (+ω p).
--
--   `Below x` is the reason an ordinal x is a member of +ω p: either x
--   is below p, or x is one of the finite iterates above p.  The
--   predicate is closed under successor, which +ω p alone does not
--   give: `Closer.suc∈γ` asks for closedω, and closedω (+ω p) is false.
-- =====================================================================

module Blocks (p : V ℓ) (op : IsOrd p) where

  Below : V ℓ → Type (ℓ-suc ℓ)
  Below x = ⟨ x ∈ˢ p ⟩ ⊎ (Σ[ j ∈ ℕ ] (x ≡ sucIter j p))

  below-p : Below p
  below-p = inr (0 , refl)

  below-in : (x : V ℓ) → Below x → ⟨ x ∈ˢ +ω p ⟩
  below-in x (inl x∈) = +ω-sup p x x∈
  below-in x (inr (j , q)) =
    subst (λ w → ⟨ w ∈ˢ +ω p ⟩) (sym q) (+ω-iter j p)

  below-suc : (x : V ℓ) → IsOrd x → Below x → Below (sucV x)
  below-suc x ox (inl x∈) =
    Sum.rec inl (λ q → inr (0 , q)) (suc∈or≡ x p ox op x∈)
  below-suc x ox (inr (j , q)) = inr (suc j , cong sucV q)

  below-iter : (x : V ℓ) → IsOrd x → Below x → (n : ℕ) → Below (sucIter n x)
  below-iter x ox b zero = b
  below-iter x ox b (suc n) =
    below-suc (sucIter n x) (sucIter-ord n ox) (below-iter x ox b n)

  -- The stage bound: anything at a stage `Below` lands in Lset (+ω p).
  below-Lset : (x : V ℓ) → Below x → (y : V ℓ)
             → ⟨ y ∈ˢ Lset x ⟩ → ⟨ y ∈ˢ Lset (+ω p) ⟩
  below-Lset x b y y∈ = Lset-mono {α = +ω p} {β = x} (below-in x b) y∈

  -- p itself, and the stage at p, are members of the stage at +ω p.
  p∈+ω : ⟨ p ∈ˢ Lset (+ω p) ⟩
  p∈+ω = below-Lset (sucV p) (inr (1 , refl)) p (ord∈Lset-suc p op)

  Lp∈+ω : ⟨ Lset p ∈ˢ Lset (+ω p) ⟩
  Lp∈+ω = below-Lset (sucV p) (inr (1 , refl)) (Lset p) (Lset∈suc p)

  -- ω needs ω ≤ p.  At p ∈ ω the statement is FALSE: +ω p is then ω,
  -- and no ordinal of Lset ω is ω itself.
  below-ω : (⟨ ω ∈ˢ p ⟩ ⊎ (ω ≡ p)) → Below ω
  below-ω (inl q) = inl q
  below-ω (inr q) = inr (0 , q)

  ω∈+ω : (⟨ ω ∈ˢ p ⟩ ⊎ (ω ≡ p)) → ⟨ ω ∈ˢ Lset (+ω p) ⟩
  ω∈+ω h = below-Lset (sucV ω) (below-suc ω ω-ord (below-ω h)) ω
    (ord∈Lset-suc ω ω-ord)
```

```agda
-- =====================================================================
-- SECTION 2.  The environment sets over a stage at or below p.
--
--   `envSetNumeral∈` bounds envSet w n at four iterates above any
--   stage that holds w and holds ω.  The bound does NOT depend on n.
--   The route of `envSet-in-carrier-lim` (src/L/GCH/Placement.lagda.md
--   :285) cannot be used here: it inflates the stage by +ω twice, and
--   +ω (+ω c) is never a member of +ω p.  The tight stage is a finite
--   iterate, and `below-iter` carries a finite iterate into +ω p.
-- =====================================================================

module _ (p : V ℓ) (op : IsOrd p) where

  open Blocks p op

  envSet-in : (c : V ℓ) (oc : IsOrd c) → Below c
            → (⟨ ω ∈ˢ p ⟩ ⊎ (ω ≡ p))
            → (n : ℕ)
            → ⟨ fst (envSet (LsetS c oc) n) ∈ˢ Lset (+ω p) ⟩
  envSet-in c oc bc hω n = resolve (ord-tri ω ω-ord c oc)
    where
    -- The stage is chosen so that it holds ω and holds Lset c.
    at : (σ : V ℓ) → IsOrd σ → Below σ → ⟨ ω ∈ˢ σ ⟩ → ⟨ Lset c ∈ˢ Lset σ ⟩
       → ⟨ fst (envSet (LsetS c oc) n) ∈ˢ Lset (+ω p) ⟩
    at σ oσ bσ ω∈σ hB =
      below-Lset (sucIter 4 σ) (below-iter σ oσ bσ 4)
        (fst (envSet (LsetS c oc) n))
        (envSetNumeral∈ σ oσ ω∈σ (LsetS c oc) n hB)

    -- ω below c: the stage after c already holds both.
    high : ⟨ ω ∈ˢ c ⟩ → ⟨ fst (envSet (LsetS c oc) n) ∈ˢ Lset (+ω p) ⟩
    high ω∈c = at (sucV c) (suc-ord oc) (below-suc c oc bc)
      (∈sucV-inl ω∈c) (Lset∈suc c)

    -- c at or below ω: the stage after ω holds both.
    low : ⟨ Lset c ∈ˢ Lset (sucV ω) ⟩
        → ⟨ fst (envSet (LsetS c oc) n) ∈ˢ Lset (+ω p) ⟩
    low hB = at (sucV ω) (suc-ord ω-ord)
      (below-suc ω ω-ord (below-ω hω)) (self∈sucV ω) hB

    eq-case : ω ≡ c → ⟨ Lset c ∈ˢ Lset (sucV ω) ⟩
    eq-case q = subst (λ w → ⟨ Lset c ∈ˢ Lset (sucV w) ⟩) (sym q) (Lset∈suc c)

    lt-case : ⟨ c ∈ˢ ω ⟩ → ⟨ Lset c ∈ˢ Lset (sucV ω) ⟩
    lt-case c∈ω = Lset-mono {α = sucV ω} {β = sucV c} succ∈ (Lset∈suc c)
      where
      succ∈ : ⟨ sucV c ∈ˢ sucV ω ⟩
      succ∈ = Sum.rec ∈sucV-inl
        (λ q → subst (λ w → ⟨ w ∈ˢ sucV ω ⟩) (sym q) (self∈sucV ω))
        (suc∈or≡ c ω oc ω-ord c∈ω)

    resolve : Tri ω c → ⟨ fst (envSet (LsetS c oc) n) ∈ˢ Lset (+ω p) ⟩
    resolve (inl ω∈c) = high ω∈c
    resolve (inr (inl ω≡c)) = low (eq-case ω≡c)
    resolve (inr (inr c∈ω)) = low (lt-case c∈ω)
```

```agda
-- =====================================================================
-- SECTION 3.  The successor step of the internal table.
--
--   `hierL p` is the set of pairs ⟨c, Lset c⟩ for c ∈ p.  At a
--   successor p = sucV c the table is the table at c with one pair
--   adjoined, and the adjunction is a union of two members of a stage.
--   The equality is read off `IsHier` in both directions: nothing here
--   is a definable subset, so nothing here needs the level formula.
-- =====================================================================

module Successor (c : V ℓ) (hc : ⟨ isL c ⟩) (oc : IsOrd c)
                 (hsc : ⟨ isL (sucV c) ⟩) where

  private
    Hc : SL
    Hc = hierL c hc oc

    Hs : SL
    Hs = hierL (sucV c) hsc (suc-ord oc)

    H : V ℓ
    H = fst Hc

    -- The one pair the successor adjoins.
    P : V ℓ
    P = pr c (Lset c)

    U : V ℓ
    U = ⋃ ⁅ H , ⁅ P ⁆s ⁆

    spc = hierL-spec c hc oc
    sps = hierL-spec (sucV c) hsc (suc-ord oc)

    -- The pair sits three iterates above c, so it is constructible.
    P∈ : ⟨ P ∈ˢ Lset (sucIter 3 c) ⟩
    P∈ = pr∈Lset-suc (sucV c) c (Lset c) (ord∈Lset-suc c oc) (Lset∈suc c)

    isL-P : ⟨ isL P ⟩
    isL-P = Lset→isL (sucIter 3 c) (sucIter-ord 3 oc) P P∈

    -- Into the union: through the left member, or through the singleton.
    in-H : (v : V ℓ) → ⟨ v ∈ˢ H ⟩ → ⟨ v ∈ₛ U ⟩
    in-H v v∈ = union-ax ⁅ H , ⁅ P ⁆s ⁆ v .snd
      ∣ H , ( pairing-ax H ⁅ P ⁆s H .snd ∣ inl refl ∣₁
            , ∈∈ₛ {a = v} {b = H} .fst v∈ ) ∣₁

    in-P : (v : V ℓ) → v ≡ P → ⟨ v ∈ₛ U ⟩
    in-P v q = union-ax ⁅ H , ⁅ P ⁆s ⁆ v .snd
      ∣ ⁅ P ⁆s , ( pairing-ax H ⁅ P ⁆s ⁅ P ⁆s .snd ∣ inr refl ∣₁
                 , v∈sgl ) ∣₁
      where
      v∈sgl : ⟨ v ∈ₛ ⁅ P ⁆s ⟩
      v∈sgl = subst (λ w → ⟨ v ∈ₛ w ⟩) (pair-singleton P)
        (pairing-ax P P v .snd ∣ inl q ∣₁)

    sgl-out : (v : V ℓ) → ⟨ v ∈ₛ ⁅ P ⁆s ⟩ → v ≡ P
    sgl-out v h = PT.rec (setIsSet v P) (Sum.rec (λ e → e) (λ e → e))
      (pairing-ax P P v .fst
        (subst (λ w → ⟨ v ∈ₛ w ⟩) (sym (pair-singleton P)) h))

    -- The table at sucV c is inside the union.
    sub₁ : ⟨ fst Hs ⊆ U ⟩
    sub₁ v v∈ₛ = ∈∈ₛ {a = v} {b = U} .fst
      (PT.rec (snd (v ∈ˢ U)) step rec)
      where
      v∈ : ⟨ v ∈ˢ fst Hs ⟩
      v∈ = ∈∈ₛ {a = v} {b = fst Hs} .snd v∈ₛ
      z : SL
      z = v , isL-trans {x = fst Hs} {y = v} v∈ (snd Hs)
      rec : ⟨ Recorded (sucV c) v ⟩
      rec = subst ⟨_⟩ (sps z) v∈
      step : Σ[ d ∈ SL ] (⟨ fst d ∈ˢ sucV c ⟩
               × (v ≡ pr (fst d) (Lset (fst d))))
           → ⟨ v ∈ˢ U ⟩
      step (d , (d∈ , q)) =
        ∈sucV-elim {A = c} {x = fst d} (snd (v ∈ˢ U)) d∈ kA k≡
        where
        kA : ⟨ fst d ∈ˢ c ⟩ → ⟨ v ∈ˢ U ⟩
        kA h = ∈∈ₛ {a = v} {b = U} .snd
          (in-H v (subst ⟨_⟩ (sym (spc z)) ∣ d , (h , q) ∣₁))
        k≡ : fst d ≡ c → ⟨ v ∈ˢ U ⟩
        k≡ e = ∈∈ₛ {a = v} {b = U} .snd
          (in-P v (q ∙ cong (λ w → pr w (Lset w)) e))

    -- The union is inside the table at sucV c.
    sub₂ : ⟨ U ⊆ fst Hs ⟩
    sub₂ v v∈ₛU = PT.rec (snd (v ∈ₛ fst Hs)) fromPair
      (union-ax ⁅ H , ⁅ P ⁆s ⁆ v .fst v∈ₛU)
      where
      fromH : ⟨ v ∈ˢ H ⟩ → ⟨ v ∈ₛ fst Hs ⟩
      fromH h = ∈∈ₛ {a = v} {b = fst Hs} .fst
        (subst ⟨_⟩ (sym (sps z)) (PT.map raise (subst ⟨_⟩ (spc z) h)))
        where
        z : SL
        z = v , isL-trans {x = H} {y = v} h (snd Hc)
        raise : Σ[ d ∈ SL ] (⟨ fst d ∈ˢ c ⟩
                  × (v ≡ pr (fst d) (Lset (fst d))))
              → Σ[ d ∈ SL ] (⟨ fst d ∈ˢ sucV c ⟩
                  × (v ≡ pr (fst d) (Lset (fst d))))
        raise (d , (d∈ , q)) = d , (∈sucV-inl d∈ , q)

      fromP : v ≡ P → ⟨ v ∈ₛ fst Hs ⟩
      fromP q = ∈∈ₛ {a = v} {b = fst Hs} .fst
        (subst ⟨_⟩ (sym (sps z)) ∣ (c , hc) , (self∈sucV c , q) ∣₁)
        where
        z : SL
        z = v , subst (λ w → ⟨ isL w ⟩) (sym q) isL-P

      fromPair : Σ[ b ∈ V ℓ ] (⟨ b ∈ₛ ⁅ H , ⁅ P ⁆s ⁆ ⟩ × ⟨ v ∈ₛ b ⟩)
               → ⟨ v ∈ₛ fst Hs ⟩
      fromPair (b , (b∈ , v∈b)) = PT.rec (snd (v ∈ₛ fst Hs)) which
        (pairing-ax H ⁅ P ⁆s b .fst b∈)
        where
        which : (b ≡ H) ⊎ (b ≡ ⁅ P ⁆s) → ⟨ v ∈ₛ fst Hs ⟩
        which (inl e) = fromH
          (∈∈ₛ {a = v} {b = H} .snd (subst (λ w → ⟨ v ∈ₛ w ⟩) e v∈b))
        which (inr e) = fromP
          (sgl-out v (subst (λ w → ⟨ v ∈ₛ w ⟩) e v∈b))

  -- THE SUCCESSOR IDENTITY.
  table-suc : fst Hs ≡ U
  table-suc = extensionality (fst Hs) U (sub₁ , sub₂)

  table-union : fst (hierL (sucV c) hsc (suc-ord oc))
              ≡ ⋃ ⁅ fst (hierL c hc oc) , ⁅ pr c (Lset c) ⁆s ⁆
  table-union = table-suc
```

```agda
-- =====================================================================
-- SECTION 4.  Placement of the successor step in a closed stage.
-- =====================================================================

-- Two members of a closed stage share a stage inside it.
common : (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) (x y : V ℓ)
       → ⟨ x ∈ˢ Lset γ ⟩ → ⟨ y ∈ˢ Lset γ ⟩
       → ∥ Σ[ σ ∈ V ℓ ] (⟨ σ ∈ˢ γ ⟩
             × (⟨ x ∈ˢ Lset σ ⟩ × ⟨ y ∈ˢ Lset σ ⟩)) ∥₁
common γ oγ clγ x y hx hy = PT.rec PT.squash₁
  (λ { (δ , (δ∈ , hxδ)) → PT.rec PT.squash₁
        (λ { (ε , (ε∈ , hyε)) → pick δ δ∈ hxδ ε ε∈ hyε })
        (Lset-out′ γ y hy) })
  (Lset-out′ γ x hx)
  where
  Goal = Σ[ σ ∈ V ℓ ] (⟨ σ ∈ˢ γ ⟩ × (⟨ x ∈ˢ Lset σ ⟩ × ⟨ y ∈ˢ Lset σ ⟩))
  pick : (δ : V ℓ) → ⟨ δ ∈ˢ γ ⟩ → ⟨ x ∈ˢ Lset (sucV δ) ⟩
       → (ε : V ℓ) → ⟨ ε ∈ˢ γ ⟩ → ⟨ y ∈ˢ Lset (sucV ε) ⟩
       → ∥ Goal ∥₁
  pick δ δ∈ hxδ ε ε∈ hyε = PT.map choose
    (∣ ord-tri (sucV δ) (suc-ord (mem-ord {A = γ} oγ δ δ∈))
               (sucV ε) (suc-ord (mem-ord {A = γ} oγ ε ε∈)) ∣₁)
    where
    sδ∈γ : ⟨ sucV δ ∈ˢ γ ⟩
    sδ∈γ = sucIter-in-γ γ oγ clγ δ δ∈ 1
    sε∈γ : ⟨ sucV ε ∈ˢ γ ⟩
    sε∈γ = sucIter-in-γ γ oγ clγ ε ε∈ 1
    choose : Tri (sucV δ) (sucV ε) → Goal
    choose (inl sδ∈sε) = sucV ε , (sε∈γ
      , (Lset-mono {α = sucV ε} {β = sucV δ} sδ∈sε hxδ , hyε))
    choose (inr (inl q)) = sucV ε , (sε∈γ
      , (subst (λ w → ⟨ x ∈ˢ Lset w ⟩) q hxδ , hyε))
    choose (inr (inr sε∈sδ)) = sucV δ , (sδ∈γ
      , (hxδ , Lset-mono {α = sucV δ} {β = sucV ε} sε∈sδ hyε))

-- The adjunction stays in the stage: a union of two of its members.
adjoin-in : (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) (a b : V ℓ)
          → ⟨ a ∈ˢ Lset γ ⟩ → ⟨ b ∈ˢ Lset γ ⟩
          → ⟨ (⋃ ⁅ a , ⁅ b ⁆s ⁆) ∈ˢ Lset γ ⟩
adjoin-in γ oγ clγ a b ha hb =
  PT.rec (snd ((⋃ ⁅ a , ⁅ b ⁆s ⁆) ∈ˢ Lset γ)) step (common γ oγ clγ a b ha hb)
  where
  step : Σ[ σ ∈ V ℓ ] (⟨ σ ∈ˢ γ ⟩ × (⟨ a ∈ˢ Lset σ ⟩ × ⟨ b ∈ˢ Lset σ ⟩))
       → ⟨ (⋃ ⁅ a , ⁅ b ⁆s ⁆) ∈ˢ Lset γ ⟩
  step (σ , (σ∈ , (haσ , hbσ))) =
    Lset-mono {α = γ} {β = sucIter 3 σ} (sucIter-in-γ γ oγ clγ σ σ∈ 3)
      (union∈Lset-suc (sucV (sucV σ)) ⁅ a , ⁅ b ⁆s ⁆
        (pair∈Lset-suc (sucV σ) a ⁅ b ⁆s
          (Lset-mono {α = sucV σ} {β = σ} (self∈sucV σ) haσ)
          (sgl∈Lset-suc σ b hbσ)))

-- THE SUCCESSOR STEP, placed.
hier-suc : (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
         → (c : V ℓ) (hc : ⟨ isL c ⟩) (oc : IsOrd c) (hsc : ⟨ isL (sucV c) ⟩)
         → ⟨ c ∈ˢ γ ⟩
         → ⟨ fst (hierL c hc oc) ∈ˢ Lset γ ⟩
         → ⟨ fst (hierL (sucV c) hsc (suc-ord oc)) ∈ˢ Lset γ ⟩
hier-suc γ oγ clγ c hc oc hsc c∈γ hH =
  subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym (Successor.table-union c hc oc hsc))
    (adjoin-in γ oγ clγ (fst (hierL c hc oc)) (pr c (Lset c)) hH P∈γ)
  where
  P∈γ : ⟨ pr c (Lset c) ∈ˢ Lset γ ⟩
  P∈γ = Lset-mono {α = γ} {β = sucIter 3 c} (sucIter-in-γ γ oγ clγ c c∈γ 3)
    (pr∈Lset-suc (sucV c) c (Lset c) (ord∈Lset-suc c oc) (Lset∈suc c))
```

```agda
-- =====================================================================
-- SECTION 5.  The base case, and the hypothesis this chapter leaves.
--
--   `Recorded ∅` records nothing, so the table at ∅ is ∅, and the
--   placement at ∅ is the stage fact of Section 1.  With `hier-suc`
--   this closes every finite p.  The LIMIT case does not close here:
--   see the note under `HierIn`.
-- =====================================================================

∅-isL : ⟨ isL ∅ ⟩
∅-isL = Lset→isL (sucV ∅) (suc-ord ∅-ord) ∅ (ord∈Lset-suc ∅ ∅-ord)

hier-empty : fst (hierL ∅ ∅-isL ∅-ord) ≡ ∅
hier-empty = extensionality (fst H₀) ∅ (s₁ , s₂)
  where
  H₀ : SL
  H₀ = hierL ∅ ∅-isL ∅-ord
  sp = hierL-spec ∅ ∅-isL ∅-ord
  s₁ : ⟨ fst H₀ ⊆ ∅ ⟩
  s₁ v v∈ₛ = PT.rec (snd (v ∈ₛ ∅)) step (subst ⟨_⟩ (sp z) v∈)
    where
    v∈ : ⟨ v ∈ˢ fst H₀ ⟩
    v∈ = ∈∈ₛ {a = v} {b = fst H₀} .snd v∈ₛ
    z : SL
    z = v , isL-trans {x = fst H₀} {y = v} v∈ (snd H₀)
    step : Σ[ d ∈ SL ] (⟨ fst d ∈ˢ ∅ ⟩ × (v ≡ pr (fst d) (Lset (fst d))))
         → ⟨ v ∈ₛ ∅ ⟩
    step (d , (d∈ , _)) =
      Empty.rec (∅-empty (fst d) (∈∈ₛ {a = fst d} {b = ∅} .fst d∈))
  s₂ : ⟨ ∅ ⊆ fst H₀ ⟩
  s₂ v v∈ₛ = Empty.rec (∅-empty v v∈ₛ)

hier-in-∅ : ⟨ fst (hierL ∅ ∅-isL ∅-ord) ∈ˢ Lset (+ω ∅) ⟩
hier-in-∅ = subst (λ w → ⟨ w ∈ˢ Lset (+ω ∅) ⟩) (sym hier-empty)
  (Blocks.below-Lset ∅ ∅-ord (sucV ∅) (inr (1 , refl)) ∅
    (ord∈Lset-suc ∅ ∅-ord))

-- THE HYPOTHESIS.  The table at p lies in the stage at p+ω.
--
--   The successor step is `hier-suc`, and the base is `hier-in-∅`.
--   At a LIMIT p the union over c ∈ p of the tables at c is NOT a
--   definable subset of Lset p by any stage-internal formula: the only
--   candidate characterisation is
--     hierL p = { x ∈ Lset p′ : x is a pair ⟨c, u⟩ , c ∈ p , u ≡ Lset c }
--   and the clause `u ≡ Lset c` is not expressible at the stage without
--   the level formula's completeness at every c ∈ p.  That induction is
--   not carried here, and the fact is taken as this hypothesis.
HierIn : Type (ℓ-suc ℓ)
HierIn = (p : V ℓ) (hp : ⟨ isL p ⟩) (op : IsOrd p)
       → ⟨ fst (hierL p hp op) ∈ˢ Lset (+ω p) ⟩
```
