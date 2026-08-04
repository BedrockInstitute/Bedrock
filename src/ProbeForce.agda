{-# OPTIONS --cubical --safe --guardedness #-}
-- ProbeForce: the [L3.31-GLp] POC 1, the FORCING ENTRY TICKET.
--
-- QUESTION: does the W5-validated set-valued ∈-recursion pattern
-- (V.Hierarchy.∈-induction at P x = S, plus ∈-induction-compute) carry the
-- two-place P-name recursion of forcing?  Pieces: (0) poset + filter, stated
-- minimally; (1) the transitive closure of ∈ and its well-foundedness [CURE];
-- (2) the check name x̌ by ∈-recursion (depth 1); (3) P-names and (4) the
-- evaluation val(τ,G), both by ∈⁺-recursion (depth 3); (5) the baby lemma
-- val(x̌,G) ≡ x for a filter containing the top.
-- Probe-local, untracked. No postulates, no holes, no TERMINATING pragmas.

open import Base.Prelude
open import Base.Truth

module ProbeForce {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; ∈-induction; ∈-induction-compute; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj )

import Cubical.Induction.WellFounded as WF
open WF using ( Acc; acc; WellFounded; access )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Equiv using ( fiber; equivFun; invEq )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; extensionality; _⊆_
        ; _∼_; _≊_; identityPrinciple )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⁅_⁆s; SingletonPackage; SetPackage )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------
-- 0. Shared micro-kit
------------------------------------------------------------------------

-- membership of a small index's value (used everywhere)
memˢ : (x : S) (m : ⟪ x ⟫) → ⟪ x ⟫↪ m ∈ᵗ x
memˢ x m = ∈∈ₛ {a = ⟪ x ⟫↪ m} {b = x} .snd (∈ₛ⟪ x ⟫↪ m)

-- C-14 datum: V.Coding keeps these four PRIVATE, so a consumer must
-- re-derive them.  This is their third occurrence in the tree.
∈singl : {a x : S} → ⟨ x ∈ₛ ⁅ a ⁆s ⟩ → x ≡ a
∈singl {a} {x} = SetPackage.classification (SingletonPackage a) x .fst

singl∈ : {a x : S} → x ≡ a → ⟨ x ∈ₛ ⁅ a ⁆s ⟩
singl∈ {a} {x} = SetPackage.classification (SingletonPackage a) x .snd

inl∈⁅,⁆ : {a b x : S} → x ≡ a → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩
inl∈⁅,⁆ {a} {b} {x} e = pairing-ax a b x .snd ∣ inl e ∣₁

mem⁅,⁆ : {a b x : S} → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩ → ∥ (x ≡ a) ⊎ (x ≡ b) ∥₁
mem⁅,⁆ {a} {b} {x} = pairing-ax a b x .fst

-- small equality both ways
≊→≡ : {a b : S} → a ≊ b → a ≡ b
≊→≡ = equivFun identityPrinciple

≡→≊ : {a b : S} → a ≡ b → a ≊ b
≡→≊ = invEq identityPrinciple

------------------------------------------------------------------------
-- 1. THE CURE: the transitive closure of ∈, and its well-foundedness
--
-- The Kuratowski pair buries the name two levels down:
--   σ ∈ ⁅σ⁆s ∈ pr σ p ∈ τ,
-- so `val` needs its recursive value at ∈-DEPTH 3, which ∈-induction (which
-- hands the IH at direct members only) cannot supply.  The classical texts say
-- "by recursion on rank" for exactly this reason.  Here is the cheaper cure:
-- transport well-foundedness along the transitive closure and reuse the SAME
-- library recursor.
------------------------------------------------------------------------

-- C-6 CONTROL.  The depth gap is REAL MATHEMATICS, not an artifact of the
-- formulation: the name σ is a member of the pair's singleton, never of the
-- pair itself, so no ∈ᵗ-indexed induction hypothesis can ever reach it.
-- (Both branches collapse to σ ∈ σ, refuted by the hierarchy's regularity.)
name∉pair : (σ p : S) → σ ∈ᵗ pr σ p → Empty.⊥
name∉pair σ p h = PT.rec Empty.isProp⊥ discr
  (mem⁅,⁆ {a = ⁅ σ ⁆s} {b = ⁅ σ , p ⁆} {x = σ}
    (∈∈ₛ {a = σ} {b = pr σ p} .fst h))
  where
  discr : (σ ≡ ⁅ σ ⁆s) ⊎ (σ ≡ ⁅ σ , p ⁆) → Empty.⊥
  discr (inl e) = ∈-irrefl σ (∈∈ₛ {a = σ} {b = σ} .snd
                    (subst (λ w → ⟨ σ ∈ₛ w ⟩) (sym e) (singl∈ refl)))
  discr (inr e) = ∈-irrefl σ (∈∈ₛ {a = σ} {b = σ} .snd
                    (subst (λ w → ⟨ σ ∈ₛ w ⟩) (sym e) (inl∈⁅,⁆ refl)))

data _∈⁺_ : S → S → Type (ℓ-suc ℓ) where
  here  : {y x : S} → y ∈ᵗ x → y ∈⁺ x
  there : {z y x : S} → z ∈⁺ y → y ∈ᵗ x → z ∈⁺ x

acc⁺ : (x : S) → Acc _∈ᵗ_ x → Acc _∈⁺_ x
acc⁺ x (acc rs) = acc go
  where
  go : (z : S) → z ∈⁺ x → Acc _∈⁺_ z
  go z (here zx) = acc⁺ z (rs z zx)
  go z (there {y = y} zy yx) = access (acc⁺ y (rs y yx)) z zy

wf⁺ : WellFounded _∈⁺_
wf⁺ x = acc⁺ x (regularityV x)

module ⁺I = WF.WFI wf⁺

------------------------------------------------------------------------
-- 2. The check name x̌, by ∈-recursion at depth 1 (the W5 pattern verbatim)
------------------------------------------------------------------------

module Check (𝟙 : S) where

  chkStep : (x : S) → (∀ y → y ∈ᵗ x → S) → S
  chkStep x rec = sett ⟪ x ⟫ (λ m → pr (rec (⟪ x ⟫↪ m) (memˢ x m)) 𝟙)

  opaque
    chk : S → S
    chk = ∈-induction chkStep

  opaque
    unfolding chk
    chk-compute : (x : S) → chk x ≡ chkStep x (λ y _ → chk y)
    chk-compute = ∈-induction-compute chkStep

  -- reading out
  chk-mem : (x e : S) → ⟨ e ∈ˢ chk x ⟩
          → ∥ Σ[ y ∈ S ] ((y ∈ᵗ x) × (pr (chk y) 𝟙 ≡ e)) ∥₁
  chk-mem x e h = PT.map mk (subst (λ w → ⟨ e ∈ˢ w ⟩) (chk-compute x) h)
    where
    mk : Σ[ m ∈ ⟪ x ⟫ ] (pr (chk (⟪ x ⟫↪ m)) 𝟙 ≡ e)
       → Σ[ y ∈ S ] ((y ∈ᵗ x) × (pr (chk y) 𝟙 ≡ e))
    mk (m , q) = ⟪ x ⟫↪ m , memˢ x m , q

  -- reading in
  chk-in : (x y : S) → y ∈ᵗ x → ⟨ pr (chk y) 𝟙 ∈ˢ chk x ⟩
  chk-in x y yx = subst (λ w → ⟨ pr (chk y) 𝟙 ∈ˢ w ⟩) (sym (chk-compute x)) wit
    where
    fib : fiber ⟪ x ⟫↪ y
    fib = ∈-asFiber {a = y} {b = x} yx
    wit : ⟨ pr (chk y) 𝟙 ∈ˢ sett ⟪ x ⟫ (λ m → pr (chk (⟪ x ⟫↪ m)) 𝟙) ⟩
    wit = ∣ fib .fst , cong (λ u → pr (chk u) 𝟙) (fib .snd) ∣₁

------------------------------------------------------------------------
-- 3. The nested small index: a member's member's member, R-35-clean
--    (no union representation anywhere)
------------------------------------------------------------------------

e₁ : (τ : S) → ⟪ τ ⟫ → S
e₁ τ m = ⟪ τ ⟫↪ m

e₂ : (τ : S) (m : ⟪ τ ⟫) → ⟪ e₁ τ m ⟫ → S
e₂ τ m j = ⟪ e₁ τ m ⟫↪ j

e₃ : (τ : S) (m : ⟪ τ ⟫) (j : ⟪ e₁ τ m ⟫) → ⟪ e₂ τ m j ⟫ → S
e₃ τ m j i = ⟪ e₂ τ m j ⟫↪ i

deep3 : (τ : S) (m : ⟪ τ ⟫) (j : ⟪ e₁ τ m ⟫) (i : ⟪ e₂ τ m j ⟫)
      → e₃ τ m j i ∈⁺ τ
deep3 τ m j i =
  there (there (here (memˢ (e₂ τ m j) i)) (memˢ (e₁ τ m) j)) (memˢ τ m)

------------------------------------------------------------------------
-- 4. The poset and the filter, stated minimally (the hypothesis ledger)
------------------------------------------------------------------------

record Poset : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    ∣P∣     : S
    _≼_     : S → S → hProp (ℓ-suc ℓ)
    top     : S
    top∈P   : ⟨ top ∈ˢ ∣P∣ ⟩
    ≼-refl  : (p : S) → ⟨ p ∈ˢ ∣P∣ ⟩ → ⟨ p ≼ p ⟩
    ≼-trans : (p q r : S) → ⟨ p ≼ q ⟩ → ⟨ q ≼ r ⟩ → ⟨ p ≼ r ⟩
    ≼-top   : (p : S) → ⟨ p ∈ˢ ∣P∣ ⟩ → ⟨ p ≼ top ⟩

record Filter (𝔓 : Poset) : Type (ℓ-suc ℓ) where
  open Poset 𝔓
  field
    ∣G∣      : S
    G⊆P      : (p : S) → ⟨ p ∈ˢ ∣G∣ ⟩ → ⟨ p ∈ˢ ∣P∣ ⟩
    top∈G    : ⟨ top ∈ˢ ∣G∣ ⟩
    upward   : (p q : S) → ⟨ p ∈ˢ ∣G∣ ⟩ → ⟨ q ∈ˢ ∣P∣ ⟩ → ⟨ p ≼ q ⟩ → ⟨ q ∈ˢ ∣G∣ ⟩
    directed : (p q : S) → ⟨ p ∈ˢ ∣G∣ ⟩ → ⟨ q ∈ˢ ∣G∣ ⟩
             → ∥ Σ[ r ∈ S ] ((⟨ r ∈ˢ ∣G∣ ⟩) × ⟨ r ≼ p ⟩ × ⟨ r ≼ q ⟩) ∥₁

------------------------------------------------------------------------
-- 5. P-names and evaluation, by ∈⁺-recursion
------------------------------------------------------------------------

module Force (𝔓 : Poset) (𝔊 : Filter 𝔓) where

  open Poset 𝔓
  open Filter 𝔊
  open Check top public

  -- 5a. the P-name predicate, by ∈⁺-recursion into hProp
  NameStep : (τ : S) → (∀ y → y ∈⁺ τ → hProp (ℓ-suc ℓ)) → hProp (ℓ-suc ℓ)
  NameStep τ rec =
    ( (m : ⟪ τ ⟫)
      → ∥ Σ[ j ∈ ⟪ e₁ τ m ⟫ ] Σ[ i ∈ ⟪ e₂ τ m j ⟫ ] Σ[ k ∈ ⟪ ∣P∣ ⟫ ]
          ((e₁ τ m ≊ pr (e₃ τ m j i) (⟪ ∣P∣ ⟫↪ k))
            × ⟨ rec (e₃ τ m j i) (deep3 τ m j i) ⟩) ∥₁ )
    , isPropΠ (λ _ → PT.isPropPropTrunc)

  opaque
    isName : S → hProp (ℓ-suc ℓ)
    isName = ⁺I.induction NameStep

  opaque
    unfolding isName
    isName-compute : (τ : S) → isName τ ≡ NameStep τ (λ y _ → isName y)
    isName-compute = ⁺I.induction-compute NameStep

  -- 5b. evaluation.  The index picks a member e of τ, a member of e, a member
  -- of that, and a condition p of the filter, subject to e = ⟨σ, p⟩.  Every
  -- component is SMALL: ⟪_⟫ is Type ℓ and _≊_ is the library's small equality
  -- (V.Smallness.small-≡), so no resizing is spent.
  Idx : S → Type ℓ
  Idx τ = Σ[ m ∈ ⟪ τ ⟫ ] Σ[ j ∈ ⟪ e₁ τ m ⟫ ] Σ[ i ∈ ⟪ e₂ τ m j ⟫ ] Σ[ k ∈ ⟪ ∣G∣ ⟫ ]
            (e₁ τ m ≊ pr (e₃ τ m j i) (⟪ ∣G∣ ⟫↪ k))

  nameOf : (τ : S) → Idx τ → S
  nameOf τ (m , j , i , _ , _) = e₃ τ m j i

  valStep : (τ : S) → (∀ y → y ∈⁺ τ → S) → S
  valStep τ rec = sett (Idx τ) (λ q → rec (nameOf τ q) (dp q))
    where
    dp : (q : Idx τ) → nameOf τ q ∈⁺ τ
    dp (m , j , i , _ , _) = deep3 τ m j i

  opaque
    val : S → S
    val = ⁺I.induction valStep

  opaque
    unfolding val
    val-compute : (τ : S) → val τ ≡ valStep τ (λ y _ → val y)
    val-compute = ⁺I.induction-compute valStep

  -- reading out
  val-mem : (τ z : S) → ⟨ z ∈ˢ val τ ⟩
          → ∥ Σ[ σ ∈ S ] Σ[ p ∈ S ]
              ((⟨ p ∈ˢ ∣G∣ ⟩) × (⟨ pr σ p ∈ˢ τ ⟩) × (val σ ≡ z)) ∥₁
  val-mem τ z h = PT.map mk (subst (λ w → ⟨ z ∈ˢ w ⟩) (val-compute τ) h)
    where
    mk : Σ[ q ∈ Idx τ ] (val (nameOf τ q) ≡ z)
       → Σ[ σ ∈ S ] Σ[ p ∈ S ]
           ((⟨ p ∈ˢ ∣G∣ ⟩) × (⟨ pr σ p ∈ˢ τ ⟩) × (val σ ≡ z))
    mk ((m , j , i , k , eq) , q) =
        e₃ τ m j i
      , ⟪ ∣G∣ ⟫↪ k
      , memˢ ∣G∣ k
      , subst (λ w → ⟨ w ∈ˢ τ ⟩) (≊→≡ eq) (memˢ τ m)
      , q

  -- reading in
  val-in : (τ σ p : S) → ⟨ p ∈ˢ ∣G∣ ⟩ → ⟨ pr σ p ∈ˢ τ ⟩ → ⟨ val σ ∈ˢ val τ ⟩
  val-in τ σ p pG h =
    subst (λ w → ⟨ val σ ∈ˢ w ⟩) (sym (val-compute τ))
      ∣ (m , j , i , k , cond) , cong val pi ∣₁
    where
    fτ : fiber ⟪ τ ⟫↪ (pr σ p)
    fτ = ∈-asFiber {a = pr σ p} {b = τ} h
    m : ⟪ τ ⟫
    m = fτ .fst
    pm : e₁ τ m ≡ pr σ p
    pm = fτ .snd
    -- ⁅σ⁆s is a member of the pair, hence of e₁ τ m
    s∈e : ⁅ σ ⁆s ∈ᵗ e₁ τ m
    s∈e = subst (λ w → ⁅ σ ⁆s ∈ᵗ w) (sym pm)
            (∈∈ₛ {a = ⁅ σ ⁆s} {b = pr σ p} .snd (inl∈⁅,⁆ refl))
    fe : fiber ⟪ e₁ τ m ⟫↪ (⁅ σ ⁆s)
    fe = ∈-asFiber {a = ⁅ σ ⁆s} {b = e₁ τ m} s∈e
    j : ⟪ e₁ τ m ⟫
    j = fe .fst
    pj : e₂ τ m j ≡ ⁅ σ ⁆s
    pj = fe .snd
    -- σ is a member of ⁅σ⁆s, hence of e₂ τ m j
    σ∈s : σ ∈ᵗ e₂ τ m j
    σ∈s = subst (λ w → σ ∈ᵗ w) (sym pj)
            (∈∈ₛ {a = σ} {b = ⁅ σ ⁆s} .snd (singl∈ refl))
    fs : fiber ⟪ e₂ τ m j ⟫↪ σ
    fs = ∈-asFiber {a = σ} {b = e₂ τ m j} σ∈s
    i : ⟪ e₂ τ m j ⟫
    i = fs .fst
    pi : e₃ τ m j i ≡ σ
    pi = fs .snd
    fG : fiber ⟪ ∣G∣ ⟫↪ p
    fG = ∈-asFiber {a = p} {b = ∣G∣} pG
    k : ⟪ ∣G∣ ⟫
    k = fG .fst
    pk : ⟪ ∣G∣ ⟫↪ k ≡ p
    pk = fG .snd
    cond : e₁ τ m ≊ pr (e₃ τ m j i) (⟪ ∣G∣ ⟫↪ k)
    cond = ≡→≊ (pm ∙ cong₂ pr (sym pi) (sym pk))

  ----------------------------------------------------------------------
  -- 6. THE BABY LEMMA: val(x̌, G) ≡ x, for a filter containing the top
  ----------------------------------------------------------------------

  val-chk : (x : S) → val (chk x) ≡ x
  val-chk = ∈-induction bstep
    where
    bstep : (x : S) → (∀ y → y ∈ᵗ x → val (chk y) ≡ y) → val (chk x) ≡ x
    bstep x IH = extensionality (val (chk x)) x (fwd , bwd)
      where
      -- ⊆ : every member of val(x̌) is a member of x
      fwd : ⟨ val (chk x) ⊆ x ⟩
      fwd z z∈ = ∈∈ₛ {a = z} {b = x} .fst
        (PT.rec (snd (z ∈ˢ x)) outer
          (val-mem (chk x) z (∈∈ₛ {a = z} {b = val (chk x)} .snd z∈)))
        where
        outer : Σ[ σ ∈ S ] Σ[ p ∈ S ]
                  ((⟨ p ∈ˢ ∣G∣ ⟩) × (⟨ pr σ p ∈ˢ chk x ⟩) × (val σ ≡ z))
              → ⟨ z ∈ˢ x ⟩
        outer (σ , p , pG , pin , vz) =
          PT.rec (snd (z ∈ˢ x)) inner (chk-mem x (pr σ p) pin)
          where
          inner : Σ[ y ∈ S ] ((y ∈ᵗ x) × (pr (chk y) top ≡ pr σ p))
                → ⟨ z ∈ˢ x ⟩
          inner (y , yx , eqp) = subst (λ w → ⟨ w ∈ˢ x ⟩) z≡y yx
            where
            chky≡σ : chk y ≡ σ
            chky≡σ = pr-inj eqp .fst
            z≡y : y ≡ z
            z≡y = sym (IH y yx) ∙ cong val chky≡σ ∙ vz
      -- ⊇ : every member of x is a member of val(x̌)
      bwd : ⟨ x ⊆ val (chk x) ⟩
      bwd z z∈ = ∈∈ₛ {a = z} {b = val (chk x)} .fst
        (subst (λ w → ⟨ w ∈ˢ val (chk x) ⟩) (IH z zx)
          (val-in (chk x) (chk z) top top∈G (chk-in x z zx)))
        where
        zx : z ∈ᵗ x
        zx = ∈∈ₛ {a = z} {b = x} .snd z∈
