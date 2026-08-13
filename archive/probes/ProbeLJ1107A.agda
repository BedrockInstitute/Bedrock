{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.107] probe A: build sq at every infinite ordinal.
--
-- The route of [LJ-1.101] section 2.2, measured step by step:
--   sq ω by the delivered pairing; |α| as the least ordinal in
--   bijection with α (leastOf over the well-order on ⟪ sucV α ⟫);
--   Init |α| for the initial case; sq |α| by the delivered
--   via-col-square; sq α from sq |α| by composition.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module ProbeLJ1107A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import ProbeLJ1106A {ℓ} lem as P106
open P106 using ( module NumeralPresentation )
import ProbeLJ194A {ℓ} lem as P194
open P194 using ( module OrdSWO; isSet⟪⟫ )
import ProbeLJ192A {ℓ} as P192
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase )
import L.Ordinal {ℓ} as Ord
open Ord using ( mem-ord; suc-ord; ω-ord; #∈ω; numeral-ord )
open import L.Constructible {ℓ} using ( IsOrd )
import L.Ordinal.Linear {ℓ} lem as Lin
open Lin using ( ord-tri )
import FOL.Count {ℓ} as Count
import L.Choice.Finite {ℓ} lem as LF
open LF using ( natOrder )
import V.Hierarchy {ℓ} as Hier
open Hier using ( 𝒮ᵥ; ∈-irrefl; ∈-induction; regularityV )
import V.Model {ℓ} as VModel
open VModel using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
import V.Presentation {ℓ} as VPres
open VPres using ( member; fiber; ↪-inj )
import V.Coding {ℓ} as VCoding
open VCoding using ( #-inj′; #mono )
import FOL.ZFStructure as ZF
open ZF using ( module hPropStructure )
import Cubical.HITs.CumulativeHierarchy.Properties as CH
open CH using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
open CHC using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Foundations.Isomorphism as Iso
open Iso using ( iso; isoToEquiv )
import Cubical.Foundations.Equiv as Eq
open Eq using ( _≃_; equivFun; invEq; retEq; secEq; idEquiv )
open Eq using ( invEquiv )
import Cubical.Functions.Embedding as Emb
open Emb using ( isEmbedding→hasPropFibers )
import Cubical.Data.Sigma as Sig
open Sig using ( ΣPathP; Σ≡Prop )
import Cubical.Foundations.HLevels as HL
open HL using ( isProp× )
import Cubical.Foundations.Transport as Tr
open Tr using ( transportTransport⁻ )
import Cubical.Induction.WellFounded as WF
open WF using ( Acc; acc )
import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} as WOBase
open WOBase using ( SWO; Tri; lt; eq; gt; IsLeast; leastOf; module SWO )
import Cubical.Data.Nat as Nat
open Nat using ( ℕ; zero; suc )
import Cubical.Data.Nat.Properties as NatProp
open NatProp using ( injSuc; znots; snotz )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum.Properties as SumProp
open SumProp using ( isProp⊎ )
import Cubical.Data.Unit as Unit
open Unit using ( Unit; tt )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Nat.Order as NatOrd
open NatOrd using ( _<_; isProp≤ )
import Cubical.Data.Sigma.Properties as SigProp

open hPropStructure 𝒮ᵥ

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- Cantor-Bernstein for h-sets, with LEM as the standing parameter.
--   The chain construction: C₀ is the part of A outside the image of g;
--   Cₙ₊₁ is g(f(Cₙ)); C is the union.  On C the map is f, off C it is
--   g⁻¹.  The fibers of g are propositions because g is injective and A
--   is a set, so g⁻¹ is extracted from the truncation.  The classical
--   step is the LEM case split x ∈ C vs x ∉ C, twice.
--   This is the square clause's missing half:  h : |α| ↪ β and
--   j : β ↪ |α| give |α| ≃ β, and the leastness refutes β < |α|.
-- =====================================================================
module CSB (A B : Type ℓ) (isSetA : isSet A) (isSetB : isSet B)
           (f : A → B) (f-inj : (x y : A) → f x ≡ f y → x ≡ y)
           (g : B → A) (g-inj : (x y : B) → g x ≡ g y → x ≡ y) where

  g-inj' : {x y : B} → g x ≡ g y → x ≡ y
  g-inj' {x} {y} = g-inj x y

  Wit : A → Type ℓ
  Wit a = Σ[ b ∈ B ] (g b ≡ a)

  isPropFibG : (a : A) → isProp (Σ[ b ∈ B ] (g b ≡ a))
  isPropFibG a (b , p) (b' , p') =
    Σ≡Prop {B = λ x → g x ≡ a} (λ x → isSetA (g x) a) (g-inj' (p ∙ sym p'))

  Cn : ℕ → A → hProp ℓ
  Cn zero    a = (Wit a → Empty.⊥) , isPropΠ (λ _ → Empty.isProp⊥)
  Cn (suc n) a = ( ∥ Σ[ x ∈ A ] (⟨ Cn n x ⟩ × (g (f x) ≡ a)) ∥₁ , squash₁ )

  C : A → hProp ℓ
  C a = ( ∥ Σ[ n ∈ ℕ ] ⟨ Cn n a ⟩ ∥₁ , squash₁ )

  ∈C : (a : A) → Type ℓ
  ∈C a = ⟨ C a ⟩

  C-closed : (a : A) → ⟨ C a ⟩ → ⟨ C (g (f a)) ⟩
  C-closed a = PT.rec squash₁ (λ { (n , c) → ∣ suc n , ∣ a , (c , refl) ∣₁ ∣₁ })

  decC : (a : A) → ⟨ C a ⟩ ⊎ (⟨ C a ⟩ → Empty.⊥)
  decC a = lowerLEM lem (C a)

  hasWit : (a : A) → (⟨ C a ⟩ → Empty.⊥) → ∥ Wit a ∥₁
  hasWit a ¬Ca = go (lowerLEM lem (Wit a , isPropFibG a))
    where
    go : (Wit a) ⊎ ((Wit a) → Empty.⊥) → ∥ Wit a ∥₁
    go (inl w) = ∣ w ∣₁
    go (inr nw) = Empty.rec (¬Ca ∣ zero , nw ∣₁)

  ginv : (a : A) → (⟨ C a ⟩ → Empty.⊥) → B
  ginv a ¬Ca = fst (extract)
    where
    extract : Wit a
    extract = PT.rec (isPropFibG a) (λ w → w) (hasWit a ¬Ca)

  ginv-spec : (a : A) (¬Ca : ⟨ C a ⟩ → Empty.⊥) → g (ginv a ¬Ca) ≡ a
  ginv-spec a ¬Ca = snd (extract)
    where
    extract : Wit a
    extract = PT.rec (isPropFibG a) (λ w → w) (hasWit a ¬Ca)

  hgo : (a : A) (d : ⟨ C a ⟩ ⊎ (⟨ C a ⟩ → Empty.⊥)) → B
  hgo a (inl _) = f a
  hgo a (inr n) = ginv a n

  decProp : (a : A) → isProp (⟨ C a ⟩ ⊎ (⟨ C a ⟩ → Empty.⊥))
  decProp a = isProp⊎ (snd (C a)) (isPropΠ (λ _ → Empty.isProp⊥)) (λ c n → n c)

  h : A → B
  h a = hgo a (decC a)

  h-inl : (a : A) (c : ⟨ C a ⟩) → h a ≡ f a
  h-inl a c = cong (hgo a) (decProp a (decC a) (inl c))

  h-inr : (a : A) (n : ⟨ C a ⟩ → Empty.⊥) → h a ≡ ginv a n
  h-inr a n = cong (hgo a) (decProp a (decC a) (inr n))

  h-inj : (x y : A) → h x ≡ h y → x ≡ y
  h-inj x y e = gox (decC x) (decC y)
    where
    gox : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) → ⟨ C y ⟩ ⊎ (⟨ C y ⟩ → Empty.⊥) → x ≡ y
    gox (inl cx) (inl cy) = f-inj x y (sym (h-inl x cx) ∙ e ∙ h-inl y cy)
    gox (inl cx) (inr ny) = Empty.rec (ny (subst (λ z → ⟨ C z ⟩) gfx≡y (C-closed x cx)))
      where
      gfx≡y : g (f x) ≡ y
      gfx≡y = cong g (sym (h-inl x cx) ∙ e ∙ h-inr y ny) ∙ ginv-spec y ny
    gox (inr nx) (inl cy) = Empty.rec (nx (subst (λ z → ⟨ C z ⟩) (sym x≡gfy) (C-closed y cy)))
      where
      x≡gfy : x ≡ g (f y)
      x≡gfy = sym (ginv-spec x nx) ∙ cong g (sym (h-inr x nx) ∙ e ∙ h-inl y cy)
    gox (inr nx) (inr ny) =
      sym (ginv-spec x nx) ∙ cong g (sym (h-inr x nx) ∙ e ∙ h-inr y ny) ∙ ginv-spec y ny

  h-surj : (b : B) → ∥ Σ[ a ∈ A ] (h a ≡ b) ∥₁
  h-surj b = go (decC (g b))
    where
    go : ⟨ C (g b) ⟩ ⊎ (⟨ C (g b) ⟩ → Empty.⊥) → ∥ Σ[ a ∈ A ] (h a ≡ b) ∥₁
    go (inl cgb) = PT.rec squash₁ pre (cgb)
      where
      pre : Σ[ n ∈ ℕ ] ⟨ Cn n (g b) ⟩ → ∥ Σ[ a ∈ A ] (h a ≡ b) ∥₁
      pre (zero , c₀) = Empty.rec (c₀ (b , refl))
      pre (suc n , c₊) = PT.rec squash₁ inner (c₊)
        where
        inner : Σ[ x ∈ A ] (⟨ Cn n x ⟩ × (g (f x) ≡ g b)) → ∥ Σ[ a ∈ A ] (h a ≡ b) ∥₁
        inner (x , (cnx , gfx≡gb)) =
          ∣ x , (h-inl x ∣ n , cnx ∣₁ ∙ g-inj' gfx≡gb) ∣₁
    go (inr ngb) = ∣ g b , (h-inr (g b) ngb ∙ g-inj' (ginv-spec (g b) ngb)) ∣₁

  isPropFibH : (b : B) → isProp (Σ[ a ∈ A ] (h a ≡ b))
  isPropFibH b (a , p) (a' , p') =
    Σ≡Prop {B = λ x → h x ≡ b} (λ x → isSetB (h x) b) (h-inj a a' (p ∙ sym p'))

  isContrFibH : (b : B) → isContr (Σ[ a ∈ A ] (h a ≡ b))
  isContrFibH b = c , (λ w → sym (isPropFibH b w c))
    where
    c : Σ[ a ∈ A ] (h a ≡ b)
    c = PT.rec (isPropFibH b) (λ v → v) (h-surj b)

  csb : A ≃ B
  csb = (h , record { equiv-proof = isContrFibH })

-- =====================================================================
-- The least cardinal of an ordinal, |α|.
--   The predicate: γ ∈ sucV α whose presentation bijects with α's.
--   Inhabited by α itself (self∈sucV, idEquiv).  leastOf over the
--   ∈-well-order on ⟪ sucV α ⟫ picks the least; α is an ordinal, so
--   the order is the delivered OrdSWO, no choice.  The witness of the
--   predicate is the TRUNCATED ∥ ⟪ |α| ⟫ ≃ ⟪ α ⟫ ∥₁ (leastOf needs a
--   proposition); the leastness κ-min is data.
-- =====================================================================
module LeastCard (α : S) (oα : IsOrd α) where

  Eq : S → Type ℓ
  Eq γ = ⟪ γ ⟫ ≃ ⟪ α ⟫

  EqP : S → hProp ℓ
  EqP γ = ∥ Eq γ ∥₁ , squash₁

  EqP' : ⟪ sucV α ⟫ → hProp ℓ
  EqP' γ = EqP (⟪ sucV α ⟫↪ γ)

  w : SWO (⟪ sucV α ⟫)
  w = OrdSWO.ordSWO (sucV α) (suc-ord oα)

  least : Σ[ γ ∈ ⟪ sucV α ⟫ ] IsLeast w EqP' γ
  least = leastOf w lem EqP'
    (∣ fiber (sucV α) (self∈sucV α) .fst , ∣ idEquiv (⟪ α ⟫) ∣₁ ∣₁)

  γ-card : ⟪ sucV α ⟫
  γ-card = fst least

  κ : S
  κ = ⟪ sucV α ⟫↪ γ-card

  oκ : IsOrd κ
  oκ = mem-ord {A = sucV α} (suc-ord oα) κ (member (sucV α) γ-card)

  κ∈sα : ⟨ κ ∈ˢ sucV α ⟩
  κ∈sα = member (sucV α) γ-card

  κ-eqα : ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁
  κ-eqα = fst (snd least)

  κ-min : (b : ⟪ sucV α ⟫) → ⟨ EqP' b ⟩ → (SWO._<∙_ w b γ-card → Empty.⊥)
  κ-min = snd (snd least)

  -- the leastness at a member δ of κ: δ < κ with δ ≃ α is absurd
  κ-min-at : (δ : S) → ⟨ δ ∈ˢ κ ⟩ → ∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁ → Empty.⊥
  κ-min-at δ δ∈κ δ≃α = κ-min b (bEqP) b<γ
    where
    δ∈sα : ⟨ δ ∈ˢ sucV α ⟩
    δ∈sα = suc-ord oα .fst {x = κ} {y = δ} δ∈κ (member (sucV α) γ-card)
    b : ⟪ sucV α ⟫
    b = fiber (sucV α) δ∈sα .fst
    bδ : ⟪ sucV α ⟫↪ b ≡ δ
    bδ = fiber (sucV α) δ∈sα .snd
    bEqP : ⟨ EqP' b ⟩
    bEqP = subst (λ w → ∥ ⟪ w ⟫ ≃ ⟪ α ⟫ ∥₁) (sym bδ) δ≃α
    b<γ : SWO._<∙_ w b γ-card
    b<γ = subst (λ z → ⟨ z ∈ˢ κ ⟩) (sym bδ) δ∈κ

-- =====================================================================
-- The successor absorption: for infinite γ, sucV γ injects into γ.
--   Members of sucV γ are members of γ plus the top γ.  The numerals
--   inside γ shift up by one, the top maps to the numeral zero, and
--   every other member maps to itself.  The shift is injective; with
--   the inclusion γ ↪ sucV γ, CSB turns it into the equivalence
--   sucV γ ≃ γ that the successor closure of an initial ordinal needs.
--   The γ = ω instance is a separate small module:  ω ∈ ω is false, so
--   the numerals come from #∈ω directly.
-- =====================================================================
module ShiftAbs (γ : S) (oγ : IsOrd γ)
                (γ∉ω : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥)
                (numerals : (k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩) where

  NP : (v : S) → ℕ → hProp (ℓ-suc ℓ)
  NP v k = (v ≡ # k) , isSetS v (# k)

  numeralOf : (v : S) → ⟨ v ∈ˢ ω ⟩ → ℕ
  numeralOf v v∈ω = fst (leastOf natOrder lem (NP v) (FiniteBase.ω-mem→numeral v v∈ω))

  numeralOf-spec : (v : S) (v∈ω : ⟨ v ∈ˢ ω ⟩) → v ≡ # (numeralOf v v∈ω)
  numeralOf-spec v v∈ω = fst (snd (leastOf natOrder lem (NP v) (FiniteBase.ω-mem→numeral v v∈ω)))

  numeralOf-uniq : (v : S) (p q : ⟨ v ∈ˢ ω ⟩) → numeralOf v p ≡ numeralOf v q
  numeralOf-uniq v p q = #-inj′ (sym (numeralOf-spec v p) ∙ numeralOf-spec v q)

  v-of : ⟪ sucV γ ⟫ → S
  v-of m = ⟪ sucV γ ⟫↪ m

  v-in-γ : (m : ⟪ sucV γ ⟫) → (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥) → ((v-of m ≡ γ) → Empty.⊥)
         → ⟨ v-of m ∈ˢ γ ⟩
  v-in-γ m ¬ω ¬γ = ∈sucV-elim (snd (v-of m ∈ˢ γ)) (member (sucV γ) m)
    (λ q → q) (λ q → Empty.rec (¬γ q))

  shift-dec : (m : ⟪ sucV γ ⟫)
            → ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
            → (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥) → ⟪ γ ⟫
  shift-dec m (inl v∈ω) _ = fiber γ (numerals (suc (numeralOf (v-of m) v∈ω))) .fst
  shift-dec m (inr _) (inl v≡γ) = fiber γ (numerals 0) .fst
  shift-dec m (inr ¬v∈ω) (inr ¬v≡γ) = fiber γ (v-in-γ m ¬v∈ω ¬v≡γ) .fst

  shift : ⟪ sucV γ ⟫ → ⟪ γ ⟫
  shift m = shift-dec m (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))

  shift-top : (m : ⟪ sucV γ ⟫) → (v-of m ≡ γ) → ⟪ γ ⟫↪ (shift m) ≡ # 0
  shift-top m v≡γ = go (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ # 0
    go (inl v∈ω) _ = Empty.rec (γ∉ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) v≡γ v∈ω))
    go (inr _) (inl _) = fiber γ (numerals 0) .snd
    go (inr ¬v∈ω) (inr ¬v≡γ) = Empty.rec (¬v≡γ v≡γ)

  shift-num : (m : ⟪ sucV γ ⟫) (v∈ω : ⟨ v-of m ∈ˢ ω ⟩)
            → ⟪ γ ⟫↪ (shift m) ≡ # (suc (numeralOf (v-of m) v∈ω))
  shift-num m v∈ω = go (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ # (suc (numeralOf (v-of m) v∈ω))
    go (inl v∈ω') _ =
      fiber γ (numerals (suc (numeralOf (v-of m) v∈ω'))) .snd
        ∙ cong (λ k → # (suc k)) (numeralOf-uniq (v-of m) v∈ω' v∈ω)
    go (inr ¬v∈ω) _ = Empty.rec (¬v∈ω v∈ω)

  shift-other : (m : ⟪ sucV γ ⟫) (¬v∈ω : ⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
              (¬v≡γ : (v-of m ≡ γ) → Empty.⊥)
            → ⟪ γ ⟫↪ (shift m) ≡ v-of m
  shift-other m ¬v∈ω ¬v≡γ = go (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ γ) , isSetS (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ v-of m
    go (inl v∈ω) _ = Empty.rec (¬v∈ω v∈ω)
    go (inr _) (inl v≡γ) = Empty.rec (¬v≡γ v≡γ)
    go (inr x₁) (inr x) = fiber γ (v-in-γ m x₁ x) .snd

  shift-inj : (m₁ m₂ : ⟪ sucV γ ⟫) → shift m₁ ≡ shift m₂ → m₁ ≡ m₂
  shift-inj m₁ m₂ e = go (lem (v₁ ∈ˢ ω)) (lem ((v₁ ≡ γ) , isSetS v₁ γ))
                          (lem (v₂ ∈ˢ ω)) (lem ((v₂ ≡ γ) , isSetS v₂ γ))
    where
    v₁ : S
    v₁ = v-of m₁
    v₂ : S
    v₂ = v-of m₂
    eqv : ⟪ γ ⟫↪ (shift m₁) ≡ ⟪ γ ⟫↪ (shift m₂)
    eqv = cong (⟪ γ ⟫↪) e
    v₁≡v₂ : v₁ ≡ v₂ → m₁ ≡ m₂
    v₁≡v₂ q = ↪-inj {a = sucV γ} q
    go : ⟨ v₁ ∈ˢ ω ⟩ ⊎ (⟨ v₁ ∈ˢ ω ⟩ → Empty.⊥)
       → (v₁ ≡ γ) ⊎ ((v₁ ≡ γ) → Empty.⊥)
       → ⟨ v₂ ∈ˢ ω ⟩ ⊎ (⟨ v₂ ∈ˢ ω ⟩ → Empty.⊥)
       → (v₂ ≡ γ) ⊎ ((v₂ ≡ γ) → Empty.⊥) → m₁ ≡ m₂
    go (inl a₁) _ (inl a₂) _ = v₁≡v₂
      (numeralOf-spec v₁ a₁ ∙ cong (λ k → # k) (injSuc (#-inj′
        (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-num m₂ a₂))) ∙ sym (numeralOf-spec v₂ a₂))
    go (inl a₁) _ (inr ¬a₂) (inl p₂) = Empty.rec
      (snotz (#-inj′ (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-top m₂ p₂)))
    go (inl a₁) _ (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
        (#∈ω (suc (numeralOf v₁ a₁)))))
    go (inr ¬a₁) (inl p₁) (inl a₂) _ = Empty.rec
      (znots (#-inj′ (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-num m₂ a₂)))
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inl p₂) = v₁≡v₂ (p₁ ∙ sym p₂)
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂) (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inl a₂) _ = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-num m₂ a₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁)
        (#∈ω (suc (numeralOf v₂ a₂)))))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inl p₂) = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-top m₂ p₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁) (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inr ¬p₂) = v₁≡v₂
      (sym (shift-other m₁ ¬a₁ ¬p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)

  shift-inj' : P194._↪_ ⟪ sucV γ ⟫ ⟪ γ ⟫
  shift-inj' = shift , shift-inj

-- the γ = ω instance:  the numerals live in ω by #∈ω, and the top ω
-- maps to the numeral zero.  sucV ω ↪ ω, injective.
module Shiftω = ShiftAbs ω ω-ord (∈-irrefl ω) (λ k → #∈ω k)

-- =====================================================================
-- The finite exclusion at ω: no injection ⟪ ω ⟫ ↪ ⟪ # n ⟫ × ⟪ # n ⟫.
--   Restated from the CoreAtω shape:  every member of a numeral is a
--   numeral, so ⟪ # m ⟫ injects into ⟪ ω ⟫ by the transitivity of ω,
--   and the delivered FiniteBase counting (toFin/fromFin, the product
--   factor, the pigeonhole) refutes the square injection.
-- =====================================================================
module FiniteAtω where

  open FiniteBase

  numeral-into-ω : (m : ℕ) → ⟪ # m ⟫ → ⟪ ω ⟫
  numeral-into-ω m i = fiber ω (ω-ord .fst (member (# m) i) (#∈ω m)) .fst

  numeral-into-ω-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                     → numeral-into-ω m i₁ ≡ numeral-into-ω m i₂ → i₁ ≡ i₂
  numeral-into-ω-inj m i₁ i₂ e = ↪-inj {a = # m}
    (sym (fiber ω (ω-ord .fst (member (# m) i₁) (#∈ω m)) .snd)
      ∙ cong (⟪ ω ⟫↪) e
      ∙ fiber ω (ω-ord .fst (member (# m) i₂) (#∈ω m)) .snd)

  no-inj-finite-ω : (n : ℕ) → (f : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                  → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
  no-inj-finite-ω n f finj =
    AbstractChase.NoInj.no-inj
      (λ n → ⟪ # n ⟫)
      toFin toFin-inj
      fromFin fromFin-inj
      (⟪ ω ⟫)
      numeral-into-ω
      numeral-into-ω-inj
      n f finj

  -- an honest injection from a truncated equivalence into a finite
  -- ordinal is already absurd, so the truncation eliminates into ⊥
  no-eq-finite : (n : ℕ) → ∥ ⟪ ω ⟫ ≃ ⟪ # n ⟫ ∥₁ → Empty.⊥
  no-eq-finite n = PT.rec Empty.isProp⊥ go
    where
    go : ⟪ ω ⟫ ≃ ⟪ # n ⟫ → Empty.⊥
    go e = no-inj-finite-ω n (λ x → equivFun e x , equivFun e x) inj
      where
      inj : (x y : ⟪ ω ⟫) → (equivFun e x , equivFun e x) ≡ (equivFun e y , equivFun e y) → x ≡ y
      inj x y p = sym (retEq e x) ∙ cong (invEq e) (cong fst p) ∙ retEq e y

-- the inclusion of an ordinal's index into its successor's index
module Incl (δ : S) (oδ : IsOrd δ) where

  incl : ⟪ δ ⟫ → ⟪ sucV δ ⟫
  incl m = fiber (sucV δ) {x = ⟪ δ ⟫↪ m} (∈sucV-inl (member δ m)) .fst

  incl-inj : (m n : ⟪ δ ⟫) → incl m ≡ incl n → m ≡ n
  incl-inj m n e = ↪-inj {a = δ}
    (sym (fiber (sucV δ) {x = ⟪ δ ⟫↪ m} (∈sucV-inl (member δ m)) .snd)
      ∙ cong (⟪ sucV δ ⟫↪) e
      ∙ fiber (sucV δ) {x = ⟪ δ ⟫↪ n} (∈sucV-inl (member δ n)) .snd)

  incl' : P194._↪_ ⟪ δ ⟫ ⟪ sucV δ ⟫
  incl' = incl , incl-inj

-- =====================================================================
-- The initial case: |α| = α.  Init α holds:
--   IsOrd and ω ∈ α are the hypotheses; the successor closure uses
--   the shift absorption (sucV γ ↪ γ plus the inclusion, CSB gives
--   γ ≃ sucV γ, the leastness refutes sucV γ = α); the square clause
--   composes the injection α ↪ β×β with the induction hypothesis
--   sq β, then CSB and the leastness refute β < α.  sq α follows by
--   the delivered via-col-square.
-- =====================================================================
module InitialCase (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩)
                   (leastα : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁ → Empty.⊥)
                   (ih : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β
                       → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq β) where

  noinj² : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
         → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
         → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
  noinj² β oβ β∈α ω∈β f f-inj = leastα β β∈α (∣ invEquiv csb ∣₁)
    where
    β∉ω : ⟨ β ∈ˢ ω ⟩ → Empty.⊥
    β∉ω β∈ω = ∈-irrefl ω (ω-ord .fst ω∈β β∈ω)
    sqβ : SQ.sq β
    sqβ = ih β β∈α oβ β∉ω
    h : ⟪ α ⟫ → ⟪ β ⟫
    h m = sqβ .fst (f m)
    h-inj : (m n : ⟪ α ⟫) → h m ≡ h n → m ≡ n
    h-inj m n e = f-inj m n (sqβ .snd (f m) (f n) e)
    j : ⟪ β ⟫ → ⟪ α ⟫
    j m = fiber α {x = ⟪ β ⟫↪ m} (oα .fst (member β m) β∈α) .fst
    j-inj : (m n : ⟪ β ⟫) → j m ≡ j n → m ≡ n
    j-inj m n e = ↪-inj {a = β}
      (sym (fiber α {x = ⟪ β ⟫↪ m} (oα .fst (member β m) β∈α) .snd)
        ∙ cong (⟪ α ⟫↪) e
        ∙ fiber α {x = ⟪ β ⟫↪ n} (oα .fst (member β n) β∈α) .snd)
    csb : ⟪ α ⟫ ≃ ⟪ β ⟫
    csb = CSB.csb (⟪ α ⟫) (⟪ β ⟫) (isSet⟪⟫ α) (isSet⟪⟫ β) h h-inj j j-inj

  succ-closure : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩
  succ-closure γ γ∈α =
    go (ord-tri (sucV γ) (suc-ord (mem-ord {A = α} oα γ γ∈α)) α oα)
    where
    oγ : IsOrd γ
    oγ = mem-ord {A = α} oα γ γ∈α
    go : (⟨ sucV γ ∈ˢ α ⟩ ⊎ ((sucV γ ≡ α) ⊎ ⟨ α ∈ˢ sucV γ ⟩)) → ⟨ sucV γ ∈ˢ α ⟩
    go (inl h) = h
    go (inr (inr h)) = ∈sucV-elim {A = γ} {x = α} {P = ⟨ sucV γ ∈ˢ α ⟩}
      (snd (sucV γ ∈ˢ α)) h
      (λ α∈γ → Empty.rec (∈-irrefl α (oα .fst {x = γ} {y = α} α∈γ γ∈α)))
      (λ α≡γ → Empty.rec (∈-irrefl γ (subst (λ w → ⟨ γ ∈ˢ w ⟩) α≡γ γ∈α)))
    go (inr (inl sγ≡α)) = go2 (ord-tri γ oγ ω ω-ord)
      where
      go2 : (⟨ γ ∈ˢ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ˢ γ ⟩)) → ⟨ sucV γ ∈ˢ α ⟩
      go2 (inl γ∈ω) = PT.rec (snd (sucV γ ∈ˢ α)) go3 (FiniteBase.ω-mem→numeral γ γ∈ω)
        where
        go3 : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ˢ α ⟩
        go3 (n , q) = Empty.rec (∈-irrefl ω (ω-ord .fst ω∈α α∈ω))
          where
          α∈ω : ⟨ α ∈ˢ ω ⟩
          α∈ω = subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (cong sucV q) ∙ sγ≡α) (#∈ω (suc n))
      go2 (inr (inl γ≡ω)) = Empty.rec (leastα ω ω∈α (∣ subst (λ w → ⟪ ω ⟫ ≃ ⟪ w ⟫) (sym α≡sucω) csbω ∣₁))
        where
        module SW = Shiftω
        module IW = Incl ω ω-ord
        csbω : ⟪ ω ⟫ ≃ ⟪ sucV ω ⟫
        csbω = CSB.csb (⟪ ω ⟫) (⟪ sucV ω ⟫) (isSet⟪⟫ ω) (isSet⟪⟫ (sucV ω))
                 IW.incl IW.incl-inj SW.shift SW.shift-inj
        α≡sucω : α ≡ sucV ω
        α≡sucω = sym sγ≡α ∙ cong sucV γ≡ω
      go2 (inr (inr ω∈γ)) = Empty.rec (leastα γ γ∈α (∣ subst (λ w → ⟪ γ ⟫ ≃ ⟪ w ⟫) sγ≡α csbγ ∣₁))
        where
        γ∉ω' : ⟨ γ ∈ˢ ω ⟩ → Empty.⊥
        γ∉ω' h = ∈-irrefl ω (ω-ord .fst ω∈γ h)
        module SA = ShiftAbs γ oγ γ∉ω' (λ k → oγ .fst {x = ω} {y = # k} (#∈ω k) ω∈γ)
        module IG = Incl γ oγ
        csbγ : ⟪ γ ⟫ ≃ ⟪ sucV γ ⟫
        csbγ = CSB.csb (⟪ γ ⟫) (⟪ sucV γ ⟫) (isSet⟪⟫ γ) (isSet⟪⟫ (sucV γ))
                 IG.incl IG.incl-inj SA.shift SA.shift-inj

  initα : SQ.Init α
  initα = oα , ω∈α , succ-closure , noinj²

  sqα : SQ.sq α
  sqα = SQ.via-col-square α initα

-- =====================================================================
-- The non-initial case, conditional on the honest injection.
--   |α| ∈ α: the induction hypothesis at κ gives sq κ, and with the
--   injection α ↪ κ and the inclusion κ ↪ α the pairing composes.
--   The injection is the brief's step 5 datum "α ↪ |α| by the
--   bijection"; the least-of witness is truncated (LeastCard.κ-eqα),
--   so this module is stated with the injection as a hypothesis, and
--   the chain's final theorem cannot discharge it (the report
--   documents the term that cannot be written).
-- =====================================================================
module NonInitial (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                  (κ : S) (oκ : IsOrd κ) (κ-eqα : ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁)
                  (κ∈α : ⟨ κ ∈ˢ α ⟩)
                  (α↪κ : ⟪ α ⟫ ↪ ⟪ κ ⟫)
                  (ih : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β
                      → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq β) where

  κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥
  κ∉ω κ∈ω = PT.rec Empty.isProp⊥ go3 (FiniteBase.ω-mem→numeral κ κ∈ω)
    where
    go3 : Σ[ n ∈ ℕ ] (κ ≡ # n) → Empty.⊥
    go3 (n , q) = go4 (ord-tri ω ω-ord α oα)
      where
      eqακ : ∥ ⟪ # n ⟫ ≃ ⟪ α ⟫ ∥₁
      eqακ = subst (λ w → ∥ ⟪ w ⟫ ≃ ⟪ α ⟫ ∥₁) q κ-eqα
      emb : ⟨ ω ∈ˢ α ⟩ → ⟪ ω ⟫ ↪ ⟪ α ⟫
      emb ω∈α = (λ m → fiber α {x = ⟪ ω ⟫↪ m} (oα .fst (member ω m) ω∈α) .fst)
              , λ m n e → ↪-inj {a = ω}
                  (sym (fiber α {x = ⟪ ω ⟫↪ m} (oα .fst (member ω m) ω∈α) .snd)
                    ∙ cong (⟪ α ⟫↪) e
                    ∙ fiber α {x = ⟪ ω ⟫↪ n} (oα .fst (member ω n) ω∈α) .snd)
      id-inj : (ω ≡ α) → ⟪ ω ⟫ ↪ ⟪ α ⟫
      id-inj ω≡α = subst (λ w → P194._↪_ ⟪ ω ⟫ ⟪ w ⟫) ω≡α
        ((λ x → x) , (λ x y e → e))
      refute : ⟪ ω ⟫ ↪ ⟪ α ⟫ → Empty.⊥
      refute g = PT.rec Empty.isProp⊥ go5 eqακ
        where
        go5 : ⟪ # n ⟫ ≃ ⟪ α ⟫ → Empty.⊥
        go5 e = FiniteAtω.no-inj-finite-ω n (λ x → f (g .fst x) , f (g .fst x)) inj
          where
          f : ⟪ α ⟫ → ⟪ # n ⟫
          f = invEq e
          inj : (x y : ⟪ ω ⟫) → (f (g .fst x) , f (g .fst x)) ≡ (f (g .fst y) , f (g .fst y)) → x ≡ y
          inj x y p = g .snd x y
            (sym (secEq e (g .fst x)) ∙ cong (equivFun e) (cong fst p) ∙ secEq e (g .fst y))
      go4 : (⟨ ω ∈ˢ α ⟩ ⊎ ((ω ≡ α) ⊎ ⟨ α ∈ˢ ω ⟩)) → Empty.⊥
      go4 (inl ω∈α) = refute (emb ω∈α)
      go4 (inr (inl ω≡α)) = refute (id-inj ω≡α)
      go4 (inr (inr α∈ω)) = Empty.rec (α∉ω α∈ω)

  j : ⟪ κ ⟫ → ⟪ α ⟫
  j m = fiber α {x = ⟪ κ ⟫↪ m} (oα .fst (member κ m) κ∈α) .fst

  j-inj : (m n : ⟪ κ ⟫) → j m ≡ j n → m ≡ n
  j-inj m n e = ↪-inj {a = κ}
    (sym (fiber α {x = ⟪ κ ⟫↪ m} (oα .fst (member κ m) κ∈α) .snd)
      ∙ cong (⟪ α ⟫↪) e
      ∙ fiber α {x = ⟪ κ ⟫↪ n} (oα .fst (member κ n) κ∈α) .snd)

  sqκ : SQ.sq κ
  sqκ = ih κ κ∈α oκ κ∉ω

  pair : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  pair (x , y) = j (sqκ .fst (α↪κ .fst x , α↪κ .fst y))

  pair-inj : (p q : ⟪ α ⟫ × ⟪ α ⟫) → pair p ≡ pair q → p ≡ q
  pair-inj (x , y) (x' , y') e = ΣPathP (x≡x' , y≡y')
    where
    pq : (α↪κ .fst x , α↪κ .fst y) ≡ (α↪κ .fst x' , α↪κ .fst y')
    pq = sqκ .snd (α↪κ .fst x , α↪κ .fst y) (α↪κ .fst x' , α↪κ .fst y')
      (j-inj (sqκ .fst (α↪κ .fst x , α↪κ .fst y))
             (sqκ .fst (α↪κ .fst x' , α↪κ .fst y')) e)
    x≡x' : x ≡ x'
    x≡x' = α↪κ .snd x x' (cong fst pq)
    y≡y' : y ≡ y'
    y≡y' = α↪κ .snd y y' (cong snd pq)

  sqα : SQ.sq α
  sqα = pair , pair-inj

-- =====================================================================
-- The chain: sq at every infinite ordinal, by ∈-induction.
--   The step: trichotomy against ω (ω = α is the pairing, α ∈ ω is
--   refuted); for ω ∈ α, the least cardinal κ = |α| splits into
--   κ = α (the initial case, closed by InitialCase) and κ ∈ α (the
--   non-initial case, closed by NonInitial given the honest injection
--   α ↪ κ).  The injection is the brief's step 5 datum; the least-of
--   witness is truncated (LeastCard.κ-eqα), so the theorem is stated
--   conditional on it and the report documents that the term cannot
--   be written from the delivered data.
-- =====================================================================
module Chain (inj : (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) (κ : S)
                    (κ∈α : ⟨ κ ∈ˢ α ⟩) → ⟪ α ⟫ ↪ ⟪ κ ⟫) where

  P : S → Type (ℓ-suc ℓ)
  P α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq α

  sqω : SQ.sq ω
  sqω = NumeralPresentation.pairω , NumeralPresentation.pairω-inj

  step : (α : S) → ((β : S) → β ∈ᵗ α → P β) → P α
  step α ih oα α∉ω = go (ord-tri ω ω-ord α oα)
    where
    go : (⟨ ω ∈ˢ α ⟩ ⊎ ((ω ≡ α) ⊎ ⟨ α ∈ˢ ω ⟩)) → SQ.sq α
    go (inr (inl ω≡α)) = subst (λ w → SQ.sq w) ω≡α sqω
    go (inr (inr α∈ω)) = Empty.rec (α∉ω α∈ω)
    go (inl ω∈α) = split (∈sucV-elim {A = α} {x = LC0.κ}
      {P = ⟨ LC0.κ ∈ˢ α ⟩ ⊎ (LC0.κ ≡ α)}
      (isProp⊎ (snd (LC0.κ ∈ˢ α)) (isSetS LC0.κ α)
        (λ m e → ∈-irrefl α (subst (λ w → ⟨ w ∈ˢ α ⟩) e m)))
      LC0.κ∈sα (λ q → inl q) (λ q → inr q))
      where
      module LC0 = LeastCard α oα
      ih' : (β : S) → ⟨ β ∈ˢ α ⟩ → IsOrd β → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq β
      ih' β β∈α = ih β β∈α
      split : (⟨ LC0.κ ∈ˢ α ⟩ ⊎ (LC0.κ ≡ α)) → SQ.sq α
      split (inr κ≡α) = InitialCase.sqα α oα ω∈α leastα ih'
        where
        leastα : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ ⟪ δ ⟫ ≃ ⟪ α ⟫ ∥₁ → Empty.⊥
        leastα δ δ∈α δ≃α = LC0.κ-min-at δ δ∈κ δ≃α
          where
          δ∈κ : ⟨ δ ∈ˢ LC0.κ ⟩
          δ∈κ = subst (λ w → ⟨ δ ∈ˢ w ⟩) (sym κ≡α) δ∈α
      split (inl κ∈α) = NonInitial.sqα α oα ω∈α α∉ω LC0.κ LC0.oκ LC0.κ-eqα κ∈α
                          (inj α oα ω∈α LC0.κ κ∈α) ih'

  theorem : (α : S) → P α
  theorem = ∈-induction step
