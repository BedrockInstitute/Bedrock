# Successor absorption in L

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Absorption {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; con; var; ∃̇∈; ∃̇_; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( #∈ω )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
open import L.Choice.Finite {ℓ} lem using ( natOrder )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro; sucAtL; sucAtL-adequate )
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-in; module Small )
open import L.InjChain {ℓ} lem using ( module StageBound )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Nat.Properties using ( injSuc; znots; snotz )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open FiniteBase using ( ω-mem→numeral )

-- ---------------------------------------------------------------------
-- PART 1.  THE AMBIENT SHIFT, over the hierarchy.
--
-- Take an ordinal γ that is not a member of ω and that holds every
-- numeral.  Then the successor of γ injects into γ.  The map has three
-- cases: a numeral goes to its successor, the top member γ goes to 0,
-- and every other member goes to itself.  The excluded middle decides
-- the case, and each case gets its own readback lemma.  This part builds
-- no element of L; it is the object the next parts internalize.
-- ---------------------------------------------------------------------

module ShiftAbs (γ : V ℓ) (oγ : IsOrd γ)
                (γ∉ω : ⟨ γ ∈ ω ⟩ → Empty.⊥)
                (numerals : (k : ℕ) → ⟨ (# k) ∈ γ ⟩) where

  NP : (v : V ℓ) → ℕ → hProp (ℓ-suc ℓ)
  NP v k = (v ≡ # k) , setIsSet v (# k)

  numeralOf : (v : V ℓ) → ⟨ v ∈ ω ⟩ → ℕ
  numeralOf v v∈ω = fst (leastOf natOrder lem (NP v) (ω-mem→numeral v v∈ω))

  numeralOf-spec : (v : V ℓ) (v∈ω : ⟨ v ∈ ω ⟩) → v ≡ # (numeralOf v v∈ω)
  numeralOf-spec v v∈ω =
    fst (snd (leastOf natOrder lem (NP v) (ω-mem→numeral v v∈ω)))

  numeralOf-uniq : (v : V ℓ) (p q : ⟨ v ∈ ω ⟩)
                 → numeralOf v p ≡ numeralOf v q
  numeralOf-uniq v p q =
    #-inj′ (sym (numeralOf-spec v p) ∙ numeralOf-spec v q)

  v-of : ⟪ sucV γ ⟫ → V ℓ
  v-of m = ⟪ sucV γ ⟫↪ m

  v-in-γ : (m : ⟪ sucV γ ⟫) → (⟨ v-of m ∈ ω ⟩ → Empty.⊥)
         → ((v-of m ≡ γ) → Empty.⊥) → ⟨ v-of m ∈ γ ⟩
  v-in-γ m ¬ω ¬γ = ∈sucV-elim (snd (v-of m ∈ γ)) (member (sucV γ) m)
    (λ q → q) (λ q → Empty.rec (¬γ q))

  shift-dec : (m : ⟪ sucV γ ⟫)
            → ⟨ v-of m ∈ ω ⟩ ⊎ (⟨ v-of m ∈ ω ⟩ → Empty.⊥)
            → (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥) → ⟪ γ ⟫
  shift-dec m (inl v∈ω) _ = fiber γ (numerals (suc (numeralOf (v-of m) v∈ω))) .fst
  shift-dec m (inr _) (inl v≡γ) = fiber γ (numerals 0) .fst
  shift-dec m (inr ¬v∈ω) (inr ¬v≡γ) = fiber γ (v-in-γ m ¬v∈ω ¬v≡γ) .fst

  shift : ⟪ sucV γ ⟫ → ⟪ γ ⟫
  shift m = shift-dec m (lem (v-of m ∈ ω))
    (lem ((v-of m ≡ γ) , setIsSet (v-of m) γ))

  shift-top : (m : ⟪ sucV γ ⟫) → (v-of m ≡ γ) → ⟪ γ ⟫↪ (shift m) ≡ # 0
  shift-top m v≡γ = go (lem (v-of m ∈ ω))
    (lem ((v-of m ≡ γ) , setIsSet (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ ω ⟩ ⊎ (⟨ v-of m ∈ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ # 0
    go (inl v∈ω) _ = Empty.rec (γ∉ω (subst (λ w → ⟨ w ∈ ω ⟩) v≡γ v∈ω))
    go (inr _) (inl _) = fiber γ (numerals 0) .snd
    go (inr ¬v∈ω) (inr ¬v≡γ) = Empty.rec (¬v≡γ v≡γ)

  shift-num : (m : ⟪ sucV γ ⟫) (v∈ω : ⟨ v-of m ∈ ω ⟩)
            → ⟪ γ ⟫↪ (shift m) ≡ # (suc (numeralOf (v-of m) v∈ω))
  shift-num m v∈ω = go (lem (v-of m ∈ ω))
    (lem ((v-of m ≡ γ) , setIsSet (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ ω ⟩ ⊎ (⟨ v-of m ∈ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ # (suc (numeralOf (v-of m) v∈ω))
    go (inl v∈ω') _ =
      fiber γ (numerals (suc (numeralOf (v-of m) v∈ω'))) .snd
        ∙ cong (λ k → # (suc k)) (numeralOf-uniq (v-of m) v∈ω' v∈ω)
    go (inr ¬v∈ω) _ = Empty.rec (¬v∈ω v∈ω)

  shift-other : (m : ⟪ sucV γ ⟫) (¬v∈ω : ⟨ v-of m ∈ ω ⟩ → Empty.⊥)
              (¬v≡γ : (v-of m ≡ γ) → Empty.⊥)
            → ⟪ γ ⟫↪ (shift m) ≡ v-of m
  shift-other m ¬v∈ω ¬v≡γ = go (lem (v-of m ∈ ω))
    (lem ((v-of m ≡ γ) , setIsSet (v-of m) γ))
    where
    go : (d : ⟨ v-of m ∈ ω ⟩ ⊎ (⟨ v-of m ∈ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ γ) ⊎ ((v-of m ≡ γ) → Empty.⊥))
       → ⟪ γ ⟫↪ (shift-dec m d e) ≡ v-of m
    go (inl v∈ω) _ = Empty.rec (¬v∈ω v∈ω)
    go (inr _) (inl v≡γ) = Empty.rec (¬v≡γ v≡γ)
    go (inr h₁) (inr h₂) = fiber γ (v-in-γ m h₁ h₂) .snd

  shift-inj : (m₁ m₂ : ⟪ sucV γ ⟫) → shift m₁ ≡ shift m₂ → m₁ ≡ m₂
  shift-inj m₁ m₂ e = go (lem (v₁ ∈ ω)) (lem ((v₁ ≡ γ) , setIsSet v₁ γ))
                          (lem (v₂ ∈ ω)) (lem ((v₂ ≡ γ) , setIsSet v₂ γ))
    where
    v₁ : V ℓ
    v₁ = v-of m₁
    v₂ : V ℓ
    v₂ = v-of m₂
    eqv : ⟪ γ ⟫↪ (shift m₁) ≡ ⟪ γ ⟫↪ (shift m₂)
    eqv = cong (⟪ γ ⟫↪) e
    v₁≡v₂ : v₁ ≡ v₂ → m₁ ≡ m₂
    v₁≡v₂ q = ↪-inj {a = sucV γ} q
    go : ⟨ v₁ ∈ ω ⟩ ⊎ (⟨ v₁ ∈ ω ⟩ → Empty.⊥)
       → (v₁ ≡ γ) ⊎ ((v₁ ≡ γ) → Empty.⊥)
       → ⟨ v₂ ∈ ω ⟩ ⊎ (⟨ v₂ ∈ ω ⟩ → Empty.⊥)
       → (v₂ ≡ γ) ⊎ ((v₂ ≡ γ) → Empty.⊥) → m₁ ≡ m₂
    go (inl a₁) _ (inl a₂) _ = v₁≡v₂
      (numeralOf-spec v₁ a₁ ∙ cong (λ k → # k) (injSuc (#-inj′
        (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-num m₂ a₂))) ∙ sym (numeralOf-spec v₂ a₂))
    go (inl a₁) _ (inr ¬a₂) (inl p₂) = Empty.rec
      (snotz (#-inj′ (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-top m₂ p₂)))
    go (inl a₁) _ (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ ω ⟩) (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
        (#∈ω (suc (numeralOf v₁ a₁)))))
    go (inr ¬a₁) (inl p₁) (inl a₂) _ = Empty.rec
      (znots (#-inj′ (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-num m₂ a₂)))
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inl p₂) = v₁≡v₂ (p₁ ∙ sym p₂)
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ ω ⟩) (sym (shift-top m₁ p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
        (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inl a₂) _ = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ ω ⟩)
        (sym (shift-num m₂ a₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁)
        (#∈ω (suc (numeralOf v₂ a₂)))))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inl p₂) = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ ω ⟩)
        (sym (shift-top m₂ p₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁) (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inr ¬p₂) = v₁≡v₂
      (sym (shift-other m₁ ¬a₁ ¬p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)

  -- The ambient conclusion, in the shape the L side must reproduce.
  shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫
  shift↪ = shift , shift-inj

-- ---------------------------------------------------------------------
-- PART 2.  THE DESCRIPTION, AND IT TAKES ONE PLACE.
--
-- The graph of the shift is the set of pairs <x, sh x> for x in sucV γ.
-- The value is the three cases above.  Every atom of the formula is
-- DELIVERED: `prAtL` reads the pair, `sucAtL` reads the successor, and
-- membership, equality and the connectives come from the syntax.  No new
-- vocabulary enters, and that is why the carve below needs separation
-- only, never replacement.
--
-- De Bruijn: inside `∃̇∈ (con D)`, the bound x is 0 and p is 1.  Inside
-- the inner `∃̇`, the bound y is 0, x is 1, p is 2.
-- ---------------------------------------------------------------------

-- The shift value at a member x of D, as a V-set.
val : (D C : S) (sh : ⟪ fst D ⟫ → ⟪ fst C ⟫) (x : S) (m : ⟨ x ∈ˢ D ⟩) → V ℓ
val D C sh x m = ⟪ fst C ⟫↪ (sh (fiber (fst D) m .fst))

shiftCase1 : S → Formula S 3
shiftCase1 ω = (var (suc zero) ∈̇ con ω) ∧̇ sucAtL (suc zero) zero

shiftCase2 : S → S → Formula S 3
shiftCase2 γ z = (var (suc zero) ≐ con γ) ∧̇ (var zero ≐ con z)

shiftCase3 : S → S → Formula S 3
shiftCase3 γ ω = (var (suc zero) ∈̇ con γ) ∧̇ ¬̇ (var (suc zero) ∈̇ con ω)
               ∧̇ (var zero ≐ var (suc zero))

shiftRel : S → S → S → Formula S 3
shiftRel γ ω z = shiftCase1 ω ∨̇ (shiftCase2 γ z ∨̇ shiftCase3 γ ω)

shiftFo : S → S → S → S → Formula S 1
shiftFo D γ ω z =
  ∃̇∈ (con D) (∃̇ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ shiftRel γ ω z))

-- The reading, and it matches the ambient shift case for case.
module ShiftFo (D C γ ω z : S)
               (sh : ⟪ fst D ⟫ → ⟪ fst C ⟫)
               (shInj : (m n : ⟪ fst D ⟫) → sh m ≡ sh n → m ≡ n)
               (shNum : (m : ⟪ fst D ⟫) (v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩)
                      → ⟪ fst C ⟫↪ (sh m) ≡ sucV (⟪ fst D ⟫↪ m))
               (shTop : (m : ⟪ fst D ⟫) (v≡γ : ⟪ fst D ⟫↪ m ≡ fst γ)
                      → ⟪ fst C ⟫↪ (sh m) ≡ fst z)
               (shOther : (m : ⟪ fst D ⟫) (¬v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩ → Empty.⊥)
                        (¬v≡γ : (⟪ fst D ⟫↪ m ≡ fst γ) → Empty.⊥)
                        → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m)
               (D-in-dec : (x : S) → ⟨ x ∈ˢ D ⟩ → ((fst x ≡ fst γ) → Empty.⊥)
                         → ⟨ fst x ∈ fst γ ⟩) where

  private
    fb : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟪ fst D ⟫
    fb x m = fiber (fst D) m .fst

    fb-eq : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟪ fst D ⟫↪ (fb x m) ≡ fst x
    fb-eq x m = fiber (fst D) m .snd

    prAtRead : (p x y : S)
             → ⟨ (y ∷ x ∷ p ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
             ≡ (fst p ≡ pr (fst x) (fst y))
    prAtRead p x y = cong ⟨_⟩
      (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ p ∷ []))

    sucAtRead : (p x y : S) → ⟨ (y ∷ x ∷ p ∷ []) ⊨ sucAtL (suc zero) zero ⟩
              ≡ (fst y ≡ sucV (fst x))
    sucAtRead p x y = cong ⟨_⟩
      (sucAtL-adequate (suc zero) zero (y ∷ x ∷ p ∷ []))

  -- The value equality is stated between two possibly different members
  -- u and u', keyed by the equality of their underlying sets.
  val-cong : (u u' : S) (m : ⟨ u ∈ˢ D ⟩) (m' : ⟨ u' ∈ˢ D ⟩) (e : fst u ≡ fst u')
           → val D C sh u m ≡ val D C sh u' m'
  val-cong u u' m m' e =
    cong (⟪ fst C ⟫↪) (cong sh (↪-inj {a = fst D} (fb-eq u m ∙ e ∙ sym (fb-eq u' m'))))

  val-inj : (u u' : S) (m : ⟨ u ∈ˢ D ⟩) (m' : ⟨ u' ∈ˢ D ⟩)
          → val D C sh u m ≡ val D C sh u' m' → fst u ≡ fst u'
  val-inj u u' m m' e =
    sym (fb-eq u m)
    ∙ cong (⟪ fst D ⟫↪) (shInj (fb u m) (fb u' m') (↪-inj {a = fst C} e))
    ∙ fb-eq u' m'

  private
    case1-val : (x y : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ x ∈ˢ ω ⟩ → fst y ≡ sucV (fst x)
              → fst y ≡ val D C sh x m
    case1-val x y m x∈ω y≡sx =
      y≡sx ∙ sym (shNum (fb x m) v∈ω' ∙ cong sucV (fb-eq x m))
      where
      v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩
      v∈ω' = subst (λ w → ⟨ w ∈ fst ω ⟩) (sym (fb-eq x m)) x∈ω

    case2-val : (x y : S) (m : ⟨ x ∈ˢ D ⟩) → fst x ≡ fst γ → fst y ≡ fst z
              → fst y ≡ val D C sh x m
    case2-val x y m x≡γ y≡z = y≡z ∙ sym (shTop (fb x m) (fb-eq x m ∙ x≡γ))

    case3-val : (x y : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ x ∈ˢ γ ⟩
              → (⟨ x ∈ˢ ω ⟩ → Empty.⊥) → fst y ≡ fst x → fst y ≡ val D C sh x m
    case3-val x y m x∈γ ¬x∈ω y≡x =
      y≡x ∙ sym (shOther (fb x m) ¬v∈ω' ¬v≡γ' ∙ fb-eq x m)
      where
      ¬v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩ → Empty.⊥
      ¬v∈ω' h = ¬x∈ω (subst (λ w → ⟨ w ∈ fst ω ⟩) (fb-eq x m) h)
      ¬v≡γ' : (⟪ fst D ⟫↪ (fb x m) ≡ fst γ) → Empty.⊥
      ¬v≡γ' h = ∈-irrefl (fst γ) (subst (λ w → ⟨ w ∈ fst γ ⟩) (sym (fb-eq x m) ∙ h) x∈γ)

    relVal : (p x y : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftRel γ ω z ⟩
           → fst y ≡ val D C sh x m
    relVal p x y m rel = PT.rec (setIsSet (fst y) (val D C sh x m)) go rel
      where
      go : ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase1 ω ⟩ ⊎
           ∥ ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase2 γ z ⟩ ⊎
             ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase3 γ ω ⟩ ∥₁
         → fst y ≡ val D C sh x m
      go (inl c1) = case1-val x y m (fst c1) (subst (λ T → T) (sucAtRead p x y) (snd c1))
      go (inr c23) = PT.rec (setIsSet (fst y) (val D C sh x m)) go23 c23
        where
        go23 : ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase2 γ z ⟩ ⊎
               ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftCase3 γ ω ⟩
             → fst y ≡ val D C sh x m
        go23 (inl c2) = case2-val x y m (fst c2) (snd c2)
        go23 (inr c3) = case3-val x y m (fst c3) (fst (snd c3)) (snd (snd c3))

  out : (p : S) → ⟨ (p ∷ []) ⊨ shiftFo D γ ω z ⟩
      → ∥ Σ[ x ∈ S ] Σ[ m ∈ ⟨ x ∈ˢ D ⟩ ]
          (fst p ≡ pr (fst x) (val D C sh x m)) ∥₁
  out p h = PT.map step h
    where
    step : Σ[ x ∈ S ] (⟨ x ∈ˢ D ⟩
             × ⟨ (x ∷ p ∷ []) ⊨ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero
                                 ∧̇ shiftRel γ ω z)) ⟩)
         → Σ[ x ∈ S ] Σ[ m ∈ ⟨ x ∈ˢ D ⟩ ]
             (fst p ≡ pr (fst x) (val D C sh x m))
    step (x , (m , hy)) = x , m ,
      PT.rec (setIsSet (fst p) (pr (fst x) (val D C sh x m))) go hy
      where
      go : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ p ∷ [])
             ⊨ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ shiftRel γ ω z) ⟩
         → fst p ≡ pr (fst x) (val D C sh x m)
      go (y , (prAtH , relH)) = subst (λ T → T) (prAtRead p x y) prAtH
        ∙ cong (pr (fst x)) (relVal p x y m relH)

  into : (p x : S) (m : ⟨ x ∈ˢ D ⟩) → fst p ≡ pr (fst x) (val D C sh x m)
       → ⟨ (p ∷ []) ⊨ shiftFo D γ ω z ⟩
  into p x m e = ∣ x , (m , ∣ y , (prAtPf , relPf) ∣₁) ∣₁
    where
    y : S
    y = val D C sh x m
      , isL-trans {x = fst C} {y = val D C sh x m}
          (member (fst C) (sh (fiber (fst D) m .fst))) (snd C)

    prAtPf : ⟨ (y ∷ x ∷ p ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
    prAtPf = subst (λ T → T) (sym (prAtRead p x y)) e

    relPf : ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftRel γ ω z ⟩
    relPf = go (lem (fst x ∈ fst ω)) (lem ((fst x ≡ fst γ) , setIsSet (fst x) (fst γ)))
      where
      x∈γPf : ((fst x ≡ fst γ) → Empty.⊥) → ⟨ fst x ∈ fst γ ⟩
      x∈γPf ¬v≡γ = D-in-dec x m ¬v≡γ

      sucPf : ⟨ fst x ∈ fst ω ⟩ → ⟨ (y ∷ x ∷ p ∷ []) ⊨ sucAtL (suc zero) zero ⟩
      sucPf x∈ω = subst (λ T → T) (sym (sucAtRead p x y))
        (shNum (fb x m) v∈ω' ∙ cong sucV (fb-eq x m))
        where
        v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩
        v∈ω' = subst (λ w → ⟨ w ∈ fst ω ⟩) (sym (fb-eq x m)) x∈ω

      topPf : (fst x ≡ fst γ) → ⟨ (y ∷ x ∷ p ∷ []) ⊨ (var zero ≐ con z) ⟩
      topPf x≡γ = shTop (fb x m) (fb-eq x m ∙ x≡γ)

      idPf : (⟨ fst x ∈ fst ω ⟩ → Empty.⊥) → ((fst x ≡ fst γ) → Empty.⊥)
           → ⟨ (y ∷ x ∷ p ∷ []) ⊨ (var zero ≐ var (suc zero)) ⟩
      idPf ¬v∈ω ¬v≡γ = shOther (fb x m) ¬v∈ω' ¬v≡γ' ∙ fb-eq x m
        where
        ¬v∈ω' : ⟨ ⟪ fst D ⟫↪ (fb x m) ∈ fst ω ⟩ → Empty.⊥
        ¬v∈ω' h = ¬v∈ω (subst (λ w → ⟨ w ∈ fst ω ⟩) (fb-eq x m) h)
        ¬v≡γ' : (⟪ fst D ⟫↪ (fb x m) ≡ fst γ) → Empty.⊥
        ¬v≡γ' h = ¬v≡γ (sym (fb-eq x m) ∙ h)

      go : ⟨ fst x ∈ fst ω ⟩ ⊎ (⟨ fst x ∈ fst ω ⟩ → Empty.⊥)
         → (fst x ≡ fst γ) ⊎ ((fst x ≡ fst γ) → Empty.⊥)
         → ⟨ (y ∷ x ∷ p ∷ []) ⊨ shiftRel γ ω z ⟩
      go (inl x∈ω) _ = ∣ inl ( x∈ω , sucPf x∈ω ) ∣₁
      go (inr ¬x∈ω) (inl x≡γ) = ∣ inr ∣ inl ( x≡γ , topPf x≡γ ) ∣₁ ∣₁
      go (inr ¬x∈ω) (inr ¬x≡γ) = ∣ inr ∣ inr ( x∈γPf ¬x≡γ , ¬x∈ω , idPf ¬x∈ω ¬x≡γ ) ∣₁ ∣₁

-- ---------------------------------------------------------------------
-- PART 3.  THE GRAPH, CARVED.  NOT ONE `hasReplacementL`.
--
-- The bound and the separation field are PARAMETERS, so no line of this
-- module names an L axiom or an L stage.  The shift itself arrives as a
-- function with three readback lemmas, so the module is blind to how the
-- shift was built.
-- ---------------------------------------------------------------------

module Carve (D C γ ω z : S)
             (sh : ⟪ fst D ⟫ → ⟪ fst C ⟫)
             (shInj : (m n : ⟪ fst D ⟫) → sh m ≡ sh n → m ≡ n)
             (shNum : (m : ⟪ fst D ⟫) (v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩)
                    → ⟪ fst C ⟫↪ (sh m) ≡ sucV (⟪ fst D ⟫↪ m))
             (shTop : (m : ⟪ fst D ⟫) (v≡γ : ⟪ fst D ⟫↪ m ≡ fst γ)
                    → ⟪ fst C ⟫↪ (sh m) ≡ fst z)
             (shOther : (m : ⟪ fst D ⟫) (¬v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ω ⟩ → Empty.⊥)
                      (¬v≡γ : (⟪ fst D ⟫↪ m ≡ fst γ) → Empty.⊥)
                      → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m)
             (D-in-dec : (x : S) → ⟨ x ∈ˢ D ⟩ → ((fst x ≡ fst γ) → Empty.⊥)
                       → ⟨ fst x ∈ fst γ ⟩)
             (bnd : S)
             (below : (x : S) (m : ⟨ x ∈ˢ D ⟩)
                    → ⟨ pr (fst x) (val D C sh x m) ∈ fst bnd ⟩)
             (sep : (b : S) (φ : Formula S 1)
                  → isContr (SetOf (λ w → (w ∈ˢ b) ⊓ ((w ∷ []) ⊨ φ)))) where

  module Fo = ShiftFo D C γ ω z sh shInj shNum shTop shOther D-in-dec

  private
    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

  opaque
    G : S
    G = fst (fst (sep bnd (shiftFo D γ ω z)))

    G-spec : (w : S) → (w ∈ˢ G) ≡ ((w ∈ˢ bnd) ⊓ ((w ∷ []) ⊨ shiftFo D γ ω z))
    G-spec = snd (fst (sep bnd (shiftFo D γ ω z)))

  G-out : (w : S) → ⟨ w ∈ˢ G ⟩
        → ∥ Σ[ x ∈ S ] Σ[ m ∈ ⟨ x ∈ˢ D ⟩ ]
            (fst w ≡ pr (fst x) (val D C sh x m)) ∥₁
  G-out w h = Fo.out w (snd (subst ⟨_⟩ (G-spec w) h))

  G-in : (w x : S) (m : ⟨ x ∈ˢ D ⟩) → fst w ≡ pr (fst x) (val D C sh x m)
       → ⟨ w ∈ˢ G ⟩
  G-in w x m e = subst ⟨_⟩ (sym (G-spec w))
    ( subst (λ t → ⟨ t ∈ fst bnd ⟩) (sym e) (below x m)
    , Fo.into w x m e )

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
           → ∥ Σ[ u ∈ S ] Σ[ m ∈ ⟨ u ∈ˢ D ⟩ ]
               ((fst x ≡ fst u) × (fst y ≡ val D C sh u m)) ∥₁
  pair-out x y h = PT.map step (G-out (prʟ x y) h')
    where
    h' : ⟨ prʟ x y ∈ˢ G ⟩
    h' = subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst x y)) h
    step : Σ[ u ∈ S ] Σ[ m ∈ ⟨ u ∈ˢ D ⟩ ]
             (fst (prʟ x y) ≡ pr (fst u) (val D C sh u m))
         → Σ[ u ∈ S ] Σ[ m ∈ ⟨ u ∈ˢ D ⟩ ]
             ((fst x ≡ fst u) × (fst y ≡ val D C sh u m))
    step (u , (m , e)) = u , m , pr-inj (sym (prʟ-fst x y) ∙ e)

  pair-in : (x : S) (m : ⟨ x ∈ˢ D ⟩) → ⟨ pr (fst x) (val D C sh x m) ∈ fst G ⟩
  pair-in x m = subst (λ w → ⟨ w ∈ fst G ⟩) (prʟ-fst x y)
                  (G-in (prʟ x y) x m (prʟ-fst x y))
    where
    y : S
    y = toC (sh (fiber (fst D) m .fst))

  -- THE FOUR CONJUNCTS.
  γ2 : S ^ 2
  γ2 = G ∷ D ∷ []

  sv : ⟨ γ2 ⊨ svAt zero ⟩
  sv = svAt-in zero γ2 go
    where
    go : (x y y' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
       → ⟨ pr (fst x) (fst y') ∈ fst G ⟩ → fst y ≡ fst y'
    go x y y' p q = PT.rec (setIsSet (fst y) (fst y'))
      (λ r → PT.rec (setIsSet (fst y) (fst y'))
        (λ r' → r .snd .snd .snd
          ∙ Fo.val-cong (r .fst) (r' .fst) (r .snd .fst) (r' .snd .fst)
              (sym (r .snd .snd .fst) ∙ r' .snd .snd .fst)
          ∙ sym (r' .snd .snd .snd))
        (pair-out x y' q))
      (pair-out x y p)

  ij : ⟨ γ2 ⊨ injAt zero ⟩
  ij = injAt-in zero γ2 go
    where
    go : (y x x' : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
       → ⟨ pr (fst x') (fst y) ∈ fst G ⟩ → fst x ≡ fst x'
    go y x x' p q = PT.rec (setIsSet (fst x) (fst x'))
      (λ r → PT.rec (setIsSet (fst x) (fst x'))
        (λ r' → r .snd .snd .fst
          ∙ Fo.val-inj (r .fst) (r' .fst) (r .snd .fst) (r' .snd .fst)
              (sym (r .snd .snd .snd) ∙ r' .snd .snd .snd)
          ∙ sym (r' .snd .snd .fst))
        (pair-out x' y q))
      (pair-out x y p)

  dm : ⟨ γ2 ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ2 (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
          (λ r → subst (λ w → ⟨ w ∈ fst D ⟩) (sym (r .snd .snd .fst)) (r .snd .fst))
          (pair-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ toC (sh (fiber (fst D) m .fst)) , pair-in x m ∣₁

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst C ⟩
  ran x y h = PT.rec (snd (fst y ∈ fst C))
    (λ r → subst (λ w → ⟨ w ∈ fst C ⟩) (sym (r .snd .snd .snd))
        (member (fst C) (sh (fiber (fst D) (r .snd .fst) .fst))))
    (pair-out x y h)

  -- THE READBACK, and it is the shift.  A graph that carves, proves four
  -- conjuncts and reads back as SOME injection is not evidence for THIS
  -- object.  `shiftFun-val` says the value is the shift's value.
  private
    module Sm = Small G D C sv dm ij ran

    fiber-member : (m : ⟪ fst D ⟫) → fiber (fst D) (member (fst D) m) .fst ≡ m
    fiber-member m = ↪-inj {a = fst D} (fiber (fst D) (member (fst D) m) .snd)

  opaque
    shiftFun : ⟪ fst D ⟫ → ⟪ fst C ⟫
    shiftFun = Sm.small

    shiftFun-inj : (m n : ⟪ fst D ⟫) → shiftFun m ≡ shiftFun n → m ≡ n
    shiftFun-inj = Sm.small-inj

    shiftFun-val : (m : ⟪ fst D ⟫) → shiftFun m ≡ sh m
    shiftFun-val m = ↪-inj {a = fst C} (snd (Sm.fib m) ∙ val')
      where
      val' : fst (Sm.E.toFun (Sm.at m)) ≡ ⟪ fst C ⟫↪ (sh m)
      val' = PT.rec (setIsSet (fst (Sm.E.toFun (Sm.at m))) (⟪ fst C ⟫↪ (sh m))) go
        (pair-out (Sm.toS m) (Sm.E.toFun (Sm.at m)) (Sm.E.toFun-graph (Sm.at m)))
        where
        go : Σ[ u ∈ S ] Σ[ mu ∈ ⟨ u ∈ˢ D ⟩ ]
               ((fst (Sm.toS m) ≡ fst u)
                × (fst (Sm.E.toFun (Sm.at m)) ≡ val D C sh u mu))
           → fst (Sm.E.toFun (Sm.at m)) ≡ ⟪ fst C ⟫↪ (sh m)
        go (u , (mu , (xEq , yEq))) =
          yEq
          ∙ Fo.val-cong u (Sm.toS m) mu (member (fst D) m) (sym xEq)
          ∙ cong (⟪ fst C ⟫↪) (cong sh (fiber-member m))

-- ---------------------------------------------------------------------
-- PART 4.  THE L INSTANTIATION.  It supplies the bound, the three-case
-- adequacy of the ambient shift, and `hasSeparationL`.  The bound is the
-- shared `StageBound` of `L.InjChain`.
-- ---------------------------------------------------------------------

module ShiftGraph (γ : S) (oγ : IsOrd (fst γ))
                  (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
                  (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩) where

  module SA = ShiftAbs (fst γ) oγ γ∉ω numerals

  D : S
  D = sucV (fst γ) , subst (λ x → ⟨ isL x ⟩) (sucʟ-fst γ) (snd (sucʟ γ))

  C : S
  C = γ

  sh : ⟪ fst D ⟫ → ⟪ fst C ⟫
  sh = SA.shift

  private
    -- The hierarchy numeral successor is the von Neumann successor.  The
    -- library's `#` steps by `sucV`, so this is definitional.
    sucV-# : (n : ℕ) → sucV (# n) ≡ # (suc n)
    sucV-# n = refl

    shInj : (m n : ⟪ fst D ⟫) → sh m ≡ sh n → m ≡ n
    shInj = SA.shift-inj

    shNum : (m : ⟪ fst D ⟫) (v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ωʟ ⟩)
          → ⟪ fst C ⟫↪ (sh m) ≡ sucV (⟪ fst D ⟫↪ m)
    shNum m v∈ω = SA.shift-num m v∈ω
      ∙ sym (sucV-# (SA.numeralOf (SA.v-of m) v∈ω))
      ∙ cong sucV (sym (SA.numeralOf-spec (SA.v-of m) v∈ω))

    shTop : (m : ⟪ fst D ⟫) (v≡γ : ⟪ fst D ⟫↪ m ≡ fst γ)
          → ⟪ fst C ⟫↪ (sh m) ≡ fst ∅ʟ
    shTop m v≡γ = SA.shift-top m v≡γ

    shOther : (m : ⟪ fst D ⟫) (¬v∈ω : ⟨ ⟪ fst D ⟫↪ m ∈ fst ωʟ ⟩ → Empty.⊥)
            (¬v≡γ : (⟪ fst D ⟫↪ m ≡ fst γ) → Empty.⊥)
            → ⟪ fst C ⟫↪ (sh m) ≡ ⟪ fst D ⟫↪ m
    shOther = SA.shift-other

    D-in-dec : (x : S) → ⟨ x ∈ˢ D ⟩ → ((fst x ≡ fst γ) → Empty.⊥)
             → ⟨ fst x ∈ fst γ ⟩
    D-in-dec x m ¬v≡γ = ∈sucV-elim {A = fst γ} {x = fst x} (snd (fst x ∈ fst γ)) m
      (λ q → q) (λ q → Empty.rec (¬v≡γ q))

    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

    dg : ⟪ fst D ⟫ → S
    dg m = prʟ (toD m) (toC (sh m))

    module SB = StageBound ⟪ fst D ⟫ dg

    bel : (x : S) (m : ⟨ x ∈ˢ D ⟩)
        → ⟨ pr (fst x) (val D C sh x m) ∈ fst SB.bnd ⟩
    bel x m = subst (λ w → ⟨ w ∈ fst SB.bnd ⟩) pa
      (SB.below (fiber (fst D) m .fst))
      where
      pa : fst (dg (fiber (fst D) m .fst)) ≡ pr (fst x) (val D C sh x m)
      pa = prʟ-fst (toD (fiber (fst D) m .fst)) (toC (sh (fiber (fst D) m .fst)))
         ∙ cong₂ pr (snd (fiber (fst D) m)) refl

  open Carve D C γ ωʟ ∅ʟ sh shInj shNum shTop shOther D-in-dec SB.bnd bel
    hasSeparationL public

-- ---------------------------------------------------------------------
-- PART 5.  A6's CONCLUSION, uniform over the infinite L-ordinals that
-- hold every numeral.  It was A7's `absorbs` hypothesis, written out.
-- The [LJ-1.323] restatement removed that hypothesis from the trophy,
-- so `AbsorbsShape` no longer exists and this shape is proof-side only.
-- ---------------------------------------------------------------------

absorbs : (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ ω ⟩ → Empty.⊥)
        → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
        → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫
absorbs γ oγ γ∉ω numerals = SG.shiftFun , SG.shiftFun-inj
  where
  module SG = ShiftGraph γ oγ γ∉ω numerals
```
