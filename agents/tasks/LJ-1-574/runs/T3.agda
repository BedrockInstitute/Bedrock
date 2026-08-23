{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.574] T3.  THE FORMULA FOR THE SELECTION.  Slice, run alone.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-574.runs.T3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ¬̇_; ∀̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in; injAt-out )
open import L.InjChain {ℓ} lem using ( appC; appC-adequate )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; IsLeast; isPropLeastOf )
open import L.Choice.Step {ℓ} lem using ( Mem; relOf; orderAt )
open import L.Choice.Order {ℓ} lem using ( relL; relL-fill; relL-rep )

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

import LJ-1-549.Probe549 {ℓ} lem as P549
import LJ-1-554.Probe554 {ℓ} lem as P554
import LJ-1-574.runs.T2 {ℓ} lem as T2

open T2 using ( S-path; upS )


-- ===================================================================
-- SECTION 1.  `InjCode` AS A FORMULA AT ANY TWO SLOTS.
--
--   W3 wrote it at slots (0,1,2) with the target a VARIABLE.  Here the
--   target is a CONSTANT and the two slots are free, because the
--   selection's description reads the same condition twice: once at
--   the value, once under a quantifier where every index has shifted.
-- ===================================================================

valFoAt : {n : ℕ} → Fin n → S → Formula S n
valFoAt f c = ∀̇ (∀̇ ( appAt (fsuc (fsuc f)) (fsuc fzero) fzero
                   ⇒̇ (var fzero ∈̇ con c) ))

valFoAt-adequate : {n : ℕ} (f : Fin n) (c : S) (γ : S ^ n)
  → ⟨ γ ⊨ valFoAt f c ⟩
  ≡ ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩ → ⟨ fst y ∈ fst c ⟩)
valFoAt-adequate f c γ i =
  (x y : S)
  → ⟨ appAt-adequate (fsuc (fsuc f)) (fsuc fzero) fzero (y ∷ x ∷ γ) i ⟩
  → ⟨ fst y ∈ fst c ⟩

codeFoAt : {n : ℕ} → Fin n → Fin n → S → Formula S n
codeFoAt f d c = svAt f ∧̇ (domAt f d ∧̇ (injAt f ∧̇ valFoAt f c))

private
  domBoth : {n : ℕ} (f d : Fin n) (γ : S ^ n) (F a : S)
          → (F ≡ lookup f γ) → (a ≡ lookup d γ)
          → ⟨ (F ∷ a ∷ []) ⊨ domAt fzero (fsuc fzero) ⟩
          → (x : S)
          → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
             → ⟨ fst x ∈ fst (lookup d γ) ⟩)
          × (⟨ fst x ∈ fst (lookup d γ) ⟩
             → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩)
  domBoth f d γ F a ef ea dm x =
      PT.rec (snd (fst x ∈ fst (lookup d γ)))
        (λ { (y , p) → subst (λ t → ⟨ fst x ∈ fst t ⟩) ea
               (domAt-out fzero (fsuc fzero) (F ∷ a ∷ []) dm x y
                 (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)) })
    , (λ h → PT.map (λ { (y , p) →
               y , subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p })
        (domAt-in fzero (fsuc fzero) (F ∷ a ∷ []) dm x
          (subst (λ t → ⟨ fst x ∈ fst t ⟩) (sym ea) h)))

codeFoAt-in : {n : ℕ} (f d : Fin n) (c : S) (γ : S ^ n) (F a : S)
            → (F ≡ lookup f γ) → (a ≡ lookup d γ)
            → InjCode F a c → ⟨ γ ⊨ codeFoAt f d c ⟩
codeFoAt-in f d c γ F a ef ea (sv , dm , ij , vl) =
    svAt-in f γ (λ x y y' p q →
      svAt-out fzero (F ∷ a ∷ []) sv x y y'
        (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)
        (subst (λ t → ⟨ pr (fst x) (fst y') ∈ fst t ⟩) (sym ef) q))
  , ( domAt-intro f d γ (domBoth f d γ F a ef ea dm)
    , ( injAt-in f γ (λ y x x' p q →
          injAt-out fzero (F ∷ a ∷ []) ij y x x'
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)
            (subst (λ t → ⟨ pr (fst x') (fst y) ∈ fst t ⟩) (sym ef) q))
      , transport (sym (valFoAt-adequate f c γ))
          (λ x y p → vl x y
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p)) ) )

codeFoAt-out : {n : ℕ} (f d : Fin n) (c : S) (γ : S ^ n) (F a : S)
             → (F ≡ lookup f γ) → (a ≡ lookup d γ)
             → ⟨ γ ⊨ codeFoAt f d c ⟩ → InjCode F a c
codeFoAt-out f d c γ F a ef ea (sv , (dm , (ij , vl))) =
    svAt-in fzero (F ∷ a ∷ []) (λ x y y' p q →
      svAt-out f γ sv x y y'
        (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)
        (subst (λ t → ⟨ pr (fst x) (fst y') ∈ fst t ⟩) ef q))
  , ( domAt-intro fzero (fsuc fzero) (F ∷ a ∷ []) dom₀
    , ( injAt-in fzero (F ∷ a ∷ []) (λ y x x' p q →
          injAt-out f γ ij y x x'
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)
            (subst (λ t → ⟨ pr (fst x') (fst y) ∈ fst t ⟩) ef q))
      , (λ x y p → transport (valFoAt-adequate f c γ) vl x y
            (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)) ) )
  where
  dom₀ : (x : S)
       → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩)
       × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩)
  dom₀ x =
      PT.rec (snd (fst x ∈ fst a))
        (λ { (y , p) → subst (λ t → ⟨ fst x ∈ fst t ⟩) (sym ea)
               (domAt-out f d γ dm x y
                 (subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) ef p)) })
    , (λ h → PT.map (λ { (y , p) →
               y , subst (λ t → ⟨ pr (fst x) (fst y) ∈ fst t ⟩) (sym ef) p })
        (domAt-in f d γ dm x (subst (λ t → ⟨ fst x ∈ fst t ⟩) ea h)))


-- ===================================================================
-- SECTION 2.  THE DESCRIPTION, AND ITS TWO READINGS.
--
--   THE SHAPE IS `L.Choice.Transversal.Pick`
--   (src/L/Choice/Transversal.lagda.md:116-123) AND NOT A NEW IDEA:
--   a member of the stage, a condition on it, and nothing before it in
--   the stage's own order, with that order pinned as a CONSTANT
--   because it is an element of the model (src/L/Choice/Order.lagda.md:693).
--   Only the condition is new: "codes an injection of x into κ".
-- ===================================================================

module Link (δ κ : S) (β : V ℓ) (oβ : IsOrd β)
            (codes : (a : S) → ⟨ fst a ∈ fst δ ⟩
                   → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁)
            where

  module Sel = T2.Select δ κ β oβ codes

  βisL : ⟨ isL β ⟩
  βisL = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

  c : S
  c = LsetS β oβ

  r : S
  r = relL β βisL oβ

  w : SWO (Mem (Lset β))
  w = orderAt β oβ

  -- THE DESCRIPTION.  Environment (y ∷ x ∷ z ∷ []); `z` is `LinkAt`'s
  -- third slot and no conjunct reads it.
  Fo : Formula S 3
  Fo = (var fzero ∈̇ con c)
     ∧̇ ( codeFoAt fzero (fsuc fzero) κ
       ∧̇ (¬̇ ∃̇ ( (var fzero ∈̇ con c)
               ∧̇ ( codeFoAt fzero (fsuc (fsuc fzero)) κ
                 ∧̇ appC r fzero (fsuc fzero) ) )) )

  private
    memOf : (y : S) → ⟨ fst y ∈ Lset β ⟩ → Mem (Lset β)
    memOf y h = fst y , h

    upEq : (y : S) (h : ⟨ fst y ∈ Lset β ⟩) → Sel.upM (memOf y h) ≡ y
    upEq y h = S-path (Sel.upM (memOf y h)) y refl

  -- READING ONE.  The selected value satisfies the description.
  lin : (x y z : S) (m : ⟨ fst x ∈ fst δ ⟩)
      → fst y ≡ fst (Sel.s (P549.ixOf δ x m))
      → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Fo ⟩
  lin x y z m e = c1 , (c2 , c3)
    where
    k : ⟪ fst δ ⟫
    k = P549.ixOf δ x m

    xk : x ≡ Sel.memD k
    xk = S-path x (Sel.memD k) (sym (P549.ixOf-val δ x m))

    yk : y ≡ Sel.s k
    yk = S-path y (Sel.s k) e

    c1 : ⟨ fst y ∈ Lset β ⟩
    c1 = subst (λ t → ⟨ t ∈ Lset β ⟩) (sym e) (snd (Sel.gm k))

    c2 : ⟨ (y ∷ x ∷ z ∷ []) ⊨ codeFoAt fzero (fsuc fzero) κ ⟩
    c2 = PT.rec (snd ((y ∷ x ∷ z ∷ []) ⊨ codeFoAt fzero (fsuc fzero) κ))
           (λ code → codeFoAt-in fzero (fsuc fzero) κ (y ∷ x ∷ z ∷ []) y x
                       refl refl
                       (subst (λ u → InjCode u x κ) (sym yk)
                         (subst (λ v → InjCode (Sel.s k) v κ) (sym xk) code)))
           (Sel.s-good k)

    c3 : ⟨ (y ∷ x ∷ z ∷ []) ⊨
            (¬̇ ∃̇ ( (var fzero ∈̇ con c)
                  ∧̇ ( codeFoAt fzero (fsuc (fsuc fzero)) κ
                    ∧̇ appC r fzero (fsuc fzero) ) )) ⟩
    c3 = PT.rec Empty.isProp⊥ bad
      where
      bad : Σ[ y' ∈ S ]
              ( ⟨ fst y' ∈ Lset β ⟩
              × ( ⟨ (y' ∷ y ∷ x ∷ z ∷ []) ⊨ codeFoAt fzero (fsuc (fsuc fzero)) κ ⟩
                × ⟨ (y' ∷ y ∷ x ∷ z ∷ []) ⊨ appC r fzero (fsuc fzero) ⟩ ) )
          → Empty.⊥
      bad (y' , (y'∈ , (cod , rel))) = Sel.s-min k F' good below
        where
        F' : Mem (Lset β)
        F' = memOf y' y'∈

        good : ⟨ Sel.Good k F' ⟩
        good = ∣ subst (λ u → InjCode u (Sel.memD k) κ) (sym (upEq y' y'∈))
                 (subst (λ v → InjCode y' v κ) xk
                   (codeFoAt-out fzero (fsuc (fsuc fzero)) κ
                     (y' ∷ y ∷ x ∷ z ∷ []) y' x refl refl cod)) ∣₁

        below : relOf w F' (Sel.gm k)
        below = relL-rep β βisL oβ F' (Sel.gm k)
          (subst (λ t → ⟨ pr (fst y') t ∈ fst r ⟩) e
            (subst ⟨_⟩ (appC-adequate r fzero (fsuc fzero)
                         (y' ∷ y ∷ x ∷ z ∷ [])) rel))

  -- READING TWO.  Only the selected value satisfies it.
  lout : (x y z : S) → ⟨ (y ∷ x ∷ z ∷ []) ⊨ Fo ⟩
       → (m : ⟨ fst x ∈ fst δ ⟩) → fst y ≡ fst (Sel.s (P549.ixOf δ x m))
  lout x y z (c1 , (c2 , c3)) m =
    cong fst (cong fst (isPropLeastOf w (Sel.Good k) (Fy , leastFy)
                                        (Sel.gm k , snd (Sel.least k))))
    where
    k : ⟪ fst δ ⟫
    k = P549.ixOf δ x m

    xk : x ≡ Sel.memD k
    xk = S-path x (Sel.memD k) (sym (P549.ixOf-val δ x m))

    Fy : Mem (Lset β)
    Fy = memOf y c1

    codeY : InjCode y x κ
    codeY = codeFoAt-out fzero (fsuc fzero) κ (y ∷ x ∷ z ∷ []) y x refl refl c2

    goodY : ⟨ Sel.Good k Fy ⟩
    goodY = ∣ subst (λ u → InjCode u (Sel.memD k) κ) (sym (upEq y c1))
              (subst (λ v → InjCode y v κ) xk codeY) ∣₁

    minY : (b : Mem (Lset β)) → ⟨ Sel.Good k b ⟩ → relOf w b Fy → Empty.⊥
    minY b gb rb = c3 ∣ Sel.upM b , (snd b , (codB , relB)) ∣₁
      where
      codB : ⟨ (Sel.upM b ∷ y ∷ x ∷ z ∷ []) ⊨ codeFoAt fzero (fsuc (fsuc fzero)) κ ⟩
      codB = PT.rec (snd ((Sel.upM b ∷ y ∷ x ∷ z ∷ [])
                            ⊨ codeFoAt fzero (fsuc (fsuc fzero)) κ))
        (λ code → codeFoAt-in fzero (fsuc (fsuc fzero)) κ
                    (Sel.upM b ∷ y ∷ x ∷ z ∷ []) (Sel.upM b) x refl refl
                    (subst (λ v → InjCode (Sel.upM b) v κ) (sym xk) code))
        gb

      relB : ⟨ (Sel.upM b ∷ y ∷ x ∷ z ∷ []) ⊨ appC r fzero (fsuc fzero) ⟩
      relB = subst ⟨_⟩ (sym (appC-adequate r fzero (fsuc fzero)
                              (Sel.upM b ∷ y ∷ x ∷ z ∷ [])))
               (relL-fill β βisL oβ b Fy rb)

    leastFy : IsLeast w (Sel.Good k) Fy
    leastFy = goodY , minY

  -- AND THE LINK, IN [LJ-1.554]'s OWN TYPE.
  link : P554.LinkAt δ Sel.s
  link = Fo , (lin , lout)
