{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.574] T2.  THE SELECTION AT THE UNIFORM STAGE.  Slice, run alone.
--
-- T1 put a code for EVERY member of δ inside ONE stage.  T2 picks the
-- least one, in the stage's own well-order, and shows the pick is
-- injective.  The formula comes in T3.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-574.runs.T2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL; Lset-layer; layer-trans )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ} using ( domAt-in; domAt-out )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; isPropLeastOf )
open import L.Choice.Step {ℓ} lem using ( Mem; relOf; orderAt )

open import Cubical.Data.FinData using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax; ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )


-- A path of the L-carrier is a path of its first component.
S-path : (u v : S) → fst u ≡ fst v → u ≡ v
S-path u v = Σ≡Prop (λ x → snd (isL x))

-- The L-element of a member of an L-set.
upS : (b : S) → ⟪ fst b ⟫ → S
upS b m = ⟪ fst b ⟫↪ m , isL-trans (member (fst b) m) (snd b)


module Select (δ κ : S)
              (β : V ℓ) (oβ : IsOrd β)
              (codes : (a : S) → ⟨ fst a ∈ fst δ ⟩
                     → ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset β ⟩ × InjCode F a κ) ∥₁)
              where

  -- A member of the stage, as an L-element.
  upM : Mem (Lset β) → S
  upM m = fst m , Lset→isL β oβ (fst m) (snd m)

  -- The k-th member of δ, as an L-element.
  memD : ⟪ fst δ ⟫ → S
  memD = upS δ

  -- THE PREDICATE.  Truncated, because `InjCode` is a Σ and the search
  -- takes an hProp.  Nothing is lost: the conclusion is truncated too.
  Good : ⟪ fst δ ⟫ → Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good k F = ∥ InjCode (upM F) (memD k) κ ∥₁ , squash₁

  nonempty : (k : ⟪ fst δ ⟫) → ∥ Σ[ F ∈ Mem (Lset β) ] ⟨ Good k F ⟩ ∥₁
  nonempty k = PT.map
    (λ { (F , (F∈β , code)) →
         (fst F , F∈β)
       , ∣ subst (λ u → InjCode u (memD k) κ) (S-path F (upM (fst F , F∈β)) refl)
             code ∣₁ })
    (codes (memD k) (member (fst δ) k))

  least : (k : ⟪ fst δ ⟫)
        → Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) (Good k) F
  least k = leastOf (orderAt β oβ) lem (Good k) (nonempty k)

  -- THE ASSIGNMENT, as a member of the stage and as an L-element.
  gm : ⟪ fst δ ⟫ → Mem (Lset β)
  gm k = fst (least k)

  s : ⟪ fst δ ⟫ → S
  s k = upM (gm k)

  s-good : (k : ⟪ fst δ ⟫) → ∥ InjCode (s k) (memD k) κ ∥₁
  s-good k = fst (snd (least k))

  s-min : (k : ⟪ fst δ ⟫) (F : Mem (Lset β)) → ⟨ Good k F ⟩
        → relOf (orderAt β oβ) F (gm k) → Empty.⊥
  s-min k = snd (snd (least k))

  -- THE SAME, in the stage's presentation, which is the shape the
  -- obligation asks for.
  g : ⟪ fst δ ⟫ → ⟪ Lset β ⟫
  g k = fiber (Lset β) (snd (gm k)) .fst

  g-val : (k : ⟪ fst δ ⟫) → ⟪ Lset β ⟫↪ (g k) ≡ fst (s k)
  g-val k = fiber (Lset β) (snd (gm k)) .snd

  -- INJECTIVITY, AND IT IS FREE.  A code determines its DOMAIN, by
  -- `domAt` in both directions (src/L/Coding/Model.lagda.md:296,:302),
  -- and the domain of the code at `k` is the k-th member of δ.  So two
  -- members of δ with the same code have the same members, hence are
  -- equal by extensionality, hence have the same index.
  private
    dom-eq : (k k' : ⟪ fst δ ⟫) → s k ≡ s k'
           → InjCode (s k) (memD k) κ → InjCode (s k') (memD k') κ
           → fst (memD k) ≡ fst (memD k')
    dom-eq k k' e ck ck' =
      extensionalV {a = fst (memD k)} {b = fst (memD k')}
        (λ z → ⇔toPath (fwd z) (bwd z))
      where
      Fk = s k
      dmk = fst (snd ck)
      dmk' = fst (snd ck')

      toS : (z : V ℓ) (u : S) → ⟨ z ∈ fst u ⟩ → S
      toS z u h = z , isL-trans {x = fst u} {y = z} h (snd u)

      fwd : (z : V ℓ) → ⟨ z ∈ fst (memD k) ⟩ → ⟨ z ∈ fst (memD k') ⟩
      fwd z hz = PT.rec (snd (z ∈ fst (memD k')))
        (λ { (y , p) → domAt-out fzero (fsuc fzero) (s k' ∷ memD k' ∷ []) dmk'
                         (toS z (memD k) hz) y
                         (subst (λ t → ⟨ pr z (fst y) ∈ fst t ⟩) e p) })
        (domAt-in fzero (fsuc fzero) (Fk ∷ memD k ∷ []) dmk
           (toS z (memD k) hz) hz)

      bwd : (z : V ℓ) → ⟨ z ∈ fst (memD k') ⟩ → ⟨ z ∈ fst (memD k) ⟩
      bwd z hz = PT.rec (snd (z ∈ fst (memD k)))
        (λ { (y , p) → domAt-out fzero (fsuc fzero) (Fk ∷ memD k ∷ []) dmk
                         (toS z (memD k') hz) y
                         (subst (λ t → ⟨ pr z (fst y) ∈ fst t ⟩) (sym e) p) })
        (domAt-in fzero (fsuc fzero) (s k' ∷ memD k' ∷ []) dmk'
           (toS z (memD k') hz) hz)

  isSet⟪δ⟫ : isSet ⟪ fst δ ⟫
  isSet⟪δ⟫ = Embedding-into-isSet→isSet
               (⟪ fst δ ⟫↪ , isEmb⟪ fst δ ⟫↪) setIsSet

  ginj : (k k' : ⟪ fst δ ⟫) → g k ≡ g k' → k ≡ k'
  ginj k k' e = PT.rec (isSet⟪δ⟫ k k')
    (λ ck → PT.rec (isSet⟪δ⟫ k k') (λ ck' → step ck ck') (s-good k'))
    (s-good k)
    where
    se : s k ≡ s k'
    se = S-path (s k) (s k') (sym (g-val k) ∙ cong (⟪ Lset β ⟫↪) e ∙ g-val k')

    step : InjCode (s k) (memD k) κ → InjCode (s k') (memD k') κ → k ≡ k'
    step ck ck' = ↪-inj {a = fst δ} (dom-eq k k' se ck ck')
