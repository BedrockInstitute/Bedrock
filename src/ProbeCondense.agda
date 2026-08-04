{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- [L3.31-IVp] D-1 probe: the CONDENSATION miniature over the delivered
-- internalized stock.  Untracked, no master touched, Everything untouched.
--
-- Three pieces, per the brief:
--   1. STATEMENT COST -- can "a transitive set M satisfies the level-hood
--      face" be stated today, and what carries it?
--   2. THE SUCCESSOR CASE of the condensation induction, in miniature.
--   3. The residue, measured (the hull is priced in the report, not built).
------------------------------------------------------------------------

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeCondense {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; Transitive; module hPropStructure )
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; isTransV; IsOrd; 𝒟ₒ; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )

open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open SemV.At S (λ x → x) using () renaming ( _⊨_ to _⊨ⱽ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

Sʟ : Type (ℓ-suc ℓ)
Sʟ = AbsL.SM

-- Ordinals are constructible: two delivered exports, one line.
ord-isL : (a : S) → IsOrd a → ⟨ isL a ⟩
ord-isL a oa = Lset→isL (sucV a) (suc-ord oa) a (ord∈Lset-suc a oa)

------------------------------------------------------------------------
-- PIECE 1.  The statement, at a transitive SET carrier.
------------------------------------------------------------------------

module AtCarrier (M : S) (Mtr : isTransV M) where

  -- 1a.  The set carrier is a first-class restriction class: `Single`
  -- instantiates at `∈ˢ M` exactly as it does at `isL`, and delivers the
  -- inner reading, the ambient reading, abs₀, σ₁-up and π₁-down for free.
  module AbsM = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ M) Mtr

  Sᴹ : Type (ℓ-suc ℓ)
  Sᴹ = AbsM.SM

  InM : Sʟ → Type (ℓ-suc ℓ)
  InM c = ⟨ fst c ∈ˢ M ⟩

  -- 1b.  The certified transport Formula Sʟ n → Formula Sᴹ n exists and
  -- instantiates in five lines: the delivered `Bounding.Relabel` machine.
  module Down = Relabel {K = Sʟ} {K' = Sᴹ} {W = S}
                  fst fst InM (λ c p → fst c , p) (λ c p → refl)

  ----------------------------------------------------------------------
  -- The face, generic in the formula (Rule 9 / R-25: never name the
  -- closed sentence in a type that a proof must convert against).
  ----------------------------------------------------------------------

  Believes : Formula Sᴹ 2 → Sᴹ → Sᴹ → Type (ℓ-suc ℓ)
  Believes φ v b = ⟨ (v ∷ b ∷ []) AbsM.⊨ᵐ φ ⟩

  -- The crossing, out of the inner world (all the assembly ever needs).
  CrossOut : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  CrossOut φ = (v b : Sᴹ) → IsOrd (fst b) → Believes φ v b
             → fst v ≡ Lset (fst b)

  -- M's internal story, two clauses.
  HasLevels : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  HasLevels φ = (b : Sᴹ) → IsOrd (fst b) → ∥ Σ[ v ∈ Sᴹ ] Believes φ v b ∥₁

  Covered : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  Covered φ = (x : Sᴹ)
            → ∥ Σ[ b ∈ Sᴹ ] Σ[ v ∈ Sᴹ ]
                (IsOrd (fst b) × Believes φ v b × ⟨ fst x ∈ˢ fst v ⟩) ∥₁

  -- M closed under the ordinal successor (a fragment of M's internal ZF).
  SucClosed : Type (ℓ-suc ℓ)
  SucClosed = (b : Sᴹ) → IsOrd (fst b) → ⟨ sucV (fst b) ∈ˢ M ⟩

  -- The target of the whole theorem.
  Condenses : Type (ℓ-suc ℓ)
  Condenses = Σ[ β ∈ S ] (IsOrd β × (M ≡ Lset β))

  ----------------------------------------------------------------------
  -- PIECE 2.  The condensation assembly over the delivered tower.
  ----------------------------------------------------------------------

  module Face (φ : Formula Sᴹ 2) (co : CrossOut φ) where

    -- (A) THE SUCCESSOR CLAUSE.  If M's story gives a level at δ+1, then
    -- every definable subset of the δ-th level is already a member of M.
    -- This is "the collapsed image of a stage is a stage", and over the
    -- delivered tower it is `Lset-suc` plus M's transitivity.
    succ-step : HasLevels φ → SucClosed
              → (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ
              → (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩ → ⟨ x ∈ˢ M ⟩
    succ-step hl sc δ δ∈ oδ x x∈ =
      PT.rec (snd (x ∈ˢ M)) go (hl b (suc-ord oδ))
      where
      b : Sᴹ
      b = sucV δ , sc (δ , δ∈) oδ
      go : Σ[ v ∈ Sᴹ ] Believes φ v b → ⟨ x ∈ˢ M ⟩
      go (v , hv) = Mtr {x = fst v} {y = x}
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym q) x∈) (snd v)
        where
        q : fst v ≡ 𝒟ₒ (Lset δ)
        q = co v b (suc-ord oδ) hv ∙ Lset-suc δ

    -- (B) Every level indexed inside M is a MEMBER of M.
    level-in : HasLevels φ
             → (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ → ⟨ Lset δ ∈ˢ M ⟩
    level-in hl δ δ∈ oδ =
      PT.rec (snd (Lset δ ∈ˢ M)) go (hl (δ , δ∈) oδ)
      where
      go : Σ[ v ∈ Sᴹ ] Believes φ v (δ , δ∈) → ⟨ Lset δ ∈ˢ M ⟩
      go (v , hv) =
        subst (λ w → ⟨ w ∈ˢ M ⟩) (co v (δ , δ∈) oδ hv) (snd v)

    -- (C) M ⊆ L.  This is the half the GCH endgame actually consumes.
    M⊆L : Covered φ → (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ isL x ⟩
    M⊆L cv x x∈ = PT.rec (snd (isL x)) go (cv (x , x∈))
      where
      go : Σ[ b ∈ Sᴹ ] Σ[ v ∈ Sᴹ ]
             (IsOrd (fst b) × Believes φ v b × ⟨ x ∈ˢ fst v ⟩)
         → ⟨ isL x ⟩
      go (b , v , ob , hv , x∈v) = Lset→isL (fst b) ob x
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (co v b ob hv) x∈v)

  ----------------------------------------------------------------------
  -- PIECE 3.  The residue: where CrossOut has to come from.
  ----------------------------------------------------------------------

  -- The transported formula has the SAME ambient meaning as the original.
  -- Generic in the formula, so no closed sentence is ever normalized.
  module Transport (Φ : Formula Sʟ 2) (h : BoundedFo InM Φ) where

    lifted : Formula Sᴹ 2
    lifted = Down.liftFo Φ h

    amb-agree : (γ : S ^ 2) → (γ AbsM.⊨ᵛ lifted) ≡ (γ AbsL.⊨ᵛ Φ)
    amb-agree γ =
        sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst (λ x → x) lifted γ)
      ∙ cong (λ ψ → γ ⊨ⱽ ψ) (Down.liftFo-correct Φ h)
      ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst (λ x → x) Φ γ

  -- The transfer M's inner reading would need (what σ₁-up would give).
  TransferM : Formula Sᴹ 2 → Type (ℓ-suc ℓ)
  TransferM φ = (v b : Sᴹ) → ⟨ (v ∷ b ∷ []) AbsM.⊨ᵐ φ ⟩
              → ⟨ (fst v ∷ fst b ∷ []) AbsM.⊨ᵛ φ ⟩

------------------------------------------------------------------------
-- The ambient-reading form of `Lset-only`.  NOT delivered: the tree's
-- `Lset-only` is stated at AbsL's INNER reading, i.e. at the class L.
------------------------------------------------------------------------

AmbientOnly : Type (ℓ-suc ℓ)
AmbientOnly = (v b : S) → IsOrd b
            → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
            → v ≡ Lset b

-- ... and it factors into exactly two things, both undelivered: the
-- transfer at L (what π₁-down would give) and the value's constructibility.
TransferL : Type (ℓ-suc ℓ)
TransferL = (v b : Sʟ)
          → ⟨ (fst v ∷ fst b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
          → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩

ValueIsL : Type (ℓ-suc ℓ)
ValueIsL = (v b : S) → IsOrd b
         → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
         → ⟨ isL v ⟩

ambientOnly-from : TransferL → ValueIsL → AmbientOnly
ambientOnly-from tl vl v b ob h =
  Lset-only zero (suc zero) (vL ∷ bL ∷ []) (tl vL bL h) ob
  where
  bL : Sʟ
  bL = b , ord-isL b ob
  vL : Sʟ
  vL = v , vl v b ob h

-- The whole crossing, assembled: at a transitive set carrier the inner
-- face crosses out through ONE transfer at M and the ambient form at L.
module Crossing (M : S) (Mtr : isTransV M)
                (h : BoundedFo (AtCarrier.InM M Mtr)
                       (LsetGraphAt {2} zero (suc zero))) where

  open AtCarrier M Mtr
  open Transport (LsetGraphAt {2} zero (suc zero)) h

  crossOut-from : TransferM lifted → AmbientOnly → CrossOut lifted
  crossOut-from tm ao v b ob hv =
    ao (fst v) (fst b) ob
       (subst ⟨_⟩ (amb-agree (fst v ∷ fst b ∷ [])) (tm v b hv))

------------------------------------------------------------------------
-- PIECE 3b.  The measurement (C-6): the level formula's quantifier
-- profile, which decides whether ANY delivered transfer theorem applies.
-- (size , constant occurrences , unbounded ∃̇ , unbounded ∀̇)
------------------------------------------------------------------------

private
  Q : Type
  Q = ℕ × ℕ × ℕ × ℕ

  _⊕_ : Q → Q → Q
  (a , b , c , d) ⊕ (a' , b' , c' , d') = (a + a' , b + b' , c + c' , d + d')

  node : Q
  node = 1 , 0 , 0 , 0

  qT : ∀ {ℓk} {K : Type ℓk} {n} → Term K n → Q
  qT (con _) = 1 , 1 , 0 , 0
  qT (var _) = 1 , 0 , 0 , 0

  q : ∀ {ℓk} {K : Type ℓk} {n} → Formula K n → Q
  q (t ∈̇ u)  = node ⊕ (qT t ⊕ qT u)
  q (t ≐ u)  = node ⊕ (qT t ⊕ qT u)
  q (a ∧̇ b)  = node ⊕ (q a ⊕ q b)
  q (a ∨̇ b)  = node ⊕ (q a ⊕ q b)
  q (a ⇒̇ b)  = node ⊕ (q a ⊕ q b)
  q (¬̇ a)    = node ⊕ q a
  q ⊤̇        = node
  q ⊥̇        = node
  q (∃̇ a)    = (1 , 0 , 1 , 0) ⊕ q a
  q (∀̇ a)    = (1 , 0 , 0 , 1) ⊕ q a
  q (∀̇∈ t a) = node ⊕ (qT t ⊕ q a)
  q (∃̇∈ t a) = node ⊕ (qT t ⊕ q a)

  -- R2p measured 169,683 nodes / 1,688 constants / 2,287 ∃̇ / 2,159 ∀̇ on
  -- 2026-08-03.  Re-verified here on today's tree, drift check.
  profile : Q
  profile = q (LsetGraphAt {2} zero (suc zero))

  -- Forces the normalization.  A wrong numeral prints the true tuple.
  check : profile ≡ (208565 , 1688 , 2287 , 2159)
  check = refl
