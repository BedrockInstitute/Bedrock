{-# OPTIONS --cubical --safe --guardedness #-}

-- O7. THE CLASSICAL DEFINABILITY LEMMA, stated once and projected three times.
--
-- THE GENERAL STATEMENT. For each FIXED formula of the extension's language,
-- the relation "r forces phi at the environment nu" is internally definable in
-- the ground by one ground formula whose free slots are the CODE OF THE
-- CONDITION and the CODES OF THE NAMES in nu, in that order:
--
--   forcesD         : forall {k} -> Formula Nm k -> Formula S (suc k)
--   forcesD-reading : forall {k} (phi : Formula Nm k) (nu : Vec Nm k) (r : Cond)
--                   -> ((cnd r :: codesOf nu) |= forcesD phi) == forces r phi nu
--
-- It is a HOST function from an object formula to a ground formula, the shape
-- `interp` already has at K4/Compile.agda:1061, and never an internal function
-- on codes of formulas.
--
-- WHAT THIS FILE PROVES. That datum alone, with K3's name kernel and no axiom
-- of the ground at all, yields all THREE of the projections K6 pays for:
-- Track F's sepD (K6/Separation.agda:280-283), Track E's powD
-- (K6/Power.agda:369-373) and Track H's colD (K6/Replacement.agda:331-336),
-- each at its own arity and each with its reading theorem in the consumer's
-- verbatim shape. The three differ only by a renaming and, for the two that
-- read at an entry, by one Kuratowski repackaging.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula; Term; con; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import Cubical.Functions.Logic using ( ⇔toPath )
import FOL.Semantics
import CodedVocabulary
import Cubical.HITs.PropositionalTruncation as PT

open PT using ( ∣_∣₁ )

module O7.Definability {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- Ground satisfaction, the SAME instance the three consumers read their cut
-- formulas in: FOL.Semantics at the ground structure with the ground sets as
-- their own constants. K6/Separation.agda:148-149, K4/Compile.agda:112 and
-- CodedVocabulary.agda:57 all take `At S id`.

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
open SemG using ( _^_ )
module SatG = SemG.At S id
open SatG using () renaming ( _⊨_ to _⊨ᴳ_ )

open Sat (hPropAlgebra ℓ) 𝒮 {K = S} id using ( Agrees; ⊨-rename )

open CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ; prAtˢ-reading )

--------------------------------------------------------------------------------
-- The name kernel, flat
--------------------------------------------------------------------------------

-- No axiom of the ground profile appears in this file: the three projections
-- below are formula manipulation plus one kernel identity.

module Names (IsNm : S → Ω) where

  -- The name type, spelled as the consumers spell it: K6/Separation.agda:
  -- 173-174 and K6/Power.agda:214-215 are this Sigma at two recognisers.

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩

  codesOf : ∀ {k} → Vec Nm k → S ^ k
  codesOf []      = []
  codesOf (σ ∷ ν) = fst σ ∷ codesOf ν

  -- Three of K3's kernel facts and nothing else. entry-isKPair is
  -- NameKernel.agda:332, kpair-unique is NameSpace.agda:388 (whose ground
  -- Extensionality is spent there, not here), entry-inj is NameKernel.agda:321.

  module Kernel
    (entry         : S → S → S)
    (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
    (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
    (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
    where

  ------------------------------------------------------------------------------
  -- THE DATUM
  ------------------------------------------------------------------------------

    module Datum
      (Cond            : Type ℓ)
      (cnd             : Cond → S)
      (forces          : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (forcesΔ         : ∀ {k} → Formula Nm k → Formula S (suc k))
      (forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                       → ((cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ) ≡ forces r φ ν)
      where

      ----------------------------------------------------------------------
      -- Repackaging a two slot reading as a reading at one entry
      ----------------------------------------------------------------------

      -- The inclusion of the two slots (condition , subname code) into the
      -- three slot context (condition , subname code , entry) that the two
      -- existentials open. Slot 0 stays the condition and slot 1 stays the
      -- subname code, so both agreements are refl.

      ρE : Fin 2 → Fin 3
      ρE zero       = zero
      ρE (suc zero) = suc zero

      ρE-ag : (p x e : S) → Agrees ρE (p ∷ x ∷ e ∷ []) (p ∷ x ∷ [])
      ρE-ag p x e zero       = refl
      ρE-ag p x e (suc zero) = refl

      -- "the argument is the Kuratowski pair of some x and some p, and theta
      -- holds of that p and that x". The pair clause is CodedVocabulary's
      -- prAtˢ, whose reading is refl, at (q , u , v) = (entry , x , p).

      atEntry : Formula S 2 → Formula S 1
      atEntry θ =
        ∃̇ (∃̇ (prAtˢ (suc (suc zero)) (suc zero) zero ∧̇ renameFo ρE θ))

      atEntry-reading : (θ : Formula S 2) (x p : S)
                      → ((entry x p ∷ []) ⊨ᴳ atEntry θ) ≡ ((p ∷ x ∷ []) ⊨ᴳ θ)
      atEntry-reading θ x p =
        ⇔toPath {P = (entry x p ∷ []) ⊨ᴳ atEntry θ} {Q = (p ∷ x ∷ []) ⊨ᴳ θ} to from
        where
          Tgt : Type ℓ
          Tgt = ⟨ (p ∷ x ∷ []) ⊨ᴳ θ ⟩

          inner : (u : S) → Σ[ v ∈ S ]
                    (⟨ (v ∷ u ∷ entry x p ∷ [])
                         ⊨ᴳ prAtˢ (suc (suc zero)) (suc zero) zero ⟩
                     × ⟨ (v ∷ u ∷ entry x p ∷ []) ⊨ᴳ renameFo ρE θ ⟩)
                → Tgt
          inner u (v , hk , hθ) =
            subst (λ w → ⟨ (w ∷ x ∷ []) ⊨ᴳ θ ⟩) (sym (snd shape))
              (subst (λ w → ⟨ (v ∷ w ∷ []) ⊨ᴳ θ ⟩) (sym (fst shape)) atUV)
            where
              shape : (x ≡ u) × (p ≡ v)
              shape = entry-inj
                (kpair-unique (entry x p) u v
                  (subst ⟨_⟩
                    (prAtˢ-reading (suc (suc zero)) (suc zero) zero
                      (v ∷ u ∷ entry x p ∷ [])) hk))

              atUV : ⟨ (v ∷ u ∷ []) ⊨ᴳ θ ⟩
              atUV = subst ⟨_⟩
                (⊨-rename ρE θ (v ∷ u ∷ entry x p ∷ []) (v ∷ u ∷ []) (ρE-ag v u (entry x p)))
                hθ

          to : ⟨ (entry x p ∷ []) ⊨ᴳ atEntry θ ⟩ → Tgt
          to = PT.rec (snd ((p ∷ x ∷ []) ⊨ᴳ θ))
                 (λ { (u , h) → PT.rec (snd ((p ∷ x ∷ []) ⊨ᴳ θ)) (inner u) h })

          from : Tgt → ⟨ (entry x p ∷ []) ⊨ᴳ atEntry θ ⟩
          from h = ∣ x , ∣ p , pairPart , thetaPart ∣₁ ∣₁
            where
              pairPart : ⟨ (p ∷ x ∷ entry x p ∷ [])
                             ⊨ᴳ prAtˢ (suc (suc zero)) (suc zero) zero ⟩
              pairPart = subst ⟨_⟩
                (sym (prAtˢ-reading (suc (suc zero)) (suc zero) zero
                       (p ∷ x ∷ entry x p ∷ [])))
                (entry-isKPair x p)

              thetaPart : ⟨ (p ∷ x ∷ entry x p ∷ []) ⊨ᴳ renameFo ρE θ ⟩
              thetaPart = subst ⟨_⟩
                (sym (⊨-rename ρE θ (p ∷ x ∷ entry x p ∷ []) (p ∷ x ∷ [])
                       (ρE-ag p x (entry x p))))
                h

      ----------------------------------------------------------------------
      -- PROJECTION ONE. Track F, K6/Separation.agda:280-283, verbatim.
      ----------------------------------------------------------------------

      sepΔ : (α : Nm) (φ : Formula Nm 1) → Formula S 1
      sepΔ α φ = atEntry (forcesΔ ((var zero ∈̇ con α) ∧̇ φ))

      sepΔ-reading : (α : Nm) (φ : Formula Nm 1) (χ : Nm) (r : Cond)
                   → ((entry (fst χ) (cnd r) ∷ []) ⊨ᴳ sepΔ α φ)
                   ≡ forces r ((var zero ∈̇ con α) ∧̇ φ) (χ ∷ [])
      sepΔ-reading α φ χ r =
          atEntry-reading (forcesΔ ((var zero ∈̇ con α) ∧̇ φ)) (fst χ) (cnd r)
        ∙ forcesΔ-reading ((var zero ∈̇ con α) ∧̇ φ) (χ ∷ []) r

      ----------------------------------------------------------------------
      -- PROJECTION TWO. Track E, K6/Power.agda:369-373, up to the shape of
      -- Cond; the verbatim form is the module Power below.
      ----------------------------------------------------------------------

      powΔ : Nm → Nm → Formula S 1
      powΔ α χ = atEntry (forcesΔ (var zero ∈̇ con χ))

      powΔ-reading : (α χ y : Nm) (r : Cond)
                   → ((entry (fst y) (cnd r) ∷ []) ⊨ᴳ powΔ α χ)
                   ≡ forces r (var zero ∈̇ con χ) (y ∷ [])
      powΔ-reading α χ y r =
          atEntry-reading (forcesΔ (var zero ∈̇ con χ)) (fst y) (cnd r)
        ∙ forcesΔ-reading (var zero ∈̇ con χ) (y ∷ []) r

      ----------------------------------------------------------------------
      -- PROJECTION THREE. Track H, K6/Replacement.agda:331-336. No entry is
      -- opened here: Collection reads the three slots flat, so the projection
      -- is one permutation of the datum's own layout.
      ----------------------------------------------------------------------

      ρC : Fin 3 → Fin 3
      ρC zero             = suc zero
      ρC (suc zero)       = zero
      ρC (suc (suc zero)) = suc (suc zero)

      ρC-ag : (t q c : S) → Agrees ρC (t ∷ q ∷ c ∷ []) (q ∷ t ∷ c ∷ [])
      ρC-ag t q c zero             = refl
      ρC-ag t q c (suc zero)       = refl
      ρC-ag t q c (suc (suc zero)) = refl

      colΔ : Formula Nm 2 → Formula S 3
      colΔ ψ = renameFo ρC (forcesΔ ψ)

      colΔ-reading : (ψ : Formula Nm 2) (τ χ : Nm) (r : Cond)
                   → ((fst τ ∷ cnd r ∷ fst χ ∷ []) ⊨ᴳ colΔ ψ)
                   ≡ forces r ψ (τ ∷ χ ∷ [])
      colΔ-reading ψ τ χ r =
          ⊨-rename ρC (forcesΔ ψ)
            (fst τ ∷ cnd r ∷ fst χ ∷ []) (cnd r ∷ fst τ ∷ fst χ ∷ [])
            (ρC-ag (fst τ) (cnd r) (fst χ))
        ∙ forcesΔ-reading ψ (τ ∷ χ ∷ []) r

  ------------------------------------------------------------------------------
  -- The two consumer-verbatim wrappers
  ------------------------------------------------------------------------------

    -- Track E states Cond as the Sigma type itself (K6/Power.agda:211-212) and
    -- reads the condition code as `fst r`. Instantiating the datum's abstract
    -- (Cond , cnd) at that pair turns powΔ-reading into Track E's field TYPE
    -- character for character. The definition is the general one; the type
    -- ascription is the check.

    module Power
      (carrierᶠ : S)
      (forces   : ∀ {k} → Σ[ p ∈ S ] ⟨ p ∈ˢ carrierᶠ ⟩
                → Formula Nm k → Vec Nm k → Ω)
      (forcesΔ  : ∀ {k} → Formula Nm k → Formula S (suc k))
      (forcesΔ-reading
                : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
                  (r : Σ[ p ∈ S ] ⟨ p ∈ˢ carrierᶠ ⟩)
                → ((fst r ∷ codesOf ν) ⊨ᴳ forcesΔ φ) ≡ forces r φ ν)
      where

      Cond : Type ℓ
      Cond = Σ[ p ∈ S ] ⟨ p ∈ˢ carrierᶠ ⟩

      private
        module D = Datum Cond fst forces forcesΔ forcesΔ-reading

      powΔ : Nm → Nm → Formula S 1
      powΔ = D.powΔ

      powΔ-reading : (α χ y : Nm) (r : Cond)
                   → ((entry (fst y) (fst r) ∷ []) ⊨ᴳ powΔ α χ)
                   ≡ forces r (var zero ∈̇ con χ) (y ∷ [])
      powΔ-reading = D.powΔ-reading

    -- Track H states the condition as a code together with its membership and
    -- rebuilds the Cond with cndOf (K6/Replacement.agda:249). At the instance
    -- Cond is a plain Sigma, cndOf q hq is (q , hq) and cnd-cndOf is refl,
    -- which K6/Replacement.agda:128-130 records.

    module Replacement
      (Cond            : Type ℓ)
      (cnd             : Cond → S)
      (carrierᶠ        : S)
      (cndOf           : (q : S) → ⟨ q ∈ˢ carrierᶠ ⟩ → Cond)
      (cnd-cndOf       : (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩) → cnd (cndOf q hq) ≡ q)
      (forces          : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
      (forcesΔ         : ∀ {k} → Formula Nm k → Formula S (suc k))
      (forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                       → ((cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ) ≡ forces r φ ν)
      where

      private
        module D = Datum Cond cnd forces forcesΔ forcesΔ-reading

      colΔ : Formula Nm 2 → Formula S 3
      colΔ = D.colΔ

      colΔ-reading : (ψ : Formula Nm 2) (τ : Nm) (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩)
                     (χ : Nm)
                   → ((fst τ ∷ q ∷ fst χ ∷ []) ⊨ᴳ colΔ ψ)
                   ≡ forces (cndOf q hq) ψ (τ ∷ χ ∷ [])
      colΔ-reading ψ τ q hq χ =
          cong (λ w → (fst τ ∷ w ∷ fst χ ∷ []) ⊨ᴳ colΔ ψ) (sym (cnd-cndOf q hq))
        ∙ D.colΔ-reading ψ τ χ (cndOf q hq)
