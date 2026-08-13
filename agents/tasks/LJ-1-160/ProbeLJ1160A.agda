{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.160 probe A.  THE RE-ROUTE, MEASURED.  NOT an attempt on the wall.
--
-- The archived rud route derived a `levelIn`-shaped fact and an `M ⊆ L`
-- fact at a TRANSITIVE carrier, from one crossing obligation plus two
-- inner-story facts, and it never named the Mostowski collapse:
--   archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:208-257.
--
-- This probe re-states that derivation against the CURRENT route's own
-- two hypotheses, at the collapse IMAGE `πX`, which the current tree
-- delivers as a transitive set (src/V/Collapse.lagda.md:89).
--
-- What it measures:
--   (1) `FOL.Absoluteness.Single` opens at the collapse image in one line,
--       so `abs₀`, `σ₁-up` and `π₁-down` are available there.
--   (2) The current `levelIn` (src/L/BoundedSubset.lagda.md:917) follows
--       from `CrossOut` + `HasLevels`.
--   (3) The current `cover`  (src/L/BoundedSubset.lagda.md:918-919) follows
--       from `CrossOut` + `Covered` + the delivered `πX-intro`.
--
-- The term [LJ-1.51] could not write, `π (Lset m') ≡ Lset (π m')`, does
-- NOT appear.  That is the point of the probe.

open import Base.Prelude
open import Base.Truth

module LJ-1-160.ProbeLJ1160A {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans; module Collapse )
open import L.Constructible {ℓ} using ( Lset; IsOrd )

import FOL.Absoluteness
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- ---------------------------------------------------------------------
-- (1) The absoluteness machine opens at ANY transitive set, hence at πX.
--     `isTrans u = Transitive 𝒮ᵥ (λ x → x ∈ˢ u)` definitionally
--     (src/V/Collapse.lagda.md:25-26), which is `Single`'s third
--     parameter (src/FOL/Absoluteness.lagda.md:57-59).
-- ---------------------------------------------------------------------

module AtImage (P : S) (Ptr : isTrans P) where

  module Abs = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ P) Ptr

  -- the inner world at P, and the two transfers the crossing spends.
  -- Naming them proves they are in scope at the collapse image.
  open Abs using ( SM; abs₀; σ₁-up; π₁-down ) public

-- ---------------------------------------------------------------------
-- (2) and (3): the derivation, stated with the crossing face abstract.
--     `Bel v b` stands for "the inner world of P believes the level
--     formula of v at index b".  Nothing below inspects it.
-- ---------------------------------------------------------------------

module Reroute
  (M : S)                                   -- the hull carrier
  (P : S)                                   -- the collapse image C.πX
  (pi : S → S)                              -- the collapse C.π
  (piIntro : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ pi y ∈ˢ P ⟩)   -- πX-intro, delivered
  (Bel : S → S → Type (ℓ-suc ℓ))            -- the inner belief at P
  -- the archived CrossOut, at P: a believed value at an ordinal index IS
  -- the tower's level there.  archive .../Condensation.lagda.md:168-170.
  (crossOut : (v b : S) → ⟨ v ∈ˢ P ⟩ → ⟨ b ∈ˢ P ⟩ → IsOrd b
            → Bel v b → v ≡ Lset b)
  -- the archived HasLevels, at P.  archive .../Condensation.lagda.md:173-175.
  (hasLevels : (b : S) → ⟨ b ∈ˢ P ⟩ → IsOrd b
             → ∥ Σ[ v ∈ S ] (⟨ v ∈ˢ P ⟩ × Bel v b) ∥₁)
  -- the archived Covered, at P.  archive .../Condensation.lagda.md:177-180.
  (covered : (x : S) → ⟨ x ∈ˢ P ⟩
           → ∥ Σ[ b ∈ S ] Σ[ v ∈ S ]
               (⟨ b ∈ˢ P ⟩ × ⟨ v ∈ˢ P ⟩ × IsOrd b × Bel v b × ⟨ x ∈ˢ v ⟩) ∥₁)
  where

  -- THE CURRENT `levelIn`, verbatim from src/L/BoundedSubset.lagda.md:917.
  levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ P ⟩ → ⟨ Lset δ ∈ˢ P ⟩
  levelIn δ oδ δ∈ = PT.rec (snd (Lset δ ∈ˢ P)) go (hasLevels δ δ∈ oδ)
    where
    go : Σ[ v ∈ S ] (⟨ v ∈ˢ P ⟩ × Bel v δ) → ⟨ Lset δ ∈ˢ P ⟩
    go (v , (v∈ , bel)) =
      subst (λ w → ⟨ w ∈ˢ P ⟩) (crossOut v δ v∈ δ∈ oδ bel) v∈

  -- THE CURRENT `cover`, verbatim from src/L/BoundedSubset.lagda.md:918-919.
  cover : (y : S) → ⟨ y ∈ˢ M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ P ⟩ × ⟨ pi y ∈ˢ Lset γ ⟩) ∥₁
  cover y y∈M = PT.rec squash₁ go (covered (pi y) (piIntro y y∈M))
    where
    go : Σ[ b ∈ S ] Σ[ v ∈ S ]
           (⟨ b ∈ˢ P ⟩ × ⟨ v ∈ˢ P ⟩ × IsOrd b × Bel v b × ⟨ pi y ∈ˢ v ⟩)
       → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ P ⟩ × ⟨ pi y ∈ˢ Lset γ ⟩) ∥₁
    go (b , (v , (b∈ , (v∈ , (ob , (bel , y∈v)))))) =
      ∣ b , (ob , (b∈ ,
        subst (λ w → ⟨ pi y ∈ˢ w ⟩) (crossOut v b v∈ b∈ ob bel) y∈v)) ∣₁

-- ---------------------------------------------------------------------
-- The site match: the hypotheses above are the DELIVERED objects of the
-- current route, not invented ones.  `Collapse M` supplies πX, πX-trans
-- and πX-intro, so `Reroute` applies at the real site.
-- ---------------------------------------------------------------------

module AtSite (M : S) where

  module C = Collapse M

  -- πX is transitive: src/V/Collapse.lagda.md:89.
  imageTrans : isTrans C.πX
  imageTrans = C.πX-trans

  -- the absoluteness machine at the collapse image, in one line.
  module AbsImage = AtImage C.πX imageTrans

  -- Reroute applied at the real site: only the three crossing facts stay
  -- open.  The collapse map and its intro lemma are delivered.
  module Here (Bel : S → S → Type (ℓ-suc ℓ))
    (crossOut : (v b : S) → ⟨ v ∈ˢ C.πX ⟩ → ⟨ b ∈ˢ C.πX ⟩ → IsOrd b
              → Bel v b → v ≡ Lset b)
    (hasLevels : (b : S) → ⟨ b ∈ˢ C.πX ⟩ → IsOrd b
               → ∥ Σ[ v ∈ S ] (⟨ v ∈ˢ C.πX ⟩ × Bel v b) ∥₁)
    (covered : (x : S) → ⟨ x ∈ˢ C.πX ⟩
             → ∥ Σ[ b ∈ S ] Σ[ v ∈ S ]
                 (⟨ b ∈ˢ C.πX ⟩ × ⟨ v ∈ˢ C.πX ⟩ × IsOrd b × Bel v b
                  × ⟨ x ∈ˢ v ⟩) ∥₁)
    = Reroute M C.πX C.π C.πX-intro Bel crossOut hasLevels covered
