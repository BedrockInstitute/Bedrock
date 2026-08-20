{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.402] PROBE.  The selected code, read back as an UNTRUNCATED
-- ambient injection.  It runs in agents/tasks/LJ-1-402/ and lands
-- nothing in src/.
--
-- [LJ-1.401]'s `sel-code` is a MODULE HYPOTHESIS, not imported and not
-- rebuilt.  That task returned GO.  The type here is the type its
-- report gives (Probe401.agda:57-63).
--
-- W3, FIRST: `up-lands`, the lift of `sel-code`'s F : Mem (Lset β)
-- to Small's first set argument.  Small wants three arguments at S;
-- only the graph needs the lift.  Stated alone and run before
-- `sel-arrow`, per the brief.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-402.Probe402 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module SiteBound; module InternalLeastCard )
open import L.Coding.Injection {ℓ} lem using ( module Small )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3, FIRST.  The lift at Small's three set arguments.
--
--   Small (F D C : S)  (src/L/Coding/Injection.lagda.md:123).
--   D is κ, already S.  C is δᴸ, already S (it is SiteBound.up of the
--   selected member, src/L/Cardinal.lagda.md:253-254).  F arrives as
--   Mem (Lset β) and is the one argument that needs SiteBound.up.
-- =====================================================================

up-lands : (κ : S) (oκ : IsOrd (fst κ))
         → (nonempty : ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
                          ⟨ InternalLeastCard.Good κ oκ δ ⟩ ∥₁)
         → Mem (Lset (SiteBound.β κ))
         → S × S × S
up-lands κ oκ nonempty F =
    SiteBound.up κ F
  , κ
  , InternalLeastCard.Selected.δᴸ κ oκ nonempty

-- =====================================================================
-- THE HYPOTHESIS AND THE READBACK.
--
--   `sel-code` is [LJ-1.401]'s obligation, taken as a module parameter
--   after L.Cardinal is open, because its type names Selected and
--   InjCode.  This probe does not import Probe401 and does not rebuild
--   the term.  The type is the type [LJ-1.401] reports
--   (Probe401.agda:57-63).
--
--   The four conjuncts of InjCode arrive as one value.  Small wants
--   four arguments.  Destructure, open Small at the three sets
--   `up-lands` already named, project `small` and `small-inj`.
-- =====================================================================

module _
  (sel-code :
       (κ : S) (oκ : IsOrd (fst κ))
     → (nonempty : ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
                      ⟨ InternalLeastCard.Good κ oκ δ ⟩ ∥₁)
     → Σ[ F ∈ Mem (Lset (SiteBound.β κ)) ]
         InjCode (SiteBound.up κ F) κ
                 (InternalLeastCard.Selected.δᴸ κ oκ nonempty))
  where

  sel-arrow :
      (κ : S) (oκ : IsOrd (fst κ))
    → (nonempty : ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
                     ⟨ InternalLeastCard.Good κ oκ δ ⟩ ∥₁)
    → ⟪ fst κ ⟫ ↪ ⟪ fst (InternalLeastCard.Selected.δᴸ κ oκ nonempty) ⟫
  sel-arrow κ oκ nonempty = Sm.small , Sm.small-inj
    where
    Fcode = sel-code κ oκ nonempty
    module Sm = Small (SiteBound.up κ (fst Fcode)) κ
                  (InternalLeastCard.Selected.δᴸ κ oκ nonempty)
                  (fst (snd Fcode))
                  (fst (snd (snd Fcode)))
                  (fst (snd (snd (snd Fcode))))
                  (snd (snd (snd (snd Fcode))))
