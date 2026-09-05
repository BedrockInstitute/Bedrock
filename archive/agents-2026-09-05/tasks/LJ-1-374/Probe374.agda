{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.374 probe.  RECON.  It lands nothing.  It runs in
-- agents/tasks/LJ-1-374/.
--
-- THE BRIEF ASKS AGDA FOR TWO MEASUREMENTS AND NOTHING ELSE.
--
--   1.  Re-derive, in this file's own spelling, that `BandChoice` is
--       an instance of `SetChoice (ℓ-suc ℓ)`
--       (src/Base/Choice.lagda.md:54-56), the claim [LJ-1.373]
--       measured green at Probe373.agda.  The index telescope, the
--       set proof and the wrap below are spelled here from the band's
--       own types; a wrong spelling refuses against `LimitBandT` and
--       `LimitBand` at the two pinning sites.
--
--   2.  Typecheck the TYPE of the GCH trophy if it carried the same
--       interface.  Types only: no inhabitant is built and src/ is
--       not touched.  The statement lives or dies with the owner's
--       ruling, not with this file.
--
-- `SetChoice` stays a hypothesis of every stated item.  Nothing here
-- assumes it, proves it, or supplies it.  DD4: both items are pure
-- wraps over the one generic interface chapter, `Base.Choice`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Base.Choice using ( SetChoice )

module LJ-1-374.Probe374 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isPropIsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )

open import LJ-1-337.ProbeLJ1337A {ℓ} lem using ( Closed; isPropClosed )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand )
open import LJ-1-368.Probe368 {ℓ} lem
  using ( BandChoice; LimitBandT; sq-set )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Foundations.HLevels
  using ( isSetΣ; isSetΠ; isOfHLevelLift )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_; isSetS )

-- =====================================================================
-- PART 1.  THE INSTANCE, RE-DERIVED.
--
--   `LimitBandT`'s domain telescope, spelled as one Σ.  This is the
--   index of the selection.  Every component after δ is a proposition
--   except the induction hypothesis, which is a family of sets.
-- =====================================================================

BandTel : Type (ℓ-suc ℓ)
BandTel = Σ[ δ ∈ S ] Σ[ oδ ∈ IsOrd δ ] Σ[ w ∈ ⟨ ω ∈ˢ δ ⟩ ]
  Σ[ c ∈ Closed δ ] Σ[ n ∈ (Init δ → Empty.⊥) ]
  ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)

tel-set : isSet BandTel
tel-set =
  isSetΣ isSetS
    (λ δ → isSetΣ (isProp→isSet (isPropIsOrd δ))
      (λ _ → isSetΣ (isProp→isSet (snd (ω ∈ˢ δ)))
        (λ _ → isSetΣ (isProp→isSet (isPropClosed δ))
          (λ _ → isSetΣ (isProp→isSet (isPropΠ (λ _ → Empty.isProp⊥)))
            (λ _ → isSetΠ (λ β → isSetΠ (λ _ → isSetΠ (λ _ →
              isSetΠ (λ _ → sq-set β)))))))))

--   The fiber at an index is `sq δ` lifted one universe, which is
--   what `SetChoice (ℓ-suc ℓ)` asks of its family.
fiberAt : BandTel → Type (ℓ-suc ℓ)
fiberAt t = Lift (sq (fst t))

--   PIN ONE.  `LimitBandT`'s own shape must accept this reading; a
--   wrong telescope refuses here.
inhAt : (t : LimitBandT) (i : BandTel) → ∥ fiberAt i ∥₁
inhAt t (δ , oδ , w , c , n , ih) = PT.map lift (t δ oδ w c n ih)

--   PIN TWO.  The section, curried back into `LimitBand`'s shape; a
--   wrong telescope refuses here too.
secAt : ((i : BandTel) → fiberAt i) → LimitBand
secAt s δ oδ w c n ih = lower (s (δ , oδ , w , c , n , ih))

--   The measurement.  The whole distance from the interface to the
--   band is one `isSet` proof, paid above, and the two lifts.
band-is-instance : SetChoice (ℓ-suc ℓ) → BandChoice
band-is-instance sc t =
  PT.map secAt (sc BandTel tel-set fiberAt (inhAt t))

-- =====================================================================
-- PART 2.  THE GCH TROPHY'S TYPE, IF IT TOOK THE SAME INTERFACE.
--
--   Types only.  `GCHStatement` is the delivered statement
--   (src/L/GCH.lagda.md:59-70) and `L⊨ZF` its model argument.
--   FORM A keeps the LEM bill and adds the choice bill beside it.
--   FORM B is `V⊨ZFC`'s own pattern (src/V/Model.lagda.md:528-531):
--   one choice instance pays both bills, because `choice→lem` is
--   proved in `Base.Choice`.  Neither form is inhabited here.
-- =====================================================================

open import Base.Choice using ( choice→lem )
open import L.GCH {ℓ} lem using ( GCHStatement )
import L.Model

--   FORM A: the LEM bill stays, the choice bill is added beside it.
L⊨GCH-form-A : Type (ℓ-suc (ℓ-suc ℓ))
L⊨GCH-form-A =
  SetChoice (ℓ-suc ℓ) → GCHStatement (L.Model.L⊨ZF lem)

--   FORM B: `V⊨ZFC`'s own pattern.  One choice instance pays both
--   bills, since `choice→lem` is proved.  The hypothesis list of the
--   trophy shrinks to one entry, and it is the same entry `V⊨ZFC`
--   takes at the same level.
L⊨GCH-form-B : Type (ℓ-suc (ℓ-suc ℓ))
L⊨GCH-form-B =
  (sc : SetChoice (ℓ-suc ℓ))
    → GCHStatement (L.Model.L⊨ZF (choice→lem sc))
