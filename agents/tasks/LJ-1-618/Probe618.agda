{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.618]  THE PAIRING AT ONE ALPHA, at the grain the tree spends it.
--
-- THE BRIEF'S OBLIGATION, re-stated VERBATIM:
--
--     pairing-at-alpha :
--       (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
--       → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
--           ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)
--
-- that is, ONE binary function on one infinite ordinal with its
-- injectivity, for EVERY infinite ordinal.  `S` here is the ambient
-- carrier `V ℓ` (src/V/Hierarchy.lagda.md:79-84), the grain `sq`
-- itself is stated at (src/L/Ordinal/SquareLaw.lagda.md:685-687) and
-- the band parameter repeats (src/L/BoundedSubset.lagda.md:1388-1391).
--
-- NO TERM OF THIS FILE HAS THAT NAME, and no term of this file has
-- that type as its body: the tree does not inhabit it, and this probe
-- carries every row the tree holds, green, so that each row is a
-- measurement and not a claim.  What the probe MEASURES is the exact
-- shape of the gap: Section 3 proves the obligation FROM one named
-- residue (`Inj-extract`), and Section 4 shows that residue is the
-- untruncation of a non-proposition, the wall [LJ-1.107] and
-- [LJ-1.114] already measured
-- (archive/dev/LJ-dispatch-index.md:183, :190) and [LJ-1.605] priced
-- at the band as the square law itself
-- (agents/tasks/LJ-1-605/review-of-uniform-pairing.md:90).
--
--   Section 0.  The payload type, and its identity with `sq`.
--   Section 1.  THE COVERAGE MAP: every candidate in the tree that
--               reaches one α, marked.
--   Section 2.  The truncated supply the tree DOES deliver at every
--               infinite ordinal of the band.
--   Section 3.  THE RESIDUE: `Inj-extract`, type only, and
--               `pairing-from-extract`, the obligation FROM it.
--   Section 4.  Why the residue is an untruncation and not a dne.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Every run is capped and recorded under
-- runs/ (floor first, per the heavy-object rule: the floor run holes
-- exactly the recursion body).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd )

module LJ-1-618.Probe618 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.SquareLawClosed {ℓ} lem ω ω-ord
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- ===================================================================
-- SECTION 0.  THE PAYLOAD TYPE.
-- ===================================================================

-- The brief's Σ, spelled VERBATIM, at one α.
PairingAt : V ℓ → Type ℓ
PairingAt α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
                ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

-- And it is the tree's own type former, by one delta step
-- (src/L/Ordinal/SquareLaw.lagda.md:685-687).
PairingAt-is-sq : PairingAt ≡ sq
PairingAt-is-sq = refl

-- The obligation, as a type.  Green, and NOT inhabited by any row of
-- this file.
Obligation : Type (ℓ-suc ℓ)
Obligation = (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → PairingAt α

-- ===================================================================
-- SECTION 1.  THE COVERAGE MAP.  Every candidate the search found,
-- re-ascribed at the payload, each marked by what it reaches.
-- ===================================================================

-- 1.1  THE FIBER AT ω.  Reaches ONE infinite ordinal: ω itself is
--      infinite (ω is not a member of ω, by ∈-irrefl on the ordinal
--      ω-ord).  Delivered by the order route at the base
--      (src/L/InjChain.lagda.md:184-185), machine-checked there.
at-ω : PairingAt ω
at-ω = squareω

-- 1.2  THE FIBER AT EVERY INITIAL ORDINAL, one at a time, with NO
--      band and NO uniformity: `Init` is carried by the argument
--      (src/L/Ordinal/SquareLaw.lagda.md:692-698).  Reaches every
--      infinite ordinal that has ω as a STRICT member, is
--      successor-closed, and injects into no infinite member's
--      square.  Does NOT reach ω (Init needs ⟨ ω ∈ˢ ω ⟩) and does NOT
--      reach a non-initial ordinal (clause 4 fails there: at such an
--      ordinal the index DOES inject into some infinite member's
--      square, which is why the ordinal is not initial).
at-init : (α : V ℓ) → Init α → PairingAt α
at-init α iα = via-col-square α iα

-- 1.3  THE BAND PARAMETER, for contrast only.  This is what the
--      consumer's telescope names (src/L/BoundedSubset.lagda.md:
--      1388-1391) and what [LJ-1.605] measured as the square law at
--      the band.  It is NOT one α: it is a uniform supply over every
--      δ of sucV α.  This row is a TYPE, not a term.
Band : V ℓ → Type (ℓ-suc ℓ)
Band α = (δ : V ℓ) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → PairingAt δ

-- ===================================================================
-- SECTION 2.  WHAT THE TREE DELIVERS AT EVERY INFINITE ORDINAL TODAY:
-- the TRUNCATED fiber, over the band, by the closed recursion
-- (src/L/SquareLawClosed.lagda.md:325-328).
-- ===================================================================

trunc-at-band : (δ : V ℓ) → ⟨ δ ∈ˢ sucV ω ⟩
              → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ PairingAt δ ∥₁
trunc-at-band = sq-trunc-closed

-- The truncated recursion's own least-cardinal injection, re-ascribed
-- (src/L/Cardinal.lagda.md:133-134).  This is the honest fact the
-- recursion holds at every descent site, and its payload is a
-- truncated existence.
κ-inj-at : (a : S) (oa : IsOrd (fst a))
         → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
κ-inj-at = κ-injL

-- ===================================================================
-- SECTION 3.  THE RESIDUE, and the obligation FROM it.
-- ===================================================================

-- 3.1  THE RESIDUE, TYPE ONLY.  The untruncation of the least-cardinal
--      injection at every L-element ordinal.  NOT INHABITED by any row
--      of this file.  Its premise is exactly `κ-inj-at`'s conclusion,
--      so the residue adds nothing but the extraction itself.
Inj-extract : Type (ℓ-suc ℓ)
Inj-extract = (a : S) (oa : IsOrd (fst a))
            → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
            → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

-- 3.2  THE OBLIGATION FROM THE RESIDUE.  The recursion of
--      src/L/SquareLawClosed.lagda.md:280-323 with the motive
--      UNTRUNCATED: the ω case spends the honest base (1.1), the
--      own-least-cardinal case spends `via-col-square` at an `Init`
--      the truncated induction hypothesis still serves (clause 4
--      concludes ⊥, so truncation is harmless there), and the descent
--      case spends the residue at exactly one place: the `down`
--      argument of `descent-core`
--      (src/L/SquareLawClosed.lagda.md:241-246).  Every other row is
--      the tree's own, reused.
Goal′ : V ℓ → Type (ℓ-suc ℓ)
Goal′ x = IsOrd x → (⟨ x ∈ˢ ω ⟩ → Empty.⊥) → PairingAt x

step′ : Inj-extract
      → (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal′ y) → Goal′ x
step′ ext x ih ox infx = go (ord-tri x ox ω ω-ord)
  where
  a : S
  a = x , isL-ord x ox

  go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → PairingAt x
  go (inl x∈ω) = Empty.rec (infx x∈ω)
  go (inr (inl x≡ω)) = subst PairingAt (sym x≡ω) squareω
  go (inr (inr ω∈x)) = splitOwn (kappa-decides a ox)
    where
    κ : S
    κ = κL a ox

    oκ : IsOrd (fst κ)
    oκ = κoL a ox

    ω∈κ : fst κ ≡ x → ⟨ ω ∈ fst κ ⟩
    ω∈κ κ≡x = subst (λ w → ⟨ ω ∈ w ⟩) (sym κ≡x) ω∈x

    members : fst κ ≡ x
            → (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst κ ⟩
            → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁
    members κ≡x β oβ β∈κ infβ =
      ∣ ih β (subst (λ w → ⟨ β ∈ w ⟩) κ≡x β∈κ) oβ infβ ∣₁

    by-init : fst κ ≡ x → PairingAt x
    by-init κ≡x = subst PairingAt κ≡x
      (via-col-square (fst κ) (init-at-kappa a ox (ω∈κ κ≡x) (members κ≡x)))

    by-descent : ⟨ fst κ ∈ x ⟩ → PairingAt x
    by-descent κ∈x = descent-core a κ (mem-incl x (fst κ) ox κ∈x)
      (ih (fst κ) κ∈x oκ (kappa-not-fin x ox ω∈x))
      (ext a ox (κ-injL a ox))

    splitOwn : (fst κ ≡ x) ⊎ ⟨ fst κ ∈ x ⟩ → PairingAt x
    splitOwn (inl κ≡x) = by-init κ≡x
    splitOwn (inr κ∈x) = by-descent κ∈x

-- THE ROW THIS TASK IS FOR.  The obligation, from the residue.
pairing-from-extract : Inj-extract → Obligation
pairing-from-extract ext = ∈-induction {P = Goal′} (step′ ext)

-- ===================================================================
-- SECTION 4.  WHY THE RESIDUE IS AN UNTRUNCATION AND NOT A DNE.
-- ===================================================================

-- 4.1  The truncation is BY CONSTRUCTION, not an accident of the
--      proof: the least-cardinal search feeds `leastOf` an hProp, so
--      the injection existence must be truncated
--      (src/L/Cardinal.lagda.md:63-66: `InjP γ = ∥ Inj γ ∥₁,
--      squash₁`), and the witness it returns is that truncated
--      statement's proof (src/L/Cardinal.lagda.md:133-134).
--
-- 4.2  `dne` cannot extract it.  LEM in this tree gives
--      `dne : (P : hProp) → (¬⟨ P ⟩ → ⊥) → ⟨ P ⟩`
--      (src/L/StageCardinal.lagda.md:423-424), and it applies only to
--      PROPOSITIONS.  The payload `⟪ fst a ⟫ ↪ ⟪ fst κ ⟫` is a Σ
--      whose first component is a FUNCTION (src/L/Cardinal.lagda.md:
--      40-41): two injections into one target can differ, so the
--      payload is not a proposition, and [LJ-1.107] recorded exactly
--      this as the measured reason the non-initial case stayed open
--      (archive/dev/LJ-dispatch-index.md:183).
--
-- 4.3  The residue is per-site choice.  What it asks, at each descent
--      site, is one honest injection picked from a truncated
--      existence.  That is the same grade of object [LJ-1.605] priced
--      at the band: the untruncation IS the square law there
--      (agents/tasks/LJ-1-605/review-of-uniform-pairing.md:90).  At
--      one α the residue is strictly weaker than the band version
--      (it asks at every ordinal, but one at a time, with no
--      uniformity and no coherence), and no row of the tree inhabits
--      it.  See review-of-pairing-at-alpha.md for the ruling.
