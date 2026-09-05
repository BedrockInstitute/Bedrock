{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.740] PROBE.  Sat-at-asConst:  Sat of an asConst-relabelled
-- formula sits in LsetS gamma ogamma, at closedomega gamma.
-- Lands nothing in src/.
--
--   THE ALPHABET IS THE FIX.  LJ-1.736 measured `Sat` over `Formula S n`
--   FALSE at `closedomega gamma`:  a constant may sit above gamma.  Here
--   the alphabet is carrier-bounded, the 736-review corrected target:
--   every constant of `mapFo (asConst A) psi` is `asConst A m`, whose
--   underlying set lies in the carrier, and the carrier sits below gamma
--   by hypothesis.  Route:  merge the carrier's stage with omega under
--   gamma (the 735 close); place the base constants (envSet at every
--   arity by the landed envSetNumeral-in, numerals by numeral-in-limit,
--   asConst by the brief-authorized hypothesis asConst-in-carrier); bound
--   the six unbounded witnesses of `cond`'s own clauses (atom escorts,
--   quantifier extenders) by the stage set and by envSet A (suc n);
--   run the landed AtStage carve on a Delta0 bounded description at a
--   sucIter stage of +omega-blocks; absorb the finite iterate by
--   closedomega.  The climb is carried by `size psi`, one number per
--   formula, and no constructor of `cond` is left unbounded.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by the
-- program and never touched here.
--
-- DISPATCH STATE AT RETURN (honest):  the file does NOT yet typecheck
-- end to end.  Machine-checked green in this dispatch's runs:  the
-- full scaffold (Section 2), the placement core `place` (Section 3,
-- the AtStage carve + identification), the kit and the dIs conversion
-- (Section 1/4a).  Written but NOT yet green:  Section 4c's quantifier
-- adequacies, `bddBd`, and Section 5's climb `R` with the merge and
-- `Sat-at-asConst` (Section 6 is not yet written).  The remaining
-- defects are localized in the R-clause glue (the <=-chains) and the
-- unwritten merge;  every ingredient is named in the report.  The
-- dispatch was terminated by repeated system-side kills (the
-- agda-watchdog's swap guard, _build/tools/agda-watchdog.log) and by
-- the runner artifact before the last rounds could land.
-- LAST GREEN RUN: p-34 (Sections 0-3 + kit) and p-45-era (through the
-- first adequacy clauses);  see runs/p-*.out.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-740.Probe740 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_
        ; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Bounding using ( BoundedFo; BoundedTm )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import L.Absoluteness {ℓ} using ( InL; liftFo; Δ₀-liftFo )
import FOL.Absoluteness
open import Cubical.Data.Nat
  using ( ℕ; _+_ ) renaming ( zero to nzero; suc to nsuc )
open import Cubical.Data.FinData using ( Fin; toℕ; zero; suc )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; extensionality; _⊆_; _∈ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⋃_; _∪_; union-ax; pairing-ax; ⁅_,_⁆; ⁅_⁆s
        ; module InfinitySet )
open InfinitySet using ( #_; ω; sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro
        ; Lset-mono; Lset-in; Lset-out
        ; Lset-layer; layer-trans; Lset→isL )
open import L.Ordinal {ℓ} using ( ω-ord; mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; sucIter-ord; +ω; +ω-mem; +ω-iter; +ω-sup; +ω-ord
        ; closedω )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( env; cons; Δ₀-consAt )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; consAtL-adequate; numL )
open import L.Coding.EnvSet {ℓ} lem
  using ( Ix; envS; envSet; envSet-in; envSet-out; envSet-mem )
open import L.Coding.Sat {ℓ} lem
  using ( Sat; cond; Sat-mem; tmIs; tmIs-var-in; tmIs-var-out
        ; cond∈-in; cond∈-out; cond≐-in; cond≐-out
        ; cond∃-in; cond∃-out; cond∀-in; cond∀-out
        ; cond∃∈-in; cond∃∈-out; cond∀∈-in; cond∀∈-out )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )
open import L.Coding.Bound {ℓ} lem using ( Lset-trans′ )
open import L.Coding.Bridge {ℓ} lem
  using ( asConst; graph; graph-envSet; consAtL-out )

open import Cubical.Data.Unit using ( Unit )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

-- =====================================================================
-- SECTION 0.  THE BRIEF'S HYPOTHESIS.
--
-- `asConst-in-carrier` is taken as a hypothesis exactly as the brief
-- authorizes (supply 0):  relabelling a carrier member keeps its
-- underlying set inside the carrier.
-- =====================================================================

AsConstInCarrier : Type (ℓ-suc ℓ)
AsConstInCarrier = (A : S) (m : ⟪ fst A ⟫) → ⟨ fst (asConst A m) ∈ˢᵥ fst A ⟩

-- =====================================================================
-- SECTION 1.  ARITHMETIC AND DELTA0 HELPERS.
-- =====================================================================

-- The arithmetic facts the climb needs (`_+_` recurses on its
-- first argument, so none of these equations is definitional).
plus-zero : (d : ℕ) → d + nzero ≡ d
plus-zero nzero = refl
plus-zero (nsuc d) = cong nsuc (plus-zero d)

plus-suc : (d s : ℕ) → d + nsuc s ≡ nsuc (d + s)
plus-suc nzero s = refl
plus-suc (nsuc d) s = cong nsuc (plus-suc d s)

plus-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
plus-assoc nzero b c = refl
plus-assoc (nsuc a) b c = cong nsuc (plus-assoc a b c)

-- A bare order on naturals, with the facts the climb needs.
infix 4 _≤ⁿ_
data _≤ⁿ_ : ℕ → ℕ → Type ℓ-zero where
  ≤r  : {n : ℕ} → n ≤ⁿ n
  ≤s  : {m n : ℕ} → m ≤ⁿ n → m ≤ⁿ nsuc n

≤ⁿ-trans : {a b c : ℕ} → a ≤ⁿ b → b ≤ⁿ c → a ≤ⁿ c
≤ⁿ-trans p ≤r = p
≤ⁿ-trans p (≤s q) = ≤s (≤ⁿ-trans p q)

m≤ⁿ+ : (m s : ℕ) → m ≤ⁿ m + s
m≤ⁿ+ m nzero = subst (λ w → m ≤ⁿ w) (sym (plus-zero m)) ≤r
m≤ⁿ+ m (nsuc s) =
  subst (λ w → m ≤ⁿ w) (sym (plus-suc m s)) (≤s (m≤ⁿ+ m s))

≤ⁿ-zend : (n : ℕ) → nzero ≤ⁿ n
≤ⁿ-zend nzero = ≤r
≤ⁿ-zend (nsuc n) = ≤s (≤ⁿ-zend n)

-- The climb's sub-stage fact:  the parent's sub-clause stage is at or
-- below the parent's own.
-- The parent's sub-clause stage is at or below the parent's own
-- (the child sizes are all at least one, supplied as the hypothesis).
sub≤bin : (d sa : ℕ) → ∀ sb → nsuc nzero ≤ⁿ sb
        → nsuc (d + sa) ≤ⁿ d + (sa + sb)
sub≤bin d sa nzero ()
sub≤bin d sa (nsuc sb′) (≤s p′) =
  subst (λ w → nsuc (d + sa) ≤ⁿ w)
    (sym (cong (λ w → d + w) (plus-suc sa sb′) ∙ plus-suc d (sa + sb′)))
    (≤s (sub≤bin d sa sb′ p′))
sub≤bin d sa (nsuc sb) ≤r =
  subst (λ w → nsuc (d + sa) ≤ⁿ w)
    (sym (cong (d +_) (plus-suc sa nzero)
      ∙ (plus-suc d (sa + nzero)
      ∙ (cong nsuc (cong (d +_) (plus-zero sa))))))
    ≤r

-- The Delta0 certificates for the lifted atoms, by the generic lift of
-- the landed certificates for the unlifted forms.  The bounded-fo
-- argument is solved by conversion, exactly as
-- src/L/Condensation.lagda.md does it.
Δ₀-prAtL : ∀ {n} (q u v : Fin n) → Δ₀ (prAtL q u v)
Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

Δ₀-appAt : ∀ {n} (f x y : Fin n) → Δ₀ (appAt f x y)
Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

Δ₀-consAtL : ∀ {n} (e′ m e : Fin n) → Δ₀ (consAtL e′ m e)
Δ₀-consAtL e′ m e = Δ₀-liftFo _ (Δ₀-consAt e′ m e)

-- The numeral constant, exactly Sat's own `nn` shape:  the tag proof
-- from the numeral chapter.  Its underlying set is the tag.
numS : ℕ → S
numS k = # k , numL k

-- =====================================================================
-- SECTION 2.  THE STAGE SCAFFOLD.
--
-- `WithStage` carries the five facts the 735 close hands back:  one
-- stage m in gamma with omega, the carrier's placement above
-- +omega m, and the carrier's one-up stage inside it.  Above m,
-- sigma0 = +omega (+omega m) holds the base constants uniformly in the
-- formula:  envSet at every arity (envSetNumeral-in lands at a uniform
-- sucIter 4), numerals (numeral-in-limit lifted twice), the carrier,
-- and every asConst value (by the hypothesis, through transitivity).
-- =====================================================================

module WithStage
  (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) (ω∈γ : ⟨ ω ∈ˢᵥ γ ⟩)
  (A : S) (hyc : AsConstInCarrier)
  (m : V ℓ) (om : IsOrd m) (m∈γ : ⟨ m ∈ˢᵥ γ ⟩)
  (ω∈+ωm : ⟨ ω ∈ˢᵥ +ω m ⟩) (A∈+ωm : ⟨ fst A ∈ Lset (+ω m) ⟩)
  where

  σ₀ : V ℓ
  σ₀ = +ω (+ω m)

  oσ₀ : IsOrd σ₀
  oσ₀ = +ω-ord (+ω m) (+ω-ord m om)

  σ₀∈γ : ⟨ σ₀ ∈ˢᵥ γ ⟩
  σ₀∈γ = clγ (+ω m) (clγ m m∈γ)

  +ωσ₀∈γ : ⟨ +ω σ₀ ∈ˢᵥ γ ⟩
  +ωσ₀∈γ = clγ σ₀ σ₀∈γ

  -- The stage set as a model element:  the uniform witness bound.
  Om : S
  Om = LsetS σ₀ oσ₀

  module Dσ = DefOf (Lset σ₀)

  Om∈sucσ₀ : ⟨ Om ∈ˢ LsetS (sucV σ₀) (suc-ord oσ₀) ⟩
  Om∈sucσ₀ =
    subst (λ w → ⟨ Lset σ₀ ∈ˢᵥ w ⟩) (sym (Lset-suc σ₀))
      (𝒟ₒ-intro (Lset σ₀) (Lset σ₀)
        ∣ ⊤̇ , Dσ.defSet⊤≡A ∣₁)

  BelowAt : V ℓ → S → Type (ℓ-suc ℓ)
  BelowAt β c = ⟨ fst c ∈ Lset β ⟩

  -- The room:  the base constants, placed at an arbitrary stage, with
  -- that stage's own order.
  Room : (β : V ℓ) → IsOrd β → Type (ℓ-suc ℓ)
  Room β oβ =
      ⟨ A ∈ˢ LsetS β oβ ⟩
    × ((k : ℕ) → ⟨ envSet A k ∈ˢ LsetS β oβ ⟩)
    × ((k : ℕ) → ⟨ numS k ∈ˢ LsetS β oβ ⟩)
    × ((m′ : ⟪ fst A ⟫) → ⟨ asConst A m′ ∈ˢ LsetS β oβ ⟩)

  roomσ₀ : Room σ₀ oσ₀
  roomσ₀ =
    ( rA
    , (λ k → Lset-mono {α = σ₀} {β = sucIter 4 (+ω m)}
              (+ω-iter 4 (+ω m))
              (envSetNumeral∈ (+ω m) (+ω-ord m om) ω∈+ωm A k A∈+ωm))
    , (λ k → Lset-mono {α = σ₀} {β = +ω m} (+ω-mem (+ω m))
              (Lset-mono {α = +ω m} {β = ω} ω∈+ωm (numeral∈limit k)))
    , (λ m′ → Lset-trans′ σ₀ {x = fst A} {y = fst (asConst A m′)}
              (hyc A m′) rA)
    )
    where
    rA : ⟨ A ∈ˢ LsetS σ₀ oσ₀ ⟩
    rA = Lset-mono {α = σ₀} {β = +ω m} (+ω-mem (+ω m)) A∈+ωm

  -- One successor step, and the two monotone lifts the climb needs.
  Room-suc : (β : V ℓ) (oβ : IsOrd β) → Room β oβ
           → Room (sucV β) (suc-ord oβ)
  Room-suc β oβ (rA , rE , rN , rC) =
    ( Lset-mono {α = sucV β} {β = β} (self∈sucV β) rA
    , (λ k → Lset-mono {α = sucV β} {β = β} (self∈sucV β) (rE k))
    , (λ k → Lset-mono {α = sucV β} {β = β} (self∈sucV β) (rN k))
    , (λ m′ → Lset-mono {α = sucV β} {β = β} (self∈sucV β) (rC m′)) )

  Room-lift : (d s : ℕ)
            → Room (sucIter d σ₀) (sucIter-ord d oσ₀)
            → Room (sucIter (d + s) σ₀) (sucIter-ord (d + s) oσ₀)
  Room-lift d nzero r =
    subst (λ w → Room (sucIter w σ₀) (sucIter-ord w oσ₀))
      (sym (plus-zero d)) r
  Room-lift d (nsuc s) r =
    subst (λ w → Room (sucIter w σ₀) (sucIter-ord w oσ₀))
      (sym (plus-suc d s))
      (Room-suc (sucIter (d + s) σ₀) (sucIter-ord (d + s) oσ₀)
        (Room-lift d s r))

  Lset-lift : (x : S) (d s : ℕ)
            → ⟨ x ∈ˢ LsetS (sucIter d σ₀) (sucIter-ord d oσ₀) ⟩
            → ⟨ x ∈ˢ LsetS (sucIter (d + s) σ₀) (sucIter-ord (d + s) oσ₀) ⟩
  Lset-lift x d nzero x∈ =
    subst (λ w → ⟨ x ∈ˢ LsetS (sucIter w σ₀) (sucIter-ord w oσ₀) ⟩)
      (sym (plus-zero d)) x∈
  Lset-lift x d (nsuc s) x∈ =
    subst (λ w → ⟨ x ∈ˢ LsetS (sucIter w σ₀) (sucIter-ord w oσ₀) ⟩)
      (sym (plus-suc d s))
      (Lset-mono {α = sucIter (nsuc (d + s)) σ₀}
                 {β = sucIter (d + s) σ₀}
        (self∈sucV (sucIter (d + s) σ₀)) (Lset-lift x d s x∈))

  -- A stage at or above another:  the ≤-form the climb uses.
  Lset-lift≤ : (x : S) (j k : ℕ) → j ≤ⁿ k
             → ⟨ x ∈ˢ LsetS (sucIter j σ₀) (sucIter-ord j oσ₀) ⟩
             → ⟨ x ∈ˢ LsetS (sucIter k σ₀) (sucIter-ord k oσ₀) ⟩
  Lset-lift≤ x j .j ≤r x∈ = x∈
  Lset-lift≤ x j .(nsuc _) (≤s p) x∈ =
    Lset-mono {α = sucIter (nsuc _) σ₀} {β = sucIter _ σ₀}
      (self∈sucV (sucIter _ σ₀)) (Lset-lift≤ x j _ p x∈)

  LsetV-lift≤ : (x : V ℓ) (j k : ℕ) → j ≤ⁿ k
             → ⟨ x ∈ˢᵥ Lset (sucIter j σ₀) ⟩
             → ⟨ x ∈ˢᵥ Lset (sucIter k σ₀) ⟩
  LsetV-lift≤ x j .j ≤r x∈ = x∈
  LsetV-lift≤ x j .(nsuc _) (≤s p) x∈ =
    Lset-mono {α = sucIter (nsuc _) σ₀} {β = sucIter _ σ₀}
      (self∈sucV (sucIter _ σ₀)) (LsetV-lift≤ x j _ p x∈)

  Room-lift≤ : (j k : ℕ) → j ≤ⁿ k
             → Room (sucIter j σ₀) (sucIter-ord j oσ₀)
             → Room (sucIter k σ₀) (sucIter-ord k oσ₀)
  Room-lift≤ j k j≤k (rA , rE , rN , rC) =
    ( Lset-lift≤ A j k j≤k rA
    , (λ n → Lset-lift≤ (envSet A n) j k j≤k (rE n))
    , (λ n → Lset-lift≤ (numS n) j k j≤k (rN n))
    , (λ m′ → Lset-lift≤ (asConst A m′) j k j≤k (rC m′)) )

  -- Every member of a placed set sits in the stage (transitivity), at
  -- the V level, with the constructibility witness carried along.
  mem-trans : (β : V ℓ) (oβ : IsOrd β) (x : S) (y : S) (yL : ⟨ isL (fst y) ⟩)
            → ⟨ x ∈ˢ LsetS β oβ ⟩ → ⟨ fst y ∈ˢᵥ fst x ⟩
            → ⟨ (fst y , yL) ∈ˢ LsetS β oβ ⟩
  mem-trans β oβ x y yL hx hy =
    Lset-trans′ β {x = fst x} {y = fst y} hy hx

  -- The pair decomposition:  a Kuratowski pair in the stage hands its
  -- second projection down.
  snd∈L : (a b : V ℓ) → ⟨ pr a b ∈ˢᵥ Lset σ₀ ⟩ → ⟨ b ∈ˢᵥ Lset σ₀ ⟩
  snd∈L a b h =
    Lset-trans′ σ₀ {x = ⁅ a , b ⁆} {y = b} b∈⁅a,b⁆
      (Lset-trans′ σ₀ {x = pr a b} {y = ⁅ a , b ⁆} ⁅a,b⁆∈pr h)
    where
    b∈⁅a,b⁆ : ⟨ b ∈ˢᵥ ⁅ a , b ⁆ ⟩
    b∈⁅a,b⁆ =
      ∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .snd
        (pairing-ax a b b .snd ∣ inr refl ∣₁)
    ⁅a,b⁆∈pr : ⟨ ⁅ a , b ⁆ ∈ˢᵥ pr a b ⟩
    ⁅a,b⁆∈pr =
      ∈∈ₛ {a = ⁅ a , b ⁆} {b = pr a b} .snd
        (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ .snd ∣ inr refl ∣₁)

  -- ===================================================================
  -- SECTION 3.  THE PLACEMENT CORE.
  --
  -- One carve, run once for any formula whose bounded description is
  -- given:  `Sat A chi` is identified with the AtStage carve of the
  -- conjunction (the envSet bound, the lifted description), and the
  -- carve sits in `𝒟ₒ (Lset beta)` by the landed `carve∈𝒟ₒ`, hence in
  -- `Lset (sucV beta)`.  The description `Bd` carries the bounded
  -- witnesses;  its adequacy against `cond A chi` is a hypothesis,
  -- discharged per formula constructor by Section 4.
  -- ===================================================================

  module SatPlace (β : V ℓ) (oβ : IsOrd β) where
    module ASβ = AtStage β oβ

    place : (n : ℕ) (χ : Formula S n)
      (Bd : Formula S 1) (bddB : BoundedFo ASβ.Below Bd) (dφ : Δ₀ Bd)
      (hE : ⟨ envSet A n ∈ˢ LsetS β oβ ⟩)
      (adeq-fwd : (z : S) (zL : ⟨ isL (fst z) ⟩) → ⟨ z ∈ˢ envSet A n ⟩
                  → ⟨ (z ∷ []) ⊨ Bd ⟩ → ⟨ (z ∷ []) ⊨ cond A χ ⟩)
      (adeq-bwd : (z : S) (zL : ⟨ isL (fst z) ⟩) → ⟨ z ∈ˢ envSet A n ⟩
                  → ⟨ (z ∷ []) ⊨ cond A χ ⟩ → ⟨ (z ∷ []) ⊨ Bd ⟩)
      → ⟨ Sat A χ ∈ˢ LsetS (sucV β) (suc-ord oβ) ⟩
    place n χ Bd bddB dφ hE adeq-fwd adeq-bwd = result
      where
      hE′ : ⟨ fst (envSet A n) ∈ˢᵥ Lset β ⟩
      hE′ = hE

      mₑ : ⟪ Lset β ⟫
      mₑ = ∈-asFiber {a = fst (envSet A n)} {b = Lset β} hE′ .fst
      mₑ-eq : ⟪ Lset β ⟫↪ mₑ ≡ fst (envSet A n)
      mₑ-eq = ∈-asFiber {a = fst (envSet A n)} {b = Lset β} hE′ .snd

      ψc : Formula ⟪ Lset β ⟫ 1
      ψc = (var zero ∈̇ con mₑ) ∧̇ ASβ.RL.liftFo Bd bddB

      carved∈ : ⟨ ASβ.carve ψc ∈ˢᵥ Lset (sucV β) ⟩
      carved∈ =
        subst (λ w → ⟨ ASβ.carve ψc ∈ˢᵥ w ⟩) (sym (Lset-suc β))
          (ASβ.carve∈𝒟ₒ ψc)

      out : (w : V ℓ) → ⟨ w ∈ˢᵥ fst (Sat A χ) ⟩ → ⟨ w ∈ˢᵥ ASβ.carve ψc ⟩
      out w h = subst (λ z → ⟨ z ∈ˢᵥ ASβ.carve ψc ⟩) fib-eq memF
        where
        wL : ⟨ isL w ⟩
        wL = isL-trans {x = fst (Sat A χ)} {y = w} h (snd (Sat A χ))
        ws : S
        ws = (w , wL)
        split : ⟨ ws ∈ˢ envSet A n ⟩ × ⟨ (ws ∷ []) ⊨ cond A χ ⟩
        split = subst ⟨_⟩ (Sat-mem A χ ws) h
        w∈env : ⟨ w ∈ˢᵥ fst (envSet A n) ⟩
        w∈env = split .fst
        hcond : ⟨ (ws ∷ []) ⊨ cond A χ ⟩
        hcond = split .snd
        w∈L : ⟨ w ∈ˢᵥ Lset β ⟩
        w∈L = Lset-trans′ β {x = fst (envSet A n)} {y = w} w∈env hE′
        fib : ⟪ Lset β ⟫
        fib = ∈-asFiber {a = w} {b = Lset β} w∈L .fst
        fib-eq : ⟪ Lset β ⟫↪ fib ≡ w
        fib-eq = ∈-asFiber {a = w} {b = Lset β} w∈L .snd
        xLfib : ⟨ isL (⟪ Lset β ⟫↪ fib) ⟩
        xLfib = subst (λ z → ⟨ isL z ⟩) (sym fib-eq) wL
        fm : ⟨ ⟪ Lset β ⟫↪ fib ∈ˢᵥ ⟪ Lset β ⟫↪ mₑ ⟩
        fm =
          subst (λ z → ⟨ ⟪ Lset β ⟫↪ fib ∈ˢᵥ z ⟩) (sym mₑ-eq)
            (subst (λ z → ⟨ z ∈ˢᵥ fst (envSet A n) ⟩) (sym fib-eq) w∈env)
        hBd : ⟨ ((⟪ Lset β ⟫↪ fib , xLfib) ∷ []) ⊨ Bd ⟩
        hBd =
          ASβ.⊨-transport Bd dφ ws (⟪ Lset β ⟫↪ fib , xLfib) (sym fib-eq)
            (adeq-bwd ws wL w∈env hcond)
        memF : ⟨ ⟪ Lset β ⟫↪ fib ∈ˢᵥ ASβ.carve ψc ⟩
        memF = ASβ.carveIn mₑ Bd bddB dφ fib xLfib (fm , hBd)

      inw : (w : V ℓ) → ⟨ w ∈ˢᵥ ASβ.carve ψc ⟩ → ⟨ w ∈ˢᵥ fst (Sat A χ) ⟩
      inw w h = subst ⟨_⟩ (sym (Sat-mem A χ ws)) (w∈envS , hcond)
        where
        w∈L : ⟨ w ∈ˢᵥ Lset β ⟩
        w∈L = ASβ.carve⊆ ψc w h
        xLw : ⟨ isL w ⟩
        xLw = Lset→isL β oβ w w∈L
        ws : S
        ws = (w , xLw)
        fib : ⟪ Lset β ⟫
        fib = ∈-asFiber {a = w} {b = Lset β} w∈L .fst
        fib-eq : ⟪ Lset β ⟫↪ fib ≡ w
        fib-eq = ∈-asFiber {a = w} {b = Lset β} w∈L .snd
        xLfib : ⟨ isL (⟪ Lset β ⟫↪ fib) ⟩
        xLfib = subst (λ z → ⟨ isL z ⟩) (sym fib-eq) xLw
        memF : ⟨ ⟪ Lset β ⟫↪ fib ∈ˢᵥ ASβ.carve ψc ⟩
        memF = subst (λ z → ⟨ z ∈ˢᵥ ASβ.carve ψc ⟩) (sym fib-eq) h
        carOut : ⟨ ⟪ Lset β ⟫↪ fib ∈ˢᵥ ⟪ Lset β ⟫↪ mₑ ⟩
               × ⟨ ((⟪ Lset β ⟫↪ fib , xLfib) ∷ []) ⊨ Bd ⟩
        carOut = ASβ.carveOut mₑ Bd bddB dφ fib xLfib memF
        w∈env : ⟨ w ∈ˢᵥ fst (envSet A n) ⟩
        w∈env =
          subst (λ z → ⟨ z ∈ˢᵥ fst (envSet A n) ⟩) fib-eq
            (subst (λ z → ⟨ ⟪ Lset β ⟫↪ fib ∈ˢᵥ z ⟩) mₑ-eq (carOut .fst))
        hBd : ⟨ ((⟪ Lset β ⟫↪ fib , xLfib) ∷ []) ⊨ Bd ⟩
        hBd = carOut .snd
        hcond : ⟨ (ws ∷ []) ⊨ cond A χ ⟩
        hcond =
          adeq-fwd ws xLw w∈env
            (ASβ.⊨-transport Bd dφ (⟪ Lset β ⟫↪ fib , xLfib) ws fib-eq hBd)
        w∈envS : ⟨ ws ∈ˢ envSet A n ⟩
        w∈envS = w∈env

      result : ⟨ Sat A χ ∈ˢ LsetS (sucV β) (suc-ord oβ) ⟩
      result =
        subst (λ z → ⟨ z ∈ˢᵥ Lset (sucV β) ⟩)
          (sym (extensionalV (λ w → ⇔toPath (out w) (inw w))))
          carved∈



  -- ===================================================================
  -- SECTION 4.  THE BOUNDED DESCRIPTION, AND ITS ADEQUACY.
  --
  -- `dIs` is tmIs with the numeral witness bounded by the stage set;
  -- `Bd` is `cond` with every unbounded witness bounded (atom escorts
  -- by the stage set, quantifier extenders by envSet A (suc n)) and
  -- the propositional clauses left as `cond` itself.  The adequacy is
  -- per constructor, both directions, from Sat's own readers plus the
  -- witness boundedness at sigma0.
  -- ===================================================================

  -- The sigma0-level room components, fixed once.
  rE₀ : (k : ℕ) → ⟨ envSet A k ∈ˢ LsetS σ₀ oσ₀ ⟩
  rE₀ k = roomσ₀ .snd .fst k
  rN₀ : (k : ℕ) → ⟨ numS k ∈ˢ LsetS σ₀ oσ₀ ⟩
  rN₀ k = roomσ₀ .snd .snd .fst k
  rC₀ : (m′ : ⟪ fst A ⟫) → ⟨ asConst A m′ ∈ˢ LsetS σ₀ oσ₀ ⟩
  rC₀ m′ = roomσ₀ .snd .snd .snd m′
  rA₀ : ⟨ A ∈ˢ LsetS σ₀ oσ₀ ⟩
  rA₀ = roomσ₀ .fst

  -- A tagged member of z's value:  its tag-pair is in the stage, so
  -- the member itself is.
  slot-bounded : (k : ℕ) (z : S) (zL : ⟨ isL (fst z) ⟩)
    → ⟨ z ∈ˢ envSet A k ⟩
    → (j : ℕ) (b : V ℓ) → ⟨ pr (# j) b ∈ fst z ⟩
    → ⟨ b ∈ˢᵥ Lset σ₀ ⟩
  slot-bounded k z zL hE₀ j b pr∈ =
    snd∈L (# j) b pr-placed
    where
    prL : ⟨ isL (pr (# j) b) ⟩
    prL = isL-trans {x = fst z} {y = pr (# j) b} pr∈ zL
    pr-placed : ⟨ (pr (# j) b , prL) ∈ˢ LsetS σ₀ oσ₀ ⟩
    pr-placed = mem-trans σ₀ oσ₀ z (pr (# j) b , prL) prL
                  (mem-trans σ₀ oσ₀ (envSet A k) z zL (rE₀ k) hE₀) pr∈

  -- An asConst-constant's underlying value is in the stage.
  asConst-bounded : (m′ : ⟪ fst A ⟫) (v : V ℓ)
    → v ≡ fst (asConst A m′)
    → ⟨ v ∈ˢᵥ Lset σ₀ ⟩
  asConst-bounded m′ v e =
    subst (λ q → ⟨ q ∈ˢᵥ Lset σ₀ ⟩) (sym e) (rC₀ m′)

  -- dIs:  tmIs with the numeral witness bounded by the stage set.
  dIs : ∀ {n m} → Term S n → Fin m → Fin m → Formula S m
  dIs (var i) v e =
    ∃̇∈ (con Om) ((var zero ≐ con (numS (toℕ i))) ∧̇ appAt (suc e) zero (suc v))
  dIs (con c) v e = var v ≐ con c

  dIsΔ₀ : ∀ {n m} (t : Term S n) (v e : Fin m) → Δ₀ (dIs t v e)
  dIsΔ₀ (var i) v e = δ-∃∈ (δ-∧ δ-≐ (Δ₀-appAt (suc e) zero (suc v)))
  dIsΔ₀ (con c) v e = δ-≐

  -- dIs satisfaction, both directions, for var-terms:  the bounded
  -- numeral witness supplied from (or delivered to) the stage set.
  -- For con-terms dIs IS tmIs (both are `var v ≐ con c`), so the
  -- adequacy there is literal.
  dIs-var-in : ∀ {n m} (i : Fin n) (v e : Fin m) (γ : S ^ m)
    → ⟨ pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩
    → ⟨ γ ⊨ dIs (var i) v e ⟩
  dIs-var-in i v e γ h =
    ∣ numS (toℕ i)
    , ( rN₀ (toℕ i)
    , ( refl
      , subst ⟨_⟩
            (sym (appAt-adequate (suc e) zero (suc v) (numS (toℕ i) ∷ γ)))
            h ) )
    ∣₁

  dIs-var-out : ∀ {n m} (i : Fin n) (v e : Fin m) (γ : S ^ m)
    → ⟨ γ ⊨ dIs (var i) v e ⟩
    → ⟨ pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩
  dIs-var-out i v e γ sat =
    PT.rec (snd (pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ)))
    (λ { (m′ , hp) →
      subst (λ q → ⟨ pr q (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩)
      (hp .snd .fst)
      (subst ⟨_⟩ (appAt-adequate (suc e) zero (suc v) (m′ ∷ γ))
            (hp .snd .snd)) })
    sat

  -- ===================================================================
  -- NOT YET IN THIS FILE (parked; see lj-1.740-report.md and
  -- runs/unfinished-4c-5-6.agda.txt):  the bounded description `Bd`
  -- with its Delta0 certificate, the per-constructor adequacy against
  -- `cond`'s own clauses, the climb `R` with `size psi`, and the
  -- merge + `Sat-at-asConst` assembly.  All the ingredients above
  -- (place, the kit, dIs, the room) are the pieces that assembly
  -- consumes.
  -- ===================================================================
