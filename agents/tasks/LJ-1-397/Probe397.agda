{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.397] PROBE.  The ordinal-least CODED cardinal, and the arrow as
-- DATA.  It runs in agents/tasks/LJ-1-397/ and lands nothing in src/.
--
--   TERM 1  `coded-least`.  The mirror of `LeastCardInjL`
--            (src/L/Cardinal.lagda.md:60-155) with the CODED predicate:
--            the ORDINAL order over the members of `sucV (fst a)`, with
--            the predicate "receives a code".  The selection returns the
--            least ordinal `b` that receives a code, with its coded
--            witness and its ordinal minimality, all as data.
--
--   TERM 2  `coded-arrow`.  The arrow `⟪ fst a ⟫ ↪ ⟪ fst b ⟫` as DATA,
--            at a site where the internal cardinal fails.  THREE STEPS:
--            step 1 reads a member with a code out of the failure;
--            step 2 selects the least coded ordinal `b`; step 3 reads
--            the code out through the door.
--
-- THE DOOR AND THE IDENTITY CODE ARE HYPOTHESES, not imports.  The door
-- is `code-untruncates` (agents/tasks/LJ-1-386/Probe386.agda:264-268).
-- The brief names `code-exists` (:227-230), which is `Canonical.Good` at
-- one site; the nonempty this mirror consumes is the stronger identity
-- `InjCode G D D` (`IdGraph.idCode`, :186-187), taken at a generic `a`.
-- Both types live in a `lem`-taking module, so they cannot sit in the
-- preamble: `coded-arrow` takes them as arguments.
--
-- W3, THE CODE-QUANTIFIER MISMATCH.  `IsCardinalL` quantifies the code
-- over all of `S`; `coded-least`'s predicate quantifies it over
-- `Mem (Lset (SiteBound.β a))`.  The probe `code-lands` states the one
-- implication from the `S` form to the `Mem` form; it fails on the
-- placement residue (see the report).  So `coded-arrow` is delivered
-- under the REPAIRED hypothesis `IsCardinalL-Mem a → Empty.⊥`, whose
-- code quantifier is the `Mem` form.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-397.Probe397 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module SiteBound )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- TERM 1.  `coded-least`: the ORDINAL order with the CODED predicate.
--
--   The mirror of `LeastCardInjL` (src/L/Cardinal.lagda.md:60-155),
--   line by line, with the ambient predicate `InjP'` replaced by the
--   coded predicate `CodeP'`: a tower member `m` satisfies it when its
--   lift `upT m` receives a code from `Mem (Lset β)`.  The well-order
--   is SEALED exactly as the delivered module seals it, and `w-lt` is
--   the one read the seal needs.
--
--   The nonempty witness is the IDENTITY code: `a` itself receives a
--   code, carried at the tower member `self` whose lift is `a`.
-- =====================================================================

coded-least : (a : S) (oa : IsOrd (fst a))
            → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                  InjCode (SiteBound.up a F) a a ∥₁
            → Σ[ b ∈ S ] ( ⟨ fst b ∈ sucV (fst a) ⟩
                         × ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                               InjCode (SiteBound.up a F) a b ∥₁
                         × ((c : S) → ⟨ fst c ∈ fst b ⟩
                            → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                                  InjCode (SiteBound.up a F) a c ∥₁
                            → Empty.⊥) )
coded-least a oa nonempty = (κ , (κ∈sα , (κ-code , κ-min-at)))
  where
  open SiteBound a renaming ( up to upβ )

  -- The tower lift, exactly as in `LeastCardInjL`.
  hSuca : ⟨ isL (sucV (fst a)) ⟩
  hSuca = Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
            (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upT : ⟪ sucV (fst a) ⟫ → S
  upT m = ⟪ sucV (fst a) ⟫↪ m
        , isL-trans (member (sucV (fst a)) m) hSuca

  -- The coded predicate: a target receives a code.
  CodeP : S → hProp (ℓ-suc ℓ)
  CodeP γ = (∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (upβ F) a γ ∥₁)
          , squash₁

  CodeP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  CodeP' m = CodeP (upT m)

  -- The well-order is SEALED (R-36), exactly as in `LeastCardInjL`.
  opaque
    w : SWO (⟪ sucV (fst a) ⟫)
    w = ordSWO (sucV (fst a)) (suc-ord oa)

  opaque
    unfolding w
    w-lt : (m n : ⟪ sucV (fst a) ⟫)
         → SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst a) ⟫↪ m ∈ˢ ⟪ sucV (fst a) ⟫↪ n ⟩
    w-lt m n = refl

  self : ⟪ sucV (fst a) ⟫
  self = fiber (sucV (fst a)) (self∈sucV (fst a)) .fst

  self-eq : ⟪ sucV (fst a) ⟫↪ self ≡ fst a
  self-eq = fiber (sucV (fst a)) (self∈sucV (fst a)) .snd

  upT-self≡a : upT self ≡ a
  upT-self≡a = Σ≡Prop (λ v → snd (isL v)) self-eq

  nonempty' : ∥ Σ[ m ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodeP' m ⟩ ∥₁
  nonempty' = PT.map into nonempty
    where
    into : Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (upβ F) a a
         → Σ[ m ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodeP' m ⟩
    into (F , code) = self
      , ∣ F , subst (λ γ → InjCode (upβ F) a γ) (sym upT-self≡a) code ∣₁

  least : Σ[ m ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w CodeP' m
  least = leastOf w lem CodeP' nonempty'

  γ-card : ⟪ sucV (fst a) ⟫
  γ-card = fst least

  κ : S
  κ = upT γ-card

  κ∈sα : ⟨ fst κ ∈ sucV (fst a) ⟩
  κ∈sα = member (sucV (fst a)) γ-card

  -- The witness: a code into `κ`, still truncated, still a proposition.
  κ-code : ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (upβ F) a κ ∥₁
  κ-code = fst (snd least)

  κ-min : (m : ⟪ sucV (fst a) ⟫) → ⟨ CodeP' m ⟩
        → (SWO._<∙_ w m γ-card → Empty.⊥)
  κ-min = snd (snd least)

  κ-min-at : (c : S) → ⟨ fst c ∈ fst κ ⟩
           → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (upβ F) a c ∥₁
           → Empty.⊥
  κ-min-at c c∈κ c-code = κ-min m mCode m<γ
    where
    c∈sα : ⟨ fst c ∈ sucV (fst a) ⟩
    c∈sα = suc-ord oa .fst {x = fst κ} {y = fst c} c∈κ κ∈sα
    m : ⟪ sucV (fst a) ⟫
    m = fiber (sucV (fst a)) c∈sα .fst
    mc : ⟪ sucV (fst a) ⟫↪ m ≡ fst c
    mc = fiber (sucV (fst a)) c∈sα .snd
    upT-m≡c : upT m ≡ c
    upT-m≡c = Σ≡Prop (λ v → snd (isL v)) mc
    mCode : ⟨ CodeP' m ⟩
    mCode = subst (λ γ → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                            InjCode (upβ F) a γ ∥₁)
              (sym upT-m≡c) c-code
    m<γ : SWO._<∙_ w m γ-card
    m<γ = transport (λ i → sym (w-lt m γ-card) i)
            (subst (λ z → ⟨ z ∈ fst κ ⟩) (sym mc) c∈κ)

-- =====================================================================
-- The internal cardinal with the code quantifier over `Mem (Lset β)`,
-- the Mem form `coded-arrow` takes as its hypothesis (the repaired
-- hypothesis of W3).
-- =====================================================================

IsCardinalL-Mem : S → Type (ℓ-suc ℓ)
IsCardinalL-Mem κ =
  (δ : S) → ⟨ fst δ ∈ fst κ ⟩
          → (∥ Σ[ F ∈ Mem (Lset (SiteBound.β κ)) ]
                  InjCode (SiteBound.up κ F) κ δ ∥₁ → Empty.⊥)

-- =====================================================================
-- TERM 2.  `coded-arrow`.  THREE STEPS.
--
--   STEP 1  `¬ IsCardinalL-Mem a` gives, by `lem` at the truncated
--           existence, a member `c` of `fst a` with a merely existing
--           Mem-code.  The conclusion is a proposition, so nothing is
--           untruncated here.
--
--   STEP 2  `coded-least` at `a`, fed by the identity code, gives `b`
--           as data with its coded witness and its ordinal minimality.
--           Minimality against `c` refutes `fst b ≡ fst a`, so the
--           `sucV` case split leaves `⟨ fst b ∈ fst a ⟩`.
--
--   STEP 3  The door at source `a` and target `b` gives the arrow.
-- =====================================================================

Door : Type (ℓ-suc ℓ)
Door = (a b : S) → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β a)) ]
                      InjCode (SiteBound.up a A) a b ∥₁
                 → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

IdCode : Type (ℓ-suc ℓ)
IdCode = (a : S) → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                      InjCode (SiteBound.up a F) a a ∥₁

coded-arrow : (door : Door) (id-code : IdCode)
            → (a : S) (oa : IsOrd (fst a)) → (IsCardinalL-Mem a → Empty.⊥)
            → Σ[ b ∈ S ] (⟨ fst b ∈ fst a ⟩ × (⟪ fst a ⟫ ↪ ⟪ fst b ⟫))
coded-arrow door id-code a oa ¬card = (b , (b∈a , arrow))
  where
  open SiteBound a renaming ( up to upβ )

  sel : Σ[ b ∈ S ] ( ⟨ fst b ∈ sucV (fst a) ⟩
                   × ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                         InjCode (upβ F) a b ∥₁
                   × ((c : S) → ⟨ fst c ∈ fst b ⟩
                      → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                            InjCode (upβ F) a c ∥₁ → Empty.⊥) )
  sel = coded-least a oa (id-code a)

  b : S
  b = sel .fst

  b∈suc : ⟨ fst b ∈ sucV (fst a) ⟩
  b∈suc = sel .snd .fst

  code-b : ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (upβ F) a b ∥₁
  code-b = sel .snd .snd .fst

  min-b : (c : S) → ⟨ fst c ∈ fst b ⟩
        → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (upβ F) a c ∥₁
        → Empty.⊥
  min-b = sel .snd .snd .snd

  -- STEP 3.  The door, at source `a` and target `b`.
  arrow : ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  arrow = door a b code-b

  -- STEP 1.  A member of `a` with a Mem-code, merely, from the failure.
  Exists : Type (ℓ-suc ℓ)
  Exists = ∥ Σ[ c ∈ S ] (⟨ fst c ∈ fst a ⟩
                        × ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                                InjCode (upβ F) a c ∥₁) ∥₁

  c-witness : Exists
  c-witness = decide (lem (Exists , squash₁))
    where
    decide : Exists ⊎ (Exists → Empty.⊥) → Exists
    decide (inl q) = q
    decide (inr ¬q) = Empty.rec (¬card rebuild)
      where
      rebuild : IsCardinalL-Mem a
      rebuild δ δ∈a code = ¬q ∣ δ , (δ∈a , code) ∣₁

  -- STEP 2.  Minimality against `c` refutes `fst b ≡ fst a`.
  b∈a : ⟨ fst b ∈ fst a ⟩
  b∈a = ∈sucV-elim {A = fst a} {x = fst b} (snd (fst b ∈ fst a)) b∈suc
          (λ b∈a → b∈a) (λ b≡a → Empty.rec (contra b≡a))
    where
    contra : fst b ≡ fst a → Empty.⊥
    contra b≡a = PT.rec Empty.isProp⊥
      (λ { (c , (c∈a , code-c)) →
           min-b c (subst (λ v → ⟨ fst c ∈ v ⟩) (sym b≡a) c∈a) code-c })
      c-witness
