{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.184] probe A.  THE CARRIER-GENERIC READ-OFF, and Devlin's
-- clause (a) at the AMBIENT carrier.
--
-- [LJ-1.178] built `levelIn` and `cover` at the real site as functions
-- of four hypotheses and named the one it could not write:
--
--   AmbientRead = (v b : S) -> IsOrd b
--               -> < (v :: b :: []) AbsP.|=v embed f0 > -> v == Lset b
--
-- The tree delivers that read-off at the CLASS carrier only
-- (`Lset-only`, src/L/Hierarchy.lagda.md:334-335, fixed at 𝒮ʟ by :73
-- and :78-79).  This probe RESTATES the read-off with the carrier a
-- module parameter and the satisfaction relation a module parameter,
-- and instantiates it TWICE: at the class carrier, where it must
-- reproduce `Lset-only`, and at the AMBIENT carrier, where it is
-- Devlin's (a).
--
--   SECTION 1  the shapes, generic in a class Cl
--   SECTION 2  the machine: step-Lset, approx-val, read-off
--   SECTION 3  the CLASS instance, checked against the delivered one
--   SECTION 4  the AMBIENT instance, and `AmbientRead`
--
-- DD4.  Nothing in sections 1 and 2 names `isL`, `𝒮ʟ` or a tower
-- stage.  The class is a parameter with three closure hypotheses, the
-- satisfaction is a parameter, and the coded step enters as six
-- readings.  Both towers instantiate the same module.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, and it lives beside its report.

open import Base.Prelude
open import Base.Truth

module LJ-1-184.ProbeLJ1184A {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Manipulation.Relabelling using ( mapFo; embed; embed-⊨ )

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( Lset; IsOrd; 𝒟ₒ; Lset-in; Lset-out; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord )

open import Cubical.Data.Sigma using ( _×_; _,_; Σ≡Prop )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; [] )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

-- =====================================================================
-- SECTION 1: THE SHAPES, GENERIC IN A CLASS.
--
-- `Cl` replaces `isL`; the three closure hypotheses replace
-- `isL-trans`, `LsetS` and `isL-𝒟ₒ`.  Nothing below names a tower
-- presentation, so P-l holds by construction.
-- =====================================================================

module ReadOff
  -- THE TOWER AXIS.  `Tow` is the tower, `Dee` its step operation, and
  -- the two legs are the tower's own decomposition.  The L tower
  -- instantiates them with `Lset`, `𝒟ₒ`, `Lset-in` and `Lset-out`
  -- (src/L/Constructible.lagda.md:319, :336); the J tower supplies its
  -- own four and re-instantiates.  Nothing below names either tower.
  (Tow : V ℓ → V ℓ)
  (Dee : V ℓ → V ℓ)
  (Tow-in : (α δ x : V ℓ) → ⟨ δ ∈ˢ α ⟩ → ⟨ x ∈ˢ Dee (Tow δ) ⟩
          → ⟨ x ∈ˢ Tow α ⟩)
  (Tow-out : (α x : V ℓ) → ⟨ x ∈ˢ Tow α ⟩
           → ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ Dee (Tow δ) ⟩) ∥₁)
  -- THE CARRIER AXIS.  `Cl` is the class the reading happens in.
  (Cl : S → Ω)
  (Cl-tr : Transitive 𝒮ᵥ Cl)
  (Cl-Tow : (d : V ℓ) → IsOrd d → ⟨ Cl (Tow d) ⟩)
  (Cl-Dee : (d : V ℓ) → IsOrd d → ⟨ Cl (Dee (Tow d)) ⟩)
  where

  module Abs = FOL.Absoluteness.Single 𝒮ᵥ Cl Cl-tr

  SC : Type (ℓ-suc ℓ)
  SC = Abs.SM

  -- src/L/Hierarchy.lagda.md:112-124, with `isL` abstracted away.
  Values : SC → V ℓ → Type (ℓ-suc ℓ)
  Values h B = (c z : SC) → ⟨ fst c ∈ B ⟩
             → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → fst z ≡ Tow (fst c)

  Entries : SC → V ℓ → Type (ℓ-suc ℓ)
  Entries h B = (c : SC) → ⟨ fst c ∈ B ⟩
              → ⟨ pr (fst c) (Tow (fst c)) ∈ fst h ⟩

  -- src/L/Coding/Sequence.lagda.md:155-163 and :283-284.
  Records : ∀ {n} → Fin n → Fin n → Vec SC n → SC → SC → Type (ℓ-suc ℓ)
  Records b f γ c w = ⟨ fst c ∈ fst (lookup b γ) ⟩
                    × ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩

  StepOf : ∀ {n} → Fin n → Fin n → Vec SC n → SC → Type (ℓ-suc ℓ)
  StepOf b f γ z = Σ[ c ∈ SC ] Σ[ w ∈ SC ]
                     (Records b f γ c w × ⟨ fst z ∈ Dee (fst w) ⟩)

  PowOK : ∀ {n} → Fin n → Fin n → Vec SC n → Type (ℓ-suc ℓ)
  PowOK b f γ = (c w : SC) → Records b f γ c w → ⟨ Cl (Dee (fst w)) ⟩

  Domain₀ : SC → V ℓ → Type (ℓ-suc ℓ)
  Domain₀ h B = (c z : SC) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩

-- =====================================================================
-- SECTION 2: THE MACHINE.
--
-- The satisfaction relation is a PARAMETER.  The read-off proof never
-- unfolds it: it only spends the six readings below.  That is what
-- lets one module serve the inner reading at `L` and the AMBIENT
-- reading in `V` with no bridge lemma between them.
-- =====================================================================

  module Machine
    (_⊨_ : ∀ {n} → Vec SC n → Formula SC n → Ω)
    (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula SC n)
    (Approx : ∀ {n} → Fin n → Fin n → Formula SC n)
    (Graph : ∀ {n} → Fin n → Fin n → Formula SC n)
    (Step-out : ∀ {n} (v b f : Fin n) (γ : Vec SC n)
              → ⟨ γ ⊨ Step v b f ⟩ → PowOK b f γ
              → (z : SC) → ⟨ fst z ∈ fst (lookup v γ) ⟩
              → ∥ StepOf b f γ z ∥₁)
    (Step-back : ∀ {n} (v b f : Fin n) (γ : Vec SC n)
               → ⟨ γ ⊨ Step v b f ⟩ → PowOK b f γ
               → (z : SC) → StepOf b f γ z → ⟨ fst z ∈ fst (lookup v γ) ⟩)
    (Approx-dom : ∀ {n} (f a : Fin n) (γ : Vec SC n)
                → ⟨ γ ⊨ Approx f a ⟩
                → Domain₀ (lookup f γ) (fst (lookup a γ)))
    (Approx-value : ∀ {n} (f a : Fin n) (γ : Vec SC n)
                  → ⟨ γ ⊨ Approx f a ⟩ → (c : SC)
                  → ⟨ fst c ∈ fst (lookup a γ) ⟩
                  → ∥ (Σ[ z ∈ SC ]
                        ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩) ∥₁)
    (Approx-step : ∀ {n} (f a : Fin n) (γ : Vec SC n)
                 → ⟨ γ ⊨ Approx f a ⟩ → (c z : SC)
                 → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                 → ⟨ (z ∷ c ∷ γ) ⊨ Step zero (suc zero) (sh2 f) ⟩)
    (Graph-out : ∀ {n} (w b : Fin n) (γ : Vec SC n)
               → ⟨ γ ⊨ Graph w b ⟩
               → ∥ (Σ[ f ∈ SC ]
                     ( ⟨ (f ∷ γ) ⊨ Approx zero (suc b) ⟩
                     × ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ )) ∥₁)
    where

    -- src/L/Hierarchy.lagda.md:165-215, generic.
    module _ {n : ℕ} (v b f : Fin n) (γ : Vec SC n) where
      private
        ok : IsOrd (fst (lookup b γ)) → Values (lookup f γ) (fst (lookup b γ))
           → PowOK b f γ
        ok ob vals c z rec = subst (λ u → ⟨ Cl (Dee u) ⟩)
          (sym (vals c z (rec .fst) (rec .snd)))
          (Cl-Dee (fst c) (mem-ord {A = fst (lookup b γ)} ob (fst c) (rec .fst)))

        below : IsOrd (fst (lookup b γ))
              → Entries (lookup f γ) (fst (lookup b γ))
              → (z : SC)
              → Σ[ δ ∈ V ℓ ] (⟨ δ ∈ fst (lookup b γ) ⟩ × ⟨ fst z ∈ Dee (Tow δ) ⟩)
              → StepOf b f γ z
        below ob ents z (δ , (δ∈ , hz)) =
          d , ((Tow δ , Cl-Tow δ oδ) , ((δ∈ , ents d δ∈) , hz))
          where
          oδ : IsOrd δ
          oδ = mem-ord {A = fst (lookup b γ)} ob δ δ∈
          d : SC
          d = δ , Cl-tr {x = fst (lookup b γ)} {y = δ} δ∈ (lookup b γ .snd)

        above : Values (lookup f γ) (fst (lookup b γ)) → (z : SC)
              → StepOf b f γ z → ⟨ fst z ∈ Tow (fst (lookup b γ)) ⟩
        above vals z (c , (w , (rec , hz))) =
          Tow-in (fst (lookup b γ)) (fst c) (fst z) (rec .fst)
            (subst (λ u → ⟨ fst z ∈ Dee u ⟩) (vals c w (rec .fst) (rec .snd)) hz)

      step-value : ⟨ γ ⊨ Step v b f ⟩ → IsOrd (fst (lookup b γ))
                → Values (lookup f γ) (fst (lookup b γ))
                → Entries (lookup f γ) (fst (lookup b γ))
                → fst (lookup v γ) ≡ Tow (fst (lookup b γ))
      step-value h ob vals ents =
        extensionalV {a = fst (lookup v γ)} {b = Tow (fst (lookup b γ))} pt
        where
        fwd : (x : V ℓ) → ⟨ x ∈ fst (lookup v γ) ⟩
            → ⟨ x ∈ Tow (fst (lookup b γ)) ⟩
        fwd x hx = PT.rec (snd (x ∈ Tow (fst (lookup b γ)))) (above vals z)
          (Step-out v b f γ h (ok ob vals) z hx)
          where
          z : SC
          z = x , Cl-tr {x = fst (lookup v γ)} {y = x} hx (lookup v γ .snd)

        bwd : (x : V ℓ) → ⟨ x ∈ Tow (fst (lookup b γ)) ⟩
            → ⟨ x ∈ fst (lookup v γ) ⟩
        bwd x hx = PT.rec (snd (x ∈ fst (lookup v γ))) put
          (Tow-out (fst (lookup b γ)) x hx)
          where
          z : SC
          z = x , Cl-tr {x = Tow (fst (lookup b γ))} {y = x} hx
                    (Cl-Tow (fst (lookup b γ)) ob)
          put : Σ[ δ ∈ V ℓ ]
                  (⟨ δ ∈ fst (lookup b γ) ⟩ × ⟨ x ∈ Dee (Tow δ) ⟩)
              → ⟨ x ∈ fst (lookup v γ) ⟩
          put s = Step-back v b f γ h (ok ob vals) z (below ob ents z s)

        pt : (x : V ℓ) → (x ∈ fst (lookup v γ)) ≡ (x ∈ Tow (fst (lookup b γ)))
        pt x = ⇔toPath (fwd x) (bwd x)

    -- src/L/Hierarchy.lagda.md:268-300, generic.
    module _ {n : ℕ} (f a : Fin n) (γ : Vec SC n) where
      private
        Value : V ℓ → Type (ℓ-suc ℓ)
        Value u = ⟨ Cl u ⟩ → (z : SC)
                → ⟨ pr u (fst z) ∈ fst (lookup f γ) ⟩ → fst z ≡ Tow u

      approx-val : ⟨ γ ⊨ Approx f a ⟩ → IsOrd (fst (lookup a γ))
                 → (x z : SC) → ⟨ pr (fst x) (fst z) ∈ fst (lookup f γ) ⟩
                 → fst z ≡ Tow (fst x)
      approx-val h oa x = ∈-induction {P = Value} go (fst x) (snd x)
        where
        go : (u : V ℓ) → ((t : V ℓ) → ⟨ t ∈ u ⟩ → Value t) → Value u
        go u IH hu z p = step-value zero (suc zero) (sh2 f) (z ∷ d ∷ γ)
          (Approx-step f a γ h d z p) ou vals ents
          where
          d : SC
          d = u , hu
          u∈a : ⟨ u ∈ fst (lookup a γ) ⟩
          u∈a = Approx-dom f a γ h d z p
          ou : IsOrd u
          ou = mem-ord {A = fst (lookup a γ)} oa u u∈a
          vals : Values (lookup f γ) u
          vals c y c∈ q = IH (fst c) c∈ (snd c) y q
          ents : Entries (lookup f γ) u
          ents c c∈ = PT.rec
            (snd (pr (fst c) (Tow (fst c)) ∈ fst (lookup f γ))) named
            (Approx-value f a γ h c (oa .fst {x = u} {y = fst c} c∈ u∈a))
            where
            named : Σ[ y ∈ SC ] ⟨ pr (fst c) (fst y) ∈ fst (lookup f γ) ⟩
                  → ⟨ pr (fst c) (Tow (fst c)) ∈ fst (lookup f γ) ⟩
            named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst (lookup f γ) ⟩)
              (IH (fst c) c∈ (snd c) y q) q

    -- src/L/Hierarchy.lagda.md:333-355, generic.  THIS IS THE TERM.
    module _ {n : ℕ} (w b : Fin n) (γ : Vec SC n) where
      graph-only : ⟨ γ ⊨ Graph w b ⟩ → IsOrd (fst (lookup b γ))
                 → fst (lookup w γ) ≡ Tow (fst (lookup b γ))
      graph-only h ob = PT.rec
        (setIsSet (fst (lookup w γ)) (Tow (fst (lookup b γ)))) read
        (Graph-out w b γ h)
        where
        read : Σ[ f ∈ SC ] ( ⟨ (f ∷ γ) ⊨ Approx zero (suc b) ⟩
                           × ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ )
             → fst (lookup w γ) ≡ Tow (fst (lookup b γ))
        read (f , (ha , hs)) =
          step-value (suc w) (suc b) zero (f ∷ γ) hs ob vals ents
          where
          vals : Values f (fst (lookup b γ))
          vals c z _ p = approx-val zero (suc b) (f ∷ γ) ha ob c z p
          ents : Entries f (fst (lookup b γ))
          ents c c∈ = PT.rec (snd (pr (fst c) (Tow (fst c)) ∈ fst f)) named
            (Approx-value zero (suc b) (f ∷ γ) ha c c∈)
            where
            named : Σ[ y ∈ SC ] ⟨ pr (fst c) (fst y) ∈ fst f ⟩
                  → ⟨ pr (fst c) (Tow (fst c)) ∈ fst f ⟩
            named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst f ⟩)
              (approx-val zero (suc b) (f ∷ γ) ha ob c y q) q

-- =====================================================================
-- SECTION 3: THE CLASS INSTANCE.
--
-- `Cl = isL` and the inner reading `⊨ᵐ`.  The three closure
-- hypotheses are the three delivered facts, at their file:line.  This
-- instance must reproduce `Lset-only`, and section 3's type ascription
-- is the check.
-- =====================================================================

open import L.Axioms.Basic {ℓ} using ( LsetS; isL-𝒟ₒ )

module ClassSide where
  module R = ReadOff Lset 𝒟ₒ Lset-in Lset-out isL isL-trans
    (λ d od → LsetS d od .snd)          -- src/L/Axioms/Basic.lagda.md:160
    (λ d od → isL-𝒟ₒ d od)              -- src/L/Axioms/Basic.lagda.md:230

  -- The class carrier's own reading: `Single`'s inner semantics.
  inner : ∀ {n} → Vec R.SC n → Formula R.SC n → Ω
  inner = R.Abs._⊨ᵐ_

-- =====================================================================
-- SECTION 4: THE AMBIENT INSTANCE, AND `AmbientRead`.
--
-- `Cl` is the class of EVERYTHING, so all three closure hypotheses are
-- discharged by `tt*`, and the reading is `⊨ᵛ` at the projected
-- environment.  That is the AMBIENT reading, and the read-off at this
-- instance IS Devlin's clause (a).
-- =====================================================================

Full : S → Ω
Full _ = Unit* {ℓ-suc ℓ} , isPropUnit*

Full-tr : Transitive 𝒮ᵥ Full
Full-tr {x = x} {y = y} h k = tt*

Full-Lset : (d : V ℓ) → IsOrd d → ⟨ Full (Lset d) ⟩
Full-Lset d od = tt*

Full-Def : (d : V ℓ) → IsOrd d → ⟨ Full (𝒟ₒ (Lset d)) ⟩
Full-Def d od = tt*

module Ambient where
  module R = ReadOff Lset 𝒟ₒ Lset-in Lset-out
             Full (λ {x} {y} → Full-tr {x} {y}) Full-Lset Full-Def

  -- The AMBIENT reading, at the projected environment.
  ambient : ∀ {n} → Vec R.SC n → Formula R.SC n → Ω
  ambient γ φ = (map fst γ) R.Abs.⊨ᵛ φ

  up : S → R.SC
  up x = x , tt*

  -- The AMBIENT reading of a PARAMETER-FREE formula does not depend on
  -- the constant domain the formula is embedded into.  The delivered
  -- `embed-⊨` (src/FOL/Manipulation/Relabelling.lagda.md:184-186) is
  -- both halves; the empty domain's two interpretations agree because
  -- there is nothing to interpret.
  module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ

  free : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd}
         (ι : K → S) (ι' : K' → S) {n} (φ₀ : Formula (⊥* {ℓ-suc ℓ}) n)
         (γ : Vec S n)
       → ⟨ Sem.At._⊨_ K ι γ (embed φ₀) ⟩
       → ⟨ Sem.At._⊨_ K' ι' γ (embed φ₀) ⟩
  free {K = K} {K' = K'} ι ι' φ₀ γ h =
    subst ⟨_⟩ (sym (embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ ι' φ₀ γ))
      (subst (λ j → ⟨ Sem.At._⊨_ (⊥* {ℓ-suc ℓ}) j γ φ₀ ⟩)
             (funExt (λ b → Empty.rec* b))
        (subst ⟨_⟩ (embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ ι φ₀ γ) h))


  -- DEVLIN'S CLAUSE (a), AT THE AMBIENT CARRIER, IN [LJ-1.178]'s
  -- VERBATIM SHAPE.  `go` is `Machine.graph-only zero (suc zero)` at
  -- the ambient reading, for a `Graph` whose two-slot instance is the
  -- embedded level-hood formula.  Nothing else enters.
  clause-a : ∀ {ℓc} {K : Type ℓc} (ι : K → S)
             (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
             (go : (γ : Vec R.SC 2) → ⟨ ambient γ (embed φ₀) ⟩
                 → IsOrd (fst (lookup (suc zero) γ))
                 → fst (lookup zero γ) ≡ Lset (fst (lookup (suc zero) γ)))
             (v b : S) → IsOrd b
           → ⟨ Sem.At._⊨_ K ι (v ∷ b ∷ []) (embed φ₀) ⟩ → v ≡ Lset b
  clause-a ι φ₀ go v b ob h =
    go (up v ∷ up b ∷ []) (free ι fst φ₀ (v ∷ b ∷ []) h) ob
