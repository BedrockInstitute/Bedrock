{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.510] The three consK fields: how deep the shift really goes.
--
-- W3 FIRST, and ALONE: THE DEPTH.  The brief asks whether `KFactsCons`
-- composes eight more times over the eight cell prefix, and warns that
-- nobody has iterated it past six.  Two terms answer it, and the second
-- is the one that matters:
--
--   `tower-14`  iterates the shift to fourteen, by an induction that is
--               generic in the depth, so it stops at NO depth.
--   `depth-is-free`  says the fourteen deep lookup over the eight cell
--               prefix IS the six deep lookup over the frame, by `refl`.
--
-- The obligation is added only after W3 lands.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-510.Probe510 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS; KFactsCons )
open import L.Condensation.TwelveAgree {ℓ} lem using ( TFacts )
open import FOL.Syntax using ( var; _∈̇_; _∧̇_ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( isTransV; Lset )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ; LsetS )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using ( consAtL; consAtL-adequate )
open import L.Coding.Environment {ℓ} using ( env; cons; lookup-spec )
open import L.Coding.EnvSet {ℓ} lem using ( Ix; envS )
open import L.Coding.EnvSupply {ℓ} lem using ( module Fact )
open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open KFactsNS
open KFacts

-- =====================================================================
-- W3.  THE SHIFT DOES NOT STOP, AND THE FIELDS DO NOT NEED IT.
--
-- `KFactsCons` (src/L/Condensation.lagda.md:6122-6128) adds one `suc` to
-- all fourteen indices and one cons to the environment.  `[LJ-1.495]`
-- composed it six times at this frame
-- (agents/tasks/LJ-1-495/lj-1.495-report.md:71).  The brief asks for
-- eight more.
--
-- `KTower k` is that composition stated ONCE, at any depth: the record
-- `k` cells deeper, over ANY `k` cells.  `kTower` builds it by induction
-- on `k`, so no depth is special and there is no maximum to find.
-- =====================================================================

KTower : (k : ℕ) {m : ℕ}
         (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
         (γ : S ^ m) → Type (ℓ-suc ℓ)
KTower zero A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ =
  KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
KTower (suc k) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ =
  (c : S) → KTower k (suc A) (suc K) (suc N0) (suc N1) (suc N2) (suc N3)
                     (suc N4) (suc N5) (suc N6) (suc N7) (suc N8) (suc N9)
                     (suc N10) (suc N11) (c ∷ γ)

kTower : (k : ℕ) {m : ℕ}
         (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
         (γ : S ^ m)
       → KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
       → KTower k A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
kTower zero A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ f = f
kTower (suc k) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ f = λ c →
  kTower k (suc A) (suc K) (suc N0) (suc N1) (suc N2) (suc N3)
           (suc N4) (suc N5) (suc N6) (suc N7) (suc N8) (suc N9)
           (suc N10) (suc N11) (c ∷ γ)
    (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ c f)

-- =====================================================================
-- FOURTEEN, AT `KValue`'s OWN FRAME, AND NOT AN ESTIMATE.
-- `KValue` (src/L/Condensation.lagda.md:7380-7395) supplies one `KFacts`
-- over `Kenv : S ^ 14`.  `tower-14` is that record fourteen cells deeper,
-- which is the six of `[LJ-1.495]` plus the eight the brief asks about.
-- =====================================================================

module Depth
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  tower-14 : KTower 14 iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
  tower-14 = kTower 14 iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv facts

-- =====================================================================
-- AND THE FIELDS NEED NONE OF IT.
--
-- `TFacts.consK-exist` (src/L/Condensation/TwelveAgree.lagda.md:317-321)
-- concludes at `lookup (suc¹⁴ K)` of an EIGHT cell prefix on `γ'`.
-- Fourteen minus eight is six, and six is the shift every other field of
-- the record already carries (:133).  `lookup (suc i) (c ∷ γ)` is
-- `lookup i γ` by definition and both sides are literal chains, so the
-- two are THE SAME `S`, not two sets joined by a transport.
--
-- The same arithmetic settles the other two: `consK-forall` (:322-325)
-- is fourteen over eight, and `consK-allin` (:332-336) is sixteen over
-- ten.  Both leave six.
-- =====================================================================

depth-is-free : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
                (x z E ya yc a ar c : S)
  → lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
      (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')
  ≡ lookup (suc (suc (suc (suc (suc (suc K)))))) γ'
depth-is-free K γ' x z E ya yc a ar c = refl

depth-is-free-allin : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
                      (x w z E ya yc b a ar c : S)
  → lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))))
      (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
  ≡ lookup (suc (suc (suc (suc (suc (suc K)))))) γ'
depth-is-free-allin K γ' x w z E ya yc b a ar c = refl

-- =====================================================================
-- THE STATEMENT, WRITTEN ONCE AT THE GENERIC FRAME (W2).
--
-- `TFacts.consK-exist`'s type verbatim
-- (src/L/Condensation/TwelveAgree.lagda.md:317-321), at `TFacts`'s own
-- generic shape: `K : Fin (5 + n)` over `γ' : S ^ (11 + n)` (:130-131).
-- It is instantiated ONCE below, at `KValue`'s frame.
-- =====================================================================

ConsKExist : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) → Type (ℓ-suc ℓ)
ConsKExist {n} K γ' =
    (ya yc a ar c E z x e' : S)
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
        consAtL {9 + (11 + n)} zero (suc zero) (suc (suc zero))
        ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                     (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩

-- `ConsKExist` IS THE FIELD'S TYPE, AND AGDA SAYS SO.  The term below is
-- the record's own `consK-exist` read at `ConsKExist`, with no coercion,
-- no `subst` and no re-association.  It certifies the STATEMENT only; the
-- obligation below never calls it, and no `TFacts` field is used to prove
-- a `TFacts` field.

statement-matches : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → ConsKExist {n} K γ'
statement-matches N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  TFacts.consK-exist tf

-- =====================================================================
-- THE HONEST FORM, AND IT IS `src/`'s OWN.
--
-- THE SWEEP THE BRIEF ASKED FOR, RUN BEFORE ANY TERM WAS WRITTEN.  The
-- brief says `consK` occurs six times in `src/`, all inside
-- `src/L/Condensation/TwelveAgree.lagda.md`, and that nothing outside
-- that file names a `consK` of any shape.  BOTH ARE FALSE.  COUNT of
-- `consK` in `src/`: 44, in FOUR files.  The closure over `consAtL` that
-- the brief told me to look for EXISTS:
--
--   src/L/Coding/EnvSupply.lagda.md:626-668   module Fact.ConsK
--   src/L/Coding/EnvSupply.lagda.md:702-748   module Fact.ConsKClosed
--   src/L/Coding/EnvSupply.lagda.md:672-700   module Fact.EnvClosure (envConsK)
--
-- Each of the two carries all THREE names, `consK-forall`, `consK-allin`
-- and `consK-exist`.  So the family had a supplier all along.
--
-- AND THE SUPPLIER'S `consK-exist` TAKES ONE HYPOTHESIS THE RECORD'S
-- FIELD DOES NOT: `⟨ fst ya ∈ fst K ⟩`
-- (src/L/Coding/EnvSupply.lagda.md:661-668, and again at :742-748).  Its
-- whole body is `Ktr (h .snd) yaK`.  The record dropped that hypothesis
-- (src/L/Condensation/TwelveAgree.lagda.md:317-321), and `Refute` below
-- measures what dropping it costs: the bare form is FALSE at this frame.
--
-- `ConsKExist⁺` is the field with that one hypothesis restored.  It pins
-- NO slot of `γ'`: `ya` is a bound variable of the field, so nothing here
-- fixes what occupies any cell, and `[LJ-1.505]` is not pre-empted.
-- =====================================================================

ConsKExist⁺ : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) → Type (ℓ-suc ℓ)
ConsKExist⁺ {n} K γ' =
    (ya yc a ar c E z x e' : S)
  → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
        consAtL {9 + (11 + n)} zero (suc zero) (suc (suc zero))
        ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                     (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩

-- =====================================================================
-- THE ONE INPUT, AND NOTHING ELSE.
--
-- `arity` is `KFacts.arityK`'s SHAPE over `S`
-- (src/L/Condensation.lagda.md:6114-6115), which is the form the frame
-- delivers.  `[LJ-1.509]` measured that this is the right thing to ask a
-- frame for, and that `isL-trans` (src/L/Constructible.lagda.md:379) is
-- the whole bridge to `isTransV` over the raw carrier
-- (agents/tasks/LJ-1-509/lj-1.509-report.md, section 3).  I re-measured
-- it here rather than transferring it (a measured cure does not transfer
-- by analogy, AGENTS.md:45): the packaging typechecks at THIS site, and
-- it is the same three lines.
--
-- `depth-is-free` above is what makes the conclusion reachable at all:
-- the field's fourteen deep lookup over the eight cell prefix IS
-- `Kset`, so `Ktr` lands directly and NO `KFactsCons` is applied.
-- =====================================================================

module ConsK {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  (arity : (N v : S) → ⟨ fst v ∈ fst N ⟩
         → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  where

  Kset : S
  Kset = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

  Ktr : isTransV (fst Kset)
  Ktr {A} {u} u∈A A∈K = arity (A , isLA) (u , isL-trans u∈A isLA) u∈A A∈K
    where
    isLA : ⟨ isL A ⟩
    isLA = isL-trans A∈K (snd Kset)

  module F = Fact Kset Ktr

  -- The membership atom is the second conjunct, and transitivity of the
  -- bound closes it.  The `consAtL` conjunct is NOT used: it is what
  -- `consK-forall` needs and what this field can do without.
  consK-exist : ConsKExist⁺ {n} K γ'
  consK-exist ya yc a ar c E z x e' yaK h = Ktr (h .snd) yaK

-- =====================================================================
-- THE OBLIGATION, AT `KValue`'s FRAME.
--
-- `KValue` (src/L/Condensation.lagda.md:7380-7395) binds the carrier and
-- the stage and supplies ONE `KFacts` value, `facts` (:7411), over
-- `Kenv : S ^ 14`.  Six cons cells put it at `TFacts`'s lengths, the
-- frame `[LJ-1.495]` measured
-- (agents/tasks/LJ-1-495/lj-1.495-report.md:56-60): `S ^ 20` is
-- `S ^ (11 + 9)` and `Fin 14` is `Fin (5 + 9)`.
--
-- `arityK` NEEDS NO `KFactsCons` HERE, and neither does the conclusion.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  consK-exist-at-KValue :
      (c1 c2 c3 c4 c5 c6 : S)
    → ConsKExist⁺ {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
  consK-exist-at-KValue c1 c2 c3 c4 c5 c6 =
    ConsK.consK-exist {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
      (facts .arityK)

consK-exist-at-frame = Frame.consK-exist-at-KValue

-- =====================================================================
-- AND `yaK` CANNOT BE DROPPED.  THE FRAME DOES NOT DECIDE IT.
--
-- C-42: a refutation measures the site it names.  This one names
-- `KValue`'s frame, not a generic one.
--
-- The witness is an ENVIRONMENT, because that is what `consAtL` talks
-- about, and `src/` already builds environments inside `L`: `envS`
-- (src/L/Coding/EnvSet.lagda.md:153-154) takes an index function into a
-- set of `L` and returns the graph AS an element of `L`, with
-- `fst (envS B g)` DEFINITIONALLY `env` of the values.  That is the whole
-- reason this refutation is cheap: no extensionality argument is needed
-- to say what the witness set is.
--
-- Take `B` one cell above the bound, so the bound itself is a value:
-- `B = sucʟ Lλ` and `Lset lam ∈ fst B` by `self∈sucV`
-- (src/V/Model.lagda.md:236), the same idiom `[LJ-1.506]` used
-- (agents/tasks/LJ-1-506/Probe506.agda:128-130).  Then
--
--   z  = the EMPTY environment over `B`
--   x  = the bound itself
--   e' = `z` with `x` consed on, which `consAtL-adequate`
--        (src/L/Coding/Model.lagda.md:1487-1498) says satisfies the
--        formula, and it is the only content of the first conjunct
--   ya = `sucʟ e'`, which gives the membership atom for free
--
-- If the bare form held, `e'` would lie in the bound.  The bound is
-- transitive, so its entry `pr (# 0) (Lset lam)` would too
-- (`lookup-spec`, src/L/Coding/Environment.lagda.md:102-104), and `prK`
-- (src/L/Coding/EnvSupply.lagda.md:452-459) would put `Lset lam` inside
-- itself.  `∈-irrefl` (src/V/Hierarchy.lagda.md:155) closes it.
--
-- SO THE WEAKEST REPAIRING HYPOTHESIS IS `yaK` ITSELF, which is the one
-- the obligation takes and the one `src/`'s own honest form already
-- takes.  No slot is pinned by it.
-- =====================================================================

module Refute
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  Lλ : S
  Lλ = LsetS lam ordλ

  -- One cell above the bound, so the bound is a VALUE of an environment.
  BB : S
  BB = sucʟ Lλ

  Lλ∈BB : ⟨ Lset lam ∈ fst BB ⟩
  Lλ∈BB = subst (λ u → ⟨ Lset lam ∈ u ⟩) (sym (sucʟ-fst Lλ))
            (self∈sucV (Lset lam))

  m₀ : ⟪ fst BB ⟫
  m₀ = ∈-asFiber {a = Lset lam} {b = fst BB} Lλ∈BB .fst

  q₀ : ⟪ fst BB ⟫↪ m₀ ≡ Lset lam
  q₀ = ∈-asFiber {a = Lset lam} {b = fst BB} Lλ∈BB .snd

  g₀ : Ix BB 0
  g₀ = λ ()

  g₁ : Ix BB 1
  g₁ = λ _ → m₀

  zz : S
  zz = envS BB g₀

  ee : S
  ee = envS BB g₁

  -- The raw value function of the empty environment.  `hE` is `refl`
  -- because `envS` builds `env` of exactly this.
  gg : Fin 0 → V ℓ
  gg i = ⟪ fst BB ⟫↪ (g₀ i)

  hE : fst zz ≡ env gg
  hE = refl

  qcons : fst ee ≡ env (cons (fst Lλ) gg)
  qcons = cong env (funExt (λ { zero → q₀ ; (suc ()) }))

  yaBad : S
  yaBad = sucʟ ee

  ee∈yaBad : ⟨ fst ee ∈ fst yaBad ⟩
  ee∈yaBad = subst (λ u → ⟨ fst ee ∈ u ⟩) (sym (sucʟ-fst ee))
               (self∈sucV (fst ee))

  γR : S ^ (9 + 20)
  γR = ee ∷ Lλ ∷ zz ∷ ∅ʟ ∷ yaBad ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ
     ∷ (∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ Kenv)

  hcons : ⟨ γR ⊨ consAtL {9 + 20} zero (suc zero) (suc (suc zero)) ⟩
  hcons = subst ⟨_⟩
            (sym (consAtL-adequate zero (suc zero) (suc (suc zero)) γR gg hE))
            qcons

  -- The entry of the witness environment at key 0 is the bound.
  entry : ⟨ pr (# 0) (⟪ fst BB ⟫↪ m₀) ∈ fst ee ⟩
  entry = subst ⟨_⟩
            (sym (lookup-spec (λ i → ⟪ fst BB ⟫↪ (g₁ i)) zero (⟪ fst BB ⟫↪ m₀)))
            refl

  module CK = ConsK {9} iK (∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ Kenv) (facts .arityK)

  no-yaK-is-not-a-theorem :
      ( (c1 c2 c3 c4 c5 c6 : S)
      → ConsKExist {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) )
    → Empty.⊥
  no-yaK-is-not-a-theorem h = ∈-irrefl (Lset lam)
    (subst (λ w → ⟨ w ∈ Lset lam ⟩) q₀
      (CK.F.prK (# 0) (⟪ fst BB ⟫↪ m₀)
        (CK.Ktr entry
          (h ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ
             yaBad ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ zz Lλ ee (hcons , ee∈yaBad)))
        .snd))

no-yaK-is-not-a-theorem = Refute.no-yaK-is-not-a-theorem

-- =====================================================================
-- C-42: THE SWEEP.  THE REFUTATION ABOVE NAMES ONE SITE.  HOW FAR DOES
-- THE SHAPE GO?
--
-- `dev/LESSONS.md:3752` says a refutation measures ONE site and says
-- nothing about how many others carry the same false shape, so the next
-- action is the sweep and the COUNT, before any cure is priced.  The
-- COUNT of fields of this record that state a `consAtL` closure is
-- THREE, and the two below are the other two.  The SAME witness settles
-- both: neither uses the membership atom, so both are strictly stronger
-- than the field already refuted.
--
-- I DID NOT BUILD EITHER FIELD.  These are refutations, which is the
-- opposite of an inhabitant, and the brief's one obligation stays one.
-- =====================================================================

ConsKForall : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) → Type (ℓ-suc ℓ)
ConsKForall {n} K γ' =
    (ya yc a ar c E z x e' : S)
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
        consAtL {9 + (11 + n)} zero (suc zero) (suc (suc zero)) ⟩
  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                     (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩

ConsKAllin : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) → Type (ℓ-suc ℓ)
ConsKAllin {n} K γ' =
    (E ya yc b a ar c z w x e' : S)
  → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
        consAtL {11 + (11 + n)} zero (suc zero) (suc (suc (suc zero))) ⟩
  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))))
                     (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩

-- Both types are the record's own, and Agda says so.

statement-matches-forall : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → ConsKForall {n} K γ'
statement-matches-forall N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  TFacts.consK-forall tf

statement-matches-allin : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → ConsKAllin {n} K γ'
statement-matches-allin N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  TFacts.consK-allin tf

module Sweep
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  open Refute lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- `consK-forall` reads `z` at the SAME index, so the witness is the
  -- one already built.
  forall-is-not-a-theorem :
      ( (c1 c2 c3 c4 c5 c6 : S)
      → ConsKForall {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) )
    → Empty.⊥
  forall-is-not-a-theorem h = ∈-irrefl (Lset lam)
    (subst (λ w → ⟨ w ∈ Lset lam ⟩) q₀
      (CK.F.prK (# 0) (⟪ fst BB ⟫↪ m₀)
        (CK.Ktr entry
          (h ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ
             yaBad ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ zz Lλ ee hcons))
        .snd))

  -- `consK-allin` reads `z` ONE cell further in, so the witness needs a
  -- new environment vector and NOTHING else: same `gg`, same `qcons`.
  γA : S ^ (11 + 20)
  γA = ee ∷ Lλ ∷ ∅ʟ ∷ zz ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ
     ∷ (∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ Kenv)

  hconsA : ⟨ γA ⊨ consAtL {11 + 20} zero (suc zero) (suc (suc (suc zero))) ⟩
  hconsA = subst ⟨_⟩
             (sym (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
                     γA gg hE))
             qcons

  allin-is-not-a-theorem :
      ( (c1 c2 c3 c4 c5 c6 : S)
      → ConsKAllin {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) )
    → Empty.⊥
  allin-is-not-a-theorem h = ∈-irrefl (Lset lam)
    (subst (λ w → ⟨ w ∈ Lset lam ⟩) q₀
      (CK.F.prK (# 0) (⟪ fst BB ⟫↪ m₀)
        (CK.Ktr entry
          (h ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ
             ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ zz ∅ʟ Lλ ee hconsA))
        .snd))

forall-is-not-a-theorem = Sweep.forall-is-not-a-theorem
allin-is-not-a-theorem = Sweep.allin-is-not-a-theorem
