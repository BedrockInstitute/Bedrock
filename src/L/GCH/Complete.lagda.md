# The level matrix is complete at an adequate stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Complete {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∃̇∈; ∀̇∈; ⊤̇ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using
  ( 𝒮ʟ; isL; isL-trans; IsOrd; isPropIsOrd; Lset; Lset-mono; Lset→isL
  ; 𝒟ₒ; 𝒟ₒ-intro; Lset-in; Lset-out )
open import L.Ordinal {ℓ} using
  ( boundingOrd; bound2; setUnion-ord; mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc; pair∈Lset-suc; sgl∈Lset-suc )
open import V.Model {ℓ} using ( self∈sucV )
open import FOL.Manipulation.Relabelling using ( embed )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using
  ( prʟ; prʟ-fst; prAtL; prAtL-adequate; envSetAt; sucAtL; sucAtL-adequate; appAt
  ; consAtL; consAtL-adequate; envOverAt )
open import L.Condensation {ℓ} lem using ( domB; closedBS; shapedBS; envSetB; module EnvSet )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; envSet-in; envSet-out; envS; Ix; module Recover )
open import L.Coding.Sound {ℓ} lem using ( module Ambient; module AmbientHolds )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; keyS )
open import L.Coding.Uniform {ℓ} lem using ( module Table )
open import L.GCH.Definable {ℓ} lem using ( DefinableMap ) renaming ( module Graph to MapGraph )
open import L.Coding.Bound {ℓ} lem using ( module Bound; Lset-out′; Lset-trans′ )
open import L.Coding.Key {ℓ} lem using ( union∈Lset-suc )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Hierarchy {ℓ} lem using ( hierL-spec; IsHier; hier-out; hier-in; Values; Entries )
open import L.BoundedSubset {ℓ} lem using ( module Cnt )
open import L.GCH.Frame {ℓ} lem using ( module W3; isOrd-at-p; _⊨ₚ_ )
open import L.GCH.Sound {ℓ} lem using ( read )
open import L.GCH.Level {ℓ} lem using
  ( module W3V; levelFo; Δ₀-levelFo; module DefV; module StepV; module ApproxV; module GraphV
  ; KC; Tags; tagsCons; app-in; app-out; pr-out; numsAt
  ; arNumAt; envTowerAt; towerAt; memAt; allAt; twelveAt; module Close
  ; i0; i1; i2; i3; sh1; sh2; sh3; sh4; sh5 )
open import L.GCH.LevelRows {ℓ} lem using ( module Chain )
open import L.Coding.Environment {ℓ} using ( env; cons )

open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _∈ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The class-carrier reading, as src/L/Condensation.lagda.md:76-77.
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The 𝒮ʟ carrier, for the syntax.  Same name as src/L/GCH/Level.lagda.md.
module CS = hPropStructure 𝒮ʟ

-- A member of a class-carrier element, packaged as one.
down : (x : CS.S) (y : V ℓ) → ⟨ y ∈ fst x ⟩ → CS.S
down x y y∈x = y , isL-trans {x = fst x} {y = y} y∈x (snd x)
```

```agda
-- =====================================================================
-- SECTION 1.  THE ENVIRONMENT TOWER IS AN ELEMENT OF L.  The table of
-- pairs (n, Eₙ) over a carrier B, Eₙ the environment set of arity n
-- (src/L/Coding/EnvSet.lagda.md `envSet`), cut by separation out of a
-- stage that holds every entry (src/L/Recursion.lagda.md `smallDom`).
-- The cutting formula names the entry shape: z = (n, E) with n a
-- numeral (a member of ωʟ) and E the environment set of arity n over B
-- (src/L/Coding/Model.lagda.md `envSetAt`).  Its two readers are the
-- adequacy of `envSetAt`, src/L/Coding/Sound.lagda.md `Ambient` and
-- `AmbientHolds`.
-- =====================================================================

module EnvTower (B : CS.S) where

  entry : ℕ → CS.S
  entry n = prʟ (numeralL n) (envSet B n)

  private
    dom : Σ[ d ∈ CS.S ] ((m : Lift {ℓ-zero} {ℓ} ℕ) → ⟨ fst (entry (lower m)) ∈ fst d ⟩)
    dom = smallDom (Lift {ℓ-zero} {ℓ} ℕ) (λ m → entry (lower m))

  -- At E ∷ n ∷ b ∷ z ∷ []: b = B, z = (n, E), n ∈ ω, E the environment
  -- set of arity n over b.
  towerFo : Formula CS.S 1
  towerFo = ∃̇ (∃̇ (∃̇ ( (var i2 ≐ con B)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 )))))

  opaque
    tower : CS.S
    tower = hasSeparationL (dom .fst) towerFo .fst .fst

    tower-mem : (x : CS.S)
              → (fst x ∈ fst tower) ≡ ((fst x ∈ fst (dom .fst)) ⊓ ((x ∷ []) ⊨ towerFo))
    tower-mem = hasSeparationL (dom .fst) towerFo .fst .snd

  -- The environment set of arity n satisfies the third conjunct at its
  -- numeral.
  private
    holdsAt : (n : ℕ) → ⟨ (envSet B n ∷ numeralL n ∷ B ∷ entry n ∷ []) ⊨ envSetAt i0 i1 i2 ⟩
    holdsAt n = AmbientHolds.holds B (envSet B n ∷ numeralL n ∷ B ∷ entry n ∷ [])
                  i0 i1 i2 n refl (numeralL-fst n) refl

  tower-in : (n : ℕ) → ⟨ fst (entry n) ∈ fst tower ⟩
  tower-in n = subst ⟨_⟩ (sym (tower-mem (entry n)))
    ( dom .snd (lift n)
    , ∣ B , ∣ numeralL n , ∣ envSet B n
      , ( refl
        , ( subst ⟨_⟩ (sym (prAtL-adequate i3 i1 i0 (envSet B n ∷ numeralL n ∷ B ∷ entry n ∷ [])))
              (prʟ-fst (numeralL n) (envSet B n))
          , ( subst ⟨_⟩ (sym (ω-specL (numeralL n))) ∣ lift n , refl ∣₁
            , holdsAt n ))) ∣₁ ∣₁ ∣₁ )

  -- The entry at a numeral, in the ambient shape.
  tower-in′ : (n : ℕ) → ⟨ pr (# n) (fst (envSet B n)) ∈ fst tower ⟩
  tower-in′ n = subst (λ u → ⟨ u ∈ fst tower ⟩)
    (prʟ-fst (numeralL n) (envSet B n) ∙ cong (λ u → pr u (fst (envSet B n))) (numeralL-fst n))
    (tower-in n)

  -- Every member is an entry.
  tower-out : (x : CS.S) → ⟨ fst x ∈ fst tower ⟩
            → ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet B n))) ∥₁
  tower-out x hx = PT.rec squash₁ byB (subst ⟨_⟩ (tower-mem x) hx .snd)
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet B n))) ∥₁

    byB : Σ[ b ∈ CS.S ] ⟨ (b ∷ x ∷ []) ⊨ ∃̇ (∃̇ ( (var i2 ≐ con B)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 )))) ⟩ → Goal
    byB (b , hb) = PT.rec squash₁ byN hb
      where
      byN : Σ[ n ∈ CS.S ] ⟨ (n ∷ b ∷ x ∷ []) ⊨ ∃̇ ( (var i2 ≐ con B)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
      byN (n , hn) = PT.rec squash₁ byE hn
        where
        byE : Σ[ E ∈ CS.S ] ⟨ (E ∷ n ∷ b ∷ x ∷ []) ⊨ ( (var i2 ≐ con B)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
        byE (E , (qb , (hp , (hω , hE)))) = PT.rec squash₁ byK (subst ⟨_⟩ (ω-specL n) hω)
          where
          xq : fst x ≡ pr (fst n) (fst E)
          xq = subst ⟨_⟩ (prAtL-adequate i3 i1 i0 (E ∷ n ∷ b ∷ x ∷ [])) hp

          byK : Σ[ k ∈ Lift {ℓ-zero} {ℓ-suc ℓ} ℕ ] (fst n ≡ fst (numeralL (lower k))) → Goal
          byK (k , qn) = ∣ lower k , xq ∙ cong₂ pr (qn ∙ numeralL-fst (lower k)) Eq ∣₁
            where
            module Am = Ambient B (E ∷ n ∷ b ∷ x ∷ []) i0 i1 i2 (lower k)
                          (qn ∙ numeralL-fst (lower k)) qb hE
            Eq : fst E ≡ fst (envSet B (lower k))
            Eq = extensionalV {a = fst E} {b = fst (envSet B (lower k))}
              (λ z → ⇔toPath
                (λ z∈ → Am.into (down E z z∈) z∈)
                (λ z∈ → Am.outof (down (envSet B (lower k)) z z∈) z∈))
```

```agda
-- =====================================================================
-- SECTION 2.  THE WITNESSES AT A STAGE, AND ADEQUACY.  At an ordinal c
-- the level formula's rows name four sets over the carrier w = Lset c:
-- the hierarchy table on c (the approximation slot f, src/L/GCH/Level
-- .lagda.md `GraphV`, `domB f a K` pins its domain to c), the code
-- set (the slot C of `DefV.body`), the uniform satisfaction table (the
-- slot T), and the environment tower (the slot Ê of `envTowerAt`).
-- Every other set the rows quantify is a member of one of these, or a
-- pair or numeral, and the closures of an adequate stage reach it.
-- =====================================================================

-- THE SATISFACTION TABLE AS A GRAPH.  src/L/Coding/Uniform.lagda.md
-- `Table` is the replacement IMAGE of the value function on the code
-- set: the set of values, with the codes forgotten.  The level
-- formula's slot T is read by `appAt T c v` (src/L/GCH/Level.lagda.md
-- `memAt`, `domB T C K`), so it wants the GRAPH: the pairs (c, value
-- at c).  src/L/GCH/Definable.lagda.md `Graph` builds that graph for
-- any definable map; the map here is the uniform table's own value
-- function, defined by its own recursion graph, landing in its image.
module SatMap (A : CS.S) where

  M : DefinableMap
  M = record
    { dom     = AllCodes A
    ; cod     = Table.table A A
    ; fn      = λ x m → Table.val A A x m
    ; into    = λ x m → Table.table-in A A x (Table.val A A x m) m
                          (Table.funct A A x m .fst .snd)
    ; graph   = Table.graph A A
    ; defines = λ x m → Table.funct A A x m .fst .snd
    ; only    = λ x m y h → sym (Table.val-uniq A A x m y h) }

  module G = MapGraph M

  -- SEALED (P-t): the value at a member is a contractibility centre,
  -- and written out inside a satisfaction it does not elaborate
  -- (src/L/Coding/Uniform.lagda.md `val-at`'s measurement: four
  -- seconds at a variable, past six minutes at the construction).
  -- Every consumer below names the value by this atom.
  opaque
    valOf : (x : CS.S) → ⟨ fst x ∈ fst (AllCodes A) ⟩ → CS.S
    valOf x m = Table.val A A x m

    valOf≡ : (x : CS.S) (m : ⟨ fst x ∈ fst (AllCodes A) ⟩) → valOf x m ≡ Table.val A A x m
    valOf≡ x m = refl

  -- The graph, SEALED for the reason `AllCodes` and `tower` are: a
  -- consumer compares the slot that holds it with the name, and open
  -- the comparison normalises the replacement image.  MEASURED: with
  -- `pairs` open, `Rows.dom` below exhausted the 8 GB heap in 106 s;
  -- sealed, the whole file checked in 23 s at 1.9 GB peak RSS.
  opaque
    pairs : CS.S
    pairs = G.F

  opaque
    unfolding valOf pairs

    pairs-in : (x : CS.S) (m : ⟨ fst x ∈ fst (AllCodes A) ⟩)
             → ⟨ pr (fst x) (fst (valOf x m)) ∈ fst pairs ⟩
    pairs-in = G.F-in

    pairs-out : (p : V ℓ) → ⟨ p ∈ fst pairs ⟩
              → ∥ Σ[ x ∈ CS.S ] Σ[ m ∈ ⟨ fst x ∈ fst (AllCodes A) ⟩ ]
                   (p ≡ pr (fst x) (fst (valOf x m))) ∥₁
    pairs-out = G.F-out

-- SEALED: the key of a formula is a pair whose first component is
-- the arity numeral.  Read here once, at variables, so no consumer
-- unfolds `keyS`.
opaque
  key-arity : (A : CS.S) {n : ℕ} (ψ : Formula ⟪ fst A ⟫ n) (ar t : V ℓ)
            → fst (keyS A ψ) ≡ pr ar t → ar ≡ # n
  key-arity A ψ ar t e = sym (pr-inj e .fst)

module At (c : V ℓ) (oc : IsOrd c) where

  A : CS.S
  A = LsetS c oc

  cL : ⟨ isL c ⟩
  cL = Lset→isL (sucV c) (suc-ord oc) c (ord∈Lset-suc c oc)

  hier : CS.S
  hier = hierL c cL oc

  codes : CS.S
  codes = AllCodes A

  table : CS.S
  table = SatMap.pairs A

  tower : CS.S
  tower = EnvTower.tower A

-- The four witnesses at c lie in K, at whatever proof of ordinality.
Witnesses : V ℓ → V ℓ → Type (ℓ-suc ℓ)
Witnesses K c = (oc : IsOrd c)
  → ⟨ fst (At.hier c oc) ∈ K ⟩
  × ⟨ fst (At.codes c oc) ∈ K ⟩
  × ⟨ fst (At.table c oc) ∈ K ⟩
  × ⟨ fst (At.tower c oc) ∈ K ⟩

isPropWitnesses : (K c : V ℓ) → isProp (Witnesses K c)
isPropWitnesses K c = isPropΠ λ oc →
  isProp× (snd (fst (At.hier c oc) ∈ K))
    (isProp× (snd (fst (At.codes c oc) ∈ K))
      (isProp× (snd (fst (At.table c oc) ∈ K)) (snd (fst (At.tower c oc) ∈ K))))

-- ADEQUACY.  γ is an ordinal closed under successor, holds ω, and
-- Lset γ holds the four witnesses of every c ∈ γ.
Adequate : V ℓ → Type (ℓ-suc ℓ)
Adequate γ =
    IsOrd γ
  × ((x : V ℓ) → ⟨ x ∈ γ ⟩ → ⟨ sucV x ∈ γ ⟩)
  × ⟨ ω ∈ γ ⟩
  × ((c : V ℓ) → ⟨ c ∈ γ ⟩ → Witnesses (Lset γ) c)

isPropAdequate : (γ : V ℓ) → isProp (Adequate γ)
isPropAdequate γ =
  isProp× (isPropIsOrd γ)
    (isProp× (isPropΠ λ x → isPropΠ λ _ → snd (sucV x ∈ γ))
      (isProp× (snd (ω ∈ γ))
        (isPropΠ λ c → isPropΠ λ _ → isPropWitnesses (Lset γ) c)))

module Adequate (γ : V ℓ) (ad : Adequate γ) where
  ord = ad .fst
  succ = ad .snd .fst
  ω∈ = ad .snd .snd .fst
  wit = ad .snd .snd .snd
```

```agda
-- =====================================================================
-- SECTION 3.  AN ADEQUATE STAGE ABOVE ANY ORDINAL.  One step bounds
-- the birth stages of the witnesses of every member of α, the
-- successors of the members, α itself and ω (src/L/Ordinal.lagda.md
-- `boundingOrd`, `bound2`); ω steps from p+1 and the union of the chain
-- is adequate: a member of the union is a member of some step, and
-- whatever that step owes is in the next.
-- =====================================================================

-- The members of a set as a family of stages, and the union of a chain.
private
  ι : (α : V ℓ) → ⟪ α ⟫ → V ℓ
  ι α = ⟪ α ⟫↪

  ι∈ : (α : V ℓ) (m : ⟪ α ⟫) → ⟨ ι α m ∈ α ⟩
  ι∈ α m = ∈∈ₛ {a = ι α m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)

  -- Membership in an ordinal is transitive, spelled at the values.
  tr : (β : V ℓ) → IsOrd β → (x y : V ℓ) → ⟨ x ∈ β ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ β ⟩
  tr β oβ x y x∈ y∈ = oβ .fst {x = x} {y = y} y∈ x∈

-- ONE STEP.
module Bound1 (α : V ℓ) (oα : IsOrd α) where

  private
    W : ⟪ α ⟫ → (c : V ℓ) → IsOrd c → CS.S → V ℓ
    W m c oc s = stage (fst s) (snd s)

    oc : (m : ⟪ α ⟫) → IsOrd (ι α m)
    oc m = mem-ord {A = α} oα (ι α m) (ι∈ α m)

    st : (f : (c : V ℓ) (o : IsOrd c) → CS.S) → ⟪ α ⟫ → V ℓ
    st f m = stage (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))

    st-ord : (f : (c : V ℓ) (o : IsOrd c) → CS.S) (m : ⟪ α ⟫) → IsOrd (st f m)
    st-ord f m = stage-ord (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))

    b1 = boundingOrd ⟪ α ⟫ (st At.hier) (st-ord At.hier)
    b2 = boundingOrd ⟪ α ⟫ (st At.codes) (st-ord At.codes)
    b3 = boundingOrd ⟪ α ⟫ (st At.table) (st-ord At.table)
    b4 = boundingOrd ⟪ α ⟫ (st At.tower) (st-ord At.tower)
    b5 = boundingOrd ⟪ α ⟫ (λ m → sucV (ι α m)) (λ m → suc-ord (oc m))
    b6 = bound2 α ω oα ω-ord
    b7 = bound2 (b1 .fst) (b2 .fst) (b1 .snd .fst) (b2 .snd .fst)
    b8 = bound2 (b3 .fst) (b4 .fst) (b3 .snd .fst) (b4 .snd .fst)
    b9 = bound2 (b5 .fst) (b6 .fst) (b5 .snd .fst) (b6 .snd .fst)
    b10 = bound2 (b7 .fst) (b8 .fst) (b7 .snd .fst) (b8 .snd .fst)
    b11 = bound2 (b9 .fst) (b10 .fst) (b9 .snd .fst) (b10 .snd .fst)

  β : V ℓ
  β = b11 .fst

  oβ : IsOrd β
  oβ = b11 .snd .fst

  private
    b9∈ : ⟨ b9 .fst ∈ β ⟩
    b9∈ = b11 .snd .snd .fst
    b10∈ : ⟨ b10 .fst ∈ β ⟩
    b10∈ = b11 .snd .snd .snd
    b5∈ : ⟨ b5 .fst ∈ β ⟩
    b5∈ = tr β oβ (b9 .fst) (b5 .fst) b9∈ (b9 .snd .snd .fst)
    b6∈ : ⟨ b6 .fst ∈ β ⟩
    b6∈ = tr β oβ (b9 .fst) (b6 .fst) b9∈ (b9 .snd .snd .snd)
    b7∈ : ⟨ b7 .fst ∈ β ⟩
    b7∈ = tr β oβ (b10 .fst) (b7 .fst) b10∈ (b10 .snd .snd .fst)
    b8∈ : ⟨ b8 .fst ∈ β ⟩
    b8∈ = tr β oβ (b10 .fst) (b8 .fst) b10∈ (b10 .snd .snd .snd)
    b1∈ : ⟨ b1 .fst ∈ β ⟩
    b1∈ = tr β oβ (b7 .fst) (b1 .fst) b7∈ (b7 .snd .snd .fst)
    b2∈ : ⟨ b2 .fst ∈ β ⟩
    b2∈ = tr β oβ (b7 .fst) (b2 .fst) b7∈ (b7 .snd .snd .snd)
    b3∈ : ⟨ b3 .fst ∈ β ⟩
    b3∈ = tr β oβ (b8 .fst) (b3 .fst) b8∈ (b8 .snd .snd .fst)
    b4∈ : ⟨ b4 .fst ∈ β ⟩
    b4∈ = tr β oβ (b8 .fst) (b4 .fst) b8∈ (b8 .snd .snd .snd)

  α∈β : ⟨ α ∈ β ⟩
  α∈β = tr β oβ (b6 .fst) α b6∈ (b6 .snd .snd .fst)

  ω∈β : ⟨ ω ∈ β ⟩
  ω∈β = tr β oβ (b6 .fst) ω b6∈ (b6 .snd .snd .snd)

  suc∈β : (x : V ℓ) → ⟨ x ∈ α ⟩ → ⟨ sucV x ∈ β ⟩
  suc∈β x x∈ = subst (λ u → ⟨ sucV u ∈ β ⟩) (fib .snd)
    (tr β oβ (b5 .fst) (sucV (ι α (fib .fst))) b5∈ (b5 .snd .snd (fib .fst)))
    where
    fib : Σ[ m ∈ ⟪ α ⟫ ] (ι α m ≡ x)
    fib = ∈-asFiber {a = x} {b = α} x∈

  private
    -- A witness at an indexed member lies in Lset β, through its stage
    -- and the bound of the stages.
    land : (f : (c : V ℓ) (o : IsOrd c) → CS.S)
           (b : Σ[ σ ∈ V ℓ ] (IsOrd σ × ((m : ⟪ α ⟫) → ⟨ st f m ∈ σ ⟩)))
         → ⟨ b .fst ∈ β ⟩
         → (m : ⟪ α ⟫) → ⟨ fst (f (ι α m) (oc m)) ∈ Lset β ⟩
    land f b b∈ m =
      Lset-mono {α = β} {β = b .fst} b∈
        (Lset-mono {α = b .fst} {β = st f m} (b .snd .snd m)
          (stage-mem (fst (f (ι α m) (oc m))) (snd (f (ι α m) (oc m)))))

    -- At the indexed member, at any proof of its ordinality.
    witAt : (m : ⟪ α ⟫) → Witnesses (Lset β) (ι α m)
    witAt m o =
        subst (λ u → ⟨ fst (At.hier (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
          (land At.hier b1 b1∈ m)
      , ( subst (λ u → ⟨ fst (At.codes (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
            (land At.codes b2 b2∈ m)
        , ( subst (λ u → ⟨ fst (At.table (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
              (land At.table b3 b3∈ m)
          , subst (λ u → ⟨ fst (At.tower (ι α m) u) ∈ Lset β ⟩) (isPropIsOrd (ι α m) (oc m) o)
              (land At.tower b4 b4∈ m) ))

  wit : (c : V ℓ) → ⟨ c ∈ α ⟩ → Witnesses (Lset β) c
  wit c c∈ = subst (Witnesses (Lset β)) (fib .snd) (witAt (fib .fst))
    where
    fib : Σ[ m ∈ ⟪ α ⟫ ] (ι α m ≡ c)
    fib = ∈-asFiber {a = c} {b = α} c∈

-- THE UNION OF AN ω-CHAIN OF ORDINALS, with its two membership
-- directions.  The chain is any family; the consumers below supply
-- one whose every step lies in the next.
module Union (ch : ℕ → V ℓ) (och : (n : ℕ) → IsOrd (ch n)) where

  private
    F : Lift {ℓ-zero} {ℓ} ℕ → V ℓ
    F n = ch (lower n)

  γ : V ℓ
  γ = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) F)

  oγ : IsOrd γ
  oγ = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) F (λ n → och (lower n))

  into : (n : ℕ) (x : V ℓ) → ⟨ x ∈ ch n ⟩ → ⟨ x ∈ γ ⟩
  into n x x∈ = ∈∈ₛ {a = x} {b = γ} .snd
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .snd
      ∣ ch n , ( ∈∈ₛ {a = ch n} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .fst ∣ lift n , refl ∣₁
               , ∈∈ₛ {a = x} {b = ch n} .fst x∈ ) ∣₁)

  outof : (x : V ℓ) → ⟨ x ∈ γ ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ ch n ⟩ ∥₁
  outof x x∈ = PT.rec squash₁ go
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .fst (∈∈ₛ {a = x} {b = γ} .fst x∈))
    where
    go : Σ[ w ∈ V ℓ ] (⟨ w ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) F ⟩ × ⟨ x ∈ₛ w ⟩)
       → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ ch n ⟩ ∥₁
    go (w , (w∈ , x∈w)) = PT.map
      (λ { (n , q) → lower n
         , ∈∈ₛ {a = x} {b = ch (lower n)} .snd (subst (λ u → ⟨ x ∈ₛ u ⟩) (sym q) x∈w) })
      (∈∈ₛ {a = w} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .snd w∈)

-- THE STAGE ABOVE p.
module Above (p : V ℓ) (op : IsOrd p) where

  private
    base = bound2 p ω op ω-ord

  ch : ℕ → Σ[ β ∈ V ℓ ] IsOrd β
  ch zero = base .fst , base .snd .fst
  ch (suc n) = Bound1.β (ch n .fst) (ch n .snd) , Bound1.oβ (ch n .fst) (ch n .snd)

  module C = Union (λ n → ch n .fst) (λ n → ch n .snd)

  γ : V ℓ
  γ = C.γ

  oγ : IsOrd γ
  oγ = C.oγ

  private
    up : (n : ℕ) → ⟨ ch n .fst ∈ ch (suc n) .fst ⟩
    up n = Bound1.α∈β (ch n .fst) (ch n .snd)

    ch∈γ : (n : ℕ) → ⟨ ch n .fst ∈ γ ⟩
    ch∈γ n = C.into (suc n) (ch n .fst) (up n)

  p∈γ : ⟨ p ∈ γ ⟩
  p∈γ = C.into zero p (base .snd .snd .fst)

  ω∈γ : ⟨ ω ∈ γ ⟩
  ω∈γ = C.into zero ω (base .snd .snd .snd)

  succ : (x : V ℓ) → ⟨ x ∈ γ ⟩ → ⟨ sucV x ∈ γ ⟩
  succ x x∈ = PT.rec (snd (sucV x ∈ γ))
    (λ { (n , x∈n) → C.into (suc n) (sucV x) (Bound1.suc∈β (ch n .fst) (ch n .snd) x x∈n) })
    (C.outof x x∈)

  wit : (c : V ℓ) → ⟨ c ∈ γ ⟩ → Witnesses (Lset γ) c
  wit c c∈ = PT.rec (isPropWitnesses (Lset γ) c)
    (λ { (n , c∈n) → λ oc →
      let w = Bound1.wit (ch n .fst) (ch n .snd) c c∈n oc
          mono = Lset-mono {α = γ} {β = ch (suc n) .fst} (ch∈γ (suc n))
      in mono (w .fst) , ( mono (w .snd .fst) , ( mono (w .snd .snd .fst) , mono (w .snd .snd .snd) )) })
    (C.outof c c∈)

  adequate : Adequate γ
  adequate = oγ , ( succ , ( ω∈γ , wit ))

adequate-above : (p : V ℓ) → IsOrd p
               → Σ[ γ ∈ V ℓ ] (IsOrd γ × ⟨ p ∈ γ ⟩ × Adequate γ)
adequate-above p op = Above.γ p op , ( Above.oγ p op , ( Above.p∈γ p op , Above.adequate p op ))
```

```agda
-- =====================================================================
-- SECTION 4.  SUPERADEQUACY.  λ is superadequate when every member
-- lies in an adequate member.  Iterating `adequate-above` ω times from
-- α and taking the union gives a stage that is adequate and
-- superadequate at once: a member of the union lies in some step, and
-- every step is adequate and lies in the next.
--
-- NOTE.  src/L/Ordinal.lagda.md:205-213 `IsLimit` asks closure under
-- EVERY small-indexed union.  No ω-union has that property: the chain
-- itself, indexed by ℕ, is a small family in the union whose union is
-- the union.  So the stage below is delivered with the two closure
-- facts an ω-union does have (successor closure, and ω as a member),
-- as `Adequate` states them, and not with `IsLimit`.
-- =====================================================================

Superadequate : V ℓ → Type (ℓ-suc ℓ)
Superadequate lam = (d : V ℓ) → ⟨ d ∈ lam ⟩
  → ∥ Σ[ γ ∈ V ℓ ] (⟨ γ ∈ lam ⟩ × ⟨ d ∈ γ ⟩ × Adequate γ) ∥₁

module Super (α : V ℓ) (oα : IsOrd α) where

  ch : ℕ → Σ[ γ ∈ V ℓ ] (IsOrd γ × Adequate γ)
  ch zero =
    adequate-above α oα .fst
    , ( adequate-above α oα .snd .fst , adequate-above α oα .snd .snd .snd )
  ch (suc n) =
    adequate-above (ch n .fst) (ch n .snd .fst) .fst
    , ( adequate-above (ch n .fst) (ch n .snd .fst) .snd .fst
      , adequate-above (ch n .fst) (ch n .snd .fst) .snd .snd .snd )

  module U = Union (λ n → ch n .fst) (λ n → ch n .snd .fst)

  lam : V ℓ
  lam = U.γ

  olam : IsOrd lam
  olam = U.oγ

  private
    up : (n : ℕ) → ⟨ ch n .fst ∈ ch (suc n) .fst ⟩
    up n = adequate-above (ch n .fst) (ch n .snd .fst) .snd .snd .fst

    ch∈λ : (n : ℕ) → ⟨ ch n .fst ∈ lam ⟩
    ch∈λ n = U.into (suc n) (ch n .fst) (up n)

  α∈λ : ⟨ α ∈ lam ⟩
  α∈λ = U.into zero α (adequate-above α oα .snd .snd .fst)

  succ : (x : V ℓ) → ⟨ x ∈ lam ⟩ → ⟨ sucV x ∈ lam ⟩
  succ x x∈ = PT.rec (snd (sucV x ∈ lam))
    (λ { (n , x∈n) → U.into n (sucV x) (Adequate.succ (ch n .fst) (ch n .snd .snd) x x∈n) })
    (U.outof x x∈)

  ω∈λ : ⟨ ω ∈ lam ⟩
  ω∈λ = U.into zero ω (Adequate.ω∈ (ch zero .fst) (ch zero .snd .snd))

  wit : (c : V ℓ) → ⟨ c ∈ lam ⟩ → Witnesses (Lset lam) c
  wit c c∈ = PT.rec (isPropWitnesses (Lset lam) c)
    (λ { (n , c∈n) → λ oc →
      let w = Adequate.wit (ch n .fst) (ch n .snd .snd) c c∈n oc
      in  Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .fst)
        , ( Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .fst)
          , ( Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .snd .fst)
            , Lset-mono {α = lam} {β = ch n .fst} (ch∈λ n) (w .snd .snd .snd) )) })
    (U.outof c c∈)

  adequate : Adequate lam
  adequate = olam , ( succ , ( ω∈λ , wit ))

  super : Superadequate lam
  super d d∈ = PT.map
    (λ { (n , d∈n) → ch n .fst , ( ch∈λ n , ( d∈n , ch n .snd .snd )) })
    (U.outof d d∈)

superadequate-above : (α : V ℓ) → IsOrd α
                    → Σ[ lam ∈ V ℓ ] (IsOrd lam × ⟨ α ∈ lam ⟩ × Adequate lam × Superadequate lam)
superadequate-above α oα =
  Super.lam α oα , ( Super.olam α oα , ( Super.α∈λ α oα , ( Super.adequate α oα , Super.super α oα )))
```

```agda
-- =====================================================================
-- SECTION 5.  THE CLOSURE FACTS AT AN ADEQUATE STAGE.  K = Lset λ is
-- transitive, closed under pairs and successor, holds every numeral,
-- ω, every ordinal below λ and every stage below λ; O = ω holds exactly
-- the numerals.  Together: the `KC` product of src/L/GCH/Level.lagda.md
-- at (Lset λ, ω).
-- =====================================================================

-- A stage is a member of the next stage: it is the definable subset
-- of itself that ⊤̇ carves out.
Lset∈suc : (β : V ℓ) → ⟨ Lset β ∈ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

module Closed (lam : V ℓ) (ad : Adequate lam) where

  open Adequate lam ad public

  ∅∈λ : ⟨ ∅ ∈ lam ⟩
  ∅∈λ = tr lam ord ω ∅ ω∈ (#∈ω zero)

  module B = Bound lam ord succ ∅∈λ

  K : V ℓ
  K = Lset lam

  InK : V ℓ → Type (ℓ-suc ℓ)
  InK x = ⟨ x ∈ K ⟩

  transK : (x y : V ℓ) → InK x → ⟨ y ∈ x ⟩ → InK y
  transK x y xK y∈x = Lset-trans′ lam {x = x} {y = y} y∈x xK

  -- The successor of a member of K lies in K: sucV a = ⋃ ⁅ a , ⁅ a ⁆s ⁆
  -- climbs three stages above the stage that holds a (the shape of
  -- src/L/Coding/EnvSupply.lagda.md:204).
  sucK : (a : V ℓ) → InK a → InK (sucV a)
  sucK a a∈ = PT.rec (snd (sucV a ∈ K)) step (Lset-out′ lam a a∈)
    where
    step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ lam ⟩ × ⟨ a ∈ Lset (sucV δ) ⟩) → InK (sucV a)
    step (δ , (δ∈ , a∈δ₁)) = Lset-mono {α = lam} {β = sucV δ₃} δ₄∈λ sucV∈
      where
      δ₁ = sucV δ
      δ₂ = sucV (sucV δ)
      δ₃ = sucV (sucV (sucV δ))
      δ₄∈λ : ⟨ sucV δ₃ ∈ lam ⟩
      δ₄∈λ = succ δ₃ (succ δ₂ (succ δ₁ (succ δ δ∈)))
      a∈δ₂ : ⟨ a ∈ Lset δ₂ ⟩
      a∈δ₂ = Lset-mono {α = δ₂} {β = δ₁} (self∈sucV δ₁) a∈δ₁
      sgl∈δ₂ : ⟨ ⁅ a ⁆s ∈ Lset δ₂ ⟩
      sgl∈δ₂ = sgl∈Lset-suc δ₁ a a∈δ₁
      pair∈δ₃ : ⟨ ⁅ a , ⁅ a ⁆s ⁆ ∈ Lset δ₃ ⟩
      pair∈δ₃ = pair∈Lset-suc δ₂ a ⁅ a ⁆s a∈δ₂ sgl∈δ₂
      sucV∈ : ⟨ sucV a ∈ Lset (sucV δ₃) ⟩
      sucV∈ = union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃

  ord∈K : (c : V ℓ) → ⟨ c ∈ lam ⟩ → InK c
  ord∈K c c∈ = Lset-mono {α = lam} {β = sucV c} (succ c c∈)
    (ord∈Lset-suc c (mem-ord {A = lam} ord c c∈))

  Lset∈K : (c : V ℓ) → ⟨ c ∈ lam ⟩ → InK (Lset c)
  Lset∈K c c∈ = Lset-mono {α = lam} {β = sucV c} (succ c c∈) (Lset∈suc c)

  ω∈K : InK ω
  ω∈K = ord∈K ω ω∈

  numO : (k : ℕ) → ⟨ fst (numeralL k) ∈ ω ⟩
  numO k = subst (λ u → ⟨ u ∈ ω ⟩) (sym (numeralL-fst k)) (#∈ω k)

  O-num : (x : V ℓ) → ⟨ x ∈ ω ⟩ → ∥ Σ[ k ∈ ℕ ] (x ≡ fst (numeralL k)) ∥₁
  O-num x x∈ = PT.map (λ { (k , q) → lower k , q })
    (subst ⟨_⟩ (ω-specL (down ωʟ x x∈)) x∈)

  kc : KC K ω
  kc = transK
     , ( B.prʟ∈λ
     , ( (λ a → sucK (fst a))
     , ( B.num∈λ
     , ( numO
     , ( O-num
     , ω∈K )))))
```

```agda
-- =====================================================================
-- SECTION 6.  THE COMPLETENESS FRAME.  The step, the approximation and
-- the graph hold at the hierarchy table, exactly as src/L/GCH/Level
-- .lagda.md `Sound4` reads them, with the definable-powerset row
-- supplied by ONE hypothesis, `DefComplete`, stated at the strongest
-- site facts available: the bound is Lset λ for an adequate λ, the
-- numeral slot is ω, the tags are the numerals, the carrier is Lset c
-- for c ∈ λ, and d is its definable powerset.  Everything the row's
-- bounded quantifiers reach is then in Lset λ by `Adequate` and the
-- closures of Section 5.
-- =====================================================================

DefComplete : Type (ℓ-suc ℓ)
DefComplete =
  ∀ {m} (d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
    (γ : CS.S ^ m)
  → (lam : V ℓ) → Adequate lam
  → fst (lookup K γ) ≡ Lset lam
  → fst (lookup O γ) ≡ ω
  → Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
  → (c : V ℓ) (oc : IsOrd c) → ⟨ c ∈ lam ⟩
  → fst (lookup w γ) ≡ Lset c
  → fst (lookup d γ) ≡ 𝒟ₒ (Lset c)
  → ⟨ γ ⊨ DefV.defAt d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩

-- One bounded existential over the last slot, introduced.  The mirror
-- of src/L/GCH/Sound.lagda.md `unwrap`.
wrap-in : {n : ℕ} (φ : Formula CS.S (suc (suc n))) (γ : CS.S ^ (suc n)) (x : CS.S)
        → ⟨ fst x ∈ fst (lookup (W3.lastFin {n}) γ) ⟩ → ⟨ (x ∷ γ) ⊨ φ ⟩
        → ⟨ γ ⊨ W3.wrap {n} φ ⟩
wrap-in φ γ x m h = ∣ x , (m , h) ∣₁

module Complete4 (dc : DefComplete) where

  -- THE STEP at (v, b, f): v = Lset b, b ∈ λ, f a table that is correct
  -- and complete on b (src/L/Hierarchy.lagda.md `Values`, `Entries`).
  module Step {m : ℕ} (v b f K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
              (γ : CS.S ^ m)
              (lam : V ℓ) (ad : Adequate lam)
              (Kq : fst (lookup K γ) ≡ Lset lam)
              (Oq : fst (lookup O γ) ≡ ω)
              (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
              (ob : IsOrd (fst (lookup b γ)))
              (b∈λ : ⟨ fst (lookup b γ) ∈ lam ⟩)
              (vq : fst (lookup v γ) ≡ Lset (fst (lookup b γ)))
              (vals : Values (lookup f γ) (fst (lookup b γ)))
              (ents : Entries (lookup f γ) (fst (lookup b γ))) where

    module SV = StepV {m} v b f K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
    module Cl = Closed lam ad

    private
      Kv Bv Fv Vv : V ℓ
      Kv = fst (lookup K γ)
      Bv = fst (lookup b γ)
      Fv = fst (lookup f γ)
      Vv = fst (lookup v γ)

      InK : V ℓ → Type (ℓ-suc ℓ)
      InK x = ⟨ x ∈ Kv ⟩

      toK : (x : V ℓ) → ⟨ x ∈ Lset lam ⟩ → InK x
      toK x h = subst (λ u → ⟨ x ∈ u ⟩) (sym Kq) h

      δ∈λ : (δ : V ℓ) → ⟨ δ ∈ Bv ⟩ → ⟨ δ ∈ lam ⟩
      δ∈λ δ δ∈ = tr lam Cl.ord Bv δ b∈λ δ∈

    -- SOUNDNESS HALF: a member x of Lset b lies in 𝒟ₒ (Lset δ) for some
    -- δ ∈ b; the table records (δ, Lset δ); d = Lset (δ+1) is that
    -- definable powerset, in K, and x ∈ d.
    into : ⟨ γ ⊨ SV.intoAt ⟩
    into x x∈v = PT.rec (snd P) put
      (Lset-out Bv (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) vq x∈v))
      where
      P : hProp (ℓ-suc ℓ)
      P = (x ∷ γ) ⊨ ∃̇∈ (var (sh1 b)) (∃̇∈ (var (sh2 K)) (∃̇∈ (var (sh3 K))
            ( appAt (sh4 f) i2 i1
            ∧̇ ( DefV.defAt {4 + m} i0 i1 (sh4 O) (sh4 K)
                  (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
                  (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11)
              ∧̇ (var i3 ∈̇ var i0) ))))

      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ Bv ⟩ × ⟨ fst x ∈ 𝒟ₒ (Lset δ) ⟩) → ⟨ P ⟩
      put (δ , (δ∈b , x∈D)) =
        ∣ cS , ( δ∈b , ∣ wS , ( wK , ∣ dS , ( dK , ( ha , ( hd , x∈d ))) ∣₁ ) ∣₁ ) ∣₁
        where
        oδ : IsOrd δ
        oδ = mem-ord {A = Bv} ob δ δ∈b
        cS wS dS : CS.S
        cS = down (lookup b γ) δ δ∈b
        wS = LsetS δ oδ
        dS = LsetS (sucV δ) (suc-ord oδ)
        δλ : ⟨ δ ∈ lam ⟩
        δλ = δ∈λ δ δ∈b
        wK : InK (Lset δ)
        wK = toK (Lset δ) (Cl.Lset∈K δ δλ)
        dK : InK (Lset (sucV δ))
        dK = toK (Lset (sucV δ)) (Cl.Lset∈K (sucV δ) (Cl.succ δ δλ))
        ha : ⟨ (dS ∷ wS ∷ cS ∷ x ∷ γ) ⊨ appAt (sh4 f) i2 i1 ⟩
        ha = app-in (sh4 f) i2 i1 (dS ∷ wS ∷ cS ∷ x ∷ γ) (ents cS δ∈b)
        hd : ⟨ (dS ∷ wS ∷ cS ∷ x ∷ γ) ⊨ DefV.defAt {4 + m} i0 i1 (sh4 O) (sh4 K)
                  (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
                  (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11) ⟩
        hd = dc {4 + m} i0 i1 (sh4 O) (sh4 K)
               (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
               (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11)
               (dS ∷ wS ∷ cS ∷ x ∷ γ) lam ad Kq Oq
               (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (wS ∷ cS ∷ x ∷ γ) dS
                 (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (cS ∷ x ∷ γ) wS
                   (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (x ∷ γ) cS
                     (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ x tags))))
               δ oδ δλ refl (Lset-suc δ)
        x∈d : ⟨ fst x ∈ Lset (sucV δ) ⟩
        x∈d = subst (λ u → ⟨ fst x ∈ u ⟩) (sym (Lset-suc δ)) x∈D

    -- COMPLETENESS HALF: a recorded (c, w) with c ∈ b has w = Lset c;
    -- d = Lset (c+1) is its definable powerset, in K, and d ⊆ Lset b.
    over : ⟨ γ ⊨ SV.overAt ⟩
    over c c∈b w wK ha = ∣ dS , ( dK , ( hd , sub )) ∣₁
      where
      rec : ⟨ pr (fst c) (fst w) ∈ Fv ⟩
      rec = app-out (sh2 f) i1 i0 (w ∷ c ∷ γ) ha
      wq : fst w ≡ Lset (fst c)
      wq = vals c w c∈b rec
      oc : IsOrd (fst c)
      oc = mem-ord {A = Bv} ob (fst c) c∈b
      cλ : ⟨ fst c ∈ lam ⟩
      cλ = δ∈λ (fst c) c∈b
      dS : CS.S
      dS = LsetS (sucV (fst c)) (suc-ord oc)
      dK : InK (Lset (sucV (fst c)))
      dK = toK (Lset (sucV (fst c))) (Cl.Lset∈K (sucV (fst c)) (Cl.succ (fst c) cλ))
      hd : ⟨ (dS ∷ w ∷ c ∷ γ) ⊨ DefV.defAt {3 + m} i0 i1 (sh3 O) (sh3 K)
                (sh3 N0) (sh3 N1) (sh3 N2) (sh3 N3) (sh3 N4) (sh3 N5)
                (sh3 N6) (sh3 N7) (sh3 N8) (sh3 N9) (sh3 N10) (sh3 N11) ⟩
      hd = dc {3 + m} i0 i1 (sh3 O) (sh3 K)
             (sh3 N0) (sh3 N1) (sh3 N2) (sh3 N3) (sh3 N4) (sh3 N5)
             (sh3 N6) (sh3 N7) (sh3 N8) (sh3 N9) (sh3 N10) (sh3 N11)
             (dS ∷ w ∷ c ∷ γ) lam ad Kq Oq
             (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (w ∷ c ∷ γ) dS
               (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (c ∷ γ) w
                 (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ c tags)))
             (fst c) oc cλ wq (Lset-suc (fst c))
      sub : (y : CS.S) → ⟨ fst y ∈ fst dS ⟩ → ⟨ fst y ∈ Vv ⟩
      sub y y∈ = subst (λ u → ⟨ fst y ∈ u ⟩) (sym vq)
        (Lset-in Bv (fst c) (fst y) c∈b
          (subst (λ u → ⟨ fst y ∈ u ⟩) (Lset-suc (fst c)) y∈))

    step : ⟨ γ ⊨ SV.stepAt ⟩
    step = into , over

  -- THE APPROXIMATION at (f, a): f the hierarchy table on the ordinal
  -- a ∈ λ.  Its domain is a, and every recorded pair is a step.
  module Approx {m : ℕ} (f a K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
                (γ : CS.S ^ m)
                (lam : V ℓ) (ad : Adequate lam)
                (Kq : fst (lookup K γ) ≡ Lset lam)
                (Oq : fst (lookup O γ) ≡ ω)
                (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
                (oa : IsOrd (fst (lookup a γ)))
                (a∈λ : ⟨ fst (lookup a γ) ∈ lam ⟩)
                (sp : IsHier (fst (lookup a γ)) (lookup f γ)) where

    module AV = ApproxV {m} f a K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
    module Cl = Closed lam ad

    private
      Kv Av Fv : V ℓ
      Kv = fst (lookup K γ)
      Av = fst (lookup a γ)
      Fv = fst (lookup f γ)

      InK : V ℓ → Type (ℓ-suc ℓ)
      InK x = ⟨ x ∈ Kv ⟩

      toK : (x : V ℓ) → ⟨ x ∈ Lset lam ⟩ → InK x
      toK x h = subst (λ u → ⟨ x ∈ u ⟩) (sym Kq) h

      hout : (c z : CS.S) → ⟨ pr (fst c) (fst z) ∈ Fv ⟩
           → ⟨ fst c ∈ Av ⟩ × (fst z ≡ Lset (fst c))
      hout = hier-out Av oa (lookup f γ) sp

      hin : (c : CS.S) → ⟨ fst c ∈ Av ⟩ → ⟨ pr (fst c) (Lset (fst c)) ∈ Fv ⟩
      hin = hier-in Av oa (lookup f γ) sp

    dom : ⟨ γ ⊨ domB f a K ⟩
    dom c cK =
        (λ h → PT.rec (snd (fst c ∈ Av))
                 (λ { (z , (zK , ap)) → hout c z (app-out (sh2 f) i1 i0 (z ∷ c ∷ γ) ap) .fst })
                 h)
      , (λ c∈a → ∣ LsetS (fst c) (oc c∈a)
                  , ( toK (Lset (fst c)) (Cl.Lset∈K (fst c) (tr lam Cl.ord Av (fst c) a∈λ c∈a))
                    , app-in (sh2 f) i1 i0 (LsetS (fst c) (oc c∈a) ∷ c ∷ γ) (hin c c∈a) ) ∣₁)
      where
      oc : ⟨ fst c ∈ Av ⟩ → IsOrd (fst c)
      oc c∈a = mem-ord {A = Av} oa (fst c) c∈a

    steps : ⟨ γ ⊨ ∀̇∈ (var K) (∀̇∈ (var (sh1 K))
                (appAt (sh2 f) i1 i0
                ⇒̇ StepV.stepAt {2 + m} i0 i1 (sh2 f) (sh2 K) (sh2 O)
                     (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                     (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11))) ⟩
    steps c cK w wK ha = St.step
      where
      rec : ⟨ pr (fst c) (fst w) ∈ Fv ⟩
      rec = app-out (sh2 f) i1 i0 (w ∷ c ∷ γ) ha
      c∈a : ⟨ fst c ∈ Av ⟩
      c∈a = hout c w rec .fst
      wq : fst w ≡ Lset (fst c)
      wq = hout c w rec .snd
      oc : IsOrd (fst c)
      oc = mem-ord {A = Av} oa (fst c) c∈a
      vals : Values (lookup f γ) (fst c)
      vals c' z _ p = hout c' z p .snd
      ents : Entries (lookup f γ) (fst c)
      ents c' c'∈c = hin c' (oa .fst {x = fst c} {y = fst c'} c'∈c c∈a)
      module St = Step {2 + m} i0 i1 (sh2 f) (sh2 K) (sh2 O)
                    (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                    (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
                    (w ∷ c ∷ γ) lam ad Kq Oq
                    (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (c ∷ γ) w
                      (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ c tags))
                    oc (tr lam Cl.ord Av (fst c) a∈λ c∈a) wq vals ents

    approx : ⟨ γ ⊨ AV.approxAt ⟩
    approx = dom , steps

  -- THE GRAPH at (w, b): w = Lset b, b ∈ λ; the witness is the
  -- hierarchy table on b, in K by adequacy.
  module Graph {m : ℕ} (w b K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
               (γ : CS.S ^ m)
               (lam : V ℓ) (ad : Adequate lam)
               (Kq : fst (lookup K γ) ≡ Lset lam)
               (Oq : fst (lookup O γ) ≡ ω)
               (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
               (ob : IsOrd (fst (lookup b γ)))
               (b∈λ : ⟨ fst (lookup b γ) ∈ lam ⟩)
               (wq : fst (lookup w γ) ≡ Lset (fst (lookup b γ))) where

    module GV = GraphV {m} w b K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
    module Cl = Closed lam ad

    private
      Bv : V ℓ
      Bv = fst (lookup b γ)

      F : CS.S
      F = At.hier Bv ob

      sp : IsHier Bv F
      sp = hierL-spec Bv (At.cL Bv ob) ob

      fK : ⟨ fst F ∈ fst (lookup K γ) ⟩
      fK = subst (λ u → ⟨ fst F ∈ u ⟩) (sym Kq) (Cl.wit Bv b∈λ ob .fst)

    graph : ⟨ γ ⊨ GV.graphAt ⟩
    graph = ∣ F , ( fK , ( Ap.approx , St.step )) ∣₁
      where
      tags' = tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ F tags
      vals : Values F Bv
      vals c z _ p = hier-out Bv ob F sp c z p .snd
      ents : Entries F Bv
      ents c c∈ = hier-in Bv ob F sp c c∈
      module Ap = Approx {1 + m} i0 (sh1 b) (sh1 K) (sh1 O)
                    (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                    (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11)
                    (F ∷ γ) lam ad Kq Oq tags' ob b∈λ sp
      module St = Step {1 + m} (sh1 w) (sh1 b) i0 (sh1 K) (sh1 O)
                    (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                    (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11)
                    (F ∷ γ) lam ad Kq Oq tags' ob b∈λ wq vals ents

  -- THE MATRIX at the sixteen-slot environment: the twelve numerals,
  -- ω, Lset p, p and Lset λ.
  module Finish (lam : V ℓ) (ad : Adequate lam)
                (p : V ℓ) (op : IsOrd p) (p∈λ : ⟨ p ∈ lam ⟩) where

    open W3V
    module Cl = Closed lam ad

    aS pS zS : CS.S
    aS = LsetS p op
    pS = p , At.cL p op
    zS = LsetS lam Cl.ord

    E : CS.S ^ 16
    E = numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
      ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
      ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11
      ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []

    tags : Tags n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 E
    tags = record
      { t0 = refl ; t1 = refl ; t2 = refl ; t3 = refl
      ; t4 = refl ; t5 = refl ; t6 = refl ; t7 = refl
      ; t8 = refl ; t9 = refl ; t10 = refl ; t11 = refl }

    private
      -- A numeral's successor is the next numeral.
      nsuc : (k : ℕ) → fst (numeralL (suc k)) ≡ sucV (fst (numeralL k))
      nsuc k = numeralL-fst (suc k) ∙ cong sucV (sym (numeralL-fst k))

      sucTag : (i j : Fin 16) (k : ℕ)
             → fst (lookup i E) ≡ fst (numeralL k)
             → fst (lookup j E) ≡ fst (numeralL (suc k))
             → ⟨ E ⊨ sucAtL i j ⟩
      sucTag i j k qi qj = subst ⟨_⟩ (sym (sucAtL-adequate i j E))
        (qj ∙ nsuc k ∙ cong sucV (sym qi))

    ht : ⟨ E ⊨ Mx.P.transK ⟩
    ht x xK y y∈x = Cl.transK (fst x) (fst y) xK y∈x

    hq : ⟨ E ⊨ Mx.P.pairK ⟩
    hq x xK y yK = ∣ prʟ x y
      , ( Cl.B.prʟ∈λ x y xK yK
        , subst ⟨_⟩ (sym (prAtL-adequate zero (suc (suc zero)) (suc zero) (prʟ x y ∷ y ∷ x ∷ E)))
            (prʟ-fst x y) ) ∣₁

    hs : ⟨ E ⊨ Mx.P.sucK ⟩
    hs x xK = ∣ sucʟ x
      , ( subst (λ u → ⟨ u ∈ fst zS ⟩) (sym (sucʟ-fst x)) (Cl.sucK (fst x) xK)
        , subst ⟨_⟩ (sym (sucAtL-adequate (suc zero) zero (sucʟ x ∷ x ∷ E))) (sucʟ-fst x) ) ∣₁

    hp : ⟨ E ⊨ Mx.P.pins ⟩
    hp = (λ x x∈ → Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst
                     (subst (λ u → ⟨ fst x ∈ u ⟩) (numeralL-fst 0) x∈))))
       , ( sucTag n0 n1 0 refl refl , ( sucTag n1 n2 1 refl refl , ( sucTag n2 n3 2 refl refl
       , ( sucTag n3 n4 3 refl refl , ( sucTag n4 n5 4 refl refl , ( sucTag n5 n6 5 refl refl
       , ( sucTag n6 n7 6 refl refl , ( sucTag n7 n8 7 refl refl , ( sucTag n8 n9 8 refl refl
       , ( sucTag n9 n10 9 refl refl , sucTag n10 n11 10 refl refl ))))))))))

    hn : ⟨ E ⊨ numsAt oo n0 ⟩
    hn = Cl.numO 0 , ( up , back )
      where
      up : (n : CS.S) → ⟨ fst n ∈ ω ⟩
         → ⟨ (n ∷ E) ⊨ ∃̇∈ (var (sh1 oo)) (sucAtL i1 i0) ⟩
      up n n∈ = PT.rec squash₁ go (Cl.O-num (fst n) n∈)
        where
        go : Σ[ k ∈ ℕ ] (fst n ≡ fst (numeralL k))
           → ⟨ (n ∷ E) ⊨ ∃̇∈ (var (sh1 oo)) (sucAtL i1 i0) ⟩
        go (k , q) = ∣ numeralL (suc k)
          , ( Cl.numO (suc k)
            , subst ⟨_⟩ (sym (sucAtL-adequate i1 i0 (numeralL (suc k) ∷ n ∷ E)))
                (nsuc k ∙ cong sucV (sym q)) ) ∣₁

      back : (n : CS.S) → ⟨ fst n ∈ ω ⟩
           → ⟨ (n ∷ E) ⊨ ((var i0 ≐ var (sh1 n0)) ∨̇ ∃̇∈ (var (sh1 oo)) (sucAtL i0 i1)) ⟩
      back n n∈ = PT.rec squash₁ go (Cl.O-num (fst n) n∈)
        where
        go : Σ[ k ∈ ℕ ] (fst n ≡ fst (numeralL k))
           → ⟨ (n ∷ E) ⊨ ((var i0 ≐ var (sh1 n0)) ∨̇ ∃̇∈ (var (sh1 oo)) (sucAtL i0 i1)) ⟩
        go (zero , q) = ∣ inl q ∣₁
        go (suc k , q) = ∣ inr ∣ numeralL k
          , ( Cl.numO k
            , subst ⟨_⟩ (sym (sucAtL-adequate i0 i1 (numeralL k ∷ n ∷ E)))
                (q ∙ nsuc k) ) ∣₁ ∣₁

    wK : ⟨ fst aS ∈ fst zS ⟩
    wK = Cl.Lset∈K p p∈λ

    bK : ⟨ fst pS ∈ fst zS ⟩
    bK = Cl.ord∈K p p∈λ

    module Gr = Graph {16} ww bb kk oo n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
                  E lam ad refl refl tags op p∈λ refl

    hm : ⟨ E ⊨ Mx.matrix ⟩
    hm = ht , ( hq , ( hs , ( hp , ( hn , ( wK , ( bK , Gr.graph ))))))

    private
      mk : (k : ℕ) → ⟨ fst (numeralL k) ∈ fst zS ⟩
      mk = Cl.B.num∈λ

    -- The thirteen bounded existentials, spent with the numerals and ω.
    h3 : ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ W3V.three ⟩
    h3 =
      wrap-in s4 (aS ∷ pS ∷ zS ∷ []) ωʟ Cl.ω∈K (
      wrap-in s5 (ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 11) (mk 11) (
      wrap-in s6 (numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 10) (mk 10) (
      wrap-in s7 (numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 9) (mk 9) (
      wrap-in s8 (numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 8) (mk 8) (
      wrap-in s9 (numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 7) (mk 7) (
      wrap-in s10 (numeralL 7 ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 6) (mk 6) (
      wrap-in s11 (numeralL 6 ∷ numeralL 7 ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 5) (mk 5) (
      wrap-in s12 (numeralL 5 ∷ numeralL 6 ∷ numeralL 7 ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 4) (mk 4) (
      wrap-in s13 (numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7 ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 3) (mk 3) (
      wrap-in s14 (numeralL 3 ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7 ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 2) (mk 2) (
      wrap-in s15 (numeralL 2 ∷ numeralL 3 ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7 ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 1) (mk 1) (
      wrap-in inner (numeralL 1 ∷ numeralL 2 ∷ numeralL 3 ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7 ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ ωʟ ∷ aS ∷ pS ∷ zS ∷ []) (numeralL 0) (mk 0)
        (inner-in E hm)))))))))))))

    -- The ordinality conjunct, at the class carrier.
    ho : ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ embed isOrd-at-p ⟩
    ho = (λ x x∈p y y∈x → op .fst {x = fst x} {y = fst y} y∈x x∈p)
       , (λ x x∈p y y∈x u u∈y → op .snd (fst x) x∈p {x = fst y} {y = fst u} u∈y y∈x)

    hφ : ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ embed W3V.erased ⟩
    hφ = subst (λ ψ → ⟨ (aS ∷ pS ∷ zS ∷ []) ⊨ ψ ⟩)
           (sym (Cnt.erase-inv W3V.three W3V.count-three)) h3

    complete : ⟨ (Lset p ∷ p ∷ Lset lam ∷ []) ⊨ₚ levelFo ⟩
    complete = subst ⟨_⟩ (read Δ₀-levelFo (aS ∷ pS ∷ zS ∷ [])) (ho , hφ)

-- THE THEOREM, under the one hypothesis.
level-complete-of : DefComplete
                  → (γ : V ℓ) → Adequate γ → (p : V ℓ) → IsOrd p → ⟨ p ∈ γ ⟩
                  → ⟨ (Lset p ∷ p ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
level-complete-of dc γ ad p op p∈ = Complete4.Finish.complete dc γ ad p op p∈
```

```agda
-- =====================================================================
-- SECTION 7.  THE DEFINABLE-POWERSET ROW, SPLIT INTO ITS NINE ROWS.
-- `DefV.body` at (T ∷ C ∷ γ) with C the code set and T the
-- satisfaction graph of the carrier Lset c.  Each row is one named
-- type; `defAt-of` assembles them.  Three rows are discharged here
-- (arities are numerals, T is total on C, the environment tower); the
-- other six are the hypotheses `DefComplete` reduces to
-- (`defComplete-of-rows`).
-- =====================================================================

module Rows {m : ℕ} (d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            (γ : CS.S ^ m)
            (lam : V ℓ) (ad : Adequate lam)
            (Kq : fst (lookup K γ) ≡ Lset lam)
            (Oq : fst (lookup O γ) ≡ ω)
            (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
            (c : V ℓ) (oc : IsOrd c) (c∈λ : ⟨ c ∈ lam ⟩)
            (wq : fst (lookup w γ) ≡ Lset c)
            (dq : fst (lookup d γ) ≡ 𝒟ₒ (Lset c)) where

  module Cl = Closed lam ad
  module DV = DefV {m} d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11

  A Cs Ts Ês : CS.S
  A = At.A c oc
  Cs = At.codes c oc
  Ts = At.table c oc
  Ês = At.tower c oc

  E2 : CS.S ^ (2 + m)
  E2 = Ts ∷ Cs ∷ γ

  E3 : CS.S ^ (3 + m)
  E3 = Ês ∷ Ts ∷ Cs ∷ γ

  private
    Kv : V ℓ
    Kv = fst (lookup K γ)

    InK : V ℓ → Type (ℓ-suc ℓ)
    InK x = ⟨ x ∈ Kv ⟩

    toK : (x : V ℓ) → ⟨ x ∈ Lset lam ⟩ → InK x
    toK x h = subst (λ u → ⟨ x ∈ u ⟩) (sym Kq) h

    wit = Cl.wit c c∈λ oc

    CK : InK (fst Cs)
    CK = toK (fst Cs) (wit .snd .fst)
    TK : InK (fst Ts)
    TK = toK (fst Ts) (wit .snd .snd .fst)
    ÊK : InK (fst Ês)
    ÊK = toK (fst Ês) (wit .snd .snd .snd)

    transK : (x y : V ℓ) → InK x → ⟨ y ∈ x ⟩ → InK y
    transK x y xK y∈x = toK y (Cl.transK x y (subst (λ u → ⟨ x ∈ u ⟩) Kq xK) y∈x)

    module Z = Chain Kv transK

    arityK : (N v : CS.S) → ⟨ fst v ∈ fst N ⟩ → InK (fst N) → InK (fst v)
    arityK N v v∈N NK = transK (fst N) (fst v) NK v∈N

  -- THE NINE ROWS.
  Closed Shaped ArNum CloseR Dom Tower Twelve Mem All : Type (ℓ-suc ℓ)
  Closed = ⟨ E2 ⊨ closedBS i1 (sh2 K) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                    (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
  Shaped = ⟨ E2 ⊨ shapedBS i1 (sh2 w) (sh2 K)
                    (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                    (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
  ArNum = ⟨ E2 ⊨ arNumAt i1 (sh2 O) (sh2 K) ⟩
  CloseR = ⟨ E2 ⊨ Close.closeAt {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                    (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                    (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
  Dom = ⟨ E2 ⊨ domB i0 i1 (sh2 K) ⟩
  Tower = ⟨ E2 ⊨ envTowerAt (sh2 O) (sh2 w) (sh2 K) ⟩
  Twelve = ⟨ E2 ⊨ twelveAt i1 i0 (sh2 w) (sh2 K)
                    (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                    (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
  Mem = ⟨ E2 ⊨ memAt (sh2 d) (sh2 w) i1 i0 (sh2 K) (sh2 N0) (sh2 N1) ⟩
  All = ⟨ E2 ⊨ allAt (sh2 d) (sh2 w) i1 i0 (sh2 K) (sh2 N0) (sh2 N1) ⟩

  body-of : Closed → Shaped → ArNum → CloseR → Dom → Tower → Twelve → Mem → All
          → ⟨ E2 ⊨ DV.body ⟩
  body-of h1 h2 h3 h4 h5 h6 h7 h8 h9 =
    h1 , ( h2 , ( h3 , ( h4 , ( h5 , ( h6 , ( h7 , ( h8 , h9 )))))))

  defAt-of : ⟨ E2 ⊨ DV.body ⟩ → ⟨ γ ⊨ DV.defAt ⟩
  defAt-of hb = DV.defAt-in γ ∣ Cs , ( CK , ∣ Ts , ( TK , hb ) ∣₁ ) ∣₁

  -- ROW 3.  Every code's arity is a numeral: a code is the key of a
  -- formula, (# n, ⌜ψ⌝), and the pair is injective.
  arNum : ArNum
  arNum c' c'∈ ar arK t tK hp =
    PT.rec (snd (fst ar ∈ fst (lookup (sh3 (sh2 O)) (t ∷ ar ∷ c' ∷ E2)))) go
      (AllCodes-out A c' c'∈)
    where
    e : fst c' ≡ pr (fst ar) (fst t)
    e = pr-out i2 i1 i0 (t ∷ ar ∷ c' ∷ E2) hp
    go : Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst A ⟫ n ] (fst c' ≡ fst (keyS A ψ))
       → ⟨ fst ar ∈ fst (lookup O γ) ⟩
    go (n , (ψ , q)) =
      subst (λ u → ⟨ fst ar ∈ u ⟩) (sym Oq)
        (subst (λ u → ⟨ u ∈ ω ⟩) (sym (key-arity A ψ (fst ar) (fst t) (sym q ∙ e))) (#∈ω n))

  -- ROW 5.  T is total on C, both ways: a pair in the graph has its
  -- index in the code set, and every code has its value recorded.
  dom : Dom
  dom c' c'K =
      (λ h → PT.rec (snd (fst c' ∈ fst Cs)) byPair h)
    , (λ c'∈ → ∣ SatMap.valOf A c' c'∈
               , ( Z.sndK (fst Ts) (fst c') (fst (SatMap.valOf A c' c'∈)) TK
                     (SatMap.pairs-in A c' c'∈)
                 , app-in (sh2 i0) (suc zero) zero (SatMap.valOf A c' c'∈ ∷ c' ∷ E2)
                     (SatMap.pairs-in A c' c'∈) ) ∣₁)
    where
    byPair : Σ[ v ∈ CS.S ] (InK (fst v)
               × ⟨ (v ∷ c' ∷ E2) ⊨ appAt (sh2 i0) (suc zero) zero ⟩)
           → ⟨ fst c' ∈ fst Cs ⟩
    byPair (v , (_ , ap)) = PT.rec (snd (fst c' ∈ fst Cs))
      (λ { (x , (mx , eq)) → subst (λ u → ⟨ u ∈ fst Cs ⟩) (sym (pr-inj eq .fst)) mx })
      (SatMap.pairs-out A (pr (fst c') (fst v))
        (app-out (sh2 i0) (suc zero) zero (v ∷ c' ∷ E2) ap))

  -- ROW 6.  The environment tower.  The witness is the tower of
  -- Section 1; each entry is the environment set of its numeral arity,
  -- bounded by K through src/L/Condensation.lagda.md `EnvSet.back`,
  -- and consecutive entries are joined by `cons`.
  private
    -- An environment over the carrier of arity k lies in K: it is a
    -- member of the k-th environment set, which is in K.
    envInK : (k : ℕ) (n Ek : CS.S) → fst n ≡ # k → fst Ek ≡ fst (envSet A k)
           → InK (fst Ek)
           → (z : CS.S) → ⟨ (z ∷ Ek ∷ n ∷ E3) ⊨ envOverAt zero (suc i1) (suc (sh5 w)) ⟩
           → InK (fst z)
    envInK k n Ek qn qE EkK z hz =
      transK (fst Ek) (fst z) EkK
        (subst (λ u → ⟨ fst z ∈ u ⟩) (sym qE)
          (subst (λ u → ⟨ u ∈ fst (envSet A k) ⟩) (sym R.recovers) (envSet-in A R.g)))
      where
      module R = Recover A k (z ∷ Ek ∷ n ∷ E3) zero (suc i1) (suc (sh5 w)) qn wq hz

    -- The bounded environment-set condition at an entry.
    bnd : (k : ℕ) (n Ek : CS.S) → fst n ≡ # k → fst Ek ≡ fst (envSet A k)
        → InK (fst n) → InK (fst Ek)
        → ⟨ (Ek ∷ n ∷ E3) ⊨ envSetB i0 i1 (sh2 (sh3 w)) (sh2 (sh3 K)) ⟩
    bnd k n Ek qn qE nK EkK = ES.back hAt
      where
      module ES = EnvSet {2 + (3 + m)} i0 i1 (sh2 (sh3 w)) (sh2 (sh3 K)) (Ek ∷ n ∷ E3)
                    arityK EkK nK (envInK k n Ek qn qE EkK)
      hAt : ⟨ (Ek ∷ n ∷ E3) ⊨ envSetAt i0 i1 (sh2 (sh3 w)) ⟩
      hAt = AmbientHolds.holds A (Ek ∷ n ∷ E3) i0 i1 (sh2 (sh3 w)) k qE qn wq

    -- A member of the tower, read.
    entry : (n Ek : CS.S) → ⟨ pr (fst n) (fst Ek) ∈ fst Ês ⟩
          → ∥ Σ[ k ∈ ℕ ] ((fst n ≡ # k) × (fst Ek ≡ fst (envSet A k))) ∥₁
    entry n Ek p = PT.map (λ { (k , eq) → k , pr-inj eq })
      (EnvTower.tower-out A (down Ês (pr (fst n) (fst Ek)) p) p)

  tower : Tower
  tower = ∣ Ês , ( ÊK , ( cl1 , ( cl2 , cl3 ))) ∣₁
    where
    cl1 : (n : CS.S) → ⟨ fst n ∈ fst (lookup (sh3 O) E3) ⟩
        → ⟨ (n ∷ E3) ⊨ ∃̇∈ (var (sh1 (sh3 K)))
              (appAt (sh2 i0) i1 i0 ∧̇ envSetB i0 i1 (sh2 (sh3 w)) (sh2 (sh3 K))) ⟩
    cl1 n n∈O = PT.rec squash₁ go (Cl.O-num (fst n) (subst (λ u → ⟨ fst n ∈ u ⟩) Oq n∈O))
      where
      go : Σ[ k ∈ ℕ ] (fst n ≡ fst (numeralL k))
         → ⟨ (n ∷ E3) ⊨ ∃̇∈ (var (sh1 (sh3 K)))
               (appAt (sh2 i0) i1 i0 ∧̇ envSetB i0 i1 (sh2 (sh3 w)) (sh2 (sh3 K))) ⟩
      go (k , q) = ∣ envSet A k , ( EkK , ( app-in (sh2 i0) i1 i0 (envSet A k ∷ n ∷ E3) p
                                         , bnd k n (envSet A k) qn refl nK EkK )) ∣₁
        where
        qn : fst n ≡ # k
        qn = q ∙ numeralL-fst k
        p : ⟨ pr (fst n) (fst (envSet A k)) ∈ fst Ês ⟩
        p = subst (λ u → ⟨ pr u (fst (envSet A k)) ∈ fst Ês ⟩) (sym qn)
              (EnvTower.tower-in′ A k)
        nK : InK (fst n)
        nK = transK ω (fst n) (toK ω Cl.ω∈K) (subst (λ u → ⟨ fst n ∈ u ⟩) Oq n∈O)
        EkK : InK (fst (envSet A k))
        EkK = Z.sndK (fst Ês) (fst n) (fst (envSet A k)) ÊK p

    cl2 : (n : CS.S) → InK (fst n) → (Ek : CS.S) → InK (fst Ek)
        → ⟨ (Ek ∷ n ∷ E3) ⊨ appAt (sh2 i0) i1 i0 ⟩
        → ⟨ (Ek ∷ n ∷ E3) ⊨ envSetB i0 i1 (sh2 (sh3 w)) (sh2 (sh3 K)) ⟩
    cl2 n nK Ek EkK ap =
      PT.rec (snd ((Ek ∷ n ∷ E3) ⊨ envSetB i0 i1 (sh2 (sh3 w)) (sh2 (sh3 K))))
        (λ { (k , (qn , qE)) → bnd k n Ek qn qE nK EkK })
        (entry n Ek (app-out (sh2 i0) i1 i0 (Ek ∷ n ∷ E3) ap))

    cl3 : (n : CS.S) → InK (fst n) → (n' : CS.S) → InK (fst n')
        → (Ek : CS.S) → InK (fst Ek) → (Ek' : CS.S) → InK (fst Ek')
        → ⟨ (Ek' ∷ Ek ∷ n' ∷ n ∷ E3) ⊨
            ( appAt (sh4 i0) i3 i1 ∧̇ ( appAt (sh4 i0) i2 i0 ∧̇ sucAtL i3 i2 )) ⟩
        → (e : CS.S) → ⟨ fst e ∈ fst Ek ⟩
        → (x : CS.S) → ⟨ fst x ∈ fst (lookup (sh5 (sh3 w)) (e ∷ Ek' ∷ Ek ∷ n' ∷ n ∷ E3)) ⟩
        → ⟨ (x ∷ e ∷ Ek' ∷ Ek ∷ n' ∷ n ∷ E3) ⊨ ∃̇∈ (var i2) (consAtL i0 i1 i2) ⟩
    cl3 n nK n' n'K Ek EkK Ek' Ek'K (ap1 , (ap2 , hs)) e e∈ x x∈ =
      PT.rec squash₁ (λ { (k , (qn , qE)) →
        PT.rec squash₁ (λ { (k' , (qn' , qE')) → at k k' qn qE qn' qE' })
          (entry n' Ek' (app-out (sh4 i0) i2 i0 (Ek' ∷ Ek ∷ n' ∷ n ∷ E3) ap2)) })
        (entry n Ek (app-out (sh4 i0) i3 i1 (Ek' ∷ Ek ∷ n' ∷ n ∷ E3) ap1))
      where
      Goal : Type (ℓ-suc ℓ)
      Goal = ⟨ (x ∷ e ∷ Ek' ∷ Ek ∷ n' ∷ n ∷ E3) ⊨ ∃̇∈ (var i2) (consAtL i0 i1 i2) ⟩

      x∈A : ⟨ fst x ∈ fst A ⟩
      x∈A = subst (λ u → ⟨ fst x ∈ u ⟩) wq x∈

      fib : Σ[ mx ∈ ⟪ fst A ⟫ ] (⟪ fst A ⟫↪ mx ≡ fst x)
      fib = ∈-asFiber {a = fst x} {b = fst A} x∈A

      at : (k k' : ℕ) → fst n ≡ # k → fst Ek ≡ fst (envSet A k)
         → fst n' ≡ # k' → fst Ek' ≡ fst (envSet A k') → Goal
      at k k' qn qE qn' qE' = PT.rec squash₁ byG
        (envSet-out A k e (subst (λ u → ⟨ fst e ∈ u ⟩) qE e∈))
        where
        -- n' = n + 1, so k' = k + 1.
        kk : k' ≡ suc k
        kk = #-inj′ (sym qn' ∙ subst ⟨_⟩ (sucAtL-adequate i3 i2 (Ek' ∷ Ek ∷ n' ∷ n ∷ E3)) hs
                     ∙ cong sucV qn)

        byG : Σ[ g ∈ Ix A k ] (fst e ≡ fst (envS A g)) → Goal
        byG (g , eg) = ∣ e' , ( e'∈ , hc ) ∣₁
          where
          g' : Ix A (suc k)
          g' = cons (fib .fst) g
          e' : CS.S
          e' = envS A g'
          e'∈ : ⟨ fst e' ∈ fst Ek' ⟩
          e'∈ = subst (λ u → ⟨ fst e' ∈ u ⟩) (sym qE')
                  (subst (λ j → ⟨ fst e' ∈ fst (envSet A j) ⟩) (sym kk) (envSet-in A g'))
          hc : ⟨ (e' ∷ x ∷ e ∷ Ek' ∷ Ek ∷ n' ∷ n ∷ E3) ⊨ consAtL i0 i1 i2 ⟩
          hc = subst ⟨_⟩
                 (sym (consAtL-adequate i0 i1 i2 (e' ∷ x ∷ e ∷ Ek' ∷ Ek ∷ n' ∷ n ∷ E3)
                        (λ i → ⟪ fst A ⟫↪ (g i)) eg))
                 (cong env (funExt (λ { zero → fib .snd ; (suc i) → refl })))

-- THE REDUCTION.  Six rows are the hypotheses; the other three are
-- the module's own.
RowHyps : Type (ℓ-suc ℓ)
RowHyps =
  ∀ {m} (d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
    (γ : CS.S ^ m)
  → (lam : V ℓ) (ad : Adequate lam)
  → (Kq : fst (lookup K γ) ≡ Lset lam)
  → (Oq : fst (lookup O γ) ≡ ω)
  → (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
  → (c : V ℓ) (oc : IsOrd c) (c∈λ : ⟨ c ∈ lam ⟩)
  → (wq : fst (lookup w γ) ≡ Lset c)
  → (dq : fst (lookup d γ) ≡ 𝒟ₒ (Lset c))
  → let module R = Rows d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
                        lam ad Kq Oq tags c oc c∈λ wq dq
    in R.Closed × R.Shaped × R.CloseR × R.Twelve × R.Mem × R.All

defComplete-of-rows : RowHyps → DefComplete
defComplete-of-rows hyp d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
                    lam ad Kq Oq tags c oc c∈λ wq dq =
  R.defAt-of (R.body-of h1 h2 R.arNum h4 R.dom R.tower h7 h8 h9)
  where
  module R = Rows d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
                  lam ad Kq Oq tags c oc c∈λ wq dq
  hs = hyp d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ lam ad Kq Oq tags c oc c∈λ wq dq
  h1 = hs .fst
  h2 = hs .snd .fst
  h4 = hs .snd .snd .fst
  h7 = hs .snd .snd .snd .fst
  h8 = hs .snd .snd .snd .snd .fst
  h9 = hs .snd .snd .snd .snd .snd

-- THE THEOREM, under the six row hypotheses.
level-complete-of-rows : RowHyps
                       → (γ : V ℓ) → Adequate γ → (p : V ℓ) → IsOrd p → ⟨ p ∈ γ ⟩
                       → ⟨ (Lset p ∷ p ∷ Lset γ ∷ []) ⊨ₚ levelFo ⟩
level-complete-of-rows hyp = level-complete-of (defComplete-of-rows hyp)
```
