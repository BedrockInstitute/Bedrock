{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.31-R5p] D-1 probe: the Basic defSet->isL chain re-founded on isJ.
--
-- Six representative declarations of L.Axioms.Basic, re-proven over the J
-- tower using ONLY delivered exports.  Measures statement-churn lines against
-- genuine-proof lines per declaration, and names the engine gaps rather than
-- building them.
--
-- Line-count convention: non-blank lines inside the agda region (comments
-- included, blanks excluded), the pinned convention.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeR5 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; ↾-reflects )
import FOL.ZFModel
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( pair-singleton; union-spec )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( ∅-ord; bound2 )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-mem; +ω-sup; +ω-limit )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-mono; Sset-mem; Sset-in; Sset-zero; Sset-suc; Sset-trans
  ; Jset; Jset-rud; step; step-∈
  ; f0; f1; f5; Fof-f0; Fof-f1; Fof-f5 )
open import L.Rud.Ops {ℓ} using ( F1-spec )
open import L.Rud.ClassJ {ℓ} lem A using ( isJ; isPropIsJ; isJ-trans; Jset→isJ; 𝒮ⱼ )
open import L.Rud.Switch {ℓ} lem A using ( module LimitSwitch )
open import L.Rud.SatSets {ℓ} lem A using ( module LimitFullSwitch )

open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( _∈ₛ_; ∈∈ₛ; _⊆_; ⟪_⟫; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions using
  ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; ⋃_; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( isPropIsContr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- ===================================================================
-- P0 (CONTROL).  Basic:196 `Lset-suc : Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)`
-- is the tower's successor identity, 21 lines on the L side.
-- The J twin is DELIVERED VERBATIM as `Sset-suc`.  Zero new lines:
-- the alias below exists only to witness that the name typechecks
-- at the probe's telescope.
-- ===================================================================

Ssuc-control : (β : S) → Sset (sucV β) ≡ step (Sset β)
Ssuc-control = Sset-suc

-- ===================================================================
-- P1  (class (b): the theorem whose L-side proof leans on Lset-specific
--      stage structure).
-- L side: Basic:156-161, `isL-Lset` + `LsetS`, 6 lines PLUS an
-- `opaque` seal (R-29/Rule 2: unsealed, L.Axioms.Full did not finish
-- in ten minutes).  Its proof runs stage -> defSet(TOP) -> 𝒟ₒ -> isL,
-- i.e. it spends the WHOLE definability engine to say a stage is
-- constructible.
-- J side: the level is a member of any larger level.  `Sset-mem` is
-- the whole proof; the outer limit is manufactured by `+ω`.
-- ===================================================================

isJ-Jset : (β : S) (limβ : ⟨ isLimit β ⟩) → ⟨ isJ (Jset β limβ) ⟩
isJ-Jset β limβ =
  Jset→isJ (+ω β) (+ω-limit β (isLimit-ord β limβ)) (Jset β limβ)
    (Sset-mem {α = +ω β} {β = β} (+ω-mem β))

JsetS : (β : S) (limβ : ⟨ isLimit β ⟩) → Σ[ x ∈ S ] ⟨ isJ x ⟩
JsetS β limβ = Jset β limβ , isJ-Jset β limβ

-- ===================================================================
-- P2  (the empty set: Basic:490-508, `∅∈𝒟ₒ` + `∅∈L` + `∅ʟ`, 19 lines,
--      of which 13 are the extensionality proving `defSet ⊥̇ ≡ ∅`).
-- J side: the base level IS empty (`Sset-zero`, delivered), and a set
-- is a member of the step over itself (`step-∈`, delivered).  No
-- formula, no defSet, no extensionality.
-- ===================================================================

∅∈J : ⟨ isJ ∅ ⟩
∅∈J = Jset→isJ (+ω ∅) (+ω-limit ∅ ∅-ord) ∅
  (Sset-in (+ω ∅) ∅ ∅ (+ω-mem ∅)
    (subst (λ t → ⟨ t ∈ˢ step (Sset ∅) ⟩) Sset-zero (step-∈ (Sset ∅))))

-- ===================================================================
-- P3  (class (c): the comprehension consumer.  Basic:547-599,
--      `pair∈𝒟ₒ` + `pair∈Lset-suc` + `sgl∈Lset-suc` + `pr∈Lset-suc`,
--      50 lines, of which 38 are the two-direction extensionality
--      identifying `defSet φ` with the pair.
-- J side: F0 IS the unordered pair, definitionally, and the level is
-- closed under the sixteen operations (`Jset-rud`, delivered
-- unconditionally).  The ordered pair costs no level climb at all,
-- against the L side's TWO successor stages.
-- ===================================================================

pair∈J : (α : S) (limα : ⟨ isLimit α ⟩) (x y : S)
       → ⟨ x ∈ˢ Jset α limα ⟩ → ⟨ y ∈ˢ Jset α limα ⟩
       → ⟨ ⁅ x , y ⁆ ∈ˢ Jset α limα ⟩
pair∈J α limα x y x∈ y∈ = subst (λ t → ⟨ t ∈ˢ Jset α limα ⟩)
  (Fof-f0 x y) (Jset-rud α limα f0 x y x∈ y∈)

sgl∈J : (α : S) (limα : ⟨ isLimit α ⟩) (x : S)
      → ⟨ x ∈ˢ Jset α limα ⟩ → ⟨ ⁅ x ⁆s ∈ˢ Jset α limα ⟩
sgl∈J α limα x x∈ = subst (λ t → ⟨ t ∈ˢ Jset α limα ⟩)
  (pair-singleton x) (pair∈J α limα x x x∈ x∈)

pr∈J : (α : S) (limα : ⟨ isLimit α ⟩) (x y : S)
     → ⟨ x ∈ˢ Jset α limα ⟩ → ⟨ y ∈ˢ Jset α limα ⟩
     → ⟨ pr x y ∈ˢ Jset α limα ⟩
pr∈J α limα x y x∈ y∈ = pair∈J α limα ⁅ x ⁆s ⁅ x , y ⁆
  (sgl∈J α limα x x∈) (pair∈J α limα x y x∈ y∈)

-- ===================================================================
-- P4  (class (c'): the Separation-style bounded-quantifier carve.
--      Basic:657-717, `UnionOf.mkUnion`'s `defSet≡` + `union∈𝒟ₒ`,
--      42 lines: a bounded existential formula, a two-direction
--      extensionality against `union-ax`, and one transitivity spend
--      (`layer-trans`) to place the witness inside the stage.
-- J side: F5 IS the union, definitionally.
-- ===================================================================

-- LESSONS C-20 fired verbatim here: `⋃ a ∈ˢ _` is rejected by the mixfix
-- parser, so the union term is bound first.  One line, recorded cure.
setUn : S → S
setUn a = ⋃ a

union∈J : (α : S) (limα : ⟨ isLimit α ⟩) (a : S)
        → ⟨ a ∈ˢ Jset α limα ⟩ → ⟨ setUn a ∈ˢ Jset α limα ⟩
union∈J α limα a a∈ = subst (λ t → ⟨ t ∈ˢ Jset α limα ⟩)
  (Fof-f5 a a) (Jset-rud α limα f5 a a a∈ a∈)

-- ===================================================================
-- P5  (class (d): the Stages-style directedness/cofinality fact.
--      Basic:385-407, `isL-directed`, 23 lines: two ordinals bounded
--      by `boundingOrd`, then `Lset-mono` twice.
-- J side: the same shape, but the bound must be re-taken to a LIMIT,
-- which is `+ω` of the ordinal bound.  One extra delivered lemma.
-- ===================================================================

isJ-directed : (x y : S) → ⟨ isJ x ⟩ → ⟨ isJ y ⟩
             → ∥ Σ[ γ ∈ S ] Σ[ lim ∈ ⟨ isLimit γ ⟩ ]
                 (⟨ x ∈ˢ Jset γ lim ⟩ × ⟨ y ∈ˢ Jset γ lim ⟩) ∥₁
isJ-directed x y px py = PT.rec2 squash₁ go px py
  where
  Bound : Type (ℓ-suc ℓ)
  Bound = Σ[ γ ∈ S ] Σ[ lim ∈ ⟨ isLimit γ ⟩ ]
            (⟨ x ∈ˢ Jset γ lim ⟩ × ⟨ y ∈ˢ Jset γ lim ⟩)
  go : (Σ[ α ∈ S ] Σ[ limα ∈ ⟨ isLimit α ⟩ ] ⟨ x ∈ˢ Jset α limα ⟩)
     → (Σ[ β ∈ S ] Σ[ limβ ∈ ⟨ isLimit β ⟩ ] ⟨ y ∈ˢ Jset β limβ ⟩)
     → ∥ Bound ∥₁
  go (α , limα , x∈) (β , limβ , y∈) =
    ∣ +ω σ , +ω-limit σ ordσ
    , ( Sset-mono {α = +ω σ} {β = α} (+ω-sup σ α α∈σ) x x∈
      , Sset-mono {α = +ω σ} {β = β} (+ω-sup σ β β∈σ) y y∈ ) ∣₁
    where
    bnd = bound2 α β (isLimit-ord α limα) (isLimit-ord β limβ)
    σ = bnd .fst
    ordσ = bnd .snd .fst
    α∈σ = bnd .snd .snd .fst
    β∈σ = bnd .snd .snd .snd

-- ===================================================================
-- P6  (class (a): the pure defSet-former theorem).
-- L side: Basic:130-133, `defSet→isL`, 4 lines, riding `𝒟ₒ→isL`
-- (Basic:98-116, 19 lines) and `𝒟ₒ-intro`.  Total 23 lines, all
-- delivered on the L side with NO hypothesis.
--
-- J side: the same statement needs the definable subset of a J level
-- to be a member of a larger J level.  That is the switch theorem's
-- comprehension direction, `Switch.LimitSwitch.Up.definable→closure`.
-- It is DELIVERED, but inside `module Up (Jimg : ...)`: the rud image
-- principle is an UNDISCHARGED hypothesis (Switch's own recap:
-- "Two residues stand").  `LimitSwitch` is instantiated nowhere in
-- `src/` and no `Jimg` is supplied anywhere.
--
-- So the probe states the residue (D-15[B] standing shape) and proves
-- the theorem from it.  The residue also carries a Δ₀ rider the L-side
-- statement does not have.
-- ===================================================================

DefClosureJ : Type (ℓ-suc ℓ)
DefClosureJ = (α : S) (limα : ⟨ isLimit α ⟩) (β : S) (limβ : ⟨ isLimit β ⟩)
            → ⟨ β ∈ˢ α ⟩ → (φ : Formula ⟪ Jset β limβ ⟫ 1) → Δ₀ φ
            → ⟨ DefOf.defSet (Jset β limβ) φ ∈ˢ Jset α limα ⟩

defSet→isJ : DefClosureJ → (β : S) (limβ : ⟨ isLimit β ⟩) (x : S)
           → ∥ Σ[ φ ∈ Formula ⟪ Jset β limβ ⟫ 1 ]
               (Δ₀ φ × (DefOf.defSet (Jset β limβ) φ ≡ x)) ∥₁
           → ⟨ isJ x ⟩
defSet→isJ dc β limβ x = PT.rec (isPropIsJ x) go
  where
  ordβ : IsOrd β
  ordβ = isLimit-ord β limβ
  go : Σ[ φ ∈ Formula ⟪ Jset β limβ ⟫ 1 ]
         (Δ₀ φ × (DefOf.defSet (Jset β limβ) φ ≡ x)) → ⟨ isJ x ⟩
  go (φ , d , q) = Jset→isJ (+ω β) (+ω-limit β ordβ) x
    (subst (λ t → ⟨ t ∈ˢ Jset (+ω β) (+ω-limit β ordβ) ⟩) q
      (dc (+ω β) (+ω-limit β ordβ) β limβ (+ω-mem β) φ d))

-- The OTHER residue of the switch chapter, the description side's image
-- arm, IS nameable from outside; the closure side's `Jimg` is not,
-- because Switch takes `Comp` from Realize's `Basis` with a
-- non-`public` open.  C-14[B]: a hypothesis a consumer must supply and
-- cannot name is a delivery defect.
module ResidueShape (α : S) (limα : ⟨ isLimit α ⟩)
                    (β : S) (limβ : ⟨ isLimit β ⟩) (β∈α : ⟨ β ∈ˢ α ⟩) where
  module LS = LimitSwitch α limα β limβ β∈α
  imgArm : Type (ℓ-suc ℓ)
  imgArm = LS.Ds.ImgArm

-- ===================================================================
-- P6b  The residue is DISCHARGED TODAY -- but by a chapter R5 retires.
-- `L.Rud.SatSets.LimitFullSwitch.full-switch-⊇` is the switch's
-- comprehension direction with BOTH riders gone: no Δ₀ hypothesis and
-- no `Jimg`.  It rides the coded satisfaction table (SatTable/CodeSet/
-- CodePred), i.e. the bridge cluster the R5 census retires (§5,
-- 5,970 lines).  So under R5-as-specified this is a residue again.
-- ===================================================================

DefClosureJ-delivered : DefClosureJ
DefClosureJ-delivered α limα β limβ β∈α φ _ =
  LimitFullSwitch.full-switch-⊇ α limα β limβ β∈α φ

defSet→isJ-today : (β : S) (limβ : ⟨ isLimit β ⟩) (x : S)
                 → ∥ Σ[ φ ∈ Formula ⟪ Jset β limβ ⟫ 1 ]
                     (Δ₀ φ × (DefOf.defSet (Jset β limβ) φ ≡ x)) ∥₁
                 → ⟨ isJ x ⟩
defSet→isJ-today = defSet→isJ DefClosureJ-delivered

-- ===================================================================
-- P7  The G-bucket churn measured end to end: the UNION AXIOM over 𝒮ⱼ.
-- L side: Basic:429-439 (`extensionalL`, 11), :466-470 (`uniqueL` +
-- `mere→uniqueL`, 5), :657-732 (`UnionOf` + `hasUnionL`, 65).
-- Every line below is a character-level re-point of those, with
-- `isL-trans` -> `isJ-trans`, `Lset σ` -> `Jset α limα`, `IsOrd` ->
-- `isLimit`, and the carve replaced by P4.  Nothing is re-proven.
-- ===================================================================

module J = hPropStructure 𝒮ⱼ
module ModelJ = FOL.ZFModel 𝒮ⱼ
open ModelJ using ( SetOf; setOf-unique )

extensionalJ : {a b : J.S} → ((x : J.S) → (x J.∈ˢ a) ≡ (x J.∈ˢ b)) → a ≡ b
extensionalJ {a} {b} h =
  ↾-reflects {𝒮 = 𝒮ᵥ} {M = isJ} (extensionalV {a = fst a} {b = fst b} vwise)
  where
  vwise : (v : S) → (v ∈ˢ fst a) ≡ (v ∈ˢ fst b)
  vwise v = ⇔toPath fwd bwd
    where
    fwd : ⟨ v ∈ˢ fst a ⟩ → ⟨ v ∈ˢ fst b ⟩
    fwd v∈a = subst ⟨_⟩ (h (v , isJ-trans v∈a (a .snd))) v∈a
    bwd : ⟨ v ∈ˢ fst b ⟩ → ⟨ v ∈ˢ fst a ⟩
    bwd v∈b = subst ⟨_⟩ (sym (h (v , isJ-trans v∈b (b .snd)))) v∈b

uniqueJ : (Q : J.S → Ω) → SetOf Q → isContr (SetOf Q)
uniqueJ = setOf-unique extensionalJ

mere→uniqueJ : (Q : J.S → Ω) → ∥ SetOf Q ∥₁ → isContr (SetOf Q)
mere→uniqueJ Q = PT.rec isPropIsContr (uniqueJ Q)

module UnionOfJ (a : J.S) where
  Q : J.S → Ω
  Q x = ⋁ J.S (λ y → (y J.∈ˢ a) ⊓ (x J.∈ˢ y))

  mkUnion : (α : S) (limα : ⟨ isLimit α ⟩) → ⟨ fst a ∈ˢ Jset α limα ⟩ → SetOf Q
  mkUnion α limα fa∈ = unionElt , spec
    where
    unionElt : J.S
    unionElt = setUn (fst a)
             , Jset→isJ α limα (setUn (fst a)) (union∈J α limα (fst a) fa∈)
    spec : (z : J.S) → (z J.∈ˢ unionElt) ≡ Q z
    spec z = union-spec (fst a) (fst z) ∙ bridge
      where
      bridge : ⋁ S (λ y → (y ∈ˢ fst a) ⊓ (fst z ∈ˢ y)) ≡ Q z
      bridge = ⇔toPath
        (PT.map (λ { (y , py) →
          (y , isJ-trans {x = fst a} {y = y} (py .fst) (a .snd)) , py }))
        (PT.map (λ { (y , py) → fst y , py }))

  build : ∥ SetOf Q ∥₁
  build = PT.rec squash₁
    (λ { (α , limα , fa∈) → ∣ mkUnion α limα fa∈ ∣₁ }) (a .snd)

hasUnionJ : (a : J.S)
          → isContr (SetOf (λ x → ⋁ J.S (λ y → (y J.∈ˢ a) ⊓ (x J.∈ˢ y))))
hasUnionJ a = mere→uniqueJ (UnionOfJ.Q a) (UnionOfJ.build a)

-- ===================================================================
-- P8  Two honesty checks on statement strength (a false GO is one that
-- quietly weakened the target).
--
-- (i) P1 was stated at a LIMIT β, while `isL-Lset` asks only `IsOrd`.
--     The general form costs the same three lines, so the index is not
--     weakened: the `+ω` block manufactures the limit certificate.
-- (ii) P6's Δ₀ rider is an artefact of Switch's `switch-⊇`, not of the
--     J tower.  The delivered SatSets switch is Δ₀-free, so the
--     Δ₀-free statement (the exact L-side shape) holds today.
-- ===================================================================

isJ-Sset : (β : S) → IsOrd β → ⟨ isJ (Sset β) ⟩
isJ-Sset β ordβ = Jset→isJ (+ω β) (+ω-limit β ordβ) (Sset β)
  (Sset-mem {α = +ω β} {β = β} (+ω-mem β))

defSetFree→isJ : (β : S) (limβ : ⟨ isLimit β ⟩) (x : S)
               → ∥ Σ[ φ ∈ Formula ⟪ Jset β limβ ⟫ 1 ]
                   (DefOf.defSet (Jset β limβ) φ ≡ x) ∥₁
               → ⟨ isJ x ⟩
defSetFree→isJ β limβ x = PT.rec (isPropIsJ x) go
  where
  ordβ : IsOrd β
  ordβ = isLimit-ord β limβ
  go : Σ[ φ ∈ Formula ⟪ Jset β limβ ⟫ 1 ]
         (DefOf.defSet (Jset β limβ) φ ≡ x) → ⟨ isJ x ⟩
  go (φ , q) = Jset→isJ (+ω β) (+ω-limit β ordβ) x
    (subst (λ t → ⟨ t ∈ˢ Jset (+ω β) (+ω-limit β ordβ) ⟩) q
      (LimitFullSwitch.full-switch-⊇ (+ω β) (+ω-limit β ordβ) β limβ
        (+ω-mem β) φ))
