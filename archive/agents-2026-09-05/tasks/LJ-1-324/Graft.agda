{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.324] PROBE.  Does `stage-card-upper` transplant to `CanonInj`'s
-- pair?
--
-- THE LEAD.  `[LJ-1.321]` section 8 item 4 named `stage-card-upper`
-- (src/L/StageCardinal.lagda.md:564-566) as the strongest delivered
-- source for `CanonInj` (agents/tasks/LJ-1-321/Door.agda:193-195), and
-- refused to price the transplant under P-l.  This file settles it by
-- building it.
--
-- WHAT THIS FILE MEASURES, in order:
--
--   PART 1  THE ENGINE, EXTRACTED GENERIC.  `LimitStep`
--           (src/L/StageCardinal.lagda.md:277-403) with `Lset`,
--           `Formula`, `V` and `L` all removed.  It is tower-blind and
--           it is the whole positive content of the technique.
--   PART 2  THE ENGINE AT `CanonInj`'s PAIR.  A `Coding` gives
--           `CanonInj`.  And a `CanonInj` gives a `Coding` back.  So the
--           engine ALONE buys nothing: the content is where the code
--           type comes from.
--   PART 3  THE COVER TRANSPLANTS.  MEASURED.  Every member of an
--           ordinal is a member of its own stage, so the delivered
--           definability decomposition names it.  This half works.
--   PART 4  THE VALUE MAP DOES NOT.  MEASURED by a term.  An injective
--           value map on `stage-card-upper`'s own code type ALREADY
--           CONTAINS `CanonInj`'s conclusion.  So the transplant cannot
--           be cheaper than its goal.
--   PART 5  WHY.  At the own pair the branch composes the induction
--           hypothesis with the FREE small-into-big embedding.  At the
--           transplanted pair the same composition runs big-into-small,
--           which is the goal's own shape at every member.
--
-- Nothing lands.  Tracked probe.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-324.Graft {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula; ⊥̇ )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-inv; Lset-out )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( Lset-cumul; ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; leastOf )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Foundations.Prelude using ( J; substRefl )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; isSetS; _∈ˢ_ )

-- =====================================================================
-- PART 1.  THE ENGINE, EXTRACTED GENERIC.
--
--   `LimitStep` (src/L/StageCardinal.lagda.md:277-403) does exactly
--   this and nothing else.  Read `class-pred` (:319-323), `nonempty`
--   (:325-348), `h` (:350-351) and `h-inj` (:353-394) against the five
--   definitions below.
--
--   The delivered form spends 73 non-blank non-comment lines (:319-394)
--   plus 26 more for its stability lemmas (:288-317), against 39 here.
--   It is longer because its code type is
--   DEPENDENT (`Σ[ m ∈ ⟪ α ⟫ ] Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`), so the
--   injectivity of its value map needs a transport dance (`cnt-stable`
--   :294-298, `defset-stable` :300-306, `defset-stable-δ` :308-317).
--   Taking that injectivity as a HYPOTHESIS leaves the engine below.
--
--   DD4, my axis: does the construction name a tower?  NO.  `Engine`
--   names no `V`, no `L`, no `Lset` and no ordinal.  It is generic in
--   the carrier, so it is shared machinery by construction.
-- =====================================================================

module Engine (Src : Type ℓ) (Tgt : Type ℓ) (Cod : Type ℓ)
              (Amb : Type (ℓ-suc ℓ)) (setAmb : isSet Amb)
              (order : SWO {ℓ} Tgt)
              (into : Src → Amb)
              (into-inj : (x y : Src) → into x ≡ into y → x ≡ y)
              (name : Cod → Amb)
              (val : Cod → Tgt)
              (val-inj : (c d : Cod) → val c ≡ val d → c ≡ d)
              (cover : (x : Src) → ∥ Σ[ c ∈ Cod ] (name c ≡ into x) ∥₁)
              where

  pred : Src → Tgt → hProp (ℓ-suc ℓ)
  pred x y = ∥ Σ[ c ∈ Cod ] ((name c ≡ into x) × (val c ≡ y)) ∥₁ , squash₁

  nonempty : (x : Src) → ∥ Σ[ y ∈ Tgt ] ⟨ pred x y ⟩ ∥₁
  nonempty x = PT.map
    (λ w → val (fst w) , ∣ fst w , (snd w , refl) ∣₁) (cover x)

  h : Src → Tgt
  h x = fst (leastOf order lem (pred x) (nonempty x))

  h-inj : (x y : Src) → h x ≡ h y → x ≡ y
  h-inj x y e = into-inj x y (go pm)
    where
    lx = leastOf order lem (pred x) (nonempty x)
    ly = leastOf order lem (pred y) (nonempty y)
    pm : ⟨ pred x (fst ly) ⟩
    pm = subst (λ z → ⟨ pred x z ⟩) e (fst (snd lx))
    py : ⟨ pred y (fst ly) ⟩
    py = fst (snd ly)
    go : ⟨ pred x (fst ly) ⟩ → into x ≡ into y
    go = PT.rec (setAmb (into x) (into y)) go₁
      where
      go₁ : Σ[ c ∈ Cod ] ((name c ≡ into x) × (val c ≡ fst ly))
          → into x ≡ into y
      go₁ (c , nc , vc) = PT.rec (setAmb (into x) (into y)) go₂ py
        where
        go₂ : Σ[ d ∈ Cod ] ((name d ≡ into y) × (val d ≡ fst ly))
            → into x ≡ into y
        go₂ (d , nd , vd) =
          sym nc ∙ cong name (val-inj c d (vc ∙ sym vd)) ∙ nd

  embed : Σ[ f ∈ (Src → Tgt) ] ((x y : Src) → f x ≡ f y → x ≡ y)
  embed = h , h-inj

-- =====================================================================
-- PART 2.  THE ENGINE AT `CanonInj`'s PAIR.
--
--   `CanonInj` is copied verbatim from
--   agents/tasks/LJ-1-321/Door.agda:193-195.  Nothing here changes it.
-- =====================================================================

CanonInj : Type (ℓ-suc ℓ)
CanonInj = (α : V ℓ) (m : ⟪ α ⟫) → IsOrd α
         → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁ → ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫

-- The engine's input at `CanonInj`'s pair, with the ambient set fixed to
-- `S` and the comparison done there, exactly as `LimitStep` does it.
CodingAt : (α : S) (m : ⟪ α ⟫) → Type (ℓ-suc ℓ)
CodingAt α m =
  Σ[ Cod ∈ Type ℓ ]
  Σ[ name ∈ (Cod → S) ]
  Σ[ val ∈ (Cod → ⟪ ⟪ α ⟫↪ m ⟫) ]
    ( ((c d : Cod) → val c ≡ val d → c ≡ d)
    × ((x : ⟪ α ⟫) → ∥ Σ[ c ∈ Cod ] (name c ≡ ⟪ α ⟫↪ x) ∥₁) )

-- THE TRANSPLANT, as far as the engine carries it.
coding→canon : ((α : S) (m : ⟪ α ⟫) → IsOrd α
                → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁ → CodingAt α m)
             → CanonInj
coding→canon k α m oα h = E.embed
  where
  δ : S
  δ = ⟪ α ⟫↪ m
  oδ : IsOrd δ
  oδ = mem-ord {A = α} oα δ (member α m)
  cd = k α m oα h
  module E = Engine ⟪ α ⟫ ⟪ δ ⟫ (fst cd) S isSetS (ordSWO δ oδ)
                    (⟪ α ⟫↪) (λ x y p → ↪-inj {a = α} p)
                    (fst (snd cd)) (fst (snd (snd cd)))
                    (fst (snd (snd (snd cd)))) (snd (snd (snd (snd cd))))

-- AND BACK.  MEASURED: a coding is no easier than the injection it
-- builds, so the engine ALONE buys nothing at any pair.  The content of
-- `stage-card-upper` is never the engine; it is the delivered code type
-- that feeds it.
canon→coding : (α : S) (m : ⟪ α ⟫)
             → ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ → CodingAt α m
canon→coding α m e =
  ⟪ α ⟫ , (⟪ α ⟫↪) , fst e , snd e , λ x → ∣ x , refl ∣₁

-- =====================================================================
-- PART 3.  THE COVER TRANSPLANTS.  MEASURED.
--
--   `stage-card-upper`'s code type is
--   `Σ[ m ∈ ⟪ α ⟫ ] Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`
--   (src/L/StageCardinal.lagda.md:285-286, :320-322), and its cover is
--   `nonempty` (:325-348), built from `Lset-out` and `𝒟ₒ-inv`.
--
--   Its source is `⟪ Lset α ⟫`.  `CanonInj`'s source is `⟪ α ⟫`.  The
--   cover still works, because every member of an ordinal is a member of
--   that ordinal's own stage (`Lower.α⊆Lset`, :193-195).
-- =====================================================================

-- src/L/StageCardinal.lagda.md:193-195, re-derived here (C-45: I compile
-- it, I do not quote it).  It is stated at a bare α rather than inside
-- the chapter's module telescope.
ord⊆Lset : (α : S) → IsOrd α → (β : S) → ⟨ β ∈ˢ α ⟩ → ⟨ β ∈ˢ Lset α ⟩
ord⊆Lset α oα β β∈α =
  Lset-cumul β α (mem-ord {A = α} oα β β∈α) oα β∈α
    (ord∈Lset-suc β (mem-ord {A = α} oα β β∈α))

-- The code type, transplanted verbatim.
Code : (α : S) → Type ℓ
Code α = Σ[ m ∈ ⟪ α ⟫ ] Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1

codeName : (α : S) → Code α → S
codeName α (m , φ) = DefOf.defSet (Lset (⟪ α ⟫↪ m)) φ

-- src/L/StageCardinal.lagda.md:308-317 at the delivered `D`.
defset-stable-δ : (δ₁ δ₂ : S) (p : δ₁ ≡ δ₂) (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1)
                → DefOf.defSet (Lset δ₁) φ₀
                  ≡ DefOf.defSet (Lset δ₂)
                      (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀)
defset-stable-δ δ₁ δ₂ p φ₀ =
  J (λ δ₂ p → (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1)
            → DefOf.defSet (Lset δ₁) φ₀
              ≡ DefOf.defSet (Lset δ₂)
                  (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀))
    (λ φ₀ → sym (cong (DefOf.defSet (Lset δ₁))
      (substRefl {B = λ w → Formula ⟪ Lset w ⟫ 1} {x = δ₁} φ₀))) p φ₀

-- THE COVER, AT `CanonInj`'s SOURCE.  MEASURED: this half transplants
-- with no new hypothesis.
cover-ord : (α : S) (oα : IsOrd α) (x : ⟪ α ⟫)
          → ∥ Σ[ c ∈ Code α ] (codeName α c ≡ ⟪ α ⟫↪ x) ∥₁
cover-ord α oα x = PT.rec squash₁ toWitness
  (Lset-out α (⟪ α ⟫↪ x)
    (ord⊆Lset α oα (⟪ α ⟫↪ x) (member α x)))
  where
  toWitness : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ ⟪ α ⟫↪ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
            → ∥ Σ[ c ∈ Code α ] (codeName α c ≡ ⟪ α ⟫↪ x) ∥₁
  toWitness (δ , (δ∈α , x∈𝒟ₒδ)) =
    PT.map mk (𝒟ₒ-inv (Lset δ) (⟪ α ⟫↪ x) x∈𝒟ₒδ)
    where
    fib = fiber α {x = δ} δ∈α
    m : ⟪ α ⟫
    m = fib .fst
    p : ⟪ α ⟫↪ m ≡ δ
    p = fib .snd
    mk : Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ]
           (DefOf.defSet (Lset δ) φ₀ ≡ ⟪ α ⟫↪ x)
       → Σ[ c ∈ Code α ] (codeName α c ≡ ⟪ α ⟫↪ x)
    mk (φ₀ , e₀) = (m , φ) , e
      where
      φ : Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1
      φ = subst (λ w → Formula ⟪ Lset w ⟫ 1) (sym p) φ₀
      e : DefOf.defSet (Lset (⟪ α ⟫↪ m)) φ ≡ ⟪ α ⟫↪ x
      e = sym (defset-stable-δ δ (⟪ α ⟫↪ m) (sym p) φ₀) ∙ e₀

-- =====================================================================
-- PART 4.  THE VALUE MAP DOES NOT TRANSPLANT.  MEASURED BY A TERM.
--
--   `stage-card-upper`'s value map is
--   `val (m , φ) = pair m (cnt m φ)`
--   (src/L/StageCardinal.lagda.md:322, with `pair` from `Bound`
--   :68-69 and `cnt` :288-289).  Its FIRST component is the stage index
--   `m : ⟪ α ⟫` ITSELF, which at the own pair already lives in the
--   target.  At `CanonInj`'s pair the target is `⟪ δ ⟫` and the index
--   must be placed there INJECTIVELY.
--
--   The term below measures the consequence, and it needs no reading of
--   the delivered code: ANY injective value map on the transplanted code
--   type already contains `CanonInj`'s conclusion.  The section picks the
--   closed formula `⊥̇` (src/FOL/Syntax.lagda.md:98), which exists over
--   every parameter type.
-- =====================================================================

val→goal : (α : S) (δ : S) (val : Code α → ⟪ δ ⟫)
         → ((c d : Code α) → val c ≡ val d → c ≡ d)
         → ⟪ α ⟫ ↪ ⟪ δ ⟫
val→goal α δ val val-inj = f , inj
  where
  sect : ⟪ α ⟫ → Code α
  sect m = m , ⊥̇
  f : ⟪ α ⟫ → ⟪ δ ⟫
  f m = val (sect m)
  inj : (m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n
  inj m n e = cong fst (val-inj (sect m) (sect n) e)

-- THE REFUTATION, stated at `CanonInj`'s own pair.  Building the
-- transplanted value map is at least as hard as building `CanonInj`.
transplant-not-cheaper :
    ((α : S) (m : ⟪ α ⟫) → IsOrd α
     → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁
     → Σ[ val ∈ (Code α → ⟪ ⟪ α ⟫↪ m ⟫) ]
         ((c d : Code α) → val c ≡ val d → c ≡ d))
  → CanonInj
transplant-not-cheaper v α m oα h =
  val→goal α (⟪ α ⟫↪ m) (fst (v α m oα h)) (snd (v α m oα h))

-- =====================================================================
-- PART 5.  WHY THE VALUE MAP FAILS: THE BRANCH RUNS THE OTHER WAY.
--
--   `cnt m φ` (src/L/StageCardinal.lagda.md:288-289) counts the formulas
--   over `⟪ Lset (⟪ α ⟫↪ m) ⟫` into the target.  It needs an injection
--   of that stage into the target, and that is `branch`
--   (:534-559, consumed at :562).
--
--   At the OWN pair `branch` composes the induction hypothesis
--   `⟪ Lset γ ⟫ ↪ ⟪ γ ⟫` with the FREE small-into-big embedding
--   `⟪ γ ⟫ ↪ ⟪ α ⟫` (:506-515, used at :556).  `own-branch` below is
--   that composition, re-derived.
--
--   At the TRANSPLANTED pair the target is `⟪ δ ⟫` with `δ ∈ α`, so the
--   same composition would have to run big-into-small.
--   `branch→member` measures what a transplanted branch would give: a
--   canonical injection of EVERY member of `α` into `δ`, which is
--   `CanonInj`'s own shape at every member.
-- =====================================================================

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- src/L/StageCardinal.lagda.md:506-515, re-derived.  The FREE direction.
emb : (α : S) → IsOrd α → (δ : S) → ⟨ δ ∈ˢ α ⟩ → ⟪ δ ⟫ ↪ ⟪ α ⟫
emb α oα δ δ∈α = f , inj
  where
  f : ⟪ δ ⟫ → ⟪ α ⟫
  f m = fiber α {x = ⟪ δ ⟫↪ m} (oα .fst (member δ m) δ∈α) .fst
  inj : (m n : ⟪ δ ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = δ}
    (sym (fiber α {x = ⟪ δ ⟫↪ m} (oα .fst (member δ m) δ∈α) .snd)
      ∙ cong (⟪ α ⟫↪) e
      ∙ fiber α {x = ⟪ δ ⟫↪ n} (oα .fst (member δ n) δ∈α) .snd)

-- The own pair's branch, and it is free given the induction hypothesis.
own-branch : (α : S) (oα : IsOrd α)
           → ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫)
           → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
own-branch α oα ih m =
  comp-inj (ih m) (emb α oα (⟪ α ⟫↪ m) (member α m))

-- src/L/StageCardinal.lagda.md:197-205, re-derived: the lower half of the
-- stage-cardinality statement, at a bare α.
ord-into-stage : (α : S) → IsOrd α → ⟪ α ⟫ ↪ ⟪ Lset α ⟫
ord-into-stage α oα = f , inj
  where
  f : ⟪ α ⟫ → ⟪ Lset α ⟫
  f m = fiber (Lset α) {x = ⟪ α ⟫↪ m}
          (ord⊆Lset α oα (⟪ α ⟫↪ m) (member α m)) .fst
  inj : (m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = α}
    (sym (fiber (Lset α) {x = ⟪ α ⟫↪ m}
      (ord⊆Lset α oα (⟪ α ⟫↪ m) (member α m)) .snd)
      ∙ cong (⟪ Lset α ⟫↪) e
      ∙ fiber (Lset α) {x = ⟪ α ⟫↪ n}
          (ord⊆Lset α oα (⟪ α ⟫↪ n) (member α n)) .snd)

-- MEASURED: a transplanted branch is `CanonInj`'s own shape at every
-- member of α, and it is demanded at ALL of them at once.
branch→member : (α : S) (oα : IsOrd α) (δ : S)
              → ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ δ ⟫)
              → (m : ⟪ α ⟫) → ⟪ ⟪ α ⟫↪ m ⟫ ↪ ⟪ δ ⟫
branch→member α oα δ br m =
  comp-inj (ord-into-stage (⟪ α ⟫↪ m)
             (mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)))
           (br m)

-- =====================================================================
-- PART 6.  THE TERM I COULD NOT WRITE (C-36).
--
--   Two types, neither inhabited here.  They are the two ingredients
--   PARTS 4 and 5 measure, written out.
-- =====================================================================

-- The index placement `stage-card-upper` gets for free at its own pair,
-- because there the stage index already lives in the target
-- (src/L/StageCardinal.lagda.md:322, `B.pair m (cnt m φ)`).
MissingIndex : Type (ℓ-suc ℓ)
MissingIndex = (α : S) (m : ⟪ α ⟫) → IsOrd α
             → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁
             → Σ[ f ∈ (⟪ α ⟫ → ⟪ ⟪ α ⟫↪ m ⟫) ]
                 ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y)

-- MEASURED: `MissingIndex` IS `CanonInj`.  The identity typechecks, so
-- the first ingredient of the transplant is the goal itself, and no
-- work has been moved.
missing-is-goal : MissingIndex → CanonInj
missing-is-goal x = x

-- The branch at the transplanted target.  `branch→member` above measures
-- that it carries the goal's own shape at every member of α.
MissingBranch : Type (ℓ-suc ℓ)
MissingBranch = (α : S) (m : ⟪ α ⟫) → IsOrd α
              → (k : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ k) ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫
