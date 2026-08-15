{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.321] PROBE.  Is there a `2-Constant` map `Wat α → sq α`?
--
-- THE QUESTION.  `sq α` is a SET (agents/tasks/LJ-1-319/SqIsSet.agda,
-- re-run green here).  So by `trunc→Set≃`
-- (Cubical/HITs/PropositionalTruncation/Properties.agda:225, exported
-- at :268) the maps `∥ Wat α ∥₁ → sq α` ARE the `2-Constant` maps
-- `Wat α → sq α`.  This file measures what builds one.
--
-- WHAT THIS FILE MEASURES, in order:
--
--   PART 1  A map that factors through ANY proposition is `2-Constant`.
--           So the `2-Constant` obligation is never about the witness
--           `Wat α`.  It is about split support for the TARGET.
--   PART 2  The member half of `Wat α` discharges by `leastOf`, with no
--           new principle.  `leastWat` below.  MEASURED.
--   PART 3  The residue after PART 2, named exactly: `CanonInj`.  Given
--           it, the `2-Constant` map EXISTS and is built here.
--   PART 4  The naive map is NOT `2-Constant`.  A transposition of two
--           image points refutes it, at every site that holds two
--           distinct members.  MEASURED.
--   PART 5  A well-order on `sq α` gives the map outright, with no
--           `Wat` at all, and `pullOrder` reduces that well-order to an
--           injection of `sq α` into any well-ordered carrier.  That
--           injection is the ambient-to-code crossing.
--   PART 6  `BoundedToCode → InjData`, the composite `[LJ-1.314]`
--           section 1.4 left INFERRED.
--
-- Nothing lands.  Tracked probe.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-321.Door {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; ordSWO )
open import L.Absorption {ℓ} lem using ( absorbs )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.Choice.Step {ℓ} lem using ( pullOrder )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )

-- The premise, re-run inside this build (C-45: I compile it, I do not
-- quote it).
open import LJ-1-319.SqIsSet {ℓ} lem using ( sq-set; carrier-set )

-- The coded route, read and re-compiled, never edited.
open import LJ-1-314.CodeUntrunc {ℓ} lem using ( BoundedToCode; bridge→data )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Foundations.Function using ( 2-Constant )
open import Cubical.Data.Sigma using ( _×_; ΣPathP )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Unit using ( Unit; tt; isPropUnit )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; isPropPropTrunc; squash₁; rec→Set )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE DELIVERED SHAPES, copied verbatim with provenance.
--
--   `Wat`, `ord-mem-emb` and `sq-transport` are
--   agents/tasks/LJ-1-305/Untruncated.agda:76-108.  They are copied and
--   not imported so that this probe compiles one small file.  Nothing
--   here changes them.
-- =====================================================================

ord-mem-emb : (a b : V ℓ) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
ord-mem-emb a b ob a∈b = f , inj
  where
  f : ⟪ a ⟫ → ⟪ b ⟫
  f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst
  inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
  inj m n e = ↪-inj {a = a}
    ( sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
    ∙ cong (⟪ b ⟫↪) e
    ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd )

sq-transport : (α δ : V ℓ) → IsOrd α → ⟨ δ ∈ˢ α ⟩
             → ⟪ α ⟫ ↪ ⟪ δ ⟫ → sq δ → sq α
sq-transport α δ oα δ∈α e (g , gi) = h , hinj
  where
  include : ⟪ δ ⟫ ↪ ⟪ α ⟫
  include = ord-mem-emb δ α oα δ∈α
  h : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  h (a , b) = include .fst (g (e .fst a , e .fst b))
  hinj : (p q : ⟪ α ⟫ × ⟪ α ⟫) → h p ≡ h q → p ≡ q
  hinj (a₁ , a₂) (b₁ , b₂) eq =
    ΣPathP ( e .snd a₁ b₁ (cong fst pq) , e .snd a₂ b₂ (cong snd pq) )
    where
    gh : g (e .fst a₁ , e .fst a₂) ≡ g (e .fst b₁ , e .fst b₂)
    gh = include .snd (g (e .fst a₁ , e .fst a₂))
                     (g (e .fst b₁ , e .fst b₂)) eq
    pq : (e .fst a₁ , e .fst a₂) ≡ (e .fst b₁ , e .fst b₂)
    pq = gi _ _ gh

Wat : (α : V ℓ) → Type (ℓ-suc ℓ)
Wat α = Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ α ⟩ × (⟪ α ⟫ ↪ ⟪ δ ⟫))

InjData : Type (ℓ-suc ℓ)
InjData = (α : V ℓ) → IsOrd α → ∥ Wat α ∥₁ → Wat α

-- =====================================================================
-- PART 1.  A MAP THAT FACTORS THROUGH A PROPOSITION IS `2-Constant`.
--
--   This is the whole of the `2-Constant` side, and it says that the
--   obligation is never about `Wat α`.  Any construction that reads
--   only the TRUNCATION of its input is `2-Constant` for free.
-- =====================================================================

factor-2Const : {ℓa ℓb ℓp : Level} {A : Type ℓa} {B : Type ℓb} {P : Type ℓp}
              → isProp P → (u : A → P) (v : P → B)
              → 2-Constant (λ a → v (u a))
factor-2Const pp u v x y = cong v (pp (u x) (u y))

-- The immediate corollary, at the site.  Any map out of `∥ Wat α ∥₁`
-- gives the `2-Constant` map, and by `rec→Set` the converse holds too.
untrunc→2Const : (α : V ℓ) (s : ∥ Wat α ∥₁ → sq α)
               → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
untrunc→2Const α s =
  (λ w → s ∣ w ∣₁) , factor-2Const isPropPropTrunc ∣_∣₁ s

2Const→untrunc : (α : V ℓ) (f : Wat α → sq α) → 2-Constant f
               → ∥ Wat α ∥₁ → sq α
2Const→untrunc α f kf = rec→Set (sq-set α) f kf

-- =====================================================================
-- PART 2.  THE MEMBER HALF DISCHARGES.  MEASURED.
--
--   `leastOf` over `α`'s own well-order takes the LEAST member index
--   that α injects into.  The predicate is the TRUNCATED injection, an
--   hProp, which is all `leastOf` allows
--   (src/L/WellOrder/Base.lagda.md:158-161).  This is the delivered
--   `LeastCardInjL` pattern (src/L/Cardinal.lagda.md:116-134) at α
--   itself rather than at `sucV α`.
--
--   Note the shape: `leastWat` reads only `∥ Wat α ∥₁`.  So by PART 1
--   every construction built on it is `2-Constant` for free.
-- =====================================================================

leastWat : (α : V ℓ) (oα : IsOrd α) → ∥ Wat α ∥₁
         → Σ[ m ∈ ⟪ α ⟫ ] ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁
leastWat α oα h = fst least , fst (snd least)
  where
  -- The order is SEALED: the medicine of `LeastCardInjL`
  -- (src/L/Cardinal.lagda.md:85-92) and of `esc-wit`
  -- (agents/tasks/LJ-1-305/Untruncated.agda:135-137).
  opaque
    wα : SWO ⟪ α ⟫
    wα = ordSWO α oα

  Inj : ⟪ α ⟫ → hProp ℓ
  Inj m = ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁ , squash₁

  nonempty : ∥ Σ[ m ∈ ⟪ α ⟫ ] ⟨ Inj m ⟩ ∥₁
  nonempty = PT.map
    (λ w → fiber α (fst (snd w)) .fst
         , subst (λ v → ∥ ⟪ α ⟫ ↪ ⟪ v ⟫ ∥₁)
                 (sym (fiber α (fst (snd w)) .snd))
                 ∣ snd (snd w) ∣₁)
    h

  least : Σ[ m ∈ ⟪ α ⟫ ] IsLeast wα Inj m
  least = leastOf wα lem Inj nonempty

-- =====================================================================
-- PART 3.  THE RESIDUE, NAMED EXACTLY.
--
--   After PART 2 the ONLY open term is a canonical injection at the
--   least member, built from the ordinal and NOT read off the witness.
--   `CanonInj` states it.  Given it, the `2-Constant` map is BUILT
--   below, with its `2-Constant` proof.
--
--   C-45: `CanonInj` is ASSUMED here.  Nothing below proves it.  The
--   point of the part is the REDUCTION, and the reduction is the term.
-- =====================================================================

CanonInj : Type (ℓ-suc ℓ)
CanonInj = (α : V ℓ) (m : ⟪ α ⟫) → IsOrd α
         → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁ → ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫

-- The untruncated induction hypothesis of the descent, at members.
-- `stepU` (agents/tasks/LJ-1-305/Untruncated.agda:293) has exactly it.
IH : (α : V ℓ) → Type (ℓ-suc ℓ)
IH α = (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → sq δ

canon→step : CanonInj → (α : V ℓ) → IsOrd α → IH α → ∥ Wat α ∥₁ → sq α
canon→step ci α oα ih h =
  sq-transport α (⟪ α ⟫↪ m₀) oα (member α m₀)
    (ci α m₀ oα (snd got)) (ih (⟪ α ⟫↪ m₀) (member α m₀))
  where
  got = leastWat α oα h
  m₀ = fst got

-- THE MAP, WITH ITS `2-Constant` PROOF, conditional on `CanonInj`.
canon→door : CanonInj → (α : V ℓ) → IsOrd α → IH α
           → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
canon→door ci α oα ih = untrunc→2Const α (canon→step ci α oα ih)

-- HOW FAR THE ORDINAL MACHINERY REACHES.  MEASURED.
--
--   The tree builds exactly ONE canonical injection of a bigger carrier
--   into a smaller one, and it is the SUCCESSOR case: `absorbs`
--   (src/L/Absorption.lagda.md:613-616) returns
--   `⟪ sucV γ ⟫ ↪ ⟪ γ ⟫` from ordinal data alone, with no witness read.
--   The line below is that reading, and it typechecks.
--
--   MEASURED by census: no other term in `src/` returns an injection of
--   a carrier into the carrier of a MEMBER.  So `CanonInj` at a LIMIT
--   non-initial ordinal has no supplier, which is the wall the ruling
--   expected.
succCanon : (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ ω ⟩ → Empty.⊥)
          → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
          → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫
succCanon = absorbs

-- =====================================================================
-- PART 4.  THE NAIVE MAP IS NOT `2-Constant`.  MEASURED.
--
--   The naive map sends a witness to `sq-transport` at that witness.
--   Two injections that differ by a transposition of two image points
--   give two composites that differ at one argument.  Nothing about
--   `α`, `δ` or `sq δ` is used beyond two distinct points of `⟪ α ⟫`.
--
--   The transposition is `NotProp`'s `swap`
--   (agents/tasks/LJ-1-305/NotProp.agda:99-165) made generic in its two
--   points.  Every clause matches on a decision passed as an ARGUMENT,
--   never on a `with`-abstraction, because the `with` form exhausted an
--   8 GB heap at the original site (P-i, C-51).
-- =====================================================================

decV : (x y : V ℓ) → (x ≡ y) ⊎ ((x ≡ y) → Empty.⊥)
decV x y = lem ((x ≡ y) , setIsSet x y)

module Swap (δ : V ℓ) (p q : ⟪ δ ⟫) (p≢q : (p ≡ q) → Empty.⊥) where

  memInj : (m n : ⟪ δ ⟫) → (⟪ δ ⟫↪ m ≡ ⟪ δ ⟫↪ n) → m ≡ n
  memInj m n u = ↪-inj {a = δ} u

  Vp≢Vq : (⟪ δ ⟫↪ p ≡ ⟪ δ ⟫↪ q) → Empty.⊥
  Vp≢Vq u = p≢q (memInj p q u)

  Dec₀ : ⟪ δ ⟫ → Type (ℓ-suc ℓ)
  Dec₀ m = (⟪ δ ⟫↪ m ≡ ⟪ δ ⟫↪ p) ⊎ ((⟪ δ ⟫↪ m ≡ ⟪ δ ⟫↪ p) → Empty.⊥)

  Dec₁ : ⟪ δ ⟫ → Type (ℓ-suc ℓ)
  Dec₁ m = (⟪ δ ⟫↪ m ≡ ⟪ δ ⟫↪ q) ⊎ ((⟪ δ ⟫↪ m ≡ ⟪ δ ⟫↪ q) → Empty.⊥)

  d₀ : (m : ⟪ δ ⟫) → Dec₀ m
  d₀ m = decV (⟪ δ ⟫↪ m) (⟪ δ ⟫↪ p)

  d₁ : (m : ⟪ δ ⟫) → Dec₁ m
  d₁ m = decV (⟪ δ ⟫↪ m) (⟪ δ ⟫↪ q)

  swapBy : (m : ⟪ δ ⟫) → Dec₀ m → Dec₁ m → ⟪ δ ⟫
  swapBy m (inl _) _ = q
  swapBy m (inr _) (inl _) = p
  swapBy m (inr _) (inr _) = m

  swap : ⟪ δ ⟫ → ⟪ δ ⟫
  swap m = swapBy m (d₀ m) (d₁ m)

  swap-at-p : swap p ≡ q
  swap-at-p = go (d₀ p)
    where
    go : (u : Dec₀ p) → swapBy p u (d₁ p) ≡ q
    go (inl _) = refl
    go (inr nx) = Empty.rec (nx refl)

  swap-inj : (m n : ⟪ δ ⟫) → swap m ≡ swap n → m ≡ n
  swap-inj m n u = go (d₀ m) (d₀ n) (d₁ m) (d₁ n) u
    where
    go : (am : Dec₀ m) (an : Dec₀ n) (bm : Dec₁ m) (bn : Dec₁ n)
       → swapBy m am bm ≡ swapBy n an bn → m ≡ n
    go (inl x) (inl y) _ _ _ = memInj m n (x ∙ sym y)
    go (inl _) (inr _) _ (inl _) e = Empty.rec (Vp≢Vq (cong (⟪ δ ⟫↪) (sym e)))
    go (inl _) (inr _) _ (inr nb) e = Empty.rec (nb (cong (⟪ δ ⟫↪) (sym e)))
    go (inr _) (inl _) (inl _) _ e = Empty.rec (Vp≢Vq (cong (⟪ δ ⟫↪) e))
    go (inr _) (inl _) (inr nb) _ e = Empty.rec (nb (cong (⟪ δ ⟫↪) e))
    go (inr _) (inr _) (inl x) (inl y) _ = memInj m n (x ∙ sym y)
    go (inr _) (inr ny) (inl _) (inr _) e = Empty.rec (ny (cong (⟪ δ ⟫↪) (sym e)))
    go (inr nx) (inr _) (inr _) (inl _) e = Empty.rec (nx (cong (⟪ δ ⟫↪) e))
    go (inr _) (inr _) (inr _) (inr _) e = e

-- The twisted witness: post-compose the injection with the transposition
-- of the images of two distinct points.
twist : (α δ : V ℓ) (e : ⟪ α ⟫ ↪ ⟪ δ ⟫) (a₀ a₁ : ⟪ α ⟫)
      → ((a₀ ≡ a₁) → Empty.⊥) → ⟪ α ⟫ ↪ ⟪ δ ⟫
twist α δ e a₀ a₁ a₀≢a₁ = (λ x → S.swap (e .fst x)) , inj
  where
  im≢ : (e .fst a₀ ≡ e .fst a₁) → Empty.⊥
  im≢ u = a₀≢a₁ (e .snd a₀ a₁ u)
  module S = Swap δ (e .fst a₀) (e .fst a₁) im≢
  inj : (x y : ⟪ α ⟫) → S.swap (e .fst x) ≡ S.swap (e .fst y) → x ≡ y
  inj x y u = e .snd x y (S.swap-inj (e .fst x) (e .fst y) u)

-- THE REFUTATION.  If the naive family were `2-Constant`, the
-- transposition would fix the point it moves.
naive-not-2Const :
    (α δ : V ℓ) (oα : IsOrd α) (δ∈α : ⟨ δ ∈ˢ α ⟩) (sqδ : sq δ)
  → (e : ⟪ α ⟫ ↪ ⟪ δ ⟫) (a₀ a₁ : ⟪ α ⟫) (a₀≢a₁ : (a₀ ≡ a₁) → Empty.⊥)
  → 2-Constant (λ (w : ⟪ α ⟫ ↪ ⟪ δ ⟫) → sq-transport α δ oα δ∈α w sqδ)
  → Empty.⊥
naive-not-2Const α δ oα δ∈α sqδ e a₀ a₁ a₀≢a₁ kf =
  im≢ (sym fixed)
  where
  im≢ : (e .fst a₀ ≡ e .fst a₁) → Empty.⊥
  im≢ u = a₀≢a₁ (e .snd a₀ a₁ u)

  module S = Swap δ (e .fst a₀) (e .fst a₁) im≢

  e' : ⟪ α ⟫ ↪ ⟪ δ ⟫
  e' = twist α δ e a₀ a₁ a₀≢a₁

  include : ⟪ δ ⟫ ↪ ⟪ α ⟫
  include = ord-mem-emb δ α oα δ∈α

  -- The two composites agree, by the assumed `2-Constant`.
  same : sq-transport α δ oα δ∈α e sqδ ≡ sq-transport α δ oα δ∈α e' sqδ
  same = kf e e'

  -- Read off the value at the diagonal point `(a₀ , a₀)`.
  val : include .fst (sqδ .fst (e .fst a₀ , e .fst a₀))
      ≡ include .fst (sqδ .fst (S.swap (e .fst a₀) , S.swap (e .fst a₀)))
  val = cong (λ g → g (a₀ , a₀)) (cong fst same)

  inner : sqδ .fst (e .fst a₀ , e .fst a₀)
        ≡ sqδ .fst (S.swap (e .fst a₀) , S.swap (e .fst a₀))
  inner = include .snd _ _ val

  pair : (e .fst a₀ , e .fst a₀)
       ≡ (S.swap (e .fst a₀) , S.swap (e .fst a₀))
  pair = sqδ .snd _ _ inner

  fixed : e .fst a₁ ≡ e .fst a₀
  fixed = sym S.swap-at-p ∙ sym (cong fst pair)

-- THE NAIVE MAP ITSELF, in the brief's own words: the `sq-transport`
-- composite read off the witness.
naive : (α : V ℓ) → IsOrd α → IH α → Wat α → sq α
naive α oα ih w =
  sq-transport α (fst w) oα (fst (snd w)) (snd (snd w))
    (ih (fst w) (fst (snd w)))

-- MEASURED: `naive` is NOT `2-Constant`, at every site that carries a
-- witness and two distinct points.  Two witnesses with the SAME member
-- and injections differing by one transposition already break it.
naive-refuted : (α : V ℓ) (oα : IsOrd α) (ih : IH α)
              → (δ : V ℓ) (δ∈α : ⟨ δ ∈ˢ α ⟩) (e : ⟪ α ⟫ ↪ ⟪ δ ⟫)
              → (a₀ a₁ : ⟪ α ⟫) → ((a₀ ≡ a₁) → Empty.⊥)
              → 2-Constant (naive α oα ih) → Empty.⊥
naive-refuted α oα ih δ δ∈α e a₀ a₁ a₀≢a₁ kf =
  naive-not-2Const α δ oα δ∈α (ih δ δ∈α) e a₀ a₁ a₀≢a₁
    (λ w w' → kf (δ , δ∈α , w) (δ , δ∈α , w'))

-- =====================================================================
-- PART 5.  A WELL-ORDER ON `sq α` GIVES THE MAP OUTRIGHT.
--
--   This route never mentions `Wat`.  The descent already delivers
--   `∥ sq α ∥₁` at every α with NO new principle
--   (agents/tasks/LJ-1-305/Untruncated.agda:208-209, `SqI`).  A
--   well-order on `sq α` untruncates that directly, and PART 1 then
--   gives the `2-Constant` map for free.
--
--   `pullOrder` (src/L/Choice/Step.lagda.md:252-259) reduces the
--   well-order to an INJECTION of `sq α` into any well-ordered carrier.
--   Every SWO the tree builds carries `⟪ x ⟫`, `Mem (Lset β)`, `ℕ`,
--   `Name`, `New δ`, `Point n`, `Limit`, `SL`, or a product of those.
--   NONE carries a function type.  So the injection is the
--   ambient-to-code crossing and nothing smaller.
-- =====================================================================

Triv : {ℓa : Level} {A : Type ℓa} → A → hProp ℓ-zero
Triv _ = Unit , isPropUnit

-- Split support from a well-order.  Kraus, Escardó, Coquand and
-- Altenkirch, LMCS 13(1) 2017, Theorem 16, in the direction this tree
-- can use: a well-order gives a weakly constant endomap.
least-elt : {A : Type ℓ} → SWO {ℓ} A → ∥ A ∥₁ → A
least-elt w h = fst (leastOf w lem Triv (PT.map (λ a → a , tt) h))

-- Kraus, Escardó, Coquand and Altenkirch, Theorem 16, in the direction
-- this tree uses: a well-order gives a weakly constant endomap, and a
-- weakly constant endomap is what split support amounts to.
order→wconst : {A : Type ℓ} (w : SWO {ℓ} A)
             → 2-Constant (λ a → least-elt w ∣ a ∣₁)
order→wconst w = factor-2Const isPropPropTrunc ∣_∣₁ (least-elt w)

sq-split : (α : V ℓ) → SWO {ℓ} (sq α) → ∥ sq α ∥₁ → sq α
sq-split α w = least-elt w

-- And the `2-Constant` map, BUILT, with no `CanonInj` and no `Wat`.
order→door : (α : V ℓ) → SWO {ℓ} (sq α) → (Wat α → ∥ sq α ∥₁)
           → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
order→door α w t =
  (λ u → sq-split α w (t u))
  , factor-2Const isPropPropTrunc t (sq-split α w)

-- The reduction of the well-order to the crossing.
code→order : (α : V ℓ) {ℓc : Level} (C : Type ℓc) (w : SWO {ℓc} C)
           → (c : sq α → C) → ((u v : sq α) → c u ≡ c v → u ≡ v)
           → SWO {ℓ} (sq α)
code→order α C w c cinj = pullOrder (sq α) C w c cinj

-- =====================================================================
-- PART 6.  `BoundedToCode → InjData`.
--
--   `[LJ-1.314]` section 1.4 left this join INFERRED and priced it at
--   about 20 lines.  It is built here.  `leastWat` takes the member
--   half (PART 2) and `bridge→data`
--   (agents/tasks/LJ-1-314/CodeUntrunc.agda:150-155) takes the
--   injection at it.
--
--   ONE DEVIATION, stated: the composite needs `⟨ isL α ⟩`, which
--   `InjData` does not carry, because `bridge→data` speaks of `S`.  The
--   call site has it: `stepU` holds `isLα`
--   (agents/tasks/LJ-1-305/Untruncated.agda:293-316).
-- =====================================================================

InjDataL : Type (ℓ-suc ℓ)
InjDataL = (α : V ℓ) → IsOrd α → ⟨ isL α ⟩ → ∥ Wat α ∥₁ → Wat α

bounded→injdata : BoundedToCode → InjDataL
bounded→injdata btc α oα isLα h =
  ⟪ α ⟫↪ m₀ , member α m₀
  , bridge→data btc (α , isLα)
      (⟪ α ⟫↪ m₀ , isL-trans (member α m₀) isLα) (snd got)
  where
  got = leastWat α oα h
  m₀ = fst got

-- The unconditional reading of PART 6, for the record: under the
-- bounded crossing the descent's one data join closes with no new
-- principle, and by PART 1 the resulting map is `2-Constant`.
bounded→2Const : BoundedToCode → (α : V ℓ) → IsOrd α → ⟨ isL α ⟩ → IH α
               → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
bounded→2Const btc α oα isLα ih = untrunc→2Const α step
  where
  step : ∥ Wat α ∥₁ → sq α
  step h = sq-transport α (fst w) oα (fst (snd w)) (snd (snd w))
             (ih (fst w) (fst (snd w)))
    where
    w = bounded→injdata btc α oα isLα h

-- One import is kept live by this line alone: `carrier-set` witnesses
-- that the transposition of PART 4 acts on a SET, which is what makes
-- `sq-set` apply at all.
carrier-is-set : (α : V ℓ) → isSet ⟪ α ⟫
carrier-is-set = carrier-set
