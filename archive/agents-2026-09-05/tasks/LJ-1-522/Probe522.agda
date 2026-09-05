{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.522] PROBE.  The definable powerset closure, from K being a
-- limit level.  It runs in agents/tasks/LJ-1-522/ and lands nothing in
-- src/.
--
--   W3, FIRST      the limit reading, written alone in runs/W3.agda and
--                  typechecked before this file existed.  IT DECOMPOSES.
--   DELIVERED      defPow-closed, the briefed obligation: the ninth row
--                  of [LJ-1.520]'s cost table, as a FRAME hypothesis
--                  discharged from the limit and never as a conjunct.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-522.Probe522 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ⊤̇; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-⊤; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import FOL.Manipulation.Parameters using ( lookup-map )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; Lset-out; Lset-mono
        ; Lset→isL; Lset-layer; layer-trans )
open import L.Absoluteness {ℓ} using ( InL; liftFo; Δ₀-liftFo; transferFo )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; 𝒟ₒ→isL )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import L.Coding.Environment {ℓ} using ( env; tag0At; Δ₀-tag0At; tag0At-adequate )
open import L.Coding.Powerset {ℓ} lem
  using ( envOne; DefBody; DefinesAt; DefinesAt-out; DefinesAt-in )

open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Vec using ( lookup; map; _∷_; [] )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV; ω; ω-empty; ω-next )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- SECTION 1.  THE LIMIT LEVEL, AND W3.
--
-- The tower has NO separate limit constructor: one equation covers zero,
-- successors and limits at once (src/L/Constructible.lagda.md:16), so a
-- limit is said of the INDEX and not of the stage.  W3 measured that a
-- limit index decomposes the stage into the earlier stages; this is that
-- file's statement, restated here so the obligation can consume it.
-- ---------------------------------------------------------------------
IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ α ⟩
          × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

limit-union : (α : V ℓ) → IsLimit α → (x : V ℓ) → ⟨ x ∈ Lset α ⟩
            → ∥ Σ[ δ ∈ V ℓ ] (IsOrd δ × ⟨ δ ∈ α ⟩ × ⟨ x ∈ Lset δ ⟩) ∥₁
limit-union α (oα , (_ , sc)) x x∈Lα = PT.map step (Lset-out α x x∈Lα)
  where
  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ α ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
       → Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ σ ∈ α ⟩ × ⟨ x ∈ Lset σ ⟩)
  step (δ , (δ∈α , x∈𝒟ₒδ)) =
      sucV δ
    , ( suc-ord (mem-ord {A = α} oα δ δ∈α)
      , ( sc δ δ∈α
        , subst (λ u → ⟨ x ∈ u ⟩) (sym (Lset-suc δ)) x∈𝒟ₒδ ) )

-- Two members of a limit level are members of ONE earlier level.  This
-- is where the linear order on the ordinals is spent, and it is the only
-- classical step this file adds.
twoBelow : (α : V ℓ) → IsLimit α → (a b : V ℓ)
         → ⟨ a ∈ Lset α ⟩ → ⟨ b ∈ Lset α ⟩
         → ∥ Σ[ τ ∈ V ℓ ]
             (IsOrd τ × ⟨ τ ∈ α ⟩ × ⟨ a ∈ Lset τ ⟩ × ⟨ b ∈ Lset τ ⟩) ∥₁
twoBelow α lim a b a∈ b∈ =
  PT.rec2 squash₁ merge (limit-union α lim a a∈) (limit-union α lim b b∈)
  where
  Goal : Type (ℓ-suc ℓ)
  Goal = Σ[ τ ∈ V ℓ ] (IsOrd τ × ⟨ τ ∈ α ⟩ × ⟨ a ∈ Lset τ ⟩ × ⟨ b ∈ Lset τ ⟩)
  merge : Σ[ δ ∈ V ℓ ] (IsOrd δ × ⟨ δ ∈ α ⟩ × ⟨ a ∈ Lset δ ⟩)
        → Σ[ ε ∈ V ℓ ] (IsOrd ε × ⟨ ε ∈ α ⟩ × ⟨ b ∈ Lset ε ⟩)
        → ∥ Goal ∥₁
  merge (δ , (oδ , (δ∈α , a∈δ))) (ε , (oε , (ε∈α , b∈ε))) =
    ∣ Sum.rec
        (λ δ∈ε → ε , (oε , (ε∈α , (Lset-mono {α = ε} {β = δ} δ∈ε a∈δ , b∈ε))))
        (Sum.rec
          (λ δ≡ε → ε , (oε , (ε∈α ,
            (subst (λ u → ⟨ a ∈ Lset u ⟩) δ≡ε a∈δ , b∈ε))))
          (λ ε∈δ → δ , (oδ , (δ∈α ,
            (a∈δ , Lset-mono {α = δ} {β = ε} ε∈δ b∈ε)))))
        (ord-tri δ oδ ε oε) ∣₁

-- NOT VACUOUS.  ω is a limit level, so the hypothesis of the obligation
-- is inhabited and the obligation is not true by an empty antecedent.
ω-IsLimit : IsLimit ω
ω-IsLimit =
    ω-ord
  , ( ∈∈ₛ {a = ∅} {b = ω} .snd ω-empty
    , (λ β β∈ω → ∈∈ₛ {a = sucV β} {b = ω} .snd
        (ω-next β (∈∈ₛ {a = β} {b = ω} .fst β∈ω))) )

-- A member of the definable powerset of an EARLIER level is a member of
-- the limit level.  This is the whole reason the frame hypothesis can be
-- discharged, and it is Lset-suc followed by the successor closure.
closeAt : (α : V ℓ) → IsLimit α → (τ : V ℓ) → ⟨ τ ∈ α ⟩
        → (D : V ℓ) → ⟨ D ∈ 𝒟ₒ (Lset τ) ⟩ → ⟨ D ∈ Lset α ⟩
closeAt α (_ , (_ , sc)) τ τ∈α D D∈ =
  Lset-mono {α = α} {β = sucV τ} (sc τ τ∈α)
    (subst (λ u → ⟨ D ∈ u ⟩) (sym (Lset-suc τ)) D∈)

-- ---------------------------------------------------------------------
-- SECTION 2.  "THE SET AT e IS THE ONE-ENTRY ENVIRONMENT OF THE SET AT
-- x", AS A Δ₀ FORMULA WITH NO CONSTANT AND NO OUTER BOUND.
--
-- This is what makes the closure a SEPARATION rather than a definable
-- powerset.  The tree already carries the Kuratowski pair of the empty
-- set as a Δ₀ reader over the hierarchy (tag0At,
-- src/L/Coding/Environment.lagda.md:336-339, Δ₀ at :348), so the only
-- new syntax is the singleton wrapper: a one-entry environment is the
-- SINGLETON of the entry (src/L/Coding/Environment.lagda.md:84-86), and
-- "singleton" is two bounded quantifiers over the set itself.  No bound
-- K is needed anywhere, which is what lets the formula travel to a
-- STAGE rather than to the carrier.
-- ---------------------------------------------------------------------
private
  tagB : ∀ {n} (s x : Fin n) → BoundedFo InL (tag0At s x)
  tagB s x = _

tag0AtL : ∀ {n} → Fin n → Fin n → Formula S n
tag0AtL s x = liftFo (tag0At s x) (tagB s x)

Δ₀-tag0AtL : ∀ {n} (s x : Fin n) → Δ₀ (tag0AtL s x)
Δ₀-tag0AtL s x = Δ₀-liftFo (tagB s x) (Δ₀-tag0At s x)

private
  tag0AtL-eq : ∀ {n} (s x : Fin n) (γ : S ^ n)
             → (γ ⊨ tag0AtL s x)
               ≡ ((lookup s (map fst γ) ≡ pr ∅ (lookup x (map fst γ)))
                  , setIsSet _ _)
  tag0AtL-eq s x γ =
      transferFo (tag0At s x) (tagB s x) (Δ₀-tag0At s x) γ
    ∙ tag0At-adequate s x (map fst γ)

tag0AtL-out : ∀ {n} (s x : Fin n) (γ : S ^ n)
            → ⟨ γ ⊨ tag0AtL s x ⟩
            → fst (lookup s γ) ≡ pr ∅ (fst (lookup x γ))
tag0AtL-out s x γ h =
  subst2 (λ a b → a ≡ pr ∅ b) (lookup-map fst γ s) (lookup-map fst γ x)
    (subst ⟨_⟩ (tag0AtL-eq s x γ) h)

tag0AtL-in : ∀ {n} (s x : Fin n) (γ : S ^ n)
           → fst (lookup s γ) ≡ pr ∅ (fst (lookup x γ))
           → ⟨ γ ⊨ tag0AtL s x ⟩
tag0AtL-in s x γ q =
  subst ⟨_⟩ (sym (tag0AtL-eq s x γ))
    (subst2 (λ a b → a ≡ pr ∅ b)
      (sym (lookup-map fst γ s)) (sym (lookup-map fst γ x)) q)

-- The one-entry environment, read off its own members.
private
  readEntry : (v y : V ℓ) → ⟨ y ∈ envOne v ⟩ → y ≡ pr ∅ v
  readEntry v y = PT.rec (setIsSet y (pr ∅ v))
    (λ { (lift zero , q) → sym q ; (lift (suc ()) , _) })

  entry∈ : (v y : V ℓ) → y ≡ pr ∅ v → ⟨ y ∈ envOne v ⟩
  entry∈ v y q = ∣ lift zero , sym q ∣₁

envOneL : ∀ {n} → Fin n → Fin n → Formula S n
envOneL e x = ∀̇∈ (var e) (tag0AtL zero (suc x)) ∧̇ ∃̇∈ (var e) ⊤̇

Δ₀-envOneL : ∀ {n} (e x : Fin n) → Δ₀ (envOneL e x)
Δ₀-envOneL e x = δ-∧ (δ-∀∈ (Δ₀-tag0AtL zero (suc x))) (δ-∃∈ δ-⊤)

envOneL-out : ∀ {n} (e x : Fin n) (γ : S ^ n) → ⟨ γ ⊨ envOneL e x ⟩
            → fst (lookup e γ) ≡ envOne (fst (lookup x γ))
envOneL-out e x γ (hall , hne) =
  extensionalV {a = fst (lookup e γ)} {b = envOne v} pt
  where
  E : V ℓ
  E = fst (lookup e γ)

  v : V ℓ
  v = fst (lookup x γ)

  entryOf : (y : V ℓ) → ⟨ y ∈ E ⟩ → y ≡ pr ∅ v
  entryOf y y∈E = tag0AtL-out zero (suc x) (yS ∷ γ) (hall yS y∈E)
    where
    yS : S
    yS = y , isL-trans {x = E} {y = y} y∈E (snd (lookup e γ))

  hasEntry : ⟨ pr ∅ v ∈ E ⟩
  hasEntry = PT.rec (snd (pr ∅ v ∈ E))
    (λ { (u , (u∈E , _)) → subst (λ w → ⟨ w ∈ E ⟩) (entryOf (fst u) u∈E) u∈E })
    hne

  pt : (y : V ℓ) → (y ∈ E) ≡ (y ∈ envOne v)
  pt y = ⇔toPath fwd bwd
    where
    fwd : ⟨ y ∈ E ⟩ → ⟨ y ∈ envOne v ⟩
    fwd y∈E = entry∈ v y (entryOf y y∈E)

    bwd : ⟨ y ∈ envOne v ⟩ → ⟨ y ∈ E ⟩
    bwd y∈ = subst (λ w → ⟨ w ∈ E ⟩) (sym (readEntry v y y∈)) hasEntry

envOneL-in : ∀ {n} (e x : Fin n) (γ : S ^ n)
           → fst (lookup e γ) ≡ envOne (fst (lookup x γ))
           → ⟨ γ ⊨ envOneL e x ⟩
envOneL-in e x γ q = hall , hne
  where
  E : V ℓ
  E = fst (lookup e γ)

  v : V ℓ
  v = fst (lookup x γ)

  hall : (u : S) → ⟨ fst u ∈ E ⟩ → ⟨ (u ∷ γ) ⊨ tag0AtL zero (suc x) ⟩
  hall u u∈E = tag0AtL-in zero (suc x) (u ∷ γ)
    (readEntry v (fst u) (subst (λ w → ⟨ fst u ∈ w ⟩) q u∈E))

  entry∈E : ⟨ pr ∅ v ∈ E ⟩
  entry∈E = subst (λ w → ⟨ pr ∅ v ∈ w ⟩) (sym q) (entry∈ v (pr ∅ v) refl)

  hne : ⟨ ⋁ S (λ u → (u ∈ˢ lookup e γ) ⊓ ⊤) ⟩
  hne = ∣ (pr ∅ v , isL-trans {x = E} {y = pr ∅ v} entry∈E (snd (lookup e γ)))
        , (entry∈E , tt*) ∣₁

-- ---------------------------------------------------------------------
-- SECTION 3.  SEPARATION AT A STAGE, WITH THE STAGE EXPOSED.
--
-- src/L/Axioms/Separation.lagda.md:273-320 already carves a Δ₀ subset of
-- a member of a stage, but it returns `isContr (SetOf …)` and the stage
-- is spent inside.  This task needs the stage: the whole discharge is
-- "the carved set lands one stage up, and one stage up is still below
-- the limit".  So the same body is rerun here with `carve ψ` and its
-- own `carve∈𝒟ₒ` as the return value, and nothing else changes.
-- ---------------------------------------------------------------------
module Sep (τ : V ℓ) (oτ : IsOrd τ) where
  open AtStage τ oτ

  private
    memberIsL : (m : ⟪ Lset τ ⟫) → ⟨ isL (⟪ Lset τ ⟫↪ m) ⟩
    memberIsL m = Lset→isL τ oτ (⟪ Lset τ ⟫↪ m)
      (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m} {b = Lset τ} .snd (∈ₛ⟪ Lset τ ⟫↪ m))

  carveSet : (a : S) (fa∈τ : ⟨ fst a ∈ Lset τ ⟩)
             (φ : Formula S 1) (h : BoundedFo Below φ) (dφ : Δ₀ φ)
           → Σ[ D ∈ V ℓ ]
               ( ⟨ D ∈ 𝒟ₒ (Lset τ) ⟩
               × (((y : S) → ⟨ fst y ∈ D ⟩
                    → ⟨ fst y ∈ fst a ⟩ × ⟨ (y ∷ []) ⊨ φ ⟩)
               × ((y : S) → ⟨ fst y ∈ fst a ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩
                    → ⟨ fst y ∈ D ⟩)) )
  carveSet a fa∈τ φ h dφ = carve ψ , (carve∈𝒟ₒ ψ , (fwd , bwd))
    where
    mₐ = ∈-asFiber {a = fst a} {b = Lset τ} fa∈τ .fst
    qₐ : ⟪ Lset τ ⟫↪ mₐ ≡ fst a
    qₐ = ∈-asFiber {a = fst a} {b = Lset τ} fa∈τ .snd

    ψ : Formula ⟪ Lset τ ⟫ 1
    ψ = (var zero ∈̇ con mₐ) ∧̇ RL.liftFo φ h

    fwd : (y : S) → ⟨ fst y ∈ carve ψ ⟩
        → ⟨ fst y ∈ fst a ⟩ × ⟨ (y ∷ []) ⊨ φ ⟩
    fwd y y∈ = fy∈fa , yφ
      where
      fy∈Lτ = carve⊆ ψ (fst y) y∈
      m = ∈-asFiber {a = fst y} {b = Lset τ} fy∈Lτ .fst
      q : ⟪ Lset τ ⟫↪ m ≡ fst y
      q = ∈-asFiber {a = fst y} {b = Lset τ} fy∈Lτ .snd
      xL = memberIsL m
      m∈ : ⟨ ⟪ Lset τ ⟫↪ m ∈ carve ψ ⟩
      m∈ = subst (λ w → ⟨ w ∈ carve ψ ⟩) (sym q) y∈
      dk = carveOut mₐ φ h dφ m xL m∈
      fy∈fa = subst (λ w → ⟨ fst y ∈ w ⟩) qₐ
        (subst (λ w → ⟨ w ∈ ⟪ Lset τ ⟫↪ mₐ ⟩) q (dk .fst))
      yφ = ⊨-transport φ dφ (⟪ Lset τ ⟫↪ m , xL) y q (dk .snd)

    bwd : (y : S) → ⟨ fst y ∈ fst a ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩
        → ⟨ fst y ∈ carve ψ ⟩
    bwd y fy∈fa yφ = subst (λ w → ⟨ w ∈ carve ψ ⟩) q m∈
      where
      fy∈Lτ = layer-trans (Lset-layer τ) {x = fst a} {y = fst y} fy∈fa fa∈τ
      m = ∈-asFiber {a = fst y} {b = Lset τ} fy∈Lτ .fst
      q : ⟪ Lset τ ⟫↪ m ≡ fst y
      q = ∈-asFiber {a = fst y} {b = Lset τ} fy∈Lτ .snd
      xL = memberIsL m
      p₁ : ⟨ ⟪ Lset τ ⟫↪ m ∈ ⟪ Lset τ ⟫↪ mₐ ⟩
      p₁ = subst (λ w → ⟨ w ∈ ⟪ Lset τ ⟫↪ mₐ ⟩) (sym q)
        (subst (λ w → ⟨ fst y ∈ w ⟩) (sym qₐ) fy∈fa)
      p₂ : ⟨ ((⟪ Lset τ ⟫↪ m , xL) ∷ []) ⊨ φ ⟩
      p₂ = ⊨-transport φ dφ y (⟪ Lset τ ⟫↪ m , xL) (sym q) yφ
      m∈ : ⟨ ⟪ Lset τ ⟫↪ m ∈ carve ψ ⟩
      m∈ = carveIn mₐ φ h dφ m xL (p₁ , p₂)

-- ---------------------------------------------------------------------
-- SECTION 4.  THE SEPARATING FORMULA, AT ARITY ONE WITH THE ENVIRONMENT
-- SET AS ITS ONLY CONSTANT.
-- ---------------------------------------------------------------------
envInAt : S → Formula S 1
envInAt V' = ∃̇∈ (con V') (envOneL zero (suc zero))

Δ₀-envInAt : (V' : S) → Δ₀ (envInAt V')
Δ₀-envInAt V' = δ-∃∈ (Δ₀-envOneL zero (suc zero))

envInAt-out : (V' y : S) → ⟨ (y ∷ []) ⊨ envInAt V' ⟩
            → ⟨ envOne (fst y) ∈ fst V' ⟩
envInAt-out V' y = PT.rec (snd (envOne (fst y) ∈ fst V'))
  (λ { (E , (E∈V , hE)) →
       subst (λ u → ⟨ u ∈ fst V' ⟩)
         (envOneL-out zero (suc zero) (E ∷ y ∷ []) hE) E∈V })

envInAt-in : (V' y : S) → ⟨ envOne (fst y) ∈ fst V' ⟩
           → ⟨ (y ∷ []) ⊨ envInAt V' ⟩
envInAt-in V' y h = ∣ ES , (h , envOneL-in zero (suc zero) (ES ∷ y ∷ []) refl) ∣₁
  where
  ES : S
  ES = envOne (fst y)
     , isL-trans {x = fst V'} {y = envOne (fst y)} h (snd V')

-- ---------------------------------------------------------------------
-- THE OBLIGATION.
--
-- "K is closed under the definable powerset of its members": every
-- definable subset of a member of K, with a code and an environment in
-- K, is a member of K, discharged from K being a limit level.  It is a
-- FRAME hypothesis: K is a VALUE here, not a slot of a formula, which
-- is exactly why the circularity [LJ-1.520] measured
-- (agents/tasks/LJ-1-520/lj-1.520-report.md:262) does not arise.
--
-- The leaf's own vocabulary is used and nothing is restated: `DefBody w`
-- is the delivered three-conjunct code-set description
-- (src/L/Coding/Powerset.lagda.md:437-440), `z` is the subset, `c` the
-- code and `v` the recorded satisfaction set.
-- ---------------------------------------------------------------------
defPow-closed-noCode :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (w K : Fin n) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → (z c v : S)
  → ⟨ fst v ∈ fst (lookup K γ) ⟩
  → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩
  → ⟨ fst z ∈ fst (lookup K γ) ⟩
defPow-closed-noCode α lim w K γ qK W∈K z c v v∈K hDefBody =
  subst (λ u → ⟨ fst z ∈ u ⟩) (sym qK)
    (PT.rec (snd (fst z ∈ Lset α)) go (twoBelow α lim W (fst v) W∈Lα v∈Lα))
  where
  W : V ℓ
  W = fst (lookup w γ)

  W∈Lα : ⟨ W ∈ Lset α ⟩
  W∈Lα = subst (λ u → ⟨ W ∈ u ⟩) qK W∈K

  v∈Lα : ⟨ fst v ∈ Lset α ⟩
  v∈Lα = subst (λ u → ⟨ fst v ∈ u ⟩) qK v∈K

  δ : S ^ (suc (suc (suc _)))
  δ = v ∷ c ∷ z ∷ γ

  hD : ⟨ δ ⊨ DefinesAt (suc (suc zero)) (suc (suc (suc w))) zero ⟩
  hD = hDefBody .snd .snd

  mem-out : (u : S) → ⟨ fst u ∈ fst z ⟩
          → ⟨ fst u ∈ W ⟩ × ⟨ envOne (fst u) ∈ fst v ⟩
  mem-out = DefinesAt-out (suc (suc zero)) (suc (suc (suc w))) zero δ hD

  mem-in : (u : S) → ⟨ fst u ∈ W ⟩ × ⟨ envOne (fst u) ∈ fst v ⟩
         → ⟨ fst u ∈ fst z ⟩
  mem-in = DefinesAt-in (suc (suc zero)) (suc (suc (suc w))) zero δ hD

  go : Σ[ τ ∈ V ℓ ]
         (IsOrd τ × ⟨ τ ∈ α ⟩ × ⟨ W ∈ Lset τ ⟩ × ⟨ fst v ∈ Lset τ ⟩)
     → ⟨ fst z ∈ Lset α ⟩
  go (τ , (oτ , (τ∈α , (W∈Lτ , v∈Lτ)))) =
    closeAt α lim τ τ∈α (fst z)
      (subst (λ u → ⟨ u ∈ 𝒟ₒ (Lset τ) ⟩) D≡z D∈)
    where
    cs = Sep.carveSet τ oτ (lookup w γ) W∈Lτ
           (envInAt v) (v∈Lτ , _) (Δ₀-envInAt v)

    D : V ℓ
    D = cs .fst

    D∈ : ⟨ D ∈ 𝒟ₒ (Lset τ) ⟩
    D∈ = cs .snd .fst

    DisL : ⟨ isL D ⟩
    DisL = 𝒟ₒ→isL τ oτ D D∈

    D≡z : D ≡ fst z
    D≡z = extensionalV {a = D} {b = fst z} pt
      where
      pt : (y : V ℓ) → (y ∈ D) ≡ (y ∈ fst z)
      pt y = ⇔toPath f g
        where
        f : ⟨ y ∈ D ⟩ → ⟨ y ∈ fst z ⟩
        f y∈D = mem-in yS (r .fst , envInAt-out v yS (r .snd))
          where
          yS : S
          yS = y , isL-trans {x = D} {y = y} y∈D DisL
          r = cs .snd .snd .fst yS y∈D

        g : ⟨ y ∈ fst z ⟩ → ⟨ y ∈ D ⟩
        g y∈z = cs .snd .snd .snd yS (r .fst) (envInAt-in v yS (r .snd))
          where
          yS : S
          yS = y , isL-trans {x = fst z} {y = y} y∈z (snd z)
          r = mem-out yS y∈z

-- THE BRIEFED STATEMENT, with the code's membership in K carried as the
-- brief writes it.  MEASURED: that hypothesis is never consumed.  The
-- term above inhabits the same type without it, and this one only
-- forgets the extra argument.
defPow-closed :
    (α : V ℓ) → IsLimit α
  → ∀ {n} (w K : Fin n) (γ : S ^ n)
  → fst (lookup K γ) ≡ Lset α
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → (z c v : S)
  → ⟨ fst c ∈ fst (lookup K γ) ⟩
  → ⟨ fst v ∈ fst (lookup K γ) ⟩
  → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩
  → ⟨ fst z ∈ fst (lookup K γ) ⟩
defPow-closed α lim w K γ qK W∈K z c v c∈K v∈K hDefBody =
  defPow-closed-noCode α lim w K γ qK W∈K z c v v∈K hDefBody
