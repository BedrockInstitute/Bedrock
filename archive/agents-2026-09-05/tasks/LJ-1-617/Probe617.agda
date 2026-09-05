{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.617]  DOES THE BILL EVER NEED THE PAIRING AT MODULE GRAIN.
--
-- VERDICT: GO.  The obligation `site-grain-suffices` is at section 8
-- below: from ingredient (iii) stated at the SITE the tree spends it
-- (ONE pairing function at ONE alpha, with its injectivity) and the
-- sibling hypothesis `absorbs`, it lands the exact type of
-- `code-inj` (src/L/BoundedSubset.lagda.md:1512-1513), the bill's only
-- consumer of the pairing's proof-only demand.  This file carries NO
-- hole and NO postulate in its final form, so every row is a
-- measurement.  Nothing lands in `src/`.
--
-- W3 WAS DONE FIRST, BY GREP, AND ITS COUNT IS IN THE REPORT
-- (lj-1.617-report.md, section `EVERY SPEND SITE`): the product `sq`
-- is applied at an ordinal at exactly TWO lines of `src/`, and only
-- ONE of them spends it at a fixed alpha
-- (src/L/BoundedSubset.lagda.md:1410).  The other
-- (src/L/StageCardinal.lagda.md:283) ranges over the band only
-- because `stage-card-upper` is an `∈-induction`, and the sole
-- consumer of that induction reads it at `gamma = alpha` and nowhere
-- else (src/L/BoundedSubset.lagda.md:1513).
--
-- THE RESTRUCTURE, AND IT IS ONE CHANGE.  The tree proves
-- `stage-card-upper` by an `∈-induction` whose predicate fixes the
-- TARGET at each step's own ordinal (`P alpha = ... ↪ ⟪ alpha ⟫`), so
-- each step's counting runs at that ordinal and needs the pairing
-- there.  This probe runs the SAME induction with the target FIXED AT
-- THE SITE alpha (`Q gamma = ... ↪ ⟪ alpha ⟫`): every step counts its
-- formulas into `⟪ alpha ⟫`, packs with the pairing at alpha, and
-- indexes each member ordinal of gamma into alpha.  The pairing is
-- then consumed at alpha ONLY.  Three consequences, all measured by
-- the rows below:
--   * no `L.Choice.Finite` (the tree's omega base, `FinInj`/`Tally`,
--     exists to inject FINITE stages into their own ordinal; with the
--     target fixed at alpha the same step covers them);
--   * no per-step infinity hypothesis: `Q gamma` demands only
--     `IsOrd gamma` and `gamma ∈ sucV alpha`;
--   * `L.StageCardinal` itself is NEVER imported.  Its `Bound` and
--     `OrdSWO` are copied verbatim at a generic carrier and fed the
--     site fiber, which is what section 2 and 3 do.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Caps are set and reported per run in
-- `runs/`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import L.Constructible using ( IsOrd; Lset )
open import LJ-1-594.runs.W3 using ( SqParam )
import Cubical.Data.Empty as Empty

module LJ-1-617.Probe617 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) (oα : IsOrd α)
  (α∉ω : ⟨ α ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
  (iii : Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
          ((u v : ⟪ α ⟫ × ⟪ α ⟫) → f u ≡ f v → u ≡ v)) where

open import FOL.Syntax using ( Formula )
open import FOL.Count {ℓ} using ( composed-count; code; shape-count-inj )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction; regularityV )
open import V.Presentation {ℓ} using ( fiber; member; ↪-inj )
open import V.Coding {ℓ} using ( #-inj′ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import L.Constructible {ℓ} using ( 𝒟ₒ; 𝒟ₒ-inv; Lset-out )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( #∈ω; numeral-ord; numeral-mem; mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; leastOf )
open import Cubical.Foundations.Prelude using ( J; transportRefl; substRefl; PathP; toPathP )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Data.Vec using ( Vec )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( _∪_; ⁅_⁆s )
open InfinitySet using ( ω; sucV; #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Ingredient (iii) at the SITE: one binary function with its
-- injectivity at one ordinal.  The telescope's `iii` states it inline;
-- this name is the same type by unfolding.  It is the value half of
-- `SqParam` at the site (the product applied, as at
-- src/L/BoundedSubset.lagda.md:1410) and it is the tree's own fiber
-- type `sq` (src/L/Ordinal/SquareLaw.lagda.md:685-688), under a third
-- name to keep the two `sq`s apart ([LJ-1.604]'s naming hazard).
SiteGrain : V ℓ → Type ℓ
SiteGrain β = Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
  ((u v : ⟪ β ⟫ × ⟪ β ⟫) → f u ≡ f v → u ≡ v)

-- =====================================================================
-- SECTION 1.  The injection type and its composition, both local, both
-- the tree's own shapes (src/L/StageCardinal.lagda.md:243-246 and
-- src/L/BoundedSubset.lagda.md:1365-1368).
-- =====================================================================

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- =====================================================================
-- SECTION 2.  THE TREE'S OWN `Bound`, COPIED VERBATIM AT A GENERIC
-- CARRIER.  Source: src/L/StageCardinal.lagda.md:69-241, module
-- `Bound`.  The copy is byte-faithful to the proof text; only the
-- module name and this comment differ.  It is copied because the
-- original sits inside the `L.StageCardinal` telescope, whose `sq`
-- parameter this probe refuses to pay: `Bound` itself never uses the
-- product, it takes ONE pairing at its own beta.
-- =====================================================================

module SiteBound (β : S) (oβ : IsOrd β) (infβ : ⟨ β ∈ˢ ω ⟩ → Empty.⊥)
                 (pairing : SiteGrain β) where

  pair : ⟪ β ⟫ → ⟪ β ⟫ → ⟪ β ⟫
  pair x y = fst pairing (x , y)

  pair-inj : (x y x' y' : ⟪ β ⟫) → pair x y ≡ pair x' y' → (x ≡ x') × (y ≡ y')
  pair-inj x y x' y' e = cong fst p , cong snd p
    where
    p : (x , y) ≡ (x' , y')
    p = snd pairing (x , y) (x' , y') e

  numeral∈β : (n : ℕ) → ⟨ (# n) ∈ˢ β ⟩
  numeral∈β n = go (ord-tri (# n) (numeral-ord n) β oβ)
    where
    go : (⟨ (# n) ∈ˢ β ⟩ ⊎ (((# n) ≡ β) ⊎ ⟨ β ∈ˢ (# n) ⟩)) → ⟨ (# n) ∈ˢ β ⟩
    go (inl h) = h
    go (inr (inl q)) =
      Empty.rec (infβ (subst (λ w → ⟨ w ∈ˢ ω ⟩) q (#∈ω n)))
    go (inr (inr h)) = Empty.rec (infβ (numeral-mem n β h))

  numeral : ℕ → ⟪ β ⟫
  numeral n = fiber β {x = # n} (numeral∈β n) .fst

  numeral-inj : (n m : ℕ) → numeral n ≡ numeral m → n ≡ m
  numeral-inj n m e = #-inj′ (sym (fiber β {x = # n} (numeral∈β n) .snd)
    ∙ cong (⟪ β ⟫↪) e ∙ fiber β {x = # m} (numeral∈β m) .snd)

  code-stable : (k k' : ℕ) (p : k' ≡ k) (ψ : Formula (⊥* {ℓ}) k')
              → code (subst (Formula (⊥* {ℓ})) p ψ) ≡ code ψ
  code-stable k k' p ψ =
    J (λ k p → code (subst (Formula (⊥* {ℓ})) p ψ) ≡ code ψ)
      (cong code (transportRefl ψ)) p

  tuple-g : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
          → (k : ℕ) → Vec K k → ⟪ β ⟫
  tuple-g g zero [] = numeral 0
  tuple-g g (suc k) (x ∷ xs) = pair (fst g x) (tuple-g g k xs)

  tuple-g-inj : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
              → (k : ℕ) (xs ys : Vec K k) → tuple-g g k xs ≡ tuple-g g k ys → xs ≡ ys
  tuple-g-inj g zero [] [] _ = refl
  tuple-g-inj g (suc k) (x ∷ xs) (y ∷ ys) e = cong₂ _∷_ xeq (tuple-g-inj g k xs ys xs≡ys)
    where
    p : (fst g x , tuple-g g k xs) ≡ (fst g y , tuple-g g k ys)
    p = snd pairing (fst g x , tuple-g g k xs) (fst g y , tuple-g g k ys) e
    xeq : x ≡ y
    xeq = snd g x y (cong fst p)
    xs≡ys : tuple-g g k xs ≡ tuple-g g k ys
    xs≡ys = cong snd p

  tuple-g-stable : (K : Type ℓ) (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                 → (k k' : ℕ) (p : k' ≡ k) (cs : Vec K k')
                 → tuple-g {K} g k (subst (Vec K) p cs) ≡ tuple-g {K} g k' cs
  tuple-g-stable K g k k' p cs =
    J (λ k p → tuple-g {K} g k (subst (Vec K) p cs) ≡ tuple-g {K} g k' cs)
      (cong (tuple-g {K} g k') (transportRefl cs)) p

  count-bound : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
              → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k)) → ⟪ β ⟫
  count-bound g (k , (ψ , (n , cs))) =
    pair (numeral k) (pair (pair (numeral (code ψ)) (numeral n)) (tuple-g g k cs))

  count-bound-inj : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                  → (x y : Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k)))
                  → count-bound g x ≡ count-bound g y → x ≡ y
  count-bound-inj {K} g (k , (ψ , (n , cs))) (k' , (ψ' , (n' , cs'))) e = outer
    where
    P : ⟪ β ⟫
    P = pair (pair (numeral (code ψ)) (numeral n)) (tuple-g g k cs)
    P' : ⟪ β ⟫
    P' = pair (pair (numeral (code ψ')) (numeral n')) (tuple-g g k' cs')
    e-out : (numeral k , P) ≡ (numeral k' , P')
    e-out = snd pairing (numeral k , P) (numeral k' , P') e
    pk : k ≡ k'
    pk = numeral-inj k k' (cong fst e-out)
    e-in : P ≡ P'
    e-in = cong snd e-out
    e-pair : (pair (numeral (code ψ)) (numeral n) , tuple-g g k cs)
           ≡ (pair (numeral (code ψ')) (numeral n') , tuple-g g k' cs')
    e-pair = snd pairing (pair (numeral (code ψ)) (numeral n) , tuple-g g k cs)
                         (pair (numeral (code ψ')) (numeral n') , tuple-g g k' cs') e-in
    e-code : code ψ ≡ code ψ'
    e-code = numeral-inj (code ψ) (code ψ')
      (cong fst (snd pairing (numeral (code ψ) , numeral n) (numeral (code ψ') , numeral n') (cong fst e-pair)))
    e-num : numeral n ≡ numeral n'
    e-num = cong snd (snd pairing (numeral (code ψ) , numeral n) (numeral (code ψ') , numeral n') (cong fst e-pair))
    qn : PathP (λ _ → ℕ) n n'
    qn = numeral-inj n n' e-num
    e-tup : tuple-g g k cs ≡ tuple-g g k' cs'
    e-tup = cong snd e-pair
    ψ₀ : Formula (⊥* {ℓ}) k
    ψ₀ = subst (Formula (⊥* {ℓ})) (sym pk) ψ'
    sψ : ψ ≡ ψ₀
    sψ = snd shape-count-inj {k = k} {φ = ψ} {ψ = ψ₀} (e-code ∙ sym (code-stable k k' (sym pk) ψ'))
    qψ : PathP (λ i → Formula (⊥* {ℓ}) (pk i)) ψ ψ'
    qψ = toPathP (cong (subst (Formula (⊥* {ℓ})) pk) sψ ∙ substSubst⁻ (Formula (⊥* {ℓ})) pk ψ')
    cs₀ : Vec K k
    cs₀ = subst (Vec K) (sym pk) cs'
    scs : cs ≡ cs₀
    scs = tuple-g-inj g k cs cs₀ (e-tup ∙ sym (tuple-g-stable K g k k' (sym pk) cs'))
    qcs : PathP (λ i → Vec K (pk i)) cs cs'
    qcs = toPathP (cong (subst (Vec K) pk) scs ∙ substSubst⁻ (Vec K) pk cs')
    inner₂ : PathP (λ i → ℕ × Vec K (pk i)) (n , cs) (n' , cs')
    inner₂ = ΣPathP {A = λ _ → ℕ} {B = λ i _ → Vec K (pk i)} (qn , qcs)
    inner₁ : PathP (λ i → Formula (⊥* {ℓ}) (pk i) × (ℕ × Vec K (pk i)))
                   (ψ , (n , cs)) (ψ' , (n' , cs'))
    inner₁ = ΣPathP {A = λ i → Formula (⊥* {ℓ}) (pk i)} {B = λ i _ → ℕ × Vec K (pk i)} (qψ , inner₂)
    outer : (k , (ψ , (n , cs))) ≡ (k' , (ψ' , (n' , cs')))
    outer = ΣPathP {A = λ _ → ℕ} {B = λ _ k → Formula (⊥* {ℓ}) k × (ℕ × Vec K k)} (pk , inner₁)

  formula-bound : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                → Σ[ f ∈ (Formula K 1 → ⟪ β ⟫) ] ((φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ)
  formula-bound {K} g = f , inj
    where
    f : Formula K 1 → ⟪ β ⟫
    f φ = count-bound g (fst (composed-count {K}) φ)
    inj : (φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ
    inj φ ψ e = snd (composed-count {K}) φ ψ
      (count-bound-inj g (fst (composed-count {K}) φ) (fst (composed-count {K}) ψ) e)

-- =====================================================================
-- SECTION 3.  THE TREE'S OWN ORDINAL WELL-ORDER, COPIED VERBATIM AT A
-- GENERIC CARRIER.  Source: src/L/StageCardinal.lagda.md:249-293,
-- module `OrdSWO`.  Copied for the same reason as `Bound`: it sits
-- behind the `sq` telescope and its content uses no `sq`.
-- =====================================================================

module SiteOrdSWO (β : S) (oβ : IsOrd β) where

  _≺_ : ⟪ β ⟫ → ⟪ β ⟫ → Type (ℓ-suc ℓ)
  m ≺ n = ⟪ β ⟫↪ m ∈ᵗ ⟪ β ⟫↪ n

  ord-inord : (m : ⟪ β ⟫) → IsOrd (⟪ β ⟫↪ m)
  ord-inord m = mem-ord {A = β} oβ (⟪ β ⟫↪ m) (member β m)

  tri₁ : (m n : ⟪ β ⟫) → Tri (m ≺ n) (m ≡ n) (n ≺ m)
  tri₁ m n = go (ord-tri (⟪ β ⟫↪ m) (ord-inord m) (⟪ β ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ β ⟫↪ m ∈ˢ ⟪ β ⟫↪ n ⟩
          ⊎ ((⟪ β ⟫↪ m ≡ ⟪ β ⟫↪ n) ⊎ ⟨ ⟪ β ⟫↪ n ∈ˢ ⟪ β ⟫↪ m ⟩))
       → Tri (m ≺ n) (m ≡ n) (n ≺ m)
    go (inl h)       = lt h
    go (inr (inl p)) = eq (↪-inj {a = β} p)
    go (inr (inr h)) = gt h

  irr₁ : (m : ⟪ β ⟫) → (m ≺ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ β ⟫↪ m) h

  trans₁ : (m n k : ⟪ β ⟫) → m ≺ n → n ≺ k → m ≺ k
  trans₁ m n k h h' = ord-inord k .fst h h'

  acc₁ : (m : ⟪ β ⟫) → Acc _∈ᵗ_ (⟪ β ⟫↪ m) → Acc _≺_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ β ⟫↪ n) n≺m))

  wf₁ : WellFounded _≺_
  wf₁ m = acc₁ m (regularityV (⟪ β ⟫↪ m))

  ordSWO : SWO ⟪ β ⟫
  ordSWO = record
    { _<∙_   = _≺_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

-- The two copies, instantiated ONCE, at the site alpha, on the site
-- fiber.  These two lines are the whole demand this probe makes on
-- ingredient (iii), and they mirror
-- src/L/BoundedSubset.lagda.md:1410 exactly.
module B = SiteBound α oα α∉ω iii
module O = SiteOrdSWO α oα

-- =====================================================================
-- SECTION 4.  THE RESTRUCTURED INDUCTION STEP.  Source of the proof
-- text: src/L/StageCardinal.lagda.md:296-394, module `LimitStep`, with
-- ONE change of shape: the step's own alpha is replaced by the fixed
-- site alpha as the COUNTING and PACKING carrier, so `sq` is never
-- applied at any ordinal other than the site.  Against `LimitStep`:
--   * `B` is the site instantiation above, not `Bound α ... (sq α ...)`;
--   * the member index m lives in `⟪ gamma ⟫` and is embedded into
--     `⟪ alpha ⟫` by `emb` before packing (LimitStep could pack its m
--     directly because its carrier WAS its target);
--   * the composed induction hypothesis `ih` is supplied per member
--     ordinal by the `∈-induction` below, instead of by `branch`.
-- =====================================================================

module SiteStep (γ : S) (oγ : IsOrd γ) (γ∈suc : ⟨ γ ∈ˢ sucV α ⟩)
  (IH : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → ⟨ δ ∈ˢ sucV α ⟩
      → ⟪ Lset δ ⟫ ↪ ⟪ α ⟫) where

  δ∈sucV : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → ⟨ δ ∈ˢ sucV α ⟩
  δ∈sucV δ δ∈γ = suc-ord oα .fst {x = γ} {y = δ} δ∈γ γ∈suc

  ihm : (m : ⟪ γ ⟫) → ⟪ Lset (⟪ γ ⟫↪ m) ⟫ ↪ ⟪ α ⟫
  ihm m = IH (⟪ γ ⟫↪ m) (member γ m)
    (mem-ord {A = γ} oγ (⟪ γ ⟫↪ m) (member γ m))
    (δ∈sucV (⟪ γ ⟫↪ m) (member γ m))

  γ⊆α : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → ⟨ δ ∈ˢ α ⟩
  γ⊆α δ δ∈γ = ∈sucV-elim {A = α} {x = γ} {P = ⟨ δ ∈ˢ α ⟩} ((δ ∈ˢ α) .snd)
    γ∈suc
    (λ γ∈α → oα .fst {x = γ} {y = δ} δ∈γ γ∈α)
    (λ γ≡α → subst (λ w → ⟨ δ ∈ˢ w ⟩) γ≡α δ∈γ)

  emb : ⟪ γ ⟫ → ⟪ α ⟫
  emb m = fiber α {x = ⟪ γ ⟫↪ m} (γ⊆α (⟪ γ ⟫↪ m) (member γ m)) .fst

  emb-inj : (m n : ⟪ γ ⟫) → emb m ≡ emb n → m ≡ n
  emb-inj m n e = ↪-inj {a = γ}
    (sym (fiber α {x = ⟪ γ ⟫↪ m} (γ⊆α (⟪ γ ⟫↪ m) (member γ m)) .snd)
      ∙ cong (⟪ α ⟫↪) e
      ∙ fiber α {x = ⟪ γ ⟫↪ n} (γ⊆α (⟪ γ ⟫↪ n) (member γ n)) .snd)

  D : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S
  D δ φ = DefOf.defSet (Lset δ) φ

  F : ⟪ γ ⟫ → Type ℓ
  F m = Formula ⟪ Lset (⟪ γ ⟫↪ m) ⟫ 1

  cnt : (m : ⟪ γ ⟫) → F m → ⟪ α ⟫
  cnt m = fst (B.formula-bound {K = ⟪ Lset (⟪ γ ⟫↪ m) ⟫} (ihm m))

  cnt-inj : (m : ⟪ γ ⟫) (φ ψ : F m) → cnt m φ ≡ cnt m ψ → φ ≡ ψ
  cnt-inj m = snd (B.formula-bound {K = ⟪ Lset (⟪ γ ⟫↪ m) ⟫} (ihm m))

  cnt-stable : (m₁ m₂ : ⟪ γ ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
             → cnt m₁ (subst F q φ) ≡ cnt m₂ φ
  cnt-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → cnt m₁ (subst F q φ) ≡ cnt m₂ φ)
      (λ φ → cong (cnt m₂) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable : (m₁ m₂ : ⟪ γ ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
                → D (⟪ γ ⟫↪ m₁) (subst F q φ)
                  ≡ D (⟪ γ ⟫↪ m₂) φ
  defset-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → D (⟪ γ ⟫↪ m₁) (subst F q φ)
                ≡ D (⟪ γ ⟫↪ m₂) φ)
      (λ φ → cong (D (⟪ γ ⟫↪ m₂)) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable-δ : (δ₁ δ₂ : S) (p : δ₁ ≡ δ₂) (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1)
                  → D δ₁ φ₀
                    ≡ D δ₂
                        (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀)
  defset-stable-δ δ₁ δ₂ p φ₀ =
    J (λ δ₂ p → (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1) → D δ₁ φ₀
                ≡ D δ₂
                    (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀))
      (λ φ₀ → sym (cong (D δ₁)
                   (substRefl {B = λ w → Formula ⟪ Lset w ⟫ 1} {x = δ₁} φ₀))) p φ₀

  class-pred : (x : ⟪ Lset γ ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  class-pred x y = ( ∥ Σ[ m ∈ ⟪ γ ⟫ ] Σ[ φ ∈ F m ]
                        ( ( D (⟪ γ ⟫↪ m) φ ≡ ⟪ Lset γ ⟫↪ x )
                        × ( B.pair (emb m) (cnt m φ) ≡ y ) ) ∥₁
                   , squash₁ )

  nonempty : (x : ⟪ Lset γ ⟫)
           → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩ ∥₁
  nonempty x = PT.rec (squash₁) toWitness
    (Lset-out γ (⟪ Lset γ ⟫↪ x) (member (Lset γ) x))
    where
    toWitness : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ ⟪ Lset γ ⟫↪ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
              → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩ ∥₁
    toWitness (δ , (δ∈γ , x∈𝒟ₒδ)) =
      PT.map mk (𝒟ₒ-inv (Lset δ) (⟪ Lset γ ⟫↪ x) x∈𝒟ₒδ)
      where
      fib = fiber γ δ∈γ
      m : ⟪ γ ⟫
      m = fib .fst
      p : ⟪ γ ⟫↪ m ≡ δ
      p = fib .snd
      mk : Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ]
             (D δ φ₀ ≡ ⟪ Lset γ ⟫↪ x)
         → Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩
      mk (φ₀ , e₀) = (B.pair (emb m) (cnt m φ) , ∣ (m , φ , (e , refl)) ∣₁)
        where
        φ : F m
        φ = subst (λ w → Formula ⟪ Lset w ⟫ 1) (sym p) φ₀
        e : D (⟪ γ ⟫↪ m) φ ≡ ⟪ Lset γ ⟫↪ x
        e = sym (defset-stable-δ δ (⟪ γ ⟫↪ m) (sym p) φ₀) ∙ e₀

  h : ⟪ Lset γ ⟫ → ⟪ α ⟫
  h x = fst (leastOf O.ordSWO lem (class-pred x) (nonempty x))

  h-inj : (x y : ⟪ Lset γ ⟫) → h x ≡ h y → x ≡ y
  h-inj x y e = ↪-inj {a = Lset γ} (go pm)
    where
    lx = leastOf O.ordSWO lem (class-pred x) (nonempty x)
    ly = leastOf O.ordSWO lem (class-pred y) (nonempty y)
    pm : ⟨ class-pred x (fst ly) ⟩
    pm = subst (λ z → ⟨ class-pred x z ⟩) e (fst (snd lx))
    py : ⟨ class-pred y (fst ly) ⟩
    py = fst (snd ly)
    go : ⟨ class-pred x (fst ly) ⟩
       → ⟪ Lset γ ⟫↪ x ≡ ⟪ Lset γ ⟫↪ y
    go = PT.rec (isSetS (⟪ Lset γ ⟫↪ x) (⟪ Lset γ ⟫↪ y)) go₁
      where
      go₁ : Σ[ m₁ ∈ ⟪ γ ⟫ ] Σ[ φ₁ ∈ F m₁ ]
              ( ( D (⟪ γ ⟫↪ m₁) φ₁ ≡ ⟪ Lset γ ⟫↪ x )
              × ( B.pair (emb m₁) (cnt m₁ φ₁) ≡ fst ly ) )
          → ⟪ Lset γ ⟫↪ x ≡ ⟪ Lset γ ⟫↪ y
      go₁ (m₁ , φ₁ , eφ₁ , ec₁) =
        PT.rec (isSetS (⟪ Lset γ ⟫↪ x) (⟪ Lset γ ⟫↪ y)) go₂ py
        where
        go₂ : Σ[ m₂ ∈ ⟪ γ ⟫ ] Σ[ φ₂ ∈ F m₂ ]
                ( ( D (⟪ γ ⟫↪ m₂) φ₂ ≡ ⟪ Lset γ ⟫↪ y )
                × ( B.pair (emb m₂) (cnt m₂ φ₂) ≡ fst ly ) )
            → ⟪ Lset γ ⟫↪ x ≡ ⟪ Lset γ ⟫↪ y
        go₂ (m₂ , φ₂ , eφ₂ , ec₂) = sym eφ₁ ∙ eq-defset ∙ eφ₂
          where
          ec : B.pair (emb m₁) (cnt m₁ φ₁) ≡ B.pair (emb m₂) (cnt m₂ φ₂)
          ec = ec₁ ∙ sym ec₂
          p-pair : (emb m₁ ≡ emb m₂) × (cnt m₁ φ₁ ≡ cnt m₂ φ₂)
          p-pair = B.pair-inj (emb m₁) (cnt m₁ φ₁) (emb m₂) (cnt m₂ φ₂) ec
          qm : m₁ ≡ m₂
          qm = emb-inj m₁ m₂ (fst p-pair)
          ecount : cnt m₁ φ₁ ≡ cnt m₂ φ₂
          ecount = snd p-pair
          ecount' : cnt m₁ φ₁ ≡ cnt m₁ (subst F (sym qm) φ₂)
          ecount' = ecount ∙ sym (cnt-stable m₁ m₂ (sym qm) φ₂)
          eφ : φ₁ ≡ subst F (sym qm) φ₂
          eφ = cnt-inj m₁ φ₁ (subst F (sym qm) φ₂) ecount'
          eq-defset : D (⟪ γ ⟫↪ m₁) φ₁
                    ≡ D (⟪ γ ⟫↪ m₂) φ₂
          eq-defset = cong (D (⟪ γ ⟫↪ m₁)) eφ
                    ∙ defset-stable m₁ m₂ (sym qm) φ₂

  leg : ⟪ Lset γ ⟫ ↪ ⟪ α ⟫
  leg = h , h-inj

-- =====================================================================
-- SECTION 5.  THE INDUCTION, AT THE SITE'S TARGET.  The predicate
-- fixes the TARGET at alpha; compare `Upper.P` at
-- src/L/StageCardinal.lagda.md:526-529, which fixes it at each step's
-- own ordinal and thereby buys the band.
-- =====================================================================

Q : S → Type (ℓ-suc ℓ)
Q γ = IsOrd γ → ⟨ γ ∈ˢ sucV α ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α ⟫

step : (γ : S) → ((δ : S) → ⟨ δ ∈ˢ γ ⟩ → Q δ) → Q γ
step γ IH oγ γ∈suc = SiteStep.leg γ oγ γ∈suc IH

site-stage-card : (γ : S) → Q γ
site-stage-card = ∈-induction step

-- The bill's own reading: the same type `Up.stage-card-upper` gives at
-- `gamma = alpha` (src/L/BoundedSubset.lagda.md:1513), paid at the
-- site grain.
site-leg-α : ⟪ Lset α ⟫ ↪ ⟪ α ⟫
site-leg-α = site-stage-card α oα (self∈sucV α)

-- =====================================================================
-- SECTION 6.  ORIENTATION: the site grain is the WEAKER hypothesis.
-- The product gives the site fiber by application; this row mirrors
-- src/L/BoundedSubset.lagda.md:1410 verbatim.  The probe's obligation
-- below runs the other way and needs no product.
-- =====================================================================

family-gives-site : SqParam α → SiteGrain α
family-gives-site fam = fam α (self∈sucV α) α∉ω

-- =====================================================================
-- SECTION 7.  THE OBLIGATION.  The bill's demand on ingredient (iii),
-- stated at the site the tree spends it, shown to suffice for
-- everything downstream: with `absorbs` (the sibling parameter at
-- src/L/BoundedSubset.lagda.md:1392) the term lands the exact type of
-- `code-inj` (src/L/BoundedSubset.lagda.md:1512-1513), the value that
-- feeds `CodeCount` and everything below it.  Every other `SC.` use in
-- `BoundedSubsetAt` is sq-free in content (`OrdSWO` at `:1518` and
-- `:1528`, `stage-card-lower` at `:1581`).
-- =====================================================================

site-grain-suffices : (x : S) (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
                    → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ α ⟫
site-grain-suffices x absorbs = comp-inj absorbs site-leg-α
