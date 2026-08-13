{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T125] The below-lim gate at the first limit: Sset ω ∈ Lset (+ω ω).
-- Untracked probe, no master, no git.  Written incrementally (C-22).
-- Route (a) for StepInL: scratch tree at /tmp/t125-scratch with the
-- left-compute bridge (T121 section 3.2) applied at the three sites.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeBelowLim {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using
  ( IsOrd; isTransV; Lset; Lset-in; Lset-out; Lset-mono; Lset-layer; layer-trans
  ; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; finSet )
open import L.Ordinal {ℓ} using
  ( ∅-ord; suc-ord; #∈ω; numeral-ord; ω-ord; ω-mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-mem; +ω-ord; +ω-limit )
open import L.InitialSegment {ℓ} using ( _∈ran_; _⟷_ )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-out; Sset-mono; Sset-suc; limit-succ-mem
  ; step; step-in; step-in-self; step-in-img; step-out; StepArm
  ; arm-member; arm-self; arm-image; Op16; Fof )
open import L.TowerKit {ℓ} lem A using ( Ltr; suc⁴; ext-⊆ )
open import L.Rud.Bridge {ℓ} lem A using
  ( Lset-zero; Sset-zero; Sset-union-limit; Sset-union-in; Lpr-limit
  ; Lset∈Lsuc; suc⁴-up; suc⁴∈; Lstage; Lstage₂; ∅∈Lset; Lstep⊆
  ; Lval )
open import L.Rud.Finite {ℓ} lem A using ( limω; finSetMem )
open import L.Rud.HF {ℓ} lem A using
  ( Lsetω⊆Ssetω; numeral∈Lsetω; numeral∈HF; pr-in-HF; stage∈HF )
open import L.Rud.StepInL {ℓ} lem A using ( module Slot; values∈L; stepSet∈L )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import Cubical.Data.FinData.Base using ( Fin )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2 )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Inclusion and extensional equality (the HF/ProbeCarried shape).
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

-- The numeral for k, named (the `#` prefix does not parse inside ⟨_⟩).
nk : ℕ → S
nk k = # k

-- D-10 check 2: the kit at the L-stage carrier Lset ω.  The four shared
-- clauses (pairhood, singleValued, zeroClause, exactDom) with their formulas
-- and decodes instantiate here through the delivered layer-trans.
module K = LevelKit (Lset ω) (layer-trans (Lset-layer ω))
open K public

-- The carrier's transitivity certificate, named (the kit parameter).
utr : isTransV (Lset ω)
utr = layer-trans (Lset-layer ω)

-- The bounded successor atom and its decode, at the L-stage carrier.
-- The formula is carrier-generic ordinal content; the level-sigma chapter
-- hosts it only at the rud carrier, so it is restated here (verbatim body).
sucKcov : {n : ℕ} → Fin n → Fin n → Formula ⟪ Lset ω ⟫ (suc n)
sucKcov k a = (var zero ∈̇ var (suc a)) ∨̇ (var zero ≐ var (suc a))

sucAt : {n : ℕ} → Fin n → Fin n → Formula ⟪ Lset ω ⟫ n
sucAt k a =
  (var a ∈̇ var k)
  ∧̇ (∀̇∈ (var a) (var zero ∈̇ var (suc k)))
  ∧̇ (∀̇∈ (var k) (sucKcov k a))

sucAt-ok : {n : ℕ} (k a : Fin n) (δ : Vec SM n)
         → ⟨ δ ⊨ᵐ sucAt k a ⟩ ⟷ (fst (lookup k δ) ≡ sucV (fst (lookup a δ)))
sucAt-ok k a δ = (out , bwd)
  where
  valK valA : S
  valK = fst (lookup k δ)
  valA = fst (lookup a δ)
  out : ⟨ δ ⊨ᵐ sucAt k a ⟩ → valK ≡ sucV valA
  out (k∈ , (A⊆K , Kcov)) = ext-⊆ K⊆suc suc⊆K
    where
    K⊆suc : valK ⊆ sucV valA
    K⊆suc z z∈K = PT.rec (snd (z ∈ˢ sucV valA)) go (Kcov zm z∈K)
      where
      zm : SM
      zm = PK.pt z (utr {x = valK} {y = z} z∈K (snd (lookup k δ)))
      go : (⟨ z ∈ˢ valA ⟩ ⊎ (z ≡ valA)) → ⟨ z ∈ˢ sucV valA ⟩
      go (inl z∈A) = ∈sucV-inl {A = valA} {x = z} z∈A
      go (inr z≡A) = subst (λ w → ⟨ w ∈ˢ sucV valA ⟩) (sym z≡A)
        (self∈sucV valA)
    suc⊆K : sucV valA ⊆ valK
    suc⊆K z z∈suc = ∈sucV-elim (snd (z ∈ˢ valK)) z∈suc
      (λ z∈A → A⊆K (PK.pt z (utr {x = valA} {y = z} z∈A
        (snd (lookup a δ)))) z∈A)
      (λ z≡A → subst (λ w → ⟨ w ∈ˢ valK ⟩) (sym z≡A) k∈)
  bwd : valK ≡ sucV valA → ⟨ δ ⊨ᵐ sucAt k a ⟩
  bwd q = ( k∈q , (A⊆Kq , Kcovq) )
    where
    k∈q : ⟨ valA ∈ˢ valK ⟩
    k∈q = subst (λ w → ⟨ valA ∈ˢ w ⟩) (sym q) (self∈sucV valA)
    A⊆Kq : ⟨ δ ⊨ᵐ ∀̇∈ (var a) (var zero ∈̇ var (suc k)) ⟩
    A⊆Kq zm z∈A = subst (λ w → ⟨ fst zm ∈ˢ w ⟩) (sym q)
      (∈sucV-inl {A = valA} {x = fst zm} z∈A)
    Kcovq : ⟨ δ ⊨ᵐ ∀̇∈ (var k) (sucKcov k a) ⟩
    Kcovq zm z∈K = ∈sucV-elim (snd sat) z∈suc inA eqA
      where
      sat = (zm ∷ δ) ⊨ᵐ sucKcov k a
      z∈suc : ⟨ fst zm ∈ˢ sucV valA ⟩
      z∈suc = subst (λ w → ⟨ fst zm ∈ˢ w ⟩) q z∈K
      inA : ⟨ fst zm ∈ˢ valA ⟩ → ⟨ (zm ∷ δ) ⊨ᵐ sucKcov k a ⟩
      inA h = ∣ inl h ∣₁
      eqA : fst zm ≡ valA → ⟨ (zm ∷ δ) ⊨ᵐ sucKcov k a ⟩
      eqA e = ∣ inr e ∣₁

-- The RudBelow bundle at the first limit: inclusion and membership of an
-- S-stage below ω in Lset ω.  This is T90's O2, built at the first limit
-- through the delivered successor machinery (stepSet∈L, values∈L, Lstage₂).
RudBelow-ω : S → Type (ℓ-suc ℓ)
RudBelow-ω β = ((v : S) → ⟨ v ∈ˢ Sset β ⟩ → ⟨ v ∈ˢ Lset ω ⟩) × ⟨ Sset β ∈ˢ Lset ω ⟩

isPropRudBelow-ω : (β : S) → isProp (RudBelow-ω β)
isPropRudBelow-ω β = isProp× (isPropΠ2 (λ v _ → snd (v ∈ˢ Lset ω)))
  (snd (Sset β ∈ˢ Lset ω))

∅∈ω : ⟨ ∅ ∈ˢ ω ⟩
∅∈ω = #∈ω 0

-- The gate proper: the memberships and the landing are proved under the
-- relativization-slot hypothesis A ∈ Lset ω (Reduce's slot∈L at the first
-- limit; the trunk discharges it at A = ∅, ∅∈Lset).  Nothing else depends
-- on it.
module Gate (A∈ω : ⟨ A ∈ˢ Lset ω ⟩) where

  -- The StepInL op-graph machinery instantiated at the L-stage carrier
  -- Lset ω (the S-story's successor clause is written against it, T90 O4).
  module Sl = Slot (Lset ω) (Ltr ω)
    (∈-asFiber {a = A} {b = Lset ω} A∈ω .fst)
    (∈-asFiber {a = A} {b = Lset ω} A∈ω .snd)
    (∅∈Lset ω limω ∅∈ω)
  open Sl using ( bigOr; bigOr-in; bigOr-out; graphOf; graph-in )

  -- The variable calculus at the inner satisfaction: embedding a 3-variable
  -- graph formula into the 8-variable step-membership environment is a pure
  -- weakening, so the agreement is pointwise refl.
  module RenIn = Sat (hPropAlgebra (ℓ-suc ℓ))
    (𝒮ᵥ ↾ (λ x → x ∈ˢ Lset ω)) {ℓ} {⟪ Lset ω ⟫} K.ι

  inj : Fin 3 → Fin 8
  inj zero = zero
  inj (suc zero) = suc zero
  inj (suc (suc zero)) = suc (suc zero)

  -- The op graphs assemble at the L-stage carrier: one graph decode read at
  -- Lset ω (the successor clause's atoms are built from these, T90 O4).
  graphInTest : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ Lset ω ⟩)
              (a∈ : ⟨ a ∈ˢ Lset ω ⟩) (y∈ : ⟨ y ∈ˢ Lset ω ⟩)
            → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ω ⟩)
            → y ≡ Fof i a b
            → ⟨ ((b , b∈) ∷ (a , a∈) ∷ (y , y∈) ∷ []) ⊨ᵐ graphOf i ⟩
  graphInTest i b a y b∈ a∈ y∈ sub e = graph-in i b a y b∈ a∈ y∈ sub e

  -- The rud step is L-stage closed: step c ⊆ Lset ω for c ∈ Lset ω, by the
  -- delivered sixteen-value reads at the stage of c.
  stepInL : (c : S) → ⟨ c ∈ˢ Lset ω ⟩
          → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ Lset ω ⟩
  stepInL c c∈ v v∈step = PT.rec (snd (v ∈ˢ Lset ω)) go (step-out c v v∈step)
    where
    go : StepArm c v → ⟨ v ∈ˢ Lset ω ⟩
    go (arm-member v∈c) = Ltr ω {x = c} {y = v} v∈c c∈
    go (arm-self e) = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym e) c∈
    go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ Lset ω)) both
      (Lstage₂ ω limω c A c∈ A∈ω)
      where
      both : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × ⟨ c ∈ˢ Lset ξ ⟩ × ⟨ A ∈ˢ Lset ξ ⟩)
           → ⟨ v ∈ˢ Lset ω ⟩
      both (ξ , ξ∈ω , c∈ξ , A∈ξ) =
        Lset-mono {α = ω} {β = sucV (suc⁴ ξ)}
          (limit-succ-mem ω (suc⁴ ξ) limω (suc⁴∈ ω ξ limω ξ∈ω))
          (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ξ)) ⟩) (sym e)
            (Lval (suc⁴ ξ) (suc⁴-up ξ A A∈ξ) i a b a∈ b∈
              (values∈L c ξ c∈ξ i a b sa sb)))
        where
        argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ξ ⟩
        argIn x (inl h) = Ltr ξ h c∈ξ
        argIn x (inr e) = subst (λ w → ⟨ w ∈ˢ Lset ξ ⟩) (sym e) c∈ξ
        a∈ : ⟨ a ∈ˢ Lset (suc⁴ ξ) ⟩
        a∈ = suc⁴-up ξ a (argIn a sa)
        b∈ : ⟨ b ∈ˢ Lset (suc⁴ ξ) ⟩
        b∈ = suc⁴-up ξ b (argIn b sb)

  -- The successor step of the entry induction: from Sset δ ∈ Lset ω (and the
  -- relativization slot A ∈ Lset ω) to Sset (sucV δ) ∈ Lset ω, riding the
  -- stage dance through stepSet∈L and values∈L exactly as Bridge.Below does.
  sucStep : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → RudBelow-ω δ → RudBelow-ω (sucV δ)
  sucStep δ δ∈ω rb = PT.rec (isPropRudBelow-ω (sucV δ)) atStage
    (Lstage₂ ω limω (Sset δ) A (rb .snd) A∈ω)
    where
    atStage : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ ω ⟩ × ⟨ Sset δ ∈ˢ Lset ζ ⟩ × ⟨ A ∈ˢ Lset ζ ⟩)
            → RudBelow-ω (sucV δ)
    atStage (ζ , ζ∈ω , u∈ , A∈) = (subFn , memFn)
      where
      ζ₄ ζ₅ ζ₆ : S
      ζ₄ = suc⁴ ζ
      ζ₅ = sucV ζ₄
      ζ₆ = sucV ζ₅
      up₁ : (ξ y : S) → ⟨ y ∈ˢ Lset ξ ⟩ → ⟨ y ∈ˢ Lset (sucV ξ) ⟩
      up₁ ξ y h = Lset-mono {α = sucV ξ} {β = ξ} (self∈sucV ξ) h
      ζ₄∈ω : ⟨ ζ₄ ∈ˢ ω ⟩
      ζ₄∈ω = suc⁴∈ ω ζ limω ζ∈ω
      ζ₅∈ω : ⟨ ζ₅ ∈ˢ ω ⟩
      ζ₅∈ω = limit-succ-mem ω ζ₄ limω ζ₄∈ω
      ζ₆∈ω : ⟨ ζ₆ ∈ˢ ω ⟩
      ζ₆∈ω = limit-succ-mem ω ζ₅ limω ζ₅∈ω
      u∈₄ : ⟨ Sset δ ∈ˢ Lset ζ₄ ⟩
      u∈₄ = suc⁴-up ζ (Sset δ) u∈
      A∈₄ : ⟨ A ∈ˢ Lset ζ₄ ⟩
      A∈₄ = suc⁴-up ζ A A∈
      stepSub : (v : S) → ⟨ v ∈ˢ step (Sset δ) ⟩ → ⟨ v ∈ˢ Lset ζ₅ ⟩
      stepSub = Lstep⊆ (Sset δ) ζ₄ A∈₄ u∈₄ (values∈L (Sset δ) ζ u∈)
      u∈₅ : ⟨ Sset δ ∈ˢ Lset ζ₅ ⟩
      u∈₅ = up₁ ζ₄ (Sset δ) u∈₄
      subFn : (v : S) → ⟨ v ∈ˢ Sset (sucV δ) ⟩ → ⟨ v ∈ˢ Lset ω ⟩
      subFn v h = Lset-mono {α = ω} {β = ζ₅} ζ₅∈ω
        (stepSub v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Sset-suc δ) h))
      memFn : ⟨ Sset (sucV δ) ∈ˢ Lset ω ⟩
      memFn = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (Sset-suc δ))
        (Lset-mono {α = ω} {β = ζ₆} ζ₆∈ω
          (stepSet∈L (Sset δ) ζ₅ u∈₅ (up₁ ζ₄ A A∈₄) stepSub))

  -- The entry induction: every S-stage below ω is included in and a member of
  -- Lset ω.  At the first limit the induction is only zero and successor steps
  -- (every ordinal below ω is a numeral).
  memberAt : (n : ℕ) → RudBelow-ω (nk n)
  memberAt zero = ( subz , memz )
    where
    subz : (v : S) → ⟨ v ∈ˢ Sset ∅ ⟩ → ⟨ v ∈ˢ Lset ω ⟩
    subz v h = Empty.rec (∅-empty v (∈∈ₛ {a = v} {b = ∅} .fst
      (subst (λ w → ⟨ v ∈ˢ w ⟩) Sset-zero h)))
    memz : ⟨ Sset ∅ ∈ˢ Lset ω ⟩
    memz = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym Sset-zero)
      (∅∈Lset ω limω ∅∈ω)
  memberAt (suc n) = sucStep (nk n) (#∈ω n) (memberAt n)

  memberAtOrd : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩ → RudBelow-ω β
  memberAtOrd β ordβ β∈ω = PT.rec (isPropRudBelow-ω β) go β∈ω
    where
    go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (nk (lower m) ≡ β) → RudBelow-ω β
    go (m , e) = subst (λ w → RudBelow-ω w) e (memberAt (lower m))

  -- The inclusion half of the identification: Sset ω ⊆ Lset ω, through the
  -- union structure of the S-tower at the limit and the memberships below.
  Ssetω⊆Lsetω : Sset ω ⊆ Lset ω
  Ssetω⊆Lsetω x x∈S = PT.rec (snd (x ∈ˢ Lset ω)) go (Sset-out ω x x∈S)
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → ⟨ x ∈ˢ Lset ω ⟩
    go (δ , δ∈ω , x∈step) =
      memberAtOrd (sucV δ) (suc-ord (ω-mem-ord δ δ∈ω))
        (limit-succ-mem ω δ limω δ∈ω) .fst x
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc δ)) x∈step)

  -- The identification at the first limit: Sset ω ≡ Lset ω, both directions.
  Ssetω≡Lsetω : Sset ω ≡ Lset ω
  Ssetω≡Lsetω = ext-⊆ Ssetω⊆Lsetω Lsetω⊆Ssetω

  Ssetω∈Lsucω : ⟨ Sset ω ∈ˢ Lset (sucV ω) ⟩
  Ssetω∈Lsucω = subst (λ w → ⟨ w ∈ˢ Lset (sucV ω) ⟩) (sym Ssetω≡Lsetω)
    (Lset∈Lsuc ω)

  +ωω-lim : ⟨ isLimit (+ω ω) ⟩
  +ωω-lim = +ω-limit ω ω-ord

  sucVω∈+ωω : ⟨ sucV ω ∈ˢ +ω ω ⟩
  sucVω∈+ωω = limit-succ-mem (+ω ω) ω +ωω-lim (+ω-mem ω)

  -- The gate target: Sset ω ∈ Lset (+ω ω), at the first limit pair
  -- (β = ω, γ = +ω ω), via the identification route's landing and the
  -- delivered +1 slack.
  target : ⟨ Sset ω ∈ˢ Lset (+ω ω) ⟩
  target = Lset-mono {α = +ω ω} {β = sucV ω} sucVω∈+ωω Ssetω∈Lsucω
