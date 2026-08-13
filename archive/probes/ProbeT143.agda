{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T143] The exact-domain wall, cured.  T138 found that segDom₀,
-- the limit segment's exact-domain proof, walls past 7.5 minutes and the
-- 893-line probe cannot finish in 35.  This probe is the smallest file
-- that elaborates segDom₀, with the proof restated so it checks in
-- seconds.  The statement K0.exactDom seg₀ is byte-identical to T138's.
-- The cure is I-5: the in-direction's two branches are named top-level
-- functions with written types; the eliminator's continuation arguments
-- are names, not inline lambdas.  The out-direction's pgo carries the
-- missing ∈sucV-inl step (T138's shape does not typecheck).  Untracked
-- probe, no git, no master, Everything untouched.  The graph layer is
-- consumed only through the delivered probes T126/T127; no StepInL
-- content is re-built here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT143 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl; pair-singleton )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import Cubical.Data.FinData.Base using ( Fin; toℕ; zero; suc )
open import Cubical.Data.FinData.Properties
  using ( fromℕ'; toFromId' )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Order using ( ≤-refl )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Functions.Logic as Logic
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2 )
open import Cubical.Data.Sigma.Properties using ( Σ≡Prop; ΣPathP )
open import Cubical.Foundations.Prelude using ( isProp→PathP )
open import Cubical.Foundations.Prelude using ( PathP )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈-asFiber; _∈ₛ_; _≡ₕ_; extensionality )
  renaming ( _⊆_ to _⊆ₛ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; ⋃_; union-ax; ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; Lset-layer; layer-trans; isTransV; 𝒟ₒ; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using
  ( ∅-ord; numeral-ord; numeral-mem; #∈ω; ω-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( +ω; +ω-limit; +ω-iter; +ω-in; +ω-out; sucIter )
open import L.Rud.Step {ℓ} lem ∅
  using ( Sset; Sset-suc; Sset-zero; Sset-mono; limit-succ-mem; step-in-self )
  renaming ( step to rudStep )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( 𝒟ₒ⊆Lsuc; Lset∈Lsuc; Lpair; Lpr-limit; ∅∈Lset; Sset-union-limit; Sset-union-in )
open import L.Rud.Finite {ℓ} lem ∅ using ( limω )
open import L.Rud.HF {ℓ} lem ∅ using ( numeral∈Lsetω )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in )
open import L.Rud.Ops {ℓ} using ( F0; F5; F0-spec; F5-spec; F5-RHS )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
import ProbeT128 {ℓ} lem as PT128
import ProbeT127 {ℓ} lem ∅ as PT127
import ProbeBelowLim {ℓ} lem ∅ as PB125

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The T128 carrier and the meta limit clause, reused: a₀ = +ω ∅ is the first
-- limit ordinal, β₀ = +ω a₀ is the carrier's index, and the limit clause is
-- carrier-generic (T128's).  T128's carrier setup (C, utr, a₀∈C) is reused
-- as well.
open PT128 using ( a₀; β₀; a₀-ord; firstLimit; β₀-lim; limitClause; C; utr; a₀∈C )

-- The kits: K0 at the target carrier Lset β₀ (the six-clause story's
-- carrier), Kω at Lset ω (the segment formula's carrier).  Kω is opened
-- because the formula layer (SM, ι, PK, isOrdAt, pair∈, ...) is used at
-- Lset ω; K0 stays qualified.
module K0 = LevelKit C utr
module Kω = LevelKit (Lset ω) (layer-trans (Lset-layer ω))
open Kω public

-- The numeral for k, named (the `#` prefix does not parse inside ⟨_⟩).
nk : ℕ → S
nk k = # k

_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

-- a₀ = +ω ∅ is ω: the finite iterates of successor from ∅ are exactly the
-- numerals, so both sides are the set of numerals.  (Prose in OrdBlocks and
-- Bridge: "γ ∅ = +ω ∅ = ω"; the equation itself is not delivered, so it is
-- proved here by the numeral characterizations on both sides.)
sucIter-∅≡# : (n : ℕ) → sucIter n ∅ ≡ # n
sucIter-∅≡# zero = refl
sucIter-∅≡# (suc n) = cong sucV (sucIter-∅≡# n)

a₀≡ω : a₀ ≡ ω
a₀≡ω = ext-⊆ {a₀} {ω} a₀⊆ω ω⊆a₀
  where
  a₀⊆ω : a₀ ⊆ ω
  a₀⊆ω x x∈a₀ = PT.rec (snd (x ∈ˢ ω)) go (+ω-out ∅ x x∈a₀)
    where
    go : Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) ∅ ⟩ → ⟨ x ∈ˢ ω ⟩
    go (n , h) = numeral-mem (suc n) x
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (sucIter-∅≡# (suc n)) h)
  ω⊆a₀ : ω ⊆ a₀
  ω⊆a₀ x x∈ω = PT.rec (snd (x ∈ˢ a₀)) go x∈ω
    where
    go : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower m) ≡ x) → ⟨ x ∈ˢ a₀ ⟩
    go (m , q) = subst (λ w → ⟨ w ∈ˢ a₀ ⟩) q
      (+ω-in ∅ (nk (lower m)) (lower m)
        (subst (λ w → ⟨ nk (lower m) ∈ˢ w ⟩)
          (sym (sucIter-∅≡# (suc (lower m)))) (self∈sucV (nk (lower m)))))

module G127 = PT127.Gate (∅∈Lset ω limω (#∈ω 0))

-- The SM eta: the certificate in an SM is proof-irrelevant, so every small
-- member is the ι of its own fiber.
smEta : (x : SM) → x ≡ ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst)
smEta x = ΣPathP (p , q)
  where
  p : fst x ≡ fst (ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst))
  p = sym (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .snd)
  q : PathP (λ i → ⟨ p i ∈ˢ Lset ω ⟩) (snd x)
         (snd (ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst)))
  q = isProp→PathP (λ i → snd (p i ∈ˢ Lset ω))
    (snd x) (snd (ι (∈-asFiber {a = fst x} {b = Lset ω} (snd x) .fst)))

-- The story formula renamed from arity 2 into the segment formula's arity-4
-- environment (s, y, ξ, x): the story's witness slot lands on s (index 2),
-- the read-member slot on y (index 1).
embStory : Fin 2 → Fin 4
embStory zero = suc (suc zero)
embStory (suc zero) = suc zero

storyRen : Formula ⟪ Lset ω ⟫ 4
storyRen = renameFo embStory G127.storyForm

module RenS = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ Lset ω))
  {ℓ} {⟪ Lset ω ⟫} Kω.ι

-- hmm: the kit at Lset ω needs to be opened for ι/SM here; T127's K is the
-- same kit.  Use PT127's K (the kit at Lset ω).
storyRen-ok : (δ : Vec SM 4)
            → ⟨ δ ⊨ᵐ storyRen ⟩ ⟷ G127.story (fst (lookup (suc (suc zero)) δ))
storyRen-ok δ = (out , bwd)
  where
  sm ym : SM
  sm = lookup (suc (suc zero)) δ
  ym = lookup (suc zero) δ
  fibY : ⟪ Lset ω ⟫
  fibY = ∈-asFiber {a = fst ym} {b = Lset ω} (snd ym) .fst
  ag : RenS.Agrees embStory δ (sm ∷ ym ∷ [])
  ag zero = refl
  ag (suc zero) = refl
  out : ⟨ δ ⊨ᵐ storyRen ⟩ → G127.story (fst sm)
  out h = G127.story-ok sm fibY .fst
    (subst (λ w → ⟨ (sm ∷ w ∷ []) ⊨ᵐ G127.storyForm ⟩) (smEta ym)
      (subst ⟨_⟩ (sym (RenS.⊨-rename embStory G127.storyForm δ (sm ∷ ym ∷ []) ag)) h))
  bwd : G127.story (fst sm) → ⟨ δ ⊨ᵐ storyRen ⟩
  bwd st = subst ⟨_⟩
    (RenS.⊨-rename embStory G127.storyForm δ (sm ∷ ym ∷ []) ag)
    (subst (λ w → ⟨ (sm ∷ w ∷ []) ⊨ᵐ G127.storyForm ⟩) (sym (smEta ym))
      (G127.story-ok sm fibY .snd st))

-- The segment's defining formula at arity 1, env (x): ∃s, ∃y, ∃ξ,
-- x = pr ξ y ∧ ξ is an ordinal ∧ s satisfies the story ∧ pr ξ y ∈ s.
segBody : Formula ⟪ Lset ω ⟫ 4
segBody = (PK.prAt (suc (suc (suc zero))) zero (suc zero))
      ∧̇ (isOrdAt zero)
      ∧̇ storyRen
      ∧̇ (∃̇∈ (var (suc (suc zero)))
            (PK.prAt zero (suc zero) (suc (suc zero))))

segForm : Formula ⟪ Lset ω ⟫ 1
segForm = ∃̇ (∃̇ (∃̇ segBody))

-- The two-way decode: the formula's extension is exactly the pairs
-- (ξ, Sset ξ) for ξ ∈ ω.
segForm-ok : (m : ⟪ Lset ω ⟫)
           → ⟨ (ι m ∷ []) ⊨ᵐ segForm ⟩
           ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
segForm-ok m = (out , bwd)
  where
  δ₁ : Vec SM 1
  δ₁ = ι m ∷ []
  out : ⟨ δ₁ ⊨ᵐ segForm ⟩
      → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
  out sat = PT.rec squash₁ s₁ sat
    where
    s₁ : Σ[ sm ∈ SM ] ⟨ (sm ∷ δ₁) ⊨ᵐ ∃̇ (∃̇ segBody) ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
    s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
      where
      s₂ : Σ[ ym ∈ SM ] ⟨ (ym ∷ sm ∷ δ₁) ⊨ᵐ ∃̇ segBody ⟩
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
      s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
        where
        s₃ : Σ[ ξm ∈ SM ] ⟨ (ξm ∷ ym ∷ sm ∷ δ₁) ⊨ᵐ segBody ⟩
           → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
        s₃ (ξm , (pr-sat , (ord-sat , (st-sat , pr∈-sat)))) =
          ∣ fst ξm , (ξ∈ω , x≡prξSξ) ∣₁
          where
          δ₄ : Vec SM 4
          δ₄ = ξm ∷ ym ∷ sm ∷ δ₁
          x≡prξy : ⟪ Lset ω ⟫↪ m ≡ pr (fst ξm) (fst ym)
          x≡prξy = PK.prAt-out (suc (suc (suc zero))) zero (suc zero) δ₄ pr-sat
          st : G127.story (fst sm)
          st = storyRen-ok δ₄ .fst st-sat
          h4 : exactDom (fst sm)
          h4 = st .snd .snd .snd .fst
          prξy∈s : ⟨ pr (fst ξm) (fst ym) ∈ˢ fst sm ⟩
          prξy∈s = pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
          ξ∈ω : ⟨ fst ξm ∈ˢ ω ⟩
          ξ∈ω = PT.rec (snd (fst ξm ∈ˢ ω)) dStep h4
            where
            dStep : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ Lset ω ⟩ × IsOrd δ₀
                     × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst sm ⟩ ∥₁)
                     × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ fst sm ⟩ ∥₁ → ⟨ a ∈ˢ δ₀ ⟩) )
                  → ⟨ fst ξm ∈ˢ ω ⟩
            dStep (δ₀ , (δ₀∈u , ordδ₀ , _ , out-d)) =
              ω-ord .fst {x = δ₀} {y = fst ξm} ξ∈δ₀ δ₀∈ω
              where
              ξ∈δ₀ : ⟨ fst ξm ∈ˢ δ₀ ⟩
              ξ∈δ₀ = out-d (fst ξm) ∣ fst ym , prξy∈s ∣₁
              δ₀∈ω : ⟨ δ₀ ∈ˢ ω ⟩
              δ₀∈ω = ord∈Lset→∈ ω ω-ord δ₀ ordδ₀ δ₀∈u
          y≡Ssetξ : fst ym ≡ Sset (fst ξm)
          y≡Ssetξ = G127.chainValue (fst sm) st (fst ξm) (fst ym) ξ∈ω prξy∈s
          x≡prξSξ : ⟪ Lset ω ⟫↪ m ≡ pr (fst ξm) (Sset (fst ξm))
          x≡prξSξ = x≡prξy ∙ cong₂ pr refl y≡Ssetξ
  bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ))) ∥₁
      → ⟨ δ₁ ⊨ᵐ segForm ⟩
  bwd h = PT.rec (snd (δ₁ ⊨ᵐ segForm)) step₀ h
    where
    step₀ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ)))
          → ⟨ δ₁ ⊨ᵐ segForm ⟩
    step₀ (ξ , (ξ∈ω , x≡prξSξ)) = PT.rec (snd (δ₁ ⊨ᵐ segForm)) num ξ∈ω
      where
      num : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower k) ≡ ξ)
          → ⟨ δ₁ ⊨ᵐ segForm ⟩
      num (k , #k≡ξ) = ∣ sm , (∣ ym , (∣ ξm , body-sat ∣₁) ∣₁) ∣₁
        where
        ξ∈L : ⟨ ξ ∈ˢ Lset ω ⟩
        ξ∈L = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) #k≡ξ (numeral∈Lsetω (lower k))
        Sξ∈L : ⟨ Sset ξ ∈ˢ Lset ω ⟩
        Sξ∈L = subst (λ w → ⟨ Sset w ∈ˢ Lset ω ⟩) #k≡ξ
          (G127.G125.memberAt (lower k) .snd)
        sm : SM
        sm = PK.pt (G127.seg (lower k)) (G127.seg∈Lsetω (lower k))
        ym : SM
        ym = PK.pt (Sset ξ) Sξ∈L
        ξm : SM
        ξm = PK.pt ξ ξ∈L
        δ₄ : Vec SM 4
        δ₄ = ξm ∷ ym ∷ sm ∷ δ₁
        body-sat : ⟨ δ₄ ⊨ᵐ segBody ⟩
        body-sat = ( pr-sat , (ord-sat , (st-sat , pr∈-sat)) )
          where
          pr-sat : ⟨ δ₄ ⊨ᵐ PK.prAt (suc (suc (suc zero))) zero (suc zero) ⟩
          pr-sat = PK.prAt-in (suc (suc (suc zero))) zero (suc zero) δ₄
            x≡prξSξ
          ord-sat : ⟨ δ₄ ⊨ᵐ isOrdAt zero ⟩
          ord-sat = isOrd-in zero δ₄ (subst IsOrd #k≡ξ (numeral-ord (lower k)))
          st-sat : ⟨ δ₄ ⊨ᵐ storyRen ⟩
          st-sat = storyRen-ok δ₄ .snd (G127.segStory (lower k))
          prξSξ∈s : ⟨ pr ξ (Sset ξ) ∈ˢ G127.seg (lower k) ⟩
          prξSξ∈s = finSet-in (suc (lower k)) hseg (pr ξ (Sset ξ)) ∣ idx , eq ∣₁
            where
            hseg : Fin (suc (lower k)) → S
            hseg i = pr (nk (toℕ i)) (Sset (nk (toℕ i)))
            idx : Fin (suc (lower k))
            idx = fromℕ' (suc (lower k)) (lower k) (≤-refl {suc (lower k)})
            e : toℕ idx ≡ lower k
            e = toFromId' (suc (lower k)) (lower k) (≤-refl {suc (lower k)})
            eq : hseg idx ≡ pr ξ (Sset ξ)
            eq = cong₂ pr (cong nk e) (cong Sset (cong nk e))
               ∙ cong₂ pr #k≡ξ (cong Sset #k≡ξ)
          pr∈-sat : ⟨ δ₄ ⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                       (PK.prAt zero (suc zero) (suc (suc zero))) ⟩
          pr∈-sat = pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd prξSξ∈s

-- P, the pairs below the first limit: the definable family
-- {(ξ, Sset ξ) : ξ ∈ ω}, a member of Lset β₀ via the definable-power step
-- at Lset ω and the +1 slack.
P : S
P = defSet segForm

module Dω = DefOf (Lset ω)

P∈𝒟ₒω : ⟨ P ∈ˢ 𝒟ₒ (Lset ω) ⟩
P∈𝒟ₒω = 𝒟ₒ-intro (Lset ω) P ∣ segForm , refl ∣₁

P∈Lsucω : ⟨ P ∈ˢ Lset (sucV ω) ⟩
P∈Lsucω = 𝒟ₒ⊆Lsuc ω P P∈𝒟ₒω

P∈Lβ₀ : ⟨ P ∈ˢ C ⟩
P∈Lβ₀ = Lset-mono {α = β₀} {β = sucV a₀} (+ω-iter 1 a₀)
  (subst (λ w → ⟨ P ∈ˢ Lset (sucV w) ⟩) (sym a₀≡ω) P∈Lsucω)

-- The two directions of P's membership: in, from a numeral index (the
-- story-checked finite segment as witness); out, back to the numeral index
-- and the S-stage value (the story's chain).
prξSξ∈Lω : (ξ : S) → ⟨ ξ ∈ˢ ω ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ Lset ω ⟩
prξSξ∈Lω ξ ξ∈ω = PT.rec (snd (pr ξ (Sset ξ) ∈ˢ Lset ω)) go ξ∈ω
  where
  go : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower k) ≡ ξ)
     → ⟨ pr ξ (Sset ξ) ∈ˢ Lset ω ⟩
  go (k , q) = subst (λ w → ⟨ pr w (Sset w) ∈ˢ Lset ω ⟩) q
    (Lpr-limit ω limω (nk (lower k)) (Sset (nk (lower k)))
      (numeral∈Lsetω (lower k)) (G127.G125.memberAt (lower k) .snd))

P∈-out : (p : S) → ⟨ p ∈ˢ P ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
P∈-out p p∈ = out' sat
  where
  m : ⟪ Lset ω ⟫
  m = ∈-asFiber {a = p} {b = Lset ω} (Dω.defSet⊆A segForm p p∈) .fst
  p∈m : ⟨ ⟪ Lset ω ⟫↪ m ∈ˢ P ⟩
  p∈m = subst (λ w → ⟨ w ∈ˢ P ⟩) (sym (∈-asFiber {a = p} {b = Lset ω}
    (Dω.defSet⊆A segForm p p∈) .snd)) p∈
  sat : ⟨ (ι m ∷ []) ⊨ᵐ segForm ⟩
  sat = subst ⟨_⟩ (Dω.defSet-mem segForm m) p∈m
  out' : ⟨ (ι m ∷ []) ⊨ᵐ segForm ⟩
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
  out' h = PT.rec squash₁ go (segForm-ok m .fst h)
    where
    go : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (⟪ Lset ω ⟫↪ m ≡ pr ξ (Sset ξ)))
       → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (p ≡ pr ξ (Sset ξ))) ∥₁
    go (ξ , (ξ∈ω , q)) = ∣ ξ , (ξ∈ω , p≡m ∙ q) ∣₁
      where
      p≡m : p ≡ ⟪ Lset ω ⟫↪ m
      p≡m = sym (∈-asFiber {a = p} {b = Lset ω} (Dω.defSet⊆A segForm p p∈) .snd)

P∈-in : (ξ : S) → ⟨ ξ ∈ˢ ω ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ P ⟩
P∈-in ξ ξ∈ω = PT.rec (snd (pr ξ (Sset ξ) ∈ˢ P)) go ξ∈ω
  where
  go : Σ[ k ∈ Lift {ℓ-zero} {ℓ} ℕ ] (# (lower k) ≡ ξ)
     → ⟨ pr ξ (Sset ξ) ∈ˢ P ⟩
  go (k , q) = subst (λ w → ⟨ w ∈ˢ P ⟩) (cong₂ pr q (cong Sset q))
    (subst (λ w → ⟨ w ∈ˢ P ⟩) (fib .snd)
      (subst ⟨_⟩ (sym (Dω.defSet-mem segForm m))
        (segForm-ok m .snd ∣ nk (lower k) , ( #∈ω (lower k) , fib .snd ) ∣₁)))
    where
    fib : Σ[ m ∈ ⟪ Lset ω ⟫ ]
            (⟪ Lset ω ⟫↪ m ≡ pr (nk (lower k)) (Sset (nk (lower k))))
    fib = ∈-asFiber {a = pr (nk (lower k)) (Sset (nk (lower k)))}
      {b = Lset ω} (prξSξ∈Lω (nk (lower k)) (#∈ω (lower k)))
    m : ⟪ Lset ω ⟫
    m = fib .fst


T : S
T = pr a₀ (Sset a₀)

seg₀ : S
seg₀ = F5 (F0 P (F0 T T)) T

segRHS : S → hProp (ℓ-suc ℓ)
segRHS x = Logic._⊔_ (x ∈ˢ P) ((x ≡ T) , setIsSet x T)

-- The segment's membership is the disjunction, by the delivered F0/F5
-- specifications (the union reads a member of a member, the pair reads the
-- two members).
seg∈ : (x : S) → ⟨ x ∈ˢ seg₀ ⟩ ⟷ ⟨ segRHS x ⟩
seg∈ x = (out , bwd)
  where
  out : ⟨ x ∈ˢ seg₀ ⟩ → ⟨ segRHS x ⟩
  out h = PT.rec (snd (segRHS x)) o₂ (F5-spec (F0 P (F0 T T)) T x .fst h)
    where
    o₂ : Σ[ v ∈ S ] ⟨ v ∈ˢ F0 P (F0 T T) ⊓ x ∈ˢ v ⟩ → ⟨ segRHS x ⟩
    o₂ (v , (v∈F0 , x∈v)) = PT.rec (snd (segRHS x)) o₃
      (F0-spec P (F0 T T) v .fst v∈F0)
      where
      o₃ : ⟨ v ≡ₕ P ⟩ ⊎ ⟨ v ≡ₕ F0 T T ⟩ → ⟨ segRHS x ⟩
      o₃ (inl v≡P) = ∣ inl (subst (λ w → ⟨ x ∈ˢ w ⟩) v≡P x∈v) ∣₁
      o₃ (inr v≡T) = ∣ inr (PT.rec (setIsSet x T) o₅
        (F0-spec T T x .fst (subst (λ w → ⟨ x ∈ˢ w ⟩) v≡T x∈v))) ∣₁
        where
        o₅ : ⟨ x ≡ₕ T ⟩ ⊎ ⟨ x ≡ₕ T ⟩ → x ≡ T
        o₅ (inl e) = e
        o₅ (inr e) = e
  bwd : ⟨ segRHS x ⟩ → ⟨ x ∈ˢ seg₀ ⟩
  bwd h = PT.rec (snd (x ∈ˢ seg₀)) b' h
    where
    b' : ⟨ x ∈ˢ P ⟩ ⊎ (x ≡ T) → ⟨ x ∈ˢ seg₀ ⟩
    b' (inl x∈P) = F5-spec (F0 P (F0 T T)) T x .snd
      ∣ P
        , ( F0-spec P (F0 T T) P .snd
            ∣ inl refl ∣₁
          , x∈P ) ∣₁
    b' (inr x≡T) = F5-spec (F0 P (F0 T T)) T x .snd
      ∣ F0 T T
        , ( F0-spec P (F0 T T) (F0 T T) .snd
            ∣ inr refl ∣₁
          , F0-spec T T x .snd ∣ inl x≡T ∣₁ ) ∣₁

T∈seg₀ : ⟨ T ∈ˢ seg₀ ⟩
T∈seg₀ = seg∈ T .snd ∣ inr refl ∣₁

-- The values below the limit are in the segment, by the left disjunct.
prξSξ∈seg₀ : (ξ : S) → ⟨ ξ ∈ˢ a₀ ⟩ → ⟨ pr ξ (Sset ξ) ∈ˢ seg₀ ⟩
prξSξ∈seg₀ ξ ξ∈a₀ = seg∈ (pr ξ (Sset ξ)) .snd ∣ inl (P∈-in ξ ξ∈ω) ∣₁
  where
  ξ∈ω : ⟨ ξ ∈ˢ ω ⟩
  ξ∈ω = subst (λ w → ⟨ ξ ∈ˢ w ⟩) a₀≡ω ξ∈a₀

-- The exact domain of the segment: sucV a₀.  Every member of the domain has
-- a pair (the values below via P, the top via T), and every pair's first
-- component lies in the domain.  The in-direction's two branches are named
-- top-level functions with written types (I-5); the T138 shape with two
-- inline lambdas walls past 7.5 minutes.  The out-direction's pgo moves
-- ξ ∈ a₀ to ξ ∈ sucV a₀ through ∈sucV-inl before the transport; the T138
-- shape omits that step and does not typecheck.
segDom-in-below : (a : S) → ⟨ a ∈ˢ a₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁
segDom-in-below a a∈a₀ = ∣ Sset a , prξSξ∈seg₀ a a∈a₀ ∣₁

segDom-in-top : (a : S) → a ≡ a₀ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁
segDom-in-top a a≡a₀ = ∣ Sset a₀ , subst (λ w → ⟨ pr w (Sset a₀) ∈ˢ seg₀ ⟩) (sym a≡a₀) T∈seg₀ ∣₁

segDom-in : (a : S) → ⟨ a ∈ˢ sucV a₀ ⟩
         → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁
segDom-in a a∈suc = ∈sucV-elim {A = a₀} {x = a} squash₁ a∈suc
  (segDom-in-below a) (segDom-in-top a)

segDom-out : (a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ ∥₁ → ⟨ a ∈ˢ sucV a₀ ⟩
segDom-out a = PT.rec (snd (a ∈ˢ sucV a₀)) go
  where
  go : Σ[ b ∈ S ] ⟨ pr a b ∈ˢ seg₀ ⟩ → ⟨ a ∈ˢ sucV a₀ ⟩
  go (b , pr∈) = PT.rec (snd (a ∈ˢ sucV a₀)) d (seg∈ (pr a b) .fst pr∈)
    where
    d : ⟨ pr a b ∈ˢ P ⟩ ⊎ (pr a b ≡ T) → ⟨ a ∈ˢ sucV a₀ ⟩
    d (inl p∈P) = PT.rec (snd (a ∈ˢ sucV a₀)) pgo (P∈-out (pr a b) p∈P)
      where
      pgo : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × (pr a b ≡ pr ξ (Sset ξ)))
          → ⟨ a ∈ˢ sucV a₀ ⟩
      pgo (ξ , (ξ∈ω , q)) = subst (λ w → ⟨ w ∈ˢ sucV a₀ ⟩) (sym (pr-inj q .fst))
        (∈sucV-inl {A = a₀} {x = ξ} (subst (λ w → ⟨ ξ ∈ˢ w ⟩) (sym a₀≡ω) ξ∈ω))
    d (inr q) = subst (λ w → ⟨ w ∈ˢ sucV a₀ ⟩) (pr-inj (sym q) .fst)
      (self∈sucV a₀)

segDom₀ : K0.exactDom seg₀
segDom₀ = ∣ sucV a₀ , ( suca₀∈C , suc-ord a₀-ord , segDom-in , segDom-out ) ∣₁
  where
  suca₀∈C : ⟨ sucV a₀ ∈ˢ C ⟩
  suca₀∈C = Lset-mono {α = β₀} {β = sucV (sucV a₀)} (+ω-iter 2 a₀)
    (ord∈Lset-suc (sucV a₀) (suc-ord a₀-ord))
