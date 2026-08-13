{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T128] The limit-clause gate: is the sixth story clause expressible
-- as an object formula over the carrier, and what does it cost at the first
-- limit where it has content?  Untracked probe, no git, no master.  The
-- clause is written with the delivered kit (LevelKit) and ordinal machinery
-- (OrdArith, OrdBlocks, Ordinal) only, so the archived StepInL is not needed
-- and no scratch tree is used.  The carrier is Lset β₀ with β₀ = +ω a₀ and
-- a₀ = +ω ∅: the first limit a₀ sits strictly below the carrier's index.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT128 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; layer-trans; Lset-layer; isTransV )
open import L.Ordinal {ℓ} using ( ∅-ord; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; isLimit-not-zero; isLimit-not-succ; isSucc
  ; predecessor-mem )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-iter; suc-⊆ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import Cubical.Data.FinData.Base using ( Fin; zero; suc )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2 )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

-- The first limit where the clause has content: a₀ = +ω ∅ (the tree's first
-- limit ordinal) sits strictly below the carrier's index β₀ = +ω a₀, so a
-- story over the domain β₀ has a limit index a₀ at which the sixth clause
-- constrains the value.  At ω = +ω ∅ there is no limit ordinal below it, so
-- the clause is vacuous there and cannot be gated.
a₀ : S
a₀ = +ω ∅

β₀ : S
β₀ = +ω a₀

a₀-ord : IsOrd a₀
a₀-ord = isLimit-ord a₀ (+ω-limit ∅ ∅-ord)

firstLimit : ⟨ isLimit a₀ ⟩
firstLimit = +ω-limit ∅ ∅-ord

β₀-lim : ⟨ isLimit β₀ ⟩
β₀-lim = +ω-limit a₀ a₀-ord

-- The carrier and the kit at it.
C : V ℓ
C = Lset β₀

utr : isTransV C
utr = layer-trans (Lset-layer β₀)

module K = LevelKit C utr
open K public

-- The content point is below the carrier's index: a₀ ∈ Lset β₀, by
-- ord∈Lset-suc plus the successor a₀'s place inside +ω a₀.
a₀∈C : ⟨ a₀ ∈ˢ C ⟩
a₀∈C = Lset-mono {α = β₀} {β = sucV a₀} (+ω-iter 1 a₀) (ord∈Lset-suc a₀ a₀-ord)

-- The limit atom at arity 4, env (b, a, f, x): "a is a limit ordinal", read
-- as: a is an ordinal, a is nonempty, and every member of a has a member
-- above it.  The meta-level limit predicate is the delivered isLimit
-- (IsOrd × not-zero × not-succ); the atom's two-way decode (limAt-ok) is the
-- bridge between the two readings.
limAt : Formula ⟪ C ⟫ 4
limAt = isOrdAt (suc zero)
     ∧̇ (∃̇∈ (var (suc zero)) (var zero ≐ var zero))
     ∧̇ (∀̇∈ (var (suc zero))
           (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero)))

-- The pair membership pr a b ∈ f at arity 4, env (b, a, f, x).
pairIn : Formula ⟪ C ⟫ 4
pairIn = ∃̇∈ (var (suc (suc zero)))
           (PK.prAt zero (suc (suc zero)) (suc zero))

-- The union membership reading at arity 5, env (z, b, a, f, x):
-- ∃ ξ ∈ a, ∃ w, ∃ p ∈ f, p = pr ξ w ∧ z ∈ w.  The ξ-quantifier is bounded
-- inside the carrier (∃̇∈ over members of a, each a carrier member by
-- transitivity); the w-quantifier is unbounded but the satisfaction is read
-- at the carrier-restricted structure, whose universe is the carrier.
-- The innermost quantifier body, at arity 7, env (w, ξ, z, b, a, f, x):
-- ∃ p ∈ f, p = pr ξ w ∧ z ∈ w.
inner7 : Formula ⟪ C ⟫ 7
inner7 = ∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
           (PK.prAt zero (suc (suc zero)) (suc zero)
              ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero)))

unionRHS : Formula ⟪ C ⟫ 5
unionRHS = ∃̇∈ (var (suc (suc zero))) (∃̇ inner7)

-- The conclusion at arity 4, env (b, a, f, x): for every z, z ∈ b ⟷ the
-- union reading (the pointwise form of b = ⋃ { w : ∃ ξ < a, pr ξ w ∈ f },
-- the R-35 small-index statement).
limitConc : Formula ⟪ C ⟫ 4
limitConc = ∀̇ ( (var zero ∈̇ var (suc zero) ⇒̇ unionRHS)
             ∧̇ (unionRHS ⇒̇ var zero ∈̇ var (suc zero)) )

-- The clause body at arity 4: a limit index with pr a b ∈ f forces the
-- value to be the union of the values below.
limitBody : Formula ⟪ C ⟫ 4
limitBody = (limAt ∧̇ pairIn) ⇒̇ limitConc

-- The sixth clause as an object formula at the standing arity 2, env (f, x).
limitForm : Formula ⟪ C ⟫ 2
limitForm = ∀̇ (∀̇ limitBody)

-- The sixth clause at the meta level: at a limit index, the value is the
-- union of the values below, stated pointwise (no union representation is
-- built; membership is read at the small index, per R-35).
limitClause : S → Type (ℓ-suc ℓ)
limitClause f = (a b : S) → ⟨ isLimit a ⟩ → ⟨ pr a b ∈ˢ f ⟩
  → (z : S) → ⟨ z ∈ˢ b ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
       × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁

-- The limit characterization the atom decode rests on.  For an ordinal a,
-- "every member has a member above it" is the not-a-successor half of the
-- delivered limit predicate: if a were sucV β then β ∈ a has no member of a
-- above it (β ∈ η ∈ a = sucV β forces β ∈ β by transitivity), and if a has
-- no member above ξ then every member of a is in ξ or is ξ, so a = sucV ξ.
-- Both halves are classical in the extraction direction (lem), and both are
-- stated with the memberships at the small index, per R-35.

noAbove→succ : (a ξ : S) → IsOrd a → ⟨ ξ ∈ˢ a ⟩
             → ((η : S) → ⟨ η ∈ˢ a ⟩ → ⟨ ξ ∈ˢ η ⟩ → Empty.⊥)
             → ⟨ isSucc a ⟩
noAbove→succ a ξ ordA ξ∈a noAbove = (ξ , (mem-ord {A = a} ordA ξ ξ∈a , a≡sucξ))
  where
  a≡sucξ : sucV ξ ≡ a
  a≡sucξ = sym (ext-⊆ {a} {sucV ξ} a⊆suc sucξ⊆a)
    where
    a⊆suc : a ⊆ sucV ξ
    a⊆suc x x∈a = go (ord-tri x (mem-ord {A = a} ordA x x∈a)
                       ξ (mem-ord {A = a} ordA ξ ξ∈a))
      where
      go : Tri x ξ → ⟨ x ∈ˢ sucV ξ ⟩
      go (inl x∈ξ) = ∈sucV-inl {A = ξ} {x = x} x∈ξ
      go (inr (inl x≡ξ)) = subst (λ w → ⟨ w ∈ˢ sucV ξ ⟩) (sym x≡ξ) (self∈sucV ξ)
      go (inr (inr ξ∈x)) = Empty.rec (noAbove x x∈a ξ∈x)
    sucξ⊆a : sucV ξ ⊆ a
    sucξ⊆a = suc-⊆ {A = a} {x = ξ} ordA ξ∈a

closedFromLim : (a : S) → ⟨ isLimit a ⟩
              → (ξ : S) → ⟨ ξ ∈ˢ a ⟩
              → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩ × ⟨ ξ ∈ˢ η ⟩) ∥₁
closedFromLim a lim ξ ξ∈a = decide (lem (∥ P ∥₁ , squash₁))
  where
  P : Type (ℓ-suc ℓ)
  P = Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩ × ⟨ ξ ∈ˢ η ⟩)
  decide : ∥ P ∥₁ ⊎ (∥ P ∥₁ → Empty.⊥) → ∥ P ∥₁
  decide (inl h) = h
  decide (inr np) = Empty.rec
    (isLimit-not-succ a lim
      (noAbove→succ a ξ (isLimit-ord a lim) ξ∈a noAbove))
    where
    noAbove : (η : S) → ⟨ η ∈ˢ a ⟩ → ⟨ ξ ∈ˢ η ⟩ → Empty.⊥
    noAbove η η∈a ξ∈η = np ∣ η , (η∈a , ξ∈η) ∣₁

nonemptyFromLim : (a : S) → ⟨ isLimit a ⟩ → ∥ Σ[ ξ ∈ S ] ⟨ ξ ∈ˢ a ⟩ ∥₁
nonemptyFromLim a lim = decide (lem (∥ P ∥₁ , squash₁))
  where
  P : Type (ℓ-suc ℓ)
  P = Σ[ ξ ∈ S ] ⟨ ξ ∈ˢ a ⟩
  decide : ∥ P ∥₁ ⊎ (∥ P ∥₁ → Empty.⊥) → ∥ P ∥₁
  decide (inl h) = h
  decide (inr np) = Empty.rec
    (isLimit-not-zero a lim (empty→∅ (λ ξ ξ∈a → np ∣ ξ , ξ∈a ∣₁)))
    where
    empty→∅ : ((ξ : S) → ⟨ ξ ∈ˢ a ⟩ → Empty.⊥) → a ≡ ∅
    empty→∅ ne = ext-⊆ {a} {∅} subs sup
      where
      subs : (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ ∅ ⟩
      subs x x∈a = Empty.rec (ne x x∈a)
      sup : (x : S) → ⟨ x ∈ˢ ∅ ⟩ → ⟨ x ∈ˢ a ⟩
      sup x x∈∅ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))

-- The limit atom's two-way decode: the object formula "a is a limit
-- ordinal" is satisfied exactly when the delivered meta-level limit
-- predicate holds at a.  The ordinal bridge above is the content.
limAt-ok : (δ : Vec SM 4) → ⟨ δ ⊨ᵐ limAt ⟩ ⟷ ⟨ isLimit (fst (lookup (suc zero) δ)) ⟩
limAt-ok δ = (out , bwd)
  where
  valA : S
  valA = fst (lookup (suc zero) δ)

  out : ⟨ δ ⊨ᵐ limAt ⟩ → ⟨ isLimit valA ⟩
  out (ord-sat , (ne-sat , cl-sat)) = ( ordA , nz , ns )
    where
    ordA : IsOrd valA
    ordA = isOrd-out (suc zero) δ ord-sat
    nz : (valA ≡ ∅) → Empty.⊥
    nz e = PT.rec Empty.isProp⊥ step ne-sat
      where
      step : Σ[ ξm ∈ SM ] (⟨ fst ξm ∈ˢ valA ⟩
                          × ⟨ (ξm ∷ δ) ⊨ᵐ (var zero ≐ var zero) ⟩)
           → Empty.⊥
      step (ξm , (ξ∈A , _)) =
        ∅-empty (fst ξm)
          (∈∈ₛ {a = fst ξm} {b = ∅} .fst
            (subst (λ w → ⟨ fst ξm ∈ˢ w ⟩) e ξ∈A))
    ns : ⟨ isSucc valA ⟩ → Empty.⊥
    ns (β , ordβ , eq) = PT.rec Empty.isProp⊥ step (cl-sat βm β∈a)
      where
      β∈a : ⟨ β ∈ˢ valA ⟩
      β∈a = predecessor-mem β valA eq
      β∈C : ⟨ β ∈ˢ C ⟩
      β∈C = utr {x = valA} {y = β} β∈a (snd (lookup (suc zero) δ))
      βm : SM
      βm = PK.pt β β∈C
      step : Σ[ ηm ∈ SM ] (⟨ fst ηm ∈ˢ valA ⟩ × ⟨ β ∈ˢ fst ηm ⟩)
           → Empty.⊥
      step (ηm , (η∈a , β∈η)) = Empty.rec* {A = Empty.⊥}
        (∈sucV-elim {A = β} {x = fst ηm} {P = Empty.⊥* {ℓ-suc ℓ}}
          (Empty.isProp⊥* {ℓ-suc ℓ})
          (subst (λ w → ⟨ fst ηm ∈ˢ w ⟩) (sym eq) η∈a) inβ inEq)
        where
        inβ : ⟨ fst ηm ∈ˢ β ⟩ → Empty.⊥* {ℓ-suc ℓ}
        inβ η∈β = lift (∈-irrefl β (ordβ .fst {x = fst ηm} {y = β} β∈η η∈β))
        inEq : fst ηm ≡ β → Empty.⊥* {ℓ-suc ℓ}
        inEq e' = lift (∈-irrefl β (subst (λ w → ⟨ β ∈ˢ w ⟩) e' β∈η))

  bwd : ⟨ isLimit valA ⟩ → ⟨ δ ⊨ᵐ limAt ⟩
  bwd lim = ( ord-sat , (ne-sat , cl-sat) )
    where
    ordA : IsOrd valA
    ordA = isLimit-ord valA lim
    ord-sat : ⟨ δ ⊨ᵐ isOrdAt (suc zero) ⟩
    ord-sat = isOrd-in (suc zero) δ ordA
    ne-sat : ⟨ δ ⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero) ⟩
    ne-sat = PT.rec (snd (δ ⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero)))
      go (nonemptyFromLim valA lim)
      where
      go : Σ[ ξ ∈ S ] ⟨ ξ ∈ˢ valA ⟩
         → ⟨ δ ⊨ᵐ ∃̇∈ (var (suc zero)) (var zero ≐ var zero) ⟩
      go (ξ , ξ∈a) = ∣ ξm , (ξ∈a , refl) ∣₁
        where
        ξm : SM
        ξm = PK.pt ξ (utr {x = valA} {y = ξ} ξ∈a (snd (lookup (suc zero) δ)))
    cl-sat : ⟨ δ ⊨ᵐ ∀̇∈ (var (suc zero))
                (∃̇∈ (var (suc (suc zero))) (var (suc zero) ∈̇ var zero)) ⟩
    cl-sat ξm ξ∈a = PT.rec
      (snd ((ξm ∷ δ) ⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                 (var (suc zero) ∈̇ var zero)))
      go (closedFromLim valA lim (fst ξm) ξ∈a)
      where
      go : Σ[ η ∈ S ] (⟨ η ∈ˢ valA ⟩ × ⟨ fst ξm ∈ˢ η ⟩)
         → ⟨ (ξm ∷ δ) ⊨ᵐ ∃̇∈ (var (suc (suc zero)))
               (var (suc zero) ∈̇ var zero) ⟩
      go (η , (η∈a , ξ∈η)) = ∣ ηm , (η∈a , ξ∈η) ∣₁
        where
        ηm : SM
        ηm = PK.pt η (utr {x = valA} {y = η} η∈a (snd (lookup (suc zero) δ)))

-- The union membership reading's two-way decode at arity 5, env (z, b, a,
-- f, x): the formula is satisfied exactly when z ∈ b's RHS reading holds,
-- i.e. some ξ < a has a value w with pr ξ w ∈ f and z ∈ w.  The decode
-- walks the three quantifiers; the innermost pair membership is the kit's
-- pair∈ shape, and the z ∈ w conjunct is the atomic membership itself.
unionRHS-ok : (δ : Vec SM 5) → ⟨ δ ⊨ᵐ unionRHS ⟩
  ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ fst (lookup (suc (suc zero)) δ) ⟩
       × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst (lookup (suc (suc (suc zero))) δ) ⟩
           × ⟨ fst (lookup zero δ) ∈ˢ w ⟩) ∥₁) ∥₁
unionRHS-ok δ = (out , bwd)
  where
  valZ : S
  valZ = fst (lookup zero δ)
  valA : S
  valA = fst (lookup (suc (suc zero)) δ)
  valF : S
  valF = fst (lookup (suc (suc (suc zero))) δ)

  out : ⟨ δ ⊨ᵐ unionRHS ⟩
      → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
           × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
  out sat = PT.rec squash₁ step₁ sat
    where
    step₁ : Σ[ ξm ∈ SM ] (⟨ fst ξm ∈ˢ valA ⟩
          × ⟨ (ξm ∷ δ) ⊨ᵐ ∃̇ inner7 ⟩)
          → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
               × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
    step₁ (ξm , (ξ∈a , rest)) = PT.rec squash₁ step₂ rest
      where
      step₂ : Σ[ wm ∈ SM ] ⟨ (wm ∷ ξm ∷ δ) ⊨ᵐ inner7 ⟩
            → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                 × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
      step₂ (wm , wm-sat) = PT.rec squash₁ step₃ wm-sat
        where
        step₃ : Σ[ pm ∈ SM ] (⟨ fst pm ∈ˢ valF ⟩
              × ⟨ (pm ∷ wm ∷ ξm ∷ δ) ⊨ᵐ
                   (PK.prAt zero (suc (suc zero)) (suc zero)
                      ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero))) ⟩)
              → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
                   × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
        step₃ (pm , (pm∈f , (pr-sat , z∈w-sat))) =
          ∣ fst ξm , ( ξ∈a
            , ∣ fst wm , ( prξw∈f , z∈w ) ∣₁ ) ∣₁
          where
          p≡prξw : fst pm ≡ pr (fst ξm) (fst wm)
          p≡prξw = PK.prAt-out zero (suc (suc zero)) (suc zero)
            (pm ∷ wm ∷ ξm ∷ δ) pr-sat
          prξw∈f : ⟨ pr (fst ξm) (fst wm) ∈ˢ valF ⟩
          prξw∈f = subst (λ t → ⟨ t ∈ˢ valF ⟩) p≡prξw pm∈f
          z∈w : ⟨ valZ ∈ˢ fst wm ⟩
          z∈w = z∈w-sat

  bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
          × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁) ∥₁
      → ⟨ δ ⊨ᵐ unionRHS ⟩
  bwd h = PT.rec (snd (δ ⊨ᵐ unionRHS)) step₁ h
    where
    step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ valA ⟩
          × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩) ∥₁)
          → ⟨ δ ⊨ᵐ unionRHS ⟩
    step₁ (ξ , (ξ∈a , rest)) = PT.rec (snd (δ ⊨ᵐ unionRHS)) step₂ rest
      where
      ξm : SM
      ξm = PK.pt ξ (utr {x = valA} {y = ξ} ξ∈a (snd (lookup (suc (suc zero)) δ)))
      step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ valF ⟩ × ⟨ valZ ∈ˢ w ⟩)
            → ⟨ δ ⊨ᵐ unionRHS ⟩
      step₂ (w , (pw∈f , z∈w)) = ∣ ξm , (ξ∈a , inner∃) ∣₁
        where
        w∈C : ⟨ w ∈ˢ C ⟩
        w∈C = PM.pair-right {a = ξ} {b = w}
          (utr {x = valF} {y = pr ξ w} pw∈f (snd (lookup (suc (suc (suc zero))) δ)))
        wm : SM
        wm = PK.pt w w∈C
        pr∈C : ⟨ pr ξ w ∈ˢ C ⟩
        pr∈C = utr {x = valF} {y = pr ξ w} pw∈f
          (snd (lookup (suc (suc (suc zero))) δ))
        pm : SM
        pm = PK.pt (pr ξ w) pr∈C
        pr-sat : ⟨ (pm ∷ wm ∷ ξm ∷ δ) ⊨ᵐ
                   PK.prAt zero (suc (suc zero)) (suc zero) ⟩
        pr-sat = PK.prAt-in zero (suc (suc zero)) (suc zero)
          (pm ∷ wm ∷ ξm ∷ δ) refl
        z∈w-sat : ⟨ (pm ∷ wm ∷ ξm ∷ δ) ⊨ᵐ
                    (var (suc (suc (suc zero))) ∈̇ var (suc zero)) ⟩
        z∈w-sat = z∈w
        inner : ⟨ (wm ∷ ξm ∷ δ) ⊨ᵐ inner7 ⟩
        inner = ∣ pm , (pw∈f , (pr-sat , z∈w-sat)) ∣₁
        inner∃ : ⟨ (ξm ∷ δ) ⊨ᵐ ∃̇ inner7 ⟩
        inner∃ = ∣ wm , inner ∣₁

-- The sixth clause's two-way decode at the standing arity: the object
-- formula is satisfied exactly when the meta-level limit clause holds.  The
-- out direction reads the antecedent's limit and pair memberships back into
-- the meta hypotheses (limAt-ok, pair∈), walks the conclusion's quantifiers
-- through unionRHS-ok, and reassembles the pointwise union.  The in
-- direction decodes the antecedent satisfaction to the meta hypotheses,
-- applies the clause, and rebuilds the conclusion's satisfaction.
limit-ok : (f : SM) (x : ⟪ C ⟫) → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ limitForm ⟩ ⟷ limitClause (fst f)
limit-ok f x = (out , bwd)
  where
  δ₂ : Vec SM 2
  δ₂ = f ∷ ι x ∷ []

  out : ⟨ δ₂ ⊨ᵐ limitForm ⟩ → limitClause (fst f)
  out h a b lim ab∈f z = (fwd , bwd)
    where
    a∈C : ⟨ a ∈ˢ C ⟩
    a∈C = PM.pair-left {a = a} {b = b}
      (utr {x = fst f} {y = pr a b} ab∈f (snd f))
    b∈C : ⟨ b ∈ˢ C ⟩
    b∈C = PM.pair-right {a = a} {b = b}
      (utr {x = fst f} {y = pr a b} ab∈f (snd f))
    am : SM
    am = PK.pt a a∈C
    bm : SM
    bm = PK.pt b b∈C
    body-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitBody ⟩
    body-sat = h am bm
    conc-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitConc ⟩
    conc-sat = body-sat (limAt-sat , pairIn-sat)
      where
      limAt-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limAt ⟩
      limAt-sat = limAt-ok (bm ∷ am ∷ f ∷ ι x ∷ []) .snd lim
      pairIn-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ pairIn ⟩
      pairIn-sat = pair∈ (suc (suc zero)) (suc zero) zero
        (bm ∷ am ∷ f ∷ ι x ∷ []) .snd ab∈f
    fwd : ⟨ z ∈ˢ b ⟩
        → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
             × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
    fwd z∈b = unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .fst
      (conc-sat zm .fst z∈b)
      where
      z∈C : ⟨ z ∈ˢ C ⟩
      z∈C = utr {x = b} {y = z} z∈b b∈C
      zm : SM
      zm = PK.pt z z∈C
    bwd : ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
            × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
        → ⟨ z ∈ˢ b ⟩
    bwd hz = conc-sat zm .snd (unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .snd hz)
      where
      z∈C : ⟨ z ∈ˢ C ⟩
      z∈C = PT.rec (snd (z ∈ˢ C)) step₁ hz
        where
        step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
              × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
              → ⟨ z ∈ˢ C ⟩
        step₁ (ξ , (ξ∈a , rest)) = PT.rec (snd (z ∈ˢ C)) step₂ rest
          where
          step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ fst f ⟩ × ⟨ z ∈ˢ w ⟩) → ⟨ z ∈ˢ C ⟩
          step₂ (w , (pw∈f , z∈w)) = utr {x = w} {y = z} z∈w w∈C
            where
            w∈C : ⟨ w ∈ˢ C ⟩
            w∈C = PM.pair-right {a = ξ} {b = w}
              (utr {x = fst f} {y = pr ξ w} pw∈f (snd f))
      zm : SM
      zm = PK.pt z z∈C

  bwd : limitClause (fst f) → ⟨ δ₂ ⊨ᵐ limitForm ⟩
  bwd lc am bm = body-sat
    where
    body-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitBody ⟩
    body-sat (limAt-sat , pairIn-sat) = conc-sat
      where
      lim : ⟨ isLimit (fst am) ⟩
      lim = limAt-ok (bm ∷ am ∷ f ∷ ι x ∷ []) .fst limAt-sat
      ab∈f : ⟨ pr (fst am) (fst bm) ∈ˢ fst f ⟩
      ab∈f = pair∈ (suc (suc zero)) (suc zero) zero
        (bm ∷ am ∷ f ∷ ι x ∷ []) .fst pairIn-sat
      conc-sat : ⟨ (bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ limitConc ⟩
      conc-sat zm = ( fwd , back )
        where
        fwd : ⟨ fst zm ∈ˢ fst bm ⟩ → ⟨ (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ unionRHS ⟩
        fwd z∈b = unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .snd
          (lc (fst am) (fst bm) lim ab∈f (fst zm) .fst z∈b)
        back : ⟨ (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) ⊨ᵐ unionRHS ⟩
             → ⟨ fst zm ∈ˢ fst bm ⟩
        back rhssat = lc (fst am) (fst bm) lim ab∈f (fst zm) .snd
          (unionRHS-ok (zm ∷ bm ∷ am ∷ f ∷ ι x ∷ []) .fst rhssat)

-- Exercise: the clause is live at the first limit where it has content.
-- The content point is a₀ = +ω ∅: a limit ordinal strictly below the
-- carrier's index β₀ = +ω a₀ (so a story over the domain β₀ has a limit
-- index at which the sixth clause constrains the value).  At ω = +ω ∅ the
-- clause is vacuous, because every member of ω is a numeral and none is a
-- limit ordinal; that is why the gate had to reach β₀.
am : SM
am = PK.pt a₀ a₀∈C

x₀ : ⟪ C ⟫
x₀ = ∈-asFiber {a = a₀} {b = C} a₀∈C .fst

-- The limit reading is live at the first limit, in both directions: the
-- atom is satisfied at a₀ exactly because a₀ is a limit ordinal.
lim-read : ⟨ (am ∷ am ∷ am ∷ ι x₀ ∷ []) ⊨ᵐ limAt ⟩
lim-read = limAt-ok (am ∷ am ∷ am ∷ ι x₀ ∷ []) .snd firstLimit

lim-read-back : ⟨ isLimit a₀ ⟩
lim-read-back = limAt-ok (am ∷ am ∷ am ∷ ι x₀ ∷ []) .fst lim-read

-- The clause decode at the carrier, read at the first-limit point: the
-- formula is satisfied by exactly the graphs that satisfy the meta-level
-- limit clause, both directions, with the content point in the domain.
clause-read : ⟨ (am ∷ ι x₀ ∷ []) ⊨ᵐ limitForm ⟩ ⟷ limitClause a₀
clause-read = limit-ok am x₀
