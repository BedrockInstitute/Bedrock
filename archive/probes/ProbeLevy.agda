{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T54] The Levy-certificate gate: measure the per-clause rate.
-- Bounded rewrites + Delta-0 witnesses of the level story's six clauses at
-- the generic carrier u with binding set K (P-h full strength), plus the
-- Sigma-1 witness of the face's sigma.  Untracked probe; one Agda process.

open import Base.Prelude
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-∃∈; δ-∀∈; Σ₁; σ-Δ₀ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

module ProbeLevy {ℓ : Level} (u : V ℓ) (K : ⟪ u ⟫) where

  -- Variable zero at any depth: what the bounded quantifiers bind.
  f0 : {n : ℕ} → Fin (suc n)
  f0 = zero

  -- "var k is a singleton": inhabited, all members equal.
  sgl : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  sgl k = ∃̇∈ (var k) (∀̇∈ (var (suc k)) (var f0 ≐ var (suc zero)))

  sglΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (sgl k)
  sglΔ₀ k = δ-∃∈ (δ-∀∈ δ-≐)

  -- "var k is an unordered pair of two distinct sets".
  pair2 : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  pair2 k = ∃̇∈ (var k) (∃̇∈ (var (suc k))
             ( ¬̇ (var f0 ≐ var (suc zero))
             ∧̇ ∀̇∈ (var (suc (suc k)))
                  ((var f0 ≐ var (suc zero)) ∨̇ (var f0 ≐ var (suc (suc zero))))))

  pair2Δ₀ : {n : ℕ} (k : Fin n) → Δ₀ (pair2 k)
  pair2Δ₀ k = δ-∃∈ (δ-∃∈ (δ-∧ (δ-¬ δ-≐) (δ-∀∈ (δ-∨ δ-≐ δ-≐))))

  -- "var k is a Kuratowski pair", degenerate pairs allowed: a singleton
  -- member x; every other member is a two-element set containing x's
  -- element; at most two members.
  kpair : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  kpair k = ∃̇∈ (var k)
             ( sgl f0
             ∧̇ ∀̇∈ (var (suc k))
                  ((var f0 ≐ var (suc zero))
                ∨̇ (pair2 f0 ∧̇ ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero))))
             ∧̇ ∀̇∈ (var (suc k)) (∀̇∈ (var (suc (suc k))) (∀̇∈ (var (suc (suc (suc k))))
                  ((var (suc zero) ≐ var (suc (suc zero)))
                ∨̇ (var f0 ≐ var (suc (suc zero)))
                ∨̇ (var f0 ≐ var (suc zero))))))

  kpairΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (kpair k)
  kpairΔ₀ k = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                 (δ-∧ (δ-∀∈ (δ-∨ δ-≐ (δ-∧ (pair2Δ₀ f0) (δ-∀∈ δ-∈))))
                      (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∨ δ-≐ (δ-∨ δ-≐ δ-≐)))))))

  -- "the first component of var k equals var a" (var k a Kuratowski pair).
  fstEqTo : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  fstEqTo k a = ∃̇∈ (var k) (sgl f0 ∧̇ ∀̇∈ (var zero) (var f0 ≐ var (suc (suc a))))

  fstEqToΔ₀ : {n : ℕ} (k a : Fin n) → Δ₀ (fstEqTo k a)
  fstEqToΔ₀ k a = δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ δ-≐))

  -- "the first component of var k is a member of the first component of
  -- var l" (both Kuratowski pairs).
  fstLt : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  fstLt k l = ∃̇∈ (var k) (sgl f0 ∧̇ ∃̇∈ (var (suc l))
               (sgl f0 ∧̇ ∃̇∈ (var zero)
                 (∀̇∈ (var (suc (suc zero))) (var f0 ∈̇ var (suc zero)))))

  fstLtΔ₀ : {n : ℕ} (k l : Fin n) → Δ₀ (fstLt k l)
  fstLtΔ₀ k l = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                (δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∃∈ (δ-∀∈ δ-∈)))))

  -- "var k is a member of the second component of var l".
  sndIn : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  sndIn ku kw = ∃̇∈ (var kw) (sgl f0 ∧̇
                ∃̇∈ (var (suc kw)) (pair2 f0 ∧̇
                  ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero)) ∧̇
                  var (suc (suc ku)) ∈̇ var f0 ∧̇
                  ∀̇∈ (var (suc zero)) (¬̇ (var f0 ≐ var (suc (suc (suc ku)))))))

  sndInΔ₀ : {n : ℕ} (ku kw : Fin n) → Δ₀ (sndIn ku kw)
  sndInΔ₀ ku kw = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                  (δ-∃∈ (δ-∧ (pair2Δ₀ f0)
                    (δ-∧ (δ-∀∈ δ-∈) (δ-∧ δ-∈ (δ-∀∈ (δ-¬ δ-≐)))))))

  -- "the second component of var k is a member of the second component of
  -- var l".
  snd∈Snd : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  snd∈Snd k l = ∃̇∈ (var k) (sgl f0 ∧̇
                ∃̇∈ (var (suc k)) (pair2 f0 ∧̇
                  ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero)) ∧̇
                  ∃̇∈ (var zero) (∀̇∈ (var (suc (suc zero))) (¬̇ (var f0 ≐ var (suc zero)))
                                ∧̇ sndIn f0 (suc (suc (suc l))))))

  snd∈SndΔ₀ : {n : ℕ} (k l : Fin n) → Δ₀ (snd∈Snd k l)
  snd∈SndΔ₀ k l = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                  (δ-∃∈ (δ-∧ (pair2Δ₀ f0)
                    (δ-∧ (δ-∀∈ δ-∈) (δ-∃∈ (δ-∧ (δ-∀∈ (δ-¬ δ-≐)) (sndInΔ₀ f0 (suc (suc (suc l))))))))))

  -- The ordinal predicate (delivered shape, already bounded).
  isOrdAt' : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  isOrdAt' k = (∀̇∈ (var k) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc k)))))
            ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

  isOrdAtΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (isOrdAt' k)
  isOrdAtΔ₀ k = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

  -- The limit-ordinal predicate, bounded: ordinal, nonempty, no greatest.
  isLimitAt' : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  isLimitAt' k = isOrdAt' k ∧̇ (∃̇∈ (var k) ⊤̇)
              ∧̇ (∀̇∈ (var k) (∃̇∈ (var (suc k)) (var (suc zero) ∈̇ var zero)))

  isLimitAtΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (isLimitAt' k)
  isLimitAtΔ₀ k = δ-∧ (isOrdAtΔ₀ k) (δ-∧ (δ-∃∈ δ-⊤) (δ-∀∈ (δ-∃∈ δ-∈)))

  -- "the first component of var k is a limit ordinal".
  isLimitOf : {n : ℕ} → Fin n → Formula ⟪ u ⟫ n
  isLimitOf k = ∃̇∈ (var k) (sgl f0 ∧̇ ∀̇∈ (var zero) (isLimitAt' f0))

  isLimitOfΔ₀ : {n : ℕ} (k : Fin n) → Δ₀ (isLimitOf k)
  isLimitOfΔ₀ k = δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (isLimitAtΔ₀ f0)))

  -- "the first components of var k and var l are equal" (both pairs).
  fstEq : {n : ℕ} → Fin n → Fin n → Formula ⟪ u ⟫ n
  fstEq k l = ∃̇∈ (var k) (sgl f0 ∧̇ ∃̇∈ (var (suc l))
              (sgl f0 ∧̇ ∀̇∈ (var (suc zero)) (∀̇∈ (var zero) (var f0 ≐ var (suc zero)))))

  fstEqΔ₀ : {n : ℕ} (k l : Fin n) → Δ₀ (fstEq k l)
  fstEqΔ₀ k l = δ-∃∈ (δ-∧ (sglΔ₀ f0)
                (δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (δ-∀∈ δ-≐)))))

  -- THE SIX CLAUSES, at the face's generic carrier (arity 2: f at var 0,
  -- the read member x at var 1).

  -- D-10 first: the two predicted resisters.
  -- (1) pairForm: every member of f is a Kuratowski pair.  The unbounded
  -- pair existentials become the structural pair predicate, bounded by z.
  pairForm' : Formula ⟪ u ⟫ 2
  pairForm' = ∀̇∈ (var zero) (kpair f0)

  pairFormΔ₀ : Δ₀ pairForm'
  pairFormΔ₀ = δ-∀∈ (kpairΔ₀ f0)

  -- (4) domForm: the first components of the pairs of f form an ordinal,
  -- i.e. a transitive set with transitive members.  The unbounded ordinal
  -- witness delta is replaced by the structural D-is-an-ordinal read.
  domForm' : Formula ⟪ u ⟫ 2
  domForm' = (∀̇∈ (var zero) (kpair f0 ⇒̇
               ∀̇∈ (var zero) (sgl f0 ⇒̇
                 ∀̇∈ (var zero) (∀̇∈ (var zero)
                   (∃̇∈ (var (suc (suc (suc (suc zero)))))
                      (kpair f0 ∧̇ fstEqTo f0 (suc (suc (suc zero)))))))))
           ∧̇
             (∀̇∈ (var zero) (kpair f0 ⇒̇
               ∀̇∈ (var zero) (sgl f0 ⇒̇
                 ∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero)
                   (∃̇∈ (var (suc (suc (suc zero)))) (var (suc zero) ∈̇ var zero)))))))

  domFormΔ₀ : Δ₀ domForm'
  domFormΔ₀ = δ-∧
    (δ-∀∈ (δ-⇒ (kpairΔ₀ f0)
       (δ-∀∈ (δ-⇒ (sglΔ₀ f0)
         (δ-∀∈ (δ-∀∈ (δ-∃∈ (δ-∧ (kpairΔ₀ f0) (fstEqToΔ₀ f0 (suc (suc (suc zero))))))))))))
    (δ-∀∈ (δ-⇒ (kpairΔ₀ f0)
       (δ-∀∈ (δ-⇒ (sglΔ₀ f0)
         (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∃∈ δ-∈))))))))

  -- (2) singleForm: two pairs of f with equal first components are equal.
  singleForm' : Formula ⟪ u ⟫ 2
  singleForm' = ∀̇∈ (var zero) (∀̇∈ (var (suc zero))
                 (fstEq f0 (suc zero) ⇒̇ var (suc zero) ≐ var zero))

  singleFormΔ₀ : Δ₀ singleForm'
  singleFormΔ₀ = δ-∀∈ (δ-∀∈ (δ-⇒ (fstEqΔ₀ f0 (suc zero)) δ-≐))

  -- (3) zeroForm: some memberless a has pr a a in f, i.e. f has a member
  -- that is the singleton of a singleton of a memberless set.
  zeroForm' : Formula ⟪ u ⟫ 2
  zeroForm' = ∃̇∈ (var zero) (sgl f0 ∧̇ ∀̇∈ (var zero)
                (sgl f0 ∧̇ ∀̇∈ (var zero) (¬̇ (∃̇∈ (var f0) ⊤̇))))

  zeroFormΔ₀ : Δ₀ zeroForm'
  zeroFormΔ₀ = δ-∃∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (δ-∧ (sglΔ₀ f0) (δ-∀∈ (δ-¬ (δ-∃∈ δ-⊤))))))

  -- (5) limitForm: at a limit point (a, y) of the graph, y is the union of
  -- the values below a, as two inclusions over the pairs of f.
  limIn : Formula ⟪ u ⟫ 3
  limIn = ∃̇∈ (var zero) (sgl f0 ∧̇
          ∃̇∈ (var zero) (pair2 f0 ∧̇
            ∀̇∈ (var (suc zero)) (var f0 ∈̇ var (suc zero)) ∧̇
            ∀̇∈ (var (suc zero)) (∀̇∈ (var (suc (suc zero))) (¬̇ (var f0 ≐ var (suc zero)))
              ⇒̇ ∃̇∈ (var (suc (suc (suc (suc zero)))))
                   (kpair f0 ∧̇ fstLt f0 (suc (suc (suc (suc zero))))
                         ∧̇ sndIn (suc zero) f0))))

  limInΔ₀ : Δ₀ limIn
  limInΔ₀ = δ-∃∈ (δ-∧ (sglΔ₀ f0)
            (δ-∃∈ (δ-∧ (pair2Δ₀ f0)
              (δ-∧ (δ-∀∈ δ-∈)
                  (δ-∀∈ (δ-⇒ (δ-∀∈ (δ-¬ δ-≐))
                    (δ-∃∈ (δ-∧ (kpairΔ₀ f0)
                      (δ-∧ (fstLtΔ₀ f0 (suc (suc (suc (suc zero)))))
                            (sndInΔ₀ (suc zero) f0))))))))))

  limOut : Formula ⟪ u ⟫ 3
  limOut = ∀̇∈ (var (suc zero)) (kpair f0 ⇒̇ fstLt f0 (suc zero) ⇒̇ snd∈Snd f0 (suc zero))

  limOutΔ₀ : Δ₀ limOut
  limOutΔ₀ = δ-∀∈ (δ-⇒ (kpairΔ₀ f0) (δ-⇒ (fstLtΔ₀ f0 (suc zero)) (snd∈SndΔ₀ f0 (suc zero))))

  limitForm' : Formula ⟪ u ⟫ 2
  limitForm' = ∀̇∈ (var zero) (kpair f0 ⇒̇ isLimitOf f0 ⇒̇ (limIn ∧̇ limOut))

  limitFormΔ₀ : Δ₀ limitForm'
  limitFormΔ₀ = δ-∀∈ (δ-⇒ (kpairΔ₀ f0) (δ-⇒ (isLimitOfΔ₀ f0) (δ-∧ limInΔ₀ limOutΔ₀)))

  -- (6) rangeForm: the read member x is the second component of a pair of f.
  Rg' : Formula ⟪ u ⟫ 2
  Rg' = ∃̇∈ (var zero) (kpair f0 ∧̇ sndIn (suc (suc zero)) f0)

  rangeForm' : Formula ⟪ u ⟫ 2
  rangeForm' = Rg'

  rangeFormΔ₀ : Δ₀ rangeForm'
  rangeFormΔ₀ = δ-∃∈ (δ-∧ (kpairΔ₀ f0) (sndInΔ₀ (suc (suc zero)) f0))

  -- The assembled level story and its Sigma-1 witness.
  Ap' : Formula ⟪ u ⟫ 2
  Ap' = pairForm' ∧̇ singleForm' ∧̇ zeroForm' ∧̇ domForm' ∧̇ limitForm'

  Cl' : Formula ⟪ u ⟫ 2
  Cl' = ⊤̇

  σ' : Formula ⟪ u ⟫ 1
  σ' = ∃̇∈ (con K) (Ap' ∧̇ (Cl' ∧̇ Rg'))

  levelΣ₁ : Σ₁ σ'
  levelΣ₁ = σ-Δ₀ (δ-∃∈ (δ-∧ ApΔ₀ (δ-∧ δ-⊤ RgΔ₀)))
    where
    ApΔ₀ : Δ₀ Ap'
    ApΔ₀ = δ-∧ pairFormΔ₀
             (δ-∧ singleFormΔ₀ (δ-∧ zeroFormΔ₀ (δ-∧ domFormΔ₀ limitFormΔ₀)))
    RgΔ₀ : Δ₀ Rg'
    RgΔ₀ = rangeFormΔ₀
