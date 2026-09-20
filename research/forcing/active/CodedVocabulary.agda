{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 Track E: the object-language vocabulary of a coded forcing notion.
--
-- Everything here is a triple in the K0 shape: a variable-indexed
-- Formula S n, a Δ₀ witness obtained by checkΔ₀ from the formula's own
-- shape, and a reading theorem identifying the evaluator's value with a
-- host predicate written in _∈ˢ_, _≈ˢ_ and the hProp algebra's ⋀ and ⋁.
-- Every reading below is refl, which is the point of writing the host
-- predicate as the literal unfolding.
--
-- Three rules are observed throughout.
--
-- 1. No slot is ever a con. Each argument position is a Fin n, so a
--    formula of this file can be placed inside a larger one; the tree has
--    no substitution (grep -rn "substFo|substTm|_[_]" src/FOL/ returns
--    nothing), so a con-parameterized formula could not be. Section
--    "Constant instantiation" at the end supplies the missing operation
--    and its soundness, which is what turns these into the Formula S 1
--    arguments that Separation takes.
--
-- 2. No unbounded quantifier anywhere. K1's Subsetφ and PairφK both lead
--    with ∀̇ (CardinalBridge.agda:69-70, :116-117) and bounded (∀̇ φ) is
--    false (FOL/LevyHierarchy.lagda.md:110), so nothing built from them
--    can carry a Δ₀ witness. This file rebuilds the pair vocabulary on
--    the model of src/L/Coding/PairFormulas.lagda.md:239-263, retargeted
--    from Formula (V ℓ) n to Formula S n.
--
-- 3. Negation is spelled _ ⇒ ⊥ on the host side and ¬̇ (which is
--    φ ⇒̇ ⊥̇) on the object side, never the algebra's ¬_, so that the two
--    agree by refl. Nothing here uses ¬_, so ¬-as-⇒⊥ is not needed.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module CodedVocabulary {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var
        ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; checkΔ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import OrdinaryProfile 𝒮 using ( iff )
open import CardinalBridge 𝒮 using ( _↔̇_ )

open import Cubical.Data.Unit using ( tt )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_; ⟦_⟧ )

-- ---------------------------------------------------------------------
-- Singletons and unordered pairs
-- ---------------------------------------------------------------------

-- "the set at w is the singleton of the set at u". The bounded quantifier
-- binds a fresh variable at position zero, so the outer slot u is named
-- suc u underneath it.

sglAtˢ : ∀ {n} → Fin n → Fin n → Formula S n
sglAtˢ w u = (var u ∈̇ var w) ∧̇ (∀̇∈ (var w) (var zero ≐ var (suc u)))

isSglΔ : S → S → Ω
isSglΔ w u = (u ∈ˢ w) ⊓ (⋀ S (λ x → (x ∈ˢ w) ⇒ (x ≈ˢ u)))

Δ₀-sglAtˢ : ∀ {n} (w u : Fin n) → Δ₀ (sglAtˢ w u)
Δ₀-sglAtˢ w u = checkΔ₀ (sglAtˢ w u) tt

sglAtˢ-reading : ∀ {n} (w u : Fin n) (γ : S ^ n)
               → (γ ⊨ sglAtˢ w u) ≡ isSglΔ (lookup w γ) (lookup u γ)
sglAtˢ-reading w u γ = refl

-- "the set at w is the unordered pair of the sets at u and v".

pairAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
pairAtˢ w u v =
    (var u ∈̇ var w)
  ∧̇ ((var v ∈̇ var w)
  ∧̇ (∀̇∈ (var w) ((var zero ≐ var (suc u)) ∨̇ (var zero ≐ var (suc v)))))

isPairΔ : S → S → S → Ω
isPairΔ w u v =
    (u ∈ˢ w)
  ⊓ ((v ∈ˢ w)
  ⊓ (⋀ S (λ x → (x ∈ˢ w) ⇒ ((x ≈ˢ u) ⊔ (x ≈ˢ v)))))

Δ₀-pairAtˢ : ∀ {n} (w u v : Fin n) → Δ₀ (pairAtˢ w u v)
Δ₀-pairAtˢ w u v = checkΔ₀ (pairAtˢ w u v) tt

pairAtˢ-reading : ∀ {n} (w u v : Fin n) (γ : S ^ n)
                → (γ ⊨ pairAtˢ w u v)
                  ≡ isPairΔ (lookup w γ) (lookup u γ) (lookup v γ)
pairAtˢ-reading w u v γ = refl

-- ---------------------------------------------------------------------
-- The Kuratowski pair
-- ---------------------------------------------------------------------

-- "the set at q is the Kuratowski pair of the sets at u and v": some
-- member of q is the singleton of u, some member is the unordered pair,
-- and every member is one of the two. All three clauses are bounded by q,
-- which is what makes the reader Δ₀ and is exactly why K1's PairφK, whose
-- outermost connective is ∀̇, cannot serve here.

prAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
prAtˢ q u v =
    (∃̇∈ (var q) (sglAtˢ zero (suc u)))
  ∧̇ ((∃̇∈ (var q) (pairAtˢ zero (suc u) (suc v)))
  ∧̇ (∀̇∈ (var q) (sglAtˢ zero (suc u) ∨̇ pairAtˢ zero (suc u) (suc v))))

isKPairΔ : S → S → S → Ω
isKPairΔ q u v =
    (⋁ S (λ w → (w ∈ˢ q) ⊓ isSglΔ w u))
  ⊓ ((⋁ S (λ w → (w ∈ˢ q) ⊓ isPairΔ w u v))
  ⊓ (⋀ S (λ w → (w ∈ˢ q) ⇒ (isSglΔ w u ⊔ isPairΔ w u v))))

Δ₀-prAtˢ : ∀ {n} (q u v : Fin n) → Δ₀ (prAtˢ q u v)
Δ₀-prAtˢ q u v = checkΔ₀ (prAtˢ q u v) tt

prAtˢ-reading : ∀ {n} (q u v : Fin n) (γ : S ^ n)
              → (γ ⊨ prAtˢ q u v)
                ≡ isKPairΔ (lookup q γ) (lookup u γ) (lookup v γ)
prAtˢ-reading q u v γ = refl

-- ---------------------------------------------------------------------
-- The order of a coded forcing notion
-- ---------------------------------------------------------------------

-- A coded notion is presented by two sets: a carrier c and an order graph
-- o whose members are Kuratowski pairs of carrier elements. "p refines q"
-- is then membership of the pair ⟨p, q⟩ in o, and the quantifier that
-- looks for that pair is bounded by o.

orderAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
orderAtˢ o p q = ∃̇∈ (var o) (prAtˢ zero (suc p) (suc q))

refinesΔ : S → S → S → Ω
refinesΔ o p q = ⋁ S (λ z → (z ∈ˢ o) ⊓ isKPairΔ z p q)

Δ₀-orderAtˢ : ∀ {n} (o p q : Fin n) → Δ₀ (orderAtˢ o p q)
Δ₀-orderAtˢ o p q = checkΔ₀ (orderAtˢ o p q) tt

orderAtˢ-reading : ∀ {n} (o p q : Fin n) (γ : S ^ n)
                 → (γ ⊨ orderAtˢ o p q)
                   ≡ refinesΔ (lookup o γ) (lookup p γ) (lookup q γ)
orderAtˢ-reading o p q γ = refl

-- ---------------------------------------------------------------------
-- Compatibility
-- ---------------------------------------------------------------------

-- Two conditions are compatible when a third refines both. The witness
-- is sought inside the carrier, so the quantifier is bounded and the
-- reading carries the truncation of ⋁ rather than a bare Σ.

compatAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
compatAtˢ c o p q =
  ∃̇∈ (var c) (orderAtˢ (suc o) zero (suc p) ∧̇ orderAtˢ (suc o) zero (suc q))

compatibleΔ : S → S → S → S → Ω
compatibleΔ c o p q =
  ⋁ S (λ r → (r ∈ˢ c) ⊓ (refinesΔ o r p ⊓ refinesΔ o r q))

Δ₀-compatAtˢ : ∀ {n} (c o p q : Fin n) → Δ₀ (compatAtˢ c o p q)
Δ₀-compatAtˢ c o p q = checkΔ₀ (compatAtˢ c o p q) tt

compatAtˢ-reading : ∀ {n} (c o p q : Fin n) (γ : S ^ n)
                  → (γ ⊨ compatAtˢ c o p q)
                    ≡ compatibleΔ (lookup c γ) (lookup o γ)
                                  (lookup p γ) (lookup q γ)
compatAtˢ-reading c o p q γ = refl

-- A reading theorem proved by refl cannot by itself catch a formula that
-- is wrong in the same way its host predicate is wrong. Each check below
-- is a fact about the host predicate alone, free of hypotheses, that
-- fails if the argument order or a de Bruijn index is off.

compatibleΔ-sym : (c o p q : S)
                → compatibleΔ c o p q ≡ compatibleΔ c o q p
compatibleΔ-sym c o p q = ⇔toPath
  (PT.map (λ { (r , hc , h₁ , h₂) → r , (hc , (h₂ , h₁)) }))
  (PT.map (λ { (r , hc , h₁ , h₂) → r , (hc , (h₂ , h₁)) }))

-- ---------------------------------------------------------------------
-- Inclusion and inhabitedness
-- ---------------------------------------------------------------------

-- Inclusion with the universal quantifier bounded by the smaller set.
-- K1's Subsetφ leads with ∀̇ (CardinalBridge.agda:69-70) and is Δ₀ for
-- no witness at all; this is the replacement.

subsetAtˢ : ∀ {n} → Fin n → Fin n → Formula S n
subsetAtˢ a b = ∀̇∈ (var a) (var zero ∈̇ var (suc b))

subsetΔ : S → S → Ω
subsetΔ a b = ⋀ S (λ x → (x ∈ˢ a) ⇒ (x ∈ˢ b))

Δ₀-subsetAtˢ : ∀ {n} (a b : Fin n) → Δ₀ (subsetAtˢ a b)
Δ₀-subsetAtˢ a b = checkΔ₀ (subsetAtˢ a b) tt

subsetAtˢ-reading : ∀ {n} (a b : Fin n) (γ : S ^ n)
                  → (γ ⊨ subsetAtˢ a b) ≡ subsetΔ (lookup a γ) (lookup b γ)
subsetAtˢ-reading a b γ = refl

-- Positivity is inhabitedness, the primitive of the architecture's
-- section 1.1, not the classical "nonzero". The body is ⊤̇, which the
-- syntax spells ⊥̇ ⇒̇ ⊥̇, so the reading carries a trailing ⊥ ⇒ ⊥ that
-- positiveΔ-simp removes.

positiveAtˢ : ∀ {n} → Fin n → Formula S n
positiveAtˢ u = ∃̇∈ (var u) ⊤̇

positiveΔ : S → Ω
positiveΔ u = ⋁ S (λ q → (q ∈ˢ u) ⊓ (⊥ ⇒ ⊥))

Δ₀-positiveAtˢ : ∀ {n} (u : Fin n) → Δ₀ (positiveAtˢ u)
Δ₀-positiveAtˢ u = checkΔ₀ (positiveAtˢ u) tt

positiveAtˢ-reading : ∀ {n} (u : Fin n) (γ : S ^ n)
                    → (γ ⊨ positiveAtˢ u) ≡ positiveΔ (lookup u γ)
positiveAtˢ-reading u γ = refl

positiveΔ-simp : (u : S) → positiveΔ u ≡ ⋁ S (λ q → q ∈ˢ u)
positiveΔ-simp u = ⇔toPath
  (PT.map (λ { (q , h , _) → q , h }))
  (PT.map (λ { (q , h) → q , (h , (λ z → z)) }))

-- ---------------------------------------------------------------------
-- The pseudocomplement and the regularization
-- ---------------------------------------------------------------------

-- "the condition at q lies in the pseudocomplement of the coded subset at
-- d": no refinement of q inside the carrier lies in d. The architecture's
-- host operator is (U ⋆) q = ⋀ Cond (λ r → (r ≼ q) ⇒ (U r ⇒ ⊥)); the
-- object version replaces the quantifier over Cond by one bounded by the
-- carrier code.

pseudoAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
pseudoAtˢ c o d q =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc q) ⇒̇ ¬̇ (var zero ∈̇ var (suc d)))

pseudoΔ : S → S → S → S → Ω
pseudoΔ c o d q =
  ⋀ S (λ r → (r ∈ˢ c) ⇒ (refinesΔ o r q ⇒ ((r ∈ˢ d) ⇒ ⊥)))

Δ₀-pseudoAtˢ : ∀ {n} (c o d q : Fin n) → Δ₀ (pseudoAtˢ c o d q)
Δ₀-pseudoAtˢ c o d q = checkΔ₀ (pseudoAtˢ c o d q) tt

pseudoAtˢ-reading : ∀ {n} (c o d q : Fin n) (γ : S ^ n)
                  → (γ ⊨ pseudoAtˢ c o d q)
                    ≡ pseudoΔ (lookup c γ) (lookup o γ)
                              (lookup d γ) (lookup q γ)
pseudoAtˢ-reading c o d q γ = refl

-- The regularization is the pseudocomplement applied twice. Written out,
-- rather than as an application of pseudoAtˢ to a code for d ⋆, because
-- d ⋆ is not a code until Separation has produced one, and the formula
-- has to exist before that Separation can be taken.

regularizeAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
regularizeAtˢ c o d q =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc q)
       ⇒̇ ¬̇ (pseudoAtˢ (suc c) (suc o) (suc d) zero))

regularizeΔ : S → S → S → S → Ω
regularizeΔ c o d q =
  ⋀ S (λ r → (r ∈ˢ c) ⇒ (refinesΔ o r q ⇒ (pseudoΔ c o d r ⇒ ⊥)))

Δ₀-regularizeAtˢ : ∀ {n} (c o d q : Fin n) → Δ₀ (regularizeAtˢ c o d q)
Δ₀-regularizeAtˢ c o d q = checkΔ₀ (regularizeAtˢ c o d q) tt

regularizeAtˢ-reading : ∀ {n} (c o d q : Fin n) (γ : S ^ n)
                      → (γ ⊨ regularizeAtˢ c o d q)
                        ≡ regularizeΔ (lookup c γ) (lookup o γ)
                                      (lookup d γ) (lookup q γ)
regularizeAtˢ-reading c o d q γ = refl

-- ---------------------------------------------------------------------
-- Regularity
-- ---------------------------------------------------------------------

-- "the coded subset at u is a regular open set": it agrees with its own
-- regularization at every condition of the carrier. This is the regular
-- element definition U ≡ U ⋆ ⋆, which is the one that is Boolean
-- constructively; Bell's dense-below formula is a LEM-dependent theorem
-- about it and is not the definition here.

regularAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
regularAtˢ c o u =
  ∀̇∈ (var c)
     ((var zero ∈̇ var (suc u))
       ↔̇ regularizeAtˢ (suc c) (suc o) (suc u) zero)

isRegularΔ : S → S → S → Ω
isRegularΔ c o u =
  ⋀ S (λ q → (q ∈ˢ c) ⇒ iff (q ∈ˢ u) (regularizeΔ c o u q))

Δ₀-regularAtˢ : ∀ {n} (c o u : Fin n) → Δ₀ (regularAtˢ c o u)
Δ₀-regularAtˢ c o u = checkΔ₀ (regularAtˢ c o u) tt

regularAtˢ-reading : ∀ {n} (c o u : Fin n) (γ : S ^ n)
                   → (γ ⊨ regularAtˢ c o u)
                     ≡ isRegularΔ (lookup c γ) (lookup o γ) (lookup u γ)
regularAtˢ-reading c o u γ = refl

-- ---------------------------------------------------------------------
-- The regularized cone
-- ---------------------------------------------------------------------

-- The completion map sends a condition p to the regularization of its
-- cone, never to the cone itself. The cone ↓ᶜ p has no code either, so
-- both stars are again written out: first the pseudocomplement of the
-- cone, then its pseudocomplement.

coneStarAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
coneStarAtˢ c o p r =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc r) ⇒̇ ¬̇ (orderAtˢ (suc o) zero (suc p)))

coneStarΔ : S → S → S → S → Ω
coneStarΔ c o p r =
  ⋀ S (λ s → (s ∈ˢ c) ⇒ (refinesΔ o s r ⇒ (refinesΔ o s p ⇒ ⊥)))

Δ₀-coneStarAtˢ : ∀ {n} (c o p r : Fin n) → Δ₀ (coneStarAtˢ c o p r)
Δ₀-coneStarAtˢ c o p r = checkΔ₀ (coneStarAtˢ c o p r) tt

coneStarAtˢ-reading : ∀ {n} (c o p r : Fin n) (γ : S ^ n)
                    → (γ ⊨ coneStarAtˢ c o p r)
                      ≡ coneStarΔ (lookup c γ) (lookup o γ)
                                  (lookup p γ) (lookup r γ)
coneStarAtˢ-reading c o p r γ = refl

-- What the pseudocomplement of a cone says, in the vocabulary the
-- completion consumes: r has no compatibility witness with p. The two
-- sides are not definitionally equal, because one is a bounded universal
-- and the other the negation of a bounded existential, and they agree
-- constructively.

coneStarΔ-as-incompatible :
  (c o p r : S) → coneStarΔ c o p r ≡ (compatibleΔ c o r p ⇒ ⊥)
coneStarΔ-as-incompatible c o p r = ⇔toPath
  (λ h k → PT.rec isProp⊥* (λ { (s , hc , hr , hp) → h s hc hr hp }) k)
  (λ g s hc hr hp → g ∣ s , (hc , (hr , hp)) ∣₁)

-- "the condition at q lies in the regularized cone of the condition at
-- p". Under LEM this is Bell's displayed formula, every refinement of q
-- being compatible with p; constructively it is the double negation of
-- that, and the LEM step belongs to the host module, not here.

coneAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
coneAtˢ c o p q =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc q)
       ⇒̇ ¬̇ (coneStarAtˢ (suc c) (suc o) (suc p) zero))

coneΔ : S → S → S → S → Ω
coneΔ c o p q =
  ⋀ S (λ r → (r ∈ˢ c) ⇒ (refinesΔ o r q ⇒ (coneStarΔ c o p r ⇒ ⊥)))

Δ₀-coneAtˢ : ∀ {n} (c o p q : Fin n) → Δ₀ (coneAtˢ c o p q)
Δ₀-coneAtˢ c o p q = checkΔ₀ (coneAtˢ c o p q) tt

coneAtˢ-reading : ∀ {n} (c o p q : Fin n) (γ : S ^ n)
                → (γ ⊨ coneAtˢ c o p q)
                  ≡ coneΔ (lookup c γ) (lookup o γ)
                          (lookup p γ) (lookup q γ)
coneAtˢ-reading c o p q γ = refl

-- ---------------------------------------------------------------------
-- Dense and predense coded subsets
-- ---------------------------------------------------------------------

-- Density: every condition of the carrier has a refinement inside the
-- coded subset. The inner quantifier is bounded by the subset code, so
-- the whole is Δ₀ and Separation can read it.

denseAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
denseAtˢ c o d =
  ∀̇∈ (var c) (∃̇∈ (var (suc d)) (orderAtˢ (suc (suc o)) zero (suc zero)))

denseΔ : S → S → S → Ω
denseΔ c o d =
  ⋀ S (λ q → (q ∈ˢ c) ⇒ (⋁ S (λ p → (p ∈ˢ d) ⊓ refinesΔ o p q)))

Δ₀-denseAtˢ : ∀ {n} (c o d : Fin n) → Δ₀ (denseAtˢ c o d)
Δ₀-denseAtˢ c o d = checkΔ₀ (denseAtˢ c o d) tt

denseAtˢ-reading : ∀ {n} (c o d : Fin n) (γ : S ^ n)
                 → (γ ⊨ denseAtˢ c o d)
                   ≡ denseΔ (lookup c γ) (lookup o γ) (lookup d γ)
denseAtˢ-reading c o d γ = refl

denseΔ-mono : (c o d e : S) → ⟨ subsetΔ d e ⟩
            → ⟨ denseΔ c o d ⟩ → ⟨ denseΔ c o e ⟩
denseΔ-mono c o d e sub h q hq =
  PT.map (λ { (p , hp , hr) → p , (sub p hp , hr) }) (h q hq)

-- Predensity weakens refinement to compatibility. It is the form K7's
-- chain condition is stated through, so it ships as its own formula
-- rather than as a corollary of density.

predenseAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
predenseAtˢ c o d =
  ∀̇∈ (var c)
     (∃̇∈ (var (suc d))
         (compatAtˢ (suc (suc c)) (suc (suc o)) zero (suc zero)))

predenseΔ : S → S → S → Ω
predenseΔ c o d =
  ⋀ S (λ q → (q ∈ˢ c) ⇒ (⋁ S (λ p → (p ∈ˢ d) ⊓ compatibleΔ c o p q)))

Δ₀-predenseAtˢ : ∀ {n} (c o d : Fin n) → Δ₀ (predenseAtˢ c o d)
Δ₀-predenseAtˢ c o d = checkΔ₀ (predenseAtˢ c o d) tt

predenseAtˢ-reading : ∀ {n} (c o d : Fin n) (γ : S ^ n)
                    → (γ ⊨ predenseAtˢ c o d)
                      ≡ predenseΔ (lookup c γ) (lookup o γ) (lookup d γ)
predenseAtˢ-reading c o d γ = refl

predenseΔ-mono : (c o d e : S) → ⟨ subsetΔ d e ⟩
               → ⟨ predenseΔ c o d ⟩ → ⟨ predenseΔ c o e ⟩
predenseΔ-mono c o d e sub h q hq =
  PT.map (λ { (p , hp , hc) → p , (sub p hp , hc) }) (h q hq)

-- ---------------------------------------------------------------------
-- Constant instantiation
-- ---------------------------------------------------------------------

-- Every formula above is variable-indexed, which is what lets it sit
-- inside a larger formula. Separation, however, takes a Formula S 1
-- (OrdinaryProfile.agda:88-91), and the parameters of the construction
-- are sets, not variables. The tree has renaming, which sends variables
-- to variables (FOL/Manipulation/Renaming.lagda.md:61), and nothing that
-- sends a variable to a term. The operation below is that missing map,
-- built as the exact analogue of renameFo with Fin n → Term S m in place
-- of Fin n → Fin m, together with the soundness theorem in the shape of
-- Sat.⊨-rename and the transport of Δ₀ witnesses along it.

wkTm : ∀ {n} → Term S n → Term S (suc n)
wkTm (con a) = con a
wkTm (var i) = var (suc i)

liftι : ∀ {n m} → (Fin n → Term S m) → Fin (suc n) → Term S (suc m)
liftι σ zero    = var zero
liftι σ (suc i) = wkTm (σ i)

instTm : ∀ {n m} → (Fin n → Term S m) → Term S n → Term S m
instTm σ (con a) = con a
instTm σ (var i) = σ i

instFo : ∀ {n m} → (Fin n → Term S m) → Formula S n → Formula S m
instFo σ (t ∈̇ u)  = instTm σ t ∈̇ instTm σ u
instFo σ (t ≐ u)  = instTm σ t ≐ instTm σ u
instFo σ (φ ∧̇ ψ)  = instFo σ φ ∧̇ instFo σ ψ
instFo σ (φ ∨̇ ψ)  = instFo σ φ ∨̇ instFo σ ψ
instFo σ (φ ⇒̇ ψ)  = instFo σ φ ⇒̇ instFo σ ψ
instFo σ ⊥̇        = ⊥̇
instFo σ (∃̇ φ)    = ∃̇ instFo (liftι σ) φ
instFo σ (∀̇ φ)    = ∀̇ instFo (liftι σ) φ
instFo σ (∀̇∈ t φ) = ∀̇∈ (instTm σ t) (instFo (liftι σ) φ)
instFo σ (∃̇∈ t φ) = ∃̇∈ (instTm σ t) (instFo (liftι σ) φ)

-- Fits σ γ δ says that reading the substituted variables in γ gives back
-- the environment δ the original formula was to be read in.

Fits : ∀ {n m} → (Fin n → Term S m) → S ^ m → S ^ n → Type ℓ
Fits σ γ δ = ∀ i → ⟦ σ i ⟧ γ ≡ lookup i δ

wkTm-val : ∀ {n} (t : Term S n) (x : S) (γ : S ^ n)
         → ⟦ wkTm t ⟧ (x ∷ γ) ≡ ⟦ t ⟧ γ
wkTm-val (con a) x γ = refl
wkTm-val (var i) x γ = refl

fits∷ : ∀ {n m} {σ : Fin n → Term S m} {γ : S ^ m} {δ : S ^ n} (x : S)
      → Fits σ γ δ → Fits (liftι σ) (x ∷ γ) (x ∷ δ)
fits∷ x fi zero = refl
fits∷ {σ = σ} {γ = γ} x fi (suc i) = wkTm-val (σ i) x γ ∙ fi i

⟦⟧-inst : ∀ {n m} (σ : Fin n → Term S m) (t : Term S n)
          (γ : S ^ m) (δ : S ^ n) → Fits σ γ δ
        → ⟦ instTm σ t ⟧ γ ≡ ⟦ t ⟧ δ
⟦⟧-inst σ (con a) γ δ fi = refl
⟦⟧-inst σ (var i) γ δ fi = fi i

⊨-inst : ∀ {n m} (σ : Fin n → Term S m) (φ : Formula S n)
         (γ : S ^ m) (δ : S ^ n) → Fits σ γ δ
       → (γ ⊨ instFo σ φ) ≡ (δ ⊨ φ)
⊨-inst σ (t ∈̇ u)  γ δ fi =
  cong₂ _∈ˢ_ (⟦⟧-inst σ t γ δ fi) (⟦⟧-inst σ u γ δ fi)
⊨-inst σ (t ≐ u)  γ δ fi =
  cong₂ _≈ˢ_ (⟦⟧-inst σ t γ δ fi) (⟦⟧-inst σ u γ δ fi)
⊨-inst σ (φ ∧̇ ψ)  γ δ fi =
  cong₂ _⊓_ (⊨-inst σ φ γ δ fi) (⊨-inst σ ψ γ δ fi)
⊨-inst σ (φ ∨̇ ψ)  γ δ fi =
  cong₂ _⊔_ (⊨-inst σ φ γ δ fi) (⊨-inst σ ψ γ δ fi)
⊨-inst σ (φ ⇒̇ ψ)  γ δ fi =
  cong₂ _⇒_ (⊨-inst σ φ γ δ fi) (⊨-inst σ ψ γ δ fi)
⊨-inst σ ⊥̇        γ δ fi = refl
⊨-inst σ (∃̇ φ)    γ δ fi = cong (⋁ S) (funExt (λ x →
  ⊨-inst (liftι σ) φ (x ∷ γ) (x ∷ δ) (fits∷ x fi)))
⊨-inst σ (∀̇ φ)    γ δ fi = cong (⋀ S) (funExt (λ x →
  ⊨-inst (liftι σ) φ (x ∷ γ) (x ∷ δ) (fits∷ x fi)))
⊨-inst σ (∀̇∈ t φ) γ δ fi = cong (⋀ S) (funExt (λ x →
  cong₂ _⇒_ (cong (x ∈ˢ_) (⟦⟧-inst σ t γ δ fi))
            (⊨-inst (liftι σ) φ (x ∷ γ) (x ∷ δ) (fits∷ x fi))))
⊨-inst σ (∃̇∈ t φ) γ δ fi = cong (⋁ S) (funExt (λ x →
  cong₂ _⊓_ (cong (x ∈ˢ_) (⟦⟧-inst σ t γ δ fi))
            (⊨-inst (liftι σ) φ (x ∷ γ) (x ∷ δ) (fits∷ x fi))))

Δ₀-inst : ∀ {n m} (σ : Fin n → Term S m) {φ : Formula S n}
        → Δ₀ φ → Δ₀ (instFo σ φ)
Δ₀-inst σ δ-∈          = δ-∈
Δ₀-inst σ δ-≐          = δ-≐
Δ₀-inst σ (δ-∧ d e)    = δ-∧ (Δ₀-inst σ d) (Δ₀-inst σ e)
Δ₀-inst σ (δ-∨ d e)    = δ-∨ (Δ₀-inst σ d) (Δ₀-inst σ e)
Δ₀-inst σ (δ-⇒ d e)    = δ-⇒ (Δ₀-inst σ d) (Δ₀-inst σ e)
Δ₀-inst σ δ-⊥          = δ-⊥
Δ₀-inst σ (δ-∀∈ d)     = δ-∀∈ (Δ₀-inst (liftι σ) d)
Δ₀-inst σ (δ-∃∈ d)     = δ-∃∈ (Δ₀-inst (liftι σ) d)

-- The shape Separation wants: slot zero stays a variable and every other
-- slot becomes the constant recorded in the parameter vector.

atCon : ∀ {k} → Vec S k → Fin (suc k) → Term S 1
atCon ps zero    = var zero
atCon ps (suc i) = con (lookup i ps)

atCon-fits : ∀ {k} (ps : Vec S k) (x : S) → Fits (atCon ps) (x ∷ []) (x ∷ ps)
atCon-fits ps x zero    = refl
atCon-fits ps x (suc i) = refl

sepAt : ∀ {k} → Formula S (suc k) → Vec S k → Formula S 1
sepAt φ ps = instFo (atCon ps) φ

sepAt-reading : ∀ {k} (φ : Formula S (suc k)) (ps : Vec S k) (x : S)
              → ((x ∷ []) ⊨ sepAt φ ps) ≡ ((x ∷ ps) ⊨ φ)
sepAt-reading φ ps x =
  ⊨-inst (atCon ps) φ (x ∷ []) (x ∷ ps) (atCon-fits ps x)

Δ₀-sepAt : ∀ {k} {φ : Formula S (suc k)} → Δ₀ φ → (ps : Vec S k)
         → Δ₀ (sepAt φ ps)
Δ₀-sepAt d ps = Δ₀-inst (atCon ps) d
