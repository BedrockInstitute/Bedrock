{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 Track F: the model-internal regular-open completion.
--
-- Every object below is a set of the ground model, produced by ONE instance
-- of the ground's own PowerSet or Separation and read back only through its
-- membership specification. Nothing is built in the ambient universe: the
-- separation functions of V.Smallness return a separated set as data with no
-- formula and no truncation and would silently build the object outside the
-- model, so this file imports neither V. nor L. anything.
--
-- The hypotheses are the parameter list of module Core, and that list is the
-- ledger: the structure, ordinary Extensionality, PowerSet, Separation, the
-- path realization of the structure equality, a Presentation and its two
-- order laws. No Pairing, no Union, no Infinity, no Foundation, no
-- Collection, no Choice, no resizing. LEM appears nowhere in Core; in module
-- Classical it is an explicit first argument of each lemma that needs it,
-- never a module parameter.
--
-- Notation rules of K2 section 1.0: the cubical powerset membership never
-- appears, and every negation is spelled _ ⇒ ⊥ with the algebra's own bottom.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import GroundDescription
import CodedVocabulary
import ForcingNotion as FN
import HostRegularOpen as HRO

module CodedCompletion {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Base.Classical using ( LEM )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt; tt* )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module OP = OrdinaryProfile 𝒮
module CV = CodedVocabulary 𝒮

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

open OP using ( iff; Extensionality; PowerSet; Separation )
open CV
  using ( isKPairΔ; refinesΔ; compatibleΔ; pseudoΔ; regularizeΔ; isRegularΔ
        ; coneStarΔ; coneΔ; denseΔ; predenseΔ
        ; orderAtˢ; coneAtˢ; pseudoAtˢ; regularAtˢ
        ; sepAt; sepAt-reading; Δ₀-sepAt )

-- ---------------------------------------------------------------------
-- Object-language vocabulary the construction table needs and Track E
-- does not supply
-- ---------------------------------------------------------------------

-- Track E delivers the pseudocomplement, the regularization and the
-- regularized cone of a single code. The join of two codes and the
-- supremum of a coded family regularize a UNION, and a union has no code
-- until Pairing and Union have produced one. Writing the union out inside
-- the double star is exactly what keeps Union out of the core ledger, so
-- these four formulas are written here on Track E's model: every slot is a
-- variable, every quantifier is bounded, every reading is refl.

-- "the set at s belongs to some member of the coded family at a".

memUnionAtˢ : ∀ {n} → Fin n → Fin n → Formula S n
memUnionAtˢ a s = ∃̇∈ (var a) (var (suc s) ∈̇ var zero)

memUnionΔ : S → S → Ω
memUnionΔ a s = ⋁ S (λ w → (w ∈ˢ a) ⊓ (s ∈ˢ w))

Δ₀-memUnionAtˢ : ∀ {n} (a s : Fin n) → Δ₀ (memUnionAtˢ a s)
Δ₀-memUnionAtˢ a s = checkΔ₀ (memUnionAtˢ a s) tt

memUnionAtˢ-reading : ∀ {n} (a s : Fin n) (γ : S ^ n)
                    → (γ ⊨ memUnionAtˢ a s) ≡ memUnionΔ (lookup a γ) (lookup s γ)
memUnionAtˢ-reading a s γ = refl

-- "the set at q belongs to every member of the coded family at a". The
-- infimum of a coded family of regular opens is their intersection and
-- needs no regularization, so this is the only formula of the four that is
-- not a double star.

interAtˢ : ∀ {n} → Fin n → Fin n → Formula S n
interAtˢ a q = ∀̇∈ (var a) (var (suc q) ∈̇ var zero)

interΔ : S → S → Ω
interΔ a q = ⋀ S (λ w → (w ∈ˢ a) ⇒ (q ∈ˢ w))

Δ₀-interAtˢ : ∀ {n} (a q : Fin n) → Δ₀ (interAtˢ a q)
Δ₀-interAtˢ a q = checkΔ₀ (interAtˢ a q) tt

interAtˢ-reading : ∀ {n} (a q : Fin n) (γ : S ^ n)
                 → (γ ⊨ interAtˢ a q) ≡ interΔ (lookup a γ) (lookup q γ)
interAtˢ-reading a q γ = refl

-- The pseudocomplement of the union of the two codes at d and at e.

unionStarAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
unionStarAtˢ c o d e r =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc r)
       ⇒̇ ¬̇ ((var zero ∈̇ var (suc d)) ∨̇ (var zero ∈̇ var (suc e))))

unionStarΔ : S → S → S → S → S → Ω
unionStarΔ c o d e r =
  ⋀ S (λ s → (s ∈ˢ c) ⇒ (refinesΔ o s r ⇒ (((s ∈ˢ d) ⊔ (s ∈ˢ e)) ⇒ ⊥)))

Δ₀-unionStarAtˢ : ∀ {n} (c o d e r : Fin n) → Δ₀ (unionStarAtˢ c o d e r)
Δ₀-unionStarAtˢ c o d e r = checkΔ₀ (unionStarAtˢ c o d e r) tt

unionStarAtˢ-reading : ∀ {n} (c o d e r : Fin n) (γ : S ^ n)
                     → (γ ⊨ unionStarAtˢ c o d e r)
                       ≡ unionStarΔ (lookup c γ) (lookup o γ) (lookup d γ)
                                    (lookup e γ) (lookup r γ)
unionStarAtˢ-reading c o d e r γ = refl

-- The regularized union: the Boolean join of two coded regular opens.

joinAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
joinAtˢ c o d e q =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc q)
       ⇒̇ ¬̇ (unionStarAtˢ (suc c) (suc o) (suc d) (suc e) zero))

joinΔ : S → S → S → S → S → Ω
joinΔ c o d e q =
  ⋀ S (λ r → (r ∈ˢ c) ⇒ (refinesΔ o r q ⇒ (unionStarΔ c o d e r ⇒ ⊥)))

Δ₀-joinAtˢ : ∀ {n} (c o d e q : Fin n) → Δ₀ (joinAtˢ c o d e q)
Δ₀-joinAtˢ c o d e q = checkΔ₀ (joinAtˢ c o d e q) tt

joinAtˢ-reading : ∀ {n} (c o d e q : Fin n) (γ : S ^ n)
                → (γ ⊨ joinAtˢ c o d e q)
                  ≡ joinΔ (lookup c γ) (lookup o γ) (lookup d γ)
                          (lookup e γ) (lookup q γ)
joinAtˢ-reading c o d e q γ = refl

-- The same two steps for the union of a whole coded family.

supStarAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
supStarAtˢ c o a r =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc r) ⇒̇ ¬̇ (memUnionAtˢ (suc a) zero))

supStarΔ : S → S → S → S → Ω
supStarΔ c o a r =
  ⋀ S (λ s → (s ∈ˢ c) ⇒ (refinesΔ o s r ⇒ (memUnionΔ a s ⇒ ⊥)))

Δ₀-supStarAtˢ : ∀ {n} (c o a r : Fin n) → Δ₀ (supStarAtˢ c o a r)
Δ₀-supStarAtˢ c o a r = checkΔ₀ (supStarAtˢ c o a r) tt

supStarAtˢ-reading : ∀ {n} (c o a r : Fin n) (γ : S ^ n)
                   → (γ ⊨ supStarAtˢ c o a r)
                     ≡ supStarΔ (lookup c γ) (lookup o γ)
                                (lookup a γ) (lookup r γ)
supStarAtˢ-reading c o a r γ = refl

supAtˢ : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
supAtˢ c o a q =
  ∀̇∈ (var c)
     (orderAtˢ (suc o) zero (suc q)
       ⇒̇ ¬̇ (supStarAtˢ (suc c) (suc o) (suc a) zero))

supΔ : S → S → S → S → Ω
supΔ c o a q =
  ⋀ S (λ r → (r ∈ˢ c) ⇒ (refinesΔ o r q ⇒ (supStarΔ c o a r ⇒ ⊥)))

Δ₀-supAtˢ : ∀ {n} (c o a q : Fin n) → Δ₀ (supAtˢ c o a q)
Δ₀-supAtˢ c o a q = checkΔ₀ (supAtˢ c o a q) tt

supAtˢ-reading : ∀ {n} (c o a q : Fin n) (γ : S ^ n)
               → (γ ⊨ supAtˢ c o a q)
                 ≡ supΔ (lookup c γ) (lookup o γ) (lookup a γ) (lookup q γ)
supAtˢ-reading c o a q γ = refl

-- ---------------------------------------------------------------------
-- The coded forcing notion
-- ---------------------------------------------------------------------

-- A presentation is two sets of the model: a carrier and an order GRAPH
-- whose members are Kuratowski pairs of carrier elements. The graph is a
-- set and not only a formula because the chain-condition packages must
-- prove that the notion and its order are sets in the model; the formula
-- of Track E is needed in ADDITION, because Separation reads a formula and
-- not a graph.

record Presentation : Type ℓ where
  field
    carrier : S
    order   : S
    order-typed :
      ⟨ ⋀ S (λ z → (z ∈ˢ order) ⇒ ⋁ S (λ p → ⋁ S (λ q →
          (p ∈ˢ carrier) ⊓ ((q ∈ˢ carrier) ⊓ isKPairΔ z p q)))) ⟩
    inhabited : ⟨ ⋁ S (λ p → p ∈ˢ carrier) ⟩

module Coded (𝔓 : Presentation) where

  open Presentation 𝔓 public

  -- "p refines q", read off the graph. This is Track E's refinesΔ at the
  -- presentation's own order code, so every formula of Track E that
  -- mentions the order reads through it definitionally.

  _≼ᴵ_ : S → S → Ω
  p ≼ᴵ q = refinesΔ order p q

  infix 20 _≼ᴵ_

  Cond : Type ℓ
  Cond = Σ[ x ∈ S ] ⟨ x ∈ˢ carrier ⟩

  record ForcingLaws : Type ℓ where
    field
      ≼ᴵ-refl  : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ p ≼ᴵ p ⟩
      ≼ᴵ-trans : (r q p : S)
               → ⟨ r ∈ˢ carrier ⟩ → ⟨ q ∈ˢ carrier ⟩ → ⟨ p ∈ˢ carrier ⟩
               → ⟨ r ≼ᴵ q ⟩ → ⟨ q ≼ᴵ p ⟩ → ⟨ r ≼ᴵ p ⟩

  -- The adapter runs one way only, and it is total and free. There is no
  -- encode in the other direction: presenting a given host notion inside
  -- the model is a per-notion obligation, not a theorem.

  decode : ForcingLaws → FN.ForcingNotion {ℓ}
  decode laws = record
    { Cond     = Cond
    ; isSetC   = isSetΣSndProp isSetS (λ x → snd (x ∈ˢ carrier))
    ; _≼_      = λ p q → fst p ≼ᴵ fst q
    ; ≼-refl   = λ p → ForcingLaws.≼ᴵ-refl laws (fst p) (snd p)
    ; ≼-trans  = λ {p} {q} {r} h k →
                   ForcingLaws.≼ᴵ-trans laws (fst p) (fst q) (fst r)
                     (snd p) (snd q) (snd r) h k
    ; nonempty = PT.map (λ { (p , hp) → p , hp }) inhabited }

-- ---------------------------------------------------------------------
-- The model-internal completion
-- ---------------------------------------------------------------------

-- This parameter list IS the assumption ledger. Nothing named OrdinaryZF,
-- isZFModel, Infinity, Foundation, Collection, Choice or Resizing appears
-- in it, and LEM appears nowhere in this module.

module Core
  (ext   : Extensionality)
  (pow   : PowerSet)
  (sep   : Separation)
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (𝔓     : Presentation)
  (laws  : Coded.ForcingLaws 𝔓)
  where

  open Coded 𝔓
  module GD = GroundDescription 𝒮 ext paths
  open GD using ( ext-path; powerOf; powerOf-spec; separateOf; separateOf-spec )
  open OP.PathRealization paths using ( ≈ˢ-to-path )
  module FS = FN.Structure (decode laws)

  refl≼ : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ p ≼ᴵ p ⟩
  refl≼ = ForcingLaws.≼ᴵ-refl laws

  trans≼ : (r q p : S)
         → ⟨ r ∈ˢ carrier ⟩ → ⟨ q ∈ˢ carrier ⟩ → ⟨ p ∈ˢ carrier ⟩
         → ⟨ r ≼ᴵ q ⟩ → ⟨ q ≼ᴵ p ⟩ → ⟨ r ≼ᴵ p ⟩
  trans≼ = ForcingLaws.≼ᴵ-trans laws

  -- ---------------------------------------------------------------
  -- The pseudocomplement, as an operation on host predicates
  -- ---------------------------------------------------------------

  -- The whole construction is one operation applied at most twice, and
  -- Track E's four regularity formulas are that operation spelled out at
  -- the places where the intermediate set has no code yet. Naming it once
  -- on host predicates makes every one of those readings a definitional
  -- unfolding, which the four identities below record.

  Pred : Type (ℓ-suc ℓ)
  Pred = S → Ω

  mem : S → Pred
  mem u x = x ∈ˢ u

  starOf : Pred → Pred
  starOf W q = ⋀ S (λ r → (r ∈ˢ carrier) ⇒ ((r ≼ᴵ q) ⇒ (W r ⇒ ⊥)))

  cone : S → Pred
  cone p s = s ≼ᴵ p

  star-is-pseudo : (d : S) → starOf (mem d) ≡ pseudoΔ carrier order d
  star-is-pseudo d = refl

  star²-is-regularize : (d : S)
                      → starOf (starOf (mem d)) ≡ regularizeΔ carrier order d
  star²-is-regularize d = refl

  star-is-coneStar : (p : S) → starOf (cone p) ≡ coneStarΔ carrier order p
  star-is-coneStar p = refl

  star²-is-cone : (p : S) → starOf (starOf (cone p)) ≡ coneΔ carrier order p
  star²-is-cone p = refl

  star-is-unionStar : (d e : S)
    → starOf (λ s → (s ∈ˢ d) ⊔ (s ∈ˢ e)) ≡ unionStarΔ carrier order d e
  star-is-unionStar d e = refl

  star²-is-join : (d e : S)
    → starOf (unionStarΔ carrier order d e) ≡ joinΔ carrier order d e
  star²-is-join d e = refl

  star-is-supStar : (a : S) → starOf (memUnionΔ a) ≡ supStarΔ carrier order a
  star-is-supStar a = refl

  star²-is-sup : (a : S)
    → starOf (supStarΔ carrier order a) ≡ supΔ carrier order a
  star²-is-sup a = refl

  -- ---------------------------------------------------------------
  -- Inclusion, downward closure and regularity, all relative to the
  -- carrier
  -- ---------------------------------------------------------------

  _⊑_ : Pred → Pred → Type ℓ
  W ⊑ V = (x : S) → ⟨ x ∈ˢ carrier ⟩ → ⟨ W x ⟩ → ⟨ V x ⟩

  infix 4 _⊑_

  _≑_ : Pred → Pred → Type ℓ
  W ≑ V = (W ⊑ V) × (V ⊑ W)

  infix 4 _≑_

  ≑-sym : (W V : Pred) → W ≑ V → V ≑ W
  ≑-sym W V (f , g) = g , f

  ≑-trans : (W V U : Pred) → W ≑ V → V ≑ U → W ≑ U
  ≑-trans W V U (f , g) (h , k) =
    (λ x hx w → h x hx (f x hx w)) , (λ x hx u → g x hx (k x hx u))

  DownClosed : Pred → Type ℓ
  DownClosed W = (r s : S) → ⟨ r ∈ˢ carrier ⟩ → ⟨ s ∈ˢ carrier ⟩
               → ⟨ r ≼ᴵ s ⟩ → ⟨ W s ⟩ → ⟨ W r ⟩

  Regular : Pred → Type ℓ
  Regular W = (starOf (starOf W) ⊑ W) × (W ⊑ starOf (starOf W))

  star-anti : (W V : Pred) → W ⊑ V → starOf V ⊑ starOf W
  star-anti W V f q _ h r hr hrq hw = h r hr hrq (f r hr hw)

  star²-mono : (W V : Pred) → W ⊑ V → starOf (starOf W) ⊑ starOf (starOf V)
  star²-mono W V f = star-anti (starOf V) (starOf W) (star-anti W V f)

  star-down : (W : Pred) → DownClosed (starOf W)
  star-down W r s hr hs hrs h t ht htr hw =
    h t ht (trans≼ t r s ht hr hs htr hrs) hw

  star-expand : (W : Pred) → DownClosed W → W ⊑ starOf (starOf W)
  star-expand W dc s hs hws r hr hrs k =
    k r hr (refl≼ r hr) (dc r s hr hs hrs hws)

  star-Regular : (V : Pred) → DownClosed V → Regular (starOf V)
  star-Regular V dc =
      star-anti V (starOf (starOf V)) (star-expand V dc)
    , star-expand (starOf V) (star-down V)

  Regular→DownClosed : (W : Pred) → Regular W → DownClosed W
  Regular→DownClosed W (a , b) r s hr hs hrs hws =
    a r hr (star-down (starOf W) r s hr hs hrs (b s hs hws))

  star-cong : (W V : Pred) → W ≑ V → starOf W ≑ starOf V
  star-cong W V (f , g) = star-anti V W g , star-anti W V f

  star²-cong : (W V : Pred) → W ≑ V
             → starOf (starOf W) ≑ starOf (starOf V)
  star²-cong W V e = star-cong (starOf W) (starOf V) (star-cong W V e)

  Regular-≑ : (W V : Pred) → W ≑ V → Regular W → Regular V
  Regular-≑ W V e (a , b) =
      (λ x hx h → e .fst x hx (a x hx (star²-cong W V e .snd x hx h)))
    , (λ x hx h → star²-cong W V e .fst x hx (b x hx (e .snd x hx h)))

  DownClosed-≑ : (W V : Pred) → W ≑ V → DownClosed W → DownClosed V
  DownClosed-≑ W V e dc r s hr hs hrs hv =
    e .fst r hr (dc r s hr hs hrs (e .snd s hs hv))

  spec≑ : (u : S) (W : Pred) → ((x : S) → (x ∈ˢ u) ≡ W x) → mem u ≑ W
  spec≑ u W sp =
    (λ x _ h → subst ⟨_⟩ (sp x) h) , (λ x _ h → subst ⟨_⟩ (sym (sp x)) h)

  guard≑ : (W : Pred) → (λ x → (x ∈ˢ carrier) ⊓ W x) ≑ W
  guard≑ W = (λ x _ h → h .snd) , (λ x hx h → hx , h)

  -- ---------------------------------------------------------------
  -- The carrier of the completion
  -- ---------------------------------------------------------------

  -- One PowerSet instance, the only one in the core, and one Separation
  -- inside it. B is the set of coded regular opens of the presentation.

  𝒫ᶜ : S
  𝒫ᶜ = powerOf pow carrier

  𝒫ᶜ-mem : (x : S) → (x ∈ˢ 𝒫ᶜ) ≡ (x ⊆ˢ carrier)
  𝒫ᶜ-mem = powerOf-spec pow carrier

  regφ : Formula S 1
  regφ = sepAt (regularAtˢ (suc zero) (suc (suc zero)) zero)
               (carrier ∷ order ∷ [])

  B : S
  B = separateOf sep 𝒫ᶜ regφ

  B-mem : (x : S)
        → (x ∈ˢ B) ≡ ((x ⊆ˢ carrier) ⊓ isRegularΔ carrier order x)
  B-mem x =
    separateOf-spec sep 𝒫ᶜ regφ x
    ∙ cong₂ _⊓_ (𝒫ᶜ-mem x)
        (sepAt-reading (regularAtˢ (suc zero) (suc (suc zero)) zero)
                       (carrier ∷ order ∷ []) x)

  -- The internal regularity sentence and the host predicate say the same
  -- thing with the two conjuncts of the biconditional swapped.

  toRegular : (u : S) → ⟨ isRegularΔ carrier order u ⟩ → Regular (mem u)
  toRegular u h = (λ q hq k → h q hq .snd k) , (λ q hq k → h q hq .fst k)

  fromRegular : (u : S) → Regular (mem u) → ⟨ isRegularΔ carrier order u ⟩
  fromRegular u (a , b) q hq = (λ k → b q hq k) , (λ k → a q hq k)

  B-sub : (u : S) → ⟨ u ∈ˢ B ⟩ → ⟨ u ⊆ˢ carrier ⟩
  B-sub u h = subst ⟨_⟩ (B-mem u) h .fst

  B-regular : (u : S) → ⟨ u ∈ˢ B ⟩ → Regular (mem u)
  B-regular u h = toRegular u (subst ⟨_⟩ (B-mem u) h .snd)

  B-down : (u : S) → ⟨ u ∈ˢ B ⟩ → DownClosed (mem u)
  B-down u h = Regular→DownClosed (mem u) (B-regular u h)

  inB : (u : S) → ⟨ u ⊆ˢ carrier ⟩ → Regular (mem u) → ⟨ u ∈ˢ B ⟩
  inB u sub reg = subst ⟨_⟩ (sym (B-mem u)) (sub , fromRegular u reg)

  -- Every object of the table except the top and the bottom is a single
  -- Separation whose reading is a carrier guard meeting a host predicate.
  -- These two lemmas turn such a reading into membership in B.

  fromGuarded : (W : Pred) (u : S)
              → ((x : S) → (x ∈ˢ u) ≡ ((x ∈ˢ carrier) ⊓ W x))
              → Regular W → ⟨ u ∈ˢ B ⟩
  fromGuarded W u sp reg = inB u sub reg'
    where
      e : mem u ≑ W
      e = ≑-trans (mem u) (λ x → (x ∈ˢ carrier) ⊓ W x) W
            (spec≑ u (λ x → (x ∈ˢ carrier) ⊓ W x) sp) (guard≑ W)
      sub : ⟨ u ⊆ˢ carrier ⟩
      sub x h = subst ⟨_⟩ (sp x) h .fst
      reg' : Regular (mem u)
      reg' = Regular-≑ W (mem u) (≑-sym (mem u) W e) reg

  fromStar : (V : Pred) (u : S)
           → ((x : S) → (x ∈ˢ u) ≡ ((x ∈ˢ carrier) ⊓ starOf V x))
           → DownClosed V → ⟨ u ∈ˢ B ⟩
  fromStar V u sp dc = fromGuarded (starOf V) u sp (star-Regular V dc)

  -- ---------------------------------------------------------------
  -- The elements of the completion and their order
  -- ---------------------------------------------------------------

  El : Type ℓ
  El = Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩

  isSetEl : isSet El
  isSetEl = isSetΣSndProp isSetS (λ b → snd (b ∈ˢ B))

  El≡ : (u v : El) → ((x : S) → (x ∈ˢ fst u) ≡ (x ∈ˢ fst v)) → u ≡ v
  El≡ u v h = Σ≡Prop (λ b → snd (b ∈ˢ B)) (ext-path h)

  _≤ᴮ_ : El → El → Ω
  u ≤ᴮ v = fst u ⊆ˢ fst v

  infix 20 _≤ᴮ_

  ≤ᴮ-refl : (u : El) → ⟨ u ≤ᴮ u ⟩
  ≤ᴮ-refl u x h = h

  ≤ᴮ-trans : (u v w : El) → ⟨ u ≤ᴮ v ⟩ → ⟨ v ≤ᴮ w ⟩ → ⟨ u ≤ᴮ w ⟩
  ≤ᴮ-trans u v w f g x h = g x (f x h)

  ≤ᴮ-antisym : (u v : El) → ⟨ u ≤ᴮ v ⟩ → ⟨ v ≤ᴮ u ⟩ → u ≡ v
  ≤ᴮ-antisym u v f g = El≡ u v (λ x → ⇔toPath (f x) (g x))

  positiveᴮ : El → Ω
  positiveᴮ u = ⋁ S (λ q → q ∈ˢ fst u)

  -- ---------------------------------------------------------------
  -- Top and bottom
  -- ---------------------------------------------------------------

  -- The carrier is its own regularization, and the only input is
  -- reflexivity of the order.

  ⊤ᴮ : El
  ⊤ᴮ = carrier , inB carrier (λ x h → h) reg
    where
      dc : DownClosed (mem carrier)
      dc r s hr hs hrs hm = hr
      reg : Regular (mem carrier)
      reg = (λ q hq _ → hq) , star-expand (mem carrier) dc

  ⊤ᴮ-top : (u : El) → ⟨ u ≤ᴮ ⊤ᴮ ⟩
  ⊤ᴮ-top u = B-sub (fst u) (snd u)

  ⊥ᴮset : S
  ⊥ᴮset = separateOf sep carrier ⊥̇

  ⊥ᴮ-mem : (x : S) → (x ∈ˢ ⊥ᴮset) ≡ ((x ∈ˢ carrier) ⊓ ⊥)
  ⊥ᴮ-mem x = separateOf-spec sep carrier ⊥̇ x

  ⊥ᴮ-empty : (x : S) → ⟨ x ∈ˢ ⊥ᴮset ⟩ → ⟨ ⊥ ⟩
  ⊥ᴮ-empty x h = subst ⟨_⟩ (⊥ᴮ-mem x) h .snd

  ⊥ᴮ : El
  ⊥ᴮ = ⊥ᴮset , inB ⊥ᴮset sub reg
    where
      sub : ⟨ ⊥ᴮset ⊆ˢ carrier ⟩
      sub x h = subst ⟨_⟩ (⊥ᴮ-mem x) h .fst
      reg : Regular (mem ⊥ᴮset)
      reg = (λ q hq h → Empty.rec*
                          (h q hq (refl≼ q hq) (λ t ht htq hm → ⊥ᴮ-empty t hm)))
          , (λ q hq h → Empty.rec* (⊥ᴮ-empty q h))

  ⊥ᴮ-bot : (u : El) → ⟨ ⊥ᴮ ≤ᴮ u ⟩
  ⊥ᴮ-bot u x h = Empty.rec* (⊥ᴮ-empty x h)

  -- ---------------------------------------------------------------
  -- The completion map
  -- ---------------------------------------------------------------

  -- i sends a condition to the REGULARIZATION of its cone and never to the
  -- cone itself: the bare cone is a regular open only when the
  -- presentation is refined, and K2 must accept presentations that are
  -- not.

  coneφ : S → Formula S 1
  coneφ p =
    sepAt (coneAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero))) zero)
          (carrier ∷ order ∷ p ∷ [])

  iSet : S → S
  iSet p = separateOf sep carrier (coneφ p)

  iSet-mem : (p x : S)
           → (x ∈ˢ iSet p) ≡ ((x ∈ˢ carrier) ⊓ coneΔ carrier order p x)
  iSet-mem p x =
    separateOf-spec sep carrier (coneφ p) x
    ∙ cong (λ w → (x ∈ˢ carrier) ⊓ w)
        (sepAt-reading
           (coneAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero))) zero)
           (carrier ∷ order ∷ p ∷ []) x)

  cone-down : (p : S) → ⟨ p ∈ˢ carrier ⟩ → DownClosed (cone p)
  cone-down p hp r s hr hs hrs k = trans≼ r s p hr hs hp hrs k

  iSet-inB : (p : S) → ⟨ iSet p ∈ˢ B ⟩
  iSet-inB p =
    fromStar (coneStarΔ carrier order p) (iSet p) (iSet-mem p)
             (star-down (cone p))

  iᴮ : Cond → El
  iᴮ p = iSet (fst p) , iSet-inB (fst p)

  i-intro : (p : Cond) (r : S) → ⟨ r ∈ˢ carrier ⟩ → ⟨ r ≼ᴵ fst p ⟩
          → ⟨ r ∈ˢ fst (iᴮ p) ⟩
  i-intro p r hr hrp =
    subst ⟨_⟩ (sym (iSet-mem (fst p) r))
      (hr , star-expand (cone (fst p)) (cone-down (fst p) (snd p)) r hr hrp)

  i-self : (p : Cond) → ⟨ fst p ∈ˢ fst (iᴮ p) ⟩
  i-self p = i-intro p (fst p) (snd p) (refl≼ (fst p) (snd p))

  i-pos : (p : Cond) → ⟨ positiveᴮ (iᴮ p) ⟩
  i-pos p = ∣ fst p , i-self p ∣₁

  i-mono : (p q : Cond) → ⟨ fst q ≼ᴵ fst p ⟩ → ⟨ iᴮ q ≤ᴮ iᴮ p ⟩
  i-mono p q hqp x hx = subst ⟨_⟩ (sym (iSet-mem (fst p) x)) (xc , step)
    where
      w : ⟨ (x ∈ˢ carrier) ⊓ coneΔ carrier order (fst q) x ⟩
      w = subst ⟨_⟩ (iSet-mem (fst q) x) hx
      xc : ⟨ x ∈ˢ carrier ⟩
      xc = w .fst
      sub : cone (fst q) ⊑ cone (fst p)
      sub y hy k = trans≼ y (fst q) (fst p) hy (snd q) (snd p) k hqp
      step : ⟨ coneΔ carrier order (fst p) x ⟩
      step = star²-mono (cone (fst q)) (cone (fst p)) sub x xc (w .snd)

  -- Density of the image, and it is constructive: a regular open is
  -- downward closed, so any member of it already dominates the cone of
  -- itself, and the regularization is monotone.

  i-dense : (b : El) → ⟨ positiveᴮ b ⟩
          → ⟨ ⋁ FS.Cond (λ p → iᴮ p ≤ᴮ b) ⟩
  i-dense b = PT.map step
    where
      step : Σ[ x ∈ S ] ⟨ x ∈ˢ fst b ⟩ → Σ[ p ∈ FS.Cond ] ⟨ iᴮ p ≤ᴮ b ⟩
      step (x , hx) = (x , xc) , below
        where
          xc : ⟨ x ∈ˢ carrier ⟩
          xc = B-sub (fst b) (snd b) x hx
          sub : cone x ⊑ mem (fst b)
          sub y hy k = B-down (fst b) (snd b) y x hy xc k hx
          below : ⟨ (iSet x , iSet-inB x) ≤ᴮ b ⟩
          below y hy =
            B-regular (fst b) (snd b) .fst y yc
              (star²-mono (cone x) (mem (fst b)) sub y yc (w .snd))
            where
              w : ⟨ (y ∈ˢ carrier) ⊓ coneΔ carrier order x y ⟩
              w = subst ⟨_⟩ (iSet-mem x y) hy
              yc : ⟨ y ∈ˢ carrier ⟩
              yc = w .fst

  -- ---------------------------------------------------------------
  -- Meet, complement, join
  -- ---------------------------------------------------------------

  -- The meet is a plain intersection, and it is regular because the
  -- regular elements of any Heyting algebra are closed under meet. The
  -- Separation is taken inside the first argument, so the carrier guard
  -- comes for free.

  Regular-meet : (W V : Pred) → Regular W → Regular V
               → Regular (λ x → W x ⊓ V x)
  Regular-meet W V rw rv = down , up
    where
      M : Pred
      M = λ x → W x ⊓ V x
      dcM : DownClosed M
      dcM r s hr hs hrs h =
          Regular→DownClosed W rw r s hr hs hrs (h .fst)
        , Regular→DownClosed V rv r s hr hs hrs (h .snd)
      down : starOf (starOf M) ⊑ M
      down x hx h =
          rw .fst x hx (star²-mono M W (λ y _ k → k .fst) x hx h)
        , rv .fst x hx (star²-mono M V (λ y _ k → k .snd) x hx h)
      up : M ⊑ starOf (starOf M)
      up = star-expand M dcM

  meetSet : El → El → S
  meetSet u v = separateOf sep (fst u) (var zero ∈̇ con (fst v))

  meet-mem : (u v : El) (x : S)
           → (x ∈ˢ meetSet u v) ≡ ((x ∈ˢ fst u) ⊓ (x ∈ˢ fst v))
  meet-mem u v x = separateOf-spec sep (fst u) (var zero ∈̇ con (fst v)) x

  _⊓ᴮ_ : El → El → El
  u ⊓ᴮ v = meetSet u v , inB (meetSet u v) sub reg
    where
      sub : ⟨ meetSet u v ⊆ˢ carrier ⟩
      sub x h = B-sub (fst u) (snd u) x (subst ⟨_⟩ (meet-mem u v x) h .fst)
      M : Pred
      M = λ x → (x ∈ˢ fst u) ⊓ (x ∈ˢ fst v)
      e : mem (meetSet u v) ≑ M
      e = spec≑ (meetSet u v) M (meet-mem u v)
      reg : Regular (mem (meetSet u v))
      reg = Regular-≑ M (mem (meetSet u v)) (≑-sym (mem (meetSet u v)) M e)
              (Regular-meet (mem (fst u)) (mem (fst v))
                 (B-regular (fst u) (snd u)) (B-regular (fst v) (snd v)))

  infixr 12 _⊓ᴮ_

  ⊓ᴮ-le₁ : (u v : El) → ⟨ (u ⊓ᴮ v) ≤ᴮ u ⟩
  ⊓ᴮ-le₁ u v x h = subst ⟨_⟩ (meet-mem u v x) h .fst

  ⊓ᴮ-le₂ : (u v : El) → ⟨ (u ⊓ᴮ v) ≤ᴮ v ⟩
  ⊓ᴮ-le₂ u v x h = subst ⟨_⟩ (meet-mem u v x) h .snd

  ⊓ᴮ-glb : (u v w : El) → ⟨ w ≤ᴮ u ⟩ → ⟨ w ≤ᴮ v ⟩ → ⟨ w ≤ᴮ (u ⊓ᴮ v) ⟩
  ⊓ᴮ-glb u v w f g x h =
    subst ⟨_⟩ (sym (meet-mem u v x)) (f x h , g x h)

  -- The pseudocomplement. A single star is already regular, so nothing has
  -- to be said about the complement beyond the Separation itself.

  negφ : S → Formula S 1
  negφ d =
    sepAt (pseudoAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero))) zero)
          (carrier ∷ order ∷ d ∷ [])

  negSet : S → S
  negSet d = separateOf sep carrier (negφ d)

  neg-mem : (d x : S)
          → (x ∈ˢ negSet d) ≡ ((x ∈ˢ carrier) ⊓ pseudoΔ carrier order d x)
  neg-mem d x =
    separateOf-spec sep carrier (negφ d) x
    ∙ cong (λ w → (x ∈ˢ carrier) ⊓ w)
        (sepAt-reading
           (pseudoAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero))) zero)
           (carrier ∷ order ∷ d ∷ []) x)

  ¬ᴮ_ : El → El
  ¬ᴮ u = negSet (fst u)
       , fromStar (mem (fst u)) (negSet (fst u)) (neg-mem (fst u))
           (B-down (fst u) (snd u))

  infix 13 ¬ᴮ_

  -- The join is written as ONE Separation with the regularized union
  -- inline. Building it as a union followed by a regularization would put
  -- Union into the core ledger, and the core does not have it.

  joinφ : S → S → Formula S 1
  joinφ d e =
    sepAt (joinAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
                   (suc (suc (suc (suc zero)))) zero)
          (carrier ∷ order ∷ d ∷ e ∷ [])

  joinSet : S → S → S
  joinSet d e = separateOf sep carrier (joinφ d e)

  join-mem : (d e x : S)
           → (x ∈ˢ joinSet d e) ≡ ((x ∈ˢ carrier) ⊓ joinΔ carrier order d e x)
  join-mem d e x =
    separateOf-spec sep carrier (joinφ d e) x
    ∙ cong (λ w → (x ∈ˢ carrier) ⊓ w)
        (sepAt-reading
           (joinAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
                    (suc (suc (suc (suc zero)))) zero)
           (carrier ∷ order ∷ d ∷ e ∷ []) x)

  pairUnion : El → El → Pred
  pairUnion u v = λ s → (s ∈ˢ fst u) ⊔ (s ∈ˢ fst v)

  pairUnion-down : (u v : El) → DownClosed (pairUnion u v)
  pairUnion-down u v r s hr hs hrs =
    PT.map (λ { (inl a) → inl (B-down (fst u) (snd u) r s hr hs hrs a)
              ; (inr b) → inr (B-down (fst v) (snd v) r s hr hs hrs b) })

  _⊔ᴮ_ : El → El → El
  u ⊔ᴮ v = joinSet (fst u) (fst v)
         , fromStar (unionStarΔ carrier order (fst u) (fst v))
             (joinSet (fst u) (fst v)) (join-mem (fst u) (fst v))
             (star-down (pairUnion u v))

  infixr 12 _⊔ᴮ_

  ⊔ᴮ-ge₁ : (u v : El) → ⟨ u ≤ᴮ (u ⊔ᴮ v) ⟩
  ⊔ᴮ-ge₁ u v x h =
    subst ⟨_⟩ (sym (join-mem (fst u) (fst v) x))
      ( xc
      , star-expand (pairUnion u v) (pairUnion-down u v) x xc ∣ inl h ∣₁ )
    where
      xc : ⟨ x ∈ˢ carrier ⟩
      xc = B-sub (fst u) (snd u) x h

  ⊔ᴮ-ge₂ : (u v : El) → ⟨ v ≤ᴮ (u ⊔ᴮ v) ⟩
  ⊔ᴮ-ge₂ u v x h =
    subst ⟨_⟩ (sym (join-mem (fst u) (fst v) x))
      ( xc
      , star-expand (pairUnion u v) (pairUnion-down u v) x xc ∣ inr h ∣₁ )
    where
      xc : ⟨ x ∈ˢ carrier ⟩
      xc = B-sub (fst v) (snd v) x h

  ⊔ᴮ-lub : (u v w : El) → ⟨ u ≤ᴮ w ⟩ → ⟨ v ≤ᴮ w ⟩ → ⟨ (u ⊔ᴮ v) ≤ᴮ w ⟩
  ⊔ᴮ-lub u v w f g x h =
    B-regular (fst w) (snd w) .fst x xc
      (star²-mono (pairUnion u v) (mem (fst w)) below x xc (p .snd))
    where
      p : ⟨ (x ∈ˢ carrier) ⊓ joinΔ carrier order (fst u) (fst v) x ⟩
      p = subst ⟨_⟩ (join-mem (fst u) (fst v) x) h
      xc : ⟨ x ∈ˢ carrier ⟩
      xc = p .fst
      below : pairUnion u v ⊑ mem (fst w)
      below y _ k =
        PT.rec (snd (y ∈ˢ fst w))
          (λ { (inl a) → f y a ; (inr b) → g y b }) k

  -- ---------------------------------------------------------------
  -- Completeness, relative to the model's coded subsets
  -- ---------------------------------------------------------------

  -- The family is a ground code X with X ⊆ B, never a host family over an
  -- arbitrary index type. This restriction is the whole content of
  -- "complete for the ground's coded subsets"; the one legal bridge to a
  -- host family is codedFamilyJoin below, whose coding hypothesis is an
  -- explicit argument.

  supφ : S → Formula S 1
  supφ a =
    sepAt (supAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero))) zero)
          (carrier ∷ order ∷ a ∷ [])

  supSet : S → S
  supSet a = separateOf sep carrier (supφ a)

  sup-mem : (a x : S)
          → (x ∈ˢ supSet a) ≡ ((x ∈ˢ carrier) ⊓ supΔ carrier order a x)
  sup-mem a x =
    separateOf-spec sep carrier (supφ a) x
    ∙ cong (λ w → (x ∈ˢ carrier) ⊓ w)
        (sepAt-reading
           (supAtˢ (suc zero) (suc (suc zero)) (suc (suc (suc zero))) zero)
           (carrier ∷ order ∷ a ∷ []) x)

  union-down : (X : S) → ⟨ X ⊆ˢ B ⟩ → DownClosed (memUnionΔ X)
  union-down X h r s hr hs hrs =
    PT.map (λ { (w , hwX , hsw) →
                w , (hwX , B-down w (h w hwX) r s hr hs hrs hsw) })

  supᴮ : (X : S) → ⟨ X ⊆ˢ B ⟩ → El
  supᴮ X h = supSet X
           , fromStar (supStarΔ carrier order X) (supSet X) (sup-mem X)
               (star-down (memUnionΔ X))

  sup-upper : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u : El)
            → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ supᴮ X h ⟩
  sup-upper X h u hu x hx =
    subst ⟨_⟩ (sym (sup-mem X x))
      ( xc
      , star-expand (memUnionΔ X) (union-down X h) x xc
          ∣ fst u , (hu , hx) ∣₁ )
    where
      xc : ⟨ x ∈ˢ carrier ⟩
      xc = B-sub (fst u) (h (fst u) hu) x hx

  sup-least : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (v : El)
            → ((u : El) → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ v ⟩)
            → ⟨ supᴮ X h ≤ᴮ v ⟩
  sup-least X h v ub x hx =
    B-regular (fst v) (snd v) .fst x xc
      (star²-mono (memUnionΔ X) (mem (fst v)) below x xc (p .snd))
    where
      p : ⟨ (x ∈ˢ carrier) ⊓ supΔ carrier order X x ⟩
      p = subst ⟨_⟩ (sup-mem X x) hx
      xc : ⟨ x ∈ˢ carrier ⟩
      xc = p .fst
      below : memUnionΔ X ⊑ mem (fst v)
      below y _ k =
        PT.rec (snd (y ∈ˢ fst v))
          (λ { (w , hwX , hyw) → ub (w , h w hwX) hwX y hyw }) k

  -- The infimum needs no regularization: an arbitrary intersection of
  -- regular opens is regular, because it is downward closed and is below
  -- each of them.

  infφ : S → Formula S 1
  infφ a = sepAt (interAtˢ (suc zero) zero) (a ∷ [])

  infSet : S → S
  infSet a = separateOf sep carrier (infφ a)

  inf-mem : (a x : S)
          → (x ∈ˢ infSet a) ≡ ((x ∈ˢ carrier) ⊓ interΔ a x)
  inf-mem a x =
    separateOf-spec sep carrier (infφ a) x
    ∙ cong (λ w → (x ∈ˢ carrier) ⊓ w)
        (sepAt-reading (interAtˢ (suc zero) zero) (a ∷ []) x)

  inter-Regular : (X : S) → ⟨ X ⊆ˢ B ⟩ → Regular (interΔ X)
  inter-Regular X h = down , up
    where
      dc : DownClosed (interΔ X)
      dc r s hr hs hrs k w hw =
        B-down w (h w hw) r s hr hs hrs (k w hw)
      down : starOf (starOf (interΔ X)) ⊑ interΔ X
      down x hx g w hw =
        B-regular w (h w hw) .fst x hx
          (star²-mono (interΔ X) (mem w) (λ y _ k → k w hw) x hx g)
      up : interΔ X ⊑ starOf (starOf (interΔ X))
      up = star-expand (interΔ X) dc

  infᴮ : (X : S) → ⟨ X ⊆ˢ B ⟩ → El
  infᴮ X h = infSet X
           , fromGuarded (interΔ X) (infSet X) (inf-mem X) (inter-Regular X h)

  inf-lower : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u : El)
            → ⟨ fst u ∈ˢ X ⟩ → ⟨ infᴮ X h ≤ᴮ u ⟩
  inf-lower X h u hu x hx =
    subst ⟨_⟩ (inf-mem X x) hx .snd (fst u) hu

  inf-greatest : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (v : El)
               → ((u : El) → ⟨ fst u ∈ˢ X ⟩ → ⟨ v ≤ᴮ u ⟩)
               → ⟨ v ≤ᴮ infᴮ X h ⟩
  inf-greatest X h v lb x hx =
    subst ⟨_⟩ (sym (inf-mem X x))
      ( B-sub (fst v) (snd v) x hx
      , (λ w hw → lb (w , h w hw) hw x hx) )

  record CompleteForCoded : Type ℓ where
    field
      sup          : (X : S) → ⟨ X ⊆ˢ B ⟩ → El
      sup-ub       : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u : El)
                   → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ sup X h ⟩
      sup-lub      : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (v : El)
                   → ((u : El) → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ v ⟩)
                   → ⟨ sup X h ≤ᴮ v ⟩
      inf          : (X : S) → ⟨ X ⊆ˢ B ⟩ → El
      inf-lb       : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u : El)
                   → ⟨ fst u ∈ˢ X ⟩ → ⟨ inf X h ≤ᴮ u ⟩
      inf-glb      : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (v : El)
                   → ((u : El) → ⟨ fst u ∈ˢ X ⟩ → ⟨ v ≤ᴮ u ⟩)
                   → ⟨ v ≤ᴮ inf X h ⟩

  completeForCoded : CompleteForCoded
  completeForCoded = record
    { sup     = supᴮ     ; sup-ub = sup-upper ; sup-lub = sup-least
    ; inf     = infᴮ     ; inf-lb = inf-lower ; inf-glb = inf-greatest }

  -- ---------------------------------------------------------------
  -- The one legal bridge to a host family
  -- ---------------------------------------------------------------

  -- A host family I → El has a supremum in the completion only when its
  -- values are attained by a code, and that hypothesis is an explicit
  -- argument here and a field of AdmittedFamily below. There is no
  -- hostSup : (I : Type ℓ) → (I → El) → El anywhere in this file.

  codedFamilyJoin : (I : Type ℓ) (f : I → El) (X : S) (sub : ⟨ X ⊆ˢ B ⟩)
    → ((b : S) → (b ∈ˢ X) ≡ ⋁ I (λ k → b ≈ˢ fst (f k)))
    → ((k : I) → ⟨ f k ≤ᴮ supᴮ X sub ⟩)
      × ((v : El) → ((k : I) → ⟨ f k ≤ᴮ v ⟩) → ⟨ supᴮ X sub ≤ᴮ v ⟩)
  codedFamilyJoin I f X sub att = up , lo
    where
      inX : (k : I) → ⟨ fst (f k) ∈ˢ X ⟩
      inX k = subst ⟨_⟩ (sym (att (fst (f k))))
                ∣ k , OP.≈ˢ-refl ext (fst (f k)) ∣₁
      up : (k : I) → ⟨ f k ≤ᴮ supᴮ X sub ⟩
      up k = sup-upper X sub (f k) (inX k)
      lo : (v : El) → ((k : I) → ⟨ f k ≤ᴮ v ⟩) → ⟨ supᴮ X sub ≤ᴮ v ⟩
      lo v hv = sup-least X sub v step
        where
          step : (u : El) → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ v ⟩
          step u hu =
            PT.rec (snd (u ≤ᴮ v))
              (λ { (k , eq) →
                   subst (λ w → ⟨ w ⊆ˢ fst v ⟩)
                     (sym (≈ˢ-to-path (fst u) (fst (f k)) eq)) (hv k) })
              (subst ⟨_⟩ (att (fst u)) hu)

  -- The K0 contract, verbatim: Separation of the attained values inside B,
  -- an admitted supremum, and upper-bound transfer. This is the interface
  -- the name-evaluation package will call, and shipping it is an exit
  -- condition of K2. AdmittedFamily lands at Type (ℓ-suc ℓ), not Type ℓ,
  -- because the attainment field is a path in the truth-value type.

  record AdmittedFamily {I : Type ℓ} (val : I → El) : Type (ℓ-suc ℓ) where
    field
      values     : S
      values-sub : ⟨ values ⊆ˢ B ⟩
      attained   : (b : S) → (b ∈ˢ values) ≡ ⋁ I (λ k → b ≈ˢ fst (val k))

    join : El
    join = supᴮ values values-sub

  admitted-upper : {I : Type ℓ} {val : I → El} (a : AdmittedFamily val)
                 → (k : I) → ⟨ val k ≤ᴮ AdmittedFamily.join a ⟩
  admitted-upper {I} {val} a =
    codedFamilyJoin I val (AdmittedFamily.values a)
      (AdmittedFamily.values-sub a) (AdmittedFamily.attained a) .fst

  admitted-transfer : {I : Type ℓ} {val : I → El} (a : AdmittedFamily val)
                    (c : El) → ((k : I) → ⟨ val k ≤ᴮ c ⟩)
                    → ⟨ AdmittedFamily.join a ≤ᴮ c ⟩
  admitted-transfer {I} {val} a =
    codedFamilyJoin I val (AdmittedFamily.values a)
      (AdmittedFamily.values-sub a) (AdmittedFamily.attained a) .snd

  admitted-unique : {I : Type ℓ} {val : I → El} (a b : AdmittedFamily val)
                  → AdmittedFamily.join a ≡ AdmittedFamily.join b
  admitted-unique a b =
    ≤ᴮ-antisym (AdmittedFamily.join a) (AdmittedFamily.join b)
      (admitted-transfer a (AdmittedFamily.join b) (admitted-upper b))
      (admitted-transfer b (AdmittedFamily.join a) (admitted-upper a))

  -- ---------------------------------------------------------------
  -- Coded subsets of conditions, and genericity
  -- ---------------------------------------------------------------

  -- Every notion below quantifies over a CODE d : S, never over a host
  -- predicate on conditions. That single decision is what keeps the
  -- genericity record at Type ℓ and what makes the chain conditions of
  -- the later packages statable; a host-quantified draft lands at
  -- Type (ℓ-suc ℓ), which is the diagnostic.

  subsetOf : S → Ω
  subsetOf d = d ⊆ˢ carrier

  compatibleᴵ : S → S → Ω
  compatibleᴵ = compatibleΔ carrier order

  denseᴵ : S → Ω
  denseᴵ = denseΔ carrier order

  predenseᴵ : S → Ω
  predenseᴵ = predenseΔ carrier order

  denseBelowᴵ : S → S → Ω
  denseBelowᴵ r d =
    ⋀ S (λ q → (q ∈ˢ carrier) ⇒ ((q ≼ᴵ r) ⇒
      ⋁ S (λ p → (p ∈ˢ d) ⊓ (p ≼ᴵ q))))

  antichainᴵ : S → Ω
  antichainᴵ d =
    ⋀ S (λ p → ⋀ S (λ q →
      (((p ∈ˢ carrier) ⊓ (p ∈ˢ d))
        ⊓ (((q ∈ˢ carrier) ⊓ (q ∈ˢ d)) ⊓ compatibleᴵ p q))
      ⇒ ((p ≡ q) , isSetS p q)))

  reflect : S → FS.Sub
  reflect d p = fst p ∈ˢ d

  compat-transfer→ : (p q : FS.Cond) → ⟨ compatibleᴵ (fst p) (fst q) ⟩
                   → ⟨ FS.compatible p q ⟩
  compat-transfer→ p q =
    PT.map (λ { (r , hrc , h₁ , h₂) → (r , hrc) , (h₁ , h₂) })

  compat-transfer← : (p q : FS.Cond) → ⟨ FS.compatible p q ⟩
                   → ⟨ compatibleᴵ (fst p) (fst q) ⟩
  compat-transfer← p q =
    PT.map (λ { (r , h₁ , h₂) → fst r , (snd r , (h₁ , h₂)) })

  dense-transfer→ : (d : S) → ⟨ subsetOf d ⟩ → ⟨ denseᴵ d ⟩
                  → ⟨ FS.dense (reflect d) ⟩
  dense-transfer→ d sub dn q =
    PT.map (λ { (p , hpd , hpq) → (p , sub p hpd) , (hpd , hpq) })
           (dn (fst q) (snd q))

  dense-transfer← : (d : S) → ⟨ FS.dense (reflect d) ⟩ → ⟨ denseᴵ d ⟩
  dense-transfer← d dn q hq =
    PT.map (λ { (p , hpd , hpq) → fst p , (hpd , hpq) }) (dn (q , hq))

  predense-transfer→ : (d : S) → ⟨ subsetOf d ⟩ → ⟨ predenseᴵ d ⟩
                     → ⟨ FS.predense (reflect d) ⟩
  predense-transfer→ d sub pd q =
    PT.map (λ { (p , hpd , hc) →
                (p , sub p hpd) , (hpd , compat-transfer→ (p , sub p hpd) q hc) })
           (pd (fst q) (snd q))

  predense-transfer← : (d : S) → ⟨ FS.predense (reflect d) ⟩ → ⟨ predenseᴵ d ⟩
  predense-transfer← d pd q hq =
    PT.map (λ { (p , hpd , hc) →
                fst p , (hpd , compat-transfer← p (q , hq) hc) })
           (pd (q , hq))

  antichain-transfer→ : (d : S) → ⟨ subsetOf d ⟩ → ⟨ antichainᴵ d ⟩
                      → ⟨ FS.antichain (reflect d) ⟩
  antichain-transfer→ d sub ac p q (hp , hq , hc) =
    Σ≡Prop (λ x → snd (x ∈ˢ carrier))
      (ac (fst p) (fst q)
        ( (snd p , hp)
        , ((snd q , hq) , compat-transfer← p q hc) ))

  -- Genericity, model relative: G is a HOST subset of the decoded
  -- conditions, and the dense sets it must meet are MODEL elements. The
  -- asymmetry is forced. Symmetrizing downward asks for a host generic
  -- filter, which Track A refutes for atomless notions under LEM;
  -- symmetrizing upward asks for G itself to be coded, which Separation
  -- inside the model refutes.

  record isGeneric (G : FS.Sub) : Type ℓ where
    field
      filter : FS.isFilter G
      meets  : (d : S) → ⟨ subsetOf d ⟩ → ⟨ denseᴵ d ⟩
             → ⟨ ⋁ FS.Cond (λ p → (FS._∈ᴾ_ p G) ⊓ (fst p ∈ˢ d)) ⟩

  generic-inhabited : (G : FS.Sub) → isGeneric G → ⟨ FS.positive G ⟩
  generic-inhabited G g = FS.isFilter.inhabited (isGeneric.filter g)

  -- Genericity read against the host vocabulary: it is exactly host
  -- genericity restricted to the reflections of coded dense sets.

  generic-as-host : (G : FS.Sub) → isGeneric G → (d : S) → ⟨ subsetOf d ⟩
                  → ⟨ FS.dense (reflect d) ⟩
                  → ⟨ ⋁ FS.Cond (λ p → (FS._∈ᴾ_ p G) ⊓ (FS._∈ᴾ_ p (reflect d))) ⟩
  generic-as-host G g d sub dn = isGeneric.meets g d sub (dense-transfer← d dn)

  generic-meets-predense : (G : FS.Sub) → isGeneric G → (d : S)
                         → ⟨ subsetOf d ⟩ → ⟨ denseᴵ d ⟩
                         → ⟨ FS.predense (reflect d) ⟩
  generic-meets-predense G g d sub dn =
    FS.dense-predense (reflect d) (dense-transfer→ d sub dn)

  -- ---------------------------------------------------------------
  -- Dense below, the constructive half
  -- ---------------------------------------------------------------

  -- A coded regular open already contains every condition below which it
  -- is dense. The converse, that membership implies density below, is the
  -- classical half and lives in module Classical.

  denseBelow→mem : (u : S) → ⟨ u ∈ˢ B ⟩ → (q : S) → ⟨ q ∈ˢ carrier ⟩
                 → ⟨ denseBelowᴵ q u ⟩ → ⟨ q ∈ˢ u ⟩
  denseBelow→mem u hu q hq db =
    B-regular u hu .fst q hq step
    where
      step : ⟨ starOf (starOf (mem u)) q ⟩
      step r hr hrq k =
        PT.rec isProp⊥*
          (λ { (p , hpu , hpr) →
               k p (B-sub u hu p hpu) hpr hpu })
          (db r hr hrq)

  -- ---------------------------------------------------------------
  -- The cone formula against Bell's displayed formula
  -- ---------------------------------------------------------------

  -- Track E's coneΔ is the CONSTRUCTIVE double star: "every refinement of
  -- q inside the carrier is NOT NOT compatible with p". Bell's displayed
  -- formula (1) is the doubly negated statement stripped of its double
  -- negation, so only this direction is free; the other one is classical
  -- and lives in module Classical.

  Bell→cone : (p q : S)
    → ⟨ ⋀ S (λ r → (r ∈ˢ carrier) ⇒ ((r ≼ᴵ q) ⇒ compatibleᴵ r p)) ⟩
    → ⟨ coneΔ carrier order p q ⟩
  Bell→cone p q h r hr hrq cs =
    subst ⟨_⟩ (CV.coneStarΔ-as-incompatible carrier order p r) cs
      (h r hr hrq)

  positive→nonzero : (u : El) → ⟨ positiveᴮ u ⟩ → (u ≡ ⊥ᴮ) → ⟨ ⊥ ⟩
  positive→nonzero u h eq =
    PT.rec isProp⊥*
      (λ { (x , hx) →
           ⊥ᴮ-empty x (subst (λ w → ⟨ x ∈ˢ fst w ⟩) eq hx) }) h


  -- Track C measured that the host form of this needs no excluded middle,
  -- and the coded form needs none either: a regular open is downward
  -- closed, so a member of it is already a witness below every refinement
  -- of itself. The architecture charged this direction a LEM and it does
  -- not cost one.

  mem→denseBelow : (u : S) → ⟨ u ∈ˢ B ⟩ → (q : S) → ⟨ q ∈ˢ carrier ⟩
                 → ⟨ q ∈ˢ u ⟩ → ⟨ denseBelowᴵ q u ⟩
  mem→denseBelow u hu q hq hqu r hr hrq =
    ∣ r , (B-down u hu r q hr hq hrq hqu , refl≼ r hr) ∣₁

  -- Two pointwise unpackings. They are stated generically, at variables
  -- u v : El and p : S, and never at the composite iᴮ p ⊓ᴮ iᴮ q: a
  -- statement whose TYPE mentions that composite sends the elaborator
  -- into a check that never finished: three drafts, killed at 19 min,
  -- 11 min and 11 min, each at about 1.15 GB resident. See the report.

  meet-split : (u v : El) (z : S) → ⟨ z ∈ˢ fst (u ⊓ᴮ v) ⟩
             → ⟨ (z ∈ˢ fst u) ⊓ (z ∈ˢ fst v) ⟩
  meet-split u v z hz = subst ⟨_⟩ (meet-mem u v z) hz

  iSet-split : (p z : S) → ⟨ z ∈ˢ iSet p ⟩
             → ⟨ (z ∈ˢ carrier) ⊓ coneΔ carrier order p z ⟩
  iSet-split p z hz = subst ⟨_⟩ (iSet-mem p z) hz

  meet-join : (u v : El) (z : S) → ⟨ (z ∈ˢ fst u) ⊓ (z ∈ˢ fst v) ⟩
            → ⟨ z ∈ˢ fst (u ⊓ᴮ v) ⟩
  meet-join u v z h = subst ⟨_⟩ (sym (meet-mem u v z)) h

  -- The free half of Bell's Problem 2.4(iii) compatibility clause. It is
  -- stated with the meet abstracted into m, for the reason recorded at
  -- meet-split above; a caller instantiates m := iᴮ p ⊓ᴮ iᴮ q and passes
  -- meet-join.

  i-compat→-at : (p q : Cond) (m : El)
               → ((z : S) → ⟨ (z ∈ˢ iSet (fst p)) ⊓ (z ∈ˢ iSet (fst q)) ⟩
                    → ⟨ z ∈ˢ fst m ⟩)
               → ⟨ FS.compatible p q ⟩ → ⟨ positiveᴮ m ⟩
  i-compat→-at p q m into =
    PT.map (λ { (r , hrp , hrq) →
                fst r , into (fst r) ( i-intro p (fst r) (snd r) hrp
                                     , i-intro q (fst r) (snd r) hrq ) })

  -- ---------------------------------------------------------------
  -- The reading injection into the host algebra
  -- ---------------------------------------------------------------

  -- This is the central economy of the design. A coded element is read as
  -- a host subset of the decoded conditions; the reading is injective and
  -- preserves every finite operation, so every BOOLEAN LAW of the coded
  -- algebra is transported from Track C's roLaws along reads-inj, and not
  -- one of them is proved internally here.

  module RO = HRO FS.Cond FS.isSetC FS._≼_ FS.≼-refl
                  (λ {a} {b} {c} → FS.≼-trans {a} {b} {c})

  downP : Pred → RO.Sub
  downP W p = W (fst p)

  readsᴾ : El → RO.Sub
  readsᴾ u p = fst p ∈ˢ fst u

  -- The two star operators agree. The host one quantifies over the
  -- decoded conditions, the coded one over the carrier with a membership
  -- guard, and currying the sigma is the whole proof.

  ⋆-agree→ : (W : Pred) (q : FS.Cond)
           → ⟨ starOf W (fst q) ⟩ → ⟨ RO._⋆ (downP W) q ⟩
  ⋆-agree→ W q h r hrq hw = h (fst r) (snd r) hrq hw

  ⋆-agree← : (W : Pred) (q : FS.Cond)
           → ⟨ RO._⋆ (downP W) q ⟩ → ⟨ starOf W (fst q) ⟩
  ⋆-agree← W q h r hr hrq hw = h (r , hr) hrq hw

  ⋆⋆-agree→ : (W : Pred) (q : FS.Cond)
            → ⟨ starOf (starOf W) (fst q) ⟩ → ⟨ RO._⋆ (RO._⋆ (downP W)) q ⟩
  ⋆⋆-agree→ W q h r hrq k = h (fst r) (snd r) hrq (⋆-agree← W r k)

  ⋆⋆-agree← : (W : Pred) (q : FS.Cond)
            → ⟨ RO._⋆ (RO._⋆ (downP W)) q ⟩ → ⟨ starOf (starOf W) (fst q) ⟩
  ⋆⋆-agree← W q h r hr hrq k = h (r , hr) hrq (⋆-agree→ W (r , hr) k)

  reads-isRegular : (u : El) → ⟨ RO.isRegular (readsᴾ u) ⟩
  reads-isRegular u q =
      (λ hu → ⋆⋆-agree→ (mem (fst u)) q
                (B-regular (fst u) (snd u) .snd (fst q) (snd q) hu))
    , (λ hs → B-regular (fst u) (snd u) .fst (fst q) (snd q)
                (⋆⋆-agree← (mem (fst u)) q hs))

  reads : El → RO.Reg
  reads u = readsᴾ u , reads-isRegular u

  reads-inj : (u v : El) → reads u ≡ reads v → u ≡ v
  reads-inj u v e = El≡ u v (λ x → ⇔toPath
    (λ hx → RO.Reg⊑ (reads u) (reads v) e
              (x , B-sub (fst u) (snd u) x hx) hx)
    (λ hx → RO.Reg⊑ (reads v) (reads u) (sym e)
              (x , B-sub (fst v) (snd v) x hx) hx))

  reads-⊤ : reads ⊤ᴮ ≡ RO.⊤ᴮ
  reads-⊤ = RO.Reg≡ (reads ⊤ᴮ) RO.⊤ᴮ (λ q _ → tt*) (λ q _ → snd q)

  reads-⊥ : reads ⊥ᴮ ≡ RO.⊥ᴮ
  reads-⊥ = RO.Reg≡ (reads ⊥ᴮ) RO.⊥ᴮ
    (λ q h → ⊥ᴮ-empty (fst q) h) (λ q h → Empty.rec* h)

  reads-⊓ : (u v : El) → reads (u ⊓ᴮ v) ≡ (RO._⊓ᴮ_ (reads u) (reads v))
  reads-⊓ u v = RO.Reg≡ (reads (u ⊓ᴮ v)) (RO._⊓ᴮ_ (reads u) (reads v))
    (λ q h → meet-split u v (fst q) h)
    (λ q h → subst ⟨_⟩ (sym (meet-mem u v (fst q))) h)

  reads-¬ : (u : El) → reads (¬ᴮ u) ≡ (RO.¬ᴮ_ (reads u))
  reads-¬ u = RO.Reg≡ (reads (¬ᴮ u)) (RO.¬ᴮ_ (reads u))
    (λ q h → ⋆-agree→ (mem (fst u)) q
               (subst ⟨_⟩ (neg-mem (fst u) (fst q)) h .snd))
    (λ q h → subst ⟨_⟩ (sym (neg-mem (fst u) (fst q)))
               (snd q , ⋆-agree← (mem (fst u)) q h))

  reads-⊔ : (u v : El) → reads (u ⊔ᴮ v) ≡ (RO._⊔ᴮ_ (reads u) (reads v))
  reads-⊔ u v = RO.Reg≡ (reads (u ⊔ᴮ v)) (RO._⊔ᴮ_ (reads u) (reads v))
    (λ q h → ⋆⋆-agree→ (pairUnion u v) q
               (subst ⟨_⟩ (join-mem (fst u) (fst v) (fst q)) h .snd))
    (λ q h → subst ⟨_⟩ (sym (join-mem (fst u) (fst v) (fst q)))
               (snd q , ⋆⋆-agree← (pairUnion u v) q h))

  -- The order agrees too, so a Boolean order fact transported through
  -- reads-inj lands on the coded order without a further step.

  reads-≤→ : (u v : El) → ⟨ u ≤ᴮ v ⟩ → RO._⊑_ (readsᴾ u) (readsᴾ v)
  reads-≤→ u v h q = h (fst q)

  reads-≤← : (u v : El) → RO._⊑_ (readsᴾ u) (readsᴾ v) → ⟨ u ≤ᴮ v ⟩
  reads-≤← u v h x hx = h (x , B-sub (fst u) (snd u) x hx) hx

-- ---------------------------------------------------------------------
-- The classical fragment
-- ---------------------------------------------------------------------

-- Separated out so that the constructive core above can be read off its
-- own parameter list. Excluded middle is an explicit FIRST ARGUMENT of
-- each lemma here and is not a parameter of this module, so no
-- constructive result is silently covered by it. At the constructible
-- instance the level is ℓ-suc ℓ₀, which is exactly the hypothesis the two
-- landmark theorems already carry, so K2 adds nothing to the ledger.

module Classical
  (ext   : Extensionality)
  (pow   : PowerSet)
  (sep   : Separation)
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (𝔓     : Presentation)
  (laws  : Coded.ForcingLaws 𝔓)
  where

  open Coded 𝔓
  open Core ext pow sep paths 𝔓 laws

  -- Bell's displayed formula (1) for the regularized cone. This is a
  -- theorem needing excluded middle, never a reading by reflexivity.

  cone-as-Bell : LEM ℓ → (p q : S) → ⟨ coneΔ carrier order p q ⟩
    → ⟨ ⋀ S (λ r → (r ∈ˢ carrier) ⇒ ((r ≼ᴵ q) ⇒ compatibleᴵ r p)) ⟩
  cone-as-Bell lem p q h r hr hrq = decide (lem (compatibleᴵ r p))
    where
      decide : ⟨ compatibleᴵ r p ⟩ ⊎ (⟨ compatibleᴵ r p ⟩ → Empty.⊥)
             → ⟨ compatibleᴵ r p ⟩
      decide (inl c) = c
      decide (inr nc) = Empty.rec*
        (h r hr hrq
          (subst ⟨_⟩ (sym (CV.coneStarΔ-as-incompatible carrier order p r))
            (λ c → Empty.rec (nc c))))

  -- Inhabitedness is primitive and nonzero is the derived classical
  -- notion, not the other way round. Both directions are stated
  -- separately so that a consumer needing only the free one does not
  -- carry excluded middle; the free one is Core.positive→nonzero.

  nonzero→positive : LEM ℓ → (u : El) → ((u ≡ ⊥ᴮ) → ⟨ ⊥ ⟩)
                   → ⟨ positiveᴮ u ⟩
  nonzero→positive lem u nz = decide (lem (positiveᴮ u))
    where
      decide : ⟨ positiveᴮ u ⟩ ⊎ (⟨ positiveᴮ u ⟩ → Empty.⊥)
             → ⟨ positiveᴮ u ⟩
      decide (inl yes) = yes
      decide (inr no) = Empty.rec*
        (nz (El≡ u ⊥ᴮ
              (λ x → ⇔toPath (λ hx → Empty.rec (no ∣ x , hx ∣₁))
                             (λ hx → Empty.rec* (⊥ᴮ-empty x hx)))))

  -- Compatibility is recovered from a positive meet of two cones. The
  -- forward direction is Core.i-compat→ and is free; this one runs Bell's
  -- formula twice and closes up by transitivity, so it spends the LEM
  -- exactly where the double negation of the star calculus sits.

  compat-close : (p q : FS.Cond) (t : S) → ⟨ t ∈ˢ carrier ⟩
               → ⟨ t ≼ᴵ fst p ⟩
               → Σ[ s ∈ S ] ⟨ (s ∈ˢ carrier) ⊓ ((s ≼ᴵ t) ⊓ (s ≼ᴵ fst q)) ⟩
               → ⟨ FS.compatible p q ⟩
  compat-close p q t tc htp (s , sc , hst , hsq) =
    ∣ (s , sc) , (trans≼ s t (fst p) sc tc (snd p) hst htp , hsq) ∣₁

  compat-mid : LEM ℓ → (p q : FS.Cond) (z : S)
             → ⟨ coneΔ carrier order (fst q) z ⟩
             → Σ[ t ∈ S ] ⟨ (t ∈ˢ carrier) ⊓ ((t ≼ᴵ z) ⊓ (t ≼ᴵ fst p)) ⟩
             → ⟨ FS.compatible p q ⟩
  compat-mid lem p q z cq (t , tc , htz , htp) =
    PT.rec (snd (FS.compatible p q)) (compat-close p q t tc htp)
      (cone-as-Bell lem (fst q) z cq t tc htz)

  compat-from-meet : LEM ℓ → (p q : FS.Cond) (z : S) → ⟨ z ∈ˢ carrier ⟩
                   → ⟨ coneΔ carrier order (fst p) z ⟩
                   → ⟨ coneΔ carrier order (fst q) z ⟩
                   → ⟨ FS.compatible p q ⟩
  compat-from-meet lem p q z zc cp cq =
    PT.rec (snd (FS.compatible p q)) (compat-mid lem p q z cq)
      (cone-as-Bell lem (fst p) z cp z zc (refl≼ z zc))

  -- The packaged form, with the meet abstracted into a variable m whose
  -- members are known to lie in both cones. A consumer instantiates
  -- m := iᴮ p ⊓ᴮ iᴮ q and supplies meet-split; the abstraction is what
  -- keeps the composite out of this lemma's type.

  i-compat←-at : LEM ℓ → (p q : FS.Cond) (m : El)
               → ((z : S) → ⟨ z ∈ˢ fst m ⟩
                    → ⟨ (z ∈ˢ iSet (fst p)) ⊓ (z ∈ˢ iSet (fst q)) ⟩)
               → ⟨ positiveᴮ m ⟩ → ⟨ FS.compatible p q ⟩
  i-compat←-at lem p q m split h = PT.rec (snd (FS.compatible p q)) go h
    where
      go : Σ[ z ∈ S ] ⟨ z ∈ˢ fst m ⟩ → ⟨ FS.compatible p q ⟩
      go (z , hz) =
        compat-from-meet lem p q z (cpz .fst) (cpz .snd) (cqz .snd)
        where
          w : ⟨ (z ∈ˢ iSet (fst p)) ⊓ (z ∈ˢ iSet (fst q)) ⟩
          w = split z hz
          cpz : ⟨ (z ∈ˢ carrier) ⊓ coneΔ carrier order (fst p) z ⟩
          cpz = iSet-split (fst p) z (w .fst)
          cqz : ⟨ (z ∈ˢ carrier) ⊓ coneΔ carrier order (fst q) z ⟩
          cqz = iSet-split (fst q) z (w .snd)
