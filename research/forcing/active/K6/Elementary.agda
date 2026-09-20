{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track B: the `hasPair` and `hasUnion` fields of the ordinary profile at
-- the extension structure.
--
-- ---------------------------------------------------------------------
-- WHAT THE TWO FIELDS SAY, AND WHAT THIS FILE PROVES
-- ---------------------------------------------------------------------
--
-- Transcribed from the record's own source, OrdinaryProfile.agda:62-72, after
-- checking that OrdinaryZF has EIGHT fields at :126-135 and that `hasPair` and
-- `hasUnion` are the second and the third of them:
--
--     Pairing : Type ℓ
--     Pairing =
--       (a b : S)
--         → ⟨ ⋁ S (λ p → ⋀ S (λ x → iff (x ∈ˢ p) ((x ≈ˢ a) ⊔ (x ≈ˢ b)))) ⟩
--
--     Union : Type ℓ
--     Union =
--       (a : S)
--         → ⟨ ⋁ S (λ v → ⋀ S (λ x → iff (x ∈ˢ v)
--              (⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))) ⟩
--
-- Neither is a description: `℩` does not occur in OrdinaryProfile.agda and the
-- header says so at :53-56. Both are TRUNCATED EXISTENTIALS, `⋁` being
-- Logic.∃[]-syntax, so the deliverable is an explicitly constructed name under
-- `∣_∣₁` and nothing may be projected back out. Rule 2's sealing therefore has
-- no target among the fields themselves; it applies to the GROUND sets, and
-- every ground set this file uses (`pairOf`, `⋃ᴳ`, `mk`, `entryBound`) arrives
-- as a module PARAMETER, which cannot unfold at all.
--
-- The vacuity question is the one that matters here, because both fields only
-- assert that something EXISTS. A witness whose value is empty would satisfy
-- the type and prove nothing. So the content of this file is not `hasPair` and
-- `hasUnion`; it is `pair-mem` and `union-mem`, which say exactly WHAT the two
-- constructed names contain, in both directions, and out of which the two
-- fields fall in one line each through OrdinaryProfile.spec-to-iff.
--
-- ---------------------------------------------------------------------
-- THE MEASURED HYPOTHESIS, WHICH IS NOT THE ONE THE BRIEF NAMES
-- ---------------------------------------------------------------------
--
-- The architecture states both fields at `isFilter G`. Rule 14 and coordinator
-- ruling 13 govern: the measurement wins and it is reported. Measured here by
-- following the two proofs to the laws they actually project:
--
--   * `hasPair` spends ONE filter law, `inhabited`, in its weakest form
--     ⟨ positive G ⟩, and it spends it in exactly one place: the pair name
--     weights each of its two entries by EVERY condition, so an entry is
--     active as soon as SOME condition lies in G. `upward` and `directed` are
--     not used and are not in the telescope of `hasPairᴾ`.
--
--   * `hasUnion` spends TWO filter laws, `upward` and `directed`, and does NOT
--     spend `inhabited`. Both directions are one-sided: the forward direction
--     needs upward closure (from `r ∈ G` and `r ≼ p` conclude `p ∈ G`) and the
--     backward direction needs directedness (from `p , q ∈ G` produce an
--     `r ∈ G` below both). Neither follows from positivity.
--
-- This reproduces, for two different theorems inside one track, the split K5
-- measured between its Tracks E/F (positivity only) and its Track G (every law
-- is `directed`). The architecture's own spelling ships as a two-line corollary
-- through K5's own `filter-positive` and `isFilter`, in the seam probe
-- K6/ElementaryAtStructures.agda, so nothing downstream has to know.
--
-- ---------------------------------------------------------------------
-- THE TWO NAMES, AND WHY THE UNION ONE CARRIES REFINEMENT CONJUNCTS
-- ---------------------------------------------------------------------
--
-- `pairCode m n` is the set of entries `entry x p` with `x` one of `m`, `n`
-- and `p` ANY condition. `unionCode n` is the set of entries `entry χ r` for
-- which there are `y`, `p`, `q` with `entry y q ∈ n`, `entry χ p ∈ y`, and `r`
-- refining BOTH `p` and `q`.
--
-- Trap T-B1 is the reason the last two conjuncts are there, and dropping them
-- is not a weaker theorem but a wrong one. Without them the name would be
-- { entry χ p : entry y q ∈ n , entry χ p ∈ y }, weighting a grandchild by its
-- own weight and forgetting its parent's. The FORWARD direction then fails:
-- `p ∈ G` says nothing about `q`, so the `y` that the witness has to be a
-- member of is not shown to be a value member of `n` at all, and the only
-- repair is to weaken the statement. The break file K6/breaks/NoRefine.agda-break
-- records the goal that stands open. Weighting by a single shared condition
-- fails the same way in the other direction: the parent entry need not be
-- present at the child's weight.
--
-- Trap T-B2 is the mirror image on the pairing side: a transcriber of the
-- BOOLEAN construction writes one fixed condition into the pair name, because
-- at the Boolean side the top element is always in the ultrafilter. There is
-- no top at the poset side; a fixed `p₀` is in G for no stated reason and the
-- backward direction of `pair-mem` stops. K6/breaks/FixedCondition.agda-break
-- records it.
--
--
-- ---------------------------------------------------------------------
-- THE TELESCOPE AUDIT, RULE 15
-- ---------------------------------------------------------------------
--
-- A field's TYPE does not discriminate a legitimate proof from one standing on
-- a hypothesis that is false at a genuine forcing extension, because such a
-- hypothesis never appears in the body and no body-level grep can see it. So
-- every group of parameters below is named with the source that inhabits it.
--
--  1. `paths`. A statement about the GROUND structure and about nothing else:
--     its equality is realised as a host path. It is GroundDescription.agda's
--     own module parameter at :34-35 and K3's `≈ˢ-paths`, and every ground
--     instance in the programme supplies it. It says nothing about G, about
--     the conditions, or about the extension.
--
--  2. The name kernel: `entry`, `entry-inj`, `entry-isKPair`, `kpair-unique`,
--     `Child`, `child-entry`. All six are K3 THEOREMS, proved from the ground's
--     regularity alone: NameKernel.agda:204, :321, :332, :368, and
--     NameSupport.agda:486. None mentions a condition or a filter.
--
--  3. The poset side: `carrierᶠ`, `_≼ᶜ_`, `order`, `≼-reading`, `IsNameᴾ`,
--     `child-nameᴾ`. Five are K5's own PosetSide telescope
--     (K5/Structures.agda:777-784). The sixth, `≼-reading`, is the only genuine
--     RESTRICTION this file adds: it asks that the abstract order be the one
--     read off a coded order graph. At the coded completion it is `refl`,
--     because `_≼ᴵ_` IS `refinesΔ order` there (CodedCompletion.agda:218-219)
--     and the notion's `_≼_` is that at :241. That no CONCRETE forcing notion
--     is built anywhere yet is obstruction O4 and is K8's, a fact about the
--     programme rather than about this telescope.
--
--  4. The value relation: `G`, `_≈[G]_`, `_∈[G]_`, `‖Active‖`, `active-spec`,
--     `∈-unfold`, `entry-value`, `≈-refl`, `≈-sym`, `∈-congˡ`, `∈-congʳ`. K3
--     defines and proves every one of them at an ARBITRARY `G : Sub`
--     (Valuation.agda:245-475); `active-spec` and `∈-unfold` are `refl` there,
--     being the two defining equations. They do not ASSUME anything: they pin
--     the two abstract relations down to K3's, which is the opposite of a
--     poison parameter, and without them nothing below is provable at all.
--     `≈-refl` is worth naming separately, because it is what refutes the
--     degenerate instantiation `_≈[G]_ := λ _ _ → ⊥`: that assignment satisfies
--     `∈-unfold` and `active-spec` and makes `pair-mem` vacuously true, and it
--     is `≈-refl` that has no inhabitant there and `pair-left`/`pair-right`
--     below that turn the failure into a visible one.
--
--  5. Track A's name calculus: `entryBound`, `entryBound-spec`, `mk`,
--     `mk-spec`, `mk-name`. Track A's stated exports, taken as variables under
--     ruling D4 and IN FLIGHT at the time this file was written. This is the
--     one row of the audit whose inhabitant is not yet on disk, and the seam
--     probe K6/ElementaryAtNames.agda is what settles it.
--
--  6. Two ground terms and three of their laws: `pairOf`, `pairOf-spec`, `⋃ᴳ`,
--     `⋃ᴳ-in`, `support-bound`. NameKernel.agda:204-207 and
--     NameSupport.agda:444-450, :465. They cost ground Pairing, ground Union
--     and one description operator each, all spent upstream.
--
--  7. Nothing else. The three poset laws `≼ᶜ-refl`, `≼ᶜ-trans` and
--     `inhabitedᶜ` that K5's PosetSide carries are NOT in this telescope: an
--     earlier draft took them so that K2's isFilter record could be named
--     here, and rule 13 removed them when the corollary moved to the seam
--     probe, where K5's own isFilter is already in scope.
--
-- WHAT IS NOT IN THE TELESCOPE, and the measured form of the claim: the string
-- `WellFounded`, the token `Acc` and the qualifier `WFI.` each occur 0 times in
-- this file with comments stripped, telescope included; no parameter asserts
-- anything about G; and the only two hypotheses on G in the whole file,
-- `Upward` and `Directed`, are explicit ARGUMENTS of the two theorems that
-- spend them and are visible in those signatures.
--
-- ---------------------------------------------------------------------
-- WHAT IS NOT HERE
-- ---------------------------------------------------------------------
--
-- No LEM, no genericity, no truth lemma, no forcing relation, no atomic graph
-- (O1), no image datum (O3), no `Uof`, no `ext-surjective`, no Boolean side.
-- The ground's own axioms appear only through the four derived terms `pairOf`,
-- `⋃ᴳ`, `entryBound` and `mk`, so the ledger row for this track is ground
-- Pairing plus ground Union plus ground Separation, all spent upstream, and
-- nothing classical.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT

module K6.Elementary {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula ; var ; _∈̇_ ; _∧̇_ ; ⊤̇ ; ∃̇_ )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
open import Cubical.Data.Sigma using ( _×_ ; Σ≡Prop )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open At S id using ( _⊨_ )

open import CodedVocabulary 𝒮
  using ( isKPairΔ ; refinesΔ ; prAtˢ ; orderAtˢ ; sepAt ; sepAt-reading )

-- K3's conditions, Valuation.agda:121-122 verbatim. It is a definition of that
-- file rather than of any module inside it, so writing it here costs no module
-- application and the seam probe's argument slots match definitionally.

Conditions : S → Type ℓ
Conditions c = Σ[ p ∈ S ] ⟨ p ∈ˢ c ⟩

module Build
  -- The ground's equality realised as a host path. K5 spine.
  (paths         : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  -- The name kernel. K5/Structures.agda:209-217, plus the two facts about the
  -- entry that K3 proves at NameKernel.agda:321 and :332.
  (entry         : S → S → S)
  (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
  (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
  (Child         : S → S → Type ℓ)
  (child-entry   : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  -- The poset side. K5/Structures.agda:777-784, plus the coded order graph the
  -- abstract order is read off, CodedCompletion.agda:214-219.
  (carrierᶠ      : S)
  (_≼ᶜ_          : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (order         : S)
  (≼-reading     : (p q : Conditions carrierᶠ)
                 → (p ≼ᶜ q) ≡ refinesΔ order (fst p) (fst q))
  (IsNameᴾ       : S → Ω)
  (child-nameᴾ   : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  -- The extension structure at one G, flat. K5/Structures.agda:263-300,
  -- Valuation.agda:249-295 and :434-436.
  (G             : Conditions carrierᶠ → Ω)
  (_≈[G]_ _∈[G]_ : S → S → Ω)
  (‖Active‖      : S → S → Ω)
  (active-spec   : (x n : S) → ‖Active‖ x n
                 ≡ ( ∥ Σ[ p ∈ S ] Σ[ hp ∈ ⟨ p ∈ˢ carrierᶠ ⟩ ]
                         (⟨ entry x p ∈ˢ n ⟩ × ⟨ G (p , hp) ⟩) ∥₁ , PT.squash₁ ))
  (∈-unfold      : (m n : S) → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
  (entry-value   : (n x p : S) (hp : ⟨ p ∈ˢ carrierᶠ ⟩) → ⟨ G (p , hp) ⟩
                 → ⟨ entry x p ∈ˢ n ⟩ → ⟨ x ∈[G] n ⟩)
  (≈-refl        : (m : S) → ⟨ m ≈[G] m ⟩)
  (≈-sym         : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩)
  (∈-congˡ       : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩)
  (∈-congʳ       : {m n n' : S} → ⟨ n ≈[G] n' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m ∈[G] n' ⟩)
  -- Track A's ground-side name calculus, taken as variables under ruling D4.
  (entryBound      : S → S)
  (entryBound-spec : (D e : S) → (e ∈ˢ entryBound D)
                   ≡ ⋁ S (λ x → (x ∈ˢ D)
                        ⊓ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry x p))))
  (mk              : S → Formula S 1 → S)
  (mk-spec         : (bound : S) (θ : Formula S 1) (e : S)
                   → (e ∈ˢ mk bound θ) ≡ ((e ∈ˢ bound) ⊓ ((e ∷ []) ⊨ θ)))
  (mk-name         : (bound : S) (θ : Formula S 1)
                   → ((e : S) → ⟨ e ∈ˢ mk bound θ ⟩
                      → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
                           ((e ≡ entry x p)
                            × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
                   → ⟨ IsNameᴾ (mk bound θ) ⟩)
  -- Two ground-side terms, sealed where they are defined and therefore opaque
  -- here as well: a variable cannot unfold. NameKernel.agda:204-207 and
  -- NameSupport.agda:444-450, :465.
  (pairOf        : S → S → S)
  (pairOf-spec   : (a b x : S) → (x ∈ˢ pairOf a b) ≡ ((x ≈ˢ a) ⊔ (x ≈ˢ b)))
  (⋃ᴳ            : S → S)
  (⋃ᴳ-in         : (a y x : S) → ⟨ y ∈ˢ a ⟩ → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ ⋃ᴳ a ⟩)
  (support-bound : (n x b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ x ∈ˢ ⋃ᴳ (⋃ᴳ n) ⟩)
  where

  ------------------------------------------------------------------------------
  -- The extension structure, rebuilt from the flat spine
  ------------------------------------------------------------------------------

  -- K5/Structures.agda:263-264 and :285-291, written out rather than obtained
  -- by applying K5.Structures, which no K6 file outside a seam probe does. The
  -- record is built here rather than the field types being transcribed flat,
  -- because a transcription of `Pairing` or `Union` is exactly the kind of
  -- retyping rule 8 exists to forbid: the two obligations below ARE the
  -- profile's own types, applied to this structure, and nothing is restated.

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNameᴾ n ⟩

  nm : Nm → S
  nm σ = fst σ

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNameᴾ n))

  structureᴱ : ZFStructure (hPropAlgebra ℓ)
  structureᴱ = record
    { S      = Nm
    ; isSetS = isSetNm
    ; _≈ˢ_   = λ σ τ → nm σ ≈[G] nm τ
    ; _∈ˢ_   = λ σ τ → nm σ ∈[G] nm τ }

  Cond : Type ℓ
  Cond = Conditions carrierᶠ

  ------------------------------------------------------------------------------
  -- Small bridges
  ------------------------------------------------------------------------------

  -- The ground's equality is a host path, by the spine's `paths`. Both
  -- directions are used: the entry decomposition arrives as a `≈ˢ` and the
  -- kernel's injectivity is stated at `≡`.

  ≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈→≡ {x} {y} h = subst ⟨_⟩ (paths x y) h

  ≡→≈ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
  ≡→≈ {x} {y} h = subst ⟨_⟩ (sym (paths x y)) h

  -- An active entry, as data. This is K3's `Active` (Valuation.agda:245-247)
  -- spelled out, and `active-spec` is its defining equation, which is `refl` at
  -- the instance. The truncation is K3's and is never eliminated into data.

  ActiveAt : S → S → Type ℓ
  ActiveAt x n =
    Σ[ p ∈ S ] Σ[ hp ∈ ⟨ p ∈ˢ carrierᶠ ⟩ ] (⟨ entry x p ∈ˢ n ⟩ × ⟨ G (p , hp) ⟩)

  active-out : (x n : S) → ⟨ ‖Active‖ x n ⟩ → ∥ ActiveAt x n ∥₁
  active-out x n h = subst ⟨_⟩ (active-spec x n) h

  active-in : (x n : S) → ∥ ActiveAt x n ∥₁ → ⟨ ‖Active‖ x n ⟩
  active-in x n h = subst ⟨_⟩ (sym (active-spec x n)) h

  ∈-out : (m n : S) → ⟨ m ∈[G] n ⟩
        → ∥ Σ[ y ∈ S ] (⟨ ‖Active‖ y n ⟩ × ⟨ m ≈[G] y ⟩) ∥₁
  ∈-out m n h = subst ⟨_⟩ (∈-unfold m n) h

  ∈-in : (m n : S) → ∥ Σ[ y ∈ S ] (⟨ ‖Active‖ y n ⟩ × ⟨ m ≈[G] y ⟩) ∥₁
       → ⟨ m ∈[G] n ⟩
  ∈-in m n h = subst ⟨_⟩ (sym (∈-unfold m n)) h

  -- The coded reading of "the entry of x at b is a member of a". `refinesΔ` is
  -- CodedVocabulary's order reader (CodedVocabulary.agda:144-145), and it is
  -- the same gadget whether the ambient set is an order graph or a name: it
  -- says that SOME member of the set is the Kuratowski pair. Determinacy, in
  -- the form of `kpair-unique`, is what turns that back into the entry itself.

  entry→refines : (a x b : S) → ⟨ entry x b ∈ˢ a ⟩ → ⟨ refinesΔ a x b ⟩
  entry→refines a x b h = ∣ entry x b , h , entry-isKPair x b ∣₁

  refines→entry : (a x b : S) → ⟨ refinesΔ a x b ⟩ → ⟨ entry x b ∈ˢ a ⟩
  refines→entry a x b = PT.rec (snd (entry x b ∈ˢ a))
    (λ { (z , hz , hk) → subst (λ w → ⟨ w ∈ˢ a ⟩) (kpair-unique z x b hk) hz })

  -- Entries of a Track A bound, in both directions.

  bound-in : (D x p : S) → ⟨ x ∈ˢ D ⟩ → ⟨ p ∈ˢ carrierᶠ ⟩
           → ⟨ entry x p ∈ˢ entryBound D ⟩
  bound-in D x p hx hp = subst ⟨_⟩ (sym (entryBound-spec D (entry x p)))
    ∣ x , hx , ∣ p , hp , ≡→≈ refl ∣₁ ∣₁

  bound-out : (D e : S) → ⟨ e ∈ˢ entryBound D ⟩
            → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
                 ((e ≡ entry x p) × (⟨ x ∈ˢ D ⟩ × ⟨ p ∈ˢ carrierᶠ ⟩)) ∥₁
  bound-out D e h = PT.rec PT.squash₁
    (λ { (x , hx , inner) →
           PT.map (λ { (p , hp , hq) → x , p , ≈→≡ hq , hx , hp }) inner })
    (subst ⟨_⟩ (entryBound-spec D e) h)

  ------------------------------------------------------------------------------
  -- PAIRING
  ------------------------------------------------------------------------------

  -- The name. Every condition weights both entries, which is `checkᴾ`'s own
  -- convention on the poset side (StandardNames.agda:13-19) and the reason the
  -- field costs no more than positivity: a filter's mere inhabitedness already
  -- activates an entry that is present at every condition. The `⊤̇` cut is there
  -- only because Track A's name certificate is stated for `mk`.

  pairCode : S → S → S
  pairCode m n = mk (entryBound (pairOf m n)) ⊤̇

  pair-bound : (m n e : S) → (e ∈ˢ pairCode m n) ≡ (e ∈ˢ entryBound (pairOf m n))
  pair-bound m n e = mk-spec (entryBound (pairOf m n)) ⊤̇ e ∙ trim
    where
      trim : ((e ∈ˢ entryBound (pairOf m n)) ⊓ ((e ∷ []) ⊨ ⊤̇))
           ≡ (e ∈ˢ entryBound (pairOf m n))
      trim = ⇔toPath fst (λ h → h , (λ z → z))

  -- An entry is active in the pair name exactly when its subname is one of the
  -- two, and the backward half is where positivity is spent and the ONLY place
  -- any hypothesis on G is spent in the whole of Pairing.

  pair-active-out : (m n y : S) → ⟨ ‖Active‖ y (pairCode m n) ⟩
                  → ⟨ y ∈ˢ pairOf m n ⟩
  pair-active-out m n y h = PT.rec (snd (y ∈ˢ pairOf m n))
    (λ { (p , hp , hmem , _) → PT.rec (snd (y ∈ˢ pairOf m n))
       (λ { (x , p' , eq , hx , _) →
              subst (λ w → ⟨ w ∈ˢ pairOf m n ⟩) (sym (fst (entry-inj eq))) hx })
       (bound-out (pairOf m n) (entry y p)
          (subst ⟨_⟩ (pair-bound m n (entry y p)) hmem)) })
    (active-out y (pairCode m n) h)

  pair-active-in : ⟨ ⋁ Cond G ⟩ → (m n y : S) → ⟨ y ∈ˢ pairOf m n ⟩
                 → ⟨ ‖Active‖ y (pairCode m n) ⟩
  pair-active-in pos m n y hy = active-in y (pairCode m n)
    (PT.map (λ { ((p , hp) , hG) →
                   p , hp
                 , subst ⟨_⟩ (sym (pair-bound m n (entry y p)))
                         (bound-in (pairOf m n) y p hy hp)
                 , hG })
            pos)

  -- THE CONTENT OF PAIRING. What the name contains, in both directions, stated
  -- as a universal property of the value membership and never as an equation
  -- naming the constructed set (rule 7).

  pair-mem : ⟨ ⋁ Cond G ⟩ → (m n χ : S)
           → (χ ∈[G] pairCode m n) ≡ ((χ ≈[G] m) ⊔ (χ ≈[G] n))
  pair-mem pos m n χ = ⇔toPath fwd bwd
    where
      leftIn : ⟨ m ∈ˢ pairOf m n ⟩
      leftIn = subst ⟨_⟩ (sym (pairOf-spec m n m)) ∣ inl (≡→≈ refl) ∣₁

      rightIn : ⟨ n ∈ˢ pairOf m n ⟩
      rightIn = subst ⟨_⟩ (sym (pairOf-spec m n n)) ∣ inr (≡→≈ refl) ∣₁

      fwd : ⟨ χ ∈[G] pairCode m n ⟩ → ⟨ (χ ≈[G] m) ⊔ (χ ≈[G] n) ⟩
      fwd h = PT.rec PT.squash₁
        (λ { (y , ha , he) → PT.map
           (λ { (inl q) → inl (subst (λ w → ⟨ χ ≈[G] w ⟩) (≈→≡ q) he)
              ; (inr q) → inr (subst (λ w → ⟨ χ ≈[G] w ⟩) (≈→≡ q) he) })
           (subst ⟨_⟩ (pairOf-spec m n y) (pair-active-out m n y ha)) })
        (∈-out χ (pairCode m n) h)

      bwd : ⟨ (χ ≈[G] m) ⊔ (χ ≈[G] n) ⟩ → ⟨ χ ∈[G] pairCode m n ⟩
      bwd h = ∈-in χ (pairCode m n) (PT.map
        (λ { (inl e) → m , pair-active-in pos m n m leftIn , e
           ; (inr e) → n , pair-active-in pos m n n rightIn , e })
        h)

  -- The name certificate. A member of the pair name is an entry whose subname
  -- is one of the two given names, so it is a name.

  pair-valid : (σ τ : Nm) → ⟨ IsNameᴾ (pairCode (nm σ) (nm τ)) ⟩
  pair-valid σ τ = mk-name (entryBound (pairOf (nm σ) (nm τ))) ⊤̇ decomp
    where
      inD : (x : S) → ⟨ x ∈ˢ pairOf (nm σ) (nm τ) ⟩ → ⟨ IsNameᴾ x ⟩
      inD x h = PT.rec (snd (IsNameᴾ x))
        (λ { (inl e) → subst (λ w → ⟨ IsNameᴾ w ⟩) (sym (≈→≡ e)) (snd σ)
           ; (inr e) → subst (λ w → ⟨ IsNameᴾ w ⟩) (sym (≈→≡ e)) (snd τ) })
        (subst ⟨_⟩ (pairOf-spec (nm σ) (nm τ) x) h)

      decomp : (e : S) → ⟨ e ∈ˢ pairCode (nm σ) (nm τ) ⟩
             → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
                  ((e ≡ entry x p) × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁
      decomp e h = PT.map
        (λ { (x , p , eq , hx , hp) → x , p , eq , hp , inD x hx })
        (bound-out (pairOf (nm σ) (nm τ)) e
           (subst ⟨_⟩ (pair-bound (nm σ) (nm τ) e) h))

  pairNm : Nm → Nm → Nm
  pairNm σ τ = pairCode (nm σ) (nm τ) , pair-valid σ τ

  -- THE FIELD. One line out of the content lemma, through the profile's own
  -- specification-to-biconditional bridge (OrdinaryProfile.agda:43-47).

  hasPairᴾ : ⟨ ⋁ Cond G ⟩ → OrdinaryProfile.Pairing structureᴱ
  hasPairᴾ pos a b =
    ∣ pairNm a b
    , OrdinaryProfile.spec-to-iff structureᴱ (pairNm a b)
        (λ x → (nm x ≈[G] nm a) ⊔ (nm x ≈[G] nm b))
        (λ x → pair-mem pos (nm a) (nm b) (nm x))
    ∣₁

  -- Positive controls against the degenerate witness: the pair really does
  -- contain both of its arguments. A name whose value is empty cannot satisfy
  -- either of these, so together with `pair-mem` they pin the content down.

  pair-left : ⟨ ⋁ Cond G ⟩ → (m n : S) → ⟨ m ∈[G] pairCode m n ⟩
  pair-left pos m n =
    subst ⟨_⟩ (sym (pair-mem pos m n m)) ∣ inl (≈-refl m) ∣₁

  pair-right : ⟨ ⋁ Cond G ⟩ → (m n : S) → ⟨ n ∈[G] pairCode m n ⟩
  pair-right pos m n =
    subst ⟨_⟩ (sym (pair-mem pos m n n)) ∣ inr (≈-refl n) ∣₁

  ------------------------------------------------------------------------------
  -- UNION
  ------------------------------------------------------------------------------

  -- The separation class, as a variable-indexed formula with the name, the
  -- order graph and the carrier frozen into constant slots by K2's `sepAt`
  -- (CodedVocabulary.agda:541-547), which is the only way to do it: the tree
  -- has no substitution, so a con-parameterized formula cannot be nested under
  -- a binder.
  --
  -- The five binders, outermost first, are χ, r, y, p, q; the four constant
  -- slots are e, N, O, C. Inside the binders the environment therefore reads
  -- (q ∷ p ∷ y ∷ r ∷ χ ∷ e ∷ N ∷ O ∷ C ∷ []) and the indices below name it.

  private
    sq sp sy sr sχ se sN sO sC : Fin 9
    sq = zero
    sp = suc zero
    sy = suc (suc zero)
    sr = suc (suc (suc zero))
    sχ = suc (suc (suc (suc zero)))
    se = suc (suc (suc (suc (suc zero))))
    sN = suc (suc (suc (suc (suc (suc zero)))))
    sO = suc (suc (suc (suc (suc (suc (suc zero))))))
    sC = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

  unionBody : Formula S 9
  unionBody =
       prAtˢ se sχ sr
    ∧̇ ((var sr ∈̇ var sC)
    ∧̇ ((var sp ∈̇ var sC)
    ∧̇ ((var sq ∈̇ var sC)
    ∧̇ ( orderAtˢ sN sy sq
    ∧̇ ( orderAtˢ sy sχ sp
    ∧̇ ( orderAtˢ sO sr sp
    ∧̇   orderAtˢ sO sr sq ))))))

  unionFo : Formula S 4
  unionFo = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ unionBody))))

  unionΔ : S → S → S → S → Ω
  unionΔ e N O C =
    ⋁ S (λ χ → ⋁ S (λ r → ⋁ S (λ y → ⋁ S (λ p → ⋁ S (λ q →
        isKPairΔ e χ r
      ⊓ ((r ∈ˢ C)
      ⊓ ((p ∈ˢ C)
      ⊓ ((q ∈ˢ C)
      ⊓ ( refinesΔ N y q
      ⊓ ( refinesΔ y χ p
      ⊓ ( refinesΔ O r p
      ⊓   refinesΔ O r q )))))))))))

  -- The reading, by refl, because every sub-reading in CodedVocabulary is by
  -- refl and the host predicate above is the literal unfolding. A reading
  -- theorem proved by refl cannot catch a formula that is wrong in the same
  -- way its host predicate is wrong, so the discrimination is done by the two
  -- content theorems below and by the break files, not here.

  unionFo-reading : (e N O C : S)
                  → ((e ∷ N ∷ O ∷ C ∷ []) ⊨ unionFo) ≡ unionΔ e N O C
  unionFo-reading e N O C = refl

  unionFo1 : S → Formula S 1
  unionFo1 N = sepAt unionFo (N ∷ order ∷ carrierᶠ ∷ [])

  unionFo1-reading : (N e : S)
                   → ((e ∷ []) ⊨ unionFo1 N) ≡ unionΔ e N order carrierᶠ
  unionFo1-reading N e = sepAt-reading unionFo (N ∷ order ∷ carrierᶠ ∷ []) e

  -- The bound. A grandchild of n sits five unions up: the child y lands in
  -- ⋃² n by support-bound, its own entry lands one union higher, and a second
  -- support-bound places the grandchild two above that.

  unionBound : S → S
  unionBound n = ⋃ᴳ (⋃ᴳ (⋃ᴳ (⋃ᴳ (⋃ᴳ n))))

  grandchild-bound : (n y χ p q : S) → ⟨ entry y q ∈ˢ n ⟩ → ⟨ entry χ p ∈ˢ y ⟩
                   → ⟨ χ ∈ˢ unionBound n ⟩
  grandchild-bound n y χ p q hy hχ =
    support-bound (⋃ᴳ (⋃ᴳ (⋃ᴳ n))) χ p
      (⋃ᴳ-in (⋃ᴳ (⋃ᴳ n)) y (entry χ p) (support-bound n y q hy) hχ)

  unionCode : S → S
  unionCode n = mk (entryBound (unionBound n)) (unionFo1 n)

  union-spec : (n e : S) → (e ∈ˢ unionCode n)
             ≡ ((e ∈ˢ entryBound (unionBound n)) ⊓ unionΔ e n order carrierᶠ)
  union-spec n e =
    mk-spec (entryBound (unionBound n)) (unionFo1 n) e
    ∙ cong ((e ∈ˢ entryBound (unionBound n)) ⊓_) (unionFo1-reading n e)

  -- The witness package of the separation class, as data under one truncation.

  UnionWit : S → S → Type ℓ
  UnionWit n e =
    Σ[ χ ∈ S ] Σ[ r ∈ S ] Σ[ y ∈ S ] Σ[ p ∈ S ] Σ[ q ∈ S ]
      ((e ≡ entry χ r)
       × (⟨ r ∈ˢ carrierᶠ ⟩ × (⟨ p ∈ˢ carrierᶠ ⟩ × (⟨ q ∈ˢ carrierᶠ ⟩
       × (⟨ entry y q ∈ˢ n ⟩ × (⟨ entry χ p ∈ˢ y ⟩
       × (⟨ refinesΔ order r p ⟩ × ⟨ refinesΔ order r q ⟩)))))))

  unionΔ-out : (n e : S) → ⟨ unionΔ e n order carrierᶠ ⟩ → ∥ UnionWit n e ∥₁
  unionΔ-out n e =
    PT.rec PT.squash₁ (λ { (χ , h1) →
    PT.rec PT.squash₁ (λ { (r , h2) →
    PT.rec PT.squash₁ (λ { (y , h3) →
    PT.rec PT.squash₁ (λ { (p , h4) →
    PT.map (λ { (q , hk , hrC , hpC , hqC , hN , hy , hrp , hrq) →
                  χ , r , y , p , q
                , kpair-unique e χ r hk
                , hrC , hpC , hqC
                , refines→entry n y q hN
                , refines→entry y χ p hy
                , hrp , hrq })
      h4 }) h3 }) h2 }) h1 })

  unionΔ-in : (n e : S) → UnionWit n e → ⟨ unionΔ e n order carrierᶠ ⟩
  unionΔ-in n e (χ , r , y , p , q , eq , hrC , hpC , hqC , hN , hy , hrp , hrq) =
    ∣ χ , ∣ r , ∣ y , ∣ p , ∣ q
      , subst (λ w → ⟨ isKPairΔ w χ r ⟩) (sym eq) (entry-isKPair χ r)
      , hrC , hpC , hqC
      , entry→refines n y q hN
      , entry→refines y χ p hy
      , hrp , hrq ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

  -- The name certificate. A member of the union name is an entry whose subname
  -- is a child of a child of n, so two applications of the hereditary clause
  -- certify it.

  union-valid : (τ : Nm) → ⟨ IsNameᴾ (unionCode (nm τ)) ⟩
  union-valid τ =
    mk-name (entryBound (unionBound (nm τ))) (unionFo1 (nm τ)) decomp
    where
      decomp : (e : S) → ⟨ e ∈ˢ unionCode (nm τ) ⟩
             → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
                  ((e ≡ entry x p) × (⟨ p ∈ˢ carrierᶠ ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁
      decomp e h = PT.map
        (λ { (χ , r , y , p , q , eq , hrC , _ , _ , hN , hy , _ , _) →
               χ , r , eq , hrC
             , child-nameᴾ y
                 (child-nameᴾ (nm τ) (snd τ) y (child-entry y q (nm τ) hN))
                 χ (child-entry χ p y hy) })
        (unionΔ-out (nm τ) e (snd (subst ⟨_⟩ (union-spec (nm τ) e) h)))

  unionNm : Nm → Nm
  unionNm τ = unionCode (nm τ) , union-valid τ

  -- The two filter laws, flat, each an explicit argument of the direction that
  -- spends it. Neither is a module parameter, so the conditionality ledger of
  -- this track is its signatures (ruling D4).

  Upward : Type ℓ
  Upward = (p q : Cond) → ⟨ G p ⟩ → ⟨ p ≼ᶜ q ⟩ → ⟨ G q ⟩

  Directed : Type ℓ
  Directed = (p q : Cond) → ⟨ G p ⟩ → ⟨ G q ⟩
           → ⟨ ⋁ Cond (λ r → G r ⊓ ((r ≼ᶜ p) ⊓ (r ≼ᶜ q))) ⟩

  -- THE FORWARD DIRECTION, and the only place `upward` is spent. The weight of
  -- the member entry refines both the parent's weight and the child's, so both
  -- of those weights are in G as soon as the member's own weight is.

  union-out : Upward → (τ : Nm) (χ : S) → ⟨ χ ∈[G] unionCode (nm τ) ⟩
            → ⟨ ⋁ Nm (λ y → (nm y ∈[G] nm τ) ⊓ (χ ∈[G] nm y)) ⟩
  union-out up τ χ h = PT.rec PT.squash₁
    (λ { (w , ha , he) → PT.rec PT.squash₁
       (λ { (c , hc , hmem , hG) → PT.rec PT.squash₁
          (λ { (χ' , r , y , p , q , eq , hrC , hpC , hqC , hN , hy , hrp , hrq) →
                 let cr  : (c , hc) ≡ (r , hrC)
                     cr  = Σ≡Prop (λ x → snd (x ∈ˢ carrierᶠ)) (snd (entry-inj eq))
                     hGr : ⟨ G (r , hrC) ⟩
                     hGr = subst (λ k → ⟨ G k ⟩) cr hG
                     hGp : ⟨ G (p , hpC) ⟩
                     hGp = up (r , hrC) (p , hpC) hGr
                             (subst ⟨_⟩ (sym (≼-reading (r , hrC) (p , hpC))) hrp)
                     hGq : ⟨ G (q , hqC) ⟩
                     hGq = up (r , hrC) (q , hqC) hGr
                             (subst ⟨_⟩ (sym (≼-reading (r , hrC) (q , hqC))) hrq)
                     hyn : ⟨ IsNameᴾ y ⟩
                     hyn = child-nameᴾ (nm τ) (snd τ) y (child-entry y q (nm τ) hN)
                     hχ' : ⟨ χ ≈[G] χ' ⟩
                     hχ' = subst (λ v → ⟨ χ ≈[G] v ⟩) (fst (entry-inj eq)) he
                 in ∣ (y , hyn)
                    , entry-value (nm τ) y q hqC hGq hN
                    , ∈-congˡ (≈-sym hχ') (entry-value y χ' p hpC hGp hy)
                    ∣₁ })
          (unionΔ-out (nm τ) (entry w c)
             (snd (subst ⟨_⟩ (union-spec (nm τ) (entry w c)) hmem))) })
       (active-out w (unionCode (nm τ)) ha) })
    (∈-out χ (unionCode (nm τ)) h)

  -- THE BACKWARD DIRECTION, and the only place `directed` is spent. Both
  -- witnesses arrive at their own weights and the union name has no entry at
  -- either of them; the common refinement is what puts one there.

  union-in : Directed → (τ : Nm) (χ y : S) → ⟨ y ∈[G] nm τ ⟩ → ⟨ χ ∈[G] y ⟩
           → ⟨ χ ∈[G] unionCode (nm τ) ⟩
  union-in dir τ χ y hy hχ = PT.rec (snd (χ ∈[G] unionCode (nm τ)))
    (λ { (y' , hay , ey) → PT.rec (snd (χ ∈[G] unionCode (nm τ)))
       (λ { (q , hqC , hN , hGq) → PT.rec (snd (χ ∈[G] unionCode (nm τ)))
          (λ { (χ' , haχ , eχ) → PT.rec (snd (χ ∈[G] unionCode (nm τ)))
             (λ { (p , hpC , hM , hGp) → PT.rec (snd (χ ∈[G] unionCode (nm τ)))
                (λ { ((r , hrC) , hGr , hrp , hrq) →
                       ∈-congˡ (≈-sym eχ)
                         (entry-value (unionCode (nm τ)) χ' r hrC hGr
                           (subst ⟨_⟩ (sym (union-spec (nm τ) (entry χ' r)))
                             ( bound-in (unionBound (nm τ)) χ' r
                                 (grandchild-bound (nm τ) y' χ' p q hN hM) hrC
                             , unionΔ-in (nm τ) (entry χ' r)
                                 ( χ' , r , y' , p , q , refl
                                 , hrC , hpC , hqC , hN , hM
                                 , subst ⟨_⟩ (≼-reading (r , hrC) (p , hpC)) hrp
                                 , subst ⟨_⟩ (≼-reading (r , hrC) (q , hqC)) hrq ) ))) })
                (dir (p , hpC) (q , hqC) hGp hGq) })
             (active-out χ' y' haχ) })
          (∈-out χ y' (∈-congʳ ey hχ)) })
       (active-out y' (nm τ) hay) })
    (∈-out y (nm τ) hy)

  -- THE CONTENT OF UNION, in the architecture's own spelling over all of S,
  -- with the name-indexed form the profile field needs beside it. The forward
  -- direction produces a NAME and not merely a code, which is what makes the
  -- name-indexed form available at all.

  union-mem : Upward → Directed → (τ : Nm) (χ : S)
            → (χ ∈[G] unionCode (nm τ)) ≡ ⋁ S (λ y → (y ∈[G] nm τ) ⊓ (χ ∈[G] y))
  union-mem up dir τ χ = ⇔toPath
    (λ h → PT.map (λ { (y , hm , hc) → nm y , hm , hc }) (union-out up τ χ h))
    (PT.rec (snd (χ ∈[G] unionCode (nm τ)))
       (λ { (y , hm , hc) → union-in dir τ χ y hm hc }))

  union-memᴺ : Upward → Directed → (τ : Nm) (χ : S)
             → (χ ∈[G] unionCode (nm τ))
             ≡ ⋁ Nm (λ y → (nm y ∈[G] nm τ) ⊓ (χ ∈[G] nm y))
  union-memᴺ up dir τ χ = ⇔toPath (union-out up τ χ)
    (PT.rec (snd (χ ∈[G] unionCode (nm τ)))
       (λ { (y , hm , hc) → union-in dir τ χ (nm y) hm hc }))

  hasUnionᵁᴰ : Upward → Directed → OrdinaryProfile.Union structureᴱ
  hasUnionᵁᴰ up dir a =
    ∣ unionNm a
    , OrdinaryProfile.spec-to-iff structureᴱ (unionNm a)
        (λ x → ⋁ Nm (λ y → (nm y ∈[G] nm a) ⊓ (nm x ∈[G] nm y)))
        (λ x → union-memᴺ up dir a (nm x))
    ∣₁

  ------------------------------------------------------------------------------
  -- Degenerate controls
  ------------------------------------------------------------------------------

  -- The vacuity question, answered at the two degenerate points rather than
  -- argued. A field that only asserts existence can be proved by a witness
  -- whose value is empty, and `pair-mem` alone does not exclude that: at an
  -- empty G both sides of it are false and the path holds for the wrong
  -- reason. So the two ends are pinned down separately.
  --
  -- At the EMPTY G, nothing is a value member of anything, so the pair name's
  -- value is empty and `pair-left` is not derivable. That is not a defect: it
  -- is the measurement that `hasPairᴾ`'s hypothesis is load bearing, since the
  -- hypothesis is exactly the statement that G is not empty.

  empty-G-no-member : ((c : Cond) → ⟨ G c ⟩ → ⟨ ⊥ ⟩)
                    → (m n : S) → ⟨ m ∈[G] n ⟩ → ⟨ ⊥ ⟩
  empty-G-no-member noc m n h = PT.rec (snd ⊥)
    (λ { (y , ha , _) → PT.rec (snd ⊥)
       (λ { (p , hp , _ , hG) → noc (p , hp) hG })
       (active-out y n ha) })
    (∈-out m n h)

  pair-degenerate : ((c : Cond) → ⟨ G c ⟩ → ⟨ ⊥ ⟩)
                  → (m n χ : S) → ⟨ χ ∈[G] pairCode m n ⟩ → ⟨ ⊥ ⟩
  pair-degenerate noc m n χ = empty-G-no-member noc χ (pairCode m n)

  -- At the ONE POINT poset, both of Union's filter laws collapse into
  -- Pairing's single one, so `hasUnionᵁᴰ` is available there from positivity
  -- alone. This is the check that discriminates a union construction which
  -- secretly asks for more than a filter: the trivial notion is the one place
  -- where the extension provably is the ground, and a construction whose
  -- hypotheses do not degenerate there has a hypothesis it should not have.
  -- The exit example itself is Track J's, under decision D8; this is only its
  -- hypothesis half, which is the half this track owns.

  one-point-laws : ((c d : Cond) → c ≡ d) → ((c : Cond) → ⟨ c ≼ᶜ c ⟩)
                 → ⟨ ⋁ Cond G ⟩ → Upward × Directed
  one-point-laws one refl≼ pos = up , dir
    where
      up : Upward
      up c d hc _ = subst (λ k → ⟨ G k ⟩) (one c d) hc

      dir : Directed
      dir c d hc hd =
        ∣ c , hc , refl≼ c , subst (λ k → ⟨ c ≼ᶜ k ⟩) (one c d) (refl≼ c) ∣₁

  ------------------------------------------------------------------------------
  -- The architecture's spelling, and where it went
  ------------------------------------------------------------------------------

  -- The architecture states both fields at `isFilter G`, and the corollary
  -- that re-spells them that way is NOT here. It is in the seam probe
  -- K6/ElementaryAtStructures.agda, as `hasPairᶠ` and `hasUnionᶠ`, because
  -- `isFilter` is K2's record over a ForcingNotion and `filter-positive` is
  -- K3's projection out of it (Valuation.agda:195-198 and :225-226): writing
  -- the corollary here would mean rebuilding a ForcingNotion record that two
  -- layers already own, and carrying `≼ᶜ-refl`, `≼ᶜ-trans` and `inhabitedᶜ`
  -- as three parameters used for nothing else. Rule 13. The probe's version is
  -- also the stronger evidence, since it runs through K5's own isFilter rather
  -- than through a local copy of it.
