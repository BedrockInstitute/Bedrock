# K0 partial atomic tables and internal table images

Date: 2026-09-08. Repository source baseline: `ae36ae02`. Status: two safe probe modules checked; K0 remains open. This follows the [internal-name probes](k0-internal-names-probes-2026-09.md). No production source or public landmark was changed.

## Checked contracts

`PartialAtomicTables.agda` proves compatibility of downward-closed partial tables by well-founded induction, then constructs their partial union and proves its local equations. It is universe-polymorphic and assumes no LEM or host choice. Its inputs are a well-founded relation, an h-set output carrier, a proposition-valued local step relation and determinacy of that relation. Both coordinates decrease in each recursive dependency; induction on the first coordinate suffices. This is a semantic kernel, not yet an internally set-coded table theorem.

The step interface is a relation on predecessor functions and proposed outputs. There is deliberately no assertion that every host predecessor function has a step output. Relative Boolean completeness only handles internally represented images. An unconditional functional step would demand an additional, unjustified closure theorem. A future internal table adapter must supply step witnesses from actual coded predecessor images. These requirements must remain visible when implementing the general-ground interface.

For a family of compatible tables, union membership merely asserts that some table supplies the entry. The graph is propositionally truncated. Functionality proves that the pair consisting of its Boolean value and graph membership is a proposition. Truncation elimination into this proved proposition returns the unique value, without returning a selected table index. The resulting `joined` record includes downward closure and the step equation. The union's domain universe is the maximum of the family-index and individual-domain levels; there is no resizing claim.

`TableImages.agda` constructs, in actual L under precisely `LEM (ℓ-suc ℓ)`, the set

    image = { b ∈ B | exists x ∈ D: pair(x,b) ∈ T }.

Here T, D and B are supplied internal sets. A concrete finite formula and the checked pair-formula reading theorem justify Separation. Both membership directions and exact predicate equality are proved. This construction needs neither functionality nor totality of T. The additional `Certified` adapter assumes a function whose values lie in B, its entries in T, and agreement of all relevant T entries with that function. It proves equivalence of upper-bound predicates and transfers a supplied internal supremum, comparing only upper bounds in B. It does not assume or prove completeness for arbitrary host families, nor does it construct the recursive table T.

## Bounded internal recursion design

The following is an audited proof plan, not checked Agda. Existing `L.Recursion.Definition` takes graph syntax, adequacy and uniqueness as inputs; it cannot supply atomic definability before those inputs exist. `L.GCH.OmegaRecursion` suffices for the already checked name closure but is not an arbitrary well-founded graph construction.

For an internal closed family C of valid names, construct D = C × C and an internal Boolean carrier B. Define one fixed formula Good(H): H is a single-valued subset of D × B, its domain is downward closed, and each entry obeys a fixed local Step formula. Form internally

    K = { H ∈ P(D × B) | Good(H) }
    T = ⋃ K.

Construct K before using external well-founded induction. The internal Power Set ranges over internal candidate graphs; it does not collect all host partial functions. The checked semantic compatibility/union kernel is intended to prove that this actual T is good, after the formula-reading and set-union adapters have been supplied.

To prove totality, induction gives predecessor values already in T. A nonrecursive step-existence theorem for this internal T supplies b. Prove the internal one-entry extension T ∪ {pair(p,b)} is good. It therefore belongs to K, and its new entry belongs to T. This avoids collecting a host family of inductively chosen graphs and does not use Zorn. Totality, the extension proof, fixed Good syntax and its reading theorem are still unimplemented.

Step existence is required for an internal functional table covering the relevant predecessors. Locality must show agreement of its predecessor values preserves the step relation. An arbitrary host Boolean operation is insufficient: Boolean order and operations need internal codes or fixed formulas with proved adequacy. Suprema must be established for internally coded subsets of B.

For atomic equality, expand the usual recursive clauses so both name coordinates decrease. For e = pair(u,a) ∈ x and f = pair(v,c) ∈ y, use H(u,v) in both halves:

    j_e = sup { c ∧ H(u,v) | pair(v,c) ∈ y }
    k_f = sup { a ∧ H(u,v) | pair(u,a) ∈ x }
    E_H(x,y) = inf { a ⇒ j_e | pair(u,a) ∈ x }
               ∧ inf { c ⇒ k_f | pair(v,c) ∈ y }.

Each displayed image needs a concrete bounded formula and its membership theorem, including Boolean-operation graphs. The checked plain table-image theorem is an initial component; it does not yet construct these weighted or nested images. Repeated children with different weights must remain represented through the original entry indices. Prove image congruence and relative supremum uniqueness to establish locality. No symmetry theorem is assumed to define this expanded step.

After total table existence, prove independence of the chosen closed family by compatibility on overlaps. Existential quantification over internal closed families and tables then yields fixed atomic formulas with adequate, unique values. Membership uses one more internal image of equality values and needs no separate well-founded recursion. Prefer deriving semantic equality from the actual tables and proving its computation law; do not compare it to an independently postulated host recursion whose image admission has never been proved.

Subsequent evidence: the [internal candidate-table probes](k0-internal-candidate-tables-2026-09.md) discharge internal product construction, formula-parametric candidate-family/union construction and the functionality/readout part of the coding bridge. Full Good reading, recursive union goodness and totality below remain pending.

## Next acceptance gates

1. Construct internal products and the fixed Good formula, with exact reading into the partial-table interface and an adapter for internal union. Prove the one-entry extension and WFI totality theorem. A concrete definable finite step can test this machinery without claiming the Boolean instance.
2. Construct weighted/nested Boolean images from coded operations; prove step totality on admitted internal tables and locality. Supply an actual relatively complete coded Boolean instance.
3. Combine with checked L name closure; prove closed-domain independence and fixed equality/membership formula adequacy. Generalize the ground adapters with their explicit set-coding and accessibility contracts.
4. Only then feed these atomic graphs to the shared formula compiler and attained-value Separation backend. Collection/fullness, internal ultrafilter existence and the later model quotient remain separate obligations.

This preserves a single shared semantics for the Boolean and poset interfaces and their certified bridge. It changes neither T3's actual ordinary-model target nor the mandatory general supplied-generic theorem or T4. No host-choice assumption has been added. These local checks do not certify the entire route's final assumption budget.

## Verification and reproducibility

Both final entry points exited 0 in `/tmp/bedrock-k0-probes/extraction/compile-root`:

```text
GHCRTS="-A64m -I0 -M8g" agda src/PartialAtomicTables.agda
GHCRTS="-A64m -I0 -M8g" agda src/TableImages.agda
```

The first final check reused its checked interface; TableImages was copied from the scoped agent's checked tree and checked again against the shared probe dependencies. Both sources retain `--cubical --safe --guardedness`. TableImages imports the exact PairFormulaReading snapshot in the preceding ledger. Dependency source is the repository baseline; probes are copied into its src directory only in a temporary tree. No whole-tree build is claimed. The mathematical audit is stored temporarily at `/tmp/bedrock-k0-probes/atomic-audit/REPORT.md`; its actionable argument and limitations are recorded above. The audit itself is not a formal proof.

Scoped prose and glossary checks and `git diff --check` exited 0. Repository tracked source and copied baseline source were compared byte-for-byte against `ae36ae02`; probe snapshots match the compiled sources and recorded SHA-256 values. Chapter-framework and whole-tree gates were not run because this change only archives temporary probes and design notes.

The exact source snapshots below use text fences for grep and reproducibility, not production module registration.

### PartialAtomicTables.agda

SHA-256: `f3d877ab7989a47bfdb25e385d8c81a9a7f584b86973d7ee07a428af7532bd21`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module PartialAtomicTables {ℓa ℓr ℓb ℓs : Level}
  (A : Type ℓa) (R : A → A → Type ℓr)
  (B : Type ℓb) (setB : isSet B)
  (Step : (x y : A) → ((u v : A) → R u x → R v y → B) → B → hProp ℓs)
  (deterministic : ∀ x y f b c → ⟨ Step x y f b ⟩ → ⟨ Step x y f c ⟩ → b ≡ c) where

open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

record LocalTable (ℓd : Level) : Type (ℓ-max ℓa (ℓ-max ℓr (ℓ-max ℓb (ℓ-max ℓs (ℓ-suc ℓd))))) where
  field
    domain : A → A → hProp ℓd
    down : ∀ x y → ⟨ domain x y ⟩ → ∀ u v → R u x → R v y → ⟨ domain u v ⟩
    value : ∀ x y → ⟨ domain x y ⟩ → B
    equation : ∀ x y p →
      ⟨ Step x y (λ u v ru rv → value u v (down x y p u v ru rv)) (value x y p) ⟩

module WellFoundedTables (wf : WellFounded R) where

  compatible : ∀ {ℓd ℓe} (T : LocalTable ℓd) (U : LocalTable ℓe)
    → ∀ x y (p : ⟨ LocalTable.domain T x y ⟩) (q : ⟨ LocalTable.domain U x y ⟩)
    → LocalTable.value T x y p ≡ LocalTable.value U x y q
  compatible T U = WFI.induction wf
    (λ x below y p q → deterministic x y
      (λ u v ru rv → LocalTable.value U u v (LocalTable.down U x y q u v ru rv)) _ _
      (subst (λ f → ⟨ Step x y f (LocalTable.value T x y p) ⟩)
        (funExt (λ u → funExt (λ v → funExt (λ ru → funExt (λ rv →
          below u ru v (LocalTable.down T x y p u v ru rv) (LocalTable.down U x y q u v ru rv))))))
        (LocalTable.equation T x y p)) (LocalTable.equation U x y q))

  module Union {ℓt ℓd : Level} (I : Type ℓt) (table : I → LocalTable ℓd) where

    domain : A → A → hProp (ℓ-max ℓt ℓd)
    domain x y = ∥ Σ[ i ∈ I ] ⟨ LocalTable.domain (table i) x y ⟩ ∥₁ , PT.squash₁

    Graph : A → A → B → Type (ℓ-max ℓt (ℓ-max ℓd ℓb))
    Graph x y b = ∥ Σ[ i ∈ I ] Σ[ p ∈ ⟨ LocalTable.domain (table i) x y ⟩ ]
      LocalTable.value (table i) x y p ≡ b ∥₁

    functional : ∀ x y b c → Graph x y b → Graph x y c → b ≡ c
    functional x y b c = PT.rec (isPropΠ (λ _ → setB b c))
      (λ { (i , p , eb) → PT.rec (setB b c)
        (λ { (j , q , ec) → sym eb ∙ compatible (table i) (table j) x y p q ∙ ec }) })

    result-is-prop : ∀ x y → isProp (Σ[ b ∈ B ] Graph x y b)
    result-is-prop x y (b , p) (c , q) = Σ≡Prop (λ _ → PT.squash₁) (functional x y b c p q)

    result : ∀ x y → ⟨ domain x y ⟩ → Σ[ b ∈ B ] Graph x y b
    result x y = PT.rec (result-is-prop x y)
      (λ { (i , p) → LocalTable.value (table i) x y p , ∣ i , p , refl ∣₁ })

    value : ∀ x y → ⟨ domain x y ⟩ → B
    value x y p = fst (result x y p)

    down : ∀ x y → ⟨ domain x y ⟩ → ∀ u v → R u x → R v y → ⟨ domain u v ⟩
    down x y p u v ru rv = PT.map
      (λ { (i , q) → i , LocalTable.down (table i) x y q u v ru rv }) p

    agrees : ∀ x y p i q → value x y p ≡ LocalTable.value (table i) x y q
    agrees x y p i q = functional x y _ _ (snd (result x y p)) ∣ i , q , refl ∣₁

    equation : ∀ x y p →
      ⟨ Step x y (λ u v ru rv → value u v (down x y p u v ru rv)) (value x y p) ⟩
    equation x y p = PT.rec
      (snd (Step x y (λ u v ru rv → value u v (down x y p u v ru rv)) (value x y p)))
      (λ { (i , q) → subst ⟨_⟩
        (cong₂ (Step x y)
          (funExt (λ u → funExt (λ v → funExt (λ ru → funExt (λ rv →
            sym (agrees u v (down x y p u v ru rv) i (LocalTable.down (table i) x y q u v ru rv)))))))
          (sym (agrees x y p i q)))
        (LocalTable.equation (table i) x y q) }) p

    joined : LocalTable (ℓ-max ℓt ℓd)
    joined = record { domain = domain; down = down; value = value; equation = equation }
```

### TableImages.agda

SHA-256: `292129bf16be5da9339a05718b2ba459a51d0ea880968a91b5d9a92193206a7f`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module TableImages {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import FOL.ZFModel 𝒮ʟ using ( isZFModel )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ )
open import L.Model {ℓ} lem using ( L⊨ZF )
open import PairFormulaReading {ℓ} using ( reading )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

opaque
  actualL : isZFModel
  actualL = L⊨ZF

module Construction (T D B : S) where

  open isZFModel actualL using ( separate; separate-spec )

  imageFormula : Formula S 1
  imageFormula = ∃̇∈ (con D)
    (∃̇∈ (con T) (prAtL zero (suc zero) (suc (suc zero))))

  image : S
  image = separate B imageFormula

  Table : S → S → Type (ℓ-suc ℓ)
  Table x b = ⟨ prʟ x b ∈ˢ T ⟩

  Occurs : S → Type (ℓ-suc ℓ)
  Occurs b = ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ D ⟩ × Table x b) ∥₁

  formula→occurs : ∀ b → ⟨ (b ∷ []) ⊨ imageFormula ⟩ → Occurs b
  formula→occurs b = PT.map λ { (x , (xD , witnesses)) →
    x , xD , PT.rec (snd (prʟ x b ∈ˢ T))
      (λ { (e , (eT , pair)) →
        subst (λ z → ⟨ z ∈ˢ T ⟩)
          (subst ⟨_⟩
            (reading zero (suc zero) (suc (suc zero)) (e ∷ x ∷ b ∷ [])) pair)
          eT })
      witnesses }

  occurs→formula : ∀ b → Occurs b → ⟨ (b ∷ []) ⊨ imageFormula ⟩
  occurs→formula b = PT.map λ { (x , (xD , pairT)) →
    x , xD , ∣ prʟ x b , pairT , subst ⟨_⟩
      (sym (reading zero (suc zero) (suc (suc zero))
        (prʟ x b ∷ x ∷ b ∷ []))) refl ∣₁ }

  image-out : ∀ b → ⟨ b ∈ˢ image ⟩ → ⟨ b ∈ˢ B ⟩ × Occurs b
  image-out b member with subst ⟨_⟩ (separate-spec B imageFormula b) member
  ... | bB , holds = bB , formula→occurs b holds

  image-in : ∀ b → ⟨ b ∈ˢ B ⟩ → Occurs b → ⟨ b ∈ˢ image ⟩
  image-in b bB occurs = subst ⟨_⟩
    (sym (separate-spec B imageFormula b)) (bB , occurs→formula b occurs)

  image-membership : ∀ b
    → (b ∈ˢ image) ≡ ((b ∈ˢ B) ⊓ (Occurs b , PT.squash₁))
  image-membership b = ⇔toPath (image-out b)
    (λ { (bB , occurs) → image-in b bB occurs })

  module Certified
    (eval : (x : S) → ⟨ x ∈ˢ D ⟩ → S)
    (eval-in-B : (x : S) (xD : ⟨ x ∈ˢ D ⟩) → ⟨ eval x xD ∈ˢ B ⟩)
    (eval-graph : (x : S) (xD : ⟨ x ∈ˢ D ⟩) → Table x (eval x xD))
    (table-agrees : (x : S) (xD : ⟨ x ∈ˢ D ⟩) (b : S)
      → Table x b → b ≡ eval x xD)
    (order : S → S → hProp (ℓ-suc ℓ)) where

    eval-occurs : (x : S) (xD : ⟨ x ∈ˢ D ⟩) → ⟨ eval x xD ∈ˢ image ⟩
    eval-occurs x xD = image-in (eval x xD) (eval-in-B x xD)
      ∣ x , xD , eval-graph x xD ∣₁

    UpperImage : S → Type (ℓ-suc ℓ)
    UpperImage c = (b : S) → ⟨ b ∈ˢ image ⟩ → ⟨ order b c ⟩

    UpperEval : S → Type (ℓ-suc ℓ)
    UpperEval c = (x : S) (xD : ⟨ x ∈ˢ D ⟩) → ⟨ order (eval x xD) c ⟩

    upper-image→eval : ∀ c → UpperImage c → UpperEval c
    upper-image→eval c upper x xD = upper (eval x xD) (eval-occurs x xD)

    upper-eval→image : ∀ c → UpperEval c → UpperImage c
    upper-eval→image c upper b member = PT.rec (snd (order b c))
      (λ { (x , (xD , graph)) →
        subst (λ z → ⟨ order z c ⟩) (sym (table-agrees x xD b graph))
          (upper x xD) })
      (snd (image-out b member))

    upper-equivalence : ∀ c →
      (UpperImage c → UpperEval c) × (UpperEval c → UpperImage c)
    upper-equivalence c = upper-image→eval c , upper-eval→image c

    transfer-supremum : ∀ j → ⟨ j ∈ˢ B ⟩ → UpperImage j
      → ((c : S) → ⟨ c ∈ˢ B ⟩ → UpperImage c → ⟨ order j c ⟩)
      → ⟨ j ∈ˢ B ⟩ × UpperEval j ×
        ((c : S) → ⟨ c ∈ˢ B ⟩ → UpperEval c → ⟨ order j c ⟩)
    transfer-supremum j jB upper least =
      jB , upper-image→eval j upper ,
      λ c cB bound → least c cB (upper-eval→image c bound)
```
