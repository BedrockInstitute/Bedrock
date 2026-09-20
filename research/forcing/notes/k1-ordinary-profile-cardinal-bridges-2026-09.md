# K1 ordinary profile, cardinal bridges and the CH and GCH sentences

Date: 2026-09-11. Source baseline: `cbd1510e`. Status: K1 complete, INCLUDING the L re-expression of GCH, which section 5 of an earlier revision of this record listed as not delivered. All five comparison theorems are proved and the closure theorem composes them; see section 5. This record follows the K0 convention: all proof work stays in temporary probes under a task-specific compile root, with checked snapshots recorded here. No repository source file is changed, because the separate trilingual writing phase owns `src/` on `main`.

## 1. Why K1 exists

The [K0 final representation decision](k0-representation-decision-2026-09.md) closes with one instruction: "The next bounded task is K1: implement shared ordinary ZFC/CH/GCH interpretations and equality coherence, separate the transitive realization contract, then adapt existing L results without changing their statements or LEM budget."

The mathematical reason is the gap the [interface audit](forcing-bedrock-interface-audit-2026-09.md) section 2 records. The existing `isZFModel` (`src/FOL/ZFModel.lagda.md:217-230`) is not first-order ZF. Its regularity field is host `WellFounded _∈ᵗ_`, external well foundedness. Its Infinity carries an actual host map `numeral : ℕ → S` and demands a set whose members are exactly the host indexed numerals, which excludes every model with nonstandard naturals. Its existence fields are `isContr`, host unique existence with a chosen centre. A two valued quotient of a Boolean valued universe satisfies none of the three for free. Stating T3 against that record would make T3 unprovable for reasons that have nothing to do with forcing.

K1 therefore separates the ordinary first-order profile from the transitive realization contract, builds the CH and GCH vocabulary over an arbitrary structure, and proves that each sentence agrees with the truth value a reader would write by hand.

## 2. K1-a: the ordinary profile, equality coherence, and the L instance

`OrdinaryZF`, over an arbitrary `𝒮 : ZFStructure (hPropAlgebra ℓ)`, has eight fields, each the host reading of an ordinary first-order sentence through `FOL.Semantics`: `extensional`, `hasPair`, `hasUnion`, `hasPower`, `hasInfinity`, `hasSeparation`, `hasReplacement` and `foundation`. Every existence field is the truncated existential the hProp algebra already interprets, written `⟨ ⋁ S ... ⟩`. No `isContr`, no description operator, no host chosen witness. Replacement is Bell's Collection form and Foundation is Bell's induction form, both from the [full text](bell-2005-boolean-valued-models.fulltext.md), printed pages 17 and 18. `OrdinaryZFC` adds `hasChoice` in the shape of the existing `isZFCModel.hasChoice` (`src/FOL/ZFModel.lagda.md:478-484`), with uniqueness stated internally through `≈ˢ`.

The two Foundation forms are related honestly and their hypotheses are parameters of exactly the lemmas that need them. Induction form to minimal element form needs `LEM ℓ` and nothing else. The converse needs `LEM ℓ` together with an explicit transitive closure existence hypothesis, because the classical argument separates a transitive closure of the starting set by the negated formula and the profile's truncated operations cannot build one.

### Equality coherence

`⟨ x ≈ˢ y ⟩` is a proposition from `ZFStructure` alone, and congruence of membership along host paths is `cong`. Reflexivity of `≈ˢ` is NOT available from `ZFStructure` and NOT available from `isZFModel`, but ordinary Extensionality alone proves it, by instantiating the sentence at `a = b` where the premise is trivially inhabited. Substitution along `≈ˢ`, and symmetry of `≈ˢ`, are not available from the ordinary profile at all; they belong to the realization side. `PathRealization` in `OrdinaryProfile.agda` derives them from the single hypothesis `≈ˢ-paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y)`. That module is the only place the identification of `≈ˢ` with host path equality is permitted to happen.

### Two measured negatives

The transfer `isZFModel 𝒮 → OrdinaryZF 𝒮` does NOT hold as stated. Two independent obstructions, both checked against source.

Extensionality. The strong field concludes a host path `a ≡ b` (`src/FOL/ZFModel.lagda.md:219`); the ordinary sentence concludes `⟨ a ≈ˢ b ⟩`. The bridge is reflexivity of `≈ˢ`, which `isZFModel` does not supply. The countermodel is explicit, and one clause of it was wrong in an earlier revision of this record. Reinterpret `≈ˢ` on a strong model's carrier as the always false relation AND replace the numeral chain by the constant empty-set chain. Most fields survive the first change alone: `hasEmpty`, `hasUnion`, `hasPower` and regularity never mention `≈ˢ`; `hasPair` survives with the empty set because a join of two false propositions is false; `hasSeparation` and `hasReplacement` survive because each formula read under the new `≈ˢ` equals the old reading of the formula with its `≐` atoms replaced by falsity, so the old witness serves. But `numeral-suc` (`src/FOL/ZFModel.lagda.md:400-402`) does NOT survive the first change alone. Instantiate its first component at `z = numeral n` in any strong model whose `≈ˢ` is reflexive, which includes both `𝒮ᵥ` and `𝒮ʟ`: the hypothesis still holds because `∈ˢ` is unchanged, while the conclusion becomes a truncated sum of `numeral n ∈ˢ numeral n` and the empty type, and external well foundedness makes membership irreflexive, so it is empty. Replacing the numeral chain repairs it: numeral zero and both halves of numeral successor then hold, the numeral class is empty and the infinity set is empty. The conclusion, that reflexivity of `≈ˢ` is independent of `isZFModel`, stands; the reason recorded here is the repaired one. So `extensionalFromStrong` takes reflexivity as an explicit parameter, and so do `infinityFromStrong` and `choiceFromStrong`, which are the other two lemmas whose conclusions mention `≈ˢ`. Reflexivity is charged once, to Extensionality, because ordinary Extensionality alone proves it (`≈ˢ-refl`); the other two are not independent failure points.

Replacement. The strong hypothesis is host contractible functionality (`src/FOL/ZFModel.lagda.md:226-228`); Bell's Collection premise is truncated totality, strictly weaker. Closing the gap is the classical Collection from Replacement theorem, which runs through internal rank theory or a reflection ladder, and neither is available generically. `imageFromStrong` records what does transfer; `hasImage` records the converse half of Bell's Remark 1 inside the ordinary profile. Seven of the nine fields transfer; these two do not.

No converse `OrdinaryZF 𝒮 → isZFModel 𝒮` is claimed or attempted. The two records sit on opposite sides of the separation this work exists to expose.

### The L instance

`Lʟ-ordinary : (lem : LEM (ℓ-suc ℓ)) → OrdinaryZFC (𝒮ʟ {ℓ})`, consuming only `L.Model.L⊨ZFC lem` (`src/L/Model.lagda.md:106-107`, registered at `src/Landmarks.lagda.md:84-85`) and `L.ExistentialReflection lem`. No second hypothesis was needed anywhere.

At `𝒮ʟ` both obstructions above vanish concretely, which is the separation doing its work rather than a weakening of it: `⟨ a ≈ˢ b ⟩` is literally `fst a ≡ fst b`, so reflexivity is `refl`, and Collection comes from a single reflection step, `pickStage` (`src/L/ExistentialReflection.lagda.md:196,223`), `boundingOrd`, `bound2` and `LsetS` (`src/L/Axioms/Basic.lagda.md:171-172`). A ladder is needed only when the bound must absorb the parameters of a whole tower; one step suffices because every `x ∈ a` already lies under `Lset sa` by transitivity. The evaluator used by `L.ExistentialReflection` is the profile's own: it is `FOL.Absoluteness.Single`'s renamed `⊨ᵐ` (`src/FOL/Absoluteness.lagda.md:95-96`), which is `FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ isL)` at the same carrier and `id`, and `𝒮ʟ` is defined as exactly that restriction. They agree definitionally and no bridge lemma was needed.

Level bookkeeping: for `𝒮 : ZFStructure (hPropAlgebra ℓ)` the axiom readings and `LEM ℓ` sit at level `ℓ`; at `𝒮ʟ {ℓ}` the relevant level is `ℓ-suc ℓ`, matching `L⊨ZFC`'s hypothesis exactly, and `OrdinaryZFC (𝒮ʟ {ℓ})` lives at `Type (ℓ-suc (ℓ-suc ℓ))`, which the K0 universe ledger already permits for structure packaging.

## 3. K1-b, part one: the cardinal vocabulary and its bridges

`CardinalBridge.agda` is parameterized by `𝒮 : ZFStructure (hPropAlgebra ℓ)` and imports nothing whose name begins with `L.` or `V.`, which is the roadmap's requirement that internal cardinal lemmas stay clear of L-specific condensation. Grep over the file finds no such import.

The syntax has no function symbols (`src/FOL/Syntax.lagda.md`), so every set operation is a defined formula relating its arguments: "p is an ordered pair of x and y", never "the ordered pair". The file defines `Subsetφ`, `IsSingletonφ`, `IsPairφ`, `PairφK` (Kuratowski), `IsRelationφ`, `IsFunctionφ`, `IsInjectionφ`, `Injectableφ`, `IsSuccOfφ`, `IsInductiveφ`, `IsOmegaφ`, `IsPowerSetφ`, `IsTransitiveφ`, `IsOrdinalφ`, `IsCardinalφ` and `IsSuccCardinalφ`, each with a host predicate and a bridge theorem equating the evaluator's reading with that predicate as a path of truth values.

Variable juggling inside the larger formulas goes through `FOL.Manipulation.Renaming` and its correctness theorem `⊨-rename`, reusing the device K1-a already used for one transposition. No second renaming engine was written.

Four corrections were needed on the way. TWO of them, and only two, were defects that typechecking alone would not have caught, because the formulas were well formed and said the wrong thing. The other two failed to typecheck and were therefore cheap: an arity mismatch and a mismatch between two spellings of the empty type. An earlier revision of this record claimed all four were silent, which doubled the true count of what survives a typecheck in this style of work; that figure is the one a later planner would use to decide how much manual formula review a package needs, so it is corrected here rather than left.

The linearity clause of `IsOrdinalφ` ranged its inner bounded quantifier over the outer bound variable instead of over the ordinal. Reading it out, the clause said "for every `x ∈ α` and every `y ∈ x`, `x ∈ y` or `x ≈ y` or `y ∈ x`", whose third disjunct is the hypothesis, so the clause held vacuously and `IsOrdinalφ` was equivalent to transitivity alone. The inner quantifier now ranges over `α`.

`IsSuccOfφ` asserted `x ∈ y` and `y ⊆ x ∪ {x}` but not `x ⊆ y`, so it admitted `y = {x}` as a successor of `x`. Under that reading the inductive sets include the Zermelo chain, the least inductive set is not the von Neumann `ω`, and `IsOmegaφ` would not pin a unique object. The missing inclusion is now a conjunct.

`IsSuccCardinalφ` used `IsCardinalφ`, a `Formula S 1`, directly inside a `Formula S 2` body and again under a further binder. The two occurrences are now renamed into place, and the bridge is rebuilt from the component bridges rather than asserted by `refl`.

The bridge through a negated subformula did not typecheck: the syntax expands `¬̇ φ` to `φ ⇒̇ ⊥̇`, the evaluator sends `⊥̇` to the algebra's `⊥`, which is `⊥* = Lift ⊥` (`src/Base/Truth.lagda.md:128`), while the algebra's `¬_` is the library's, built on the unlifted `⊥` (`src/Base/Truth.lagda.md:126`). The two are logically equivalent and not definitionally equal. `¬-as-⇒⊥` reconciles them once and is reused by the negation of CH.

One mechanical lesson worth keeping. A bare `refl` as an argument of `cong₂` over `_⊓_` or `_⇒_` leaves the `isProp` component of its endpoint undetermined, because those operations build a Σ-pair and matching the goal fixes the carrier and not the proof of propositionality. Nine such sites produced unsolved metas. The file now names each unchanged endpoint through a one line helper, `same : (P : Ω) → P ≡ P`.

## 4. K1-b, part two: CH, its negation, and the omega instance of GCH

`CHSentence.agda` defines `CHsent : Formula S 0`, `¬CHsent = ¬̇ CHsent`, and `GCHωsent : Formula S 0`, each with the truth value a host reader would write down, and each with its agreement theorem. The agreement theorems are the deliverable. Roadmap section 1 makes them an acceptance condition of T3: "The semantic CH predicate and its object-language sentence must agree; likewise for the omega-instance of GCH." Without them a proof that the negation has Boolean value top would say nothing about the model actually having many reals.

Because the syntax has no function symbols, neither omega nor the power set can appear as a term. Both sentences universally quantify over a `w` that is omega and a `p` that is its power set, and say nothing when no such pair exists. Existence is a separate matter, supplied by the profile's Infinity, Power Set and Separation, not by these sentences. This is a deliberate design choice and it is what keeps the sentences meaningful in a model whose omega is not the host's.

CH is the no-intermediate-set form: for every omega `w` and power set `p` of `w`, a set that `w` injects into and that injects into `p` either injects back into `w` or receives an injection from `p`. This is the form the Cohen argument hits directly, because that argument produces an intermediate set rather than refuting a cardinal equation.

`GCHωsent` is the successor cardinal form, matching the shape of the existing `L.GCH.GCHStatement` (`src/L/GCH.lagda.md:51-61`): the power set of omega is equinumerous with the successor cardinal of omega, equinumerous meaning a pair of injections rather than a bijection.

The three checked statements:

```text
CH-agrees   : ([] ⊨ CHsent)   ≡ chValue
¬CH-agrees  : ([] ⊨ ¬CHsent)  ≡ (¬ chValue)
GCHω-agrees : ([] ⊨ GCHωsent) ≡ gchωValue
```

`¬CH-agrees` needs no excluded middle. Its only step beyond transporting `CH-agrees` is `¬-as-⇒⊥`, the lifted bottom reconciliation above.

The implication from the omega instance of GCH to CH is NOT proved, and an earlier revision of this record misattributed the blocker. It is not Choice. The hypothesis already grants an injection of `x` into the power set, and the omega instance grants an injection of the power set into a successor cardinal, which is an ordinal; composing gives an injection of `x` into an ordinal, and pulling the membership order back along an injection well orders `x` outright. That is a theorem of ZF, not the axiom of choice, and neither Hartogs nor Cantor Bernstein appears in it; the disjuncts the CH value asks for need mutual injections, never a bijection. What is genuinely missing is internal order-type machinery, an order-type construction from Collection and least-ordinal reasoning from induction-form Foundation, both of which are already fields of `OrdinaryZF`, plus a classical case split that the existing LEM pays for. It is a K7 or K15 obligation, not a K1 one, but it is a smaller one than this record first claimed.

## 5. The L re-expression, delivered

An earlier revision of this record listed the L re-expression of GCH as not
delivered and decomposed it into five comparison theorems. All five are now
proved, together with one ingredient the repository did not have, and the closure
theorem composes them. The decomposition itself was accurate and is kept below as
the map of what each file does.

The closure theorem, checked at exit 0:

```text
L⊨GCHω : (lem : LEM (ℓ-suc ℓ)) → ⟨ [] ⊨ GCHωsent ⟩
```

at `𝒮ʟ {ℓ}`. The existing `L⊨GCH` is consumed unchanged and its single `LEM
(ℓ-suc ℓ)` is the only hypothesis. What this buys is the thing the agreement
theorem of section 4 exists for: the object-language sentence is true in the
constructible structure, in a vocabulary that is structure-polymorphic and will
therefore also speak about a Cohen quotient. Pairing L against that quotient is
K15's job, and K15 now has its positive half in the right language.

### The five comparisons, as proved

1. **The pair, the keystone.** `pair-to-pr` and `pr-to-pair`, both directions
   between the internal Kuratowski pair predicate and the ambient pair. NO
   excluded middle at any level, and no field of `OrdinaryZF`. The reverse
   direction needs neither ambient extensionality nor closure of `L` under
   pairing, because every set the internal quantifier meets is already a member of
   the pair. The convenient helpers at `src/V/Coding.lagda.md:149-170` are
   `private` and cannot be imported, but they proved unnecessary:
   `V.Model.pair-spec` (`src/V/Model.lagda.md:94`) is public and already carries
   the pairing classification.
2. **Injection and injectability.** `inj-to` and `inj-from` are FALSE as this
   record first stated them, and each is delivered with one isolated extra
   hypothesis. The two predicates differ by a conjunct in each direction, and both
   gaps are real. The general `isInjection` does not bound the domain: its domain
   clause is one implication while `domAt` (`src/L/Coding/Model.lagda.md:301-302`)
   is a biconditional, so a graph may have domain strictly larger than the
   intended one; the counterexample is the empty domain with a one-point graph.
   Conversely `InjCode` never requires the graph to consist of pairs, since all
   four of its conjuncts speak only of members of the form of a pair, while
   `isInjection` reaches `isRelation` through `isFunction`; the counterexample
   adds the empty set to a graph. Both gaps ask a graph to be SMALLER, so
   separation inside L closes both, and because injectability, `InjL`,
   `IsCardinalL` and `SuccCardL` all quantify the graph existentially, the four
   downstream comparisons carry NO extra hypothesis and the two extra hypotheses
   are consumed internally and never have to be discharged by anyone.
3. **The ordinal.** `ord-to` with no excluded middle, `ord-from` with `LEM (ℓ-suc ℓ)`
   as an argument of that lemma alone, and `ord-agrees` as a path of truth values
   rather than a mere logical equivalence, which is the form a rewrite inside a
   satisfaction statement needs. The forward direction costs acyclicity rather than
   irreflexivity: trichotomy leaves a membership 2-cycle and a 3-cycle to refute,
   and the repository had only the 1-cycle case, `∈-irrefl`
   (`src/V/Hierarchy.lagda.md:169`), which does not generalise. The two new lemmas
   are each one well-founded induction whose step rotates the cycle.
4. **Cardinal and successor cardinal.** Six results, all without extra hypotheses
   beyond the parameters from 1 and 3. The minimality clauses of the two successor
   notions are genuinely different sentences, a truncated disjunction against a
   subset relation, and they agree only for ordinals, which is one more use of the
   existing trichotomy rather than a new obligation.
5. **Omega and the power set.** Six results including `isOmega-pins`, that the
   internal omega predicate pins the ambient omega uniquely, and `isPowerSet-pins`
   for the power set. This is what lets an arbitrary `w` and `p` in the sentence be
   identified with the specific objects the L theorem speaks about. The realization
   step is `↾-reflects` (`src/FOL/ZFStructure.lagda.md:194`), used at three points
   and named there, because it is exactly what the general profile does not have.

### The ingredient the repository did not have

`ωʟ-IsCardinalL`, that omega is an internal cardinal of L. Searched and confirmed
absent before it was built. The ambient form `ω-noInj` sits at the top level of a
module whose only parameter is the universe level, so its independence from
excluded middle is machine checked rather than claimed; the internal form takes
the single `LEM (ℓ-suc ℓ)`, once for the constructible omega and once for reading
a constructible injection graph back as an ambient one. The finite pigeonhole is
the cubical library's constructive one and the only decidability used is
decidability of equality on finite sets. The brief asked for the ambient statement
at the top level, which is impossible because the ambient cardinal predicate is
declared inside a module parameterized by excluded middle and cannot be named
without it; the delivered form is that statement written out.

### Where the sources live

These files are in a temporary compile root and are NOT embedded below. `/tmp`
does not survive a reboot on this machine and two earlier worktrees were lost that
way, so they must be preserved or re-embedded before this record is trusted alone.

| File | What | Lines | SHA-256 prefix |
|---|---|---|---|
| `/tmp/bedrock-k1-t1/PairComparison.agda` | comparison 1, the Kuratowski pair keystone | 194 | `c33d8f7be67f6473` |
| `/tmp/bedrock-k1-t2/OrdinalComparison.agda` | comparison 3, the ordinal predicates | 193 | `2637587193b64bc6` |
| `/tmp/bedrock-k1-t3/InjectionComparison.agda` | comparisons 2 and 4, injection and cardinal | 344 | `054475f1c4e84e44` |
| `/tmp/bedrock-k1-t4/OmegaPowerComparison.agda` | comparison 5, omega and the power set | 176 | `bc843035fe271ce6` |
| `/tmp/bedrock-k1-t5/OmegaCardinal.agda` | omega is an internal cardinal of L | 140 | `dfc2d1899ec5d43a` |
| `/tmp/bedrock-k1-t6/GCHInNewVocabulary.agda` | the assembly | 225 | `9371202a989dd60b` |
| `/tmp/bedrock-k1-close/K1Closure.agda` | the closure theorem | 41 | `989942df885f2451` |

### Still not delivered, and still named

The implication from the omega instance of GCH to CH, discussed in section 4. The
existence of an omega in an arbitrary model of the profile, which needs
substitution along the structure equality that section 2 measures as unavailable
outside a realization. Both belong to later packages.

## 6. Validation

All five probes were rechecked by the coordinator after deleting every probe interface file, so none of the exit codes below rests on a cached interface.

| File | Lines | Command | Exit |
|---|---|---|---|
| `OrdinaryProfile.agda` | 398 | `GHCRTS="-A64m -I0 -M8g" agda OrdinaryProfile.agda` | 0 |
| `ProfileFromStrong.agda` | 199 | `GHCRTS="-A64m -I0 -M8g" agda ProfileFromStrong.agda` | 0 |
| `ProfileFromL.agda` | 239 | `GHCRTS="-A64m -I0 -M8g" agda ProfileFromL.agda` | 0 |
| `CardinalBridge.agda` | 608 | `GHCRTS="-A64m -I0 -M8g" agda CardinalBridge.agda` | 0 |
| `CHSentence.agda` | 200 | `GHCRTS="-A64m -I0 -M8g" agda CHSentence.agda` | 0 |

Every file carries exactly `{-# OPTIONS --cubical --safe --guardedness #-}`. Grep over all five finds no `postulate`, no `TERMINATING` or `NON_TERMINATING`, no `trustMe`, no hole and no unsolved meta. Agda reported no warning on any of them. The 8 GB heap was never exhausted. Grep over `CardinalBridge.agda`, `CHSentence.agda`, `OrdinaryProfile.agda` and `ProfileFromStrong.agda` finds no import whose name begins with `L.` or `V.`. The repository worktree carries no tracked change; the only writes inside it were Agda's git-ignored interface cache under `_build/`. No whole-tree build was run for this document-only change.

## 7. Reproducible snapshots

The probes live in the temporary compile root `/tmp/bedrock-k1-probes`, whose library file puts the repository `src` on the include path. That root does not survive a reboot, and the K0 worktrees were lost that way once, so the checked text is preserved below. Each snapshot is the exact file that produced the exit code above, with its single trailing newline stripped by the fence; each SHA-256 is of the file itself, trailing newline included.

### OrdinaryProfile.agda

K1-a: the ordinary first-order profile, the Foundation equivalences, the realization module and the image lemma.

SHA-256: `20b4b95abda458828cb7511bae092e10b5cbd9a2638a8881413cb4388f3b0475`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

-- K1 probe A and B: the ordinary first-order ZF profile, its Choice extension,
-- the Foundation form equivalences, and the equality coherence facts.
-- Bell 2005, printed pages 17-18, fixes the axiom shapes used here.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module OrdinaryProfile {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import Base.Classical using ( LEM )
open import FOL.ZFStructure
  using ( module hPropStructure; Transitive )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ⊥̇; ¬̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- The internal biconditional. Spelled from the algebra's implication and meet,
-- exactly the reading of the object-language abbreviation φ ↔ ψ.

iff : Ω → Ω → Ω
iff P Q = (P ⇒ Q) ⊓ (Q ⇒ P)

iff-intro : (P Q : Ω) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩) → ⟨ iff P Q ⟩
iff-intro P Q f g = f , g

-- The bridge the later files consume: an hProp-valued membership
-- specification, stated as paths of hProps, becomes the internal biconditional
-- the ordinary sentences read.

spec-to-iff : (b : S) (Q : S → Ω) → ((x : S) → (x ∈ˢ b) ≡ Q x)
            → ⟨ ⋀ S (λ x → iff (x ∈ˢ b) (Q x)) ⟩
spec-to-iff b Q sp =
  λ x → iff-intro (x ∈ˢ b) (Q x)
    (λ h → subst ⟨_⟩ (sp x) h) (λ h → subst ⟨_⟩ (sym (sp x)) h)

iff-to-spec : (a b : S) → ⟨ ⋀ S (λ z → iff (z ∈ˢ a) (z ∈ˢ b)) ⟩
            → (z : S) → (z ∈ˢ a) ≡ (z ∈ˢ b)
iff-to-spec a b h z = ⇔toPath (h z .fst) (h z .snd)

-- The axiom readings. Each is the host reading of an ordinary first-order
-- sentence through FOL.Semantics: existence fields use the truncated
-- existential the hProp algebra interprets, never host contractibility, never
-- a description operator, never a host-chosen witness.

Extensionality : Type ℓ
Extensionality =
  (a b : S) → ⟨ ⋀ S (λ z → iff (z ∈ˢ a) (z ∈ˢ b)) ⟩ → ⟨ a ≈ˢ b ⟩

Pairing : Type ℓ
Pairing =
  (a b : S)
    → ⟨ ⋁ S (λ p → ⋀ S (λ x → iff (x ∈ˢ p) ((x ≈ˢ a) ⊔ (x ≈ˢ b)))) ⟩

Union : Type ℓ
Union =
  (a : S)
    → ⟨ ⋁ S (λ v → ⋀ S (λ x → iff (x ∈ˢ v)
         (⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y))))) ⟩

PowerSet : Type ℓ
PowerSet =
  (a : S)
    → ⟨ ⋁ S (λ v → ⋀ S (λ x → iff (x ∈ˢ v)
         (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a))))) ⟩

-- Bell (6) with ∅ spelled as "memberless": there is an inductive set, a set
-- with a memberless member in which every member has a member. Not the
-- standard-numeral formulation of the existing strong record.

Infinity : Type ℓ
Infinity =
  ⟨ ⋁ S (λ u → (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ z → (z ∈ˢ e) ⇒ ⊥))))
            ⊓ (⋀ S (λ x → (x ∈ˢ u) ⇒ (⋁ S (λ y → (y ∈ˢ u) ⊓ (x ∈ˢ y)))))) ⟩

Separation : Type ℓ
Separation =
  (a : S) (φ : Formula S 1)
    → ⟨ ⋁ S (λ s → ⋀ S (λ x → iff (x ∈ˢ s) ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ)))) ⟩

-- Bell (3), Collection form Replacement.

Collection : Type ℓ
Collection =
  (a : S) (φ : Formula S 2)
    → ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → (y ∷ x ∷ []) ⊨ φ))) ⟩
    → ⟨ ⋁ S (λ b → ⋀ S (λ x → (x ∈ˢ a) ⇒
         (⋁ S (λ y → (y ∈ˢ b) ⊓ ((y ∷ x ∷ []) ⊨ φ))))) ⟩

-- Bell (7), induction form Foundation.

FoundationInduction : Type ℓ
FoundationInduction =
  (φ : Formula S 1)
    → ( (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩)
                  → ⟨ (x ∷ []) ⊨ φ ⟩ )
    → (x : S) → ⟨ (x ∷ []) ⊨ φ ⟩

-- Choice, truncated existence of a choice set, with the hypothesis shape the
-- existing isZFCModel already uses. "Exactly one point" is internal: existence
-- by the truncated existential, uniqueness up to the structure's ≈ˢ.

ChoiceSet : Type ℓ
ChoiceSet =
  (a : S)
    → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
    → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
         → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
    → ⟨ ⋁ S (λ c → ⋀ S (λ x → (x ∈ˢ a) ⇒
         ( (⋁ S (λ z → (z ∈ˢ c) ⊓ (z ∈ˢ x)))
         ⊓ (⋀ S (λ z → ⋀ S (λ z' → (((z ∈ˢ c) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ c) ⊓ (z' ∈ˢ x)))
             ⇒ (z ≈ˢ z'))))))) ⟩

record OrdinaryZF : Type (ℓ-suc ℓ) where
  field
    extensional    : Extensionality
    hasPair        : Pairing
    hasUnion       : Union
    hasPower       : PowerSet
    hasInfinity    : Infinity
    hasSeparation  : Separation
    hasReplacement : Collection
    foundation     : FoundationInduction

record OrdinaryZFC : Type (ℓ-suc ℓ) where
  field
    zf : OrdinaryZF
  open OrdinaryZF zf public
  field
    hasChoice : ChoiceSet

-- Part B: equality coherence.
--
-- What ZFStructure alone supplies: ≈ˢ is a field into Ω, so its truth is a
-- proposition, and host path equality substitutes under both arguments of
-- membership, because membership is a function.

≈ˢ-isProp : (x y : S) → isProp ⟨ x ≈ˢ y ⟩
≈ˢ-isProp x y = snd (x ≈ˢ y)

∈ˢ-cong-subst : (x y z : S) → x ≡ y → (x ∈ˢ z) ≡ (y ∈ˢ z)
∈ˢ-cong-subst x y z p = cong (_∈ˢ z) p

∈ˢ-cong-base : (x y z : S) → y ≡ z → (x ∈ˢ y) ≡ (x ∈ˢ z)
∈ˢ-cong-base x y z p = cong (x ∈ˢ_) p

-- What ordinary Extensionality supplies beyond that: reflexivity, by
-- instantiating the sentence at a = b, where its premise holds trivially; and
-- with reflexivity, every host path reflects into ≈ˢ.

≈ˢ-refl : Extensionality → (x : S) → ⟨ x ≈ˢ x ⟩
≈ˢ-refl ext x = ext x x (λ z → (λ p → p) , (λ p → p))

≈ˢ-of-path : Extensionality → {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
≈ˢ-of-path ext {x} {y} p = subst (λ w → ⟨ x ≈ˢ w ⟩) p (≈ˢ-refl ext x)

-- What is NOT available: from truth of ⟨ x ≈ˢ y ⟩ to equality of the hProps
-- x ∈ˢ z and y ∈ˢ z, in either argument. Neither ZFStructure nor
-- Extensionality gives it; Extensionality runs the other way, from agreement
-- of membership to equality. The facts below hold under the realization
-- contract that identifies ≈ˢ with host paths, which is what the quotient
-- construction of K0 and the concrete V and L instances supply.

module PathRealization
  (≈ˢ-paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y)) where

  ≈ˢ-to-path : (x y : S) → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ-to-path x y h = subst ⟨_⟩ (≈ˢ-paths x y) h

  path-to-≈ˢ : (x y : S) → x ≡ y → ⟨ x ≈ˢ y ⟩
  path-to-≈ˢ x y p = subst ⟨_⟩ (sym (≈ˢ-paths x y)) p

  ≈ˢ-sym : (x y : S) → ⟨ x ≈ˢ y ⟩ → ⟨ y ≈ˢ x ⟩
  ≈ˢ-sym x y h = path-to-≈ˢ y x (sym (≈ˢ-to-path x y h))

  subst-member : (x y z : S) → ⟨ x ≈ˢ y ⟩ → (x ∈ˢ z) ≡ (y ∈ˢ z)
  subst-member x y z h = cong (_∈ˢ z) (≈ˢ-to-path x y h)

  subst-base : (x y z : S) → ⟨ y ≈ˢ z ⟩ → (x ∈ˢ y) ≡ (x ∈ˢ z)
  subst-base x y z h = cong (x ∈ˢ_) (≈ˢ-to-path y z h)

-- Part A extra: the relation between induction form Foundation and the
-- ordinary minimal element form, Bell (7) against Bell (7*).

MinimalElement : Type ℓ
MinimalElement =
  (u : S) → ⟨ ⋁ S (λ z → z ∈ˢ u) ⟩
        → ⟨ ⋁ S (λ x → (x ∈ˢ u)
             ⊓ (⋀ S (λ w → ((w ∈ˢ x) ⊓ (w ∈ˢ u)) ⇒ ⊥))) ⟩

TransitiveClosure : Type ℓ
TransitiveClosure =
  (u : S) → ∥ Σ[ t ∈ S ] (⟨ u ∈ˢ t ⟩ × Transitive 𝒮 (λ z → z ∈ˢ t)) ∥₁

module MinimalForm (u : S) where

  noCommon : S → S → Ω
  noCommon x u' = ⋀ S (λ w → ((w ∈ˢ x) ⊓ (w ∈ˢ u')) ⇒ ⊥)

  minimal-sentence : S → Ω
  minimal-sentence x = (x ∈ˢ u) ⊓ noCommon x u

  -- z ∈ u ⇒ ∃ x. x ∈ u ∧ ∀ w. (w ∈ x ∧ w ∈ u) ⇒ ⊥, with u as a constant.

  fo : Formula S 1
  fo = (var zero ∈̇ con u)
    ⇒̇ ∃̇ ((var zero ∈̇ con u)
      ∧̇ (∀̇ (¬̇ ((var zero ∈̇ var (suc zero)) ∧̇ (var zero ∈̇ con u)))))

  fo-reading : (z : S)
    → ((z ∷ []) ⊨ fo) ≡ ((z ∈ˢ u) ⇒ (⋁ S minimal-sentence))
  fo-reading z = refl

-- Induction form gives the minimal element form, given excluded middle at the
-- profile's own level. The classical step is the case split on "x and u have a
-- common member"; with no common member, x itself is minimal.

foundation→minimal : FoundationInduction → LEM ℓ → MinimalElement
foundation→minimal find lem u nonempty =
  PT.rec (snd target) (λ { (z₀ , z₀∈u) → find fo step z₀ z₀∈u }) nonempty
  where
    open MinimalForm u

    target : Ω
    target = ⋁ S minimal-sentence

    step : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ fo ⟩)
         → ⟨ (x ∷ []) ⊨ fo ⟩
    step x ih x∈u = decide (lem (⋁ S (λ w → (w ∈ˢ x) ⊓ (w ∈ˢ u))))
      where
        decide : ⟨ ⋁ S (λ w → (w ∈ˢ x) ⊓ (w ∈ˢ u)) ⟩
               ⊎ (⟨ ⋁ S (λ w → (w ∈ˢ x) ⊓ (w ∈ˢ u)) ⟩ → Empty.⊥)
               → ⟨ target ⟩
        decide (inl some) = PT.rec (snd target)
          (λ { (w , w∈x , w∈u) → ih w w∈x w∈u }) some
        decide (inr none) =
          ∣ x , (x∈u , λ w common → Empty.rec (none ∣ w , common ∣₁)) ∣₁

-- The converse needs more than excluded middle: the classical proof separates
-- a transitive closure of the starting set by the negated formula and applies
-- the minimal element form there. The profile's truncated operations do not
-- build transitive closures, so the closure is an explicit hypothesis of this
-- lemma, alongside excluded middle and the schema's Separation field.

minimal→foundation : OrdinaryZF → MinimalElement → LEM ℓ → TransitiveClosure
                   → FoundationInduction
minimal→foundation r minimal lem tc φ step u₀ =
  decideTop (lem ((u₀ ∷ []) ⊨ φ))
  where
    refute : (t : S) → Transitive 𝒮 (λ z → z ∈ˢ t)
           → (s : S) → ((z : S) → ⟨ iff (z ∈ˢ s)
                ((z ∈ˢ t) ⊓ ((z ∷ []) ⊨ ¬̇ φ)) ⟩)
           → (x : S) → ⟨ x ∈ˢ s ⟩
           → ⟨ ⋀ S (λ w → ((w ∈ˢ x) ⊓ (w ∈ˢ s)) ⇒ ⊥) ⟩
           → ⟨ (u₀ ∷ []) ⊨ φ ⟩
    refute t trans s spec x x∈s disj =
      branch (lem (⋁ S (λ y → (y ∈ˢ x) ⊓ ((y ∷ []) ⊨ ¬̇ φ))))
      where
        x∈t : ⟨ x ∈ˢ t ⟩
        x∈t = spec x .fst x∈s .fst

        nφx : ⟨ (x ∷ []) ⊨ ¬̇ φ ⟩
        nφx = spec x .fst x∈s .snd

        branch : ⟨ ⋁ S (λ y → (y ∈ˢ x) ⊓ ((y ∷ []) ⊨ ¬̇ φ)) ⟩
               ⊎ (⟨ ⋁ S (λ y → (y ∈ˢ x) ⊓ ((y ∷ []) ⊨ ¬̇ φ)) ⟩ → Empty.⊥)
               → ⟨ (u₀ ∷ []) ⊨ φ ⟩
        branch (inl some) = PT.rec (snd ((u₀ ∷ []) ⊨ φ))
          (λ { (y , y∈x , nφy) →
               Empty.rec* (disj y
                 ( y∈x
                 , spec y .snd (trans y∈x x∈t , nφy) )) })
          some
        branch (inr none) = Empty.rec* (nφx (step x all-members))
          where
            all-members : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ (y ∷ []) ⊨ φ ⟩
            all-members y y∈x = decideY (lem ((y ∷ []) ⊨ φ))
              where
                decideY : ⟨ (y ∷ []) ⊨ φ ⟩ ⊎ (⟨ (y ∷ []) ⊨ φ ⟩ → Empty.⊥)
                       → ⟨ (y ∷ []) ⊨ φ ⟩
                decideY (inl holds) = holds
                decideY (inr nφy) = Empty.rec
                  (none ∣ y , (y∈x , λ h → Empty.rec (nφy h)) ∣₁)

    decideTop : ⟨ (u₀ ∷ []) ⊨ φ ⟩ ⊎ (⟨ (u₀ ∷ []) ⊨ φ ⟩ → Empty.⊥)
              → ⟨ (u₀ ∷ []) ⊨ φ ⟩
    decideTop (inl holds) = holds
    decideTop (inr fails) =
      PT.rec (snd ((u₀ ∷ []) ⊨ φ))
        (λ { (t , u₀∈t , trans) →
             PT.rec (snd ((u₀ ∷ []) ⊨ φ))
               (λ { (s , spec) →
                    PT.rec (snd ((u₀ ∷ []) ⊨ φ))
                      (λ { (x , x∈s , disj) →
                           refute t trans s spec x x∈s disj })
                      (minimal s
                        ∣ u₀ , spec u₀ .snd (u₀∈t , λ h → Empty.rec (fails h)) ∣₁) })
               (OrdinaryZF.hasSeparation r t (¬̇ φ)) })
        (tc u₀)

-- The compensation direction for Replacement, the half of Bell's Remark 1
-- equivalence that the ordinary profile proves on its own: Collection plus
-- Separation turns a functional relation into an image set. Functionality is
-- host contractibility here, matching the hypothesis shape of the existing
-- strong record, so this is also the exact statement of what the strong
-- record's Replacement field would need to be re-obtained after transferring.

module Swap where

  swap : Fin 2 → Fin 2
  swap zero    = suc zero
  swap (suc _) = zero

  swapFo : Formula S 2 → Formula S 2
  swapFo = renameFo swap

  module Ren = Sat (hPropAlgebra ℓ) 𝒮 id

  swapAgrees : (x z : S) → Ren.Agrees swap (x ∷ z ∷ []) (z ∷ x ∷ [])
  swapAgrees x z zero       = refl
  swapAgrees x z (suc zero) = refl

  ⊨-swap : (φ : Formula S 2) (x z : S)
         → ((x ∷ z ∷ []) ⊨ swapFo φ) ≡ ((z ∷ x ∷ []) ⊨ φ)
  ⊨-swap φ x z =
    Ren.⊨-rename swap φ (x ∷ z ∷ []) (z ∷ x ∷ []) (swapAgrees x z)

hasImage : OrdinaryZF
  → (a : S) (φ : Formula S 2)
  → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
  → ⟨ ⋁ S (λ b → ⋀ S (λ y → iff (y ∈ˢ b)
       (⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))) ⟩
hasImage r a φ fc =
  PT.rec (snd target)
    (λ { (b , bound) →
         PT.rec (snd target)
           (λ { (img , spec) → ∣ img , assemble b bound img spec ∣₁ })
           (OrdinaryZF.hasSeparation r b θ) })
    (OrdinaryZF.hasReplacement r a φ premise)
  where
    open Swap

    image-pred : S → Ω
    image-pred y = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))

    target : Ω
    target = ⋁ S (λ b → ⋀ S (λ y → iff (y ∈ˢ b) (image-pred y)))

    θ : Formula S 1
    θ = ∃̇∈ (con a) (swapFo φ)

    θ-reading : (y : S)
      → ((y ∷ []) ⊨ θ) ≡ (image-pred y)
    θ-reading y =
      cong (⋁ S) (funExt (λ x → cong ((x ∈ˢ a) ⊓_) (⊨-swap φ x y)))

    premise : ⟨ ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → (y ∷ x ∷ []) ⊨ φ))) ⟩
    premise x x∈a = ∣ fc x x∈a .fst ∣₁

    assemble : (b : S)
      → ((x : S) → ⟨ x ∈ˢ a ⟩
           → ⟨ ⋁ S (λ y → (y ∈ˢ b) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩)
      → (img : S)
      → ((z : S) → ⟨ iff (z ∈ˢ img) ((z ∈ˢ b) ⊓ ((z ∷ []) ⊨ θ)) ⟩)
      → ⟨ ⋀ S (λ y → iff (y ∈ˢ img) (image-pred y)) ⟩
    assemble b bound img spec = λ y → backward y , forward y
      where
        forward : (y : S) → ⟨ image-pred y ⟩ → ⟨ y ∈ˢ img ⟩
        forward y image =
          PT.rec (snd (y ∈ˢ img))
            (λ { (x , x∈a , sat) →
                 PT.rec (snd (y ∈ˢ img))
                   (λ { (y' , y'∈b , sat') →
                        spec y .snd
                          ( subst (λ w → ⟨ w ∈ˢ b ⟩)
                              (sym (cong fst (sym (fc x x∈a .snd (y , sat))
                                          ∙ fc x x∈a .snd (y' , sat'))))
                              y'∈b
                          , subst ⟨_⟩ (sym (θ-reading y))
                              ∣ x , (x∈a , sat) ∣₁ ) })
                   (bound x x∈a) })
            image

        backward : (y : S) → ⟨ y ∈ˢ img ⟩ → ⟨ image-pred y ⟩
        backward y y∈img =
          subst ⟨_⟩ (θ-reading y) (spec y .fst y∈img .snd)
```

### ProfileFromStrong.agda

K1-a: what the strong record transfers, and the two fields it does not.

SHA-256: `8153d3ba09b2bc16733301e81969c054dc9b08e72a108991fa43e793c3ff1a68`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

-- K1 probe C: what the existing strong record isZFModel transfers to the
-- ordinary profile, and exactly where the transfer stops.
--
-- Two obstructions, both measured, neither closed here:
--
-- Extensionality. The strong field gives host paths a ≡ b from pointwise
-- equality of membership; the ordinary sentence, read through FOL.Semantics,
-- concludes ⟨ a ≈ˢ b ⟩. The bridge is reflexivity of ≈ˢ along host paths,
-- which isZFModel does not supply: reinterpret ≈ˢ as the always-false relation
-- on any carrier satisfying the strong record and every field survives, since
-- the ≈ˢ-mentioning specifications then describe the empty set (pairing), or
-- the empty class (isNumeral, realized by any empty set), or are witnessed by
-- the same carrier reading each formula with its ≐ atoms false, while
-- ⟨ x ≈ˢ x ⟩ fails everywhere. So reflexivity is an explicit parameter EqRefl
-- below, of exactly the lemmas that need it and of nothing else. At the
-- concrete V and L structures, and at the K0 two-valued quotient, ≈ˢ is host
-- path equality, so EqRefl holds there by refl.
--
-- Replacement. The strong hypothesis is host-contractible functionality
-- (src/FOL/ZFModel.lagda.md, field hasReplacement); Bell's Collection premise
-- is truncated totality, strictly weaker. Closing the gap between them is the
-- classical Collection-from-Replacement theorem, which runs through internal
-- rank theory (Scott's trick) or a reflection ladder; the ordinary profile's
-- truncated operations build neither, and no other field of the strong record
-- connects host well-foundedness to internal set construction. What transfers
-- is recorded below as imageFromStrong; the converse half of Bell's Remark 1
-- equivalence, Collection plus Separation implying the image form, is proved
-- inside the ordinary profile as hasImage in OrdinaryProfile.agda.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module ProfileFromStrong {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
import FOL.ZFModel
import Cubical.Induction.WellFounded as WFRec
import Cubical.Data.Empty as Empty
import Cubical.Data.Nat using ( ℕ ; zero )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

open import OrdinaryProfile 𝒮
  using ( iff; iff-intro; spec-to-iff; iff-to-spec
        ; Extensionality; Pairing; Union; PowerSet; Infinity; Separation
        ; Collection; FoundationInduction; ChoiceSet )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module ModelS = FOL.ZFModel 𝒮
open ModelS using ( isZFModel; isZFCModel; ℩-spec )

EqRefl : Type ℓ
EqRefl = (x : S) → ⟨ x ≈ˢ x ⟩

-- Extensionality transfers under EqRefl: pointwise iff becomes pointwise hProp
-- equality by propositional extensionality, the strong field turns that into a
-- host path, and EqRefl transports reflexivity along it.

extensionalFromStrong : EqRefl → isZFModel → Extensionality
extensionalFromStrong reflˢ r a b same =
  subst (λ w → ⟨ a ≈ˢ w ⟩)
    (ModelS.isZFModel.extensional r (iff-to-spec a b same)) (reflˢ a)

-- Pairing, Union, Power Set and Separation transfer directly: the centre of
-- the strong unique-existence field satisfies the hProp specification, and
-- spec-to-iff turns it into the internal biconditional the ordinary sentence
-- reads.

pairFromStrong : isZFModel → Pairing
pairFromStrong r a b =
  let (p , sp) = ModelS.isZFModel.hasPair r a b .fst
  in ∣ p , spec-to-iff p _ sp ∣₁

unionFromStrong : isZFModel → Union
unionFromStrong r a =
  let (v , sp) = ModelS.isZFModel.hasUnion r a .fst
  in ∣ v , spec-to-iff v _ sp ∣₁

powerFromStrong : isZFModel → PowerSet
powerFromStrong r a =
  let (v , sp) = ModelS.isZFModel.hasPower r a .fst
  in ∣ v , spec-to-iff v _ sp ∣₁

separationFromStrong : isZFModel → Separation
separationFromStrong r a φ =
  let (s , sp) = ModelS.isZFModel.hasSeparation r a φ .fst
  in ∣ s , spec-to-iff s _ sp ∣₁

-- Infinity: the strong record's numeral chain and its ω form an inductive set
-- in Bell's sense. Placing elements into ω goes through the isNumeral
-- specification, which speaks ≈ˢ, so EqRefl is consumed once per placement;
-- the successor step itself comes from the numeral-suc field's right-to-left
-- direction, which needs nothing.

infinityFromStrong : EqRefl → isZFModel → Infinity
infinityFromStrong reflˢ r =
  ∣ ω , ∣ numeral zero , (e∈ω , empty-e) ∣₁ , succ-closed ∣₁
  where
    open ModelS.isZFModel r using ( numeral; numeral-zero; numeral-suc
                                  ; hasInfinity; ω; isNumeral )

    specω : (x : S) → (x ∈ˢ ω) ≡ (isNumeral x)
    specω = ℩-spec hasInfinity

    e∈ω : ⟨ numeral zero ∈ˢ ω ⟩
    e∈ω = subst ⟨_⟩ (sym (specω (numeral zero)))
      ∣ lift zero , reflˢ (numeral zero) ∣₁

    empty-e : ⟨ ⋀ S (λ z → (z ∈ˢ numeral zero) ⇒ ⊥) ⟩
    empty-e z h = Empty.rec (numeral-zero z h)

    succ-closed : ⟨ ⋀ S (λ x → (x ∈ˢ ω) ⇒ (⋁ S (λ y → (y ∈ˢ ω) ⊓ (x ∈ˢ y)))) ⟩
    succ-closed x x∈ω =
      PT.rec (snd (⋁ S (λ y → (y ∈ˢ ω) ⊓ (x ∈ˢ y))))
        (λ { (n , x≈n) →
             ∣ numeral (suc (lower n))
               , ( subst ⟨_⟩ (sym (specω (numeral (suc (lower n)))))
                     ∣ lift (suc (lower n))
                        , reflˢ (numeral (suc (lower n))) ∣₁
                 , numeral-suc (lower n) x .snd (∣ inr x≈n ∣₁) ) ∣₁ })
        (subst ⟨_⟩ (specω x) x∈ω)

-- Foundation: host well-foundedness gives the induction form. This is the
-- direction that holds, with nothing else consumed.

foundationFromStrong : isZFModel → FoundationInduction
foundationFromStrong r φ step =
  WFRec.WFI.induction (ModelS.isZFModel.regularity r) {P = P} step
  where
    P : S → Type ℓ
    P x = ⟨ (x ∷ []) ⊨ φ ⟩

-- What does transfer of Replacement's conclusion: the strong field, applied
-- under its own host-contractible functionality hypothesis, yields the image
-- set as a truncated existential with the internal biconditional
-- specification. See the header for why the hypothesis cannot be obtained from
-- Bell's Collection premise.

imageFromStrong : isZFModel
  → (a : S) (φ : Formula S 2)
  → ((x : S) → ⟨ x ∈ˢ a ⟩ → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
  → ⟨ ⋁ S (λ b → ⋀ S (λ y → iff (y ∈ˢ b)
       (⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))))) ⟩
imageFromStrong r a φ fc =
  let (b , sp) = ModelS.isZFModel.hasReplacement r a φ fc .fst
  in ∣ b , spec-to-iff b _ sp ∣₁

-- Choice: the strong choice field's contractible fibres give, for each member
-- x of a, a point of the strong model's derived intersection c ∩ x, unique up
-- to host paths; EqRefl reflects those paths into ≈ˢ for the internal
-- uniqueness conjunct.

choiceFromStrong : EqRefl → isZFCModel → ChoiceSet
choiceFromStrong reflˢ r a nonempty disjoint =
  PT.rec choice-prop (λ { (c , h) → ∣ c , point c h ∣₁ })
    (ModelS.isZFCModel.hasChoice r a nonempty disjoint)
  where
    open ModelS.isZFModel (ModelS.isZFCModel.zf r) using ( _∩_; ∩-spec )

    choice-reading : S → Ω
    choice-reading c = ⋀ S (λ x → (x ∈ˢ a) ⇒
      ( (⋁ S (λ z → (z ∈ˢ c) ⊓ (z ∈ˢ x)))
      ⊓ (⋀ S (λ z → ⋀ S (λ z' → (((z ∈ˢ c) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ c) ⊓ (z' ∈ˢ x)))
          ⇒ (z ≈ˢ z'))))))

    choice-prop : isProp ⟨ ⋁ S choice-reading ⟩
    choice-prop = snd (⋁ S choice-reading)

    point : (c : S)
      → ((x : S) → ⟨ x ∈ˢ a ⟩
           → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩))
      → ⟨ choice-reading c ⟩
    point c h x x∈a =
      (∣ z₀ , subst ⟨_⟩ (∩-spec c x z₀) (h x x∈a .fst .snd) ∣₁
      , uniqueness)
      where
        z₀ : S
        z₀ = h x x∈a .fst .fst

        uniqueness : ⟨ ⋀ S (λ z → ⋀ S (λ z' →
          (((z ∈ˢ c) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ c) ⊓ (z' ∈ˢ x))) ⇒ (z ≈ˢ z'))) ⟩
        uniqueness z z' ((zc , zx) , (z'c , z'x)) =
          subst (λ w → ⟨ z ≈ˢ w ⟩)
            (cong fst (sym (h x x∈a .snd (z , into c x z zc zx))
                        ∙ h x x∈a .snd (z' , into c x z' z'c z'x)))
            (reflˢ z)
          where
            into : (c' : S) (x' : S) (w : S) → ⟨ w ∈ˢ c' ⟩ → ⟨ w ∈ˢ x' ⟩
                 → ⟨ w ∈ˢ (c' ∩ x') ⟩
            into c' x' w wc wx = subst ⟨_⟩ (sym (∩-spec c' x' w)) (wc , wx)
```

### ProfileFromL.agda

K1-a: the actual L instance.

SHA-256: `92588938da17f353de7568efd0bab64e63145f1382a97a40ab86fffe3865168b`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

-- K1 probe D: the ordinary profile at the actual constructible structure.
-- The only hypothesis is the single LEM (ℓ-suc ℓ) that L⊨ZFC already takes.
--
-- Two facts about 𝒮ʟ do the work that the generic transfer of probe C could
-- not. First, 𝒮ʟ is a restriction of 𝒮ᵥ, whose equality field is host path
-- equality, so ⟨ a ≈ˢ b ⟩ is literally fst a ≡ fst b and EqRefl holds by refl;
-- this closes the Extensionality, Infinity and Choice transfers. Second, L's
-- existential reflection machinery (L.ExistentialReflection) answers Bell's
-- Collection premise for a fixed matrix: for each environment there is a
-- least constructible stage holding a witness, and the answering stages of
-- all environments drawn from one stage have a common ordinal bound, which is
-- then realized as the stage set LsetS β, a member of the model.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )

module ProfileFromL {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; layer-trans; Lset-layer )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At; _^_ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Ordinal {ℓ} using ( boundingOrd; bound2 )
import Cubical.Induction.WellFounded as WFRec
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open import OrdinaryProfile 𝒮ʟ
  using ( iff; iff-intro; spec-to-iff; iff-to-spec
        ; Extensionality; Pairing; Union; PowerSet; Infinity; Separation
        ; Collection; FoundationInduction; ChoiceSet
        ; OrdinaryZF; OrdinaryZFC )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open At S id using ( _⊨_ )

module Instance (lem : LEM (ℓ-suc ℓ)) where

  open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
  open import L.ExistentialReflection {ℓ} lem
    using ( Sat; Wit; pickStage; pickStage-ord; pickWitness
          ; LsetEnv; indexEnv; Below )
  open import L.Model {ℓ} lem using ( L⊨ZFC )
  import FOL.ZFModel
  module ModelL = FOL.ZFModel 𝒮ʟ
  open ModelL using ( isZFModel; isZFCModel; ℩-spec )
  open ModelL.isZFModel (ModelL.isZFCModel.zf L⊨ZFC)
    using ( extensional; regularity; hasPair; hasUnion; hasPower
          ; hasSeparation; numeral; numeral-zero; numeral-suc; hasInfinity
          ; ω; isNumeral; _∩_; ∩-spec )
  open ModelL.isZFCModel L⊨ZFC using ( hasChoice )

  reflˢ : (x : S) → ⟨ x ≈ˢ x ⟩
  reflˢ x = refl {x = fst x}

  extensionalL : Extensionality
  extensionalL a b same =
    cong fst (extensional {a} {b} (iff-to-spec a b same))

  pairL : Pairing
  pairL a b =
    let (p , sp) = hasPair a b .fst
    in ∣ p , spec-to-iff p _ sp ∣₁

  unionL : Union
  unionL a =
    let (v , sp) = hasUnion a .fst
    in ∣ v , spec-to-iff v _ sp ∣₁

  powerL : PowerSet
  powerL a =
    let (v , sp) = hasPower a .fst
    in ∣ v , spec-to-iff v _ sp ∣₁

  separationL : Separation
  separationL a φ =
    let (s , sp) = hasSeparation a φ .fst
    in ∣ s , spec-to-iff s _ sp ∣₁

  foundationL : FoundationInduction
  foundationL φ step =
    WFRec.WFI.induction regularity {P = λ x → ⟨ (x ∷ []) ⊨ φ ⟩} step

  infinityL : Infinity
  infinityL =
    ∣ ω , ∣ numeral zero , (e∈ω , empty-e) ∣₁ , succ-closed ∣₁
    where
      specω : (x : S) → (x ∈ˢ ω) ≡ (isNumeral x)
      specω = ℩-spec hasInfinity

      e∈ω : ⟨ numeral zero ∈ˢ ω ⟩
      e∈ω = subst ⟨_⟩ (sym (specω (numeral zero)))
        ∣ lift zero , reflˢ (numeral zero) ∣₁

      empty-e : ⟨ ⋀ S (λ z → (z ∈ˢ numeral zero) ⇒ ⊥) ⟩
      empty-e z h = Empty.rec (numeral-zero z h)

      succ-closed : ⟨ ⋀ S (λ x → (x ∈ˢ ω) ⇒ (⋁ S (λ y → (y ∈ˢ ω) ⊓ (x ∈ˢ y)))) ⟩
      succ-closed x x∈ω =
        PT.rec (snd (⋁ S (λ y → (y ∈ˢ ω) ⊓ (x ∈ˢ y))))
          (λ { (n , x≈n) →
               ∣ numeral (suc (lower n))
                 , ( subst ⟨_⟩ (sym (specω (numeral (suc (lower n)))))
                       ∣ lift (suc (lower n))
                          , reflˢ (numeral (suc (lower n))) ∣₁
                   , numeral-suc (lower n) x .snd (∣ inr x≈n ∣₁) ) ∣₁ })
          (subst ⟨_⟩ (specω x) x∈ω)

  replacementL : Collection
  replacementL a φ total = ∣ boundStage , member-witness ∣₁
    where
      sa : V ℓ
      sa = stage (fst a) (a .snd)

      oSa : IsOrd sa
      oSa = stage-ord (fst a) (a .snd)

      fa∈sa : ⟨ fst a ∈ Lset sa ⟩
      fa∈sa = stage-mem (fst a) (a .snd)

      answer : ⟪ Lset sa ⟫ ^ 1 → V ℓ
      answer ms = pickStage φ (LsetEnv sa oSa ms)

      answered : Σ[ β ∈ V ℓ ] (IsOrd β
                   × ((ms : ⟪ Lset sa ⟫ ^ 1) → ⟨ answer ms ∈ β ⟩)
                   × ⟨ sa ∈ β ⟩)
      answered =
        let b = boundingOrd (⟪ Lset sa ⟫ ^ 1) answer
                  (λ ms → pickStage-ord φ (LsetEnv sa oSa ms))
            m = bound2 (b .fst) sa (b .snd .fst) oSa
        in m .fst , (m .snd .fst , (λ ms →
             m .snd .fst .fst (b .snd .snd ms) (m .snd .snd .fst))
           , m .snd .snd .snd)

      β : V ℓ
      β = answered .fst

      oβ : IsOrd β
      oβ = answered .snd .fst

      boundStage : S
      boundStage = LsetS β oβ

      member-witness : (x : S) → ⟨ x ∈ˢ a ⟩
        → ⟨ ⋁ S (λ y → (y ∈ˢ boundStage) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩
      member-witness x x∈a =
        PT.map pack (pickWitness φ ρ₀ premise₀)
        where
          below : Below sa (x ∷ [])
          below = layer-trans (Lset-layer sa) x∈a fa∈sa , tt*

          chosen : Σ[ ms ∈ ⟪ Lset sa ⟫ ^ 1 ]
                     (LsetEnv sa oSa ms ≡ (x ∷ []))
          chosen = indexEnv sa oSa (x ∷ []) below

          ρ₀ : S ^ 1
          ρ₀ = LsetEnv sa oSa (chosen .fst)

          e : ρ₀ ≡ (x ∷ [])
          e = chosen .snd

          premise₀ : ⟨ ⋁ S (λ y → (y ∷ ρ₀) ⊨ φ) ⟩
          premise₀ = subst ⟨_⟩
            (sym (cong (λ r → ⋁ S (λ y → (y ∷ r) ⊨ φ)) e)) (total x x∈a)

          ps∈β : ⟨ pickStage φ ρ₀ ∈ β ⟩
          ps∈β = answered .snd .snd .fst (chosen .fst)

          pack : Σ[ q ∈ S ] (⟨ fst q ∈ Lset (pickStage φ ρ₀) ⟩ × ⟨ Sat φ ρ₀ q ⟩)
               → Σ[ q ∈ S ] (⟨ q ∈ˢ boundStage ⟩ × ⟨ (q ∷ x ∷ []) ⊨ φ ⟩)
          pack (q , q∈ps , satq) =
            q , ( Lset-mono ps∈β q∈ps
                , subst ⟨_⟩ (cong (λ r → (q ∷ r) ⊨ φ) e) satq )

  choiceL : ChoiceSet
  choiceL a nonempty disjoint =
    PT.rec choice-prop (λ { (c , h) → ∣ c , point c h ∣₁ })
      (hasChoice a nonempty disjoint)
    where
      choice-reading : S → Ω
      choice-reading c = ⋀ S (λ x → (x ∈ˢ a) ⇒
        ( (⋁ S (λ z → (z ∈ˢ c) ⊓ (z ∈ˢ x)))
        ⊓ (⋀ S (λ z → ⋀ S (λ z' → (((z ∈ˢ c) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ c) ⊓ (z' ∈ˢ x)))
            ⇒ (z ≈ˢ z'))))))

      choice-prop : isProp ⟨ ⋁ S choice-reading ⟩
      choice-prop = snd (⋁ S choice-reading)

      point : (c : S)
        → ((x : S) → ⟨ x ∈ˢ a ⟩
             → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩))
        → ⟨ choice-reading c ⟩
      point c h x x∈a =
        ( ∣ z₀ , subst ⟨_⟩ (∩-spec c x z₀) (h x x∈a .fst .snd) ∣₁
        , uniqueness )
        where
          z₀ : S
          z₀ = h x x∈a .fst .fst

          uniqueness : ⟨ ⋀ S (λ z → ⋀ S (λ z' →
            (((z ∈ˢ c) ⊓ (z ∈ˢ x)) ⊓ ((z' ∈ˢ c) ⊓ (z' ∈ˢ x))) ⇒ (z ≈ˢ z'))) ⟩
          uniqueness z z' ((zc , zx) , (z'c , z'x)) =
            subst (λ w → ⟨ z ≈ˢ w ⟩)
              (cong fst (sym (h x x∈a .snd (z , into c x z zc zx))
                          ∙ h x x∈a .snd (z' , into c x z' z'c z'x)))
              (reflˢ z)
            where
              into : (c' : S) (x' : S) (w : S) → ⟨ w ∈ˢ c' ⟩ → ⟨ w ∈ˢ x' ⟩
                   → ⟨ w ∈ˢ (c' ∩ x') ⟩
              into c' x' w wc wx = subst ⟨_⟩ (sym (∩-spec c' x' w)) (wc , wx)

  L-ordinaryZF : OrdinaryZF
  L-ordinaryZF = record
    { extensional    = extensionalL
    ; hasPair        = pairL
    ; hasUnion       = unionL
    ; hasPower       = powerL
    ; hasInfinity    = infinityL
    ; hasSeparation  = separationL
    ; hasReplacement = replacementL
    ; foundation     = foundationL }

  L-ordinaryZFC : OrdinaryZFC
  L-ordinaryZFC = record { zf = L-ordinaryZF ; hasChoice = choiceL }

Lʟ-ordinary : (lem : LEM (ℓ-suc ℓ)) → OrdinaryZFC
Lʟ-ordinary lem = Instance.L-ordinaryZFC lem
```

### CardinalBridge.agda

K1-b: the cardinal vocabulary and its semantic bridges.

SHA-256: `cd0833204bef4c144d7b2f49cddbedeaeac735650b4fe39d204633f28a8b5985`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

-- K1-b probe B1: the object-language cardinal vocabulary and its semantic
-- bridges, structure-polymorphic over any 𝒮 : ZFStructure (hPropAlgebra ℓ).
-- No import below begins with L. or V.; that is checked by grep in the report.
--
-- The syntax has no function symbols, so every operation is a defined FORMULA
-- relating its arguments: "p is an ordered pair of x and y", never "the pair".
-- Each bridge lemma is a path of hProps between the evaluator's reading of the
-- formula and a host predicate written with _∈ˢ_, _≈ˢ_ and the hProp
-- algebra's own ⋀ and ⋁, so the host side carries exactly the truncation the
-- evaluator uses and never mentions host path equality where the formula says
-- _≐_.
--
-- Variable juggling inside larger formulas is done by FOL.Manipulation.Renaming
-- (renameFo with the correctness theorem Sat.⊨-rename), reusing the same
-- device K1-a used for a transposition.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module CardinalBridge {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ¬̇_; ∃̇_; ∀̇_
        ; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import OrdinaryProfile 𝒮 using ( iff )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open Ren using ( Agrees; ⊨-rename )

infixr 11 _↔̇_

-- The object-language biconditional, spelled from the primitive connectives.

_↔̇_ : ∀ {K : Type ℓ} {n : ℕ} → Formula K n → Formula K n → Formula K n
φ ↔̇ ψ = (φ ⇒̇ ψ) ∧̇ (ψ ⇒̇ φ)

-- Two bottoms meet whenever a bridge passes through a negated subformula. The
-- syntax expands ¬̇ φ to φ ⇒̇ ⊥̇ and the evaluator sends ⊥̇ to the algebra's
-- ⊥, which is ⊥* = Lift ⊥, while the algebra's ¬_ is the library's, built on
-- the unlifted ⊥. They are logically equivalent and not definitionally equal.

¬-as-⇒⊥ : (P : Ω) → (¬ P) ≡ (P ⇒ ⊥)
¬-as-⇒⊥ P = ⇔toPath (λ f p → Empty.rec (f p)) (λ g p → Empty.rec* (g p))

-- A bare refl inside cong₂ over an hProp operation leaves the isProp component
-- of its endpoint undetermined: _⊓_ and _⇒_ build a Σ-pair, so matching the
-- goal fixes the carrier and not the proof of propositionality. Naming the
-- endpoint pins it. Every unchanged component below goes through this.

same : (P : Ω) → P ≡ P
same _ = refl

-- Subset. Env (x ∷ y ∷ []), reading "x ⊆ y".

Subsetφ : Formula S 2
Subsetφ =
  ∀̇ ((var zero ∈̇ var (suc zero)) ⇒̇ (var zero ∈̇ var (suc (suc zero))))

isSubset : S → S → Ω
isSubset x y = ⋀ S (λ z → (z ∈ˢ x) ⇒ (z ∈ˢ y))

Subset-bridge : (x y : S) → ((x ∷ y ∷ []) ⊨ Subsetφ) ≡ (isSubset x y)
Subset-bridge x y = refl

-- Singleton and unordered pair, used inside the Kuratowski pair. Envs
-- (t ∷ x ∷ []) and (t ∷ x ∷ y ∷ []), readings "t = {x}" and "t = {x, y}".

IsSingletonφ : Formula S 2
IsSingletonφ =
  (var (suc zero) ∈̇ var zero)
  ∧̇ (∀̇∈ (var zero) (var zero ≐ var (suc (suc zero))))

isSingleton : S → S → Ω
isSingleton t x =
  (x ∈ˢ t) ⊓ (⋀ S (λ u → (u ∈ˢ t) ⇒ (u ≈ˢ x)))

IsSingleton-bridge : (t x : S)
  → ((t ∷ x ∷ []) ⊨ IsSingletonφ) ≡ (isSingleton t x)
IsSingleton-bridge t x = refl

IsPairφ : Formula S 3
IsPairφ =
  (var (suc zero) ∈̇ var zero)
  ∧̇ ((var (suc (suc zero)) ∈̇ var zero)
  ∧̇ (∀̇∈ (var zero)
       ((var zero ≐ var (suc (suc zero)))
        ∨̇ (var zero ≐ var (suc (suc (suc zero)))))))

isPair : S → S → S → Ω
isPair t x y =
  (x ∈ˢ t) ⊓ ((y ∈ˢ t)
  ⊓ (⋀ S (λ u → (u ∈ˢ t) ⇒ ((u ≈ˢ x) ⊔ (u ≈ˢ y)))))

IsPair-bridge : (t x y : S)
  → ((t ∷ x ∷ y ∷ []) ⊨ IsPairφ) ≡ (isPair t x y)
IsPair-bridge t x y = refl

-- The Kuratowski ordered pair. Env (p ∷ x ∷ y ∷ []), reading
-- "p = {{x}, {x, y}}": every member of p is either the singleton of x or the
-- pair of x and y, and conversely.

PairφK : Formula S 3
PairφK =
  ∀̇ ((var zero ∈̇ var (suc zero))
    ↔̇ (((var (suc (suc zero)) ∈̇ var zero)
        ∧̇ (∀̇∈ (var zero) (var zero ≐ var (suc (suc (suc zero))))))
     ∨̇ ((var (suc (suc zero)) ∈̇ var zero)
        ∧̇ ((var (suc (suc (suc zero))) ∈̇ var zero)
        ∧̇ (∀̇∈ (var zero)
             ((var zero ≐ var (suc (suc (suc zero))))
              ∨̇ (var zero ≐ var (suc (suc (suc (suc zero)))))))))))

isKPair : S → S → S → Ω
isKPair p x y =
  ⋀ S (λ t → iff (t ∈ˢ p) ((isSingleton t x) ⊔ (isPair t x y)))

PairφK-bridge : (p x y : S)
  → ((p ∷ x ∷ y ∷ []) ⊨ PairφK) ≡ (isKPair p x y)
PairφK-bridge p x y = refl

-- Relation. Env (r ∷ []), reading "every member of r is an ordered pair of
-- some two sets". The pair formula is embedded by renaming: inside the two
-- existentials, positions 2, 1, 0 hold p, x, y.

rel-emb : Fin 3 → Fin 4
rel-emb zero              = suc (suc zero)
rel-emb (suc zero)        = suc zero
rel-emb (suc (suc zero))  = zero

IsRelationφ : Formula S 1
IsRelationφ = ∀̇∈ (var zero) (∃̇ (∃̇ (renameFo rel-emb PairφK)))

isRelation : S → Ω
isRelation r =
  ⋀ S (λ p → (p ∈ˢ r) ⇒ (⋁ S (λ x → ⋁ S (λ y → isKPair p x y))))

rel-emb-agrees : (p x y r : S)
  → Ren.Agrees rel-emb (y ∷ x ∷ p ∷ r ∷ []) (p ∷ x ∷ y ∷ [])
rel-emb-agrees p x y r zero              = refl
rel-emb-agrees p x y r (suc zero)        = refl
rel-emb-agrees p x y r (suc (suc zero))  = refl

IsRelation-bridge : (r : S) → ((r ∷ []) ⊨ IsRelationφ) ≡ (isRelation r)
IsRelation-bridge r =
  cong (⋀ S) (funExt (λ p → cong ((p ∈ˢ r) ⇒_) (cong (⋁ S) (funExt (λ x →
    cong (⋁ S) (funExt (λ y →
      ⊨-rename rel-emb PairφK (y ∷ x ∷ p ∷ r ∷ []) (p ∷ x ∷ y ∷ [])
        (rel-emb-agrees p x y r))))))))

-- Function. Env (f ∷ []), reading "f is a relation and single-valued: two
-- pairs of f with the same first component have the same second component".

fn-pair₁ : Fin 3 → Fin 6
fn-pair₁ zero              = suc (suc (suc (suc zero)))
fn-pair₁ (suc zero)        = suc (suc zero)
fn-pair₁ (suc (suc zero))  = suc zero

fn-pair₂ : Fin 3 → Fin 6
fn-pair₂ zero              = suc (suc (suc zero))
fn-pair₂ (suc zero)        = suc (suc zero)
fn-pair₂ (suc (suc zero))  = zero

IsFunctionφ : Formula S 1
IsFunctionφ =
  IsRelationφ
  ∧̇ (∀̇∈ (var zero)
      (∀̇∈ (var (suc zero))
        (∀̇ (∀̇ (∀̇
          (((renameFo fn-pair₁ PairφK) ∧̇ (renameFo fn-pair₂ PairφK))
            ⇒̇ (var (suc zero) ≐ var zero)))))))

isFunction : S → Ω
isFunction f =
  (isRelation f)
  ⊓ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
       (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
         ((isKPair p x y) ⊓ (isKPair q x z)) ⇒ (y ≈ˢ z)))))))))

fn-pair₁-agrees : (p q x y z f : S)
  → Ren.Agrees fn-pair₁ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ []) (p ∷ x ∷ y ∷ [])
fn-pair₁-agrees p q x y z f zero              = refl
fn-pair₁-agrees p q x y z f (suc zero)        = refl
fn-pair₁-agrees p q x y z f (suc (suc zero))  = refl

fn-pair₂-agrees : (p q x y z f : S)
  → Ren.Agrees fn-pair₂ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ []) (q ∷ x ∷ z ∷ [])
fn-pair₂-agrees p q x y z f zero              = refl
fn-pair₂-agrees p q x y z f (suc zero)        = refl
fn-pair₂-agrees p q x y z f (suc (suc zero))  = refl

IsFunction-bridge : (f : S) → ((f ∷ []) ⊨ IsFunctionφ) ≡ (isFunction f)
IsFunction-bridge f =
  cong₂ _⊓_ (IsRelation-bridge f) (cong (⋀ S) (funExt (λ p →
    cong ((p ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ q →
      cong ((q ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ x →
        cong (⋀ S) (funExt (λ y →
          cong (⋀ S) (funExt (λ z →
            cong₂ _⇒_
              (cong₂ _⊓_
                (⊨-rename fn-pair₁ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ [])
                  (p ∷ x ∷ y ∷ []) (fn-pair₁-agrees p q x y z f))
                (⊨-rename fn-pair₂ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ [])
                  (q ∷ x ∷ z ∷ []) (fn-pair₂-agrees p q x y z f)))
              (same (y ≈ˢ z)))))))))))))))

-- Injection. Env (f ∷ a ∷ b ∷ []), reading "f is an injective function with
-- domain exactly a and values in b": a function, total on a, with range in b,
-- and two pairs with the same second component have the same first component.

inj-fun : Fin 1 → Fin 3
inj-fun zero = zero

inj-dom : Fin 3 → Fin 6
inj-dom zero              = zero
inj-dom (suc zero)        = suc (suc zero)
inj-dom (suc (suc zero))  = suc zero

inj-ran : Fin 3 → Fin 6
inj-ran zero              = suc (suc zero)
inj-ran (suc zero)        = suc zero
inj-ran (suc (suc zero))  = zero

inj-pair₁ : Fin 3 → Fin 8
inj-pair₁ zero              = suc (suc (suc (suc zero)))
inj-pair₁ (suc zero)        = suc (suc zero)
inj-pair₁ (suc (suc zero))  = suc zero

inj-pair₂ : Fin 3 → Fin 8
inj-pair₂ zero              = suc (suc (suc zero))
inj-pair₂ (suc zero)        = zero
inj-pair₂ (suc (suc zero))  = suc zero

InjDomφ : Formula S 3
InjDomφ =
  ∀̇∈ (var (suc zero))
       (∃̇ (∃̇ ((var zero ∈̇ var (suc (suc (suc zero))))
            ∧̇ (renameFo inj-dom PairφK))))

InjRanφ : Formula S 3
InjRanφ =
  ∀̇∈ (var zero)
       (∀̇ (∀̇ ((renameFo inj-ran PairφK)
            ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero)))))))))

InjPairφ : Formula S 3
InjPairφ =
  ∀̇∈ (var zero)
       (∀̇∈ (var (suc zero))
         (∀̇ (∀̇ (∀̇ (((renameFo inj-pair₁ PairφK) ∧̇ (renameFo inj-pair₂ PairφK))
                  ⇒̇ (var (suc (suc zero)) ≐ var zero))))))

IsInjectionφ : Formula S 3
IsInjectionφ =
  (renameFo inj-fun IsFunctionφ)
  ∧̇ (InjDomφ
  ∧̇ (InjRanφ
  ∧̇ InjPairφ))

isInjection : S → S → S → Ω
isInjection f a b =
  (isFunction f)
  ⊓ ((⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → ⋁ S (λ p →
       (p ∈ˢ f) ⊓ (isKPair p x y))))))
  ⊓ ((⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ x → ⋀ S (λ y →
       (isKPair p x y) ⇒ (y ∈ˢ b))))))
  ⊓ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
       (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
         ((isKPair p x y) ⊓ (isKPair q z y)) ⇒ (x ≈ˢ z)))))))))))

inj-fun-agrees : (f a b : S)
  → Ren.Agrees inj-fun (f ∷ a ∷ b ∷ []) (f ∷ [])
inj-fun-agrees f a b zero = refl

inj-dom-agrees : (p x y f a b : S)
  → Ren.Agrees inj-dom (p ∷ y ∷ x ∷ f ∷ a ∷ b ∷ []) (p ∷ x ∷ y ∷ [])
inj-dom-agrees p x y f a b zero              = refl
inj-dom-agrees p x y f a b (suc zero)        = refl
inj-dom-agrees p x y f a b (suc (suc zero))  = refl

inj-ran-agrees : (p x y f a b : S)
  → Ren.Agrees inj-ran (y ∷ x ∷ p ∷ f ∷ a ∷ b ∷ []) (p ∷ x ∷ y ∷ [])
inj-ran-agrees p x y f a b zero              = refl
inj-ran-agrees p x y f a b (suc zero)        = refl
inj-ran-agrees p x y f a b (suc (suc zero))  = refl

inj-pair₁-agrees : (p q x y z f a b : S)
  → Ren.Agrees inj-pair₁ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
                     (p ∷ x ∷ y ∷ [])
inj-pair₁-agrees p q x y z f a b zero              = refl
inj-pair₁-agrees p q x y z f a b (suc zero)        = refl
inj-pair₁-agrees p q x y z f a b (suc (suc zero))  = refl

inj-pair₂-agrees : (p q x y z f a b : S)
  → Ren.Agrees inj-pair₂ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
                     (q ∷ z ∷ y ∷ [])
inj-pair₂-agrees p q x y z f a b zero              = refl
inj-pair₂-agrees p q x y z f a b (suc zero)        = refl
inj-pair₂-agrees p q x y z f a b (suc (suc zero))  = refl

InjDom-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ InjDomφ)
    ≡ (⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → ⋁ S (λ p →
         (p ∈ˢ f) ⊓ (isKPair p x y))))))
InjDom-bridge f a b =
  cong (⋀ S) (funExt (λ x → cong ((x ∈ˢ a) ⇒_) (cong (⋁ S) (funExt (λ y →
    cong (⋁ S) (funExt (λ p → cong₂ _⊓_ (same (p ∈ˢ f))
      (⊨-rename inj-dom PairφK (p ∷ y ∷ x ∷ f ∷ a ∷ b ∷ [])
        (p ∷ x ∷ y ∷ []) (inj-dom-agrees p x y f a b)))))))))

InjRan-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ InjRanφ)
    ≡ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ x → ⋀ S (λ y →
         (isKPair p x y) ⇒ (y ∈ˢ b))))))
InjRan-bridge f a b =
  cong (⋀ S) (funExt (λ p → cong ((p ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ x →
    cong (⋀ S) (funExt (λ y → cong₂ _⇒_
      (⊨-rename inj-ran PairφK (y ∷ x ∷ p ∷ f ∷ a ∷ b ∷ [])
        (p ∷ x ∷ y ∷ []) (inj-ran-agrees p x y f a b))
      (same (y ∈ˢ b)))))))))

InjPair-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ InjPairφ)
    ≡ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
         (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
           ((isKPair p x y) ⊓ (isKPair q z y)) ⇒ (x ≈ˢ z)))))))))
InjPair-bridge f a b =
  cong (⋀ S) (funExt (λ p → cong ((p ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ q →
    cong ((q ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ x →
      cong (⋀ S) (funExt (λ y → cong (⋀ S) (funExt (λ z → cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename inj-pair₁ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
            (p ∷ x ∷ y ∷ []) (inj-pair₁-agrees p q x y z f a b))
          (⊨-rename inj-pair₂ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
            (q ∷ z ∷ y ∷ []) (inj-pair₂-agrees p q x y z f a b)))
        (same (x ≈ˢ z))))))))))))))

InjFun-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ (renameFo inj-fun IsFunctionφ)) ≡ (isFunction f)
InjFun-bridge f a b =
  ⊨-rename inj-fun IsFunctionφ (f ∷ a ∷ b ∷ []) (f ∷ [])
    (inj-fun-agrees f a b)
  ∙ IsFunction-bridge f

IsInjection-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ IsInjectionφ) ≡ (isInjection f a b)
IsInjection-bridge f a b =
  cong₂ _⊓_ (InjFun-bridge f a b)
    (cong₂ _⊓_ (InjDom-bridge f a b)
      (cong₂ _⊓_ (InjRan-bridge f a b) (InjPair-bridge f a b)))

-- Injectable, the internal cardinal comparison. Env (x ∷ y ∷ []), reading
-- "some injection carries x into y". The bound variable sits at position 0
-- with x and y at 1 and 2, so the injection formula applies unrenamed.

Injectableφ : Formula S 2
Injectableφ = ∃̇ IsInjectionφ

injectable : S → S → Ω
injectable x y = ⋁ S (λ f → isInjection f x y)

Injectable-bridge : (x y : S)
  → ((x ∷ y ∷ []) ⊨ Injectableφ) ≡ (injectable x y)
Injectable-bridge x y =
  cong (⋁ S) (funExt (λ f → IsInjection-bridge f x y))

-- Successor of a set. Env (y ∷ x ∷ []), reading "y = x ∪ {x}".

IsSuccOfφ : Formula S 2
IsSuccOfφ =
  (var (suc zero) ∈̇ var zero)
  ∧̇ ((∀̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero)))
  ∧̇ (∀̇∈ (var zero)
       ((var zero ∈̇ var (suc (suc zero)))
        ∨̇ (var zero ≐ var (suc (suc zero))))))

isSuccOf : S → S → Ω
isSuccOf y x =
  (x ∈ˢ y)
  ⊓ ((⋀ S (λ z → (z ∈ˢ x) ⇒ (z ∈ˢ y)))
  ⊓ (⋀ S (λ z → (z ∈ˢ y) ⇒ ((z ∈ˢ x) ⊔ (z ≈ˢ x)))))

IsSuccOf-bridge : (y x : S)
  → ((y ∷ x ∷ []) ⊨ IsSuccOfφ) ≡ (isSuccOf y x)
IsSuccOf-bridge y x = refl

-- Inductive. Env (u ∷ []). The closure is by the SUCCESSOR operation, not
-- Bell's "every member has a member above it": a Bell-inductive set need not
-- contain any numeral beyond the empty set, since u = {∅} together with an
-- ascending chain of pairs {{∅, junk}, ...} is Bell-inductive while missing
-- {∅}. Under successor closure the least inductive set exists and behaves,
-- which is what IsOmegaφ below needs.

wk2 : Fin 2 → Fin 3
wk2 zero       = zero
wk2 (suc zero) = suc zero

wk2-agrees : (y x u : S)
  → Ren.Agrees wk2 (y ∷ x ∷ u ∷ []) (y ∷ x ∷ [])
wk2-agrees y x u zero       = refl
wk2-agrees y x u (suc zero) = refl

IsInductiveφ : Formula S 1
IsInductiveφ =
  (∃̇∈ (var zero) (∀̇∈ (var zero) ⊥̇))
  ∧̇ (∀̇∈ (var zero) (∃̇∈ (var (suc zero)) (renameFo wk2 IsSuccOfφ)))

isInductive : S → Ω
isInductive u =
  (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ w → (w ∈ˢ e) ⇒ ⊥))))
  ⊓ (⋀ S (λ x → (x ∈ˢ u) ⇒ (⋁ S (λ y → (y ∈ˢ u) ⊓ (isSuccOf y x)))))

IsInductive-bridge : (u : S) → ((u ∷ []) ⊨ IsInductiveφ) ≡ (isInductive u)
IsInductive-bridge u =
  cong₂ _⊓_ (same (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ w → (w ∈ˢ e) ⇒ ⊥)))))
    (cong (⋀ S) (funExt (λ x → cong ((x ∈ˢ u) ⇒_) (cong (⋁ S) (funExt (λ y →
      cong₂ _⊓_ (same (y ∈ˢ u))
        (⊨-rename wk2 IsSuccOfφ (y ∷ x ∷ u ∷ []) (y ∷ x ∷ [])
          (wk2-agrees y x u))))))))

-- Omega. Env (w ∷ []), reading "w is inductive and every member of w belongs
-- to every inductive set".

wk1 : Fin 1 → Fin 2
wk1 zero = zero

wk1-agrees : (i w : S) → Ren.Agrees wk1 (i ∷ w ∷ []) (i ∷ [])
wk1-agrees i w zero = refl

IsOmegaφ : Formula S 1
IsOmegaφ =
  IsInductiveφ
  ∧̇ (∀̇ ((renameFo wk1 IsInductiveφ)
        ⇒̇ (∀̇∈ (var (suc zero)) ((var zero) ∈̇ (var (suc zero))))))

isOmega : S → Ω
isOmega w =
  (isInductive w)
  ⊓ (⋀ S (λ i → (isInductive i) ⇒ (⋀ S (λ v → (v ∈ˢ w) ⇒ (v ∈ˢ i)))))

IsOmega-bridge : (w : S) → ((w ∷ []) ⊨ IsOmegaφ) ≡ (isOmega w)
IsOmega-bridge w =
  cong₂ _⊓_ (same (isInductive w))
    (cong (⋀ S) (funExt (λ i → cong₂ _⇒_
      (⊨-rename wk1 IsInductiveφ (i ∷ w ∷ []) (i ∷ []) (wk1-agrees i w))
      (same (⋀ S (λ v → (v ∈ˢ w) ⇒ (v ∈ˢ i)))))))

-- Power set. Env (p ∷ a ∷ []), reading "the members of p are exactly the
-- subsets of a".

pow-emb : Fin 2 → Fin 3
pow-emb zero       = zero
pow-emb (suc zero) = suc (suc zero)

IsPowerSetφ : Formula S 2
IsPowerSetφ =
  ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇ (renameFo pow-emb Subsetφ))

isPowerSet : S → S → Ω
isPowerSet p a = ⋀ S (λ x → iff (x ∈ˢ p) (isSubset x a))

pow-emb-agrees : (x p a : S)
  → Ren.Agrees pow-emb (x ∷ p ∷ a ∷ []) (x ∷ a ∷ [])
pow-emb-agrees x p a zero       = refl
pow-emb-agrees x p a (suc zero) = refl

IsPowerSet-bridge : (p a : S)
  → ((p ∷ a ∷ []) ⊨ IsPowerSetφ) ≡ (isPowerSet p a)
IsPowerSet-bridge p a =
  cong (⋀ S) (funExt (λ x →
    cong₂ _⊓_
      (cong₂ _⇒_ (same (x ∈ˢ p))
        (⊨-rename pow-emb Subsetφ (x ∷ p ∷ a ∷ []) (x ∷ a ∷ [])
          (pow-emb-agrees x p a)))
      (cong₂ _⇒_
        (⊨-rename pow-emb Subsetφ (x ∷ p ∷ a ∷ []) (x ∷ a ∷ [])
          (pow-emb-agrees x p a))
        (same (x ∈ˢ p)))))

-- Transitive set. Env (a ∷ []).

IsTransitiveφ : Formula S 1
IsTransitiveφ =
  ∀̇∈ (var zero) (∀̇∈ (var zero) ((var zero) ∈̇ (var (suc (suc zero)))))

isTransitiveSet : S → Ω
isTransitiveSet a =
  ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a))))

IsTransitive-bridge : (a : S)
  → ((a ∷ []) ⊨ IsTransitiveφ) ≡ (isTransitiveSet a)
IsTransitive-bridge a = refl

-- Ordinal. Env (α ∷ []), reading "α is transitive and membership linearly
-- orders α". No well-foundedness: the only well-foundedness the ordinary
-- profile has is the induction form Foundation field, and a Cohen quotient has
-- nothing else.

IsOrdinalφ : Formula S 1
IsOrdinalφ =
  IsTransitiveφ
  ∧̇ (∀̇∈ (var zero)
       (∀̇∈ (var (suc zero))
         (((var (suc zero)) ∈̇ (var zero))
          ∨̇ (((var (suc zero)) ≐ (var zero))
           ∨̇ ((var zero) ∈̇ (var (suc zero)))))))

isOrdinal : S → Ω
isOrdinal α =
  (isTransitiveSet α)
  ⊓ (⋀ S (λ x → (x ∈ˢ α) ⇒ (⋀ S (λ y → (y ∈ˢ α) ⇒
       ((x ∈ˢ y) ⊔ ((x ≈ˢ y) ⊔ (y ∈ˢ x)))))))

IsOrdinal-bridge : (α : S)
  → ((α ∷ []) ⊨ IsOrdinalφ) ≡ (isOrdinal α)
IsOrdinal-bridge α = refl

-- Cardinal. Env (κ ∷ []), reading "κ is an ordinal that does not inject into
-- any strictly smaller ordinal". Smaller is membership, the von Neumann order.

swap21 : Fin 2 → Fin 2
swap21 zero       = suc zero
swap21 (suc zero) = zero

IsCardinalφ : Formula S 1
IsCardinalφ =
  IsOrdinalφ
  ∧̇ (∀̇∈ (var zero) (¬̇ (renameFo swap21 Injectableφ)))

isCardinal : S → Ω
isCardinal κ =
  (isOrdinal κ)
  ⊓ (⋀ S (λ β → (β ∈ˢ κ) ⇒ ¬ (injectable κ β)))

swap21-agrees : (κ β : S)
  → Ren.Agrees swap21 (β ∷ κ ∷ []) (κ ∷ β ∷ [])
swap21-agrees κ β zero       = refl
swap21-agrees κ β (suc zero) = refl

IsCardinal-bridge : (κ : S)
  → ((κ ∷ []) ⊨ IsCardinalφ) ≡ (isCardinal κ)
IsCardinal-bridge κ =
  cong₂ _⊓_ (IsOrdinal-bridge κ)
    (cong (⋀ S) (funExt (λ β → cong ((β ∈ˢ κ) ⇒_)
      (cong (_⇒ ⊥)
        (⊨-rename swap21 Injectableφ (β ∷ κ ∷ []) (κ ∷ β ∷ [])
          (swap21-agrees κ β)
         ∙ Injectable-bridge κ β)
       ∙ sym (¬-as-⇒⊥ (injectable κ β))))))

-- Successor cardinal. Env (δ ∷ κ ∷ []), reading "δ is a cardinal strictly
-- above κ and below-or-equal to every cardinal strictly above κ".

sc-emb : Fin 1 → Fin 2
sc-emb zero = zero

sc-emb-mu : Fin 1 → Fin 3
sc-emb-mu zero = zero

IsSuccCardinalφ : Formula S 2
IsSuccCardinalφ =
  (renameFo sc-emb IsCardinalφ)
  ∧̇ ((var (suc zero) ∈̇ var zero)
  ∧̇ (∀̇ (((renameFo sc-emb-mu IsCardinalφ)
        ∧̇ ((var (suc (suc zero))) ∈̇ (var zero)))
       ⇒̇ (((var (suc zero)) ≐ (var zero))
        ∨̇ ((var (suc zero)) ∈̇ (var zero))))))

isSuccCardinal : S → S → Ω
isSuccCardinal δ κ =
  (isCardinal δ)
  ⊓ ((κ ∈ˢ δ)
  ⊓ (⋀ S (λ μ → ((isCardinal μ) ⊓ (κ ∈ˢ μ))
       ⇒ ((δ ≈ˢ μ) ⊔ (δ ∈ˢ μ)))))

sc-emb-agrees : (δ κ : S) → Ren.Agrees sc-emb (δ ∷ κ ∷ []) (δ ∷ [])
sc-emb-agrees δ κ zero = refl

sc-emb-mu-agrees : (μ δ κ : S)
  → Ren.Agrees sc-emb-mu (μ ∷ δ ∷ κ ∷ []) (μ ∷ [])
sc-emb-mu-agrees μ δ κ zero = refl

IsSuccCardinal-bridge : (δ κ : S)
  → ((δ ∷ κ ∷ []) ⊨ IsSuccCardinalφ) ≡ (isSuccCardinal δ κ)
IsSuccCardinal-bridge δ κ =
  cong₂ _⊓_
    (⊨-rename sc-emb IsCardinalφ (δ ∷ κ ∷ []) (δ ∷ []) (sc-emb-agrees δ κ)
     ∙ IsCardinal-bridge δ)
    (cong₂ _⊓_ (same (κ ∈ˢ δ))
      (cong (⋀ S) (funExt (λ μ → cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename sc-emb-mu IsCardinalφ (μ ∷ δ ∷ κ ∷ []) (μ ∷ [])
            (sc-emb-mu-agrees μ δ κ)
           ∙ IsCardinal-bridge μ)
          (same (κ ∈ˢ μ)))
        (same ((δ ≈ˢ μ) ⊔ (δ ∈ˢ μ)))))))
```

### CHSentence.agda

K1-b: CH, its negation, the omega instance of GCH, and the three agreement theorems.

SHA-256: `0420da6abad9df5b99f0367029a81731819acf66c3871483b3418fbf6e02aeb0`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

-- K1-b probe B2: the continuum hypothesis, its negation, and the omega
-- instance of the generalized continuum hypothesis, as sentences of the
-- object language, each paired with the truth value a host reader would
-- write down, and each with the agreement theorem between the two.
--
-- The agreement theorems are the point. Roadmap section 1 makes them an
-- acceptance condition of T3: "The semantic CH predicate and its
-- object-language sentence must agree; likewise for the omega-instance of
-- GCH." Without them a proof that the negation has Boolean value top would
-- say nothing about the model actually having many reals.
--
-- The syntax has no function symbols, so neither omega nor the power set can
-- appear as a term. Both sentences universally quantify over a w that is
-- omega and a p that is its power set, and say nothing when no such pair
-- exists. Existence is a separate matter, supplied by the profile's Infinity
-- and Power Set fields, not by these sentences.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module CHSentence {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo )
open import CardinalBridge 𝒮

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

open Ren using ( ⊨-rename )

-- Renamings into the two-variable context (p ∷ w ∷ []).

om-w : Fin 1 → Fin 2
om-w zero = suc zero

om-w-agrees : (p w : S) → Ren.Agrees om-w (p ∷ w ∷ []) (w ∷ [])
om-w-agrees p w zero = refl

-- Renamings into the three-variable context (x ∷ p ∷ w ∷ []).

inj-wx : Fin 2 → Fin 3
inj-wx zero       = suc (suc zero)
inj-wx (suc zero) = zero

inj-xw : Fin 2 → Fin 3
inj-xw zero       = zero
inj-xw (suc zero) = suc (suc zero)

inj-px : Fin 2 → Fin 3
inj-px zero       = suc zero
inj-px (suc zero) = zero

inj-wx-agrees : (x p w : S) → Ren.Agrees inj-wx (x ∷ p ∷ w ∷ []) (w ∷ x ∷ [])
inj-wx-agrees x p w zero       = refl
inj-wx-agrees x p w (suc zero) = refl

inj-xw-agrees : (x p w : S) → Ren.Agrees inj-xw (x ∷ p ∷ w ∷ []) (x ∷ w ∷ [])
inj-xw-agrees x p w zero       = refl
inj-xw-agrees x p w (suc zero) = refl

inj-px-agrees : (x p w : S) → Ren.Agrees inj-px (x ∷ p ∷ w ∷ []) (p ∷ x ∷ [])
inj-px-agrees x p w zero       = refl
inj-px-agrees x p w (suc zero) = refl

inj-xp : Fin 2 → Fin 3
inj-xp zero       = zero
inj-xp (suc zero) = suc zero

inj-xp-agrees : (x p w : S) → Ren.Agrees inj-xp (x ∷ p ∷ w ∷ []) (x ∷ p ∷ [])
inj-xp-agrees x p w zero       = refl
inj-xp-agrees x p w (suc zero) = refl

-- The continuum hypothesis. Reading: for every omega w and every power set p
-- of w, a set that omega injects into and that injects into p either injects
-- back into omega or receives an injection from p. In words, nothing sits
-- strictly between omega and its power set in the injectability preorder.

CHsent : Formula S 0
CHsent =
  ∀̇ (∀̇ (((renameFo om-w IsOmegaφ) ∧̇ IsPowerSetφ)
       ⇒̇ (∀̇ (((renameFo inj-wx Injectableφ)
              ∧̇ (renameFo inj-xp Injectableφ))
            ⇒̇ ((renameFo inj-xw Injectableφ)
             ∨̇ (renameFo inj-px Injectableφ))))))

¬CHsent : Formula S 0
¬CHsent = ¬̇ CHsent

chValue : Ω
chValue =
  ⋀ S (λ w → ⋀ S (λ p → ((isOmega w) ⊓ (isPowerSet p w))
    ⇒ (⋀ S (λ x → ((injectable w x) ⊓ (injectable x p))
         ⇒ ((injectable x w) ⊔ (injectable p x))))))

CH-agrees : ([] ⊨ CHsent) ≡ chValue
CH-agrees =
  cong (⋀ S) (funExt (λ w →
    cong (⋀ S) (funExt (λ p →
      cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename om-w IsOmegaφ (p ∷ w ∷ []) (w ∷ []) (om-w-agrees p w)
           ∙ IsOmega-bridge w)
          (IsPowerSet-bridge p w))
        (cong (⋀ S) (funExt (λ x →
          cong₂ _⇒_
            (cong₂ _⊓_
              (⊨-rename inj-wx Injectableφ (x ∷ p ∷ w ∷ []) (w ∷ x ∷ [])
                (inj-wx-agrees x p w)
               ∙ Injectable-bridge w x)
              (⊨-rename inj-xp Injectableφ (x ∷ p ∷ w ∷ []) (x ∷ p ∷ [])
                (inj-xp-agrees x p w)
               ∙ Injectable-bridge x p))
            (cong₂ _⊔_
              (⊨-rename inj-xw Injectableφ (x ∷ p ∷ w ∷ []) (x ∷ w ∷ [])
                (inj-xw-agrees x p w)
               ∙ Injectable-bridge x w)
              (⊨-rename inj-px Injectableφ (x ∷ p ∷ w ∷ []) (p ∷ x ∷ [])
                (inj-px-agrees x p w)
               ∙ Injectable-bridge p x)))))))))

-- The negation transports through the same agreement. It needs no excluded
-- middle: the only step is the lifted-bottom lemma of CardinalBridge, which
-- reconciles the evaluator's reading of ¬̇ with the algebra's own ¬.

¬CH-agrees : ([] ⊨ ¬CHsent) ≡ (¬ chValue)
¬CH-agrees = cong (_⇒ ⊥) CH-agrees ∙ sym (¬-as-⇒⊥ chValue)

-- Renamings into the three-variable context (d ∷ p ∷ w ∷ []).

sc-dw : Fin 2 → Fin 3
sc-dw zero       = zero
sc-dw (suc zero) = suc (suc zero)

inj-pd : Fin 2 → Fin 3
inj-pd zero       = suc zero
inj-pd (suc zero) = zero

inj-dp : Fin 2 → Fin 3
inj-dp zero       = zero
inj-dp (suc zero) = suc zero

sc-dw-agrees : (d p w : S) → Ren.Agrees sc-dw (d ∷ p ∷ w ∷ []) (d ∷ w ∷ [])
sc-dw-agrees d p w zero       = refl
sc-dw-agrees d p w (suc zero) = refl

inj-pd-agrees : (d p w : S) → Ren.Agrees inj-pd (d ∷ p ∷ w ∷ []) (p ∷ d ∷ [])
inj-pd-agrees d p w zero       = refl
inj-pd-agrees d p w (suc zero) = refl

inj-dp-agrees : (d p w : S) → Ren.Agrees inj-dp (d ∷ p ∷ w ∷ []) (d ∷ p ∷ [])
inj-dp-agrees d p w zero       = refl
inj-dp-agrees d p w (suc zero) = refl

-- The omega instance of the generalized continuum hypothesis, in the shape
-- the existing L theorem uses: the power set of omega is equinumerous with
-- the successor cardinal of omega, equinumerous meaning a pair of injections
-- rather than a bijection.

GCHωsent : Formula S 0
GCHωsent =
  ∀̇ (∀̇ (((renameFo om-w IsOmegaφ) ∧̇ IsPowerSetφ)
       ⇒̇ (∃̇ ((renameFo sc-dw IsSuccCardinalφ)
            ∧̇ ((renameFo inj-pd Injectableφ)
            ∧̇ (renameFo inj-dp Injectableφ))))))

gchωValue : Ω
gchωValue =
  ⋀ S (λ w → ⋀ S (λ p → ((isOmega w) ⊓ (isPowerSet p w))
    ⇒ (⋁ S (λ d → (isSuccCardinal d w)
         ⊓ ((injectable p d) ⊓ (injectable d p))))))

GCHω-agrees : ([] ⊨ GCHωsent) ≡ gchωValue
GCHω-agrees =
  cong (⋀ S) (funExt (λ w →
    cong (⋀ S) (funExt (λ p →
      cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename om-w IsOmegaφ (p ∷ w ∷ []) (w ∷ []) (om-w-agrees p w)
           ∙ IsOmega-bridge w)
          (IsPowerSet-bridge p w))
        (cong (⋁ S) (funExt (λ d →
          cong₂ _⊓_
            (⊨-rename sc-dw IsSuccCardinalφ (d ∷ p ∷ w ∷ []) (d ∷ w ∷ [])
              (sc-dw-agrees d p w)
             ∙ IsSuccCardinal-bridge d w)
            (cong₂ _⊓_
              (⊨-rename inj-pd Injectableφ (d ∷ p ∷ w ∷ []) (p ∷ d ∷ [])
                (inj-pd-agrees d p w)
               ∙ Injectable-bridge p d)
              (⊨-rename inj-dp Injectableφ (d ∷ p ∷ w ∷ []) (d ∷ p ∷ [])
                (inj-dp-agrees d p w)
               ∙ Injectable-bridge d p)))))))))
```

