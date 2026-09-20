# K6 the transfer of the ZFC axioms to the extension structure

Date: 2026-09-12. Source baseline: `cbd1510e`. Branch `research/forcing-cohen-k0`.
Status: K6 COMPLETE on its roadmap scope with one item measured as not reachable
and re-owned, in section 4.4. Ten proof tracks A through J wrote Agda and an
eleventh, Track K, wrote the consolidated assumption ledger and no code.
Twenty-nine files, 8819 lines, every one carrying `--cubical --safe
--guardedness` on line 1. The terminology track is still blocked on the same
owner ruling that blocked K2 through K5 and blocks no code; see section 11. This
record follows the K0 through K5 convention: proof work lives in a task-specific
temporary compile root, the sources are archived outside it, and no repository
source file is changed.

Every line count, hash and token census below was computed for this record from
the archived bytes at `~/Agentic/bedrock-proofs-archive/k6/`, which this record
verified byte-identical to the compile root's final bytes at
`/tmp/bedrock-k6-probes/K6/` by `cmp` over all 29 files, zero differences. No
number here is copied from prose. Track K found three line counts wrong in K5's
reports and several numbers wrong in K6's, and this record found further ones;
where a report and the source disagree the source is the authority and both are
printed.

**Two counting conventions must be named before any number is read.** "Code"
means non-blank lines of the comment-stripped source, where stripping removes
`{- ... -}` with nesting and everything from a `--` token at line start or
preceded by whitespace to end of line. The stripper preserves line breaks, so a
stripped line number equals its source line number and every `file:line` below
is a source line. Under that convention the corpus is **4254 code lines**. The
figure 4283 that circulated in briefs is the same census with the
`{-# OPTIONS --cubical --safe --guardedness #-}` line counted as code: 4254 plus
one per file for 29 files is exactly 4283. Neither is wrong; they are different
conventions and the difference is the pragma. This record uses 4254 throughout.
The second convention is that a token census counts **lines** matching, not
occurrences. Track K's censuses are line counts and this record reproduces them
as such; where occurrences differ from lines the record says which it is
quoting.

## 1. What K6 delivers

The roadmap's K6 transfers the axioms "with one substantive proof per genuinely
different profile", asking for separate obligations for
Extensionality/Foundation, elementary set constructions, Separation, Power Set,
Replacement and AC, for no new ordinals and the identification of ground
naturals, for AC proved separately from ZF, and for every result labelled by its
ground assumptions (`cohen-implementation-roadmap-2026-09.md:207`). Twenty-nine
files:

| File | Track | What | Lines | Code | SHA-256 prefix |
|---|---|---|---|---|---|
| `NameBuild.agda` | A | the ground-side name calculus, route G only | 365 | 198 | `e21c67af6908feb3` |
| `NameValid.agda` | A | validity and the `nameBound` candidate set | 242 | 118 | `a29acf8c9390bcdb` |
| `NameBuildAtGround.agda` | A | the seam, all 31 slots from real K3 exports | 119 | 74 | `1f880ab8db30b65e` |
| `Elementary.agda` | B | `hasPairᴾ` and `hasUnionᵁᴰ` | 781 | 386 | `be149f426c761420` |
| `ElementaryAtStructures.agda` | B | `structure-agrees` by `refl` | 176 | 106 | `d542098e3066d26e` |
| `ElementaryAtNames.agda` | B | Track A's exports supplied | 199 | 134 | `d767cdb7937b8777` |
| `GroundTransfer.agda` | C | `hasInfinity` and the ground naturals | 536 | 175 | `caf68e1a71c83eea` |
| `GroundTransferAtStructures.agda` | C | the structure seam | 155 | 89 | `743eafdf246c8436` |
| `GroundTransferAtCheck.agda` | C | the `chk` seam, and X3's recorded exception | 114 | 59 | `c6ec9d79d289231e` |
| `Foundation.agda` | D | `foundation`, induction form, at an arbitrary `G` | 221 | 64 | `57461c88dfe08884` |
| `FoundationAtStructures.agda` | D | the seam, and K5's NON-CLAIM 3 witnessed | 114 | 59 | `8e08ae5a619cf7ee` |
| `TruthSeam.agda` | E | K5 Track F's surface joined to K5 Track G's truth lemma | 257 | 161 | `930b0a6ad6dc0ca4` |
| `Definability.agda` | E | the constant bridge, `sat-abs` and its variants | 178 | 80 | `e24084c217a05087` |
| `ForcesTruth.agda` | E | the engine, and every conditional hypothesis | 348 | 168 | `5484b18101c7b45a` |
| `ProbeE4.agda` | E | the seam scaffold | 57 | 43 | `398e221e8134b30e` |
| `ProbeE5.agda` | E | the engine applied down to `truth-at` | 143 | 126 | `ce46e660b810479c` |
| `Separation.agda` | F | `hasSeparation` | 467 | 195 | `adb5dc8e07907c21` |
| `SeparationAtStructure.agda` | F | the seam, four `refl` identifications | 182 | 98 | `6bdce5ed052cb937` |
| `Power.agda` | G | `hasPower`, by the ZF route | 605 | 273 | `fe988e392cabf9ad` |
| `PowerAtNames.agda` | G | `structure-agrees` and `field-agrees`, both `refl` | 107 | 63 | `2a9a216389f3f0b3` |
| `PowerAtNameBuild.agda` | G | Track A's exports supplied | 146 | 107 | `e27b8104f7a42a16` |
| `PowerDegenerate.agda` | G | the exact degenerate control | 62 | 29 | `fe7c142a837e6cbf` |
| `Replacement.agda` | H | `hasReplacement`, Bell's Collection form | 706 | 350 | `76b599febdb39fb0` |
| `Ordinals.agda` | H | the ordinal transport, and the stop report | 232 | 73 | `3dfcb79a69c316bb` |
| `Choice.agda` | I | `hasChoice`, `zfᴾ` and `zfcᴾ` | 967 | 486 | `9b598463f540d0c1` |
| `ChoiceAtStructures.agda` | I | the assembly at the real `𝒮ᴾ[ G ]` | 210 | 127 | `ed86fd3881fe0c3b` |
| `Refuted.agda` | J | the refutations, the controls and the audit | 836 | 266 | `7e18bcc016e7cfb7` |
| `OnePoint.agda` | J | the one-point coded presentation | 274 | 131 | `309ab8fb38f8978d` |
| `Smoke.agda` | none | an import-only reachability probe | 20 | 16 | `46d9d5e85663351a` |

By track, with the same two conventions: A three files, 726 lines, 390 code; B
three, 1156, 626; C three, 805, 323; D two, 335, 123; E five, 983, 578; F two,
649, 293; G four, 920, 472; H two, 938, 423; I two, 1177, 613; J two, 1110, 397;
and `Smoke.agda`, which belongs to no track, 20 and 16. Total 29 files, 8819
lines, 4254 code. Track K's own per-track table reproduces here row for row.

`Smoke.agda` is a reachability probe with no declarations: it names
`OrdinaryProfile`, **nine** `K5.` modules and two `K4.` modules and nothing else.
`LEDGER-K6.md:59` describes it as naming five `K5.` modules; measured, the
imports are `K5.Structures`, `K5.ExtensionSat`, `K5.Truth`, `K5.Dense`,
`K5.Generic`, `K5.RoundTrip`, `K5.Agreement`, `K5.InstanceBase` and
`K5.InstanceValue`, which is nine, plus `K4.Compile` and `K4.ValueSets`.

Forty further files are deliberate breaks, parked with `.agda-break` extensions
under `breaks/`, 12583 lines, with forty logs under `breaks/logs/`. They are not
part of the corpus and are counted separately throughout.

The architecture that produced all of this is
`~/Agentic/bedrock-proofs-archive/k6-architecture.md`, 1902 lines, also archived.
It was never compiled, which is the same deliberate trade K2 through K5 made.
Sections 7 and 10 are what it cost.

## 2. The constraints K6 exists to respect, and how each is enforced

### The extension structure is K5's and is never rebuilt

A field proved at a structure the file assembled for itself would be a
well-typed theorem about nothing, and no body-level grep would see it. The
enforcement is one identification per seam, by `refl`: `structure-agrees :
B.structureᴱ ≡ PS.𝒮ᴾ[ G ]` at `K6/ElementaryAtStructures.agda:141-142`, with
`∈-unfold` `:122-123` and `active-spec` `:125-128` beside it; `structure-is`,
`separation-is`, `sat-is` and `agree-is`, four `refl`s, at
`K6/SeparationAtStructure.agda:111-124`; `structure-agrees` `:85-86` and
`field-agrees` `:91-93`, two `refl`s, at `K6/PowerAtNames.agda`. All eight lines
were read at source for this record. Track B named the reason and Tracks F and G
ran the same check independently.

### No maximum-principle witness anywhere

`roadmap:195` gives the mathematical reason the constraint matters rather than
being hygiene: the maximum principle uniformly over all complete Boolean
algebras is equivalent to AC, so exporting it would destroy the separation of AC
from ZF that section 3 reports. Measured over all 29 comment-stripped files,
each of `Fullness`, `FullnessAt`, `MaximumPrinciple`, `MaximumPrincipleContract`,
`Refinement`, `MixtureSupply`, `Mixture`, `WitnessSpec`, `ValueCover`,
`ElementPrinciple`, `Separated`, `HostPower`, `antichain` and `predense` is
**0**, hypotheses included. All seven ZF fields beyond AC are proved with the
maximum principle at zero.

`AdequateDomain` measures **0** as well. Ruling D10 permitted it in Track H
only, as the return type of `adequate-exists`; Track H's route avoids
`adequate-exists` entirely and the measurement confirms it. **The one exception
the architecture wrote into the exit grep was never used.** Track F's `Separated`
is 0 because the module was renamed to `Cut`, which is the same fact reported
from the other side.

### No elimination of a truncated sigma into data

This is the check that actually protects the package, and it is stronger than
any regular expression. Measured over the 29 comment-stripped files: **84
`PT.rec` and 27 `PT.map`.** The distribution of the 84 motives is exhaustive and
every one is a proposition or a truncation: `(snd …)` 65, `PT.squash₁` 15,
`isProp⊥ᴸ` 2, `(propP τ)` 1, `(isPropAcc ρ)` 1. **Zero data-valued motives.**
The census passes across the whole corpus at once, which is why section 7.3
retires a grep in its favour.

The narrow rule K6 carries beside it: `ext-surjective`'s untruncated Σ is a
construction and not a choice. `K5/RoundTrip.agda:507` reads
`ext-surjective n hn = (trᴾ n , trᴾ-name n hn) , ext-onto-raw n`, verified at
source, and no K6 proof projects `fst (ext-surjective n hn)` outside a
proposition.

### The safety surface

`postulate`, `TERMINATING`, `NON_TERMINATING`, `trustMe`, `primTrustMe`, the
hole marker `{!` and U+2014 are each **0** in all 29 files, re-run for this
record. Every file carries `{-# OPTIONS --cubical --safe --guardedness #-}` on
line 1; zero files lack `--safe`, zero lack `--guardedness`, zero carry the
pragma anywhere but line 1.

Host choice is 0 in every spelling: `Base.Choice`, `SetChoice`,
`lowerSetChoice`, `choice→lem`, `merePicker`, `AxiomOfChoice`,
`CountableChoice`, `ACω`, `DependentChoice`, `DC`, `Zorn`, `BPI`,
`ultrafilterLemma`, `primeIdealTheorem`, `SetQuotients`, `squash/`, each
measured 0 across the corpus. **That zero is a genuine independence claim**,
because nothing in the programme's hypothesis yields any of them.
`ChoiceSet` is not on that list: it is the sentence K6's AC obligation produces,
`OrdinaryProfile.agda:115-124`, and is not a choice leak.

### The module parameter list is the ledger, and excluded middle is an argument

`LEM ℓ` is named at **21 sites in six files**, measured on the comment-stripped
source with import lines excluded, every site read at its source line.
`Choice.agda` 8: the three `module Fields` parameters at `:867-869`, `:870-872`
and `:873-876`, `lem` `:882` in `module Assembled`, `:941-944` and `lem` `:950`
in `module WithChoice` and `module AssembledC`, and the declarations `zfᴾ`
`:929-931` and `zfcᴾ` `:963-965`. `ChoiceAtStructures.agda` 6, at `:170`,
`:174`, `:178`, `:187`, `:199` and `:207`. `TruthSeam.agda` 4, the declarations
`seam-Uof` `:242`, `seam-truth` `:246`, `seam-not-both` `:251` and
`seam-decided` `:255`. `ForcesTruth.agda` 1, the parameter `lem` `:301`.
`ProbeE5.agda` 1, `:136`. `Replacement.agda` 1, `:337`. The other twenty-three
files name `LEM` nowhere, Tracks A, B, C, D, F, G and J entirely and
`Definability.agda` of Track E.

**`LEM (ℓ-suc ℓ)` measures 0 in the code of all 29 files** and 6 raw, all six in
prose. The programme's single `LEM (ℓ-suc ℓ)` covers `LEM ℓ` through
`lowerLEM : ∀ {ℓ} → LEM (ℓ-suc ℓ) → LEM ℓ` at
`src/Base/Classical.lagda.md:82`, and the lowering happens at the instance,
which is K8's and later. `lowerLEM` itself measures 0 in all 29 files. **K6's net
addition to the assumption ledger is zero**, and this record does not equate the
two levels nor treat `LEM ℓ` as a separate assumption.

Two consequences of the same hypothesis, `lem→resizing`
(`src/Base/Classical.lagda.md:281`) and `lem→impredicativity` (`:310`), also
measure 0. **That zero is a usage measurement and not an independence claim**,
and the supplier is named here rather than in a footnote: both follow from the
`LEM (ℓ-suc ℓ)` the programme already carries.

A fourth kind of zero, which is neither: `isGeneric` measures **0** in all 29
files, and the reason is that under obstruction O6 there is no coded order graph
of `B`, so `isGeneric` cannot be applied to a subset of the algebra at all. The
sentence cannot be written down, which is a different fact from declining to
prove it. `i-inj` and `hostSup` also measure 0.

## 3. The result, stated exactly

`OrdinaryZF` has eight fields, `OrdinaryProfile.agda:126-135`, verified at
source: the record opens at `:126` and the eight fields run `:128-135`.

**Five of the eight are unconditional.**

| field | filler | what it rests on |
|---|---|---|
| `extensional` | `ext[_]` at `K5/Structures.agda:794` | `G : Sub` only. This is **K5's**, not K6's |
| `hasPair` | `hasPairᴾ` at `K6/Elementary.agda:455` | ground Pairing as `pairOf`, Collection and Separation through Track A, and `⟨ ⋁ Cond G ⟩` |
| `hasUnion` | `hasUnionᵁᴰ` at `K6/Elementary.agda:713` | as above plus ground Union as `⋃ᴳ`; `Upward` and `Directed` |
| `hasInfinity` | `hasInfinity` at `K6/GroundTransfer.agda:388` | ground `Infinity` and `⟨ positiveᴾ ⟩` |
| `foundation` | `foundation` at `K6/Foundation.agda:213`, seam at `K6/FoundationAtStructures.agda:108-109` | `child-wf` `:118` and `sat-cong` `:131`. **Nothing on `G` at all** |

The ground naturals ship with `hasInfinity` on the same hypotheses, as the
`nat-*` family at `K6/GroundTransfer.agda:504-524`. `extensional` is proved
again in no K6 file: every K6 occurrence is a parameter or the degenerate
audit's witness at `K6/Refuted.agda:122-123`, and the assembly takes it as
`ext[G]` at `K6/Choice.agda:850` and supplies it at
`K6/ChoiceAtStructures.agda:134-135` as `PS.ext[ G ]`, K5's own.

**Four are conditional.**

| field | filler | conditional on exactly what |
|---|---|---|
| `hasSeparation` | `K6/Separation.agda:461` | `forces` `:276` and `truth-at` `:277`, hence O1 and O3b through the engine, **plus O7** as `sepΔ` `:280` and `sepΔ-reading` `:281-283`; ground Separation and Collection |
| `hasPower` | `K6/Power.agda:587` | as `hasSeparation`, plus ground `PowerSet`, plus `sepᴾ` `:378`, plus O7 as `powΔ` `:369-372`, plus `pos` `:305` |
| `hasReplacement` | `K6/Replacement.agda:705` | as `hasSeparation`, plus `lem : LEM ℓ` `:337`, plus O7 as `colΔ` `:331-335` |
| `hasChoice` | `K6/Choice.agda:743` | the whole engine, plus `directed` `:352-353`, `meets-below` `:361-363`, and a ground well order `lt`/`lt-tri`/`wo-least` at `:418-422` |

**The record assembles.** `zfᴾ` at `K6/Choice.agda:928-931` takes twelve
arguments and returns `OrdinaryProfile.OrdinaryZF 𝒮ᴾ`; `zfcᴾ` at `:962-967`
takes those twelve plus a `GroundWellOrder` and returns `OrdinaryZFC 𝒮ᴾ`.
`ChoiceAtStructures.agda` repeats the assembly at the real `𝒮ᴾ[ G ]`. The
five-three split is readable off one term, `Assembled.ordinaryZF` at
`K6/Choice.agda:887-902`, verified field for field: `extensional = ext[G]`,
`hasPair = pair inhabited`, `hasUnion = union upward dir`,
`hasInfinity = infinity inhabited` and `foundation = found` take no engine
component at all, while `hasPower`, `hasSeparation` and `hasReplacement` each
take the full twelve-argument prefix.

**AC is proved separately from ZF, and the separation is structural rather than
grepped.** `module Assemble` is a sibling of `module Selection`, so `lt`,
`wo-least`, `cut` and `selName` are not in scope at `zfᴾ`, and all eight ZF
fields typecheck without them. Measured here: the ground well ordering is
declared at `K6/Choice.agda:418-422` inside `module Selection`, `wo-least` and
`lt-tri` occur in no other K6 file, `zfᴾ` `:929-931` does not mention
`GroundWellOrder`, and `zfcᴾ` `:963-965` does and is the only declaration that
does.

### 3.1 `no-new-ordinals` is NOT proved

`K6/Ordinals.agda` exits 0 and ships a stop report rather than a theorem. Read
at source:

- `NoNewOrdinals` at `:186-189`, **with no inhabitant in the file**;
- the proved reflection half, `reflect-ordinal` at `:196-203`, by `sat-cong`
  plus Δ₀ absoluteness, needing no rank, no filter and no excluded middle;
- the exact open goal, `OpenGoal` at `:209-212`;
- **the reduction, which is proved**, `goal→theorem : OpenGoal → NoNewOrdinals`
  at `:216-219`. So the open goal is the whole gap and nothing else is missing;
- the prerequisite, `OrdinalRankBound` at `:227-232`, written as a function type
  because rule 9 forbids re-declaring K3's `NameRankContract`.

**The prerequisite is `NameRankContract` and it has one declaration and zero
fillers**, measured over the whole compile root rather than over K6: the only
occurrence in Agda code anywhere is the record declaration at
`LInstanceRank.agda:159`. Its three occurrences in `K6/Ordinals.agda` (`:68`,
`:78`, `:222`) are prose, and its six in `K6/breaks/OrdRespell.agda-break` and
`K6/breaks/OrdViaOnto.agda-break` are prose. The zero-fillers figure is
confirmed.

Three routes are blocked, each at a named place, as Track H reports them and
section 9.5 records with their evidence. The roadmap's own paragraph
(`cohen-implementation-roadmap-2026-09.md:205`) re-owns the item rather than
dropping it, and it did not block the Collection field in the same package.

## 4. The filter hypothesis, measured six ways

The architecture types every ZF field over `isFilter G`. **No field needs it.**
`isFilter` measures 0 in `Elementary.agda`, `Separation.agda`, `Power.agda`,
`Replacement.agda`, `Choice.agda`, `Foundation.agda` and `GroundTransfer.agda`,
which is every file that proves a field. Its non-zero occurrences are exactly
four in `ElementaryAtNames.agda` and four in `ElementaryAtStructures.agda`,
which are the architecture's `hasPairᶠ`/`hasUnionᶠ` spellings shipped beside the
measured ones through K5's own `filter-positive` and
`isFilter.upward`/`.directed`; one each in `ForcesTruth.agda`, `ProbeE5.agda`,
`TruthSeam.agda` and `PowerAtNames.agda`, each a forwarded seam parameter; and
two in `OnePoint.agda`, Track J's control.

What each field does spend is different in six ways:

| field | positivity | `upward` | `directed` | `isFilter` | the spelling it does spend |
|---|---|---|---|---|---|
| `hasPair` | **yes, alone** | no | no | no | `⟨ ⋁ Cond G ⟩`, `K6/Elementary.agda:455` |
| `hasUnion` | **no** | **yes** | **yes** | no | not applicable |
| `hasInfinity` and the naturals | **yes, alone** | no | no | no | `⟨ positiveᴾ ⟩`, `K6/GroundTransfer.agda:388` |
| `foundation` | **no** | no | no | no | **nothing on `G` at all** |
| `hasSeparation` | **no** | no | no | no | **none**: all six tokens measure 0 in `K6/Separation.agda` |
| `hasPower` | **yes, alone** | no | no | no | `pos : ⟨ ⋁ Cond (λ q → G q) ⟩`, `K6/Power.agda:305` |
| `hasReplacement` | **no** | no | no | no | all six tokens measure 0 in `K6/Replacement.agda` |
| `hasChoice` | **no** | **no** | **yes, alone** | no | `directed`, `K6/Choice.agda:352-353` |

Eight fields, six different costs. The two `⋁ Cond` occurrences in
`K6/Separation.agda`, at `:200` and `:278`, and the two in
`K6/Replacement.agda`, at `:258` and `:327`, were read at source and are neither
of them a hypothesis on `G`: `:200` and `:258` are the `∈`-unfolding
specification and `:278` and `:327` are the right-hand side of the `truth-at`
parameter. `K6/Power.agda:305` is a genuine positivity hypothesis and is the
only one Power spends.

**Why this could only be found per field, and not per package.** Every field
enters the assembly through the same uniform prefix. All three conditional ZF
slots at `K6/Choice.agda:867-876` are typed
`… → LEM ℓ → ⟨ Positive ⟩ → Upward → Directed → Meets → …`, so the assembly's
type is a supertype of each field's actual need, and reading the assembly gives
the same answer for all three. The source says so itself at
`K6/Choice.agda:859-865`: the filter and the genericity belong in the engine
prefix, because both are spent once inside `K6/ForcesTruth.agda`'s `module
Engine`, and the per-field narrowing is a narrowing beyond the engine, of which
there is none. The only place the six costs are visible is inside each field's
own file, one file at a time, which is why the ledger is per field and why a
single measurement at the assembly would have reported one cost where there are
six.

**Two independent measurements agree.** Track B measured `hasPair` and
`hasUnion` from inside `K6/Elementary.agda` while proving them; Track I measured
the same two from the assembly at `K6/Choice.agda:379-384` while assembling
them, and wrote its own table there. Both agree file for file, and this record
reproduces both.

**One distinction the table does not make.** `directed` is a filter law;
`meets-below` (`K6/Choice.agda:361-363`) is genericity in the dense-below form,
and `hasChoice` spends both. The source's note at `K6/Choice.agda:354-356` says
that at the instance `meets-below` is `generic-meets-denseBelow lem G meets fil`
(`K5/Dense.agda:497-501`) and so is not an assumption beyond `MeetsAll`,
`LEM ℓ` and the filter. This record records the note and does not check it: the
instance does not exist during K6.

## 5. O7, the obligation K6 discovered

The architecture's obstruction ledger (1.4) ends "All six were re-verified
against source in the K6 compile root for this document, by telescope and not by
comment. All six stand. **No seventh was found.**" K6 found one, and the roadmap
now records it (`cohen-implementation-roadmap-2026-09.md:205`).

**O7 is the classical Definability Lemma.** Over a poset, the class of
conditions forcing a formula at an environment must itself be a ground-definable
class, uniformly in whatever the surrounding construction leaves free. The value
half already exists, as `codeOf` at `K4/Compile.agda:1209` and `describes` at
`:1212`, both read at source. **The missing half is an internal description of
`below` or of `i`.** It is free at the coded completion, where `below` is `fst`
and the description is Δ₀, and it is missing at the abstract frame.

**Two tracks reached it independently, and one of them before the coordinator's
ruling arrived.** Track F reached it from Separation. Track G reached it from
Power Set independently, then adopted the ruling's spelling when it came. Track
H reached a third form from Collection and measured that Track G's cheaper form
does not generalise. Where two tracks measure the same thing independently and
agree, this record says so and names both: F and G on the existence of the
obligation, F and H on its shape for a quantified formula.

### 5.1 The three spellings, verbatim from source

Track F, `K6/Separation.agda:280-283`:

```agda
(sepΔ : (α : Nm) (φ : Formula Nm 1) → Formula S 1)
(sepΔ-reading : (α : Nm) (φ : Formula Nm 1) (χ : Nm) (r : Cond)
              → ((entry (fst χ) (cnd r) ∷ []) ⊨ᴳ sepΔ α φ)
              ≡ forces r ((var zero ∈̇ con α) ∧̇ φ) (χ ∷ []))
```

Track G, `K6/Power.agda:369-372`:

```agda
(powΔ : Nameᴾ → Nameᴾ → Formula S 1)
(powΔ-reading : (α χ y : Nameᴾ) (r : Cond)
              → ((entry (fst y) (fst r) ∷ []) ⊨ᴳ powΔ α χ)
              ≡ forces r (var zero ∈̇ con χ) (y ∷ []))
```

Track H, `K6/Replacement.agda:331-335`:

```agda
(colΔ : Formula Nm 2 → Formula S 3)
(colΔ-reading : (ψ : Formula Nm 2) (τ : Nm) (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩)
                (χ : Nm)
              → ((fst τ ∷ q ∷ fst χ ∷ []) ⊨ᴳ colΔ ψ)
              ≡ forces (cndOf q hq) ψ (τ ∷ χ ∷ []))
```

### 5.2 Why the arities differ, and it is mathematics rather than convention

The ground formula's arity counts the slots the surrounding construction leaves
free.

**Separation, `Formula S 1`.** The cut happens at a fixed `α` and a fixed `φ`,
so only the entry code is free. Both `α` and `φ` are host indices of the family,
which is why `sepΔ` takes them as host arguments and returns an arity-one
formula. Track F's reason for needing the datum at all: the separated name's
weight at a subname `χ` is the set of conditions forcing `χ ∈ α ∧ φ(χ)`, and
**that set varies with `χ`**. `forcesSet` is free per formula and environment,
because `below` is a `ForcingBase` field, but the χ-indexed family is assembled
by nothing Track E2 exports.

**Power Set, `Formula S 1` with a different second index.** Track G's second
index is the second name `χ` rather than a formula, because the formula here is
the fixed atomic `var zero ∈̇ con χ`. The source says so at `K6/Power.agda:365-368`:
"`fst y` here is Track F's `fst χ` and `fst r` here is Track F's `cnd r`". That
is the **atomic** half only, and it is strictly weaker than a definability datum
for a universally quantified formula.

**Collection, `Formula S 3`.** Collection is a schema quantifying over every
`φ : Formula Nm 2`, and its witnesses are arbitrary names with no candidate
bound to cut, so no fixed atomic statement can stand in for `φ`. Collection must
be uniform in the domain member too, so the witness, the condition and the
member are all free: three slots, an arity-three ground formula, and the object
formula itself as a host argument.

### 5.3 Why none of the five existing rows supplies it

Track G verified this at source and this record re-verified every cite.

- **`atom-∈` and `atom-≐`, `K5/Truth.agda:733-734`.** Read at source:
  `atom-∈ : (σ τ : Nameᴮ) → (σ ∈ᵁ τ) ≡ Uof (memᴬ (fst σ) (fst τ))`. These are
  **host paths in `Ω` and carry no internal formula.**
- **The internal half is the other part of the same O1 record, and it is equally
  unsupplied.** `record AtomicGraph` at `K4/AtomicGraph.agda:411`, with
  `memAtˢ` `:414`, `memΔ` `:416`, `mem-sound` `:429` and `mem-total` `:431`. The
  single route to it is `table→graph : TableComparison → TableSupply →
  AtomicGraph` at `:719-720`, and `TableSupply` at `:616-617` is uninhabited.
  (Track G cited the block as `:412-432`, which is the `field` keyword through
  the last field's continuation and is right. `LEDGER-K6.md:487` gives `memΔ`
  `:417` and `mem-total` `:432`; measured, `memΔ` is at `:416` and
  `mem-total`'s declaration is at `:431` with its type running to `:432`.)
- **`Supply` is `Admits`, at the wrong universe and the wrong shape.**
  `record Admits {I : Type ℓ} (val : I → Pt B) : Type (ℓ-suc ℓ)` at
  `K4/ValueSets.agda:291`, with fields `values`, `values-sub` and `attained`.
  **It yields value sets, never a graph.**
- **`p ⊩ᴮ b` is `i p ≤ᴮ b`**, with `below` and `i` host fields and no internal
  graph of either. Read at source: `_⊩ᴮ_` is declared at `K5/Frame.agda:252` and
  defined at `:253`, and `⊩ᴮ-spec` at `:255`. Track G cited `:255`; the
  definition is at `:252-253` and the substance is unaffected.

**So O7 is a genuine sixth row**, and the architecture's "no seventh was found"
is now false with machine evidence behind the correction.

### 5.4 Its general form is one object, not three

An internal description of `below` or of `i` discharges every instance at once,
because `sepΔ`, `powΔ` and `colΔ` are three projections of one obligation.
`below` is `fst` at the coded completion (`K5/InstanceBase.agda:352`, with
`below-⊤` a parameter at `StandardNames.agda:683`), and with K4's
`codeOf`/`describes` the whole row closes. Owner: unassigned; the natural home
is beside K4's compiler.

## 6. Rule 15, its refutation, and its correct witness

This is the package's sharpest methodological result, and telling it accurately
requires saying that the coordinator's original witness was wrong. The
architecture carries three successive statements of the rule, at Parts 4a,
4a-bis and 4a-ter, in the reverse of the order they were written.

### 6.1 The principle, which stands

A field's type can fail to discriminate a legitimate proof from a poisoned one.
The telescope is the only protection, and it must be audited separately from the
body. A hypothesis false at the intended instance makes any conclusion cheap
with no type error, because the file is only ever checked against variables. The
audit question is mechanical: is there an inhabitant of this hypothesis at a
genuine forcing extension?

### 6.2 Track D's control, which passes

Track D wrote the wrong proof of `foundation` deliberately, as
`K6/breaks/ExtAcc.agda-break`. It exits 0, measured: `K6/breaks/logs/ExtAcc.log`
carries one `Checking` line and `EXIT=0`. The proof body is three tokens:

```agda
(ext-wf : WellFounded (λ (ρ τ : NameOf IsNameᴾ) → ⟨ fst ρ ∈[G] fst τ ⟩))
...
foundation φ step = WFI.induction ext-wf step
```

Every body-level grep in the package passes on that file, and the single
`WellFounded` occurrence is in the telescope. **On that basis the coordinator
stated rule 15 with `ext-wf` as its witness and broadcast it to nine tracks**
(architecture Part 4a), asserting that at a genuine forcing extension `ext-wf`
is false and that Bell makes external well-foundedness equivalent to genericity
through the collapse.

### 6.3 Track J's refutation: `ext-wf` is a theorem

`K6/Refuted.agda:551-552`, read at source:

```agda
ext-wf : WellFounded _<ᴾ_
ext-wf σ = WFI.induction child-wf {P = Motive} go (nmOf σ) (snd σ)
```

Proved from `child-wf`, `active-child` (`Valuation.agda:257`), `child-name`
(`K5/Structures.agda:250`), the `_∈[G]_` unfolding (`Valuation.agda:294-295`)
and `∈-congʳ` (`Valuation.agda:445-449`), **with no hypothesis on `G` at all.**
All five cites were verified at source. Track J's report spells the K5 parameter
`child-nameᴾ`; the source at `K5/Structures.agda:250` spells it `child-name`,
and `K6/Refuted.agda` uses the local spelling `child-nameᴾ`.

**The mechanism, and it is the thing to remember.** `𝒮ᴾ[ G ]`'s carrier is
`Nm = Σ[ n ∈ S ] ⟨ IsNm n ⟩` (`K5/Structures.agda:263-264`, read verbatim): **a
plain Σ-type and not a quotient.** Two value-equal names are different points of
it, so an `∈[G]`-predecessor decomposes into an active child, accessibility
descends along `Child`, and `acc-≈` (`K6/Refuted.agda:548-549`) transports it
sideways along `≈[G]`. The value relation never creates new descent. **Bell's
equivalence of ill-foundedness with genericity is about the quotient carrier**,
where two value-equal codes are one point and there is nothing to transport. K6
never forms that quotient; K13 does.

The consequence for Track D's control is that it is an indirect proof rather
than a poisoned one. `K6/Refuted.agda:575-576` ships `foundation-via-ext-wf`
from the proved `ext-wf`, and `:568-569` ships `ext-acc = ext-wf` in the exact
shape the coordinator's message quoted, so that a reviewer can diff the two.
Track D's own direct route by `Child`-induction remains the better one because
it is direct, but the control does not show what it was written to show.

### 6.4 Track H's correct witness: K5's `Onto`

`Onto` at `K5/Structures.agda:532-533`, read at source:

```agda
Onto : (S → Nm) → Type ℓ
Onto h = (σ : Nm) → ∥ Σ[ a ∈ S ] ⟨ fst σ ≈[G] fst (h a) ⟩ ∥₁
```

Every name is value-equal to a check name: the extension contains nothing the
ground did not. **That is false at every genuine forcing extension**, and it is
the point of forcing. K5 shipped it deliberately as an uninhabited NON-CLAIM 4.

`K6/breaks/OrdViaOnto.agda-break:244-245` derives `no-new-ordinals` from it, and
the derivation is literally two lines, counted at source:

```agda
onto→no-new : Onto → NoNewOrdinals
onto→no-new onto = goal→theorem (λ σ _ → onto σ)
```

Exit 0, measured: `K6/breaks/logs/OrdViaOnto.log` carries `EXIT=0`. **Track H
did not take it; it demonstrated it.**

### 6.5 The three classes, and what the spelling does not tell you

| class | meaning | witnesses | status |
|---|---|---|---|
| (i) | landed or provable | `ext-wf`, `child-wf`, `acc∈` | `ext-wf` **proved** at `K6/Refuted.agda:551` |
| (ii) | open at this layer, inhabited in principle | `atom-∈`, `atom-≐`, the O3b five, `Supply`, `LEM ℓ`, **O7** | unbuilt, not false |
| (iii) | false at the intended instance | **`Onto`** | `K6/breaks/OrdViaOnto.agda-break`, exit 0 |

**Class (iii) is unoccupied in every K6 deliverable.** It is occupied only in a
deliberate break, which is where a class (iii) hypothesis belongs. Three tracks
found this independently: Track F's telescope audit reports 35 parameters with
class (iii) empty and class (i) 31, every one of the 31 filled from landed
source in the seam probe and class (ii) 4 (`forces`, `truth-at`, `sepΔ`,
`sepΔ-reading`); Track I found it again at the assembly; Track J found it a
third time from the refutation side.

**Spelling carries no information.** Three `WellFounded` hypotheses in this
programme, `ext-wf`, `child-wf` and `acc∈`, are all class (i). One
non-`WellFounded` hypothesis, `Onto`, is class (iii). A grep tells them apart
from nothing; only inhabitation does. That is the whole content of rule 15 and
it is now demonstrated in both directions.

**Track H's handling of a printed poison is the model.** The architecture printed
`witnessBound` and `witnessBound-covers` as signatures, and taking either would
have been exactly the poisoned telescope. Track H built both instead, from
ground Collection twice plus Separation plus Union.

## 7. The five checks measured unsound, and one of them is the dangerous kind

Four package greps report correct files as violations, and a fifth check passes
vacuously. Each is given with the number, the corrected form, and the check that
actually matters.

### 7.1 `chk [a-z] ≈\[G\] [a-z]`, inherited from K5's exit item X6

Measured **3 comment-stripped, 4 raw**. The three are
`K6/GroundTransfer.agda:345` (`chk-≈`), `:511` (`nat-inj`) and `:518`
(`nat-cong`), all of the shape `chk _ ≈[G] chk _`, which is Bell 1.23(ii) and is
K5's own `chk-≈`, entirely legitimate. The fourth raw hit is a comment at
`K6/Refuted.agda:766` explaining exactly this.

**The corrected form needs a guard in both directions, because the sentence is
symmetric.** Measured here on the comment-stripped source:

```
grep -rnP 'chk [a-z] ≈\[G\] (?!chk)'        →  0
grep -rnP '(?<!chk )[a-z] ≈\[G\] chk [a-z]' →  0
```

and the reverse shape unguarded measures 3, the same three lines from the other
side. **The actually-forbidden shape is a check name value-equal to a non-check
name, and a single-direction guard would miss half of it.** Track C measured the
forward guard and Track J measured both, independently; both report 0 and this
record reproduces both.

### 7.2 `MemberImage|imageOn|image-spec` without comment stripping

Measured **31 raw, 4 comment-stripped**. Twenty-seven of the 31 raw hits are
prose, and the prose is required: rule 14 makes every track transcribe the
forbidden route it declined, and the pattern then flags that transcription.
Track A measured the same shape on its own files and called it "a control grep
reports its own rule-14 compliance as a violation".

**The corrected form is the same pattern run on comment-stripped text.** The
four remaining hits are all in `K6/GroundTransferAtCheck.agda`, at `:68`, `:90`,
`:97` and `:101`, and with the bare `image` parameter at `:67` they are X3's
recorded exception: `image` `:67`, `image-spec` `:68`, `SK.Weighted` `:90`,
`imageOn` `:97`, `imageOn-spec` `:101`, all five surviving comment stripping.
That is class (ii) with O3b visible in a seam probe's telescope, a legitimate
recorded exception in ruling D10's sense. Measured over every other K6 file
those spellings are 0.

### 7.3 `Σ\[ x ∈ S \]`, the architecture's exit item X7 shape

The architecture asks for zero "`Σ[ _ ∈ S ]` quantifier over names in an
exported signature that is not indexed by a ground code". The bare pattern
`Σ\[ x ∈ S \]` measures **18 lines** comment-stripped, and the general
identifier form `Σ\[ [A-Za-z0-9ᴾᴮᴳ_]+ ∈ S \]` measures **89 occurrences across
21 files**, of which `K6/Power.agda` has 8 and `K6/Replacement.agda` has 6,
exactly reproducing Track G's and Track H's own counts. Every hit is legitimate.
Track G classified its eight at source: two are the types `Cond` and `Nameᴾ`,
six are untruncated payloads under a `PT.rec`.

**The corrected form is not a better regular expression. It is section 2's
structural census.** Every `PT.rec` motive must be an `Ω` carrier or a
truncation, which measures 84 out of 84 across the package. A `Σ[ x ∈ S ]` under
a propositional motive is a construction; a `Σ[ x ∈ S ]` eliminated into data is
the violation, and there are none.

### 7.4 The AC-leak check on the token `wo`

Track I reports that the suggested grep "would have passed vacuously: the token
`wo` occurs nowhere, the well-order being spelled `lt`/`lt-tri`/`wo-least`".
**Measured against the final bytes that is not what the source says, and the
source outranks the report.** `grep -rnwE 'wo'` measures **4 comment-stripped
lines and 9 raw**, all in `K6/Choice.agda`: `:420` and `:559`, which are
`wo-least` and which `grep -w` matches because `-` is a word boundary; **`:952`,
`(meets : Meets) (wo : GroundWellOrder)`**, a genuine standalone binder named
`wo` in `module AssembledC`; and **`:960`, its use** in
`hasChoice = choice … meets wo`. `K6/Choice.agda`'s mtime is the latest in the
package, which is consistent with the binder being named after the report was
written. This record does not adjudicate which came first.

**Either way the grep is the wrong check, and Track I is right about that.** It
would flag `K6/Choice.agda`, which is precisely where AC belongs, and it would
miss the real well ordering, spelled `lt`, `lt-tri`, `wo-least` and
`GroundWellOrder`. The check that actually matters is the module-scope one of
section 3, which Track I states exactly. One check the assembly cannot perform,
in Track I's words: a well ordering hidden inside a producer's module telescope
is invisible in the producer's exported type, and that needs a per-file audit.

### 7.5 Exit item X7's positive check, which is the dangerous one

Ruling D1 says `hasSeparation`, `hasPower`, `hasReplacement` and `hasChoice`
"carry `atom-∈`, `atom-≐`, `ext-surjective` and their `Supply` in their types",
and exit item X7's positive check is "each one's TYPE names `atom-∈`, `atom-≐`,
`ext-surjective` and its `Supply`, so a reader sees the conditionality without
opening the ledger". Measured, comment-stripped, by lines:

| file | `atom-∈` | `atom-≐` | `ext-surjective` | `Supply`/`supply` |
|---|---|---|---|---|
| `Separation.agda` | 0 | 0 | 0 | 0 |
| `Power.agda` | 0 | 0 | 0 | 0 |
| `Replacement.agda` | 0 | 0 | 0 | 0 |
| `Choice.agda` | 7 | 7 | 7 | 16 |
| `ForcesTruth.agda` | 2 | 2 | 2 | 4 |
| `TruthSeam.agda` | 2 | 2 | 0 | 6 |
| `ProbeE5.agda` | 2 | 2 | 2 | 2 |
| `ChoiceAtStructures.agda` | 0 | 0 | 0 | 8 |
| every other K6 file | 0 | 0 | 0 | 0 |

The `Supply` column counts lines matching `supply` case-insensitively, which is
the convention that makes it comparable to the other three. `LEDGER-K6.md:348`
gives `Choice.agda` 9 and `ChoiceAtStructures.agda` 2 in that column, and
neither reproduces here under that convention, under the case-sensitive one
(`Supply` 11 and 8) or under an occurrence count (19 and 8); the ledger's three
other rows reproduce exactly. **Nothing in the finding turns on it, because the
finding is the three zeroes and those are identical under every convention.**

**Tracks F, G and H name none of the four.** They take `forces` and `truth-at`
as abstract parameters, at `K6/Separation.agda:276-277`,
`K6/Power.agda:356-358` and `K6/Replacement.agda:325-328`, which is the engine's
**output** interface, so their own signatures do not display O1 or O3b. **A
reader running X7 as written would conclude the three conditional fields are
unconditional.** That is why this one is the dangerous kind: the other four
produce false positives, which a reader investigates, and this one produces a
false clearance, which a reader does not.

**Nothing is hidden, and the conditionality is visible one layer up, in two
places and only two.** `K6/ForcesTruth.agda`'s `module Conditional` at
`:279-301`, whose telescope is the O3b five at `:288-293` plus `supply` `:298`
plus `lem` `:301`, all under `atom-∈`/`atom-≐` from the enclosing module. And
`K6/Choice.agda`'s `module Fields` at `:867-876`, where `separation`, `power`
and `replacement` each take the full twelve-argument engine prefix ending in
`LEM ℓ → ⟨ Positive ⟩ → Upward → Directed → Meets`. Both blocks were read at
source. **The correct positive check is over those two ranges and not over the
field files**; a hypothesis absorbed into a construction would be the defect,
and none is.

### 7.6 Check F3 passes vacuously, zero instantiation sites

The architecture's check F3 asks that at every K6 site applying a module taking
`(Child : S → S → Type ℓ)` and `(child-wf : WellFounded Child)`, the arguments
be `NameKernel.Kernel.Child` (`NameKernel.agda:368`) and
`NameKernel.Kernel.child-wf` (`:392`) by name, a lambda or a locally defined
relation in that slot being the finding. Both cites verified at source.

Measured comment-stripped: **46 `child-wf|WellFounded` lines across 14 files**,
and none is a lambda. The categories, every line read: 14 import lines, plus one
import continuation at `K6/Refuted.agda:34`; 14 parameter declarations, which
are thirteen `(child-wf : WellFounded Child)` plus
`(acc∈ : WellFounded _∈ᵗ_)` at `K6/GroundTransferAtCheck.agda:66`; 14
forwardings of the file's own `child-wf` parameter into a landed module's
telescope; 2 uses of the parameter, `WFI.induction child-wf` at
`K6/Foundation.agda:178` and `K6/Refuted.agda:552`; and 1 declaration of a
`WellFounded` inhabitant, `ext-wf` at `K6/Refuted.agda:551`.

**`child-wf` is supplied by name at zero sites.** Every occurrence is an import,
a parameter, or a parameter forwarded. So the ledger row must read "no
`child-wf` instantiation sites in K6, forwarded", not "0", which is Track J's
own correction and it is right.

Two arithmetic notes. Track J reports 40 lines in 16 files; the source says 46
in 14 and the source is the authority, and the reasoning survives the corrected
number. `LEDGER-K6.md` splits the 46 as 14/14/15/2/1, counting the import
continuation at `K6/Refuted.agda:34` among the forwardings; this record counts
it as an import continuation, giving 14/14/14/2/1 plus that one line. Nothing
turns on it.

**The `Child` half is different.** `Child` is supplied by name from
`NameKernel.Kernel` at four sites, measured: `K6/NameBuildAtGround.agda:86` and
`:117`, and `K6/SeparationAtStructure.agda:151` and `:155`, the last two through
`AG.K.Child`. Those are the sites F3 wanted and they are clean.

**One further measurement worth the row.** The architecture's check **F2**, the
shape census `(WellFounded|\bAcc\b|WFI\.)[^-]*(∈\[|≈\[|Nm\b|…)`, is expected 0
and measures **2**, both in `K6/Refuted.agda`: `:289`, the poison type `ExtAcc`
transcribed under rule 14, and `:568`, `ext-acc` derived from the proved
`ext-wf`. Track J's file is the one file in the package where F2 is supposed to
fire, and a sweep that does not exempt it will report the refutation track as a
violation.

## 8. The controls that pass, which are the valuable kind

Five of the forty breaks exit 0 by design, measured from
`K6/breaks/logs/*.log`, each of which ends in an `EXIT=` line. The logs tally
**35 at `EXIT=42` and 5 at `EXIT=0`**. A control that fires shows a check can
discriminate; a control that passes shows a check does **not** discriminate,
which is worth more, because it is the finding a reviewer cannot reach by
reading the proof.

- **`ExtAcc`, exit 0.** `foundation` follows in three tokens from a hypothesis
  the coordinator believed was false and Track J then proved is a theorem. It
  drove rule 15 and then refuted the witness attached to it. Section 6.
- **`NoRefineBackward`, exit 0**, 25461 bytes on disk. The defective union name
  is built, certified a name, and its backward direction goes through. **Trap
  T-B1 is therefore measured silent, not argued.** The four Track B breaks that
  do fail at 42 are `PairNoPositive`, `UnionNoUpward`, `UnionCompatibleOnly` and
  `NoRefine`.
- **`OrdViaOnto`, exit 0.** `no-new-ordinals` follows in two lines from `Onto`,
  which is false at every genuine extension. The exit 0 is the finding and not a
  result, in the break file's own words at `:238-239`. Section 6.4.
- **`NameBuildUnsealed`, exit 0.** Half of Track A's seal measurement: removing
  the rule-2/2b seals changes nothing, because every description operator
  reaches Track A as a module parameter and a parameter is maximally stuck.
  Section 9.8.
- **`ProbeE3-no-truth-at`, exit 0.** Removing `truth-at` from the engine
  composition still elaborates, which is the measurement that isolates the cost
  of section 12 to telescope elaboration rather than to the composition.

## 9. The measured negatives

Project rule 14 is refute, do not repair. Each negative below carries the same
weight as a theorem and each has its evidence and its `file:line`.

### 9.1 Bell 1.38 refuted as written, with `nameBound` as the replacement

`roadmap:207` asks, for Power Set, to "normalize candidates to Boolean-valued
functions on the given name's domain in M (Bell Lemma 1.38)". **The object does
not exist here.** A name is a material set of Kuratowski entries, the same
subname may occur at many entries at many weights, and `NameWeight.agda:11-13`
says so in the tree's own words: "there is no function from a subname to a
weight to be had, and the object that does exist is the SET of weights". A
search over the compile root for a product or function space construction
returns only `CardinalBridge.agda:185` `isFunction`, a predicate.

**The replacement is built and is the reason Power Set is reachable.**
`nameBound` at `NameSpace.agda:640-641` with `nameBound-contains` at `:643-646`,
both read at source, plus one Separation against the coded name recogniser
`nameAtˢ` (`NameSpace.agda:176-177`), whose adequacy is `name-adequate` at
`:951-953`. K6 spends both: `nameBound`/`nameBound-contains` appear as
parameters at `K6/NameValid.agda:93-94` and are applied by name at
`K6/NameBuildAtGround.agda:87`.

Track G's two rule-14 departures are recorded rather than smoothed over. First,
it takes the **ZF route and not Bell's weighted name**: Bell 4.7 weights each
candidate by the value of a universally quantified formula, which would need O7
in its full strength, while a bounding name cut by Separation needs only the
atomic half. Strictly weaker. Second, it normalizes **at `G` and not at a
condition `p`**, so both inclusions run through the truth lemma directly.

### 9.2 The silent-O3b hazard at `graph→image`

`graph→image`'s return type at `NameImage.agda:190-193` is
`Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T) ≡ ImageClass f a z)`, with
`ImageClass f a z = ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))` at `:86-87`.
`imageOn-spec` at `StandardNames.agda:284-285` has the identical shape, verified
at source:

```agda
imageOn-spec : (c : S) (f : S → S) (z : S)
             → (z ∈ˢ imageOn c f) ≡ ⋁ S (λ x → (x ∈ˢ c) ⊓ (z ≈ˢ f x))
```

**A filler that ignores `graph`, `coll` and `sep` and calls `imageOn`
typechecks**, and `imageOn` is built from the tier-4 `MemberImage.image`, so O3b
enters silently. **Not detectable by any body-level grep**; the check is reading
the argument at each application site. `K6/NameBuildAtGround.agda:64-73` is the
legitimate filler and the template: it names `NI.graph→image` and passes
`record { graph = g ; defines = d ; only = o }`. Track A's report gives the
range as `:64-72`; measured, the application runs `:64-73`.

Three tracks named this hazard independently: Track A, Track G at
`K6/Power.agda:144-148`, and Track H at `K6/Replacement.agda:155-160`.

### 9.3 The `⊨₀` form that does not chain

`K6/Definability.agda:26-33` records it: the architecture prints `sat-abs` with
`⊨₀` on the right, which is satisfaction at the empty constant domain, and
**that form does not compose with K5**, because `ext-⊨` is stated at
`(ν ⊨ᴾ embed φ) ≡ (envᴮ ν ⊨ᴮ embed φ)` with `embed` on both sides. Track E
therefore ships `sat-abs` in the embed form at `K6/Definability.agda:150-155`
and the architecture's printed form beside it as `sat-abs₀` at `:161-166`, so
nothing is lost. Both ship, and `sat-abs₁` `:170` and `sat-abs₂` `:176` are
built from the embed form.

A cite correction, and it runs the other way from Track K's. `K6/TruthSeam.agda:19`
and `K6/Definability.agda:29` both give `ext-⊨` as
`K5/ExtensionSat.agda:219-220`. Measured: the declaration is at
`K5/ExtensionSat.agda:214` and its type runs `:214-215`; `:216` is blank and
`:217`, `:218` and `:219` are clauses, `:219` being
`ext-⊨ (con e ∈̇ u) ν = Empty.rec* e`. The architecture's `:214-215` is the
correct address. `LEDGER-K6.md:691` gives the signature as `:214-216`; measured
it is `:214-215`.

### 9.4 Track G's atomic saving does not generalise to Collection

Track H attempted it rather than arguing it and reports the failure with its
reason. **Collection is a schema quantifying over every `φ : Formula Nm 2`, and
its witnesses are arbitrary names with no candidate bound to cut, so no fixed
atomic statement can stand in for `φ`.** The consequence is the arity difference
of section 5.2: Separation cuts at a fixed `α` and `φ` so only the entry code is
free, while Collection must be uniform in the domain member too, so witness,
condition and member are all free, and the datum is
`colΔ : Formula Nm 2 → Formula S 3`. Tracks G and H agree that the atomic form
is strictly weaker; they reached that agreement from opposite directions and
neither adjudicated the other.

### 9.5 `no-new-ordinals`: three blocked routes

Each stops at a named place, as Track H reports them.

1. **Child induction** needs a ground Collection along the class "`chk a` has
   the same value as `x`", which is not ground-definable, because
   `G : Sub = Cond → Ω` lives at `Type (ℓ-suc ℓ)` and is not an element of `S`.
   **O7 does not repair this**, because O7 internalizes forcing, which is
   `G`-free, and the obstruction is membership in `G`.
2. **The forcing route** is circular without the rank bound already in hand.
3. **Collection** bounds witnesses inside the extension, not ground ordinals.

The one to carry forward is the first, because it is the one a reader will
expect O7 to close and it does not.

### 9.6 O4's first half discharged, and the residual is strictly smaller

`K6/OnePoint.agda:158-163` ships

```agda
𝔓 : CC.Presentation
𝔓 = record
  { carrier     = carrierOP
  ; order       = orderOP
  ; order-typed = order-typed-OP
  ; inhabited   = ∣ p₀ , sgl-member p₀ ∣₁ }
```

**the first inhabitant of the coded `Presentation` in the programme.** The
record it inhabits is `CodedCompletion.agda:201-208`, verified: four fields
`carrier`, `order`, `order-typed`, `inhabited`. The claim that it is the first
was re-verified here over the whole compile root rather than taken from a
report: the only other `Presentation` inhabitants are
`K2Bridge.agda:65-66` (`hostPresentation : G.Presentation`) and
`Certificate.agda:992` (`B⁺`), and both inhabit the host record at
`Certificate.agda:366`, which lives at `Type (ℓ-suc ℓ)` and is a different
record. Its cost is ground Extensionality (`K6/OnePoint.agda:34`), `paths`,
Pairing and one set constant: **no PowerSet, no Separation, no LEM.** That is
below the architecture's measured floor at `CodedCompletion.agda:256-263`,
because `Presentation` sits outside `Core`.

**`K2Bridge.Bridge` now has a witnessed hypothesis**, verified at
`K2Bridge.agda:60`: `module Bridge (𝔓 : F.Presentation) (laws :
F.Coded.ForcingLaws 𝔓) where`. The residual obstruction is **"no nontrivial
coded presentation"**, strictly smaller than O4 as written, and the reason it is
not smaller still is stated in source at `K6/Refuted.agda:595-603`: the notion
R6 needs is one that adds a set, and the one-point notion is precisely the one
at which the extension is the ground (`K5/Structures.agda:527-531`).
`K6/Refuted.agda:603` declines the refutation explicitly, and K6 does not narrow
exit example E1's statement, per ruling D8.

### 9.7 The degenerate audit fails to discriminate six fields, not four

Machine-checked by Track J and read here at `K6/Refuted.agda:122-157`. At
`G = λ _ → ⊥` all six of these are inhabited by terms in the file:
`yes-extensional` `:122`, `yes-union` `:125`, `yes-separation` `:131`,
`yes-collection` `:135`, `yes-foundation` `:138`, `yes-choice` `:141`. The
summary term `audit-nondiscriminating` at `:148-153` is a **six**-tuple of
exactly those, and `audit-discriminating` at `:155-157` refutes three:
`Pairing`, `PowerSet`, `Infinity`.

A small arithmetic slip in a source comment, caught by reading the type. The
comment at `K6/Refuted.agda:144-146` says "seven of the nine components of
OrdinaryZFC are simultaneously inhabited here and three are refuted, so the
audit separates the eight-field record into 3 and 6". Six and three is nine;
**the type says six, and "seven" in the same sentence as "3 and 6" is wrong.**
Nothing mathematical turns on it: the terms are all there and the typechecker
checked six.

The consequence is the one ruling D8 anticipated. A positive control is needed,
because a vacuous proof of any of the six would pass the degenerate audit
unremarked. Four of the six take the argument set itself as the witness for
their existential, so the witness costs nothing at all, which the source says at
`:118-120`.

### 9.8 Further measured negatives, each with its evidence

**The rule-2/2b seal is not load-bearing in Track A**, and the reason is
structural: every description operator reaches Track A as a module parameter,
and a parameter is maximally stuck. Track A reports sealed 1.05 s / 313.7 MB
against unsealed 1.08 s / 313.7 MB, and at the seam 3.33 s / 684.4 MB against
3.54 s / 680.2 MB. All four seals were kept because they are free. **Half of that
pair does not reproduce**: see section 10.

**The Δ₀ boundary of Infinity, located exactly.** `Infinity`'s body is Δ₀, with
certificate `δ-∧ (δ-∃∈ (δ-∀∈ δ-⊥)) (δ-∀∈ (δ-∃∈ δ-∈))`. The sentence is not: its
outermost constructor is the unbounded `∃̇` and `Δ₀` has no `∃̇` case.
`B1Delta.agda-break` asks for the certificate anyway and measures exit 42 with
`[UnequalTerms]`. The boundary is crossed by hand, once, in the
ground-to-extension direction only, by `PT.map`.

**K5 Track F's join-index datum reproduced inside the bounded fragment.**
`B4JoinIndex.agda-break`, exit 42, `Σ S (λ n → ⟨ IsNameᴾ n ⟩) != S`. This is
rule 4's shape at a new site.

**Rule 13 removals in Track F.** The architecture types `hasSeparation` as
`Engine → isFilter G → Generic G → Separation`. **`isFilter G` and `Generic G`
are not used and were removed**, confirmed by section 4's measurement of zero
filter tokens in `K6/Separation.agda`. Also unused and removed: `forces-mono`,
`forcesSet` and both entailments, `paths`, ground Extensionality, and three of
K3's seven kernel facts.

**The degenerate control for Power is exact.** `K6/PowerDegenerate.agda:61-62`
proves `no-positivity : ⟨ ⋁ K6K.Cond (λ q → degenerate q) ⟩ → ⟨ ⊥ ⟩`, so `pos`
is exactly the hypothesis the degenerate `G` kills, and it is the only
hypothesis on `G` charged to Power. `power-contains-self` at
`K6/Power.agda:575-576` is a theorem beside it.

**`sat-cong` is load-bearing and spent exactly once in Track D.** Measured: two
occurrences in the code of `K6/Foundation.agda`, the parameter at `:131` and the
single use at `:220`. The mandatory break `NoSatCong.agda-break` measures exit
42.

**The dependency edge F to G is new and acyclic.** `K6/Power.agda:378` takes
`sepᴾ : OrdinaryProfile.Separation 𝒮ᴾ` as a parameter and applies it at `:588`.
Verified acyclic by measurement: `K6/Separation.agda` names neither `PowerSet`
nor `hasPower`, both measuring 0 there.

**Ruling D4's five ground axioms are three.** Track A spends `Separation`,
`Collection` and `PowerSet`; `Pairing` and `Union` measure **0** across all three
Track A files, measured here as well. Union is spent through `⋃ᴳ` as an
operation and Pairing upstream inside `entry`. Track G reports the same three
for Power with `Pairing` and `Union` at 0: measured 0 and 0. Track H reports
`Separation` 8, `Collection` 6, `PowerSet` 0 and `Pairing` 0 for
`K6/Replacement.agda`: measured 8, 6, 0, 0, under both the line and the
occurrence convention.

**R2 remains an implication nothing witnesses.** Its antecedent needs a notion
with two conditions and a `G` omitting one. Owner K8. This is the K5 Track J
shape recurring.

**Rule 6's mechanisms, per control, from Track J.** R1, R2 and R7 are caught by
the **value** of `∈[G]`, and no syntax check sees them; R3 by **type checking**;
R4 by the **`⋁` index type**; the `nameAtˢ` slot swap by the **reading theorem
only**, both spellings being well-scoped `Formula S 2` with `refl` readings
(`K6/Refuted.agda:623-645`).

**Two break files carry no `--safe` pragma at all**, measured:
`K6/breaks/ChoiceInZF.agda-break` and `K6/breaks/ClassLeast.agda-break`. Four
further break files carry the pragma but not on line 1, measured:
`SepIgnoresFormula`, `SepNoGuard`, `SepNoSatCong` and `SepWrongCondition`. This
is recorded because a tree-wide pragma audit over `K6/breaks/` will flag all six
and none is a regression.

## 10. The break ledger, and what it found

`BREAKS-K6.md` is the coordinator's measured break ledger and this record
reproduces its tally from the logs: forty `.agda-break` files, forty logs, **35
at `EXIT=42` and 5 at `EXIT=0`**. Before that run the package had forty break
files and zero logs, so every break exit code in every track report rested on
the report alone; Track K found that and it was fixed.

**Two of the forty are prose records with zero non-comment lines and were never
measurable.** Measured here on the comment-stripped source:
`ChoiceInZF.agda-break` is 42 lines and **0 code**, `ClassLeast.agda-break` is
36 lines and **0 code**, and they are the only two breaks with no code at all.
Their logs confirm it from the harness side: both end at
`[ModuleNameDoesntMatchFileName]` with the hint "no module header was found in
this file". Track I listed them among its parked breaks, which overstates them.
The reasoning they record may still be sound; it is simply not machine-checked.
So the substantive tally is 33 at exit 42 with a real diagnostic, 5 at exit 0 by
design, and 2 not runnable.

**`UnsealedAtGround` does not reproduce Track A's reported exit 0.** Track A
reported it at exit 0, 3.54 s / 680.2 MB, as half of its seal measurement.
`K6/breaks/logs/UnsealedAtGround.log`, read here, records `EXIT=42` at
`[UnequalTerms]` on line 88, with its sibling `NameBuildUnsealed` present and
itself at exit 0. This is recorded as a discrepancy and not adjudicated: Track
A's seal conclusion rests on the pair, so the half that does reproduce still
shows the seal is not load-bearing, but the pair as reported does not stand.

## 11. Terminology

The terminology track is blocked on the same owner ruling that blocked K2
through K5 and blocks no code; K6 proceeded with English-only source prose
throughout, which is what the current phase permits. The collision is the one
K2, K4 and K5 already carry: `dev/glossary.toml` holds `coherence` with the
Chinese rendering 相容 owner-ruled on 2026-08-03, and the same word is the
standard Chinese rendering of the forcing compatibility of two conditions. The
evidence for a ruling is assembled in `terminology-compatible-2026-09.md`, which
proposes three options and chooses none, because the project rule is that
parallel authors may not resolve a terminology collision. No Chinese or Japanese
rendering of either sense has been written by any agent, and that is the state
the rule exists to protect. K6 adds one term to the queue rather than to the
glossary: the definability datum of section 5 is called O7 and the Definability
Lemma in English only, and its rendering waits on the same ruling.

## 12. Coordinator failures

Five, recorded plainly, because relaying an unverified claim has cost this
programme more than once. Four are factual errors in briefs, every one caught by
a track reading source, and the fifth is a wrong artefact path. Two further
items follow that are not brief errors but belong here.

**1. `minimal→foundation` described in its pre-fix state.** A brief premise said
it takes the whole `OrdinaryZF` record whose `foundation` field is its
conclusion. Track D refuted it at source and this record verified the same
lines: `OrdinaryProfile.agda:257-258` reads

```agda
minimal→foundation : Separation → MinimalElement → LEM ℓ → TransitiveClosure
                   → FoundationInduction
```

**Four standalone arguments, no record.** K1 narrowed the telescope long ago and
the architecture's own ruling D4 cites the fix; the brief described the defect
rather than the repair. The live record-taking example in the tree is `hasImage`
at `OrdinaryProfile.agda:340`, verified:
`hasImage : OrdinaryZF → (a : S) (φ : Formula S 2) → …`.

**2. `chk` called unconstructible when only its internal image form is.** Track
C's brief said constructing `chk` re-attempts something measured unavailable.
False, and it conflates two statements. Verified at source:
`StandardNames.Weighted` **builds** `chk` at `StandardNames.agda:319-320` by host
well-founded recursion, `chk = WFI.induction acc∈ {P = λ _ → S} chkStep`, with
its computation law `chk-host` at `:322-323`, its specification `chk-spec` at
`:331` and its validity `chk-name` at `:391`. All four lines were opened and
read here. What is unavailable is the **internal image form**, and
`NameImage.agda:392-400` says exactly that and only that: the contract produces
`img` for a given `f`, while `chk` is the fixed point at which `f` is built from
`img` itself, and no tier produces a fixed point. (Track C cited `:394-400`; the
passage begins at `:392`.) So ruling D3's five are a cost with a named supplier
and a named price, `module Weighted`'s telescope at
`StandardNames.agda:265-273`, and not an impossibility. The ruling is unchanged
and its correct justification is that taking `chk` as a parameter keeps the O3b
price visible in the type.

**3. O3b charged to `ext-surjective` alone, when it is proved and the row is
five exports.** Track E's correction, verified: `ext-surjective` is **proved** at
`K5/RoundTrip.agda:507` by one induction on `child-wf`. O3b enters through the
translation layer, and the row is five parameters that
`K6/ForcesTruth.agda:288-293` ships as a single telescope block, read at source:
`trᴮ`, `trᴮ-name`, `≈-agree`, `∈-agree`, `ext-surjective`. Track I reports the
same correction independently from the assembly side.

Two cite corrections inside that correction, one of them Track K's and one this
record's. `TranslateForward.agda:21` and `TranslateReverse.agda:73` are the
lines three K6 files use for the O3b entry point; opened here, **both are
comment lines**, and the declarations a reader checking the claim needs are at
`TranslateForward.agda:185-188` and `TranslateReverse.agda:390-393`. And "all
exports of that one layer" is two files too few: `trᴮ`
(`TranslateForward.agda:387`) and `trᴮ-name` (`:504`) are K3's translation
layer, but `≈-agree` is proved at `K5/Agreement.agda:438`, `∈-agree` at `:542`,
and `ext-surjective` at `K5/RoundTrip.agda:507`. **Three files, not one.** What
unites the five is not a file but a dependency: each is built over K3's tier-4
`MemberImage`. The row is still five and its price is still O3b; the phrase
"exports of one layer" is the part that does not survive a grep.

**4. Rule 15's witness `ext-wf` called false when it is a theorem.** Section 6.
This is the most widely broadcast of the four: it was sent to nine tracks as a
new rule with the wrong example attached, and the architecture's Part 4a states
in its own words that at a genuine forcing extension `ext-wf` is false. Tracks
D, A, C and J each measured against a coordinator assertion and reported the
counter-evidence, which is project rule 14 applied to the coordinator and is
exactly what the architecture's thirteenth ruling asks for: when a track's own
measurement contradicts its brief, the measurement wins and the track says so.

**5. A wrong artefact path in Track K's brief.** The brief named
`/tmp/bedrock-k6-probes/K6/coordinator-final-verify.log` and "40 parked
`.agda-break` files with their logs". At the time Track K measured, neither
existed: there were forty break files and zero logs, and the only run log was
`/tmp/k6-verify.log`. The consequence was stated plainly by that track and is
worth keeping: **it could report no exit code of its own for any break file, and
every break exit code in its ledger is attributed to the track that ran it.**
The break logs were produced afterwards and section 10 is measured from them,
which is why this record can confirm what that ledger could only attribute. The
verify log is now archived as
`~/Agentic/bedrock-proofs-archive/k6/coordinator-final-verify.log` and is
byte-identical to `/tmp/k6-verify.log`, verified by `cmp`.

**Plus one understatement in the architecture itself, and it is the same shape
as the defect K5 named.** The architecture's `Engine` (4.5, E2) understates
conditionality by three rows, measured by Track I against `K6/ForcesTruth.agda`
and confirmed here at source: it also takes the compiler surface with fourteen
laws, which is a **second O1 row** (`K6/TruthSeam.agda:173-216`, with `atom-∈`
`:215` and `atom-≐` `:216` the only two open slots of twenty-two parameters); it
also takes `cob`/`boc` and the frame `B L Cm Kc fb`, which is **O4**; it also
takes `fil`/`meets`; and `Conditional` takes the O3b five, not `ext-surjective`
alone. **This is the same shape as the `K5/Truth.agda:696-699` defect**, whose
own words were read at source for this record: "Stated as a hypothesis, it is
visible in the type, which is what part 5's rule demands: **a deliverable whose
conditionality is invisible in its type is a defect.**" Section 7.5 records the
K6 instance of the same shape, which exit item X7 will not catch.

**Plus the break harness, and it is the same class as K5's.** The coordinator's
first break run gave a uniform exit 42 across all forty. That is the signature of
a harness being measured rather than a subject: the temporary filename carried
two consecutive underscores, which Agda rejects as a name, so 38 died at
`[ParseError]` and 2 at `[InvalidFileName]`, none of them for its own defect.
The run was invalidated and redone, and only the redone run is reported. This is
the same class as K5's zsh word-splitting batch and was caught the same way, **by
the result being too uniform**. The forty logs now on disk are the redone run;
their first lines name the temporary files, for example
`Checking K6.BrkExtAcc (/private/tmp/bedrock-k6-probes/K6/BrkExtAcc.agda)`,
which is the corrected naming scheme.

## 13. What K6 hands forward

**1. O7's general form, and it is one object.** Section 5.4. Owner unassigned;
the natural home is beside K4's compiler.

**2. `no-new-ordinals`, with its prerequisite named and its filler count
measured.** Section 3.1. `NameRankContract` (`LInstanceRank.agda:159`) has zero
fillers in the compile root, verified. Owner per ruling D7: Track H re-owned, or
K7.

**3. `choiceFromStrong` must be re-checked against Track J's
`ChoiceDisjointProposed`.** Track J's D11 attempt closed:
`choice-premise-forces-code-equality` at `K6/Refuted.agda:445-452` shows the two
`ChoiceSet` premises collapse the whole `≈[G]`-class of any inhabited member of
`a` to one code, and the proposal ships as `ChoiceDisjointProposed` `:474-478`
with `proposed-premise-is-weaker` `:480-484`. `OrdinaryProfile.agda` is
untouched, as ruling D11 requires. The residual gap is a code-distinct
value-equal pair, needing two conditions and a `G` omitting one.

**A cite the hand-off needs and which no track could verify.** Track I cites
`choiceFromStrong` at `ProfileFromStrong.agda:162-199`. There is no
`ProfileFromStrong.agda` in the K6 compile root and none under
`/Users/alsg/Agentic/bedrock-forcing-cohen-k0/src`, and `grep -rl
choiceFromStrong` over both returns only `K6/Refuted.agda`, `K6/Choice.agda` and
`dev/literature/k1-ordinary-profile-cardinal-bridges-2026-09.md`. That document
records the file at 199 lines at exit 0 and transcribes `choiceFromStrong`. **So
the K1 file exists as a described artefact and not as a file this checkout can
open**, and whoever takes this item must find it first.

**4. The residual O4 obstruction: no nontrivial coded presentation.** Section
9.6. Owner: K8.

**5. X3's recorded exception.** Section 7.2, five lines in one file, all
surviving comment stripping, class (ii) with O3b visible in a seam probe's
telescope.

**6. Two things K6 measured that the next package should not re-measure.** The
cost of the composed engine, section 14 below: **two `ForcesTruth`-down-to-
`truth-at` runs cannot coexist on this machine.** And the five-three split at the
assembly, readable off `K6/Choice.agda:887-902`.

**7. For K10, Track C's export list, transcribed as given.** `copy-mem`/`-mem→`/
`-mem←`, `copy-eq`/`-eq→`/`-eq←`, `copy-members`/`←`, `nat-faithful`,
`nat-onto`, `nat-inj`, `nat-cong`, `nat-onto-Nm`, `nat-in`, `nat-inductive`,
`infinity-at`.

## 14. Validation

**All twenty-nine K6 files typecheck at exit 0 in the root's final bytes**, as
relayed and verified by the coordinator after every track finished. **The
archived run log records twenty-eight of them.**
`~/Agentic/bedrock-proofs-archive/k6/coordinator-final-verify.log` is 29 lines,
byte-identical to `/tmp/k6-verify.log`, and lists twenty-eight files at `exit=0`
before ending `K6 VERIFY COMPLETE`. The twenty-ninth file, `Smoke.agda`, does
not appear in it; it is the import-only reachability probe of section 1 and
belongs to no track, and it was not run in that pass. So "29 deliverables, all
exit 0" is not what the log says, and this record states what it does say.

**`ProbeE5.agda` at 99 s independently reproduces Track E's measurement.** The
log's `ProbeE5.agda exit=0 99s` is the package's cost warning and its
independent confirmation: Track E measured 102.95 s and **9.08 GB** for applying
`K6.ForcesTruth` down to `truth-at`, which **exceeds the `-M8g` cap** and forced
serialisation. Each layer alone is about 300 MB; the combination is the cost.
Removing `truth-at` changed nothing, 32.98 s and 6.82 GB, and
`ProbeE3-no-truth-at.agda-break` at exit 0 is the artefact of that control, so
the three-step composition is nearly free and the cost is telescope elaboration.
**No mechanism is named**, per architecture 1.5, and none should be read into
this paragraph. Two such runs cannot coexist on this machine.

**Upstream drift is zero, and the audited set is larger than the reported one.**
The K5 record audited 47 upstream modules, 29 top-level and 18 under `K4/`, and
K6 inherited that figure. Measured here from the K6 root against
`/tmp/bedrock-k5-probes`: **79 non-K6 `.agda` files compared, zero differing,
zero without an upstream.** The 79 are those 47 plus the 32 `K5/` deliverables,
which are upstream from K6's point of view and are also byte-identical. The 47
is correct and is a subset.

**What this record verified for itself.** The 29 archived K6 files are
byte-identical to the compile root's final bytes, `cmp` over all 29, zero
differences. Every one carries `--cubical --safe --guardedness` on line 1. No
`postulate`, no pragma, no hole marker, no `trustMe`, no `{!` in any of them.
The forty breaks and their forty logs are on disk and every log ends in an
`EXIT=` line, which is the one-line fix K5's record asked for after fifteen of
K5's eighteen break logs recorded no exit code.

Timings and peaks, as each track measured them under the one option set ruled by
D12, `GHCRTS="-A64m -I0 -M8g" agda <file>`: Track A 1.05 s / 313.7 MB, 1.01 s /
292.0 MB and 3.33 s / 684.4 MB; Track B 7.65 s / 785.6 MiB, 1.66 s / 390.6 MiB
and 2.60 s / 486.4 MiB; Track C 1.13 s / 277 MiB, 1.27 s / 413 MiB and 3.00 s
cold / 491 MiB; Track D 0.66 s / 246.6 MB and 0.97 s / 323.3 MB; Track E
`TruthSeam.agda` 18.17 s cold / 2.29 GB and 1.07 s warm / 323 MB,
`Definability.agda` 0.84 s / 286 MB, `ForcesTruth.agda` 33.23 s / 6.97 GB,
`ProbeE4.agda` 0.88 s / 310 MB, `ProbeE5.agda` 102.95 s / 9.08 GB; Track F
2.24 s / 488 MB cold and 3.66 s / 1.00 GB; Track G 2.28 s / 510 MB, 2.38 s /
666 MB, 1.05 s / 282 MB and 0.77 s / 269 MB; Track H 4.73 s cold / 711 MiB and
0.69 s; Track I 11.22 s cold / 1.29 GB and 4.31 s / 1.14 GB; Track J 1.65 s /
450.9 MB and 1.45 s / 441.7 MB. **Every wall time and every peak resident set in
that list is a track's own number and not this record's**, and the only figures
this record can confirm are the integer seconds in the verify log, which agree
with the tracks' where both exist.

The sources are archived at `~/Agentic/bedrock-proofs-archive/k6/` with the
architecture, `REPORTS-K6.md` transcribing all ten track reports,
`LEDGER-K6.md`, `BREAKS-K6.md`, the verify log, and the forty deliberate breaks
with their forty logs, alongside K0 through K5. `REPORTS-K6.md` exists because
in K5 three tracks each hit a brief citing a report that was not on disk and
each spent time re-investigating; it states in its own header that the sources
outrank it, and this record treated it that way throughout. No Agda process was
started for this record and no file was compiled for it.
