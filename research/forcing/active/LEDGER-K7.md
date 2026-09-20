# LEDGER-K7. K7 Track K, the package ledger.

**Outcome: DONE. No Agda process was started and no file was compiled by this track.**
Every number below was computed here by reading `/tmp/bedrock-k7-probes/K7/*.agda`,
`/tmp/bedrock-k7-probes/O7/*.agda`, the 36 logs under `K7/breaks/` and `/tmp/k7-verify.log`,
or is attributed to a named source by `file:line`. Where a brief, the architecture or a
track report disagrees with the source, both are printed and the source is the authority.

This is the ledger for K7 of the Cohen forcing branch (`research/forcing-cohen-k0`, T3):
the three countable chain conditions, their equivalence, the ZFC completion transfer as a
property certificate, the coordinate by coordinate ground bound, the preservation theorem,
omega-1 and omega-2, and cofinality. Nine proof tracks, A through H and J, have landed, plus
the general O7 track dispatched outside K7 under ruling 12.

---

## 0. METHOD, CONVENTIONS, AND WHAT A NUMBER HERE MEANS

**Comment stripping.** Every census in this file was run on a comment stripped copy of the
source: `{- ... -}` blocks removed with nesting, `{-# ... #-}` pragmas kept as code, then
everything from a `--` token at line start or preceded by whitespace, bracket or semicolon to
end of line removed, with string literals respected. "Code" means non blank lines of the
stripped text. The stripper preserves line breaks, so **a stripped line number equals its
source line number**, and every `file:line` below is a source line checked against the source.

**The corpus.** 17 files matching `K7/*.agda`, **8948 lines by `wc -l`, 4092 code**. Both
figures are exactly the Track K brief's. Plus 36 parked break artefacts under `K7/breaks/`
with the `.agda-break` extension, **2768 lines**, which are not part of the corpus, and
**36 logs, one per break**, which are.

| track | files | lines | code |
|---|---|---|---|
| A `ChainConditions`, `ChainConditionsAtCoded` | 2 | 675 | 262 |
| B `CardinalOrder`, `CardinalOrderAtBridge` | 2 | 1550 | 949 |
| C `CCCEquivalence`, `CCCEquivalenceAtA` | 2 | 1108 | 458 |
| D `CompletionTransfer`, `TransferAtCertificate` | 2 | 930 | 468 |
| E `PossibleValues`, `ValuesAtNames` | 2 | 822 | 417 |
| F `NoCollapse`, `PreserveAtTracks` | 2 | 1049 | 467 |
| G `Aleph`, `AlephAtStructures` | 2 | 835 | 346 |
| H `Cofinality` | 1 | 941 | 342 |
| J `Refuted` | 1 | 1037 | 369 |
| none (`Smoke.agda`) | 1 | 18 | 14 |
| **total** | **17** | **8965** | **4092** |

The 8965 is the line total under the stripper's convention, which counts the empty segment
after a file's final newline; `wc -l` reports 8948, which is 8965 minus one per file. The
code column is identical under both conventions.

**Pragma sweep.** All 17 files carry `{-# OPTIONS --cubical --safe --guardedness #-}`
verbatim on line 1. Measured: zero files without `--safe`, zero without `--guardedness`,
zero with the pragma anywhere but line 1. **All 36 break files carry `--safe` as well.**
K6 shipped two break files with no pragma at all (architecture 1.6, attributed; the K6 tree
was not re-read here); K7 ships none.

### 0.1 THE PACKAGE'S FINAL STATE, AND WHAT THE LOGS DO AND DO NOT CONFIRM

`/tmp/k7-verify.log` records **17 files at `exit=0`** and ends `K7 VERIFY COMPLETE`.
`Smoke.agda` is in that log, at 38 s, so unlike K6 the smoke probe is covered by the final
pass and "17 deliverables, all exit 0" is what the log says.

**Every one of the 36 break exit codes is confirmed by its own log.** This is the first
package in the programme for which that is true: K6's forty breaks shipped with zero logs and
every K6 exit code is attributed. The tally is **16 at exit 0 and 20 at exit 42**, counting
one break file as one result; two logs carry more than one run (`AntichainSwapReading` has
two, `CCCCollapse` has three, all exit 42).

**One exception, and it is the coordinator's own track.** The five O7 files are not in
`/tmp/k7-verify.log`, and the five log files that would cover them,
`/tmp/o7-Definability.log`, `/tmp/o7-PlugPower.log`, `/tmp/o7-PlugReplacement.log`,
`/tmp/o7-PlugSeparation.log` and `/tmp/o7-Supply.log`, are all **zero bytes**. Architecture
Part 0c states "The coordinator re-ran all five files: exit 0 at 0.86 s / 284 MB, 0.80 s /
277 MB, 1.24 s / 421 MB, 2.07 s / 576 MB, 1.39 s / 452 MB". **Those five exit codes and ten
figures are attributed, not confirmed by anything on disk in this package**, and the O7
mathematics was read here while the O7 compilation was not. The brief's sentence "Every exit
code in this package is confirmed by a log" is true of K7's 17 files and K7's 36 breaks and
false of O7's five.

**Two timing figures that are confirmed.** Track H's `Cofinality.agda`: cold 3.82 s real,
345 MB max RSS (`/tmp/k7h-cold.log`), final 2.08 s, 328 MB (`/tmp/k7h-final.log`).
`/tmp/k7h-warm.log` is zero bytes. Track D's seam figure, 10.71 s and 1.43 GB cold for
`TransferAtCertificate.agda`, is attributed to architecture Part 0d; `/tmp/k7-verify.log`
independently shows that file at 4 s warm, the slowest of the 16 non-smoke files.

**The O7 corpus, for the record.** 5 files, 999 lines by `wc -l`, **642 code**. All five
carry the exact pragma. `ChoiceSet`, `postulate`, `TERMINATING`, `trustMe`, `isGeneric` and
`Onto` all measure 0 comment stripped; `LEM` measures 2, one import and one module parameter
`(lem : LEM ℓ)` at `O7/PlugReplacement.agda:108`.

---

## 1. THE PER FILE ASSUMPTION LEDGER

Classical strength column: the exact spelling named in the file, comment stripped, with the
count of declaration sites. Ground axiom column: the profile hypotheses named, which are
**not** ledger leaks and belong in their own table (shared preamble 1.3).

| file | track | lines | code | classical strength | ground axioms named | conditionality |
|---|---|---|---|---|---|---|
| `ChainConditions.agda` | A | 462 | 171 | **none** | **none** | unconditional except `paths` and `ext` |
| `ChainConditionsAtCoded.agda` | A probe | 213 | 91 | none | `Separation`, `PowerSet` (1 site, forwarded) | probe only |
| `CardinalOrder.agda` | B | 1262 | 806 | `LEM ℓ`, 4 sites | `Separation`, `Collection`, `Pairing`, `FoundationInduction` | per declaration, all as arguments |
| `CardinalOrderAtBridge.agda` | B probe | 288 | 143 | `LEM ℓ`, 1 site | `Separation`, `Collection`, `Pairing`, `FoundationInduction` | probe only |
| `CCCEquivalence.agda` | C | 911 | 372 | `LEM ℓ`, 5 sites | `Separation`, `Collection` | `GreedySupply` open; `MaximalExtensionIn` refuted |
| `CCCEquivalenceAtA.agda` | C probe | 197 | 86 | `LEM ℓ`, 1 site | `Separation`, `Collection` | probe only |
| `CompletionTransfer.agda` | D | 704 | 340 | **none** | `Separation`, `Collection` | `SelDefinable`; `pull-injectable`; O6-for-B⁺ typed |
| `TransferAtCertificate.agda` | D probe | 226 | 128 | none | `Separation` | probe only |
| `PossibleValues.agda` | E | 567 | 273 | **none** | `Separation` | `forcesΔ` pair (O7); `chkFo` pair (second residue) |
| `ValuesAtNames.agda` | E probe | 255 | 144 | none | `Separation`, `Collection` | residue reduced to `valΔ` plus `chkFo` |
| `NoCollapse.agda` | F | 782 | 321 | **none** | `Separation`, `Collection` | `CCC₂ᴵ`, `FamilySet`, `ValueAntichain`, `InverseSpread`, `ProvedRangeHolds` |
| `PreserveAtTracks.agda` | F probe | 267 | 146 | none | `Separation`, `Collection` | probe only |
| `Aleph.agda` | G | 524 | 184 | `LEM ℓ`, 4 sites | **extension's** `Separation`, `FoundationInduction` only | `chk-injectable`, three cardinal hypotheses, `CCC₂ᴵ` |
| `AlephAtStructures.agda` | G probe | 311 | 162 | `LEM ℓ`, 2 sites | `Separation`, `Collection`, `Pairing`, `FoundationInduction`, `Infinity` | probe only |
| `Cofinality.agda` | H | 941 | 342 | `LEM ℓ`, 1 site | **none** | `GroundCover` open; stop report by design |
| `Refuted.agda` | J | 1037 | 369 | **none** | `Separation`, `Collection`, `Pairing` | nothing imports it; every conclusion is reached for a bad reason |
| `Smoke.agda` | none | 18 | 14 | none | none | import only |

**Every one of the coordinator's four headline figures is confirmed here.**

* `LEM (ℓ-suc` : **0**, over all 17 files comment stripped. Confirmed.
* Every forbidden host choice spelling: **0**. `Base.Choice`, `SetChoice`, `lowerSetChoice`,
  `choice→lem`, `merePicker`, `AxiomOfChoice`, `CountableChoice`, `ACω`, `DependentChoice`,
  `\bDC\b`, `[Zz]orn`, `\bBPI\b`, `ultrafilterLemma`, `primeIdealTheorem`, `SetQuotients`,
  `postulate`, `TERMINATING`, `NON_TERMINATING`, `trustMe`, `isGeneric`, `import L.`,
  `import V.` all measure 0. Confirmed.
* `ChoiceSet` : **2**, both in conclusion position, both Track C's:
  `K7/CCCEquivalence.agda:375` `wo→choiceSet : Separation → Collection → LtDefinable →
  OP.ChoiceSet`, and its seam application `K7/CCCEquivalenceAtA.agda:98`. Confirmed.
* `LEM` : **25** occurrences, of which **7 are import lines** and **18 are declaration
  sites**. Confirmed.

### 1.1 The eighteen `LEM ℓ` sites, named

`Aleph.agda:314` (inside the type of the `ord-compare` parameter), `:471`, `:500`, `:513`;
`AlephAtStructures.agda:225`, `:297`; `CCCEquivalence.agda:292`, `:847`, `:874`, `:895`,
`:910`; `CCCEquivalenceAtA.agda:177`; `CardinalOrder.agda:362`, `:478`, `:1230`, `:1249`;
`CardinalOrderAtBridge.agda:228`; `Cofinality.agda:466`.

**Every one is `LEM ℓ`, and in every one it is an explicit argument of a function type.
There is no module parameter of type `LEM ℓ` anywhere in K7**, measured: no line matching
`(lem : LEM` occurs in any K7 file. O7 does have one, `O7/PlugReplacement.agda:108`. The
consequence is that a reader of any K7 theorem's type sees the excluded middle it spends.

Ten of the seventeen files name `LEM` nowhere at all: `ChainConditions`,
`ChainConditionsAtCoded`, `CompletionTransfer`, `NoCollapse`, `PossibleValues`,
`PreserveAtTracks`, `Refuted`, `Smoke`, `TransferAtCertificate`, `ValuesAtNames`.

### 1.2 The two levels, covered and not equated

The programme's ledger row is unchanged and K7 adds nothing to it. K7 names `LEM ℓ`; the
final theorem's single hypothesis is `LEM (ℓ-suc ℓ)`; `lowerLEM`
(`src/Base/Classical.lagda.md:82`) covers the first from the second. **K7's net addition is
zero and no new row is opened.** Resizing and impredicativity at zero are usage facts, since
both are consequences of the same hypothesis. **Host choice at zero is the independence
claim**, and it is the claim above.

### 1.3 The profile hypotheses, which are not leaks

`Separation`, `Collection`, `Pairing`, `PowerSet`, `FoundationInduction`, `Infinity` and the
ground well order triple `lt`/`lt-tri`/`wo-least` are the internal axioms of a named
structure and are what a K7 choice obligation legitimately consumes. Counts of
comment stripped occurrences, per file, in the order Sep / Coll / Pair / Pow / Fnd / Inf:

`Aleph` 4/0/0/0/4/0 (all four Separation and all four FoundationInduction are `OPᴱ.`, the
**extension's**, never the ground's); `AlephAtStructures` 4/2/2/0/2/1; `CCCEquivalence`
4/3/0/0/0/0; `CCCEquivalenceAtA` 1/1/0/0/0/0; `CardinalOrder` 9/5/10/0/8/0;
`CardinalOrderAtBridge` 3/2/2/0/1/0; `ChainConditions` 0/0/0/0/0/0;
`ChainConditionsAtCoded` 1/0/0/1/0/0; `Cofinality` 0/0/0/0/0/0; `CompletionTransfer`
3/3/0/0/0/0; `NoCollapse` 16/9/0/0/0/0; `PossibleValues` 10/0/0/0/0/0; `PreserveAtTracks`
10/5/0/0/0/0; `Refuted` 3/3/3/0/0/0; `TransferAtCertificate` 1/0/0/0/0/0; `ValuesAtNames`
6/2/0/0/0/0.

**`Union` measures 0 in every K7 file comment stripped.** Including comments it measures
exactly **1**, at `Cofinality.agda:139`, which is Track H's own sentence saying no K7 file
uses the axiom. That is not a virtue; section 9 records it as the unfunded row cofinality preservation waits on.

**Two files name no ground axiom at all: `ChainConditions.agda` and `Cofinality.agda`.**
Track A's three predicates and two free arrows are theorems of a bare `ZFStructure` plus
`Extensionality` and `paths`. Track H's whole vocabulary, its four reading theorems, its
Δ₀ certificate and its dichotomy cost one `LEM ℓ` and nothing else.

---

## 2. THE CONDITIONALITY LEDGER, PER DELIVERABLE

**K7 is the first package in this programme whose mathematics genuinely wants choice**, so
the ledger's central question is not whether choice is spent but **whose**. That question is
settled in section 4, and its answer is that the distinction is real, is invisible to the
typechecker, and is carried by module structure alone.

| deliverable | status | conditional on | at |
|---|---|---|---|
| D1 the antichain formula, its Δ₀ certificate, its `refl` reading | **PROVED** | nothing beyond `paths`, `ext` | `ChainConditions.agda:112`, `:131`, `:141` |
| D2 the three predicates `CCC₁ᴵ`, `CCC₂ᴵ`, `CCC₃ᴵ` ascribed to `Ω` | **PROVED** | nothing | `ChainConditions.agda:305` |
| D3a `ccc₂→ccc₁`, `ccc₃→ccc₁`, the two free arrows | **PROVED** | nothing; `paths` twice | `ChainConditions.agda:381`, `:397` |
| D3b `ccc₁→ccc₂` | **PROVED CONDITIONALLY** | `MaximalExtension` | `CCCEquivalence.agda` module `Free` |
| D3c `ccc₂→ccc₃` | **PROVED CONDITIONALLY, HYPOTHESIS REFUTED** | `MaximalExtensionIn`, which is **false** at a legitimate configuration | `CCCEquivalence.agda:689` |
| D3d `MaximalExtension` from M's well ordering | **NOT PROVED. Reduced to exactly one thing.** | `GreedySupply` | `CCCEquivalence.agda:890` |
| D3e the converse the coordinator wanted | **PROVED** | `Separation` + `Collection` + `LtDefinable` | `CCCEquivalence.agda:375` |
| D4 the transfer `transfer-runs`, and `CCCHypotheses` | **PROVED CONDITIONALLY** | six record fields; four of six discharged by `hyp-from-choice` | `CompletionTransfer.agda:551`, `:666` |
| D4b O6-for-B⁺ | **TYPED, NOT BUILT**, route priced at source | `PowerSet` + `Pairing` + `Separation` on one declaration | `CompletionTransfer.agda:222` |
| D5 `valuesOf`, `valuesOf-spec`, `values-bounded`, `values-covers` | **PROVED CONDITIONALLY** | O7's `forcesΔ` pair, K6's `mk` four, abstract `forces`/`truth-at`, **and a second residue** | `PossibleValues.agda:452`, `:455`, `:481`, `:491` |
| D6 `no-collapse-in-range` | **PROVED CONDITIONALLY** | `FamilySet`, `ValueAntichain`, `InverseSpread`, `ProvedRangeHolds`, `Collection`, `Separation`, `positiveᴾ`, `CCC₂ᴵ` | `NoCollapse.agda:743` |
| D7a ω₂ preserved | **PROVED**, as D6 applied | as D6 | `Aleph.agda` module `Aleph` |
| D7b ω₁ identified | **PROVED CONDITIONALLY** | extension `FoundationInduction` + extension `Separation` + `LEM ℓ` + `chk-injectable` + `ω₁-members-countable` + `CCC₂ᴵ` + three cardinal hypotheses | `Aleph.agda:499` |
| D8a the cofinality vocabulary with four reading theorems | **PROVED** | nothing | `Cofinality.agda:334`, `:385`, `:423`, `:509` |
| D8b `Δ₀-IsCofinalφ` | **PROVED** | nothing | `Cofinality.agda:350` |
| D8c `singular→¬regular` | **PROVED** | nothing | `Cofinality.agda:450` |
| D8d `¬regular→singular` | **PROVED** | `LEM ℓ` | `Cofinality.agda:466` |
| D8e `CofinalityRange`, the exact range | **PROVED EMPTY BY `refl`** | nothing | `Cofinality.agda:672`, `:675` |
| D8f `RegularPreserved`, `NoShortCofinal` | **NOT PROVED. Reduced to exactly one thing.** | `GroundCover` | `Cofinality.agda:824`, `:835` |
| D8g `cofinal-range→covering-range` | **PROVED** | nothing | `Cofinality.agda:645` |

**The four unwitnessed rows, stated so nobody over reads the table.** `GreedySupply`,
`GroundCover`, `ProvedRangeHolds` and `chk-injectable` are rule 15 class (ii): inhabited at a
genuine ZFC ground or a genuine ccc extension, with **no filler anywhere in this tree**,
measured. Above them all sits one residual that is worse, and section 9 carries it:
**no coded presentation in this programme makes any chain condition non-trivially true**, so
every `⟨ CCC₂ᴵ c o w ⟩` hypothesis in the package is unwitnessed at the only presentation on
disk.

---

## 3. RULE 15, AND K7's SIXTEEN EXIT-0 BREAKS

**The brief says eight. The measurement is sixteen**, and it then names ten. Rule 14 applies
to the ledger track as much as to any other: the tally below is what the 36 logs say.

**A control that passes is worth more than one that fires.** A break that exits 42 confirms
that a slot is load bearing, which the author already believed. A break that exits 0
**refutes something**, and this package produced more of them than any before it: **16 of 36,
every one confirmed by a log**, against K6's **3 of 40, every one attributed**
(`LEDGER-K6.md:615-627`, section 5.1, whose own closing sentence reads "No log for any break
file exists on disk, so this ledger confirms none of them").

### 3.1 The sixteen, each with what it shows

| break | track | shows |
|---|---|---|
| `HostSelector` | D | **A bare host `pick : S → S` with its membership fact fills all three `WithSelection` parameters and fills `SelTotal` in one line.** The field M's choice was supposed to pay for, filled with no well ordering and no `ChoiceSet`. `host-total u _ = ∣ pick u , refl ∣₁`. |
| `ChoiceSlotLeaks` | J | Three leaks at an arbitrary instance: the host function fills `hyp-from-ground`'s `GroundWellOrder` slot; the three arguments collapse to one `SelTotal` by `refl`; and `ChoicelessTransfer`, the statement `CompletionTransfer.agda:699-702` refuses, follows **from module `Well`**, that is from M's own well ordering. The boundary is porous in both directions. |
| `HostMaximalExtension` | C | The same answer at Track C's obligation. `MaximalExtension`'s conclusion is a truncated internal existential, and `∣_∣₁` does not ask where its first component came from, so a host `hostExtend : S → S` with three host specifications fills it in one line and Track C's paid arrow then runs on it. A choiceless CCC transfer in everything but name. |
| `HostCofinalCover` | H | The same answer at Track H's one open type. A host `pick : Nm → S` with two pointwise proofs fills `GroundCover` in one line, and `cover→bounded` then delivers `NoShortCofinal`. Track H relies on **neither** protection, because it ships no inhabitant; the warning is for whoever closes it. |
| `HostFamilyRange` | F | **The proper class trap passes the typechecker.** `ProvedRangeHost` is Track F's `ProvedRange` with the family binder changed from `⋀ S` to `⋀ (S → S)`. It is well formed, still lands in `Ω`, is **shorter**, and needs no `FamilySet` and no `Collection`: `collapse-host` is one line. Nothing in the type distinguishes it; only reading the binder does. The reviewer test the file leaves behind: inside an `Ω`-valued predicate every binder must be `S`, `Nm` or the notion's `Cond`; a binder of type `(S → S)`, `(S → Ω)` or `Type ℓ` is host fiat whatever the predicate is called. |
| `ConstantCheck` | E | **A field's type does not see a poisoned check map.** Replace `chk` by a constant `λ _ → n₀`. Its internal graph is `var 0 ≐ con (fst n₀)`, whose reading theorem is `refl`, so module `AtBound` applies with no complaint and all four shipped theorems elaborate and are true. `no-coordinate : poisoned-values sep f ξ ≡ poisoned-values sep f η` is `refl`: the "coordinate by coordinate" bound does not depend on the coordinate. What protects the track is the seam probe `ValuesAtNames.agda`, where `chk` is filled by K5's `Copy.groundName`. |
| `OnePointDiscriminates` | A | **At the only presentation this programme has, the chain condition cannot see the order.** At a carrier with at most one member every ground set is an antichain, so `CCC₂ᴵ` collapses to "every coded subset of the carrier injects into `w`", in which the order does not occur; `order-irrelevant` proves `⟨ CCC₂ᴵ c o w ⟩ → ⟨ CCC₂ᴵ c o' w ⟩` for an arbitrary other set `o'` of the model. A predicate invariant under arbitrary change of order is not a chain condition. |
| `AntichainAtOnePoint` | F | The same measurement run against K6's actual one-point presentation rather than parametrically. `antichain-everywhere` holds for every `d` at `K6/OnePoint.agda`'s own carrier, and `ccc₂-from-countability` closes `CCC₂ᴵ` from bare countability with the antichain argument discarded. So instantiating a Track F theorem there proves nothing about the theorem. Two tracks, independently, same conclusion. |
| `OrdinalDeltaBlind` | B | **A Δ₀ certificate is not a correctness check.** `checkΔ₀` passes on the poisoned `IsOrdinalφ` (one de Bruijn index changed, the inner bound ranging over `x` instead of `α`) exactly as on the correct one, because `bounded` recurses on connectives and never inspects a slot. And the poisoned predicate says nothing beyond transitivity: its third disjunct **is** its hypothesis, so it is inhabited in one line for every `α`. |
| `CofinalBound` | H | The sharpened form, and it is the stronger finding. The poisoned `IsCofinalφ-misbound` is well scoped, is Δ₀-certified, **and has a `refl` reading theorem** against its own unfolding, so a track that writes the reading by unfolding the formula it has just written will not notice. `vacuous` proves the predicate collapses to `a ⊆ α`. **A reading theorem is necessary and is not sufficient.** |
| `AntichainSwapIsDelta0` | A | The same blindness at Track A's own new formula, in two shapes: `swapGuard` (the guard `p ∈ d` replaced by `p ∈ c`, which is already the bound, so the sentence is about the carrier) and `swapCompat` (the two condition slots of `compatAtˢ` exchanged, semantically harmless because compatibility is symmetric, and therefore the more dangerous). `checkΔ₀ … tt` accepts both. Its companion `AntichainSwapReading` exits 42 on the same two formulas: **the reading theorem accepts neither.** |
| `AntichainAtEmpty` | A | The empty coded set is an antichain of every coded notion, spending nothing: not the carrier's inhabitedness, not the order, not `ext`, not `paths`. And `empty-not-predense` shows it is never maximal, spending inhabitedness. So the empty set lies inside `CCC₂`'s hypothesis and outside `CCC₁`'s and `CCC₃`'s, which is the precise sense in which `CCC₃` is the variant a consumer should prefer. |
| `TransferVacuous` | D | `Certificate.agda:1542-1545`'s `PropertyTransfer` has an unconstrained `hypotheses : Type ℓ`. This file inhabits it twice with hypotheses carrying no mathematics, both at exit 0. A checker that closes an exit item by observing "a `PropertyTransfer` was delivered" closes it on nothing. The discriminating construction is a **named record plus an inhabitation lemma beside it**, which is what `CCCHypotheses` and `hyp-from-ground` are. |
| `GWOParamAtTypeL` | C | **Rule 15 one level down, and no grep finds it.** A `GroundWellOrder` declared as an abstract module **parameter** at `Type ℓ`, with every use through a large projection, elaborates; the order theory inside it elaborates too; and it can never be instantiated, because anything with those projections is a `Type (ℓ-suc ℓ)`. The file is empty of content in the only sense that matters and nothing in it says so. Its companion `GWOParamAtTypeLApplied` adds one application and exits 42. |
| `AlephViaDownward` | G | **The poisoned hypothesis Track G is actually exposed to.** Not `Onto`: the reversed injectability arrow `inj-down : ⟨ injectableᴱ (chk a) (chk b) ⟩ → ⟨ injectableᴳ a b ⟩`, one substitution away from the true `chk-injectable` and reading identically in a telescope. It is false at exactly the extensions the theorem is interesting at, and it buys ω₁ preservation with `no-collapse`, `CCC₂ᴵ`, `PossibleValues`, `ProvedRange`, `ord-compare`, `chk-injectable`, `ω₁-members-countable` **and `ω` itself** all removed from scope. |
| `AlephViaOnto` | G | **Exits 0, but not at the statement the brief asked for**, and the track reported it as it came out. `Onto` does not reach ω₁-identified at any price this track can pay, because `IsInjectionφ` is not Δ₀ in either direction. What `Onto` does buy, both halves at exit 0: `NotClaimed-NoNewOrdinals` in two lines, and the minimality conjunct with the conditional hypothesis replaced by an unconditional ground one. **So `Onto` does not remove a hypothesis from this track; it removes this track's entire conditionality, which is worse, because a ledger row that reads "unconditional" is the one a reader stops checking.** |

### 3.2 The twenty that fired, in one line each

`CCCCollapse` (three runs, trap T10: the three conditions are not definitionally equal in any
pairing), `CCCOverHostSub` (a chain condition over `Sub = Cond → Ω` is a **sort** error, not a
type error, because `⋀` is indexed by a `Type ℓ`), `AntichainSwapReading` (two runs, the
reading theorem rejects both mutilations `AntichainSwapIsDelta0` accepted), `ArchAntichainRefl`
(the architecture's displayed `antichainΔ` is **not** definitionally Track A's; `refl`
refused), `CCC1to2NoChoice` (`ccc₁→ccc₂` without `MaximalExtension` cannot close:
the missing half is predensity), `GreedyNoLEM` (`greedy-predense` without `LEM ℓ`; the error
names `LEM ℓ` as the gap, and the antichain half is constructive), `GWORecordAtTypeL`
(the **record** spelling at `Type ℓ` is rejected outright, `[ConstructorDoesNotFitInData]`),
`GWOParamAtTypeLApplied` (the parameter spelling, applied), `PredicateField` (a predicate
field in a `Type ℓ` record, the shape architecture 2.4 sketched),
`InjectableTransNoSep` (`injectable-trans` without `Separation`), `CardinalDeltaZero`
(`bounded IsCardinalφ` is false, verifying architecture G3's unverified claim),
`OrdinalRespellReading`, `SurjRespell`, `RegularBound`, `CofinalSwap` (four respelling
controls, each rejected by its reading theorem alone), `CheckCodeGap` (O7's second name slot
will not take a ground `a` where `fst (chk a)` is wanted), `ClassBound` (the possible value
bound cannot be a host predicate: every set former on the route takes an element of `S`),
`NoCCC` (Track F's `countable-values` with `CCC₂ᴵ` deleted: an antichain proof is not a
countability proof), `AlephNoOrdCompare` (Track G without `ord-compare`, body left as a hole
so the compiler prints the real obligation), `CCCAtEmptyFree` (at the empty presentation the
**conclusion** of `CCC₂` is not free, and the printed goal is the injection code).

---

## 4. THE TWO PROTECTIONS, ONE OF THEM REFUTED

Architecture Part 0d named two structural facts as what protects the ledger where the type
cannot. **One is refuted and one is confirmed.**

### 4.1 REFUTED: opacity

Part 0d says `GroundWellOrder` "reaches the assembly only as an opaque `Type (ℓ-suc ℓ)`, so
no consumer can look inside it and **no host function can be passed where it is expected**."

**The second clause is false.** `CompletionTransfer.agda:634` and `:667` are the
`(GroundWellOrder : Type (ℓ-suc ℓ))` lines of `hyp-from-ground` (`:633`) and
`hyp-from-choice` (`:666`), and at both of them `GroundWellOrder` is an argument of the
**declaration**, universally quantified, so **the caller chooses the type**.
`Refuted.agda:650-660` declares

```
data HostChoiceFunction : Type (ℓ-suc ℓ) where
  hostPick : (f : S → S)
           → ((u : S) → ⟨ u ∈ˢ B⁺set ⟩ → ⟨ selRel u (f u) ⟩)
           → HostChoiceFunction
```

and `host-fills-the-choice-slot : HostChoiceFunction → Rest → T.CCCHypotheses` at
`Refuted.agda:658` passes it into that slot. It is declared at `Type (ℓ-suc ℓ)` only because
that is the level the slot asks for, and a data declaration may sit above its constructors.

**And the slot is eliminable by `refl`**, which is stronger and cheaper:

```
choice-slot-eliminable :
    (GWO : Type (ℓ-suc ℓ)) (wo : GWO) (supply : GWO → T.SelTotal) (rest : Rest)
  → from-ground GWO wo supply rest ≡ without-choice (supply wo) rest
choice-slot-eliminable GWO wo supply rest = refl
```

`Refuted.agda:677-681`, with the witness type `NoChoiceAtAll` having one point and no
structure. The joint content of the triple is exactly one `SelTotal`.

### 4.2 CONFIRMED: the sibling arrangement

`module Well` (`CompletionTransfer.agda:100`) and `module Structural` (`:251`) are top level
siblings, on K6's model at `K6/Choice.agda:415` beside `:772`. `ltOf` is out of scope inside
`Structural`, so `sel-injective` (`:311`) and `sel-antichain` (`:331`), Bell's transfer, were
proved with the well ordering not in scope, and nothing inside `Structural` can manufacture a selection: it
must be handed one. Track C copies the arrangement, with `module Free` and `module FromChoice`
as siblings inside `module Presented`. **No edit to a type can falsify this without moving a
module.**

**Every one of Track J's attacks goes through the type and none through the scope.** That is
the sharpest available statement of the finding, and it is what makes the sibling arrangement
the protection that survives.

### 4.3 The census that carries the arrangement, corrected

`Refuted.agda:1018-1023` states: "Three K7 files name a selection or a well ordering in a
non-comment line: `K7/CompletionTransfer.agda`, `K7/CCCEquivalence.agda` and
`K7/TransferAtCertificate.agda`. Measured over the other nine, the count is 0."

**Re-measured here over all 17 files, comment stripped, keying on the set `GroundWellOrder`,
`selRel`, `ltOf`, `leastOf`, `SelTotal`, `wo-least`, `lt-tri`: the answer is FIVE files, not
three, and "the other nine" should read "the other twelve".** The two Track J omitted are
`K7/CCCEquivalenceAtA.agda` (three non-comment occurrences of `GroundWellOrder`, at `:90`,
`:96` and `:177`) and `K7/Refuted.agda` itself (six). Track C's seam probe is the file that
composes Track C's well ordering with its greedy reduction, so it is exactly where the
composition ought to be visible; the omission is a counting error, not a leak. **The
finding the census supports is unchanged**: outside those five files the count is 0, and in
all of them the module that holds the choice is a sibling of the module that proves the
mathematics.

`pick` occurs eight times in `CardinalOrder.agda` (`:389`, `:391-393`, `:415`, `:417-419`)
and is **not** a selector: it is a local helper that consumes a `LEM ℓ` decision. Checked.

---

## 5. THE DEGENERATE AUDIT

### 5.1 The defect, one field, one line

`CodedCompletion.agda:201-208` is the coded `Presentation` record, four fields:
`carrier`, `order`, `order-typed`, and `inhabited : ⟨ ⋁ S (λ p → p ∈ˢ carrier) ⟩` at
**`:208`**. `CompletionTransfer.agda`'s `module Structural` (`:251`) takes `carrier order
B⁺set order⁺` flat as four elements of `S` and **drops `inhabited`**. Dropping `order-typed`
costs nothing. Dropping `inhabited` costs the audit, because K5 records in its own words that
"an empty coded set is not dense, because the carrier is inhabited; so a density hypothesis is
never vacuous and never free. The antichain condition at the same empty set holds"
(`K5/Dense.agda:520-523`).

### 5.2 What the empty presentation defeats, measured

Every item below is at exit 0 inside `Refuted.agda` module `AtEmptyPresentation`, instantiated
at one memberless ground code `nul`, with **Track A's real `antichainΔ`** and not a stand-in,
so this is a degenerate-instance audit and not a degenerate-predicate one.

* All six fields of `CCCHypotheses`, discharged with no axiom, no choice, no definability
  datum and no counting (`:424`).
* The conclusion of `transfer-runs` available **without** the record (`:443-445`,
  `deg-hypotheses-not-load-bearing`). At this instance `CCCHypotheses` is not load bearing.
* `ChoicelessTransfer`, transcribed at `CompletionTransfer.agda:699-702` under rule 14 as
  "the statement K7 refuses" with its own comment saying it is "NOT inhabited anywhere in
  this tree", **inhabited twice**: at `:463-464` with nothing at all (`choiceless-at-empty d
  ds _ = (λ x → x) , (λ u hu → ds u hu)`), and at `:753-757` **from module `Well`**, that is
  from M's own well ordering plus density, because `Well.pick` is a host `S → S` once its
  inhabitation argument is supplied. So it is not a refusal and it separates nothing.
* `OrderGraphFor`, shipped at `CompletionTransfer.agda:222` as the name of the missing
  O6-for-B⁺, inhabited at the empty set in three lines (`:296-299`). What is missing is
  `OrderGraphFor B⁺set`, not `OrderGraphFor`.
* `MaximalExtension` and `MaximalExtensionIn`, the package's two "class (ii), no supplier"
  rows, inhabited with no choice and no recursion (`:327`, `:331`).

**Contrast K6.** Part 0e says the K6 degenerate audit "defeated six of ten"; the K6 ledger's
own measurement (`LEDGER-K6.md:699-712`) is **six of nine inhabited and three refuted**
(`Pairing`, `PowerSet`, `Infinity`), and it records a source comment that said "seven" in the
same sentence as "3 and 6". Either way the contrast holds and sharpens: **K6's audit still
discriminated three slots; K7's defeats every slot but one.**

### 5.3 The one slot that survived, and why

**Track A's `antichain-use` / `antichain-intro` pair.** The two together pin `antichainΔ` up
to logical equivalence, so no degenerate stand-in satisfies both: a constantly true
`antichainΔ` fails `antichain-use`, whose conclusion is `⟨ p ≈ˢ q ⟩`, and a constantly false
one fails `antichain-intro`. It had to be filled with Track A's real export, and it was
(`Refuted.agda:390`, the last argument line of `module St` at `:381`). Recorded at
`Refuted.agda:1027-1033`.

### 5.4 And the one thing the empty presentation does not make free

`CCC₂` is **equivalent** to one instance of `injectable` there, both directions:
`ccc₂-at-empty-needs` (`:345`) and `ccc₂-at-empty-gives` (`:366`). The residue is then
supplied by Track B's `injectable-incl` at `Separation` + `Collection` + `Pairing`, so
`ccc₂-at-empty` (`:361`) is a theorem and not a hypothesis. **Countability is about `w` and
never about the notion**, which is why a degenerate instance does not make a chain condition
free, and the price of the one that is free is exactly three ground axioms. The break
`CCCAtEmptyFree` (exit 42) is the same fact from the other side: the compiler prints the goal,
which is the truncated join over an injection code.

---

## 6. THE MEASURED NEGATIVES

Each is a result and carries the same weight as a positive.

### 6.1 `MaximalExtensionIn` is REFUTED, because compatibility is not transitive

Architecture 2.3 calls `MaximalExtensionIn` "the same Zorn-shaped obligation as extending an
antichain to a maximal one". **It is not the same, and the difference is not a matter of
price. `MaximalExtension` is a consequence of ZFC; `MaximalExtensionIn` is not.** An antichain
inside `b` can be maximal inside `b` and still miss conditions that `b` itself meets.

The witness is a seven element poset, in prose at `CCCEquivalence.agda:640-654`, and the file
says why it is prose: coding a presentation is K8's job and not a reduction. The points are
`p₁ p₂ r₁ r₂ x y z` with `x ≼ p₁`, `x ≼ p₂`, `y ≼ r₁`, `y ≼ p₂`, `z ≼ r₂`, `z ≼ p₁`. Then
`b = {p₁, p₂}` is predense, `r₁` is incompatible with `p₁`, `r₂` with `p₂`, and `p₁` meets
`p₂` at `x`, so the only antichains inside `b` are `∅`, `{p₁}` and `{p₂}` and none is
predense. `MaximalExtensionIn-refuted` at **`CCCEquivalence.agda:689-702`** is that argument
machine checked, **schematic**: it proves failure at every presentation with this
configuration, not that some coded presentation has it. The configuration is consistent, by
the poset. The one-point presentation does not satisfy it, having one point.

**Consequence, and K8 must be told before it quotes CCC₃.** `ccc₂→ccc₃` is a true
implication and is the arrow the architecture asked for, but its hypothesis is rule 15
class (iii) at legitimate presentations, so **the arrow does not establish "CCC₂ implies CCC₃
under internal ZFC"**. The correct classical route goes elsewhere: a maximal antichain in the
downward closure of `b`, then a selection of an element of `b` above each member. That route
needs `MaximalExtension` at the downward closure, plus M's choice, plus an
image-cardinality lemma, and **the image lemma is itself an open row**, because "the image of
a countable set is countable" is about surjections and this package's countability is
`injectable`, an injection. Track B landed the surjection form separately
(`CardinalOrder.agda:180`, `:187`) and **nothing in this tree relates the two**; without
choice they are different notions.

### 6.2 The CCC equivalence reduces to exactly `GreedySupply`, with three routes each stopping at a named place

`GreedySpec` (`CCCEquivalence.agda:780`) is the fixpoint equation a transfinite greedy
recursion along `lt` would satisfy, written with no recursion in it. `greedy→maximal`
(`:874`) proves that **any** set satisfying it is a maximal antichain extending the given one,
from trichotomy, the antichain law of `d`, and one `LEM ℓ`. So the distance from
`GroundWellOrder` to `MaximalExtension` is **exactly the existence of a solution**,
`GreedySupply` (`:890`), and `greedy→extension` (`:895`) is the arrow. Measured: `GreedySupply`
has **no filler anywhere in the compile root**; its only other occurrences are its consumer at
`:895` and the seam probe at `CCCEquivalenceAtA.agda:178`.

The three routes, each measured over the whole compile root comment stripped:

1. **Bell's own** (`fulltext:4978-4983`), enumerate `A ∪ {(⋁A)*}` by an ordinal of M and
   subtract transfinitely. **Stops at the vocabulary.** `transfinite`, `Hartogs`, `enumerat`,
   `orderType`, `otp`, `wfRec`, `wellFoundedRec` each measure zero, and `OrdinaryProfile.agda`
   declares no recursion theorem of any kind.
2. **The approximation method**, cut the `lt`-approximations by Separation and take the union.
   **Stops at definability, and the boundary is in the file.** `lt-induction` (`:292`) proves
   induction along the well ordering **is** available at this profile, so well-foundedness is
   not the obstruction. `Separation` reads a `Formula S 1` (`OrdinaryProfile.agda:88-90`), and
   `lt` has **no formula anywhere**: it occurs only as a bare `S → S → Ω`, and a search for any
   `ltAt` / `ltΔ` / `ltFo` / `Ltφ` shaped name returns zero. **Route 2 cannot cut its first
   set.** That missing datum is `LtDefinable` (`:367`), and part 3 shows what granting it buys.
3. **The host recursion combinator.** Cubical's `WFI.induction` exists and this tree uses it
   27 times (Track C's count, `CCCEquivalence.agda:82-96`, attributed). **Stops twice, both at O3b.** Every use feeds it a **host** `WellFounded` proof
   taken as a parameter, and nothing in the tree produces one: a comment stripped search for a
   declaration concluding `WellFounded` returns parameters only, twenty of them, and no
   theorem. Producing `WellFounded lt` from the triple needs the least-element principle over a
   **host** predicate `S → Ω`, which is ground class Separation, which is O3b and is K6's own
   poisoned form. **And granting it would not finish**: the recursion returns a host predicate
   on codes, and turning that into the single ground set `e : S` needs a second Separation over
   a host predicate. What it would produce is precisely `HostMaximalExtension.agda-break` at
   exit 0.

**What it does close, and it was cheap.** `wo→choiceSet` (`:375`) proves the converse the
coordinator named as the most reusable theorem K7 could deliver: `GroundWellOrder` plus
`Separation` plus `Collection` plus `LtDefinable` gives the profile's own `ChoiceSet`, through
`least-contr` and `hasImage′`. **So K7's well ordering is at least as strong as the profile's
internal choice, which is what "consumes M's choice" has to mean.** The other direction,
`ChoiceSet ⟹ GroundWellOrder`, **has no proof in this tree**. Re-measured here over all 130
`.agda` files of the compile root, comment stripped: `ChoiceSet` has **13 occurrences across 6
files**, of which 2 are K7's (section 1) and 11 are in 4 other files (`OrdinaryProfile.agda`
3, `K6/Choice.agda` 5, `K6/Refuted.agda` 2, `K6/ChoiceAtStructures.agda` 1). **None is in a
hypothesis position producing the triple.** Part 0d's census said "11 across 5 files"; the
occurrence count is right and the file count is one too many. The price of the missing
direction is Zermelo, and the profile has neither transfinite recursion nor an ordinal
enumeration.

**And one thing the census turns up that the ledger should carry forward.** Two of the eleven,
`K6/Choice.agda:943` and `K6/ChoiceAtStructures.agda:201`, are `GroundWellOrder → ChoiceSet`
slots, that is the same **direction** Track C proved. They are **not discharged by
`wo→choiceSet`** and no claim is made that they are: K6's are at the **extension**
`𝒮ᴾ[ G ]` and are conditional on eleven further data including `LEM ℓ` and `⟨ Positive ⟩`,
while K7's is at the **ground** and costs `Separation` + `Collection` + `LtDefinable`.
Whether the ground proof transports is a question nobody in this package asked.

### 6.3 `valΔ` is NOT Track E's entire residue

Architecture Part 0c says "**`valΔ` is the entire residue**", and `O7/Supply.agda` module
`Chain` (`:209-242`) does machine check that `forcesΔ` follows from `valΔ` plus the K5 below
pair plus K6's forced set. **That is true of the forcing side and false of Track E.**

Track E's own header names four data and calls the fourth a second residue:
**the internal graph of the check map on `β`**, `chkFo : Formula S 2` with
`chkFo-reading` (`PossibleValues.agda:297-301`). The file states why O7 does not discharge it
(`:279-294`): **O7 makes the forcing relation definable at FIXED name codes; the coordinate by
coordinate bound needs it at a code that VARIES with a ground set, and no renaming of
`forcesΔ` reaches that.** It is class (ii): at a genuine extension the check map is an `∈`
recursion and is ground definable and its restriction to a set is a set by ground Replacement;
the tree has no internal recursion machine, the same gap `NameImage.agda:395-400` records.

The break confirms it by type error. `CheckCodeGap` (exit 42) attempts exactly the step the
architecture's 4.5 sketch printed, filling O7's second name slot with the ground element `a`
rather than with `fst (chk a)`. The error is `a != (fst (chk a)) of type S`. **A check name is
a set of entries and a ground set is not.** The architecture's 4.5 sketch hid the second
residue inside a would-be fourth projection whose stated reading is ill formed.

`module FromTable` (`PossibleValues.agda:533`) discharges the second residue from a ground
set, so the row is reduced rather than open, but it is a row and `valΔ` is not alone on it.

### 6.4 The Maximum Principle is NOT Track H's blocker; the union bound is

Ruling Q4's **conclusion survives and its reason is refuted.** Bell needs 1.27 because he
never leaves `V(B)`: to turn `[∃f φ(f)] ≠ 0` into a single name he must attain a supremum in a
Boolean algebra. **K6 already left `V(B)`.** The extension is an ordinary first-order structure
over `Nm`, and `FOL/Semantics.lagda.md:120` reads `∃̇` as `⋁` over the carrier, so

```
ext-existential : ∀ {k} (φ : Formula Nm (suc k)) (ν : Vec Nm k)
                → (ν ⊨ᴱ (∃̇ φ)) ≡ ⋁ Nm (λ τ → (τ ∷ ν) ⊨ᴱ φ)
ext-existential φ ν = refl
```

at **`Cofinality.agda:735-737`**. There is no supremum to attain; the witnessing name is handed
over. What paid for it is K6's truth lemma, already paid. **K7 must not request fullness from
K4, and not because it is refused.** `k4-architecture.md:998` predicted a repair by truncated
elimination; the confirmed form is stronger: the elimination never has to happen.

**The real blocker is the union bound.** Re-measured at `Cofinality.agda:137-140`: no
declaration anywhere in the compile root states that a union of β-many `w`-countable ground
sets injects into anything, and **no K7 file uses the `Union` axiom at all** (independently
confirmed here, section 1.3). Track F states the consequence as `ProvedRange`
(`NoCollapse.agda:582`) and tags it class (ii) with the reason. Cofinality preservation is
re-owned to whoever funds that, **not to K12a for fullness**.

**And a correction inside K7 itself, which the ledger must not smooth over.**
`NoCollapse.agda:765-772` diagnoses its own gap correctly ("a cofinal range need not contain
any given member of κ") and then, in the next sentence, attributes the blocker to the Maximum
Principle. **Those two sentences name different things and only the first is this programme's
obstruction.** Track F's type is right and one sentence of its prose is not. Two tracks, F and
H, measured the covering-versus-cofinal gap independently and agree; they disagree on the
attribution of the blocker, and the evidence, `ext-existential` by `refl`, is on Track H's
side.

### 6.5 `paths` is class (iii) at the extension, and the coordinator put it in the shared spine

Track B refused the shared spine's `paths` and was right. `K6/Ordinals.agda:141` builds `𝒮ᴱ`
with `_≈ˢ_ = λ σ τ → fst σ ≈[G] fst τ`, and `Nm` is a Σ-type and **not a quotient**, so
`paths`, which asserts `≈ˢ` **is** the path type, is **false there**. A track carrying it could
not be instantiated at the extension at all.

Measured here: **`paths` occurs 0 times in `K7/CardinalOrder.agda`**, comment stripped.
`module Order` (`:252`) takes `Extensionality` plus two membership congruences instead, which
are class (i) at **both** structures, and `CardinalOrderAtBridge.agda` instantiates the whole
of part 3 at K6's extension structure to prove it, with `paths` not available there and not
needed.

### 6.6 The chain condition is unwitnessed non-trivially anywhere, and the census is sharper than the architecture's

Track J's headline, re-measured here independently and confirming it exactly. `injectable x y`
is `⋁ S (λ f → isInjection f x y)` (`CardinalBridge.agda:382-383`), a truncated join over a
ground **code**, so producing one means exhibiting an injection's graph as a set of the model.

**Every declaration in the compile root whose conclusion is an `⟨ injectable _ _ ⟩`:**

* **Producers, no `injectable` among their hypotheses, TWO.**
  `injectable-incl` (`CardinalOrder.agda:886-887`), on `Separation` + `Collection` + `Pairing`,
  producing `injectable a b` **only for `a ⊆ b`**; and `injectable-refl` (`:950-951`), which is
  `injectable-incl` at `a = a`.
* **Non-producers, each taking an `injectable`, SIX.** `injectable-mono-dom`
  (`ChainConditions.agda:280` and `CardinalOrder.agda:299`), `injectable-mono-cod` (`:308`),
  `injectable-cong` (`:315`), `injectable-cong-cod` (`:322`), `injectable-trans` (`:1046`).

**So every `injectable` this programme can produce comes from an inclusion**, and
`⟨ injectable d w ⟩` is available exactly where `⟨ subsetΔ d w ⟩` is. A chain condition holds
today exactly at a presentation whose antichains are all subsets of the ground `ω` code, and
at no other. At the empty presentation that is met vacuously and `CCC₂` is a theorem
(section 5.4). **At the one-point presentation it is not met**, because the one-point carrier
is not a subset of `w` and nothing supplies that.

**This refutes the sentence in Track F's own header** that at the one-point notion "every
antichain is a subset of a singleton and CCC₂ is trivially true". `Refuted.agda:523-532`
proves both directions: `CCC₂` there is exactly "every subset of the carrier injects into
`w`", with the antichain hypothesis discarded in the forward direction. **CCC₂ at the only
presentation this programme has is neither trivially true nor provable.**

The theorem stays correctly conditional. What the ledger row must not say is that the
hypothesis is trivially available.

### 6.7 The one-point presentation is the only inhabitant, re-verified here

`𝔓 : CC.Presentation` at `K6/OnePoint.agda:158` is the only inhabitant of
`CodedCompletion.Presentation` in the compile root. Every other non-comment occurrence of the
record name is a parameter declaration (`NameWeight.agda:139`, `:381`,
`K4/InstanceCoded.agda:114`, `K5/InstanceBase.agda:80`, `K5/InstanceValue.agda:65`,
`K5/ProbeD1.agda:39`, `K5/ProbeI1.agda:39` through `K5/ProbeI6.agda:40`, and K7's two seam
probes) or a function of an assumed presentation (`Certificate.agda:992`, the host record's
`B⁺`). Confirmed.

`antichain-transfer←` does not exist. `grep -rn antichain-transfer` returns two lines, both
`antichain-transfer→` at `CodedCompletion.agda:1055` and `:1057`, while `dense` and `predense`
have both directions. Confirmed, unchanged from architecture G2.

---

## 7. METHODOLOGY THIS PACKAGE ESTABLISHED

Two are new and both matter beyond K7.

### 7.1 A Δ₀ certificate is not a correctness check

`checkΔ₀` recurses on the connectives and never inspects a slot (`bounded` at
`FOL/LevyHierarchy.lagda.md:101-113`). So it passes on a poisoned formula **exactly as** on
the correct one whenever the poison is a slot permutation or a de Bruijn shift at uniform
depth. Three breaks measure this on three different formulas: `OrdinalDeltaBlind` (the K1
linearity bug at `IsOrdinalφ`), `AntichainSwapIsDelta0` (two mutilations of Track A's new
antichain formula), `CofinalBound` (the same defect at `IsCofinalφ`).

**Track H sharpened it to the form that matters.** `CofinalBound` exits 0 with a formula that
is well scoped, Δ₀-certified, **and has a `refl` reading theorem against its own unfolding**,
while `vacuous` proves the predicate collapses. A track that writes its reading theorem by
unfolding the formula it has just written gets a `refl` and learns nothing.

**The recipe that does discriminate, in three parts.**

1. Write the **host side first**, from the mathematics, before the formula exists.
2. Prove the reading theorem **against that host predicate**, not against the formula's own
   unfolding. `AntichainSwapReading`, `OrdinalRespellReading`, `SurjRespell`, `RegularBound`
   and `CofinalSwap` are five exit-42 confirmations that this step catches what `checkΔ₀`
   does not.
3. Run a **vacuity probe**: exhibit the predicate holding of an arbitrary object from
   hypotheses that carry no content. `OrdinalDeltaBlind`'s `poisoned-is-transitivity` and
   `CofinalBound`'s `vacuous` are the two instances.

### 7.2 A report's "X does not exist" is valid only as of its own timestamp

**Raw token counts over this root are now useless.** Nine tracks landed mid-flight, so a
census taken early is stale by the end.

The canonical instance, and **neither track erred**: Track F correctly measured
`injectable-trans` and `injectable-incl` absent from Track B's file, recording at
`PreserveAtTracks.agda:32-35` that "the only occurrence of either token in
`K7/CardinalOrder.agda` is the header comment at `:16`", and **Track B landed them afterwards**
at `CardinalOrder.agda:1046` and `:886`. Both measurements were true when taken. The same
shape recurs inside Track J, whose part 1b says in its own words that its first census was
"SUPERSEDED BY A LANDING" and was re-run at the end of the session; and again at
`Cofinality.agda:129-131`, where Track H refuses to repeat architecture G3's "injectable has
ZERO theorems" because it is now stale.

**The stable measurement recipe, in the form Track H wrote it and this ledger used:**

```
grep -rnE --include='*.agda' '^ *<token>[A-Za-zΔφ]* +:' .
```

run on comment stripped text, which counts **declarations** and not mentions. Run here for
ruling Q4's four tokens it returns: `cofinal` 0, `cofinality` 0, `singular` 0, and
**`isRegular` THREE**, at `HostRegularOpen.agda:229`, `CodedVocabulary.agda:303` and
`K7/Cofinality.agda:391`. The first two are the regular-**open** sense and the third is
Track H's own new cardinal sense.

**Every "X does not exist" row in this ledger carries the recipe's result and the date of this
pass, and nothing older.**

### 7.3 Two smaller conventions worth carrying

* **A positive check runs at the APPLICATION, never at the definition** (device D-II,
  inherited from K6's exit item X7 failure). **Seven of the nine tracks ship a seam probe**
  that fills its telescope from the real producer; H and J do not, H because it ships no
  inhabitant and J because it is the audit. Each probe caught something no grep at the
  definition could have: `PreserveAtTracks` returned four corrections to the architecture
  (`:20-48`), `AlephAtStructures` filled `chk-ordinal`, which `K6/Ordinals.agda:179-180` takes
  as a parameter and no file had ever filled, `ValuesAtNames` checked by `refl` that the
  extension structure Track E builds as a record literal **is** K5's own, and
  `CCCEquivalenceAtA` made Track C's two obligation types an **alias** of Track A's rather
  than a second opinion.
* **A break is not a result until its log is on disk.** K7 shipped 36 logs for 36 breaks.
  K6 shipped 0 for 40 and the coordinator had to re-run them all afterwards, invalidating one
  harness on the way. The convention costs nothing and it is the reason section 3's tally is a
  measurement rather than an attribution.

---

## 8. THE COORDINATOR'S FAILURES

Part 0e records five. Here they are with what the ledger adds, followed by the ones found
since. Stated plainly, without softening.

**The five in Part 0e.**

1. **Opacity was named as a protection and is not one.** Part 0d's "no host function can be
   passed where it is expected" is false at both lines it cites. Refuted at
   `Refuted.agda:658`, and the slot is eliminable by `refl` at `:677-681`. Section 4.1.
2. **The certificate's telescope dropped `inhabited`**, so the whole transfer instantiates at
   the empty presentation and every slot but one is defeated. Section 5.
3. **Ruling Q4's reason is refuted.** The Maximum Principle is not Track H's blocker;
   `ext-existential` is `refl`. The conclusion survives its evidence. Section 6.4.
4. **The premise the coordinator gave Track H was false on one token.** `isRegular` was
   stated to measure zero declarations; it measures two (three, after Track H landed).
5. **`paths` is class (iii) at the extension and the coordinator put it in the shared spine.**
   Track B refused it. Section 6.5.

**And five from Part 0d, three of which withdrew a ruling.**

6. **Ruling Q3 authorised a widening that does not exist**, and it is withdrawn.
   `GroundDescription.hasImage′` (`:181-185`) takes `Separation` and `Collection` as two
   standalone arguments, not the `OrdinaryZF` record, and K3 and K4 already consume it that
   way. K7 records no widening.
7. **Architecture 2.4's sketched `CCCHypotheses` fields are inadmissible as written**, because
   `Ω = hProp ℓ : Type (ℓ-suc ℓ)`. Measured at exit 42, `[ConstructorDoesNotFitInData]`
   (`PredicateField.log`).
8. **A `GroundWellOrder` at `Type ℓ` was reported as "typechecked and could never have been
   instantiated".** Track C measured the claim in both spellings and **corrected it**: the
   **record** spelling does **not** typecheck (`GWORecordAtTypeL`, exit 42, and the message
   names `S → S → Ω` as the offending argument). Only the **parameter** spelling has the
   silent shape (`GWOParamAtTypeL`, exit 0). The hazard a K7 reader should carry is the
   parameter one.
9. **`ChoiceSet ⟹ GroundWellOrder` has no proof in this tree**, confirmed by census, and the
   converse is one lemma away and was taken. Section 6.2.
10. **`GroundWellOrder` is nowhere a record** in K6, only an opaque parameter, so Track C had
    to declare it itself.

**Ruling 13, the coordinator's own correction.** The O3b `file:line` in every brief since K6
was wrong: `TranslateForward.agda:21` and `TranslateReverse.agda:73` are **comment lines
describing the datum**. The flat takers are `TranslateForward.agda:185-188` and
`TranslateReverse.agda:390-393`. Same shape as the coordinator's four K6 errors: a citation
pointing at where a thing is described rather than where it is declared.

**Found since, and added here.**

11. **The architecture's printed `antichainΔ` at 2.1 is not Track A's.** `refl` refused,
    `ArchAntichainRefl.log`, exit 42. The two are logically equivalent, proved once at
    `Refuted.agda:160-167` so nobody else has to, and **not** definitionally equal.
12. **`CompletionTransfer.agda:499` records the `[ConstructorDoesNotFitInData]` rejection "at
    exit 1". Re-run, it is exit 42**, log at `K7/breaks/PredicateField.log`.
13. **Architecture 3.9's second clause is wrong.** It says at the one-point notion "every Sub
    is an antichain and all three chain conditions hold vacuously". The first clause is right.
    The second is false for K7's predicates: `one-point` (`K6/OnePoint.agda:200-201`)
    discharges the conclusion `p ≡ q` of the **host** antichain predicate, while `CCC₂ᴵ`
    concludes `injectable d w`, about which it says nothing. Two tracks measured this
    independently (`OnePointDiscriminates`, Track A; `AntichainAtOnePoint`, Track F) and agree.
14. **Architecture 2.2 prints `CCC₂ᴵ : S → Ω`. It is `S → S → S → Ω`**
    (`ChainConditions.agda:305`), carrier and order explicit.
15. **Architecture 2.5 prints `valuesOf : Collection → Separation → (f : Nm) (β ξ : S) → S`.
    It is `valuesOf : Separation → (f : Nm) (ξ : S) → S`** (`PossibleValues.agda:452-453`),
    with the bound a module parameter and **no `Collection` spent**.
16. **Architecture 2.6's sketch has `ord-compare` taking `Pairing`. It does not**
    (`CardinalOrder.agda:478-480`); Track B measured it unused and removed it.
17. **Architecture 4.11's B-to-F edge names `injectable-trans` and `injectable-incl` as
    available.** They were not, when Track F measured; they are now. Section 7.2.
18. **Architecture G3's "`injectable` has ZERO theorems" is stale**, re-measured by Track H at
    `Cofinality.agda:129-136` against the current root: seven declarations, listed at section 6.6.
19. **Architecture 4.5's Track E sketch hid the second residue inside a would-be fourth
    projection whose stated reading is ill formed.** Section 6.3, with the type error at
    `CheckCodeGap.log`.
20. **Architecture 2.3 calls `MaximalExtensionIn` "the same Zorn-shaped obligation".** It is
    not an obligation of ZFC at all. Section 6.1.
21. **The Track K brief's own two errors, recorded under the same rule.** It says "eight
    exit-0 breaks" and then names ten; the measurement is **sixteen** (section 3). And it says
    "Every exit code in this package is confirmed by a log"; the five O7 logs are **zero
    bytes** (section 0.1).
22. **One error inside a track, recorded so it is not carried forward.** Track J's
    selection-scope census says three files and twelve; it is five and seventeen (section 4.3).
    The finding the census supports is unchanged.

---

## 9. WHAT K7 HANDS FORWARD

Five rows, with owners where an owner exists, and three smaller ones at 9.6.

### 9.1 The `inhabited` repair. One line. No owner assigned.

Add `inhabited` to `module Structural`'s telescope at `CompletionTransfer.agda:251`, matching
`CodedCompletion.agda:208`. That single line closes the degenerate audit of section 5: with the
carrier forced inhabited, the empty presentation is no longer an instance, and `OrderGraphFor`,
`MaximalExtension`, `MaximalExtensionIn` and the six `CCCHypotheses` fields stop being free.
**It is not made here; rule 14 says transcribe and report.** It is the cheapest structural
improvement available to this package and it should be made before K8 instantiates anything.

### 9.2 The union bound. Unfunded. Cofinality preservation waits on it.

**No declaration anywhere in the compile root states that a union of β-many `w`-countable
ground sets injects into anything, and no K7 file uses the `Union` axiom at all.** Measured
here and by Track H independently. This is what `ProvedRange` (`NoCollapse.agda:582`) and
`ProvedRangeHolds` (`:599`) assert without proof; it is a theorem of ZFC in the ground for
every cardinal κ with ω ∈ κ, singular ones included, and it is class (ii) here because the
ordinary profile has **no ordinal arithmetic, no Hartogs construction and no transfinite
recursion**. Track H's `GroundCover` (`Cofinality.agda:824`) is the same gap from the other
end, and `cover→bounded` (`:835`) closes `NoShortCofinal` the moment it is supplied. **Whoever
funds the union bound owns cofinality preservation. It is not K12a and not fullness.**

### 9.3 `GreedySupply`. Class (ii). No filler in this tree.

`CCCEquivalence.agda:890`. The existence of a solution to the greedy equation, which is the
entire distance between M's well ordering and `MaximalExtension`, and therefore between CCC₁
and CCC₂. `greedy→maximal` proves the equation alone forces maximality; the three routes and
their exact stopping places are section 6.2. Supplying it closes D3b and D3d together.

### 9.4 `chk-injectable`. True at every extension. **No owner anywhere.**

```
chk-injectable : (a b : S) → ⟨ injectableᴳ a b ⟩ → ⟨ injectableᴱ (chk a) (chk b) ⟩
```

`Aleph.agda:321`, forwarded at `AlephAtStructures.agda:264`. Measured: those are the only two
non-comment occurrences in the compile root, both telescope parameters, **no producer**.
`AlephAtStructures.agda:40` says in its own words that it "has no owner anywhere". The upward
transfer is not free because `IsInjectionφ` is not Δ₀ in either direction: `IsFunctionφ`
carries three unbounded `∀̇` (`CardinalBridge.agda:176-182`) and `InjDomφ` two unbounded `∃̇`
(`:257-261`), so K5's `groundSat`, whose `∃̇` and `∀̇` clauses are absurd patterns on the Δ₀
witness (`K5/Structures.agda:689-690`), does not carry it across the check map.

**And the hazard beside it, which is the reason this row must be read before it is filled.**
Its **reversal** buys ω₁ preservation with Track F's entire hypothesis column removed, at exit
0 (`AlephViaDownward`, section 3.1), and it is false at exactly the extensions the theorem is
interesting at. Nothing in either type says which way the implication runs. What protects
Track G is that `chk-injectable` is written in the telescope with its direction visible, that
its reversal is transcribed and not inhabited, as `NotClaimed-InjectableDown`
(`Aleph.agda:250`) inside `module Boundary` (`:207`), and that `Boundary` is a **sibling** of
`module Aleph` (`:258`).

### 9.5 "No nontrivial coded presentation." Owner K8, `roadmap:219`.

This is O4's residual and it is the row that makes every chain-condition hypothesis in the
package unwitnessed. The only inhabitant of `CodedCompletion.Presentation` is
`K6/OnePoint.agda:158` (section 6.7), and there the chain condition **cannot see the order**
(section 3.1, two tracks agreeing). So:

* No hypothesis of the form `⟨ CCC₂ᴵ c o w ⟩` can be shown load bearing **by instance** in
  this tree, only **by break** (`NoCCC`, exit 42).
* Track F passes the T3 check, and it passes it **for exactly the reason that makes its
  hypothesis unwitnessed**: `ccc-use`'s conclusion is `⟨ injectable d w ⟩`, and nothing in the
  compile root produces one except from an inclusion. One measured fact does both jobs, and a
  ledger that reports only the first has reported half of it (`Refuted.agda:984-993`).
* K8 builds the Cohen poset as a coded presentation and proves CCC₂(P). **Until it does, every
  preservation theorem in K7 is a true implication with an unwitnessed antecedent.**

### 9.6 Three smaller rows, for completeness

* **O6-for-B⁺**, `OrderGraphFor` at `CompletionTransfer.agda:222`, typed and not built, route
  priced at source: one `Separation` out of the double power set of `B⁺set` (+`PowerSet`), plus
  component recovery through `kpair-det` composed with `entry-isKPair` and `entry-fst`
  (+`Pairing`), plus the `NameKernel` `entry` interface. It is a construction and belongs
  beside `K6/OnePoint` rather than in a certificate track.
* **The second residue of Track E**, the internal graph of `chk` on `β`
  (`PossibleValues.agda:297-301`), class (ii), discharged from a ground set by `module
  FromTable` and open at the abstract frame. Section 6.3.
* **The surjection-to-injection bridge.** Track B landed `IsSurjectionφ`
  (`CardinalOrder.agda:180`) and `Surjectableφ` (`:225`); nothing in this tree relates them to
  `injectable`, and without choice they are different notions. The correct route to
  `ccc₂→ccc₃` needs it. Section 6.1.

---

## 10. WHAT THIS LEDGER DID NOT CHECK

Stated so no reader over-reads section 1.

* **No Agda was run.** Every exit code here is read from a log on disk or attributed to a
  named source. This track started no process and compiled nothing.
* **The five O7 exit codes and their ten timing figures are attributed**, because the five log
  files are zero bytes (section 0.1). The O7 mathematics was read; the O7 compilation was not
  confirmed.
* **No K7 telescope was instantiated by this track.** The degenerate audit of section 5 is
  Track J's, run at exit 0, and re-read here rather than re-run. In particular **nobody ran
  step 1 of the T3 check on Track F's own telescope**, whose seventeen slots include `forces`,
  `truth-at` and a `valuesOf` specification over an abstract `Cond`; `Refuted.agda:994-998`
  names that as a gap rather than an omission, and the reason is architecture 1.7's measurement
  that composing the engine costs 102.95 s and 9.08 GB.
* **The forbidden-spelling sweep found eight tokens with non-zero counts, all in one file and
  all legitimate.** `Fullness` 4, `MaximumPrinciple` 4, `Refinement` 5, `MixtureSupply` 3,
  `Mixture` 5, `WitnessSpec` 2, `ValueCover` 2, `ElementPrinciple` 2, every one of them between
  `Refuted.agda:863` and `:905`, inside `module K4NonClaims` and `module Mixing`, transcribed
  under rule 14, **uninhabited, and imported by nothing**. `Refuted.agda` is the named non-zero
  partner that device D-I requires so that a census which is zero everywhere cannot pass by
  accident. A sweep run without reading where the hits are will report a violation.
* **Two claims in this ledger rest on Track reports rather than on source read here**: Track
  D's 10.71 s / 1.43 GB seam figure, and the 27 uses of `WFI.induction` with twenty
  `WellFounded` parameters and no theorem. Both are attributed to their tracks by `file:line`
  above.
