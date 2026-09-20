# K5 the poset-side forcing relation, the generic filter, and the truth lemma

Date: 2026-09-12. Source baseline: `cbd1510e`. Branch `research/forcing-cohen-k0`.
Status: K5 COMPLETE on its roadmap scope with two named exceptions, both in
section 3, and one measurement left open, in section 6. Ten proof tracks A
through J wrote Agda and an eleventh, Track K, wrote the consolidated assumption
ledger and no code. Thirty-two files, 9972 lines, every one carrying
`--cubical --safe --guardedness` on line 1. The terminology track is blocked on
an owner ruling and blocks no code; see section 9. This record follows the K0,
K1, K2, K3 and K4 convention: proof work lives in a task-specific temporary
compile root, the sources are archived outside it, and no repository source file
is changed.

Every line count and hash below was computed for this record from the archived
bytes at `~/Agentic/bedrock-proofs-archive/k5/`. Three line counts printed in
the track reports do not match their files, which is why none is copied from
prose: `ClausesAtFrame.agda` is 98 and `REPORT-B.md:11` says 113;
`Structures.agda` is 825 and `REPORT-F.md:22` says 822; `ExtensionSat.agda` is
332 and the same line says 331. Every other line count in all ten reports
matches to the line, and no mathematical claim depends on any of the three.

## 1. What K5 delivers

The roadmap's K5 transports the compiler and semantics to the poset and proves
the ordinary clauses, valuation agreement, generic truth and the extension
correspondence (`cohen-implementation-roadmap-2026-09.md:197-203`). Thirty-two
files:

| File | Track | What | Lines | SHA-256 prefix |
|---|---|---|---|---|
| `Frame.agda` | A | the abstract forcing frame, `ForcingBase` and `_⊩ᴮ_` | 414 | `0e178f5c69c1b6c9` |
| `ProbeD1.agda` | A | decision D1 at the coded completion | 121 | `3b8980386198f2fb` |
| `Clauses.agda` | B | the ten clauses, `⊩-clauses` and `⊩-unique` | 965 | `f2cac0816966b8ad` |
| `ClausesAtFrame.agda` | B | the Track A seam, nine parameters filled | 98 | `18326520f9f51e88` |
| `Dense.agda` | C | the four coded dense sets and `MeetsAll` | 727 | `fca776b36b29f460` |
| `ProbeC.agda` | C | the Track C into Track D interface | 77 | `c16bd69bad9340fb` |
| `Generic.agda` | D | `Uof`, the filter laws, reflection and the ultrafilter clause | 460 | `9bb0942975fd7080` |
| `ProbeD.agda` | D | Track D's own seam | 237 | `0a20675addef2e8f` |
| `Agreement.agda` | E | `≈-agree`, `∈-agree` and the two standard-name corollaries | 699 | `40aab1b397abcc2e` |
| `AgreementAtTranslation.agda` | E | K3's real forward translation supplied | 153 | `207c6fccac513d78` |
| `AgreementAtUof.agda` | E | the bridge at `Uof G` | 173 | `12e5b10d18c89f92` |
| `Structures.agda` | F | the two extension structures and the ground copy | 825 | `a75f970a213b3d8a` |
| `ExtensionSat.agda` | F | `ext-⊨`, satisfaction across the extension map | 332 | `141428ca9f804147` |
| `Truth.agda` | G | `join-prime`, `meet-complete`, `truth`, `not-both`, `decided` | 1029 | `2dc09583569575f4` |
| `TruthAtFrame.agda` | G | the truth lemma's seam, applied not asserted | 230 | `2aa6cdbe1489b5b8` |
| `RoundTrip.agda` | H | `ext-onto` and `ext-surjective` | 549 | `9b480a445e090666` |
| `RoundTripAtUof.agda` | H | the two `U` entailments at `Uof G` | 167 | `1e286562501a1b5d` |
| `RoundTripAtValue.agda` | H | the value relation at `(B, ≤ᴮ)` | 184 | `76dd062574f1b5c7` |
| `RoundTripAtReverse.agda` | H | K3's reverse translation, with `image` still a variable | 141 | `cb90a39857ab71b4` |
| `InstanceBase.agda` | I | `codedBase`, all fourteen frame fields at the coded completion | 365 | `65bf52a8380afb8b` |
| `InstanceValue.agda` | I | `val` and K4's fourteen interpretation laws | 232 | `48c7b2777a6acaeb` |
| `ProbeI1.agda` … `ProbeI6.agda` | I | probe 0's four-rung ladder and two scope probes | 616 | see below |
| `RefutedClauses.agda` | J | the three-element "V", and separativity does not repair | 400 | `cecaaf2a901b256f` |
| `AntichainControl.agda` | J | both naive clauses are theorems at an antichain | 167 | `5837618f8db34b0e` |
| `RefutedOrder.agda` | J | order reflection, `SameName`, `i` not onto | 221 | `b966afb65fad0f0d` |
| `RefutedGenericity.agda` | J | the binary tree, atomless, and no host generic on it | 247 | `0ae5d881417402cd` |
| `Refuted.agda` | J | the packaged refutation statements | 143 | `e4fe20c00b6e4a8e` |

The six Track I probes are `ProbeI1.agda` 93 `4ca10ec4a6b25f23`, `ProbeI2.agda`
135 `9aa08a7659f17377`, `ProbeI3.agda` 130 `ef73e6e9de4ebd5f`, `ProbeI4.agda`
128 `b7e89db16420897e`, `ProbeI5.agda` 53 `ec3eae88ac4a5698` and `ProbeI6.agda`
77 `fdda9dce4c8f7505`.

Thirty of the thirty-two are expected to reach exit 0. `ProbeI4.agda` and
`ProbeI6.agda` are probe 0's negative rungs and were killed at a 471 second and
a 200 second cap; their logs carry one `Checking` line and no timing block,
which is the on-disk signature of a killed run. The coordinator's count of the
package is 24 deliverables and six green seam probes and evidence files. This
record does not recompute that split: the reports label nine files "evidence,
not a deliverable" or "seam probe", and the arithmetic that yields six leaves
`ProbeC`, `ProbeD1`, `ProbeI1`, `ProbeI2`, `ProbeI3` and `ProbeI5` outside the
24, with `K5/ProbeD.agda` the one file the two conventions classify
differently. The figure 24 is the coordinator's and is relayed as such.

Eighteen further files are deliberate breaks, parked with `.agda-break`
extensions under `breaks/`, `breaksE/`, `fbreaks/` and `gbreaks/` with their
logs. Track F's three were live `.agda` files in the compile root while
`LEDGER-K.md` measured, and a tree-wide check therefore reported three exit 42
results that were successes of the method; they have since been parked, and the
live root now holds 32 K5 `.agda` files and the parked
`AgreementAtDense.agda-slow`.

The architecture that produced all of this is
`~/Agentic/bedrock-proofs-archive/k5-architecture.md`, 717 lines, also archived.
It was never compiled, which was the same deliberate trade K2, K3 and K4 made.
Sections 3 and 4 are what it cost, and it was paid in measured refutations
rather than in silent errors.

## 2. The constraints K5 exists to respect, and how each is enforced

### Genericity means meeting every coded dense set

The roadmap's sentence is that generic correspondence "must meet all coded dense
subsets, not just the maximal antichains available under an unstated Choice
principle" (`cohen-implementation-roadmap-2026-09.md:201`). Track C's `MeetsAll`
(`K5/Dense.agda:482-487`) is K2's `meets` field character for character, and its
dense sets are ground codes `d : S`. The enforcement is a level fact rather than
a habit: the type elaborates at `Type ℓ` only because the dense sets are codes,
and break C5, which replaces the code by a host subset, fails with
`[UnequalSorts] Type (ℓ-suc ℓ) != Type ℓ` at the annotation itself. Measured
over all 32 files with comments stripped, `predense` is 0 everywhere and
`antichain` and `separative` are non-zero only in Track J's refutation files,
where they are the refutation targets.

### No maximum-principle witness anywhere

The existential step of the truth lemma is the one place a textbook reaches for
a name attaining the supremum. Track G replaces it with a coded set met at the
generic: `witnessAt-denseBelow` makes `witnessAt V` dense below a condition,
`generic-meets-denseBelow` meets it, `witnessAt-force` turns the result into a
forced member of the value set, and `attained-elim` (`K4/ValueSets.agda:314-318`)
turns that member into an index with target an `Ω`. Nothing anywhere asks for an
index given a member. Measured over all 32 files with comments stripped,
`Fullness`, `MaximumPrinciple`, `Refinement`, `Mixture`, `WitnessSpec`,
`ValueCover`, `ElementPrinciple` and `AdequateDomain` are each 0 in every
position, hypotheses included.

### No internal global truth-value function

Bell page 24 forbids it and the roadmap repeats it. Every statement of the truth
lemma is at a fixed `φ` and a fixed `ν`; `truth` is a host-level family of
theorems indexed externally by a formula, and the ground cannot form the family.
The non-claim is source prose beside the `Sat` telescope it constrains, on K3's
and K4's model.

### The module parameter list is the ledger, and excluded middle is an argument

`LEM ℓ` is an explicit first argument of every K5 declaration that spends it.
The only module parameters carrying it are the three probe modules of
`K5/AgreementAtUof.agda` at `:136`, `:156` and `:166`, plus the parameters
`Uof-ultra`, `witnessAt-denseBelow` and `meets-below` of `K5/Truth.agda`, which
are transcriptions of other tracks' signatures rather than new decisions. The
same discipline governs cross-track seams: no K5 deliverable imports another
K5 deliverable. Track B's nine frame parameters, Track G's whole Track C and
Track D surface, and Track H's two `U` entailments all enter as flat parameters,
and each is proved to be the real thing in a separate seam file that applies the
supplier and ascribes the consumer's type character for character.

### The safety surface

`postulate`, `TERMINATING`, `NON_TERMINATING`, `trustMe` and U+2014 are each 0
in all 32 files with comments stripped, re-run for this record rather than
copied from a report. So are `Base.Choice`, `ChoiceSet`, `SetQuotients`,
`import L.`, `import V.`, `i-inj`, `isGeneric` and `ReadsSup` in every spelling.

## 3. The two roadmap requirements K5 found it cannot meet

Both are stated here without softening, because both are requirements the
roadmap names and K5 does not meet.

### 3.1 K5 ships no instance and no acceptance example at a concrete forcing notion

Track I built `codedBase : LEM ℓ → P.ForcingBase CO.B IC.codedLattice
IC.codedComplement` at `K5/InstanceBase.agda:309`, filling all fourteen fields
of Track A's record at the coded completion of an **arbitrary** presentation, on
`LEM ℓ` and nothing else. `K5/InstanceValue.agda` supplies `val` and
`valLaws : VC.InterpLaws`, K4's fourteen interpretation laws, at the same sealed
algebra. So everything Tracks A through H prove about an abstract frame holds at
the coded completion, and the abstract layer is a theory about something.

The record has fourteen fields, counted here directly from `K5/Frame.agda:148`:
`≼-refl`, `≼-trans`, `inhabited`, `i`, `i-mono`, `i-nonzero`, `i-compat→`,
`i-compat←`, `i-dense`, `below`, `below-sub`, `below-in`, `below-out`,
`below-regular`. All fourteen are filled at `K5/InstanceBase.agda:310-324`.
REPORT-A printed thirteen; this is the fifth independent count and every one
after the first says fourteen.

**What this is not.** `codedBase`'s type is an implication from a
`Presentation`, and no inhabitant of the coded `Presentation` exists anywhere in
the programme. Verified here by a census over the whole compile root rather than
taken from a report: the coded record is declared at `CodedCompletion.agda:201`,
`module Coded` takes it at `:210`, and it is a module parameter at `:261`,
`:1287`, `NameWeight.agda:139`, `:381`, `K4/InstanceCoded.agda:114` and in five
K5 files. The only `Presentation` inhabitants in the root are
`K2Bridge.agda:65-66` and `Certificate.agda:992`, and both inhabit the **host**
record at `Certificate.agda:366`, which lives at `Type (ℓ-suc ℓ)` and is a
different record. Separately, K2's three acceptance instances,
`Instances.NonRefined` at `Instances.agda:98`, `Instances.K0Four` at `:253` and
`Instances.Trivial` at `:483`, are host regular-open algebras whose elements are
host predicates, so they cannot inhabit `K4.Algebra.Lattice B`, whose points are
`Σ[ x ∈ S ] ⟨ x ∈ˢ B ⟩`, and therefore cannot inhabit `ForcingBase` either. Both
routes to a concrete notion are closed inside K5.

**The consequence in the roadmap's own terms.** Three of the roadmap's five exit
examples (`cohen-implementation-roadmap-2026-09.md:205`), "trivial forcing fixes
the ground", "a nonseparative P has the expected semantic translation" and "a
nontrivial existential exercises the compiler and generic truth", are not
runnable in K5 at all. The owner is K8. The two that are runnable are proved:
`check-faithful` (`Valuation.agda:655-657`) and `generic-value` (`:659-661`) are
K3's, at `isFilter` and instance-free, and Track E additionally has them on the
Boolean side as `check-faithful-at-positive` (`K5/Agreement.agda:612`),
`check-faithful-across` (`:619`), `generic-name-value-at-positive` (`:643`) and
`generic-name-value-across` (`:650`). The `-at-positive` forms take
`⟨ VP.positive G ⟩` and the `-across` forms route through `filter-positive`, so
the filter spelling is strictly the weaker statement and both ship.

### 3.2 "Corresponding model-relative generics" cannot mean the coded genericity predicate on both sides

The roadmap asks, for corresponding model-relative generics, for valuation
agreement and generic truth (`:201`). What K5 delivers on the Boolean side is
`Uof G` (`K5/Generic.agda:150-151`) with the filter laws all free
(`Uof-inhabited` `:176` at positivity, `Uof-up` `:182`, `Uof-dir` `:199` at
`isFilter`, `Uof-proper` `:227`), reflection of `G` (`generic-forward` `:169`
free, `generic-reflect` `:370` at `LEM ℓ` plus the genericity clause plus
`isFilter G`, packaged as `generic-bridge` `:411`), and the ultrafilter clause
`Uof-ultra` `:388` at `LEM ℓ` plus genericity.

**Boolean-side genericity is an unbuilt interface and not an unproved theorem.**
The reason is obstruction O6 and it is structural. `isGeneric` is declared
inside `CodedCompletion.Core` at `CodedCompletion.agda:1070`, and `Core` is
parameterized by a `Presentation` carrying `order : S` as a coded graph
(`:201-208`). `B` has no presentation: the coded order graph of the nonzero part
is the one thing K2 did not deliver, and building one needs the double power
set, a Separation against instantiated `prAtˢ` and `subsetAtˢ`, Pairing for the
reflexivity and transitivity witnesses, and internal Kuratowski injectivity
(`k2/REPORT-G.md:222-239`). Only the last now exists, as `entry-inj` at
`NameKernel.agda:321` and `kpair-unique` at `NameSpace.agda:388`.

So the sentence "`Uof G` is generic" cannot be written down in this programme
today. The missing thing is a type, not a proof of an existing type. Measured
here: `isGeneric` occurs 0 times in all 32 files, in any position including as a
hypothesis, and `K5/Generic.agda:424-431` says so in source. The reverse
correspondence `G-of U` is a separate, sized non-claim: directedness of a filter
demands a common refinement inside the filter
(`ForcingNotion.agda:175-180`) while the preimage of an ultrafilter yields only
separate compatibility of the two conditions, and closing that gap needs
separativity, which is additional data and never a field. Owner K6 or K11, under
an explicit separative hypothesis.

## 4. What was refuted rather than repaired

Project rule 14 is refute, do not repair. K5's measured negatives rank with its
theorems and are listed with the same weight.

### The architecture's `generic-reflect` route does not close

Track D found that compatibility does not compose. The correct route applies
`i-compat←` to the common refinement: `generic-reflect-from`
(`K5/Generic.agda:256-302`) takes a common refinement `r` of `s` and a member
`q` of `G` forcing `i p`, transports `i r ≤ᴮ i p`, and applies `i-compat← r p nz`
at `:275`. Track D reported the open goal rather than a repair. This is the one
measured negative of the package whose only written record is the coordinator's
`REPORT-D.md`, which states in its own first line that it is not Track D's
report; the source is the authority, it carries the corrected route, and it
carries no numbered correction. `grep -i "correction"` over `K5/Generic.agda` is
0, confirmed here. There is no "D-6".

### Architecture 1.9's quantifier claim, refuted at all four clauses

The struck sentence read "Satisfaction transfer needs `ext-onto` and only for
the two unbounded quantifier clauses, because those quantify over the carriers."
It is false. All four need it, the two bounded ones included, and
`ext-surjective` is named in the telescope of `K5/ExtensionSat.agda` at `:172`
and in each of the `∃̇`, `∀̇`, `∀̇∈` and `∃̇∈` clauses at `:237`, `:250`, `:263`
and `:292`, resolved here rather than copied (see section 8). The reason
is in the types and not in the proofs: bounding a quantifier restricts which
elements are admitted, it does not change the type they are drawn from, so the
P side still quantifies over `Nameᴾ` and the B side over `Nameᴮ`. The machine
evidence is `K5/fbreaks/BreakF3.agda-break`, which asks for the bounded
universal clause by reflexivity:

    K5/BreakF3.agda:271.34-38: error: [UnequalTerms]
    fst (IsNameᴮ n) != fst (IsNameᴾ n) of type Type ℓ

`EXIT=42` in `K5/fbreaks/f-BreakF3.log`, read here. `REPORT-F.md` quotes the
same diagnostic at `:267`; the file was edited after the report and the log says
`:271`. The refutation is marked in the architecture at
`k5-architecture.md:375`, struck rather than repaired, with the original
sentence preserved.

### Architecture 1.6's `generic-meets-denseBelow` route, and a fourth coded set

Track C found that meeting `coneOrApart r` at a filter containing `r` yields a
member of the filter refining `r`, that `d` is then dense below that member, and
that nothing puts the member of `d` it produces back inside the filter. The left
disjunct has to be `d` itself. The delivered `generic-meets-denseBelow`
(`K5/Dense.agda:497-518`) meets `memOrApart d r` at `:504`, and `memOrApart` is
the **fourth** coded set, declared at `K5/Dense.agda:401-402` and sealed in its
own `opaque` block at `:400`. `coneOrApart` is still built, because Track D's
`generic-reflect` consumes it. Track C's break C6 gives exit 42 with
`[UnequalTerms] coneOrApart r != memOrApart d r of type S`; that break is not on
disk and is attributable to `REPORT-C.md` section 3 only.

A second Track C negative that the architecture nowhere anticipates: **the four
coded sets must be sealed.** Four unsealed, no finish in 11 minutes at 2.2 GB.
One seal removed, no finish in 300 seconds. As delivered, four `opaque` blocks,
exit 0 at 1.65 s and 386 MB. The threshold is one declaration, `decideAt-dense`
(`K5/Dense.agda:250`), the first whose proof puts the separated set under a `⋁`
and converts against it; declarations that only transport along the Separation
specification are free unsealed. The four seals are on disk and verified here at
`K5/Dense.agda:207`, `:314`, `:400` and `:558`.

### The atomless-notion gap

Track J found that **no atomless forcing notion existed anywhere in K1 through
K4.** K2's `no-host-generic` was therefore an implication whose hypothesis had
never been witnessed: a theorem about atomless notions in a programme containing
none, and the existence of a host-generic filter had not been refuted anywhere.
Track J built the binary tree of finite two-valued strings under extension,
`treeNotion` at `K5/RefutedGenericity.agda:166`, proved `tree-atomless` at
`:177`, then `no-generic-on-the-tree` at `:193` and
`host-generic-existence-fails : LEM ℓ → HostGenericExists → ⟨ ⊥ ⟩` at `:233`.
The trivial one-point notion ships beside it as the positive control
(`trivial-host-generic` `:209`, `trivial-not-atomless` `:221`), and
`host-genericity-is-notion-dependent` `:243` is the two in one statement. This
is the clearest case in the programme of a measured negative that only a
refutation track would find, because every other track consumes the hypothesis
rather than asking whether anything satisfies it.

### The naive clauses: Track B's break and Track J's complement

Track B's break B4 weakened `at-∨←` from the dense-below form to the naive
disjunction clause and repaired `⊩-clauses` so that forcing still inhabits the
weakened record. **`⊩-clauses` then typechecks and `⊩-unique` does not:**

    K5/Break4.agda:858.14-863.34: error: [UnequalTerms]
    (x : Cond) →
    ⟨ (fst x ≼ᶜ fst p) ⇒
      ⋁ Cond (λ r → (fst r ≼ᶜ fst x) ⊓ (r ⊩ φ [ ν ]) ⊔ (r ⊩ ψ [ ν ])) ⟩
    !=< ∥ ⟨ p ⊩ φ [ ν ] ⟩ ⊎ ⟨ p ⊩ ψ [ ν ] ⟩ ∥₁

The dense-below form of `at-∨←` is load bearing for uniqueness. The break file
is not on disk and the diagnostic is attributable to `REPORT-B.md` section 8
only.

Track J's complement is on disk and is a different fact. At an antichain **both
naive clauses are theorems**: `antichain-naive-disjunction : LEM ℓ →
NaiveDisjunctionA2` at `K5/AntichainControl.agda:115`,
`antichain-naive-existential` at `:140`, `antichain-refutes-nothing` at `:165`.
That is why the naive forcing relation looks correct until it is asked to be
unique. Track B showed the naive clause is underdetermined; Track J showed why
it nevertheless looks right; neither result is the other.

**And separativity does not repair them, proved rather than argued.** Track J's
three-element "V" is separative and antisymmetric (`V3-separative` at
`K5/RefutedClauses.agda:364`, `V3-antisymmetric` at `:373`), the naive clauses
fail there anyway (`naive-disjunction-fails` `:248`, `naive-existential-fails`
`:308`), and the correctly qualified clauses hold at the very same condition
(`disjunction-dense-below` `:326`, `existential-dense-below` `:335`).
`no-repair-by-separativity` at `K5/Refuted.agda:138` is the packaged statement,
and it is what stops a later track reaching for separativity as a fix.

### Neither direction of `≈-agree` is free

The natural expectation is that the forward implication, poset side to Boolean
side, needs only the free half of the bridge. Track E measured that it does not.
Both of its clauses begin by taking an arbitrary active entry of a **translated**
name, and recognizing that entry as the translation of a source entry is
`active←`, the paid half. So `generic-reflect` is consumed by **both** halves of
`≈-agree`, and the architecture's ledger row is right for a reason that is not
the obvious one.

Counted here on the comment-stripped source: five lines name `bridge←`
(`K5/Agreement.agda:280`, `:404`, `:671`, `:688`, `:691`) of which exactly one
is a proof-body use, at `:404` inside `active←` (`:358`); five name `bridge→`
(`:279`, `:321`, `:671`, `:687`, `:691`) of which exactly one is a proof-body
use, at `:321` inside `active→` (`:315`). The machine evidence is
`K5/breaksE/BreakPath.agda-break`, which weakens `active←`'s conclusion from
"some active entry of `n` whose translation is this code" to "some active entry
of `n`" and fails at the first clause of `≈-agree` with
`[UnequalTerms] ∥ Pv.Active x m ∥₁ !=< Σ ⟨ Pv.‖Active‖ x m ⟩ (λ _ → y ≡ trᴮ x)`.
The path component is load bearing, and the log is on disk.

### Excluded middle and nontriviality: the poset side needs neither, the Boolean side needs both

Two tracks, opposite sides, one reason, and they belong together. Track F
measured a negative against a natural expectation: `LEM` and `nontrivial` are
each 0 over `K5/Structures.agda` and `K5/ExtensionSat.agda` with comments
stripped, confirmed here, and `groundSat` and `ext-⊨` are **paths** of truth
values, strictly stronger than a biconditional and strictly cheaper than K4's
`Reflects`. Track G measured the other side and they cannot be dropped there:
break BG3 drops `Uof-proper`, hence `ForcingBase.i-nonzero`, from
`Uof-not-both` and gets exit 42 with
`[UnequalTerms] fst (Uof ⊥ᴮ) !=< Lift Empty.⊥`. `not-both` is false at a
degenerate algebra and that is where the exclusion happens.

The one reason is Track F's and it explains both. On the Boolean side the two
sides of the equation live in different algebras, a `Pt B` value against an `Ω`
proposition, so the induction must carry `Reflects`, and a join in an abstract
Boolean algebra is the top only if some member is, which is exactly join
primeness. On the poset side both sides are truth values of `hPropAlgebra ℓ`, so
every connective clause is a congruence and every bounded-quantifier clause is a
bijection of witnesses. **K4's `LEM ℓ` and nontriviality are artefacts of the
Boolean-valued side, not of Bell 1.23(v).**

### Further measured negatives

**Order reflection is false**, refuted upstream at
`InstancesCompletion.agda:131-134` and refuted again on Track J's own notion:
`order-reflection-fails : OrderReflection → ⟨ ⊥ ⟩` at `K5/RefutedOrder.agda:109`,
with `mono-converse-fails` at `:132` and `i-not-onto` at `:167`.
`reflection-under-separativity` at `:142` and `reflection-boundary` at `:146`
draw the boundary. Measured: `i-inj` is 0 in all 32 files.

**`SameName` is refuted as codes and now proved as values.**
`generic-name-identification-fails : Witnessed.SameName → ⟨ ⊥ ⟩` at
`K5/RefutedOrder.agda:220`, with the scope statement beside it: the two names
may still have the same value at a filter, since an entry of weight `⊥ᴮ` is
never active. Track E closed the value side as
`generic-name-value-at-positive` and states in source that this does **not** say
`trᴮ Γᴾ` and `U̇` have the same value. `U̇` appears in no K5 file, measured 0 in
all 32, and Track J's code refutation stands untouched.

**`i-compat→` needs neither `i-compat→-at` nor any meet lemma.** Track I
measured the whole route unnecessary: three lattice laws and one emptiness fact
suffice. `i-compat→-at`, `meet-join` and `meet-split` are each named 0 times in
both Track I deliverables with comments stripped, confirmed here (the three raw
hits in `K5/InstanceBase.agda` at `:192`, `:209` and `:210` are the comment
lines recording why the route is not taken), so REPORT-A's correction A-6, which
owed Track I two
transfer lemmas, is half wrong in Track I's favour: only `compat-transfer←` is
spent and `compat-transfer→` is not named at all.

**Probe 0's unmeasured shape elaborates, and the sealing rule is looser than K4
stated it.** `sealed-op (unsealed-description) (unsealed-description)` is 1.54 s
(`ProbeI3`); the same with the **outer** operation unsealed does not finish in
471 s at 1.00 GB (`ProbeI4`); and with one unsealed nested argument under an
unsealed outer operation it still does not finish in 200 s (`ProbeI6`). The
negative half of the rule is confirmed and the positive half is stronger than it
needs to be: sealing the outer operation sufficed, and K2's own unsealed inner
descriptions did not have to be touched. Track I's threshold is two coded
operations nested in a **type**; Track C's, above, is a description-operator term
under a join in a **proof**. Different triggers, same remedy, and they must not
be merged.

**K4's five seals are never opened.** Measured here: every `unfolding` directive
in all 32 files opens `iᴷ`, K5's own sixth seal, at `K5/InstanceBase.agda:138`
and in four Track I probes, and none names `meetᴷ`, `negᴷ`, `joinᴷ`, `supᴷ` or
`infᴷ`. The reason is Track I's, that everything it needed from the coded meet
turned out to be a lattice law: `⟨ u ≤ᴮ v ⟩` is `⟨ fst u ⊆ˢ fst v ⟩`
(`K4/Algebra.agda:76-77`), so `⊓-lb₁` and `⊓-lb₂` give the membership split in
one line. The consequence is recorded as an open question and not as a result:
whether an `opaque` seal survives a module application was never tested and is
not known.

## 5. The classical strength, with its two kinds of zero

### The census

Over the 32 archived files with comments stripped, the token `LEM` occurs **80
times in 16 files**, counted here for this record. The two-token string `LEM ℓ`
occurs 64 times in 15 files: `Truth.agda` 12, `Clauses.agda` 11, `Dense.agda` 6,
`Generic.agda` 5, `AgreementAtUof.agda` 5, `ProbeD.agda` 5, `InstanceBase.agda`
4, `TruthAtFrame.agda` 3, `AntichainControl.agda` 3, `RefutedGenericity.agda` 3,
`Refuted.agda` 3, `RefutedOrder.agda` 1, `ProbeI2.agda` 1, `ProbeI3.agda` 1,
`ProbeI4.agda` 1. The sixteenth file is `ProbeI6.agda`, whose single `LEM` is an
import line. `Frame.agda`, `Agreement.agda`, `Structures.agda`,
`ExtensionSat.agda`, `InstanceValue.agda`, `RefutedClauses.agda` and all four
Track H files carry none.

**`LEM (ℓ-suc ℓ)` occurs zero times in the code of all 32 files**, in every
position including hypotheses. It occurs once in the whole corpus, in a comment
at `K5/InstanceBase.agda:305`, which is the line recording what the level
becomes at `𝒮ʟ`. Likewise `import L.` and `import V.` are 0 everywhere, so no
K5 file makes the `𝒮 := 𝒮ʟ` instantiation at which the level identification
becomes concrete. That instantiation is K8's and later.

### The two levels, covered and not equated

K5's classical cost is `LEM ℓ` at an arbitrary
`𝒮 : ZFStructure (hPropAlgebra ℓ)`. The project rule is one `LEM (ℓ-suc ℓ)` and
nothing else. These are different statements and this record does not write them
as one. They do not need to be: the tree proves the implication, as
`lowerLEM : ∀ {ℓ} → LEM (ℓ-suc ℓ) → LEM ℓ` at
`src/Base/Classical.lagda.md:82`, which lifts the proposition one universe,
decides it there and lowers the verdict. So the correct ledger row is that **K5
names `LEM ℓ`, which the programme's single `LEM (ℓ-suc ℓ)` covers through
`lowerLEM`, and K5's net addition to the assumption ledger is zero.** Two
errors are avoided by writing it that way: silently equating the two levels, and
treating `LEM ℓ` as a separate assumption when it is discharged by a hypothesis
already on the books.

`lowerLEM` itself occurs 0 times in all 32 files. Every K5 declaration that
spends excluded middle takes `LEM ℓ` as an explicit first argument, so the
lowering happens outside K5, at whichever caller supplies that argument. That is
the right place for it and it is why K5's signatures are readable without the
level bookkeeping.

### Independence zeroes

For each of these the zero is a genuine independence claim, because nothing in
the programme's hypothesis yields them: `LEM (ℓ-suc ℓ)` does not give any form
of choice. Measured over all 32 files with comments stripped, every one is 0:
the axiom of choice in any spelling, `Base.Choice`, `ChoiceSet`, countable
choice, dependent choice, Zorn, the Boolean prime ideal theorem, the ultrafilter
lemma, and `SetQuotients`. **Host choice in every form is 0 across all files and
that is a genuine independence claim.**

The structural counterpart, which three tracks state independently for their own
files and which grep confirms for the corpus: no file eliminates a truncated
sigma into data. Every `PT.rec` and `PT.map` targets an `Ω` carrier produced by
`snd`, or a truncation. Track G's one application of `attained-elim` targets
`⋁ Nameᴮ (λ σ → Uof (f σ))`, an `Ω`; the variant returning an index would be
host choice and `K4/ValueSets.agda:310-313` records that it deliberately does
not exist. Track F's one use of `ext-surjective` as data is a Σ that Track H
exhibits rather than truncates, so no clause eliminates a truncation there
either.

### Usage zeroes, which look the same and are not

`resizing`, `PropRes`, `REWRITE`, `Impredicativity` and `hPropSmallness` are
also each 0 in all 32 files. **That zero is a usage measurement only and must
not be read as an independence claim.** Both consequences follow from the
programme's own hypothesis: `lem→resizing : ∀ {ℓ} → LEM (ℓ-suc ℓ) → Resizing ℓ`
at `src/Base/Classical.lagda.md:281`, and
`lem→impredicativity : ∀ {ℓ} → LEM (ℓ-suc ℓ) → Impredicativity ℓ` at `:310`,
whose two fields are `lem→resizing lem` and `lem→hPropSmallness (lowerLEM lem)`
with `lem→hPropSmallness` at `:218`. So the development is not resizing-free and
K5 is not resizing-free. What the measurement says, and all it says, is that no
K5 file names either, so no K5 proof reaches for resizing as a separate
hypothesis and no K5 signature carries one. That is a fact about the shape of
K5's proofs and not a fact about the strength of the theory they live in.

### The filter hypothesis: three tracks, two answers, both correct

This must not be flattened into one row. Tracks E and F agree, independently,
that **positivity alone** suffices for their theorems: Track E's two standard
name corollaries take `⟨ VP.positive G ⟩`, and `grep -c "upward\|directed"` over
`K5/Agreement.agda` is 0, confirmed here; Track F's `groundCopy` and `groundSat`
live inside `module WithPos (G-pos : ⟨ positive G ⟩)` and `isFilter` occurs
nowhere inside it, with `groundCopy-at-filter` at `K5/Structures.agda:762` as
the one-line filter spelling. Track G's answer is the other way and is also
correct: the truth lemma's `∧`, `⇒`, `∃` and `∀` cases consume
`isFilter.directed` and nothing else. The mathematical reason is worth the line:
conjunction at a filter is meet closure, positivity does not give meet closure,
and a `∧` clause stated at `⟨ positive G ⟩` would be false.

The full projection census, measured here over all 32 files: `isFilter.` is
projected at exactly four sites, three of them in a deliverable.
`K5/Generic.agda:211` (`directed`, inside `Uof-dir`), `:271` (`directed`, inside
`generic-reflect-from`), `:296` (`upward`, inside `generic-reflect-from`), and
`K5/ProbeD.agda:155` (`directed`, the probe's copy of `Uof-dir`).
**`isFilter.upward` is projected exactly once in all of K5, and that once is
inside `generic-reflect`**, which is the one Track D lemma Track G does not use.
`isFilter.inhabited` is projected nowhere.

## 6. The unresolved measurement, stated as open

Three tracks measured the cost of applying a landed K5 module. **They do not
agree, the coordinator turned one of them into a rule, two tracks falsified the
rule with their own numbers, and the discriminator is not known.** The numbers
below were read from the logs in the compile root for this record; those logs
are not in the archive.

| | file | lines | applications, as the track counted | result |
|---|---|---|---|---|
| Track E, probe 3 | `K5/AgreementAtDense.agda-slow` | 81 | 10 | **no finish**, killed at about 20 minutes, 2.08 GB |
| Track F | `K5/ExtensionSat.agda` | 332 | 5 | exit 0, 2.51 s, 531,103,744 B (506 MiB) |
| Track F | `K5/Structures.agda` | 825 | 11 | exit 0, 2.64 s, 580,583,424 B (554 MiB) |
| Track G, seam probe | `K5/TruthAtFrame.agda` | 230 | 14 | exit 0, 3.73 s, 1,132,511,232 B |

Track E's own control, the same telescope with the eight dense slots filled by
variables, is `K5/AgreementAtUof.agda` at exit 0, 4.25 s and 1,114,243,072 B.
The failing file's log carries two `Checking` lines and no timing block, which
is the kill.

**What the measurements exclude.** Counted here from the two files rather than
taken from a report, Track G's seam probe consumes **sixteen** distinct
`K5.Dense` exports (`decideAt`, `decideAt-sub`, `decideAt-spec`,
`decideAt-dense`, `coneOrApart`, `coneOrApart-sub`, `coneOrApart-spec`,
`coneOrApart-dense`, `witnessAt`, `witnessAt-sub`, `witnessAt-force`,
`witnessAt-denseBelow`, `generic-meets-denseBelow`, `MeetsAll`, `CodeOfBelow`,
`BelowOfCode`), and the failing file consumes **eight**, the first eight of that
list, fed into the same `Meeting` destination. **The failing file's consumption
set is a strict subset of the finishing one.** So the non-finish is measurably
not explained by applying `K5.Dense`, nor by filling `Meeting`'s eight slots
from an applied `K5.Dense`, nor by consuming Track C's sealed coded sets through
projections of an applied module, nor by line count, nor by the number of dense
exports consumed.

**Nor by the application count, because the counts were never on one scale.**
Counting `module X = M args` lines directly in each file, measured here:
`AgreementAtDense.agda-slow` has 2, `AgreementAtUof.agda` has 5,
`TruthAtFrame.agda` has 12, `Structures.agda` has 7 and `ExtensionSat.agda` has
3. Track E's "10" for probe 3 is its own 2 plus probe 2's 8, counted
transitively through one level; Track G's "14" counts within-file applications
only. **Under the direct count convention the rule inverts: the file with the
fewest applications, 2, is the one that hangs, and the one with 12 finishes in
3.73 s.** Under Track E's transitive convention it does not invert, but it does
not predict either. (`LEDGER-K.md` gives `Structures.agda` 6 where this record
measures 7; the seventh line is `module Gr = At S id` at
`K5/Structures.agda:175`, an application of `FOL.Semantics.At`, and the
difference is a convention about what counts as an application, not a
disagreement about the file.)

**What was narrowed, and what remains open.** Track K narrowed the failing
file's unique feature to the co-occurrence, in one file, of projections of an
applied `K5.Dense` together with K3's valuation recursion telescope, measured by
the `child-wf : WellFounded Child` entry: present in the failing file and in
Track F's two, absent from Track G's, which carries no name kernel at all. A
second candidate is the depth and shape of the path the projections travel:
Track E's probe feeds them into a three-level nested module whose enclosing
layers have already been applied with 2 and 25 arguments, one of which is a
`trᴮ-entries` telescope entry with three nested `⋁` and a record field
projection applied to a constructed pair inside
(`K5/AgreementAtUof.agda:71-75`, repeated at
`K5/AgreementAtDense.agda-slow:56-62`); Track G feeds its sixteen into a
two-level path whose enclosing layers take 2 and 7 arguments, every one a file
parameter. **Those two candidates are not separated by any file in the package.**
No probe has both features at shallow nesting, and none has the deep nesting
without both. **This record names no mechanism and no track should be read as
having named one.** Track G explicitly declined to name one on the ground that
it did not run Track E's probe. The probe that would separate them is not
written and is cheap: `K5/AgreementAtUof.agda` with the eight slots filled from
an applied `K5.Dense` but with the two enclosing layers flattened into a single
module application.

**Rule 10's status, recorded honestly.** The rule as previously stated is to
budget heap by module applications rather than by line count. It has a four-point
within-track supporting series from Track E (3 applications to 682,475,520 B, 7
to 783,646,720 B, 8 to 1,114,243,072 B, 10 to no finish at 2.08 GB) at 153, 699,
173 and 81 lines, which does show that line count predicts nothing. It has two
counterexamples, Track F's `Structures.agda` and Track G's `TruthAtFrame.agda`,
both well inside budget. Track C reports nine applications at 386 MB and Track I
two at 541 MB and 727 MB against K4's two-application reference of 3.30 GB.
**Status: rule 10 is a better proxy than line count and it is not a predictor.**
Three tracks, C, E and I, converge independently on the thing that does
correlate, whether the applied module's arguments are variables, which cannot
unfold, or projections of an applied module, which can; that is a mechanism for
the direction of the effect, it is not a quantitative predictor, and it did not
predict Track G's probe, whose sixteen consumed exports are all projections of
an applied module and which finishes in 3.73 s. The application counts should
not be used as a budget by anyone, which is Track I's own conclusion reached
independently by Track C.

## 7. New obligations K5 discovered

Each is an obligation rather than a result, each has an owner, and each is
sized.

**The universal quantifier node needs an `Admits` at the complemented family.**
Track G's G-2. Architecture 1.9 writes "one per `∃` node of `φ`"; the universal
nodes need one too, at the family `σ ↦ ¬ᴮ (val φ (σ ∷ ν))`. The reason is not
presentational: the forward direction of the universal case runs
`⋀ b σ ∉ U`, hence `¬ ⋀ b σ ∈ U`, hence `⋁ ¬ b σ ∈ U`, hence some `¬ b σ ∈ U`,
and the last step is join primeness at the complemented family, which a generic
ultrafilter has only at a family whose join is coded. Bell's own proof of the
universal case is de Morgan followed by the existential case, so no textbook
route avoids it. It is **not derivable** from the plain family's `Admits` inside
`Core`, because the complemented value set is the image of the plain one under
`¬ᴮ`, which needs Collection or an internal image former, and `Core` has
neither. Proved mechanically by break BG2:

    K5/gbreaks/BreakG2.agda-break:657.66-68: error: [UnequalTerms]
    (f σ) != (¬ᴮ f σ) of type (Σ S (λ x → ⟨ x ∈ˢ B ⟩))
    when checking that the expression Ad has type Admits (λ σ → ¬ᴮ f σ)

Size: one Separation over `B` against a Δ₀ formula, the same shape as Track C's
four sets, plus the `attained` reading, because `neg-mem` reads membership in
the complement as the poset clause "no refinement of `z` lies in `u`"
(`CodedCompletion.agda:300-301`, `:701-708`). Owner: Track I or K8.

**The two atomic bridges have no supplier anywhere.**
`atom-∈ : (σ τ : Nameᴮ) → (σ ∈ᵁ τ) ≡ Uof (memᴬ (fst σ) (fst τ))` and `atom-≐`
likewise, at `K5/TruthAtFrame.agda:206-207`. They are the base case of the truth
lemma's induction and are not provable inside its telescope: K3's value relation
is built by a pair recursion and K4's atomic values by a host recursion over the
support, and relating the two is an induction on names, which is join primeness
at the coded family of entry weights. The missing input is an `Admits` for that
family, which is obstruction O1. `K5/TruthAtFrame.agda` leaves exactly these two
gaps and nothing else; every other Track G parameter is filled from a landed
track at exit 0. Break BG4 confirms the two are not interchangeable, exit 42.
Owner: whoever discharges O1. This is O1 wearing a new face, and the face is
new.

**`Γᴾ` and `Γᴾ-spec` belong one module deeper in `Valuation.agda`.** Track F's
F-5. They are parameters of K3's `module Standard` (`Valuation.agda:501-503`)
while `check-≈-inj`, `check-faithful` and `check-value` live inside it, and
neither is used by any Track F proof. This is exactly the move K3 made for
`entry-inj`, `≈ˢ-paths` and `ext-path`, on the ground that the parameter list is
the ledger. Reported, not made; Track F touched no K3 file. Owner: a K3 follow-up.

**The reverse half of the denotational round trip, `trᴾ (trᴮ m) ≈[G] m`.** Not
proved and not claimed. Its backward half is free and its forward half is
exactly `generic-reflect`, so it prices at `LEM ℓ` plus `meets` plus
`isFilter G`. It needs a second `Valuation.Poset` at the conditions, which
already exists as `VP` at `K5/Agreement.agda:197`. Sized and priced in
`REPORT-H.md` section 7 and stated in source at `K5/RoundTrip.agda:84-104`. K5's
contract does not consume it. Owner: Track E or a K6 follow-up.

**Whether an `opaque` seal survives a module application is untested and
unknown**, recorded as an open question rather than an obligation with a
deliverable, and **the isolating probe of section 6 is unwritten**. A standing
engineering constraint rather than an obligation: keep Track C's dense sets as
parameters at every consumer and instantiate only at the final instance file.
Track E recommended it and Track G's deliverable already obeys it, measured 0
before the coordinator's message arrived. Given section 6 this should be read as
prudence under an unknown mechanism and not as a rule with a measured basis.

## 8. Coordinator failures

Track K counted eight and this record adds a ninth. All of them are the
coordinator's, and this record says so plainly rather than distributing them
across the tracks that absorbed them.

**Briefs cited reports that were not on disk, three times.** Tracks F, H and I
each hit it and each correctly read the shipped source instead, which is rule 7
working. Track F's brief named a K4 `REPORT-H.md` (K4 shipped A, B, C, D, E, F,
I, J and no G or H) and a K5 Track J report that did not exist; Track H's brief
named a K3 `REPORT-F.md` and `REPORT-G.md` (K3 shipped A, B, C, D, E, H, I and
no F or G); Track I ran while `REPORT-D.md` did not exist in the root. Tracks D
and J never had their reports transcribed at all, and the `REPORT-D.md` and
`REPORT-J.md` now in the root are the coordinator's records and say so in their
first line. For both, the authority is the source.

**Three architecture citations to `REPORT-G.md` were mis-scoped to K3 when they
resolve in K2.** All three ranges read correctly in
`~/Agentic/bedrock-proofs-archive/k2/REPORT-G.md`: `:203-212` is the warning
that the backward direction is not order reflection, `:222-239` is the finding
on the undelivered coded order graph, `:230-239` sizes it. Track H was right to
refuse the citation and read the two K3 sources directly.

**REPORT-A's `ForcingBase` field count was thirteen and the record has
fourteen.** Corrected inline, recounted by Track I, by Track G, by Track K and
again here from `K5/Frame.agda:148`. Five recounts, every one fourteen, against
the report's thirteen.

**A single measurement was turned into a rule without a control.** Track E's
non-finish was relayed to the other tracks as a prohibition on applying
`K5.Dense`. Track F measured against it and Track G measured against it, and
both falsified it; the prohibition was then withdrawn and Track G was asked to
measure instead, which it did. The cost was small because both tracks measured
rather than complied. The control was already in Track E's own report, as
`K5/AgreementAtUof.agda`, the same telescope with variables, exit 0.

**A stale un-prefixed citation survived in the source after the architecture was
swept.** `K5/Generic.agda:431` read "The interface is sized in
`REPORT-G.md:222-239`", which no reader in the compile root could resolve. This
has since been fixed: the archived bytes now read `k2/REPORT-G.md:222-239`,
verified here.

**REPORT-E's `file:line` citations into `K5/Agreement.agda` are stale by about
twelve lines**, because the coordinator asked Track E to write Track H's
correction into the source as a comment on `module Agree` after the report was
written. Measured offsets, re-resolved here: `active→` reported `:303`, actual
`:315`; `active←` reported `:346`, actual `:358`; `≈-agree` reported `:426`,
actual `:438`; `∈-agree` reported `:530`, actual `:542`; `module StandardNames`
reported `:571`, actual `:584`; the two proof-body bridge uses reported `:309`
and `:392`, actual `:321` and `:404`. **Every count in REPORT-E verifies
exactly**; only the addresses moved. A report whose source is edited after it is
written needs its line cites re-resolved, and the coordinator requested the edit.

**REPORT-F's timing table disagrees with its own log.** The table gives
`K5/ExtensionSat.agda` at 2.12 s and 598,441,984 B; `K5/f-ExtensionSat.log`, read
here, says 2.51 s and 531,103,744 B with `EXIT=0`. Both are Track F's own runs
under the one option set. The log is the artefact and the table is the report.
Recorded, not adjudicated.

**REPORT-G's `LEM` census is short by one.** Eleven sites reported over
`K5/Truth.agda`, twelve measured, here and by Track K. The twelfth is the
`witnessAt-denseBelow` parameter opening at `K5/Truth.agda:411`, whose type
names `LEM ℓ` on the next line, which the report's prose names as a forwarding
destination and whose table row is missing. Nothing
mathematical turns on it: it is a parameter transcribed from Track C, not a new
decision, and the census is the kind of number a later track will reuse.

**A ninth, found by this record and not by Track K, of the same class as the
sixth.** `REPORT-F.md` section 7 locates `ext-surjective` in the four
quantifier clauses of `K5/ExtensionSat.agda` at `:232`, `:245`, `:258` and
`:290`, and `k5-architecture.md:375` copies those four numbers into the struck
sentence. In the delivered bytes the four naming sites are at `:237`, `:250`,
`:263` and `:292`, with the telescope entry at `:172`; two of the report's four
lines are blank. The cause is the one Track K already recorded for Track F,
that Track F narrowed its telescope and re-typechecked after its first report,
but Track K re-resolved Track E's stale cites and not Track F's. The
refutation itself is unaffected: `ext-surjective` is named in all four clauses
and the break gives exit 42.

Two further gaps in the artefact record, which are the coordinator's in the same
way. **Fifteen of the eighteen break logs on disk record no exit code.** Only
Track F's three carry `EXIT=42`; each of the other fifteen carries exactly one
Agda `error: [...]` line, which is what an exit 42 produces, so the result is
evidenced, but an automated sweep looking for `EXIT=` would read them as unrun.
A one-line change to the break runner would have prevented it. And **twelve of
K5's thirty break results exist only as quotations in a report**: Track A's two,
Track B's four and Track C's six were deleted after their runs and are
attributable to `REPORT-A.md` section 3, `REPORT-B.md` section 8 and
`REPORT-C.md` section 3 only. The reports say so and the deletions were
deliberate. It remains the case that for those twelve, "trust grep, not prose"
cannot be applied, because there is nothing to grep.

## 9. Terminology

The terminology track is blocked on an owner ruling and blocks no code; K5
proceeded with English-only source prose throughout, which is what the current
phase permits. The collision is the one K2 and K4 already carry:
`dev/glossary.toml` holds `coherence` with the Chinese rendering 相容 owner-ruled
on 2026-08-03, and the same word is the standard Chinese rendering of the
forcing compatibility of two conditions. The evidence for a ruling is assembled
in `terminology-compatible-2026-09.md`, which proposes three options and chooses
none, because the project rule is that parallel authors may not resolve a
terminology collision. No Chinese or Japanese rendering of either sense has been
written by any agent, and that is the state the rule exists to protect.

## 10. Validation

**All 24 K5 deliverables typecheck at exit 0 in the root's final bytes**, as
relayed and verified by the coordinator after every track finished and after the
citation edit of section 8. `Truth.agda`, `ExtensionSat.agda`,
`InstanceValue.agda` and `Dense.agda` were rebuilt cold after deleting every K5
interface, at 13 s, 4 s, 2 s and 2 s; the remaining twenty were checked warm.
`Truth.agda`'s 13 s independently reproduces Track G's 13.36 s, which this
record read from `K5/g5.log`. No Agda process was started for this record and no
file was compiled for it.

What this record verified for itself: the 32 archived K5 files are
byte-identical to the compile root's final bytes, `cmp` over all 32, zero
differences. Every one carries `--cubical --safe --guardedness` on line 1, and
so do the three parked Track F breaks. No `postulate`, no pragma, no hole
marker, no `trustMe`, no `{!` and no bare `?` in any of them. **The 47 upstream
modules, 29 top-level and 18 under `K4/`, are byte-identical to the K2, K3 and
K4 roots, zero drift, verified twice independently:** Track I ran the `cmp`
audit and additionally cross-checked the modules present in more than one
upstream root against every root that has them, and this record re-ran the
comparison from the K5 root against `/tmp/bedrock-k4-probes`,
`/tmp/bedrock-k3-probes` and `/tmp/bedrock-k2-probes` and found 47 files
compared, zero differing and none without an upstream.

Timings and peaks, as each track measured them under the one option set
`GHCRTS="-A64m -I0 -M8g" agda <file>` from `/tmp/bedrock-k5-probes` with
`-WnoUnsupportedIndexedMatch`: `Frame.agda` 0.81 s and 286 MB;
`Clauses.agda` 6.00 s and 1.30 GB; `Dense.agda` 1.65 s and 386 MB;
`Generic.agda` at exit 0; `Agreement.agda` 3.11 s and 784 MB;
`AgreementAtUof.agda` 4.25 s and 1,114,243,072 B; `Structures.agda` 2.64 s and
580,583,424 B; `ExtensionSat.agda` 2.51 s and 531,103,744 B; `Truth.agda`
13.36 s and 1,341,980,672 B; `TruthAtFrame.agda` 3.73 s and 1,132,511,232 B;
`RoundTrip.agda` 1.06 s and 305 MB, its three seam files 0.85 s, 1.06 s and
3.53 s; `InstanceBase.agda` 1.78 s and 541 MB; `InstanceValue.agda` 2.47 s and
727 MB. The 8 GB heap was never approached; every failure in this package was a
time wall at a flat resident set, which is the same signature K2 and K4
isolated.

One measurement convention diverged between tracks and no document records it,
so it is recorded here. Each run log carries both a
`maximum resident set size` line and a `peak memory footprint` line, and they
differ by roughly a tenth. Tracks E, F and K quote the first; REPORT-G quotes
the second, which is why its 1.28 GB for `K5/Truth.agda` and 1.08 GB for
`K5/TruthAtFrame.agda` are smaller than the 1,341,980,672 B and 1,132,511,232 B
in the same two logs. No conclusion in this record turns on the difference, and
a later package comparing peaks across tracks should say which line it is
quoting.

The sources are archived at `~/Agentic/bedrock-proofs-archive/k5/` with the
architecture, the ten reports, `LEDGER-K.md` and the eighteen deliberate breaks,
alongside K0 recovered byte-exact from the record documents, K1, K2, K3 and K4.
The run logs quoted in sections 4 and 6 that are not break logs live only in the
temporary compile root under `/tmp`, which does not survive a reboot on this
machine; two worktrees were lost that way earlier in the programme.
