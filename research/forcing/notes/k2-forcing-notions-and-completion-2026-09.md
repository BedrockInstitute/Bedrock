# K2 forcing notions, the two regular-open completions, and the certificate calculus

Date: 2026-09-12. Source baseline: `cbd1510e`. Status: K2 COMPLETE on its roadmap
scope with two named exceptions, the coded order graph of `B⁺` and the coded half
of acceptance instance 1, both in section 6. Nine tracks, A through I, of which
eight wrote Agda and the ninth is terminology and is blocked on an owner ruling;
ten files, 6317 lines, every one at exit 0 under `--cubical --safe
--guardedness`. Eight track reports are archived, `REPORT-A` through `REPORT-G`
and `REPORT-I`. There is no `REPORT-H`, because Track H is the terminology track
and wrote no code, and the architecture declares no Track J
(`bedrock-k2-architecture.md:578-686` lists exactly nine tracks). This record
follows the K0, K1, K3 and K4 convention: proof work lives in a task-specific
temporary compile root, with the sources archived outside it, and no repository
source file is changed.

## 1. What K2 delivers

The roadmap's K2 is "structural forcing and automatic completion", whose concrete
output is "preorders, lawful Booleans, model-internal completion and B⁺
certificates" (`cohen-implementation-roadmap-2026-09.md:49`), expanded in section
4 at `:158-167`: separate the structural preorder and Boolean mathematics from
forcing semantics, preserve nonseparative presentations, define completeness
relative to the model's coded subsets, and supply the completion adapter,
`B⁺`, Bell Lemma 2.3's comparison, and explicit noninjectivity of `i`.

Ten files:

| File | Track | What | Lines | SHA-256 prefix |
|---|---|---|---|---|
| `ForcingNotion.agda` | A | the host structural poset layer, zero hypotheses | 347 | `3bf56c22f64ad77b` |
| `Algebra.agda` | B | the law-bearing Boolean interface over an arbitrary `TruthAlgebra` | 482 | `8967b685db0891ee` |
| `HostRegularOpen.agda` | C | the host regular-open algebra and the completion map | 912 | `d1d7d812f11e1bca` |
| `GroundDescription.agda` | D | truncated existence to a term, by description | 236 | `8d308389c662c453` |
| `CodedVocabulary.agda` | E | the object-language vocabulary of a coded notion | 551 | `57877f3682d5034b` |
| `CodedCompletion.agda` | F | the model-internal regular-open completion | 1374 | `ef1e119e3d04405e` |
| `Certificate.agda` | G | certificates, the nonzero part, comparison, dense maps | 1545 | `635dc0270d786010` |
| `Instances.agda` | I | three acceptance presentations and what each witnesses | 576 | `f620a25b8f8cfc57` |
| `InstancesCompletion.agda` | I | the same three against Track C's actual algebra | 212 | `0979e8396b4a1870` |
| `K2Bridge.agda` | closure | the two halves of K2 compose, by `refl` | 82 | `7fdf0b536e30dffe` |

`K2Bridge.agda` has no track letter and no report: it is the coordinator's
closure file, and section 5 says what it proves.

An eleventh K2 file sits beside these and is deliberately not counted in the
6317: `CertificateUse.agda`, 208 lines, `f6ed5a82e450d8c0`. It is Track G's
interface evidence, which is a different claim from Track G's proofs going
through. It imports `Certificate` from outside as a module application, ascribes
the declared type to every delivered name, and builds four composite objects out
of the calculus, including the nonzero part of the unit, which is what shows the
adapter iterates rather than firing once (`REPORT-G.md:20-25`).

Three further files in the archive directory are K1's, present only because K2's
compile root mounted them for import: `OrdinaryProfile.agda` (398 lines),
`CardinalBridge.agda` (619) and `CHSentence.agda` (200). They are byte-identical
to the K1 archive copies, checked by `diff`, and the shared preamble forbade
editing them (`bedrock-k2-shared.md:9-12`). Attributing any of the three to K2
would misreport both packages.

The archived sources are byte-identical to the live compile root
`/tmp/bedrock-k2-probes`: `diff` over all eleven K2 files reports no difference.
The hashes above are what let K0 be restored byte-exact after `/tmp` was cleared,
and `/tmp` does not survive a reboot on this machine.

Three figures in the reports disagree with the sources, and the sources win.
`REPORT-E.md:11` gives `CodedVocabulary.agda` as 557 lines; `wc -l` gives 551.
`REPORT-G.md:18` gives `CertificateUse.agda` as 219 lines; `wc -l` gives 208.
`REPORT-I.md:15-16` says `LEM ℓ` is the first explicit argument of exactly three
theorems in `InstancesCompletion.agda`; `grep -n "LEM ℓ"` returns five
declarations, at `:68`, `:105`, `:140`, `:192` and `:207`, which is the list that
report's own section 3 gives at `:230-232`. The discrepancy is in the abstract,
not in the mathematics.

The architecture that produced all of this is
`bedrock-k2-architecture.md`, 80827 bytes, archived with the shared preamble
`bedrock-k2-shared.md`. It was never compiled. That was the same deliberate trade
K3 and K4 later made, and sections 3 and 4 are what it cost.

## 2. The constraints K2 exists to respect, and how each is enforced

### The module parameter list is the ledger, and the check reads the list

The architecture's exit item C4 states this as a rule rather than a habit: "the
module parameter list is the ledger and the check reads the list, not the prose"
(`bedrock-k2-architecture.md:723`). `CodedCompletion.agda:256-263` is that list in
full, and it is six entries: `ext`, `pow`, `sep`, `paths`, the `Presentation` and
its `ForcingLaws`. No Pairing, no Union, no Infinity, no Foundation, no
Collection, no Choice, no resizing, no `OrdinaryZF` and no `isZFModel`. The
enforcement is that a hypothesis cannot be used without appearing there, so a
reader who wants to know what the completion costs reads six lines rather than
trusting a paragraph.

Track D built the same discipline one layer down. `GroundDescription.agda` takes
the structure, ordinary Extensionality and the path realization, and nothing
else; `OrdinaryZF` appears in exactly one place in that file, as the explicit
argument of `fromOrdinaryZF`, so that `hasInfinity` and `foundation` stay outside
the ledger of every description result (`REPORT-D.md:23-28`). Its `hasImage′`
takes Separation and Collection as two standalone arguments where K1's `hasImage`
took an eight-field record and used exactly those two, a fact established by
reading the body rather than the header.

The strongest form of the same idea is that a parameter cannot unfold. Track C
is parameterized by the five FIELDS of a `ForcingNotion` rather than by the
record (`REPORT-C.md:44-48`), which both removes the wait on Track A and lets a
consumer instantiate from raw data.

### Completeness is relative to the model's coded subsets

The roadmap's sentence is that "a ground-complete algebra is not automatically
complete for external families"
(`cohen-implementation-roadmap-2026-09.md:158`), and the architecture's N3
explains why the coded algebra cannot be a `TruthAlgebra` instance at all: `⋀` and
`⋁` are total fields with no side condition (`src/Base/Truth.lagda.md:72`), so
instantiating the record at the coded carrier needs either a junk default, which
makes every unbounded quantifier evaluate to junk, or an added hypothesis.

The enforcement is by absence, and the absence is greppable.
`CodedCompletion.agda` contains no `TruthAlgebra` at the coded algebra: the one
occurrence of the name is `open TruthAlgebra (hPropAlgebra ℓ)` at `:53`, the host
algebra. `hostSup` occurs exactly once in the file, at `:926`, inside a comment
saying it is not there. `CompleteForCoded` quantifies over a ground code `X : S`
with `⟨ X ⊆ˢ B ⟩` and has no predicate parameter and no host family in any field.
The single legal bridge to a host family is `AdmittedFamily`, whose `attained`
field is the coding hypothesis written out, together with `admitted-upper`,
`admitted-transfer` and `admitted-unique` (`REPORT-F.md:201-221`). Track B carries
the mirror constraint on its own side: `CompleteHost` is for the two algebras that
genuinely have host-indexed suprema and must never be applied to the coded
algebra, recorded at `Algebra.agda:27-31` and again at `REPORT-C.md:382-384`.

### Nothing is built in the ambient universe, and nothing is chosen

The architecture's N10 names this the single most likely silent failure in the
package: `V.Smallness.separateFromSmall` returns a separated set as data with no
formula and no truncation, it is the shortest path to every object K2 needs, and
the set it returns lives in V and not in M. Nothing would fail until K12's
internal ultrafilter or K13's quotient. Measured over the ten deliverables,
`V.Smallness` occurs once, in the `CodedCompletion.agda:8` header comment that
forbids it, and `Base.Choice` and `Cubical.HITs.SetQuotients` occur zero times in
any file. The separative quotient is delivered as a coded image and never as a
quotient set, which is why K2 adds no new dependency on set quotients
(`bedrock-k2-architecture.md`, N9).

`grep -cE "postulate|TERMINATING|trustMe"` over the ten files returns zero
matches, and so does a search for U+2014.

### `i` is not injective, and no signature may assume it is

Bell defines a Boolean completion as an order isomorphism onto a dense subset
(`bell-2005-boolean-valued-models.fulltext.md:3473-3476`), and the architecture's
N8 records that this contract is uninhabitable for the posets K2 must accept. K2
takes Problem 2.4(iii) instead. The enforcement is that there is no `i-inj` field
anywhere, and that `i-injective` at `HostRegularOpen.agda:908` takes `LEM ℓ`,
`separative` AND `antisymmetric`, each as an explicit argument. Section 3 records
that the two adapters are independent and that this was proved rather than
assumed.

### A semantic certificate and a property certificate are different objects

The roadmap forbids manufacturing a chain condition on the completion from one on
the presentation (`cohen-implementation-roadmap-2026-09.md`, section 4's
certificate table). Track G's enforcement is structural and checkable: no field of
`CertifiedCompletion`, `Embedding`, `BoundedLattice`, `IsBoolean` or
`CompleteForCoded` mentions a chain condition, countability, closure, a size
bound, fullness, a name or a translation, and `PropertyTransfer` is a separate
record whose two property arguments are arbitrary `Presentation → Ω`
(`REPORT-G.md:160-166`). Measured here: `grep -niE "chain|countab|fullness|
translat"` over `Certificate.agda` returns eleven lines and every one of them is
a comment. A transfer package for one chain-condition variant therefore inhabits
a type naming that variant and no other, and no operation in the file rewrites
it.

### Excluded middle is an argument, never a parameter

`LEM ℓ` is a parameter of no top-level K2 module. Measured over the ten
deliverables it is an explicit argument of 37 named declarations in six files, at
`ForcingNotion.agda:315` (one), `Algebra.agda:418,435,475` (three),
`HostRegularOpen.agda` (thirteen, `:770` through `:908`), `CodedCompletion.agda`
(five, `:1297` through `:1359`), `Certificate.agda` (ten, `:518` through
`:1511`), and `InstancesCompletion.agda` (five, `:68` through `:207`). The one
place it is a module parameter at all is the anonymous inner module
`Certificate.agda:858`, whose `lem` covers the five homomorphism laws of the
comparison. The remaining four files, `GroundDescription.agda`,
`CodedVocabulary.agda`, `Instances.agda` and `K2Bridge.agda`, do not mention it.
At the intended instantiation `ℓ := ℓ-suc ℓ₀` every one of these is
`LEM (ℓ-suc ℓ₀)`, which is the hypothesis `L⊨ZFC` and `L⊨GCH` already carry, so
K2 adds nothing to the T3 ledger.

## 3. What was refuted rather than repaired

Project rule 14 is refute, do not repair. Every item below was measured, and
where an exit code is quoted it came from a compile that was run rather than
predicted.

### The architecture's construction table is not typeable, and its own repair does not exist

Track D found the idiom that carries the whole table. `the _ (pow carrier)` does
not elaborate: an element of the truth-value type is a pair of a type and a proof
that the type is a proposition, the class argument appears only under the bracket
and inside the `isProp` components, so unification determines the carrier half of
the metavariable and leaves the `isProp` half blocked. Measured rather than
argued: exit 42 with `[UnsolvedConstraints]` blocked on `_Q.snd`, against exit 0
with the class written out (`REPORT-D.md:32-42`). The remedy shipped is
`powerOf`/`powerOf-spec` and `separateOf`/`separateOf-spec`. Track F confirmed the
idiom dead at all twelve of its sites by using the remedy instead
(`REPORT-F.md:394-398`).

Track E found the deeper half. The table's rows instantiate a formula's slots
with constants, and the tree has no operation that turns a variable into a term:
`grep -rn "substFo\|substTm\|_\[_\]" src/FOL/` returns nothing, `renameFo` maps
variables to variables, `mapFo` maps constants to constants, and `placeFo` runs
the opposite way, from constants to fresh variables (`REPORT-E.md:183-213`). The
architecture's own trap 2 had asserted the operation existed. Track E wrote it:
`instFo` with `⊨-inst` and `Δ₀-inst`, on the exact model of `renameFo` and
`Sat.⊨-rename`, plus the `sepAt` specialization for the `Formula S 1` shape
Separation takes. Without it not one row of the table is writable.

### Two architecture signatures do not typecheck, and one of them is a type error rather than a level slip

Track B measured the `Nondegenerate` field verbatim inside a module over a generic
`TruthAlgebra` and got exit 42 with `Ω !=< Σ (Type _ℓ_11) _S_13`
(`REPORT-B.md:149-161`). The delivered field is `⊥ ≡ ⊤ → Empty.⊥`, which stays in
`Type ℓ'`.

Track C measured two more. The architecture's `i-dense` indexes a `⋁ Cond` by
`i p ≤ᴮ U`, which unfolds to a path in `Reg : Type (ℓ-suc ℓ)` where the family
must be `Cond → hProp ℓ`; written verbatim at the Bool instance it gives exit 42
with `[UnequalSorts] Type₁ != Type` (`REPORT-C.md:261-280`). The architecture's
`positive↔nonzero` fails the same way (`:282-293`). Both are delivered in repaired
form, `i-dense` over the small entailment `fst (i p) ⊑ fst U` and
`positive↔nonzero` as a cross-level equivalence. The cross-level equivalence
carries its own measured negative: the track suspected the library's
`propBiimpl→Equiv` was level monomorphic because one variable block declares four
types at one level, checked that suspicion in a probe before reporting it, and
found it WRONG at exit 0 (`REPORT-C.md:295-302`). The negative was measured before
it was written down.

### The pseudocomplement is not a pseudocomplement, and the one-sided draft would have compiled

This is the item that most nearly entered the tree as a silent error. On the
two-condition poset, `{a} ⋆ = {b}` and `{a} ⋆ ⋆ = ∅`, so `U ⊑ U ⋆ ⋆` fails for a
`U` that is not downward closed; and `{b} ⋆ ⋆ ⋆ = ∅ ⋆` is everything, so
`U ⋆ ⋆ ⋆ ⊑ U ⋆` fails too (`REPORT-C.md:320-333`). The consequence is that
`⋆⋆-unit` and `⋆-regular` carry `Down U` explicitly and `regular-down` derives it
from regularity so that no operation has to assume it. The sharp part is the
counterfactual: a draft taking regularity to be the one-sided `U ⋆ ⋆ ⊑ U` would
have TYPECHECKED and been wrong, because `{a}` satisfies that one-sided condition.
The two-sided biconditional at `HostRegularOpen.agda:229` is load bearing. Track F
met the same obstruction independently in the coded calculus and computed its own
counterexample, `starOf {b} = {a}`, `starOf² {b} = ∅`, `starOf³ {b} = {a,b}`
(`REPORT-F.md:407-413`), and its `Regular` is two-sided for the same reason
(`:400-405`).

### The standing nonseparative witness is not nonseparative

The architecture's N5 found by reading that `NonseparativeCompletion.agda` of the
K0 evidence ledger orders its two left conditions so that each refines the other,
which is a failure of ANTISYMMETRY and not of separativity, and that Bell's
refinement condition holds on every pair. Track I turned that reading into
machine-checked theorems: `K0Four.sep` proves the example separative in sixteen
cases each with its witness, `K0Four.not-antisymmetric` proves antisymmetry fails,
and `adapters-independent` states both halves of the independence in one type,
one presentation separative and not antisymmetric, another antisymmetric and not
separative (`REPORT-I.md:154-166`, `:265-272`). So `i-injective` needs two
independent adapters and not one, which is why it takes both. The consequence for
the record is the one N5 demanded: the file name `NonseparativeCompletion.agda`
names the property its example HAS, and the roadmap's request at `:251` for a
nonseparative example was not satisfiable from existing material until Track I
built the two-condition presentation.

The same track refuted the untruncated form of the K0 compatibility relation
rather than porting it. `k0-Σ-form-is-compatibleData` is `refl`, so the K0
relation IS Track A's `compatibleData`; and `Σ-form-not-prop` shows that at the
pair `(k-top, k-top)` the sigma has two distinct witnesses, so it is not a
proposition and cannot be the value of a formula or an argument of `⋀` or `⋁`
(`REPORT-I.md:112-127`).

### No host-generic filter, and the hypothesis that had never been witnessed

`ForcingNotion.agda:315-316` proves

    no-host-generic : LEM ℓ → atomless → (G : Sub) → isFilter G
                    → hostGeneric G → ⟨ ⊥ ⟩

that is, on an atomless notion no filter meets every dense HOST subset. It
consumes `LEM ℓ` as its first explicit argument and, of `isFilter`, only the
`directed` field, through `filter-compatible`; `inhabited`, `upward`, `nonempty`,
`isSetC`, `≼-refl` and `≼-trans` are not consumed (`REPORT-A.md:194-201`). The
architecture's proof sketch contained a case split the delivered proof does not
need, which is a simplification and not a defect in the statement
(`REPORT-A.md:227-235`).

Track I then proved the atomlessness hypothesis load bearing rather than
decorative: trivial forcing is not atomless, and `everything` is a filter on it
that IS host generic, so `atomless-not-removable` exhibits the counterexample and
no excluded middle is involved in either direction (`REPORT-I.md:146-152`,
`Instances.agda:557-558`).

**This item has since been sharpened by a later package and the sharpening is not
comfortable.** K5's refutation track found that NO ATOMLESS FORCING NOTION EXISTED
ANYWHERE in K1 through K4 (`k4-boolean-semantics-and-compiler-2026-09.md:340-356`).
K2's three acceptance instances are a two-condition presentation, a
four-condition one and a one-point one, and none of them is atomless. So K2's own
theorem forbidding a host-generic filter was for three packages an implication
whose hypothesis had never been witnessed, and the existence of a host-generic
filter had not been refuted anywhere. K5 supplied the missing notion, the binary
tree of finite two-valued strings under extension, with atomlessness proved
constructively. A successor reading K2's instance list should read it as covering
the empty, one-point, two-element and degenerate cases and NOT the atomless one.

### Hypothesis lists wrong in both directions

Five results were charged excluded middle they do not spend. `regular-denseBelow`
is constructive in both directions, and the backward direction is a `PT.rec` into
the bottom rather than a decision, so it is delivered with no `LEM` argument at
all (`REPORT-C.md:252-259`). Track F's coded `mem→denseBelow` is shorter still,
one line, and the architecture had charged it a `LEM` too (`REPORT-F.md:415-420`).
Track G measured that `compare`, `compare-ub`, `compare-lub`, `compare-mono`,
`compare-id` and `compare-unique` all compile with no `LEM` in scope, against an
architecture that said "`compare` and every `compare*` statement carry `LEM ℓ`"
(`REPORT-G.md:177-185`). The consequence is a real mathematical statement and not
bookkeeping: uniqueness of the completion is a CONSTRUCTIVE consequence of the
certificate plus the two ground hypotheses, and only the existence of the
isomorphism's laws is classical (`REPORT-G.md:51-58`). `compare-id` is literally
the `recover` field, which is the cleanest evidence that the map is the density
field and nothing more.

Two went the other way. `transport-certificate` DOES need `LEM ℓ`, where the
architecture listed it with no hypotheses, because the transported `recover` must
show that `b` is dominated by the join of the images of the source conditions
below it and the only available route runs through the classical `dense-form`
(`REPORT-G.md:254-259`). And Track G found a classical step the architecture
records nowhere: Track C defines `positiveᴮ` as inhabitedness while a certificate
must define it as nonzeroness, since without `B-spec` nothing says an element's
code is a set of conditions, so instantiating `i-pos`, `i-compat→` and
`i-compat←` from the regular-open construction spends one `LEM ℓ` at the
instantiation site (`REPORT-G.md:187-200`).

### Two claims of the architecture's table were wrong about the mathematics

`⋀ᴮ` needs no regularization and must not have one: an arbitrary intersection of
regular opens is already regular, being downward closed and below each member, so
the double star would have been correct but strictly more work and would have made
the infimum laws harder (`REPORT-F.md:377-384`). And the table's join and supremum
rows cannot be applications of Track E's `regularizeAtˢ` at all, because the set
being regularized is a UNION and a union has no code inside the core: producing
one needs Union, which the table's own annotation forbids on those rows. Six
further formulas were written to close that gap, each with a `Δ₀` witness and a
`refl` reading (`REPORT-F.md:366-375`).

### The obstruction that was stated rather than claimed

Track C's `i-kernel` is delivered constructively in the INCOMPATIBILITY form and
classically in Bell's separative form, with the bridge split into a constructive
half and a classical half. The report is explicit that this is an obstruction and
not a refutation: no countermodel was constructed, and the honest claim is that
the separative form is not provable by this calculus without excluded middle
while the incompatibility form is (`REPORT-C.md:304-318`). Track I made the same
distinction for its own two-element classification: `Bottomed.two-valued` takes
`LEM ℓ` and spends it on exactly one decision, and the converse, that a
constructive classification would decide every double-negation-stable
proposition, is flagged as reasoning rather than as a checked theorem
(`REPORT-I.md:253-263`). Both notes are worth more than a confident sentence would
have been.

## 4. What the tracks measured that the architecture could not know

### The declaration that does not elaborate, met here first

`CodedCompletion.agda:1148-1152` records the measurement in the source itself: a
statement whose TYPE mentions the composite `iᴮ p ⊓ᴮ iᴮ q` sends the elaborator
into a check that never finished. Three drafts of exactly the architecture's
signature, differing only in how the proof was factored, were killed at 19 min
35 s, 10 min 51 s and 10 min 59 s of wall clock, each at about 1.15 GB resident,
the last measured by `time` at 657.26 s of user CPU; the same file with that one
declaration removed checks in 6.8 s (`REPORT-F.md:422-440`). The third draft had
every auxiliary lifted to a top-level definition with an explicit type, so the
cost is in the SIGNATURE and not in the proof term. The delivered repair
abstracts the meet into a variable `m : El` with a splitting hypothesis, and the
caller instantiates. The same reason is why `reads-⋁` and `reads-⋀` are not
delivered.

This is the first appearance in the programme of what K3 and K4 later reproduced
at new sites and what K5 finally sized with a ladder. The remedy that worked here
worked because K2 never had to state a law AT the composite; section 6 records
what it costs a package that does.

### Universe levels, wrong in both directions

Four reports corrected a declared sort, and the rule behind all four is the one
K4 later stated in general: a record rises only if a FIELD is a path in the
truth-value type. Track B's `CompleteHost` compiles at the architecture's
`Type (ℓ-suc (ℓ-max ℓ ℓ'))` but lives in `ℓ-max (ℓ-suc ℓ) ℓ'`, and copying the
larger spelling pushes a level a consumer does not need (`REPORT-B.md:167-172`).
Track D's `ProductFragment` is `Type ℓ` and not `Type (ℓ-suc ℓ)`, while
`GroundFragment` really is large because its paths field is a path in the
truth-value type (`REPORT-D.md:44-46`). Track G found four records at `Type ℓ`
where the architecture printed one level up, and confirmed five others large for
the stated reason (`REPORT-G.md:261-267`). Only Track F found the opposite:
`AdmittedFamily` is `Type (ℓ-suc ℓ)` and not `Type ℓ`, because its `attained`
field is a path between two elements of `Ω` (`REPORT-F.md:360-364`).

Track A's report is the counterweight and is worth recording as a measured
positive: every type in architecture section 1.1 typechecked unchanged, levels
included (`REPORT-A.md:237-244`).

### Implicit arguments are where this tree costs time

Four independent measurements, all mechanical, all invisible until the compile.
A record field whose type begins with implicit arguments cannot be filled by a
function that pattern matches on them: `≼-trans = ord-trans` inside a record
literal gives "Refusing to invert pattern matching of ord because the maximum
depth (50) has been reached", then eighteen unsolved metas, exit 42
(`REPORT-I.md:320-328`). The same lambda is needed for a MODULE application, which
Track C measured first and which every consumer of `HostRegularOpen` repeats,
including `CodedCompletion.agda:1190` (`REPORT-C.md:357-362`). A lemma whose
implicit argument occurs only under `fst` leaves an unsolved meta at every call
site, measured at eleven unsolved metas with no type error, and the fix is to
state the lemma on the codes and substitute along code paths
(`REPORT-G.md:342-351`). And a record declared inside a parameterized module has a
record module whose telescope makes the enclosing parameters IMPLICIT, so the
qualified application is a `ModuleArityMismatch`; `K2Bridge.agda:54-58` records
that its own first draft failed at exit 42 for exactly this reason, which is the
fact reproduced rather than taken on trust.

Two smaller ones from Track I, both about finite carriers. A `Lift Bool` carrier
with pattern synonyms gives no constraint on the lift level, so every equation
about the named points leaves the level meta open; a `data` declaration inside a
module whose level is already fixed has no such argument (`REPORT-I.md:337-343`).
And ordering the clauses of a finite order so the SECOND argument is matched first
turns transitivity from sixty-four cases into four clauses plus two four-clause
lemmas (`:345-349`).

### A reading proved by `refl` needs a negative control, and Track E ran one

Every reading theorem in `CodedVocabulary.agda` is `refl`, which is worthless if
the formula and the host predicate are wrong in the same way. Track E swapped two
arguments on the right of `orderAtˢ-reading` and recompiled: exit 42,
`[UnequalTerms] p != q of type Fin n`, then restored the file from a byte copy and
rechecked at exit 0 (`REPORT-E.md:24-30`). The argument order of `orderAtˢ` is
load bearing, and this is the evidence that it is checked. The same track shipped
five hypothesis-free consistency facts, including `coneStarΔ-as-incompatible` and
`compatibleΔ-sym`, for the same purpose.

Track F's eight definitional identities are the contract between the two tracks
and serve the same role: `starOf` applied at most twice IS each of Track E's
regularity formulas, all eight proved by `refl`, so if any of `coneΔ`, `pseudoΔ`,
`regularizeΔ` or `refinesΔ` is respelled those eight lines fail first and loudly
(`REPORT-F.md:104-118`, `:492-495`).

### Bell's own formula is a theorem here, not a definition

`coneΔ` is the constructive double star, which reads "every `r` below `q` in the
carrier is NOT NOT compatible with `p`". Bell's displayed formula, every `r`
below `q` compatible with `p`, is strictly stronger and is the classical theorem
`cone-as-Bell`, while the free direction `Bell→cone` is constructive
(`REPORT-E.md:250-256`, `REPORT-F.md:496-498`). Both reports say the same thing in
the imperative: do not state Bell's formula by `refl` anywhere. This is the one
place where transcribing the textbook would have produced a definition that is
classically but not constructively the intended one.

### The truth-value algebra unfolds by `refl`, and excluded middle does not

Track A's table is the fact every later track used: at the `hPropAlgebra`
instance every connective unfolds definitionally, `⟨ P ⊓ Q ⟩` to a product,
`⟨ ⋁ A F ⟩` to a truncated sigma, so `PT.rec`, `PT.map` and `∣_∣₁` apply to any
`⟨ ⋁ _ _ ⟩` with no lemma in between (`REPORT-A.md:287-306`). Against that, `LEM`
in this tree is stated with the UNLIFTED bottom while the algebra's `⊥` is
lifted, so every consumer of the `inr` branch converts at the use site
(`REPORT-A.md:308-313`). That mismatch bit more than one track.

Two interface facts of the same kind. A record may share its name with its
enclosing top-level module, verified by a five-line probe before the file was
written and again by a downstream consumer (`REPORT-A.md:315-320`). And
`Cubical.Functions.Logic` already proves six of Track B's fifteen hProp laws, with
two orientation corrections and one trap: the library's `⊔-identityʳ` is NOT
usable for `⊥-unit`, because the algebra's bottom is lifted and the library's is
not (`REPORT-B.md:202-211`).

### The cost profile, and the one thing that was not cheap

Every K2 file is cheap to check. The heaviest deliverable is `Certificate.agda` at
6.3 s and 1.37 GB, and the next is `CodedCompletion.agda` at 7.57 s wall
(`REPORT-G.md:17`, `REPORT-F.md:26`). The architecture's N13 heap obstruction,
carried over from two K0 measurements that exhausted the fixed 8 GB heap, did not
materialise anywhere in K2, and the reason is the design it forced: no K2 module
takes `isZFModel` or any `L.` import, and the ground enters as named fragment
fields. What did cost machine time was the elaboration wall above, and it is a
TIME wall at a flat resident set rather than a heap failure, which is the same
signature K4 and K5 later isolated.

## 5. Two records called Presentation, and the theorem that settled it

Track F and Track G each declared a record named `Presentation`, and they differ.
Track F carries the order as a ground SET of Kuratowski pairs with `order-typed`;
Track G carries it as a host relation on points of the carrier. Both stated a
reason and the reasons do not conflict.

Track F's is a necessity argument: `Separation` takes `(a : S) (φ : Formula S 1)`,
every object of the construction table is a Separation whose formula takes the
order code as a constant slot, so with a host order there is no formula to hand to
Separation and the completion cannot be built at all, no `B`, no `i p`, no join,
no supremum (`REPORT-F.md:462-477`). Track G's is a reachability argument: `B⁺`
must produce a presentation of the same type its own certificate consumes, and
producing a CODED presentation of the nonzero part means producing its order
graph, which is the missing work of section 6. Had Track G taken the coded record
it would have delivered the certificate and the comparison and then stopped before
`B⁺`, `unit` and the whole map calculus (`REPORT-G.md:298-308`).

The coordinator did not rule between them. `K2Bridge.agda` writes the adapter, one
record expression, and then proves the theorem that makes the adapter worth
writing:

    bridge-agrees : G.notion hostPresentation ≡ decode laws
    bridge-agrees = refl

Track G reaches the host structural vocabulary through its own notion and Track F
reaches it through `decode`; they agree, so compatibility, density, antichains,
separativity and Bell's separative equality mean the same thing on both sides of
K2, and no second definition of any of them is in play. Without the theorem the
two halves could have drifted silently, since the types already agree
definitionally and a drift would not have been a type error.

The correct reading of the pair, and it is Track G's own recommendation stated as
a measured opinion rather than a ruling: keep both records, because Track F's is
the coded layer the roadmap requires and Track G's is the host reading the
certificate consumes. A certificate over a coded presentation stays coded under
`transport-certificate` and under comparison, because those keep the presentation
fixed; it does NOT stay coded under `B⁺` (`REPORT-G.md:310-317`).

## 6. Open items handed forward

### The coded order graph of `B⁺`, with one of its four inputs now supplied

This is the one thing K2 did not deliver, and Track G says so in its own report
rather than leaving it to be discovered (`REPORT-G.md:222-239`). `B⁺` exists, is
separative, has a top, carries a `unit` certificate and iterates, and it is built
from one Separation on `B` against `¬̇ (var zero ≐ con (fst ⊥ᴮ))`, needing neither
`ProductFragment` nor `PowerSet` nor `LEM ℓ`, against an architecture signature
that demanded all four (`REPORT-G.md:214-220`). What is missing is `B⁺` as a
`Presentation` in Track F's sense, that is with an order GRAPH, and therefore as
something K3 can write Δ₀ formulas about.

Track G names four inputs for it:

1. the double power set of the nonzero part;
2. a Separation against `prAtˢ` and `subsetAtˢ` instantiated by constants;
3. Pairing, to construct the witnesses `{{u}}` and `{{u},{u,v}}` for the
   reflexivity and transitivity laws;
4. internal injectivity of the Kuratowski pair, which at the time no track had
   written.

**Input 4 is now stale and the record should not be read as if it still stood.**
K3 proved both halves of it, over K2's own `isKPairΔ` and not a variant.
`NameKernel.agda:321` proves

    entry-inj : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c)

and `NameSpace.agda:388` proves

    kpair-unique : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b

that a set the object language reads as the Kuratowski pair of `x` and `b` is the
kernel's entry on the nose, with Extensionality spent there and essentially
nowhere else on that track. `NameSpace.agda` imports `isKPairΔ` and `prAtˢ`
directly from `CodedVocabulary` at `:97-98`, so the two vocabularies are the same
one. A caution on the locator: the copy archived at
`bedrock-proofs-archive/k3/NameSpace.agda` is the earlier 882-line version and
has the lemma at `:317`; the 973-line version mounted in the K3, K4 and K5
compile roots has it at `:388`, and `entry-inj` is at `:321` in both.

Inputs 1, 2 and 3 do not exist. Track G sizes the remainder as a self-contained
follow-up brief of the size of its Track D, and records that nothing else in K2 as
designed consumes the graph of `B⁺`. The consumer that does is K3 over `B⁺`; K3
over an ordinary coded presentation needs nothing new.

### The five coded operations are unsealed, and three later packages have priced it

`grep -c opaque` over every K2 file returns 0. So every coded operation of
`CodedCompletion.agda` is an unsealed description-operator term, `separateOf`
being `the` over the description operator, and nesting one inside another puts one
description inside the syntax of another. Three independent measurements have
since established what that costs downstream, and they are quoted here as numbers
rather than as a style preference.

K4's Track K measured that a declaration whose type nests two operations of an
unsealed coded algebra does not elaborate: no finish in 200 s unsealed against
1.38 s sealed, one change and nothing else, for the first complement law
transported through `reads`, `reads-inj` and the host law
(`bedrock-proofs-archive/k4/InstanceCoded.agda:44-48`). Its ladder also shows that
depth one is free and that which operations are nested makes no difference.

K5's Track C measured a different threshold with the same remedy. Four coded sets
built by `separateOf` and left unsealed do not finish in 11 minutes at 2.2 GB
observed by `ps`, while the same file with four separate `opaque` blocks exits 0
in 1.65 s at 386 MB; the threshold is the first declaration whose PROOF puts a
separated set under a join and converts against it, and declarations that only
transport along the Separation specification are free unsealed
(`/tmp/bedrock-k5-probes/REPORT-C.md:28-33`).

K5's Track I measured K2's OWN named composite. `iᴮ p ⊓ᴮ iᴮ q`, the one
`CodedCompletion.agda:1148-1152` names and says it never wrote a statement at, does
not finish in 471 s at 1.00 GB with the outer meet unsealed, and exits 0 in 1.54 s
at 462 MB with the outer meet sealed and the two inner descriptions left exactly
as K2 wrote them (`/tmp/bedrock-k5-probes/REPORT-I.md:81-82`). A further rung
shows that ONE unsealed nested argument under an unsealed outer operation already
hangs, in 200 s (`:83`). The resident set is flat, so this is a time wall and not
a heap failure. The positive half of the rule is therefore weaker than K4 stated
it: sealing the OUTER operation suffices.

The handoff is precise. Seal each of the five coded operations inside
`CodedCompletion.agda` itself, one `opaque` block per operation with its
membership specification: `_⊓ᴮ_` at `:664`, `¬ᴮ_` at `:710`, `_⊔ᴮ_` at `:748`,
`supᴮ` at `:820`, `infᴮ` at `:882`. K4 already built exactly these five seals on
its own side as `negᴷ`, `meetᴷ`, `joinᴷ`, `supᴷ` and `infᴷ`, in five separate
blocks (`k4/InstanceCoded.agda:144-168`), so the shape is known to work and the
only question is where it lives. The separate blocks are load bearing and one
block holding all five would be useless, because opening it to unfold the meet
would also unfold the complement (`k4/InstanceCoded.agda:138-141`). Sealing at the
source would remove the wall for every later package at once, and would be
consistent with K3's own practice of sealing a description-operator term together
with its specification at the point of definition.

### The coded half of acceptance instance 1

Exit item C6 asks for the two-condition non-refined presentation "checked
host-side AND as a coded presentation in a ground"
(`bedrock-k2-architecture.md:735`). The host half is delivered and is thorough.
The coded half was not attempted, and Track I reports the reason rather than
hiding an exit code: nothing was run (`REPORT-I.md:291-316`). A coded instance 1
must produce two SETS of the ground, a two-element carrier and an order graph
containing three Kuratowski pairs, plus `ForcingLaws` for them, and Track F's
`Core` takes a `Presentation` as an INPUT with no Pairing and no Infinity in its
ledger, so building one is a new construction needing set-existence hypotheses no
landed K2 track supplies. What a successor needs is named: two distinct ground
sets, their Kuratowski pairs, the graph, and `decode`, which is total and free
once the presentation exists.

### What Track F did not deliver, and why it matters to Track G

`below`, `iImage`, `recover` and the third module `CodedOperations` with `igraph`
are absent from `CodedCompletion.agda` (`REPORT-F.md:448-458`). `below` and
`iImage` are fields of Track G's `Embedding`, and `igraph` is the only row of the
construction table that consumes Pairing and Union. The coordinator's standing
instruction was to spend the remaining effort on the construction table and
relative completeness, which are delivered. The consequence for a successor is
that a CERTIFICATE over Track F's coded completion cannot be assembled from Track
F alone: the `starOf` calculus, `fromStar`, `iSet-mem` and `meet-split` are what a
follow-on brief needs, and Track F names the shape of the missing `isConeAtˢ`
formula. The infinitary agreements `reads-⋁` and `reads-⋀` are missing for the
elaboration reason of section 4 and are the other half of the same brief.

### Interfaces handed forward, with their one measured consumer

`AdmittedFamily` was the architecture's N14, the item K2 could not settle from its
own side: whether the interface as specified suffices for K4's compiler was not
decidable within K2. It has one measured consumer today, and it is not K4. K3's
`NameWeight.agda` takes `K2.AdmittedFamily` for the Boolean weight of a subname,
cites `admitted-transfer` and `admitted-unique` by name, and proves that any
admitted family with the same values has the same join
(`/tmp/bedrock-k5-probes/NameWeight.agda:248`, `:279-298`). No K4 or K5
deliverable names it: `grep -rln "AdmittedFamily"` over the K4 and K5 compile
roots returns only the K2 and K3 sources themselves.

### Smaller items, carried rather than closed

The complete-subalgebra agreement of Bell Theorem 1.20 and Corollary 1.21 was
assigned by K2's exit item C5 to K6, on the architecture's N12 reasoning that
those theorems quantify over names and formula values and so cannot be stated
before K3 and K4. **That assignment has since been superseded**: the coordinator
ruled that K4 owns 1.20 and the atomic half of 1.21 and that K6 keeps the
consequences, because the mathematics is a simultaneous induction on the ATOMIC
values in two algebras
(`k4-boolean-semantics-and-compiler-2026-09.md:211-223`). K2 delivers the
definition of complete subalgebra and the structural laws of the inclusion, which
is what it promised.

`hasImage′` carries a prime on an exported name, against the style rule, and the
spelling was kept so that Track F and the coordinator could find it; a rename is
owed when K2 moves into `src/` (`REPORT-D.md:62-65`).

The reserved-seat prose at `src/Base/Truth.lagda.md:161-166` promises the
`TruthAlgebra` seat to "the regular-open Boolean completion of a forcing poset".
That promise is kept, by the HOST algebra of Track C, and the prose needs one
added clause saying that the model-internal completion is complete only for the
ground's coded subsets and is not the instance. This is a `src/` prose change and
is therefore a coordination item with the trilingual writing phase, not a K2 code
change.

## 7. Terminology

The terminology track is blocked on an owner ruling and blocks no code; K2
proceeded with English-only source prose throughout, which is what the current
phase permits. The collision is that `dev/glossary.toml` carries `coherence` with
the Chinese rendering 相容 owner-ruled on 2026-08-03 and that the same word is
the standard Chinese rendering of the forcing compatibility of two conditions,
which is the notion K2 introduces. The evidence for the ruling is assembled in
`terminology-compatible-2026-09.md`, which proposes three options and chooses
none, because the project rule is that parallel authors may not resolve a
terminology collision. The one practical asymmetry that note records is that the
2026-08-03 entry is consumed by settled K0-era prose while forcing compatibility
has no Chinese prose at all, so the cheaper move today is to give forcing
compatibility a different word, and the cheapest moment to decide is before K2's
prose is written. No Chinese or Japanese rendering of either sense has been
written by any agent.

Track H's remaining deliverable is unchanged: a glossary batch with literature
evidence in both languages for the twenty-two structural terms listed at
`bedrock-k2-architecture.md:664`, plus a note recording Bell's "refined" as the
printed source synonym for "separative" with its locator.

## 8. Validation

Every one of the ten files checked at exit 0 with
`GHCRTS="-A64m -I0 -M8g" agda <file>`, each from a deleted interface so that no
exit code quoted in a report is a cache hit. No `postulate`, no pragma, no hole,
no unsolved metavariable in any of them; `--safe` batch mode reports an unsolved
metavariable as an error. Every track waited for a process slot with the
prescribed two-process loop, and the 8 GB heap was never exhausted.

Timings and peaks, as each report measured them: `ForcingNotion.agda` 0.75 s and
245 MiB (`REPORT-A.md:23-25`); `HostRegularOpen.agda` 2 s wall, peak not measured
(`REPORT-C.md:27-31`); `CodedVocabulary.agda` 0.98 s (`REPORT-E.md:17`);
`CodedCompletion.agda` 7.36 s user and 7.57 s wall (`REPORT-F.md:26`);
`Certificate.agda` 6.3 s and 1.37 GB, `CertificateUse.agda` 3.4 s and 0.82 GB
(`REPORT-G.md:17-18`); `Instances.agda` 0.82 s and 255 MiB and
`InstancesCompletion.agda` 1.01 s and 314 MiB (`REPORT-I.md:33-35`).
`Algebra.agda` and `GroundDescription.agda` were checked at exit 0 with no peak
measured, and `K2Bridge.agda` was checked by the coordinator.

Hygiene, re-run over the ten deliverables for this record rather than copied from
a report: `postulate`, `TERMINATING` and `trustMe` return zero matches;
`Base.Choice` returns zero; `Cubical.HITs.SetQuotients` returns zero; U+2014
returns zero; `i-inj` matches only two comment lines and the two lines of
`i-injective`, which takes `separative` and `antisymmetric` explicitly;
`hostSup` matches one comment line; `V.Smallness` matches one comment line; and
`opaque` returns zero, which is the open item of section 6.

The sources are archived at `~/Agentic/bedrock-proofs-archive/k2/` with the
architecture, the shared preamble and the eight reports, alongside K0 recovered
byte-exact from the record documents, K1, K3 and K4. The K5 reports quoted in
section 6 are not yet archived and live in the K5 compile root under `/tmp`,
which does not survive a reboot on this machine; two worktrees were lost that way
earlier in the programme.
