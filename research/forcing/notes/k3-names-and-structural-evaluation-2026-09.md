# K3 names, structural evaluation, translations, check and generic names

Date: 2026-09-11. Source baseline: `cbd1510e`. Status: K3 complete on its roadmap
scope, sixteen files at exit 0 under `--safe`, with one obstruction PROVED rather
than reported. This record follows the K0, K1 and K2 convention: proof work lives
in a task-specific temporary compile root, with the sources archived outside it.
No repository source file is changed, because the trilingual writing phase owns
`src/` on `main`.

## 1. What K3 delivers

The roadmap's K3 is "names, codes, valuation, translations, check and generic
names" (`cohen-implementation-roadmap-2026-09.md` section 2). All of it is
delivered, on the representation K0 selected and against the interfaces K1 and K2
supply. Sixteen files, 7448 lines.

| File | Track | What | Lines | SHA-256 prefix |
|---|---|---|---|---|
| `NameKernel.agda` | A | the name carrier, the subname descent and the recursor | 644 | `b24d6cc76f155975` |
| `NameSupport.agda` | B | supports, entry indices and weight families | 709 | `6e815f219a34448b` |
| `NameSpace.agda` | C | closed families, the recognizer and the name bound | 882 | `07cba904f55a739c` |
| `NameImage.agda` | D | the internalization contract, the keystone | 413 | `2a443d11f958861d` |
| `NameWeight.agda` | E | the Boolean weight of a subname, as a join | 499 | `d8329635f8753388` |
| `TranslateForward.agda` | F | the forward translation | 662 | `dce4218861a96641` |
| `TranslateReverse.agda` | G | the reverse translation | 986 | `b6f8e0d6c11e822b` |
| `StandardNames.agda` | H | check names and the generic name | 737 | `2db219fa5b9f07a6` |
| `Valuation.agda` | I | the value relation and its fifteen laws | 715 | `dbe049e66382c2dd` |
| `LInstanceCore.agda` | J | tier 0 and tier 1 at L, no excluded middle | 150 | `d88fb56ee874085e` |
| `LInstanceSets.agda` | J | tier 2 and power set at L | 93 | `9b32d7dbd3894ee6` |
| `LInstanceFamilies.agda` | J | tier 3 at L | 171 | `83480edf60a079f4` |
| `LInstanceRank.agda` | J | the rank drop and the rank contract | 177 | `86f8c37f68b203eb` |
| `LInstanceImage.agda` | J | tier 4 at both grounds, and the measured negative | 351 | `132189c2dea35c9f` |
| `LInstanceOmega.agda` | J | the omega iterator | 170 | `1341dce6737dc0a2` |
| `LInstanceGround.agda` | J | the ledger, applied to the consumers | 89 | `531404dc0b8fcde5` |

The architecture that produced these is `/tmp/bedrock-k3-architecture.md`, also
archived. It was never compiled, which was a deliberate trade: a design phase that
waits for the two Agda process slots would have serialized behind K2. The cost of
that trade is visible below and was paid in measured corrections rather than in
silent errors.

## 2. The obstruction, proved

Tier 4 of the ground ledger, the member-image datum, is NOT dischargeable at the
constructible structure, and track J proved this rather than reporting it.

Tier 4 at L is EQUIVALENT to separation of an arbitrary ambient truth-valued class
out of a constructible set, with no formula, no complexity bound and no
definability requirement. Both directions are checked. That statement says L
absorbs every ambient subclass of each of its sets, which is a form of V = L for
the ambient theory: consistent, holding in any ambient model of V = L, and false
in any ambient model with a non-constructible subset of a constructible set.
Nothing short of deciding it discharges tier 4 at L.

The obstruction is located exactly, and it is NOT smallness. Tier 4 is discharged
at the ambient hierarchy in four lines, because a set there is a small-indexed
family and the membership law is definitional. A constructible set still has a
small presentation; its members are still constructible; the image still exists as
a set of the ambient universe; the values are still boundable inside L by
`smallDom`. The missing step is carving the image out of the bound. Carving is
Separation, and Separation at L reads a formula.

The consequence the programme must carry. Track D measured that tier 0 and tier 4
TOGETHER produce the check name and its recursion equation, and that neither alone
suffices. At L that route is closed, so the L instances of the check name, the
generic name and both translations must go through definable graphs, which
requires each of those four host functions to carry a formula. That is real work
and it is not done here.

## 3. The keystone result

Track D's section is titled, in the architecture's own words, the internalization
contract and the one thing no axiom gives. Its result is a measured negative at
global granularity with a positive complement at stage granularity.

The global recursion is unreachable at the tier the architecture grants, for two
independent reasons with the goals quoted: the recursion is a host recursion and
the only well-foundedness in the ledger is tier 0, which that track is not
granted; and the definable-graph route cannot start, because the graph mentions
the function the recursion is producing.

The sharpest form, and the one later packages should carry: the internal image of
the entry-forming function and the recursion equation are THE SAME STATEMENT up to
one fixed-point condition. The contract supplies the image for a GIVEN function; a
name-valued recursion is the case where the function is built from the image; and
no tier gives a fixed point. Track F later confirmed this from the consumer side,
which is independent evidence rather than a restatement: once the forward
translation exists its internalization is one line, so the contract was never the
expensive half.

## 4. What each track measured against the architecture

The architecture was never compiled and every track found signatures wrong. The
corrections are the package's second product and are listed here so K4 does not
repeat the analysis.

A join that binds a membership witness must be indexed by the membership
proposition, not by the carrier. FOUR independent reports, from tracks A, D, E and
H, each with its own compiler evidence, at four distinct sites. One of the
coordinator's repairs of such a site produced a WELL-TYPED FALSE THEOREM and was
refuted by track G rather than accepted: the Boolean support of a name is its set
of subnames, so demanding that a subname lie in the algebra constrains no weight
of the name, while the conclusion needs a positive weight at every subname. The
repaired hypothesis quantifies over the weights occurring in the name. Fixing a
binding is not the same as reading the statement back.

Every description-operator term must be sealed opaque together with its
specification at the point of definition, not only the name predicate. Track A
measured 761 s at 1.05 GB without finishing against 1.04 s at 327 MB sealed, one
term, nothing else changed. Track C independently measured 420 s killed at the
ceiling against 3.96 s sealed. Track F obeyed the rule structurally with no opaque
block at all, because every ground code former in its file is a module parameter
and a parameter is a variable that cannot unfold, which is a tighter seal.

Track J then bounded the rule. Sealed and unsealed ground ledgers cost the same,
1.56 s at 536 MB each. The earlier deaths were terms COMPARED DEFINITIONALLY
inside a proof; a tier record only ever passed as a module parameter is never
compared. The seal is correct practice and cheap insurance; what saves a file is
sealing the objects that do get compared.

A declaration, not a term, can fail to elaborate in bounded time when its type
contains a construction of one layer applied to a term of another. K2 measured it
first; track E reproduced it here at a new site, killed at 2 min 09 s and then at
a 360 s wall with the declaration isolated by ten probes. The remedy is to
abstract the composite into a variable with a splitting hypothesis; the abstracted
form is strictly more general.

The permitted-hypothesis lists over-state, reported by FIVE tracks. Track A's
empty name is not constructible from its granted tier; track B's accessibility is
never consumed; track C consumes neither accessibility nor Union, the latter
because the operations arrive as parameters and a parameter cannot unfold, which
is a compile-cost win as well as a ledger correction; track F's monotonicity and
positivity grants are unusable in the forward direction; track G's list is wrong
in four places at once.

The ground-ledger module has no owner. The architecture lists it as a dependency
node and assigns it to no track; track A hosts the four tier records at the
kernel's top level, and every later track takes them from there.

## 5. The cross-carrier question, asked and answered properly

Track H was the first module to use the kernel at both weight carriers and
measured that the two instantiations do not share the entry, child or shape
definitions definitionally, because the pairing term is sealed. It established
that unfolding the seal is NOT a repair, reproducing track A's figure, gave a
twenty-line bridge, and predicted the translation tracks would hit it harder
because they cross at every entry.

Track F measured its own half and found the cost conclusion does not follow: its
deliverable contains no bridge at all, because the subname relation never mentions
the weight, so the two carriers differ only where they genuinely differ and the
crossing collapses to three declarations paid once in a probe. It then asked that
track G be ASKED the same question rather than told its answer, because its result
was a measurement of one half and only a prediction about the other.

Track G measured for itself and got the mirror three, with a sharpening: the
subname relation never mentions the weight but is spelled through the sealed entry
former, so the two are not convertible even though neither depends on the weight;
and descent DOES transport, so one recursor serves both. Both tracks recommend
against restructuring the landed kernel, for different reasons.

## 6. The exit checklist

The architecture's seven items are closed. The negative evidence is
grep-checkable and was rerun by the coordinator on the nine name-layer files with
comments stripped, 6247 lines of code.

| forbidden | occurrences |
|---|---|
| `SetQuotients`, the quotient is K13's | 0 |
| `Base.Choice`, host choice in any form | 0 |
| `hasReplacement`, `isZFModel`, the strong record | 0 |
| `TransitiveClosure` | 0 |
| `postulate`, `TERMINATING`, `trustMe` | 0 |
| `i-inj`, injectivity of the embedding | 0 |
| `hostSup`, a join with no admitted family | 0 |
| `isGeneric`, genericity in a K3 signature | 0 |
| `OrdinaryZF` in a module defining a name | 0 |
| `import L.` or `import V.` in tracks A to I | 0 |

The last row is the one that matters most, and the architecture named it the
single most likely silent failure in the package. The smallness and presentation
modules are facts about the concrete cumulative hierarchy, not about an arbitrary
ground. A track that took an arbitrary ground and reached for a small presentation
would prove its theorem about one model while stating it about all of them, and
the two statements have the SAME TYPE, so the typechecker would not object. None
of the nine did. Track J imports them twenty-two times, which is correct, because
that is where the ground stops being arbitrary; the paragraph saying so is the
header of its first file, so it travels with the code.

There is exactly one name predicate in the package.

## 7. Open items handed on

Tier 4 at L, section 2. Either route every L-side name-valued recursion through
definable graphs, writing graph formulas for the check name, the generic name and
both translations, or record tier 4 at L as a new ledger row whose cost is stated:
it implies V = L for subclasses.

The omega-iterator adapter is supplied and the adapter is not built; whoever builds
it still owes the definability of the one-step closure operator.

The rank contract is shipped and deliberately unfilled, with its two prohibited
signatures recorded in the source.

The K2 completion has no L instance and cannot have one in K3, because a
presentation is a forcing notion with a coded order and the Cohen poset is K8's.

Terminology is blocked on an owner ruling and blocks no code: the Chinese
rendering ruled for coherence on 2026-08-03 is the standard rendering for forcing
compatibility of conditions, and parallel authors may not resolve that.

## 8. Validation

Every file checked at exit 0 with `GHCRTS="-A64m -I0 -M8g" agda <file>`; track J's
seven files additionally under `-W error`. No postulate, no pragma, no hole, no
unsolved metavariable in any of the sixteen. The heaviest single file is the
Collection proof at L, 48.8 s at 466 MB, paid once because every consumer sees it
as a sealed constant. The whole name apparatus over the constructible ground
elaborates in 1.55 s at 536 MB.

The sources are in a temporary compile root and are archived at
`~/Agentic/bedrock-proofs-archive/k3/` together with the architecture, the K0
sources recovered byte-exact from the record documents, and K1 and K2. `/tmp` does
not survive a reboot on this machine and two worktrees were lost that way.
