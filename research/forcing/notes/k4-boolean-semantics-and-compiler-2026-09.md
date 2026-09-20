# K4 Boolean atomic values, the fixed-formula compiler, and the witness contract

Date: 2026-09-12. Source baseline: `cbd1510e`. Status: K4 COMPLETE. Eleven proof
tracks, eighteen files, 11869 lines, every one at exit 0 under `--safe`. The
terminology track is blocked on an owner ruling and blocks no code; see section 7b. This record follows the K0, K1, K2 and K3 convention: proof work lives
in a task-specific temporary compile root, with the sources archived outside it,
and no repository source file is changed.

## 1. What K4 delivers

The roadmap's K4 is the Boolean semantics and the internal compiler
(`cohen-implementation-roadmap-2026-09.md` section 5). Fourteen files:

| File | Track | What | Lines | SHA-256 prefix |
|---|---|---|---|---|
| `Algebra.agda` | A | the Boolean algebra records, copied field for field from K2 | 170 | `8e939d500e0e087c` |
| `Implication.agda` | A | the implication and its adjunction | 372 | `46a7fdb37beca000` |
| `Infinitary.agda` | A | the infinitary calculus, carrying the refutation of section 1.2 | 279 | `e815d1ac88cc520f` |
| `ValueSets.agda` | B | attained value sets, admission and bound independence | 780 | `6bb3061cdb22a1e8` |
| `Atomic.agda` | C | the two Boolean atomic values | 628 | `9344bd47afe1d532` |
| `AtomicLaws.agda` | D | Bell 1.17 and 1.18 | 780 | `f83f2a705e753a22` |
| `SubalgebraAgreement.agda` | D | Bell 1.20 and the atomic half of 1.21 | 550 | `edd0ba7f81bb5ac6` |
| `AtomicGraph.agda` | E | the atomic graph contract | 720 | `e4c23d366d8e46a2` |
| `Compile.agda` | F | the fixed-formula compiler and its correctness | 1548 | `09ffb9a6cf6532a5` |
| `Substitution.agda` | G | Bell 1.17(vii), the substitution calculus | 780 | `dbd614403cde1534` |
| `CheckValues.agda` | H | Bell 1.23, the check-name values | 1352 | `26cd55e9ff5d9173` |
| `Witnesses.agda` | I | mixing, unique existence, and the fullness contract | 1093 | `25b84b748f50a6e9` |
| `AdequateExists.agda` | I | the adequate domain, built rather than chosen | 429 | `9fa2972049094969` |
| `HostSemantics.agda` | J | the host reference semantics and the conditional agreement | 1356 | `34aee1151014414f` |

The architecture that produced these is `/tmp/bedrock-k4-architecture.md`, also
archived. It was never compiled, which was the same deliberate trade K2 and K3
made: a design phase that waits for the two Agda process slots serializes behind
the previous package. Section 4 is the cost of that trade, and it was paid in
measured refutations rather than in silent errors.

## 2. The two constraints K4 exists to respect, and how they are enforced

### No internal global truth-value function

Bell page 24 forbids a truth-value function on all formulas of the ground's own
universe, and the roadmap repeats it. For each FIXED input formula the compiler's
output is interpreted inside the ground, and agreement with the host evaluator is
conditional on both admitting the relevant families. The non-claims are source
prose beside the signatures they constrain, on K3's model.

The compiler track found a second, deeper reason for the design that carries this
constraint. The rule that every value fact is stated as a UNIVERSAL PROPERTY
rather than as an equation naming a constructed join was introduced for
elaboration cost. Its real justification is that A UNIVERSAL PROPERTY IN AN
INTERNAL ORDER IS INTERNALLY EXPRESSIBLE AND A CONSTRUCTION IS NOT. That is why
the compiler's whole internal vocabulary reduces to one atomic formula plus
bounded quantification with all eleven of its readings by reflexivity, and why
the repair for the existential node REMOVED a parameter rather than adding one. A
track that states a value fact as an equation is not merely risking a slow
elaboration; it is writing something the ground cannot say.

### The maximum principle is not K4's to export

The maximum principle uniformly over all complete Boolean algebras is equivalent
to the axiom of choice. The witness track defends that boundary and the defence
is a ledger fact rather than a theorem: NOT ONE FIELD OF THE COMPLETENESS RECORD
IS PROJECTED ANYWHERE IN THAT FILE. Measured over its code lines, every
completeness name is absent. So Boolean completeness is not merely insufficient
for the maximum principle; it is not even used by the two theorems the principle
generalizes.

The boundary is typechecker-enforced. Six record constructions occur in that file
and not one produces a contract record from the algebra records alone. A later
package wanting the maximum principle must inhabit a contract with TWO fields,
deliberately separated because only one is choice: forming the mixture of a coded
family is ground machinery and is NOT choice, while producing a coherent family
whose weights lie below the values and whose join is the existential's value IS
choice, and is Bell's own enumeration step. The architecture predicted that a
later package reading Bell would find the maximum principle in its source proof
and ask K4 for it; the answer is no, it is written into the file header with its
reason, and the repair is named. A package that MERGES those two fields loses the
only thing the track exists to record: which half costs choice.

## 3. Four statements of the architecture refuted, not repaired

Each was transcribed into a file under its own name and shown false or shown not
to elaborate, at exit 0. This is the package's default response to a suspect
statement, and it was adopted after a coordinator repair earlier in the programme
turned an ill-formed hypothesis into a well-typed FALSE theorem and had to be
refuted by a later track.

The infimum residual law collapses the algebra. At an empty family the infimum is
the top, so the hypothesis is vacuous and the law yields an arbitrary order fact,
hence that top and bottom coincide. The premise is real: the coded completion
does build an empty coded subset. Bell's identity is a SUPREMUM statement and the
operator had been swapped. Three repairs ship and the genuine dual is named as
the default.

The total value-set constructor is refuted on quantifier order: the environment is
fixed before the host function, so the set cannot vary while the class does. A
per-argument version ships, which is what a recursion consumes.

The existential node cannot be built from the coded supremum vocabulary, because
that vocabulary carries slots for a condition carrier and a refinement order and
the compiler has neither. The repair is the architecture's own English read as an
order statement, and it removes a parameter.

Bell 1.23(ii) as printed is FALSE, unconditionally stated in both section 1.9 and
the exit checklist. At an algebra whose top and bottom coincide the membership
clause proves that every set is a member of every set. K4 nowhere assumes
nontriviality and K2's nontriviality record is a field of none of the algebra
records. Both equivalences now live inside a module taking excluded middle AND
nontriviality, and excluded middle cannot be confined to one clause because Bell's
proof is one induction with three mutually consuming clauses.

## 4. What the tracks measured that the architecture could not know

### The permitted-hypothesis lists, wrong in both directions

Five tracks reported an over-stated list: the atomic laws use no completeness
field in eleven of thirteen cases; the substitution calculus needs no
completeness at all; the witness track projects none; the check values carry a
completeness parameter of which not one field is projected; and the adequate
domain needs no power set. One track reported the opposite: it took TEN
hypotheses its list does not grant, and the cause is structural rather than an
oversight. In the atomic layer the support and the weight are BARE OPERATIONS
WITH NO LAW, so every atomic law is stated about whatever they happen to be.
Bell 1.23(i) is the first statement in the package that needs to know what they
ARE at one particular name, and nothing bridges a name's membership
specification to a separation over a double union without the entry-level laws.
The rule that follows: derive a track's hypotheses from what the atomic layer
actually EXPORTS whenever the track must compute a support or a weight at a named
object rather than reason about an arbitrary one.

### The universe default was wrong three times out of three

Three tracks independently measured a record at the carrier's level where the
architecture printed one level up. A record rises only if a FIELD is a path in
the truth-value type; if none is, it stays down and can therefore index a join,
which is the difference that matters. In one case the printed level would have
made a truncation over the record fail to typecheck.

### A measurement confound that nearly entered the record as a finding

Agda's interface cache is KEYED ON WARNING OPTIONS, so alternating the strict and
plain invocations rebuilds the whole dependency chain. One track measured the same
file at 15.78 s across that boundary and 1.28 s under one option set, bisected
over the confounded numbers, and appeared to find a single declaration costing
14.5 s, which would have been a spectacular instance of the elaboration rule.
Re-measured under one option set the two forms differ by noise. The rule now
stands in the shared preamble: take timings under one option set and say which,
and never bisect across the boundary. A later track reproduced the confound
independently and RETRACTED a figure it had already reported.

### An elaboration rule, and its boundary

A declaration, not a term, can fail to elaborate in bounded time when its TYPE
names a construction of one layer applied to a term of another. The compiler
track's earlier package measured kills at nineteen and eleven minutes; a K4 track
reproduced the shape at a new site with a kill at a 360 second wall, located by
ten probes. But another track BOUNDED the rule by deliberately placing a supremum
on a projection out of a constructed record, which elaborated in 0.72 s. So the
rule concerns naming a constructed join in a type, not projections, and a later
track should not contort around the bounded case.

### Inferring a formula from a value: a blanket instruction became a criterion

One track measured that applying a connective law without its formulas explicit
leaves an unsolved constraint blocked on the formula metavariable, and handed that
forward as an instruction. The next track ran the same control in its own file and
got exit 0. The difference is structural: in the first the value is a DEFINED
recursive function whose clauses cannot be inverted, in the second a MODULE
PARAMETER, that is a variable, so unification solves the formula at once. The rule
is therefore a criterion about which of the two a law applies, not an instruction
to write formulas out, though writing them out costs nothing and reads better.

### Negative controls, and where scoping stops helping

A reading theorem proved by reflexivity is worthless if the formula and the host
predicate are wrong together. Four tracks ran deliberate breaks and between them
separated the failure modes: exchanging key arguments fails in a finite-index
type, a well-scoped wrong slot fails in the carrier type, and a PURE OFF-BY-ONE
is caught by intrinsic scoping before any reading is reached. The consequence: a
track writing formulas AT UNIFORM DEPTH gets no protection from scoping and all
of it from the readings.

### What Bell leaves to the reader

Bell's proof of 1.17(vii) is the sentence that it is a straightforward induction
left to the reader. Three things that sentence omits, and the third fixes the
shape of the file: the statement must be SIMULTANEOUS IN BOTH ENVIRONMENTS,
because the implication node is antitone in its antecedent, so the inductive
hypothesis must be read at the swapped pair. Measured: that is the only clause
that needs it. This belongs beside 1.17(vii) wherever the project records its
reading of the source.

Bell's proof of 1.23(ii) is likewise left to the reader as tedious but
straightforward. Three of those details are design decisions, and the first is
that a biconditional is not enough: a join of Boolean values is the top only if
some member is, which fails in a general Boolean algebra, so the induction must
carry TWO-VALUEDNESS as data rather than as a proposition.

### One accounting that was audited rather than accumulated

The symmetry of Boolean equality is proved with NO infinitary law, only the
commutativity of meet, because under the expanded symmetric equation the two
image sets are the same operation applied to families equal pointwise. The
architecture had feared they were different constructions and had parked symmetry
behind the residuation group as an open item. Four later results each needed a
second induction without it: transitivity, Bell 1.16, the subalgebra agreement,
and the third clause of 1.23(ii). A fifth track examined its own use, found it
needed only an inequality it could prove for itself, SHIPPED THE UNUSED
ALTERNATIVE SO THE LEDGER CLAIM WOULD BE CHECKABLE, and declined to count itself.

## 5. A ruling, and a cross-track constraint satisfied before it was raised

Bell Theorem 1.20 and the atomic half of Corollary 1.21 had no settled owner: K2's
exit checklist assigns the complete-subalgebra agreement to K6 while the
mathematics is a simultaneous induction on the ATOMIC values in two algebras, which
is K4's machinery and exists nowhere else. THE COORDINATOR RULED THAT K4 OWNS
1.20 AND THE ATOMIC HALF OF 1.21 AND K6 KEEPS THE CONSEQUENCES, because K4 not
proving it means K6 rebuilds the induction and the roadmap forbids exactly that,
and because K2's own constraint is that a complete-subalgebra inclusion receives
the JUSTIFIED atomic and bounded-formula agreement, whose justification is atomic.
The ruling arrived after that track was briefed, which was a coordinator failure
and is recorded as one. The induction then needed nothing the atomic layer does
not have.

The host semantics track later derived a constraint on that theorem: stated over a
constructed supremum it would not discharge the agreement's hard half, while over
an abstract family with a coded least upper bound it would. The constraint was
already satisfied, because the theorem had been stated as a universal-property
transfer for an unrelated reason, namely the architecture's own rule. That is the
third independent payoff of the universal-property rule, after elaboration cost
and internal expressibility.

## 6. Two obstructions, unchanged and named

The atomic graph has no discharge at any ground. The contract can be STATED,
which was the thing that might have failed, and the implication from a value table
to a graph is proved; general-ground portability stands where K0 left it. Every
correctness statement of the compiler is conditional on it.

The agreement between the coded and host semantics is conditional, by design and
by the roadmap's own sentence. The host semantics track re-scoped the measurement
that was planned to close it: the hypotheses as the architecture states them reach
only one of the six sites where they are actually spent, because the coded
equality value is a greatest lower bound over a sum of supports and the four
compiler quantifier nodes are indexed by names rather than by a ground code, which
they cannot be. It also halved the remaining work by proving that one direction of
each hypothesis is free, leaving a hard half that is complete-subalgebra-ness for
that family, which is the theorem of section 5.

## 7. The instance track, and a third elaboration threshold

The instance track discharged two of its four obligations, returned one as a
measured negative with BOTH bounds proved, and reported one blocked with three
independent open inputs named. Four files, 1032 lines, all at exit 0. The heap
risk the architecture predicted did not materialise: the largest peak is 805 MB
against an 8 GB ceiling, because each of its files applies AT MOST ONE heavy
module. That is the third independent confirmation of the rule to budget heap by
module applications rather than by line count.

### A third threshold, isolated to the exact depth

What did bite is orthogonal to the heap and was invisible to every earlier
measurement in the programme: a TIME wall at a flat 940 MB of resident set. An
agent watching only memory would have concluded nothing was wrong.

A DECLARATION WHOSE TYPE NESTS TWO OPERATIONS OF AN UNSEALED CODED ALGEBRA DOES
NOT ELABORATE. Depth one costs nothing. Sixteen probes separate the passing rows
from the failing ones and rule out every other explanation: it is not the
complement, because a nested meet fails exactly as a meet with a complement does;
it is not the reading map, because a statement containing none fails the same way
while the reading OF the same composite is free; it is not the truth-value form,
because the entailment form fails exactly as the path form does; and it is not
terms, because a depth-two TERM elaborates in under a second. The one number that
separates every passing row from every failing row is the nesting depth inside a
declaration's type, and the boundary sits between one and two.

This is NOT the elaboration rule of section 4 as that rule is stated, AND ITS
REMEDY DOES NOT WORK: both probes that abstracted the composite into a variable
were killed. The reason is that the general lemma elaborates instantly and what
does not elaborate is SUPPLYING the composite as an argument, so there is no
caller left to push the problem to. K2 met the same wall from the other side and
recorded it in its own source, and K2's remedy worked there only because K2 never
had to state a law AT the composite. A K4 law is exactly that.

THE REPAIR is the sealing rule applied on the K4 side to objects K2 left
transparent. The coded completion contains no seal at all, so every coded
operation is an unsealed description-operator term whose nesting puts one
description operator inside the syntax of another. Sealing each operation in its
OWN block, and opening each alone, makes the inner argument of a nest neutral.
Measured, one change and nothing else: no finish in 200 seconds unsealed against
1.38 seconds sealed. That is the third independent reproduction of the sealing
rule in this programme, after 761 seconds against 1.04, and 420 seconds against
3.96. Separate blocks are load bearing: one block holding all five operations
would be useless, because opening it to unfold the meet would also unfold the
complement.

The handoff is named and is not actioned here: the right home for these seals is
the coded completion itself, one block per operation with its membership
specification, on the model of the weight in K3. Sealing there would remove the
wall for every later package at once.

### The measured negative, with both bounds proved rather than asserted

The value-set contract at the constructible structure is OPEN, and the track
refused to report it open on an asserted bridge. Two earlier results bounded it
from opposite sides: one track measured that only the image route can discharge
the total contract, and K3 proved the image tier at L equivalent to a form of V
equals L for the ambient theory. But one is about a contract and the other about
a tier, and their inter-derivability had been asserted rather than checked. So
this track proved the lower bound itself: the contract plus excluded middle
implies that every ambient truth-valued class holding somewhere in the algebra
carves a set out of it, with no formula, no complexity bound and no definability
assumed. With the upper bound and the application at L, the contract and the
relevant half of the tier are now inter-derivable at L, machine checked, with no
gap between them in which to look for a discharge.

What L DOES supply is the positive half and it says where a successor should
spend effort: the graph route at L has both its axioms discharged, Separation and
Collection, so the remaining gap is ONE FORMULA PER STEP rather than two axioms
and a datum. That is the same obligation K3 handed forward for the check name,
the generic name and both translations. A successor should plan for definable
graphs from the start rather than look for a value-set construction.

The fourth obligation, the atomic graph at L, is blocked through the third and on
two further inputs that are independently open: there is no forcing notion inside
L and therefore no concrete coded algebra there, which the roadmap places at K8
and K9; and K0's archived atomic-graph instance is stated over a different
algebra and a different value relation, so it cannot be applied. The archived
sources and their hashes are named so a successor can restore them the moment the
first two move. The track did not restore them, because restoring them would have
measured nothing.

## 7b. Terminology

The terminology track is blocked on an owner ruling and blocks no code. The
Chinese rendering ruled for one term on 2026-08-03 is the standard rendering for
the compatibility of forcing conditions, and parallel authors may not resolve
that.

## 7c. A gap in the acceptance instances, found three packages later

K5's refutation track found that NO ATOMLESS FORCING NOTION EXISTED ANYWHERE in
K1 through K4. K2's three acceptance instances are a two-condition presentation,
a four-condition one and a one-point one. The consequence is that K2's own
theorem forbidding a host-generic filter was an implication WHOSE HYPOTHESIS HAD
NEVER BEEN WITNESSED, and the existence of a host-generic filter had never been
refuted anywhere in the programme.

That track supplied the missing notion: the binary tree of finite two-valued
strings under extension, with its carrier's set-ness proved by retraction into a
list type and its order written by recursion on both arguments so that it is a
truth value by construction rather than by a propositionality lemma.
Atomlessness is proved constructively. The degenerate-case tables of the K3 and
K4 checklists should gain a row for it; they currently cover the empty notion,
the one-point poset, the two-element algebra and the degenerate algebra, and an
atomless notion is the case those four cannot exercise.

The same track settled an architecture correction the strong way. K5's
architecture had told it that a two-element antichain does not refute the naive
disjunction clause and had corrected a designer who proposed it. Rather than
accept that, the track PROVED that at the antichain both naive clauses are
THEOREMS, so the proposal was not merely inconclusive: it named a notion at which
the statement is true. It also found the architecture's own reason for the
correction to be non-constructive, because the pseudocomplement calculus yields a
double negation there and stripping it costs excluded middle, and it carries that
hypothesis explicitly with a deliberate break confirming where it is spent.

## 8. A coordinator failure worth recording

The K4 compile root holds COPIES of the K1, K2 and K3 deliverables rather than
including those roots on its path. The isolation is deliberate: an upstream change
cannot break K4 mid-flight. The cost is that an upstream CORRECTION does not reach
K4 either, and nothing reports it, because the copy is self-consistent. When K3
gained four new exports late, the K4 copy went stale and the staleness was found
only because one track happened to need one of the new lemmas. That track did not
silently fix it: it measured exactly what the stale copy still provided, took the
missing lemma as a parameter typed verbatim from the new export so a drift would
fail in its probe, and handed the decision back. A full audit then found that one
file stale and every other copy fresh; it was refreshed and its consumers
rechecked at exit 0.

## 9. Validation

Every file checked at exit 0 with `GHCRTS="-A64m -I0 -M8g" agda <file>`, most
additionally under the strict warning option, and no timing figure in any report
crosses that boundary. No postulate, no pragma, no hole, no unsolved metavariable
in any of the fourteen. Several tracks elaborated on the first attempt; the two
compiles lost in the package were both lost to a local name colliding with a
builtin, and the running list for later briefs is lower, lift, fst, zero, suc.

The heaviest measurements, all under one option set: the compiler at 6.75 s, the
check values at 6.43 s of which the formula layer is 3.5 s, the host semantics at
9.78 s and 1.08 GB. The probes cost far more than the deliverables and the reason
is measured: BUDGET HEAP BY MODULE APPLICATIONS, NOT BY LINE COUNT. One probe at
314 lines cost 3.30 GB where a deliverable at 1356 lines cost 1.08 GB, and another
applying four modules in one file reached 2.68 GB against an 8 GB ceiling.

The sources are archived at `~/Agentic/bedrock-proofs-archive/k4/` with the
architecture and the reports, alongside K0 recovered byte-exact from the record
documents, K1, K2 and K3. The temporary root does not survive a reboot and two
worktrees were lost that way earlier in the programme.
