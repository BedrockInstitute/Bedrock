# LESSONS.md: the measured lesson book

The living home for every measured law and recorded lesson this project has paid
for: performance laws, conversion rules, termination traps, inference traps, and
the design doctrines that keep recurring. Developer doc, English only, written
for agent readers: explicit structure over narrative, every entry traceable to
its source, no entry without its numbers.

`dev/PLAN.md` is the goal-history registry: what was ruled, when, with what
outcome. This file is where the substance of those rows lives. A chapter that
needs a countermeasure carries a `-- perf:` marker naming the entry here. A
lesson lands only when it has a source (a memo, a PLAN row, a probe report, or a
commit) and a measurement where one exists; nothing here is guessed.

## Entry format and IDs

Each entry gives: the ID, a one-line rule, the measured evidence (the numbers),
the provenance pointer (memo, PLAN row, report, or commit), and when it bites.

- **P series**: performance laws (P-a onward, continuing the numbering recorded
  in `dev/memos/L3.28-ac-route.md` §9).
- **R series**: conversion rules (rules 1 to 20 as recorded in PLAN, then R-21
  onward for the recorded laws the PLAN never numbered; the source numbering has
  gaps: rules 7, 17, 18 and 19 never appear in the record).
- **T series**: termination traps.
- **I series**: inference traps.
- **D series**: design doctrines.
- **C series**: craft and process lessons.

## 1. Performance laws (P series)

### P-a. Tag discrimination through helpers with explicit-data numeral indices

**Rule:** Discriminate tags through helpers whose numeral indices are explicit
data; never let unification meet a literal numeral under `#`.

**Measured:** an absurd clause headed `snotz ∘ injSuc` with `#-inj′`'s implicits
left to inference ran 252 s and failed with unsolved metas (constraint-order
luck: the `znots`-headed siblings happened to solve); through generic
`tagNe`/`payNe` helpers with explicit indices, the same 16-clause induction sits
in a 3.5 s module. The M4 build dodged the trap twice more: the membership
laws' implicits passed explicitly at `L.Godel.InL` (first attempt green, 168
lines, 1.2 s).

**Provenance:** `dev/memos/L3.28-ac-route.md` §9 (from probe P2);
`dev/PLAN.md` §11 rows L3.29 (M1, M4) and L3.22.

**When it bites:** clause dispatch, tag matching, and any code equation under a
literal numeral; the first symptom is unsolved metas whose fate depends on
sibling order.

### P-b. Union-free operation definitions

**Rule:** The operations calculus must be union-free at the definition level:
each operation is one direct `sett` (sum-typed index); `∪`/`⋃` may appear in
composition terms but never under a membership proof obligation.

**Measured:** written as a singleton-∪-shift, one lemma did not finish in six
minutes and drove the checker past 30 GB; as a direct `sett`, 7 s. This law
binds the closure-step chapter too.

**Provenance:** `dev/memos/L3.28-ac-route.md` §9 (from probe P1);
`dev/PLAN.md` §11 row L3.29.

**When it bites:** defining set operations; the moment a membership obligation
mentions `⋃`.

### P-c. Seal `⋃`-tower indices opaque at birth

**Rule:** An operation whose index carries a `⋃`-tower is sealed `opaque` at its
birth site.

**Measured (four-way bisect, mechanism corrected the same day):** the shift
equation at bare hierarchy values ran 446 s with the operation's head open, and
neither locality (a verbatim same-module transplant, 446 s) nor law P-a's
helpers changed it; the identical proof at carrier-valued assignments checked in
1.1 s, which first suggested the value domain; then the existential satisfaction
case, carrier-valued throughout, ran 250 s against the same open head, refuting
that reading; with `tailGraph` sealed at its birth site, both the existential
case (3 s) and the bare-hierarchy shift equation (1.0 s) collapsed at once.
Mechanism: the `⋃`-tower in the index re-normalizes at every concrete set former
it meets downstream. Carrier-valued statements stay as the API (every consumer
arrives carrier-valued) but are not load-bearing for performance.

**Provenance:** `dev/memos/L3.28-ac-route.md` §9; `dev/PLAN.md` §11 row L3.29.

**When it bites:** any operation whose index cannot avoid a `⋃`-tower; the seal
replaces union-freedom one level up.

### P-d. Reductions travel as direction pairs, never as hProp paths

**Rule:** A pointwise semantic reduction travels as a pair of directions, never
as an hProp path.

**Measured (eight-step bisect, 2026-08-01):** building the `⇔toPath` path
between the satisfactions of two fully concrete formulas ran 386 s for one atom
shape, while its two directions cost under 2 s each; with the respect lemma's
hypotheses restated as the two directions, the whole batch (the exceptional
atom, five constant-atom reductions, both bounded-quantifier reductions, the
classical cases re-adapted) checks in 1.9 s. Semi-concrete formulas with
variable leaves never paid (the classical cases were 17 ms as paths), so the
hazard is the path former at concrete leaves. Named continuations with spelled
payloads remain necessary but were not sufficient.

**Provenance:** `dev/memos/L3.28-ac-route.md` §9; `dev/PLAN.md` §11 rows L3.29
(M2, M4).

**When it bites:** any path or equivalence between satisfactions of concrete
formulas, and any successor-clause equation in the same wall class (see the B
pivot memo's open risks).

### P-e. Presentation-parameterized data types at abstract type parameters

**Rule:** A data type whose constructors mention a module parameter's
presentation type is declared at an abstract type parameter and applied, never
inside the parameterized module.

**Measured:** the composition-term syntax with `param : ⟪ A ⟫ → GT` inside the
carrier module spent 345.5 s in the positivity checker alone (the
definition-level profile showed every definition under 200 ms; the internal
profile attributed the whole cost to Positivity, which normalizes the
presentation); declared as `GT (P : Type ℓ)` at top level and applied at
`⟪ A ⟫`, the whole chapter checks in 1.4 s, a 250x collapse from moving one
declaration.

**Provenance:** `dev/memos/L3.28-ac-route.md` §9 (found 2026-08-01 at the
normal-form chapter); `dev/PLAN.md` §11 row L3.29 (M2).

**When it bites:** inductive syntax over a carrier or presentation type inside a
parameterized module.

### P-f. Dependent transports restated as path lambdas under one non-dependent subst

**Rule:** A dependent transport over a sigma motive at concrete towers is
restated as a path lambda under one non-dependent substitution.

**Measured:** stating "the term's own entry is in its approximation" by `subst`
along the arity-packed subterm equation, with the code and the denotation in the
motive, ran past 300 s (the cubical `transp` computes the motive structure
rather than treating the hProp as a black box); the same content as one
congruence path lambda `λ ι → pr (code (p ι)) (denote (p ι))` composed into a
single value-level `subst` is instant.

**Provenance:** `dev/memos/L3.28-ac-route.md` §9 (found 2026-08-01 at the table
chapter's self-membership lemma); `dev/PLAN.md` §11 row L3.29 (M4c).

**When it bites:** self-membership and similar lemmas at concrete towers;
generalizes P-d one step: not only path formers but transports must stay
non-dependent at concrete towers.

### P-g. No `cong` with a function lambda at concrete presentation-carrying types

**Rule:** At concrete presentation-carrying types, `cong` with a function lambda
hangs; the cure is writing the path lambda directly.

**Measured (M5a, 2026-08-01):** the first formulation of the graft retraction
used `cong (λ p → …)` (even with a plain non-pattern lambda) and `subst` over an
equality motive; it ran past 6 minutes for the file, well over the 180 s
per-definition tripwire, while the identical code over an abstract `X : Type ℓ`
checked in under a second. Replacing every such step with a direct path lambda
(`λ ι → let p = … ι in …`) made the whole file check in ≈1.7 s.

**Provenance:** `_build/m5a-report.md` Surprises 1 (the M5a re-cut, committed as
`9539088`); PLAN row L3.29 M5a (see the landing record added by the doc surgery).

**When it bites:** goals whose values carry `⟪ A ⟫` (presentation) types; a new
data point alongside P-d/P-f: at concrete towers the path former should be
written directly, not through `cong` with a function whose domain carries the
presentation type.

### P-h. Definability walks are module-parameterized, never function-parameterized

**Rule:** A definability walk (the `defSet≡` extensionality of an InL-idiom
constructibility lemma) takes its set arguments as parameters of a module, not
of a function, and those parameters stay ABSTRACT through the walk: the
formulas and the readers never mention a concrete `sett` body (`slice`,
`satSet`, a stage over them); the instantiation at real sets happens only at
the lemma-assembly level, where memberships and equations flow but nothing
unfolds.

**Measured (B4d, 2026-08-02):** the values-image walk formulated as
`valsWalk : (X : V ℓ) → ...` ran past 4 minutes cold and never finished;
restating it as `module ValsWalk (X : V ℓ) ... where` dropped the whole file to
~13 s. The bridge chapter's Vals/SelMem modules were already
module-parameterized; the mechanism now has a measurement.

**Measured (B4e, 2026-08-02):** the abstractness half confirmed: the selection
walk whose environment reached concrete shelf bodies (B4d's wall) exceeded
4 minutes cold and never finished; restated over abstract shelves, keys, and
stage (`SelWalk`/`SelEWalk`), the whole file checks in ~30 s cold and the two
selection images assemble at the real shelves with nothing unfolding.
Notably, the isolated machinery did NOT reproduce the wall in any standalone
parameterization; only the real-file context did, so bisects for this class
must run in situ (B4e report, sections 1-2 and 7).

**Provenance:** the B4d batch record (PLAN row L3.29 ledger) and the B4d
report's failure 1; the sibling abstractness hypothesis confirmed by the final
B batch (B4e report, the headline probe).

### P-i. The conversion-explosion playbook (imported from the source project)

**Rule:** When cubical Agda hangs or exhausts memory on this codebase family,
the cause is one of three heavy-thing classes forced into normalization, and
the cure is selected by the decision tree below, not by trial. Imported whole
from the antecedent development's worklog (`../fol-reification/docs/WORKLOG.md`
§5, twenty measured cases); read that section before any surgery on a hang.

**The three heavy-thing classes (root cause):** (1) membership in a heavy set
(`sett`, `Def`/`defSet`, `⋃`, `sucV`, `# n`, `Lset`, `pr`, `⁅⁆`-pairs), value
equalities between heavy sets, and hProp-pair head shapes; (2) heavy HIT-types
transported along paths (`Σ≡Prop`/`subst` carrying `⟨isL x⟩`-class types);
(3) heavy operators welded into a FIELD or obligation TYPE and applied to deep
recursive terms (stuck `℩(mere→isContr)` heads). Abstract parameters and deep
recursion multiply all three.

**The repair taxonomy** (letters as in the source; Bedrock correspondences in
parentheses):

- **[F] Explicit indices first, one line**: a lemma with an implicit formula
  or code index applied at a concrete huge argument must get the index
  explicitly; a left metavariable makes the unifier normalize the huge
  instance under a type-level FUNCTION head, which is not invertible
  (source case 16: 74 min to 69 s). (Extends P-a, Rule 12, I-1; the sharper
  mechanism statement is the type-level-function-head unification.)
- **[A] Keep it neutral**: heavy values never sit inside
  `extensionalV`/`Σ≡Prop`/conversion positions; use stuck terms or variables
  and bridge the concrete membership by one `subst`. (Extends Rule 1.)
- **[B] Seal the operator or the set** `opaque` at its birth site; where the
  set itself is the heavy thing, seal the SET, not just a bridge. (Extends
  Rule 2 and P-c.) **Layer cap sub-rule** (source case 12): any tower of two
  or more `Lset ∘ sucV` layers gets one independent opaque alias PER LAYER,
  so conversion unfolds at most one; costs multiply per exposed layer.
  **[B′] Seal terminal exports** (source case 17, NEW here): when a
  consumer's profile shows OTHER modules' definition names, the consumer is
  re-normalizing imported proof bodies; seal the terminal theorems at the
  definition side (consumers need types, not bodies). Measured 662 s to
  153 s.
- **[C] Extract helpers with variable parameters**: where-bound heavy heads
  are inlined past `opaque`; make the heavy datum an explicit helper
  parameter, `with` becomes `Sum.rec`/`decide`, truncation continuations
  become named helpers. (Extends Rule 10 and the named-continuation
  discipline.) **[C′] Grid dispatcher** (source case 19, NEW here): a
  coverage grid whose every clause carries a huge goal type pays a fixed
  per-clause elasticity cost regardless of body; move the grid to a cheap
  codomain (a small inductive view plus a dispatcher on explicit `Tri`
  arguments, never `with`). Measured 486 s to 120 s.
- **[D] Lower the dimension** (NEW here as an explicit pattern; P-f is its
  cousin): when the heavy thing is a HIT-TYPE being transported, `opaque` is
  useless; construct the path at a lower level whose motive does not mention
  the heavy type (drop to V-satisfaction, transport along the light
  `fst`-path, lift back).
- **[E] Reshape the obligation** (NEW here): when the heavy operator is
  welded into the TYPE of a field or proof obligation and applied to a deep
  term, `opaque`/`abstract` cannot help (the type still mentions it) and
  rewriting is illegal under `--safe`; the only cure is changing the
  upstream interface so the obligation never applies the heavy operator to
  the deep term (the von Neumann membership-extensional characterization
  replacing welded successor equations is the paradigm). Warning from the
  source: merely rewriting the equation MOVES the explosion; the replacement
  obligation must not mention the heavy operator at all.
- **Record discipline** (source cases 13 and 14, NEW here): heavy hypothesis
  packs go as module Π-parameters, never `record`s (cubical derives
  transp/hcomp machinery per record, and twelve heavy fields hang the
  DECLARATION); record field types, especially ∈-families and path
  endpoints, must not contain any expanding concrete code term, not even one
  `sucV` layer; alias such heads opaque first. Measured: a six-hour file to
  20 s.

**Diagnostics** (source §5.2): bisect by `postulate` (faster than holing);
kill-timers, `pkill` stuck agda; an OOM hard cap `GHCRTS="-M20g"` turns OS
death into a clean heap-exhausted exit; cold-check attribution inflates 2-4x
under system-state residue, so isolate-recompile before and after surgery;
beware false greens from unsolved implicit metas and warm `.agdai` caches
(extends C-8). Consumer-side versus definition-side disease is read off the
profile's module names.

**Provenance:** the source project's worklog, `../fol-reification/docs/WORKLOG.md`
§5 (the playbook, the twenty-case table §5.4, and the decision tree §5.5),
integrated 2026-08-02 by owner direction. The walk-transparency hypothesis
under test in the final B batch is this playbook's case-12/case-20 family
(transparent shared heavy objects at `Lset`-argument positions) meeting the
B4d walk lesson (P-h).

## 2. Conversion rules (R series)

Recorded in PLAN as "rules" with the numbers below; the numbering is the
recorded one (gaps at 7, 17, 18, 19). R-21 onward are recorded laws the PLAN
never numbered. Every one is measured.

### Rule 1. Discharge adequacy substitutions at variable arguments

**Rule:** Discharge an adequacy substitution at a *variable* argument, never at
a concrete one.

**Measured:** [L3.21] decode 2,237 s to 1.5 s via variable restatement; [L2.4]
Limit's level inlined at its six sites cost 144.55 s, as a variable with its
defining equation 1.76 s (82x); [L3.23] a value stated at a named key ran past
400 s twice, and as a one-line corollary of the variable-argument version checks
in 4.6 s.

**Provenance:** PLAN §11 rows L3.0.1 (five walls), L3.21, L2.4, L3.23.

**When it bites:** any proof step whose expensive term sits under a concrete
argument; see R-30 for the boundary with rule 2.

### Rule 2. Seal a construction `opaque` at the site where it is built

**Rule:** Seal a construction with `opaque` at the site where it is built, and a
module application is such a site.

**Measured:** one `opaque` block around four numerals and their projections took
the `FOL.Coding` module application from over 600 s to 0.3 s; sealing
`isL-Lset` took `L.Axioms.Full` from over 600 s to 1.4 s (259 ms with the
sharpest single factor, at least 2,300x); sealing `rank`/`rank-compute` took
`[L3.21]`'s chain from 164 s to 1.4 s.

**Provenance:** PLAN §11 rows L3.0.1, L2.2 finding, L3.21, L2.4.

**When it bites:** a construction appearing in a goal or a type, and especially
when instantiating a chapter; sealing the reflected ordinal first did nothing,
the certificate travelling with it was the problem (see R-29).

### Rule 3. Compute one side of a two-indexed case analysis from the tag

**Rule:** Compute one side of a two-indexed case analysis from the tag rather
than matching both.

**Measured:** 96 → 12, 144 → 12, 150-200 → 21 across `byTag`, `⌜⌝-inj`
(`tagOf`/`payOf`/`shape`/`Match`/`matches`) and the value-carrying tag dispatch;
the 132 off-diagonal `clash` cases are never written at all.

**Provenance:** PLAN §11 rows L3.0.1, L3.20, L3.22.

**When it bites:** grids indexed by two things a tag already relates (twelve
constructors against eight demands, twelve-by-twelve dispatch).

### Rule 4. Transport a statement rather than re-parameterizing its proof

**Rule:** When a statement is invariant under a change that agrees where it
looks, transport the statement rather than re-parameterizing its proof.

**Measured:** `envOverAt-transport` is 41 lines in `L.Coding.Model` at variable
environments throughout, so no conversion risk, and `L.Coding.Sound.Ambient` is
then 20 lines giving both directions for all seven ambient-consuming clauses.

**Provenance:** PLAN §11 row L3.0.1 (U5b); L3.23.

**When it bites:** environment agreement, carrier changes, and any
hypothesis whose vector is a module parameter; the alignment-commits
precedent made `[L3.9]` unnecessary.

### Rule 5. Frames generic in a constructor (or a sentence) take the defining equation as a hypothesis

**Rule:** When a frame is generic in a constructor, hand it the constructor's
defining equation rather than leaving the elaborator to rediscover it under a
stuck term; generalized, a frame generic in a sentence takes that sentence's
equation as a hypothesis.

**Measured:** [L3.21] decode: the frame with its body a hole is 1.3 s, the whole
cost is the equation saying the produced formula's code is the code that was
peeled, fixed by taking the coding equation as a hypothesis and passing `refl`
at the twelve concrete call sites (2,237 s to 1.5 s). `L.Coding.Sequence`
first measured 129.6 s: alias everywhere 108 s, fully concrete with no alias
586 s, the sentence as a parameter with its own equation and `refl` at the one
call site 23.5 s. Related, same family: a propositional equation between two set
constructions is expensive to carry even when it is `refl`, and the maps it
induces are free (did not finish in ten minutes vs 2.4 s).

**Provenance:** PLAN §11 rows L3.21, L3.19 (RULE 9), L3.20.

**When it bites:** frames parameterized over constructors or sentences whose
quotation or satisfaction is stuck; `L.Coding.Slot`'s `payOp` is the standing
precedent.

### Rule 6. Grep what unfolds what you change before estimating

**Rule:** The grep of unfold sites predicts what a change costs its consumers,
and says nothing about what the theorem costs to prove; ask both questions.

**Measured:** it called four goals correctly ([L3.24] three sites, [L3.25] two,
[L3.26] zero across eleven outside consumers), all landing at or under estimate;
but [L3.26] walled at 482 s inside its own proof while every consumer was
untouched.

**Provenance:** PLAN §11 bookkeeping, "Rule 6 has a boundary, found by
[L3.26]".

**When it bites:** any estimate of an index-threading change; a new theorem is
exactly where the grep is silent.

### Rule 8. A `PT.rec` over an object-language existential must name its payload type

**Rule:** A `PT.rec` over an object-language existential must name its payload
type; left to inference, the payload is a metavariable standing for the
satisfaction of a formula the elaborator has not committed to.

**Measured:** consuming an existential with a `PT.rec` whose payload type is left
to inference cost over 140 s; the same two lines with the payload written out
are 2.1 s; the chapter went from 3.2 s to over 600 s and back. Second sighting:
`L.Coding.Uniform`'s totality hypothesis.

**Provenance:** PLAN §11 row L3.27 (RULE 8).

**When it bites:** eliminating object-language existentials, especially in
readers over satisfactions.

### Rule 9. A named alias in a unification position is fatal; the cost is the sentence reducing at concrete slots

**Rule:** Naming data reached from another module, or a named alias in a
unification position, forces the order (or description) to unfold; the cost is
the reduction of the sentence once its slots are concrete.

**Measured:** [L2.4] C2/C3: stating anything about a projection defined in a
different module cost 221 to 225 s, concentrated in trichotomy and the
accessibility steps; defining the same projections in the very module whose
telescope binds the parameter: 2.4 s (local 1.9 s, two submodule openings 221
and 225 s, top-level with the parameter implicit over 400 s). Sequence: a
reading at fully concrete slots is 15 ms, the same reading against a named
closed-sentence alias is 51 s. Its other side: a description read at constants
must be sealed where it is built (two readings 163 s and 160 s, sealed the whole
chapter is 3.5 s).

**Provenance:** PLAN §11 rows L2.4 (C2/C3, faithfulness), L3.19 (RULE 9).

**When it bites:** unification against aliases of order or satisfaction
descriptions; the cure is locality plus a seal, never abstraction alone
(see Rule 13).

### Rule 10. Splits concluding in a membership hProp are named helpers, never `with`

**Rule:** A case split on ordinal trichotomy (or any split into a satisfaction)
whose branches conclude in a membership hProp must be a named helper with its
conclusion written down, never a `with`.

**Measured:** inline, the trichotomy probe did not finish in 90 s and one whole
run was killed at 693 s and 13 GB; the identical three branches in a named
helper are 2 s (45x). Generalizes: a two-way case split into a satisfaction was
killed at 300 s; as a named helper with its conclusion written down, 3.46 s.

**Provenance:** PLAN §11 row L2.4 (route audit RULE 10; faithfulness "Law 10
generalizes").

**When it bites:** any case analysis whose branches conclude in a membership
proposition, in `L.Ordinal.Stages`-shaped chapters and everywhere the order
family is built.

### Rule 11. A data declaration whose constructor mentions the order is fatal

**Rule:** The positivity checker fully normalizes constructor arguments, so a
`data` declaration whose constructor mentions the order is fatal; write it as a
nested sum.

**Measured:** over 180 s and killed, even at variable arguments with no codes
involved; written as a nested sum: 1.3 s. Consequence at the same boundary: the
order at a concrete pair of names is not derivable at all (probes killed at 90
and 100 s; the abstract statement is the only assurance).

**Provenance:** PLAN §11 rows L2.4 (C2/C3, C5).

**When it bites:** data whose constructors mention a well-order or relation.

### Rule 12. An introduction helper with implicit arguments is fatal

**Rule:** An introduction helper with implicit arguments is fatal in a
unification position; write the injection directly.

**Measured:** used in one transitivity clause it cost 84.7 s; writing the
injection directly: 1.2 s. This is rule 9's cousin, a named alias in a
unification position.

**Provenance:** PLAN §11 row L2.4 (C2/C3).

**When it bites:** unification that unfolds the order through an implicit
argument.

### Rule 13. Abstraction is not the cure for non-locality

**Rule:** Module-parameterized recursion values do not cure non-locality; the
cure is locality itself, defining the data in the module whose telescope binds
the parameter.

**Measured:** stating anything about a projection defined in a different module
cost 221 to 225 s; taking the order as a module parameter did not help, measured
at over 400 s while the data was still non-local; defining the projections in
the very module whose telescope binds the parameter: 2.4 s. Rule 2's usual cure
was measured to make no difference once the data was local.

**Provenance:** PLAN §11 row L2.4 (C2/C3); L3.28 lever (f); cited by the
compression audits as the binding constraint on parameterized frames.

**When it bites:** any plan to abstract recursion values or order-carrying data
into a shared module; only the parts whose types do not mention the recursion's
value may move.

### Rule 14. A concrete element at a slot inside a satisfaction must be sealed

**Rule:** A concrete element at a slot inside a satisfaction must be sealed;
corrected: seal the pair carrying the constructibility proof, not just the
underlying set.

**Measured:** 77 s against 1.6 s (isolated: forming the type is free, passing a
variable of that type is free, and only checking a term at it costs). The
correction: unsealed 178 s, sealed 2.0 s; again at four elements of another
reading, past 400 s against 3.5 s.

**Provenance:** PLAN §11 rows L2.4 (C5; faithfulness, "Law 14 was mis-stated").

**When it bites:** law 1's boundary in the case where the argument cannot be a
variable because the description names a fixed object.

### Rule 15. A block of binders must be a frame generic in its body

**Rule:** A block of binders must be a FRAME generic in its body, never packed
with the body inlined.

**Measured:** packing a six-fold existential directly ran past 120 s, because it
puts the whole description into normal form; as a frame with the body a variable
the two readings are one line each and the file is 7.4 s.

**Provenance:** PLAN §11 row L2.4 (C5).

**When it bites:** existential blocks in object-language descriptions; law 5 met
on a block of binders rather than on a constructor or a sentence.

### Rule 16. An environment must be spelled out, never abbreviated

**Rule:** An environment must be spelled out, never abbreviated.

**Measured:** a private abbreviation for a four-element environment cost 207 s
against 2.84 s (73x); the sequence chapter measured the same shape at 15 s per
conversion.

**Provenance:** PLAN §11 row L2.4 (faithfulness).

**When it bites:** any reading whose environment is a concrete abbreviation.

### Rule 20. Composites of adequacy equations are consumed factor by factor

**Rule:** A composite of adequacy equations is consumed factor by factor, never
as a composite.

**Measured:** `L.Choice.Name.denote-table` cannot be discharged at all: not at
concrete arguments, not at sealed ones, not at fully variable ones; restating
its own type and filling it with itself does not finish in 400 s, while each of
its two factors checks in 2.4 s. With the result type inferred the same
substitution is 2.4 s; with it written down it never returns.

**Provenance:** PLAN §11 row L2.4 (obligation (a), RULE 20).

**When it bites:** any consumer that writes a composite adequacy goal down.

### R-21. The conclusion type a frame lands in must be sealed where it is built

**Rule:** The TYPE a frame concludes in must be sealed where it is built.

**Measured:** instantiating the frame at the concrete elements the description
binds normalizes that type: unsealed it did not finish past 200 s, sealed the
chapter is 7 s; the same application at variable slots is free, and a defined
constant already blocks the runaway, `opaque` being the robust form of that.

**Provenance:** PLAN §11 row L2.4 (the assembly, "One more law").

**When it bites:** frames concluded at concrete elements in signatures.

### R-22. A property of a computed least name must be the exported least-element predicate

**Rule:** A property of a computed least name must BE the well-order chapter's
least-element predicate at an exported family, never a re-spelling of it.

**Measured:** written out it costs 16 s attributed to one definition; as the
predicate it costs nothing, because conversion at a computed name opens the code
order down to the level search.

**Provenance:** PLAN §11 row L2.4 (the re-cut, "Two more laws").

**When it bites:** any property stated of `leastOf`-style computed names.

### R-23. The stage arrives as a term, not a slot

**Rule:** The stage must arrive as a term, not a slot.

**Measured:** two binders 163 s, one binder 3 s, at `L.Choice.Faithful`'s
readings.

**Provenance:** PLAN §11 row L2.4 (faithfulness).

**When it bites:** descriptions whose stage is bound inside a satisfaction.

### R-24. A library round-trip lemma is a conversion hazard in its own right

**Rule:** A library round-trip lemma between two representations of the same
data is a conversion hazard in its own right; writing the two clauses by hand is
shorter and free.

**Measured:** turning the environment index into a vector through
`FinVec→Vec` measured 481.7 s for that lemma alone, and it is neither rule 1 nor
rule 2 (sealing made no difference); a two-clause local recursion took it to
2.1 s.

**Provenance:** PLAN §11 row L3.26.

**When it bites:** representation round trips (Fin to Vec and kin) inside
readings.

### R-25. Naming a module application in a TYPE re-does it

**Rule:** Naming a module application in a TYPE re-does it; keep a local alias
in the type.

**Measured:** spelling one lemma with the full application instead of the local
alias cost `L.Axioms.Basic` +10.3 s (8.2 to 18.5); keeping the alias in the type
costs zero.

**Provenance:** PLAN §11 row L2.4 (C0/C1, "A fresh instance of law 2").

**When it bites:** signatures naming a long module application.

### R-26. The parameter remedy and the seal are not alternatives

**Rule:** The parameter-carrying-its-own-equation remedy and the seal at the
birth site are not alternatives; this chapter needed both.

**Measured:** `L.Choice.Before`: the parameter remedy alone brought the family
build to 376 s and no further (the template remedy alone did not finish, killed
past 400 s); with five descriptions sealed where built, each reading in its own
unfolding block: 376 s to 3.79 s, mathematics untouched. Cause: law 9 in a new
place, every satisfaction at a concrete environment normalized a formula
carrying two copies of the whole hierarchy description.

**Provenance:** PLAN §11 row L2.4 (the earliest-disagreement family).

**When it bites:** descriptions whose formulas carry whole other descriptions as
constants.

### R-27. The check-time predictor is induction count times truncation elimination

**Rule:** The predictor is induction count times truncation elimination, not
formula size.

**Measured:** a `Recursion` carrying the full satisfaction graph (about 8,830
constructor nodes against `closureGraph`'s 2,240) cold-checks at 1.34 s against
1.33 s with the `Of` application deleted; the shipped instance's 12.7 s is 25
lines of `holds` and `uniq`.

**Provenance:** PLAN §11 row L3.0.1 (design ruling for satisfaction's `funct`).

**When it bites:** estimating the cost of clause-heavy recursion assemblies;
the two twelve-case inductions and the inversion are the careful items.

### R-28. Witness-locality

**Rule:** A graph may not describe an object by asserting the existence of that
very object; discharging the assertion is the problem it was meant to solve.

**Measured:** pinned by the typechecker at `L.Recursion.witnessInModel` rather
than left as an argument; the false mechanism (circularity of existence or
uniqueness) would have cost five build steps.

**Provenance:** PLAN §11 bookkeeping, reconnaissance and adjudication [L3.0.1].

**When it bites:** any description whose existential witness is the described
object; the reason a bound table and a bound index set travel together.

### R-29. Seal the membership certificate where the element is built, not the element

**Rule:** When a restricted structure's elements appear as constants of the
object language, seal the membership certificate where the element is built, not
the element.

**Measured:** `L.Axioms.Full` did not finish in ten minutes; sealing the
certificate alone (`opaque isL-Lset`) took it to 1.4 s (259 ms at the sharpest
measurement); sealing the reflected ordinal was tried first and did nothing.

**Provenance:** PLAN §11 bookkeeping, conversion-blowup finding [L2.2].

**When it bites:** constants of the object language that are elements of a model
carrying constructibility proofs.

### R-30. Rules 1 and 2 split on where the expensive construction lands

**Rule:** The split between rules 1 and 2 is not proof-versus-type; it is where
the expensive construction lands, and one statement can need both.

**Measured:** a statement of the value at a named key ran past 400 s and was
killed twice, the second time as a one-line corollary of the variable-argument
version that checks in 4.6 s; the fix took one rule each, rule 1 for the
readings and rule 2 for the name a consumer would otherwise write (a three-line
`opaque` alias).

**Provenance:** PLAN §11 row L3.23 ("Finding one, and it sharpens rule 1").

**When it bites:** any term that sits in a plain equation's type rather than
inside a proof or a goal.

### R-31. A disjunction whose branches can overlap is a truncated sum

**Rule:** When an internal case split's branches are not provably disjoint, the
meta-level goal is the truncated sum `∥ A ⊎ B ∥₁`, never the plain `⊎` with
`isProp⊎` (which demands a disjointness proof).

**Measured (B4a, 2026-08-02):** the layer's per-member goal (old member OR new
image) admits members that are both; every layer reader, wrapper, and the union
equation had to be rebuilt against the truncated sum after the plain-sum
formulation failed on `isProp⊎`'s disjointness obligation.

**Provenance:** the B4a batch record (PLAN row L3.29 ledger, commit `7b6d799`).

### R-32. Pin a cross-reading table at all keys at once, with a combined bound

**Rule:** A pinning theorem over a keyed table whose clauses read OTHER keys'
entries (shift and extension read neighbouring shelves) must quantify all keys
in one statement, with the recursion's bound combining the indices (level plus
arity below the bound); a per-column recursion at the goal level cannot supply
the other columns, because the environment pins each column's index slot.

**Measured (B4b/B4c, 2026-08-02):** the per-column formulation was
uncompileable (`# k` at a `Fin` slot; the shift shelf's pin contradicts the
column equality by numeral injectivity); the all-keys statement with
`n₀ + suc k₀ < b₀` landed at full strength.

**Provenance:** the B4b report's formulation trail; the B4c pinning
(commit `810d9cd`).

### R-33. Pass clause environments as pieces, rebuild them concretely

**Rule:** A helper consuming a clause's satisfaction takes the environment's
PIECES as arguments and rebuilds the concrete environment inside; an opaque
environment parameter blocks `lookup` from reducing and the slot machinery
fails.

**Measured (B4b, 2026-08-02):** the clause-level successor reader only checked
once the environment was rebuilt from its pieces (`suc-clause`'s design);
the abstract-env formulation left the shelves untypeable.

**Provenance:** the B4b report (delivered as `suc-clause`); commit `810d9cd`.

### R-34. Pin every implicit universe level a `using`-import leaves open

**Rule:** After `open M using (...)`, a lemma whose type leaves an imported
name's universe level implicit can send the checker into a type-level meta
search that walls the whole file; pin the level once through a module alias
(`module M' = M {ℓ}`) and read the name through the alias.

**Measured (B4e, 2026-08-02):** `num∈num : ⟨ # m ∈ # n ⟩` with `#_`'s level
left implicit after `open InfinitySet using (…)` walled the whole file; the
two-line lemma was innocent, the meta search was the cost. `module IS =
InfinitySet {ℓ}` fixed it with no other change (B4e report, the probe trail).

**Provenance:** the B4e probe trail, section 2.

## 3. Termination traps (T series)

### T-1. At-pattern aliases of accessibility constructors; split the nests outer and inner

**Rule:** At-pattern aliases of accessibility constructors reconstruct and lose
the equality column; split the accessibility nests outer and inner.

**Measured:** recorded while building `L.WellOrder.Tree`'s well-foundedness
(strong induction on size with nested accessibility nests), 2026-08-01; the
chapter lands at 279 lines, 1.1 s. The pure pointwise trap is documented at the
definition.

**Provenance:** PLAN §11 row L3.29 (M5, N1).

**When it bites:** any well-foundedness proof with nested accessibility
eliminations.

### T-2. The transitive-closure accessibility pattern

**Rule:** When a child code sits several membership steps down and composing
accessibility projections is rejected, run the recursion on the accessibility of
the transitive closure of membership, built once by a mutual
`accTC`/`goTC` pair whose two-argument descent the checker accepts.

**Measured:** the Tower honesty recursion was pre-dissolved in the brief with
exactly this pattern; the chapter stands at 1,235 lines, 4.8 s cold, with the
eight branches running the code equations backwards.

**Provenance:** PLAN §11 row L3.29 (M5, d2).

**When it bites:** decodes and honesty proofs where a Kuratowski pair puts a part
four membership steps down.

## 4. Inference traps (I series)

### I-1. `mirrorBy`-style formula metas; explicit formulas at call sites

**Rule:** A satisfaction-set path determines no formula, so every formula-typed
metavariable at a mirror/respect call site must be passed explicitly.

**Measured:** the atom lemmas errored fast with unsolved formula metas at
`mirrorBy`, the same inference trap the respect lemma recorded; with every
`mirrorBy` call carrying its two formulas explicitly, everything through the
atom lemmas is 1.8 s green. The residual wall dissolved with the per-case split:
`mirror` restated as twelve dispatches to named private case functions with the
induction hypotheses as arguments checked straight through, and the whole
chapter lands at 195 lines, 1.7 s cold. The wall was never the arity index; it
was the unsolved-formula-meta churn end to end.

**Provenance:** PLAN §11 row L3.29 (M3, 2026-08-01).

### I-2. hProp expressions cannot sit in type positions; wrap or name them

**Rule:** The library's hProp connectives (`⊔`, `⊓`, `⇔`, `¬`, `∃[_]`) carry a
result-level meta that Agda cannot solve in a signature codomain ("should be a
sort"), and an hProp-valued expression in a codomain is rejected even with
explicit levels; write `⟨ expr ⟩` around signature-level hProp expressions, or
define explicit-level wrapper connectives, or name the type.

**Measured (the P1 probe, 2026-08-02):** every unwrapped connective in a
signature codomain failed with the sort error; the probe's explicit-level
wrappers (`⊔ₚ` and friends) plus `⟨_⟩` at signatures cleared all of them, and
the file lands at 339 code lines, 2.9 s cold (the p1 report, surprises 2).

**Provenance:** the [L3.30-P1] probe (`ProbeRudComp.agda`, preserved in the
session scratchpad; the p1 report).

### I-3. Inside opaque blocks, every binding carries a type signature

**Rule:** Agda never infers a definition's type inside an `opaque` block
(`MissingTypeSignatureForOpaque`: inference would leak sealed information),
so an unascribed `where`-binding there becomes an open meta and the block's
metas storm the checker. Ascribe every binding inside `opaque`, including
where-locals whose types feel obvious.

**Measured (the rud polish, 2026-08-02):** dropping noise-only signatures
from `where` bindings inside `Ops`'s sealed spec blocks ran a 2-second file
past 600 s (killed); one dropped signature in `F1-spec` sufficed. Bisected
in four minutes by C-10 staging (three stages, per-swap asserts, typecheck
per stage, every stage under 4 s); restoring the signatures restored the
2-second check.

**Provenance:** the polish report `_build/polish-r-report.md` (commit
`77ac3e0`); sibling of C-11 and I-2.

**When it bites:** any sound/mirror chain where an object-language equation or
path must determine a formula.

## 5. Design doctrines (D series)

### D-1. The probe doctrine

**Rule:** Before committing to a heavy or hard-to-reverse path, run the cheapest
decisive probe with its abort criterion fixed in advance; a red verdict costs
the attempt and nothing else.

**Measured:** exercised every layer: P3/P2/P1 decided the AC-route fork in one
day (all PASS, memo §9); `[L3.0.3]` ran paper-level before L2 and corrected the
projection; the `[L3.24]` probe settled three open questions at once; the
cut-probe and order-probe settled the B pivot.

**Provenance:** `dev/memos/L3.28-ac-route.md` §6; PLAN §6.1 and §11 rows L3.0.3,
L3.24, L3.28, L3.29.

**When it bites:** architecture forks, unpriced risk items, and any "measure
before estimating" claim.

### D-2. The junk-table lesson

**Rule:** Naked existentials over tables admit junk: conditional clause shapes
certify nothing, so a vacuous-payload pair satisfies its clause and the
description has no honest content; exclude junk by construction (a certificate,
an honesty proof, or a kinded level table), not by decoration.

**Measured:** route C's step body with a naked existential over tables admitted
junk approximations (walked end to end 2026-08-01); the certificate formula
`CertAt` was the ruling-in-scope fix. The cut probe then proved the naive
values-cut unsound: the seed-cut junk `values (A ∩ ⟦t⟧)` escapes `𝒟ₒ A` for
non-transitive carriers (the escape case enters the probe as one flagged
postulate, settled meta-theoretically by an automorphism argument). The order
probe showed candidate 2's junk skeletons are not excluded by pair projections
either: "s is a bona fide skeleton" is not first-order definable without a
finiteness or rank predicate.

**Provenance:** PLAN §11 row L3.29 (M5, d); `_build/cut-probe-report.md` §2.2
(the four junk cases table); `_build/order-probe-report.md` §3.

**When it bites:** any object-language description that quantifies a table or
approximation whose clauses are conditional on shape properties.

### D-3. The scaffold-copy pattern for coexistence

**Rule:** When two routes must coexist before a rewire, land the new route's
consumer as a parallel scaffold: a line-for-line copy with one import
re-pointed and prose that says exactly that; the old cluster stays untouched and
green, the new route states its laws against the scaffold, and at the rewire one
copy retires.

**Measured:** `L.Godel.Step` (362 lines) is line-for-line `L.Choice.Step` with
one import re-pointed; the whole spine (birth, the carve, byName, stepAt,
orderAt) ran on the term names with zero code changes, 3.3 s, which is the
interface parity of N2 proved in the consumer. The dependency map showed the
in-place swap would falsify the old cluster's content, not just its types.

**Provenance:** PLAN §11 row L3.29 (M5, N3); `_build/compression-audit.md` F6.

**When it bites:** any swap that must keep the old development typechecking until
the pedagogy or rewire verdict.

### D-4. The collector principle

**Rule:** A constant-plus-atoms slot is cheaper than a formula carrying tables:
materialize a heavy description as one element of the model whose membership is
the meta relation, and let consumers read it as a constant through two atoms,
rather than carrying coded tables inside formulas.

**Measured:** the old `Bound` interface is already minimal: `Pick` names the
order only as a constant (`var zero ≐ con r`) read by one `appAt`; the
formula-side alternative relocates the collector's mathematics into the one
place the route measured to be expensive (a formula carrying coded tables is the
measured wall class) and would reopen `Transversal`; the collector is the cheap
end, about 200 to 400 lines for the materialization half of M5c.

**Provenance:** `_build/deep-levers.md` §3.3; `_build/order-probe-report.md`
§2 (candidate 1's internal side needs no certificate for the same reason).

**When it bites:** any endgame (the axiom of choice's least-member pick, an
order read at a bound) where the description threatens to grow coded tables.

### D-5. Readers do not validate a formula; the meta-match table does

**Rule:** A described formula's in/out readers typechecking (and even being
green in both directions) does not validate the formula against its meta
semantics; the validator is the clause-by-clause meta-match table, stating for
every disjunct at every index where it matches the meta step and where it must
be refuted.

**Measured (B4b/B4c, 2026-08-02):** the layer disjunction shipped green with
eighteen direction-paired readers and was wrong twice: the values disjunct
over-described at every positive arity, and the extension disjunct at arity
one (the second found by the mandated table against the reviewer's own
eight-already-match claim, then confirmed by instantiating the delivered
in-reader at the mismatched arity). Both fixed by guards, refuted-not-untypeable.

**Provenance:** the B4b report §2; the B4c report §2 with its table; commit
`810d9cd`.

### D-6. Probe prices multiply by three

**Rule:** An estimate extrapolated from a shape-validating probe underprices
the production surface by roughly a factor of three; budget probe-derived
estimates times three before ruling on them.

**Measured (2026-08-01 to 02):** route C landed at roughly twice its memo
bucket (5,936 against 2,700-4,900 at the M4 accounting, with the tower bucket
alone at 4,400 against 250-400); option B's closure side landed at 1.6-2.7
times the cut probe's 1,220-2,060 while still unfinished. The recurring
mechanism: probes validate one to three clauses; production pays readers in
both directions, guards, dispatch chains, and environment plumbing per clause.

**Provenance:** PLAN row L3.29 (the tripwire accountings and the B ledger);
`dev/memos/L3.29-b-pivot.md`; the L3.30 row's calibrated budget clause.

### D-7. A constructive rud basis carries intersection as a primitive

**Rule:** The classical derivation of intersection from difference
(`a ∩ b = a ∖ (a ∖ b)`, SZ 1.3(c)) is not constructive: the double difference
realizes `{x ∈ a | ¬¬ (x ∈ b)}`. A rud basis interface meant to run without
invoking LEM in its algebra carries an intersection operation as a primitive
(or explicitly spends LEM at that spot and says so).

**Measured (the P1 probe, 2026-08-02):** the probe's abstract basis needed
`interOp` as its own parameter; the `∖`-derived formulation left the `∧`
clause unprovable without double-negation elimination (the p1 report,
surprises 3). Bedrock assumes classical logic globally, so spending LEM here
is admissible; the lesson is that the choice is a design decision to make
explicitly, not an oversight to discover mid-build.

**Provenance:** the [L3.30-P1] probe; the p1 report.

## 6. Craft and process lessons (C series)

### C-1. Two conversations must not share a worktree

**Rule:** Two conversations must not share a worktree; give the second one its
own, or serialise them.

**Measured:** `[L3.2]`'s exploration ran in a git branch while a second
conversation worked the same worktree; its `git add -A` swept a revert into one
of its commits, so the backing-out is recorded inside `7428a23` rather than in a
commit of its own. Nothing was lost, but the bookkeeping cost real time.

**Provenance:** PLAN §11 row L3.2 (process note).

**When it bites:** parallel agent sessions on one checkout.

### C-2. Never sort Agda's profile output numerically without stripping the separator

**Rule:** Agda prints a thousands separator in profile numbers; sort
numerically only after stripping it.

**Measured:** the per-module list at `[L3.16]` sorted every module at or above
1,000 ms as though it were under ten; the real worst module was `L.Axioms.Basic`
at 7,142 ms, ten times the reported figure, 36% of the whole tree.

**Provenance:** PLAN §11 bookkeeping, cold-check baseline correction
(2026-07-27).

**When it bites:** any `--profile=modules` analysis.

### C-3. Prose that states an invariant is load-bearing and has to be checked like code

**Rule:** A prose sentence stating an invariant is load-bearing and has to be
checked like code; it can hide a defect the code cannot report.

**Measured:** the sentence "the same with the two innermost quantifiers turned
around" hid fatal clause bug 2; the sentence "a term of a parameter-free
formula is a variable" stopped being true at `[L3.18]` and hid a one-case
reader under a two-directional frame; a third prose contradiction was caught at
`[L3.23]` (`AllCodes-closed`). All three were caught by reading the statement
rather than the report.

**Provenance:** PLAN §11 rows L3.0.1 (twelve-clause audit), L3.16, L3.23.

**When it bites:** any recap or invariant sentence beside code.

### C-4. A shape reader that reads fewer layers than the data has is silently vacuous

**Rule:** A shape reader that reads fewer layers than the data has is silently
vacuous rather than ill-typed; check the layer count against the data's
structure.

**Measured:** with arity on the outside of tagged codes, both frames read only
one layer and the clause was vacuous at every arity but one, and wrong at that
one; both `-out` lemmas still typechecked and were still true. Fixed by reading
the key in two layers.

**Provenance:** PLAN §11 row L3.16 (mis-count correction).

**When it bites:** any reader whose data is a nested pair/tag tower.

### C-5. Every reader a clause consumes should carry a characterization in both directions

**Rule:** Every reader that a clause consumes should carry one, a
characterization in both directions.

**Measured:** `tmValAt` matched one tag of two and sat under `extAt`, which
asserts both directions, pinning constants to the empty set; the fix was 26
lines against a 55-to-80 estimate once the reader carried `tmValAt-var`,
`tmValAt-con` and `tmValAt-out`.

**Provenance:** PLAN §11 row L3.16 (defect in delivered code).

**When it bites:** any reader feeding a two-directional frame.

### C-6. Check by perturbation rather than by reading

**Rule:** Verify load-bearing predicates and decodes by perturbation: deliberate
corruptions must all be rejected, positive controls accepted, with the
introduction neutralized first so a failure is unambiguously in the elimination.

**Measured:** 11 deliberate corruptions of the decode, all rejected (including
same-frame swaps that look plausible); 17 corruptions of the code set plus 3
positive controls; 14 perturbations of `hierL` including three deep ones. The
tautology substitution distinguished "the conjunct is present" from "the
conjunct means what it says".

**Provenance:** PLAN §11 rows L3.21, L3.19.

**When it bites:** any predicate whose correctness is not typechecked (tags are
only numbers, so a wrong tag typechecks).

### C-7. A row's opening word is what a reader takes

**Rule:** A row's opening word is what a reader takes; appending a DONE record
to the end of a long row does not change it. Every status change goes at the
front, and a code carries exactly one status.

**Measured:** five rows carried a stale opening word at the L3 status
re-confirmation; `[L3.17]` read PLANNED in §11 while the unit table recorded it
DONE, and projections double-counted work for a day.

**Provenance:** PLAN §11 rows L3.17, L3.21, and the L3 status re-confirmation
(2026-07-29).

**When it bites:** any registry row with a long history.

### C-8. The gate has blind spots; name and close them

**Rule:** `lint-prose.py` and `check-glossary.py` discover inputs through
`git ls-files`, so a new untracked file is silently skipped by those two stages;
the glossary checker's avoid-list keys off language markers, so a forbidden
rendering outside any marker is silently not a violation; nothing checks that a
file ends where it should. Run the linters explicitly on new files, exercise
checks inside language blocks, and file the fixes under `[L5.1]`.

**Measured:** a positive control appending outside a language marker reported a
false green; the table chapter carried two lines of tool-call scaffolding after
its final marker with every gate green.

**Provenance:** PLAN §11 rows L2.4 (C6), L3.19 (route audit), L2.4
(earliest-disagreement family).

**When it bites:** every new file and every end-of-file edit.

### C-9. The graft entry: graft retractions as explicit projections

**Rule:** Write graft retraction equations with explicit `fst`/`snd`
projections, not `let`/`where` bindings, so the retraction proofs can be direct
path lambdas.

**Measured (M5a):** the brief's `let (cs' , rest) = graftL cs ps in …` form made
the definitional-equality checks not terminate inside the budget; the same
content as explicit projections (`(node … (fst (graftL cs ps))) , snd (graftL cs ps)`)
let the retraction proofs be written as direct path lambdas.

**Provenance:** `_build/m5a-report.md` (Deviation in the graft equations);
committed as `9539088` with P-g.

**When it bites:** any retraction or round-trip proof over a pair-valued
recursion at concrete types; pairs with P-g.

### C-10. Mechanical multi-site edits: script, assert, typecheck, and mind containment

**Rule:** Apply repetitive refactors as a script of exact-string swaps with a
per-swap occurrence assertion and an immediate typecheck after the batch; order
swaps so no pattern is a substring of a later one; never let a transformer
rewrite the helper definitions it just inserted; and re-check helper bodies
after any pattern-driven pass.

**Measured (the Tower polish, 2026-08-02):** three transformer mishaps in one
session (the adequacy helpers rewritten into self-references by their own
pattern; `interK t₁ t₂` matched inside `code-interK t₁ t₂`; a two-space anchor
substring-matching a four-space line and mangling indentation), all caught at
the assert-or-typecheck step, none escaping to a commit.

**Provenance:** the Tower polish commits `da5a09c`, `e57f2b5` and this row's
session record.

### C-11. Parameterized module bodies indent deeper than the header

**Rule:** In a `module M (p : ...) where` whose body sits at the same column
as `M`, only the first declaration sees `p`; later declarations report the
parameter out of scope (Agda layout). Indent the body deeper than the module
header; a nested parameterized module additionally needs its `where` indented
deeper than its telescope.

**Measured (the P1 probe, 2026-08-02):** the probe's `Basis` module lost its
parameters after the first declaration at column 0; re-indenting the body one
level cured it with no other change (the p1 report, surprises 1).

**Provenance:** the [L3.30-P1] probe; the p1 report.

### C-12. Agda runs under a hard heap cap; parallel writers under a quota

**Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`)
so a runaway typecheck dies with a clean "Heap exhausted" exit instead of
OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make`
exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02
once the caps and the watchdog were live): WIDE mode for routine batches,
up to FOUR concurrent Agda writers at `-M8g` each; HEAVY mode for assembly
and close-out batches, at most TWO at `-M12g` each; the tier is chosen at
dispatch, mixed tiers keep the worst-case heap sum at or under 32 GB, and
the third and fourth slots are filled only when system free memory reads
above 25%. A watchdog (`_build/tools/agda-watchdog.sh`, restart it each
session) backstops at 14 GB per process and an 8% system-free floor. A
heap-exhausted exit is a WALL event: apply the P-i playbook, never simply
rerun.

**Measured (2026-08-02):** four concurrent unguarded flash writers; one
`agda src/L/Rud/Images.lagda.md` climbed past 5.8 GB and the 64 GB machine
OOM-crashed, killing all four in-flight tasks. The cure imports the sister
playbook's guard (P-i: `GHCRTS` hard cap, macOS `ulimit -v` is ignored, RTS
`-M` is the lever; a 36 GB box capped at 20-22 GB for a single check), scaled
to this machine's concurrency.

**Provenance:** the crash of 2026-08-02 (four L3.31 wave tasks lost mid-
flight, session-resumed after); P-i's OOM-guard clause; the Makefile GHCRTS
export added the same day.

## Adding an entry

Take the next free ID under the series (P-h, R-31, T-3, I-2, D-5, C-10), cite
the source in the entry, and keep the evidence column to measured numbers. When
a new measured wall joins a class an entry already covers, extend that entry's
evidence and provenance instead of minting a duplicate. If a lesson cannot be
sourced, it is not entered; it is surfaced to the owner instead.
