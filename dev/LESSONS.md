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
lines, 1.2 s). Derived operation aliases (`f0..f15`) are not constructors:
enumerating over them fails with `Op16.op0 != f0`; enumerate over the
underlying constructors `op0..op15` (K1).

**Provenance:** `dev/memos/L3.28-ac-route.md` §9 (from probe P2);
`dev/PLAN.md` §11 rows L3.29 (M1, M4) and L3.22; the K1 datum:
`agents/tasks/archive/K1/k1-report.md`.

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

**Provenance:** `agents/tasks/archive/M5A/m5a-report.md` Surprises 1 (the M5a re-cut, committed as
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
  Sub-case (R5-D2, 2026-08-03): a formula index is a huge argument even when the
  formula itself is small, once it sits under a satisfaction head (implicit
  φ ψ cost a 168 s check; explicit indices and fifteen named tails fixed it).
- **[A] Keep it neutral**: heavy values never sit inside
  `extensionalV`/`Σ≡Prop`/conversion positions; use stuck terms or variables
  and bridge the concrete membership by one `subst`. (Extends Rule 1.)
  **Measured again (2026-08-03):** prophylactic use before a wall (sixteen
  heavy modules at abstract carriers, 40 s total, G3G4G5); a 1,200-line
  abstract-carrier file at 47.8 s (R5-D2); a 1,347-line predicate at a
  seven-fact telescope, 9.5 s cold (K3); set-level identities at abstract
  carriers fire none of the machinery, 246 lines at 1.9 s (K4); and the
  obvious cheaper replacement is worse when extensionality meets a tower
  built from cheap sealed parts (600 s kill, R5a-2).
- **[B] Seal the operator or the set** `opaque` at its birth site; where the
  set itself is the heavy thing, seal the SET, not just a bridge. (Extends
  Rule 2 and P-c.) **Layer cap sub-rule** (source case 12): any tower of two
  or more `Lset ∘ sucV` layers gets one independent opaque alias PER LAYER,
  so conversion unfolds at most one; costs multiply per exposed layer.
  Trigger widened (part M, 2026-08-03): four exposed `Lset ∘ sucV` layers in
  a module HYPOTHESIS type doubled a file's check (44 s → 90 s) and one
  18-line seal restored it; the layers need not be in a term.
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
B4d walk lesson (P-h). The same-day datum batch (2026-08-03) is filed from
`agents/tasks/archive/G3G4G5/g3g4g5-report.md`, `agents/tasks/archive/R5D2/r5d2-report.md`, `agents/tasks/archive/K3/k3-report.md`,
`agents/tasks/archive/K4/k4-report.md`, and `agents/tasks/archive/R5A/r5a-report.md`.

### P-j. A path lambda is a normalization request

**Rule:** A path lambda is a normalization request: `λ i → op (p i) (q i)`
forces `op` to whnf at both endpoints.

**Measured (r3c, 2026-08-03):** nine of ten `eval-agree` clauses were free
and the one fatal differed only in whether `op` was sealed.

**Provenance:** `agents/tasks/archive/R3C/r3c-report.md`.

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
conversion. Datum (K3, 2026-08-03): environments spelled out at fixed
concrete arities cost ~60 lines in a 1,347-line chapter, and generic arities
were not the wall source (probe 11 vs 13).

**Provenance:** PLAN §11 row L2.4 (faithfulness); the K3 datum:
`agents/tasks/archive/K3/k3-report.md`.

**When it bites:** any reading whose environment is a concrete abbreviation.

### Rule 20. Composites of adequacy equations are consumed factor by factor

**Rule:** A composite of adequacy equations is consumed factor by factor, never
as a composite.

**Measured:** `L.Choice.Name.denote-table` cannot be discharged at all: not at
concrete arguments, not at sealed ones, not at fully variable ones; restating
its own type and filling it with itself does not finish in 400 s, while each of
its two factors checks in 2.4 s. With the result type inferred the same
substitution is 2.4 s; with it written down it never returns.

**The subject was deleted 2026-08-10 and the measurement is unaffected.**
`denote-table` was dead in code and it was removed. **Last green with it:
commit `35cb762`**, at `src/L/Choice/Name.lagda.md:478-484`, inside
`Naming.Internal`. Restore with `git show 35cb762:src/L/Choice/Name.lagda.md`
to re-run the measurement. **The law never depended on the lemma being live.**
It binds any consumer that writes a composite adequacy goal down, and the wing
will write several. Keeping the code would also have re-verified only the
cheap half: the tree holds the factor-by-factor form, so `make check` confirms
the 2.4 s factors and never exercises the 400 s wall at all.

**Provenance:** PLAN §11 row L2.4 (obligation (a), RULE 20); commit `35cb762`
for the deleted subject.

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
uniqueness) would have cost five build steps. **`witnessInModel` was dead in
code and was deleted 2026-08-10; last green with it is commit `35cb762`, at
`src/L/Recursion.lagda.md:139-141`.** D-27 class 3: a citation is repointed at
a commit, never paid for by keeping the code in `src/`.

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

### R-35. Union representations are meta-poisoned; state memberships at small indices

**Rule:** Index or path extraction from the representation of a union of an
open term (`⟪ ⋃ x ⟫`-level fiber extraction, `separation-ax` over a union)
leaves unsolved metas or churns the presentation machinery; state the
membership at the SMALL INDEX instead (an existential over `⟪ y ⟫` with the
inclusion applied), and keep constructions at the stuck-member level.

**Measured (R1b, 2026-08-02):** the original F8-spec backward direction via
fiber extraction over `⟪ y ⟫` was the OOM runaway that crashed the machine;
two sibling formulations (separation over a union; index extraction from a
union representation) walled the same way; the small-index restatement
checks the whole file in 54.6 s cold and the walls did not return. First
pre-wall syntax-indexed datum (K2, 2026-08-03): the small-indexed sett over
external syntax gave both membership directions definitionally in 45 lines.

**Provenance:** the r1b report (the crash-resumed batch); commit `7c28ce2`;
the K2 datum: `agents/tasks/archive/K2/k2-report.md`.

**Appended (the GLp probe, 2026-08-04):** a nested small-index type
(`⟪ ⟪ τ ⟫↪ m ⟫`) is free inline but hit a 12 GB heap wall at 4:37 when stored
in a RECORD FIELD; three distinct cures failed, including I-4's prescribed
carrier-level restatement, and the only measured cure is to inline the
decomposition at each use site. Storage position, not expression size, was
the trigger. Provenance: `agents/tasks/archive/L3-31-GLPROBE/l3.31-glprobe-report.md`.

### R-36. Expose a sealed decomposition with an opaque-unfolding read lemma

**Rule:** When a consumer needs to decompose a value sealed per P-c, do not
move the definition out of the opaque block and do not unseal it: add a READ
LEMMA in its own `opaque unfolding X` block, proving the decomposition
inside the seal and exporting only the truncation-explicit type. The seal
stays, the surface grows by exactly the needed read.

**Measured (R2c, 2026-08-02/03):** adopted three times in one batch chain:
the five Ops reads (F2/F3/F4/F6/F7-read, +117 lines, unblocking three
transitivity cases and the description hops), the four Images junk lemmas
(constructive, no LEM inside Images), and the Fof equality lemmas; each
left every existing export and seal untouched. This dissolved a planned
unsealing surgery. The read's direction is a public interface choice, and a
consumer needing both directions must state the reverse read as its
dependency (r3b2); an opaque index family wants a small block of unfolding
equalities next to it as its official interface (r2c).

**Provenance:** the r2c report parts 2-4; commits `7c69beb`, `a3c9f80`;
companion to P-c; the r3b2 read-direction datum: `agents/tasks/archive/R3B2/r3b2-report.md`.

### R-38. A consumer's alias of a transparent imported operation is a birth site

**Rule:** P-c extends one layer up: when a consumer names a composite of a
TRANSPARENT imported operation (a derived op whose body reaches an imported
sett/union tower), the consumer's alias is itself a birth site and must be
sealed opaque with its spec inside, even though the imported operation was
delivered transparent. Transparent-by-delivery kit operations (the Images
F10 and the left/right projections are the standing instances) are a hazard
for every future consumer.

**Measured (R3c, 2026-08-03):** eval-agree hung past 400 s twice; the
bisect isolated the collection clause, whose transparent colOp unfolds into
the transparent F10 and its union/intersection tower under a sett index;
sealing the nine derived operations at birth with specs inside dropped the
check to 3.7 s. **Prophylactic datum (R5a, 2026-08-03):** the rule applied
BEFORE any wall kept a 731-line sett-tower chapter at a 2.8 s cold check
end to end, the first case of the seal discipline preceding a wall instead
of repairing one. **Measured again (R5-D2, R5a-2, K1, 2026-08-03):** statement
positions count: naming transparent `left`/`right` in a theorem statement
cost 170.7 s cold (R5-D2); an imported transparent operation can cost 25.7 s to
invoke even at variable arguments and sealing only moves the cost, so the
alias's job is to be the single site that invokes it (R5a-2); second
prophylactic datum: the base block ran at 1.3 s warm with the discipline
applied first (K1).

**Provenance:** `agents/tasks/archive/R3C/r3c-report.md` (the wall trail); commit `d15c114`;
companion to P-c and R-36; the R5-D2, R5a-2, and K1 datums:
`agents/tasks/archive/R5D2/r5d2-report.md`, `agents/tasks/archive/R5A/r5a-report.md`, `agents/tasks/archive/K1/k1-report.md`.

**Appended (the PZ polish, 2026-08-03):** when an expensive imported
invocation has consumers in more than one chapter, the single sealed
invocation belongs in the EARLIEST consumer, trunk-wide, not once per file
(`right-at-pair` sealed in Step took the Step+StepInL pair from 202.2 s to
118.2 s; sealing in StepInL alone would have left ~144 s). And profile before
applying a transferred perf datum even when it is trusted: the same 175 s
profile that confirmed the r5a figure (26-29 s per site) also exposed a
larger unattributed cost in the same file (`Slot.k1` 31.7 s, `Slot.tupleIn`
24.9 s). Provenance: `agents/tasks/archive/POLISH2/polish2-report.md`.

**Appended (the W3 sealing probe, 2026-08-04, measured at 60x):** never `with`
on a transparent least-witness term. The construction RE-ELABORATES the search
in every branch, so the cost is in the `with`, not in the search: the same case
analysis aborted at 60 s with RSS climbing through 8 GB (a 150 s run reached
10.5 GB), at the ABSTRACT carrier as well as the concrete one, and checks in
0.91 s once the branch is a named helper whose written type carries the
equation. Two other cures work equally: sealing the consumer alias opaque at
its birth site with an unfolding read lemma beside it (0.93 s), which then
lets even the `with` on the sealed key check, and absorbing the truncated
search result into a proposition-valued goal (0.96 s). The same run found that
two sibling walls (a heap exhaustion at a concrete presentation and a hang on
comparison types carrying a concrete ordinal) did not reproduce at all under
pinned implicits and warm caches, so an elaboration-context artifact can look
exactly like a statement-level wall: re-measure a recorded wall before pricing
a design around it. Provenance: `agents/tasks/archive/L3-32-T22/l3.32-t22-report.md`,
`agents/tasks/archive/L3-32-T19/l3.32-t19-report.md`.

### R-37. A transported membership in a compared statement position re-fires the tower

**Rule:** A hypothesis of the shape ⟨ x ∈ Sset (concrete index) ⟩ whose proof
arrives by transport, placed in a lemma STATEMENT at a concrete index, puts
the proof term in conversion position and re-normalizes the union tower
under it: the P-c mechanism arriving through a statement, not an index.
The trap is invisible at the definition site (the same lemma at variable
indices checks in milliseconds) and fires at the consumer. Cure (P-i [E]):
take the membership as a VARIABLE hypothesis; the statement becomes
strictly stronger and the mathematics is unchanged.

**Measured (R4, 2026-08-03):** the restriction lemma with
`Sset-mono ... : ⟨ x ∈ˢ Sset (sucV β) ⟩` in its statement ran past 600 s
(killed, deletion-bisected to the single lemma); the variable-hypothesis
restatement checks in 10 s inside a 2.6 s-cold file.

**Provenance:** `agents/tasks/archive/R4/r4-report.md` section 6; commit `03f7bc6`.

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

### R-39. State the satisfaction telescope at the fragment that consumes it

**Rule:** Keep a satisfaction telescope honest by the fragment that consumes
it: the pure atom/negation/existential core is constructive and
transitivity-free (JU + Jrud only); Utrans enters at parameter atoms and
bounded quantifiers, UmemInJ at `con c` atoms.

**Measured (G2p, 2026-08-03):** the probe's three clauses plus adequacy in
286 lines, 1.8 s cold, zero Utrans uses.

**Provenance:** `agents/tasks/archive/G2P/g2p-report.md`.

### R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures

**Rule:** An ordinal-membership premise stated at a deep iterated successor
(`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the
whole chain against the level's union representation, and the cost is
super-linear in the depth. State the witness at a SHALLOW index and climb by
the limit-ordinal successor closure (`limit-succ-mem`,
`L.Rud.Hierarchy:455`), one step per line. R-35's small-index shape is the
cure; the mechanism differs (no index extraction, pure premise conversion).

**Measured ([L3.32-T154], 2026-08-08):** depth 1 converts in 0.7 s, depth 3
in 18.9 s, depth 6 never inside 600 s under the 8 GB cap; the nine-line
climb takes the site from KILLED at 631 s to 59 s, exit 0. Found by prefix
bisection of the below-lim probe; the wall survived every postulate variant
except postulating the ordinal witness itself.

**Provenance:** `agents/tasks/archive/L3-32-T154/l3.32-t154-report.md` sections 2 to 4; the harness
family `/tmp/t154-scratch`.

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

**Provenance:** the polish report `agents/tasks/archive/POLISH-R/polish-r-report.md` (commit
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

**Where a probe lives (standing rule, owner-ruled 2026-08-13, replacing the
lifecycle of 2026-08-04):** a probe is the REPORT'S OTHER HALF. The report
carries the verdict; the probe carries the term, which no prose copies without
loss. Both are evidence and both are kept.

1. **Write the probe in `agents/tasks/<TASK>/`, beside the report.** One
   directory per task, because a task often writes several probes. The
   directory is the module qualifier, so the file declares
   `module LJ-1-141.ProbeLJ1141A`. `bedrock.agda-lib` lists `agents/tasks` as
   an include root, so the probe imports the tower exactly as a master does and
   **you run it where you wrote it. It never moves, so no citation into it is
   ever rewritten.**
2. **NEVER under `src/`.** Thirteen probes were swept into a commit by a
   `git add -A src/` on 2026-08-04, 3,274 lines, and had to be untracked.
   `scripts/check-probes.py` is the gate, in `make check` and in the pre-commit
   hook, because an ignore rule is a default that `git add -f` walks past.
3. **The probe is TRACKED and is NEVER deleted.** Nothing sweeps it, nothing
   archives it, and there is no clock on it.
4. **The report is still written, and it is still written first** (C-22). A
   probe whose verdict is not in a report is not finished, however green it is.
5. **Nothing typechecks a probe once its task closes.** It becomes text, like
   the report, and its claim is true of the tree at its date. **So run it
   yourself while your task is live: that is the only check it will ever get.**
6. **A pattern worth keeping is not kept by keeping the file.** If a probe
   taught a reusable shape, that shape belongs in this law book or in the
   chapter it seeded. A tracked file is still not a home for a lesson.

**Enforcement points, because a rule with none is a wish.** Rule 2 is the only
mechanical one: `scripts/check-probes.py --check` in `make check` and `--staged`
in `scripts/git-hooks/pre-commit`, pinned by `scripts/tests/test_probe_gate.py`.
**Rules 1, 3, 4, 5 and 6 are enforced by the brief and by the return audit**
(`dev/ORCHESTRATION.md` section 1's standing clauses), and by nothing else.

**Provenance.** Owner ruling 2026-08-13, which replaced the ruling of
2026-08-04 after `[LJ-1.133]`, `[LJ-1.138]` and `[LJ-1.141]` measured what the
throwaway rule actually cost: 284 probes accumulated untracked in `src/` with
986 line-number citations pointing into them, one `git clean -xdf` from gone.
The lifecycle machinery of 2026-08-13 is frozen at
`archive/scripts/check-probes-lifecycle.py`; `archive/src/2026-08-13-probe-sweep/README.md` maps
every pre-ruling path to its new one.

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

**Provenance:** PLAN §11 row L3.29 (M5, d); `agents/tasks/archive/CUT-PROBE/cut-probe-report.md` §2.2
(the four junk cases table); `agents/tasks/archive/ORDER-PROBE/order-probe-report.md` §3.

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

**Provenance:** PLAN §11 row L3.29 (M5, N3); `agents/tasks/archive/COMPRESSION-AUDIT/compression-audit.md` F6.

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

**Provenance:** `agents/tasks/archive/DEEP-LEVERS/deep-levers.md` §3.3; `agents/tasks/archive/ORDER-PROBE/order-probe-report.md`
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
both directions, guards, dispatch chains, and environment plumbing per
clause. Family calibration datum: graph-style chapters price ambient-set
bookkeeping at roughly 3:1 over content lines, not zero (R5a-2's clause
table).

**Provenance:** PLAN row L3.29 (the tripwire accountings and the B ledger);
`dev/memos/L3.29-b-pivot.md`; the L3.30 row's calibrated budget clause; the
R5a-2 family calibration datum: `agents/tasks/archive/R5A/r5a-report.md`.

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

### I-5. Inner-world truncation branches carry written types

**Rule:** In the inner world, every `PT.rec`/`PT.map` branch gets a named
`where` function with a WRITTEN type; a branch whose type is left to
inference re-elaborates the inner satisfaction machinery per constraint and
reads as a conversion wall. The trap's target class is wider than the
retiring stack recorded: it fires on equations between iterated Kuratowski
pairs, not only on disjunctions of readings, and the textbook pr-seal is
NOT the cure (reported unmeasured in the source batch, honestly).

**Measured (K3, 2026-08-03):** six 180 s+ wall events, one root cause; the
isolating pair: the identical application checks in 1.8 s against a written
type and does not finish in 180 s inside a `PT.map` lambda with the branch
type inferred.

**Provenance:** `agents/tasks/archive/K3/k3-report.md`; commit recorded with the K3 chapter.

**Measured again (2026-08-07, the sharpest instance on record):** `[L3.32-T143]`
bisected a check-time wall in a below-lim probe to ONE call: `∈sucV-elim` at a
concrete successor index, with its two branches passed as inline lambdas. The
walled run passed 595 seconds without completing. Naming the two branches as
top-level functions with written types, 29 lines total, took the proof to
**27 milliseconds**: a factor of at least 22,000. The rule's cure applies
beyond `PT.rec`: ANY eliminator whose branches are inline lambdas over
inner-world content can carry the wall, and `[T138]`'s harness had already
shown every named-branch clause beside it checking under 45 ms.

### I-4. Implicits inverted through content-of never solve; state combinators over carriers

**Rule:** An implicit argument that unification must invert through `⟨_⟩`
applied to a defined function (`_⇔_`, `_∈ₛ_`, any hProp-valued operator) is
never solved: Agda blocks the constraint and keeps normalizing the V-side
presentation machinery underneath it, which reads as a conversion wall in
situ while the isolated machinery stays fast. State every bidirectional
combinator and membership transport over the CARRIERS (a `_↔_` on `Type ℓ`
that is definitionally `⟨ A ⇔ₚ B ⟩`), so every implicit is solved from a
path or a Π type; state characterizations at a restricted carrier whose
index carries the certificate (a projection of a variable), never at an
eliminator application.

**Measured (the Realize walls, 2026-08-03):** the controlled A/B/C on
byte-identical proof bodies: abstract face with hProp-level implicits 27 s
FAIL (blocked constraints naming the presentation machinery); the same
face with carrier-level combinators 18.4 s green; concrete face 14 s
green. The A/B delta is the cure; the B/C delta also refutes face
abstraction as the cure of THIS wall class (P-h remains measured law for
walk arguments over transparent sett bodies, and is kept in Realize as
insurance, but it is not a cure-all: the mandated-first-formulation
protocol exists exactly to catch this). The companion reshape (bounded
quantifier ranging over u itself) dissolved the second wall's obligation
outright and un-spent the walk's transitivity hypothesis. The
mandated-first-formulation protocol then held a 1,285-line chapter: ten
incremental checks, one scope-level fix, no formulation retry, no wall (G2).

**Provenance:** `agents/tasks/archive/R3A/r3a-walls-report.md` (the A/B/C table and the five
candidates); commit `6153e58`; sibling of I-2/I-3; the G2 datum:
`agents/tasks/archive/G2/g2-report.md`.

### I-6. hProp connective carriers come pre-shaped; consume at the carrier level

**Rule:** The library connectives' carriers are not opaque: `⟨ P ⊔ Q ⟩` is
already `∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁` and an hProp `⊓` codomain is an untruncated
dependent Σ; consume them at the carrier level (apply the join-valued
function directly and do the `PT.rec` at the plain-sum level, or project the
pair), never wrap the result in another `PT.rec`.

**Measured (2026-08-03):** probe LC-2 (no `PT.rec` needed at `⊓`); K1 lost
three ~10 s checks to the double-truncation confusion.

**Provenance:** `agents/tasks/archive/G2P/g2p-report.md` (LC-2); `agents/tasks/archive/K1/k1-report.md`.

### I-7. Refutations through `∈sucV-elim` land in `⊥*` at `ℓ-suc ℓ`

**Rule:** `∈sucV-elim`'s motive lives at `Type (ℓ-suc ℓ)`, so an ordinal
no-go eliminated through it must land in `Empty.⊥* {ℓ-suc ℓ}` with
`Empty.isProp⊥* {ℓ-suc ℓ}`, not `Empty.⊥`; the consumer is `Empty.rec*`.

**Measured (2026-08-02/03):** G6's not-a-successor branches, R2b's refutation
motive, K4's ordinal contradiction, three occurrences, one of K4's three
errors.

**Provenance:** `agents/tasks/archive/G1G6/g1g6-report.md`; `agents/tasks/archive/R2B/r2b-report.md`;
`agents/tasks/archive/K4/k4-report.md`.

### I-8. `dne` is at level ℓ; bridge structure-level memberships before classical steps

**Rule:** `Switch.dne` takes an `hProp ℓ` while `∈ˢ` lands in
`hProp (ℓ-suc ℓ)`, so every classical step on a structure-level membership
goes `∈s`, then `dne`, then `∈S`; invisible until the error appears.

**Measured (R5a, 2026-08-03):** `cap-outr` (not `cap-outl`) is the classical
half, a one-line idiom.

**Provenance:** `agents/tasks/archive/R5A/r5a-report.md`.

### I-9. Verify at-most-one witnesses before LEM decides a witness-shaped proposition

**Rule:** Before LEM decides a witness-shaped proposition, verify at-most-one
witnesses; injectivity is often the missing lemma.

**Measured (r2a, 2026-08-02/03):** `isSucc` forced `sucV-inj-ord` (27 lines),
a gap the brief did not list.

**Provenance:** `agents/tasks/archive/R2A/r2a-report.md`.

### D-9. Choose the induction carrier by which operations act homomorphically

**Rule:** Before running a structural induction over a composite calculus,
choose the carrier object by counting which clauses act homomorphically on
it; a carrier that absorbs most operations turns their clauses into one-line
ports, and the wrong carrier hides that as apparent hardness.

**Measured (R5a, 2026-08-03):** the image principle's induction over the
element relation gives six of ten clauses essentially free (intersection
and difference are the same operations one level up; the extraction is one
F8 with no union), against one of ten over the graph form the classical
gloss suggests.

**Provenance:** `agents/tasks/archive/R5A/r5a-report.md`; commit `a34907c`.

### D-10. Price the truth of a recorded residue before pricing its proof

**Rule:** A residue recorded under the wall protocol names a TARGET, and a
target can be false; before dispatching a discharge batch, spend the five
minutes checking the target's truth at the intended generality (a Tarskian
or cardinality obstruction is the usual killer), and record the corrected
target beside the original.

**Measured (R5b, 2026-08-03):** the r3c report's third residue as recorded
(the tower lift at arbitrary stage spread) is false two limits up by the
satisfaction predicate; the true one-block form was provable the same day.
The r2c chain had already shown the mirror case (a correct measurement of a
wrong target at the step's shape). Same-day extensions, all measured: price
the recorded target's index translation (the block-translated
`Lset α ≡ Jset (b α)` is false at α = 1); price a reduction's hypotheses for
dischargeability and for nameability of every module parameter they
implicitly quantify over (`values∈L` was underspecified by two nested pairs;
`stepSet∈L` is not dischargeable until the telescope names A); price the
residue against the interface that actually consumes it (Δ₀ was a crossing
tax, not a wall); price the supplier's INDEX against the consumer's
quantifier (the two-limit supplier fails at γ = ω·2, ζ = ω+3); and let a
corrected target delete a chapter (the same-index restatement removed the
block map and its missing dichotomy).

**Provenance:** `agents/tasks/archive/R5B/r5b-report.md`; commits `d15c114`, `a34907c`; the
same-day extension datums: `agents/tasks/archive/G3G4G5/g3g4g5-report.md`, `agents/tasks/archive/R5D1/r5d1-report.md`,
`agents/tasks/archive/R5D2/r5d2-report.md`, `agents/tasks/archive/K4/k4-report.md`.

**Appended (the P1 stop, 2026-08-03):** when a residue is stated as a named
classical lemma, the truth check INCLUDES a delegated dossier against the
in-repo corpus; a target stronger than the literature's theorem means the
repairing batch is repairing the wrong object, and the check costs twenty
minutes (`BlockPow` without the limit hypothesis appears in no text; Devlin
VI.2.3 is one hypothesis stronger). A stop report also measures the rejected
plan's improvement anyway (the flat coding's offset: linear to logarithmic,
against a required constant), and always tries the delivered machinery at the
corrected target before concluding the machinery is the problem (two of the
five stop theorems took eight lines and moved the residue to a satisfiable
index). Provenance: `agents/tasks/archive/L3-31-P1/l3.31-p1-report.md`.

**Appended (the P2R fork recon, 2026-08-03):** a route that keeps failing to
supply an index should be suspected of aiming at a false statement. K2, K3,
K4 and P1 each failed to supply an index for a consumer nobody had
truth-checked at the top; the top target (`Matching`) was classically false
(Devlin names and refutes it), and the "named hypothesis" framing has no
defence when the hypothesis is false. The truth check now runs on the
CHAIN'S ROOT before any link is priced. Provenance: `agents/tasks/archive/P2-FORK-RECON/p2-fork-recon.md`.

**Appended (the reshaped reduction, 2026-08-05, and this is the sharpest form
of the rule yet):** truth-checking a TARGET is not enough. When a target is
found false, every DELIVERED theorem must be re-checked for whether its proof
passes through it. A direction of the two-tower bridge was reported as
unconditionally delivered through four separate reports and as many rulings;
the reshaped reduction then found that its proof ran through a limit-membership
lemma, which used the per-level identification, whose own proof used the
residue that had been refuted. The theorem was true, but it was not proved, and
nobody had looked because the falsity was assessed at the residue and never
propagated backwards through the consumers. **A refutation is not complete until
the consumers of the refuted object have been walked.** Provenance:
`agents/tasks/archive/L3-32-T35/l3.32-t35-report.md`.

### D-8. A self-containing step operator is not subset-monotone; condition on membership

**Rule:** A step operator whose value mentions its own argument (the rud step
reads u ∪ {u}) cannot be monotone in the subset order; state its
monotonicity in an abstract telescope conditioned on membership
(u ⊆ v AND u ∈ v → step u ⊆ step v). The universal form looks harmless and
is refutable by a two-element counterexample ({u} = F0(u,u) ∈ step u needs
u ∈ v to survive into step v), while every classical use is at level pairs,
where the containing structure supplies the membership for free.

**Measured (R2c and the reshape, 2026-08-02):** the universal parameter was
proved undischargeable for any sixteen-image step (the r2c report's
counterexample); the reshape then showed the conditioned form is not a
patch but the native shape: the membership the condition needs falls out of
the same hypothesis and construction as the inclusion (Sset-mono/Sset-mem
differ only by step-⊆ versus step-∈, same price), and the whole fix cost
one added lemma, one call-site insertion, +4 code lines.

**Provenance:** `agents/tasks/archive/R2C/r2c-report.md` (the no-go trail);
`agents/tasks/archive/RESHAPE/reshape-report.md`; commits `0322860` and the reshape commit.

### D-11. State two-way adequacy at a tuple, not at a member

**Rule:** Quantify adequacy over the environment, never over a member, so the
equation `m ≡ Tup n δ` never appears in a clause; recover the member-level
pair once through a subset lemma (`T-sub`).

**Measured (G2, 2026-08-03):** the probe's 56-line negation clause became 7
lines arity-generic (16x), zero `pr-inj` chases in twelve clauses, total
adequacy 245 lines both directions. This is the tuple-level restatement of
"price decode-uniqueness once per arity".

**Provenance:** `agents/tasks/archive/G2P/g2p-report.md` (LC-1); `agents/tasks/archive/G2/g2-report.md`
(LC-G2-1).

### D-12. The tuple calculus

**Rule:** The tuple calculus has five laws, each measured below: fix the
convention by the projection (the quantified coordinate is the tuple's
head); build the diagonal first, the only permutation primitive; recurse on
the arity, never permute coordinates; instantiate one abstract
binary-relation interface at a relation and its converse; and the calculus
has exactly three moves, which are named.

**The five laws** (measured):

- **[A] The quantified coordinate is the tuple's head; fix the convention by
  the projection**: under de Bruijn binding the quantified coordinate is the
  tuple's head, so the tuple convention is fixed by which projection the
  quantifier needs, and the same choice fixes which of F3/F4 does the atom
  plumbing. Measured: one 41-line range operation amortised over four
  consumers bought the coordinate families free; the probe's F6-only reading
  of the fork got the sign backwards (G2, 2026-08-03).
- **[B] Build the diagonal first; it is the only permutation primitive**: in
  the tuple calculus F3 inserts after the first coordinate, F4 appends a
  block at a pair's end, `ranOp` strips the leading coordinate, and none
  moves a coordinate left past another; the identity graph pays for every
  such move, so build it first and treat it as the coordinate-permutation
  primitive. Measured: the equality atom needs no foundation axiom and no
  `≐`-elimination: diagonal 130 lines, converse 30, self-membership slice
  30, all from extensionality plus the range (G2); R5a-2 then spent the
  identity graph five times (2026-08-03).
- **[C] Recurse on the arity, never permute coordinates**: an atom relating
  two coordinates of an (n+1)-tuple splits four ways on whether each index
  is the head: both past the head is a cylinder one arity down; head against
  a later coordinate is the F3-insertion family; the converse is the same
  family at the converse relation; both at the head is the diagonal slice.
  Measured: `LR` 3 clauses, `Bin` 5, `Sel` 3; the whole k-ary plumbing 211
  lines with no permutation lemma (G2, 2026-08-03).
- **[D] One abstract binary-relation interface at a relation and its
  converse**: a module generic in a relation (membership plus in/out) gives
  the insertion family; instantiating it at a relation, its converse and the
  diagonal slice covers both atom kinds from one recursion. Measured: 169
  lines of shared machinery covering 2 atom relations x every index pair,
  versus a per-relation build that would have doubled it (G2, 2026-08-03).
- **[E] The calculus has exactly three moves; name them**: F3 inserts a
  coordinate after the first, F4 appends one at the end of a pair or a whole
  block with a product argument, `ranOp` strips the leading coordinate;
  choose the coordinate order in which the quantified variables lead, pad
  each constraint into the common tuple space, intersect, strip. Measured:
  `swp` fell from a four-coordinate design to a three-coordinate one, half
  the code (R5a, 2026-08-03).

**Provenance:** `agents/tasks/archive/G2/g2-report.md` (LC-G2-2 through LC-G2-5);
`agents/tasks/archive/R5A/r5a-report.md` (the three-moves law).

### D-13. Junk is junk only relative to the tower reading it

**Rule:** A value class is junk or not relative to the tower that reads it:
the rud step's level-slot junk is irreducible against the rud level (which
cannot contain itself) and evaporates against the Def tower the moment a
stage holds the level as a member.

**Measured (G3G4G5, 2026-08-03):** `Ljunk` 11 lines, a two-case split, where
LevelDesc spends ~700 lines on the same level cases; choose the carrier by
what it can contain, a sibling of D-9.

**Provenance:** `agents/tasks/archive/G3G4G5/g3g4g5-report.md`.

### D-14. A closure fragment cannot live inside the block it closes

**Rule:** Any bounding object asked to be closed under the sixteen operations
is infinite (singletons), so it is never a member of the first rud level
`Sset ω`, whose members are all finite; the base block of every
rud-versus-Def statement is a separate theorem with a finiteness proof, and
no offset engineering merges it with the general case.

**Measured (R5-D1, 2026-08-03):** negatively, it removed a planned 150-line
layer; the kernel recon registered the base block as its own residue.

**Provenance:** `agents/tasks/archive/R5D1/r5d1-report.md`.

### D-15. Reductions: the equivalence test, and a reduction is a deliverable

**Rule:** Before reporting a residue as a reduction, apply the two-way test;
when a residue cannot be discharged, the reduction itself is the deliverable
(two laws, measured below).

**The two laws** (measured):

- **[A] The two-way test before reporting**: before reporting a residue as a
  reduction, check whether the residue implies the target AND the target
  implies the residue; a failure means the product is a chain around a
  weakening, not a reduction. Measured: `DefFragment` passes (one line of
  reasoning, licensing the trade); K4 ran it on
  `fragment`/`pow-from-fragment` in 4 lines (r5d1, K4, 2026-08-03).
- **[B] The extensional standing shape**: when a residue cannot be
  discharged, deliver the reduction: state the residue for an arbitrary
  target with an extensional entry point (two containments at a variable
  member instead of a set equation) and treat it as the standing shape for
  "named and left standing". Measured: 30 lines; second instance of the
  `DefFragment`/`Discharge` pattern (K2, 2026-08-03).

**Provenance:** `agents/tasks/archive/R5D1/r5d1-report.md`; `agents/tasks/archive/K2/k2-report.md`;
`agents/tasks/archive/K4/k4-report.md`.

### D-16. The inner semantics is the working face; Δ₀ absoluteness is a crossing tax only

**Rule:** Write readers and formulas in the inner semantics at an abstract
transitive carrier; Δ₀ is needed only when a proof crosses between the
ambient and the inner reading, and inner-world readers are reusable across
chapters because they carry no absoluteness obligation.

**Measured (R5-D2, K3, 2026-08-03):** the Graphs-class re-run estimate (~1k
lines, the G2 wall class) became 2,124 lines of ordinary reading work with
zero walls; the pair kit imported whole cost zero lines against 187; no Δ₀
witness was constructed anywhere.

**Provenance:** `agents/tasks/archive/R5D2/r5d2-report.md`; `agents/tasks/archive/K3/k3-report.md`.

### D-17. Read the definition, not the case analysis

**Rule:** Describe a total projection (or an operation's junk) through its
definition, not the case analysis that motivated it: `left b = ⋃ (⋂ b)` has
one equality frame over the intersection's two-clause membership, and an
operation whose members are pairs definitionally needs no pairhood split.

**Measured (r5d2, r5b, 2026-08-03):** 30 lines of formula and adequacy
against an estimated 90, removing two of three junk readings; F11-F14 at
four operations cost zero case splits.

**Provenance:** `agents/tasks/archive/R5D2/r5d2-report.md`; `agents/tasks/archive/R5B/r5b-report.md`.

### D-18. Cofinality audits: count rank growth per member, then decide where the ranks come from

**Rule:** Before pricing a "gather the family as one set" residue at a finite
offset, count the constructor cost per member; if rank grows with the index,
transitivity refutes every finite offset and the surviving target is a
satisfaction obligation, not an arm obligation. When the cofinality is then
recorded as a fact about the target, check whether the ranks come from the
mathematics or the representation: nested-pair codes are cofinal because one
Kuratowski pair per formula layer grows rank with depth, and a flat coding
has bounded rank and no cofinality at all.

**Measured (K2, K4, 2026-08-03):** K2 refuted the finite-offset target in
five minutes (193 lines for the corrected pair); K4 showed the cofinality is
the coding's artifact, removable by rank-bounded codes.

**Provenance:** `agents/tasks/archive/K2/k2-report.md`; `agents/tasks/archive/K4/k4-report.md`.

**Appended (the P1 stop, 2026-08-03):** the check has two halves and both are
cheap: whether the ranks come from the representation, AND whether the
obstruction blamed on the cofinality is a fact about the tower's own step. K4
ran only the first half: the codes' cofinality is representational (the flat
coding really cuts it to logarithmic), but the obstruction to the block target
is `Sset`'s single-application successor, which no representation touches.
Provenance: `agents/tasks/archive/L3-31-P1/l3.31-p1-report.md`.

### D-19. Price a port against the retiring tree's transitive closure, and split both directions

**Rule:** A "port the pattern" estimate is calibrated against the retiring
chapter's import graph, not its file, and every both-directions adequacy
estimate is split into elimination and introduction and priced separately,
because the introduction has been the larger half twice.

**Measured (2026-08-03):** 250-450 became 3-4x against a 616-line chapter
importing ~1,400 code lines; K3's re-price omitted the 274-line witness-set
construction.

**Provenance:** `agents/tasks/archive/K2/k2-report.md`; `agents/tasks/archive/K3/k3-report.md`.

### D-20. A many-way disjunction is a fold over ℕ, not a right-nested injection chain

**Rule:** A twelve-way disjunction should be a fold over ℕ (`orUpto` by
induction on the bound), not a right-nested chain of injections; no
truncation nests deeper than one.

**Measured (K3, 2026-08-03):** the twelve-way layer cost 188 lines including
both meta-level translations, against Shape's 354 for the disjunction alone.

**Provenance:** `agents/tasks/archive/K3/k3-report.md`.

### D-21. Check whether the approximation's own target is the witness

**Rule:** Before building the machinery a two-sided approximation needs,
check whether the approximation's own target is the witness: the identity
fragment collapses to `λ y k → k`, so the residue is a membership and the
fragment formulation is an indirection.

**Measured (BaseBlock, K4, 2026-08-03):** both halves of the fragment
collapse at ω and at general limits (`powFragment`); removed
`Sep`/`Sstage₂` from the general case.

**Provenance:** `agents/tasks/archive/K4/k4-report.md`.

### D-22. A closure hypothesis on the carrier is worth more than a description chapter

**Rule:** Before instantiating a delivered description at a carrier, ask
whether the carrier's own closure already puts the value inside it: at a
rud-closed carrier the whole plain-argument half of `ImgArm` is `Jset-rud`
followed by `memArm`, one line per operation.

**Measured (R5b, 2026-08-03):** 16 dispatch lines plus a 12-line helper vs
the anticipated several hundred.

**Provenance:** `agents/tasks/archive/R5B/r5b-report.md`.

### D-23. Transparency of a syntax-directed recursion is an interface asset: seal the heavy values, not the syntax walk

**Rule:** Seal the heavy values, not the syntax walk; the transparency of a
syntax-directed recursion is an interface asset.

**Measured (r3c, 2026-08-03):** `Realize`'s dropped certificates were
recoverable from outside in 78 lines only because the walk stayed
transparent.

**Provenance:** `agents/tasks/archive/R3C/r3c-report.md`.

## 6. Craft and process lessons (C series)

### D-24. A transitive tower converts block absorption into a uniform bound

**Rule:** In a cumulative tower whose levels are transitive, membership of a
set in a limit or block level is never weaker than a UNIFORM finite bound on
its members' offsets: what the block buys for containment it cannot buy for
membership. A plan of the form "the members sit at unbounded-but-finite
offsets and the block absorbs that" is always false for membership and always
true for containment, and the two must be separated before any coding or
family design is committed.

**Measured (2026-08-03):** the claim fell to three chained delivered lemmas
(`Sset-out`, `+ω-out`, `Sset-trans`) in 16 probe lines before any chapter was
opened; the build it removed was priced at 1,400 lines. The general form of
K2's cofinality finding, and a sibling of D-10.

**Provenance:** `agents/tasks/archive/L3-31-P1/l3.31-p1-report.md`. Its probe, `ProbeD10.agda`, was never tracked and is absent from the tree, from the archive, and from the 283-probe index `[LJ-1.133]` built, so the report is the only surviving evidence.

### D-25. An archive goes red on its own, and pending work that needs it must be extracted first

**Rule:** An archived module is frozen, so its greenness decays the moment any
SURVIVOR it imports changes underneath it. That is legal (archived D20 says a red
archive is not a defect) and it is harmless, right up until some pending item
still needs content from the archived chapter: at that moment the cheapest
route to that content, typechecking the archived file against an explicit
include path, is gone, and it cannot be repaired because archived files are
never edited. **Before archiving a chapter, name every unstarted item that
still consumes it, and extract what they need first.** "Nothing imports it"
is the test for whether a chapter can leave the tree; it is NOT the test for
whether the chapter is finished being useful.

**Measured (2026-08-06):** `[L3.32-T122]` archived `L.Rud.StepInL` on the
correct and verified ground that nothing outside the `Everything` index
imported it. Twenty-six minutes later `[L3.32-T124]` sealed `left` opaque in
`L.Rud.Images`, a survivor, which was the whole point of that dispatch and
removed 70.3 s. `L.Rud.StepInL` unfolds `left`'s body at three sites
(`archive/src/2026-08-07-arm-a/L/Rud/StepInL.lagda.md:941, :959, :976`), so the archived file
stopped typechecking: `agda -i archive/src/2026-08-07-arm-a -i src` exits 42 on
`⟨ v ∈ˢ left (fst (lookup bk δ)) ⟩`. The `below-lim` gate needs exactly three
objects from that chapter (`values∈L`, `stepSet∈L`, and the op graphs
`graphOf`/`graph-out`/`graph-in`, recorded in `agents/tasks/archive/L3-32-T90/l3.32-t90-report.md`),
so a gate that could have run against the archive for free now needs a
scratch tree carrying `[T121]`'s six-line `left-compute` bridge.

**The cost here was small** because the bridge was already measured and the
gate is a throwaway probe. It is recorded because the general case is not
small: the same two dispatches in the same order, with a consumer whose
repair had NOT been measured, would have left pending work with no route to
content that is frozen by ruling.

### D-26. A well-founded key on a tower needs generation data, or it needs syntax

**Rule:** When a route must well-order a cumulative tower's stage, ask first
what the stage's members CARRY. A stage built as the values of finitely many
total operations carries its own generation data, so a well-founded key exists
with NO syntax at all: the operation index, then the arguments, ordered
recursively. A stage built as a definable power carries nothing: its members
are sets, not constructions, so the only well-founded key is the DEFINING
FORMULA, and that single choice drags in codes, an order on codes, and
satisfaction. **The difference is not a matter of technique or taste, and no
amount of cleverness moves it**: the syntax-free candidate on the definable
side, least symmetric difference, is refuted by an explicit descending chain
(`Xₙ = {n, n+1, ...}`).

**Measured ([L3.32-T203], 2026-08-08):** pricing both shapes from the rewrite
side, the crossing route costs 5,880-6,860 naive marginal and the
order-supplier route costs 10,000-11,000. Not crossing costs about +4.1k
naive. The campaign had carried the question as an open architectural
preference for four days; it is a structural fact about the two towers.

**When it bites:** any route decision that moves a well-ordering between a
rud-style tower and a definability-style tower, in either direction. It is
also the reason `L ⊨ AC` on the rud route pays for a bridge at all.

**Provenance:** `agents/tasks/archive/L3-32-T203/l3.32-t203-route.md` sections 1 to 3;
`src/L/Rud/Order.lagda.md:329-332`; `src/L/Choice/Order.lagda.md:184-187`.

### D-27. "No code consumer" identifies a dead helper, never a dead result

**Rule:** A deletion sweep may use "no code consumer" to find a dead HELPER. It
may not use it to find a dead RESULT. Three classes fail the test and must be
kept, whatever the grep says.

1. **A chapter's stated result.** If the chapter's opening or its recap
   advertises the property, deleting the proof leaves the chapter asserting
   what it no longer proves.
2. **The readings of a seal.** An `opaque` definition plus its unsealing
   lemmas are ONE unit. Delete the readings and the definition survives as a
   seal nobody can open, which is strictly worse than deleting both.
3. ~~**A name a recorded MEASUREMENT cites.**~~ **CLASS 3 IS WITHDRAWN, same
   day, by the owner's argument.** Repoint the citation at the commit where
   the name was last green and delete the code. `dev/ARCHIVE.md` already
   accepts a commit as provenance, and `git show <sha>:<path>` re-runs the
   measurement. **Live code buys one thing here and it is less than it
   looks:** `make check` re-verifies it continuously, so a compiler upgrade
   that invalidated the figure would surface. But a tree holds the CHEAP form
   of a measured trap, never the expensive one, so the continuous check
   confirms the half nobody doubts and never exercises the wall. Preserving a
   measurement is not a reason to keep code in `src/`.

**The operational test, which is cheap:** before deleting, read the chapter's
first paragraph and its recap. If either names the result, stop.

**Measured (`[LJ-0.4m]`, 2026-08-10):** a re-scan deleted 68 lines on the
no-consumer criterion, correctly by that criterion, and 51 of them were
reverted. `src/L/Choice/Step.lagda.md` lost 36 lines of end-extension
machinery while keeping prose that both ASSERTS the property and MEASURES what
it cost, "one path-induction lemma of a dozen lines, one line for the
agreement". The chapter's own opening calls that property the one "the rest of
the part needs". `src/L/Choice/Stage.lagda.md` lost `defStage-ord` and
`defStage-suc`, the only two openings of `defStage`'s seal.

**Class 3 was proposed on a fourth name and then REFUTED on it the same day.**
`L.Choice.Name.denote-table` was held back because Rule 20 cites it as that
law's measurement. The owner asked why a law that is MORE GENERAL than its
instance needs the instance alive. It does not: Rule 20 now carries the
commit, and the lemma is deleted. **Keep the two classes that survived and
distrust any argument of the form "a document mentions it".**

**The cost of the wrong direction is asymmetric, which is why this is a rule
and not a preference.** Deleting a live helper fails the typecheck in seconds.
Deleting a dead result typechecks green and is found only by reading prose.

**When it bites:** any compression campaign under a line target. The pressure
runs one way, and the criterion that produced the campaign's best result
(`[LJ-0.4a]`, minus 240) is the same one that over-reaches here.

**Provenance:** `agents/tasks/archive/LJ-0-4M/lj-0.4m-report.md` sections 2 and 3;
`agents/tasks/archive/LJ-0-4M/LJ-0.4m.md` rule 2, which named class 1 and missed class 2;
commits `ab99b23` and `9c6d036`; `dev/LESSONS.md:568-581` for Rule 20.

### D-28. A kit's break-even is set by its PARAMETER count, not its line count

**Rule:** Price a shared kit by how many parameters it takes, not by how many
lines it holds. **Before building, find the boundary where the parameter count
drops, and share only the low-parameter side.** The high-parameter side stays
at its sites, however much of it there is.

**Why the line count misleads.** A kit's lines are paid once. Its parameters
are paid at EVERY site, twice over: once in the declaration and again in the
per-site glue that supplies them. So a kit's true cost grows with parameters
times sites, and its saving grows with sites alone. **Past a small parameter
count the arithmetic can never close, and adding sites makes it worse rather
than better.**

**Measured (`[LJ-0.4f]` and `[LJ-0.4n]`, 2026-08-10, the same material on the
same day):**

| | parameters | kit lines | sites | net |
|---|---:|---:|---:|---:|
| whole assembly | 11 | 208 | 2 | **+4** |
| shape half only | **1** | 53 | 5 | **-104** |

The bigger kit lost. The smaller kit, over MORE sites, won by 108 lines.
`[LJ-0.4f]`'s own report named the cause without drawing the rule from it:
"the parameter declarations plus per-site glue absorbed the savings".

**The split is found by asking what each half MENTIONS.** Here the shape half
mentions only the step; the induction half mentions the recursion's value, its
uniqueness and its motive, which is the whole eleven-parameter telescope. The
literature drew the same line first: Sacks and Zeman state their Lemma 1.10 and
1.11 as two objects with one FORM, so sharing the form captures what the
sources state twice, and sharing the value would unify what they keep apart.

**The corollary that saved this block: host the kit where a copy already
lives.** A new master costs about 26 lines of preamble before it saves
anything. `[LJ-0.4n]` put its kit INSIDE `L.Coding.Sequence`, which already
held one of the five copies and already paid that preamble.

**When it bites:** every extraction. Five kit blocks in this campaign measured
net POSITIVE (B +24, E +19, G +49, F +4) and the only one that paid took one
parameter.

**Provenance:** `agents/tasks/archive/LJ-0-4F/lj-0.4f-report.md`; `agents/tasks/archive/LJ-0-4F/lj-0.4f-review.md` section
6; `agents/tasks/archive/LJ-0-4N/lj-0.4n-report.md`; commits `3269da5` and `dd59127`.

### C-30. A compression block is gated, and the gates have a home

**Rule:** Every compression or extraction block carries the same gates. They
are listed here ONCE so a brief cites them instead of re-deriving them.

1. **Count the sites by grepping the MECHANISM tree-wide, before writing the
   kit.** Report the grep and the per-site line counts. Never trust a survey's
   line range.
2. **The break-even gate, before wiring the SECOND site.** Build the kit,
   typecheck it, convert one site, measure the saving, and compute break-even
   as kit lines over that saving. If break-even exceeds the site count, stop
   and report the three numbers.
3. **The staging gate.** Write the projection into the report BEFORE the
   second site, never after.
4. **Sum the seconds, including the kit's own**, at tree level. A new module's
   check time is a cost the tree pays forever.
5. **The stop trigger, three cases.** Seconds rise, a consumer must unfold
   what it did not before, or the measured net cannot reach the floor. The
   third is a refusal with a number and it is a full deliverable.
6. **A chapter must remain a chapter.** A file left as a re-export stub is a
   failed block, not a compressed one.
7. **The twice-today rule.** A shared home may hold only lines that exist at
   least twice in TODAY's tree. Moving a once-occurring line is relocation.
8. **The noise rule.** A per-file delta under 0.5 s or under 5 percent,
   whichever is larger, is noise: report it flat. Never report a verdict word
   where a number fits.
9. **Kit preservation.** A refused kit moves to its task's own directory,
   `agents/tasks/<TASK>/`, beside the brief and the report that produced it.
   Never to `/tmp`, never to `_build/`, and never to deletion. **`_build/` was this
   gate's own answer until the `[LJ-0.4]` closeout found it wrong:** the path
   is in `.gitignore` and `make clean` runs `rm -rf _build`, so four kits sat
   one command from the fate that already took E's `Walk` and G's `Lex`. An
   artifact a routine command destroys is not preserved.

**Measured:** nine blocks ran in `[LJ-0.4]` and eight bands were tested. Gates
1 and 4 did not exist for the first eight and both cost real money: `[T208]`'s
survey misread `L.Choice.Before` and never counted `L.Coding.Sequence`, and
`[LJ-0.4f]` measured plus 1.50 s for its kit and never entered it in the
decision. Gate 2 was worded "before any wiring" until `[LJ-0.4f-R]` observed
that it cannot be run, because it needs a measured per-site saving.

**Why it is here rather than in a brief.** These gates lived only in
`agents/tasks/archive/LJ-0-8/lj-0.8-review.md` 7.1 and in whichever brief last pasted them. A rule
whose only home is a report is found by the person who already knows it. The
GCH wing will compress too.

**When it bites:** any brief that proposes to share, extract, fold or
de-duplicate. Cite this entry; do not re-derive the list.

**Provenance:** `agents/tasks/archive/LJ-0-8/lj-0.8-review.md` 7.1; `agents/tasks/archive/LJ-0-4F/lj-0.4f-review.md`
section 7 items 5 to 7; `agents/tasks/archive/LJ-0-4N/LJ-0.4n.md`, the first brief to carry
all nine.


### C-31. A budget from a PROJECTED size is divided by the projected size, never by today's

**Rule:** When a threshold gives a total budget over a projected size, judge a
candidate against the PROJECTED denominator. Dividing by what is built today
reads a partly-built artifact as over budget, and the error grows as the
fraction built shrinks.

**Measured (`[LJ-1.17-R]`, 2026-08-10):** DD24's bar over a projected GCH wing
of 7,553 to 11,197 lines gives a seconds budget of 99.6 to 147.7 s. The
archived square law is 1,283 in-fence at a measured 41.36 s. Divided by the
wing's line count **that day**, 2,677, it read **0.0177 s/line, 1.34x the bar,
FAIL**. Divided by the projected count, crediting the residue with 0.0065
s/line, which is HIGHER than any wing module measured at the caliber:

| wing | seconds | s/line | verdict |
|---:|---:|---:|---|
| 7,553 | 82.12 | 0.0109 | 0.82x PASS |
| 11,197 | 105.80 | 0.0094 | 0.72x PASS |

**The verdict inverted.** The wing fails only if its residue runs above 0.0093
to 0.0107, which is 1.8x the measured `StageCardinal` and 8.7x the measured
`FOL.Count`.

**THE SAME ERROR STOOD IN THREE PLACES AT ONCE**, which is why this is a law
and not a note: in `dev/ledger.toml`, in the brief the orchestrator wrote from
it, and in the return that propagated it back. A wrong denominator in a ledger
looks exactly like a measurement.

**The instrument had already said so.** `scripts/check-ratio.py`'s own header:
"THE PER-MODULE FLAG IS ADVICE; THE AGGREGATE IS THE JUDGMENT. A single module
may sit above the bar for a reason the wing as a whole pays back." A
per-module rate was never the verdict.

**When it bites:** every DD24 judgment before the wing is finished, and any
future budget derived from `gch_wing_apriori` or from a `[[remaining]]` row.

**Provenance:** `agents/tasks/archive/LJ-1-17/lj-1.17-review.md` section 1; `agents/tasks/archive/LJ-1-17/lj-1.17-report.md`;
`dev/ledger.toml`'s `gch_wing_seconds_budget` block, corrected in the same
commit.


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

**Appended (2026-08-03):** agent report filenames collide across goal
codes: `agents/tasks/archive/P1/p1-report.md` named both the [L3.30-P1] probe report (the
cited provenance of I-2, D-7, C-11) and the [L3.31-P1] batch's directed
output; a brief-directed overwrite of law-book provenance is a blind spot no
linter covers. Convention adopted: agent reports carry the goal code
(`agents/tasks/archive/L3-31-P1/l3.31-p1-report.md`), and a batch finding its path occupied writes
beside it and says so. Provenance: `agents/tasks/archive/L3-31-P1/l3.31-p1-report.md`.

### C-9. The graft entry: graft retractions as explicit projections

**Rule:** Write graft retraction equations with explicit `fst`/`snd`
projections, not `let`/`where` bindings, so the retraction proofs can be direct
path lambdas.

**Measured (M5a):** the brief's `let (cs' , rest) = graftL cs ps in …` form made
the definitional-equality checks not terminate inside the budget; the same
content as explicit projections (`(node … (fst (graftL cs ps))) , snd (graftL cs ps)`)
let the retraction proofs be written as direct path lambdas.

**Provenance:** `agents/tasks/archive/M5A/m5a-report.md` (Deviation in the graft equations);
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
above 25%. A watchdog (`scripts/agda-watchdog.sh`, restart it each
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

### C-13. Direction discipline for rewrites and conversions

**Rule:** Rewrites and conversions have directions; name them before writing
the step (two laws, measured below).

**The two laws** (measured):

- **[A] subst: spell P and both endpoints, decide element vs level**:
  `subst P p` moves `P x → P y` along `p : x ≡ y`; in membership rewrites
  decide whether the path acts on the element or the level, and spell `P`
  and both endpoints in block equalities. Measured: four early flips in G6,
  two `sym`-direction errors in R2a, the stable pattern in R2c's twelve
  trans cases (2026-08-02/03).
- **[B] The small/big membership conversion has a direction**: the
  small/big membership equivalence (`a ∈ b ⇔ a ∈ₛ b`) has `.fst`
  big-to-small and `.snd` small-to-big; check it, the error text is the only
  witness. Measured: one fibre step in `+ω-out` was written the wrong way
  and only the error text exposed it (G6, 2026-08-03).

**Provenance:** `agents/tasks/archive/G1G6/g1g6-report.md`; `agents/tasks/archive/R2A/r2a-report.md`;
`agents/tasks/archive/R2C/r2c-report.md`.

### C-14. A restated helper, a missing export, or an unnameable private helper is a delivery defect

**Rule:** A helper written a third time, a case equation the definition site
fails to export, or a private helper a consumer's proof needs is a delivery
defect, not a coincidence (two laws, measured below).

**The two laws** (measured):

- **[A] Host once, export the bottom equation at the definition site**:
  host the arbitrary-domain reader once and export the bottom equation at
  the definition site. Measured: `prAt′` written three times (57 lines, no
  risk, the third copy the signal); `Sset-zero` missing from Step's exports
  cost a 6-line local proof at the base block (r5b, K1, 2026-08-03).
- **[B] Re-export what a consumer's proof needs**: a private helper a
  consumer's proof needs must be re-exported as a public lemma; privacy is a
  name-and-reduction wall, not a hygiene marker. Measured:
  `rightSlice`/`sndExtract` were unnameable and blocked F11-F14's junk facts
  (r2c).

**Provenance:** `agents/tasks/archive/R5B/r5b-report.md`; `agents/tasks/archive/K1/k1-report.md`;
`agents/tasks/archive/R2C/r2c-report.md`.

**Appended (2026-08-03):** a missing export breeds MORE than one re-proof:
`Sset-zero`'s absence from Step's exports produced two independent local
derivations in BaseBlock (only one of which any report had spotted) and a
third in Bridge. When filing a missing export, grep the FACT, not the name.
Provenance: `agents/tasks/archive/POLISH2/polish2-report.md`.

**Appended (2026-08-04):** third instance class: four `V.Coding`
pair/singleton helpers are `private` and were re-derived a third time by the
GLp probe. Provenance: `agents/tasks/archive/L3-31-GLPROBE/l3.31-glprobe-report.md`.

### C-15. Close out with a consumer probe; the in-file module beats the probe, then the probe still earns its keep

**Rule:** For any batch that exports into a fixed telescope, apply the
consuming module inside the exporting chapter (making the telescope match a
typechecking obligation), then run the scratchpad probe, since it is the
only place the module parameters get concrete.

**Measured (2026-08-03):** the 25-line `Bridge.Reduce` probe caught
`f3ad704`'s mid-batch telescope change in 1.7 s; K4's in-file application
plus probe exercised `slot-empty` at `A := ∅`.

**Provenance:** `agents/tasks/archive/R5D1/r5d1-report.md`; `agents/tasks/archive/K4/k4-report.md`.

### C-16. A wall that survives the obvious seal is a mis-diagnosis: stop sealing, start bisecting

**Rule:** After a seal fails to move a wall, stop sealing and start bisecting
the elaboration; report the failed seal as unmeasured rather than
retro-fitting credit when the real cause is found.

**Measured (K3, 2026-08-03):** the textbook pr-seal was wrong in K3, costing
one full rewrite and three wall events before bisection found the
branch-type cause.

**Provenance:** `agents/tasks/archive/K3/k3-report.md`.

### C-17. Record "two routes are circular", never "the base case is circular"

**Rule:** When two routes to a base case are circular, the finding to record
is "two routes are circular", never "the base case is circular"; the third
route is often the textbook's.

**Measured (R5a, 2026-08-03):** R3c's recorded circularity was a scoping
artefact; the classical construction is extensionality relativized to
`p ∪ ⋃p`, 95 lines with one `dne` per direction.

**Provenance:** `agents/tasks/archive/R5A/r5a-report.md`.

### C-18. Generalize a working frame from the free variable to an index

**Rule:** When a frame works "at the free variable", generalize it to "at an
index" (the target term becomes `var k`, shifted by the binders) and keep
the original as the zero case; the generalization is a mechanical edit that
buys every deeper binder.

**Measured (R5b, 2026-08-03):** `prDesc` → `prDescAt k` made F3/F4's six
cases green on the first check; all de Bruijn arithmetic lives in one
20-line definition.

**Provenance:** `agents/tasks/archive/R5B/r5b-report.md`.

### C-19. Read the exit code, not the log tail

**Rule:** Read the exit code, not the log tail: unsolved constraints exit 42
while the tail otherwise looks like a clean check.

**Measured (r1b, 2026-08-02):** UnsolvedConstraints exits 42 while the tail
looks clean.

**Provenance:** `agents/tasks/archive/R1B/r1b-report.md`.

### C-20. Never write `∈ˢ ⋃` / `⊆ ⋃` directly; bind the union term

**Rule:** Never write `∈ˢ ⋃` / `⊆ ⋃` directly; bind the union term.

**Measured (r2b):** Agda's mixfix parser rejects an infix operator applied
to a prefix `⋃` operand.

**Provenance:** `agents/tasks/archive/R2B/r2b-report.md`.

### C-21. Telescope types may only use level-generic imported names

**Rule:** Telescope types may only use level-generic imported names; inline
level-parameterized predicates into the header, or take the subject
parameters in an inner `module _` block.

**Measured (r2b):** a level-specific imported name
(`L.Constructible.isTransV`, importable only with `{ℓ}` applied) is
invisible inside the module header.

**Provenance:** `agents/tasks/archive/R2B/r2b-report.md`.

### C-22. A dispatched agent writes its deliverable incrementally, never at the end

**Rule:** When an agent's deliverable is a file, the brief must require it
WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer
lands. An agent that researches for its whole budget and leaves the writing to
the end returns nothing when the budget runs out, and its research dies with
it. A partial dossier is a real deliverable; an unwritten perfect one is not.

**Measured (2026-08-04):** a literature-fetch agent spent its entire run
locating its sources correctly (it identified the right arXiv identifiers,
corrected a wrong title carried in its own brief, and established that shell
network was blocked while the search tools had access), then died before
writing a line. Zero output. The re-dispatch carried those findings forward in
its brief and made incremental writing a binding constraint.

**Measured again (2026-08-07), and this time the rule was IN the brief and
still failed, which is the part worth having.** `[L3.32-T131]` was briefed
with C-22 binding and it did create its skeleton first. Then it ran two hours,
grew a 17 MB log, and left that skeleton at 42 lines with every section empty,
because it had fallen into a loop: **1,622 file-create diffs for the same
scratch diagnostic file**, grinding one type puzzle. Meanwhile its probe held
`chainLimit` and `segLimit₀`, which are both halves of what it had been sent
for, unreported and one budget-exhaustion away from being lost.

**So the citation is not the enforcement.** A brief that says "write
incrementally" catches the agent that forgets; it does nothing about the agent
that stops making progress and therefore has nothing to write. The two look
identical from outside: a live process and a growing log.

**Enforcement point, added the same day:** `dispatch.py status` now flags a
live agent on two independent signals, since either alone lies. First, the
deliverable is untouched for 30 minutes while the log keeps moving. Second,
the log repeats one file-create diff 40 times or more, which is the signature
of a loop rather than exploration. It reports and never kills, because a
stalled agent is often recoverable: T131's was.

**Provenance:** `archive/dev/JOURNAL-archived.md:2356` for `[T131]`, and
`archive/dev/TASKS-archived.md:47` and `:166` for both task rows. The journal
was archived on 2026-08-09; a law whose provenance cannot be opened cannot be
checked, which is the whole point of recording one.

### C-23. A consumer scan counts same-file instantiation bodies, or it lies

**Rule:** A definition-level consumer scan that walks cross-file references
misses the SAME-FILE instantiation class: a module instantiated later in its
own file (a tower, a `ConcreteS`) consumes names in its body, and whatever
that instantiation exports feeds every importer downstream. A name with "no
external consumer" can still be load-bearing for the file's own exported
surface. Every movability verdict must check the file's own later bodies
before the cross-file walk means anything.

**Measured ([L3.32-T160], 2026-08-08):** T155's name-flow scan marked 429
lines of `L.Rud.Step` movable with "no AC-side consumer"; the split agent
found `ConcreteS` (Step:935) consumes all four headline names in-file, and
its exports feed `L.Rud.Bridge`, an AC root. The split would have needed a
cyclic import or a sixty-name telescope. The stop cost one dispatch; a
landed wrong split would have cost the naturalness condition.

**Provenance:** `agents/tasks/archive/L3-32-T160/l3.32-t160-report.md` sections 1 and 7.

## Adding an entry

Take the next free ID under the series (P-o, R-41, T-3, I-10, D-27, C-24), cite
the source in the entry, and keep the evidence column to measured numbers. When
a new measured wall joins a class an entry already covers, extend that entry's
evidence and provenance instead of minting a duplicate. If a lesson cannot be
sourced, it is not entered; it is surfaced to the owner instead.

### P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type

**The law.** Being about a concrete position is not what costs. Naming a
transparent construction in a statement's TYPE is. If the tower's stage values
are `opaque` upstream, a theorem may quantify over, hypothesize about and
conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and
nothing unfolds. If instead the type mentions a transparent presentation, such
as `⟪ sucV (γp p) ⟫` where `⟪ a ⟫` unfolds to a kernel-quotient tower, then
every check of that statement re-normalizes the tower, and no proof-body or
consumer-side fix can reach it.

**The measurement, and it is a controlled pair inside one repository.**
`L.Rud.HF` proves content genuinely about the first limit stage at concrete
positions (`ord∈HF→∈ω`, `src/L/Rud/HF.lagda.md:224`; `stage∈HF`, `:263`) and
checks at **0.030 s per line with zero `opaque` of its own**, because `Sset` and
`Lset` are sealed upstream (`src/L/Rud/Hierarchy.lagda.md:219`,
`src/L/Constructible.lagda.md:221`). `L.Ordinal.SquareLaw` states at concrete
positions carrying `⟪ ⟫` and checks at **3.424 s per obligation, 46 times the
benchmark**, with 88 percent of it in four definitions whose STATEMENTS carry
the tower (`[L3.32-T88]`). Same tree, same era, same kind of subject matter,
two orders of magnitude apart.

**A CURE DOES NOT TRANSFER BY ANALOGY. Re-measure it at every new site.**
This project tried three transplants in one day and all three failed, while the
one transplant guided by a diagnosed ROOT CAUSE succeeded:

| cure | where it was measured | transplanted to | result |
|---|---|---|---|
| the abstract-carrier discipline | the retiring subtree, 0.074 s/obligation | `SquareLaw`'s chase | **heap exhausted at `-M8g`, twice** |
| the same | the same | `Condensation`'s clauses | **no movement at all**, 203.3 s against 203.5 |
| the `Bridge` read-lemma seal | `Bridge`, 939 s to 199 s | `SquareLaw`'s `h₀-inj` | **neutral transparent, 1.9x SLOWER sealed** |
| R-38's seal-at-birth, anchored at 25.7 s per unsealed invocation | `r5a` | `L.Rud.Images`' `right-spec` | **zero**: 52.9 to 53.2 s, and `Step` 28.8 to 28.2 |
| `[T102]`'s telescope lift | `SquareLaw`'s `h₀` pair, 374.3 s to 82 ms | `Condensation`'s three pieces, argued by `[T104]` from resemblance, **unmeasured** | **REFUTED by `[T106]`**: piece 1 made the module WORSE, 204.7 s to 308.8; piece 3's cost MOVED rather than went; piece 2's export-preserving form is worse than the control |
| the abstract restatement, **redirected by root cause** | `[T98]`'s diagnosis, not by analogy | `SquareLaw`'s chase, abstracting the SOURCE rather than the target | **1.28 s where the analogy-guided form had exhausted 8 GB after 26 minutes** |

**Five transplants on 2026-08-06, four failed, and the four failures share one
shape: somebody reasoned that a cure should apply and did not measure it.** The
fourth is the sharpest, because the ORCHESTRATOR endorsed it: `[T104]` argued
in prose that `[T102]`'s lift would carry to `Condensation`, ran no Agda, and
said so honestly; the orchestrator recorded the earlier verdict as overturned
before anything was measured, and `[T106]` then measured it and restored the
original. **A design recon that runs nothing produces a hypothesis, and writing
it into the register as a finding is the error, not the recon.**

The last row is the point. `[T88]` abstracted by analogy and left the concrete
presentation in the telescope; `[T99]` abstracted where the diagnosis said the
cost was, and the same theorem went from a heap wall to 1.28 seconds. **An
expected figure anchored on a comparable is a HYPOTHESIS, not a price.** In the
R-38 case the rule's own text already said "sealing only moves the cost"
(`dev/LESSONS.md:835`), and the estimate contradicted the rule it cited.

**THREE DISEASES, NOT ONE, each measured on a different module of this tree,
and each needing a different cure. Applying the wrong one is worse than doing
nothing.**

| disease | where the cost is | the test that identifies it | measured on | cure |
|---|---|---|---|---|
| **consumer-bound** | consumers re-normalize what a read lemma stopped short of | the hot rows carry OTHER modules' names | `Bridge`, 939 s | seal the read lemma where consumers use it. 4.7x, then a floor |
| ~~**statement-bound**~~ | ~~the hot definition's own TYPE names a transparent construction~~ | **WITHDRAWN 2026-08-06.** The one exemplar was `SquareLaw`'s `h₀-inj`, and `[L3.32-T102]` showed the experiment that classified it was CONFOUNDED: `[T88]`'s "gutted" body still passed four concrete memberships `fst∈sucmax {a , b} {p} pr` at the tower position as ARGUMENTS, so the conversion checks stayed inside the row. Moving those into module parameters removed the term entirely, 374.3 s to 82 ms. **The family is body-bound.** No module in this tree is currently known to be statement-bound, and the category is kept here only as a hypothesis to be re-earned by a properly gutted experiment. | n/a |
| **body-bound** | a body elaborates delivered machinery at a concrete argument | gut the body: the cost MOVES to wherever the concrete application went, and the total is unchanged | `Condensation`, `ambientOnly-from` 128.5 s to 0 ms with 131.1 s appearing in the lemma it now calls | only an interface change: restate the obligation so the concrete application is not built |

**The gutted-body experiment separates them in one run**, and it is cheap:
replace the hottest definition's body with the cheapest thing that still
typechecks, and watch where the seconds go. Moves with the application: body.
Was never there but in the consumers: consumer. Survives a PROPERLY gutted
body: statement, and nothing in this tree has yet earned that verdict.

**GUT THE ARGUMENTS, NOT JUST THE SHAPE. This is the whole trap and it cost
this project a wrong diagnosis that stood for a day.** A one-line body that
still PASSES concrete applications as arguments has not been gutted: the
conversion checks are still billed to that row, and the definition reads as
statement-bound when it is body-bound. `[T88]` reduced `h₀-inj` to a one-line
application of a free generic lemma and concluded from its surviving 190 s
that no body-side cure could reach it; `[T102]` then reached it, 374.3 s to 82
ms, by moving the same four concrete memberships into module parameters where
they are checked once at a neutral position. **The test is not "is the body
short" but "does any concrete application remain anywhere in the definition,
including inside its arguments".**

**The diagnostic that tells you which disease you have, from `[L3.32-T97]`.**
Read the per-definition profile and ask **whose names the hot rows carry.**
`Bridge`'s hot rows named OTHER modules: a consumer-side disease, cured by
sealing the read lemma where consumers use it, 939 s to 199 s (P-k).
`SquareLaw`'s four hot rows are **its own definitions**: a definition-side
disease, and `[T88]` proved by experiment that the consumer-side cure cannot
touch it, reducing a hot body to a one-line application of a free generic lemma
and still paying 190 s. **Applying the wrong cure is not merely useless: the
sealed variant ran at least 1.9 times SLOWER.**

**The floor this law does not remove.** A tower's computation rule must relate
a stage to its body at least once, and that once is paid wherever it is stated.
`Bridge`'s residual 199 s is 149.5 s of exactly this (`γ-compute-full` 94.9 s,
`towerStep≡+ωU` 54.6 s), which is why its seal converted an eightfold repeat
into a single payment and then stopped. **Sealing buys the repeats, never the
once.** Expect a floor and price it rather than chasing it.

### P-k. A read lemma is stated where its consumers use it, not where its proof ends

**The law.** When a lemma exists so that consumers can rewrite with it, its
stated right-hand side must be **the form the consumers actually need**, not the
form the proof happened to reach. If it stops one layer early, every consumer
re-normalizes the missing layer, and the same conversion is paid once per
consumer instead of once in total. **Absorb the last layer into the lemma and
seal it**, so the normalization happens exactly once, behind an `opaque`.

**The measurement.** `[L3.32-T86]` profiled `L.Rud.Bridge` at **939 seconds**
and found **95 percent of it concentrated in one family**. (That is the share of time IN the family. The share the fix actually REMOVED was 79 percent. Confusing the two cost this project a wrong freeze threshold on 2026-08-06, so the entry states both.) `γ-compute`'s stated type ended at
the tower body rather than at `+ω (U α)`, the form its consumers use, so each of
about ten `subst` consumers re-normalized the union tower inside `towerStep`,
paying the same conversion roughly eight times. The fix was **six lines**: an
`opaque` `towerStep≡+ωU` proved by `refl`, composed into `γ-compute`. Measured
**939 s to 199 s**, reproduced independently at 199.53 s (`[L3.32-T87]`,
`src/L/Rud/Bridge.lagda.md`). **767 seconds for six lines, with no mathematical
content whatsoever.**

**Why this needs its own entry when R-36 and R-38 already exist.** Those two say
seal an unfolding read lemma, and seal it at birth. Both were followed here:
`γ-compute` WAS sealed. The seal was in the right place and the **statement was
in the wrong place**, which neither entry reaches. Sealing the wrong form just
makes the wrong form cheap to reach and leaves the real cost outside the seal.

**Why no gate can catch this, which is the part that matters.** A module with
this defect **typechecks correctly**. `make check` goes green, both linters are
happy, no obligation fails. It is not a wrong proof, it is a proof that costs
eight times what it should, and the project had no instrument that could see the
difference. `L.Ordinal.SquareLaw` reached **0.94 s/line and 44 percent of the
entire tree's check time** without tripping anything, and it took a profiler
months later to find out. `scripts/check-timing.py` exists because of this
paragraph; it is the only gate here that can fail a module for being expensive.

**What the cheap tree actually does, read out of it by `[L3.32-T93]` before it
is archived.** Its two largest files, `L.Godel.Closure` (3,490 lines, 102.1 s)
and `L.Godel.Levels` (2,775 lines, 60.3 s), contain **zero `opaque`, zero
`postulate`, zero `TERMINATING`**, and still check at a fraction of the hot
modules' rate. So sealing is not the cause. What they do instead: everything
lives in a module-parameterized block at an abstract carrier
(`module _ (A : V ℓ) where`, `src/L/Godel/Closure.lagda.md:135`,
`src/L/Godel/Levels.lagda.md:133`), statements are at variable indices over
that carrier, and every `subst` runs along a locally proved equality at that
same abstract carrier, so **no conversion ever normalizes a concrete
presentation**. In one sentence: **statements at abstract carriers make sealing
unnecessary, and sealing is what the trunk reaches for where the statement
discipline was already broken.**

**The uncomfortable corollary, recorded because it is the real lesson.** The
subtree that archived D18 retires costs **0.013 s/line over 26,483 lines**; the surviving
trunk cost 0.104. The retiring chapters were not better mathematics, they simply
**stated at abstract carriers and variable indices so nothing re-normalized**,
which is P-h's discipline billed in seconds instead of lines. The newer work
lost that habit and nobody noticed for months. **A discipline that is only
visible in a measurement nobody takes will be lost, and it will be lost in the
direction of whatever is quicker to write.** This is the finding that produced
D30's freeze, and the reason its exit condition includes recording the practice
before the code that carries it is archived.

### P-m. The check-cost rate is a content-class certificate, and instantiation is the expensive class

**Rule:** Seconds per line identify a block's CONTENT CLASS before any
profile is run, and line count alone predicts nothing. **Parameterized
content**, whose definitions check at bound variables under a module
telescope, checks near **0.01 s per line**. **Instantiation content**, which
states object-language formulas at a concrete carrier, proves decodes that
walk the satisfaction relation, and places concrete sets into deep stages,
checks near **0.22 s per line** at this site. The two classes differ by
twenty to sixty times, so a build brief that projects seconds from a line
count without naming the class is projecting nothing. **Plan the split
between blocks on the class boundary, not on the line count.**

**Measured ([L3.32-T219], 2026-08-08, over ten episodes):** the same master,
the same author and the same cited laws produced both rates. `L.Rud.BelowLim`
block 1, 604 lines of parameterized story and segment machinery, checks in
6.30 s cold, slowest definition 130 ms. Block 2, 948 lines instantiating the
first limit, costs about 210 s, and 66 percent of the profile sits in ten
decode and placement definitions.

**Provenance:** `agents/tasks/archive/L3-32-T219/l3.32-t219-seconds.md` sections 1 and 3;
`agents/tasks/archive/L3-32-T191/l3.32-t191-report.md:78`, `:86`; `agents/tasks/archive/L3-32-T195/l3.32-t195-report.md:149-155`.

### P-n. Satisfaction content at a concrete carrier is a payable floor, not a defect

**Rule:** When a proof states object-language formulas at a CONCRETE carrier
and proves their two-way decodes, the elaborator normalizes the carrier's
presentation at every such definition, and **named branches with written
types do not remove that cost**. I-5's cure applies to a missing type, not to
this; if every hot branch already carries a written type, the remaining cost
is the machinery and the profile is telling the truth. **Do not fund a cure
for it.** The admissible moves are to need less instantiation (keep content
parameterized and instantiate once), or to accept the floor and price it.

**Measured ([L3.32-T219], 2026-08-08):** `[T195]`'s profile of the below-lim
master's first-limit instantiation. `seg∈C` 37.2 s, `ψ-in` 27.0 s with its
`go` branch 17.9 s, the `out`/`bwd`/`δNum` group about 30 s, and the
`segForm-ok` and `sat` reads about 33 s. Every hot branch is a named helper
with a written type, which is why `[T143]`'s I-5 cure, worth 595 s to 27 ms
in the same neighbourhood, has no purchase here.

**When it bites:** any block that instantiates the graph layer, the story or
the segment machinery at a concrete stage. `[T217]` priced block 3 at this
rate for exactly that reason.

**Provenance:** `agents/tasks/archive/L3-32-T219/l3.32-t219-seconds.md` sections 1 and 5;
`agents/tasks/archive/L3-32-T195/l3.32-t195-report.md` section 5.


### P-o. A record field at a carrier-indexed type hangs the elaborator; use a nested Σ

**The law.** A `record` whose FIELD has a type indexed by the carrier, such as
`Formula ⟪ u ⟫ 2`, hangs Agda 2.8.0's elaborator. The identical content written
as a right-nested `Σ` checks immediately. The cost is in the record's
elaboration, not in the content: the same type as a plain definition is
instant.

**The measurement, 2026-08-09, `[L3.32-T226]`.** A minimal reproducer carrying
ONLY that one field timed out at 25 s. The `Σ` form of the same clause type
checked in seconds. The clause type therefore sits at
`Type (ℓ-suc (ℓ-suc ℓ))`, one universe above the predicate component, which is
the price of the shape and is worth paying.

**The companion trap, same measurement.** The fold's empty-list case needs a
universe-polymorphic unit, `Unit.Unit*`. The cubical `Unit` at `Type ℓ-zero`
fails the sort check, and the failure reads as a sort error in the FOLD rather
than in the unit, which is where the time goes.

**Why it is a law and not a note.** This project reaches for a record whenever
it bundles a predicate with its object formula and its two decode directions,
which is the shape of every story clause. The nested `Σ` is uglier to read and
will be "cleaned up" into a record by anyone who does not know the price.

### P-r. A fold-over-a-clause-list assembly costs about 3x the hand-written conjunction

**The law.** Replacing a hand-written right-nested conjunction and its decode
with a FOLD over a clause list is dearer at the check, by about a factor of
three, because every consumer must unfold the fold and its list to see the
type. The abstraction is good for lines and for reading. It is bad for
seconds, and at a site where seconds bind it must not be used.

**The measurement, 2026-08-09, `[L3.32-T242]`, three shapes at ONE site so the
comparison is clean.** The carrier is `Lset γ` under the same telescope in each
case.

| shape | profile ms |
|---|---:|
| hand-written decode, five clauses | 7,242 |
| hand-written decode, six clauses | 7,507 |
| clause bundle plus kit aliases, six clauses | **22,011** |

**The clause COUNT is not the driver and this is what makes the law usable.**
The sixth clause adds 0.5 s to the hand-written shape. The SHAPE adds 14.5 s.
So the cure is not fewer clauses; it is not folding.

**Where it applies.** `[L3.32-T226]` built exactly this assembly as candidate
C4 and it was kept for naturalness after measuring +72 lines and +0.85 s at
its own sites. This law does not overturn that judgment, which was made on the
line meter, but it adds the number C4 did not have: at a site where the
assembly REPLACES a hand-written decode, it costs about 14.5 s. Do not
propagate it into content that the wall gate prices.

**The tension with "write it generic" is real and is resolved by threshold.**
AGENTS.md names generic writing as the rule that has cost this project most,
and it is right for lines and for re-instantiation. P-r is the exception, and
it is narrow: a fold whose result type must be UNFOLDED by every consumer.
`[L3.32-T239]`'s carrier-generic limit clause is not this shape and measured a
saving; the clause-list assembly is.

### P-s. A slice rate is not an estimate of the content's rate, in either direction

**The law.** Timing a SLICE and dividing by its lines does not price the
content the slice came from. The error is not a bias you can correct for: it
runs both ways, because a slice either omits the expensive families or
consists of them. **Time the piece whose rate is in doubt, whole, at its own
carrier.** If the budget will not stretch to that, report the slice as a slice
and refuse to divide.

**The measurement, 2026-08-09, two probes on the same day, both against
126-line slices.**

| slice | slice rate | the content, measured whole | error |
|---|---:|---:|---|
| `[T222]`'s witness layer | 0.085 s/line | `[T240]`: 0.297 over 589 lines | **3.5x LOW** |
| `[T211]`'s Part I | 0.0603 s/line | `[T249]`: 0.0113 over 1,343 lines | **5.3x HIGH** |

`[T222]`'s slice lacked three of the four content families, 52.8 percent of
the check, so it under-priced. `[T211]`'s slice was the instantiation tail of
a body that is otherwise PARAMETERIZED, so it over-priced: the bulk checks at
P-m's parameterized rate and the slice did not contain the bulk.

**What this cost and what it bought.** The low error carried a whole campaign's
block A projections and produced a stop-line no correct build could meet
(`dev/ledger.toml`, `block_a_breakeven_lines`). The high error held the
largest remaining AC row at TOO CLOSE TO CALL for a day when it FITS at every
caliber. Both were repaired by building the piece whole.

**The tell.** Ask which content class the slice belongs to (P-m), and whether
the WHOLE body belongs to the same one. A slice drawn from a body of mixed
class prices neither part. Both failures here are that single mistake.

### P-t. The content class follows the FORMULA, not the carrier: a built tree unfolds, a sealed carrier does not

**The law.** P-m says the check-cost rate certifies a content class. This
says what decides the class. **It is not whether the carrier is concrete or
variable. It is whether the object-language FORMULA is a built tree or a
telescope hypothesis.** Satisfaction is a transparent recursion over the
formula's structure, so it unfolds the tree at every use. A sealed carrier
never unfolds and costs nothing extra, however concrete it looks.

**The measurement, 2026-08-09, `[L3.32-T255]` reading `[T240]`, `[T241]` and
the delivered block 1.** The same mathematics, stated two ways:

| | rate | the formula |
|---|---:|---|
| block 1, `src/L/Rud/BelowLim.lagda.md` | **0.0104 s/line** | the walks are HYPOTHESES in a telescope |
| the carried sequence, `[T240]` | **0.297 s/line** | the tree is BUILT: the fold, its rename, the decode |

**28 times, for the same content.** And the cost is type elaboration, not
proof: `[T241]` measured three ONE-LINE decode aliases at 36,647 ms.

**Why it matters more than it sounds.** The campaign spent two days reading
0.297 as "the carrier is concrete, so this is instantiation content", and
looked for a cure by moving to a variable carrier. `[T240]` then measured a
variable carrier at 0.297 anyway and nobody could explain it. This law
explains it: `Lset ξ` was sealed all along, and the expensive object was the
formula tree beside it.

**What it licenses.** Seal a BUILT formula opaque wherever its consumers do
not need to see inside, and prefer stating a walk as a telescope hypothesis
over building it, when the consumer can supply it. Both are seconds levers
and neither is a line lever (P-q).

### P-q. A line lever and a seconds lever are different levers; dedup buys lines, not seconds

**The law.** Removing DUPLICATED content removes lines and almost no seconds.
A restated definition is cheap to CHECK; what costs is the USE of it at a
concrete carrier. So a deduplication that looks like a big win on the line
meter can be worth almost nothing at the wall gate, and the two thresholds
must be priced separately. Never convert a measured line saving into a seconds
saving with a rate.

**The measurement, 2026-08-09, `[L3.32-T237]` and `[L3.32-T240]`, the same
miniature before and after.** `[T239]` made the limit clause carrier-generic,
which deleted a 315-line restatement from the consumer.

| | lines | cold seconds | rate |
|---|---:|---:|---:|
| `[T237]`, restated port | 904 | 186.43 | 0.206 |
| `[T240]`, generic clause | 589 | 174.62 | 0.297 |
| delta | **-315** | **-11.80** | |

The 315 removed lines were worth **0.037 s per line**, cheaper than the
parameterized class's own 0.010-0.013 floor would predict for their size, and
far below the 26.8 s that `[T222]`'s bound-variable rate would have given. The
589 lines that STAYED carry 174.62 s between them. They state formulas at the
concrete carrier and prove decodes and placements there, which is P-n's
signature exactly.

**Note the trap in the rate.** The measured rate ROSE, from 0.206 to 0.297,
because the same cost now divides by fewer lines. A rate that rises after a
successful refactor is not a regression: it is the certificate becoming
honest, since the cheap lines are gone and what remains is the real content.
Do not read a rising rate as damage.

**What it means for a campaign.** If the wall is the binding threshold,
deduplication is not the lever, however good it looks on the meter. P-n's only
admissible move stands: need LESS instantiation, which is a change of
mathematical shape and not a change of where the code lives.

### P-p. A stale interface masquerades as a heap wall; move the `.agdai` before you believe a price

**The law.** Agda's incremental reuse can produce a STALE `.agdai` whose
re-elaboration costs orders of magnitude more than checking the module from
cold. The failure presents as the module's own content being ruinously
expensive: a long run, then `Heap exhausted` under the C-12 cap. It is not the
content. Move the interface aside and re-check before you record any price, and
ALWAYS before you report a heap wall.

**The measurement, 2026-08-09, `[L3.32-T225]`.** A stale `LevelKit.agdai` made
that module's own check take 191 s and exhaust the 8 g heap, measured twice,
and made `L.Rud.HF` exhaust 8 g as well. With the stale interface moved aside,
LevelKit checked in 2.4 s and HF in 2.7 to 13.9 s at the same cap. The
orchestrator confirmed it independently after the lanes exited: 583 in-fence
lines, about 2 s, exit 0.

**Why it is worth a law.** AGENTS.md tells every dispatched agent to report a
heap exhaustion as a wall and never to raise the cap, which is correct and must
stay. This law says what to do BEFORE that report. A wall attributed to content
that belongs to a cache gets paid for twice: once when a build is re-planned
around a cost that does not exist, and once when the real cause resurfaces. The
orchestrator made exactly that error on the day this was measured, and wrote it
into a law before `[T225]`'s return corrected it.

### C-24. A shape certificate is not a meaning certificate

**The law.** A proof obligation that certifies a formula's SHAPE (`Δ₀`, `Σ₁`,
`Π₁`) says nothing about what the formula MEANS. A wrong de Bruijn index changes
the meaning and leaves the shape untouched, so it passes every linter, every
gate and every typecheck. **An object-language atom is not usable until it
carries a two-way decode against a delivered meta-level reading**, and no
consumer may be built on an atom that lacks one.

**The measurement.** In `L.Condensation`'s structural story, three defects of
this kind were found in one day by three different agents:

- `sndIn` read a FIRST component while its name, its comment and all three of
  its use sites said second, so the range clause `Rg` read a **domain**;
- the corrected `snd∈Snd` asserts **equality** of second components where the
  limit clause needs **membership**;
- `limIn`'s second binder ranges over the singleton member rather than the pair
  member, making the value inclusion **vacuous**, machine-checked unsatisfiable
  at a concrete pair.

All three typechecked. Two chapters were built on top of them (`σᴹ` transported
to the set carrier, `σL` mirrored at the class), plus both story transfers and
the Levy certificates, and every one of those stayed green. The wrong content
passed several full-tree gates. It was found only when an agent read the atom
against its own documentation, by hand.

**Why the discipline is cheap.** The rest of this campaign already pays it: the
face's `read-off`, `L.Rud.LevelSigma`'s clause decodes and `L.Rud.OpGraph`'s
two-way graphs all pin meaning as well as shape, and none of them has produced a
defect of this class. The structural story is the one place it was skipped, and
it is the one place this happened.

**Provenance.** `[L3.32-T70]` found the first defect while mirroring the story;
`[L3.32-T75]` settled that the code rather than the comment was wrong;
`[L3.32-T76]` fixed it and found the other two; the owner ruled the story a
rewrite rather than a patch on 2026-08-05, executing as `[L3.32-T77]`.

### C-26. Signature-identical is not type-identical; verify the CONSUMERS, not the exports

**The law.** When a generalization replaces hand-written content, checking that
the exported SIGNATURES are byte-identical does not show the exports are
unchanged. A signature names a type; it does not show that type's internal
SHAPE, and a consumer that destructures positionally reads the shape. The only
sufficient check is to typecheck the consumers.

**The measurement, 2026-08-09, `[L3.32-T226]` and `[L3.32-T234]`.** C4 replaced
five hand-written story assemblies with a fold over a clause list. Its report
verified, correctly, that "all 20 signature lines are present verbatim,
diffed against the recorded pre-edit text; the bodies alone changed", and
concluded the exports were byte-identical. They were not. The fold's base case
is `Conj [] f = Unit*`, so a five-clause story acquired the type
`c₁ × (c₂ × (c₃ × (c₄ × (c₅ × Unit*))))` where the hand form was
`c₁ × (c₂ × (c₃ × (c₄ × c₅)))`. Nothing in any signature mentions that
difference.

`src/L/Rud/HF.lagda.md` destructures the story positionally at `:502`, so
`st .snd .snd .snd .snd` changed from the clause FUNCTION to a PAIR. Agda
reported `[CannotApply]`, exit 42. A delivered master was red, and the lane
that verified its own exports did not check it. `[T233]`'s A/B, run for an
unrelated reason, is what surfaced it.

**The cure is at the fold, not the consumer.** Give the fold a one-element
case, so a non-empty list ends bare. Repairing the consumer treats the symptom,
leaves every other positional consumer exposed, and keeps the generalization's
types different from the form it replaced, which is the opposite of what a
generalization is for.

**The check that would have caught it**, and it is cheap: typecheck the
consumers. C-23 already says a consumer scan must count same-file
instantiation bodies. This law says the scan must END in a typecheck, because
the defect is invisible to reading.

### C-27. An alarm for "never announced" is blind to "announced and dropped"

**The law.** A return can be lost in two different ways, and a check for one
cannot see the other. A waiter that never announced a return leaves a record
that says so, and an alarm can read it. A return that WAS announced and then
dropped at audit leaves a record that says everything went fine. The second
failure needs its own check, and the check is a cross-reference: **announced,
but the task index still says DISPATCHED.**

**The measurement, 2026-08-08 to 2026-08-09, `[L3.32-T208]`.** T208 and T209
returned in the SAME announcement, at the same second
(`returns.log` lines 124 and 125). T209 was audited and its verdict
registered. T208 was dropped. Its row read `DISPATCHED` for a day with a
finished 16 KB report on disk, and it was the OWNER who noticed, not the
tooling. The registry said `reported = True` throughout, so the existing
"RETURNS NEVER REPORTED" alarm was blind to it by construction.

**Why it took this long to happen, which is the useful part.** Of 145
announcements in the log, **140 carried exactly one return.** An audit loop
keyed on the ANNOUNCEMENT is indistinguishable from one keyed on each TASK
while that holds. The defect was latent from the first dispatch and only
became visible the day an announcement carried two. A process that is correct
on the common case and silently wrong on the rare one will pass every informal
review it ever gets.

**The enforcement point** is `dispatch.py status`, which now cross-references
the registry against `dev/PLAN.md` and prints every announced return whose row
still reads `DISPATCHED`.

### C-28. A threshold set from your own projection carries that projection's error inside it

**The law.** When the number a gate compares against is produced by the same
work the gate judges, the gate cannot fail in the direction that matters.
Padding the input raises the bar; the bar is then cleared; every checker
reports green. **Nobody has to cheat for this to happen**, which is why review
does not catch it: each step is defensible on its own. The cure is not a
tighter threshold. It is an INDEPENDENT figure, recorded before the work
starts, and a rule that the binding number is the SMALLER of the two.

**The measurement, 2026-08-06 to 2026-08-07, D30's wall gate.** The exit
condition's first version set a projected total of 1,100 s. The projection's
own error band was 1,088 to 1,121, **bracketing the very threshold it was
meant to clear**, so the gate's verdict flipped with which of two measurements
you used. `[L3.32-T93]` found the figure unreproducible from the ledger,
independently and from the other direction. The condition was withdrawn and
re-ruled to carry **no projected number at all**, and the owner recorded that
this was stricter rather than looser, because nothing now earned a pass by
sitting under a line. The replacement gate, 498 s, was still the campaign's
own figure and was met at 487.9 s with a margin of +10.1: meeting it proved
the campaign's arithmetic, not the tree's health.

**Where it binds now, and this is why the law is written and not just the
history.** DD5's line benchmark is measured from a GCH wing this project
builds itself (`dev/PLAN.md` DD5). `[LJ-0.3]` found the same shape and the
same blindness: a wing larger than it needed to be raises the bar by exactly
that much. **DD24 does not help**, and a first reading of it was backwards:
`scripts/check-ratio.py` fails only ABOVE the bar, and padding with cheap
lines LOWERS seconds per line, so a padded wing passes it more easily.

**The enforcement point** is `validate_benchmark()` in `scripts/ledger.py`,
which refuses a binding line benchmark that has no a-priori projection or one
larger than it. It is silent while the benchmark reads unbound, so it costs
nothing until the day the number matters.

### C-29. When the subject matter has not changed, amend; do not rebuild

**The law.** A rulebook rewrite is priced as editing, and it is not: it is a
migration, and every citation, checker, flag and cross-reference is a call
site. **Amendment keeps every old reference true by construction.** A rebuild
makes each one a thing that must be re-derived, and the ones that are missed
do not announce themselves, because a document that reads well is assumed to
be right. Ask what actually changed. If the SUBJECT did not, amend.

**The measurement, 2026-08-09.** A route change rebuilt `dev/PLAN.md`,
`dev/ORCHESTRATION.md`, `AGENTS.md`, the ledger, three archives and the whole
task-code series in thirteen commits. It consolidated 25 decision rows into
15. An audit then found **30 defects, six of them load-bearing**
(`agents/tasks/archive/LJ-0-1-CONSISTENCY/lj-0.1-consistency.md`), and eleven further commits were spent
repairing them. The defects were of exactly the migration class: dangling
citations, a dropped rule with a live pointer at it, three suspension flags
with half-written readers, a commit gate left RED by the rebuild itself, and
a brief clause still naming the RETIRED route.

**The control is in the same corpus.** D30, over the same documents in the
same week, was amended seven times, A through G, each recorded and dated and
none rewriting what came before
(`archive/dev/DECISIONS-archived.md:50`). It produced no defect of this class.

**What actually changed on 2026-08-09 was the architecture, not the
rulebook's subject matter.** The rules about gating, pricing, retirement,
dispatch and prose were the same rules the day after. `[LJ-0.3]` judged the
full rebuild a choice rather than a necessity, and the defect count is the
price of that choice.

**The enforcement point** is review: `dev/ORCHESTRATION.md` section 6, which
since 2026-08-09 puts the orchestrator's own diffs through the return audit
and sends a change to the rules themselves OUT for audit rather than
self-reviewing it.

### C-25. Two parallel writers may not share a file, and "the home you propose" IS a shared file

**The law.** A brief that grants an agent a file it does not NAME, such as "the
shared home you propose", grants an unbounded write. Two such briefs live at
once will collide, because agents reading the same tree propose the same home:
it is the correct home, which is exactly why both find it. The collision is
invisible to a checker that keys on the brief path, and invisible to each
agent, which sees a file that grew and assumes it wrote it.

**The measurement, 2026-08-09.** `[L3.32-T225]` (dedup) and `[L3.32-T226]`
(story assembly) were dispatched in parallel. Both scopes said "the shared home
you propose". Both proposed `src/L/LevelKit.lagda.md`, which was the right
answer for both. Nothing was overwritten, because they appended to different
regions, and that is luck rather than a mechanism.

What it actually cost, all of it recorded by the lanes themselves. `[T226]` saw
a `_⊆_` clash appear in LevelSigma while `[T225]` was mid-edit and vanish on
`[T225]`'s next write, and recorded it so the orchestrator would not chase a
ghost. `[T225]` had to EXCLUDE the sibling's 66 kit lines and its LevelSigma
rewrite from its own line counts, and stated that all its checks ran on shared
state it did not control. Both lanes debugged a file whose other half neither
had written. One created a probe named `ProbeT226Clash.agda`, which is how the
orchestrator learned an agent had worked the collision out by itself.

**The auditability is the cost, and it is enough.** Neither lane could report
its own delta without subtracting work it did not do, and a return whose
numbers depend on a sibling's timing cannot be audited against its brief. That
alone justifies the refusal; no dramatic failure is needed.

**A CORRECTION, because the first draft of this law claimed one.** The
orchestrator originally cited a `Heap exhausted` death at 195 s as this law's
evidence. That was a misattribution. `[T225]` measured the true cause: a stale
`LevelKit.agdai`, which is P-p, and it reproduced the cure. LevelKit at 583
in-fence lines checks in about 2 s, verified independently by the orchestrator
after both lanes exited. The collision is real; the heap wall was not its
doing.

**What to do.** Give each parallel writer a file it does not share, and when a
shared home is genuinely right, SERIALIZE: one lane lands it, the next is
briefed against the landed tree. The mechanical form is a write-territory
refusal at dispatch, comparing named paths across live lanes AND refusing two
unnamed grants at once, since two unbounded grants always intersect.

### P-u. A Levy witness travels along a relabelling for free and does not travel along a placement at all

**The law.** A `Δ₀` or `Σₙ` certificate transports along a constant
RELABELLING at zero cost, because the delivered `mapΔ₀` and `mapΣₙ` are
structural recursions on the certificate. It does NOT transport along a
parameter PLACEMENT. **So certify the formula BEFORE you place it, then compose
the absoluteness through the unplaced form.** A statement that asks for the
certificate of a PLACED formula is a different content class from the same
statement over the unplaced one.

**Why the asymmetry is structural, not a gap somebody can fill.** Relabelling
changes the constant type and leaves the formula's shape alone, so the
certificate maps constructor by constructor. Placement moves constants into
environment slots, which changes the shape, so no structural map exists.
`src/FOL/Manipulation/Parameters.lagda.md` never imports `FOL.LevyHierarchy`,
so no placement analogue can be stated there at all.

**Measured (`[LJ-1.27-R]`, 2026-08-10).** At `[LJ-1.27]`'s hardest condensation
clause, the placed witness `Δ₀ (embed (absFo φ))` EXHAUSTS 8 GB in 55 s. The
wall reproduced in two formulations, including one with every placement written
out by hand so that no meta-solving is involved, and in a probe that never
mentions `abs₀`. The composed route through the unplaced form checks in 25.6 s
in the same isolation. The delivered relabelling transport is
`src/FOL/Manipulation/Relabelling.lagda.md:209-242`.

**It confirms P-t from a new direction.** The class follows the FORMULA, and
PLACING the formula changes the class.

**The consequence that costs money.** `[LJ-1.27]`'s block is 0.110 to 0.113 s
per line against a 0.10 gate, and 31.0 s of its 33.3 s sits in the two placed
obligations. The same content stated directly runs at 0.0053 to 0.0114. **The
route out is upstream: a formula with NO constants reaches the parameter-free
axis through the delivered `erase` with no placement anywhere**
(`src/FOL/Count.lagda.md:598-611`, `:617-637`).

**Provenance:** `agents/tasks/archive/LJ-1-27/lj-1.27-review.md` sections 4 and 5. Probes
`agents/tasks/archive/LJ-1-27/ProbeDD25C.agda`, `agents/tasks/archive/LJ-1-27/ProbeDD25D.agda` and `agents/tasks/archive/LJ-1-27/ProbeDD25E.agda`, the
last red by design with its error message as its measurement.

### C-32. A cure invalidates every downstream measurement; RE-RUN THE GATE before you act on the old number

**The law.** When a cure lands anywhere in the import cone, every figure
measured before it is stale, **including figures in files the cure did not
touch**. A gate verdict is the first thing to re-run and the last thing anybody
remembers to re-run, because the gate lives in a different file from the cure
and nothing links them. **Re-measure the gate on the cured tree BEFORE you
route around a red gate.**

**Measured (`[LJ-1.32-R]`, 2026-08-11).** `[LJ-1.27]`'s gate probe measured
0.1135 s per line against a 0.100 NO-GO line, and the phase stopped for a
re-route. `[LJ-1.31]` then landed a cure in `L.Coding.Environment` and
`L.Coding.Model`, two files the gate probe does not name. **The unchanged gate
probe fell from 32.07 to 18.95 s, a 41 percent cut, which is 0.067 s per line
and a GO.** Nobody re-ran it: not `[LJ-1.32]`, which spent a whole dispatch
measuring walls to route around a gate that had already opened, and not the
orchestrator, who held the pre-cure figure and quoted it three times.

**The second half, and it cost the same dispatch.** `[LJ-1.27-R]` had already
WRITTEN the cured block as `agents/tasks/archive/LJ-1-27/ProbeDD25E.agda`, and it failed at exactly one
line, the `refl` asserting count 0, which is what `[LJ-1.31]` fixed. On the
cured tree it is green in 2.87 s at 0.0114 s per line. **A finished probe sat
one command away for a whole dispatch.**

**Why it was missed, stated so the cure is mechanical.** The orchestrator's
brief scoped the archive read to `agents/tasks/archive/LJ-1-27/lj-1.27-review.md` **section 4**. The
erase route and the probe's name are in **section 6**. A brief that names a
SECTION rather than a document hides everything the orchestrator did not
already know, and that is exactly what an archive survey exists to prevent
(DD18).

**What to do.** After any cure lands, re-run the gate probe and every measured
comparable in its cone before dispatching work that depends on them. **Cite
whole documents in an ARCHIVE section, never a section number**, unless the
document is large and the section is an ADDITION to it rather than a
restriction.

**Provenance:** `agents/tasks/archive/LJ-1-32/lj-1.32-review.md` sections 1 and 5;
`agents/tasks/archive/LJ-1-32/lj-1.32-report.md`; `agents/tasks/archive/LJ-1-32/LJ-1.32.md:101,131-133`.

### C-33. Name the OBLIGATION in a brief, never one delivered entry point: the agent will use the one you named

**The law.** When a brief names a specific delivered API for a job, the agent
uses THAT one, even when a cheaper delivered entry point exists beside it and
would prove the same theorem. **A brief that names an entry point has made a
design decision without measuring it.** State the obligation and let the agent
survey the delivered surface; name an API only to FORBID one, or when the
choice has been measured.

**The same failure has a twin: naming a STYLE.** Telling an agent to follow a
delivered chapter's shape copies that chapter's decisions, including ones that
were right there and wrong here.

**Measured (`[LJ-1.33-R]`, 2026-08-11), and the two causes separate cleanly.**
The task was condensation's leg D, the story-to-machine agreement. A 2x2, each
cell a cold pair at one process, on ONE theorem with ONE set of hypotheses:

| route \ body | hand-written body | delivered body reused |
|---|---:|---:|
| machine CONTENT projections (`StepAt-out`/`-in`) | **50.13 s, 0.334** | 13.34 s, 0.092 |
| machine FORMULA readings (`extAt-out`/`-in`/`-in-both`) | 30.00 s, 0.297 | **1.32 s, 0.0108** |

**Neither cure alone passes DD24's 0.013193 bar. Together they pass with
room: 38x in seconds, 31x in rate.** The orchestrator reproduced the endpoints
independently at 49.79 s and 1.41 s.

**Both cells on the expensive diagonal were the brief's doing.** It named
`src/L/Coding/Sequence.lagda.md:217-229` for the machine side, which are the
CONTENT projections; the FORMULA readings at
`src/L/Coding/Model.lagda.md:667-678` are equally delivered and the brief never
named them. It then told the agent to take block 1's `Clause` shapes as its
source; block 1 hand-writes every formula, correctly, because those are new
bounded content, but the step body is DELIVERED and copying the style copied
the re-typing.

**The finding underneath, which is why the cheap cell exists.** The story
clause and the delivered machine clause carry the SAME body and differ only by
three bounds, proved by `refl`. So the row is a bound-drop over an abstract
body, and the layer that does it is 37 lines, generic in the body, costing
34 ms. Six instantiations cost 1.72 s, so each extra clause is 0.08 s and the
rate FALLS to 0.0054. **The expensive-looking half is template and the J tower
gets it free** (DD4).

**One correction it also forced.** The return placed 0.334 in P-n's
concrete-carrier floor band. It is not there: a control at 0.297 sits inside
that band with no carrier at all, so the band does not diagnose this cost.

**Provenance:** `agents/tasks/archive/LJ-1-33/lj-1.33-review.md`; `agents/tasks/archive/LJ-1-33/lj-1.33-report.md`;
`agents/tasks/archive/LJ-1-33/LJ-1.33.md:42-43,55-60`.

### P-v. Never force a satisfaction-level conversion between two spellings of one formula

**The law.** A formula-level identity is free: two spellings of one formula are
equal by `refl` or by a one-line `cong`. **The SAME identity under
`⟨ γ ⊨ - ⟩` costs seconds, and it costs them inside the type of every lemma
that carries it.** So prove the spelling identity ONCE at the formula level,
then state everything downstream in ONE spelling. **Where the story is yours to
write, write it in the machine's spelling from the start.**

**Measured (`[LJ-1.34-R]`, 2026-08-11): 59 ms against 29,415 ms for the
IDENTICAL theorem, a factor of 499.** The site was condensation's leg D. The
story spelled the definable-powerset leaf `DefAtB` and the delivered machine
spelled it `DefAt`. Every agreement lemma's type then carried a
satisfaction-level conversion between the two, and two endpoint conversions
alone held 29.4 s of a 73 s block.

**It is P-l's mechanism seen from a new side.** P-l says naming a transparent
or built construction in a statement's TYPE is what costs. Here the type names
the same built construction TWICE, in two spellings, and the elaborator pays to
reconcile them at every use.

**The whole-block effect at the same site**: 0.436 s per line against 0.0079,
a factor of 55, for the same theorem with the same hypotheses. The orchestrator
reproduced both endpoints at 72.21 s and 1.57 s.

**THE SECOND SPELLING ALSO HIDES IN A PROOF ARGUMENT, and there it is worth
681x.** The law above names two spellings of a FORMULA. The same mechanism runs
one level up: when a proof argument is written inline as `refl` in BOTH a type
and a body, the elaborator must decide a conversion between two elaborations of
one proof, and it unfolds the built tree to do it. **Give the proof a NAME and
pass the name.**

**Measured (`[LJ-1.50-R]`, 2026-08-11), and the isolation is exact.** The probe
is one file with ONE change: the count proof `countFo defb ≡ 0` gets a name
instead of being written `refl` inline in both positions. Agda's own attribution
for the identical `erase-Δ₀` call on the identical leaf:

| spelling | ms |
|---|---:|
| `refl` inline in the type AND the body | **150,133** |
| the proof NAMED and passed | **220** |
| named in the type, `refl` in the body | 151,402 |

**The third row isolates the mechanism**: one named side is not enough, because
the conversion is still between two elaborations. The orchestrator re-ran the
ends at 154.92 s against 2.20 s whole-file.

**What it cost before it was found.** `[LJ-1.49]` measured 150.13 s and called
it the instantiation-class cost. `[LJ-1.50]` then measured three spellings,
concluded the number stood, and reported that one step exceeded the GCH side's
WHOLE seconds budget of 99.6 to 147.7 s. **The route looked infeasible and the
150 s was a probe artefact.**


**Provenance:** `agents/tasks/archive/LJ-1-34/lj-1.34-review.md` sections 1 and 2;
`agents/tasks/archive/LJ-1-34/ProbeDD25D5.agda` against `agents/tasks/archive/LJ-1-34/ProbeLJ134.agda`.

### P-w. A module application COPIES; an interposed module cannot amortize one

**The law.** A module application copies its target's definitions; it never
references them. So interposing a module that RE-EXPORTS its target strictly
ADDS one set of copies, and it cannot amortize anything, however the
parameters are spelled. **Only three moves reduce instantiation cost: (a)
fewer applications, (b) fewer definitions copied per application, (c) cheaper
types on the definitions that are copied.** Interposition is none of them.

**The action.** Before funding a move against an instantiation wall, classify
it. If it interposes a module that re-exports its target, refuse it without
measuring. If it narrows, count what the target exports against what its
consumers reach, and price the difference.

**The measurement, 2026-08-12, four regressions and no success in class.**

| move | interposes | measured |
|---|---|---:|
| shared frames in the chain wrappers, abstract arguments | yes | **+17.23 s** |
| three depth frames over `EnvSet`, concrete slots | yes | **+10.88 s** |
| `TwelveAgree.twelveB` aliased to `SatGraphB.twelveB` | yes | **+3.29 s** |
| abstract-stack module inside `NegAgree` | yes | **+2.82 s** |
| `KFacts` record bundle, fewer parameters per application | no, (c) | **-30 s** |
| `Lift12Back` telescope kit, fewer statements | no, (a) | **4.28x** |
| `StageCardinal`'s un-consumed `Successor` cluster removed | no, (a) | **-9.85 s** |

Four interpositions, four regressions. Three moves in classes (a) and (c),
three wins. **The law would have refused four dispatches before they were
funded, and checking it costs one count of the interposed module's exports.**

**The exception it names, and the exception is the useful half.**
Interposition WINS when the interposed module narrows: when it exports fewer
definitions than its target, it is class (b) wearing an interposition's shape.
`EnvSet` exports fifteen definitions and its eighteen application sites reach
exactly three, `out`, `back` and `memE-bnd`.

**How the orchestrator broke it.** `[LJ-1.67]`'s brief argued that abstracting
the stack removes the concrete argument, then prescribed "the row's `out` and
`back` instantiate it at their own stacks", which puts the concrete argument
back at every site. **The mechanism claim and the prescribed shape contradicted
each other on the page**, and the agent built what it was told. The `[LJ-1.25]`
analogy the brief leaned on fails at the one joint that made the original
work: there the transparent index never appeared again, and here the concrete
stack still appears at every site (P-l).

**AMENDED THE SAME DAY, and the amendment is the useful half. THE COPY IS
PAID AT USE, NOT AT WRITING.** `[LJ-1.69]` measured that a module-level
`module X = M ...` binding that nothing uses costs **0.089 s**, inside the
noise, and `agda --profile=definitions` shows **no elaborated copy at all**.
A let-bound application inside a proof body is the eager shape: `[LJ-1.66]`
measured that one at **1.016 s**. So "an application copies" is right about
WHAT is paid and wrong about WHEN, and an instrument that counts unused
module-level applications measures nothing. **Price an application by what
USES it.** That the difference is the binding site rather than the two
different modules is INFERRED; only one shape was measured at each site.

**AND THE COST IS USUALLY NOT THE COPY.** At the discharge frame `[LJ-1.69]`
measured one row module at **3.6 s**, of which the used surface is about
**0.12 s**: the `row` formula and the `out`/`back` aliases. The other 3.5 s
is the FRAME TELESCOPE, seventeen site facts of which four state satisfaction
over the built trees `envSetAt`, `envOverAt` and `tmValAt`. That is P-t
content. **So class (c), cheaper types on what is copied, is where the money
is, and classes (a) and (b) were always going to return little.**

**THE SWING THIS OPENS, measured in parts and composed:** writing one frame
per row pays the 3.6 s telescope thirteen times, about **47 s**. Writing ONE
generic frame whose seventeen facts are parameterized by the row tag pays it
once plus thirteen used surfaces, about **5 s**. **Nine to one, and it is the
same shape `KFacts` took for the other fact family at `-30 s`.** The generic
frame is the DD4 move and the cheap one at the same time.

**Provenance:** `agents/tasks/archive/LJ-1-66/lj-1.66-review.md` section E.1, a DD25 review that
read the four regressions as one mechanism rather than four failures;
`agents/tasks/archive/LJ-1-63/lj-1.63-report.md` section 5, `agents/tasks/archive/LJ-1-66/lj-1.66-report.md:94`,
`agents/tasks/archive/LJ-1-67/lj-1.67-report.md:32`, `agents/tasks/archive/LJ-1-62/lj-1.62-report.md:85-112`. The
amendment is `agents/tasks/archive/LJ-1-69/lj-1.69-report.md` sections 2 to 4.

### C-34. A return that names a cure PRICES it, or reports the wall that stops it

**The law.** A cure named in a return and left unpriced is not a caveat. **It
is an unmeasured term inside the verdict, and it decides the verdict.** A
return that names one either builds it and measures it, or reports the wall
that stopped it. **P-l forbids pricing a cure by ANALOGY; it never forbids
building the cure and MEASURING it.** A brief that says "measure it, do not
argue it" is asking for exactly this and must be obeyed.

**Measured twice in one lineage, on consecutive dispatches, both overturned by
`[DD25]` reviews that built the named cure:**

| return | the cure it named and did not price | verdict | after the review built it |
|---|---|---:|---:|
| `[LJ-1.33]` | a shared machine-reading layer | NO-GO at 0.334 | **0.0108, a factor of 38** |
| `[LJ-1.34]` | a generic leaf layer with the body abstract | NO-GO at 0.436 | **0.0072, a factor of 61** |

**Both returns cited P-l as their reason not to measure.** That is a misreading
of P-l, and it cost two dispatches and two adversarial reviews. Each NO-GO
would have stopped the phase.

**The orchestrator's half of the fix.** Say in the brief that a named cure must
be built or walled, not deferred. **Both of these briefs did say "measure it,
do not argue it" and were still read as permission to defer**, so the sentence
must name P-l explicitly and say what it does not forbid.

**Provenance:** `agents/tasks/archive/LJ-1-33/lj-1.33-review.md`, `agents/tasks/archive/LJ-1-34/lj-1.34-review.md`,
`agents/tasks/archive/LJ-1-33/lj-1.33-report.md` section 6, `agents/tasks/archive/LJ-1-34/lj-1.34-report.md` section 6.

### C-35. A delivered block with no consumer is UNTESTED: its first consumer is its first real audit

**The law.** A green typecheck, a `--safe` header, a clean rate and a verified
line count say the code COMPILES and is CHEAP. **They say nothing about whether
the statements are the right statements.** A block that nothing imports has
never been asked to mean anything. **So a block delivered without a consumer is
not delivered; it is staged.** Do not record it as complete, and do not build a
size or ratio figure on it, until something consumes it.

**The orchestrator's audit must include one mathematical question**, not only
the mechanical ones: **pick the block's least obvious statement and ask what
would be false if it were wrong.** If the answer is "nothing yet", the block is
untested and the report must say so.

**Measured (`[LJ-1.37]` and `[LJ-1.38-R]`, 2026-08-11).** `[LJ-1.37]` delivered
1,723 in-fence lines, the twelve-clause condensation table. The orchestrator
verified 2,031 in-fence lines, ZERO placement constructs, `--safe`, no
`postulate`, no hole, and 9.00 s cold at 0.0046 s per line, then committed it as
DELIVERED and quoted its ratio to the owner. **Every one of those checks was
mechanical and every one passed.**

**The next block's first attempt to CONSUME it found the rows defective.** Each
story frame ended in `∀̇∈ (var yc) body`, which is vacuous at an empty value,
where the machine's `extAt yc body` constrains it. Worse, at a NONEMPTY value
one index made the defining condition never mention the element it defines, so
the row is FALSE of the true satisfaction table, not merely weak.
`agents/tasks/archive/LJ-1-38/ProbeDD25E1.agda` proves the countermodel, `agents/tasks/archive/LJ-1-38/ProbeDD25E3.agda` is the
control that fails with `fst e != fst z` when the index is corrected, and both
were re-run by the orchestrator.

**968 of 2,141 in-fence lines re-open.** The defect survived one delivery, one
orchestrator audit and one commit, and it cost a build dispatch and a
maximum-effort review to surface.

**The tell was on the record and unheeded.** The orchestrator wrote to the
owner, before the defect was known, that the block had "zero consumers" and
that its delivered-and-unconsumed state "should not be treated as redeemed".
**Naming a risk is not acting on it.** The gate is: no consumer, no DELIVERED.

**Provenance:** `agents/tasks/archive/LJ-1-38/lj-1.38-review.md`; `agents/tasks/archive/LJ-1-38/lj-1.38-report.md`;
`agents/tasks/archive/LJ-1-37/lj-1.37-report.md`; commit `92e8b8b`.

### D-29. A shared layer propagates a FIX and a DEFECT at the same rate; sharing concentrates risk as well as saving lines

**The law.** DD4 says maximize what the two proofs share. **This is DD4's other
face, and it is not an argument against DD4.** A shared definition that is
WRONG is wrong at every site at once, and no site's own test catches it,
because every site inherits the same mistake. **So the audit that a shared
layer needs is not proportional to its size; it is proportional to the number
of sites that depend on it.**

**The operational consequence, which is cheap.** When a block's design is
"one frame, N instantiations", **audit the FRAME against an external
reference before instantiating it N times.** Instantiating first and auditing
after buys N copies of any frame defect at the price of one.

**Measured (`[LJ-1.37]`, `[LJ-1.38-R]` and `[LJ-1.40]`, 2026-08-11).** The
condensation table is one frame family instantiated twelve times, one row per
`Formula` constructor.

**The saving side is real.** After the frame repair, **nine of eleven rows were
pure mechanical re-indexing**. Only `Forall` needed an individual slot fix, and
`Exist` and block 1's `Clause` needed an `extAtB` wrap. **So one frame change
repaired nine rows.**

**The risk side is the same mechanism.** The defect was IN the shared layer:
the two shapes and their numeral twins, the term value and the environment
condition were shared and defective, so **all twelve rows were false of the
satisfaction table at once**. 968 of 2,141 in-fence lines re-opened.

**And the scope estimate was optimistic in the same way.** A maximum-effort
adversarial review computed which regions survived, by index arithmetic. **The
first consumer audit found six more definitions that had to be re-laid or
corrected**, including `arTagB`, `arTagPairB`, `arTagBnum`, `arTagPairBnum`,
`tmValB` and `envBndGen`. **Index arithmetic that is not machine-checked is a
residue** (D-10), even when a careful reviewer produces it.

**Read this beside C-35.** C-35 says a block with no consumer is untested. This
says a shared layer is untested at N sites simultaneously, so the first
consumer's audit is worth N times what a single site's audit is worth.

**Provenance:** `agents/tasks/archive/LJ-1-40/lj-1.40-report.md` sections 4 and 5;
`agents/tasks/archive/LJ-1-38/lj-1.38-review.md` section 6; `agents/tasks/archive/LJ-1-37/lj-1.37-report.md`.

### C-36. A failed substitution is not a proof of impossibility: a type error says the types differ, never that no term connects them

**The law.** When a probe writes the identity coercion between two statements
and Agda rejects it, the message is **"these two types are not the same"**. It
is NOT "no term inhabits the implication". **A refusal built on a bare coercion
failure has measured a spelling, not a mathematics.** Before reporting an
impossibility, write the term you think cannot exist, or state which
constructor is missing and show that nothing supplies it.

**The brief-craft half, and the orchestrator owes it.** A brief that says
**"do not WEAKEN a statement to make it close"** and says nothing about
strengthening is one-sided. **A cure is often a STRENGTHENING**, and an agent
holding only the first half can read the whole direction as closed. Write both
halves: **do not weaken, and you MAY strengthen, provided the stronger form is
still true and still Δ₀-compatible.**

**Measured (`[LJ-1.41]` and `[LJ-1.41-R]`, 2026-08-11).** `[LJ-1.41]` closed two
of eleven row agreements and declared the other nine unclosable, on a stated
Δ₀ IMPOSSIBILITY: the machine's `envSetAt` is unbounded, the story's condition
is K-bounded, `Δ₀` has no `δ-∀` and no `δ-∃`, so no witness exists.

**Every part of that reasoning was refuted by four probes.** The unbounded
witness is never needed, because every leaf is a K-bounded Δ₀ restatement
transferred under site facts; `agents/tasks/archive/LJ-1-41/ProbeDD25F41A.agda` builds the supposedly
missing witness in ONE line from the delivered `Δ₀-extAtB` and `Δ₀-envBndGen`,
GREEN in 1.45 s. `agents/tasks/archive/LJ-1-41/ProbeDD25F41B.agda` then builds BOTH directions between
the bounded condition and `envSetAt` in 98 lines, GREEN, marginal cost 0.22 s.

**The real defect was ONE MISSING CONJUNCT.** The machine's `extAt` is a pair
of implications and the story wrote the first and stopped.
`agents/tasks/archive/LJ-1-41/ProbeDD25F41D.agda` is the control: it supplies the delivered condition
PLUS all three site facts and Agda still refuses, so the conjunct is what is
missing and not the facts.

**The tell was in the failing probe itself.** `agents/tasks/archive/LJ-1-41/ProbeLJ141C.agda`'s body is a
bare `henv`, an identity coercion, and its error shows a Π on one side against
a Σ of two Π on the other. **The shape of the error named the missing conjunct
and the return read it as impossibility.**

**And the same defect had been in block 1 since `[LJ-1.5]`.** That report
recorded the symptom in its own words, "the matrix-to-clause link is unproven",
and nobody read it as this. **Read beside C-35**: a block with no consumer is
untested, and its own report may already contain the finding nobody has
consumed.

**Provenance:** `agents/tasks/archive/LJ-1-41/lj-1.41-review.md`; `agents/tasks/archive/LJ-1-41/lj-1.41-report.md`;
probes `agents/tasks/archive/LJ-1-41/ProbeDD25F41{A,B,C,D}.agda`, re-run by the orchestrator.

### D-30. Price what the CONSUMER needs, never the general law: generality nobody asked for is the cheapest thing to delete and the most expensive thing to keep

**The law.** When a block takes a lemma at its most general form because that
was convenient to state, the generality is not free: it is paid in every second
the elaborator spends on the parts no consumer reaches. **Before pricing a
construction, read its consumers and write down what they actually demand.**
Then price THAT. A general law is a decision, and a decision made for
convenience is one nobody measured.

**The corollary that finds the money: look for sections with NO consumer at
all.** They cost their full check time and return nothing, and they are the
cheapest possible cure because deleting them cannot break anything.

**Measured (`[LJ-1.47]`, 2026-08-11), 5.45x on seconds.** `src/L/StageCardinal`
takes the square law at EVERY infinite set as the module parameter `sq`, and
`[LJ-1.21]` chose that form because it was convenient. The GCH chain uses it at
two sites only, the initial ordinals κ and κ⁺ of Devlin 5.5 and 5.6.

| form | lines | cold s | rate |
|---|---:|---:|---:|
| the archived general law | 1,278 | 43.26 | 0.0338 |
| **what the consumer needs** | **744** | **7.94** | **0.0107** |

The rate falls from 2.7x DD24's bar into P-m's parameterized band, and the GCH
side flips from **1.25x OVER to 0.96x UNDER**. One module decided the wing.

**Both levers were DELETIONS, not rewrites, and that is the pattern to look
for.** Four of the five general-law sections had no consumer at all: the
archive's own deliverable never used them and nothing outside imported them.
And one definition, `col→τ-fiber`, held **18,363 ms of a 19,481 ms module
profile, 94.3 percent**, because it built an order type as a V-set when the
collapse already landed inside the target: the consumer wanted an injection,
not an order type. The orchestrator re-measured the two ends at 19.35 s against
1.32 s, a factor of 14.7.

**What it does NOT promise.** The residue after both deletions is
`comp₀-inj`'s exclusion chase at a variable carrier, 4,752 ms of 6,272 ms. That
is body-bound machinery paid once, and no consumer question reduces it. **A
consumer audit finds unreached generality; it does not make required content
cheaper.**

**Read beside D-29.** D-29 says a shared layer propagates a fix and a defect at
the same rate. This says the same layer propagates unreached GENERALITY at the
same rate, and that generality is invisible until somebody reads the consumers.

**Provenance:** `agents/tasks/archive/LJ-1-47/lj-1.47-report.md`; `agents/tasks/archive/LJ-1-46/lj-1.46-report.md`;
probes `agents/tasks/archive/LJ-1-47/ProbeLJ147PairingSealed.agda` against
`agents/tasks/archive/LJ-1-47/ProbeLJ147PairingGut.agda`, re-run by the orchestrator.

### C-37. State a law with the ACTION it prescribes, never only the prohibition: a law written as a wall hides its own cure

**The law.** Most laws in this book have two halves: a thing that costs, and the
move that avoids it. **A brief that transmits only the prohibition turns the
law into a dead end**, and the agent stops exactly where the law would have told
it what to do. **Write both halves, and put the action first.**

**The two shapes that keep failing.** A law quoted as "if you see X, STOP"
suppresses the cure X has. A law introduced as a COST law ("this shape is
expensive") reads as a diagnosis rather than an instruction, so nobody applies
it as a fix.

**Measured (`[LJ-1.7]` and `[LJ-1.7-R]`, 2026-08-11).** The brief stated P-u as
"if you need `absFo` or a placed `Δ₀`, STOP and report it: the wall is flat at
8 GB". P-u's actual content is **certify BEFORE you place**, and its cure is to
make the formula constant-free so that no placement is needed at all. Two lines
later the brief introduced P-v as a cost law, "this file paid 10 to 15x for the
two-spelling shape", rather than as the cure it is.

**The return then stopped on a constant count and called it a wall.** It
reported `countFo matrix = 328` and concluded the level-hood instantiation was
blocked. The count is TRUE and machine-checked; the conclusion is an inference
and it is wrong.

**The review built the cure the laws prescribe.** The 328 decomposes as eight
copies of one 41-constant leaf, and every constant is `con (numeralL k)`, an
arity tag. **The file already documents the cure as its own house style**
(`src/L/Condensation.lagda.md:1111-1114`, "the tag numerals are slots, so every
formula is constant-free") **and its twelve delivered rows already run it.** The
`*Bnum` family is simply a SECOND SPELLING, which is P-v's defect. The slot
spelling of the whole chain gives `countFo ≡ 0` by `refl`, `erase` then applies,
Δ₀ survives, and it costs 256 lines at 0.0113 s per line with **ZERO consumer
edits**, because the signature already carries the slots.

**So the cure was documented in the file the agent was editing, and the brief's
framing walked it past.**

**Read beside C-33 and C-36.** C-33 says name the obligation, not an entry
point. C-36 says a failed substitution is not a proof of impossibility, and you
may strengthen. This says the same failure enters one step earlier: **the brief
can remove the cure from the agent's reach before any substitution is tried.**

**Provenance:** `agents/tasks/archive/LJ-1-7/lj-1.7-review.md`; `agents/tasks/archive/LJ-1-7/lj-1.7-report.md`;
`agents/tasks/archive/LJ-1-7/LJ-1.7.md`; probe `agents/tasks/archive/LJ-1-7/ProbeDD25G1.agda`, re-run by the
orchestrator.

### C-38. A hypothesis is discharged when something SUPPLIES it, never when it is restated

**The law.** Counting a module's hypothesis parameters down to zero is not a
discharge. A telescope that replaces them must be SATISFIABLE, and the only
proof of that is an instantiation. **Until something instantiates the module,
"discharged" means "restated", and a restatement that nothing can satisfy
makes the module vacuously true: it typechecks, it is fast, and it proves
nothing.**

**The action.** When a return says hypotheses are discharged, do not audit the
parameter count. **Audit the instantiation.** If none exists, the correct word
is "restated", and the acceptance test is the next dispatch that consumes it.

**The measurement, 2026-08-12.** `[LJ-1.70]` replaced `TwelveAgree`'s
twenty-four hypotheses with a forty-seven fact telescope and reported them
discharged. The orchestrator verified three things, all true and all about
shape: the parameter count was zero where it had been twenty-four, the twelve
row modules were instantiated inside, and `out`/`back` still stated both
directions. He committed it as `c21b417` saying the debt was paid.

`[LJ-1.71]`, dispatched under C-35 precisely because the module had no
consumer, found the telescope's first fact:

```agda
(tagEq : (k : ℕ) (N : Fin (11 + n)) → fst (lookup N γ) ≡ fst (numeralL k))
```

**Every slot equals every numeral.** Taking `k = 0` and `k = 1` at one slot
gives `numeralL 0 ≡ numeralL 1`, refuted by the delivered `numeralL-inj`.
The type is uninhabited at every frame, not merely at the consumer's, so the
module could never be instantiated by anything. Machine-checked at
`agents/tasks/archive/LJ-1-71/ProbeLJ171A.agda:170-173` (`tagEq-refutes`), re-run by the orchestrator.

**The same audit found the slot fix of `[LJ-1.55]` HOLDS**: the frame's row
facts land at the telescope's slots definitionally. The defect is the
over-general statement, not the slot convention.

**This is the third time the shape has been paid for.** `[LJ-1.37]` shipped
1,723 lines whose rows were false of the satisfaction table, past an audit
that checked line counts, placement, safety flags and timing. `[LJ-1.64]`
passed the DD24 gate by deleting the band that discharges these same
hypotheses, and the orchestrator caught that one. `[LJ-1.70]` moved the
obligation into a hypothesis nothing can satisfy, and he did not.

**Read beside C-35.** C-35 says a block with no consumer is untested. This
says what the untested thing usually is: not the proofs, which typecheck, but
the assumption that the hypotheses mean anything.

**THE WIDEST INSTANCE, 2026-08-12, and it was not found by any audit of
mine.** The owner asked for an adversarial review of the mathematics rather
than the seconds. It found that `KFacts`, the record `[LJ-1.62]` measured as
a minus-thirty-second win and the orchestrator committed, has an
uninhabitable field:

```agda
arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩
```

**It reads as conditional and is not.** Every set belongs to its own
singleton, so it asserts that EVERY set belongs to `K`, including `K`.
`[LJ-1.77]` machine-checked the refutation in one step through the delivered
`∈-irrefl`: `arityK ⁅X⁆ X (X ∈ ⁅X⁆)` gives `X ∈ X`
(`agents/tasks/archive/LJ-1-77/ProbeLJ177A.agda:75-78`, green at 2.47 s). `innerK`, `innerPairK` and
`pairK` are the same shape without any premise at all, refuted by a
membership cycle rather than by irreflexivity, and they stay INFERRED
because the tree delivers no no-cycle lemma.

**The blast radius, MEASURED**: six masters take `KFacts` (`ShapesAgree`,
`ClosedAgree`, `ShapedAgree`, `WitnessAgree`, `SatGraphAgree`, `LeafAgree`)
and twenty more take a suspect field type directly, which is the whole
row-agreement band. **All of them are uninstantiable as stated, including
the leaf adequacy the orchestrator had reported as the phase's completed
mathematics.**

**THE CHECKER NOW EXISTS: `scripts/check-unbound-hyp.py`, written
2026-08-13.** On the unrepaired frame it flags **all eleven** hypotheses this
phase machine-refuted, plus the two of the same shape that resisted
refutation, and it does NOT flag `carrierK`, `arityK`, `pairK` or `innerK`.
It is ADVISORY and not in `make check`, because a flag is a question and the
cure is a refutation probe. **Run it on a frame before you fund a build
against it.**

**THE SHAPE IS MECHANIZABLE.** A closure hypothesis
about a bounding set `K` must be CONDITIONAL:
`(a : S) → a ∈ <bound> → a ∈ K`. One quantified over arbitrary sets with no
membership premise is refuted by regularity, always. **A grep is not enough
to find these**: the orchestrator's one-line regex over-matched and flagged
`carrierK`, which is sound. A real checker needs the parse, and it is worth
writing.

**Provenance:** `agents/tasks/archive/LJ-1-71/lj-1.71-report.md` sections 0 to 2;
`agents/tasks/archive/LJ-1-71/ProbeLJ171A.agda`, re-run by the orchestrator; commit `c21b417`, whose
claim that the twenty-four hypotheses were discharged is false.

### C-39. A brief's prohibition binds harder than its goal: an agent stops at the wall and never reports the door behind it

**The law.** A dispatched agent cannot contradict its brief. So a prohibition
written to prevent one known failure also forbids every legitimate move that
looks like it, and the return reads as a clean negative rather than as a
blocked search. **The orchestrator then believes a route is dead when only
the brief was.**

**The action.** Write a prohibition with its TEST, never with its shape.
"Do not add a hypothesis" is a shape. "Do not add a hypothesis the consumer
cannot supply, and name what supplies each one you add" is a test, and it
admits the delivered fact while still refusing the invented one. The same
for an abort criterion: "stop at the first negative" is right only when the
question has one candidate answer. **Count the candidates before you write
the stop.**

**The measurement, 2026-08-13, two dispatches in one session.**

`[LJ-1.98]` was told "STOP at that one" on the first tie measured not
supplied. It measured the T-slot tie for `entryK` absent at the site, which
was true, and stopped with ten facts unattempted. `[LJ-1.99]` then measured a
second tie GREEN: four applications of the delivered `KFacts.arityK`
(`src/L/Condensation.lagda.md:5769-5770`), `agents/tasks/LJ-1-99/ProbeLJ199A.agda:65-204`. The
question had at least two candidate ties and the criterion admitted one.

`[LJ-1.102]` was told "Do not add a hypothesis to the row to make the tie
available". It measured both tie forms failing, each on one component of the
same transfer, the two premises exactly one `arityK` step apart, and reported
that the row's telescope holds neither `arityK` nor `transK`
(`src/L/Condensation.lagda.md:4142-4185`). **`arityK` is a field of the
consumer's own `KFacts` and `transK` is already a fact of the composer's
frame** (`src/L/Condensation/TwelveAgree.lagda.md:167-169`). The prohibition
was written against invented facts and it blocked a held one.

**Both returns were correct measurements of what they were asked.** Neither
was wrong. The defect is upstream of them, in the brief, and it cost one
dispatch each time.

**Provenance:** `agents/tasks/LJ-1-98/lj-1.98-report.md` section 0; `agents/tasks/LJ-1-99/lj-1.99-report.md`
section 0, probe re-run by the orchestrator at 1.85 s;
`agents/tasks/LJ-1-102/lj-1.102-report.md` sections 0 and 2; briefs
`agents/tasks/LJ-1-98/LJ-1.98.md`, `LJ-1.102.md`, whose stop lines are quoted above.

### P-x. A transparent construction in a RECORD FIELD type is paid by every elaboration of the record: state it as a telescope fact instead

**The law.** P-l says a statement may be about a concrete position without
dragging that position's PRESENTATION into its type. **A record field is the
worst place to break that rule.** A telescope hypothesis is elaborated where
it is stated; a record field's type is forced into every elaboration of the
record, at every instantiation and every projection, whether or not anything
consumes the field. **So a transparent term in a field type is multiplied by
the record's whole use surface.**

**The action.** When a frame needs a closure fact whose statement names a
transparent construction, **state it as a telescope fact of the frame, the
shape the other closure facts already take. Do not add it to the record.**
The test is cheap and it is two lines: add the field, check, remove the
field, check.

**The measurement, 2026-08-13, a controlled pair in one master.** The tied
key-fact family needs a successor closure,
`sucK : (a : S) → a ∈ K → sucV a ∈ K`. Adding it as a field of the `KFacts`
record (`src/L/Condensation.lagda.md`) **exhausted the C-12 heap cap in every
configuration that carried it**: with the derivations inside the transfers,
walled at about 247 s; with them hoisted to module level, walled at about
247 s; with plain tied telescopes and no derivations at all, walled at about
256 s. **Removing exactly the two lines, the field and its `KFactsCons`
line, returns the master to GREEN at 154 to 155 s.** The rows never consume
the field. The transparent `sucV (fst a)` in the field TYPE is what the
record's elaborations carry.

**The supply is unaffected and was measured separately.** All three tied
shapes derive from `sucK` plus the existing `pairK` at the generic frame:
`agents/tasks/LJ-1-109/ProbeLJ1109A.agda`, module `TiesSupplied`, GREEN. **The wall is about
where the fact is STATED, never about whether it is true or useful.**

**Provenance:** `agents/tasks/LJ-1-109/lj-1.109-report.md` section 2; `agents/tasks/LJ-1-109/ProbeLJ1109A.agda`;
the green master at commit `c728e8b` plus the tie landing. Related: [[P-l]],
[[P-o]], [[P-i]] class 3, and [[P-w]], which measures the same multiplication
for module applications rather than record fields.

### C-40. Verify the CONSUMERS of a changed master, never the master alone: the gate exists because the author's own check is blind by construction

**The law.** A master's own check answers "does this file still elaborate",
never "does anything that uses it still elaborate". A change to a telescope
is invisible to the file that states it and fatal to the file that applies
it. **So an author who checks the file they edited has measured the one
thing that cannot fail.**

**The action.** After any change to a module's telescope or signature,
**check a consumer before you believe the green, and run `make check` in the
background** so the whole import closure answers. It is `dev/PLAN.md` DD15
that says background, never foreground, and the reason it is background is
so there is no excuse to skip it.

**The measurement, 2026-08-13.** The row repair changed every row telescope
in `src/L/Condensation.lagda.md`: `entryK`, `arSubK` and `tmKeyK` deleted,
`arityK` added, five key facts restated in tied form. The orchestrator ran
that master's own cold check three times, twice to completion, and committed
three times on the strength of it: `20f5704`, `c728e8b`, `3f8301f`.

**All three commits left the tree RED.** The three masters under
`src/L/Condensation/` instantiate those rows and still passed the deleted
arguments. Measured: `agda` exit 42 on `LowerAgree`, `UpperAgree` and
`TwelveAgree`, all three, and `make check` fails at `typecheck` with the
same `Error 42` inside the `MemAgree` module application.

**`make check` was never run once during the session that made those five
master edits.** It found the break in four seconds when it was finally run.
The rule that says run it in the background exists so that its cost is never
a reason, and the cost was never the reason: it was simply skipped.

**Provenance:** commits `20f5704`, `c728e8b`, `3f8301f`, each green on
`src/L/Condensation.lagda.md` alone; the three exit-42 measurements and the
`make check` output, 2026-08-13. Related: [[C-35]], which says a block with
no consumer is untested, and this is its mirror: a CHANGE with no consumer
check is unverified.

### C-41. A retired numbering series must carry its home at every citation, because a resolution check cannot see intent

**Rule:** When a numbering series is retired and a new series reuses its
numbers, **every citation of the old series carries its home beside the code**,
in the same clause: `archived D7`, `struck D8`. A checker that tests whether a
code RESOLVES cannot see this defect, because both codes resolve. **Do not
renumber the old code**; the fix is the home, never the number. And **before
reusing any number, check what else in the tree already writes that shape**:
the collision is rarely with only one other series.

**Measured, 2026-08-13, two dispatches.** `[LJ-1.139]` found **10 bad pointers
in 9 memo headers, 8 of which RESOLVE** and lead to a rule the author never
meant. `[LJ-1.140]` ran the census the same day and found **87 defective lines
in 15 live files, all 87 resolving**, of which 68 are a genuine
archived-decision citation with a live `DD` twin that states a different rule.
`scripts/check-rule-ids.py` was GREEN through every one, for four days, because
it verifies that a code resolves and never that it resolves to the series the
author meant.

**The two multipliers, and they are why this is a law rather than a chore.**
**(1) Detection is not the failure; CLASSIFICATION is.** Two audits saw it
first. `agents/tasks/archive/LJ-0-2/lj-0.2-sufficiency.md:214-218` found the
pair, wrote that both memos name the revoked two-caliber discipline as current,
and then filed it **under preferences** with "fix when next touched".
`lj-0.1-consistency.md` never scanned the memos at all. **A pointer that
resolves to a REVERSED rule was priced as cosmetic staleness, and that bought it
a deferral instead of a fix.** **(2) A retarget can switch a live rule OFF.**
`dev/STYLE-agda.md:73` and `:152` cited archived D7 for naming hygiene while DD7
reads REVOKED OUTRIGHT, so a style rulebook that every dispatched agent reads
before it writes code told them a live rule was dead.

**The corollary that generalizes, and it is measured too.** The census found
**four MORE numbering series writing `D<n>`**: a recon batch inside
`dev/LESSONS.md`, where an R5 recon code of the same shape means a report, `[T95]`'s own defect numbers in
`scripts/check-timing.py`, a task code in `dev/literature/`, and the checkers'
own prose about the notation. **A shape that two series share is usually shared
by more than two.**

**Enforcement:** `scripts/check-rule-ids.py`'s series check, pinned by
`scripts/tests/test_rule_series.py`, with its limit stated in
`scripts/README.md`: it reads the word beside the code, never the sentence, so
it cannot tell which series an author MEANT.

**Provenance:** `agents/tasks/LJ-1-139/lj-1.139-report.md`,
`agents/tasks/LJ-1-140/lj-1.140-report.md`. Related: [[C-32]], a threshold
outliving its tree, and [[C-26]], a duplicated rule drifts.
