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
`_build/k1-report.md`.

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
  Sub-case (D2, 2026-08-03): a formula index is a huge argument even when the
  formula itself is small, once it sits under a satisfaction head (implicit
  φ ψ cost a 168 s check; explicit indices and fifteen named tails fixed it).
- **[A] Keep it neutral**: heavy values never sit inside
  `extensionalV`/`Σ≡Prop`/conversion positions; use stuck terms or variables
  and bridge the concrete membership by one `subst`. (Extends Rule 1.)
  **Measured again (2026-08-03):** prophylactic use before a wall (sixteen
  heavy modules at abstract carriers, 40 s total, G3G4G5); a 1,200-line
  abstract-carrier file at 47.8 s (D2); a 1,347-line predicate at a
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
`_build/g3g4g5-report.md`, `_build/r5d2-report.md`, `_build/k3-report.md`,
`_build/k4-report.md`, and `_build/r5a-report.md`.

### P-j. A path lambda is a normalization request

**Rule:** A path lambda is a normalization request: `λ i → op (p i) (q i)`
forces `op` to whnf at both endpoints.

**Measured (r3c, 2026-08-03):** nine of ten `eval-agree` clauses were free
and the one fatal differed only in whether `op` was sealed.

**Provenance:** `_build/r3c-report.md`.

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
`_build/k3-report.md`.

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
the K2 datum: `_build/k2-report.md`.

**Appended (the GLp probe, 2026-08-04):** a nested small-index type
(`⟪ ⟪ τ ⟫↪ m ⟫`) is free inline but hit a 12 GB heap wall at 4:37 when stored
in a RECORD FIELD; three distinct cures failed, including I-4's prescribed
carrier-level restatement, and the only measured cure is to inline the
decomposition at each use site. Storage position, not expression size, was
the trigger. Provenance: `_build/l3.31-glprobe-report.md`.

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
companion to P-c; the r3b2 read-direction datum: `_build/r3b2-report.md`.

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
of repairing one. **Measured again (D2, R5a-2, K1, 2026-08-03):** statement
positions count: naming transparent `left`/`right` in a theorem statement
cost 170.7 s cold (D2); an imported transparent operation can cost 25.7 s to
invoke even at variable arguments and sealing only moves the cost, so the
alias's job is to be the single site that invokes it (R5a-2); second
prophylactic datum: the base block ran at 1.3 s warm with the discipline
applied first (K1).

**Provenance:** `_build/r3c-report.md` (the wall trail); commit `d15c114`;
companion to P-c and R-36; the D2, R5a-2, and K1 datums:
`_build/r5d2-report.md`, `_build/r5a-report.md`, `_build/k1-report.md`.

**Appended (the PZ polish, 2026-08-03):** when an expensive imported
invocation has consumers in more than one chapter, the single sealed
invocation belongs in the EARLIEST consumer, trunk-wide, not once per file
(`right-at-pair` sealed in Step took the Step+StepInL pair from 202.2 s to
118.2 s; sealing in StepInL alone would have left ~144 s). And profile before
applying a transferred perf datum even when it is trusted: the same 175 s
profile that confirmed the r5a figure (26-29 s per site) also exposed a
larger unattributed cost in the same file (`Slot.k1` 31.7 s, `Slot.tupleIn`
24.9 s). Provenance: `_build/polish2-report.md`.

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
a design around it. Provenance: `_build/l3.32-t22-report.md`,
`_build/l3.32-t19-report.md`.

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

**Provenance:** `_build/r4-report.md` section 6; commit `03f7bc6`.

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

**Provenance:** `_build/g2p-report.md`.

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

**The probe's lifecycle (standing rule, owner-ruled 2026-08-04):** a probe's
value is its VERDICT, and the verdict lives in a report under `_build/`; the
file is scaffolding.

1. **A probe is never committed.** Its home is the working tree, ignored by
   `.gitignore`. (Thirteen were swept into a commit by a `git add -A src/` on
   2026-08-04 and had to be untracked: 3,274 lines of scaffolding the
   repository would otherwise have carried forever.)
2. **The report is written before the probe is deleted, always.** A probe whose
   verdict is not yet in a report is not finished, however green it is.
3. **The file survives only while it is a TEMPLATE for imminent work**, that
   is, while the chapter it seeds is about to be written from it. When that
   chapter lands, the probe goes. Three of the fourteen live probes were kept
   on this ground alone (the face, the re-home, and the generic-reading
   precedent); the other ten were pure history the moment their reports landed.
4. **A pattern worth keeping is not kept by keeping the file.** If a probe
   taught a reusable shape, that shape belongs in this law book or in the
   chapter it seeded. A stray file is not a home for a lesson.

**Provenance of the lifecycle rule:** owner ruling 2026-08-04, after the
accidental commit; the probe inventory of that day is in `dev/JOURNAL.md`.

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
both directions, guards, dispatch chains, and environment plumbing per
clause. Family calibration datum: graph-style chapters price ambient-set
bookkeeping at roughly 3:1 over content lines, not zero (R5a-2's clause
table).

**Provenance:** PLAN row L3.29 (the tripwire accountings and the B ledger);
`dev/memos/L3.29-b-pivot.md`; the L3.30 row's calibrated budget clause; the
R5a-2 family calibration datum: `_build/r5a-report.md`.

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

**Provenance:** `_build/k3-report.md`; commit recorded with the K3 chapter.

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

**Provenance:** `_build/r3a-walls-report.md` (the A/B/C table and the five
candidates); commit `6153e58`; sibling of I-2/I-3; the G2 datum:
`_build/g2-report.md`.

### I-6. hProp connective carriers come pre-shaped; consume at the carrier level

**Rule:** The library connectives' carriers are not opaque: `⟨ P ⊔ Q ⟩` is
already `∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁` and an hProp `⊓` codomain is an untruncated
dependent Σ; consume them at the carrier level (apply the join-valued
function directly and do the `PT.rec` at the plain-sum level, or project the
pair), never wrap the result in another `PT.rec`.

**Measured (2026-08-03):** probe LC-2 (no `PT.rec` needed at `⊓`); K1 lost
three ~10 s checks to the double-truncation confusion.

**Provenance:** `_build/g2p-report.md` (LC-2); `_build/k1-report.md`.

### I-7. Refutations through `∈sucV-elim` land in `⊥*` at `ℓ-suc ℓ`

**Rule:** `∈sucV-elim`'s motive lives at `Type (ℓ-suc ℓ)`, so an ordinal
no-go eliminated through it must land in `Empty.⊥* {ℓ-suc ℓ}` with
`Empty.isProp⊥* {ℓ-suc ℓ}`, not `Empty.⊥`; the consumer is `Empty.rec*`.

**Measured (2026-08-02/03):** G6's not-a-successor branches, R2b's refutation
motive, K4's ordinal contradiction, three occurrences, one of K4's three
errors.

**Provenance:** `_build/g1g6-report.md`; `_build/r2b-report.md`;
`_build/k4-report.md`.

### I-8. `dne` is at level ℓ; bridge structure-level memberships before classical steps

**Rule:** `Switch.dne` takes an `hProp ℓ` while `∈ˢ` lands in
`hProp (ℓ-suc ℓ)`, so every classical step on a structure-level membership
goes `∈s`, then `dne`, then `∈S`; invisible until the error appears.

**Measured (R5a, 2026-08-03):** `cap-outr` (not `cap-outl`) is the classical
half, a one-line idiom.

**Provenance:** `_build/r5a-report.md`.

### I-9. Verify at-most-one witnesses before LEM decides a witness-shaped proposition

**Rule:** Before LEM decides a witness-shaped proposition, verify at-most-one
witnesses; injectivity is often the missing lemma.

**Measured (r2a, 2026-08-02/03):** `isSucc` forced `sucV-inj-ord` (27 lines),
a gap the brief did not list.

**Provenance:** `_build/r2a-report.md`.

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

**Provenance:** `_build/r5a-report.md`; commit `a34907c`.

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

**Provenance:** `_build/r5b-report.md`; commits `d15c114`, `a34907c`; the
same-day extension datums: `_build/g3g4g5-report.md`, `_build/r5d1-report.md`,
`_build/r5d2-report.md`, `_build/k4-report.md`.

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
index). Provenance: `_build/l3.31-p1-report.md`.

**Appended (the P2R fork recon, 2026-08-03):** a route that keeps failing to
supply an index should be suspected of aiming at a false statement. K2, K3,
K4 and P1 each failed to supply an index for a consumer nobody had
truth-checked at the top; the top target (`Matching`) was classically false
(Devlin names and refutes it), and the "named hypothesis" framing has no
defence when the hypothesis is false. The truth check now runs on the
CHAIN'S ROOT before any link is priced. Provenance: `_build/p2-fork-recon.md`.

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
`_build/l3.32-t35-report.md`.

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

**Provenance:** `_build/r2c-report.md` (the no-go trail);
`_build/reshape-report.md`; commits `0322860` and the reshape commit.

### D-11. State two-way adequacy at a tuple, not at a member

**Rule:** Quantify adequacy over the environment, never over a member, so the
equation `m ≡ Tup n δ` never appears in a clause; recover the member-level
pair once through a subset lemma (`T-sub`).

**Measured (G2, 2026-08-03):** the probe's 56-line negation clause became 7
lines arity-generic (16x), zero `pr-inj` chases in twelve clauses, total
adequacy 245 lines both directions. This is the tuple-level restatement of
"price decode-uniqueness once per arity".

**Provenance:** `_build/g2p-report.md` (LC-1); `_build/g2-report.md`
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

**Provenance:** `_build/g2-report.md` (LC-G2-2 through LC-G2-5);
`_build/r5a-report.md` (the three-moves law).

### D-13. Junk is junk only relative to the tower reading it

**Rule:** A value class is junk or not relative to the tower that reads it:
the rud step's level-slot junk is irreducible against the rud level (which
cannot contain itself) and evaporates against the Def tower the moment a
stage holds the level as a member.

**Measured (G3G4G5, 2026-08-03):** `Ljunk` 11 lines, a two-case split, where
LevelDesc spends ~700 lines on the same level cases; choose the carrier by
what it can contain, a sibling of D-9.

**Provenance:** `_build/g3g4g5-report.md`.

### D-14. A closure fragment cannot live inside the block it closes

**Rule:** Any bounding object asked to be closed under the sixteen operations
is infinite (singletons), so it is never a member of the first rud level
`Sset ω`, whose members are all finite; the base block of every
rud-versus-Def statement is a separate theorem with a finiteness proof, and
no offset engineering merges it with the general case.

**Measured (D1, 2026-08-03):** negatively, it removed a planned 150-line
layer; the kernel recon registered the base block as its own residue.

**Provenance:** `_build/r5d1-report.md`.

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

**Provenance:** `_build/r5d1-report.md`; `_build/k2-report.md`;
`_build/k4-report.md`.

### D-16. The inner semantics is the working face; Δ₀ absoluteness is a crossing tax only

**Rule:** Write readers and formulas in the inner semantics at an abstract
transitive carrier; Δ₀ is needed only when a proof crosses between the
ambient and the inner reading, and inner-world readers are reusable across
chapters because they carry no absoluteness obligation.

**Measured (D2, K3, 2026-08-03):** the Graphs-class re-run estimate (~1k
lines, the G2 wall class) became 2,124 lines of ordinary reading work with
zero walls; the pair kit imported whole cost zero lines against 187; no Δ₀
witness was constructed anywhere.

**Provenance:** `_build/r5d2-report.md`; `_build/k3-report.md`.

### D-17. Read the definition, not the case analysis

**Rule:** Describe a total projection (or an operation's junk) through its
definition, not the case analysis that motivated it: `left b = ⋃ (⋂ b)` has
one equality frame over the intersection's two-clause membership, and an
operation whose members are pairs definitionally needs no pairhood split.

**Measured (r5d2, r5b, 2026-08-03):** 30 lines of formula and adequacy
against an estimated 90, removing two of three junk readings; F11-F14 at
four operations cost zero case splits.

**Provenance:** `_build/r5d2-report.md`; `_build/r5b-report.md`.

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

**Provenance:** `_build/k2-report.md`; `_build/k4-report.md`.

**Appended (the P1 stop, 2026-08-03):** the check has two halves and both are
cheap: whether the ranks come from the representation, AND whether the
obstruction blamed on the cofinality is a fact about the tower's own step. K4
ran only the first half: the codes' cofinality is representational (the flat
coding really cuts it to logarithmic), but the obstruction to the block target
is `Sset`'s single-application successor, which no representation touches.
Provenance: `_build/l3.31-p1-report.md`.

### D-19. Price a port against the retiring tree's transitive closure, and split both directions

**Rule:** A "port the pattern" estimate is calibrated against the retiring
chapter's import graph, not its file, and every both-directions adequacy
estimate is split into elimination and introduction and priced separately,
because the introduction has been the larger half twice.

**Measured (2026-08-03):** 250-450 became 3-4x against a 616-line chapter
importing ~1,400 code lines; K3's re-price omitted the 274-line witness-set
construction.

**Provenance:** `_build/k2-report.md`; `_build/k3-report.md`.

### D-20. A many-way disjunction is a fold over ℕ, not a right-nested injection chain

**Rule:** A twelve-way disjunction should be a fold over ℕ (`orUpto` by
induction on the bound), not a right-nested chain of injections; no
truncation nests deeper than one.

**Measured (K3, 2026-08-03):** the twelve-way layer cost 188 lines including
both meta-level translations, against Shape's 354 for the disjunction alone.

**Provenance:** `_build/k3-report.md`.

### D-21. Check whether the approximation's own target is the witness

**Rule:** Before building the machinery a two-sided approximation needs,
check whether the approximation's own target is the witness: the identity
fragment collapses to `λ y k → k`, so the residue is a membership and the
fragment formulation is an indirection.

**Measured (BaseBlock, K4, 2026-08-03):** both halves of the fragment
collapse at ω and at general limits (`powFragment`); removed
`Sep`/`Sstage₂` from the general case.

**Provenance:** `_build/k4-report.md`.

### D-22. A closure hypothesis on the carrier is worth more than a description chapter

**Rule:** Before instantiating a delivered description at a carrier, ask
whether the carrier's own closure already puts the value inside it: at a
rud-closed carrier the whole plain-argument half of `ImgArm` is `Jset-rud`
followed by `memArm`, one line per operation.

**Measured (R5b, 2026-08-03):** 16 dispatch lines plus a 12-line helper vs
the anticipated several hundred.

**Provenance:** `_build/r5b-report.md`.

### D-23. Transparency of a syntax-directed recursion is an interface asset: seal the heavy values, not the syntax walk

**Rule:** Seal the heavy values, not the syntax walk; the transparency of a
syntax-directed recursion is an interface asset.

**Measured (r3c, 2026-08-03):** `Realize`'s dropped certificates were
recoverable from outside in 78 lines only because the walk stayed
transparent.

**Provenance:** `_build/r3c-report.md`.

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

**Provenance:** `_build/l3.31-p1-report.md`; `src/ProbeD10.agda` (untracked).

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

**Appended (2026-08-03):** `_build` report filenames collide across goal
codes: `_build/p1-report.md` named both the [L3.30-P1] probe report (the
cited provenance of I-2, D-7, C-11) and the [L3.31-P1] batch's directed
output; a brief-directed overwrite of law-book provenance is a blind spot no
linter covers. Convention adopted: `_build` reports carry the goal code
(`_build/l3.31-p1-report.md`), and a batch finding its path occupied writes
beside it and says so. Provenance: `_build/l3.31-p1-report.md`.

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

**Provenance:** `_build/g1g6-report.md`; `_build/r2a-report.md`;
`_build/r2c-report.md`.

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

**Provenance:** `_build/r5b-report.md`; `_build/k1-report.md`;
`_build/r2c-report.md`.

**Appended (2026-08-03):** a missing export breeds MORE than one re-proof:
`Sset-zero`'s absence from Step's exports produced two independent local
derivations in BaseBlock (only one of which any report had spotted) and a
third in Bridge. When filing a missing export, grep the FACT, not the name.
Provenance: `_build/polish2-report.md`.

**Appended (2026-08-04):** third instance class: four `V.Coding`
pair/singleton helpers are `private` and were re-derived a third time by the
GLp probe. Provenance: `_build/l3.31-glprobe-report.md`.

### C-15. Close out with a consumer probe; the in-file module beats the probe, then the probe still earns its keep

**Rule:** For any batch that exports into a fixed telescope, apply the
consuming module inside the exporting chapter (making the telescope match a
typechecking obligation), then run the scratchpad probe, since it is the
only place the module parameters get concrete.

**Measured (2026-08-03):** the 25-line `Bridge.Reduce` probe caught
`f3ad704`'s mid-batch telescope change in 1.7 s; K4's in-file application
plus probe exercised `slot-empty` at `A := ∅`.

**Provenance:** `_build/r5d1-report.md`; `_build/k4-report.md`.

### C-16. A wall that survives the obvious seal is a mis-diagnosis: stop sealing, start bisecting

**Rule:** After a seal fails to move a wall, stop sealing and start bisecting
the elaboration; report the failed seal as unmeasured rather than
retro-fitting credit when the real cause is found.

**Measured (K3, 2026-08-03):** the textbook pr-seal was wrong in K3, costing
one full rewrite and three wall events before bisection found the
branch-type cause.

**Provenance:** `_build/k3-report.md`.

### C-17. Record "two routes are circular", never "the base case is circular"

**Rule:** When two routes to a base case are circular, the finding to record
is "two routes are circular", never "the base case is circular"; the third
route is often the textbook's.

**Measured (R5a, 2026-08-03):** R3c's recorded circularity was a scoping
artefact; the classical construction is extensionality relativized to
`p ∪ ⋃p`, 95 lines with one `dne` per direction.

**Provenance:** `_build/r5a-report.md`.

### C-18. Generalize a working frame from the free variable to an index

**Rule:** When a frame works "at the free variable", generalize it to "at an
index" (the target term becomes `var k`, shifted by the binders) and keep
the original as the zero case; the generalization is a mechanical edit that
buys every deeper binder.

**Measured (R5b, 2026-08-03):** `prDesc` → `prDescAt k` made F3/F4's six
cases green on the first check; all de Bruijn arithmetic lives in one
20-line definition.

**Provenance:** `_build/r5b-report.md`.

### C-19. Read the exit code, not the log tail

**Rule:** Read the exit code, not the log tail: unsolved constraints exit 42
while the tail otherwise looks like a clean check.

**Measured (r1b, 2026-08-02):** UnsolvedConstraints exits 42 while the tail
looks clean.

**Provenance:** `_build/r1b-report.md`.

### C-20. Never write `∈ˢ ⋃` / `⊆ ⋃` directly; bind the union term

**Rule:** Never write `∈ˢ ⋃` / `⊆ ⋃` directly; bind the union term.

**Measured (r2b):** Agda's mixfix parser rejects an infix operator applied
to a prefix `⋃` operand.

**Provenance:** `_build/r2b-report.md`.

### C-21. Telescope types may only use level-generic imported names

**Rule:** Telescope types may only use level-generic imported names; inline
level-parameterized predicates into the header, or take the subject
parameters in an inner `module _` block.

**Measured (r2b):** a level-specific imported name
(`L.Constructible.isTransV`, importable only with `{ℓ}` applied) is
invisible inside the module header.

**Provenance:** `_build/r2b-report.md`.

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

**Provenance:** `dev/JOURNAL.md`, the `[L3.32-T12]` entry.

## Adding an entry

Take the next free ID under the series (P-k, R-40, T-3, I-10, D-25, C-23), cite
the source in the entry, and keep the evidence column to measured numbers. When
a new measured wall joins a class an entry already covers, extend that entry's
evidence and provenance instead of minting a duplicate. If a lesson cannot be
sourced, it is not entered; it is surfaced to the owner instead.

### P-NN (proposed 2026-08-06, awaiting the owner's ID): a read lemma is stated where its consumers use it, not where its proof ends

**The law.** When a lemma exists so that consumers can rewrite with it, its
stated right-hand side must be **the form the consumers actually need**, not the
form the proof happened to reach. If it stops one layer early, every consumer
re-normalizes the missing layer, and the same conversion is paid once per
consumer instead of once in total. **Absorb the last layer into the lemma and
seal it**, so the normalization happens exactly once, behind an `opaque`.

**The measurement.** `[L3.32-T86]` profiled `L.Rud.Bridge` at **939 seconds**
and found **95 percent of it in one family**. `γ-compute`'s stated type ended at
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

**The uncomfortable corollary, recorded because it is the real lesson.** The
subtree that D18 retires costs **0.013 s/line over 26,483 lines**; the surviving
trunk cost 0.104. The retiring chapters were not better mathematics, they simply
**stated at abstract carriers and variable indices so nothing re-normalized**,
which is P-h's discipline billed in seconds instead of lines. The newer work
lost that habit and nobody noticed for months. **A discipline that is only
visible in a measurement nobody takes will be lost, and it will be lost in the
direction of whatever is quicker to write.** This is the finding that produced
D30's freeze, and the reason its exit condition includes recording the practice
before the code that carries it is archived.

### C-NN (proposed 2026-08-05, awaiting the owner's ID): a shape certificate is not a meaning certificate

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
