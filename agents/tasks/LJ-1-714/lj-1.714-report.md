# LJ-1.714 report: the binder count, as a number

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.714
obligation: agents/tasks/LJ-1-714/Probe714.agda::binder-count
verdict: **GO. The count is 4447.** `binder-count` is delivered as
`(γ : S) → unb (recordedFo γ) ≡ 4447` (`Probe714.agda:128`), proved by
`refl`, so the typechecker computed the counter to exactly that numeral and
refuses any other. Two companion rows pin the number on the relativized
formula itself: its constant-bound binders are 4448 (`Probe714.agda:135`),
that is the 4447 relativized ones plus the one passed-through outer bound
at `con γ`, and it carries no unbounded quantifier at all
(`Probe714.agda:140`). `[LJ-1.706]`'s "at least three"
(`agents/tasks/LJ-1-706/lj-1.706-report.md:14-15`) was true and was never a
measurement; the measurement is 1482 times its lower bound. Written as a
skeleton before any Agda beyond the predecessor read and filled as each
answer landed (C-22). No commit, no push. Nothing lands in `src/`.

**EVERY NUMBER BELOW IS MEASURED IN THIS WORKTREE**, at
`agents/tasks/LJ-1-714/runs/`. One Agda process per run; the pane's
`GHCRTS="-A64m -I0 -M2g"` (wide) was read off the environment and never
set or changed by this task.

## 1. WHAT THE OBLIGATION ASKED, AND HOW THE COUNTER IS HONEST

The brief asks for the exact count of relativized binders in the base
formula, the relativized pair-graph `[LJ-1.698]` built, as an equality a
typechecker can refuse. The refusal is manufactured this way:

- `unb` (`Probe714.agda:58`) counts the `∃̇`/`∀̇` nodes of the object
  syntax, one clause per constructor, generic in the constant domain. It
  reads only the shape, never a constant's payload.
- `relativize` turns each unbounded quantifier into exactly one binder
  whose bound is the relativizer constant
  (`src/FOL/Manipulation/Relativize.lagda.md:57-58`), passes bounded
  quantifiers through (`:59-60`), and changes nothing else, so the
  source-side `unb` count IS the count of relativized binders carried by
  the relativized formula.
- `conb` (`Probe714.agda:72`) counts the bounded-quantifier nodes whose
  bound is a constant. Applied to the relativized formula it must read
  4447 relativized binders plus the one outer `con γ` binder that
  `relativize` passed through (`Relativize.lagda.md:60`): hence
  `conb-rel ... ≡ 4448` (`Probe714.agda:135`). This row pins the number
  on the relativized pair-graph itself, which is where the brief's
  premise 3 put the base formula.
- `rel-unb ... ≡ zero` (`Probe714.agda:140`) is the remark at
  `Relativize.lagda.md:64-66` made checkable: no unbounded quantifier
  survives.

`refl` succeeds only if the counter reduces to the numeral. A stuck
counter cannot equal a numeral, so a green run is a certificate that the
reduction walked the whole formula and the number is the syntax's own.

Generality: all three rows quantify `γ` and the relativizer `A` as
variables of `S` (`Probe714.agda:128`, `:135`, `:140`). The counters
ignore constant payloads, so the count cannot depend on either.
Instantiating `A := LsetS γ oγ` gives the `[LJ-1.698]` instance of
`bound-of` (`agents/tasks/LJ-1-698/Probe698.agda:97-101`) unchanged, and
`recordedFo` is restated verbatim from `agents/tasks/LJ-1-698/Probe698.agda:84-85`
(the brief's basis line 87 is the `recordedΔ₀` row that relativizes the
same formula one line later). No `LEM`-carrying frame beyond `Sequence`'s
own parameter is imported; the Separation, Hierarchy and Definability
cones that `[LJ-1.698]` needed for the door are not needed for the count.

## 2. W3 ANSWERED: ONE BINDER-CLASS DEFINITION DOES NOT UNFOLD, AND THE COUNT COMPUTES ONLY PAST IT

The brief's W3 asked whether the count reduces at all or whether the
binders hide behind a definition that does not unfold. Measured answer:
one does, and the count computes only past it.

- `satGraphAt` is sealed under `opaque`
  (`src/L/Coding/Graph.lagda.md:203-205`). The seal is measured, not
  aesthetic: the comment there names the 2,459 ms coercion it prevents.
- With the seal on, `unb (recordedFo γ)` is STUCK at
  `unb (satGraphAt ...)` and the equality cannot be checked
  (`runs/run-4.out`; the mismatch reported there is against the sealed
  normal form). At this presentation the count does not reduce.
- The tree's own cure is `opaque unfolding`, consumer-side, scoped to
  the declarations inside the block. The one prior consumer is
  `src/L/Condensation.lagda.md:7185-7187`, marked there as the only
  place that opens the seal. The probe does the same around the three
  obligation rows (`Probe714.agda:121-140`). An unfolding block that
  does not contain the rows has no effect: at `runs/run-4.out` the
  block sat at top level with the name in scope and the term stayed
  stuck; at `runs/run-5.out` a module wrapper inside the block was
  refused (`NotAffectedByOpaque`). The rows must sit inside the
  block. `V/Collapse`'s `π-member` confirms the scope reading by
  structure: it stays outside its block and reaches `π` only through
  the computation law (`src/V/Collapse.lagda.md:56-66`).
- With the seal lifted for the rows, the counter runs to the end and
  the machine first refused my numeral: `4447 != 249` (`runs/run-6.out`).

That last line is the report's second finding. 249 was my own hand audit
of the definition tree, built by reading every reader:
`PairGraphAt` (`src/L/Coding/Sequence.lagda.md:328-329`), `GraphAt`
(`:292`), `ApproxAt` (`:287-289`), `StepAt`/`StepBody` (`:113-120`),
`domAt`/`inDomAt` (`src/L/Coding/Model.lagda.md:277-280`,
`:270-271`), `extAt` (`:662-663`), `prAtL` (`:122-123`), `appAt`
(`:160-161`), `prAt` (`src/L/Coding/Base.lagda.md:285-288`) and the
sealed-then-unsealed `satGraphOn` (`src/L/Coding/Graph.lagda.md:105-115`)
with `twelveAt` and the clause readers of Model. The audit missed a
factor of 18, chiefly because `DefBody` has three conjuncts, not the one
my first read caught (`src/L/Coding/Powerset.lagda.md:438-441`), and
because each clause reader carries its own frame. A reading of this
reader tree is not a measurement. The computing counter is.

## 3. WHAT THE NUMBER DOES TO THE RE-BOUNDING ARITHMETIC

Premise 2's law stands as `[LJ-1.706]` stated it: the bound climbs one
successor per relativized binder, each climb a `bound2` merge
(`agents/tasks/LJ-1-706/lj-1.706-report.md:14`, on
`src/FOL/Manipulation/Relativize.lagda.md:57` and
`src/L/Axioms/Separation.lagda.md:449-462`). This task supplies the law's
missing operand.

- If the law is applied at 4447 binders, the merge chain floors about
  4447 successors above the constants' own stages. Every arithmetic row
  that placed the bounding stage from a count of 3 is wrong by about
  4444 successors. The brief's reasoning section named this outcome:
  the true count refutes the step-2 arithmetic before `[LJ-1.712]`
  finishes, and that is cheap.
- What survives, and strengthens: `[LJ-1.706]`'s finding was that the
  merge chain pushes the stage ABOVE where the door needs it, so the
  placement row fails in the direction the door needs unless the carve
  is re-bounded. A larger count pushes harder in the same direction.
  Whether `[LJ-1.712]`'s statement survives in a corrected form is the
  mathematician's call; the number it now has is 4447, machine-checked,
  and 4448 minus the outer binder if it counts only constant-bound
  binders of the relativized formula (`Probe714.agda:135`).
- Premise 4 is respected: the count and the merge are separate. This
  task merges nothing; `conb-rel`'s 4448 is delivered precisely so the
  merge arithmetic can separate the outer `con γ` binder from the
  4447 relativized ones without re-deriving either.

D-10: the recorded residue here was a lower bound, not a target, and a
lower bound cannot be false. It is now sharpened to the exact value. The
corrected target beside the original is the same target with 4447 in
place of "at least three". C-42 does not fire: no statement was
refuted, a count was measured, and there is no second site of the same
false shape to sweep.

## 4. THE RUN

| run | file | what it shows | exit | price |
|---|---|---|---|---|
| run-1 | `runs/run-1.out` | `_+_` not in scope | 42 | 1.3 s |
| run-2 | `runs/run-2.out` | first full counter run, stuck | 42 | 6.3 s |
| run-4 | `runs/run-4.out` | seal on: count does not reduce | 42 | 6.3 s |
| run-6 | `runs/run-6.out` | seal lifted for the rows: `4447 != 249` | 42 | 1.5 s |
| floor-1 | `runs/floor-1.out` | file-cold (interface removed), green | 0 | 1.99 s, peak RSS 523,223,040 B |
| final | `runs/final.out` | green, no warnings | 0 | 2.04 s, peak RSS 523,091,968 B |

The obligation's price is 2.04 s and 523,091,968 bytes peak, 24 percent
of the 2,147,483,648-byte wide cap. **NO HEAP WALL WAS MET ANYWHERE IN
THIS TASK**, so no restructuring clause applied and none was needed. The
frame was never the problem; the file imports `Sequence` (whose own cone
it pays for) and nothing heavier. `scripts/gate/lint-agda.py --check`
exits 0. The only `.agda` under the task home is the probe itself, as
conjunction 1 requires; no file failed finally, so no `.agda.txt` exists.

## 5. PROPOSED CLAUSE (coder file; the owner rules)

Measured here, twice, at a cost of two wrong priors: **a count is a
computation, not a reading.** When a brief asks a coder for a count over
syntax, hand-built figures from reading definitions are not evidence,
even when every leaf was checked; only a term the typechecker computes
counts, and a counter that stops at an `opaque` seal reports no number
at all. Proposed wording for the slot file: before quoting any count of
syntax nodes, land it as a `refl`-proved equality in the task's probe.

## 6. CONFORMANCE

- Scope: exactly `agents/tasks/LJ-1-714/Probe714.agda`,
  `agents/tasks/LJ-1-714/lj-1.714-report.md`,
  `agents/tasks/LJ-1-714/review-of-binder-count.md` (not needed: this is
  a GO, so no NO-GO review exists), and `agents/tasks/LJ-1-714/runs/`.
  Nothing outside the task home was written; nothing lands in `src/`.
- The probe carries `--safe`, no postulate, no hole, and one
  consumer-side `opaque unfolding` justified in place
  (`Probe714.agda:107-122`).
- Ratio bar: the probe is a raw `.agda`, carries no fence, counts 0
  in-fence lines, and the bar cannot fire.
- Standing direction (`dev/pod/direction.md:37`): one SRC collection
  after LJ-1. This task is LJ-1 work; it starts no collection and no
  phase 3. No Boundary clause is in conflict.
- C-22 held: the report existed as a skeleton before the first Agda run
  and was filled at each answer.
- Never committed, never pushed. The working tree is exactly as this
  report describes it.

## APPENDIX: THE SURVEY DUTY, DISCHARGED ON REJECTION (attempt 2)

The return above failed acceptance conjunct 6 only (`runs/accept-1.out`,
`error_class: lint`): it carried no `ARCHIVE USED` and no `LITERATURE USED`
section. The checker's `report_of()` reads this file and never a review
companion (`scripts/pod/check-survey-quotes.py:427-439`), and the
lint-back-to-author routing directs the citation here
(`scripts/pod/pod.py:2722-2730`), so the re-dispatched coder appends the two
sections. Nothing above this heading is altered. The reads are the second
attempt's, made 2026-08-28 in this worktree.

### ARCHIVE USED

- archive/dev/DD-archived.md:24: "A build brief that cannot name its widest
  unmeasured term, and the probe that measures it, is not ready to send",
  read as the probe discipline this task ran under; the brief named W3 and
  `Probe714.agda` measured it.
- archive/dev/ORCHESTRATION.md:230: "the verdict still goes in the report",
  read as the return-form contract the archived D-1 row states.
- archive/dev/PLAN-archived.md: declined, not used: the construction
  registry frozen at 2026-08-20; it carries nothing on binder counts or on
  this task's route.
- archive/dev/STATUS-archived.md: declined, not used: the retired route's
  96-goal status table; no row touches LJ-1.714.
- archive/dev/TASKS-archived.md: declined, not used: the retired `L3.32-T`
  dispatch index; no row of this task's series is in it.

### LITERATURE USED

- dev/literature/glossary-review-2026-08.md:712: "relativization is 相对化 in
  Chinese logic", read for the term the report's subject turns on; the
  report's "relativized binder" is that established term.
- dev/literature/formalizations.md:86: "two instances of V = L are
  formalized differently: one is relativized and the", read as the
  literature record of the relativized-formula presentation whose binder
  count this task measured.
- dev/literature/devlin-errata.md: declined, not used: errata for Devlin's
  book; the count runs over the tree's own syntax, not over Devlin's text.
- dev/literature/level-formula-slot-roles.md: declined, not used: slot-role
  notes; nothing in them bears on the probe or on this return.
- dev/literature/BIBLIOGRAPHY.md: declined, not used: the source index; the
  count is machine-checked in the tree and needed no source list.
