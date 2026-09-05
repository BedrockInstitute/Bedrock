# LJ-1.724-SPLIT: adversarial review of LJ-1.724-SPLIT#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

**Ruling in three sentences.** The NO-GO on `table-sat` at the SPLIT scope is
correct, and this review upholds it: every anchor of the refutation chain
resolves in today's tree, and a refuting instance exists. Two of the return's
own numbers are wrong and this review repairs them for the next brief: the
counterexample lives only at successor `x`, not at "any `x ≥ ω`", and the
membrane constant is at least `rank z + 7`, not `+6`, so the corrected scope
`x + 6 ≤ γ` the return proposes is not safe and would have sent the next GO
into the same wall. Neither repair overturns the verdict; a larger constant
only strengthens a refutation of a universal statement.

## What I read, and what the record carries

I read the report (`lj-1.724-SPLIT-report.md`), the brief
(`LJ-1.724-SPLIT.md`), the filed review (`review-of-table-sat.md`), the probe
(`Probe724Split.agda`), both acceptance arms (`runs/accept-1.out`,
`runs/accept-2.out`, newest last), and every `src/` anchor the chain cites.

`dev/pod/transitions/2026-08.jsonl` carries NO line with
`"task": "LJ-1.724-SPLIT"`: the file ends at sequence 4839, dated 2026-08-27
(dev/pod/transitions/2026-08.jsonl, line 4840 is the last line), and this task
ran on 2026-08-29. As the brief anticipates, the worktree holds the tracked
file at its base commit, so I use the accept arm for the six facts and infer
nothing the transitions file does not carry. In particular the predecessor
instance's `model` and `effort` are not attested by anything in this checkout.

## Question 1: does the verdict LINE match its own BODY?

The verdict line is NO-GO: the obligation is not inhabitable at
`ω ≤ γ, x + 2 < γ` (`lj-1.724-SPLIT-report.md:6-8`,
`review-of-table-sat.md:96-100`). I re-derived the chain link by link at
today's anchors. All of them hold:

- `extAt`'s first clause demands the body at EVERY `z ∈ᴬ w`
  (`src/L/Coding/Model.lagda.md:662-663`, projections at `:667-673`).
- The Step body carries `DefAt zero (suc zero)` and the membership clause
  (`src/L/Coding/Sequence.lagda.md:115-120`, `StepAt` at `:119-120`).
- `DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))`
  (`src/L/Coding/Powerset.lagda.md:442-443`), and `relativize` binds a raw
  `∃̇` at `con c` (`src/FOL/Manipulation/Relativize.lagda.md:55-56`), so code
  and graph must lie in `A`.
- `DefinesAt`'s conjunction form hands `envOne(z)` into the graph
  (`src/L/Coding/Powerset.lagda.md:217-220`; `envOne` at `:125-126`).
- The graph witness puts `pr (code) (graph)` into the table, read as
  `∈ fst T` (`src/L/Coding/Graph.lagda.md:145`).
- `rank-Lset` closes the chain: a member of `Lset α` has rank in `α`
  (`src/L/Ordinal/Stages.lagda.md:190-191`).
- The frame is as cited: `carveSat`
  (`src/L/Axioms/Separation.lagda.md:163-168`), `imageOut`/`imageIn` at
  `:219-229`, `relativize-correct`
  (`src/FOL/Manipulation/Relativize.lagda.md:142-148`), the `Carved` module
  (`agents/tasks/LJ-1-698/Probe698.agda:107-123`).

The line matches the body. The body carries ONE defect in its own numbers,
and it does not touch the line. The counterexample is stated at
"any `x ≥ ω`, `γ := sucV (sucV (sucV x))`"
(`review-of-table-sat.md:70-73`, report `:37-38`), and step 9 aggregates the
per-member demand to `x + 5 < γ` "cofinally in `x`"
(`review-of-table-sat.md:68`). That aggregation is a successor-ordinal step.
At a LIMIT `x`, every `z ∈ᴬ Lset x` has `rank z < x`, and a limit is closed
under finite addition, so `rank z + 7 < x < x + 3 = γ` for every member: the
chain is silent at `γ = x+3` for every limit `x`, including `ω`. Members of
rank cofinal in `x` do not reach `x + 3` through `+7` at a limit. The
refuting instance survives at successor `x`: take `x = ω+1`, `γ = ω+4`. The
three hypotheses hold (`ω+1 < ω+4`, `ω < ω+4`, `ω+3 < ω+4`), and
`z = Lset ω` sits in `Lset x` by the probe's own `Lset-self` leg, anchored at
`Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`), with `rank z = ω`, so the
membrane demand `rank z + 7 < γ` fails. One refuting instance is all the
universal obligation needs. The verdict stands; the counterexample's site is
narrowed to successor `x`.

The return labels its negative model-side and lands nothing in `src/`
(`review-of-table-sat.md:100`). I confirm: the chain's anchors are
code-verified shapes, and no in-tree term decides witness non-existence
through the opaque `carve`. That labeling is correct, and the brief's NO-GO
clause (name which of rank, `DefAt` codes, or the Step conjunct fails) is
answered: it is the `DefAt` membrane.

## Question 2: is every load-bearing claim backed by a `file:line` that resolves today?

Every anchor I opened resolves at the cited lines with the quoted content:
`Separation.lagda.md:163-168` and `:219-229`, `Relativize.lagda.md:47-60` and
`:142-148`, `Powerset.lagda.md:125-126`, `:217-220`, `:442-443`,
`Graph.lagda.md:88`, `:140-147`, `:151-164`, `Sequence.lagda.md:115-120`,
`Model.lagda.md:662-673`, `Stages.lagda.md:137-139`, `:190-191`, `:265-267`,
`Basic.lagda.md:160-161`, `:196`, `Definability.lagda.md:178`,
`Bound.lagda.md:33-45`, `Probe698.agda:107-123`. The run claims I
spot-checked also read as stated: `runs/devframe-t1.out:5-7` (killed,
19.05 s, 2028339200 bytes RSS), `runs/devZs5-r2.out:6` (green, 1.97 s),
`runs/q-1.out:5,23` (green, 27.42 s, `EXIT=0`), and `suc∈or≡`'s branches are
`⟨ sucV β ∈ˢ α ⟩` and `sucV β ≡ α` (`src/L/Ordinal/Stages.lagda.md:137-139`),
so at `β = suc²x` they are indeed the `suc³x` branches the report's repair
claim describes.

ONE constant in the chain is miscomputed, and it is the constant the next
brief inherits. Step 6 prices `rank(envOne z) + 1 = rank z + 3`
(`review-of-table-sat.md:49`), that is, `rank(envOne z)` at `rank z + 2`. By
the tree's own codings it is `rank z + 3`: `envOne y = env {1} (λ _ → y)`
(`src/L/Coding/Powerset.lagda.md:125-126`) unfolds to the one-entry graph
`sett` whose sole member is `pr (# 0) y`
(`src/L/Coding/Environment.lagda.md:84-87`), and `pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆`
is Kuratowski (`src/V/Coding.lagda.md:175-176`), so `rank pr (#0) z = rank z + 2`
and the graph adds one more level (rank is `∈`-recursion,
`src/L/Rank.lagda.md:92-93`). The corrected chain: `rank(graph) ≥ rank z + 4`;
the witness record puts `pr (code) (graph)` into `fst T`
(`src/L/Coding/Graph.lagda.md:145`), so `rank(fst T) ≥ rank z + 7`; and the
table's witness is read through `fst T`, so the table is itself a coded pair
and the A-bound on `T` adds two Kuratowski levels more, giving
`rank z + 9 < γ` as the evidence-backed demand.

Consequences, both adverse to the return's numbers and neither adverse to its
verdict:

- The proposed corrected scope `x + 6 ≤ γ`
  (`review-of-table-sat.md:78-80`, report `:117`) is NOT safe. At `γ = x+6`
  with successor `x`, the worst member has `rank z = x−1`, and
  `rank z + 7 = x+6` is not below `x+6`: the membrane still bites, so a GO
  priced at that scope would wall a second time. The flat-table bound gives
  `x + 7 ≤ γ`; the paired-table reading gives `x + 9 ≤ γ`.
- The refutation itself is unaffected: a larger constant only widens the gap
  at `γ = x+3`.

## Question 3: is the predecessor's enumeration complete?

Almost. All three scope files are written (probe, report,
`review-of-table-sat.md`), the obligation is accounted with its why, W3 is
answered at the brief's own question, and the ARCHIVE USED and LITERATURE
USED blocks match the return's own candidate lists. Two omissions remain,
neither mathematical:

1. **The mandated paste is missing.** The brief orders: run
   `check-survey-quotes.py LJ-1-724-SPLIT` and paste its output
   (`LJ-1.724-SPLIT.md:23`). The report carries no paste. I ran the checker
   today from this worktree: it reports `LJ-1-724-SPLIT clean (0 note(s),
   0 defect(s))`, exit 0. The omission hides no defect, but the instruction
   was not followed.
2. **The acceptance record is not clean and the report does not say so.** The
   newest arm shows `conjunct 1 FAILED`
   (`runs/accept-2.out:10`), the probe itself green at rc 0, 2.29 s
   (`:16`), and `runs/devF.agda` killed at rc −9, 15.77 s (`:17`), error
   class `other` (`:23`), exit `−9` (`:24`). The mechanism: acceptance counts
   EVERY changed `.agda` under the task home as a verification target
   (`scripts/pod/facts.py:520-523`), in path order, and stops at the first
   failure, so the probe's green was discarded when the kept bisection file
   `runs/devF.agda` drew the sweep kill. The brief had ordered non-typechecking
   files to be named `.agda.txt`, never `.agda`
   (`LJ-1.724-SPLIT.md:21`), and about thirty scratch `.agda` files are kept
   under `runs/`. The report documents the swap spiral as tooling debt but
   not this consequence for its own return's six facts. The "fully green"
   headline is true of the probe file; the acceptance facts of the return are
   exit `−9`, error class `other`, `obligations_open` 1.

## What the next brief carries

- **The stated target is refuted; do not re-queue it.** The refuting site is
  successor `x` (for example `x = ω+1`, `γ = ω+4`). At a limit `x` the chain
  is silent even at the SPLIT scope, so a limit-restricted obligation may be
  true at `x + 2 < γ`; the universal statement is not.
- **The membrane constant is `rank z + 7` at the least, and `rank z + 9`
  through the paired table.** A21 places the measurement with the coder, so I
  name the probe and stop there: a probe that CONSTRUCTS the Step-membrane
  witnesses (code, graph, index set, table) inside `Lset γ` at successor `x`,
  once at `γ = x+7` and once at `γ = x+9`, and a third application expected
  to fail at `γ = x+6`. Its GO legs fix the constant by construction,
  including the table's own coding levels, and the next GO's scope takes its
  number from that measurement instead of from rank arithmetic. The probe
  lives in the next task's directory, never under `src/`. I write no `.agda`
  file in this dispatch.
- **Until that probe lands, `x + 6 ≤ γ` is refused as a scope**, and any GO
  priced without it should use the limit-frame route instead: `BoundOver`
  (`src/L/Coding/Bound.lagda.md:33-45`) at a limit, with `Lset`'s five tower
  facts each measured by its own probe, exactly as the return already says.
- **Acceptance hygiene:** scratch files kept for the record go to `runs/` as
  `.agda.txt`, or conjunct 1 goes red on them again at the next dispatch
  whose window a sweep crosses.

## Disposition

`verdict: upheld`. The NO-GO on `table-sat` at the SPLIT scope is correct on
its own chain, and this review corrects the two numbers the next brief would
otherwise inherit: the counterexample site (successor `x`, not "any
`x ≥ ω`") and the membrane constant (`+7` through `fst T` at the least, `+9`
through the paired table, against the return's `+6`). The obligation stays
open, so per the owner's ruling of 2026-08-20 in the slot file, this file
plus exit 0 closes the task under row `sys-critic-upheld-no-go`.

## ARCHIVE USED

- `archive/dev/DD-archived.md:35`: "The questions are: is the refusal correct
  on its own numbers; is the measurement sound; did the BRIEF cause the
  outcome; and is there a cure the return missed." READ. This row carries the
  four questions I attacked with (my slot file's lens, DD25), so it is the
  one archived record this review uses.
- `archive/dev/PLAN-archived.md`: declined, not read. This review rules on
  the return and the live tree only; the archived plan adds nothing to it.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch and landing
  are the program's business in this exchange; the review writes one file.
- `archive/dev/measurements/README.md`: declined, not read. Every measurement
  I cite comes from this task's own `runs/` files and the live `src/` tree.
- `archive/dev/TASKS-archived.md`: declined, not read. The retired `L3.32-T`
  series predates the LJ-1 campaign and nothing in the return touches it.

## LITERATURE USED

- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No external source is
  cited in this review.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. This
  review adds no glossary term and cites none.
- `dev/literature/devlin-errata.md`: declined, not read. The obstruction is
  measured inside the tree's own codings, not in an external account.
- `dev/literature/primary-sources.md`: declined, not read. No fetched text
  backs any step of the ruling above.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. The chain
  runs through `DefAt`, `DefinesAt` and the graph witness, not the level
  formula.
