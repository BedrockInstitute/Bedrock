# LJ-1.712 report: the carve re-bounded, at the stage the door needs

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.712
obligation: agents/tasks/LJ-1-712/Probe712.agda::carve-rebounded
verdict: **NO-GO on the target as named. THE OBLIGATION NAME IS ABSENT ON
PURPOSE.** `review-of-carve-rebounded.md` states the stop. The corrected
target named by `[LJ-1.706]` was priced for truth (D-10) and it is
FALSE at general `gamma`: the re-bounded certificate at
`step 2 gamma` must carry EVERY constant of the relativized pair-graph,
and the readers under `DefBody` pin NUMERAL constants
(`con (numeralL k)`, pins `k = 0..11`) into the spine, not only the
ordinal and the stage the review counted. At `gamma := the empty
ordinal` the pin `k = 11` provably does not fit under
`step 2 emptyset`, and every link of the proof is a `src/` lemma. The
refutation is a term: `refuted-pin`
(`agents/tasks/LJ-1-712/Probe712.agda:217-220`). The probe is green:
exit 0, median 1.68 s over three forced rechecks. The witness meter
reads `missing`, `1 UNRESOLVED of 1`, `probe_red=False`
(`runs/meter-1.out`). The door itself is NOT tied to `mkBoundedFo`'s
stage: `AtCert` / `rebound-lands`
(`Probe712.agda:85-111`) fire at ANY stage a certificate is presented
for. That is the brief's W3 question, answered by a term, and it
survives the stop.

Written as a skeleton before any Agda beyond the predecessor read and
filled as each answer landed (C-22). No commit, no push. I wrote only
inside `agents/tasks/LJ-1-712/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated; the delivered probe carries `--safe` and has no hole; and
nothing lands in `src/`. The probe is a raw `.agda` file, so it
carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio
bar cannot fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 786,923,648 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), 37 percent of it. No restructuring was needed and
the heap-wall clause never fired.

**EVERY NUMBER BELOW IS MEASURED IN THIS WORKTREE.** `floor-1` is the
row that rechecked the predecessor cone (`Probe706`, `Probe698`,
`Probe693` and the `src/` facts they import); every later row ran on
the interfaces those probes left.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause: take the type from the probe that
typechecked, and the verdict from the report; if the report is NO-GO or
names the statement FALSE, do not inhabit that type.

`[LJ-1.706]`'s report is NO-GO on `below-from-carved`
(`agents/tasks/LJ-1-706/lj-1.706-report.md:9-15`, stated in
`agents/tasks/LJ-1-706/review-of-below-from-carved.md:1-6`). My brief
does NOT name `below-from-carved`; it names the CORRECTED target that
the same report wrote down at `:15`. So the clause does not stop this
task; it did two things:

1. I did not inhabit `below-from-carved`, and I do not import its
   absent witness. My frame imports only types and terms that
   typechecked: `Below`, `Identified`, `Bound-in-tower` from
   `Probe706` (its own section 1, green), `recordedFo` / `bound-of` /
   `Carved` from `Probe698` (`:73-129`, green), `step` / `door-next` /
   `Door` / `isL-ord` from `Probe693` (green).
2. The corrected target itself had to be PRICED FOR TRUTH before
   proof (D-10). Priced: it is false at general gamma. That pricing,
   not a failed proof attempt, is this task's stop.

## 2. D-10, THE PRICING THAT DECIDED THE TASK

The target: assemble `BoundedFo (Below' (step 2 gamma)) phi_r` by
hand, fire the door at `Lset tau`, land at `Lset (sucV tau) =
Lset (step 3 gamma)` by computation. The certificate is a per-constant
demand: for EVERY `con c` in `phi_r`'s normal form, a proof of
`Below' tau c = ⟨ fst c ∈ Lset tau ⟩`
(`src/L/Axioms/Separation.lagda.md:431-432`,
`src/FOL/Manipulation/Bounding.lagda.md:63-64`).

The inventory, each site read at source:

- The TWO constants `[LJ-1.706]` counted: the ordinal `(gamma , hgamma)`
  (from `recordedFo`'s own binder, `Probe698.agda:73-74`) and the
  relativize constant `LsetS gamma ogamma`
  (`src/FOL/Manipulation/Relativize.lagda.md:56-57`, one `con` per
  unbounded binder, same constant each time). Both fit under
  `step 2 gamma`: `gamma-fit` and `stage-fit`
  (`Probe712.agda:134-148`) are green terms.
- The constants the review did not count: `tagAtL` carries
  `con (numeralL k)` (`src/L/Coding/Model.lagda.md:585-586`), and the
  callers under `DefBody` pin `k = 1` (`keyArityAtL`,
  `src/L/Coding/CodeSet.lagda.md:135`), `k = 0` (`envOneAt`,
  `src/L/Coding/Powerset.lagda.md:128-129`), and `k = 2,3,4,5,8,9,10,11`
  (`closedAt`'s eight clauses, `src/L/Coding/Model.lagda.md:2172-2189`),
  besides the twelve-shape reader (`src/L/Coding/Shape.lagda.md:140-145`,
  `:160-189`). The reachability chain is cited site by site in the
  review: `DefBody` -> `DefAt` -> `StepBody` -> `StepAt` -> `GraphAt` ->
  `PairGraphAt` -> `recordedFo`, all in `src/` or in the green
  predecessors.
- The KILLER: the pin-11 piece is
  `⟨ # 11 ∈ Lset (step 2 gamma) ⟩` for every ordinal gamma, and it
  fails at `gamma := ∅` by rank arithmetic made exact through
  `ord∈Lset→∈` (`src/L/Ordinal/Stages.lagda.md:266-268`) and the
  successor case-split `∈sucV-elim`
  (`src/V/Model.lagda.md:218-222`). `no-11`
  (`Probe712.agda:186-210`) closes all four cases;
  `refuted-pin` (`:217-220`) lifts it to the general row.

C-42 did not fire as a refutation-sweep of `Below` (no negation of
`Below` anywhere); the sweep question for THIS finding, the incomplete
inventory, is answered in the review's sweep section: one live site
(the `[LJ-1.706]` review's inventory paragraph), `[LJ-1.704]`
unaffected, `[LJ-1.711]` to be re-read against the flat re-bound, and
`[LJ-1.714]`'s count redirected. D-26 did not bind: no well-founded key
was built.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. The
skeleton (imports plus restated types, all sections absent) ran first:
`runs/floor-1.out`, exit 0, 28.14 s, 786,923,648 bytes. The floor is
the cone recheck (Probe706 -> Probe698 -> Probe693 -> src/), not my
file: every later row of mine is 1.7-10.6 s. The import trim is
`Probe706`'s trim, reused (W2): `src/` plus `Probe693` plus `Probe698`
plus `Probe706`; the `Probe652`/`Probe679` chain is NOT imported and
the one lemma it carried that I need (`Lset∈suc`) is re-derived
inline from `Lset-suc` and `𝒟ₒ-intro`
(`Probe712.agda:125-129`), exactly as `[LJ-1.697]` re-derived it
from `src/`.

## 4. WHAT IS DELIVERED, ALL GREEN

1. **Section 1, the frame** (`Probe712.agda:68-81`): imports and
   `phi_r`, the relativized pair-graph as a term.
2. **Section 2, the door is general** (`:85-111`): `AtCert` at an
   ARBITRARY stage tau, `rebound-carve` / `rebound-door` /
   `rebound-lands`: given ANY certificate at tau, the carve exists, is
   in `𝒟ₒ (Lset tau)`, opens the door, and lands in
   `Lset (sucV tau)`. THE W3 ANSWER: `𝒟ₒ-intro` is not tied to
   `mkBoundedFo`'s stage; it is tied to the CERTIFICATE, and only to
   it.
3. **Section 3, the two counted constants fit** (`:125-148`):
   `Lset∈suc`, `mono-up`, `gamma-fit`, `stage-fit`.
4. **Section 4, the refutation** (`:152-220`): the pin inventory in
   the header comment, `ord#`, `climb`, the numeral chains, `no-11`,
   `pin-11`, `refuted-pin`.

The obligation name `carve-rebounded` is absent on purpose; no
postulate stands in for it, and the meter confirms the absence
(`runs/meter-1.out`).

## 5. W2 ANSWER

Nothing is proved twice. Section 2 is stated at a GENERIC stage (tau
is a parameter, not `step 2 gamma`), so the door-generality fact is
instantiated nowhere and reusable everywhere. `Below`, `Identified`,
`Bound-in-tower`, `recordedFo`, `bound-of`, `Carved`, `step`,
`door-next`, `Door`, `isL-ord` are imported from the probes that
typechecked them. `Lset∈suc` is the one re-derivation, forced by the
import trim that saved the 144.56 s `Probe652`/`Probe679` frame
(`lj-1.697-report.md:126`), and it is three lines from `src/` names.
The refutation's numeral chain is built once from `self∈sucV` /
`∈sucV-inl` and reused by both chains. No deadline forced a fixed
form; no conflict to report.

## 6. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. One dead
fragment (`#∈Lset`, a helper superseded by a direct `subst` in
`refuted-pin`) was deleted in-file before this report; it never
typechecked green in a landed state, so there is nothing to archive
and no `dev/LESSONS.md` entry cited it.

**P-l: obeyed.** Every type names `Lset` stages, which are opaque
(`src/L/Constructible.lagda.md:221-223`), or is a certificate/lemma
type (`pin-11`). No type names a transparent presentation of a stage
value; no conversion between successor presentations is asked anywhere.

## 7. WHAT THE SHAPE RESISTED

- **What it cost.** 231 lines, 112 code. Floor 28.14 s cold-cone.
  First all-green run 10.58 s. Median forced recheck 1.68 s. Highest
  peak 786,923,648 bytes against the 2 GiB cap. No heap wall.
- **What the shape resisted.** Nothing mathematical in Sections 2-3:
  the general door compiled on the second attempt, the two fits on
  the next. ALL the resistance was in the refutation's plumbing: the
  `subst` direction along `numeralL-fst` (the third time this campaign
  has hit the wrong-way `subst`, after `[LJ-1.706]`'s `p-1`), the
  `⊥*`-level of `∈sucV-elim`'s P, an off-by-one in the climb chain,
  and `¬` resolving to the Omega-level negation. One `UnequalTerms`
  (`Lset∈suc`, `sym` missing on `Lset-suc`) was the same lesson again.
- **What I had to weaken.** Nothing. The refutation is stated at full
  generality (all gamma, by one instance); no hypothesis was added to
  `Below`, none removed from the certificate demand.
- **What I could not close.** The pin-11 route is closed for good, but
  the two rescue shapes are open: R2 (numeral-free readers) is the one
  that makes the original corrected target true; R1 (the floor above
  the numerals) needs a measurement the tree does not have (an upper
  stage bound for `fst (numeralL k)`). Both are priced in the review.

## 8. WHAT THE NEXT BRIEF NEEDS

1. **DECIDE BETWEEN R1 AND R2 BEFORE `[LJ-1.704]` CLOSES** (review,
   "the corrected target, beside the original"). R2 re-aims the reader
   stack at `arityNumAtL`'s shape (`ωʟ`-bound arities instead of
   pinned numerals); only R2 can make "re-bound at `step 2 gamma`"
   true as stated. R1 buys the route only above a numeral floor that
   is itself unmeasured.
2. **DO NOT RE-DISPATCH** `AtCert`, `rebound-lands`, `gamma-fit`,
   `stage-fit`, `Lset∈suc`, `mono-up`, `ord#`, `climb`, `no-11`,
   `refuted-pin`: green here, importable from `Probe712`.
3. **DO NOT READ `[LJ-1.714]`'s COUNT AS THE DECIDER.** The count
   never gated the certificate: `relativize` repeats the same constant
   at every binder, and that constant's fit (`stage-fit`) is
   count-independent. The count still matters for `[LJ-1.706]`'s
   overshoot argument about `mkBoundedFo`'s own stage, which is a
   DIFFERENT question and still open.
4. **`[LJ-1.704]` STANDS.** Its identification is at `mkBoundedFo`'s
   stage, which absorbs the numerals; this stop does not touch it.
   What this stop removes is the belief that the identification can
   feed `Below` through a re-bounded door at small gamma.
5. **THE GENERAL DOOR IS CAMPAIGN PROPERTY.** Section 2 is the fact
   the next door-shaped task should import instead of re-deriving:
   wherever a certificate can be presented at stage tau, the door
   opens and lands at `sucV tau`.

## 9. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 231 | 112 | `Probe712.agda` |
| `phi_r` | 2 | 2 | `Probe712.agda:80-81` |
| `AtCert` + `rebound-lands` | 27 | 17 | `Probe712.agda:85-111` |
| the two fits + `Lset∈suc` | 24 | 15 | `Probe712.agda:125-148` |
| the refutation | 56 | 42 | `Probe712.agda:165-220` |

The brief estimated 90 to 220 lines for W3. The delivered term set is
112 code lines. The estimate's worth was spent where the review says:
on the inventory that the estimate's premise (two constants) got
wrong.

## 10. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. All runs from
the repository root, through `runs/run.sh` (mechanism copied from
`agents/tasks/LJ-1-706/runs/run.sh`).

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/floor-1.out` | skeleton frame, cone recheck | 28.14 | 786,923,648 | 0 |
| `runs/sec2-1.out` | `Below'` NotInScope | 1.87 | 607,354,880 | 42 |
| `runs/sec2-2.out` | `Formula S` carrier mismatch | 1.85 | 608,632,832 | 42 |
| `runs/sec2-3.out` | section 2 first green | 10.32 | 771,522,560 | 0 |
| `runs/sec34-1..15.out` | refutation ladder (14 rows) | 0.06-10.26 | <= 785,743,872 | 42 |
| `runs/sec34-16.out` | first all-green probe | 10.58 | 779,436,032 | 0 |
| `runs/recheck-1.out` | forced recheck, post-prune | 10.13 | 762,658,816 | 0 |
| `runs/recheck-2.out` | forced recheck | 1.68 | 605,421,568 | 0 |
| `runs/recheck-3.out` | forced recheck | 1.68 | 605,405,184 | 0 |
| `runs/meter-1.out` | witness meter | 1.77 | not taken | 1 |

Median of the three forced rechecks of the delivered probe **1.68 s**.
Highest peak of any run **786,923,648 bytes** (`runs/floor-1.out`),
37 percent of the 2 GiB cap. No heap event.

Witness meter, one obligation: `runs/meter-1.out`, `missing`,
`1 UNRESOLVED of 1`, `probe_red=False`, `[NotInScope]` at the
generated witness for `carve-rebounded`. That is the designed absence.
The meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`,
as `[LJ-1.697]` and `[LJ-1.706]` ran it. I did not add a `.venv` to
this worktree.

## 11. COMMIT

Nothing committed, nothing pushed, per the Boundary. The working tree
holds exactly: `agents/tasks/LJ-1-712/Probe712.agda`,
`agents/tasks/LJ-1-712/lj-1.712-report.md`,
`agents/tasks/LJ-1-712/review-of-carve-rebounded.md`,
`agents/tasks/LJ-1-712/runs/` (run.sh, floor-1, sec2-1..3,
sec34-1..16, recheck-1..3, meter-1). The program commits by explicit
path.

## 12. SURVEY REPAIR NOTE

Added by LJ-1.712#2, the lint-back-to-author repair attempt. This return's
first delivery carried no survey answer, and acceptance conjunct 6 reads THIS
file: `report_of()` (`scripts/pod/check-survey-quotes.py:427-439`) resolves to
the task-named `lj-1.712-report.md` and never to a `review-of-*.md`
companion, so the answer belongs here and not in the review file. Each
candidate below was opened. None bears on the verdict: the verdict rests on
`src/` terms, the green predecessors, and this task's own runs.

## ARCHIVE USED

- `archive/dev/DD-archived.md`: declined, not used; the DD ruling series closed on 2026-08-18, and no row of it decides a line of this report.
- `archive/dev/ORCHESTRATION.md`: declined, not used; the orchestrator's process rules govern dispatches, not the truth of a refutation term.
- `archive/dev/PLAN-archived.md`: declined, not used; a construction registry frozen on 2026-08-20, with no bearing on the pin inventory.
- `archive/dev/STATUS-archived.md`: declined, not used; the goal table of the internalization route archived on 2026-08-09.
- `archive/dev/TASKS-archived.md`: declined, not used; the archived L3.32-T task index names no site this report touches.

## LITERATURE USED

- `dev/literature/BIBLIOGRAPHY.md`: declined, not surveyed; the rud-route source list is not evidence for a tree term.
- `dev/literature/devlin-errata.md`: declined, not used; the refutation is internal to `src/` terms, so no published account of the levels is needed.
- `dev/literature/primary-sources.md`: declined, not used; Jensen, Devlin and Jech quotations are not evidence here.
- `dev/literature/level-formula-slot-roles.md`: declined, not used; the door-stage question was closed by the probe's own section 2 terms.
- `dev/literature/glossary-review-2026-08.md`: declined, not read; a glossary term review, with no bearing on this verdict.
