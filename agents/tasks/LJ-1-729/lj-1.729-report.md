# LJ-1.729 report: `keyS-in-carrier-stage`, the key bound

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.729
obligation: agents/tasks/LJ-1.729/Probe729.agda::keyS-in-carrier-stage
verdict: **NO-GO STATED ON THE BRIEF'S TYPE, GO ON THE CORRECTED
SCOPE.** The brief's type is FALSE at `omega in^sv gamma`; the D-10
truth check refuted it before any proof was priced, and
`review-of-keyS-in-carrier-stage.md` records the counterexample at
`gamma := sucV (sucV omega)`. The corrected target, one hypothesis
wider (`closedomega gamma`), is STATED and INHABITED in the same probe
as `keyS-in-carrier-lim`. The probe TYPECHECKS: p-20 is the verdict
run on the delivered bytes, EXIT=0. Nothing is postulated, the probe
carries `--safe`, nothing lands in `src/`, and `stage-read`,
`carved-is-hier` and `table-sat` are not inhabited.

## 0. THE PREDECESSOR QUESTION

The missing-lemma finding is taken from
agents/tasks/LJ-1-725-SPLIT/lj-1.725-SPLIT-report.md:9 and section 6
item 1: the backward half of `stage-read` dies at the DefAt membrane
because no landed lemma bounds `keyS`, `Sat` or the environment sets
by the carrier's stage. That report's verdict is a STOP, not a NO-GO
against the bound's truth, so this dispatch proceeds. The predecessor
probe's two lemmas (`Lset-trans-set`, `ord-in-Lset`) were NOT copied:
this route consumes `Lset-out`, `𝒟ₒ∋⊆`, `Lset-mono` and `ord-tri`
directly, and the predecessor's report marked them reusable only for
the spine, not for this bound. The type under obligation is the
brief's own, taken verbatim up to the two membership glyphs (the
hypothesis reads at the V structure, the conclusion at the L
structure; the probe's comment at the `open` lines records this).

## 1. WHAT WAS BUILT

1. The climb, REAL. `Climb.code-in-iter` places the code of
   `mapFo iota phi` at SOME finite iterate `sucIter j sigma` of any
   stage sigma that holds the alphabet's values and the numerals, by
   one line per formula constructor (twelve) over an EXISTENTIAL
   iterate: no weight function, no max, no arithmetic on the index.
   Two helpers carry the shape: `pr-in-iter` pairs two pieces sitting
   at different iterates at ONE common stage (the sum, by
   `sucIter-shift` and `+-comm`, plus the fixed +2 that
   `pr∈Lset-suc` charges), and `tagStep`/`pairStep` wrap the
   numerals.
2. The absorption, REAL. `close` runs the climb at a common
   `sigma in^sv gamma` and lifts by `+omega-iter` then `closedomega`
   then `Lset-mono`. The case split is `ord-tri omega delta`: below,
   equal, above; each branch names its sigma.
3. `keyS-in-carrier-lim`, REAL and INHABITED: the brief's type with
   `closedomega gamma` added. This is the review's corrected target.
4. `keyS-in-carrier-stage`, STATED, NOT INHABITED: the brief's type,
   exported at the file's top level as a Type. No postulate stands in
   for it and no weaker form is inhabited under its name.

## 2. THE FLOOR, AND THE HEAP WALL

Per the heavy-object rule the floor was priced before the proof:
imports first, then the file with a minimal body. The import cone is
`L.Coding.CodeSet` and `L.Ordinal.StageArith` with their dependencies
(708 cached interfaces under `_build/2.8.0/agda`); the frame alone
costs about 1.4 s and 350 MB on this pane, so the climb's own rows
are the small remainder. THE HEAP WALL WAS MET AND ROUTED IN THE SAME
DISPATCH. Runs p-12 to p-14 (the twelve `with`-abstractions over the
opaque tower) died without an Agda message: 435 MB at 2.8 s, then
1.12 GB at 9.3 s, then 1.91 GB at 18.2 s, killed near the 2 GB wide
cap, each run slower and fatter than the last on identical bytes. The
restructure replaced every `with` with projection-driven helpers
(`pairStep`, `tagStep`, and `fst`/`snd` at the use sites), which
keeps the goal types definitional instead of re-elaborating them
twelve times. The new shape was TESTED at its own site: p-15 fell to
an ordinary type error at 1.8 s and 354 MB, and p-16 went green at
2.2 s and 366 MB. The wall is reported as a finding WITH the routed
cure, per the coder clause. Two runs (p-12, p-13) also show a runner
artifact, `time: signal: Invalid argument` with no Agda output; the
direct run of the same bytes between them passed, and the mechanism
was re-validated on the green [LJ-1.725-SPLIT] probe in this pane
before the restructure.

| run | wall | peak | note |
|---|---|---|---|
| p-1 to p-11 | 0.06 to 2.30 s | 107 to 359 MB | one defect fixed per run, never repeated unchanged: parse of the brief's unnamed telescopes, missing `hPropStructure` import, `+` scope, `#`-prefix precedence, `key` import, first-argument `_+_` arithmetic, `subst` directions |
| p-12 to p-14 | 2.8 / 9.3 / 18.2 s | 436 MB / 1.12 GB / 1.91 GB | the `with`-shaped file killed at the cap, no Agda message: THE HEAP WALL |
| x-ref-725split | 1.92 s | 392 MB | runner re-validated on the green predecessor probe, EXIT=0 |
| p-15 | 1.81 s | 354 MB | restructured file, ordinary type error left |
| p-16 | 2.17 s | 366 MB | restructured file GREEN |
| p-17, p-18 | 0.06 / 0.19 s | 107 MB | two import-tidying parse slips, fixed at once |
| p-19 | 2.03 s | 387 MB | green after the import trim |
| p-20 (verdict) | **2.14 s** | **387,006,464 B** | **EXIT=0, green, delivered bytes** |

## 3. W3 ANSWER

The brief's W3: whether `keyS A phi` sits in `LsetS gamma ogamma` at
`omega in^sv gamma`, estimated 40 to 120 lines. Answer: **NO at that
generality, and the estimate was below the truth.** The bound is
false at successor gamma (review, section 2), and the repaired scope
cost 250 non-blank lines of raw `.agda` probe, of which about 90 are
the climb and its helpers, about 70 the corrected target, and the
rest imports and the shift lemmas. The successor-height reading of
NO-GO also fails: no FIXED iterate of gamma bounds the family, the
climb's index grows with the formula's size, which is the whole
content of the review.

## 4. W2 ANSWER

The climb is stated ONCE at a generic carrier: `Climb` quantifies
over an arbitrary small alphabet `K`, an arbitrary value map `f`, and
stage facts `hf` and `hnum`; `keyS-in-carrier-lim` instantiates it at
the alphabet `⟪ fst A ⟫`. No sibling proof is duplicated and no
landed reading is re-derived. No deadline forced a fixed form.

## 5. WHAT THE NEXT BRIEF NEEDS

1. Fund the move of `Climb`, `pr-in-iter`, the shift lemmas and the
   `closedomega` absorption into `src/`, with `L.Coding.CodeSet` the
   likely home, priced from p-20, not from this report's prose.
2. The `stage-read` spine may now be re-briefed against the
   corrected bound: its DefAt membrane wanted exactly this key bound,
   and `keyS-in-carrier-lim` supplies it wherever `closedomega`
   holds. Price the spine after the bound lands in `src/`.
3. Do not re-fund `relativize-correct`, `Lset-trans-set`,
   `ord-in-Lset`, or `smallAny`'s hidden stage: the corrected route
   never touches `boundingOrd`.
4. If a later chapter needs the bound at a non-closed successor, the
   scope to price is a slack hypothesis (the carrier held omega
   stages below gamma), not the brief's hypothesis. The counterexample
   kills the brief's scope for every successor gamma.

## 6. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 2.14 s (`runs/p-20.out`) |
| peak, verdict run | 387,006,464 B, 18 percent of the 2,147,483,648-byte wide cap |
| runs this dispatch | p-1 to p-20, plus x-ref-725split |
| heap wall | MET at p-12 to p-14 (1.91 GB peak), routed by restructure, re-tested green at p-16 |
| probe lines | 279 total, 250 non-blank, raw `.agda` (in-fence count 0, the ratio bar cannot fire) |
| brief estimate | 40 to 120 lines (W3); the corrected scope cost 250 and the estimate's scope was false |
| caliber | `-A64m -I0 -M2g`, never set here |
| `src/` edits | none |

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not read. This dispatch measures its own probe; no archived dispatching rule bears on a NO-GO statement or an Agda run.
- `archive/dev/DD-archived.md:1` `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Declined: not read. The clauses this dispatch answers to live in the slot file and the brief; the closed DD series is history.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not read. The live screen is `dev/pod/screen.toml` and the live direction is `dev/pod/direction.md`; this task follows those.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not read. The route this task sits on is the live queue's, not the archived table's.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the \`L3.32-T\` series`. Declined: not read. The `L3.32-T` series predates the POD and shares no obligation with LJ-1.729.

## LITERATURE USED

- `dev/literature/devlin-II5.md:248` `concrete set K(u), the finite sequences over the formula set, the variables`. Read. This is the classical counterpart of the reviewed bound: Devlin's `K(u)` substrate is bounded by the carrier and consumed at limit-closed levels, which is the shape the corrected target restores with `closedomega`. The review cites the digest as the standing record.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. A raw `.agda` probe and its records carry no translation surface.
- `dev/literature/devlin-errata.md`: declined, not read. This dispatch cites no Devlin page; the errata scope is the literature team's to keep.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. The slot census belongs to the graph tasks; the climb here counts constructor nodes only.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No new source is cited beyond the II.5 digest named above.
- `dev/literature/primary-sources.md`: declined, not read. The fetch map is the literature team's record; this dispatch fetches nothing.
