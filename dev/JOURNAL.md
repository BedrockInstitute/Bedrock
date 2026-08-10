# JOURNAL

The execution record of the two-tower bridge route, `[LJ1]`. One entry per
episode: what was asked, what came back, what it cost, and what changed as a
result.

**The retired route's 4,280 lines are `archive/dev/JOURNAL-archived.md`, unedited.**
It is a required survey target for a new brief, together with
`archive/dev/TASKS-archived.md`, `archive/dev/DECISIONS-archived.md` and `archive/`.

## Conventions

- One heading per episode, dated, with its task code.
- An entry is a RECORD, not exposition. DD23 freezes mathematical prose until
  both trophies land; a journal entry is neither mathematical prose nor
  exempt from ASD-STE100, which binds all working text.
- Evidence is `file:line`. An entry that cannot be checked can only be
  believed.
- An entry is never rewritten to match a later ruling. It was true when
  written and that is what a record is for.
- A superseded entry gets a marker pointing at what replaced it. It does not
  get deleted.

## Entries

### 2026-08-09, `[LJ-0.1]`: the consistency audit, and the gate was RED

**Asked.** Audit every edit since the branch point, `faf02fc..HEAD`, 13
commits and 98 files, against seven named failure classes. Dispatched before
phase 1, because six things changed at once and they interact.

**Returned.** NOT consistent. 30 defects, six load-bearing. `make check` was
RED: the `AGENTS.md` refresh had pushed the file 222 words over its cap and
nobody ran the checker. `make dashboard` crashed, because a suspension banner
was printed to a stdout that another tool parses as data. `check-timing.py`
printed "not enforcing" and then returned 1. `check-ratio.py` measured WARM
against a COLD baseline, and ran Agda inside the commit gate.

**Cost.** One dispatch. It found the gate broken by the change that was
supposed to rest on it.

**Changed.** All 30 repaired across commits `2391f05` to `1410e7c`. The audit
is `_build/lj-0.1-consistency.md`.

**A defect it could not have caught, found while repairing.** `make test` ran
three of seven suites, and the four it skipped had been red for days. One was
red because the `LJ` renumbering changed a checker's return shape, and it had
broken a real behaviour with it: a zero-padded citation `[L3.32-T01]` keyed as
`T01` and resolved against nothing. **Test suites are not checkers, and
nothing ran them.** `make test` now runs all seven.

### 2026-08-09, `[LJ-0.2]`: the sufficiency audit, and a brief clause naming the retired route

**Asked.** The complement of `[LJ-0.1]`. Not what contradicts, but what the
route switch had NOT yet reached. Dispatched to codex through `dispatch.py`.

**Returned.** Three blocking gaps and eight more. The blocking one that
mattered: `dev/ORCHESTRATION.md` still ordered every brief header to state
"the campaign route, R2'", which is the RETIRED route. **Every phase-1 brief
written to the rules would have sent its agent to the wrong route.** It also
found that DD4, the route's core constraint, had no measure, no declaration
and no checker, so by the project's own standard it was a wish.

**Cost.** 675 s, one codex agent.

**Changed.** All three blocking gaps and five of the eight closed. The audit
is `_build/lj-0.2-sufficiency.md`. Its N1, the reuse checker, was REFUSED by
the owner and then partly adopted: no gate, but a report.

### 2026-08-09, `[LJ-0.3]`: the retrospective, and the ruling moves

**Asked.** Judge the route change itself. Read the struggle first, then the
four axes, then say what you would have decided with full authority and no
hindsight. Sent to codex rather than opus for a reason stated in the brief:
the orchestrator planned and executed the change, so its review would confirm
its own judgment.

**Returned.** The direction was defensible, the TIMING was not. It did not
refute the two-tower bridge. The asymmetry it found was exact and both halves
were verified before acting: archived D26 held that a number alone may never
put the route back on the table, and D39 changed the route on `[T257]`'s
figure, which `dev/ledger.toml:172` declares NOT YET CLEAR ENOUGH TO BIND the
constraints that same figure set.

**Cost.** One codex agent. It read the four archives in full.

**Changed, and the owner adopted all of it.** DD2 now separates the RULED
endpoint from the CANDIDATE architecture, and the architecture ruling moved to
`[LJ-2.5]`, after the benchmark and the reuse map exist. Phase 2 gained the
reuse map, its adversarial review and the ruling; `[LJ-3.1]` and `[LJ-3.2]`
are SUPERSEDED with pointers, because rule 3 forbids a third renumbering and
prescribes exactly that instead. DD4 accepts `ledger.py --reuse`, a report and
never a gate. Two laws were admitted with their measurements, `C-28` and
`C-29`. The retrospective is `_build/lj-0.3-retrospective.md`.

**Its best finding, which nobody had written down: the benchmark is
self-set.** Phase 1 builds the wing that `[LJ-2.1]` measures to set the number
phase 3 must beat, so the project writes its own examination paper. **A first
repair claimed DD24's ratio was a partial defence and that was backwards**:
`check-ratio.py` fails only ABOVE the bar, and padding with cheap lines LOWERS
seconds per line, so a padded wing passes it more easily. There was no defence
at all. Three measures replaced the wrong one, and the first is mechanical:
the line benchmark is the SMALLER of `[LJ-1.1]`'s a-priori projection and the
measurement, enforced by `validate_benchmark()` in `scripts/ledger.py`.

### 2026-08-09, the closeout: what phase 1 starts on

**`src/` is untouched by this whole audit campaign.** Its last change is
`86c7b66`, the restore to `main`. Everything since has been documents, rulings
and tooling. The tree is 75 masters and 17,492 in-fence lines, measured.

**Nothing blocks `[LJ-1.1]`.** `[LJ-2.0]`, the owed re-pricing of `[T257]`'s
weak point and `[T261]`'s probe, gates `[LJ-2.5]` only and is done when it is
needed.


### 2026-08-10, `[LJ-0.4]`: the compression campaign, and what a tree does when the mass is not there

**Asked.** Bring the AC side under a line prerequisite before phase 1
continues. The figure moved three times: 16,000, then about 16,400, then
17,000, each after the previous one failed.

**Came back.** Eight blocks planned, seven bands tested, one result.

| Block | Band | Measured | Outcome |
|---|---|---|---|
| A, dead names | -226 to -296 | **-240** | landed |
| B, existential frame | -190 to -340 | **+24** | refused, kit kept |
| C, clause frames | -180 to -315 | **-59** | stopped, it gutted two chapters |
| D, Model arity-generic | -60 to -130 | not run | skipped on review evidence |
| E, traversal share | -60 to -120 | **+19** | refused, reverted |
| G, lex kit | -40 to -80 | **+49** | refused, reverted |
| H, preamble helpers | -30 to -60 | not run | never travels alone |
| I, within-file dedup | -80 to -140 | **-30** | landed one file of seven |
| prose-freed names | -55 to -65 | **-59** | landed, orchestrator only |

**EVERY KIT BLOCK MEASURED NET POSITIVE.** Only deletion measured negative:
block A, the prose-freed names, and one local helper in `Separation`. That is
the campaign's whole result and it is one sentence.

**The one error, six times.** Every survey priced the SAVINGS at the call
sites and never priced the KIT. A parameterized kit costs 31, 43 or 111
lines, and the sites it serves save less. Block A worked because deletion has
no kit. `[LJ-0.8]` diagnosed it after five blocks and `[LJ-0.4i]` confirmed it
as the sixth: a measured surface of 170 raw lines yielded a net of 30.

**Two scans bound what is left, and both say the mass is absent rather than
mispriced.** Tree-wide byte-identical code repeats total 264 RAW lines. The
identifier-blind structural surface is 1,705 lines and sits exactly where
three surveys already looked.

**A third scan closed a class nobody had priced.** 74 of 78 masters are in the
import closure of `Landmarks`, which states both trophies. There is no dead
MODULE. That matters because a dead module would have been a kitless
deletion, the only shape that ever paid here. The class is empty. The same run
found `V.Presentation` mis-declared: 18 wing lines were sitting in the AC
denominator of the DD24 ratio, and the fix moves buckets without compressing
anything.

**Cost.** AC side 17,273 to 17,166. Ten dispatches, four of them refusals with
numbers, and every refusal was worth having.

**Changed.** `dev/ledger.toml` carries the block table so no future survey
writes a band without reading seven tested ones. The dead-name sweep STOPS at
`Codes-out` and `Codes-in`: deleting a set's characterization is content
removal, not compression, and the line where that boundary sits is now
written down rather than felt.
