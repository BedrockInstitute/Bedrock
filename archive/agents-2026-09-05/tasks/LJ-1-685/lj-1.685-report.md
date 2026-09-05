# LJ-1.685 report: the reverse direction, with the K now chosen

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.685
obligation: agents/tasks/LJ-1-685/Probe685.agda::same-as-graph-reverse
verdict: **GO.** The reverse conjunct of `SameAsGraph` is inhabited at
`[LJ-1.678]`'s `K`, with `powIter` and the `[LJ-1.681]` bridge as hypotheses.
The obligation is discharged: `same-as-graph-reverse` typechecks green
(`Probe685.agda:89`, arm `runs/accept-1.out:16`, obligations delta -1 at
`runs/accept-1.out:27`). Cold full-probe price under the wide caliber:
71.29 s wall, 833667072 B peak (`runs/p-3.out:5-6`). Nothing landed in
`src/`.

The report was written as a skeleton before any Agda, and filled as each
answer landed (C-22). The first author session left two defects, both
measured by the four reviews this task then took: a stale verdict line
(`review-of-LJ-1-685-1.md:8-11`) and two survey sections left at
"(filled at return)". This redispatch is the one act every review named
(`review-of-LJ-1-685-4.md`, section 3, "The repair, one act"): the fill
below, the true verdict line above, and the precision fixes N1, N2 and N4
from `review-of-LJ-1-685-1.md` folded into sections 1 and 2. This redispatch
changed no `.agda` file and no `runs/` file. It started no Agda process,
as the first review instructed ("do not re-run the probe",
`review-of-LJ-1-685-1.md`, section 4 item 2): the arm is the measurement.
It ran one check, `check-survey-quotes.py LJ-1-685`, to verify the fill.
No commit, no push. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the wide tier, one Agda process at a
time. I did not set `GHCRTS`. Nothing is postulated: no `postulate`
occurs in any `.agda` or `.agda.txt` file of this task home. The probe is
a raw `.agda` file, so it carries no fence, counts 0 in-fence lines, and
the ratio bar cannot fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It starts no
collection and no phase 3. No Boundary clause is in conflict.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.672]` closed **NO-GO on `same-as-graph`**
(`agents/tasks/LJ-1-672/lj-1.672-report.md:9-11`). That NO-GO is not a
stop here. The report does not name `SameAsGraph` FALSE. It names both
directions uninhabited at the type `[LJ-1.520]` wrote, and it funds an
adequate `K` first (`:174-180`). The critic upheld the stop
(`agents/tasks/LJ-1-672/review-of-LJ-1-672-1.md:8`).

`[LJ-1.678]` closed **GO on `k-value`**
(`agents/tasks/LJ-1-678/lj-1.678-report.md:9-10`). The type I take is
`KValue.facts` at `ωBlock gam` for a generic ordinal
(`Probe678.agda:27-32`). The report says the reverse can now choose this
`K` and says not to expect `k-value` to discharge `powIter`
(`:150-154`).

`[LJ-1.681]` is a sibling, not a closed predecessor. This worktree has no
`agents/tasks/LJ-1-681/` directory. `[LJ-1.684]` restated that bridge as
a HYPOTHESIS, DOWN, at one environment
(`agents/tasks/LJ-1-684/Probe684.agda:69-72`). This file takes that
type's SHAPE at this consumer's shifted layout (N1,
`review-of-LJ-1-685-1.md`, section 1.4): `Bridge` at `Probe685.agda:66-69`
is quantified over `S ^ (13 + n)` environments at the shifted slots
`sh13 w`, `sh13 b`, because that is the layout `[LJ-1.520]`'s matrix fixes
(`Probe520.agda:125`, `:160`).

The types I take are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `SameAsGraph` reverse | graph to Σ₁ | `Probe520.agda:192-195` | TYPE, green; not inhabited |
| `k-value` | `KValue.facts` at ω-block | `Probe678.agda:32` | GO |
| `W3.Pins.pins` / `Reverse.hpins` | pins at the numerals | `LJ-1-672/runs/W3.agda` | GO; not re-dispatched |
| `Bound.PowIter` | `𝒟ₒ`-climb | `src/L/Coding/Bound.lagda.md:147-152` | hypothesis |
| `Bridge` | `LsetGraphAt → graphBndAt` | `Probe684.agda:69-72` | hypothesis; 681's debt |

**W2.** The reverse is written once at a generic arity and generic slots,
the same carrier `[LJ-1.520]` used. `k-value` instantiates at
`fst (lookup b γ)`. No fixed form (`n = 0`, `lam = ω` only) is required.
There is no deadline conflict.

**W4.** This task retires no module. The probe modules live in this task
home, are tracked, and are never deleted. No `archive/` row is due.

## 2. D-10, BEFORE THE PROOF WAS PRICED

The target is the reverse conjunct of `SameAsGraph`
(`Probe520.agda:195`):

    ⟨ γ ⊨ LsetGraphAt w b ⟩ → ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩

at `[LJ-1.678]`'s `K`, with `powIter` and the `[LJ-1.681]` bridge as
hypotheses.

I did not find a Tarskian or cardinality obstruction. The formula is a
prenex of thirteen existentials over `transK ∧ pins ∧ graphBndAt`
(`Probe520.agda:124-164`). Pins is green. transK is transitivity of
`Lset λ`, which `Bound.trans∈λ` supplies
(`src/L/Coding/Bound.lagda.md:93-94`). graphBndAt is the hypothesized
bridge. Packing is plumbing with an explicit formula argument
(`[LJ-1.672]` `lj-1.672-report.md:184-185`).

`Lset-only` takes `IsOrd` and does not produce it
(`src/L/Hierarchy.lagda.md:334-335`). `k-value` takes a generic ordinal
(`Probe678.agda:27`). Instantiating at `fst (lookup b γ)` puts `IsOrd` in
the `k-value` telescope. That is not a fourth input.

C-42 does not fire. This is not a refutation of a site.

## 3. THE TERM, DELIVERED

The delivered telescope, at a generic arity `n`, slots `w b` and
environment `γ` (`Probe685.agda:71-76`):

    PowIterHyp → IsOrd (fst (lookup b γ)) → Bridge →
    ⟨ γ ⊨ LsetGraphAt w b ⟩ → ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩

The body does three things (`Probe685.agda:77-87`): lift the graph
hypothesis from `γ` to the thirteen-slot environment (`LF.lift13`, the
`hgraph` row at `:86-87`), apply the hypothesized bridge (`br T.env`),
then pack `transK`, `pins` and `graphBndAt` into the thirteen
existentials (`A.from-conj T.htrans P.hpins hgraph`) and close at
`levelFo-Σ₁` (`A.to-levelFo`). The pieces are modules under `runs/`:

| module | role | site |
|---|---|---|
| `LIFT.agda` | graph weakened by 13 front slots, numerals and K | `runs/LIFT.agda:3-5` |
| `PINS.agda` | pins at the 13-slot env from 672 combinators | `runs/PINS.agda:3-4` |
| `TRANS.agda` | transK at the ω-block K, `kk = LsetS lam ordλ` | `runs/TRANS.agda:31`, `:36` |
| `PACK.agda` | 13 existentials packed at a GENERIC formula | `runs/PACK.agda:3-6` |
| `PACKAT.agda` | the pack sealed at `Matrix.matrix`, hypothesis | `runs/PACKAT.agda:3` |
| `W3.agda` | thin re-export of PACK | `runs/W3.agda:3-6` |
| `RENAME3.agda` | renameFo commute for LsetGraphAt | `runs/RENAME3.agda:3` |

The `K` is `[LJ-1.678]`'s: `TRANS.agda:31` opens `W678.Block` at
`fst (lookup b γ)` under the `IsOrd` argument. `powIter` is bound and not
spent (`Probe685.agda:77`), as `[LJ-1.678]` said to expect
(`lj-1.678-report.md:150-154`): the bridge carries the graph side, so the
reverse body needs no `𝒟ₒ`-climb. The conclusion is not vacuous: it
depends on the graph hypothesis and the bridge
(`Probe685.agda:78`, `:86-87`; arm `agda_vacuous: false`,
`runs/accept-1.out:32`).

## 4. THE PRICE, MEASURED

All runs under `GHCRTS="-A64m -I0 -M2g"` wide, one Agda process at a
time, through the wrapper `runs/run.sh` (wall cap is perl's alarm).

**The floor, priced first** (owner's ruling 2026-08-23). `FLOOR.agda.txt`
states the obligation with a hole standing in for the term
(`runs/FLOOR.agda.txt:87`). The frame costs 2.58 s and 603684864 B
(`runs/floor-2.out:8-9`), and the only error is the standing hole
(`runs/floor-2.out:5`). The first floor run had an `UnequalTerms` error
in the frame statement itself (`runs/floor-1.out`, error at
`FLOOR.agda:45`), fixed before the floor was read. So the elaboration
frame was never the problem on this obligation, and the cost lives in the
term. Each run module then carries only the imports its own rows use
(`runs/LIFT.agda:4` says it outright: "Does NOT import Probe520 or
DefBodyB").

**The pieces.** LIFT 17.96 s (`runs/lift-1.out:5`, EXIT=0 at `:23`);
PINS 2.78 s (`runs/pins-1.out:5`, EXIT=0 at `:23`); TRANS 2.30 s
(`runs/trans-1.out:5`, EXIT=0 at `:23`); RENAME3 8.06 s
(`runs/rename-3.out:2`).

**The walls, and the restructures that routed them** (owner's ruling
2026-08-23: a wall is a signal to restructure in the same dispatch). The
sealed packing first walls at its cap four times: W3 as one sealed module
killed at 300 s and 180 s (`runs/w3-2.out:6`, EXIT=142 at `:25`;
`runs/w3-3.out:6`, EXIT=142 at `:25`), PACKAT killed at 90 s and 60 s
(`runs/packat-1.out:6`, EXIT=142 at `:25`; `runs/packat-2.out:6`, EXIT=142
at `:25`). The restructure: the pack moved to a generic module with the
formula as an explicit argument (`runs/PACK.agda:5-6`), green at 1.30 s
(`runs/pack-2.out:5`, EXIT=0 at `:23`; the run before it,
`runs/pack-1.out:6`, died at 118.02 s EXIT=1 `:25`), PACKAT re-sealed at
the hypothesis matrix, green at 2.26 s (`runs/packat-3.out:5`, EXIT=0 at
`:23`; same at `packat-4`, `packat-5`), and `W3.agda` became a thin
re-export so the name the brief used stays a green module
(`runs/W3.agda:5-6`; arm 0.86 s at `runs/accept-1.out:23`). The full probe
itself hit the heap cap once: killed at EXIT=137
(`runs/p-2.out:2`, SIGKILL under `-M2g`). After the split above, the same
obligation went cold green at 71.29 s and 833667072 B peak
(`runs/p-3.out:5-6`, EXIT=0 at `:23`).

**The arm.** `runs/accept-1.out` ran every `.agda` under this task home:
eight files, all rc 0 (`:16-23`), `Probe685.agda` at 2.25 s (`:16`),
36 of 36 changed files inside this task home (`:24-25`), 0 in-fence lines
(`:26`), obligations delta -1 (`:27`). Arms `accept-2` and `accept-3`
still ran Agda (accept-2 with one load kill, `runs/accept-2.out:21`),
and `accept-4` to `accept-6` re-read a warm tree (`runs_all: []`), so
the cold numbers above are the prices to plan with, not the arm's warm
ones.

**W3, answered with the measurement.** The brief estimated 120 to 260
lines for the packing. The delivered packing stack is 164 lines
(`runs/PACK.agda` 93 + `runs/PACKAT.agda` 59 + `runs/W3.agda` 12), inside
the estimate. The whole task home is 439 lines of Agda across 8 files.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **The forward direction is still open.** This task closed only the
   reverse conjunct (`Probe520.agda:195`). The forward conjunct
   (`:194`) stays uninhabited, as `[LJ-1.672]` measured for both.
2. **`powIter` is still only a hypothesis, and unspent here.** Nothing in
   the reverse body consumes it (`Probe685.agda:77`). Its discharge is
   untouched by this GO.
3. **The bridge is still `[LJ-1.681]`'s debt.** It is taken DOWN, at one
   environment (`Probe685.agda:66-69`, shape from
   `Probe684.agda:69-72`). Any forward-direction brief needs it up, or
   needs it at the shifted layout this file fixed.
4. **`IsOrd` sits in the telescope.** `k-value`'s generic ordinal puts
   `IsOrd (fst (lookup b γ))` before the bridge (`Probe685.agda:73`). A
   consumer that lacks the ordinal fact pays for it separately.
5. **`KValue.facts` itself is not consumed.** Only the `K` value
   (`kk = LsetS lam ordλ`, `runs/TRANS.agda:36`) is spent. The fourteen
   facts stay available for the next consumer.

## 6. THE FOUR REVIEWS, ANSWERED

Four reviews stand in this home. The first overturned the stale verdict
line (`review-of-LJ-1-685-1.md:8-11`); the next three upheld that overturn
(`review-of-LJ-1-685-2.md:8`, `review-of-LJ-1-685-3.md:8`,
`review-of-LJ-1-685-4.md:8`). All four named the same one repair: fill
the two survey sections, an act only the author slot can do
(`review-of-LJ-1-685-4.md`, section 3). This redispatch is that act. The
three precision notes of the first review are folded in: N1 (the bridge
type is the shape at the shifted slots, section 1 above), N2 (the reverse
conjunct is `Probe520.agda:195`, not `:194`, section 2 above), N4 (the
678 GO verdict cites `lj-1.678-report.md:9-10`, not `:1`, section 1
above). I wrote no `review-of-*` file: the verdict is GO, and
`review-of-same-as-graph-reverse.md` is the NO-GO instrument.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** `archive/dev/DD-archived.md:30`
  is DD18: "THE ARCHIVE AND LITERATURE SURVEYS are sections of the brief
  and of the return, not a hope." That ruling is the mechanism this
  section discharges. The four-question lens of DD25 at `:35` belongs to
  the review slots, and this return does not use it.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read. The dispatch
  rules of the retired route do not bind this term; the live process
  facts are in `scripts/pod/`.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read. The standing
  status is `dev/pod/screen.toml` and no planning history bears on this
  return.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read. A retired
  status page; the campaign state that matters here is on the screen.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read. A retired task
  ledger; this task's producers are `dev/pod/queue.toml` and the
  transition log.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:84-86`: "A port that writes
  one is doing something the textbook does not do, and it owns the slot
  bookkeeping alone." That is why `runs/LIFT.agda` exists: no source text
  owns the thirteen-slot bookkeeping this lifting does, so the probe
  carries it, and carries it once, at generic arity (W2).
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read. No source was
  added and none was missing.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read. This return
  certifies no Devlin leaf and quotes no scanned certificate.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read. No
  naming question arose and this return proposes no `dev/glossary.toml`
  entry.
- **`dev/literature/primary-sources.md` DECLINED.** Not read. The bridge
  stays a hypothesis, so no primary text decides anything in this return.
