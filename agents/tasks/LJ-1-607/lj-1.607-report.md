# [LJ-1.607] report: the untruncation at the band, and the cure that was never lost

tier: probe. **No master was edited. Nothing landed in `src/`. No
commit, no push.**

Every claim is marked **MEASURED** (read at the cited line, or a machine
result under `runs/`) or **INFERRED** (my composition or judgement).

**STATUS: NO-GO on `band-untruncation`, AND THE BRIEF'S PREMISE ABOUT
THE LOST CURE IS FALSE.** The term `pick-canonical` was never lost. It
is in the tree, it was re-checked cold at this dispatch, and it is
green. It does not reach the band's payload, and the term that shows
why is in the probe. The statement of the NO-GO is at
`agents/tasks/LJ-1-607/review-of-band-untruncation.md`.

## 1. THE LEAD FINDING, AND IT CORRECTS THE BRIEF

**THE BRIEF'S PREMISE 5 IS FALSE AT TODAY'S TREE.** The brief says
`pick-canonical` "exists in **no Agda anywhere**: not in `src/`, not in
`archive/src/`, only as that one name in the index". MEASURED, by
grep at this dispatch:

```
$ grep -rln "pick-canonical" . | grep -v ".git/"
archive/dev/LJ-dispatch-index.md
agents/tasks/LJ-1-136/lj-1.136-report.md
agents/tasks/LJ-1-136/ProbeLJ1136B.agda
```

The term lives at `agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114`, in a
file the library puts ON THE INCLUDE PATH (`bedrock.agda-lib`,
`include: src agents/tasks`). The brief's grep covered `src/` and
`archive/src/`. It did not cover `agents/tasks/`, the directory
`[LJ-1.142]` ruled the probes' home, tracked and never deleted.

**AND THE TREE'S OWN RECORD SAYS THE SURVIVAL WAS DELIBERATE.**
`archive/dev/JOURNAL.md:878-881`, the `[LJ-1.227]` entry: the probe sat
UNTRACKED in `src/`, "one `git clean` from gone", and was moved into
`agents/tasks/LJ-1-134/` and `agents/tasks/LJ-1-136/` and tracked,
"which is where D-1 says a probe lives". The archive is faithful. The
search was wrong, not the record.

**AND THE CURE STILL WORKS, COLD, AT THIS TREE.** MEASURED. The
interface Agda held for the file was computed 2026-08-19 and only
validated by a warm run (`runs/p136-2.out`, exit 0, 1.17 s), so both
probe files (`LJ-1.136` and its dependency `LJ-1.134`) were copied
VERBATIM into `runs/cold/` and re-ascribed from a fresh interface
namespace: `runs/p136-cold-1.out`, **GREEN, exit 0, 1.83 s, 327 MB
peak, cap 600 s**, under the program's caliber. Both halves of the cure
elaborate today:

- `pick-canonical` (`agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114-116`),
  the selection that does not depend on which proof of non-emptiness
  reached it: the term `[LJ-1.114]` could not write.
- `discharge` (`agents/tasks/LJ-1-136/ProbeLJ1136B.agda:146-148`): from
  the truncated existence of a constructible injective graph, an honest
  injection, with no truncation left over.

## 2. THE MEASUREMENTS, WITH THE CAPS

Every typecheck ran under `GHCRTS=-A64m -I0 -M2g` as the program set it
on this pane. One Agda process at a time. The wrapper is
`runs/run.sh`, taken from `[LJ-1.605]`; the cap is perl's alarm and
every `.out` records it.

| run | file | cap | result |
|---|---|---|---|
| W3 alone, cold | `runs/w3-1.out` | 120 s | GREEN, 1.30 s |
| W3 alone, warm | `runs/w3-2.out` | 120 s | GREEN, 1.20 s |
| direct route, refused | `runs/direct-refused-1.out` | 300 s | exit 42, 1.14 s |
| cure, warm (validate only) | `runs/p136-1.out` → `runs/p136-2.out` | 600 s | exit 0, 1.17 s |
| cure, COLD | `runs/p136-cold-1.out` | 600 s | **GREEN, 1.83 s, 327 MB** |
| probe, attempt | `runs/final-1.out` | 600 s | exit 42, 6.26 s (see below) |
| probe, final | `runs/final-2.out`, `runs/final-3.out` | 600 s | **GREEN, 1.93 s / 1.76 s** |

`runs/p136-1.out` is the first attempt at the recheck and it failed
with `[FileNotFound]`: the rehomed file's top module name
(`ProbeLJ1136B`) no longer matches its path under the library's include
roots, so it cannot be imported through the library as-is. The cold
recheck restored its original include context with explicit `-i` flags.
That mismatch is a defect of the rehoming, not of the term: any future
import of a `[LJ-1.13x]`-era probe must give the flags, or copy.

`runs/final-1.out` is the intermediate attempt, exit 42 at a scope
check, and it doubles as the frame floor the heavy-object rule asks
for: the import frame (`L.SquareLawClosed`, `L.Absorption` and the
rest) checked cold in that run before the error, at 6.26 s wall. The
final frame runs at 1.8 to 1.9 s. The term itself costs nothing; the
frame is cheap at this caliber, and no trimming was needed.

## 3. W3, THE WIDEST UNMEASURED TERM

The payload under the band's truncation, written out, TYPE ONLY, in
`runs/W3.agda:46-50`: one pairing function on the pairs of the members
of δ, and one injectivity proof, under the truncation sign. Two rows
prove the transcription: `payload-is-the-truncation`
(`runs/W3.agda:53-54`, `refl`) and `untruncation-is-the-missing-
direction` (`runs/W3.agda:69-73`, `refl`), which ties the obligation's
type to `[LJ-1.605]`'s `missing-direction-type`
(`agents/tasks/LJ-1-605/Probe605.agda:177-181`). Written first,
typechecked alone, GREEN inside the two-minute cap.

What W3 reads off the type, and what the whole task turns on: **the
payload's two components are AMBIENT**. No `Formula`, no L-set, no
satisfaction and no ordinal grade occurs in it
(`agents/tasks/LJ-1-594/runs/W3.agda:42-43`). The truncation sits over
ambient function data.

## 4. WHAT THE TREE HAS FOR UNTRUNCATION

The search the brief ordered (D-10), answered row by row. Every
candidate is marked: does it reach THIS payload or not.

| candidate | site | reaches the band payload |
|---|---|---|
| `leastOf` | `src/L/WellOrder/Base.lagda.md:158-161` | **no, not directly.** It is the tree's ONE elimination of a truncation into data, and its goal `Σ IsLeast` is a proposition by `isPropLeastOf` (`src/L/WellOrder/Base.lagda.md:136-139`). It reaches a payload only through a code family it can select. |
| `L.Cardinal`'s `least` | `src/L/Cardinal.lagda.md:115-117` | **no.** MEASURED at today's lines: the predicate is `InjP γ = ∥ Inj γ ∥₁ , squash₁` (`src/L/Cardinal.lagda.md:66-67`), so the engine delivers the least INDEX untruncated while the ambient injection witness stays truncated inside the proposition. The tree's own chapter is a live instance of the wall: the ambient function never comes out. |
| `InjCode` + `leastOf`, the `[LJ-1.576]` route | `agents/tasks/LJ-1-576/Probe576.agda:77-84`, `:141` | **no.** `InjCode F a b` is an hProp, four Ω-valued conjuncts, so the coded selection absorbs the truncation. This is the property the brief asked about, and it is a property of a CODE family. |
| `pick-canonical` + `discharge`, the `[LJ-1.136]` cure | `agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114-116`, `:146-148` | **no.** Verified green, cold, at this dispatch. It untruncates `Ne = ∥ Σ A ∈ Mem (Lset β), ⟨ Good A ⟩ ∥₁` (`:98-99`), the truncated existence of a CONSTRUCTIBLE graph at a bounded stage. The band's payload is an ambient function package. |
| direct `PT.rec` into `sq δ` | measured at `runs/direct-refused-1.out` | **no.** The elaborator demands `isProp (sq δ)` first and refuses the only candidate (`[UnequalTerms]`, exit 42). |
| split support by constant endomap | `dev/literature/truncation-and-selection.md:155-159` | **no.** Theorem 16: split support for a type is equivalent to a weakly constant endomap on it, and such an endomap on `sq δ` IS a canonical selection of one pairing. |

The survey behind the "one engine" row, MEASURED: 66 files in `src/`
use `PT.rec`; the scan of every elimination target found propositions
only (memberships, satisfaction, set-ness, `IsLeast`), plus `⊥`. No
exception.

**THE PROPERTY COMPARISON, ANSWERED.** The band's payload has NO
property comparable to `InjCode`'s. `InjCode` is an hProp family, and
that is what lets `leastOf` untruncate on the coded side. `sq δ` is a
Σ whose first component is a function
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`), the truncation sits over
ambient data, and no code family stands anywhere in its type.

## 5. THE TERM THAT REFUTES IT HERE

The probe is green and carries five rows
(`agents/tasks/LJ-1-607/Probe607.agda:160-254`). Two of them are the
answer:

- **`the-circle`** (`agents/tasks/LJ-1-607/Probe607.agda:228-229`): a
  term of `Untruncation`, composed with the band supply the tree
  already holds (`sq-trunc-closed`,
  `src/L/SquareLawClosed.lagda.md:325-328`), IS `SqParam α₀`. By
  `[LJ-1.604]`'s product identity
  (`agents/tasks/LJ-1-604/Probe604.agda:160-164`) that is the
  untruncated square law at every infinite ordinal of the band, fiber
  by fiber. So the untruncation is not a cheaper object than the
  square law: composed with the held supply, it IS the square law.
- **`route-b-assembles`** (`agents/tasks/LJ-1-607/Probe607.agda:240-254`):
  the canonical-selection route, assembled from three pieces. Engine
  (`leastOf`) plus decoding (from a selected code to the honest
  pairing; `[LJ-1.136]`'s `discharge` is this piece, green today) plus
  ONE missing piece, the BRIDGE: from the ambient truncated pairing to
  a coded truncated existence. Supply the bridge at any selectable code
  family and the site's untruncation exists.

**WHY THE BRIDGE IS THE WALL.** The bridge must turn an ambient
pairing into a constructible graph coding one. The only two producers
of an L-element set are `hasSeparationL`
(`src/L/Axioms/Full.lagda.md:144-146`) and `hasReplacementL`
(`src/L/Axioms/Full.lagda.md:277-280`), and both take a `Formula` in
their type. An element of `sq δ` carries no `Formula`
(`agents/tasks/LJ-1-594/runs/W3.agda:42-43`), so neither generator can
be called on it. This is `[LJ-1.533]`'s generator argument, re-read at
today's lines (`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:107-111`).
INFERRED, and stated as an inference: `[LJ-1.533]` measured the wall
for ambient INJECTIONS; the bridge here wants ambient PAIRINGS; the
generators are the same two, and the payload carries no more syntax
than an injection does. The reduction row (`route-b-assembles`) is the
measured part: it is the bridge or nothing, on this route.

## 6. IS THE CIRCLE CLOSED

`[LJ-1.605]` measured that the pairing IS the square law at the band,
and `[LJ-1.593]` measured that the square law is a corollary of B9,
whose formula needs the pairing. **This task CONFIRMS the circle, as a
term: `the-circle` proves that the untruncation composed with the held
supply is `SqParam α₀` itself, so the untruncation is not a way around
the square law but the square law under another type, and the one
route that could detach it (`route-b-assembles`) reduces to a bridge
the tree's generators cannot build.** The circle is closed for good as
a FUNDING question at this tree: four tasks entered it, the fifth
measured the root, and both exits are walled by measurements that
already stand.

## 7. WHAT THE NEXT BRIEF NEEDS

- **This is a ruling for the owner, not a funding question.** A NO-GO
  that closes a five-dispatch circle goes to the owner in the hour it
  lands, per the brief's own branch. The two candidate routes out are
  both measured shut: the square law is forbidden to fund
  (`agents/tasks/LJ-1-593/review-of-square-coded.md:82-84`), and the
  coder for ambient pairings is the `[LJ-1.533]` generator wall.
- **If the owner wants the bridge attempted anyway**, the honest name
  of the object is: a coder for ambient pairings, at the same two
  `Formula`-typed generators `[LJ-1.533]` counted. It is a new object,
  not a sixth arrival at this point, and its price starts at the
  generator argument, not at the square law.
- **The rehoming defect is cheap to fix and worth a row in a W4 pass**:
  rehomed probes whose top module name predates `[LJ-1.142]` cannot be
  imported through the library (`runs/p136-1.out`). No mathematical
  content is at risk; the flags or a copy restore them, as
  `runs/cold/` shows.

## 8. W2, ANSWERED

The mathematics is written once, at a generic carrier:
`route-b-assembles` takes the carrier, the code family, the order, the
bridge and the decoding as parameters (`agents/tasks/LJ-1-607/
Probe607.agda:240-254`), and `[LJ-1.136]`'s `Sel` is that row's
instance, named in the row's own comment. Both the AC tower and the
GCH tower would consume the same assembly unchanged. No deadline
conflict arose.

## 9. SCOPE AND COMPLIANCE

- Write scope only: `agents/tasks/LJ-1-607/Probe607.agda`,
  `runs/W3.agda`, `runs/run.sh`, `runs/DirectRefused.agda`,
  `runs/P136Check.agda`, `runs/cold/` (two VERBATIM copies of
  `[LJ-1.134]`/`[LJ-1.136]` probes plus the cold checker), the `.out`
  files, this report, and
  `agents/tasks/LJ-1-607/review-of-band-untruncation.md`.
- `runs/cold/` is working-class material under this task's code: the
  copies are reproducible from their tracked originals at any time,
  and the originals are the canonical homes.
- Interfaces my runs wrote under `_build/2.8.0/agda/` are covered by
  the manifest's `2.8.0/**` toolchain glob; no manifest change was
  needed.
- No postulate. No hole. No `src/` change. `make check` is the gate
  before a commit; I commit nothing, and `git status` shows no change
  outside the write scope.
- The probe's rows put no `step`, `branch` or `stage-card-upper` into
  a conversion problem.

## ARCHIVE USED

- **archive/dev/LJ-dispatch-index.md**: read. `:190`, the `LJ-1.114` row,
  begins: "`| LJ-1.114 | Thread the truncation from StageCardinal to
  Devlin55 | WALL, ROUTE-`" and ends: "`two truncation eliminations
  collide. Reverted; the cause is proved |`". `:212`, the `LJ-1.136`
  row, carries: "`GO, BOTH PROBES | pick-canonical elaborates, so
  LJ-1.114's wall falls. A5's risk is seconds, not lines: 2.594 s per
  line |`". Also read `:183` (`[LJ-1.107]` PARTIAL), `:187`
  (`[LJ-1.111]` truncated chain) and `:217` (`[LJ-1.141]` rehome),
  all cited in section 4 and the probe.
- **archive/dev/JOURNAL-archived.md**: not used. Keyword-checked
  (`pick-canonical`, `LJ-1.114`, `LJ-1.136`): no hit. The dispatch
  index and the live journal held every record this task needed.
- **archive/dev/JOURNAL.md**: read. `:879`: "`measured core, 78 lines,
  one `git clean` from gone.** I moved all three into`" and `:880`:
  "`agents/tasks/LJ-1-134/` and `agents/tasks/LJ-1-136/` and tracked
  them, which`". This is the record of the rescue that falsifies the
  brief's premise.
- **dev/ARCHIVE.md**: not used. Keyword-checked: no hit. It indexes
  retired modules under `archive/src/`, and no module ever held
  `pick-canonical`: the term was never in a master.
- **archive/dev/ORCHESTRATION.md**: declined, not read. It is
  superseded orchestration history; whether a term typechecks at
  today's tree is decided by the tree and the machine, not by it.

## LITERATURE USED

- **dev/literature/truncation-and-selection.md**: read. `:146`:
  "`**The constraint the route carries: `P` must be `hProp`-valued.**
  So `leastOf`"; `:148`: "`index is a proposition. **A data payload
  does not come out.**`"; `:155`: "`- `splitSup X :≡ ∥X∥ → X` (section
  3, equation (29)).`" `:157-159` carries Theorem 16, the
  constant-endomap criterion, cited in the probe's row 1.2.
- **dev/literature/devlin-II5.md**: not used. Keyword-checked
  (`truncat`): no hit. It is the Devlin 5.5 set-theory notes; this
  task's truncation is the type-theoretic one.
- **dev/literature/digest.md**: not used. Keyword-checked
  (`truncat`): no hit.
- **dev/literature/terms-2026-08.md**: not used. Keyword-checked
  (`truncat`): no hit.
- **dev/literature/geology.md**: not used. Keyword-checked
  (`truncat`): no hit.
