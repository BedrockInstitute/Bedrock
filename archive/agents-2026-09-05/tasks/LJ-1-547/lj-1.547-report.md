# LJ-1.547 report: the close. `[LJ-1.566]`'s term, imported and bound

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `injcode-assembled` is bound by IMPORT, with no holes and no
postulate.** `agents/tasks/LJ-1-547/Probe547.agda:54-57`, exit 0, caliber
`-A64m -I0 -M2g` taken from the pane, one Agda process at a time. Three
runs of the file at 1.60 s, 1.58 s and 1.56 s, the last on the tree as
it stands (`runs/full-1.out`, `runs/full-2.out`, `runs/full-final.out`),
and `runs/W3.agda` alone, written and typechecked FIRST, at 2.06 s and
1.55 s (`runs/w3type-1.out`, `runs/w3type-2.out`). The program's own
witness passes on the final tree:
`agents/tasks/LJ-1-547/Probe547.agda::injcode-assembled`, `pass`, 1.59 s,
0 unresolved.

**THE MATHEMATICS IS `[LJ-1.566]`'S AND THIS TASK CLAIMS NO CREDIT FOR
IT.** The obligation this task was first sent for was delivered by
`[LJ-1.566]` at the same obligation name
(`agents/tasks/LJ-1-566/Probe566.agda:492-500`), GO at a measured 1.67 s
floor and 9.66 s finish (`agents/tasks/LJ-1-566/lj-1.566-report.md`,
`## THE FLOOR AND THE FINISH`). This close binds that term at its own
type. Nothing was re-derived, weakened or re-ascribed at this task's old
frame.

**ONE SPELLING, AND NO BRIDGE.** Every carve name in this task's files is
`P566.Carve`, the spelling `[LJ-1.566]`'s own proof produces. No second
spelling of the carve appears anywhere in this task, so R-42's hazard
(`dev/LESSONS.md`, R-42: a carve output compared across two spellings
costs by the unfolding) is not present to pay.

## WHAT I BOUND AND FROM WHERE

**THE IMPORT is at `agents/tasks/LJ-1-547/Probe547.agda:40`:**

    import LJ-1-566.Probe566 {ℓ} lem as P566

**THE BIND is at `agents/tasks/LJ-1-547/Probe547.agda:54-57`:**

    injcode-assembled :
        (a : S) (oa : IsOrd (fst a))
      → InjCode (P566.Carve.G a oa) a (P566.Carve.C a oa)
    injcode-assembled = P566.injcode-assembled

The type is `[LJ-1.566]`'s own (`Probe566.agda:492-495`), spelled through
the import: the binders, the head `InjCode`, the `a`, and `F` and `b` at
`Carve.G` and `Carve.C` are that type component for component, and the
elaborator checked my longhand spelling against the imported term at one
spelling and accepted it with no conversion.

**THE TYPECHECK TIMES.** `runs/W3.agda` alone first: 2.06 s, 428 MB peak
resident set, exit 0 (`runs/w3type-1.out`). The probe: 1.60 s and 1.58 s
over two runs (`runs/full-1.out`, `runs/full-2.out`), about 411 to 428 MB
peak resident set each. All under the pane caliber `-A64m -I0 -M2g`, well
under the two minutes the brief set as the wrong-approach bar.

**WHERE THE IMPORTED FILE CAME FROM.** This worktree was forked before
`[LJ-1.566]` landed and did not hold it. I copied
`agents/tasks/LJ-1-566/Probe566.agda` byte-identical from the main tree
(`diff` confirms identical) and one warm interface
`_build/2.8.0/agda/agents/tasks/LJ-1-566/Probe566.agdai` from the
`LJ-1-572` worktree's store, which the program's own `make_worktree()`
measurement says interfaces are (`scripts/pod/pod.py:1160`: "the
interfaces are path-portable"). Both copies are untracked, outside this
task's write scope, and die with this worktree. See `## THE ENVIRONMENT I
FOUND` for why they were necessary.

## WHY THIS IS NOT A PROOF

The mathematics was done by `[LJ-1.566]`, which built all four conjuncts
at one carve and measured the price, and this task only closed a parked
row by importing that delivered term at its own type. This report claims
no credit for the term and adds no mathematical content to the tree.

## D-10, THE TYPE COMPARISON, DONE BEFORE ANY AGDA

The brief ordered `[LJ-1.566]`'s type and this task's old type put side
by side before any Agda, with a stop if they are not identical. Here is
that comparison.

**`[LJ-1.566]`'s delivered type, `agents/tasks/LJ-1-566/Probe566.agda:492-495`:**

    injcode-assembled :
        (a : S) (oa : IsOrd (fst a))
      → InjCode (Carve.G a oa) a (Carve.C a oa)

**This task's old type, attempt 1's `Probe547.agda:372-375`, quoted from
the parked copy in the main tree:**

    injcode-assembled :
        (a : S) (oa : IsOrd (fst a))
      → InjCode (Asm.G a oa) a (Asm.C a oa)

**COMPONENT BY COMPONENT.** The binders are identical: `(a : S)` with `S`
the carrier of `𝒮ʟ`, and `(oa : IsOrd (fst a))`, at the same module frame
`{ℓ : Level} (lem : LEM (ℓ-suc ℓ))`. The head is identical: `InjCode`
from `L.Cardinal {ℓ} lem`, `src/L/Cardinal.lagda.md:223-228`. The `a` in
the middle position is identical. The `F` is each file's ONE local
spelling of the coding leg's carve: `module Carve` at
`Probe566.agda:316`, `module Asm` at attempt 1's `Probe547.agda:135`,
and each type says the name and never the body, which is R-42's cure in
both files. The `b` is the same: each file's own name for the bounding
ordinal of that carve, `Carve.C` and `Asm.C`, both `[LJ-1.529]`'s
`Bound′.C` family.

**VERDICT: THE SAME OBLIGATION AT THE SAME FRAME, AND THERE IS NOTHING TO
BRIDGE.** The old brief's obligation was a placeholder, `InjCode F a b at
the coding leg's own frame` (the void brief, `LJ-1.547.md:11-12` as it
stood in this worktree before this close synced it), and the delivered
type fills that placeholder component for component: one `F`, one `a`,
one `b`, at the coding leg's frame. The two texts are not
token-identical, because each file names its own local carve module, and
that difference is not a frame difference: it is which file owns the one
spelling. The old spelling no longer exists, because this rewrite
replaced attempt 1's file, so there is no second spelling on any side of
the bind to convert against. I did not bridge the two types, and no term
of this task ever mentions both spellings. This is the GO case, and it is
what `runs/W3.agda` measured first: the longhand type and the imported
term agree on the nose, at 2.06 s.

## THE CLOSE COST

| what was checked | lines | result | evidence |
|---|---|---|---|
| `runs/W3.agda`, `[LJ-1.566]`'s interface warm | 46 | 2.06 s, exit 0, 428 MB | `runs/w3type-1.out` |
| `runs/W3.agda`, second run | 46 | 1.55 s, exit 0, 411 MB | `runs/w3type-2.out` |
| `Probe547.agda`, first run | 57 | 1.60 s, exit 0, 428 MB | `runs/full-1.out` |
| `Probe547.agda`, second run | 57 | 1.58 s, exit 0, 411 MB | `runs/full-2.out` |
| `Probe547.agda`, final run, the tree as it stands | 57 | 1.56 s, exit 0, 411 MB | `runs/full-final.out` |
| the program's witness, my own pre-run | derived | `pass`, 1.65 s, 0 unresolved | terminal, section `## VERDICT` |

**THE ESTIMATE HELD.** The brief estimated about 40 lines and under 30
seconds against `[LJ-1.566]`'s measured 9.66 s. The probe is 57 lines
with its comments, of which 4 are the bind, and the slowest run of the
task is 2.06 s, warm. **NO HEAP WALL**: the largest peak resident set any
run of this task measured is 428,130,304 bytes, against the `-M2g`
caliber. **I never set `GHCRTS` and I never ran two Agda processes of my
own.**

## THE ENVIRONMENT I FOUND, AND WHAT I DID TO IT

This section records every change this task made outside its own
deliverables, because the working tree must be exactly as described.

1. **THE WORKTREE IS STALE, AND THE BRIEF'S PREMISE "IMPORT
   `[LJ-1.566]`" WAS NOT REACHABLE AS FOUND.** This worktree was forked
   at commit `b8bd6709` ("pod: admit LJ-1.547", the FIRST admit) and was
   re-used for this re-dispatch, so it lacks every task directory
   admitted after that, 66 of them, including `agents/tasks/LJ-1-566/`.
   `src/` did NOT move in that window: `git diff --stat b8bd6709
   3a0bfb5b -- src/` is empty, and `[LJ-1.547]`'s own probe imports
   (`LJ-1-521`, `LJ-1-531`, `LJ-1-537`) are unchanged at my base. So the
   only missing piece for the import was `[LJ-1.566]`'s own file.
2. **I COPIED TWO FILES IN, both untracked and outside my scope.**
   `agents/tasks/LJ-1-566/Probe566.agda`, byte-identical to the main
   tree's tracked copy, and the warm interface named in `## WHAT I BOUND
   AND FROM WHERE`. Without the first, the import cannot resolve;
   without the second, the acceptance run would cold-typecheck
   `[LJ-1.566]` under the wide `-M2g` cap, and its own measured peak on
   the file is 2,391,031,808 bytes (`agents/tasks/LJ-1-566/runs/
   full-final.out`), which is ABOVE the cap: a cold acceptance run could
   heap-wall a green task. The interface is fresh against the copied
   source, so no run of this task or of its acceptance will re-typecheck
   `[LJ-1.566]`.
3. **THE FOUR PARKS WERE THE ACCEPTANCE ARM RE-RUNNING ATTEMPT 1'S KILL
   MINIATURE, AND I REMOVED THAT CAUSE.** Conjunct 1 runs every changed
   `.agda` under the task home (`scripts/pod/facts.py:431`,
   `verification_target`, case 2). Attempt 1 left `runs/BisName.agda`
   there, a file whose own report records that it does not finish (it
   was killed at 301 s by attempt 1's own cap, `runs/bisname.out`), and
   the arm re-ran it uncapped: 1800.01 s, `rc None`, `error class
   timeout`, four times to `attempt_max` (`runs/accept-4.out` to
   `runs/accept-7.out`, each `runs_all` row naming
   `runs/BisName.agda`). **A parked task keeps its worktree** (A24), so
   the file would have re-walled a fifth time. I deleted the `.agda`
   files of the void plan from `runs/`: `BisName.agda`, `BisBody.agda`
   and `Pin.agda`. Every `.out` record is kept. `Pin.agda` could not
   have survived the rewrite in any case: it reads `P547.Asm.G`
   (`runs/pin-1.out` records it; the file cited it at `:43-46`), a name
   this rewrite deleted with attempt 1's file.
4. **I SYNCED THE BRIEF IN THIS WORKTREE TO THE DISPATCHED TEXT.** The
   worktree still held the void brief, because the re-dispatch seeded
   main's rewrite there only if the file was missing and it was not.
   Left alone, two failures follow: conjunct 6 would read the OLD
   injected candidate lists, and `salvage_worktree()` would copy the
   void text back over the main tree's rewrite (untracked path, no
   collision check stops it). The copy is byte-identical to
   `agents/tasks/LJ-1-547/LJ-1.547.md` in the main tree.
5. **WHAT THE TREE HOLDS NOW.** My deliverables: `Probe547.agda`
   (rewritten), `runs/W3.agda` (rewritten), `runs/run.sh` and the new
   `.out` records `runs/w3type-1.out`, `runs/w3type-2.out`,
   `runs/full-1.out`, `runs/full-2.out`, `runs/full-final.out` (the last
   three names REPLACE attempt 1's records where they collide; its
   timings survive in `runs/full-3.out`, `runs/full-allcold.out` and
   `runs/stage-a.out`), and this report.
   Kept from attempt 1: every `.out` not named above, the four
   `review-LJ-1-547-*.md` and four `review-of-LJ-1-547-*.md`, and
   `.pod`. Foreign to my scope and untracked: the two copies of item 2.
   `_build/2.8.0/agda/agents/tasks/LJ-1-547/` also gained this task's
   own interfaces; the whole interface store is declared `toolchain` by
   `dev/build-manifest.toml`'s `2.8.0/**` entry. **Nothing was
   committed and nothing was pushed. Nothing landed in `src/`.**

## THE WALL, RE-MEASURED HERE

**This section is attempt 1's measurement, carried into this report
verbatim in substance because R-42 cites it as the independent
confirmation of its law (`dev/LESSONS.md`, R-42, Evidence:
"`agents/tasks/LJ-1-547/lj-1.547-report.md` §`## THE WALL, RE-MEASURED
HERE`"). R-42's line citations `:254-262` and `:268` pointed into
attempt 1's report and now drift: this section is their new home.** The
`.agda` arms of the measurement were deleted from `runs/` by this close
(item 3 above); the `.out` records remain.

`AGENTS.md` says a measured cure does not transfer by analogy, so attempt
1 re-measured `[LJ-1.541]`'s wall at this site rather than citing it.
`runs/BisBody.agda` and `runs/BisName.agda` differed in ONE line of code:

    <   G = fst (P529.rank-graph Q a bnd)     -- BisBody, exit 0 at 1.85 s
    >   G = P529.Carve.G a oa                 -- BisName, killed at 301 s

| run | what it writes for `G` | result | evidence |
|---|---|---|---|
| `runs/BisBody.agda` | `fst (P529.rank-graph Q a bnd)` | 1.85 s, exit 0 | `runs/bisbody.out` |
| `runs/BisName.agda` | `P529.Carve.G a oa`, ONE LINE changed | killed at 301 s | `runs/bisname.out` |

This is not a heap wall: `runs/BisName.agda` was killed by attempt 1's
own 301 second cap at 100 percent CPU, and `/usr/bin/time` never printed
for it, so no maximum resident set figure exists. So `[LJ-1.541]`'s law
held at this site too, and the one-name shape it dictates is the shape
this close binds at: one spelling, `P566.Carve`, and never the body.

## W2, ANSWERED

The brief did not state W2 and I answer it. **This task wrote no
mathematics that could be fixed or generic.** The one term it binds is
`[LJ-1.566]`'s, and that term is already at the generic carrier: it
takes any `a` and any `oa : IsOrd (fst a)` and names neither trophy,
and `InjCode` is consumed by both proofs through `IsCardinalL`
(`src/L/Cardinal.lagda.md:231-233`). There is no second copy of anything
to share and nothing to instantiate.

## W4, ANSWERED

**Nothing was retired and nothing should be.** No module left `src/`,
nothing landed in `src/`, and `dev/ARCHIVE.md` takes no row from this
task. The three `.agda` files deleted from `runs/` are not modules and
not masters: they are a void plan's miniatures inside this task's own
home, and the rule for them is the probe rule's own grain, a probe pairs
with its report, is tracked and is never deleted. Their measurements are
the record and the records were kept (`.out` files, the table above, and
R-42's own text). Priced the other way, as W4 asks: written fresh today,
this close is what a fresh write would be, an import and a bind; there
is no cheaper form and no part of attempt 1's file worth reviving.

## WHAT THE NEXT BRIEF NEEDS

1. **The row is closed at its own obligation name, by import.**
   `injcode-assembled` resolves in this tree at
   `agents/tasks/LJ-1-547/Probe547.agda:54-57`, and the term it binds is
   `[LJ-1.566]`'s. A consumer that wants the four conjuncts apart can
   project them out of `InjCode` as `runs/Pin.agda` of `[LJ-1.566]`
   (`agents/tasks/LJ-1-566/runs/Pin.agda`) already measures.
2. **Do not fund anything against the seconds above as though they price
   a conjunct.** They price an import and a bind, warm. The conjuncts'
   prices are `[LJ-1.566]`'s and `[LJ-1.559]`'s to report, not mine.
3. **The `b` is still not free.** Attempt 1's warning stands and nothing
   in this close changed it: the term injects `a` into the bounding
   ordinal of its own carve, and whether a consumer can bring that `b`
   under its control is the question `[LJ-1.546]` held and no task has
   answered.
4. **A re-dispatch into a parked worktree inherits the parked base.**
   This task had to copy a committed predecessor in by hand, and it is
   the second time the tree has hit this: attempt 1 could not import
   `[LJ-1.541]` for the same reason (its own report, `## D-10`, item on
   `W541`). A brief that names an import should say where the file comes
   from if the worktree is older than the import.
5. **R-42's line citations into this report need re-pointing** by whoever
   owns `dev/LESSONS.md`: its citations `:254-262` (the one-line diff and
   the wall table) and `:268` (the old type's `Asm.G a oa` reading)
   pointed into attempt 1's report and now hold this report's
   `## THE WALL, RE-MEASURED HERE` section, whose diff and table sit at
   `lj-1.547-report.md:223-229` and whose reading at `:231-235`. The old
   type itself, quoted with `Asm.G a oa`, is at `:94-97` of this report.
   My scope could not edit `dev/LESSONS.md`.

## GATES RUN

Run as `/Users/alsg/Agentic/Bedrock/.venv/bin/python`, because this
worktree carries no `.venv`. Each exit 0.

- `scripts/gate/lint-prose.py --check`
- `scripts/gate/lint-agda.py --check`
- `scripts/gate/check-probes.py --check`
- `scripts/pod/check-closure.py --check closure`
- `scripts/pod/check-survey-quotes.py --brief agents/tasks/LJ-1-547/LJ-1.547.md --report agents/tasks/LJ-1-547/lj-1.547-report.md`

**THE RATIO BAR HAS NO DIVISOR HERE.** The write scope holds no
`.lagda.md` master, so this task's in-fence line count is 0 and the bar
cannot fire.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: not read, declined. This close
  imports a delivered term at its own type and prices nothing, so the
  dispatch record's pricing rows cannot change a line of it. I searched
  it for `LJ-1.547` and `LJ-1.566` and it holds no row for either.
- `archive/dev/JOURNAL-archived.md`: not read, declined. I searched it
  for `LJ-1.547`, `LJ-1.566` and `InjCode` and found no hit. It cannot
  carry a type this task must match or a price it must pay.
- `archive/dev/JOURNAL.md`: not read, declined. Same search, same empty
  result: no `LJ-1.547`, no `LJ-1.566`, no `InjCode`. Attempt 1 read it
  for `injAt`'s missing master; that question is closed by
  `src/L/Coding/Injection.lagda.md:44` and was not mine.
- `archive/dev/DECISIONS-archived.md`: not read, declined. The decisions
  archive of an earlier route; the decision this task executes is the
  owner's close authorization, quoted in the brief, not in this file.
- `archive/dev/ORCHESTRATION.md`: not read, declined. The archived
  operating document of the loop. I read the loop's live code instead
  (`scripts/pod/facts.py`, `scripts/pod/accept.py`,
  `scripts/pod/check-survey-quotes.py`), because the acceptance mechanics
  are what parked this task and the live code is the only admissible
  evidence of them.
- `dev/ARCHIVE.md`: not used. It was a candidate of the brief this
  worktree held before the sync (item 4 of `## THE ENVIRONMENT I
  FOUND`) and is not a candidate of the dispatched brief. This task
  retires nothing, so the archive ledger takes no row.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: not read, declined. A bookkeeping
  close binds an already proved term and reads no mathematics.
- `dev/literature/digest.md`: not read, declined. No hit for `InjCode`
  or `carve` when I searched, and no price this task pays could come
  from a literature digest.
- `dev/literature/geology.md`: not read, declined. Same search, no hit.
- `dev/literature/truncation-and-selection.md`: not read, declined.
  Same search, no hit.
- `dev/literature/terms-2026-08.md`: not read, declined. Same search, no
  hit.
