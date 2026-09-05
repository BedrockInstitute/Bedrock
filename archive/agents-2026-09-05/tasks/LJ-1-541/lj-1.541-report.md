# LJ-1.541 report: `domAt`, the fourth conjunct, and a wall between files

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `domAt-at-carve` is built, with no holes and no postulate.**
`agents/tasks/LJ-1-541/Probe541.agda:349-350`, exit 0, caliber
`-A64m -I0 -M8g` taken from the pane, one Agda process at a time. Three cold
runs at 7.67 s, 6.65 s and 6.62 s (`runs/full-1.out` to `runs/full-3.out`; the
interface was removed before each), and a final green run after the last edit
at 7.00 s (`runs/full-final.out`, with `runs/pin-final.out` at 1.69 s).

    domAt-at-carve : (a : S) (oa : IsOrd (fst a)) → DomAtOf (Dom.G a oa) a

    DomAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩

**THE TYPE IS THE `InjCode` COMPONENT AND NOT ANOTHER READING OF THE WORDS.**
`domAt-is-second-of-InjCode` (`Probe541.agda:156-157`) projects that exact type
out of `InjCode` (`src/L/Cardinal.lagda.md:223-228`), and `runs/Pin.agda:55-67`
states the obligation again with no name of `DomAtOf` and inhabits it by
`P541.domAt-at-carve` and by nothing else. Exit 0, 1.57 s (`runs/pin-1.out`).

**THE BRIEF ASKED FOR A MEASUREMENT AND IT GOT ONE THAT CHANGES THE NEXT TASK.**
Every mathematical piece `[LJ-1.537]` named fits where its report says it does.
Nothing had to be weakened and no adapter was written into a term. But the
composition could NOT be made at `[LJ-1.529]`'s carve BY NAME, and the reason is
not mathematical. See `## THE WALL`.

## ALL FOUR CONJUNCTS

`InjCode F a b` is four components (`src/L/Cardinal.lagda.md:223-228`).

| # | conjunct | delivered | where | at which carve |
|---|---|---|---|---|
| 1 | `svAt zero` | YES, as the conjunct | `agents/tasks/LJ-1-524/Probe524.agda:263-266` | `P524.Carve.G a oa bnd`, `bnd` FREE |
| 2 | `domAt zero (suc zero)` | YES, as the conjunct, THIS TASK | `agents/tasks/LJ-1-541/Probe541.agda:349-350` | `P541.Dom.G a oa` |
| 3 | `injAt zero` | **NO. The LEMMA only** | `agents/tasks/LJ-1-531/Probe531.agda:185-203` | no carve: the statement names none |
| 4 | the range clause | YES, as the conjunct | `agents/tasks/LJ-1-529/Probe529.agda:282-285` | `P529.Carve.G a oa`, codomain `P529.Carve.C a oa` |

**`InjCode` IS NOT YET A COMPOSITION OF DELIVERED TERMS, AND TWO SEPARATE
THINGS STAND IN THE WAY.**

1. **`injAt` is a lemma and not a conjunct.** `[LJ-1.531]` delivered
   `rank-at′-inj` (`Probe531.agda:185-189`), which is "two members with the same
   rank are the same member". The conjunct `⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩` needs
   `injAt-in` (`src/L/Coding/Injection.lagda.md:72-75`) applied to the reading
   over the carve. That is NOT in the tree. I ESTIMATE it at about ten lines,
   from the shape of `injAt-in` and of this file's `read`, and the estimate is
   not a measurement. The brief's
   premise 11 says `[LJ-1.531]` "closed `injAt`'s lemma", and that is exactly
   right: the lemma, not the conjunct.
2. **The four are stated at four spellings of the carve, and the spellings
   cannot be converted.** See `## THE WALL`. This is the finding of the task.

**WHAT THE ASSEMBLY TASK MUST DO.** Build all four conjuncts in ONE module over
ONE `G` whose body is `fst (rank-graph Q a bnd)` at that module's own `Q` and
`bnd`. Do not try to assemble the four terms that are in the tree today. Three
of them are green, and the one pair I MEASURED could not be put over one `F`:
this task's carve against `[LJ-1.529]`'s name, `runs/BisF.agda`, killed at
334.56 s. I did not measure the other pairs and I do not assert them.

## D-10, BEFORE ANY AGDA

The brief orders every piece checked at its `file:line` first, and orders a STOP
if one does not fit. **All six fit, and section 1 of the probe says so by
machine rather than in prose.** Each of `piece-pr`, `piece-Q`, `piece-val`,
`piece-bound`, `piece-approx` and `piece-read`
(`Probe541.agda:98-143`) is a TYPE ASCRIPTION, transcribed from the
predecessor's report, over a right-hand side that is one name. A drift between
a report and the tree is then a type error in this file. With section 2 they
cost 1.77 s together (`runs/BisA.agda`, `runs/bisA.out`, exit 0).

**THE BRIEF ORDERED `[LJ-1.537]`'s OWN CHECK RE-RUN AND NOT TAKEN ON ITS WORD.**
`[LJ-1.537]` checked the environment in `agents/tasks/LJ-1-537/runs/Pin.agda:46-62`, which pins the
three conjuncts at a HAND-WRITTEN telescope. That is not the same check as
running the carve inside `rankFo`, so this task did the second one: W3 below
places `approx-carve` four existentials deep, under `rankFo`'s own binders.

**`[LJ-1.537]`'s READING OF THE TYPES IS CORRECT IN EVERY PARTICULAR.** The
four pieces of the satisfaction half and the one piece of the bound half are
where its report says they are, and they compose with no adapter:

- `var zero ≐ con Q` at `q := Q` is `refl` (`Probe541.agda:196-197`). The model's
  `≈ˢ` is `λ u v → fst u ≈ˢ fst v` (`src/FOL/ZFStructure.lagda.md:148`) over
  `𝒮ᵥ`'s path equality (`src/V/Hierarchy.lagda.md:82`).
- `prAtL (s3 zero) (suc zero) zero` is `prʟ-fst` through `prAtL-adequate`
  (`Probe541.agda:201-204`).
- `var (suc zero) ∈̇ con a` is the hypothesis, passed unchanged.
- `fnAt ∧̇ assignAt ∧̇ supAt` is `approx-carve a oa x xa` passed WHOLE
  (`Probe541.agda:208-212`), not split into three, so this file cannot re-spell
  its environment even by accident.
- `pr x r ∈ fst bnd` is `[LJ-1.529]`'s `below` carried over `rank-at′-val`
  (`Probe541.agda:285-288`).

## W3, THE ENVIRONMENT MATCH

**GO. 1.32 s, 1.33 s, 1.32 s cold, exit 0 each** (`runs/W3.agda`,
`runs/w3-1.out` to `runs/w3-3.out`). Green at the FIRST attempt it was ever
typechecked (`runs/w3-try1.out`, 1.43 s, before the box was quiet).

The brief named the widest unmeasured term as the environment match and ordered
it written first, alone, with the obligation omitted. `runs/W3.agda` is that:
118 lines, of which 48 are code, and it builds

    carve-at-pair :
        (a : S) (oa : IsOrd (fst a)) (x : S) (xa : ⟨ fst x ∈ fst a ⟩)
      → ⟨ (prʟ x (P521.rank-at′ a oa x xa) ∷ [])
          ⊨ P521.rankFo (P521.ord-set-witness a oa .fst) a ⟩

**THE ENVIRONMENTS DO NOT DIFFER AND THERE IS NO ADAPTER TO PRICE.** `rankFo`'s
four existentials put the innermost point at `(f ∷ r ∷ m ∷ q ∷ z ∷ [])`, which
is `[LJ-1.521]`'s `Env.γ5` (`Probe521.agda:512-516`); `[LJ-1.537]`'s
`Approximates` (`Probe537.agda:587-592`) is stated at that same `Env`, at
`Zof = prʟ m (rank-at′ a oa m mx)` and `Qwit = ord-set-witness a oa .fst`; and
the pair the converse must exhibit is that same `Zof`. So the fourth
existential takes `approx-carve` as ONE term and nothing is transported.

**ESTIMATE WAS ABOUT 25 LINES AND UNDER 45 SECONDS. MEASURED 48 CODE LINES
AND 1.32 SECONDS.** The lines came in over because W3 here is the whole
satisfaction half and not a slice of it; the seconds came in far under. **I did
not fund W3 against `[LJ-1.537]`'s numbers**, as the brief ordered: every number
above is this file, cold, on this pane.

## THE WALL

**THIS IS THE FINDING, AND IT IS WORTH MORE THAN THE TERM.**

`[LJ-1.524]` measured that two spellings of the carve do not finish, and stated
the cure as ONE NAME FOR THE CARVE (`lj-1.524-report.md`, section 3: two runs
killed at ten and at eight minutes). **That cure does not carry across files,
and this task measured where it stops.**

**`runs/BisC.agda` AND `runs/BisE.agda` DIFFER IN ONE LINE OF CODE.** Both build
the same separation equation over the same set. Ignoring comments and the module
name, `diff` reports exactly one line:

    <   G = P529.Carve.G a oa                  -- BisC, killed at 155.02 s
    >   G = fst (P529.rank-graph Q a bnd)      -- BisE, exit 0 at 1.74 s

| run | what it writes for `G` | result | evidence |
|---|---|---|---|
| `runs/BisA.agda` | nothing: sections 1 and 2 alone, the six D-10 pieces | 1.77 s, exit 0 | `runs/bisA.out` |
| `runs/BisE.agda` | `fst (P529.rank-graph Q a bnd)` | **1.74 s, exit 0** | `runs/bisE.out` |
| `runs/BisC.agda` | `P529.Carve.G a oa`, ONE LINE changed from `BisE` | killed at 155.02 s | `runs/bisC.out` |
| `runs/BisD.agda` | the same, with `Q` and `bnd` taken from `P529.Carve` itself | killed at 337.30 s | `runs/bisD.out` |
| `runs/BisF.agda` | `refl : G ≡ P529.Carve.G a oa`, compared at `S` and NOT under `_∈_` | killed at 334.56 s | `runs/bisF.out` |
| `runs/BisG.agda` | `refl` between `P529.Carve.G`'s own body and its name | killed at about 180 s | `runs/bisG.out` |
| `runs/PinBody.agda` | the Pin with `P541.Dom.G`'s BODY written out | killed at 321.49 s | `runs/pin-body.out` |
| `Probe541.agda` as first written | the whole file over `P529.Carve.G a oa` | killed at 718.26 s | `runs/stage-a.out` |

**NONE OF THESE IS A HEAP WALL.** Every one was killed by my own cap, at
100 percent CPU and a flat resident set. The largest maximum resident set of
the seven that `/usr/bin/time` measured is 1026621440 bytes
(`runs/stage-a.out`), against the `-M8g` caliber, so no run came near the cap.
`runs/BisG.agda` was killed with its shell, so `/usr/bin/time` never printed
for it and no figure exists. The `heap_wall` branch of this brief does not
apply and I did not report one.

**THE LAW, RESTATED FROM THE MEASUREMENT.** `[LJ-1.524]`'s "one name" is not
the invariant. The invariant is ONE DELTA, WITH THE ARGUMENTS ALREADY
SYNTACTICALLY EQUAL:

> A term of type `S` that a `hasSeparationL` carve produced may be compared with
> another spelling of itself only if the two differ by unfolding ONE definition
> whose arguments are then syntactically identical. `[LJ-1.529]`'s `Carve.sat`
> (`Probe529.agda:233-238`) pays exactly that and costs 3.55 s for its whole
> file (`runs/baseline-529.out`). Anything more does not finish.

`runs/BisD.agda` is what makes the law sharp rather than a guess: there the
arguments `Q` and `bnd` are taken from `P529.Carve` itself, so ONLY the module
projection separates the two bodies, and it still does not finish.
`runs/BisF.agda` adds that the compare is not cheaper at `S` than under `_∈_`.
`runs/PinBody.agda` adds that the wall is not about foreign files: it bites
inside THIS task's own names as soon as `G`'s arguments must be unfolded too.

**One more run, `runs/BisB.agda`, is the same measurement with `Sat` also
present, killed at 82.78 s (`runs/bisB.out`). It is kept because it is the run
that first localised the wall to section 4.**

**WHY IT MATTERS MORE THAN THIS TASK.** Three conjuncts now exist over three
spellings of one set, and the fourth, `injAt`, has no carve in its statement at
all. The assembly task cannot join them by naming a
predecessor's carve. It must restate all four in one module. That is a real
cost and this report is where it is priced, rather than being discovered inside
the assembly task's own budget.

## WHAT THE OBLIGATION COST

**EVERY NUMBER BELOW IS COLD: the file's interface was deleted before each run**,
because a warm run only reads `_build/2.8.0/agda/.../*.agdai` and measures
nothing.

| what was checked | lines | cold | runs |
|---|---|---|---|
| `runs/W3.agda`, everything else warm | 118 | 1.32 s | `w3-1.out` to `w3-3.out` |
| `runs/BisA.agda`, sections 1 and 2 alone | 114 | 1.77 s | `bisA.out` |
| `runs/BisE.agda`, the carve alone | 62 | 1.74 s | `bisE.out` |
| `Probe541.agda`, `Probe529` warm | 350 | 6.65 s | `full-1.out` to `full-3.out` |
| `runs/Pin.agda`, everything warm | 67 | 1.57 s | `pin-1.out` |
| `Probe529.agda` ALONE, the baseline | 285 | 3.55 s | `baseline-529.out` |
| `Probe541.agda` with `Probe529` ALSO cold | 350 + 285 | 8.81 s | `full-with-529.out` |

**THE ESTIMATE WAS ABOUT 220 LINES, OF WHICH ABOUT 55 THE OBLIGATION.
MEASURED 350 LINES: 172 comment, 48 blank, 130 code.** The
overrun is not the mathematics. It is the wall: `runs/BisE.agda`'s shape had to
be found by seven bisecting runs, the file carries their record in section 4,
and
section 4.2 rebuilds twelve lines of `[LJ-1.529]`'s reading that the brief
expected to be reused by import.

**A NOTE ON THE SECONDS.** The head says `machine: shared` and it was. A second
Agda process, from the `[LJ-1.536]` worktree, ran on this box during
`runs/bisD.out` and `runs/bisG.out`. Those two are kill times and not prices, so
nothing in the table above is affected; the box was clean for every run in the
table, checked immediately before with `ps`.

### what resisted

1. **The wall, and only the wall.** Seven bisecting runs plus the first whole
   file went to locating it. Seven of them were killed and cost about 2129
   seconds of wall clock in total (718.26, 82.78, 155.02, 337.30, 334.56, about
   180 and 321.49); the two green controls cost 1.77 and 1.74. **Every one of
   them was a spelling question and none was a mathematical one.**
2. **Nothing else.** W3 was green at the first attempt. The whole file was green
   at the first attempt once the carve was written at `[LJ-1.529]`'s shape
   (`runs/stage-b.out`, exit 0, 6.84 s). The two directions of `domAt` cost nine
   lines and three lines (`Probe541.agda:322-330` and `:334-336`).

### what did not resist, and I flag it because the brief expected it to

**The brief expected "the de Bruijn transcription of `rankFo`'s four
existentials to be its real cost"**, quoting `[LJ-1.537]`. It was not. The
transcription is `Probe541.agda:208-212`, five lines, and it was green the first
time it was typechecked. `[LJ-1.521]`'s `Env` and `[LJ-1.537]`'s `Approximates`
had already put every slot where `rankFo` wants it, so there was nothing to
transcribe: there was one term to pass.

## THE BRIEF'S ONE CONTRADICTION

**The brief says: "DO NOT REBUILD `approx-carve`, `rank-bound′` OR `rankFo`.
All three are delivered in predecessors' probes. Rebuild at their delivered
types; do not import a probe."** The last two clauses cannot both be obeyed.
`approx-carve` is 633 lines over `rankFo`'s 1176, the brief's own estimate for
this file is about 220 lines, and a rebuilt `rankFo` would state the obligation
at a DIFFERENT formula, which is the drift `[LJ-1.537]` built its Pin to rule
out. **I read the first clause as binding and imported**, which is what
`[LJ-1.524]` (`Probe524.agda:20-32`), `[LJ-1.529]` (`Probe529.agda:16-30`) and
`[LJ-1.537]` all did, and `bedrock.agda-lib:2` lists `agents/tasks` as an
include root. I record it here rather than resolving it in silence.

## W2, ANSWERED

The brief did not state W2 and I answer it.

**NOTHING IN THIS FILE IS AT A FIXED FORM THAT COULD BE GENERIC.** `Sat`
(`Probe541.agda:178-212`) takes any `a`, `oa`, `x` and `xa`. `Dom`
(`:248-341`) takes `a` and `oa`. Neither names `L ⊨ AC` or `L ⊨ GCH`, and the
obligation is the `InjCode` conjunct that `InjL` (`src/L/GCH.lagda.md:37-38`)
consumes for both.

**THE ONE THING THAT IS NOT GENERIC IS `Q`, AND THE RULING SAYS IT MUST NOT
BE.** `Q` is instantiated at `ord-set-witness a oa .fst` and not hypothesised,
by the standing ruling the brief restates. `[LJ-1.537]` left `approx-carve-at`
(`Probe537.agda:600-614`) for any `Q` that `ord-reads-Q` reads, and this file
does not need it: the coding site's `Q` is that witness.

## W4, ANSWERED

**NOTHING WAS RETIRED AND NOTHING SHOULD BE.** No module left `src/`, so
`dev/ARCHIVE.md` takes no row from this task.

**PRICED THE OTHER WAY, AS W4 ASKS.** Written fresh today, this file would be
written as it is, with one change: section 4.2 would not exist, because
`[LJ-1.529]` would have exported its reading at a `G` PARAMETER rather than at
`Carve.G`. That is the restatement this task's measurement suggests, it belongs
to `[LJ-1.529]`'s file and not to mine, and I did not make it, because a probe
does not edit a predecessor's probe.

## WHAT THE NEXT BRIEF NEEDS

1. **`injAt` is not delivered as a conjunct.** It is `injAt-in`
   (`src/L/Coding/Injection.lagda.md:72-75`) over `[LJ-1.531]`'s
   `rank-at′-inj` and this file's `read`. I ESTIMATE about ten lines and I did
   not build it, so the figure is not a measurement. **It is the only
   mathematical gap left in `InjCode`.**
2. **The assembly must be ONE module.** See `## THE WALL`. Budget the four
   conjuncts as a rewrite over one `G`, not as four imports.
3. **The reading is the shared part.** `svAt`, `injAt` and `domAt`'s first
   direction all consume the same `read` (`Probe541.agda:306-313`). In one
   module it is written once.
4. **`domAt`'s domain slot is `a` itself**, not a separate `D`
   (`Probe541.agda:153-154`). `InjCode F a b` puts `a` in slot 1 and `b` is read
   only by the range clause.

## THE IMPORT OF A PREDECESSOR PROBE

**THREE, AND EACH IS FORCED.** `[LJ-1.521]` for `rankFo`, `rank-at′`,
`rank-at′-val` and the `Q` witness; `[LJ-1.529]` for `rank-graph`, `Bound′` and
`adequate-at-witness`; `[LJ-1.537]` for `approx-carve`. A rebuild of any of the
three would state the obligation at a different term, and the brief's own
estimate rules out rebuilding 1809 lines. `bedrock.agda-lib:2` lists
`agents/tasks` as an include root and the tree already carries cross-task probe
imports (`agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29`,
`agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24`).

## GATES RUN

Run as `/Users/alsg/Agentic/Bedrock/.venv/bin/python`, because this worktree
carries no `.venv`. Each exit 0.

- `scripts/gate/lint-prose.py --check`
- `scripts/gate/lint-agda.py --check`
- `scripts/gate/check-probes.py --check`: clean, 5916 tracked files, no probe
  outside `agents/tasks/` and no generated file
- `scripts/pod/check-closure.py --check closure`: clean, 102 masters

**THE RATIO BAR HAS NO DIVISOR HERE.** The write scope holds no `.lagda.md`
master, so the in-fence line count of this task is 0 and the 0.0123 seconds per
in-fence line cannot fire.

**I DID NOT COMMIT AND DID NOT PUSH.** Nothing landed in `src/`. The working
tree holds only `agents/tasks/LJ-1-541/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ. `:292` says
  "| LJ-1.220 | Parameterize every leak and census the chain once | EXIT 0. WIDTH 8 MODULES, 19 NAMES | LJ-1.224 corrected 9 and 22 down. extAt-in and the domAt trio now MEASURED. The 17 was inferred |".
  I read it because it is the only archived row that names `domAt`. It is a
  WIDTH census of the leak chain and it names "the domAt trio", which is
  `domAt-out`, `domAt-in` and `domAt-intro` of `src/L/Coding/Model.lagda.md`.
  It carries no carve and no rank, so nothing in it changes this task's types;
  it did confirm that the trio is the intended interface and that this task
  should enter through `domAt-intro` and not rebuild the formula.
- `dev/ARCHIVE.md`: READ. `:89` says
  "| `archive/src/2026-08-13-probe-sweep/` | **Empty since 2026-08-13.** A tombstone that maps 257 pre-ruling probe paths to their homes in `agents/tasks/<TASK>/` | `archive/src/2026-08-13-probe-sweep/README.md` |".
  I read it to confirm where a probe of this task belongs before I wrote one.
  All eleven `.agda` files of this task are under `agents/tasks/LJ-1-541/`.
- `archive/dev/PLAN-archived.md`: NOT READ, declined. I searched it for
  `domAt`, `InjCode` and `conjunct`; its "carve" hits are the `LJ-9` phase
  carve-out and not a set-theoretic carve, and its `conjunct` hits are the
  acceptance conjuncts of the program. Neither bears on a type in this file.
- `archive/dev/JOURNAL.md`: NOT READ, declined. Same search, no hit on `domAt`
  or `InjCode`. A journal of closed work cannot carry a type this task must
  match.
- `archive/dev/JOURNAL-archived.md`: NOT READ, declined. Same search. Its two
  "carve" hits are about `Basic`'s carve chapters evaporating in a port, which
  is a different sense of the word and a different chapter.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: READ. `:143` says
  "the reason: "a proposition-valued goal absorbs the truncation"".
  I read it because `domAt` is truncated on BOTH sides: `domAt-intro`
  (`src/L/Coding/Model.lagda.md:298-305`) asks for a map INTO
  `⟨ ∃[ y ∶ S ] ... ⟩` and a map OUT of it. The line above is the exact
  condition my `fwd` (`Probe541.agda:322-330`) meets: the goal
  `⟨ fst x ∈ fst a ⟩` is an hProp, so `PT.rec` applies and no choice is made.
  **No selection principle is used anywhere in this task**, and this file is
  where I checked that none is needed.
- `dev/literature/level-formula-slot-roles.md`: READ. `:38` says
  "slots its conclusion uses.** No source leaves anything else free."
  I read it because this task is entirely slot arithmetic: `rankFo`'s four
  existentials against `Env.γ5`'s five slots, and `domAt zero (suc zero)`
  against `InjCode`'s two. The dossier is about the LEVEL-HOOD formula and not
  about `rankFo`, so it settles nothing here directly. It did confirm that no
  outside source numbers the slots for a rank formula, so `[LJ-1.521]`'s
  numbering is the only authority and I matched it rather than re-deriving it.
- `dev/literature/devlin-II5.md`: NOT READ, declined. `[LJ-1.537]` read it to
  separate this rank from the fine-structural rank
  (`lj-1.537-report.md`, LITERATURE USED). That separation is already made and
  this task adds no rank: it places the one `[LJ-1.521]` sealed.
- `dev/literature/geology.md`: NOT READ, declined. Set-theoretic geology bears
  on no part of a domain clause.
- `dev/literature/terms-2026-08.md`: NOT READ, declined. It is a naming
  dossier, and this task added no `dev/glossary.toml` entry and coined no term.
