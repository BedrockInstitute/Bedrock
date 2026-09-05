# LJ-1.659 report: does [LJ-1.651]'s formula give the level formula

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.659
obligation: agents/tasks/LJ-1-659/Probe659.agda::lset-formula-to-level
verdict: **STOP ON THE OBLIGATION AS WRITTEN, AND THE STOP IS
`review-of-lset-formula-to-level.md`. THE CORRECTED ARROW IS BUILT AND
GREEN, AND IT COSTS ONE RENAMING.**

The obligation reads `missing` (`runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`: the probe is green and the name is
absent, not broken). Twenty-seven other names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 27`).

**READ THESE FOUR SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE ANSWER IS NO, AND THE REASON IS NOT THE ONE THE BRIEF EXPECTED.**
   The brief's premise 3 guessed the arrow runs the other way. It does not
   run either way, because the hypothesis is EMPTY: `[LJ-1.651]` delivered
   `lset-formula : Formula Code 2`, a type of pure syntax, and the tree
   inhabits that type with `⊤̇`. So the brief's arrow is interderivable with
   its own target (`obligation-is-the-target`, `Probe659.agda:141-143`).
2. **`[LJ-1.651]` IS NOT BESIDE THE PATH, AND IT MUST NOT BE RETIRED.** The
   brief's NO-GO branch says NO-GO "retires `[LJ-1.651]` from the critical
   path". **That would be the wrong action.** `[LJ-1.651]` delivered the
   FIRST of three components. Add the other two and the arrow the brief
   wanted runs, for 25 lines.
3. **THE MISSING TWO ARE NAMED, TYPED AND GREEN AS A TYPE**: `Sound` and
   `Complete` (`Probe659.agda:155-161`), the soundness and the completeness
   of `lset-formula` for `_⊨c_`. `level-from-laws`
   (`Probe659.agda:199-214`) takes those and delivers `LevelFormula`.
4. **W3 IS A GO AND IT FOUND A SECOND THING.** The index binder is free on
   the two laws (section 4). But it PROVABLY destroys the grade
   certificate, and `[LJ-1.651]`'s own arity-1 reading `inF` is the casualty
   (section 4.3). That is a machine-checked negative, not a failure to
   search.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-659/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a time. I
did not set `GHCRTS`. Nothing is postulated, every delivered file carries
`--safe`, the delivered probe carries no hole, and nothing lands in `src/`.
The probe is a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.** No
number here is a cold-cache number, and this report does not bound one.

## 1. THE FLOOR, AND A CORRECTION TO A GENERALISATION

**THE FRAME IS CHEAP AND THE PREDECESSOR'S TYPE WAS TAKEN BY IMPORT.**
`[LJ-1.650]` measured that importing `LJ-1-595.Probe595` EXHAUSTS the wide
caliber's heap on the frame alone, and closed with the advice that "Any task
that plans to import a probe two or more links down the LJ chain should price
the frame first" (`agents/tasks/LJ-1-650/lj-1.650-report.md`, section 1).

**I priced it, and here the import is affordable**, because `Probe651`
imports NO probe: only `src/`. `runs/Floor659.agda`, `runs/floor-1.out`,
exit 0 in 5.82 s at 857,849,856 bytes, which is 40 % of the 2,147,483,648-byte
wide cap. Re-elaborated cold at the end of the task with its interface
removed: `runs/floor-final.out`, exit 0 in 4.98 s at 537,296,896 bytes.

**SO THE 2026-08-23 WALL IS ABOUT PROBE CHAINS AND NOT ABOUT PROBE IMPORTS.**
One link over `src/` is 5.82 s. Six links is a heap wall. The rule that
follows is the one `[LJ-1.650]` already wrote, and this run is its second
data point rather than a new law.

**THE TWO MODULES MEET.** `[LJ-1.651]`'s `Code` and this file's `Code` are
the same object: both are `AtStage lam ordλ .Hull X X⊆L ∅∈λ .T .Code`
(`src/L/BoundedSubset.lagda.md:907-909` against
`agents/tasks/LJ-1-651/Probe651.agda:53-57`). No transport is spent anywhere
in this probe to reconcile them.

## 2. THE OBLIGATION, AND WHY IT IS A STOP

`review-of-lset-formula-to-level.md` is the stop and carries the proof in
full. In four lines here:

- `[LJ-1.651]` delivered the type `Formula Code 2`
  (`agents/tasks/LJ-1-651/Probe651.agda:141`). That is SYNTAX. It carries no
  law about `_⊨c_`.
- The tree inhabits it with `⊤̇` (`trivial`, `Probe659.agda:121-122`).
- So the brief's arrow gives its target (`level-from-obligation`, `:127-128`)
  and the target gives the arrow back (`obligation-from-level`, `:134-135`).
- And it gives the target even at `⊤̇` (`level-from-nothing`, `:130-131`),
  which is the sharpest form: the predecessor is not what would pay.

**I DID NOT PROVE THE OBLIGATION'S TYPE FALSE.** I proved that the
hypothesis names no fact, so the arrow is the target under another name.
Agda states the underlying gap in its own words at
`runs/NO-LAWS.agda.txt` / `runs/nolaws-1.out` (exit 42, 3.18 s):

```
fst ((v ∷ γ ∷ []) T.AtCode.⊨ lf) !=< fst v ≡ Lset (fst γ)
```

**AND THE TREE HAS NO TERM THAT CLOSES THAT GAP.** `levelHoodB`
(`src/L/BoundedSubset.lagda.md:108-111`) carries a `Δ₀` certificate
(`:113-139`) and a `Σ₁` certificate (`:145-146`) and NO adequacy theorem.
`graphBndAt` (`src/L/Condensation.lagda.md:2492-2497`) is the same: `Δ₀` and
nothing else. `grep -rn "levelHood\|graphBndAt" src/` finds no consumer
outside those two files.

## 3. WHAT IS DELIVERED, AND WHAT EACH THING COSTS

Every name below is metered green in `runs/meter-names.out`.

| name | line | what it is | hypothesis |
|---|---|---|---|
| `delivered` | 95 | `[LJ-1.651]`'s term, by import | none |
| `trivial` | 121 | `⊤̇` inhabits the same type | none |
| `level-from-obligation` | 127 | the arrow gives the target | the arrow |
| `level-from-nothing` | 130 | it gives it at `⊤̇` too | the arrow |
| `obligation-from-level` | 134 | the target gives the arrow | the target |
| `obligation-is-the-target` | 141 | the two together | both |
| `Sound` / `Complete` | 155 / 158 | THE TWO MISSING LAWS, as types | none |
| `LsetFormulaWithLaws` | 164 | the corrected hypothesis | none |
| `delivered-is-the-first-component` | 169 | the correction adds and discards nothing | the two laws |
| `swap-agrees` | 189 | `Agrees` for the transposition | none |
| `transpose` | 193 | `⊨-rename` at the transposition | none |
| `level-from-laws` | 199 | **THE CORRECTED ARROW** | the two laws |
| `bindIx` / `bindIx-is-inF` | 231 / 234 | the index binder, and that it IS `inF` | none |
| `ix-sound` | 238 | soundness survives the binder | `Sound` |
| `ix-complete` | 248 | completeness survives it | `Complete` |
| `no-Δ₀-∃` | 281 | `Δ₀` has no `∃̇` clause | none |
| `no-Σ₁-∃∧` | 284 | `Σ₁` has no `∧̇` closure | none |
| `no-Σ₁-bindIx` | 292 | so the binder's shape is in neither class | none |
| `no-Σ₁-inF` | 303 | **and `[LJ-1.651]`'s `inF` is that shape** | none |
| `no-Σ₁-mapped-inF` | 313 | still that shape after `mapFo val` | none |
| `laws-to-coded-cover` | 339 | the whole payoff, composed | the two laws + `[LJ-1.650]` |

The probe is 341 lines, 144 non-blank non-comment.
`runs/p-final.out`: exit 0 in 4.39 s at 787,546,112 bytes, re-elaborated with
its interface removed.

**W2.** Nothing is proved twice. `LevelFormula` and `CodedCover` are
RESTATED from `[LJ-1.650]`'s probe rather than imported, and the reason is
not convenience: `[LJ-1.650]`'s own frame is a second frame this task did not
price, and its theorem enters as a hypothesis instead
(`laws-to-coded-cover`, `Probe659.agda:339-341`). Each restatement cites the
line it was read at.

## 4. W3, THE INDEX BINDER: GO, AND THE ESTIMATE WAS HIGH

The brief named "the index binder of premise 2" and priced it at 60 to 130
lines. **Section 5 of the probe is 39 non-blank non-comment lines**
(`Probe659.agda:217-322`), and it answers in three parts.

### 4.1 THE BINDER CANNOT BE A SUBSTITUTION, BECAUSE THERE IS NONE

`[LJ-1.595]` recorded the index substitution as "a renaming it did not
price" (the brief's premise 4). **It is not a renaming and it cannot be
one.** Renaming "moves only variables, leaving constants alone"
(`src/FOL/Manipulation/Renaming.lagda.md:43-44`), and the tree has no
substitution at all: "The syntax chapter pointed out an absence: no
substitution, no weakening" (`:7`). That absence is a DESIGN DECISION and the
archive records it (section ARCHIVE USED).

**So the only route is the equality trick, and `[LJ-1.651]` already wrote
it.** `bindIx lf c = ∃̇ (lf ∧̇ (var zero ≐ con c))` is `[LJ-1.651]`'s `inF`
(`bindIx-is-inF`, `Probe659.agda:234-235`, by `refl`).

### 4.2 ON THE TWO LAWS THE BINDER IS FREE

`ix-sound` (`:238-246`) and `ix-complete` (`:248-259`) are two-line terms
each. Given `Sound lf` and `Complete lf`, the index-bound reading at any code
`c` is sound and complete for "the free slot is `Lset (val c)`" with nothing
added. **The binder difference `[LJ-1.650]` measured is real on the SYNTAX
and it is FREE on the SEMANTICS, provided the semantics exists.**

### 4.3 BUT IT PROVABLY DESTROYS THE GRADE, AND `inF` IS THE CASUALTY

`Δ₀` is generated by ten clauses and none is `∃̇`
(`src/FOL/LevyHierarchy.lagda.md:47-57`). `Σ₁` is generated by `σ-Δ₀` and
`σ-∃` and by nothing else (`:73-75`). **There is no `σ-∧`.** So a conjunction
whose left half is an unbounded existential lies in NEITHER class, and the
index binder puts exactly that conjunction under one `∃̇`.

Four machine-checked negatives, each an absurd pattern on a constructor that
does not exist: `no-Δ₀-∃`, `no-Σ₁-∃∧`, `no-Σ₁-bindIx`, and the two concrete
ones, `no-Σ₁-inF` and `no-Σ₁-mapped-inF` (`Probe659.agda:281-321`).

**THIS CONTRADICTS NOTHING `[LJ-1.651]` SAID, AND IT COMPLETES IT.** That
report certified `lset-formula` as Σ₁ with two unbounded `∃̇` and concluded
"the grade wall does not recur in the Σ₀ shape". True, at the two-slot
matrix. **It did not check the arity-1 reading it delivered beside it**, and
that reading carries no certificate at all.

**THE CONSEQUENCE, STATED EXACTLY AND NOT WIDER.** `σ₁-up`
(`src/FOL/Absoluteness.lagda.md:182-183`) has premise `Σ₁ φ`, and that
premise cannot be met for `inF` at any parameter and at either alphabet. It
says NOTHING about `hull-closed`, which takes a bare `Formula Code 1` and
asks for no grade (`src/L/Hull.lagda.md:415-417`). **So the finding is: any
consumer that needs `inF` to be ABSOLUTE is blocked; any consumer that needs
`inF` only to be a formula is not.** Which consumers are which is a
mathematical judgement and it is not mine.

The gap is machinery and not mathematics: Σ₁ IS closed under conjunction in
the textbook, by prenexing. The tree has no prenexing.

## 5. WHAT THE NEXT BRIEF NEEDS

**5.1 THE OBLIGATION TO RESTATE.** Not `lset-formula → LevelFormula`. It is

```
Sound delivered × Complete delivered
```

`Probe659.agda:155-161` gives both types verbatim, at `[LJ-1.651]`'s own slot
order, so a brief can copy them. Everything downstream of that pair is
already built: `level-from-laws` reaches `LevelFormula` and
`laws-to-coded-cover` reaches `[LJ-1.595]`'s `CodedCover` through
`[LJ-1.650]`'s delivered theorem.

**5.2 IT HAS A HISTORY, AND THE HISTORY IS NOT ENCOURAGING.** The level-hood
adequacy at the hull was already a dispatched campaign and it did not close.
`archive/dev/LJ-dispatch-index.md:101` records `[LJ-1.52]`, "The level-hood
adequacy at the hull", as "PINNED, not discharged". **Price it against that
record before pricing it against this task's 39 lines.** Nothing in this task
measures the adequacy: it measures what the adequacy would BUY, which is
everything downstream, cheaply.

**5.3 THE SLOT ORDER IS SETTLED AND SHOULD BE WRITTEN DOWN ONCE.**
`[LJ-1.651]` reads ordinal 0, value 1. `[LJ-1.650]` reads value 0,
ordinal 1. **Both are right and the transposition is `renameFo swap` with
`⊨-rename`, delivered at `Probe659.agda:185-197`.** A future brief should
name which order it wants and cite `transpose`, rather than leaving the next
coder to rediscover that the two probes disagree.

**5.4 C-42, AND THIS TASK DID NOT RUN THE SWEEP.** The grade refutation in
section 4.3 measures ONE site: `inF`. **It says nothing about how many other
delivered or queued terms put a Σ₁ formula under a conjunction.** The sweep
is `grep` for `∧̇` with an existential-headed left half over `src/` and over
`agents/tasks/`, and it is a recon dispatch. This task's scope is one probe
and it did not run it. **A cure funded against `inF` alone is funded against
a number nobody has.**

**5.5 THE BRIEF'S NO-GO BRANCH IS WRONG AND SHOULD BE CORRECTED IN THE
TABLE.** It says NO-GO "retires `[LJ-1.651]` from the critical path with a
reason, which stops four reports' worth of citation drift". The measurement
says the opposite: `[LJ-1.651]` sits ON the critical path and delivered its
first third. The citation drift is real, but its cure is to cite
`lset-formula` as SYNTAX and not as a fact about `Lset`.

## 6. HEAP AND TIME, IN FULL

| run | file | exit | wall | peak bytes |
|---|---|---|---|---|
| `floor-1` | `runs/Floor659.agda` | 0 | 5.82 s | 857,849,856 |
| `p-1` | `Probe659.agda`, first attempt | 42 | 3.33 s | 611,631,104 |
| `p-2` | `Probe659.agda`, sections 1-4, 6 | 0 | 4.46 s | 838,664,192 |
| `p-3` | `Probe659.agda`, with 5.4 | 0 | 4.73 s | 763,379,712 |
| `p-4` | `Probe659.agda`, with the mapped negative | 0 | 5.68 s | 734,789,632 |
| `nolaws-1` | `runs/NO-LAWS.agda.txt` | 42 | 3.18 s | 693,878,784 |
| `floor-final` | `runs/Floor659.agda`, interface removed | 0 | 4.98 s | 537,296,896 |
| `p-final` | `Probe659.agda`, interface removed | 0 | 4.39 s | 787,546,112 |
| `meter-obligation` | the brief's obligation | 42 | 2.97 s | not measured |
| `meter-names` | 27 names, grouped | 0 | 3.71 s | not measured |

**The highest peak of any run is 857,849,856 bytes, 40 % of the
2,147,483,648-byte wide cap, and it is a GREEN run.** No run walled. No run
came near the 900 s wall cap enforced by the perl alarm (`runs/run.sh`),
because this macOS has no `timeout` (`[LJ-1.602]`, `[LJ-1.610]`).

**THE ONLY FAILURE OF THE WHOLE TASK WAS `p-1`**: `[NotInScope]` on
`SV.setIsSet`, because `hPropStructure` re-exports the `ZFStructure` record's
fields and `setIsSet` is not one of them
(`src/FOL/ZFStructure.lagda.md:91-97`). The fix is one expression: the
`isProp` witness comes from `snd (x SV.≈ˢ y)`, and at `𝒮ᵥ` that field IS the
path (`src/V/Hierarchy.lagda.md:82`). **No heap wall was met, so the
restructuring clause was not exercised.**

**Every `.agda` file under this task home typechecks.** There are two,
`Probe659.agda` and `runs/Floor659.agda`, and both are green in the table
above. The one file that cannot typecheck is named `runs/NO-LAWS.agda.txt`,
which is what the brief ordered and what `[LJ-1.636]` and `[LJ-1.643]` each
lost a return to. It was run as `.agda` and renamed after the run, the
mechanism `[LJ-1.650]` used.

**W4.** Nothing was retired and nothing was deleted. No `dev/ARCHIVE.md` row
is owed by this task. Section 5.5 recommends AGAINST a retirement the brief
contemplated.

## 7. WORKING TREE

`git status --porcelain` reads `?? agents/tasks/LJ-1-659/` and nothing else.

- `agents/tasks/LJ-1-659/Probe659.agda`: the probe, green (p-final).
- `agents/tasks/LJ-1-659/lj-1.659-report.md`: this report.
- `agents/tasks/LJ-1-659/review-of-lset-formula-to-level.md`: the stop.
- `agents/tasks/LJ-1-659/runs/`: every run, the floor, the red file and the
  two meters.

No `src/` change. No file under `_build/` authored (the interface cache
entries are Agda's own). Not committed, not pushed.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`**: **READ, AND IT IS SECTION 5.2.**
  At `archive/dev/LJ-dispatch-index.md:101` the line records

  > The level-hood adequacy at the hull

  as `PINNED, not discharged`, with "Three named leaves remain, each written
  as the term not written". **That is the same object this task's section 5.1
  asks the next brief to fund**, and it has already consumed a dispatch
  without closing. The row above it (`:100`) records that "cover and levelIn
  survive on the hull adequacy", which is the same dependency one level up.
- **`archive/dev/JOURNAL-archived.md`**: **READ, AND IT EXPLAINS SECTION
  4.1.** At `archive/dev/JOURNAL-archived.md:3988` the line reads

  > NEEDED**; parameters enter as an environment rather than by substitution.

  **That is why the tree has no substitution**, and therefore why the index
  binder must be the equality trick and not a substitution. The absence in
  `src/FOL/Manipulation/Renaming.lagda.md:7` is a design decision recorded
  here, not an oversight, so a brief must not price "add substitution" as a
  small fix.
- **`archive/dev/JOURNAL.md`**: **READ.** At `archive/dev/JOURNAL.md:410`
  the line reads

  > level-hood must run through codes and satisfaction, and those leaves are

  and it completes at `:411` with `unbounded.` **That is section 4.3's
  finding stated years earlier at the design level**: level-hood on this
  tower cannot avoid unbounded quantifiers, so the grade class it lands in
  was always going to be the binding constraint.
- **`dev/ARCHIVE.md`**: **DECLINED.** It is the register of retired modules.
  This task retires nothing (section 6) and recommends against a retirement
  (section 5.5), so it owes no row and reads none.
- **`archive/dev/ORCHESTRATION.md`**: **DECLINED.** It is the archived
  operating document, superseded by
  `dev/memos/LJ-4-pod-program-design.md`. Nothing in this task turns on how
  the loop is operated.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`**: **READ, AND IT IS THE SHAPE OF THE
  TWO MISSING LAWS.** At `dev/literature/devlin-II5.md:96` the line reads

  > (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

  **The `↔` is the point.** Devlin's statement is a BICONDITIONAL: one
  direction is `Sound`, the other is `Complete`. `[LJ-1.651]` delivered the
  `Φ`, which is the left-hand side of neither direction, and the brief priced
  it as though it were the whole line. At `:219` the same file gives the
  STAGE reading this task's `LevelFormula` uses:

  >    v = L_γ iff v ∈ L_α and L_α ⊨ ∃z φ(z, v, γ)

  Satisfaction INSIDE the stage on the right, real equality on the left,
  which is exactly why `Sound` concludes an equality in `S` from a witness in
  `⊨c`, and therefore why it bundles adequacy AND absoluteness.
- **`dev/literature/truncation-and-selection.md`**: **NOT USED, DECLINED.**
  It is about lifting truncations by a weakly constant endomap.
  `[LJ-1.650]`'s `skolemCode` needed it. This task's two truncations
  (`Complete`, `ix-complete`) are consumed by `PT.map` into another
  truncation and by `PT.rec` into a path type, which is a set, so no lifting
  question arises.
- **`dev/literature/digest.md`**: **NOT READ, DECLINED.** It is the
  corpus-wide digest. `devlin-II5.md` is its II.5 chapter at full detail, and
  that is the only chapter this task's statement comes from.
- **`dev/literature/terms-2026-08.md`**: **DECLINED.** It is a terminology
  file. This task adds no `dev/glossary.toml` entry and proposes none.
- **`dev/literature/geology.md`**: **DECLINED.** Set-theoretic geology bears
  on ground models and the mantle. This task is about a formula's slot order
  and its Levy grade, and neither is a geology question.
