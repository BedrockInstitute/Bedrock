# LJ-1.510 report: the depth was never the obstacle, and the supplier was already written

slot: `coder`. Written early as a skeleton and filled as runs land (C-22,
`dev/LESSONS.md:2297`). No commit, no push. I wrote only in
`agents/tasks/LJ-1-510/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did
not set `GHCRTS`. No heap event, no WALL.

TARGET: one term `consK-exist-at-frame` in
`agents/tasks/LJ-1-510/Probe510.agda`, the type of `TFacts`'s
`consK-exist` at `KValue`'s frame, **or a refutation with the hypothesis
it needs named**. The brief offers both. I returned both. Nothing lands
in `src/`. I did not build `consK-forall` or `consK-allin`, and I did not
build a `TFacts` value.

The standing direction (`dev/pod/direction.md:37`) reads

> **One SRC collection after LJ-1, not after `[LJ-2.5]`.** Owner, 2026-08-20.

This task is still LJ-1 work. It does not start that collection and it
does not start phase 3. No Boundary clause is in conflict.

## VERDICT

**GO on the obligation, and a REFUTATION of the record.** Two results, and
the second is the one the next brief has to act on.

1. **`consK-exist-at-frame` typechecks** (`Probe510.agda:277-282`,
   top-level alias at `:284`, exit 0, median **4.44 s** on three forced
   rechecks of the full file) and PASSes the program's witness meter
   (`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-510
   --brief agents/tasks/LJ-1-510/LJ-1.510.md`, exit 0, 3.17 s, **0
   UNRESOLVED of 1**, `probe_red=False`, `runs/witness-1.out`; re-run after the last report
   correction at 3.21 s, `runs/witness-2.out`).
   `.venv/bin/python` is absent in this worktree. I added no dependency.

2. **The record's field, AS WRITTEN, IS FALSE at `KValue`'s frame.**
   `no-yaK-is-not-a-theorem` (`Probe510.agda:395-405`, alias at `:407`)
   is a machine-checked counterexample. The obligation therefore carries
   ONE extra hypothesis, `⟨ fst ya ∈ fst Kset ⟩`, which is the weakest
   repair and is **the hypothesis `src/`'s own honest form already takes**
   (`src/L/Coding/EnvSupply.lagda.md:661-668`). I wrote
   `review-of-consK-exist-at-frame.md` for that finding, as my slot file
   requires when the brief's literal target is named FALSE.

**W3 is GO and it dissolves the brief's central worry.** The depth is not
an obstacle. See section 1.

**THE BRIEF'S CENTRAL PREMISE IS FALSE AND I HAVE TO SAY SO FIRST.** The
brief states, twice and in bold, that `consK` occurs **six times in
`src/`, all of them inside `src/L/Condensation/TwelveAgree.lagda.md`**,
and that **nothing outside that file names a `consK` of any shape**, and
that this family **has nothing** while every other family had a supplier
waiting. Measured:

- COUNT of `consK` in `src/`: **44**, in **four** files.
  `src/L/Condensation/TwelveAgree.lagda.md` 6,
  `src/L/Condensation.lagda.md` 17,
  `src/L/Condensation/UpperAgree.lagda.md` 7,
  `src/L/Coding/EnvSupply.lagda.md` 14.
  Command: `grep -rn "consK" src/ | wc -l`.
- The supplier the brief told me to sweep for EXISTS, in the very chapter
  `[LJ-1.499]` and `[LJ-1.509]` both found their answers in:
  `Fact.ConsK` (`src/L/Coding/EnvSupply.lagda.md:626-668`),
  `Fact.EnvClosure` with `envConsK` (`:672-700`), and
  `Fact.ConsKClosed` (`:702-748`). Each of `ConsK` and `ConsKClosed`
  carries all THREE names.
- The archive records the family as CLOSED, twice, in 2026.
  `archive/dev/LJ-dispatch-index.md:329` and `:330`, quoted in
  ARCHIVE USED below.

So the correct statement of this task's ground is the opposite of the
brief's: **the mathematics was delivered years-of-dispatches ago; what is
missing is one generic re-statement and one hypothesis the record
dropped.**

A GO here does NOT open the last corner of the record in the sense the
brief means. It closes one field under a stated weakening and it refutes
three. It does not land anything in `src/`. It does not build a `TFacts`
value. It does not fill `someEnv`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It does not
claim a trophy.

## 1. W3, THE WIDEST UNMEASURED TERM: THE DEPTH

Done FIRST and ALONE, with the obligation omitted, as the brief required.
The W3-only file is kept verbatim at `runs/Probe510.w3-only.agda.txt`.
Exit 0 on its FIRST submission (`runs/w3-0.out`, 2.64 s).

**GO, AND THE BRIEF ASKED THE WRONG QUESTION.** Two terms answer it.

**(a) The shift stops at NO depth.** `KTower` (`Probe510.agda:75-83`) is
the composition of `KFactsCons` stated ONCE, at any depth `k`: the record
`k` cells deeper, over ANY `k` cells. `kTower` (`:85-95`) builds it by
induction on `k`. `tower-14` (`Probe510.agda:112-113`) is that at
`KValue`'s own frame at `k = 14`, which is `[LJ-1.495]`'s six plus the
eight the brief asked about. **Nothing is special about fourteen and there
is no maximum to find**: the induction is uniform in `k`, so a brief that
needs twenty gets twenty for free.

**(b) THE FIELDS NEED NONE OF IT, AND THAT IS THE REAL MEASUREMENT.**
`depth-is-free` (`Probe510.agda:130-135`) is `refl`:

    lookup (suc¹⁴ K) (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')
      ≡ lookup (suc⁶ K) γ'

Fourteen minus the eight cell prefix is six, and six is the shift every
other field of `TFacts` already carries
(`src/L/Condensation/TwelveAgree.lagda.md:133`). `lookup (suc i) (c ∷ γ)`
is `lookup i γ` by definition and both sides are literal chains, so the
two are **the same `S`**, not two sets joined by a transport.
`depth-is-free-allin` (`:137-142`) is the same for `consK-allin`: sixteen
minus a ten cell prefix is six again.

**So the fourteen in the brief's title is a printing artefact of the
prefix, not a depth.** The three fields conclude at the SAME `Kset` as
`subK-un`, `valK` and every other field of the record. `[LJ-1.509]`
finding 3 (`agents/tasks/LJ-1-509/lj-1.509-report.md`, section 6 item 3)
already said the six-fold shift is definitional for a FIELD; this task
says the eight further cells are definitional too, and it says it for the
deepest fields in the record.

**The brief's stop condition did not trigger.** It said: "If the shift
stops short, name the step at which it stops and STOP." The shift stops
at no step, so the task continued.

W3 timing: measured at its own site and NOT funded against `[LJ-1.495]`'s
2.44 s, as the brief required. Median **2.40 s** over three forced
rechecks of the W3-only file, peak RSS 610,582,528 B (582.3 MiB).
Individual walls 2.36, 2.40, 2.54. The brief estimated "about 25 lines
and under 40 seconds"; measured **40 code lines** and **2.40 s**.

## 2. D-10: IS THE TARGET TRUE?

D-10 (`dev/LESSONS.md:1375`) asks whether a recorded target is TRUE before
its proof is priced. The brief told me to run it before any Agda. I did,
and it is what turned this task around.

1. **The statement is what the brief says it is.** `statement-matches`
   (`Probe510.agda:168-174`) reads `TFacts.consK-exist` off a `TFacts`
   value at the type `ConsKExist K γ'`, with no coercion, no `subst` and
   no re-association. Agda accepts it, so `ConsKExist` IS the field's
   type. The obligation never calls that term, so no `TFacts` field is
   used to prove a `TFacts` field.

2. **THE TARGET IS FALSE.** The field concludes `e' ∈ Kset` from a
   `consAtL` conjunct and the membership atom `e' ∈ ya`, and **nothing in
   the frame ties `ya` to `Kset`**: `ya` is a bound variable of the field.
   `src/`'s own honest form of the same field takes exactly that missing
   tie as a hypothesis (`src/L/Coding/EnvSupply.lagda.md:661-668`), and
   its whole body is one line, `Ktr (h .snd) yaK`. The record dropped the
   hypothesis and kept the conclusion.

3. **The refutation is machine-checked at THIS frame** (C-42 measures the
   site it names), `no-yaK-is-not-a-theorem` (`Probe510.agda:395-405`).
   Its shape:

   - `BB = sucʟ Lλ`, one cell above the bound, so the bound `Lset lam`
     is available as a VALUE (`self∈sucV`, `src/V/Model.lagda.md:236`;
     the idiom is `[LJ-1.506]`'s, `agents/tasks/LJ-1-506/Probe506.agda:128-130`).
   - `z` is the EMPTY environment over `BB` and `e'` is `z` with the bound
     consed on, both built by `envS` (`src/L/Coding/EnvSet.lagda.md:153-154`).
   - `consAtL-adequate` (`src/L/Coding/Model.lagda.md:1487-1498`) turns
     the first conjunct into exactly `fst e' ≡ env (cons (fst x) g)`,
     which is one `funExt` (`Probe510.agda:368-369`).
   - `ya = sucʟ e'` gives the membership atom for free.
   - If the bare form held, `e'` would lie in the bound; the bound is
     transitive, so its entry `pr (# 0) (Lset lam)` would too
     (`lookup-spec`, `src/L/Coding/Environment.lagda.md:102-104`), and
     `prK` (`src/L/Coding/EnvSupply.lagda.md:452-459`) would put
     `Lset lam` inside itself. `∈-irrefl`
     (`src/V/Hierarchy.lagda.md:155`) closes it.

   **THE WITNESS IS CHEAP BECAUSE `envS` EXISTS.** `fst (envS B g)` is
   `env` of the values DEFINITIONALLY, so no extensionality argument is
   needed to say what the witness set is. That is the reusable half of
   this refutation and the next brief should spend it rather than rebuild
   it.

4. **The weakest repairing hypothesis is `⟨ fst ya ∈ fst Kset ⟩`, and it
   PINS NO SLOT.** `ya` is a bound variable of the field, so nothing here
   fixes what occupies any cell of `γ'`. `[LJ-1.505]` is not pre-empted.
   I did not use a `TFacts` field to supply it and I did not postulate.

5. **AND THE REPAIR IS FREE AT THE CONSUMER, MEASURED.**
   `src/L/Condensation.lagda.md:4084` binds the existential clause as

       out h = λ c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv →

   and `unFullAt` (`src/L/Condensation.lagda.md:689-698`) shows what each
   binder is: `ya` is bounded by `var (suc⁴ K)`, so **`yaK` is the
   membership `⟨ fst ya ∈ fst (lookup K γ) ⟩`.** The call site is
   `:4062`, inside `module Leaf (E ya yc a ar c : S)` (`:4023`), and that
   same clause instantiates `Leaf` at `:4096` with the very `ya` that
   `yaK` is about. **So `yaK` is in scope at the one site that supplies
   the field**, and restoring the hypothesis costs the consumer ONE
   argument it is already holding. That is the finding that decides the
   cure's price, and it is why this is a repair rather than a route
   change.

## 3. THE OBLIGATION

**I WROTE NO SET THEORY.** The derivation is `Ktr (h .snd) yaK`, one line
(`Probe510.agda:254`), and it is `src/`'s own
(`src/L/Coding/EnvSupply.lagda.md:668`). What this task supplied is the
INPUT and the GENERICITY.

`ConsKExist⁺` (`Probe510.agda:205-213`) is the field with the one
hypothesis restored, written ONCE at `TFacts`'s generic shape.
`module ConsK` (`:233-254`) takes ONE hypothesis and nothing else:

| hypothesis | shape | where it comes from |
|---|---|---|
| `arity` | `(N v : S) → v ∈ N → N ∈ Kset → v ∈ Kset` | `KFacts.arityK`, `src/L/Condensation.lagda.md:6114-6115` |

`Ktr : isTransV (fst Kset)` (`Probe510.agda:242-247`) is the packaging
from the S-level `arityK` to the raw-carrier `isTransV` that
`Fact` (`src/L/Coding/EnvSupply.lagda.md:450`) wants. **`[LJ-1.509]`
measured that packaging at its own site and I RE-MEASURED it at mine**,
because a measured cure does not transfer by analogy (`AGENTS.md:45`). It
is the same three lines and it typechecks here.

`Frame.consK-exist-at-KValue` (`:277-282`) instantiates at `n = 9`
against `KValue`'s `Fin 14` over `S ^ 20`, the frame `[LJ-1.495]`
measured (`agents/tasks/LJ-1-495/lj-1.495-report.md:56-60`). **It passes
`facts .arityK` with NO `KFactsCons` and no conversion**, and the
conclusion needs none either, by `depth-is-free`.

**PREDECESSORS, TAKEN AS REPORTS AND NOT AS BRIEFS.** Audit F1 is the
measurement behind that rule; its heading at
`dev/pod/audit-2026-08-20.md:34` reads

> ### F1 / F2. LJ-1.398 GO is hollow

- `[LJ-1.495]` is **GO** (`agents/tasks/LJ-1-495/lj-1.495-report.md:71`).
  I took its frame arithmetic (`:56-60`) and its verdict. I did not import
  its probe. Nothing in it required a stop.
- `[LJ-1.509]` is **GO** (`agents/tasks/LJ-1-509/lj-1.509-report.md:56`).
  I took its `arityK`-not-`isTransV` finding as a lead and re-measured it.
  Nothing in it required a stop.
- `[LJ-1.506]` is GO; I took its refutation idiom (`sucʟ`, `self∈sucV`,
  `∈-irrefl`) and re-measured it at this site.
- `[LJ-1.499]` and `[LJ-1.500]` are cited by the brief as method, not as
  hypothesis; I used only their method (look for the supplier first), and
  it is what found `Fact.ConsK`.

No predecessor report names any of these statements FALSE, so no
predecessor forced a stop. The FALSE statement this task found is in
`src/`, not in a predecessor.

## THE THREE consK FIELDS

**A LINE NUMBER IN THE BRIEF IS WRONG AND IT CHANGES NOTHING
MATHEMATICALLY.** The brief gives the three as `:317`, `:322`, `:326`.
`src/L/Condensation/TwelveAgree.lagda.md:326` is **`subK-allin`**, not
`consK-allin`; `consK-allin` is at **`:332`**. Verified by
`grep -n "consK-exist :\|consK-forall :\|consK-allin :" src/L/Condensation/TwelveAgree.lagda.md`.

| # | field | line | hypothesis | prefix / index | serves? |
|---|---|---|---|---|---|
| 1 | `consK-exist` | `:317-321` | `consAtL 0 1 2` **∧ `e' ∈ ya`** | 8 cells / `suc¹⁴` → `suc⁶` | **BUILT here**, after ONE hypothesis is restored (`ya ∈ Kset`). Bare form REFUTED, `Probe510.agda:395-405`. |
| 2 | `consK-forall` | `:322-325` | `consAtL 0 1 2` only | 8 cells / `suc¹⁴` → `suc⁶` | **NOT AT ALL.** This argument does not reach it: there is no membership atom to feed `Ktr`. It needs the `envConsK` route and FOUR hypotheses. Bare form REFUTED by the SAME witness, `Probe510.agda:470-480`. |
| 3 | `consK-allin` | `:332-336` | `consAtL 0 1 3` only | 10 cells / `suc¹⁶` → `suc⁶` | **NOT AT ALL**, same reason. Serves the refutation after a PREFIX CHANGE and nothing else. Bare form REFUTED, `Probe510.agda:494-504`. |

**All three conclude at the SAME `Kset`.** That is `depth-is-free` and
`depth-is-free-allin`.

**The honest forms `src/` already carries**, for rows 2 and 3
(`src/L/Coding/EnvSupply.lagda.md:631-645` and `:646-660`), take FOUR
extra hypotheses each: an index function `g`, `fst z ≡ env g`,
`⟨ fst z ∈ fst K ⟩` and `⟨ fst x ∈ fst K ⟩`. Row 1's honest form
(`:661-668`) takes ONE. **So row 1 is the cheap one and the brief was
right to name it the obligation.** I did not check whether the four are in
scope at rows 2 and 3's consumers (`src/L/Condensation.lagda.md:3926`,
`:3959`, `:4949`, `:4996`, `:5093`, `:5124`, `:5222`, `:5253`); that is
the next brief's question and I am not going to guess it.

**C-42's sweep** (`dev/LESSONS.md:3752`) asks for the COUNT of the shape
before any cure is priced. COUNT of fields stating a `consAtL` closure:
**three per record**, in **three records**: `TFacts`
(`src/L/Condensation/TwelveAgree.lagda.md:317`, `:322`, `:332`), `UFacts`
(`src/L/Condensation/UpperAgree.lagda.md:191`, `:196`, `:206`) and the
`consK` telescope hypotheses of `src/L/Condensation.lagda.md` (`:3889`,
`:4001`, `:4183`, `:4817`, `:5070`, `:5199`). `UFacts`'s three are
CHARACTER-FOR-CHARACTER the same statements as `TFacts`'s, modulo the
environment's name (`γ` against `γ'`). **So the shape sits at SIX record
field positions and SIX telescope positions, twelve in all.** I refuted
three, at one frame, and priced no cure for the other nine.
`LFacts` (`src/L/Condensation/LowerAgree.lagda.md:95-225`) does NOT carry
them: the fills at `src/L/Condensation/TwelveAgree.lagda.md:478-481`
belong to `uf : UFacts` (`:445-446`), not to `lf : LFacts` (`:405-406`).
Grep count of `consK` in `src/L/Condensation/LowerAgree.lagda.md`: **0**.

**I DID NOT BUILD `consK-forall` OR `consK-allin`.** Rows 2 and 3 carry
refutations, which are the opposite of an inhabitant. AD12's one
obligation stays one, and the witness meter counts one.

## HOW DEEP THE SHIFT GOES

MEASURED, not estimated.

| what | depth reached | evidence |
|---|---|---|
| `KFactsCons`, one step | 1 | `src/L/Condensation.lagda.md:6122-6128` |
| `KValue.consed`, the tree's own consumer | 1 | `src/L/Condensation.lagda.md:7429-7434` |
| `[LJ-1.495]` `twice`, then `six` | 6 | `agents/tasks/LJ-1-495/lj-1.495-report.md:71` |
| `tower-14`, THIS task | **14** | `Probe510.agda:112-113`, exit 0 |
| `kTower k`, uniform in `k` | **unbounded** | `Probe510.agda:85-95`, induction on `k` |

**THE MAXIMUM DEPTH IS NOT FOURTEEN AND IT IS NOT A NUMBER.** `kTower` is
proved by induction on `k`, so the shift reaches ANY depth at `KValue`'s
frame; fourteen is only the instance this task needed. **No obstruction
exists to find**, which is why the brief's NO-GO branch ("the frame cannot
reach its own deepest fields") could not fire.

**And the number that actually matters is ZERO.** The three fields need
**no** `KFactsCons` application, because their fourteen and sixteen deep
lookups over eight and ten cell prefixes ARE the six deep lookup on `γ'`
by `refl` (`Probe510.agda:130-142`). The obligation applies `KFactsCons`
exactly **0** times.

## 4. W2, W4 AND THE LAWS

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

| piece | written once at | instantiated at |
|---|---|---|
| `KTower` / `kTower` | `Probe510.agda:75-95`, generic in the depth `k`, the length `m`, all fourteen indices and the environment | `k = 14` at `KValue`, `:113` |
| `ConsKExist` | `:153-160`, at `TFacts`'s own `Fin (5 + n)` over `S ^ (11 + n)` | `n = 9`, `:397` |
| `ConsKExist⁺` | `:205-213`, same generic shape | `n = 9`, `:279` |
| `module ConsK` | `:233-254`, generic frame | `:280-282` |
| `depth-is-free` | `:130-135`, generic frame | used definitionally throughout |
| `Ktr` packaging | `:242-247` | reused by `Refute` and `Sweep` through `CK` |

**A W2 DEFECT IN `src/`, MEASURED, AND IT IS THE ONE THING THIS FAMILY
STILL NEEDS.** `Fact.subK-gen` and `Fact.subKSucc-gen`
(`src/L/Coding/EnvSupply.lagda.md:481-495`) are generic in the environment
LENGTH and in all four indices, which is why `[LJ-1.509]` could spend them
at `KValue`'s frame. `Fact.ConsK`'s three
(`src/L/Coding/EnvSupply.lagda.md:631`, `:646`, `:661`) are **pinned to
`γ' : Vec S 2`**, so the formula they mention is `consAtL {11}` and the
frame needs `consAtL {29}`. **They cannot be instantiated at `KValue`'s
frame at all**, and that is the whole reason this task had to restate the
one line instead of calling it. **The cure is a `consK-gen` beside
`subK-gen`: generic in the length and in the three indices, body
unchanged.** It is one line of body and a telescope. I did not write it,
because it belongs in `src/` and nothing lands in `src/` from this task.

W4 does not fire: no module was retired.

P-l (`dev/LESSONS.md:2357`) did not fire. `ConsKExist`'s type
(`Probe510.agda:153-160`) names `Fin`, `lookup`, `consAtL`, `var`, `∈̇`,
`∧̇` and numerals, and NO transparent stage presentation. `sucV` occurs in
a stated type only in the `Frame`, `Refute`, `Sweep` and `Depth`
telescopes, and each is `KValue`'s OWN telescope entry copied verbatim
from `src/L/Condensation.lagda.md:7381`, where `sucV` is applied to a
bound variable. The refutation's successors are `sucʟ`, which is `opaque`
(`src/L/Axioms/Numerals.lagda.md:97-105`), the same guard `[LJ-1.506]`
used.

D-26 (`dev/LESSONS.md:1735`) did not fire: this is a closure over a
record, not a well-founded key on a tower.

D-10 fired and is section 2. C-22 fired: this report was written as a
skeleton before the obligation and filled as runs landed. C-42 fired and
is the sweep in THE THREE consK FIELDS.

## 5. MEASUREMENTS

One Agda process at a time. `GHCRTS="-A64m -I0 -M8g"`, set by the program
on this pane, untouched. A recheck is forced by deleting
`_build/2.8.0/agda/agents/tasks/LJ-1-510/Probe510.agdai` before each run,
so the probe re-elaborates while the `src/` interfaces stay warm.

| file | runs | median wall | peak RSS | evidence |
|---|---|---|---|---|
| W3 only, first landing | 1 | 2.64 s | 610,533,376 B (582.2 MiB) | `runs/w3-0.{out,time}` |
| W3 only | 3 forced | **2.40 s** | 610,582,528 B (582.3 MiB) | `runs/w3-r0..2.{out,time}` |
| obligation added | 1 | 3.57 s | 672,595,968 B (641.4 MiB) | `runs/oblig-0.{out,time}` |
| refutation added | 1 | 4.35 s | 766,509,056 B (731.0 MiB) | `runs/refute-0.{out,time}` |
| sweep added, full file | 1 | 4.58 s | 746,733,568 B (712.1 MiB) | `runs/sweep-0.{out,time}` |
| full file | 3 forced | **4.44 s** | 746,815,488 B (712.2 MiB) | `runs/full-r0..2.{out,time}` |
| witness meter | 2 | 3.17 s and 3.21 s (meter), 3.23 s (wall, run 1) | 643,153,920 B (run 1) | `runs/witness-1.out`, `runs/witness-2.out` |
| final forced recheck (warm) | 1 | 4.71 s | 746,733,568 B | `runs/final.{out,time}` |
| INCIDENTAL cold recompile of `L.Condensation` | 1 | 181.83 s | 8,892,547,072 B (8.28 GiB) | `runs/final-cold.{out,time}` |

Individual walls: W3 2.36, 2.40, 2.54; full 4.44, 4.40, 4.67. Exit 0
everywhere. **No heap event, no WALL, no rerun after a failure.** Every
term in this file typechecked on its FIRST submission; the later runs are
the forced rechecks, not repairs.

**ONE ADVISORY CHECK WAS ABANDONED, AND IT COST ONE COLD RECOMPILE.**
`scripts/measure/check-ratio.py --check` was started after every
measurement above had landed; it exceeded a 120 s budget and was killed.
No figure in this report comes from it, and no Agda process survived it
(`pgrep -fl agda` showed only `scripts/ops/agda-watchdog.sh`).
**It did invalidate `L.Condensation`'s interface**, so the next forced
recheck recompiled that master from scratch. I let that run finish, kept
it as `runs/final-cold.{out,time}`, and re-ran the warm recheck as
`runs/final.{out,time}`. Only the warm one is comparable with the rows
above.

**THE COLD ROW IS AN UNPLANNED MEASUREMENT AND IT IS WORTH KEEPING.**
A full recompile of `src/L/Condensation.lagda.md` plus this probe, at the
WIDE caliber `-A64m -I0 -M8g` and one Agda process, is **181.83 s** with a
peak RSS of **8,892,547,072 B (8.28 GiB)**, exit 0. **It did not wall.**
That is the closest measurement I have seen to the wide cap and the next
brief that plans to touch `L.Condensation` should price against it rather
than against a probe.

The gates that DID run and are clean: `scripts/gate/check-probes.py
--check` (exit 0, "clean, 5203 tracked files, no probe outside
agents/tasks/") and `scripts/pod/check-closure.py --check closure`
(exit 0, "clean, 102 masters").

**THE BRIEF'S SHAPE ESTIMATE WAS 180 LINES, OF WHICH 45 THE OBLIGATION.**
Measured: the file is **507 lines**, of which 183 are comment, 69 blank
and **255 code**. The obligation's own chain, `ConsKExist⁺` (`:205-213`)
plus `module ConsK` (`:233-254`) plus `module Frame` (`:269-284`), is
**37 code lines**, under the brief's 45-line shape, and almost all of it
is the statement: `consK-exist`'s BODY is ONE line (`:254`) and `Frame`'s
instantiation is three (`:280-282`). The file overruns the 180-line shape
because W3 (40), the two `statement-matches` certificates (7 + 14), the
refutation (60) and the C-42 sweep (67) are all extra and only W3 was
required. Comparables are of SHAPE and nothing is funded against them.

**THE RATIO BAR DOES NOT FIRE.** This task wrote a raw `.agda` probe, this
report, `review-of-consK-exist-at-frame.md` and the `runs/` evidence, and
nothing else. A raw `.agda` file carries no ` ```agda ` fence, so the
divisor is 0 and the bar cannot fire. In-fence `agda` lines under `src/`
written by this task: **0**. Nothing landed in `src/`.

## 6. WHAT THE NEXT BRIEF SHOULD KNOW

1. **THE DEPTH IS A PRINTING ARTEFACT. STOP PRICING IT.** Any field of
   `TFacts` whose conclusion is `lookup (sucⁿ K)` over an `(n - 6)` cell
   prefix concludes at the frame's own `Kset`, by `refl`. Three fields at
   fourteen and sixteen were the deepest in the record and they cost
   nothing. `KFactsCons` applications needed: **0**.
2. **`kTower` is uniform in the depth and it is 20 code lines.** If a
   later task really does need the RECORD `k` cells deeper, that is
   `Probe510.agda:85-95` and it is worth ten minutes to move into `src/`
   as a replacement for hand-iterating `KFactsCons`.
3. **THE RECORD STATES THREE FIELDS THAT ARE FALSE.** `consK-exist`,
   `consK-forall` and `consK-allin`, in `TFacts` and again in `UFacts`,
   nine positions in all. This is a `src/` defect and not a route problem.
   The cure for `consK-exist` is ONE hypothesis and it is already in scope
   at the consumer (`src/L/Condensation.lagda.md:4084`). See
   `review-of-consK-exist-at-frame.md`.
4. **THE ONE THING STILL MISSING IS `consK-gen`.** `Fact.ConsK`'s three
   are pinned to `Vec S 2` while `subK-gen` beside them is generic. Making
   the three generic in the environment length and the three indices is a
   telescope change with an unchanged body, and it is what would let a
   frame SPEND them instead of restating them. That is a `src/` task and
   it should be queued as one.
5. **`envS` is how you build an environment witness inside `L` for
   nothing.** `src/L/Coding/EnvSet.lagda.md:153-154`;
   `fst (envS B g)` is `env` of the values definitionally. Any later
   refutation or construction that has to exhibit a concrete `consAtL`
   instance should start there, not from `pairʟ` and extensionality.
6. **Ask a frame for `arityK`, never for `isTransV`.** `[LJ-1.509]`'s
   finding, re-measured here at a second site
   (`Probe510.agda:242-247`), so it is now measured twice and is a
   candidate for `dev/LESSONS.md` if a third site wants it.
7. **The brief's sweep numbers were wrong by a factor of seven.** Before
   the next brief in this series asserts that a family "has nothing", run
   `grep -rn "<name>" src/ | wc -l` and put the number in the brief. This
   one cost the dispatch nothing, because the sweep the brief itself
   ordered caught it, but a brief that had been believed would have paid
   for a re-derivation of `envConsK`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED, and it is the
  decisive archive hit of this task.** `:329` reads:

  `| LJ-1.259 | Build the env closure | BUILDS ON ONE NEW HYPOTHESIS. 3 consK CLOSE | The sweep caught the supply before it was called absent: Lset-fin and paramEnv∈ are delivered |`

  and `:330` reads:

  `| LJ-1.261 | The finite-supremum merge | BUILDS. finSetK is SUPPLIED, 3 consK CLOSE | 148 lines, 48 for the merge against union's 52. The first attempt walled and the cure is recorded |`

  and `:328` reads:

  `| LJ-1.258 | The fifteen fields that do not touch envSetK | 12 OF 15. RATES ARE 2, 1, 1 BODY LINES | Far UNDER 9.1. LJ-1.168's 1.5-line entry estimate HOLDS. The three consK need an env closure |`

  **Three rows, in order, that record this exact family being identified,
  closed and then closed again.** `[LJ-1.258]` names the gap in the words
  the brief used, `[LJ-1.259]` closes it, `[LJ-1.261]` supplies the last
  hypothesis. The code those rows produced is
  `src/L/Coding/EnvSupply.lagda.md:626-748` today, and the comments there
  cite the same two task codes (`:625-626`, `:670`). Row `:329`'s own
  remark, "the sweep caught the supply before it was called absent", is
  the same failure this task's brief repeated.
- `archive/dev/JOURNAL.md`: **READ, NOT USED.** `:1` reads: `# ARCHIVED 2026-08-20`.
  Its one `[LJ-1.259]` mention (`:1114`) is about a probe file being moved
  out of `src/` during another task, not about the closure. Grep count for
  `consK` and `consAt`: **0**. Nothing in it bears on this task.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `:1` reads:
  `# Archived journal: the retired route`. Grep count for `consK` and
  `consAt`: **0**. It is the retired route's journal and this family is on
  the live route. Not read beyond that search.
- `dev/ARCHIVE.md`: **DECLINED.** `:1` reads:
  `# ARCHIVE.md: the archive registry`. It registers RETIRED MODULES, and
  W4 did not fire on this task because nothing was retired. Grep count for
  `consK` and `consAt`: **0**. Not used.
- `archive/dev/DECISIONS-archived.md`: **DECLINED.** `:1` reads:
  `# Archived decisions: the D series`. A bare `D<n>` resolves only against
  this archived series and is not a rule in force. Grep count for `consK`
  and `consAt`: **0**. Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, background only, and NO step of
  the Agda rests on it.** `:75` reads:

  `> (ii) if Y ⊆ X is transitive, then π ↾ Y = id ↾ Y;`

  This is the condensation lemma's transitivity clause, which is a
  COLLAPSE argument. The transitivity this task uses is the BOUND's own
  (`arityK`, `Ktr`), a different use of the word, and nothing here touches
  condensation or collapse. I read it to be sure the two were not the
  same, and they are not.
- `dev/literature/truncation-and-selection.md`: **DECLINED.** `:1` reads:
  `# Truncation and selection: how the two literatures pick a witness`.
  This task selects no witness out of a truncation. The one place a `PT`
  step could have entered, the environment entry, is closed by
  `lookup-spec`'s backward direction with `refl`
  (`Probe510.agda:388-391`). Not used.
- `dev/literature/digest.md`: **DECLINED.** `:1` reads:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  The rud route is the ARCHIVED route
  (`archive/src/2026-08-09-rud-route/`), and this family is on the live
  one. Not used.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` reads:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  It is a translation dossier. This task added no `dev/glossary.toml`
  entry, coined no term and wrote no prose. Not used.
- `dev/literature/geology.md`: **DECLINED.** `:1` reads:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Set-theoretic geology belongs to the route question at `[LJ-2.5]`, not
  to a field of a delivered record. Not used.
