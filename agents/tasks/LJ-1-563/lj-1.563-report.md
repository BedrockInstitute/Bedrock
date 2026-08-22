# LJ-1.563 report: THE LAST THREE ASK AT THE FIELD'S OWN BINDERS, AND THAT IS THE SEAM

slot: `coder`. I wrote this file early as a skeleton and I filled it as the runs
landed (C-22, `dev/LESSONS.md:2297`). No commit, no push. I wrote only in
`agents/tasks/LJ-1-563/`. Agda ran under the caliber that the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **No heap event, no WALL.**

TARGET: one term `last-three-collected` in `agents/tasks/LJ-1-563/Probe563.agda`.
The brief asks for the three `TFacts` fields that ask for something the record
does not give and are NOT memberships in `K`, collected at `KValue`'s frame.
Nothing lands in `src/`. I did not build a `TFacts` value. I did not re-collect
the 38, the 37 or the 13. I did not trim any telescope. I did not edit `src/`. I
postulated nothing.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection after
LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection and it does not start phase 3. No Boundary clause is in conflict.

## VERDICT

**GO, AND THE COUNT IS THREE. ALL THREE ARE COLLECTED.**

1. **The count IS three and I confirm it at first hand.** `[LJ-1.551]` named
   them (`agents/tasks/LJ-1-551/lj-1.551-report.md:381-386`) and `[LJ-1.553]`
   re-read them and named the same three
   (`agents/tasks/LJ-1-553/lj-1.553-report.md:287-308`). I read all three in the
   master and the count did not move. Section `THE THREE, NAMED`.

2. **`last-three-collected` typechecks** (`Probe563.agda:399-406`, top-level
   alias at `:408`), `--safe` at `:1`, exit 0, no hole, no postulate, no
   `TERMINATING`, no warning on any run (`runs/final.out`). It typechecked on its
   first full run at every stage (`runs/frame-try-0.out`, `runs/nb-try-0.out`).

3. It PASSes the program's witness meter:
   `/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-563 --brief
   agents/tasks/LJ-1-563/LJ-1.563.md`, exit 0, **0 UNRESOLVED of 1**,
   `probe_red=False` (`runs/witness-0.out`). `.venv/bin/python` is absent in this
   worktree, as `[LJ-1.512]`, `[LJ-1.545]`, `[LJ-1.551]` and `[LJ-1.553]` all
   found. I added no dependency. `check-probes.py --check` is clean
   (`runs/check-probes.out`, 6583 tracked files, no probe outside
   `agents/tasks/`). `check-fences.py`, `check-rule-ids.py`, `lint-agda.py` and
   `lint-prose.py` are also clean (`runs/check-fences.out`,
   `runs/check-rule-ids.out`, `runs/lint-agda.out`, `runs/lint-prose.out`).

4. **THE THREE DO NOT SHARE ONE HYPOTHESIS AND THEY DO NOT NEED ONE.** The brief
   allows three different asks and there are two: an environment witness plus two
   memberships for the two `consK` rows, and a truncated numeral arity for
   `someEnv`. **Each is carried as an EXTRA ARGUMENT of the field, not as a
   supplied hypothesis of the frame.** Section `WHY THE EXTRAS ARE ARGUMENTS AND
   NOT A SUPPLY` says why that is forced, and the machine says it too.

5. **THE FRAME SUPPLIES NOTHING. THE TELESCOPE IS `KValue`'s SEVEN, `ω∈σ`, AND
   THE FIVE FREE CELLS, AND THAT IS ALL** (`Probe563.agda:362-367` and `:399`). `[LJ-1.553]`
   had to supply ONE membership and inhabit it
   (`agents/tasks/LJ-1-553/Probe553.agda:235-236`). **This task supplies no
   hypothesis at all**: every one of `Discharge`'s seven parameters is paid from
   the tree at `Probe563.agda:402-406`.

6. **W3 IS GO AND IT RAN FIRST, ALONE.** The three extras hold TOGETHER at one
   frame at a CONCRETE instantiation, not at a free cell
   (`Probe563.agda:120-127`, top-level alias `:129`). Section `W3`.

7. **THE FRONT NOW STANDS AT 49 OF 59, of which 46 are at the record's own type
   and 3 carry a named extra. 10 are not collected at all.** Section `WHAT THE
   FRONT NOW STANDS AT`. I counted the fields myself.

8. **THE THREE ARE NOT CHEAPER THAN THE NINE, AND I STOP THERE.** 740,835,328 B
   against `[LJ-1.553]`'s 695,435,264 B on THIS pane. **That gap is a THIRD of
   `[LJ-1.551]`'s unexplained band, so I do NOT claim the three cost more.** What
   I do claim is that no field-count model survives contact with it. Section
   `THE PRICE`.

I did not write `agents/tasks/LJ-1-563/review-of-last-three.md`. All three
obligations are inhabited, so there is no NO-GO to state. What the record
over-asks is reported below and is machine-checked, but it did not stop a single
field from being collected.

**A NOTE ON THE RATIO BAR.** My write scope is one raw `.agda` probe and two
`.md` files. A raw `.agda` file carries no ` ```agda ` fence, so the in-fence
divisor is 0 and the bar cannot fire on this return, as my role section states.

## 0. THE PREDECESSORS, TAKEN FROM THEIR REPORTS

Audit F1 (`dev/pod/audit-2026-08-20.md`) says a module hypothesis taken from a
predecessor is the type that the predecessor DELIVERED, read from its report and
its probe. I opened both for both.

- **`[LJ-1.551]` is GO** (`agents/tasks/LJ-1-551/lj-1.551-report.md:23`, which
  reads `**GO, AND THE COUNT IS 37, NOT 38.**`). I take its FRAME from
  `agents/tasks/LJ-1-551/Probe551.agda:337-338` and I re-state it in my own file
  rather than importing its probe. I do NOT take its 37 fields.
- **`[LJ-1.553]` is GO** (`agents/tasks/LJ-1-553/lj-1.553-report.md:23`, which
  reads `**GO, AND THE COUNT IS 9 OF THE 13.**`). I take from it the frame it
  delivered (`agents/tasks/LJ-1-553/Probe553.agda:343-344`, the same as
  `[LJ-1.551]`'s), and its measured finding that the record's `transK` over `S`
  cannot produce `EnvSupply.Fact`'s `isTransV` over `V ℓ`
  (`agents/tasks/LJ-1-553/lj-1.553-report.md:232-247`). **That finding is why my
  `Discharge` takes `Ktr`, `pairK`, `sucK`, `numK0` and `finSetK` as `V`-level
  parameters and never touches the record's `S`-level fields.** I do NOT take its
  nine fields.

Neither is a NO-GO on a statement I inhabit here, so no stop is owed on that
account.

## D-10, BEFORE ANY AGDA: THE COUNT IS THREE AND IT DID NOT MOVE

The brief tells me to take `[LJ-1.551]`'s three and to report the number I
measure if it is not three. **It is three.** I read each in the master rather
than taking either predecessor's summary.

`[LJ-1.512]` counted 54 honest forms of 59 with 16 asking for more
(`agents/tasks/LJ-1-512/lj-1.512-report.md:1`). `[LJ-1.553]` split the 16 into
9 that one membership reaches, 4 memberships at binders no supply reaches, and
these 3 (`agents/tasks/LJ-1-553/lj-1.553-report.md:287-308`). 9 + 4 + 3 = 16, and
the three below are the residue.

## THE THREE, NAMED

Record lines are `src/L/Condensation/TwelveAgree.lagda.md`. Honest lines are
`src/L/Coding/EnvSupply.lagda.md`.

| # | field | record | honest form | what it asks that the record does not give | collected |
|---:|---|---:|---:|---|---|
| 1 | `someEnv` | `:289` | `:417-444` | `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, the truncated NUMERAL arity | **YES** |
| 2 | `consK-forall` | `:322-325` | `:712-725` | `{k : ℕ} (g : Fin k → V ℓ)` with `fst z ≡ env g`, plus `⟨ fst z ∈ fst K ⟩` and `⟨ fst x ∈ fst K ⟩` | **YES** |
| 3 | `consK-allin` | `:332-335` | `:727-740` | the SAME three, one environment cell deeper | **YES** |

**1. `someEnv`.** Its type is `someEnvDef {n} K γ'`
(`src/L/Condensation/LowerAgree.lagda.md:52-59`), which binds
`(ya yc b a ar c : S)` and hands over three memberships in `K` and NOTHING
about `ar` beyond that. The tree's only supplier is `SupplyEnv.someEnv`
(`src/L/Coding/EnvSupply.lagda.md:417-444`) and its first hypothesis is
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` (`:418`). **That hypothesis is not decoration
and the master says why in its own comment**: `envSetK` was RESTRICTED to a
numeral arity by `[LJ-1.173]` because at an unrestricted `ar` the field asks a
level to hold the full constructible function space, and a successor-closed limit
does not, so the general form is FALSE at the bound `HullStage` gives
(`src/L/Condensation/TwelveAgree.lagda.md:296-308`, citing `[LJ-1.172]`).
**`someEnv` was never given the same restriction, and that is the gap.**

**2 and 3. `consK-forall` and `consK-allin`.** Each field's own hypothesis is one
satisfaction, `⊨ consAtL` at its slots, and nothing else. The honest forms
(`ConsK` at `:631` and `:646`, `ConsKClosed` at `:712` and `:727`) each add
`{k : ℕ} (g : Fin k → V ℓ)` with `fst z ≡ env g`, `⟨ fst z ∈ fst K ⟩` and
`⟨ fst x ∈ fst K ⟩`, because the proof rebuilds `e'` as `env (cons (fst x) g)`
before the closure applies (`:719-725`). `consK-allin` is the same construction
at a one-cell-deeper environment (`:727-740`), so it is the same shell at
different slots and NOT the same instance.

**THE TWO ASKS ARE NOT ONE AND I DID NOT FORCE THEM TOGETHER.** They are
collected side by side, as the brief allows.

## THE OBLIGATION, AND WHAT IT IS EXACTLY

`LastThree` (`Probe563.agda:149-176`) states the three ONCE at a generic `K` and
a generic `γ'` (W2), at `TFacts`'s own indices. **Every field type is the
master's own, extracted with `sed` and not retyped** (`runs/fields-verbatim.txt`
holds the extraction), with `someEnvDef` inlined from
`src/L/Condensation/LowerAgree.lagda.md:53-59`, and with each field's EXTRA ASK
written in as extra arguments, each marked `-- EXTRA` in the file.

**`statement-matches` (`Probe563.agda:190-200`) IS AGDA'S WORD THAT THE EXTRAS
ARE THE WHOLE WEAKENING.** It fills every field of `LastThree` from a `TFacts`
value by DROPPING the extras on the left of the arrow and doing nothing else: no
coercion, no `subst`, no re-association. So the answer to "what did you weaken"
is not a sentence, it is a term that typechecks. It is not part of the obligation
and the obligation never calls it. This is `[LJ-1.545]`'s device
(`agents/tasks/LJ-1-553/Probe553.agda:305-315` uses it at nine fields).

`Discharge` (`Probe563.agda:226-338`) fills the three at a generic `K` and `γ'`
from seven parameters. `Frame` (`:361-406`) instantiates at `n = 9` against
`KValue`'s `Fin 14` and pays all seven from the tree:

| parameter | paid by | at |
|---|---|---|
| `Ktr` | `layer-trans (Lset-layer lam)` | `Probe563.agda:381-383` |
| `numK0` | `Bound.#∈Tλ 0` | `:385-387` |
| `sucK` | `SupplyEnv.sucK` | `src/L/Coding/EnvSupply.lagda.md:204` |
| `pairK` | `Bound.pr∈λ` | `src/L/Coding/Bound.lagda.md:69`, re-exported at `:135-136` |
| `finSetK` | `SupplyMerge.finSetK` | `src/L/Coding/EnvSupply.lagda.md:906` |
| `envSetGenK` | `SupplyEnv.envSetK` under `PT.rec` | `Probe563.agda:389-396` |
| `envInKp` | `SupplyEnv.envInK-gen` | `src/L/Coding/EnvSupply.lagda.md:351` |

**`ω∈σ` IS IN THE TELESCOPE AND THIS TASK CONSUMES IT.** `someEnv+` runs through
`SupplyEnv.envSetK`, which runs through `envSetNumeral∈`
(`src/L/Coding/Key.lagda.md:486-490`), whose third argument is `⟨ ω ∈ σ ⟩`.
`[LJ-1.553]` carried the same parameter and never consumed it
(`agents/tasks/LJ-1-553/lj-1.553-report.md:256`, "THE NINE NEVER CONSUME
IT"). **The cell-0 pin is load-bearing here for the same reason**: `someEnv+`
reads `lookup zero γ'` as the carrier slot `B`, and at this frame that cell is
`SupplyEnv.B₀`.

## W3, THE WIDEST UNMEASURED TERM

The brief names it: whether the three hypotheses hold together at one frame.

    -- the three fields' extra hypotheses, at KValue's frame, INHABITED

**GO, AND THE INSTANTIATION IS CONCRETE.** `extras-inhabited`
(`Probe563.agda:120-127`, top-level alias `:129`) is ONE value carrying all three
at one frame:

- **the environment witness**: `k = 0` and `g₀ : Fin 0 → V ℓ` the empty family,
  with `fst z₀ ≡ env g₀` by `refl`, where `z₀` is `env {0} g₀` carrying its own
  `isL` (`Probe563.agda:105-107`). `env {0} g₀` IS `finSet 0 (λ i → pr (# (toℕ i)) (g₀ i))`
  character for character: `env` at `src/L/Coding/Environment.lagda.md:84-86` and
  `finSet` at `src/L/Axioms/Basic.lagda.md:285-286` are the same `sett`.
- **the two memberships**: `⟨ fst z₀ ∈ Lset lam ⟩` from `SupplyMerge.finSetK` at
  `n = 0` (`:102-103`), and `⟨ fst x₀ ∈ Lset lam ⟩` from `KValue.facts .numK0`
  with `x₀ = numeralL 0` (`:112-113`).
- **the truncated numeral arity**: `∣ 0 , numeralL-fst 0 ∣₁` at the same
  `ar = x₀` (`:127`).

**THE GUARD IS STRONGER HERE THAN IT WAS AT `[LJ-1.553]`, AND I SAY SO.**
`[LJ-1.553]` wrote that its witness sat at a FREE cell of the frame, so a single
instantiation proved only that the hypothesis was not absurd
(`agents/tasks/LJ-1-553/lj-1.553-report.md:181-185`). **My three extras sit at
binders of the FIELDS, not at cells of the frame**, so they are inhabited per
application and the free cells `g1 .. g5` never enter W3 at all. `[LJ-1.71]`'s
failure was a telescope uninhabited at EVERY frame
(`archive/dev/LJ-dispatch-index.md:135`); nothing of that shape can happen to an
argument that a caller chooses.

W3 alone, three forced rechecks with the interface deleted before each
(`runs/w3-0.time` to `runs/w3-2.time`; the file at that run is
`runs/Probe563.w3-only.agda.txt`, 119 lines): **2.18 to 2.24 s, median peak RSS
687,964,160 B, 8.01 percent of the 8 GiB cap.** Exit 0 on the first run
(`runs/w3-try-0.out`). The brief estimated about 18 lines and under 30 seconds. It
was 119 lines, most of them the import header the file needs anyway, and 2.2
seconds.

**SO THE TASK WAS NOT REFUTED BEFORE A FIELD WAS TOUCHED.**

## WHY THE EXTRAS ARE ARGUMENTS AND NOT A SUPPLY

`[LJ-1.553]` closed nine fields by SUPPLYING one hypothesis at a frame SLOT and
inhabiting it once. **That move is not available here, and I did not argue it: I
refuted it.** `no-blanket-supply` (`Probe563.agda:458-462`, top-level alias
`:464`) is one value carrying two refutations at `KValue`'s frame.

1. **The `consK` pair's membership extra, blanket form**, that is
   `(z : S) → ⟨ fst z ∈ Lset lam ⟩`: REFUTED by the level itself,
   `z := LsetS lam ordλ` and `∈-irrefl` (`Probe563.agda:436-437`).
2. **`someEnv`'s truncation extra, blanket form**, that is
   `(ar : S) → ⟨ fst ar ∈ Lset lam ⟩ → ∥ Σ[ p ∈ ℕ ] (fst ar ≡ # p) ∥₁`: REFUTED
   by `ω`, which IS in `K` at this frame because the frame carries `ω∈σ`
   (`Probe563.agda:442-455`). The membership goes `ω ∈ sucV gam` then
   `sucV gam ∈ Lset lam` by `ord∈Lset-suc` and `Lset-mono`, then `Bound.trans∈λ`;
   the non-numerality is `#∈ω p` against `∈-irrefl ω`.

**THIS REFUTES THE BLANKET FORM AND NOTHING MORE.** It says nothing about a
supply CONDITIONED on the field's own satisfaction hypothesis. **I did not
measure that and I do not claim it.** Section `WHAT THE NEXT BRIEF NEEDS` names
it as the next probe.

## THE TWO THINGS THAT RESISTED

### 1. `src/` HAS NO SLOT-GENERIC `consK` SHELL, AND THE PINNED FORMS CANNOT BE APPLIED AT THIS FRAME AT ALL

**MEASURED: sixteen honest forms in `src/L/Coding/EnvSupply.lagda.md` are pinned
at `(γ' : Vec S 2)`.** `grep -n "Vec S 2"` returns exactly 16 lines: `:497`,
`:508`, `:519`, `:530`, `:541`, `:552`, `:563`, `:594`, `:604`, `:614`, `:631`,
`:646`, `:661`, `:712`, `:727`, `:742`. **A record field's tail is `S ^ (11 + n)`
and `11 + n` is never 2, so not one of the sixteen can be applied at the record's
frame.**

**THIRTEEN OF THE SIXTEEN HAVE A GENERIC ESCAPE AND THREE DO NOT.** The seven
`subK-*` go through `subK-gen` (`:481`) or `subKSucc-gen` (`:489`), and that is
how `[LJ-1.553]` reached them. `valV`, `valW` and `wKfact` go through `tmValK`
(`:575`). **The three `consK` forms have no `-gen` shell in `src/`, in either
copy** (`ConsK` at `:626`, `ConsKClosed` at `:702`), **so there are six pinned
declarations and zero generic ones.**

So I wrote the shell: `Discharge.consK-gen` (`Probe563.agda:267-279`). Its body
is `ConsKClosed.consK-forall`'s own body
(`src/L/Coding/EnvSupply.lagda.md:719-725`) with the vector length and the three
slots made variable and NOTHING else changed. Both `consAtL-adequate`
(`src/L/Coding/Model.lagda.md:1487-1491`) and `EnvClosure.envConsK`
(`src/L/Coding/EnvSupply.lagda.md:692-699`) are already generic, so the shell is
free.

### 2. `SupplyEnv.someEnv` IS PINNED AT A FOUR-CELL ENVIRONMENT AND `someEnvDef` ASKS AT A TWENTY-SEVEN-CELL ONE

`SupplyEnv.someEnv` concludes at `E ∷ ar ∷ B₀ ∷ level ∷ []`
(`src/L/Coding/EnvSupply.lagda.md:431`) while `someEnvDef` asks for satisfaction
at `E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ`
(`src/L/Condensation/LowerAgree.lagda.md:58`), which at `n = 9` is 27 cells.
**The two are the SAME formula constructor at different slots**, because
`envHypB2 {m} B K` is `envSetB zero (suc^5 zero) (suc^7 B) (suc^7 K)`
(`src/L/Condensation.lagda.md:654-658`) and `envSetB` takes its four slots as
`Fin n` (`:567-569`). So the repair is again a shell, and again the tree already
carries every generic piece: `Discharge.someEnv-gen` (`Probe563.agda:293-308`) is
`EnvSet.back` (`src/L/Condensation.lagda.md:3045`) after `Generic.Holds.holds`
(`src/L/Coding/EnvSet.lagda.md:540`), both already generic in the vector length.

**THE ONE THING THAT MADE IT WORK IS THE CELL-0 PIN.** `envHypB2`'s `B` slot is
`zero`, so the carrier the collected `someEnv+` builds over is `lookup zero γ'`,
and `[LJ-1.551]`'s frame pins that cell to `SupplyEnv.B₀`
(`agents/tasks/LJ-1-551/Probe551.agda:338`). **At a frame that does not pin cell
0 to the carrier, `someEnv` does not collect at all.** That is a constraint on the
frame and it belongs in the next brief.

## THE C-42 SWEEP: HOW FAR EACH SHAPE EXTENDS

C-42 (`dev/LESSONS.md:3752`) says a measurement of one site says nothing about how
many sites carry the shape, and that the count comes before the cure. I counted
both shapes and I priced neither.

**SHAPE A: a field whose honest form needs a fact at a binder the FIELD ITSELF
quantifies over.** Fourteen sites in three records, by name:

| record | fields | count |
|---|---|---:|
| `TFacts` (59 fields) | `valV`, `valW`, `wKfact`, `consK-exist`, `consK-forall`, `consK-allin`, `someEnv` | 7 |
| `UFacts` (35 fields) | `wKfact`, `consK-exist`, `consK-forall`, `consK-allin` | 4 |
| `LFacts` (37 fields) | `valV`, `valW`, `someEnv` | 3 |

Field counts are my own, from the field lines of `record TFacts`
(`src/L/Condensation/TwelveAgree.lagda.md:129-335`), `record UFacts`
(`src/L/Condensation/UpperAgree.lagda.md:92-210`) and `record LFacts`
(`src/L/Condensation/LowerAgree.lagda.md:95-230`). **This task collected three of
the fourteen and left eleven. I priced none of them.**

**SHAPE B: an honest form pinned to a fixed environment length.** Seventeen
sites: the sixteen `Vec S 2` forms listed above, plus `SupplyEnv.someEnv`'s
four-cell pin (`:431`). **Six of the seventeen have no generic shell in `src/`
and this probe wrote two shells that cover all six plus `someEnv`.** The shells
are in the probe and NOT in `src/`, because a probe never lands in `src/` and
because a module redesign is the mathematician's call under AD3.

## WHAT THE FRONT NOW STANDS AT

**I COUNTED THE FIELDS. I DID NOT ESTIMATE.** `record TFacts` has **59** field
lines (`src/L/Condensation/TwelveAgree.lagda.md:129-335`), which agrees with
`[LJ-1.512]`.

| state | count | which |
|---|---:|---|
| collected at the record's OWN type | **46** | `[LJ-1.551]`'s 37 clean, `[LJ-1.553]`'s 9 |
| collected WITH a named extra | **3** | `someEnv`, `consK-forall`, `consK-allin` (this task) |
| **have a collected value** | **49** | |
| NOT collected at all | **10** | below |

**THE TEN, BY NAME.** `codesK`, `codesK-un`, `t0eq`, `t1eq`, `t0K` are the five
that `[LJ-1.512]` measured to have no supplier at all, and I did not re-open that.
`valV`, `valW`, `wKfact`, `consK-exist` are `[LJ-1.553]`'s four memberships at
binders the field quantifies over. `envSetK` runs the other way and needs a
decision, not a proof, which is `[LJ-1.551]`'s finding
(`agents/tasks/LJ-1-551/lj-1.551-report.md:418-419`). 5 + 4 + 1 = 10, and
49 + 10 = 59.

**SO THE HONEST-FORM FRONT IS NOT CLOSED, AND THE BRIEF'S "A GO CLOSES THE
HONEST-FORM FRONT" IS ONE STEP AHEAD OF THE TREE.** What closed is the group the
brief named. Ten fields remain, and nine of them were already known before this
task.

## THE PRICE

Every row is a WHOLE-FILE total on ONE pane, which is what `[LJ-1.551]`'s band
finding demands. No row is a baseline subtraction. Three forced rechecks per row,
with the interface deleted before each. The cap is 8 GiB, 8,589,934,592 B.

| fields | file | seconds | peak RSS (median) | of the cap | runs |
|---:|---|---|---:|---:|---|
| n/a | W3 alone, NOT a baseline, 119 lines | 2.18 to 2.24 | 687,964,160 B | 8.01 % | `runs/w3-0..2.time` |
| **3** | **this obligation alone, 315 lines** | **3.14 to 3.33** | **740,835,328 B** | **8.62 %** | `runs/obl-0..2.time` |
| 3 | the DELIVERED file, 464 lines | 3.42 to 3.56 | 766,050,304 B | 8.92 % | `runs/full-0..2.time` |
| 9 | `[LJ-1.553]`'s obligation, HERE | 2.82 to 2.83 | 695,435,264 B | 8.10 % | `runs/rerun553-obl-0..2.time` |
| 37 | `[LJ-1.551]`'s obligation, HERE | 4.26 to 4.28 | 1,071,005,696 B | 12.47 % | `runs/rerun551-obl-0..2.time` |

**THE PANE IS COMPARABLE TO BOTH PREDECESSORS' AND I CHECKED IT RATHER THAN
ASSUMING IT.** I copied `agents/tasks/LJ-1-553/runs/Probe553.obligation-only.agda.txt`
and `agents/tasks/LJ-1-551/runs/Probe551.obligation-only.agda.txt`, renamed only
the module line, and ran both here.

- `[LJ-1.553]`'s obligation gives 695,435,264 B here against the 695,418,880 B its
  report states: a difference of 16,384 B, **0.0024 percent**.
- `[LJ-1.551]`'s obligation gives 1,071,005,696 B here, against 1,069,957,120 B on
  `[LJ-1.553]`'s pane (**0.098 percent**) and 1,067,859,968 B on its own
  (**0.295 percent**).

**Its TIME does not carry over the same way**: `[LJ-1.553]` reports 3.16 to 3.21 s
for that file and it takes 2.82 to 2.83 s here, about 12 percent faster. **So I
compare peak RSS across panes and I do not compare seconds across panes.**

### WHAT THE THREE ROWS DO AND DO NOT SETTLE

**THE RAW GAPS, ALL WHOLE-FILE PEAK RSS ON THIS PANE.** My three-field file is
**45,400,064 B (6.53 percent) ABOVE** `[LJ-1.553]`'s nine-field file. The
thirty-seven-field file is **330,170,368 B above mine** and **375,570,432 B above
the nine-field file**.

**I DO NOT CONCLUDE THAT THREE FIELDS COST MORE THAN NINE, AND THE REASON IS
`[LJ-1.551]`'s MEASUREMENT AND NOT CAUTION.** It measured peak RSS for a term-free
import header to be bimodal in two bands **136,265,728 B apart**, with the band a
file lands in NOT determined by the code it elaborates: two files whose elaborated
code normalises to the same hash sat in different bands
(`agents/tasks/LJ-1-551/lj-1.551-report.md:297-324`). **45,400,064 B is 0.33 of
that band.** Two different files cannot be separated at that resolution and I will
not pretend otherwise. The 330 MB and 375 MB gaps are each more than TWICE the
band, so THOSE are real.

**AND THE LINEAR MODEL IS NOT REFUTED EITHER, WHICH IS THE POINT.** A model linear
in field count through (9, 695,435,264 B) and (37, 1,071,005,696 B) predicts
614,955,886 B at three fields. The measurement is 740,835,328 B, an excess of
125,879,442 B, which is **0.92 of the band**. So the model is neither confirmed nor
refuted here.

**SO THE SENTENCE THE NEXT BRIEF NEEDS IS A NEGATIVE ONE: AT THIS FRONT'S SIZE, A
FIELD COUNT PREDICTS NOTHING THAT THIS PANE CAN MEASURE, AND IT WILL PREDICT
NOTHING UNTIL SOMEBODY ISOLATES `[LJ-1.551]`'s BAND.** `[LJ-1.545]` measured the
heap linear in field count (the brief's premise 8); at 3 against 9 that line is
inside the noise, and premise 8 must not be used to fund a task at this scale.

**WHAT IS VISIBLE IN THE FILE, AND IT IS A READING AND NOT A MEASUREMENT:** nine
of `[LJ-1.553]`'s fields were the SAME `EnvSupply.Fact` form at different indices,
while these three drag in `EnvSet` at a 27-cell environment, the whole `Generic`
module at a fresh `(B, ar)`, and `EnvClosure`'s four-way closure. **I did not
measure that any of those three is the cause and I do not claim it.**

**I GIVE NO PER-FIELD RATE, AND THE REASON IS A MEASUREMENT AND NOT CAUTION.** A
per-field rate needs a baseline and I have none. **The 687,964,160 B row is NOT a
baseline**: that file carries the full import header AND the W3 term, so
subtracting it measures "three fields minus one W3 term". `[LJ-1.551]` measured a
reproducible 136 MB band in whole-file peak RSS whose cause it could not isolate,
and it warns that a subtraction can be wrong by a whole band. **So a rate computed
here would be invented. I do not give one.**

**NO HEAP EVENT AT ANY AGDA RUN OF THIS TASK.** The highest row is 12.47 percent
of the cap and it is not mine; mine is 8.92 percent.

**AGAINST THE BRIEF'S ESTIMATE.** The brief estimated about 140 lines in the
probe, of which the obligation is about 30, and under 10 seconds of Agda.
Delivered: **464 lines**, of which `LastThree` is `:149-176` (28 lines) and
`Discharge` is `:226-338` (113 lines); **3.1 to 3.3 s** for the obligation-only file and
**3.4 to 3.6 s** for the delivered one. The obligation-statement estimate was right to
the line. The file estimate was low because the two generic shells that `src/`
does not carry are 29 lines by themselves and the blanket refutations are another
40. The time estimate was high.

## W2 AND W4, ANSWERED

**W2.** `LastThree` (`Probe563.agda:149-176`) states the three ONCE at a generic
`K` and a generic `γ'`. `Discharge` (`:226-338`) fills them ONCE at the same
generic carrier, and BOTH of its shells, `consK-gen` (`:267-279`) and
`someEnv-gen` (`:293-308`), are generic in the vector length AND in the slots, so
neither is written twice and neither is written in a fixed form.
`Frame` (`:361-406`) instantiates at `n = 9` in exactly one place (`:401-406`).
**No block in this file is written twice, and nothing is stated in a fixed form
that could have been stated generically.** No deadline pushed me toward a fixed
form, so there is no conflict to report. DD4's core constraint is at
`archive/dev/DD-archived.md:22`.

**THE ONE PLACE W2 IS NOT FULLY HONOURED IS NOT MINE.** `Frame` is concrete in
`lam` and `gam` because `SupplyEnv` is, and `SupplyEnv` is the tree's own
concrete-site module (`src/L/Coding/EnvSupply.lagda.md:107-112`). I did not make
it concrete and I did not make it generic; a module redesign is the
mathematician's call under AD3.

**W4.** Nothing is retired by this task and nothing moves to `archive/`, so
`dev/ARCHIVE.md` gains no row. The clause's second half asks me to price the ideal
form written fresh today against the chapter I have. **For these three the ideal
form written fresh today is `EnvSupply.Fact` with SLOT-GENERIC `consK` and
`someEnv` shells beside the pinned ones**, exactly as it already has `subK-gen`
beside `subK₁-and` and `tmValK` beside `valV`. **The measurement is in this file:
the two shells are 29 lines together, they use no lemma the tree does not already
have, and they made three fields collect that had never collected before.** I
propose no move, because C-42 says I must count the sites before I price a cure:
I counted seventeen pinned sites and six with no shell (section `THE C-42
SWEEP`), and I priced nothing.

## WHAT THE NEXT BRIEF NEEDS

1. **THE SIXTEEN ARE FOUR PROBLEMS AND THREE OF THEM ARE NOW MEASURED.** One
   supplied membership (9 fields, `[LJ-1.553]`), an environment witness plus two
   memberships (`consK-forall`, `consK-allin`, this task), one truncated numeral
   arity (`someEnv`, this task), and four memberships at binders no supply reaches
   (`valV`, `valW`, `wKfact`, `consK-exist`, still open).
2. **THE REAL SEAM IS NOT WHICH FIELD, IT IS WHERE THE ASK SITS.** A field that
   asks at a FRAME SLOT is closed by supplying that slot once, and `[LJ-1.553]`
   did it nine times over. **A field that asks at its OWN binder cannot be, and I
   refuted the blanket supply for both of my shapes**
   (`Probe563.agda:458-462`). Fourteen fields across the three records carry that
   shape and eleven are still open.
3. **THE NEXT PROBE IS THE CONDITIONED SUPPLY, AND IT IS A REFUTATION TARGET.**
   Ask whether `⟨ γ ⊨ consAtL e' x z ⟩` alone forces `z` to be an environment and
   forces `z` and `x` into `K`. If it does not, `TFacts.consK-forall` as stated is
   FALSE and the record over-asks; if it does, the extras come off for free. **I
   did not measure this and neither did anybody**: the shape is a concrete
   `consAtL` instance at a `z` outside `K`, and `consAt` is at
   `src/L/Coding/Environment.lagda.md:488-492`. D-10 says price that truth before
   pricing its proof.
4. **`someEnv` IS THE ONE FIELD WHOSE EXTRA THE MASTER ALREADY ARGUED IS
   NECESSARY.** `envSetK`'s own comment says the unrestricted form is FALSE at the
   bound (`src/L/Condensation/TwelveAgree.lagda.md:296-308`, `[LJ-1.172]`), and
   `[LJ-1.173]` restricted `envSetK` for exactly that reason. **`someEnv` was left
   unrestricted.** The cure that costs nothing is the one already taken next door:
   put the numeral restriction into `someEnvDef` itself. That is a statement
   change and it is the mathematician's, not mine.
5. **THE CELL-0 PIN IS NOW LOAD-BEARING.** `someEnv+` reads `lookup zero γ'` as
   the carrier. `[LJ-1.551]` pinned it to `SupplyEnv.B₀` and `[LJ-1.553]` said a
   later task could drop the pin
   (`agents/tasks/LJ-1-553/lj-1.553-report.md:256-258`). **It cannot be dropped any
   more.** Any frame this front lands on must pin cell 0 to the carrier.
6. **A FIELD COUNT PREDICTS NOTHING AT THIS FRONT'S SIZE.** My three-field file
   sits 45,400,064 B above `[LJ-1.553]`'s nine-field file on the same pane, and
   that gap is 0.33 of `[LJ-1.551]`'s unexplained 136,265,728 B band, so it
   settles nothing in EITHER direction (section `THE PRICE`). **Do not fund a
   task of this size against premise 8's linear-in-field-count model, and do not
   fund one against my rows either.** What is measurable at this pane's
   resolution is the 37-field row, which is more than two bands above both.
7. **A GREEN COLLECTION STILL DOES NOT PREDICT A GREEN APPLICATION.**
   `archive/dev/LJ-dispatch-index.md:137` records a union frame that checked green
   while the APPLICATION heap-walled at the 8 GB cap. **I measured a value being
   BUILT. I did not apply it to anything, and I claim nothing about applying it.**
8. **THE CONSUMERS ARE NAMED AND THEY ARE FOUR CALL SITES.** `consK-forall` goes
   to `ForallAgree` (`src/L/Condensation/UpperAgree.lagda.md:278`), `consK-allin`
   to `AllInAgree` and `ExInAgree` (`:285`, `:292`), `consK-exist` to
   `ExistAgree` (`:270`); `TFacts` passes all three through to `LFacts` at
   `src/L/Condensation/TwelveAgree.lagda.md:478-481`. **Whether a consumer can
   supply my extras at its call site is a mathematical question and it is not
   mine.**

## THE WORKING TREE

Files I created, all inside my write scope:

- `agents/tasks/LJ-1-563/Probe563.agda` (464 lines)
- `agents/tasks/LJ-1-563/lj-1.563-report.md` (this file)
- `agents/tasks/LJ-1-563/runs/` (the `.out` and `.time` pairs for every run named
  above, plus the file variants below)

I did not create `agents/tasks/LJ-1-563/review-of-last-three.md`. I did not touch
`src/`. `git status --porcelain` shows `?? agents/tasks/LJ-1-563/` and nothing
else. I did not commit and I did not push.

Agda wrote interface files under `_build/2.8.0/agda/`, which
`dev/build-manifest.toml:117-120` declares `class = "toolchain"`, so no new
lifecycle declaration is owed.

**ONE RUN IN `runs/` IS RED AND I NAME IT.** `runs/dis-try-0.out` is exit 42, a
`[ParseError]`: one unbalanced closing parenthesis in the `someEnv+` field.
`runs/dis-try-1.out` is the same file with the parenthesis removed, exit 0, and it
is the first full run of the generic discharge. **Every other run in `runs/` is
exit 0, and every stage typechecked on its first non-parse run.**
`runs/final.out` is a last forced recheck of the delivered file after the report
was written, exit 0, 3.75 s.

Every file variant I measured is kept beside its runs, so a critic can re-run any
row of the price table. The delivered file is byte-identical to
`runs/Probe563.delivered.agda.txt` (`diff -q`, checked after the last run).

| file | what it is |
|---|---|
| `runs/Probe563.w3-only.agda.txt` | the file at the W3 runs, 119 lines |
| `runs/Probe563.generic-only.agda.txt` | the file before `Frame` and `NoBlanket`, kept as the point where the generic discharge first checked |
| `runs/Probe563.obligation-only.agda.txt` | the obligation without W3, `statement-matches` or `NoBlanket`, 315 lines |
| `runs/Probe563.delivered.agda.txt` | the delivered file, 464 lines |
| `runs/Probe563.rerun553-obl.agda.txt` | `[LJ-1.553]`'s obligation-only file, module line renamed |
| `runs/Probe563.rerun551-obl.agda.txt` | `[LJ-1.551]`'s obligation-only file, module line renamed |
| `runs/fields-verbatim.txt` | the `sed` extraction of the three field types and `someEnvDef` |

I read `agents/tasks/LJ-1-551/`, `agents/tasks/LJ-1-553/` and
`agents/tasks/LJ-1-512/` and wrote nothing in any of them.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ AND USED.** `:135` reads

  > `| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |`

  This is the brief's premise 9 and it is why W3 ran first and alone. My W3
  section says the guard is STRONGER at this site than at `[LJ-1.553]`'s,
  because `[LJ-1.71]`'s hypothesis sat in a telescope and mine sit at the fields'
  own binders. `:137` reads

  > `| LJ-1.72 | Repair TwelveAgree, then consume it | STATEMENT FIXED, APPLICATION WALLS | The per-row telescope and the union frame both check green. The application heap-walls at the 8 GB cap |`

  which is item 7 of `WHAT THE NEXT BRIEF NEEDS`: I claim nothing about applying
  this value.
- **`archive/dev/JOURNAL.md`: NOT READ, declined.** `grep -c` for `TFacts`,
  `consK`, `someEnv` and `EnvSupply` returns 0, 0, 0 and 0 over its 1378 lines. It
  carries nothing about this record.
- **`archive/dev/JOURNAL-archived.md`: NOT READ, declined.** The same four counts
  over its 4280 lines are 0, 0, 0 and 0.
- **`archive/dev/PLAN-archived.md`: NOT READ, declined.** The same four counts
  over its 485 lines are 0, 0, 0 and 0. It is the archived plan and this task
  changes no plan row.
- **`dev/ARCHIVE.md`: NOT USED, declined.** The same four counts over its 299
  lines are 0. This task retires no module, so W4 has no row to write there.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`: READ AND USED.** `:289` reads

  > `1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to`

  This is the rule that settles both of my truncation eliminations without a
  detour. `someEnv`'s extra is the truncation
  `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` and I eliminate it twice: into
  `⟨ fst (Generic.envSetGen B₀ ar) ∈ Lset lam ⟩` at `Probe563.agda:394-396`, and
  into `Empty.⊥` at `:450-455`. **Both goals are propositions, so `PT.rec` applies
  and neither needed `rec→Set` or unique choice.** I checked the rule rather than
  assuming it, because the file's whole point is that a truncation is sometimes
  not eliminable.
- **`dev/literature/devlin-II5.md`: NOT USED, declined.** It is the Condensation
  Lemma and the GCH in L, the mathematics BEHIND `TFacts`. This task changes no
  statement and re-derives none; every step is either the tree's own lemma or a
  slot generalisation of one.
- **`dev/literature/digest.md`: NOT USED, declined.** It pins the orthodox form of
  the rud route, which is `[LJ-2]` territory. This task touches no rud
  construction.
- **`dev/literature/rudimentary-functions.md`: NOT USED, declined.** Rudimentary
  closure is the same `[LJ-2]` territory. My closure is `EnvClosure`, which is
  four named set operations at a level (`src/L/Coding/EnvSupply.lagda.md:672-699`)
  and not a rud function at all.
- **`dev/literature/terms-2026-08.md`: NOT USED, declined.** It is the terminology
  dossier for the owner's naming ruling. I added no `dev/glossary.toml` entry and
  I named no new term.
