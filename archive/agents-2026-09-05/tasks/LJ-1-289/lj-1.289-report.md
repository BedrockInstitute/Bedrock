# [LJ-1.289] report: land the `sucV∈` respelling on the master

STATUS: COMPLETE against the abort criterion's FIRST branch. **THE CURE LANDS
AND THE MASTER DROPS.** Written incrementally (C-22). Every negative is marked
MEASURED or INFERRED, in those words. ASD-STE100 applies.

Machine at start: load 3.79 4.76 5.29 at 16:05, 16 cores.
Zero agda processes at start, MEASURED by `ps aux | grep -iE "agda"`.
One agda process of mine at all times through the whole series.

## LEAD

**THE MASTER GOES FROM A 495.23 s THREE-RUN CONTROL MEAN TO A 6.65 s SIX-RUN
TREATED MEAN. MINUS 488.59 s. MINUS 98.66 PERCENT. The change is five inserted
lines and three deleted lines.** Exit 0 on every run, no wall, cap never
raised.

**THE WHOLE-FILE RATE CROSSES THE BAR.** The delivered master ran at
495.23 s over 833 in-fence non-blank lines, **0.5945 s per line, 56.5 times
the 0.010514 bar**. The treated master runs at 6.65 s over 835 lines,
**0.0080 s per line, 0.76 times the bar.** The file moves from the worst rate
in the wing to UNDER the bar.

**`sucV∈` IS GONE FROM THE PROFILE. MEASURED on four profiled treated runs.**
`grep -c "sucV∈"` returns **0** on `t1.out`, `t2.out`, `t5.out` and `t6.out`.
The control charges the same definition **488,760 ms of 494,425 ms, 98.85
percent** (`agents/tasks/LJ-1-289/runs/c1.out:2-4`). The new climb `δ₄∈λ`
costs **22 ms**.

**THE LANDING IS PROVEN THROUGH THE ONLY IMPORTER (C-45).**
`agda src/Everything.lagda.md`, cold in the master and in `Everything`, exits
0 in **8.02 s**. A second consumer that APPLIES the `sucK` field,
`agents/tasks/LJ-1-289/Consume.lagda.md`, exits 0 cold in **7.20 s**.

**NO CONSUMER NEEDED THE OLD SPELLING. MEASURED.** `sucV∈` is a `where`
binding inside `sucK`'s body. No signature in the file changed, and
`grep -rn "SupplyEnv" src/` outside the master returns ZERO lines.

**THE DELTA IS LARGER ON THE MASTER THAN ON THE PROBE IN SECONDS, AND SMALLER
IN PERCENT.** `[LJ-1.287]`'s probe delta was 476.15 s and 99.15 percent. The
master's is **488.59 s and 98.66 percent**. The abort branch that watches for
a smaller delta does not fire on seconds. The percent falls by 0.49 points
because the master carries about 443 lines the probe did not, and that content
is the treated file's floor.

## 0. THE CLOCK

Agda's own `--profile=definitions` Total is the figure of record. The wall
figure from `agents/tasks/LJ-1-289/measure.sh` uses `time.time()`, the
wall-clock epoch, which is comparable across processes. `time.monotonic()` is
NOT comparable on this machine (`[LJ-1.283]` section 8).

The harness targets the MASTER, `src/L/Coding/EnvSupply.lagda.md`, and deletes
`_build/2.8.0/agda/src/L/Coding/EnvSupply.agdai` before every run. Each run is
therefore cold in the master and warm in its dependencies.

## 1. MY OWN CONTROL, ON THE MASTER

`agda --profile=definitions`, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, one
agda process of mine at all times. The target is the delivered master.

`w0` is the warm-up and is DISCARDED, as the brief requires. It is recorded
here because it is evidence and it agrees with the kept runs.

| run | wall s | agda Total ms | `sucV∈` ms | share | load before to after |
|---|---:|---:|---:|---:|---|
| w0, DISCARDED warm-up | 496.09 | 495,055 | 489,374 | 98.85 percent | 4.61 to 5.25 |

`agents/tasks/LJ-1-289/runs/w0.out:2-3`.

The kept control runs are in section 3's table, beside the treated runs.

**THE CONTROL RE-DERIVES `[LJ-1.287]`'s PREMISE ON THE MASTER.** `[LJ-1.287]`
measured the probe at a 480.25 s three-run mean and charged `sucV∈` 99.32
percent. The master's warm-up run charges the SAME definition 98.85 percent.

## 2. THE EDIT

**FOUR LINES CHANGE AND TWO OF THEM ARE NEW.** The edit is `[LJ-1.287]`'s
`TreatedNoIter.lagda.md` arm, applied to the master. It changes no statement
that anything outside the `where` block can see.

| master site | before | after |
|---|---|---|
| `:210` | `Lset-mono {α = lam} {β = sucIter 4 δ}` | `Lset-mono {α = lam} {β = sucV δ₃}` |
| `:211` | `(B.suc^∈λ 4 δ δ∈)` | `δ₄∈λ` |
| after `:216` | absent | `δ₄∈λ : ⟨ sucV δ₃ ∈ lam ⟩` and `δ₄∈λ = succλ δ₃ (succλ δ₂ (succλ δ₁ (succλ δ δ∈)))` |
| `:223` | `sucV∈ : ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩` | `sucV∈ : ⟨ sucV a ∈ Lset (sucV δ₃) ⟩` |

**`sucV∈`'s BODY at `:224` does not change.** The body is
`union∈Lset-suc δ₃ ⁅ a , ⁅ a ⁆s ⁆ pair∈δ₃`, byte-identical before and after.
Only the declared level changes, from `sucIter 4 δ` to `sucV δ₃`.

**I LAND THE ARM THAT WAS MEASURED, NOT A RE-DERIVATION OF IT.** `module
SupplyEnv` in `agents/tasks/LJ-1-287/ControlEnv.lagda.md` is byte-identical to
`module SupplyEnv` in the master: `diff` of the two blocks is EMPTY. The four
edit rows above are exactly the `diff` of `TreatedNoIter.lagda.md` against that
control.

**`sucIter` and `B.suc^∈λ` STAY IN THE FILE.** `envSetK` at
`src/L/Coding/EnvSupply.lagda.md:144` still uses both, and `[LJ-1.287]`
measured it at 11 ms. The edit removes neither import.

The master goes from 833 to 835 in-fence non-blank lines, counted by
`scripts/ledger.py`'s own `count` function, which is the ledger basis.

## 3. THE TREATED RUNS

Every run is a COLD run on the master: `measure.sh` deletes
`_build/2.8.0/agda/src/L/Coding/EnvSupply.agdai` before each one. Every run
carries its own load pair. `GHCRTS="-A64m -I0 -M8g"`, cap never raised, one
agda process of mine at all times, exit 0 every run.

The arms swap by file copy. `git diff` confirms the state before each control
run is EMPTY against HEAD, and the state before each treated run is the
five-insertion, three-deletion diff of section 2.

| cycle | run | arm | wall s | load before to after | agda Total ms |
|---|---|---|---:|---|---:|
| 0 | w0 | control, **DISCARDED warm-up** | 496.09 | 4.61 to 5.25 | 495,055 |
| 1 | c1 | control | **495.64** | 5.10 to 6.27 | 494,425 |
| 1 | t1 | **treated** | **7.16** | 5.82 to 5.75 | 5,989 |
| 1 | t2 | **treated** | **6.32** | 5.75 to 5.78 | 5,818 |
| 1 | t3 | **treated** | **6.48** | 5.78 to 5.96 | not profiled |
| 2 | c2 | control | **495.97** | 11.10 to 6.33 | not profiled |
| 2 | t4 | **treated** | **6.91** | 6.21 to 6.12 | not profiled |
| 3 | t5 | **treated**, arm runs FIRST | **5.92** | 6.12 to 5.70 | 5,519 |
| 3 | c3 | control, arm runs SECOND | **494.09** | 5.33 to 4.23 | not profiled |
| 4 | t6 | **treated**, the final landed state | **7.09** | 4.48 to 4.87 | 5,891 |

`c2` started under a load of 11.10, the highest of the series. Its wall figure
is 495.97 s, inside 0.07 percent of `c1`. **MEASURED: the load spike did not
move the control.**

### 3.1 THE MEANS AND THE DELTA

- **Control, n = 3 kept**: 495.64, 495.97 and 494.09 s. **Mean 495.23 s,
  spread 0.38 percent.** The discarded warm-up `w0` at 496.09 s agrees.
- **Treated, n = 6**: 7.16, 6.32, 6.48, 6.91, 5.92 and 7.09 s. **Mean 6.65 s**,
  lowest 5.92, highest 7.16.
- **THE WHOLE-SERIES FIGURE: 495.23 s to 6.65 s, MINUS 488.59 s, MINUS 98.66
  PERCENT.**

### 3.2 THE PAIRED DELTAS, AND THE ORDER DOES NOT MOVE THEM

| cycle | order | control s | treated s | delta s | percent |
|---|---|---:|---:|---:|---:|
| 1 | control first | 495.64 | 7.16 | **minus 488.48** | **minus 98.56** |
| 2 | control first | 495.97 | 6.91 | **minus 489.06** | **minus 98.61** |
| 3 | **treated first** | 494.09 | 5.92 | **minus 488.17** | **minus 98.80** |

**MEASURED: no position effect.** Cycle 3 ran the treated arm FIRST and the
control second. Its delta is minus 98.80 percent against minus 98.56 and minus
98.61 in the two control-first cycles.

### 3.3 THE RATE AGAINST THE 0.010514 BAR

The line figures come from `scripts/ledger.py`'s own `count` function, which is
the ledger basis: non-blank lines inside ` ```agda ` fences.

| state | lines | seconds | rate, s per line | against the bar |
|---|---:|---:|---:|---:|
| delivered master, control | 833 | 495.23 | 0.5945 | **56.5x** |
| **treated master** | **835** | **6.65** | **0.0080** | **0.76x** |

`[LJ-1.276]` delivered this master at 482.73 s and 0.5795 s per line, **55.1x
the bar** (`agents/tasks/LJ-1-276/lj-1.276-report.md:84-87`). My control is
495.23 s, **2.6 percent above that figure**, and the difference is inside the
range the record has measured for a cold master.

### 3.4 THE PROBE AGAINST THE MASTER (P-l)

| quantity | `[LJ-1.287]` probe | this master |
|---|---:|---:|
| control mean | 480.25 s, n=3 | **495.23 s, n=3** |
| treated mean | 4.10 s, n=4 | **6.65 s, n=6** |
| delta, seconds | 476.15 | **488.59** |
| delta, percent | 99.15 | **98.66** |

**THE ABORT BRANCH "THE DELTA IS SMALLER ON THE MASTER" DOES NOT FIRE on
seconds: the master's delta is 12.44 s LARGER.** It fires weakly on percent:
98.66 against 99.15, a fall of 0.49 points. **INFERRED**, from the two line
counts: the master carries 835 lines against the probe's 390, and the extra
content is a floor the treated file still pays. `[LJ-1.287]` projected the
treated master at "about 25 s" and said plainly it was a PROJECTION.
**The measurement is 6.65 s, and the projection was 3.8 times too high.**

## 4. THE PROFILE, `sucV∈` GONE

Control `c1` against treated `t1`, both `--profile=definitions`, both on the
master.

| definition | control `c1` ms | treated `t1` ms |
|---|---:|---:|
| **`SupplyEnv._._.sucV∈`** | **488,760** | **not charged at all** |
| **`SupplyEnv._._.δ₄∈λ`, the new climb** | absent | **22** |
| `Fact.ConsKClosed._.e'eq` | 132 | 147 |
| `Fact.ConsK._.e'eq` | 131 | 144 |
| `SupplyEnv.someEnv` | 112 | 120 |
| `SupplyEnv._._.sub₁` | 55 | 85 |
| `Fact.ConsKClosed.consK-allin` | 69 | 77 |
| `SupplyEnv.envInK-imp` | 40 | 43 |
| Miscellaneous | 3,235 | 3,350 |
| **Total** | **494,425** | **5,989** |

`agents/tasks/LJ-1-289/runs/c1.out:2-4` and
`agents/tasks/LJ-1-289/runs/t1.out:2-20`.

**`sucV∈` DOES NOT APPEAR IN THE TREATED PROFILE. MEASURED.**
`grep -c "sucV∈" agents/tasks/LJ-1-289/runs/t1.out` returns **0**, and the same
grep on `runs/t2.out` returns **0**. Both are profiled runs.

**THE NEW CLIMB COSTS 22 ms ON THE MASTER.**
`agents/tasks/LJ-1-289/runs/t1.out:51` and `runs/t2.out:48` both read
`L.Coding.EnvSupply.SupplyEnv._._.δ₄∈λ 22ms`. **The brief's premise said 18 ms,
measured on the probe. The master's figure is 22 ms.** The difference is 4 ms
and it does not move any conclusion. P-l is answered: I re-measured at the
site rather than carrying the probe's number.

**NOTHING MOVED ELSEWHERE.** Every other definition keeps its figure to within
a few tens of milliseconds. No cost was traded away, and no new charge appears
in the treated profile above 147 ms. **MEASURED**, by reading both profiles
whole.

## 5. PREMISES, VERIFIED OR REFUTED

| the brief's premise | verdict, with evidence |
|---|---|
| `succλ` is a module parameter at `:108` and is tower-neutral | **VERIFIED.** `src/L/Coding/EnvSupply.lagda.md:108` reads `(succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)`. It names an ordinal fact about `V ℓ` and no tower |
| `succλ` is in scope at `sucK` | **VERIFIED.** `module SupplyEnv` opens at `:107` and the next top-level module, `Fact`, opens at `:448`. `sucK` is at `:204`, inside that span |
| `sucK` is a REQUIRED `EnvClosure` field at `Key.lagda.md:568` | **VERIFIED.** `src/L/Coding/Key.lagda.md:568` reads `(sucK : (a : S) → ⟨ a ∈ K ⟩ → ⟨ sucV a ∈ K ⟩)`. The master passes its own `sucK` parameter to `EnvClosure` at `src/L/Coding/EnvSupply.lagda.md:708` |
| the field's statement never mentions a chain, so the respelling is free at the interface | **VERIFIED, and it is stronger than the brief states.** The edit does not reach `sucK`'s statement at all. `sucV∈` is a `where` binding of `step`, which is a `where` binding of `sucK`'s body. `sucK`'s own type at `src/L/Coding/EnvSupply.lagda.md:204` is byte-identical before and after |
| `envSetK` is the in-file one-spelling control | **VERIFIED.** `src/L/Coding/EnvSupply.lagda.md:144` substs at `Lset (sucIter 4 σ)` and its supplier `envSetNumeral∈` concludes `⟨ fst (envSet B n) ∈ Lset (sucIter 4 σ) ⟩` at `src/L/Coding/Key.lagda.md:488`. One spelling on both sides |
| the arm I land is the arm `[LJ-1.287]` measured | **VERIFIED.** `module SupplyEnv` in `agents/tasks/LJ-1-287/ControlEnv.lagda.md` is BYTE-IDENTICAL to the same block in the master. `diff` of the two blocks is EMPTY |
| `sucV∈` vanishes from the profile after the cure, `grep -c` returns 0 | **VERIFIED on the master.** `grep -c "sucV∈"` returns **0** on all FOUR profiled treated runs: `agents/tasks/LJ-1-289/runs/t1.out`, `t2.out`, `t5.out` and `t6.out` |
| the new climb costs 18 ms | **VERIFIED IN KIND, CORRECTED IN FIGURE.** On the master the climb `δ₄∈λ` costs **22, 22, 21 and 22 ms** (`runs/t1.out:51`, `runs/t2.out:48`, `runs/t5.out:48`, `runs/t6.out:48`). The brief's 18 ms was the probe's figure. P-l: I re-measured at the site |
| control n=3 mean 480.25 s, spread 2.3 percent, on the probe | **RE-DERIVED ON THE MASTER, and the master is slower.** My control is **495.23 s, n=3, spread 0.38 percent.** The master is 3.1 percent above the probe, which is what 445 extra lines buy |
| treated n=4 mean 4.10 s, best 3.65 s, on the probe | **RE-DERIVED ON THE MASTER, and the master is slower.** My treated mean is **6.65 s, n=6, best 5.92 s** |
| `sucV∈` carries about 99 percent of the control | **VERIFIED.** 488,760 ms of 494,425 ms, **98.85 percent**, at `agents/tasks/LJ-1-289/runs/c1.out:2-4`. The warm-up agrees at 98.85 percent |

## 6. THE CONSUMERS

**NO CONSUMER NEEDS THE OLD SPELLING. MEASURED, by my own greps, not by
trusting `[LJ-1.287]`'s (C-44).**

**FIRST, THE EDIT CHANGES NO STATEMENT ANY CONSUMER CAN SEE.** `sucV∈` is a
`where` binding of `step`, and `step` is a `where` binding of `sucK`'s body at
`src/L/Coding/EnvSupply.lagda.md:205-206`. Neither name is exported. `sucK`'s
own type at `:204` is byte-identical before and after the edit, and so is
every other signature in the file: `git diff` touches only lines `:210`,
`:211`, `:217-218` (new) and `:223`, all inside that `where` block.

**SECOND, THE MASTER HAS EXACTLY ONE CONSUMER.**

| grep | result |
|---|---|
| `grep -rn "L\.Coding\.EnvSupply" src/` | TWO lines: `src/L/Coding/EnvSupply.lagda.md:17`, the master's own header, and `src/Everything.lagda.md:382`, `import L.Coding.EnvSupply` |
| `grep -rn "EnvSupply" src/` outside the master | ONE line: `src/Everything.lagda.md:382` |
| `grep -rn "SupplyEnv" src/` outside the master | **ZERO lines. MEASURED** |
| `git grep -n "L\.Coding\.EnvSupply"` over the whole tree | the two `src/` lines above, plus prose in `agents/tasks/LJ-1-276/`, `LJ-1-283/` and `LJ-1-287/` reports, and my own run log. **No probe imports the master. MEASURED** |

`src/Everything.lagda.md:382` is a bare `import L.Coding.EnvSupply`. It names
no field, so it cannot depend on `sucV∈`'s spelling.

**THIRD, THE INTERFACE FIELD IS NOT REACHED BY THE EDIT.**
`src/L/Coding/Key.lagda.md:568` declares
`(sucK : (a : S) → ⟨ a ∈ K ⟩ → ⟨ sucV a ∈ K ⟩)` as a required parameter of
`module EnvClosure`. The master supplies it through `module SupplyMerge`'s own
`sucK` parameter at `src/L/Coding/EnvSupply.lagda.md:702`, opened at `:708`.
**Neither statement mentions a successor chain, a `sucIter` or a depth.** The
abort branch "THE INTERFACE FIELD WILL NOT TAKE THE NEW SPELLING" therefore
does not fire, and I did not edit `src/L/Coding/Key.lagda.md`.

**C-40 IS ANSWERED BY SECTION 7, not by this section.** A grep proves who could
break. Only a run proves that nothing did.

## 7. THE RE-RUN THAT PROVES THE LANDING (C-45)

**AN `exit 0` ON THE MASTER IS NOT A SUPPLY.** I ran TWO consumers, both cold
in the master, after the cure was in place.

| consumer | what it does | wall s | exit | load before to after |
|---|---|---:|---:|---|
| **`src/Everything.lagda.md`** | the ONLY tracked importer of the master | **8.02** | **0** | 3.37 to 3.39 |
| **`agents/tasks/LJ-1-289/Consume.lagda.md`** | imports the master, instantiates `module SupplyEnv` and APPLIES `sucK` | **7.20** | **0** | 3.38 to 3.43 |

Both runs deleted `_build/2.8.0/agda/src/L/Coding/EnvSupply.agdai` first, and
the `Everything` run deleted `_build/2.8.0/agda/src/Everything.agdai` too. Both
logs show `Checking L.Coding.EnvSupply` as a nested line, so the master was
rebuilt inside the consumer's own run.
`agents/tasks/LJ-1-289/runs/everything.out` and
`agents/tasks/LJ-1-289/runs/consume-cold.out`.

**`Consume.lagda.md` IS THE STRONGER PROOF.** It writes
`useSucK : (a : V ℓ) → ⟨ a ∈ Lset lam ⟩ → ⟨ sucV a ∈ Lset lam ⟩` and defines
it as `SE.sucK`, and it applies the field at an argument in `sucOfEmpty`. So
the field is read from the interface AT ITS DECLARED TYPE and used. **The
respelling is invisible to it. MEASURED.**

**BEFORE THE CURE, THE SAME `Everything` RUN COST ABOUT 496 s.** The importer
now costs 8.02 s. That is the landing, measured at the consumer and not at the
author's own file (C-40).

I did NOT run `make check`. The brief forbids it. **The consumer closure of
this master is exactly one file**, and I ran it.

## 8. DD4, WITH ITS AXIS

**AXIS NAMED (C-46): DD4's own axis is AC-against-GCH**, the axis
`scripts/ledger.py` computes from `reuse.ac_root` and `reuse.gch_root`, and the
axis `dev/ledger.toml` declares.

**THE CURE MOVES THE RATIO BY ZERO, AND I DO NOT JUSTIFY IT BY DD4.**
`src/L/Coding/EnvSupply.lagda.md` is a LEAF: no master imports it, only
`src/Everything.lagda.md:382` names it. It therefore sits in neither trophy's
import closure, and `scripts/ledger.py --reuse` classes it "ambiguous", which
the report folds into "shared" for the LINE accounting only. `[LJ-1.276]`
measured the block NEUTRAL on this axis
(`agents/tasks/LJ-1-276/lj-1.276-report.md:124`). The cure changes no import
and no closure, so the classification is unchanged.

**ON REUSE, THE BRIEF'S CLAIM HOLDS AFTER MY EDIT. MEASURED at `file:line`.**

- **The cure REMOVES a supplier and ADDS none.** It deletes
  `B.suc^∈λ 4 δ δ∈` from `sucK`'s `step` and puts four direct applications of
  `succλ` in its place. `succλ` is a PARAMETER of `module SupplyEnv` at
  `src/L/Coding/EnvSupply.lagda.md:108`, with type
  `(d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩`. **That names an ordinal fact
  about `V ℓ` and no tower, so it is tower-neutral.** A second tower that
  supplies `succλ` supplies this step unchanged.
- **It imports nothing new.** `git diff` adds no import line. The two imports
  the old spelling used, `L.Ordinal.StageArith`'s `sucIter` at `:75` and
  `L.Coding.Bound`'s `module Bound` at `:46`, both STAY, because `envSetK` at
  `src/L/Coding/EnvSupply.lagda.md:144` still uses `sucIter 4 σ` and
  `B.suc^∈λ 4 σ σ∈λ`. **So the file's supplier set is unchanged at the file
  level and reduced at the SITE.**
- **It proves nothing new.** `sucV∈`'s body at `:226` after the edit is
  byte-identical to `:224` before it.
- **It is written generic in the sense DD4 means**, because the climb now rests
  on the module's own abstract parameter rather than on a numeral iterate that
  the stage-arithmetic module defines.

**THE 55-LINE `union∈Lset-suc` DUPLICATE IS NOT BUNDLED (P-q).**
`[LJ-1.287]` measured that duplicate across `src/L/Coding/Key.lagda.md:504-560`
and `src/L/Coding/EnvSupply.lagda.md:148-202`, and priced the local copy's
whole family under 100 ms. **A line lever and a seconds lever are different
levers**, so I left it alone. I also left `src/L/Coding/Key.lagda.md:424-429`
alone: it is `[LJ-1.287]`'s C-42 sweep candidate and it is not this task.

## 9. THE ABORT CRITERION, ANSWERED BRANCH BY BRANCH

| branch, fixed before the run | verdict |
|---|---|
| **IT LANDS AND THE MASTER DROPS** | **FIRED.** 495.23 s to 6.65 s, minus 488.59 s, minus 98.66 percent. `sucV∈` gone from four profiled runs. The rate crosses the bar, 56.5x to 0.76x |
| A CONSUMER NEEDS THE OLD SPELLING | **DID NOT FIRE. MEASURED FALSE.** The master has ONE importer, `src/Everything.lagda.md:382`, and it names no field. `grep -rn "SupplyEnv" src/` outside the master returns zero lines. Both consumers exit 0 |
| THE INTERFACE FIELD WILL NOT TAKE THE NEW SPELLING | **DID NOT FIRE. MEASURED FALSE.** The edit never reaches `sucK`'s statement. `src/L/Coding/Key.lagda.md:568` is untouched and unread by the change |
| THE DELTA IS SMALLER ON THE MASTER THAN ON THE PROBE | **DID NOT FIRE ON SECONDS**, where the master's delta is 12.44 s LARGER. **PARTLY FIRED ON PERCENT**, 98.66 against 99.15. Both figures are reported in section 3.4 |
| A WALL | **DID NOT FIRE. MEASURED.** Longest run 496.09 s, far under the 30-minute wall. Exit 0 on every run. No heap exhaustion. Cap `-M8g`, never raised |

## 10. WHAT THIS ADDS TO THE RECORD

**C-50 IS CONFIRMED AT THE LANDING, not only at the diagnosis.** The profile
was the instrument at both ends: `[LJ-1.287]` used it to find the term, and I
used it to prove the term is gone. **A wall figure alone would not have shown
that `sucV∈` vanished rather than moved**, which is exactly the failure
`[LJ-1.283]`'s void seal hid until `[LJ-1.287]` profiled it.

**THE PROPOSED LAW IN `[LJ-1.287]` SECTION 9 NOW HAS A MASTER-SIDE
MEASUREMENT.** The rule as proposed says a stage iterate at a numeral depth and
the explicit chain it reduces to are ruinous to convert against each other. On
the delivered master the mixed spelling costs **488,760 ms of a 494,425 ms
file**, and removing it costs five inserted lines. **The orchestrator assigns
the ID.** I add no new law and I claim none.

**A PROJECTION IS NOT A PRICE, AND THIS ONE WAS 3.8 TIMES TOO HIGH.**
`[LJ-1.287]` projected about 25 s for the treated master and labelled the
figure a PROJECTION. The measurement is 6.65 s. The label was correct and the
number was not, which is DD8 working as intended.

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-287/lj-1.287-report.md`, read WHOLE as the brief
  requires.** ONE line: `:417-423`, section 4.5's four-row landing edit.
  **TAKEN:** the exact edit, applied unchanged to the master. **NOT TAKEN:**
  its "about 25 s" projection at `:432`, which I measured at 6.65 s.
- **`agents/tasks/LJ-1-287/TreatedNoIter.lagda.md` and `ControlEnv.lagda.md`,
  the arm files.** ONE line: `TreatedNoIter.lagda.md:218`,
  `δ₄∈λ = succλ δ₃ (succλ δ₂ (succλ δ₁ (succλ δ δ∈)))`. **TAKEN:** the arm
  verbatim, and the proof that I land the arm that was MEASURED: `module
  SupplyEnv` in `ControlEnv.lagda.md` is byte-identical to the master's block,
  so the probe's diff is the master's diff.
- **`agents/tasks/LJ-1-283/lj-1.283-report.md`.** ONE line: `:235`, the
  `SupplyEnv._._.sucV∈` row at 475,710 ms. **TAKEN:** the earliest localization
  of the charge, as the third independent measurement of the same site.
  **WHAT I DID NOT TAKE:** its two void arms. I built neither, because
  `[LJ-1.287]` priced both.
- **`agents/tasks/LJ-1-276/lj-1.276-report.md`.** ONE line: `:84`, "delivered
  master, cold elapsed 482.73 s, exit 0". **TAKEN:** the delivered baseline
  that my 495.23 s control reproduces to within 2.6 percent, and the 833-line
  figure and the 55.1x rate that my 0.76x replaces.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY and never a claim.** ONE line:
  `:209`, `[L3.32-T180]`, "LANDED, net -83 lines; Bridge cold falls 55 s
  (-34%); 64 signatures byte-identical". **TAKEN AS SHAPE:** a landing is
  proven by the CONSUMER's cold time falling while the signatures stay
  identical, which is section 7's design. **WHAT WOULD NOT TRANSFER:** the
  55 s and the 34 percent price a retired tree, and P-l forbids carrying them
  here. I carried none.
- **`dev/LESSONS.md` R-40, FULL entry at `:929`.** **TAKEN:** the cure, "climb
  by small closures", which is the landed edit. **NOT TAKEN:** its stated
  mechanism, depth, which `[LJ-1.287]`'s `v5` refuted.
- **`dev/LESSONS.md` C-40, FULL entry at `:3620-3656`.** **TAKEN:** "check a
  consumer before you believe the green". Section 7 is that check. **NOT
  TAKEN:** its `make check` instruction, which this brief forbids; the master
  has exactly one importer and I ran it.
- **`dev/LESSONS.md` C-45, FULL entry at `:3915`.** **TAKEN:** "`exit 0`
  separates them not at all", which is why `Consume.lagda.md` applies the field
  rather than only importing the module. **NOT APPLICABLE:** its own subject,
  an assumed equation in a telescope. Neither the master's telescope nor my
  probe's carries one.
- **`dev/LESSONS.md` C-46, FULL entry at `:3980`.** **TAKEN:** name the axis.
  Section 8 names AC-against-GCH.
- **`dev/LESSONS.md` P-q, FULL entry at `:2651`.** **TAKEN:** the reason I did
  NOT bundle the 55-line `union∈Lset-suc` dedup into this task.

## LITERATURE USED (DD18)

Nothing in the literature governs elaboration cost.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

**THE ONE `src/` EDIT.** `src/L/Coding/EnvSupply.lagda.md`, five insertions and
three deletions, all inside `sucK`'s `where` block. `git diff --stat` reads
`1 file changed, 5 insertions(+), 3 deletions(-)`. The file is 835 in-fence
non-blank lines, up from 833. **The landed state is the TREATED state**, and
`t6` is its cold measurement.

Everything else I wrote is in `agents/tasks/LJ-1-289/`:

- `LJ-1.289.md`, the pinned brief, written FIRST from the dispatch.
- `lj-1.289-report.md`, this file, written early and filled incrementally.
- `measure.sh`, `[LJ-1.287]`'s harness with the probe path replaced by the
  master path.
- `Consume.lagda.md`, the C-45 consumer probe. GREEN, exit 0, cold in 7.20 s.
- `timings.csv` and `runs/`, ten agda runs plus the two consumer runs.

**GATES I RAN.** `scripts/lint-agda.py --check` exits 0 on the master and on
the probe. `scripts/lint-prose.py --check` exits 0 on the master and on every
file I wrote. `scripts/check-probes.py --check` reads "clean (2369 tracked
files, no probe outside agents/tasks/ and no generated file)".
`scripts/ledger.py --check` reads "declaration clean". **No em dash in
anything I wrote.**

**WHAT I DID NOT TOUCH.** No `src/Everything.lagda.md`, no `dev/ledger.toml`,
no `dev/PLAN.md`, no `src/L/Choice/Name.lagda.md`, no
`src/L/Coding/Key.lagda.md`. No file under any other `agents/tasks/`
directory. I did not run `make check`. No commit, no push, no `git checkout .`,
no stash, no reset, no clean.

**THE ARM SWAPS USED A FILE COPY, NEVER A DESTRUCTIVE GIT COMMAND.** I wrote
the control text with `git show HEAD:src/L/Coding/EnvSupply.lagda.md` into a
scratchpad file outside the repository, and copied the two versions in and out
with `cp`. `git diff` verified the state before every run.

**SIBLINGS ARE LIVE AND I TOUCHED NONE.** `git status` shows
`agents/tasks/LJ-1-290/`, `agents/tasks/LJ-1-292/lj-1.292-report.md` and
`agents/tasks/LJ-1-223/LJ-1.223.md` as untracked. **None of those three is
mine.** A commit landed during my series, `f2cfa93`, which tracked my brief,
`measure.sh`, `timings.csv` and `runs/w0.out`. **I did not make it.**

**AGDA HYGIENE.** `GHCRTS="-A64m -I0 -M8g"` on every invocation, cap NEVER
raised. One agda process of mine at all times, MEASURED by
`ps aux | grep -c "[a]gda"`, which read 0 before the series and 0 after it.

**FOURTEEN agda invocations in total, and THIRTEEN exited 0.** Ten are the
timed runs in `timings.csv`. Three are consumer runs: `Consume` warm,
`Consume` cold and `Everything` cold. **ONE FAILED and it was mine, not the
master's:** the first `Consume.lagda.md` attempt raised `[NotInScope] ω`,
because I had not copied the master's `open InfinitySet using ( ω )` at
`src/L/Coding/EnvSupply.lagda.md:85`. I added `ω` to the probe's own open and
it exits 0. **No timed run failed.** Zero heap walls, zero postulates, zero
holes, `--safe --guardedness` throughout.
