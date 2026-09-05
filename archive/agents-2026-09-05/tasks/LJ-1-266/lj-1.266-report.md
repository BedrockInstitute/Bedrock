# LJ-1.266 report: what step 6 costs in SECONDS inside Condensation

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

**STATUS: COMPLETE. THE ANSWER IS "ABOVE 0.0198", AND IT IS NOT CLOSE.**

## 0. LEAD

**THE CONTROL'S ELAPSED SECONDS, THEN THE TREATED, THEN THE MARGINAL RATE.**

| arm | what it is | elapsed (mean, cold) | in-fence lines | marginal |
|---|---:|---:|---:|
| **control** | `Condensation.lagda.md` copied, module renamed | **137.36 s** (n=3) | 6,718 | — |
| **fact** | control + the twelve tower-neutral fields + the env closure + three `consK-*` | **147.64 s** (n=3) | 7,007 | **10.3 s / 289 lines = 0.036 s/line** |
| **env** | control + `envSetK` + `sucK` + `union∈Lset-suc` + the collapsed five `envK-*` + four `envInK-*` + `someEnv` | **998.21 s** (n=3) | 7,080 | **860.9 s / 362 lines = 2.38 s/line** |
| **full** | control + ALL of the above + the finite-supremum merge | **HEAP WALL** | 7,523 | **does not typecheck at -M8g** |

**Step 6 is NOT one block with one rate. It is two blocks with two rates, and
the expensive one is the env supply.** The fields land at 0.036 s/line (1.8x
the chapter's own 0.0198, 3.4x the 0.010514 bar). The env supply lands at
**2.38 s/line — 120x the chapter's rate, 226x the bar**. And the whole block
together heap-exhausts at the `-M8g` cap, so the full landing does not
typecheck at all on the standard bound.

**Which world: ABOVE 0.0198, decisively, and not by a little.** The env supply
alone adds about **861 seconds** to the chapter's ~137 s. Landing step 6 as
measured grows the wing's 60.0 s gap by roughly **861 s** (the env supply)
plus **10 s** (the fields), not shrinks it — and the full block cannot land
at the standard cap at all.

The control number is reported FIRST, then the treated, then the marginal, as
the brief orders.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at all times, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
No run passed 30 minutes (the longest kept run was the env arm at ~16.6
minutes; the heap wall was interrupted by the cap itself at ~17.8 minutes).
Load is recorded beside every run in `runs/series.log` and in section 3.

The machine carries the standing background (GF-Trader, Warp, Bitcoin-Qt,
WindowServer) that `dev/ledger.toml` and `[LJ-1.218]` already record. Load
spiked during the session (up to 88 in the minute after the heap wall's GC
thrash) and decayed back toward 6 to 14 for the kept series. Every figure
below carries its load.

## 2. THE ARMS

**All four files live in `agents/tasks/LJ-1-266/`, tracked, never near
`src/`.** Each is `src/L/Condensation.lagda.md` copied byte-for-byte with ONE
line changed: the module header. The content is appended as additional code
fences inside the same module, which is the only way Agda accepts multiple
content blocks in one file (a second top-level module is refused by
`[DeclarationsAfterTopLevelModule]`).

The content was transcribed from the six probes, composed into the master's
own structure. Two conversions were required, and they are the axis the DD4
section answers:

- **`CS.S` → `S`.** The probes open `hPropStructure 𝒮ᵥ` and name the
  L-structure `CS`; the master opens `hPropStructure 𝒮ʟ`, so `S` already IS
  the L-carrier and the ambient carrier is `V ℓ` with Cubical `_∈_`.
- **`_⊨ᵐ_` → `_⊨_`.** The master renames `AbsL`'s satisfaction to `_⊨_`.

One transcription defect was found and fixed: `_⊎_` is not an infix operator
in this scope and must be written `Sum.⊎` (the probes do exactly that).
`ω` had to be added to the `InfinitySet` import.

**The control typechecks, MEASURED exit 0.** **The fact arm typechecks,
MEASURED exit 0.** **The env arm typechecks, MEASURED exit 0.** **The full arm
does NOT typecheck: MEASURED "Heap exhausted" at 8,192 MB, exit 251.**

## 3. THE MEASUREMENT

Instrument: cold `agda` (the module's own `.agdai` removed before each run),
warm dependencies, `GHCRTS="-A64m -I0 -M8g"`, wall seconds from `time.monotonic`,
ONE process, alternating arms. The first run of each arm was a discarded
warm-up. The harness is `agents/tasks/LJ-1-266/measure.py`; raw output in
`runs/series.log`.

| run | arm | wall (s) | load before → after | exit |
|---|---:|---:|---|
| C.warmup (discarded) | control | 143.36 | 30.57 → 11.11 | 0 |
| E.warmup (discarded) | env | 1005.18 | 10.51 → 8.46 | 0 |
| F.warmup (discarded) | fact | 154.07 | 80.11 → 14.89 | 0 |
| C1 | control | 138.15 | 4.94 → 7.09 | 0 |
| E1 | env | 997.45 | 7.09 → 6.09 | 0 |
| F1 | fact | 147.48 | 6.09 → 5.65 | 0 |
| C2 | control | 136.46 | 5.65 → 6.50 | 0 |
| E2 | env | 996.17 | 6.50 → 6.63 | 0 |
| F2 | fact | 147.51 | 6.63 → 4.96 | 0 |
| C3 | control | 137.48 | 4.96 → 5.40 | 0 |
| E3 | env | 1001.00 | 5.40 → 5.45 | 0 |
| F3 | fact | 147.92 | 5.45 → 7.03 | 0 |

| arm | mean | own spread |
|---|---:|---:|
| control | **137.36 s** | 1.2% |
| env | **998.21 s** | 0.5% |
| fact | **147.64 s** | 0.3% |

Raw evidence: `runs/series.log` (the harness prints load beside every run).

**Where the env seconds live, MEASURED from `--profile=internal`
(`runs/env.warmup.txt`).** The env arm's 1,003 s total is 933 s of `Typing`,
and inside that **879 s is `Typing.CheckRHS`** — the conversion checker working
the proof BODIES, not the field signatures. The control's own `CheckRHS` is
35.1 s. So the whole env marginal is the bodies: `union∈Lset-suc`'s
extensionality argument and `someEnv`'s `EnvSet`/`Generic.Holds`
instantiation, the two terms `[LJ-1.261]` and `[LJ-1.257]` already priced as
the expensive class. This is P-m (instantiation is the expensive class) and
P-t (an average hides the term): the 2.38 s/line is concentrated in two
bodies, not spread over the 362 lines.

## 4. THE ONE NUMBER

**The marginal seconds per line, per block, and the resulting whole-file rate.**

| quantity | figure | basis |
|---|---:|---|
| control, whole file | **137.36 s / 6,718 lines = 0.0204 s/line** | n=3 |
| fact marginal | **10.3 s / 289 lines = 0.036 s/line** | n=3 paired |
| fact, new whole-file rate | **147.64 s / 7,007 lines = 0.0211 s/line** | n=3 |
| env marginal | **860.9 s / 362 lines = 2.38 s/line** | n=3 paired |
| env, new whole-file rate | **998.21 s / 7,080 lines = 0.141 s/line** | n=3 |
| the full landing | **does not typecheck at -M8g (heap wall)** | MEASURED |

**Against 0.0198:** the fields push the chapter from 0.0204 to 0.0211
(above, barely); the env supply pushes it to 0.141 (6.9x the chapter, and
the chapter was already the expensive one). **Against the 0.010514 bar:** the
fields land at 3.4x the bar; the env supply at 226x the bar.

**Which world:** ABOVE 0.0198. The 60.0 s gap grows on the day of the landing
by roughly **861 s** from the env supply alone (the fields add ~10 s more, and
the full block does not land at all at the standard cap).

## 5. NOISE AND THE REVERSED SECOND SERIES

**The env effect sits nowhere near the noise.** 860.9 s of marginal seconds
against a control of 137.36 s is a 6.3x multiple; the within-series spread
(0.5 to 4.0 percent, ~0.7 to 5.5 s at this size) and even the between-series
12.8 percent (~17.6 s) are each two orders of magnitude below the effect. The
env arm's own spread is 0.5 percent. A reversed second series cannot move a
6.3x separation.

**The fact effect is real and outside the within-series band, measured.**
10.3 s on a 137.36 s base is 7.5 percent. The within-series spread of the
control arm is 1.2 percent (1.7 s) and of the fact arm 0.3 percent (0.4 s),
so the 10.3 s delta is 6x the control arm's own swing and 23x the fact arm's.
It sits ABOVE the 0.5-to-4.0 percent within-series band and BELOW the 12.8
percent between-series figure, which is exactly why the brief prescribes the
within-series paired design rather than a between-series comparison. The run
order was a three-arm rotation C-E-F repeated three times, so each arm is
sampled across the whole window and first-order drift is canceled by design;
the control and fact runs are interleaved, not blocked. **No reversed second
series was needed**: the effect is outside the within-series band, not inside
it.

**The heap wall is not noise and not a timing artifact.** `agda: Heap
exhausted; Current maximum heap size is 8589934592 bytes` is the cap doing
its job (C-12). It is a wall, reported as such.

## 6. DD4 AND THE AXIS

**Maximize the code the two proofs share, and write it generic.**

**Does "paid once" hold for the whole added block? NO.** It holds for the
fields; it does NOT hold for the env supply, which is the concrete L site and
not the `(K, Ktr)` form. The two blocks split cleanly on that line, which is
the same line the two rates split on.

- **The fields (fact arm) are paid once, and `[LJ-1.258]` already measured
  it.** All twelve plus the closure are stated over `(K, Ktr)` from the first
  line; none names a tower or a concrete slot. The J tower re-instantiates
  `Fact` unchanged. **The 10.3 s is paid ONCE for both towers.**
- **The env supply (env arm) is the concrete-site special case, not the
  general form.** `[LJ-1.257]` section 6 named this itself: `envK-gen` and
  `envInK-gen` carry `qb : lookup bi γ ≡ B₀`, pinning the carrier to the
  concrete `B₀ = LsetS gam ordγ`. The general form replaces `qb` with the
  `TFacts` `envSetK` field. **So the 860.9 s I measured is the concrete-site
  price; the general form that actually lands may differ, and I mark that
  difference INFERRED, not measured.**
- **The one genuinely new L-row in the env block, `union∈Lset-suc`, is
  tower-neutral.** It is an ordinal closure fact over `(lam, ordλ, succλ,
  ∅∈λ)` and names no tower, so it too is paid once. `[LJ-1.261]` measured the
  same shape as an unpriced L-row and recorded that its first form walled;
  the cured form is what I transcribed.
- **The axis.** This phase mixes the two axes `[LJ-1.262]` separated: the
  fields sit on the Def-against-J axis (tower-neutral, paid once), while the
  env supply sits on the L-against-ambient axis (it is the concrete
  L-instantiation of the generic machine supply). **No figure here says which
  axis the seconds attach to; the measurement is on the concrete site.**

## 7. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the copy typechecks (control) | **MEASURED TRUE**, exit 0 |
| the fields compose green into the master | **MEASURED TRUE**, exit 0, 147.64 s |
| the env supply composes green into the master | **MEASURED TRUE**, exit 0, 998.21 s |
| the full step-6 block composes green | **MEASURED FALSE.** "Heap exhausted" at 8,192 MB |
| the marginal rate is one number | **MEASURED FALSE.** two blocks, 0.036 and 2.38 s/line |
| landing step 6 moves the wing toward the bar | **MEASURED FALSE.** ABOVE 0.0198 on both blocks |
| the env content is cheap like the fields | **MEASURED FALSE.** 67x the fields' marginal rate |
| a wall occurred | **MEASURED TRUE.** the full arm heap-exhausted at -M8g |
| I raised the cap | **MEASURED FALSE.** -M8g throughout |
| I edited a master | **MEASURED FALSE.** only `agents/tasks/LJ-1-266/` written |
| I ran `make check` | **MEASURED FALSE.** reserved for the orchestrator |
| the general (non-concrete-site) form costs the same 2.38 s/line | **INFERRED**, not measured |

## 8. CHECKERS

| checker | result |
|---|---|
| `scripts/lint-prose.py --check` | exit 0 |
| `scripts/lint-agda.py --check` | exit 0 |
| `scripts/check-probes.py` | clean (2,225 tracked files, no probe outside `agents/tasks/`) |
| `make check` | NOT RUN, the orchestrator runs it |
| agda | ONE process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised |

`git status --porcelain` shows only `agents/tasks/LJ-1-266/` as my
contribution (plus a sibling's pre-existing `LJ-1-274` and `LJ-1-223`
entries, which I did not touch). No master is modified.

## 9. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-218/lj-1.218-report.md`, read WHOLE. **Line read `:1-40`:**
  the per-master table giving Condensation 132.28 s at 0.0198 and the four
  Condensation masters 151.90 s; the 82-percent-on-65-percent finding.
- `agents/tasks/LJ-1-209/lj-1.209-report.md`, read WHOLE. **Line read `:47`**
  (`section 3.1`): the within-series paired design that resolved an 83 ms
  effect, which is my method.
- `agents/tasks/LJ-1-214/lj-1.214-report.md`, read WHOLE. **Line read `:1-30`:**
  the 8.2 s lives in the telescope component's existence, so the step-6
  content's cost is not to be confused with that term.
- `agents/tasks/LJ-1-254/`, `LJ-1-255/`, `LJ-1-257/`, `LJ-1-258/`, `LJ-1-259/`,
  `LJ-1-261/`: read WHOLE. **Line read per file:** `lj-1.254-report.md:50`
  (`union∈Lset-suc` adapted from `mkUnion`); `ProbeLJ1255.agda:354` (the
  five envK-* before collapse); `lj-1.257-report.md:26` (the 67-line collapse);
  `lj-1.258-report.md:45` (the four groups); `ProbeLJ1259.agda:118`
  (`finSetK`'s exact type); `ProbeLJ1261.agda:1-148` (the cured merge).
- `archive/dev/TASKS-archived.md`: SURVEYED, NOT USED. **Line read `:10`**
  (the shape note). The retired route holds no seconds-per-line figure for a
  step-6 supply, because it never built one at a fixed level.

## 10. LITERATURE USED (DD18)

Nothing in the literature governs elaboration cost.

## 11. THE FILES

All under `agents/tasks/LJ-1-266/`, tracked, never near `src/`.

| file | what it is |
|---|---|
| `lj-1.266-report.md` | this report |
| `CondensationControl.lagda.md` | the control arm: the master copied, module renamed |
| `CondensationFact.lagda.md` | control + the tower-neutral fields + closure |
| `CondensationEnv.lagda.md` | control + the env supply (the expensive block) |
| `CondensationStep6.lagda.md` | control + ALL content (heap-exhausts) |
| `step6-content.md`, `fact-content.md`, `env-content.md` | the content sources |
| `measure.py` | the cold paired harness |
| `runs/` | every raw profile and `series.log` |
