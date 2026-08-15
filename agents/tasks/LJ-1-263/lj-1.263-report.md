# LJ-1.263 report: land the three L-rows into `src/L/Coding/Key.lagda.md`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
A master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**All three landed, and `src/L/Coding/Key.lagda.md` is GREEN.** MEASURED,
exit 0, three kept runs.

| lemma | landed at | probe source |
|---|---|---|
| `union∈Lset-suc` | `src/L/Coding/Key.lagda.md:504` | `ProbeLJ1254.agda:117-118` |
| `envConsK` (with `prK`, `numK`, `env-entry`, `giK`) | `src/L/Coding/Key.lagda.md:566-606` | `ProbeLJ1259.agda:114-117` |
| `union2∈λ`, `merge2`, `finSup`, `finSetK` (the merge) | `src/L/Coding/Key.lagda.md:615-772` | `ProbeLJ1261.agda:161-241` |

**The home is checked, and it is right.** All three are L-hierarchy
level-closure facts, neighbours of the two the brief named: `Lset-fin`
(`:130-135`) and `paramEnv∈` (`:104-111`). None belongs anywhere else.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run past
20 minutes. No heap exhaustion. No kill.

| file | exit | cold real s | cold user s | warm real s | warm user s |
|---|---:|---:|---:|---:|---|
| `src/L/Coding/Key.lagda.md` | 0 | 5.17 | 4.17 | 1.64-2.44 | 1.47-1.49 |
| `ReRun1254.agda` | 0 | 442.86 | 439.48 | 2.44 | 1.41 |
| `ReRun1259.agda` | 0 | 1.91 | 1.73 | — | — |
| `ReRun1261Closure.agda` | 0 | 1.77 | 1.58 | — | — |

The master's warm figure is the mean of three kept runs (user 1.47, 1.49,
1.47). `ReRun1254`'s cold 442.86 s is the known satisfaction-at-a-concrete-
carrier cost (P-m/P-n), the same ~7 minutes `[LJ-1.261]` recorded for
re-deriving `union∈Lset-suc` at the concrete site; its warm run is 2.44 s.

## 2. LINES ADDED

`git diff --numstat src/L/Coding/Key.lagda.md`: **314 insertions, 6
deletions, net +308 lines** (wc basis; the 6 deletions are the import lines
replaced). DD8 caliber, non-blank lines inside the ```agda fence: **408
before, 690 after, +282**. The 26-line gap is the header comments and the
blank separators.

## 3. THE RE-RUNS AGAINST THE MASTER (C-45)

Three new files under `agents/tasks/LJ-1-263/` re-run the three probes with
their own copies removed, importing the master's versions. All exit 0.

- **`ReRun1254.agda`** = `ProbeLJ1254.agda` minus its local
  `union∈Lset-suc`; imports `union∈Lset-suc` from `L.Coding.Key`
  (`open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈;
  union∈Lset-suc )`). `envSetK` and `sucK` unchanged. exit 0.
- **`ReRun1259.agda`** = `ProbeLJ1259.agda` minus its local `prK` and
  `EnvClosure`; imports `module EnvClosure` from `L.Coding.Key` and opens
  `EnvClosure (fst K) Ktr numK0 sucK pairK finSetK`. The three `consK-*`
  sit unchanged on the master's `envConsK`. exit 0.
- **`ReRun1261Closure.agda`** = `ProbeLJ1261Closure.agda` with `finSetK`
  from the master's `FiniteSup` (not `P1261.Supply`), `envConsK` via
  `ReRun1259`, `sucK` via `ReRun1254`. `ConsKClosed` instantiates with
  `(B.#∈Tλ 0) S1254.sucK B.pr∈λ finSetK`. exit 0.

## 4. CONSUMERS (C-40)

**The only `src/` consumer of `L.Coding.Key` is `src/Everything.lagda.md:351`
(`import L.Coding.Key`).** MEASURED by grep: the string `L.Coding.Key`
appears in `src/` only at `Everything.lagda.md:351` and in `KeyRead.lagda.md`
as its OWN module name (`:10`), not an import.

The landing is **purely additive**: three new top-level names
(`union∈Lset-suc`, `EnvClosure`, `FiniteSup`) are added; no existing export
is removed, renamed, or re-typed. So the consumer cannot break. MEASURED
TRUE for the master (exit 0); the `Everything` re-wire is the orchestrator's
step and was not touched (per the brief). No fix to price.

## 5. DD4, WITH ITS AXIS NAMED

**Axis: L against ambient (the port's axis).** All three lemmas are
L-hierarchy closure facts against ambient V operations: `union∈Lset-suc`
closes `Lset σ` under `⋃` and `sucV`; `EnvClosure` closes a transitive level
under `env (cons x g)` built from ambient `pr`, `finSet`, `#`, `sucV`;
`FiniteSup` merges finitely many ambient ordinal stages by `sucV`/`∪`/
`ord-tri`. None mentions `Def` or `J`, so none is on Devlin's Def-against-J
axis.

The sharing is real on that axis: each lemma is stated over an abstract
transitive level (`K : S` with `isTransV K`, or `(lam, ordλ, succλ, ∅∈λ)`)
and names no tower, so the L tower and the J tower re-instantiate them
unchanged and pay once, exactly as `[LJ-1.259]` and `[LJ-1.261]` measured.
The `Lset-fin` already in the master is reused by `finSetK` rather than
re-derived, so the DD4 line is shared, not copied.

## 6. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| all three landed | **MEASURED TRUE.** `Key.lagda.md:504,566,615` |
| the master is green | **MEASURED TRUE.** exit 0, three kept runs |
| the three re-runs against the master are green | **MEASURED TRUE.** exit 0 each |
| a wall (agda > 20 min) | **MEASURED FALSE.** max 442.86 s real |
| a consumer broke | **MEASURED FALSE.** additive change; sole consumer `Everything.lagda.md:351` |
| a lemma does not belong in `Key.lagda.md` | **MEASURED FALSE.** all three are its neighbours' level-closure facts |
| `make check` run | **MEASURED FALSE.** reserved for the orchestrator |
| I touched `Everything.lagda.md` or `LJ-1-264/` | **MEASURED FALSE.** only `Key.lagda.md` and `agents/tasks/LJ-1-263/` written |

## 7. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/LJ-1-261/lj-1.261-report.md`, read WHOLE. **Line read `:79`**,
  "The cure is P-i [A]: keep every stage a DIRECT term."
- `agents/tasks/LJ-1-261/ProbeLJ1261.agda`, read WHOLE. **Line read `:218`**,
  `finSetK`'s type, the supply I landed.
- `agents/tasks/LJ-1-259/lj-1.259-report.md`, read WHOLE. **Line read `:9`**,
  "`envConsK` does NOT build over `(K, Ktr)`."
- `agents/tasks/LJ-1-259/ProbeLJ1259.agda`, read WHOLE. **Line read `:114`**,
  `envConsK`'s type.
- `agents/tasks/LJ-1-254/lj-1.254-report.md`, read WHOLE. **Line read `:50`**,
  `union∈Lset-suc` adapted from `mkUnion`.
- `agents/tasks/LJ-1-254/ProbeLJ1254.agda`, read WHOLE. **Line read `:117`**,
  `union∈Lset-suc`'s type.
- `agents/tasks/LJ-1-260/lj-1.260-report.md`, read WHOLE. **Line read `:18`**,
  "Total: 60 insertions, 18 deletions, net +42" (the comparable).
- `src/L/Coding/Key.lagda.md:104-111` and `:130-135`, read at the source:
  `paramEnv∈` and `Lset-fin`, the two neighbours.
- `archive/dev/TASKS-archived.md`, read the header. **Line read `:10`**, "The
  264 rows below record every dispatch made on the retired route"; its shape
  carries no fixed-level gather closure.

## 8. LITERATURE USED (DD18)

**Devlin names none of the three closures and takes all three for granted.**
His `L_α` for limit α is closed under successor, so a finite union of stages
below α stays below α, and his `K(u)` is the finite sequences over the
formula set, so a finite environment extension and a finite supremum are
inside the carrier by definition; he states no separate lemma for any of the
three (`dev/literature/devlin-II5.md:246-255`, read directly).
