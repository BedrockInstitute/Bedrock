# LJ-1.277 report: land A2 as `src/L/Coding/Injection.lagda.md`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
A new master written. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**238 in-fence lines, 1.66 s cold, rate 0.0070 s/line, which is 0.66x the
0.010514 bar.** MEASURED, three cold runs, load 5.6-7.4. The master is GREEN,
exit 0, `--safe`. The re-run that imports it is GREEN, exit 0. This is a
landing, not a copy (C-45).

| figure | value |
|---|---:|
| in-fence non-blank lines (ledger caliber, live) | 238 |
| cold elapsed (mean of 3) | 1.66 s |
| cold range | 1.57-1.74 s |
| rate | 0.0070 s/line |
| bar | 0.010514 s/line |
| rate as a share of the bar | 0.66x |

The rate is the P-m parameterized-class rate: the master states formulas and
proves decodes at bound variables under a module telescope, no concrete
carrier, so it checks near 0.01 s/line. That is the expected class for A2 and
it is under the bar.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no heap
exhaustion, no kill, no run past 30 minutes.

| run | exit | cold/warm | elapsed s | 1-min load |
|---|---|---|---:|---:|
| master, run 1 | 0 | cold (fresh .agdai) | 1.68 | 7.36 |
| master, run 2 | 0 | cold (deleted .agdai) | 1.74 | 5.63 |
| master, run 3 | 0 | cold (deleted .agdai) | 1.57 | 5.67 |
| master, run 4 | 0 | warm | 1.09 | 5.90 |
| `ReRun.agda` | 0 | cold (fresh) | 1.27 | 9.57 |

Cold figure reported in the lead is the mean of the three cold runs, 1.66 s.
The machine was loaded throughout (load 5.6-9.6); the figure is an upper
bound in the sense of `[LJ-1.268]`'s loaded-machine convention, and it still
clears the bar.

## 2. WHAT THE MASTER EXPORTS, AND WHAT IT KEEPS PRIVATE

The boundary is set by what A3, A4, A5 row 1 and A6 each name, read out of
their probes at `file:line`. P-k: each read lemma is stated at the form its
consumer uses, and nothing with no external consumer is exported.

**Exports** (each with its consumers):

| name | consumers | evidence |
|---|---|---|
| `injAt` | A3, A4, A5 row 1, A6, A7 | `ProbeLJ1232A3.agda:73`, `ProbeLJ1236A4.agda:67`, `ProbeLJ1264A.agda:88`, `ProbeLJ1217A.agda:240`, `ProbeLJ1236A7.agda:79` |
| `injAt-out` | A3, A5 row 1 | `ProbeLJ1232A3.agda:98`, `ProbeLJ1264A.agda:111` |
| `injAt-in` | A3, A5 row 1, A6 | `ProbeLJ1232A3.agda:101`, `ProbeLJ1264A.agda:116`, `ProbeLJ1217A.agda:240` |
| `module Extract` | A5 row 1 | `ProbeLJ1264A.agda:121` |
| `module Small` | A5 row 1, A6 | `ProbeLJ1264A.agda:162`, `ProbeLJ1217A.agda:240,588` |

**Kept private** (the master's own proof that the pieces assemble; no block
outside names them, MEASURED by the same five probes):

`rangeGraph`, `rangeGraph-adequate`, `module Range` (the range set C by
`hasReplacementL`), `inRanAt`, `inRanAt-adequate`, `ranAt`, `ranAt-out`,
`ranAt-in`, `ranAt-intro`, `module RanHolds` (C satisfies `ranAt`), and
`module Injection` (the whole, assembled, renamed from the probe's `A2`).

The probe's own header split was description-plus-adequacy (S1, consumed by
A4) against readback (S2+S6, not consumed by A4). That split is now literal:
the description and the readback are exported; the range machinery that sits
between them is private. The read lemmas are stated at the S-carrier
membership form (`pr (fst x) (fst y) ∈ fst F`) and at the small-index form
(`⟪ fst D ⟫ → ⟪ fst C ⟫`), which is exactly the form the consumers rewrite
with, so no consumer re-normalizes a layer the master already absorbed.

`module Injection` is private because no consumer imports the assembly; A5 and
A6 import the pieces and supply C and `ran` themselves (`ProbeLJ1217A.agda:588`).
When a block needs the assembled form, un-privatizing one module is one cheap
change, and P-k says to seal it here until a consumer names it.

## 3. THE `src/Everything.lagda.md` LINE

**`import L.Coding.Injection`**, to be inserted **after line 335
(`import L.Coding.Model`), before line 336 (`import L.Coding.InL`)**. That is
the coding-master block, immediately after the master's direct dependency
`L.Coding.Model`; its other dependency `L.Axioms.Full` sits at line 332, so
the position satisfies reading order. I did NOT touch `Everything.lagda.md`;
the orchestrator wires it after audit.

## 4. THE RE-RUN (C-45)

**`agents/tasks/LJ-1-277/ReRun.agda`, exit 0.** It imports all five exports
and uses each in a consumer-shaped term:

- `injAt` in the `ij`/`sv`/`dm` hypothesis types;
- `Extract` via `module E = Extract F D sv dm` and `E.Dom`/`E.toFun`/
  `E.toFun-graph`;
- `Small` via `module Sm = Small F D C sv dm ij ran` and `Sm.small`/
  `Sm.small-inj`;
- `injAt-out` in `toFun-inj′`, the readback re-derived at the consumer site;
- `injAt-in` in `ij-from`, the hypothesis built at the consumer site, exactly
  as A6 builds it.

All over abstract parameters, so the re-run is cheap (1.27 s). A copy that
compiles is not a landing; this re-run proves the master is a supply.

## 5. EVERY EXISTING MASTER I DID NOT EDIT

**MEASURED: zero tracked files modified.** `git diff --stat` over tracked
files is empty; `git status --short` shows no ` M` entry. The four
over-the-bar Condensation masters are untouched: `src/L/Condensation.lagda.md`,
`src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md`,
`src/L/Condensation/TwelveAgree.lagda.md`. All 88 tracked masters are
unedited; the landing is a new file
(`src/L/Coding/Injection.lagda.md`) plus my task directory
(`agents/tasks/LJ-1-277/`), and the sibling's
`src/L/Coding/EnvSupply.lagda.md` is its own file, not mine and not colliding.
`[LJ-1.268]`'s claim holds: no over-the-bar master gains a line.

## 6. DD4, ON THE AC-AGAINST-GCH AXIS

**Axis named (C-46): DD4's own axis is AC-against-GCH**, fixed in code at
`scripts/ledger.py:50` (the AC closure against the GCH closure), per
`dev/LESSONS.md:4010` and `dev/PLAN.md:945`.

**On that axis this master sits on the GCH side alone.** MEASURED twice. The
AC root's import list at `src/L/Model.lagda.md:49-57` imports `L.Constructible`,
`L.Axioms.Basic/Numerals/Infinity/Full/Power` and `L.Choice.Transversal`; none
reaches `L.Coding.Injection`. And `grep -rl "L.Coding.Injection" src/` returns
only the new master itself, so no existing master imports it and the AC closure
excludes it by construction. The GCH root does not exist yet
(`dev/ledger.toml:177`, `gch_root = ""`), but A7 (`L.GCH`) imports `injAt`, so
the day the GCH endpoint lands, this master enters the GCH closure. What it
means: DD4's own report still cannot run today, and this master is honest
GCH-side content, not a shared-intersection line.

**On the phase's proxy axis (Def-against-J), A2 is tower-neutral**
(`[LJ-1.227]`), so the sharing is preserved where the code is generic even
though DD4's own axis places it on the GCH side. **What a J instantiation
would need:** swap `𝒮ʟ`/`isL`/`isL-trans` for the J structure and J's
level-hood predicate (the only per-tower content is the
`Σ≡Prop (λ z → snd (isL z))` equality lift, two sites), swap `hasReplacementL`
for J's replacement, and swap `appAt`/`svAt`/`domAt`/`prAtL`/`prʟ` for the J
coding atoms with the same adequacy interfaces. The formulas (`injAt`, `ranAt`,
`inRanAt`, `rangeGraph`) are pure syntax over `appAt`/`prAtL` and transfer
verbatim; the readback (`Extract`, `Small`) uses only ambient
`⟪_⟫`/`⟪_⟫↪`/`fiber`/`↪-inj`/`member`.

## 7. ARCHIVE USED (DD18)

One line read named per archived file.

- **`agents/tasks/LJ-1-229/ProbeLJ1229A.agda`, read WHOLE.** Line read `:205`,
  `rep = hasReplacementL D (rangeGraph F) funct .fst`, the range set by
  replacement. TAKEN: the whole content, which became the master.
- **`agents/tasks/LJ-1-229/lj-1.229-report.md`, read WHOLE.** Line read `:47`,
  the 27-line description-plus-adequacy split. TAKEN: the export boundary.
- **`agents/tasks/LJ-1-268/lj-1.268-report.md`, read.** Line read `:29`,
  "A2 -> src/L/Coding/Injection.lagda.md (new)". TAKEN: the home and the
  no-extension finding.
- **`agents/tasks/LJ-1-263/lj-1.263-report.md`, read WHOLE.** Line read `:5`,
  "All three landed, and src/L/Coding/Key.lagda.md is GREEN". TAKEN: the
  landing method (re-run the consumer against the master), copied here.
- **`agents/tasks/LJ-1-134/lj-1.134-report.md`, read.** Line read `:219-227`,
  the per-part table with `injAt` at 27 and the extraction at 29. TAKEN: the
  core A2 grew from.
- **`archive/dev/TASKS-archived.md:10`.** TAKEN, SHAPE ONLY: "The 264 rows
  below record every dispatch made on the retired route".
- **`archive/src/2026-08-09-rud-route/L/Coding/Base.lagda.md:10`.** TAKEN,
  SHAPE ONLY: `module L.Coding.Base {ℓ : Level} where`, the retired coding
  cone. **WHAT WOULD NOT TRANSFER:** `grep -rl "ranAt\|injAt"` over the
  archive returns nothing; the rud route reached its trophy through `L/Rud/*`
  closure machinery and never wrote a coding-layer `injAt`/`ranAt`, so there
  is no archive shape to copy. The natural shape, `ranAt` mirroring `domAt`,
  is what I wrote.

## 8. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:365-395`, read directly.** TAKEN: the
twelve-row step table and the verdict at `:387-389`.

**Which row A2 serves: row F**, the 5.5 cardinal-comparison step
(`|L_α| = |α|`, initial ordinals, `|𝒫(κ)| ≤ κ⁺`). A2 is the machinery that
internalizes "there is an injection from a to b" and reads it back as
`⟪D⟫ ↪ ⟪C⟫`, which is A-prime's own form for the cardinal comparison that row F
concludes. Devlin states that comparison by subset containment and level size,
never by internal injection, so the literature names no shape for A2
(`ProbeLJ1229A.agda`'s own report, `lj-1.229-report.md` section 8). A2 is
A-prime's machinery for the same step, not a step Devlin writes.

## 9. THE NEGATIVES, CLASSIFIED

- **MEASURED FALSE. The master fails to typecheck.** exit 0, `--safe`, three
  cold runs and one warm.
- **MEASURED FALSE. An import is not delivered.** Every import of the probe is
  a delivered master; `lint-agda.py --check` exits 0, which is the master
  necessity check.
- **MEASURED FALSE. A master refused what the probe accepted.** The only
  differences are the module name, the trimmed `using` lists (dropped `V`,
  kept `_∈_`), the reorder, and the `private` block; `lint-agda.py --check`
  and `lint-prose.py --check` both exit 0.
- **MEASURED FALSE. A wall.** Max single run 1.74 s, far under 30 minutes.
- **MEASURED FALSE. I touched an existing master or `Everything.lagda.md`.**
  `git diff --stat` empty; only new files written.
- **MEASURED FALSE. I touched `L.Choice.Name` or `agents/tasks/LJ-1-276/`.**
  Neither appears in my writes; my write territory was
  `src/L/Coding/Injection.lagda.md` and `agents/tasks/LJ-1-277/` only.
- **INFERRED. `module Injection` stays private.** It is the placement decision
  from P-k; no consumer names it today, and un-privatizing is one change.

## 10. WORKING TREE, AS MY REPORT DESCRIBES IT

Three files written: `src/L/Coding/Injection.lagda.md` (the new master),
`agents/tasks/LJ-1-277/ReRun.agda` (the re-run), and
`agents/tasks/LJ-1-277/lj-1.277-report.md` (this file). No master, brief or
report edited. No commit, no push, no `git checkout .`, stash, reset or clean.
The sibling directory `agents/tasks/LJ-1-276/` and the sibling master
`src/L/Coding/EnvSupply.lagda.md` were not touched.

`scripts/lint-agda.py --check` and `scripts/lint-prose.py --check` both exit 0
on the master.
