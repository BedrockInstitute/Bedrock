# LJ-1.110 report: restate the three split frames, and make the tree green again

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.110-report.md`.

## 0. Verdict

**ALL THREE MASTERS ARE GREEN, MEASURED.** `LowerAgree`, `UpperAgree`
and `TwelveAgree` each typecheck, exit 0, one process at the C-12 cap,
two cold runs each.  The tree was RED at HEAD: the orchestrator
measured exit 42 on all three (C-40), and my own pre-edit run of
`LowerAgree` failed fast at 3.30 s (load 3.78 start).  A failed check
is not a comparable figure; the last GREEN cold figures are the
[LJ-1.76] build numbers, 20.64 / 11.23 / 21.33 s.

After (cold, check-timing protocol, `GHCRTS=-M8g`, one process at a
time, machine NOT quiet: orchestrator `make check` and the sibling
cardinal agent share the machine):

| master | before (green, [LJ-1.76]) | after run 1 | after run 2 | load at start |
|---|---:|---:|---:|---:|
| LowerAgree | 20.64 | 20.6 | 20.2 | 5.10 / 3.84 |
| UpperAgree | 11.23 | 12.4 | 12.2 | 5.10 / 3.84 |
| TwelveAgree | 21.33 | 24.8 | 24.6 | 5.10 / 3.84 |

The spread across the two after-runs is 0.4 / 0.2 / 0.2 s.  The
UpperAgree and TwelveAgree deltas (+1.0 and +3.4 s) sit inside or just
outside the 8.2 s run-to-run spread [LJ-1.105] measured on this
content class; the lower bound of the true delta is not pinned.

Non-blank in-fence lines: LowerAgree 249 to 265 (+16), UpperAgree 240
to 268 (+28), TwelveAgree 295 to 303 (+8); +52 total.  Raw diff across
the three files: +207 / -135.

The frame fact count (telescope hypotheses): LowerAgree 43 to 37,
UpperAgree 43 to 36, TwelveAgree 69 to 59.  **The eleven refuted
hypotheses became `arityK` (reusing `transK` in LowerAgree and
TwelveAgree, a new hypothesis in UpperAgree) plus `sucK` (new in
UpperAgree and TwelveAgree) plus the site memberships the rows already
bind.**  The five tied key facts are DERIVATIONS from `sucK` and
`pairK`, zero hypothesis cost.

## 1. The three frames, restated

Every row telescope in `src/L/Condensation.lagda.md` was read as it
stands now; no earlier report's line numbers were used for the rows.
The repair is the one the brief names: the frames passed the OLD
arguments (`tmKeyK`, `entryK`, `arSubK-*`) that no longer exist in the
row telescopes, and lacked the new `arityK`.

### 1.1 LowerAgree (`src/L/Condensation/LowerAgree.lagda.md`)

Deleted from the telescope: `tmKeyK`, `entryK`, `arSubK-mem`,
`arSubK-neg`, `arSubK-imp`, and the untied `keyK-neg` (6 hypotheses;
all eleven-refuted names, `src/ProbeLJ197A.agda` and
`src/ProbeLJ195A.agda:45-48`).

Added: none.  The rows' `arityK` is supplied by the existing `transK`
with the binder roles swapped (a derivation, not a hypothesis):
`arityK N v hv hNK = transK v N hv hNK` (`LowerAgree.lagda.md:204-207`),
the same swap [LJ-1.93] measured.

Added derivation: `keyK-neg-tied`, the Neg row's tied key fact, from
`pairK` via `prʟ-fst` (`LowerAgree.lagda.md:194-199`), through the
generic module `KeyNegTies` (`:59-74`).

Row applications updated: MemAgree and EqAgree now pass
`arityK` in the arity position and drop `tmKeyK entryK arSubK-mem`
(`M` `:210-215`, `E` `:217-222`); ImpAgree passes `arityK` and drops
`entryK arSubK-imp` (`I` `:236-239`); NegAgree passes `arityK` and
`keyK-neg-tied`, drops `entryK arSubK-neg` (`N` `:242-245`).
AndAgree and OrAgree applications are unchanged (their telescopes
carry no `arityK`).

### 1.2 UpperAgree (`src/L/Condensation/UpperAgree.lagda.md`)

Deleted: `tmKeyK`, `entryK`, `arSubK-neg`, `arSubK-top`,
`arSubK-imp`, and the untied `succK`, `keyK-un`, `succK-allin`,
`keyK-allin` (9 hypotheses).

Added: `arityK` in its exact KFacts field shape (the KFacts field is
the consumer's supplier; there is no `transK` in this frame, so the
fact is stated, `:97-100`) and `sucK`, the successor closure, as a
TELESCOPE FACT, never a `KFacts` record field (P-x, `:150-152`).

Added derivations: the four tied key facts of the upper rows,
`succK-tied`, `keyK-un-tied`, `succK-allin-tied`, `keyK-allin-tied`,
from `sucK` and `pairK` (`:180-209`) through the generic module
`SuccKeyTies` (`:52-76`).

Row applications updated: TopAgree passes `arityK`, drops
`entryK arSubK-top` (`T` `:212-215`); ExistAgree and ForallAgree pass
`arityK`, the tied `succK-tied`/`keyK-un-tied`, and drop
`entryK arSubK-neg` (`X` `:223-228`, `F` `:231-236`); AllInAgree and
ExInAgree pass `arityK`, the tied allin facts, and drop
`entryK arSubK-imp tmKeyK` (`AI` `:239-244`, `EI` `:247-252`).
BotAgree's application is unchanged (its telescope carries no
`arityK`).

### 1.3 TwelveAgree (`src/L/Condensation/TwelveAgree.lagda.md`)

Deleted from `AbstractFrame`: all eleven refuted hypotheses,
`tmKeyK`, `entryK`, `arSubK-mem/neg/top/imp`, `keyK-neg`, `succK`,
`keyK-un`, `succK-allin`, `keyK-allin`.

Added: `sucK` as a telescope fact (`:186-188`).  `arityK` is not a new
name: `transK` already has the exact type, and the frame derives
`arityK` from it by the binder swap (`:218-221`), exactly the reuse
the brief's step 2 asks to check.

Added derivations: the five tied key facts, `keyK-neg-tied`,
`succK-tied`, `keyK-un-tied`, `succK-allin-tied`, `keyK-allin-tied`,
from `sucK` and `pairK` (`:230-261`), instantiating the generic
`KeyNegTies` (imported from LowerAgree) and `SuccKeyTies` (imported
from UpperAgree).

The LowerAgree and UpperAgree applications (`p0b`, `p1b`, `out`,
`back`) pass the new telescopes: `arityK` (derived) at the arity
positions, `sucK` for UpperAgree, and none of the deleted names
(`TwelveAgree.lagda.md:266-327`).

The generic modules are shared: `KeyNegTies` (one derivation) lives in
LowerAgree and is instantiated by LowerAgree and TwelveAgree;
`SuccKeyTies` (two derivations) lives in UpperAgree and is
instantiated by UpperAgree and TwelveAgree.  No new cross-file
dependency is added beyond TwelveAgree importing the two module
names from the partials.

## 2. Hypotheses and their suppliers

Every hypothesis the restated frames carry must be one the consumer
can supply; `src/ProbeLJ1100A.agda` is the record of what the consumer
can hold.

| hypothesis | frame | supplier |
|---|---|---|
| `arityK` | UpperAgree only (`:97-100`) | **SUPPLIED, MEASURED.** A `KFacts` field in the exact shape (`src/L/Condensation.lagda.md:5975-5977`); the extended consumer frame holds it as `kf .arityK` (`src/ProbeLJ1100A.agda:346-352` uses it to build `transK`), and TwelveAgree's derived `arityK` is that same field under a binder swap |
| `sucK` | UpperAgree (`:150-152`), TwelveAgree (`:186-188`) | **SUPPLIED, INFERRED.** A constructibility level closed under V-successor: `sucV a = a ∪ ⁅a⁆s`, for `a ∈ L β` at `β < α` with `α` limit, `a ∪ ⁅a⁆s ∈ L (β+1) ⊆ L α` (named at `_build/lj-1.109-report.md` section 2).  No instantiation exists in this tree; the extended consumer frame must grow this hypothesis |
| `transK` (reused as `arityK`) | LowerAgree, TwelveAgree (unchanged hypothesis) | **SUPPLIED, MEASURED.** The consumer derives it from `kf .arityK` (`src/ProbeLJ1100A.agda:352-354`) |
| the five tied key facts | none (derivations) | zero hypothesis cost (C-38); MEASURED inhabited in all three masters |
| `arityK` (derived) | LowerAgree `:204-207`, TwelveAgree `:218-221` | zero hypothesis cost; the binder swap of `transK` |

Refutation attempts:

| fact | attempt | status |
|---|---|---|
| `arityK` (hypothesis) | the conditional K-transitivity shape, the delivered field after the [LJ-1.77] repair | **NOT REFUTED, MEASURED.** Inhabited as a `KFacts` field and elaborated by the rows |
| `sucK` (hypothesis) | the [LJ-1.109] recipe: at the K-slot element X the premise is `X ∈ X`, refuted by `∈-irrefl` (`src/ProbeLJ1109A.agda`, `RefuteAttempts`, MEASURED) | **NOT REFUTED, INFERRED** (same verdict [LJ-1.109] recorded) |
| the five tied derivations | they are inhabited terms, not hypotheses | **MEASURED** inhabited; nothing to refute |

No twelfth refuted hypothesis was added: the two new names are the
sound `arityK` (delivered field) and `sucK` (unforceable at the
abstract frame, INFERRED not refuted).

## 3. C-39 section

1. "Do not touch `src/L/Condensation.lagda.md`" blocked the
   DD4-ideal home for the generic key-tie derivations: next to
   `ChainZ`/`EnvSet` in the master, which already hosts the other
   generic derivations and is the J tower's import surface.  The
   derivations therefore live in the split masters (`KeyNegTies` in
   LowerAgree, `SuccKeyTies` in UpperAgree), and TwelveAgree imports
   them from the partials.  The cost is one extra import edge, not a
   new copy: the two generic modules are instantiated once per frame
   (P-w: the copy is paid at use, and there are three uses).
2. "The successor closure `sucK` ... goes as a TELESCOPE FACT of the
   frame" blocked the route where the five tied facts are stated
   directly as frame hypotheses (the `ProbeLJ1100A.agda` `Extended`
   shape) and `sucK` stays out of the frames.  The mandated shape
   requires the consumer to supply `sucK`, which the extended
   consumer frame does not yet record.  The supplier is named in
   section 2 and is INFERRED, not measured; the next consumer dispatch
   must extend `ProbeLJ1100A.agda` with `sucK` before the composer is
   instantiable.

No other brief line blocked a route.

## 4. Negatives classified

1. All three masters are green: **MEASURED TRUE**, exit 0, two cold
   runs each, 20.2-20.6 / 12.2-12.4 / 24.6-24.8 s.
2. The frame fact count fell: **MEASURED TRUE**, 43/43/69 to 37/36/59
   by telescope count.
3. The cold seconds changed: **MEASURED TRUE**; the delta's lower
   bound is not pinned (the tree measured an 8.2 s spread on the same
   content class in [LJ-1.105], and the machine is not quiet).
4. The frames pass only arguments the rows' current telescopes take:
   **MEASURED TRUE**, the masters elaborate all twelve row
   applications.
5. Every new hypothesis is consumer-suppliable: `arityK` **MEASURED**
   (a delivered `KFacts` field); `sucK` **INFERRED** (constructibility
   closure; the extended consumer frame does not record it yet).
6. No new hypothesis is refuted: `arityK` **MEASURED** inhabited;
   `sucK` **INFERRED** not refuted ([LJ-1.109]'s premise barrier is
   MEASURED); the five tied facts are derivations, **MEASURED**
   inhabited.
7. The rows' conclusions are unchanged: **MEASURED TRUE by the diff**,
   no row or transfer in `src/L/Condensation.lagda.md` was touched,
   and the three frames' `out`/`back` state the same statements.
8. DD23 prose: three header sentences became FALSE and were left
   unchanged per DD23: "forty-three site facts" in
   `LowerAgree.lagda.md:6` (now 37) and `UpperAgree.lagda.md:6` (now
   36), and "the full sixty-nine-fact frame" in
   `TwelveAgree.lagda.md:5` (now 59), plus their Chinese twins at
   `LowerAgree.lagda.md:9`, `UpperAgree.lagda.md:9`,
   `TwelveAgree.lagda.md:8`.

## 5. DD4 answer

**The eleven refuted hypotheses became `arityK` plus `sucK` plus the
site memberships the rows already bind.**  Per frame, before to after:

| frame | before | after | delta |
|---|---:|---:|---:|
| LowerAgree | 43 | 37 | -6 |
| UpperAgree | 43 | 36 | -7 |
| TwelveAgree | 69 | 59 | -10 |

The eleven names are gone from all three frames.  `arityK` is reused
from `transK` in two frames and stated once in UpperAgree; `sucK` is
stated once per frame that needs it (UpperAgree, TwelveAgree); the
five tied key facts are derived, not stated, from the two closure
primitives through one generic module each (`KeyNegTies` in
LowerAgree, `SuccKeyTies` in UpperAgree), so the derivations are
written once and instantiated by the frames that need them.

## 6. Measurements

Cold seconds (check-timing protocol: module interface moved aside, one
process at a time, `GHCRTS=-M8g`).  The machine is NOT quiet: the
orchestrator runs `make check` in the background and a sibling agent
holds the cardinal slot.  Load averages are `uptime` at run start.

| master | last green before | after run 1 | after run 2 | spread |
|---|---:|---:|---:|---:|
| LowerAgree | 20.64 | 20.6 | 20.2 | 0.4 |
| UpperAgree | 11.23 | 12.4 | 12.2 | 0.2 |
| TwelveAgree | 21.33 | 24.8 | 24.6 | 0.2 |

Loads: before ([LJ-1.76]) 6.69 / 8.38 / 7.98, 4 users; after run 1
start 5.10, after run 2 start 3.84, 4 users both.

Non-blank in-fence lines (the same counter `check-timing` uses):
LowerAgree 249 to 265 (+16), UpperAgree 240 to 268 (+28), TwelveAgree
295 to 303 (+8), +52 total.  Raw diff: +207 / -135 across the three
files.

`scripts/check-fences.py --check`: clean, 87 masters.
`scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`:
clean on the three masters and this report.
`scripts/ledger.py --brief`: standing 28,373 lines over 85 masters,
measured from HEAD (the uncommitted edits are not counted).

No `make check` was run (the orchestrator runs it).  No commit, no
push; `src/L/Condensation.lagda.md`, `src/L/Coding/`, `src/V/`,
`src/L/BoundedSubset.lagda.md` and `src/Everything.lagda.md` are
untouched.  One `agda` process at a time throughout; each run started
only after the previous exited.

## ARCHIVE USED

- `_build/lj-1.109-report.md`, read WHOLE.  TOOK section 2 (P-x:
  `sucK` is a telescope fact, never a `KFacts` field; the wall
  measurement) and the `TiesSupplied` derivations the frames reuse.
- `_build/lj-1.108-report.md`, read WHOLE.  TOOK section 2's grep of
  which names left the row telescopes (`entryK`, `arSubK-*`,
  `tmKeyK` deleted; `arityK` added).
- `_build/lj-1.105-report.md`, read WHOLE.  TOOK the `EnvSet`/`ChainZ`
  shape and the arityK-supply pattern.
- `_build/lj-1.100-report.md`, read WHOLE, and
  `src/ProbeLJ1100A.agda`, read WHOLE.  TOOK the extended consumer
  frame (the 28 supplied, the 11 refuted), the tied `*-tied` shapes
  (`ProbeLJ1100A.agda:262-340`), and the `transK` binder swap
  (`:352-354`).
- `src/ProbeLJ199A.agda`, read WHOLE.  TOOK `ChainZ` and the site
  shapes.
- `src/ProbeLJ1109A.agda`, read WHOLE.  TOOK `TiesSupplied` (the
  exact `succ-tied`, `key-neg-tied`, `key-un-tied` terms) and
  `RefuteAttempts`.
- `src/ProbeLJ1104A.agda`, read `:1-200` and the module shapes
  `:200-694`.  TOOK the keyValK refutation and the tied-row pattern.
- `src/ProbeLJ197A.agda` and `src/ProbeLJ195A.agda`, read WHOLE.
  TOOK the eleven refutations that justify deleting the names.
- `_build/lj-1.76-report.md`, read WHOLE.  TOOK the three masters'
  build-time cold seconds (20.64 / 11.23 / 21.33 s) and the
  43/43/69 fact counts.
- `dev/LESSONS.md`, P-x (`:3556-3589`), C-38 as extended
  (`:3427-3511`), C-39 (`:3513-3555`), C-35 (`:3200-3242`),
  C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30 (`:3332-3380`),
  P-i (`:203-262`), P-w (`:3094-3164`), C-40 (`:3591-end`), read
  WHOLE.  TOOK the satisfiable-telescope standard, the
  prohibition-priority rule, the record-field wall, and the
  consumer-check discipline.
- `scripts/rules.py --for build` and `--for rewrite`, read all
  statements.

## LITERATURE

Banked; nothing spent.

## ARCHIVE USED

FILLED LAST at `file:line`.

## LITERATURE

Banked; nothing spent.
