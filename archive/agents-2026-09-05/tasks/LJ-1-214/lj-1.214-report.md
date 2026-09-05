# LJ-1.214 report: is the 8.2 s the telescope component, or the rest of the commit?

**STATUS: COMPLETE.** I edited no master. I committed nothing and pushed
nothing. I ran no `make check`. Every probe lives under
`agents/tasks/LJ-1-214/`, tracked, never deleted. **No heap exhaustion; the
longest single invocation was 126.77 s.**

**Head: DeepSeek v4 pro, selected by the clock** (`scripts/dispatch_policy.py`,
`VERSION_IN_FORCE = 'auto'`). I hold ONE Agda process at all times at
`GHCRTS="-A64m -I0 -M8g"`, cap never raised.

**MACHINE STATE.** Load at session start: 5.61 / 6.20 / 17.20. A sibling may
hold the other slot. Load is recorded beside every run in section 3.

## 0. LEAD

**THE COMPONENT CARRIES IT. MEASURED.** Six kept runs per arm, two series with
reversed order, one machine state:

| arm | `Deserialization` self, mean |
|---|---:|
| `ProbeDelete` — revert commit `c8a628b` ONLY (the numeral component), keep `a01ef58`'s `envInK` field | **1,131 ms** |
| `ProbeMinusArNum` — revert `a01ef58` AND `c8a628b` (rung 1) | **1,139 ms** |
| `ProbePlain` — today's master (rung 3) | **9,056 ms** |

**Reverting the numeral component recovers 9,056 - 1,131 = 7,925 ms of the
8,236 ms term.** The extra revert in `ProbeMinusArNum` (commit `a01ef58`'s
`envInK` ar-membership field) moves a further **+8 ms** — inside the fast arms'
own spread, so it is ZERO. **The whole 8.2 s is the telescope component's
EXISTENCE; the rest of the commit carries none of it.**

## 1. THE TRAP: the two `graphWitK` bindings, found BEFORE any edit

Found before any edit, in `agents/tasks/LJ-1-214/ProbeDelete.agda`:

- **`:6868`** `ks = witK d e f h` — inside `body-out` of `SatGraphAgree`.
- **`:6967`** `let ks = witK d e f body` — inside `SatGraphAgree.out`.

Both bind a `ks` from `graphWitK` (the parameter at `:7056`), a THREE-component
product of memberships `⟨ fst d ∈ ⟩ × ⟨ fst e ∈ ⟩ × ⟨ fst f ∈ ⟩` with **no
numeral component**. Their projections `.fst`, `.snd .fst`, `.snd .snd` are all
real and must NOT be rewritten. The 71 edits touch only the `ks` bindings from
`codesK` / `unCodesK` / `compK` / `unCompK`, which DO carry the numeral.

## 2. THE METHOD

The DELETE arm is `agents/tasks/LJ-1-214/ProbeDelete.agda`, built by
`gen_probes.py` from `git show c8a628b~1:src/L/Condensation.lagda.md` (module
renamed). This reverts commit `c8a628b` ONLY and keeps commit `a01ef58`'s
`envInK` ar-membership field.

**Why `c8a628b~1` is the right cut.** The rung-1 probe
(`ProbeMinusArNum`, 1,165 ms) was built from commit `423ea83`, which predates
TWO commits: `a01ef58` (the four cheap fields, the `envInK` ar-membership) AND
`c8a628b` (the numeral component). So rung 1 reverts both together, and the
8.2 s it measures is their SUM. The DELETE arm separates them.

**Verified against the master:** `ProbeDelete` differs from `ProbePlain` in
exactly **71 hunks, 182 lines (113 insertions, 67 deletions)**, every hunk a
numeral-component site (the 46 type sites, 11 destructuring, 9 argument, 5
projection — one hunk holds two projections). `diff` printed no other change.

### 2.1 The bisection that located it

The ladder's rung 1 (`ProbeMinusArNum`) was built from commit `423ea83`, which
predates TWO commits, so it reverts both together and its 8.2 s is their SUM.
My DELETE arm cuts between them:

| arm | what it reverts | mean |
|---|---|---:|
| `ProbeMinusArNum` (rung 1) | `a01ef58` + `c8a628b` | 1,139 ms |
| `ProbeDelete` (this task) | `c8a628b` only | 1,131 ms |
| `ProbePlain` (rung 3) | nothing | 9,056 ms |

DELETE sits at rung 1's level, so the cost is inside `c8a628b`, and the extra
`a01ef58` revert buys +8 ms. Inside `c8a628b` there is nothing left to bisect:
its Condensation diff is 100 percent numeral-component sites (section 2), and
LJ-1.209 already split the component's CONTENT (47 ms) and VISIBILITY (83 ms)
off the EXISTENCE. **The 8.2 s is the component's existence, and it is the
whole of what c8a628b added to this master.**

## 3. THE MEASUREMENT

Instrument: `--profile=internal`, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time, each run cold (the probe's own `.agdai` deleted first).
Within-series paired design, three arms, three kept runs each, warm-up
discarded.

### 3.1 SERIES 1 (rotation order Delete, Plain, MinusArNum)

| run | `ProbeDelete` (revert c8a628b) | `ProbePlain` (master) | `ProbeMinusArNum` (revert both) |
|---|---:|---:|---:|
| 1 | 1,063 | 8,934 | 1,152 |
| 2 | 1,138 | 8,869 | 1,070 |
| 3 | 1,151 | 9,125 | 1,148 |
| **mean** | **1,117** | **8,976** | **1,123** |
| own spread | 88 ms (7.9%) | 256 ms (2.9%) | 82 ms (7.3%) |

Load before each run: 2.86 to 4.29 (1-minute), 15-minute decaying from 10.32
to 5.51 across the series. **Evidence:** `series1.log` holds all nine
`Deserialization` lines; `runs-series1/` holds the raw profiles (its `m1` was
overwritten by Series 2's first run before the copy, and its 1,152 ms is in
`series1.log`).

**Series 1 says it already:** reverting `c8a628b` alone recovers
8,976 - 1,117 = **7,859 ms**; the extra revert in `ProbeMinusArNum` (commit
`a01ef58`) moves a further **+6 ms**. The two fast arms sit eight times below
the master.

### 3.2 SERIES 2 (reversed order MinusArNum, Plain, Delete)

| run | `ProbeMinusArNum` | `ProbePlain` | `ProbeDelete` |
|---|---:|---:|---:|
| 1 | 1,162 | 9,061 | 1,138 |
| 2 | 1,150 | 9,153 | 1,141 |
| 3 | 1,152 | 9,194 | 1,152 |
| **mean** | **1,155** | **9,136** | **1,144** |

Load before each run: 3.21 to 5.08 (1-minute). **Evidence:** `series2.log`
holds all nine lines; `runs/` holds Series 2 raw profiles plus the discarded
`ProbeDelete.validate` warm-up.

### 3.3 BOTH SERIES COMBINED (6 kept runs per arm)

| arm | runs | mean | own spread |
|---|---:|---:|---:|
| `ProbeDelete` (revert c8a628b) | 1,063 1,138 1,151 1,138 1,141 1,152 | **1,131 ms** | 89 ms (7.9%) |
| `ProbeMinusArNum` (revert both) | 1,152 1,070 1,148 1,162 1,150 1,152 | **1,139 ms** | 92 ms (8.1%) |
| `ProbePlain` (master) | 8,934 8,869 9,125 9,061 9,153 9,194 | **9,056 ms** | 325 ms (3.6%) |

**The figure a decision rests on, six runs each:**

- **c8a628b's numeral component carries 9,056 - 1,131 = 7,925 ms.**
- **a01ef58's `envInK` field carries 1,139 - 1,131 = +8 ms, i.e. nothing.**

The two fast arms are 8.0 times below the master; the +8 ms is an eighth of
the fast arms' own 89-to-92 ms spread. **No drift, no order effect, no load
swing can fake an 8x separation.**

## 4. THE CLASSIFICATION

| statement | class |
|---|---|
| the 8.2 s is the extra telescope component | **CONFIRMED. MEASURED.** DELETE recovers 7,925 ms of it |
| commit `a01ef58`'s `envInK` field carries part of the 8.2 s | **REFUTED. MEASURED.** +8 ms between DELETE and MinusArNum |
| the numeral CONTENT carries the term | **REFUTED (by LJ-1.209). MEASURED.** |
| the numeral VISIBILITY (`opaque`) carries the term | **REFUTED (by LJ-1.209). MEASURED.** |
| a shared `isNumeral` definition would save the 8.2 s | **REFUTED. INFERRED.** The cost is the field's presence in the telescope type, not its definition site |
| I edited a master, committed, pushed, ran `make check` | **MEASURED FALSE.** None of these |
| I ran more than one Agda process, or raised the cap | **MEASURED FALSE.** One at a time, `-A64m -I0 -M8g` |
| a single invocation passed 30 minutes | **MEASURED FALSE.** Longest 126 s |
| I touched `graphWitK`'s `ks` bindings | **MEASURED FALSE.** Byte-exact from git; trap verified at `:6868`, `:6967` |

## 5. DD4

**Maximize the code the two proofs share, and write it generic.**

The wing's property is `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`. Its definition sits
BELOW both towers: `#_` is Cubical's `InfinitySet` on `V`, and `V ℓ` is
tower-free, so an `isNumeral : V ℓ → Type (ℓ-suc ℓ)` definition re-instantiates
free for the J tower (zero extra lines).

**One shared form CAN serve all three sites, at the price of one `sym`.** The
two existing sites use opposite orientations: `# n ≡ δ`
(`src/L/StageCardinal.lagda.md:422`) and `β ≡ # n`
(`src/L/Ordinal/SquareLaw.lagda.md:539`). The wing's orientation matches
SquareLaw. A single shared `isNumeral x = ∥ Σ[ n ∈ ℕ ] (x ≡ # n) ∥₁` serves the
wing and SquareLaw as-is; StageCardinal pays one `sym` (unmeasured).

**But sharing does NOT touch the 8.2 s. MEASURED, and it is the point of this
task.** The cost is the component's EXISTENCE in the telescope type, not its
definition site or content. LJ-1.209 already emptied the content (`x ≡ x`) and
sealed it `opaque`, and neither moved the term; this task shows deleting the
component moves all of it. A shared definition is three shared lines that still
carry the same presence cost. **The property is tower-neutral; the cost is
not a DD4 defect.**

## 6. WHAT A CURE WOULD COST

**The cure is removing the component, and it would restore the 21 false
fields.** The component exists to make 21 fields provable; `[LJ-1.173]` added
it because the fields were false without it. Deleting it recovers the 8.2 s AND
un-cures the fields. That is a complete and useful answer, and the cure is a
design question for the owner, not an edit for me.

**Keeping the field's content while paying less for its presence: no measured
mechanism reaches.** LJ-1.209 already priced the two candidates and both are
void:

- **Seal it `opaque`:** 83 ms of 8,236 ms, sign flipping (LJ-1.209 section 3.2).
- **Empty the content (`x ≡ x`):** 47 ms the wrong way (LJ-1.209 section 3.3).

So the cost is the field's EXISTENCE in the telescope type itself, not its
content, its transparency, or its definition site. The three cheap levers
(content, visibility, sharing) are all measured NOT to reach. **Any cure that
keeps the field must change WHERE the numeral fact lives** (out of the
telescope type, into a definition body or a single shared supplier), which is a
mathematical restructure, not a probe. I do not price it because it is not
built; I name it INFERRED.

## 7. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-209/lj-1.209-report.md`, read WHOLE with its probes.**
  **TOOK:** the four-rung ladder at section 3.4; the three refutations (seal
  83 ms at section 3.2, `unfolding` zero at section 2, content 47 ms the wrong
  way at section 3.3); the 63-occurrence count at section 1; the 71-edit table
  and the `graphWitK` trap at section 7.1; the within-series paired design at
  section 3.1. **Its probes are my starting point; I did not rebuild them.**
- **`agents/tasks/LJ-1-204/LJ-1.204-report.md`, read WHOLE.** **TOOK:** the
  8.4 s cause at `:16-18`; the `ProbeMinusArNum` bottom rung 1,238 ms at `:58`;
  the probe generator shape. **Re-read and re-ran its `ProbeMinusArNum.agda`**
  (copied to `agents/tasks/LJ-1-214/` with the module renamed).
- **`agents/tasks/LJ-1-173/lj-1.173-report.md`, read section 1.** **TOOK:** the
  two-stage cure (codesK component + the dear fields) and the 21 false fields.
- **`git show c8a628b` and `git show a01ef58`, read the diffs directly.**
  **TOOK:** c8a628b's Condensation diff is 71 hunks, all numeral-component
  sites (verified by `diff`); a01ef58's is the `envInK` ar-membership field.
  **This is what located the cost: the DELETE arm is `c8a628b~1`, which keeps
  a01ef58 and reverts c8a628b.**
- **`agents/tasks/LJ-1-145/lj-1.145-report.md`, read section 0, 1, 4.**
  **TOOK AS SHAPE ONLY (P-l):** the seal cure, never a transferred price.
- **`scripts/check-ratio.py:65-85`.** **TOOK:** the 12.8% between-series band,
  which is why the design is within-series paired.
- **`dev/ledger.toml` and `scripts/ledger.py --brief`.** **TOOK:** standing
  29,777 lines over 88 masters.
- **`archive/dev/TASKS-archived.md`: SURVEYED, NOT USED.** The retired route
  holds no interface-deserialization account. Taken as shape only.
- **`dev/LESSONS.md` at each entry named in the brief:** D-1 (abort criterion
  fixed before the run), P-t (the seal licence, already void), P-l (I re-measured
  at the site, never transferred LJ-1.145's seal), P-q (no line deletion to buy
  a ratio), C-42 (the refutation names one site: the component), C-12 (one
  process, cap never raised), C-22 (this file existed before the first run),
  DD8 (one number with its basis: the six-run mean).

## 8. LITERATURE (DD18)

Nothing in the literature governs elaboration cost.
