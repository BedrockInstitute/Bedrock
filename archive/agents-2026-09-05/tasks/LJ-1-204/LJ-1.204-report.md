# LJ-1.204 report: `Deserialization` at Condensation, cause and cure

Status: COMPLETE. No master edited, nothing committed, nothing pushed. All
probes live under `agents/tasks/LJ-1-204/`, tracked, never deleted. One Agda
process at a time at `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no wall hit.

## 0. LEAD

**CAUSED. The cause is the `arNum` field `[LJ-1.173]` added to the
`codesK`/`envK` telescope hypotheses, NOT the `Bound` import the brief
suspected. The rise is the price
of content the wing now needs, at a pathological rate, and the cure is a seal
hypothesis that is UNPRICED.**

**`Deserialization` TODAY (cold, `--profile=internal`, same caliber): 9,920 /
9,823 / 9,989 ms self, mean 9,911 ms; cumulative 10,495 / 10,380 / 10,537 ms,
mean 10,471 ms.** Against the 1,689 ms baseline (`[LJ-1.155]`) and ~10,000 ms
(`[LJ-1.185]`). **The rise is REPRODUCIBLE and NOT transient.**

**The brief's interface-size hypothesis is REFUTED, MEASURED.** The full
transitive interface closure (bedrock `src/` PLUS the pinned cubical library)
grew 32,795,596 bytes to 33,073,334 bytes, +277,738 bytes, **+0.85 percent**,
while cold `Deserialization` self time grew x8.1. A +0.85 percent size change
cannot price a +714 percent time change.

## 1. THE PAIRED MEASUREMENT, within-series

Three cold runs, one series, today, at the ledger caliber:

| run | `Deserialization` self | cumulative | load before | load after |
|---|---:|---:|---|---|
| 1 | 9,920 ms | 10,495 ms | 5.99 / 5.47 / 5.23 | 6.50 / 5.55 / 5.27 |
| 2 | 9,823 ms | 10,380 ms | 6.50 / 5.55 / 5.27 | 5.44 / 5.52 / 5.30 |
| 3 | 9,989 ms | 10,537 ms | 5.44 / 5.52 / 5.30 | 6.22 / 5.82 / 5.45 |

Within-series spread: **1.7 percent self, 1.5 percent cumulative** (max-min
over mean). This is inside the 0.5-to-4.0 percent within-series band
`check-ratio.py` names. Files: `runs/src_L_Condensation.today.int{1,2,3}.txt`.

The spread resolves the 3 s the brief names: a percent-level cure is
measurable. Today's load (5.4 to 6.5) sits above `[LJ-1.185]`'s (3.4 to 3.7)
because a sibling holds the other Agda slot (`LJ-1.198`,
`ProbeLJ1198A.agda`, live for over four hours at ~99 percent of one core),
and today's mean reads ~5 percent higher than `[LJ-1.185]`'s. That few-percent
drift is the load's size, and it is beside the point: the rise to price is
8.3 s, and `[LJ-1.201]` section 4.1 already measured that the LOADED day was
the FASTER one at the baseline, so load is not its cause.

## 2. THE CAUSE, isolated by two probes

`[LJ-1.172]` added the `Bound` import + the `KValue` supply; `[LJ-1.173]`
added the `arNum : ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` field. I built renamed
copies of `src/L/Condensation.lagda.md` that separate the two (generator
`gen_probes.py`; the copy is a probe, not a master edit):

| probe | content | `Deserialization` self | cumulative | total |
|---|---|---|---:|---:|
| `ProbeMinusArNum.agda` | `Bound` + `KValue`, NO arNum (commit 423ea83) | **1,238 ms** | 1,793 ms | 126,274 ms |
| `ProbeMinusBound.agda` | arNum, NO `Bound`/`KValue` (current minus last fence) | **9,664 ms** | 10,219 ms | 135,524 ms |
| master, today | both | 9,920 ms | 10,495 ms | 141,607 ms |
| `[LJ-1.155]` baseline | neither | 1,156 ms | 1,689 ms | 121,115 ms |

**MEASURED: the `arNum` field alone reproduces the rise (9,664 ms), and
`Bound` alone leaves `Deserialization` at the baseline (1,238 ms).** The two
cells are 1,238 against 9,664, a factor of 7.8, far outside the load swing.

**MEASURED within one day, the split is:** `arNum` adds 9,250 ms to the total
of which 8,426 ms is `Deserialization` (ProbeMinusBound minus
ProbeMinusArNum); `Bound` adds 6,083 ms to the total of which 256 ms is
`Deserialization` (today's master minus ProbeMinusBound). So `Bound` costs
seconds in `Serialization` and `InterfaceInstantiateFull`, and next to nothing
in `Deserialization`.

**MEASURED: the interface-size hypothesis is REFUTED.** Only two modules are
new in the closure: `L.Coding.Bound` (192,697 B) and `L.Ordinal.StageArith`
(85,041 B). `probe_closure_full.py` prints the full account.

## 3. THE MECHANISM

**The trigger is MEASURED; the attribution below is INFERRED.**

A warm check today (interface present, up-to-date, no typecheck) reads
`Deserialization` 1,334 ms self. A cold check reads 9,920 ms. The extra ~8.5 s
appears only during the full typecheck. **So `Deserialization` here is not a
one-time read of the import list; it is the on-demand (lazy) read of imported
definition bodies that the typechecker pulls while it checks the master's
body.**

**INFERRED cause of the pull:** the `arNum` conjunct `× ∥ Σ[ n ∈ ℕ ] (fst ar
≡ # n) ∥₁` is a truncated dependent sum placed in the `*Agree` telescope
TYPES, and
its proofs are built at the leaves. This is the first place in the master
where the numeral enters an EQUALITY inside a Σ inside a truncation inside a
module signature (earlier `# k` uses sit in definition bodies, computing a
code). Elaborating those signatures and constructing their proofs forces the
typechecker to pull imported definition bodies on demand, and that read is
billed to `Deserialization`. The `Bound` import names none of it, which is
why it bills zero.

**I mark this INFERRED, and I name what I did NOT establish.** I did not
observe per-import deserialization timing, so I did not identify WHICH
imported definitions are pulled; I ruled out the simplest candidate ("`# n`
with a variable is new") because `# k` with a variable already sat at
`src/L/Condensation.lagda.md:2551,2588,2639,2685` at the baseline. The tool
does not offer a per-import account: `--profile=serialize` reports the
master's OWN serialization statistics (54,206,496 modal polarities,
12,786,407 term nodes), not a per-import deserialization account
(`runs/src_L_Condensation.serialize1.txt`). The trigger (arNum) is measured;
the attribution of the 8.4 s is inference.

## 4. CURE AND PRICE

**CAUSED AND NOT CURABLE as a revert, and the cure is a HYPOTHESIS, UNPRICED.**

The `arNum` content cannot be removed: `[LJ-1.173]` added it to make 21 false
fields provable, and the fields are the mathematical content the wing now
needs. So the rise is the price of content the wing needs.

**But the price is pathological, not inherent.** A handful of small type
fields cost 8.4 s, about 420 ms per field, for a field that only names "ar is
a numeral."
That is the same class this project has cured before by sealing a built
formula opaque: `[LJ-1.145]` measured 2,459 ms to below 1 ms by sealing
`satGraphAt`, and P-t licenses sealing a built formula wherever its consumers
do not look inside.

**The cure hypothesis:** define the numeral property opaque once, and state
the `arNum` fields through it:

```agda
opaque
  isNumeral : S → Type (ℓ-suc ℓ)
  isNumeral x = ∥ Σ[ n ∈ ℕ ] (x ≡ # n) ∥₁
```

then write `isNumeral (fst ar)` at the type sites and `unfolding isNumeral` at
the proof sites. If the inferred mechanism is right, the conversion checker
then meets a stuck head and stops the 8.4 s pull.

**Price, stated as a hypothesis and marked INFERRED:** about 25 in-fence lines
(one opaque alias in a shared module, the type-site rewrites, unfolding blocks
at the proof sites), buying back up to the whole 8.4 s. **Nothing here is
MEASURED at the cure site.** P-l forbids carrying `[LJ-1.145]`'s seal factor
onto this term: a seal that cured a `Typing.CheckRHS` coercion is a hypothesis
at a `Deserialization` site.

**The probe that prices it:** one edit to a renamed copy of the master
(`ProbeMinusBound.agda` already exists and carries the arNum content), seal
`isNumeral`, run the paired `--profile=internal` read, and compare
`Deserialization` against 9,664 ms. That is one cold run of about 140 s and no
master edit.

## 5. SHARED or WING-LOCAL

**The trigger is WING-LOCAL. The payload is SHARED machinery. The cure is
SHARED.**

- The trigger (the `arNum` fields) lives in `src/L/Condensation.lagda.md`, a
  GCH-wing master. The AC tower imports none of it, so only the wing pays the
  8.4 s. **The cost is wing-local.**
- The payload is the deserialization of shared interfaces
  (`L.Axioms.Numerals`, `L.Coding.Model`, Cubical's `InfinitySet`), which both
  towers already read. The wing's local spelling is what forces the full read.
- The cure, if it works, is one opaque alias in shared machinery that both
  towers can use, so it is worth landing once (DD4). The immediate benefit is
  the wing's.

## 6. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the rise tracks interface SIZE | **REFUTED. MEASURED.** +0.85 percent size against x8.1 time |
| the rise is `Bound`'s interface reading | **REFUTED. MEASURED.** `Bound`-only probe reads 1,238 ms |
| the rise is the `arNum` fields | **CAUSED. MEASURED.** arNum-only probe reads 9,664 ms |
| the rise is transient / page cache / contention | **REFUTED. MEASURED.** three flat cold runs today; loaded day reads higher, not lower |
| the 8.4 s is a fair price of content | **REFUTED. INFERRED.** 420 ms per tiny field is a spelling pathology, not content |
| a seal cures it | **UNPRICED. INFERRED.** named, not measured |
| the cost is shared | **REFUTED for the trigger.** The trigger is wing-local; the payload and cure are shared |
| I edited a master, committed, pushed, or ran `make check` | **MEASURED FALSE**, none of these |
| I ran more than one Agda process at once, or raised the cap | **MEASURED FALSE.** One at a time, `-A64m -I0 -M8g` throughout |
| a single invocation passed 30 minutes | **MEASURED FALSE.** Longest was 271 s (`--profile=serialize`) |

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-201/LJ-1.201-report.md`, read WHOLE. **TOOK:** section
  4.1 at `:255-280`, the term's four dates and the two ruled-out causes (page
  cache, contention), which this report does not re-test; section 8.5's
  narrower admissible law; section 10's classification table.
- `agents/tasks/LJ-1-185/runs/src_L_Condensation.int{1,2,3}.txt`. **TOOK:**
  the three raw cold profiles; `Deserialization` self 9,409 / 9,417 / 9,682
  and cumulative 9,955 / 9,954 / 10,230, read straight off the files, not the
  report about them. `master-batch.log` for the load record (3.04 to 3.65).
- `agents/tasks/LJ-1-155/runs/src_L_Condensation.int1.txt`. **TOOK:** the
  1,689 ms baseline at `:28`, and the load header (5.51 to 8.44).
- `agents/tasks/LJ-1-155/measure.py`, read WHOLE. **TOOK:** the cold protocol
  (stash the target interface, run, restore) and the output format; my cold
  harness re-implements only the shell around it because its `wait_for_quiet`
  would have blocked behind the sibling's live Agda for ten minutes.
- `agents/tasks/LJ-1-145/lj-1.145-report.md`, read section 0, 1, 4. **TOOK:**
  the seal cure measured 2,459 ms to below 1 ms (`:4.2`), the opaque status of
  `numeralL` and `numeralL-fst` (`:2.3`), and the `--profile=serialize`/module
  convention. This is the SHAPE of the cure hypothesis, never a transferred
  price (P-l).
- `archive/dev/TASKS-archived.md`: SURVEYED, NOT USED. The retired route holds
  single-account profiles only; nothing there bears on interface
  deserialization.
- `dev/LESSONS.md` at each entry: P-l (refuses the seal transfer), P-t (the
  seal licence), P-q (no line deletion to buy a ratio), C-12 (heap cap and one
  process), C-22 (this file existed before the first run), D-1 (abort criteria
  fixed before the run), C-42 (the refutation names the arNum site and does
  not measure its extent).

## 8. LITERATURE (DD18)

Nothing in the literature governs interface serialization.

## 9. PROBES

| file | question | verdict |
|---|---|---|
| `probe_closure_full.py` | did interface size grow? | NO: +0.85 percent |
| `ProbeMinusArNum.agda` | does `Bound` cause the rise? | NO: 1,238 ms |
| `ProbeMinusBound.agda` | does `arNum` cause the rise? | YES: 9,664 ms |
| `gen_probes.py` | build the renamed copies | generator |

Raw runs in `runs/`.
