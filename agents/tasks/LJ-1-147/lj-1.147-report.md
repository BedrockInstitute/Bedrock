# LJ-1.147 report: seal `satGraphAt`, and measure what the seal buys

**Status: IN PROGRESS.**

## 0. THE ANSWER

TBD.

## 0.1 The method, fixed before the first run

**The instrument is `scripts/check-ratio.py`**, at the ledger's own caliber
`GHCRTS="-A64m -I0 -M8g"` (`dev/ledger.toml:2632`), which the tool reads from
`ratio.ac_baseline_ghcrts` and passes to `check-timing.time_module`
(`scripts/check-ratio.py:143`). Every module is timed COLD with its
dependencies WARM: the tool moves that module's own `.agdai` aside and puts it
back (`scripts/check-timing.py:254-271`).

**Three instruments, each run before and after:**

1. the whole declared wing, 12 masters, which contains
   `src/L/Condensation.lagda.md`;
2. the four masters OUTSIDE the wing that the seal touches:
   `L/Coding/Graph`, `L/Coding/Powerset`, `L/Choice/Internal`,
   `L/Choice/Adequate`. The last two are the AC wing (C-40);
3. `agda --profile=definitions` on `src/L/Condensation.lagda.md`, cold, which
   is what MEASURES the four `SatGraphAgree` definitions that carry the
   `unfolding` block.

**ONE agda process throughout, cap never raised.** The load is recorded beside
every figure and the run count is stated with it.

## 0.2 Machine load and run count, beside every figure

| run | when | load 1m / 5m / 15m | result |
|---|---|---|---|
| BEFORE 1, wing | 19:10 to 19:14 | 3.93 / 4.56 / 4.53 before, 4.49 / 4.86 / 4.68 after | wing 214.25 s, `Condensation` 124.53 s |

Raw output: `agents/tasks/LJ-1-147/runs/before-1.txt`.

## 1. THE SEAL

TBD.

## 2. WHAT `unfolding` COST. MEASURED

TBD.

## 3. THE MASTER, before and after

TBD.

## 4. THE CONSUMERS (C-40)

TBD.

## 5. THE WING against the bar

TBD.

## 6. THE AC SIDE (DD4)

TBD.

## 7. WHAT REMAINS OF THE GAP

TBD.

## 8. LITERATURE (DD18)

TBD.

## 9. ARCHIVE USED

TBD.

## 10. NEGATIVES, classified

TBD.
