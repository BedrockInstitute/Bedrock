# LJ-1.669 runs

One Agda process per run. Caliber from the pane, never set here.
Harness: `runs/run.sh`. Guard 1500 s (perl alarm).

| stamp (UTC) | run | file | EXIT | real s | peak RSS |
|---|---|---|---:|---:|---:|
| 2026-08-26T14:41:39Z | floor-0 | Probe669.agda | 0 | 3.26 | 709967872 |
| 2026-08-26T14:41:56Z | wall | Wall669.agda (temp copy of Wall669.agda.txt, removed) | 42 | 2.96 | 704692224 |
| 2026-08-26T14:42:58Z | wall-ii | Wall669-ii.agda (temp copy of Wall669-ii.agda.txt, removed) | 42 | 3.29 | 704331776 |
| 2026-08-26T14:44:36Z | final-0 | Probe669.agda | 0 | 4.00 | 686243840 |

GHCRTS on every `.out` header: `[-A64m -I0 -M2g]`.
