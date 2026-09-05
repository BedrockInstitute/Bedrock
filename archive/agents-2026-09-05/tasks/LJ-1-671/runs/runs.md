# [LJ-1-671] Run table

One Agda process per run. `run.sh` takes the file, an out-name, and a
wall cap (perl alarm; this macOS has no `timeout`). `GHCRTS=-A64m -I0
-M2g`, caliber from the pane, never set in the script. Every `.out`
carries the GHCRTS line, start and end stamps, and `EXIT=`.

| run | file | real | peak bytes | exit | what it measured |
|---|---|---|---|---|---|
| floor-1 | runs/Floor671.agda | 4.95 s | 851,214,336 | 0 | the interface cache is valid |
| atk-1 | runs/ATK-1.agda | 48.52 s | 1,911,406,592 | 42 | the structural skeleton with the residue as a hole; Agda does not print the hole's type |
| atk-2 | runs/ATK-1.agda | 2.58 s | 692,928,512 | 42 | the wrong-term trick; the goal type of the residue is printed (`∥ Σ[ x ∈ SL ] ⟨ (x ∷ K₀ ∷ γ ∷ v) ⊨c F ⟩ ∥₁`, `F` the renamed matrix) |
| atk-3 | runs/ATK-1.agda | 1200.04 s (cap) | 946,241,536 | 142 | the deep witness attempt; one frame step of the bounded matrix at the stage did not finish in 20 minutes |
| probe-3/4/5 | Probe671.agda | 2.62 / 3.42 / 3.56 s | 624,132,096 / 733,904,896 / 730,726,400 | 42 / 0 / 0 | the deliverable; probe-3 the intermediate red (module argument with a generalized variable), probe-5 the final green with the brief's obligation name |
| atk-4/5/6 | runs/ATK-1.agda | 2.56 / 3.59 / 3.21 s | 691,273,728 / 871,284,736 / 760,102,912 | 42 / 0 / 0 | the attempt record; atk-4 the intermediate red (`failWith` not in scope), atk-6 the final green |

The load-bearing measurement is atk-3: the full satisfaction of the
bounded matrix is not a matter of more clever witnesses; one clause
reduction in this context exceeds the run cap. See
`review-of-sat-at-packed.md`, section 3, Wall 3.
