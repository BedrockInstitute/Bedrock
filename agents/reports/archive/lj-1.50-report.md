# LJ-1.50: the 150-second certificate transfer, and the one step with no price

Status: COMPLETE. Written incrementally per C-22. The report uses
ASD-STE100. No commit, no push. No master edited: the cure the brief
prescribed was built in probes and measured, and it does not land.

## 1. THE VERDICT

**The variable-slot move does NOT remove the cost, and the number
stands.** The erase-to-Delta-0 certificate transfer costs 150 to
172 s user at every spelling measured:

| spelling | runs, user s | mean | spread |
|---|---:|---:|---:|
| concrete leaf, direct (control) | 152.19 / 150.31 / 149.73 | 150.74 | 2.46 (1.6 percent) |
| variable slots + instantiate once (the brief's cure) | 172.03 / 165.90 / 164.98 | 167.64 | 7.05 (4.2 percent) |
| linear recursion, projected count proofs, concrete leaf | 150.16 (one run) | | |

LJ-1.49's own baseline is 150.13 s user at the same caliber. The
variable-slot version is about 17 s SLOWER on the mean, and the
profile explains why: `ProbeLJ150Slots.EraseLeaf.transfer` (the module
BODY, at variable slots) holds 166,571 ms of a 168,579 ms check, while
the concrete instantiation at the end costs 57 ms. The elaborator
unfolds the BUILT tree to run the structural recursion, and it does so
identically at variables. The cost follows the formula's class (P-t:
the formula is built, not a telescope hypothesis), not the slot
spelling. The diagnosis "instantiation-class cost" does not hold for
this piece; the instantiation is the cheapest part of it.

The full matrix does not finish at either spelling within the stop
bounds (section 3). One measured piece, 150 to 172 s, exceeds the GCH
side's WHOLE seconds budget of 99.6 to 147.7 s
(`dev/ledger.toml:305`, from the DD24 bar 0.012716 = 0.011057 x 1.15
at `:2590` and `:2810`). **The route as measured does not fit.** The
exit is not a cheaper spelling of this transfer; it is a restatement
of the connector's obligation on the delivered `EraseTransfer` route
(`src/L/Condensation.lagda.md:273-306`), which never runs
erase-Delta-0 at all: it transports the ORIGINAL certificate by
`abs₀` and shifts by the erase-inv equality. Whether the adequacy
connector can ride that route is a design decision for the connector
build, and it is not measured here.

Because the number stands, the second task is not started: the price
of the collapse-of-the-level for `levelIn` does not matter yet
(section 4).

## 2. THE NUMBER: THE CERTIFICATE TRANSFER AT VARIABLE SLOTS

The obligation is `Δ₀ (Cnt.erase φ refl)` from `Δ₀ φ` for the built
leaf `DefBodyB {0} zero ... zero` at the class carrier. LJ-1.49
measured it directly at the concrete leaf: 150.13 s user. The brief
prescribes P-u's cure: build the certificate at variable slots and
instantiate once at the end, so the elaborator never normalizes a
built tree at a concrete argument.

Probes, all cold (own interface moved aside), warm dependencies, one
process, `GHCRTS="-A64m -I0 -M8g"`:

| probe | what it measures | runs, user s |
|---|---:|---|
| `ProbeLJ150Control` | `erase-Δ₀ defb refl Δ₀-defb` at the concrete leaf | 152.19 / 150.31 / 149.73 |
| `ProbeLJ150Slots` | `EraseLeaf.transfer` at variable slots, then `EraseLeaf.transfer {0} zero ... zero` once | 172.03 / 165.90 / 164.98 |
| `ProbeLJ150Linear` | the recursion with count proofs projected (`plus-zero-l`/`plus-zero-r`), concrete leaf | 150.16 |

The profile of `ProbeLJ150Slots`:

```
Total                              168,579ms
ProbeLJ150Slots.EraseLeaf.transfer 166,571ms
ProbeLJ150Slots.transfer-concrete       57ms
```

The module body at VARIABLES is the entire cost; the concrete
instantiation is 57 ms. The linear-recursion variant answers the
secondary hypothesis (the `_` count metas in the delivered
`erase-Δ₀`, `src/L/BoundedSubset.lagda.md:505-517`, force a `countFo`
traversal per node): projecting the proofs changes nothing
(150.16 s). So the cost is the recursion over the built tree itself:
the elaborator must unfold the tree to run the structural recursion,
and variables versus concrete arguments is immaterial to that
unfolding. This is P-t's class exactly: the formula is BUILT, so it
unfolds at every use, whatever the carrier spelling.

## 3. THE FULL MATRIX

Two stop-bounded attempts, both interrupted, no real number:

| probe | spelling | result |
|---|---|---|
| `ProbeLJ150MatrixSlots` | variable slots + instantiate once | interrupted after about 570 s |
| `ProbeLJ150MatrixLinear` | linear recursion at the concrete `LevelHood0.matrix` | interrupted after about 520 s |

Both are STOPS, not walls (C-36): each produced a lower bound only.
The scaling is consistent with the leaf measurement: the matrix nests
the leaf at two arities inside the step and approximation frames
(`GraphB` takes `ψs` and `ψa`, `src/L/Condensation.lagda.md:2464-2481`;
`LevelHood0.matrix` is `LH.levelHoodB`,
`src/L/BoundedSubset.lagda.md:520-531`), so the matrix is several
times the leaf, and a recursion that costs 150 s on one leaf cannot
finish the matrix inside any budget that fits the wing. No projected
finish time is offered: a projection from the leaf is a hypothesis,
not a price (P-l).

## 4. THE COLLAPSE-OF-THE-LEVEL PRICE

NOT PRICED. The brief orders it second, and only if the 150 s does not
stand. It stands at every spelling (section 2), so the price of
`levelIn`'s collapse-of-the-level step does not matter yet. The return
stops here per the brief's own stop rule.

## 5. THE MEASUREMENTS

Caliber: USER seconds from `/usr/bin/time -p`, cold probe (own
interface moved aside), warm dependencies, one process, quiet machine
(load read 3.8 to 4.3, similar to LJ-1.49's 4 to 6). No heap
exhaustion at any run; every completed run exited 0 under the cap.

| piece | runs, user s | mean | spread | note |
|---|---:|---:|---:|---|
| concrete leaf, direct (control) | 152.19 / 150.31 / 149.73 | 150.74 | 2.46 (1.6 percent) | LJ-1.49 baseline 150.13 |
| variable slots + instantiate once | 172.03 / 165.90 / 164.98 | 167.64 | 7.05 (4.2 percent) | profile: body 166.6 s, instantiation 0.057 s |
| linear recursion, concrete leaf | 150.16 | n/a | n/a | one run |
| full matrix, variable slots | interrupted about 570 s | n/a | n/a | stop, not a wall |
| full matrix, linear | interrupted about 520 s | n/a | n/a | stop, not a wall |

The verdict does not sit inside any spread: the variable-slot mean is
17 s ABOVE the control mean, and both sit above the GCH wing's whole
seconds budget (99.6 to 147.7 s, `dev/ledger.toml:305`).

## 6. THE DD4 ANSWER

No new template landed: the shared move the brief prescribed (certify
at variable slots, instantiate once) was built and measured, and it
does not change the class. The J tower inherits the measurement, not a
code layer. The delivered `EraseTransfer` template
(`src/L/Condensation.lagda.md:273-306`) is the route that avoids the
class entirely, because it never runs erase-Delta-0: it transports the
ORIGINAL certificate by `abs₀` and shifts by the erase-inv equality.
Both towers already share that template; the question the adequacy
connector must answer is whether its obligation can ride the same
route. That is a design decision, not a measurement, and it is the
exit this report names.

## 7. ARCHIVE USED

- `_build/lj-1.49-report.md`, read WHOLE. Took the residue's
  decomposition, the wall statement (`:42-44`, `:86-94`), the
  measurements table (`:113-125`) and the not-sure list (`:199-217`).
- `_build/lj-1.7-review.md`, read the named sections WHOLE. Took the
  overturns (`:12-35`), the count decomposition (`:100-160`), the
  `erase-Δ₀` zero-consumer fact (`:159`), and the not-sure list
  (`:325-371`).
- `_build/lj-1.24-report.md`, read WHOLE. Took the abstract-source
  cure's shape (29.1 to 2.3 s) for contrast with this failure.
- `_build/lj-1.47-report.md`, read WHOLE. Took the consumer-price
  cure's shape (43.26 to 7.94 s) and the caliber discipline.
- `src/ProbeDD25G1.agda`, `src/ProbeDD25G2.agda`,
  `src/ProbeDD25G3.agda`, read WHOLE. They bear on cure 2 (the
  `collapseCode` deletion), not on the certificate transfer; took the
  house-style citation and the two-leg composite context only.
- `src/ProbeLJ149.agda`, read WHOLE. The concrete objects this
  dispatch measured.
- `src/L/BoundedSubset.lagda.md`, read `erase-Δ₀` (`:505-517`),
  `LevelHood` (`:50-130`), `LevelHood0` (`:520-560`),
  `HullStage.Condense` (`:596-715`) and `Co` (`:952-1093`).
- `src/L/Condensation.lagda.md`, read `EraseTransfer`
  (`:273-306`), the house style (`:1111-1114`), the leaf internals
  (`:1463-1790`), `DefBodyB` (`:2316-2336`), `StepB`/`StepAtB`
  (`:2417-2445`) and `GraphB` (`:2464-2481`).
- `src/FOL/Count.lagda.md`, read `erase`/`erase-inv` and
  `plus-zero-l`/`plus-zero-r` (`:595-637`).
- `dev/ledger.toml`, read the seconds budget (`:305`), the DD24 bar
  (`:2590`, `:2810`).
- `dev/LESSONS.md`, via `scripts/rules.py --for build` and the
  entries for P-t, P-u, P-v, C-31 to C-37, D-26, D-29, D-30, plus the
  transplant table (`:2328-2410`).

Nothing else in `archive/` was read. WHY NOT: the retired route's
crossings do not bear on an elaborator cost on this tree's own code.

## 8. LITERATURE USED

NONE. This is an elaborator cost measurement on this tree's own code;
Devlin asserts absoluteness where this proves a transfer, so no
literature entry bears (DD18). `dev/literature/` was not opened.

## 9. WHAT I AM NOT SURE OF

1. The matrix's real finish time: both attempts were stopped, so only
   lower bounds exist (about 570 s and about 520 s). The leaf numbers
   exclude any finish inside budget, which is the verdict's basis.
2. Whether the adequacy connector can be re-stated on the
   `EraseTransfer` pattern (`abs₀` on the original certificate plus
   erase-inv congs), deleting this cost instead of paying it. The
   template exists and is green; the connector's obligation is not
   built, so this is a design decision, not a measurement.
3. The linear-recursion variant has one run only (150.16 s); its
   verdict (no change) is corroborated by the slots/control means, so
   the single run does not decide anything alone.
4. The machine load read 3.8 to 4.3 during the runs, not zero; user
   seconds are the caliber and the spreads are reported, and the
   verdict does not sit inside a spread.
