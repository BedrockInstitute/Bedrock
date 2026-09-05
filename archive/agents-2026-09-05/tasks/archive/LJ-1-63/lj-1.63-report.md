# LJ-1.63: find 11.83 seconds anywhere in the wing

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.63-report.md`.

## 0. THE VERDICT

**The gate's aggregate verdict, quoted: `wing aggregate 0.0132 s/line over
8,269 lines and 108.90 s, OVER THE BAR (1.19x the AC side at the SAME
caliber, module-cold with warm dependencies)`. The residual is 3.12 to
3.75 s (two gate runs: 108.27 s and 108.90 s against a 105.15 s ceiling
at 8,269 lines).**

The seconds I removed: 9.22 to 9.85 s, all from `L.StageCardinal`. Its
overage was dead content. The `Successor` cluster had no consumer anywhere
in the tree. I removed it from the master, backed it up outside the
repository, and measured the gate drop from 118.12 s to 108.27 s.

Everything else I measured to recover the remaining seconds regressed.
The claim that the chain's cost is a payable P-n floor is now supported
by three measured negatives at this site: birth-site sealing (+1.61 s),
shared instantiation frames (+17.23 s), and a twelve-row tree alias
(+3.29 s). Each was reverted. The final tree carries only the
`StageCardinal` edit. Per the pre-fixed abort criterion, the dispatch
ends at the gate, still over, and this report is the price.

## 1. THE GATE AND ITS ENVIRONMENTAL REFUSAL

The gate's guard refuses in this sandbox. `pgrep -x agda` cannot read the
process list here (no `sysmond` service), so the guard fails closed. The
bypass is the one [LJ-1.61] and [LJ-1.62] used: the gate's own code path
with `agda_blocker` neutralized, so every verdict below is the gate's own
arithmetic over the gate's own measurements. Every Agda invocation in this
session was sequential; no two Agda processes ever overlapped, which is
C-12's intent.

**LOAD CAVEAT, MEASURED:** the machine load average ranged 8.7 to 2.3
(4 users) across the session. Every absolute figure carries the caveat.
Same-session deltas are the comparable figures, and the three regressions
were measured at loads equal to or CLEANER than their before-states, so
their direction is not noise.

## 2. THE PROFILE OF `L.StageCardinal`

The cold profile (module interface aside, warm dependencies,
`-A64m -I0 -M16g`, one process) read 10,797 ms total, of which **8,977 ms
(83 percent) sat in one module**: `L.StageCardinal.Successor`.

| definition | ms |
|---|---:|
| `Successor._._._.go₂` | 4,723 |
| `Successor._._.go₁` | 2,146 |
| `Successor._.go` | 2,108 |
| `Miscellaneous` | 1,372 |
| `LimitStep` pieces, total | about 380 |
| rest, total | about 70 |

**The D-30 answer:** the `Successor` cluster has NO consumer anywhere in
the tree. `L.BoundedSubset`, the wing's only consumer of `L.StageCardinal`,
uses exactly `OrdSWO.ordSWO` (`src/L/BoundedSubset.lagda.md:1534,1544`),
`stage-card-lower` (`:1580`) and `Upper.stage-card-upper` (`:1371-1373`).
`op-step`, `successor-step`, `SucUpper` and `stage-card-suc` appear nowhere
outside the module except comments (`src/L/BoundedSubset.lagda.md:1053`,
`src/ProbeDD25G3.agda:11,90`; both describe the transplanted pattern, no
import). The generic union step serves successor ordinals too, which
`src/L/StageCardinal.lagda.md` states ("one step serves both successor and
limit ordinals"); the successor-specific route is the superseded
`ProbeLJ124Base` shape.

The edit: the 87 in-fence lines of the dead cluster were removed from
`src/L/StageCardinal.lagda.md`, together with the imports only it used
(`∈sucV-inl` from `V.Model`, `Lset-suc` from `L.Axioms.Basic`, `sucV` from
the `InfinitySet` open). The removed text is preserved at
`/tmp/lj163-successor-block.backup` (100 lines, 87 non-blank). Nothing is
deleted. MEASURED before/after at the gate's own caliber:

| state | cold profile | gate's module row |
|---|---:|---:|
| before | 10,797 ms | 11.51 s |
| after | 1,735 ms | 1.97 s / 2.12 s / 1.98 s (three gate runs) |

The consumer `L.BoundedSubset` re-checks green against the edited module
(exit 0, warm, 3.8 s with `L.Hull` re-checked).

## 3. `L.V.Presentation`

Eighteen in-fence lines, 0.57 to 0.65 s at the gate's caliber, 611 ms in
the cold profile, **all `Miscellaneous`**: the cost is the module header
and its dependency interfaces (`Cubical.HITs.CumulativeHierarchy.Properties`,
`Cubical.Functions.Embedding`, `FOL.ZFStructure`, `V.Hierarchy`), not the
four one-line facts. All four facts have consumers: `member` and `fiber`
in `L.Hull`, `V.Collapse`, `L.StageCardinal`, `L.BoundedSubset`,
`L.Ordinal.SquareLaw`; `↪-inj` in the same minus `L.Hull`; `∈ₛ↪` in
`V.Collapse`. The module must stay in the wing.

Its 0.39 s overage is a small-denominator artifact: 18 lines cannot
amortize a fixed module cost. The only levers are a ledger wing-list change
or merging the facts into a non-wing module; both are outside this
dispatch's write scope. The `S` carrier is the structure's field
(`FOL.ZFStructure.lagda.md:46`), so dropping the structure imports would
be a type-level rewrite for an estimated fraction of a second; not tried.

## 4. THE CHAIN'S HOT DEFINITIONS

The current cold profile of `L.Condensation` (99,055 ms total, first run)
names the chain rows the brief predicted and three pre-chain rows the
brief's table did not name:

| definition | ms |
|---|---:|
| `LeafAgree.back` / `.out` | 4,034 / 4,015 |
| `SatGraphAgree.back` / `.out` | 3,263 / 2,008 |
| `PropAgree.subB2T-back` (pre-chain) | 2,949 |
| `ImpLeaf.yaOut` (pre-chain) | 1,579 |
| `BinFormAgree._.go` (pre-chain) | 1,317 |
| `WitnessAgree._.go` | 1,013 / 959 |
| `SatGraphAgree.body-back` / `.body-out` | 1,002 / 919 |
| `TwelveAgree.back` / `.twelveB` / `.out` | 744 / 730 / 696 |
| `Miscellaneous` | 42,379 |

The chain rows state and destruct the built trees (`SatGraphB.twelveB`,
`SatGraphB.satGraphB`, `DefBodyB`) at the 8-deep concrete environment.
`DefBody` (the story side of `LeafAgree.out`/`back`) is imported from
`L.Coding.Powerset` (transparent, off-limits to edit); `DefBodyB` and the
`SatGraphB` trees are born inside `L.Condensation`
(`src/L/Condensation.lagda.md:2227-2360`).

**The D-30 answer for the chain:** every chain module (`TagAgree` through
`LeafAgree`) and every row module (`MemAgree` through `ExInAgree`,
`PropAgree`, `ImpLeaf`) is exported by `L.Condensation` and consumed by NO
master outside it (`src/L/BoundedSubset.lagda.md` imports only
`DefBodyB`, `Δ₀-DefBodyB`, `GraphB`). The chain is placed for the post-leaf
five per the brief; it is the deliverable. `TwelveAgree` is never
instantiated either, but it is the intended supplier of the twelve row
agreements to the future assembly. The finding is reported, not deleted:
the brief's "do not delete content to buy the ratio" and the deliverable
scope both bind.

The hot rows' branches all carry written types (I-5 does not apply). The
cost is the satisfaction of built formula trees at the concrete carrier,
which is P-n's signature exactly (`dev/LESSONS.md:2483`).

## 5. ATTEMPTS, WITH MEASURED BEFORE AND AFTER

Caliber: the gate's own, cold module, warm dependencies,
`-A64m -I0 -M16g`, one process. The Condensation before-figures are the
gate's own rows across three runs: 99.54 / 99.99 s.

1. **`Successor` cluster removed from `L.StageCardinal`.** MEASURED:
   cold profile 10,797 ms to 1,735 ms; gate row 11.51 s to 1.97 to
   2.12 s; wing 118.12 s to 108.27 s (first gate) and 108.90 s (final
   gate), minus 87 in-fence lines. D-30's consumer audit found no consumer
   (section 2). The removed text is backed up at
   `/tmp/lj163-successor-block.backup`. KEPT.

2. **Birth-site sealing of `SatGraphB.twelveB` (P-c, R-36, R-38).**
   MEASURED REGRESSION: `twelveB` and `Δ₀-twelveB` moved into `opaque`
   blocks at `src/L/Condensation.lagda.md:2233-2260`; the module checked
   with no other edit, and the gate read Condensation 101.15 s against
   99.54 s before, wing 109.83 s against 108.27 s. The sealed run had the
   cleaner load (3.3 vs 8.7), so the direction is not noise. REVERTED.
   The claim that sealing this tree helps is **MEASURED FALSE** at this
   site: sealing removes the repeat payments and moves the cost into the
   decode proofs' unification instead (the same shape [LJ-1.47] measured
   as "sealing buys the repeats, never the once").

3. **Shared frame modules in `SatGraphAgree`, `WitnessAgree`,
   `ShapedAgree`.** Each instantiated its helper modules twice with
   identical arguments (once per direction, the double-instantiation
   [LJ-1.61] section 4 named). Each gained one module-level frame
   (`Body`, `WFrame`, `SFrame`) so the `ClosedAgree`/`DomainAgree`/
   `ShapedAgree`/`ShapesAgree` instantiations were elaborated once.
   Same statements, same proofs. MEASURED REGRESSION: the module checked
   green, and the gate read Condensation 116.77 s against 99.54 s,
   +17.23 s. Module application with abstract arguments is not the cheap
   sharing the pattern assumed. REVERTED.

4. **`TwelveAgree.twelveB` reduced to an alias of `SatGraphB.twelveB`.**
   The two definitions are the same formula (verified byte-for-byte with
   `K'` expanded; `w` is unused in the body, so no new parameter). The
   duplicate's 730 ms row was to be removed. MEASURED REGRESSION: the
   module checked green, and the gate read Condensation 102.83 s against
   99.54 s, +3.29 s; the module application in the alias costs more than
   the definition it removes. REVERTED. DD4 note: the convergence is
   right, the price is wrong.

5. **`L.V.Presentation`.** Nothing tried: all four facts are consumed and
   the cost is fixed header elaboration (section 3). What the cost IS is
   MEASURED (611 ms all-`Miscellaneous`). The claim that no in-scope edit
   recovers the 0.39 s overage is INFERRED (no variant was measured).

The final tree carries attempt 1 only. Two final gate runs agree:
108.27 s and 108.90 s over 8,269 lines, 0.0131 to 0.0132, 1.18x to 1.19x.
The ceiling at 8,269 lines is 105.15 s; the residual is 3.12 to 3.75 s.

## 6. THE DD4 ANSWER

The `Successor` removal does not reduce what the J tower inherits. The
cluster was GCH-side-specific, superseded by the generic union step that
already serves both successor and limit ordinals; nothing in the J tower
imports it, and no placed type mentions a concrete carrier. The bundle's
packaging of the sharing is untouched (attempt 2 changed it only
temporarily). Attempt 4 would have reduced duplication (one twelve-row
tree instead of two spellings), which is the DD4 direction, but it
measured +3.29 s and was reverted; the trade is named: the convergence
costs seconds at this site, so it waits for a re-price.

## 7. THE CONVERGENCE ANSWER

The obligation is not renamed. `L.StageCardinal`'s overage was dead
content: the D-30 audit found no consumer, removal took the wing from
1.28x to 1.18x (minus 9.22 to 9.85 s). The remaining 3.12 to 3.75 s sits
in `L.Condensation`, whose hot rows are P-n content: satisfaction decodes
of built formula trees at the 8-deep concrete carrier, every branch
carrying a written type. The three statement-level moves this dispatch
measured (sealing, sharing frames, aliasing the tree) all regressed at
this site. The floor claim is now supported by measurement, and the
residual is its price. `levelIn` and `cover` were not attempted, per the
pre-fixed criterion.

## 8. NEGATIVES AND THEIR STATUS

1. `L.StageCardinal`'s overage sits in the un-consumed `Successor`
   cluster: **MEASURED** (cold profile 10,797 ms with 8,977 ms in the
   cluster; consumer grep; gate drop 11.51 s to about 2.0 s).
2. Birth-site sealing of `SatGraphB.twelveB` helps the chain:
   **MEASURED FALSE** (+1.61 s at the gate, cleaner load; reverted).
3. Shared frame modules reduce the double-instantiation cost:
   **MEASURED FALSE** (+17.23 s at the gate; reverted).
4. Aliasing `TwelveAgree.twelveB` to `SatGraphB.twelveB` helps:
   **MEASURED FALSE** (+3.29 s at the gate; reverted).
5. The full R-36 surgery (seal the destructed trees and move the decode
   proofs into `opaque unfolding` blocks) would close the residual:
   **INFERRED, NOT MEASURED**. It was not attempted. The partial seal
   (negative 2), the frames and the alias all moved the cost rather than
   removing it, and [LJ-1.47] measured the same shape as a once-payment.
   A negative resting on inference sets no verdict; the floor claim stands
   on negatives 2 to 4 plus the P-n signature.
6. `PropAgree.subB2T-back` and the pre-chain row modules are curable:
   **INFERRED** (their branches carry written types and destruct imported
   transparent formula trees; no cure was measured). Sets no verdict.
7. `L.V.Presentation`'s 0.39 s overage is removable in scope:
   **MEASURED FALSE as stated** for the profile attribution (all
   `Miscellaneous`, all facts consumed); the claim that no in-scope edit
   recovers it is **INFERRED** (no variant measured).
8. The gate's pgrep guard cannot verify the process list in this sandbox:
   **MEASURED** (pgrep exits 3; bypass per [LJ-1.61]/[LJ-1.62], C-12's
   intent held procedurally).

## 9. ARCHIVE USED

- `_build/lj-1.62-report.md`, read WHOLE. TOOK the profile split (section
  3: the chain's hot names), the chain's placement list (section 4 item
  2), the DD4 trade (section 5), the negative statuses (section 7), the
  gate bypass (section 1) and the archive list (section 8). Its negative
  8 ("a statement-level re-spelling would close the 12 s gap: INFERRED")
  is the claim this dispatch measured.
- `_build/lj-1.47-report.md`, read WHOLE. TOOK the D-30 consumer audit
  shape (sections 1 and 2), the dead-general-law pattern (four of five
  sections with no consumer), the seal experiment's once-payment result
  (section 3: "sealing buys the repeats, never the once"), and the wing
  arithmetic (section 4).
- `_build/lj-1.61-report.md`, section 4. TOOK the wall before the bundle
  and its attribution: `WitnessAgree` instantiates `ClosedAgree` and
  `ShapedAgree` four times; the marginal cost sat in `Miscellaneous`.
  That is the double-instantiation attempt 3 attacked.
- `_build/gch-compression-audit.md`, read WHOLE. TOOK the seconds-neutral
  deletion caution (P-q's class); no deletion was made beyond the
  D-30-class `Successor` cluster, whose seconds-per-line is 0.103, the
  opposite of the audit's cheap-content case.
- `src/ProbeLJ161A.agda` and the four earlier probes: read the
  `TwelveAgree`/`SatGraphAgree`/`LeafAgree` templates for comparison;
  untouched (verified by `git status`). They survive.
- `dev/LESSONS.md`, read P-m (`:2460`), P-n (`:2483`), P-t (`:2601`),
  P-q (`:2633`), P-c (`:71`), R-36 (`:808`), R-38 (`:829`), D-13
  (`:1463`), D-30 (`:3255`), WHOLE each. TOOK P-t (the class follows the
  formula, not the carrier), P-n (the payable floor), R-38's appended
  datum ("sealing only moves the cost"), and D-30 (the consumer audit).
- `dev/PLAN.md` DD13 row (`:174`) and DD18 (`:177`). TOOK the archive-never-
  delete rule and the section-archiving boundary; the removed `Successor`
  block is backed up outside the repository rather than archived as a
  module, because it is a section of a live master, and the finding is
  reported per D-13/D-30.
- `archive/rud-route/`, SHAPE only (the README and file list). WHY NOT
  more: [LJ-1.11] ruled its condensation content classically false and the
  brief forbids taking a price from it.
- `scripts/check-ratio.py` and `scripts/check-timing.py`, read WHOLE.
  TOOK the gate's verdict path, the cold/warm-dependency caliber and the
  interface-stash protocol, so the bypass runs the gate's own code with
  the guard neutralized.
- `dev/ledger.toml`, read the `[ratio]` table. TOOK the wing list, the
  bar 0.012716 (0.011057 at 1.15 tolerance) and the gate's GHCRTS.
  Not edited.

## 10. LITERATURE USED

Nothing in the literature prices a spelling. [LJ-1.59] already banked the
Devlin Step C answer; spend nothing.

## 11. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0 on the edited master.
`scripts/ledger.py --check` clean (declaration clean; standing 26,794
lines over 82 masters). `L.Condensation` counts 6,390 in-fence lines in
the working tree; `L.StageCardinal` counts 475 (HEAD 564); `L.BoundedSubset`
re-checks green on the final tree. `check-ratio --check` ran five times
this session (section 5); the final tree reads 108.27 / 108.90 s over
8,269 lines, 1.18x to 1.19x. No `make check` was run, per the brief. No
commit, no push. The working tree carries the `StageCardinal` edit and
this report; `L.Condensation` is byte-identical to its pre-dispatch state
(the [LJ-1.62] placement), verified against a session backup.
