# LJ-1.17 report: is the square law affordable at DD24?

## 1. THE VERDICT

NO SHAPE FITS.

The square law pair measures 41.36 s at the declared caliber. That is 28
to 42 percent of the wing's whole seconds budget for 11 to 17 percent of
its lines. No port and no ideal form reach the DD24 bar of 0.013193 s
per line. The refusal is the deliverable. It re-prices the wing.

The pair rate is 0.0322 s per line. That is 2.44 times the bar and 2.81
times the module baseline. The transfer to the consumer adds an
estimated 8 s. The wing cannot absorb the pair because the remaining
content cannot be built at the residue rate. The residue rate falls
below the cheapest measured class, P-m's 0.01 to 0.013 s per line.

Section 7 carries the measurement. Section 5 carries the budget
arithmetic. Section 2 answers the necessity question. Section 3 prices
the transfer. Section 4 prices the ideal form.

## 2. IS THE FULL SQUARE LAW NEEDED?

YES, in substance. The hoped-for negative answer does not materialize.

The chain consumes |Lset α| = |α| at arbitrary infinite α. The digest
records the two uses in 5.5's proof (`dev/literature/devlin-II5.md:147-158`;
the printed proof at `_build/literature/dev2.txt:1372-1384`). The upper
half needs the injection of the level into the ordinal. The lower half
is delivered. The level-size equation itself is a basic hierarchy fact,
proved in `dev2.txt:200-240`.

Devlin's proof of 1.1(vii) needs the square law at every infinite
cardinal and at every infinite limit ordinal. The successor step counts
formulas over L_β, whose cardinality is |β|. The count at the cardinal
needs the square law at |β|, an initial ordinal. The limit step reads
|⋃_{γ<λ} L_γ| ≤ Σ_{γ<λ} |γ| = |λ|. The equality needs |λ × λ| = |λ| at
the limit ordinal λ itself, or an injection of λ's index into |λ|'s
index. That injection is the transfer.

The tree has no weaker bound. The delivered `Bound` module takes the
pairing at β as a parameter (`src/L/StageCardinal.lagda.md:51-58`). It
proves nothing weaker. The review's section 4 closed the index-level
re-route. No other route to the level-size equation exists in the tree.

The two UNRESOLVED OCR items do not touch this question. Item 6.5 is
5.2's carrier subscripts. Item 6.6 is 2.2's display matrix. The digest
states the mathematics is identical on every candidate
(`devlin-II5.md:433-437`). I checked both. Neither bears on the counting.

## 3. THE NON-INITIAL TRANSFER

The archived square law holds at initial ordinals only. The archive says
so in its own prose (`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:956-963`).
`Init` requires `ω ∈ˢ α`, successor closure, and the no-injection clause
(`:974-978`). `Init ω` is uninhabited. The chain needs the level size at
arbitrary infinite ordinals (`devlin-II5.md:147-158`). The gap is real.

The gap is one injection: for every infinite ordinal λ, an injection of
`⟪ λ ⟫` into `⟪ |λ| ⟫`. The limit step of the level-size induction codes
the stage coordinate γ < λ into the cardinal. The count needs that code.
Two shapes exist. The cardinal-first shape needs this injection. The
delivered `Bound` shape needs the square law at every level ordinal β,
including every non-initial ordinal. Both are the same content class.
No honest shape avoids the non-initial ordinal arithmetic.

The injection is not free. `Card.least` returns the least ordinal κ
equinumerous to α with a TRUNCATED witness
`∥ ⟪ α ⟫ ≃ ⟪ κ ⟫ ∥₁` (`SquareLaw.lagda.md:599-634`; the prose at
`:583-598` says the honest bijection is not returned). The least-of
machinery needs a non-truncated witness. The truncation cannot supply
one. The honest bijection needs ordinal absorption arithmetic: the shift
at successors (delivered, `Shift` at `:652-771`) and a Cantor-style
coding at limits (not delivered). The archive's recap says the law at
non-initial ordinals stays named until the witness is carried through
the reduction (`:898-918`).

Price: 150 to 400 lines, same content class as the square-law core.
Basis: survey. The delivered shift is about 120 lines. The limit
absorption is the square law's own missing arithmetic. One best-effort
figure: about 250 lines at the pair's measured rate, about 8 s. The
transfer is an additional cost on any square-law port. It does not
improve the seconds picture.

## 4. THE IDEAL FORM

The ideal form is not materially cheaper than the port. The rewrite-side
exercise already ran. The archived modules ARE the presentation-reduced
form.

`[T98]` diagnosed the cost as presentation-bound. `[T99]` abstracted the
counting chase. The abstract chase checked in 1.28 s where the
analogy-guided form heap-exhausted at `-M8g` (`_build/l3.32-t98-report.md`;
`dev/LESSONS.md:2264`). `[T101]` landed the chase, 859.0 to 465.5 s.
`[T103]` reshaped the `h₀` pair, 470.6 to 64.4 s
(`_build/l3.32-t101-report.md`, `_build/l3.32-t103-report.md`). The
whole-tree profile then measured SquareLaw at 23.3 s
(`dev/ledger.toml:1796`).

The remaining seconds are the once-payment floor. `[T103]`'s after
profile shows `Initial.pair-inj` at 38.5 s and the two `comp₀-inj` at
6.0 s each. `[T121]`'s Pairing profile leaves `col→τ-fiber` at 18.8 s,
which the ledger calls the once-payment P-l predicts
(`dev/ledger.toml:2376-2382`). The law is explicit: sealing buys the
repeats, never the once (`dev/LESSONS.md:2357-2358`). A fresh write pays
the same once.

The one line-level waste is the Core and InitialCore mirror. The ledger
records 78 byte-identical and 150 to 200 near-identical lines
(`dev/ledger.toml:1412-1413`). An ideal form can parameterize the core
by the exclusion hypothesis and save about 230 to 280 lines. Those
lines are cheap after `[T103]`. The saving is in lines, not seconds.

Ideal-form estimate: 1,000 to 1,100 lines, about 41 s. Basis: the
measured pair, minus the mirror. Rate: 0.037 to 0.041 s per line. That
is 2.8 to 3.1 times the bar. The ideal form does not change the verdict.

Both shapes need the transfer of section 3 to reach the consumer. A
port that omits the transfer is worth nothing, however cheap it is.

## 5. SECONDS

MEASURED at the declared caliber. The protocol is in section 7.

| module | runs (s) | median (s) | in-fence | s/line |
|---|---:|---:|---:|---:|
| Pairing (scratch) | 18.58, 18.23, 18.06 | 18.23 | 376 | 0.0485 |
| SquareLaw (scratch) | 23.50, 23.13, 22.84 | 23.13 | 907 | 0.0255 |
| pair |  | 41.36 | 1,283 | 0.0322 |

The declared bar is 0.013193 s per line. That is the module baseline
0.011472 times the tolerance 1.15 (`dev/ledger.toml:2475-2525`). The
pair rate is 2.44 times the bar and 2.81 times the baseline.

The wing's whole seconds budget is 99.6 to 147.7 s
(`dev/ledger.toml:241-245`). The pair takes 41.36 s. That is 41.5
percent of the low end and 28.0 percent of the high end.

The scenario table, with the measured pair:

| scenario | lines | seconds | s/line | vs 0.013193 |
|---|---:|---:|---:|---|
| wing plus the delivered counting half | 1,394 | 5.46 | 0.0039 | 0.30x PASS |
| plus the square law pair, measured | 2,677 | 46.82 | 0.0175 | 1.33x FAIL |
| zero seconds for everything else | 2,677 | 41.36 | 0.0155 | 1.17x FAIL |

The fail does not depend on the rest of the wing's rate. Even at zero
seconds for everything else, the pair alone breaks the bar at the
current line count.

The budget framing is stronger. The rest of the wing, 6,270 to 9,914
lines, then has 58.2 to 106.3 s. That is 0.0059 to 0.0170 s per line.
The cheapest measured class, P-m, runs 0.01 to 0.013
(`dev/LESSONS.md:2419`). The wing contains measured instantiation
content. The ledger measured satisfaction content at 0.297 s per line
(`dev/ledger.toml:1754`), the top of the instantiation class
(`dev/LESSONS.md:2442`). The residue cannot absorb it.

One best-effort seconds figure: the square-law row at about 41 s,
measured. With the transfer, about 49 s, estimated. The transfer is
about 250 lines at the pair's measured rate. The row then takes 33 to 50
percent of the budget.

## 6. THE CONTENT CLASS

The pair sits between the two measured classes, closer to P-m.

| shape | s/line | class |
|---|---:|---|
| P-m parameterized floor | 0.01 to 0.013 | parameterized |
| DD24 bar | 0.013193 |  |
| Pairing, measured | 0.0485 | middle |
| SquareLaw, measured | 0.0255 | middle |
| P-n instantiation floor | 0.22 to 0.297 | instantiation |

Why the middle: the modules are parameterized in α, but they bind
concrete hierarchy operations at the ordinal carriers. The collapse runs
well-founded recursion over the product order on `⟪ α ⟫`. The fibers at
α and τ read members concretely. The membership proofs walk the union.
The Initial module instantiates the core at a concrete `Init` record.
The hot rows are this concrete instantiation tail.

The tail is the once-payment P-l predicts. The ordinal carriers'
computation rules must relate the stage to its body once
(`dev/LESSONS.md:2357-2358`). Abstraction cannot remove the once. The
presentation-reduction already spent its savings.

Per shape: the port is measured at 0.0322. The ideal form lands at the
same floor, 0.037 to 0.041 by the line estimate. Neither lands in the
parameterized class. A square law in the instantiation class cannot fit
any budget. The measured rate is already 2.44 times the bar.

The transfer lands in the same class. It is ordinal absorption
arithmetic at concrete carriers. It does not change the class verdict.

## 7. THE PAIRING MEASUREMENT

Made at the declared caliber, in a scratch copy, on today's tree.

First check, 19:11: LJ-1.15 was RUNNING with `agda=True`. The slots read
3/2. The brief forbids measuring while a sibling is live. A contended
measurement is void. I recorded the block.

LJ-1.15 completed at 19:14. Its final report exists
(`.claude/skills/codex-dispatch/.state/logs/LJ-1.15-20260810-182155-final.md`).
T77's record is a stale completion from Aug 5. Its log froze on Aug 5
20:58 and its final report exists. Re-check, 19:22: slots 2/2, no live
sibling. The machine was quiet. Measurement proceeded.

Scratch setup: I extracted the archived Pairing code fences into
`src/ProbeLJ117Pairing.agda`. The only edits are the module header and
two import re-points. The archived `L.WellOrder.Combinators` (`prodSWO`)
and `natSWO` are absent from today's tree, so I re-supplied them as
`src/ProbeLJ117Combinators.agda`, verbatim archived content. Both probes
typecheck against today's tree, exit 0. `V.Presentation` is delivered
today (`src/V/Presentation.lagda.md`).

Protocol: cold module, warm dependencies. The probe's `.agdai` moved
aside for each run. The 82 dependency interfaces stayed in the cache.
One Agda process. `GHCRTS="-A64m -I0 -M16g"`, the declared caliber
(`dev/ledger.toml:2475-2525`).

Results: Pairing median 18.23 s, runs 18.58, 18.23, 18.06. SquareLaw
median 23.13 s, runs 23.50, 23.13, 22.84. Pair total 41.36 s.

The ledger's retired-tree figures were 18.6 and 23.3 (`dev/ledger.toml:1796`,
`:1801`). The declared caliber confirms them. The pair is 41.36 s
against the recorded 41.9 s. The review's guess that the DD24 figure is
likely higher is not borne out for these two modules.

The measurement cost a partial port prerequisite: the two scratch
modules, verbatim archived content, 765 file lines total. The
measurement itself cost three runs per module, about 125 s of wall time.

## 8. DD4

The square law is ordinal arithmetic. Its types mention the ordinal
carriers `⟪ α ⟫`, the order type τ, and the hierarchy membership. They
mention no Def-tower content. Its imports are `V.*`, `L.Ordinal`,
`L.WellOrder`, and `FOL.ZFStructure`. `IsOrd` is about ordinals as sets,
generic over the towers.

Both towers consume the same pairing and square law. The digest's
section 4 lists the level-size equation as per-tower size, with the
ordinal arithmetic underneath shared (`devlin-II5.md:385-405`). The J
tower has the analogue |J_ρ^A| = H_ρ^M (`devlin-II5.md:411-417`). The
square law itself is tower-agnostic.

The shape I priced is shared content. Each tower reuses the identical
module. There is no cheaper Def-specific shape. The content is
tower-agnostic by construction. That is an argument for the shared
shape, and the shared shape is the only honest one.

The AC side may want the square law too. `[LJ-0.7]` found the per-tower
content is exactly two objects. A square law is neither. It should be
template content both proofs share. The DD4 answer does not depend on
the AC side's actual need.

D-26 does not bear here. The square law well-orders the ordinal's
members through regularity. It needs no syntax and no generation data.
D-26's syntax requirement applies to well-ordering a tower's stage.
That is the descent, a different row.

## 9. LITERATURE USED

- `dev/literature/devlin-II5.md:134-143` (1.4, Devlin 5.4). TOOK: the
  hull count is a count of formulas over the parameter set. The
  parameter set is the carrier of L_α.
- `dev/literature/devlin-II5.md:145-158` (1.5, 5.5 to 5.8). TOOK: the
  chain consumes |L_α| = |α| and |L_γ| = |γ| at arbitrary ordinals.
- `dev/literature/devlin-II5.md:272-277` (2.5, Step E). TOOK: the
  counting needs cardinal arithmetic on a countable formula set with
  parameters from X.
- `dev/literature/devlin-II5.md:278-284` (2.6, Step F). TOOK: 5.5 needs
  the level-size equation and initial-ordinal arithmetic.
- `dev/literature/devlin-II5.md:411-417` (5.2, II.1.1(vii)). TOOK: the
  level-size equation is generic cardinal arithmetic. The J tower has
  the analogue.
- `dev/literature/devlin-II5.md:346-348` (section 8, item 8). TOOK:
  |L_α| = |α| for α ≥ ω is a basic hierarchy fact.
- `_build/literature/dev2.txt:1357-1360` (5.4). TOOK: |M| = max(|X|, ω),
  the count.
- `_build/literature/dev2.txt:200-240` (1.1(vii)'s proof). TOOK: the
  successor step counts at the cardinal. The limit step uses
  Σ|α| = |λ|, which needs the square law at the limit or the transfer.
- `_build/literature/dev2.txt:1369-1384` (5.5). TOOK: the printed chain
  |γ| = |M| = |L_α| = |α| < κ.
- `dev/literature/devlin-II5.md:433-437` and `:500-530` (section 6, the
  two UNRESOLVED OCR items). CHECKED: neither touches the counting or
  the square law. Item 6.5 is 5.2's carrier subscripts. Item 6.6 is
  2.2's display matrix.
- SKIPPED: `devlin-II5.md` sections 6.1 to 6.4, 6.7, 7, 5.3, and
  `j-hierarchy.md`. WHY NOT: the resolved OCR items and the Jech
  cross-check do not bear on the square law. Section 5.3 is the cheap
  condensation instances. The J-side size analogue does not change the
  ordinal arithmetic underneath.

## 10. ARCHIVE USED

- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:956-963`: the
  initial-ordinal restriction prose. `:969-978`: `sq` and `Init`.
  `:599-634`: `Card.least` and the truncated witness. `:652-771`: the
  shift. `:988-1259`: the initial core. `:1259-1299`: the honest pair at
  initial ordinals. TOOK: the law's boundary, the truncation, and the
  delivered honest pair.
- `archive/rud-route/src/L/Ordinal/Pairing.lagda.md`, 376 in-fence.
  TOOK: the Gödel well-order, the collapse, the order type, and the
  pairing module, measured in section 7.
- `archive/rud-route/src/L/WellOrder/Combinators.lagda.md:209-210` and
  `archive/rud-route/src/L/WellOrder/Base.lagda.md:197-198`. TOOK: the
  scratch re-supply for the measurement.
- `_build/lj-1.6-review.md`: the commissioning numbers, the scenario
  table, and the non-initial gap. TOOK: the budget arithmetic.
- `_build/lj-1.6-report.md`: the delivered half and the refused upper
  half. TOOK: the `Bound` parameterization.
- `_build/lj-1.1-recon.md:135-149` (block 4) and `:251-253` (the
  633/376 caliber error). TOOK: the row structure and the error record.
- `_build/l3.32-t98-report.md`: the presentation-bound diagnosis.
  `_build/l3.32-t99-report.md`, `_build/l3.32-t101-report.md`,
  `_build/l3.32-t103-report.md`: the chase and the `h₀` reshape. TOOK:
  the archive is already the presentation-reduced form.
- `dev/ledger.toml:1796`, `:1801`: the 23.3 and 18.6 s figures.
  `:241-245`: the wing budget. `:2475-2525`: the ratio block and the
  declared caliber. `:1412-1413`: the Core and InitialCore mirror.
  `:2376-2382`: Pairing's profile and the once-payment. TOOK: the
  seconds record, the budget, the caliber, and the mirror.
- `archive/dev/TASKS-archived.md:119` (T98), `:120` (T85), `:94` (T59).
  TOOK: the rewrite history and the Init-ω red gate.
- `dev/LESSONS.md:2264` (P-l), `:2357-2358` (the once-payment), `:2419`
  (P-m), `:2442` (P-n), `:2528` (P-s), `:1316` (D-10). TOOK: the class
  certificates and the caliber warnings.

## 11. WHAT I AM NOT SURE OF

1. The scratch measurement re-pointed two imports and added two missing
   names. The content is verbatim archived code. The measurement runs on
   today's tree, not the retired tree. The ledger figures agree within 1
   percent, so the drift is small.
2. The transfer price, 150 to 400 lines and about 8 s, is a survey, not
   a measurement. No one has built the honest injection λ ↪ |λ|. The
   archive's prose says it is the counting's plumbing. That suggests it
   is buildable, not that it is cheap.
3. The ideal-form seconds assume the once-payment floor. The floor is
   measured at the module level, not re-measured for a deduplicated
   rewrite. The dedup lines are cheap after `[T103]`. The assumption is
   safe but not measured.
4. The rest-of-the-wing rates use P-m and P-n from the ledger. The
   wing's actual mix is unmeasured. The conclusion does not depend on
   the mix. Even all-P-m content at the floor does not fit the residue
   at the low end of the budget.
5. Whether the AC side actually wants the square law is not established.
   The DD4 answer does not depend on it.

Probe files `src/ProbeLJ117Pairing.agda`, `src/ProbeLJ117Combinators.agda`
and `src/ProbeLJ117SquareLaw.agda` were created for the measurement.
They are untracked by standing rule. They will not be committed. The
only written deliverable is this report.
