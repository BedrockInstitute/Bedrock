# LJ-1.46: gate LJ-1.7, the bounded-subset lemma (Devlin 5.5)

Status: COMPLETE. Read-only recon. No Agda run. No make check. No commit,
no push. Written incrementally per C-22. The report uses ASD-STE100.
Every figure comes from the record and from reading, never from a run:
`[LJ-1.45]` is measuring timings on this machine and I kept it quiet.

## Verdict

**LJ-1.7 prices at about 1,675 naive in-fence lines center, range 1,290 to
2,230, and about 36 seconds center, range 22 to 75. The basis is a sum of
eight obligations. Two anchors are MEASURED: the condensation limit case at
124 lines, and the `[LJ-1.19]` closure probe at 30 body lines. The Code
count at about 120 lines for about 2 seconds is ESTIMATED by its own
report. The rest are surveys from `[LJ-1.12]`, `[LJ-1.21]`, `[LJ-1.26]`
and the delivered modules. The one widest unmeasured term is the condensation
theorem assembly, about 850 lines center, range 700 to 1,100, and its
   seconds class. The probe that measures it is in the probe section
   below.**

The DD24 verdict is negative at the center and fragile at the floor. The
bar is 0.011057 x 1.15 = 0.012716, about 0.0127 seconds per line
(`dev/ledger.toml:2589-2610` and `:2810`). The GCH side today measures
0.0131 over 6,407 lines and 84.13 seconds, OVER the bar, at the
`[LJ-1.44]`-era measurement. `[LJ-1.45]` has landed a cure in flight: the
aggregate estimate is about 77.6 seconds over 6,407 lines, 0.0121, under
the bar (`_build/lj-1.45-report.md:147-148`, ESTIMATED, set D still
measuring). Adding LJ-1.7 at the center gives 8,082 lines and about 113.6
seconds, 0.0141, about 10 percent OVER the bar. The headroom at 8,082
lines is about 25 seconds. LJ-1.7 exceeds it by about 11 seconds at the
center. Even at the parameterized floor, 22 seconds over 1,290 lines, the
aggregate lands 99.6 over 7,697, 0.0129, inside the noise band at the
bar. **5.5 must not be priced as if there were room. It consumes the
whole headroom and breaches at the center. The verdict turns on the
seconds class of the condensation transfer, which is exactly what the
probe measures.**

## Obligations and what discharges each

Devlin 5.5's proof (`dev2.txt:1372-1385`): pick alpha below kappa with
x inside L_alpha; take a limit lambda with x in L_lambda; take the hull
M of L_alpha union {x} in L_lambda; collapse M to pi M; the collapse
fixes L_alpha union {x}, so x is in pi M; condensation gives pi M =
L_gamma; the sizes give |gamma| = |alpha| < kappa, so gamma < kappa; x is
in L_kappa. Each step is one obligation below. "Delivered" means the
signature exists in the tree and I checked it. "Gap" means no consumer and
no theorem statement exists.

### O1. The condensation theorem assembly (the widest term)

The theorem: for M a Sigma-1-elementary extensional substructure of
L_lambda with lambda a limit ordinal, the collapse pi M is a level
Lset gamma. No such theorem exists in the tree. The substrate that exists
for it is complete: the bounded twelve-row table and block 1
(`src/L/Condensation.lagda.md:106-2171`), the bounded graph matrices
(`GraphB` at `:2396`, `StepAtB` at `:2354`, `DefBodyB` at `:2261`), the
row agreements (`:2424-5003`), and the tower-landing legs `ride-only` and
`ride-defines` (`:403-417`). The collapse with the transitive-fixing
clause is delivered (`src/V/Collapse.lagda.md:40`, `:337`). The
Tarski-Vaught equivalence is delivered (`src/L/Hull.lagda.md:174-306`).
The Levy kit is delivered: `abs_0`, `sigma-1-up`, `pi-1-down`
(`src/FOL/Absoluteness.lagda.md:122-189`).

The unbuilt pieces, each with its price and basis:

| piece | lines | basis |
|---|---:|---|
| extensionality of M from elementarity, `isExt M` | 40 | survey |
| the Sigma-1 level-hood statement with a bounded witness inside the carrier | 150 | survey, the level-hood wrapper at 100 to 250 in `[LJ-1.12]` route C |
| carrier facts: the witness w and the bound K live in L_lambda | 80 | survey, probe statement 2 at under 100 in `[LJ-1.12]` section 6; `boundCloses` and `envCloses` delivered at `src/L/Ordinal/StageArith.lagda.md:86-97`; the `closed-omega` closure probed GO at 30 lines (`_build/lj-1.19-report.md:9`) |
| the transfer legs down at M and along the collapse, both ways, plus satisfaction iso-invariance | 280 | survey, iso-invariance at 80 to 140 in `[LJ-1.12]`, transport certificate at 150 to 300 in `[LJ-1.12]` |
| the two inclusions, the ordinal bookkeeping, the limit case | 180 | MEASURED 124 for the limit case (`_build/l3.32-t261-report.md:32-47`); union law delivered at `src/L/Constructible.lagda.md:319-356`; assembly about 60 survey |
| the theorem statement and module wiring | 60 | survey |
| total O1 | 850, range 700 to 1,100 | see rows |

The seconds: about 22, range 14 to 55. The content class is the P-v
family for the transfer statements at concrete carriers (measured 0.026
seconds per line at the agreement layer, `_build/lj-1.44-report.md:9-13`),
and the parameterized class for the variable-slot majority (0.010 to
0.013, P-m at `dev/LESSONS.md:2460`). The range spans the neutral-carrier
decode class at 0.085 (`dev/ledger.toml:643`) as the bad end.

### O2. The hull elementarity theorem

The theorem: the hull M is elementary in L_lambda at the set carrier.
`hull-closed` gives the criterion at hull parameters
(`src/L/Hull.lagda.md:415`). `TV-thm` gives the equivalence
(`:306`). The bridge from formulas over Code to formulas over the hull's
carrier is the residue (`_build/lj-1.26-report.md:396-398`). Price: 120
lines, range 100 to 200, about 2 seconds. Basis: survey, parameterized
class.

### O3. The hull size bound

The bound: |M| is at most |L_alpha| when X = L_alpha union {x} and alpha
is infinite. The Code count is priced at about 120 lines for about 2
seconds with an itemized obligation list
(`_build/lj-1.22-report.md:8-9` and section 3). The one-element addition,
|L_alpha union {x}| = |L_alpha|, is new, 40 to 80 lines survey. The
chain glue is 30 to 60 lines survey. The presentation
identity, |M| = |Code|, is by construction: M is `sett Code val`
(`src/L/Hull.lagda.md:114-115`). Price: 220 lines, range 180 to 260,
about 4 seconds.

### O4. The finite-stage injections

`fin-inj`, the finite stages' injections into omega, completes
`stage-card-upper` at every infinite ordinal
(`src/L/StageCardinal.lagda.md:508-571`). Price: 75 lines, range 50 to
100, about 1.5 seconds. Basis: `[LJ-1.21]` section 9, survey with the
`Tally` anchor at `src/L/Choice/Finite.lagda.md:120`.

### O5. The cardinal argument

The argument: |gamma| = |alpha| < kappa and kappa a cardinal force gamma
< kappa. The tree has no cardinal predicate. New content: the `IsCardinal`
definition, no-injection from kappa into a smaller ordinal, and the
contradiction chain. Delivered pieces: `stage-card-lower`
(`src/L/StageCardinal.lagda.md:204`), `Emb.emb` (`:514-525`), the
injection type (`:217`), and trichotomy
(`src/L/Ordinal/Linear.lagda.md:136`). The collapse's carrier is a
presentation quotient of M's, so the bijection M to pi M is by
construction. Price: 180 lines, range 130 to 260, about 3 seconds. Basis:
survey, parameterized class.

### O6. The lambda choice and the limit stage

The lambda choice: `stage` and `stage-mem` name a stage of x
(`src/L/Stage.lagda.md:180-189`); `+omega` and `+omega-ord` give an
ordinal above it (`src/L/Ordinal/StageArith.lagda.md:41-83`); `Lset-mono`
carries x up (`src/L/Constructible.lagda.md:355`). Missing: `+omega-limit`
and the `+omega` closure landing, both priced but not delivered
(`_build/lj-1.20-report.md:125-129`; the closure probed GO at 30 body
lines, `_build/lj-1.19-report.md:35-76`). The tree has no `isLimit`
machinery (`_build/lj-1.20-report.md:127`). Price: 80 lines, range 50 to
100, about 1.5 seconds. Basis: the probe and the omission note.

### O7. The finite case

For kappa at most omega, x is finite and appears in L_omega. The tree has
`finiteStage` (`src/L/Choice/Finite.lagda.md:823`). Price: 40 lines,
range 0 to 60, about 0.5 seconds. Basis: survey. The case vanishes if the
lemma is stated for infinite kappa only, which is all 5.6 uses.

### O8. The 5.5 assembly

The theorem statement, the set X = L_alpha union {x}, the module
instantiations, and the final chain. Price: 110 lines, range 80 to 150,
about 1.5 seconds. Basis: survey, comparable to the archived 5.5 row at
0.08 to 0.15k (`dev/ledger.toml:966`) minus the pieces booked elsewhere.

### The total

| obligation | lines center | range | seconds center |
|---|---:|---:|---:|
| O1 condensation theorem | 850 | 700 to 1,100 | 22 |
| O2 hull elementarity | 120 | 100 to 200 | 2 |
| O3 hull size bound | 220 | 180 to 260 | 4 |
| O4 fin-inj | 75 | 50 to 100 | 1.5 |
| O5 cardinal argument | 180 | 130 to 260 | 3 |
| O6 lambda and limit | 80 | 50 to 100 | 1.5 |
| O7 finite case | 40 | 0 to 60 | 0.5 |
| O8 assembly | 110 | 80 to 150 | 1.5 |
| total | 1,675 | 1,290 to 2,230 | 36, range 22 to 75 |

MEASURED anchors: the 124-line limit case and the 30-line closure probe.
The Code count at 120 lines for about 2 seconds is ESTIMATED by its own
report (`_build/lj-1.22-report.md:21`, `:108-110`). Everything else is
ESTIMATED.
The square law is a module parameter of the delivered level size
(`src/L/StageCardinal.lagda.md:14-16`), not part of the total; it is
priced separately in the LJ-1.8 section.

## The probe

The widest unmeasured term is O1, the condensation theorem assembly. The
probe builds the condensation core at one instance and measures its
seconds class.

What it builds:

1. The Sigma-1 level-hood statement at the class carrier with a bounded
   witness: "x = Lset gamma" reads as "exists w in K (graphBndAt w gamma
   K and x = w)", with the Sigma-1 certificate at variable slots. This
   uses the delivered `GraphB`, `DefBodyB` and the block-1 certificate
   shape.
2. The satisfaction iso-invariance under the collapse at the hull
   carrier: for M the hull inside L_lambda and pi the collapse, the
   bounded graph formula's satisfaction transfers between M and pi M and
   back.
3. The down-reflection at M: the same Sigma-1 statement reflects from
   L_lambda into M through `hull-closed`.

Cost: one dispatch, about 300 to 450 probe lines, about 120 to 180
minutes of work, one Agda process at `GHCRTS=-M8g` for about 15 to 30
minutes of check time. The probe is never committed.

GO: the three statements close at or below 350 lines and the transfer
statements check at or below 0.02 seconds per line, the boundary between
the parameterized class and the agreement class. Then O1 re-prices at the
measured rate. The center 850 lines lands at about 20 to 25 seconds, and
LJ-1.7's aggregate lands at 0.0130 to 0.0134, near the bar, fundable with
the one-spelling discipline.

NO-GO: the iso-invariance or the carrier facts force the instantiation
class (0.22 to 0.297, P-n) or the neutral-carrier decode class (0.085),
or a new closure lemma appears. Then O1 re-prices at 1,000 plus lines at
0.085 or worse, about 85 seconds, and LJ-1.7's aggregate lands above
0.015. LJ-1.7 stops for a re-price (DD8).

## What LJ-1.8 hides

The formal distance from 5.5 to `L models GCH` is not comparable to three
lines of book. `[LJ-1.8]` is one PLAN row with no estimate
(`dev/PLAN.md:496`). It hides at least four priced bodies:

1. **5.6's external derivation.** For every infinite cardinal kappa, every
   subset x of kappa lands in Lset (kappa-plus). This needs a successor
   cardinal kappa-plus that exists and is a cardinal, Cantor's theorem,
   and the equality |P(kappa)| = kappa-plus. The tree has no cardinal
   chapter: no `IsCardinal`, no successor cardinal, no Cantor, no
   Schroeder-Bernstein. The archived CSB shape is about 183 lines plus the
   graph form (`archive/rud-route/src/L/Cardinal.lagda.md:89-287`). The
   archived route priced the cardinal chapter at 0.40 to 0.80k naive with
   the limit case never itemized (`_build/l3.32-t5-report.md:466-467`).
   The level-size half is delivered, so the residue is about 700 lines
   center, range 500 to 900. Survey.
2. **The internal GCH vocabulary over `S_l`.** The endpoint is stated
   internally (`dev/PLAN.md:137-138`). The Card, Infinite, successor
   cardinal and bijection-as-set content in the model, plus the packaging,
   is about 450 lines center, range 300 to 600. Survey, anchored on the
   archived "GCH assembly plus internal sentence" at 0.17 to 0.35k after
   the upward correction for the new predicates
   (`_build/l3.32-t5-report.md:467`).
3. **The square-law discharge.** The level size takes the square law at
   every infinite set as a module parameter. No row in the current plan
   builds it. The archived port is 1,283 in-fence lines at a MEASURED
   41.36 seconds (`dev/ledger.toml:252-253`;
   `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:918-963` for the
   shape). The trophy is conditional on `sq` until it lands.
4. **The 5.6 assembly at kappa-plus.** Applying 5.5 at kappa-plus with
   alpha = kappa, and the subset-to-injection steps, about 110 lines.
   Survey.

Best-effort LJ-1.8: about 1,200 lines and 20 seconds excluding the square
law; about 2,500 lines and 60 seconds including it. The whole wing then
projects to about 10,565 lines and 175 seconds, 0.0166, about 30 percent
OVER the bar, and over the a-priori seconds budget of 99.6 to 147.7
(`dev/ledger.toml:242-246`). The phase-1 wing as planned does not fit its
own DD24 budget once 5.5 and 5.6 land. The seconds levers are not margin:
they are a requirement. Caveat: DD5's framing makes the wing's own
measurement the benchmark, and DD24 guards content class, not total.
That framing does not change the seconds arithmetic.

## DD4 split

The template, paid once and shared with the J tower: O2, O3, O4, O5, O6,
O7, O8, about 825 of the 1,675, plus O1's transfer, iso-invariance,
ordinal bookkeeping, limit case and assembly, about 500 of O1. The
per-tower content, Def only: O1's level-hood certificate consumption, the
Sigma-1 statement over the Def bounded machine and its decode, about 350
of O1. This matches the `[LJ-0.7]` verdict: the level-hood certificate is
the one per-tower object left on the chain, and DD27 removed the second,
the definable well-order, by indexing the hull on the meta term algebra
(`_build/lj-1.23-report.md:1-8`). The J tower pays the template once and
supplies its own structural certificate, which may avoid the satisfaction
layer entirely (`_build/lj-1.44-report.md:37-40`). D-26 bears exactly
there: the Def certificate keys on syntax and is delivered; the J
certificate keys on generation data and is cheaper on seconds.

## ARCHIVE USED

- `archive/rud-route/src/L/Condensation.lagda.md`: read for shape only,
  per the brief. Took the transfer template at `:278-295` (`Transport`),
  the class-carrier level story at `:791-865`, `level-transfer-up` and
  `level-transfer-down` at `:845-850`, `amb-agree` at `:283`. The shape
  survives; the `dot-top` step story is classically false (`[LJ-1.11]` F1)
  so no price transfers. The retired route's 5.5 residue was never a
  theorem: T48 records 5.5 consuming condensation parts (i) and (ii) only
  (`archive/dev/JOURNAL-archived.md:1756-1760`).
- `archive/dev/JOURNAL-archived.md`: T5's decomposition at `:1024`
  (bounded subsets at 0.08 to 0.15k with condensation assumed delivered).
  Took the exclusion: that row is not a price for LJ-1.7 on this route.
- `archive/dev/TASKS-archived.md`: T84 at `:119` (STOP under D-10), T259
  at `:266` (the J-side re-target viable). Took the warnings.
- `archive/rud-route/src/L/Cardinal.lagda.md:89-287`: CSB and its graph
  form, `:305` Cantor. Shape for LJ-1.8's cardinal chapter. No price.
- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:918-963`: the
  initial-ordinal restriction. Shape for the `sq` parameter.
- `_build/lj-1.12-report.md`, `_build/lj-1.21-report.md`,
  `_build/lj-1.43-report.md`, `_build/lj-1.44-report.md`,
  `_build/lj-1.45-report.md`: read whole, per the brief's warning. The
  decisive items: the route-A component prices (`lj-1.12`), the fin-inj
  price (`lj-1.21:218-221`), the closed twelve-row table and its rate
  (`lj-1.43`), the agreement-layer class at 0.026 (`lj-1.44:9-13`), and
  the in-flight cure at 77.6 seconds (`lj-1.45:147-148`).
- `_build/lj-1.19-report.md`, `_build/lj-1.20-report.md`,
  `_build/lj-1.22-report.md`, `_build/lj-1.23-report.md`,
  `_build/lj-1.26-report.md`, `_build/lj-1.28-report.md`,
  `_build/l3.32-t5-report.md`: the closure probe, the +omega omissions,
  the Code count, the hull deliverable, the seconds gate, the legs, and
  the archived W7 decomposition.
- `dev/LESSONS.md` via `scripts/rules.py --for recon`: D-10, C-22, P-l,
  D-26 read as the mandatory recon set; P-m and P-n at the citations
  above.

Nothing else in `archive/` was read. WHY NOT: the remaining archived task
rows are the retired route's other crossings and do not bear on 5.5.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read in full. Took section 1.5 (`5.5
  to 5.8`, `:147-164`), section 2 (the strength requirements, `:170-292`),
  section 4 (the per-tower verdict), and section 6 (the resolved OCR).
  The K(u)-bound requirement at section 2.3 is the shape the delivered
  substrate satisfies.
- `_build/literature/dev2.txt:1369-1388`: verified 5.5's statement and
  proof and 5.6's derivation myself.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids re-checking.
- `_build/literature/jech13.txt`: NOT read. WHY NOT: the digest's Jech
  cross-check at section 6.7 settles the shape for pricing.
- `dev/literature/primary-sources.md`, `BIBLIOGRAPHY.md`: NOT read. WHY
  NOT: no pricing content beyond the digest's fetch notes.

What Devlin assumes that the formal proof must supply, in one line: he
assumes the cardinal arithmetic of 1.1(vii) and the initial-ordinal facts,
and asserts the Sigma-0 absoluteness of the level-hood matrix at
transitive carriers; the formal proof must supply the cardinal predicate
and the injection chain, the absoluteness theorem (delivered as `abs_0`),
and the square law (a standing parameter).

## Not sure of

1. O1's price and seconds class. The probe in section 4 decides both. The
   aggregate verdict turns on it: at the parameterized floor LJ-1.7 sits
   inside the noise band at the bar, and at the center it breaches by
   about 10 percent.
2. The square law's placement. No row in the current plan builds it. If
   the trophy must be unconditional, the wing must port or rebuild it at
   1,283 lines and a MEASURED 41.36 seconds, or the 5.5 and 5.6 theorems
   stay conditional on `sq`.
3. Whether 5.5's statement ranges over all kappa or only infinite kappa.
   The finite case is about 40 lines. The statement shape also decides
   whether the level size is needed at arbitrary infinite alpha below
   kappa, which interacts with the square law's initial-ordinal
   restriction. This is worth about 100 to 200 lines of the total.
4. The exact 5.6 packaging shape, semantic record fields or an
   object-language sentence. The internal vocabulary differs by about 200
   to 300 lines.
5. `[LJ-1.45]` is in flight. My aggregate arithmetic uses its pooled mean
   of 58.62 seconds and its 77.6-second aggregate estimate. Its set D may
   move the number.
6. The hotel, |L_alpha union {x}| = |L_alpha|, has no delivered
   comparable. It is a survey at 40 to 80 lines.
