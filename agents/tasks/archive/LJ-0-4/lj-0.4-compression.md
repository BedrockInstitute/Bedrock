# LJ-0.4 Compression recon: can the internalization AC tree land under 16,000?

Recon, read-only. Baseline measured from HEAD on branch `two-tower-bridge`,
2026-08-10, by `scripts/ledger.py --brief`: **17,492** non-blank in-fence lines
over 75 masters. The target is under 16,000, so the needed reduction is
**1,493 lines or more**.

## 1. VERDICT

**No. Under 16,000 is not credibly reachable by compression of the delivered
tree. The honest projection is about 16,400 lines, with a defensible range
of 16,300 to 16,600.**

The basis is a measurement, not an estimate. `[L3.32-T208]` measured the six
July levers on this exact content: minus 620 to minus 860 raw, minus 550 to
minus 780 overlap-free (`_build/l3.32-t208-report.md`). The July survey's
minus 1,486 optimistic end was never probed (`archive/dev/TASKS-archived.md:276`).
The target needs minus 1,493. This recon found new levers worth minus 356 to
minus 796 before calibration. The calibrated sum is about minus 680 to minus
1,160, so the landing is about 16,332 to 16,812. Only the optimistic end of
the optimistic class touches 16,000, and the project's own calibration law
says that class over-promises 1.7 to 2.4 times (`_build/l3.32-t208-report.md`
section 4). The best reachable figure is about 16.3k to 16.6k. Reaching
16,000 needs the new frame levers to beat the measured calibration, or a
content-level retirement, which this brief rules out. I recommend re-pricing
phase 1 on a tree near 16.3k to 16.6k, and still landing the frame blocks,
because they make the GCH wing's twelve clauses cheaper later (DD4).

## 2. THE SIX LEVERS RE-VERIFIED

Verification method: I compared `main` against HEAD per file. No file differs
in in-fence line count, and the branch diff is prose-only (80 insertions, 80
deletions, all translation-word changes). So the content T208 measured on
`main` is the content here, and T208's measurements transfer. I spot-checked
each lever's sites in today's tree. Nothing is already banked: no code landed
between T208 and today. Site numbers are non-blank in-fence line numbers in
today's files, unless they cite a report. Each row gives the measured value
and the site.

| lever | July band | status | value today | site |
|---|---|---:|---|---|
| (a) dead names | -150 to -400 | live | -210 to -280 | 54 names, 210 lines measured; floor 210, likely 210 to 280 (`_build/l3.32-t208-report.md` 3.1) |
| (b) Sound/Unique repeats | -90 | live | -55 to -75 | byte-identical blocks, e.g. `Sound` termAgree witness, `Unique` domAt-in setup (`l3.32-t208-report.md` 3.2) |
| (c) existential-frame | -120 to -300 | live | -105 to -130 | 4 sites: `Internal` Six/Differs/DenoteOf, `Before` At tower (`l3.32-t208-report.md` 3.3) |
| (d) frame retrofit, pre-law | -200 to -341 | live | -90 to -125 | `Unique` clause types 61-83, `Sound` soundness product 792-801 (`l3.32-t208-report.md` 3.4) |
| (e) generic fold, FOL/Manipulation | -120 to -200 | live, narrowed | -60 to -120 | `Renaming` 13-25, `Relabelling` 15-27 identical traversals; cone-audit B3 comparable (`l3.32-t208-report.md` 3.5) |
| (f) recursion assembly | -130 to -200 | live | -100 to -200 | `Hierarchy` 116-124, `Table` 158-167, `Before` 229-398 (`l3.32-t208-report.md` 3.6) |
| sum, raw | -755 to -1,486 | | -620 to -860 | measured by T208 |
| sum, overlap-free | | | -550 to -780 | T208's disjoint total |

Two caveats stand. (e) overlaps the rejected S17 fold: share only the bare
12-clause traversal skeleton, never a stored decomposition or a fusion lemma
(`dev/memos/simplification-register.md:37`). (f) is a measured wall class:
abstracting the recursion's value cost over 400 seconds once
(`dev/LESSONS.md` P-r context; rule 13 in the record), so it needs the named
bisect probe before landing.

## 3. NEW COMPRESSION FOUND

The July survey ran once and priced the frame classes at their statement
surfaces. The same classes appear at sites the survey did not count. Each row
below is an estimate from site counts, not a measurement. I name the sites so
a probe can price each.

| id | what | sites | net lines | risk |
|---|---|---:|---|
| N1 | the existential-frame combinator, extended | `Internal` DenoteBody tower 378-397, LexAt tower 500-519; `Adequate` denote-fill/read 259-359, NameAt-read 359-420, LeastAt-fill/read 442-495; `Limit` PrecedesAt 184-233, LimitOrdAt 348-364, codeOrder-fill/rep 401-450; `Finite` part 175-199 | -120 to -250 | medium-high |
| N2 | the per-clause proof shell in `Unique` | the 12 clause bodies, 487 lines total: the PT.rec over domAt-in, the where-blocks, the extensionalV skeleton repeat per clause (`Unique` 117-603) | -60 to -130 | medium |
| N3 | the residual connective pairs in `Sound` | and/or 257-301, exist/forall 576-661, allIn/exIn 471-576, mem/eq 661-739, top/bot 437-471, imp/neg 739-792 | -30 to -60 | medium |
| N4 | one arity-generic clause frame for `Model` | the per-arity -out/-in pairs: binClause 511-538, unClause 556-583, propClause 607-648, negClause, impClause, quantClause, atomClause, bndClause, shape and sameClosed pairs, about 250 lines | -60 to -130 | medium |
| N5 | dead names above the measured floor | the likely 210 to 280 surface (`l3.32-t208-report.md` 3.1) | 0 to -70 | low |
| N6 | one lex-order kit | `Name` `_≺ᵥ_` 265-334 and `_≺ₙ_` 336-410, two levels of the same lex with the same law suite | -40 to -80 | medium |
| N7 | shared preamble and shift helpers | the TruthAlgebra/hPropStructure/AbsL opens in 8 to 10 masters, the sh2-sh6 helpers in 11 masters, 26 lines | -30 to -60 | low-medium |
| N8 | `𝒟ₒ→isL` to 2 lines | `src/L/Axioms/Basic.lagda.md:98` is still the 18-line proof; `isL-𝒟ₒ` at `:96` and `isL-trans` are in the same file | -16 | low |

N1 to N4 are the DD4 move: they replace repeated fixed content with one
generic thing, and the GCH wing's twelve clauses would instantiate the same
frames. N5 to N8 do not make the wing cheaper.

What I hunted and found tight: `Sat`'s twelve-clause `cond` (32 lines),
`Uniform`'s exists/unique pair (18 lines), and the `Sound` frames already
built (Un/Bin/UnSucc/Atom/BinSucc/Const). A full fold over the twelve clauses
is out: the pinned result type is unfolded by every consumer (`Uniform`
99-101, `Internal` 372), which is exactly the P-r 3x-seconds shape.

## 4. THE SHARED-BASE FOUNDATION KIT

The kit adds lines. It is a readability refactor, not a slimming lever, and
it must not be counted toward the target.

Measured against `godel-route` today: `L/Definability` is 122 against 118
(+4), `V/Coding` is 93 against 92 (+1), and `V/Presentation` exists there at
18 lines and is absent here. So the kit saves 5 at the call sites and costs
18 for its own master: net +13 on those files. The T8 report's own table
measures the whole kit at +15 net: +18 for `Presentation`, minus 3 for
`Definability`, minus 1 for `Basic`, 0 for `Separation`, 0 for `Full`, +1 for
`Power` (`_build/l3.32-t8-report.md` section 3).

The 58-line `Basic` difference between the branches is not the kit. The
`godel-route` `Basic` carries an extra finite-set-equations section and
`L.Rud.Ops` imports; today's `Basic` inlines `∈-asFiber` where the kit uses
`fiber`. The kit's own delta in `Basic` is minus 1.

Recommendation: judge the kit on readability only. It may still be worth
landing for the wing's fiber-and-membership one-liners, but it moves the
line count the wrong way by about 13 to 15.

## 5. THE BLOCK PLAN

Blocks are disjoint by file. Each block names its files, net lines, consumer
risk, and what it makes cheaper later. Block A runs first because dead-name
deletion touches many files. After A, B to G run in parallel. H runs last.

| block | files | net lines | consumer risk | DD4 value |
|---|---|---:|---|---|
| A. dead names + `𝒟ₒ→isL` | the masters holding the 54 dead names (T208's list), plus `L/Axioms/Basic` | -226 to -296 | low: pure removal; one typecheck for `𝒟ₒ→isL` | low |
| B. existential frame, extended | new `L.Choice.Frame`, `L/Choice/Internal`, `Adequate`, `Limit`, `Finite` | -190 to -340 | medium-high: fill/read statements change shape; consumers re-verify; P-r watch | high: the wing's clauses instantiate it |
| C. `Unique`/`Sound` clause frames | new `L.Coding.Pinned`, `L/Coding/Unique`, `L/Coding/Sound` | -180 to -315 | medium: pinned result type is unfolded by consumers; reduction watch | high |
| D. `Model` arity-generic clause frame | new `L.Coding.Clause`, `L/Coding/Model` | -60 to -130 | medium: Sound/Unique/Uniform re-verify | high |
| E. FOL/Manipulation traversal share | `FOL/Manipulation/Renaming`, `Relabelling`, `Bounding`, `Relativize`, `Parameters` | -60 to -120 | medium: no stored decompositions, no fusion lemma, S17 boundary | medium-high |
| F. recursion-assembly triplication | `L/Hierarchy`, `L/Choice/Table`, `L/Choice/Before` | -100 to -200 | medium-high: rule 13 wall; run the named bisect first | high |
| G. lex-order kit | `L/Choice/Name` | -40 to -80 | medium: well-founded lex is delicate | medium |
| H. preamble and shift helpers | about 12 masters, run last | -30 to -60 | low-medium: namespace only | low |
| total | | -886 to -1,541 | | |

The total lands 15,951 to 16,606. The center is about 16,280. The calibrated
total is about minus 680 to minus 1,160, landing 16,332 to 16,812. The block
order by risk is A, H, E, G, C, D, B, F. The parallel set after A is B, C, D,
E, F, G: no two blocks write the same file, and each new module is a
separate file.

## 6. WHAT I WOULD NOT DO

Each rejected item has its reason and its record.

| item | reason | record |
|---|---|---|
| sealed-constant dedupe, lever (g) | module-application hazard; measured 30 to 35 lines, zero executed value | `l3.32-t208-report.md` 3.7 |
| FOL.Fold fusion over the five manipulation modules | probe RED; a stored decomposition walled at 12 GB, inline ran in one second | `dev/memos/simplification-register.md:37` |
| the defSet computation table, S14 | reverted at its gate: 112 lines against a 57-line stop-line | `dev/memos/simplification-register.md:34` |
| the axiom-frame kit, S16 | reverted: line gate missed, and a conversion regression ran over 15 minutes | `dev/memos/simplification-register.md:36`, `_build/l3.32-t8-report.md` 4 |
| the double-encoding collapse, S18 | deferred behind the wing by the owner; weakest accepted candidate | `dev/memos/simplification-register.md:38` |
| the min-difference order | struck: canonicity has a consumer; nets +60 to +360 | `archive/dev/JOURNAL-archived.md:4229` |
| deleting a chapter | no module-level dead weight; the cone reaches every master | `archive/dev/JOURNAL-archived.md:4222` |
| the foundation kit as a line lever | it adds 13 to 15 lines | section 4 above |
| a fold over the twelve clauses | the result type is unfolded by every consumer; P-r measured 3x seconds | `dev/LESSONS.md:2327` |

## 7. ARCHIVE USED

- `archive/dev/JOURNAL-archived.md:4200-4240`: the July survey, the lever
  table, the gating, and the D15 resolution. I took the lever definitions and
  the gate-lift reasoning.
- `dev/memos/L3.28-ac-route.md:1-120`: the fork memo, section 1 cone
  measurements, section 3 Option A, section 4.2 buckets. I took the mass
  distribution and the swap-surface fact.
- `dev/memos/simplification-register.md:33-38`: S13 to S18 verdicts. I took
  the S14 and S16 reversion gates and the S17 RED as boundaries.
- `archive/dev/TASKS-archived.md:43,276,279,295-299`: T8, T205, T208, T168,
  T155, T157 rows. T205's verdict is that the 16,000 floor was a survey
  optimistic end, never probed.
- `archive/dev/DECISIONS-archived.md:25,38-39`: the retired-decision list,
  D16 and D17. D15's full ruling text is at
  `archive/dev/JOURNAL-archived.md:4279`.
- `dev/PLAN.md:35-80,154-174,335-341,413`: the 2026-08-09 route change, the
  rebuilt DD series, the L3.32 close, and the LJ-0.4 row recording the
  un-gate.
- `dev/LESSONS.md:2254,2327,2395,2427`: P-m, P-r, P-t, P-q. P-r forbids the
  fold-over-clause-list shape.
- `_build/l3.32-t208-report.md`: the measured lever table, the calibration
  finding, and the overlap-free total. This is the load-bearing prior.
- `_build/l3.32-t8-report.md`: the foundation kit measurement, +15 net.
- `_build/l3.32-t168-report.md`: the compression-class sweep, alias rows.
- `_build/compress-recon.md`, `_build/deep-levers.md`,
  `_build/compression-audit.md`: methodology and delivered comparables for
  levers (e) and (f).
- `git diff main -- src`: verified the branch differs in prose only, so T208
  transfers to today's tree.

## 8. WHAT I AM NOT SURE OF

- The new lever nets are site counts, not measurements. T208's ratio says the
  optimistic end of a frame class over-promises 1.7 to 2.4 times
  (`dev/LESSONS.md` P-l). A probe must measure N1 to N4 before dispatch.
- The true dead-name surface is 210 to 280, not one number. The scan is
  reference-level, so a name re-exported through a module instance could
  hide a consumer.
- `𝒟ₒ→isL` may not collapse today: `isL-𝒟ₒ` is sealed in an `opaque` block,
  and the July file-order block may still bind. One typecheck settles it.
- The traversal share, block E, must not cross the S17 boundary. Only a
  probe can show whether the bare skeleton shares without the 12 GB wall.
- The exact yield of block F is a measured wall class. The named
  before-and-after bisect on `Table` onto `Hierarchy`'s shape settles it.
- The center figure, about 16.4k, assumes the measured levers land as T208
  measured and the new levers land at their conservative ends. A different
  assumption moves it about 200 lines either way.
- The branch baseline reads 17,492 against T208's main 17,496. Per-file
  fence counts are identical, so I treated the four lines as immaterial.
