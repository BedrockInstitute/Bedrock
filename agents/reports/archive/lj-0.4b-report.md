# LJ-0.4b: compression block B, the existential frame

Status: COMPLETE. REFUSED on measurement. No commit, no push.
The working tree is at HEAD. The kit module was moved out of the tree after
measurement. It sits at `/tmp/lj04b-kit/Frame.lagda.md`, recoverable.

## 1. THE VERDICT

**REFUSED. The measured net is plus 24.** The band is minus 190 to minus 340.
The full priced wiring nets about minus 6. The block misses its band by about
180 lines even at the optimistic end.

The verdict has a measured anchor, not only a price. I built the kit, wired the
cleanest site, typechecked it, and measured it. The Six site saved 19 lines in
`Internal` at flat seconds. The kit cost 43 lines. One instance cannot pay for
the kit. All instances together pay for the kit and leave about minus 6.

## 2. THE NUMBER

The counts are the ledger caliber. They are non-blank lines inside ```agda
fences, counted by `scripts/ledger.py` with `at_head=False`.

| File | Before | After | Delta |
|---|---:|---:|---:|
| L/Choice/Frame (new kit) | 0 | 43 | +43 |
| L/Choice/Internal (measured, Six wired) | 805 | 786 | -19 |
| **measured net** | 805 | 829 | **+24** |
| L/Choice/Internal, full wiring priced | 805 | about 761 | about -44 |
| L/Choice/Limit, full wiring priced | 456 | about 451 | about -5 |
| L/Choice/Adequate | 573 | 573 | 0 |
| L/Choice/Finite | 619 | 619 | 0 |
| **full net, priced** | 2453 | about 2447 | **about -6** |

The band is minus 190 to minus 340 (`_build/lj-0.4-compression.md:117`).
The full priced net does not reach the band.

## 3. SECONDS

The protocol is one Agda process at a time under
`GHCRTS="-A64m -I0 -M8g"`. Each row deletes the file's own interface, keeps
the dependencies' interfaces, and checks the file once. The first run after a
dependency interface changes is the real recheck cost. The second run is a
cache no-op, so it is not the measurement.

| File | Before (s) | After (s) | Exit |
|---|---:|---:|---:|
| L/Choice/Frame | n/a | 0.57 | 0 |
| L/Choice/Internal | 7.68 | 7.76 | 0 |
| L/Choice/Adequate (consumer) | 14.57 | 14.45 | 0 |
| L/Choice/Limit (consumer) | 2.43 | 2.61 | 0 |
| L/Choice/Before (consumer) | 4.14 | 4.52 | 0 |
| L/Choice/Order (consumer) | 4.95 | 5.22 | 0 |
| L/Choice/Finite | 2.16 | 2.16 | 0 |
| L/Choice/Name (dependency) | 2.22 | 2.22 | 0 |

The deltas are inside run-to-run noise. The Six rewire added no wall seconds.
The P-r hazard did not fire at this site. The reason is in section 4.

## 4. WHAT I SHARED

I built `L.Choice.Frame`, a carrier-generic kit with one pack and four
eliminators. The eliminators walk a nested truncation tower into a flat
existential. The pack rebuilds the tower from the flat tuple. The tower is
never a stored structure. It is the satisfaction relation's own normal form.
No consumer unfolds a stored structure, so P-r (`dev/LESSONS.md:2327`) does
not apply.

I wired one site: `Internal`'s `∃₆-out`. The hand-written `at₁` to `at₆`
tower, 24 lines, became one `unpack₆` call. `Six`, `∃₆`, `∃₆-in` and the
statement of `∃₆-out` are unchanged. Consumers see the same types.

I left the other sites unwired. Their prices are in the table. The reasons
are the arithmetic and the content. `Differs` and `DenoteBody` carry a decode
between the satisfaction form and the decoded form. The decode is content, and
it stays at the site. `Limit`'s sites are already thin. `Adequate`'s and
`Finite`'s sites are single-level, so `∣_∣₁` and `PT.rec` already do the
whole job.

The kit's cost is the block's problem, not its sites. The five real towers
save about 49 lines in total. The kit costs 43 lines. The measured ratio of
one clean instance is 19 lines saved against 43 lines of kit. That ratio
cannot reach the band.

## 5. WHAT THE GCH WING COULD INSTANTIATE (DD4)

The wing's twelve clauses state object-language formulas at concrete carriers
and prove the two-way decodes. Each clause has the same nested-existential
shape this kit walks. The wing would instantiate `unpack₆`, `unpack₃P`,
`unpack₄P`, `unpack₂E` and `pack₆` directly. It would not re-derive the
truncation walk.

The DD4 value is real, and it is why the kit exists. The brief's rule stands:
DD4 does not license landing a block that misses its band. It licenses saying
so. A later task can revive the kit from `/tmp/lj04b-kit/Frame.lagda.md` when
a second consumer exists.

## 6. CONSUMERS RE-VERIFIED

| Consumer | Exit |
|---|---:|
| L/Choice/Adequate | 0 |
| L/Choice/Limit | 0 |
| L/Choice/Before | 0 |
| L/Choice/Order | 0 |
| L/Choice/Finite | 0 |
| L/Choice/Name | 0 |

All consumers checked after the intermediate build and again after the
revert. The revert state is HEAD, so the tree is green.

## 7. LITERATURE USED

I read `dev/literature/digest.md` and `dev/literature/j-hierarchy.md`. The
order and well-order material does not bear on this block. The ∃ⁿ-with-∧
truncation walk is a meta-language nesting pattern. The literature does not
treat it as a single object, and a mechanical unification needs no citation.

## 8. ARCHIVE USED

- `_build/lj-0.4e-report.md:1-31`: the model return. I copied the
  build-measure-revert protocol from it.
- `_build/lj-0.4e-report.md:81-113`: block G's pricing-before-wiring stop.
  I followed it once the arithmetic was negative.
- `_build/l3.32-t208-report.md:143-166`: lever (c), the measured sites and
  the minus 105 to minus 130 band.
- `_build/lj-0.4-compression.md:67`: N1, the extended sites.
- `_build/lj-0.4-compression.md:117`: block B's row and band.
- `dev/memos/simplification-register.md:34,36-37`: S14 and S16 reverted,
  S17 probe RED. I did not re-propose their shapes.
- `dev/LESSONS.md:2327` (P-r) and `:2427` (P-q): read in full. P-r governs
  the frame's shape; the frame stores no structure, so consumers do not
  unfold a fold.

## 9. WHAT I AM NOT SURE OF

1. The unpriced site deltas are design prices, not measurements. The
   measured Six site anchors the rate. The refusal holds even at twice the
   priced savings, so the exact prices do not change the verdict.
2. The "after" seconds for the consumers include the cost of re-reading the
   changed `Internal` interface. The deltas are inside noise. A second run
   of each file is faster because the interface is fresh.
3. The review `_build/lj-0.8-review.md` is in progress. It may correct the
   block's premises. The owner's commit says block B keeps running, so I
   measured the brief as written.
4. The kit's DD4 value is a claim about the wing, not a measurement. It is
   the reason the kit is recoverable rather than deleted.
