# LJ-1.44 report: locate the content class that costs 65 seconds in Condensation

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100.

## 1. THE VERDICT

The expensive class is the row-agreement layer. It is satisfaction-level
transfer content at built formulas with concrete indices. Its types name
two spellings of each leaf (the story's bounded formula and the machine's
unbounded formula). That is the P-t/P-v family: a built formula tree
unfolds at every use, and a satisfaction-level conversion between two
spellings costs seconds inside the type of every lemma that carries it.

Its share of the 65 seconds: the agreement layer (PropAgree through
EqAgree, `src/L/Condensation.lagda.md:2947-4943`) carries 48.8 of the
61.6 profile seconds, about 79 percent. The named-definition rows carry
33.8 seconds. The Miscellaneous bucket carries 27.9 seconds, and the slice
measurement shows about 24 of those are unbilled elaboration of the
agreement regions. The import cone is 1.28 seconds
(`_build/lj-1.43-report.md:44`).

The class CAN change. I built the decisive miniature and measured it. The
same theorem, restated in ONE spelling with the bound carried as a
meta-level membership hypothesis, checks 10.1 times faster at the hottest
row: `PropAgree.subB2T` falls from 883 ms to 87 ms mean
(`src/ProbeLJ144D.agda` against `src/ProbeLJ144E.agda`). The back
direction of the same pair is flat: its residual is the K-membership
derivation, which is content.

The class is NOT the P-n payable floor. The agreement layer checks at
0.026 seconds per line. P-n's measured floor is 0.22 to 0.297
(`dev/LESSONS.md:2483-2498`). This content is about ten times below it.

## 2. THE PROFILE ATTRIBUTION

Instrument: `GHCRTS="-A64m -I0 -M8g" agda --profile=definitions`, one
process, the master's own interface moved aside, dependencies warm. Three
runs. Raw logs: `/tmp/lj144-prof1.log` to `/tmp/lj144-prof3.log`.

| run | Total ms | Miscellaneous ms | named ms |
|---|---:|---:|---:|
| 1 | 61,893 | 27,919 | 33,974 |
| 2 | 61,829 | 28,042 | 33,787 |
| 3 | 61,182 | 27,676 | 33,506 |
| mean | 61,635 | 27,879 (45.2%) | 33,756 (54.8%) |

The named-definition rows, grouped by family, mean of three runs:

| family | ms | share |
|---|---:|---:|
| PropAgree | 6,078 | 9.9% |
| ImpLeaf | 3,749 | 6.1% |
| ExInAgree | 2,951 | 4.8% |
| AllInAgree | 1,768 | 2.9% |
| anonymous `_` | 1,634 | 2.7% |
| ExistAgree | 1,449 | 2.4% |
| BndLeaf | 1,319 | 2.1% |
| ImpAgree | 1,174 | 1.9% |
| ForallAgree | 1,086 | 1.8% |
| EqAgree | 1,036 | 1.7% |
| MemAgree | 1,024 | 1.7% |
| the rest, each under 1.5% | 10,488 | 17.0% |

The single hottest rows are `PropAgree.subB2T-back` (mean 3,025 ms),
`ExInAgree.back` (2,246 ms), `PropAgree.subB2T` (2,029 ms),
`ImpLeaf.yaBack` (1,518 ms) and `AllInAgree.back` (1,076 ms). Every hot
row is a satisfaction-level transfer between the story's bounded formula
and the machine's unbounded formula at a built tree with concrete
indices, e.g. `subB2T` at `src/L/Condensation.lagda.md:3031` with
`subValB` at `:472` and `subValAt` at `src/L/Coding/Model.lagda.md:817`.

The slice measurement attributes the seconds to regions and shows the
Miscellaneous bucket is content. The slices are woven copies of the
master truncated at clean fence boundaries (`src/ProbeLJ144A.agda`,
`B`, `C`), profiled cold with the same instrument:

| region | in-fence lines | total ms (mean) | Misc ms (mean) | delta |
|---|---:|---:|---:|---|
| base, through OpTransfer | 2,648 | 12,860 | 3,956 | - |
| + PropAgree | 248 | 21,378 | 6,567 | +8,518 |
| + And, Or, Top, NegAgree | 368 | 25,494 | 8,447 | +4,116 |
| + ForallAgree to EqAgree | 1,248 | 61,635 | 27,879 | +36,141 |

The delta of each region is the region's own cost. The base is cheap:
0.0049 seconds per line. PropAgree is 0.034. The And/Or/Top/Neg
instantiations are 0.011. The last agreement layer is 0.029. The whole
agreement layer is 0.026 over 1,864 lines.

Miscellaneous scales with the content: 30.8% of slice A, 30.7% of slice
B, 33.1% of slice C, 45.2% of the whole. It is not a fixed artifact. The
import and serialization floor is about 1.3 seconds
(`_build/lj-1.43-report.md:44`). The rest is unbilled elaboration of the
same agreement content.

## 3. THE BAR AND THE NUMBERS

The bar is 0.011057 x 1.15 = 0.012716 seconds per line
(`dev/ledger.toml:2590` and `dev/ledger.toml:2810`). It rounds to 0.0127.

Whole-file cold runs, plain `agda`, user seconds: 61.97, 62.37, 61.21.
Mean 61.85. Spread 1.16 seconds, about 1.9 percent. Rate: 61.85 / 4,512
= 0.0137 seconds per line. That is 1.08 times the bar, about 8 percent
over. Run-to-run variance is about 10 percent, so the breach sits inside
the noise band.

The profile totals (61,635 ms mean) agree with the plain runs. The
profile instrumentation adds no material overhead here.

## 4. CAN THE CLASS CHANGE?

Measured: yes, at the decisive site. `src/ProbeLJ144D.agda` is the
control: `PropAgree.subB2T` and `subB2T-back` copied verbatim into a
minimal module, with the PropAgree telescope trimmed to what they need.
It reproduces the hot rows: mean 883 ms and 924 ms.

`src/ProbeLJ144E.agda` is the variant. The same two theorems are stated
with ONE spelling. The bounded story formula disappears from the types.
The bound becomes a meta-level hypothesis: a witness `z`, its membership
`⟨ fst z ∈ K ⟩`, and the shared core formula `coreS` at the extended
environment. The bodies keep the same adequate-transports byte for byte.

| definition | control ms (mean) | one-spelling ms (mean) | factor |
|---|---:|---:|---:|
| subB2T | 883 | 87 | 10.1x |
| subB2T-back | 924 | 969 | 1.0x |
| probe total | 2,999 | 2,150 | 1.4x |

The forward direction's saving is the built bounded tree: the control
eliminates `⟨ env ⊨ subValB ... ⟩` by truncation recursion, which unfolds
the tree; the variant receives the parts directly. The back direction's
residual is the K-membership derivation
(`src/L/Condensation.lagda.md:3096-3097`), which no spelling removes.

The whole-file application of the lever is the D5 shape measured at leg D
in this same file: write the story once in the machine's vocabulary and
never convert (`dev/LESSONS.md:3037-3055`). I did not rebuild the whole
agreement layer. Per C-34, the miniature is the D-1 decisive instrument,
and the whole-layer delta is unmeasured, not claimed.

The class can change in principle, and the lever has a measured price at
the hottest site. The row-agreement content is not a floor; a restatement
of the statements (not the lines) is the seconds lever, which is P-q's
distinction.

## 5. DD4

The expensive class is per-tower Def content. It lives in the GCH wing's
own agreement layer. The shared frames are cheap: EnvSet 0.74 seconds,
TmVal 0.72, the shape transfers about 1.0, SubValB2T 24 ms. The base
slice checks at 0.0049 seconds per line over 2,648 lines. The J tower
inherits the cheap generic frames, not the expensive agreement layer.
The J tower's structural certificate may avoid the layer entirely (D-26).

## 6. D-26 IN ONE LINE

The expensive class is Def-syntax agreement content at the tower's
concrete carrier, so D-26 bears: the J tower's structural certificate may
avoid it, while the shared well-founded machinery carries generation data
and checks cheap.

## 7. LITERATURE USED

None bears. This is an elaborator cost measurement on this tree's own
code. `devlin-II5.md` prices the mathematics and says nothing about check
cost; `j-hierarchy.md` covers the J side, which this file does not touch;
`devlin-errata.md` does not reach Chapter II section 5, which `[LJ-1.14]`
verified. Spent nothing.

## 8. ARCHIVE USED

- `_build/lj-1.43-report.md`, whole. Took the whole-file protocol, the
  cone figure at `:44`, and the agreement-layer shape at `:9-23`.
- `_build/lj-1.42-report.md`, whole. Took the shared layer (`EnvSet`,
  the shape and subvalue transfers) and the leaf-transfer blockers.
- `_build/lj-1.39-report.md`, whole. Took the compression measurement to
  avoid repeating it; the file's `:34-60` rules out a line lever.
- `dev/LESSONS.md`: P-l, P-m, P-n, P-q, P-t, P-v whole, plus P-k, P-o,
  P-r, P-s and C-34 in context.
- `scripts/check-ratio.py`, `scripts/check-timing.py` and
  `dev/ledger.toml` `[ratio]`: the caliber and the baseline.
- `_build/l3.32-t219-seconds.md` and `_build/l3.32-t195-report.md`: the
  P-m/P-n measured rates and the prior Miscellaneous treatment.
- `_build/lj-1.34-review.md`: the P-v site measurement (59 ms against
  29,415 ms) and the D5 one-spelling shape.

Nothing in `archive/` bears. `archive/rud-route/` holds the retired
route's Condensation, measured at 0.395 s per line there but aimed at a
classically false target (`[LJ-1.11]`), so it prices nothing here. The
archived `D`-series documents cover the retired route and the rud
dispatches. I found no archived comparable the brief missed.

## 9. WHAT I AM NOT SURE OF

1. The slice deltas use means with run-to-run spread of 8 to 9 percent.
   The And/Or/Top/Neg region (0.011 s per line) is inside that noise.
   The last region's 36.1 seconds is robust.
2. The probe's forward saving bundles the one-spelling type with the
   dropped truncation elimination. I did not separate the two. Both are
   costs of the built bounded formula in the statement, which is the
   class claim.
3. The whole-layer cure is unmeasured. The 10.1x is the miniature pair.
   Leg D's 499x is a sibling site and does not transfer by analogy (P-l).
4. The exact Agda billing point of the Miscellaneous bucket is unknown.
   The slice evidence shows it scales with the agreement content, which
   is what the class claim needs.
5. The back-direction residual (about 0.9 to 1.0 seconds per row) is
   content; whether a different site-fact shape removes part of it is
   unmeasured.
