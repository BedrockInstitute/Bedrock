# Archived probes

A **probe** is a throwaway miniature that prices a load-bearing assumption
before heavy work. `dev/LESSONS.md` **D-1** says a probe is throwaway by
doctrine and that its VERDICT, in the report, is what must outlive it.

This directory holds the probes that D-1's default does not fit, and the owner
ruled on 2026-08-13 that they belong here. `archive/README.md` carries the
ruling.

## The test, and `[LJ-1.133]` measured why it is the right one

**A probe is kept when a document points INTO the file.** Three forms count,
and `scripts/check-probes.py` applies all three:

1. **A line-number citation**, `src/ProbeX.agda:72-130` or `ProbeX:61`. Such a
   citation resolves against the file and against nothing else.
2. **Prose that sends the reader there.** "in full", "diff against", "read
   WHOLE", "verbatim", "ported from".
3. **A name in a `dev/` document.** `dev/` holds the binding rules. A rule
   whose provenance cannot be opened is a rule nobody can check.

**A probe that no document points into is still throwaway**, and a probe that
no document names at all is deleted. D-1 is unchanged for both.

### Why the report alone is not enough

`[LJ-1.133]` read report and probe pairs to settle this. **A report is the
evidence for a VERDICT; a probe carries a TERM.** A verdict is a sentence and
copies into prose without loss: "GREEN, 2.88 s", "26 lines", "WALL at 65 s".
A term does not. `agents/reports/lj-1.118-report.md:68-81` gives the location
and the line count of a 49-line proof at `ProbeLJ1118A.agda:72-130`, and the
report does not carry the proof. Reports quote types. They do not quote
proofs.

## What is here

The table below is GENERATED from this directory by
`scripts/check-probes.py --index`. Do not edit it by hand. Once a probe leaves
`src/`, the verdict tool stops seeing it, so the citation that justified
keeping it would be lost if a hand-written table were the only record.

<!-- BEGIN GENERATED INDEX: scripts/check-probes.py --index -->

| File | Strongest citation | Kind |
|---|---|---|
| `CutProbe.agda` | agents/reports/archive/cut-probe-report.md:56 | line citation |
| `OrderProbe.agda` | agents/reports/archive/order-probe-report.md:133 | line citation |
| `ProbeBelowLim.agda` | agents/reports/archive/l3.32-t127-report.md:87 | line citation |
| `ProbeCarried.agda` | agents/reports/archive/l3.32-t53-report.md:14 | line citation |
| `ProbeDD25C.agda` | dev/LESSONS.md:2944 | binding rule |
| `ProbeDD25CD.agda` | agents/reports/archive/lj-1.35-report.md:43 | line citation |
| `ProbeDD25CE.agda` | agents/reports/archive/lj-1.33-review.md:38 | line citation |
| `ProbeDD25CS.agda` | agents/reports/archive/lj-1.33-review.md:47 | line citation |
| `ProbeDD25D.agda` | dev/LESSONS.md:2944 | binding rule |
| `ProbeDD25D2.agda` | agents/reports/archive/lj-1.41-review.md:191 | line citation |
| `ProbeDD25D5.agda` | dev/LESSONS.md:3092 | binding rule |
| `ProbeDD25E.agda` | dev/LESSONS.md:2944 | binding rule |
| `ProbeDD25E1.agda` | dev/LESSONS.md:3226 | binding rule |
| `ProbeDD25E3.agda` | dev/LESSONS.md:3226 | binding rule |
| `ProbeDD25F.agda` | dev/LESSONS.md:3307 | binding rule |
| `ProbeDD25F41A.agda` | dev/LESSONS.md:3307 | binding rule |
| `ProbeDD25F41B.agda` | dev/LESSONS.md:3309 | binding rule |
| `ProbeDD25F41D.agda` | dev/LESSONS.md:3314 | binding rule |
| `ProbeDD25G.agda` | dev/LESSONS.md:3424 | binding rule |
| `ProbeDD25G1.agda` | dev/LESSONS.md:3424 | binding rule |
| `ProbeDD25G2.agda` | agents/reports/archive/lj-1.7-review.md:26 | line citation |
| `ProbeDD25G3.agda` | agents/reports/archive/lj-1.63-report.md:64 | line citation |
| `ProbeDD25H.agda` | agents/reports/archive/lj-1.53-report.md:80 | named |
| `ProbeDD25H2.agda` | agents/reports/archive/lj-1.53-report.md:80 | named |
| `ProbeDD25H3.agda` | agents/reports/archive/lj-1.50-review.md:21 | line citation |
| `ProbeDD25H4.agda` | agents/reports/archive/lj-1.50-review.md:400 | line citation |
| `ProbeDD25H8.agda` | agents/reports/archive/lj-1.50-review.md:505 | line citation |
| `ProbeDefStep.agda` | agents/reports/archive/l3.32-t66-report.md:48 | line citation |
| `ProbeLJ1100A.agda` | agents/reports/lj-1.100-report.md:10 | line citation |
| `ProbeLJ1101A.agda` | agents/reports/lj-1.101-report.md:17 | line citation |
| `ProbeLJ1102A.agda` | agents/reports/lj-1.102-report.md:11 | line citation |
| `ProbeLJ1103A.agda` | agents/reports/lj-1.103-report.md:91 | line citation |
| `ProbeLJ1104A.agda` | agents/reports/lj-1.105-report.md:111 | line citation |
| `ProbeLJ1106A.agda` | agents/reports/lj-1.107-report.md:70 | line citation |
| `ProbeLJ1107A.agda` | agents/reports/lj-1.118-report.md:38 | line citation |
| `ProbeLJ1109A.agda` | dev/LESSONS.md:3594 | binding rule |
| `ProbeLJ1111A.agda` | agents/reports/lj-1.111-report.md:31 | line citation |
| `ProbeLJ1111B.agda` | agents/reports/lj-1.114-report.md:51 | line citation |
| `ProbeLJ1112A.agda` | agents/reports/lj-1.113-report.md:31 | line citation |
| `ProbeLJ1114A.agda` | agents/reports/lj-1.114-report.md:42 | line citation |
| `ProbeLJ1116A.agda` | agents/reports/lj-1.116-report.md:49 | line citation |
| `ProbeLJ115.agda` | agents/reports/archive/lj-1.15-report.md:19 | line citation |
| `ProbeLJ115b.agda` | agents/reports/archive/lj-1.15-report.md:120 | line citation |
| `ProbeLJ117Combinators.agda` | agents/reports/archive/lj-1.17-review.md:241 | named |
| `ProbeLJ117SquareLaw.agda` | agents/reports/lj-1.107-report.md:241 | named |
| `ProbeLJ118.agda` | agents/reports/archive/lj-1.18-report.md:29 | line citation |
| `ProbeLJ119.agda` | agents/reports/archive/lj-1.19-report.md:8 | line citation |
| `ProbeLJ124Arm1.agda` | agents/reports/archive/lj-1.25-report.md:89 | line citation |
| `ProbeLJ124Control.agda` | agents/reports/archive/lj-1.24-report.md:14 | named |
| `ProbeLJ127.agda` | agents/reports/archive/lj-1.27-report.md:29 | line citation |
| `ProbeLJ130A.agda` | agents/reports/archive/lj-1.30-report.md:16 | named |
| `ProbeLJ130B.agda` | agents/reports/archive/lj-1.30-report.md:17 | named |
| `ProbeLJ131.agda` | agents/reports/archive/lj-1.32-report.md:118 | named |
| `ProbeLJ132C0.agda` | agents/reports/archive/lj-1.32-report.md:40 | named |
| `ProbeLJ133.agda` | agents/reports/archive/lj-1.33-review.md:20 | line citation |
| `ProbeLJ134.agda` | dev/LESSONS.md:3092 | binding rule |
| `ProbeLJ135.agda` | agents/reports/archive/lj-1.38-report.md:242 | named |
| `ProbeLJ136.agda` | agents/reports/archive/lj-1.36-report.md:223 | line citation |
| `ProbeLJ139.agda` | agents/reports/archive/lj-1.39-report.md:128 | named |
| `ProbeLJ139V2.agda` | agents/reports/archive/lj-1.39-report.md:128 | named |
| `ProbeLJ141C.agda` | dev/LESSONS.md:3318 | binding rule |
| `ProbeLJ144D.agda` | agents/reports/archive/lj-1.44-report.md:27 | named |
| `ProbeLJ147Collapse.agda` | agents/reports/archive/lj-1.51-report.md:258 | named |
| `ProbeLJ147PairingGut.agda` | dev/LESSONS.md:3379 | binding rule |
| `ProbeLJ147PairingSealed.agda` | dev/LESSONS.md:3378 | binding rule |
| `ProbeLJ147SquareLawViaCol.agda` | agents/reports/archive/lj-1.51-report.md:258 | named |
| `ProbeLJ148.agda` | agents/reports/archive/lj-1.48-report.md:4 | named |
| `ProbeLJ149.agda` | agents/reports/archive/lj-1.50-report.md:161 | named |
| `ProbeLJ150Control.agda` | agents/reports/archive/lj-1.50-review.md:20 | line citation |
| `ProbeLJ150Linear.agda` | agents/reports/archive/lj-1.50-review.md:253 | line citation |
| `ProbeLJ150MatrixControl.agda` | agents/reports/archive/lj-1.50-review.md:255 | line citation |
| `ProbeLJ150MatrixSlots.agda` | agents/reports/archive/lj-1.50-review.md:254 | line citation |
| `ProbeLJ150Slots.agda` | agents/reports/archive/lj-1.50-review.md:253 | line citation |
| `ProbeLJ152A.agda` | agents/reports/archive/lj-1.57-report.md:141 | line citation |
| `ProbeLJ152B.agda` | agents/reports/archive/lj-1.57-report.md:139 | line citation |
| `ProbeLJ153A.agda` | agents/reports/archive/lj-1.53-report.md:40 | line citation |
| `ProbeLJ153Cone.agda` | agents/reports/archive/lj-1.53-report.md:8 | named |
| `ProbeLJ154A.agda` | agents/reports/archive/lj-1.61-report.md:37 | line citation |
| `ProbeLJ155A.agda` | agents/reports/archive/lj-1.55-report.md:26 | line citation |
| `ProbeLJ155B.agda` | agents/reports/archive/lj-1.70-report.md:202 | line citation |
| `ProbeLJ155C.agda` | agents/reports/archive/lj-1.55-report.md:100 | line citation |
| `ProbeLJ156A.agda` | agents/reports/archive/lj-1.56-report.md:28 | line citation |
| `ProbeLJ156Cone.agda` | agents/reports/archive/lj-1.57-report.md:196 | named |
| `ProbeLJ156Shape.agda` | agents/reports/archive/lj-1.57-report.md:193 | named |
| `ProbeLJ157A.agda` | agents/reports/archive/lj-1.61-report.md:40 | line citation |
| `ProbeLJ158A.agda` | agents/reports/archive/lj-1.58-report.md:50 | named |
| `ProbeLJ161A.agda` | agents/reports/archive/tmp-cond-dd3aa13.lagda.md:6231 | named |
| `ProbeLJ17.agda` | dev/LESSONS.md:3458 | binding rule |
| `ProbeLJ171A.agda` | dev/LESSONS.md:3458 | binding rule |
| `ProbeLJ173A.agda` | agents/reports/archive/lj-1.74-report.md:171 | named |
| `ProbeLJ174A.agda` | agents/reports/archive/lj-1.74-report.md:209 | named |
| `ProbeLJ174B.agda` | agents/reports/archive/lj-1.75-report.md:44 | line citation |
| `ProbeLJ174C.agda` | agents/reports/archive/lj-1.75-report.md:50 | line citation |
| `ProbeLJ174D.agda` | agents/reports/archive/lj-1.75-report.md:53 | line citation |
| `ProbeLJ174F.agda` | agents/reports/archive/diag-twelve-row-math.md:64 | line citation |
| `ProbeLJ174P0.agda` | agents/reports/archive/diag-twelve-row-math.md:80 | line citation |
| `ProbeLJ175A.agda` | agents/reports/archive/lj-1.76-report.md:185 | named |
| `ProbeLJ177A.agda` | dev/LESSONS.md:3489 | binding rule |
| `ProbeLJ178A.agda` | agents/reports/archive/lj-1.78-report.md:20 | line citation |
| `ProbeLJ180A.agda` | agents/reports/archive/lj-1.81-report.md:97 | line citation |
| `ProbeLJ182A.agda` | agents/reports/archive/lj-1.82-report.md:12 | line citation |
| `ProbeLJ183A.agda` | agents/reports/archive/lj-1.83-report.md:24 | line citation |
| `ProbeLJ184A.agda` | agents/reports/archive/lj-1.84-report.md:38 | line citation |
| `ProbeLJ185A.agda` | agents/reports/archive/lj-1.85-report.md:68 | line citation |
| `ProbeLJ185B.agda` | agents/reports/archive/lj-1.87-report.md:216 | line citation |
| `ProbeLJ185C.agda` | agents/reports/archive/lj-1.85-report.md:81 | line citation |
| `ProbeLJ186A.agda` | agents/reports/lj-1.90-report.md:93 | line citation |
| `ProbeLJ187A.agda` | agents/reports/archive/lj-1.87-report.md:153 | line citation |
| `ProbeLJ187B.agda` | agents/reports/archive/lj-1.87-report.md:35 | line citation |
| `ProbeLJ188A.agda` | agents/reports/archive/lj-1.88-report.md:29 | line citation |
| `ProbeLJ189A.agda` | agents/reports/lj-1.90-report.md:108 | line citation |
| `ProbeLJ190A.agda` | agents/reports/lj-1.94-report.md:21 | line citation |
| `ProbeLJ192A.agda` | agents/reports/lj-1.92-report.md:72 | line citation |
| `ProbeLJ193A.agda` | agents/reports/lj-1.93-report.md:56 | line citation |
| `ProbeLJ193B.agda` | agents/reports/lj-1.93-report.md:15 | named |
| `ProbeLJ193C.agda` | agents/reports/lj-1.113-report.md:121 | line citation |
| `ProbeLJ194A.agda` | agents/reports/lj-1.101-report.md:20 | line citation |
| `ProbeLJ195A.agda` | agents/reports/lj-1.95-report.md:9 | line citation |
| `ProbeLJ196A.agda` | agents/reports/lj-1.113-report.md:189 | line citation |
| `ProbeLJ197A.agda` | agents/reports/lj-1.98-report.md:107 | line citation |
| `ProbeLJ198A.agda` | agents/reports/lj-1.98-report.md:15 | line citation |
| `ProbeLJ198B.agda` | agents/reports/lj-1.98-report.md:80 | line citation |
| `ProbeLJ199A.agda` | dev/LESSONS.md:3543 | binding rule |
| `ProbeLJ199B.agda` | agents/reports/lj-1.99-report.md:21 | line citation |
| `ProbeLevy.agda` | agents/reports/archive/l3.32-t66-report.md:13 | line citation |
| `ProbeRudComp.agda` | dev/LESSONS.md:1012 | binding rule |
| `ProbeSatSets.agda` | agents/reports/lj-1.132-report.md:102 | named |
| `ProbeT126.agda` | agents/reports/archive/l3.32-t127-report.md:85 | line citation |
| `ProbeT127.agda` | agents/reports/archive/l3.32-t127-report.md:80 | line citation |
| `ProbeT128.agda` | agents/reports/archive/l3.32-t239-report.md:37 | line citation |
| `ProbeT131.agda` | agents/reports/archive/l3.32-t131-report.md:22 | line citation |
| `ProbeT132.agda` | agents/reports/archive/l3.32-t133-report.md:225 | line citation |
| `ProbeT138.agda` | dev/memos/L3.32-below-lim-design.md:22 | binding rule |
| `ProbeT140.agda` | agents/reports/archive/l3.32-t145-report.md:155 | line citation |
| `ProbeT142.agda` | agents/reports/archive/l3.32-t142-report.md:122 | line citation |
| `ProbeT143.agda` | agents/reports/archive/l3.32-t143-report.md:111 | line citation |
| `ProbeT145.agda` | dev/ledger.toml:651 | binding rule |
| `ProbeT151.agda` | agents/reports/archive/l3.32-t151-report.md:23 | line citation |
| `ProbeT154.agda` | agents/reports/archive/l3.32-t154-report.md:11 | line citation |
| `ProbeT159.agda` | agents/reports/archive/l3.32-t174-strategy.md:27 | line citation |
| `ProbeT161.agda` | agents/reports/archive/l3.32-t161-report.md:53 | line citation |
| `ProbeT175.agda` | agents/reports/archive/l3.32-t177-report.md:25 | line citation |
| `ProbeT177.agda` | agents/reports/archive/l3.32-t212-report.md:47 | line citation |
| `ProbeT179.agda` | agents/reports/archive/l3.32-t244-report.md:79 | line citation |
| `ProbeT182.agda` | agents/reports/archive/l3.32-t194-report.md:67 | line citation |
| `ProbeT185.agda` | agents/reports/archive/l3.32-t227-report.md:134 | line citation |
| `ProbeT193.agda` | agents/reports/archive/l3.32-t193-report.md:13 | line citation |
| `ProbeT194.agda` | agents/reports/archive/l3.32-t199-report.md:28 | line citation |
| `ProbeT204.agda` | agents/reports/archive/l3.32-t217-report.md:40 | line citation |
| `ProbeT222.agda` | agents/reports/archive/l3.32-t242-report.md:19 | line citation |
| `ProbeT237.agda` | dev/ledger.toml:1723 | binding rule |
| `ProbeT240.agda` | agents/reports/archive/l3.32-t245-report.md:93 | line citation |
| `ProbeT249.agda` | agents/reports/archive/l3.32-t249-report.md:57 | line citation |
| `ProbeT251.agda` | agents/reports/archive/l3.32-t251-report.md:65 | line citation |
| `ProbeT261.agda` | agents/reports/archive/l3.32-t261-report.md:29 | line citation |
| `ProbeT68.agda` | agents/reports/archive/l3.32-t68-report.md:41 | line citation |
| `ProbeTowerInd.agda` | dev/ledger.toml:299 | binding rule |
| `ProbeTowerInd2.agda` | dev/ledger.toml:299 | binding rule |
| `ProbeW3Seq.agda` | agents/reports/archive/l3.32-t50-report.md:46 | line citation |
| `StepProbe.agda` | agents/reports/archive/cut-probe-report.md:236 | line citation |

<!-- END GENERATED INDEX -->

## The paths in the citing documents are stale, and stay stale

Most citing reports are frozen and name the probe at `src/Probe*.agda`, which
is where it ran; it was never committed there and `scripts/check-probes.py`
still forbids that. Some of the oldest name `_build/probe*/`. **Find the file
by its basename**, which is unique in this directory. `[LJ-1.130]` ruled that
a brief and a report are frozen records, corrected in the next one and never
rewritten; `[LJ-1.133]` rewrote the 27 citations in the LIVE `dev/` documents
and left every report and brief alone.

## The same archive rules apply

- **Frozen.** Never edited in place. A revival copies the probe OUT.
- **Not required to be green.** Each was written against a tree that has moved,
  and each may use constructs the live tree forbids.
- **Outside every gate**, structurally, because `archive/` is outside `src/`.
- **Do not revive one without re-pricing it.** `dev/LESSONS.md` **P-l**: a
  price measured elsewhere is a hypothesis, not a price.
