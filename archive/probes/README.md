# Archived probes

A **probe** is a throwaway miniature that prices a load-bearing assumption
before heavy work. `dev/LESSONS.md` **D-1** says a probe is throwaway by
doctrine and that its VERDICT, in the report, is what must outlive it.

This directory holds the probes that D-1's default does not fit, and the owner
ruled on 2026-08-13 that they belong here. `archive/README.md` carries the
ruling.

## WHEN a probe leaves `src/`, and where that rule executes

**A probe may be swept when its own task is closed AND no LIVE task needs it.**
Both halves are read off files on disk. `[LJ-1.138]` wrote the rule on
2026-08-13 and it replaced the file's mtime.

**mtime was a PROXY for 「a task is live」 and it failed in both directions.** A
probe written at the start of a three-hour task aged out of the six-hour window
while the agent still needed it, which killed two agents on 2026-08-05. A
finished task's probe stayed protected for six hours after it was dead. On
2026-08-13 the tool called all 14 probes in `src/` FRESH, and all 14 tasks were
closed with their reports written.

**A tool reads 「live」 from three tests, and any one of them holds the file.**

1. **`dev/PLAN.md` section 11 says so.** One row per dispatched code, written
   before the work starts (PLAN section 6.0 rule 6). A verdict cell of
   `DISPATCHED` or `planned` is a live task.
2. **A live task's brief names the probe**, directly, or through one hop into a
   document that points INTO the file.
3. **A brief exists for the code and no report file exists.**

**「The report exists」 NEVER closes a task, and C-22 is the reason.** C-22 makes
every agent write its deliverable as a skeleton first. MEASURED on 2026-08-13:
`agents/reports/lj-1.136-report.md` was 39,948 bytes while `[LJ-1.136]` was
still reading. A missing report proves a task is unfinished; the converse is
false.

**WHERE IT EXECUTES.** `make check` runs `check-probes.py --gate`, which FAILS
when a finished probe is still in `src/`. The gate moves no file. `make
probes-sweep` archives and deletes in one command, and it never touches a probe
a live task needs.

## The test, and `[LJ-1.133]` measured why it is the right one

**A probe is kept when a document points INTO the file.** Three forms count,
and `scripts/check-probes.py` applies all three:

1. **A line-number citation**, `src/ProbeX.agda:72-130` or `ProbeX:61`. Such a
   citation resolves against the file and against nothing else.
2. **Prose that sends the reader there.** "in full", "diff against", "read
   WHOLE", "verbatim", "ported from".
3. **A name in a `dev/` document.** `dev/` holds the binding rules. A rule
   whose provenance cannot be opened is a rule nobody can check.

**A probe that a document merely NAMES is also kept**, ruled by the owner on
2026-08-13. `[LJ-1.133]` measured that the three tests above cannot separate a
named probe from a pointed-into one: the prose detector was fitted to its own
counterexamples, so its recall is unknown. **When a test cannot separate two
classes reliably, take the recoverable side.** Archiving costs disk and
reverses. A deletion and a dangling pointer do not.

**A probe that no document names at all is deleted.** D-1 is unchanged for it.

### A mover must handle the shorthand forms

A citation can name a family without writing any member out:
`archive/probes/ProbeDD25F41{A,B,C,D}.agda` at `dev/LESSONS.md:3330`, and
`src/ProbeLJ174A..F.agda` at `agents/reports/archive/lj-1.74-report.md:209`.
**A plain `src/ProbeX.agda` search does not see them**, in either direction:
it will not find the members when deciding what to keep, and it will not
rewrite the path when they move. `[LJ-1.133]` was bitten once each way, and
`[LJ-1.132]` was bitten by the same shape at
`agents/reports/lj-1.128-report.md:86`.

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
| `ProbeDD25A.agda` | agents/reports/archive/lj-1.27-review.md:140 | named |
| `ProbeDD25B.agda` | agents/reports/lj-1.133-report.md:63 | named |
| `ProbeDD25B1.agda` | agents/reports/lj-1.133-report.md:63 | named |
| `ProbeDD25B10.agda` | agents/reports/archive/lj-1.32-review.md:192 | named |
| `ProbeDD25B11.agda` | agents/reports/archive/lj-1.32-review.md:193 | named |
| `ProbeDD25B12.agda` | agents/reports/archive/lj-1.32-review.md:194 | named |
| `ProbeDD25B13.agda` | agents/reports/lj-1.133-report.md:63 | named |
| `ProbeDD25B14.agda` | agents/reports/archive/lj-1.32-review.md:196 | named |
| `ProbeDD25B2.agda` | agents/reports/archive/lj-1.32-review.md:389 | named |
| `ProbeDD25B3.agda` | agents/reports/archive/lj-1.32-review.md:137 | named |
| `ProbeDD25B4.agda` | agents/reports/archive/lj-1.32-review.md:178 | named |
| `ProbeDD25B5.agda` | agents/reports/archive/lj-1.32-review.md:167 | named |
| `ProbeDD25Bd04.agda` | agents/reports/archive/lj-1.32-review.md:206 | named |
| `ProbeDD25Bd08.agda` | agents/reports/archive/lj-1.32-review.md:207 | named |
| `ProbeDD25Bd12.agda` | agents/reports/archive/lj-1.32-review.md:208 | named |
| `ProbeDD25Bd16.agda` | agents/reports/archive/lj-1.32-review.md:209 | named |
| `ProbeDD25Bd20.agda` | agents/reports/archive/lj-1.32-review.md:210 | named |
| `ProbeDD25C.agda` | dev/LESSONS.md:2944 | binding rule |
| `ProbeDD25CB.agda` | agents/reports/archive/lj-1.33-review.md:70 | named |
| `ProbeDD25CD.agda` | agents/reports/archive/lj-1.35-report.md:43 | line citation |
| `ProbeDD25CE.agda` | agents/reports/archive/lj-1.33-review.md:38 | line citation |
| `ProbeDD25CF.agda` | agents/reports/archive/lj-1.33-review.md:238 | named |
| `ProbeDD25CL.agda` | agents/reports/archive/lj-1.33-review.md:71 | named |
| `ProbeDD25CM.agda` | agents/reports/archive/lj-1.33-review.md:95 | named |
| `ProbeDD25CS.agda` | agents/reports/archive/lj-1.33-review.md:47 | line citation |
| `ProbeDD25D.agda` | dev/LESSONS.md:2944 | binding rule |
| `ProbeDD25D1.agda` | agents/reports/archive/lj-1.34-review.md:50 | named |
| `ProbeDD25D2.agda` | agents/reports/archive/lj-1.41-review.md:191 | line citation |
| `ProbeDD25D3.agda` | agents/reports/archive/lj-1.34-review.md:51 | named |
| `ProbeDD25D4.agda` | agents/reports/archive/lj-1.34-review.md:52 | named |
| `ProbeDD25D5.agda` | dev/LESSONS.md:3092 | binding rule |
| `ProbeDD25E.agda` | dev/LESSONS.md:2944 | binding rule |
| `ProbeDD25E1.agda` | dev/LESSONS.md:3226 | binding rule |
| `ProbeDD25E2.agda` | agents/reports/archive/tmp-cond-dd3aa13.lagda.md:2505 | named |
| `ProbeDD25E3.agda` | dev/LESSONS.md:3226 | binding rule |
| `ProbeDD25F.agda` | dev/LESSONS.md:3307 | binding rule |
| `ProbeDD25F41A.agda` | dev/LESSONS.md:3307 | binding rule |
| `ProbeDD25F41B.agda` | dev/LESSONS.md:3309 | binding rule |
| `ProbeDD25F41C.agda` | agents/reports/lj-1.133-report.md:498 | named |
| `ProbeDD25F41D.agda` | dev/LESSONS.md:3314 | binding rule |
| `ProbeDD25G.agda` | dev/LESSONS.md:3424 | binding rule |
| `ProbeDD25G1.agda` | dev/LESSONS.md:3424 | binding rule |
| `ProbeDD25G2.agda` | agents/reports/archive/lj-1.7-review.md:26 | line citation |
| `ProbeDD25G2Cone.agda` | agents/reports/archive/lj-1.7-review.md:9 | named |
| `ProbeDD25G3.agda` | agents/reports/archive/lj-1.63-report.md:64 | line citation |
| `ProbeDD25H.agda` | agents/reports/archive/lj-1.53-report.md:80 | named |
| `ProbeDD25H1.agda` | agents/reports/archive/lj-1.50-review.md:5 | named |
| `ProbeDD25H2.agda` | agents/reports/archive/lj-1.53-report.md:80 | named |
| `ProbeDD25H2N.agda` | agents/reports/archive/lj-1.50-review.md:6 | named |
| `ProbeDD25H3.agda` | agents/reports/archive/lj-1.50-review.md:21 | line citation |
| `ProbeDD25H4.agda` | agents/reports/archive/lj-1.50-review.md:400 | line citation |
| `ProbeDD25H5.agda` | agents/reports/archive/lj-1.50-review.md:146 | named |
| `ProbeDD25H6.agda` | agents/reports/archive/lj-1.50-review.md:271 | named |
| `ProbeDD25H7.agda` | agents/reports/archive/lj-1.50-review.md:27 | named |
| `ProbeDD25H8.agda` | agents/reports/archive/lj-1.50-review.md:505 | line citation |
| `ProbeDefStep.agda` | agents/reports/archive/l3.32-t66-report.md:48 | line citation |
| `ProbeLJ1100A.agda` | agents/reports/lj-1.100-report.md:10 | line citation |
| `ProbeLJ1101A.agda` | agents/reports/lj-1.101-report.md:17 | line citation |
| `ProbeLJ1102A.agda` | agents/reports/lj-1.102-report.md:11 | line citation |
| `ProbeLJ1103A.agda` | agents/reports/lj-1.103-report.md:91 | line citation |
| `ProbeLJ1104A.agda` | agents/reports/lj-1.105-report.md:111 | line citation |
| `ProbeLJ1105A.agda` | agents/reports/lj-1.133-report.md:62 | named |
| `ProbeLJ1106A.agda` | agents/reports/lj-1.107-report.md:70 | line citation |
| `ProbeLJ1107A.agda` | agents/reports/lj-1.118-report.md:38 | line citation |
| `ProbeLJ1109A.agda` | dev/LESSONS.md:3594 | binding rule |
| `ProbeLJ1111A.agda` | agents/reports/lj-1.111-report.md:31 | line citation |
| `ProbeLJ1111B.agda` | agents/reports/lj-1.114-report.md:51 | line citation |
| `ProbeLJ1112A.agda` | agents/reports/lj-1.113-report.md:31 | line citation |
| `ProbeLJ1114A.agda` | agents/reports/lj-1.134-report.md:281 | line citation |
| `ProbeLJ1115A.agda` | agents/reports/lj-1.115-report.md:12 | line citation |
| `ProbeLJ1115B.agda` | agents/reports/lj-1.115-report.md:18 | line citation |
| `ProbeLJ1116A.agda` | agents/reports/lj-1.116-report.md:49 | line citation |
| `ProbeLJ1117A.agda` | agents/reports/lj-1.118-report.md:168 | line citation |
| `ProbeLJ1118A.agda` | agents/reports/lj-1.118-report.md:20 | line citation |
| `ProbeLJ1119A.agda` | agents/reports/lj-1.121-report.md:15 | line citation |
| `ProbeLJ1120A.agda` | agents/reports/lj-1.120-report.md:9 | line citation |
| `ProbeLJ1120B.agda` | agents/reports/lj-1.120-report.md:13 | line citation |
| `ProbeLJ1120C.agda` | agents/reports/lj-1.120-report.md:113 | line citation |
| `ProbeLJ1121A.agda` | agents/reports/lj-1.121-report.md:95 | line citation |
| `ProbeLJ1122A.agda` | agents/reports/lj-1.122-report.md:93 | named |
| `ProbeLJ1122B.agda` | agents/reports/lj-1.122-report.md:16 | named |
| `ProbeLJ1124A.agda` | agents/reports/lj-1.124-report.md:25 | line citation |
| `ProbeLJ1125A.agda` | agents/reports/lj-1.125-report.md:45 | line citation |
| `ProbeLJ1125B.agda` | agents/reports/lj-1.125-report.md:21 | line citation |
| `ProbeLJ115.agda` | agents/reports/archive/lj-1.15-report.md:19 | line citation |
| `ProbeLJ115b.agda` | agents/reports/archive/lj-1.15-report.md:120 | line citation |
| `ProbeLJ117Combinators.agda` | agents/reports/archive/lj-1.17-review.md:241 | named |
| `ProbeLJ117Pairing.agda` | agents/reports/archive/lj-1.17-review.md:240 | named |
| `ProbeLJ117SquareLaw.agda` | agents/reports/lj-1.107-report.md:241 | named |
| `ProbeLJ118.agda` | agents/reports/archive/lj-1.18-report.md:29 | line citation |
| `ProbeLJ119.agda` | agents/reports/archive/lj-1.19-report.md:8 | line citation |
| `ProbeLJ124Arm1.agda` | agents/reports/archive/lj-1.25-report.md:89 | line citation |
| `ProbeLJ124Base.agda` | agents/reports/archive/lj-1.63-report.md:68 | named |
| `ProbeLJ124Control.agda` | agents/reports/archive/lj-1.24-report.md:14 | named |
| `ProbeLJ127.agda` | agents/reports/archive/lj-1.27-report.md:29 | line citation |
| `ProbeLJ130A.agda` | agents/reports/archive/lj-1.30-report.md:16 | named |
| `ProbeLJ130B.agda` | agents/reports/lj-1.133-report.md:59 | named |
| `ProbeLJ131.agda` | agents/reports/archive/lj-1.32-report.md:118 | named |
| `ProbeLJ132C0.agda` | agents/reports/archive/lj-1.32-report.md:40 | named |
| `ProbeLJ132C2.agda` | agents/reports/archive/lj-1.32-report.md:42 | named |
| `ProbeLJ132C5.agda` | agents/reports/archive/lj-1.32-report.md:43 | named |
| `ProbeLJ132Counts.agda` | agents/reports/archive/lj-1.32-report.md:57 | named |
| `ProbeLJ132Ctrl0.agda` | agents/reports/archive/lj-1.32-report.md:54 | named |
| `ProbeLJ132Ctrl1.agda` | agents/reports/archive/lj-1.32-report.md:53 | named |
| `ProbeLJ132NotD0.agda` | agents/reports/archive/lj-1.32-report.md:56 | named |
| `ProbeLJ132Small0.agda` | agents/reports/archive/lj-1.32-report.md:55 | named |
| `ProbeLJ133.agda` | agents/reports/archive/lj-1.33-review.md:20 | line citation |
| `ProbeLJ133Ctrl.agda` | agents/reports/archive/lj-1.33-report.md:22 | named |
| `ProbeLJ134.agda` | dev/LESSONS.md:3092 | binding rule |
| `ProbeLJ134Cert.agda` | agents/reports/archive/lj-1.34-report.md:35 | named |
| `ProbeLJ135.agda` | agents/reports/archive/lj-1.38-report.md:242 | named |
| `ProbeLJ136.agda` | agents/reports/archive/lj-1.36-report.md:223 | line citation |
| `ProbeLJ136Ctrl.agda` | agents/reports/archive/lj-1.36-report.md:18 | named |
| `ProbeLJ137C.agda` | agents/reports/archive/lj-1.37-report.md:85 | named |
| `ProbeLJ137Ctrl.agda` | agents/reports/archive/lj-1.37-report.md:85 | named |
| `ProbeLJ138A.agda` | agents/reports/archive/lj-1.38-report.md:121 | named |
| `ProbeLJ138Ctrl.agda` | agents/reports/archive/lj-1.38-report.md:122 | named |
| `ProbeLJ139.agda` | agents/reports/lj-1.133-report.md:57 | named |
| `ProbeLJ139V2.agda` | agents/reports/lj-1.133-report.md:57 | named |
| `ProbeLJ140A.agda` | agents/reports/archive/lj-1.40-report.md:178 | named |
| `ProbeLJ140Ctrl.agda` | agents/reports/archive/lj-1.40-report.md:101 | named |
| `ProbeLJ141A.agda` | agents/reports/archive/lj-1.41-report.md:73 | named |
| `ProbeLJ141B.agda` | agents/reports/archive/lj-1.41-report.md:82 | named |
| `ProbeLJ141C.agda` | dev/LESSONS.md:3318 | binding rule |
| `ProbeLJ141Ctrl.agda` | agents/reports/archive/lj-1.41-review.md:31 | named |
| `ProbeLJ144A.agda` | agents/reports/archive/lj-1.44-report.md:75 | named |
| `ProbeLJ144D.agda` | agents/reports/archive/lj-1.44-report.md:27 | named |
| `ProbeLJ144E.agda` | agents/reports/archive/lj-1.44-report.md:27 | named |
| `ProbeLJ145A.agda` | agents/reports/archive/lj-1.45-report.md:33 | named |
| `ProbeLJ147Collapse.agda` | agents/reports/archive/lj-1.51-report.md:258 | named |
| `ProbeLJ147PairingGut.agda` | dev/LESSONS.md:3379 | binding rule |
| `ProbeLJ147PairingSealed.agda` | dev/LESSONS.md:3378 | binding rule |
| `ProbeLJ147SquareLawMin.agda` | agents/reports/archive/lj-1.47-report.md:305 | named |
| `ProbeLJ147SquareLawViaCol.agda` | agents/reports/archive/lj-1.51-report.md:258 | named |
| `ProbeLJ148.agda` | agents/reports/archive/lj-1.48-report.md:4 | named |
| `ProbeLJ148Cone.agda` | agents/reports/archive/lj-1.48-report.md:152 | named |
| `ProbeLJ149.agda` | agents/reports/archive/lj-1.50-report.md:161 | named |
| `ProbeLJ150Control.agda` | agents/reports/archive/lj-1.50-review.md:20 | line citation |
| `ProbeLJ150Linear.agda` | agents/reports/archive/lj-1.50-review.md:253 | line citation |
| `ProbeLJ150MatrixControl.agda` | agents/reports/archive/lj-1.50-review.md:255 | line citation |
| `ProbeLJ150MatrixLinear.agda` | agents/reports/archive/lj-1.50-report.md:91 | named |
| `ProbeLJ150MatrixSlots.agda` | agents/reports/archive/lj-1.50-review.md:254 | line citation |
| `ProbeLJ150Slots.agda` | agents/reports/archive/lj-1.50-review.md:253 | line citation |
| `ProbeLJ152A.agda` | agents/reports/archive/lj-1.57-report.md:141 | line citation |
| `ProbeLJ152B.agda` | agents/reports/archive/lj-1.57-report.md:139 | line citation |
| `ProbeLJ153A.agda` | agents/reports/archive/lj-1.53-report.md:40 | line citation |
| `ProbeLJ153Cone.agda` | agents/reports/archive/lj-1.53-report.md:8 | named |
| `ProbeLJ154A.agda` | agents/reports/lj-1.133-report.md:183 | line citation |
| `ProbeLJ155A.agda` | agents/reports/archive/lj-1.55-report.md:26 | line citation |
| `ProbeLJ155B.agda` | agents/reports/archive/lj-1.70-report.md:202 | line citation |
| `ProbeLJ155C.agda` | agents/reports/archive/lj-1.55-report.md:100 | line citation |
| `ProbeLJ156A.agda` | agents/reports/archive/lj-1.56-report.md:28 | line citation |
| `ProbeLJ156Cone.agda` | agents/reports/archive/lj-1.57-report.md:196 | named |
| `ProbeLJ156Shape.agda` | agents/reports/archive/lj-1.57-report.md:193 | named |
| `ProbeLJ157A.agda` | agents/reports/archive/lj-1.61-report.md:40 | line citation |
| `ProbeLJ157Cone.agda` | agents/reports/archive/lj-1.57-report.md:114 | named |
| `ProbeLJ158A.agda` | agents/reports/archive/lj-1.58-report.md:50 | named |
| `ProbeLJ158Cone.agda` | agents/reports/archive/lj-1.58-report.md:130 | named |
| `ProbeLJ161A.agda` | agents/reports/archive/tmp-cond-dd3aa13.lagda.md:6231 | named |
| `ProbeLJ161B.agda` | agents/reports/archive/lj-1.64-report.md:228 | named |
| `ProbeLJ17.agda` | dev/LESSONS.md:3458 | binding rule |
| `ProbeLJ171A.agda` | dev/LESSONS.md:3458 | binding rule |
| `ProbeLJ173A.agda` | agents/reports/archive/lj-1.74-report.md:171 | named |
| `ProbeLJ174A.agda` | agents/reports/lj-1.133-report.md:173 | named |
| `ProbeLJ174B.agda` | agents/reports/archive/lj-1.75-report.md:44 | line citation |
| `ProbeLJ174C.agda` | agents/reports/archive/lj-1.75-report.md:50 | line citation |
| `ProbeLJ174D.agda` | agents/reports/archive/lj-1.75-report.md:53 | line citation |
| `ProbeLJ174E.agda` | agents/reports/lj-1.133-report.md:176 | named |
| `ProbeLJ174F.agda` | agents/reports/archive/diag-twelve-row-math.md:64 | line citation |
| `ProbeLJ174P0.agda` | agents/reports/archive/diag-twelve-row-math.md:80 | line citation |
| `ProbeLJ174P1.agda` | agents/reports/archive/diag-twelve-row-math.md:428 | named |
| `ProbeLJ174P2.agda` | agents/reports/lj-1.133-report.md:176 | named |
| `ProbeLJ174P3.agda` | agents/reports/lj-1.133-report.md:176 | named |
| `ProbeLJ175A.agda` | agents/reports/archive/lj-1.76-report.md:185 | named |
| `ProbeLJ177A.agda` | dev/LESSONS.md:3489 | binding rule |
| `ProbeLJ178A.agda` | agents/reports/archive/lj-1.78-report.md:20 | line citation |
| `ProbeLJ179A.agda` | agents/reports/archive/lj-1.79-report.md:15 | named |
| `ProbeLJ17Cone.agda` | agents/reports/archive/lj-1.7-report.md:7 | named |
| `ProbeLJ17Skel.agda` | agents/reports/archive/lj-1.7-report.md:6 | named |
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
| `ProbeT136.agda` | agents/reports/archive/l3.32-t136-report.md:121 | named |
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
| `ProbeT198.agda` | agents/reports/archive/l3.32-t198-report.md:26 | named |
| `ProbeT204.agda` | agents/reports/archive/l3.32-t217-report.md:40 | line citation |
| `ProbeT211.agda` | agents/reports/archive/l3.32-t214-report.md:142 | named |
| `ProbeT214.agda` | agents/reports/archive/l3.32-t214-report.md:15 | named |
| `ProbeT222.agda` | agents/reports/archive/l3.32-t242-report.md:19 | line citation |
| `ProbeT237.agda` | dev/ledger.toml:1723 | binding rule |
| `ProbeT240.agda` | agents/reports/archive/l3.32-t245-report.md:93 | line citation |
| `ProbeT242.agda` | agents/reports/archive/l3.32-t242-report.md:71 | named |
| `ProbeT242b.agda` | agents/reports/archive/l3.32-t242-report.md:87 | named |
| `ProbeT249.agda` | agents/reports/archive/l3.32-t249-report.md:57 | line citation |
| `ProbeT251.agda` | agents/reports/archive/l3.32-t251-report.md:65 | line citation |
| `ProbeT258Base.agda` | agents/reports/archive/l3.32-t258-report.md:21 | named |
| `ProbeT258Ctr2.agda` | agents/reports/archive/l3.32-t258-report.md:27 | named |
| `ProbeT258Cure2.agda` | agents/reports/archive/l3.32-t258-report.md:26 | named |
| `ProbeT258GutPsi.agda` | agents/reports/archive/l3.32-t258-report.md:25 | named |
| `ProbeT258GutSeg.agda` | agents/reports/archive/l3.32-t258-report.md:24 | named |
| `ProbeT258NoConv.agda` | agents/reports/archive/l3.32-t258-report.md:23 | named |
| `ProbeT258NoUC.agda` | agents/reports/archive/l3.32-t258-report.md:22 | named |
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
