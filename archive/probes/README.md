# `archive/probes/`: a tombstone

**THIS DIRECTORY IS EMPTY AND NOTHING ARRIVES HERE AGAIN.** It held 257 probes
for part of one day, 2026-08-13. This file is the record of where they went.

## What happened, in order, on 2026-08-13

1. `[LJ-1.133]` swept 284 probes out of `src/` and archived 244 here, because a
   probe that a document points into is evidence for a checkable claim.
2. `[LJ-1.138]` gave the sweep a correct trigger and a real execution point.
3. **The owner ruled the same afternoon that a probe pairs one-to-one with its
   report, lives beside it, is tracked, and is NEVER deleted.** `[LJ-1.141]`
   moved all 257 to `agents/reports/<TASK>/` and retired the sweep.

**`dev/LESSONS.md` D-1 is the live rule. Read it there, not here.**

## Why a citation from before 2026-08-13 does not resolve

**A brief and a report are frozen records** (`[LJ-1.130]`): they are corrected
in the next document and never rewritten. So **216 briefs and 251 reports still
write `src/ProbeX.agda`**, and 65 citations still write
`archive/probes/ProbeX.agda`. Both are correct about the day they were written
and neither points at a file today.

**The table below is that map, and it is FROZEN.** It was generated once, at the
move, by the tool that is now retired
(`archive/tooling/check-probes-lifecycle.py --index`). Nothing regenerates it,
because nothing moves any more.

**The third column is the strongest citation each probe carried at the move**,
which is what justified keeping the file at all: `line citation` means a
document points INTO the file at a line number, `binding rule` means a `dev/`
document names it as a live rule's provenance, and `named` means a document
names it and nothing points in.

| Old path, as frozen briefs and reports cite it | Where it is now | Strongest citation at the move | Kind |
|---|---|---|---|
| `archive/probes/CutProbe.agda` | `agents/reports/Unpaired/CutProbe.agda` | agents/reports/archive/cut-probe-report.md:56 | line citation |
| `archive/probes/OrderProbe.agda` | `agents/reports/Unpaired/OrderProbe.agda` | agents/reports/archive/order-probe-report.md:133 | line citation |
| `archive/probes/ProbeBelowLim.agda` | `agents/reports/Unpaired/ProbeBelowLim.agda` | agents/reports/archive/l3.32-t127-report.md:87 | line citation |
| `archive/probes/ProbeCarried.agda` | `agents/reports/Unpaired/ProbeCarried.agda` | agents/reports/archive/l3.32-t53-report.md:14 | line citation |
| `archive/probes/ProbeDD25A.agda` | `agents/reports/DD25/ProbeDD25A.agda` | agents/reports/archive/lj-1.27-review.md:140 | named |
| `archive/probes/ProbeDD25B.agda` | `agents/reports/DD25/ProbeDD25B.agda` | agents/reports/lj-1.133-report.md:63 | named |
| `archive/probes/ProbeDD25B1.agda` | `agents/reports/DD25/ProbeDD25B1.agda` | agents/reports/lj-1.133-report.md:63 | named |
| `archive/probes/ProbeDD25B10.agda` | `agents/reports/DD25/ProbeDD25B10.agda` | agents/reports/archive/lj-1.32-review.md:192 | named |
| `archive/probes/ProbeDD25B11.agda` | `agents/reports/DD25/ProbeDD25B11.agda` | agents/reports/archive/lj-1.32-review.md:193 | named |
| `archive/probes/ProbeDD25B12.agda` | `agents/reports/DD25/ProbeDD25B12.agda` | agents/reports/archive/lj-1.32-review.md:194 | named |
| `archive/probes/ProbeDD25B13.agda` | `agents/reports/DD25/ProbeDD25B13.agda` | agents/reports/lj-1.133-report.md:63 | named |
| `archive/probes/ProbeDD25B14.agda` | `agents/reports/DD25/ProbeDD25B14.agda` | agents/reports/archive/lj-1.32-review.md:196 | named |
| `archive/probes/ProbeDD25B2.agda` | `agents/reports/DD25/ProbeDD25B2.agda` | agents/reports/archive/lj-1.32-review.md:389 | named |
| `archive/probes/ProbeDD25B3.agda` | `agents/reports/DD25/ProbeDD25B3.agda` | agents/reports/archive/lj-1.32-review.md:137 | named |
| `archive/probes/ProbeDD25B4.agda` | `agents/reports/DD25/ProbeDD25B4.agda` | agents/reports/archive/lj-1.32-review.md:178 | named |
| `archive/probes/ProbeDD25B5.agda` | `agents/reports/DD25/ProbeDD25B5.agda` | agents/reports/archive/lj-1.32-review.md:167 | named |
| `archive/probes/ProbeDD25Bd04.agda` | `agents/reports/DD25/ProbeDD25Bd04.agda` | agents/reports/archive/lj-1.32-review.md:206 | named |
| `archive/probes/ProbeDD25Bd08.agda` | `agents/reports/DD25/ProbeDD25Bd08.agda` | agents/reports/archive/lj-1.32-review.md:207 | named |
| `archive/probes/ProbeDD25Bd12.agda` | `agents/reports/DD25/ProbeDD25Bd12.agda` | agents/reports/archive/lj-1.32-review.md:208 | named |
| `archive/probes/ProbeDD25Bd16.agda` | `agents/reports/DD25/ProbeDD25Bd16.agda` | agents/reports/archive/lj-1.32-review.md:209 | named |
| `archive/probes/ProbeDD25Bd20.agda` | `agents/reports/DD25/ProbeDD25Bd20.agda` | agents/reports/archive/lj-1.32-review.md:210 | named |
| `archive/probes/ProbeDD25C.agda` | `agents/reports/DD25/ProbeDD25C.agda` | dev/LESSONS.md:2944 | binding rule |
| `archive/probes/ProbeDD25CB.agda` | `agents/reports/DD25/ProbeDD25CB.agda` | agents/reports/archive/lj-1.33-review.md:70 | named |
| `archive/probes/ProbeDD25CD.agda` | `agents/reports/DD25/ProbeDD25CD.agda` | agents/reports/archive/lj-1.35-report.md:43 | line citation |
| `archive/probes/ProbeDD25CE.agda` | `agents/reports/DD25/ProbeDD25CE.agda` | agents/reports/archive/lj-1.33-review.md:38 | line citation |
| `archive/probes/ProbeDD25CF.agda` | `agents/reports/DD25/ProbeDD25CF.agda` | agents/reports/archive/lj-1.33-review.md:238 | named |
| `archive/probes/ProbeDD25CL.agda` | `agents/reports/DD25/ProbeDD25CL.agda` | agents/reports/archive/lj-1.33-review.md:71 | named |
| `archive/probes/ProbeDD25CM.agda` | `agents/reports/DD25/ProbeDD25CM.agda` | agents/reports/archive/lj-1.33-review.md:95 | named |
| `archive/probes/ProbeDD25CS.agda` | `agents/reports/DD25/ProbeDD25CS.agda` | agents/reports/archive/lj-1.33-review.md:47 | line citation |
| `archive/probes/ProbeDD25D.agda` | `agents/reports/DD25/ProbeDD25D.agda` | dev/LESSONS.md:2944 | binding rule |
| `archive/probes/ProbeDD25D1.agda` | `agents/reports/DD25/ProbeDD25D1.agda` | agents/reports/archive/lj-1.34-review.md:50 | named |
| `archive/probes/ProbeDD25D2.agda` | `agents/reports/DD25/ProbeDD25D2.agda` | agents/reports/archive/lj-1.41-review.md:191 | line citation |
| `archive/probes/ProbeDD25D3.agda` | `agents/reports/DD25/ProbeDD25D3.agda` | agents/reports/archive/lj-1.34-review.md:51 | named |
| `archive/probes/ProbeDD25D4.agda` | `agents/reports/DD25/ProbeDD25D4.agda` | agents/reports/archive/lj-1.34-review.md:52 | named |
| `archive/probes/ProbeDD25D5.agda` | `agents/reports/DD25/ProbeDD25D5.agda` | dev/LESSONS.md:3092 | binding rule |
| `archive/probes/ProbeDD25E.agda` | `agents/reports/DD25/ProbeDD25E.agda` | dev/LESSONS.md:2944 | binding rule |
| `archive/probes/ProbeDD25E1.agda` | `agents/reports/DD25/ProbeDD25E1.agda` | dev/LESSONS.md:3226 | binding rule |
| `archive/probes/ProbeDD25E2.agda` | `agents/reports/DD25/ProbeDD25E2.agda` | agents/reports/archive/tmp-cond-dd3aa13.lagda.md:2505 | named |
| `archive/probes/ProbeDD25E3.agda` | `agents/reports/DD25/ProbeDD25E3.agda` | dev/LESSONS.md:3226 | binding rule |
| `archive/probes/ProbeDD25F.agda` | `agents/reports/DD25/ProbeDD25F.agda` | dev/LESSONS.md:3307 | binding rule |
| `archive/probes/ProbeDD25F41A.agda` | `agents/reports/DD25/ProbeDD25F41A.agda` | dev/LESSONS.md:3307 | binding rule |
| `archive/probes/ProbeDD25F41B.agda` | `agents/reports/DD25/ProbeDD25F41B.agda` | dev/LESSONS.md:3309 | binding rule |
| `archive/probes/ProbeDD25F41C.agda` | `agents/reports/DD25/ProbeDD25F41C.agda` | agents/reports/lj-1.133-report.md:498 | named |
| `archive/probes/ProbeDD25F41D.agda` | `agents/reports/DD25/ProbeDD25F41D.agda` | dev/LESSONS.md:3314 | binding rule |
| `archive/probes/ProbeDD25G.agda` | `agents/reports/DD25/ProbeDD25G.agda` | dev/LESSONS.md:3424 | binding rule |
| `archive/probes/ProbeDD25G1.agda` | `agents/reports/DD25/ProbeDD25G1.agda` | dev/LESSONS.md:3424 | binding rule |
| `archive/probes/ProbeDD25G2.agda` | `agents/reports/DD25/ProbeDD25G2.agda` | agents/reports/archive/lj-1.7-review.md:26 | line citation |
| `archive/probes/ProbeDD25G2Cone.agda` | `agents/reports/DD25/ProbeDD25G2Cone.agda` | agents/reports/archive/lj-1.7-review.md:9 | named |
| `archive/probes/ProbeDD25G3.agda` | `agents/reports/DD25/ProbeDD25G3.agda` | agents/reports/archive/lj-1.63-report.md:64 | line citation |
| `archive/probes/ProbeDD25H.agda` | `agents/reports/DD25/ProbeDD25H.agda` | agents/reports/archive/lj-1.53-report.md:80 | named |
| `archive/probes/ProbeDD25H1.agda` | `agents/reports/DD25/ProbeDD25H1.agda` | agents/reports/archive/lj-1.50-review.md:5 | named |
| `archive/probes/ProbeDD25H2.agda` | `agents/reports/DD25/ProbeDD25H2.agda` | agents/reports/archive/lj-1.53-report.md:80 | named |
| `archive/probes/ProbeDD25H2N.agda` | `agents/reports/DD25/ProbeDD25H2N.agda` | agents/reports/archive/lj-1.50-review.md:6 | named |
| `archive/probes/ProbeDD25H3.agda` | `agents/reports/DD25/ProbeDD25H3.agda` | agents/reports/archive/lj-1.50-review.md:21 | line citation |
| `archive/probes/ProbeDD25H4.agda` | `agents/reports/DD25/ProbeDD25H4.agda` | agents/reports/archive/lj-1.50-review.md:400 | line citation |
| `archive/probes/ProbeDD25H5.agda` | `agents/reports/DD25/ProbeDD25H5.agda` | agents/reports/archive/lj-1.50-review.md:146 | named |
| `archive/probes/ProbeDD25H6.agda` | `agents/reports/DD25/ProbeDD25H6.agda` | agents/reports/archive/lj-1.50-review.md:271 | named |
| `archive/probes/ProbeDD25H7.agda` | `agents/reports/DD25/ProbeDD25H7.agda` | agents/reports/archive/lj-1.50-review.md:27 | named |
| `archive/probes/ProbeDD25H8.agda` | `agents/reports/DD25/ProbeDD25H8.agda` | agents/reports/archive/lj-1.50-review.md:505 | line citation |
| `archive/probes/ProbeDefStep.agda` | `agents/reports/Unpaired/ProbeDefStep.agda` | agents/reports/archive/l3.32-t66-report.md:48 | line citation |
| `archive/probes/ProbeLJ1100A.agda` | `agents/reports/LJ-1-100/ProbeLJ1100A.agda` | agents/reports/lj-1.100-report.md:10 | line citation |
| `archive/probes/ProbeLJ1101A.agda` | `agents/reports/LJ-1-101/ProbeLJ1101A.agda` | agents/reports/lj-1.101-report.md:17 | line citation |
| `archive/probes/ProbeLJ1102A.agda` | `agents/reports/LJ-1-102/ProbeLJ1102A.agda` | agents/reports/lj-1.102-report.md:11 | line citation |
| `archive/probes/ProbeLJ1103A.agda` | `agents/reports/LJ-1-103/ProbeLJ1103A.agda` | agents/reports/lj-1.103-report.md:91 | line citation |
| `archive/probes/ProbeLJ1104A.agda` | `agents/reports/LJ-1-104/ProbeLJ1104A.agda` | agents/reports/lj-1.105-report.md:111 | line citation |
| `archive/probes/ProbeLJ1105A.agda` | `agents/reports/LJ-1-105/ProbeLJ1105A.agda` | agents/reports/lj-1.133-report.md:62 | named |
| `archive/probes/ProbeLJ1106A.agda` | `agents/reports/LJ-1-106/ProbeLJ1106A.agda` | agents/reports/lj-1.107-report.md:70 | line citation |
| `archive/probes/ProbeLJ1107A.agda` | `agents/reports/LJ-1-107/ProbeLJ1107A.agda` | agents/reports/lj-1.118-report.md:38 | line citation |
| `archive/probes/ProbeLJ1109A.agda` | `agents/reports/LJ-1-109/ProbeLJ1109A.agda` | dev/LESSONS.md:3594 | binding rule |
| `archive/probes/ProbeLJ1111A.agda` | `agents/reports/LJ-1-111/ProbeLJ1111A.agda` | agents/reports/lj-1.111-report.md:31 | line citation |
| `archive/probes/ProbeLJ1111B.agda` | `agents/reports/LJ-1-111/ProbeLJ1111B.agda` | agents/reports/lj-1.114-report.md:51 | line citation |
| `archive/probes/ProbeLJ1112A.agda` | `agents/reports/LJ-1-112/ProbeLJ1112A.agda` | agents/reports/lj-1.113-report.md:31 | line citation |
| `archive/probes/ProbeLJ1114A.agda` | `agents/reports/LJ-1-114/ProbeLJ1114A.agda` | agents/reports/lj-1.134-report.md:281 | line citation |
| `archive/probes/ProbeLJ1115A.agda` | `agents/reports/LJ-1-115/ProbeLJ1115A.agda` | agents/reports/lj-1.115-report.md:12 | line citation |
| `archive/probes/ProbeLJ1115B.agda` | `agents/reports/LJ-1-115/ProbeLJ1115B.agda` | agents/reports/lj-1.115-report.md:18 | line citation |
| `archive/probes/ProbeLJ1116A.agda` | `agents/reports/LJ-1-116/ProbeLJ1116A.agda` | agents/reports/lj-1.116-report.md:49 | line citation |
| `archive/probes/ProbeLJ1117A.agda` | `agents/reports/LJ-1-117/ProbeLJ1117A.agda` | agents/reports/lj-1.118-report.md:168 | line citation |
| `archive/probes/ProbeLJ1118A.agda` | `agents/reports/LJ-1-118/ProbeLJ1118A.agda` | agents/reports/lj-1.118-report.md:20 | line citation |
| `archive/probes/ProbeLJ1119A.agda` | `agents/reports/LJ-1-119/ProbeLJ1119A.agda` | agents/reports/lj-1.121-report.md:15 | line citation |
| `archive/probes/ProbeLJ1120A.agda` | `agents/reports/LJ-1-120/ProbeLJ1120A.agda` | agents/reports/lj-1.120-report.md:9 | line citation |
| `archive/probes/ProbeLJ1120B.agda` | `agents/reports/LJ-1-120/ProbeLJ1120B.agda` | agents/reports/lj-1.120-report.md:13 | line citation |
| `archive/probes/ProbeLJ1120C.agda` | `agents/reports/LJ-1-120/ProbeLJ1120C.agda` | agents/reports/lj-1.120-report.md:113 | line citation |
| `archive/probes/ProbeLJ1121A.agda` | `agents/reports/LJ-1-121/ProbeLJ1121A.agda` | agents/reports/lj-1.121-report.md:95 | line citation |
| `archive/probes/ProbeLJ1122A.agda` | `agents/reports/LJ-1-122/ProbeLJ1122A.agda` | agents/reports/lj-1.122-report.md:93 | named |
| `archive/probes/ProbeLJ1122B.agda` | `agents/reports/LJ-1-122/ProbeLJ1122B.agda` | agents/reports/lj-1.122-report.md:16 | named |
| `archive/probes/ProbeLJ1124A.agda` | `agents/reports/LJ-1-124/ProbeLJ1124A.agda` | agents/reports/lj-1.124-report.md:25 | line citation |
| `archive/probes/ProbeLJ1125A.agda` | `agents/reports/LJ-1-125/ProbeLJ1125A.agda` | agents/reports/lj-1.125-report.md:45 | line citation |
| `archive/probes/ProbeLJ1125B.agda` | `agents/reports/LJ-1-125/ProbeLJ1125B.agda` | agents/reports/lj-1.125-report.md:21 | line citation |
| `archive/probes/ProbeLJ115.agda` | `agents/reports/LJ-1-15/ProbeLJ115.agda` | agents/reports/archive/lj-1.15-report.md:19 | line citation |
| `archive/probes/ProbeLJ115b.agda` | `agents/reports/LJ-1-15/ProbeLJ115b.agda` | agents/reports/archive/lj-1.15-report.md:120 | line citation |
| `archive/probes/ProbeLJ117Combinators.agda` | `agents/reports/LJ-1-17/ProbeLJ117Combinators.agda` | agents/reports/archive/lj-1.17-review.md:241 | named |
| `archive/probes/ProbeLJ117Pairing.agda` | `agents/reports/LJ-1-17/ProbeLJ117Pairing.agda` | agents/reports/archive/lj-1.17-review.md:240 | named |
| `archive/probes/ProbeLJ117SquareLaw.agda` | `agents/reports/LJ-1-17/ProbeLJ117SquareLaw.agda` | agents/reports/lj-1.107-report.md:241 | named |
| `archive/probes/ProbeLJ118.agda` | `agents/reports/LJ-1-18/ProbeLJ118.agda` | agents/reports/archive/lj-1.18-report.md:29 | line citation |
| `archive/probes/ProbeLJ119.agda` | `agents/reports/LJ-1-19/ProbeLJ119.agda` | agents/reports/archive/lj-1.19-report.md:8 | line citation |
| `archive/probes/ProbeLJ124Arm1.agda` | `agents/reports/LJ-1-24/ProbeLJ124Arm1.agda` | agents/reports/archive/lj-1.25-report.md:89 | line citation |
| `archive/probes/ProbeLJ124Base.agda` | `agents/reports/LJ-1-24/ProbeLJ124Base.agda` | agents/reports/archive/lj-1.63-report.md:68 | named |
| `archive/probes/ProbeLJ124Control.agda` | `agents/reports/LJ-1-24/ProbeLJ124Control.agda` | agents/reports/archive/lj-1.24-report.md:14 | named |
| `archive/probes/ProbeLJ127.agda` | `agents/reports/LJ-1-27/ProbeLJ127.agda` | agents/reports/archive/lj-1.27-report.md:29 | line citation |
| `archive/probes/ProbeLJ130A.agda` | `agents/reports/LJ-1-30/ProbeLJ130A.agda` | agents/reports/archive/lj-1.30-report.md:16 | named |
| `archive/probes/ProbeLJ130B.agda` | `agents/reports/LJ-1-30/ProbeLJ130B.agda` | agents/reports/lj-1.133-report.md:59 | named |
| `archive/probes/ProbeLJ131.agda` | `agents/reports/LJ-1-31/ProbeLJ131.agda` | agents/reports/archive/lj-1.32-report.md:118 | named |
| `archive/probes/ProbeLJ132C0.agda` | `agents/reports/LJ-1-32/ProbeLJ132C0.agda` | agents/reports/archive/lj-1.32-report.md:40 | named |
| `archive/probes/ProbeLJ132C2.agda` | `agents/reports/LJ-1-32/ProbeLJ132C2.agda` | agents/reports/archive/lj-1.32-report.md:42 | named |
| `archive/probes/ProbeLJ132C5.agda` | `agents/reports/LJ-1-32/ProbeLJ132C5.agda` | agents/reports/archive/lj-1.32-report.md:43 | named |
| `archive/probes/ProbeLJ132Counts.agda` | `agents/reports/LJ-1-32/ProbeLJ132Counts.agda` | agents/reports/archive/lj-1.32-report.md:57 | named |
| `archive/probes/ProbeLJ132Ctrl0.agda` | `agents/reports/LJ-1-32/ProbeLJ132Ctrl0.agda` | agents/reports/archive/lj-1.32-report.md:54 | named |
| `archive/probes/ProbeLJ132Ctrl1.agda` | `agents/reports/LJ-1-32/ProbeLJ132Ctrl1.agda` | agents/reports/archive/lj-1.32-report.md:53 | named |
| `archive/probes/ProbeLJ132NotD0.agda` | `agents/reports/LJ-1-32/ProbeLJ132NotD0.agda` | agents/reports/archive/lj-1.32-report.md:56 | named |
| `archive/probes/ProbeLJ132Small0.agda` | `agents/reports/LJ-1-32/ProbeLJ132Small0.agda` | agents/reports/archive/lj-1.32-report.md:55 | named |
| `archive/probes/ProbeLJ133.agda` | `agents/reports/LJ-1-33/ProbeLJ133.agda` | agents/reports/archive/lj-1.33-review.md:20 | line citation |
| `archive/probes/ProbeLJ133Ctrl.agda` | `agents/reports/LJ-1-33/ProbeLJ133Ctrl.agda` | agents/reports/archive/lj-1.33-report.md:22 | named |
| `archive/probes/ProbeLJ134.agda` | `agents/reports/LJ-1-34/ProbeLJ134.agda` | dev/LESSONS.md:3092 | binding rule |
| `archive/probes/ProbeLJ134Cert.agda` | `agents/reports/LJ-1-34/ProbeLJ134Cert.agda` | agents/reports/archive/lj-1.34-report.md:35 | named |
| `archive/probes/ProbeLJ135.agda` | `agents/reports/LJ-1-35/ProbeLJ135.agda` | agents/reports/archive/lj-1.38-report.md:242 | named |
| `archive/probes/ProbeLJ136.agda` | `agents/reports/LJ-1-36/ProbeLJ136.agda` | agents/reports/archive/lj-1.36-report.md:223 | line citation |
| `archive/probes/ProbeLJ136Ctrl.agda` | `agents/reports/LJ-1-36/ProbeLJ136Ctrl.agda` | agents/reports/archive/lj-1.36-report.md:18 | named |
| `archive/probes/ProbeLJ137C.agda` | `agents/reports/LJ-1-37/ProbeLJ137C.agda` | agents/reports/archive/lj-1.37-report.md:85 | named |
| `archive/probes/ProbeLJ137Ctrl.agda` | `agents/reports/LJ-1-37/ProbeLJ137Ctrl.agda` | agents/reports/archive/lj-1.37-report.md:85 | named |
| `archive/probes/ProbeLJ138A.agda` | `agents/reports/LJ-1-38/ProbeLJ138A.agda` | agents/reports/archive/lj-1.38-report.md:121 | named |
| `archive/probes/ProbeLJ138Ctrl.agda` | `agents/reports/LJ-1-38/ProbeLJ138Ctrl.agda` | agents/reports/archive/lj-1.38-report.md:122 | named |
| `archive/probes/ProbeLJ139.agda` | `agents/reports/LJ-1-39/ProbeLJ139.agda` | agents/reports/lj-1.133-report.md:57 | named |
| `archive/probes/ProbeLJ139V2.agda` | `agents/reports/LJ-1-39/ProbeLJ139V2.agda` | agents/reports/lj-1.133-report.md:57 | named |
| `archive/probes/ProbeLJ140A.agda` | `agents/reports/LJ-1-40/ProbeLJ140A.agda` | agents/reports/archive/lj-1.40-report.md:178 | named |
| `archive/probes/ProbeLJ140Ctrl.agda` | `agents/reports/LJ-1-40/ProbeLJ140Ctrl.agda` | agents/reports/archive/lj-1.40-report.md:101 | named |
| `archive/probes/ProbeLJ141A.agda` | `agents/reports/LJ-1-41/ProbeLJ141A.agda` | agents/reports/archive/lj-1.41-report.md:73 | named |
| `archive/probes/ProbeLJ141B.agda` | `agents/reports/LJ-1-41/ProbeLJ141B.agda` | agents/reports/archive/lj-1.41-report.md:82 | named |
| `archive/probes/ProbeLJ141C.agda` | `agents/reports/LJ-1-41/ProbeLJ141C.agda` | dev/LESSONS.md:3318 | binding rule |
| `archive/probes/ProbeLJ141Ctrl.agda` | `agents/reports/LJ-1-41/ProbeLJ141Ctrl.agda` | agents/reports/archive/lj-1.41-review.md:31 | named |
| `archive/probes/ProbeLJ144A.agda` | `agents/reports/LJ-1-44/ProbeLJ144A.agda` | agents/reports/archive/lj-1.44-report.md:75 | named |
| `archive/probes/ProbeLJ144D.agda` | `agents/reports/LJ-1-44/ProbeLJ144D.agda` | agents/reports/archive/lj-1.44-report.md:27 | named |
| `archive/probes/ProbeLJ144E.agda` | `agents/reports/LJ-1-44/ProbeLJ144E.agda` | agents/reports/archive/lj-1.44-report.md:27 | named |
| `archive/probes/ProbeLJ145A.agda` | `agents/reports/LJ-1-45/ProbeLJ145A.agda` | agents/reports/archive/lj-1.45-report.md:33 | named |
| `archive/probes/ProbeLJ147Collapse.agda` | `agents/reports/LJ-1-47/ProbeLJ147Collapse.agda` | agents/reports/archive/lj-1.51-report.md:258 | named |
| `archive/probes/ProbeLJ147PairingGut.agda` | `agents/reports/LJ-1-47/ProbeLJ147PairingGut.agda` | dev/LESSONS.md:3379 | binding rule |
| `archive/probes/ProbeLJ147PairingSealed.agda` | `agents/reports/LJ-1-47/ProbeLJ147PairingSealed.agda` | dev/LESSONS.md:3378 | binding rule |
| `archive/probes/ProbeLJ147SquareLawMin.agda` | `agents/reports/LJ-1-47/ProbeLJ147SquareLawMin.agda` | agents/reports/archive/lj-1.47-report.md:305 | named |
| `archive/probes/ProbeLJ147SquareLawViaCol.agda` | `agents/reports/LJ-1-47/ProbeLJ147SquareLawViaCol.agda` | agents/reports/archive/lj-1.51-report.md:258 | named |
| `archive/probes/ProbeLJ148.agda` | `agents/reports/LJ-1-48/ProbeLJ148.agda` | agents/reports/archive/lj-1.48-report.md:4 | named |
| `archive/probes/ProbeLJ148Cone.agda` | `agents/reports/LJ-1-48/ProbeLJ148Cone.agda` | agents/reports/archive/lj-1.48-report.md:152 | named |
| `archive/probes/ProbeLJ149.agda` | `agents/reports/LJ-1-49/ProbeLJ149.agda` | agents/reports/archive/lj-1.50-report.md:161 | named |
| `archive/probes/ProbeLJ150Control.agda` | `agents/reports/LJ-1-50/ProbeLJ150Control.agda` | agents/reports/archive/lj-1.50-review.md:20 | line citation |
| `archive/probes/ProbeLJ150Linear.agda` | `agents/reports/LJ-1-50/ProbeLJ150Linear.agda` | agents/reports/archive/lj-1.50-review.md:253 | line citation |
| `archive/probes/ProbeLJ150MatrixControl.agda` | `agents/reports/LJ-1-50/ProbeLJ150MatrixControl.agda` | agents/reports/archive/lj-1.50-review.md:255 | line citation |
| `archive/probes/ProbeLJ150MatrixLinear.agda` | `agents/reports/LJ-1-50/ProbeLJ150MatrixLinear.agda` | agents/reports/archive/lj-1.50-report.md:91 | named |
| `archive/probes/ProbeLJ150MatrixSlots.agda` | `agents/reports/LJ-1-50/ProbeLJ150MatrixSlots.agda` | agents/reports/archive/lj-1.50-review.md:254 | line citation |
| `archive/probes/ProbeLJ150Slots.agda` | `agents/reports/LJ-1-50/ProbeLJ150Slots.agda` | agents/reports/archive/lj-1.50-review.md:253 | line citation |
| `archive/probes/ProbeLJ152A.agda` | `agents/reports/LJ-1-52/ProbeLJ152A.agda` | agents/reports/archive/lj-1.57-report.md:141 | line citation |
| `archive/probes/ProbeLJ152B.agda` | `agents/reports/LJ-1-52/ProbeLJ152B.agda` | agents/reports/archive/lj-1.57-report.md:139 | line citation |
| `archive/probes/ProbeLJ153A.agda` | `agents/reports/LJ-1-53/ProbeLJ153A.agda` | agents/reports/archive/lj-1.53-report.md:40 | line citation |
| `archive/probes/ProbeLJ153Cone.agda` | `agents/reports/LJ-1-53/ProbeLJ153Cone.agda` | agents/reports/archive/lj-1.53-report.md:8 | named |
| `archive/probes/ProbeLJ154A.agda` | `agents/reports/LJ-1-54/ProbeLJ154A.agda` | agents/reports/lj-1.133-report.md:183 | line citation |
| `archive/probes/ProbeLJ155A.agda` | `agents/reports/LJ-1-55/ProbeLJ155A.agda` | agents/reports/archive/lj-1.55-report.md:26 | line citation |
| `archive/probes/ProbeLJ155B.agda` | `agents/reports/LJ-1-55/ProbeLJ155B.agda` | agents/reports/archive/lj-1.70-report.md:202 | line citation |
| `archive/probes/ProbeLJ155C.agda` | `agents/reports/LJ-1-55/ProbeLJ155C.agda` | agents/reports/archive/lj-1.55-report.md:100 | line citation |
| `archive/probes/ProbeLJ156A.agda` | `agents/reports/LJ-1-56/ProbeLJ156A.agda` | agents/reports/archive/lj-1.56-report.md:28 | line citation |
| `archive/probes/ProbeLJ156Cone.agda` | `agents/reports/LJ-1-56/ProbeLJ156Cone.agda` | agents/reports/archive/lj-1.57-report.md:196 | named |
| `archive/probes/ProbeLJ156Shape.agda` | `agents/reports/LJ-1-56/ProbeLJ156Shape.agda` | agents/reports/archive/lj-1.57-report.md:193 | named |
| `archive/probes/ProbeLJ157A.agda` | `agents/reports/LJ-1-57/ProbeLJ157A.agda` | agents/reports/archive/lj-1.61-report.md:40 | line citation |
| `archive/probes/ProbeLJ157Cone.agda` | `agents/reports/LJ-1-57/ProbeLJ157Cone.agda` | agents/reports/archive/lj-1.57-report.md:114 | named |
| `archive/probes/ProbeLJ158A.agda` | `agents/reports/LJ-1-58/ProbeLJ158A.agda` | agents/reports/archive/lj-1.58-report.md:50 | named |
| `archive/probes/ProbeLJ158Cone.agda` | `agents/reports/LJ-1-58/ProbeLJ158Cone.agda` | agents/reports/archive/lj-1.58-report.md:130 | named |
| `archive/probes/ProbeLJ161A.agda` | `agents/reports/LJ-1-61/ProbeLJ161A.agda` | agents/reports/archive/tmp-cond-dd3aa13.lagda.md:6231 | named |
| `archive/probes/ProbeLJ161B.agda` | `agents/reports/LJ-1-61/ProbeLJ161B.agda` | agents/reports/archive/lj-1.64-report.md:228 | named |
| `archive/probes/ProbeLJ17.agda` | `agents/reports/LJ-1-7/ProbeLJ17.agda` | dev/LESSONS.md:3458 | binding rule |
| `archive/probes/ProbeLJ171A.agda` | `agents/reports/LJ-1-71/ProbeLJ171A.agda` | dev/LESSONS.md:3458 | binding rule |
| `archive/probes/ProbeLJ173A.agda` | `agents/reports/LJ-1-73/ProbeLJ173A.agda` | agents/reports/archive/lj-1.74-report.md:171 | named |
| `archive/probes/ProbeLJ174A.agda` | `agents/reports/LJ-1-74/ProbeLJ174A.agda` | agents/reports/lj-1.133-report.md:173 | named |
| `archive/probes/ProbeLJ174B.agda` | `agents/reports/LJ-1-74/ProbeLJ174B.agda` | agents/reports/archive/lj-1.75-report.md:44 | line citation |
| `archive/probes/ProbeLJ174C.agda` | `agents/reports/LJ-1-74/ProbeLJ174C.agda` | agents/reports/archive/lj-1.75-report.md:50 | line citation |
| `archive/probes/ProbeLJ174D.agda` | `agents/reports/LJ-1-74/ProbeLJ174D.agda` | agents/reports/archive/lj-1.75-report.md:53 | line citation |
| `archive/probes/ProbeLJ174E.agda` | `agents/reports/LJ-1-74/ProbeLJ174E.agda` | agents/reports/lj-1.133-report.md:176 | named |
| `archive/probes/ProbeLJ174F.agda` | `agents/reports/LJ-1-74/ProbeLJ174F.agda` | agents/reports/archive/diag-twelve-row-math.md:64 | line citation |
| `archive/probes/ProbeLJ174P0.agda` | `agents/reports/LJ-1-74/ProbeLJ174P0.agda` | agents/reports/archive/diag-twelve-row-math.md:80 | line citation |
| `archive/probes/ProbeLJ174P1.agda` | `agents/reports/LJ-1-74/ProbeLJ174P1.agda` | agents/reports/archive/diag-twelve-row-math.md:428 | named |
| `archive/probes/ProbeLJ174P2.agda` | `agents/reports/LJ-1-74/ProbeLJ174P2.agda` | agents/reports/lj-1.133-report.md:176 | named |
| `archive/probes/ProbeLJ174P3.agda` | `agents/reports/LJ-1-74/ProbeLJ174P3.agda` | agents/reports/lj-1.133-report.md:176 | named |
| `archive/probes/ProbeLJ175A.agda` | `agents/reports/LJ-1-75/ProbeLJ175A.agda` | agents/reports/archive/lj-1.76-report.md:185 | named |
| `archive/probes/ProbeLJ177A.agda` | `agents/reports/LJ-1-77/ProbeLJ177A.agda` | dev/LESSONS.md:3489 | binding rule |
| `archive/probes/ProbeLJ178A.agda` | `agents/reports/LJ-1-78/ProbeLJ178A.agda` | agents/reports/archive/lj-1.78-report.md:20 | line citation |
| `archive/probes/ProbeLJ179A.agda` | `agents/reports/LJ-1-79/ProbeLJ179A.agda` | agents/reports/archive/lj-1.79-report.md:15 | named |
| `archive/probes/ProbeLJ17Cone.agda` | `agents/reports/LJ-1-7/ProbeLJ17Cone.agda` | agents/reports/archive/lj-1.7-report.md:7 | named |
| `archive/probes/ProbeLJ17Skel.agda` | `agents/reports/LJ-1-7/ProbeLJ17Skel.agda` | agents/reports/archive/lj-1.7-report.md:6 | named |
| `archive/probes/ProbeLJ180A.agda` | `agents/reports/LJ-1-80/ProbeLJ180A.agda` | agents/reports/archive/lj-1.81-report.md:97 | line citation |
| `archive/probes/ProbeLJ182A.agda` | `agents/reports/LJ-1-82/ProbeLJ182A.agda` | agents/reports/archive/lj-1.82-report.md:12 | line citation |
| `archive/probes/ProbeLJ183A.agda` | `agents/reports/LJ-1-83/ProbeLJ183A.agda` | agents/reports/archive/lj-1.83-report.md:24 | line citation |
| `archive/probes/ProbeLJ184A.agda` | `agents/reports/LJ-1-84/ProbeLJ184A.agda` | agents/reports/archive/lj-1.84-report.md:38 | line citation |
| `archive/probes/ProbeLJ185A.agda` | `agents/reports/LJ-1-85/ProbeLJ185A.agda` | agents/reports/archive/lj-1.85-report.md:68 | line citation |
| `archive/probes/ProbeLJ185B.agda` | `agents/reports/LJ-1-85/ProbeLJ185B.agda` | agents/reports/archive/lj-1.87-report.md:216 | line citation |
| `archive/probes/ProbeLJ185C.agda` | `agents/reports/LJ-1-85/ProbeLJ185C.agda` | agents/reports/archive/lj-1.85-report.md:81 | line citation |
| `archive/probes/ProbeLJ186A.agda` | `agents/reports/LJ-1-86/ProbeLJ186A.agda` | agents/reports/lj-1.90-report.md:93 | line citation |
| `archive/probes/ProbeLJ187A.agda` | `agents/reports/LJ-1-87/ProbeLJ187A.agda` | agents/reports/archive/lj-1.87-report.md:153 | line citation |
| `archive/probes/ProbeLJ187B.agda` | `agents/reports/LJ-1-87/ProbeLJ187B.agda` | agents/reports/archive/lj-1.87-report.md:35 | line citation |
| `archive/probes/ProbeLJ188A.agda` | `agents/reports/LJ-1-88/ProbeLJ188A.agda` | agents/reports/archive/lj-1.88-report.md:29 | line citation |
| `archive/probes/ProbeLJ189A.agda` | `agents/reports/LJ-1-89/ProbeLJ189A.agda` | agents/reports/lj-1.90-report.md:108 | line citation |
| `archive/probes/ProbeLJ190A.agda` | `agents/reports/LJ-1-90/ProbeLJ190A.agda` | agents/reports/lj-1.94-report.md:21 | line citation |
| `archive/probes/ProbeLJ192A.agda` | `agents/reports/LJ-1-92/ProbeLJ192A.agda` | agents/reports/lj-1.92-report.md:72 | line citation |
| `archive/probes/ProbeLJ193A.agda` | `agents/reports/LJ-1-93/ProbeLJ193A.agda` | agents/reports/lj-1.93-report.md:56 | line citation |
| `archive/probes/ProbeLJ193B.agda` | `agents/reports/LJ-1-93/ProbeLJ193B.agda` | agents/reports/lj-1.93-report.md:15 | named |
| `archive/probes/ProbeLJ193C.agda` | `agents/reports/LJ-1-93/ProbeLJ193C.agda` | agents/reports/lj-1.113-report.md:121 | line citation |
| `archive/probes/ProbeLJ194A.agda` | `agents/reports/LJ-1-94/ProbeLJ194A.agda` | agents/reports/lj-1.101-report.md:20 | line citation |
| `archive/probes/ProbeLJ195A.agda` | `agents/reports/LJ-1-95/ProbeLJ195A.agda` | agents/reports/lj-1.95-report.md:9 | line citation |
| `archive/probes/ProbeLJ196A.agda` | `agents/reports/LJ-1-96/ProbeLJ196A.agda` | agents/reports/lj-1.113-report.md:189 | line citation |
| `archive/probes/ProbeLJ197A.agda` | `agents/reports/LJ-1-97/ProbeLJ197A.agda` | agents/reports/lj-1.98-report.md:107 | line citation |
| `archive/probes/ProbeLJ198A.agda` | `agents/reports/LJ-1-98/ProbeLJ198A.agda` | agents/reports/lj-1.98-report.md:15 | line citation |
| `archive/probes/ProbeLJ198B.agda` | `agents/reports/LJ-1-98/ProbeLJ198B.agda` | agents/reports/lj-1.98-report.md:80 | line citation |
| `archive/probes/ProbeLJ199A.agda` | `agents/reports/LJ-1-99/ProbeLJ199A.agda` | dev/LESSONS.md:3543 | binding rule |
| `archive/probes/ProbeLJ199B.agda` | `agents/reports/LJ-1-99/ProbeLJ199B.agda` | agents/reports/lj-1.99-report.md:21 | line citation |
| `archive/probes/ProbeLevy.agda` | `agents/reports/Unpaired/ProbeLevy.agda` | agents/reports/archive/l3.32-t66-report.md:13 | line citation |
| `archive/probes/ProbeRudComp.agda` | `agents/reports/Unpaired/ProbeRudComp.agda` | dev/LESSONS.md:1012 | binding rule |
| `archive/probes/ProbeSatSets.agda` | `agents/reports/Unpaired/ProbeSatSets.agda` | agents/reports/lj-1.132-report.md:102 | named |
| `archive/probes/ProbeT126.agda` | `agents/reports/T126/ProbeT126.agda` | agents/reports/archive/l3.32-t127-report.md:85 | line citation |
| `archive/probes/ProbeT127.agda` | `agents/reports/T127/ProbeT127.agda` | agents/reports/archive/l3.32-t127-report.md:80 | line citation |
| `archive/probes/ProbeT128.agda` | `agents/reports/T128/ProbeT128.agda` | agents/reports/archive/l3.32-t239-report.md:37 | line citation |
| `archive/probes/ProbeT131.agda` | `agents/reports/T131/ProbeT131.agda` | agents/reports/archive/l3.32-t131-report.md:22 | line citation |
| `archive/probes/ProbeT132.agda` | `agents/reports/T132/ProbeT132.agda` | agents/reports/archive/l3.32-t133-report.md:225 | line citation |
| `archive/probes/ProbeT136.agda` | `agents/reports/T136/ProbeT136.agda` | agents/reports/archive/l3.32-t136-report.md:121 | named |
| `archive/probes/ProbeT138.agda` | `agents/reports/T138/ProbeT138.agda` | dev/memos/L3.32-below-lim-design.md:22 | binding rule |
| `archive/probes/ProbeT140.agda` | `agents/reports/T140/ProbeT140.agda` | agents/reports/archive/l3.32-t145-report.md:155 | line citation |
| `archive/probes/ProbeT142.agda` | `agents/reports/T142/ProbeT142.agda` | agents/reports/archive/l3.32-t142-report.md:122 | line citation |
| `archive/probes/ProbeT143.agda` | `agents/reports/T143/ProbeT143.agda` | agents/reports/archive/l3.32-t143-report.md:111 | line citation |
| `archive/probes/ProbeT145.agda` | `agents/reports/T145/ProbeT145.agda` | dev/ledger.toml:651 | binding rule |
| `archive/probes/ProbeT151.agda` | `agents/reports/T151/ProbeT151.agda` | agents/reports/archive/l3.32-t151-report.md:23 | line citation |
| `archive/probes/ProbeT154.agda` | `agents/reports/T154/ProbeT154.agda` | agents/reports/archive/l3.32-t154-report.md:11 | line citation |
| `archive/probes/ProbeT159.agda` | `agents/reports/T159/ProbeT159.agda` | agents/reports/archive/l3.32-t174-strategy.md:27 | line citation |
| `archive/probes/ProbeT161.agda` | `agents/reports/T161/ProbeT161.agda` | agents/reports/archive/l3.32-t161-report.md:53 | line citation |
| `archive/probes/ProbeT175.agda` | `agents/reports/T175/ProbeT175.agda` | agents/reports/archive/l3.32-t177-report.md:25 | line citation |
| `archive/probes/ProbeT177.agda` | `agents/reports/T177/ProbeT177.agda` | agents/reports/archive/l3.32-t212-report.md:47 | line citation |
| `archive/probes/ProbeT179.agda` | `agents/reports/T179/ProbeT179.agda` | agents/reports/archive/l3.32-t244-report.md:79 | line citation |
| `archive/probes/ProbeT182.agda` | `agents/reports/T182/ProbeT182.agda` | agents/reports/archive/l3.32-t194-report.md:67 | line citation |
| `archive/probes/ProbeT185.agda` | `agents/reports/T185/ProbeT185.agda` | agents/reports/archive/l3.32-t227-report.md:134 | line citation |
| `archive/probes/ProbeT193.agda` | `agents/reports/T193/ProbeT193.agda` | agents/reports/archive/l3.32-t193-report.md:13 | line citation |
| `archive/probes/ProbeT194.agda` | `agents/reports/T194/ProbeT194.agda` | agents/reports/archive/l3.32-t199-report.md:28 | line citation |
| `archive/probes/ProbeT198.agda` | `agents/reports/T198/ProbeT198.agda` | agents/reports/archive/l3.32-t198-report.md:26 | named |
| `archive/probes/ProbeT204.agda` | `agents/reports/T204/ProbeT204.agda` | agents/reports/archive/l3.32-t217-report.md:40 | line citation |
| `archive/probes/ProbeT211.agda` | `agents/reports/T211/ProbeT211.agda` | agents/reports/archive/l3.32-t214-report.md:142 | named |
| `archive/probes/ProbeT214.agda` | `agents/reports/T214/ProbeT214.agda` | agents/reports/archive/l3.32-t214-report.md:15 | named |
| `archive/probes/ProbeT222.agda` | `agents/reports/T222/ProbeT222.agda` | agents/reports/archive/l3.32-t242-report.md:19 | line citation |
| `archive/probes/ProbeT237.agda` | `agents/reports/T237/ProbeT237.agda` | dev/ledger.toml:1723 | binding rule |
| `archive/probes/ProbeT240.agda` | `agents/reports/T240/ProbeT240.agda` | agents/reports/archive/l3.32-t245-report.md:93 | line citation |
| `archive/probes/ProbeT242.agda` | `agents/reports/T242/ProbeT242.agda` | agents/reports/archive/l3.32-t242-report.md:71 | named |
| `archive/probes/ProbeT242b.agda` | `agents/reports/T242/ProbeT242b.agda` | agents/reports/archive/l3.32-t242-report.md:87 | named |
| `archive/probes/ProbeT249.agda` | `agents/reports/T249/ProbeT249.agda` | agents/reports/archive/l3.32-t249-report.md:57 | line citation |
| `archive/probes/ProbeT251.agda` | `agents/reports/T251/ProbeT251.agda` | agents/reports/archive/l3.32-t251-report.md:65 | line citation |
| `archive/probes/ProbeT258Base.agda` | `agents/reports/T258/ProbeT258Base.agda` | agents/reports/archive/l3.32-t258-report.md:21 | named |
| `archive/probes/ProbeT258Ctr2.agda` | `agents/reports/T258/ProbeT258Ctr2.agda` | agents/reports/archive/l3.32-t258-report.md:27 | named |
| `archive/probes/ProbeT258Cure2.agda` | `agents/reports/T258/ProbeT258Cure2.agda` | agents/reports/archive/l3.32-t258-report.md:26 | named |
| `archive/probes/ProbeT258GutPsi.agda` | `agents/reports/T258/ProbeT258GutPsi.agda` | agents/reports/archive/l3.32-t258-report.md:25 | named |
| `archive/probes/ProbeT258GutSeg.agda` | `agents/reports/T258/ProbeT258GutSeg.agda` | agents/reports/archive/l3.32-t258-report.md:24 | named |
| `archive/probes/ProbeT258NoConv.agda` | `agents/reports/T258/ProbeT258NoConv.agda` | agents/reports/archive/l3.32-t258-report.md:23 | named |
| `archive/probes/ProbeT258NoUC.agda` | `agents/reports/T258/ProbeT258NoUC.agda` | agents/reports/archive/l3.32-t258-report.md:22 | named |
| `archive/probes/ProbeT261.agda` | `agents/reports/T261/ProbeT261.agda` | agents/reports/archive/l3.32-t261-report.md:29 | line citation |
| `archive/probes/ProbeT68.agda` | `agents/reports/T68/ProbeT68.agda` | agents/reports/archive/l3.32-t68-report.md:41 | line citation |
| `archive/probes/ProbeTowerInd.agda` | `agents/reports/Unpaired/ProbeTowerInd.agda` | dev/ledger.toml:299 | binding rule |
| `archive/probes/ProbeTowerInd2.agda` | `agents/reports/Unpaired/ProbeTowerInd2.agda` | dev/ledger.toml:299 | binding rule |
| `archive/probes/ProbeW3Seq.agda` | `agents/reports/Unpaired/ProbeW3Seq.agda` | agents/reports/archive/l3.32-t50-report.md:46 | line citation |
| `archive/probes/StepProbe.agda` | `agents/reports/Unpaired/StepProbe.agda` | agents/reports/archive/cut-probe-report.md:236 | line citation |

## What a mover after me must know

**A citation can name a family without writing any member out.**
`archive/probes/ProbeDD25F41{A,B,C,D}.agda` at `dev/LESSONS.md`, and
`src/ProbeLJ174A..F.agda` at `agents/reports/archive/lj-1.74-report.md:209`. A
plain stem search sees neither. `[LJ-1.133]` was bitten once in each direction
and `[LJ-1.132]` was bitten by the same shape.

**`[LJ-1.141]` was not bitten, and the reason is structural rather than lucky.**
Every member of every family moved to the SAME directory, so a prefix rewrite
carried the brace and the range forms untouched. **A move that splits a family
across two directories brings the bug straight back.**

## Why the report alone was never enough

`[LJ-1.133]` read report and probe pairs to settle this, and the finding is why
a probe is kept at all. **A report is the evidence for a VERDICT; a probe
carries a TERM.** A verdict is a sentence and copies into prose without loss:
「GREEN, 2.88 s」, 「26 lines」, 「WALL at 65 s」. A term does not.
`agents/reports/lj-1.118-report.md:68-81` gives the location and the line count
of a 49-line proof at `ProbeLJ1118A.agda:72-130`, and the report does not carry
the proof. Reports quote types. They do not quote proofs.
