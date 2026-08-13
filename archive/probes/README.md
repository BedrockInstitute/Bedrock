# Archived probes

A **probe** is a throwaway miniature that prices a load-bearing assumption
before heavy work. `dev/LESSONS.md` **D-1** says a probe is throwaway by
doctrine and that its VERDICT, in the report, is what must outlive it.

This directory holds the few probes that are an exception, and the exception
has one test: **an archived report cites the probe file at a LINE NUMBER.**
Such a citation resolves only against the file. Delete the file and the
report's evidence stops being checkable, which is the one thing this project
does not allow.

## This directory departs from `archive/README.md`, and the owner must rule

[archive/README.md](../README.md) says "Nothing else belongs here: no live
code, **no probes**, no generated files". That line was written 2026-08-04.
The archive has since grown `archive/tooling/` (2026-08-09) and
`archive/kits/` (2026-08-10), and neither is a retired module at its original
path either. `[LJ-1.132]` created this directory under its brief's
instruction to archive what a historical document cites.

**The alternative was deletion, which would break five line-number citations.**
If the owner prefers the `archive/README.md` line as written, the cure is to
delete this directory and accept the broken citations, or to widen that line.
The choice is the owner's; `agents/reports/lj-1.132-report.md` states it.

## What is here

| File | Task | Cited at line level by |
|---|---|---|
| `CutProbe.agda` | the cut probe | `agents/reports/archive/cut-probe-report.md:56,60,64` |
| `StepProbe.agda` | the cut probe, Unknown 3 | `agents/reports/archive/cut-probe-report.md:236,248,251` |
| `OrderProbe.agda` | the order probe | `agents/reports/archive/order-probe-report.md:133,136,138` |
| `ProbeRudComp.agda` | `[L3.30-P1]` | `agents/reports/archive/p1-report.md:41,80-83`; provenance for `dev/LESSONS.md` **I-2** |
| `ProbeSatSets.agda` | `[L3.31-R5-G2p]` | `agents/reports/archive/g2p-report.md:14`; `l3.31-r5probe-report.md:176` |

`ProbeRudComp.agda` is the strongest case. `dev/LESSONS.md:1012` names it as
the provenance of a LIVE rule and says it is "preserved in the session
scratchpad". This directory is what that sentence now means.

## The paths in the citing documents are stale, and stay stale

Every report above is frozen and cites the old `_build/probe*/` path. **Find
the file by its basename**, which is unique here. The reports also refer to
some of these as `src/Probe*.agda`, which is where they ran; they were never
committed there, and `scripts/check-probes.py` still forbids that.

## The same archive rules apply

- **Frozen.** Never edited in place. A revival copies the probe OUT.
- **Not required to be green.** Each was written against a tree that has moved,
  and each may use constructs the live tree forbids.
- **Outside every gate**, structurally, because `archive/` is outside `src/`.
- **Do not revive one without re-pricing it.** `dev/LESSONS.md` **P-l**: a
  price measured elsewhere is a hypothesis, not a price.
