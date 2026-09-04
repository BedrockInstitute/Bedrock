# Review of `bound2-in-limit`, task LJ-1.715-SPLIT

verdict: **GO on the term. PARK on the accept arm**, per the brief's branch
`heap-wall-park` (`agents/tasks/LJ-1-715-SPLIT/LJ-1.715-SPLIT.md`, branch table,
priority 30). This file states the split verdict the critic reads. It is not a
NO-GO on the statement's truth and not a NO-GO on the worktree proof.

## The term

The obligation
`agents/tasks/LJ-1-715-SPLIT/Probe715Split.agda::bound2-in-limit` typechecks:
`runs/probe715split.out`, EXIT=0, 1.04 s, one Agda process, heavy caliber
`-A64m -I0 -M4g` set on the pane by the program. The landed master checks in
place: `runs/ordinal-final.out`, EXIT=0, 0.82 s. The transcription is verbatim:
`diff` against `.pod-state/worktrees/LJ-1-715/src/L/Ordinal.lagda.md` reports
the two files identical. `bound2` is untouched.

## The accept arm

The brief's W3 question was: does Everything at heavy `-M4g` and one Agda
process accept those 33 lines? Measured answer: NO.

| run | tree state | warmth | verdict | evidence |
|---|---|---|---|---|
| floor A | with the 33 lines | cold outside the L.Ordinal subtree | `L.Condensation` heap exhausted, EXIT=251, 217.07 s | runs/everything-floor.out |
| floor B, control | lines reverted | same run sequence, one step warmer | Everything closes, EXIT=0, 111.91 s | runs/everything-floor-nolines.out |
| floor C | lines restored | warm outside the L.Ordinal subtree, identical to B | `L.Condensation` heap exhausted, EXIT=251, 196.66 s | runs/everything-floor-warm.out |

B and C are the controlled pair: identical warmth, identical build order, and
the only source difference is the 33 lines. B closes; C dies at the same site
as A. The wall is the marginal cost of the two new exported names on
`L.Ordinal`'s forty-dependent frame at the 4 GB cap, measured twice, not a
cold-build accident.

## What was tried before reporting the wall

1. The 2026-08-23 import-trim cure, re-measured at its own site: my fence
   pulls in NOTHING the file did not already import. `sett`, `⋃_` and `sucV`
   stand in the import block at `src/L/Ordinal.lagda.md:52-56`, and `suc-ord`
   at `src/L/Ordinal.lagda.md:96` already uses `sucV`. There is nothing to
   trim; the fence is import-clean.
2. Build-state shaping: cold-ish and warm-ish runs both wall at the same
   module (A and C above). Rerunning the same code at the same state hoping
   for a different result was not done.
3. No restructuring of the fence was attempted, for a specific reason: the
   brief mandates verbatim transcription (`Transcribe. Do not re-invent.`),
   forbids touching `bound2`, and pre-declares this exact wall as the split's
   expected finding (premise 3 and the `heap-wall-park` branch). An `abstract`
   seal or a restated `IsLimit` would be a third landing, which the brief
   forbids.

## What the next brief needs

- The wall site is `L.Condensation`, a dependent of `L.Ordinal`, and the cap
  is the heavy `-M4g`. Without the lines the whole tree closes at the cap in
  111.91 s, so the frame is under the cap and the landing tips it over.
- The cure is not in this task's write scope: `Everything` may not be edited
  here, and `L.Condensation` is not in scope either. The cure is a frame
  decision (split a consumer, raise the tier, or seal the two exports), and it
  belongs to the mathematician and the owner, not to a wider transcription.
- The obligation itself costs 27 non-blank in-fence lines (ledger's way) and
  0.82 s warm where it sits. No number above was taken under any other
  caliber; one Agda process per run throughout.
