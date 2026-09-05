# LJ-1.248 report: Route A-prime's total, now that every block is measured

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Recon only. No
Agda ran. No master, brief or report was edited. No commit, no push.

Every negative is marked MEASURED (read at the cited line) or INFERRED (my
judgement). ASD-STE100 applies.

## 0. LEAD: ONE NUMBER, ONE WORD

**1,150. ARITHMETIC.**

The seven measured figures sum to 1,150:

`54 + 186 + 26 + 43 + 348 + 446 + 47 = 1,150`.

It is not a price. Six reports refused a total because some block rested on
reading. That reason is almost gone. Three causes stay, and each is named:

1. **A4's 43 is a minimal core, not the master.** The master owes the full
   object-language internal `IsCardinal` formula with its adequacy. That gap
   is INFERRED at about 30 lines. Section 2.
2. **A7's 47 counts about 14 lines that A2 and A4 already count.** The
   corrected A7 is about 33, and the corrected sum is about 1,136. Section 3.
3. **A6's 150 base still carries 47 lines of reading.** The 296 charge is
   measured, and 103 of the base is measured by `[LJ-1.107]`, but the 47-line
   theorem wrapper is reading (`agents/tasks/LJ-1-217/lj-1.217-report.md:160`).
   Section 3.

So the refusal has THREE named causes, not the one the brief guessed. The A4
gap is the missing piece. The A7 over-count is a double-count. The A6 base
wrapper is the last reading residue in the route, and it is small: 47 of
1,150, which is 4 percent.

**The corrected arithmetic.** 1,150 minus 14 (A7's borrowed lines) is 1,136.
Add the A4 gap of about 30 and the full route is about 1,166. Both are
INFERRED arithmetic, not a price. The 47-line A6 wrapper is the only reading
residue left.

## 1. THE FIVE OVERLAPS, RE-CHECKED AGAINST TODAY'S FIGURES

The five overlaps are `agents/tasks/LJ-1-175/lj-1.175-report.md:142-148`.
`[LJ-1.227]` resolved four and `[LJ-1.229]` closed the fifth. I re-check all
five against the figures that moved: A5 went 547 to 348, A4 went 190 to 43.

| # | overlap | today | verdict |
|---|---|---|---|
| 1 | A6's price names A5 | A6 = 446 = 150 + 296, one number, inherits nothing (`agents/tasks/LJ-1-217/lj-1.217-report.md:14`) | RESOLVED, still |
| 2 | A5's list contains A6's object | A5's list is composition, CSB, inclusion j, column square, pairω; `ShiftAbs`/`Shiftω` sit in A6 (`agents/tasks/LJ-1-247/lj-1.247-report.md:21`) | RESOLVED, still |
| 3 | A4's extra content is A2's content | A4 = 43 excludes A2's copied `injAt` (5 lines), and the 27-line description-plus-adequacy is no longer inside A4's figure (`agents/tasks/LJ-1-236/lj-1.236-report.md:142-153`) | RESOLVED, closed by construction |
| 4 | A4 and A6 are steps of the probe whose whole is A5's basis | A5's basis is five objects built into L, not the 582-line ambient probe (`agents/tasks/LJ-1-247/lj-1.247-report.md:21-33`) | RESOLVED, still |
| 5 | a 300-line item sits across A4 and A5 | the item names no object, so no block owns it; its basis was measured false (`agents/tasks/LJ-1-176/lj-1.176-report.md` section 6) | RESOLVED, DISSOLVED |

**MEASURED. No overlap re-opens.** None of the five was resolved only against
a dead figure. Overlap 3 is the one that moved, and it moved in the safe
direction: A4's figure now excludes A2's predicate, so the double-count is
gone from the numbers rather than subtracted after the fact.

**One new defect appears, and it is not one of the five.** A7's 47 counts
A2's `injAt` and A4's `InjCode` plus `IsCardinalL`. Section 3 prices it. It
is a caliber defect, not a partition overlap.

## 2. THE A4 GAP, PRICED

**What it is.** `[LJ-1.236]` states it: "the probe is a minimal core, not the
master: the master adds the full object-language internal `IsCardinal`
formula with its adequacy, and the concrete nonempty witness (A2's `lid`,
which is A5's deliverable, not A4's)" (`agents/tasks/LJ-1-236/lj-1.236-report.md:153-155`).

Two pieces are named there. Only one is A4's.

- **The nonempty witness is NOT A4's gap.** `[LJ-1.236]` says so in the same
  sentence: it is A2's `lid`, which is A5's deliverable. It sits inside A5's
  348, not in A4. MEASURED by reading the sentence.
- **The internal `IsCardinal` formula with its adequacy IS A4's gap.** The
  probe writes `IsCardinalL` as a metatheoretic Type predicate
  (`agents/tasks/LJ-1-236/ProbeLJ1236A4.agda` S3). The master must write it
  as an object-language `Formula` with a satisfaction certificate.

**The price, one number with its basis (DD8).** INFERRED **30 lines**.

Basis: the closest measured comparable is A2's `injAt` description plus
adequacy at 27 lines (`agents/tasks/LJ-1-229/lj-1.229-report.md:20`). That
pair is a three-quantifier formula with a two-direction adequacy. The
internal `IsCardinal` formula adds one bounded universal over membership and
one negation over a delivered coding conjunction. Every coding atom's
adequacy (`svAt-adequate`, `domAt-adequate`, `injAt-adequate`,
`appAt-adequate`) is delivered. So the new work is the quantifier structure
and the two adequacy directions, the same order as A2's 27.

**The probe that closes it.** Build `isCardinalFo : Formula S n` ("no smaller
ordinal admits an L-element coding an injection from κ") and its two
directions `isCardinalFo-out` and `isCardinalFo-in`, mirroring A2's
`injAt`/`injAt-out`/`injAt-in` (`agents/tasks/LJ-1-229/ProbeLJ1229A.agda`
S1). One file, over A2's delivered predicate. This is the only missing piece
between the seven figures and a total.

## 3. WHAT THE FIGURES COUNT, AND ONE CALIBER DEFECT

**The clean half. MEASURED.** Three of the brief's four caliber checks pass.

- **A4 excludes the 5 copied `injAt` lines.** `[LJ-1.236]` counts 48 charge
  and subtracts the 5 copied `injAt`, giving 43
  (`agents/tasks/LJ-1-236/lj-1.236-report.md:142-153`). MEASURED clean.
- **A2 counts `injAt` at 27 and the readback at 51.** 27 is the description
  plus adequacy (`injAt` plus `injAt-out` plus `injAt-in`); 51 is `Extract`
  (29) plus `Small` (22). 27 + 29 + 45 (range) + 31 (`ranAt`) + 20
  (discharge) + 22 (Small) + 12 (assembly) = 186
  (`agents/tasks/LJ-1-229/lj-1.229-report.md:20-22`; the parts sum in the
  probe file). MEASURED clean.
- **A5 counts the shared `StageBound` at 16, and A6 does not.** A5 = 16 + 160
  + 0 + 112 + 0 + 60 = 348 (`agents/tasks/LJ-1-247/lj-1.247-report.md:33`).
  A6's 296 charge is Part 2 + Part 4 + Part 5 + two helpers, and its Part 3
  `StageBound` (16) is "SHARED, no object owns it" and not in the charge
  (`agents/tasks/LJ-1-217/lj-1.217-report.md` section 3). So `StageBound` is
  counted once, in A5. MEASURED clean.

**The defect. A7's 47 counts lines that A2 and A4 own.**

`[LJ-1.236]`'s own A7 table marks the borrowing
(`agents/tasks/LJ-1-236/lj-1.236-report.md:94-95`):

- `injAt` (copied from A2's S1), 5 lines, "not A7's; A2's deliverable".
- `_↪_`, `InjCode`, `IsCardinalL`, 12 lines, "the internal cardinal (A4's
  object, named)".

So the 47 charge includes 5 lines of A2's `injAt` and about 9 lines of A4's
`InjCode` plus `IsCardinalL`. In a master, A7 imports those from A2 and A4;
it does not re-write them. A4's own probe did the same borrow and excluded it
(A4 = 43 = 48 minus 5). A7's probe did the borrow and kept it.

**Corrected figures.** A7's own content is about **33 lines** (47 minus 14:
the 5 `injAt` and the 9 `InjCode` plus `IsCardinalL`). The corrected sum is
**1,136** (1,150 minus 14). MEASURED that the lines are borrowed (the table
says so); INFERRED that 14 is the exact count, because the report's 12 lumps
`_↪_` (3 generic lines) with the two A4 objects.

**A second, smaller caliber note.** A4's 43 includes its `Atω` guard (11
lines) and A7's 47 includes its guard (5 lines). Both are C-38 probe-only
instantiations. A5's inclusion (112) and A6's charge (296) exclude their
probe-only guards. So A4 and A7 are about 16 lines heavier than the A5/A6
caliber. It does not change any verdict, and I name it rather than net it.

**A third note, and it is the last reading residue.** A6 = 446 is 296
measured charge plus a 150 base. Of that base, 103 lines are measured by
`[LJ-1.107]` and 47 lines are the theorem wrapper, which is reading
(`agents/tasks/LJ-1-217/lj-1.217-report.md:160`). No task after `[LJ-1.217]`
re-measured that wrapper. So A6 is 89 percent measured (399 of 446), not
fully. MEASURED that the residue exists, at the cited line.

## 4. THE TOWER SPLIT FOR THE WHOLE ROUTE (DD4)

The brief asks for the per-tower half of A-prime, the part the J tower pays
again. `[LJ-1.227]` section 8 covered A1, A2, A3, A4, A7 and not A5 or A6.
The later tasks added A6's split and part of A5's.

| block | figure | tower class | per-tower lines | evidence |
|---|---:|---|---:|---|
| A1 | 54 | PER-TOWER, level-hood certificate | 54 | `[LJ-1.227]` section 8 |
| A2 | 186 | TOWER-NEUTRAL, the coding layer | 0 | `[LJ-1.227]` section 8; `[LJ-1.229]` section 5 |
| A3 | 26 | PER-TOWER, definable well-order | 26 | `[LJ-1.227]` section 8 |
| A4 | 43 | PER-TOWER, well-order applied to cardinality | 22 (`InternalLeastCard`) | `[LJ-1.227]` section 8; `[LJ-1.236]` section 6 |
| A5 | 348 | **OPEN** (see below) | unsettled | `[LJ-1.247]` section 6 |
| A6 | 446 | 85 percent neutral, 15 percent per-tower (charge); base neutral | 44 (Part 5) | `[LJ-1.217]` section 6 |
| A7 | 47 | TOWER-NEUTRAL, the statement | 0 | `[LJ-1.227]` section 8; `[LJ-1.236]` section 6 |

**The measured per-tower half is 146 lines: A1 54 + A3 26 + A4 22 + A6 44.**
A2 and A7 add none, and A6's base (150) and generic charge (252) are neutral.

**A5 is OPEN as a block, and I say so rather than settle it.**
`[LJ-1.247]` section 6 states A5's tower status stays OPEN. Its parts carry
partial verdicts:

- `pairω` (60) is tower-neutral, MEASURED by grep
  (`agents/tasks/LJ-1-234/lj-1.234-report.md` section 4).
- the column square is dissolved to 0 and its statement names no tower atom
  (`agents/tasks/LJ-1-247/lj-1.247-report.md` section 6).
- composition (160) is tower-neutral in shape: written fixed it would be 198
  lines the J tower writes again, and the only L names are two imports
  (`agents/tasks/LJ-1-152/lj-1.152-report.md:305-318`).
- the inclusion j is 81 percent generic: 91 of 112 lines name no L axiom and
  no L stage (`agents/tasks/LJ-1-176/lj-1.176-report.md` section 7.1). Its
  L half is StageBound (16) plus `InclGraph` (18), about 21 to 34 lines.
- `StageBound` (16) is the shared bound device, "generic in index and
  family", counted once in A5 and not in A6.

So the whole-route per-tower half is not yet one number. A5's per-tower share
is between about 21 and 50 lines, and only the orchestrator's tower ruling
closes it. The part that is measured is 146 lines, and the J tower pays those
again before A5 is settled.

**The literature's two objects map onto this split.** MEASURED by reading
`dev/literature/devlin-II5.md:387-389`: the per-tower content is exactly two
objects, the level-hood certificate and the definable well-order. Object 1 is
A1. Object 2 is A3 plus A4's `InternalLeastCard` plus the L instantiation of
A5 and A6. The mapping holds, and nothing in it moved.

## 5. ARCHIVE USED (DD18)

One line read per archived file.

- **`agents/tasks/LJ-1-227/lj-1.227-report.md`, read WHOLE.** TAKEN: the five
  overlaps at section 7 and the tower table at section 8.
- **`agents/tasks/LJ-1-175/lj-1.175-report.md`, read WHOLE.** TAKEN: the five
  overlaps at `:142-148` and the partition finding at section 3.
- **`agents/tasks/LJ-1-247/lj-1.247-report.md`, read WHOLE.** TAKEN: A5 = 348
  at `:21` and `:33`; A5's tower status OPEN at section 6.
- **`agents/tasks/LJ-1-236/lj-1.236-report.md`, read WHOLE.** TAKEN: A4 = 43
  and the gap at `:142-155`; A7 = 47 and the borrowed lines at `:94-95`.
- **`agents/tasks/LJ-1-232/lj-1.232-report.md`, read WHOLE.** TAKEN: A1 = 54
  and A3 = 26 at the lead.
- **`agents/tasks/LJ-1-229/lj-1.229-report.md`, read WHOLE.** TAKEN: A2 = 186
  at `:14`; description plus adequacy 27 and readback 51 at `:20-22`.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`, read WHOLE.** TAKEN: A6 = 446
  at `:14`; 85 percent generic at section 6.
- **`agents/tasks/LJ-1-176/lj-1.176-report.md`, read WHOLE.** TAKEN: the
  300-line dissolution at section 6; j at 81 percent generic at section 7.1.
- **`agents/tasks/LJ-1-234/lj-1.234-report.md`, read WHOLE.** TAKEN: `pairω`
  at 60 lines, tower-neutral, at section 4.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`, section 7.** TAKEN:
  composition tower-neutral in shape at `:305-318`.
- **`archive/dev/TASKS-archived.md:262`.** TAKEN: the retired route's GCH wing
  priced at 25,485 to 28,258 naive, 29,909 to 37,275 calibrated.
- **`agents/tasks/archive/L3-32-T257/l3.32-t257-routes.md`, read the head.**
  TAKEN: the caliber, non-blank lines inside ` ```agda ` fences over
  `*.lagda.md` under `src/`.

**What the retired total counted, and why it does NOT transfer.** It counted
the WHOLE double trophy, `L ⊨ AC ∧ L ⊨ GCH`, on the internalization route, in
the ledger's in-fence caliber. It does not transfer for three reasons. First,
it is the whole trophy, not the seven-block A-prime route. Second, the
seven-block split postdates the archive
(`agents/tasks/LJ-1-175/lj-1.175-report.md:74-77`). Third, P-l forbids
carrying a figure across the tree change. The archive's number prices a
different object on a different tree.

## 6. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:387-389`.** USED. The per-tower content is
  exactly two objects, the level-hood certificate and the definable
  well-order. Section 4 maps them onto the split.

**Does the literature bound any of the seven blocks?** No. No source in
`dev/literature/` states a line or seconds figure for any block, so nothing
bounds A1 to A7. MEASURED as the absence of any such figure in the sources I
opened, and carried from `[LJ-1.175]` section 10.

**Do the two per-tower objects map onto my split?** Yes. Object 1 is A1.
Object 2 is A3 plus A4's `InternalLeastCard` plus the L halves of A5 and A6.
The mapping is the one `[LJ-1.227]` gave and it survives the new figures.

## 7. THE NEGATIVES, CLASSIFIED

- **MEASURED. The seven figures sum to 1,150.** Arithmetic.
- **MEASURED. No overlap re-opens.** Section 1.
- **MEASURED. A4's 43 excludes A2's copied `injAt`.** 48 minus 5.
- **MEASURED. A2 counts `injAt` at 27 and the readback at 51.** The 78-line
  core plus 108 more lines sums to 186.
- **MEASURED. `StageBound` is counted once, in A5, not in A6.**
- **MEASURED. A7's 47 counts borrowed lines.** `[LJ-1.236]`'s own table marks
  `injAt` "not A7's" and `InjCode`/`IsCardinalL` "A4's object".
- **MEASURED. A6's 150 base carries 47 lines of reading.** The theorem
  wrapper, at `agents/tasks/LJ-1-217/lj-1.217-report.md:160`. A6 is 89
  percent measured, not fully.
- **MEASURED. The nonempty witness is not A4's gap.** It is A2's `lid`, A5's
  deliverable.
- **INFERRED. The A4 gap is about 30 lines.** Basis is A2's 27-line
  description-plus-adequacy. It needs the named probe.
- **INFERRED. A7's own content is about 33 lines, and the corrected sum is
  about 1,136.** The 14 is my split of the report's 12-plus-5.
- **MEASURED. The per-tower half across A1, A3, A4, A6 is 146 lines.**
- **MEASURED. A5's tower status is OPEN.** `[LJ-1.247]` section 6 states it,
  and its parts carry partial verdicts only.
- **INFERRED. The full route is about 1,166 lines once the two numeric
  corrections land.** 1,136 (A7 minus 14) plus 30 (the A4 gap). The A6
  wrapper's 47 lines do not change the sum; they stay unmeasured. It is
  arithmetic, not a price.

## 8. WORKING TREE, AS MY REPORT DESCRIBES IT

One file written: `agents/tasks/LJ-1-248/lj-1.248-report.md`, this file. No
master edited. No brief or report edited. No probe written. No Agda process
ran. No commit, no push, no `git checkout .`, stash, reset or clean.

`scripts/lint-prose.py --check` runs on this report and exits 0.
