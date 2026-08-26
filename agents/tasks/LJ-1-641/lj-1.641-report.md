# LJ-1.641 report: the commute at ordinal collapse

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
verdict: NO-GO on `commute-at-ordinal`. The obligation reduces, as a green
term, to three named gaps and to nothing else. All three have one producer,
`lset-code`, and it is unbuilt. PREMISE 4 OF THE BRIEF IS NOT SUPPORTED, and
that is measured and not asserted.

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-641/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated, the probe carries `--safe`, the delivered
probe is green and carries no hole, and nothing lands in `src/`. The probe is
a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence
lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run
of this frame is 745,275,392 bytes against the 2,147,483,648-byte cap
(`runs/floor-2.out`). One run peaked at 2,224,013,312 bytes
(`runs/floor-1.out`): that run compiled `L.BoundedSubset` COLD and prices the
dependency, not this frame. It did not wall and it did not fail; it exited 42
at the one designed hole.

The standing direction (`dev/pod/direction.md`, "Current direction") orders
one SRC collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work.
It does not start that collection and it does not start phase 3. No Boundary
clause is in conflict.

## VERDICT

**THE OBLIGATION IS NOT INHABITED.** No name `commute-at-ordinal` is declared
in `agents/tasks/LJ-1-641/Probe641.agda`. The meter says so:
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`
(`runs/witness.out:1-2`). The stop is stated at
`agents/tasks/LJ-1-641/review-of-commute-at-ordinal.md`.

**THE PROBE IS GREEN.** Three forced rechecks, interface deleted before each,
`EXIT=0` every time: 3.74 s, 3.54 s, 3.76 s (`runs/recheck-1.out` to
`runs/recheck-3.out`). Median wall **3.74 s**. Peak RSS **738,508,800 bytes**,
identical on all three. The four central delivered names were metered by name
and return `0 UNRESOLVED of 4`, 3.45 s (`runs/witness-names.out`).

**WHAT WAS BUILT INSTEAD OF THE OBLIGATION.** The obligation follows from
three gaps and from nothing else, and that implication is a term:

    commute-from-gaps : IndexInHull → DefFwd → DefBwd → Commute   (:278)
    Residue           = IndexInHull × DefFwd × DefBwd             (:421)
    residue-suffices  : Residue → Commute                         (:424)

Everything around the three gaps is discharged. No fourth thing is owed.

## D-10, BEFORE ANY AGDA: IS THE TARGET TRUE?

**I did not find the target false, and I did not build a term of the
negation.** The statement is very probably TRUE. The hull is a definable hull
built from LEAST witnesses (`src/L/Hull.lagda.md:403`, `leastWit`), and that
is what makes it elementary; condensation is true of an elementary hull. The
stop is about the PROOF, not about the truth.

I checked one candidate refutation and it does not survive the hull. Take δ
with no member in the hull. Then `HS.C.π δ` is a `sett` over an empty index,
so it is `∅`, and `IsOrd ∅` holds, so the hypothesis is met; `Lset ∅` is `⋃`
of an empty family, so the right side is `∅`; but `∅` is a definable subset of
every level, so the left side is not `∅` whenever δ is not `∅`. That would
refute the obligation. **It is not realizable in this hull.** The hull is
closed under least witnesses, so if δ is in the hull and δ is not empty, the
least member of δ is in the hull too. The same closure kills the `δ = {{∅}}`
reading: `{∅}` is the union of `{{∅}}` and the union is definable, so `{∅}`
is dragged into the hull and `HS.C.π δ` stops being an ordinal.

**THIS IS THE POINT THE BRIEF'S PREMISE 4 MISSES.** What blocks `[LJ-1.477]`'s
candidate obstruction is the hull's closure, not the ordinality hypothesis.

## PREMISE 4, MEASURED

The brief's premise 4 says `IsOrd (HS.C.π δ)` "excludes exactly" the case
`[LJ-1.477]` named, and the brief's reasoning section calls that "the whole
reason this is worth a dispatch and not a repeat".

**THE REDUCTION NEVER READS THAT HYPOTHESIS.** `fwd-from-gaps`
(`Probe641.agda:224`) and `bwd-from-gap` (`:253`) bind `oπδ` and pass it on
unexamined. No row of either term eliminates it. I did not leave that as a
claim. `commute-no-ord-from-gaps` (`:320`) restates the same three gaps with
the ordinality dropped from every one of them, and derives the MORE GENERAL
commute, the one `[LJ-1.477]` attacked (`PiCommuteLset`,
`agents/tasks/LJ-1-477/Probe477.agda:100-102`). **It typechecks.**

So the hypothesis buys nothing between the obligation and the three gaps. If
it excludes anything, it must do so inside `IndexInHull`, the only gap whose
statement it can reach.

**THE CHAIN OF CUSTODY IS WORTH THE MATHEMATICIAN'S ATTENTION.** `[LJ-1.477]`
wrote that the candidate obstruction is "A non-ordinal `y ∈ M` whose members
lie outside `M`" (`agents/tasks/LJ-1-477/lj-1.477-report.md`, STEP TWO).
`[LJ-1.602]` restated that as "a NON-ORDINAL collapse"
(`agents/tasks/LJ-1-602/Probe602.agda:267`), and the brief's premise 4 cites
that restatement, not the original. The two are not the same statement:
`[LJ-1.477]`'s obstruction is about which MEMBERS lie outside the hull, and
`IsOrd (HS.C.π δ)` constrains only the IMAGE of the index. `[LJ-1.598]` had
already measured that `IsOrd (HS.C.π ...)` does not make its argument an
ordinal, with the `δ = {{∅}}` reading, and `[LJ-1.602]`'s own report repeats
that measurement in its D-10 section
(`agents/tasks/LJ-1-602/lj-1.602-report.md`, D-10 section).

## W3, THE WIDEST UNMEASURED TERM

The brief names W3: "Whether the two computation laws join once the collapse
is an ordinal." The slice `runs/W3.agda` states it alone and is green
(`runs/w3-2.out`, `EXIT=0`, 3.18 s, peak 694,075,392 bytes). It delivers the
reduction `join-gives-commute` (`Probe641.agda:110`): the obligation IS the
join once both laws are spent, so the join is not a detour.

**THE ANSWER IS NO, AND THE HYPOTHESES ARE NOT WHY.** The diagnostic
`runs/JOINREFL.agda` puts `refl` at the join with `IsOrd (HS.C.π δ)` AND
`⟨ Lset δ ∈ˢ HS.M ⟩` both in scope. It fails with `[UnequalTerms]`
(`runs/join-refl.out:4`), the same error class `[LJ-1.477]` measured WITHOUT
the hypotheses. That is not new evidence about the ordinal. **`refl` is
decided by conversion, and conversion does not read a hypothesis. Adding a
hypothesis to a type cannot change whether its two sides are definitionally
equal.** The brief's W3 estimate was 90 to 180 lines; the question is settled
in 2, and the estimate is not what the answer cost.

The diagnostic is not one of the kept green runs. The delivered probe does not
contain that `refl`.

## THE THREE GAPS, AND THEIR ONE PRODUCER

The computation-law route joins two CONSTRUCTORS and they do not meet. The
member route asks what each side CONTAINS. Set equality is mutual membership
(`extensionalV`, `src/V/Hierarchy.lagda.md:114-115`) and membership is an
hProp, so the split is lossless (`halves-give-commute`, `:196`). Expanding
each half once by the tree's own member readings leaves exactly three things.

    IndexInHull  (:202)  `Lset δ` unions over ALL members of δ; `HS.C.π δ`
                         sees only the members of δ inside the hull. A level
                         contributed by a member of δ outside the hull has no
                         counterpart on the right.
    DefFwd       (:210)  π carries a hull member of `𝒟ₒ (Lset β)` into
                         `𝒟ₒ (Lset (HS.C.π β))`.
    DefBwd       (:216)  every member of `𝒟ₒ (Lset (HS.C.π β))` is hit by one.

`DefFwd` and `DefBwd` together are "π commutes with `𝒟ₒ`", and `IndexInHull`
is "`Lset-out` witnesses lie in `M`". **Those are the two demands
`[LJ-1.477]` named in prose and did not state as types**
(`agents/tasks/LJ-1-477/lj-1.477-report.md`, "## 4. What the next brief
needs"). This task states them as types and discharges everything else.

**ALL THREE HAVE ONE PRODUCER AND IT IS UNBUILT.** The hull is closed under
DEFINABLE witnesses and only those: `hull-closed` (`src/L/Hull.lagda.md:415`)
takes a `Formula Code 1`. Each gap asks for a hull member picked out by a
condition that names `Lset` or `𝒟ₒ`. So each needs `Lset` named in the hull's
language, which is `lset-code` (`agents/tasks/LJ-1-462/Probe462.agda:109-111`),
step 3 of `[LJ-1.462]`'s four. `grep -rn "lset-code" src/` returns nothing.
`[LJ-1.474]` is GO on `lset-codes`, the vector of CONSTANT codes of the graph
formula, and its report says in terms "I did not inhabit `levelIn` or
`lset-code`" (`agents/tasks/LJ-1-474/lj-1.474-report.md:74-75`).

**SO THE COMMUTE IS NOT A FOURTH INDEPENDENT DEBT. It is step 3's consumer.**

## ONE LEMMA THE TREE OWED AND THIS TASK BUILT

`HS.C.π-member` (`src/V/Collapse.lagda.md:63-73`) returns the hull-membership
of the preimage and its π-value, but DROPS the fact that the preimage is a
member of the argument. This obligation needs that fact, because the preimage
must be fed to `Lset-out` at δ. `π-member'` (`Probe641.agda:132`) is that
lemma, built at the same `π-compute` unfolding and keeping the third conjunct.
It is metered green. **A successor task at this site will want it, and a
successor task in `src/` may want it in `src/V/Collapse.lagda.md`.** I did not
put it there: this task's scope forbids `src/`.

## 1. What was built

All in `agents/tasks/LJ-1-641/Probe641.agda`, module
`LJ-1-641.Probe641 {ℓ} (lem)`, inside `module Frame`. 425 total lines, 221
non-blank non-comment lines.

- `Commute` (`:68`), the obligation's type, copied letter for letter from
  `agents/tasks/LJ-1-602/Probe602.agda:178-182`.
- Section 1, W3: `law-π`, `law-L`, `JoinStepsAtOrd` (`:103`),
  `join-gives-commute` (`:110`).
- Section 2: `π-member'` (`:132`), `π-into`.
- Section 3: `Fwd`, `Bwd`, `halves-give-commute` (`:196`), the three gap types
  (`:202`, `:210`, `:216`), `fwd-from-gaps` (`:224`), `bwd-from-gap` (`:253`),
  `commute-from-gaps` (`:278`).
- Section 4: `CommuteNoOrd` (`:306`), `IndexInHullNoOrd` (`:311`),
  `commute-no-ord-from-gaps` (`:320`), `no-ord-gives-commute` (`:379`),
  `ord-gap-from-no-ord`.
- Section 5: `Residue` (`:421`), `residue-suffices` (`:424`).

**The imports are trimmed.** `[LJ-1.602]`'s frame carried `CollapseIso`,
`Formula` and `mapFo` because its clause was a SYNTAX statement. This
obligation is a SET-LEVEL equation and reads no formula anywhere, so none of
the three is imported, and `HullExt` is not either. The standing coder clause
orders that trim before a heavy object.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M2g`, set on the pane by the program and untouched here.
One Agda process at a time, from the repository root. The runner is
`runs/run.sh`; it sets no `GHCRTS`.

**THE FLOOR WAS PRICED BEFORE ANY PROOF** (D-10, and the standing coder
clause). `runs/FLOOR.agda` states the obligation at a BARE META in this file's
own trimmed frame.

| run | what | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `runs/floor-1.out` | floor, `L.BoundedSubset` COLD | 42 | 23.06 | 2224013312 |
| `runs/floor-2.out` | floor, warm | 42 | 2.81 | 745275392 |
| `runs/w3-2.out` | W3 slice, alone | 0 | 3.18 | 694075392 |
| `runs/join-refl.out` | `refl` at the join, diagnostic | 42 | 2.94 | 693911552 |
| `runs/recheck-1.out` | full, forced | 0 | 3.74 | 738508800 |
| `runs/recheck-2.out` | full, forced | 0 | 3.54 | 738508800 |
| `runs/recheck-3.out` | full, forced | 0 | 3.76 | 738508800 |
| `runs/recheck-final.out` | full, forced, delivered state | 0 | 3.88 | 738525184 |

Median full-file wall over the three kept rechecks **3.74 s**, median peak
RSS **738,508,800 bytes**. `runs/recheck-final.out` is a fourth forced recheck
of the file exactly as delivered, also `EXIT=0`. The
warm floor is **2.81 s** and **745,275,392 bytes**, which is 0.69 GiB against
the 2 GiB cap. **The frame is affordable and the whole task cost 0.93 s of
wall over its own floor.** `runs/w3-1.out` and `runs/p-1.out` to
`runs/p-5.out` are the incremental checks as the file was filled; they are not
forced rechecks and they are not priced.

`runs/floor-1.out` is the only run that approached the cap, and it did so
compiling `L.BoundedSubset`, not this frame. It exited 42 at the designed hole.
No run in this task walled.

- Witness meter, the obligation: `1 UNRESOLVED of 1`, 2.93 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name `commute-at-ordinal` is
  not in scope. That is the intended NO-GO reading.
- Witness meter, four delivered names: `0 UNRESOLVED of 4`, 3.45 s
  (`runs/witness-names.out`).
- This worktree has no `.venv`. The meter ran as
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`. I did
  not add a dependency and I did not create a local `.venv`.

## W2 (DD4)

The mathematics is written once at a generic carrier and instantiated nowhere.
The module is generic in `ℓ`. `lam`, `X` and the stage hypotheses stay
parameters of `module Frame`. No ordinal is fixed. No second copy at a
concrete stage. **The clause's conflict did not arise, and the deliverable is
a reduction, which is generic by construction.** The three gap types are
stated at the same generic carrier as the obligation.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No dead fragment was
deleted. `dev/ARCHIVE.md` gains no row from this task.

## C-42

C-42 orders a sweep when a REFUTATION lands, and it asks for the COUNT before
the cure. **No refutation landed here**, so the law does not fire on the
obligation. It does fire, weakly, on the premise finding, so I swept anyway
and report the count.

`grep -rn "IsOrd (.*π " src/` returns **0**. The shape "ordinality of a
collapse used as a hypothesis" does not occur in the live tree at all. It
occurs in **35 files** under `agents/tasks/`, all briefs, probes, reports and
reviews. **So no cure is owed in `src/`, and no `src/` row is at risk from
this finding.** The one live consumer, `levelIn`
(`src/L/BoundedSubset.lagda.md:917`), hypothesises `IsOrd δ` on the INDEX and
not on the collapse, so it does not carry the shape.

## 3. What the next brief needs

- **Do not re-dispatch this obligation on the strength of the ordinality
  hypothesis.** It is measured unused in the reduction
  (`commute-no-ord-from-gaps`, `Probe641.agda:320`). A brief that adds another
  hypothesis to the same type should first say which of the three gaps that
  hypothesis reaches, because a hypothesis that reaches none of them cannot
  change the answer.
- **Do not order the computation-law route again, with or without an
  ordinal.** `refl` fails by conversion and conversion is hypothesis-blind
  (`runs/join-refl.out:4`). `[LJ-1.477]` measured this and this task measured
  it again with the hypotheses added.
- **The next task at this site is step 3, `lset-code`**, and it is already
  `[LJ-1.474]`'s unfinished half, not a new debt. `[LJ-1.474]` built
  `lset-codes` and `feed` and stopped short of `lset-code`. All three gaps of
  this task consume it.
- **When step 3 lands, this obligation is `residue-suffices`
  (`Probe641.agda:424`) applied to three terms.** The reduction is green and
  will not need rebuilding. Price the successor against the three gap types
  and not against the obligation.
- **`IndexInHull` is the gap to attack first.** It is the only one the
  ordinality hypothesis can reach, and it is the one Devlin's proof pays with
  Σ₁ elementarity downward rather than with a definability code.
- **`π-member'` (`Probe641.agda:132`) belongs in `src/V/Collapse.lagda.md`**
  beside `π-member`, whenever a task with `src/` scope passes that way. The
  tree's `π-member` drops a conjunct that every consumer of this shape needs.
- Devlin 5.2 has NO ordinality hypothesis on an individual index. Its
  hypotheses are `lim(α)` and `X ≺₁ L_α`
  (`dev/literature/devlin-II5.md:72`). The operative hypothesis in the
  literature is Σ₁-elementarity, and the tree's counterpart of it is
  `HullElemDown.WithCode.elem` (`src/L/BoundedSubset.lagda.md:759`), which
  `HullStage` does not open. **Whether to open it at this site is a
  mathematical call and it is the mathematician's.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. **Declined, not used.**
  It is the retired dispatch index. The predecessors this task needs are named
  in the brief and were read directly.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. **Declined, not used.** It records
  the retired route. This obligation sits in the live `BoundedSubset` chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  **Declined, not used.** The per-episode journal is retired. The history of
  this task is this directory.
- `dev/ARCHIVE.md`: read at `:1`. Quote: `# ARCHIVE.md: the archive registry`.
  **Declined as not used for the term.** W4 did not fire: no module was
  retired by this task, so the registry gains no row.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`. **Declined, not
  used.** It is the archived operating rules of the retired loop. The live
  rules reached me in the preamble.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED.** Read at `:72`. Quote:
  `> 5.2 Theorem (The Condensation Lemma). Let α be a limit ordinal. If`.
  Also read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:102`. Quote:
  `The chain (c) to (q) then runs: for each ordinal γ of the collapse, the Σ₁`.
  **Used, and it corroborates the three gaps.** Devlin proves `M = L_β` by two
  inclusions, which is exactly this task's `Fwd` and `Bwd` split, and both
  inclusions are paid by transferring a Σ₁ statement built from Φ. Φ is the
  formula that names `v = L_γ`, which is this tree's `lset-code`. So the
  literature's engine and this task's residue are the same object. Devlin's
  hypotheses are `lim(α)` and `X ≺₁ L_α`, and NEITHER is an ordinality
  hypothesis on an individual index; that is independent support for the
  premise 4 finding.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  **Declined, not used.** It pins the rud route. This obligation is on the
  `𝒟`-definability route and consults no rud step.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  **Declined, not used for the term.** The truncations in this probe are the
  tree's own `∥_∥₁` on member readings, eliminated into hProps by `PT.rec`. No
  selection principle was needed and none was used.
- `dev/literature/primary-sources.md`: read at `:1`. Quote:
  `# Primary sources, second round: Jensen manuscript, Devlin, Jech`.
  **Declined, not used.** The Devlin dossier already carries 5.2 in the form
  this task needed. I did not need the source round.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  **Declined, not used.** Set-theoretic geology is not on this obligation's
  path.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `commute-at-ordinal`, `IndexInHull`, `DefFwd`, `DefBwd`,
  `JoinStepsAtOrd`, `lset-code` or `levelIn`.
- I did not refute `commute-at-ordinal`. I built no term of the negation.
- I did not postulate. I did not add a hypothesis to the obligation's type.
- I did not open the seal on `π`, on `Lset` or on `𝒟ₒ`.
- I did not open `HullElemDown` at this site. That is a mathematical call.
- I did not hide any gap in a `subst`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not delete `runs/JOINREFL.agda`. It is the diagnostic's record.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-641/`:

- `Probe641.agda`, the green probe with the reduction
- `lj-1.641-report.md`, this report
- `review-of-commute-at-ordinal.md`, the stated NO-GO
- `runs/FLOOR.agda`, `runs/W3.agda`, `runs/JOINREFL.agda`, `runs/run.sh`
- `runs/*.out`, the Agda transcripts and the two meter runs named above
