# Retrospective: every mathematical research decision since the POD cutover

**Written by the resident mathematician at session start, 2026-08-25, on the
owner's instruction.** This is a project record of the standing session, so it
is English in ASD-STE100. The owner got the same content in Chinese.

**Window.** From commit `fc676cb` (2026-08-18 10:14:16 +0800, the cutover) to
the last transition record at `2026-08-25T11:33:53Z`. Source of every count
below: `dev/pod/transitions/2026-08.jsonl` (3,999 records), the briefs and
reports under `agents/tasks/LJ-1-{386..632}/`, and `git`. No number here comes
from a command containing `head`.

## 1. THE SCALE

| Fact | Value |
|---|---|
| Task codes dispatched | 242, `LJ-1.386` to `LJ-1.632` |
| Briefs on disk in that range | 245. Three (387, 405, 415) never entered the log |
| Closed GO | 109 |
| Closed NO-GO | 90, of which 76 through `sys-critic-upheld-no-go` |
| Closed `sys-obligations-satisfied` | 29 |
| SHELVED | 6 (541, 572, 603, 615, 620, 628) |
| Live now | RUNNING 629, 630. READY 631, 632 |
| Tasks needing one retry or more | 117 of 242 |
| Refill events | 125 |
| Role records | coder 1,748. mathematician_adversarial 587. coder_adversarial 314. mathematician 65 |

## 2. WHAT REACHED THE TREE

| Fact | Value |
|---|---|
| Commits since the cutover | 846 |
| Commits touching `src/` | 10 |
| `src/` change, excluding `src/README.md` | +1,156 lines, -2 lines, over 8 masters |
| Probe Agda written under `agents/tasks/LJ-1-{386..632}` | 459 files, 79,799 lines, median 129 lines |
| Probe lines per landed line | about 69 to 1 |
| `src/Landmarks.lagda.md` | UNCHANGED since the cutover. `grep -ci gch` gives 0 |
| `src/L/GCH.lagda.md` | 70 lines. It carries `GCHStatement` and no proof |
| New `dev/LESSONS.md` entries committed | ZERO. One exists, R-42, and it is uncommitted |

**READ THE LAST TWO ROWS TOGETHER.** The trophy case did not move, and the one
measured law this campaign produced is not yet in a commit.

## 3. WHAT THE BRIEFS ASKED FOR

- **21 of 245 briefs name a `src/` path.** 148 say "Land nothing in `src/`".
  The campaign was probe work by design, and the design held.
- **227 distinct obligation term names. 24 of them are carried by more than one
  task, and 54 tasks are involved in a repeat.** That is 22 percent of every
  dispatch spent on an object a previous dispatch had already been given.
- The widest repeat is `CardAboveL`: five tasks (528, 555, 599, 616, 624).
  `landing-survey`, `domAt-at-carve`, `rec-graph-at-infinite` and
  `class-pred-v` each took two.

## 4. THE MATHEMATICS, AS ONE ARC

Four threads, in order.

1. **386 to 448. The band recursion and the square law.** It proved `InjCode`
   is a proposition, so the least code is DATA (401), and it assembled the main
   chain (420). It also produced the campaign's first two hollow GOs.
2. **450 to 521. The condensation frame.** `someEnv` took nine dispatches and
   landed at 511. `levelIn` took three. This thread has the highest NO-GO
   density of the four.
3. **522 to 564. The last mile to GCH.** 523 built `GCHBridge` and priced the
   join: seven further inputs stand between the bounded subset theorem and
   `GCHStatement`, and six of the seven are stated nowhere in the tree.
4. **565 to 632. The `class-pred` table and the landings.** 625 surveyed where
   the four paid ingredients would live and REFUTED its own brief's guess: no
   ingredient needs a new master, and each lands with zero new import edges.
   626 and 628 landed two of them.

**ONE RESIDUE RUNS THROUGH ALL FOUR.** 93 of 238 reports name an untruncation.
56 name the square law. The residue has been met under at least eight names:
`amb-init` (393, refuted), `kappa-is-limit` (396, false as stated), the
ambient-to-coded crossing (441), `band-untruncation` (607), `value-is-L` and
`TransferL` (615), `Inj-extract` (618), `SiteFiber` (623) and ingredient (iii)
of `class-pred` (604).

**623 PROVED TWO OF THOSE NAMES ARE ONE TYPE**, by `refl`:
`P621.SiteFiber α ≡ P618.PairingAt α` (`agents/tasks/LJ-1-623/Probe623.agda:95-96`).

**THE REASON IS IN ONE LINE OF THE TREE.** `sq` is a bare module parameter at
`src/L/StageCardinal.lagda.md:17`, carrying injectivity and nothing else: no
formula, no `isL`, no stage, no grade. Every route above tries to make a
definable object out of a parameter that carries no definition.

## 5. THE MOST EXPENSIVE FINDING OF THIS REVIEW

**The blocker was measured before the cutover, and this campaign read that
measurement once in 238 reports.**

- `archive/dev/LJ-dispatch-index.md:465`, row `LJ-1.8`: "STATEMENT LANDED; ONE
  HYPOTHESIS BLOCKS THE PROOF | `sq : SqShape`, and LJ-1.286 measured that the
  delivered square law CANNOT supply it."
- `:344`, row `LJ-1.286`: "LANDED. ONE HYPOTHESIS LEFT, `sq`".
- `:362`, row `LJ-1.305`: "Route 1 CLOSED by countermodel: `sq omega` is NOT an
  hProp."

Measured citation counts across the 238 post-cutover reports: **`:465` cited
ONCE** (by `[LJ-1.523]`), **`:344` cited ZERO times**, `:362` cited twice.
126 of the 238 reports do cite that index at some line, so the file was being
read; the three rows that name the campaign's own wall were not the lines read.

**THE MECHANISM EXPLAINS IT AND IT IS NOT AN AGENT'S FAULT.** The
program-generated `## ARCHIVE` block names FILES with a score, never rows:

    - CANDIDATE archive/dev/LJ-dispatch-index.md  (score 236.855)

`archive/dev/LJ-dispatch-index.md` is a table of several hundred rows. A brief
that hands a coder that path has handed it a haystack. 244 of 245 briefs carry
such a block.

**`[LJ-1.523]` FOUND THE SAME SHAPE INDEPENDENTLY**: five pre-cutover
dispatches (LJ-1.90, LJ-1.90-A, LJ-1.91, LJ-1.121, LJ-1.8) had already reached
the join it was sent to price, and its own brief claimed it was the first.

## 6. WHERE THE MACHINE TIME WENT

854 acceptance records carry a seconds figure. They total **45,855 s, 12.7
hours**.

| Task | seconds | share | end state |
|---|---|---|---|
| LJ-1.541 | 20,313 | 44% | SHELVED, delivered-elsewhere |
| LJ-1.547 | 10,853 | 24% | closed `sys-obligations-satisfied` |
| LJ-1.572 | 9,000 | 20% | SHELVED, proven-futile |
| everything else, 239 tasks | 5,689 | 12% | |

**THREE TASKS TOOK 88 PERCENT OF EVERY MEASURED AGDA SECOND.** Twenty records
sat at the 1,800 s cap, worth 10.0 hours, or 79 percent of all measured
seconds, and all twenty belong to those three tasks.

**AND 541's OBLIGATION WAS THEN DELIVERED IN 7.67 s.** `[LJ-1.559]` carried the
same obligation name, `domAt-at-carve`, and measured its whole chain from
nothing at 7.67 s in a trimmed frame (`dev/pod/shelf/LJ-1.541.toml.shelved`).
The law that explains the gap is R-42, and R-42 is the uncommitted lesson of
section 2.

19 heap-wall records. Separately, **278 `no-match` records over 22 tasks**
(LJ-1.443 72, LJ-1.505 46, LJ-1.422 34): a branch table that does not match a
return re-dispatches the task, and `dev/pod/maintainer-backlog.md` items 23,
24, 25 and 26 record that the looping rows were written by this slot.

## 7. THE INDEPENDENT AUDIT

`dev/pod/audit-2026-08-20.md`, over LJ-1.386 to LJ-1.414: 10 CLEAN, 9 MINOR,
7 FLAGGED. The owner verified F1 and F9. Two failures matter beyond their
tasks:

- **F1 and F3: a GO built on a hypothesis a predecessor had REFUTED.** 398 took
  `kappa-is-limit` fifty minutes after 396 refuted it, and cited 396's BRIEF
  rather than its REPORT. The critic proved the telescope inconsistent in Agda.
- **F9: the adversarial layer almost never ran**, because `no-go-stated`
  matched on the worker's own `review-of-*.md` while the escalate branch
  required that same file to be absent.

**BOTH ARE FIXED IN THE STANDING CLAUSES AND THE FIX IS VISIBLE IN THE DATA.**
`mathematician_adversarial` first appears at `2026-08-19T07:41:02Z` and now
holds 587 records, and 76 tasks close at `sys-critic-upheld-no-go`.

## 8. WHAT I CHANGE, STARTING NOW

Each item names the measurement above that forces it.

1. **Cite the archive at a ROW, never at a file.** Section 5. When a brief's
   `## ARCHIVE` block offers `LJ-dispatch-index.md`, I open it, find the rows
   that bear, and put the row TEXT in the brief above the block. The block
   stays untouched; it is program-generated.
2. **Before funding any construction, grep the tree for the object.** Section 4
   and my standing clause of 2026-08-25. `via-col-square`
   (`src/L/Ordinal/SquareLaw.lagda.md:960-961`) already proves `Init α → sq α`.
   `[LJ-1.629]`, running now, is the first brief to ask the right question:
   is the bill's site an initial ordinal.
3. **Put a wall-clock ceiling and a bisection order in any brief whose
   obligation compares two spellings.** Section 6. R-42 is the law. A task that
   has burned two runs at the cap has told me something about the TERM, and the
   correct response is a trimmed frame, not a third run.
4. **Commit-worthy lessons are part of the deliverable.** Section 2. R-42 must
   land. I will name the lesson a task is expected to produce in the brief.
5. **Never queue two dependent tasks in one dispatch.** Backlog item 27. A
   RUNNING task's output is uncommitted and invisible to its sibling.
6. **A repeated obligation name is a signal to STOP and re-plan, not to
   re-dispatch.** Section 3. Five tries at `CardAboveL` and nine at `someEnv`
   were each re-dispatches of a brief, not a new line of attack.
7. **Take a hypothesis from the predecessor's REPORT, never its BRIEF.** Audit
   F1 and F3. This is already a standing clause; the audit shows what it costs
   when it slips.

## 9. THE ONE MATHEMATICAL QUESTION THIS REVIEW RAISES

The campaign has spent seven days proving, at eight sites and two grains, that
a definable pairing cannot be extracted from a `sq` that carries no formula.
`[LJ-1.617]` then measured that **the bill pays at SITE grain**, and that the
module-grain circle binds a demand nothing in the tree makes.

So the open question is not "how do we untruncate `sq`". It is: **at the sites
the bill actually reaches, is `sq` already proved?** `via-col-square` proves it
at initial ordinals. `[LJ-1.629]` asks whether the site is initial. If it is,
the residue that closed 33 NO-GO reports was never on the path.

I will not write a brief on this until `[LJ-1.629]` returns.
