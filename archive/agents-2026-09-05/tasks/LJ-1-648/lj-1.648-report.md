# LJ-1.648 report: clause (iii)'s commute, measured against the keystone

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.648
obligation: agents/tasks/LJ-1-648/Probe648.agda::commute-from-keystone
verdict: **NO-GO on the obligation. The brief's premise 2 is REFUTED,
and the fourth debt `[LJ-1.641]` said does not exist is real, is named,
and was already dispatched and stopped at `[LJ-1.489]`.**

The obligation term is not written. Witness meter: `1 UNRESOLVED of 1,
3.34 s, probe_red=False` (`runs/meter-obligation.out:2`). The stop is
stated in `agents/tasks/LJ-1-648/review-of-commute-from-keystone.md`;
that file is the critic's input and it does not close the task.

**WHAT THE TASK EARNS, IN ONE SENTENCE.** The keystone is EXACTLY
"the hull is closed under `Lset` at ordinals" and nothing else (a green
round trip, `Probe648.agda:203-204` and `:210-213`), and
`agents/tasks/LJ-1-477/lj-1.477-report.md:308-310` already told the pod
not to spend that at this site: "Do not take `HullClosedLset` as a way
to close `JoinSteps`."

**AND THE TWO DEFINABILITY GAPS ARE NOT GAPS.** `DefFwd` and `DefBwd`
together are the obligation itself, read at a successor: the equivalence
is green at `Probe648.agda:293`, `:298`, `:303`, and
`commute-at-suc-is-an-instance` (`:336-343`) shows the successor
statement follows from `Commute` and the three side conditions `Commute`
already carries. So they sit at the same height as the obligation, not
below it.

**NOT A REFUTATION OF `Commute`.** No term of any negation was built. C-42's
sweep does not fire: I refuted a PREMISE OF THIS BRIEF, not a statement in
the tree. The same premise appears at
`agents/tasks/LJ-1-641/lj-1.641-report.md:156` and in the queue block at
`dev/pod/queue.toml:6196`; if the mathematician reads this as a
refutation of the "one producer" reading wherever it appears, the sweep
is theirs to order and its search key is `lset-code` plus `one producer`.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-648/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a
time. I did not set `GHCRTS`. Nothing is postulated, the probe carries
`--safe`, the delivered probe is green and carries no hole, and nothing
lands in `src/`. The probe is a raw `.agda` file, so it carries no
` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire
on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any
run is 749,289,472 bytes against the 2,147,483,648-byte wide cap, 35 % of
it (`runs/p-5.out`). The longest Agda run is 4.92 s (`runs/p-1.out`)
against the caps I set (600 s for the floor, 900 s for the probe). The
caps are wall-clock caps enforced by a perl alarm (`runs/run.sh` carries
the mechanism), because this macOS has no `timeout` (`[LJ-1.602]`,
`[LJ-1.610]`).

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task). No number
here is a cold-cache number, and this report does not bound one.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

**`[LJ-1.646]` HAS NO TASK HOME AND NO REPORT, AND THAT IS BY DESIGN.**
`agents/tasks/LJ-1-646/` does not exist. 646 is a SIBLING queued in the
same block as this task, not a predecessor, and the mathematician says so
in the queue: "Four consumers take the keystone as a hypothesis, so
backlog item 27 does not bite: nothing reads a RUNNING sibling's output"
(`dev/pod/queue.toml:6216-6217`).

So the standing coder clause "a module hypothesis taken from a
predecessor is the type that predecessor delivered" has no predecessor to
read, and I did not invent one. **I took the type from the tree**,
verbatim from `[LJ-1.462]`'s own D-10 correction
(`agents/tasks/LJ-1-462/Probe462.agda:118-121`), which is the file and the
lines the same queue block cites (`dev/pod/queue.toml:6207`). It is
restated at `Probe648.agda:160-163`. `[LJ-1.647]` made the same call for
the same reason and its return was accepted, so this is the settled
reading and not a fresh one.

The three PREDECESSORS that do exist were read and their verdicts taken:
`[LJ-1.641]` (green, its reduction imported and not rebuilt),
`[LJ-1.477]` (stated NO-GO, upheld) and `[LJ-1.489]` (stated NO-GO).

## THE FLOOR, BEFORE ANY PROOF

The standing coder clause orders a floor before the proof. The floor
slice is `runs/FLOOR.agda.txt`: `[LJ-1.641]`'s telescope, the hull's
`Code` and `val` opened on top, the keystone type in full, and a HOLE
where the term goes. Its run is `runs/floor-1.out`: **exit 42 at 4.64 s,
peak 740,999,168 bytes**, with `[UnsolvedInteractionMetas]` at the one
designed hole (`runs/floor-1.out:6`) and no other error.

**THE FLOOR CARRIES THE `LJ-1-641.Probe641` IMPORT, ON PURPOSE.** The
brief's premise 3 orders `π-member'` imported and not rebuilt, so that
import is part of the frame and its cost belongs in the floor rather than
being discovered later. The floor's own line shows Agda checking
`LJ-1-641.Probe641` inside the run (`runs/floor-1.out:5`).

**THE TRIM.** The obligation's type is a SET-LEVEL equation and reads no
formula, so `Formula`, `mapFo`, `CollapseIso` and `HullExt` are not
imported, exactly as `[LJ-1.641]` trimmed them. Two imports were ADDED
over that task's set and each is used: `V.Model` (`∈sucV-elim`,
`∈sucV-inl`, `self∈sucV`) for `π-sucV`, and `L.Axioms.Basic` (`Lset-suc`)
for section 1. **The finished probe costs 0.58 to 0.75 GiB against a 2 GiB
cap, so this frame has roughly 3x headroom under the WIDE tier and never
needed the heavy one.**

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX**, as the brief orders: it
is red by design, and conjunct 1 runs every `.agda` under this task home.
`[LJ-1.641]`'s own floor was left as `runs/FLOOR.agda` and its critic
records the consequence: "conjunct 1 FAILED"
(`agents/tasks/LJ-1-641/review-of-LJ-1-641-1.md:40`). The bytes here are
what produced `runs/floor-1.out`, and the file's header carries the three
commands that reproduce the run.

## W3, AND ITS ESTIMATE IS REFUTED DOWNWARD

**The brief names W3 as "Whether `DefFwd` and `DefBwd` need the keystone
at `𝒟ₒ` as well as at `Lset`", at 80 to 170 lines. THE ANSWER IS NO AND
IT COSTS ONE LINE.**

`𝒟ₒ` at a level IS `Lset` at a successor. `Lset-suc`
(`src/L/Axioms/Basic.lagda.md:196`) is `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` and
it holds for every `σ` with no ordinality hypothesis, which that chapter
states in terms at `:185-186`: "It was stated with an ordinality
hypothesis and the hypothesis turned out to be dead". So
`𝒟-at-level` (`Probe648.agda:84`) is `sym (Lset-suc β)`, and a hypothesis
about `Lset` already speaks about every `𝒟ₒ` the obligation names. **There
is no second keystone to want, so W3's question cannot be answered YES.**

The restated gaps and their conversions are green at `Probe648.agda:90`
to `:136`. Nothing is weakened: `index-suc`, `fwd-suc` and `bwd-suc` are
`subst` along that one equation and `commute-from-suc-gaps` recovers the
obligation through `[LJ-1.641]`'s assembly unchanged.

**W3 was the wrong question, and section 4 of the probe is the right
one.** Not because the brief was careless: `𝒟ₒ` genuinely looks like a
second operation, and only `Lset-suc` shows it is not.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-648/Probe648.agda`, module
`LJ-1-648.Probe648 {ℓ} (lem)`, inside `module Frame648`. 432 total lines,
223 non-blank non-comment lines. **Twenty delivered names, all metered
green in one grouped run: `0 UNRESOLVED of 20`, 3.21 s,
`probe_red=False` (`runs/meter-names.out:21`).**

- Section 1, W3: `𝒟-at-level` (`:84`), the three successor-form gaps
  (`:90`, `:98`, `:104`), the three conversions (`:118`, `:123`, `:126`),
  `commute-from-suc-gaps` (`:133`).
- Section 2, the keystone's strength: `LsetCodeOrd` (`:160`),
  `LsetCodeOrd∥` (`:165`), `HullClosedLsetOrd` (`:170`),
  `hull-closed-op∥` (`:184`), `keystone∥` (`:199`), `keystone-closure`
  (`:203`), `closure-keystone` (`:210`).
- Section 3, the new lemma: `π-sucV` (`:230`).
- Section 4, the measurement: `CommuteAtSuc` (`:288`),
  `fwd-from-commute-suc` (`:293`), `bwd-from-commute-suc` (`:298`),
  `commute-suc-from-def-gaps` (`:303`),
  `commute-at-suc-is-an-instance` (`:336`).
- Section 5, the index gap sharpened: `RankInHull` (`:365`),
  `index-from-rank` (`:372`), `rank-from-index` (`:376`).
- Section 6, the residue: `Residue` (`:402`), `commute-from-residue`
  (`:405`), `commute-from-keystone-and-residue` (`:411`),
  `residue-from-commute` (`:416`), `keystone-supplies-side` (`:426`).

## THE THREE FINDINGS, EACH WITH ITS EVIDENCE

**1. THE KEYSTONE IS EXACTLY A CLOSURE PROPERTY OF THE HULL.**
`keystone-closure` (`:203-204`) and `closure-keystone` (`:210-213`) are a
round trip, so up to the truncation `[LJ-1.647]` measured free
(`agents/tasks/LJ-1-647/Probe647.agda:171-173`) the keystone and
`HullClosedLset` at ordinals are the same hypothesis. The backward leg
costs three lines because hull membership IS "is the value of a code"
(`src/L/Hull.lagda.md:337-339`).

**2. `DefFwd` AND `DefBwd` ARE THE OBLIGATION AT A SUCCESSOR.** With
`𝒟-at-level` and `π-sucV`, `CommuteAtSuc` (`:288-291`) is `Commute`'s own
conclusion at `δ := sucV β`, and it is interderivable with
`DefFwdSuc × DefBwdSuc` (`:293`, `:298`, `:303`). This is the finding the
brief did not expect and it is why the answer is NO-GO rather than a
partial GO: there is no arrangement of the keystone that produces two
statements which, taken together, prove clause (iii) at every successor
of a hull member.

**3. THE INDEX GAP IS ONE SENTENCE AND ITS PRODUCER IS THE FORMULA, NOT
THE CODE MAP.** `RankInHull` (`:365-370`) drops both `𝒟ₒ` and the stray
`β` and is equivalent to `IndexInHullSuc` (`:372`, `:376`). What is left
is "a hull member of `Lset δ` has a level index inside the hull", which is
a SEARCH. The hull's only search rule is `hull-closed`
(`src/L/Hull.lagda.md:415`) and it takes a `Formula Code 1`. A code map is
not a search. **Here `[LJ-1.641]`'s reading survives review: this gap does
name `Lset` in a condition. It wants the keystone's INPUT.**

## WHAT THE KEYSTONE ACTUALLY PAYS FOR

One thing, and it is real. `keystone-supplies-side` (`:426-433`) gives
`⟨ Lset (sucV β) ∈ˢ HS.M ⟩`, the third side condition of the instance in
finding 2, from `⟨ sucV β ∈ˢ HS.M ⟩`. That is a genuine consumer and
`[LJ-1.647]`'s step 2 is the same consumer at a different argument order.

And `commute-from-keystone-and-residue` (`:411-412`) is the obligation
from the residue with the keystone bound to an UNDERSCORE. **That
underscore is checkable evidence: no row of the assembly eliminates the
keystone.**

## W2 (DD4)

**The one proof in section 2 is written at a generic operation and a
generic side condition, from the WEAKEST form of the hypothesis.**
`hull-closed-op∥` (`:184-197`) is generic in `F : S → S` and in
`P : S → Type (ℓ-suc ℓ)` and takes the code map TRUNCATED; nothing in its
body names `Lset`, `IsOrd` or any stage. `keystone-closure` is its only
instance and costs one line.

**IT IS `[LJ-1.647]`'S TERM AND THE CREDIT IS THAT TASK'S.** Its report
asks this task to take it rather than rebuild it. **I could not import
it**, and the reason is structural rather than stylistic: `[LJ-1.647]`
built its own `HullStage` with `module C = Collapse M` deliberately
dropped (`agents/tasks/LJ-1-647/Probe647.agda:62-63`), while this
obligation's type is written with `HS.C.π` throughout and must use
`L.BoundedSubset`'s `HullStage`. The two `HullStage`s are different
modules with different telescopes, so no instantiation identifies them.
The probe records this at `:174-183`. **A successor that wants both
halves should ask whether `hull-closed-op∥` belongs in
`src/L/Hull.lagda.md`, where one copy would serve every consumer.** This
task's scope forbids `src/`.

`π-sucV` (`:230`) is a second W2 case and it is generic already: no
keystone, no ordinality, no extensionality, no formula.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No dead fragment was
deleted. `dev/ARCHIVE.md` gains no row from this task.

## WHAT THE NEXT BRIEF NEEDS

**FOR `[LJ-1.646]`, THE KEYSTONE ITSELF. Deliver the FORMULA as well as
the code map.** `[LJ-1.462]`'s `feed` (`Probe462.agda:101-102`) builds the
code map from `LsetGraph` and a `Vec Code (countFo LsetGraph)`, and
`[LJ-1.474]` delivered that vector. **The same two ingredients build the
`Formula Code 1` that `hull-closed` needs**, and finding 3 shows that is
what the index gap wants. A brief that asks only for
`Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))` throws the ingredient
away and keeps the half this task measures to be insufficient for every
one of clause (iii)'s three gaps. `[LJ-1.647]` is unaffected: step 2 needs
only the code map and it is already closed.

**FOR CLAUSE (iii). Do not re-dispatch `DefFwd` and `DefBwd` as separate
objects.** Finding 2 makes them one statement and that statement is
`[LJ-1.489]`'s stated NO-GO,
`piCommuteD : (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)`
(`agents/tasks/LJ-1-489/lj-1.489-report.md:12`), whose verdict is "The
two sides cannot agree without elementarity" (`:139-140`). **What is new
and worth pricing: `CommuteAtSuc` is that obligation restricted to
`y := Lset β`.** `[LJ-1.489]` attacked it at a general hull member. At a
LEVEL the right-hand side is again a level, `Lset-suc` applies on both
sides, and `[LJ-1.489]`'s `JoinAtD` obstruction may not be the same
obstruction. That is the cheapest unmeasured move I can name.

**FOR `[LJ-1.650]`.** It takes the same keystone. If its obligation
carries a condition naming `π`, the language argument in
`review-of-commute-from-keystone.md` part 3 applies there unchanged:
`hull-closed` answers a `Formula Code 1` interpreted in `Lset lam`, and
`π` is a meta-level function `S → S` (`src/V/Collapse.lagda.md:53`), not a
term of that language. **Ask that question before pricing a formula.**

**FOR `src/`. `π-sucV` is new, green and hypothesis-free**, and
`src/V/Collapse.lagda.md` is where it belongs. `[LJ-1.641]`'s `π-member'`
is still homeless for the same reason and that task said so.

**WHAT THIS TASK DOES NOT SETTLE.** It does not build `lset-code-ord`. It
does not inhabit `RankInHull`, `CommuteAtSuc`, `IndexInHull`, `DefFwd` or
`DefBwd`. It does not refute `Commute` or any of them. It does not inhabit
`levelIn`, and it does not touch `cover` or clause (i) or clause (ii). It
does not run C-42's sweep. It does not edit `src/`.

## RUNS

All runs under `GHCRTS=[-A64m -I0 -M2g]`, one Agda process at a time.

| run | file | exit | seconds | peak bytes |
|---|---|---|---|---|
| `runs/floor-1.out` | `FLOOR.agda.txt` | 42 (designed hole) | 4.64 | 740,999,168 |
| `runs/p-1.out` | `Probe648.agda` | 0 | 4.92 | 610,844,672 |
| `runs/p-2.out` | `Probe648.agda` | 0 | 4.52 | 655,376,384 |
| `runs/p-3.out` | `Probe648.agda` | 0 | 3.99 | 599,474,176 |
| `runs/p-4.out` | `Probe648.agda` | 0 | 4.35 | 709,394,432 |
| `runs/p-5.out` | `Probe648.agda` | 0 | 4.80 | 749,289,472 |
| `runs/p-final.out` | `Probe648.agda` | 0 | 3.17 | 602,357,760 |

**EVERY AGDA RUN OF THE PROBE WAS GREEN, INCLUDING THE FIRST.** `p-1` to
`p-5` are the five incremental saves C-22 asks for, not five repair
attempts, and `p-final` is the delivered bytes re-run last, after the
report's own citations were corrected in a comment. That last run
overwrote an earlier run of the same bytes which read 6.77 s and
578,093,056 bytes; the row below is the run the file now holds. I hit no Agda error in this task at all, and no `[UnequalTerms]`
anywhere: the file never attempted the join `[LJ-1.477]` and `[LJ-1.489]`
each measured to fail, because sections 1 and 4 route around the
constructors instead of through them.

Meters, both against the delivered bytes:

- The obligation: `1 UNRESOLVED of 1`, 3.34 s, `probe_red=False`,
  `[NotInScope]` (`runs/meter-obligation.out`). **That is the intended
  stated NO-GO and it is the same shape `[LJ-1.489]` returned.**
- The twenty delivered names in one grouped run: `0 UNRESOLVED of 20`,
  3.21 s, `probe_red=False` (`runs/meter-names.out:21`).
- This worktree has no `.venv`. The meter ran as
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`. I
  did not add a dependency and I did not create a local `.venv`.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. READ, AND IT SUPPLIED FINDING 3'S
  PROVENANCE.** Quote at `archive/dev/LJ-dispatch-index.md:43`:

  > | LJ-1.3 | Build: the Skolem hull, a least-witness search over the order | DELIVERED 343 lines | Ported from 241 archived. 0.0070 s/line, 0.91x the bar. Does NOT use σ₁-up: LJ-1.5 does |

  The hull was built as a SEARCH, and that is why a code map is the wrong
  object for the index gap: a map is not a search.

- **`archive/dev/JOURNAL.md`. READ.** Quote at `archive/dev/JOURNAL.md:328`:

  > **DD27 landed.** `[LJ-1.23]` re-indexed the hull by `Code`, 372 to 431 lines at

  This is why `closure-keystone` (`Probe648.agda:210-213`) costs three
  lines: the re-indexing is what makes hull membership definitionally "is
  the value of a code", so the round trip in finding 1 needs no formula.
  `[LJ-1.647]` found this line first and I confirmed it at that line.

- **`archive/dev/JOURNAL-archived.md`. NOT USED.** I grepped it for
  `collapse`, `Hull` and `𝒟ₒ`. Its hits (`:493`, `:537`, `:555`) are about
  the PORT of the collapse and hull chapters and about probe scheduling,
  not about what the collapse commutes with. Nothing in it bears on this
  obligation.

- **`dev/ARCHIVE.md`. NOT USED, and declined for a second reason.** I
  grepped it for `collapse`, `Hull` and `𝒟ₒ` and it returned no hit. W4
  also retires nothing in this task, so this file gains no row either.

- **`archive/dev/ORCHESTRATION.md`. NOT USED.** Same grep, no hit. It is
  the archived operating document of the pre-cutover flow and carries no
  mathematics.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`. READ, AND IT CORROBORATES THE NO-GO.**
  Quote at `dev/literature/devlin-II5.md:102`:

  > The chain (c) to (q) then runs: for each ordinal γ of the collapse, the Σ₁

  and at `:106`:

  > L_γ ∈ M for every γ < β, hence ⋃_{γ<β} L_γ ⊆ M (`dev2.txt:1200-1240`).

  **Devlin never commutes the collapse with the stage operation.** He
  transfers a Σ₁ statement by elementarity and concludes MEMBERSHIP. His
  two ingredients are the Σ₀ level formula `Φ(z, v, γ)` (`:95-99`) and
  Σ₁-elementarity, which are precisely `[LJ-1.477]`'s "elementarity plus
  the level formula" (`agents/tasks/LJ-1-477/lj-1.477-report.md:315`).
  Neither ingredient is a code map.

- **`dev/literature/truncation-and-selection.md`. READ, AND IT LICENSES
  SECTION 2's TRUNCATION.** Quote at
  `dev/literature/truncation-and-selection.md:95`:

  > **This is the only free case.** Everything below is about paying for the rest.

  `hull-closed-op∥` eliminates two truncations into `⟨ F y ∈ˢ HS.M ⟩`,
  which is an hProp, so both are the free case and no choice principle is
  used. This is why finding 1's round trip may pass through
  `LsetCodeOrd∥` without weakening the measurement.

- **`dev/literature/digest.md`. NOT USED.** It is the index over the
  literature notes. `devlin-II5.md` is the note this obligation needs and
  I went to it directly.

- **`dev/literature/primary-sources.md`. NOT USED.** It records where the
  sources are and how they are cited. This task quotes one source and its
  citation was already fixed by `[LJ-1.477]` and `[LJ-1.489]`.

- **`dev/literature/devlin-errata.md`. NOT USED.** No step of this task
  rests on a Devlin proof being CORRECT: the literature is cited here only
  to show which ingredients his route uses, and an erratum in that route
  would not change that reading.
