# LJ-1.649 report: levelIn, assembled from its four steps

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.649
obligation: agents/tasks/LJ-1-649/Probe649.agda::levelin-from-steps
verdict: **GO on the obligation. The decomposition COMPOSES. It also
carries TWO corrections that change what the four sibling briefs are
worth.**

The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 2.59 s`, `0 UNRESOLVED of 1`, `probe_red=False`). Every
other name in the probe is green too (`runs/meter-names.out`,
`0 UNRESOLVED of 10`).

**READ THESE THREE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **STEP 3 IS NOT A CONJUNCT OF THE ASSEMBLY.** Two hypotheses close
   `levelIn`, not three: steps 2 and 4. `levelin-from-two`
   (`Probe649.agda:162-167`) is the same conclusion with step 3 deleted
   and it is green. Step 3 is a producer for steps 2 and 4 only.
2. **THE CONSUMER'S OWN `IsOrd δ` IS ALSO UNUSED** on that route.
   `levelin-from-two` does not take it.
3. **BUT A FIFTH FACT IS REAL, AND IT IS THE PRICE OF THE ORDINAL
   KEYSTONE, NOT A FIFTH STEP OF THE DECOMPOSITION.** `[LJ-1.647]`
   delivered step 2 with `IsOrd y` on the HULL side
   (`agents/tasks/LJ-1-647/Probe647.agda:165-167`). This consumer
   carries `IsOrd δ` on the RANGE side. Nothing in the tree joins them.
   The missing fact is named `PiReflectsOrd` at `Probe649.agda:222-223`.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-649/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at
a time. I did not set `GHCRTS`. Nothing is postulated, the probe carries
`--safe`, the delivered probe carries no hole, and nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no ` ```agda `
fence, counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any
run is 507,527,168 bytes against the 2,147,483,648-byte wide cap, which
is 24 % of it. That run is `runs/p-final.out`, the delivered bytes. The
longest Agda run is 3.85 s (`runs/p-1.out`) against the caps I set
(600 s for the floor, the miniature and the red slices, 900 s for the
probe). The caps are wall-clock caps enforced by a perl alarm
(`runs/run.sh` carries the mechanism), because this macOS has no
`timeout` ([LJ-1.602], [LJ-1.610]).

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task). No number
here is a cold-cache number, and this report does not bound one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.462]` closed **NO-GO at D-10 step 3**
(`agents/tasks/LJ-1-462/lj-1.462-report.md:77`). The standing coder
clause says a NO-GO predecessor is a stop. **It is not a stop here, and
the reason is the brief's own words:** "Build none of the three
hypotheses. Step 1 is the only one you discharge, and it is already
inhabited" (`agents/tasks/LJ-1-649/LJ-1.649.md`, the OBLIGATION block).
The clause forbids me to INHABIT a type the predecessor failed to
inhabit. This task takes step 3 as a HYPOTHESIS and inhabits nothing but
the assembly. The predecessor's report does not name any of the four
steps FALSE.

**The types I took are the types the predecessor DELIVERED**, and its
file is green (`agents/tasks/LJ-1-462/lj-1.462-report.md:219-223`, three
forced rechecks, exit 0 every time):

| step | type | site |
|---|---|---|
| 1 | `Step1`, inhabited by `C.πX-member` | `agents/tasks/LJ-1-462/Probe462.agda:130-134` |
| 2 | `HullClosedLset` | `agents/tasks/LJ-1-462/Probe462.agda:136-138` |
| 3 | `lset-code` | `agents/tasks/LJ-1-462/Probe462.agda:109-111` |
| 4 | `πCommuteLset` | `agents/tasks/LJ-1-462/Probe462.agda:140-142` |

The conclusion is `levelIn` verbatim from
`src/L/BoundedSubset.lagda.md:917`, restated at `Probe649.agda:151-152`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

## 2. THE FLOOR, MEASURED BEFORE ANY PROOF

The standing coder clause orders a floor before a heavy object. I ran it.
`runs/FLOOR.agda.txt` is the trimmed frame, the four step types in full,
and a HOLE where the term goes. It is `.agda.txt` and not `.agda`,
because every `.agda` under a task home is a verification target of the
acceptance run (`scripts/pod/facts.py:489`, `verification_target`).

**THE FRAME COSTS 0.34 GiB AND 2.84 s.** Three forced rechecks, the
interface deleted before each: 2.80 s, 3.22 s, 2.84 s. Median wall
**2.84 s**. Median peak RSS **361,676,800 bytes**. Exit 42 every time,
with ONE error and it is the hole (`runs/floor-1.out`,
`[UnsolvedInteractionMetas]` at `Floor649.agda:100.24-25`).

**THE IMPORT TRIM.** I started from `[LJ-1.462]`'s import set and cut
every import that only `feed` used: `L.Coding.Sequence`, `FOL.Syntax`,
`FOL.Manipulation.Parameters`, `L.Constructible.𝒮ʟ`, `Cubical.Data.Nat`
and `Cubical.Data.Vec`. The assembly names none of them. I KEPT
`module C = Collapse M`, which `[LJ-1.647]` cut, because this conclusion
names `C.πX`.

**The frame is not the problem here.** The delivered probe is 507 MB and
2.61 s, so the whole assembly adds 0.14 GiB over the floor. This object
is not heavy and the floor proves it before any proof was attempted.

## 3. THE ASSEMBLY

### 3.1 W2 (DD4): the mathematics once, at a generic operation

`pix-closed-op` (`Probe649.agda:124-139`) is the ONLY proof in the file.
Every other term is an instance of it. It says: the collapse's RANGE is
closed under any operation `F` that the hull is closed under and that the
collapse commutes with, PROVIDED a range-side side condition `Q`
reflects back to a hull-side side condition `P`.

```
  pix-closed-op : (F : S → S) (P Q : S → Type (ℓ-suc ℓ))
                → ((y : S) → ⟨ y ∈ˢ M ⟩ → Q (C.π y) → P y)
                → ((y : S) → ⟨ y ∈ˢ M ⟩ → P y → ⟨ F y ∈ˢ M ⟩)
                → ((y : S) → ⟨ y ∈ˢ M ⟩ → P y → C.π (F y) ≡ F (C.π y))
                → (δ : S) → Q δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ F δ ∈ˢ C.πX ⟩
```

It mentions no `Lset`, no `IsOrd` and no stage. `[LJ-1.648]` and
`[LJ-1.650]` can take this term and supply their own `F`. The three
hypotheses are step 2, step 4 and one new one, `reflect`, and `reflect`
is FREE whenever `P` is trivial. That last sentence is the whole finding
of the task, stated at the generality where it is true.

The type is 5 lines (`Probe649.agda:124-128`) and the body is 11
(`:129-139`). The whole generic theorem is 16 non-blank non-comment
lines.

### 3.2 The four instances, all green

| term | site | hypotheses it spends |
|---|---|---|
| `levelin-from-steps` | `Probe649.agda:151-156` | steps 2 and 4. `lc` and `oδ` bound, never used |
| `levelin-from-two` | `Probe649.agda:162-167` | steps 2 and 4. No step 3, no `IsOrd δ` |
| `levelin-from-647` | `Probe649.agda:227-230` | `PiReflectsOrd`, 647's step 2, step 4 |
| `levelin-from-647-ord-commute` | `Probe649.agda:241-245` | the same, with step 4 ordinal-conditioned |

`levelin-is-a-weakening` (`Probe649.agda:170-173`) states the first as a
weakening of the second, so the claim "step 3 is not a conjunct" is a
term in the file and not a sentence in this report.

### 3.3 `[LJ-1.477]`'s sketch typechecks unchanged

`[LJ-1.477]` wrote the composition by hand at
`agents/tasks/LJ-1-477/lj-1.477-report.md:257-263` and said "I do not
claim this composition typechecks" (`:267-268`). I copied it verbatim
into `levelin-477-sketch` (`Probe649.agda:184-194`). **It is green.** Its
author also predicted the step 3 finding at `:265-266`: "That composition
uses steps 1, 2 and 4. It does not use step 3. Step 3 is a producer for
2 and 4, not a conjunct of this join." **That prediction is now
CONFIRMED by a typechecker and not by an argument.** It sat untested from
`[LJ-1.477]` until this task.

This is the second proof of the same fact in one file, which W2 normally
forbids. The reason it stays: it settles a claim about one specific
written term, and the generic route cannot settle that.

### 3.4 `C.πX-intro` is used, and it is not a fifth step

The assembly spends exactly one fact about the range beyond step 1:
`πX-intro : (y : S) → ⟨ y ∈ˢ X ⟩ → ⟨ π y ∈ˢ πX ⟩`
(`src/V/Collapse.lagda.md:86-87`). It is DELIVERED, and it is the
range's own introduction rule. `[LJ-1.462]` did not list it among the
four because it is not an obligation. **So the answer to the brief's
question "do steps 2, 3 and 4 compose without a fifth fact" is YES for
`[LJ-1.462]`'s own step types.**

## 4. THE FIFTH FACT, AND WHERE IT REALLY COMES FROM

**`[LJ-1.462]`'s step 2 is NOT the step 2 that `[LJ-1.647]` delivered.**

```
462:  HullClosedLset    = (y : S) → ⟨ y ∈ˢ M ⟩ →            ⟨ Lset y ∈ˢ M ⟩
647:  hull-closed-lset  = (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩
```

647 added `IsOrd y` because `[LJ-1.646]`'s keystone is
ordinal-conditioned (`agents/tasks/LJ-1-462/Probe462.agda:118-121`,
`lset-code-ord`). 647 then wrote that the added hypothesis "is free at
every consumer that already carries ordinality"
(`agents/tasks/LJ-1-647/Probe647.agda:180-181`).

**IT IS NOT FREE AT THIS CONSUMER.** This consumer carries `IsOrd δ`,
where `δ` is in `C.πX`, the RANGE. Step 2 wants `IsOrd y`, where `y` is
the hull preimage that step 1 hands over. **Agda says so in its own
words**, and I measured it rather than argued it. `runs/NO-FIFTH.agda.txt`
is the same assembly with 647's step 2 and no fifth hypothesis. It leaves
EXACTLY ONE hole, at the `IsOrd` slot (`runs/no-fifth-1.out`, one
`[UnsolvedInteractionMetas]` at `76.43-44`). `runs/NO-FIFTH-ODELTA.agda.txt`
plugs the consumer's own `oδ` into that slot:

```
NoFifthOdelta649.agda:76.43-45: error: [UnequalTerms]
y != δ of type (Cubical.HITs.CumulativeHierarchy.Base.V ℓ)
when checking that the expression oδ has type IsOrd y
```

(`runs/no-fifth-odelta-1.out`.) Everything else in that file closes.

**THE FIFTH FACT, NAMED** (`Probe649.agda:222-223`):

```
  PiReflectsOrd : (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd (C.π y) → IsOrd y
```

With it, `levelin-from-647` is green (`Probe649.agda:227-230`).

**IT IS NOT A FIFTH STEP OF THE DECOMPOSITION. IT IS THE PRICE OF THE
ORDINAL KEYSTONE.** If `[LJ-1.646]` lands the UN-ordinal `lset-code`
instead, 647's `hull-closed-lset-plain`
(`agents/tasks/LJ-1-647/Probe647.agda:187-189`) gives the plain
`HullClosedLset` and `levelin-from-two` closes with no fifth fact at
all. `no-fifth-if-keystone-is-plain` (`Probe649.agda:252-255`) is that
statement as a green term.

### 4.1 Where `PiReflectsOrd` would come from, and what I did NOT measure

The literature says the collapse of an extensional set is an
ISOMORPHISM, not just a surjection: "a unique π, a unique transitive M,
an isomorphism π : ⟨X, ∈⟩ ≅ ⟨M, ∈⟩"
(`dev/literature/devlin-II5.md:200-201`). An isomorphism reflects
ordinality. The tree has the two parts:

- `hullExt : isExt M` is **PROVED**, at
  `src/L/BoundedSubset.lagda.md:1340`, inside `module HullExt`
  (`:1235`), whose telescope is this one minus `succλ`.
- `Collapse.InjExt (Xext : isExt X)` (`src/V/Collapse.lagda.md:220`)
  turns that into `π-inj` (`:277`) and `π∈-bwd` (`:282`).

**I DID NOT BUILD IT AND I DO NOT PRICE IT.** One reason to be careful:
`π∈-bwd` needs BOTH endpoints inside `M`
(`src/V/Collapse.lagda.md:282-283`), and `isTransV y` quantifies over
members of members of `y`, which need not be in `M`. So the route is
visible but it is not obviously short. This is the next question, not
this task's answer.

## 5. THE SWEEP (C-42), RUN THOUGH NO REFUTATION LANDED

C-42 fires on a refutation. **No refutation landed here**, so the law
does not bite. I ran the sweep anyway, because the mismatch in section 4
is a SHAPE and the next brief needs the count.

**The `levelIn` hypothesis occurs at FOUR live sites in `src/`, and ALL
FOUR carry `IsOrd` on the RANGE side:**

- `src/L/BoundedSubset.lagda.md:917` (`module Condense`)
- `src/L/BoundedSubset.lagda.md:1671`
- `src/L/StageBound.lagda.md:80`
- `src/L/StageBound.lagda.md:106`

Its companion `cover` sits beside each of them (`:919`, `:1673`, `:82`,
`:108`) and each one demands `IsOrd γ` at a `γ ∈ˢ ...C.πX`, again on the
range side. **So the range-side and hull-side gap is not local to
`:917`.** Any consumer that takes the ordinal keystone through 647's step
2 meets it. I did not price a cure. The count is the deliverable.

## 6. RUNS, EVERY NUMBER

Caliber `-A64m -I0 -M2g`, set on the pane by the program and untouched
here. ONE Agda process at a time, from the repository root, warm `src/`
cache. The `LJ-1-649` interfaces were deleted before every forced
recheck.

**The floor**, `runs/FLOOR.agda.txt`, red by design (one hole):

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/floor-1.out` | 2.80 | 460,095,488 | 42 |
| `runs/floor-2.out` | 3.22 | 358,825,984 | 42 |
| `runs/floor-3.out` | 2.84 | 361,676,800 | 42 |

Median wall **2.84 s**, median peak RSS **361,676,800 bytes**.

**W3, the decisive miniature**, `runs/W3.agda`, green, 49 non-blank
non-comment lines:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/w3-1.out` | 2.47 | 476,266,496 | 0 |
| `runs/w3-2.out` | 2.37 | 476,282,880 | 0 |
| `runs/w3-3.out` | 2.56 | 476,250,112 | 0 |

Median wall **2.47 s**, median peak RSS **476,266,496 bytes**. `w3-1` is
the FIRST run of the assembly and it was green on the first attempt.

**The delivered probe**, `Probe649.agda`, three forced rechecks:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/p-2.out` | 3.01 | 507,527,168 | 0 |
| `runs/p-3.out` | 2.61 | 507,527,168 | 0 |
| `runs/p-4.out` | 2.39 | 507,510,784 | 0 |

Median wall **2.61 s**, median peak RSS **507,527,168 bytes**.
`runs/p-1.out` (3.85 s, 489,472,000 bytes, exit 0) is the first run and is
not one of the three. `runs/p-final.out` (3.15 s, 507,527,168 bytes,
exit 0) is the delivered bytes after I corrected the `file:line`
citations in the comments.

**The two red slices**, both `.agda.txt`, both by design:

| run | wall s | peak RSS bytes | exit | what it shows |
|---|---|---|---|---|
| `runs/no-fifth-1.out` | 2.60 | 456,130,560 | 42 | ONE hole, at the `IsOrd` slot |
| `runs/no-fifth-odelta-1.out` | 2.29 | 454,950,912 | 42 | `[UnequalTerms] y != δ` |

**The meters:**

- `runs/meter-obligation.out`: `pass exit=0 2.59 s`,
  `0 UNRESOLVED of 1`, `probe_red=False`.
- `runs/meter-names.out`: ten names, `0 UNRESOLVED of 10`, 5.47 s,
  `probe_red=False`.

This worktree has no `.venv`. The meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.

**Against the brief's estimate.** The brief priced W3 at "40 to 100
lines". The decisive miniature is **49 non-blank non-comment lines** and
the assembly term inside it is **9**. The delivered probe is 117
non-blank non-comment lines over 276 total, and the extra is the three
alternative routes and the two named types, not the assembly.

## 7. WHAT THE NEXT BRIEF NEEDS

**`[LJ-1.646]` IS NOW WORTH MORE THAN IT WAS, AND THE QUESTION HAS
CHANGED.** The queue plans 646 as `lset-code-ord`, ordinal-conditioned,
because `Lset-only` (`src/L/Hierarchy.lagda.md:334-335`) wants `IsOrd` on
the argument slot. Section 4 measures what that condition costs
downstream: one extra unbuilt fact, `PiReflectsOrd`, at every consumer
that carries ordinality on the range side, and section 5 counts four such
sites. **If the un-ordinal `lset-code` is reachable at any price, it is
worth that price**, because it deletes the fifth fact from four consumers
at once. If it is not reachable, `PiReflectsOrd` is the next task, and
section 4.1 names the two tree facts it would start from.

**`[LJ-1.648]` AND `[LJ-1.650]` SHOULD TAKE `pix-closed-op`, NOT REPROVE
IT.** It is generic in `F`, `P` and `Q` (`Probe649.agda:124-139`). Clause
(iii)'s Commute and clause (ii)'s CodedCover are both range-closure
statements of the same shape. Each one supplies its own `F` and its own
`reflect`, and `reflect` is `λ _ _ _ → tt*` whenever its side condition
is trivial.

**STEP 3 SHOULD LEAVE THE `levelIn` DECOMPOSITION.** After this task,
`levelIn` reduces to exactly TWO objects, not four and not three:

- step 2, `HullClosedLset`, which `[LJ-1.647]` reduced to the keystone
- step 4, `πCommuteLset`, on which `[LJ-1.477]` closed NO-GO at the join
  of the two computation laws (`agents/tasks/LJ-1-477/lj-1.477-report.md:273-275`)

**Step 4 is the campaign's real stop now.** Step 2 has a route and a
sibling working it. Step 4 has a NO-GO from `[LJ-1.477]` that names the
join precisely and has not been reattempted. `[LJ-1.477]` also recorded
that it "did not prove the type false"
(`agents/tasks/LJ-1-477/lj-1.477-report.md:188`), and D-10 says a
recorded residue names a TARGET that can itself be false. **Price step
4's truth before pricing its proof.** `Probe649.agda:237-245` shows that
an ORDINAL-CONDITIONED step 4 is enough for this consumer, so a step 4
that is only true at ordinals still closes `levelIn`, and that is a
cheaper target than the one `[LJ-1.477]` attacked.

**What this task does NOT settle.** It does not inhabit step 2, step 3 or
step 4. It does not inhabit `PiReflectsOrd`. It does not touch `cover`.
It does not edit `src/`. It does not refute anything.

## GATES

I ran every LINT-class gate of `make check` individually, as the Boundary
tells a worker to do while the work is live. All clean:

| gate | result |
|---|---|
| `scripts/gate/lint-prose.py --check` | clean, no output |
| `scripts/gate/lint-agda.py --check` | clean, no output |
| `scripts/gate/check-probes.py --check` | `clean (9810 tracked files, no probe outside agents/tasks/ and no generated file)` |
| `scripts/pod/check-closure.py --check closure` | `clean (103 masters; closure, archive)` |
| `scripts/gate/check-fences.py --check` | `clean (103 masters, run threshold 3)` |
| `scripts/gate/check-rule-ids.py` | `clean (56 files, 166 lessons, 68 decisions, dev/rules.toml)` |
| `scripts/site/weave-i18n.py --check` | clean, no output |
| `scripts/measure/ledger.py --check` | `declaration clean; standing 34,149 lines measured over 101 masters` |
| `scripts/gate/check-glossary.py --check` | clean, no output |
| `scripts/pod/check-spec-surface.py --check` | `clean (8 surface file(s), 202 declaration(s), 7 guarded rule home(s), 508 in-fence lines)` |
| `reuse lint` | `compliant with version 3.3 of the REUSE Specification` |

**I DID NOT RUN `make typecheck`.** It is the whole-tree Agda run at a
different caliber, and the standing coder clause says start ONE Agda
process and no more. This task adds no `src/` file and edits none, so the
tree it would check is unchanged. Every Agda run in section 6 is one
process under the pane's own caliber.

I added no `SPDX-*` header, committed nothing, pushed nothing and added
no dependency. The working tree carries exactly the files in the FILES
section below and nothing else.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ.**
  `archive/dev/LJ-dispatch-index.md:236` reads
  "| LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |".
  I read the `levelIn` rows to confirm that no earlier dispatch had
  composed the four steps. None had.
- `archive/dev/JOURNAL.md`: **not read.** It holds zero occurrences of
  `levelIn`. The four-step decomposition is `[LJ-1.462]`'s and post-dates
  the journal.
- `archive/dev/JOURNAL-archived.md`: **not read.** Same reason. Zero
  occurrences of `levelIn`.
- `archive/dev/ORCHESTRATION.md`: **declined.** It is the archived loop
  document. It carries no mathematics and zero occurrences of both
  `levelIn` and `collapse`.
- `dev/ARCHIVE.md`: **declined.** It records which MODULES left the tree
  and why. This task retires no module and creates no `src/` file, so
  clause W4 does not fire. Zero occurrences of `levelIn`.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it grounds section 4.1.**
  `dev/literature/devlin-II5.md:200` reads
  "relation: a unique π, a unique transitive M, an isomorphism".
  This is the source for the claim that the collapse of an extensional
  set REFLECTS structure and not only preserves it, which is what
  `PiReflectsOrd` needs.
- `dev/literature/truncation-and-selection.md`: **READ.**
  `dev/literature/truncation-and-selection.md:92` reads
  "HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`."
  This is why the `PT.rec` in `pix-closed-op` is free: the goal
  `⟨ F δ ∈ˢ C.πX ⟩` is a mere proposition, so no choice principle enters.
- `dev/literature/digest.md`: **not used.** It is the reading index. Its
  Devlin II.5 entry points at `devlin-II5.md`, which I read directly.
- `dev/literature/terms-2026-08.md`: **declined.** It is a terminology
  file for translation. This task adds no term and writes no prose for
  `docs/`.
- `dev/literature/geology.md`: **declined.** Set-theoretic geology is not
  on either trophy path and it says nothing about the Mostowski collapse
  of a definable hull.

## FILES

- `agents/tasks/LJ-1-649/Probe649.agda`, the delivered probe, GREEN
- `agents/tasks/LJ-1-649/lj-1.649-report.md`, this file
- `agents/tasks/LJ-1-649/runs/run.sh`, the run harness
- `agents/tasks/LJ-1-649/runs/W3.agda`, the decisive miniature, GREEN
- `agents/tasks/LJ-1-649/runs/FLOOR.agda.txt`, the floor, red by design
- `agents/tasks/LJ-1-649/runs/NO-FIFTH.agda.txt`, red by design
- `agents/tasks/LJ-1-649/runs/NO-FIFTH-ODELTA.agda.txt`, red by design
- `agents/tasks/LJ-1-649/runs/*.out`, every run above

No `review-of-*.md` is written. This task is a GO and it states no
NO-GO.
