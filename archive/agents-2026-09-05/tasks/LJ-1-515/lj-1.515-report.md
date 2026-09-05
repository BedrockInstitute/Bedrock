# LJ-1.515 report: the replacement rank, on the re-based order

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. The recursion terminates on the re-based order, the obligation is
delivered, and the whole file is green.**
`agents/tasks/LJ-1-515/Probe515.agda`, exit 0, caliber `-A64m -I0 -M8g`, one
Agda process. `runs/full-1.out` to `runs/full-3.out`.

The obligation is at `Probe515.agda:112-113`:

    swo-rank′ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ

**THE PADDING IS DELETED.** `predAt` and `pred`
(`agents/tasks/LJ-1-490/Probe490.agda:129-138`) do not occur in this file, and
no term replaces them. The index of `boundingOrd` is `Pred a`, the
predecessors (`Probe515.agda:90-91`), and `ih` is applied at its own proof and
at nothing else (`Probe515.agda:93-97`).

**AND THE RANK IS `∅` AT A MINIMAL ELEMENT.** That is the property
`[LJ-1.497]`'s refutation demands, and it is proved, not stated:
`swo-rank′-∅` at `Probe515.agda:218-222`. Read the section below with that
name for the type and for its converse.

I did not attempt the adequacy. I did not touch `rankFo`. I did not
postulate, and I did not weaken the rank to a bound. Nothing landed in `src/`.
I did not write a `review-of-*.md`, because this is not a stop.

## D-10, BEFORE ANY AGDA

The brief asks two questions before any Agda: what the `boundingOrd` line
reads today and what it must read instead, and whether the recursion
terminates on the re-based order. Both were settled from declarations.

**1. WHAT THE LINE READS TODAY.** `agents/tasks/LJ-1-490/Probe490.agda:145`:

    bnd = boundingOrd A (λ x → pred a ih x .fst) (λ x → pred a ih x .snd)

The index is `A`, the WHOLE carrier. `pred` pads it: at an `x` that is not
below `a`, `predAt` returns `∅ , ∅-ord`
(`agents/tasks/LJ-1-490/Probe490.agda:134-135`).

**2. WHAT IT MUST READ INSTEAD.** `Probe515.agda:95-97`:

    bnd = boundingOrd (Pred a) (λ p → ih (p .fst) (p .snd) .fst)
                               (λ p → ih (p .fst) (p .snd) .snd)

with `Pred a = Σ[ x ∈ A ] (x <∙ a)` (`Probe515.agda:90-91`). This is
`[LJ-1.513]`'s `viaRankFamily` (`agents/tasks/LJ-1-513/Probe513.agda:190-196`)
with `ih` computed in place of taken as a hypothesis.

**3. WHY THE PADDING IS THE CAUSE OF THE REFUTATION, NOT AN ACCIDENT OF IT.**
`[LJ-1.497]` states the mechanism at `agents/tasks/LJ-1-497/Probe497.agda:125`,
which reads "because `boundingOrd` is taken over the WHOLE carrier `A` and the"
(the sentence ends "point `a` itself contributes ∅ to that family", line 126).
`pred-self` (`agents/tasks/LJ-1-497/Probe497.agda:117-122`) proves
`pred a ih a .fst ≡ ∅`, because trichotomy at `a` against `a` is neither `lt`
nor `gt`. So `a` is always in the index, always contributes `∅`, and
`swo-rank` therefore always has `∅` as a member
(`agents/tasks/LJ-1-497/Probe497.agda:134-135`). **Delete the index entry for
`a` and the term that supplies its value has nothing left to do.** That is why
the cure and the padding are one change and not two.

**4. DOES THE RECURSION TERMINATE ON THE RE-BASED ORDER? YES, AND THE REASON
IS THAT THE RE-BASING DOES NOT TOUCH THE DESCENT.** `go` recurses on the
accessibility argument, not on the order: `go a (acc rs) = step a (λ x h → go
x (rs x h))` (`Probe515.agda:99-100`), and `rs x h` is a constructor argument
of `acc rs`, so it is structurally smaller whatever `_<∙_` is. The index of
`boundingOrd` is an ARGUMENT of `step` and is not where the recursion
descends. `[LJ-1.497]` already had this exact `go` and `step` shape
(`agents/tasks/LJ-1-497/Probe497.agda:104-105`); only the index changes.

**THAT ANALYSIS PREDICTED A GO AND I STILL MEASURED IT**, because a prediction
about the termination checker is not a measurement of it (`AGENTS.md:45`).
Section 1 below is that measurement.

## 1. W3, TERMINATION, FIRST

**GO. The recursion on the re-based order is accepted, on the first attempt.**
The brief asked for the recursion alone with `swo-rank′-ord` omitted. That
slice is 77 lines and is kept verbatim at
`agents/tasks/LJ-1-515/runs/w3-slice.agda.txt`. It carries only `Rank′` with
`RankAt`, `Pred`, `step`, `go` and `swo-rank′`, and the top-level
`swo-rank′`.

Caliber `-A64m -I0 -M8g`, set on the pane and untouched. One Agda process. The
interface `_build/2.8.0/agda/agents/tasks/LJ-1-515/Probe515.agdai` was deleted
before every run.

- `runs/w3-1.out` 1.47 s, 249118720 bytes, exit 0
- `runs/w3-2.out` 1.16 s, 282853376 bytes, exit 0
- `runs/w3-3.out` 1.14 s, 282853376 bytes, exit 0

**W3 median wall 1.16 s. Peak RSS 282853376 bytes.** No heap event. The first
run is the slow one and carries the cold cost of the run harness, not of the
recursion.

ESTIMATE for W3 was about 35 lines and under 60 seconds. **MEASURED 77 lines
and 1.16 s.** The line estimate is off by 2.2x and the reason is the same one
`[LJ-1.513]` recorded for its own W3
(`agents/tasks/LJ-1-513/lj-1.513-report.md:105-109`). The 77 lines are 39
comment, 12 blank and 26 code, and 10 of the 26 are the pragma, the module
header and the imports that name `SWO`, `IsOrd`, `boundingOrd`, `V` and
`Acc`. **The Agda that answers W3 is 16 lines.** The comment is large because
it carries the old `boundingOrd` line and the new one side by side, which is
what D-10 asked for.

**A NOTE ON THE ESTIMATE'S BASIS, WHICH WAS SOUND.** The brief said not to
fund W3 against `[LJ-1.513]`'s numbers, because that formed a set and this
runs a recursion. The two came out at the same wall time to two figures
(1.09 s there, 1.16 s here). **That agreement is not evidence that the brief
was wrong to separate them.** Both files are small and both are dominated by
reading the interfaces of `L.Ordinal` and its dependencies, which neither task
changes. Nothing may be funded against either number.

## 2. THE OBLIGATION

`swo-rank′` is `Probe515.agda:112-113` and its content is `module Rank′`,
`Probe515.agda:81-106`, 26 lines of which 17 are code, 3 comment and 6 blank.

    swo-rank′     : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ
    swo-rank′-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
                  → IsOrd (swo-rank′ w a)

`swo-rank′-ord` (`Probe515.agda:115-117`) costs one line, because `go` returns
the ordinal and its proof as one pair.

**WHAT THE SHAPE RESISTED, AND THE NEXT BRIEF SHOULD KNOW IT.** One thing, and
it is a naming decision that the next brief must keep.

`[LJ-1.490]` puts the `boundingOrd` call in a `where` block of `go`
(`agents/tasks/LJ-1-490/Probe490.agda:141-145`). **A `where`-bound name cannot
be spoken from outside its parent, so no law about that bounding ordinal can
be stated.** `[LJ-1.497]` had already hit this and lifted the call into a
named `step` with a companion `step-mem`
(`agents/tasks/LJ-1-497/Probe497.agda:92-102`). I kept that shape and the same
two names (`Probe515.agda:93-97,185-190`). **Section 3 is only writable
because of it.** A future edit that inlines `step` back into `go` deletes the
`∅` law and the membership law with it.

Nothing else resisted. The file was green at the first attempt in both the W3
slice and the full form.

## IS IT `∅` AT A MINIMAL ELEMENT

**YES, AND IT IS PROVED. The type is `Probe515.agda:218-222`:**

    swo-rank′-∅ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
                → ((x : A) → SWO._<∙_ w x a → Empty.⊥)
                → swo-rank′ w a ≡ ∅

That is the type `[LJ-1.513]` named
(`agents/tasks/LJ-1-513/lj-1.513-report.md:304-306`), which is
`[LJ-1.497]`'s `swo-rank′-least`
(`agents/tasks/LJ-1-497/lj-1.497-report.md:199-201`) with the minimality
hypothesis written out. It has a term.

**THE PROOF IS ABOUT `boundingOrd` AND NOT ABOUT THE RANK.** The general fact
is `boundingOrd-empty` (`Probe515.agda:134-155`):

    boundingOrd-empty :
        (X : Type ℓ) (f : X → V ℓ) (hf : (x : X) → IsOrd (f x))
      → (X → Empty.⊥)
      → boundingOrd X f hf .fst ≡ ∅

It is `extensionality` on the two directions. Out: a member of the bounding
ordinal gives, through `union-ax` then `∈∈ₛ`, an element of the index, and the
index is empty. In: `∅-empty`. `[LJ-1.513]` called this "plausible on the
shape, because `boundingOrd` over an empty index unions an empty family"
(`agents/tasks/LJ-1-513/lj-1.513-report.md:311-312`) and said plausible is not
measured. **It is now measured and the shape held.** The chain is
`step-∅` (`Probe515.agda:161-168`), `go-∅` (`Probe515.agda:170-173`),
`rank-∅` (`Probe515.agda:175-176`).

**THE `∅` LAW ALONE IS NOT ENOUGH AND I DID NOT STOP AT IT.** The constant
function `λ _ → ∅` also satisfies it, and that is not a rank. So the file
also delivers the converse (`Probe515.agda:224-231`):

    swo-rank′-mem : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a x : A)
                  → SWO._<∙_ w x a → swo-rank′ w x ∈ᵗ swo-rank′ w a

    swo-rank′-∅-only : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a x : A)
                     → SWO._<∙_ w x a → swo-rank′ w a ≡ ∅ → Empty.⊥

`swo-rank′-mem` is `swo-rank-mono` at the new rank. **That name is not new
and I checked where it lives before writing mine.** `[LJ-1.416]` delivered it
for the OLD rank at `agents/tasks/LJ-1-416/Probe416.agda:111-113`, and
`[LJ-1.490]` chose not to rebuild it because `boundingOrd` did not need it
(`agents/tasks/LJ-1-490/Probe490.agda:119-120`).

Both versions cost `isPropAcc` (`Cubical/Induction/WellFounded.agda:19`),
because the value at the predecessor is computed from the accessibility proof
`go` was handed and the statement is about the one `wf∙` gives. `Acc` is a
proposition, so the two agree: `go-irr` (`Probe515.agda:193-194`) and
`agents/tasks/LJ-1-416/Probe416.agda:94` are the same `cong`.

**THE DIFFERENCE IS WHAT ELSE THE PROOF NEEDS, AND THE NEXT BRIEF SHOULD READ
IT.** `[LJ-1.416]` needs `fromTri`
(`agents/tasks/LJ-1-416/Probe416.agda:91-98`), a three-case split that kills
the `eq` branch with `irr∙` and the `gt` branch with `trans∙` and `irr∙`,
because the padded family is read at a point whose relation to `a` is
unknown. **Mine has no such split**: the index carries the proof `x <∙ a`, so
there is no case to kill and neither `irr∙` nor `trans∙` appears
(`Probe515.agda:196-204`).

**I DO NOT CLAIM A SIZE WIN.** Both in-module chains measure exactly 18
non-blank non-comment lines: `Probe515.agda:185-207` and
`agents/tasks/LJ-1-416/Probe416.agda:80-98`. The saving is in the dependency
and not in the count, and I did not measure a time difference for it.

**READ THE TWO TOGETHER: THE RANK IS `∅` AT A MINIMAL ELEMENT AND NOWHERE
ELSE.** That is the exact contradictory of what `[LJ-1.497]` measured of
`swo-rank`, which has `∅` as a member at EVERY point
(`agents/tasks/LJ-1-497/Probe497.agda:134-135`), and the only difference
between the two files at that line is the index of `boundingOrd`.

**AND THE LAW IS NOT VACUOUS AT THE SITE.** Section 4 rebuilds
`[LJ-1.513]`'s re-based ordinal order and shows that an index of `∅` inside an
ordinal has no predecessor there, so the hypothesis is discharged by a real
element and not only by an empty carrier:

    ∅-min      : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ≡ ∅ → (x : ⟪ α ⟫) → x ≺ₛ m → Empty.⊥
    rank-at-∅  : (m : ⟪ α ⟫) → ⟪ α ⟫↪ m ≡ ∅ → swo-rank′ w m ≡ ∅

`Probe515.agda:301-307`.

**ONE LIMIT, STATED.** `∅-min` needs an index of `∅` to EXIST in `α`. I did
not prove that a non-empty ordinal has one, and this file does not claim it.
The literature line I read says that under trichotomy a minimal element is a
least element and is unique, so at most one point of any `SWO` can satisfy the
hypothesis (`dev/literature/truncation-and-selection.md:118`). **That is a
reading of a source and not a term in this file.**

## 3. AT THE RE-BASED ORDINAL ORDER

`module OrdSWO∈ₛ` (`Probe515.agda:244-286`) is `[LJ-1.513]`'s order rebuilt
verbatim (`agents/tasks/LJ-1-513/Probe513.agda:113-155`). I changed nothing in
it. `module AtOrd` (`Probe515.agda:288-307`) adds three things and no more:

- `pack` (`Probe515.agda:296-297`). This is `[LJ-1.490]`'s `Bound.pack`
  (`agents/tasks/LJ-1-490/Probe490.agda:213`) with `swo-rank′` in place of
  `swo-rank`. It typechecks, so the replacement rank is accepted where the old
  one was consumed. **The bound itself is NOT rebuilt.** That is
  `[LJ-1.513]`'s item 3 (`agents/tasks/LJ-1-513/lj-1.513-report.md:314-317`)
  and it is not this task.
- `∅-min` and `rank-at-∅`, described above.

## W2, ANSWERED

**The brief did not state clause W2, and W2 says the brief must.** I answer it
anyway.

Sections 1 to 3 of the probe are written at the generic carrier. `Rank′`
(`Probe515.agda:81`), `Rank′∅` (`Probe515.agda:157`) and every top-level name
take `{A : Type ℓ} (w : SWO {ℓc = ℓ} A)` and nothing else.
`boundingOrd-empty` (`Probe515.agda:134`) is generic in the index type and
mentions no rank at all. The one fixed thing in the file is section 4, which
instantiates at the ordinal order, and instantiation is what W2 asks for.

## PRICES

Full file, 307 lines. Caliber `-A64m -I0 -M8g`, one Agda process, interface
deleted before each run.

- `runs/full-1.out` 1.85 s, 296304640 bytes, exit 0
- `runs/full-2.out` 1.81 s, 296337408 bytes, exit 0
- `runs/full-3.out` 1.76 s, 296288256 bytes, exit 0

**Full-file median wall 1.81 s. Peak RSS 296337408 bytes.** No heap event.

ESTIMATE for the Agda was about 180 lines, of which about 45 the obligation.
**MEASURED 307 lines, of which the obligation is 26** (`Probe515.agda:81-106`).
The obligation came in at 58 percent of the estimate and the file at 171
percent of it. The overshoot is three parts, and none of them is the
obligation:

- section 4, `Probe515.agda:236-307`, 72 lines, of which 43 are
  `[LJ-1.513]`'s order rebuilt. The brief did not price it because it asked
  only for the rank.
- the two extra laws, `swo-rank′-mem` and `swo-rank′-∅-only`,
  `Probe515.agda:185-214,224-231`, 38 lines. I wrote them because the required
  report section is answerable by the constant `∅` function without them.
- comments, 103 non-blank lines across the file, which carry the `file:line`
  of every predecessor claim this task rests on. The 307 lines are 103
  comment, 49 blank and 155 code.

**THE RATIO BAR HAS NO DIVISOR ON THIS TASK.** The write scope is a raw
`.agda` probe, a report and `runs/`. No ` ```agda ` fence is created, so the
in-fence line count of the scope is 0 and the bar cannot fire. Nothing here is
evidence about what the bar would read if this rank moved into `src/`.

## GATES RUN

- `scripts/gate/check-probes.py`: "check-probes: clean (5362 tracked files, no
  probe outside agents/tasks/ and no generated file)", exit 0.
- `scripts/gate/lint-agda.py --check`: exit 0, no output.

I did not run `make check`, because it typechecks `src/Everything.lagda.md`
and I changed no file under `src/`.

## WHAT THIS EARNS, AND WHAT IT DOES NOT

**EARNED.** The counting leg has a rank that can be adequate. `[LJ-1.497]`
refuted the old one for one stated reason, and that reason is gone: the
replacement is `∅` at a minimal element (`Probe515.agda:218`) and is not `∅`
anywhere a predecessor exists (`Probe515.agda:228`).

**NOT EARNED, AND THE NEXT BRIEF MUST NOT READ IT AS EARNED.**

1. **The adequacy is not attempted.** `[LJ-1.497]` measured that it needs a
   SECOND hypothesis this task does not supply: `Q` read as the ∈-order on
   `a`, as a set of pairs (`agents/tasks/LJ-1-497/lj-1.497-report.md:211`).
   **A rank alone does not make the adequacy true**, and `[LJ-1.513]` said so
   (`agents/tasks/LJ-1-513/lj-1.513-report.md:319-325`).
2. **The bound is not rebuilt.** `[LJ-1.490]`'s `Bound`
   (`agents/tasks/LJ-1-490/Probe490.agda:211-230`) still reads `swo-rank`.
   `pack` shows the first line of it accepts the replacement. The remaining
   lines of `Bound`, and `rank-bound`, are not measured.
3. **`src/` is not measured.** Nothing landed there and I did not typecheck
   it. `[LJ-1.513]`'s C-42 count stands unchanged: all 16 importers of
   `L.WellOrder.Base` take `ℓₚ = ℓ-suc ℓ`
   (`agents/tasks/LJ-1-513/lj-1.513-report.md:253-263`). This file is the
   second instantiation at `ℓₚ = ℓ` in the repository and both are probes.
4. **No claim of rank DESCENT.** `swo-rank′-mem` is an ASCENT statement: the
   predecessor's rank is a member of the point's rank. A rank-descent claim
   was adversarially refuted once in this project's history
   (`archive/dev/JOURNAL-archived.md:3806`), so I name the direction I proved.
5. **`∅-min` needs an index of `∅` to exist.** See the limit stated above.

## C-42, THE SWEEP

C-42 makes the count come before the cure. `[LJ-1.497]` refuted at one site,
and the shape it refuted is "a `boundingOrd` whose index is a padded carrier".

**THE COUNT IS 6 LIVE SITES IN 4 FILES, AND EVERY ONE OF THEM IS A PROBE.**
`grep -rn "boundingOrd A " --include='*.agda' agents/` returns:

    agents/tasks/LJ-1-416/Probe416.agda:72
    agents/tasks/LJ-1-416/Probe416.agda:89
    agents/tasks/LJ-1-486/Probe486.agda:96
    agents/tasks/LJ-1-490/Probe490.agda:145
    agents/tasks/LJ-1-497/Probe497.agda:96
    agents/tasks/LJ-1-497/Probe497.agda:101

**MY FIRST COUNT WAS 2 AND IT WAS WRONG.** I had read only the two probes the
brief names. `[LJ-1.416]` and `[LJ-1.486]` carry the same shape and neither is
named in this brief.

All four files are the SAME rank rebuilt four times, and the evidence is that
each one also carries `predAt` and `pred`: 7 hits in `Probe416.agda`, 6 in
each of `Probe486.agda`, `Probe490.agda` and `Probe497.agda`. **So the six
sites are one shape and not six independent ones.**

**THE COUNT UNDER `src/` IS 0, AND THAT IS TWO SEPARATE GREPS.**
`grep -rn "swo-rank" --include='*.lagda.md' src/` returns nothing, and
`grep -rn "boundingOrd A " --include='*.lagda.md' src/` returns nothing. The
rank has never landed in the tree.

**TWO NEAR MISSES, NAMED SO THAT THE COUNT IS NOT MISREAD.**
`agents/tasks/LJ-1-417/Probe417.agda:83` reads
`pack = boundingOrd A swo-rank swo-rank-ord`. That index IS the whole carrier
and it is CORRECT there: it is the outer bound over every point's rank, the
same shape as `[LJ-1.490]`'s `Bound.pack`
(`agents/tasks/LJ-1-490/Probe490.agda:213`), and it has no `pred`.
`agents/tasks/LJ-1-515/Probe515.agda:62` matches the grep too and is the old
line quoted inside a comment, not a term.

So the cure has no site under `src/` to pay for. **That is a count and not a
dependency measurement**, and it says nothing about the 16 importers in item 3
above.

## WHAT I DID NOT DO

- No adequacy, and no edit to `rankFo`. AD12 gives this brief one obligation.
- No `postulate`, no hole, no `TERMINATING`, no weakened pragma. The file
  keeps `--cubical --safe --guardedness` (`Probe515.agda:1`).
- No weakening of the rank to a bound. `[LJ-1.475]` refused that.
- No change under `src/`, and no `src/` typecheck.
- No `GHCRTS` change. The caliber on the pane was `-A64m -I0 -M8g` at the
  first command and at the last.
- No commit and no push.
- No `review-of-*.md`. This is a GO and not a stop.
- No `dev/ARCHIVE.md` row. See the archive section below for why none is owed.

## ARCHIVE USED

- `dev/ARCHIVE.md`. **READ.** `dev/ARCHIVE.md:3` reads "The registry of
  Bedrock's retired modules. One entry per module, written at". I read it to
  settle whether clause W4 owes a row for this task. **It does not.** W4 is
  module-granular, and `predAt` and `pred` are fragments inside a probe, not
  modules; no module left the tree, and `agents/tasks/LJ-1-490/Probe490.agda`
  is untouched and still carries them.
- `archive/dev/LJ-dispatch-index.md`. **READ.**
  `archive/dev/LJ-dispatch-index.md:255` reads "| LJ-1.179 | DD25 review of
  LJ-1.169's rank NO-GO | OVERTURNED: A FIXED-SHAPE NO-GO |". I searched the
  index for prior rank verdicts before writing, to check that no earlier
  dispatch had already ruled this shape dead. That row is the opposite case: a
  rank NO-GO that was overturned because it was right for the coding it
  measured and wrong for the tree. It is a caution about the scope of a
  refutation and it matches C-42.
- `archive/dev/JOURNAL-archived.md`. **READ.**
  `archive/dev/JOURNAL-archived.md:3806` reads "adversarially checked; two
  refuted (the rank-descent claim; the". It is why item 4 of the
  not-earned list names the direction of `swo-rank′-mem` instead of calling it
  a descent.
- `archive/dev/JOURNAL.md`. **NOT READ, declined.** I grepped it for `rank`
  and the one hit (line 317) is about ranking three candidate cures, not about
  a rank function. It has nothing this task needs.
- `archive/dev/ORCHESTRATION.md`. **NOT READ, declined.** It is the archived
  loop document. This task is one dispatch inside the program and does not
  touch how the loop runs.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ.**
  `dev/literature/truncation-and-selection.md:118` reads "But trichotomy
  implies that any minimal element is a least element." It is the source of
  the stated limit under `## IS IT `∅` AT A MINIMAL ELEMENT`: an `SWO` carries
  `tri∙` (`src/L/WellOrder/Base.lagda.md:104`), so at most one point can
  satisfy `swo-rank′-∅`'s hypothesis. **I did not formalize that and the file
  does not claim it.**
- `dev/literature/devlin-II5.md`. **READ, and it did not decide anything.**
  `dev/literature/devlin-II5.md:445` reads "statement is π(x) ≤_L x, the
  collapse never raises the <_L-rank." Devlin's rank there is the `<_L`-rank
  of the constructible order, and the claim is about a collapse map. This
  task's rank is the ∈-rank of a well-order on one ordinal's carrier, and its
  question is which index a bounding ordinal takes. **It does not transfer**
  (`AGENTS.md:45`).
- `dev/literature/digest.md`. **NOT READ, declined.** The digest is the
  cross-source summary of the fine-structure sources. This task's two
  questions, termination and the empty case, were answered from the tree and
  from the one source above.
- `dev/literature/geology.md`. **NOT READ, declined.** Set-theoretic geology
  is not on the counting leg's route.
- `dev/literature/terms-2026-08.md`. **NOT READ, declined.** I grepped it and
  its hits are the Chinese rendering of "initial segment". This task mints no
  term and adds no `dev/glossary.toml` entry, and clause W5 forbids choosing
  one.
