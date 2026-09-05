# review-of-below-closed: a STATED NO-GO, the fourth supply is not a term

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.713
obligation: agents/tasks/LJ-1-713/Probe713.agda::below-closed
verdict: **NO-GO on `below-closed` as briefed.** The statement is not
false and the three lower arrows are green at one frame. The stop is
premise 4: the brief counts `CompletenessFrom` as delivered supply,
and the tree holds it only as a named TYPE whose inhabitation is a
separate, open, NO-GO'd obligation. The critic reads this file. It
does not close the task.

## 1. THE PREMISE THE TREE CANNOT SUPPORT

Premise 4 of the brief says the assembly above `Below` is green and
cites `agents/tasks/LJ-1-679/Probe679.agda:94`. That line names a
type, not a term:

- `Probe679.agda:94-95`: `CompletenessFrom : Type (ℓ-suc ℓ)` and
  `CompletenessFrom = SameHyp → HierInStage → Completeness`.
- `Probe679.agda:97`: "CompletenessFrom is a named supplier, not the
  obligation."

A type cannot be applied. Measured at this frame: the floor run of
the full composition stands in the tree as
`agents/tasks/LJ-1-713/runs/floor-1.out:30-33`:

```
Probe713.agda:87.5-23: error: [CannotApply]
Expression used as function but does not have function type:
  expr: A.CompletenessFrom
  type: Type (ℓ-suc ℓ)
```

The one error in that run is this application. Every other part of
the composition, including the hoisted `[LJ-1.709]` delivery checked
against `A.CompletenessFrom`'s first input, was accepted in the same
run.

## 2. THE CAMPAIGN ALREADY FUNDS THIS ARROW, AND IT RETURNED NO-GO

The inhabitation of `CompletenessFrom` is `[LJ-1.700]`'s obligation,
not a settled supply:

- `agents/tasks/LJ-1-700/LJ-1.700.md:12`: "completeness-from-hier :
  <Completeness at matrix₃ via [LJ-1.679]'s CompletenessFrom, taking
  SameHyp and HierInStage as HYPOTHESES>".
- The task closed NO-GO on the closed term
  (`agents/tasks/LJ-1-700/Probe700.agda:76-79`: the name is not
  defined; the two hypotheses "Neither supplies an ambient matrix₃
  reading at a stage member, which BoundInStage spends").
- The critic upheld the outcome:
  `agents/tasks/LJ-1-700/review-of-LJ-1-700-1.md:167` ("Upheld. The
  predecessor's NO-GO is correct on its own outcome.") and `:174-175`
  ("A GO would need a green term; nothing green exists.").
- The queue still carries the entry (`dev/pod/queue.toml:6990-6994`).

The standing coder clause says a NO-GO predecessor's type is not to
be inhabited from a brief's say-so. Premise 4 asks this task to
consume that arrow as if it existed. It does not exist.

## 3. WHAT THIS TASK MEASURED, SO THE NEXT BRIEF PAYS FOR ARROWS, NOT FOR DOUBTS

All green, one frame, `runs/p-1.out` EXIT 0 at 35.17 s warm, peak
1,130,430,464 B (53 percent of the 2 GiB wide cap), recheck
`runs/p-2.out` EXIT 0 at 2.70 s:

1. `same-hyp-of` (`Probe713.agda:89-96`): `[LJ-1.709]`'s delivered
   telescope, hoisted over `{n} w b γ`, produces `[LJ-1.679]`'s
   unconditional `SameHyp`. The floor run forced this against
   `CompletenessFrom`'s first input and accepted it. The 709-to-679
   carrier question is closed: one argument serves.
2. `below-of` (`Probe713.agda:102-107`): `[LJ-1.706]`'s
   `below-from-place` (`Probe706.agda:78`) output checked against
   `[LJ-1.697]`'s `Below` spelling inside `At`. The two `step`
   iterators (693's, in `P706.Below`; W3's, in `P697.At.Below`) are
   convertible here, as `S = V ℓ` by record literal
   (`src/V/Hierarchy.lagda.md:78-84`).
3. `hier-of` (`Probe713.agda:110-115`): the two rows, through
   `from-below` (`Probe697.agda:81`), to `A.HierInStage`.
4. `below-closed-via` (`Probe713.agda:120-130`): the whole chain with
   the fourth arrow taken as the explicit hypothesis it is,
   `(cf : A.CompletenessFrom)`. The body is one application:
   `cf (same-hyp-of …) (hier-of …)`.

## 4. WHAT GO WOULD NEED

One term: an inhabitant of `A.CompletenessFrom`, which is
`[LJ-1.700]`'s open obligation. Its recorded state: three runs of its
probe died at the wide cap (`review-of-LJ-1-700-1.md:121-125`), the
wall is localized to three definitions with an untested cure ("an
explicit codomain on `hier-at-code` is the first move nobody has
tested", `review-of-LJ-1-700-1.md:182-183`), and the floor's positive
fact is on record: the obligation TYPE is expressible at the frame
against a hole (`review-of-LJ-1-700-1.md:151-153`). This task's own
shape already applies the explicit-codomain cure at its own sites and
measures green (`Probe713.agda:110-115`, runs above); that is a
measurement at this frame, not a transfer of the cure.

## 5. CORRECTED BILL LIST FOR THE CHAIN (D-10)

The brief's GO row says two bills. Measured today the chain to
`Completeness` carries three:

1. `Bound-in-tower`: `[LJ-1.711]`, dispatched.
2. the identification of the carve (re-bounded per
   `[LJ-1.706]`'s corrected target): `[LJ-1.712]`, dispatched.
3. `A.CompletenessFrom`'s inhabitation: `[LJ-1.700]`, open, NO-GO
   upheld, cure named and untested.

Nothing here refutes the mathematics of premise 4. C-42 applies: the
`[CannotApply]` is an elaboration fact about a missing term, not a
measurement that `SameHyp` and `HierInStage` cannot reach
`BoundInStage`. That question stays open exactly where `[LJ-1.700]`
left it.
