# review-of-bound-in-stage-at-empty: NO-GO

reviewer: coder (LJ-1.746-SPLIT, the dispatch that owns the term)
statement: `bound-in-stage-at-empty` at
`agents/tasks/LJ-1-746-SPLIT/Probe746Split.agda.txt:127-137` (the
drafted shape; the file is named `.agda.txt` because it cannot
typecheck, this review is why)
verdict: **NO-GO at the wide caliber in this dispatch's shapes, with a
measured SPLIT VERDICT inside candidate 1: the spelling module the
brief named is GREEN, and the assembly that consumes it is fatal.**

The brief's W3 question was: does one shared split-spelling of the row
types make `Amb4` convert at wide?  **Answer: NO**, measured at four
independent sites, all one Agda process at a time, pane caliber
`-A64m -I0 -M2g` untouched, in this worktree with the cone warmed
bottom-up:

| probe | what it prices | result |
|---|---|---|
| `runs/pt6.out` | `runs/PT.agda`: the split-spelled row types named once at the named proofs `pA`/`pS`, and the rows carried into them by `erase-cong` -- the brief's own candidate-1 moves, WITHOUT the assembly | **rc 0, 90.92 s**, 1.14 GB peak |
| `runs/pt2-run3.out` | `runs/PT2.agda.txt`: the assembly `∣ n 0 , (mem0 , approx-split gen , step-split gen) ∣₁ : GraphAt` consuming the green spelling module | **rc 251, 351.07 s, `Heap exhausted` at the 2 g cap**, 2.20 GB peak |
| `runs/m0.out` | `runs/M0.agda.txt`: 746's b12 shape re-run here, rows as variables at the inline split spellings | **rc 251, 285.23 s, heap exhausted**, 2.39 GB peak |
| `runs/pa.out` | `runs/PA.agda.txt`: ONE conversion, isolated -- the split-spelled approx reading against its own identical spelling | **rc 251, 276.71 s, heap exhausted**, 2.51 GB peak |
| `runs/pm3.out` | `runs/PM.agda.txt`: candidate 2's one-level mirror bridge, `GraphMirror ≡ GraphAt` by `refl` | no completion in 300 s |
| `runs/amb4-732-verbatim.out` | 732's committed `runs/Amb4.agda`, verbatim, in this worktree today | **rc 251, 358.21 s, heap exhausted**, 2.28 GB peak |

## The wall, named precisely

`PT.agda` is green: the brief's named moves all land.  What dies is
the last line of `Amb4`: checking `∣ n 0 , (mem0 , ap , sp) ∣₁`
against `GraphAt` makes the elaborator compare the rows' types against
slots it derives by evaluating the reading of
`CntS.erase Mx.G.graphBndAt countGB`, and that conversion normalizes
`countFo` over the unfolded `ApproxB`/`StepB` trees.  `runs/pa.out`
isolates it: the conversion is fatal even when BOTH SIDES ARE THE SAME
SPELLING, so no spelling of the rows can dodge it -- this is the
sharpest new fact this dispatch measured.  It is consistent with 746's
b7-3 (>120 s for the different-spelling conversion) and b12 (>150 s),
and it explains today's 732-Amb4 verbatim death: the committed chain
shape was never green at this caliber.  `Amb2`'s matrix15 slot is the
same shape one level up (`CntS.erase Mx.matrix countMx` split three
ways, 746 report), and the probe's `MatrixAt` consumer (its φ₃ body is
`W3.erased`, `agents/tasks/LJ-1-667/Probe667.agda:46-47`) forces that
row, so the whole chain behind the obligation is closed at wide.

Two SECONDARY walls were pinned this dispatch, both inside the
probe's own frame (they would survive a chain cure):

- The 746 draft's bridge (`matrix-conj-from`, the `AT.read` step)
  grinds on its own: the full frame did not complete in 300 s nor in
  700 s (`runs/floor746split.out`, `runs/floor746split-2.out`).
  Without that one definition the same frame is cheap: 31.95 s, rc 42
  at the designed hole (`runs/floorB1.out`).  The grind is the
  unifier comparing `mapFo val A.matrix₃-Code` against
  `embed P667.matrix₃`, two relabellings over the big matrix.
  Rewriting by `conv` first, so the ∙'s sides spell
  `embed P667.matrix₃` textually, did NOT cure it in 300 s
  (`runs/floorB2b.out`).
- The unifier cannot decompose `countFo` of a Def formula against a
  meta-headed plus: the natural spelling
  `CntS.plus-zero-l (CntS.plus-zero-r countGB)` burns ~90 s and ends
  blocked on `_a` (`runs/pt.out`, `runs/pt4.out`), and `countTm
  (var kk)`'s alphabet needs `countTm {K = CS.S}` or its implicit
  stays unsolved (`runs/pt5.out`).  The measured cure, green in
  `runs/PT.agda`: name the split proofs once with every implicit
  spelled (`pA`, `pS`), spell the row types at those names, and
  transport with `erase-cong`.

## The statement's truth is not in question

No mathematics was refuted.  `bound-in-stage-at-empty`'s target is the
one 746's review recorded, and D-10's check of its truth stands as it
was: the wall is elaboration cost at a caliber, not a false target.

## What survives for the next brief

- `runs/PT.agda` (rc 0): the green spelling module -- `pA`/`pS`,
  `ApproxSlot`, `StepSlot`, `approx-split`, `step-split`.  Import it;
  do not rebuild it.
- `runs/PT2.agda.txt`, `runs/M0.agda.txt`, `runs/PA.agda.txt`,
  `runs/PM.agda.txt`: the four fatal shapes, with numbers.  Do not
  retry the GraphAt assembly in any spelling, and do not retry a
  reading-level `≡` conversion (mirror or not) without a new idea:
  PA shows identical spellings die.
- `Probe746Split.agda.txt`: the full drafted probe, bridge in the
  conv-first shape, ready to typecheck the day the chain closes.
- `runs/FloorB1.agda.txt` (31.95 s, rc 42 at the designed hole): the
  frame is NOT the problem, except for the bridge named above.

## What would reopen a GO

A shape in which no value is ever checked at, and no equality ever
compares, a type containing `CntS.erase <graph-or-matrix formula> p`.
The consumer chain makes that impossible today: `MatrixAt`'s φ₃ body
is `W3.erased`, so the probe cannot read `ambient-matrix` without the
erased-matrix row, and that row's graph component has no buildable
value.  Three moves could reopen it, all above this slot's pay grade:

1. A candidate 3 at the BRIEF level: restate what `Amb2`/the probe
   consume so the matrix15 slot is a NAMED mirror type end to end --
   that changes the obligation's consumer types, not just the chain
   internals, and needs the mathematician's ruling.
2. The heavy caliber (`-M4g`), the 746 review's third option.  PA's
   evidence cuts against it: the poison is the conversion's
   normalization, which heavy only caps later, not cheaper.  The
   owner's tier call, not mine -- the brief forbids asking from here.
3. A bridge candidate that makes `AT.read`'s application elaborate
   cheaply (the conv-first shape measured here does not).

Per DD25 (archive/dev/DD-archived.md:35) this NO-GO is delivered
beside the dispatch that owns the term, in the same directory as its
report, so the adversarial review can attack both as one pair.
