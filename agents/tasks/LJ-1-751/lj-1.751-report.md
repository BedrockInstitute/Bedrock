# LJ-1.751 return: sucIter-in-γ, finite successor iterates stay inside closedω

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: GO.** The obligation is inhabited at
`agents/tasks/LJ-1-751/Probe751.agda:91`, the file typechecks at the
pane caliber (`runs/green-2.out`, rc 0, 1.18 s; re-run rc 0,
`runs/green-3.out`, 0.97 s, no warnings), and `table-sat` and every
`Sat` symbol stay absent (`Probe751.agda:18` is the only occurrence of
the name, in the comment that forbids it). Nothing lands in `src/`
(`git status --porcelain` names `agents/tasks/LJ-1-751/` only).
The brief's W3 question, whether induction on `n` converts from
`suc∈γ`, has the answer YES, at a price barely above the floor.

## What the obligation is

The brief names one term in `agents/tasks/LJ-1-751/Probe751.agda`:

    sucIter-in-γ :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
        (n : ℕ) → ⟨ sucIter n x ∈ˢ γ ⟩

Body: induction on `n`. The zero clause returns the hypothesis, because
`sucIter zero u` computes to `u`
(`src/L/Ordinal/StageArith.lagda.md:35`). The successor clause computes
`sucIter (suc n) x` to `sucV (sucIter n x)`
(`src/L/Ordinal/StageArith.lagda.md:36`) and applies the 747 step at
the previous iterate (`Probe751.agda:96-99`). `closedω` enters through
`suc∈γ` alone; no `+ω` leg is needed, because the iterate block is
finite. The term is 5 lines (`Probe751.agda:95-99`).

## THE BRIEF'S OBLIGATION BLOCK DROPPED ONE ARROW, and this return fixed it

The brief printed the obligation as four lines with NO arrow between
the hypothesis line and the `n` line:

    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
    (n : ℕ) → ⟨ sucIter n x ∈ˢ γ ⟩

Agda parses that as `⟨ x ∈ˢ γ ⟩` applied to `(n : ...)`, and rejects
the typed binding's colon: rc 42, `[ParseError]` at 94.8
(`runs/green-1.out:1-4`, 0.07 s). The statement the brief intends is
the arrow chain, the form `boundCloses` and `envCloses` use
(`src/L/Ordinal/StageArith.lagda.md:81-93`) and the 747 obligation
carried (`agents/tasks/LJ-1-747/Probe747.agda:106`). This return
inserts the one `→` at `Probe751.agda:93`. Nothing else in the type
moved: the delivered statement is the brief's named statement, no
weakening. **The next brief built from this template should be checked
for the same slip before dispatch.**

## Shape kept, shape changed

- KEPT: the 747 closer `no-succ` and `suc∈γ`, token for token from
  `agents/tasks/LJ-1-747/Probe747.agda:65-87`, which is itself the
  737-SPLIT closer with the `hγ : ⟨ isL γ ⟩` argument trimmed. The
  transcription sits at `Probe751.agda:58-80`; the successor step the
  brief names is `Probe751.agda:78-80`.
- KEPT: the trimmed telescope. This obligation carries no `isL γ` and
  no `⟨ ω ∈ˢ γ ⟩`, so the import list is a strict subset of 747's:
  no `L.Coding.Bound`, no `L.Axioms.Numerals`, no `#∈ω`, no `Lset`,
  no `ω`. The obligation type mentions only `sucIter` and `closedω`
  beyond what the closer needs, both from
  `src/L/Ordinal/StageArith.lagda.md:34-36` and `:81`.
- TRANSCRIBED, NOT IMPORTED: the brief commands it, and the trade is
  the same one 747 records as its ONE DEVIATION: importing
  `LJ-1-747.Probe747` (possible; `bedrock.agda-lib` includes
  `agents/tasks`) would drag the numerals and Bound frame into every
  recheck of this file for legs this obligation never names.

## What the next brief needs

- Supply 1 at the meter's name: later briefs may cite
  `agents/tasks/LJ-1-751/Probe751.agda:91` for the whole finite
  iterate block, and `Probe751.agda:78-80` for the single step.
- The induction recipe, measured: zero clause is the hypothesis, one
  `suc∈γ` application per successor, no rewriting needed because
  `sucIter` reduces definitionally on both constructors. A later
  transfinite-iterate brief should NOT expect this recipe to carry:
  at a limit ordinal the block is `+ω`, and the route there is
  `closedω` directly (`src/L/Ordinal/StageArith.lagda.md:81`), not
  this induction.
- The floor and the price sit 0.13 s apart (1.05 s against 1.18 s):
  the frame IS the cost, the induction is free. No heap wall, no
  timeout, no import left to trim.
- TIMING CAVEAT for any comparison against other panes: the box was
  shared during these runs; `pgrep` showed live Agda processes from
  the LJ-1-740-SPLIT and LJ-1-742-SPLIT-SPLIT worktrees. The absolute
  numbers above carry that load; the floor-minus-price delta is the
  comparable figure.
- EXIT-CODE HAZARD, same as 747 recorded: Agda 2.8.0 exits 42 on a
  PARSE error too, not only on scope errors. The branch rows keyed on
  `exit_code = 42` cannot tell a parse slip from a NO-GO; this report
  is the disambiguator, and it names the GO.

## W3 answer

The brief's W3: whether induction on `n` converts from `suc∈γ`
(estimated 20 to 80 lines). IT CONVERTS. The proof proper is 5 lines
(`Probe751.agda:95-99`); the file is 99 lines, and the gap is the
closer transcription plus its header comments, which the estimate did
not count. No binder resisted. The one resistance was in the brief's
own type block, and it was the missing arrow recorded above.

## W2 answer

The closer now exists in the tree three times: 737-SPLIT with `isL γ`,
747 and this file with the trim. The once-and-instantiate home for a
chapter-sized closer does not exist yet, and this probe adds the third
copy knowingly, because the brief names transcription. No deadline
forced the form; the telescope and the brief did. A later brief that
needs the closer a fourth time should instead queue the absorption
747's own report already proposed.

## Runs (wide caliber, pane GHCRTS `-A64m -I0 -M2g` untouched, one Agda
process per run, /usr/bin/time -p)

- `runs/floor-1.out`: floor, imports and closer without the obligation
  block, rc 0, 1.05 s. THE FLOOR.
- `runs/green-1.out`: full file with the brief's type block verbatim,
  rc 42, 0.07 s, `[ParseError]` at 94.8. NOT a price; it is the
  missing-arrow record above.
- `runs/green-2.out`: full file with the arrow fixed, rc 0, 1.18 s,
  no warnings. THE PRICE.
- `runs/green-3.out`: re-certification, rc 0, 0.97 s.

## Mandated paste

    $ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-751
    check-survey-quotes: LJ-1-751 clean (0 note(s), 0 defect(s))

    (The interpreter is the main tree's .venv; the worktree carries none.
    lint-agda.py --check also ran, rc 0.)

The scope slot `review-of-sucIter-in-γ.md` stays unwritten: this is a
GO, and per the coder instructions a `review-of-*.md` file is how a
NO-GO is stated, not an extra artifact of a GO.

## Ratio bar

The deliverable is a raw `.agda` probe: it carries no ` ```agda `
fence, so the in-fence divisor counts 0 and the 0.0123 s/line bar
cannot fire on this task, exactly as the brief states.

## ARCHIVE USED

- `archive/dev/DD-archived.md:30`: "**A return carries an ARCHIVE USED
  section** naming what it actually read and what it took from each item,
  at `file:line`." READ. This row is the mechanism this block and the
  LITERATURE USED block run under, and its why-not rule is applied below.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch wiring
  and slot orchestration are the program's business; this return writes
  one probe and its report.
- `archive/dev/PLAN-archived.md`: declined, not read. The disposition
  follows the brief's own branch table, not the archived plan.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing
  status is `dev/pod/screen.toml`, and no standing figure is quoted here.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  evidence this return builds on is cited at `file:line` from the live
  tree: `agents/tasks/LJ-1-747/Probe747.agda` and
  `src/L/Ordinal/StageArith.lagda.md`.

## LITERATURE USED

- `dev/literature/devlin-errata.md:132`: "  transitive + contains ω +
  closed under the finite set of generators of B." READ. This is the
  WS-suggested amenable definition, and its finite-generator closure is
  the classical shadow of this obligation: one generator (`sucV`),
  finitely many iterates of a member, all inside. The same entry block
  (lines 133-135) records that the naive uniform `Sat` claim is FALSE
  (WS counterexample, Model M6,5), which is the literature-side
  corroboration of premise 4's ban on inhabiting `table-sat`.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. This
  return introduces no term and proposes no glossary entry.
- `dev/literature/primary-sources.md`: declined, not read. The formal
  fact this return needs is already green in the tree
  (`src/L/Ordinal/Stages.lagda.md:137-138`); no fetch decision is open.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. No
  level-formula slot is touched; the obligation quantifies over
  `n : ℕ` and never names a formula.
- `dev/literature/rudimentary-functions.md`: declined, not read. The
  rud-route closure machinery concerns definable power operations; the
  obligation's iteration is the plain `sucV` successor at
  `src/L/Ordinal/StageArith.lagda.md:36`, and no rudimentary function
  enters the proof.
