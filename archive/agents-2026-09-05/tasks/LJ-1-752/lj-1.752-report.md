# LJ-1.752 return: block∈Lγ, stage membership lifts along the finite iterate

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: GO.** The obligation is inhabited at
`agents/tasks/LJ-1-752/Probe752.agda:120`, the body is ONE `Lset-mono`
application (`Probe752.agda:126`), and the file typechecks at the pane
caliber (`runs/green-3.out`, rc 0, 0.99 s, on the final bytes; earlier
passes rc 0 at 0.97 s and 0.94 s in `runs/green-1.out` and
`runs/green-2.out`). `table-sat` is absent: the final file carries zero
`Sat` tokens (`grep -c Sat` over `Probe752.agda` returns 0). Nothing
lands in `src/` (`git status --porcelain` names `agents/tasks/LJ-1-752/`
only). The brief's W3 question, whether `Lset-mono` along
`sucIter-in-γ` converts, has the answer YES.

## What the obligation is

The brief names one term in `agents/tasks/LJ-1-752/Probe752.agda`:

    block∈Lγ :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
        (n : ℕ) (b : V ℓ) →
        ⟨ b ∈ˢ Lset (sucIter n x) ⟩ → ⟨ b ∈ˢ Lset γ ⟩

Route: `sucIter-in-γ` puts the iterate inside γ, and one `Lset-mono`
(`src/L/Constructible.lagda.md:365`) lifts the stage membership along
that inclusion. `[LJ-1.751]` has a GO report
(`agents/tasks/LJ-1-751/lj-1.751-report.md`, Disposition line), so per
the coder rule on module hypotheses this file takes the term that
predecessor DELIVERED, not merely its type: `sucIter-in-γ` and its
closer are transcribed token for token from
`agents/tasks/LJ-1-751/Probe751.agda:58-99`. The body of the new
obligation is 1 line (`Probe752.agda:126`); the file is 126 lines, and
the gap is the transcription plus its header, which the W3 estimate did
not count.

## The brief's type block dropped one arrow, again

The brief printed the obligation as

    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
    (n : ℕ) (b : V ℓ)

with no arrow between the two lines. This is the same slip `[LJ-1.751]`
measured and fixed
(`agents/tasks/LJ-1-751/lj-1.751-report.md`, section "THE BRIEF'S
OBLIGATION BLOCK DROPPED ONE ARROW", rc 42 `[ParseError]` at its own
site). This return inserted the one `→` after `⟨ x ∈ˢ γ ⟩` at
`Probe752.agda:120-121` and changed nothing else: the delivered
statement is the brief's named statement, no weakening. **The brief
template still carries the slip one task after 751 named it. The
producer should fix the template, not the next report.**

## Shape kept, shape changed

- KEPT: the closer (`no-succ`, `suc∈γ`) and the induction, token for
  token from `agents/tasks/LJ-1-751/Probe751.agda:58-99`, transcribed at
  `Probe752.agda:74-110`. The closer is itself the 747 closer
  (`agents/tasks/LJ-1-747/Probe747.agda:65-87`) with the
  `hγ : ⟨ isL γ ⟩` argument trimmed, which is the 737-SPLIT closer one
  trim up the chain.
- KEPT: the trimmed telescope of 751. The obligation names no `isL γ`
  and no `ω`, so the imports stay a strict subset of 747's.
- ADDED: `Lset` and `Lset-mono` to the `L.Constructible` import
  (`Probe752.agda:41`). This is the only import delta over the 751 file.
- TRANSCRIBED, NOT IMPORTED: `open import LJ-1-751.Probe751` is
  available (`bedrock.agda-lib` lists `agents/tasks` as an include
  root), and this return declined it on a ground one step past 751's
  trade. A probe is a frozen record, and nothing typechecks it after its
  task closes (`agents/README.md:92`). `archive/` is not an include root
  (`bedrock.agda-lib`: `include: src agents/tasks`), so a cross-probe
  import dies the day the other probe retires under `archive/`, which
  the post-LJ-1 collection pass is queued to do. The chain
  737-SPLIT -> 747 -> 751 is the same trade, each recorded at its own
  site (`agents/tasks/LJ-1-737-SPLIT/lj-1.737-SPLIT-report.md:33`).
  W2 note: the closer is now written 4 times in the tree and the
  induction twice; the canonical homes stay the 747 probe and the 751
  probe until a chapter-sized absorption lands.
- NAMED, NOT RUN: the same statement closes without ANY closer, by the
  `+ω` route, because `+ω-iter`
  (`src/L/Ordinal/StageArith.lagda.md:68`) puts every finite iterate
  inside `+ω x` and `clγ x x∈` puts `+ω x` inside γ, so two nested
  `Lset-mono` applications on those two memberships reach the same
  conclusion (`boundCloses`/`envCloses` are the same shape at
  `src/L/Ordinal/StageArith.lagda.md:86` and `:92`). That route drops
  the closer frame, `L.Ordinal.Stages`, and `V.Model` from the file
  entirely. The brief commands the `sucIter-in-γ` route and 737-SPLIT's
  trimmed shape used it, so this file did not run the `+ω` variant; the
  note is untested here and is the first thing a frame-cutting brief
  should measure.

## What the next brief needs

- Supply 1 at the meter's name: later briefs may cite
  `agents/tasks/LJ-1-752/Probe752.agda:120` for the whole
  block-in-stage leaf, and `Probe752.agda:126` for the lift.
- The floor and the price sit inside one run-to-run noise band on this
  box: floor 1.07 s (`runs/floor-1.out`), price 0.97/0.94/0.99 s across
  three full passes. The term is free; the frame is the cost, and the
  frame is the 751 file. No heap wall, no timeout, no import left to
  trim.
- TIMING CAVEAT: the box was shared during these runs; `pgrep` showed
  one live foreign Agda process (pid 68355) beside them. The absolute
  numbers carry that load. The worktree's `_build` was warm (708 cached
  interfaces) when the runs started.
- EXIT-CODE HAZARD, same as 747 and 751 recorded: Agda 2.8.0 exits 42 on
  a PARSE error too, so branch rows keyed on `exit_code = 42` cannot
  tell a parse slip from a NO-GO. No 42 occurred in this task; all four
  runs exited 0.

## W3 answer

The brief's W3: whether `Lset-mono` along `sucIter-in-γ` converts
(estimated 20 to 80 lines). IT CONVERTS. The proof proper is 1 line
(`Probe752.agda:126`); the file is 126 lines, and the gap is the
transcription plus header, which the estimate did not count. No binder
resisted. The one resistance was again in the brief's own type block,
and it is the missing arrow recorded above.

## W2 answer

The closer now exists 4 times in the tree and the finite-iterate
induction twice. This return adds its copy knowingly, because the chain
precedent (737-SPLIT, 747, 751) transcribes and the hermeticity ground
above rules out the import route for a probe. No deadline forced the
form. The once-and-instantiate home for a chapter-sized closer does not
exist yet; a brief that needs the closer a 5th time should queue the
absorption instead of a 5th copy.

## Runs (wide caliber, pane GHCRTS `-A64m -I0 -M2g` untouched, one Agda
process per run, /usr/bin/time -p)

- `runs/floor-1.out`: floor, imports and the full 751 frame with the
  obligation block removed, rc 0, 1.07 s. THE FLOOR.
- `runs/green-1.out`: full file, rc 0, 0.97 s, no warnings. THE PRICE.
- `runs/green-2.out`: re-certification, rc 0, 0.94 s.
- `runs/green-3.out`: re-certification on the FINAL bytes after one
  header comment reword (the old comment named `Sat` while denying it;
  the file now carries zero `Sat` tokens), rc 0, 0.99 s.

## Mandated paste

    $ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-752
    check-survey-quotes: LJ-1-752 clean (0 note(s), 0 defect(s))

    (The interpreter is the main tree's .venv; the worktree carries none.
    lint-agda.py --check also ran, rc 0.)

The scope slot `review-of-block∈Lγ.md` stays unwritten: this is a GO,
and per the coder instructions a `review-of-*.md` file is how a NO-GO is
stated, not an extra artifact of a GO.

## Ratio bar

The deliverable is a raw `.agda` probe: it carries no ` ```agda ` fence,
so the in-fence divisor counts 0 and the 0.0123 s/line bar cannot fire
on this task, exactly as the brief states.

## ARCHIVE USED

- `archive/dev/DD-archived.md:30`: "**A return carries an ARCHIVE USED
  section** naming what it actually read and what it took from each item,
  at `file:line`." READ. This row is the mechanism this block and the
  LITERATURE USED block run under, and its why-not rule is applied below.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch wiring and
  slot orchestration are the program's business; this return writes one
  probe and its report.
- `archive/dev/PLAN-archived.md`: declined, not read. The disposition
  follows the brief's own branch table, not the archived plan.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing
  status is `dev/pod/screen.toml`, and no standing figure is quoted here.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  evidence this return builds on is cited at `file:line` from the live
  tree: `agents/tasks/LJ-1-751/Probe751.agda`,
  `agents/tasks/LJ-1-747/Probe747.agda`, and
  `agents/tasks/LJ-1-737-SPLIT/lj-1.737-SPLIT-report.md:33`.

## LITERATURE USED

- `dev/literature/devlin-errata.md:132`: "transitive + contains ω +
  closed under the finite set of generators of B." READ. This is the
  WS-suggested amenable definition, and its finite-generator closure is
  the classical shadow of this obligation: one generator (`sucV`),
  finitely many iterates of a member, and the stage they generate sits
  below the closed bound. The same entry block records at
  `dev/literature/devlin-errata.md:134`: "amenable M is false; WS gives
  a counterexample with Model M6,5 (pp. 62-63):", which is the
  literature-side corroboration of premise 4's ban on inhabiting
  `table-sat`.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. This
  return introduces no term and proposes no glossary entry.
- `dev/literature/primary-sources.md`: declined, not read. The formal
  fact this return needs is already green in the tree
  (`src/L/Constructible.lagda.md:365`); no fetch decision is open.
- `dev/literature/rudimentary-functions.md`: declined, not read. The
  rud-route closure machinery concerns definable power operations; the
  obligation's iteration is the plain `sucV` successor
  (`src/L/Ordinal/StageArith.lagda.md:36`), and no rudimentary function
  enters the proof.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. The errata entry
  already names its source (WS counterexample, Devlin pp. 62-63), and
  this return cites no new source.
