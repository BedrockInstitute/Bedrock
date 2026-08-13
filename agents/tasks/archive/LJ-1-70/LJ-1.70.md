# LJ-1.70: one generic frame, and the discharge it carries

tier: codex (default)

## GOAL

`[LJ-1.69]` measured a nine-to-one swing between two spellings of the same
discharge. **Write the cheap one, and discharge `TwelveAgree`'s twenty-four
hypotheses with it.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `43275a5`.
**The working tree carries an uncommitted, GREEN placement**:
`src/L/Condensation.lagda.md` at 6,390 in-fence lines against HEAD's 5,562.
**Do not discard it.** `[LJ-1.69]` left it byte-identical to its own start.

## THE MEASUREMENT THIS DISPATCH EXISTS TO ACT ON

`[LJ-1.69]` priced one row module at the discharge frame at **3.6 s**, and
found that almost none of it is the module application:

| what | measured |
|---|---:|
| the USED surface: `row`, `out`, `back` | **about 0.12 s** |
| an UNUSED module-level application | **0.089 s**, no elaborated copy at all |
| the FRAME TELESCOPE: seventeen site facts | **about 3.5 s** |

**Four of those seventeen state satisfaction over the BUILT trees**
`envSetAt`, `envOverAt` and `tmValAt` (`envK`, `envInK`, `valV`, `valW`).
That is P-t content and it is where the money is.

**So the two spellings differ by nine to one:**

```text
one frame PER ROW    3.6 s x 13                = 46.8 s
ONE GENERIC frame    3.4 s + 0.12 s x 13       =  5.0 s
```

**Write the generic one.** It is the same shape `KFacts` took for the other
fact family at `src/L/Condensation.lagda.md:5674-5725`, which measured
**-30 s**.

## WHAT TO BUILD

1. **ONE generic discharge frame.** The seventeen site facts stated once,
   parameterized by the row's tag and slots, so the thirteen rows
   instantiate it rather than each restating the telescope. The probe shape
   is `src/ProbeLJ155B.agda:71-137` (`RowMem`); `[LJ-1.69]` section 1 gives
   the exact application it measured.
2. **The discharge.** Use the frame to supply `TwelveAgree`'s twenty-four
   hypotheses: `mem-out mem-back eq-out eq-back and-out and-back or-out
   or-back imp-out imp-back neg-out neg-back top-out top-back bot-out
   bot-back exist-out exist-back forall-out forall-back allin-out allin-back
   exin-out exin-back` (`src/L/Condensation.lagda.md:6406`).

**This is real wiring, not a probe.** If it lands, `TwelveAgree` stops
resting on twenty-four hypotheses, which is the C-35 debt the whole band was
placed to pay.

**The proofs already exist.** The thirteen row modules are in the band and
each proves its own `out`/`back`. **This is instantiation, not proof.** If
you find yourself proving a row, stop and say which.

## THE LAW, amended today, that tells you where to look

**P-w, as amended by `[LJ-1.69]`.** Read it whole in `dev/LESSONS.md`.

- **A module application is LAZY at module level**: the copy is paid when
  something USES it, not when it is written. An instrument that counts
  unused applications measures nothing.
- **Classes (a) fewer applications and (b) fewer definitions copied are
  MEASURED FALSE at this file** (two hoists, one narrowing).
- **Class (c), cheaper types on what is copied, is where the money is**, and
  the four built-tree fact types are its target.

**Do not build a fifth interposition.** A module that re-exports another
module strictly adds copies. The generic frame is not an interposition: it
replaces thirteen telescopes with one, which is fewer restatements, not a
layer on top of them.

## THE ABORT CRITERION, fixed in advance per D-1

Measure `L.Condensation` cold, three runs each side, same session, gate
caliber, loads reported beside every figure. **Then run
`python3 scripts/check-ratio.py --check` and quote its aggregate.**

- **The discharge lands at 8 s or less** over the as-placed baseline: **GO.
  Report and STOP.** Do not go on to the post-leaf five.
- **Between 8 s and 20 s**: **STOP and report the number.** That is still a
  large win against 47 s and the owner needs it before anything else is
  funded.
- **Above 20 s, or any wall**: **STOP and report the price.**

**Either way this dispatch ends after the discharge is measured.** Do not
attempt `levelIn`, `cover`, or the post-leaf five.

**The gate's guard may refuse in your sandbox** (`pgrep` cannot read the
process list). Say so, bypass it as the last five dispatches did, and keep
every Agda invocation sequential. **I re-run the gate myself.**

## WHAT YOU MUST NOT DO

- **You may not weaken a statement and you may not narrow a direction.**
  Both directions of every row are needed; that is settled.
- **Do not delete the band or any part of it.** It is the discharge.
- **Do not delete content to buy the ratio.** P-q.
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`.
- **Count a module's exports by finding its boundary, not by guessing a line
  range.** I reported `EnvSet` at fifteen when it has eleven, because I read
  past its end into `TmVal`. If you report a count, say where the module
  ends.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**This dispatch IS the DD4 move.** `[LJ-1.69]` found that "write it generic"
is exactly the lever separating 47 s from 5 s, so for once the rule and the
cheap answer are the same thing. **Say what the J tower inherits from the
generic frame**, and whether it can instantiate it at its own slots without
a second frame.

## ARCHIVE (DD18)

- **`_build/lj-1.69-report.md`**, read WHOLE. Sections 1 to 4 are the frame
  shape, the measurement and the arithmetic you are acting on.
- **`src/ProbeLJ155B.agda:71-137`**, the `RowMem` frame shape, and
  `src/ProbeLJ161A.agda` for the chain's own shape.
- `_build/lj-1.62-report.md` sections 2-3, the `KFacts` bundle you are
  copying, and its -30 s.
- `_build/lj-1.66-review.md` section E.1, P-w's evidence.
- `_build/lj-1.68-report.md`, the narrowing negative and the export-count
  discipline.
- `dev/LESSONS.md` **P-w as amended**, P-t (`:2601`), P-m (`:2460`),
  P-n (`:2483`), P-q (`:2633`), D-30 (`:3255`), read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and
spend nothing.

## SCOPE (read)

`_build/lj-1.69-report.md` sections 1 and 4 FIRST, then
`src/ProbeLJ155B.agda:71-137`, then
`src/L/Condensation.lagda.md:6406-6604` (`TwelveAgree`), then the `KFacts`
record at `:5674-5725`.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ170*.agda`. Your report is
`_build/lj-1.70-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-w as amended.** The copy is paid at use; class (c) is where the money
  is.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-q, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-1, D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries uncommitted work
  that is not in HEAD.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.70-report.md` incrementally, skeleton first.

**Lead with whether `TwelveAgree`'s twenty-four hypotheses are DISCHARGED**,
and the discharge's measured cost, three runs each side, one caliber, with
the spread and the load. Then the gate's aggregate, quoted. Then whether the
four built-tree fact types are still the mass, since that is class (c)'s
target. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer
and **the convergence answer.**
