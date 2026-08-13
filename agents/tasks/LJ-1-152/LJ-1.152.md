# LJ-1.152: can two L-graphs compose without a second `hasReplacementL`?

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**One measurement decides whether A5 costs 254 seconds twice or six times, and
A5 is the last unpriced block of Route A-prime.** `[LJ-1.136]` named it as the
one measurement it would run next, and named it rather than guessed it.

**`[LJ-1.8]`, the GCH trophy, cannot be funded until A-prime has a total.**

## THE QUESTION, in `[LJ-1.136]`'s own words

> **Can two L-graphs be composed WITHOUT a second `hasReplacementL`?** If yes,
> A5 pays the 254 s once or twice instead of six times, and the seconds problem
> shrinks by a factor of three.

## WHAT IS MEASURED, and I verified the figures

`agents/tasks/LJ-1-136/ProbeLJ1136A.agda`: **98 lines, 254.22 s**, `--safe`,
exit 0. It builds the identity graph on an arbitrary L-set through
`hasReplacementL` and proves all four conjuncts.

**A free bisection, from a run that errored after 250.71 s:**

| | seconds | share |
|---|---:|---:|
| the graph construction, through `hasReplacementL` | ~250.7 | **98.6 percent** |
| all four conjuncts | 3.51 | 1.4 percent |

**The cost is the replacement step and nothing else.** So a construction that
COMPOSES two existing graphs instead of building a third pays the 3.51 s and
not the 250.

**A5 needs six constructions.** At one `hasReplacementL` each that is about 25
minutes of cold check, INFERRED by multiplication, which `[LJ-1.136]` marked as
not a price under P-l.

## WHAT TO DO

1. **Build the smallest composition that decides it.** Two L-graphs, composed,
   with the composite read back as an honest function. **If it needs a second
   `hasReplacementL`, the answer is no; if it does not, the answer is yes.**
2. **Measure it cold**, and report the seconds beside the load and the run
   count.
3. **Then re-price A5** with whichever answer you get, and say which of the six
   constructions can compose and which must build.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **GO** if the composite elaborates **without a second `hasReplacementL`**,
  and its cold seconds are nearer 3.51 than 254. **Then A5's seconds fall by
  about a factor of three and the block prices.**
- **NO-GO** if composition needs its own replacement. **Then A5 is six
  replacements, about 25 minutes, and the block's price is a DD24 question for
  the owner rather than a craft one.** Say so plainly; that is a complete
  answer.
- **The composite does not elaborate at all**: STOP and report the error. That
  would be a wall and it re-prices A-prime.

## THE C-38 GUARD, which `[LJ-1.136]` needed and so do you

**An abstract interface that nothing satisfies is a restatement, not a
supply.** `[LJ-1.136]` nearly shipped exactly that and its own C-38 guard
caught it, so it instantiated the interface at `[LJ-1.134]`'s concrete
non-degenerate graph.

**Do the same. Instantiate at a real graph, or your GO is vacuous.**

## THE OTHER HARD CONSTRAINT, measured at this site

**`[LJ-1.136]` hit three heap walls at the C-12 cap and cured all three:**

| what | seconds | result |
|---|---:|---|
| two `Small` module applications, unsealed | 138.52 | **heap exhausted at 8g** |
| one application, unsealed | 2.01 | green |
| `agree` instantiated, unsealed | 98.42 | **heap exhausted at 8g** |
| same file, `injOf` sealed `opaque` | 1.27 | green |

**Every derived injection must be sealed at its definition, or the chain does
not check at all under the cap.** **P-y**, admitted today, tells you how to
price a seal: count the definitions that look INSIDE, not the ones that name
it.

**Report a heap exhaustion as a wall. Never raise the cap.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe.
- **Do not touch `src/L/Condensation/TwelveAgree.lagda.md`**: `[LJ-1.150]`
  landed there and it is green.
- **Do not touch `src/L/Coding/Graph.lagda.md`**: 21 consumers are green on
  `[LJ-1.147]`'s seal.
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.** They are
  the evidence you build on.
- **A probe goes in `agents/tasks/LJ-1-152/`**, never in `src/`, tracked, never
  deleted. **Read `AGENTS.md` and `dev/LESSONS.md` D-1 fresh; both changed
  today.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
  `[LJ-1.151]` may be running Agda; its figure is lines, not seconds, but
  **yours IS seconds. Say whether the machine was quiet and report the load
  beside every figure.** The machine moved figures by up to 20 percent today,
  and `[LJ-1.148]` measured a fixed first-run penalty of about 0.9 s per
  series: **discard a warm-up.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.136]` already found the shape here and it is P-w: the shared helper
must be a FUNCTION, not a module applied per site.** That was the difference
between an exhausted heap and two seconds. **If composition works, say whether
the composer is template content both towers use.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-136/lj-1.136-report.md`**, read WHOLE, especially
  section 17.5 which states this measurement, and the heap-wall table.
- **`agents/tasks/LJ-1-136/ProbeLJ1136A.agda`** and **`ProbeLJ1136B.agda`**,
  read WHOLE. **You extend the first.**
- `agents/tasks/LJ-1-134/`: the read direction and its concrete graph.
- **`dev/LESSONS.md` P-w, P-y, P-l, C-38 as extended, C-12, D-1**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**
**But say whether Devlin's own square-law argument needs six separate
constructions or reuses one.**

## SCOPE (read)

`agents/tasks/LJ-1-136/ProbeLJ1136A.agda` FIRST, then its report's section 17.

## SCOPE (write)

`agents/tasks/LJ-1-152/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The abort criterion fixed BEFORE the run.
- **C-38 as extended.** Instantiate, or the GO is vacuous.
- **P-w, P-y, P-l, P-m, P-s, C-12, C-22, C-36, C-39, C-40.**
- **DD8, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO against the criterion, and the composite's cold seconds
with its load and run count.** Then A5 re-priced, and which of the six
constructions compose. Then whether any seal was forced and what P-y said.
Then the DD4 answer. **Mark every negative MEASURED or INFERRED.**
