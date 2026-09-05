# LJ-1.154: carve the identity graph by separation, not by replacement

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.152]` named this as the highest-value next hour and measured why.**
Build the identity graph on an L-set by ONE `hasSeparationL` instead of by
`hasReplacementL`, and measure it.

**If it lands near 2.5 s, `[LJ-1.136]`'s 254 s construction was never
necessary, and A5's seconds collapse.**

## WHAT IS MEASURED, and every figure below is somebody else's measurement

| | seconds | source |
|---|---:|---|
| one `hasSeparationL` | **under 0.1**, below this machine's resolution | `[LJ-1.152]` |
| one `hasReplacementL` | **259 to 269**, net of a 1.18 s import baseline | `[LJ-1.152]` |
| the ratio | **at least 2,500 to 1** | `[LJ-1.152]` |
| `ProbeLJ1136A`, the identity graph BY REPLACEMENT | **254.22**, 98 lines | `[LJ-1.136]` |
| of which the graph construction | **98.6 percent** | `[LJ-1.136]`'s free bisection |
| the composite BY SEPARATION | **2.50, 2.52, 2.49**, warm-up discarded | `[LJ-1.152]` |

**`[LJ-1.152]` composed two L-graphs by separation and it worked.** The device:
the pairs are indexed by a SMALL type, `boundingOrd` bounds them, and a stage is
an element of L. **That is `hasPowerL`'s own device**
(`src/L/Axioms/Power.lagda.md:143-190`) **with the resizing dropped.**

**The open question is whether the same device BUILDS a graph, or only
COMPOSES two that already exist.** Nobody has tried.

## WHAT TO DO

1. **Read `agents/tasks/LJ-1-152/ProbeLJ1152E.agda` whole.** It is the working
   separation carve and your starting point.
2. **Read `src/ProbeLJ1136A.agda` whole.** It is the 254 s construction you are
   trying to replace, and its four conjuncts are the acceptance criterion:
   whatever you build must prove the same four.
3. **Build the identity graph by separation**, prove all four conjuncts, and
   **instantiate at `[LJ-1.134]`'s concrete non-degenerate graph so the result
   is not vacuous.** C-38.
4. **Measure it cold**, warm-up discarded, at least three kept runs, with the
   load beside every figure.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **GO** if the identity graph carves by separation, proves the same four
  conjuncts, and its cold seconds are **under 30**. That is an order of
  magnitude below 254 and it settles the question without quibbling over 2.5
  against 5.
- **NO-GO** if the carve needs a `hasReplacementL` after all. **Then
  `[LJ-1.136]`'s 254 s stands, A5 is six replacements, and the price becomes a
  DD24 question for the owner.** That is a complete answer.
- **The carve needs a bound nobody can supply**: STOP and name the bound. That
  is the interesting failure.

## WHY SEPARATION MIGHT NOT REACH IT, stated so you test it rather than assume

**Separation carves a subset OUT of a set you already have. Replacement BUILDS
a set from a function.** `[LJ-1.152]`'s composite worked because both graphs
already existed and their pairs live in a bounded stage.

**For the identity graph the question is whether the pairs `⟨x, x⟩` for
`x ∈ A` live inside a set you can name before you build them.** If
`boundingOrd` bounds them the same way, the carve works. **If naming that set
needs replacement, the device does not transfer and that is the NO-GO.**

**`[LJ-1.152]` measured that a separation takes a ONE-PLACE formula**, and its
only new object-language content was 20 lines for that reason.

## THE TRAP THIS SESSION MEASURED TWICE TODAY

**A measured cure does not transfer by analogy. Re-measure it at its own
site.** P-l.

**`[LJ-1.152]` proved it on itself**: sealing `G` and `G-spec` `opaque`, which
cured Condensation, moved this site by nothing. 247.60 s against controls of
260.37 and 270.53, inside the file's own 6.4 percent spread.

**So do not assume the composition result transfers to construction. Measure
it.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe.
- **Do not touch `src/L/Condensation.lagda.md` or the three `*Agree`
  masters.** `[LJ-1.153]` repaired them hours ago and they are green.
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.** They are
  the evidence you build against.
- **A probe goes in `agents/tasks/LJ-1-154/`**, never in `src/`, tracked, never
  deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
  **`make check` is running on this machine right now**, so **discard a warm-up,
  take at least three kept runs, and report the load beside every figure.**
  `[LJ-1.148]` measured a fixed first-run penalty of about 0.9 s per series and
  a between-series uncertainty of 12.8 percent.
- **Report a heap exhaustion as a wall.** `[LJ-1.136]` hit three at this site
  and the walls were the finding.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.152]` found the shape: only two names tie its composer to L,
`hasSeparationL` and the stage device.** **Take those as module parameters and
the J tower re-instantiates instead of rewriting. If your carve has the same
property, say so.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-152/lj-1.152-report.md`** and **`ProbeLJ1152E.agda`**,
  read WHOLE. **The device you are extending and the seal refutation.**
- **`src/ProbeLJ1136A.agda`** and `agents/tasks/LJ-1-136/lj-1.136-report.md`
  section 17, read WHOLE. **The construction you are replacing.**
- `src/L/Axioms/Power.lagda.md:143-190`, the bounding device in its original
  home.
- **`dev/LESSONS.md` P-l, P-y, P-w, C-38 as extended, C-12, D-1**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **Say whether Devlin builds these graphs by
replacement or carves them by separation.** If he carves, our 254 s was our
choice and not the mathematics. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-152/ProbeLJ1152E.agda` FIRST, then `src/ProbeLJ1136A.agda`.

## SCOPE (write)

`agents/tasks/LJ-1-154/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The abort criterion fixed BEFORE the run.
- **P-l.** A measured cure does not transfer by analogy. **This task is P-l's
  test case twice over.**
- **C-38 as extended.** Instantiate at a real graph or the GO is vacuous.
- **P-y, P-w, P-m, P-s, C-12, C-22, C-36, C-39, C-40.**
- **DD8, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO against the 30 s criterion, and the cold seconds with
the load and the run count.** Then whether the four conjuncts closed. Then what
the bound was and who supplies it. Then A5 re-priced, and say plainly whether
it is priced or still unpriced. Then the DD4 answer. **Mark every negative
MEASURED or INFERRED.**
