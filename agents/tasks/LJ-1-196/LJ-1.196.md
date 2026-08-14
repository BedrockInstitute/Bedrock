# LJ-1.196: `DefAt`'s ambient reading, 84 lines or a chapter

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**, by the owner's
rule of 2026-08-14: this task runs Agda, so it takes pro and holds an Agda slot.

## GOAL

**`[LJ-1.184]` supplied `AmbientRead` and closed one of `[LJ-1.7]`'s four open
hypotheses. It then fixed THIS probe's GO and NO-GO in advance, before it could
know the answer.** `agents/tasks/LJ-1-184/lj-1.184-report.md` section 5.4.

**Run it. The answer decides whether the ambient port is 84 lines or a
chapter.**

## THE OBLIGATION, in `[LJ-1.184]`'s own words

> `DefAt`'s ambient reading is only ever spent at a RECORDED VALUE, and the
> induction has already pinned that value to `Tow c` for an ordinal `c`. So ask
> whether the ambient reading can be spent at an environment whose two `DefAt`
> slots are CONSTRUCTIBLE, where the delivered `abs₀` plus the delivered
> `DefAt-stage` close it.

**The smallest decisive miniature, also its words:** restate `StepAt-out` at the
ambient carrier with TWO extra hypotheses, that the recorded value is `Lset c`
and that `c` is an ordinal, and try to close it with `abs₀`, `DefAt-stage` and a
slot-agreement lemma of `⊨-rename`'s shape.


## WHAT THE FIRST ATTEMPT REACHED BEFORE IT EXHAUSTED, and it wrote NOTHING

**`[LJ-1.196]`'s first run died with its report file never created.** Its brief
carried C-22 and it did not obey it. **You obey it: create
`agents/tasks/LJ-1-196/lj-1.196-report.md` in your FIRST five minutes and fill
it as answers land. Research held only in your head dies with your budget, and
it did.**

**Its reasoning is salvaged here so you do not repay it.** Verify each step; it
is a dead agent's scratch work and NOT a measurement.

- The ambient reading is `ambient γ φ = (map fst γ) AbsF.⊨ᵛ φ` for
  `φ : Formula (Σ Full) n`, while the class `DefAt : Formula (Σ isL) n` pushes
  along `emb : Σ isL → Σ Full`, `emb (x , p) = (x , tt*)`.
- `⊨-map` in `Relabelling` gives
  `(γ ⊨ mapFo f φ) ≡ (γ ⊨∘ φ)` at the composed interpretation. **At `f = emb`
  and `ι = fst` the composite `fst ∘ emb` IS `fst : Σ isL → S`**, because
  `fst (emb (x , p)) = x`. So the ambient reading of the pushed formula is
  definitionally `AbsL`'s own reading.
- `abs₀` at `AbsL` then relates that to the class reading.
- **THE CRUX IT REACHED AND COULD NOT PASS:** in `StepAt-out`, `w`'s value is
  constructible, `fst (lookup w γ) ≡ Lset c` with `isL (Lset c)` via `LsetS c oc`.
  **`u`'s value is `d`, and it saw no way to get `isL d` from the two extra
  hypotheses.**
- **Its last thought, unfinished:** whether `u`'s slot at the ACTUAL use site is
  `d` at all, or something already constructible.

**THAT LAST QUESTION IS YOUR FIRST ONE.** Go to the use site and read what fills
`u`. `[LJ-1.184]` says the ambient reading is only ever spent at a RECORDED
value the induction has already pinned. **If `u`'s slot is pinned too, the crux
dissolves; if it is genuinely `d`, that is the NO-GO and you say so.**

## THE ABORT CRITERION, FIXED BEFORE THE RUN AND NOT BY YOU (D-1)

**`[LJ-1.184]` fixed it before it could know the answer, which is what makes it
worth obeying. Do not restate it in your own terms.**

- **GO** if the two extra hypotheses are enough. **Then the residue never
  touches `L.Coding.Model`, and the whole ambient port is the 84 lines of
  `[LJ-1.184]` section 5.2 plus one restructuring of `step-value`.**
- **NO-GO** if `abs₀` cannot be applied because the OTHER environment slots, the
  approximation `f` and the argument `b`, are not constructible and no
  slot-agreement lemma reaches. **Then the ambient `DefAt` reading is a port of
  the satisfaction coding, and that IS a chapter.**

**Both answers are complete deliverables. NO-GO re-prices `[LJ-1.7]` and that is
worth more than a partial build.**

## THE PREDICTION ON THE RECORD, and it is not evidence

**`[LJ-1.184]` marked its expectation INFERRED: it believes GO is more likely,
because `Lset-only`'s own proof already carries the value equation at every
step, `src/L/Hierarchy.lagda.md:283-299`. It typechecked NOT ONE LINE of it.**

**So the prediction is a hypothesis and you are the measurement. Do not let it
steer you toward GO.**

## P-l BINDS BY CONSTRUCTION AND `[LJ-1.184]` SAID SO

**The class-carrier instance is NOT a price for the ambient instance.** The
whole reason this probe exists is that the tree delivers the read-off at the
class carrier only. **Re-measure at the ambient carrier or you have measured
nothing.**

## BEFORE YOU WRITE A LINE

**Grep the WHOLE tree for what you are about to build, and include the file you
think you already know.** `[LJ-1.163]` measured that three dispatches priced a
term the tree already held, because a grep excluded the file holding the answer.
**Report the search you ran, and its filter.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a probe.
- **A SIBLING'S FILE MAY BE RED WHILE YOU WORK.** `[LJ-1.178]` lost fifteen
  minutes to that. **BUILD GENERIC FIRST** so you do not depend on a sibling's
  import path.
- **A probe goes in `agents/tasks/LJ-1-196/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure, discard a warm-up, and take at least three
  kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE BAR

**DD24 unchanged, and nothing tightens it** (owner, 2026-08-14). The GCH bar was
FIXED when the AC trophy landed and does not drift; every GCH module uses that
one number; and **INTERMEDIATE DEBT IS ALLOWED**, because only the whole GCH
side, at the end, is judged.

**Report your lines and seconds as measured. Record an overage plainly (DD8).
Never delete a line to improve a ratio.**

## THE INSTRUMENT

**`check-ratio.py` prints `noise band: at least +-12.8%, MEASURED [LJ-1.148]`.**
`[LJ-1.185]` then measured that a term everyone had quoted for two days was a
DOUBLE SUBTRACTION and never existed. **A delta inside the band is not a small
measurement, it is no measurement.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.184]` wrote its generic module at 167 lines naming ZERO of `isL`,
`𝒮ʟ`, `Lset` and `𝒟ₒ`, with both the tower and the carrier as parameters, and
measured that SIX extra lines bought the second tower.** **Write yours the same
way and say how much re-instantiates for the J tower.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-184/`**, read WHOLE with all three probes. **It is the
  build you continue and its section 5.4 is your brief within this brief.**
- `agents/tasks/LJ-1-178/`: `levelIn` and `cover` built at the real site, and
  `ProbeLJ1178B`, which reads `theorem` out.
- `src/L/Hierarchy.lagda.md:283-299`, the proof `[LJ-1.184]` names as the reason
  it expects GO, and `:334-335` for the class-carrier read-off.
- **`archive/dev/JOURNAL-archived.md:2126-2128` and `:2197`.** **The retired
  route stated this same obligation as `AmbientOnly` and STOPPED on it**, and
  measured its most expensive row at about 77 s. **Read what it hit; take SHAPE,
  never a claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md:93-106`, `devlin-errata.md`, `j-hierarchy.md`.
**Say whether Devlin spends clause (a) at a recorded value or at an arbitrary
one.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-184/lj-1.184-report.md` section 5.4 FIRST, then its probes.

## SCOPE (write)

`agents/tasks/LJ-1-196/` only. **No master.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed before the run, and here it was fixed by
  somebody else.
- **P-l.** A measured cure does not transfer by analogy. **This probe is P-l's
  test case by construction.**
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-k, P-m, P-y, C-12, C-22, C-39, C-40. DD0, DD8, DD24, D-10, D-26, D-29,
  D-30. I-5.**

## CONSTRAINTS

- Count with `python3 scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO against `[LJ-1.184]`'s criterion, in one word, then the
ambient port's price in lines.** Then the miniature, and which hypotheses closed
it or failed. Then the supply search you ran, with its filter. Then the seconds
with load and run count. Then the DD4 re-instantiation figure. Then what
`[LJ-1.7]` still needs. **Mark every negative MEASURED or INFERRED.**
