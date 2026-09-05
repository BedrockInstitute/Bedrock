# LJ-1.332: the limit band, the last gap in `sq`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHERE THIS SITS, and it is the last one

**`[LJ-1.330]` returned CANONICAL after four「do not fund this」returns in a
row.** The gap that was「all non-initial ordinals」is now **the non-initial
LIMIT ordinals, and nothing else.**

| band | status |
|---|---|
| `Init α` | **DELIVERED**, `via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961` |
| ω | **DELIVERED**, `squareω`, `src/L/InjChain.lagda.md:184-185` |
| successors | **BUILT, 25 code lines**, `agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-152` |
| **non-initial LIMITS** | **THE ONLY WALL LEFT** |

**The successor step works because the hard leg is already delivered
untruncated:** `shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫` at
`src/L/Absorption.lagda.md:188-190`. **I read it. It is ambient by its own
header, and that is fine here: `sq` is proof-side.**

**And a correction of mine made that build work**, so read it before you assume
the limit case needs a bijection: **`[LJ-1.330]` measured that a bijection is
NOT needed. TWO injections suffice, and one leg is free**, `ord-emb` at
`src/L/BoundedSubset.lagda.md:1370-1379`.

## THE WALL, exactly

**`src/L/Cardinal.lagda.md:133-134`.** `LeastCardInjL` gives `κ` untruncated at
`:126`, and then `κ-inj : ∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁` **truncated**. **The
chapter's own comment at `:132` says so.**

**INFERRED by `[LJ-1.330]`, and you should test it:** ordinal recursion does not
reach the limit case either, because `godSWO` is `via-col-square`'s own device
and `Init` is exactly its landing condition (`SquareLaw.lagda.md:308`, `:384`,
`:931-932`).

## THE LEAD, and its earlier refutation does NOT apply here

**`[LJ-1.330]` names `stage-card-upper` as the lead for this band**, and
`[LJ-1.321]`'s section 8 item 4 is still live while item 3 is now RETIRED.

**`[LJ-1.324]` REFUTED a `stage-card-upper` transplant, and you must read WHY
before you either repeat it or dismiss it:**

> It refuted the transplant **at `CanonInj`'s pair**, a BIG-INTO-SMALL injection
> whose motive has TWO indices while `stage-card-upper`'s has one. **Its killer
> was the motive, and `missing-is-goal` typechecks with body `x`, so no work
> moved.**

**THIS IS A DIFFERENT PAIR.** **Read `agents/tasks/LJ-1-324/lj-1.324-report.md`
whole and say, in your first section, whether its killer applies here.** **If it
does, this lead is dead too and saying so early saves the task.** **If it does
not, say exactly why the motive differs.**

**`[LJ-1.324]` also left an asset: it extracted the engine GENERIC, 39 non-blank
non-comment lines**, `agents/tasks/LJ-1-324/Graft.agda:86-129`, tower-blind.
**That asset survives its own refutation. Use it if it fits.**

## THE QUESTION

**Is there a canonical `sq α` at a non-initial LIMIT ordinal, and what does it
cost?**

**「Canonical」means the same thing it meant for `[LJ-1.330]`: a term built from
α's own structure, with no selection step, no truncation and no order on a
function type.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT BUILDS.** **Then `sq` is total, `[LJ-1.8]`'s blocker is gone, and this is
  the largest result of the campaign.** Report the term, its lines, its seconds
  and its negative control. STOP.
- **THE MOTIVE KILLS IT, as it killed `[LJ-1.324]`.** **Say so in your first
  section and stop early.** **That closes the lead honestly and the project
  needs the answer more than it needs an attempt.**
- **IT NEEDS THE TRUNCATED `κ-inj` AND NOTHING ELSE.** **Then the wall is
  exactly one delivered truncation, and the question returns to
  `[LJ-1.321]`'s live candidates.** **Name which one.**
- **THE LIMIT BAND IS EMPTY OR UNREACHABLE.** **If the trophy never quantifies
  over a non-initial limit, the wall is not a wall.** **CHECK THAT FIRST; it
  would be the cheapest possible answer** and `[LJ-1.314]` already measured that
  the consumers need the law at every δ below the site.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-332/`. **`src/` is forbidden** (I-5).
- **DO NOT LAND `[LJ-1.330]`'s successor lemma.** **Its landing site is an open
  question: `BoundedSubsetAt` at `src/L/BoundedSubset.lagda.md:1385` has NO
  consumer in `src/`, and that chapter imports neither `L.Absorption` nor
  `L.InjChain`. MEASURED by `[LJ-1.330]`.** The orchestrator settles it.
- **Do not attempt `[LJ-1.329]`'s alternative 2**, moving `sq` inside L.
  `[LJ-1.330]` measured it is NOT forced.
- **Do not edit another task directory.** You may READ and RE-RUN the sibling
  probes in `agents/tasks/LJ-1-321/`, `LJ-1-324/` and `LJ-1-330/`; you may not
  change them.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling is measuring CHECK TIMES.** Take ONE slot and report the load
  beside every figure.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **RUN NEGATIVE CONTROLS, and prefer the kind that MEASURES.** **`[LJ-1.330]`
  ran three and all three measured: one of them put the limit band in a single
  Agda error message.** **That is the standard here.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-332/lj-1.332-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISES OF MINE MOST LIKELY TO BE WRONG

**`[LJ-1.330]` found my last brief's premise wrong in ALL THREE PARTS**, and one
of its corrections is what made the build succeed. **The score across this leg:
four of my last five briefs carried a claim an agent measured FALSE.**

**The one most at risk here: 「`stage-card-upper` is the lead」.** **It is
`[LJ-1.330]`'s recommendation, not a measurement, and `[LJ-1.324]` already
refuted that module at a different pair.** **Check it before you spend budget
on it.**

## THE RULES THIS CHAIN EARNED

**C-44.** See above. **This is the fifth brief in a row to warn about itself and
four of the four checks found something.**

**C-36. A failed substitution is not a proof of impossibility.** **`[LJ-1.324]`
refuted ONE transplant at ONE pair. That is not a refutation of the module.**

**C-42. A refutation measures the site it names.** The same point from the other
side.

**D-10. Price the TRUTH of a recorded residue before pricing its proof.**
**Check the limit band is non-empty before you build for it.**

**P-l, C-45.**

**A STOP IS A DELIVERABLE. It was right four times running on this leg, and
then the fifth task built the thing. Both outcomes are real.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**`[LJ-1.330]`'s term is tower-blind, MEASURED from its imports**, and it
reaches its site **because it takes a POINT of a delivered injection type
instead of a total map out of `sq α`** — which is exactly why `[LJ-1.329]`'s
object could not exist. **Keep that property.**

**INFERRED by `[LJ-1.330]` and worth confirming:** landing the successor lemma
pulls `L.Absorption` and `L.InjChain` back into the GCH closure, which
`dev/ledger.toml:206-211` already bounds at 51 masters, 9,953 lines and 39.1
percent. **Say what YOUR term would add.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-330/lj-1.330-report.md`, read WHOLE.** It funds you and
  it corrected three premises to get its build.
- **`agents/tasks/LJ-1-324/lj-1.324-report.md`, read WHOLE.** The refutation you
  must decide applies or not, and the generic engine it left behind.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md` section 8**, the live candidates,
  with item 3 now RETIRED by `[LJ-1.330]`.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route met the limit case too. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Devlin proves the square law for every
infinite ordinal and `[LJ-1.327]` measured that his 5.6 takes the pairing from
generic cardinal arithmetic.** **Say in one line how his argument handles the
LIMIT case specifically**, because that is the only band left and his method may
name the device this tree is missing. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-324/lj-1.324-report.md` FIRST, to decide whether the lead is
already dead.

## SCOPE (write)

`agents/tasks/LJ-1-332/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, D-10, C-36, C-42, C-44, C-45, P-l.** Named above with what each
  governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-52, C-53, C-49, C-50, P-i, P-k, P-m, P-y, R-40, R-41.**
- **C-22, C-32, C-38, C-39, C-40.** I-5. **D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: BUILDS, DEAD-LEAD, ONE-TRUNCATION or EMPTY-BAND.** Then
whether `[LJ-1.324]`'s killer applies at this pair, in your FIRST section. Then
the term or the wall at `file:line`. Then lines, seconds and load. Then your
negative controls and what they named. Then what remains of `[LJ-1.8]`'s
blocker. Then the DD4 axis and closure. **Mark every negative MEASURED or
INFERRED.**
