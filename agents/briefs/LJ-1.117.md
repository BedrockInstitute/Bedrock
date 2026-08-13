# LJ-1.117: restrict sq to the ordinals the consumer reaches

tier: codex (default)

## GOAL

**Move the hypothesis to where the consumer can supply it.** `sq` is stated
for every ordinal and demanded only below the site. **Restrict it, and the
unconstructible case never arises.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`075204f`. `make check` passes.** A sibling agent works on the coding side
in probes only. **Do not touch `src/L/Condensation*`.**

## WHAT IS MEASURED

`[LJ-1.116]` traced the demand at `file:line` and it is narrow.

- **`sq` appears in `L.StageCardinal` at exactly two lines**: the parameter
  (`:15`) and `LimitStep`'s `Bound α oα infα (sq α infα)` (`:281`).
- **The induction never demands `sq` at a finite ordinal**: `P δ` carries
  the premise `δ ∉ ω` (`:528-530`), which is empty there.
- **`Devlin55`'s two uses are both at the site's own `α`**
  (`src/L/BoundedSubset.lagda.md:1529-1530` and `:1426-1427`).
- **So the demand set is the site's `α` and every infinite ordinal below
  it.** At the `[LJ-1.94]` site, `α = ω`, so **only `ω` is demanded, and the
  honest ℕ pairing supplies it.**

**`Init` cannot cover the general demand**, and two refutations say so:
`Init ω` is false because `Init` demands `ω ∈ ω`, and `Init (sucV δ)` is
false for every `δ`. **Both machine-checked**
(`src/ProbeLJ1116A.agda:62-63`).

`[LJ-1.114]` measured that the truncated `sq` cannot pass through `Upper`'s
induction, and proved why. **So restricting the hypothesis is the remaining
move.**

## WHAT TO BUILD

**Restrict `sq` so it is stated only where it is demanded, and check that
every consumer still goes through.**

1. **Find the narrowest restriction the bodies support.** The obvious
   candidate is to bound the quantifier by the site's ordinal:
   `sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → …`.
   **Read `LimitStep` and the induction to see what `δ` the step actually
   has in hand, and state the restriction from that. Do not adopt my
   sketch without checking it.**
2. **`α` is not a parameter of `Devlin55`; it is a parameter of
   `BoundedSubsetAt` and of `CodeCount`'s `Bound` use.** So the restricted
   `sq` may have to move out of `Devlin55`'s telescope into the modules
   that name `α`. **Say where it lands and why.**
3. **Then supply it at the `[LJ-1.94]` site**, where `α = ω` and the only
   infinite `δ ≤ ω` is `ω` itself. **Machine-check that supply.**
4. **Every master you touch is GREEN when you finish, or you revert all of
   them and say so.**

## C-40, AND IT IS THE RULE I BROKE THIS MORNING

**After you change `StageCardinal`'s or `BoundedSubset`'s parameter, check
every master that imports them and say which ones you checked, at
`file:line`.** `git grep -l "StageCardinal\|BoundedSubset" src/` is the
list. **Do NOT run `make check`; I run it. But name the consumers.**

## THE ABORT CRITERION

- **The restriction lands, every consumer is green, and the site supplies
  it**: report the diff, the cold seconds, the consumers checked, and STOP.
- **A body needs `sq` at an ordinal the restriction excludes**: STOP, name
  the body and the ordinal at `file:line`, and say what the narrowest
  workable restriction is. **That is still a good return.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. If more than one consumer breaks, say
how many.**

**Work in `src/ProbeLJ1117*.agda` for anything exploratory.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any theorem's conclusion.** Only the hypothesis's domain
  moves. **If a conclusion must change, that is the finding and you stop.**
- **Do not assume the axiom of choice.** Six dispatches measured this chain
  choice-free.
- **Do not re-attempt the truncation threading.** `[LJ-1.114]` measured it
  dead and proved why.
- **Do not touch `src/L/Condensation*`, `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**A restricted hypothesis is a weaker demand on both towers.** Say whether
the J tower inherits the restricted modules unchanged.

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
each touched master's cold seconds before and after, **with your run-to-run
spread before you claim a delta.**

## ARCHIVE (DD18)

- **`_build/lj-1.116-report.md`**, read WHOLE, and `src/ProbeLJ1116A.agda`.
  **The demand trace and the two `Init` refutations. This is your work
  list.**
- **`_build/lj-1.114-report.md`**, read WHOLE. **The threading is dead and
  the reason is proved; do not repeat it.**
- `_build/lj-1.111-report.md`, the truncated chain, still the fallback if
  the restriction fails.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, the site with
  `α = ω`.
- **`src/L/StageCardinal.lagda.md` whole**, and
  **`src/L/BoundedSubset.lagda.md:1361-1627`**.
- `dev/LESSONS.md` **D-30, C-40, C-39, C-38 as extended**, C-36, D-1, D-8,
  D-10, P-l, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** `[LJ-1.116]` settled what Devlin assumes. Say so
in one line.

## SCOPE (read)

`_build/lj-1.116-report.md` section 1 FIRST, then
`src/L/StageCardinal.lagda.md:270-300` and `:520-560`, then
`src/L/BoundedSubset.lagda.md:1420-1435` and `:1520-1540`.

## SCOPE (write)

`src/L/StageCardinal.lagda.md`, `src/L/BoundedSubset.lagda.md` and any
master their change forces (**all green at the end, or all reverted**), plus
`src/ProbeLJ1117*.agda`. Your report is `_build/lj-1.117-report.md`.
**Never `src/Everything.lagda.md`. Never `src/L/Condensation*`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **D-30.** Price what the CONSUMER needs. **This brief IS D-30.**
- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-38 as extended, C-35, C-36, D-10, D-29.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-x, P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`. **I run it on your result.**
- **Run `scripts/check-fences.py --check`** and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- **Run `scripts/check-unbound-hyp.py`** on anything you write.
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.117-report.md` incrementally, skeleton first.

**Lead with the restriction you landed, quoted**, and whether every consumer
is green. Then the site supply, machine-checked. **Then the C-40 section:
every consumer you checked, at `file:line`, and its result.** Then whether
any conclusion changed. Then the C-39 section. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer.
