# LJ-1.121: supply levelIn and cover at the site

tier: codex (default)

## GOAL

**Reach the frontier.** `BoundedSubsetAt` is entered and its body
elaborates. **The first two hypotheses the site cannot supply are `levelIn`
and `cover`. Supply them, or say exactly what is missing.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`f941eea`. `make check` passes: I ran it.** A sibling agent works on the
coding side in probes only. **Do not touch `src/L/Coding/`.**

## WHAT IS MEASURED

`[LJ-1.119]`: **`Devlin55` now has NO parameter**, `BoundedSubsetAt` takes
`absorbs` at its own `α` and `x`, and **the site entry closes**: all fifteen
values supplied, each a VALUE and not a parameter, and the body elaborates
through `code-inj` (`src/ProbeLJ1119A.agda:38-79`, GREEN).

**The stop was pre-fixed and it fired where I asked**: the first hypotheses
the site does not supply are `levelIn` and `cover`, at `Co`'s boundary
(`src/L/BoundedSubset.lagda.md:1409-1411`), one module past
`BoundedSubsetAt`.

The two, quoted from the source at `:1409-1411`:

```agda
(levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩)
(cover : (y : S) → ⟨ y ∈ˢ HS.M ⟩
       → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩) ∥₁)
```

**`HullExt` states the same pair at `:917-919`**, so whatever you find binds
in two places. **Read both.**

## WHAT TO DO

1. **Say what each one asserts, in one sentence, from the source.**
   `levelIn`: the hull is closed under taking the stage AT an ordinal it
   contains. `cover`: every collapsed member lands in a stage whose ordinal
   is in the hull. **Verify those readings; do not take mine.**
2. **REFUTE FIRST, before you build.** Eleven hypotheses of the neighbouring
   layer were empty types, and each was found only when somebody attacked
   it. **Run `scripts/check-unbound-hyp.py` on the master and see what it
   says about these two**, then attempt a refutation the way
   `src/ProbeLJ197A.agda` does. **If either is refutable, STOP: that is the
   most valuable outcome available.**
3. **If they survive, supply them at the site.** The site is the
   `[LJ-1.119]` entry (`src/ProbeLJ1119A.agda`), where `α = ω`, `x = ∅` and
   `κ` is the Hartogs cardinal. **The hull `C.πX` and the carrier `M` are
   determined there, so the two facts are about concrete objects.**
4. **Report how far you reach, and what the next unsupplied hypothesis is**,
   at `file:line`.

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you supply must receive a VALUE, not another parameter.**
C-38. **Say for each whether it is supplied or restated, in those words.**

**If a hypothesis is stated more generally than the site uses it, say so.**
Both of `Devlin55`'s parameters were that defect, and both went by D-30
rather than by new mathematics (`[LJ-1.117]`, `[LJ-1.119]`). **Check
whether these two are the same shape before you build anything.**

## THE ABORT CRITERION

- **Either is refutable**: STOP and report it with the term. **Best
  outcome.**
- **Both are supplied at the site**: report the terms and the next
  unsupplied hypothesis, then STOP.
- **One is supplied and the other is not**: report both, with the term you
  could not write for the second. **A partial with an honest boundary is a
  good return.**
- **They are stated too generally**: report the narrowest form the body
  uses, and whether the site supplies THAT.
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. Report how far you reached.**

**Work in `src/ProbeLJ1121*.agda`. Do NOT edit any master.** If the cure is
a restriction, the master edit is the next dispatch.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken either statement to make it suppliable.** If it cannot be
  supplied, that is the finding.
- **Do not add a hypothesis to the site.** A site that assumes what it
  should supply has moved the obligation, not discharged it.
- **Do not edit any master.**
- **Do not write a probe as `.lagda.md`.** `[LJ-1.113]` did and five probes
  counted as masters. **Probes are `src/ProbeLJ1121*.agda`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and types from the source, never from a report.**
  **`BoundedSubset` moved twice today.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`levelIn` and `cover` are about the hull and the collapse, not about
definability.** Say whether the J tower inherits them unchanged.

## ARCHIVE (DD18)

- **`_build/lj-1.119-report.md`**, read WHOLE, and **`src/ProbeLJ1119A.agda`**.
  **The site entry and its fifteen values. This is your starting material.**
- `_build/lj-1.118-report.md` and `src/ProbeLJ1118A.agda`, the `absorbs`
  site value.
- `_build/lj-1.117-report.md`, the restriction pattern, in case these two
  are the same shape.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, the site.
- **`src/L/BoundedSubset.lagda.md:890-1050`**, `HullExt` and `Condense`,
  where the same pair is stated at `:917-919`; and **`:1400-1440`**.
- `src/ProbeLJ197A.agda`, the refutation shape.
- `dev/LESSONS.md` **C-38 as extended, C-39, C-40, P-x**, C-35, C-36, D-30,
  D-10, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Say in two lines how Devlin's 5.5 gets the hull closed under stages**,
from `dev/literature/devlin-II5.md`. **This is a place a source can settle
the shape cheaply, so spend a little.**

## SCOPE (read)

`src/L/BoundedSubset.lagda.md:917-1050` FIRST, then `:1400-1440`, then
`src/ProbeLJ1119A.agda`.

## SCOPE (write)

`src/ProbeLJ1121*.agda` only. Your report is `_build/lj-1.121-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch is the supply site.**
- **C-35.** A block with no consumer is UNTESTED. **You are the consumer.**
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40, D-8, D-30, D-10, D-29.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-x, P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- **Run `scripts/check-fences.py --check`** and say the master count. **It
  should be 87.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py`** on the master and on your probe,
  and report both.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.121-report.md` incrementally, skeleton first.

**Lead with whether either is refutable**, then whether each is supplied at
the site, in the words SUPPLIED or NOT SUPPLIED, with terms at `file:line`
and their seconds. Then the next unsupplied hypothesis. Then whether either
is stated more generally than the body uses it. Then what
`check-unbound-hyp.py` says. Then the C-39 section. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer.
