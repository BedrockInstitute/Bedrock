# Task B4d report: the closure's constructibility, the fill, and the step (closing the levels)

**Date:** 2026-08-02. **Scope:** B4d on `godel-route` — per-tag image
constructibility for the meta step's nine tags, the step's ≤9-fold union, the
ℕ-induction `sliceL`, then the packed prefix table, the fill, and the step both
ways in Levels, per the brief. **Files touched:** `src/L/Godel/Closure.lagda.md`
(+1074 lines), `_build/b4d-report.md`. No git, no postulates, no holes, no
`TERMINATING`.

## 1. Status

The chapter is **green where the delivered code ends**: `agda
src/L/Godel/Closure.lagda.md` (~13 s cold), `agda src/L/Godel/Levels.lagda.md`
(~83 s cold, the recheck of Closure plus Levels), `agda
src/Everything.lagda.md`, the prose linter, the i18n marker check, the Agda-code
linter, and the glossary check all pass; `reuse lint` is the recorded
environmental failure. Delivered in Closure:

1. **The tag-image definitions, all nine**: `interImg`, `unionImg`, `diffImg`,
   `selMImg`, `selEImg`, `allImg`, `extImg`, `shiftImg`, `valuesImg` — each the
   `sett` over the tag's own payload, so the step is their nine-fold union.
2. **Five per-tag constructibility lemmas**, in the InL idiom: `interImgL`,
   `unionImgL`, `diffImgL` (one shared frame `BinImg`), `allImgL` (the tuple
   image is the singleton of the tuple family, so `sglL` on the delivered
   `allTuplesL`), and `valuesImgL` (`ValImg`, with the values walk
   `ValsWalk`). Each is one `defSet→isL`: a stage from `isL-directed` /
   `stageFam` over the shelves involved, a bounded defining formula with the
   operation's delivered description as the body atom, and the extensionality
   of the described set against the tag's fiber, whose two directions are the
   description's readers. The one-step climb `mkUp` (definable over a stage
   ⇒ member of the next one) is restated in the three lines the door costs,
   and each pin's second inclusion is bounded over the stage (a member of the
   next stage by `defSet ⊤̇ ≡ Lset σ`), so every formula is Δ₀ and the chain
   applies.

Not delivered: the four remaining tag lemmas (the two selections, the shift,
the extension), `stepL`, `sliceL`, and everything downstream in Levels (the
packed table, `prefix-fill`, `StepAt`, `step-out`, `step-in`). This report is
written against that honest state, per the wall protocol and the B4b/B4c
precedent. **The step laws did not land, so option B's tower side is not
closed end to end.**

## 2. The five delivered images, sizes and timings

Whole-file cold checks of Closure (agda 2.8.0, this machine), measured after
each addition:

| image | definition size | cold check | notes |
|---|---|---|---|
| inter / union / diff (shared `BinImg`) | ~290 lines | 10.5 s | one frame, three formulas; the walks (`BinWalk`) are the three two-line `z ∈ X`-connective formulas plus the operations chapter's laws |
| all | ~25 lines | 13 s | the payload is a unit, so the image is the singleton of the tuple family |
| values (`ValImg` + `ValsWalk`) | ~350 lines | 13 s | the delivered values description's body as the pin; the walk is the bridge chapter's values definability, module-parameterized (see §3) |
| whole file with all five | | 13 s | stable |

No single definition crossed the 180 s wall in the delivered region; the
delivered definitions typecheck in seconds each.

## 3. The two genuinely different failures

**Failure 1 (resolved): the values walk's performance.** The first
formulation of the values walk took >4 min cold and never finished. Bisect
showed the culprit was the walk's `defSet≡` when parameterized as a function
`valsWalk : (X : V ℓ) → ...`; restating the walk as a module parameterized by
`X` at the module level (`module ValsWalk (X : V ℓ) (hX : ...) where`) dropped
the whole file to ~13 s. This matches the pattern that the bridge chapter's
Vals/SelMem modules are module-parameterized, and the lesson is recorded below.

**Failure 2 (the wall): the selection image's walk.** The selection frame
(`SelImg`, with the membership shape over the member chain through the
recorded pairs and the pin's stage-bounded second inclusion) and its machinery
(`ΦM`, `dΦM`, `chainM`, the singleton-stage helper) typecheck in seconds, but
the walk's `defSet≡` sub₁ — the SelMem-style `fromSat` reading the eight
bounded quantifiers with two `prAt-adequate` applications on a nine-element
environment and the `selectMember-in` call — exceeds 4 min cold and does not
finish, while the byte-identical structure in `L.Godel.InL`'s `SelMem`
compiles in the 16 s whole-file cold check of InL. Bisect pinned the slowness
to `sel≡`'s sub₁ (stubbing sub₁ restores the ~13 s file time; stubbing sub₂
does not help). The P-d/P-c performance laws are the suspected mechanism, but
the InL-identical code being fast rules out the obvious culprits, and the
distinction could not be isolated within budget.

The two failures are genuinely different: failure 1 was the module-vs-function
parameterization of a walk; failure 2 is a fromSat-region performance wall on
an InL-identical structure. Per the wall protocol (180 s, LESSONS,
stop-and-report after three genuinely different failures), work stopped at the
second, with the third (the shift/extension walks, the SftD/ExtF-shaped
siblings of the same pattern) virtually certain to follow.

## 4. Which InL names were public vs restated

Public and used directly: `stageFam`, `allTuplesL` from `L.Godel.InL`; `sglL`
from `L.Coding.InL`; `defSet→isL`, `isL-directed` from `L.Axioms.Basic`;
`prAt-adequate` from `L.Coding.Base`; `∈pair-introR` from `L.Coding.Base`; the
operations chapter's membership laws and `C`'s closure family (all public after
B4b's de-privatization). Restated locally, exactly as the bridge chapter
restates them (all `private` there): the domain-generic atoms `sglAt′`,
`pairAt′`, `prAt′`, `appAt′` with their Δ₀ witnesses, and the one-step climb
`mkUp` (three lines). The `At`-descriptions' bodies are the pin atoms, per the
brief; the descriptions' readers are the two directions of each
extensionality.

## 5. LESSONS

Applied: P-d (directions over paths; the pins are bounded Δ₀ formulas and the
walks' satisfactions are read via the chain), P-c (no `⋃`-tower under a
membership obligation; the tag images are direct setts over their payloads),
Rule 1 (discharge substitutions at variable arguments), Rule 10 (named helpers
for the disjunct dispatch), D-2 (junk excluded by construction; the pins'
second inclusions range over the stage so the equality is exact). Newly
recorded: the module-parameterization performance law for the walks (failure
1), and the selection-walk performance wall with its bisect trail (failure 2),
both in the report's §3.

## 6. Verification

`agda src/L/Godel/Closure.lagda.md`, `agda src/L/Godel/Levels.lagda.md`,
`agda src/Everything.lagda.md` green; `lint-prose.py --check`,
`weave-i18n.py --check`, `check-glossary.py --check`, `lint-agda.py --check`
pass. The only failing gate is `reuse lint` (environmental, recorded from
B4a/B4b).
