# Task B4e report: the probe verdict, the two selection images, and the shift-image wall

**Date:** 2026-08-02. **Scope:** B4e on `godel-route` — first the
transparency-hypothesis probe on the B4d selection wall (the report's
headline), then the four remaining tag images, `stepL`, `sliceL`, prose, and
the report, per the brief. **Files touched:** `src/L/Godel/Closure.lagda.md`
(+2372 lines), `_build/b4e-report.md`. No git, no postulates, no holes, no
`TERMINATING`; temporary probe files lived under `src/` and were removed
before finalizing.

## 1. The headline: the transparency hypothesis is confirmed

B4d's wall was the selection walk's `sel≡` sub₁ — the SelMem-style `fromSat`
reading the eight bounded quantifiers with two `prAt-adequate` applications on
a nine-element environment at concrete shelves — exceeding 4 min cold and
never finishing. The hypothesis: the difference from InL was not the proof but
the transparency of the arguments; InL's walks take their sets as abstract
module parameters, while the B4d walk's environment reached the concrete
transparent bodies (`slice`'s recursion, the payload's concrete setts, the
assembly's stage over them).

**The mandated first formulation confirmed the hypothesis.** Restating the
selection walks with the shelves, the keys and the stage as abstract module
parameters — the formulas and the `fromSat` readers never mentioning `slice`,
`satSet`, or any concrete `sett` — the file checks green with both selection
images in **~30 s cold** (deps cached), against B4d's recorded **>4 min,
never finished**. The instantiation at the real shelves happens only at the
lemma-assembly level, where memberships and equations flow but nothing
unfolds.

## 2. The probe trail

The probe was run in three stages:

1. **Standalone mini-probes** (`_build/probe3/`, deleted before finalizing):
   the SelMem machinery at abstract args checks in ~2.1 s; at concrete
   `X`/`Ka`/`Kb` with an abstract stage, ~2.2 s (the isolated wall did not
   reproduce); at a concrete stage in the module header, ~2.0 s. A concrete
   stage with concrete membership proofs (the singleton climb
   `sglUp-mini (sucV ∅) ∅∈`) walled past 270 s and was killed — the P-d/R-9
   class reproduced at the membership-construction level, a related but
   distinct wall from the selection walk.
2. **The real-file before/after**: the abstract `SelWalk`/`SelEWalk` in
   Closure check green as part of the ~30 s file; the two selection frames and
   assemblies follow (also ~30 s). The B4d before number is its recorded
   >4 min.
3. **A level-meta detour**: `num∈num`'s type `⟨ # m ∈ # n ⟩` left `#_`'s
   level implicit after the `open InfinitySet using (…)`; the unresolved meta
   walled the whole file. Pinning the level through a module alias
   (`module IS = InfinitySet {ℓ}`) fixed it — the type-level meta search, not
   the recursion, was the cost.

## 3. Delivered: the two selection images

`selMImgL`/`selEImgL`, one frame per selection (the membership shape differs
by one recorded value), sharing the discipline:

- The image formula ranges over the shelf and over the singletons of the
  arity numeral's members, with the selection description's membership shape
  (the eight- or six-quantifier pair-chain, the keys bound, not constants) as
  the body atom, and the pin's second inclusion bounded over the stage.
- The payload keys are read through the numeral memberships: `num∈num`
  (numerals are von Neumann ordinals) and `∈#-elim`, with `fromℕ'` for the
  `Fin k` payload.
- The walk (`SelWalk`/`SelEWalk`) is the bridge chapter's SelMem/SelEq with
  abstract shelves, keys and stage; the frames apply it at the real shelves
  only in the pin's two directions.
- Assembly via `stageFam (suc (suc k))` over the shelf, the numeral, and the
  numeral's singletons.

Also delivered green: the shift's seek machinery (`sucAt′`, `tailSeek`,
`seekOut`/`seekIn`, `pairUp`/`prUp`/`tailStage`) and the abstract `ShiftWalk`
(the SftD-shaped walk, ~75 s of the file's cold time, currently unconsumed —
the shift image frame below walled).

| item | approx. lines | file cold check |
|---|---|---|
| `SelWalk` + `SelEWalk` | ~230 | — |
| `SelMImg` + `selMImgL` | ~250 | — |
| `SelEImg` + `selEImgL` | ~250 | — |
| `num∈num` + seek machinery + `ShiftWalk` | ~460 | — |
| whole file (seven images + shift machinery) | +2372 | ~107 s cold |

## 4. The shift-image wall (B4e's first genuinely different failure)

The shift image frame (`ShiftImg`) at the image stage (`sucV⁴ τ`) with the
seek sentence's membership shape as the pin atom did not finish: the file's
cold check exceeded 240 s and was killed repeatedly (once at 360 s).

Bisect trail (each step by deleting or commenting the region, measuring,
restoring — stub types with formula holes themselves wall, so deletion was
used):

1. Stage machinery alone: fast (~2.5 s).
2. + formulas (`shape`/`dShape`/`shapeV`/`Φ`/`dΦ`): fast.
3. + `chain`: fast.
4. + readers (`shape-read`/`shape-fill`): fast.
5. The pin's `sub₂`: the deep satisfaction type
   `⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩` walls even with a hole
   body; restating it at a bound stage index or as a frame-level helper over a
   plain `z` parameter does not help; even the two-line term
   `∣ X , hXˢ , {!!} ∣₁` against that type walls.

Mechanism: constructing the deep formula's satisfaction directly forces the
checker to unfold the seek sentence's 6-deep chain structure in conversion;
the library's `abs-defSet`-based `chain` is cheap because its type matches
without unfolding. The `opaque` seal does not cure it (the proofs need the
unfolding). This is the P-d/R-9 class at the seek sentence's scale — the
same class the concrete-stage singleton climb reproduced in §2.

Consequence: the extension image is of the same class (the ExtF machinery is
deeper, at `sucV⁵`), and was not started; `stepL` (the nine-fold union of the
images) and `sliceL` (successor via `stepL`) are blocked behind the shift
image. Per the wall protocol (three genuinely different failures across the
route, this being the third), work stopped here, pending a design ruling on
the deep satisfaction construction rather than a workaround.

## 5. Items accounted

1. Selection images `selMImgL`/`selEImgL`: **delivered** (§3).
2. Shift image `shiftImgL`: **walled** (§4); the SftD-shaped walk and seek
   machinery delivered green.
3. Extension image `extImgL`: **not started** (same wall class, deeper).
4. `stepL`: **blocked** (needs all nine images).
5. `sliceL`: **blocked** (needs `stepL`).
6. Prose (en + zh): updated for the delivered state — the constructibility
   section now says seven images and records the wall; the Recap says what is
   delivered and what waits on a ruling.
7. `make check`: green through the glossary stage; `reuse lint` fails with the
   recorded environmental `PermissionError` (sysconf) — the same environmental
   failure as B4a/B4b.
8. Levels fill/step: not started, per the brief.

## 6. LESSONS

Applied: P-d, P-c, R-2, R-9, R-13 (locality; the frame-level helpers did not
avoid the wall), Rule 1, Rule 10, D-1 (the probe doctrine: cheapest decisive
probe first, abort criterion fixed), D-2, C-8 (the probe files under `src/`
would be skipped by the git-ls-files linters; removed before finalizing).
No new lesson is recorded: the shift wall has no cure yet, and the lesson
book admits only measured, sourced entries.

## 7. Surprises

- The isolated selection machinery did **not** reproduce the B4d wall in any
  standalone parameterization; the real-file context (and the concrete-stage
  singleton climb) did.
- Stub types with formula holes wall as badly as the real code — bisecting
  with `{!!}` is unreliable; deletion-based bisects were required.
- An unresolved universe level in a two-line lemma (`num∈num`) walled the
  whole file until pinned.
