# LJ-1.710 report: the one unpaid lemma, in a frame trimmed to ordinals

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.710
obligation: agents/tasks/LJ-1-710/Probe710.agda::the-obligation
verdict: **NO-GO on the obligation; GREEN frame and GREEN merge at an own-name
presentation delivered beside it.** `review-of-bound2-in-limit.md` states the
stop with `file:line`. The probe typechecks clean under the pane caliber:
`runs/final.out`, EXIT=0 (on disk 2026-08-27 it reads `1.50 real`,
280887296 bytes; the harness rewrote it after the report named an
earlier pair of decimals). This dispatch re-ran the same delivered
file green under the pane caliber: `runs/t-recap.out`, EXIT=0,
0.84 s warm, 275103744 bytes.

## 1. WHAT THE DISPATCH BUILT

One file, `agents/tasks/LJ-1-710/Probe710.agda`, four sections:

1. `IsLimit`, the restructured limit predicate: ordinality, successor
   closure, and small-family union closure
   `(X : Type ℓ) (h : X → S) → (∀ i → ⟨ h i ∈ₛ α ⟩) → ⟨ ⋃ (sett X h) ∈ₛ α ⟩`.
   Presentation-honest by construction: the clause takes any family, so the
   instance side never needs a judgmental match.
2. `the-obligation : Type (ℓ-suc ℓ)`: the brief's statement, verbatim, over
   that predicate. Well-formedness is the measured floor.
3. The merge theorem CLOSES at a family written in this file:
   `bound2OwnLimit` (`succFam` named once top-level so no expression ever
   compares two spellings of one family), plus `ownMergedOrd` from
   `suc-ord`/`setUnion-ord` and membership into the limit. This is the whole
   proof skeleton of the obligation modulo one name.
4. The gap, typed out as a comment, with the runs that measure it.

## 2. THE LADDER, MEASURED

| id | question | verdict | evidence |
|---|---|---|---|
| t-small | does the trimmed frame (L.Ordinal only, no LEM, no FOL proof cone, no probes) admit the obligation TYPE? | GO, EXIT=0, 1.37 s, 278 MB cold | runs/t-small.out |
| t-e1 | can the union-closure clause be INSTANCED against `fst (bound2 …)` through elaboration unification alone? | NO-GO, `[UnequalTerms]` `L.Ordinal.f σ₁ σ₂ o₁ o₂ x != mf x` | runs/t-e1.out:5-9 |
| t-paths2 | is bound2's where-bound family referenceable by qualified name? | NO-GO, `[NotInScope]` for `L.Ordinal.bound2.f` | runs/t-paths2.out:5-8 |
| t-selflambda | is a locally defined clause function convertible to its own written case lambda at a variable? | NO-GO, same wall on MY OWN symbol | runs/t-selflambda.out:5-6 |
| final | does the delivered probe check clean in place? | GO, EXIT=0 (2026-08-27 rerun: EXIT=0, runs/t-recap.out) | runs/final.out |

The intermediate diagnostics `t-floor … t-spelling` record the harness bring-up
and the discovery that `_∈ˢ_` memberships over quantified families need the
small `_∈ₛ_` layer here; they are kept as research trail.

## 3. W3, THE WIDEST UNMEASURED TERM, ANSWERED

The brief asks whether `bound2`'s pair construction converts without
unfolding `sett`. Measured answer, three data points:

- Judgmental conversion NO for predecessor p-26 style `refl`
  (agents/tasks/LJ-1-705/runs/p-26.out:5-8), reconfirmed for the pair-vs-sett
  spelling in p-21.
- Judgmental conversion NO even through elaboration-time metavariable solving,
  which p-26 does not cover (runs/t-e1.out:5-9).
- Conversion also fails between my own function and its identical written case
  lambda at a variable position (runs/t-selflambda.out:5-6). Index-splitting
  to constructors is what revives normalization: Section 3's proofs all pass
  that way, and only that way.

Price came in under estimate: the estimate was 60 to 150 lines for inhabiting
the membership; the delivered file carries ~120 lines total including the
frame, floor and green merge, because the route found never needs a
sett-unfolding equation, it needs a name.

## 4. W2 ANSWER

The mathematics is written once at a generic carrier: `IsLimit`'s closure
clause and `succFam` are stated for arbitrary families and ordinals, then the
merge instantiates them. No second copy was funded anywhere. No deadline
conflict arises; nothing was weakened in the obligation TYPE.

## 5. STOP CONTENTS AND HANDOFF

Per the Boundary this stop is a deliverable:

- The obligation reduces to ONE fact: parity between a writable family and
  bound2's internal where-bound family. That symbol is not referenceable and
  not convertible against any locally written twin.
- Minimal cure is src-side, one definition or one lemma, restated in full in
  `review-of-bound2-in-limit.md` ("what would reopen the route"). Section 3 of
  the probe is the skeleton that cure completes.
- `[LJ-1.705]`'s split plan stands: its first half is now PROVED here at own
  presentation; its second half waits on that surface.
- The target is not shown false (D-10 recorded in the review).

## 6. PRICE

| item | measured |
|---|---|
| trimmed-frame floor (type only, cold) | 1.37 s, 278 MB, EXIT=0 (runs/t-small.out) |
| elaboration-unification wall | 1.48 s, 277 MB, EXIT=42 (runs/t-e1.out) |
| self-lambda conversion wall | 1.45 s, 283 MB, EXIT=42 (runs/t-selflambda.out) |
| delivered probe, write time | EXIT=0 (runs/final.out; the harness rewrote that out after this report first saved, so the original write-time decimals live only in the review chain record) |
| delivered probe, 2026-08-27 rerun, warm | 0.84 s, 275103744 bytes, EXIT=0 (runs/t-recap.out) |
| brief estimate | 60 to 150 lines |
| probe code lines | see file; single `.agda`, comments included |
| in-fence lines | 0 (raw `.agda`, ratio bar cannot fire) |
| caliber | `-A64m -I0 -M2g`, wide, set on the pane by the program, never set here |
| heap wall | none under the trimmed frame; the p-14 wall did not recur |
| `src/` edits | none |

No number above is quoted under any other caliber than the pane's. One Agda
process per run throughout.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch measures live elaborator behavior, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE DD RULING SERIES, archived in full 2026-08-18`. Declined: not used. The governing clauses live in the slot file and AGENTS.md, not in this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the L3.32-T series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` Slot role table row for Devlin 2.6 naming `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`. Read. Confirms the consuming context: every branch of the staging formula merges two stage slots exactly once, which is what `bound2OwnLimit` closes and the obligation names.
- `dev/literature/devlin-II5.md:221` `live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for`. Read. D-10 anchor: classically the merged bound sits inside the limit; the obstruction measured here is naming, not truth.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. No classical text claim enters the deliverable beyond the D-10 note already sourced above.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used. Slot roles and Devlin II.5 cover every external citation this return makes.

- `dev/literature/primary-sources.md:23-24` "Extraction note: the Dev chapters
  are OCR scans (ABBYY), so math glyphs are degraded; the two load-bearing
  pages, Dev 236 (Basis Lemma list) and Dev 251 (J-recursion), were re-OCR'd
  with tesseract and cross-checked." Read 2026-08-27 as an amendment, sent back
  for the survey answer missing above; the source was not opened at write
  time. D-10 meaning is unchanged: the classical truth side rests on scans whose
  load-bearing pages were re-extracted and cross-checked, so the obstruction
  measured here stays a naming fact, not a truth fact.

Amendment scope, 2026-08-27, third dispatch: the LITERATURE bullet above,
cured author-side under the program's standing instruction that the citation
belongs in this file, and the stale decimals at the HEAD verdict, the ladder
table and the price table, each now citing what resolves today. No verdict,
claim or measurement above changed meaning.
