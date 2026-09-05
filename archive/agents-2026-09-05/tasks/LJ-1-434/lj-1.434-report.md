# LJ-1.434 report: does a truncated square law reach the bounded-subset conclusion

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-434/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-434/Probe434.agda`:

    bounded-from-trunc :
        ∥ ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
             → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
                 ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)) ∥₁
      → ⟨ x ∈ˢ Lset κ ⟩

## D-10, BEFORE ANY AGDA

`⟨ x ∈ˢ Lset κ ⟩` is an hProp. Evidence:

- `𝒮ᵥ` sets `_∈ˢ_ = _∈_` at `src/V/Hierarchy.lagda.md:83`.
- `_∈ˢ_ : S → S → Ω` at `src/FOL/ZFStructure.lagda.md:48`.
- For `hPropAlgebra`, `Ω = hProp ℓ` at `src/Base/Truth.lagda.md:98`.
- `⟨_⟩` projects the underlying type (`src/Base/Prelude.lagda.md:141`).
- The proposition-hood proof is `P .snd` (`src/Base/Prelude.lagda.md:134`).
  So `snd (x ∈ˢ Lset κ)` is `isProp ⟨ x ∈ˢ Lset κ ⟩`.

The chapter itself spends that witness, one line above the conclusion:

    x∈Lκ = PT.rec (snd (x ∈ˢ Lset κ)) go (cover x x∈M)

at `src/L/BoundedSubset.lagda.md:1606`. The conclusion is
`theorem : ⟨ x ∈ˢ Lset κ ⟩` at `src/L/BoundedSubset.lagda.md:1621`, and it
equals `x∈Lκ`.

The unique-choice case of the digest applies: if `P` is a mere proposition
then `P ≃ ∥ P ∥` (`dev/literature/truncation-and-selection.md:92`). So one
outer `PT.rec` into this conclusion is legal.

## PREDECESSOR TYPES

- `[LJ-1.407]` is GO (`agents/tasks/LJ-1-407/lj-1.407-report.md:18`). The
  delivered type is a FAMILY OF TRUNCATIONS
  (`agents/tasks/LJ-1-407/Probe407.agda:273-280`). This task does not inhabit
  that type.
- `[LJ-1.408]` is NO-GO (`agents/tasks/LJ-1-408/lj-1.408-report.md:12`). The
  refuted type is `pair-cross`
  (`agents/tasks/LJ-1-408/Probe408.agda:58-64`). This task does not inhabit
  that type.

## VERDICT

**GO.** The obligation typechecks (`agents/tasks/LJ-1-434/Probe434.agda:127-128`,
exit 0, median 15.01 s on three forced rechecks) and it PASSes the program's
witness meter (`scripts/pod/witness.py --code LJ-1-434 --brief
agents/tasks/LJ-1-434/LJ-1.434.md`, exit 0, 3.69 s, 0 UNRESOLVED of 1,
`probe_red=False`). The body is one `PT.rec` of the chapter's own `theorem`,
with the chapter's own witness `snd (x ∈ˢ Lset κ)`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that collection.
It does not start phase 3. No Boundary clause is in conflict.

## 1. What was built

All in `agents/tasks/LJ-1-434/Probe434.agda`, module
`LJ-1-434.Probe434 {ℓ} (lem)`.

- `SqFam` (`:44-48`), the consumer's square-law family, copied from
  `src/L/BoundedSubset.lagda.md:1388-1390`.
- `Distance` (`:54-59`), the named residue. A type. Not inhabited.
- `Instantiation` (`:67-91`), W3: `sq` as PLAIN data, two module
  applications (`BSA`, `Co`), `theorem = C.theorem`.
- The truncated form (`:100-128`): every parameter of `BoundedSubsetAt`
  and of `Co` except `sq`, then `bounded-from-trunc`.

## WHERE THE CHAPTER SPENDS sq

Command, as the brief named it:

    grep -n "sq " src/L/BoundedSubset.lagda.md src/L/StageCardinal.lagda.md

COUNT of matching lines: 4.

| file:line | what | ordinal |
|---|---|---|
| `src/L/BoundedSubset.lagda.md:1388` | declaration of the module parameter | none (binder) |
| `src/L/BoundedSubset.lagda.md:1410` | `SC.Bound` applied at `(sq α (self∈sucV α) α∉ω)` | BoundedSubsetAt's own `α` only |
| `src/L/StageCardinal.lagda.md:17` | declaration of the module parameter | none (binder) |
| `src/L/StageCardinal.lagda.md:283` | `Bound` applied at `(sq α α∈suc infα)` inside `LimitStep` | `LimitStep`'s own `α` |

The space-pattern misses `src/L/BoundedSubset.lagda.md:1397`,
`module SC = L.StageCardinal {ℓ} lem α ordα sq`, because `sq` sits at the
end of the line. That line threads the whole family into StageCardinal.
It does not read the family at an ordinal.

`src/L/BoundedSubset.lagda.md:1513` has no `sq`. It calls
`stage-card-upper α ordα (self∈sucV α) α∉ω`. That term is
`∈-induction step` (`src/L/StageCardinal.lagda.md:566`). Each inductive
step calls `limit-step`, and `limit-step` spends `sq` at
`src/L/StageCardinal.lagda.md:283`. So the upper-bound call at 1513
reads the family at every ordinal the induction visits under `sucV α`,
not at one ordinal.

**One site reads the parameter at more than one ordinal:**
`src/L/StageCardinal.lagda.md:283`, through the induction at
`src/L/BoundedSubset.lagda.md:1513`.

That does not block a truncated FAMILY. One outer `PT.rec` opens the
whole family as data. Every inductive step then reads the SAME family.
No site compares two pairings. `[LJ-1.408]`'s two-truncation reading
does not arise.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `κ`, `α`, `x` and `lam` stay parameters. No ordinal is
fixed. The only change to the telescope is that `sq` moves under
`∥ ∥₁`. `UnionKit` and `HullStage` are the chapter's own modules, applied
at those same generic arguments. They take no `sq`
(`src/L/BoundedSubset.lagda.md:1145-1148` and `:903-905`), so Co's two
hypotheses can sit outside the truncation. No extra hypothesis was added.

## STEP ONE, THE INSTANTIATION

**GO.** `Instantiation` (`Probe434.agda:67-91`) takes `sq : SqFam α` as
data and applies `Devlin55.BoundedSubsetAt` then `BSA.Co`. The obligation
is omitted. Three runs, interface removed before each, dependencies
warm: 6.58 s, 6.50 s, 6.55 s. Median **6.55 s**, exit 0 every time.
First run printed `Checking`. `runs/w3-{1,2,3}.out`. The first run is
the alone-run price.

## STEP TWO, THE OBLIGATION

**GO.** `sq` moves under one `∥ ∥₁`. The body is

    PT.rec (snd (x ∈ˢ Lset κ)) go h

at `Probe434.agda:128`, and `go` is `Instantiation.Co.theorem` at the
opened family (`:118-125`).

Co's hypotheses mention `HS.C.πX` and `HS.M`. Those names live inside
`BoundedSubsetAt`, which takes `sq`. `UnionKit` and `HullStage` do not
take `sq`, so the probe instantiates them at the site (`:109-110`) and
types `levelIn` and `cover` there. The inner `BSA.HS` is the same
application at the same arguments. The types matched. No `refl` between
two module applications was written. `[LJ-1.163]` measured a wall on
that identification (`agents/tasks/LJ-1-164/ProbeLJ1164A.agda:27-30`).
This probe does not write it.

## THE DISTANCE, AS ONE TYPE

GO moves the campaign's residue to this type, at
`agents/tasks/LJ-1-434/Probe434.agda:54-59`:

    Distance : (α : S) → Type (ℓ-suc ℓ)
    Distance α =
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
          → ∥ Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
                ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v) ∥₁)
      → ∥ SqFam α ∥₁

The domain is `[LJ-1.407]`'s `ConsumerShape`
(`agents/tasks/LJ-1-407/Probe407.agda:273-277`). The codomain is the
hypothesis of `bounded-from-trunc`. This is HoTT Book AC 3.8.1,
`(∏x ∥Y x∥) → ∥∏x Y x∥`
(`dev/literature/truncation-and-selection.md:227`), at this index.
`[LJ-1.391]` already returned NO-GO on inhabiting it
(`agents/tasks/LJ-1-391/lj-1.391-report.md:18-20`).

This task does not claim the distance is small. It does not claim the
distance is closed. It does not inhabit `Distance`.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root.

- W3 alone, three runs: 6.58 s, 6.50 s, 6.55 s. First run printed
  `Checking`. Median **6.55 s**, exit 0. `runs/w3-{1,2,3}.out`.
- Full file, first check after the obligation landed: 14.84 s, exit 0,
  printed `Checking`. `runs/full-1.out`.
- Full file, three forced rechecks (the probe interface removed before
  each run, dependencies warm): 14.89 s, 15.01 s, 15.09 s. Median
  **15.01 s**, exit 0 every time. Each printed `Checking`.
  `runs/full-recheck-{1,2,3}.out`.
- After the anonymous-module lift that the witness meter needs: 15.22 s,
  exit 0. `runs/full-2.out`.
- Witness meter, one obligation: PASS, exit 0, 3.69 s, 0 UNRESOLVED of 1,
  `probe_red=False`. `runs/witness-1.out`.

Estimate for the Agda: about 45 code lines, a comparable of SHAPE from
`src/L/BoundedSubset.lagda.md:1385-1402`. Measured, non-blank
non-comment lines in the probe are 76, of which `SqFam` is 5, `Distance`
is 6, `Instantiation` is 21, and the truncated form is 24. Nothing is
funded against the estimate.

## 3. What GO earns, and what is still owed

GO says the bounded-subset lemma needs no pairing as data at the
module boundary. It needs a truncated family. Every use of the pairing
inside the module then happens under one opened witness, including the
many-ordinal spend at `src/L/StageCardinal.lagda.md:283`.

What this task does not settle:

- It does not join `[LJ-1.407]`'s family of truncations to this truncated
  family. That join is `Distance` (`Probe434.agda:54-59`).
- It does not inhabit `Distance`.
- It does not pay `levelIn` or `cover`. They stay module parameters,
  copied from `module Co`.
- It does not edit `src/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used. Retired-route
  journal. The consumer is the live `BoundedSubset` chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history of
  this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined, not
  used. The live clauses that bound this slot are W2 and W3.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read at `:92`. Quote:
  `HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.`
  Used: that is why one `PT.rec` into `⟨ x ∈ˢ Lset κ ⟩` is legal. Also
  read at `:227`. Quote: `(∏x ∥Y x∥) → ∥∏x Y x∥`. That is `Distance`.
  Also read at `:229`. Quote:
  `that consumes `f` is not a proposition, AC does not help.** This is worth`
  The conclusion here IS a proposition, so the rec is the digest's free
  case. The remaining join is AC 3.8.1, which this task does not pay.
- `dev/literature/devlin-II5.md`: read at `:1`. Quote:
  `# Devlin II.5: the Condensation Lemma and the GCH in L`. Declined, not
  used. This probe measures a `PT.rec` at the live chapter, not II.5's
  prose.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`. Declined, not used.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `Distance`.
- I did not write `review-of-bounded-from-trunc.md`. The verdict is GO.
