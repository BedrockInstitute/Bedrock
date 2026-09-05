# LJ-1.417 report: the rank becomes an injection into an ordinal, untruncated

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-417/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`. I did
not set `GHCRTS`. ONE Agda process at a time. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-417/Probe417.agda`, at a
GENERIC small type `A` with a GENERIC well-order on it:

    swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))

There is no `∥ ∥₁` in that type. The rank hypotheses sit as module
parameters at `[LJ-1.416]`'s types. I did not import `Probe416`. I did
not rebuild the rank.

## VERDICT

**GO.** The obligation typechecks (`agents/tasks/LJ-1-417/Probe417.agda`,
exit 0, 36.55 s real, `runs/full-1.out`). The program's witness meter
closed the name (`runs/accept-1.out`: conjuncts 1-5 held,
`obligations_delta` -1, `obligations_open` 0, `witness_seconds` 0.91).
The type of `swo-into-ord` carries no `∥ ∥₁`. The rank is enough.
Accept conjunct 6 was red on the first return because this file had no
`ARCHIVE USED` or `LITERATURE USED` heading. Those sections are below.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in conflict.

## 1. D-10, before the Agda

The target is true at this generality. `tri∙` decides the order
(`src/L/WellOrder/Base.lagda.md:104`). `∈-irrefl` refutes the two
strict cases (`src/V/Hierarchy.lagda.md:155`). `irr∙` is a field of
`SWO` (`src/L/WellOrder/Base.lagda.md:105`) and is not spent:
monotonicity plus equality of ranks yields self-membership of an
ordinal, not `a <∙ a`. `boundingOrd` returns a pair, not a truncated
existence (`src/L/Ordinal.lagda.md:155`). Nothing in the type selects
a witness.

Corrected target: none. The stated type stands.

## 2. W3: `rank-inj`, first

**GO.** The brief named injectivity of the rank as the widest unmeasured
term. The probe is `rank-inj` (`Probe417.agda:60-74`).

```agda
rank-inj : (a b : A) → swo-rank a ≡ swo-rank b → a ≡ b
```

The body splits on `tri∙ a b`. The case `a <∙ b` sends `swo-rank-mono`
along `sym p` and dies at `∈-irrefl (swo-rank a)`. The case `b <∙ a` is
the mirror. The remaining case is `a ≡ b`. There is no induction.

**FIFTEEN non-blank code lines** for `rank-inj` (`Probe417.agda:60-74`).
The estimate was about 8. The extra lines are the two named `loop`
helpers and their types. The shape matches `κ-min-at`
(`src/L/Cardinal.lagda.md:145`): one trichotomy split and two
irreflexivity refutations. The live tree does not derive injectivity
from order-monotonicity. The archived pairing does, at the same shape:
`col-inj` at
`archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:424-432`
splits on `tri≺` and dies at `∈-irrefl`. That is the route this task
replaces, not a live lemma.

I stated and proved `rank-inj` before the Sigma in the same file
(`:60-74` before `:80-98`). One Agda process typechecked the complete
probe (`runs/full-1.out`, exit 0, 36.55 s). I did not start a second
process to re-check `rank-inj` in isolation. The W3 risk was the
trichotomy split, not a level wall, and the split closed in that run.

## 3. The Sigma

`swo-into-ord` (`Probe417.agda:80-98`) applies `boundingOrd A swo-rank
swo-rank-ord` (`src/L/Ordinal.lagda.md:154-156`). The first component is
`β`. The second is `IsOrd β`. The third says every `swo-rank a` is a
member of `β`. `fiber` (`src/V/Presentation.lagda.md:34-35`) turns that
membership into a point of `⟪ β ⟫`. Injectivity of the fibre map is
`rank-inj` after the two `fiber` second components and `cong (⟪ β ⟫↪)`.

**SEVENTEEN non-blank code lines** for `swo-into-ord`
(`Probe417.agda:80-98`). Together with `rank-inj`, **THIRTY-TWO
non-blank code lines**. The estimate for the whole obligation was about
25. The extra lines are named locals (`β`, `ordβ`, `memβ`, `toMem`, the
two `loop` helpers).

The type of `swo-into-ord` is the brief's type, verbatim. No `∥ ∥₁`
appears in the Agda (`Probe417.agda`; the one `∥` in the file is a
comment at `:11`).

## 4. The promotion to `↪`

The tree's `_↪_` is already a function with an injectivity proof:

```agda
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)
```

`src/L/StageCardinal.lagda.md:221-222`. The same Sigma sits at
`src/L/Cardinal.lagda.md:47-48`. The consumer at
`src/L/StageCardinal.lagda.md:565` uses that `_↪_`.

The probe copies the definition (`Probe417.agda:41-42`). The inhabitant
is the pair `(toMem , toMem-inj)` (`Probe417.agda:81`). **The pairing is
the promotion.** There is no further lemma. Cubical `isEmbedding` is a
different type and the consumer does not ask for it.

D-10 said: do not weaken `_↪_` to a bare function with an injectivity
proof if the promotion fails. The consumer's `_↪_` **is** that pair. I
did not weaken. I did not stop.

A Cubical promotion `injEmbedding : isSet A → isSet B → ... →
isEmbedding f` would need `isSet A`. `SWO` does not supply it. That fact
is not a wall for this task, because the consumer type does not mention
`isEmbedding`.

## 5. W2

The term is generic in `A` and in `w`. The outer module is generic in
`ℓ`. The 417 brief names the three rank hypotheses
(`agents/tasks/LJ-1-417/LJ-1.417.md:20-24`) and forbids importing
`Probe416`. I opened the predecessor in the sibling worktree. 416's
report is not NO-GO and does not name the statement FALSE: W3 is GO and
the obligation is still pending. The types in that probe, which I took
as module hypotheses (`Probe417.agda:47-50`), are:

- `A : Type ℓ`
- `w : SWO {ℓc = ℓ} A` at `ℓₚ = ℓ-suc ℓ`
- `swo-rank : A → S`
- `swo-rank-ord : (a : A) → IsOrd (swo-rank a)`
- `swo-rank-mono : (a b : A) → SWO._<∙_ w a b → ⟨ swo-rank a ∈ˢ swo-rank b ⟩`

Those match 416's W3-green probe. This task does not inhabit them. It
assumes them. The 417 brief says that if 416 returned NO-GO this task
still runs (`LJ-1.417.md:22-25`). 416 has not returned NO-GO.

No stage, no cardinal, no numeral and no `Lset` is named. `[LJ-1.418]`
does the instantiation. W2 holds.

Levels used, for the table `[LJ-1.416]` asked `[LJ-1.417]` to carry:

| quantity | level |
|---|---|
| carrier `A` | `ℓ` |
| order `_<∙_` | `ℓ-suc ℓ` |
| `boundingOrd` index | `Type ℓ`, instantiated at `A` |

I did not move any of the three. This task assumes the rank. It does not
re-measure whether the rank elaborates at these levels.

`swo-rank-ord` is spent only by `boundingOrd`. `rank-inj` spends
`swo-rank` and `swo-rank-mono`.

## 6. Literature, section 1

The rank is a **different device** from the classical least-witness.

Section 1 records that Devlin, Jech, and Schindler-Zeman each SELECT a
least witness under a definable well-order
(`dev/literature/truncation-and-selection.md:14-18`). The three agree
on the device: a definable well-order plus a universal guard, which
turns "some witness" into "THE witness"
(`dev/literature/truncation-and-selection.md:67-70`).

This term selects nothing. It computes a rank, bounds the image, and
reads the bound as a pair (`src/L/Ordinal.lagda.md:155`). No predicate
is being witnessed. No guard is being written. No `leastOf` and no
`PT.rec` appear.

Section 1.5 notes that a classical cardinal inequality is truncated
existence of an injection
(`dev/literature/truncation-and-selection.md:75-81`). The campaign spent
five dispatches trying to untruncate a selection. The 417 brief names
that record at `agents/tasks/LJ-1-391/lj-1.391-report.md:33-38`. That
path is not in this worktree. This route does not meet that wall,
because the bound is already a pair.

The live chapter `src/L/Rank.lagda.md` is a different device: membership
rank of a set, by `∈-induction` (`src/L/Rank.lagda.md:4-7, 92-93`). It
is not a well-order rank and this term does not use it.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:424`.
  Read. Used as the shape comparable. Quote:
  "col-inj : {p q : Pair} → col p ≡ col q → p ≡ q"
  That is trichotomy plus membership irreflexivity. The present
  `rank-inj` is that shape at a generic well-order.
- `archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:486-488`.
  Read. Used as the fibre promotion. Quote:
  "col-inj (sym (col→τ-fiber p) ∙ cong (⟪ τ ⟫↪) e ∙ col→τ-fiber q)"
  The present `toMem-inj` is that read.
- `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:23`.
  Read. The 417 brief names this file as the pairing route this task
  replaces. Quote:
  "col-mono; col-inj; col-img; τ; module Pairing"
  Used only as the name of the retired consumer. Not imported.
- `archive/dev/LJ-dispatch-index.md:168`. Read. Quote:
  "Probe the order-type module"
  That row is a probe of the pairing order-type, not a well-order rank
  at a generic carrier. Not used as a lemma.
- `archive/dev/JOURNAL.md`. Declined. Not used. The per-episode
  journal is retired. This task does not consult it.
- `dev/ARCHIVE.md`. Declined. Not used. This task does not retire a
  module.
- `archive/dev/TASKS-archived.md:8`. Read the opening. Declined. Quote:
  "Nothing here is a live task. Read it for history."
- `archive/dev/JOURNAL-archived.md:1`. Read the opening. Declined.
  Quote: "Archived journal: the retired route"
- `archive/dev/DECISIONS-archived.md:1`. Read the opening. Declined.
  Quote: "Archived decisions: the D series"

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:68`. Read section 1.
  Used. Quote:
  "The selection device is a definable well-order plus a universal guard."
  The rank is not that device. This term selects nothing.
- `dev/literature/devlin-II5.md`. Declined. Not used. This assembly
  selects nothing and does not rest on condensation.
- `dev/literature/terms-2026-08.md`. Declined. Not used. This task
  writes no glossary entry.
- `dev/literature/geology.md`. Declined. Not used. Geology is not this
  term.
- `dev/literature/digest.md:1`. Named. Not required. Read the opening.
  Not used. Quote:
  "Digest: the orthodox form of the rud route, pinned from the collected literature"
- `dev/literature/j-hierarchy.md`. Named by the brief and not required.
  Declined. Not used.
- `dev/literature/BIBLIOGRAPHY.md`. Named by the brief and not required.
  Declined. Not used.

## 7. What the next brief needs

`[LJ-1.418]` instantiates at the tower. This task measured that the rank
is enough: if `swo-rank`, `swo-rank-ord` and `swo-rank-mono` exist at
`[LJ-1.416]`'s types, then `swo-into-ord` is data and untruncated.

Whether the rank is **buildable** is `[LJ-1.416]`'s question, not this
one. If `[LJ-1.416]` returned NO-GO, the present GO still stands. The
two questions are separate.

The consumer's type is `⟪ Lset α ⟫ ↪ ⟪ α ⟫`
(`src/L/StageCardinal.lagda.md:565`). The generic term is `A ↪ ⟪ β ⟫`.
The instantiation must supply a small `A` and a well-order on it, then
transport the bound. Nothing in this probe names that site.

What the statement cost: 32 non-blank code lines for `rank-inj` plus
`swo-into-ord`, 36.55 s for the one typecheck, 0.91 s for the witness.
What the shape resisted: nothing. What I had to weaken: nothing. What I
could not close: nothing.
