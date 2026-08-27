# LJ-1.691 report: the three site facts the bridge still takes

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.691
obligation: agents/tasks/LJ-1-691/Probe691.agda::site-facts

## 0. VERDICT

**NO-GO.** The briefed obligation, the universal `site-facts` term
`[LJ-1.681]`'s `bnd-vs-unbnd` takes as hypotheses, is FALSE at an
allowed site and cannot be built: its first row, `fK` (witness-in-K),
says every element of the class carrier lies in the `K` slot of the
environment, and at the environment `∅ʟ ∷ ∅ʟ ∷ []` that slot is the
coded empty set, so `fK` asserts `∅ ∈ ∅`, which the landed `∅-empty`
discharges to a contradiction. The refutation `fK-void` stands in
`agents/tasks/LJ-1-691/Probe691.agda:114-131`, typechecked green,
`runs/p-1.out`, exit 0.

## 1. DELIVERED

1. `agents/tasks/LJ-1-691/Probe691.agda`, green, `--safe`, no
   postulate, no hole. Section 1 (`:59-103`) carries the three site
   facts verbatim the frame of `Probe681.agda:56-95`: `fK`, `domOut`,
   and the four leaf rows, bound into `Facts.SiteFacts`. Section 2
   (`:105-131`) is the refutation `fK-void`, carrying the two
   `Lset-defines` hypotheses of the composition context and
   discharging them unused.
2. `agents/tasks/LJ-1-691/review-of-site-facts.md`, the NO-GO with
   site, counterexample, and cost facts.
3. `runs/floor-1.out` and `runs/FLOOR.agda.txt`, the measured floor
   (frame with the designed hole, 1.84 s, 571 MiB), and the variant
   runs `runs/V*.out`, `runs/T*.out` that locate the cost anomaly in
   item 3 below.

## 2. WHY THE NO-GO IS VALID AT THE OBLIGATION'S FRAME

The obligation inherits its frame from the bridge.
`agents/tasks/LJ-1-681/Probe681.agda:56-57` puts the bridge in one
module over `{n : ℕ} (w b K : Fin n) (γ : S ^ n) (ψs ψa)`: the six rows
are hypotheses of a term that is UNIVERSAL in the environment. A term
called `site-facts` that fills those rows must therefore hold at every
allowed environment, and the all-`∅ʟ` environment is allowed: the
frame names no constraint on `γ` beyond the two `Lset-defines` rows,
and those constrain the `w` and `b` slots, not `K`. The refutation at
one allowed environment (n = 2, `K` split on its two values) closes
the universal obligation as false. This is the `[LJ-1.532]` pattern
(agents/tasks/LJ-1-532/review-of-approx-in-K.md:1-8), the same stop
shape at a different site.

## 3. COST ANOMY AT THIS SITE (MEASURED, LOCAL)

Passing the membership witness to `∈∈ₛ .fst` through a `subst` redex
in body position drives the checker past the 2.1 GiB heap wall in
80 to 103 s (`runs/V5.out`, `runs/V5d.out`, `runs/V5b.out`). Passing
the neutral `fst s ∅ʟ` from a `K`-split clause typechecks the same
proof in 2.02 s (`runs/V5e.out`). The delivered file uses the neutral
spelling. This is a measurement of one site. It does not transfer by
analogy, and the next body that touches `∈∈ₛ` at another site should
re-measure it there before pricing.

## 4. WHAT THE NO-GO PRICES

The GO branch of the composition (`Lset-defines` to `bnd-vs-unbnd`
to `graphBndAt`) required the six rows to hold at the canonical
bounded-graph environment. The universal reading is dead. The
corrected reading, which `[LJ-1.681]` itself names in its comment on
`fK` ("the corrected statement is that this is the canonical
approximation, not an arbitrary one", `Probe681.agda:68-69`), still
stands: a CANONICALITY hypothesis in place of the unbounded `fK`,
priced against the `KFacts` wall the 681 header references
(`Probe681.agda:12-15`). Per law C-42 the sweep (counting the other
sites that carry the same false shape) is the next action and is not
done here.

## 5. MEASUREMENTS

| run | content | result |
|---|---|---|
| `runs/floor-1.out` | frame with the designed hole | 1.84 s, 571 MiB, exit 42 (the hole only) |
| `runs/p-1.out` | the delivered file | 2.50 s, 577 MiB, exit 0 |
| `runs/V5e.out` | refutation, fK-only frame | 2.02 s, 578 MiB, exit 0 |
| `runs/V5.out`, `runs/V5d.out`, `runs/V5b.out` | `subst` spelling of the same proof | 2.1 GiB wall, exit 251 |
| `runs/V8.out` | `∈∈ₛ .fst` in isolation | 0.94 s, exit 42 (hole only) |

## 6. WHAT I DID NOT DO

I did not build `site-facts`. I did not land in `src/`. I did not
postulate: `grep -c postulate agents/tasks/LJ-1-691/Probe691.agda`
returns 0. I did not spend a `Σ₁` certificate. I deleted the scratch
probes; their measured outputs stand in `runs/`.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: not read, declined; program record, not
  mathematical content, not needed for this refutation.
- `archive/dev/DD-archived.md`: not read, declined; ditto.
- `archive/dev/PLAN-archived.md`: not read, declined; ditto.
- `archive/dev/STATUS-archived.md`: not read, declined; ditto.
- `archive/dev/TASKS-archived.md`: not read, declined; ditto.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: not read, declined;
  glossary review, no term question arose in this task.
- `dev/literature/level-formula-slot-roles.md`: not read, declined; the
  level questions here resolved against the tree itself.
- `dev/literature/devlin-errata.md`: not read, declined; no Devlin
  statement was in play.
- `dev/literature/primary-sources.md`: not read, declined; ditto.
- `dev/literature/BIBLIOGRAPHY.md`: not read, declined; ditto.
