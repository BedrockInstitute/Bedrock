# LJ-1.47: can the square law's 41.36 seconds come down?

Status: COMPLETE. PROBE. No commit, no push. No master. The only written
deliverable is this report. ASD-STE100. All measurements are mine, at the
C-12 caliber `GHCRTS="-A64m -I0 -M8g"`, cold module (own interface moved
aside), warm dependencies, one process, quiet machine.

## 1. THE VERDICT

**YES, the class can change, and the measured delta is 5.45x on seconds.**
The square law at the 5.5 and 5.6 sites (the initial ordinals κ and κ⁺),
built fresh from the archived content, checks the pair in **7.94 s over
744 lines (0.0107 s per line)** against the archived pair's **43.26 s
over 1,278 lines (0.0338 s per line)** at the same caliber. The rate
drops into the P-m parameterized band (`dev/LESSONS.md:2460`). The wing
flips from 1.23x over the DD24 bar to 0.96x under it. The ω target
needs a separate small base on top (`CoreAtω`'s pieces or the FOL.Count
coding); it is outside the pair in both routes.

Two measured levers carry the change, and both are deletions of content
that nothing consumes:

1. **Four of the five general-law sections have no consumer.** `Core`,
   `Card`, `Shift` and the successor-step module
   (`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:295-810`) are
   never used by the archive's own deliverable (`InitialCore` at `:988`,
   `Initial` at `:1259`, the exports at `:1289-1299`) and nothing outside
   imports them. `CoreAtω` (`:830-893`) has one consumer: the ω-target
   base of the fixed-target theorem, which instantiates `InitialCore` at
   `ω` with `CoreAtω`'s hypotheses (`src/ProbeTowerInd.agda:74-76`).
   Cutting the four unneeded sections and `CoreAtω` takes the square-law
   module from **23.99 s over 902 lines to 8.59 s over 468 lines**
   (means of three runs each). The κ and κ⁺ sites of 5.5 and 5.6 sit
   strictly above `ω`, so they do not need `CoreAtω`; the ω target is a
   separate small base (see section 2).
2. **The order-type route is replaceable.** The archived pairing builds
   the order type `τ` as a V-set, then bounds `τ` into `α`
   (`archive/rud-route/src/L/Ordinal/Pairing.lagda.md:457-488`). One
   definition, `col→τ-fiber`, costs **18,363 ms of the Pairing module's
   19,481 ms profile** — 94.3 percent of the module. The collapse `col`
   already lands inside `α`: `InitialCore.col∈α`
   (`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:479-484`). So the
   pairing is the direct injection `p ↦ fiber α (col∈α p) .fst`,
   injective by `col-inj`. It never forms `τ`. The collapse-only module
   checks in **1.31 s over 319 lines**; the via-collapse square law in
   **6.63 s over 425 lines**.

The remaining hot term is `InitialCore.comp₀-inj` at **4,752 ms of the
via-collapse module's 6,272 ms profile** — the no-injection exclusion
chase, stated at the variable carrier `α`. That is the floor at this
tree: body-bound machinery at a variable carrier, one payment, not
further reducible by anything this probe measured.

The cure needs no `absFo` and no placed `Δ₀` (P-u). Its imports are the
archive's own: `V.*`, `L.Ordinal`, `L.WellOrder`, `FOL.ZFStructure`.
No heap exhaustion occurred at any point; every run exited 0 under the
C-12 cap.

P-n is NOT the answer, as the brief expected. The archived pair sits at
0.0338 s per line (my caliber), six to nine times below P-n's 0.22 to
0.297 floor (`dev/LESSONS.md:2483`). The class was never satisfaction at
a concrete carrier. It was the P-l family: parameterized content whose
hot statements build presentation machinery at transparent constructions
(`dev/LESSONS.md:2305`).

The old pair re-verifies. At my caliber, Pairing measures
19.54 / 19.26 / 19.01 s and SquareLaw 23.56 / 24.26 / 24.14 s, pair mean
43.26 s, against the ledger's 41.36 s measured at `-M16g`
(`dev/ledger.toml:252-253`). The difference is the caliber and machine
drift, inside the brief's predicted band. The 1,283 in-fence line count
re-verifies: 376 (Pairing) plus 907 (SquareLaw), counted from the
archive's fences.

## 2. WHAT THE CONSUMER ACTUALLY NEEDS

**The GCH chain needs the square law at INITIAL ordinals only, and at
exactly two of them: κ and κ⁺.** The digest states the single application
of 5.5 in 5.6 as `κ⁺` with `α = κ`
(`dev/literature/devlin-II5.md:164-166`). Both are cardinals. The chain
`|γ| = |M| = |L_κ| = κ < κ⁺` consumes the level size at `κ`, and 1.1(vii)
closes at `κ⁺` (`dev2.txt:1386-1388`). This was LJ-1.17-R's error-2
correction and I re-confirmed it at the source.

**The current interface is wider than the demand.** `L.StageCardinal`
takes `sq` at every infinite SET:
`sq : (α : V ℓ) → (⟨ α ∈ ω ⟩ → Empty.⊥) → sq α`
(`src/L/StageCardinal.lagda.md:14-17`). It consumes it at every infinite
ORDINAL: the `Bound` count at `β`
(`src/L/StageCardinal.lagda.md:59-66`), the successor step at `α`
(`:270-274`), the limit step at `α` (`:373-379`), and the ∈-induction
assembly over all ordinals (`:508-571`). The `Init`-restricted law cannot
discharge this wider interface at non-initial ordinals such as `ω + ω`,
and neither could the archived module
(`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:956-963`).

**The consumer reshaping is the review's route 1, priced but not built.**
The level-size theorem the wing needs is: for an initial `κ` and every
`β ≤ κ`, `⟪ Lset β ⟫ ↪ ⟪ κ ⟫`, with every square-law call at the target
`κ`. The successor half exists as the T85 probe, taking the pairing as
`Initial.square α iα` at `Init α`
(`src/ProbeTowerInd2.agda:99-104`, the fixed-target signature at
`:155-159`). The limit half is priced at 150 to 220 lines
(`_build/lj-1.6-review.md:124-126`), the whole reshaping at 200 to 280
lines (`_build/lj-1.17-review.md` route 1). That reshaping is not part
of this probe, but it is the interface the via-collapse law serves:
`via-col-square : (α : S) → Init α → sq α`.

**The two residuals survive unchanged.** `Init ω` is uninhabited
(`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:936-944`), so GCH
at `ω` still needs the elementary `ℕ × ℕ ↪ ℕ` coding separately
(`_build/lj-1.17-review.md` section 2.4). And `Init κ` must be verified
for each cardinal, or `Init` adopted as the cardinal notion
(`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:961-963`).

Devlin's assumption, in one line: he assumes the cardinal arithmetic of
1.1(vii) — `|L_λ| ≤ Σ_{α<λ} |α| = |λ|` at limits and "easily seen"
formula counts at successors — and proves none of it
(`_build/literature/dev2.txt:200-215`).

## 3. THE PROFILE ATTRIBUTION

Profiles (`agda --profile=definitions`, cold module, same caliber). The
Pairing profile is the measurement LJ-1.17-R requested and nobody ran
(`_build/lj-1.17-review.md` section 3.4).

| module | total | hot rows | share |
|---|---:|---|---:|
| Pairing (archived) | 19,481 ms | `col→τ-fiber` 18,363 ms | 94.3% in one definition |
| SquareLaw, minimal | 8,403 ms | `comp₀-inj` 5,231 ms, `τ⊆α` 1,534 ms | 80.5% in two definitions |
| SquareLaw, via-collapse | 6,272 ms | `comp₀-inj` 4,752 ms | 75.8% in one definition |

The gut experiment separates statement from body, per the LESSONS
protocol (`dev/LESSONS.md:2352-2362`): Pairing with `col→τ`,
`col→τ-fiber` and `col→τ-inj` replaced by same-typed postulates checks in
**1.35 s** against 19.27 s. The 18 s is BODY-bound — building
`fiber τ (col∈τ p)` at the transparent `τ` — not the statement's type.
The seal experiment confirms the once-payment: wrapping `τ` and its
consumers in one `opaque` block changed nothing (20.23 s, warning
"opaque block has no effect"). Sealing buys the repeats, never the once
(`dev/LESSONS.md:2357-2358`). The only cure is to stop building the
fiber at the built `τ` at all, which is what the via-collapse
construction does: it builds the fiber at the variable `α` instead.

The class attribution, whole:

| shape | lines | seconds | s per line | class |
|---|---:|---:|---:|---|
| Pairing, archived | 376 | 19.27 | 0.0513 | middle, once-payment |
| SquareLaw, archived | 902 | 23.99 | 0.0266 | middle, once-payment |
| pair, archived | 1,278 | 43.26 | 0.0338 | middle |
| dead general-law sections (Core, Card, Shift, successor, CoreAtω) | 434 | 15.40 | 0.0355 | middle, no κ/κ⁺ consumer |
| minimal SquareLaw | 468 | 8.59 | 0.0184 | middle |
| Collapse only | 319 | 1.31 | 0.0041 | parameterized |
| SquareLaw, via-collapse | 425 | 6.63 | 0.0156 | middle, one hot row |
| pair, via-collapse | 744 | 7.94 | 0.0107 | P-m band |

The line counts are non-comment lines of the probe files, within a few
lines of the in-fence caliber (the archived pair counts 1,278 against
the ledger's 1,283). Seconds are means of three cold runs, spread in
section 4.

## 4. THE MEASUREMENTS

All at `GHCRTS="-A64m -I0 -M8g"`, cold module, warm deps, one process.
Each run moved the module's own interface aside; dependencies stayed
warm. Every figure is the mean of three runs.

| probe | runs, s | mean, s | spread |
|---|---:|---:|---:|
| Pairing (archived) | 19.54 / 19.26 / 19.01 | 19.27 | 0.53 |
| SquareLaw (archived) | 23.56 / 24.26 / 24.14 | 23.99 | 0.70 |
| archived pair |  | 43.26 |  |
| SquareLaw, minimal (dead weight cut) | 8.43 / 8.73 / 8.61 | 8.59 | 0.30 |
| Collapse only | 1.37 / 1.25 / 1.31 | 1.31 | 0.12 |
| SquareLaw, via-collapse | 6.65 / 6.45 / 6.78 | 6.63 | 0.33 |
| via-collapse pair |  | 7.94 |  |
| Pairing, gutted (postulates) | 1.37 / 1.34 / 1.35 | 1.35 | 0.03 |
| Pairing, τ sealed | one run | 20.23 | n/a |
| Combinators (dependency) | 1.78 / 0.98 / 0.99 | 1.25 | 0.80 |

The archived pair re-verifies at 43.26 s mean against the ledger's 41.36 s
at `-M16g` (`dev/ledger.toml:252-253`), 4.6 percent higher, consistent
with the `-M8g` heap cap and machine drift. The 1,283 in-fence count
re-verifies exactly (376 + 907).

The wing arithmetic. DD24's bar is `0.011057 × 1.15 = 0.012716`
(`dev/ledger.toml:2590`, `:2810`). Using the brief's baseline, the GCH
side today is 6,459 lines at 79.95 s (`dev/ledger.toml` wing rows; the
figure is a residue from `[LJ-1.46]`).

| wing | lines | seconds | s per line | against the bar |
|---|---:|---:|---:|---:|
| GCH side today | 6,459 | 79.95 | 0.0124 | within |
| plus the archived pair | 7,742 | 121.31 | 0.0157 | 1.23x, over |
| plus the via-collapse pair | 7,203 | 87.89 | 0.01220 | 0.96x, PASS |
| plus via-collapse and the Combinators delivery | 7,486 | 89.14 | 0.01191 | 0.94x, PASS |

The verdict is robust to the baseline choice: with LJ-1.45's newer wing
figures (6,407 lines, 77.6 s), the via-collapse wing lands at 0.01196,
also under the bar; the archived pair lands at 0.0155, over.

The Combinators module (`prodSWO`, `natSWO`, 283 lines) is absent from
today's `src/L/WellOrder/` and must be delivered with the port
(`_build/lj-1.17-report.md` section 7). It is outside the counted pair in
both routes.

## 5. DD4

The via-collapse square law is the same template content as the archive.
Its statements range over `V.*`, `L.Ordinal`, `L.WellOrder` and
`FOL.ZFStructure`, with no Def-tower object in any type. The collapse
orders `⟪ α ⟫ × ⟪ α ⟫` through the ordinal's own membership and
regularity; the exclusion chase is generic in `α`. Nothing is
Def-specific. **A cure here pays twice**: the J tower inherits the same
square law unchanged, at the same 7.94 s, and the template is shared
(`dev/literature/devlin-II5.md:385-397`). A failure here would have cost
twice as well; the probe's verdict is a gain.

D-26 bears in one line: NO. The square law well-orders the product of an
ordinal's index through regularity on `V`; it needs no generation data
and no syntax (`dev/LESSONS.md`, D-26 rule bundle). D-26's requirement
applies to well-ordering a tower's stage, which is the descent, a
different row.

## 6. ARCHIVE USED

- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md`: read WHOLE.
  Took the module skeleton (`:51-93` `AbstractH₀`, `:103-266`
  `FiniteBase`, `:988-1257` `InitialCore`, `:1259-1286` `Initial`,
  `:1289-1299` the exports). Took the `Init` boundary and the non-initial
  gap (`:918-963`), the `sq`/`Init` types (`:969-984`), and the
  general-law sections (`:295-893`, `CoreAtω`'s ω-base consumer at
  `src/ProbeTowerInd.agda:74-76`). The probe files extract verbatim
  content and re-point two imports.
- `archive/rud-route/src/L/Ordinal/Pairing.lagda.md`: read WHOLE.
  Took the well-order (`:120-293`), the collapse (`:333-353`), the order
  type and the `col→τ` family (`:457-488`), the surjectivity
  certificates (`:490-576`), and the `Pairing` module (`:605-612`).
- `_build/lj-1.17-report.md` and `_build/lj-1.17-review.md`: read WHOLE.
  Took the measurement protocol and the 41.36 s pair, the correction
  (the wing's application is at initial ordinals only), the fixed-target
  route-1 reshaping, and the unrun profile request.
- `_build/lj-1.46-report.md` and `_build/lj-1.21-report.md`: read WHOLE.
  Took the `sq` parameterization history and the StageCardinal
  assembly shape.
- `src/ProbeTowerInd2.agda:99-159`: the fixed-target successor shape and
  its `Initial.square α iα` consumption of the law.
- `src/ProbeLJ117Pairing.agda`, `src/ProbeLJ117SquareLaw.agda`,
  `src/ProbeLJ117Combinators.agda`: the LJ-1.17 scratch extractions,
  reused as the archived-pair measurement base.
- `dev/ledger.toml:252-253` (the pair), `:2589-2610` (the module
  baseline 0.011057), `:2810` (tolerance 1.15), `:2376-2382` (the
  col→τ-fiber once-payment record).
- `dev/LESSONS.md`: P-l (`:2305`), P-m (`:2460`), P-n (`:2483`), P-t
  (`:2601`), P-q (`:2633`), P-v (`:3037`), whole; the gutted-body
  protocol (`:2352-2362`) and the once-payment (`:2357-2358`).

Nothing else in `archive/` was read. WHY NOT: the remaining archived
rows and modules are other crossings that do not bear on the square law.

## 7. LITERATURE USED

- `dev/literature/devlin-II5.md:164-166`: the single application of 5.5
  in 5.6 at `κ⁺` with `α = κ`. TOOK: the initial-only consumer claim.
- `dev/literature/devlin-II5.md:145-158`: the 5.5 chain, `:272-284`
  steps E and F, `:385-397` the DD4 table, `:411-417` the J analogue.
- `_build/literature/dev2.txt:200-215`: 1.1(vii)'s proof, nine printed
  lines, no cardinal arithmetic. TOOK: Devlin's assumption boundary.
- `_build/literature/dev2.txt:1386-1388`: 5.6's proof. TOOK: the
  `|L_{κ⁺}| = κ⁺` close.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids re-checking.
- `dev/literature/j-hierarchy.md`, `jech13.txt`: NOT read. WHY NOT: the
  J-side size analogue and the Jech cross-check do not change the
  ordinal arithmetic underneath, which is the whole subject here.

## 8. WHAT I AM NOT SURE OF

1. The wing baseline. The brief's 6,459 lines / 79.95 s is a residue
   from `[LJ-1.46]`; LJ-1.45's in-flight cure reads 6,407 / 77.6. Both
   pass with the via-collapse pair and fail without it, so the verdict
   does not turn on the choice.
2. The consumer reshaping is not built. The via-collapse law serves the
   `Init`-shaped interface; the current `L.StageCardinal` parameter at
   every infinite ordinal still cannot be discharged at non-initial
   sites. The route-1 reshaping (200 to 280 lines, priced by
   LJ-1.17-R) is the gate that makes the cure usable, and its limit half
   is unmeasured.
3. The probe files are verbatim archived extractions with two
   re-pointed imports. The real masters carry prose, literate overhead
   and the Combinators delivery (`prodSWO`, `natSWO`, absent from
   today's tree). I measured Combinators at 1.25 s over 283 lines; it is
   not in the counted pair in either route.
4. `Init κ` verification remains the review's residual: either prove
   the three initiality clauses at the actual cardinals, or adopt
   `Init` as the cardinal notion. Unchanged by the cure.
5. The square law at `ω` (for GCH at `ω`) is still separate elementary
   content, unpriced here.
6. The `-M8g` versus `-M16g` caliber. My re-verification reads 4.6
   percent higher than the ledger's archived figure. The comparison of
   the cure uses the same caliber on both sides, so the verdict is
   unaffected; the absolute numbers would shift slightly at `-M16g`.

Probe files created for this probe, untracked by standing rule:
`src/ProbeLJ147SquareLawMin.agda`, `src/ProbeLJ147Collapse.agda`,
`src/ProbeLJ147SquareLawViaCol.agda`, `src/ProbeLJ147PairingSealed.agda`,
`src/ProbeLJ147PairingGut.agda`. Interfaces moved aside into
`/tmp/lj147-agdai-stash/`. No master, no `dev/` file, no commit.
