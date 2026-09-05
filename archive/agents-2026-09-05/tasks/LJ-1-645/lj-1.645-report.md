# [LJ-1.645] report: can the chapter take the CODED cardinal

## HEAD

head_slot: coder
machine: shared
task: LJ-1.645
obligation: agents/tasks/LJ-1-645/Probe645.agda::beta-in-kappa-coded
verdict: **NO-GO** (stated in `review-of-beta-in-kappa-coded.md`)

- caliber on every run: `GHCRTS=-A64m -I0 -M2g` (wide tier), which the program
  set on this pane; every `.out` records it. I did not set it and never raised it.
- one Agda process at a time; no parallelism in this dispatch.
- nothing lands in `src/`. No commit, no push.

## THE OBLIGATION IN ONE LINE

Restate `src/L/BoundedSubset.lagda.md:1710-1719` (`β∈κ`) with the ambient
`cardκ : IsCardinal κ` replaced by the coded `cardκL : IsCardinalL (κ , isLκ)`,
every other site hypothesis unchanged. The term is uninhabitable: each of its
two `Empty.rec` branches must convert an AMBIENT composite injection to a CODED
one, and the shared leg `β↪α` defeats that conversion.

## PREMISE 1, RE-DERIVED

`grep -n 'cardκ' src/L/BoundedSubset.lagda.md` returns exactly five lines, and I
re-derived the count:

- `:1386` — the binder `(cardκ : IsCardinal κ)` on `BoundedSubsetAt`.
- `:1713` — USE 1, the `β ≡ κ` branch of `β∈κ`: `Empty.rec (cardκ α α∈κ …)`.
- `:1717` — USE 2, the `κ ∈ β` branch of `β∈κ`: `Empty.rec (cardκ α α∈κ …)`.
- `:1746` — the `BSA634` alias-module signature, which takes `cardκ` and
- `:1751` — forwards it: `= Devlin55.BoundedSubsetAt κ ordκ cardκ …`.

One binder, two forwardings, two uses. There is no third use. The brief is
right.

## THE FLOOR

The floor is the frame — the full `BoundedSubsetAt` telescope, the opened `Co`
module (which yields `β`, `β↪α`, `πX↪α`), and the coded cardinal at the same
`κ`, with the two coded refutations left as holes. Measured at the program's own
caliber:

- `runs/floor-1.out` — 8.45s, 1.38GB peak, the only unsolved metas are the two
  coded-injection productions. No heap wall.
- `agents/tasks/LJ-1-645/Probe645.agda` (the typechecking form, with the
  obstruction named instead of the holes) — 9.25s, 1.76GB peak (`runs/probe.out`).

The frame is cheap. The cost of the obligation is not in the frame; it is in the
coded-injection production that the frame leaves as the only two unsolved metas.

## W3: DO `ord-emb` AND `β↪α` CARRY CODES AT THIS SITE

The answer, with file:line evidence:

**`ord-emb` CARRIES a code.** Its element function is the ordinal inclusion
`x ↦ x` (`src/L/BoundedSubset.lagda.md:1371-1375`). A definable relation; its
graph (the diagonal over `κ × β`) is a set in `L` that `InjCode` can carve.

**`β↪α` DOES NOT carry a code.** The obstruction chain:

1. `β↪α = comp-inj (subst … (SC.stage-card-lower β β-isOrd)) πX↪α`
   (`src/L/BoundedSubset.lagda.md:1693-1698`). The `stage-card-lower` leg is a
   definable presentation transport; the obstruction is in the `πX↪α` leg.
2. `πX↪α = λ p → CSel.h (IC.inv p)` (`src/L/BoundedSubset.lagda.md:1691`).
3. `CSel.h m = fst (leastOf w lem (cls m) (nonempty m))`
   (`src/L/BoundedSubset.lagda.md:1114-1115`), where `nonempty` is built from
   `mem-code` (`src/L/BoundedSubset.lagda.md:1111-1112`), a host-language code of
   the inductive type `HS.H.T.Code`.

`CSel.h` selects, for each hull element `m`, the least-count code among ALL
host-language codes that evaluate to `m`, by the ordinal's own well-order `w`
(`src/L/BoundedSubset.lagda.md:1634` instantiates `CodeSelect` with
`SC.OrdSWO.ordSWO α ordα`). The code type `HS.H.T.Code` is a host-language
inductive type, NOT a set in the model `L`. The model cannot express the map
`m ↦ CSel.h m` as a set, so no `InjCode` can carve it. The map `πX↪α`, and
therefore `β↪α`, are not model-definable.

**Both branches are blocked by the SAME obstruction.** The branch whose first leg
is `ord-emb` (definable) is still blocked, because the composite
`comp-inj (ord-emb κ β) β↪α` carries the obstruction through the shared `β↪α`
leg. A code cannot be glued from a definable leg and a non-definable leg.

## WHAT THE STATEMENT COST

- Frame (telescope + opened `Co` + coded cardinal): 8.45s / 1.38GB (floor,
  `runs/floor-1.out`).
- Typechecking form of the probe: 9.25s / 1.76GB (`runs/probe.out`).
- The coded-injection production itself: unmeasurable, because it does not exist.
  The frame leaves it as the only two unsolved metas, and the obstruction
  (above) shows why no such term can be written.

## WHAT THE SHAPE RESISTED

The shape that resisted is the AMBIENT→CODED crossing of the `β↪α` leg. The
coded cardinal `IsCardinalL` (src/L/Cardinal.lagda.md:230-233) refutes a CODED
injection `∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁`. The chapter's `β∈κ` builds an AMBIENT
composite. To feed the coded cardinal, the site must convert the composite to a
code. The `ord-emb` leg and the transported-identity leg are definable and carry
codes. The `β↪α` leg is not: its `πX↪α` leg is `CSel.h`, a `leastOf` choice over
the host-language code type, which the model `L` cannot name as a set. So the
conversion fails at exactly the leg that both branches share.

This is a LOCAL, structural fact about the named piece `β↪α` at this one site.
It is NOT the general ambient→coded crossing that `[LJ-1.533]` measured; premise
5 holds, and I did not treat it as that. The general crossing is a separate,
larger question and is out of scope here.

## CONSEQUENCE (FOR THE NEXT BRIEF)

The chapter cannot take `IsCardinalL` in place of `IsCardinal` at this site.
The two demand-side uses (`:1713`, `:1717`) require converting the ambient
composite to a code, and `β↪α` defeats that. A NO-GO earns which of the two
injections has no code: it is `β↪α`, specifically its `πX↪α = CSel.h ∘ IC.inv`
leg. Restating the bill is the owner's call, not mine.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` (score 172.443): **read** the head to
  confirm it is the archived dispatch index (`archive/dev/LJ-dispatch-index.md:3`
  — "Status: ARCHIVED RECORD. It is never rewritten."). It is a record of the 464
  pre-POD dispatch rows; it holds no ruling on the coded cardinal at this site.
  Declined for use in the verdict; the NO-GO is self-contained in the source.
- `dev/ARCHIVE.md` (score 130.850): **read** the head to confirm it is the
  archive registry of retired modules (`dev/ARCHIVE.md:3` — "The registry of
  Bedrock's retired modules."). It records retired modules, not a ruling on this
  site. Declined for use in the verdict.
- `archive/dev/JOURNAL-archived.md` (score 146.436): **not read, declined.**
  An archived journal; the verdict needs no history, and the live source is the
  evidence.
- `archive/dev/JOURNAL.md` (score 145.601): **not read, declined.** Same reason.
- `archive/dev/ORCHESTRATION.md` (score 123.948): **not read, declined.**
  Orchestration record; no bearing on whether `β↪α` carries a code.

## LITERATURE USED

- `dev/literature/devlin-II5.md` (score 41.063): **not read, declined.** The
  Devlin reference underlies the mathematical bounded-subset construction, but
  the NO-GO is a fact about the Agda coding machinery (`CSel.h`), not about the
  mathematics. The source `file:line` evidence is the evidence.
- `dev/literature/truncation-and-selection.md` (score 52.952): **not read,
  declined.** Not needed; the obstruction is a `leastOf` over a host-language
  code type, not a truncation subtlety.
- `dev/literature/digest.md` (score 36.514): **not read, declined.**
- `dev/literature/terms-2026-08.md` (score 35.775): **not read, declined.**
- `dev/literature/geology.md` (score 32.473): **not read, declined.**
