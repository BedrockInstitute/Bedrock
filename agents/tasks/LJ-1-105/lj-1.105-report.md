# LJ-1.105 report: land the tie repair in EnvSet and the Mem row

Status: COMPLETE. Written incrementally per C-22. No commit, no push.

## 0. Verdict

**MASTER GREEN, MEASURED.** `src/L/Condensation.lagda.md` typechecks,
exit 0, one process at the C-12 cap. BEFORE: 122.3 s cold at load
3.01 start (4 users). AFTER: 140.5 s cold at load 7.07 start (4
users). Lines by check-timing's own counter: 6261 before, 6445 after
(+184). A second after-run at load 4.34 measured 148.7 s; the two
after-runs bracket the delta at +18.2 to +26.4 s.

## 1. The diff

Non-blank in-fence lines (check-timing counter, same instrument):
6261 before, 6445 after, **+184 added**.

What EnvSet now carries: the telescope is
`(E ar B K : Fin n) (γ : S ^ n)` plus `arityK`, `E ∈ K`, `ar ∈ K`,
`envInK`.  Inside it derives `entryK` (the ChainZ tie, premise
`z ∈ K`) and `arSubK` (`arityK` once) from `arityK` and the two
memberships.  The out/back bodies follow ProbeLJ1104A.EnvSetTied:
the first out component climbs `z ∈ E` to `z ∈ K` by
`arityK (lookup E γ) z z∈ E∈K`, the second takes `z ∈ K` from
`envInK`.

The Mem row now states `arityK` (KFacts field shape) and no longer
states `tmKeyK`, `entryK` or `arSubK`.  Its block shrank from 96 to
85 non-blank lines (telescope plus out/back), because the ties moved
into EnvSet.  The key membership is derived inside AtomLeaf
(`keyK-of`) from `arityK`, the code slot's membership `aK`/`bK`, and
the tag satisfaction; `TmVal.keyK` is now the tied shape
(tag satisfaction -> k ∈ K).

The other eight EnvSet-using rows (Top, Neg, Forall, Exist, AllIn,
ExIn, Imp, Eq) and ClauseAgree gained `arityK` in their telescopes
(supplied by the consumer's transK / KFacts.arityK) and their EnvSet
applications now pass `arityK EK arK`; their `entryK`/`arSubK`
hypotheses stay (unused) per the brief's minimum-change rule.  Eq's
`tmKeyK` also stays (unused).  BndLeaf passes `(λ k ht → tmKeyK k)`
to the tied `TmVal.in'`.

## 2. The projected price of the other eleven rows

**Projection: about +18 non-blank in-fence lines and about +2 to
+4 s for the eleven remaining rows, basis named below.**

The shared half is already paid: EnvSet, ChainZ, the tied TmVal key
and AtomLeaf's keyK-of are in the master (the +184 lines and +18 to
+26 s measured above).  Each remaining row therefore pays only its
residual, and the residual is now mostly DELETION:

1. **Eight EnvSet rows** (Top, Neg, Forall, Exist, Eq, AllIn, ExIn,
   Imp) plus ClauseAgree: their EnvSet applications already pass
   `arityK EK arK` (forced by the signature change, landed here) and
   their telescopes already carry `arityK`.  What remains is deleting
   the now-unused `entryK` and `arSubK` telescope hypotheses, -5
   non-blank lines per row (Eq and the two BndLeaf rows also drop
   `tmKeyK`, -6).  Basis: the master is green with these hypotheses
   present but unused, so removal cannot add check cost; the Mem row
   is the measured model of the same deletion and it shrank 96 to 85
   lines with no new seconds of its own.
2. **AllIn and ExIn** additionally need the `tmKeyK` derivation at
   the allin layout, i.e. a BndLeaf `keyK-of` ported from AtomLeaf.
   Unit price: the AtomLeaf derivation in the master, 35 non-blank
   lines, profile share about 1.0 s for its two use sites
   (`AtomLeaf.tmV-in`, 1,041 ms in the cold profile).  Projected:
   about +35 lines and +1 to +2 s per row, at the SAME key slot
   mechanism (the code slot's membership plus arityK plus the tag
   satisfaction).
3. **BotAgree and PropAgree** use no EnvSet and carry no refuted
   satisfier-in-K fact; nothing to do.

Net: 9 rows x -5 to -6 lines, 2 rows x +35 lines, about +18 lines
net, and about +2 to +4 s.  The key-fact families (succK, keyK,
subK, consK, wKfact) are separate refuted facts whose tied forms
were measured supplyable at the rows' binders in [LJ-1.99]; they are
not part of this repair and are priced there.

## 3. Hypotheses added and their suppliers

One hypothesis added to the row telescopes: `arityK` in Top, Neg,
Forall, Exist, ClauseAgree, Mem, AllIn, ExIn, Imp and Eq (nine rows
plus block 1's agreement), in the exact KFacts field shape.

| hypothesis | where | supplier |
|---|---|---|
| `arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩` | each row telescope, e.g. `src/L/Condensation.lagda.md:4343-4345` | **SUPPLIED.** A `KFacts` field, `src/L/Condensation.lagda.md:5973` (`:5769-5770` pre-edit), in the exact shape; the composer's frame holds the same type as `transK`, `src/L/Condensation/TwelveAgree.lagda.md:167-169` |
| `E ∈ K`, `ar ∈ K` (EnvSet parameters) | EnvSet telescope, `:2883-2887` | **SUPPLIED, not new hypotheses.** Each row binds `EK` (out) or derives it from `envK` (back), and binds/derives `arK` from `codesK`; every one of the 18 application sites has both in scope |
| derived `entryK`, `arSubK` (inside EnvSet) | `:2896-2903` | **SUPPLIED by `arityK`.** `ChainZ.entryK-tied-zK` and `ChainZ.arSubK-tied`, MEASURED in the master and aliased in the probe |
| derived `keyK-of` (inside AtomLeaf) | `:4172-4195` | **Not a hypothesis.** Built from `arityK`, the code slot's membership (`aK`/`bK` from `codesK` in back, from the row binders in out), and the tag satisfaction |

`E ∈ K` and `ar ∈ K` are not new row hypotheses; the Mem row states
only `arityK` and dropped `tmKeyK`, `entryK` and `arSubK` entirely.

## 4. Refutation attempts on the tied forms

1. `entryK` (ChainZ tie, premise `z ∈ K`): **NOT REFUTED,
   INFERRED**; the premise is not forceable at the abstract frame
   (the K-slot element would need `X ∈ X`, refuted by `∈-irrefl`,
   MEASURED in the probe, `RefuteAttempts.zK-premise-refuted`).
   SUPPLIED, MEASURED: `ChainZ.entryK-tied-zK` typechecks from
   `arityK`.
2. `arSubK` (tie, premise `ar ∈ K`): **NOT REFUTED, INFERRED**;
   `ar ∈ K` is not forceable at the abstract frame
   (`RefuteAttempts.arK-premise-refuted`, MEASURED).  SUPPLIED,
   MEASURED: `ChainZ.arSubK-tied` is `arityK` once.
3. `keyValK` (the [LJ-1.102] tied `tmKeyK`): **REFUTED, MEASURED**,
   `RefuteKeyValK.keyValK-refutes` in the probe (the same term as
   `src/ProbeLJ1104A.agda:118-120`).  This is why `tmKeyK` is
   derived, not stated.
4. The derived `keyK-of`: a derivation, not a hypothesis.  MEASURED
   inhabited (it typechecks in the master; its premises are `aK`/`bK`
   from `codesK`, `arityK`, and the tag satisfaction).

## 5. C-39 section

One line blocked a route I could see.  "The other eleven rows keep
their current shape unless the EnvSet change forces a signature
update" (`_build/briefs/LJ-1.105.md` item 4) blocked the cheap
cleanup of deleting the now-unused `entryK`/`arSubK`/`tmKeyK`
hypotheses from the eight other EnvSet rows.  The route it blocked:
pure deletion, -5 to -6 lines per row, zero seconds, leaving the
telescopes honest today instead of carrying dead refuted hypotheses
until the frame dispatch.  The line exists to minimize churn, and it
did; the cost is about 45 lines of dead telescope carried for one
more dispatch.  No other brief line blocked a route.

## 6. Negatives classified

1. The master is green after the edit: **MEASURED TRUE**, exit 0,
   two cold runs, 140.5 s and 148.7 s.
2. The master's cold check grew: **MEASURED TRUE**, 122.3 s before
   to 140.5-148.7 s after, at loads 3.01 vs 7.07 and 4.34.
3. The EnvSet tie derivations close both directions at an abstract
   frame: **MEASURED TRUE**, master green and the probe's EnvSetUse
   aliases out/back/memE-bnd.
4. The entryK and arSubK ties are refutable at the abstract frame:
   **INFERRED FALSE**; no refutation term was found, and their
   premises (z ∈ K, ar ∈ K) are not forceable at the K-slot element
   (MEASURED by the probe's refuted-premise lemmas).  Their supply
   from arityK is MEASURED by the ChainZ derivations.
5. The [LJ-1.102] tied tmKeyK (keyValK) is an empty type:
   **MEASURED TRUE** (`RefuteKeyValK.keyValK-refutes`), which is why
   tmKeyK is derived rather than stated.
6. The other rows changed only as forced (arityK added, application
   arguments updated): **MEASURED TRUE by the diff** (18 application
   sites, one pattern each; the row telescopes otherwise untouched).
7. The consumers under `src/L/Condensation/` need the frame update
   before they typecheck again: **INFERRED** from the positional row
   applications and the signature changes.  The brief says the
   frames come after this dispatch; not measured, out of scope.
8. The J tower gets the new EnvSet unchanged: **INFERRED**.  No J
   site exists in this tree to instantiate it; the design is
   slot-generic (all arguments are Fin positions or S variables, and
   the chain is pair-encoding only).

## 7. DD4 answer

One derivation inside EnvSet instead of nine copies.  Against the
[LJ-1.104] per-row shape (each row stating the tied entryK and
arSubK, about 7 lines per row), EnvSet now derives both once, about
10 lines inside EnvSet: a saving of about 9 x 7 - 10 = 53 lines if
the per-row statements existed.  Measured in this tree: the Mem row
shrank from 96 to 85 non-blank lines (-11) while gaining the honest
arityK hypothesis and losing tmKeyK, entryK and arSubK, and the
master's other EnvSet rows no longer pass ties at all.  The J tower
gets the new EnvSet unchanged in design: EnvSet and ChainZ are
generic in the slots (Fin positions, S variables) and carry nothing
about definability; no J tower exists in this tree yet to check the
instantiation (INFERRED).

## 8. Measurements

Cold seconds (check-timing protocol: module interface moved aside,
one process at a time, GHCRTS=-M8g):

| run | seconds | load average at start | users |
|---|---:|---|---:|
| before (`5cc68f7`) | 122.3 | 3.01 | 4 |
| after, run 1 | 140.5 | 7.07 | 4 |
| after, run 2 | 148.7 | 4.34 | 4 |

Delta: +18.2 to +26.4 s.  Lines: 6,261 before to 6,445 after
(+184) by check-timing's in-fence counter; git diff +272/-68 raw.
The spread across the two after-runs (8 s) exceeds the load
difference, so system noise is part of the delta.

Cold per-definition profile (140.2 s, exit 0): no new definition
dominates.  Largest new-name costs: `AtomLeaf.tmV-in` 1,041 ms,
`AllInAgree.back` 2,469 ms, `ExInAgree.back` 2,518 ms (the rows'
backs re-elaborate the derived ties).  `EnvSet.entryK` itself is
14 ms.  The largest hot rows are pre-existing frame consumers
(`LeafAgree.back` 11,254 ms, `SatGraphAgree.body-back` 6,233 ms).

Probe `src/ProbeLJ1105A.agda`: GREEN, exit 0, 2.88 s warm (143.1 s
cold with the L.Condensation dependency re-checked), one process at
the C-12 cap.  `scripts/lint-agda.py --check` and
`scripts/lint-prose.py --check` pass on the master and the probe.
`scripts/check-fences.py --check`: clean, 87 masters.

## ARCHIVE USED

- `src/ProbeLJ1104A.agda`, read WHOLE. TOOK the `EnvSetTied` shape
  (`:132-251`), the tied `TmValTied`/`AtomLeafTied` (`:258-561`),
  the restated Mem row (`:570-676`), and the keyValK refutation
  (`:118-120`), which the probe carries as the regression guard.
- `_build/lj-1.104-report.md`, read WHOLE. TOOK the DD4 answer
  (EnvSet carries arityK plus the two memberships and derives the
  ties once), the hypothesis-supply table, and the telescope counts.
- `src/ProbeLJ1102A.agda`, read WHOLE, and
  `_build/lj-1.102-report.md`, read WHOLE. TOOK the failing
  EnvSetTied copies and the measured `z ∈ E`/`z ∈ K` split.
- `src/ProbeLJ199A.agda`, read WHOLE, and
  `_build/lj-1.99-report.md`, read WHOLE. TOOK `ChainZ`
  (`entryK-tied-zK`, `arSubK-tied`) and the site-supply table for
  EK/arK at all nine rows.
- `src/ProbeLJ197A.agda`, read WHOLE. TOOK the refutation recipes
  for the untied forms and the pair memberships.
- `src/L/Condensation.lagda.md:2764-2874`, `:4141-4240`,
  `:5734-5770` (pre-edit lines), read. TOOK EnvSet, the Mem row and
  `arityK`'s exact field type. Also read the nine rows' telescopes,
  `TmVal` (`:2884-2970`), `AtomLeaf` (`:3979-4140`), `BndLeaf`
  (`:4525-4640`), `ClauseAgree`, `extAtB→extAt` (`:2508-2514`).
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, read. TOOK
  `transK`'s type (`:167-169`, the arityK shape the consumer holds)
  and the `envK-*` family.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-39
  (`:3513-end`), C-35 (`:3200-3242`), C-36 (`:3284-3332`), D-29
  (`:3242-3284`), D-30 (`:3332-3380`), P-i (`:203-262`), P-w
  (`:3094-3164`), plus the bundle's other cited sections, read
  WHOLE. TOOK the satisfiable-telescope standard, the
  refutation discipline, and the copy-paid-at-use rule.
- `scripts/rules.py --for build` and `--for rewrite`, read all
  statements.

## LITERATURE

Banked; nothing spent.
