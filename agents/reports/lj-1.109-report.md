# LJ-1.109 report: tie the key-fact family, the last five of the eleven

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.109-report.md`.

## 0. Verdict

**ALL FIVE ARE TIED, and the master is GREEN, MEASURED.**
`src/L/Condensation.lagda.md` typechecks, exit 0, one process at the
C-12 cap, two cold runs.  BEFORE: 151.2 s cold at load 3.33 start
(4 users).  AFTER: 154.0 s at load 7.81 and 155.2 s at load 5.13
(4 users).  Lines by check-timing's own counter: 6433 before, 6445
after (+12 non-blank in-fence).  Raw diff: +42 / -30.

The run-to-run spread on this tree's content: my two after-runs spread
1.2 s.  The before figure is one run.  [LJ-1.105] measured an 8.2 s
spread on the same content class, so the +2.8 to +4.0 s delta sits
inside the tree's noise band; it is consistently positive across the
two after-runs.

The five refuted names are now stated in the master ONLY in tied form:
every `succK` and `keyK` telescope hypothesis carries the site's
membership premises (`ar ∈ K`, plus `a ∈ K` or `b ∈ K` for the key
shapes), and every use site applies them at the binders.  The abort
criterion's count of failed ties is zero.  Nothing walls at the end.

One measured warning goes with the green: adding the successor-closure
primitive as a FIELD of the `KFacts` record WALLS the master at the
C-12 cap (three configurations, section 2).  The rows do not need the
field; the frame repair must state the closure as a telescope fact, not
as a record field.

## 1. Per-name table

All five names are tied at the row telescopes, exactly the shapes
`[LJ-1.99]`'s `SuccKeySite`/`KeyNegSite` measured green
(`src/ProbeLJ199A.agda:231-272`).  The transfers are UNCHANGED: they
consume the memberships, and the rows apply the tied facts at their
binders to produce them.  Site binders are the `out` lambda positions
and the `back` `codesK` derivations, source-verified at every row.

| name | tied form (master `file:line`) | site binder | supplier | refutation attempt |
|---|---|---|---|---|
| `succK` | `(E ya yc a ar c : S) → ⟨ fst ar ∈ K ⟩ → succU …`; ForallAgree `:3797`, ExistAgree `:3901`, ClauseAgree `:4075` | `arK`: out `λ … ar arK …` (Forall `:3828`), back `(arK , aK) = codesK …` (Forall `:3857`) | the frame's future tied fact; the successor closure `sucK : (a : S) → a ∈ K → sucV a ∈ K` is named in section 2 and DERIVED in the probe | premise unforceable at the abstract frame, MEASURED (`ProbeLJ1109A.RefuteAttempts`, `∈-irrefl`); NOT REFUTED, INFERRED |
| `keyK-un` | `(E ya yc a ar c : S) → ⟨ fst ar ∈ K ⟩ → ⟨ fst a ∈ K ⟩ → keyU …`; Forall `:3799`, Exist `:3903`, Clause `:4077` | `arK`/`aK`, same rows | successor closure + `pairK` (existing field), derived in the probe | same, MEASURED unforceable; NOT REFUTED, INFERRED |
| `keyK-neg` | `(E ya yc a ar c : S) → ⟨ fst ar ∈ K ⟩ → ⟨ fst a ∈ K ⟩ → pr (fst ar) (fst a) ∈ K`; NegAgree `:3692` | `arK`/`aK`: out `:3719`, back `:3742` | `pairK` (existing `KFacts` field, frame holds it) transported along `prʟ-fst`; derived in the probe | same, MEASURED unforceable; NOT REFUTED, INFERRED |
| `succK-allin` | `(E ya yc b a ar c : S) → ⟨ fst ar ∈ K ⟩ → sucV (fst ar) ∈ K`; AllInAgree `:4930`, ExInAgree `:5050` | `arK`: out `:4976`, back `:5004` | same as `succK` | same, MEASURED unforceable; NOT REFUTED, INFERRED |
| `keyK-allin` | `(E ya yc b a ar c : S) → ⟨ fst ar ∈ K ⟩ → ⟨ fst b ∈ K ⟩ → pr (sucV (fst ar)) (fst b) ∈ K`; AllIn `:4935`, ExIn `:5055` | `arK`/`bK`: out `:4976`, back `:5004` | same as `keyK-un` with `b` at the transfer's second slot | same, MEASURED unforceable; NOT REFUTED, INFERRED |

Use sites: NegAgree `:3733`, `:3760`; Forall `:3842-3843`, `:3875-3876`;
Exist `:4018-4019`, `:4047-4048`; AllIn `:4993-4994`, `:5024-5025`;
ExIn `:5113-5114`, `:5144-5145`.  ClauseAgree forwards the tied facts to
ExistAgree unchanged (`:4100`).

## 2. The successor closure: named, not added to the record

The tie's missing primitive is the successor closure:

```agda
sucK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ sucV (fst a) ∈ fst (lookup K γ) ⟩
```

What inhabits it: a constructibility level closed under V-successor.
`sucV a = a ∪ ⁅a⁆s`; for `a ∈ L β` at `β < α` with `α` limit,
`a ∪ ⁅a⁆s ∈ L (β+1) ⊆ L α`.  `pairK` and `arityK` cannot close it,
which is the brief's own reading of `KFacts`.

**The refutation attempt: NOT REFUTED, INFERRED.**  At the abstract
frame the only candidate forcing the premise is the K-slot element X,
whose premise is `X ∈ X`, refuted by `∈-irrefl`
(`src/ProbeLJ1109A.agda`, module `RefuteAttempts`, MEASURED).

**The supply is MEASURED, and it is not the record.**  `src/ProbeLJ1109A.agda`
module `TiesSupplied` derives all three tied shapes from `sucK` +
`pairK` at the generic `K γ` frame: `succ-tied` is `sucK` itself,
`key-neg-tied` is `pairK` transported along `prʟ-fst`, `key-un-tied`
is `pairK` on the L-successor (`sucʟ-fst` gives
`fst (sucʟ a) ≡ sucV (fst a)`), GREEN.

**A `KFacts` FIELD walls the master, MEASURED.**  I added the field to
the record and to `KFactsCons`, and the master's cold check exhausted
the C-12 heap cap in every configuration that carried it: with the
derivations inside the transfers (walled at ~247 s), with them hoisted
to module level (walled at ~247 s), and with the plain tied telescopes
and no derivations (walled at ~256 s).  Removing exactly the two lines
(field + `KFactsCons` line) returns the master to GREEN at 154-155 s.
The mechanism is P-i class 3: the transparent `sucV (fst a)` in the
record FIELD type is forced into the record's elaborations.  The rows
never consume the field; the frame repair should state `sucK` as a
telescope fact of the frame (the shape `transK`/`pairK` already take),
not as a `KFacts` record field.

## 3. C-39 section

One brief line blocked a route I could see, and one measured wall names
a route for the next dispatch.

1. "Do not touch `src/L/Condensation/`" blocked updating the frame's
   fact list (`TwelveAgree.lagda.md:201-235`) and the consumers
   (`UpperAgree.lagda.md`, `LowerAgree.lagda.md`) to state the TIED
   facts, so the rows' new tied hypotheses have no green instantiator
   in this dispatch.  That was already the state before this edit:
   `[LJ-1.108]` section 4 records the same consumers red for the
   earlier repairs.  The unblocked route is the frame dispatch, which
   the orchestrator plans next; it now has the exact tied shapes to
   state, at the lines in section 1.
2. The wall in section 2 blocks the route "put the successor closure
   into `KFacts` as a record field".  The route that stays open: state
   `sucK` as a frame fact.  This is a measurement, not a prohibition;
   the frame dispatch must take the open route.

No other brief line blocked a route.

## 4. Negatives classified

1. The five are tied in the master: **MEASURED TRUE** by the diff (the
   tied premises are exactly the site memberships; no other code
   changed outside the six rows).
2. The master is green after the edit: **MEASURED TRUE**, exit 0, two
   cold runs, 154.0 s and 155.2 s.
3. The cold seconds changed: **MEASURED TRUE**, 151.2 s before to
   154.0-155.2 s after.  The delta's lower bound is not pinned: the
   after-runs spread 1.2 s, and this tree measured an 8.2 s spread in
   `[LJ-1.105]`.
4. The tied forms are refutable at the abstract frame: **INFERRED
   FALSE**.  Their premises at the K-slot element are `X ∈ X`, refuted
   by `∈-irrefl` (MEASURED, `RefuteAttempts`); no refutation term was
   found.
5. The tied forms are inhabitable: **MEASURED TRUE** by the probe's
   `TiesSupplied` derivations from `sucK` + `pairK` (the successor
   closure is a named primitive with a model inhabitant; `pairK` is a
   delivered field).
6. A `KFacts` record field for the successor closure is viable:
   **MEASURED FALSE**.  Three configurations with the field walled at
   the C-12 cap; the identical tree without the two field lines is
   green.  The field is never consumed by the master.
7. The consumers under `src/L/Condensation/` supply the tied facts:
   **INFERRED**, not measured.  They are red for earlier repairs and
   out of scope; the frame dispatch is their audit.

## 5. DD4 answer

**Five names stay, tied, at the six sites; the derivations that would
replace them wall the master, MEASURED.**  The brief's candidate,
`SubValSuccB2T`, was tried as the one home for the key-fact
derivations (the transfers take `sucK` + `pairK` + `arK`/`aK` and
derive the memberships inside, exactly the `[LJ-1.105]` EnvSet shape),
in two placements: derivations let-bound in `out`, then hoisted to
module-level named helpers (P-i [C]).  Both placements, together with
the `KFacts` field the shape needs, exhausted the C-12 heap cap; the
green shape is the tied telescopes with unchanged transfers.

What is shared instead is measured in the probe, not the master: the
three derivations from the two closure primitives
(`src/ProbeLJ1109A.agda`, `TiesSupplied`) are the exact terms the
frame repair uses to inhabit the tied facts, and the `sucK` primitive
is named with its inhabitant and its measured warning (a frame fact,
not a record field).  The rows mirror the frame's fact list; the tie
belongs in the telescopes.

## 6. Measurements

Cold seconds (check-timing protocol: module interface moved aside, one
process at a time, `GHCRTS=-M8g`):

| run | seconds | load average at start | users |
|---|---:|---:|---|
| before | 151.2 | 3.33 | 4 |
| after, run 1 | 154.0 | 7.81 | 4 |
| after, run 2 | 155.2 | 5.13 | 4 |

Delta: +2.8 to +4.0 s.  Lines: 6433 before to 6445 after (+12
non-blank in-fence) by check-timing's in-fence counter; `git diff`
+42 / -30 raw.  After-run spread: 1.2 s.  One process at a time
throughout; each run started only after the previous exited.

`scripts/check-fences.py --check`: clean, 87 masters.
`scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`:
clean on the master and the probe.  `scripts/ledger.py --brief`
measures from HEAD: standing 28,361 lines over 85 masters (the
uncommitted edit is not counted).

The wall runs (section 2) died at the C-12 cap after about 247 s
(load 4.72 start) and 256 s (load 3.81) on the two `check-timing`
runs and 168 s (load 2.45) on the combined probe+master run;
`check-timing` reports no number for a wall.  The three wall
configurations are the three that carried the `KFacts` field; the
green configurations are the two that did not.

Probe `src/ProbeLJ1109A.agda`: GREEN, exit 0, 2.3 s warm (master
interface warm), one process at the C-12 cap.

## ARCHIVE USED

- `_build/lj-1.108-report.md`, read WHOLE.  TOOK the remaining-
  occurrence grep (section 2) as the work list, the site lines for the
  five names, and the measured 147.9-148.4 s baseline.
- `_build/lj-1.99-report.md`, read WHOLE.  TOOK the per-site supply
  table (section 4), the `SuccKeySite`/`KeyNegSite` tied shapes
  (`src/ProbeLJ199A.agda:231-272`), and the "tieable by memberships the
  row sites hold" verdict.
- `_build/lj-1.105-report.md`, read WHOLE.  TOOK the EnvSet/ChainZ DD4
  precedent and the arityK-supply pattern.
- `src/ProbeLJ197A.agda`, read WHOLE.  TOOK the five refutations and
  the regularity-cycle recipes the tied forms must avoid.
- `src/ProbeLJ1104A.agda`, read WHOLE.  TOOK the keyValK refutation
  (`:118-120`) as the empty-tie regression guard and the tied-row
  shape.
- `src/L/Condensation.lagda.md`, read the six rows, the two transfers,
  `succU`/`keyU` (`:3790-3800`), `KFacts` (`:5927-6010`), and every
  use site quoted in sections 1 and 2.
- `src/L/Condensation/TwelveAgree.lagda.md:45-320`, read WHOLE.
  TOOK the five refuted facts' shapes (`:201-235`) and the frame's
  `pairK`/`transK` shapes the frame repair will mirror.
- `src/L/Axioms/Numerals.lagda.md:97-181`, read.  TOOK `sucʟ` and
  `sucʟ-fst` (opaque) for the probe's `key-un-tied`.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-39
  (`:3513-end`), C-35 (`:3200-3242`), C-36 (`:3284-3332`), D-29
  (`:3242-3284`), D-30 (`:3332-3380`), P-i (`:203-262`), P-w
  (`:3094-3164`), read WHOLE.  TOOK the satisfiable-telescope
  standard, the prohibition-priority rule, the named-helper cure
  (P-i [C], tried and measured), and the copy-paid-at-use rule.
- `scripts/rules.py --for build` and `--for rewrite`, read all
  statements.

## LITERATURE

Banked; nothing spent.

## 3. C-39 section

FILLED LAST. Any brief line that blocked a route, and the route.

## 4. Negatives classified

FILLED LAST. Every negative is MEASURED or INFERRED.

## 5. DD4 answer

FILLED LAST. One place or five names, and why.

## 6. Measurements

FILLED LAST. Cold seconds before and after, run-to-run spread, load
average, net non-blank in-fence lines.

## ARCHIVE USED

FILLED LAST at `file:line`.

## LITERATURE

Banked; nothing spent.
