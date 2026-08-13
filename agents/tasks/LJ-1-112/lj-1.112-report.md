# LJ-1.112 report: instantiate the repaired composer

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.112-report.md`.

## 0. The verdict

**The new unsolved-meta count is 0, MEASURED. The old counts are 39
([LJ-1.93]) and 11 ([LJ-1.100]).** The re-pointed instantiation of
`TwelveAgree.AbstractFrame` at the extended consumer frame typechecks,
exit 0, four runs, one process at a time at the C-12 cap. The eleven
refuted names are gone from the frame, the frame's five tied key facts
are derivations inside it, and the ONE new obligation the consumer must
supply, `sucK`, is added to the extended frame as a new hypothesis and
supplied. No hypothesis is left unsupplied. **The composer is
instantiable for the first time; this is the phase's acceptance test,
and it passes (abort criterion, first case: report the term and STOP).**

The term is the module-F application at
`src/ProbeLJ1112A.agda:408-435`, with the consumer line
`consume-out = F.out` at `:437-439` forcing the composer's body to
elaborate. The one addition to the consumer frame is `sucK`
(`src/ProbeLJ1112A.agda:317-319`), a new hypothesis, not a discharge
(C-38); its supplier is named in section 2 and is INFERRED; the
refutation attempt died in the premise (MEASURED barrier), so it is
NOT REFUTED, INFERRED. No addition was refuted. No wall occurred.

## 1. The instantiation and the count

`src/ProbeLJ1112A.agda` starts from `src/ProbeLJ1100A.agda` (read
WHOLE), keeps the consumer telescope (module `PackAttempt`), the
lifted `KFacts` (module `At`), and the extended consumer frame
(module `Extended`), and re-points the module-F application at the
CURRENT `AbstractFrame` telescope, read in the source
(`src/L/Condensation/TwelveAgree.lagda.md:45-243`), not from any
report.

The telescope changed in two ways since [LJ-1.100]:

1. `codesK` and `codesK-un` dropped their leading `d e f` binders
   (`TwelveAgree.lagda.md:97-110`).  The consumer's facts still take
   them (`src/L/Condensation.lagda.md:6709-6720`), so the application
   passes `codesK d e f` / `unCodesK d e f`; the slots match
   definitionally because `γ' = f ∷ e ∷ d ∷ γ`.
2. The eleven refuted hypotheses are gone, and `sucK` sits between
   `subK-neg` and `subK-un` (`TwelveAgree.lagda.md:186-188`).  The
   five tied key facts are derivations from `sucK` and `pairK`
   (`:230-261`); `arityK` is the binder swap of `transK` (`:218-221`).

The application supplies all 59 facts of the frame at their exact
positions (`src/ProbeLJ1112A.agda:408-435`).  Agda reports no error
and no unsolved meta: exit 0.

The count, beside the earlier measurements:

| dispatch | unsolved metas | measurement |
|---|---:|---|
| [LJ-1.93] | 39 | consumer frame as it stood |
| [LJ-1.100] | 11 | extended frame, the eleven refuted names |
| **this dispatch** | **0** | repaired frame, extended frame plus `sucK` |

The four runs: exit 0 at 10.57 s (first green, load 4.34 start), exit
0 at 11.11 s (with the `consume-out` consumer line, load 3.59 start),
exit 0 at 3.03 s (interface-warm re-check, load 3.42 start), exit 0 at
10.69 s (final text after the comment fix, load 3.06 start), one
`agda` process at a time, `GHCRTS=-M8g`.  The 10-11 s figure is the
elaboration of the instantiation; the 3.03 s figure is the
interface-warm re-check.  No process was left running; no wall was
recorded.  The machine is shared with the orchestrator and the
sibling cardinal agent (4 users).

## 2. The additions and their suppliers

**Every addition to the consumer frame is a new hypothesis, not a
discharge (C-38).** This dispatch adds exactly one fact to the
extended consumer frame:

| addition | frame obligation | what would supply it | refutation attempt |
|---|---|---|---|
| `sucK` | `TwelveAgree.lagda.md:186-188`; consumer hypothesis at `src/ProbeLJ1112A.agda:317-319` | a constructibility level closed under V-successor: `sucV a = a ∪ ⁅a⁆s`, for `a ∈ L β` at `β < α` with `α` limit, `a ∪ ⁅a⁆s ∈ L (β+1) ⊆ L α` (named at `_build/lj-1.109-report.md:63-65`). INFERRED: no instantiation of this tree supplies it | the [LJ-1.109] `RefuteAttempts` shape (`src/ProbeLJ1109A.agda:73-83`), re-measured at `src/ProbeLJ1112A.agda:76-86`: at the abstract frame the only forceable premise is the K-slot element's own membership, `A ∈ A`, refuted by the delivered `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`). The premise barrier is MEASURED; **NOT REFUTED, INFERRED** |

The extended frame keeps the six tied hypotheses and the two derivable
tied forms of [LJ-1.100] (`src/ProbeLJ1112A.agda:348-398`) as a record
of what the consumer can hold, but the repaired frame derives its own
tied facts from `sucK` and `pairK` and consumes none of them; they are
carried over, not added, and cost this dispatch nothing.

Nothing else was added: the re-pointing is a change of argument
positions, not a change of facts.  No hypothesis remains unsupplied:
the frame's 59 hypotheses are all supplied at
`src/ProbeLJ1112A.agda:408-435`: 28 from the record (the 26 `KFacts`
fields, `num1K` as `kf .numK1`, and `transK` derived from
`kf .arityK`), 2 from the consumer's site facts
`codesK d e f` / `unCodesK d e f`, and 29 from the extended frame
(the 28 carried from [LJ-1.100] plus the new `sucK`).

The `sucK` hypothesis stays OUT of `KFacts` (P-x,
`dev/LESSONS.md:3564-3601`): a record field carrying `sucV (fst a)`
walls the master, MEASURED at [LJ-1.109] section 2
(`_build/lj-1.109-report.md:79-92`), three configurations at the C-12
cap.  The frame states it as a telescope fact, the shape `transK` and
`pairK` already take, and the consumer holds it at the same shape.

## 3. What check-unbound-hyp.py says

Run on the probe as it is, `src/ProbeLJ1112A.agda`, the checker
reports **clean (1 file(s))**: the scanner reads only ```agda fence
lines (`scripts/check-unbound-hyp.py`, `fences()`), and a standalone
`.agda` probe has no fences, so the run is vacuous.  This is the first
brief to ask for the checker on a probe, and the probe's format is
invisible to the instrument.

Run on a fenced copy of the same text (`_build/lj-1112-fenced.md`),
the checker reports **7 flags**:

| line | name | flag | reading |
|---|---|---|---|
| `:217` | `valK` | rule 1, `yc` unconstrained | the known same-shape pair; [LJ-1.97] could not refute it (premise barrier at the code slot, MEASURED; NOT REFUTED, INFERRED) |
| `:220` | `valK-un` | rule 1, `yc` unconstrained | same |
| `:101`, `:107`, `:112`, `:116`, `:120` | `codesK`, `unCodesK`, `closedEntryK`, `domEntryK`, `domK` | rule 2, premise object `d`/`e` bound only by the telescope | the consumer's own site facts, spelled through the cons list `(f ∷ e ∷ d ∷ γ)`; the frame spells the same premises as `lookup ... γ'`, where no bound variable appears in the object, which is why the frames flag only six and not eleven (MEASURED by comparing the two spellings) |

**`sucK`, the one addition of this dispatch, is NOT flagged.**  Rule 3
does not fire (it has a premise); rule 1 does not fire (the conclusion
subject `sucV (fst a)` carries `a`, which the premise constrains);
rule 2 does not fire (the premise object is the K slot, not a
telescope-bound variable).  The conditional shape is the sound shape
C-38's checker was written to admit, exactly as `carrierK`, `arityK`,
`pairK` and `innerK` are not flagged.

The six frame flags the brief names are confirmed on the current
tree: `LowerAgree.lagda.md:105,108`, `UpperAgree.lagda.md:109,112`,
`TwelveAgree.lagda.md:87,90`, all rule 1 on `yc` in `valK` and
`valK-un`.

## 4. The C-39 section

One brief line blocked a route I could see.

1. The brief's P-x line, "`sucK` stays out of `KFacts`", blocks the
   route where the consumer's record supplies `sucK` as a field and
   the extended frame inherits it for free.  That route is not merely
   forbidden: it is MEASURED as a wall, three configurations at the
   C-12 cap ([LJ-1.109] section 2, `_build/lj-1.109-report.md:79-92`),
   so the open route is the one taken: `sucK` as a telescope fact of
   the frame and of the extended consumer frame, the shape `transK`
   and `pairK` already take.

No other brief line blocked a route.  The write scope
(`src/ProbeLJ1112*.agda` only) cost nothing; the instantiation needs
no master edit, and the one-new-hypothesis obligation is discharged
by the extended frame exactly as the brief's step 3 prescribes.

## 5. Negatives classified

1. The count reaches zero: **MEASURED TRUE**.  Exit 0, no unsolved
   meta, three runs, one process at a time.  This sets the verdict.
2. The eleven refuted names are gone from all three frames:
   **MEASURED TRUE**.  The telescope of
   `src/L/Condensation/TwelveAgree.lagda.md:45-243` carries 59 facts
   (mechanical count) and none of the eleven names; the frame's fact
   count fell from 69 to 59 ([LJ-1.110]).
3. Every frame hypothesis is supplied: **MEASURED TRUE**.  The
   module-F application at `src/ProbeLJ1112A.agda:408-435` typechecks
   and `consume-out = F.out` (`:437-439`) forces the composer's body
   to elaborate.
4. `sucK` is refutable: **INFERRED FALSE**.  The premise barrier is
   MEASURED (`sucK-premise-refuted = ∈-irrefl A`,
   `src/ProbeLJ1112A.agda:85`, `src/V/Hierarchy.lagda.md:155`); no
   refutation term was found, and no verdict rests on the inference.
5. The consumer can hold `sucK`: **INFERRED TRUE**, with the named
   supplier (constructibility level closed under V-successor,
   `_build/lj-1.109-report.md:63-65`).  No instantiation of this tree
   supplies it, so the acceptance test is the count, which is 0 with
   `sucK` taken as a hypothesis of the extended frame.
6. The six checker flags on the frames mark hypotheses worth
   attacking: **MEASURED TRUE** (the checker's own output); the pair
   `valK`/`valK-un` is the [LJ-1.97] same-shape pair, NOT REFUTED,
   INFERRED.
7. The five consumer-side flags on the fenced probe are not composer
   obligations: **MEASURED TRUE by spelling**.  The composer states
   those premises as `lookup ... γ'`, where the checker finds no
   bound-variable object and flags nothing.

## 6. The DD4 answer

Sharing is only free when the shared frame is the frame the consumer
actually holds ([LJ-1.93] section 6).  **This dispatch is that test,
at last, against a repaired frame.  The answer is the count: 0,
MEASURED.**  The consumer holds every one of the 59 facts the shared
frame states, the eleven refuted names are gone, the five tied key
facts are derived once from the two closure primitives and cost zero
hypotheses, and the one remaining obligation, `sucK`, is the single
new hypothesis of the extended frame, conditional in the shape the
rows actually bind.  The shared frame is the frame the consumer
holds, plus one named, INFERRED-supplied closure the consumer must
grow; nothing else separates the two sides.

## 7. Measurements

All figures below carry their load average (4 users on the machine;
orchestrator and the sibling cardinal agent share it).

| run | exit | seconds | load at start |
|---|---:|---:|---|
| first green check | 0 | 10.57 (9.56 user) | 4.34 |
| with `consume-out` | 0 | 11.11 (10.08 user) | 3.59 |
| re-check (interface warm) | 0 | 3.03 (2.01 user) | 3.42 |
| final text after comment fix | 0 | 10.69 (9.64 user) | 3.06 |

One `agda` process at a time, `GHCRTS=-M8g`, cap never raised.  Each
run started only after the previous exited.  No wall, no heap event,
no kill.  The first failed run (exit 42, `NotInScope V`, 3.15 s, load
4.34) is a fix within the probe, not a measurement.

`scripts/ledger.py --brief` (the admissible size figure): standing
28,425 lines over 85 masters, measured from HEAD; thresholds
SUSPENDED per the ledger header.

`scripts/lint-prose.py --check _build/lj-1.112-report.md`: exit 0.
`scripts/lint-agda.py --check src/ProbeLJ1112A.agda`: exit 0.
`scripts/check-unbound-hyp.py` on the probe: section 3.
No `make check` was run (brief prohibition).  No master was touched:
`src/L/Condensation/`, `src/L/Coding/`, `src/V/`,
`src/Everything.lagda.md` untouched.  The working tree carries the
probe and this report, gitignored by design; the fenced diagnostic
`_build/lj-1112-fenced.md` is scratch under `_build/`.

## ARCHIVE USED

- `_build/lj-1.110-report.md`, read WHOLE.  TOOK the restated frame
  shapes, the per-frame fact counts (37/36/59), the `sucK`-as-consumer-
  obligation naming (section 2), and the C-39 route record.
- `src/ProbeLJ1100A.agda`, read WHOLE, and
  `_build/lj-1.100-report.md`, read WHOLE.  TOOK the extended consumer
  frame (module `At`, module `Extended`), the 11-unsupplied table, and
  the module-F application to re-point.  The probe starts from this
  file.
- `_build/lj-1.109-report.md`, read WHOLE.  TOOK section 2 (the
  `sucK` supplier: constructibility level closed under V-successor,
  `:63-65`; the KFacts-field wall, `:79-92`) and the RefuteAttempts
  verdict.
- `src/ProbeLJ1109A.agda`, read WHOLE.  TOOK `RefuteAttempts`
  (`:73-83`) and `TiesSupplied` (`:95-123`), reused for the `sucK`
  refutation-attempt shape.
- `src/ProbeLJ197A.agda`, read WHOLE, and `src/ProbeLJ195A.agda`,
  read WHOLE.  TOOK the eleven refutations that justify the repair and
  the `∈-irrefl`/regularity recipes.
- `src/ProbeLJ199A.agda`, read the header and module `ChainZ`.  TOOK
  the `entryK-tied`/`arSubK-tied` derivations the extended frame keeps.
- `src/L/Condensation/TwelveAgree.lagda.md`, read WHOLE.  TOOK the
  CURRENT `AbstractFrame` telescope (`:45-243`), the derived `arityK`
  (`:218-221`), the five tied derivations (`:230-261`), and the
  `p0b`/`p1b`/`out`/`back` applications.
- `src/L/Condensation.lagda.md`, read `KFacts` (`:5939-5980`),
  `SatGraphAgree` (`:6682-6768`), `SatGraphB`.  TOOK the consumer's
  telescope and the record fields the instantiation draws on.
- `src/L/Condensation/LowerAgree.lagda.md`, read `someEnvDef`
  (`:51-58`) and the frame shapes.  `src/L/Condensation/UpperAgree.lagda.md`,
  read the frame's `arityK` and `sucK` (`:97-100`, `:150-152`).
- `dev/LESSONS.md`, C-38 as extended (`:3427-3520`), C-39
  (`:3521-3563`), P-x (`:3564-3601`), C-40 (`:3602-end`), C-35
  (`:3200-3241`), C-36 (`:3284-3331`), D-29 (`:3242-3283`), D-30
  (`:3332-3380`), read WHOLE.  TOOK the satisfiable-telescope
  standard, the prohibition-priority rule, the record-field wall, and
  the consumer-check discipline; plus P-c, P-h, P-i, P-k, P-l, P-m,
  P-n, P-o, P-q, P-t, P-u, P-v, P-w, R-35, R-36, R-38, R-40, I-5,
  C-12, C-22, C-31, C-32, C-33, C-34, C-37, D-1, D-8, D-10, D-26,
  read per the bundle.
- `scripts/rules.py --for build` and `--for probe`, read all
  statements.

## LITERATURE

Banked; nothing spent.
