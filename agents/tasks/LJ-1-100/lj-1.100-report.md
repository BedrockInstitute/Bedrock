# LJ-1.100: extend the consumer's frame and re-measure the 39

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.100-report.md`.

## 0. THE VERDICT

**The new unsolved-meta count is 11, MEASURED. The old count is 39.**
The instantiation of `AbstractFrame` against the extended consumer
frame leaves 11 unsolved metas (`src/ProbeLJ1100A.agda:380.9-402.13`,
exit 42, 7.22 s total, 6.24 s user, load average 4.08 to 5.78,
4 users). The extended frame supplies 28 of the 39 facts. The 11
remaining hypotheses have no supplier because their stated types are
empty at every frame. Each is one of the eleven refuted facts of
`[LJ-1.95]` and `[LJ-1.97]`. Their tied repairs are different types.
No frame extension can supply an empty type.

Per the abort criterion, the count does not reach zero, so this
report states the number and the names. No addition was refuted. No
wall occurred.

## 1. THE EXTENDED FRAME

The extended frame starts from the consumer's telescope:
`SatGraphAgree`, `src/L/Condensation.lagda.md:6476-6513`. It holds
`KFacts` (29 fields, `:5734-5770`) and the six site facts `codesK`,
`unCodesK`, `closedEntryK`, `domEntryK`, `domK`, `witK`
(`:6492-6513`). The extended frame adds the facts the rows hold and
the consumer does not, in their tied forms where a fact was refuted.
The frame lives in `src/ProbeLJ1100A.agda`: module `At` holds the
consumer's `γ'` and `kf`; module `Extended` holds the additions.

The K slots match: `lookup (suc^6 K) γ' ≡ lookup (suc^3 K) γ` by
definition, because `γ' = f ∷ e ∷ d ∷ γ`. Every addition below is
stated at the slots of `AbstractFrame`
(`src/L/Condensation/TwelveAgree.lagda.md:45-243`), so the supply is
by conversion.

## 2. THE ADDITIONS

**Every addition to the frame is a new hypothesis, not a discharge
(C-38).** The two derivations are the exception: they cost zero
hypotheses because the frame proves them from its own `arityK`.
Each addition was checked against the `tmKeyK` shape and a refutation
was attempted. The refutation attempts for the satisfier-in-K family
reuse the `[LJ-1.97]` analysis: the conclusion's witness is pinned by
a satisfaction or membership premise, so the unconditional
refutation recipes do not apply. The non-refutation is INFERRED
except for the two derivations, which are MEASURED inhabited.

### 2.1 The 28 untied additions

Each row: name and source line in `AbstractFrame`; why the consumer
can hold it; refutation attempt.

| name | source | why the consumer can hold it | refutation attempt |
|---|---|---|---|
| `valK` | `TwelveAgree.lagda.md:86-88` | New hypothesis, not a discharge. The rows state this type at their telescopes (`Condensation.lagda.md:3483-3485`, `:3655`). | NOT REFUTED, INFERRED. The conclusion `yc ∈ K` is unbound by premises, but the code-slot premise is uninhabitable at the abstract frame (`[LJ-1.97]` table) |
| `valK-un` | `:89-91` | New hypothesis, not a discharge. The rows state it (`:2737`, `:3549`). | NOT REFUTED, INFERRED. Same shape as `valK` |
| `t0eq` | `:92` | New hypothesis, not a discharge. The rows hold it (`MemAgree :4156`, `AtomLeaf :3981`). | NOT REFUTED, INFERRED. An equality at a slot, same shape as `KFacts.tagEq0` |
| `t1eq` | `:93` | New hypothesis, not a discharge. The rows hold it (`:4157`). | NOT REFUTED, INFERRED. Same shape as `t0eq` |
| `t0K` | `:94-95` | New hypothesis, not a discharge. The rows hold it (`:4158`). | NOT REFUTED, INFERRED. A membership at a slot, same shape as `KFacts.numK0` |
| `envK-mem` | `:98-101` | New hypothesis, not a discharge. The rows hold it (`TopAgree :3486`). | NOT REFUTED, INFERRED. `E ∈ K` is pinned by the `envSetAt` satisfaction |
| `envK-neg` | `:102-105` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `envK-top` | `:106-109` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `envK-imp` | `:110-113` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `envK-allin` | `:114-117` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `envInK-mem` | `:133-136` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. `z ∈ K` is pinned by the `envOverAt` satisfaction |
| `envInK-neg` | `:137-140` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `envInK-top` | `:141-144` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `envInK-imp` | `:145-148` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `valV` | `:149-154` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. `v ∈ K` is pinned by the `tmValAt` satisfaction |
| `valW` | `:155-160` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `wKfact` | `:161-166` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `subK₁-and` | `:170-175` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. `y ∈ K` is pinned by the `subValAt` satisfaction |
| `subK₀-and` | `:176-181` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `subK₁-imp` | `:182-187` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `subK₀-imp` | `:188-193` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `someEnv` | `:194` | New hypothesis, not a discharge. The And and Or rows hold it. | NOT REFUTED, INFERRED. Conditional existential; no abstract witness forces its falsehood |
| `subK-neg` | `:195-200` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Satisfaction pin |
| `subK-un` | `:209-214` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Satisfaction pin |
| `consK-exist` | `:215-219` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. `e' ∈ K` is pinned by the `consAtL` satisfaction |
| `consK-forall` | `:220-223` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |
| `subK-allin` | `:236-241` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Satisfaction pin |
| `consK-allin` | `:242-243` | New hypothesis, not a discharge. The rows hold it. | NOT REFUTED, INFERRED. Same pin |

### 2.2 The six tied hypotheses

Each row: the refuted fact it repairs; the tied form; why the
consumer can hold it; refutation attempt.

| name | repairs | why the consumer can hold it | refutation attempt |
|---|---|---|---|
| `keyValK` | `tmKeyK` `:96` | New hypothesis, not a discharge. The tag satisfaction pins `t`; the honest shape is stated at `Condensation.lagda.md:6764-6765` (`LeafAgree`) | NOT REFUTED, INFERRED. The `[LJ-1.95]` refutation needs no premise; here the premise is a tag satisfaction that the abstract frame cannot force |
| `succK-tied` | `succK` `:205-206` | New hypothesis, not a discharge. The rows' sites bind `ar ∈ K` (`ForallAgree :3705-3706`, `ExistAgree :3880-3881`) | NOT REFUTED, INFERRED. The `[LJ-1.97]` refutation at `ar = X` needs the premise `A ∈ A`, which `∈-irrefl` refutes, so the refutation dies in the premise |
| `keyK-un-tied` | `keyK-un` `:207-208` | New hypothesis, not a discharge. The rows' sites bind `ar ∈ K` and `a ∈ K` | NOT REFUTED, INFERRED. Same premise barrier |
| `keyK-neg-tied` | `keyK-neg` `:201-204` | New hypothesis, not a discharge. The rows' sites bind `ar ∈ K` and `a ∈ K` (`NegAgree :3583`, `:3606`) | NOT REFUTED, INFERRED. Same premise barrier |
| `succK-allin-tied` | `succK-allin` `:224-228` | New hypothesis, not a discharge. The rows' sites bind `ar ∈ K` (`AllInAgree :4780-4781`) | NOT REFUTED, INFERRED. Same premise barrier |
| `keyK-allin-tied` | `keyK-allin` `:229-235` | New hypothesis, not a discharge. The rows' sites bind `ar ∈ K` and `b ∈ K` (`AllInAgree :4811-4812`) | NOT REFUTED, INFERRED. Same premise barrier |

### 2.3 The two derivations

Each row: name; the fact it repairs; the proof; the cost.

| name | repairs | proof | cost |
|---|---|---|---|
| `entryK-tied` | `entryK` `:118-120` | The four-step `arityK` chain, GREEN at `src/ProbeLJ1100A.agda:346-352` through `ProbeLJ199A.ChainZ`; premise `E ∈ K` and `z ∈ E` | A derivation, zero hypotheses. MEASURED inhabited, so not refutable |
| `arSubK-tied` | the four `arSubK-*` `:121-132` | `arityK` exactly once, GREEN at `src/ProbeLJ1100A.agda:354-357` | A derivation, zero hypotheses. MEASURED inhabited, so not refutable |

### 2.4 The cost

The additions cost 34 new hypotheses and 2 derivations. None is a
`KFacts` field: `KFacts` has no `t0`/`t1` slots and no
satisfaction-premise structure among its fields (MEASURED by
listing, `Condensation.lagda.md:5734-5770`). All 34 hypotheses are
site facts: telescope hypotheses of the extended consumer frame,
the same kind as the six site facts at `:6492-6513`. The 2
derivations are new proofs from the existing `KFacts.arityK` field.

## 3. THE NEW COUNT

The `[LJ-1.93]` measurement was 39 unsolved metas at
`src/ProbeLJ193B.agda`, exit 42, against the consumer's frame as it
stands. The re-run against the extended frame is 11 unsolved metas at
`src/ProbeLJ1100A.agda:380.9-402.13`, exit 42. The module-F
application (`src/ProbeLJ1100A.agda:368-403`) supplies the 28 added
facts at their exact positions. Agda reports no other error, so the
28 supplies typecheck. The 11 holes stay unsolved.

39 → 11. The residue is exactly the eleven refuted facts.

## 4. THE HYPOTHESES WITH NO SUPPLIER

Each hypothesis has no supplier because its stated type is empty at
every frame. The refutations are MEASURED at `src/ProbeLJ197A.agda`
for the ten and `src/ProbeLJ195A.agda:45-48` for `tmKeyK`. The
unsolved meta at the same position in the probe is MEASURED. The
tied repair in the extended frame is a different type; it cannot
supply the stated fact.

| hypothesis | stated type | probe hole |
|---|---|---|
| `tmKeyK` | `TwelveAgree.lagda.md:96` | `ProbeLJ1100A.agda:380` |
| `entryK` | `:118-120` | `:384` |
| `arSubK-mem` | `:121-123` | `:386` |
| `arSubK-neg` | `:124-126` | `:387` |
| `arSubK-top` | `:127-129` | `:388` |
| `arSubK-imp` | `:130-132` | `:389` |
| `keyK-neg` | `:201-204` | `:396` |
| `succK` | `:205-206` | `:397` |
| `keyK-un` | `:207-208` | `:398` |
| `succK-allin` | `:224-228` | `:401` |
| `keyK-allin` | `:229-235` | `:402` |

## 5. THE DD4 ANSWER

Sharing is only free when the shared frame is the frame the consumer
actually holds (`[LJ-1.93]` section 6). This dispatch runs that test
against an extended consumer frame. **The count is 11, MEASURED.**
The extended frame holds the rows' facts, with the eleven refuted
ones in their tied forms, yet 11 of the composer's 69 hypotheses
still have no supplier. The 11 are not a frame mismatch. They are
empty types inside the shared frame itself: the composer states the
untied forms, and `[LJ-1.95]` and `[LJ-1.97]` refuted those forms at
every frame. The consumer can hold the tied repairs; the composer
does not state them.

The repair direction is a strengthening (C-36): the shared frame must
restate the eleven in tied form. The extended consumer frame then
holds every fact: 28 supplied, 11 tied, with `entryK-tied` and
`arSubK-tied` at zero hypothesis cost from `arityK`. That restated
instantiation is NOT measured here; the composer as stated is what
this dispatch measures, and its count is 11.

## 6. NEGATIVES AND THEIR STATUS

1. The extended frame closes the instantiation: **MEASURED FALSE**.
   11 unsolved metas at `src/ProbeLJ1100A.agda:380.9-402.13`,
   exit 42. This negative sets the verdict.
2. The extended frame supplies the other 28 facts: **MEASURED TRUE**.
   The module-F application typechecks at those positions; Agda
   reports no type error there.
3. The 11 have no supplier at the extended frame: **MEASURED** by the
   holes; their stated types are empty: **MEASURED** by the
   refutations of `[LJ-1.95]` and `[LJ-1.97]`.
4. `entryK-tied` and `arSubK-tied` are refutable: **MEASURED FALSE**.
   They are inhabited terms in the probe (`src/ProbeLJ1100A.agda:346-357`).
5. The other 34 additions are refutable: **INFERRED FALSE**. No
   refutation term was found. Each has a satisfaction or membership
   premise that pins the conclusion, or is a slot fact. No verdict
   rests on this alone.
6. `t0eq`, `t1eq`, `t0K` could be `KFacts` fields: **MEASURED FALSE
   by listing**. `KFacts` (`Condensation.lagda.md:5734-5770`) has no
   `t0`/`t1` slots among its parameters.
7. The satisfier-in-K additions could be `KFacts` fields:
   **MEASURED FALSE by shape**. `KFacts` fields conclude about the
   record's own slots; the additions conclude about satisfaction-
   pinned witnesses at arbitrary environments.

## 7. ARCHIVE USED

- `_build/lj-1.99-report.md`, read WHOLE, and
  `src/ProbeLJ199A.agda`, `src/ProbeLJ199B.agda`, read WHOLE. TOOK
  the tied forms (`entryK-tied`, `arSubK-tied`, `succK-tied`,
  `keyK-un-tied`, `keyK-neg-tied`, `succK-allin-tied`,
  `keyK-allin-tied`), the `ChainZ` module, and the row-supply table.
  The probe reuses `ChainZ` to derive the two zero-cost tied forms.
- `_build/lj-1.93-report.md`, read WHOLE, and
  `src/ProbeLJ193B.agda`, read WHOLE. TOOK the 39-unsupplied table,
  the consumer telescope, and the probe to copy. This dispatch copies
  that probe and extends its frame.
- `_build/lj-1.97-report.md`, read WHOLE, and
  `src/ProbeLJ197A.agda`, read WHOLE. TOOK the ten refutations and
  the NOT REFUTED analysis for the satisfier-in-K family.
- `_build/lj-1.96-report.md`, read WHOLE. TOOK the consumer-side
  no-home table and the `valK` use analysis (the `hc` premise).
- `_build/lj-1.98-report.md`, read WHOLE. TOOK the tied-form table
  and the `keyValK` shape for `tmKeyK`.
- `_build/lj-1.95-report.md`, read via `[LJ-1.96]` and `[LJ-1.98]`
  citations; `tmKeyK` refuted at every frame.
- `src/L/Condensation.lagda.md:5734-5770`, `:6476-6513`, read. TOOK
  the 29-field `KFacts` and the consumer's telescope.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, read WHOLE.
  TOOK every hypothesis type and line number quoted in sections 2
  and 4.
- `src/L/Condensation.lagda.md`, read the row telescopes: `TopAgree`
  `:3475-3496`, `ForallAgree` `:3655-3674`, `AllInAgree`
  `:4709-4730`, `MemAgree` `:4142-4158`, `TmVal` `:2884-2894`,
  `AtomLeaf` `:3979-3983`, `LeafAgree` `:6705-6765`, `EnvSet`
  `:2771-2778`. TOOK the row-supply lines quoted in section 2.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), read WHOLE. TOOK the new-hypothesis discipline,
  the conditional-closure standard, and the consumer-pricing rule.
- `scripts/rules.py --for build` and `--for probe`, read all
  statements.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 8. LITERATURE USED

Banked; nothing spent.

## 9. GATES

- `src/ProbeLJ1100A.agda`: RED as designed, exit 42, 7.22 s total,
  6.24 s user, 0.31 s sys, one process at the C-12 cap, load average
  4.08 at start and 4.15 at finish (4 users, load averages 4.08 to
  5.78 across the three runs). 11 unsolved interaction metas at
  `:380.9-13`, `:384.9-13`, `:386.9-13` to `:389.9-13`,
  `:396.9-13` to `:398.9-13`, `:401.9-13`, `:402.9-13`. The first
  check ran at load 5.00 to 4.51; the final re-check at 4.08 to
  4.15.
- `scripts/lint-agda.py --check src/ProbeLJ1100A.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.100-report.md`: exit 0.
- No master was touched. `src/L/Condensation/`, `src/L/Coding/`,
  `src/V/`, `src/Everything.lagda.md` untouched. No `make check`. No
  commit, no push. The working tree carries the probe and this
  report, gitignored by design.
