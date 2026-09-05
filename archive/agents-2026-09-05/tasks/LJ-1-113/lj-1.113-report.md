# LJ-1.113 report: who supplies the twenty nine?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.113-report.md`.

## 0. The three counts

**PROVABLE: 1.  NEEDS NEW CONTENT: 28.  UNKNOWN: 0.**

One of the 29, `t0K`, is derivable from the frame's own `t0eq` plus
the delivered `numK0` field, and the derivation is machine-checked
(probe E).  The other 28 are satisfier-in-K closure facts, slot
equalities, or environment-existence facts that the delivered
machinery does not state; each one-line supplier is named in section
1.  No fact is REFUTABLE: each is conditional on a satisfaction or
membership premise, and the refutation attempts of [LJ-1.97] died in
those premises (MEASURED there).  The classification is complete, so
the abort criterion's first case applies: report and STOP.

## 1. The 29 facts, verified from the source

All 29 are module parameters of `Extended` in
`src/ProbeLJ1112A.agda`.  Each row names the parameter, its source
line, its type in one line, and the verdict with the supplier or the
missing content.  The types are copied from the source, not from a
report.  Every negative is INFERRED unless the row says MEASURED; the
machine checks of section 2 measure three of them.

| # | name | source | type (one line) | verdict |
|---|---|---|---|---|
| 1 | `t0eq` | `src/ProbeLJ1112A.agda:212` | `fst (lookup (suc^3 t0) γ) ≡ fst (numeralL 0)` | NEEDS NEW CONTENT: the slot equality at the consumer's own `t0`.  The machinery states it only at `N0` (`tagEq0`); `t0` and `N0` are independent indices.  MEASURED by probe C |
| 2 | `t1eq` | `:213` | `fst (lookup (suc^3 t1) γ) ≡ fst (numeralL 1)` | NEEDS NEW CONTENT: same, at `t1` against `tagEq1` |
| 3 | `t0K` | `:214-215` | `⟨ fst (lookup (suc^3 t0) γ) ∈ fst (lookup (suc^3 K) γ) ⟩` | PROVABLE: `t0eq` transported into `numK0` (the delivered `KFacts` field), MEASURED by probe E |
| 4 | `valK` | `:216-219` | `c ∈ C-slot → c ≡ pr ar (pr (# k) (pr a b)) → yc ∈ K` | NEEDS NEW CONTENT: the graph membership `pr c yc ∈ T`, which the row's `back` binds (`binClause-out`, `src/L/Coding/Model.lagda.md:911-917`) but the frame's type omits; `domEntryK` then closes it.  MEASURED by probe A |
| 5 | `valK-un` | `:220-221` | `c ∈ C-slot → c ≡ pr ar (pr (# k) a) → yc ∈ K` | NEEDS NEW CONTENT: same missing graph membership, unary clause (`unClause-out`) |
| 6 | `envK-mem` | `:222-225` | `envSetAt ... satisfaction → E ∈ K` | NEEDS NEW CONTENT: K closed under the machine's environment set; `envSetAt`'s extension pins E's members, not E ∈ K |
| 7 | `envK-neg` | `:226-229` | `envSetAt ... → E ∈ K` | NEEDS NEW CONTENT: same closure |
| 8 | `envK-top` | `:230-233` | `envSetAt ... → E ∈ K` | NEEDS NEW CONTENT: same closure |
| 9 | `envK-imp` | `:234-237` | `envSetAt ... → E ∈ K` | NEEDS NEW CONTENT: same closure |
| 10 | `envK-allin` | `:238-241` | `envSetAt ... → E ∈ K` | NEEDS NEW CONTENT: same closure |
| 11 | `envInK-mem` | `:242-245` | `envOverAt ... → z ∈ K` | NEEDS NEW CONTENT: K closed under the machine's environments (pairs over K members), via `envOver-pairs` + `pairK` |
| 12 | `envInK-neg` | `:246-249` | `envOverAt ... → z ∈ K` | NEEDS NEW CONTENT: same closure |
| 13 | `envInK-top` | `:250-253` | `envOverAt ... → z ∈ K` | NEEDS NEW CONTENT: same closure |
| 14 | `envInK-imp` | `:254-257` | `envOverAt ... → z ∈ K` | NEEDS NEW CONTENT: same closure |
| 15 | `valV` | `:258-263` | `tmValAt ... → v ∈ K` | NEEDS NEW CONTENT: K closed under term values; `tmValAt-out` pins v via the environment, which only gives v ∈ K after the env closure |
| 16 | `valW` | `:264-269` | `tmValAt ... → w ∈ K` | NEEDS NEW CONTENT: same closure |
| 17 | `wKfact` | `:270-275` | `tmValAt ... → w ∈ K` | NEEDS NEW CONTENT: same closure |
| 18 | `subK₁-and` | `:276-281` | `subValAt ... → y ∈ K` | NEEDS NEW CONTENT: K closed under sub-values; `subValAt-adequate` pins `pr (pr ar a) y ∈ T`, and `arityK` closes it only with `T ∈ K` |
| 19 | `subK₀-and` | `:282-287` | `subValAt ... → y ∈ K` | NEEDS NEW CONTENT: same closure |
| 20 | `subK₁-imp` | `:288-293` | `subValAt ... → ya ∈ K` | NEEDS NEW CONTENT: same closure |
| 21 | `subK₀-imp` | `:294-299` | `subValAt ... → yb ∈ K` | NEEDS NEW CONTENT: same closure |
| 22 | `someEnv` | `:300` | `someEnvDef {n} K γ'` | NEEDS NEW CONTENT: the environment-existence construction over K; no delivered term builds `envHypB2`'s environment from K memberships |
| 23 | `subK-neg` | `:301-306` | `subValAt ... → ya ∈ K` | NEEDS NEW CONTENT: sub-value closure, negation clause |
| 24 | `sucK` | `:317-319` | `a ∈ K → sucV a ∈ K` | NEEDS NEW CONTENT: K closed under the model successor, a union closure (`sucʟ a = unionʟ (pairʟ a (pairʟ a a))`, `Numerals.lagda.md:104-105`).  MEASURED by probes B and D |
| 25 | `subK-un` | `:320-324` | `subValSuccAt ... → ya ∈ K` | NEEDS NEW CONTENT: sub-value closure at the successor arity, which is `sucK` applied to the arity plus the sub-value closure |
| 26 | `consK-exist` | `:325-329` | `consAtL ... → e' ∈ K` | NEEDS NEW CONTENT: K closed under environment extension (`consAtL`); `consAtL-adequate` pins e' as an extended environment |
| 27 | `consK-forall` | `:330-333` | `consAtL ... → e' ∈ K` | NEEDS NEW CONTENT: same closure |
| 28 | `subK-allin` | `:334-339` | `subValSuccAt ... → ya ∈ K` | NEEDS NEW CONTENT: same as `subK-un`, at the bounded-quantifier arity |
| 29 | `consK-allin` | `:340-344` | `consAtL ... → e' ∈ K` | NEEDS NEW CONTENT: same as `consK-exist`, at the bounded-quantifier layout |

The 28 NEEDS NEW CONTENT facts split into three one-line shapes: 25
are satisfier-in-K closures (the frame's conditional facts that the
machine's satisfaction pins a witness into K), 2 are slot equalities
at the consumer's own indices (`t0eq`, `t1eq`), and 1 is an
environment-existence construction (`someEnv`).  `t0K` is the only
derivation, and it is a transport, not a construction.

## 2. The machine checks

### Check 1: `valK`, the frame's value fact, at
`src/ProbeLJ1113A.lagda.md` module `CheckValK`

The attempted term is `attempt` at
`src/ProbeLJ1113A.lagda.md:90-95`.  The frame states `valK` with
two premises (`c ∈ C` and the code equation).  The row that consumes
it binds a third premise at the same site, the graph membership
`hc : pr c yc ∈ T` (`binClause-out`,
`src/L/Coding/Model.lagda.md:911-917`).  The consumer's `domEntryK`
(`src/L/Condensation.lagda.md:6504-6506`) closes exactly that shape
into `yc ∈ K`; the `reach` proof at `:74-82` shows that closure
verbatim.  The `attempt` then supplies the graph membership with the
only term in scope at that position, the environment's
constructibility certificate, and Agda rejects it with a type error
at exactly that premise.  Result: exit 42, type error at
`:95.22-47` (`lookup (suc zero) γ' .snd` does not have the membership
type), 1.85 s total (1.02 s user), load 3.08 at start, one `agda`
process, `GHCRTS=-M8g`.
**MEASURED: the frame's `valK` is not derivable from the delivered
machinery and the consumer's held facts; the missing premise is the
graph membership `hc`, which the frame's type does not state.**

### Check 2: `sucK`, the frame's successor closure, at
`src/ProbeLJ1113B.lagda.md` module `CheckSucK` and
`src/ProbeLJ1113D.lagda.md` module `ControlSucʟK`

The reduction `reach` at `src/ProbeLJ1113B.lagda.md:57-61` is GREEN:
given the model-successor closure `sucʟK`, `sucK` follows in one
transport along the delivered `sucʟ-fst`
(`Numerals.lagda.md:152-157`).  The control `attempt` at
`src/ProbeLJ1113D.lagda.md:49-52` FAILS: the delivered closure field
`pairK` (the strongest closure field of the `KFacts` record) cannot
close `sucʟ a`, because `sucʟ a = unionʟ (pairʟ a (pairʟ a a))`
needs a union closure the record does not carry.  Probe B: exit 0,
1.14 s total (1.01 s user), load 3.21 at start.  Probe D: exit 42,
`pairK` does not have the successor-membership type, 1.38 s total
(1.01 s user), load 3.15 at start.  One `agda` process at a time,
`GHCRTS=-M8g`.
**MEASURED: `sucK` reduces to a union closure of K under the model
successor; the delivered closure fields do not supply it.**

### Check 3: `t0eq`, the frame's slot equality, at
`src/ProbeLJ1113C.lagda.md` module `CheckT0eq`

The attempted term `attempt` at `src/ProbeLJ1113C.lagda.md:47-48`
tries to transport the delivered `tagEq0` (stated at the `N0` slot)
to the `t0` slot.  Result: exit 42, `UnequalTerms N0 != t0` at
`:48.13-19`, 1.11 s total (0.98 s user), load 3.04 at start.  The two
indices are independent parameters of the consumer's telescope
(`Condensation.lagda.md:6683`), so no delivered path connects them.
This restates the [LJ-1.96] measurement
(`src/ProbeLJ193C.agda:66-67`, `N0 != t0`) at the current frame.
**MEASURED: `t0eq` is not derivable from the delivered machinery.**

### Check 4: `t0K`, the one PROVABLE verdict, at
`src/ProbeLJ1113E.lagda.md` module `CheckT0K`

The derivation `reach` at `src/ProbeLJ1113E.lagda.md:44-48` is GREEN:
transport `t0eq` into the delivered `numK0` field.  Exit 0, 1.13 s
total (1.00 s user), load 3.04 at start.
**MEASURED: `t0K` is provable from `t0eq` plus the delivered
`KFacts.numK0`; the PROVABLE count rests on a term, not a reading.**

## 3. The price for the rest

**One best-effort figure: about 250 in-fence lines to build the 28,
at the delivered model's own rate (P-m's parameterized band, about
0.01 to 0.02 s per line), about 3 to 5 s of cold check time.**

Basis: the 25 satisfier facts are one pattern, a K-closure lemma per
machine construction (roughly 5 to 7 distinct lemma shapes, 20 to 40
lines each), and the delivered `Model.lagda.md` already supplies the
adequacy theorems that reduce each satisfier fact to its closure
statement (P-l: the statements are about the concrete K slot, and the
closure lemmas can quantify over it).  The figure is a hypothesis
(P-l, P-m): no closure lemma of this family has been written in this
tree, and a comparable elsewhere is not a price.

**The widest unmeasured term: `someEnv`.**  It is the only fact whose
supplier is a construction, not a closure: an environment
`E ∈ K` satisfying `envHypB2`, built from the three memberships
(`LowerAgree.lagda.md:51-58`).  The machine's environment machinery
describes environments; it does not build one from K memberships.
**The probe that measures it:** state the construction generically at
the K slot, `(ya yc ar : S) → ya ∈ K → yc ∈ K → ar ∈ K → Σ E, E ∈ K
× envHypB2-satisfaction`, build it from the model's
`env`/`cons` constructors plus the level's constructibility, then
price the rest of the family at the measured per-lemma rate.

The `t0eq`/`t1eq` slot equalities are not priced as code: they are
equalities at the consumer's concrete indices, supplied by the
consumer's site (the rows already state them), and they cost the
consumer zero new machinery.

## 4. The C-39 section

One brief line blocked a route I can see.

1. "Do not edit anything under `src/L/Coding/`" blocks the route where
   the 25 satisfier-in-K closure lemmas are stated in
   `src/L/Coding/Model.lagda.md`, which is where their proofs "would
   live or fail" per the brief's own scope note.  That is the open
   route the classification names: the closure family is exactly the
   new content, and its canonical home is the coding model.  The
   prohibition is right for this dispatch (a reading and a probe, not
   a build), and the route stays open for the build that funds it.

No other brief line blocked a route.  The write scope
(`src/ProbeLJ1113*.agda` only) cost nothing: the classification is by
reading, and the probes fit the scope.  The "do not build twenty nine
proofs" line blocked nothing the task needs; the three machine checks
are deliberate, not a build.

## 5. Negatives classified

1. The delivered machinery proves `valK` as the frame states it:
   **MEASURED FALSE** (probe A, exit 42 at the missing graph
   membership).  The machinery proves `valK` with the `hc` premise
   added: **INFERRED TRUE** by `domEntryK`'s second projection
   (`src/ProbeLJ196A.agda:50-52`, green in [LJ-1.96]).
2. The delivered machinery proves `sucK`:
   **MEASURED FALSE** as a derivation from the closure fields
   (probe D); **MEASURED TRUE** as a reduction to the model-successor
   closure `sucʟK` (probe B).  The missing content is a union
   closure, INFERRED by the record's field list
   (`Condensation.lagda.md:5939-5980` has no union field).
3. The delivered machinery proves `t0eq`: **MEASURED FALSE**
   (probe C, `N0 != t0`).  `t1eq` is the same shape:
   **INFERRED FALSE** by the same independent-indices argument.
4. The delivered machinery proves `t0K`: **MEASURED TRUE**
   (probe E).
5. The other 24 satisfier-in-K facts are provable from the delivered
   machinery: **INFERRED FALSE**.  Each concludes K-membership from a
   satisfaction premise, and the machinery's own readers (the
   `*-adequate` family of `Model.lagda.md`) reduce each satisfaction
   to memberships the closure fields do not close; no verdict among
   the 24 rests on a machine check.
6. `someEnv` is provable from the delivered machinery:
   **INFERRED FALSE**.  No delivered term constructs the
   `envHypB2` environment from the three K memberships; the machine
   describes environments, it does not build them.
7. Any of the 29 is REFUTABLE: **INFERRED FALSE**.  Each is
   conditional on a satisfaction or membership premise; [LJ-1.97]
   measured the premise barrier for the satisfier family
   (`_build/lj-1.97-report.md:70-90`), and the current `sucK` shape
   has the same barrier (`src/ProbeLJ1112A.agda:76-86`).

## 6. The DD4 split

**25 of the 29 are about the CODING machinery; 4 are about the
TOWER.**

The coding half: `valK`, `valK-un`, the five `envK-*`, the four
`envInK-*`, `valV`, `valW`, `wKfact`, the six `subK-*`, the three
`consK-*`, and `sucK`.  Each concludes K-membership from the
satisfaction of a machine formula (`envSetAt`, `envOverAt`,
`tmValAt`, `subValAt`, `subValSuccAt`, `consAtL`) or closes K under
the successor the machine's own clauses use (`subValSuccAt` reads
`sucV`).  They are shared by construction: the J tower's coding will
state the same closure facts against its own machine, and the proofs
live in `src/L/Coding/Model.lagda.md` per the brief's scope note.

The tower half: `t0eq`, `t1eq`, `t0K`, `someEnv`.  These state facts
about the consumer's concrete slots (`t0`, `t1`) and about the
environment the tower's condensation actually builds.  `t0K` is a
derivation from `t0eq` and a record field; the other three are the
per-tower residue the J tower repeats.

The DD4 answer: the J tower repeats at most the 4 tower facts; the 25
coding facts are paid once, in the shared coding model.

## 7. Measurements

All five probes ran one `agda` process at a time, `GHCRTS=-M8g`, each
run started after the previous exited, on the shared machine
(4 users; the sibling cardinal agent holds the other slot).

| probe | file | result | seconds | load at start |
|---|---|---:|---:|---:|
| A, `valK` | `src/ProbeLJ1113A.lagda.md:90-95` | exit 42, type error at the graph-membership premise (`domEntryK c yc (lookup ... γ' .snd)`, `:95.22-47`) | 1.85 (1.02 user) | 3.08 |
| B, `sucK` reduction | `src/ProbeLJ1113B.lagda.md:57-61` | exit 0 | 1.14 (1.01 user) | 3.21 |
| C, `t0eq` | `src/ProbeLJ1113C.lagda.md:47-48` | exit 42, `N0 != t0` at `:48.13-19` | 1.11 (0.98 user) | 3.04 |
| D, `sucʟK` control | `src/ProbeLJ1113D.lagda.md:49-52` | exit 42, `pairK` does not close `sucʟ a` | 1.38 (1.01 user) | 3.15 |
| E, `t0K` | `src/ProbeLJ1113E.lagda.md:44-48` | exit 0 | 1.13 (1.00 user) | 3.04 |

No heap exhaustion, no kill, no wall.  The probes are scratch under
`src/`, gitignored by design (`scripts/check-probes.py` enforces the
never-commit rule).

`scripts/lint-agda.py --check` on all five probes: exit 0.  The two
failing probes carry their failing terms without interaction holes,
so the lint sees no forbidden construct; the failures are type
errors, which are the measurements.

`scripts/lint-prose.py --check _build/lj-1.113-report.md`: exit 0.

`scripts/check-unbound-hyp.py --check` on the five probes: **clean
(5 file(s))**, exit 0.  The checker reads the ```agda fences of the
probe files, so unlike [LJ-1.112]'s standalone probe this run is not
vacuous: none of the probe's telescope hypotheses is a premise-free
conclusion (rule 1), an unconstrained premise object (rule 2), or a
premise-free telescope (rule 3).  In particular the frame facts under
check (`valK`, `sucK`, `t0eq`, `t0K`) all carry their premises.

`scripts/ledger.py --brief` (the admissible size figure): standing
28,425 lines over 85 masters, measured from HEAD; thresholds
SUSPENDED per the ledger header.

No `make check` was run (brief prohibition).  No master was touched:
`src/L/Coding/`, `src/L/Condensation/`, `src/V/`,
`src/Everything.lagda.md` untouched.  No commit, no push.

The tree was clean at the dispatch point: `git status --porcelain`
empty, HEAD `126773f`, branch `two-tower-bridge` (the brief's
`75fa586` is the parent commit of the registration).

## ARCHIVE USED

- `_build/lj-1.112-report.md`, read WHOLE.  TOOK the 29-from-the-
  extended-frame count, the `sucK` addition (`:317-319`), the module-F
  application, and the zero-metas measurement.
- `src/ProbeLJ1112A.agda`, read WHOLE.  TOOK the extended consumer
  frame's 29 parameters (`:211-344`) and the consumer telescope.
- `_build/lj-1.100-report.md`, read WHOLE (section 2 especially).
  TOOK the 28-fact table and the NOT REFUTED analyses.
- `_build/lj-1.109-report.md`, read WHOLE.  TOOK section 2 (the
  `sucK` inhabitant: a constructibility level closed under
  V-successor, `:63-65`) and the KFacts-field wall.
- `_build/lj-1.96-report.md`, read WHOLE.  TOOK the `valK` needs-`hc`
  measurement (`:55-57`, `src/ProbeLJ196A.agda:50-52`) and the
  `t0eq`-from-`tagEq0` failure (`src/ProbeLJ193C.agda:66-67`).
- `_build/lj-1.97-report.md`, read WHOLE.  TOOK the ten refutations
  and the NOT REFUTED rows for the satisfier family.
- `src/L/Coding/Model.lagda.md`, read WHOLE.  TOOK the satisfaction
  readers and adequacy theorems the satisfier facts reduce through.
- `src/L/Condensation.lagda.md`, read `KFacts` (`:5939-5980`),
  `SatGraphAgree` (`:6682-6768`), and the row `back` sites (`:3250-3480`).
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, read WHOLE.
  TOOK the current frame telescope, the `valK` shape at `:86-88`, and
  `sucK` at `:186-188`.
- `src/L/Condensation/LowerAgree.lagda.md`, read `someEnvDef`
  (`:51-58`).
- `dev/LESSONS.md`, C-35 (`:3200-3241`), C-36 (`:3284-3331`), D-8
  (`:1377`), D-30 (`:3332-3380`), C-38 as extended (`:3427-3520`),
  C-39 (`:3521-3563`), P-x (`:3564-3601`), C-40 (`:3602-end`), read
  WHOLE.  TOOK the satisfiable-telescope standard, the
  prohibition-priority rule, the record-field wall, and the
  consumer-check discipline.
- `scripts/rules.py --for build` and `--for recon`, read all
  statements.

## LITERATURE

**Devlin 5.5 assumes no coding at all in the lemma's own statement and
proof:** the argument is condensation (5.4), the transitive-fixing of
the collapse, `|L_α| = |α|`, and the initial-ordinal chain
(`devlin-II5.md:150-158`, `dev2.txt:1369-1384`).  The coding enters
only upstream, inside the Def tower's level-hood certificate
(`devlin-II5.md:375-380`, item C2: the bounded object-level step
description), which is the analogue of the machine formulas this
dispatch measures.
