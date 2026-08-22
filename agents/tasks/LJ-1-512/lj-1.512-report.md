# LJ-1.512 report: the honest forms cover 54 of 59, and 16 of them ask for something the record does not

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22,
`dev/LESSONS.md:2297`). No commit, no push. I wrote only in
`agents/tasks/LJ-1-512/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event, no WALL.

TARGET: one term `honest-covers-record` in
`agents/tasks/LJ-1-512/Probe512.agda`, plus the two required report sections.
Nothing lands in `src/`. I did not build the other 58 correspondences. I did
not build a `TFacts` value. I did not edit `src/` and I propose no redesign:
whether `TFacts` should be replaced by the honest forms is the
mathematician's call and this census is its evidence.

The standing direction (`dev/pod/direction.md:37`) reads

> **One SRC collection after LJ-1, not after `[LJ-2.5]`.** Owner, 2026-08-20.

This task is LJ-1 work. It does not start that collection and it does not
start phase 3. No Boundary clause is in conflict.

## VERDICT

**GO on the obligation, and the census is LARGE.**

1. **`honest-covers-record` typechecks.** `Probe512.agda:197-202`, top-level
   alias at `:204`, `--safe` at `:1`, exit 0, no hole, no postulate, no
   `TERMINATING`. Median **2.73 s** wall and **594 MiB** peak RSS over three
   forced rechecks of the full file (`runs/full-r0..r2.time`). It PASSes the
   program's witness meter: `/opt/homebrew/bin/python3.11 scripts/pod/witness.py
   --code LJ-1-512 --brief agents/tasks/LJ-1-512/LJ-1.512.md`, exit 0, 3.03 s,
   **0 UNRESOLVED of 1**, `probe_red=False` (`runs/witness-1.out`; re-run
   after the last edit at 2.31 s, `runs/witness-2.out`).
   `.venv/bin/python` is absent in this worktree, as `[LJ-1.499]`,
   `[LJ-1.508]`, `[LJ-1.510]` and `[LJ-1.511]` all found. I added no
   dependency.

2. **THE CENSUS SAYS PATTERN, NOT THREE ACCIDENTS. 54 of the 59 fields have
   an honest form somewhere in the tree, and 27 of them are in
   `src/L/Coding/EnvSupply.lagda.md` alone.** Only five fields have nothing:
   `codesK`, `codesK-un`, `t0eq`, `t1eq` and `t0K`.

3. **16 of the honest forms take a hypothesis the record's field does not**,
   and one more (`envSetK`) diverges the other way. The three fields already
   refuted are three of those 17. **The remaining 14 are not yet refuted; they
   are unmeasured.**

4. **The two forms do NOT correspond as written, and the reason is not
   mathematics.** EnvSupply's `Fact` members are stated at a tail of length
   `Vec S 2`; the record's are stated at `S ^ (11 + n)`. Neither is an
   instance of the other. Section 3 measures what that costs for
   `consK-exist` (nothing) and says why the same is NOT established for the
   `subK` and `val` families.

I did not write `review-of-honest-covers-record.md`. The obligation is
inhabited, so the verdict on the obligation is GO. The corrections below are
corrections of counts, not stops on the target.

**A NOTE ON THE RATIO BAR.** My write scope is one raw `.agda` probe and two
`.md` files. A raw `.agda` file carries no ` ```agda ` fence, so the in-fence
divisor is 0 and the bar cannot fire on this return.

## 0. THE PREDECESSORS, TAKEN FROM THEIR REPORTS

Audit F1 (`dev/pod/audit-2026-08-20.md:34`) says a module hypothesis taken
from a predecessor is the type that predecessor DELIVERED, read from its
report and its probe. I opened each.

- **`[LJ-1.510]` is GO** (`agents/tasks/LJ-1-510/lj-1.510-report.md:25`,
  which reads `**GO on the obligation, and a REFUTATION of the record.** Two
  results, and`). Its refutation is machine-checked at
  `agents/tasks/LJ-1-510/Probe510.agda:395`. I take the record's field type
  from `Probe510.agda:153-161` (`ConsKExist`) and the repaired type from
  `:205-215` (`ConsKExist⁺`), and I re-state both in my own file rather than
  importing a probe.
- **`[LJ-1.508]` is GO** (`agents/tasks/LJ-1-508/lj-1.508-report.md:23`,
  `**GO, AND THE BARE FORM IS ALSO REFUTED. Both results, exit 0.**`). Its
  measured missing input is about slot one.
- **`[LJ-1.511]` is GO** (`agents/tasks/LJ-1-511/lj-1.511-report.md:22`,
  `**GO. The corrected type is non-vacuous, and it is inhabited.**`). Its ONE
  added line is `Probe511.agda:79`, the truncated arity.
- **`[LJ-1.499]` is GO** and names `SupplyEnv.envK-gen` as the supplier
  (`agents/tasks/LJ-1-499/lj-1.499-report.md:31-33`).
- **`[LJ-1.509]`** is the `subK` family's dispatch and reads `[LJ-1.495]` as
  GO for the six-fold shift at `KValue`'s frame.

None of these is a NO-GO on a statement I inhabit here, so no stop is owed on
that account.

## 1. D-10, BEFORE ANY AGDA: THE COUNTS, RE-RUN

The brief says the mathematician's counts have been wrong twice and tells me
to re-run every count and print the command. I did.

**COUNT of `consK` in `src/`: 44, in four files.** Command
`grep -rn "consK" src/ | wc -l`, and `grep -rn "consK" src/ | awk -F: '{print $1}' | sort | uniq -c`:

| file | occurrences |
|---|---:|
| `src/L/Condensation.lagda.md` | 17 |
| `src/L/Coding/EnvSupply.lagda.md` | 14 |
| `src/L/Condensation/UpperAgree.lagda.md` | 7 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 6 |

**The brief's correction is itself correct**, and it reproduces
`[LJ-1.510]`'s numbers exactly.

**COUNT of `TFacts` field positions: 59, and the brief is right.** Command,
over the record body `src/L/Condensation/TwelveAgree.lagda.md:132-336`:

```
awk 'NR>=132 && NR<=336' src/L/Condensation/TwelveAgree.lagda.md \
  | grep -cE '^    [A-Za-z][A-Za-z0-9₀₁₂-]*[[:space:]]*:'
```

**AND THIS SETTLES AN ARITHMETIC `[LJ-1.508]` LEFT OPEN.** That report says
at `lj-1.508-report.md:372`

> **ONE ARITHMETIC I DID NOT SETTLE.** The brief says `TFacts` has 59 field

and reports 55 by the pattern `^    <name> :`. **The difference is exactly
four, and it is the character class.** The same command with an ASCII-only
name pattern returns 55; the four it drops are the subscripted names
`subK₁-and` (`:134` of the awk window, file line 265), `subK₀-and` (271),
`subK₁-imp` (277) and `subK₀-imp` (283). 55 + 4 = 59. **`[LJ-1.508]`'s method
was sound and its regex was not. The brief's 59 stands.**

**AND A DUPLICATE, MEASURED.** `numK1`
(`src/L/Condensation/TwelveAgree.lagda.md:146`) and `num1K` (`:185`) are
character-for-character the same type after renaming the field. So one of the
59 positions is a second copy of another. **The record has 58 distinct field
types in 59 positions.** Method: `sed -n '146p;185p'` on the master, with the
field name normalised, then string comparison.

## 2. THE OBLIGATION

`honest-covers-record` (`Probe512.agda:197-202`, alias `:204`):

```
honest-covers-record :
    (c1 c2 c3 c4 c5 c6 : S)
  → HonestConsKExist (lookup iK Kenv)
  → ConsKExist⁺ {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
```

Both endpoints are pinned to the tree by a certificate, and neither
certificate is used by the obligation:

- **`record-field-matches` (`Probe512.agda:84-90`)** reads `TFacts.consK-exist`
  at `ConsKExist` with no coercion and no `subst`. So `ConsKExist` IS the
  record's field type and Agda says so.
- **`honest-type-matches` (`Probe512.agda:124-126`)** reads
  `Fact.ConsK.consK-exist` at `HonestConsKExist`, likewise. So
  `HonestConsKExist` IS EnvSupply's delivered type
  (`src/L/Coding/EnvSupply.lagda.md:661-668`). `envConsK` there is `ConsK`'s
  own module parameter and is a bound variable in my term: **nothing is
  postulated, and `consK-exist` does not use it** (`consK-forall` and
  `consK-allin` do).

The correspondence is written ONCE at the generic frame, `covers-gen`
(`Probe512.agda:164-169`), and instantiated once at `KValue`'s frame. That is
W2 answered in the shape the clause asks for. **No `TFacts` field is used to
prove a `TFacts` field**: the only `TFacts` name in the file is inside
`record-field-matches`, which the obligation never calls.

**THE ANSWER TO THE BRIEF'S QUESTION IS YES, WITH ONE QUALIFICATION.** The
delivered honest form IS the record's field plus its missing hypothesis, at
this frame, for this field. The qualification is section 3.

## 3. WHERE THEY DIVERGE, AND WHAT IT COSTS

**THE TAIL IS THE DIVERGENCE, NOT THE MATHEMATICS.**

`Fact.ConsK.consK-exist` fixes its tail at `Vec S 2`
(`src/L/Coding/EnvSupply.lagda.md:661`). Every member of `module Fact` does:
each reads its `K` at `lookup (suc zero) γ'`
(`src/L/Coding/EnvSupply.lagda.md:497-498`), so the two cells are the carrier
and the bound. The record's field is at `S ^ (11 + n)`
(`src/L/Condensation/TwelveAgree.lagda.md:130-131`), and `S ^ n` is `Vec S n`
by definition (`src/FOL/Semantics.lagda.md:50`). So the honest form's
satisfaction hypothesis lives in an ELEVEN cell context and the record's in a
`20 + n` cell one. **Neither type is an instance of the other, at any `n`:
`20 + n = 11` has no solution.**

**FOR THIS FIELD THE GAP IS FREE, AND I MEASURED IT.** `tail-is-free`
(`Probe512.agda:147-155`) is the identity function, and it typechecks. The
reason is arithmetic on indices: `consAtL zero (suc zero) (suc (suc zero))`
reads cells 0, 1 and 2, and `var zero ∈̇ var (suc (suc (suc (suc zero))))`
reads cells 0 and 4. **All five are inside the nine cell prefix the two forms
share**, so the two satisfactions are the same proposition and no transport
is needed. In particular `consAtL-transport`
(`src/L/Coding/Model.lagda.md:1499-1510`) is NOT needed, and its `g` with
`fst (lookup d₁ γ) ≡ env g`, which this field is never given, is therefore
not a cost.

This is `[LJ-1.510]`'s `depth-is-free` (`Probe510.agda:130-135`) read at the
HYPOTHESIS instead of the conclusion. **I re-measured it at this site rather
than transferring it** (`AGENTS.md:45`).

**AND FOR TEN OTHER FIELDS IT IS NOT ESTABLISHED. THIS IS THE SENTENCE THE
NEXT BRIEF SHOULD READ TWICE.** The seven `subK-*` honest forms read index 8,
and `valV`, `valW` and `wKfact` read index 6 of a nine or ten cell prefix.
For example `subK₁-and` (`src/L/Coding/EnvSupply.lagda.md:497-504`) states
`subValAt (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ...` over
`(x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')` with `γ' : Vec S 2`: **index 8 is the
tail's second cell, outside the shared prefix.** The record's `subK₁-and`
(`src/L/Condensation/TwelveAgree.lagda.md:265-270`) names the same numeral 8
over an `18 + n` cell context, where it is again the tail's second cell, so
the SHAPE agrees. Whether the identity coercion still typechecks there is
**UNMEASURED**, and a measured cure does not transfer by analogy
(`AGENTS.md:45`). The likely recipe is to instantiate `γ₂` at the record
frame's own first two tail cells, which is what I did here
(`Probe512.agda:194-195`), but I did not test it and I do not report it as a
result.

## THE HONEST FORM CENSUS

Method: I listed the 59 field names and their file lines from
`src/L/Condensation/TwelveAgree.lagda.md:132-336` with the command in section
1, then read each declaration and searched `src/` for a term of the same
shape. **Verdicts: `ENVSUPPLY` = an honest form exists in
`src/L/Coding/EnvSupply.lagda.md`; `ELSEWHERE` = an honest form exists in
`src/` outside that file; `NONE` = nothing in `src/` delivers it.** The
`differs` column says whether the honest form takes a hypothesis the record's
field does not.

`KFacts` (`src/L/Condensation.lagda.md:6079-6115`) is another RECORD, so a
declaration there would not count as a delivery. It counts because
`KValue.facts` (`src/L/Condensation.lagda.md:7411-7425`) INHABITS all
fourteen of its fields with real terms. That is the delivery I cite.

| # | field | line | verdict | honest form | differs |
|---:|---|---:|---|---|---|
| 1-12 | `tagEq0`..`tagEq11` | 133-144 | ELSEWHERE | `KFacts.tagEq0`..`11` `src/L/Condensation.lagda.md:6082-6093`, inhabited by `refl` at `:7413-7415` | no |
| 13-24 | `numK0`..`numK11` | 145-156 | ELSEWHERE | `KFacts.numK0`..`11` `:6094-6105`, inhabited by `B.num∈λ k` at `:7416-7419`; also `Fact.EnvClosure.numK` `src/L/Coding/EnvSupply.lagda.md:682-684`, all twelve from `numK0` and `sucK` | no |
| 25 | `innerK` | 157 | ELSEWHERE | `KFacts.innerK` `src/L/Condensation.lagda.md:6106-6107`, inhabited `:7420` | no |
| 26 | `pairK` | 159 | ELSEWHERE | `KFacts.pairK` `:6110-6111`, inhabited `:7423` | no |
| 27 | `codesK` | 162 | **NONE** | 19 module hypotheses in `src/L/Condensation.lagda.md` and 3 record fields; no term | n/a |
| 28 | `codesK-un` | 168 | **NONE** | same | n/a |
| 29 | `valK` | 173 | ENVSUPPLY | `Fact.valK` `src/L/Coding/EnvSupply.lagda.md:462-469` | **YES** `(C T : S)` and `⟨ fst T ∈ fst K ⟩` |
| 30 | `valK-un` | 177 | ENVSUPPLY | `Fact.valK-un` `:471-478` | **YES** same |
| 31 | `t0eq` | 181 | **NONE** | `TmVal.t0eq` `src/L/Condensation.lagda.md:3066-3067` is a TYPE abbreviation, not a term | n/a |
| 32 | `t1eq` | 182 | **NONE** | `TmVal.t1eq` `:3069-3070`, likewise | n/a |
| 33 | `t0K` | 183 | **NONE** | `TmVal.t0K` `:3072-3073`, likewise | n/a |
| 34 | `num1K` | 185 | ELSEWHERE | identical to this record's own `numK1` (`:146`); `KFacts.numK1` `src/L/Condensation.lagda.md:6095`, inhabited `:7416` | no |
| 35 | `envK-mem` | 186 | ENVSUPPLY | `SupplyEnv.envK-mem` `src/L/Coding/EnvSupply.lagda.md:293-302` | no |
| 36 | `envK-neg` | 192 | ENVSUPPLY | `SupplyEnv.envK-neg` `:304-313` | no |
| 37 | `envK-top` | 198 | ENVSUPPLY | `SupplyEnv.envK-top` `:315-324` | no |
| 38 | `envK-imp` | 204 | ENVSUPPLY | `SupplyEnv.envK-imp` `:326-336` | no |
| 39 | `envK-allin` | 210 | ENVSUPPLY | `SupplyEnv.envK-allin` `:338-349` | no |
| 40 | `envInK-mem` | 216 | ENVSUPPLY | `SupplyEnv.envInK-mem` `:364-374` | no |
| 41 | `envInK-neg` | 223 | ENVSUPPLY | `SupplyEnv.envInK-neg` `:376-386` | no |
| 42 | `envInK-top` | 230 | ENVSUPPLY | `SupplyEnv.envInK-top` `:388-398` | no |
| 43 | `envInK-imp` | 237 | ENVSUPPLY | `SupplyEnv.envInK-imp` `:400-412` | no |
| 44 | `valV` | 244 | ENVSUPPLY | `Fact.valV` `:594-602` | **YES** `⟨ fst z ∈ K ⟩` and `⟨ fst a ∈ K ⟩` |
| 45 | `valW` | 250 | ENVSUPPLY | `Fact.valW` `:604-612` | **YES** `⟨ fst z ∈ K ⟩` and `⟨ fst b ∈ K ⟩` |
| 46 | `wKfact` | 256 | ENVSUPPLY | `Fact.wKfact` `:614-624` | **YES** `⟨ fst z ∈ K ⟩` and `⟨ fst a ∈ K ⟩` |
| 47 | `transK` | 262 | ENVSUPPLY | `SupplyEnv.transK` `:272-274`; at the frame it is `KFacts.arityK` `src/L/Condensation.lagda.md:6114-6115` with the binders swapped (`src/L/Condensation/TwelveAgree.lagda.md:347-352`), inhabited by `B.trans∈λ` at `:7425` | no |
| 48 | `subK₁-and` | 265 | ENVSUPPLY | `Fact.subK₁-and` `src/L/Coding/EnvSupply.lagda.md:497-506` | **YES** `⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩` |
| 49 | `subK₀-and` | 271 | ENVSUPPLY | `Fact.subK₀-and` `:508-517` | **YES** same |
| 50 | `subK₁-imp` | 277 | ENVSUPPLY | `Fact.subK₁-imp` `:519-528` | **YES** same |
| 51 | `subK₀-imp` | 283 | ENVSUPPLY | `Fact.subK₀-imp` `:530-539` | **YES** same |
| 52 | `someEnv` | 289 | ENVSUPPLY | `SupplyEnv.someEnv` `:417-448` against `someEnvDef` `src/L/Condensation/LowerAgree.lagda.md:52-58` | **YES** `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, which is `[LJ-1.511]`'s one added line (`Probe511.agda:79`) |
| 53 | `subK-neg` | 290 | ENVSUPPLY | `Fact.subK-neg` `src/L/Coding/EnvSupply.lagda.md:541-550` | **YES** `⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩` |
| 54 | `envSetK` | 306 | ENVSUPPLY | `SupplyEnv.envSetK` `:140-146` | **THE OTHER WAY**: the honest form PINS `B` to `B₀` and drops the record's `⟨ fst B ∈ K ⟩`, so it does not cover the record's generic-`B` field |
| 55 | `subK-un` | 311 | ENVSUPPLY | `Fact.subK-un` `:552-561` | **YES** `⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩` |
| 56 | `consK-exist` | 317 | ENVSUPPLY | `Fact.ConsK.consK-exist` `:661-668`, again at `Fact.ConsKClosed.consK-exist` `:742-749` | **YES** `⟨ fst ya ∈ fst K ⟩`. THIS TASK'S OBLIGATION |
| 57 | `consK-forall` | 322 | ENVSUPPLY | `Fact.ConsK.consK-forall` `:631-644`, again at `:712-725` | **YES** three: `{k} (g : Fin k → V ℓ)` with `fst z ≡ env g`, `⟨ fst z ∈ K ⟩`, `⟨ fst x ∈ K ⟩` |
| 58 | `subK-allin` | 326 | ENVSUPPLY | `Fact.subK-allin` `:563-573` | **YES** `⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩` |
| 59 | `consK-allin` | 332 | ENVSUPPLY | `Fact.ConsK.consK-allin` `:646-659`, again at `:727-740` | **YES** the same three as `consK-forall` |

**TOTALS: ENVSUPPLY 27, ELSEWHERE 27, NONE 5.** 27 + 27 + 5 = 59.

**THE FIVE WITH NOTHING ARE TWO GROUPS, AND THEY ARE DIFFERENT PROBLEMS.**
`codesK` and `codesK-un` are the code-shape decoders: `src/` names them 22
times and every one is a hypothesis or a record field, never a term.
`t0eq`, `t1eq` and `t0K` are about the two tag slots `t0` and `t1`, which
`KFacts` does not have at all: its fourteen slots are the carrier, the bound
and the twelve arity tags (`src/L/Condensation.lagda.md:7387-7389`). **So no
frame in the tree currently offers `t0` and `t1` anything.**

**THE NINE `envK`/`envInK` ROWS TAKE NO EXTRA HYPOTHESIS BUT ARE NOT FREE
EITHER.** Their honest forms fix the tail at `B₀ ∷ []` and the carrier at
`B₀ = LsetS gam ordγ` (`src/L/Coding/EnvSupply.lagda.md:293-297`), and their
`K` is the concrete `Lset lam`, not a slot. `[LJ-1.499]` already discharged
that restriction for the five `envK` at `KValue`'s frame and returned GO
(`agents/tasks/LJ-1-499/lj-1.499-report.md:20`). **The four `envInK` are the
same shape and were not part of that obligation.**

## HOW MANY DIFFER

**16 of the 54 honest forms take a hypothesis the record's field does not.
One more diverges the other way. 37 match.**

| group | rows | count | what the honest form adds |
|---|---|---:|---|
| `subK-*` | 48, 49, 50, 51, 53, 55, 58 | **7** | `⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩`, the graph slot in `K` |
| `valK`, `valK-un` | 29, 30 | **2** | `(C T : S)` and `⟨ fst T ∈ fst K ⟩`, the same slot |
| `valV`, `valW`, `wKfact` | 44, 45, 46 | **3** | `⟨ fst z ∈ K ⟩` plus one of `⟨ fst a ∈ K ⟩`, `⟨ fst b ∈ K ⟩` |
| `consK-*` | 56, 57, 59 | **3** | `⟨ fst ya ∈ K ⟩` for `exist`; the environment witness plus `zK` and `xK` for the other two |
| `someEnv` | 52 | **1** | the truncated numeral arity |
| **subtotal, honest form asks for MORE** | | **16** | |
| `envSetK` | 54 | **1** | the honest form asks for LESS and delivers less: `B` is pinned to `B₀` |
| **match exactly** | 1-26, 34-43, 47 | **37** | |

**THE NUMBER THE MATHEMATICIAN NEEDS IS 16, AND THE SHAPE INSIDE IT MATTERS
MORE THAN THE TOTAL.**

- **NINE OF THE 16 ASK FOR ONE AND THE SAME THING**: that the graph slot,
  `lookup (suc zero) γ'`, is a member of `K`. That is the seven `subK-*` plus
  `valK` and `valK-un`. `[LJ-1.508]` measured that `src/` states this
  NOWHERE: its sweep returns COUNT 0 for the shape and it reports at
  `lj-1.508-report.md:381-382` that the 22 declarations
  **carry ONE debt, at the slot, and paying it once at the frame pays all 22**.
  My census agrees from the other side: **the honest forms have been asking
  for it all along.**
- **THREE OF THE 16 ARE THE THREE ALREADY REFUTED** (`valK` by `[LJ-1.508]`,
  `consK-exist` by `[LJ-1.510]`, `someEnv` by `[LJ-1.507]` and `[LJ-1.511]`).
  **The other 13 are unmeasured, not sound.** A refutation measures the site
  it names and never how far the shape extends (C-42, `dev/LESSONS.md:3752`),
  so this census is the count and NOT the cure.
- **THREE OF THE 16 ARE NOT A SINGLE MEMBERSHIP.** `consK-forall` and
  `consK-allin` need the environment witness `g` with `fst z ≡ env g`, which
  is a different kind of hypothesis from a membership, and they need
  `envConsK`, which `[LJ-1.259]` built on ONE new hypothesis and
  `[LJ-1.261]` supplied. `consK-exist` needs neither, which is why it was the
  cheap one and why it is this task's obligation.

**WHAT THIS EARNS, IN THE BRIEF'S OWN TERMS.** The brief says a GO with a
LARGE census says the record should be replaced by the forms the tree already
proves. **The census is large: 54 of 59, and 27 in one chapter.** But the
replacement is not free and the price is not one number:

1. **16 field types would change**, and 9 of the 16 change by the SAME
   hypothesis, so the frame pays it once.
2. **The 37 that match are a straight substitution.**
3. **The 5 with nothing stay declarations.** No census can replace them.
4. **The tail must be reconciled** (section 3). Free for `consK-exist`,
   unmeasured for the other 26 `ENVSUPPLY` rows.
5. **`envSetK` is the one row where the record is STRONGER**, so a
   replacement there LOSES generality in `B` unless the honest form is
   re-stated.

## 4. W3, AND WHAT IT MEASURED

W3 is the census, and the brief said to do it FIRST and to write it in as it
went. I did: the report skeleton was written before any Agda ran, and the
census section was filled from reading before the obligation was attempted.
**The brief estimated "mostly reading, under 20 seconds of Agda" and told me
not to fund it against any predecessor. The census cost no Agda at all**: it
is `grep` and reading. The obligation cost 2.73 s median.

W3's own question was: do the honest forms cover most of the record, or
three? **They cover 54 of 59.** By the brief's own rule that is the large
case, and the mathematician has a redesign to rule on.

## 5. PRICES

Three forced rechecks of the full file, `agda agents/tasks/LJ-1-512/Probe512.agda`
with `Probe512.agdai` deleted before each, `/usr/bin/time -l`:

| run | wall | peak RSS | exit |
|---|---:|---:|---:|
| `runs/full-r0` | 2.73 s | 594.0 MiB | 0 |
| `runs/full-r1` | 2.73 s | 594.0 MiB | 0 |
| `runs/full-r2` | 2.99 s | 594.0 MiB | 0 |

**MEDIAN WALL 2.73 s. MEDIAN PEAK RSS 594.0 MiB** (622,903,296 bytes). These
three ran against the file as delivered, after the last edit; an earlier
triple on a draft of the same file gave 4.91, 3.53 and 3.60 s
(`runs/final.time` is a fourth run at 3.09 s). No heap event at any run, at
the wide caliber `-A64m -I0 -M8g`. The probe is 204 lines.

Comparable, for shape only and funding nothing: `[LJ-1.510]` measured 4.44 s
median on a 507 line probe at the same frame
(`agents/tasks/LJ-1-510/runs/full-r0.time`).

## 6. W2 AND W4

**W2.** The correspondence is written once at `TFacts`'s own generic shape,
`covers-gen` (`Probe512.agda:164-169`), over `K : Fin (5 + n)` and
`γ' : S ^ (11 + n)`, and instantiated at `KValue`'s frame in exactly one
place (`:204-210`). The three supporting types `ConsKExist`, `ConsKExist⁺`
and `tail-is-free` are generic in `n` too. **No fixed form is the statement's
home, and no deadline pushed me toward one.** DD4's core constraint is at
`archive/dev/DD-archived.md:22`.

**W4.** Nothing is retired by this task and nothing moves to `archive/`. The
clause's second half asks me to price the ideal form written fresh today
against the chapter I have. **For `TFacts` the honest answer is that this
census IS that pricing, and it is the mathematician's to act on**: the ideal
form of 54 of the 59 fields is already written in `src/L/Coding/EnvSupply.lagda.md`
and `src/L/Condensation.lagda.md`, and the record re-declares them at a
different tail with 16 hypotheses removed. I propose no move, because the
brief forbids a redesign proposal and because a record redesign is not a
module retirement.

## 7. WHAT THE NEXT BRIEF NEEDS

1. **The 9-row graph-slot debt is ONE task, not nine.** `[LJ-1.508]` priced
   it at the frame; my census says the honest forms already take it. The next
   dispatch that pays `valSub` at `KValue`'s frame closes the hypothesis for
   `valK`, `valK-un` and all seven `subK-*` at once.
2. **The tail reconciliation is UNMEASURED for 26 of the 27 `ENVSUPPLY`
   rows** and it is the cheapest next probe: one identity coercion per
   family, four families. If it is free everywhere, the replacement is
   mechanical; if it is not, the honest forms must be re-stated generically
   in the tail before any replacement.
3. **`codesK`, `codesK-un`, `t0eq`, `t1eq` and `t0K` have no supplier at
   all.** Those five are the record's real residue and no census will shrink
   them.
4. **`num1K` is a duplicate of `numK1`.** One position is free.
5. **`envSetK` runs the other way** and needs a decision, not a proof.

## 8. THE WORKING TREE

Files I created, all inside my write scope:

- `agents/tasks/LJ-1-512/Probe512.agda` (204 lines)
- `agents/tasks/LJ-1-512/lj-1.512-report.md` (this file)
- `agents/tasks/LJ-1-512/runs/` (`full-r0..r2.out`, `full-r0..r2.time`, `final.out`, `final.time`, `witness-1.out`, `witness-2.out`)

I did not create `agents/tasks/LJ-1-512/review-of-honest-covers-record.md`.
I did not touch `src/`. I did not commit and I did not push.
`/opt/homebrew/bin/python3.11 scripts/gate/check-probes.py --check` is clean
(5801 tracked files, no probe outside `agents/tasks/`).

The three files `review-LJ-1-512-1.md`, `-2.md` and `-3.md` were already
present and untracked in this directory when my task started. **They are
critic BRIEFS the program staged, not reviews, and they are not mine.** I did
not write them and I did not edit them.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ.** `:329` reads

  > `| LJ-1.259 | Build the env closure | BUILDS ON ONE NEW HYPOTHESIS. 3 consK CLOSE`

  and `:330` reads

  > `| LJ-1.261 | The finite-supremum merge | BUILDS. finSetK is SUPPLIED, 3 consK CLOSE`

  These two rows are the record that the `consK` family's supplier was built
  and closed in 2026, and they are why `module Fact.EnvClosure` and
  `module Fact.ConsKClosed` exist in `src/L/Coding/EnvSupply.lagda.md`. I
  cite them for census rows 56, 57 and 59.
- **`archive/dev/DD-archived.md`: READ.** `:22` reads

  > `| DD4 | **MAXIMUM REUSE is the architecture's objective, and it is the same rule as WRITE IT GENERIC.**`

  This is W2's source and I answer it in section 6.
- **`archive/dev/JOURNAL.md`: NOT USED, declined.** `grep -c` for `TFacts`,
  `consK` and `EnvSupply` returns 0, 0 and 0. It carries nothing about this
  record.
- **`archive/dev/JOURNAL-archived.md`: NOT USED, declined.** Same three
  counts, 0, 0 and 0.
- **`archive/dev/ORCHESTRATION.md`: NOT USED, declined.** Same three counts,
  0, 0 and 0. It is the archived flow document and this is a mathematical
  census.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`: READ.** `:92` reads

  > `HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.`

  Relevant because the truncated numeral arity
  `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` is the hypothesis in nine honest forms
  (the five `envK-*`, the four `envInK-*`) and is `someEnv`'s one added line
  (census row 52). The lemma is why that truncation is harmless where the
  conclusion is itself a proposition, which is the case at every one of those
  nine rows: each concludes `⟨ _ ∈ _ ⟩`.
- **`dev/literature/devlin-II5.md`: NOT USED, declined.** It is the source
  dossier for the Condensation Lemma's mathematics. This task compares two
  Agda type declarations against each other and reads no set theory.
- **`dev/literature/terms-2026-08.md`: NOT USED, declined.** It is the
  terminology dossier for a naming ruling. I introduce no term.
- **`dev/literature/digest.md`: NOT USED, declined.** It pins the orthodox
  form of the rud route, which is `[LJ-2]` territory.
- **`dev/literature/geology.md`: NOT USED, declined.** Set-theoretic geology
  is unrelated to this record.
