# LJ-1.354 report: DD25 review of `[LJ-1.351]`'s `graphWitK` refutation

tier: pi (pi-subagent-mode), the adversarial row. The critic is not the
author (DD17). Written incrementally (C-22). Every negative is MEASURED or
INFERRED, in those words. `src/` untouched. Nothing landed, nothing repaired.

## 0. VERDICT

**UPHOLD.**

**`[LJ-1.351]` measured what it says it measured.** I re-ran its probe
untouched: `agents/tasks/LJ-1-351/Refute351.agda`, **exit 0 in 1.95 s** warm,
against my own floor of **0.62 s**. I re-derived every chapter citation myself
(C-44). None had drifted. I verified the scope identity, the twelve clauses,
the eight `closedAt` tags, the `arityNumAtL` bound and the `KValue` record from
source. I found **one loose sentence** in the target's answer table. It changes
no verdict. Details in section 3.

**Four of the six construction ties are now false.** The family finding is
route-level. A repair funded on `graphWitK` would have been assumed at both
towers and would have been unsound at both.

| claim under test | verdict | basis |
|---|---|---|
| the probe re-runs green | **YES, MEASURED** | exit 0 in 1.95 s, section 8 |
| the tie at `:7288-7297` is `graphWitK`, today | **YES, MEASURED** | re-derived, section 1 |
| the transcription is the chapter's statement | **YES, MEASURED** | section 1, sizes and slots match |
| the premise is a closed term | **YES, MEASURED** | `Refute351.agda:364-370`, all components read |
| the twelfth clause is not vacuous | **YES, MEASURED** | `Refute351.agda:299-308`, section 2 |
| `Wire` runs on `KValue.facts`, no extra hypothesis | **YES, MEASURED** | instantiation audited (C-45), section 2 |
| the three-instance control holds | **YES, with one precision** | section 3 |
| `arityNumAtL` closes the tie | **MEASURED FALSE** | `Refute351.agda:414-428`, section 4 |
| the target's REASON for that is correct | **YES, MEASURED** | four sites re-read, section 4 |
| the shape occurs at more than one statement | **MEASURED FALSE** | my own sweep, section 5 |
| the word FALSE needs a qualifier | **MEASURED FALSE, it does not** | section 6 |
| the target honoured C-58 | **YES, MEASURED** | `Refute351.agda:116-123`, read |
| anything landed in `src/` | **MEASURED FALSE** | `git status --short`, section 10 |

## 1. THE TIE AND THE TRANSCRIPTION, RE-DERIVED (C-44)

The chapter is 7435 lines today. I re-derived every citation the target gives.
All reproduce at the same lines:

| what | where, today | checked |
|---|---|---|
| the outer `graphWitK` | `src/L/Condensation.lagda.md:7288-7297` | read |
| `SatGraphAgree`'s own `witK` | `src/L/Condensation.lagda.md:7009-7018` | read, `sed` |
| the wiring line | `src/L/Condensation.lagda.md:7319-7321` | read |
| `module SatGraphAgree` | `src/L/Condensation.lagda.md:6961` | read |
| the other `witK`, refuted by `[LJ-1.348]` | `src/L/Condensation.lagda.md:7233-7235` | read |
| `closedAt`'s eight tags | `src/L/Coding/Model.lagda.md:2181-2188` | read, tags 2 3 4 5 8 9 10 11 |
| `botClauseAt` | `src/L/Coding/Model.lagda.md:1281-1282` | read, tag 7 |
| `arityNumAtL` trio | `src/L/Coding/CodeSet.lagda.md:185-207` | read |
| `KValue` and its `facts` | `src/L/Condensation.lagda.md:7380-7435` | read |
| `ChainZ`, `sgltK` | `src/L/Condensation.lagda.md:2820`, `:6227` | grepped |

**The transcription is the chapter's statement.** The probe writes
`w K : Fin n` and `γ : S ^ n`; the chapter writes `w K : Fin (5 + m)` and
`γ : S ^ (8 + m)`. At `n = 5 + m` the environments have equal size and every
slot address agrees: `var (6 + w)` reaches the carrier, `lookup (3 + K)`
reaches the bound, in both. The frame facts sit at the same slots, because the
probe's `γ⁺` is the chapter's `γ` under the three-slot shift. MEASURED, by
reading both telescopes. The Wire instance runs at `n = 14`, which is the
chapter's `m = 9`. So the countermodel lands inside the chapter's instance
space.

**Scope identity, the `[LJ-1.345]` discipline.** The probe's `⊨` is
`L.Coding.Model`'s `AbsL.⊨ᵐ`. `Model.lagda.md:72` and
`Condensation.lagda.md:76` open the SAME `FOL.Absoluteness.Single 𝒮ᵥ isL
isL-trans`, with `isL` from `L.Constructible` at `Model.lagda.md:44` and
`Condensation.lagda.md:25`. The chapter imports `twelveAt` from
`L.Coding.Graph` at `:56` and `closedAt` from `L.Coding.Model` at `:52-54`.
The probe imports the same two. **This is not a refutation of a look-alike.**
MEASURED.

## 2. NON-VACUITY, ALL FOUR LAYERS

**Layer 1: the premise is a closed term at all three points.**
`Refute351.agda:364-370` builds `pin , (closed , (dom , (app , twelve)))`. I
read every component. `pin` is `refl` at `:360`. `closed` at `:250-273` uses
only the shared refusal `bad`. `dom` at `:288-297` uses `domAt-intro`,
`inE` and `cS∈dS`. `app` at `:275-283` uses `entry∈eS`. `twelve` at
`:310-357` uses the refusal eleven times and `botC` once. **No component
assumes anything beyond the module's frame parameters.** MEASURED, by reading
and by exit 0.

**Layer 2: the twelfth clause is not vacuous.** `botClauseAt` is
`unClauseAt C T 7 (emptyAt zero)` at `Model.lagda.md:1281-1282`. The term at
`Refute351.agda:299-308` does real work: it reads the entry back with `inE`,
gets `fst yc ≡ # 0` through `numeralL-fst 0`, and kills membership in the
value with `∅-empty`. The clause demands that the value at a tag-7 code is
empty. The countermodel's value IS empty, which is the true value of `bot`.
**A nonempty value would not pass this term.** INFERRED, from the term's
structure. I built no red file for it. The term itself is MEASURED, by exit 0.

**Layer 3: the conclusion holds at a good point.** See section 3, with the
precision.

**Layer 4: `Wire` runs on the delivered record, with NO extra hypothesis.**
This is the layer the brief flagged, so I audited the instantiation, not the
telescope (C-45). `module Wire` at `Refute351.agda:476` takes exactly seven
parameters: `lam`, `ordλ`, `succλ`, `∅∈λ`, `gam`, `ordγ`, `γ∈λ`. `KValue` at
`Condensation.lagda.md:7380-7382` takes exactly those seven. Its `facts` at
`:7413-7435` is built from them with no further hypothesis. `Wire` opens
`KValue`, takes `facts`, and produces `live-false` at `:488`,
`live-false-num` at `:491`, `live-bad-premise` at `:494` and `live-good` at
`:504`. **The five closure facts arrive from the chapter. Nothing here
restates one.** MEASURED, by reading both telescopes. The contrast with
`[LJ-1.350]` is real: its report at `agents/tasks/LJ-1-350/lj-1.350-report.md`
line 234 records 「ONE hypothesis is mine, `#1∈γ`」. **`[LJ-1.351]`'s `Wire`
carries no hypothesis of that shape.** MEASURED, by reading both.

## 3. THE THREE-INSTANCE CONTROL

`module Point` at `Refute351.agda:185` takes two arguments, the arity and the
payload. The three instances are in the green file:

| instance | line | arity | payload | premise | first conclusion |
|---|---|---|---|---|---|
| `Bad1` | `:400` | `Kv` | `numeralL 0` | inhabited, `:370` | **REFUTED**, `:408-412` |
| `Bad2` | `:405` | `numeralL 0` | `Kv` | inhabited, `:370` | **REFUTED**, `:414-419` |
| `Good` | `:439` | `numeralL 0` | `numeralL 0` | inhabited, `:445-454` | **HOLDS**, `:455-456` |

`Good` differs from `Bad1` in one argument. `Good` differs from `Bad2` in one
argument. The premise term is the same generic code for all three, because
`module Point` never inspects either argument. The second conclusion also
holds at `Good`, `:459-461`. **The standard this week set is met.** MEASURED,
by the re-run and by reading.

**THE ONE LOOSENESS THIS REVIEW FOUND.** The tie's conclusion is a TRIPLE.
The target's answer table says 「the conclusion holds at a good argument」 with
basis `:455-461`. Those lines prove the FIRST conclusion and the SECOND. The
third, `f ∈ K` with `f = lookup w γ`, is unmeasured at `Good`. It needs a
carrier-in-bound fact that is not among the five the probe takes. The target's
section 6 text states exactly which two conclusions it proved, so the report
is honest in its body. The table row is loose by one conjunct. **The
looseness does not change the verdict, because the refutation runs through the
FIRST conclusion only, and that is the one the control controls.** MEASURED
(first two) and MEASURED FALSE (no term for the third in the file).

## 4. DOES THE DELIVERED BOUND CLOSE THE TIE? NO. THE REASON IS CORRECT

**The measurement.** `bad2-arityNum` at `Refute351.agda:424-428` builds
`⟨ Bad2.γ⁺ ⊨ arityNumAtL (suc zero) ⟩` through the chapter's own
`arityNumAtL-in` (`CodeSet.lagda.md:201-207`). At `Bad2` the arity is
`numeralL 0`, a genuine numeral, and the payload is the bound. The bound
HOLDS there. `graphWitK-false-num` at `:414-419` refutes the tie at that same
countermodel. **So the bound holds and the tie is still false.** MEASURED, by
the re-run.

**The reason, re-checked at four sites.**

1. `[LJ-1.350]`'s tie died at an arity conjunct. Its report, line 226, says
   「ONLY the arity conjunct is [refuted]」 at its witness. Its cure
   (`Cure350.agda:81-88`) concludes `∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁`, an arity
   statement. Read.
2. `graphWitK` has no arity conjunct. Its premise at `:7288-7294` is the pin,
   `closedAt`, `domAt`, `appAt` and `twelveAt`. Its conclusion at
   `:7295-7297` is three memberships in `K`. Read.
3. `arityNumAtL-out` at `CodeSet.lagda.md:189-192` concludes
   `fst (lookup c γ) ≡ pr (# m) (fst z)`, an equation. It never concludes a
   membership in a slot. Read.
4. The `Bad2` refutation works through the PAYLOAD, not the arity: two
   `prSnd` steps reach `Kv ∈ bnd`, refused by `∈-irrefl`. The poison sits in
   the payload. Read at `:414-419`.

So the reason holds: an arity bound cannot close a tie whose failing
conclusion is a membership, and the countermodel carries its poison in the
payload. **The claim that no composition of `arityNumAtL-out` yields a
membership is INFERRED.** The term at `Bad2` is the measurement, and the
measurement is enough for the verdict. The target says the same and marks its
own survey of payload bounds as not done. That is honest.

**One limit the target states and I confirm.** `arityNumAtL` WOULD exclude
`Bad1`, whose arity is the bound. The target built no term for that exclusion
and neither did I. It does not matter: `Bad2` settles the question alone.

## 5. THE SWEEP, RE-DERIVED (C-42)

I ran the sweep myself. `grep "∧̇ twelveAt" src/` gives **5 hits**:

| site | what it is | read |
|---|---|---|
| `src/L/Condensation.lagda.md:7015` | the tie, as `SatGraphAgree`'s `witK` parameter | yes |
| `src/L/Condensation.lagda.md:7294` | the tie, as the outer `graphWitK` | yes |
| `src/L/Condensation.lagda.md:7069` | `body-out`, a consumer | yes |
| `src/L/Condensation.lagda.md:7151` | `body-back`, a consumer; it TAKES `dK` and `eK` at `:7154` | yes |
| `src/L/Coding/Graph.lagda.md:111` | `satGraphOn`, private, the definition | yes |

The two tie sites are ONE statement: `:7319-7321` wires `graphWitK` into
`SatGraphAgree`'s `witK` slot. I went one level further, as C-42 orders. I
grepped `witK`, `WitK`, `SatGraphAgree` and `LeafAgree` over all of `src/`
with `--include="*.lagda.md"`. **Nothing appears outside
`src/L/Condensation.lagda.md`.** So there is no second chapter and no V-side
counterpart of this shape. **The count is one statement at two sites. The
refutation does not extend to a family of this exact shape.** MEASURED.

The family the orchestrator counts, four of six false, spans several shapes:
`witK` (`[LJ-1.348]`), the arity conjuncts (`[LJ-1.350]`), `graphWitK`
(`[LJ-1.351]`). Their common boundary is the one `[LJ-1.349]` section 8
named: a tie that concludes a bound membership from closure predicates alone,
with no membership premise, is false. `graphWitK` sits inside that boundary at
all three conclusions.

## 6. DOES THE WORD NEED A QUALIFIER? NO

`[LJ-1.349]` section 4 ruled that `witK`'s 「MEASURED FALSE」 needed the
qualifier 「no uniform supplier」. The reason: `witK`'s premise is EMPTY at
some environments, so a supplier could exist there vacuously, and the falsity
was pointwise.

**`graphWitK` is stronger, and the difference is measured.** The premise term
lives in `module Refute`, which is generic in `w`, `K`, `γ` and the five
facts. I read every component in section 2: **no component uses any fact.**
So the premise is inhabited at EVERY admissible frame. And
`graphWitK-false` refutes the tie at every frame that carries the five facts.
Those five are `KFacts` fields, and `LeafAgree` binds the full record, so
every chapter instantiation carries them. **Within the statement's own range,
the tie is empty at every admissible frame and its premise is never empty.**
MEASURED, by the module structure and the re-run; instantiated at the
delivered record by `Wire`.

So no qualifier is needed. The word FALSE is uniform here. The one boundary
to state: uniformity ranges over `KFacts` frames, which is the statement's
own range. A frame without the facts is not a chapter frame.

## 7. DD4, WITH THE AXIS NAMED (C-46)

**The axis is AC-AGAINST-GCH**, fixed at `scripts/measure/ledger.py:49-51`,
whose `--reuse` report computes what the AC and GCH closures share.

**The refutation is class-free.** MEASURED, by reading the whole probe: the
names are `pr`, `pr-inj`, `#-inj`, `prʟ`, `numeralL`, `⁅_,_⁆`, `#_`, `∅`,
`∅-empty`, `arityNumAtL`, `∈-irrefl`, `isL-trans` and five `KFacts` fields.
**Not one mentions AC, GCH, a well-ordering or a cardinal.** As with its three
siblings, the falsity holds at both carriers by one file. Nothing lands, so no
shared line moves. What the task removes is a false parameter from
`LeafAgree`'s telescope, which both towers use.

## 8. SECONDS, LOAD, RUNS (C-53, C-12)

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. Slot count `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run
before every invocation: **0 both times, two counts, two invocations.**

| run | exit | seconds |
|---|---:|---:|
| `agents/tasks/LJ-1-354/Floor354.agda` (empty, mine) | 0 | **0.62** |
| `agents/tasks/LJ-1-351/Refute351.agda` (re-run, untouched) | **0** | **1.95** |

My 1.95 s is warm on the probe's interface. The target's 12.38 s was its cold
elaboration of its own new file, and it said so in its section 9. **No figure
of mine is comparable with any other task's**, and none is offered as one. No
invocation came near the wall. No heap exhaustion. Nothing was interrupted.

## 9. THE ABORT CRITERION, ANSWERED

**UPHOLD.** The tie is false, the premise is inhabited, the refutation runs on
the delivered record, and the word needs no qualifier. Four of the six
construction ties are false. The family is a route-level finding. Nothing has
been landed on this tie, so the uphold costs nothing but the record.

## 10. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-354/`: this report and `Floor354.agda`.
**`src/` is untouched.** I read `src/L/Condensation.lagda.md`,
`src/L/Coding/Model.lagda.md`, `src/L/Coding/Graph.lagda.md` and
`src/L/Coding/CodeSet.lagda.md`, and opened none for writing. The two
expected-red probes, `agents/tasks/LJ-1-344/Supply344.agda` and
`agents/tasks/LJ-1-350/MustFail350.agda`, were not opened, not run and not
repaired. `dev/PLAN.md` was modified before this task began; I did not touch
it. I did not open `src/Everything.lagda.md`. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. **No `make check`.** No em dash
in any language. `.venv/bin/python scripts/gate/lint-prose.py --check` and
`.venv/bin/python scripts/gate/lint-agda.py --check` both exit 0.
`.venv/bin/python scripts/dispatch/rules.py --for review` was run and every
statement was read, with the full entries opened for C-42, C-44, C-45, D-10
and P-l.

## 11. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-351/lj-1.351-report.md`, read WHOLE.** **Line read:**
  section 0, 「THE PREMISE IS NOT A DODGE. IT IS CORRECT MATHEMATICS.」
  **TOOK** the whole report as the object of review and checked every row of
  its answer table against source and re-run. **CONFIRMED all but one table
  row, which is loose by one conjunct** (section 3 above).
- **`agents/tasks/LJ-1-349/lj-1.349-report.md`, read WHOLE.** **Line read:**
  section 7, 「the row should read INFERRED until the sibling's or a
  follow-up's countermodel is green with its premise term」. **TOOK** the
  commission and verified its discharge: the premise term exists at
  `Refute351.agda:364-370` and the file is green. **TOOK** its section 4
  qualifier precedent to decide section 6 above.
- **`agents/tasks/LJ-1-350/lj-1.350-report.md`, sections 2, 3 and 4 read.**
  **Line read:** line 234, 「ONE hypothesis is mine, `#1∈γ`, which makes the
  carrier NON-EMPTY」. **TOOK** the contrast and verified it: `[LJ-1.351]`'s
  `Wire` needs no such hypothesis. **TOOK** its line 226 arity-conjunct
  reading to check the target's reason in section 4.
- **`archive/dev/TASKS-archived.md`, header `:1-9` read.** **Line read:**
  「Nothing here is a live task. Read it for history.」 **TOOK SHAPE ONLY**, a
  retired dispatch index. **REJECTED every figure:** that route has a
  different carrier and no `KFacts` record, so nothing in it prices anything
  here.

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:246-256`, read.**

**The one line the brief asks for: a tie of this shape has NO counterpart in
Devlin's text.** His 2.2 to 2.4 write `D(v, u)` as Σ₁ and 「bind every
unbounded quantifier by the concrete set `K(u)`」. The digest calls 「the Σ₀
matrix `C(w, v, u)` with `w = K(u)`」 the bounded satisfaction substrate.
Devlin FIXES the carrier and builds the code set and the satisfaction table
inside it. **He never concludes that a code set is in the bound; he builds it
there.** Our tie frees `d` and `e` as the hypothesis's own bound variables and
then asks closure predicates to recover three memberships. The refutation
measures that the recovery is impossible. **WHY NOT the rest:** `:240-245` is
the settled `[LJ-1.12]` Δ₀ question. `:258` onward is Step D, the definable
well-order, which this tie does not reach.

## 13. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the chapter citations drifted | **MEASURED FALSE.** All re-derived, section 1 |
| the transcription misstates the tie | **MEASURED FALSE.** Sizes and slots match, section 1 |
| the probe refutes a look-alike scope | **MEASURED FALSE.** Same `AbsL`, section 1 |
| the premise assumes something beyond the frame | **MEASURED FALSE.** Section 2, layer 1 |
| all twelve clauses are vacuous | **MEASURED FALSE.** `botC` at `:299-308` |
| `closedAt` speaks at tag 7 | **MEASURED FALSE.** Eight tags read, section 1 |
| `Wire` needs an extra hypothesis | **MEASURED FALSE.** Instantiation audited, section 2 |
| `arityNumAtL` closes the tie | **MEASURED FALSE.** `:414-428`, section 4 |
| the target's reason for that is wrong | **MEASURED FALSE.** Four sites re-read, section 4 |
| the shape occurs at more than one statement | **MEASURED FALSE.** My sweep, section 5 |
| the word FALSE needs a qualifier | **MEASURED FALSE.** Section 6 |
| a run hit a wall | **MEASURED FALSE.** Longest 1.95 s, section 8 |
| the third conclusion holds at `Good` | **UNMEASURED.** No term in the file; the table row is loose |
| a nonempty value would pass `botC` | **INFERRED FALSE.** Term structure, section 2 |
| no composition of `arityNumAtL-out` yields a membership | **INFERRED.** Section 4 |
| anything landed in `src/` | **MEASURED FALSE.** `git status --short`, section 10 |
