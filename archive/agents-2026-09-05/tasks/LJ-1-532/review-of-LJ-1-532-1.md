# LJ-1.532: adversarial review of LJ-1.532#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld
attacked: agents/tasks/LJ-1-532/lj-1.532-report.md and agents/tasks/LJ-1-532/review-of-approx-in-K.md
instance: LJ-1.532#1, role coder, model claude-opus-5, effort xhigh, heads_sha256 d5caf66f

## THE INVARIANT

The author of the return is the coder head. This review is the
mathematician_adversarial head. The critic is not the author.

The instance facts were not in the worktree copy of
`dev/pod/transitions/2026-08.jsonl`. That copy has 157 lines. Its last
line, `:157`, is `"task": "LJ-1.399", "tier": "wide", "to": "RETURNED"`.
The same record at the repository root holds the instance. Seq 2525
dispatches the coder (`model` claude-opus-5, `effort` xhigh,
`heads_sha256` d5caf66f, `obl_before` 1). Seq 2566 returns it. Seq 2569
records the facts and matches `stop-stated`. Seq 2570 dispatches this
review. The six facts agree with
`agents/tasks/LJ-1-532/runs/accept-1.out`: `exit_code` 0, `error_class`
null, `heap_wall` false, `lines` 0, `obligations_delta` 0,
`obligations_open` 1, `seconds` 1.29. Line 16 of that file reads
`run agents/tasks/LJ-1-532/Probe532.agda rc 0`. Line 25 reads
`# exit 0`. Line 22 reads `# obligations delta 0`.

## Q1. DOES THE VERDICT LINE MATCH ITS OWN BODY

It does.

The line at `agents/tasks/LJ-1-532/lj-1.532-report.md:3` and the stop
file `agents/tasks/LJ-1-532/review-of-approx-in-K.md:3` both say:
NO-GO, `approx-in-K` is not delivered, because the named statement is
false. The body supplies each part.

- The obligation name is absent as a term. The type that stands in for
  it is `ApproxInK` at `agents/tasks/LJ-1-532/Probe532.agda:108-117`.
  That type carries every frame hypothesis the chain uses: `K` is a
  limit level, the bound is an ordinal, and the bound lies in `K`.
- The reason is a green refutation, not a missing search.
  `ApproxInK-is-false` is at `Probe532.agda:206-209`. The acceptance
  run records `Probe532.agda rc 0` at `runs/accept-1.out:16`. The
  three isolated files are also green in that run: `Control532.agda`
  rc 0, `Section12.agda` rc 0, `W3.agda` rc 0 (`runs/accept-1.out:17-19`).
- The one-sentence summary, "the statement is false because `g` is not
  determined and `ApproxAt` does not see a non-pair", is what the body
  shows. `ApproxAt` is `domAt` and a step conjunct guarded by `appAt`
  (`src/L/Coding/Sequence.lagda.md:286-289`). `inDomAt` is an unbounded
  existential over pair membership (`src/L/Coding/Model.lagda.md:269-270`).
  The counterexample objects are at `Probe532.agda:170-193`. The
  membership failure is `sgl-ω∉Lω` at `:202-203`.
- The body also reports what is delivered beside the refutation: the
  pair agreement with `hierL`, the corrected statement `HierInK`, and
  `hier-is-approx`. None of that contradicts the line. A repair of a
  different type is not a delivery of `approx-in-K`.

The defect class of `[LJ-1.375]` and `[LJ-1.376]`, a verdict line that
its own body does not carry, is absent here. The stop file restates the
same line, the same type, and the same refutation.

The body is stronger than the line needs. Sections 3 to 5 inhabit three
terms the stop did not require. Those terms support the repair. They do
not inhabit the briefed obligation.

## Q2. DOES EVERY LOAD-BEARING `file:line` RESOLVE TODAY

Two classes. The first is clean. The second is a reporting defect.
None of the defects reach the verdict.

**CLEAN.** Every `src/` fact the refutation spends, and every
predecessor fact the NO-GO names as the remaining gap, opens at its
line. Verified this session:

- `src/L/Coding/Sequence.lagda.md:286-289` (`ApproxAt`), `:298-301`
  (`ApproxAt-value`), `:349` (the public rename `GraphAt` to
  `LsetGraphAt`). The equation the return writes for `LsetGraphAt` is
  the body of `GraphAt` at `:291-292`.
- `src/L/Coding/Model.lagda.md:269-270` (`inDomAt`), `:278-280`
  (`domAt`).
- `src/V/Coding.lagda.md:175-176` (`pr`).
- `src/V/Hierarchy.lagda.md:155-156` (`∈-irrefl`).
- `src/L/Constructible.lagda.md:83` (`isTransV`), `:141-142` (`IsOrd`),
  `:183` (`layer-trans`), `:246` (`Lset-layer`), `:319-320` (`Lset-in`).
- `src/L/Ordinal.lagda.md:77` (`∅-ord`).
- `src/L/Ordinal/Stages.lagda.md:265-268` (`ord∈Lset→∈`).
- `src/L/Coding/InL.lagda.md:363-364` (`sglʟ`), `:366-367` (`sglʟ-fst`),
  `:378` (`sglʟ-out`).
- `src/L/Axioms/Infinity.lagda.md:66` (`ω∈L`).
- `src/L/Axioms/Basic.lagda.md:160-161` (`LsetS`).
- `src/L/Hierarchy.lagda.md:274-278` (`approx-val`), `:382-419`
  (`graph-table`, with helpers at `:390-401` and `:403-415`, and
  `approx` at `:417-419`), `:507-508` (`hier-unique`, present and
  unused by the return), `:511-525` (`hier-out`), `:527-534`
  (`hier-in`), `:621-626` (`hierL`, `hierL-spec`), `:645-655`
  (`Lset-defines`).
- `src/L/Condensation.lagda.md:2492-2493` (`graphBndAt`).
- `src/L/BoundedSubset.lagda.md:108-111` (`levelHoodB`), `:69-71` (the
  environment comment), `:107` (the matrix comment `v = w`).
- `AGENTS.md:45` (a measured cure does not transfer by analogy).
- `agents/tasks/LJ-1-522/Probe522.agda:356-364` (`defPow-closed-noCode`).
  The `K ≡ Lset α` hypothesis itself is at `:360`.
- `agents/tasks/LJ-1-525/Probe525.agda:150-165` (`leaf-unbounds`).
  `agents/tasks/LJ-1-525/lj-1.525-report.md:112-122` records the
  undischarged level identification.
- `agents/tasks/LJ-1-527/Probe527.agda:184-200` (`body-unbounds`).
  `agents/tasks/LJ-1-527/lj-1.527-report.md:234` names row six's
  membership as a type.
- `agents/tasks/LJ-1-530/Probe530.agda:86-91` (`ω-IsLimit`), `:97-99`
  (`stage∈𝒟ₒ`), `:131-156` (`dK`). The `K ≡ Lset α` hypothesis of `dK`
  is at `:134`. `wK` is at `:243`.
- `agents/tasks/LJ-1-530/lj-1.530-report.md:1` (VERDICT GO), `:101-102`
  (the quoted wall: nothing collects the code and satisfaction family
  at one stage below `α`), `:209-216` (the seven-row table after
  `[LJ-1.530]`).
- `agents/tasks/LJ-1-494/lj-1.494-report.md:66-67` (the stage question
  on `hierL δ` and `Lset α`), `:116-118` (the pointer to `[LJ-1.230]`).
- `agents/tasks/LJ-1-230/lj-1.230-report.md:79`:
  `There is no `hierL b ∈ Lset …` fact.`
- `agents/tasks/LJ-1-228/lj-1.228-report.md:128-130` (the archive price
  and that nobody ran the two-way decode).
- `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:313-316` (`approx-agree`).
  `witB` itself is at `:141-147`. `step-agree` is at `:254-258`.
- The four recorded errors: `runs/w3-0.out:2` (`[NotInScope]` on `∥`),
  `runs/w3-1.out:2` (`[UnequalTerms]`, `⁅ a ⁆s` against pairing),
  `runs/full-0.out:2` (`[UnequalTerms]`, `LsetS` against an `isL`
  proof), `runs/full-2.out:2` (`[NotInScope]` on `StepAt`).
- `grep` of `postulate` and of `Σ₁-levelHood|σ₁-up|Σ₁-Σ₂` against
  `Probe532.agda` and `runs/W3.agda` returns no match. Both files open
  with `--safe`.
- The return's own archive and literature quotes that I opened:
  `archive/dev/LJ-dispatch-index.md:361`, `archive/dev/JOURNAL.md:807`,
  `dev/literature/level-formula-slot-roles.md:23`,
  `dev/literature/devlin-II5.md:339`.

**THE DEFECTS.** Five addresses are off, one figure is written two
ways, and one environment slot is numbered from the inner binder.

| claim | cited | actual |
|---|---|---|
| `[LJ-1.522]`'s `K ≡ Lset α` hypothesis | `Probe522.agda:359` | `:360` |
| `[LJ-1.530]`'s `K ≡ Lset α` hypothesis | `Probe530.agda:135` | `:134` |
| `[LJ-1.530]`'s quoted wall | `lj-1.530-report.md:102-103` | the sentence starts at `:101` |
| `StepB.witB` wrapper | `ProbeLJ1304A.agda:254-258` | `witB` is `:141-147`; `:254-258` is `step-agree` |
| `appAt` in `ApproxAt` | `Sequence.lagda.md:289` in the stop file | `appAt` is at `:288`; `:289` is the `Step` line |
| `LsetGraphAt` definition | `Sequence.lagda.md:291-292` | that line is `GraphAt`; the public name is the rename at `:349` |
| row seven, "slot 2 is the value `v`" | `BoundedSubset.lagda.md:69-71` | the outer listing at `:69-71` puts `v` at slot 1 and `γ` at slot 2; `var 2` equals `v` only inside the binder, which is what `:107` and `:111` say |

The `witB` line is inherited. `[LJ-1.530]`'s own table already points
row three at `ProbeLJ1304A.agda:254-258`
(`agents/tasks/LJ-1-530/lj-1.530-report.md:212`). The cited lines show
`step-agree`, which is row four's wrapper. The wrapper for row three
is the `witB` formula at `:141-147`. The memberships `[LJ-1.530]`
built are not in doubt: `wK` is at `Probe530.agda:243` and `dK` is at
`:131-156`.

**TWO WRITINGS OF ONE RSS FIGURE.** The price table at
`lj-1.532-report.md:232` gives peak RSS for `Probe532.agda` as
610,582,528 B. That is `runs/full-t3.time:2` and also
`runs/final.time:2`. The paragraph at `:280` gives 610,598,912 B.
That is `runs/full-t2.time:2`, the largest of the three rechecks.
Both numbers are tracked. The table is not the peak of the three
runs. The paragraph is. Neither number is near the 8 GB cap.

The defects do not reach the verdict. The refutation term sits at the
cited lines `Probe532.agda:206-209`. The type it refutes sits at
`:108-117`. The probe is green (`runs/accept-1.out:16`). A checker
who opens the off-by-one predecessor lines still finds the named
hypothesis on the next line. The `witB` mis-cite is a table row about
work already built, not about this obligation.

## Q3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

Complete enough to carry the verdict, with three named gaps. None of
the three changes the verdict.

1. **C-42 was injected and was not run.** The brief's law bundle
   includes C-42 (`dev/LESSONS.md:3752-3757`): a refutation measures
   one site, and the next action is a sweep of the shape. The return
   prices `HierInK` as the next brief and does not report a count.
   I ran the sweep this session. A search of live `src/` for
   `ApproxAt`, `LsetGraphAt` and `graphBndAt` shows:

   - The blindness is the `RecShape` formula at
     `src/L/Coding/Sequence.lagda.md:286-289`. The same shape is
     opened at `src/L/Choice/Table.lagda.md:407` and
     `src/L/Choice/Before.lagda.md:716`.
   - The bounded membership claim is one formula:
     `graphBndAt` at `src/L/Condensation.lagda.md:2492-2493`. Its live
     consumer is `LevelHood.levelHoodB` at
     `src/L/BoundedSubset.lagda.md:108-111`.
   - No other site states the briefed universal: every `g` that
     satisfies `ApproxAt` lies in `K`.

   So the false obligation is unique to this row. The formula that
   makes it false is shared. A cure of `HierInK` does not rewrite
   `ApproxAt`. The omitted count does not change what this task
   refuted.

2. **Section 3 is not the junk-addition term the prose says it is.**
   The return says the instance is cheap and the defect is not local,
   and that section 3 turns that sentence into a term
   (`lj-1.532-report.md:149`, `:227-256`). What section 3 inhabits is
   pair agreement with `hierL` (`pairs-into-hier` at
   `Probe532.agda:238-244`, `pairs-from-hier` at `:246-256`). That is
   enough to say two approximations on one ordinal differ only on
   non-pairs. It is not a term that adds a junk member to a non-empty
   approximation. The local refutation does not need that term. One
   counterexample refutes a universal.

3. **`hier-unique` is delivered and unused.**
   `src/L/Hierarchy.lagda.md:507-508` identifies two `IsHier` tables
   on one ordinal. Together with section 3 it would say: a pair-set
   restriction of `ApproxInK` is `HierInK`. The return reaches the
   same identification in words, by quantifying over the canonical
   witness. The omitted lemma is a shorter spelling, not a missing
   route.

The chain table after this task, rows 1, 2, 5, 6 and 7, matches the
cited files at the lines in Q2, with the row-3 wrapper address
corrected above. Row seven's reading, "there is `w ∈ K` with
`graphBndAt` and `v = w`", matches
`src/L/BoundedSubset.lagda.md:107` and `:108-111`. The extra
membership `⟨ Lset β ∈ Lset α ⟩` is correctly named as uncomposed:
`stage∈𝒟ₒ` is at `Probe530.agda:97-99` and `Lset-in` is at
`src/L/Constructible.lagda.md:319-320`. The return did not build it,
as AD12 required.

W3 named the term the brief asked for, `g` as a set, and named the
probe that measured it: `runs/W3.agda`, with the decisive miniature
`blind` at `runs/W3.agda:162-164`, moved to `Probe532.agda:191-193`.
Amendment A21 asks whether a mathematician's return named the term
and the probe. This return is a coder return. It both named them and
wrote them, because the brief ordered that.

## THE FOUR SLOT QUESTIONS

**Is the verdict correct on its own numbers?** Yes. The obligation
delta is 0 with one still open. The type `ApproxInK` forms. The
refutation is a green absurd pattern against that type at a concrete
instance that discharges every frame hypothesis: `K` is `Lset ω`, a
limit (`Probe532.agda:92-97`), the bound is `∅`, an ordinal in that
level (`:195-197`), and `⁅ ω ⁆s` satisfies `ApproxAt` (`:191-193`)
and is not in `Lset ω` (`:202-203`). The arithmetic of
`ord-not-pr` (`:131-153`) spends transitivity of an ordinal and
`∈-irrefl`. That is enough. The briefed name `approx-in-K` is a
weaker telescope. A counterexample that also carries the extra
hypotheses is a counterexample of the weaker type.

**Is the measurement sound?** Yes. I reproduced the medians from the
tracked files.

| file | walls | median | table |
|---|---|---:|---:|
| `runs/ctl-t1.time` to `ctl-t3.time` | 1.57, 1.58, 1.60 | 1.58 s | 1.58 s |
| `runs/w3-t1.time` to `w3-t3.time` | 3.41, 3.42, 5.52 | 3.42 s | 3.42 s |
| `runs/s12-t1.time` to `s12-t3.time` | 5.33, 5.08, 5.16 | 5.16 s | 5.16 s |
| `runs/full-t1.time` to `full-t3.time` | 9.48, 9.01, 9.05 | 9.05 s | 9.05 s |

The third W3 recheck is 5.52 s at `runs/w3-t3.time:1`, with 4,944
involuntary context switches against about 600 on the other two
runs. The median is still 3.42 s. Subtraction reproduces: 9.05 − 1.58
= 7.47 above imports; 5.16 − 1.58 = 3.58 for the refutation; 9.05 −
5.16 = 3.89 for the repair. Line counts reproduce: `Probe532.agda` is
349 lines, 181 non-blank and not a comment; `runs/W3.agda` is 164
lines, 85 of those. The RSS split in Q2 is the only figure defect,
and it is not load-bearing.

**Did the brief cause the outcome?** No. The brief ordered D-10
before any Agda, and it named this stop: if `g` is not reachable from
either route into `K`, name what `g` is built from and STOP
(`LJ-1.532.md:80-83`). A GO was reachable only if the universal was
true. The universal is false. The brief did not make it false. It
told the worker to stop when D-10 said the target was false, and the
worker did that. Two brief notes stand for the record and do not
foreclose the answer: the briefed type was a sketch, and the worker
filled the chain's hypotheses; and the brief forbade transferring
`[LJ-1.494]` as a settlement of membership in `K`. The worker
refuted the `K`-form on its own terms, then identified the surviving
statement with `[LJ-1.494]` under the standing hypothesis `K ≡ Lset
α`. That is the reading the brief allowed.

**Is there a cure the return missed?** No cure of the briefed type is
available. A pair-set restriction of `ApproxInK` is `HierInK`, by
section 3 and `hier-unique` (`src/L/Hierarchy.lagda.md:507-508`).
`HierInK` is uninhabited. `[LJ-1.494]` and `[LJ-1.230]` already
stopped on that membership. `hier-is-approx` at `Probe532.agda:346-349`
shows the canonical witness is an approximation, so the repair is not
a statement about an empty class. Weakening the obligation to inhabit
`HierInK` would have been a different task. The brief forbade that
weakening. Devlin 2.5 is stated at a limit `α > ω`
(`dev/literature/devlin-II5.md:339`). The tree's `IsLimit` does not
carry that side condition. The return's refusal to call `HierInK`
false is the W8 reading, and it is correct.

## THE VERDICT

**UPHELD.** The NO-GO is correct on its own numbers. The measurement
is sound. The enumeration carries the verdict. The return ships
reporting defects, the off-by-one predecessor citations, the `witB`
line inherited from `[LJ-1.530]`, the two RSS writings, the inner
slot numbering at row seven, and an unrun C-42 sweep. This review
corrects the addresses, reports the sweep count, and names the two
writings. None of that touches the mathematics. The task closes on
row `sys-critic-upheld-no-go`.

What the next brief should carry forward, in addition to the return's
own chain table: cite `witB` at
`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:141-147` and not at `:254-258`;
treat `HierInK` as `[LJ-1.494]`'s open fact, not as a new obstruction;
do not fund a rewrite of `ApproxAt` against this one row, because the
formula is shared and the false universal is not.

## ARCHIVE USED

Every CANDIDATE the block named is answered.

- **`archive/dev/JOURNAL.md`. READ.** `:807` reads:
  `u`'s slot is the definable powerset of the recorded value and the induction
  I opened it to confirm the return's archive citation. The quote
  resolves. It is about `dK`'s slot, which `[LJ-1.530]` paid. It is
  not evidence about `ApproxInK`.
- **`archive/dev/ORCHESTRATION.md`. READ LINE 1, NOT USED.** `:1`:
  `# ORCHESTRATION: the orchestrator's operating rules`
  It is the archived operating document. This review takes its
  process facts from `runs/accept-1.out` and from the transitions
  record. Declined for content.
- **`archive/dev/DD-archived.md`. READ LINE 1, NOT USED.** `:1` reads:
  THE `DD` RULING SERIES, archived in full 2026-08-18
  No archived DD row is load-bearing for this verdict. The live
  clauses that bind it are W3, W8, D-10 and C-42. Declined.
- **`archive/dev/PLAN-archived.md`. READ LINE 1, NOT USED.** `:1`:
  `# ARCHIVED 2026-08-20`
  The live screen is `dev/pod/screen.toml`. Declined.
- **`dev/ARCHIVE.md`. READ, NOT USED.** `:3`:
  `The registry of Bedrock's retired modules. One entry per module, written at`
  This task retires no module. No row is owed. Declined for content.

## LITERATURE USED

Every CANDIDATE the block named is answered.

- **`dev/literature/devlin-II5.md`. READ AND USED.** `:339`:
  `   - Def uniformly Δ₁^α at limit α > ω (2.5, `dev2.txt:663-666`).`
  This is why the return does not call `HierInK` false. The classical
  result carries `α > ω`. The tree's `IsLimit` does not. W8 stops a
  literature NO-GO only when the shape is an axiom with no condition
  this tree meets. That is not this case. The corrected statement
  stays an undelivered gap.
- **`dev/literature/BIBLIOGRAPHY.md`. READ LINE 1, NOT USED.** `:1`:
  `# Bibliography for the rud route`
  No bibliographic identity is in dispute. Declined.
- **`dev/literature/digest.md`. READ LINE 1, NOT USED.** `:1`:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`
  The one classical side condition this review needs is at
  `devlin-II5.md:339`. Declined.
- **`dev/literature/geology.md`. READ LINE 1, NOT USED.** `:1`:
  `# Geology dossier: set-theoretic geology sources and the five questions`
  This task is not a geology question. Declined.
- **`dev/literature/devlin-errata.md`. READ LINE 1, NOT USED.** `:1`:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  No erratum is load-bearing for the refutation of `ApproxInK`.
  Declined.
