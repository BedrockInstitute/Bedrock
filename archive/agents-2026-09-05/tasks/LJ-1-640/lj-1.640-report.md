# [LJ-1.640] report: the bill's site is a least-cardinal site EXACTLY WHEN it is an AMBIENT cardinal, and `IsCardinalL` does not buy that

## HEAD

head_slot: coder
machine: shared
task: LJ-1.640
obligation: agents/tasks/LJ-1-640/Probe640.agda::bill-site-is-least
verdict: **GO on the obligation, NEGATIVE on the campaign question.**
The term typechecks and is green: `runs/final-6.out`, exit 0, 4.07 s,
963.9 MB peak, under the 300 s cap, and it postdates the last edit of
both source files (`Probe640.agda` mtime 1787682018, `runs/W3.agda`
mtime 1787681729). It also PASSES the program's
own witness meter: `witness: 0 UNRESOLVED of 1, 3.62 s,
probe_red=False`. The caliber on every run is the program's
`GHCRTS=[-A64m -I0 -M2g]`, read from the pane and recorded in every
`.out`. I did not set it. One Agda process ran at a time. No hole and
no postulate stands in either file. Nothing was written under `src/`.
No commit, no push. `git status` shows only `agents/tasks/LJ-1-640/`
as new.

**I did NOT write `review-of-bill-site-is-least.md`, and that is a
decision, not an omission.** My standing clause says a `review-of-*.md`
is how a coder states a NO-GO, and that a NO-GO means the brief's type
was NOT inhabited. This brief's type is a DISJUNCTION in prose: "either
a witness that `κ` is `κL a oa` for some `a`, or the term naming what
the tree cannot supply". **I inhabited it, in the form that carries
BOTH halves at once**: the witness is delivered, and the one input the
tree cannot supply stands named in the telescope. Writing a review-of
file would say I built nothing, and I built the strongest form of the
answer the brief allowed. The negative half is in this report in full.

This report was a skeleton on disk before any Agda ran and was filled
as each answer landed (C-22).

## THE ANSWER IN ONE LINE

**Being a least-cardinal site and being an AMBIENT cardinal are the
SAME condition at an ordinal L-element**, and `least-site⟺amb`
(`Probe640.agda:182-188`) proves both directions. **Neither direction
spends `IsCardinalL`.** So the bill's site is a least-cardinal site if
and only if `IsCardinal (fst κ)` holds there, and the bill hands in
`IsCardinalL κ`, which is the strictly weaker CODED form.

**The above-`ω` half is therefore NOT finished, and the one
construction it still owes is now named, measured and priced to a
single named crossing:** `IsCardinal (fst κ)` at the bill's site,
which is `[LJ-1.533]`'s `AmbToCodeᵀ` applied at that site.

## THE TERM

`agents/tasks/LJ-1-640/Probe640.agda` is 188 lines, 89 of them code.
`agents/tasks/LJ-1-640/runs/W3.agda` is 100 lines, 40 of them code.

| row | what | evidence |
|---|---|---|
| `AmbMinimalAt` | the minimality shape `c4-from-min` wants and `κ-min-atL` delivers | `runs/W3.agda:53-55` |
| `coded-minimal` | **`IsCardinalL` IS a minimality, at the CODED predicate.** The row is the identity | `runs/W3.agda:60-64` |
| `amb-card→amb-minimal` | `IsCardinal` IS the same minimality at the AMBIENT predicate | `runs/W3.agda:68-69` |
| `delivered-direction` | the direction src/ HAS, taken by import: `ambient→internal` | `runs/W3.agda:79-80` |
| `IntToAmb` | the missing converse. NAMED, NOT INHABITED | `runs/W3.agda:93-94` |
| `gap-is-the-crossing` | the missing converse IS `[LJ-1.533]`'s `AmbToCodeᵀ`, imported not copied | `runs/W3.agda:96-100` |
| `LeastSite` | "`κ` is `κL a oa` for some `a`", the brief's own words as a type | `Probe640.agda:60-61` |
| `kappaL-is-ambient-cardinal` | **`κL a oa` is an AMBIENT cardinal. Unconditional, four lines** | `Probe640.agda:67-76` |
| `least-site→amb` | the ONLY IF half | `Probe640.agda:78-80` |
| `least-at-self-pointwise` | the IF half, with the input narrowed to ONE member and ONE injection | `Probe640.agda:92-104` |
| `amb→least-at-self` | the IF half at the full ambient hypothesis | `Probe640.agda:106-110` |
| `bill-site-is-least` | **THE OBLIGATION**, at the brief's telescope | `Probe640.agda:116-120` |
| `internal-is-redundant` | the obligation's `IsCardinalL κ` slot is DERIVABLE from the added input, so it is dead weight | `Probe640.agda:122-123` |
| `bill-site-is-least-pointwise` | the obligation at the narrowed input | `Probe640.agda:129-133` |
| `amb→min-inputs` | the missing input buys `c4-from-min`'s two open hypotheses DIRECTLY, with no detour through `κL` | `Probe640.agda:141-147` |
| `least-site⟺amb` | **THE ANSWER IN ONE TYPE** | `Probe640.agda:182-188` |

**The obligation, exactly as inhabited, so the next brief can quote it
without opening the probe** (`Probe640.agda:116-120`):

    bill-site-is-least :
        (κ : SL.S) (oκ : IsOrd (fst κ)) → IsCardinalL κ
      → IsCardinal (fst κ)
      → LeastSite κ

with `LeastSite κ = Σ[ a ∈ SL.S ] Σ[ oa ∈ IsOrd (fst a) ] (κL a oa ≡ κ)`
(`Probe640.agda:60-61`), and the witness it returns is `a := κ`,
`oa := oκ`.

**The spelling against the brief's.** The brief writes `(κ : S)`; the
probe writes `(κ : SL.S)`, the same carrier under a name that cannot be
confused with the ambient one. This is `[LJ-1.638]`'s convention
(`agents/tasks/LJ-1-638/Probe638.agda:129`) and `IsCardinalL` demands
that carrier anyway (`src/L/Cardinal.lagda.md:230`). The brief's
`<either a witness ... or the term naming what the tree cannot
supply>` is the pair `IsCardinal (fst κ) → LeastSite κ`: the fourth
argument NAMES what the tree cannot supply, the conclusion IS the
witness.

**`IsCardinalL κ` IS NOT SPENT IN THE BODY.** `bill-site-is-least`'s
body is `κ , oκ , amb→least-at-self κ oκ amb`; `cκ` never appears.
`internal-is-redundant` (`Probe640.agda:122-123`) says why that is not
an oversight: the added input already implies it, through the tree's
own `ambient→internal`. The brief's third hypothesis is dead on this
route and the report says so.

## WHAT THE STATEMENT COST, AND WHAT THE SHAPE RESISTED

**Nothing resisted. Every run meant to be green was green on its first
attempt**, with one exception that was a two-token fix, recorded below.

- `kappaL-is-ambient-cardinal` is the row I expected to be hard and it
  is four lines. `κ-min-atL` refutes an injection from `fst a`, not
  from the site; composing `κ-injL` in front of the given injection
  converts one into the other. The only friction was bookkeeping: the
  member `δ` arrives as an ambient `V ℓ` and `κ-min-atL` quantifies
  over the L-carrier, so `κoL` plus `mem-ord` plus `ordL` lift it. All
  three are delivered.
- **THE ONE FAILED RUN, AND IT WAS NOT THE MATHEMATICS.**
  `runs/final-1.out` is exit 42 with ONE unsolved meta at
  `Probe640.agda:97`. `↾-reflects` (`src/FOL/ZFStructure.lagda.md:164-167`)
  has implicit `{𝒮}` and `{M}` that the elaborator cannot invert out of
  the goal type, because `SL.S` reaches it as the unfolded `Σ` and not
  as `ZFStructure.S (𝒮ᵥ ↾ isL)`. Supplying `{𝒮 = 𝒮ᵥ} {M = isL}` closed
  it, and `runs/final-2.out` is green. I did not re-run the same code:
  the code changed.
- **The two `_↪_` definitions did not collide.** `IsCardinal` is stated
  at `L.BoundedSubset`'s `_↪_` (`src/L/BoundedSubset.lagda.md:1043-1044`)
  and every other row here is at `L.Cardinal`'s
  (`src/L/Cardinal.lagda.md:47-48`). Both are transparent abbreviations
  of the same `Σ`, so conversion crosses them with no transport. This
  is a measurement, not an assumption: `amb-card→amb-minimal`
  (`runs/W3.agda:68-69`) and `kappaL-is-ambient-cardinal` both cross it
  and both are green.
- **Nothing had to be weakened.** The statement is the brief's, with
  the brief's own hypothesis list, plus the one named input the answer
  requires.

## WHAT I DID NOT BUILD, AS THE BRIEF REQUIRED

**No square law and no conjunct 4.** `grep -n "Init\|sq\b" Probe640.agda
runs/W3.agda` returns nothing: no type and no term in either file names
`Init`, `Init4` or `sq`. `amb→min-inputs` (`Probe640.agda:141-147`)
produces TWO of `c4-from-min`'s THREE hypotheses and stops; the third,
the descending `∥ sq β ∥₁` induction hypothesis
(`agents/tasks/LJ-1-638/Probe638.agda:216`), is untouched, and
`c4-from-min` is never applied.

**The two hypothesis types in `amb→min-inputs` are COPIED from
`agents/tasks/LJ-1-638/Probe638.agda:214-215`, not imported, and that
is a declared departure from the import-not-copy discipline.** The
drift-proof alternative is to apply `c4-from-min` to its first two
arguments, and its result type names `Init4`, which this brief forbids.
I chose the brief. **The residual risk is real and it is named here so
the successor checks it in one application**: the moment any task
applies `c4-from-min` at the bill's site, a drift between the copy and
`Probe638.agda:214-215` shows up as a type error and not as a silent
wrong answer.

## W3: DOES `IsCardinalL κ` PIN `κ` AS A LEAST ELEMENT OF ANYTHING

The brief named this the widest unmeasured term and estimated 60 to
120 lines. **`runs/W3.agda` is 100 lines, 40 of them code, and it was
typechecked ALONE before the probe frame existed**: `runs/w3-2.out`,
exit 0, 3.83 s, 664.7 MB, warm; `runs/w3-3.out`, 3.42 s, 664.7 MB,
after the last edit. (`runs/w3-1.out` is the same file green at
39.94 s and 1802.1 MB: that run built the `L.BoundedSubset`,
`L.CardinalAbove`, `LJ-1-533.Probe533`, `LJ-1-528.Probe528` and
`LJ-1-526.Probe526` interfaces cold. The difference between the two
runs is the interface build, not the term.)

**GO, AND THE ANSWER IS YES, AT THE WRONG PREDICATE.**

`IsCardinalL κ` pins `κ` as a least element, and `coded-minimal`
(`runs/W3.agda:60-64`) is that fact written as a type: the row is the
IDENTITY, `coded-minimal κ c = c`. **`IsCardinalL` is already a
minimality statement; it is minimality at the CODED predicate**
(`src/L/Cardinal.lagda.md:230-233`). What `c4-from-min` wants, and what
`κ-min-atL` delivers, is minimality at the AMBIENT predicate
(`AmbMinimalAt`, `runs/W3.agda:53-55`). `amb-card→amb-minimal`
(`runs/W3.agda:68-69`) shows `IsCardinal` is exactly that, the
truncation absorbed by the `⊥`-valued goal.

**So the question is not whether `IsCardinalL` is a minimality. It is
which predicate it is a minimality AT, and the two predicates are
ordered ONE WAY in the tree.**

- **The direction src/ HAS**: `ambient→internal`
  (`src/L/CardinalAbove.lagda.md:102-104`), imported, not copied, at
  `runs/W3.agda:79-80`. It runs through `readL`
  (`src/L/CantorBernstein.lagda.md:33-38`): a code yields an ambient
  injection, so refusing every ambient injection refuses every coded
  one. **`IsCardinalL` is the WEAKER predicate.**
- **The direction src/ DOES NOT HAVE**: `IntToAmb`
  (`runs/W3.agda:93-94`). NAMED, NOT INHABITED.
- **And it is not a new wall.** `gap-is-the-crossing`
  (`runs/W3.agda:96-100`) derives `IntToAmb` from `[LJ-1.533]`'s
  `AmbToCodeᵀ` (`agents/tasks/LJ-1-533/Probe533.agda:111-114`), TAKEN
  BY IMPORT so the two cannot drift. `[LJ-1.533]` recorded that
  crossing as having no producer anywhere in the tree, in the line the
  brief's premise 5 quotes: "Code buys ambient. Ambient buys nothing"
  (`agents/tasks/LJ-1-533/lj-1.533-report.md:1`, section
  `## WHAT CODES AN AMBIENT INJECTION`).

**THE LIMIT OF THIS MEASUREMENT, STATED AS A LIMIT AND NOT AS A
RESULT.** `gap-is-the-crossing` runs `AmbToCodeᵀ → IntToAmb`. **I did
NOT prove the converse, and I did not prove `IntToAmb` unreachable.**
`IntToAmb` may be strictly weaker than the full crossing, and a route
to it that does not code an arbitrary injection is not excluded by
anything in this task. What IS measured is that the one crossing which
would deliver it is the walled one, and that the C-42 sweep below finds
no term in `src/` producing `IsCardinal` at a site handed in from
outside. That is a stop under the Boundary and I did not go past it.

## THE NARROWING, AND IT IS THE CHEAPEST THING THIS TASK LEAVES

`bill-site-is-least-pointwise` (`Probe640.agda:129-133`) is the
obligation with the ambient hypothesis cut down to a single instance:

    (⟨ fst (κL κ oκ) ∈ˢ fst κ ⟩
      → ∥ ⟪ fst κ ⟫ ↪ ⟪ fst (κL κ oκ) ⟫ ∥₁ → Empty.⊥)

**The demand is at ONE member of the site and at ONE injection**, and
that injection is not arbitrary: it is `κ-injL κ oκ`
(`src/L/SquareLawClosed.lagda.md:82-84`), the witness `leastOf` selected.
`least-at-self-pointwise` (`Probe640.agda:92-104`) spends it exactly
once. So a successor that wants to code an ambient injection at this
site has to code ONE named injection, not a universally quantified
family. **That is a strictly smaller target than `AmbToCodeᵀ` and I
have not priced it.** Whether the selection's own construction leaves a
`Formula` reachable is a question for the site's author, not for this
task: `κ-injL` is `fst (snd least)` (`src/L/Cardinal.lagda.md:133-134`)
and it is sealed `opaque` (`src/L/SquareLawClosed.lagda.md:72-89`).

## C-42: THE SWEEP FOR THE MISSING INPUT, AND THE COUNT BEFORE ANY CURE

C-42 says a refutation measures ONE site and never measures how far the
shape extends, so the next action is the sweep and the COUNT comes
before any cure is priced. The shape is "ambient `IsCardinal` demanded
at a site". Here is the count, over today's `src/`.

**PRODUCERS of `IsCardinal` in `src/`: ONE, and it produces one only at
a site it BUILDS ITSELF.** `θ-card` (`src/L/CardinalAbove.lagda.md:160`),
inside `module Sep` (`:116`), gated on `⟨ θ ∈ˢ β ⟩`, which `θ∈β`
(`:166-175`) pays from a member of β that does not inject into `a`.
`cardAboveAt` (`:205-217`) discharges that gate and `noInjOrd`
(`src/L/CardinalAbove.lagda.md:575-576`) is built unconditionally, so
the tree DOES produce ambient cardinals. **It produces them ABOVE a
given ordinal, at a θ carved by separation. It says nothing about a
site handed in from outside**, which is the bill's case.

**SITES where `IsCardinal` is DEMANDED at a campaign site and left
UNPAID as a module hypothesis: FOUR.**

| site | the hypothesis |
|---|---|
| `src/L/BoundedSubset.lagda.md:1386` | `BoundedSubsetAt`, `cardκ` |
| `src/L/BoundedSubset.lagda.md:1746` | `BSA634`, `cardκ` |
| `src/L/StageBound.lagda.md:65` | `Instantiation`, `cardκ` |
| `src/L/StageBound.lagda.md:94` | the applying module, `cardκ` |

**Nothing in `src/` applies any of the four with `cardκ` discharged.**
`grep -rn "StageBound\|BSA634" src/` outside the two defining chapters
returns eight lines, and NOT ONE is an application. One is
`src/Everything.lagda.md:396`, a bare `import`. The other seven are
`L.InjChain`'s unrelated same-named LOCAL module
(`src/L/InjChain.lagda.md:75`) and its three uses
(`src/L/InjChain.lagda.md:275,293,587`, `src/L/Absorption.lagda.md:36,536,594`),
which take `(I : Type ℓ) (g : I → S)` and no cardinal at all.

**SO THE MISSING INPUT IS NOT NEW TO CONJUNCT 4.** Devlin 5.5's whole
leg already carries the same unpaid hypothesis at the same kind of
site. A cure funded against conjunct 4 alone would be funded against
one of five demands.

**AND THIS TASK MOVES THE COUNT.** `kappaL-is-ambient-cardinal`
(`Probe640.agda:67-76`) is a SECOND producer, unconditional,
untruncated, four lines, at `κL a oa`, a site the conjunct-4 route
already names (`src/L/SquareLawClosed.lagda.md:96-115`). **At every
site of that form the missing input is free.** The archive row that
recorded the old state is `archive/dev/LJ-dispatch-index.md:165`
(`[LJ-1.90]`, "Nothing in the tree proves any set is a cardinal"); it
was already superseded by `L.CardinalAbove`, and this task supersedes
it a second time at a different site.

## WHAT THE NEXT BRIEF NEEDS

1. **THE ABOVE-`ω` HALF IS NOT FINISHED, AND ITS WHOLE REMAINING DEBT
   IS NOW ONE TYPE: `IsCardinal (fst κ)` AT THE BILL'S SITE.**
   `least-site⟺amb` (`Probe640.agda:182-188`) says the least-site route
   and the ambient-cardinal route are the SAME route, so
   `[LJ-1.638]`'s item 2 ("price `c4-from-min`'s minimality hypothesis
   at the bill's site", `agents/tasks/LJ-1-638/lj-1.638-report.md`) is
   answered: the price is exactly this input, and no less.
2. **DO NOT FUND THE `κL` DETOUR.** `amb→min-inputs`
   (`Probe640.agda:141-147`) shows the same input supplies
   `c4-from-min`'s two open hypotheses DIRECTLY, at `X := ⟪ fst κ ⟫`
   with the identity injection. Routing through `κL κ oκ` buys nothing
   and costs the `∈sucV-elim` case split. The least-site question was
   worth asking and its answer is: the site IS one, and only under the
   input that already finishes the job without it.
3. **THE CHEAPEST OPEN QUESTION IS THE NARROWED ONE, AND I DID NOT
   PRICE IT.** `bill-site-is-least-pointwise` needs a code for ONE
   named injection, `κ-injL κ oκ`, not for an arbitrary family. Whether
   `LeastCardInjL`'s selection leaves a `Formula` reachable at that one
   witness is a question about `src/L/Cardinal.lagda.md:116-134` and
   its `opaque` seal at `src/L/SquareLawClosed.lagda.md:72-89`. D-10 says
   to price that TRUTH before dispatching its proof.
4. **THE FOUR UNPAID `cardκ` HYPOTHESES ARE THE SAME DEBT, AND THEY ARE
   OLDER.** See the C-42 section. If the campaign is going to pay
   ambient cardinality anywhere, it should be priced once against all
   five demands, not once against conjunct 4.
5. **A MATHEMATICIAN'S CALL THIS TASK DOES NOT MAKE.** At sites of the
   form `κL a oa` the whole difficulty vanishes: `kappaL-is-ambient-cardinal`
   gives ambient cardinality free, and `κ-min-atL` is already
   `c4-from-min`'s minimality at `X := ⟪ fst a ⟫`. Restating the
   above-`ω` half at those sites would close it. **Whether the trophy
   permits that restatement is a mathematical judgement and AD3 gives
   it to the mathematician, not to me.** The trophy is stated in `L`,
   so its sites are L-internal cardinals; I record the observation and
   the evidence, and I do not decide it.
6. **What was weakened: nothing. What is not closed: the crossing**, and
   the report says exactly which crossing and exactly how wide.

## PREMISES CHECKED

- **Premise 1 HOLDS.** `src/L/SquareLawClosed.lagda.md:96` is
  `clause4-at-kappa :` and its body (`:107-115`) spends `κ-min-atL`
  (`:86-89`) and the truncated `∥ sq β ∥₁` induction hypothesis, with
  no ambient `IsCardinal` and no `BandBelow`.
- **Premise 2 HOLDS.** `agents/tasks/LJ-1-638/Probe638.agda:212` is
  `c4-from-min :`, at an arbitrary site `α` and an arbitrary injected
  type `X`, all three hypotheses open.
- **Premise 3 HOLDS.** `src/L/SquareLawClosed.lagda.md:86` is
  `κ-min-atL : (a : S) (oa : IsOrd (fst a))`, inside the `opaque` block
  at `:72`, available only at `κL a oa`.
- **PREMISE 4 IS THE WHOLE FINDING AND IT HOLDS.**
  `src/L/CantorBernstein.lagda.md:33` is
  `readL : (a b : S) → Σ[ F ∈ S ] InjCode F a b`, and it runs CODED to
  AMBIENT only. `κ-min-atL` refutes an ambient injection;
  `IsCardinalL` refutes a coded one. **This report's whole answer is
  that premise, turned into two types and a one-way arrow between
  them** (`runs/W3.agda:53-100`).
- **PREMISE 5 HOLDS, AND I OBEYED THE WARNING.**
  `agents/tasks/LJ-1-533/lj-1.533-report.md:1` is
  "# LJ-1.533 report: B9, and the code an ambient injection does not
  carry". **I did not try to bridge an ambient injection back to a
  code.** `gap-is-the-crossing` NAMES that bridge as a hypothesis and
  never inhabits it, and `IntToAmb` is named and not inhabited. The
  crossing `[LJ-1.615]` was shelved on is untouched.
- **The brief's W3 estimate is ANSWERED AND WAS CLOSE**: 60 to 120
  lines estimated, 100 lines measured, 40 of them code.

## THE FLOOR, THE CAPS, THE RUN LEDGER

Caliber on every run: `GHCRTS=[-A64m -I0 -M2g]`, set by the program on
this pane. Cap: 300 s, set by me, recorded in every `.out`. **No run
reached the cap and NO HEAP WALL occurred**, so the owner's restructure
ruling of 2026-08-23 was not engaged.

**THE FLOOR WAS MEASURED BEFORE THE PROOF, per the owner's ruling of
2026-08-23.** `runs/floor-1.out` is the probe with all six statements
written and every body a hole: exit 42 with exactly six unsolved
interaction metas and NO type error on any statement, at 4.33 s and
732.9 MB. **Every statement of this task typechecked before a single
body was written.** The green obligation costs 4.25 s against that
4.33 s floor, so **the bodies cost nothing on top of the frame**: this
is not a heavy object, and what the price measures is the elaboration
frame. The imports were kept to the facts these rows actually use, per
the same ruling; `L.SquareLawClosed` is imported for `κL` and its four
projections and for nothing else.

| run | what | exit | wall | peak RSS |
|---|---|---|---|---|
| `runs/w3-1.out` | W3 ALONE, cold; builds five interfaces | 0 | 39.94 s | 1802.1 MB |
| `runs/w3-2.out` | W3 ALONE, warm | 0 | 3.83 s | 664.7 MB |
| `runs/floor-1.out` | **THE FLOOR**: six statements, six holed bodies | 42 | 4.33 s | 732.9 MB |
| `runs/final-1.out` | bodies filled; ONE unsolved meta, `↾-reflects` implicits | 42 | 4.37 s | 852.6 MB |
| `runs/final-2.out` | green after `{𝒮 = 𝒮ᵥ} {M = isL}` | 0 | 4.23 s | 898.9 MB |
| `runs/final-3.out` | green with section 6, `least-site⟺amb`, and the C-42 counts | 0 | 4.18 s | 963.9 MB |
| `runs/final-4.out` | recheck | 0 | 3.95 s | 963.9 MB |
| `runs/final-5.out` | recheck | 0 | 4.25 s | 963.9 MB |
| `runs/w3-3.out` | W3 ALONE again, postdating its last edit | 0 | 3.42 s | 664.7 MB |
| `runs/final-6.out` | **GREEN**, the last run, postdating the last edit of both files | 0 | 4.07 s | 963.9 MB |

`_build/2.8.0/agda/agents/tasks/LJ-1-640/Probe640.agdai` (and the W3
interface for the W3 runs) was deleted before every kept run, so each
measures that file's own elaboration against warm dependencies.
`sha256` of the files these runs describe:
`4b154134075bc5c2b0d34655abcee17bbab5cbf92d7e3593e1bc91d13f7da669`
(`Probe640.agda`),
`31254c6b941c35c576aa090573182647cd7f596eda54e4967b604722dd69acef`
(`runs/W3.agda`).

**Only one non-zero-exit run was not intended**, `final-1.out`, and its
cause is named above. No code was ever re-run unchanged.

**THE GATES, RUN INDIVIDUALLY AS THE BOUNDARY ASKS.**
`scripts/gate/lint-agda.py --check` exit 0.
`scripts/gate/check-probes.py --check` clean (9705 tracked files, no
probe outside `agents/tasks/` and no generated file).
`scripts/pod/witness.py --code LJ-1-640` exit 0, 0 UNRESOLVED of 1.
`grep` for `postulate`, `TERMINATING` and `{!` over both `.agda` files
returns nothing. No em dash in any file of this scope. **`make check`
not run: it is the commit gate and nothing here commits.**

**ONE DEPARTURE, DECLARED.** `AGENTS.md` says to run every `python3`
command as `.venv/bin/python`. **This worktree has no `.venv`.** I used
the main checkout's pinned interpreter,
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, with this worktree as
the working directory. I installed nothing and created no venv here.
`[LJ-1.533]` and `[LJ-1.446]` both recorded the same departure.

## RATIO BAR

**The bar cannot fire.** Both files this task writes are raw `.agda`,
so neither carries an ` ```agda ` fence and the in-fence line count of
the write scope is 0. The write scope carries no `.lagda.md` master.

## THE LAWS THE BRIEF BOUND ME TO

- **D-10** (price the truth of a recorded residue before pricing its
  proof). Applied before any Agda. The brief's target is a QUESTION
  and not a residue, so the D-10 move was to ask whether the answer
  could be YES unconditionally, and the five minutes spent found the
  shape of the NO: `IsCardinalL` refutes coded, `κ-min-atL` refutes
  ambient, `readL` runs one way. **The corrected target is recorded
  beside the original**, as D-10 requires: `LeastSite κ` is reachable,
  and the correction is the fourth hypothesis. Item 3 of "what the next
  brief needs" applies D-10 forward, asking for the TRUTH of the
  narrowed crossing before its proof is dispatched.
- **C-22** (write the deliverable incrementally). This report was a
  skeleton on disk before the first Agda run, and it was filled section
  by section as each answer landed.
- **P-l** (a statement may be ABOUT a concrete stage without dragging
  that stage's presentation into its type). Held throughout, and it is
  visible in the price. No type in either file names a transparent
  presentation: `fst κ` and `fst (κL a oa)` are atoms, `κL` is sealed
  `opaque` upstream (`src/L/SquareLawClosed.lagda.md:72-89`) and this task
  never unfolds it. **The whole proof of `least-at-self-pointwise` runs
  on the four sealed projections and never on `κL`'s body**, which is
  why the floor and the green run are the same number.
- **D-26** (a well-founded key on a tower needs generation data, or it
  needs syntax). NOT ENGAGED. No row of this task well-orders a stage
  or builds a key. The one well-order in sight, `LeastCardInjL.w`, is
  delivered and sealed, and this task consumes only its selection's
  four projections.
- **C-42** (a refutation measures the site it names, never how far that
  site extends). Answered in full in its own section, with the count
  before any cure: one producer of `IsCardinal` in `src/` at a
  self-built site, four unpaid demands at campaign sites, and one new
  producer this task adds.

## W2 AND W4

**W2 (from DD4).** Every row is written at a generic carrier and
instantiated, so both future proofs share the code. `AmbMinimalAt`,
`IntToAmb`, `LeastSite`, `least-site⟺amb` and `amb→min-inputs` are all
stated at an ARBITRARY site `κ`, never at a fixed ordinal.
`kappaL-is-ambient-cardinal` is stated at an ARBITRARY `a`, so it
serves every least-cardinal site at once. `gap-is-the-crossing`
consumes `[LJ-1.533]`'s generic crossing rather than a site instance.
**The module parameters `α₀` and `oα₀` are carried, not invented**:
`κL` sits inside a module parameterized by them
(`src/L/SquareLawClosed.lagda.md:19-20`) whose body never uses them, so
paying the parameter keeps every row of this file generic in it.
Nothing landed in `src/`, so no fixed-form chapter was written and no
deadline conflict arose.

**W4 (from DD13).** No module was retired by this return;
`dev/ARCHIVE.md` is untouched and nothing moved to `archive/`. **Priced
against the ideal form written fresh today**, the two files as they
stand ARE that form: an alone-typechecked W3 carrying the two
minimalities and the one-way arrow, and a probe carrying the
equivalence, the obligation and the sweep. I did not pay for a worse
shape first; the only rework was two implicit arguments. **The one
PLACEMENT defect this task met is in `src/` and not in its own files,
and it is the SAME defect `[LJ-1.638]` reported**: `L.SquareLawClosed`
is parameterized by `(α₀ , oα₀)` (`:19-20`) that `κL` and its four
projections never use, so every consumer of the least-cardinal site
pays an irrelevant parameter to reach it. `[LJ-1.638]` met it at
`inf-member`; this task meets it at `κL`. **Two independent sites now,
so the cure is worth the mathematician's minute**: the fix is to lift
the sealed `κL` block to a module without those parameters. That is a
placement call and not mine to make.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:166`: "| LJ-1.90-A | Orchestrator
  audit: IsCardinal is never inhabited | CONFIRMED | Two hits in src:
  the definition and the hypothesis. The probe's own kappa, sucV omega,
  is not a cardinal either |". **This is this task's own finding,
  measured in the LJ-1.90 series and archived.** It is why the C-42
  section counts producers rather than asserting scarcity, and it is
  the row this task supersedes at a new site.
  **`:167` ALSO READ AND USED**: "| LJ-1.91 | Gate the cardinal chapter
  | AMBIENT HARTOGS, 490 to 890 lines | IsCardinal is ambient, so the
  internal omega-1-L does not provably satisfy it. Order types are the
  widest term |". **The ambient-against-internal gap this task measures
  in Agda was recorded in prose in the LJ-1.91 gate**, and the
  "provably" in that row is exactly `IntToAmb`. **`:165` ALSO READ**:
  "| LJ-1.90 | Instantiate BoundedSubsetAt for the first time | REACHES
  cardκ | Every other hypothesis takes a value, including AllCodes A in
  Lset lam. Nothing in the tree proves any set is a cardinal |", the
  oldest member of the C-42 count and the row `L.CardinalAbove` and
  this task have each moved.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the retired
  route". It records the route the owner replaced. The bill's site is
  on the live route, and no claim of this report turns on a retired
  one. Not read past line 1.
- **`archive/dev/JOURNAL.md` DECLINED.** `archive/dev/JOURNAL.md:1`:
  "# ARCHIVED 2026-08-20". A retired per-episode journal, superseded by
  `agents/tasks/<CODE>/`. The predecessor evidence this task needed is
  in those task directories and in `src/`, and I read it there. Not
  read past line 1.
- **`dev/ARCHIVE.md` DECLINED.** `dev/ARCHIVE.md:1`: "# ARCHIVE.md: the
  archive registry". It is the registry of retired MODULES. This task
  retires none, so it has no row to give and gains none. W4 above says
  the same. Not read past line 1.
- **`archive/dev/ORCHESTRATION.md` DECLINED.**
  `archive/dev/ORCHESTRATION.md:1`: "# ORCHESTRATION: the
  orchestrator's operating rules". Archived with the cutover; the live
  rules that bind this slot are `dev/pod/instructions/coder.md`,
  `AGENTS.md` and the program. Reading it would be reading history,
  which the Boundary calls a defect. Not read past line 1.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ AND USED.**
  `dev/literature/devlin-II5.md:147`: "> 5.5 Lemma. Assume V = L. Let κ
  be a cardinal. If x is a bounded subset of". **This is why the
  textbook never pays the crossing this task priced.** Devlin works
  under `V = L`, where the ambient and the internal cardinal notions
  coincide, so "let κ be a cardinal" carries no ambient-against-internal
  distinction at all. The tree proves `L ⊨ GCH` from OUTSIDE `L`, so
  the two notions come apart and the crossing appears. It also explains
  the four unpaid `cardκ` hypotheses in the C-42 count: they are the
  Agda transcription of this line, and the line's hypothesis is the
  ambient one.
  **`:164` ALSO READ AND USED**: "The application of 5.5 in 5.6 is at
  the cardinal κ⁺ with α = κ: every". The chain applies 5.5 at a
  SUCCESSOR cardinal, a site the tree can build (`L.CardinalAbove`
  produces an ambient cardinal above any ordinal, `:205-217`), which is
  the evidence behind item 5 of "what the next brief needs": at BUILT
  sites the ambient predicate is free, and only at handed-in sites is
  it owed.
- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `dev/literature/truncation-and-selection.md:143`: "the reason: \"a
  proposition-valued goal absorbs the truncation\"". **This is the rule
  `amb-card→amb-minimal` (`runs/W3.agda:68-69`) spends**: `IsCardinal`
  takes an UNTRUNCATED injection, `κ-injL` delivers a TRUNCATED one,
  and the `Empty.⊥` goal is a proposition, so `PT.rec` crosses the
  grade with no selection. It is also why this task never needed to
  choose a witness, so no selection question arises anywhere in it.
- **`dev/literature/terms-2026-08.md` DECLINED.**
  `dev/literature/terms-2026-08.md:1`: "# The terminology dossier:
  fourteen renderings for the owner's ruling". Translation provenance
  for a glossary ruling. This task names no new term and adds no
  glossary entry; every name it uses is the tree's own. Not used.
- **`dev/literature/geology.md` DECLINED.**
  `dev/literature/geology.md:1`: "# Geology dossier: set-theoretic
  geology sources and the five questions". No layering, ground-model or
  inner-model question arose. The ambient-against-internal gap this
  task measures is a CODING gap inside one model, not a question about
  grounds. Not used.
- **`dev/literature/digest.md` DECLINED.** `dev/literature/digest.md:1`:
  "# Digest: the orthodox form of the rud route, pinned from the
  collected literature". It pins the rud route. No row of this task
  touches a rud term; the site's tower is the `Def` one. Not used.
