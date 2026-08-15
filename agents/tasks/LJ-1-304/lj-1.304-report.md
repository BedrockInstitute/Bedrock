# LJ-1.304 report: `StepAgree` and `ApproxAgree` priced at the ambient carrier

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**BOTH STEMS ARE BUILT, AND TOGETHER THEY COST ABOUT 190 LINES AT THE
AMBIENT CARRIER.**

`agents/tasks/LJ-1-304/ProbeLJ1304A.agda`, exit 0, 5.0 s of user time,
holds both modules as TERMS, not hypotheses:

- `StepAgree.step-agree`: the bounded step implies the machine step at
  the ambient class, at an arbitrary env, generic in the leaf content
  and the Def-step trio.
- `ApproxAgree.approx-agree`: the bounded approximation implies the
  machine one, at the same generality, with `DomainAgree.back`
  imported from `[LJ-1.302]` and `entryK` imported as a TERM from the
  same probe's `Supply`.

**The ONE number (DD8).** Both stems complete at the ambient carrier
cost about **190 non-blank non-comment lines**. Basis: **this build**.
The file measures 150 of them (`StepAgree` 77, `ApproxAgree` 40, the
site's new lines about 30, counted by region). Two named add-ons are
INFERRED, not built: the leaf-frame wrapper, about 25 lines, and the
`dK` closure lemma, about 15 lines. Sections 2 and 4 name both.
Seconds: 5.0 s user for the whole file's elaboration, flat over two
runs, dependencies cached. MEASURED.

**The abort criterion fired on its first branch, and it fired
BETTER than the brief allowed: both are priced and BOTH are built.**
`q'`'s four named costs are now all measured. One small term remains
outside the brief's table, the archived assembly's re-landing; section
9 names it for the orchestrator.

**One correction to the record (C-44), and it matters for the
reading.** `StepAgree` and `ApproxAgree` do NOT live in
`src/L/Condensation.lagda.md:2774-7319`. No module of either name
exists in `src/`. The only mention is the chapter's own comment at
`:5476`, which cites them as `[LJ-1.52]`'s. They are HYPOTHESES in the
archived probe `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:53-58`
and `:64-68`. What `src/` holds is the two SIDES they bridge: the
bounded matrices `StepB` (`:2389-2438`), `StepAtB` (`:2441-2462`) and
`ApproxB` (`:2464-2481`), and the machine rows `StepAt`
(`src/L/Coding/Sequence.lagda.md:119-120`) and `ApproxAt`
(`src/L/Coding/Sequence.lagda.md:286-287`). MEASURED, by grep and by
reading.

**The two named obligations are the right ones (C-44, verified).**
The bounded `∀̇`-closure is `ApproxB`'s second conjunct
`∀̇∈ (var K) (∀̇∈ (var (suc K)) (appAt ⇒̇ S.stepBndAt))` at
`:2471-2476`, against the machine's unbounded `∀̇ (∀̇ (appAt ⇒̇
Step ...))` at `:287-288`. The change of leaf is `StepB`'s `leafB`
(`:2403-2410`), the bounded restatement of `DefAt`'s body, against
`DefAt zero (suc zero)` inside `StepBody` at
`src/L/Coding/Sequence.lagda.md:113-118`. Both statements confirmed by
reading the four regions whole.

## 1. WHAT EACH MODULE NEEDS AT THE AMBIENT CARRIER

A reader who instantiates the two stems at the ambient class must
supply the following. Every obligation below is a PARAMETER of a green
module, so the list is exact and machine-checked.

**For `StepAgree` (`ProbeLJ1304A.agda:168-192`):**

1. **The leaf bridge, both directions** (`leafFwd`, `leafBwd`,
   `:177-183`): `leafB ↔ DefAt` at the four-extended env, quantified
   over the payload. This is the leaf-stem's OUTPUT at ambient. The
   stem exists at the class carrier: `extAtB→extAt` and
   `extAt→extAtB` take the leaf bridge as `fwd` and `bwd` parameters
   (`src/L/Condensation.lagda.md:2511-2529`), and `LeafAgree.out` and
   `LeafAgree.back` are that bridge (`:7231-7244`). So the brief's
   premise holds: the change of leaf is SERVED at the class carrier.
   At ambient it is the priced port, `[LJ-1.298]`'s about 180 lines
   plus `[LJ-1.302]`'s about 100.
2. **`wK`** (`:184-186`): recorded values of `f` land in `K`. This is
   the second half of `DomainAgree`'s `entryK` tie, which
   `[LJ-1.302]` measured at 20 lines and which my site imports as a
   TERM (`ProbeLJ1304A.agda:357-359`).
3. **`dK`** (`:187-189`): the definable powerset of a recorded value
   lands in `K`. **This tie is NEW.** It is not among the seven's
   telescope ties that `[LJ-1.302]` priced, and no delivered lemma
   states it. Section 4 gives its status.
4. **`zK`** (`:190-192`): members of a recorded `𝒟ₒ` land in `K`. This
   DERIVES from `dK` plus the stage's transitivity, in three lines
   (`ProbeLJ1304A.agda:361-364`). It is not a separate debt.

**For `ApproxAgree` (`ProbeLJ1304A.agda:273-297`):**

5. **Everything `StepAgree` needs, at the shifted env** (the leaf
   bridge restated at `:275-283`; `wK`, `dK`, `zK` at `:284-292`,
   which carry no binder dependence).
6. **`domAgree`** (`:293`): `domB f a K → domAt f a`, which is
   `DomainAgree.back`, delivered by import from `[LJ-1.302]`'s
   `GenDomainAgree` (`agents/tasks/LJ-1-302/GenDomainAgree.agda:97`).
7. **`entryK`** (`:294-297`): the appAt satisfiers land in `K`. This
   is LITERALLY `[LJ-1.302]`'s measured tie, imported as a TERM
   (`ProbeLJ1304A.agda:341`, the `S302` application).

**What is FREE at the ambient carrier.** `PowOK` and `DefOK`, the
constructibility side conditions that the class-carrier readings carry,
discharge by `tt*` at `Full` (`ProbeLJ1304A.agda:199-203`). The
reading transport is `[LJ-1.297]`'s measured `absFull`, two lines a
direction (`:93-101`). The bounded matrices themselves are verbatim
copies, 33 lines, at `[LJ-1.298]`'s measured zero-change rate.

## 2. THE ONE BUILT, WITH LINES AND SECONDS

**Both are built. One file, exit 0.**

`agents/tasks/LJ-1-304/ProbeLJ1304A.agda`, 268 non-blank
non-comment lines, decomposed by region:

| region | lines | content |
|---|---:|---|
| setup and transports | 43 | the `[LJ-1.297]`/`[LJ-1.302]` scaffold, cribbed |
| the matrices | 33 | `extAtB`, `leafB`, `bodyB`, `witB`, `stepBndAt`, `approxBndAt`, verbatim copies |
| `StepAgree` | 77 | the stem, including its 20-line obligation telescope |
| `ApproxAgree` | 40 | the stem, including its obligation telescope |
| `Site` | 53 | the concrete supply, of which about 30 are new; the rest re-uses `[LJ-1.302]` by import |

The wrapper's own content, what this probe adds to the route beyond
the priced port and ties, is the middle three rows' bodies: about 150
lines. `StepAgree`'s `into` re-spells `GenSequence`'s `readBody`
(`agents/tasks/LJ-1-238/GenSequence.agda:90-103`) with the bounded
payload; `fill` re-spells its `fill` (`:122-135`); `closure` performs
the `∀̇`-closure in eight lines (`ProbeLJ1304A.agda:298-312`). No
line of the three is new mathematics: each is a delivered pattern with
the K-bounds and the leaf bridge spliced in.

| run | user s | wall s | what it measures |
|---|---:|---:|---|
| 1 | 5.02 | 6.13 | elaboration, dependencies cached |
| 2 | 5.00 | 6.00 | elaboration, own interface moved aside |
| 3 | 2.26 | 3.35 | interface reload |

The pair is flat, 2 percent over the mean. Load 3.75 to 4.31, three
users, throughout. One Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap
never raised. No heap exhaustion. No run near 30 minutes.

Eight failed runs preceded the green one, all in scaffolding: a parse
error in nested truncations; `ℓ` used before the module header; `+`
not in scope; `∥_∥₁` not in scope; `four` referenced inside its own
module's telescope; `𝒮ᵥ` applied to a level argument; `StepOf`'s
binders mistaken for truncated ones; and `appAt-adequate`'s direction
needing `sym`. None touched the stems' content.

## 3. THE ONE NUMBER (DD8), WITH ITS BASIS

**About 190 non-blank non-comment lines, both stems complete at the
ambient carrier. Basis: this build, with two named INFERRED add-ons.**

- 150 MEASURED in `ProbeLJ1304A.agda`: `StepAgree` 77,
  `ApproxAgree` 40, the site's new supply about 30.
- About 25 INFERRED: the leaf-frame wrapper. My `leafFwd` and
  `leafBwd` stand for `leafB ↔ DefAt`. Producing them from the ported
  `LeafAgree.out/back` and the two delivered `extAt` transfers needs
  one more wrapper of exactly the shape this probe measured twice, at
  the leaf's arity. Same surgery, one level down.
- About 15 INFERRED: the `dK` lemma, section 4.

Seconds at the measured rate: the whole file elaborates in 5.0 s with
dependencies cached; the stems' share of it is about 3 s, INFERRED by
region, and the leaf wrapper would add the same order.

**The route, re-priced.** Port the family generic, about 180
(`[LJ-1.298]`). Supply the seven's ties, about 100 (`[LJ-1.302]`).
Build the two stems, about 190 (this probe). Move readings by
`absFull`, 2 lines a direction (`[LJ-1.297]`). The four costs the
brief's table names are now all measured. Section 9 names the one term
the table omitted.

## 4. MATHEMATICS OR SITE FACT

**Neither stem is free-standing mathematics. Each is one wrapper of
plumbing around obligations that are either delivered, priced, or one
new tie.** The brief's second abort branch fires in this precise
sense, and it makes the route CHEAPER than `[LJ-1.302]` feared, not
dearer.

**The bounded `∀̇`-closure is NOT mathematics.** `closure`
(`ProbeLJ1304A.agda:298-312`) performs it in eight lines: `entryK`
lands the arbitrary satisfiers in `K`, the bounded implication fires
inside `K`, `StepAgree` lifts the result. The closure's entire content
is the satisfiers-in-`K` tie, which is `DomainAgree`'s `entryK`, which
`[LJ-1.302]` already measured and which this probe IMPORTS rather than
rewrites. The unbounded step adds no proof obligation of its own.
MEASURED, by building.

**The change of leaf is SERVED, as the brief suspected.** At the class
carrier the stem is delivered end to end: `LeafAgree.out/back` at
`src/L/Condensation.lagda.md:7231-7244` is the bridge, and the two
`extAt` transfers at `:2511-2529` consume it. At ambient it is the
priced port. My `leafFwd`/`leafBwd` hypotheses are that port's output
shape, and the wrappers around them are the measured 150 lines. The
witnesses survive the leaf change by the same in-`K` pattern as
everything else: `into` drops the leaf's bounds, `fill` rebuilds them
from `wK`, `dK` and the bridge.

**The one NEW tie is `dK`.** `𝒟ₒ` of a recorded value lands in `K`. It
is not among the seven's telescopes. No delivered lemma states it: I
searched `src/L/Hierarchy.lagda.md` and `src/L/Constructible.lagda.md`
for a `𝒟ₒ`-into-stage closure; the nearest are `Lset⊆𝒟ₒ`
(`src/L/Constructible.lagda.md:310`), which goes the other way, and
`Lset-in` (`:319`), which lands MEMBERS of `𝒟ₒ (Lset δ)`, not `𝒟ₒ`
itself, and only for stage arguments. MEASURED, by the search. The tie
is TRUE at a limit bound above the record stages, by the tower's
construction (`LsetStep`, `:216`, builds each stage from the `𝒟ₒ` of
the ones below), and I expect it provable from the `Lset-compute`
seal in about 15 lines. INFERRED, both the truth and the price. It is
the one place this probe found where the stems need a lemma nobody has
priced, and it is small.

## 5. DOES THE PORT INTRODUCE THE OBLIGATION

Section 8 answers with the literature. The summary: Devlin writes ONE
coding of level-hood and moves its satisfaction between carriers. The
bounded `∀̇`-closure exists because Bedrock writes TWO codings, the
BoundedSubset certificate for `φ₀` and the sequence graph for the
read-off, and the stems are the price of the pair. The obligation is
PORT-INTRODUCED, as `[LJ-1.302]` section 8 argued. This probe adds the
measurement: the introduced obligation costs eight lines and one
imported tie, not a chapter.

## 6. DD4, WITH THE AXIS NAMED

**My axis: the port's L-against-ambient axis, the same axis
`[LJ-1.302]` named. The carrier is the subject here, not a label.**

**These two modules pay the generic way, and they pay it MORE plainly
than the thirty did.** The thirty proved one notion's agreement at two
codings, once per row. The two stems are the rows' COMPOSITION LAW:
`StepAgree` is the step-frame transfer parameterized over the leaf
bridge, and `ApproxAgree` is the closure parameterized over
`StepAgree`. Each is written once, generic in the class, the leaf
content and the Def-step trio, and each serves the L tower's proof and
the ambient proof from the same 150 lines. MEASURED, by the module
telescopes: the class enters nowhere but the eight `GenModel`
parameters, exactly as `[LJ-1.297]` section 5.2 measured for the
chapter.

**The DD4 share grows twice.** First end, the two proofs: the wrappers
above are carrier-neutral and both carriers spend them; the leaf-frame
wrapper, once written generic, is the same object at both carriers.
Second end, AC against GCH: nothing here touches it, and I say so
rather than stretch the axis. INFERRED, that the second end gains
nothing.

**The exception `[LJ-1.52]` feared is not here.** That probe called the
two stems "the unbuilt content" of the composite. Built, they are the
cheapest modules on the route per line of route served, because
everything heavy under them was already shared. The generic port pays
the same way a fourth time.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `StepAgree`/`ApproxAgree` live in `src/L/Condensation.lagda.md:2774-7319` | **MEASURED FALSE.** The brief's premise; archived hypotheses, section 0 |
| the two named obligations are the wrong reading of the modules | **MEASURED FALSE.** Section 0's last paragraph |
| the bounded `∀̇`-closure needs mathematics beyond the tie family | **MEASURED FALSE.** Eight lines plus the imported `entryK`, section 4 |
| the change of leaf needs a new stem at the class carrier | **MEASURED FALSE.** `LeafAgree` plus the `extAt` transfers, section 4 |
| `dK` is delivered somewhere | **MEASURED FALSE.** The search of the tower chapters, section 4 |
| `dK` is true at the intended site | **INFERRED.** Limit-bound closure, tower construction |
| the leaf-frame wrapper costs about 25 lines | **INFERRED.** The same measured shape at another arity |
| the stems are vacuous (their obligations unsatisfiable) | **INFERRED FALSE.** Every obligation except `dK` is delivered or measured at a concrete site; `dK` is true at a limit bound |
| the ambient seconds transfer to a loaded machine | **INFERRED.** Load 3.75 to 4.31, 3 users, during my runs |
| the archived assembly still typechecks today | **UNKNOWN**, as `[LJ-1.302]` left it. Frozen files, not re-run |

## 8. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-100`.

**Where the bounded-to-unbounded obligation comes from: NOT the
mathematics.** The quote at `:93-97` is Devlin's 2.7: one Σ₀ formula
Φ(z, v, γ) and its ℒ-analogue φ, bridged by 1.9.15, with clause (b)
reading satisfaction INSIDE one coding at one carrier. Devlin never
writes two codings of one notion, so he never needs a stem that makes
two codings agree. The obligation exists because the port carries
BoundedSubset's `levelHoodB` on `φ₀`'s side and the sequence graph on
`q'`'s side, and `[LJ-1.297]` measured that the READING gap between
carriers closes for free while the CODING gap does not. The stems are
the coding gap's price. Confirmed by construction: my `closure` closes
the unbounded side from the bounded one with no mathematical input
beyond the in-`K` tie.

WHY NOT the other rows: C1 is the level-hood formula, per tower, the
subject matter. C3 is Σ₀ absoluteness, delivered, and spent by
`absFull`. C2's coding analogue is the `Agree` family itself. C4 is
downstream of `amb`. The rest are bookkeeping, counting, cardinals,
collapse. None prices a two-coding equation at the step level.

## 9. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-302/lj-1.302-report.md`, read WHOLE, FIRST, as the
  brief orders. **Line read:** section 4's last paragraph, "the
  bounded `∀̇`-closure of the approximation must become the unbounded
  one ... Nobody has priced those." TOOK the task, the four-cost table,
  and the leaf-stem citation; CORRECTED nothing there, and CONFIRMED
  its section 7 row that the stems exist nowhere as terms.
- `agents/tasks/LJ-1-298/lj-1.298-report.md`, read sections 0 to 2.
  **Line read:** section 0, "Zero of the 33 lines changed." TOOK the
  port rate my matrices' verbatim copies extend.
- `agents/tasks/LJ-1-297/lj-1.297-report.md`, read sections 0 to 5.
  **Line read:** section 5.1, "the six readings SUPPLY at the ambient
  carrier ... 22.81 s." TOOK the supply shape, the `absFull` transport,
  and probe D's scaffold, which my file cribs.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`, read WHOLE.
  **Line read:** `:53-58`, `StepAgree` as a hypothesis at the graph
  env. TOOK the obligation's exact shape, which my module's telescope
  generalizes, and the site-fact bundle pattern my parameters refine.
- `archive/dev/TASKS-archived.md`, grepped. **Line read:** `:68`, the
  `L3.32-T33` row, "Condensation crossing | DELIVERED". TOOK SHAPE
  only: a crossing was delivered once, under the retired route; no
  figure and no content transfers.

## 10. WHAT I DID NOT SETTLE

- **The `dK` lemma's proof.** Its truth is INFERRED, its price
  estimated at 15 lines. It is the one new obligation this probe
  found, and the build should discharge it first.
- **The leaf-frame wrapper.** INFERRED at about 25 lines. My
  `leafFwd`/`leafBwd` hypotheses absorb it; the funded build must
  produce them from the ported `LeafAgree`.
- **The archived assembly's re-landing.** `[LJ-1.52]`'s
  `graph-assembly` (17 archived lines) and `matrix-decode` would need
  porting to today's tree. The brief's table did not count it;
  `[LJ-1.302]` section 5 did. At this probe's measured wrapper rate it
  is about 40 lines, INFERRED. It is the last unpriced term on `q'`'s
  route, and the orchestrator should price it before funding
  `[LJ-1.7]` as a build.
- **Whether `q'` is TRUE.** Neither confirmed nor refuted, as
  `[LJ-1.297]`, `[LJ-1.298]` and `[LJ-1.302]` left it. This probe
  prices the bridge, not the crossing.

## 11. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap
NEVER raised. No heap exhaustion. No invocation near 30 minutes. Load
3.75 / 4.31 / 4.80 at the first run, 3.75 / 4.29 / 4.79 at the second,
3 users throughout. All dependencies' interfaces were cached, so the
seconds price my file's own elaboration.

| file | exit | elaboration | reload |
|---|---:|---:|---:|
| `ProbeLJ1304A.agda` | 0 | 5.02 s, 5.00 s | 2.26 s |

## 12. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-304/`: this report and
`ProbeLJ1304A.agda`. `src/` holds no probe of mine;
`src/L/Condensation.lagda.md` was read and copied from, never opened
for writing. `agents/tasks/LJ-1-301/` was not touched.
`src/Everything.lagda.md`, `dev/ledger.toml`, `dev/PLAN.md` and
`src/L/Choice/Name.lagda.md` were not touched. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py` and
`scripts/gate/lint-agda.py` were run on my files; both exit 0. No em
dash in any language. `_build/` holds only Agda's own interface file
for my module.
