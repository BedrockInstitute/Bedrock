# LJ-1.162 report: leg 3, the last unknown in `CrossOut`

tier: opus (version `override`). **No master was changed. One probe was written
and it runs GREEN, exit 0, in 14.5 s. No commit, no push.** Every negative is
marked **MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. THE TWO CRITERIA, BOTH FIXED BEFORE THE RUN (D-1)

### 0.1 The line criterion, which is the brief's and which I did not move

**GO at or below 60 in-fence lines for LEG 3 ALONE.** Leg 3 is: from the
transferred AMBIENT reading of the BOUNDED graph, derive `v ≡ Lset b`.

### 0.2 The wall-clock criterion, written before I ran anything

**20 minutes of wall time per agda invocation**, under `GHCRTS="-A64m -I0 -M8g"`
and ONE agda process. Past 20 minutes I record a **WALL** with its clock and its
resident set, comment the walling block out, and keep the other blocks green.
**I never raise the cap and I never move the line criterion on a wall.**

`[LJ-1.161]` measured this exact wall at this exact family of formulas and used
20 minutes. `AGENTS.md` records a cold whole-tree typecheck at about twelve
minutes, so a single declaration that outruns the whole tree has already
answered. **The criterion never fired. Section 5.**

## 1. VERDICT

### 1.1 NO-GO, and the reason is PRICE, not possibility

**NO-GO. Leg 3 is 125 in-fence lines against the 60-line criterion.**

**The bounded graph DOES carry the identification. MEASURED: the whole leg
typechecks, exit 0, 14.5 s, no unsolved meta, no hole, no postulate.**
`agents/tasks/LJ-1-162/ProbeLJ1162A.agda`.

**So the brief's first NO-GO branch is MEASURED FALSE.** `Lset-only`'s content
does NOT need the unbounded form. Leg 3 does not need its own Levy witness.

**And the brief's third branch is MEASURED FALSE too. The two graphs AGREE in
the direction leg 3 needs.** The bounded graph implies the unbounded one at the
inner reading, given the site facts named in section 4.

**What is true is neither branch: the agreement is real, it is two-directional,
and it costs a shade over twice the criterion.**

### 1.2 The one sentence a reader must carry

**`extAt` is an EXTENSIONALITY, not an implication.** It says "the set at `y` is
EXACTLY the satisfiers of `φ`". So the delivered
`extAtB→extAt` (`src/L/Condensation.lagda.md:2511-2519`) consumes **`fwd` AND
`bwd` AND a membership fact**, and a bounded-to-unbounded move on such a frame
can never be one-directional. **Leg 3 crosses TWO nested `extAt` frames, so it
pays four directions, not two.**

## 2. THE ONE LEG: line count, and what I excluded

### 2.1 The leg, module by module

| module | total | telescope | proof | what it is |
|---|---:|---:|---:|---|
| `Leaf` | 37 | 13 | 24 | `StepB.leafB` against the delivered `DefAt`, BOTH ways |
| `Step` | 48 | 13 | 35 | `StepB.stepBndAt` against the delivered `StepAt`, BOTH ways |
| `Approx` | 14 | 10 | 4 | `ApproxB.approxBndAt` against `ApproxAt` |
| `Graph` | 15 | 10 | 5 | `GraphB.graphBndAt` against `LsetGraphAt` |
| `Leg3` | 11 | 6 | 5 | ambient to inner by `abs₀`, then `Lset-only` |
| **LEG 3** | **125** | **52** | **73** | |

**Telescope means module hypotheses. They are lines of the leg and I count them.**
Section 4 says which of them the tree already discharges and which it does not.

### 2.2 What I excluded, said plainly

**Excluded**: the OPTIONS header, every import, the module header, the two module
aliases (`AbsL`, `CS`-style opens), every comment, every blank line, and three
blocks that are not the leg:

| excluded block | lines | why |
|---|---:|---|
| BLOCK 0, the generic quantifier kit (`∃∈-up`, `∃-down`) | 9 | reusable by ANY bounded restatement; I report it beside the leg, not inside it |
| BLOCK 2, `StepWired` | 27 | C-38 plumbing: it wires `Leaf` into `Step`. No new mathematics |
| BLOCK 2, `LeafAtDefBody` | 16 | C-38: the leaf frame at the REAL `DefBodyB` leaf |

**The second figure, for anyone who wants the leg plus its kit: 134.**
**The third figure, everything I wrote: 168.**

### 2.3 The file totals, separately, as the brief demands

**209 non-blank non-comment lines; 263 non-blank lines; 297 lines.**
**`[LJ-1.124]` was marked MEASURED FALSE for reporting a file total as a leg
total. The leg is 125. The file is 209.**

## 3. `CrossOut`'s FULL PRICE

| leg | figure | basis |
|---|---:|---|
| 1. inner to ambient | 20 | `[LJ-1.161]` block 1, exit 0 |
| 2. the moved formula means the delivered one | 18 | `[LJ-1.161]` block 2, exit 0 |
| **3. ambient implies `v ≡ Lset b`** | **125** | **this probe, exit 0** |
| **`CrossOut`, three legs** | **163** | |

**THREE THINGS THIS 163 DOES NOT COVER, and nobody should bank it without them.**

1. **The site facts are hypotheses in all three legs.** My 52 telescope lines
   state them; they do not discharge them. Section 4.
2. **`LeafAgree`'s own telescope is about seventeen hypotheses**
   (`src/L/Condensation.lagda.md:7013-7092`), and my `Leaf` consumes its two
   directions. That telescope is delivered but unpriced here.
3. **`[LJ-1.161]`'s WALL still stands.** Feeding the level-hood certificate to
   the transfer walls at 20 minutes. **My leg did not meet that wall because it
   never computes `countFo`;** it consumes `Δ₀-graphBndAt`, which is delivered.

## 4. DID THE BOUNDED GRAPH CARRY THE IDENTIFICATION?

### 4.1 YES, MEASURED, and here is the chain

```
ambient ⊨ᵛ graphBndAt
  --abs₀ (Δ₀-graphBndAt), a PATH, so it runs downward for free--> inner ⊨ graphBndAt
  --Graph.up--> inner ⊨ LsetGraphAt
  --Lset-only (src/L/Hierarchy.lagda.md:334)--> v ≡ Lset b
```

**The `Δ₀` certificate is what makes the first arrow free.** `abs₀`
(`src/FOL/Absoluteness.lagda.md:122`) is a path, not an implication, so a `Δ₀`
formula travels DOWN into `L` as cheaply as it travels up. **That is the whole
value of the brief's repair and it is 2 of my 125 lines.**

### 4.2 The four frames, and the two that cost

| frame | cost | why |
|---|---:|---|
| `∃̇∈ K` to `∃̇` at the graph | 5 | free: drop the bound |
| `∀̇∈ K` to `∀̇` at the approximation | 4 | one site fact places the pair in `K` |
| **`extAtB` to `extAt` at the STEP** | **35** | **two directions plus a membership fact** |
| **`extAtB` to `extAt` at the LEAF** | **24** | **two directions plus a membership fact** |

**MEASURED: 59 of the 73 proof lines are the two `extAt` frames.** The
quantifier layers are nearly free; the extensionality frames are the price.

### 4.3 THE OBLIGATION NOTHING IN `src/` SUPPLIES, and it is new

**The bounded step's THIRD existential binds the DEFINABLE POWER of the recorded
value, and bounds it by `K`.** `src/L/Condensation.lagda.md:2407-2412`:

```agda
  witB =
    ∃̇∈ (var (suc b))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          bodyB))
```

Read against `StepBody` (`src/L/Coding/Sequence.lagda.md:113-120`): the first
existential is the argument `c` and it is bounded by `b`, which the body states
anyway; the second is the recorded value `w`, bounded by `K`; **the third is
`d = 𝒟ₒ w`, bounded by `K`.**

**So the `bwd` direction of the step frame needs `𝒟ₒ w ∈ K`.** My probe names it
`powK` (`agents/tasks/LJ-1-162/ProbeLJ1162A.agda:140-141`), and consumes it at
`:183`.

**MEASURED, by `grep` over `src/`: `𝒟ₒ` does not occur in
`src/L/Condensation.lagda.md`, in `src/L/Condensation/LowerAgree.lagda.md`,
`UpperAgree.lagda.md` or `TwelveAgree.lagda.md`, and the `KFacts` record
(`src/L/Condensation.lagda.md`, `module KFactsNS` at `:5995`) has no field that
bounds a definable power.** Its closure fields are `innerK`, `innerPairK`,
`pairK`, `carrierK` and `arityK`: pairing and numerals, never `𝒟ₒ`.

**INFERRED, and I mark it: `powK` is satisfiable at the intended site**, because
`𝒟ₒ (Lset δ) ≡ Lset (sucV δ)` is a level and the bound is meant to hold the level
sequence. **I did not measure it. C-36 binds: I claim I did not find a supplier,
not that none exists.**

### 4.4 What the tree DOES supply, and I consumed it

| obligation | supplier | at |
|---|---|---|
| `domB` to `domAt`, both ways | `DomainAgree.back` | `src/L/Condensation.lagda.md:6441` |
| the twelve-row leaf, both ways | `LeafAgree.out`, `LeafAgree.back` | `:7133-7145` |
| the extensionality frames | `extAtB→extAt`, `extAt→extAtB` | `:2511`, `:2521` |
| the graph is `Δ₀` | `GraphB.Δ₀-graphBndAt` | `:2492-2494` |
| ambient to inner | `AbsL.abs₀` | `src/FOL/Absoluteness.lagda.md:122` |
| the identification | `Lset-only` | `src/L/Hierarchy.lagda.md:334` |

## 5. WALLS

**NONE. The wall-clock criterion never fired.**

| figure | value |
|---|---|
| clean run, interface deleted first | **14.5 s, exit 0** |
| processes | **ONE**. `GHCRTS="-A64m -I0 -M8g"`, cap never raised |
| machine | one user, load averages 3.06, 3.08, 3.18 at 2026-08-14 01:29 |
| heap | no exhaustion, no SIGTERM |

**Why this leg did not meet `[LJ-1.161]`'s wall, MEASURED.** Its block 3 walled
proving `countFo LH.levelHoodΣ₁ ≡ 0` by `refl`, which forces `countFo` over a
graph nesting the twelve-row table twice. **My leg never computes `countFo`. It
consumes the delivered `Δ₀-graphBndAt`, which is a proof term, not a
computation.** So the two costs are independent and neither hides the other.

## 6. DD4

**Maximize the code the two proofs share, and write it generic.**

### 6.1 The answer in one line

**103 of the 134 gated-plus-kit lines are TEMPLATE. 31 name a tower.**

| part | lines | class | why |
|---|---:|---|---|
| BLOCK 0, `∃∈-up` and `∃-down` | 9 | **TEMPLATE** | generic in `n`, `K`, `φB`, `φ`, `γ`. Zero tower tokens |
| `Leaf` | 27 of 37 | **TEMPLATE in shape** | the frame is generic; `DefBody` and `DefAt` are the Def tower's leaf |
| `Step` | 37 of 48 | **TEMPLATE in shape** | `StepB` is already parametric in `ψ`; `StepAt` and `StepBody` are the `RecShape` instance |
| `Approx`, `Graph`, `Leg3` | 30 of 40 | **TEMPLATE in shape** | the frames are generic; `ApproxAt`, `LsetGraphAt`, `Lset-only` name the Lset instance |

### 6.2 Which lines name the Def tower, exactly

**The 31 tower-naming lines split in two.** `DefBody` and `DefAt` are Def-tower
content and appear in `Leaf` only, 10 lines. **The other 21 name the `RecShape`
INSTANCE, not the tower**: `StepAt`, `StepBody`, `ApproxAt`, `LsetGraphAt`,
`Lset-only`. `RecShape` is already parametric in `Step`
(`src/L/Coding/Sequence.lagda.md:281`), so a J tower that instantiates
`RecShape` at its own step reuses `Step`, `Approx`, `Graph` and `Leg3` by
re-instantiation, not by rewriting.

### 6.3 The generic form was NOT within two lines this time, and I say so

**`[LJ-1.151]`, `[LJ-1.160]` and `[LJ-1.161]` each found the generic form within
two lines of the fixed one. This site is different and the difference is
honest.** Making `Leaf` generic in the leaf pair would abstract `DefBody` and
`DefAt` into two parameters and cost about 4 lines of telescope, against 10
tower-naming lines saved. **I did not write that version, so I give it no
number beyond that telescope count, which I did read off the module header.**
**C-40: this is a hypothesis, not a price.**

**No stop-line pushed me toward writing fixed.** BLOCK 0 was generic from the
first draft and it is used five times in the leg.

## 7. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| leg 3 fits in 60 lines | **MEASURED FALSE. 125 lines** |
| the bounded graph cannot carry the identification | **MEASURED FALSE.** The whole chain typechecks, exit 0 |
| `Lset-only` genuinely needs the unbounded graph | **MEASURED FALSE.** `Graph.up` feeds it the unbounded reading from the bounded one |
| the bounded and unbounded graphs do not agree | **MEASURED FALSE** in the direction leg 3 needs, under the site facts of section 4 |
| leg 3 needs its own Levy witness | **MEASURED FALSE.** `Δ₀-graphBndAt` is delivered and `abs₀` is a path |
| the ambient-to-inner step costs | **MEASURED FALSE. 2 lines**, because `abs₀` is a path |
| a bounded-to-unbounded move on `extAt` is one-directional | **MEASURED FALSE.** `extAtB→extAt` takes `fwd`, `bwd` AND `inK` |
| the tree supplies the definable-power bound `𝒟ₒ w ∈ K` | **MEASURED FALSE.** `𝒟ₒ` occurs in no site-fact bundle under `src/L/Condensation` |
| `powK` is unsatisfiable | **NOT CLAIMED. C-36.** I did not measure it. Section 4.3 marks the reason INFERRED |
| `DomainAgree` supplies the domain conjunct | **MEASURED TRUE.** `:6441`, consumed as `dom-back` |
| `LeafAgree` supplies the leaf, both ways | **MEASURED TRUE.** `:7133-7145`; `LeafAtDefBody` shows `Leaf` accepts the real `DefBodyB` leaf at the same arity |
| this leg meets `[LJ-1.161]`'s 20-minute wall | **MEASURED FALSE. 14.5 s.** The wall is on `countFo`, which this leg never computes |
| the 163-line `CrossOut` figure is complete | **MEASURED FALSE.** Section 3 names three things it excludes |
| `GraphB.graphBndAt` had a consumer before this probe | **MEASURED TRUE**, one: `LevelHood.levelHoodB`, `src/L/BoundedSubset.lagda.md:111`. This probe is the second |
| the site facts are discharged | **NOT CLAIMED.** They are 52 telescope lines. C-40 |
| a cheaper leg 3 exists | **NOT CLAIMED. C-36.** I measured one route and priced it |

## 8. GATES, CHECKERS AND PROHIBITIONS

### 8.1 The runs

| run | probe state | result | wall |
|---:|---|---|---:|
| 1 | BLOCK 0 only | exit 0 | 2.5 s |
| 2 | + `Leaf`, formulas as metas | exit 42, unsolved constraints | seconds |
| 3 | `Leaf` with `ΨB`, `Ψ`, `ΦB`, `Φ` and `K₅`, `K₆` named | **exit 0** | 3 s |
| 4 | + `Step` | **exit 0**, first attempt | seconds |
| 5 | + `Approx`, `Graph`, `Leg3` | **exit 0**, first attempt | seconds |
| 6 | + `StepWired`, `LeafAtDefBody` | **exit 0**, first attempt | seconds |
| 7 | whole file, interface deleted first | **exit 0** | **14.5 s** |

**Run 7 is the standing result.**

**Run 2's failure is worth one line for the next agent.** `⊨` is not injective,
so the formula arguments of a generic quantifier lemma cannot be metas. Naming
the four formulas and the two `Fin` indices fixes it, and that is 8 of `Leaf`'s
37 lines.

### 8.2 Checkers

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` on the probe | **exit 0** |
| `scripts/check-probes.py --check` | **clean, 1,766 tracked files** |
| `scripts/lint-prose.py --check` on this report | see section 8.4 |
| `scripts/ledger.py --brief` | standing **28,940 lines over 85 masters**, from HEAD; thresholds SUSPENDED per the ledger header |
| `make check` | **NOT RUN.** The orchestrator runs it |

### 8.3 Prohibitions, answered

**No master was edited.** `src/Everything.lagda.md` was never opened. The three
`*Agree` masters were read at their `README.md` only and never edited. **No
commit, no push, no `git checkout`, `stash`, `reset` or `clean`. No
`make check`.** My only files are `agents/tasks/LJ-1-162/lj-1.162-report.md` and
`agents/tasks/LJ-1-162/ProbeLJ1162A.agda`. **The probe is tracked, it sits beside
the report, and it ran while my task was live.**

### 8.4 The rules, answered

- **D-1.** Both criteria are in section 0, written before any run. The line
  criterion is the brief's and I did not move it after seeing 125.
- **C-38 as extended.** Section 4.4 lists six delivered items and every one is
  CONSUMED. `StepWired` wires `Leaf` into `Step`, so neither is an interface
  waiting for a supplier. `LeafAtDefBody` puts `Leaf` at the REAL `DefBodyB`
  leaf that `StepAtB` fixes (`src/L/Condensation.lagda.md:2441-2454`), and it
  typechecks, so the arity match is machine-checked rather than asserted.
  **I added no definition without a consumer.**
- **P-i.** No hang, so no surgery. Nothing to select from the decision tree.
- **P-l.** My comparable is LIVE and in the same tree: `DomainAgree` at `:6422`
  is 30 code lines for ONE conjunct of the approximation, and `LeafAgree` at
  `:7013` is the leaf. **The archive's `InitialSegment` is 114 in-fence lines on
  the RUD tower and I refuse it as the anchor.**
- **DD8.** One best-effort figure per term with its basis. Leg 3: 125, basis the
  probe. `CrossOut`: 163, basis three probes. The site telescope: 52 lines
  stated, NOT discharged, and I give it no discharge figure.
- **C-36.** Sections 4.3 and 7's `NOT CLAIMED` rows. I do not claim `powK` is
  unsatisfiable and I do not claim no cheaper leg exists.
- **C-40.** I re-price nothing. Section 6.3 refuses to put a number on the
  generic variant I did not write.
- **C-12.** One agda process, `-M8g`, cap never raised, load beside the seconds.
- **C-22.** This file was a skeleton with both criteria before I opened
  `L.Condensation`.
- **C-31 to C-34, C-37.** Section 4.3 names the one unsupplied obligation with
  its `file:line` and leaves no cure named and unpriced.
- **D-10.** The residue I priced is `[LJ-1.161]`'s leg 3. **Its TRUTH held: the
  bounded graph does carry the identification.** What moved is the price.
- **D-26, D-29, D-30.** Section 3 reports the reduction and refuses to bank it.
- **I-5.** No unsolved meta, no hole, no postulate in the standing probe.
- **DD23.** No mathematical prose was written. The probe carries comments only.
- **DD13.** Section 4.2 prices the ideal form first, frame by frame, before the
  total.
- **DD4.** Section 6. **C-39.** Section 10.

## 9. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`**, read
  `:150-260`. **TOOK the crossing face and `module Assembly`.**
  - **`CrossOut` at `:168-170`**, `HasLevels` at `:173-175`, `Covered` at
    `:177-180`, `Assembly` at `:208`, `succ-step` at `:210-226`, `level-in` at
    `:240-247`, `M⊆L` at `:249-257`.
  - **The brief asks whether the archive holds leg 3. MEASURED: it does NOT.**
    `module Assembly (φ : Formula Sᴹ 2) (co : CrossOut φ)` at `:208` takes the
    crossing as a MODULE HYPOTHESIS and never discharges it. **`grep` over the
    whole `archive/` tree finds `CrossOut` at nine places, all of them the
    statement or the hypothesis, none a proof.** So the archive holds the
    CONSUMERS of leg 3 and not leg 3.
  - **I took the SHAPE and no claim**, as `[LJ-1.11]` requires: the archive ran
    on the rud tower and its condensation target was ruled classically FALSE.
- **`archive/src/2026-08-09-rud-route/L/InitialSegment.lagda.md`**, read the
  chapter's declaration index (`:8-16`, `:65-70`, `:108-120`, `:166-174`,
  `:280-286`). **TOOK: the shape of an initial-segment face and its `Face`
  module's hypothesis discipline.** **NOT taken as a comparable**: it is 114
  in-fence lines on the rud tower, and P-l forbids anchoring on it. Section 8.4.
- `agents/tasks/LJ-1-161/lj-1.161-report.md`, **READ WHOLE.** TOOK the three-leg
  split (`:180-186`), the three MEASURED facts that separate `Lset-only` from the
  transfer (`:199-212`), the repair (`:214-219`), the wall (`:378-410`) and the
  20-minute criterion I reused (`:159-168`).
- `agents/tasks/LJ-1-160/` — **NOT read whole this time.** `[LJ-1.161]` read it
  whole and reports its content at `:496-499`; I took the obligation through that
  report and did not re-read the source. **I mark this so nobody credits me with
  a reading I did not do.**
- `agents/tasks/LJ-1-161/ProbeLJ1161A.agda`, **READ WHOLE.** TOOK the import
  frame and the `module AbsL` opening. **My probe reuses its shape and measures
  the NEXT leg.**
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on a line count.

## 10. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:88-125`, `:205-265` and `:600-630`.**

### 10.1 What Devlin proves at step (a), and whether he needs the unbounded graph

> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that
> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]
> (`dev/literature/devlin-II5.md:95-96`, citing `dev2.txt:1186-1194`)

**MEASURED against the text: Devlin's step (a) is stated at the BOUNDED matrix,
and he does NOT need the unbounded graph.** `Φ` is Σ₀, which is Devlin's name for
Δ₀ (`:616-619` flags the convention). The ONE unbounded quantifier in (a) is the
outer `∃z`, and the digest says so in its own words at `:216`: "Strength: the
existential over z is UNBOUNDED at the ambient level."

**And the digest states how the matrix is made bounded**, at `:249-256`: 2.2 to
2.4 write the Def step as Σ₁, "then bind every unbounded quantifier by the
concrete set K(u) ... The Σ₀ matrix C(w, v, u) with w = K(u) is the bounded
satisfaction substrate of Devlin's engine."

**So the brief's repair is not a workaround. It is Devlin's own form.**
`LevelHood.levelHoodΣ₁ = ∃̇ levelHoodB` with `Δ₀-levelHoodB`
(`src/L/BoundedSubset.lagda.md:108-146`) is `∃z Φ(z, v, γ)` to the character.

### 10.2 The consequence, which sharpens `[LJ-1.161]`

**The delivered `Lset-only` is NOT Devlin's (a).** Devlin's (a) sits at the
bounded matrix; `Lset-only` sits at the unbounded graph
(`src/L/Coding/Sequence.lagda.md:286-292`). **They are two different sentences,
and leg 3 is the bridge between them.** `[LJ-1.161]` named `Lset-only` as leg 3's
target; **the literature says leg 3's target is the BOUNDED statement and
`Lset-only` is what discharges it once the bridge is crossed.** That is the
reading my probe implements.

`dev/literature/devlin-II5.md:604-608`, the 2.6 and 2.7 chain (G is the level
sequence, H says "x = L_α"), read and used to confirm that the graph, not the
level itself, is what carries the witness.

`_build/literature/dev2.txt`: **NOT opened.** Every citation is through the
digest. `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s
measurement that the errata touch no part of II.5.

## 11. C-39: WHAT A PROHIBITION CLOSED, AND WHAT IT DID NOT

- **"Do not build `CrossOut`."** Correct and I obeyed it. I gated one leg.
- **"Do not touch the three `*Agree` masters."** Correct and it cost nothing.
  Reading their `README.md` is what told me the twelve-row split exists, and
  `LeafAgree` in the parent master is what my leaf frame consumes.
- **"A NO-GO is a complete answer."** This changed how I worked. I looked for the
  structural NO-GO first, at the `extAtB→extAt` signature, and found instead that
  the NO-GO is on price. **Finding it early is why I wrote the frames generically
  rather than inlining them.**
- **"Report the count for the ONE LEG."** This is the line that made me split
  telescope from proof. Without it I would have reported 209.

**The one line I would add to the next brief, offered and not assumed.** The
brief says the repair "was never run". **It is run now, and the answer is that
running it is 125 lines, of which 59 are two extensionality frames.** A brief
that funds the next block should say whether it wants the frames written once
and generically, or whether it accepts the Lset-only instance. **Section 6.3
says I did not price the generic variant; that is the next gate, and it is
small.**

## 12. WHAT REMAINS OPEN AFTER THIS TASK

1. **The 52 telescope lines are stated, not discharged.** The one with no
   supplier anywhere in `src/` is `powK`, the definable-power bound. Section 4.3.
2. **`LeafAgree`'s seventeen-hypothesis telescope is delivered but unpriced
   here.** My `Leaf` consumes its two directions through hypotheses of the same
   shape; `LeafAtDefBody` machine-checks the arity, not the discharge.
3. **`[LJ-1.161]`'s wall on the level-hood certificate is untouched.** It sits on
   leg 1's route, not leg 3's.
4. **`HasLevels` and `Covered` are unchanged by this task**, and `[LJ-1.161]`
   section 3 remains the standing reading of them.
