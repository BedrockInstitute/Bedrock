# LJ-1.375 report: adversarial DD25 review of `[LJ-1.373]`

tier: in-harness (adversarial row, `in-harness-subagent-mode`), model
`claude-opus-5[1m]`. Review at maximum effort. It lands nothing. Written
incrementally (C-22). No commit, no push. I wrote no file outside
`agents/tasks/LJ-1-375/`. I ran Agda only under `GHCRTS="-A64m -I0 -M8g"`, one
process, and I counted the slots before every run.

TARGET: `agents/tasks/LJ-1-373/lj-1.373-report.md`, verdict BLOCKED-OTHERWISE.
Read whole, 384 lines. Both of its Agda files re-run.

## VERDICT

**SPLIT.**

**UPHELD.** The target's Agda is correct and it re-runs. `SetChoice (ℓ-suc ℓ)`
gives `BandChoice`. `BandChoice` is the substitution instance of the choice
schema at the band's own index and fiber. I measured that instance in BOTH
directions, which the target did not. The bottom line stands: no delivered term
proves `BandChoice`, so the owner must assume it or pay the untruncation.

**OVERTURNED.** Three claims fall, and the verdict word falls with them.

1. **"With no residue" is FALSE, MEASURED.** `SetChoice` is homogeneous. The
   band's index sits one universe above the band's fiber. The interface refuses
   the raw family (`MustFail375A.agda`, exit 42, `[UnequalSorts]`).
2. **"Two obstructions stack" is FALSE.** The first obstruction has no force.
   The target measured `SetChoice → BandChoice`, a sufficiency. A sufficiency
   gives no lower bound. The target's own literature section says a set-indexed
   instance "must be ruled on" per instance, which contradicts its verdict.
3. **"The band problem bottoms out at the V-to-ZFC interface" is FALSE,
   MEASURED.** A second sufficient purchase exists, it does not follow from
   `SetChoice`, and it is exactly the target's SECOND obstruction
   (`Probe375.agda:142-144`, exit 0).

**So the correct verdict word is BLOCKED-BY-THE-COMPLEMENT, which is the
brief's own second abort criterion.** The brief's framing was not refuted. One
obstruction still explains this chain.

**AND THE BRIEF CAUSED PART OF THE OUTCOME (DD25's third question).** The brief
paid for disagreement. It wrote "a second, distinct obstruction would mean the
chain is harder than anyone has said" (`LJ-1.373.md:66-67`), and it named its
own framing as the premise most likely to be wrong (`:111-119`). An agent that
reads both lines has a gradient toward the third abort word.

## SLOTS, FLOOR, SECONDS

Floor measured fresh: `Floor375.agda`, exit 0, **0.75 s**. Every figure below is
WARM. The interface chain and the sibling probes were already built. I measure
no check time as a price, so no cold figure is owed here (P-l).

Slots counted with the brief's exact command before EVERY invocation. The count
was 0 every time. One process per run. Cap never raised. No heap exhaustion.

| run | file and outcome | exit | real s |
|---|---|---:|---:|
| 1 | `Floor375.agda`, the floor | 0 | 0.75 |
| 2 | `Probe375.agda`, mine, **GREEN** | **0** | 2.38 |
| 3 | `MustFail375A.agda`, mine, **REFUSED, the control** | **42** | 2.44 |
| 4 | `Probe373.agda`, the target's, re-run, GREEN | 0 | 2.35 |
| 5 | `MustFail373A.agda`, the target's, re-run, REFUSED | 42 | 1.54 |

Runs 4 and 5 reproduce the target's table exactly, including the error text it
quotes. Its figures were 2.46 s and 2.40 s. Mine are 2.35 s and 1.54 s on a
warmer tree.

## MECHANICAL FINDING: the target is RED on a gate its own brief named

The target's brief says "`scripts/gate/check-dd18-survey.py` GATES your return"
(`LJ-1.373.md:146-147`). **I ran it. It fails, MEASURED:**

```
check-dd18-survey: 1 gated return(s) fail B2:
  LJ-1-373:
    quote: archive/src/2026-08-09-rud-route/Everything.lagda.md:67 quotes text
    the file does not hold
```

**THE CAUSE is a transcription slip and not a false claim.** Line 67 reads
"- `Base.Choice`{.Agda}: the boundary's second interface: set-level choice".
The target quotes it without the `{.Agda}` annotation
(`lj-1.373-report.md:293-294`), so the substring does not occur.

**THE TARGET SAYS IT RAN THE GATES.** At `:382-384` it reports
"The two lint gates the brief names pass". **The brief names THREE**, and this
is the third. `lint-prose.py` and `lint-agda.py` do pass, and they pass on my
files too.

**The content of the citation is correct**, as my own ARCHIVE USED shows. Fix
the quote and the gate goes green.

**ONE CAVEAT, and I checked it rather than assuming.** `check-dd18-survey.py`
carries an uncommitted edit from the sibling `[LJ-1.372]`. `git diff --stat`
reports 52 insertions and 0 deletions, and the added lines are the mtime
backstop and the task-index row reader. **The B2 quote rule is untouched, so
the RED is not an artefact of a live edit.**

## ATTACK 1: is `BandChoice` an exact instance of `SetChoice (ℓ-suc ℓ)`?

**ANSWER: it is an exact instance of the SCHEMA, and it is NOT an instance of
the tree's `SetChoice` at any one level. The residue is two universe lifts and
it is FORCED.**

### 1.1 The schema half is true, and it is stronger than the target measured

The tree's interface, `src/Base/Choice.lagda.md:54-56`:

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```

I re-derived the substitution instance at the band's own index and fiber, with
no `Lift` and no `isSet`. `Probe375.agda:90-92`:

```agda
RawInstance : Type (ℓ-suc ℓ)
RawInstance = ((i : BandIndex) → ∥ RawFiber i ∥₁)
            → ∥ ((i : BandIndex) → RawFiber i) ∥₁
```

**BOTH directions are green**, `Probe375.agda:107-111`:
`bandchoice-from-raw : RawInstance → BandChoice` and
`raw-from-bandchoice : BandChoice → RawInstance`. Exit 0, 2.38 s, floor 0.75 s.

**WHAT THAT MEASURES.** `BandChoice` and the schema instance are
inter-derivable. The whole distance is currying. No `isSet` proof enters. So
the target's sentence "`BandChoice` is a selection from a truncated family" is
exact, and I strengthened it: the target measured one direction only
(`Probe373.agda:136-138`).

### 1.2 The residue is real, and Agda names it

`SetChoice ℓ` is HOMOGENEOUS. It binds `X : Type ℓ` and `B : X → Type ℓ` at ONE
level. The band is not homogeneous. `BandIndex : Type (ℓ-suc ℓ)`
(`Probe373.agda:78`), while `sq : S → Type ℓ`
(`src/L/Ordinal/SquareLaw.lagda.md:685`).

The target's own Agda pays for that gap. It writes `BandFiber i = Lift (sq (fst
i))` (`Probe373.agda:107`), then `PT.map lift` in `band-inh` (`:116`) and
`lower` in `band-sel` (`:122`).

**I removed only the `Lift` and measured the refusal.** `MustFail375A.agda:81`,
exit 42, 2.44 s:

```
error: [UnequalSorts]
(Type ℓ) != (Type (ℓ-suc ℓ))
when checking that the expression RawFiber has type
BandIndex → Type (ℓ-suc ℓ)
```

**So the two lifts are not a spelling choice. The interface cannot be applied to
this band without them.** The target's verdict says "exactly and with no
residue" (`lj-1.373-report.md:29`). Its own body says the opposite: "the
whole distance between the band and the tree's own interface is ONE `isSet`
proof plus two lifts" (`:158-160`). The verdict overstates the body.

**HOW MUCH DOES THE RESIDUE COST?** Little, and I say so plainly. `Lift A ≃ A`,
and the tree already does this exact move in `lowerSetChoice`
(`src/Base/Choice.lagda.md:68-74`), which `V.Model` spends at `:530`. So the
residue is precedented and it moves no strength. **It is still a residue, and
"no residue" is the word the review was asked to check.**

### 1.3 The direction, which is where the framing breaks

The orchestrator's framing says the GCH descent's last blocker "is the same
priced interface the tree already carries". **That needs two directions. Only
one is measured, and the target says so itself** (`:164-167`): "An instance can
be weaker than the interface. Nothing here proves `BandChoice` is AS STRONG as
`SetChoice (ℓ-suc ℓ)`."

I priced the gap at the one end that measures cheaply. `Probe375.agda:124-125`,
green: `lem-from-setchoice : SetChoice (ℓ-suc ℓ) → LEM (ℓ-suc ℓ)`, which is the
tree's own `choice→lem` (`src/Base/Choice.lagda.md:285-286`).

**So `SetChoice (ℓ-suc ℓ)` returns the whole classical parameter that every L
chapter already carries.** `src/L/GCH.lagda.md:10` is
`module L.GCH {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where`. Nothing is known to run
the other way from `BandChoice`. **The target's line "assuming the interface
that implies it is the same cost under a wider name" (`:210-211`) is therefore
wrong as written.** It is a strictly wider bill, MEASURED in the one direction
that can be measured.

### 1.4 "The tree already carries it" is true of the wrong tower

`src/Landmarks.lagda.md:54` is exactly as the orchestrator read it:

```agda
V⊨ZFC : ∀ {ℓ : Level} → SetChoice (ℓ-suc ℓ) → isZFCModel (𝒮ᵥ {ℓ})
```

**VERIFIED.** The level matches and the interface matches.

**BUT THE BAND IS NOT ON THAT TOWER.** `src/Landmarks.lagda.md:76`:

```agda
L⊨ZFC : ∀ {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) → isZFCModel (𝒮ʟ {ℓ})
```

The L trophy takes LEM and nothing else. The chapter prose at `:63` says "One
hypothesis, and it is the same one the previous landmark pays."

**MEASURED: `SetChoice` appears in ZERO files under `src/L/`.** `grep -rn
SetChoice src/` returns `src/Base/Choice.lagda.md`, `src/Landmarks.lagda.md`,
`src/V/Model.lagda.md`, `src/README.md` and `src/Everything.lagda.md`. **So a
`SetChoice` spend on the band would be the FIRST on the L side.** It would give
the GCH trophy a bill the AC trophy does not carry, and it would falsify the
Landmarks sentence at `:63`. The target's DD4 section notes "one new parameter"
(`:283`) but does not price this asymmetry. **That is a route-level cost, and
neither the target nor the brief has it.**

## ATTACK 2: are there two obstructions, and is the second one independent?

**ANSWER: there is ONE obstruction with force, and it is the canonicalizer's
complement. The target's FIRST obstruction is not an obstruction.**

### 2.1 The first obstruction carries no force

The target's obstruction 1 is "the SHAPE" (`:25-27`): `BandChoice` is an
instance of `SetChoice`, and the tree never proves `SetChoice`.

**That argument runs the wrong way.** "X is implied by an unproved axiom" is
true of every theorem in the tree. It gives no evidence that X is unprovable.
To turn the shape into an obstruction you need `BandChoice → SetChoice`, or
`BandChoice → LEM`, or `BandChoice →` something known unprovable. **The target
measured none of the three and says so at `:164-167`.**

**THE TARGET REFUTES ITSELF INSIDE ITS OWN LITERATURE SECTION.** At `:57-58` it
writes: "A set-indexed instance is neither proved nor refuted by the
literature. It must be ruled on per instance." That sentence says the shape
decides nothing. At `:24-26` it writes: "The obstruction that decides the
question is NOT the canonicalizer's complement. It is the SHAPE." **The two
sentences cannot both stand.**

### 2.2 The second obstruction is real, and I verified its evidence

I checked `[LJ-1.333]`'s measurement rather than believing it.

- The tree's only untruncated supplier is `via-col-square`,
  `src/L/Ordinal/SquareLaw.lagda.md:960-961`. VERIFIED at that line.
- It consumes `InitialCore`'s `noinj²`, which is `Init`'s fourth row.
  **The row is at `src/L/Ordinal/SquareLaw.lagda.md:696-698`**, which I printed
  with line numbers.
- The band negates that row: `(Init δ → Empty.⊥)` sits in `LimitBandT`
  (`Probe368.agda:195`) and in `LimitBand` (`ProbeLJ1337B.agda:127`).
- `[LJ-1.333]`'s own citation is `:696-698`
  (`agents/tasks/LJ-1-333/lj-1.333-report.md:182-183`). **The target's premise
  check cites `:697-699` (`lj-1.373-report.md:252-253`), which is off by one at
  both ends.** Minor, and it is still an evidence slip in a report that trades
  on `file:line`.

**So obstruction 2 stands.** It is real, and it is the only one.

### 2.3 The cheaper reading of the same fact, MEASURED

`Probe375.agda:142-144`, green, exit 0:

```agda
bandchoice-from-pointwise-split : ((δ : S) → ∥ sq δ ∥₁ → sq δ) → BandChoice
```

Pointwise split support of the fiber gives `BandChoice` in one line. It needs
no selection over the index. By Kraus et al. Theorem 16
(`dev/literature/truncation-and-selection.md:158-160`) split support and a
weakly constant endomap are the same condition. **That condition is the
target's SECOND obstruction.**

**AND THE TWO PURCHASES ARE INCOMPARABLE, not ordered.** `SetChoice` does not
give pointwise split support: the digest's section 2.7 records that AC's
conclusion is truncated and "never `f`" (`:229`). So the band does not "bottom
out" at `SetChoice (ℓ-suc ℓ)`. **At least two sufficient purchases exist,
neither follows from the other, and only one of them returns `LEM (ℓ-suc ℓ)`.**

## ATTACK 3: did the target miss a condition in the digest?

**ANSWER: it missed one line that bears directly on its own second obstruction,
and its audit of the digest's checklist is inaccurate. The outcome survives.**

I read `dev/literature/truncation-and-selection.md` whole, 363 lines.

### 3.1 The checklist audit is wrong

The target writes: "NO OTHER CONDITION EXISTS IN THE DIGEST. Its checklist,
`:295-310`, is the five above plus its own step 6" (`:125-127`).

**MEASURED against the file.** The checklist is at `:285-326` and it has SIX
steps.

| digest step | line | in the target's five? |
|---|---|---|
| 1. Is the GOAL a proposition? | `:289-290` | **NO** |
| 2. Is `A` a proposition? | `:291-292` | yes, its A |
| 3. Is the goal a SET, with a `2-Constant` map into it? | `:293-296` | **NO** |
| 4. `leastOf` over a well-order | `:297-300` | yes, its C |
| 5. A weakly constant endomap by any route | `:301-302` | yes, its D |
| 6. Must the map break a symmetry? | `:318-326` | yes, named |

The target's cited range `:295-310` starts in the middle of step 3. It covers
steps 4 and 5 and the `[LJ-1.334]` defect note. **It covers no part of steps 1,
2 or 6.** Its condition B (Exercise 3.19) is at `:112` and is not in the
checklist at all.

**DOES THE OUTCOME CHANGE? NO, and I say why.** Step 1 is MET at the outer goal:
`∥ LimitBand ∥₁` is a proposition, which is why `closes-from-choice` works
(`Probe368.agda:229-236`). Step 1 FAILS under the band's Pi, where the goal
becomes `sq δ`. Step 3 then asks for a `2-Constant` map into that goal, and the
goal is the fiber, so step 3 collapses into the endomap of step 5. **The
target's answer survives. Its bookkeeping does not.**

### 3.2 The one line it should have used

The digest, `:161`: "**Theorem 17: a MERELY weakly constant endomap is
enough.**"

The target quotes `:158-159` for Theorem 16 and stops one line short. Its
LITERATURE USED list (`:328-335`) names `:158-159` and never `:161`.

**WHY THAT LINE MATTERS HERE.** The target's second obstruction is that the
band has no SUPPLIER for the endomap. `band-from-endomap` demands the supplier
as data, uniformly in δ: `(δ : S) → Σ[ e ∈ (sq δ → sq δ) ] 2-Constant e`
(`Probe368.agda:205-206`). Theorem 17 weakens what must be supplied. **A
weakening of the exact requirement whose refutation is the verdict is not an
optional citation.**

**I did not measure whether Theorem 17 changes the answer, and neither did the
target.** The digest gives one sentence and no proof. UNMEASURED by both of us.
**DD18 asks for WHY NOT on anything not used, and this line has no WHY NOT.**

### 3.3 "Exactly one sufficient condition" is wrong

The target writes "the only SUFFICIENT condition the literature names, the
weakly constant endomap" (`:35-36`). **The digest names four sufficient
conditions**: steps 1, 2, 3 and 4. The endomap is the only NECESSARY AND
SUFFICIENT one, which the target states correctly at `:110`. The two sentences
disagree with each other.

### 3.4 One candidate neither of us examined

`L⊨ZFC` proves the constructible structure models ZFC from LEM alone
(`src/Landmarks.lagda.md:76`). So the tree already OWNS an internal choice
principle on the L side, proved rather than assumed. **The target never asks
whether that delivered internal choice supplies anything for the band.**

**INFERRED, and I did not measure it: it does not.** The band's index is an
external telescope over `S`, and its fiber is external data. An internal choice
set would still need an external read-out, which is the same untruncation. **I
name it as a gap in the survey and not as a cure.**

## ATTACK 4: the tree's boundary prose at `src/V/Model.lagda.md:427`

**ANSWER: the quote is exact. Its reach is smaller than the target's use of
it.**

`src/V/Model.lagda.md:426-427`, verbatim:

> The excluded middle does not prove choice, so upgrading to ZFC costs a
> genuinely new assumption: the choice chapter's `SetChoice`{.Agda}.

**VERIFIED at those two lines.** The target's citation and its wording are both
correct, and it marks the line honestly as "a recorded position, not a proof"
(`:187`).

**WHAT IT DOES NOT REACH.** The sentence is about the SCHEMA. `BandChoice` is
one instance. LEM not proving the schema says nothing about one instance, for
the same direction reason as attack 2. **So witness 2 supports the report's
END ONE and not its answer about the band.**

**WITNESS 1 IS WEAKER THAN THE TARGET PRESENTS.** `MustFail373A.agda:80-82`
applies `LEM (ℓ-suc ℓ)` to FOUR arguments. `LEM ℓ = (P : hProp ℓ) → ⟨ P ⟩ ⊎ (⟨ P
⟩ → Empty.⊥)` (`src/Base/Classical.lagda.md:41-42`) takes ONE argument, an
`hProp`. **The refusal is an arity and type mismatch, and any function of the
wrong type refuses the same way.** The target claims "The delta between exit 0
and exit 42 is the selection structure, nothing else in the body differs"
(`:239-240`). **That is false: the arity differs and the first argument's type
differs.** The brief warned about exactly this, quoting C-45's mirror: "exit 42
is not an impossibility, which is exactly how `[LJ-1.365]` overreached"
(`LJ-1.373.md:126`).

**SO "LEM ALONE: NO" RESTS ON WITNESS 3 ALONE, which the target marks
INFERRED.** I agree with the answer. I do not accept it as three independent
witnesses. It is one INFERRED argument, one prose position about a different
statement, and one type error.

## DD28: is the literature half load-bearing, or retrofitted?

**ANSWER: retrofitted in its function, though honestly reported in its
history. INFERRED, and I name the evidence.**

I cannot see the run order, so the negative is INFERRED. Four signatures point
one way.

1. **It decided nothing.** Its verdict is the digest's own "It must be ruled
   on" (`:219-221`). DD28 says the survey is the probe's GATE. A gate that
   returns "not settled" did not gate.
2. **It added nothing new to the chain.** The one condition it identifies as
   necessary and sufficient, the endomap, was already the chain's own C-54
   obligation, already spelled in Agda at `Probe368.agda:205-210` by the
   previous task, and already named in the brief at `LJ-1.373.md:69-70`.
3. **The one line that could have moved the answer was skipped**, Theorem 17 at
   `:161`, one line below the line it used. See 3.2.
4. **The checklist audit does not match the file**, and the mismatch runs in the
   direction of completeness. See 3.1.

**WHAT THE LITERATURE HALF DID EARN.** Conditions A, B and C are checked
against this band with real citations, and each check is correct. Condition E
set the Agda's scope honestly. **The survey is a real reading. It is not a
decision, and the report presents it as the spine that decides.**

**A NOTE FOR DD28 ITSELF, from this pair.** The literature said "must be ruled
on". Under DD28 that is a full return and the Agda should have stopped. The
Agda that then ran did not check a literature condition: it built a sufficiency
from an interface the literature never named. **The rule worked; the report's
own account of which half decided is the part that drifted.**

## WHAT THE TARGET GOT RIGHT, in one list

A review that only attacks is a review that cannot be trusted on its attacks.

- The green derivation is correct and it re-runs. Exit 0, 2.35 s.
- The `isSet` proof on the telescope is real work, and it discharges.
- The level claim is right. `ℓ-suc ℓ` is where the tree's interface can accept
  this index.
- Its `Landmarks:54` reading is exact.
- Its `V/Model:426-427` quote is exact.
- **Its ARCHIVE USED section is accurate at every line I checked.** See below.
- It marks its own C-36 limits in the places that matter, including the one
  that undercuts its verdict.
- The bottom line stands: no delivered term proves `BandChoice`.

## ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/`** CITED. I checked the target's claim
  that the retired route never proved a selection from a truncated family.
  **CONFIRMED, MEASURED.** `grep -rln SetChoice archive/` returns exactly ONE
  file. `archive/src/2026-08-09-rud-route/Everything.lagda.md:68`:
  "`SetChoice`{.Agda}, stated levelwise like `LEM`{.Agda}, with Diaconescu's".
  I also verified the two module lines the target quotes:
  `archive/src/2026-08-09-rud-route/L/Choice/Order.lagda.md:42` is
  `module L.Choice.Order {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where`, and
  `.../L/Choice/Transversal.lagda.md:50` is the same shape. **Both exact.** One
  correction: the target adds "and the patch" to its grep result, and no patch
  file under `archive/` holds the string. UNREPRODUCED, and it changes nothing.
- **`archive/dev/JOURNAL-archived.md`** CITED.
  `archive/dev/JOURNAL-archived.md:1630`: "evidence: a choice principle implies
  excluded middle and would cost the tree's postulate-free claim,". **Quoted at
  the right line.** The target's reading is right: the sentence argues against
  ADDING a parameter. **It now bears harder than the target says**, because
  `choice→lem` makes it literal at `ℓ-suc ℓ` (attack 1.3).
- **`archive/dev/DECISIONS-archived.md`** CITED.
  `archive/dev/DECISIONS-archived.md:30`, D2: "LEM (and any classical/choice
  principle) is an explicit parameter; the whole tree is `--safe`." **Quoted at
  the right line.** WHY NOT the rest: I scanned the table and found no row on
  truncation, on selection or on the band.
- **`archive/dev/TASKS-archived.md`** CITED.
  `archive/dev/TASKS-archived.md:66`: "| L3.32-T31 | Square law, discharged |
  DELIVERED (transfer blocked) | `_build/l3.32-t31-report.md` |". **Quoted at
  the right line.** Shape only, as the target took it: a square-law dispatch
  delivered under a hypothesis with the transfer named as blocked.

**So all four of the target's archive citations verify at their stated lines.**
That is the strongest part of its return.

## LITERATURE USED (DD18)

`dev/literature/truncation-and-selection.md`, read whole, 363 lines.

USED, and each one bears on a claim above:

- `:158-160`, Kraus et al. Theorem 16, split support equals a weakly constant
  endomap. It is what makes my `bandchoice-from-pointwise-split` the same
  condition as the target's obstruction 2.
- `:161`, Theorem 17, a merely weakly constant endomap. **The line the target
  did not use and did not decline.** Attack 3.2.
- `:229`, "AC delivers `∥ f ∥₁` for a selection function `f`, never `f`". It is
  why the two sufficient purchases are incomparable, attack 2.3.
- `:219-221`, "not refuted by the standard taboo, and it is also not proved. It
  must be ruled on." It is the sentence that refutes the target's own
  obstruction 1.
- `:285-326`, the six-step checklist, read step by step for attack 3.1.
- `:289-296`, steps 1 and 3, the two the target's five omit.
- `:293-296`, "This step is easy to skip and it is the one that most often has
  an answer."
- `:312-316`, the family-level closure of the symmetry refutation.
- `:335-337`, "A canonical injection needs a well-order on the INJECTIONS."

WHY NOT the rest. Section 1, the set-theory side, prices the least-witness
device, and the target already checked it as condition C. Section 3.1,
Paulson's classical Isabelle/ZF, cannot state the question, so it is evidence
in no direction. Section 3.2, Matthews and Rathjen, warns about a constructive
`L`, and this tree spends LEM, so its regime does not apply. Section 6, sources
and status, told me which numbers I may cite by label.

**One digest line I read and chose not to press:** `:312-316` closes a FAMILY of
canonical readers, not one recipe. It could strengthen obstruction 2 beyond
`[LJ-1.333]`'s single refutation. **P-l stops me: it was measured at
`[LJ-1.334]`'s site and this is another site.** I name it as an unpriced
strengthening and I claim nothing from it.

## DD4

The axis, fixed at `scripts/measure/ledger.py:50`: what the AC and GCH closures
SHARE, in masters and lines.

**This review lands nothing, so it moves no shared line.** Its DD4 content is a
finding, not a term, and the target's DD4 section misses it.

**THE FINDING.** A `SetChoice (ℓ-suc ℓ)` spend on the band is not one new
parameter on a neutral tree. **MEASURED: `SetChoice` appears in ZERO files
under `src/L/`.** The AC trophy takes LEM alone (`src/Landmarks.lagda.md:76`)
and `L.GCH` takes LEM alone (`src/L/GCH.lagda.md:10`). **A spend on the GCH
wing would give the two trophies DIFFERENT bills for the first time**, and the
Landmarks prose at `:63` states that they carry the same one. **That is a DD4
cost, because a hypothesis one closure carries and the other does not is a
hypothesis the two closures cannot share.**

The untruncation route keeps both bills equal. **The two prices the target
printed are therefore not the only two axes, and this one is the DD4 axis.**

## WHAT I DID NOT DO

I attempted no proof of `BandChoice` and no refutation of it. C-36 binds every
negative above and each is marked. I did not search for a second canonicalizer.
I did not measure Theorem 17. I did not touch `src/`, any sibling task's files,
`make check`, git history, or the working tree outside
`agents/tasks/LJ-1-375/`. I ran no `make` target.

Lines, in `agents/tasks/LJ-1-375/`:

| file | total | non-blank |
|---|---:|---:|
| `Probe375.agda` | 144 | 123 |
| `MustFail375A.agda` | 81 | 68 |
| `Floor375.agda` | 7 | 5 |
