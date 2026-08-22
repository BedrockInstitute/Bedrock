# LJ-1.514 report: does the level graph name any constant at all

**VERDICT: GO.** The obligation is built and it typechecks.
`agents/tasks/LJ-1-514/Probe514.agda:159-160`, exit 0, `runs/full-0.out`.
The witness resolves from outside the probe. `runs/witness.out` carries no
error line, and that run returned exit 0. The witness form is the one
`scripts/pod/witness.py:278` derives, `witness = Target.<name>`, reproduced at
`agents/tasks/LJ-1-514/runs/WitnessCheck.agda:18`.

**THE CENSUS IS NOT EMPTY. IT IS 664.** The brief's cheap branch, "if the list
is empty, `mapFo` along any map transports the formula", does NOT apply.
**The wall is still vacuous, but for a different reason than the brief
expected, and that reason is delivered machinery and not a new proof.**

**THE ONE SENTENCE FOR THE NEXT BRIEF.** `mapFo` was the wrong instrument.
The tree's instrument for a partial constant map is `Relabel`
(`src/FOL/Manipulation/Bounding.lagda.md:146`), and `mkBoundedFo`
(`src/L/Axioms/Separation.lagda.md:449`) builds its certificate for ANY
formula, with no hypothesis. **So the Formula-carrier wall of `[LJ-1.494]` is
removed for every formula of this family at once, not only for this one.**

## THE CONSTANT CENSUS

**MEASURED, NOT READ.** `countFo` is the tree's own counter
(`src/FOL/Manipulation/Parameters.lagda.md:74`). `satGraphAt` is sealed
(`src/L/Coding/Graph.lagda.md:203`), so the count is stuck behind the seal.
The probe opens it with `unfolding satGraphAt`, which is reading and not
editing.

    countFo (LsetGraphAt w b) = 664

Basis: `runs/w3-0.out:3-4`, the deliberate mismatch `664 != 0 of type ℕ`.

**NOT `NONE`.** Every occurrence is charged below. One row per naming site on
the unfolding path. Every number is machine-checked by one `refl` over a
16-entry vector (`agents/tasks/LJ-1-514/Probe514.agda:64-88`), so no number
in this table is a reading.

| site | `file:line` | `countFo` |
|---|---|---|
| `LsetGraphAt w b` | `src/L/Coding/Sequence.lagda.md:291,349` | 664 |
| `ApproxAt f a` | `src/L/Coding/Sequence.lagda.md:286` | 332 |
| `StepAt v b f` | `src/L/Coding/Sequence.lagda.md:119` | 332 |
| `domAt f d` | `src/L/Coding/Model.lagda.md:278` | 0 |
| `appAt f x y` | `src/L/Coding/Model.lagda.md:160` | 0 |
| `prAtL q u v` | `src/L/Coding/Model.lagda.md:122` | 0 |
| `DefAt u w` | `src/L/Coding/Powerset.lagda.md:442` | 166 |
| `isCodeAt c w` | `src/L/Coding/Powerset.lagda.md:297` | 35 |
| `satGraphAt B x y` | `src/L/Coding/Graph.lagda.md:204` | 44 |
| `DefinesAt x w v` | `src/L/Coding/Powerset.lagda.md:217` | 4 |
| `keyArityAtL c k` | `src/L/Coding/CodeSet.lagda.md:135` | 1 |
| `hasWitnessAt A x` | `src/L/Coding/CodeSet.lagda.md:240` | 34 |
| `envOneAt e y` | `src/L/Coding/Powerset.lagda.md:128` | 2 |
| `tagAtL s k x` | `src/L/Coding/Model.lagda.md:586` | 1 |
| `closedAt C` | `src/L/Coding/Model.lagda.md:2191` | 8 |
| `shapedAt C A` | `src/L/Coding/Shape.lagda.md:189` | 26 |

**THE ROOT NAMING SITE IS ONE LINE, AND IT IS THE ONLY ONE.**
`src/L/Coding/Model.lagda.md:586`:

    tagAtL s k x = ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))

Its own count is 1, and that 1 is `con (numeralL k)`
(`src/L/Axioms/Numerals.lagda.md:175`). **The graph's own skeleton names
nothing**: `domAt`, `appAt` and `prAtL` each count 0. The whole 664 is spent
by the definable powerset, whose shape and closure clauses tag a code with a
numeral once per clause.

**THE ARITHMETIC OF THE TABLE CHECKS.**

- `664 = 332 + 332`. `GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w)
  (suc b) zero)` (`src/L/Coding/Sequence.lagda.md:291`): one `ApproxAt`, one
  `StepAt`.
- `332 = 0 + 0 + 332`. `ApproxAt f a = domAt f a ∧̇ ∀̇ (∀̇ (appAt … ⇒̇ Step …))`
  (`src/L/Coding/Sequence.lagda.md:286`).
- `35 = 1 + 34`. `isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c`
  (`src/L/Coding/Powerset.lagda.md:297`).
- `34 = 8 + 26`. `hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero) ∧̇ (closedAt
  zero ∧̇ shapedAt zero (suc A)))` (`src/L/Coding/CodeSet.lagda.md:240`).

## DOES EACH CONSTANT LIE IN THE STAGE

**THE BRIEF ASKED FOR A PER-CONSTANT ANSWER. THE TREE GIVES A BETTER ONE, AND
THAT IS THE FINDING.** A per-constant table of 664 rows is not needed, because
one delivered recursion answers all of them at once.

`mkBoundedFo` (`src/L/Axioms/Separation.lagda.md:449`):

    mkBoundedFo : ∀ {n} (φ : Formula S n)
                → Σ[ σ ∈ V ℓ ] (IsOrd σ × BoundedFo (Below′ σ) φ)

It is TOTAL. It takes any formula over `CS.S` and returns a stage plus a
per-occurrence certificate that every constant of that formula lies in that
stage. `Below′ σ c = ⟨ fst c ∈ Lset σ ⟩`
(`src/L/Axioms/Separation.lagda.md:415`). A constant contributes `stage`, a
variable contributes nothing, and each branching node merges the two stages by
`bound2` (`src/L/Axioms/Separation.lagda.md:449-461`).

**So the answer for each of the 664 constants is: YES, in the stage that this
recursion computes.** The only open quantity was whether the ambient `α` is
above that stage, and section "WHAT WAS BUILT" closes it.

## THE TRANSPORT, AND WHY `mapFo` WAS THE WRONG INSTRUMENT

The brief is right that no total map `CS.S → SL` exists, and this task did not
look for one. **`mapFo` is not what the tree uses for this.** It uses
`Relabel` (`src/FOL/Manipulation/Bounding.lagda.md:146`), and that chapter's
own prose names this exact instance
(`src/FOL/Manipulation/Bounding.lagda.md:135-137`):

> In the intended instance the source is the model's carrier, the target is a
> stage's member type, the world is the hierarchy, and the equation is the
> fact that a member of a stage, viewed as a set, is the set it was.

`Relabel.liftFo` (`src/FOL/Manipulation/Bounding.lagda.md:162`) takes the
formula and a `BoundedFo P` certificate. **That is the partial map the brief
asked for: its domain is the finite set of constants and not the carrier.**

The instance the probe builds (`agents/tasks/LJ-1-514/Probe514.agda:110-113`):

| `Relabel` parameter | value |
|---|---|
| `K` | `CS.S`, the carrier of `𝒮ʟ` |
| `K'` | `SL` |
| `W` | `V ℓ` |
| `proj`, `up` | `fst`, `fst` |
| `P` | `Below′ α` |
| `down` | `λ c h → fst c , h` |
| `down-correct` | `refl` |

`down-correct` is `refl` because `𝒮ᵥ`'s carrier IS `V ℓ`
(`src/V/Hierarchy.lagda.md:79-82`), and `SL = Σ[ x ∈ V ℓ ] ⟨ x ∈ Lset α ⟩`
(`src/FOL/Absoluteness.lagda.md:64-65` with `src/L/Hull.lagda.md:153-156`).
The two projections agree on the nose, so the equation the interface demands
costs nothing.

## WHAT WAS BUILT

**THE OBLIGATION, UNCONDITIONAL.** `agents/tasks/LJ-1-514/Probe514.agda:159-160`:

    graphFo-at-SL : {n : ℕ} (w b : Fin n) → Formula (Stage.SL w b) n
    graphFo-at-SL w b = Stage.TR.RL.liftFo w b (LsetGraphAt w b) (Stage.cert w b)

**No module hypothesis. No postulate. No reflection principle. No `hierL`.**
`Stage.SL w b` is `AtStage.SL` (`src/L/Hull.lagda.md:153`) at the stage the
formula itself names, and that stage is computed and not assumed
(`agents/tasks/LJ-1-514/Probe514.agda:136-154`):

    σ = fst (mkBoundedFo (LsetGraphAt w b))
    α = sucV σ
    cert = liftFoTo (self∈sucV σ) (LsetGraphAt w b) (snd (snd bnd))

`self∈sucV` (`src/V/Model.lagda.md:236`) puts `σ` inside `sucV σ`, and
`suc-ord` (`src/L/Ordinal.lagda.md:96`) keeps it an ordinal. `liftFoTo`
(`src/L/Axioms/Separation.lagda.md:425`) raises the certificate from `σ` to
`α`. **Nothing in this chain is normalised. Every step is an application**,
which is why it costs seconds and not minutes.

**THE GENERAL FORM, AT AN ARBITRARY STAGE.**
`agents/tasks/LJ-1-514/Probe514.agda:118-126`:

    graphFo-at-anyStage : {n : ℕ} (w b : Fin n) → Formula SL n

under exactly one named side condition,

    inStage : {n : ℕ} (w b : Fin n) → ⟨ fst (mkBoundedFo (LsetGraphAt w b)) ∈ α ⟩

**That side condition is a bound on the stage. It is NOT a fact about
`hierL`.** `[LJ-1.494]`'s first blocker, stage membership of `hierL`
(`agents/tasks/LJ-1-494/lj-1.494-report.md:125`), is untouched by this task
and is not needed by it.

## W3, THE WIDEST UNMEASURED TERM

The brief named the census itself, and the census was done FIRST, before any
transport. It changed the task: the brief's expected answer was NONE, and the
measured answer is 664. **A NONE would have made the transport free by
`mapFo`. The 664 forced the correct instrument to be found**, and the correct
instrument turned out to be stronger than the one the brief expected.

**PRICE, one Agda process, `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, three
forced rechecks each. No heap wall. No rerun of a walled run.**

| measurement | median wall | median peak RSS | basis |
|---|---|---|---|
| W3 alone | 2.53 s | 405,422,080 bytes | `runs/w3-1.time`, `runs/w3-2.time`, `runs/w3-3.time` |
| full file | 14.42 s | 523,583,488 bytes | `runs/full-1.time`, `runs/full-2.time`, `runs/full-3.time` |
| witness | 2.45 s | 466,747,392 bytes | `runs/witness.out:2-3` |

**W3 came in under the brief's estimate.** The brief said "about 25 lines of
reading and under 30 seconds of Agda". Measured: 2.53 s. The brief told me not
to fund W3 against `[LJ-1.494]`'s W3, and I did not.

**THE ATTRIBUTION TABLE COST 16 EXTRA RUNS AND THAT IS RECORDED.** Agda stops
at the first mismatch in a vector, so each site's number cost one run at about
2.5 s. Total about 40 s. This is a method note for the next brief that wants a
census: budget one run per row, not one run per census.

## THE ESTIMATE AGAINST THE MEASUREMENT

| quantity | brief | measured |
|---|---|---|
| probe, non-blank non-comment | about 120 | 86 |
| obligation, non-blank non-comment | about 30 | 30 |

The obligation landed exactly on the brief's figure. The probe came in under,
because the census block replaced hand reading with 27 lines that Agda checks.

## W2, THE GENERIC CARRIER

**The brief did not state W2, and I answer it anyway.** Nothing in this task
writes mathematics twice. The transport is stated ONCE, at `Relabel`'s generic
telescope, which is already in the tree. This task adds one instance of it and
no new generic layer. `Stage` and `Transport` are two views of the same
instance: `Stage` fixes the stage that the formula computes, and `Transport`
leaves the stage open. **There is no fixed form here that a deadline forced.**

## W4, THE RETIREMENT CLAUSE

Not applicable. No module was retired, and nothing under `src/` changed.

## WHAT THE STATEMENT COST, AND WHAT RESISTED

- **What it cost.** 30 non-blank non-comment lines for the obligation, 86 for
  the whole probe, 14.42 s median for the full recheck.
- **What the shape resisted.** Two things, and both were mechanical.
  First, `satGraphAt` is sealed, so the census does not compute until the seal
  is opened. Opening it inside the probe is reading, and it costs nothing.
  Second, the obligation must resolve from OUTSIDE the probe.
  `[LJ-1.494]`'s obligation sat inside a submodule and read `[NotInScope]`
  (`agents/tasks/LJ-1-494/runs/witness.out:1`). **`graphFo-at-SL` is therefore
  declared at the probe's own top level**, and `runs/WitnessCheck.agda`
  reproduces the meter's own derivation
  (`scripts/pod/witness.py:260-280`) to prove it.
- **What I had to weaken.** Nothing in the obligation. The type differs from
  the brief in ONE respect: the brief wrote `Formula SL n` with `SL` fixed by
  an ambient stage, and the delivered type is `Formula (Stage.SL w b) n`,
  where the stage is COMPUTED from the formula. **That is a strengthening and
  not a weakening**: the briefed shape is also delivered, as
  `graphFo-at-anyStage`, and it is the one that carries a hypothesis.
- **What I could not close.** Nothing this brief ordered. Two things this
  brief forbade remain open, and they are named below.

## WHAT THE NEXT BRIEF NEEDS

1. **The Formula-carrier wall is GONE, and it is gone for the family.**
   `[LJ-1.494]`'s second blocker
   (`agents/tasks/LJ-1-494/lj-1.494-report.md:364-368`) asked for "a formula
   whose constants live in `SL`, or a delivered map `CS.S → SL`". The answer
   is neither. It is `Relabel` plus `mkBoundedFo`, and it applies to ANY
   `Formula CS.S n`. `LsetGraphAt` is not special.
2. **Do not order a total map `CS.S → SL`.** It would be false, and no term in
   this probe needs one.
3. **`hier-in-stage` IS STILL OPEN AND THIS TASK DID NOT TOUCH IT.**
   `[LJ-1.494]` measured it (`agents/tasks/LJ-1-494/lj-1.494-report.md:125`).
   A brief that wants `GraphSatAtStage` still needs it, or a different
   witness. **This task removed the cheaper of the two blockers only.**
4. **The stage is not free to choose in a consumer.** `graphFo-at-SL` lands at
   `sucV σ`, the stage the formula's own constants force. A consumer that
   needs the formula at ITS stage `α` must supply
   `⟨ fst (mkBoundedFo (LsetGraphAt w b)) ∈ α ⟩` and use
   `graphFo-at-anyStage`. **Name that side condition in the brief. Do not let
   a worker discover it.**
5. **Satisfaction was NOT transported, only the formula.**
   `Relabel.liftFo-correct` (`src/FOL/Manipulation/Bounding.lagda.md:198`)
   says `mapFo up (liftFo φ h) ≡ mapFo proj φ`. That is the equation an
   absoluteness argument meets at, and this task did not spend it. **The next
   brief that wants `⟨ γ AbsL.⊨ᵐ graphFo-at-SL w b ⟩` to say what
   `LsetGraphAt` says must order `liftFo-correct` and the `⊨-map` law, and
   that is a separate obligation.** I did not price it.
6. **Do not order `coverFo`, `code-of` or `ambient-level` again.**
   `[LJ-1.492]` forbids it (`agents/tasks/LJ-1-492/lj-1.492-report.md:337-342`)
   and `[LJ-1.494]` repeats it. This task did not touch them.

## D-10, AND WHAT IT CAUGHT

**The target was checked before it was priced, and the check changed the
task.** D-10 (`dev/LESSONS.md:1375`) asks for the truth of a recorded residue
before its proof. The recorded residue here was the brief's own guess that the
census might be empty. **It is not.** Five minutes of `countFo` refuted it,
and the refutation is what pointed at `Relabel`, because a non-empty census
makes `mapFo` inapplicable by inspection. **A task that had built the term
first would have built it along a map that cannot exist.**

## C-42, THE SWEEP

C-42 (`dev/LESSONS.md:3752`) says a refutation measures one site and never how
far the shape extends. **The shape here is "a `Formula CS.S n` that a stage
consumer needs at `SL`". The count of sites is not 1.** Every chapter that
opens `LsetGraphAt` carries it: `src/L/Hierarchy.lagda.md:62`,
`src/L/Condensation.lagda.md:51`, `src/L/Choice/Order.lagda.md:65`,
`src/L/Choice/Limit.lagda.md:56`, `src/L/Choice/Faithful.lagda.md:61`,
`src/L/Choice/Before.lagda.md:66`. **SIX chapters.** The cure delivered here
is generic in the formula, so it covers all six without re-measurement. **I
did not re-measure the cure at each of the six sites, and under the Boundary's
"a measured cure does not transfer by analogy" a consumer must still check its
own stage condition.** What transfers without re-measurement is the
instrument, not the stage bound.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **Declined, not read beyond its first
  line.** `:1` reads `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. It is
  the retired dispatch index. This task measures a live chapter and needs no
  dispatch history.
- `archive/dev/JOURNAL.md`. **Declined, not read beyond its first line.**
  `:1` reads `# ARCHIVED 2026-08-20`. The per-episode journal is retired.
- `archive/dev/JOURNAL-archived.md`. **Declined, not read beyond its first
  line.** `:1` reads `# Archived journal: the retired route`. It records the
  retired route, and the census reads today's `src/`.
- `dev/ARCHIVE.md`. **Declined, not used.** `:1` reads
  `# ARCHIVE.md: the archive registry`. No module was retired by this task, so
  clause W4 writes no row here.
- `archive/dev/DD-archived.md`. **Declined, not used.** `:1` reads
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. The `DD` series is
  set aside in that form, and no ruling of it binds this measurement.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ AND USED.** `:255` reads
  `bounded description with a bound inside the carrier exists.` and `:302`
  reads `object-level description of the Def step with its bound inside the
  carrier;`. **This is the orthodox name for what `mkBoundedFo` delivers.**
  The literature asks only that SOME bounded description with a bound inside
  the carrier exists, and it does not pin the presentation. The census plus
  `mkBoundedFo` is exactly that bound, computed rather than assumed. I did not
  stop as a literature NO-GO, and the literature agrees with the GO.
- `dev/literature/truncation-and-selection.md`. **Declined, not used.** `:1`
  reads `# Truncation and selection: how the two literatures pick a witness`.
  This task picks no witness. It relabels constants.
- `dev/literature/digest.md`. **Declined, not used.** `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected
  literature`. The rud route is not the route this tree took, and the census
  is a fact about this tree's own coding.
- `dev/literature/glossary-review-2026-08.md`. **Declined, not used.** `:1`
  reads `# Glossary review: the 119 pre-protocol entries`. This task names no
  new term and adds no glossary entry.
- `dev/literature/terms-2026-08.md`. **Declined, not used.** `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Same reason: no naming question arose.

## WHAT THIS TASK DID NOT DO

- It did not edit `src/`.
- It did not attempt `hier-in-stage`, `GraphSatAtStage` or
  `CoverWitnessesInHull`.
- It did not order `coverFo`, `code-of` or `ambient-level`.
- It did not build or postulate a total map `CS.S → SL`.
- It did not read `agents/tasks/LJ-1-498/`, which the brief says is empty.
- It did not commit and it did not push.
- It set no `GHCRTS`, and it started one Agda process per run.
