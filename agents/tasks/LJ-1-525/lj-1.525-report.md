# LJ-1.525 report: the leaf conversion, which consumes what 522 paid

**VERDICT: GO.** The obligation is written and it typechecks.
`agents/tasks/LJ-1-525/Probe525.agda:150-165`, exit 0, `runs/full-t2.out`.

    leaf-unbounds :
        (α : V ℓ) → IsLimit α
      → ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (sv b sf K : Fin m)
      → (γ : S ^ (4 + m))
      → fst (lookup (suc (suc (suc (suc K)))) γ) ≡ Lset α
      → ⟨ fst (lookup (suc zero) γ)
          ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
      → ((x c v : S) → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ ψ ⟩
                     → ⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody (suc zero) ⟩)
      → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo (suc zero) ⟩
                 → ⟨ (x ∷ γ) ⊨ leafBFo (suc (suc (suc (suc K)))) ψ ⟩)
      → ⟨ γ ⊨ StepB.leafB {m} ψ sv b sf K ⟩
      → ⟨ γ ⊨ DefAt zero (suc zero) ⟩

**W3 IS GO, ON THE FIRST RUN.** The two delivered terms meet.
`agents/tasks/LJ-1-525/runs/W3.agda:67-84`, exit 0, `runs/w3-0.out`.

**THE ONE SENTENCE FOR THE NEXT BRIEF.** The brief expected
`defPow-closed-noCode` to supply `inK` from the unbounded leaf alone. **It
cannot: its eighth argument is the recorded value's membership in `K`, and the
unbounded leaf does not carry it.** What carries it is `bwd`, the
machine-to-story direction, which `extAtB→extAt` ALREADY asks for
(`src/L/Condensation.lagda.md:2516`). **So `inK` costs this conversion no
hypothesis of its own**, and the leaf conversion is exactly as expensive as the
leaf agreement plus `bwd`.

## D-10, BEFORE ANY AGDA

The brief ordered this first and named the stop it was preparing: "Say at
`file:line` whether the unbounded leaf's `φ` is `DefBody w` or something that
reduces to it. If it is neither, name the gap and STOP."

### The unbounded leaf is neither, and that is not the gap

**IT IS TWO EXISTENTIALS OVER `DefBody`, AND THOSE TWO EXISTENTIALS ARE WHAT
BUILDS 522's ENVIRONMENT.**

- The machine's leaf is the third conjunct of `StepBody`:
  `DefAt zero (suc zero)` (`src/L/Coding/Sequence.lagda.md:116`).
- `DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))`
  (`src/L/Coding/Powerset.lagda.md:443`).
- So `extAtB→extAt`'s formula argument `φ` is `∃̇ (∃̇ (DefBody w))`
  (`src/L/Condensation.lagda.md:2514-2518`), and its `inK` argument reads that
  formula at `(x ∷ γ)`.
- Unfolding the two existentials at `(x ∷ γ)` gives `c`, then `v`, and
  `⟨ (v ∷ c ∷ x ∷ γ) ⊨ DefBody w ⟩`. That is `defPow-closed-noCode`'s ninth
  argument, at the same environment and with the same slot roles
  (`agents/tasks/LJ-1-522/Probe522.agda:356-364`, the hypothesis at `:363`).

**SO NO ADAPTER IS WRITTEN.** The two sides meet by unfolding, and the two-step
chain did not become a three-step one.

### The site, and what it agrees with

`leafB` (`src/L/Condensation.lagda.md:2398-2402`) is `extAtB` at slot zero,
bounded by the class carrier at `suc (suc (suc (suc K)))`, over THE SAME TWO
EXISTENTIALS, each bounded by `K`. The probe writes both conditions at one
frame, `leafFo` and `leafBFo` (`Probe525.agda:64-69`), so the pair of formulas
`extAtB→extAt` wants is written once and read twice.

### The gap D-10 DID find, and it is in the eighth argument

**`defPow-closed-noCode` DOES NOT RUN ON `DefBody` ALONE.** Its telescope is

    → (z c v : S)
    → ⟨ fst v ∈ fst (lookup K γ) ⟩        -- the eighth argument
    → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩

(`agents/tasks/LJ-1-522/Probe522.agda:356-364`). **The unbounded leaf binds `v`
with an UNBOUNDED existential, so nothing in `φ` says `v ∈ K`.** The bounded
leaf binds it with `∃̇∈ (var (suc (suc K)))`, so the bounded leaf says it and
the machine's leaf does not.

**THE CURE COSTS NOTHING, AND IT IS THE FINDING OF THIS TASK.**
`extAtB→extAt` takes three hypotheses, and the second is
`bwd : (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩`
(`src/L/Condensation.lagda.md:2516`). Apply `bwd` first: the bounded leaf hands
back `c ∈ K`, `v ∈ K` and the bounded body, and the ψ-level leaf agreement turns
the bounded body into `DefBody`. `Probe525.agda:79-100` is that term.

**I DID NOT STOP.** The brief's stop condition was "the two delivered terms do
not compose at this frame". They compose. The eighth argument is a real
finding about the telescope, not a refusal of the composition.

## WHAT THE PROBE BUILDS, AND WHERE EACH PIECE CAME FROM

| section | what | at |
|---|---|---|
| 1 | `leafFo`, `leafBFo`, `leaf-inK` (W3's term), `leaf-fwd` | `Probe525.agda:64-113` |
| 2 | `leaf-unbounds-gen`, the conversion at a generic carrier | `:122-136` |
| 3 | **THE OBLIGATION**, at `StepB.leafB` | `:150-165` |
| 4 | the same term at `StepAtB`'s class carrier | `:176-199` |
| 5 | `leaf-inK-valK`, the price of `inK` without `bwd`, not used | `:213-227` |
| 6 | `stepFrame` and two `refl`s: what the next link costs | `:244-259` |

**SECTION 6 IS A MEASUREMENT AND NOT A BUILD.** `StepB.bodyB`
(`src/L/Condensation.lagda.md:2404-2408`) and the machine's `StepBody`
(`src/L/Coding/Sequence.lagda.md:113-117`) are both written as ONE frame applied
to ONE leaf, and **both equations are `refl`** (`Probe525.agda:254`, `:259`).
So the other three conjuncts, the membership atom, the `appAt` application and
the payload atom, are the SAME FORMULA and not agreeing formulas. **The next
link up is one congruence over `stepFrame` and this task's conversion, and it
buys no further row.** The probe does not build it.

## WHAT THE STATEMENT COSTS, AND WHAT IT DOES NOT

**FIVE HYPOTHESES RIDE INTO THE CONCLUSION AND NONE IS HIDDEN.**

| hypothesis | who owes it | status |
|---|---|---|
| `α` with `IsLimit α` | the frame | NOT discharged, as the brief ordered |
| `fst (lookup K γ) ≡ Lset α` | the frame | NOT discharged. `K` must be a LEVEL |
| the carrier at slot one lies in `K` | the frame | bounded by `witB` one level out (`src/L/Condensation.lagda.md:2410-2415`) |
| the ψ-level leaf agreement | `LeafAgree` | DELIVERED as a module, `src/L/Condensation.lagda.md:7353-7358`, under its own telescope |
| `bwd`, the machine-to-story leaf direction | `extAtB→extAt` itself | UNDELIVERED, and it was already owed |

**`inK` IS FREE.** It adds no sixth row. That is what section 5 measures against:
`leaf-inK-valK` (`Probe525.agda:213-227`) builds the same `inK` from the
hypothesis "the recorded satisfaction set of an unbounded leaf witness lies in
`K`" instead of from `bwd`. **That hypothesis is one of [LJ-1.520]'s five open
rows** (`agents/tasks/LJ-1-522/lj-1.522-report.md:180-184`), so the `bwd` route
is strictly cheaper and the `valK` route is written only so the next brief can
compare the two telescopes. **It is not used by the obligation.**

**THE `K`-IS-A-LEVEL GAP IS STILL OPEN AND I DID NOT CLOSE IT.**
[LJ-1.522] recorded it: a `K` that is an elementary submodel of a level does not
satisfy `fst (lookup K γ) ≡ Lset α`
(`agents/tasks/LJ-1-522/lj-1.522-report.md:160-165`). This task inherits that
hypothesis unchanged and adds nothing to it. **The conversion at the collapse,
where `K` is the hull and not a level, is not this term.**

**`LeafAgree` IS TAKEN AS A FUNCTION AND NOT INSTANTIATED.** Its telescope is
one `KFacts` record plus about fifteen site facts
(`src/L/Condensation.lagda.md:7224-7305`), and it is stated at ONE environment
`γ : S ^ (8 + n)`, while the conversion needs it at every `(v ∷ c ∷ x ∷ γ)`.
**Instantiating it at the family is a real cost that this task did not pay and
does not claim.**

## THE MEASURED SPLIT: WHERE THE SECONDS ARE

**MEASURED, AND IT IS THE SECOND FINDING.** The conversion is cheap. Making it
concrete at `StepAtB`'s fourteen slot arguments is not.

| file | what it holds | median wall |
|---|---|---|
| `runs/Control525.agda` | the import list, NO term | **2.58 s** |
| `runs/NoClass.agda` | sections 1 to 3: the match, the generic conversion, the obligation | **5.05 s** |
| `runs/NoClass5.agda` | everything except section 4 | **5.54 s** |
| `Probe525.agda` | all six sections | **25.91 s** |

By subtraction, on this machine and at this caliber:

- the chapter load, which no term of mine pays for: **2.58 s**
- the obligation, the generic core and W3's term: **2.47 s**
- sections 5 and 6 together: **0.49 s**
- **section 4, the class-carrier instance: 20.37 s**

**SECTION 4 IS A PURE INSTANTIATION.** Its body is one call to the section 3
term with `zero` for `K` and `StepAtB.ψ` for the leaf content
(`Probe525.agda:196-199`), and it proves nothing new. **The fourteen concrete
`Fin (5 + n)` arguments of `DefBodyB` are what cost**, which is the tree's own
instantiation class, P-m. `archive/dev/LJ-dispatch-index.md:117` measured the
neighbour: "63 pc of the cost was module-header elaboration, not any
definition".

**WHY IT MATTERS TO THE NEXT BRIEF.** `GraphB` instantiates `StepB` TWICE, once
through `ApproxB` (`src/L/Condensation.lagda.md:2469`) and once directly
(`:2490`), at two different arities. `LevelHood` then feeds `GraphB` two
distinct `DefBodyB` leaf contents
(`src/L/BoundedSubset.lagda.md:81-105`). **So the chain up to the certificate
carries this instantiation price at least twice, and it is about seven times the
price of the mathematics it carries.** A brief that funds the chain against the
mathematics will be wrong by that factor.

## WHAT NOW CONSUMES THE CERTIFICATE

**RE-MEASURED TODAY: NOTHING IN `src/` CONSUMES EITHER CERTIFICATE, AND
[LJ-1.522]'s RECORD STILL HOLDS.** `grep -rn "Σ₁-levelHood\|Σ₁-Σ₂" src` returns
four lines and all four are the declarations themselves
(`src/L/BoundedSubset.lagda.md:145`, `:146`, `:858`, `:859`). **This task lands
nothing in `src/`, so it could not have changed that, and it did not.**

`Σ₁-levelHood` is a syntactic certificate: it says `levelHoodΣ₁` is `Σ₁`
(`src/L/BoundedSubset.lagda.md:142-146`). To SPEND it, through `σ₁-up`
(`src/FOL/Absoluteness.lagda.md:182-185`), a consumer needs the bounded formula
to MEAN level-hood. That meaning is the chain below. Each row is a transfer
between one bounded formula and the machine's formula at the same environment.

| # | bounded | machine | delivered? |
|---|---|---|---|
| 1 | `StepB.leafB`, `src/L/Condensation.lagda.md:2398` | `DefAt zero (suc zero)`, `src/L/Coding/Sequence.lagda.md:116` | **THIS TASK**, with the five hypotheses above. Nothing in `src/` |
| 2 | `StepB.bodyB`, `:2404` | `StepBody b f`, `src/L/Coding/Sequence.lagda.md:113` | NO. One `∧̇` congruence, and section 6 proves the other three conjuncts are equal ON THE NOSE |
| 3 | `StepB.witB`, `:2410` | `∃̇ (∃̇ (∃̇ (StepBody b f)))`, inside `src/L/Coding/Sequence.lagda.md:120` | NO. Three bounds to drop one way, three memberships in `K` to supply the other |
| 4 | `StepB.stepBndAt`, `:2417` | `StepAt v b f`, `src/L/Coding/Sequence.lagda.md:119-120` | NO. A SECOND `extAtB→extAt`, with its own `inK`: the STEP's value in `K`, which is a different and larger obligation than the leaf's |
| 5 | `ApproxB.approxBndAt`, `:2471` | `ApproxAt f a`, `src/L/Coding/Sequence.lagda.md:286` | NO. Two bounded universals against two unbounded ones, plus `domB` against `domAt` |
| 6 | `GraphB.graphBndAt`, `:2493` | `LsetGraphAt w b`, imported at `src/L/Condensation.lagda.md:51` | NO |
| 7 | `LevelHood.levelHoodB`, `src/L/BoundedSubset.lagda.md:108` | level-hood of the carrier | NO |

**ROW 4 IS THE ONE TO PRICE NEXT AND IT IS NOT THE CHEAP ONE.** Rows 2 and 3
are congruences and bound-dropping. Row 4 asks the same question this task
answered, one level out and about a bigger object: every satisfier of the
machine's step body lies in `K`. **A measured cure does not transfer by analogy
(`AGENTS.md:45`), so this task's answer does not settle it.** What this task
does give row 4 is the SHAPE: look first at whether the bounded direction
already carries the memberships, before buying a new frame row.

**AND ROW 4 WAS REFUTED ONCE AT A WIDER GENERALITY.**
`archive/dev/LJ-dispatch-index.md:319` records `[LJ-1.250]`: "Price StepAgree and
ApproxAgree | NEITHER BUILDS: UNCONSTRAINED INTERFACES ... Refutable at that
generality. The residue is the leaf-adequacy supply, not one term". **The
residue it named is the supply this task's row 1 still takes as a hypothesis.**
A brief for rows 4 and 5 must state the interface constraints that refutation
was missing, or it will be refuted again.

## THE PRICE

Three forced rechecks each. The file's own interface was removed before every
run, so each number is a real recheck of that file. `GHCRTS="-A64m -I0 -M8g"`,
the wide caliber, set on the pane by the program and untouched. ONE Agda process
per run.

| file | median wall | peak RSS | runs |
|---|---|---|---|
| `runs/W3.agda` alone | **1.95 s** | **401,457,152 B** | `runs/w3-t1.time`, `w3-t2.time`, `w3-t3.time` |
| `runs/Control525.agda` | **2.58 s** | **597,901,312 B** | `runs/ctl-t1.time`, `ctl-t2.time`, `ctl-t3.time` |
| `runs/NoClass.agda` | **5.05 s** | **604,127,232 B** | `runs/noclass-t1.time`, `noclass-t2.time`, `noclass-t3.time` |
| `runs/NoClass5.agda` | **5.54 s** | **661,880,832 B** | `runs/noclass5-t1.time`, `noclass5-t2.time`, `noclass5-t3.time` |
| `Probe525.agda`, full | **25.91 s** | **811,827,200 B** | `runs/full-t1.time`, `full-t2.time`, `full-t3.time` |

All fifteen exited 0.

**SIZE.** `Probe525.agda` is 259 lines, of which 142 are non-blank and not a
comment. `runs/W3.agda` is 84 lines, of which 41 are non-blank and not a comment.

**AGAINST THE BRIEF'S ESTIMATE.**

| item | brief | measured |
|---|---|---|
| W3 | about 20 lines, under 35 s | 41 lines, 1.95 s |
| the probe | about 150 lines | 142 lines |
| the obligation | about 35 lines | 16 lines (`:150-165`) |

**THE LINE ESTIMATE WAS RIGHT AND THE TIME ESTIMATE WAS HIGH.** W3 came in far
under its time estimate, 1.95 s against 35 s, because it matches two signatures
and proves nothing, exactly as the brief said. The probe came in UNDER its line estimate,
because the brief priced a rebuilt frame and no frame had to be rebuilt: the
site is imported from `src/L/Condensation.lagda.md` and used as it stands.

**NO WALL EVENT.** No heap exhaustion, no rerun after a wall. Peak RSS is
811,827,200 B against an 8 GB cap, about one tenth of it.

**ONE FIRST-RUN ERROR, AND IT WAS SCOPE AND NOT MATHEMATICS.** `_+_` was not
imported (`runs/full-0.out`, exit 42, `[NotInScope]`). One import line fixed it.
No unsolved meta and no universe-level error at any point.

## W2, ANSWERED

**W2 IS MET.** The mathematics is written ONCE, at a generic carrier, and
instantiated twice.

- `leaf-unbounds-gen` (`Probe525.agda:122-136`) takes `∀ {n}` with `y`, `K` and
  `w` as generic slots and `ψB` as a generic formula. It mentions no arity, no
  stage and no concrete slot.
- Section 3's obligation is that term with `y := zero` and
  `K := suc (suc (suc (suc K)))` (`:163-165`).
- Section 4 is section 3's term with `K := zero` and `ψ := StepAtB.ψ`
  (`:196-199`).

**Neither instance adds a line of content**, and the split measurement above
proves the second one adds nothing but seconds. **A deadline did not force the
fixed form and no conflict arose**, so there is nothing to report under W2's
second clause.

**W4, ANSWERED: NOTHING IS RETIRED BY THIS TASK.** It lands nothing in `src/`
and it removes no module, so no `dev/ARCHIVE.md` row is owed. **It creates no
duplication either**: `runs/NoClass.agda` and `runs/NoClass5.agda` are cut-down
copies of `Probe525.agda` written for the split measurement, they carry a header
that says exactly that, and they are measurement fixtures rather than a second
home for the term.

## WHAT I DID NOT DO

- **I did not consume either `Σ₁` certificate.** `Probe525.agda:24-41` is the
  whole import list and `L.BoundedSubset` is not in it. The brief reserved that
  for the next task and this task does not reach it.
- **I did not rebuild the graded formula, the seam or `defPow-closed`.**
  [LJ-1.520], [LJ-1.516] and [LJ-1.522] delivered them, and the last is
  IMPORTED rather than restated (`Probe525.agda:35`), so the obligation consumes
  the term that typechecked and not a copy of it.
- **I did not build the row-2 congruence.** Section 6 prices it with two `refl`s
  and stops there.
- **I did not instantiate `LeafAgree`.** Its telescope is taken as a function
  hypothesis and its own supply is not this task's.
- **I did not postulate.** The probe and all four run files carry `--safe`
  (`Probe525.agda:1`).
- **I did not commit and I did not push.** The working tree holds
  `agents/tasks/LJ-1-525/` and nothing else.

**ONE THING I COULD NOT RUN AS THE RULE WRITES IT.** `AGENTS.md` says to run
every `python3` command as `.venv/bin/python`. **This worktree has no `.venv`**,
and `make venv` would install into it. The two gates that bear on a probe read
only the standard library (`scripts/gate/check-probes.py:46-51`,
`scripts/gate/lint-agda.py:45-49`), so I ran both with the system `python3` and
both are clean: `check-probes: clean (5561 tracked files, no probe outside
agents/tasks/ and no generated file)`, and `lint-agda --check` exit 0. **I did
not run `make check`**, because it typechecks `src/Everything.lagda.md` and I
commit nothing.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ, AND IT SET THE SHAPE OF TWO
  SECTIONS.** `archive/dev/LJ-dispatch-index.md:319`:

  > | LJ-1.250 | Price StepAgree and ApproxAgree | NEITHER BUILDS: UNCONSTRAINED INTERFACES. DD25 [LJ-1.251] | Refutable at that generality. The residue is the leaf-adequacy supply, not one term |

  This is rows 4 and 5 of my certificate table, already refuted once, and it is
  why that table names the interface constraints rather than only the types.
  Also `:108`:

  > | LJ-1.57 | The shapedness walk, WitnessAgree, LeafAgree | ALL THREE BUILT | The leaf adequacy is proved both ways against the machine's DefBody. No fifth defect. levelIn and cover still survive |

  This told me `LeafAgree` exists BEFORE I wrote a leaf agreement of my own, so
  the probe hypothesizes the delivered module instead of restating it. And
  `:117`, quoted in the split-measurement section, is the neighbour measurement
  for the instantiation price.

- **`dev/ARCHIVE.md`: READ, ONE ROW, AND IT DOES NOT TOUCH THIS SITE.**
  `dev/ARCHIVE.md:285` begins:

  > | `L.Condensation` (partial, 86 lines cut in place) | `src/L/Condensation.lagda.md`, the Crossing section and its two imports | The Crossing section stated the ambient-reading form of `Lset-only` at the class carrier. It

  I read it to check whether the leaf conversion had been cut from
  `L.Condensation` before and was waiting in the archive. **It was not.** The
  cut is the Crossing section and the ambient form of `Lset-only`, which is a
  different statement about a different object. Nothing to revive here.

- **`archive/dev/JOURNAL.md`: READ, ONE LINE, AND IT CONFIRMED A NEGATIVE.**
  `archive/dev/JOURNAL.md:1045`:

  > and the leaf supply share no word, and that is exactly why the cross-read has

  I grepped this file for `leafB`, `extAtB→extAt` and `DefAt` and it carries no
  record of this conversion, only of the leaf SUPPLY. That is the negative I
  needed: the conversion has not been attempted and abandoned.

- **`archive/dev/JOURNAL-archived.md`: READ, ONE LINE, AND IT IS THE RETIRED
  ROUTE.** `archive/dev/JOURNAL-archived.md:732`:

  > revival is to be kept alive: a D-1 probe of the Σ₁ rewriting of one DefAt

  A `Σ₁` rewriting of `DefAt` is the neighbourhood of my certificate table, but
  it is the pre-`[LJ-1.90]` route and it names no term this tree carries.
  **Not used.**

- **`archive/dev/DD-archived.md`: NOT USED, DECLINED.** I grepped it for `leaf`,
  `extAtB` and `bounded restatement` and every hit is a process row: DD0, DD8,
  DD17, DD18 and DD24, about how a task is ruled, dispatched and measured. **The
  `DD` series is set aside in this form by amendment A7**, and this task adds no
  ruling and proposes none. Declined.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`: READ, ONE LINE, AND IT
  LICENSES THE WHOLE PROOF SHAPE.** `dev/literature/truncation-and-selection.md:143`:

  > the reason: "a proposition-valued goal absorbs the truncation"

  Every existential in both leaf formulas arrives as `∥ … ∥₁`, and the
  conclusion `⟨ fst x ∈ fst (lookup K γ) ⟩` is an `hProp`. **So `PT.rec` into
  the goal is legal and NO SELECTION IS NEEDED**, which is why
  `Probe525.agda:89-96` picks no witness and adds no classical step. This file
  is the record that the condition holds rather than that it was assumed.

- **`dev/literature/devlin-II5.md`: READ, ONE LINE, AS A CHECK ON THE CERTIFICATE
  TABLE.** `dev/literature/devlin-II5.md:103`:

  > statement "∃v∃z φ(z, v, γ)" is transferred from L_α to X (Σ₁-elementarity,

  This is what SPENDING `Σ₁-levelHood` looks like in the source, and it is why
  my table asks what the bounded formula MEANS rather than only whether the
  certificate exists. It is an after-the-fact check on the table's shape and no
  Agda in this task depends on it.

- **`dev/literature/level-formula-slot-roles.md`: READ, ONE ROW, AND IT SUPPORTS
  THE HYPOTHESIS THAT DID NOT CLOSE.** `dev/literature/level-formula-slot-roles.md:29`:

  > | 7 | Jech 13.13 | A Π₂ SENTENCE `σ`: `(M,∈) ⊨ σ` iff `M = L_δ` for a limit `δ` | **0** | everything | nothing | level-hood is a property of the CARRIER | `_build/literature/jech13.txt:605-614` |

  Level-hood is a property of the carrier, which is exactly why
  `fst (lookup K γ) ≡ Lset α` stays a frame hypothesis in my type and cannot
  become a conjunct of the leaf.

- **`dev/literature/digest.md`: NOT READ, DECLINED.** It is the cross-source
  digest of the orthodox route. The three files above answered every question
  this task put to the literature, and this task states no new mathematics: it
  composes two terms the tree already carries.

- **`dev/literature/geology.md`: NOT READ, DECLINED.** Set-theoretic geology is
  not on this task's path, and nothing in the leaf, the step or the certificate
  chain touches it.

## FOR THE NEXT BRIEF

1. **DO NOT ASK FOR `inK` SEPARATELY AGAIN.** At a frame where `bwd` is owed
   anyway, `inK` is free. Ask instead for `bwd`, which is the real open
   hypothesis, and name `LeafAgree` as the ψ-level supply.
2. **ROW 2 IS THE CHEAPEST NEXT LINK AND IT IS ONE CONGRUENCE.** Section 6
   proves the two bodies are one frame around two leaves, both by `refl`
   (`Probe525.agda:250-259`). `bodyB` against `StepBody` should cost a few lines.
3. **ROW 4 IS THE NEXT REAL OBLIGATION AND IT WAS REFUTED ONCE.** A second
   `extAtB→extAt`, at `stepBndAt` against `StepAt`, with an `inK` about the
   step's value rather than the leaf's. `[LJ-1.250]` refuted it at an
   unconstrained generality (`archive/dev/LJ-dispatch-index.md:319`). Price it
   with the interface constraints stated.
4. **FUND THE INSTANTIATION SEPARATELY FROM THE MATHEMATICS.** Section 4 is 20.37
   s of a 25.91 s file and proves nothing. The chain to the certificate carries
   that price at least twice.
5. **SETTLE `K` BEFORE ROW 6.** [LJ-1.522] left it and this task inherits it: the
   conversion holds for `K` a LEVEL. At the collapse `K` is a hull. Either the
   chain is run at the level and transported, or every row of the table has to be
   re-derived through the collapse.
