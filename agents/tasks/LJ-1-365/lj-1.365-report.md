# LJ-1.365 report: does a `PT.rec` at the use site dissolve the last untruncation?

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe. It lands nothing.
Written incrementally (C-22). No commit, no push. `src/` untouched.

## RETURN

**SET-MOTIVE.**

**The outermost wrap TYPES. The body cannot exist. Between the trophy's
conclusion and the band, the chain crosses data goals, and the first one is a
SET. `[LJ-1.301]`'s sentence is refuted in its premise: no delivered use site
consumes the law under a propositional motive. The last untruncation does not
dissolve. It survives unchanged, and this probe named its type at three
sites.**

## 1. WHAT WAS MEASURED

### 1.1 The top wrap, GREEN at the real conclusion type

`wrap-top`, `agents/tasks/LJ-1-365/ProbeLJ1365A.agda:116-121`, exit 0:

```agda
wrap-top : (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
         → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
         → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
         → (body : sq (fst κ) → Concl zf κ oκ cκ κ∉ω)
         → ∥ sq (fst κ) ∥₁ → Concl zf κ oκ cκ κ∉ω
wrap-top zf κ oκ cκ κ∉ω body = PT.rec squash₁ body
```

`Concl` is the trophy's conclusion at κ, spelled by hand from
`src/L/GCH.lagda.md:60-69`. `statement-fits` at `ProbeLJ1365A.agda:95-99`
applies the delivered `GCHStatement` to it, so the spelling is machine-checked
against the statement. So the OUTER elimination is free, exactly as
`[LJ-1.301]` hoped. **The conclusion at κ is a proposition, and ONE `PT.rec`
over `∥ sq κ ∥₁` types there.** That green is the last good news in the chain.

The stale citation is corrected, MEASURED: the conclusion lives at
`src/L/GCH.lagda.md:65-68` (the truncation opens at `:65`, closes at `:68`).
The file is 69 lines long. `[LJ-1.301]` cited `:85-87`. `[LJ-1.323]`'s
restatement moved it, as the brief said.

### 1.2 The body's first data goal, and Agda's own refusal

The conclusion's truncation is witnessed with injection DATA. The witness
`F` of `InjL (𝒫 κ) δ` is a set plus a code, and the delivered supplier is the
injection `⟪ Lset α ⟫ ↪ ⟪ α ⟫` (`stage-card-upper`,
`src/L/StageCardinal.lagda.md:564-566`, consumed at
`src/L/BoundedSubset.lagda.md:1513`). The same wrap at that goal REFUSES.
CONTROL 2, `agents/tasks/LJ-1-365/SoloC2.agda:24-27`, exit 42, MEASURED:

```text
error: [UnequalTerms]
(Σ (⟪ Lset α ⟫ → ⟪ α ⟫)
 (λ f → (x y : ⟪ Lset α ⟫) → f x ≡ f y → x ≡ y))
!=< ∥ _A_21 ∥₁
when checking that the expression squash₁ has type
isProp (⟪ Lset α ⟫ ↪ ⟪ α ⟫)
```

**That is the intermediate goal the brief asked for, with Agda's own type.**
The goal is not a proposition. It IS a set: `inj-set`,
`ProbeLJ1365A.agda:160-163`, exit 0, green, re-derives
`isSet (⟪ Lset α ⟫ ↪ ⟪ α ⟫)` at this session's own hand.

### 1.3 The per-use wrap, at the counting's own use, REFUSED

`[LJ-1.301]` said "ONE `PT.rec` per use". The law's actual use inside the
counting is a function application: `Bound` takes `sq α` as its `pairing`
parameter (`src/L/StageCardinal.lagda.md:283`) and pairs through its first
component (`pair x y = fst pairing (x , y)`, `:72-73`). CONTROL 1,
`agents/tasks/LJ-1-365/ProbeLJ1365C.agda:73-75`, exit 42, MEASURED:

```text
error: [UnequalTerms]
... !=< ∥ _A_19 ∥₁
when checking that the expression squash₁ has type isProp ⟪ β ⟫
```

The use's goal is a VALUE of `⟪ β ⟫`. It is not a proposition. A per-use wrap
needs `isProp ⟪ β ⟫`, and that statement is false. MEASURED, by the refusal.

### 1.4 The delivered consumer, fed the truncated band, REFUSED end to end

CONTROL 3, `agents/tasks/LJ-1-365/SoloC3.agda:30-32`, exit 42, MEASURED:

```text
error: [UnequalTerms]
∥ sq δ ∥₁ !=<
(Σ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
 (λ f → (x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
when checking that the expression t has type
LJ-1-337.ProbeLJ1337B.LimitBand lem
```

This composes the two delivered legs (`[LJ-1.332]`'s truncated band,
`[LJ-1.337]` probe D's consumer) and lets the machine print the whole
distance. It is the error `[LJ-1.337]`'s control B3 printed at the band,
reached now from the TROPHY's own body side. `bandT-from-332`
(`ProbeLJ1365A.agda:200-202`, green) checks by machine that the truncated
band I spelled is exactly the shape `[LJ-1.332]` delivers.

## 2. WHY THE WRAP CANNOT DISSOLVE THE DEBT

Three facts, all measured above, close the question together.

1. The outer motive is propositional, so the outer elimination is free
   (section 1.1).
2. The body needs the FAMILY below the stage, not the point at κ.
   `point-is-not-family` (`ProbeLJ1365A.agda:136-138`, green) restates
   `[LJ-1.332]`'s `lead-hypothesis-is-goal` against the delivered `SqBelow`:
   the family at `sucV α` yields `sq α`, and the point at κ funds one member
   only. `[LJ-1.333]` measured the same thing one level down: the consumer's
   step eats its hypothesis as a Pi-indexed family of injections
   (`agents/tasks/LJ-1-333/lj-1.333-report.md:16`).
3. Inside that family the law is consumed at data goals (sections 1.2, 1.3),
   and the family's own supplier is truncated at the band (section 1.4).

So the top wrap shifts nothing. The truncation still meets a data goal at the
first point of contact, and the eliminator refuses there.

## 3. WHAT `[LJ-1.332]`'s UNTRUNCATION BECOMES

It becomes the SAME one untruncation, not a new one, and C-54 now states its
exact price at the named goal. `c54-at-injection`
(`ProbeLJ1365A.agda:175-178`, green) states the shape:

```agda
c54-at-injection : (α : V ℓ) (f : sq α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫)
                 → 2-Constant f
                 → ∥ sq α ∥₁ → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
```

The set eliminator serves the data goal IF a `2-Constant` map from the law to
the injection exists. `sq α` is a set (re-derived at `ProbeLJ1365A.agda:154-156`,
green; `[LJ-1.319]`'s `SqIsSet.agda` re-run green this session). By
`trunc→Set≃` the 2-Constant condition is necessary too. **No such map is
built here and none is assumed.**

The delivered chain's real gate is the band site (section 1.4), and its
2-Constant price is already measured: `[LJ-1.333]` found the band is the
exact complement of the tree's only canonicalizer, and five failed attempts
were not unlucky (`agents/tasks/LJ-1-333/lj-1.333-report.md:337` and
section 3.2). **So the wrap changes the debt's ADDRESS and not its PRICE.**
The debt stays one uniform obligation, payable three ways, none free:

- the untruncation at the band, as before;
- a `2-Constant` family, C-54's door, measured hard at the band;
- a choice principle at an injection type (`ACBranch`,
  `[LJ-1.333]` `ProbeLJ1333A.agda:109-119`), stated by that task, never
  assumed, INFERRED here as the third door from its green statement.

C-36 binds this section: I measured the delivered chain's sites. I did not
measure every possible assembly.

## 4. THE RUNS, AND THE NEGATIVE CONTROL

Every run: ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no
heap exhaustion. Slots counted before every invocation with the brief's
command. The count read ONE before every run (another agent's process held
the other slot for part of the session). The cap is TWO, so I never waited.
Empty-file floor, `Floor365.agda`: **0.09 s**.

| run | file | exit | real s | slots before |
|---|---|---:|---:|---:|
| floor | `Floor365.agda` | 0 | 0.09 | 1 |
| re-run, C-44 | `LJ-1-332/ProbeLJ1332A.agda` | **0** | 1.94 | 1 |
| re-run, C-44 | `LJ-1-337/ProbeLJ1337B.agda` | **0** | 2.01 | 1 |
| re-run, C-54 | `LJ-1-319/SqIsSet.agda` | **0** | 1.34 | 1 |
| probe, GREEN | `ProbeLJ1365A.agda` | **0** | 1.89 | 1 |
| control 1 | `ProbeLJ1365C.agda` | 42 | 1.72 | 1 |
| control 2 | `SoloC2.agda` | 42 | 1.72 | 1 |
| control 3 | `SoloC3.agda` | 42 | 1.78 | 1 |

All figures are warm on `src/` and on the sibling probes' interfaces. They
price the marginal check, not a cold build (P-l).

**The negative control, and it measures.** Control 2 is the non-vacuity
control for section 1.1: the SAME `PT.rec`, the SAME `squash₁`, at the goal
one level below the conclusion, refused with the type in section 1.2. The
green of the top wrap is exactly as wide as the conclusion's truncation, and
the control draws the boundary.

## 5. DID `[LJ-1.323]`'s DROP OF `sq` CHANGE THE QUESTION?

It changed the question's STATUS, and made it easier to answer. It did not
change the mechanism.

Before the drop, `sq` sat in the statement's telescope, and the wrap question
was a question for the OWNER: may the hypothesis be restated truncated?
`[LJ-1.301]` said so itself, at
`agents/tasks/LJ-1-301/lj-1.301-report.md:162-163`: the restatement "is the
OWNER's ruling, not mine".

After the drop (`dev/PLAN.md:1259`, Fable ruling: "sq leaves, every ambient
injection leaves"), no ruling is needed. The truncated band is a proof
INTERNAL artifact, and the question became mechanical: does the body assemble
or not. This probe answered it by machine in four seconds.

The body's data demand is unchanged, because the proof must now CONSTRUCT
what the telescope used to assume. The drop did not make the debt cheaper. It
removed the last way to pay it by rewording the statement.

## 6. ARCHIVE USED (DD18)

The four corpora, each named in one line, with a real quote per file read.

- **`archive/src/2026-08-09-rud-route/`**: READ and it BEARS, at two files.
  The retired route faced this exact question and its own prose answers it.
  `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md:134`: "truncation,
  and a truncated witness cannot supply a function." The counting's call site
  goal is printed at `:129-134` with the law's own Σ type, named
  NOT proposition-valued. `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:955`:
  "the truncated square law ∥ sq α ∥₁ as its projection. It does not give the".
  The retired route's cure was a SUPPLIER change, not an eliminator change:
  the honest pairing bound at every INITIAL ordinal, with the truncated law
  only as its projection, and no honest law ever needed at non-initial sites.
- **`archive/dev/JOURNAL-archived.md`**: READ and it BEARS.
  `archive/dev/JOURNAL-archived.md:1697`: "NOT proposition-valued: its first
  component is a function, so a truncated equinumerosity cannot". T46 measured
  the same tension T43's survey raised, and T47's D-10 record resolved it by
  delivering the honest bound. `[LJ-1.301]` is T43's role; `[LJ-1.333]` is
  T46's; this probe is T47's check, at the trophy level.
- **`archive/dev/DECISIONS-archived.md`**: NOT read. WHY NOT: `grep -n
  "truncat"` returns nothing in it, so no truncation policy ruling exists
  there, MEASURED by the empty grep.
- **`archive/dev/TASKS-archived.md`**: READ and it BEARS.
  `archive/dev/TASKS-archived.md:78`: "| L3.32-T43 | Where counting calls the square law | RED (wall confirmed) |". The
  retired route's square-law dispatch table confirms the wall was confirmed
  there too, at the counting site.

**The route-level finding.** Two routes, one shape. Both routes' square-law
consumers demand the law's first component as a FUNCTION at a data goal, and
both routes' surveys once claimed the consumers were proposition-valued. The
retired route paid by changing the supplier: honest data at initial ordinals,
never demanded at non-initial ones. The live route's band is at non-initial
limits precisely because its family is consumed at EVERY infinite ordinal
below the stage. **One obstruction, `∥ sq δ ∥₁ !=< Σ (...)`, now explains
`[LJ-1.333]`'s five failures and `[LJ-1.301]`'s false hope, and the archive
says the honest cure it knows is a supplier change, INFERRED from the
retired route's shape, not measured on the live route.**

## 7. LITERATURE USED (DD18)

`dev/literature/truncation-and-selection.md`, READ and it BEARS.

The HoTT Book's treatment gives reason to expect the FINAL motive is
propositional and NO reason to expect the intermediate injection-typed goals
are. Definition 10.2.7 states cardinal inequality as a truncation, so "a proof
that only needs cardinal arithmetic never needs an injection as data" (digest
section 1.5). But the documented route out of a truncation (the paragraph
after Corollary 3.9.2, digest section 2.2) requires a predicate `Q` that makes
`Σ(x:B) Q(x)` a proposition. `Q` is leastness, and leastness is exactly what
`[LJ-1.333]` measured the band cannot have: the tree's only canonicalizer is
the complement of the band. The digest's practical rule (section 2.5) is
C-54's own statement, and this probe is that rule applied at the trophy.

## 8. DD4

**Axis named** (C-46, fixed at `scripts/measure/ledger.py:50`): the AC
closure against the GCH closure. There is no GCH endpoint in `src/` yet, so
every figure here sits on the proxy axis, as every DD4 figure to date does.

**The wrap is class-free.** Every term in this probe is stated at a concrete
stage or at the generic law. No term mentions `L` as a class, and no
consumer under `src/` was edited: the diff to `src/` is EMPTY, MEASURED by
`git status`. The wrap adds ONE eliminator outside the body and forces no
consumer edit, so `[LJ-1.337]`'s empty consumer diff is preserved. The
shared code between the two proofs is untouched by the finding: the finding
is that the shared shape (`Bound`'s pairing) is where the truncation bites
for ANY consumer with a truncated conclusion.

## 9. WHAT I DID NOT DO

I did not build a `2-Constant` map, and I claim none cannot exist (C-36). I
did not price the supplier-change cure on the live route; the archive bears
on it but nobody has measured it here. I did not touch `src/`, other tasks'
directories, or the three EXPECTED RED files named in the brief.

## 10. FILES

- `agents/tasks/LJ-1-365/ProbeLJ1365A.agda` GREEN, the measurement.
- `agents/tasks/LJ-1-365/ProbeLJ1365C.agda` EXPECTED RED, control 1, with all
  three refusals recorded in its header.
- `agents/tasks/LJ-1-365/SoloC2.agda` EXPECTED RED, control 2 solo.
- `agents/tasks/LJ-1-365/SoloC3.agda` EXPECTED RED, control 3 solo.
- `agents/tasks/LJ-1-365/Floor365.agda` GREEN, the empty-file floor.
