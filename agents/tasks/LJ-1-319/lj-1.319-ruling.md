# LJ-1.319 ruling: no new principle, no fork, open the door

Delegated ruling. The owner's authorization is dated 2026-08-15 and is
scoped to this one set of rulings. The three legs are `[LJ-1.305]` (probe),
`[LJ-1.314]` (adversarial review), `[LJ-1.316]` (literature). All three
reports were read whole. ASD-STE100. Every negative is MEASURED or
INFERRED, in those words.

## 0. THE DECISION

**The project admits NO new principle today, does NOT take the
cardinal-face fork, and OPENS the door the literature found: one funded
probe on the `2-Constant` obligation at J1. The free repair lands now. The
digest lands now, under its proposed name.**

DD4 is stated and answered in section 5, as every return must.

## 1. WHAT THIS RULING MEASURED ITSELF

The brief ordered me to verify the door myself. I did, and I added one
measurement no leg had.

1. **The door exists in the library, at the cited lines. VERIFIED by
reading.** `rec→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥₁ → B` sits
inside `module SetElim (Bset : isSet B)` at
`Cubical/HITs/PropositionalTruncation/Properties.agda:181-190` of the
installed cubical library, exported at `:268`. `trunc→Set≃ : (∥ A ∥₁ → B)
≃ Σ (A → B) 2-Constant` is at `:225`. `elim→Set` is at `:270-274`.
`2-Constant f = ∀ x y → f x ≡ f y` is at
`Cubical/Foundations/Function.agda:106-107`.
2. **The door's precondition is now MEASURED, not INFERRED.**
`[LJ-1.316]` section 2.5 left "`sq α` is a set" untypechecked. My probe
`agents/tasks/LJ-1-319/SqIsSet.agda` proves
`sq-set : (α : V ℓ) → isSet (sq α)`. Green, exit 0, 2.01 s, 1-minute load
5.89, dependencies warm, 0 agda slots in use before the run, cap never
raised. The term routes `presentation`
(`Cubical/HITs/CumulativeHierarchy/Properties.agda:268`) through
`setIsSet` and the hLevel combinators.
3. **Consequence, exact.** By `trunc→Set≃` at a set motive, the maps
`∥ Wat α ∥₁ → sq α` ARE the `2-Constant` maps `Wat α → sq α`. So J1's
obligation is exactly one question: build a witness-independent pairing
from a witness. `[LJ-1.305]`'s J1 sentence "`PT.rec` demands a
propositional motive" (`agents/tasks/LJ-1-305/lj-1.305-report.md:112-114`)
measured the wrong eliminator. Its necessity claim at the eliminator level
does not stand against the library.
4. **The review's repair term re-runs green under my own hand.**
`agents/tasks/LJ-1-314/CodeUntrunc.agda`: exit 0, 2.26 s, 1-minute load
5.60, 0 slots before. My grep confirms `InjData` has zero occurrences in
`src/` (MEASURED, `grep -rn "InjData" src/`).
5. **The quoted sources check out where they bear.** The Jech guard is
verbatim at `_build/literature/jech13.txt:744-753`. The Devlin least-witness
device is at `dev/literature/devlin-II5.md:127-131` and `:259-264`. The
consumer shapes are at `src/L/StageCardinal.lagda.md:17-19` and
`src/L/BoundedSubset.lagda.md:1388-1390`, read by me. `SqShape` and the
truncated trophy conclusion are at `src/L/GCH.lagda.md:44-47` and `:84-86`,
read by me.

## 2. THE THREE OPTIONS, RULED

### 2.1 The new principle: REFUSED today

`InjData` (`agents/tasks/LJ-1-305/Untruncated.agda:114-115`) is not
admitted to any telescope. Five reasons.

1. **Its necessity has no measurement left.** The probe's necessity claim
rested on `PT.rec` alone. Section 1 shows the library eliminates into sets,
and `sq α` is a set, MEASURED. The right obligation was never attempted.
The project does not buy an axiom-grade parameter while a delivered
eliminator is untried (D-1: verify the load-bearing assumption cheaply
before hard-to-reverse work; a telescope parameter is hard to reverse).
2. **A term-level proof of necessity can never arrive.** INFERRED: an
ambient model with choice satisfies the branch context and `sq α`
together, so no in-theory term refutes the door. The choice between
principle and construction is economic, and the economics say to try the
delivered eliminator first.
3. **The principle is expensive.** INFERRED, `[LJ-1.314]` section 4.1:
iterating `InjData` injects every countable ordinal into a power of ω
uniformly, which fails under determinacy, so it is strictly stronger than
`lem` in consequence. It is pointwise split support (Kraus, Escardó,
Coquand, Altenkirch, LMCS 13(1) 2017, equation (29), Theorem 16), a
set-theoretic commitment, not book-keeping.
4. **The residue it papers over is already a recorded fork.** MEASURED by
`bridge→data` (`agents/tasks/LJ-1-314/CodeUntrunc.agda:150-155`, green
twice): a stage-bounded ambient-to-code bridge discharges the same atom
with no principle, and the crossing is the independent fork the plan
already carries (`dev/PLAN.md:423-426`). One debt must not be recorded
twice under two names.
5. **DD4 points the same way.** Section 5.

### 2.2 The cardinal-face fork: REFUSED as a cure for this question

The fork does not solve the problem it would be taken for.

1. **MEASURED** (`[LJ-1.314]` section 2.2, sites verified by me): the two
delivered consumers take the square law at EVERY `δ` below the site,
`src/L/StageCardinal.lagda.md:17-19` as a module parameter and
`src/L/BoundedSubset.lagda.md:1388-1390` used at `:1397` and `:1410`. Most
such `δ` are not cardinals and not ambient-initial. So `sq-initial`
(`agents/tasks/LJ-1-305/Untruncated.agda:280-282`), whose face is ambient
`IsCardinal`, supplies neither consumer. The ambient face buys nothing
toward `SqShape`. MEASURED.
2. The real face fork, `IsCardinalL` against `IsCardinal` at κ in
`GCHStatement`, is a statement-level fork and it is already on the owner's
list (`dev/PLAN.md:410-431`). It is structurally the owner's. This ruling
does not need it decided: the J1 obligation has the same shape at either
face.

### 2.3 The door: OPENED, one funded file

The orchestrator funds ONE probe task. Its question, stated exactly:

> **Inside the non-initial branch of the descent, is there a `2-Constant`
> map `Wat α → sq α`?**

By section 1 this is necessary and sufficient for J1, so the probe settles
the eliminator question for good on the positive side. On the negative
side it prices the wall; it cannot refute the door outright (section 2.1
reason 2). The brief must carry:

1. **The premise, MEASURED:** `sq-set` green
(`agents/tasks/LJ-1-319/SqIsSet.agda`), and `trunc→Set≃` at `:225`.
2. **The discharge attempt.** Normalize the member half by `leastOf`, the
delivered `LeastCardInjL` pattern (`src/L/Cardinal.lagda.md:116-134`).
The residue is a canonical injection `⟪ α ⟫ ↪ ⟪ κ ⟫` built from ordinal
structure, not extracted from the witness. The classical content is the
choice-free ZF fact that an infinite ordinal and its cardinal are
equinumerous. The probe measures whether the tree's ordinal machinery
builds it, and names the wall if it walls. The literature warns that the
well-orders alone do not give it (`[LJ-1.316]` section 2.4, the `ω · 2`
example), so the expected hard case is the limit non-initial ordinal.
3. **The refutation attempt, cheap.** Adapt `NotProp`'s `swap` machinery
to two witnesses of `Wat α` and measure whether the naive step map, the
`sq-transport` composite, violates `2-Constant`. INFERRED today: it does,
because two injections that differ by a transposition give two different
composites. A refuted naive map narrows the search; it does not close the
door.
4. **The coded composite, about 20 lines.** Build
`BoundedToCode → InjData` to finish `[LJ-1.314]` section 1.4's INFERRED
join, so the coded route's record is complete whatever the door does.
5. **DD4 stated, ARCHIVE and LITERATURE sections (DD18), tier per
`dispatch_policy.py`.**

## 3. THE TWO SIDE DECISIONS

### 3.1 The free repair: LAND IT

Land the untruncation of `δ-inj` at `src/L/Cardinal.lagda.md:256-258`.
The term is `agents/tasks/LJ-1-314/CodeUntrunc.agda:64-104`: `untruncAt`,
`isPropInjCode`, `codeData`, about 30 non-blank lines, basis my count of
that region. It is additive, it needs `lem` and `orderAt` only, both
already in the telescope, and it is green twice (the review's run and
mine). It corrects the debt record: the three cited sites are TWO debts,
and `:256` is not one. The `κ-inj` site at `:132-134` stays a debt, with
its comment.

### 3.2 The digest: LAND IT, name unchanged

`agents/tasks/LJ-1-316/truncation-and-selection.md` lands as
`dev/literature/truncation-and-selection.md`. The name fits the
directory's topic-name convention (`fine-structure.md`,
`rudimentary-functions.md`). The file says it is written to land
unchanged, and my spot-checks at the load-bearing lines (section 1.5)
found no defect. The orchestrator adds the new sources to
`dev/literature/BIBLIOGRAPHY.md`: Kraus, Escardó, Coquand, Altenkirch
arXiv:1610.03346; Matthews and Rathjen arXiv:2206.08283; Escardó's
lecture notes section "Exiting truncations"; the HoTT Book source files
used.

## 4. THE HALF THAT GOES TO THE OWNER, PLAINLY

Two questions change what a trophy statement says, so they are the
owner's, not mine. Neither is urgent before the funded probe reports.

1. **The κ-face fork**, already queued at `dev/PLAN.md:410-431`.
2. **NEW, from the literature leg: the data demand in `SqShape` is the
project's own choice.** The classical conclusion at this step is a
cardinal equation, and a cardinal inequality is a truncated existence of
an injection by HoTT Book Definition 10.2.7. `GCHStatement`'s own
conclusion is already truncated (`src/L/GCH.lagda.md:84-86`), while its
one remaining hypothesis `sq : SqShape` (`:80`) demands data. If the
funded probe walls and the owner declines the crossing, the cheapest
mathematical exit is to re-spell the hypothesis in the classical truncated
shape and re-plumb the two consumers under propositional final motives.
That edit changes the trophy statement's text. I flag it with its
evidence and rule nothing on it.

## 5. DD4, STATED AND ANSWERED (the coupling, weighed)

DD4: maximize the code the two proofs share, and write it generic. The
coupling the review found is real and it CUTS AGAINST the principle, not
for it. Today every import the descent adds is GCH-only, MEASURED
(`[LJ-1.314]` section 4.2 table on `ledger.py`'s own closures). When DD4's
goal is met for this descent, the descent moves into the SHARED part, and
a module-parameter `InjData` would then sit in the AC trophy's own
telescope: a choice-shaped assumption in the type of the theorem whose
point is that choice is proved. The door and the coded route carry no such
parameter, and the coded route runs on `L.Choice.Step`'s selection
machinery, which is already SHARED. So honouring DD4 makes the refusal of
the principle MORE right, and the funded probe's deliverable, a canonical
witness-free construction, is tower-blind and generic by construction.
The probe's brief states DD4 and reports on this axis.

## 6. WHAT THE ORCHESTRATOR MUST DO, IN ORDER

1. Land the free repair (section 3.1) in `src/L/Cardinal.lagda.md`, then
run `make check` in the background (DD15) and record the ledger row.
2. Land the digest (section 3.2) at
`dev/literature/truncation-and-selection.md` and extend
`dev/literature/BIBLIOGRAPHY.md`.
3. Register and dispatch the door probe (section 2.3) as one task, brief
written to DD18, tier and head from `dispatch_policy.py`, and name the
`2-Constant` map as the widest unmeasured term it measures.
4. Record in `dev/PLAN.md` section 11 and `dev/JOURNAL.md`, in your own
words: `[LJ-1.305]`'s necessity claim measured `PT.rec` only; the
set-motive eliminator was untried; the verdict NEEDS-A-PRINCIPLE is
downgraded to NEEDS-A-2-CONSTANT-MAP-OR-THE-CROSSING.
5. Queue the two owner questions (section 4) with their evidence, marked
not urgent until the probe reports.
6. Propose two LESSONS at your numbering, with their measurements: first,
a truncation stall at a SET motive is a `2-Constant` obligation before it
is a principle (measurement: `SqIsSet.agda` green plus
`Properties.agda:181-268`); second, `[LJ-1.314]`'s sweep lesson, a
refutation sweeps by the discriminating property, payload-is-a-proposition
-over-a-well-ordered-carrier, not by family resemblance (measurement:
`CodeUntrunc.agda` green at the `:256` site).
7. Commit this task directory per `agents/README.md`. I committed
nothing.

## 7. WHAT WOULD REVERSE THIS RULING

Each condition is observable, and any one suffices for its half.

1. **Admit-the-principle reverses** when ALL of: the funded probe reports
the naive map refuted AND the canonical route walled at a named
`file:line`, AND the owner declines the bounded crossing
(`BoundedToCode`) as a parameter, AND the owner keeps the data-valued
hypothesis shape. If that day comes, prefer `BoundedToCode` over
`InjData`: it is the coded spelling the tree's own devices consume, and
`bridge→data` plus the 20-line composite derive `InjData` from it.
2. **The fork refusal reverses** when someone delivers a green consumer
chain that needs the square law at cardinal sites only: observable as
`StageCardinal` and `BoundedSubset` variants that typecheck with a
cardinal-gated `sq` parameter.
3. **The door closes** when the funded probe reports both attempts dead:
the naive map refuted by a term and the canonical route walled inside the
cap at a named site. The wall report then IS the necessity measurement at
the right eliminator, and the question goes to the owner as the coupled
crossing-or-statement ruling of section 4.
4. **The repair or the digest un-lands** if the landing audit finds a
factual defect at a cited `file:line`. MEASURED FALSE at this ruling's
reach: any such defect in the lines I checked.

## 8. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
Slots counted before every invocation with the exact awk command; both
counts returned 0. Runs: `SqIsSet.agda` exit 0 in 2.01 s at 1-minute load
5.89; `CodeUntrunc.agda` exit 0 in 2.26 s at load 5.60. Dependencies were
warm. MEASURED FALSE: any invocation past 30 minutes, any heap
exhaustion. I wrote only inside `agents/tasks/LJ-1-319/`. No commit, no
push, no `make check`, no edit to `src/`, `dev/`, `AGENTS.md` or any
sibling task directory.

## 9. CHECKS RUN

- `.venv/bin/python scripts/gate/lint-prose.py --check` on this file:
exit 0.
- MEASURED: no em dash in any file I wrote (grep, zero hits).
- Evidence spot-checks: sections 1 and 3.2.
