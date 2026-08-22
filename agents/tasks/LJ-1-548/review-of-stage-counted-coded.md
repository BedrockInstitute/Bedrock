# Review of `stage-counted-coded`

The obligation is NOT written. This file is the obstruction, for the branch
`stop-stated`.

`agents/tasks/LJ-1-548/Probe548.agda` is GREEN, exit 0. It carries no hole and
no postulate. **Every reduction quoted below typechecked.** A hole would have
made each of them a claim.

## THE STATEMENT

```
stage-counted-coded :
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ
```

It is the brief's obligation, and it is row B9,
`agents/tasks/LJ-1-523/Probe523.agda:258-261`.

## STOP 1. THE BRIEF'S OWN PRECONDITION FAILS: `[LJ-1.547]` DID NOT LAND

The brief says: "**THIS BRIEF ASSUMES `[LJ-1.547]` CAME BACK GO.** ... **If it
did not land, or landed NO-GO, STOP AT THE D-10 AND SAY SO.**"

**IT DID NOT LAND.** Three checks, all at this worktree's `HEAD`, `c35bf14b`:

1. `agents/tasks/LJ-1-547/` **does not exist in this tree**. `ls` reports
   `No such file or directory`. The sibling rows do exist: `LJ-1-544`,
   `LJ-1-545` and `LJ-1-546` are all present.
2. **No commit on ANY branch of this repository ever added it.**
   `git log --all --oneline -- 'agents/tasks/LJ-1-547' 'agents/tasks/LJ-1-541'`
   returns EMPTY.
3. The commit log carries `b8bd6709 pod: admit LJ-1.547` and **no
   `pod: LJ-1.547 done` and no `pod: expire LJ-1.547`**, while `LJ-1.544`,
   `LJ-1.545` and `LJ-1.546` each carry both, and all three were admitted
   BEFORE 547 was.

**THE TASK IS STILL LIVE IN A PARALLEL WORKTREE.**
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-547/` exists, created in
the same minute as mine, and holds an uncommitted `Probe547.agda` and a report
whose `## HEAD` says `verdict: GO`. **I did not import it and I do not cite it
as a landed fact.** Section 3 of my probe abstracts its SHAPE instead of naming
its term. Evidence is `file:line`, and a file that no commit contains is not
evidence about this tree.

**AND THE CHAIN HAS A SECOND UNLANDED LINK.** `agents/tasks/LJ-1-541/` is
absent too, by the same `git log --all` check. `[LJ-1.541]` is the brief's
fourth-conjunct predecessor, and `[LJ-1.547]`'s own report reaches it by the
absolute path `/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-541/...`.
**So `[LJ-1.547]`'s green is not reproducible in any landed tree today.**

## STOP 2. THIS EXACT TYPE WAS ALREADY REFUTED, AND THE REFUTATION IS IN THIS TREE

My slot clause: "**If the report is NO-GO, or names the statement FALSE, stop
and say so with `file:line`. Do not inhabit the brief's type in that case.**"

`[LJ-1.533]` stated the brief's type character for character as
`StageCountedCodedᵀ` (`agents/tasks/LJ-1-533/Probe533.agda:80-83`) and refuted
it. Its review is IN THIS TREE at
`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:22`:

> `## D-10. THE TYPE IS FALSE, AND THE BRIEF ASKED FOR THIS CHECK FIRST`

**THE ARGUMENT, which I did not re-derive.** The brief's binding is
`IsOrd (fst δ)` and nothing else. `LsetS` makes the stage of any ordinal an
L-element on the nose, so `refl` fills the third hypothesis, and spending the
type therefore lands the AMBIENT statement at EVERY ordinal, finite ones
included. The delivered chapter refuses exactly that: `stage-card-upper` binds
`⟨ α ∈ˢ ω ⟩ → Empty.⊥` as a HYPOTHESIS
(`src/L/StageCardinal.lagda.md:564-565`), and at a finite δ the chapter's own
branch goes to `ω` and not to δ: `fin-inj` is
`(δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫`
(`src/L/StageCardinal.lagda.md:488`).

**THE CORRECTED TARGET IS ALREADY RECORDED**, at
`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:61`, `## THE CORRECTED
TARGET`. `StageCountedCoded′ᵀ` adds back `⟨ fst δ ∈ˢ sucV α₀ ⟩` and
`⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥`, the shadow's two side conditions.

**THE BRIEF DID NOT KNOW THIS.** Its premise 10 reads `[LJ-1.533]` as having
"measured a wall for a code of an AMBIENT injection" and nothing more. That is
half of what `[LJ-1.533]` delivered. The other half is a D-10 refutation of the
type this brief asks me to inhabit, plus a corrected target. **`[LJ-1.544]`'s
count did not know it either**: its B9 row reads "STATED NOWHERE"
(`agents/tasks/LJ-1-544/lj-1.544-report.md:102`), and `[LJ-1.533]` had stated
it and refuted it eleven rows earlier.

## WHAT I MEASURED ANYWAY, AND IT IS THE NEW PART

The two stops rest on recorded facts. What follows is measured in this file,
and none of it needs `[LJ-1.547]`.

### W3: THE TYPE FORMS. THE ROW IS NOT REFUTED AT THE TOP

`W3-code-at-B9-frame` (`Probe548.agda:88-91`) is `InjCode F Lδ δ` at B9's
frame, TYPE ONLY, no inhabitant. Written FIRST and typechecked ALONE as the
brief ordered: the slice is `runs/w3-slice.agda.txt`, 35 lines, and the run is
`runs/w3-1.out`, **exit 0, 1.77 s**.

**`InjCode`'s source slot imposes no ordinal condition of its own**
(`src/L/Cardinal.lagda.md:223-228`), so a stage is admissible THERE. **The
ordinal condition that blocks this row is not `InjCode`'s. It is the coding
leg's.**

### THE PAIR: THE TWO DIFFER IN BOTH COORDINATES

| | source | target |
|---|---|---|
| what the coding leg delivers | an ORDINAL `a`, under `IsOrd (fst a)` | `C a`, produced FROM the source |
| what B9 wants | the STAGE `Lset (fst δ)` | `δ`, named by the consumer |

`CodingLegShapeᵀ` (`Probe548.agda:123-124`) is that shape, abstracted over `G`
and `C` because the term is not in this tree. **`[LJ-1.547]`'s own report says
the same about the target**, unprompted: "the `b` is not free ... NOT into any
ordinal a consumer names."

**AND THE SOURCE CANNOT BE RE-READ.** `code-source-determined`
(`agents/tasks/LJ-1-546/Probe546.agda:127-133`), which IS landed in this tree,
says one table has one source. So a code delivered at source `a` is not a code
at source `Lset (fst δ)` under any reading.

### THE BILL: EXACTLY TWO DEMANDS, AND THE REDUCTION IS INHABITED

`leg→B9` (`Probe548.agda:153-162`) is

    (G C : SL.S → SL.S)
  → CodingLegShapeᵀ G C → SourceDemandᵀ → TargetDemandᵀ C
  → StageCountedCodedᵀ

**typechecked.** So `SourceDemandᵀ` (`Probe548.agda:128-131`) and
`TargetDemandᵀ` (`Probe548.agda:136-139`) are the WHOLE distance from the
coding leg to B9, and nothing else is wanted. A successor brief may price
exactly these two.

**THE TRANSPORT COSTS NOTHING, AND THE BRIEF'S 33-LINE FEAR DID NOT
MATERIALISE.** The brief warned that `fst Lδ ≡ Lset (fst δ)` is a path and that
`[LJ-1.529]` measured one re-basing at 33 lines. **I never transport along that
path.** Both demands are stated in terms of `Lδ` itself and take `p` as their
own hypothesis, so `p` is consumed by the demand and not by me. The one `subst`
in the file is along the TARGET demand's path `C Lδ ≡ δ`, and it is three lines
(`Probe548.agda:159-161`).

### WHERE `[LJ-1.533]`'s WALL BITES, AND THE BRIEF ASKED

**IT APPLIES, AND IT BITES AT THE SOURCE COORDINATE.**

`SourceDemandᵀ` says the stage is an ordinal. That is a plain falsehood about
the tower and not a wall. **A route that does not pretend the stage is an
ordinal must cross from the stage to the ordinal instead, and what the tree
delivers for that crossing is AMBIENT**: `stage-card-upper` is
`⟪ Lset α ⟫ ↪ ⟪ α ⟫` (`src/L/StageCardinal.lagda.md:564-565`). Turning that
into a code is `AmbToCodeᵀ` (`agents/tasks/LJ-1-533/Probe533.agda:111-114`).
**That is the wall, at the source coordinate and nowhere else.**

`crossing→B9` (`Probe548.agda:210-215`) is the measurement that settles what
the coding leg is worth on this row:

    StageToOrdCodeᵀ
  → ((δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
       → ⟪ fst Lδ ⟫ ↪ ⟪ fst δ ⟫)
  → StageCountedCodedᵀ

**typechecked, and it names the coding leg NOWHERE.** One crossing, plus the
ambient injection the chapter already delivers, IS B9. **So the coding leg's
five dispatches are not on this row's critical path. The crossing is.**

**WHAT I DID NOT MEASURE.** I did not refute `SourceDemandᵀ` in Agda.
Exhibiting the members of `Lset (# n)` needs the definability machinery,
`[LJ-1.533]` declined to price it
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:54`), and I decline it
for the same reason rather than assert it.

## C-42

**COUNT of `src/` sites that DELIVER an inhabited `InjCode`: 2. PAIRS THEY
DELIVER AT: 1.**

| site | the pair |
|---|---|
| `src/L/CodedShift.lagda.md:51-52` | `(sucʟ γ , γ)` |
| `src/L/Absorption.lagda.md:625-626` | `(sucʟ γ , γ)` |

**COUNT whose SOURCE is a STAGE rather than an ordinal: 0.** This is my own
criterion at today's tree, and it is the coordinate this row dies on. Both
delivered sources are `sucʟ γ`, an ordinal successor. `src/L/Cardinal.lagda.md:240`
and `:257` do mention `Lset β`, but as the range the CODE `F` is drawn from,
never as the source.

I did not reuse `[LJ-1.546]`'s number. It counted the same two sites by its own
criterion, and I re-ran the sweep here.

**AND THE SHAPE EXTENDS.** B10, `SuccIntoPower`
(`agents/tasks/LJ-1-523/Probe523.agda:266-268`), also concludes an `InjL`, and
`[LJ-1.546]` reports its remaining wall is the same `Formula` coordinate. **B5
is not on this shape and this obstruction does not touch it.**

## WHAT WAS NOT DONE

No axiom, no postulate, no `src/` change, no hole. `SourceDemandᵀ`,
`TargetDemandᵀ`, `StageToOrdCodeᵀ` and `CodingLegShapeᵀ` appear ONLY as
hypotheses of reductions, never as inhabited terms. I did not assemble the four
conjuncts, which the brief forbade. I did not build B5 or B10. I did not import
or copy any file from an unlanded worktree.
