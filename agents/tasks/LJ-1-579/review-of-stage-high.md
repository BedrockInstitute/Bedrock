# review-of-stage-high: not delivered, and the one statement left is now a FORMULA and not a SEARCH

**NO-GO on the obligation.** `agents/tasks/LJ-1-579/Probe579.agda::stage-high`
is not inhabited and no postulate stands in for it. `StageHigh` is
`[LJ-1.536]`'s type, imported and not restated
(`agents/tasks/LJ-1-536/Probe536.agda:350-352`, imported at
`agents/tasks/LJ-1-579/Probe579.agda:56-59`). The probe is green: exit 0 on
each of three cold runs, median **213.76 s** and 1,658,306,560 B, 19.31 percent
of the 8 GiB cap (`runs/full-t1.time`, `runs/full-t2.time`,
`runs/full-t3.time`).

**THIS IS THE FOURTH NO-GO AND IT IS NOT THE SAME NO-GO.**
`Probe579.agda:445-447`:

    stage-high-from-definable-ih : LimitDefinableIH → StageHigh
    stage-high-from-definable-ih d =
      reduction (allH→all (closingIH (definable→limit-ih d)))

`[LJ-1.565]` left `StageHigh` resting on `HierBelowLimitH`, and called that an
unbounded search. **It rests on a strictly weaker statement now, that statement
asks for a formula and not for a bound, and it may use the tables below γ while
it does.**

## The brief's premise 1 does not hold

**PREMISE 1 READS "`[LJ-1.565]` parked at the heap wall. Basis:
`dev/pod/transitions/2026-08.jsonl:3169`". THE FILE HAS 157 LINES**, so the
citation resolves to nothing, and the brief's later sentence "`[LJ-1.565]` left
a park and no report. Do not be the fourth." is wrong about that task.

**IT LEFT BOTH.** Its worktree is a sibling of this one and its directory is
untracked there, so neither file is visible from here and neither is
importable:

| what | where |
|---|---|
| its report, verdict NO-GO | `../LJ-1-565/agents/tasks/LJ-1-565/lj-1.565-report.md:1-7` |
| its stop | `../LJ-1-565/agents/tasks/LJ-1-565/review-of-stage-high.md:1-9` |
| its chain, `stage-high-from-limit` | `../LJ-1-565/agents/tasks/LJ-1-565/Probe565.agda:327-328` |

**SO ITS WORK WAS REBUILT HERE AND NOT CITED.** Sections 4 to 7 of this probe
are that task's design, re-measured on this pane, and the credit is its own.

## What actually blocked it

**THE OBLIGATION IS A BOUND, NOT AN EXISTENCE, AND THAT IS THE WHOLE OF IT.**
`Probe579.agda:145-150`, exit 0 with no hypothesis and no induction:

    hier-somewhere : (γ : V ℓ) (oγ : IsOrd γ)
                   → Σ[ σ ∈ V ℓ ] (IsOrd σ × ⟨ hset γ oγ ∈ Lset σ ⟩)

`stage` (`src/L/Stage.lagda.md:180-193`) already puts `hierL γ` in the LEAST
stage that holds it. `Probe579.agda:152-159` pins the obligation from both
sides against that stage: the bound buys it, and by `stage-earliest` nothing
below can hold it. **Every route whose output is "some stage" is worth zero
lines here.**

**AND `[LJ-1.560]`'S REFLECTION IS EXACTLY SUCH A ROUTE.** The brief ordered it
tried and nobody had. It instantiates, at `Probe579.agda:313-320`, on
`[LJ-1.520]`'s Σ₁ level formula with no grade hypothesis, and it costs
168.23 s and 1,494,056,960 B alone (`runs/Control579b.agda`,
`runs/ctlb-1.time`). **Its certificate is `⟨ γ ∈ β ⟩`: the stage it names is
ABOVE the ordinal handed to it.** The obligation needs a stage below
`step 3 γ`. `mkReflect` cannot be asked for that, and
`LevelAtGamma` (`Probe579.agda:326-331`) is stated and not inhabited to say
which sentence would do instead.

## And the residue is smaller than the one that was left

**AT A LIMIT THE TABLE IS ALREADY INSIDE THE STAGE.** `Probe579.agda:360-380`,
exit 0 on its first run:

    hier-sub : (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
             → (z : V ℓ) → ⟨ z ∈ fst (hierL γ h o) ⟩ → ⟨ z ∈ Lset γ ⟩

**SO NO BOUND HAS TO BE FOUND AT A LIMIT. ONLY A FORMULA.**
`Probe579.agda:382-398`, and `:430-443` is the same with the induction
hypothesis in hand, which is the form `dev/literature/devlin-II5.md:218-222`
says the source's own proof uses:

    LimitDefinable = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
                   → Door (Lset γ) (fst (hierL γ h o))

    definable→limit : LimitDefinable → HierBelowLimitH

`Door` is `𝒟ₒ-intro`'s own premise (`agents/tasks/LJ-1-536/Probe536.agda
:76-80`), and that door asks for a formula at `⟪ Lset γ ⟫` and NOTHING else,
which is `[LJ-1.565]`'s `door-free` finding
(`src/L/Axioms/Separation.lagda.md:198-199`).

**AND IT LANDS TWO STAGES UNDER BUDGET.** `definable→limit` reaches
`Lset (sucV γ)` and the obligation allows `Lset (step 3 γ)`. **Devlin's three
is slack at the limit.**

## Why I stopped here

**THE ONE THING LEFT IS A PIECE OF MATHEMATICS AND NOT A PIECE OF AGDA.**
`LimitDefinable` asks for a `Formula ⟪ Lset γ ⟫ 1` whose `defSet` at `Lset γ`
is the table. The tree has the level formula at the CLASS carrier and both
directions of its correctness there (`src/L/Hierarchy.lagda.md:646-653` and
`:334`). What it does not have is that formula's correctness read INSIDE
`Lset γ`, at a limit γ, and no route in the tree supplies it: `mkReflect` gives
it at a different stage, and `AtStage` refuses it for want of a `Δ₀` grade that
`[LJ-1.536]` refuted (`agents/tasks/LJ-1-536/Probe536.agda:115-116`).

**AD12 GIVES THIS BRIEF ONE OBLIGATION** and the brief says "DO NOT BUILD A
REFLECTION PRINCIPLE FROM SCRATCH." Choosing that formula and proving it
correct inside the limit stage is the mathematician's call, so I name the
statement, price everything around it, and stop.

**I DO NOT OVERSTATE WHAT `hier-sub` BUYS.** It is a subset fact. It does not
say the table is definable there, and I measured nothing about whether it is.

**AND I DECLARE THE SHARED MACHINE.** `ps` showed a second Agda process on this
machine through the later runs, `agents/tasks/LJ-1-572/`, not mine and not
startable by me. **I ran ONE Agda process at a time and never a second.** The
large numbers are therefore upper bounds.
