# LJ-1.536 report: StageHigh reduces to the stage below γ, and the limit did not leave

**VERDICT: NO-GO, AND IT IS A NO-GO AT THE DOOR.** The obligation
`agents/tasks/LJ-1-536/Probe536.agda::StageHigh` is stated at
`Probe536.agda:350-352` and is not inhabited. No postulate stands in for it.
`agents/tasks/LJ-1-536/review-of-StageHigh.md` states the stop.

**THE PROBE IS GREEN AND IT CARRIES FIVE TERMS THAT ARE NOT THE OBLIGATION.**
Exit 0, `runs/full-t2.out`, median 12.45 s and 669 MB over three cold runs.

| what | where |
|---|---|
| the door of `𝒟ₒ-intro`, written out and ascribed against it | `Probe536.agda:76-80` |
| `[LJ-1.520]`'s graded formula has NO `Δ₀` witness, refuted | `Probe536.agda:115-116` |
| a recorded pair lies three stages above its own index | `Probe536.agda:163-164` |
| the adjunction at an ARBITRARY stage | `Probe536.agda:189`, `:278-280` |
| `HierBelowAll → StageHigh`, total in γ, no limit and no α | `Probe536.agda:357-358`, `:362-364` |

**AND ONE MEASUREMENT THAT IS WORTH MORE THAN ANY OF THEM.** A single row whose
body is the variable `p`, and whose type says only that three successors above a
successor are four successors, costs **425.73 s** alone in a 34-line file
(`runs/Control536e.agda:32-33`, `runs/ctle-0.time`). Inside this probe the same
row exhausted 8 GB twice. See "THE WALL" below.

## D-10, BEFORE ANY AGDA

The brief ordered one question first: is `[LJ-1.520]`'s graded formula the
formula that `𝒟ₒ-intro` wants, or does it say something adjacent?

**IT IS ADJACENT, AND THE DIFFERENCE IS THE GRADE.**

### What the door wants

`𝒟ₒ-intro` (`src/L/Constructible.lagda.md:301-304`) wants
`∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ x) ∥₁`. `Probe536.agda:76-80`
writes that out as `Door` and ascribes `𝒟ₒ-intro` to it, so the shape is
checked and not paraphrased. The door makes three demands, and only the third
is about mathematics:

1. the constant domain is `⟪ A ⟫`, the members of the stage;
2. the arity is 1;
3. `defSet` reads the formula under the INNER satisfaction of `(A , ∈)`
   (`src/L/Definability.lagda.md:111-112`, `:146-147`), so every quantifier
   ranges over the members of the stage and over nothing else.

### Why 1 and 2 are not the finding

`[LJ-1.520]` proved the graded formula carries no constant, by `refl`
(`agents/tasks/LJ-1-520/runs/CountCheck.agda:18-19`). A constant-free formula
reaches ANY constant domain through `erase` and `embed`
(`src/FOL/Manipulation/Relabelling.lagda.md:117`), and two binders fix the
arity. **Syntax is not what blocks, and a report that stopped at the type
mismatch would have stopped at the wrong place.**

### Why 3 is the finding, and it is a refutation

The tree delivers exactly ONE bridge from an external formula to the door's
inner reading: `L.Axioms.Separation.AtStage`
(`src/L/Axioms/Separation.lagda.md:119-135`, `:199-231`). Its hypotheses are
`Δ₀ φ` and "every constant of φ lies in the stage"
(`src/FOL/Manipulation/Bounding.lagda.md:63-79`). `Probe536.agda:115-116`:

    no-Δ₀-levelFo : {n : ℕ} (w b : Fin n) → Δ₀ (fst (levelFo-Σ₁ w b)) → Empty.⊥
    no-Δ₀-levelFo w b ()

`Δ₀` has no constructor indexed by an unbounded existential
(`src/FOL/LevyHierarchy.lagda.md:47-57`); `levelFo` is thirteen of them
(`agents/tasks/LJ-1-520/Probe520.agda:167-169`). Agda closes it by absurd
pattern. **The graded formula is refuted at the door, not merely absent from
it.**

### The second door, which no predecessor named

`AtStage` is delivered in `src/`, it is the tree's stage-separation bridge, and
`[LJ-1.230]`, `[LJ-1.494]`, `[LJ-1.517]`, `[LJ-1.530]` and `[LJ-1.532]` name it
in none of their reports or probes. `runs/W3.agda:111-141` re-ascribes four of
its terms so that the claim is a typechecked row and not a search result.
**Whoever writes the next brief should read `AtStage` before pricing any route
into a stage.**

## W3, WRITTEN FIRST AND ALONE

`agents/tasks/LJ-1-536/runs/W3.agda`, 163 lines, exit 0 on the FIRST run,
`runs/w3-0.out`, median **1.82 s** over three cold runs (`runs/w3-t1.time`,
`runs/w3-t2.time`, `runs/w3-t3.time`), 608 MB at `runs/w3-0.time`. The brief
estimated about 30 lines and under 50 s; the file is longer and much cheaper.

It carries five terms and every one is an ascription or a refutation:

| row | where | what it settles |
|---|---|---|
| `door` | `runs/W3.agda:65-66` | `Door` IS `𝒟ₒ-intro`'s premise |
| `graded` | `:78-79` | what `[LJ-1.520]` delivered, imported not restated |
| `no-Δ₀-levelFo` | `:94-95` | the graded formula misses the only bridge |
| `Bridge` | `:111-141` | `AtStage` is a second door, and its two directions |
| `adjoin`, `Δ₀-adjoin`, `Below-adjoin` | `:153-163` | a formula that PASSES that door |

**W3 IS GO, and its answer changed the task.** The door does not want a Levy
grade at the class carrier. It wants a `Δ₀` formula with parameters drawn from
the stage. `adjoin` is the cheapest such formula: two constants, no quantifier.
That is what section 5a of the probe is built on.

## WHAT IS DELIVERED

### The placement of one recorded pair

`Probe536.agda:163-164`. A stage is a member of the next stage, an ordinal is a
member of the stage after itself (`src/L/Ordinal/Stages.lagda.md:434`), so the
Kuratowski pair of the two is a member two stages further up
(`src/L/Axioms/Basic.lagda.md:596-599`):

    pr-at : (δ : V ℓ) → IsOrd δ → ⟨ pr δ (Lset δ) ∈ Lset (step 3 δ) ⟩

**THIS IS WHERE DEVLIN'S FOUR COMES FROM, and the probe now says so as a term.**
The sequence at δ ≤ γ has its largest entry at γ, hence inside `Lset (step 3 γ)`;
the sequence itself is one stage above that.

### The adjunction, at an arbitrary stage

`Probe536.agda:189-280`. If a set T is described member by member as "a member
of h, or the set q", and h and q both lie in a stage, then T lies in the NEXT
stage. Nothing in it is about the hierarchy or about any concrete position.

### The reduction

`Probe536.agda:357-358` and `:362-364`:

    reduction    : HierBelowAll → StageHigh
    reduction-at : (γ : V ℓ) (oγ : IsOrd γ) → HierBelow γ oγ
                 → ⟨ fst (seq γ oγ) ∈ Lset (step 4 γ) ⟩

where `HierBelow γ oγ = ⟨ fst (hierL γ (isL-ord γ oγ) oγ) ∈ Lset (step 3 γ) ⟩`
(`:186-187`). **It is pointwise: one ordinal's hypothesis pays that ordinal's
obligation.** It is total in γ. It uses no limit hypothesis, no α, and it never
reads `ω ∈ γ`.

### The residue

`Probe536.agda:408-409`, stated and not inhabited:

    HierBelowLimit = (γ : V ℓ) (oγ : IsOrd γ) → IsLimit γ → HierBelow γ oγ

**THE LIMIT DID NOT LEAVE.** `[LJ-1.519]` split Devlin 2.6(ii) so that Part B
names no limit in its TYPE, and that is correct. But `HierBelow` at a SUCCESSOR
is the obligation at the predecessor, so the adjunction is the successor case of
an induction on γ, and the only case it cannot reach is a limit. The split moved
the limit out of the statement and into the induction; it did not remove it.

### One thing the brief did not ask and the next brief needs

**DEVLIN'S FOUR IS NOT LOAD-BEARING.** `[LJ-1.519]`'s Part A is total in the
number of steps: `steps-stay` takes `(n : ℕ)`
(`agents/tasks/LJ-1-519/Probe519.agda:200-202`) and `stage-below` likewise
(`:208-210`). The reduction spends it at 4 in one line
(`:243`) and at 5 in two others (`:239`, `:241`). **So a `StageHigh` proved at
`step k γ` for any fixed k still composes with `[LJ-1.519]`'s reduction, at the
cost of one numeral.** If a route reaches the sequence at a larger finite
offset, it is not a weaker result for this chain. This probe did not need the
slack and did not take it: `reduction-at` lands at `step 4 γ` exactly.

## WHAT THE FOUR ROUTES GET

The obligation did not land, so the brief asks which of the four is furthest
from the term that was built. **Row six of the condensation chain is furthest.**
The other three are one hypothesis away from `HierBelowAll`.

| route | what it gets from `reduction` / `HierBelowAll` |
|---|---|
| `[LJ-1.519]`'s `HierInStageLimit` (`Probe519.agda:148-150`) | CLOSEST. `Probe519.agda:235` is `StageHigh → StageLow → HierInStageLimit`. With `reduction` in front, the chain needs `HierBelowAll` and `StageLow` and nothing else. |
| `[LJ-1.494]`'s `hier-in-stage` | `HierBelow` IS its statement at a named stage. `[LJ-1.494]` reported "The tree does not bound `hierL δ` by `α`" (`agents/tasks/LJ-1-494/lj-1.494-report.md:66-67`). `reduction-at` says the four-stage bound follows from the three-stage bound at the SAME ordinal, so the two gaps are one gap and it is one stage wide. |
| `[LJ-1.532]`'s `HierInK` (`agents/tasks/LJ-1-532/Probe532.agda:274-277`) | It quantifies `hierL β ∈ Lset α` for `β ∈ α` and α a limit. From `HierBelow β` plus successor closure plus `Lset-mono`, `Lset (step 3 β) ⊆ Lset α`. So `HierBelowAll` pays `HierInK` and `[LJ-1.532]`'s "the two carriers share ONE obstruction" is now three carriers and one obstruction. |
| row six of the chain | FURTHEST, and it gets nothing directly. Row six is about `graphBndAt` bounded by a variable `K`, and its standing hypothesis is that `K` is a level (`agents/tasks/LJ-1-532/lj-1.532-report.md:45`, "inherits it unchanged and the `K`-is-a-level gap stays open."). Nothing in this probe speaks about `K`. |

**AND THE TARGET IS STILL NOT VACUOUS.** `[LJ-1.532]` proved the canonical
witness is an approximation (`agents/tasks/LJ-1-532/Probe532.agda:346-349`).
This task adds the other half at the placement level: `pr-at` says every entry
of the sequence is where it must be for the sequence to fit the stage at all.

## THE WALL

**TWO HEAP EXHAUSTIONS AT 8 GB, ONE CALIBER, AND NEITHER WAS RERUN.** Both are
reported here with the controls that located them. The caliber was
`GHCRTS="-A64m -I0 -M8g"` on the pane, set by the program and untouched.

### Wall 1: the concrete stage in the type

The first form of the probe carved the sequence at `step 3 γ` directly, so the
types of the two constants, of the formula and of every `where` block under them
named `⟪ Lset (sucV (sucV (sucV γ))) ⟫`. **Heap exhausted at 8 GB**,
`runs/full-1.time`.

That is law P-l (`dev/LESSONS.md:2357`): a statement may be ABOUT a concrete
stage, but naming a transparent construction in its TYPE re-normalizes the tower
at every check. **P-l also says a cure does not transfer by analogy, so the cure
was measured alone before anything consumed it.** `runs/Control536.agda` states
the same mathematics with the stage as a module PARAMETER:

| form | result |
|---|---|
| carving at `step 3 γ`, `⟪ Lset (sucV (sucV (sucV γ))) ⟫` in the types | **heap exhausted, 8 GB**, `runs/full-1.time` |
| the same mathematics at a variable stage | **exit 0, 1.00 s, 299 MB**, `runs/ctl-0.time` |

A controlled pair inside one task. The abstract form is section 5a of the probe
and the instantiation is section 5b, which is nine lines.

### Wall 2: one row, and the row is a conversion

The probe then exhausted 8 GB a second time (`runs/full-2.time`). Four controls
located it, and every one of them is a file that stayed green:

| control | contents | result |
|---|---|---|
| `runs/Control536b.agda` | the instantiation site MINUS the instantiation | exit 0, **11.07 s**, `runs/ctlb-0.time` |
| `runs/Control536c.agda` | the same WITH the instantiation | exit 0, **11.20 s**, `runs/ctlc-0.time` |
| `Probe536.agda` minus one row | sections 1 to 7, `successor-step` removed | exit 0, **11.13 s**, `runs/full-3.time` |
| `runs/Control536d.agda` | three factor rows of that one row | **heap exhausted, 8 GB**, `runs/ctld-0.time` |

**THE ROW ASKED AGDA FOR A CONVERSION AND FOR NOTHING ELSE:**

    successor-step : (α : V ℓ) (oα : IsOrd α) → HierBelow α oα
                   → HierBelow (sucV α) (suc-ord oα)
    successor-step α oα h = Adjoin.seq∈ α oα h

`runs/Control536e.agda` then reduced it to the smallest row that could carry the
cost. That file has 33 lines, imports no hierarchy chapter, states `step` and
ONE obligation whose body is the variable `p`:

    step-conv : (α x : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
    step-conv α x p = p

**Exit 0, 425.73 s, 372 MB** (`runs/ctle-0.time`). It does not exhaust the heap
alone; it exhausts it inside a file that is already holding the probe.

**AND THE LAST CONTROL TAKES THE TOWER OUT ALTOGETHER.**
`runs/Control536f.agda` is 30 lines. It imports no chapter of `src/`. It states
`step`, and one obligation:

    step-only : (α : V ℓ) → step 4 α ≡ step 3 (sucV α)
    step-only α = refl

**Exit 0, 417.18 s, 351 MB** (`runs/ctlf-0.time`).

| row | mentions | time |
|---|---|---|
| `step-conv` (`runs/Control536e.agda:32-33`) | `step`, `sucV`, `Lset`, `∈` | 425.73 s |
| `step-only` (`runs/Control536f.agda:29-30`) | `step`, `sucV` | 417.18 s |

**98 PERCENT OF THE COST IS `sucV`, AND NO PART OF IT IS THE TOWER.** `Lset` is
`opaque` (`src/L/Constructible.lagda.md:211`, `:221`) and contributes about 8 s
of the 426. In the pinned library `sucV N = N ∪ ⁅ N ⁆s` and `a ∪ b = ⋃ ⁅ a , b ⁆`
(`Cubical.HITs.CumulativeHierarchy.Constructions`, `:156-157`, `:160-161`), so
one successor is two set layers and four successors are eight. Two spellings of
the same four successors make Agda normalize all of it, twice.

**THIS IS LAW P-l WITH THE TOWER REMOVED FROM THE EXPERIMENT.** P-l's own
measurement is about naming `⟪ sucV (γp p) ⟫` in a type. This one names no `⟪ ⟫`
and no stage: `refl` between two spellings of `sucV` applied four times to a
variable costs seven minutes on its own. **I propose it as a measured law and I
do not write it into `dev/LESSONS.md`, which is not in this task's scope:**

> **Spell a finite successor tower ONE way.** `sucV` is transparent, and
> `step (suc k) α` and `step k (sucV α)` are definitionally equal and cost
> minutes to convert. Choose one spelling per statement and never let two meet
> in a conversion. Measured 2026-08-22 at `[LJ-1.536]`: 417.18 s for `refl`
> alone at four successors, `agents/tasks/LJ-1-536/runs/ctlf-0.time`.

**WHAT THIS COSTS THE CAMPAIGN.** `step n γ` is `[LJ-1.519]`'s own vocabulary
and it is now in two probes. **Any statement that spells the same stage two
ways, once as `step (suc k) α` and once as `step k (sucV α)`, is priced in
minutes and not in seconds, and no proof body can reach it.** The identity is
real and this report states it in prose; the term that would witness it is
priced above the caliber.

## WHAT IT COST

| file | lines | result | time | memory |
|---|---|---|---|---|
| `runs/W3.agda` | 163 | exit 0, first run | 1.82 s median of 3 cold | 608 MB |
| `Probe536.agda` | 409 | exit 0 | 12.45 s median of 3 cold | 669 MB |
| `runs/Control536.agda` | 153 | exit 0, first run | 1.00 s | 299 MB |
| `runs/Control536b.agda` | 158 | exit 0 | 11.07 s | 603 MB |
| `runs/Control536c.agda` | 271 | exit 0 | 11.20 s | 670 MB |
| `runs/Control536d.agda` | 148 | HEAP WALL | 8 GB | 8 GB |
| `runs/Control536e.agda` | 33 | exit 0 | 425.73 s | 372 MB |
| `runs/Control536f.agda` | 30 | exit 0 | 417.18 s | 351 MB |

The brief estimated about 220 lines in the probe, of which the obligation was
about 60. The probe is 409 lines and the obligation is not in it. **About 90 of
those lines are the abstract adjunction, and they exist because of wall 1, not
because of the mathematics.**

## FOR THE NEXT BRIEF

**ONE STATEMENT IS LEFT AND IT IS `HierBelow` AT A LIMIT.** Everything else in
Devlin's Part B is now a green term.

1. **The next obligation is `HierBelowLimit`** (`Probe536.agda:408-409`), not
   `StageHigh`. `StageHigh` follows from it and from the successor case, and the
   successor case is `reduction-at`.
2. **The door for it is `𝒟ₒ-intro` and NOT `AtStage`.** At a limit γ the
   approximations `hierL δ` for `δ ∈ γ` all lie inside `Lset γ`, so an
   existential over the STAGE reaches them, and a `Δ₀` formula with a constant
   bound does not: the bound would have to be a member of `Lset γ` that holds
   them all, and no member of `Lset γ` does. **So the limit case needs a formula
   over `⟪ Lset γ ⟫` with an unbounded existential, and the tree has no bridge
   to that.** `dev/literature/devlin-II5.md:221-222` calls it "witnessed inside
   the carrier".
3. **Do not brief a term at `step 3 (sucV α)` or any second spelling of a
   stage.** See THE WALL: `refl` between two spellings of four successors costs
   417.18 s with no tower in the file at all. Spell every stage once, and if a
   statement must move between two spellings, that move is the task and not a
   step inside one.
4. **`AtStage` should be read before any further route into a stage is priced.**
   It was delivered in `src/` throughout this leg and no report named it.
5. `Δ₀` and `BoundedFo` are cheap to satisfy and the probe shows the pattern at
   `Probe536.agda:189-280`; the expensive hypothesis is always the bound.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: not read. The predecessors this task needs
  were named in the brief with their task codes, and their probes and reports
  are live under `agents/tasks/`.
- `archive/dev/JOURNAL-archived.md`: not read, declined. A live document carries
  no history and this task needed no history.
- `archive/dev/JOURNAL.md`: not read, declined, for the same reason.
- `dev/ARCHIVE.md`: not read. Nothing was retired by this task, so clause W4
  has no row to write here.
- `archive/dev/DECISIONS-archived.md`: not read, declined. No `D<n>` code
  appears in this task.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: READ, and it is the strongest confirmation of
  the D-10 answer. `:217`:

  > Strength: the existential over z is UNBOUNDED at the ambient level.

  and `:222`:

  > γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not

  **The digest already separates the two readings this task measured.**
  `[LJ-1.520]` delivered the ambient Σ₁ form; the door wants the witness inside
  the carrier.
- `dev/literature/level-formula-slot-roles.md`: READ. `:9`:

  > arithmetic**, and a port that numbers its variables needs the slot arithmetic.

  It is about the arity and the slot roles of the level-hood formula. This task
  did not number any slot, because D-10 refuted the graded formula at the grade
  and not at the arity, so the digest was read and then not used.
- `dev/literature/truncation-and-selection.md`: not read, declined. No choice
  and no selection is made anywhere in this task.
- `dev/literature/digest.md`: not read, declined. `devlin-II5.md` is the chapter
  digest this task needed.
- `dev/literature/geology.md`: not read, declined. Nothing here is about ground
  models.
