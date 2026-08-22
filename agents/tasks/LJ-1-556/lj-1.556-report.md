# LJ-1.556 report: the square law, inside L

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-556/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated and no hole is left, so every
reduction in the probe is a measurement and not a claim. The probe is a raw
`.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and
the ratio bar cannot fire on it.

## VERDICT

**NO-GO on `square-inside-L`.** The obstruction is
`agents/tasks/LJ-1-556/review-of-square-inside-L.md`. No term named
`square-inside-L` exists in any file of this task.

**THE PROBE IS GREEN, EXIT 0, FOUR RUNS.**
`agents/tasks/LJ-1-556/Probe556.agda`, 362 lines. `runs/full-2.out` (176.9 s,
first green), `runs/full-3.out` (1.4 s, interface reused),
`runs/full-4.out` (176.9 s, interface deleted first) and `runs/full-5.out`
(176.6 s, after a comment-only fix, interface deleted first). The one red
predecessor is `runs/full-1.out`, a `subst2` in the wrong direction at
`Probe556.agda:301`.

TWO findings, and the second is the one that decides the task.

1. **W3 IS GO, AND IT IS THE ONLY GO.** `κ × κ` IS an L-set at this frame,
   with both projections, and the second one is UNTRUNCATED. The obligation is
   about the right object.
2. **D-10. THE BRIEF'S TYPE IS UNDER-HYPOTHESIZED, AND NO CODING FIXES IT.**
   The ambient square law is not a per-ordinal theorem. It is one ∈-induction
   over all ordinals (`src/L/SquareLawClosed.lagda.md:325`), and the fourth
   conjunct of its per-ordinal hypothesis `Init`
   (`src/L/Ordinal/SquareLaw.lagda.md:692`, `:696-698`) is derived at exactly
   one site (`src/L/SquareLawClosed.lagda.md:96`) from TWO inputs, one of
   which is **the square law at every smaller infinite ordinal**
   (`src/L/SquareLawClosed.lagda.md:99-100`). `IsCardinalL κ`
   (`src/L/Cardinal.lagda.md:230-233`) supplies neither. So the brief binds
   the conclusion of an induction and none of its hypothesis.

**THE STATEMENT IS TRUE AND IT IS NOT PROVABLE FROM WHAT THE BRIEF BINDS.**
That is a different stop from `[LJ-1.533]`'s and from `[LJ-1.552]`'s: theirs
were price stops at a coding wall, this one is a type stop.

## W3, THE WIDEST UNMEASURED TERM

The brief named it: `κ × κ` as an L-SET, with its two projections, TYPE ONLY.

**WRITTEN FIRST AND TYPECHECKED ALONE**, before any other Agda of this task.
The slice is `agents/tasks/LJ-1-556/runs/W3.agda`, 187 lines. Green runs
`runs/w3-3.out` and `runs/w3-4.out`, exit 0. The two red predecessors are kept
as `runs/w3-1.out` and `runs/w3-2.out`.

**I DID MORE THAN THE TYPE, ON PURPOSE.** A type alone cannot answer the
question the brief attached to it, which is whether the product IS an L-set at
this frame. So the slice inhabits it:

| Term | What it delivers |
|---|---|
| `Square.sqL` | the L-set of Kuratowski pairs of two members of `κ` |
| `Square.sqL-in` | any two members of `κ` give a member of `sqL` |
| `Square.sqL-out` | any member of `sqL` IS such a pair, **untruncated** |

The route is the one two chapters already use for this exact shape:
`StageBound` (`src/L/InjChain.lagda.md:75`) bounds the coded pairs and
`hasSeparationL` (`src/L/Axioms/Full.lagda.md:144`) carves the product out of
the bound. The untruncation is free: `pr-inj` (`src/V/Coding.lagda.md:178`)
and `↪-inj` make the component pair unique, so the fibre type is a
proposition and `PT.rec` lands in it with no choice and no extra hypothesis.
That matters downstream, because a consumer of the product needs the two
components as INDICES and not merely their existence.

**VERDICT: GO. The obligation is about the right object.**

**THE PRICE, AND THE BRIEF GUESSED IT LOW.** The brief estimated about 15
lines and under 60 seconds. Measured: 187 lines and **180.2 s**
(`runs/w3-4.out`, interface deleted first, dependencies warm). The probe as a
whole, 362 lines, costs **176.9 s** (`runs/full-4.out`, same conditions), so
almost the whole figure is the dependency chain being read, not my code: the
extra 175 lines of section 2 to 4 cost about nothing. **Report the number
measured, not the number the brief guessed**: a slice that imports
`L.InjChain` and `L.Cardinal` starts at about 175 s in this worktree
whatever it contains.

## WHAT INTERNALIZED AND WHAT DID NOT

The brief orders this step by step against the ambient proof, each at
`file:line`. `Initial.pair` (`src/L/Ordinal/SquareLaw.lagda.md:945`) is

    pair p = fiber α {x = colA p} (col∈α p) .fst

and it decomposes into six pieces.

| # | Piece | `file:line` | Inside L? |
|---|---|---|---|
| 1 | `Pair α oα = ⟪ α ⟫ × ⟪ α ⟫` | `:212-213` | **YES, MEASURED.** `Square.sqL` and its two readings |
| 2 | `ordSWO`, membership order on members | `:176` | **YES, MEASURED.** `Square.ltFo`, `Square.ltL`, both readings |
| 3 | `maxOrd`, `_≺_`, max-then-lexicographic | `:200`, `:215` | Same device as 2. **NOT measured; I do not claim it** |
| 4 | `wf≺` / `godSWO` | `:302`, `:308` | Same device as 2. **NOT measured; I do not claim it** |
| 5 | `col`, the collapse recursion | `:378`, `:384` | **NO. FIRST WALL** |
| 6 | `col∈α`, the exclusion chase | `:862`, `:931` | **NO. SECOND WALL, and independent of 5** |

(`col-inj`, `:427`, is what makes `pair` injective, and it is a corollary of 5
and `col-mono`, `:406`. It adds no ingredient.)

### 1 internalized, and it is section 1 of the probe

Above, under W3.

### 2 internalized, and I measured it rather than transferring it

`L.Coding.Sequence.RecShape` (`src/L/Coding/Sequence.lagda.md:281`) takes its
step as a `Formula` and NEVER as a set. **So the order data the ambient
collapse consults does not have to become an L-set at all**: it has to become
a condition on the two components of a pair. Section 2 of the probe builds
that condition at the membership order, `Square.ltFo`, proves both readings,
and then carves the SET too, because once the formula exists the carve is one
more `hasSeparationL` line.

I measured ONE condition. **AGENTS.md:45 forbids the transfer by analogy**, so
what I claim for 3 and 4 is that the DEVICE is the same, not that their
adequacy is proved. The max-then-lexicographic condition adds a `max` clause
(`m ∈ {a,b} ∧ a ⊆ m ∧ b ⊆ m`) and its adequacy is unwritten.

### 5 is the first step the tree cannot take

`col` (`src/L/Ordinal/SquareLaw.lagda.md:384`) is `W.induction` over the
ambient type `Pair`, producing an ambient `S`-valued function, with step
`colStep p rec = ⋃ (sett Pair (λ r → colPick p rec r (≺-dec r p)))` (`:378`).

The tree's only route from such a function to an internal table is
`L.Recursion`, and that chapter states the condition exactly:

> A recursive definition is internalizable when its graph is expressible, and
> nothing about the recursion's shape, its depth, its order of descent, or the
> complexity of its clauses appears in the condition.
> (`src/L/Recursion.lagda.md:259-262`)

The form to fill is `Definition` (`src/L/Recursion.lagda.md:272`), five
fields: `dom`, `fn`, `graph`, `defines`, `only`. **`dom` is delivered by W3
and `fn` is `col` itself. `graph`, `defines` and `only` do not exist in the
tree for `col`.** That is the wall, and it is a price wall: the shape of the
cure is known (`RecShape`, `src/L/Coding/Sequence.lagda.md:281`) and
`L.Choice.Table` names the identical debt for its own instance and calls it
three things and not one (`src/L/Choice/Table.lagda.md:874-877`).

**D-26 IS THE LAW THAT NAMES WHY THIS ONE IS PAYABLE AT ALL.** `col` is keyed
on `⟪ κ ⟫ × ⟪ κ ⟫`, whose members carry their own generation data (two
ordinals), not on a definable power. So the key exists with no syntax; what
needs syntax is only the VALUE, which is what `graph` is.

### 6 is a second wall, independent of 5, and no coding removes it

Full argument in `review-of-square-inside-L.md`. In one paragraph: `col∈α`
(`:931`) closes through `exclude` (`:862`), `exclude` spends `noinj²`, and the
tree discharges `noinj²` at exactly one site, `clause4-at-kappa`
(`src/L/SquareLawClosed.lagda.md:96`), from the ambient leastness `κ-min-atL`
(`:86`) AND the square law at every smaller infinite ordinal, `ih`
(`:99-100`), spent at `:106`. `IsCardinalL κ` gives neither. The two gaps are
independent:

- **coded versus ambient.** `IsCardinalL` refutes only injections that carry
  a code, and `[LJ-1.533]` measured that nothing codes an arbitrary ambient
  injection (`agents/tasks/LJ-1-533/lj-1.533-report.md:30`). **This gap closes
  if 5 is paid**, because the chase is then internal from the start and its
  injection carries a code by construction.
- **`δ` versus `β × β`.** `IsCardinalL κ` refutes an injection of `κ` into a
  smaller set. `noinj²` must refute an injection of `κ` into a smaller set's
  SQUARE. **The bridge between them is the square law at that smaller set.**
  This gap does NOT close by paying 5 and does not close by coding anything.

### The corrected target, recorded beside the original as D-10 orders

Section 3 and section 4 of the probe write both out and inhabit neither.

    BriefTarget =                              -- the original
      (κ : S) → IsOrd (fst κ) → IsCardinalL κ → InternalSquare κ

    SquareStep =                               -- corrected
        (κ : S) → IsOrd (fst κ)
      → IsCardinalL κ
      → ( (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩ → InternalSquare β )
      → InternalSquare κ

    InternalSquare κ = ∥ Σ[ F ∈ S ] InjCode F (Square.sqL κ) κ ∥₁

`SquareStep` is the internal image of `init-at-kappa`
(`src/L/SquareLawClosed.lagda.md:166`) composed with `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`). **It is still not a task**: even with
its induction hypothesis, discharging it needs wall 5.

### C-42, THE SWEEP, WITH ITS COUNT

C-42 is in this task's law bundle and it orders the sweep before the cure: a
refutation measures the site it names and never how far the shape extends.

**THE SHAPE SWEPT FOR: an obligation that binds `IsCardinalL κ` and expects a
per-κ construction out of it.**

- `IsCardinalL` occurs at **9 lines in `src/`, in 3 files**
  (`src/L/Cardinal.lagda.md`, `src/L/GCH.lagda.md`,
  `src/L/SquareLawClosed.lagda.md:313`, a comment).
- It is a HYPOTHESIS at **4 places, all in `src/L/GCH.lagda.md`**: `:49`,
  `:51` (twice, inside `SuccCardL`) and `:63` (`GCHStatement`).
- **THE COUNT OF DEFECTIVE SITES IS ONE, AND IT IS THIS BRIEF.**
  `GCHStatement` (`src/L/GCH.lagda.md:60-69`) binds exactly the same
  hypothesis, and there it is CORRECT: the trophy is the conclusion of the
  whole development, so binding only `IsCardinalL κ` is right for it and wrong
  for one step of it. **The shape is not spreading. No cure is owed to `src/`.**

I also counted the consumers of the ambient square law, because a
"replace the ambient one" plan would have to pay them: `sq` is consumed at
**4 sites** outside its own two chapters, `src/L/StageBound.lagda.md:46` and
`:139`, `src/L/BoundedSubset.lagda.md:1388`, `src/L/StageCardinal.lagda.md:17`,
plus the base case `squareω` at `src/L/InjChain.lagda.md:184`. **Every one of
them wants the AMBIENT `sq` and none wants an internal one.** So an internal
square law is new surface, not a replacement, and nothing in `src/` is made
stale by this stop.

## WHAT THIS BUYS `Codes`

`[LJ-1.552]`'s step 1 is an INTERNAL injection code `a ↪ κ` for each member
`a` of `δ`, and what I built does not touch it: it still needs
`InternalLeastCard` (`src/L/Cardinal.lagda.md:235`) to produce the code, with
`L.InjChain.InclGraph` (`src/L/InjChain.lagda.md:575`) for its non-emptiness
and `L.InjChain.Comp` (`src/L/InjChain.lagda.md:314`) to compose down to κ,
exactly as `[LJ-1.552]` wrote it and with the two checks it flagged still
unchecked (`agents/tasks/LJ-1-552/review-of-succ-assignment.md:181-184`).
**What section 1 does buy is that step 3, the separation that carves the coded
subset out of κ by `hasSeparationL`, now has a domain object to name**, since
`κ × κ` is an L-set with untruncated projections, so the two steps compose as
`[LJ-1.552]` expected AT THE LEVEL OF THE OBJECTS. **They do not compose as it
expected at the level of the price**: `[LJ-1.552]` priced step 2 as "a chapter
and not a task" (`agents/tasks/LJ-1-552/review-of-succ-assignment.md:190`) and
this task measures that the chapter is TWO walls and not one, only one of
which is a price.

## ARCHIVE USED

The brief's corpus search returned five candidates. Every one is named.

- **`archive/dev/LJ-dispatch-index.md`**: READ. `:100` says
  "| LJ-1.51 | Discharge the five hypotheses | 2 of 5, plus the sq master | fin-inj and Mext DISCHARGED. SquareLaw lands as a 775-line master. cover and levelIn survive on the hull adequacy |".
  This is premise 10's basis, and it is a number in a paragraph, which
  AGENTS.md:17-18 makes inadmissible. **The admissible source contradicts it**:
  `scripts/measure/ledger.py` reports
  "HOT  L.Ordinal.SquareLaw         64s over   907 lines = 0.07 s/line", so
  the brief's estimate basis is stale by 132 in-fence lines. It changes no
  verdict here.
- **`archive/dev/JOURNAL-archived.md`**: READ. `:2001` says
  "requires `⟨ ω ∈ˢ α ⟩` (`src/L/Ordinal/SquareLaw.lagda.md:947-949`), so `Init ω` would need `ω ∈ ω`,".
  It records that `Init` is the load-bearing hypothesis and that ω is outside
  it, which is why `src/L/InjChain.lagda.md:184` carries `squareω` separately.
  Its line numbers into `SquareLaw` are stale (947-949 is now 692-698); I used
  the live file for every citation in this report.
- **`archive/dev/JOURNAL.md`**: READ. `:939` says
  "name no function. `src/L/Ordinal/SquareLaw.lagda.md:685-687` and".
  Same staleness; I did not rely on it.
- **`archive/dev/STATUS-archived.md`**: READ. `:108` records that
  `L.Ordinal.SquareLaw` went "856 s to 64.4 s in one day". I read it to check
  whether the chapter's cost would make an internalization unaffordable on
  time alone. It does not: the wall here is a missing formula, not a price.
- **`dev/ARCHIVE.md`**: NOT USED, declined in writing. I grepped it for
  `SquareLaw` and for `square` and it has no entry for either: no module of
  this chain has ever been retired, so the registry has nothing to say about
  this task.

## LITERATURE USED

The brief's corpus search returned five candidates. Every one is named.

- **`dev/literature/devlin-II5.md`**: READ. `:281` says
  "(ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact".
  1.1(vii) is the source the ambient chapter names in its own first paragraph.
  The dossier confirms the source is used only through cardinality facts and
  never through a named injection, which is consistent with the tree keeping
  the square law ambient.
- **`dev/literature/truncation-and-selection.md`**: READ. `:83` says
  "**So a proof that only needs cardinal arithmetic never needs an injection as".
  This is why `InternalSquare` in the probe is TRUNCATED: the consumer needs
  the existence of a code, not a chosen code, and truncating costs nothing
  here.
- **`dev/literature/terms-2026-08.md`**: NOT USED, declined. Not read. It is
  the terminology dossier for the owner's naming ruling, and this task names
  nothing new and adds no glossary entry.
- **`dev/literature/digest.md`**: NOT USED, declined. Not read. It pins the
  orthodox form of the RUD route, and this task is on the collapse route.
- **`dev/literature/glossary-review-2026-08.md`**: NOT USED, declined. Not
  read. It reviews the pre-protocol glossary entries, and I added no glossary
  entry, which the Boundary forbids me to do anyway.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **DO NOT RE-DISPATCH THE BRIEF'S TYPE.** It is under-hypothesized. Fund
   `SquareStep` (probe section 4) or fund nothing.
2. **THE FIRST PAYABLE PIECE IS THE `Step` FORMULA FOR `col`, AND IT IS ONE
   OBLIGATION.** Instantiate `RecShape` (`src/L/Coding/Sequence.lagda.md:281`)
   at `dom = Square.sqL κ` with `Step` saying `z = ⋃ { sucV (f r) : r ≺ c }`.
   The order enters as a FORMULA, so section 2's device carries it and no
   order-as-a-set is needed. That is a task, and it is the only part of this
   chapter that is.
3. **THE PARTS ALREADY BANKED ARE IN `Probe556.agda` AND ARE TRACKED.**
   Sections 1 and 2 are green Agda that a chapter can copy: the product, its
   two readings, and the pattern for turning a condition on the components
   into a formula and then into a set.
4. **NOTHING SHOULD BE FUNDED AGAINST THE 775-LINE FIGURE.** It is a number
   in a paragraph of `archive/dev/LJ-dispatch-index.md:100` and AGENTS.md:17-18
   refuses it. `scripts/measure/ledger.py` measures the master at **907
   in-fence lines and 64 s**. The internalization is not proportional to it
   anyway: five of its six pieces are order data that becomes one formula, and
   the sixth is a hypothesis rather than a construction.

## WHAT WAS NOT DONE

No postulate, no hole, no module parameter that asserts the square law. `src/`
is untouched. No term named `square-inside-L` exists in any file of this task.
I did not build `Codes δ κ` and I did not touch the assignment; `[LJ-1.557]`
takes the other decomposition step. I did not try to code the ambient
injection: the brief forbids it and `[LJ-1.533]` already measured it. I did
not prove the adequacy of the max-then-lexicographic condition and I do not
claim it. I did not set `GHCRTS`. I did not run `make check`, because I
committed nothing. I did not commit and did not push.
