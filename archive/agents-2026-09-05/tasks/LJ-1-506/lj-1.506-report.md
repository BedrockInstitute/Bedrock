# [LJ-1.506] report: the arity truncation, and where the code set comes from

## VERDICT

**GO, AND THE FRAME IS THE BLOCKER, NOT THE MATHEMATICS.**

Three results, all at exit 0:

1. **The truncation IS derivable from the code set's own construction.** The
   term is four lines. It uses no `TFacts` field.
   `agents/tasks/LJ-1-506/Probe506.agda:79-86`.
2. **The brief's type with `C` left a bare `S` is FALSE.** I built the
   counterexample and machine-checked the refutation.
   `agents/tasks/LJ-1-506/Probe506.agda:143-150`.
3. **So the frame needs exactly ONE new entry, and it is an equation:**
   `fst (lookup C γ') ≡ fst (AllCodes A)`. That entry is enough. Nothing else
   in the telescope changes. `agents/tasks/LJ-1-506/Probe506.agda:160-173`.

**`codesK` is neither an assumption nor a theorem today. It is a theorem about a
set the frame does not name.** The record asks the question at a slot, and a
slot has no members to speak of. Name the set and the fourth component is
proved.

**THE EQUATION IS CHEAPER THAN THE ONE THAT STALLED BEFORE.** `[LJ-1.86]`
stopped because `witK` needs `AllCodes A` INSIDE the bound `Lset lam`, and
`lam` is a module parameter at every frame
(`archive/dev/LJ-dispatch-index.md:160`). **The arity truncation needs no such
membership.** `AtSlot` (`Probe506.agda:160-162`) names `A`, `C` and `γ'` and
nothing else. It never mentions `lam` or `K`.

## WHERE THE CODE SET COMES FROM

**AT `KValue`'s FRAME THERE IS NO CODE SET AT ALL.**

- `KValue` builds `Kenv : S ^ 14` at `src/L/Condensation.lagda.md:7389-7392`.
  The fourteen slots are the carrier `LsetS gam ordγ`, the bound
  `LsetS lam ordλ`, and the twelve arity tags `numeralL 0` to `numeralL 11`.
  **No slot holds a code set.**
- `KValue` supplies a `KFacts` value at `src/L/Condensation.lagda.md:7411`.
  `KFacts` is declared at `src/L/Condensation.lagda.md:6079-6115`, and **it has
  no `codesK` field.** Its fields are twelve `tagEq`, twelve `numK`, `innerK`,
  `innerPairK`, `pairK`, `carrierK` and `arityK`.

**THE CODE SET FIRST APPEARS ONE FRAME UP, AND IT IS A PARAMETER THERE.**

- `TFacts` is declared at `src/L/Condensation/TwelveAgree.lagda.md:129-131`
  over `(γ' : S ^ (11 + n))`. The code set is `lookup (suc (suc zero)) γ'`,
  used first at `:162`. **`γ'` is a bare vector of `S`. Nothing constrains slot
  two.**
- `AbstractFrame` (`src/L/Condensation/TwelveAgree.lagda.md:337-343`) takes the
  same `γ'` and the `TFacts` value. Its telescope adds `sucK` only. **It states
  no equation about slot two.**
- **`AbstractFrame` HAS NO CONSUMER IN `src/`.** `grep -rn "AbstractFrame" src/`
  returns two lines: a comment at `:70` and the declaration at `:337`. **And no
  `TFacts` VALUE exists anywhere:** `grep -rn "TFacts" src/` returns three lines,
  the declaration at `:129`, the parameter at `:342` and the `open` at `:345`.

**SO THE ANSWER TO THE BRIEF'S QUESTION IS: PARAMETER.** At `KValue`'s frame
the set is absent, and at the frame that names it the set is an unconstrained
slot.

**BUT THE CONSTRUCTION EXISTS, AND IT IS NOT FAR AWAY.** `AllCodes A` is built
at `src/L/Coding/CodeSet.lagda.md:440`, by separation over `smallDom`'s superset
using the object-language predicate `isCodeAny A` (`:248`). **Its first conjunct
is `arityNumAtL` (`:185-187`), and that conjunct exists FOR THIS EXACT PURPOSE.**
The chapter says so at `src/L/Coding/CodeSet.lagda.md:24-27`:

> Shapedness binds the arity existentially and puts no condition on it, so a set
> holding a pair whose first component is not a numeral at all satisfies both
> halves, and the decode has nothing to say about that pair.

**AND YES, THE CONSTRUCTION FORCES THE FIRST COMPONENT TO BE A NUMERAL.**
`AllCodes-out` (`src/L/Coding/CodeSet.lagda.md:449`) returns `IsKeyOverAny`,
whose payload is a formula. `key {n} φ = pr (# n) VCode.⌜ mapFo f φ ⌝`
(`src/L/Coding/InL.lagda.md:253`) puts the arity numeral in the first component
**by definition**. W3 measured that: `codeset-numeral`
(`agents/tasks/LJ-1-506/Probe506.agda:56-59`) is `PT.map` and nothing else. **No
`subst`, no transport, no equation lemma.**

## THE OBLIGATION

`ar-is-numeral` at `agents/tasks/LJ-1-506/Probe506.agda:79-86`. Exit 0.

    ar-is-numeral : (A C : S) → fst C ≡ fst (AllCodes A)
                  → (k : ℕ) (c ar a b : S)
                  → ⟨ fst c ∈ fst C ⟩
                  → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
                  → ∥ (Σ[ n ∈ ℕ ] (fst ar ≡ # n)) ∥₁

**IT IS THE BRIEF'S TYPE PLUS ONE HYPOTHESIS, AND I STATE THAT PLAINLY.** The
brief said not to add a numeral hypothesis and not to weaken the truncation. **I
did neither.** `fst C ≡ fst (AllCodes A)` says nothing about any arity. It names
the code set. The brief asked for the term to come "from the code set's own
construction", and a construction cannot speak to a slot that could hold any set.

The body is `PT.map` over `codeset-numeral`, with `pr-inj`
(`src/V/Coding.lagda.md:178`) as the whole of the step. The brief's shape
equation and the code set's own equation are two readings of `fst c`, so their
first components agree.

**THE UNARY FORM COSTS NOTHING MORE.** `ar-is-numeral-un`
(`Probe506.agda:91-98`) discharges `codesK-un`
(`src/L/Condensation/TwelveAgree.lagda.md:168-172`) with the same two lines at a
shorter shape equation.

**THE SLOT FORM IS `AtSlot`** (`Probe506.agda:160-173`). It reaches the set
through `lookup C γ'`, which is the form `codesK` uses at
`src/L/Condensation/TwelveAgree.lagda.md:162`. It is the module a repaired
frame would apply.

## THE HYPOTHESIS IS NECESSARY, AND THIS IS MEASURED

`bare-C-is-not-a-theorem` (`Probe506.agda:143-150`), exit 0:

- `badPair = prʟ ωʟ (prʟ (numeralL 0) (prʟ ωʟ ωʟ))` (`:122-123`). Its first
  component is `ω`.
- `badSet = sucʟ badPair` (`:125-126`), and `badPair` is a member of it by
  `self∈sucV` (`:128-130`).
- `bad-shape` (`:132-137`) gives the brief's shape equation exactly, at `k = 0`.
- `ω-not-numeral` (`:139-141`) closes it: `# n ∈ ω` by `#∈ω`
  (`src/L/Ordinal.lagda.md:248`), so `ω ≡ # n` gives `ω ∈ ω`, refuted by
  `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`).

**THIS IS THE SAME SHAPE `[LJ-1.84]` MACHINE-CHECKED IN JULY**, at `witK`
instead of at `codesK`: "Shapedness leaves the arity slot free, so a junk member
`pr K (pr #6 0)` keeps `w` closed and shaped and lifts its rank past `K`"
(`archive/dev/LJ-dispatch-index.md:158`). **I found that row after I built the
refutation, not before.**

## THE C-42 SWEEP

C-42 says a refutation measures one site and never measures how far the site
extends, so the count comes before the cure.

**COUNT: 25 declarations in `src/` state `codesK` or `codesK-un` over a bare
code slot, and ALL 25 carry the truncation.** Not one of them is a definition.
Every one is a module hypothesis or a record field.

| Where | Count |
|---|---|
| `src/L/Condensation.lagda.md` | 19 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 2 |
| `src/L/Condensation/UpperAgree.lagda.md` | 2 |
| `src/L/Condensation/LowerAgree.lagda.md` | 2 |

The three record fields are at `TwelveAgree:162` and `:168`, `UpperAgree:116`
and `:122`, `LowerAgree:116` and `:122`. The nineteen module hypotheses in
`src/L/Condensation.lagda.md` are at `:2782`, `:3292`, `:3544`, `:3599`,
`:3674`, `:3747`, `:3860`, `:3972`, `:4154`, `:4422`, `:5022`, `:5151`,
`:5279`, `:5380`, `:6400`, `:6554`, `:6655`, `:6694` and `:6985`.

**THE SHAPE EXTENDS FURTHER THAN THE TERM I BUILT.** `valK` and `valK-un` add
**23 more declarations** over the same bare code slot (19 `valK`, 4 `valK-un`).
**I did not refute those.** They conclude a membership in `K` rather than a
numeral, so my counterexample does not reach them without more work. **I report
the count and I do not price the cure**, because I did not measure it.

`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` occurs **87 times** in `src/`: 50 in
`L/Condensation.lagda.md`, 11 in `TwelveAgree`, 8 in `LowerAgree`, 8 in
`UpperAgree`, and 10 in `L/Coding/EnvSupply.lagda.md`.

## WHAT THE ARCHIVE ALREADY KNEW

**THE DEBT WAS RECORDED IN JULY AND IT WAS NEVER PAID.**
`archive/dev/LJ-dispatch-index.md:157` reads:

> | LJ-1.83-A | Orchestrator audit: C = K is a probe convenience | OWED, RECORDED | The real C is AllCodes, needing AllCodes in K, unproved. The stop at witK is independent of the choice |

The four rows after it walked this exact route:

- `:158` `[LJ-1.84]` refuted `witK` at a bare slot, machine-checked.
- `:159` `[LJ-1.85]` found the premise: "w in AllCodes A kills the refutation and
  the closure supplies it."
- `:160` `[LJ-1.86]` proved a stage exists and stopped: "`AllCodes-stage` is
  green. But `lam` is a module parameter at every frame, so the obligation moves
  to the frame."

**THE ARITY TRUNCATION IS THE PART OF THAT DEBT THAT DOES NOT NEED THE STAGE.**
`[LJ-1.86]` stopped on `AllCodes A ∈ Lset lam`. My `AtSlot`
(`Probe506.agda:160-162`) does not mention `lam`, `Lset` or `K`. **So this one
component can be paid now, and the stage question stays where `[LJ-1.86]` left
it.**

## PRICES

One Agda process per run. `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set on
the pane by the program and untouched. Three forced rechecks each, by deleting
`_build/2.8.0/agda/agents/tasks/LJ-1-506/Probe506.agdai` before every run.

| Stage | Median wall | Peak RSS | Runs |
|---|---|---|---|
| W3 alone, 60 lines | **1.42 s** | **321.8 MiB** (337,379,328 B) | `runs/w3-r0.time` to `w3-r2.time` (1.43, 1.41, 1.42) |
| Full file, 202 lines | **2.07 s** | **400.0 MiB** (419,446,784 B) | `runs/full-r0.time` to `full-r2.time` (2.08, 2.05, 2.07) |

**NO HEAP WALL. NO WARNING except one I fixed:** `self∈sucV` comes from
`V.Model`, not from the Cubical `Properties` module (`runs/refute-0.out`).

**AGAINST THE ESTIMATE.** The brief priced W3 at "about 15 lines of reading and
under 25 seconds of Agda", and the file at "about 120 lines, of which the
obligation is about 30". **W3 cost 1.42 s, not 25.** **The obligation cost 8
lines, not 30** (`Probe506.agda:79-86`). **The file is 202 lines, not 120**, and
the excess is the refutation and the two frame modules, neither of which the
brief asked for. I report the numbers I measured, not the numbers the brief
guessed.

The reason the obligation is cheap is the reason W3 was the whole task:
`arityNumAtL` was written in advance to pay this debt, and `key` puts the
numeral in the first component definitionally. **There was nothing left to prove
once the set was named.**

## W2 (DD4), ANSWERED

**The mathematics is already written once, and I copied none of it.**
`AllCodes` and `arityNumAtL` sit at a generic carrier `A : S` in
`src/L/Coding/CodeSet.lagda.md`, and both wings reach them by import.

**ONE W2 FLAG FOR THE MATHEMATICIAN.** The object-language pin already exists,
but **it lives on the Choice wing**: `CodesAt` at
`src/L/Choice/Faithful.lagda.md:334`, with `CodesAt-out` at `:339` returning
the very equation `AtSlot` takes as a hypothesis. `Pinned`
(`Probe506.agda:191-202`) applies it, so the route is checked. **If the
condensation frame wants that pin, DO NOT COPY IT.** W2 says move it down beside
`AllCodes` in `L.Coding.CodeSet` and let both wings share the one copy. The
probe copies nothing.

## WHAT THE NEXT BRIEF NEEDS

1. **The frame entry to add.** One equation on `AbstractFrame`
   (`src/L/Condensation/TwelveAgree.lagda.md:337-343`) and on the two partial
   frames: the identity of slot two. Then `codesK`'s fourth component stops
   being a field and becomes a derivation, at all 25 sites.
2. **A decision the mathematician owns, not me.** `TFacts` has 59 field
   positions and no value. Adding an equation to the frame moves the fourth
   component out of `codesK`, which changes `codesK`'s TYPE at 25 sites. **That
   is a record redesign and it is not a coder's call.**
3. **The `valK` question is open.** 23 declarations state `valK` or `valK-un`
   over the same bare slot. **Nobody has asked where those come from either.**
   My counterexample does not settle them.
4. **`[LJ-1.504]`'s third difference is now the only one left, and it is
   payable.** That report calls it "NOT CLOSED. IT IS THE WHOLE REMAINING
   DISTANCE" (`agents/tasks/LJ-1-504/lj-1.504-report.md:46`), and
   `gap-suffices` (`agents/tasks/LJ-1-504/Probe504.agda:133-138`) proved the
   truncation sufficient for `someEnv`. **The truncation now has a proof. It
   needs the frame to name its code set.**

## THE WORKING TREE

`git status --porcelain` returns one line: `?? agents/tasks/LJ-1-506/`.

**NOTHING LANDS IN `src/`.** Nothing is committed and nothing is pushed. The
directory holds the brief, this report, `review-of-ar-is-numeral.md`,
`Probe506.agda`, and `runs/`. `runs/Probe506.w3-only.agda.txt` is the exact
60-line file the W3 rows were measured on.

Individual gates run clean on the new files: `check-probes.py --check` reports
"clean (5112 tracked files, no probe outside agents/tasks/ and no generated
file)"; `lint-prose.py`, `check-glossary.py` and `lint-agda.py` all return 0
when called with the new paths as arguments. **I called them with explicit paths
on purpose.** `lint-prose.py` and `check-glossary.py` discover their inputs
through `git ls-files`, so an untracked file is skipped silently
(C-8, `archive/dev/JOURNAL-archived.md:3913-3918`).

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ, and it changed the report.**
  `archive/dev/LJ-dispatch-index.md:157` reads:
  `| LJ-1.83-A | Orchestrator audit: C = K is a probe convenience | OWED, RECORDED | The real C is AllCodes, needing AllCodes in K, unproved. The stop at witK is independent of the choice |`
  Rows `:158`, `:159` and `:160` carry the rest of the route and I quote `:160`
  in the body.
- **`archive/dev/JOURNAL-archived.md` READ.** `archive/dev/JOURNAL-archived.md:3932`
  reads:
  `  (ii).** \`AllCodes-closed\` is bound to the same fork.`
  It records the 2026-07-29 ruling that generalized the code predicate to take
  the carrier as a SLOT. **That ruling is why the code set is a slot today**, so
  it is the origin of the shape this task measured. `AllCodes-closed` was retired
  with it, so there is no closure fact left to reuse.
- **`archive/dev/JOURNAL.md` NOT READ, declined.** I grepped it for `codesK`,
  `AllCodes`, `arityNum` and `code set` and it returned nothing. The dispatch
  index carried the same period at a higher density.
- **`dev/ARCHIVE.md` READ, one row, and DECLINED as a source.**
  `dev/ARCHIVE.md:266` names `L.Rud.CodePred`, an object-language code predicate
  that died with the route change ruled in D18. **It is a retired route and I
  took nothing from it.** I checked it only to be sure the live `arityNumAtL` is
  not a survivor of a dead design. It is not.
- **`archive/dev/ORCHESTRATION.md` NOT READ, declined.** It is the archived
  orchestration document. I grepped it for `codesK`, `AllCodes`, `arityNum` and
  `code set` and it returned nothing. This task is about a term in the tree, not
  about how the loop is run.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md` READ, and it is the right file
  for this task.** `dev/literature/truncation-and-selection.md:146` reads:
  `**The constraint the route carries: \`P\` must be \`hProp\`-valued.** So \`leastOf\``
  **The finding for this task is that NONE of that machinery is needed here.**
  The whole chain from `AllCodes-out` to `ar-is-numeral` stays inside `∥_∥₁`:
  `PT.map` twice and no `PT.rec` into data, so no selection happens and no
  criterion has to be met. The one `PT.rec` in the file
  (`Probe506.agda:140`) lands in `Empty.⊥`, which is a proposition.
- **`dev/literature/devlin-II5.md` READ, and DECLINED as a source for the term.**
  `dev/literature/devlin-II5.md:137` reads:
  `> smallest M ≺ L_α such that X ⊆ M. For this M, |M| = max(|X|, ω).`
  Devlin's II.5 is the definable hull and its cardinality. **The arity truncation
  is a coding fact, not a hull fact**, and no classical source states it, because
  in a classical treatment the arity is metalinguistic and never needs to be
  pinned from outside. `src/L/Coding/CodeSet.lagda.md:22-27` says exactly that.
- **`dev/literature/digest.md` NOT READ, declined.** It is the cross-source
  digest. The two files above cover the two questions this task asked, and a
  digest adds no `file:line` that either lacks.
- **`dev/literature/geology.md` NOT READ, declined.** Fine structure and the
  geology of `L`. This task did not reach fine structure.
- **`dev/literature/terms-2026-08.md` NOT READ, declined.** It is terminology
  provenance. I added no term and I proposed no glossary entry.
