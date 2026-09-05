# [LJ-1.580] report: give `β↪α` a code

## HEAD
head_slot: coder
machine: shared
task: LJ-1.580
obligation: agents/tasks/LJ-1-580/Probe580.agda::beta-into-alpha-coded
verdict: NO-GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-580/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **NO HEAP EVENT**: the largest maximum resident set size of any run
is 1,977,024,512 bytes, about 1.84 GiB, against the 8 GB cap
(`agents/tasks/LJ-1-580/runs/final-1.out`). No run gave exit 251 and no run
printed a heap message. Nothing is postulated, the probe carries `--safe`, and
there is no hole. Nothing lands in `src/`. The probe is a raw `.agda` file, so
it carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar
cannot fire on it.

## VERDICT

**NO-GO on `beta-into-alpha-coded`**, and
`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md` states it.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS** (`runs/final-1.out` to
`runs/final-3.out`). Green and not holed is deliberate: every reduction in the
file is then a measurement and not a claim.

**THE ANSWER IN FOUR LINES.**

1. **LEG 1 IS CODED, AND IT IS BUILT HERE.** `leg1-coded : InjCode Leg1.G βᴸ πXᴸ`
   (`agents/tasks/LJ-1-580/Probe580.agda:232`). Half the composite is paid.
2. **LEG 2 IS NOT BUILT FROM L-DATA, AND `[LJ-1.577]`'S PREMISE 5 IS WRONG ON
   THAT POINT.** Leg 2's value is computed from `absorbs`, a bare ambient
   injection that is a free parameter of the module. `count-applies-absorbs`
   (`Probe580.agda:148`) is the elaborator's word for it, by `refl`.
3. **WHAT REMAINS IS EXACTLY ONE STATEMENT, AND IT IS ABOUT A STAGE.**
   `residue-is-a-stage-bound` (`Probe580.agda:311`) proves the residue equals
   `InjL (Lset β) α`: **in L, the stage `Lset β` injects into α.**
4. **THE ROUTE THROUGH `β↪α` CANNOT DELIVER THAT, BUT NOTHING HERE REFUTES THE
   STATEMENT ITSELF.** This is a construction gap, not a mathematical
   obstruction, and the report says which one at every line.

**I DID NOT ATTEMPT ROWS 2 TO 5, AND I DID NOT ATTEMPT A CODE FOR AN ARBITRARY
AMBIENT INJECTION.**

## D-10: BEFORE ANY AGDA

The brief ordered the two legs named at `file:line` before any Agda, and
ordered me to say if one of them is not built from L-data after all. The
reading below was done first; SECTIONS 2 to 6 of the probe then measured it.

`β↪α` (`src/L/BoundedSubset.lagda.md:1578-1582`) is

    β↪α = comp-inj (subst (λ A → ⟪ β ⟫ ↪ ⟪ A ⟫) (sym ext)
                     (SC.stage-card-lower β β-isOrd))
                   πX↪α

`two-legs` (`agents/tasks/LJ-1-580/Probe580.agda:192`) is `refl` on that, so
the split below is the elaborator's and not a reading of the page.

## THE TWO LEGS

| | leg | `file:line` | coded today | can it be given one |
|---|---|---|---|---|
| 1 | the stage-cardinality bound at β, moved along `ext` | `src/L/BoundedSubset.lagda.md:1580-1581`, body `src/L/StageCardinal.lagda.md:209-211` | **no** | **YES, AND IT IS BUILT HERE** |
| 2 | `πX↪α`, the code selection after the inverse collapse | `src/L/BoundedSubset.lagda.md:1574-1576` | **no** (W3) | **NO at today's tree** |

### Leg 1: the stage-cardinality bound at β. CODED, and the price is 26 lines

**IT IS AN INCLUSION AND NOTHING MORE.** `stage-card-lower`
(`src/L/StageCardinal.lagda.md:209-211`) is `Lower.ord-inj` (`:197-198`), the
fibre coercion of `α⊆Lset` (`:193-195`): the members of an ordinal lie in its
own stage. So leg 1 is β ⊆ Lset β, moved to the collapse by `ext`
(`src/L/BoundedSubset.lagda.md:1568`).

**AND THE TREE CODES ANY INCLUSION BETWEEN TWO L-ELEMENTS.** `InclGraph`
(`src/L/InjChain.lagda.md:575-598`) carves the graph with `inclFo`
(`:445-446`) through `hasSeparationL`, and `Carve` proves the four conjuncts at
one `G` (`:518`, `:525`, `:532`, `:544`). `leg1-coded`
(`agents/tasks/LJ-1-580/Probe580.agda:232`) packs them.

**`[LJ-1.566]`'S TUPLE WARNING DID NOT FIRE HERE, AND I RE-MEASURED RATHER THAN
ASSUMED.** `[LJ-1.566]` found that three conjuncts from three SPELLINGS of one
carve do not elaborate (`agents/tasks/LJ-1-566/lj-1.566-report.md:38-42`). Here
the four come from ONE `Carve` at ONE `G`, which is the shape `src/` already
packs at `src/L/Absorption.lagda.md:619-620`. The pack cost nothing measurable:
`runs/s4-1.out` is 8.46 s against `runs/s3b-1.out`'s 8.24 s.

**TWO LEVEL-HOOD FACTS WERE NEEDED AND ONE IS NEW.** `Comp` composes
L-elements, so the intermediate object must be one.

- `ord-isL` (`Probe580.agda:95`): every ordinal is an L-element.
  `[LJ-1.386]`'s one-liner, restated rather than imported because
  `L.SquareLawClosed` takes an ordinal parameter this file has no use for
  (`src/L/SquareLawClosed.lagda.md:19-20`, `:51-52`).
- `Lset-isL` (`Probe580.agda:104`): **EVERY STAGE OF THE TOWER IS AN
  L-ELEMENT.** `grep -rn "isL (Lset" src/` returns nothing, so this shape was
  not in the tree. It is one line from `defSet ⊤̇ ≡ A`
  (`src/L/Definability.lagda.md:178`) and `Lset-in`
  (`src/L/Constructible.lagda.md:319`).

### Leg 2: the code selection. NOT CODED, and NOT built from L-data

**W3 SETTLED WHAT THE LEG DELIVERS, IN 3.04 SECONDS.** `delivered = CSel.leg2`
(`Probe580.agda:73-74`, `runs/w3-1.out`, GREEN) ascribes `CodeSelect`'s output
at its own parameters: `⟪ M ⟫ ↪ ⟪ α ⟫`, a bare `_↪_` with no `Formula` in the
type and no `InjCode`. **The leg does not already carry what the obligation
needs, so the brief's "half the obligation is delivered" case did not fire.**
The other half fired instead, for a different reason.

**AND THE LEG'S VALUE IS COMPUTED FROM `absorbs`.**
`count-applies-absorbs` (`Probe580.agda:148`) is `refl`:

    CC.count (base m) ≡ B.pair (B.numeral 0)
                          (fst (stage-card-upper α ordα _ α∉ω) (fst absorbs m))

The chain, each link at its own line: `CSel`'s counting parameter is `CC.count`
(`src/L/BoundedSubset.lagda.md:1518-1520`); `CC` is `CodeCount code-inj`
(`:1515`); `code-inj` is `comp-inj absorbs (stage-card-upper ...)`
(`:1512-1513`); and `absorbs` is the twelfth parameter of
`Devlin55.BoundedSubsetAt` (`:1392`), a bare `_↪_`.
`leg2-is-code-selection` (`Probe580.agda:197`) is the matching `refl` for the
other half of the composite: leg 2's function is `CSel.h ∘ IC.inv`
(`src/L/BoundedSubset.lagda.md:1518`, `:1517`).

**NOTHING IN `src/` SUPPLIES `absorbs`.** `grep -rn "absorbs" src/` outside
`src/L/BoundedSubset.lagda.md` gives only `src/L/StageBound.lagda.md:69`,
`:76`, `:97`, `:116`: a parameter passed on, never applied and never built.
`src/L/Absorption.lagda.md:635` is a DIFFERENT shape,
`⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`, and it does not fit the slot. The tree records
this already: `dev/memos/2026-08-16-pause.md:397` reads "`absorbs :
AbsorbsShape` are Pi-parameters that nothing supplies".

**SO `[LJ-1.577]` IS WRONG ON ITS PREMISE 5, AND THE BRIEF ORDERED THIS SAID.**
`agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md:79-81` reads
"`β↪α` is the composite of a stage-cardinality bound and a code selection over
the hull's term algebra, and both legs are built from L-data." **Leg 1 is. Leg
2 is not.** `[LJ-1.577]` also said this is "not `[LJ-1.533]`'s wall"; at leg 2
it is that wall, because the leg's value is a function of an ambient injection
that carries no code (`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`).

**ONE THING `[LJ-1.577]` GOT RIGHT AND I DID NOT EXPECT.** The hull's Skolem
search is NOT over an arbitrary ambient order. `wL = orderAt α ordα`
(`src/L/Hull.lagda.md:158-159`) is the tree's own stage order from
`L.Choice.Step`, which is the literature's `<δ`
(`dev/literature/truncation-and-selection.md:56-57`). So the port matches
Devlin and Jech at the selection device. The gap is elsewhere, and it is
`absorbs` plus the term algebra's metatheoretic `Code`
(`src/L/Hull.lagda.md:72-74`), which no set of the tree presents.

## WHAT REMAINS, AS ONE TYPE

`Comp` (`src/L/InjChain.lagda.md:314-433`) composes two coded injections by
separation and not by replacement. With leg 1 coded, the obligation is leg 2's
code and nothing else:

| term | `Probe580.agda` | what it says |
|---|---|---|
| `leg2-coded→at-β` | `:245` | `InjL πXᴸ αᴸ → InjL βᴸ αᴸ` |
| `at-β→at-κ` | `:263` | under κ ⊆ β, carries the code to the pair the STEP spends at |
| `BetaIntoAlphaCoded` | `:292` | the obligation's TYPE, `gap-is-a-code`'s antecedent |
| `Leg2Coded` | `:296` | the residue |
| `obligation-from-leg2` | `:303` | `Leg2Coded → BetaIntoAlphaCoded` |
| `residue-is-a-stage-bound` | `:311` | `Leg2Coded ≡ InjL (Lset β) α` |
| `gap-closed` | `:320` | `Leg2Coded → GapAtPair βᴸ αᴸ`, through the IMPORTED interface |

`obligation-from-leg2` carries `Leg2Coded` to the left of its arrow. **It is
not the obligation and it is not offered as one.** It does not even read the
ambient injection: once leg 2 is coded, the ambient input is dead weight.

**THE INTERFACE IS IMPORTED AND NOT RESTATED**, as the brief ordered:
`open import LJ-1-577.Probe577 {ℓ} lem using ( GapAtPair; gap-is-a-code )`
(`Probe580.agda:34`).

**AND THE PAIR MATTERS.** `[LJ-1.577]`'s critic wrote that the slogan "give
`β↪α` a code" types `InjL` at β while the step spends at (κ , α), and that "the
next brief must take `gap-is-a-code`, not the slogan"
(`agents/tasks/LJ-1-577/review-of-LJ-1-577-1.md`, question 3). `at-β→at-κ`
(`Probe580.agda:263`) is the bridge: in both refuted branches κ ⊆ β, and a
coded inclusion plus `Comp` carries the code across.

## THE SWEEP (C-42), RE-MEASURED HERE

`grep -rn "InjCode" src/` at today's tree. `src/` has exactly TWO producers and
both deliver the single shape `InjCode F (sucʟ γ) γ`:
`src/L/Absorption.lagda.md:611-614` and `src/L/CodedShift.lagda.md:40`.
**Neither is a stage bound.** This agrees with `[LJ-1.577]`'s count and is
re-grepped, not carried over.

`grep -rn "isL (Lset" src/` returns **zero** lines, which is why `Lset-isL` had
to be built.

`grep -rn "absorbs" src/` returns twelve lines. Two are in
`src/L/BoundedSubset.lagda.md` (the telescope slot `:1392` and its one use at
`:1513`), four are the pass-through chain in `src/L/StageBound.lagda.md`
(`:69`, `:76`, `:97`, `:116`), three are `src/L/Absorption.lagda.md`'s
different shape (`:630`, `:635`, `:638`), and three are English prose in
unrelated masters.

## WHAT THIS DOES TO ROW 1

**ROW 1 IS NOT PAYABLE TODAY, AND THE REASON IS NARROWER THAN IT WAS.**

Before this task the demand was "give `β↪α` a code", with two legs and neither
measured. After it:

- **leg 1 is paid** (`leg1-coded`, `Probe580.agda:232`);
- **leg 2 is the whole remainder**, and it is not a code for an arbitrary
  ambient injection: it is `InjL (Lset β) α`, an internal size bound on ONE
  stage at ONE pair (`residue-is-a-stage-bound`, `:311`);
- **the composition is in the tree already** (`Comp`,
  `src/L/InjChain.lagda.md:314-433`), so nothing between the legs is owed;
- **the bridge from (β , α) to the pair the step spends at is built**
  (`at-β→at-κ`, `:263`).

**I DID NOT READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.** `InjL πXᴸ αᴸ`
is not inhabited in this file, is not postulated, and has no producer in
`src/`. Row 1 stays open, and `IsCardinal` stays spent at
`src/L/BoundedSubset.lagda.md:1597` and `:1601` exactly as `[LJ-1.577]`
measured.

**WHAT IT WOULD TAKE.** `[LJ-1.568]` settled the general law: `Def`
(`agents/tasks/LJ-1-568/Probe568.agda:189-190`) is sufficient
(`def-restricted`, `:252-253`) and every sufficient hypothesis implies it
(`weakest`, `:377-381`). So the residue is a demand for ONE formula, with
parameters in L, describing an injection of `Lset β` into α. That is Devlin
1.1(vii)'s size equation read internally (`dev/literature/devlin-II5.md:156`).
This task did not find that formula and did not price finding it.

## WHAT TYPECHECKED

One Agda process at a time, caliber `-A64m -I0 -M8g` taken from the pane,
never set by this task.

| run | what | result | peak RSS (bytes) |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, SECTION 1, typechecked ALONE as ordered | GREEN, 3.04 s | 580,747,264 |
| `runs/s2-1.out` | + the site | EXIT 42, `IsCardinal` not in scope | 708,083,712 |
| `runs/s2-2.out` | after the import list was extended | GREEN, 8.16 s | 1,729,216,512 |
| `runs/s3-1.out` | + the two legs and `two-legs` | GREEN, 104.84 s | 1,938,980,864 |
| `runs/s3b-1.out` | `two-legs` parked, + the two level-hood facts | GREEN, 8.24 s | 1,811,021,824 |
| `runs/s4-1.out` | + leg 1 coded | GREEN, 8.46 s | 1,803,714,560 |
| `runs/s5-1.out` | + the two compositions | GREEN, 12.91 s | 1,904,377,856 |
| `runs/s6-1.out` | + the obligation and the residue | EXIT 42, one unsolved meta at `Σ≡Prop` | 2,441,854,976 |
| `runs/s6-2.out` | after the four implicits were given | GREEN, 9.81 s | 1,925,627,904 |
| `runs/final-1.out` | the file as it stands, `two-legs` restored, COLD | GREEN, 103.89 s | 1,977,024,512 |
| `runs/final-2.out` | the same file, WARM interface cache | GREEN, 3.11 s | 772,210,688 |
| `runs/final-3.out` | the same file, WARM | GREEN, 3.11 s | 772,227,072 |

**THE COLD FIGURE IS 103.89 SECONDS AND THE WARM FIGURE IS 3.11. THE WARM
FIGURE BOUNDS NOTHING**, and both are printed so nobody quotes the cheap one.

**ONE `refl` COSTS 96 OF THOSE SECONDS.** `two-legs` alone is the difference
between `runs/s3-1.out` (104.84 s) and `runs/s2-2.out` (8.16 s). This is
`[LJ-1.577]`'s measured law at its own site
(`agents/tasks/LJ-1-577/lj-1.577-report.md:135-141`): a `refl` across a module
application must unfold the injection, and the injection pulls the whole hull.
I re-measured it here rather than transferring it, and it is the same shape.
**Unlike `[LJ-1.577]`'s `injection-hypothesis-free`, this one converges**,
because both sides are the same composite and neither side has to be proved
independent of a hypothesis.

### The probe

321 lines, of which 132 are comment and 43 blank. The brief estimated about 220
lines with about 55 for the obligation. **The obligation is not in the file**;
its TYPE costs 2 lines (`Probe580.agda:292-293`) and the reduction that stands
in its place is SECTION 5, 42 lines (`:235-276`). The line count came in under the estimate
because leg 1 turned out to be one module application, which nobody had
measured before this task.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

- **The residue has a name and a type, and it is not a coding principle.** It
  is `InjL (Lset β) α`: in L, one stage injects into one ordinal. Everything
  else on this route is built.
- **`Comp` and `InclGraph` are the two tools that did the work**
  (`src/L/InjChain.lagda.md:314`, `:575`). Any further leg of any further
  composite is cheap the same way, and only a leg whose value reads an ambient
  parameter is not.
- **`Lset-isL` is new and generic** (`Probe580.agda:104`). If it is wanted in
  `src/`, it is four lines and it belongs beside `Lset→isL`
  (`src/L/Constructible.lagda.md:395`). I did not land it: the brief forbade
  `src/`.
- **The port's defect is `absorbs` and the term algebra, not the well-order.**
  `wL = orderAt` matches the literature (`src/L/Hull.lagda.md:158-159`,
  `dev/literature/truncation-and-selection.md:56-57`). A cure that rebuilds the
  hull over a different order is buying something the tree already has.
- **`absorbs` is a Pi-parameter nothing supplies, and it has a history.**
  `archive/dev/LJ-dispatch-index.md:177`, `:179` and `:195` record
  `absorbs-subset` refuted, restated, then restricted. A task that wants to
  code leg 2 must first decide what supplies `absorbs`.
- **What resisted:** naming the intermediate object as an L-element. `Comp`
  needs all five sets in L, the intermediate here is a STAGE, and the tree had
  no proof that a stage is constructible.
- **What I could not close:** whether `InjL (Lset β) α` is provable. This task
  did not attempt it and the brief did not order it. It is the next question,
  and `[LJ-1.568]`'s `Def` is the exact shape of what it needs.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`. READ, AND IT CHANGED A CLAIM
  IN THIS REPORT.** At `dev/literature/truncation-and-selection.md:56`:
  "> If δ is a limit ordinal, then the model (Lδ, ∈) has definable Skolem".
  The sentence continues at `:57` with the bracket "The well-ordering <δ is
  definable in (Lδ, ∈)". I had written that the hull's Skolem search used an
  arbitrary ambient order; this file sent me back to
  `src/L/Hull.lagda.md:158-159`, where `wL = orderAt α ordα` is the tree's own
  stage order. The claim is corrected above and the port matches the
  literature at that point.
- **`dev/literature/devlin-II5.md`. READ.** At `dev/literature/devlin-II5.md:156`:
  "|L_α| = |α| and |L_γ| = |γ|, so |γ| = |M| = |α| < κ, hence γ < κ and". This
  is the step the whole route turns on, and it is why the residue this task
  isolates is a SIZE statement about a stage and not a coding principle. The
  lemma opens `Assume V = L` at `:147`.
- **`dev/literature/digest.md`. NOT READ, DECLINED.** The rud route's orthodox
  form. This task is inside the Def route's own 5.5 port and builds no rud
  function.
- **`dev/literature/terms-2026-08.md`. NOT READ, DECLINED.** A terminology
  file. This task named no new term and proposed no glossary entry.
- **`dev/literature/geology.md`. NOT READ, DECLINED.** Set-theoretic geology.
  Nothing here touches ground models or mantles.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. READ, AND IT CARRIES THE HISTORY OF
  `absorbs`.** At `archive/dev/LJ-dispatch-index.md:177`:
  "| LJ-1.101 | Close the cardk type gap, then price sq | GAP CLOSED, GREEN | cardk checks at the master's IsCardinal, no transport. And absorbs-subset is REFUTED, so Devlin55 is vacuous |".
  Rows `:179` and `:195` continue it: restated, then restricted. This is why
  the report says a task that wants leg 2 must first decide what supplies
  `absorbs`.
- **`archive/dev/JOURNAL-archived.md`. NOT READ, DECLINED.** A journal is
  history, and the question here is what the tree states today.
- **`archive/dev/JOURNAL.md`. NOT READ, DECLINED.** Same reason.
- **`archive/dev/DECISIONS-archived.md`. NOT READ, DECLINED.** No `D<n>`
  decision bears on whether an inclusion between two L-elements carries a code.
- **`archive/dev/ORCHESTRATION.md`. NOT READ, DECLINED.** Archived operating
  rules. This task's rules came from the slot file, `AGENTS.md` and the brief.

## SCOPE TOUCHED

- `agents/tasks/LJ-1-580/Probe580.agda` (new)
- `agents/tasks/LJ-1-580/lj-1.580-report.md` (new)
- `agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md` (new)
- `agents/tasks/LJ-1-580/runs/` (new: `run.sh` and twelve `.out` files)

Nothing in `src/`. Nothing postulated. No hole. Not committed, not pushed.

`scripts/gate/check-probes.py --check`, `lint-prose.py --check`,
`lint-agda.py --check` and `check-fences.py --check` are all clean at this
working tree.
