# LJ-1.131 report: price the V = L route against the ambient one

tier: opus. Recon and pricing only. No master edited. No commit, no push.
No probe written (section 9 gives the reason and names the probe).

Load average through the task: 7.83 / 6.71 / 6.22 at start, four users, a
sibling agent clearing `_build/`. **The machine is not quiet.** No new
cold-second figure is reported below for that reason. Every second quoted
is a recorded measurement from an earlier dispatch, with its own load.

Every claim is marked MEASURED (read at the cited line, or a recorded
machine result) or INFERRED (my composition or judgement).

## 0. LEAD FINDING: take the well-order, not the ambient hypothesis

**The orchestrator's conclusion is right. The reason given for it is not
the operative one, and the stronger form of the route is cheaper and
safer than the form the brief prices.**

### 0.1 The mathematics

The tree's three recorded walls are one wall. `[LJ-1.107]`,
`[LJ-1.111]` and `[LJ-1.114]` all refuse at the same point: a bijection
is known to EXIST, the existence is a proposition, and the injection
wanted from it is not a proposition. MEASURED, three times:

- `[LJ-1.107]`: `PT.rec` refuses, `Type ℓ !=< x ≡ y`
  (`agents/reports/lj-1.107-report.md:29-36`).
- `[LJ-1.111]`: the same refusal with leastness in scope
  (`src/ProbeLJ1111B.agda:46`, recorded at
  `agents/reports/lj-1.111-report.md:30-35`). "The leastness constrains
  the ordinal, never the bijection type."
- `[LJ-1.114]`: two independently chosen injections give colliding
  codes, so the induction cannot cohere
  (`src/ProbeLJ1114A.agda:89-94`, recorded at
  `agents/reports/lj-1.114-report.md:34-45`).

The classical cure for exactly that refusal is a well-order on the
candidates and a least element. A least element is unique, so its type
IS a proposition, and the truncation eliminates into it.

**The tree already owns that cure. The AC trophy is built on it.**

- `leastOf` turns a truncated non-emptiness into an honest element,
  given an `SWO` on the carrier
  (`src/L/WellOrder/Base.lagda.md:158-160`). Its result type is a
  proposition (`isPropLeastOf`, `:136-139`). MEASURED.
- `orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))`
  (`src/L/Choice/Step.lagda.md:740-741`) is `<_L` at every stage, built
  by `∈`-induction. MEASURED.
- The family is COHERENT: `endExtension`
  (`src/L/Choice/Step.lagda.md:843`) proves the order at a large stage
  restricts to the order at a small one. The chapter states why: the
  comparison never mentions the stage it is read at
  (`src/L/Choice/Step.lagda.md:24-29`). MEASURED.
- Its three keys are Devlin's own: stage of first appearance, then
  formula code, then parameter vector (`_≺ₙ_`,
  `src/L/Choice/Name.lagda.md:615`; `nameOrder`, `:804`). MEASURED.
- The order sits INSIDE the model as a set,
  `relL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S`
  (`src/L/Choice/Table.lagda.md:795-796`), with both representation
  directions (`:825-832`). MEASURED.
- It is DESCRIBED in the object language, with adequacy both ways
  (`order-in` / `order-out`, `src/L/Choice/Internal.lagda.md:1314`,
  `:1330`). MEASURED.

So the load-bearing question of the brief, "does the tree have or can it
cheaply get `<_L`", is GREEN before a line is written. It is not cheap to
get. **It is already delivered, by the AC half of the double trophy,
5,903 in-fence lines over `src/L/Choice/` and `src/L/WellOrder/`.**
MEASURED (counted with the ledger's caliber, section 3.1).

**And the GCH wing already consumes it.** `src/L/Hull.lagda.md:158-159`
reads `wL : SWO SL ; wL = orderAt α ordα`, and `L.Hull` is imported by
`src/L/BoundedSubset.lagda.md:33`. The Skolem hull of Devlin 5.3 and 5.4
is built by least witness over the AC side's own order. MEASURED. **The
sharing the brief asks about is not a proposal. It is live.**

### 0.2 What `V = L` actually adds, and it is not the order

`orderAt` reaches the members of the stages, which is L. The objects the
GCH wing must choose at the `sq` wall are AMBIENT: a bijection between an
ordinal `α` and the AMBIENT least cardinal `|α|`. No well-order reaches
those. That gap is the whole of `[LJ-1.107]`.

**So the wall is not a wall of the mathematics. It is the price of
stating an internal fact ambiently.** Precisely:

- `∥ sq α ∥₁` at every infinite ordinal is a ZF theorem, and this tree
  PROVED it: `TruncatedChain.theorem` is GREEN
  (`src/ProbeLJ1111A.agda:271-272`, recorded at
  `agents/reports/lj-1.111-report.md:23-31`). MEASURED.
- `sq α` untruncated, uniformly in `α`, is NOT a ZF theorem. It asks for
  a definable choice of injection, and ZF has none. INFERRED, standard
  set theory, and consistent with the three refusals above.
- Devlin's proof of the same fact is the `<_L` counting. Under `V = L`
  the `<_L`-least bijection exists and is definable, so the choice is
  free.

**Therefore the wing needs a canonical selection, the only canonical
selection available without choice is `<_L`, and `<_L` only reaches
objects that lie in L. The wing's statements must therefore be about
objects in L.** That is the whole argument, and every step of it is
either MEASURED in this tree or standard ZF.

### 0.3 The route I would take: A', not A

**Route A' — state the wing internally, with `⟨ isL x ⟩` where Devlin
writes "Assume V = L". Do not add an ambient parameter.**

Four reasons, in mathematics:

1. **Devlin uses `V = L` in 5.5 exactly once, and only to get
   `x ∈ L`.** Everything after that line is a ZF argument about L. The
   digest says so in its own words when it resolves 5.6's application:
   "so every CONSTRUCTIBLE `x ⊆ κ` lands in `L_{κ⁺}`"
   (`dev/literature/devlin-II5.md:451`). MEASURED. Section 6 gives the
   full literature answer.
2. **The internal endpoint does not want more.** DD1 rules the endpoint
   stated in L (`dev/PLAN.md:167`). The internal GCH quantifies over
   subsets of `κ` THAT LIE IN L. For those, `x ∈ L` is not an
   assumption. It is what the internal quantifier already hands you.
3. **It is what the delivered half did.** `L⊨ZFC` assumes nothing about
   V beyond one LEM (`src/Landmarks.lagda.md:76-77`). It does not say
   "assume V = L". It builds `<_L` in the ambient and shows the model
   satisfies the choice statement. MEASURED.
4. **A global ambient `V = L` carries a vacuity risk that `⟨ isL x ⟩`
   does not.** A false parameter empties every theorem under it. This
   tree has been bitten by that twice, and the machine caught both
   (`agents/reports/lj-1.129-report.md:99-102`, `:130-138`,
   `:334-338`). MEASURED. See section 1.4.

**Where I differ from the orchestrator.** The stated reason was that
subject and proof would live in one universe. That is true and it is not
what decides. The operative reason is narrower and checkable: `<_L` is
the delivered device that discharges the exact truncation the wing is
stuck on, it reaches only what is in L, and so the statements must be
about what is in L. The universe-unification framing points at Route A,
the global hypothesis. The truncation framing points at Route A', which
is strictly weaker, cheaper in risk and lands on the ruled endpoint
directly.

**The one correction to the orchestrator's reading, MEASURED.** The
brief says `V = L` gives "the cardinal arithmetic 1.1(vii) needs".
1.1(vii) needs the well-order, not `V = L`. The digest classes it
"generic cardinal arithmetic over the level-size equation" and marks
5.5's requirement F as EITHER-tower, with no `V = L` listed
(`dev/literature/devlin-II5.md:382`, `:414-418`). Devlin's `V = L` in the
well-order chapter buys Δ₁ instead of Σ₁, a fine-structure refinement
(`dev/literature/devlin-II5.md:349-350`). The cardinal chain of 5.5 does
not consume it.

## 1. ROUTE A: assume V = L

### 1.1 What `V = L` costs to STATE: one line. MEASURED

The tree can express "every set is constructible" today.
`isL : S → Ω` is delivered at `src/L/Constructible.lagda.md:376-377`:

```agda
isL x = ⋁ S (λ α → ((IsOrd α , isPropIsOrd α) ⊓ (x ∈ˢ Lset α)))
```

So `V = L` is `(x : S) → ⟨ isL x ⟩`. One line, as a module parameter of
whatever chapter states it, over nothing but the level.

Two properties matter and both are MEASURED:

- **`isL` is truncated** (`⋁` lands in `Ω`). A `V = L` parameter gives a
  truncated `∃α` for each `x`. That is not a defect here.
  `Devlin55`'s conclusion `⟨ x ∈ˢ Lset κ ⟩` is a proposition
  (`src/L/BoundedSubset.lagda.md:1624-1625`), so `PT.rec` eliminates the
  truncation into it directly.
- **`isL` is already the hypothesis shape the order stack takes.**
  `module Bound (a : V ℓ) (p : ⟨ isL a ⟩)`
  (`src/L/Choice/Order.lagda.md:679`) and
  `relL : (α : V ℓ) → ⟨ isL α ⟩ → ...`
  (`src/L/Choice/Table.lagda.md:795`) both take it. Nothing new is
  needed to plug it in.

### 1.2 The definable well-order: DELIVERED. MEASURED

Answered in section 0.1. Two clarifications, both MEASURED, because both
change how the route must be written.

**There is no global class order, by design.** `src/Everything.lagda.md:925`
states it: "No well-order of `L` is used, because none exists here; a
set is small, so `L.Choice.Stage`'s bounding ordinal holds the family,
its members and their members at once, and `L.Choice.Order`'s `Bound`
supplies the order on the tower there as an element of the model."

So the idiom is: take a bounding ordinal first, then order there. That is
exactly the idiom the `sq` cure needs, and the tree's own prose names it.
`stageBound` is delivered (`src/L/Choice/Stage.lagda.md:294`, "One stage
for everything below a set").

**`src/L/Coding/` holds codes but no order.** The brief guessed a code
ordering might be most of `<_L`. It is not. `src/L/Coding/` gives
`AllCodes` (`src/L/Coding/CodeSet.lagda.md:440`), the evaluator
(`src/L/Coding/Uniform.lagda.md:342`) and the decoder
(`src/L/Coding/Recover.lagda.md:154`), and no comparison at all.
MEASURED, by a grep of all 20 files for `SWO`, `≺`, `WellFounded`, `Acc`,
`leastOf` and `Tri`, with zero order hits. The code order lives one part
later, at `src/L/Choice/Finite.lagda.md:1114` and
`src/L/Choice/Limit.lagda.md:607`.

### 1.3 Given `<_L`, what `sq` and `absorbs` cost as THEOREMS

The chain has four links. Three are delivered and one is assembly.

**Link 1: pick the L-least injection.** `leastOf` over `orderAt` at the
bound stage. DELIVERED as a pattern, three times in this tree:
`CodeSelect` (`src/L/BoundedSubset.lagda.md:1099-1141`), `CanonCode`
with an explicit section and retraction
(`src/L/BoundedSubset.lagda.md:463-497`), and `Hull`'s `wL`
(`src/L/Hull.lagda.md:158-159`). MEASURED.

**Link 2: read the chosen set as a function.** DELIVERED in the object
language with adequacy: `appAt` and `appAt-adequate`
(`src/L/Coding/Model.lagda.md:160-166`), `svAt` for single-valuedness
(`:210-215`), `inDomAt` and `domAt` for the domain (`:269-280`).
MEASURED. Single-valuedness makes the value fibre a proposition, and the
tree's delivered idiom for that extraction is `isContr` plus `fst`, the
same idiom `hasChoice` uses (`src/FOL/ZFModel.lagda.md:424-430`).

**Link 3: the square-law chain.** `[LJ-1.107]` MEASURED the whole
ambient chain at 582 non-blank probe lines. Every step closed except
step 5's injection, and `Chain.theorem` checked GREEN with that
injection as a parameter (`agents/reports/lj-1.107-report.md:29-36`,
the per-step table at `:40-57`). Link 1 plus link 2 supply exactly that
parameter.

**Link 4: `absorbs`.** `[LJ-1.118]` recorded that the unwritten branch
reduces to `stage-card-upper` at `α`, that is to honest `sq`
(`src/ProbeLJ1118A.agda:17-25`, recorded at
`agents/reports/lj-1.129-report.md:182-186`). MEASURED. Once `sq` is a
theorem, `absorbs` follows by the successor absorption, which
`[LJ-1.107]` measured at 103 lines (`ShiftAbs` and `Shiftω`, step 3 of
its table).

Prices are in section 3.

### 1.4 The vacuity risk of the GLOBAL form. INFERRED

I found no delivered theorem that refutes `(x : S) → ⟨ isL x ⟩`. I also
cannot prove it consistent here. The standard relative-consistency
argument is about ZF, and this ambient is a cubical cumulative hierarchy,
so the transfer is not automatic. **INFERRED, and it sets no verdict.**

What it does set is a preference. The tree's own record shows two
theorem frames that were vacuous and passed prose review
(`agents/reports/lj-1.129-report.md:334-338`). A global `V = L`
parameter would put the whole GCH wing behind one unrefuted assumption.
`⟨ isL x ⟩` as a per-theorem hypothesis carries no such exposure,
because at the internal site it is discharged by the internal
quantifier. **That is a reason to prefer A' that costs nothing to
honour.**

## 2. ROUTE B: keep the ambient route

### 2.1 The gap from `α = ω` to every infinite cardinal: MEASURED DEAD

Devlin 5.6 applies 5.5 at `κ⁺` with `α = κ` for every infinite `κ`
(`dev/literature/devlin-II5.md:164-166`). At any `α` above `ω` the
demand set of `sq` contains non-initial ordinals
(`agents/reports/lj-1.129-report.md:31-42`). There:

- honest `sq` does not close (`[LJ-1.107]`, MEASURED);
- the truncated `sq` closes but cannot be threaded into `Devlin55`
  (`[LJ-1.114]`, MEASURED, `g₂' != g₁` at line 412 of the threaded edit,
  2.49 s at load 4.98 / 4.31 / 4.40, then reverted).

**Route B has no price at this step. It has a refutation.** MEASURED.

Route B's exits are two, and I judge both closed:

- **Assume ambient choice.** `SetChoice` is a hypothesis this tree knows
  how to state (`src/Landmarks.lagda.md:54-55`). It would give the
  ambient square law at once. The brief forbids it, and the mathematics
  agrees: Gödel's theorem is `ZF ⊢ (GCH)^L`, and its whole point is that
  no choice is assumed. With ambient AC the relative-consistency content
  is gone. There is also a trophy-shelf cost, MEASURED: `L⊨ZFC` takes
  only LEM (`src/Landmarks.lagda.md:76-77`), and `Landmarks` displays
  each theorem's "full bill of assumptions" (`:5-6`). A GCH trophy
  priced at LEM plus ambient AC would not match its twin.
- **Acquire a canonical selection.** The only one without choice is
  `<_L`, which reaches only L. That is Route A'.

**INFERRED, and I mark it clearly:** that `[LJ-1.114]`'s threading has no
alternative proof is my composition, not a machine result. It rests on
two things. `stage-card-upper` concludes in DATA, so an `∈`-induction
building it needs per-member injections that cohere, and truncated
per-member data cannot cohere. And the classical proof of
`|L_α| = |α|` is the `<_L` counting. I state this as the direction the
literature and three measurements agree on.

### 2.2 The ambient-to-internal conversion: cannot be priced without a probe, and one point of it is already negative

**MEASURED absence.** No PLAN row prices it
(`agents/reports/lj-1.129-report.md:218-222`, rows 568 to 625 read). The
ledger's `remaining` rows carry `gch-proof-steps` and no conversion row.

**MEASURED negative at the one point anyone checked.** `[LJ-1.91]` found
that `ω₁ᴸ` does not provably satisfy the ambient `IsCardinal`, because
that sentence is independent: it holds under `V = L` and fails after
`Coll(ω, ω₁ᴸ)` (`agents/reports/lj-1.91-report.md:36-48`). The report
marks its own claim INFERRED, and `dev/PLAN.md:570` records the
consequence. **So Route B's ambient conclusion does not convert to the
internal statement in the direction the endpoint needs.**

**What the tree does have, MEASURED.** The one delivered
ambient-to-internal instrument is `π₁-down`
(`src/FOL/Absoluteness.lagda.md:187-188`), and it is Π₁ only, on
formulas whose constants already lie in the inner class. `abs₀` is Δ₀
both ways (`:122-123`); `transferFo` is Δ₀ with constructible constants
(`src/L/Absoluteness.lagda.md:122-123`), and that chapter's own recap
sets the ceiling: "It is Δ₀ only, because absoluteness is"
(`src/L/Absoluteness.lagda.md:144-149`). `mkReflect` covers ALL formulas
but internal to internal only (`src/L/ReflectFo.lagda.md:524-530`).

**None of these reads `IsCardinal` down.** `IsCardinal κ` is a negated
existential over the metatheory's FUNCTION SPACE
(`src/L/BoundedSubset.lagda.md:1046-1047`), not a formula. MEASURED.

**The conversion cannot be priced without a probe.** The probe: express
"there is an injection from `κ` into `δ`" as an ELEMENT of L, using the
delivered `svAt` / `domAt` / `appAt` layer, then state internal
`IsCardinal` and try `abs₀` or a direct separation at one concrete
`κ`. GO if the internal predicate elaborates and reads back to the
ambient one under `⟨ isL ⟩` hypotheses; NO-GO otherwise. This is the
SAME probe Route A' needs (section 9), which is itself a finding: the
two routes converge on one measurement.

### 2.3 `[LJ-1.114]`'s wall: Route B must go through it

Route B cannot go around. The wall is at `Upper.LimitStep`, which is the
`|L_α| = |α|` counting, and 5.5's cardinal step consumes it directly
(`src/L/BoundedSubset.lagda.md:1578-1583`). There is no branch of
Devlin's proof that omits the counting. MEASURED that the counting is
consumed; INFERRED that no alternative proof avoids it.

## 3. THE PRICES

DD8: one best-effort figure each, and each names its basis. In-fence
non-blank lines, the ledger's caliber
(`scripts/ledger.py:66`). **NEW content only.** Delivered lines that get
reused are named separately and counted at zero.

### 3.1 What both routes reuse at zero. MEASURED

| stack | in-fence lines | status |
|---|---:|---|
| `src/L/Choice/` plus `src/L/WellOrder/` (the `<_L` stack) | 5,903 | delivered, hypothesis-free |
| `src/L/Coding/` (codes, evaluator, decoder, `appAt` layer) | 6,565 | delivered |
| `src/L/Ordinal/SquareLaw.lagda.md` | 775 | delivered, `via-col-square` at `:960` |
| `src/L/StageCardinal.lagda.md` | 482 | delivered, `sq` a parameter |
| `src/L/BoundedSubset.lagda.md` | 1,409 | delivered, at a degenerate site |

MEASURED, counted per file with the ledger's fence regex. The
per-trophy split the ledger already carries: shared 17,948, GCH alone
8,624, AC alone 225.

### 3.2 Route A' (the recommendation)

| block | lines | basis |
|---|---:|---|
| A1. `⟨ isL x ⟩` replaces "assume V = L"; derive `lam` and `x∈Lλ` from it | 30 to 60 | `src/L/Choice/Stage.lagda.md:294` delivers the bounding ordinal; two of the three hypotheses replaced already exist |
| A2. an injection as an ELEMENT of L, and read back as an honest function | 120 to 220 | INFERRED band. Parts delivered at `src/L/Coding/Model.lagda.md:160-280`; this is assembly. **Widest unmeasured term** |
| A3. the `<_L`-least injection, by `leastOf` over `orderAt` at the bound | 40 to 80 | three delivered instances of the same pattern: `src/L/BoundedSubset.lagda.md:463-497`, `:1099-1141`, `src/L/Hull.lagda.md:158-159` |
| A4. internal least cardinal and internal `IsCardinal` | 90 to 170 | `[LJ-1.107]` measured ambient `LeastCard` at 38 lines; the internal form adds the L-injection predicate |
| A5. the square-law chain restated over L-injections | 300 to 450 | `[LJ-1.107]` MEASURED 582 lines for the ambient chain at this site, of which 455 closed unconditionally; the restatement rewrites types, not proofs |
| A6. `absorbs` as a theorem | 100 to 180 | `[LJ-1.107]` measured the successor absorption at 103 lines |
| A7. the internal GCH statement in `hasChoice`'s shape | 80 to 160 | `ChoiceStatement` is 13 in-fence lines (`src/L/Choice/Transversal.lagda.md:372-384`); GCH adds the power-set and successor-cardinal bookkeeping |
| **NEW total** | **760 to 1,320** | centre about 1,040 |

**Basis, stated once.** Blocks A3, A5 and A6 rest on measurements taken
at THIS site by `[LJ-1.107]` and on delivered instances in these
masters. Blocks A2, A4 and A7 are inferred bands from delivered
comparables inside this tree. P-l applies to A2, A4 and A7, and I mark
them hypotheses, not prices.

### 3.3 Route A (the brief's global-parameter form)

Blocks A2, A3, A5 and A6 only. Nothing is internalized, so the ambient
types stand and no consumer changes shape.

**NEW total: 560 to 930, centre about 745.**

**The saving is a loan, not a discount.** Route A delivers Devlin 5.6,
"V = L implies GCH". The ruled endpoint is 5.7, GCH inside L. The step
between them is the relativization, which section 2.2 measured to have
no delivered general instrument. **Route A therefore keeps Route B's
unpriced debt and adds an unrefuted global hypothesis.**

### 3.4 Route B

**No price. MEASURED refutation at its first step (section 2.1), and a
MEASURED negative at its conversion step (section 2.2).**

### 3.5 What is excluded from both, and it is route-neutral

`levelIn` and `cover`, the condensation hard part
(`src/L/BoundedSubset.lagda.md:1409`). `[LJ-1.123]` priced the chapter
at 0.6k. `[LJ-1.129]` found that centre optimistic, because it does not
carry the 28-fact closure supply
(`agents/reports/lj-1.129-report.md:256-274`). **Both routes owe it in
full and it does not separate them.** I did not re-price it.

## 4. WIDEST UNMEASURED TERM, AND ITS PROBE

**Route A and A', one term, the same one: block A2.** Turning an
L-element function into an honest Agda function, and back.

Every link around it is delivered and cited. A2 itself is assembly of
delivered parts, and nobody has run it. It is the single INFERRED step
on which the whole recommendation rests.

**The probe, with its abort criterion fixed in advance.**
`src/ProbeLJ1131A.agda`, one file, one agda process at the C-12 cap, on
a QUIET machine.

1. Fix `α = ω`. Build one concrete L-element graph `f` of an injection.
2. Assemble `svAt`, `domAt` and `appAt-adequate`
   (`src/L/Coding/Model.lagda.md:160-280`) into
   `toFun : ⟪ ω ⟫ → ⟪ ω ⟫` with `toFun-inj`, extracting the value
   through the contractible fibre.
3. Compose with `leastOf (orderAt β)` at a bound stage `β`, and force
   the composite to elaborate.

**GO** if the honest function and its injectivity elaborate. Report the
lines and the cold seconds with the load. **NO-GO** if the fibre
extraction refuses, and report the exact refusal. A NO-GO kills both
Route A and Route A', and it would leave no route at all, which makes
this probe the correct next gate.

**Route B has no widest term, because it has a refutation.**

## 5. WHAT BREAKS UNDER ROUTE A, MASTER BY MASTER

Under Route A (global parameter) almost nothing breaks, and that is its
attraction. Under Route A' more moves. Both columns below.

| master | under Route A | under Route A' |
|---|---|---|
| `src/L/StageCardinal.lagda.md` (482) | the `sq` module parameter (`:15-19`) is DELETED and becomes an import. Nothing else changes. Content survives whole | the injection types change from ambient to L-element throughout. `stage-card-upper` (`:564-566`) and `stage-card-lower` (`:209-211`) both restate. Proofs survive; types are rewritten |
| `src/L/BoundedSubset.lagda.md` (1,409) | `BoundedSubsetAt`'s `sq` and `absorbs` parameters (`:1388-1392`) are DELETED. `IsCardinal` (`:1046-1047`) unchanged. The body (`:1408-1622`) is generic in `x` and does not branch, so it survives verbatim | additionally `IsCardinal` restates over L-injections, and the header opens `𝒮ʟ` where it now opens `𝒮ᵥ` (`:56`). The cardinal step (`:1594-1603`, 10 lines) restates |
| `src/L/Ordinal/SquareLaw.lagda.md` (775) | unchanged. `via-col-square` (`:960`) still delivers the initial case | `Init` (`:685-698`) restates its fourth conjunct over L-injections |
| `src/L/Hull.lagda.md` | unchanged, both routes. It already runs on `orderAt` (`:158-159`) | unchanged |
| `src/L/Choice/*`, `src/L/WellOrder/*` (5,903) | unchanged, both routes. Nothing is consumed that they do not already export | unchanged |
| `src/L/Coding/*` (6,565) | unchanged, both routes | unchanged |
| `src/L/Condensation*.lagda.md` | unchanged, both routes. The twelve-row agreement is about the level certificate, not about cardinals | unchanged |
| new master, the internal GCH statement | not written. Route A stops at 5.6 | written, in `ChoiceStatement`'s shape |

**MEASURED** for every "unchanged" claim above, by reading the cited
declaration and its consumers. **INFERRED** for the restatement effort in
the Route A' column: I read the types, I did not run the change.

**One structural warning, MEASURED, and it is the real cost of A'.**
`BoundedSubset`, `StageCardinal` and `SquareLaw` all open the AMBIENT
structure: `open hPropStructure 𝒮ᵥ` at
`src/L/BoundedSubset.lagda.md:56`, `src/L/StageCardinal.lagda.md:54` and
`src/L/Ordinal/SquareLaw.lagda.md:64`. Their `S` is `V ℓ`. Restating the
wing internally is not a wrapper. It changes which carrier every `∈ˢ`,
`⟪_⟫` and `↪` in the chain refers to. That is why A' costs about 300
lines more than A, and the figure is in block A4 and A5.

## 6. WHERE DEVLIN USES V = L, AND WHETHER HE COULD AVOID IT

Three places, and MEASURED at each from the digest.

**1. 5.5's first line, and only for `x ∈ L`.** "Assume V = L. Let κ be a
cardinal." (`dev/literature/devlin-II5.md:147-149`). The proof then
takes a limit `λ` with `x ∈ L_λ`
(`dev/literature/devlin-II5.md:152-153`). That step is the ONLY one that
needs it: an arbitrary bounded subset of `κ` need not be in L, and
everything after it is a ZF argument about L.

**COULD HE AVOID IT? YES, and 5.7 is him doing so.** The digest's own
resolution of 5.6 already states the operative hypothesis as
constructibility: "5.6 applies 5.5 at the cardinal κ⁺ with α = κ, so
every CONSTRUCTIBLE x ⊆ κ lands in L_{κ⁺}"
(`dev/literature/devlin-II5.md:451`). 5.7 relativizes the whole chain to
L and gives `ZF ⊢ (GCH)^L`
(`dev/literature/devlin-II5.md:168-169`). MEASURED.

**2. The well-order chapter 3.1 to 3.5.** "WO(x, y) is Σ₁ and Δ₁ under
V = L" (`dev/literature/devlin-II5.md:349-350`). MEASURED.

**COULD HE AVOID IT? YES, for 5.5's purpose.** `V = L` buys the
DEFINABILITY CLASS, Δ₁ rather than Σ₁. It does not buy the order's
existence, which is a ZF theorem. 5.5's cardinal argument consumes the
order through 5.3's least witness and through 1.1(vii)'s counting, and
neither needs Δ₁. The digest's own step table classes 5.5's requirement
F as EITHER-tower and lists condensation (i)(ii), `|L_α| = |α|` and
initial ordinals, with no `V = L`
(`dev/literature/devlin-II5.md:382`). MEASURED.

**3. 1.1(vii), `|L_α| = |α|`. He does NOT use it.** The digest classes
it "generic cardinal arithmetic over the level-size equation" and notes
the J tower carries the analogue
(`dev/literature/devlin-II5.md:413-418`). MEASURED. **This corrects the
brief:** 1.1(vii) needs the well-order, not `V = L`.

**The one-sentence answer.** Devlin's `V = L` is a convenience of
exposition in II.5, and 5.7 is the paragraph where he pays it back. The
theorem underneath is `ZF ⊢ (GCH)^L`, and its hypothesis is
constructibility of the subset, not of the universe.

## 7. DD4: WHICH ROUTE SHARES MORE

**Route A' shares more, and the sharing is already load-bearing rather
than proposed.**

The evidence, MEASURED:

- **The GCH wing already runs on the AC side's well-order.**
  `src/L/Hull.lagda.md:158-159` is `wL = orderAt α ordα`, and
  `src/L/BoundedSubset.lagda.md:33` imports `L.Hull`. Devlin's 5.3
  Skolem hull and Devlin's `<_L` are one object in this tree.
- **The order stack is 5,903 delivered lines, and neither route adds to
  it.** Route A' consumes three more of its exports: `leastOf`,
  `orderAt` and `stageBound`. Route B consumes none of them, because
  its objects are ambient and the order does not reach them.
- **The ledger already books the split**: shared 17,948, GCH alone
  8,624, AC alone 225. Route A' moves the `sq` and `absorbs` content
  from GCH-alone into shared, because it is discharged by the AC side's
  order. Route B leaves it GCH-alone, and cannot discharge it at all.
- **The generic form is already written.** `SWO` and `leastOf` take a
  generic carrier (`src/L/WellOrder/Base.lagda.md:101`, `:158`), and
  `CanonCode` and `CodeSelect` are generic in the code type
  (`src/L/BoundedSubset.lagda.md:463`, `:1099`). Route A' instantiates
  generic code. It does not write fixed code.

**So DD4 favours Route A', and this is the brief's own hypothesis
confirmed with evidence: if `V = L` lets the two proofs share the
well-order, that is a DD4 argument for Route A. It does, and it is.**

**No stop-line pushed me toward writing fixed.** Nothing in this task
required a special case.

## 8. THE NEGATIVES, EACH CLASSIFIED

| negative | class |
|---|---|
| honest `sq` at non-initial ordinals does not close from delivered machinery | MEASURED (`[LJ-1.107]`) |
| the least ordinal's uniqueness does not make the bijection fibre a proposition | MEASURED (`src/ProbeLJ1111B.agda:46`) |
| the truncated `sq` cannot be threaded into `Devlin55` | MEASURED (`[LJ-1.114]`, `g₂' != g₁`) |
| no PLAN row prices the ambient-to-internal conversion | MEASURED absence |
| `ω₁ᴸ` does not provably satisfy the ambient `IsCardinal` | MEASURED as recorded; the report itself marks its argument INFERRED |
| `src/L/Coding/` contains no order on codes | MEASURED (grep of all 20 files) |
| no `V = L`, `aleph`, `ω₁`, `Hartogs` or successor-cardinal definition exists in `src/` | MEASURED absence |
| no delivered lemma reads an ambient function-space statement into L | MEASURED (the four transfer lemmas of section 2.2 read formulas, not function quantification) |
| `[LJ-1.114]`'s threading has no alternative proof | **INFERRED** |
| untruncated `sq` uniformly in `α` is not a ZF theorem | **INFERRED**, standard set theory |
| a global `V = L` parameter is consistent with this ambient | **INFERRED**, unproved either way |
| Route A' block A2 elaborates | **INFERRED**, and it is the probe of section 4 |

## 9. WHY NO PROBE RAN

The brief allows one small probe. I did not run one, for two reasons,
and I state them so the orchestrator can overrule.

1. **The machine is not quiet.** Load was 7.83 / 6.71 / 6.22 at start,
   four users, with a sibling agent clearing `_build/`. The brief's own
   rule is that a task measuring check time gets a quiet machine. A
   second figure taken now would not be admissible as a price.
2. **The probe that matters is not small.** The load-bearing step is
   block A2, and its probe must import `L.Coding.Model` (1,288 in-fence
   lines) and `L.Choice.Step` together. That is most of the tree's
   elaboration chain, and it is not a five-minute miniature.

Section 4 names the probe with its abort criterion, so the next dispatch
can run it as a gate rather than rediscover it.

## 10. WHAT I WOULD DO NEXT, IN ORDER

1. **Run the section 4 probe on a quiet machine.** It gates both
   surviving routes and it is the only INFERRED step under the
   recommendation.
2. **On GO, restate `Devlin55` with `⟨ isL x ⟩` in place of `absorbs`,
   and prove `sq` from `<_L`.** That is blocks A1, A3, A5 and A6.
3. **Do not add a global `V = L` parameter.** It buys about 300 lines
   and it costs the endpoint, because the relativization debt stays.
4. **Retire nothing yet.** Under both surviving routes every master in
   section 5 keeps its content. This is a statement change, not a
   retirement.

## 11. ARCHIVE USED (DD18)

Read whole:

- `agents/reports/lj-1.129-report.md` (374 lines). Took: the four facts
  (`:16-51`), the degenerate-site finding (`:57-76`), the two vacuous
  frames the machine caught (`:99-102`, `:334-338`), the PLAN-absence
  measurement (`:218-222`), and the `[LJ-1.123]` re-price
  (`:256-274`).

Read in part, at the cited regions:

- `agents/reports/lj-1.107-report.md:1-57`. Took the verdict, the
  unwritable injection, and the per-step table with its 582 lines and
  its 117 s at load 3.57 / 4.33 / 4.65.
- `agents/reports/lj-1.111-report.md:1-60`. Took the GREEN truncated
  chain (`:23-31`) and the refusal with leastness in scope (`:30-35`).
- `agents/reports/lj-1.114-report.md:1-60`. Took the threading failure,
  the code collision (`:34-45`) and the 2.49 s refusal with its load.
- `agents/reports/lj-1.91-report.md:1-60`. Took the internal-`ω₁ᴸ`
  rejection (`:36-48`) and its own INFERRED marking.

`archive/` proper: **NOT read directly.** The two recon agents surveyed
`archive/rud-route/src/L/Rud/Order.lagda.md` and confirmed it carries a
second, independent well-order by producer traces
(`:325`, `:646`, `:802`). I took SHAPE only and no claim, per the
brief's `[LJ-1.11]` warning. It bears on DD4 as evidence that the J
tower would also carry a `<_L` analogue, which matches
`dev/literature/devlin-II5.md:380`.

Masters read, at the cited lines: `src/L/BoundedSubset.lagda.md`,
`src/L/Constructible.lagda.md`, `src/L/StageCardinal.lagda.md`,
`src/L/Ordinal/SquareLaw.lagda.md`, `src/L/WellOrder/Base.lagda.md`
(whole), `src/L/Choice/Step.lagda.md`, `src/L/Choice/Order.lagda.md`,
`src/L/Choice/Table.lagda.md`, `src/L/Choice/Internal.lagda.md`,
`src/L/Choice/Transversal.lagda.md`, `src/L/Choice/Stage.lagda.md`,
`src/L/Choice/Name.lagda.md`, `src/L/Hull.lagda.md`,
`src/L/Coding/Model.lagda.md`, `src/Landmarks.lagda.md` (whole),
`src/Everything.lagda.md:918-932`, `src/FOL/ZFModel.lagda.md`,
`src/FOL/Absoluteness.lagda.md`, `src/L/Absoluteness.lagda.md`,
`src/L/ReflectFo.lagda.md`.

`dev/LESSONS.md`: the recon and probe bundles were loaded with
`scripts/rules.py --for recon` and `--for probe` and read. D-1, D-10,
D-26, P-l, P-i, C-12, C-22 and R-40 came back and are honoured. D-26 is
the one that bears directly: it says a stage built as a definable power
carries nothing, so a well-founded key needs syntax. That is exactly
what `src/L/Choice/Name.lagda.md` supplies, and it is why the Def tower's
`<_L` is a naming order.

## 12. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:120-133` (5.3, the least-witness hull).
- `:136-143` (5.4, the counting).
- `:147-157` (5.5, its statement and its proof chain).
- `:159-166` (5.6, and the application at `κ⁺` with `α = κ`).
- `:168-169` (5.7 and 5.8, the relativization corollaries).
- `:346-358` (what II.5 consumes, items 8, 9, 11 and 12).
- `:364-394` (the per-step Def-or-either table, and the DD4 verdict).
- `:411-418` (1.1(vii) as generic cardinal arithmetic).
- `:447-452` (the resolved reading of 5.5's second clause, and the
  "every constructible x" phrasing).
- `:454-460` (5.3's least-witness formula, restored, cross-checked
  against `jech13.txt:756-760`).

`dev/literature/devlin-errata.md`: listed in the directory. I did not
read it, because the four readings I depend on are already resolved in
`devlin-II5.md` section 6, each against the printed page by tesseract or
against Jech. **This is a gap in my return and I mark it.** If any of
5.5, 5.6, 1.1(vii) or 3.3 carries a known erratum, my section 6 should
be re-checked against it.

## 13. DD4, ANSWERED AGAIN AS THE RULE REQUIRES

**Maximize the code the two proofs share, and write it generic.** Route
A' shares the entire 5,903-line order stack, which the GCH wing already
imports at `src/L/Hull.lagda.md:158-159`. It instantiates generic
machinery (`SWO`, `leastOf`, `CanonCode`) rather than writing fixed
code. Route B shares none of it and cannot, because its objects are
ambient. **No stop-line in this task pushed me to write fixed, and I
wrote no code.**
