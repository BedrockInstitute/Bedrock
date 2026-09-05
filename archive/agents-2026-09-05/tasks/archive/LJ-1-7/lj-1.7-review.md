# DD25 adversarial review of the `[LJ-1.7]` return

Reviewer: Opus 5, maximum effort. Written incrementally per C-22.
Target: `_build/lj-1.7-report.md`, brief `_build/briefs/LJ-1.7.md`.
Both read WHOLE. ASD-STE100. No master edited. No commit, no push.

Probes written and thrown away per D-1: `src/ProbeDD25G1.agda`,
`src/ProbeDD25G2.agda`, `src/ProbeDD25G3.agda`,
`src/ProbeDD25G2Cone.agda`. All runs at `GHCRTS="-A64m -I0 -M8g"`,
one process. No heap exhaustion.

## 1. THE VERDICT

**OVERTURN on both blockers. UPHOLD on every number. The deciding
number is 0.**

The return's own figures are correct. I re-measured `countFo` of the
level-hood matrix myself: **328**, exactly as reported
(`src/ProbeDD25G1.agda:54`, green). The master is green and its rates
are as stated.

What I overturn is the diagnosis. The return names two blockers and
both fail under test:

1. `countFo (leafParts) ≡ 0` typechecks by `refl` at
   `src/ProbeDD25G2.agda:343`, and `Cnt.erase leafParts refl`
   typechecks at `:346`. **The 328 constants are a two-spelling defect
   (P-v), not a wall.** The cure is the file's OWN documented house
   style: `src/L/Condensation.lagda.md:1111-1114` says "The tag
   numerals are slots, so every formula is constant-free", and the
   twelve rows already use it. I applied it to the four leaf helpers
   the rows do not use. 256 code lines, green in 4.66 / 4.68 / 5.00
   user s.
2. `⟪ πX ⟫ ↪ ⟪ α ⟫` typechecks with **no** `collapseCode` hypothesis
   at `src/ProbeDD25G3.agda:159`, green in 0.88 / 0.86 / 0.87 user s
   over 104 code lines. The return conflated two different fibres. The
   collapse fibre **is** a proposition (`isPropFib`, `:57`), so leg one
   needs no order at all.

**The return did not ship a false theorem.** The master is honest, its
residue is named, and the C-35 tension is admitted. But the two
sentences that justify stopping are both inferences, and both are
wrong. `[LJ-1.7]` is much closer to done than the return says.

## 2. THE TWO BLOCKERS, CLASSIFIED

Per the retrospective's Change 1, I classified each deciding claim
before attacking it.

### Blocker 1: "the `countFo-328` constant wall blocks the level-hood instantiation at the hull"

**Two claims, welded together.**

| claim | class | test |
|---|---|---|
| `countFo matrix = 328` | **MACHINE-CHECKED** | **HOLDS.** I reproduced it: `src/ProbeDD25G1.agda:54` |
| `Cnt.erase matrix refl` fails with `328 != 0` | **MACHINE-CHECKED** | **HOLDS.** `erase` demands `countFo φ ≡ 0` (`src/FOL/Count.lagda.md:598`) and discharges the `con` case by `Empty.rec (snotz p)` (`:595`) |
| "so the erase/embed route to the hull's carrier is closed" | **INFERENCE** | **FAILS.** The route is closed for *this spelling of the matrix*, not for the matrix |
| "so the level-hood instantiation at the hull is blocked" | **INFERENCE** | **FAILS.** Built the cure; it is green |

This is C-36 exactly. A failed substitution said `328 != 0`. It never
said that no constant-free spelling of the same matrix exists. One
does, and the file documents it.

### Blocker 2: "the code fiber's non-prop-ness blocks the inverse collapse"

| claim | class | test |
|---|---|---|
| "the code fiber is not a proposition" | **INFERENCE**, never machine-checked | **HOLDS as stated**, but it is about the wrong fibre |
| "the witness of a collapse value is merely a code" | **INFERENCE** | **FALSE.** The witness of a collapse value is a member of `M` (`Collapse.πX-member`, `src/V/Collapse.lagda.md:78`). Only afterwards is a member of `M` merely a code |
| "no canonical extraction exists without an order on the codes" | **INFERENCE** | **FAILS twice.** Leg one needs no order. Leg two has the order: the master itself proves it |

**The conflation, precisely.** `πX = sett ⟪ M ⟫ (λ m → π (⟪ M ⟫↪ m))`
(`src/V/Collapse.lagda.md:75-76`). So a collapse value's fibre is
`Σ[ m ∈ ⟪ M ⟫ ] (π (⟪ M ⟫↪ m) ≡ z)`. That IS a proposition, because
`π` is injective on `M` (`InjExt.π-inj`, `src/V/Collapse.lagda.md:277`) and `V` is a set. I
proved it: `isPropFib` at `src/ProbeDD25G3.agda:57`. So
`⟪ πX ⟫ ↪ ⟪ M ⟫` is constructive, with no choice and no order.

Only the SECOND leg, `⟪ M ⟫ ↪ Code`, has a non-prop fibre, because two
codes can have one value. And the tree solves that shape already:
`L.StageCardinal.Successor.h` (`src/L/StageCardinal.lagda.md:270-320`) takes a member of
`𝒟ₒ (Lset α)` that is *merely* some `defSet φ`, and picks the least
`count` value under the ordinal's own well-order
(`OrdSWO.ordSWO : SWO ⟪ α ⟫`, `:253`), with injectivity from
count-injectivity and `↪-inj` only. Its own comment says so at `:265`.

I transplanted that pattern. The order on the codes is
`CC.count`/`CC.count-inj`, which **this master already proves**
(`src/L/BoundedSubset.lagda.md:890-979`). The composite
`⟪ πX ⟫ ↪ ⟪ α ⟫` is what `β↪α` actually consumes (`:986-991`), so the
cure DELETES the `collapseCode` hypothesis rather than discharging it.

Every input is delivered: `hull-member` (`src/L/Hull.lagda.md:337-339`,
whose body is the identity), `ordSWO` (`:253`), `leastOf`
(`src/L/WellOrder/Base.lagda.md:158-160`), `lem` (a module parameter),
and `isExt M`, which the master already states as a hypothesis in its
own section 3 (`:315`).

## 3. THE 328 CONSTANTS

**They are all `con (numeralL k)`, the twelve arity tags, and the count
is a multiplicity effect, not a variety effect.**

There are exactly eight `con` sites in the whole 4,564-line master, at
`src/L/Condensation.lagda.md:1458, :1467, :1481, :1500, :1643, :1644`
(and two in Δ₀ witnesses at `:1658-1659`). `numeralL 0 = ∅ʟ`,
`numeralL (suc n) = sucʟ (numeralL n)`
(`src/L/Axioms/Numerals.lagda.md:175-177`).

I measured the decomposition (`src/ProbeDD25G1.agda`, green):

| piece | `countFo` |
|---|---:|
| `isCodeB` | 29 |
| `shapesB` | 20 |
| `closedB` | 8 |
| `DefinesB` | 4 |
| `envOneBnd` | 2 |
| `satGraphB` | 8 |
| **`DefBodyB`** | **41** = 29 + 8 + 4 |
| `StepAtB.stepBndAt` | 164 = 4 x 41 |
| **`LevelHood0.matrix`** | **328** = 2 x 164 |

So 328 is **eight copies of one 41-constant leaf**. The leaf's 41 come
from four helper definitions and two literals. The source is narrow.

**Does `[LJ-1.31]`'s cure apply? YES, and the file already runs it
next door.**

`[LJ-1.31]` cured `consAtL` because its constants were `con (# 0)`.
Here the tags run 0 to 11, so the emptiness trick alone does not
serve. But the file has a SECOND, more general constant-free idiom and
documents it as the house style:

> `src/L/Condensation.lagda.md:1111-1114`: "THE ELEVEN ROWS. ... The
> tag numerals are slots, so every formula is constant-free."

The rows reach it through `arTagB` (`:435`) and `arTagPairB` (`:450`),
which take the tag as a `Fin m` slot. The code-set description instead
uses the `*Bnum` family (`keyArBnum :1455`, `tagBnum :1465`,
`arTagPairBnum :1475`, `arTagBnum :1494`), which hard-codes the
numeral. **That is the two-spelling shape P-v names, and the brief
itself warned about it at `:92-93`.**

**I built the cure** (`src/ProbeDD25G2.agda`, green). It restates the
four leaf helpers with a `Fin m` tag slot, and everything above them:
`binShapeBS`, `unShapeBS`, `binFormBS`, `unFormBS`, `isTmBS`,
`bothTmBS`, `fstTmBS`, `closedBS`, `shapesBS`, `shapedBS`,
`hasWitnessBS`, `isCodeBS`, `envOneBndS`, `DefinesBS`. Results:

- every Δ₀ witness survives **unchanged in shape**: `con` and `var`
  both certify by `δ-≐`;
- `countFo (isCodeBS …) ≡ 0` by `refl` (`:324`);
- `countFo leafParts ≡ 0` by `refl` (`:343`), covering all 41 constant
  sources of one `DefBodyB` leaf;
- `Cnt.erase leafParts refl` typechecks (`:346`), so **the erase route
  opens**;
- `erase-Δ₀` applies (`:330`). That lemma sits at
  `src/L/BoundedSubset.lagda.md:505-518` with **zero consumers**. The
  return wrote the tool for this route and then declared the route
  closed.

**Cost, measured.** 256 code lines, three cold runs 4.66 / 4.68 /
5.00 user s, mean 4.78, spread 0.34 (7.1 percent). Import cone
1.85 / 1.88 / 1.94, mean 1.89. Marginal 2.89 s over 256 lines =
**0.0113 s per line**, under the DD24 bar 0.012716.

**The in-place edit is smaller than my copy.** My probe DUPLICATES the
chain; an in-place edit REPLACES it, so the net line delta is near
zero. And `DefBodyB` needs **no signature change**: it already takes
`N0 … N11 t0 t1` (`src/L/Condensation.lagda.md:2261-2266`), because
`satGraphB` already needs them. Its consumers `StepAtB` (`:2354`) and
`LevelHood` (`src/L/BoundedSubset.lagda.md:68`) do not move. **That is
`[LJ-1.31]`'s zero-consumer-edit property, again.**

**What the cure costs that is NOT free, and I want this on the record.**
A constant carries its value; a slot does not. Moving `numeralL k` into
the environment converts a syntactic fact into a site fact, "the slot
holds the numeral". That obligation is real. Two things make it
payable rather than a hidden new wall:

1. The twelve rows already run exactly this discipline, and the file
   says so at `src/L/Condensation.lagda.md:2413-2416`: "the tag
   columns hold the numerals".
2. **Nothing proves `DefBodyB`'s adequacy today.** There is no
   `DefBodyB`-agreement module in the file. So the slot spelling
   invalidates no delivered proof; it changes the shape of a proof
   nobody has written.

**And it composes with the hull.** `hull-closed` takes
`φ : Formula Code 1` **with constants** and absorbs them itself:
`cs : Vec Code (countFo φ)` at `src/L/Hull.lagda.md:127`. So the route
is: slot spelling gives `countFo ≡ 0` over `S`; `erase` gives a
parameter-free formula; `embed` gives a `Formula Code n`; the twelve
tag slots take `con` of the hull codes of the numerals, which exist
because `numeralL k ∈ Lset α ⊆ X` for infinite α; and `hull-closed`
absorbs those constants into the parameter vector. **No `absFo`, no
`placeFo`, no placement. P-u is not touched anywhere in this cure.**

## 4. IS THE SKELETON-TO-THEOREM GAP GLUE OR OBSTRUCTION?

**Glue for the connector, plus one real unbuilt semantic obligation.
It is not a shape mismatch.**

First, the dead-code fact, verified: `erase-Δ₀` (`:505`), `LevelHood0`
(`:520`) and `AtHullInstance` (`:450`) have **zero** use sites in the
master. `LevelHood`, `IsoInv`, `CollapseIso` and `DownReflect` feed
only `AtHullInstance`. So sections 1 to 3 and the `LevelHood0` half of
4A are entirely unconsumed. Only `isOrdAt`/`Amb` from 4A is live. The
return states this itself.

Now the shape question. Devlin's route to `levelIn` does **not** need
an ∈-induction on the collapse. It needs four things:

1. `M ≺ L_λ`, from `hull-closed` plus `ElemDown`;
2. the satisfaction iso `M ≅ πM`: **BUILT**, `IsoInv` (`:188-312`);
3. the level-hood formula is Σ₁: **BUILT**, `Σ₁-levelHood` (`:139`);
4. Σ₁ upward absoluteness at the transitive `πX`: the machine is
   delivered (`σ₁-up`, `FOL.Absoluteness`), and `AtStage` already
   carries an absoluteness instance at the stage (`ASt.AbsL`, used at
   `:411`).

**The skeleton the master built is exactly the skeleton this route
wants.** It is not the wrong shape. It is unconnected, and the one
connector is "state the level-hood formula as a `Formula Code 1`".
That is precisely what the 328 blocked, and what section 3 above
unblocks.

What is genuinely unbuilt, and which I did NOT build or price:

- **the adequacy of the level-hood formula at the hull's carrier.**
  The twelve-row table proves the bounded matrices agree with the
  machine at the CLASS carrier. Re-basing to `Lset λ` is real work.
  The machine exists; the work does not.
- **`ElemDown`** (`:404-406`). Note it is stated for ALL formulas, not
  only Σ₁. That is stronger than Devlin needs and is what a full
  Skolem hull gives, so `hull-closed` is the right ingredient. Nothing
  discharges it, and `down-reflect` is conditional on it.

So: the gap is glue at the connector and an obstruction at the
adequacy. The return called the connector the obstruction and never
reached the adequacy.

## 5. DID THE BRIEF CAUSE IT?

**Partly yes, and two brief defects are nameable.**

**Defect 1, and it is the direct cause.** The brief said, at
`_build/briefs/LJ-1.7.md:88-91`:

> "**P-u.** Certify BEFORE you place. ... **If you need `absFo` or a
> placed `Δ₀`, STOP and report it**: the wall is flat at 8 GB across
> constant counts 0, 1, 2 and 5."

That is correct and it is load-bearing. But it pre-loads one frame:
*constants lead to placement, placement is a wall, so stop and
report*. When the agent met `countFo = 328` it wrote the frame's
conclusion. **The brief never named the third door**, which is not
placement at all: restate the formula constant-free. The brief DID
cite P-v two lines later (`:92-93`), which is the pointer, but it
framed P-v as a cost law ("paid 10 to 15x at its leaves"), not as the
cure for a constant. An agent reading `:88-93` in order learns "stop"
before it learns "respell".

**Defect 2. The dispatch bundled two different jobs in two different
masters.** The brief asked for the condensation theorem AND 5.5, eight
obligations, 1,675 lines. The assembly is 640 template lines in a NEW
master. The leaf surgery is inside `src/L/Condensation.lagda.md`,
which is 4,564 closed lines with a 56 s cold check. Those are not one
block. The agent spent its budget on the assembly, which it did well,
and met the leaf at the end with nothing left. **The brief also told
it the substrate was verified complete** (`:45-59`, listing "the
bounded graph matrices" as delivered), which invited consuming
`DefBodyB` as given rather than questioning its spelling.

**What the brief got right, and it should be kept.** D-30's framing
(`:61-72`) produced the hull-instance theorem instead of the general
theory, and that is where the 1,675-to-888 reduction came from. The
"read `[LJ-1.46]` WHOLE" instruction was obeyed. The rate reporting
was obeyed exactly.

**For the next brief:** state P-u with its exception in the same
breath. "A constant count is not a placement wall. Before you report a
constant as a blocker, check the file's own constant-free spelling for
that combinator." And split the leaf surgery from the assembly.

## 6. WHAT IT WOULD COST TO DISCHARGE `levelIn` AND `cover`

I give only what I measured, plus what is structurally forced. I do
not have a number for the adequacy chain and I will not invent one.

**Measured.**

| piece | what I built | lines | cold user s |
|---|---|---:|---:|
| constant-free leaf chain | `src/ProbeDD25G2.agda` | 256 | 4.78 mean (cone 1.89, marginal 2.89) |
| `⟪ πX ⟫ ↪ ⟪ α ⟫`, no `collapseCode` | `src/ProbeDD25G3.agda` | 104 | 0.87 mean |

**Structurally forced, from the measurements.**

- The leaf respelling is an **edit, not an addition**. My 256 lines
  duplicate what the file has; in place it replaces. `DefBodyB`'s
  signature does not change and no consumer moves. The formula's size
  and its Δ₀ certificate do not change, so P-l predicts no second cost,
  and my marginal rate 0.0113 is consistent with that.
- One piece I did NOT cure in place: `SatGraphB` (`:2172-2260`, about
  90 lines) calls `closedB` once. Its own `N0 … N11` parameters are
  already in scope, so the edit is passing arguments it already holds.
  I built `closedBS` and it is green; only the threading is unbuilt.
- `collapseCode` is **removed**, not discharged. The master's `β↪α`
  (`:986-991`) currently composes `collapseCode` then `CC.count`; the
  probe's composite replaces both legs and needs no new hypothesis.
  The master's `hotel`, `sq` and `fin-inj` hypotheses are untouched by
  this and remain.

**Unpriced, and this is the honest remainder.**

- The adequacy of the level-hood formula at the hull's carrier. This
  is the twelve-row table's first real consumer. `[LJ-1.46]`'s O1
  priced its carrier facts and transfer legs; I did not re-measure
  them and I do not endorse that price.
- `ElemDown`. `[LJ-1.46]` O2 priced it at 120 lines / 2 s. I did not
  test that.

**So the shape of the remaining work changes.** Before this review the
residue was "two walls plus an unpriced semantic gap". After it, the
residue is "one unpriced semantic gap, with its connector unblocked
and its cardinality leg already built".

## 7. WHAT I AM NOT SURE OF

1. **My cure is a copy, not an in-place edit.** I proved the slot
   spelling typechecks, keeps Δ₀, and reaches `countFo ≡ 0` at the
   `isCodeB` and full-leaf level. I did NOT edit
   `src/L/Condensation.lagda.md` and I did NOT re-run its 56 s check.
   An in-place edit could meet a name clash or an arity surprise I did
   not see. I judge that unlikely, because `DefBodyB` already holds the
   slots, but it is unmeasured.
2. **I did not thread the cure through `SatGraphB`.** Eight of the 41
   constants per leaf live behind that module's single `closedB` call.
   The cured `closedBS` is green; the threading is not built.
3. **The site-fact obligation is real and I did not pay it.** The slot
   spelling needs "the slot holds `numeralL k`" at every consuming
   site. I argued this is payable because nothing proves `DefBodyB`'s
   adequacy today and the rows already run the discipline. I did not
   build one such site fact.
4. **I did not test the adequacy chain at all.** Sections 4 and 6 say
   the machine exists. That is a structural reading of
   `AtStage.AbsL`, `σ₁-up` and `IsoInv`, not a measurement. It could
   still be the expensive part, and it could still hide a real
   obstruction. If it does, the return's overall stop was right for a
   reason the return did not give.
5. **My `⟪ πX ⟫ ↪ ⟪ α ⟫` is generic and needs `isExt M`.** The
   master's `HullStage` does not currently carry `isExt M`; its
   section 3 does (`:315`). Adding it to `HullStage` is Devlin's own
   hypothesis and should be cheap, but it is an added hypothesis and I
   did not wire it.
6. **Timings are from a shared session machine.** Spreads are 2.3 to
   7.1 percent, inside the predicted band, and no verdict here sits
   inside a spread. The absolute seconds would shift.
7. **I did not re-verify the master's own 9.91 s or its 888 lines.**
   The orchestrator states both as self-verified and I took them.
8. **On DD25's own record.** This is an overturn, and the retrospective
   predicted it: both deciding claims were inferences. I looked hard
   for the uphold. The uphold I found is on the numbers, which are all
   correct, and on the honesty of the return, which named its own C-35
   tension without being asked. The return's failure is narrow and
   specific: it read a machine-checked `328 != 0` as a proof that no
   term connects the two types. That is C-36, and C-36 is in the
   brief's own mandatory list.
