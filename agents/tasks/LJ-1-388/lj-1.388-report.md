# [LJ-1.388] The internal product of two L-elements, and the ambient bridge into it

Date: 2026-08-19. Slot: `mathematician`. Probe:
[`Probe388.agda`](Probe388.agda), 329 lines, GREEN.

## VERDICT

**GO. The internal product is built at generic `a` and `b`, and the bridge is
an injection.** Both obligations are green:

- `prodL : (a b : S) → S`, at `agents/tasks/LJ-1-388/Probe388.agda:296`
- `prod-bridge : (a b : S) → (⟪ fst a ⟫ × ⟪ fst b ⟫) ↪ ⟪ fst (prodL a b) ⟫`,
  at `agents/tasks/LJ-1-388/Probe388.agda:299`

**THE L-MEMBERSHIP HALF IS NOT THE EXPENSIVE HALF. It is 32 code lines, and it
is one separation over a stage.** The brief expected it to cost, and named two
candidate routes for it. **Neither route removes that separation.** The
archived one is MEASURED to be the same set, so it needs this separation and an
extensionality on top; the two-replacement one is UNMEASURED and needs two
object-language artifacts the tree does not hold. Section 2 gives both, and
marks which is measured and which is not.

**PRICE: 125 code lines and 1.39 wall seconds**, at the wide caliber
`-A64m -I0 -M8g` with one Agda process. Section 3 divides the price.

## 1. What was asked, and what is delivered

The brief asked for one object and one bridge. Both are delivered, at GENERIC
`a` and `b`. No line of the construction names an ordinal, a stage or a site.

| Deliverable | Line | What it says |
|---|---|---|
| `prodL` | `Probe388.agda:296` | the L-element whose members are the pairs |
| `prod-bridge` | `Probe388.agda:299` | the ambient injection into its member type |
| `prodL-in` | `Probe388.agda:303` | a pair of members is a member |
| `prodL-out` | `Probe388.agda:307` | a member is merely a pair of members |
| `prodL-is-F2` | `Probe388.agda:313` | the archived ambient object IS this one |
| `leg1-fst` | `Probe388.agda:328` | `Leg1`'s first conjunct, at any `c` |

**THE MEMBERSHIP READING IS DELIVERED IN BOTH DIRECTIONS**, which is item 1 of
the brief's WHAT IS MISSING. `prodL-in` and `prodL-out` are together the
statement that `F2-spec` makes for the ambient `sett` form
(`archive/src/2026-08-09-rud-route/L/Rud/Ops.lagda.md:213-221`).

**`Leg1`'S FIRST CONJUNCT IS ONE APPLICATION.** `leg1-fst c = prod-bridge c c`
(`Probe388.agda:328-329`). At `c := δ` and `P := prodL δ δ` this is exactly the
first conjunct of `Leg1` at `agents/tasks/LJ-1-386/Probe386.agda:288`. **The
probe states it at generic `c` and not at `δ`**, because `[LJ-1.386]` measured
that nothing in the tree certifies `+ω ω` as a band ordinal
(`agents/tasks/LJ-1-386/lj-1.386-report.md:211-236`, which is where that
section sits after the amendment; see section 5). The ordinal enters when
the route names it, and not before.

## 2. Which route was tried, in which order, and what each cost

**READ THIS SECTION AS A DEVIATION FROM THE BRIEF'S ORDER.** The brief said:
try the archived ambient form first, price its L-membership, and fall back to
two nested replacements if it stalls. **This probe did neither of those two.**
It read the tree first, found a third route, and built that. The archived form
was then settled by measurement rather than by attempt. What follows is what
each route costs and how that cost is known.

### 2.1 The route that was built: ONE separation over a stage

The product of `a` and `b` is bounded. Every Kuratowski pair of a member of `a`
with a member of `b` lies two stages above any stage that holds `a` and `b`,
because the pair is two unordered pairs deep. **The tree states that count and
says it was stated for exactly this use**:
`pr∈Lset-suc` at `src/L/Axioms/Basic.lagda.md:596-599`, with the reason in the
prose at `src/L/Axioms/Basic.lagda.md:529-533`.

So the product is a definable subset of `Lset (sucV (sucV σ))`, and full
separation in L delivers it as an L-element:
`hasSeparationL` at `src/L/Axioms/Full.lagda.md:144-145`. The stage is an
L-element by `LsetS` at `src/L/Axioms/Basic.lagda.md:160-161`.

**`isL` IS NEVER PROVED IN THIS PROBE. It is returned.** `hasSeparationL` gives
an element of the L-carrier, so the L-membership arrives with the object. The
whole of the L-membership half is:

- the bound, `Probe388.agda:99-141`, 26 code lines
- the separation, `Probe388.agda:181-196`, 6 code lines

### 2.2 The archived ambient form: it PORTS WHOLE, and it is the same set

`F2` ports in two lines, verbatim, with the `opaque` seal dropped
(`Probe388.agda:85-86`, from
`archive/src/2026-08-09-rud-route/L/Rud/Ops.lagda.md:210-211`).

**AND IT IS THE SAME SET AS THE SEPARATION. This is measured, not argued:**

```agda
prodL-is-F2 : (a b : S) → F2 (fst a) (fst b) ≡ fst (prodL a b)
```

at `Probe388.agda:313`, proved by extensionality at `Probe388.agda:289`. The
proof is 25 code lines (`Probe388.agda:251-294`) and it needs no port of
`F2-spec`: `sett` membership asks for a preimage merely
(`src/V/Hierarchy.lagda.md:45-49`), so the two inclusions read straight off
`prodL-in` and `prodL-out`.

**SO THE ANSWER TO THE BRIEF'S QUESTION IS: the archived construction ports,
and it buys the ambient object only.** What it never carried is `isL`, and the
separation is what supplies it. The brief expected the archived form's bridge to
be nearly free because its index type is literally `⟪ x ⟫ × ⟪ y ⟫`. **That
expectation does not hold, and the reason is measurable**: `⟪ sett X ix ⟫` is
not `X`. It is the library's deep monic presentation
(the cubical library's `Cubical/HITs/CumulativeHierarchy/Properties.agda:220-221`,
`⟪ X ⟫ = V-repr X .fst .fst`), so the bridge out of `⟪ x ⟫ × ⟪ y ⟫` must go
through a fiber even for `F2`. **And because the two sets are equal, the bridge
into `F2` IS this bridge transported along `prodL-is-F2`**, so the archived form
buys none of the 22 lines the bridge costs (`Probe388.agda:216-249`).

### 2.3 The two nested replacements: NOT TRIED, and the reason is a shape

**This route is UNMEASURED. No number below is a price for it.** The probe did
not try it, because the separation route looked cheaper by a shape argument
that is checkable:

- `hasReplacementL` (`src/L/Axioms/Full.lagda.md:277-280`) takes a
  `Formula S 2` and a functionality proof. To build the product it must be
  applied twice. **The outer application needs the relation "y is the slice of
  x with b" as an object-language formula, plus its functionality.** Neither is
  in the tree.
- `hasSeparationL` (`src/L/Axioms/Full.lagda.md:144-145`) takes a
  `Formula S 1` and nothing else. **The formula it needs is one bounded
  existential over `a`, one over `b`, and the delivered pair atom `prAtL`
  inside** (`Probe388.agda:150`, and `prAtL` at
  `src/L/Coding/Model.lagda.md:122`).

The bound is what makes separation admissible, and `pr∈Lset-suc` is the
delivered bound. **A route that needs no new object-language formula looked
better than one that needs a new formula AND its functionality proof.** This is a statement about the two signatures and it can be
checked at the two line numbers above. It is not a measurement of the
replacement route, and it must not be quoted as one.

## 3. The price

**Measured at the wide caliber `-A64m -I0 -M8g`, one Agda process, three runs:
1.39 s, 1.38 s, 1.39 s.** The empty-module floor on this machine, at the same
caliber and on the same day, is 0.06 s
(`agents/tasks/LJ-1-386/runs/accept-2.out:16`, caliber at `:5`, one slot at
`:7`). So the content costs about 1.33 s.

| Half | Lines in `Probe388.agda` | Code lines |
|---|---|---|
| the bound (PART 1) | 99-141 | 26 |
| the formula and its reading (PART 2) | 143-179 | 22 |
| the object, one separation (PART 3) | 181-196 | 6 |
| the membership reading (PART 4) | 198-214 | 9 |
| the bridge (PART 5) | 216-249 | 22 |
| the archive identification (PART 7) | 251-294 | 25 |
| the obligations and `Leg1`'s conjunct | 295-329 | 13 |
| header, module and imports | 1-84 | 35 |

**The mathematics is 125 code lines. The L-membership half is 32 of them**, and
the archive identification, 25 lines, is not part of the obligation: the brief
asked which route ports, and this is what answering it by proof cost.

**AGAINST THE ONE DELIVERED COMPARABLE.** `module Range`
(`src/L/Coding/Injection.lagda.md:186-218`) is ONE replacement with its
functionality proof: 33 raw lines, 25 code lines by the same filter. The
product is 125 code lines. **So the product costs about five times the
comparable, and `[LJ-1.386]` was right to refuse to transfer the 33**
(`agents/tasks/LJ-1-386/lj-1.386-report.md:268-272`, its post-amendment home):
the shape that
dominated is the bound and the bridge, and neither has any counterpart in
`module Range`.

## 4. What this report does NOT say

- **It does not report a bijection or an equivalence.** `prod-bridge` is an
  injection and nothing more, and `_↪_` is the injection type at
  `src/L/Cardinal.lagda.md:47-48`.
- **It does not cure either wall.** It says nothing about `L3.32-T43` or about
  the truncated square law (`archive/dev/TASKS-archived.md:78-82`).
- **It does not certify `+ω ω`, or any other ordinal, as a band ordinal.**
  Nothing in the probe names an ordinal.
- **It does not price the two-replacement route.** See section 2.3.
- **It does not contradict the literature digest.**
  `dev/literature/rudimentary-functions.md:68` lists `F2` as a rudimentary
  BASIS operation, and `:144` records Devlin's `BS` as carrying the cartesian
  product as a primitive. **Those are statements about weak systems that have
  no separation over stages.** This route has one
  (`src/L/Axioms/Full.lagda.md:144-145`), and it has the stage bound
  (`src/L/Axioms/Basic.lagda.md:596-599`). The digest priced a different
  system, so it prices nothing here, which is what the brief said it would do.
- **It does not say the product is free.** It says the product costs 125 lines,
  and that the L-membership is 32 of them.

## 5. The `[LJ-1.386]` citations, re-read

The brief warned that `[LJ-1.386]` was re-dispatched at 05:00:04Z and might
still be writing. **It is finished: its acceptance record is
`agents/tasks/LJ-1-386/runs/accept-2.out`, exit 0, all six conjuncts held
(`:10-15`).** Its two files were re-read today.

**THE WARNING WAS CORRECT, AND IT COST THE BRIEF THREE RANGES.** `[LJ-1.386]`
amended its report after the brief was built, and it says so itself: 「I edited
only this report」 (`lj-1.386-report.md:258-260`). **Three of the six ranges the
brief took from the REPORT have moved by six to eight lines, and one of the
three now holds none of what it was cited for. Every range the brief took from
`Probe386.agda` still holds.**

| The brief's citation | What is there now |
|---|---|
| `Probe386.agda:287-291`, `Leg1`'s first conjunct | `Leg1` is at 287-290, and its first conjunct is line 288. Line 291 is blank. The `291` came from `lj-1.386-report.md:274`. |
| `Probe386.agda:287-295`, `Leg1` and `leg1-gives-sq` | holds as a range; `leg1-gives-sq` is at 294-302 |
| `Probe386.agda:287-302`, both, green | **holds exactly** |
| `Probe386.agda:264-284`, `code-untruncates` | **holds exactly** |
| `Probe386.agda:264-268`, the door | holds; the declaration is 264-267 |
| `lj-1.386-report.md:127-133`, no product in `src/` | **holds at its tail.** The measured sentence is at 130-136, and the `grep` that carries it is at 132-133. |
| `lj-1.386-report.md:207-232`, `+ω` has no consumer | **MOVED.** Section 6 is 211-236, and the `grep` that measures it is at 214-216. |
| `lj-1.386-report.md:254-266`, the widest term and its probe | **MOVED.** Section 8 is 262-277. |
| `lj-1.386-report.md:256-264`, `module Range` is a shape comparable | **MOVED, and this range holds none of it.** The sentence is at 268-272. |
| `lj-1.386-report.md:106-113`, `Good` names no target | **holds.** Line 108 carries「the three conjuncts are free wherever the witness sits」and 110-117 carries the rest. |

**WHAT THIS DOES NOT CHANGE.** Every claim the brief drew from those ranges is
still in the report, and each one is still true of the tree. **Only the line
numbers moved.** No premise of this task rested on a line number that turned
out to hold something else.

**EVERY `src/` AND `archive/` CITATION IN THE BRIEF WAS RE-READ AND HOLDS**,
which is what the brief predicted: those paths are outside `[LJ-1.386]`'s write
scope. The eight premises were each checked at their own `file:line`.

## 6. The widest unmeasured term now, and the probe that measures it (W3)

**`Leg1` had two conjuncts. One is now built. The widest unmeasured term is the
OTHER one**: the truncated coded injection from `prodL δ δ` into `δ`,

```agda
∥ Σ[ A ∈ Mem (Lset (SiteBound.β P)) ] InjCode (SiteBound.up P A) P δ ∥₁
```

at `agents/tasks/LJ-1-386/Probe386.agda:289-290`. **It is the cardinal
arithmetic, and this probe says nothing about it.**

**THE PROBE THAT WOULD MEASURE IT** is one dispatch that builds an `InjCode`
whose source is `prodL δ δ` and whose target is `δ`, at ONE site, and reports
GO or NO-GO. `[LJ-1.386]` built the shape of such a thing at the identity
(`Probe386.agda:94-193`, the four conjuncts of `InjCode` at source `D` and
target `D`), so the shape is delivered and the content is not. **The estimate
is one best-effort number with a named basis: about 130 code lines, on the
basis of THIS probe as a delivered comparable of shape** (one object in L, its
membership reading, and one readback). **It is not a comparable of size**: this
probe's dominant cost was the stage bound, and a coded injection into `δ` has
no stage bound in it. **Do not quote 130 as a price.**

**WHAT WOULD REOPEN THIS TASK.** Two things, and neither is likely:

1. A consumer that needs `prodL` inside `src/`. This probe is in
   `agents/tasks/` and lands nothing. Moving it to `src/` is a separate task
   with a separate price, and this report does not price it.
2. Evidence that `prodL`'s members are not the intended ones. The reading is
   `prodL-out` at `Probe388.agda:307`, and it is the only statement of what the
   members are.
