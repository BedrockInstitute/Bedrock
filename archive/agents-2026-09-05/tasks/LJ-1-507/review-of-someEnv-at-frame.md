# review-of-someEnv-at-frame: the gap is not unpaid, it is FALSE

slot: `coder`. This file is how the slot states a stop
(`dev/pod/instructions/coder.md`, the module-hypothesis clause). It does
not close the task: the critic reads it.

## THE STOP, IN ONE SENTENCE

`someEnv-at-frame` is **NOT** inhabited, and the reason is not that
`arNumC` is too weak: **`[LJ-1.504]`'s `someEnvDef-gap` is a FALSE
statement at `[LJ-1.504]`'s own frame**, machine-checked at
`agents/tasks/LJ-1-507/Probe507.agda:257-268`, so `gap-suffices`
(`agents/tasks/LJ-1-504/Probe504.agda:133-138`) is a true implication out
of an empty antecedent and it inhabits nothing.

## WHAT THE BRIEF ASKED, AND WHAT EACH STAGE MEASURED

The brief asked for the gap to be discharged from `arNumC` and
`gap-suffices` then applied. Three measurements, in the order they ran.

1. **W3 IS GO. The two frames agree, slot for slot.** `frames-agree`
   (`agents/tasks/LJ-1-507/Probe507.agda:177-184`) states `arNumC` at
   `[LJ-1.504]`'s vector and feeds it into `[LJ-1.500]`'s rebuilt `Num`,
   which accepts it. Exit 0, `runs/w3-1.out`. The negative control
   (`Num` at `K6` instead of `iC`) is exit 42 with
   `fst g2 != L.Constructible.Lset lam of type V ℓ`
   (`runs/w3-control.out:3-4`), so the elaborator does resolve the twenty
   slots and the green run is not a vacuity.
   **THE FRAME QUESTION THE BRIEF FEARED DOES NOT EXIST.**
2. **`arNumC` does not reach the gap, and Agda names the reason.**
   `runs/attempt-0.out`, exit 42:
   `(fst ar) != (fst c) of type (V ℓ)`. The gap hands a member of `K`
   where `arNumC`'s only consumer wants a member of the CODE SET.
   `gap-with-code` (`Probe507.agda:213-224`) says the same thing
   constructively: give the gap's telescope **three** more arguments, a
   tag `k`, the code membership at `iC` and the shape equation, and
   `arNumC` pays in one line.
3. **THE GAP IS FALSE.** `gap-is-false : someEnvDef-gap → Empty.⊥`
   (`Probe507.agda:257-268`), exit 0, `runs/final.out`, under
   `--safe`, with no postulate and no hypothesis beyond the frame's own
   telescope.

## THE REFUTATION, IN THREE LINES OF MATHEMATICS

`KValue` DELIVERS a `KFacts` value at this frame
(`src/L/Condensation.lagda.md:7411-7425`). Two of its fields are all the
refutation needs:

- `numK0` puts `numeralL 0` in `K` (`src/L/Condensation.lagda.md:7416`).
- `pairK` closes `K` under the L-pair (`src/L/Condensation.lagda.md:7423`).

So `prʟ (numeralL 0) (numeralL 0)` is a member of `K`
(`Probe507.agda:251-255`), and the gap would call it a numeral. It is not
one: `pr a a` is `⁅ ⁅ a ⁆s , ⁅ a , a ⁆ ⁆` (`src/V/Coding.lagda.md:175-176`),
whose only two members each hold `a`; an ordinal is transitive
(`src/L/Constructible.lagda.md:141-142`), so `a` would belong to `pr a a`
and hence to itself, which `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`)
forbids; and every numeral IS an ordinal
(`src/L/Ordinal.lagda.md:244`). That is `pr-self-not-numeral`
(`Probe507.agda:124-126`).

**NEGATIVE CONTROL.** With a genuine numeral at the `ar` slot instead of
the pair, the same term is exit 42 (`runs/refute-control.out:3-9`). The
refutation depends on the witness and is not a type error in disguise.

## WHAT THIS CONFIRMS, AND WHAT IT DOES NOT

**CONFIRMED.** `[LJ-1.504]`'s own review suspected exactly this and said
so honestly: `agents/tasks/LJ-1-504/review-of-someEnv-reaches.md:49`
reads "**I did not machine-check this and I do not report it as
measured.**" This task machine-checked it. `[LJ-1.504]`'s reasoning
there used `B₀`; the refutation delivered here uses `pairK` and `numK0`
instead, which are the record's own fields and need nothing from
`SupplyEnv`.

**NOT CLAIMED.** I do **NOT** claim `someEnvDef {9} KV.iK (gam' …)` is
false. I refuted ONE route to it, the route this brief named. Whether
`[LJ-1.172]`'s refutation of the unrestricted `envSetK` reaches
`someEnvDef` itself is still the measurement nobody has made
(`agents/tasks/LJ-1-504/lj-1.504-report.md:224-232`), and it is a
mathematician's brief.

## WHAT THE RULING NOW FACES

**THE RULING ON `arNumC` IS NOT OVERTURNED. IT IS VINDICATED AND
RELOCATED.** The brief ruled the weaker hypothesis because it changes no
field type. `gap-with-code` shows `arNumC` is sufficient for the numeral
the supplier needs, so nothing stronger is required and
`[LJ-1.506]`'s equation stays off the list. What the refutation moves is
WHERE the hypothesis has to sit: not in a gap the record can bridge, but
in `someEnvDef`'s own type.

**THE THREAD IS NO LONGER CONVENIENT. IT IS THE ONLY ROUTE LEFT.** The
sweep in `lj-1.507-report.md` counts the sites, and the archive prices
the same SHAPE of change once already:
`archive/dev/LJ-dispatch-index.md:249` records `[LJ-1.173]` restricting
`envSetK` to a numeral arity at **21 sites for 77 lines**. That is an OLD
price at an OLD tree and I do not carry it as this task's number.

**I did not edit `someEnvDef` and I did not weaken it. Nothing landed in
`src/`. No commit. No push.**
