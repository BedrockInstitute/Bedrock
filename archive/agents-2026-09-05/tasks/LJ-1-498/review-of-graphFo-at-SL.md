# NO-GO: `graphFo-at-SL` at an arbitrary stage

**The obligation is NOT inhabited, and it must not be.** This file is the stop
the brief asked for, under the brief's own D-10 clause:

> If the list is not empty, name each constant and say whether it lies in the
> stage, and if one does not, STOP.

## The list is not empty

`countFo (LsetGraphAt w b) ≡ 664`, machine computed and asserted GREEN at
agents/tasks/LJ-1-498/Probe498.agda:63-64. The census, its attribution and its
`file:line` rows are in `lj-1.498-report.md` under `## THE CONSTANT CENSUS`.

## One constant does not lie in the stage

Every one of the 664 is `con (numeralL k)`, entering at exactly two sites:
src/L/Coding/Model.lagda.md:586 and src/L/Coding/Shape.lagda.md:179. Its
underlying set is `# k` (src/L/Axioms/Numerals.lagda.md:179).

The obligation quantifies over the stage. `graphFo-at-SL` must hold at an
ARBITRARY `α : S`, and `⟨ # k ∈ˢ Lset α ⟩` has no supplier at an arbitrary `α`.
**Nothing in `src/` proves it and nothing can, because it is false.**

## Why the type was not inhabited anyway

It could have been. `mapFo f (LsetGraphAt w b)` typechecks for ANY total
`f : CS.S → SL`, and a junk-defaulted `f` is writable under `lem`. **That term
would have the brief's type and none of its meaning**: `mapFo` moves the
constants, so a map that is wrong on the constants makes the formula say
something else. The brief forbids the total map and the brief is right.

## What is NOT the wall

`[LJ-1.494]` names the wall as a missing map `CS.S → SL`
(agents/tasks/LJ-1-494/lj-1.494-report.md:367). That statement is TRUE and it
is the wrong instrument. `Relabel` (src/FOL/Manipulation/Bounding.lagda.md:146)
relabels along a PARTIAL map and needs no total one; its own prose at
src/FOL/Manipulation/Bounding.lagda.md:135-138 names this instance. The
instance is built and green at agents/tasks/LJ-1-498/Probe498.agda:140-149,
together with

    graphFo-at-SL-given : {n : ℕ} (w b : Fin n) → Wall w b → Formula SL n

So the obligation is one certificate away, not one map away.

## What would turn this into a GO

`Wall w b = BoundedFo P (LsetGraphAt w b)`, 664 leaves, every leaf
`P (numeralL k)`. It reduces to `NUM = (k : ℕ) → P (numeralL k)`, and **`src/`
already proves `NUM` at a limit stage**: `num∈λ`,
src/L/Coding/Bound.lagda.md:139-140, wired in and green at
agents/tasks/LJ-1-498/Probe498.agda:204-214.

Eight of the 664 leaves are discharged from `NUM` alone
(agents/tasks/LJ-1-498/Probe498.agda:185-196). The residue is about 80 to 110
lines, priced in the report.

**So the next brief is `wall : NUM → BoundedFo P (LsetGraphAt w b)` at a LIMIT
stage, and not `graphFo-at-SL` at a variable one.**

Nothing landed in `src/`.
