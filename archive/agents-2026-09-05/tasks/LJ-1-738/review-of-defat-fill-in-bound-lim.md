# Review of `defat-fill-in-bound-lim`

**NO-GO, STATED. The obligation's type is stated, not inhabited, and the
clause forbids the inhabitant.** The brief's type takes
`Sat-in-carrier-lim` as a module hypothesis, and that hypothesis's
predecessor report is NO-GO and names the statement FALSE at the full
ruled scope:

- agents/tasks/LJ-1-736/lj-1.736-report.md:13: "verdict: **NO-GO,
  STATED.**"
- agents/tasks/LJ-1-736/lj-1.736-report.md:15: "prices it FALSE at the
  full ruled scope"
- agents/tasks/LJ-1-736/review-of-Sat-in-carrier-lim.md:3: "**NO-GO.
  The obligation's type is FALSE as stated, at the full ruled"

The clause of `dev/pod/instructions/coder.md` (a module hypothesis
taken from a predecessor is the type that predecessor delivered): take
the type from the probe that typechecked and the verdict from the
report; if the report is NO-GO or names the statement FALSE, stop and
say so with `file:line`, and do not inhabit the brief's type. The type
the probe typechecked is Probe736.agda:147-153 (stated, not
inhabited); the verdict is the report's. So the brief's type rests on
a false premise, its only possible inhabitant is vacuous, and this
brief's own premise 1 rules that "A vacuous inhabitant is not a GO."

## Which lim hypothesis does not reach the relativized `DefBody`

`Sat-in-carrier-lim`, as delivered. The other two hypotheses are real:

- `keyS-in-carrier-lim`: INHABITED (Probe729.agda:202-208; GO at
  lj-1.729-report.md:10, :53).
- `envSet-in-carrier-lim`: INHABITED (Probe735.agda:65-71; GO at
  lj-1.735-report.md:13).

The third one is not. The 736 defect is the ALPHABET, not the stage
height: `Sat-in-carrier-lim` quantifies over `Formula S n`
(Probe736.agda:152), whose constants range over ALL L-sets, and the
atom clause of `cond` transports a constant's global membership into
`Sat`'s extension. That transport is machine-checked in both
directions (the kernel, Probe736.agda:88-135, green at
runs/p-33.out), and `closedω γ` cannot absorb what never sits below
γ: the missing height is in a CONSTANT, not in an iterate. The
diagonal that would close a machine-checked `⊥` (one constructible
real of construction stage above γ) is unlanded and is priced by the
736 review at far more than a probe.

## Why the site consumes exactly the false scope

The landed unbounded `fill` concludes at

    (Sat A (toS ψ) ∷ keyS A ψ ∷ z ∷ γ) ⊨ DefBody w

(src/L/Coding/Powerset.lagda.md:500, conclusion at :502), and `toS ψ`
is `mapFo (asConst A) ψ : Formula S 1`. So the DefAt fill consumes its
Sat bound AT THE WIDE ALPHABET: the hypothesis the obligation feeds is
`Sat-in-carrier-lim` instantiated at `φ := toS A ψ`, which is exactly
the scope the 736 report prices FALSE. The two sibling GOs do not
cover this conjunct -- the key bound's formulas are over
`⟪ fst A ⟫` (the 729 shape), and the envSet bound is about `envSet`
only -- so the assembly has two of its three pieces and no honest
third.

This sharpens 736's corrected-target list for THIS site:

1. **Carrier-bounded alphabet** (736's correction 1) does not
   directly feed the DefAt site: the fill's environment carries
   `Sat A (toS A ψ)` with `toS A ψ : Formula S 1`, so a corrected
   bound stated only over `⟪ fst A ⟫` would need a toS-bridge to
   reach the consumption.
2. **Bounded constants** (736's correction 2) fits the site's shape:
   every constant of `toS A ψ` is an `asConst A m` (mapFo applies the
   relabelling to every constant slot; the landed
   `defSet-Sat` chain already reads `Sat B (mapFo asConst ψ)` at
   src/L/Coding/Bridge.lagda.md:623), and each `asConst A m` is
   `intoL (ιA m)` (src/L/Coding/Bridge.lagda.md:124-125), which
   carries the carrier's own members' stage. Whether that side
   condition closes cheaply from the 729 helpers is UNMEASURED here
   and the corrected scope is UNRULED; it must be priced after a
   ruling, not before. No corrected type is stated in Probe738.agda:
   inventing one would be inventing a specification.

## What is and is not machine-checked

The delivered probe (agents/tasks/LJ-1-738/Probe738.agda) is green,
EXIT=0, under `--cubical --safe --guardedness`, no postulate, no hole.
It machine-checks the TYPES only: the three hypothesis types restated
from their predecessors' probes (729's signature, 735's signature,
736's stated type, each with its verdict in the comment) and the
obligation's type stated under its exported name with no inhabitant.

No new refutation was re-run here. The falsity mechanism at this site
is the 736 diagonal, which the 736 review prices at far more than a
probe; re-measuring it would re-fund that diagonal, and the clause
needs only the predecessor's verdict, which exists. The honest split
is therefore the 736 review's own: the kernel is machine-checked, the
refutation is its stated reduction, and this dispatch adds no
measurement beyond the verdict's application to this site.

## Do not re-fund

- The 736 kernel (Probe736.agda:88-135) and its honest accounting.
- The 729 climb and `keyS-in-carrier-lim`, `envSet-in-carrier-lim`
  and its landed supply-side route, `relativize-correct`, the
  unbounded `fill`, the 730 rank chain.
- Any future claim to inhabit `Sat-in-carrier-lim` at `Formula S n`:
  the 736 review asks that such a return be checked against the
  alphabet observation first. The same applies to any future claim to
  inhabit this obligation's type while `Sat-in-carrier-lim` stands
  delivered FALSE.

## What a GO would earn, and what gates it

Unchanged from the brief: the bounded payload `stage-read`'s backward
half feeds, at the ruled scope. The gate is a ruling that delivers a
corrected Sat bound covering the toS image; per 736's review the
ruling is the mathematician's call. Until then the assembly has no
machine-checked route, and no brief should price one against the
offered hypothesis set.

## Price

| item | value |
|---|---|
| probe lines | 198 total, 180 non-blank, raw `.agda`, in-fence count 0 (the ratio bar cannot fire) |
| verdict run | 1.54 s, 402,358,272 B peak (`runs/p-1.out`) |
| floor | the file itself: the probe carries no proofs, so the frame is the whole cost |
| heap wall | none; 18.7 percent of the 2,147,483,648-byte wide cap |
| caliber | `-A64m -I0 -M2g`, set on the pane by the program, never touched here |
