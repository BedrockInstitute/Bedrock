# Review of `hier-in-stage-limit`: STOP, and the reason is in the source

VERDICT: **STOP, STATED.** The obligation is not built. W3 is a GO. The
brief's model of the price is wrong in a way that the primary text settles,
and the correction makes the next task smaller, not larger.

## 1. What the brief said the limit buys

The brief says: "THE LIMIT IS WHAT BUYS THE ROOM. At a limit every `β ∈ α`
has a successor in `α`, so two steps below `α` is reachable where at an
arbitrary `α` it is not. That is why the source states it at a limit and why
the arbitrary spelling failed" (`agents/tasks/LJ-1-519/LJ-1.519.md:41`).

The first sentence is true. I measured it. The last sentence is not what the
source says.

## 2. What the source says

`dev/literature/devlin-II5.md:221` names the target: "live inside L_α; that
is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for". The digest is correct.

The primary text proves 2.6(ii) in three sentences. Verbatim from the OCR,
`_build/literature/dev2.txt:676-678`:

> (ii) Here we quickly reduce to proving that for any limit ordinal α > ω, if δ < α
> then {Ly\γ ^δ)e L α . In fact it is not hard to see that if δ > ω, then
> (Ly\y ^ δ)e L δ + 4 , so we are done. (We leave all the details to the reader.)

Read the second sentence. The bound is `L_{δ+4}`, and it names **no `α`** and
**no limit**. The limit is used only in the third step, to put `δ+4` inside
`α`. So Devlin's proof has two parts:

- **PART A.** `δ + 4 ∈ α`, therefore `L_{δ+4} ⊆ L_α`. This is the limit's
  whole contribution. It is ordinal arithmetic on successor closure.
- **PART B.** `(L_γ | γ ≤ δ) ∈ L_{δ+4}` for `δ > ω`. This is the content.

**Devlin does not prove Part B.** "We leave all the details to the reader"
(`_build/literature/dev2.txt:678`).

## 3. The brief priced Part A and ordered Part B

`[LJ-1.517]` measured that the witness wants room two membership steps below
the stage (`agents/tasks/LJ-1-517/Probe517.agda:204`). That measurement is
correct and I did not contradict it. It is a NECESSARY condition on any
witness. The brief then treats it as the binding constraint. It is not.
Supplying room is Part A. Putting a set into a stage is Part B, and no amount
of room does that.

The distance is exact and it is in the probe as two types
(`agents/tasks/LJ-1-519/Probe519.agda:208` and `:218`):

- `stage-below` MOVES a set from a lower stage into `Lset α`.
- `StageHigh` PUTS the sequence into a stage.

The limit pays the first in full. It pays nothing of the second.

## 4. Part B is what nine dispatches have been failing at, under a new name

Part B needs `hierL (sucV γ) ∈ Lset (step 4 γ)`. The tree's only route into a
stage is `Lset-in` (`src/L/Constructible.lagda.md:319`), which demands
membership in `𝒟ₒ (Lset δ)`, and `𝒟ₒ-intro` (`src/L/Constructible.lagda.md:301`)
demands a `Formula` over the stage whose `defSet` is the sequence. That is
stage-level definability of the tower. It is `GraphSatAtStage`, which this
brief forbids at `agents/tasks/LJ-1-519/LJ-1.519.md:100`, and which
`[LJ-1.494]` returned a critic-upheld NO-GO on
(`agents/tasks/LJ-1-498/LJ-1.498.md:52`).

So the limit spelling does not escape the wall the arbitrary spelling hit. It
relocates the wall from `Lset α` to `Lset (step 4 γ)` and removes `α` from it.

## 5. This is not a null result

Removing `α` is worth having, and it is delivered as a checked term. The
probe builds Devlin's own reduction, total in `γ`
(`agents/tasks/LJ-1-519/Probe519.agda:235`):

    reduction : StageHigh → StageLow → HierInStageLimit

Every line of the reduction is Part A. The next brief can target `StageHigh`
alone. It carries no `α`, no limit hypothesis and no `ω ∈ α`. It is a
statement about one stage and the four stages above it.

## 6. Why I did not inhabit the brief's exact spelling

The brief's type takes `γ ∈ α` and no `IsOrd γ`, so ordinal hood must be
derived by `mem-ord`. That derivation exhausts the heap at this site. It is a
WALL event and it is reported in full in section "THE WALL" of
`agents/tasks/LJ-1-519/lj-1.519-report.md`. The obligation type in the probe
therefore takes `IsOrd γ` as an argument. That is a WEAKER statement to
assume and the report says so plainly.

## 7. What the mathematician should rule on

1. Whether `StageHigh` is orderable given that `[LJ-1.494]` is a NO-GO on the
   machinery it needs. If it is not, then Devlin 2.6(ii) is not transcribable
   at this tower, which the brief itself calls a ruling-grade finding
   (`agents/tasks/LJ-1-519/LJ-1.519.md:142-143`).
2. Whether a source that defers its own proof to the reader counts as "the
   statement with a source" for the purpose that ordered this task. The
   STATEMENT has a source. The ROUTE does not.
