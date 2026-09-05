# LJ-1.455 review 1: adversarial review of LJ-1.455#1

## HEAD
verdict: upheld
head_slot: mathematician_adversarial
machine: shared

The return under attack is the coder's STOP: `lj-1.455-report.md`
with the obstruction file `review-of-order-as-set.md`. I attacked it
on the three questions and on my four standing questions. The verdict
line survives. The enumeration does not, and one load-bearing claim in
the body is false on the tree today. Both defects are recorded below.
Neither defect inhabits the obligation, so the NO-GO stands and this
review closes the task.

## WHAT WAS READ

`agents/tasks/LJ-1-455/LJ-1.455.md`, `lj-1.455-report.md`,
`review-of-order-as-set.md`, `Probe455.agda`, all four files under
`runs/`, `accept-1.out`, and the instance rows in the transitions
ledger. The ledger in THIS worktree stops at seq 158, task `LJ-1.399`,
dated 2026-08-19 (`dev/pod/transitions/2026-08.jsonl`, last line). The
LJ-1.455 instance rows live in the main tree's copy: seq 1173 READY to
RUNNING, model `grok-4.6`, effort `high`, `heads_sha256` `2f6630d2`;
seq 1185 RETURNED. The six facts of the accept: exit code 0,
obligations delta 0 with 1 open, heap wall false, 1.8 s, error class
None, 7 changed files (`agents/tasks/LJ-1-455/runs/accept-1.out`,
lines `# conjunct 1 held` through `# exit 0`). One more recorded fact:
the retrieval event at seq 1188 offered 10 files and MISSED
`src/L/Choice/Internal.lagda.md`, the chapter the task is about. The
coder read it anyway; the citations below resolve.

## Q1. DOES THE VERDICT LINE MATCH ITS OWN BODY?

Yes. The line says: STOP, because Internal delivers `≺At` at eight
`Fin n` indices and not one free variable with seven slots fixed at
`a`. The body argues exactly that, and every step of the argument
resolves today:

- `≺At : ∀ {n} → Fin n → Fin n → ... → Formula S n`, eight `Fin n`
  arguments: `src/L/Choice/Internal.lagda.md:741-742`.
- A `Term` is `con` or `var` only, so a set can enter a formula only
  as a constant in a `con` position: `src/FOL/Syntax.lagda.md:43-44`.
- The live specialisation the brief named, `inclFo D = ∃̇∈ (con D)
  (prAtL (suc zero) zero zero)`: `src/L/InjChain.lagda.md:445-446`.
- Separation takes `(a : S) (φ : Formula S 1)`:
  `src/L/Axioms/Full.lagda.md:144`.
- Direct application at `n = 1` forces all eight indices to `zero`,
  and `a` does not appear: `Probe455.agda:50-51` typechecks as
  `Formula S 1`.

The measurement is sound. The probe states the type
(`Probe455.agda:45-46`), omits the obligation, and typechecks. Three
forced rechecks after removal of the `.agdai`: 1.50 s, 1.54 s,
1.56 s, exit 0 every time, peak RSS 440729600 bytes
(`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`; `runs/w3-1.out`
records the first check at 1.63 s). Median 1.54 s, as the report
says. The grep counts reproduce: `≺At` in `src/` outside its own
chapter appears in `Adequate` only, at `src/L/Choice/Adequate.lagda.md:56`
(import) and `:745` (use at raised arity), plus index prose at
`src/Everything.lagda.md:757` and `:1003`; `orderFo` and
`order-as-set` have 0 hits in `src/`.

The two cheat routes were correctly refused. A body that ignores `a`
would have typechecked (`≺At-at-one` proves it), and the separation
makes the conclusion trivial for any `orderFo` at all
(`src/L/InjChain.lagda.md:468-490` is that one-separation shape). The
coder stopped instead of weakening. The line matches the body, and the
body is correct on its own numbers.

## Q2. IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY?

All but one. Verified today: `src/L/Choice/Internal.lagda.md:741-742`
(eight indices), `:5-10` (chapter opening, the carve sentence at
`:8-9`), `:22` ("runs **no recursion of its own**"),
`src/FOL/Syntax.lagda.md:43-44`, `src/L/InjChain.lagda.md:445-446`
and `:468-490`, `src/L/Axioms/Full.lagda.md:144`,
`src/L/Choice/Before.lagda.md:1302-1303` (`appAtC`),
`src/L/Choice/Adequate.lagda.md:56` and `:745`,
`src/Landmarks.lagda.md:76` (`L⊨ZFC`), the predecessor
`agents/tasks/LJ-1-454/lj-1.454-report.md:73`, `:155-165`, `:178-182`,
`agents/tasks/LJ-1-416/Probe416.agda:67-75` (`swo-rank`), and every
probe line the report names.

The one FALSE claim is load-bearing for the enumeration:

> "The one live specialisation of a Fin-slot to a constant is
> `appAtC` at `src/L/Choice/Before.lagda.md:1302-1303`."

False. `src/L/Choice/Order.lagda.md:184` pins a Fin-slot of the
internalized step to the closed constant `codeOrder` by an object
equation, `(var zero ≐ con codeOrder)`, and `:186` pins a second one,
`(var zero ≐ con (AllCodes ∅ʟ))`, with the body of `StepAt` at the
seven slots at `:187`. `Order.lagda.md:64` imports `codeOrder`. The
chapter's own recap says the two constants are pinned "because a slot
holds a variable and those two are particular sets"
(`src/L/Choice/Order.lagda.md:716-718`). That IS a live
specialisation of Fin-slots to constants, and it is the exact move the
brief prescribed.

## Q3. IS THE PREDECESSOR'S ENUMERATION COMPLETE?

No, and the incompleteness matters for the next brief, though not for
this verdict.

The sweep listed `Cond₀` at `src/L/Choice/Limit.lagda.md:600` as a
`Formula S 1` inhabitant and discarded it with "None is `≺At`". Three
lines below that entry, the tree already contains the deliverable this
task was named for:

- `codeOrder = hasSeparationL (pairsBound .fst) Cond₀ .fst .fst` at
  `src/L/Choice/Limit.lagda.md:608`.
- `codeOrder-mem = hasSeparationL (pairsBound .fst) Cond₀ .fst .snd`
  at `:612`, which is the conclusion of `order-as-set` verbatim in
  shape: membership in the carved set equals bound membership
  conjoined with satisfaction of the `Formula S 1`.
- `codeOrder-fill` and `codeOrder-rep`, the two representation
  lemmas, stated in the shape `Adequacy.Keys` consumes.
- `L.Choice.Before` makes them unconditional:
  `open Described BeforeAt BeforeAt-in BeforeAt-out public` at
  `src/L/Choice/Before.lagda.md:1544`, with the real `BeforeAt`
  defined at `:1331`.

And the order-as-a-set exists at EVERY set, at the site the tree's
architecture chose: `module Bound (a : V ℓ) (p : ⟨ isL a ⟫)` at
`src/L/Choice/Order.lagda.md:679`, which delivers `orderL : S` at
`:693` with both directions, `orderL-fill` at `:696` and `orderL-rep`
at `:700`. That is the order on the tower over `a`'s bound ordinal, as
an element of the model, for arbitrary `a` in `L`.

So the report's "WHAT THE NEXT BRIEF NEEDS" section prices as NEW what
the tree already holds. It proposes `orderFo : (R P B C C₀ : S) →
Formula S 1` with "a new price". But `R` is already a closed term,
`codeOrder`, and the equation-pinning that feeds a closed set into a
Fin-slot is already written and already measured, at
`src/L/Choice/Order.lagda.md:184` and `:186`. The sweep's list also
mislabels its own entries: `Faithful.lagda.md:855` is
`Cond₀ : S → S → Formula S 1`, `Transversal.lagda.md:116` is
`Pick : S → S → Formula S 1`, `Before.lagda.md:220` is
`RelCond : (R A A' : S) → Formula S 1`, and `Table.lagda.md:349` is a
module parameter. These are families and parameters, not inhabitants.
The sweep was grep-shaped, not read-shaped, and that is how it saw
`Limit.lagda.md:600` and still missed `codeOrder` at `:608`.

**Did the brief cause the outcome?** In part, yes. The brief's
premise "The two have never been put in one file" is false:
`L.Choice.Limit` puts the formula and the carve in one file and landed
`codeOrder`, and `L.Choice.Order` composes `StepAt` with
`con codeOrder`. The brief's prescription "every slot but one fixed at
`a`" asks for a move the tree has rejected by design: the relation
reaches the description as a slot and "what fills the slot is the
caller's business" (`src/L/Choice/Internal.lagda.md:697-700`). The
live sites bind six sets and pin two constants
(`src/L/Choice/Order.lagda.md:176-187`); none of them fixes slots
"at `a`". The obligation also demands the carve of an ARBITRARY
`w : SWO ⟪ fst a ⟫`, while the tree carves only ITS OWN canonical
order at stages, and an arbitrary `w` enters elsewhere only as a
caller-supplied represented set with two lemmas, the `Ps`, `Prep`,
`Pfill` pattern at `src/L/Choice/Adequate.lagda.md:713-717`. The
brief foreclosed the GO it asked for.

**Why the defects do not overturn.** The missed items do not inhabit
`orderFo : (a : S) → Formula S 1` at the brief's meaning. `codeOrder`
is the limit-stage order, not a function of arbitrary `a`. `orderL`
orders the tower over `a`'s bound, not `fst a` under `w`. `Stp` keeps
six slots as bound variables, because the table value at a stage is a
recursion value and "a recursion whose values are sets cannot be
named by a term" (`src/L/Choice/Limit.lagda.md:20-21`). The
obligation as typed has no honest inhabitant, the coder measured that
at the right site, and an upheld NO-GO closes the task.

## THE CURE THE RETURN MISSED, FOR THE QUEUE

Not a cure for this obligation. A correction for the next brief, and
it is the difference between pricing new parameters and consuming
delivered ones:

1. The order-as-a-set EXISTS: `codeOrder`
   (`src/L/Choice/Limit.lagda.md:608`, unconditional via
   `src/L/Choice/Before.lagda.md:1544`) and `orderL` at every set's
   stage (`src/L/Choice/Order.lagda.md:693`).
2. The slot-to-constant move EXISTS and is measured: the object
   equation against `con codeOrder`
   (`src/L/Choice/Order.lagda.md:184`), not only `appAtC`.
3. The LJ-1.454 corrected target, "a formula with slots for the order
   as a set, then carve" (`agents/tasks/LJ-1-454/lj-1.454-report.md:178-182`),
   already has its order parameter delivered. A rank brief should
   consume `Order.Bound` and `codeOrder` and spend its price on the
   rank recursion's first-order description, not on re-deriving the
   order. Devlin's requirement is the same shape: "a definable
   well-order of L_α" (`dev/literature/devlin-II5.md:259`), a STAGE
   order, not an arbitrary set's arbitrary well-order.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: declined, not read. Line 1 reads
  "ARCHIVED 2026-08-20". The journal is retired; the live record for
  this review is the task directories and `src/`.
- `archive/dev/ORCHESTRATION.md`: declined, not used. Orchestration
  history does not bear on a slot-count obstruction at `≺At`.
- `archive/dev/DD-archived.md`: declined, not used. The archived DD
  series does not bear on the questions asked here.
- `archive/dev/PLAN-archived.md`: declined, not used. The retired plan
  does not bear on what `src/` delivers today.
- `dev/ARCHIVE.md`: read and used as a check that no `L.Choice`
  chapter was retired. `dev/ARCHIVE.md:168`:
  "in, `src/L/Choice/Stage.lagda.md`, stays live, so the fragment has
  no archived". Limit, Order and Before are live chapters; nothing in
  the archive carries a carve of an order as a set.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read and used.
  `dev/literature/devlin-II5.md:259`:
  "Requirement: a definable well-order of L_α, used to pick the <_L-least".
  Used in THE CURE above: the literature's order is of a stage, which
  matches the tree's `codeOrder` and `orderL` sites and not the
  obligation's arbitrary `a`.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not used. A
  bibliography index; no entry bears on a slot reduction inside this
  tree.
- `dev/literature/digest.md`: declined, not used. The digest was
  already spent by the predecessor for the recursion shape; this
  review's evidence is in the tree.
- `dev/literature/geology.md`: declined, not used. Geology sources do
  not bear on the internalized order formula.
- `dev/literature/devlin-errata.md`: declined, not used. A
  do-not-repeat checklist of Devlin error classes; no error class
  here bears on the three questions.
