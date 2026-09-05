# LJ-1.468 report: the order formula restated, the way its own chapter restates one

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-468/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `orderFo` in
`agents/tasks/LJ-1-468/Probe468.agda`. Land nothing in `src/`.

## PREDECESSOR, READ BEFORE ANY AGDA

`[LJ-1.455]` is a critic-upheld STOP
(`agents/tasks/LJ-1-455/lj-1.455-report.md:46-50`):

> **STOP.** W3 typechecks the type `(a : S) → Formula S 1`. Internal
> delivers `≺At` at eight `Fin n` indices, not at one free variable
> with seven slots fixed at `a`. I omitted `orderFo` as an inhabitant
> and I omitted `order-as-set`. The obstruction is
> `review-of-order-as-set.md`.

The five constants it names are present at
`agents/tasks/LJ-1-455/lj-1.455-report.md:271-275`:

> ```
> orderFo :
>     (R P B C C₀ : S)
>   → Formula S 1
> ```

Verdict is a stated STOP. The five constants are present. I did not
stop on that ground.

The critic who upheld that STOP
(`agents/tasks/LJ-1-455/review-of-LJ-1-455-1.md:4`) recorded that
`Cond₀` and `orderL` already exist as other packagings
(`:132-136`). Those are not this type. This task inhabits the type
the predecessor named.

## D-10, BEFORE ANY AGDA

Quoted from `[LJ-1.455]`, `agents/tasks/LJ-1-455/lj-1.455-report.md:59-65`:

> ```
> ≺At : ∀ {n} → Fin n → Fin n
>     → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
> ≺At R P s₁ a₁ e₁ s₂ a₂ e₂ = ...
> ```

Quoted from `src/L/Choice/Internal.lagda.md:741-747`:

```
≺At : ∀ {n} → Fin n → Fin n
    → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
≺At R P s₁ a₁ e₁ s₂ a₂ e₂ =
      appAt R s₁ s₂
  ∨̇ ( (var s₂ ≐ var s₁)
    ∧̇ ( (var a₁ ∈̇ var a₂)
      ∨̇ ( (var a₂ ≐ var a₁) ∧̇ LexAt P a₁ e₁ e₂ ) ) )
```

The eight are `R`, `P`, `s₁`, `a₁`, `e₁`, `s₂`, `a₂`, `e₂`.

Quoted from `[LJ-1.455]` D-10, `agents/tasks/LJ-1-455/lj-1.455-report.md:117-123`,
and from `src/L/Choice/Before.lagda.md:1302-1303`:

```
appAtC : ∀ {n} → S → Fin n → Fin n → Formula S n
appAtC F x y = ∃̇∈ (con F) (prAtL zero (suc x) (suc y))
```

That restates `appAt` so the relation is a constant. The live
`Formula S 1` of the same shape is `RelCond` at
`src/L/Choice/Before.lagda.md:220-226`: pins by `var zero ≐ con R`,
binds two members from `con A'`, reconstructs the pair by `prAtL`,
and applies the slot formula as it was delivered. The comment at
`:217-219` says the step description stands at slots exactly as it
was delivered.

### Eight-row table (W3 reading; no Agda)

| index | slot | what it names | home |
|---|---|---|---|
| 1 | `R` | the code-order, a set of pairs of codes (`src/L/Choice/Internal.lagda.md:696-700`, `:868`) | becomes `con` (pinned, `RelCond` shape) |
| 2 | `P` | the parameter-order (`:731`, `:868-872`) | becomes `con` |
| 3 | `s₁` | first name: skeleton (`:741-747`) | stays a bound variable (`StepAt`'s `∃₆` at `:920-975`) |
| 4 | `a₁` | first name: arity | stays a bound variable |
| 5 | `e₁` | first name: environment | stays a bound variable |
| 6 | `s₂` | second name: skeleton | stays a bound variable |
| 7 | `a₂` | second name: arity | stays a bound variable |
| 8 | `e₂` | second name: environment | stays a bound variable |

No slot has no home. I did not stop.

`B`, `C`, `C₀` are not among the eight. They are slots of `StepAt`
(`src/L/Choice/Internal.lagda.md:973-975`) and of `LeastNameAt`
(`:910-917`). They become `con` as well. The two remaining `StepAt`
slots `x` and `y` are bound from `con B` by two `∃̇∈`, and the one
free variable is their pair, by `prAtL`. That is the `RelCond` /
`appAtC` shape. Naked `≺At` does not read `B`, `C`, `C₀`. The five
constants are the right five for the member-order Internal carves
with, which is `StepAt` wrapping `≺At`. They would be the wrong
five for a pair of names with no carrier.

I did not touch `w`. Internal does not read an arbitrary well-order
(`agents/tasks/LJ-1-455/lj-1.455-report.md:262-266`).

I did not drop a conjunct of `StepAt`. The body applies `StepAt` as
Internal delivered it (`Probe468.agda:87`).

## VERDICT

**GO.** W3 typechecks the type `(R P B C C₀ : S) → Formula S 1`.
The eight slots of `≺At` all have a home. The five constants are
the right five for `StepAt`. `orderFo` inhabits that type
(`Probe468.agda:78-87`). Separation has a `Formula S 1` to consume.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

P-l (`dev/LESSONS.md:2357`): the type is over the generic carrier
`S`. It does not name a transparent stage presentation.

D-26 (`dev/LESSONS.md:1735`): this task does not well-order a
tower stage. Internal's order formula runs no recursion of its own
(`src/L/Choice/Internal.lagda.md:22`). Not a D-26 site.

## 1. W3: the type, first

**The type forms at five constants and one free variable.**

Stated as `orderFo-type : Type _` equal to
`(R P B C C₀ : S) → Formula S 1` (`Probe468.agda:53-54`). The
eight-row table is a reading. I typechecked nothing for the table.
The type-only file omitted the body of `orderFo`. The type formed.
The count is not wrong.

ESTIMATE for W3 was the table plus three lines, under 10 seconds.
MEASURED: the type is 2 lines. The type-only file typechecked.
Comparables of shape, not of size. Nothing is funded against the
estimate.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 0.92 | 271810560 | `runs/w3-2.out` |
| w3-3 | 0.89 | 271810560 | `runs/w3-3.out` |
| w3-4 | 0.99 | 260833280 | `runs/w3-4.out` |

Median wall **0.92 s**. Peak RSS **271810560** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.18 s and
271794176 bytes, also exit 0; it is not one of the three forced
rechecks.

## 2. The inhabitant `orderFo`

`orderFo` is `Probe468.agda:78-87`. It is the `RelCond` wrapping of
`StepAt`:

- five pins `var zero ≐ con R`, then `P`, `B`, `C`, `C₀`
- two members bound from `∃̇∈ (con B)`
- the free variable is their pair, by `prAtL`
- `StepAt` at those slots, as delivered
  (`src/L/Choice/Internal.lagda.md:973-975`)

That is how `appAtC` restates `appAt`
(`src/L/Choice/Before.lagda.md:1302-1303`): a set enters as `con`
in Term position. `RelCond` (`:220-226`) is the `Formula S 1`
instance of that move. I instantiated `StepAt`. I did not rewrite
`≺At`. I did not import a probe. I did not postulate. I did not
carve.

Naked `≺At` with `R` and `P` as `con` would still have six name
slots. That is not `Formula S 1`. The six become bound variables
inside `StepAt`'s `∃₆`. That is why the five constants include
`B`, `C`, `C₀`.

ESTIMATE for the Agda was about 110 lines, of which the obligation
is about 30. MEASURED: 36 non-blank non-comment lines in the full
probe, of which `orderFo` is 10 lines (`Probe468.agda:78-87`).
Comparables of shape, not of size. Nothing is funded against the
estimate.

Three forced rechecks of the full file, same caliber, one Agda
process at a time, interface removed:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| full-2 | 1.75 | 423051264 | `runs/full-2.out` |
| full-3 | 1.76 | 423034880 | `runs/full-3.out` |
| full-4 | 1.77 | 423084032 | `runs/full-4.out` |

Median wall **1.76 s**. Peak RSS **423084032** bytes. Exit 0 every
time. No heap event. The first check `runs/full-1.out` was 2.07 s
and 385941504 bytes, also exit 0; it is not one of the three forced
rechecks.

## 3. W2

The terms are generic in the carrier `S`. They name no stage, no
cardinal, no numeral, and no `Lset`. The restatement instantiates
`StepAt` as Internal delivered it, at slots, with the five
background sets pinned to constants. I did not rewrite `≺At` at a
fixed form. W2 holds for what was written.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. C-42 sweep

`[LJ-1.455]` measured ONE site: whether `≺At`'s eight `Fin n` slots
reduce to `Formula S 1` from a set `a` alone. That reduction stays
FALSE. This task is not that cure. This task is the restatement
that report named (`agents/tasks/LJ-1-455/lj-1.455-report.md:255-282`).

Sweep of THIS shape, `(R P B C C₀ : S) → Formula S 1` wrapping
`StepAt` / `≺At`:

- `src/`: 0 hits for `orderFo`.
- `src/L/Choice/` inhabitants of `Formula S 1`: `RelCond` at
  `Before.lagda.md:220`, `Cond₀` at `Faithful.lagda.md:855`,
  `Pick` at `Transversal.lagda.md:116`, `Cond₀` at
  `Limit.lagda.md:600`. `Table.lagda.md:349` is a module
  parameter of that same type family. None takes five Internal
  background constants. Count of this exact type in `src/`: **0**.
- `Stp` at `src/L/Choice/Order.lagda.md:176-188` restates `StepAt`
  at four `Fin n` indices and pins two closed terms. It is not
  `Formula S 1`.
- `orderL` at `src/L/Choice/Order.lagda.md:693` is the order as a
  set at a bound ordinal. It is not this formula.

The `[LJ-1.454]` STOP is a different shape (a missing rank
formula). This sweep does not re-price it.

## WHAT THE CARVE WOULD NOW COST

Do not carve it. Stated as a type, not built:

```
order-as-set :
    (R P B C C₀ bnd : S)
  → ((x y : S) → ⟨ x ∈ˢ B ⟩ → ⟨ y ∈ˢ B ⟩
               → ⟨ pr (fst x) (fst y) ∈ fst bnd ⟩)
  → Σ[ Ord ∈ S ] ((z : S) → ⟨ z ∈ˢ Ord ⟩
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ orderFo R P B C C₀)))
```

The bound is a set of pairs of members of `B`. The carve names that
bound before it builds the set (`src/L/InjChain.lagda.md:468-472`).
Separation takes `(a : S) (φ : Formula S 1)`
(`src/L/Axioms/Full.lagda.md:144-145`). The formula is now
`orderFo R P B C C₀`. Satisfaction at `(z ∷ [])` says `z` is a pair
of two members of `B` that stand in `StepAt` at the five constants.

The shape is one `hasSeparationL` at that named pair-bound. The
live comparable of SHAPE is the `RelCond` carve at
`src/L/Choice/Before.lagda.md:231-233`. A measured cure does not
transfer by analogy. Re-measure the carve at its own site. Nothing
is funded against `RelCond`.

A related object already exists: `orderL` at
`src/L/Choice/Order.lagda.md:693`, the order as an element of the
model at a bound ordinal of an arbitrary `a`. `Cond₀` at
`src/L/Choice/Faithful.lagda.md:855-857` is a `Formula S 1` given
a stage and a table. The next brief must name which consumer it
wants. This task delivered the five-constant formula. It did not
choose the consumer.

## WHAT THE NEXT BRIEF NEEDS

- `orderFo : (R P B C C₀ : S) → Formula S 1` typechecks
  (`Probe468.agda:78-87`). Separation has something to consume.
- Do not send the seven-slot reduction
  `orderFo : (a : S) → Formula S 1` again. That reduction is still
  FALSE. Quote D-10 above.
- Do not mix in `w : SWO ⟪ fst a ⟫`. This formula does not read it.
- The next obligation, if the target is a carve of this formula, is
  `order-as-set` as typed above. Name the pair-bound. Re-measure.
- Say whether the consumer is this five-constant carve, or
  `orderL` already at `src/L/Choice/Order.lagda.md:693`, or
  `Cond₀` at `src/L/Choice/Faithful.lagda.md:855`. Those three are
  not the same type.
- Do not attempt the rank. `[LJ-1.454]` still holds
  (`agents/tasks/LJ-1-454/lj-1.454-report.md:73`).

What the statement cost: 36 non-blank non-comment lines, W3 median
0.92 s, full-file median 1.76 s, peak RSS 423084032 bytes. What
the shape resisted: naked `≺At` at two constants is not
`Formula S 1`; the six name slots need `StepAt`'s binders, and
those binders need `B`, `C`, `C₀`. What I had to weaken: nothing.
What I could not close: the carve, which this brief forbade, and
the rank, which `[LJ-1.454]` still holds.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`
  "THE `LJ` DISPATCH INDEX, archived 2026-08-18"
  Declined. Not used. It is a dispatch index. It does not bear on
  whether the five constants restate `≺At` as `Formula S 1`.
- `archive/dev/JOURNAL-archived.md:1400`
  "the order formula's CONTENT is"
  Read. Used. That archived T19 recorded that materializing the
  order as an element was a wall at a different site, the
  concrete tower presentation. This GO is not that wall. It is a
  slot restatement of `StepAt` at the generic carrier. C-42: a
  refutation at T19 does not measure this site.
- `archive/dev/JOURNAL.md:3`
  "The per-episode journal is retired."
  Declined. Not used. The per-episode journal is retired. The
  history of this campaign is the task directories.
- `dev/ARCHIVE.md:283`
  "A classical well-order over finite labelled trees by shortlex"
  Read. Used. The retired `L.WellOrder.Tree` is a well-order, not
  a `Formula S 1` restatement of `≺At` or `StepAt`. No retired
  module pins five Internal background sets to `con`. This task
  does not retire a module.
- `archive/dev/DD-archived.md:1`
  "THE `DD` RULING SERIES, archived in full 2026-08-18"
  Declined. Not used. The archived D series does not bear on the
  five-constant restatement of `StepAt`.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin's well-order is of `L_α`. The
  five constants this formula carries (`R`, `P`, `B`, `C`, `C₀`)
  are the naming data of a stage, not an arbitrary set `a`.
- `dev/literature/truncation-and-selection.md:67`
  "The selection device is a definable well-order plus a universal guard."
  Read. Used. This task does not select. It restates the definable
  well-order, already a formula at seven `StepAt` slots, as
  `Formula S 1` with five constants in Term position.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. Internal describes
  that order without running a recursion of its own
  (`src/L/Choice/Internal.lagda.md:22`). This restatement keeps
  that description and moves five sets into Term position.
- `dev/literature/terms-2026-08.md:230`
  "The ordinal a well-order collapses to: "the order type of the"
  Read. Used. That is the sense of rank as data. This task does
  not write a rank formula. `[LJ-1.454]` still holds.
- `dev/literature/glossary-review-2026-08.md:1`
  "Glossary review: the 119 pre-protocol entries"
  Declined. Not used. It reviews glossary entries. It does not
  bear on a slot restatement of `StepAt`.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, from the repository
root. I did not set `GHCRTS`. No heap event. No other Agda
compiler was live when the first run started.

- W3 first check, `runs/w3-1.out`: 1.18 s real, 271794176 bytes
  RSS, printed `Checking LJ-1-468.Probe468`, exit 0.
- Three forced rechecks after `rm` of
  `_build/2.8.0/agda/agents/tasks/LJ-1-468/Probe468.agdai`:
  0.92 s, 0.89 s, 0.99 s. Median **0.92 s**. Peak RSS
  **271810560** bytes. Exit 0 every time
  (`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`).
- Full-file first check, `runs/full-1.out`: 2.07 s real,
  385941504 bytes RSS, printed `Checking LJ-1-468.Probe468`,
  exit 0.
- Three forced rechecks after `rm` of the same interface:
  1.75 s, 1.76 s, 1.77 s. Median **1.76 s**. Peak RSS
  **423084032** bytes. Exit 0 every time
  (`runs/full-2.out`, `runs/full-3.out`, `runs/full-4.out`).

Estimate for the Agda was about 110 lines for the whole
obligation. MEASURED 36 non-blank non-comment lines. Nothing is
funded against the estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-468/`:

- `lj-1.468-report.md`, this report
- `Probe468.agda`, W3 type then `orderFo`
- `runs/`, the Agda transcripts named above
