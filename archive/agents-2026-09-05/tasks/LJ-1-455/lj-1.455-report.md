# LJ-1.455 report: the order this tree describes, carved into a set

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-455/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `order-as-set` in
`agents/tasks/LJ-1-455/Probe455.agda`. Land nothing in `src/`.

## PREDECESSOR, READ BEFORE ANY AGDA

`[LJ-1.454]` is a critic-upheld STOP
(`agents/tasks/LJ-1-454/lj-1.454-report.md:73`):

> **STOP.** W3 typechecks the type `Formula S 2`. Internal delivers the
> ORDER and does not deliver the RANK. I omitted `rank-graph`. The
> obstruction is `review-of-rank-graph.md`.

Its inventory, quoted from `:155-165`:

> - `≺At : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n`
>   at `src/L/Choice/Internal.lagda.md:741-742`. Eight slot indices.
>   Not `Formula S 2`.
> - `LexAt` at `:731`, four indices.
> - `LeastNameAt` at `:910-911`, nine indices.
> - `StepAt` at `:973-975`, seven indices.
>
> Separation in this tree takes a `Formula`. `hasSeparationL` is
> `(a : S) (φ : Formula S 1)` at `src/L/Axioms/Full.lagda.md:144`.
> The carve in `src/L/InjChain.lagda.md:468-472` takes
> `(φ : Formula S 1)` over a named bound. There is no `φ` here for
> the rank.

Corrected target at `:178-182`: inhabit the formula first, then carve.
This task is the first half, and only the first half. I did not
attempt the rank.

The predecessor names the statement as a missing RANK formula. It
does not name `order-as-set` FALSE. I did not stop on that ground.
The stop below is a new measurement: the ORDER formula Internal
does deliver cannot be brought to `Formula S 1` from `a` alone.

## VERDICT

**STOP.** W3 typechecks the type `(a : S) → Formula S 1`. Internal
delivers `≺At` at eight `Fin n` indices, not at one free variable
with seven slots fixed at `a`. I omitted `orderFo` as an inhabitant
and I omitted `order-as-set`. The obstruction is
`review-of-order-as-set.md`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`≺At` takes eight slot indices
(`src/L/Choice/Internal.lagda.md:741-742`):

```
≺At : ∀ {n} → Fin n → Fin n
    → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
≺At R P s₁ a₁ e₁ s₂ a₂ e₂ = ...
```

The eight are `R`, `P`, `s₁`, `a₁`, `e₁`, `s₂`, `a₂`, `e₂`. Each is
`Fin n`, a de Bruijn index into an environment of length `n`
(`src/FOL/Syntax.lagda.md:43-44`: a term is `con` or `var`).
Separation takes `Formula S 1` (`src/L/Axioms/Full.lagda.md:144`).

**How `inclFo` fixes its extra slot.** At
`src/L/InjChain.lagda.md:445-446`:

```
inclFo : S → Formula S 1
inclFo D = ∃̇∈ (con D) (prAtL (suc zero) zero zero)
```

`D` enters as a `Term`, via `con D`. The binder holds the member.
The free variable is the pair. That is a specialisation: one set
parameter becomes a constant in a Term position.

**`≺At` has no Term position.** Its eight arguments are `Fin n`.
You cannot pass `con a` to `≺At`. The shape `inclFo` uses does not
apply. The reduction is not a specialisation.

**The only `Formula S 1` `≺At` forms without a restatement** is the
collapse at `n = 1`: `Fin 1` has one inhabitant `zero`, so every
slot is the same variable. The argument `a` does not appear. That
is not "seven slots fixed at `a`".

**A restatement that writes `con a` in seven places is also not
the order of `a`.** The eight slots are not "the set `a`". They
are:

| slot | what it holds | source |
|---|---|---|
| `R` | the code-order, a set of pairs of codes | `src/L/Choice/Internal.lagda.md:696-700`, `:868` |
| `P` | the parameter-order | `:731`, `:868-872` |
| `s₁ a₁ e₁` | first name: skeleton, arity, environment | `:741-747` |
| `s₂ a₂ e₂` | second name: the same three | `:741-747` |

None of those is the set whose members the carve would take pairs
of. The free variable of the carve is a pair `z`
(`(z ∷ []) ⊨ orderFo a`). `≺At` has no pair-slot.

**`StepAt` is closer and still not enough.** It compares two
members (`src/L/Choice/Internal.lagda.md:973-975`), seven `Fin n`
indices: `R P B C C₀ x y`. From `a` alone you can bound `x` and
`y` by `∃̇∈ (con a)`, in the `inclFo` shape. The other five are
the code-order, the parameter-order, the carrier, the code set,
and the free-code set. They are not members of an arbitrary `a`.
They are not `a` itself.

**The one live specialisation of a Fin-slot to a constant** is
`appAtC` at `src/L/Choice/Before.lagda.md:1302-1303`:

```
appAtC : ∀ {n} → S → Fin n → Fin n → Formula S n
appAtC F x y = ∃̇∈ (con F) (prAtL zero (suc x) (suc y))
```

That restates `appAt` so the relation is a constant. It still
returns `Formula S n` with two Fin indices. It does not bring
eight slots to one.

**Seven slots cannot be fixed from `a` alone.** What the formula
still needs, named:

1. `R`, the code-order (a set of pairs of codes).
2. `P`, the parameter-order.
3. If the compared objects are names: two names' skeletons,
   arities, and environments (`s₁ a₁ e₁ s₂ a₂ e₂`).
4. If the compared objects are members (`StepAt`): the carrier
   `B`, the code set `C`, and the free-code set `C₀`, in addition
   to `R` and `P`.
5. A pairing atom that says the free variable `z` is the pair of
   the two compared objects. `≺At` does not mention that pair.
6. The `SWO ⟪ fst a ⟫` in the obligation telescope is not a slot
   of `≺At` and is not a slot of `StepAt`. Internal does not read
   an arbitrary well-order.

The residue "fix seven slots at `a` and separate once" is FALSE at
this site. The corrected target, beside the original, is: name the
background sets `R P B C C₀` (or the two names' data) as
parameters the formula is allowed to take, then specialise. I did
not invent those parameters. I did not inhabit `orderFo`. I did
not weaken the type.

## 1. W3: `orderFo`, first

**The type is well-formed. Internal does not inhabit it as the
specialisation the brief names.**

Stated as `orderFo-type : Type _` equal to `(a : S) → Formula S 1`
(`Probe455.agda:45-46`). I did not inhabit
`orderFo : (a : S) → Formula S 1`. I did not postulate it. I did
not invent a body that ignores `a`.

What the checker did load, as measurements of the slot reduction:

- `≺At-at-one : Formula S 1` (`Probe455.agda:50-51`). The collapse
  at `n = 1`. All eight indices are `zero`. `a` is unused.
- `StepAt-at-one : Formula S 1` (`Probe455.agda:55-56`). The same
  collapse at seven indices.
- `inclFo-shape : S → Formula S 1` (`Probe455.agda:61-62`). The
  live specialisation copied from `src/L/InjChain.lagda.md:445-446`,
  so the checker sees the shape the brief named.
- `pairFo : S → Formula S 1` (`Probe455.agda:67-68`). What `a`
  alone CAN fix: `z` is a pair of two members of `a`. No order.

`order-as-set` is omitted. The name does not appear as a
definition.

**GREP, as the brief asked**, `≺At` under `src/` outside its own
chapter:

| file | line | what it is |
|---|---|---|
| `src/L/Choice/Adequate.lagda.md` | `:56` | import of `≺At` |
| `src/L/Choice/Adequate.lagda.md` | `:745-747` | use at raised arity: `≺At (sh3 R) (sh3 P) (suc (suc zero)) (suc zero) zero (sh3 s) (sh3 a) (sh3 e)` in the environment `e' ∷ a' ∷ s' ∷ γ` |
| `src/Everything.lagda.md` | `:757`, `:1003` | index prose |

Count of code files outside Internal that mention `≺At`: **1**
(`Adequate`). That consumer RAISES the arity by three (`sh3`), it
does not collapse it to one. Count of `≺At` used as
`Formula S 1` in `src/`: **0**. Count of `orderFo` or
`order-as-set` in `src/`: **0**.

The two have never been put in one file as a carve. Adequate
consumes the formula as a comparison of names at slots, which is
what Internal wrote it for.

ESTIMATE for W3 was about 20 lines and under 10 seconds.
MEASURED: 22 non-blank non-comment lines in the probe, of which
`orderFo-type` is 2 lines. The extra lines are the four
measurements. Comparables of shape, not of size.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 1.50 | 440729600 | `runs/w3-2.out` |
| w3-3 | 1.54 | 440713216 | `runs/w3-3.out` |
| w3-4 | 1.56 | 440713216 | `runs/w3-4.out` |

Median wall **1.54 s**. Peak RSS **440729600** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.63 s and
440713216 bytes, also exit 0; it is not one of the three forced
rechecks.

The full file is the W3 file. The obligation is omitted. The same
three runs are the full-file numbers.

## 2. W2

The W3 terms are generic in the carrier `S`. They name no stage,
no cardinal, no numeral, and no `Lset`. The stop is at the generic
carrier. I did not write a fixed form. W2 holds for what was
written.

## 3. W4

No module was retired. Nothing moved to `archive/`.

## 4. C-42 sweep, before any cure

This STOP measures ONE site: whether `≺At`'s eight `Fin n` slots
reduce to `Formula S 1` from a set `a` alone.

Sweep of that shape:

- `src/L/Choice/Internal.lagda.md`: 18 hits for `≺At`. Home of
  the eight-index constructor. Zero hits for `Formula S 1` on
  `≺At`.
- `src/` outside Internal: 2 files mention `≺At` (`Adequate`,
  `Everything`). Code consumers that use it as `Formula S 1`:
  **0**.
- `src/L/Choice/` inhabitants of `Formula S 1`: `Cond₀` in
  `Faithful.lagda.md:855` and `Limit.lagda.md:600`, `Pick` in
  `Transversal.lagda.md:116`, `RelCond` in `Before.lagda.md:220`,
  `Cond₀` in `Table.lagda.md:349`. None is `≺At`. Count: **0**.
- `src/`: 0 hits for `orderFo`. 0 hits for `order-as-set`.

The `[LJ-1.454]` STOP is a different shape (a missing rank
formula). This sweep does not re-price it.

No cure is priced. The next action is the missing parameters, not
the carve.

## WHAT THE NEXT BRIEF NEEDS

- Do not send `order-as-set` again with
  `orderFo : (a : S) → Formula S 1` built by fixing seven of
  `≺At`'s slots at `a`. That reduction is FALSE. Quote D-10
  above. Quote `src/L/Choice/Internal.lagda.md:741-742` against
  `src/L/InjChain.lagda.md:445-446`.
- Distinguish two orders. The obligation telescope has
  `w : SWO ⟪ fst a ⟫`, an arbitrary well-order of an arbitrary
  set. `≺At` is the constructible name-order, and it needs `R`,
  `P`, and two names' data. Internal does not read `w`. Mixing
  them is the brief's defect, not a hole in the probe.
- If the target is Internal's own order, carved as a set of
  pairs of members of a STAGE, the formula still needs the
  background sets. A type the next brief may name, and that I
  did not inhabit:

```
orderFo :
    (R P B C C₀ : S)
  → Formula S 1
```

  or, with the two members bound from a named stage `a` in the
  `inclFo` shape, still those five constants in Term position,
  restated the way `appAtC` restates `appAt`
  (`src/L/Choice/Before.lagda.md:1302-1303`). That is a
  restatement, and it needs a new price.

- Do not attempt the rank. `[LJ-1.454]` still holds.

**Once the order is a set, what a rank formula would quantify
over.** Stated as a type, not built:

```
rankFo : (a : S) (R : S) → Formula S 2
```

Satisfaction at `(z ∷ x ∷ [])` would say `z` is the rank of the
member `x` of `a` along the order-set `R`. A weaker, first-order
description of the INITIAL SEGMENT is:

```
predFo : (a : S) (R : S) → Formula S 2
```

Satisfaction at `(y ∷ x ∷ [])` would say `y ∈ a` and
`pr (fst y) (fst x) ∈ fst R`. That is one membership atom
against the carved order, plus membership in `a`. One more
separation would carve `{ y ∈ a | ⟨y,x⟩ ∈ R }`.

**Does the order-as-a-set make a first-order rank description
possible?** The comparison becomes first-order, as a membership
atom against `R`. The initial segment becomes first-order, as
`predFo`. The ORDINAL rank, `swo-rank` at
`agents/tasks/LJ-1-416/Probe416.agda:67-75`, is Acc recursion.
A `Formula` has no `Acc`. Internal's order formula runs **no
recursion of its own** (`src/L/Choice/Internal.lagda.md:22`).
Having `R` as a set does not write that recursion as a
`Formula`. This task did not deliver `R`, so a rank formula
that quantifies over `R` cannot start.

What the statement cost: 22 non-blank non-comment lines, median
1.54 s, peak RSS 440729600 bytes. What the shape resisted: seven
of `≺At`'s slots cannot be fixed from `a` alone. What I had to
weaken: nothing. What I could not close: `orderFo` as the
specialisation the brief named, and therefore `order-as-set`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`
  "THE `LJ` DISPATCH INDEX, archived 2026-08-18"
  Declined. Not used. It is a dispatch index. It does not bear on
  whether `≺At` reduces to `Formula S 1`.
- `archive/dev/JOURNAL-archived.md:1400`
  "the order formula's CONTENT is"
  Read. Used. That archived T19 recorded that materializing the
  order as an element was a wall at a different site, the
  concrete tower presentation. This STOP is not that wall. It is
  a slot-count obstruction at `≺At`. C-42: a refutation at T19
  does not measure this site.
- `archive/dev/JOURNAL.md:3`
  "The per-episode journal is retired."
  Declined. Not used. The per-episode journal is retired. The
  history of this campaign is the task directories.
- `dev/ARCHIVE.md:283`
  "A classical well-order over finite labelled trees by shortlex"
  Read. Used. The retired `L.WellOrder.Tree` is a well-order, not
  a `Formula S 1` specialisation of `≺At`. No retired module
  turns eight `Fin n` indices into one free variable at a set
  `a`. This task does not retire a module.
- `archive/dev/DD-archived.md:1`
  "THE `DD` RULING SERIES, archived in full 2026-08-18"
  Declined. Not used. The archived D series does not bear on the
  slot reduction of `≺At`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:67`
  "The selection device is a definable well-order plus a universal guard."
  Read. Used. This task does not select. It asks whether the
  definable well-order, already a formula at eight slots,
  specialises to `Formula S 1` from `a`.
- `dev/literature/devlin-II5.md:259`
  "a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin's well-order is of `L_α`, not of
  an arbitrary set `a`. The extra parameters this STOP names
  (`R`, `P`, the code sets) are the `L_α` naming data.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. That is the object
  Internal describes without running a recursion of its own
  (`src/L/Choice/Internal.lagda.md:22`). The digest does not
  specialise that description to one free variable at an
  arbitrary set.
- `dev/literature/terms-2026-08.md:230`
  "The ordinal a well-order collapses to: "the order type of the"
  Read. Used. That is the sense of `swo-rank` as DATA
  (`Probe416.agda:74-75`). Order-as-a-set does not write that
  collapse as a `Formula`.
- `dev/literature/primary-sources.md:1`
  "Primary sources, second round: Jensen manuscript, Devlin, Jech"
  Declined. Not used. It records Jensen and Devlin indexing, not
  a slot reduction of `≺At`.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, from the repository
root. I did not set `GHCRTS`. No heap event. No other Agda
compiler was live when the first run started.

- W3 first check, `runs/w3-1.out`: 1.63 s real, 440713216 bytes
  RSS, printed `Checking LJ-1-455.Probe455`, exit 0.
- Three forced rechecks after `rm` of
  `_build/2.8.0/agda/agents/tasks/LJ-1-455/Probe455.agdai`:
  1.50 s, 1.54 s, 1.56 s. Median **1.54 s**. Peak RSS
  **440729600** bytes. Exit 0 every time
  (`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`).

Estimate for the Agda was about 120 lines for the whole
obligation. I did not write the obligation. W3 measured 22
non-blank non-comment lines. Nothing is funded against the
estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-455/`:

- `lj-1.455-report.md`, this report
- `review-of-order-as-set.md`, the W3 obstruction
- `Probe455.agda`, W3 only, `order-as-set` omitted
- `runs/`, the Agda transcripts named above
