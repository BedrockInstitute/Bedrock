# LJ-1.475 report: the rank formula, over an order that is now a set

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-475/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `rank-formula` in
`agents/tasks/LJ-1-475/Probe475.agda`. Land nothing in `src/`.

## PREDECESSORS, READ BEFORE ANY AGDA

1. `[LJ-1.454]` verdict, `agents/tasks/LJ-1-454/lj-1.454-report.md:73`:
   "**STOP.** W3 typechecks the type `Formula S 2`. Internal delivers the
   ORDER and does not deliver the RANK."
   Corrected target, `:178`: first inhabit `rank-formula : Formula S 2`
   (or a formula with slots for the order as a set), then carve.
   The report does not name the statement FALSE. It names the formula
   missing. I do not inhabit a type that report refused. I inhabit the
   formula that report named as the next target.

2. `[LJ-1.471]` verdict, `agents/tasks/LJ-1-471/lj-1.471-report.md:109`:
   "**GO.** W3 typechecks `hasSeparationL bnd (orderFo R P B C C₀)`"
   Delivered type, `agents/tasks/LJ-1-471/Probe471.agda:90-94`:
   `order-as-set : (R P B C C₀ bnd : S) → Σ[ Q ∈ S ] ((z : S) →
   (z ∈ˢ Q) ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ orderFo R P B C C₀)))`
   I take that type. `Q` in this brief is that carved order, as a
   parameter. I do not rebuild the carve. I do not import a probe.

3. `[LJ-1.468]` verdict, `agents/tasks/LJ-1-468/lj-1.468-report.md:113`:
   "**GO.** W3 typechecks the type `(R P B C C₀ : S) → Formula S 1`."
   Delivered term at `Probe468.agda:78-87`. The carve consumed it.
   I do not restate it.

4. `[LJ-1.416]` verdict, `agents/tasks/LJ-1-416/lj-1.416-report.md:15`:
   "**GO.** The obligation typechecks. The witness meter PASSes."
   Delivered type `swo-rank : {A : Type ℓ} (w : SWO A) → A → S`
   at `Probe416.agda:105-106`, by Acc recursion at `:67-75`. Meta
   language. Not a `Formula`.

5. `[LJ-1.417]` verdict, `agents/tasks/LJ-1-417/lj-1.417-report.md:19`:
   "**GO.** The obligation typechecks (`agents/tasks/LJ-1-417/Probe417.agda`,"
   Delivered type `swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))`
   at `Probe417.agda:80`. A bound. Not a rank. I do not weaken to it.

None of these reports is NO-GO on the formula this brief names. The
454 STOP is the missing formula. This task is that formula.

## D-10, BEFORE ANY AGDA

A rank is a well-founded recursion. Its first-order description is the
approximating-function form the brief names. Written as a type, before
any Agda:

```
rank-formula : (Q : S) → Formula S 2
```

Satisfaction at `(z ∷ a ∷ [])` is the conjunction of these clauses.
Each clause names the delivered constructor it spends.

| clause | what it says | delivered constructor | home |
|---|---|---|---|
| pair | `z` is the pair `(m , r)` | `prAtL` | `src/L/Coding/Model.lagda.md:122` |
| member | `m` is a member of `a` | `_∈̇_` | `src/FOL/Syntax.lagda.md:95` |
| function | `f` is single-valued | `svAt` | `src/L/Coding/Model.lagda.md:210-214` |
| domain | domain of `f` is the `Q`-predecessors of `m` | `inDomAt` and `appAt`, two implications | `src/L/Coding/Model.lagda.md:269-280` and `:160-161` |
| application | `f` sends `x` to `ρ` | `appAt` | `src/L/Coding/Model.lagda.md:160-161` |
| successor | `τ` is the successor of `ρ` | `sucAtL` | `src/L/Coding/Model.lagda.md:1395-1396` |
| supremum | a slot is the set of exactly the `α` that belong to some such successor | `extAt` | `src/L/Coding/Model.lagda.md:662-664` |
| assignment | on the domain, the value at `x` is that supremum over `Q`-predecessors of `x` | the same four, under `∀̇_` and `∃̇_` | `src/FOL/Syntax.lagda.md:99` |

`InjCode` already spends `svAt` and `domAt` as conjuncts
(`src/L/Cardinal.lagda.md:225-227`). `domAt` wants a named domain
set. The `Q`-predecessors of `m` are not a named set. They are the
`x` with `appAt Q x m`. `inDomAt` plus `appAt` plus two implications
is that biconditional. The object language has no biconditional of
its own (`src/L/Coding/Model.lagda.md:253-254`).

`extAt y φ` is "y is the set of exactly the things that satisfy φ"
(`src/L/Coding/Model.lagda.md:662-664`). The meta-level rank step is
`⋃ (sett ⟪ x ⟫ (λ m → sucV (rec ...)))` at
`src/L/Rank.lagda.md:86`. The object-language spelling of that union
of successors is `extAt` at a condition that binds a predecessor, an
application, a successor, and a membership. There is no constructor
named `supAt`. `unionAt` at `:687-688` is binary union of two named
sets. It is not a family-union. `extAt` is the delivered supremum
clause.

No clause has no delivered formula. I did not stop. I did not invent
a constructor. I composed the constructors the table names.

The W3 term is the function-and-domain clause alone, at three slots
`(f ∷ Q ∷ m ∷ [])`:

```
fn-clause : Formula S 3
fn-clause = fnAt zero (suc zero) (suc (suc zero))
```

where `fnAt f Q m` is `svAt f` and the two implications between
`inDomAt f x` and `appAt Q x m`. The obligation was omitted from
that file.

## VERDICT

**GO.** W3 typechecks `fn-clause : Formula S 3`
(`Probe475.agda:86-87`). `svAt`, `inDomAt` and `appAt` compose into
the function-as-a-set clause. `rank-formula : (Q : S) → Formula S 2`
inhabits the obligation (`Probe475.agda:95-103`). Exit 0. No heap
event. I did not write `review-of-rank-formula.md`. I did not
postulate. I did not weaken the rank to a bound. I did not prove
adequacy. I did not carve.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

P-l (`dev/LESSONS.md:2357`): the type is over the generic carrier
`S`. It does not name a transparent stage presentation.

D-26 (`dev/LESSONS.md:1735`): a definable power carries no generation
data and needs syntax. This formula is that syntax for the rank of
an order carried as a set. This task does not well-order a tower
stage.

## 1. W3: `fn-clause`, first

**GO.** `svAt` and `inDomAt` compose with `appAt` at a slot for `Q`.
The named-domain form `domAt` is not required.

Stated as `fn-clause : Formula S 3` equal to
`fnAt zero (suc zero) (suc (suc zero))` (`Probe475.agda:86-87`).
Env is `(f ∷ Q ∷ m ∷ [])`. The body of `fnAt` is `svAt f` and two
implications (`Probe475.agda:51-55`). The obligation was omitted.
The clause typechecked. Constants in Term position were not yet in
play: `Q` is a slot.

ESTIMATE for W3 was about 20 lines and under 20 seconds. MEASURED:
`fnAt` is 5 lines, `fn-clause` is 2 lines. The W3-only file
typechecked. Comparables of shape, not of size. Nothing is funded
against the estimate.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 0.97 | 328597504 | `runs/w3-2.out` |
| w3-3 | 0.97 | 328613888 | `runs/w3-3.out` |
| w3-4 | 0.97 | 328597504 | `runs/w3-4.out` |

Median wall **0.97 s**. Peak RSS **328613888** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.07 s and
328613888 bytes, also exit 0. It is not one of the three forced
rechecks.

## 2. The inhabitant `rank-formula`

`rank-formula` is `Probe475.agda:95-103`. `Q` is a parameter. One
pin `var zero ≐ con Q` puts it in Term position, the RelCond /
`appAtC` move (`src/L/Choice/Before.lagda.md:220-226`, `:1302-1303`).
Then three binders `m`, `r`, `f`. After those the env is
`0 = f, 1 = r, 2 = m, 3 = Q', 4 = z, 5 = a`. The body is:

- `prAtL` at `z`, `m`, `r`
- `m ∈̇ a`
- `fnAt` at `f`, `Q'`, `m`
- `assignAt` at `f`, `Q'`
- `supAt` at `f`, `r`

`assignAt` (`Probe475.agda:63-71`) is the rank assignment: every
domain member has a value, and that value is `extAt` of belonging
to `sucAtL` of a value at a `Q`-predecessor. `supAt`
(`Probe475.agda:75-80`) is the same `extAt` over the values of `f`.
Both are generic in slots. `rank-formula` instantiates them after
the pin.

I did not rebuild `order-as-set`. I did not import a probe. I did
not postulate. I did not inhabit a bound. I did not write
`rank-graph`.

ESTIMATE for the Agda was about 160 lines, of which the obligation
is about 50. MEASURED: 53 non-blank non-comment lines in the full
probe, of which `rank-formula` is 9 lines (`Probe475.agda:95-103`).
Comparables of shape, not of size. Nothing is funded against the
estimate.

Three forced rechecks of the full file, same caliber, one Agda
process at a time, interface removed:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| full-2 | 0.99 | 310853632 | `runs/full-2.out` |
| full-3 | 1.04 | 310837248 | `runs/full-3.out` |
| full-4 | 0.97 | 310853632 | `runs/full-4.out` |

Median wall **0.99 s**. Peak RSS **310853632** bytes. Exit 0 every
time. No heap event. The first check `runs/full-1.out` was 0.97 s
and 310886400 bytes, also exit 0. It is not one of the three forced
rechecks.

## WHAT THE CARVE WOULD NOW COST

Do not carve it. The type, once `a` is pinned to a constant so
separation sees `Formula S 1`:

```
rankFo : (Q a : S) → Formula S 1

rank-graph :
    (Q a bnd : S)
  → Σ[ G ∈ S ] ((z : S) → (z ∈ˢ G)
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ rankFo Q a)))
```

`rankFo Q a` is `rank-formula Q` with the free `a` pinned as
`con a`, the same RelCond move this probe used for `Q`.
`hasSeparationL` consumes that formula
(`src/L/Axioms/Full.lagda.md:144-145`). The unique `SetOf` is the
carve, as `order-as-set` spent it (`Probe471.agda:90-94`).

The bound `bnd` is not delivered at this `Q`. The device that
would name it is `PairBound a β` (`src/L/InjChain.lagda.md:276-297`).
`β` is an ordinal bound for the ranks. `[LJ-1.417]` delivers
`swo-into-ord` at a generic `SWO A` (`Probe417.agda:80`), not at a
set `Q`. Instantiating `PairBound a β` from that injection, and
bridging `Q` as a set to an `SWO`, are separate prices. Do not
postulate the bound. `[LJ-1.471]` already measured that the bound
of the order-carve stays a parameter
(`agents/tasks/LJ-1-471/lj-1.471-report.md:264-268`). Re-measure
the rank bound at its own site.

## ADEQUACY, NOT PROVED

`[LJ-1.454]` asked for a formula, not for its two readings
(`agents/tasks/LJ-1-454/lj-1.454-report.md:73`). This task does
not prove them.

`prAt-adequate` is one line because the clauses match the
meta-level pair characterization
(`src/L/Coding/Base.lagda.md:323-329`). The rank formula's clauses
match approximating functions. The meta rank is Acc recursion
(`Probe416.agda:67-75`). Those are not the same spelling. Adequacy
is the bridge from `(z ∷ a ∷ []) ⊨ rank-formula Q` to "`z` is the
pair of a member of `a` and `swo-rank` of that member". It needs
a well-order from the set `Q`, which this formula does not read
as `SWO`. The comparable of shape is `LimitOrdAt-in` /
`LimitOrdAt-out` (`src/L/Choice/Limit.lagda.md:535-554`), not the
one-line `prAt-adequate`. I did not price that bridge as a number.
It is a separate brief.

## 3. W2

The terms are generic in the carrier `S`. `fnAt`, `assignAt` and
`supAt` are written once at slots. `rank-formula` instantiates `Q`
as a constant by one pin. They name no stage, no cardinal, no
numeral, and no `Lset`. I did not write a fixed form. W2 holds for
what was written. No deadline asked for a fixed form.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. C-42 sweep

`[LJ-1.454]` measured ONE site: whether Internal delivers
`rank-formula : Formula S 2`. That site still does not. This task
is not that inventory. It writes the formula from Coding's
constructors.

Sweep of THIS shape, a `Formula` for the rank of a well-order
carried as a set:

- `src/`: 0 hits for `rank-formula`. 0 hits for `swo-rank`.
- `src/`: 0 hits for `fn-clause`. 0 hits for `assignAt` as a
  `Formula`.
- Internal's exported `Formula` constructors that describe rank:
  **0**, as `[LJ-1.454]` counted
  (`agents/tasks/LJ-1-454/lj-1.454-report.md:209-211`).
- Live `Formula` constructors this probe composed: `prAtL`,
  `appAt`, `svAt`, `inDomAt`, `extAt`, `sucAtL`. Count of a
  rank formula in `src/`: **0**.

The three `amb-to-coded` NO-GOs are a different shape (an arbitrary
element of `_↪_`). This sweep does not re-price them.

## WHAT THE NEXT BRIEF NEEDS

- `rank-formula : (Q : S) → Formula S 2` typechecks
  (`Probe475.agda:95-103`). Satisfaction at `(z ∷ a ∷ [])` is
  spelled by a pin of `Q`, a pair reader, membership in `a`, a
  function whose domain is the `Q`-predecessors of `m`, a rank
  assignment on that domain, and a supremum of successors of
  values.
- `fn-clause : Formula S 3` typechecks (`Probe475.agda:86-87`).
  `domAt` is not the obstruction. `inDomAt` plus `appAt` is the
  domain clause when the domain is not a named set.
- Do not send `rank-graph` without a `Formula S 1` (pin `a`) and
  a named bound. The carve type is in `## WHAT THE CARVE WOULD NOW
  COST`. The bound device is `PairBound a β`. Re-measure it.
- Do not send adequacy as part of the carve. Adequacy is a
  separate bridge from approximating functions to `swo-rank`.
- Do not weaken to `swo-into-ord`. That is a bound
  (`Probe417.agda:80`).
- Do not rebuild `order-as-set`. Take `Q` as a parameter, as this
  probe did.
- Do not reuse `[LJ-1.414]`, `[LJ-1.426]`, or `[LJ-1.441]`. Those
  sites are arbitrary `leastOf` arrows. C-42 forbids the transfer.

What the statement cost: 53 non-blank non-comment lines, W3 median
0.97 s, full-file median 0.99 s, peak RSS 328613888 bytes. What
the shape resisted: `domAt` wants a named domain; the predecessor
set is a formula, so `inDomAt` plus `appAt` is the clause. What I
had to weaken: nothing. What I could not close: adequacy, and the
carve, both out of scope.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`
  "THE `LJ` DISPATCH INDEX, archived 2026-08-18"
  Declined. Not used. It is a dispatch index. It does not bear on
  whether `svAt` and `appAt` compose into a rank formula.
- `archive/dev/JOURNAL-archived.md:1229`
  "no ordinal arithmetic, no order-type or rank theory; the absence was"
  Read. Used. That archived journal records the absence of rank
  theory in the retired route. `[LJ-1.416]` filled the rank as
  DATA. This task fills the object-language half of that absence
  as a `Formula`.
- `archive/dev/JOURNAL.md:3`
  "The per-episode journal is retired."
  Declined. Not used. The per-episode journal is retired. The
  history of this campaign is the task directories.
- `dev/ARCHIVE.md:283`
  "A classical well-order over finite labelled trees by shortlex"
  Read. Used. The retired `L.WellOrder.Tree` is a well-order, not
  a rank formula. No retired module turns a well-order into a
  `Formula S 2` for the rank. This task does not retire a module.
- `archive/dev/DD-archived.md:1`
  "THE `DD` RULING SERIES, archived in full 2026-08-18"
  Declined. Not used. The archived D series does not bear on
  `rank-formula`.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin uses a definable well-order to
  SELECT a least witness. This task does not select. It describes
  the rank of an order that is already a set.
- `dev/literature/truncation-and-selection.md:67`
  "The selection device is a definable well-order plus a universal guard."
  Read. Used. The rank formula is not that device. Internal's
  order formula is the well-order side. The rank is a recursion
  on that order, now spelled as approximating functions.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. Internal describes
  that order without running a recursion of its own
  (`src/L/Choice/Internal.lagda.md:22`). This formula is the
  recursion, in the object language, of the rank of that order.
- `dev/literature/terms-2026-08.md:230`
  "The ordinal a well-order collapses to: "the order type of the"
  Read. Used. That is the sense of `swo-rank` as DATA
  (`Probe416.agda:105-106`). This formula is the object-language
  description of that ordinal, at a member, over the order as a
  set.
- `dev/literature/glossary-review-2026-08.md:1`
  "Glossary review: the 119 pre-protocol entries"
  Declined. Not used. It reviews glossary entries. It does not
  bear on a rank formula.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, from the repository
root. I did not set `GHCRTS`. No heap event. No other Agda
compiler was live when the first run started.

- W3 first check, `runs/w3-1.out`: 1.07 s real, 328613888 bytes
  RSS, printed `Checking LJ-1-475.Probe475`, exit 0.
- Three forced rechecks after `rm` of
  `_build/2.8.0/agda/agents/tasks/LJ-1-475/Probe475.agdai`:
  0.97 s, 0.97 s, 0.97 s. Median **0.97 s**. Peak RSS
  **328613888** bytes. Exit 0 every time
  (`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`).
- Full-file first check, `runs/full-1.out`: 0.97 s real,
  310886400 bytes RSS, printed `Checking LJ-1-475.Probe475`,
  exit 0.
- Three forced rechecks after `rm` of the same interface:
  0.99 s, 1.04 s, 0.97 s. Median **0.99 s**. Peak RSS
  **310853632** bytes. Exit 0 every time
  (`runs/full-2.out`, `runs/full-3.out`, `runs/full-4.out`).

Estimate for the Agda was about 160 lines for the whole
obligation. MEASURED 53 non-blank non-comment lines. Nothing is
funded against the estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched. No `review-of-*.md`.

New files, all in `agents/tasks/LJ-1-475/`:

- `lj-1.475-report.md`, this report
- `Probe475.agda`, W3 `fn-clause` then `rank-formula`
- `runs/`, the Agda transcripts named above
