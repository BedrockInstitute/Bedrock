# LJ-1.307 report: are the thirty `Agree` modules thirty things, or one thing thirty times?

tier: pi (pi-subagent-mode), model `glm-5.3`. Recon, lands nothing. No
Agda was run. Written incrementally (C-22). Every negative is MEASURED
or INFERRED, in those words.

## 0. LEAD

**PARTLY.**

**ONE shape.** Every module of the thirty proves the same form: a
two-direction bridge between two codings of one notion. The machine
coding names the notion with an `*At` formula. The certificate coding
names it with a `*BS` or `*BndAt` formula. The module proves `out`
and `back` between their satisfaction readings, under closure ties.
`BotAgree` states the form in four lines at
`src/L/Condensation.lagda.md:2792-2799`:

```agda
bot-out : ⟨ γ ⊨ botClauseAt C T ⟩ → ⟨ γ ⊨ φB ⟩
bot-in  : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ botClauseAt C T ⟩
```

MEASURED, by reading all thirty statements.

**About FIFTEEN things.** The thirty fall into fifteen buckets of
genuine mathematics. Five engines are generic over the tag and the
relation. Eight bridges are one-offs. Four row scripts carry the
clause-level rows. The remaining buckets are twins of these. Section 4
gives the partition.

**THIRTY spellings.** Nine of the thirty modules carry no
mathematics of their own. Three are aliases. Two are instantiation
tables. Two are wrappers at moved frames. Two are near-duplicates of
a sibling, one formula or one tag apart. The other twenty-one carry
the fifteen things. MEASURED, by reading each body.

**The abort branch that fired: PARTLY.** The family does not collapse
to one module. It also is not thirty. The port `[LJ-1.306]` builds is
the RIGHT move, and section 6 says why with evidence. A compression of
about 470 lines sits inside the family, it composes with the port, and
it does not close the DD24 gap alone.

## 1. THE COUNT (C-44)

I counted the family myself. The region `src/L/Condensation.lagda.md:2774-7319`
holds 56 module declarations. Thirty carry `Agree` in their name. The
list, in file order:

`BotAgree` 2774, `PropAgree` 3282, `AndAgree` 3534, `OrAgree` 3589,
`TopAgree` 3663, `NegAgree` 3736, `ForallAgree` 3849, `ExistAgree`
3961, `ClauseAgree` 4143, `MemAgree` 4409, `AllInAgree` 5009,
`ExInAgree` 5138, `ImpAgree` 5266, `EqAgree` 5367, `TmAgree` 5708,
`BinFormAgree` 5823, `UnFormAgree` 5913, `ShapesAgree` 6157,
`BinFrameAgree` 6289, `UnFrameAgree` 6339, `ClosedAgree` 6446,
`DomainAgree` 6510, `ShapedAgree` 6548, `WitnessAgree` 6576,
`TagAgree` 6670, `KeyAgree` 6699, `EnvOneAgree` 6748, `DefinesAgree`
6778, `SatGraphAgree` 6844, `LeafAgree` 7107.

MEASURED, by `awk` over the region. The count agrees with
`[LJ-1.298]` and `[LJ-1.302]`. The abort branch "the family is not 30
modules" did not fire.

**Calibers.** The region holds 4,223 non-blank span lines by my count.
The record's 4,208 is the in-fence caliber of `[LJ-1.298]`. The delta
is 15 lines at the fence edges. The thirty modules themselves hold
2,619 non-blank span lines. The other 1,604 sit in the 26 helper
modules, from `ChainZ` at 2817 to `KValue` at 7264. MEASURED.

## 2. THE ONE SHAPE, AND THE TIE CENSUS

### 2.1 The shape

Each module takes a frame of `Fin` indices and an environment. It
takes closure ties. It proves `out` and `back` between the two
codings' satisfaction readings. The bodies run one script: transfer
the code shape, transfer the value, transfer the environment, close
with `extAt→extAtB` or its inverse. `MemAgree.out` at `:4463-4477`
runs all four steps in fifteen lines. MEASURED, by reading.

The recursion hypotheses make the shape inductive. `PropAgree` takes
`fwd` and `bwd` for the bodies at `:3331-3337`. `BinFrameAgree` takes
`relOut` and `relBack` at `:6310-6315`. `SatGraphAgree` takes
`twelve-out` and `twelve-back` at `:6854-6863`. So the family is a
bridge closed under the formula syntax, one step per notion. MEASURED.

### 2.2 The ties are one debt, family-wide

`[LJ-1.302]` found the ties are one debt at the dirty seven. My census
extends the finding to all thirty. The count of telescope positions
per tie name, over `:2774-7319`:

| tie | positions | tie | positions |
|---|---:|---|---:|
| `tagEq` | 32 | `consK` | 16 |
| `numK` | 31 | `valK` | 15 |
| `codesK` | 30 | `subK` family | 14 |
| `envInK` | 30 | `succK` | 14 |
| `keyK` | 29 | `pairK` | 13 |
| `arityK` | 24 | `envK` | 12 |
| `innerK` | 22 | `entryK` | 10 |

MEASURED, by `awk`. The `codesK` shape statement
`fst c ≡ pr (fst ar) (pr (# ...) ...)` appears 45 times in the region.
MEASURED. Every tie says one of three things: the tag slot holds the
numeral, the codes and pairs land in `K`, or the witnesses land in `K`.
That is `[LJ-1.302]`'s one debt, spelled thirty times.

**The telescopes cost about 990 non-blank lines.** I measured the
pre-`where` lines of each module. The detector missed six modules
whose `where` shares a line with the last tie, so 990 is a lower
bound. `SatGraphAgree` alone spends 130 telescope lines, `ShapesAgree`
86, `PropAgree` 60. MEASURED, lower bound. So about 38 percent of the
modules' lines state the ties, and the ties are one debt.

## 3. THE TABLE OF THIRTY ROWS

Calibers: `lines` are non-blank span lines, cut at the next module.
`tel` are pre-`where` telescope lines, lower bound where the detector
missed. `class` is section 4's partition. MEASURED, by reading each
module's statement and body.

| # | module | span | lines | tel | class | bridges; what varies |
|---|---|---|---:|---:|---|---|
| 1 | `BotAgree` | 2774 | 39 | 20 | row | `botClauseAt` against `Bot.botBndAt`, tag 7; no sub-value, `emptyAt` leaf |
| 2 | `PropAgree` | 3282 | 241 | 60 | engine | the op-row protocol, tag `k` and op pair generic; `fwd`/`bwd` for bodies |
| 3 | `AndAgree` | 3534 | 54 | 37 | alias | `PropAgree` at `k=2`, `interAt`, identity `fwd`/`bwd`, `:3572` |
| 4 | `OrAgree` | 3589 | 71 | 37 | alias | `PropAgree` at `k=3`, `unionAt`, disjunction `inK`, `:3627` |
| 5 | `TopAgree` | 3663 | 69 | 27 | row | `topClauseAt` against `topBndAt`, tag 6; no sub-value |
| 6 | `NegAgree` | 3736 | 106 | 37 | row | tag 5; `SubValB2T` sub-value, body is `membership and not` |
| 7 | `ForallAgree` | 3849 | 108 | 41 | row | tag 9; `SubValSuccB2T`, `consK`, `bodyForall` |
| 8 | `ExistAgree` | 3961 | 167 | 42 | row | tag 8; direction twin of 7, exist lift and drop, internal `Leaf` |
| 9 | `ClauseAgree` | 4143 | 59 | 42 | alias | `ExistAgree` re-export, `out = E.out` at `:4195` |
| 10 | `MemAgree` | 4409 | 105 | 46 | row | `memClauseAt` against `memBndAt`, tag 0; `AtomLeaf`, compare `is member` at `:4460` |
| 11 | `ImpAgree` | 5266 | 96 | 42 | row | tag 4; own body, `ImpLeaf` frame swap, `:4518` |
| 12 | `EqAgree` | 5367 | 107 | 46 | twin | tag 1; body of 10 with compare `equals` at `:5418` |
| 13 | `AllInAgree` | 5009 | 124 | 62 | row | tag 10; `BndLeaf`, `all-fwd` and `all-bwd` at `:5102` |
| 14 | `ExInAgree` | 5138 | 125 | 62 | twin | tag 11; body of 13 with `ex-fwd` and `ex-bwd` at `:5262` |
| 15 | `TmAgree` | 5708 | 24 | 6 | one-off | `isTmBS` against `isTmAt`; applies `TmBranch` twice, `:5720-5723` |
| 16 | `BinFormAgree` | 5823 | 87 | 25 | engine | `binForm k relM` against `binFormBS tag K relB`; `k` and both relations generic |
| 17 | `UnFormAgree` | 5913 | 60 | 20 | engine | unary twin of 16 |
| 18 | `ShapesAgree` | 6157 | 126 | 86 | table | applies 16 and 17 at the twelve tags, `B0` to `U11`, `:6185-6229` |
| 19 | `BinFrameAgree` | 6289 | 47 | 28 | engine | `binShapeAt` against `binShapeBS`; `k` and relations generic |
| 20 | `UnFrameAgree` | 6339 | 42 | 25 | engine | unary twin of 19 |
| 21 | `ClosedAgree` | 6446 | 59 | 20 | table | applies 19 and 20 at tags 2 to 11, `C2` to `C11`, `:6471-6483` |
| 22 | `DomainAgree` | 6510 | 34 | 22 | one-off | `domAt` against `domB`, two ties |
| 23 | `ShapedAgree` | 6548 | 25 | 8 | wrapper | `ShapesAgree` at a cons frame, `:6563-6567` |
| 24 | `WitnessAgree` | 6576 | 90 | 31 | one-off | `hasWitnessAt` against `hasWitnessBS`; composes closed and shaped |
| 25 | `TagAgree` | 6670 | 26 | 5 | one-off | `tagAtL` against `tagBS`, tag `k` generic |
| 26 | `KeyAgree` | 6699 | 46 | 7 | one-off | `keyArityAtL` against `keyArBS`; the tag script with a value tie |
| 27 | `EnvOneAgree` | 6748 | 23 | 11 | wrapper | `TagAgree` at `k=0` on a cons frame, plus closure, `:6763-6769` |
| 28 | `DefinesAgree` | 6778 | 58 | 19 | one-off | `DefinesAt` against `DefinesBS`; wraps 27 |
| 29 | `SatGraphAgree` | 6844 | 255 | 130 | one-off | the graph body; applies `ClosedAgree` twice and `DomainAgree` twice, `:6982-7074` |
| 30 | `LeafAgree` | 7107 | 146 | 30 | one-off | `DefBody` against `DefBodyB`; tuple of 26, 29 and 28, `:7231-7243` |

**What varies between neighbours.** Four axes carry all the variance:
the tag numeral, the frame depth and index layout, the sub-value and
leaf transfers the body needs, and the direction of the bounded
wrapper. No module varies by mathematics outside these axes. MEASURED,
by reading. D-26 does not bear: no module differs by what its carrier
carries. The carrier is the class `S` in all thirty, and every tie is
a closure fact or a tag equality. MEASURED, by reading every
telescope.

## 4. THE PARTITION

The abort branch that fired. The partition, with line sums from
section 3:

| class | modules | count | lines | content |
|---|---|---:|---:|---|
| alias | `AndAgree`, `OrAgree`, `ClauseAgree` | 3 | 184 | an application of one engine, re-exported |
| table | `ShapesAgree`, `ClosedAgree` | 2 | 185 | twelve and eight applications of the engines |
| wrapper | `ShapedAgree`, `EnvOneAgree` | 2 | 48 | one application at a moved frame, plus closure |
| twin | `EqAgree`, `ExInAgree` | 2 | 232 | a sibling body with one formula or direction changed |
| row | `BotAgree`, `TopAgree`, `NegAgree`, `ForallAgree`, `ExistAgree`, `ImpAgree`, `MemAgree`, `AllInAgree` | 8 | 814 | own bodies in four shared scripts |
| engine | `PropAgree`, `BinFormAgree`, `UnFormAgree`, `BinFrameAgree`, `UnFrameAgree` | 5 | 477 | generic over tag and relation |
| one-off | `TmAgree`, `TagAgree`, `KeyAgree`, `DomainAgree`, `WitnessAgree`, `DefinesAgree`, `SatGraphAgree`, `LeafAgree` | 8 | 679 | a bridge no other module states |

The sum is 2,619. MEASURED.

**Nine modules carry no mathematics of their own**: the aliases, the
tables, the wrappers and the twins, 649 of the 2,619 lines. MEASURED,
by reading: `AndAgree`
is `module P = PropAgree ... ; open P public` at `:3572-3586`;
`ClauseAgree` sets `out = E.out` at `:4191-4196`; `EqAgree` differs
from `MemAgree` in the compare formula at `:4460` against `:5418`;
`ExInAgree` differs from `AllInAgree` in the tag and two field names
at `:5102` against `:5262`.

**Fifteen buckets hold the mathematics**: the op-row protocol, the
degenerate row, the unary row with sub-value, the quantifier row and
its direction twin, the atom row and its formula twin, the bounded
row, the term bridge, the two form bridges, the two frame bridges, the
tag and key chain, the domain bridge, the witness bridge, and the
graph and leaf composition. MEASURED, by reading. INFERRED, that the
bin and un bridges of each pair could merge into one arity-generic
bridge. Not probed, because this task runs no Agda.

## 5. THE DD13 COMPARISON

### 5.1 What the family would be, written fresh today

Not one module plus thirty instantiations. Not thirty. **Five shapes
plus instantiations**, in the pattern the family already uses one and
two levels down:

1. **Tag-generic row engines.** `BinFrameAgree` takes the tag `k` and
   both relation formulas as parameters, at `:6289-6315`. The row
   modules hard-code what it parameterizes: `MemAgree` fixes tag 0 and
   the membership compare. A fresh row engine would take the clause
   pair as parameters, as `BinFrameAgree` takes `relB` and `relM`.
   The twelve rows become twelve applications.
2. **A tie record.** `KFacts` at `:6076-6110` states thirty-one tie
   fields once, in 35 lines, and `KFactsCons` rebuilds them one frame
   deeper at `:6119-6156`. `SatGraphAgree` passes the block as one
   `f : KFacts` parameter at `:6847-6853`. The row modules instead
   spell nine to twelve ties each, which is the 990-line telescope
   debt of section 2.2. A `RowTies` record in the `KFacts` pattern
   replaces most of it.
3. **The engines, one-offs and composition stay.** They are the
   mathematics. No fresh form shrinks `DomainAgree` or `WitnessAgree`,
   because each states one bridge.
4. **The tables and aliases become applications.** The measured price
   of an application is 7.4 lines in `ClosedAgree` and 10.5 in
   `ShapesAgree`. The measured price of an alias module is 54 to 71
   lines, of which 37 are telescope.

**The `KFacts` block is the measured proof that the record pattern
pays here.** The record and its cons rebuild cost 115 lines once.
Each consumer then takes one parameter. `PropAgree`'s telescope alone
spells 60 lines for the same closure content. MEASURED.

### 5.2 The line estimate, one number with its basis (DD8)

**The fresh family costs about 2,150 non-blank module lines, plus or
minus 150.** Today it costs 2,619. The saving is about 470 lines, 18
percent of the modules and 11 percent of the region's 4,223.

**Basis.** MEASURED: the application prices 7.4 and 10.5 lines per row
inside the two tables; the alias prices 54, 71 and 59 against the 15
an application needs; the `KFacts` record, 35 lines stating what a
60-line `PropAgree` telescope spells; the twin pairs, whose bodies
differ in one formula or two field names; the telescope share, 990 of
2,619. INFERRED: that the clause-level rows can take their formula
pairs as parameters, the way the form and frame twins already do.
This task ran no Agda, so that genericity is an inference from a
measured pattern two levels down, not a probe.

**Seconds.** The chapter checks in 132.28 s and its overage is 61.7 s
against a wing gap of 63.1 s, figures the orchestrator measured and I
inherit. An 11 percent line cut maps to about 15 s, and the cut lines
are telescope lines, which elaborate lookup-chain types, so 15 to
20 s is the plausible band. INFERRED, not measured. **The compression
does not close the DD24 gap alone.** A 15 to 20 s cut against a 61.7 s
overage leaves more than two thirds standing.

### 5.3 What would NOT transfer from the archive

The retired route's `L/Condensation.lagda.md` is 885 lines and holds
no `Agree` family at all. Its one carrier-generic module is `AtCarrier`
at `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:123`.
MEASURED, by reading its module list. So a crossing was delivered once
with one coding and no per-connective agreements. **The shape
transfers: the thirty are not forced by condensation.** The figures and
the theorem do not transfer: the route differed, and nothing there is
checked. The two-dialect coding is this route's choice, and the family
is its price. This confirms `[LJ-1.302]` section 8 from the code side.

## 6. IS THE PORT THE RIGHT MOVE

**YES. Three reasons.**

1. **The genuine 1,970 lines must exist in any form.** The engines,
   rows and one-offs total 477 plus 814 plus 679. Every fresh form
   carries them. `[LJ-1.306]` moved 23 modules at 0 changed lines,
   MEASURED by its verbatim-run search. A rewrite would re-open those
   lines to save the 470 of section 5.2, at an unmeasured price.
2. **The compression composes with the port.** The port makes the
   chapter generic. The compression edits the generic copy: merge the
   telescopes into records, make the rows tag-generic, drop the
   aliases. None of that competes with wave 2. The port is the first
   half of the rewrite, not its rival.
3. **The stop-line reads the other way.** DD13 prices the rewrite
   side, and the rewrite side here says: the ideal form keeps about
   75 percent of the text. "We already paid for it" decides nothing,
   but "the fresh form is three quarters of the old one" does. A
   whole-family rewrite to save 18 percent, inside the wing's widest
   file, while the port stands green at 0 changed lines, is the wrong
   trade today. MEASURED where cited; the trade judgement is mine.

**Do not stop `[LJ-1.306]`.** Its wave 2, the dirty seven, should
proceed. `SatGraphAgree` is the biggest compression candidate later,
with 130 telescope lines of its 255. INFERRED, that its telescope
collapses into the `KFacts` it already takes.

## 7. DD4, WITH THE AXIS NAMED

**My axis: the machine-dialect-against-certificate-dialect axis.** The
family's two codings of one notion are the subject. This is the Def
tower's internal axis, one level below the port's L-against-ambient
axis of `[LJ-1.306]` section 5.

**Would the collapse serve both towers?** No, not directly. The file
sits in the GCH wing and its seconds are the wing's. The orchestrator
measured an hour ago that `src/L/Condensation.lagda.md` sits in
neither trophy closure today. I inherit that measurement and did not
re-measure it. So the de-duplication serves the Def side's lines and
seconds only. INFERRED, from the inherited closure fact.

**The port serves both towers, and the collapse rides the port.** The
generic family re-instantiates at any carrier for one application
block, the 2 lines `[LJ-1.306]` measured at section 4.3. If the J
tower ever needs the agreement machinery, it inherits the compressed
generic form for free. That is DD4's first end. The second end, the
AC-against-GCH share, gains nothing from this task directly. I say so
rather than stretch the axis.

**P-l bears as the design law for the fresh form.** The row modules
name `numeralL 7` and its siblings inside telescope types, a
transparent presentation in a statement's type. The engines already
parameterize `k`. The fresh form states about the tag and stops
spelling it. MEASURED, by reading the telescopes against
`PropAgree`'s `k` parameter at `:3283`.

## 8. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-302/lj-1.302-report.md`, read WHOLE. **Line
  read:** section 4, "The ties are ONE debt, not sixteen." TOOK the
  motivation and the dirty-seven spans; my census extends the finding
  to all thirty.
- `agents/tasks/LJ-1-298/lj-1.298-report.md`, read WHOLE. **Line
  read:** section 0, "The family is 4,208 non-blank in-fence lines."
  TOOK the caliber and the 23/7 split; my own count confirms thirty.
- `agents/tasks/LJ-1-306/lj-1.306-report.md`, read WHOLE. **Line
  read:** section 0, "The count is 23 of 23, and the changed-line
  total is 0." TOOK the port status for section 6. The file was
  complete, not half-written.
- `archive/dev/TASKS-archived.md`, read `:58-75`. **Line read:** the
  `L3.32-T33` row, "Condensation crossing | DELIVERED". TOOK SHAPE
  only: a crossing was delivered under the retired route. No figure
  transfers.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read
  the module list and `:40-60`. **Line read:** `:123`,
  `module AtCarrier (M : S) (Mtr : isTransV M)`. TOOK the shape: one
  carrier-generic module, 885 lines, no `Agree` family. Section 5.3
  says what would not transfer.
- `archive/src/2026-08-09-rud-route/README.md`, read `:1-20`.
  **Line read:** "Nothing here is checked and nothing imports it."
  TOOK the boundary rule for section 5.3.

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:68-133` and `:364-383`.

**How many agreement lemmas does Devlin state? None.** His 5.2 proof
uses one Sigma-zero level-hood formula pair, `Phi` and its analogue
`phi`, bridged by one absoluteness lemma, 1.9.15, quoted at `:88-97`.
He never states a per-connective bridge, at any carrier, in either
direction. MEASURED, by reading the digest.

**So thirty is the port, not the mathematics.** The mathematics is:
the two codings of one notion agree, stated once per notion. Devlin
needs it zero times because he carries one coding. Bedrock carries
two, the certificate for the erase and the graph for the read-off, as
`[LJ-1.302]` section 8 measured. My addition: the port also spells
the once-per-notion statement thirty times where about fifteen would
do.

**WHY NOT the other rows.** Row C2, the bounded Def-step matrix, is
the row family's subject matter and is per-tower; the digest prices
its shape, not a spelling count. Rows A, B, C3 to C6, E and F are
elementarity, collapse, absoluteness, bookkeeping and counting; none
bears on how many modules a coding bridge needs. Rows D and G are
well-order transfers, outside the family.

## 10. WHAT I DID NOT SETTLE

- **The tag-generic row engine.** Section 5.1's first shape is
  INFERRED from the form and frame twins. A probe must typecheck one
  row engine with the clause pair as parameters before the estimate
  binds. This task ran no Agda, so the estimate stays an estimate.
- **The seconds band.** The 15 to 20 s cut of section 5.2 is INFERRED
  from line share. No run measured it.
- **The `RowTies` record's exact size.** The 80-line `KFacts` is the
  comparable; the row ties differ per frame, so the record covers
  most, not all, of the 990. INFERRED.
- **Whether the twelve row instantiations typecheck.** The applications
  exist in the tables, but the row-level instantiation against
  `LowerAgree` and `UpperAgree` was not checked by me.
- **The composite.** `[LJ-1.302]` left `StepAgree` and `ApproxAgree`
  unpriced. Nothing here touches them.

## 11. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-307/`: this report. No Agda was
run, so no heap cap was needed and no `_build/` file of mine exists.
`src/L/Condensation.lagda.md` was read, never opened for writing.
`agents/tasks/LJ-1-306/` and `agents/tasks/LJ-1-305/` were not
touched; the first was read only. `src/Everything.lagda.md`,
`dev/ledger.toml`, `dev/PLAN.md` and `src/L/Choice/Name.lagda.md`
were not touched. No commit, no push, no `git checkout`, `stash`,
`reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py --check` was run on this
report before closing; it passes. No em dash in any language.
