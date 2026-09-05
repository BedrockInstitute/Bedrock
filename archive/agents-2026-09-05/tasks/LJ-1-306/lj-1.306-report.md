# LJ-1.306 report: the clean 23 `Agree` modules ported generic, wave 1 of `q'`

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**The count is 23 of 23, and the changed-line total is 0.**

`agents/tasks/LJ-1-306/GenAgree.agda`, exit 0, cold 155.1 s, ports ALL
twenty-three clean modules: `BotAgree`, `PropAgree`, `AndAgree`,
`OrAgree`, `TopAgree`, `NegAgree`, `ForallAgree`, `ExistAgree`,
`ClauseAgree`, `MemAgree`, `AllInAgree`, `ExInAgree`, `ImpAgree`,
`EqAgree`, `TmAgree`, `BinFormAgree`, `UnFormAgree`, `ShapesAgree`,
`BinFrameAgree`, `UnFrameAgree`, `ClosedAgree`, `ShapedAgree` and
`TagAgree`. It also ports their whole supporting closure: 146 blocks in
all, the 23 modules plus 123 helpers, from the twelve row modules to
`KFactsNS` and the `PairIs` carve. MEASURED, by the manifest and the
green run.

**Zero copied lines changed.** The port copies 5,131 span lines from
`src/L/Condensation.lagda.md`, 4,711 non-blank, and 32 lines from
`src/L/Coding/Shape.lagda.md`, 27 non-blank. Every one of the 146
chapter blocks and all three Shape blocks appear in the emitted file as
exact contiguous runs. **The changed-line count is 0 of 4,738 copied
non-blank lines.** MEASURED, by the verbatim-run search over
`manifest.json`.

**One scaffold served them all.** The hand-written scaffold is 45
non-blank load-bearing lines, plus a 19-line header comment. It is
`[LJ-1.298]`'s `GenTagAgree` shape, once, for the whole chapter. No
module needed its own. MEASURED FALSE, the abort branch "the scaffold
does not serve them all".

**The 180 stands, and wave 1 costs less than its share.** My
hand-written total is 45 scaffold lines. Nothing else was written: the
Shape syntax the five modules need is copied, and the clean 23 needed
no formula re-statements at all. The remaining about 135 of the 180
belongs to the dirty seven's gaps, which `[LJ-1.298]` priced. The rate
is also better than projected: 155.1 s over 4,958 non-blank lines is
0.031 s per line, below the 0.039 s the record projected.

**One list correction (C-44).** `[LJ-1.298]`'s sweep said the 23 name
"nothing outside `GenModel`'s deliveries, the chapter's own `*BS`
syntax and its pre-family helpers". Five of them name committed
`L.Coding.Shape` deliveries in their types. Section 1 gives the names
and the cure, which cost 27 copied lines.

**The owner's ruling is answered in section 4.** The replacement serves
every consumer unchanged, at zero external edit cost, MEASURED three
ways.

## 1. THE CLEAN LIST, RE-DERIVED

I re-derived the list from the text, comment-stripped, with a
name-dependency closure over the chapter's blocks. Two corrections to
the record came out of the re-derivation.

**Correction one: five modules name `L.Coding.Shape`.** On
comment-stripped code, five of the 23 name ten committed Shape
deliveries in their statement types:

| module | names | at |
|---|---|---|
| `TmAgree` | `isTmAt` | `:5722-5723` |
| `BinFormAgree` | `binForm` | `:5840` |
| `UnFormAgree` | `unForm` | `:5936` |
| `ShapesAgree` | `shapes`, `binForm`, `unForm`, `bothTm`, `fstTm`, `noneB`, `noneU`, `zeroPay` | `:6225-6277` |
| `ShapedAgree` | `shapedAt` | `:6561` |

The sweep was textual and these names are not aliases: they are direct
imports at `src/L/Condensation.lagda.md:58-60`. So the honest split is
18 strictly clean plus 5 clean after one restatement. **The cure is
measured: restate the Shape syntax**, copied verbatim from
`src/L/Coding/Shape.lagda.md:99-105`, `:140-142` and `:169-190`, 27
non-blank lines, pure syntax over `GenModel` primitives, 0 changed. The
five then port at the same zero rate. MEASURED.

**Correction two: the closure is bigger than the sweep's eye.** My
first parse missed every `Δ₀-*` name, because they start with a Greek
letter. The corrected parser found 58 `Δ₀-*` derivation blocks inside
the closure, from `Δ₀-prAtL` at `:81` to `Δ₀-DefinesBS` at `:1780`.
None is dirty: the dirty seven's spans never entered the closure.
`DIRTY IN CLOSURE: []`, MEASURED by the closure computation over
`closure.json`.

The 23's closure is 146 blocks and 4,711 non-blank copied lines. The
dirty seven's spans, `DomainAgree` through `LeafAgree`, were never
touched, and `KValue` at `:7246-7319` was not ported.

## 2. THE PORT

`GenAgree.agda` has three regions. The scaffold is the 45-line
`[LJ-1.298]` shape: the imports, `GenModel`'s eight parameters, the
`GM` application, and the two opens, `open GM` and
`open GM.ToL using ( Δ₀-liftFo )`. `Δ₀-liftFo` is the generic twin of
the committed `L.Absoluteness` delivery, and it arrives under the same
name. The second region is the Shape restatement of section 1. The
third region is the 146 blocks, copied in chapter order, with
`manifest.json` recording each block's source range.

The port re-derives the `[LJ-1.298]` rate at 23 sites at once, not just
the second module the brief asked for. `TagAgree` was one observation;
this run is twenty-three, plus 123 helpers, all at 0 changed lines. The
C-42 caveat on the clean modules is now retired for the port itself.

Three scaffold edits were needed to make the file load, and none
touched the copied text: `⁅_⁆s` joined an import, and two fence-marker
leaks from my slicing were removed. The first parse error and the
missing import are in the runs table.

## 3. THE RATE, THE SECONDS, THE ABORT REVIEW

| quantity | value |
|---|---|
| modules ported | 23 of 23 clean |
| supporting blocks | 123 |
| copied span lines | 5,131 chapter + 32 Shape |
| copied non-blank lines | 4,711 + 27 |
| changed lines | **0** |
| hand-written scaffold | 45 non-blank, plus 19 comment |
| cold elaboration | 155.1 s, load 6.73 / 6.58 / 5.94, 3 users |
| reload | 2.3 s |
| rate | 0.031 s per non-blank line |

The abort criteria, fixed before the run:

- **The port runs at the measured rate.** 23 ported, 0 changed, one
  scaffold, 155.1 s cold. This branch fired and I stop here.
- **A module is not clean after all.** Fired in the corrected form of
  section 1: five modules reach committed Shape names. The cure was 27
  copied lines, and the port is green with it.
- **The rate is not zero.** MEASURED FALSE, by the verbatim-run search.
- **The scaffold does not serve them all.** MEASURED FALSE.
- **A wall.** No run passed 30 minutes. The longest was 155.1 s.

## 4. THE REPLACEMENT, C-40, OWNER'S RULING 2026-08-15

The ruling changes the landing from additive to a replacement. A
replacement must serve every consumer of the family. This section
answers the three questions, and the probe
`agents/tasks/LJ-1-306/ProbeCompat.agda` measures the answers.

### 4.1 WHO CONSUMES THE CLEAN 23 TODAY

**Five files outside the chapter import `L.Condensation`.** MEASURED,
by grep over `src/`.

| consumer | reaches | ported? |
|---|---|---|
| `src/L/BoundedSubset.lagda.md:29-32` | `DefBodyB`, `Δ₀-DefBodyB`, `module GraphB` | none; all pre-family, they stay |
| `src/L/Condensation/LowerAgree.lagda.md:33-35` | `envHypB2`, rows `Mem` `Eq` `And` `Or` `Imp` `Neg`, `MemAgree` `EqAgree` `AndAgree` `OrAgree` `ImpAgree` `NegAgree` | all 13 ported |
| `src/L/Condensation/UpperAgree.lagda.md:33-36` | `succU`, `keyU`, rows `Top` `Bot` `Exist` `Forall` `AllIn` `ExIn`, `TopAgree` `BotAgree` `ExistAgree` `ForallAgree` `AllInAgree` `ExInAgree` | all 14 ported |
| `src/L/Condensation/TwelveAgree.lagda.md:31` | `succU`, `keyU`, `module SatGraphB` | 2 ported, `SatGraphB` stays |
| `src/L/Coding/EnvSupply.lagda.md:47` | `envSetB`, `module EnvSet` | both ported |

**Inside the chapter, 53 blocks outside the closure reach ported
names.** They are the `Δ₀-*` derivations, the twelve `*Row` modules at
`:1814-2229`, `SatGraphB`, `StepB`, `ApproxB`, the dirty seven and
`KValue`. All sit inside the replaced file, so the application serves
them by scope. MEASURED, by the consumer computation over
`closure.json`.

### 4.2 WOULD THE GENERIC FORM SERVE THEM UNCHANGED

**YES, MEASURED, 39 checks green, `ProbeCompat.agda` exit 0, 7.9 s.**
The probe applies `GenAgree` at the class, with `isL`, `isL-trans` and
the six `L.Axioms.Numerals` supplies, which is the application
`[LJ-1.210]` already measured at `ProbeLJ1210Inst.agda:47`. Then:

1. **Four formula refls, generic against delivered**: `tagAtL`,
   `botClauseAt`, `topClauseAt`, `envOverAt`. These extend
   `[LJ-1.210]`'s nine to the names the family statements reach.
2. **Twenty-seven term-identity refls**: the first field of all twelve
   row modules, `envHypB2`, `envSetB`, `succU`, `keyU`, `tagBS`, and
   the ten restated Shape names against `L.Coding.Shape`. All `refl`.
3. **Four serving checks**: `TagAgree.out` and `.back`, `BotAgree`
   both directions. Each states the consumer's statement at the
   ORIGINAL names and gives the GENERIC module's field as the term.
   This is the consumer's exact situation, and it typechecks.
4. **Two `EnvSet` refls**, for `L.Coding.EnvSupply`'s two names.

**The one failure, and why it does not bind.** My first probe form
compared proof terms on the nose:
`Orig.TagAgree.out ... ≡ Fam.TagAgree.out ...`. It FAILED, with

```text
L.Coding.Model.lookup-fst s γ (primINeg i)
!= Fam.GM.lookup-fst s γ (primINeg i)
```

The adequacy paths embed `lookup-fst` proofs, which are stuck neutrals
under a variable `Fin` index. Two copies with different head symbols
do not convert. MEASURED, at the first run of the restructured probe.
No consumer writes that equation: the family's outputs are
prop-valued, squashed, and consumers apply the fields, they never
equate them. The boundary is exact: types and terms at the formula
layer serve; proof-term identity across the two declarations does not
survive. The serving checks live inside that boundary and are green.

**`KFacts` is the one structural exception.** It is a fresh record
declaration in the port, and two records never convert nominally. No
external file reaches it, MEASURED by the grep in 4.1. Its internal
consumers, the dirty seven and `KValue`, resolve it through the open.
INFERRED green for them: their own text was not checked against the
landed chapter today, because their port is wave 2.

**The landing mechanic is measured too.** `ReexportTest.agda` applies
the family and does `open Fam public`; `ReexportUse.agda` imports it
with `LowerAgree`'s exact `using` list. Both exit 0. The consumer
files keep their import lines byte for byte. MEASURED.

### 4.3 WHAT THE REPLACEMENT COSTS ON TOP OF THE PORT

**About 4 to 8 lines, all inside the replaced chapter, and zero
external edits.** MEASURED as the probe's own application block:

- the class application, 2 lines, `module Fam = GenAgree {ℓ} isL
  isL-trans numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst`;
- `open Fam public`, 1 line;
- the import of the generic module, 1 line;
- the preamble merge, about 2 to 4 lines edited: the ten Shape names
  now come from the port, and the `L.Coding.Model` using-list shrinks
  to what the non-closure remainder needs.

Nothing in the 180 moves. The figure was hand-written code for the
family and its gaps, and the replacement adds none: the supplies were
already delivered at the class by `L.Axioms.Numerals`. DD13 and
`dev/ARCHIVE.md` are the orchestrator's, per the ruling, and this
report only prices the replacement.

## 5. DD4, WITH THE AXIS NAMED

**My axis is the port's L-against-ambient axis.** The carrier is the
subject of this port. `amb` reads one formula at two carriers, and the
`Agree` family is the machinery that makes the two codings agree. This
task is DD4 itself: it takes a chapter written at one carrier and
makes it serve two, which is the rule's first end.

**What the J tower pays to re-instantiate the family.** One
application block, the 2 measured lines of section 4.3, at any carrier
that supplies the class and the six operations. The per-module
instantiation is then free, as `[LJ-1.298]` measured at `TagAgree`
with 30 ambient lines including two transports, and `[LJ-1.302]` at
`DomainAgree` with 51 lines including both ties. What does NOT
transfer for free is the per-site tie supply: the clean modules'
telescopes take the same kinds of ties as the dirty seven's, and
`[LJ-1.302]` priced the dirty seven's at about 100 lines. The clean
23's ties at a concrete ambient environment are UNMEASURED, INFERRED
at the same order. The second end, AC against GCH, gains nothing from
this port, and I say so rather than stretch the axis.

**P-h holds here.** The definability walk is module-parameterized, and
that is exactly what the class parameter is. The port is the law's
paid instance at chapter scale.

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| any of the 4,738 copied non-blank lines changed | **MEASURED FALSE.** Verbatim-run search over all 149 blocks |
| a second scaffold was needed | **MEASURED FALSE.** One served 146 blocks |
| the clean 23 need formula re-statements | **MEASURED FALSE.** Zero written; the Shape restatement is a copy |
| `[LJ-1.298]`'s 23 name nothing committed | **MEASURED FALSE.** Five name ten `L.Coding.Shape` deliveries, section 1 |
| the port hits a wall | **MEASURED FALSE.** Longest run 155.1 s under the 8g cap |
| the generic family fails to serve an external consumer | **MEASURED FALSE** at 39 checks, `ProbeCompat.agda` exit 0 |
| proof terms of the two declarations are identical | **MEASURED FALSE.** Stuck `lookup-fst` neutrals, section 4.2 |
| `LowerAgree`'s import line survives the landing | **MEASURED.** `ReexportUse.agda` exit 0 |
| the dirty seven typecheck verbatim against the landed chapter | **INFERRED.** Their port is wave 2, not checked today |
| the other 18 clean modules serve, untested one by one | **INFERRED.** The mechanism is measured at `TagAgree` and `BotAgree` plus 27 refls, C-42 |
| the clean 23's ties supply at ambient at the dirty seven's rate | **INFERRED.** Tie kinds match, sites differ |
| the whole-chapter check lands near 300 s | **INFERRED.** My rate, 0.031 s per line, sits below the projection's 0.039 |
| a probe under `src/` was written | **MEASURED FALSE.** All files sit in `agents/tasks/LJ-1-306/` |
| the sibling `LJ-1-305` was touched | **MEASURED FALSE.** `git status` shows my writes only |

## 7. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-298/lj-1.298-report.md`, read WHOLE, FIRST, as
  the brief orders. **Line read:** section 3, "23 of 30 modules clean:
  their text names nothing outside `GenModel`'s deliveries". TOOK the
  task, the family figures and the 180; CORRECTED the clean-list
  claim at my section 1.
- `agents/tasks/LJ-1-298/GenTagAgree.agda`, read WHOLE, FIRST, per
  SCOPE. **Line read:** `:58-59`, the eight-parameter telescope and
  `module GM =` application. TOOK the scaffold, copied line for line.
- `agents/tasks/LJ-1-302/lj-1.302-report.md`, read WHOLE. **Line
  read:** section 4's tie table, "`DomainAgree` ... `entryK`,
  `domK`". TOOK the dirty-seven boundary, so nothing was ported into
  their shape.
- `agents/tasks/LJ-1-238/GenSequence.agda`, read `:1-75`. **Line
  read:** `:33`, `module GM = LJ-1-210.GenModel {ℓ} M M-trans ...`.
  TOOK the generic-port precedent that paid.
- `agents/tasks/LJ-1-210/ProbeLJ1210Inst.agda`, read `:1-60`.
  **Line read:** `:47`, `module AtL = LJ-1-210.GenModel {ℓ} isL
  isL-trans`. TOOK the class application and the discovery that
  `sucʟ` and `sucʟ-fst` are delivered at the class.
- `agents/tasks/LJ-1-210/GenModel.agda`, read `:1-100` and grepped.
  **Line read:** `:70`, `open ToL using ( liftFo; Δ₀-liftFo )`. TOOK
  the delivery surface and the `Δ₀-liftFo` routing.
- `archive/dev/TASKS-archived.md`, read `:58-75`. **Line read:** the
  `L3.32-T33` row, "Condensation crossing | DELIVERED". TOOK SHAPE
  only: a crossing was delivered under the retired route, and no
  figure and no content transfers.

## 8. LITERATURE USED (DD18)

No literature bears on a mechanical re-instantiation, as the brief
states. Nothing was read and nothing was used.

## 9. WHAT I DID NOT SETTLE

- **The dirty seven's port.** Wave 2. Their ambient ties are
  `[LJ-1.302]`'s about 100 lines, and their verbatim typecheck against
  the landed chapter is INFERRED, section 4.2.
- **The one opaque in the family.** `opaque unfolding satGraphAt` at
  `src/L/Condensation.lagda.md:7069-7071` sits inside dirty
  `SatGraphAgree`. MEASURED, by grep, it is the only opaque. Wave 2
  must unfold the generic `satGraphAt` there.
- **The clean 23's tie supply at the ambient carrier.** Unmeasured.
  `StepAgree` and `ApproxAgree` are `[LJ-1.304]`'s, untouched here.
- **Whether `q'` is true.** Neither confirmed nor refuted, as the
  chain leaves it.
- **The landed chapter's own seconds.** 155.1 s prices my file with
  `GenModel`'s interface cached and the chapter's remainder absent.

## 10. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap
NEVER raised. No heap exhaustion. No invocation near 30 minutes. Load
4.62 to 9.15, 3 users throughout.

| file | exit | seconds | note |
|---|---:|---:|---|
| `GenAgree.agda` | 42 | 0.6 | parse: a fence marker leaked into a slice |
| `GenAgree.agda` | 42 | 2.6 | scope: `⁅_⁆s` missing from an import |
| `GenAgree.agda` | 0 | **155.1** | cold elaboration |
| `GenAgree.agda` | 0 | 2.3 | reload |
| `ProbeCompat.agda` | 42 | 7.1 | the term-identity finding, section 4.2 |
| `ProbeCompat.agda` | 0 | 7.9 | restructured, 39 checks green |
| `ReexportTest.agda` | 0 | 4.3 | application plus public open |
| `ReexportUse.agda` | 0 | 1.4 | `LowerAgree`'s import line, unchanged |
| `ProbeCompat.agda` | 42 | 3.0 | scope: `GenModel` import missing |

The first two and the last failures sat in scaffolding and never
touched copied text.

## 11. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-306/`: the report, the brief
copy, `GenAgree.agda`, `ProbeCompat.agda`, `ReexportTest.agda`,
`ReexportUse.agda`, and the three evidence files `closure.json`,
`manifest.json` and `gmnames.json`. `src/` holds no probe of mine, and
`src/L/Condensation.lagda.md` was read and copied from, never opened
for writing. `agents/tasks/LJ-1-305/` was not touched. I did not open
`src/Everything.lagda.md`, `dev/ledger.toml`, `dev/PLAN.md` or
`src/L/Choice/Name.lagda.md` for writing. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py --check` and
`scripts/gate/lint-agda.py --check` both pass on my files. No em dash
in any language. `_build/` holds only Agda's own interface files for
my modules. `dev/ARCHIVE.md` is the orchestrator's, per the ruling.
