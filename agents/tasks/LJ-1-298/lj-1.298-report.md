# LJ-1.298 report: the price of `q'` through the delivered class-carrier analogues

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe, lands nothing. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**The re-instantiation is MECHANICAL, and the count is ZERO.**

`TagAgree` and its two local dependencies total 33 non-blank agda lines in the
delivered chapter. I re-instantiated all 33 with the class as a module
parameter. **Zero of the 33 lines changed.** A `diff` of the ported region
against `src/L/Condensation.lagda.md:6666-6669`, `:1484-1487` and `:6670-6697`
reports one added blank separator line and nothing else. The file typechecks:
`agents/tasks/LJ-1-298/GenTagAgree.agda`, exit 0, 1.29 s. MEASURED.

The port added 57 non-blank scaffolding lines around the verbatim body. Of
those, 19 are the header comment and 38 are imports, the class telescope and
the `GenModel` application. One scaffold serves the whole chapter, as
`GenSequence`'s header serves all of `L.Coding.Sequence`.

**The ambient instantiation is green too.**
`agents/tasks/LJ-1-298/ProbeLJ1298Amb.agda`, exit 0, 3.90 s, applies the
generic module at the ambient class `Full` with probe D's numerals, pairs and
successor, and delivers both directions of `TagAgree` at the ambient reading
`A.ambient`. MEASURED.

**Two corrections to the record (C-44), neither of which softens the verdict.**

1. The family is **4,208** non-blank in-fence lines, not 3,871. I re-derived
   the figure with the ledger's own caliber over lines 2774 to 7319. The
   closest reconstruction of 3,871 is 3,849, the region minus its 359 comment
   lines, and that is not the ledger's caliber either. The file total 6,718
   re-derives exactly, so the caliber is right and the family figure was wrong.
   The family is 337 lines BIGGER than the record says.
2. `TagAgree` is NOT the smallest of the thirty. It has 26 non-blank lines.
   `EnvOneAgree` has 23 and `ShapedAgree` has 25. `TagAgree` is the third
   smallest.

**`q'` does NOT follow from what exists.** The family's ambient instantiation
supplies one construct at a time. `q'` is the composite at the level-hood
formula, and no term composes the thirty. Section 4 names what is missing.
MEASURED, as to the absent composite.

**`[LJ-1.7]` has a priced route for the first time.** The price is in section 3.

## 1. WHAT `TagAgree` IS

`TagAgree` sits at `src/L/Condensation.lagda.md:6670`. It bridges two codings
of one notion at one carrier. The `At` coding `tagAtL` is the semantic family
from `L.Coding.Model` (`src/L/Coding/Model.lagda.md:585`). The `BS` coding
`tagBS` is the bounded family, defined in the chapter itself at `:1484`. The
module proves both directions between their satisfaction readings, under two
hypotheses that name the tag's value and its membership.

The chapter commits to the class `isL` at three places. Line 71 opens
`hPropStructure 𝒮ʟ`, and `𝒮ʟ = 𝒮ᵥ ↾ isL` at `src/L/Constructible.lagda.md:410`.
Line 73 opens `FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans` as the reading. The
codings come from `L.Coding.Model`, which opens the same class. `[LJ-1.297]`
section 5.2 measured that the commitment is concentrated. My port tests the
claim at one module.

`[LJ-1.238]`'s `GenSequence` shows the target shape. It takes the class and
its eight supplies as parameters and applies `LJ-1-210.GenModel` at them.
`GenModel` is `L.Coding.Model` made class-generic,
`agents/tasks/LJ-1-210/GenModel.agda:12-24`. It already delivers `tagAtL`,
`tagAtL-adequate`, `prAtL` and `prAtL-adequate` at `:340` and `:88`.

## 2. THE RE-INSTANTIATION AND THE DIFF

`agents/tasks/LJ-1-298/GenTagAgree.agda` holds the port. The file takes
`GenModel`'s eight parameters, applies `GenModel` at them, and opens the
restricted structure and the `Single` reading exactly as `GenModel` does.
Below a marker comment it carries three blocks copied from the chapter.

| block | source lines | non-blank lines |
|---|---|---:|
| `PairIs` | `:6666-6669` | 3 |
| `tagBS` | `:1484-1487` | 4 |
| `TagAgree` | `:6670-6697` | 26 |
| total | | 33 |

The diff command and its output are the measurement:

```text
$ diff <original blocks> <ported region>
8a9
> (one blank line)
```

No non-blank line differs. **The changed-line count is 0 of 33.** MEASURED.

Two edits were needed to make the file load, and both sit in the scaffolding,
not the body. `import FOL.Absoluteness` was missing, exit 42, and one import
of a nonexistent cubical module was removed. Neither touched the ported text.
The passing run elaborates the module with `GenModel`'s interface cached, so
1.29 s prices my module's 90 non-blank lines, at 0.039 s per line.

`agents/tasks/LJ-1-298/ProbeLJ1298Amb.agda` then applies the generic module at
the ambient class. It uses `P1297A.Full` and `Full-tr`
(`agents/tasks/LJ-1-297/ProbeLJ1297A.agda:59-63`) and the numeral, pair and
successor supplies in probe D's shape
(`agents/tasks/LJ-1-297/ProbeLJ1297D.agda:44-50`). It moves both directions to
`A.ambient` through `absFull`. `Check.out-amb` and `Check.back-amb` are the
ambient-reading statements, and both typecheck. MEASURED.

## 3. THE EXTRAPOLATION, WITH ITS BASIS (DD8)

**Basis: this probe, plus two sweeps over the chapter.** The sweeps are
measured counts. The per-line rate is measured at one site only.

**What ports at the measured rate.** A sweep for committed-family names inside
the family region finds **23 of 30 modules clean**: their text names nothing
outside `GenModel`'s deliveries, the chapter's own `*BS` syntax and the
chapter's own pre-family helpers. Those 23 modules total 3,511 of the family's
4,208 lines. `TagAgree` is one of them. My probe measured 0 changed lines at
the one site. **INFERRED: the other 22 port at the same rate.** The inference
is from one site, and C-42 binds me to say so.

**What resists, and by how much.** Seven modules name committed formulas:
`DomainAgree`, `WitnessAgree`, `KeyAgree`, `EnvOneAgree`, `DefinesAgree`,
`SatGraphAgree` and `LeafAgree`, 697 lines. The named formulas are pure syntax
over `GenModel` primitives, and their re-statements are short: `keyArityAtL`
is one line at `src/L/Coding/CodeSet.lagda.md:136`, `hasWitnessAt` is three at
`:240`, `twelveAt` is eleven at `src/L/Coding/Graph.lagda.md:94`,
`satGraphAt` is about sixteen around `:104` and `:204`, and the `DefBody`,
`envOneAt`, `DefinesAt`, `isCodeAt` group is about twelve lines, already
re-stated once at `agents/tasks/LJ-1-210/GenPowerset.agda:64-177`. Two gaps
are larger. `GenModel` stops before `L.Coding.Model`'s clause region, 374
in-fence non-blank lines from `:1735`, of which the clause FORMULAS are the
needed part. `L.Coding.Shape` is unported, 354 lines, of which the `shapes`
syntax at `:99-104` and `:182-191` is the needed part, about 40 lines.

**The closure.** The family's proofs use 58 names defined in the chapter
before line 2774, spanning lines 100 to 2773. That region is about 2,674
in-fence non-blank lines. A whole-chapter port carries it. `L.BoundedSubset`
imports `DefBodyB` and `module GraphB` from `L.Condensation` at its `:30-33`,
so `φ₀`'s own ingredients sit inside this closure. MEASURED, by import.

**ONE number (DD8).** A whole-family generic port costs about **180 lines of
new hand-written code**: 38 of scaffolding, about 145 of formula re-statements
and gap syntax. It places about **6,900 lines whole-chapter**, 4,208 of family
plus the 2,674-line closure region, nearly all verbatim copy at the measured
0-changed rate. At the probe's 0.039 s per ported line, the check price
projects to about 300 s. **Basis: this probe for the rate, the sweeps and gap
counts for the volume.** The record's projection said chapter-scale by volume
and mechanical per line. Both halves now carry a measurement. The volume is 8
percent larger than the record said, and the family is about 27 times
`[LJ-1.238]`'s 157-line port, or about 44 times with the closure.

## 4. DOES `q'` FOLLOW

**It does not follow from the ambient instantiation of `TagAgree`.** One
construct of thirty bridges one small coding. MEASURED, by the module's
statement.

**It does not follow from the whole family either, and here is what is
missing.**

1. **The composite term does not exist.** `src/L/Condensation.lagda.md` ends
   at line 7319 with `LeafAgree`'s closing fence. No theorem composes the
   thirty into a bridge at any formula. MEASURED, by reading the file's end.
2. **The dirty seven carry hypothesis telescopes.** `SatGraphAgree` alone
   takes `twelve-out`, `twelve-back`, `codesK`, `unCodesK`, `closedEntryK`,
   `domEntryK`, `domK` and `witK` as parameters, at `:6844-6900`. At the
   ambient carrier somebody must SUPPLY them. Nobody has measured that cost.
   It is the exact analogue of the six readings `[LJ-1.297]` supplied for
   `GenSequence`, and my probe did not touch it. INFERRED, that it is payable.
3. **The kinship is identity, which helps.** `q'`'s `embed φ₀` side is built
   from `DefBodyB` and `module GraphB`, which `L.BoundedSubset` imports FROM
   `L.Condensation` at `:30-33`. So the family bridges `φ₀`'s own ingredients,
   and the composite does not need a translation between two BS dialects.
   MEASURED, by import. `q'`'s other side `LsetGraphAt` is already class-generic
   through `GenSequence`. MEASURED, by `[LJ-1.238]`.

**So the honest form of the route:** port the family and its closure generic,
instantiate at `Full`, supply the dirty seven's telescopes, then write the
composite at `embed φ₀` against `LsetGraphAt`. The first two steps are priced
in section 3. The last two are unpriced, and the composite is where I would
send the next probe.

## 5. IS `TagAgree` REPRESENTATIVE

**By size, it sits at the easy end.** It is the third smallest of thirty, 26
lines against a median near 90. MEASURED.

**By dependency shape, it represents the many.** 23 of 30 modules, 83 percent
of the family's lines, share its shape: no committed name, body over
`GenModel` primitives and chapter-local syntax. MEASURED, by the sweep.

**It does NOT represent the dirty seven.** Those need the clause region, the
`shapes` syntax and the formula re-statements of section 3, and their
hypothesis telescopes are the port's real unknown. If one more module is
measured, measure `SatGraphAgree`: 254 lines, the dirtiest telescope, and the
module closest to `q'`'s graph side.

## 6. DD4, WITH THE AXIS NAMED

**My axis: the port's L-against-ambient axis.** The carrier is the subject
here, not a label. `amb` reads one formula at two carriers, and the `Agree`
family is the machinery that makes the two readings agree.

**Writing the family generic pays the same way `GenSequence` paid, and my
probe is the first payment evidence at this family.** Because the generic form
exists, the ambient instance of `TagAgree` cost one module application and two
transports, about 30 lines in `ProbeLJ1298Amb.agda`, against a re-derivation
of the construct from scratch. MEASURED, at one construct. The bet at 30 times
the size is the same bet: about 180 lines of hand-written generic code buys
the family at BOTH carriers, and the second carrier costs an application. The
one-site caveat of section 3 binds this paragraph.

**The shared object grows.** The generic family is one object serving the L
proof and the ambient proof, which is DD4's first end. The second end, the
AC-against-GCH share, gains nothing from this port directly. I say so rather
than stretch the axis.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| any of the 33 ported lines changed | **MEASURED FALSE.** `diff` reports one blank line added, nothing else |
| the port needs a proof edit inside `TagAgree` | **MEASURED FALSE.** Exit 0 with the body verbatim, `GenTagAgree.agda` |
| the ambient class fails to supply the eight parameters | **MEASURED FALSE.** `ProbeLJ1298Amb.agda`, exit 0 |
| the generic reading differs from `absFull`'s reading | **MEASURED FALSE.** `toAmb` and `fromAmb` typecheck through it |
| the family is 3,871 lines | **MEASURED FALSE.** 4,208 by the ledger caliber over the same span |
| `TagAgree` is the smallest of the thirty | **MEASURED FALSE.** Third smallest, 26 against 23 and 25 |
| the other 22 clean modules port verbatim | **INFERRED.** One site measured, C-42 |
| the pre-family closure ports verbatim | **INFERRED.** Not tested by this probe |
| `q'` follows from the ambient family instantiation | **MEASURED FALSE.** No composite term exists, the chapter ends at `LeafAgree` |
| the dirty seven's telescopes supply at `Full` | **INFERRED.** Not attempted |
| Devlin needs `q'` | **MEASURED FALSE.** Section 9 |
| a probe under `src/` was written | **MEASURED FALSE.** Both files sit in `agents/tasks/LJ-1-298/` |

## 8. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-297/lj-1.297-report.md`, read WHOLE, FIRST, as the brief
  orders. **Line read:** section 5.2, "Re-instantiate ONE delivered `Agree`
  module with the class as a parameter, and diff it. Nobody has run it." TOOK
  the task, the family's span, and the projection this probe prices.
- `agents/tasks/LJ-1-297/ProbeLJ1297D.agda`, read WHOLE. **Line read:** `:47-50`,
  the ambient application of `GenSequence` at `Full`. TOOK the supply shape my
  ambient probe reuses.
- `agents/tasks/LJ-1-297/ProbeLJ1297C.agda`, read `:78-90`. **Line read:**
  `absFull (∧̇ φ ψ) δ = cong₂ _⊓_ ...`. TOOK the transport my `toAmb` and
  `fromAmb` spend.
- `agents/tasks/LJ-1-297/ProbeLJ1297A.agda`, read `:57-63`. **Line read:**
  `Full-tr h k = tt*`. TOOK the ambient class and its transitivity.
- `agents/tasks/LJ-1-238/GenSequence.agda`, read `:1-75`. **Line read:** `:33`,
  `module GM = LJ-1-210.GenModel {ℓ} M M-trans ...`. TOOK the generic-port
  shape `GenTagAgree` copies.
- `agents/tasks/LJ-1-224/lj-1.224-report.md`, read `:1-60` and grepped.
  **Line read:** `:28`, "8 lines differ out of 338 non-blank". TOOK the
  carrier-substitution comparable, which my 0-of-33 sharpens for the
  generic route.
- `agents/tasks/LJ-1-210/GenModel.agda`, read `:1-75` and grepped for
  coverage. **Line read:** `:340`, `tagAtL : ∀ {n} → Fin n → ℕ → Fin n →
  Formula S n`. TOOK the generic codings the port consumes, and the coverage
  boundary of section 3.
- `agents/tasks/LJ-1-210/GenPowerset.agda`, read `:12-62`. **Line read:**
  `:59`, `module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`. TOOK the
  finding that this port is NOT class-generic, which sizes the dirty seven's
  gaps.
- `archive/dev/TASKS-archived.md`, read `:60-75`. **Line read:** the `L3.32-T33`
  row, "Condensation crossing | DELIVERED". TOOK SHAPE only: the retired route
  carried its own crossing, and no content transfers. No archived row moves a
  figure in this report.

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-115` and `:370-392`.

**Is `q'` the port's own artifact, as `q` was? YES. INFERRED, from the same
site `[LJ-1.297]` used.** `:93-97` quotes Devlin's 2.7: one Σ₀ formula Φ and
its ℒ-analogue φ, bridged by 1.9.15. Devlin states one coding of level-hood
and moves its satisfaction between carriers. He never asks two codings of one
notion to agree, at any carrier.

**The same is true of `q'`, and the digested reason carries over.** `q'`
exists because Bedrock codes level-hood twice: the BoundedSubset certificate
for the erase, and the sequence graph for the read-off. `AmbientStep`'s `go`
spends an equation between the two satisfactions. Row C1 of the digest
(`:374`) names the level-hood formula as PER-TOWER content, and no row of C2
through C6 names a two-coding equation. So the right question stands: why does
the port need both codings at one carrier. My section 4 finding, that `φ₀`'s
ingredients are the chapter's own BS family, makes that question sharper. The
family exists to bridge the two dialects, and `q'` is the bridge's top
instance.

**WHY NOT the other rows.** C3 is probe C's transport, delivered. C4 is the
elementarity transfer, downstream of `amb`. C5, C6, D and G are bookkeeping,
unions and well-order. E, F and A, B are counting, cardinals and collapse.
None prices a two-coding equation.

## 10. WHAT I DID NOT SETTLE

- **The verbatim rate at any module besides `TagAgree`.** One site. The 22
  clean modules are INFERRED, and the pre-family closure is INFERRED.
- **The dirty seven's hypothesis telescopes at the ambient carrier.**
  Unmeasured. `SatGraphAgree` is the module to probe next.
- **The composite term from the family to `q'`.** It does not exist, and I did
  not write it. Its price is not my 180-line figure.
- **Whether `q'` is TRUE.** Neither confirmed nor refuted, as
  `[LJ-1.297]` left it.
- **The check time of the whole ported chapter.** 300 s is a projection from
  0.039 s per line at one site, with dependencies cached.

## 11. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. No heap exhaustion. No invocation near 30 minutes. Load 6.2 to 7.5
with 3 users throughout.

| file | exit | elaboration | reload |
|---|---:|---:|---:|
| `GenTagAgree.agda` | 0 | 1.29 s | 1.60 s |
| `ProbeLJ1298Amb.agda` | 0 | 3.90 s | 2.57 s |

Two failed runs precede the green ones, both in the scaffolding: a missing
`import FOL.Absoluteness`, exit 42, and an import of a nonexistent cubical
module, exit 42. Two more intermediate failures sat in the ambient probe's
scaffolding: a name not in scope for the reading, and a double `{ℓ}`
application. None touched the ported body. `GenModel`'s interface was cached,
so the elaboration times price my modules' own lines.

## 12. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-298/`: the brief, this report,
`GenTagAgree.agda` and `ProbeLJ1298Amb.agda`. `src/` holds no probe of mine,
and I never opened `src/L/Condensation.lagda.md` for writing. I did not touch
`agents/tasks/LJ-1-299/`, `src/Everything.lagda.md`, `dev/ledger.toml`,
`dev/PLAN.md` or `src/L/Choice/Name.lagda.md`. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py --check` and
`scripts/gate/lint-agda.py --check` both pass on my files. No em dash in any
language. `_build/` holds only Agda's own interface files for my two modules,
which Agda wrote, not I.
