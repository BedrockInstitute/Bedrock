# LJ-1.302 report: the composite over the thirty, typed and priced

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**The composite's TYPE is `q'` itself, it is WRITABLE, and it FEEDS.**

`agents/tasks/LJ-1-302/ProbeLJ1302A.agda`, exit 0, 4.42 s, states and
typechecks, at the ambient carrier, with both sides named by delivered
machinery:

```agda
Composite : Type (ℓ-suc ℓ)
Composite = (γ : Vec A.R.SC 2)
          → ⟨ A.ambient γ (embed P1241.φ₀) ⟩
          → ⟨ A.ambient γ (S.Graph* {2} zero (suc zero)) ⟩
```

`φ₀` is `[LJ-1.241]`'s, the right side is `[LJ-1.238]`'s generic
sequence graph at the ambient class, as `[LJ-1.297]`'s probe D applied
it. **A term of this type discharges `AmbientStep`'s `q'` slot and
`amb` comes out**: the same file's `Fed` module applies
`[LJ-1.244]`'s `AmbientStep` at probe D's six readings and at a
hypothetical `comp : Composite`, and `amb-from-composite = AS.amb`
typechecks. MEASURED.

**A composite over the thirty would have to state exactly this.** `q'`
is not a consequence of the composite; `q'` IS the composite's ambient
instance. The composite decomposes as

```text
q'  =  φ₀-extraction  ∘  graph-stem  ∘  approx-stem  ∘  step-stem
       ∘  leaf-stem ( =  extAt→extAtB/→extAtB  ∘  LeafAgree )
```

and this decomposition is NOT mine alone: `[LJ-1.52]` drew the same one
and PROVED the top of it, in the archive. See section 2.

**ONE DIRTY MODULE IS PRICED.** `DomainAgree`, one of the seven, ports
to the class-generic form with ZERO changed body lines and its two
telescope ties SUPPLY at the ambient carrier as terms, from delivered
lemmas, at a concrete environment: 51 non-blank supply lines,
`ProbeLJ1302B.agda`, exit 0, 3.39 s. MEASURED. Section 3.

**The abort criterion fired on its first branch: the composite's type
is writable and one dirty module is priced. STOP.** `q'` has a shape
and a rate for the first time.

**One correction to the record (C-44), and it is the report's second
finding.** `[LJ-1.298]` measured "the chapter ends at line 7319 with
`LeafAgree`'s closing fence. No theorem composes the thirty". The
verdict stands; the file-end detail was wrong. `LeafAgree`'s fence
closes at `:7244`, and a SUPPLY block follows: `module KValue` at
`:7246-7319`, 68 non-blank lines, building one `KFacts` value (`facts`,
`consed`). It supplies the `KFacts` record and no tie and no theorem at
any formula. MEASURED, by reading `:7244-7319`.

## 1. WHAT THE THIRTY GIVE THE COMPOSITE

Of the five factors in the decomposition, the delivered tree holds two.

- **The leaf-stem exists.** `extAtB→extAt` and `extAt→extAtB` at
  `src/L/Condensation.lagda.md:2511-2529` take the leaf bridge as `fwd`
  and `bwd` parameters, and `LeafAgree.out/back` at `:7231-7241` is
  that bridge (`DefBody` against `DefBodyB`). The sequence coding's own
  leaf `DefAt u w = extAt u (∃̇ ∃̇ (DefBody w))` at
  `src/L/Coding/Powerset.lagda.md:442-443` is BUILT from `DefBody`, so
  the leaf-stem is `extAtB→extAt` fed by `LeafAgree`. MEASURED, by
  reading.
- **The φ₀-extraction is trivial.** `φ₀ = closeN 14 (pins ∧̇ renamed)`
  at `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:146`, fourteen `∃̇` over
  the 16-slot matrix, leaving the value and index slots free. MEASURED,
  by reading.

The other three factors, the stems above the leaf, are absent from
`src/`: no `StepAgree`, `ApproxAgree` or `GraphAgree` module exists in
the delivered tree. `grep -c "^module .*Agree"` over the chapter finds
thirty names and none of the three. `GraphB.`, `ApproxB.`, `StepAtB.`,
`StepB.` have zero consumers outside `src/L/Condensation.lagda.md`; the
chapter's own comment at `:2464-2468` names these modules as the bounded
restatements of the sequence coding's `StepAt`, `ApproxAt`,
`LsetGraphAt`; the only consumer of `GraphB` is `LevelHood` at
`src/L/BoundedSubset.lagda.md:81-111`. MEASURED, by grep.

## 2. THE ARCHIVE ALREADY DREW THIS DECOMPOSITION, AND PROVED ITS TOP

**This is the C-44 finding, and it changes what `q'` costs.**
`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda` holds, at the class
carrier:

- `StepAgree` (`:53-58`), a TYPE: the bounded step implies the machine
  step at the graph environment. A hypothesis, not a term.
- `ApproxAgree` (`:64-68`), a TYPE: the bounded approximation implies
  the machine one. A hypothesis, not a term.
- **`graph-assembly` (`:71-87`), PROVED**: from `StepAgree`,
  `ApproxAgree` and a site-fact bundle, `⟨env ⊨ graphBndAt⟩` gives
  `⟨env ⊨ LsetGraphAt⟩`, through the delivered `LsetGraph-in`.

and `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda` holds `GraphAgree`
(`:48-51`), `matrix-decode` (`:58-76`) and `adeq-decode` (`:85-104`):
from the level-hood matrix's satisfaction, given the graph agreement,
`fst w ≡ Lset (fst γ)`. **That is the composite over the stems, proved
modulo the two stems, at the class carrier, in 2026-08.** The chapter's
comment at `src/L/Condensation.lagda.md:5476` still cites
"`[LJ-1.52]` StepAgree/ApproxAgree/GraphAgree" as the consumers of the
leaf adequacy, in the story-to-machine direction only.

**So the missing work is narrower than "three stem modules".** The
graph-stem's assembly is proved (archived); the leaf-stem is delivered
in `src/`. What no tree, live or archived, holds as a TERM is
`StepAgree` and `ApproxAgree` themselves: the bounded-to-unbounded
conversion at the step and approximation levels. Everything above them
was assembled; everything below them was landed; the two middle links
were parameterized and never discharged. That is the same crossing
`[LJ-1.299]` is approaching from the other side, and the same shape
C-45's sweep found twice on the retired route.

**Status of the archived proofs: ARCHIVED-PROVED, current green
UNKNOWN.** The probes import `L.BoundedSubset`'s `LevelHood0`, which
still lives at `src/L/BoundedSubset.lagda.md:840`, and
`L.Coding.Sequence`'s `LsetGraphAt`/`LsetGraph-in`, which still live at
`src/L/Coding/Sequence.lagda.md:349-354`. I did not re-run the archived
files: they are frozen, and a probe prices THIS setting. INFERRED, that
they still typecheck; nobody has checked.

## 3. THE ONE DIRTY MODULE, PRICED AT THE AMBIENT CARRIER

`DomainAgree` (`src/L/Condensation.lagda.md:6510-6547`, 34 non-blank
lines) is one of the dirty seven, on `SatGraphAgree`'s path
(`SatGraphAgree` instantiates it at `:7063`). Its dirt is `domB`
(`:1746-1753`, 7 non-blank lines), pure syntax over `appAt`.

**The port.** `agents/tasks/LJ-1-302/GenDomainAgree.agda`, exit 0,
1.45 s, 94 non-blank lines: 53 of scaffolding in `[LJ-1.298]`'s
`GenTagAgree` shape and 41 of body copied VERBATIM (`domB` +
`DomainAgree`). A `diff` of the copy against `:1746-1753` and
`:6510-6547` reports zero differing body lines; the only differences
are my two-line marker comment and the chapter's separator comment
after the module. MEASURED. **So the dirty module ports at the same
zero-line rate as the clean `TagAgree`.** The dirt was in the NAME
environment, not the text.

**The supply.** `agents/tasks/LJ-1-302/ProbeLJ1302B.agda`, exit 0,
3.39 s. It applies the port at the ambient class in `ProbeLJ1298Amb`'s
shape, then supplies BOTH telescope ties as TERMS at a concrete ambient
environment `f ∷ d ∷ K ∷ []` with `f := Lset beta`, `d := Lset gam`,
`K := Lset lam`, `beta`, `gam` members of `lam`:

- `domK` (members of `d` land in `K`): one `Lset-mono`
  (`src/L/Constructible.lagda.md:355`). One line.
- `entryK` (pair components of `f`'s members land in `K`): two
  transitivity steps through the Kuratowski pair, `layer-trans` over
  `Lset-layer`, then `Lset-mono`. The pair memberships come from
  `pairing-ax`, moved from its `∈ₛ` statement to `∈` by `∈∈ₛ`. Twenty
  lines with the three shared pair lemmas.

The supply block, with the module application and the two directions
moved to the ambient reading, is 51 non-blank lines. **Nothing in it is
new mathematics**: every ingredient (`pairing-ax`, `∈∈ₛ`, `layer-trans`,
`Lset-layer`, `Lset-mono`) is delivered. The supply is NON-VACUOUS: the
environment's `f` has pairs whenever `beta` is above a pair stage.
MEASURED.

The comparable the brief named, `[LJ-1.297]`'s six readings, cost 20
lines for the transport (`ProbeLJ1297C.agda`) and about 60 for the
supply (`ProbeLJ1297D.agda:71-117`). **The dirty module's tie supply is
the same order: 51 lines, dominated by one shared closure block.**

## 4. THE EXTRAPOLATION TO SEVEN, WITH ITS BASIS (DD8)

**Basis: one module measured here, the module spans counted, the tie
kinds read. The per-module rate is measured at ONE site (C-42).**

My span counts, non-blank, module bodies only (caliber: the ledger's,
cut at the module, so `[LJ-1.298]`'s 697 for the seven becomes 634; its
spans carried the inter-module separators):

| module | span | lines | ties in the telescope |
|---|---|---:|---|
| `DomainAgree` | `:6510-6547` | 34 | `entryK`, `domK` |
| `WitnessAgree` | `:6576-6669` | 90 | `witK`, `wCodesK`, `wUnCodesK`, `wEntryK` |
| `KeyAgree` | `:6699-6747` | 46 | `tagEq1`, `numK1`, `keyValK` |
| `EnvOneAgree` | `:6748-6777` | 23 | `N0eq`, `numK`, `pairK` |
| `DefinesAgree` | `:6778-6843` | 58 | `tagEq0`, `numK0`, `envK`, `defPairK`, `satK` |
| `SatGraphAgree` | `:6844-7106` | 255 | `f : KFacts`, `twelve-out`, `twelve-back`, `codesK`, `unCodesK`, `closedEntryK`, `domEntryK`, `domK`, `witK` |
| `LeafAgree` | `:7107-7243` | 128 | `f : KFacts` and fifteen named ties |

**The ties are ONE debt, not sixteen.** Read together, every tie says
the same thing: the site's codes, pairs, witnesses and members land in
the bound `K`. My measured `domK` and `entryK` are two instances of
that one closure content, and the shared block that proves them
(`x∈pair`, `y∈pair`, `pair∈pr`, `Ltr`, `Lset-mono`, about 20 lines) is
written ONCE and serves every tie of the same shape. `KeyAgree`'s and
`EnvOneAgree`'s tag ties add the numeral side, which `Bound`'s
`num∈λ`/`prʟ∈λ` pattern already fixes (`src/L/Coding/Bound.lagda.md:139-144`)
and `KValue` instantiates at `:7264-7319`. `SatGraphAgree`'s and
`LeafAgree`'s `twelve-out`/`twelve-back` are NOT ties: they are
BS-to-machine readings of the twelve, which the clean family supplies
once it is ported, and `[LJ-1.298]` priced that port at about 180
hand-written lines.

**ONE number (DD8).** The ambient tie supply for the whole dirty seven
costs about **100 lines**: about 20 of shared closure block (MEASURED
here, in `ProbeLJ1302B.agda`), about 10 per module of tie statements
re-spelled at each module's environment, six more times, INFERRED from
the tie columns above and the one measured site. Seconds at the
measured rate: my one module's supply elaborated in 3.39 s with
dependencies cached; the seven together stay inside the minute, INFERRED.

**What this number does NOT cover.** It prices the TIES only. It does
not price `StepAgree` and `ApproxAgree`, which are mathematics, not
site facts: the bounded `∀̇`-closure of the approximation must become
the unbounded one, and the witnesses must survive the change of leaf.
Nobody has priced those, and they are the last unpriced term on `q'`'s
route. DD8 names them as the next widest term.

## 5. DOES `q'` FOLLOW

**Not from what exists. MEASURED, three ways.**

1. The delivered tree holds no composite: the chapter's `Agree` family
   ends at `LeafAgree` (`:7243`), followed only by the `KFacts` supply
   (`:7246-7319`). Section 0's correction.
2. The two stem terms exist nowhere: `StepAgree` and `ApproxAgree` are
   hypotheses in an archived probe (`ProbeLJ152B.agda:53-68`) and
   absent from `src/`. Section 2.
3. My feeding probe makes the residue exact: everything else about
   `amb` is SUPPLIED (`ProbeLJ1302A.agda`'s `Fed`, green), so what
   stands between the tree and `amb` is a term of `Composite`'s type
   and nothing else. MEASURED.

**The route, re-priced by this probe.** Port the family generic
(`[LJ-1.298]`'s about 180 lines, my 0-of-41 confirming at a dirty
module), instantiate at ambient (6 lines, `ProbeLJ1302B.agda`'s shape),
supply the seven's ties (about 100 lines, section 4), build `StepAgree`
and `ApproxAgree` at the generic carrier (UNPRICED, the widest term),
re-land `[LJ-1.52]`'s assembly and decode on today's tree (archived at
`:71-87` and `:58-76`; porting cost unknown, the files are frozen),
then move the result to the ambient reading by `absFull` (2 lines a
direction, `[LJ-1.297]`'s probe C shape). The composite then has
`q'`'s type by construction, and `Fed` shows `amb` falls out.

## 6. DD4, WITH THE AXIS NAMED

**My axis: the port's L-against-ambient axis.** The carrier is the
subject of this port, not a label: `amb` reads one formula at two
carriers, and the `Agree` family is the machinery that makes the two
codings of that formula agree.

**A generic `Agree` family pays the same way `GenSequence` paid, and
the payment is now measured at TWO modules, one clean and one dirty.**
`[LJ-1.298]`: `TagAgree`, 0 of 33 lines changed. This probe:
`DomainAgree`, 0 of 41 lines changed, dirt included. Because the
generic form exists, the ambient instance cost 51 lines including BOTH
ties supplied as terms, against re-deriving the domain agreement at the
ambient carrier from scratch. MEASURED, at two sites. The bet at thirty
times the size is the same bet with one new term of evidence.

**The DD4 share grows twice here.** First end, the two proofs: the
generic `Agree` family is one object serving the L tower's proof and
the ambient proof, and the shared closure block inside my supply
(`x∈pair`, `Ltr`, `Lset-mono`) is carrier-neutral V-level code that
both carriers spend. Second end, AC against GCH: nothing in this probe
touches it, and I say so rather than stretch the axis. INFERRED, that
the second end gains nothing here.

**The archive is DD4's other half on this route.** `[LJ-1.52]`'s
decomposition and assembly are the shared object's top; `[LJ-1.157]`'s
`LeafAgree` port is its bottom. The two middle links were never shared
between any two proofs because they were never built. Writing
`StepAgree` and `ApproxAgree` generic in the class is what would make
the whole bridge one object.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the composite's type is unwritable at the ambient carrier | **MEASURED FALSE.** `Composite` typechecks, `ProbeLJ1302A.agda`, exit 0 |
| a composite term feeds `AmbientStep` and `amb` fails to come out | **MEASURED FALSE.** `Fed.amb-from-composite = AS.amb`, exit 0 |
| a dirty module resists the verbatim generic port | **MEASURED FALSE.** 0 of 41 lines changed, `GenDomainAgree.agda` |
| a dirty module's ties cannot be supplied at the ambient carrier | **MEASURED FALSE at `DomainAgree`.** Both ties are terms, `ProbeLJ1302B.agda`, exit 0 |
| the other six modules' ties supply at the same rate | **INFERRED.** One site measured, C-42 |
| the chapter ends with `LeafAgree`'s fence | **MEASURED FALSE.** `KValue` follows, `:7246-7319` |
| no theorem composes the thirty | **MEASURED, in `src/`.** The archive holds the assembly, section 2 |
| `StepAgree`/`ApproxAgree` exist as terms somewhere | **MEASURED FALSE.** Hypotheses in `ProbeLJ152B.agda:53-68`, absent from `src/`, absent from the live tasks |
| the archived `[LJ-1.52]` probes still typecheck today | **UNKNOWN.** Not re-run; frozen files. Their imports still exist, `INFERRED` green |
| `q'` follows from the thirty as delivered | **MEASURED FALSE.** Section 5 |
| the ambient seconds transfer to a loaded machine | **INFERRED.** Load 3.27 to 5.77, 3 users, during my runs |
| Devlin needs a `q'`-shaped bridge | **MEASURED FALSE.** Section 8 |

## 8. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-115` and `:370-392`.

**Does Devlin need `q'`? NO, and `[LJ-1.297]`'s measurement for `q`
carries to `q'` unchanged.** `:93-97` quotes Devlin's 2.7: one Σ₀
formula Φ(z, v, γ) and its ℒ-analogue φ, bridged by 1.9.15. Devlin
states one coding of level-hood and moves its satisfaction between
carriers. He never asks two codings of one notion to agree, at any
carrier, in either direction.

**The brief's sharper question: why does the port need thirty modules
when Devlin needs none.** Because Bedrock codes level-hood twice: the
BoundedSubset certificate for the erase (`φ₀`'s side, `levelHoodB` at
`src/L/BoundedSubset.lagda.md:108-111`) and the sequence graph for the
read-off (`q'`'s side, `LsetGraphAt` at `src/L/Coding/Sequence.lagda.md:349-354`,
whose two-variable instance `LsetGraph` at `:354` is exactly `q'`'s
right side). Devlin's informal Φ is one coding with no constants; the
machine needs a parameter-free certificate for the elementarity
transfer AND a graph the read-off consumes, and the `Agree` family is
the price of the pair. **This probe's addition: the thirty do not even
finish paying it.** The family bridges the two dialects at the leaf and
the clause; the step and approximation levels, where the two codings
actually differ, were parameterized in 2026-08 and never built. The
port does not need thirty modules; it needs thirty-two.

**WHY NOT the other rows.** C1 is the level-hood formula, PER-TOWER,
`q'`'s subject matter. C3 is Σ₀ absoluteness; `[LJ-1.297]`'s probe C is
its ambient half, delivered, and my `toAmb`/`fromAmb` spend it. C2's
coding analogue is the family itself. C4, the elementarity transfer, is
downstream of `amb`. C5, C6, D, G are bookkeeping, unions, well-order.
E, F, A, B are counting, cardinals, extensionality, collapse. None
prices a two-coding equation at the step level.

## 9. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-298/lj-1.298-report.md`, read WHOLE, FIRST, as the
  brief orders. **Line read:** section 4.1, "The composite term does
  not exist ... MEASURED, by reading the file's end." TOOK the task,
  the family's figures, and the `SatGraphAgree` telescope; CORRECTED
  the file-end detail at my section 0.
- `agents/tasks/LJ-1-298/GenTagAgree.agda`, read WHOLE. **Line read:**
  `:58-59`, the eight-parameter telescope and `module GM =` application.
  TOOK the port scaffold `GenDomainAgree.agda` copies line for line.
- `agents/tasks/LJ-1-297/lj-1.297-report.md`, read WHOLE. **Line read:**
  section 5.1, "the six readings SUPPLY at the ambient carrier ...
  22.81 s". TOOK the supply shape and the comparable my section 3
  prices against.
- `agents/tasks/LJ-1-297/ProbeLJ1297D.agda`, read `:30-131`. **Line
  read:** `:71-82`, the `Supply` module's DefAt-trio telescope. TOOK
  the trio my `CompositeTy` re-uses and the six readings `Fed` spends.
- `agents/tasks/LJ-1-238/lj-1.238-report.md`, read WHOLE. **Line read:**
  section 3, "written (added) 40, removed 12, verbatim 145". TOOK the
  generic-port comparable my 0-of-41 extends to a dirty module.
- `agents/tasks/LJ-1-238/GenSequence.agda`, read `:150-229`. **Line
  read:** `:224`, `renaming (GraphAt to LsetGraphAt ...)`. TOOK the
  identity of `q'`'s right side at the ambient carrier.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`, read WHOLE. **Line
  read:** `:48-51`, `GraphAgree : Type` as "the obligation's unbuilt
  half". TOOK the composite-over-the-stems' archived statement and its
  decode, my section 2.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`, read WHOLE. **Line
  read:** `:71-87`, `graph-assembly`, PROVED from `StepAgree` and
  `ApproxAgree`. TOOK the decomposition this report confirms and the
  two links it leaves unbuilt.
- `agents/tasks/LJ-1-244/ProbeLJ1244A.agda`, read WHOLE. **Line read:**
  `:104-107`, the `q'` slot's type. TOOK the composite's target shape,
  which my `Composite` restates and `Fed` feeds.
- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda`, read `:75-150`. **Line
  read:** `:146`, `φ₀ = closeN 14 (pins ∧̇ renamed)`. TOOK `φ₀`'s
  closure structure, the extraction factor.
- `archive/dev/TASKS-archived.md`, read `:58-75` and grepped. **Line
  read:** the `L3.32-T33` row, "Condensation crossing | DELIVERED". TOOK
  SHAPE only: a crossing was delivered once, under the retired route;
  no figure and no content transfers.

## 10. WHAT I DID NOT SETTLE

- **`StepAgree` and `ApproxAgree`.** Their price is the route's last
  unpriced term. I typed the composite and priced the ties; the stems'
  mathematics (bounded `∀̇` to unbounded, witness survival at the leaf
  change) is untouched.
- **Whether the archived `[LJ-1.52]` files still typecheck.** Not
  re-run. Frozen.
- **The other six dirty modules' supplies.** INFERRED from one site,
  C-42. `SatGraphAgree`'s eight-parameter telescope at `:6852-6900`
  remains the unmeasured big end.
- **Whether `q'` is TRUE.** Neither confirmed nor refuted, as
  `[LJ-1.297]` and `[LJ-1.298]` left it.
- **The `L.Coding.Bound` port.** My tie supply bypassed it with V-level
  lemmas; a generic `Bound` would face the same class commitment
  `GenPowerset` faced (`[LJ-1.213]`, exit 42).

## 11. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. No heap exhaustion. No invocation near 30 minutes. Load 3.27 /
4.22 / 5.54 at the first run, 5.15 / 5.40 / 5.77 at the last, 3 users
throughout. All dependencies' interfaces were cached, so the seconds
price my files' own elaboration.

| file | exit | elaboration | reloads |
|---|---:|---:|---:|
| `GenDomainAgree.agda` | 0 | 1.45 s | 1.08 s, 0.98 s |
| `ProbeLJ1302B.agda` | 0 | 3.39 s | 2.76 s, 2.72 s |
| `ProbeLJ1302A.agda` | 0 | 4.42 s | 2.82 s, 2.80 s |

Six failed runs precede the green ones, all in scaffolding: `squash₁`
not in scope; a duplicated `P184` import; `inl` not in scope;
`GDA.domAt` for `GDA.GM.domAt`; and `pairing-ax`'s `∈ₛ` statement
needing `∈∈ₛ`'s transport. None touched the ported body or the supply's
mathematics.

## 12. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-302/`: this report,
`GenDomainAgree.agda`, `ProbeLJ1302A.agda` and `ProbeLJ1302B.agda`.
`src/` holds no probe of mine; `src/L/Condensation.lagda.md` was read
and copied from, never opened for writing. `agents/tasks/LJ-1-301/` was
not touched. `src/Everything.lagda.md`, `dev/ledger.toml`, `dev/PLAN.md`
and `src/L/Choice/Name.lagda.md` were not touched. No commit, no push,
no `git checkout`, `stash`, `reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py --check` and
`scripts/gate/lint-agda.py --check` were run on my files before this
report was closed; both pass. No em dash in any language. `_build/`
holds only Agda's own interface files for my three modules.
