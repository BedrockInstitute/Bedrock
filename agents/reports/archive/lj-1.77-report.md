# LJ-1.77: machine-check whether KFacts is uninhabitable

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.77-report.md`.

## 0. THE VERDICT

**THE REFUTATION TYPECHECKS. STOP, per the pre-fixed abort criterion
(D-1).** `KFacts` is uninhabitable, machine-checked.

A location note: the brief cites the `KFacts` record at
`src/L/Condensation.lagda.md:2588`; in this tree the record is at
`:5675-5708`. Line 2588 is inside `UnaryShape`/`BinaryShape`, and the
`:2588-2640` range holds no record. The grep evidence
(`record KFacts` at `:5675`) is what the refutation uses; every other
field citation in this report is against this tree's line numbers.

`arityK-refutes` (`src/ProbeLJ177A.agda:75-78`) derives `⊥` from the
`KFacts.arityK` field type at any `K` and `γ`. `KFacts-refutes`
(`src/ProbeLJ177A.agda:81-87`) derives `⊥` from a value of the whole
`KFacts` record. Both check GREEN at the C-12 cap, one process:

```text
GHCRTS="-A64m -I0 -M8g" agda -i . -i _build/2.8.0/agda/src src/ProbeLJ177A.agda
exit 0, 2.47 s cold probe, warm dependencies, load average 4.99 (4 users)
```

The deciding negative is MEASURED: `KFacts` has no inhabitant.

## 1. THE TERM THAT TYPECHECKS

The record is `KFactsNS.KFacts` at
`src/L/Condensation.lagda.md:5675-5708`. Its `arityK` field
(`:5707-5708`) is:

```text
arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩
```

Let `X = lookup K γ : S` and `N = pairʟ X X : S`, the L-singleton.
`fst N ≡ ⁅ fst X , fst X ⁆ ≡ ⁅ fst X ⁆s` by the delivered
`pairʟ-fst` (`src/L/Axioms/Numerals.lagda.md:127`) and
`pair-singleton` (`src/V/Model.lagda.md:173`). The premise
`⟨ fst X ∈ fst N ⟩` is `X ∈ {X}`, supplied by the hierarchy pairing
axiom (machine-checked as `X∈pair`/`X∈N`,
`src/ProbeLJ177A.agda:66-72`). Then `arityK N X` concludes
`⟨ fst X ∈ fst (lookup K γ) ⟩`, which is `X ∈ X`, and the delivered
`∈-irrefl` (`src/V/Hierarchy.lagda.md:155`) refutes it:

```text
arityK-refutes arityK = ∈-irrefl (fst X) (arityK N X X∈N)
```

The term exists at every `n : ℕ`, every `K : Fin n`, every
`γ : S ^ n`, and every `A`, `N0`..`N11`. The field type is empty at
every environment. `carrierK` (`:5705-5706`) is NOT used by the
refutation and is NOT under suspicion: its premise ties `v` to the
`A`-slot, which is ordinary closure content.

## 2. WHICH FIELDS ARE UNINHABITABLE, AND HOW

| field | line in `Condensation.lagda.md` | status |
|---|---|---|
| `arityK` | `:5707-5708` | **MEASURED UNINHABITABLE** (machine-checked, one step) |
| `pairK` | `:5704` | INFERRED UNINHABITABLE (3-cycle, not machine-checked) |
| `innerK` | `:5702` | INFERRED UNINHABITABLE (same 3-cycle shape) |
| `innerPairK` | `:5703` | INFERRED UNINHABITABLE (same 3-cycle shape) |
| `carrierK` | `:5705-5706` | not under suspicion |

One machine-checked refutation settles the record: since `arityK` is a
field of `KFacts`, `KFacts` has no inhabitant. Per the pre-fixed abort
criterion, the dispatch stops here; `pairK` and the two `inner*` fields
were NOT machine-checked.

The review's own word stands on them (`_build/diag-twelve-row-math.md:
289-305`): `pairK X X` gives `pr X X ∈ X`, and
`X ∈ {X} ∈ pr X X ∈ X` is a membership 3-cycle. The tree delivers no
no-cycle lemma (`rg 'cycle|no-cycle' src/` finds none outside probes),
so a `pairK` refutation would need one written from `regularityV` as an
infinite-descent argument. That is exactly the case the review called
INFERRED (`:475-477`), and it stays INFERRED here.

## 3. THE BLAST RADIUS

Everything that takes `KFacts` or a suspect field type as a parameter
is uninstantiable as stated. All references are in committed masters
under `src/L/`; the probes listed by grep are untracked scaffolding
and are omitted.

### 3a. Masters that take `KFacts` as a parameter

- `ShapesAgree`, `src/L/Condensation.lagda.md:5753` (`f : KFacts`,
  `:5756`)
- `ClosedAgree`, `:6033` (`f : KFacts`, `:6036`)
- `ShapedAgree`, `:6133` (`f : KFacts`, `:6135`)
- `WitnessAgree`, `:6159` (`f : KFacts`, `:6161`)
- `SatGraphAgree`, `:6411` (`f : KFacts`, `:6414`)
- `LeafAgree`, `:6640` (`f : KFacts`, `:6642`)

`SatGraphAgree` and `LeafAgree` are the modules the brief names. Both
are consumers of the `KFacts` record as one parameter
(`:6411-6414`, `:6640-6642`).

### 3b. Masters that take a suspect field TYPE as a parameter

The row-agreement and shape modules in `src/L/Condensation.lagda.md`
take `innerK`, `innerPairK` or `pairK` types directly:

- `BotAgree`, `:2720` (`innerK`, `:2723`)
- `PropAgree`, `:3090` (`innerK`, `:3093`; `pairK`, `:3094`)
- `AndAgree`, `:3336` (`innerK`, `:3339`; `pairK`, `:3340`)
- `OrAgree`, `:3386` (`innerK`, `:3389`; `pairK`, `:3390`)
- `TopAgree`, `:3455` (`innerK`, `:3458`)
- `NegAgree`, `:3520` (`innerK`, `:3523`)
- `ForallAgree`, `:3625` (`innerK`, `:3628`)
- `ExistAgree`, `:3727` (`innerK`, `:3730`)
- `ClauseAgree`, `:3899` (`innerK`, `:3902`)
- `MemAgree`, `:4117` (`innerK`, `:4120`; `pairK`, `:4121`)
- `AllInAgree`, `:4668` (`innerK`, `:4671`; `pairK`, `:4672`)
- `ExInAgree`, `:4788` (`innerK`, `:4791`; `pairK`, `:4792`)
- `ImpAgree`, `:4907` (`innerK`, `:4910`; `pairK`, `:4911`)
- `EqAgree`, `:4998` (`innerK`, `:5001`; `pairK`, `:5002`)
- `UnShapeClosed`, `:5102` (`innerK`, `:5105`)
- `BinShapeClosed`, `:5171` (`innerK`, `:5174`; `pairK`, `:5175`)
- `BinFormAgree`, `:5432` (`innerK`, `:5436`; `pairK`, `:5437`)
- `UnFormAgree`, `:5515` (`innerK`, `:5519`)
- `BinFrameAgree`, `:5883` (`innerK`, `:5886`; `pairK`, `:5887`)
- `UnFrameAgree`, `:5929` (`innerK`, `:5932`)

The `arityK`-type consumers:

- `TmAgree`, `:5323` (`arityK`, `:5330`)
- `BothTmRel`, `:5351` (`arityK`, `:5358`)
- `FstTmRel`, `:5379` (`arityK`, `:5386`)

### 3c. The three new masters

- `L.Condensation.LowerAgree`, `src/L/Condensation/LowerAgree.lagda.md`
  (`innerK`, `:74`; `pairK`, `:75`)
- `L.Condensation.UpperAgree`,
  `src/L/Condensation/UpperAgree.lagda.md` (`innerK`, `:64`;
  `pairK`, `:65`)
- `L.Condensation.TwelveAgree`'s `AbstractFrame`,
  `src/L/Condensation/TwelveAgree.lagda.md` (`innerK`, `:72`;
  `pairK`, `:73`)

`src/Everything.lagda.md:371-373` imports all three.

### 3d. The inherited verdict

Every module above has at least one uninhabitable hypothesis, so none
can ever be instantiated as stated. The `KFacts`-parameter modules
inherit the full record, including the machine-checked `arityK`;
their uninhabitability is MEASURED (from `KFacts-refutes`). The
field-type-parameter modules inherit `innerK`/`pairK`/`innerPairK`/
`arityK`; their uninhabitability is INFERRED (the fields are inferred
uninhabitable, and the modules state them as parameters). No repair
was attempted, per the brief.

## 4. NEGATIVES AND THEIR STATUS

1. `arityK` has an inhabitant: **MEASURED FALSE**. The field type is
   empty at every `K`, `γ`
   (`src/ProbeLJ177A.agda:75-78`). This negative sets the verdict.
2. `KFacts` has an inhabitant: **MEASURED FALSE**. Same refutation,
   stated at the record (`src/ProbeLJ177A.agda:81-87`).
3. `pairK` has an inhabitant: **INFERRED FALSE**. The 3-cycle needs a
   no-cycle lemma the tree does not deliver; not machine-checked. No
   verdict rests on it.
4. `innerK`, `innerPairK` have inhabitants: **INFERRED FALSE**. Same
   status.
5. `carrierK` is uninhabitable: **INFERRED FALSE** is NOT claimed.
   `carrierK` is ordinary closure content, not under suspicion.

## 5. THE DD4 ANSWER UNDER D-29

The `KFacts` record is the L tower's shared site-fact block
(`src/L/Condensation.lagda.md:5672-5674`, the LJ-1.62 content-class
change). The defect is in the shared layer: `arityK` is a field of the
one record, so the record's every consumer inherits it at once
(`dev/LESSONS.md` D-29, `:3242-3284`). The machine-check proves the
defect propagates to at least the six `KFacts`-parameter modules
(section 3a) at every site, MEASURED.

The J tower would have inherited the same record shape. A J-side reuse
of `KFacts`, or of its field types as the three new masters already do
for the L side, would carry the uninhabitable fields into every J
instantiation at once. That consequence is INFERRED. The J tower does
not yet exist in this tree, so nothing was machine-checked there. The
mechanism is D-29's own law, and the L side of the same mechanism is
now measured.

## 6. ARCHIVE USED

- `_build/diag-twelve-row-math.md`, section 4 read WHOLE
  (`:252-370`). TOOK the `arityK` recipe, the `pairK`/`innerK`
  3-cycle argument, and the INFERRED/MEASURED split. Checked, not
  trusted: the `arityK` recipe is now machine-checked; the review's
  `pairK` recipe stays inferred.
- `_build/lj-1.71-report.md`, read WHOLE. TOOK the probe shape, the
  C-12 invocation line, and the tagEq refutation as the pattern to
  repeat.
- `src/ProbeLJ171A.agda`, read WHOLE. TOOK the import set and the
  frame pattern.
- `_build/lj-1.62-report.md`, sections 2-3. TOOK the KFacts
  content-class history.
- `src/V/Hierarchy.lagda.md:130-160`. TOOK `regularityV` (`:139`) and
  `∈-irrefl` (`:155`).
- `dev/LESSONS.md`: C-38, C-35, D-29 read WHOLE (`:3427-3465`,
  `:3200-3242`, `:3242-3284`). TOOK the discharge standard and the
  shared-layer propagation law.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 7. LITERATURE USED

Nothing in the literature bears on this; it is a fact about this
tree's own statements. One line, nothing spent.

## 8. GATES

- `scripts/check-fences.py --check`: clean (87 masters).
- `scripts/lint-agda.py --check src/ProbeLJ177A.agda`: exit 0.
- Probe check: GREEN at the C-12 cap, 2.47 s cold, exit 0, load
  average 4.99 (4 users). The machine is NOT quiet. Every absolute
  figure carries the caveat.
- No `make check`. No `check-ratio`.
- No master was edited. The tree is byte-identical to the start
  (`fc99a58`, clean) apart from this report and the probe, both
  gitignored by design (`_build/`, `src/Probe*.agda`).
