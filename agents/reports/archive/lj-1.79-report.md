# LJ-1.79: guard the closure facts across the band

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.79-report.md`.

## 0. THE VERDICT

**The whole band is repaired and green.** Every master re-checks at
the C-12 cap, one process. The closure facts in `KFacts` and at every
row are guarded with the memberships of the components their
conclusions mention; `arityK` is bound to the `K` slot by the
transitivity form, and every guarded premise has a named supplier in
the module that uses it. The LJ-1.77 refutation no longer applies:
`src/ProbeLJ177A.agda` no longer typechecks against the repaired
`arityK`, and `src/ProbeLJ179A.agda` documents that failure. Nothing
is wired; `levelIn` and `cover` are untouched.

Measured seconds, warm dependencies, C-12 cap, one process each:

| master | seconds |
|---|---:|
| `src/L/Condensation.lagda.md` | 105.82 s user, 108.20 s wall |
| `src/L/Condensation/LowerAgree.lagda.md` | 21.13 s user, 21.57 s wall |
| `src/L/Condensation/UpperAgree.lagda.md` | 10.80 s user, 11.18 s wall |
| `src/L/Condensation/TwelveAgree.lagda.md` | 22.13 s user, 22.58 s wall |

Load average during the runs: 6.46 to 6.71, four users. The machine
was NOT quiet. Every absolute figure carries that caveat.

## 1. THE GUARDED FORMS

The `KFacts` record
(`src/L/Condensation.lagda.md:5760-5768`) now states the four
suspect facts with the memberships of the components their
conclusions mention:

```agda
innerK     : (k : ℕ) (a : S) → ⟨ fst a ∈ K-slot ⟩ → ⟨ fst (prʟ (numeralL k) a) ∈ K-slot ⟩
innerPairK : (k : ℕ) (a b : S) → ⟨ fst a ∈ K-slot ⟩ → ⟨ fst b ∈ K-slot ⟩
             → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ K-slot ⟩
pairK      : (a b : S) → ⟨ fst a ∈ K-slot ⟩ → ⟨ fst b ∈ K-slot ⟩
             → ⟨ fst (prʟ a b) ∈ K-slot ⟩
arityK     : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ K-slot ⟩
             → ⟨ fst v ∈ K-slot ⟩
```

`carrierK` is unchanged: its premise already tied `v` to the `A`
slot, and it was never under suspicion.

`arityK`'s right form is argued here. The LJ-1.77 refutation
instantiated the old type `(N v : S) → v ∈ N → v ∈ K-slot` at
`N = pairʟ X X`, the L-singleton of `X = lookup K γ`, with the premise
`X ∈ {X}` always true. The conclusion became `X ∈ X`, refuted by
`∈-irrefl`. The repair guards the arity value itself: the premise
`⟨ fst N ∈ K-slot ⟩` ties `N` to the `K` slot the way `carrierK` ties
`v` to the `A` slot. The consumers can supply it because every use of
`arityK` is at a code whose arity component is concluded `∈ K-slot`
by the module's own `codesK`/`compK` fact. The singleton case can
supply no `{X} ∈ K-slot`, so the refutation no longer goes through.

The same guard applies to the row-level `keyK` closure fact
(`(x y : S) → x ∈ K-slot → y ∈ K-slot → prʟ x y ∈ K-slot`), which the
masters supply from `pairK` (`src/L/Condensation/lagda.md:3114`,
`3364`, `3417`, `4246`, `4955`). `keyK` is the same pair closure as
`pairK`; the old code passed `pairK` where `keyK` was expected
(`_build/lj-1.78` did not touch it, and the masters' telescopes have
no separate key fact for these rows).

## 2. THE SUPPLY POINTS

Every guarded premise is supplied at the use site by a fact the
module already has. The witnesses flow from the code-decomposition
facts (`codesK`/`unCodesK`/`compK`), which conclude the arity and
payload memberships from the code's shape.

- **`UnaryShape.in'`/`BinaryShape.in'`** (`:2573`, `:2669`): the
  witness parameters are `a₀K`/`b₀K` at the frame's own `a₀`/`b₀`
  positions. Every row's `back` supplies them from its
  `codesK`/`unCodesK` conclusions: unary rows at `:2758` (Bot),
  `:3525` (Top), `:3608` (Neg), `:3722` (Forall), `:3892` (Exist),
  `:3922` (Clause, through ExistAgree); binary rows at `:3324`
  (Prop), `:4217` (Mem), `:4793` (AllIn), `:4915` (ExIn), `:5015`
  (Imp), `:5110` (Eq).
- **`UnShapeClosed`/`BinShapeClosed`** (`:5141`, `:5212`): the same
  witnesses, supplied by `BinFormAgree`/`UnFormAgree` from `compK`/
  `unCompK` (`:5531-5532`, `:5604`) and by `BinFrameAgree`/
  `UnFrameAgree` from `codesK`/`unCodesK` (`:5980`, `:6025`).
- **`BinFormAgree.relBack`/`relOut`** (`:5490`): the arity's
  K-membership `N ∈ K-slot` is a parameter, supplied by `compK` at
  `:5532`. `BothTmRel`/`FstTmRel` receive it as `hNK` and thread it
  into the guarded `arityK` (`:5414-5426`, `:5444-5452`).
- **`arityK`**: the premise `N ∈ K-slot` is supplied by `compK` in
  `BinFormAgree.out` (`:5532`, `ks .fst`) through `relBack` into
  `BothTmRel.back`/`FstTmRel.back` (`:5414`, `:5424`, `:5444`), and
  by `codesK` in the
  `ShapesAgree`-instantiated rows. No new hypothesis was added.
- **`keyK`**: `PropAgree`'s use sites pass the witnesses from
  `codesK` (`:3304`, `:3336`, `:3339`); `ImpLeaf`'s `yaOut`/`ybOut`
  receive `arK aK`/`arK bK` from `ImpAgree.back` (`:5027-5028`).
- **The six masters** (`ShapesAgree` `:5815`, `ClosedAgree` `:6098`,
  `ShapedAgree` `:6198`, `WitnessAgree` `:6224`, `SatGraphAgree`
  `:6476`, `LeafAgree` `:6705`): they take the guarded `KFacts`
  record and thread its fields into the rows, whose `codesK`/
  `compK` facts supply the witnesses as above.
- **The three new masters** (`LowerAgree.lagda.md:188-224`,
  `UpperAgree.lagda.md:175-213`, `TwelveAgree.lagda.md:72-76`): their
  `innerK`/`pairK` are guarded, and the row instantiations thread the
  witnesses through the lambdas (`LowerAgree` `:188-216`,
  `UpperAgree` `:175-213`). The witnesses are supplied by each row's
  `codesK`, exactly as in the master rows.

No guard's premise is left without a supplier. A guard whose premise
nothing supplied would have moved the defect, not fixed it; the
typecheck of every master above is the machine's confirmation that
each premise is supplied at the use site.

## 3. MODULES REPAIRED AND GREEN

All four files re-check green at the C-12 cap (section 0). The
`L.Condensation` master contains `KFacts`, the twenty row/frame
modules, and the six `KFacts`-consuming masters; the three new
masters are the separate files. `src/ProbeLJ178A.agda` (the LJ-1.78
probe, unmodified) still checks green, confirming the repaired
master is compatible with the probe's guarded shape.

## 4. THE REFUTATION NO LONGER APPLIES

`src/ProbeLJ177A.agda` no longer typechecks. Its `arityK-refutes`
term applies the field as `(N v : S) → v ∈ N → v ∈ K-slot`, but the
repaired field has the extra premise `N ∈ K-slot`. The error is
MEASURED: exit 42, "the inferred type of an application matches the
expected type" failure at `src/ProbeLJ177A.agda:87`.

`src/ProbeLJ179A.agda` documents the repaired type and the missing
premise, and checks GREEN. The distinction is kept: showing that the
refutation no longer applies is NOT exhibiting an inhabitant of
`KFacts`. Constructing a hull-shaped site that supplies all the
guarded facts is the project's own business, not this dispatch's.

## 5. DD4 ANSWER UNDER D-29

**The guarded forms are still generic in the slots.** Every guarded
fact quantifies over `S` and states each membership at the frame's
own `K`-slot (`lookup K γ`), exactly as `carrierK` already did. The
`in'` witness parameters are at the frames' own `a₀`/`b₀` positions
and the frames' `K`-slots. No concrete carrier, set body, or stage
presentation enters any type.

Under D-29 the fix propagates at the same rate the defect did. The
defect lived in the shared `KFacts` record and the shared shape
frames (`UnaryShape`/`BinaryShape`/`UnShapeClosed`/`BinShapeClosed`);
it reached every row and both towers through those shared layers.
The repair lives in the same layers: `KFacts`'s fields, the shape
frames' `in'` signatures, and the row telescopes. The J tower, if it
reuses these layers, inherits the repair rather than the defect. That
inheritance is INFERRED: the J tower does not exist in this tree, so
nothing was machine-checked there.

## 6. NEGATIVES AND THEIR STATUS

1. "The band cannot be repaired mechanically": **MEASURED FALSE**.
   All four files re-check green at the C-12 cap (section 0).
2. "Some site cannot supply its guarded premises": **MEASURED
   FALSE**. Every master typechecks with the guarded signatures, and
   each premise's supplier is named at `file:line` (section 2).
3. "The refutation still applies to the repaired `KFacts`":
   **MEASURED FALSE**. `src/ProbeLJ177A.agda` no longer typechecks
   (section 4).
4. "`arityK`'s guard is unsatisfiable": **NOT CLAIMED**. A guarded
   closure fact is satisfiable at a hull-shaped site (INFERRED from
   the Devlin reading); constructing such a site is not this
   dispatch's business. No verdict rests on it.
5. "`KFacts` is inhabited": **NOT CLAIMED**. Showing the refutation
   no longer applies is not exhibiting an inhabitant. The distinction
   is kept throughout.

## 7. ARCHIVE USED

- `_build/lj-1.78-report.md`, read WHOLE. TOOK the guarded
  `innerK`/`pairK` forms and the supply argument (from `codesK`) that
  this dispatch generalized to the whole band.
- `src/ProbeLJ178A.agda`, read WHOLE. TOOK the explicit-witness
  pattern for the guarded `BinaryShape'.in'` and `MemAgree'.back`
  threading.
- `_build/lj-1.77-report.md`, read WHOLE. TOOK the blast-radius list
  (the work list) and the `arityK` refutation recipe.
- `src/ProbeLJ177A.agda`, read WHOLE. TOOK the refutation term that
  this dispatch's probe shows no longer applies.
- `_build/diag-twelve-row-math.md` section 4, read WHOLE. TOOK the
  K-relativization recipe (the repair is to relativize the unguarded
  quantified variables to K).
- `_build/lj-1.62-report.md` sections 2 and 3. TOOK the `KFacts`
  content-class history.
- `dev/LESSONS.md`: C-38 as extended (`:3427-3520`), C-35
  (`:3200-3242`), D-29 (`:3242-3284`), D-30 (`:3332-3380`), read
  WHOLE. TOOK the discharge standard, the shared-layer propagation
  law, and the price-what-the-consumer-needs rule.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 8. LITERATURE USED

Yes: Devlin's hull is closed under the operations for arguments
already in it (`_build/literature/dev2.txt:1907-1914`, Claim 1). The
guarded form is exactly what the hull gives: the closure facts
require their components in K before concluding the construction in
K.

## 9. GATES

- `scripts/check-fences.py --check`: clean, 87 masters.
- `scripts/lint-agda.py --check` on the four edited files and
  `src/ProbeLJ179A.agda`: exit 0.
- `scripts/lint-prose.py --check` on the same plus this report:
  exit 0.
- `scripts/ledger.py --check`: declaration clean; standing 28,115
  lines over 85 masters.
- Probes: `src/ProbeLJ179A.agda` GREEN; `src/ProbeLJ177A.agda` no
  longer typechecks (exit 42, MEASURED); `src/ProbeLJ178A.agda`
  GREEN.
- No `make check`. No commit, no push.
