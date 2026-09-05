# LJ-1.476 report: is someEnvDef inhabitable at all, or is the field misstated

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-476/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `ar-numeral` in
`agents/tasks/LJ-1-476/Probe476.agda`. The type is

```
ar-numeral :
    (ar : S) → ⟨ fst ar ∈ fst K ⟩ → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

at `[LJ-1.457]`'s frame, where `K` is that frame's bound slot.
Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.473]` is **NO-GO**, critic-upheld
(`agents/tasks/LJ-1-473/lj-1.473-report.md:114-122`,
`agents/tasks/LJ-1-473/review-of-LJ-1-473-1.md:179`). I took the
verdict from its report and the missing-truncation type from its
probe (`Probe473.agda:99`) and its named gap
(`lj-1.473-report.md:211-220`). I did not inhabit `someEnv-gated`.
Predecessor `[LJ-1.457]` is **GO**
(`agents/tasks/LJ-1-457/lj-1.457-report.md:87-89`). I took the
layout from its probe (`Probe457.agda:52-55`, `:74-75`), not from
its brief. Predecessor `[LJ-1.467]` is **NO-GO**, critic-upheld
(`agents/tasks/LJ-1-467/lj-1.467-report.md:105-113`). I took the
legal instance `lam = ω`, `gam = ∅` from its probe
(`Probe467.agda:83-95`). I did not inhabit a predecessor NO-GO.

## D-10, BEFORE ANY AGDA

`K` at `[LJ-1.457]`'s frame is the bound slot of `KValue`
(`src/L/Condensation.lagda.md:7387-7397`): `lookup iK Kenv` is
`LsetS lam`. At `n = 9` the padded lookup `suc^6 iK'` reads that
same slot. Members of a constructible level are not all numerals.

`someEnvDef` at `src/L/Condensation/LowerAgree.lagda.md:52-58`
takes three memberships and no numeral fact.
`SupplyEnv.someEnv` at `src/L/Coding/EnvSupply.lagda.md:417-418`
takes `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` as `arNum`. `envSetK`
spends `arNum` directly (`:143`). The brief forbids a new
hypothesis and forbids a postulate.

The cheap move is a refutation at one legal instance.

W3 exhibits one member of that slot. The obligation is inhabited
only if that member, and every other, is a numeral.

## VERDICT

**NO-GO.** W3 is GO: `witness` typechecks
(`Probe476.agda:72-74`, exit 0, median **1.85 s** on three
forced rechecks). The bound slot at `lam = ω` contains the
L-pair of two copies of `numeralL 0`. The obligation does not
close. `ar-numeral` is a hole at `Probe476.agda:137`
(`runs/full-4.out`, exit 42, `[UnsolvedInteractionMetas]`,
median **1.88 s** on three forced rechecks). The implication is
FALSE at that witness: `ar-numeral-refute` is
`(∥ Σ[ n ∈ ℕ ] (fst (fst witness) ≡ # n) ∥₁) → Empty.⊥`
(`Probe476.agda:121-124`). The hole is the only error. I did
not inhabit `ar-numeral`. I did not apply `SupplyEnv.someEnv`.
I did not transport.

I wrote `review-of-ar-numeral.md`.

This does not inhabit the `TFacts` record. It does not supply
`twelve-out` or `twelve-back`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It
does not claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The obstruction is generic in `KValue`'s bound `lam`. The
countermodel instantiates that telescope at `lam = ω` and
`gam = ∅`. The pair-is-not-a-numeral fact is one copy, at
`# 0`. No band, no numeral-as-carrier, and no site is named as
a fixed form of `someEnv`. There is no conflict with W2. The
stop is a false implication, not a fixed-form rewrite.

W4 does not fire: no module was retired.

P-l did not fire: the types name `# n` and membership in `K`.
They do not name a transparent `sucV`-chain of a stage.

D-26 did not fire: this is a truth check for a numeral
truncation, not a well-founded key.

## 2. W3: one member of `K`, first

**GO.** The widest unmeasured term was a single member of the
bound slot, because the obligation is true only if every member
is a numeral.

```
witness : Σ[ ar ∈ S ] ⟨ fst ar ∈ fst K ⟩
witness = prʟ (numeralL 0) (numeralL 0)
        , pairK (numeralL 0) (numeralL 0) numK0 numK0
```

at `Probe476.agda:72-74`, inside `module Countermodel` at a
legal `KValue` instance. `module Inst = KValue ω ω-ord succω
∅∈ω ∅ ∅-ord ∅∈ω` (`:63`). `K = lookup Inst.iK Inst.Kenv`
(`:67-68`). `pairK` and `numK0` are `KValue.facts`
(`Condensation.lagda.md:7416,7423`). The member is the L-pair
of two copies of `numeralL 0`.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-476/Probe476.agdai`).

First landing: 1.89 s, peak RSS 571211776 bytes, exit 0, printed
`Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.85 | 571211776 |
| `runs/w3-3.out` / `w3-3.time` | 1.85 | 571211776 |
| `runs/w3-4.out` / `w3-4.time` | 1.86 | 571244544 |

Median wall **1.85 s**. Median peak RSS **571211776 bytes**. No
heap event.

TWO non-blank code lines for `witness` (type plus body). The
estimate was about 8 lines and under 15 seconds. Measured, the
witness is that size and in that second. The instance around it
is copied from `[LJ-1.467]`. Nothing is funded against the
estimate. A pair sits in the bound slot. The obligation cannot
be true at this instance.

## 3. The obligation

`ar-numeral` (`Probe476.agda:133-137`) is the named type at
`Countermodel.K`. The type is written. The body is a hole.
Agda reports `[UnsolvedInteractionMetas]` at
`Probe476.agda:137.14-18` (`runs/full-4.out`, exit 42). The
transport was not attempted.

The refutation at the W3 witness, as a type
(`Probe476.agda:121-124`):

```
ar-numeral-refute :
    (∥ Σ[ n ∈ ℕ ] (fst (fst witness) ≡ # n) ∥₁) → Empty.⊥
```

The body is `pr00≢#` (`:98-113`). `fst (fst witness) ≡ pr (# 0)
(# 0)` by `prʟ-fst` and `numeralL-fst` (`:115-118`). A
Kuratowski pair is not a numeral: `# n` is an ordinal
(`numeral-ord`, `src/L/Ordinal.lagda.md:244`), so transitive,
so `# 0 ∈ pr (# 0) (# 0)`, so `# 0` is `⁅ # 0 ⁆s` or
`⁅ # 0 , # 0 ⁆` by `pairing-ax`, so `# 0 ∈ # 0`, which
`∈-irrefl` forbids (`src/V/Hierarchy.lagda.md:155`).
Classification is copied from `Condensation.lagda.md:2827-2844`.
No nested brace goal.

**82** non-blank non-comment lines in the probe.
`witness` is 2 of those. `ar-numeral-refute` is 4. `pr00≢#` is
16. The brief's estimate was about 120 lines, of which the
obligation or its refutation was about 20, comparables of SHAPE.
Measured, the file is smaller. Nothing is funded against the
estimate.

I did not add a numeral hypothesis. I did not postulate. I did
not inhabit the other 27 fields. I did not write a `TFacts`
record. I did not import a probe. I did not apply
`SupplyEnv.someEnv`. I did not transport. I did not inhabit
`ar-numeral`.

The shape that resisted was the truth of the implication, not
the layout and not slot 0. At `n = 9` the type forms. At a
legal `KValue` instance it is false at one member of `K`.

First landing of the file with the refutation and the hole:
1.88 s, peak RSS 601997312 bytes, exit 42, hole the only error.
`runs/full-1.out` / `full-1.time`.

Three forced rechecks of the file with the hole, interface
deleted each time, same caliber, one Agda process, exit 42
every time, hole the only error:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 1.88 | 601997312 |
| `runs/full-3.out` / `full-3.time` | 2.01 | 601997312 |
| `runs/full-4.out` / `full-4.time` | 1.87 | 601997312 |

Median wall **1.88 s**. Median peak RSS **601997312 bytes**. No
heap event.

## WHAT THE FIELD MUST BECOME

`TFacts.someEnv` as stated cannot be inhabited from the
delivered supplier at this frame. The field is
`someEnv : someEnvDef {n} K γ'`
(`src/L/Condensation/TwelveAgree.lagda.md:289`). `someEnvDef`
takes three memberships and no numeral fact
(`LowerAgree.lagda.md:52-58`). The implication this task
refuted is the missing hypothesis. Two readings, as types.
I do not choose.

Reading 1. The truncation belongs in `someEnvDef`'s own
telescope.

```
someEnvDef-gated :
    {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n)) → Type (ℓ-suc ℓ)
someEnvDef-gated {n} K γ =
  (ya yc b a ar c : S)
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
          envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)
```

Then `TFacts.someEnv` becomes `someEnvDef-gated {n} K γ'`.
Sibling fields already take the truncation this way
(`envK-mem` at `TwelveAgree.lagda.md:186-187`).

Reading 2. `TFacts.someEnv` stays `someEnvDef {n} K γ'` and is
only usable where a consumer already supplies the truncation.
`codesK` at `src/L/Condensation.lagda.md:2785` is such a site:
the truncation is a conjunct of the code, not a consequence of
membership in `K`. The brief named `:279`. That line is
`EraseTransfer`, not the truncation. The measured site is
`:2785`.

Neither reading is this task's call. Both wait on a
mathematical judgement.

## 5. WHAT IS LEFT

The obligation `ar-numeral` at `K = LsetS lam` on
`[LJ-1.457]`'s frame. This task did not inhabit it. The
implication is false at one legal instance.

`SupplyEnv.someEnv` (`EnvSupply.lagda.md:417-444`) is the
delivered constructor. It still takes the truncation. It is
still not transported onto `someEnvDef`. The 4-to-27 reindex
from `E ∷ ar ∷ B₀ ∷ level ∷ []` onto `envHypB2` is unmeasured.

The other 27 `TFacts` fields. This task did not inhabit them.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:527-537`) still need a `TFacts` value at
a real `K`. `SatGraphAgree` still leaves those two parameters
unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

A next brief that wants the `TFacts` record itself must name
that record. This task was forbidden to build it.

## 6. C-42

This return is a refutation of ONE implication at ONE instance:
membership in `KValue`'s bound slot at `lam = ω` does not give
the numeral truncation. It does not refute `someEnvDef`. It
does not refute the truncation as a hypothesis.

COUNT of the false shape
`(ar : S) → ⟨ fst ar ∈ fst K ⟩ → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`
in `src/`: **0**. The tree does not claim this implication.
The supplier takes the truncation. It does not derive it from
membership.

COUNT of the truncation string
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` in `src/`: **87**.
`Condensation.lagda.md` 50, `LowerAgree.lagda.md` 8,
`UpperAgree.lagda.md` 8, `TwelveAgree.lagda.md` 11,
`EnvSupply.lagda.md` 10. Every one of the 87 is a hypothesis
or a conjunct of `codesK`, not a consequence of membership
in `K`.

COUNT of `someEnvDef` in `src/`: **3**.
`LowerAgree.lagda.md:52`, `:218`;
`TwelveAgree.lagda.md:289`. None of the three takes the
truncation.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes the truncation at `:418`.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. It takes neither.

A cure of `TFacts.someEnv` at this site is not a measured
cure of `LFacts.someEnv`. It is not a measured cure of the
87 truncation hypotheses. It is not a measured cure of the
4-to-27 transport.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on the numeral truncation at `KValue`.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit or refute `ar-numeral` at this frame.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The work is a truth check for a numeral truncation at `KValue`, not a truncated witness selection from the literature.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a membership at `KValue`. It does not consult the orthodox rud digest.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit `ar-numeral`.
- I did not inhabit the other 27 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not import a probe.
- I did not postulate.
- I did not add a hypothesis to make `ar-numeral` true.
- I did not apply `SupplyEnv.someEnv`.
- I did not transport `SupplyEnv.someEnv`.
- I did not build `someEnv-gated`.
- I did not choose between the two readings.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO. The bound slot at `lam = ω` contains a pair that is
not a numeral. `ar-numeral` is false at that instance. That is
measured. `TFacts.someEnv` as stated cannot be inhabited from
the delivered supplier at this frame.

What a next brief can order, one at a time:

1. A choice between the two readings in WHAT THE FIELD MUST
   BECOME. That choice is a mathematical judgement. Do not fund
   it against this 1.85 s. Re-measure the chosen type.
2. The 25 closure lemmas. The 250-line hypothesis still stands
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do
   not fund them against this refutation. C-42 forbids a
   transfer onto them (`dev/LESSONS.md:3752`).
3. A `TFacts` record at this pad, once the other 31 have
   suppliers. This task was forbidden to build that record.
   `TFacts.someEnv` as declared is still the ungated
   `someEnvDef`. `[LJ-1.467]` refuted that form on `ω∈γ`.
   `[LJ-1.473]` named the missing truncation. This return
   refutes the implication that would have closed it. Do not
   claim the field from a gated probe.

The condensation front is open for those briefs. It is not open
for a landing in `src/` until a brief names a field that does
not demand a false implication, and names the consumer's two
parameters.
