# LJ-1.473 report: the frame with a carrier in slot zero and its side condition stated

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-473/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `someEnv-gated` in
`agents/tasks/LJ-1-473/Probe473.agda`. The type is
`someEnvDef {9} iK' Kenv'`. `someEnvDef` is
`src/L/Condensation/LowerAgree.lagda.md:52-58`. The frame puts
`LsetS gam` in slot 0. The module hypothesis is the type
`SupplyEnv` takes, `⟨ ω ∈ sucV gam ⟩`
(`src/L/Coding/EnvSupply.lagda.md:111`). Body from
`SupplyEnv.someEnv`. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.467]` is **NO-GO**, critic-upheld
(`agents/tasks/LJ-1-467/lj-1.467-report.md:105-113`,
`agents/tasks/LJ-1-467/review-of-LJ-1-467-1.md:203-208`). I took
the verdict from its report and the missing-hypothesis type from
its probe (`Probe467.agda:104-107`): `⟨ ω ∈ sucV gam ⟩`. I did
not inhabit the ungated `someEnv-numeral` that 467 left as a hole
(`Probe467.agda:133`). Predecessor `[LJ-1.457]` is **GO**
(`agents/tasks/LJ-1-457/lj-1.457-report.md:87-89`). I took the
layout from its probe (`Probe457.agda:52-55`, `:74-75`), not from
its brief.

The brief writes the hypothesis as `⟨ ω ∈ˢ fst gam ⟩`. That type
does not form. `_∈ˢ_` is `S → S → Ω`
(`src/FOL/ZFStructure.lagda.md:48-50`). `gam` is `V ℓ`
(`src/L/Condensation.lagda.md:7384`). Audit F1 forbids taking a
brief type over the type a predecessor delivered
(`dev/pod/audit-2026-08-20.md:34-41`). The type I state is
`⟨ ω ∈ sucV gam ⟩`. Audit F3: a predecessor NO-GO is not
inhabited (`:56-60`).

## D-10, BEFORE ANY AGDA

`SupplyEnv.someEnv` at `src/L/Coding/EnvSupply.lagda.md:417-424`:

```
someEnv : (ya yc b a ar c : S)
        → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
        → ⟨ fst ya ∈ Lset lam ⟩
        → ⟨ fst yc ∈ Lset lam ⟩
        → ⟨ fst ar ∈ Lset lam ⟩
        → Σ S (λ E → ⟨ fst E ∈ Lset lam ⟩
            × ⟨ (E ∷ ar ∷ B₀ ∷ level ∷ []) ⊨
                  envSetB zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))) ⟩)
```

Module telescope of `SupplyEnv` at `:107-111` takes the `KValue`
parameters plus `ω∈γ : ⟨ ω ∈ sucV gam ⟩`. `B₀ = LsetS gam ordγ`
(`:124-125`). `level = LsetS lam ordλ` (`:414-415`).

`someEnvDef` at `src/L/Condensation/LowerAgree.lagda.md:52-58`:

```
someEnvDef : {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n)) → Type (ℓ-suc ℓ)
someEnvDef {n} K γ =
  (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)
```

The three hypotheses `[LJ-1.467]` named
(`agents/tasks/LJ-1-467/lj-1.467-report.md:90-97`), and the
source of each at this frame:

1. `ω∈γ : ⟨ ω ∈ sucV gam ⟩`. `SupplyEnv` takes it
   (`EnvSupply.lagda.md:111`). `KValue` does not
   (`Condensation.lagda.md:7380-7384`). `someEnvDef` does not.
   **Source at this frame: a stated module hypothesis.** The
   brief gates this one. `[LJ-1.467]` measured that the ungated
   form is empty at a legal `KValue` instance
   (`Probe467.agda:104-107`).

2. Numeral truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`.
   `SupplyEnv.someEnv` takes it (`EnvSupply.lagda.md:418`).
   `someEnvDef` does not (`LowerAgree.lagda.md:52-58`). `KValue`
   does not. Putting the carrier in slot 0 does not produce it.
   The body uses it at `EK` and at `envInK₀`
   (`EnvSupply.lagda.md:433`, `:439`). **No source at this
   frame.** The brief forbids gating it.

3. Carrier in slot 0. `[LJ-1.457]` put dummy `numeralL 0` there
   (`Probe457.agda:53-54`). The supplier builds at
   `B₀ = LsetS gam` (`EnvSupply.lagda.md:124-125`). `envHypB2`
   reads slot 0 as `B` (`Condensation.lagda.md:654-658`).
   **Source at this frame: the filler.** This brief puts
   `LsetS gam ordγ` in slot 0. That is not a gate. W3 measures
   the equality.

The brief gates ONE of the three. Gating all three would make
the obligation vacuous. Hypothesis 2 has no source. The brief
says: if either of the other two has no source, name it and
STOP. The named gap is the truncation.

W3 still runs. It measures hypothesis 3, which has a source.
The brief says that finding outranks the obligation. I do not
invent a source for the truncation. I do not gate it.

W3 runs first.

## VERDICT

**NO-GO.** W3 is GO: `slot-zero` typechecks by `refl`
(`Probe473.agda:69-70`, exit 0, median **1.81 s** on three
forced rechecks). The carrier sits in slot 0. The layout and
the supplier share that slot. The obligation does not close.
`someEnv-gated` is a hole at `Probe473.agda:99`
(`runs/full-2.out`, exit 42, `[UnsolvedInteractionMetas]`,
median **1.86 s** on three forced rechecks). The truncation
has no source at `someEnvDef`. The brief forbids gating it.
I did not apply `SupplyEnv.someEnv`. I did not transport.

I wrote `review-of-someEnv-gated.md`. I did not inhabit
`someEnv-gated`.

This does not inhabit the `TFacts` record. It does not supply
`twelve-out` or `twelve-back`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It
does not claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The frame is generic in `KValue`'s bound `lam` and stage `gam`.
The gate `ω∈γ : ⟨ ω ∈ sucV gam ⟩` is the same telescope. `n = 9`
is the layout integer from `[LJ-1.457]`. It is not a fixed
mathematical carrier. One copy. No band, no numeral, and no
site is named as a fixed form of `someEnv`. There is no
conflict with W2. The stop is the missing truncation, not a
fixed-form rewrite.

W4 does not fire: no module was retired.

P-l did not fire: `slot-zero` names `lookup zero` of `Kenv'`
and `LsetS gam`. It does not name a transparent `sucV`-chain
of a stage.

D-26 did not fire: this is a source check for a supplier
argument, not a well-founded key.

## 2. W3: carrier in slot 0, first

**GO.** The widest unmeasured term was slot 0, because
`[LJ-1.467]` measured that the dummy is wrong and nobody had
put the carrier there.

```
slot-zero : fst (lookup zero Kenv') ≡ fst (LsetS gam ordγ)
slot-zero = refl
```

at `Probe473.agda:69-70`, inside `module W3` at a real `KValue`
frame. `Kenv'` is `LsetS gam ordγ` in slot 0, then five dummy
`numeralL 0`, then `Kenv` (`:61-64`). The body is `refl`.
`lookup zero` of a cons is the head.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-473/Probe473.agdai`).

First landing: 1.86 s, peak RSS 611172352 bytes, exit 0, printed
`Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.81 | 611139584 |
| `runs/w3-3.out` / `w3-3.time` | 1.81 | 611172352 |
| `runs/w3-4.out` / `w3-4.time` | 1.82 | 611139584 |

Median wall **1.81 s**. Median peak RSS **611139584 bytes**. No
heap event.

**15** non-blank non-comment lines in `module W3` (`:52-70`).
`slot-zero` is two of those. The estimate was about 15 lines
and under 20 seconds. Measured, it is that size and in that
second. Nothing is funded against the estimate. Nothing is
funded against `[LJ-1.457]`'s 2.20 s: that measurement was at
the dummy layout.

`suc^6` reads `Kenv`. Changing slot 0 does not touch the
24-field transfer of `[LJ-1.457]`. The layout and the supplier
can both sit at this frame on slot 0. That finding does not
close the truncation.

## 3. The obligation

`someEnv-gated` (`Probe473.agda:92-99`) is the named type
`someEnvDef {9} iK' (Kenv' ...)`, with `ω∈γ : ⟨ ω ∈ sucV gam ⟩`
in the telescope (`:97`). The type is written. The body is a
hole. Agda reports `[UnsolvedInteractionMetas]` at
`Probe473.agda:99.17-21` (`runs/full-2.out`, exit 42). The
transport was not attempted.

The missing source, as a type
(`review-of-someEnv-gated.md`, section THE MISSING SOURCE):

```
truncation :
    (ar : S)
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK'))))))
                           (Kenv' lam ordλ succλ ∅∈λ gam ordγ γ∈λ)) ⟩
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

`someEnvDef` does not take this. Sibling `TFacts` fields do
(`envK-mem` at `TwelveAgree.lagda.md:186-187`). I did not
inhabit `truncation`. I did not add it to `someEnv-gated`.

**49** non-blank non-comment lines in the probe.
`module W3` is 15 of those. `someEnv-gated` is 8. The brief's
estimate was about 170 lines, of which the obligation was
about 50, comparables of SHAPE. Measured, the file is smaller
because the truncation has no source. Nothing is funded
against the estimate.

I did not add a numeral hypothesis. I did not postulate. I
did not inhabit the other 27 fields. I did not write a
`TFacts` record. I did not import a probe. I did not
re-derive the layout arithmetic. I did not apply
`SupplyEnv.someEnv`. I did not transport the four-slot
`envSetB` onto `envHypB2`.

The shape that resisted was the source of the truncation, not
the layout and not slot 0. At `n = 9` the type forms. At the
carrier-in-slot-0 frame with `ω∈γ` stated, the supplier still
cannot be applied.

One earlier full-file run failed on a dropped `∅` import
after W3 (`runs/full-1.out`, `[NotInScope]`, 1.87 s). It is
not the price.

Three forced rechecks of the file with the hole, interface
deleted each time, same caliber, one Agda process, exit 42
every time, hole the only error:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 1.84 | 605732864 |
| `runs/full-3.out` / `full-3.time` | 1.86 | 605732864 |
| `runs/full-4.out` / `full-4.time` | 1.86 | 605716480 |

Median wall **1.86 s**. Median peak RSS **605732864 bytes**. No
heap event.

## WHAT THE GATE COSTS

A gated `someEnv` is weaker than the field `TFacts` declares.
I do not claim the field.

`TFacts.someEnv` at `src/L/Condensation/TwelveAgree.lagda.md:289`:

```
someEnv : someEnvDef {n} K γ'
```

No `ω∈γ`. No truncation. No constraint on slot 0 of `γ'`.

What this task wrote, as a type (`Probe473.agda:92-98`):

```
someEnv-gated :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
    (ω∈γ : ⟨ ω ∈ sucV gam ⟩)
  → someEnvDef {9} iK' (Kenv' lam ordλ succλ ∅∈λ gam ordγ γ∈λ)
```

The difference is one extra hypothesis, `ω∈γ : ⟨ ω ∈ sucV gam ⟩`.
The carrier in slot 0 is a filler, not a hypothesis. The body
is a hole, so even this weaker type is not inhabited.

Can any consumer discharge `⟨ ω ∈ sucV gam ⟩` at the site it
is spent? No, at the `KValue` site. `KValue` does not take it
(`Condensation.lagda.md:7380-7384`). `SatGraphAgree` does not
take it (`:6961-6976`). `twelve-out` and `twelve-back` do not
take it (`TwelveAgree.lagda.md:527-537`). `BoundedSubsetAt`
takes `α∉ω` (`src/L/BoundedSubset.lagda.md:1385-1387`).
`[LJ-1.252]` inhabits `ω∈sucα` from `α∉ω`
(`ProbeLJ1252A.agda:93-99`). That derivation is not a measured
source at `KValue`. A measured cure does not transfer
(`dev/LESSONS.md:3752`).

## 5. WHAT IS LEFT

The obligation `someEnv-gated` at `someEnvDef {9}` with `ω∈γ`
stated and the carrier in slot 0. This task did not inhabit it.

The truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` still has no
source at `someEnvDef`. Sibling fields already take it
(`envK-mem` at `TwelveAgree.lagda.md:186-187`). `TFacts.someEnv`
does not (`:289`).

`SupplyEnv.someEnv` (`EnvSupply.lagda.md:417-444`) is the
delivered constructor. It is still not transported onto
`someEnvDef`. The 4-to-27 reindex from
`E ∷ ar ∷ B₀ ∷ level ∷ []` onto `envHypB2` is unmeasured.

The other 27 `TFacts` fields. This task did not inhabit them.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:527-537`) still need a `TFacts` value at
a real `K`. `SatGraphAgree` still leaves those two parameters
unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

A next brief that wants the `TFacts` record itself must name
that record. This task was forbidden to build it.

## 6. C-42

This return is a NO-GO at one hypothesis, not a refutation of
`someEnvDef`. The count below is the sweep of the ungated
environment-existence shape and of the truncation on the
supplier, re-measured in `src/` on this dispatch.

COUNT of `someEnvDef` in `src/`: **3**.
`LowerAgree.lagda.md:52`, `:218`;
`TwelveAgree.lagda.md:289`. None of the three takes `ω∈γ`.
None takes the truncation.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes `ω∈γ` at `:111` and the
truncation at `:418`.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. It takes neither.

The pad that puts the carrier in slot 0 is not a measured
cure of the truncation. It is the frame this hypothesis
failed on. A cure of the truncation at this site is not a
measured cure of `LFacts.someEnv` or of `TFacts.someEnv`. It
is not a measured cure of the 4-to-27 transport.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on `someEnv` at the carrier-in-slot-0 frame.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit `someEnvDef {9}` at `Kenv'` with the carrier in slot 0.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The work is a source check for the numeral argument of `SupplyEnv.someEnv`, not a truncated witness selection from the literature.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a module hypothesis and a filler at `KValue`. It does not consult the orthodox rud digest.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit `someEnv-gated`.
- I did not inhabit the other 27 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not import a probe.
- I did not postulate.
- I did not add a numeral hypothesis.
- I did not apply `SupplyEnv.someEnv`.
- I did not attempt the transport.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO. The carrier sits in slot 0 by `refl`. `ω∈γ` is
stated, at the type `SupplyEnv` takes. The type
`someEnvDef {9} iK' Kenv'` forms. The truncation has no
source at `someEnvDef`. That is measured.

What a next brief can order, one at a time:

1. A type that takes the truncation, then the body from
   `SupplyEnv.someEnv` plus the transport onto `envHypB2`.
   `[LJ-1.463]` named the fully gated type
   (`review-of-someEnv-at-K.md:97-118`). This brief gated
   `ω∈γ` and put the carrier in the frame. The remaining
   gate is the truncation. Do not fund it against this
   1.81 s. Re-measure it.
2. The 25 closure lemmas. The 250-line hypothesis still stands
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do
   not fund them against this source NO-GO.
3. A `TFacts` record at this pad, once the other 31 have
   suppliers. This task was forbidden to build that record.
   `TFacts.someEnv` as declared is still the ungated
   `someEnvDef`. `[LJ-1.467]` refuted that form on `ω∈γ`.
   This return names the missing truncation. Do not claim
   the field from a gated probe.

The condensation front is open for those briefs. It is not open
for a landing in `src/` until a brief names a frame that
sources the truncation and the consumer's two parameters.
