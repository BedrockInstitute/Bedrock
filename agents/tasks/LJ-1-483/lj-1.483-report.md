# LJ-1.483 report: someEnv where the truncation is actually in scope

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-483/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `someEnv-at-codesK` in
`agents/tasks/LJ-1-483/Probe483.agda`. The type is
`someEnvDef {n} K γ`, at a frame where `codesK` is a module
hypothesis at `src/L/Condensation.lagda.md:2782-2786`. Body from
`SupplyEnv.someEnv`. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.480]` is **GO** on the refutation
(`agents/tasks/LJ-1-480/lj-1.480-report.md:66`). I took the verdict
from its report. I did not inhabit `ar-numeral`. Predecessor
`[LJ-1.473]` is **NO-GO** on `someEnv-gated`
(`agents/tasks/LJ-1-473/lj-1.473-report.md:112`) and **GO** on W3
slot 0 (`:112`). I took the frame from its probe
(`Probe473.agda:61-67`), not from its brief. Predecessor
`[LJ-1.457]` is **GO** (`agents/tasks/LJ-1-457/lj-1.457-report.md:87`).
Audit F1: a predecessor taken as a hypothesis is the report
(`dev/pod/audit-2026-08-20.md:34`).

The brief's ruling is Reading 2. Do not change `someEnvDef` and do
not gate it. If the work forces Reading 1, stop.

## D-10, BEFORE ANY AGDA

`codesK` at `src/L/Condensation.lagda.md:2782-2786`:

```
codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
       → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
         × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

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

`codesK`'s third component is exactly `arNum`'s type:
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` at `:2785` and at
`EnvSupply.lagda.md:418`. The consuming site spends it as `arNum`
at `:2806`.

`codesK` needs two inputs before it yields that triple
(`Condensation.lagda.md:2782-2784`):

1. A code `c` in the class carrier:
   `⟨ fst c ∈ fst (lookup C γ) ⟩`.
2. A shape equation:
   `fst c ≡ pr (fst ar) (pr (# 7) (fst a))`.

`someEnvDef` at `src/L/Condensation/LowerAgree.lagda.md:52-58`
takes three K-memberships and no numeral fact. It does not take
(1) or (2).

At this frame, AbstractFrame's C is `suc (suc zero)` of `γ'`
(`TwelveAgree.lagda.md:494`, `LowerAgree.lagda.md:255`). The
`[LJ-1.473]` pad puts dummy `numeralL 0` in that slot
(`Probe473.agda:62-64`). So (1) has no inhabitant at this frame:
C is `# 0`. (2) is not produced from `someEnvDef`'s arguments.

Those inputs have a source deeper in the chain, at the clause
lambdas: `BotAgree.bot-in` (`Condensation.lagda.md:2801-2806`)
and `PropAgree.back` (`:3505-3515`). They have no source at
`someEnvDef`. The brief says: name them and STOP.

W3 still runs. It measures whether `codesK` can be applied at
this frame at all.

## VERDICT

**STOP.** W3 is GO: `no-code` typechecks
(`Probe483.agda:90-96`, exit 0, median **2.32 s** on three
forced rechecks) and `arNum-from-codesK` typechecks
(`Probe483.agda:109-114`, same runs). The domain of `codesK`
at this frame is empty. The named obligation was not written.
I wrote `review-of-someEnv-at-codesK.md`. The work forces
Reading 1. I did not gate `someEnvDef`. I did not inhabit
`someEnv-at-codesK`.

This does not inhabit the `TFacts` record. It does not supply
`twelve-out` or `twelve-back`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It
does not claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The frame is generic in `KValue`'s bound `lam` and stage `gam`.
`n = 9` is the layout integer from `[LJ-1.457]`. C as
`suc (suc zero)` is AbstractFrame's index, not a fixed
mathematical carrier. One copy. No band, no numeral-as-carrier,
and no site is named as a fixed form of `someEnv`. There is no
conflict with W2. The stop is the missing domain of `codesK`,
not a fixed-form rewrite.

W4 does not fire: no module was retired.

P-l did not fire: the types name `lookup` of `Kenv'` and
`numeralL`. They do not name a transparent `sucV`-chain of a
stage.

D-26 did not fire: this is a source check for `codesK`'s
domain, not a well-founded key.

## 2. W3: arNum from codesK, first

**GO** on the two named terms. The widest unmeasured term was
whether `codesK` can be applied at this frame at all. The
brief wrote the closed type

```
arNum-from-codesK : ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

That type has no `ar` in the frame. The derived form, from
`codesK` alone, is

```
arNum-from-codesK :
    (c ar a : S)
  → ⟨ fst c ∈ fst (lookup C Kenv') ⟩
  → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
arNum-from-codesK c ar a c∈ shEq = codesK c ar a c∈ shEq .snd .snd
```

at `Probe483.agda:109-114`, inside `module W3.FromCodes`.
The body is the third projection. `codesK` is a module
hypothesis at the type `Condensation.lagda.md:2782-2786`
delivers, instantiated at this frame's `C = suc (suc zero)`
and `Krow = suc^6 iK'` (`:79-84`, `:100-106`).

The two extra arguments are exactly the two inputs D-10
named. They have no source at `someEnvDef`. At this pad they
have no inhabitant: `C-slot` is `refl` (`:86-87`), so C is
`numeralL 0`, and `no-code` (`:90-96`) sends every
C-membership to `Empty.⊥` by `∅-empty` after `numeralL-fst
zero`. The closed truncation is not inhabited. The
projection is the type match. The empty domain is why
`codesK` cannot be applied at this frame.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-483/Probe483.agdai`).

First landing: 3.01 s, peak RSS 569393152 bytes, exit 0, printed
`Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 2.28 | 605044736 |
| `runs/w3-3.out` / `w3-3.time` | 2.37 | 573358080 |
| `runs/w3-4.out` / `w3-4.time` | 2.32 | 595394560 |

Median wall **2.32 s**. Median peak RSS **595394560 bytes**. No
heap event.

**61** non-blank non-comment lines in the probe.
`module W3` is 39 of those. `no-code` is 7. `arNum-from-codesK`
is 6. The estimate was about 15 lines and under 20 seconds.
Measured, the named terms are that size and in that second.
Nothing is funded against the estimate. Nothing is funded
against `[LJ-1.473]`'s 1.81 s: that measurement was slot 0,
not the C slot.

## 3. The obligation

`someEnv-at-codesK` was not written. The type `someEnvDef {9}
iK' Kenv'` forms. The body cannot come from
`SupplyEnv.someEnv` at this frame, because `arNum` is the
third component of `codesK` and `codesK` cannot be applied:
its domain is empty (`no-code`) and `someEnvDef` does not
take `c∈` or `shEq`. Putting those on `someEnvDef` is
Reading 1. The brief forbids it. The work forces it. STOP.

I did not add a hole. I did not postulate. I did not inhabit
the other 27 fields. I did not write a `TFacts` record. I
did not import a probe. I did not re-derive the layout
arithmetic. I did not apply `SupplyEnv.someEnv`. I did not
transport the four-slot `envSetB` onto `envHypB2`.

The shape that resisted was the domain of `codesK` at
`someEnvDef`, not the type match of the third component.
The third component is `arNum`. The two inputs that produce
it are not in the field.

The full file is W3: the obligation was omitted. First
landing of that file: 2.16 s, peak RSS 605044736 bytes,
exit 0, printed `Checking`. `runs/full-1.out` / `full-1.time`.

Three forced rechecks of the full file, interface deleted
each time, same caliber, one Agda process, exit 0 every time:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 2.17 | 605028352 |
| `runs/full-3.out` / `full-3.time` | 2.48 | 507510784 |
| `runs/full-4.out` / `full-4.time` | 2.60 | 605028352 |

Median wall **2.48 s**. Median peak RSS **605028352 bytes**. No
heap event.

The brief's estimate was about 180 lines, of which the
obligation was about 55, comparables of SHAPE. Measured, the
file is 61 lines because the obligation was not written.
Nothing is funded against the estimate.

## WHERE THE FIELD LIVES

`someEnv` is inhabitable at the clause lambda, not at the
field and not at this pad.

**Not inhabitable**, at `file:line`:

- `TFacts.someEnv` at `src/L/Condensation/TwelveAgree.lagda.md:289`.
  The field is `someEnvDef {n} K γ'`. No `codesK`, no `c∈`,
  no `shEq`.
- `LFacts.someEnv` at `src/L/Condensation/LowerAgree.lagda.md:218`.
  The same type.
- `someEnvDef` itself at `LowerAgree.lagda.md:52-58`. Three
  memberships, no numeral fact, no C-membership, no shape
  equation.
- This pad, `Probe483.agda:70-73`. Slot 2 is dummy
  `numeralL 0`. AbstractFrame's C is that slot
  (`TwelveAgree.lagda.md:494`, `LowerAgree.lagda.md:255`,
  `LFacts.codesK` at `LowerAgree.lagda.md:116`). `no-code`
  (`Probe483.agda:90-96`) refutes every C-membership.

**Inhabitable**, at `file:line`, as a local, not as the field:

- `PropAgree.back` at `src/L/Condensation.lagda.md:3505-3515`.
  `arNum` is bound at `:3509` from binary `codesK`. `someEnv`
  is called at `:3515` with `yaK ycK arK` and without
  `arNum`. Inlining `SupplyEnv.someEnv` there, feeding
  `:3509`, would inhabit the call. It would not inhabit
  `someEnvDef`.
- `BotAgree.bot-in` at `:2801-2806` spends `arNum` from
  unary `codesK`. BotAgree does not take `someEnv`. The
  brief named this site as the consumer of the truncation.
  It is not a consumer of the field.

`TwelveAgree.AbstractFrame` cannot reach the first inhabitable
site. It takes `TFacts` as a whole
(`TwelveAgree.lagda.md:337-343`). `someEnv` is one field of
that record (`:289`). A local at `PropAgree.back:3515` is
not a field. If the field is inhabitable only under `codesK`
plus `c∈` plus `shEq`, `TFacts` may need splitting. The
split type, named and not written:

```
someEnvDef-at-codesK :
    {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n))
    (C : Fin (11 + n))
  → (c ar a : S)
  → ⟨ fst c ∈ fst (lookup C γ) ⟩
  → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
  → (ya yc b : S)
  → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
      × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
            envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)
```

That type is Reading 1: `someEnvDef` gated by `c∈` and
`shEq`. I did not inhabit it. I did not add it to `TFacts`.

## 5. WHAT IS LEFT

The obligation `someEnv-at-codesK` at `someEnvDef {9}` with
`codesK` as a hypothesis and the carrier in slot 0. This
task did not inhabit it.

The two inputs of `codesK` still have no source at
`someEnvDef`. They have a source at `PropAgree.back:3505-3515`.
Sibling `TFacts` fields already take the truncation
(`envK-mem` at `TwelveAgree.lagda.md:186-187`).
`TFacts.someEnv` does not (`:289`).

`SupplyEnv.someEnv` (`EnvSupply.lagda.md:417-444`) is the
delivered constructor. It is still not transported onto
`someEnvDef`. The 4-to-27 reindex from
`E ∷ ar ∷ B₀ ∷ level ∷ []` onto `envHypB2` is unmeasured.

Slot 2 of the pad is still dummy `numeralL 0`. A code class
in that slot is a different brief. It is not this pad.

The other 27 `TFacts` fields. This task did not inhabit them.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:527-537`) still need a `TFacts` value at
a real `K`. `SatGraphAgree` still leaves those two parameters
unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

A next brief that wants the `TFacts` record itself must name
that record. This task was forbidden to build it.

## 6. C-42

This return is a STOP at one site: the two inputs of
`codesK` at `Condensation.lagda.md:2782-2784`, against
`someEnvDef` at `LowerAgree.lagda.md:52-58`. It says those
inputs have no source at this frame. It does not measure how
many other sites carry the same missing domain.

COUNT of `someEnvDef` in `src/`: **5** raw, **3** typed.
Raw: `LowerAgree.lagda.md:52`, `:53`; `:218`;
`TwelveAgree.lagda.md:33`, `:289`. Typed sites, where the
identifier carries a type: `:52`, `:218`, `:289`. None of the
five takes `c∈` or `shEq`. None takes the truncation. In
`archive/src/`: **0**.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes the truncation at `:418`.

COUNT of the ungated `someEnv` parameter (three memberships,
no truncation, not via `someEnvDef`) in `src/`: **3**,
`Condensation.lagda.md:3317`, `:3569`, `:3624`. One call that
throws `arNum` away: `:3515`. A cure of `TFacts.someEnv` is
not a measured cure of these three.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. It takes neither `codesK` nor a
code class.

COUNT of the truncation string
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` in `src/`: **87**.
`Condensation.lagda.md` 50, `LowerAgree.lagda.md` 8,
`UpperAgree.lagda.md` 8, `TwelveAgree.lagda.md` 11,
`EnvSupply.lagda.md` 10. In `archive/src/`: **0**. Every one of
the 87 is a hypothesis or a conjunct of `codesK`, not a
consequence of membership in `K`.

COUNT of `codesK c ar` applications in `src/`: **21**, all in
`Condensation.lagda.md`. None of them is inside `someEnvDef`.
The one `someEnv` call that sits next to such an application
and does not pass `arNum` is `:3515`.

A cure of `TFacts.someEnv` at this site is not a measured
cure of `LFacts.someEnv`. It is not a measured cure of the
87 truncation hypotheses. It is not a measured cure of the
3 ungated `someEnv` parameters. It is not a measured cure of
the 4-to-27 transport. It is not a measured cure of a code
class in slot 2.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on whether `codesK` applies at this frame.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit `someEnvDef` at a frame whose C slot is dummy `# 0`.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The work is a source check for the two inputs of `codesK`, not a truncated witness selection from the literature.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a module hypothesis at `KValue`. It does not consult the orthodox rud digest.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit `someEnv-at-codesK`.
- I did not inhabit the other 27 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not import a probe.
- I did not postulate.
- I did not change `someEnvDef`.
- I did not gate `someEnvDef`.
- I did not apply `SupplyEnv.someEnv`.
- I did not transport.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO. `no-code` is green. `arNum-from-codesK` is green as
the third projection. C at this pad is dummy `# 0`. `codesK`
cannot be applied at `someEnvDef`. That is measured.
`TFacts.someEnv` as stated cannot be inhabited from the
delivered supplier at this frame, even with `codesK` as a
hypothesis. Reading 2 does not inhabit the field. The work
forces Reading 1.

What a next brief can order, one at a time:

1. Reading 1, as a type: `someEnvDef` gated by `c∈` and
   `shEq`, or gated by `arNum` directly. `[LJ-1.463]` named
   the fully gated type
   (`agents/tasks/LJ-1-463/review-of-someEnv-at-K.md:109-118`).
   This brief forbade that gate. Do not fund it against this
   2.32 s. Re-measure it.
2. A local at `PropAgree.back:3515` that feeds `arNum` from
   `:3509` into `SupplyEnv.someEnv`. That is not the
   `TFacts` field. `AbstractFrame` takes `TFacts` as a whole,
   so a local does not close `twelve-out`. Name the split of
   `TFacts` if that is the ruling. Do not fund it against
   this pad.
3. A code class in slot 2 of the pad. `no-code` measures that
   the dummy is empty. Putting a real C there is a different
   frame. Re-measure `codesK` at that frame. Do not fund it
   against this 2.32 s.
4. The 25 closure lemmas. The 250-line hypothesis still stands
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do
   not fund them against this source STOP. C-42 forbids a
   transfer onto them (`dev/LESSONS.md:3752`).
5. A `TFacts` record at this pad, once the other 31 have
   suppliers. This task was forbidden to build that record.
   `TFacts.someEnv` as declared is still the ungated
   `someEnvDef`. `[LJ-1.467]` refuted that form on `ω∈γ`.
   `[LJ-1.473]` named the missing truncation. `[LJ-1.480]`
   refuted the truncation from K-membership. This return
   names the missing domain of `codesK` at the field. Do not
   claim the field from a gated probe.

The condensation front is open for those briefs. It is not open
for a landing in `src/` until a brief names a type that takes
the two inputs of `codesK`, or names a frame whose C slot is
a code class, and names the consumer's two parameters.
