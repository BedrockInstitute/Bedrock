# LJ-1.480 report: a pair of numerals is not a numeral

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-480/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `ar-numeral-refuted` in
`agents/tasks/LJ-1-480/Probe480.agda`. The type is

```
ar-numeral-refuted :
    (∥ Σ[ n ∈ ℕ ] (fst (prʟ (numeralL 0) (numeralL 0)) ≡ # n) ∥₁)
  → Empty.⊥
```

at `[LJ-1.457]`'s frame with `lam = ω`, the instance `[LJ-1.476]`
already exhibits. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.476]` is **NO-GO**, critic-upheld
(`agents/tasks/LJ-1-476/lj-1.476-report.md:59`,
`agents/tasks/LJ-1-476/review-of-LJ-1-476-1.md:11`). I took the
verdict from its report. Its W3 is **GO**: `witness` typechecks at
`agents/tasks/LJ-1-476/Probe476.agda:72-74`. I took that type from
the probe that typechecked. I did not inhabit `ar-numeral`. The
brief of this task said to stop if W3 was not GO or the witness was
absent. Neither holds. I proceed.

The brief said `[LJ-1.476]` left the refutation a hole. That is
not what the predecessor delivered. `ar-numeral` is the hole at
`Probe476.agda:137`. The side term `ar-numeral-refute` at
`Probe476.agda:121-124` typechecks; the critic confirmed the hole
was the only error (`review-of-LJ-1-476-1.md:40-43`). This task
re-measures that argument as the named obligation. It does not
transfer the price by analogy.

## D-10, BEFORE ANY AGDA

`# n` is a von Neumann numeral. `prʟ (numeralL 0) (numeralL 0)` is
a Kuratowski pair. The delivered facts that separate them:

1. `numeralL-fst` at `src/L/Axioms/Numerals.lagda.md:179`:
   `fst (numeralL n) ≡ # n`. The numeral's underlying set is `#`.
2. `prʟ-fst` at `src/L/Coding/Model.lagda.md:329`:
   `fst (prʟ a b) ≡ pr (fst a) (fst b)`. The pair's underlying set
   is the hierarchy Kuratowski pair.
3. `numeral-ord` at `src/L/Ordinal.lagda.md:244`:
   `IsOrd (# n)`. So `# n` is transitive.
4. Pair classification from `pairing-ax` only, copied at
   `src/L/Condensation.lagda.md:2827-2844`.
5. `∈-irrefl` at `src/V/Hierarchy.lagda.md:155`: no set is a
   member of itself.

Together: if `pr (# 0) (# 0) ≡ # n`, transitivity of `# n` puts
`# 0` inside the pair, so `# 0` equals `⁅ # 0 ⁆s` or
`⁅ # 0 , # 0 ⁆`, so `# 0 ∈ # 0`, which `∈-irrefl` forbids.

That is a delivered separating fact. The tree can tell a pair from
a numeral. I do not stop.

## VERDICT

**GO.** W3 is GO: `not-a-numeral` typechecks
(`Probe480.agda:120-123`, exit 0, median **2.43 s** on three
forced rechecks). The obligation `ar-numeral-refuted` typechecks
(`Probe480.agda:129-132`, exit 0, median **2.09 s** on three
forced rechecks). A Kuratowski pair of two copies of
`numeralL 0` is not a numeral. The truncated form is one `PT.rec`
of that fact. I did not inhabit `ar-numeral`. I did not apply
`SupplyEnv.someEnv`. I did not transport. I did not postulate.

The frame is the legal `KValue` instance `lam = ω`, `gam = ∅`
(`Probe480.agda:61`). The witness is rebuilt, not imported
(`Probe480.agda:71-73`): the L-pair sits in the bound slot.

This does not inhabit the `TFacts` record. It does not supply
`twelve-out` or `twelve-back`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It
does not claim a trophy.

I did not write `review-of-ar-numeral-refuted.md`. The obligation
closed.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The separating fact is one copy, `pr00≢#` at the hierarchy pair
`pr (# 0) (# 0)` (`Probe480.agda:97-112`). The L-pair instance is
`fst-pair≡pr00` (`:114-117`), from `prʟ-fst` and `numeralL-fst`.
`not-a-numeral` is that one fact, transported. The `KValue`
telescope is generic. The countermodel instantiates it at
`lam = ω` and `gam = ∅`. No band, no numeral-as-carrier, and no
site is named as a fixed form of `someEnv`. There is no conflict
with W2.

W4 does not fire: no module was retired.

P-l did not fire: the obligation names `# n` and
`prʟ (numeralL 0) (numeralL 0)`. It does not name a transparent
`sucV`-chain of a stage.

D-26 did not fire: this is a truth check for a pair-versus-numeral
equality, not a well-founded key.

## 2. W3: the untruncated separating fact, first

**GO.** The widest unmeasured term was

```
not-a-numeral :
    (n : ℕ) → fst (prʟ (numeralL 0) (numeralL 0)) ≡ # n → Empty.⊥
```

at `Probe480.agda:120-123`. The body is `pr00≢#` after
`fst-pair≡pr00`. Classification is `pairing-ax` only
(`Condensation.lagda.md:2827-2844`). Transitivity is
`numeral-ord n .fst` (`Ordinal.lagda.md:244`). The contradiction
is `∈-irrefl` (`Hierarchy.lagda.md:155`). No nested brace goal.

The frame and the witness sit in `module Countermodel` so the
pair is exhibited as a member of the bound slot. They are not
the W3 term.

```
module Inst = KValue ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω
```

at `Probe480.agda:61`. `K = lookup Inst.iK Inst.Kenv` (`:65-66`).

```
witness : Σ[ ar ∈ S ] ⟨ fst ar ∈ fst K ⟩
witness = prʟ (numeralL 0) (numeralL 0)
        , pairK (numeralL 0) (numeralL 0) numK0 numK0
```

at `Probe480.agda:71-73`. Rebuilt from
`agents/tasks/LJ-1-476/Probe476.agda:72-74`. Not imported.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-480/Probe480.agdai`).

First landing: 2.97 s, peak RSS 609288192 bytes, exit 0, printed
`Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 2.43 | 609402880 |
| `runs/w3-3.out` / `w3-3.time` | 2.36 | 609304576 |
| `runs/w3-4.out` / `w3-4.time` | 2.48 | 609288192 |

Median wall **2.43 s**. Median peak RSS **609304576 bytes**. No
heap event.

`not-a-numeral` is 4 non-blank non-comment lines (`:120-123`).
`pr00≢#` is 16 (`:97-112`). The estimate was about 10 lines and
under 15 seconds. Measured, the named term is 4 lines and in
that second. The classification around it is the 16. Nothing is
funded against the estimate.

## 3. The obligation

`ar-numeral-refuted` (`Probe480.agda:129-132`) is the named type.
The body is `PT.rec Empty.isProp⊥` of `not-a-numeral`. Agda
reports no error (`runs/full-4.out`, exit 0).

**80** non-blank non-comment lines in the probe.
`not-a-numeral` is 4 of those. `ar-numeral-refuted` is 4.
`pr00≢#` is 16. The brief's estimate was about 120 lines, of
which the obligation was about 15, comparables of SHAPE.
Measured, the file is smaller. Nothing is funded against the
estimate.

I did not inhabit `ar-numeral`. I did not add a hypothesis. I
did not postulate. I did not inhabit the other 27 `TFacts`
fields. I did not write a `TFacts` record. I did not import a
probe. I did not apply `SupplyEnv.someEnv`. I did not transport.

The shape that resisted was nothing: the untruncated form closed,
so the truncated form closed. At `lam = ω` the pair in the bound
slot is not a numeral.

First landing of the file with the obligation: 2.25 s, peak RSS
605290496 bytes, exit 0, printed `Checking`.
`runs/full-1.out` / `full-1.time`.

Three forced rechecks of the full file, interface deleted each
time, same caliber, one Agda process, exit 0 every time:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 2.09 | 605306880 |
| `runs/full-3.out` / `full-3.time` | 2.09 | 605306880 |
| `runs/full-4.out` / `full-4.time` | 2.08 | 605306880 |

Median wall **2.09 s**. Median peak RSS **605306880 bytes**. No
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
`EraseTransfer` (`Condensation.lagda.md:277-279`), not the
truncation. The measured site is `:2785`.

Neither reading is this task's call. Both wait on a
mathematical judgement.

## 5. WHAT IS LEFT

The obligation `ar-numeral` at `K = LsetS lam` on
`[LJ-1.457]`'s frame. This task did not inhabit it. The
implication is false at one legal instance. `[LJ-1.476]` left
that hole. This return is the refutation, not a fill of that
hole.

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

This return is a refutation of ONE equality at ONE instance: the
L-pair of two copies of `numeralL 0` is not a numeral, at
`KValue` with `lam = ω`. It does not refute `someEnvDef`. It
does not refute the truncation as a hypothesis.

COUNT of the false shape
`(ar : S) → ⟨ fst ar ∈ fst K ⟩ → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`
in `src/`: **0**. The tree does not claim this implication.
The supplier takes the truncation. It does not derive it from
membership. In `archive/src/`: **0**.

COUNT of that false shape in `agents/tasks/`: **1** typed
attempt, `agents/tasks/LJ-1-115/ProbeLJ1115B.agda:63`,
`numeralise`. It sits inside `module Refute` (`:55`). Its body
cannot inhabit the stated type (`:64`). It is a record of a
failed attempt, not a claim that the implication holds.

COUNT of the pair-versus-numeral type
`(∥ Σ[ n ∈ ℕ ] (fst (prʟ (numeralL 0) (numeralL 0)) ≡ # n) ∥₁) → Empty.⊥`
in `src/`: **0**. In this tree: **2**, this obligation
(`Probe480.agda:129-132`) and the predecessor side term
(`Probe476.agda:121-124`).

COUNT of the truncation string
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` in `src/`: **87**.
`Condensation.lagda.md` 50, `LowerAgree.lagda.md` 8,
`UpperAgree.lagda.md` 8, `TwelveAgree.lagda.md` 11,
`EnvSupply.lagda.md` 10. In `archive/src/`: **0**. Every one of
the 87 is a hypothesis or a conjunct of `codesK`, not a
consequence of membership in `K`.

COUNT of `someEnvDef` in `src/`: **5** raw, **3** typed.
Raw: `LowerAgree.lagda.md:52`, `:53`; `:218`;
`TwelveAgree.lagda.md:33`, `:289`. Typed sites, where the
identifier carries a type: `:52`, `:218`, `:289`. None of the
five takes the truncation.

COUNT of the ungated `someEnv` parameter (three memberships, no
truncation, not via `someEnvDef`) in `src/`: **3**,
`Condensation.lagda.md:3317`, `:3569`, `:3624`. A cure of
`TFacts.someEnv` is not a measured cure of these three.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes the truncation at `:418`.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. It takes neither.

A cure of `TFacts.someEnv` at this site is not a measured
cure of `LFacts.someEnv`. It is not a measured cure of the
87 truncation hypotheses. It is not a measured cure of the
3 ungated `someEnv` parameters. It is not a measured cure of
the 4-to-27 transport.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on whether a pair is a numeral.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit or refute the pair-versus-numeral fact at this frame.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The work is a truth check for a pair-versus-numeral equality, not a truncated witness selection from the literature.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a combinatorial equality at `KValue`. It does not consult the orthodox rud digest.
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
- I did not apply `SupplyEnv.someEnv`.
- I did not transport `SupplyEnv.someEnv`.
- I did not build `someEnv-gated`.
- I did not choose between the two readings.
- I did not write `review-of-ar-numeral-refuted.md`.

## WHAT THE NEXT BRIEF NEEDS

W3 is GO. The bound slot at `lam = ω` contains a pair that is
not a numeral. `ar-numeral-refuted` is green. That is
measured. `TFacts.someEnv` as stated cannot be inhabited from
the delivered supplier at this frame.

What a next brief can order, one at a time:

1. A choice between the two readings in WHAT THE FIELD MUST
   BECOME. That choice is a mathematical judgement. Do not fund
   it against this 2.09 s. Re-measure the chosen type.
2. The 25 closure lemmas. The 250-line hypothesis still stands
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do
   not fund them against this refutation. C-42 forbids a
   transfer onto them (`dev/LESSONS.md:3752`).
3. A `TFacts` record at this pad, once the other 31 have
   suppliers. This task was forbidden to build that record.
   `TFacts.someEnv` as declared is still the ungated
   `someEnvDef`. `[LJ-1.467]` refuted that form on `ω∈γ`.
   `[LJ-1.473]` named the missing truncation. `[LJ-1.476]`
   exhibited the pair in the bound slot. This return writes
   the refutation as the obligation. Do not claim the field
   from a gated probe. Do not fund a sixth attempt at
   `ar-numeral`.

The condensation front is open for those briefs. It is not open
for a landing in `src/` until a brief names a field that does
not demand a false implication, and names the consumer's two
parameters.
