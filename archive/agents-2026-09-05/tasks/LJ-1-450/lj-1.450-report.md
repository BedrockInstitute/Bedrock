# LJ-1.450 report: the environment the condensation frame has never been given

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-450/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `someEnv-at-K` in
`agents/tasks/LJ-1-450/Probe450.agda`. The brief names the type
`someEnvDef {3} iK Kenv`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

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

`Kenv` and the fourteen names at `src/L/Condensation.lagda.md:7387-7409`:

```
Kenv : S ^ 14
Kenv = LsetS gam ordγ ∷ LsetS lam ordλ
     ∷ numeralL 0 ∷ numeralL 1 ∷ numeralL 2 ∷ numeralL 3
     ∷ numeralL 4 ∷ numeralL 5 ∷ numeralL 6 ∷ numeralL 7
     ∷ numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ []

iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Fin 14
iA = zero
iK = suc zero
i0 = suc (suc zero)
```

TFacts at `src/L/Condensation/TwelveAgree.lagda.md:129-131` takes
`N0 ... K : Fin (5 + n)` and `γ' : S ^ (11 + n)`, and it reads
`lookup (suc^6 X) γ'` (`:133`).

Two equations, one `n`:

1. Index types meet: `Fin (5 + n) = Fin 14`, so `n = 9`. Then
   `γ : S ^ (11 + 9) = S ^ 20`, and `Kenv : S ^ 14` does not fit.
2. Env lengths meet: `11 + n = 14`, so `n = 3`. Then
   `K : Fin (5 + 3) = Fin 8`, and `iK : Fin 14` does not fit.

No `n` solves both. The brief's type `someEnvDef {3} iK Kenv` asks
for both at once.

At `n = 3`, `lookup (suc^6 K) Kenv` reads positions 6 through 13
(`numeralL 4` through `numeralL 11`). `iK` is position 1
(`LsetS lam ordλ`). `6 + k ≥ 6 > 1`. No `Fin 8` index lands on the
bound.

Predecessor `[LJ-1.113]` at `agents/tasks/LJ-1-113/lj-1.113-report.md:8`
is COMPLETE, not NO-GO. It names `someEnv` as NEEDS NEW CONTENT
(`:52`, row 22) and INFERRED FALSE as a derivation from delivered
machinery (`:207-210`). It does not name the statement FALSE. The
type of `someEnvDef` is live. This task does not inhabit a predecessor
NO-GO.

W3 runs first.

## VERDICT

**NO-GO on `someEnv-at-K`. NO-GO on W3 `frame-sigma`.**

- W3 is `Transfer.frame-sigma` at `Probe450.agda:86-111` (line 83 of
  the W3-only file). The 24 TFacts `tagEq`/`numK` fields at `Kenv`,
  inhabited from `KValue.facts`. Three forced rechecks, exit 42 every
  time, `[UnequalTerms]` at that one site (`runs/w3-{1,2,3}.out`).
  Median wall **2.45 s**. Median peak RSS **640401408 bytes**.
- `someEnv-at-K` is `Probe450.agda:47-48`. Full file, three forced
  rechecks, exit 42 every time, `[UnequalTerms]` `14 != 8` at
  `:47.33-35` (`runs/full-recheck-{1,2,3}.out`). Median wall
  **1.95 s**. Median peak RSS **619020288 bytes**.
- The witness meter reports 1 UNRESOLVED of 1, `probe_red=True`,
  2.10 s (`runs/witness-1.out`). The name is in scope. The probe is
  red by the type of `someEnv-at-K`.
- The obstruction is `review-of-someEnv-at-K.md`. The one type that
  would make the frames meet is `someEnv-padded` there. It is a
  re-layout. This task does not inhabit it.

A GO here would put the first `TFacts` field at a real `K` and give
`[LJ-1.113]`'s 250-line hypothesis one measured member. This return
is not that GO. It does not claim a trophy. `src/Landmarks.lagda.md`
is untouched.

## 1. W2

The W3 record `TagNum` is generic in `KValue`'s parameters `lam` and
`gam`. `someEnvDef` is already generic in `n` and in the `K` slot.
No band, no numeral and no site is named as a fixed carrier. There
is no fixed form to report. The stop is the layout, so no shared
construction was written twice.

W4 does not fire: no module was retired.

## 2. W3: the 24 fields, first

**NO-GO.** The widest unmeasured term was whether the two frames
meet. The brief's `frame-meets` line was not written. The smaller
term is `TagNum` (`Probe450.agda:52-74`) with the twelve `tagEq`
fields and the twelve `numK` fields of TFacts
(`TwelveAgree.lagda.md:133-156`), at `Kenv`, inhabited from
`KValue.facts` (`Condensation.lagda.md:7411-7419`).

`TagNum` takes `Fin 8` indices, which is `Fin (5 + 3)`. That record
typechecks. The inhabitant `frame-sigma` does not.

W3 ran ALONE, with the obligation omitted. Three forced rechecks.
The probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-450/Probe450.agdai`). Caliber
`-A64m -I0 -M8g`, set on the pane, untouched. One Agda process.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` | 2.48 | 640401408 |
| `runs/w3-2.out` | 2.45 | 640401408 |
| `runs/w3-3.out` | 2.14 | 640401408 |

Median wall **2.45 s**. Median peak RSS **640401408 bytes**. No heap
event. Exit 42 every time. The error is
`Probe450.agda:83.18-37` of that W3-only file (`runs/w3-1.out:2-14`):

```
error: [UnequalTerms]
fst (numeralL 0) !=
fst
(lookup N0
 (numeralL 4 ∷
  numeralL 5 ∷
  numeralL 6 ∷
  numeralL 7 ∷
  numeralL 8 ∷ numeralL 9 ∷ numeralL 10 ∷ numeralL 11 ∷ []))
of type V ℓ
when checking that the expression KFacts.tagEq0 facts has type
fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) Kenv) ≡
fst (numeralL 0)
```

`KFacts.tagEq0 facts` is `fst (numeralL 0) ≡ fst (numeralL 0)`.
TFacts's `suc^6` lookup on `Kenv` skips the first six slots
(carrier, bound, numerals 0, 1, 2, 3) and reads `N0` in the tail
that starts at `numeralL 4`. The 24 fields that `KFacts` already has
do not transfer. The break is the LAYOUT.

A prior discarded run (`runs/w3-first.out:2-4`) measured the index
types alone: `iK` against `Fin 8`, `14 != 8`. That is the same split
the obligation later names.

## 3. The obligation

The brief's type is `someEnvDef {3} iK Kenv` at
`Probe450.agda:47-48`. It does not form. Full file, three forced
rechecks, interface deleted each time:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` | 1.96 | 619020288 |
| `runs/full-recheck-2.out` | 1.94 | 619003904 |
| `runs/full-recheck-3.out` | 1.95 | 619020288 |

Median wall **1.95 s**. Median peak RSS **619020288 bytes**. No heap
event. Exit 42 every time. The error is `Probe450.agda:47.33-35`
(`runs/full-recheck-1.out:2-5`):

```
error: [UnequalTerms]
14 != 8 of type ℕ
when checking that the expression iK has type
Fin (5 Agda.Builtin.Nat.+ 3)
```

The hole on `:48` is not an inhabitant. The type fails first. No
re-layout of `Kenv` was written to make the type form.

The witness meter (`runs/witness-1.out`):

```
probe-red exit=42       2.10s  agents/tasks/LJ-1-450/Probe450.agda::someEnv-at-K  (exit 42 inside the probe: UnequalTerms)
witness: 1 UNRESOLVED of 1, 2.10 s, probe_red=True
```

## 4. WHAT THE 27 NOW COST

This task measured one of the 28, and that one did not inhabit.

Measured for `someEnv-at-K`: **no construction**. The type does not
form. Wall time of the full file is the 1.95 s median above. The
probe is 116 lines. The obligation is two lines. None of those lines
is an inhabitant of `someEnvDef`.

`[LJ-1.113]` priced the 28 at about 250 in-fence lines and called
the figure a hypothesis (`lj-1.113-report.md:135-146`). **That
figure still stands as a hypothesis.** This return does not give it
a measured member. The 25 closures are a different shape. C-42
forbids a transfer of this layout price onto them
(`dev/LESSONS.md:3752`). The two slot equalities `t0eq` and `t1eq`
were not in scope here.

The 250-line plan assumed the frames meet. They do not. A next
price for the 25 must wait on a frame that TFacts can read.

## 5. WHAT IS LEFT

The re-layout this task did not write. Named, not inhabited:

```
someEnv-padded :
  (c0 c1 c2 c3 c4 c5 : S) →
  someEnvDef {9} iK (c0 ∷ c1 ∷ c2 ∷ c3 ∷ c4 ∷ c5 ∷ Kenv)
```

`n = 9` because `5 + 9 = 14` and `11 + 9 = 20 = 6 + 14`. Then
`lookup (suc^6 iK) (c0 ∷ ... ∷ c5 ∷ Kenv)` is `lookup iK Kenv`.
The six prefix values are skipped by `suc^6`. They are not
determined by `KValue`.

The same pad would make the 24 W3 fields transfer: `lookup (suc^6
i0) (pad Kenv) = lookup i0 Kenv`, and `KFacts.tagEq0 facts` inhabits
that. That is still a re-layout. It is not a price for `someEnv`'s
environment constructor.

A next brief that wants `someEnv` at this `K` must pick one of:

1. Accept `someEnv-padded` and fund the constructor at `n = 9`.
2. Re-index `someEnvDef` to bare `Fin n` at `S ^ n`, like `KFacts`.
3. Re-layout `Kenv` itself so the bound sits at a `suc^6` slot.

This task does none of the three.

## 6. C-42

The refutation is one type: `someEnvDef {3} iK Kenv` at
`Probe450.agda:47`.

COUNT of `S ^ (11 + n)` in `src/`: **7**.
`LowerAgree.lagda.md:52`, `:97`, `:228`;
`TwelveAgree.lagda.md:131`, `:339`;
`UpperAgree.lagda.md:94`, `:213`. Every one of the seven uses
`Fin (5 + n)` and the `suc^6` lookup.

COUNT of `Kenv : S ^ 14`: **1**, `Condensation.lagda.md:7389`.
`KFacts` is the matching convention: `Fin n` and `S ^ n` at
`Condensation.lagda.md:6079-6080`.

COUNT of the consumer's `S ^ (8 + n)` in Condensation: **2**,
`SatGraphAgree` at `:6963` and `LeafAgree` at `:7225`. That is a
third length (3 conses on a `5 + n` frame).

The seven `S ^ (11 + n)` sites share the convention that failed
here. A pad that repairs `someEnvDef {9}` is not a measured cure of
`TFacts` or of `SatGraphAgree`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on the TFacts/`KValue` layout.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the D series". Declined. The live rule for this NO-GO is C-42 at `dev/LESSONS.md:3752`, not an archived D-series row.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:8`, read: "level-hood chain and its complexity requirements. **It does not carry the slot". Used: the two live chapters number the same K slot by two conventions, and the machine check is that slot arithmetic.
- `dev/literature/level-formula-slot-roles.md:9`, read: "arithmetic**, and a port that numbers its variables needs the slot arithmetic." Used: same.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a layout. It does not consult the orthodox rud digest.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not number `Fin 14` against `Fin 8`.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The obstruction is an index type, not a truncated witness.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions". Declined. Geology is not the condensation frame.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit the other 27 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not invent a re-layout of `Kenv`.
- I did not add a module hypothesis that asserts the frames meet.
- I did not postulate.

## WHAT THE NEXT BRIEF NEEDS

The condensation front does not open at this `K` until the frames
meet. The obstruction file names the adapter type
`someEnv-padded`. A next brief that wants `someEnv` constructed
must accept that pad, or change `someEnvDef`, or change `Kenv`.

The 25 closures stay unmeasured. Their 250-line hypothesis is
untouched. Do not fund them against this layout NO-GO.
