# LJ-1.457 report: the frame re-layout the condensation stack needs

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-457/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `tfacts-prefix` in
`agents/tasks/LJ-1-457/Probe457.agda`. The twelve `tagEq` fields and the
twelve `numK` fields of `TFacts`, as a Sigma at a re-laid-out
environment `Kenv'`, inhabited from `KValue.facts`. Nothing lands in
`src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## D-10, BEFORE ANY AGDA

Two conventions, side by side.

`TFacts` at `src/L/Condensation/TwelveAgree.lagda.md:129-133`:

```
record TFacts {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ' : S ^ (11 + n)) : Type (ℓ-suc ℓ) where
  field
    tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ') ≡ fst (numeralL 0)
```

`KValue` at `src/L/Condensation.lagda.md:7387-7409`:

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

`KFacts` at `src/L/Condensation.lagda.md:6079-6082` reads a bare
index: `fst (lookup N0 γ) ≡ fst (numeralL 0)`.

Two equations, one `n`:

1. Index types meet: `Fin (5 + n) = Fin 14`, so `n = 9`. Then
   `γ' : S ^ (11 + 9) = S ^ 20`.
2. Env lengths meet without a pad: `11 + n = 14`, so `n = 3`. Then
   `K : Fin (5 + 3) = Fin 8`.

No `n` solves both at `Kenv` itself. That is the `[UnequalTerms]`
`14 != 8` that `[LJ-1.450]` measured
(`agents/tasks/LJ-1-450/lj-1.450-report.md:57-62`,
`Probe450.agda:47`).

`n = 9` plus six fillers does solve both:

- `X : Fin (5 + 9) = Fin 14`
- `γ' : S ^ (11 + 9) = S ^ 20`
- `6 + 14 = 20`
- `lookup (suc^6 X) (c0 ∷ c1 ∷ c2 ∷ c3 ∷ c4 ∷ c5 ∷ Kenv) = lookup X Kenv`

The brief names this arithmetic
(`agents/tasks/LJ-1-457/LJ-1.457.md:29-30`). I checked it. It is
right. The corrected arithmetic is not the deliverable. The term at
that layout is.

Predecessor `[LJ-1.450]` is NO-GO on `someEnv-at-K` at
`someEnvDef {3} iK Kenv`
(`agents/tasks/LJ-1-450/lj-1.450-report.md:75`). That type is not
this brief's type. The 450 report names the pad this task inhabits
(`:219-228`). I did not inhabit a predecessor NO-GO.

Predecessor `[LJ-1.113]` is COMPLETE, not NO-GO
(`agents/tasks/LJ-1-113/lj-1.113-report.md:3`). It does not name
`TFacts` FALSE.

W3 runs first.

## VERDICT

**GO.** `tfacts-prefix` typechecks
(`agents/tasks/LJ-1-457/Probe457.agda:136-167`, exit 0, median
**2.20 s** on three forced rechecks) and PASSes the program's
witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-457
--brief agents/tasks/LJ-1-457/LJ-1.457.md`, exit 0, 2.88 s, 0
UNRESOLVED of 1, `probe_red=False`, `runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree. `/usr/bin/python3`
is 3.9.6 and has no `tomllib`. The meter ran under
`/opt/homebrew/bin/python3.11`. I added no dependency.

I did not write `review-of-tfacts-prefix.md`. The verdict is GO.

A GO puts the first `TFacts` content in the tree at a real `K`, as
a 24-field Sigma at the re-laid-out `Kenv'`. It does not inhabit
the `TFacts` record. It does not supply `twelve-out` or
`twelve-back`. It does not touch `src/Landmarks.lagda.md`. It does
not close the campaign. It does not claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The 24-field Sigma is generic in `KValue`'s bound `lam` and stage
`gam`. `n = 9` is the layout integer that makes `Fin (5 + n)` meet
`Fin 14`. It is not a fixed mathematical carrier. One copy.
Instantiated at `KValue`'s parameters. No band, no numeral, and no
site is named as a fixed form. There is no conflict with W2.

W4 does not fire: no module was retired.

P-l did not fire: the types name `lookup` of `Kenv'` and
`numeralL`. They do not name a transparent `sucV`-chain of a
stage.

D-26 did not fire: this is a layout transfer, not a well-founded
key.

## 2. W3: one `tagEq` field, first

**GO.** The widest unmeasured term was one field at the pad, not
twenty-four.

```
one-tag : fst (lookup (suc (suc (suc (suc (suc (suc i0')))))) Kenv')
        ≡ fst (numeralL 0)
one-tag = KFacts.tagEq0 facts
```

at `Probe457.agda:62-64`, inside `module W3` at a real `KValue`
frame. `i0' : Fin (5 + 9)` and `i0' = i0` (`:57-58`). `Kenv'` is
six `numeralL 0` fillers in front of `Kenv` (`:52-55`). The body
is `KFacts.tagEq0 facts` (`src/L/Condensation.lagda.md:7413`).

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-457/Probe457.agdai`).

First landing: 1.78 s, peak RSS 611155968 bytes, exit 0, printed
`Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.72 | 611139584 |
| `runs/w3-3.out` / `w3-3.time` | 1.73 | 611139584 |
| `runs/w3-4.out` / `w3-4.time` | 1.72 | 611139584 |

Median wall **1.72 s**. Median peak RSS **611139584 bytes**. No
heap event.

TWO non-blank code lines for `one-tag` (type plus body). The
estimate was two lines and under 10 seconds. Measured, it is that
size and in that second. Nothing is funded against the estimate.
One field transferred, so the arithmetic is right.

## 3. The obligation

`tfacts-prefix` (`Probe457.agda:136-167`) is the 24-tuple of
`KFacts.tagEq0` through `KFacts.numK11` from `KValue.facts`
(`src/L/Condensation.lagda.md:7413-7419`). Its type is
`TFactsPrefix (Kenv' lam ...)` (`:141`). `TFactsPrefix`
(`:109-134`) is the Sigma of the 24 field types, copied from
`src/L/Condensation/TwelveAgree.lagda.md:133-156`. `Kenv'`
(`:101-107`) is `W3.Kenv'`. The indices `iK'` and `i0'` through
`i11'` (`:74-99`) are KValue's Fin 14 names at `Fin (5 + 9)`.

The file imports `L.Condensation` and `L.Condensation.TwelveAgree`
from `src/` (`:21-22`). It does not import a probe. It does not
build a `TFacts` record. It does not inhabit the other 31 fields.
It does not postulate. It does not weaken a field.

**124 non-blank non-comment lines** in the probe. `tfacts-prefix`
itself is 32 of those. `TFactsPrefix` is 26. The brief's estimate
was about 140 lines, of which the obligation was about 50,
comparables of SHAPE. Measured, the file is smaller. Nothing is
funded against the estimate.

Full file, first landing: 3.06 s, peak RSS 680542208 bytes, exit
0, printed `Checking`. `runs/full-1.out` / `full-1.time`. The
TwelveAgree import is the extra load against W3.

Three forced rechecks, interface deleted each time, same caliber,
one Agda process:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.44 | 680509440 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.20 | 680460288 |
| `runs/full-recheck-4.out` / `full-recheck-4.time` | 2.19 | 680476672 |

Median wall **2.20 s**. Median peak RSS **680476672 bytes**. No
heap event. Exit 0 every time.

The witness meter (`runs/witness-1.out`):

```
pass      exit=0        2.88s  agents/tasks/LJ-1-457/Probe457.agda::tfacts-prefix
witness: 0 UNRESOLVED of 1, 2.88 s, probe_red=False
```

The shape that resisted was the layout, not the mathematics. At
`n = 3` the 24 fields do not transfer (`[LJ-1.450]`,
`runs/w3-1.out` there). At `n = 9` with six fillers they transfer
by `refl` of the lookup reduction. I did not weaken a field. I
did not leave a hole.

## 4. WHAT THE 31 NOW COST

This task measured the 24 fields that `KFacts` already supplies.
They transfer at the pad. Wall time of the full file is the
2.20 s median above.

`[LJ-1.113]` priced the 28 at about 250 in-fence lines and called
the figure a hypothesis
(`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). **That
figure still stands as a hypothesis for the rest.** This return
does not re-price the 25 closure lemmas. They are a different
shape. C-42 forbids a transfer of this layout price onto them
(`dev/LESSONS.md:3752`). The two slot equalities `t0eq` and
`t1eq` were not in scope here.

The 250-line plan assumed the frames meet. They meet at this pad.
They do not meet at `Kenv` itself. A next price for the 25 still
waits on a closure lemma of that family, which this tree has not
written.

## 5. WHAT IS LEFT

The other 31 `TFacts` fields. This task did not inhabit them.

The six fillers of `Kenv'` are dummy `numeralL 0`
(`Probe457.agda:53-54`). `tagEq` and `numK` skip them via
`suc^6`. `TFacts.valK` reads `lookup (suc zero) γ'`
(`TwelveAgree.lagda.md:175`) and `TFacts.codesK` reads
`lookup (suc (suc zero)) γ'` (`:162`). A next brief that
inhabits those fields must pick a real graph and a real code set
for slots 1 and 2. It must not reuse these dummies.

`someEnv-padded` from `[LJ-1.450]`
(`agents/tasks/LJ-1-450/review-of-someEnv-at-K.md:72-75`) is the
same pad at `n = 9`. It is still uninhabited. This return does
not construct an environment.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:527-537`) still need a `TFacts` value at a
real `K` (`:523-526`). `SatGraphAgree` still leaves those two
parameters unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

A next brief that wants the `TFacts` record itself must name that
record. This task was forbidden to build it.

## 6. C-42

This return is a GO at one Sigma, not a refutation. The count
below is the sweep of the two conventions, re-measured in `src/`
on this dispatch.

COUNT of `S ^ (11 + n)` in `src/`: **7**.
`LowerAgree.lagda.md:52`, `:97`, `:228`;
`TwelveAgree.lagda.md:131`, `:339`;
`UpperAgree.lagda.md:94`, `:213`. Every one of the seven uses
`Fin (5 + n)` and the `suc^6` lookup.

COUNT of `Kenv : S ^ 14` in `src/`: **1**,
`Condensation.lagda.md:7389`. `KFacts` is the matching
convention: `Fin n` and `S ^ n` at
`Condensation.lagda.md:6079-6080`.

COUNT of the consumer's `S ^ (8 + n)` in Condensation: **2**,
`SatGraphAgree` at `:6963` and `LeafAgree` at `:7225`. That is a
third length (3 conses on a `5 + n` frame).

The pad that repairs the 24 fields at `n = 9` is not a measured
cure of `someEnvDef`, of `SatGraphAgree`, or of the other six
`S ^ (11 + n)` sites. It is a measurement of
`Probe457.agda::tfacts-prefix`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on the TFacts/`KValue` layout.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/ORCHESTRATION.md:1`, read: "# ORCHESTRATION: the orchestrator's operating rules". Declined. The live loop is `dev/pod/README.md`. This task does not consult the archived orchestrator rules.

## LITERATURE USED

- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures a layout. It does not consult the orthodox rud digest.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not number `Fin 14` against `Fin (5 + 9)`.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The work is an index transfer, not a truncated witness.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit the other 31 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not import a probe.
- I did not postulate.
- I did not weaken a field.
- I did not write `review-of-tfacts-prefix.md`.

## WHAT THE NEXT BRIEF NEEDS

The 24 `tagEq` and `numK` fields transfer at `n = 9` with six
fillers. The lookup reduction is definitional. `KValue.facts`
inhabits the Sigma. That is measured.

What a next brief can order, one at a time:

1. The remaining `KFacts` fields that `TFacts` also names
   (`innerK`, `pairK`, and their kin), at this same pad. Do not
   fund them against this 2.20 s. Re-measure them.
2. `someEnv-padded` at this pad
   (`agents/tasks/LJ-1-450/review-of-someEnv-at-K.md:72-75`). The
   constructor is still unbuilt.
3. The 25 closure lemmas. The 250-line hypothesis still stands.
   Do not fund them against this layout GO.
4. A `TFacts` record at this pad, once the other 31 have
   suppliers. This task was forbidden to build that record.
   Slots 1 and 2 of `Kenv'` must then be a real graph and a real
   code set, not dummy `numeralL 0`.

The condensation front is open for those briefs. It is not open
for a landing in `src/` until a brief names the `TFacts` record
and the consumer's two parameters.
