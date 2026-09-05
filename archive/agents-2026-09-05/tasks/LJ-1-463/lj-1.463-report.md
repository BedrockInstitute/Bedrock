# LJ-1.463 report: someEnv again, on the frame that now transfers

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-463/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `someEnv-at-K` in
`agents/tasks/LJ-1-463/Probe463.agda`. The type is
`someEnvDef {9} iK' Kenv'`. `someEnvDef` is
`src/L/Condensation/LowerAgree.lagda.md:52-58`. `iK'` and `Kenv'`
are the frame `[LJ-1.457]` delivered at
`agents/tasks/LJ-1-457/Probe457.agda:52-55` and `:74-75`. Nothing
lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.457]` is **GO**
(`agents/tasks/LJ-1-457/lj-1.457-report.md:87-89`). I took the
layout from its probe, not from its brief. I did not inhabit a
predecessor NO-GO.

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

`[LJ-1.457]`'s frame at `agents/tasks/LJ-1-457/Probe457.agda:52-55`
and `:74-75`:

```
Kenv' : Vec S (11 + 9)
Kenv' = numeralL 0 ∷ numeralL 0 ∷ numeralL 0
      ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
      ∷ Kenv

iK' : Fin (5 + 9)
iK' = suc zero
```

The arity `[LJ-1.457]` settled is the arity `someEnvDef` needs:
`someEnvDef {9}` wants `K : Fin (5 + 9)` and `γ : S ^ (11 + 9)`,
and the probe delivers `iK' : Fin (5 + 9)` and `Kenv' : Vec S (11 + 9)`
(`LowerAgree.lagda.md:52-53` against `Probe457.agda:52,74`). They
meet. I do not stop on layout.

W3 runs first.

## VERDICT

**NO-GO.** W3 built `Generic.envSetGen` as a term of type `S` and
failed to put it in the bound. Agda reports `[UnequalTerms]`
`fst (numeralL 0) != fst G.envSetGen` at
`agents/tasks/LJ-1-463/Probe463.agda:87`
(`runs/w3-1.out`, exit 42, median **1.90 s** on three forced
rechecks). `KFacts.numK0` is membership of `numeralL 0`
(`src/L/Condensation.lagda.md:7416`). It is not membership of
the environment set. The bound's delivered closures do not
include `envSetK` (`:7413-7425`).

Satisfaction of `envHypB2` was not attempted. The brief stops
when the membership half cannot be built. I wrote
`review-of-someEnv-at-K.md`. I did not inhabit `someEnv-at-K`.

A NO-GO names what the environment construction still needs.
The delivered constructor is `SupplyEnv.someEnv`
(`src/L/Coding/EnvSupply.lagda.md:417-444`). It needs a numeral
arity, `ω∈γ`, and the carrier as `B`. `someEnvDef` names none
of these. The brief forbids a new hypothesis. See the review
for the corrected target.

This does not inhabit the `TFacts` record. It does not supply
`twelve-out` or `twelve-back`. It does not touch
`src/Landmarks.lagda.md`. It does not close the campaign. It
does not claim a trophy.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

The environment set is `Generic.envSetGen B ar`
(`src/L/Coding/EnvSet.lagda.md:396,456`). That is one generic
construction. `SupplyEnv.someEnv` instantiates it at the
carrier `B₀ = LsetS gam` (`EnvSupply.lagda.md:124-125,427`).
This probe instantiated it at slot 0 of the delivered `Kenv'`,
which is dummy `numeralL 0`. One copy of the construction. No
band, no numeral, and no site is named as a fixed form. There
is no conflict with W2. The stop is the missing membership, not
a fixed-form rewrite.

W4 does not fire: no module was retired.

P-l did not fire: the types name `lookup` of `Kenv'` and
`Generic.envSetGen`. `envSetGen` is `opaque`
(`EnvSet.lagda.md:455-456`). They do not name a transparent
`sucV`-chain of a stage.

D-26 did not fire: this is an environment-set construction, not
a well-founded key.

## 2. W3: membership of the environment, first

**NO-GO.** The widest unmeasured term was whether THE
environment set lies in `K`, without satisfaction.

```
env-in-K : (ya yc ar : S)
         → ⟨ fst ya ∈ fst bound ⟩
         → ⟨ fst yc ∈ fst bound ⟩
         → ⟨ fst ar ∈ fst bound ⟩
         → Σ S (λ E → ⟨ fst E ∈ fst bound ⟩)
env-in-K ya yc ar yaK ycK arK = E , EK
  where
  B = lookup zero Kenv'
  module G = Generic B ar
  E = G.envSetGen
  EK = KFacts.numK0 facts
```

at `Probe463.agda:70-87`, inside `module W3` at a real `KValue`
frame. `bound` is `lookup (suc^6 iK') Kenv'` (`:61-62`). `iK'`
and `Kenv'` are `[LJ-1.457]`'s names (`:53-59`). The body of
`EK` is `KFacts.numK0 facts` (`Condensation.lagda.md:7416`).

Typechecked ALONE, obligation omitted on the W3 runs, caliber
`-A64m -I0 -M8g`, set on the pane, untouched. One Agda process.
Dependencies warm. The probe interface was deleted before every
kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-463/Probe463.agdai`).

First landing: 2.16 s, peak RSS 610910208 bytes, exit 42,
printed `Checking` then `[UnequalTerms]`. `runs/w3-1.out` /
`w3-1.time`.

Three forced rechecks, exit 42 every time, each printed
`Checking` then the same `[UnequalTerms]`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 2.01 | 605683712 |
| `runs/w3-3.out` / `w3-3.time` | 1.90 | 610910208 |
| `runs/w3-4.out` / `w3-4.time` | 1.84 | 610926592 |

Median wall **1.90 s**. Median peak RSS **610910208 bytes**. No
heap event.

The estimate was about 20 lines and under 15 seconds. Measured,
the W3 block is 18 non-blank non-comment lines (`:70-87`) and
in that second. Nothing is funded against the estimate. The
construction elaborates. The membership does not close.

`[LJ-1.113]` said the machine describes environments and does
not build one from `K` memberships
(`lj-1.113-report.md:152-155`). Measured here: `envSetGen`
builds the set as a term of type `S`. The missing piece is the
membership in the bound, which is `envSetK` gated at a numeral
(`EnvSupply.lagda.md:140-146`).

## 3. The obligation

`someEnv-at-K` (`Probe463.agda:107-113`) is the named type
`someEnvDef {9} iK' (Kenv' ...)`. The type is written. The body
is a hole. Agda did not reach the hole: it stopped at W3's
`[UnequalTerms]` (`runs/full-1.out`, exit 42, 1.75 s, peak RSS
604618752 bytes). Satisfaction was not attempted.

**63 non-blank non-comment lines** in the probe. `env-in-K` is
18 of those. The brief's estimate was about 150 lines, of which
the obligation was about 45, comparables of SHAPE. Measured,
the file is smaller because the membership half failed. Nothing
is funded against the estimate.

I did not add a numeral hypothesis. I did not add `ω∈γ`. I did
not rewrite a filler. I did not postulate. I did not inhabit
the other 27 fields. I did not write a `TFacts` record. I did
not import a probe.

The shape that resisted was the membership of `envSetGen` in
`K`, not the layout. At `n = 9` the type forms. At the
delivered `KFacts` the membership does not close.

The full file has one run after the obligation name was added.
Agda stopped at the same W3 error, so three full-file rechecks
would repeat W3. I did not run them. The W3 median above is the
price.

## WHAT THE 27 NOW COST

This task measured one of the 28: the environment-existence
construction, membership half only. Measured: 18 non-blank
lines of W3, median wall **1.90 s**, exit 42, peak RSS
610910208 bytes. The construction elaborates. The membership
does not close from `KFacts`.

`[LJ-1.113]` priced the 28 at about 250 in-fence lines and
called the figure a hypothesis
(`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). **That
figure still stands as a hypothesis for the 25 closures.** This
return does not re-price those 25. They are a different shape.
C-42 forbids a transfer of this membership failure onto them
(`dev/LESSONS.md:3752`). The two slot equalities `t0eq` and
`t1eq` were not in scope here.

The 250-line plan counted this construction as one of the 28.
The construction still needs a numeral gate, `ω∈γ`, and a real
`B` in slot 0. A next price for `someEnv` waits on that gated
type. It is not this 1.90 s, and it is not the 25.

## 5. WHAT IS LEFT

The obligation `someEnv-at-K` at the ungated `someEnvDef {9}`.
This task did not inhabit it.

The six fillers of `Kenv'` are dummy `numeralL 0`
(`Probe463.agda:54-56`, copied from `Probe457.agda:53-54`).
`envHypB2 {11 + n} zero` reads slot 0 as `B`. The supplier
uses the carrier `LsetS gam`. A next brief that inhabits
`someEnv` must put the carrier in slot 0. It must not reuse
this dummy.

`SupplyEnv.someEnv` (`EnvSupply.lagda.md:417-444`) is the
delivered constructor. It is still not transported onto
`someEnvDef`. The review names the gated type.

The other 27 `TFacts` fields. This task did not inhabit them.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:527-537`) still need a `TFacts` value at
a real `K`. `SatGraphAgree` still leaves those two parameters
unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

A next brief that wants the `TFacts` record itself must name
that record. This task was forbidden to build it.

## 6. C-42

This return is a NO-GO at one membership, not a refutation of
`someEnvDef`. The count below is the sweep of the ungated
environment-existence shape, re-measured in `src/` on this
dispatch.

COUNT of `someEnvDef` in `src/`: **3**.
`LowerAgree.lagda.md:52`, `:218`;
`TwelveAgree.lagda.md:289`. None of the three gates the arity.

COUNT of numeral-gated `envSetK` in `src/`: **2**.
`TwelveAgree.lagda.md:306`; `EnvSupply.lagda.md:140`. Both take
`fst ar ≡ # n`.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes the truncation and `ω∈γ`.

The pad that repaired the 24 fields at `n = 9` is not a
measured cure of `someEnvDef`. It is the frame this membership
failed on. A cure of `env-in-K` at this site is not a measured
cure of `LFacts.someEnv` or of `TFacts.someEnv`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on `someEnv` at the re-laid-out frame.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived in full 2026-08-18". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived DD rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. Devlin 5.5 does not inhabit `someEnvDef {9}` at `Kenv'`.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The work is a membership of a constructed environment set, not a truncated witness selection.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task measures an environment-set membership. It does not consult the orthodox rud digest.
- `dev/literature/glossary-review-2026-08.md:1`, read: "# Glossary review: the 119 pre-protocol entries". Declined. This task adds no glossary entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit `someEnv-at-K`.
- I did not inhabit the other 27 `TFacts` fields.
- I did not write a `TFacts` record.
- I did not import a probe.
- I did not postulate.
- I did not add a numeral hypothesis or `ω∈γ`.
- I did not rewrite a filler.
- I did not attempt the satisfaction half.

## WHAT THE NEXT BRIEF NEEDS

The layout at `n = 9` is measured GO by `[LJ-1.457]`. The type
`someEnvDef {9} iK' Kenv'` forms. Membership of
`Generic.envSetGen` in the bound does not follow from `KFacts`.
That is measured.

What a next brief can order, one at a time:

1. The gated `someEnv-numeral` named in
   `review-of-someEnv-at-K.md`. Body from `SupplyEnv.someEnv`
   (`EnvSupply.lagda.md:425-444`), plus a transport from the
   4-slot frame onto `envHypB2`. It needs `ω∈γ`, the numeral
   truncation, and the carrier in slot 0. Do not fund it
   against this 1.90 s. Re-measure it.
2. The 25 closure lemmas. The 250-line hypothesis still stands.
   Do not fund them against this membership NO-GO.
3. A `TFacts` record at this pad, once the other 31 have
   suppliers. This task was forbidden to build that record.
   Slots 0, 1 and 2 of `Kenv'` must then be a real carrier, a
   real graph and a real code set, not dummy `numeralL 0`.

The condensation front is open for those briefs. It is not open
for a landing in `src/` until a brief names the gated `someEnv`
and the consumer's two parameters.
