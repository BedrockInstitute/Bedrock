# LJ-1.493 report: Repair B at the real frame

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-493/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `someEnv-inlined` in
`agents/tasks/LJ-1-493/Probe493.agda`. The type is the return type of
`someEnv ya yc b a ar c yaK ycK arK` at
`src/L/Condensation.lagda.md:3515`. The body opens `SupplyEnv` at the
`KValue` telescope and does not call the `someEnv` field. Gate
`⟨ ω ∈ sucV gam ⟩` from `src/L/Coding/EnvSupply.lagda.md:111`. Nothing
lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

Predecessor `[LJ-1.483]` is a stated **STOP**
(`agents/tasks/LJ-1-483/lj-1.483-report.md:90-97`). I took the verdict
from that report. I did not repeat its dummy-C pad
(`Probe483.agda:70-73`, `:89-96`). Predecessor `[LJ-1.488]` is **GO**
on the double gate (`agents/tasks/LJ-1-488/lj-1.488-report.md:108-114`)
and declined to choose Repair A or Repair B (`:339`). Predecessor
`[LJ-1.491]` is **GO** (`agents/tasks/LJ-1-491/lj-1.491-report.md:75-77`)
and tells the landing to take `⟨ ω ∈ sucV gam ⟩`, not `⟨ ω ∈ gam ⟩`
(`:244-247`). Audit F1: a predecessor taken as a hypothesis is the
report (`dev/pod/audit-2026-08-20.md:34-41`). I did not reopen the Repair
B ruling.

## D-10, BEFORE ANY AGDA

`codesK` at `src/L/Condensation.lagda.md:3292-3296` (the
`PropAgree` hypothesis spent at `:3509`):

```
codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
         × ⟨ fst b ∈ fst (lookup K γ) ⟩
         × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

Two inputs, named at `file:line`:

1. `c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩`. Binder of `PropAgree.back`
   at `:3505` (`λ c c∈ ar a b yc shD hc ya yb hya hyb`). In scope.
2. `shEq : fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))`.
   Computed at `:3506-3508` from `shD` by
   `transport (cong fst (arityTagPairAtL-adequate ...))`. In scope.
   Not a binder. Not a postulate.

`arNum` is the fourth component of `codesK c ar a b c∈ shEq` at
`:3509`. It is already bound one line group above the `:3515` call.

`[LJ-1.483]` measured a different frame. Its C was
`suc (suc zero)` of a pad whose slot 2 was dummy `numeralL 0`
(`Probe483.agda:79-87`, `lj-1.483-report.md:89-96`). That domain
is empty. This task does not use that pad. The real site is
generic in `C`. The two inputs come from the `back` lambda, not
from a filled dummy.

The real frame can be reproduced in a probe: take `C`, `K`, `γ`,
`k` and `codesK` as `PropAgree` takes them, take the `:3505`
binders, and compute `shEq` as `:3506-3508` does. W3 is that
reproduction, obligation omitted.

## VERDICT

**GO.** W3 is GO: `frame-reachable` and `arNum-at-frame` typecheck
(`Probe493.agda:66-95`, exit 0, median **1.29 s** on three
forced rechecks). `c∈` is the `:3505` binder. `shEq` is computed
from `shD`. `codesK` applies. The domain is not empty: `C` is a
parameter.

The obligation `someEnv-inlined` typechecks
(`Probe493.agda:139-184` and the top-level alias at `:186`,
exit 0, median **4.53 s** on three forced rechecks) and PASSes
the program's witness meter
(`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-493
--brief agents/tasks/LJ-1-493/LJ-1.493.md`, exit 0, 3.23 s, 0
UNRESOLVED of 1, `probe_red=False`, `runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree. I added no
dependency.

The body opens `SupplyEnv` at the `KValue` telescope plus
`⟨ ω ∈ sucV gam ⟩` (`Probe493.agda:109-112`) and calls
`SE.someEnv` (`:169`). It does not call the `someEnv` field.
I did not write `review-of-someEnv-inlined.md`. The verdict
is GO.

This does not inhabit the `TFacts` record. It does not delete
`someEnvDef`. It does not supply `twelve-out` or `twelve-back`.
It does not touch `src/Landmarks.lagda.md`. It does not close
the campaign. It does not claim a trophy. It does not claim
the landing.

## 1. W2

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it.

One copy of `SupplyEnv.someEnv` at the generic `KValue` carrier
(`Probe493.agda:112`, `:169`). The satisfaction half is
`EnvSet.back` of `Generic.Holds`
(`src/L/Condensation.lagda.md:3045-3048`,
`src/L/Coding/EnvSet.lagda.md:521-541`), the same generic
transfer `someEnv` uses at 4 slots (`EnvSupply.lagda.md:440-444`),
instantiated here at 21 slots (`7 + 14`). `C`, `T` and `k` stay
parameters of `PropAgree`'s frame. `14` is `Kenv`'s length
(`Condensation.lagda.md:7389`), not a numeral used as a carrier.
No band. No site is named as a fixed form. There is no conflict
with W2.

W4 does not fire: no module was retired.

P-l did not fire: the types name `lookup` of `Kenv`. The gate
`⟨ ω ∈ sucV gam ⟩` is the type `SupplyEnv` already declares
(`EnvSupply.lagda.md:111`). No new type names a transparent
`sucV`-chain of a stage.

D-26 did not fire: this is an application of a delivered
supplier at a rebuilt frame, not a well-founded key.

## 2. W3: the frame, first

**GO.** The widest unmeasured term was the `:3509` frame itself.
`[LJ-1.483]` emptied `C`. This frame does not.

`frame-reachable` (`Probe493.agda:66-81`) returns the two
inputs `codesK` needs:

1. `c∈`, the binder of `PropAgree.back` at
   `Condensation.lagda.md:3505`.
2. `shEq`, computed from `shD` by the same transport as
   `:3506-3508`.

Neither is a `postulate`. `C` is a `Fin m` parameter, as
`PropAgree` states it at `:3285`. `arNum-at-frame`
(`Probe493.agda:83-95`) is the fourth component of `codesK`
applied to that pair.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`,
set on the pane, untouched. One Agda process. Dependencies warm.
The probe interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-493/Probe493.agdai`).

The first Agda run was a missing `_∈_` import (`runs/w3-1.out`,
exit 42, `[NoParseForApplication]` at `Probe493.agda:53`,
1.58 s). That is not a missing input. I added `_∈_` from
`Cubical.HITs.CumulativeHierarchy.Base`. I did not change the
term.

First green landing: 1.29 s, peak RSS 306167808 bytes, exit 0,
printed `Checking`. `runs/w3-1b.out` / `w3-1b.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.31 | 306135040 |
| `runs/w3-3.out` / `w3-3.time` | 1.29 | 306184192 |
| `runs/w3-4.out` / `w3-4.time` | 1.28 | 306151424 |

Median wall **1.29 s**. Median peak RSS **306151424 bytes**. No
heap event.

**38** non-blank non-comment lines in `module W3`
(`Probe493.agda:56-95`). `frame-reachable` is 16 of those.
`arNum-at-frame` is 13. The estimate was about 35 lines and
under 40 seconds. Measured, the named terms are that size and
in that second. Nothing is funded against the estimate. Nothing
is funded against `[LJ-1.483]`'s 2.32 s: that measurement
supplied `c∈` and `shEq` by hand at an empty `C`.

## 3. The obligation

**GO.** `someEnv-inlined` is the return type of
`someEnv ya yc b a ar c yaK ycK arK` at
`Condensation.lagda.md:3515`, rebuilt at `KValue`'s `Kenv`
with `B = iA` and `K = iK` (`Probe493.agda:139-184`). The
top-level name the witness reads is the alias at `:186`.

`arNum` comes from `codesK` at the W3 pair (`:166`). `ycK`
comes from `valK` after `GraphEntry.bin` (`:167`), as
`:3510`. `yaK` comes from `subK₁` (`:168`), as `:3513`.
The body then opens `SupplyEnv` and calls `SE.someEnv`
(`:169`). The satisfaction half is the 4-to-21 reindex
(`:170-184`), the same transfer `[LJ-1.488]` used at 27
slots.

`C` and `T` stay parameters. Slot 2 of `Kenv` is `numeralL 0`
(`Condensation.lagda.md:7391`). This term does not pick that
slot for `C`. That is the difference from `[LJ-1.483]`.

The first full-file run was `subValAt` not exported by
`L.Condensation` (`runs/full-1.out`, exit 42, `[NotInScope]`
at `Probe493.agda:130`, 3.22 s). The name lives in
`L.Coding.Model`. I moved the import. I did not change the
term.

Typechecked, caliber `-A64m -I0 -M8g`, set on the pane,
untouched. One Agda process. The probe interface was deleted
before every kept recheck.

First green landing: 4.76 s, peak RSS 768016384 bytes, exit 0,
printed `Checking`. `runs/full-1b.out` / `full-1b.time`.

Three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-2.out` / `full-2.time` | 4.60 | 769032192 |
| `runs/full-3.out` / `full-3.time` | 4.33 | 769048576 |
| `runs/full-4.out` / `full-4.time` | 4.53 | 769048576 |

Median wall **4.53 s**. Median peak RSS **769048576 bytes**. No
heap event.

**143** non-blank non-comment lines in the final probe.
`someEnv-inlined` is 46 of those (`:139-184`). The estimate
was about 150 lines, of which the obligation was about 40,
comparables of SHAPE. Measured, the named term is that size
and in that second. Nothing is funded against the estimate.
Nothing is funded against `[LJ-1.491]`'s 2.40 s: that pad
measured a record telescope, not this frame
(`lj-1.491-report.md:259-260`).

## WHAT REPAIR B STILL OWES

From `[LJ-1.488]` `lj-1.488-report.md:308-328`, five site groups.
This task measures group 1 at the probe, not in `src/`.

1. `src/L/Condensation.lagda.md:3515` (replace the call; `arNum`
   is already bound at `:3509`). **THIS TASK.** Probe term
   `someEnv-inlined`. Not a landing.
2. `src/L/Condensation.lagda.md:3285-3320` (`PropAgree` must open
   `SupplyEnv`, so it must take `lam`, `gam`, and `ω∈γ`).
   Re-parameterisation. Unmeasured as a landing.
3. `src/L/Condensation.lagda.md:3317`, `:3569`, `:3624` (the
   `someEnv` parameter can then go). Deletion. Unmeasured as a
   landing.
4. `src/L/Condensation/LowerAgree.lagda.md:52-58`, `:218`, `:273`,
   `:279` (delete or retire `someEnvDef` / `LFacts.someEnv` and
   stop passing it). Deletion. Unmeasured as a landing.
5. `src/L/Condensation/TwelveAgree.lagda.md:289`, `:442` (delete
   `TFacts.someEnv` and stop filling it). Deletion. Unmeasured as
   a landing.

I do not claim the landing.

## 5. WHAT IS LEFT

The obligation at this frame is inhabited. Repair B is still a
landing. This GO gives the landing its pad at group 1. It does
not land group 1.

`PropAgree` still does not take `lam`, `gam`, or `ω∈γ`
(`Condensation.lagda.md:3285-3320`). The `someEnv` parameter
is still there (`:3317`, `:3569`, `:3624`). `someEnvDef` is
still there (`LowerAgree.lagda.md:52-58`, `:218`,
`TwelveAgree.lagda.md:289`, `:442`). Those are groups 2 to 5.

The other 27 `TFacts` fields. This task did not inhabit them.

`twelve-out` and `twelve-back`
(`TwelveAgree.lagda.md:527-537`) still need a `TFacts` value at
a real `K`. `SatGraphAgree` still leaves those two parameters
unsupplied (`src/L/Condensation.lagda.md:6971-6976`).

The 25 closure lemmas. The 250-line hypothesis still stands
(`agents/tasks/LJ-1-113/lj-1.113-report.md:135-146`). Do not
fund them against this 4.53 s.

Do not fund a landing against this pad. Re-measure it at the
chosen site in `src/`.

## 6. C-42

This return is a GO at one site: the `:3515` call, rebuilt in
the probe at `KValue`'s `Kenv` with `B = iA` and `K = iK`.
It says the inlined term typechecks. It does not measure a
landing in `src/`.

COUNT of `module KValue` in `src/`: **1**,
`Condensation.lagda.md:7380`. In `archive/src/`: **0**.

COUNT of the type `⟨ ω ∈ sucV gam ⟩` in `src/`: **1**,
`EnvSupply.lagda.md:111`. In `archive/src/`: **0**.

COUNT of `someEnvDef` in `src/`: **5** raw, **3** typed.
Raw: `LowerAgree.lagda.md:52`, `:53`; `:218`;
`TwelveAgree.lagda.md:33`, `:289`. Typed sites:
`:52`, `:218`, `:289`. None takes `ω∈γ`. None takes the
truncation. In `archive/src/`: **0**.

COUNT of `SupplyEnv.someEnv` in `src/`: **1**,
`EnvSupply.lagda.md:417`. It takes the truncation at `:418`
and lives under `ω∈γ` at `:111`.

COUNT of the ungated `someEnv` parameter in `src/`: **3**,
`Condensation.lagda.md:3317`, `:3569`, `:3624`. One call that
throws `arNum` away: `:3515`. A cure of this probe is not a
measured cure of those three parameters in `src/`. Re-measure
each.

A landing that inlines `:3515` is not a measured cure of
`PropAgree`'s missing `KValue` telescope. It is not a measured
cure of `someEnvDef`. Re-measure each.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. The live producer is `dev/pod/queue.toml`. This task does not consult the archived dispatch rows.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on whether the `:3509` frame supplies `c∈` and `shEq`.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the D series". Declined. The live rulings are `dev/pod/rulings.toml`. This task does not consult the archived D rows.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined. Devlin II.5 does not inhabit `someEnv-inlined` at this frame.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary term is at issue.
- `dev/literature/truncation-and-selection.md:1`, read: "# Truncation and selection: how the two literatures pick a witness". Declined. The truncation is the fourth component of `codesK` at `:3509`. The work is an application, not a literature selection.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. The rud route is not this term.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions". Declined. Geology is not this term.
