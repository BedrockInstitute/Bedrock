# LJ-1.422 report: untruncate the least-cardinal arrow, or name the device the tree lacks

slot: `coder`. Written early as a skeleton and filled as answers landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-422/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term `kappa-arrow-data` in
`agents/tasks/LJ-1-422/Probe422.agda`, at a generic L-element, the
same arrow as `κ-inj` / `κ-injL`, as DATA.

## VERDICT

**NO-GO.** The truncated arrow is delivered. The data form is a
choice of one of several injections. No live untruncation device
covers that carrier. The orthodox size proof does not name this
arrow as data. The missing device is a well-order on the injections.
It is absent. The archived condensation chapter is not that device.

The obstruction is `review-of-kappa-arrow-data.md`, written for the
branch `no-go-stated`.

The dispatched direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## WHAT THE ORTHODOX PROOF NAMES THIS ARROW WITH

W8. Literature was read before any Agda.

**Which theorem supplies the arrow.** Devlin II.1.1(vii),
`|L_α| = |α|` for `α ≥ ω` (`dev/literature/devlin-II5.md:413`, quoting
`dev2.txt:117` and `dev2.txt:200-240`). The J-side parallel is SZ 1.17:
a `Σ₁` surjection `α → J_α^A`, and if `α` is closed under the Gödel
pairing function, the enumeration `Φ : otp(<_α^A) → J_α^A` with
`otp = α` (`dev/literature/j-hierarchy.md:147-149`). SZ 1.27 is
`|J_ρ^A| = H_ρ^M` (`dev/literature/j-hierarchy.md:181`). These
theorems name the size of a LEVEL against its INDEX.

**What device makes the arrow canonical.** The canonical well-order
of the level, then leastness with a universal guard. Digest Q4:
stage-first, then the lexicographically minimal producer triple
(`dev/literature/digest.md:56-63`). SZ p. 11 writes that order as
`<^A_β` (`dev/literature/j-hierarchy.md:122-132`). Devlin II.5.3
writes the guard as `φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))`
(`dev/literature/devlin-II5.md:127-131`). For an injection as DATA,
that well-order must sit on the INJECTIONS
(`dev/literature/truncation-and-selection.md:335-337`).

**Whether that device is live, archived, or absent.** The well-order
of stage members is live (`orderAt` at
`src/L/Choice/Step.lagda.md:730`; `wL` at `src/L/Hull.lagda.md:158`).
A well-order on ambient function types is **absent**. The archived
condensation chapter is **not** the device: its first paragraph is
the recognition step of a collapse
(`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:4`). The
size-equation's pairing-and-enumeration device, the order-type
reading of Gödel pairing, lives on the retired route
(`archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:4`).
The live square-law chapter never forms that order type
(`src/L/Ordinal/SquareLaw.lagda.md:10-11`). That archived device
names `L_α ↪ α`, not `α ↪ κ`.

A cardinal inequality is a truncated existence of an injection
(`dev/literature/truncation-and-selection.md:75-86`). A proof that
only needs cardinal arithmetic never needs an injection as data.
A formalization that states the conclusion with the injection as
data asks for something the sources do not supply.

## DEVICE CHECKLIST

Carrier of the truncation: `⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫`, a Sigma
of a function and a proof (`src/L/Cardinal.lagda.md:47-48`).

### 1. PT.rec

No. The target is not an hProp. The chapter says so in its own
comment: "The witness, an injection, still truncated, still not an
hProp." (`src/L/Cardinal.lagda.md:132-133`). `PT.rec` demands an
`isProp` motive. A Sigma of a function space and injectivity is a
set, not a proposition: many injections exist whenever one does.
Not applied in Agda.

### 2. leastOf / SWO enumeration

No. `leastOf` untruncates over a carrier that carries an `SWO`
(`src/L/WellOrder/Base.lagda.md:158-160`). `P` must be hProp-valued,
so a data payload does not come out
(`dev/literature/truncation-and-selection.md:147-148`).

Re-enumeration, this run, pattern `': SWO|SWO ('` over `src/`,
files `*.lagda.md` and `*.agda`: **COUNT 49**. I did not cite
`[LJ-1.391]`. The audit F8 named that count as the thing a re-run
returns (`dev/pod/audit-2026-08-20.md:102-103`).

Six shapes, none a function type or `_↪_`:

| Shape | Sites |
|---|---|
| Generic parameter (`A`, `X`, `Y`, `B`, `C`, `ZFStructure.S`) | `src/L/WellOrder/Base.lagda.md:127`; `src/L/Ordinal/SquareLaw.lagda.md:70`, `:77`; `src/L/Choice/Step.lagda.md:220`, `:226`; `src/L/Hull.lagda.md:60` |
| Member types `⟪_⟫`, `Mem`, `SL` | `src/L/Ordinal/SquareLaw.lagda.md:176`; `src/L/StageCardinal.lagda.md:258`; `src/L/Cardinal.lagda.md:91`; `src/L/Choice/Step.lagda.md:272`, `:730`; `src/L/Hull.lagda.md:158`; and the `SWO ⟪ A ⟫` / `SWO (Mem _)` hypotheses in Choice and BoundedSubset |
| Products of member types | `src/L/Ordinal/SquareLaw.lagda.md:127`, `:282`, `:285` |
| Gödel `Pair` / `PairA` | `src/L/Ordinal/SquareLaw.lagda.md:308`, `:755` |
| `Name` / `New` | `src/L/Choice/Name.lagda.md:804`; `src/L/Choice/Step.lagda.md:373`, `:429`; `src/L/Choice/Faithful.lagda.md:400` |
| `ℕ` / `Point n` / `Limit` | `src/L/Choice/Finite.lagda.md:596`, `:884`, `:1114` |

One of the 49 lines is a name, not a carrier: `module OrdSWO (` at
`src/L/StageCardinal.lagda.md:228`. No line is `SWO (_ ↪ _)` or
`SWO (_ → _)`. No delivered `SWO` injects into the injection type.
Not applied in Agda.

### 3. swo-into-ord

This is the one device applied. Predecessor `[LJ-1.417]`: **GO**
(`agents/tasks/LJ-1-417/lj-1.417-report.md:18-19`). Type that
typechecked (`agents/tasks/LJ-1-417/Probe417.agda:80`):

```
swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))
```

under `{A : Type ℓ}`, `w : SWO {ℓc = ℓ} A`, and the three rank
parameters. It returns an injection into SOME ordinal. The task's
target is an injection into the NAMED `κL`. Even a well-typed
application to THIS carrier would inject the injection-type into
some `β`, not produce one injection `⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫`.

The carrier of the truncation does not carry an `SWO` (section 2).
The fragment feeds the delivered domain order `ordSWO` at
`src/L/Ordinal/SquareLaw.lagda.md:176`. The elaborator rejects it.

## D-10: MAY THE TREE NAME THE DATA?

The truncated form is true. The data form is a choice of one of
several. A canonical choice is possible if and only if the
injections carry a well-order, or some other weakly constant
endomap exists (Kraus et al., Theorem 16, recorded at
`dev/literature/truncation-and-selection.md:157-165`). The greedy
construction from two well-orders fails at `ω · 2` into `ω`
(`dev/literature/truncation-and-selection.md:332-337`). The live
tree has well-orders on stages and on ordinals, not on ambient
function types. Nothing makes a canonical choice possible at this
type.

`swo-into-ord` on the DOMAIN `⟪ fst a ⟫`, which does carry `ordSWO`,
would inject `a` into SOME ordinal of the same order type, not into
the least cardinal. That is the identity embedding when the rank is
membership. It is not `α ↪ κ`.

## W2

Generic in `a`. The hypotheses are generic. No cardinal and no
numeral except `ω`, which this file does not name in any type.
W2 holds. There is no conflict with a deadline: the data form is
not inhabited.

## W3: device-covers-carrier

**NO-GO.** The widest unmeasured term was whether `swo-into-ord`
covers this carrier. The probe is `device-covers-carrier`
(`Probe422.agda:61-65`). One device, one fragment, one run.

```
device-covers-carrier a oa =
  swo-into-ord {A = ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫} (ordSWO (fst a) oa)
```

Elaboration error, `UnequalTerms`, at `Probe422.agda:65.55-72`
(`runs/w3-3.out`, exit 42, 1.05 s real):

```
when checking that the inferred type of an application
  SWO ⟪ fst a ⟫
matches the expected type
  SWO (⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)
```

The device does not cover this carrier. The delivered `SWO` is on
the domain. The carrier is the type of injections.

## PROBE

All in `agents/tasks/LJ-1-422/Probe422.agda`, module
`LJ-1-422.Probe422 {ℓ} (lem)`.

Predecessor `[LJ-1.406]`, opened as the slot clause requires.
Verdict **GO** (`agents/tasks/LJ-1-406/lj-1.406-report.md:13`).
Types that typechecked:

```
κL  : (a : S) (oa : IsOrd (fst a)) → S
κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa))
```

at `Probe406.agda:82` and `:85`. The truncated arrow `κ-injL` is at
`:88`. The report does not name the untruncated form FALSE. It
names it unused: "Nothing in this file untruncates anything"
(`lj-1.406-report.md:16-17`). I take those types as hypotheses. I
do not inhabit the truncated arrow as data.

Predecessor `[LJ-1.417]`, opened. Verdict **GO**. Type as above.
I do not import `Probe417`. I do not rebuild the rank.

- `_↪_` (`Probe422.agda:42-43`), as Cardinal writes it.
- Four module hypotheses (`:49-54`): `κL`, `κoL` at 406's types;
  `swo-into-ord` at 417's type with `S` written as `V ℓ`;
  `ordSWO` at `src/L/Ordinal/SquareLaw.lagda.md:176`.
- `device-covers-carrier` (`:61-65`), the W3 fragment.
- `kappa-arrow-data` (`:70-74`), the same application at the named
  target. Not inhabited.

Non-blank code lines of the fragment: eight, from the W3
application through the obligation (`:61-65` and `:70-74`, comments
and blanks excluded from the count of the two bodies). The estimate
was about 8 if none does. The measured error is a type mismatch at
the SWO argument, not a heap event.

`[LJ-1.418]` instantiated `swo-into-ord` at every stage
(`agents/tasks/LJ-1-418/lj-1.418-report.md:19-24`). That term is
`⟪ Lset α ⟫ ↪ ⟪ β ⟫` for SOME `β`. It does not name `κL`. It does
not well-order the injection type. I did not import `Probe418`.

## WHAT A GO WOULD HAVE PAID, AND WHAT THIS NO-GO SAYS INSTEAD

A GO would have paid `[LJ-1.421]`'s hypothesis: the least-cardinal
arrow as data. This NO-GO says that hypothesis is not a live
untruncation. It is a well-order on the injections, which the tree
does not have.

That is an architecture fact, not a route fact. The two-tower
candidate's J-side generation data well-orders stages. It does not
well-order ambient `_↪_`. The archived condensation chapter is the
recognition step of a collapse, not that well-order.

## W4

No module was retired. Nothing moved to `archive/`.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root. I did not
set `GHCRTS`. No heap event. `ps` showed only
`scripts/ops/agda-watchdog.sh`, no Agda binary, before the run.

- First run, `S` taken from `𝒮ᵥ`: `UnequalTerms` at `:50.34-35`,
  `V ℓ !=< Σ`, 0.75 s (`runs/w3-1.out`). Carrier error in the
  hypothesis telescope. Not the W3 measurement.
- Second run, `S` from `𝒮ʟ` but `swo-into-ord`'s `β` still in `S`:
  `UnequalTerms` at `:53.37-38`, L-carrier `!=< V ℓ`, 0.78 s
  (`runs/w3-2.out`). Predecessor type of `[LJ-1.417]` uses `𝒮ᵥ.S`.
  Not the W3 measurement.
- Third run, hypotheses at the predecessor types: `UnequalTerms` at
  `Probe422.agda:65.55-72`, `SWO ⟪ fst a ⟫` against
  `SWO (⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)`, **1.05 s** real, exit 42
  (`runs/w3-3.out`). Printed `Checking`. This is the W3 measurement.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: declined. It is the archived
  dispatch index. This task names a live untruncation device, not a
  historical dispatch row. Not used.
- `archive/dev/JOURNAL-archived.md`: declined. It is the retired-route
  journal. The device question is answered from literature and from
  live `src/`. Not used.
- `archive/dev/JOURNAL.md`: declined. It is the archived per-episode
  journal. The history of this campaign is the task directories. Not
  used.
- `dev/ARCHIVE.md`: declined. This task does not retire a module. Not
  used.
- `archive/dev/DD-archived.md`: declined. It is the archived DD
  ruling series. The live direction is `dev/pod/direction.md`. Not
  used.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:4`
  "The condensation lemma is the recognition step of constructibility theory."
  Read, as the brief required. Used: this is not the device the size
  theorem names.
- `archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:4`
  "The cardinal step of the later chapters needs one fact about ordinals that the"
  Read. Used: the archived pairing chapter is the order-type reading
  of Gödel pairing, a different arrow.
- `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md:6`
  "object is Devlin 5.4's size claim for the definable hull, |M| ="
  Read. Used: the archived counting chapter is hull-size, not
  `α ↪ κ`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:83`
  "So a proof that only needs cardinal arithmetic never needs an injection as"
  Read. Used: the orthodox conclusion is truncated.
- `dev/literature/truncation-and-selection.md:148`
  "A data payload does not come out."
  Read. Used: `leastOf` does not deliver this arrow as data.
- `dev/literature/truncation-and-selection.md:335`
  "A canonical injection needs a well-order on the INJECTIONS, which is"
  Read. Used: this is the missing device.
- `dev/literature/devlin-II5.md:413`
  "|L_α| = |α| for α ≥ ω"
  Read. Used: the theorem that names the size-equation arrow.
- `dev/literature/digest.md:58`
  "Q4 (the canonical well-order).** Stage-first, then minimal producer"
  Read. Used: the canonical well-order is the orthodox selection
  device, on the level, not on ambient injections.
- `dev/literature/glossary-review-2026-08.md`: declined. It is a
  review of glossary renderings. Not used.
- `dev/literature/geology.md`: declined. It is a geology-sources
  dossier (grounds, Hamkins). Not used.

SZ 1.17 was read in `dev/literature/j-hierarchy.md:147-149`, which
the injected candidate list did not name. The quote at `:147` is
"SZ 1.17 (p. 15) uses the well-order for the enumeration".
