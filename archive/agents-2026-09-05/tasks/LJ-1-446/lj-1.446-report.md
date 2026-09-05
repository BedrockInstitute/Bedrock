# LJ-1.446 report: the coded least cardinal is not below the ambient one

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-446/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-446/Probe446.agda`:

    kappaC-not-below :
        (a : S) (oa : IsOrd (fst a))
      → ⟨ fst (κC a oa) ∈ˢ fst (κL a oa) ⟩ → Empty.⊥

`κL` is the sealed ambient least cardinal, five projections, at
`agents/tasks/LJ-1-437/Probe437.agda:90-107`. `κC` is the coded
selection at `agents/tasks/LJ-1-431/Probe431.agda:126-134`. Nothing
lands in `src/`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict.

## PREDECESSOR VERDICTS, BEFORE ANY AGDA

- `[LJ-1.431]` `agents/tasks/LJ-1-431/lj-1.431-report.md:27` reads
  "**GO.** The obligation typechecks". Delivered type
  `agents/tasks/LJ-1-431/Probe431.agda:133-134`:
  `arrow-at-kappaC : ⟪ fst a ⟫ ↪ ⟪ fst κC ⟫`.
- `[LJ-1.438]` `agents/tasks/LJ-1-438/lj-1.438-report.md:73` reads
  "**GO.** `coded-nonempty` typechecks". Delivered type
  `agents/tasks/LJ-1-438/Probe438.agda:128-131`:
  `coded-nonempty : ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ ∥₁`.
- `[LJ-1.430]` `agents/tasks/LJ-1-430/lj-1.430-report.md:81` reads
  "**GO.** `coded-selects` typechecks". Delivered types
  `agents/tasks/LJ-1-430/Probe430.agda:89-90` `coded-selects` and
  `:96-98` `kappaC-ord : IsOrd (fst κC)`.

No predecessor report is NO-GO. No predecessor names the statement
FALSE. I take those types and those verdicts. I do not stop.

## D-10, BEFORE ANY AGDA

The two selections, written as types.

Ambient, `src/L/Cardinal.lagda.md:82-83`, inside `LeastCardInjL (α : S)`:

    InjP' : ⟪ sucV (fst α) ⟫ → hProp ℓ
    InjP' γ = InjP (up γ)

Coded, `agents/tasks/LJ-1-431/Probe431.agda:120-122`, inside
`module _ (a : S) ... (γ : V ℓ)`:

    CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
    CodedInjP' d =
      ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

They range over the SAME carrier `⟪ sucV (fst a) ⟫` when `α` is `a`.
The predicates differ (truncated ambient injection against truncated
coded existence) and the hProp levels differ (`ℓ` against `ℓ-suc ℓ`).
The carrier is the same, so the ordering question is the question
this brief asks. I do not stop.

The target is not false on a Tarskian or cardinality ground. Ambient
minimality already refuses an ambient injection into a strictly
smaller ordinal (`src/L/Cardinal.lagda.md:140-141`). A code yields
an ambient injection (`Probe431.agda:133-134`). Feeding that
injection to the ambient minimality is the one application the brief
names. Corrected target: none. Original target stands.

## VERDICT

**GO.** `kappaC-not-below` typechecks
(`agents/tasks/LJ-1-446/Probe446.agda:203-206`, exit 0, median 1.78 s
on three forced rechecks) and it PASSes the program's witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-446 --brief agents/tasks/LJ-1-446/LJ-1.446.md`, exit 0,
1.81 s, 0 UNRESOLVED of 1, `probe_red=False`). This worktree has no
`.venv`. The witness meter ran under the parent venv. I added no
dependency. I did not write `review-of-kappaC-not-below.md`. The
verdict is GO.

The exact type inhabited, so the next brief can quote it without
opening the probe, is at `Probe446.agda:203-206`, under
`module _ (a : S) (oa : IsOrd (fst a))` (`:117`) and
`module _ (coded-nonempty : ...)` (`:164-166`):

    kappaC-not-below :
        ⟨ fst κC ∈ˢ fst (κL a oa) ⟩ → Empty.⊥

`a` and `oa` are module parameters, the same packaging
`[LJ-1.431]` uses for `κC` (`Probe431.agda:130-131`). `κC` is a
local `S`, not a two-argument function. The application is
`κ-min-atL a oa κC κC∈κL ∣ arrow-at-kappaC ∣₁`
(`Probe446.agda:206`). That is the brief's one application. The
telescope of the brief names `κC a oa`; the probe names `κC` because
`a` and `oa` are already in scope. That is packaging, not a
weakening of the statement.

This GO says the coded least cardinal is not strictly below the
ambient one. It does not say the two are equal. It does not say the
coded route closes. C-42: a measurement of this site does not
measure the other direction.

## 1. W3: `plug`

**GO.** Typechecked ALONE, with the obligation omitted. Caliber
`-A64m -I0 -M8g`, set on the pane, untouched. One Agda process. The
probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-446/Probe446.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.04 | 391135232 |
| `runs/w3-2.out` / `w3-2.time` | 1.66 | 391135232 |
| `runs/w3-3.out` / `w3-3.time` | 1.69 | 391168000 |

Median wall **1.69 s**. Median peak RSS **391135232 bytes**. No heap
event.

The one line is `plug = coded-nonempty` at `Probe446.agda:169-170`.
`coded-nonempty` is a module hypothesis at `[LJ-1.438]`'s delivered
type (`Probe438.agda:128-131`, rebuilt at `:164-166`). `CodedInjP'`
is `[LJ-1.431]`'s spelling (`Probe431.agda:120-122`, rebuilt at
`:158-160`). `⟨ CodedInjP' d ⟩` is definitionally the inner
truncation of the 438 type. The elaborator printed `Checking` and
nothing else. There is no elaborator quote, because there was no
mismatch.

`γ` in this file is the 438 construction: `bound2 β (sucV stgG) oβ
(suc-ord oStg) .fst` at `Probe446.agda:132-136`, the same lines as
`Probe438.agda:72-76`. `upγ` is `x , Lset→isL γ oγ x m`
(`Probe446.agda:144-145`), the same line as `Probe431.agda:95-96`
and `Probe438.agda:86-87`. `upα` is the LeastCardInjL crossing
(`Probe446.agda:153-155`), the same three lines as
`Probe431.agda:112-114` and `Probe438.agda:101-103`. The two
rebuilds meet at every index that the types name.

`[LJ-1.431]` is generic in `γ` (`Probe431.agda:93`). This file
instantiates that `γ` at the 438 bound so the 438 payment can plug
in. W3 does not measure a generic ordinal. `[LJ-1.438]` already
recorded that its GO is at this bound and at no other
(`lj-1.438-report.md:225-227`).

## 2. The obligation

After W3 was green I added `isPropInjCode` (`Probe446.agda:71-84`),
`coded-to-arrow-at` (`:176-181`), the sealed `w` (`:185-187`),
`selected`, `κC`, `arrow-at-kappaC` (`:191-198`), and
`kappaC-not-below` (`:203-206`). I did not import
`LJ-1-431.Probe431`, `LJ-1-437.Probe437` or `LJ-1-438.Probe438`.

Three forced rechecks of the full file, probe interface deleted,
dependencies warm, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.78 | 402997248 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.80 | 403013632 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.78 | 403030016 |

Median wall **1.78 s**. Median peak RSS **403013632 bytes**. First
check after the obligation landed: 1.71 s, RSS 403030016
(`runs/full-1.out` / `full-1.time`), exit 0. No heap event.

W3's median was 1.69 s and 391135232 bytes. The obligation added
0.09 s and 11878400 bytes of peak RSS. It did not approach the 8 g
caliber.

P-l did not fire as a cost: `w` is sealed, and the types name
`⟪ sucV (fst a) ⟫`, which is the ambient site's own carrier
(`src/L/Cardinal.lagda.md:82-83`).

D-26 does not fire: the well-order is the delivered `ordSWO` on
members of an ordinal successor. I did not build a new well-founded
key.

What the shape resisted: nothing. The two spellings of the truncated
existence met. The one application typechecked as written. No
weakening. Nothing was left a hole.

Shape comparable, never a size comparable:
`agents/tasks/LJ-1-431/Probe431.agda` is the selection and the
arrow this file rebuilds, and `Probe437.agda:90-107` is the seal.
Nothing is funded against the estimate of about 150 lines.

## WHO OWES WHAT

`coded-nonempty` is a hypothesis in this file. I did not inhabit it.

| | this file | payer |
|---|---|---|
| name | `coded-nonempty` at `Probe446.agda:164-166` | `coded-nonempty` at `Probe438.agda:128-131` |
| report | this report, hypothesis | `agents/tasks/LJ-1-438/lj-1.438-report.md:73`, **GO** |
| type | `∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ ∥₁` | the same |

The two types agree. That is the W3 finding. `[LJ-1.438]` pays it at
the wide bound `γ = bound2 β (sucV stgG) oβ (suc-ord oStg) .fst`
(`Probe438.agda:72-76`, rebuilt at `Probe446.agda:132-136`). It does
not pay it at a generic ordinal, and it does not pay it at
`SiteBound.β`.

`arrow-at-kappaC` is rebuilt, not hypothesized. `[LJ-1.431]` is GO
on that term (`lj-1.431-report.md:27`). `κ-min-atL` is rebuilt from
the 437 seal (`Probe437.agda:104-107`). `[LJ-1.437]` is GO
(`agents/tasks/LJ-1-437/lj-1.437-report.md:17`).

## 3. What this term says, and what it does not

The term says: if `fst κC` is a member of `fst (κL a oa)`, then
`Empty.⊥`. For two ordinals that is: the coded least cardinal is not
strictly below the ambient one.

It does not say `fst κC ≡ fst (κL a oa)`. It does not say the
ambient least cardinal is not strictly below the coded one. It does
not close the coded route. Audit finding F5 measured that inflation
once (`dev/pod/audit-2026-08-20.md:76`).

What still stands:

- `coded-nonempty` remains a hypothesis. `[LJ-1.438]` pays it at
  this bound. This dispatch does not inhabit it.
- Equality of `κC` and `κL` is the remaining direction. This term
  is one half of that pair.
- An untruncated arrow at `κL` remains the campaign residue
  (`agents/tasks/LJ-1-421/lj-1.421-report.md:60`). C-42: this GO
  does not move that residue.

What the next brief needs: a term that the ambient least cardinal is
not strictly below the coded one, or a ruling that this one
direction is the relation the campaign uses. This term is not that
other direction.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. The inner module is generic in `a` and in `oa`
(`Probe446.agda:25`, `:117`). It names no cardinal, no band, no
numeral and no `ω` of this probe's own. `isPropInjCode` is generic
in `F a b`. `coded-to-arrow-at` does not know what `b` is. The
selection instantiates `b` at `κC`. Both proofs can share this code:
the carrier is one L-element, not a named cardinal. There is no
fixed form to report.

W4 does not fire: no module was retired.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`
  Read. `archive/dev/LJ-dispatch-index.md:1`
  quotes: # THE `LJ` DISPATCH INDEX, archived 2026-08-18
  Declined: archived dispatch rows. This task's live producer is
  `dev/pod/queue.toml`. The term does not consult a retired row.
- `archive/dev/JOURNAL-archived.md`
  Read. `archive/dev/JOURNAL-archived.md:1`
  quotes: # Archived journal: the retired route
  Declined: the retired journal does not measure this join of the
  two least cardinals.
- `archive/dev/JOURNAL.md`
  Read. `archive/dev/JOURNAL.md:1`
  quotes: # ARCHIVED 2026-08-20
  Declined: retired per-episode journal. The record of this task is
  this directory.
- `dev/ARCHIVE.md`
  Read. `dev/ARCHIVE.md:1`
  quotes: # ARCHIVE.md: the archive registry
  Declined: not used. No module was retired. W4 does not apply.
- `archive/dev/ORCHESTRATION.md`
  Read. `archive/dev/ORCHESTRATION.md:1`
  quotes: # ORCHESTRATION: the orchestrator's operating rules
  Declined: archived operating rules. The live loop is
  `dev/pod/README.md`. This probe does not consult it.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`
  Used. `dev/literature/truncation-and-selection.md:75`
  quotes: "**A cardinal inequality is a"
  The ambient minimality fires on a truncated injection
  (`src/L/Cardinal.lagda.md:140-141`). The coded arrow is data, so
  `∣_∣₁` is the only step (`Probe446.agda:206`).
  Also `dev/literature/truncation-and-selection.md:146`
  quotes: "**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`"
  and `dev/literature/truncation-and-selection.md:148`
  quotes: "index is a proposition. **A data payload does not come out.**"
  `CodedInjP'` is hProp-valued, so the index `κC` comes out. The
  ambient injection at `κL` stays truncated. Wrapping the coded
  arrow with `∣_∣₁` is how the two payloads meet.
- `dev/literature/devlin-II5.md`
  Used. `dev/literature/devlin-II5.md:129`
  quotes: "ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))"
  That is the classical least-witness guard. `κ-min-at` is that
  guard at the ambient predicate (`src/L/Cardinal.lagda.md:140-141`).
- `dev/literature/terms-2026-08.md`
  Read. `dev/literature/terms-2026-08.md:1`
  quotes: # The terminology dossier: fourteen renderings for the owner's ruling
  Declined: translation terms. This task writes no glossary entry.
- `dev/literature/digest.md`
  Read. `dev/literature/digest.md:1`
  quotes: # Digest: the orthodox form of the rud route, pinned from the collected literature
  Declined: rud-route digest, not this join.
- `dev/literature/geology.md`
  Read. `dev/literature/geology.md:1`
  quotes: # Geology dossier: set-theoretic geology sources and the five questions
  Declined: geology sources. This probe does not touch grounds or
  the mantle.
