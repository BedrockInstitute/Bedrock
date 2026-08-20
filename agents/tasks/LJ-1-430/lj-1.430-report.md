# LJ-1.430 report: select the least cardinal by the CODED predicate, on the AMBIENT carrier

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-430/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-430/Probe430.agda`, at a
GENERIC L-element `a : S` with `oa : IsOrd (fst a)`, at a GENERIC
ordinal `γ` with `oγ : IsOrd γ`, and with ONE bare module hypothesis
`nonempty-coded`:

    kappaC-ord : IsOrd (fst κC)

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:38`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict. Nothing was written into `src/`.

## D-10, BEFORE ANY AGDA

Two selections sit in `src/L/Cardinal.lagda.md`. Each gives one of the
two properties the descent needs, and each withholds the other.

| | ambient, `:116-134` | internal, `:235-263` |
|---|---|---|
| carrier | `⟪ sucV (fst α) ⟫` (`:119`) | `Mem (Lset β)` (`:249`) |
| predicate | truncated ambient injection, `hProp ℓ` (`:82-83`) | coded existential, `hProp (ℓ-suc ℓ)` (`:239-240`) |
| gives | `IsOrd` in two lines, `mem-ord` along `member (sucV (fst α)) γ-card` (`:125-127`) | a CODE, the shape `[LJ-1.424]` untruncates |
| withholds | the payload stays truncated, still not an hProp (`:132-133`) | ordinality: `Good` has no `IsOrd` conjunct (`:239-240`) |

`[LJ-1.427]` measured the internal gap and returned NO-GO
(`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-427/agents/tasks/LJ-1-427/lj-1.427-report.md:59`).
That report's W3 type is `IsOrd (fst δᴸ)` with a hole
(`Probe427.agda:74-76`). `mem-ord` does not apply: the container is
`Lset β`, not `sucV` of an ordinal
(`src/L/Cardinal.lagda.md:249-254`). A corrected `Good` with an added
conjunct would select a different object
(`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-427/agents/tasks/LJ-1-427/lj-1.427-report.md:46`).
This task adds no conjunct. It moves the carrier. This worktree's
`dev/pod/transitions/2026-08.jsonl` ends at line 158 and does not
record that instance.

This task's pair of choices is the ambient carrier with the coded
predicate. No selection in `src/` has that pair.

**THE ONE THING THIS TASK CAN FAIL ON.** `leastOf` takes its predicate
at an arbitrary level `ℓ''` and its `LEM` at
`ℓ-max ℓc (ℓ-max ℓₚ ℓ'')` (`src/L/WellOrder/Base.lagda.md:158`).
The chapter's `lem` is `LEM (ℓ-suc ℓ)` (`src/L/Cardinal.lagda.md:10`).
On this carrier `ℓc = ℓ` (`⟪ sucV (fst a) ⟫ : Type ℓ`). The sealed
order has `ℓₚ = ℓ-suc ℓ` (`src/L/Cardinal.lagda.md:25-26`,
`src/L/Ordinal/SquareLaw.lagda.md:148`). The coded predicate is
`hProp (ℓ-suc ℓ)`, so `ℓ'' = ℓ-suc ℓ`. The max of those three is
`ℓ-suc ℓ`. Whether Agda accepts the chapter's `lem` at that max, on
this mixed pair, is not stated in the tree. That is W3. If the
elaborator refuses the level, that is the NO-GO and it closes this
route in one dispatch.

The target `IsOrd (fst κC)` is not false. Ordinality of a selected
index on `⟪ sucV (fst a) ⟫` does not depend on the predicate: the
index is a member of `sucV (fst a)`, that set is an ordinal by
`suc-ord oa`, and `mem-ord` applies
(`src/L/Ordinal.lagda.md:221`). The residue is the level of
`leastOf`, not the truth of ordinality. Corrected target: none.
Original target stands.

`nonempty-coded` is a hypothesis. I do not inhabit it. `[LJ-1.429]`
owes it. I did not import that task's probe. I did not copy a type
out of its brief. I do not assert its statement.

A cardinal inequality is truncated existence of an injection
(`dev/literature/truncation-and-selection.md:75`). `leastOf`
delivers the least index untruncated; a data payload does not come
out (`dev/literature/truncation-and-selection.md:148`). The
coded payload is an hProp, so it may come out with the index.

## VERDICT

**GO.** `coded-selects` typechecks
(`agents/tasks/LJ-1-430/Probe430.agda:89-90`, exit 0, median 1.53 s
on three forced rechecks). `kappaC-ord` typechecks
(`Probe430.agda:96-98`, exit 0, median 1.57 s on three forced
rechecks). The witness meter PASSes
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-430 --brief agents/tasks/LJ-1-430/LJ-1.430.md`, exit 0,
1.61 s, 0 UNRESOLVED of 1, `probe_red=False`). This worktree has no
`.venv`. The witness meter ran under the parent venv. I added no
dependency.

The chapter's `lem` covers `leastOf`'s level at this carrier and
this predicate. The elaborator asked for
`LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))` at
`src/L/WellOrder/Base.lagda.md:158`. It has `LEM (ℓ-suc ℓ)` at
`Probe430.agda:25` and `src/L/Cardinal.lagda.md:10`. With
`ℓc = ℓ`, `ℓₚ = ℓ-suc ℓ`, `ℓ'' = ℓ-suc ℓ`, that max is `ℓ-suc ℓ`.
No universe-level error was printed.

The ambient site's two lines transfer unchanged. `kappaC-ord` is
`mem-ord {A = sucV (fst a)} (suc-ord oa) (fst κC)
(member (sucV (fst a)) (fst selected))`
(`Probe430.agda:97-98`), the same shape as
`src/L/Cardinal.lagda.md:126-127`.

This GO repairs `[LJ-1.427]`'s obstruction at its root: ordinality
comes from membership in `sucV (fst a)`, not from a conjunct on the
predicate. C-42: a measurement of this site does not measure
`nonempty-coded`, and it does not measure `readL` at this `γ`.

## 1. What was built

All in `agents/tasks/LJ-1-430/Probe430.agda`, module
`LJ-1-430.Probe430 {ℓ} (lem)`. Generic in `a` and in `γ`. I did not
open `LeastCardInjL`. I did not open `SiteBound`. I imported
`InjCode` only from `L.Cardinal` (`:38`).

- `hSucα` and `upα` (`:60-66`), LeastCardInjL's crossing rebuilt at
  the call site from `src/L/Cardinal.lagda.md:72-80`.
- `w` sealed (`:73-75`), `ordSWO (sucV (fst a)) (suc-ord oa)`, the
  same seal as `src/L/Cardinal.lagda.md:90-92`.
- `upγ` (`:79-80`), SiteBound.up's one line restated at `γ` and `oγ`
  (`src/L/Cardinal.lagda.md:171-172`).
- `CodedInjP'` (`:82-83`) at `hProp (ℓ-suc ℓ)`.
- One module hypothesis `nonempty-coded` (`:86`). Not inhabited.
- W3: `coded-selects` (`:89-90`).
- Obligation: `selected`, `κC`, `kappaC-ord` (`:93-98`).

## 2. W3: `coded-selects`, first

**GO.** Typechecked ALONE, obligation omitted, result discarded.
Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One Agda
process. The probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-430/Probe430.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.55 | 395329536 |
| `runs/w3-2.out` / `w3-2.time` | 1.53 | 395345920 |
| `runs/w3-3.out` / `w3-3.time` | 1.52 | 395313152 |

Median wall **1.53 s**. Median peak RSS **395329536 bytes**. No heap
event.

The mixed pair fits `leastOf`'s level. The predicate is
`hProp (ℓ-suc ℓ)`. The carrier is `Type ℓ`. The chapter's `lem` is
`LEM (ℓ-suc ℓ)`. Neither NO-GO condition fired.

## 3. The obligation

After W3 was green I added `mem-ord` to the import and wrote
`selected`, `κC` and `kappaC-ord` (`:93-98`). The two lines
transfer unchanged. The elaborator printed `Checking` and nothing
else.

Three forced rechecks of the full file, probe interface deleted,
dependencies warm, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1` | 1.57 | 395378688 |
| `runs/full-recheck-2` | 1.58 | 395345920 |
| `runs/full-recheck-3` | 1.53 | 395329536 |

Median wall **1.57 s**. Median peak RSS **395345920 bytes**. First
check after the obligation landed: 1.57 s, exit 0,
`runs/full-1.out`. No heap event.

P-l did not fire as a cost: `w` is sealed, so `leastOf w` is a
stuck atom. The types name `⟪ sucV (fst a) ⟫`, which is the ambient
site's own carrier.

D-26 does not fire: the well-order is the delivered `ordSWO` on
members of an ordinal successor. Those members carry membership in
an ordinal, which is the data `mem-ord` reads. I did not build a
new well-founded key.

## 4. Extra hypotheses

One: `nonempty-coded` (`Probe430.agda:86`). `[LJ-1.429]` owes it.
I did not inhabit it.

## W2 (DD4)

Everything is written once at a generic carrier. The module is
generic in `ℓ`. The inner module is generic in `a` and in `γ`. No
cardinal, no band, no numeral and no `ω` occurs in the probe. The
term does not know what `γ` is. There is no fixed form to report.

W4 does not fire: no module was retired.

## 5. What the selected `κC` still owes before it can serve as a descent target

A GO here delivers `IsOrd (fst κC)` from the ambient carrier. That
is the property `[LJ-1.427]` could not get from `δᴸ`. It is not a
descent.

`[LJ-1.421]`'s `descent-from-data` still needs, at the target:

- a split `(fst κC ≡ x) ⊎ ⟨ fst κC ∈ x ⟩`. That split spends
  `ord-tri`, which needs `IsOrd` on both sides. `kappaC-ord` is
  that certificate at `κC`. The split itself is not in this probe.
- an untruncated arrow `⟪ fst a ⟫ ↪ ⟪ fst κC ⟫`. The payload this
  selection returns is
  `∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a κC ∥₁`
  (`CodedInjP'` at `Probe430.agda:82-83`). That is a truncated
  code at a GENERIC `γ`. `[LJ-1.424]` untruncates a code at
  `SiteBound.β` of the domain, which is a different stage. A
  measured cure does not transfer by analogy. The next brief must
  re-measure `readL` at this `γ`, or instantiate `γ`.
- infiniteness, and `Init` at `κC` in the self-cardinal case.
  Neither is in this probe.
- minimality clauses. The brief dropped them.

`IsCardinalL` at `κC` is not delivered. `nonempty-coded` remains
owed by `[LJ-1.429]`.

Shape comparable, never a size comparable:
`src/L/Cardinal.lagda.md:82-127` is the ambient selection with its
seal and its ordinality. This probe is that block with one
predicate replaced and the minimality clauses dropped
(`Probe430.agda:56-98`). Nothing is funded against the estimate.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined: it is the retired dispatch index, not a measurement of `leastOf`'s level.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined: the retired journal does not measure this mixed pair.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Not used. W4 does not fire. No module was retired.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined: per-episode journal, not this selection.
- `archive/dev/STATUS-archived.md:1`, read: "# STATUS-archived: the goal table of the internalization route". Declined: internalization-route status table, not this site.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:75`, read: "**A cardinal inequality is a". Also `:148`, read: "**A data payload does not come out.**". The coded predicate is an hProp, so the index and the truncated code both come out.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined: condensation, not the mixed-pair level.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined: terminology dossier, not this selection.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions". Declined: geology, not this site.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined: rud-route digest, not this mixed pair.
