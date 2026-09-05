# LJ-1.438 report: pay the bare hypothesis that four delivered probes carry

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-438/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-438/Probe438.agda`, at a
GENERIC L-element `a : S` with `oa : IsOrd (fst a)`:

    coded-nonempty :
      ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ]
          ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ ∥₁

`γ` and `upγ` are rebuilt from `[LJ-1.429]`. `upα` is rebuilt from
`[LJ-1.430]`. The module takes `lem` and `ℓ` and nothing else.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict. Nothing was written into `src/`.

## D-10, BEFORE ANY AGDA

Which conjuncts of `InjCode` (`src/L/Cardinal.lagda.md:223-228`)
mention the THIRD argument, and through what.

`InjCode F a b` is four conjuncts.

- `:225` `⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩`. Names `F` and `a`. Does not
  name `b`.
- `:226` `⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩`. Names `F` and
  `a`. Does not name `b`.
- `:227` `⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩`. Names `F` and `a`. Does not
  name `b`.
- `:228` `((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)`.
  Names `b` at the last atom, and only as `fst b`.

No conjunct reads more of the third argument than its `fst`. A `subst`
on `fst` can carry a code from `a` to `upα self`. The route is not
refuted at this check. I do not stop.

Predecessor reports, opened before any Agda.

- `[LJ-1.429]` is GO, not NO-GO, not FALSE
  (`agents/tasks/LJ-1-429/lj-1.429-report.md:85`). The type that
  typechecked is `id-code-wide` at
  `agents/tasks/LJ-1-429/Probe429.agda:97`. I take that type and that
  verdict. The third argument there is `a`, the site.
- `[LJ-1.430]` is GO (`agents/tasks/LJ-1-430/lj-1.430-report.md:81`).
  It does not inhabit `nonempty-coded`. The hypothesized type is at
  `agents/tasks/LJ-1-430/Probe430.agda:86`. That is this task's
  target, written as `⟨ CodedInjP' d ⟩`.
- `[LJ-1.431]` is GO (`agents/tasks/LJ-1-431/lj-1.431-report.md:27`).
  It takes the same hypothesis bare. It does not inhabit it.
- `[LJ-1.432]` is GO (`agents/tasks/LJ-1-432/lj-1.432-report.md:63`).
  It stands on `[LJ-1.431]`'s conclusion. It does not inhabit this
  type.

No predecessor names this statement FALSE. I inhabit the type the
brief named.

The target is not false on a Tarskian or cardinality ground. The site
is a member of its own successor (`src/V/Model.lagda.md:236`). The
fiber of that membership is a member of `⟪ sucV (fst a) ⟫`
(`src/L/Cardinal.lagda.md:103-107`). The identity code at the site is
delivered (`Probe429.agda:97`). The remaining step is the `subst` on
`fst`. Corrected target: none. Original target stands.

## VERDICT

**GO.** `coded-nonempty` typechecks
(`agents/tasks/LJ-1-438/Probe438.agda:128-131`, exit 0, median 4.67 s
on three forced rechecks) and it PASSes the program's witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-438 --brief agents/tasks/LJ-1-438/LJ-1.438.md`, exit 0,
1.66 s, 0 UNRESOLVED of 1, `probe_red=False`). This worktree has no
`.venv`. The witness meter ran under the parent venv. I added no
dependency. I did not write `review-of-coded-nonempty.md`. The
verdict is GO.

The exact type inhabited, so the next brief can quote it without
opening the probe, is at `agents/tasks/LJ-1-438/Probe438.agda:128-131`:

    coded-nonempty :
      ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ]
          ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ ∥₁

That is the type `[LJ-1.430]` hypothesized at
`agents/tasks/LJ-1-430/Probe430.agda:86` as `nonempty-coded`, with
`⟨ CodedInjP' d ⟩` the inner truncation at `:83`. It is the type
`[LJ-1.431]` takes bare as well. The inhabitant is
`∣ self , ∣ Fg , moved ∣₁ ∣₁` at `Probe438.agda:131`. `γ` is the
wide bound built FROM the graph, `bound2 β (sucV stgG) oβ (suc-ord oStg) .fst`
at `Probe438.agda:72-76`.

This GO retires that hypothesis AT THIS BOUND. `[LJ-1.430]`,
`[LJ-1.431]` and `[LJ-1.432]` become unconditional when they
instantiate `γ` to this wide bound. They do not become unconditional
at a generic ordinal, and they do not become unconditional at
`SiteBound.β`.

## 1. W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. The inner module is generic in `a` and in `oa`
(`Probe438.agda:23`, `:57`). It names no cardinal, no band, no
numeral and no `ω` of this probe's own. The `ω` inside `stageBound`
is the chapter's. This probe does not write it. Both proofs can share
this code: the carrier is one L-element, not a named cardinal. There
is no fixed form to report.

W4 does not fire: no module was retired.

## 2. W3: `code-target-swap`

**GO.** Typechecked ALONE, with the graph, `γ` and the obligation
omitted. Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One
Agda process. The probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-438/Probe438.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.61 | 399212544 |
| `runs/w3-2.out` / `w3-2.time` | 1.63 | 399245312 |
| `runs/w3-3.out` / `w3-3.time` | 1.52 | 399196160 |

Median wall **1.61 s**. Median peak RSS **399212544 bytes**. No heap
event.

The inhabitant is a four-tuple. The first three conjuncts are copied.
The fourth is `subst (λ v → ⟨ fst y ∈ v ⟩) e (ran x y p)`. No
conjunct of `InjCode` refused the `subst` on `fst`. Neither NO-GO
condition fired. The elaborator printed `Checking` and nothing else.

## 3. Graph RSS, before the swap is added

The graph was typechecked ALONE, with `code-target-swap` and the
obligation omitted. Same caliber, one process, interface deleted
before every kept run. Exit 0 every time. Each printed `Checking`.
No heap event. The 8 g `Small` warning at
`src/L/InjChain.lagda.md:552-553` did not fire: this probe does not
unfold the sealed `incl`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/graph-1.out` / `graph-1.time` | 1.60 | 405667840 |
| `runs/graph-2.out` / `graph-2.time` | 1.58 | 405684224 |
| `runs/graph-3.out` / `graph-3.time` | 1.58 | 405667840 |

Median wall **1.58 s**. Median peak RSS **405667840 bytes**.

Against W3's median 399212544 bytes the graph added 6455296 bytes of
peak RSS. It did not approach the 8 g caliber.

## 4. The obligation

After W3 was green and the graph RSS was recorded, I wrote `hSucα`
and `upα` (`Probe438.agda:97-103`), copied from
`Probe430.agda:60-66`, then `self` and `self-eq` (`:115-119`), the
two lines at `src/L/Cardinal.lagda.md:103-107`, then `id-code` and
`moved` (`:122-126`), then `coded-nonempty` (`:128-131`). I did not
import `LJ-1-429.Probe429`, `LJ-1-430.Probe430` or
`LJ-1-431.Probe431`. The rebuilt lines are:

- graph, bound, `upγ`, `Fg`: `Probe438.agda:59-93` from
  `Probe429.agda:53-95`
- `hSucα`, `upα`: `Probe438.agda:97-103` from
  `Probe430.agda:60-66`
- `self`, `self-eq`: `Probe438.agda:115-119` from
  `src/L/Cardinal.lagda.md:103-107`

`self-eq` is `⟪ sucV (fst a) ⟫↪ self ≡ fst a`. `fst (upα self)` is
that same embedding, so `fst a ≡ fst (upα self)` is `sym self-eq`.
`moved` is `code-target-swap (upγ Fg) a (upα self) (sym self-eq) id-code`
(`Probe438.agda:126`).

Three forced rechecks of the full file, probe interface deleted,
dependencies warm, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 4.67 | 1297301504 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 4.69 | 1297350656 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 4.61 | 1297285120 |

Median wall **4.67 s**. Median peak RSS **1297301504 bytes**. First
check after the obligation landed: 4.58 s, exit 0,
`runs/full-1.out`, peak RSS 1297268736 bytes. No heap event.

The swap alone was 1.61 s and 399212544 bytes. The graph alone was
1.58 s and 405667840 bytes. Together with `upα` and the four
conjuncts the full file is 4.67 s and 1297301504 bytes. That is the
price of inhabiting the identity code and moving it onto the ambient
carrier in one module. It is under the 8 g caliber. It is not a WALL.

P-l did not fire as a cost unique to this probe: the types name
`⟪ sucV (fst a) ⟫`, which is the ambient site's own carrier
(`src/L/Cardinal.lagda.md:103-112`).

D-26 does not fire: this task does not well-order a stage. The
well-order sits in `[LJ-1.430]`, not here.

What the shape resisted: the `subst` on `fst` did not resist. The
four conjuncts did not resist. Combining `InclGraph` with
`ord∈Lset-suc` and the inhabitant of `InjCode` raised peak RSS from
405667840 bytes to 1297301504 bytes. Nothing was weakened to avoid that.
Nothing was left a hole.

Shape comparable, never a size comparable:
`agents/tasks/LJ-1-429/Probe429.agda` is the graph and the wide
bound, and `src/L/Cardinal.lagda.md:103-114` is the `self` device.
Nothing is funded against the estimate of about 65 code lines.

## 5. Extra hypotheses

None. `coded-nonempty` is inhabited. The predecessors carried it as
a module hypothesis. This task pays it at the wide bound.

## WHAT THIS DOES NOT MEASURE

A GO here pays the hypothesis AT THE WIDE BOUND `γ` and at no other
bound. `γ` is `bound2 β (sucV stgG) oβ (suc-ord oStg) .fst`
(`Probe438.agda:72-76`). It is not `SiteBound.β`.

The site bound that `[LJ-1.425]` measured is
`src/L/Cardinal.lagda.md:163-172`: `β = stageBound (fst a) (snd a) .fst`
at `:165-166`, with `up` at `:171-172`. That return was NO-GO on the
same shape (`agents/tasks/LJ-1-425/lj-1.425-report.md:57` reads
`**NO-GO on `internal-nonempty`. GO on `κ-in-site-bound`. GO on W3's`).
A GO here does not overturn that. It measures a different bound.

C-42: this GO does not measure `Canonical.Good` at `β`. It does not
measure `InternalLeastCard.Good` at `β`. It does not measure
`nonempty-coded` at a generic `γ`. `[LJ-1.430]` is generic in `γ`
(`Probe430.agda:56`). This inhabitant is at one constructed `γ`.

## W4

No module was retired. Nothing moved to `archive/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined: it is the retired dispatch index, not a measurement of the `subst` on `fst`.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined: the retired journal does not measure this bound.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Not used. W4 does not fire. No module was retired.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined: per-episode journal, not this selection.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the D series". Declined: archived D series, not the coded nonempty.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:75`, read: "**A cardinal inequality is a". Also `:148`, read: "**A data payload does not come out.**". The payload here is truncated existence of a code, which is a proposition, so it comes out with `self`.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined: condensation, not the `subst` on `fst`.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined: rud-route digest, not this bound.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic geology sources and the five questions". Declined: geology, not this site.
- `dev/literature/devlin-errata.md:1`, read: "# Devlin errata: documented error classes (do-not-repeat checklist)". Declined: errata checklist, not this inhabitant.

