# LJ-1.439 report: a limit ordinal above any ordinal, with successor closure

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-439/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-439/Probe439.agda`, at a
GENERIC ordinal `u : S`:

    limit-above :
        (u : S) → IsOrd u
      → Σ[ lam ∈ S ] ( IsOrd lam
                     × ⟨ u ∈ˢ lam ⟩
                     × ((d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) )

The witness is `+ω u` and nothing else.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:38`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict. Nothing was written into `src/`.

## D-10, BEFORE ANY AGDA

**The `opaque` block at `src/L/Ordinal/StageArith.lagda.md:44-78`
exports six names. Inventory:**

| name | line | kind |
|---|---|---|
| `+ω-in` | `:48` | introduction (puts a member of a finite iterate into the block) |
| `+ω-mem` | `:62` | introduction (puts the base into the block) |
| `+ω-sup` | `:65` | introduction (puts every member of the base into the block) |
| `+ω-iter` | `:68` | introduction (puts every finite iterate into the block) |
| `sucIter-ord` | `:72` | neither (ordinality of each iterate) |
| `+ω-ord` | `:76` | neither (ordinality of the block) |

**The block exports no elimination.** Four names put a set INTO the
block. Two names are ordinality facts. No exported name takes a
member out of the block.

That is an opinion until Route 1 is attempted. The attempt is the
measurement. The target is not false: the ω-block is a limit ordinal,
and `WithOut` inhabits the third conjunct once an elimination is
supplied (`Probe439.agda:133-135`, green at median 0.82 s). The
residue is a missing export, not a false statement.

## VERDICT

**NO-GO.** Route 1 through the six exported names does not inhabit
`plus-omega-suc`. The elaborator stops at
`agents/tasks/LJ-1-439/Probe439.agda:90.16-20` with
`UnsolvedInteractionMetas` (`runs/w3-alone-1.out:2-5`, exit 42).
`limit-above` is written at `Probe439.agda:176-181` as
`+ω u , (+ω-ord u ou , +ω-mem u , plus-omega-suc u ou)` and is
blocked by that hole. I did not inhabit a weaker type. I did not
unfold `+ω`. I did not edit `src/`.

The one declaration that closes Route 1 is in
`agents/tasks/LJ-1-439/review-of-limit-above.md`. It is a TYPE, to be
exported from the `unfolding +ω` block at
`src/L/Ordinal/StageArith.lagda.md` after `+ω-in` (`:48-59`).

## 1. W2 (DD4)

The mathematics is written once at a generic ordinal `u : S`. The
probe names no stage, no cardinal and no band. Finite iterate
indices `1`, `2` and `3` appear only as arguments of the exported
`+ω-iter` inside the Route 1 peel (`Probe439.agda:77`, `:94`,
`:99-102`). They are not a specialization of the statement. Both
proofs can share this code: the carrier is one ordinal, not a named
cardinal. No deadline asked for a fixed form.

## 2. W3: `plus-omega-suc`

**NO-GO.** Typechecked ALONE, with `limit-above` omitted. Caliber
`-A64m -I0 -M8g`, set on the pane, untouched. One Agda process.
The probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-439/Probe439.agdai`).

Three forced rechecks, exit 42 every time, each printed `Checking`
then the same hole:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-alone-1.out` / `w3-alone-1.time` | 1.11 | 281919488 |
| `runs/w3-alone-2.out` / `w3-alone-2.time` | 1.08 | 281919488 |
| `runs/w3-alone-3.out` / `w3-alone-3.time` | 1.07 | 282001408 |

Median wall **1.08 s**. Median peak RSS **281919488 bytes**. No heap
event.

The elaborator, at `runs/w3-alone-1.out:2-5`:

    error: [UnsolvedInteractionMetas]
    Unsolved interaction metas at the following locations:
      .../Probe439.agda:90.16-20

Line 90 is the inner hole of `eq-above`
(`Probe439.agda:87-90`). Context at that hole:

- `⟨ u ∈ˢ d ⟩`
- `⟨ d ∈ˢ +ω u ⟩`
- `sucV d ≡ +ω u`
- `⟨ sucV u ∈ˢ d ⟩`
- goal `⟨ sucV d ∈ˢ +ω u ⟩`

The statement is not false at this generality. The exports do not
name an iterate that `d` equals, so the next iterate cannot be
formed.

## 3. Route 1, and where it stops

Trichotomy on `d` and `u` (`ord-tri`,
`src/L/Ordinal/Linear.lagda.md:136`), with `IsOrd d` from `mem-ord`
(`src/L/Ordinal.lagda.md:221`) and `IsOrd (sucV d)` from `suc-ord`
(`src/L/Ordinal.lagda.md:96`).

**Case `d ∈ u`.** Closes. Trichotomy of `sucV d` against `u`:
membership goes in by `+ω-sup` (`Probe439.agda:65`); equality goes
in by `+ω-mem` (`:67`); `u ∈ sucV d` is irreflexive against
`d ∈ u` (`:68-73`).

**Case `d ≡ u`.** Closes. `sucV d` is `sucIter 1 u`, already in the
block by `+ω-iter 1` (`Probe439.agda:76-77`).

**Case `u ∈ d`.** Trichotomy of `sucV d` against `+ω u`.

- `sucV d ∈ +ω u`: the goal (`Probe439.agda:113`).
- `+ω u ∈ sucV d`: irreflexive. Either `+ω u ∈ d` and
  `d ∈ +ω u`, or `+ω u ≡ d` and `d ∈ +ω u` (`:104-110`).
- `sucV d ≡ +ω u`: the residue. Peel `sucIter 1`:
  `sucV u ∈ sucV d` by `+ω-iter 1` and the equality
  (`:93-94`). The branch `sucV u ≡ d` contradicts: it forces
  `sucIter 2 u ≡ +ω u`, then `sucV (+ω u) ∈ +ω u` by
  `+ω-iter 3`, then `+ω u ∈ +ω u` (`:95-102`). The remaining
  branch is `sucV u ∈ d`. **Route 1 stops there.**
  `Probe439.agda:90`. Another named iterate moves the hole. It
  does not close it.

## 4. Route 2: one export closes the residue

`module WithOut` (`Probe439.agda:128-170`) takes the archived
elimination as a module parameter and inhabits both
`plus-omega-suc-from-out` and `limit-above-from-out`. It is a
diagnostic. It is not the obligation.

Green, `limit-above` omitted, same caliber, interface deleted
before every kept run, three forced rechecks, exit 0 every time,
each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/without-1.out` / `without-1.time` | 1.21 | 282001408 |
| `runs/without-2.out` / `without-2.time` | 0.82 | 282017792 |
| `runs/without-3.out` / `without-3.time` | 0.82 | 281985024 |

Median wall **0.82 s**. Median peak RSS **282001408 bytes**. No heap
event.

The body is: eliminate `d` into some `sucIter (suc n) u`, then
compare `sucV d` with that iterate. Membership of the iterate
introduces by `+ω-in`. Equality of the iterate is `+ω-iter`.
The iterate sitting in `sucV d` is irreflexive against
`d ∈ sucIter n u`. No second ω-block.

## 5. What the next brief needs

- The obligation type is true and uninhabited from the live
  exports. Do not re-ask Route 1.
- Order one export in `src/L/Ordinal/StageArith.lagda.md`, inside
  the `opaque unfolding +ω` block, after `+ω-in`
  (`:48-59`). The type is in
  `review-of-limit-above.md`. Last green:
  `archive/src/2026-08-09-rud-route/L/Rud/OrdBlocks.lagda.md:107-108`.
- Once that name is in the seal, `WithOut`'s body
  (`Probe439.agda:133-170`) is the consumer proof. Measured at
  median 0.82 s on this pane, this caliber.
- Do not build a second ω-block. The witness stays `+ω u`.

## WHAT THIS DOES NOT MEASURE

This task asked for a limit ordinal above a given ordinal, with
successor closure. It measures that one conjunct against the live
`+ω` seal. It measures nothing else.

C-42: a measurement of one site does not measure how far that site
extends. After a GO, two hypotheses of the bounded-subset lemma
would still be owed:

- the absorption arrow, `src/L/BoundedSubset.lagda.md:1392`
  (`absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`);
- the membership of the subject in the stage,
  `src/L/BoundedSubset.lagda.md:1395`
  (`x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩`).

This return is a NO-GO, so those two stay owed, and the three
conjuncts of `limit-above` stay owed as well. The hull's use of
successor closure at `src/L/BoundedSubset.lagda.md:904` is not
discharged.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: not read. Declined. The
  obstruction is the live `+ω` seal, not a dispatch index.
- `archive/dev/JOURNAL-archived.md`: not read. Declined. The
  last-green elimination was taken from the archived master, not
  from a journal paragraph.
- `archive/dev/JOURNAL.md`: not read. Declined. Same reason.
- `dev/ARCHIVE.md`: not read. Declined. No `+ω-out` or
  `OrdBlocks` row was required to name the export.
- `archive/dev/TASKS-archived.md`: not read. Declined. The
  live brief named the file and the statement.

Read outside the candidate list, for the last-green type:
`archive/src/2026-08-09-rud-route/L/Rud/OrdBlocks.lagda.md:107-108`
reads `+ω-out : (u x : S) → ⟨ x ∈ˢ +ω u ⟩` and
`→ ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: not read.
  Declined. The residue is a missing elimination, not a
  truncation question.
- `dev/literature/devlin-II5.md`: not read. Declined. The
  statement is an Agda inhabitability measurement against a
  sealed union.
- `dev/literature/digest.md`: not read. Declined. Same reason.
- `dev/literature/fine-structure.md`: not read. Declined. Same
  reason.
- `dev/literature/devlin-errata.md`: not read. Declined. Same
  reason.
