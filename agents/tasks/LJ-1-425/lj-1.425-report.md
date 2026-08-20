# LJ-1.425 report: unlock the internal least cardinal, with the identity graph

slot: `coder`. Written early as a skeleton and filled as answers land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-425/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`. I did
not set `GHCRTS`. One Agda process at a time. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-425/Probe425.agda`, at a
GENERIC L-element `κ : S` with its ordinal certificate `oκ` as module
parameters, with `L.Cardinal`'s own site bound in scope (`open SiteBound κ`,
`src/L/Cardinal.lagda.md:163`):

    internal-nonempty :
      ∥ Σ[ δ ∈ Mem (Lset β) ]
          ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ ∥₁

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work. It
does not start that collection. It does not start phase 3. No Boundary
clause is in conflict. Nothing was written into `src/`.

## D-10, BEFORE ANY AGDA

The statement is an existence claim over a bounded stage. It is true
only if BOTH `κ` and a code `F` are members of `Lset β`.

`β` is `stageBound (fst κ) (snd κ) .fst`
(`src/L/Cardinal.lagda.md:166`). That device is `bound2 ω (stage κ)`
(`src/L/Choice/Stage.lagda.md:366-368`). `bound2` is `boundingOrd` on
a two-element family (`src/L/Ordinal.lagda.md:185-196`), so `β` is
the union of `sucV ω` and `sucV (stage κ)`. It contains `ω` and
`stage κ`. It does not contain `sucV (stage κ)`.

Carve's bound is a sealed `boundingOrd` over the pair family
(`src/L/InjChain.lagda.md:75-93`). The tree states no comparison
between those two bounds.

The chapter that places ordered pairs on the tower says they appear
two stages up: `pr∈Lset-suc`
(`src/L/Axioms/Basic.lagda.md:596-597`). The identity graph's members
are those pairs. At a successor `stage κ` above `ω`, `Lset β` is
`𝒟ₒ (Lset (stage κ))` along `Lset-suc`
(`src/L/Axioms/Basic.lagda.md:196`). A member of `Lset β` is then a
definable subset of `Lset (stage κ)`. The pairs do not live in
`Lset (stage κ)`.

The site bound's one downward bridge is `bound-below₂`
(`src/L/Choice/Stage.lagda.md:370-373`): members of members of `κ`.
A pair is not a member of a member.

So `κ ∈ Lset β` is true. The identity graph as a member of `Lset β`
is false at this generality. The existence claim with that witness
is false as written.

## VERDICT

**NO-GO on `internal-nonempty`. GO on `κ-in-site-bound`. GO on W3's
implication `graph-in-site-bound`.**

- `κ-in-site-bound` is GREEN (`Probe425.agda:65-69`). It spends
  `stageBound (fst κ) (snd κ) .snd .snd .snd`
  (`src/L/Choice/Stage.lagda.md:366-368`) and `stage-mem`
  (`src/L/Stage.lagda.md:188`). `δκ` is `(fst κ , κ-in-site-bound)`
  (`Probe425.agda:71-72`).
- `graph-in-site-bound` is GREEN as an implication from
  `⟨ stage (fst G) (snd G) ∈ˢ β ⟩` (`Probe425.agda:49-54`). The
  unconditioned membership is not inhabited. The tree delivers no
  fact that pays the premise.
- `internal-nonempty` is a hole at `Probe425.agda:92`. Agda reports
  `UnsolvedInteractionMetas` (`runs/final-hole.out`, exit 42, 1.93 s).
  The obstruction is `review-of-internal-nonempty.md`. The `δ`
  conjunct is paid. The `F` conjunct is not.

InclGraph was not applied. D-10 stops the membership. The brief says
to stop in that case. Carve's private `Small` instance
(`src/L/InjChain.lagda.md:552-553`) is the 8g warning; this task does
not need `Small`.

## 1. W2

`GraphInSite`, `KappaInSite` and `Obligation` are generic in `κ`. The
ordinal certificate is a module parameter, as `InternalLeastCard`
states it (`src/L/Cardinal.lagda.md:235`). `GraphInSite` is also
generic in `G`. No cardinal, no band and no numeral is named. `ω`
does not appear in the probe. W2 holds.

## 2. W3: `graph-in-site-bound`

**The membership typechecks as an implication. The crossing fact is
none.**

Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One Agda
process. Dependencies warm. The probe interface was deleted before
every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-425/Probe425.agdai`).

W3 ALONE (file held only `module GraphInSite`, nothing carved, no
`InclGraph`), three forced rechecks, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.55 | 398868480 |
| `runs/w3-2.out` / `w3-2.time` | 1.57 | 398884864 |
| `runs/w3-3.out` / `w3-3.time` | 1.49 | 398786560 |

Median wall **1.55 s**. Median peak RSS **398868480 bytes**. No heap
event.

The inhabitant is `Lset-mono` plus `stage-mem`
(`Probe425.agda:52-54`). The premise is
`⟨ stage (fst G) (snd G) ∈ˢ β ⟩`. **No delivered fact pays that
premise.** The site bound compares `stage κ` with `β`
(`src/L/Choice/Stage.lagda.md:368`). It does not compare a graph's
stage, and it does not compare Carve's `boundingOrd`
(`src/L/InjChain.lagda.md:82`), with `β`.

## 3. The two memberships

`κ-in-site-bound` closed after W3, still with nothing carved
(`runs/kappa-1.out`, exit 0, 1.47 s, RSS 390529024). Same caliber,
one process, no heap event.

The graph membership did not close. That is the `F` hole.

## 4. What GO would earn, and what it costs

If `nonempty` were green, `InternalLeastCard.Selected` would deliver
`δᴸ` (`src/L/Cardinal.lagda.md:253`) and `δ-inj`
(`src/L/Cardinal.lagda.md:257`) by one `leastOf` at `orderAt β oβ`
(`src/L/Cardinal.lagda.md:247`). `δ-inj` is still truncated. No extra
term is built. That is the input `[LJ-1.424]` would consume. This
return does not unlock it.

## 5. Corrected statement

Quantify `Good` and `Selected` over a stage `γ` that contains both
`β` and `sucV (sucV (sucV (stage (fst κ) (snd κ))))`. Then
`pr∈Lset-suc` lands in `Lset (sucV (sucV (stage κ)))` and one `𝒟ₒ`
step puts the graph in `Lset (sucV (sucV (sucV (stage κ))))`.
`bound2` of those two ordinals is the shape the tree already has
(`src/L/Ordinal.lagda.md:185`).

The brief's priced alternative, re-carve the graph inside `Lset β`,
does not repair this witness. The pairs are not members of
`Lset (stage κ)`, so a separation from `Lset β` cannot keep them.
I did not attempt that alternative.

## 6. C-42

The refuted shape is: a graph, or an `InjCode` witness, as
`Mem (Lset β)` with `β` from `stageBound`.

COUNT in `src/`: **2**. Both in `src/L/Cardinal.lagda.md`.

| n | site | shape |
|---|---|---|
| 1 | `Canonical.Good` (`src/L/Cardinal.lagda.md:187-190`) | graph `A : Mem (Lset β)` with `svAt`/`domAt`/`injAt` |
| 2 | `InternalLeastCard.Good` (`src/L/Cardinal.lagda.md:239-243`) | `F : Mem (Lset β)` with `InjCode` |

`Selected` has no consumer in `src/` (`InternalLeastCard` occurs only
at `src/L/Cardinal.lagda.md:235` and `:242`). `InclGraph` has one
consumer, `OrdIncl` (`src/L/InjChain.lagda.md:607`), and that consumer
does not place `G` in `Lset (stageBound _)`.

A3's `Canonical` carries the same residue. A cure funded against A4
alone is priced against one of two sites.

## 7. W4

No module was retired. Nothing moved to `archive/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read. `:1` reads
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. It is the retired
  dispatch table. This task's code is not a row I needed. Not used
  beyond the heading.
- `archive/dev/JOURNAL-archived.md`: read. `:1` reads
  `# Archived journal: the retired route`. Declined: a dated record
  of the retired route, not the two bounds.
- `archive/dev/JOURNAL.md`: read. `:1` reads
  `# ARCHIVED 2026-08-20`. Declined: per-episode journal, retired.
  The product of this task sits in `agents/tasks/LJ-1-425/`.
- `dev/ARCHIVE.md`: read. `:1` reads
  `# ARCHIVE.md: the archive registry`. Declined: no module was
  retired, so no row is written.
- `archive/dev/STATUS-archived.md`: read. `:1` reads
  `# STATUS-archived: the goal table of the internalization route`.
  Declined: retired-route goal table, not the two bounds.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read and used.
  `:75` reads
  `13.20 (`dev/literature/devlin-II5.md:145-166`). **A cardinal inequality is a`.
  `:76` reads
  `truncated existence of an injection.** That is the HoTT Book's own definition,`.
  That is why `δ-inj` stays truncated at
  `src/L/Cardinal.lagda.md:257` even if `nonempty` were paid.
- `dev/literature/devlin-II5.md`: read. `:1` reads
  `# Devlin II.5: the Condensation Lemma and the GCH in L`.
  Declined: condensation and GCH, not the site-bound versus pair-stage
  comparison.
- `dev/literature/terms-2026-08.md`: read. `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined: glossary renderings, not used.
- `dev/literature/geology.md`: read. `:1` reads
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined: geology sources, not used.
- `dev/literature/digest.md`: read. `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined: rud-route digest, not used.
