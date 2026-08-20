# LJ-1.429 report: the identity code, at a bound built FROM the graph

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-429/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-429/Probe429.agda`, at a
GENERIC L-element `a : S`:

    id-code-wide : ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a a ∥₁

where `γ` is the ordinal this task DEFINES from the identity graph on
`a`, not `SiteBound`'s own `β`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:38`). This task is still LJ-1 work. It
does not start that collection. It does not start phase 3. No Boundary
clause is in conflict. Nothing was written into `src/`.

## D-10, BEFORE ANY AGDA

**Why this bound is admissible where `SiteBound`'s is not.**

`SiteBound.β` is `stageBound (fst a) (snd a) .fst`
(`src/L/Cardinal.lagda.md:165-166`). That device is
`bound2 ω (stage a p)` (`src/L/Choice/Stage.lagda.md:366-368`). It is
computed from `a` alone, before any graph exists. It contains `ω` and
`stage a`. The tree states no comparison between a graph's stage and
that `β`.

`[LJ-1.425]` measured that site and returned NO-GO on the existence
claim at `β`. Its W3 term `graph-in-site-bound` typechecked only as an
implication from `⟨ stage (fst G) (snd G) ∈ˢ β ⟩`
(`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-425/agents/tasks/LJ-1-425/Probe425.agda:49-54`).
The unconditioned membership was not inhabited. Verdict:
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-425/agents/tasks/LJ-1-425/lj-1.425-report.md:57-58`
reads `**NO-GO on `internal-nonempty`. GO on `κ-in-site-bound`. GO on W3's
implication `graph-in-site-bound`.**` That report names the statement
FALSE at that witness
(`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-425/agents/tasks/LJ-1-425/review-of-internal-nonempty.md:24`
reads `FALSE at this witness, at the intended generality. See`). This
task does not inhabit that type.

This task's `γ` is

    bound2 β (sucV (stage (fst G) (snd G))) oβ (suc-ord (stage-ord _ _)) .fst

It is computed AFTER `G` exists. `G` is an L-element
(`src/L/InjChain.lagda.md:479`). `stage (fst G) (snd G)` exists and is
an ordinal (`src/L/Stage.lagda.md:185`), and `G` is a member of that
stage (`src/L/Stage.lagda.md:188`). `bound2` returns an ordinal that
contains BOTH arguments, as a genuine pair
(`src/L/Ordinal.lagda.md:185-186`):

- it contains `β`, so nothing `SiteBound` proves is lost;
- it contains `sucV (stage G)`.

`self∈sucV` (`src/V/Model.lagda.md:236`) gives
`⟨ stage G ∈ˢ sucV (stage G) ⟩`. `IsOrd γ` includes `isTransV γ`
(`src/L/Constructible.lagda.md:141-142`). ONE transitivity step then
gives `⟨ stage G ∈ˢ γ ⟩`. `Lset-mono`
(`src/L/Constructible.lagda.md:355`) and `stage-mem`
(`src/L/Stage.lagda.md:188`) then put `G` in `Lset γ`. That is the
premise `[LJ-1.425]` could not pay.

This is not a comparison with `StageBound`'s sealed `boundingOrd`
(`src/L/InjChain.lagda.md:75-93`). That seal is not opened. The graph
is taken as an L-element and asked for its own stage.

**THE ONE THING THAT COULD STILL BE FALSE.** `bound2` needs `IsOrd` of
both arguments (`src/L/Ordinal.lagda.md:185`). `oβ` is
`SiteBound`'s `IsOrd β` (`src/L/Cardinal.lagda.md:168-169`).
`suc-ord (stage-ord (fst G) (snd G))` is `IsOrd` of
`sucV (stage (fst G) (snd G))` (`src/L/Ordinal.lagda.md:96` and
`src/L/Stage.lagda.md:185`). If those two certificates type as `IsOrd`
of those two arguments, `bound2` accepts them and the transitivity
step is one field projection. If `bound2` will not accept
`sucV (stage (fst G) (snd G))`, or the transitivity step does not
close, that is the NO-GO.

## VERDICT

**GO.** The obligation typechecks
(`agents/tasks/LJ-1-429/Probe429.agda:97-98`, exit 0, median 1.63 s on
three forced rechecks) and it PASSes the program's witness meter
(`python3 scripts/pod/witness.py --code LJ-1-429 --brief
agents/tasks/LJ-1-429/LJ-1.429.md`, exit 0, 1.64 s, 0 UNRESOLVED of 1,
`probe_red=False`). `.venv/bin/python` is absent in this worktree. The
witness meter ran under `python3`. I added no dependency.

`bound2` accepted `sucV (stage (fst G) (snd G))`. The transitivity
step closed. The four conjuncts come out at `G ∷ a ∷ []` with no
repackaging. `InjCode (upγ Fg) a a` accepted the raw tuple. No
`Σ≡Prop` was needed for the obligation. No hole. No
`review-of-id-code-wide.md`. The GO branch forbids that file.

This GO is at `γ`, a bound built FROM the graph. It is not a witness
at `SiteBound.β`. C-42: a measurement of one site does not measure
the other.

## 1. W2 (DD4)

The mathematics is written once at a generic carrier. `module _ (a : S)`
opens `SiteBound a` and instantiates `InclGraph a a (λ _ h → h)`
(`Probe429.agda:52-56`). It names no cardinal, no band, no numeral and
no `ω` of this probe's own. The `ω` inside `stageBound` is the
chapter's. This probe does not write it. Both proofs can share this
code: the carrier is one L-element, not a named cardinal.

## 2. W3: `stage-in-gamma`

**GO.** Typechecked ALONE, with the graph built and the `InjCode`
conjuncts omitted. Caliber `-A64m -I0 -M8g`, set on the pane,
untouched. One Agda process. The probe interface was deleted before
every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-429/Probe429.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.65 | 403341312 |
| `runs/w3-2.out` / `w3-2.time` | 1.61 | 403308544 |
| `runs/w3-3.out` / `w3-3.time` | 1.60 | 403324928 |

Median wall **1.61 s**. Median peak RSS **403324928 bytes**. No heap
event.

The inhabitant is `oγ .fst (self∈sucV stgG) (pair .snd .snd .snd)`
(`Probe429.agda:76-77`). `bound2` accepted both arguments
(`Probe429.agda:67-68`). `oβ` and `suc-ord oStg` typed as `IsOrd` of
those arguments. The one thing D-10 named as still possibly false
is not false. The transitivity step closed. Neither NO-GO condition
fired. The obstruction is not the seal at
`src/L/InjChain.lagda.md:75-93`. The ordinal arithmetic paid.

## 3. Step one: the graph and the four conjuncts

`InclGraph a a (λ _ h → h)` (`Probe429.agda:56`). Not `OrdIncl`.
`OrdIncl` derives its subset witness from a strict membership
`⟨ fst D ∈ fst C ⟩` (`src/L/InjChain.lagda.md:604-607`), and `a ∈ a`
is false.

The four conjuncts come out at `G ∷ a ∷ []` with no repackaging.
`Carve` sets `γI = G ∷ D ∷ []` (`src/L/InjChain.lagda.md:515-516`).
Here `D = a`, so `γI` is `G ∷ a ∷ []`. The tuple is

    IG.sv , IG.dm , IG.ij , IG.ran

which is `InjCode G a a` term for term
(`src/L/Cardinal.lagda.md:223-228`). The same assembly
`[LJ-1.326]` already typed at `OrdIncl`
(`agents/tasks/LJ-1-326/ProbeLJ1326A.agda:66-67`). Instantiating
`InclGraph` at the identity did not need a new packager.

## 4. Step three: packaging

`upγ` is `SiteBound.up` restated at `γ` and `oγ`
(`Probe429.agda:81-82`, against `src/L/Cardinal.lagda.md:171-172`).
`Fg = (fst G , mG)` (`Probe429.agda:89-90`). `mG` is `Lset-mono`
plus `stage-mem` (`Probe429.agda:86-87`), the implication
`[LJ-1.425]` already typed, now with the premise paid.

`G` and `upγ Fg` agree on `fst` and differ on the `isL` proof. They
are NOT equal definitionally as `S`. A `refl` test was checked once
and refused. The elaborator, at
`agents/tasks/LJ-1-429/runs/sigma-refl.out:2-10`, reported:

    error: [UnequalTerms]
    IG.G .snd != ∣ γ , oγ , Fg .snd ∣₁ of type
    ∥
    Σ (FOL.ZFStructure.ZFStructure.S 𝒮ᵥ)
    (λ x →
       ⟨ (IsOrd x , L.Constructible.isPropIsOrd x) ⊓ IG.G .fst ∈ˢ Lset x
       ⟩)
    ∥₁
    when checking that the expression refl has type G ≡ upγ Fg

That `refl` test is not in the final probe. One `Σ≡Prop` would close
`G ≡ upγ Fg`, because `isL` is a proposition
(`src/L/Constructible.lagda.md:376-377`). The obligation does not
need that path. `InjCode` mentions `F` at `fst F` and at
`(F ∷ a ∷ [])` (`src/L/Cardinal.lagda.md:223-228`). The environment
is the `𝒮ᵥ` list, so it sees the underlying set. The raw tuple
inhabits `InjCode (upγ Fg) a a` definitionally
(`Probe429.agda:98`, `runs/defeq-1.out`, exit 0, 1.64 s). Then
truncate.

## 5. The obligation, three forced rechecks

Three forced rechecks of the full file, exit 0 every time, each
printed `Checking`. Interface deleted before every kept run. Same
caliber, one process, no heap event.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.64 | 405700608 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.61 | 405684224 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.63 | 405733376 |

Median wall **1.63 s**. Median peak RSS **405700608 bytes**.

Against W3's median 1.61 s the packaging did not move the figure.

## 6. What the selection at this bound would then cost

A GO here is a truncated identity code at `γ`, not at `SiteBound.β`.

`Canonical` is still guarded by a nonempty hypothesis over
`Mem (Lset β)` (`src/L/Cardinal.lagda.md:192-193`).
`InternalLeastCard.Selected` is still guarded by a nonempty
hypothesis over `Mem (Lset β)` (`src/L/Cardinal.lagda.md:242-243`).
`grep` of `InternalLeastCard` in `src/` returns the definition only,
at `src/L/Cardinal.lagda.md:235`. This brief forbids widening that
module. This GO does not discharge either hypothesis as written.

What it does discharge is the same existence, restated at `γ`:

    ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a a ∥₁

Selection at `γ` would then be one `leastOf (orderAt γ oγ)` on a
four-conjunct `Good`, the shape `[LJ-1.424]` already typed at
`SiteBound.β` (`agents/tasks/LJ-1-424/Probe424.agda:83-86`, W3
median 1.54 s). A measured cure does not transfer by analogy.
Re-measure that `leastOf` at `γ`. The payload is a proposition, so
the index comes out as data
(`dev/literature/truncation-and-selection.md:146-148`). That is
Devlin's least-witness guard
(`dev/literature/devlin-II5.md:129`) in the form `IsLeast` already
has.

The next brief, if it wants the chapter's `Selected`, must name a
new file and a new statement: either a selector at `γ`, or a reason
the chapter's `β` may move. This probe does not move it.

## 7. C-42

This GO measures ONE site: the identity graph on a generic
L-element, placed in `Lset γ` with `γ` built from that graph's own
stage. It does not measure another graph. It does not measure
`Canonical.Good` at `β`. It does not measure
`InternalLeastCard.Good` at `β`. Those two sites remain the COUNT
`[LJ-1.425]` reported: **2**, both in `src/L/Cardinal.lagda.md`.

## 8. W4

No module was retired. Nothing moved to `archive/`.

## 9. What the shape resisted, and what closed

The bound was the risk. It closed in 1.61 s. The `IsOrd`
certificates that D-10 named were enough. The four conjuncts did
not resist. The packaging resisted only as a Sigma equality, which
the obligation does not need. Nothing was weakened. Nothing was
left a hole.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read. `:1` reads
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined: the
  retired dispatch table. This task's code is not a row I needed.
- `archive/dev/JOURNAL-archived.md`: read. `:1` reads
  `# Archived journal: the retired route`. Declined: a dated record
  of the retired route, not the two bounds.
- `archive/dev/JOURNAL.md`: read. `:1` reads
  `# ARCHIVED 2026-08-20`. Declined: per-episode journal, retired.
  The product of this task sits in `agents/tasks/LJ-1-429/`.
- `dev/ARCHIVE.md`: read. `:1` reads
  `# ARCHIVE.md: the archive registry`. Declined: no module was
  retired, so no row is written.
- `archive/dev/DD-archived.md`: read. `:1` reads
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined:
  archived DD series, not the bound built from the graph.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read and used.
  `:147` reads
  `delivers the least INDEX untruncated, and any payload it delivers with the`.
  `:148` reads
  `index is a proposition. **A data payload does not come out.**`.
  That is why selection at `γ` would return the member as data and
  keep any ambient arrow truncated.
- `dev/literature/devlin-II5.md`: read and used. `:129` reads
  `ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))`.
  That is the least-witness guard. `IsLeast` is that guard. The
  selection at `γ` would spend it, and this dispatch did not run
  that selection.
- `dev/literature/terms-2026-08.md`: read. `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined: a glossary dossier, not the bound.
- `dev/literature/digest.md`: read. `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined: the rud-route digest, not the identity graph.
- `dev/literature/geology.md`: read. `:1` reads
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined: geology sources, not this placement.
