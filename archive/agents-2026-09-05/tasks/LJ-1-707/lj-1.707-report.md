# LJ-1.707 report: ThroughDoor, from its two named misses as hypotheses

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.707
obligation: agents/tasks/LJ-1-707/Probe707.agda::through-door-closed
verdict: **GO AS AN ASSEMBLY. `through-door-closed` is inhabited, and
the two misses `[LJ-1.698]` named are the whole distance it costs.**
The meter resolves the obligation (`runs/meter-obligation.out`: `pass
exit=0`, 0 UNRESOLVED of 1, `probe_red=False`). The delivered probe
typechecks at 6.29 s and 773,701,632 bytes under the wide caliber
(`runs/p-3.out`). `[LJ-1.704]`'s identification and `[LJ-1.705]`'s
bound are now the only remaining bills on this route; nothing else
stands between them and `HierInK`.

This skeleton was written before any Agda ran and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-707/`. Agda ran ONE process at a time under the
caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"`,
the WIDE tier. I did not set `GHCRTS` and never re-ran a failing run
unchanged: each failing scope produced one new shape that was then
tested (`floor-1` to `floor-2`). Nothing is postulated, the probe
carries `--safe` and no hole, nothing lands in `src/`
(`git status`: the task directory is the only untracked path). The
probe is a raw `.agda` file, so it counts 0 in-fence lines and the
ratio bar cannot fire on it.

**NO HEAP WALL WAS MET.** The highest peak of any run is 798,621,696
bytes against the 2,147,483,648-byte wide cap (`runs/floor-1.out`),
which is 37 percent of it. The longest Agda run is 28.92 s
(`runs/floor-1.out`) against the 600 s cap.

## 0. THE PREDECESSOR QUESTION

The standing clause binds module hypotheses to the type the
predecessor DELIVERED, taken from its typechecking probe and its
report verdict. Both consumed probes answer:

| piece | taken from | verdict there | use here |
|---|---|---|---|
| `ThroughDoor`, `Door`, `IsLimit`, `HierInK` | Probe693.agda:135-139, :72-75, :77-80 | TYPE green; NOT inhabited. Its NO-GO is at `hier-in-K-placement`, a different name. | obligation type + consumer, verbatim |
| `from-door` | Probe693.agda:141-150 | GO as composition | reused, not rebuilt |
| `module Carved` | Probe698.agda:96-129 | door GREEN on the carved set (report :36) | source of `At.carved`, `At.σ`, `carved-door` |
| `through-door` | Probe698.agda (absent by design) | NO-GO, stated in review-of-through-door.md | **not inhabited here.** A different name carries hypotheses |

Neither report was NO-GO AT A TYPE I HABIT. `[LJ-1.704]` and
`[LJ-1.705]` have no predecessor dispatch yet, so their hypothesis
types come from the brief's own premises and from `[LJ-1.698]`'s
corrected target rows (`agents/tasks/LJ-1-698/lj-1.698-report.md:117-119`),
NOT from an invented specification:
identification = `Carved.carved ≡ fst (hierL γ hγ oγ)`;
bound = `⟨ fst (bound-of γ oγ hγ) ∈ α ⟩` for `γ ∈ α`.
No other input is taken. The forbidden list stands obeyed:
`adequacy-bnd` not rebuilt, DOWN not funded, `ApproxInK` not
inhabited (`agents/tasks/LJ-1-698/lj-1.698-report.md:41-45`).

## 1. THE TWO HYPOTHESES, WRITTEN AND TYPECHECKED

File `agents/tasks/LJ-1-707/Probe707.agda`.

```agda
identification : Type (ℓ-suc ℓ)
identification =
    (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
  → At.carved γ oγ hγ ≡ fst (hierL γ hγ oγ)

the-bound : Type (ℓ-suc ℓ)
the-bound =
    (α : V ℓ) → IsLimit α
  → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → ⟨ γ ∈ α ⟩
  → ⟨ At.σ γ oγ hγ ∈ α ⟩
```

Field access goes through
one module alias, `module At (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
= Carved γ oγ hγ` (Probe707.agda:53), because Carved's fields carry
its three parameters. Each hypothesis may be WEAKER than what its
keystone finally delivers; weaker still feeds the assembly, since a
weakened premise keeps the term total. Neither may need MORE than the
telescopes shown.

P-l holds: every type names `Lset δ`, `V ℓ`, `𝒟ₒ`-free stage values
and opaque constructions, never a transparent presentation. D-26
passes unused: no well-founded key on a stage is attempted here.
D-10 was already paid by `[LJ-1.698]` at this residue, target truth
included (`agents/tasks/LJ-1-698/lj-1.698-report.md:98-120`); both
keystones sit inside that
paid residue, so this dispatch re-checks nothing and asserts nothing
new about Devlin's sequence beyond its own terms.

## 2. THE FLOOR, MEASURED BEFORE ANY PROOF

Floor first (coder clause, owner 2026-08-23). Hole unavailable under
`--safe`, so the floor is the obligation TYPE formed and nothing
behind it: imports, both hypothesis types, NO definition body. First
scope failed on scope hygiene, which is itself part of the floor
measurement; then it landed warm.

| run | content | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `floor-1` | cold dependency cone PLUS first floor scope, `⟨ γ ∈ α ⟩` unparseable (`_∈_` not imported) | 42 | 28.92 | 798,621,696 |
| `floor-2` | floor, `_∈_` added, warm cone | 0 | 2.70 | 647,741,440 |
| `p-3` | full assembly + route | 0 | 6.29 | 773,701,632 |

Every number after `floor-1` is WARM (probe interfaces cached by the
failed run). This report does not bound a second cold run. The frame
costs less than 3 s warm; the assembly adds 3.59 s and 126 MB over
that floor. No import trim below the current set was attempted: the
frame was never the problem at this size.

## 3. THE ASSEMBLY, AND WHY NOTHING RESISTED

`through-door-closed` (Probe707.agda:80-90):

```agda
through-door-closed ident bnd α lim β hβ oβ β∈α =
  ∣ At.σ β oβ hβ ,
    ( bnd α lim β oβ hβ β∈α
    , subst (λ x → Door (Lset (At.σ β oβ hβ)) x)
        (ident β oβ hβ)
        (At.carved-door β oβ hβ) ) ∣₁
```

δ IS σ, `[LJ-1.705]`'s own stage. δ ∈ α is exactly `bnd`. The Door
row is `[LJ-1.698]`'s own `carved-door`
(`agents/tasks/LJ-1-698/Probe698.agda:128-129`) transported along
`[LJ-1.704]`'s equation by `subst`. The witness reuses predecessor
work in place instead of proving anything new about satisfaction,
bounds or carving: the entire term after hypothesis intake is one
pair plus one transport.

**THE ZERO CASE NEEDS NO BRANCH HERE.** At β = ∅ both hypotheses
instance like anywhere else. `[LJ-1.698]` already learned the zero
case was not the miss: `empty-door` is paid whole and generic
(`agents/tasks/LJ-1-698/Probe698.agda:173-177`), with
`empty-in-limit` giving ∅ ∈ α (`:184-185`). A separate zero case in
this file would have been dead code next to those rows.

Composed with `[LJ-1.693]`'s consumer, `the-route ident bnd :
identification → the-bound → HierInK` (Probe707.agda:100-101) closes
`HierInK` end to end from the two keystones alone. That row prices
what remains AFTER `[LJ-1.704]` and `[LJ-1.705]` land on this route:
nothing but the composition already shown.

## 4. W3, THE WIDEST UNMEASURED TERM, ANSWERED

The brief names W3 as whether `ThroughDoor` needs a third input
beyond the two misses. **IT DOES NOT.** The meter resolves the
obligation on exactly two inputs (`runs/meter-obligation.out`).
Brief estimate 40 to 120 lines; delivered file is 101 lines total,
86 non-blank, so the estimate held. The GO branch earns what the
brief promised: the two misses are the whole distance, priced at
6.29 s warm end to end.

What the GO does NOT measure: neither keystone's own proof cost. If
`[LJ-1.704]` or `[LJ-1.705]` lands needing extra premises, this GO
survives only if those premises discharge INSIDE one keystone; if a
keystone must reach across BOTH misses at once, the critic should
re-read `review-of-through-door-closed.md`, whose contract section
names that falsification condition in writing.

## 5. W2 ANSWER

W2: mathematics written once at a generic carrier, instantiated at
consumers. Observed. `through-door-closed` quantifies over `(α, β)`
with NO fixed presentation, consumes the generic `Carved` machinery
at whatever `(γ, oγ, hγ)` arrives, and instantiates nowhere. There is
no `n = 0` copy, no second Δ₀ ascription, no rebuilt adequacy. No
deadline conflicts with any fixed form, so no stop for price arises.

## 6. WHAT THE NEXT BRIEF NEEDS

- For `[LJ-1.704]` (identification): deliver at `identification`'s
  exact telescope or weaker (a pointwise-in-δ variant with the
  identification restricted to stages relevant per-consumer would
  also feed `subst` here, but state the weakening explicitly). Do
  not add parameters the assembly does not read. Basis for the
  shape: the field it delivers is
  `Carved.carved` (`agents/tasks/LJ-1-698/Probe698.agda:123`).
- For `[LJ-1.705]` (bound): deliver at `the-bound`'s exact telescope
  or weaker. The plausible false target to guard against is a bound
  proven only for SOME limits (say, only where LsetS's constants
  stay low); if success is conditional, say so in the report rather
  than land the unconstrained-looking type.
- After both land: a one-line consumer on this probe composes them
  into `HierInK` via `the-route`; nobody needs to re-run this
  measurement to do that.
- Keep `[LJ-1.684]`'s recipe line untouched: this file still does
  not pay `adequacy-bnd`'s membership debt
  (`lj-1.698-report.md:41-45`).

## 7. PRICE

| item | measured |
|---|---|
| floor (cold cone + bad first scope) | 28.92 s, 798,621,696 bytes, EXIT=42 (`runs/floor-1.out`) |
| floor (warm, `_∈_` fixed) | 2.70 s, 647,741,440 bytes, EXIT=0 (`runs/floor-2.out`) |
| delivered probe | 6.29 s, 773,701,632 bytes, EXIT=0 (`runs/p-3.out`) |
| witness meter | pass exit=0, 2.65 s, 0 UNRESOLVED of 1, `probe_red=False` (`runs/meter-obligation.out`) |
| file lines / non-blank / in-fence | 101 / 86 / 0 (raw `.agda`) |
| brief estimate | 40 to 120 lines |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none; peak 37 percent of cap |
| `src/` edits | none |

The brief promised that "if two hypotheses are the whole distance,
this closes in an hour". Measured wall time of the task's Agda runs
sums to well under 60 s including the cold cone; the campaign learns
exactly that no third input hides on this route.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch measures a live assembly between two live probes; no archived operating rule bears on it.
- `archive/dev/DD-archived.md:1` `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live home of the hypothesis clause and W2 is the coder slot file, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the \`L3.32-T\` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` `| 2 | Devlin 2.6 | \`G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]\`; \`G\` says \`f = (L_γ ∣ γ ≤ α)\` | 2 | \`w\`, ONE bound, determined | \`f\`, \`α\` | SEQUENCE, ORDINAL | \`_build/literature/dev2.txt:655-659\` |`. Read. `ThroughDoor` asks the table at β to be definable at some earlier stage of the SAME limit α that β sits in; slot roles fixes which slots the door's formula may bind, and both hypotheses respect that reading.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles already cites the primary page range this task could need.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used. No translation surface exists in a raw `.agda` probe.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Surveyed and declined: its recorded classes (junk sequences at :86, finite-sequence typing at :100-105, Σ1-at-limits at :140-141) touch none of the two hypothesis rows assembled here.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used. The rud route is not this door.
