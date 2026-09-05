# LJ-1.741 report: `defSet-in-carrier-lim`, the definable subset under the carrier's closure

(This report was written after the probe landed; the probe itself was
built and saved incrementally across the run log in `runs/`, see C-22,
`dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.741
obligation: agents/tasks/LJ-1-741/Probe741.agda::defSet-in-carrier-lim
verdict: **GO.** The obligation is INHABITED:
`defSet-in-carrier-lim` (agents/tasks/LJ-1-741/Probe741.agda:371,
term body at :376-379) typechecks at EXIT=0
(`runs/p-35.out` first green, `runs/p-36.out` confirm; instrumented
confirm `runs/p-36.err`: 0.95 s wall, 234,799,872 B peak), under
`--cubical --safe --guardedness`, no postulate and no hole. The brief's
type is inhabited at exactly the offered hypotheses: `IsOrd γ`,
`closedω γ`, `fst A ∈ Lset γ`, `ψ : Formula ⟪ fst A ⟫ 1` -- no `ω ∈ γ`,
no bounded-constant side condition, no Sat bound. Nothing lands in
`src/`. `Sat-in-carrier-lim` is not inhabited (it is priced FALSE by
its own predecessor, agents/tasks/LJ-1-736/lj-1.736-report.md:13); the
landed unbounded `fill`, `stage-read`, and `envSet-in-carrier-stage`
appear nowhere in the file.

## 0. THE PREDECESSOR QUESTION

| piece | taken from | verdict there | use here |
|---|---|---|---|
| the unbounded `fill` | the brief's premise 1, src/L/Coding/Powerset.lagda.md:500 (`fill` pins `z` to `DA.defSet ψ`, conclusion at :502) | landed, green | this obligation is the bound that reading still needs; the term is delivered, not the `fill` |
| the operator's membership | the brief's premise 2, src/L/Definability.lagda.md:137 (`Def A = sett (Formula ⟪ A ⟫ 1) defSet`) with `defSet-mem` (:150) and `𝒟ₒ-intro` (src/L/Constructible.lagda.md:301) | landed, green | one line puts `defSet (fst A) ψ` in `𝒟ₒ (fst A)`; the hard half is placing that set in the tower |
| the successor identity | the brief's premise 3, src/L/Axioms/Basic.lagda.md:196 (`Lset-suc`) | landed, green | `𝒟ₒ (Lset σ) = Lset (sucV σ)` is the landing stage |
| the closure | the brief's premise 4, src/L/Ordinal/StageArith.lagda.md:81 (`closedω`) with `+ω-iter` and `Lset-mono` | landed, green | absorbs `sucIter 2 δ` into `γ` |
| D-10 | the brief's premise 5, agents/tasks/LJ-1-730/lj-1.730-report.md:13 | 730 NO-GO on `ω ∈ˢ γ` alone | truth priced before proof (section 1, step 0); the delivered GO lives strictly above 730's refutation site |

No predecessor NO-GO is contradicted. 736 priced `Sat A φ` FALSE for
`φ : Formula S n` -- the WIDE alphabet, whose constants can name any
`L`-set (agents/tasks/LJ-1-736/review-of-Sat-in-carrier-lim.md, section
"Why the sibling scope works"). This obligation's `ψ` is over
`⟪ fst A ⟫`, the carrier-bounded sibling scope, and the probe never
enters `Sat` at all.

## 1. WHAT WAS BUILT

`agents/tasks/LJ-1-741/Probe741.agda` (379 lines, 347 non-blank; raw
`.agda`, in-fence count 0, so the ratio bar cannot fire). One new
mathematical asset, everything else bookkeeping:

1. **Step 0, D-10 truth check (no code).** Before any proof: the
   members of `defSet (fst A) ψ` sit in `fst A` (`defSet⊆A`), so from
   `Lset-out γ (fst A) hA` the carrier sits in `𝒟ₒ (Lset δ)` with
   `δ ∈ γ`; the subset belongs to the NEXT definable power
   `𝒟ₒ (Lset (sucV δ)) = Lset (sucIter 2 δ)` (premise 3), and
   `closedω γ` absorbs the iterate (`+ω-iter 2 δ`, then
   `clγ δ δ∈γ`). TRUE at the offered scope; no `ω` needed anywhere.
2. **The transfer module** (`Carrier`, Probe741.agda:92-346), generic
   in one carrier `a` and one transitive stage `σ` holding it (W2):
   the fibers `κ`/`κEq` (:103-108) and `mA`/`mAEq` (:109-113); the
   entry repack `repack`/`repV` (:117-123); the two term lemmas
   `tm-fst`/`tm-fst1` (:132-149); the relativized image `cnd`
   (:153-164) -- atoms pass through `mapFo κ`, unbounded quantifiers
   are bounded by `con mA`, BOUNDED quantifiers keep their bound AND
   gain the carrier guard `var zero ∈̇ tmSuc t`, the double guard the
   inner semantics reads (src/L/Coding/Bridge.lagda.md:14-22, the
   clause on what the bridge does not say); its Δ₀ witness (:167-179);
   the top-level guard `bnd`/`Δ₀-bnd` (:181-185).
3. **The transfer induction** (`sat≈`, Probe741.agda:193-273): one
   induction on ψ, twelve clauses, carrier-inner satisfaction iff
   stage-inner satisfaction of the image, at environments that agree
   on raw sets. Stated as a PAIR OF FUNCTIONS, not as a path of truth
   values -- the path form made the elaborator unify the two reduced
   Ω-terms whole and that is the heap wall this shape routes around
   (section 2). Quantifier glue rides the presentation equivalence
   (`Σ≡Prop` on the entry proofs); the ∃̇∈/∀̇∈ clauses carry the double
   guard via `tm-fst1`.
4. **One extensional equation** (`bnd≡`, Probe741.agda:279-346):
   `DS.defSet (bnd ψ) ≡ DA.defSet ψ` by `extensionality`, both
   directions through `defSet-mem`, the induction, and one entry
   naming `repκ` (:275-277).
5. **The landing** (`landing` + `defSet-in-carrier-lim`,
   Probe741.agda:349-379): `𝒟ₒ-intro (Lset σ) d ∣ bnd ψ , bnd≡ ψ ∣₁`,
   `Lset-suc σ` renames it to `Lset (sucV σ)`, `Lset-mono` twice
   through `+ω-iter 2 δ` and `clγ` closes at `Lset γ`.

**Why this is the GO shape and not 736's NO-GO shape:** 736's defect
was the alphabet (`Formula S n` admits constants of any rank). Here
every constant of the stage-side formula is a fiber of `fst A` or of
its members -- all inside `Lset σ` with `σ = sucV δ ∈ˢ +ω δ ⊆ γ` --
so `closedω` absorbs exactly what appears, and nothing wider is
quantified.

## 2. THE FLOOR, THE WALL, AND THE RUNS

Per the heavy-object rule the floor was priced first: a throwaway
harness with the delivered file's import block and one trivial
definition (recipe in `runs/p-1-floor.*`; the harness itself lives in
`/tmp` and is not kept). Floor: EXIT=0, 0.99 s, 230,621,952 B peak.
The frame IS the whole cost: the delivered file's confirm run is
0.95 s / 234,799,872 B -- the file's own rows add nothing measurable,
so there was nothing to trim.

**One environment wall was met and routed, and it was not the term's.**
The first completion attempt of the path-form induction was SIGKILLed
(`runs/p-11b.*`, 11.4 s). The cause is machine-level, measured:
`scripts/ops/agda-watchdog.sh` kills the largest agda process whenever
system swap is at or above 8 GB, and this box sits at 8758 MB swapped
from other applications (watchdog log: six KILLED entries 05:01-06:12,
all "swap 8758MB >= 8192MB"). Peak RSS of my runs never exceeded 416
MB -- 19.4 percent of the wide cap -- so this was never a price of the
term. Two cures, both applied. First, restructure: the transfer was
restated from an Ω-path to a pair of functions (section 1 item 3),
which removed the whole-term unification that made elaboration slow
enough to be a repeated watchdog victim. Second, protocol: killed runs
were retried; identical bytes were never re-run after an Agda verdict
(only after SIGKILLs, which are not verdicts). After the restructure
the file checks in about 1-2 s per run.

| run | wall | peak RSS (B) | note |
|---|---|---|---|
| p-1-floor | 0.99 s | 230,621,952 | floor harness EXIT=0 (first attempt hit the `/usr/bin/time` "signal: Invalid argument" artifact, the 729 protocol: direct re-run of same bytes passed) |
| p-2 .. p-10, p-13..p-15, p-17..p-28 | 0.9-2.1 s each | <= 242,107,136 | iteration: scope, arity, and transport-direction fixes, one error per run, all logged |
| p-11b, p-12, p-16, p-29(first) | 0.4-11.4 s | <= 416,080 (sampled) | SIGKILLed by the watchdog (swap spiral); environment kills, not Agda verdicts |
| p-35 (first green) | 2.11 s | not instrumented | EXIT=0, delivered bytes |
| p-36 (confirm) | 0.95 s | **234,799,872** | EXIT=0, same bytes, instrumented |

ONE Agda process per run; GHCRTS `-A64m -I0 -M2g` was set on the pane
by the program and never touched here.

## 3. WHAT THE NEXT BRIEF NEEDS

1. **The `z` bound exists.** `fill`'s pinned set (`fill` at
   src/L/Coding/Powerset.lagda.md:500 pins `z` to `DA.defSet ψ`) can
   now be taken with `z := defSet (fst A) ψ` and landed by this term
   at `Lset γ`. The bounded-fill assembly (738's blocked obligation)
   still waits on the Sat scope ruling -- correction 2 of 736's review
   (bounded constants) is now PARTIALLY measured: this probe transfers
   carrier-bounded satisfaction to stages WITHOUT Sat, which is
   evidence that the asConst-Sat bound may be dispensable at sites
   that only need the definable subset, not the satisfaction table.
2. **Reusable asset.** `Carrier.sat≈` is general in the formula arity
   and stated tower-neutrally inside `Carrier (a) (σ) (oσ) (a∈σ)`. Any
   task needing "a definable subset of a carrier in `Lset γ` sits in
   `Lset γ` under `closedω`" can consume `bnd≡` + the landing pattern
   verbatim. Do not re-fund: the transfer induction, `cnd`/`Δ₀-cnd`,
   `repκ`, and the two-carve equation.
3. **Do not re-fund, predecessors:** the 736 kernel and its review's
   wide-alphabet verdict (still TRUE, still not compensable by
   closure), the 729 climb, the 735 close pattern (this probe's
   landing is a strictly simpler two-mono close -- no `ord-tri`, no
   `ω`), the landed `fill`.
4. **W2 answer.** The transfer is written ONCE at the generic module
   `Carrier (a) (σ) (oσ) (a∈σ)` -- generic carrier, generic
   transitive stage -- and instantiated once (landing,
   Probe741.agda:368). Nothing is duplicated with a sibling; the
   predecessor probes' restated hypothesis types are not repeated
   here because the brief's type is self-contained. No deadline
   conflict arose.
5. **C-42 note.** This GO measures ONE site: `DefOf.defSet (fst A) ψ`
   at `closedω γ`, carrier-bounded alphabet. It says nothing about
   `Sat A (mapFo asConst ψ)` (the unruled neighbour), about the wide
   alphabet (736's FALSE verdict stands), or about any other carrier
   coding. The sweep this verdict owes: none -- a GO is not a
   refutation.
6. **Watchdog note for any heavy follow-up.** While system swap sits
   at or above 8 GB the watchdog kills the largest agda every cycle;
   keep per-run checks short during iteration and prefer the
   function-form of transfer lemmas over Ω-path form (the path form's
   whole-term unification is what made this file slow enough to be a
   repeated victim).

## 4. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 0.95 s (`runs/p-36.err`) |
| peak, verdict run | 234,799,872 B, 10.9 percent of the 2,147,483,648-byte wide cap |
| first green | 2.11 s wall (`runs/p-35`), uninstrumented |
| floor | 0.99 s / 230,621,952 B (`runs/p-1-floor.err`); the frame IS the whole cost |
| runs this dispatch | floor + 30 logged runs; 6 watchdog SIGKILLs retried; no Agda-verdict failure re-run unchanged |
| heap wall | none (peak 10.9 percent of cap); one environment watchdog wall, routed (section 2) |
| in-file / in-fence lines | 379 total, 347 non-blank / 0 (raw `.agda`) |
| brief estimate (W3) | 20 to 80 lines |
| actual vs estimate | EXCEEDED: 347 non-blank. The estimate prices the assembly the premises sketch (premises 2-4 are indeed one line each); what it does not price is the definability transfer (section 1 items 2-3), which no landed chapter carries and which is the mathematical content this obligation exists to measure |
| caliber | `-A64m -I0 -M2g`, never set here |

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used. The GO
rests on landed masters and predecessor probes, cited at `file:line`
in sections 0 to 1.

- archive/dev/DD-archived.md: declined, not read; the clauses this
  dispatch answers to live in the live slot file and the brief.
- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  history does not touch a definability-transfer probe.
- archive/dev/PLAN-archived.md: declined, not read; retired plans name
  no bounded-fill obligation.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  lives in `dev/pod/screen.toml`, and this task's record is its own
  runs directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  files this task needed (LJ-1.729, LJ-1.730, LJ-1.735, LJ-1.736,
  LJ-1.738) are live files named by the brief and cited at `file:line`
  in section 0.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
verdict quotes no book: every step is an in-tree fact cited at
`file:line` in sections 0 to 1, and the D-10 truth check is a
three-line stage-arithmetic argument from landed lemmas
(`Lset-suc`, `+ω-iter`, `closedω`, `Lset-mono`).

- dev/literature/glossary-review-2026-08.md: declined, not read; a
  term-provenance review cannot change a machine-checked GO.
- dev/literature/devlin-errata.md: declined, not read after header
  check; documented error classes of Devlin's book, scoped to the
  rud-route formalization -- this probe cites no external source.
- dev/literature/level-formula-slot-roles.md: declined, not read past
  the header; it digests how outside authors number level-hood
  formula slots -- this probe numbers no new slots, it reuses the
  landed `Formula ⟪ A ⟫ n` syntax and its landed semantics.
- dev/literature/primary-sources.md: declined, not read; a source
  index names no in-tree obligation.
- dev/literature/BIBLIOGRAPHY.md: declined, not read; cite-only
  bibliography entries feed prose, which is frozen until both
  trophies land.
