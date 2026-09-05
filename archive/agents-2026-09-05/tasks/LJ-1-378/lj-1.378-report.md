# LJ-1.378 report: the composite's TERM, probed

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**MECHANICAL.**

`agents/tasks/LJ-1-378/ProbeLJ1378A.agda`, **exit 0**, assembles a term
of `Composite`'s type at one instance, at the ambient carrier, at
`φ₀`'s own frame, and feeds it to `[LJ-1.302]`'s `Fed`:
`amb-from-composite` is a term there. The assembly between the named
obligations is BUILT: the graph stem (`[LJ-1.52]`'s shape, re-landed on
`[LJ-1.304]`'s stems), the level stem, the `≐`-retarget, and the
packaging. `ProbeLJ1378B.agda`, **exit 0**, builds the frame
restriction from the delivered `⊨-rename`, with ONE syntactic
equation as a parameter whose only non-definitional content a failed
`refl` run localized to the opaque `DefAt` leaf.

**No mathematics hides in the assembly.** What hides elsewhere, named
at `file:line` below: the `φ₀` EXTRACTION is unwritten and unpriced;
the leaf bridge at the composite's frame carries `[LJ-1.338]`'s
residue, two of whose ties may be false as stated; and the trio owes
one renaming-naturality equation, measured here for the first time.

**The 470 is a floor and it grows by about 180 plus two unpriced
items**, section 5. The owner should hear that the composite itself is
now a writing job with a price, and that the price's open ends are the
extraction and the residue, not the assembly.

## 1. `Composite` AS A TYPE (re-derived, C-44)

`agents/tasks/LJ-1-302/ProbeLJ1302A.agda:78-82`, VERIFIED by reading:

```agda
Composite : Type (ℓ-suc ℓ)
Composite = (γ : Vec A.R.SC 2)
          → ⟨ A.ambient γ (embed P1241.φ₀) ⟩
          → ⟨ A.ambient γ (S.Graph* {2} zero (suc zero)) ⟩
```

`S.Graph*` is `Seq.LsetGraphAt` at the ambient class
(`agents/tasks/LJ-1-297/ProbeLJ1297D.agda:93-94`), `φ₀ = closeN 14
(pins ∧̇ renamed)` (`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:146`).
This is `AmbientStep`'s `q'` slot's type
(`agents/tasks/LJ-1-244/ProbeLJ1244A.agda:104-107`), and `Fed`
(`ProbeLJ1302A.agda:91-99`) turns a hypothetical term into `amb`.

## 2. THE FIVE FACTORS, EACH CHECKED (the premise the brief doubted)

The premise「the four parts are each at a BUILT site」: VERIFIED for
three parts, OVER-CLAIMED around the fourth. Each part is built IN A
PROBE OR IN `src/`; none was a composite-facing term, and the
graph-stem re-landing was built nowhere until this probe.

| factor | status before this probe | evidence |
|---|---|---|
| leaf-stem, class carrier | DELIVERED | `extAtB→extAt`/`extAt→extAtB` at `src/L/Condensation.lagda.md:2511-2529`, fed by `LeafAgree.out/back` at `:7231-7244` |
| leaf-stem, ambient | TERMS modulo residue | `[LJ-1.338]`, `LA` instantiated, `ProbeLeaf338.agda:353-356`, six residues parameters |
| step-stem, approx-stem | BUILT as terms | `[LJ-1.304]`, `StepAgree.step-agree`, `ApproxAgree.approx-agree`, exit 0, obligations parameters |
| graph-stem | ARCHIVED at class, NEVER at ambient | `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:71-87`, frozen; `[LJ-1.304]` section 10:「the last unpriced term」 |
| `φ₀`-extraction | UNWRITTEN | `[LJ-1.302]` section 1 priced it trivial by DESCRIPTION only |

The graph row inside `φ₀`: `LevelHood.levelHoodB`
(`src/L/BoundedSubset.lagda.md:109-112`) is `∃̇∈ (var K)
(G.graphBndAt ∧̇ (v ≐ w))` with `G = GraphB` on `DefBodyB` leaves
(`:81-107`), so `φ₀`'s matrix contains the SAME `GraphB` row the stems
consume. The two dialects agree by construction. MEASURED, by reading.

Delivered lemmas the assembly spends: `⊨-rename`
(`src/FOL/Manipulation/Renaming.lagda.md:127`), `Cnt.erase-inv`
(`src/FOL/Count.lagda.md:617`, spent at
`src/L/Condensation.lagda.md:296`), `⊨-map`
(`src/FOL/Manipulation/Relabelling.lagda.md:154`). MEASURED, by grep.

## 3. WHAT THE TERM CONSUMES AND WHAT IT PRODUCES

**Consumes, as terms or delivered machinery:** the Def-step trio
(a parameter, by design); the two stems (imported from
`[LJ-1.304]`); `LsetGraph-in` and the machine rows (`[LJ-1-238]`);
`absFull` and the ambient readings (`[LJ-1.297]`); `⊨-rename`
(DELIVERED, spent in `ProbeLJ1378B.agda`); `CompositeTy` and `Fed`
(imported from `[LJ-1.302]`).

**Consumes, as NAMED obligations, each priced elsewhere:** the leaf
bridge at the composite's own frame (`leafFwd4/leafBwd4`,
`leafFwd6/leafBwd6`, `[LJ-1.298]`'s port plus `[LJ-1.338]`'s ties plus
the wrapper); the in-K facts (`wK`, `dK`, `zK`, `domAgree`, `entryK`,
the 327-line tie family and `dK`); the extraction (unpriced, section
4); the trio's renaming-naturality (measured here, section 4).

**Produces, BUILT here:** the graph stem at ambient (`graphStem`,
`ProbeLJ1378A.agda`, `[LJ-1.52]`'s pattern with `Seq.LsetGraph-in`);
the level stem (`levelStem`, `levelHoodB`'s row to the machine graph
at the frame); the `≐`-retarget along `Σ≡Prop`; `comp : Composite`
itself; `amb-from-composite` through `Fed` fed MY `comp`. The
restriction from the seventeen-slot frame to the pair is BUILT in
`ProbeLJ1378B.agda` from `⊨-rename`.

## 4. THE MINIATURE, AND THE TWO WALLS IT FOUND

**`ProbeLJ1378A.agda`, exit 0** (nine failed runs first, all
scaffolding: an `∃̇` name, `ΣPathP` endpoint reduction, a `cong₂` on a
`Vec`, projection chains into the obligation bundle, the `≐` path's
direction, the carrier mismatch `P184.Full` against `P1297A.Full`
which `[LJ-1.297]` had already settled by `refl` at
`ProbeLJ1297A.agda:83`). The file holds 246 non-blank non-comment
lines; the assembly core (the two stem applications, the graph stem,
the level stem, `comp`) is about 100 of them, the rest is the
obligation bundle's statement and the scaffold. **The assembly's own
elaboration is free beside the scaffold**: 2.4 s user for the whole
file against a 2.3 s user floor (`Floor378.agda`, exit 0, same
imports, empty body). MEASURED.

**WALL ONE, small and named: the trio's renaming-naturality.**
`ProbeLJ1378B.agda` builds the restriction from the delivered
`⊨-rename`. The one syntactic equation it needs, `renameFo ρ₀
(LsetGraphAt {2} 0 1) ≡ LsetGraphAt {17} 0 3`, FAILED as `refl` at
exactly one subterm: renaming cannot push through the OPAQUE `DefAt`
leaf (`renameFo (liftρ⁷ ρ₀) (DefAt zero (suc zero))`, where the seven
lifts act as the identity on those slots). Everything else in the
equation was DEFINITIONAL, by the row builders' `sh2`-shifts.
MEASURED, by the failed run. The cure is a naturality hypothesis
`renameFo ρ (DefAt u w) ≡ DefAt (ρ u) (ρ w)` on the trio: a syntactic
condition the real coding satisfies, unpriced, likely small.

**WALL TWO, standing and unpriced: the extraction.** The named
hypothesis `Extraction` (`ProbeLJ1378A.agda`, Comp module) states the
`φ₀`-side obligation exactly: the fourteen witnesses, the level row,
and the carrier-level slot equations. Its legs: a fourteen-fold `∃̇`
unfold (mechanical), a conjunct projection (mechanical), the
rename-back along `ρ` (delivered `⊨-rename`, and it will need the SAME
leaf-naturality), the un-erase along `Cnt.erase-inv` (delivered), an
`embed`-`renameFo` commutation (an unwritten mechanical induction,
about 12 lines), and `[LJ-1.241]`'s slot-map towers (finite
arithmetic, tedious). **Nobody has priced this factor, and
`[LJ-1.302]`'s「trivial」was a description, not a measurement.** Its
obstruction class is bookkeeping, not mathematics: every leg is a
delivered lemma or a finite check. INFERRED, from the legs' inventory;
the factor itself is UNPRICED.

**THE NEGATIVE CONTROL.** `Control378.agda`, a ONE-line edit of the
green file (the two packaging arguments of `LsetGraph-in` swapped in
`graphStem`'s `go`), **exit 42**, refused at `Control378.agda:295`,
the swapped line, with the step's satisfaction refused where the
approximation's is expected. The assembly SPENDS the imported stems;
the packaging is not decoration. MEASURED.

## 5. WHAT THE 470 BECOMES

The abort criterion's first branch fires, with additions the record
owes:

| item | lines | basis |
|---|---:|---|
| the priced four parts | 470 | `[LJ-1.298]` 180, `[LJ-1.338]` 327, `[LJ-1.304]` 190, type free |
| the assembly itself | **about 140, MEASURED here** | `ProbeLJ1378A.agda`'s assembly core about 100 plus `ProbeLJ1378B.agda`'s restriction about 40; against `[LJ-1.304]` section 10's INFERRED 40 |
| `dK` and the leaf-frame wrapper | about 40 | `[LJ-1.304]` sections 3 and 10, INFERRED, unbuilt |
| the leaf-naturality equation | unpriced, likely under 20 | measured obstruction, section 4 |
| **the extraction** | **UNPRICED** | section 4; legs delivered or finite, factor unwritten |
| **the residue's proofs** | **UNPRICED, two ties may be false** | `[LJ-1.338]` section 4; D-10 |

**ONE number (DD8): the composite's term is a writing job at about
650 hand-written lines on top of the tree, PLUS the extraction and the
residue's proofs, which no figure covers yet.** Basis: the measured
miniature and the priced parts; the 650 is not a band, it is a floor
with two named open ends.

## 6. DOES THE COMPOSITE NEED `[LJ-1.338]`'s RESIDUE

**YES, BY THE TELESCOPE, and the miniature CONFIRMS it.** The
composite's leaf bridge is `LeafAgree`'s output, and `LeafAgree`'s
telescope carries `witK`, `graphWitK`, `envK`, `defPairK` and the two
code-arity conjuncts (`ProbeLeaf338.agda:315-352`, types verbatim from
the chapter at `src/L/Condensation.lagda.md:7116-7189`). My `comp`
consumes that bridge as `leafFwd4/leafBwd4/leafFwd6/leafBwd6`, so the
51 residue lines are ON the composite's route, not beside it.
MEASURED, by the miniature's own obligation bundle. **`envK` and
`defPairK` may be false as stated at the composite's frame exactly as
at `[LJ-1.338]`'s frame, INFERRED from the same unbounded `z`; D-10
says a brief that funds the leaf at the composite's frame prices their
TRUTH first.**

## 7. PREMISES CHECK

| premise | status |
|---|---|
| the composite's term never written, `dev/PLAN.md:104` | **VERIFIED**, `dev/PLAN.md:104-106`; this probe assembles one for the first time, modulo named obligations |
| `[LJ-1.302]` proved FEEDS not EXISTS | **VERIFIED**, `ProbeLJ1302A.agda:93`, `module Fed (comp : Composite)`, hypothetical |
| the four parts each at a BUILT site, `dev/PLAN.md:57-63` | **VERIFIED for three parts; OVER-CLAIMED around the fourth**: the stems and the leaf are probe-built, not landed; the graph-stem re-landing was built nowhere;「the composite's type, writable」was never a term |
| 51 of 327 state a residue nothing proves, `dev/PLAN.md:63` | **VERIFIED**, `[LJ-1.338]` section 4 |

**The premise the brief doubted was the one at risk, and it broke in
the smallest way: nothing in section 0.0's table was FALSE, but「each
at a BUILT site」hid that the assembly between the sites was unbuilt
and that the extraction row of the decomposition was never a
measurement.**

## 8. ARCHIVE USED (DD18)

The four corpora, one line each.

- **`archive/src/2026-08-09-rud-route/`**: grepped `Agree|composite`
  over its `L/Condensation.lagda.md` (885 lines) and its tree:
  **zero hits**. The retired route never built a composite of this
  shape. MEASURED. **Line read:** its `README.md:1`,「The rud route's
  `src/`, archived 2026-08-09」.
- **`archive/dev/TASKS-archived.md`**: grepped `assembl|composite`.
  **Line read:** `:230`,「L3.32-T226 | C4: one story assembly, before
  the general STEP is written | KEPT: +72 naive」. TOOK SHAPE only: the
  retired route's assemblies were story/switch assemblies, priced as
  deltas against delivered reductions; no figure transfers to a
  two-coding agreement bridge.
- **`archive/dev/JOURNAL-archived.md`**: **Line read:** `:293`,「WAVE
  3: `[R3c]` the switch theorem assembled (realization instantiated at
  F0..F15 + descriptions + the defSet bridge)」. WHY the retired
  assembly was shaped differently: it assembled ONE coding's
  realization, not two codings' agreement. TOOK the lesson that an
  assembly is priced as a delta, which section 5 follows.
- **`archive/dev/DECISIONS-archived.md`**: grepped
  `composite|assembl`, zero hits in 61 lines. **WHY NOT: no ruling on
  composite structure exists; the composite is an artefact of the
  current route's two-coding architecture, and no archived decision
  bears on it.**

Also read, beside the four corpora as the brief's SCOPE ordered:
`agents/tasks/LJ-1-302/` whole (report and both probes),
`LJ-1-304/lj-1.304-report.md` and `ProbeLJ1304A.agda` whole,
`LJ-1-338/lj-1.338-report.md` and `ProbeLeaf338.agda`,
`LJ-1-297/ProbeLJ1297A.agda` and `ProbeLJ1297D.agda`,
`LJ-1-244/ProbeLJ1244A.agda`, `LJ-1-241/ProbeLJ1241A.agda:60-160`,
`LJ-1-238/GenSequence.agda`, `archive/LJ-1-52/ProbeLJ152B.agda` whole.

## 9. LITERATURE USED (DD18)

**The one line the brief asks for: the orthodox development assembles
NOTHING of this shape, so the literature cannot help the composite,
and the composite is an artefact of this formalization.**

- `dev/literature/devlin-II5.md`, read `:93-97`. **Line read:** the
  2.7 quote,「By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that
  (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]」. Devlin writes ONE coding of
  level-hood and moves its satisfaction between carriers; no second
  coding exists to agree with, so no composite, no extraction, no
  residue. WHY NOT the rest of the digest: `[LJ-1.302]` and
  `[LJ-1.304]` already priced the obligations the port INTRODUCED;
  this probe adds nothing that changes those rows.
- `dev/literature/j-hierarchy.md`, read its head. **WHY NOT: it is the
  rud route's fine-structure notes (S vs J stratification,
  condensation informally); it stratifies one coding and never bridges
  two, so nothing there prices an agreement assembly.**

## 10. DD4, WITH THE AXIS NAMED (C-46)

**My axis is the L-against-ambient axis; DD4's own axis is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.**

**On DD4's own axis this probe is NEUTRAL BY STRUCTURE.** `L.Condensation`
is in neither trophy's closure (`[LJ-1.336]`'s measurement, which
`[LJ-1.338]` re-ran and I take unchanged); nothing here moves either
closure. INHERITED measurement, not re-run.

**On the L-against-ambient axis, the miniature MAXIMIZES the share.**
The graph stem, the level stem and the restriction are written GENERIC
in the class, the leaf content and the Def-step trio: they serve the L
tower's proof and the ambient proof from the same lines, exactly the
generic form DD4 demands. The only carrier-committed lines are the
scaffold's, cribbed from `[LJ-1.304]`. MEASURED, by the module
telescopes: the class enters nowhere but the scaffold's eight
parameters.

**The `[LJ-1.113]` per-tower split, about 28 lines, about 7 percent:
this probe neither honours nor breaks it, because it touches no
per-tower content.** The assembly sits below the towers' divergence.
MEASURED, by what the file names.

## 11. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap
NEVER raised. No heap exhaustion. No invocation near 30 minutes; the
longest wall time was 7 s. Slot count
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` read before
every invocation: 0 except once (1, a sibling live; I ran anyway, one
slot free under the cap of two). Load between 2.5 and 5.8, 3 users,
throughout. All dependencies' interfaces were cached after the first
run, so the seconds price my files' own elaboration.

| file | exit | user s | note |
|---|---:|---:|---|
| `ProbeLJ1378A.agda` | 42, 7 runs | 2 to 4 | scaffolding: names, `ΣPathP` endpoints, `cong₂`, projections, `≐` direction, carrier display |
| `ProbeLJ1378A.agda` | **0** | 2.4 | the assembly, green; 3.5 s, 2.6 s, 2.6 s wall over three runs |
| `Floor378.agda` | **0** | 2.3 | **the empty-file floor (C-53)**, same imports |
| `Control378.agda` | **42** | 2 | **EXPECTED RED**, at the swapped packaging line `:295` |
| `ProbeLJ1378B.agda` | 42, 3 runs | 2 to 3 | module arity (four args for a three-arg telescope), the `refl` wall, a `subst` direction |
| `ProbeLJ1378B.agda` | **0** | 3.8 | the restriction, green |

## 12. WHAT I DID NOT SETTLE

- **The extraction's price.** Its type is named and its legs are
  inventoried; the factor is unwritten and unpriced. That is the next
  brief's first item.
- **The leaf-naturality equation's proof.** Its obstruction is
  measured; the hypothesis's discharge at the real coding is unpriced.
- **The residue's truth at the composite's frame.** `envK` and
  `defPairK` may be false as stated; D-10 prices truth before proof.
- **Whether `q'` is TRUE.** This probe prices the assembly, not the
  crossing. The named obligations include everything unresolved.
- **The landing.** Nothing landed; `src/` untouched.

## 13. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-378/`: this report,
`ProbeLJ1378A.agda`, `ProbeLJ1378B.agda`, `Floor378.agda`,
`Control378.agda`. `src/` holds no probe of mine; the chapters and the
sibling task directories were read and imported, never edited.
`src/Everything.lagda.md`, `dev/ledger.toml`, `dev/PLAN.md` were not
touched. No commit, no push, no `git checkout`, `stash`, `reset` or
`clean`. No `make check`. `_build/` holds only Agda's own interface
files for my four modules. `.venv/bin/python scripts/gate/lint-prose.py`
and `scripts/gate/lint-agda.py` were run on my files before this
report closed; both pass. No em dash in any language.
