# LJ-1.250 report: price `StepAgree` and `ApproxAgree`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot
held. No master edited. No commit, no push. Written incrementally (C-22).
Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**NEITHER BUILDS, and the reason is D-10, not a wall.** `StepAgree` and
`ApproxAgree` as stated in the port are **UNCONSTRAINED interfaces**, not
theorems. `ψs`/`ψa` (the BS leaf) and `DefAt` (the At leaf) are unrelated
parameters; the implication `stepBndAt ⊨ → StepAt ⊨` is refutable at that
generality. Written proof lines: **0**. The concrete per-tower proof is a
composition of a delivered generic lifting and a leaf adequacy that exists
in `src/` only as an **open module**, so the residue is NOT "one named
term": it is the leaf-adequacy supply plus one placement.

**`amb` is NOT supplied outright.** It stays conditional on the leaf chain.

**The delivered leaf adequacy did NOT transfer into a proof.** It is placed
(`LeafAgree`, `src/L/Condensation.lagda.md:7065`) but its telescope is
never discharged: nothing in `src/` instantiates `LeafAgree`, and the
supplier of its `twelve-out`/`twelve-back` is itself unbuilt
(`src/L/Condensation/TwelveAgree.lagda.md:519-522`).

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run near
20 minutes. No heap exhaustion. Load average 4.39 / 5.04 / 4.93 on 16
cores, so every absolute second carries the load caveat; the verdicts rest
on exit codes and readings, not on these seconds.

| run | file | exit | user s | real s |
|---|---|---:|---:|---:|
| control, the port | `ProbeLJ1249.agda` | 0 | 0.78 | 1.10 |
| control, the twelve-row master | `L/Condensation/TwelveAgree.lagda.md` | 0 | 1.57 | 1.74 |
| control, the leaf-adequacy master | `L/Condensation.lagda.md` | 0 | 1.96 | 2.10 |
| this probe | `ProbeLJ1250.agda` | 0 | 0.03 | 0.07 |

The two masters typecheck green, so the leaf chain (`LeafAgree`,
`SatGraphAgree`, `KeyAgree`, `WitnessAgree`, `DefinesAgree`) is placed and
green. The port control matches `[LJ-1.249]`'s warm figure (0.78 s).

## 2. THE D-10 CHECK FIRST: THE STATEMENTS ARE NOT CONSTRAINED

The port's `Body` module takes three leaf parameters at
`ProbeLJ1249.agda:141-151`: the `DefAt` trio and the bare
`ψs : Formula S 13`, `ψa : Formula S 15`. Then:

- `StepAgree` (`ProbeLJ1249.agda:164-168`) states
  `⟨ env ⊨ GB.S.stepBndAt ⟩ → ⟨ env ⊨ StepAt (suc (suc zero)) (suc (suc (suc (suc zero)))) zero ⟩`.
- `GB.S.stepBndAt` is built from `ψs` alone (`:124-128`, `:109-110`).
- `StepAt` is built from `DefAt` alone (`GenSequence.agda:63-66`).

**No parameter, hypothesis or equation relates `ψs` to `DefAt`.**
`[LJ-1.249]`'s "constrained" claim (`lj-1.249-report.md`, section 4) means
each leaf OCCURS in the statement; occurrence is not constraint. This is
exactly the `[LJ-1.244]` `φ₀` shape, one level up: take `ψs` satisfiable
and `DefAt` a step leaf the satisfiable `ψs` does not imply, and the
implication is false. The refutation instance is **INFERRED** (I did not
run it; `[LJ-1.246]` gave the same classification to its `φ₀`
refutation). That the leaves are unrelated is **MEASURED** by reading the
telescope: `ψs`/`ψa` occur only in the premises, `DefAt` only in the
conclusions.

**Consequence.** "Replace the two hypotheses with proofs" is impossible in
the generic port without adding a leaf relation. The port itself is not
wrong: `graph-assembly` (`:176-194`) correctly takes them as hypotheses.
They are an interface, and the interface needs a per-tower supply.

## 3. THE LEAF ADEQUACY, AND WHETHER IT TRANSFERS

The source comment at `src/L/Condensation.lagda.md:5433-5434` is real, and
the names exist nowhere as code: `grep -rn StepAgree\|ApproxAgree src/`
returns only that comment. MEASURED.

The brief says the source "already carries leaf adequacy". What it carries
is `LeafAgree` (`src/L/Condensation.lagda.md:7065-7200`), the two-way
`DefBodyB ↔ DefBody` transfer:

- `out : DefBody → DefBodyB` (`:7189`), machine → story.
- `back : DefBodyB → DefBody` (`:7195`), story → machine.

`StepAgree`/`ApproxAgree` consume story → machine, so the needed direction
is `back`, and it is present. That half of the brief's premise holds.

**It does not transfer into a proof, for two measured reasons.**

1. **`LeafAgree` is an open module, not a theorem.** Its telescope takes
   `twelve-out`/`twelve-back` (`:7097`/`:7100`), which `SatGraphAgree`
   also takes (`:6812`/`:6815`). `grep -rn LeafAgree src/` finds it only
   at its definition and two comment lines; no module instantiates it.
   MEASURED.

2. **The supplier of `twelve-out`/`twelve-back` is unbuilt.** The only
   candidate is `L.Condensation.TwelveAgree.AbstractFrame` instantiated at
   a real bound `K`, and its own comment says so:
   `src/L/Condensation/TwelveAgree.lagda.md:519-522` — "THIS DISCHARGES
   NOTHING (C-38)... Supplying `SatGraphAgree` still needs the frame
   INSTANTIATED at a real `K`, which is `[LJ-1.113]`'s 28 pieces of new
   content." MEASURED by reading the comment and by `grep` finding no
   `AbstractFrame` application outside the file.

**The structural half is generic and already delivered.** `extAtB→extAt`
sits at `src/L/Condensation.lagda.md:2511`, and the `∃̇∈ → ∃̇` drop that
lifts a leaf through the step frame is `ProbeDD25D5`'s
`LeafAgreeG.leaf-out` (`agents/tasks/archive/LJ-1-34/ProbeDD25D5.agda:127-142`),
proved generic in `ψ`. So `StepAgree`/`ApproxAgree` are NOT "exactly the
two leaves agreeing": they are the step/approx-frame lifting (shared,
delivered) composed with the leaf agreement `LeafAgree` (per-tower, placed
but open).

## 4. THE TERM NOT WRITTEN (C-36)

The term that would discharge `StepAgree` and `ApproxAgree` together, at
`file:line`:

1. **`twelve-out` / `twelve-back` at a real bound `K`** — the instantiation
   of `L.Condensation.TwelveAgree.AbstractFrame` (the twelve-row
   `twelveAt ↔ SatGraphB.twelveB` transfer at the graph frame), which is
   `[LJ-1.113]`'s 28 pieces of new content, still unbuilt at HEAD.
   Named at `src/L/Condensation/TwelveAgree.lagda.md:519-522`.

2. **The `LeafAgree` site-fact bundle** (`witK`, `wCodesK`, `wUnCodesK`,
   `wEntryK`, `gCodesK`, `gUnCodesK`, `gEntryK`, `domEntryK`, `domK`,
   `graphWitK`, `keyValK`, `envK`, `defPairK`, `satK`) at the concrete
   graph environment — the LEG-D site facts, stated at
   `src/L/Condensation.lagda.md:7073-7157` and not yet supplied at that
   environment.

3. **The frame lifting placement**: `ProbeDD25D5`'s generic
   `LeafAgreeG`/`BodyAgreeG`/`StepAgreeG` adapted to the current `StepB`
   outer frame (`extAtB`, not `extAt`) and to `ApproxB`'s `domB → domAt`
   step. The pieces exist (`extAtB→extAt` at `:2511`; the `∃̇∈ → ∃̇` drop in
   D5), but nothing in `src/` composes them over `LeafAgree`.

Term 1 is the widest unmeasured term and it gates terms 2 and 3. A build
brief that cannot name term 1 is not ready to send (D-1).

## 5. PER-TOWER LINE COUNT (DD4)

**The two lemmas are not per-tower objects; they have no independent line
count.** They split into:

- **Shared, already built:** the frame lifting. `ProbeDD25D5` measured it
  generic in `ψ` (the generic layer `G` spans `agents/tasks/archive/LJ-1-34/ProbeDD25D5.agda:66-225`,
  about 160 lines), plus `extAtB→extAt` (`src/L/Condensation.lagda.md:2511-2520`).
  Paid once for both towers. The genericity is MEASURED by reading (`module G`
  takes `ψ` as a parameter); `[LJ-1.34]` recorded the probe green.

- **Per-tower, placed but open:** the leaf adequacy `LeafAgree`
  (`src/L/Condensation.lagda.md:7065-7200`, 135 non-blank lines) and its
  support chain `SatGraphAgree`/`KeyAgree`/`WitnessAgree`/`DefinesAgree`.
  This is the L tower's leaf. Its SUPPLY (`twelve-out`/`back`, term 1
  above) is the unbuilt per-tower residue, not `StepAgree`/`ApproxAgree`
  themselves.

So phase 1's last per-tower figure is NOT a two-lemma figure. It is
`[LJ-1.113]`'s 28 pieces plus the placement of the frame lifting. The
brief's "everything below them is green" is TRUE for the At-side readings
(`[LJ-1.238]`) and FALSE for the BS-side leaf supply, which the brief
counts as "already carried" but which is an open telescope.

## 6. ARCHIVE USED (DD18)

One line read named per file.

- `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`, read WHOLE. **Line read
  `:53`**, the original `StepAgree`/`ApproxAgree` hypotheses at the class
  carrier, which `ProbeLJ1249` ports.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`, read WHOLE. **Line read
  `:58`**, `matrix-decode`, the companion that closes to `fst w ≡ Lset (fst γ)`.
- `agents/tasks/archive/LJ-1-52/lj-1.52-report.md`, read `:1-175`.
  **Line read `:63-64`**, "the unbuilt content is `StepAgree` ... and
  `ApproxAgree`", which this run corrects into "the leaf supply is the
  unbuilt content".
- `agents/tasks/archive/LJ-1-57/ProbeLJ157A.agda`, read section 5
  (`:822-985`). **Line read `:946`**, `module SG = ...SatGraphAgree`, the
  probe form whose `twelve-out`/`back` stay parameters.
- `agents/tasks/archive/LJ-1-61/lj-1.61-report.md`, read WHOLE. **Line read
  `:144-146`**, the post-leaf five naming `StepAgree`/`ApproxAgree` from
  `LeafAgree` as step 1.
- `agents/tasks/archive/LJ-1-61/LJ-1.61.md`, read WHOLE. **Line read
  `:80`**, "`StepAgree` and `ApproxAgree` from `LeafAgree`."
- `agents/tasks/archive/LJ-1-34/ProbeDD25D5.agda`, read WHOLE. **Line read
  `:127-142`**, the generic `∃̇∈ → ∃̇` leaf drop, the shared half of the two
  lemmas.
- `agents/tasks/LJ-1-246/lj-1.246-report.md`, read WHOLE. **Line read
  `:68`**, the `φ₀` refutation shape, which `ψs`/`ψa` repeat.
- `agents/tasks/LJ-1-249/lj-1.249-report.md` and `ProbeLJ1249.agda`, read
  WHOLE. **Line read `ProbeLJ1249.agda:164`**, `StepAgree`, the target.
- `agents/tasks/LJ-1-238/GenSequence.agda`, read WHOLE. **Line read
  `:63-66`**, `StepBody` built from `DefAt` alone.
- `src/L/Condensation.lagda.md`, read `:5433-5434`, `:6802-7200`,
  `:2511-2520`. **Line read `:7065`**, `LeafAgree`, the open leaf adequacy.
- `src/L/Condensation/TwelveAgree.lagda.md`, read WHOLE. **Line read
  `:519-522`**, the `[LJ-1.113]` 28-piece supply, the widest unmeasured
  term.

## 7. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:224-227`, already read by `[LJ-1.246]`: the
  matrix is Σ₀ and the carrier is transitive. **These two lemmas touch that
  gap and leave it whole**: `StepAgree`/`ApproxAgree` transfer satisfaction
  between the two codings at a common env; they carry no Δ₀/Σ₁ certificate.
  The Σ₁ certificate lives in the BS leaf (`Δ₀-DefBodyB`,
  `src/L/Condensation.lagda.md:2352`) and is spent by the crossing, not by
  these two. MEASURED by reading: `ProbeLJ1249.agda` has 0 references to
  `Δ₀`, `Σ₁` or `φP`.

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `StepAgree`/`ApproxAgree` build as stated | **MEASURED FALSE.** Unconstrained leaves; section 2 |
| the refutation instance typechecks | **INFERRED.** Reading-based; `[LJ-1.246]` classified its `φ₀` the same way |
| the source carries discharged leaf adequacy | **MEASURED FALSE.** `LeafAgree` is defined, never instantiated; section 3 |
| `twelve-out`/`twelve-back` have a supplier in `src/` | **MEASURED FALSE.** No `AbstractFrame` application outside `TwelveAgree.lagda.md`; its own comment names the 28 pieces |
| the structural lifting is unbuilt | **MEASURED FALSE.** `extAtB→extAt` at `:2511`; the `∃̇∈→∃̇` drop is generic in `ψ` in `ProbeDD25D5` (recorded green at `[LJ-1.34]`) |
| `amb` is supplied outright | **MEASURED FALSE.** It stays conditional on the leaf chain, which is open |
| `StepAgree`/`ApproxAgree` are "exactly the two leaves agreeing" | **MEASURED FALSE.** They are the frame lifting composed with `LeafAgree`, one level above the leaf |

## 9. RULES ANSWERED

- **D-1.** The abort criterion was fixed by the brief. The branch that
  fired is closest to NEITHER BUILDS, with the D-10 correction: the
  statements are refutable, and the concrete term is named at `file:line`.
- **D-10.** Done first, section 2. The leaves are unrelated; the statement
  is satisfiable-by-absurdity and unprovable at once.
- **C-36.** The term is named, section 4, three parts, term 1 the widest.
- **C-44.** The brief's "already carries leaf adequacy" claim was unchecked.
  I checked it: placed but open.
- **C-45.** I audited the telescope, not the port's assembly. `ψs`/`ψa`
  occur only in premises, `DefAt` only in conclusions.
- **C-22.** The report skeleton was written before the first run.
- **C-12.** One process, `-M8g`, cap never raised.
- **DD4.** Section 5: the lifting is shared and delivered; the leaf is
  per-tower, placed but open.
- **DD8.** One number per claim: 0 proof lines, 28 unbuilt pieces, 135-line
  open `LeafAgree` module.
- **DD18.** Archive and literature sections above.
- **I-5, R-34.** No probe under `src/`. No heap wall.
