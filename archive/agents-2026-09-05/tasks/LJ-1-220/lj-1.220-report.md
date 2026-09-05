# LJ-1.220 report: parameterize every leak, census the chain in one pass

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Written incrementally
(C-22). No master edited. No commit, no push. Every negative is MEASURED or
INFERRED, in those words.

## 0. LEAD

**EXIT 0. TWO COUNTS, REPORTED APART.**

- **(a) SUPPLIED: 2 names.** `keyOf` and `keyOf-fst`. They are the delivered
  `L.Coding.Recover` one-liners, and every ingredient is already green in the
  generic Model (`GenModel.agda`): `prʟ` at `:193`, `prʟ-fst` at `:196`,
  `numeralL`/`numeralL-fst` at `:16-17`. MEASURED.
- **(b) PARAMETERIZED: 22 names, because nothing on record supplies them.**
  This is the chain width. MEASURED. Each is an undischarged hypothesis (C-38).

**The 22 parameters come from exactly 9 home modules.** Against `[LJ-1.213]`'s
17-module chain, the body ACTUALLY touches 9 modules whose names pin `𝒮ʟ` and
must go generic. `L.Coding.Recover` is NOT one of them: the generic Model
already supplies its content. MEASURED.

**Two INFERRED findings from `[LJ-1.219]` are now MEASURED.** `extAt-in` and
the `domAt` trio compose. The body runs past `:142` to `DefAt-out` and exits 0.

**The instrument has one blind spot, and it is a finding.** Three names the
body uses DEFINITIONALLY cannot be parameterized, because a bare parameter
cannot express a reduction: `GraphWitAt` (pattern-matched), `codeS` and `keyS`
(`fst (keyS A φ)` must reduce to `pr (# n) (fst (codeS A φ))`). I reconstructed
them transparently at the ambient class, where their only tower-pinning content
is the trivial `tt*` proof. They are not hypotheses and not exports.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process. `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised. No run
passed 20 minutes. No heap exhaustion.

The machine is not quiet. Load sits beside every figure. The first successful
run was the warm-up and was discarded. The verdict rests on exit code 0 and the
parameter count, not on seconds.

## 2. ARTIFACTS

| file | what it is |
|---|---|
| `Probe.agda` | the parameterize probe. The `[LJ-1.219]` body, wrapped in `module Body` with 22 parameters, 2 supplied names, and 5 transparent reconstructions. Exit 0 |
| `lj-1.220-report.md` | this report |

The file is new. Nothing is deleted. It sits in `agents/tasks/LJ-1-220/`. It is
a probe. Nothing lands in `src/`. `check-probes.py` is clean.

## 3. COUNT (a): NAMES SUPPLIED FROM A GENERIC MODULE

Two names. The rule a corrected census must follow: a name a ported generic
module already exports is NOT a leak. Try to supply it first.

| name | supplied by | generic line |
|---|---|---|
| `keyOf` | `prʟ`, `numeralL` in `LJ-1-210.GenModel` | `GenModel.agda:193` (`prʟ`), `:16` (`numeralL`) |
| `keyOf-fst` | `prʟ-fst`, `numeralL-fst` in `LJ-1-210.GenModel` | `GenModel.agda:196` (`prʟ-fst`), `:17` (`numeralL-fst`) |

The supplied definitions, written in `Probe.agda` after `open AtFull`:

```
keyOf n x = prʟ (numeralF n) x
keyOf-fst n x = prʟ-fst (numeralF n) x ∙ cong₂ pr (numeralF-fst n) refl
```

`numeralF` and `numeralF-fst` are this file's own numeral operations, the same
six from `[LJ-1.210]`. `prʟ` and `prʟ-fst` are opened from `AtFull`. The body
of `keyOf-fst` is character-for-character the generic `tagBridge` at
`GenModel.agda:215`. MEASURED.

**`[LJ-1.219]` named `L.Coding.Recover` as brick two. That brick was never a
brick.** Its two names are one-liners already built in the generic Model. The
`[LJ-1.219]` finding is REFUTED by supply, not by port. MEASURED.

## 4. COUNT (b): THE PARAMETERIZED LEAK LIST, one row per name

Each type below is the delivered signature with the carrier `𝒮ʟ` replaced by
the ambient `S = hPropStructure.S (𝒮ᵥ ↾ M)` with `M = Full`. Every parameter is
an undischarged hypothesis (C-38): nothing at the ambient class supplies it.

| # | name | home module | type written |
|---|---|---|---|
| 1 | `keyArityAtL` | `src/L/Coding/CodeSet.lagda.md:135` | `∀ {n} → Fin n → ℕ → Formula S n` |
| 2 | `keyArityAtL-in` | `src/L/Coding/CodeSet.lagda.md:145` | `∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n) (z : S) → fst (lookup c γ) ≡ pr (# k) (fst z) → ⟨ γ ⊨ keyArityAtL c k ⟩` |
| 3 | `keyArityAtL-out` | `src/L/Coding/CodeSet.lagda.md:138` | `∀ {n} (c : Fin n) (k : ℕ) (γ : S ^ n) → ⟨ γ ⊨ keyArityAtL c k ⟩ → ∥ (Σ[ z ∈ S ] (fst (lookup c γ) ≡ pr (# k) (fst z))) ∥₁` |
| 4 | `hasWitnessAt` | `src/L/Coding/CodeSet.lagda.md:240` | `∀ {n} → Fin n → Fin n → Formula S n` |
| 5 | `witnessAt-in` | `src/L/Coding/CodeSet.lagda.md:365` | `(A : S) → ∀ {n k} (b c : Fin n) (γ : S ^ n) (φ : Formula ⟪ fst A ⟫ k) → fst (lookup b γ) ≡ fst A → fst (lookup c γ) ≡ fst (keyS A φ) → ⟨ γ ⊨ hasWitnessAt b c ⟩` |
| 6 | `witnessAt-out` | `src/L/Coding/CodeSet.lagda.md:375` | `(A : S) → ∀ {n} (b c : Fin n) (γ : S ^ n) → fst (lookup b γ) ≡ fst A → ⟨ γ ⊨ hasWitnessAt b c ⟩ → (k : ℕ) (z : S) → fst (lookup c γ) ≡ pr (# k) (fst z) → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ k ] (fst (lookup c γ) ≡ fst (keyS A ψ))) ∥₁` |
| 7 | `satGraphAt` | `src/L/Coding/Graph.lagda.md:204` | `∀ {n} → Fin n → Fin n → Fin n → Formula S n` |
| 8 | `graphAt-in` | `src/L/Coding/Graph.lagda.md:210` | `∀ {n} (B x y : Fin n) (γ : S ^ n) → ∥ GraphWitAt B x y γ ∥₁ → ⟨ γ ⊨ satGraphAt B x y ⟩` |
| 9 | `graphAt-out` | `src/L/Coding/Graph.lagda.md:215` | `∀ {n} (B x y : Fin n) (γ : S ^ n) → ⟨ γ ⊨ satGraphAt B x y ⟩ → ∥ GraphWitAt B x y γ ∥₁` |
| 10 | `keyʟ` | `src/L/Coding/Table.lagda.md:82` | `∀ {n} → Formula S n → S` |
| 11 | `Sat` | `src/L/Coding/Sat.lagda.md:142` | `(B : S) → ∀ {n} → Formula S n → S` |
| 12 | `slot` | `src/L/Coding/Table.lagda.md:106` | `(B : S) → ∀ {n} → Formula S n → S` |
| 13 | `satTable` | `src/L/Coding/Table.lagda.md:103` | `(B : S) → ∀ {n} → Formula S n → S` |
| 14 | `total` | `src/L/Coding/Table.lagda.md:277` | `(B : S) → ∀ {n} (φ : Formula S n) (x : V ℓ) → ⟨ x ∈ fst (slot B φ) ⟩ → ∥ (Σ[ y ∈ S ] ⟨ pr x (fst y) ∈ fst (satTable B φ) ⟩) ∥₁` |
| 15 | `inSlot` | `src/L/Coding/Table.lagda.md:287` | `(B : S) → ∀ {n} (φ : Formula S n) (x y : V ℓ) → ⟨ pr x y ∈ fst (satTable B φ) ⟩ → ⟨ x ∈ fst (slot B φ) ⟩` |
| 16 | `entry-in` | `src/L/Coding/Table.lagda.md:321` | `(B : S) → ∀ {n} (φ : Formula S n) → ⟨ pr (fst (keyʟ φ)) (fst (Sat B φ)) ∈ fst (satTable B φ) ⟩` |
| 17 | `slotClosed` | `src/L/Coding/Slot.lagda.md:262` | `(B : S) → ∀ {n} (φ : Formula S n) {k : ℕ} (γ : S ^ k) → ⟨ (B ∷ satTable B φ ∷ slot B φ ∷ γ) ⊨ closedAt (suc (suc zero)) ⟩` |
| 18 | `soundness` | `src/L/Coding/Sound.lagda.md:1099` | `(B : S) → ∀ {n} (φ : Formula S n) {k : ℕ} (γ : S ^ k) → Clauses (B ∷ satTable B φ ∷ slot B φ ∷ γ) (suc (suc zero)) (suc zero) zero` |
| 19 | `asConst` | `src/L/Coding/Bridge.lagda.md:124` | `(B : S) → ⟪ fst B ⟫ → S` |
| 20 | `defSet-Sat` | `src/L/Coding/Bridge.lagda.md:621` | `(A : S) → (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫) → (⟪ fst A ⟫↪ m ∈ DefOf.defSet (fst A) ψ) ≡ (envOne (⟪ fst A ⟫↪ m) ∈ fst (Sat A (mapFo (asConst A) ψ)))` |
| 21 | `keyBridge` | `src/L/Coding/Uniform.lagda.md:180` | `(A : S) → ∀ {n} (ψ : Formula ⟪ fst A ⟫ n) → fst (keyS A ψ) ≡ fst (keyʟ (mapFo (asConst A) ψ))` |
| 22 | `pinned` | `src/L/Coding/Unique.lagda.md:884` | `∀ {k} (γ : S ^ k) (Ci Ti Bi : Fin k) → ⟨ γ ⊨ closedAt Ci ⟩ → ⟨ γ ⊨ domAt Ti Ci ⟩ → Clauses γ Ci Ti Bi → ∀ {m} (ψ : Formula S m) (c y : S) → fst c ≡ fst (keyʟ ψ) → ⟨ fst c ∈ fst (lookup Ci γ) ⟩ → ⟨ pr (fst c) (fst y) ∈ fst (lookup Ti γ) ⟩ → fst y ≡ fst (Sat (lookup Bi γ) ψ)` |

Two dependent parameters are written above and stated in the probe: `Clauses`
(the 12-way product of clause satisfactions) and `GraphWitAt` (the witness Sigma
the body pattern-matches). They are transparent reconstructions, not
hypotheses; see section 6.

**The parameter block: 22 parameters, 58 non-blank lines** (`Probe.agda:141`
`module Body` through `:198` `where`). MEASURED by `grep -c .`.

## 5. THE MODULE COUNT, against the 17

The 22 parameters group into **9 home modules**:

| home module | names | count |
|---|---|---:|
| `L.Coding.CodeSet` | `keyArityAtL`, `keyArityAtL-in`, `keyArityAtL-out`, `hasWitnessAt`, `witnessAt-in`, `witnessAt-out` | 6 |
| `L.Coding.Graph` | `satGraphAt`, `graphAt-in`, `graphAt-out` | 3 |
| `L.Coding.Table` | `keyʟ`, `slot`, `satTable`, `total`, `inSlot`, `entry-in` | 6 |
| `L.Coding.Slot` | `slotClosed` | 1 |
| `L.Coding.Sound` | `soundness` | 1 |
| `L.Coding.Unique` | `pinned` | 1 |
| `L.Coding.Sat` | `Sat` | 1 |
| `L.Coding.Bridge` | `asConst`, `defSet-Sat` | 2 |
| `L.Coding.Uniform` | `keyBridge` | 1 |
| **total** | | **22** |

**The body touches 9 of the 17 modules and they must go generic. MEASURED.**
`[LJ-1.213]`'s 17 was INFERRED as a chain count. The body does not name the
other 8 (`L.Absoluteness`, `L.Coding.Closed`, `L.Coding.EnvSet`,
`L.Coding.InL`, `L.Coding.Model`, `L.Coding.Powerset`, `L.Coding.Recover`,
`L.Coding.Shape`). Seven of those eight are suppliers' suppliers, needed
transitively by the port, never written by this body. The eighth,
`L.Coding.Recover`, is not needed at all: its two names are already supplied
(section 3).

**Four fixed imports the body names do NOT leak. MEASURED.** They already
compose at the ambient class, because they are over `V ℓ`, not `𝒮ʟ`:
`V.Coding` (`pr`), `L.Constructible` (`𝒟ₒ`, `𝒟ₒ-intro`, `𝒟ₒ-inv`),
`L.Definability` (`DefOf`), `L.Coding.Environment` (`env`).

So the measured answer to the DD4 question "how many modules must go generic
before the shared body serves both towers" is **9**, not 17. Count (a) is work
already done; count (b) is the width that remains.

## 6. THE INSTRUMENT'S BLIND SPOT: three names are not parameters

Three names the body uses DEFINITIONALLY cannot be stated as module parameters,
because a parameter cannot express a reduction:

| name | home module | why it cannot be a parameter | what I did |
|---|---|---|---|
| `GraphWitAt` | `src/L/Coding/Graph.lagda.md:191` | the body pattern-matches it as a Sigma at `graphAt-unique` | reconstructed transparently from the generic Model's `closedAt`, `domAt`, `twelveAt` |
| `codeS` | `src/L/Coding/CodeSet.lagda.md:297` | the body needs `fst (keyS A φ) ≡ pr (# n) (fst (codeS A φ))` definitionally | reconstructed: `codeS A φ = VCode.⌜ mapFo ⟪ fst A ⟫↪ φ ⌝ , tt*` |
| `keyS` | `src/L/Coding/CodeSet.lagda.md:300` | same definitional link | reconstructed: `keyS A {n} φ = pr (# n) (fst (codeS A φ)) , tt*` |

These three are NOT hypotheses and NOT exports of a generic module. Their only
tower-pinning content in the delivered code is the proof that a formula's code
is constructible (`codeL`, `keyL`); at the ambient class `M = Full` that proof
is `tt*`. So they compose. **The parameterize instrument measures the opaque
leaks; the definitional leaks are measured by reconstruction, and they come
back tower-neutral.** MEASURED.

The transparent reconstruction is **30 non-blank code lines**: `Clauses` (10),
`twelveAt` (8), `GraphWitAt` (8), `codeS` (2), `keyS` (2). These are not DD4
plumbing: a delivered generic supplier pays them once and both towers get them.

## 7. DD4 NUMBERS, reported apart

| number | lines | basis |
|---|---:|---|
| parameter block (count b) | 58 | 22 parameters, `Probe.agda:141-198`, non-blank |
| supplied (count a) | 9 | `keyOf` (2) + `keyOf-fst` (2) + the comment (5), non-blank |
| transparent reconstruction | 30 | 5 definitions, non-blank code |
| `[LJ-1.219]` plumbing | 21 | unchanged, not recomputed here |

The 22 parameters are an INSTRUMENT, not DD4 plumbing. They are hypotheses a
delivered port discharges by supplying the generic supplier; the shared body
pays nothing for them. Count (a) is work already done and is reported apart.

## 8. TIMINGS

All runs use `GHCRTS="-A64m -I0 -M8g"`.

| run | exit | seconds | load |
|---|---:|---:|---|
| warm-up (discarded) | 0 | not timed | not timed |
| kept 1 | 0 | 1.10 | 4.73 / 4.82 / 4.97 |
| kept 2 | 0 | 1.02 | 4.73 / 4.82 / 4.97 |
| kept 3 | 0 | 1.00 | 4.73 / 4.82 / 4.97 |

Three kept runs: 1.10, 1.02, 1.00 seconds. Exit 0 each time. The seconds decide
nothing. Exit code 0 and the parameter count decide.

## 9. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the body typechecks at the ambient class | **MEASURED TRUE.** Exit 0 |
| the body reaches exit 0 with fewer than 9 modules' names | **MEASURED FALSE.** 9 modules |
| `extAt-in` composes | **MEASURED TRUE.** The body reaches `hasKey` (`extAt-in`) and typechecks |
| the `domAt` trio composes | **MEASURED TRUE.** `graphAt-holds` and `graphAt-unique` use `domAt-intro` and `domAt-out`, and typecheck |
| the chain is 17 modules | **MEASURED FALSE for the body.** The body touches 9; 8 are transitive or already built |
| `L.Coding.Recover` is brick two | **MEASURED FALSE.** Its two names are supplied by `GenModel` |
| every leaking name is parameterizable | **MEASURED FALSE.** `GraphWitAt`, `codeS`, `keyS` need reconstruction, not parameters |

## 10. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-219/lj-1.219-report.md`, read WHOLE. TOOK the `:142`
  `keyOf` wall, the 21-line join figure, and the INFERRED status of `extAt-in`
  and the `domAt` trio, which this probe converts to MEASURED.
- `agents/tasks/LJ-1-219/JoinAtAmbient.agda`, read WHOLE. It is the starting
  file; my `Probe.agda` is its body wrapped in `module Body`.
- `agents/tasks/LJ-1-213/lj-1.213-report.md` and `LJ-1.213.md`, read WHOLE.
  TOOK the 17-module chain, the 5,822 lines, the 125-line census floor, the
  bottom-up order. My 9-module count prices the body's share of the 17.
- `agents/tasks/LJ-1-210/lj-1.210-report.md`, read at section 8. TOOK the
  17-module census table and the class-surface figure. `GenModel.agda` supplies
  `closedAt`, `domAt`, the 12 clause formulas, `prʟ`, `prʟ-fst`, and the
  `numeralL`/`numeralL-fst` parameters this probe uses.
- `src/L/Coding/Powerset.lagda.md:41-86`, `:125-129`, `:445-496`, read. TOOK the
  fixed imports and the delivered `defSet-Sat`/`inSat` shapes.
- `src/L/Coding/Recover.lagda.md:112-116`, read. TOOK the `keyOf`/`keyOf-fst`
  one-liners, which this probe supplies instead of parameterizes.
- `src/L/Coding/{CodeSet,Graph,Table,Slot,Sound,Unique,Sat,Bridge,Uniform}.lagda.md`,
  read at the signature lines cited in section 4. TOOK each home signature.
- `archive/dev/TASKS-archived.md`, read for shape only. No figure transfers.

## 11. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md:370-383` is a table of 12 rows: **8 EITHER and
4 PER-TOWER** (A, B, C3, C4, C5, C6, E, F are EITHER; C1, C2, D, G are
PER-TOWER). The per-tower content is the level-hood certificate and the
definable well-order, both satisfaction-based on the Def tower.

This corrects the brief's figure, which said "nine tower-neutral and three
per-tower". The word "nine" does not occur in that file. MEASURED by reading
the table.

**The measured leak list does not match that split as modules.** Every one of
the 22 names and all 9 modules are satisfaction-based coding machinery: formula
coding (`codeS`, `keyS`), the satisfaction recursion (`Sat`), its tables
(`slot`, `satTable`, `keyʟ`), its soundness and uniqueness (`soundness`,
`pinned`), and the witness and bridge lemmas. As mathematics they all sit on ONE
side of Devlin's table: the Def tower's per-tower, satisfaction carrier. As
Agda they are 9 separate modules, each independently pinning `𝒮ʟ`.

So Agda's module boundaries cut ACROSS Devlin's step split, in the same way
`[LJ-1.219]` found for `keyOf`: one mathematical step (the definable powerset)
is spread over nine modules, and each module is tower-neutral as an idea and
tower-fixed as a term. The census does not subdivide Devlin's steps; it
subdivides his per-tower carrier.

## 12. RULES ANSWERED

- D-1. The abort criterion was fixed by the brief. The EXIT-0 branch fired: 22
  parameters, reported in full, with 2 supplied names reported apart.
- C-38 as extended. Every parameter is an undischarged hypothesis. Nothing at
  the ambient class supplies them. Section 4 says so.
- C-42. I measure one site: the Powerset body at the ambient class. I do not
  price the 8 modules the body does not name.
- P-l. `[LJ-1.219]`'s 21 is a comparable, not a price. I report my own 58.
- C-22. The report file existed before the first Agda run.
- C-36. The terms I could not parameterize are `GraphWitAt`, `codeS`, `keyS`.
  Section 6 names them and why.
- C-12. One process, `-M8g`, cap never raised. Load beside every figure.
- DD0, DD8. One number per claim. Line counts are non-blank lines.
- DD4. Section 7. The parameter block is an instrument, reported apart.
- DD23. No mathematical prose written. No master edited.
- D-26, D-29, D-30, I-5, P-k, P-m, P-y, C-39, C-40, D-10, R-40. No probe under
  `src/`; `check-probes.py` is clean; `lint-agda.py` and `lint-prose.py` are
  clean.
