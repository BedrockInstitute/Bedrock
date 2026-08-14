# LJ-1.255 report: build the eleven fields `envSetK` unlocks

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**N of eleven built: 5.** `envK-mem`, `envK-neg`, `envK-top`, `envK-imp`,
`envK-allin` all typecheck (exit 0) at the concrete site, on top of
[LJ-1.254]'s green `envSetK` and `sucK`. **The four `envInK-*` and `someEnv`
do NOT build as stated, and the reason is one missing hypothesis, not the
budget.** `t0eq`/`t1eq` really do cost zero, and this task measured that
rather than inferring it.

**Marginal lines per field, apart from shared setup: 17 with the field
signature, 11 for the proof body alone.** The five `envK-*` fields cost 85
lines total, and the one-time setup beneath them (the decode `envSetAt-ident`,
the decode `envOverAt-in`, `#∈λ`, `transK`) costs 38 lines.

## 1. WHAT BUILT AND WHAT DID NOT (MEASURED)

Probe `agents/tasks/LJ-1-255/ProbeLJ1255.agda`, module `Supply`, the same
concrete site as [LJ-1.254]: `K = Lset lam`, carrier `B₀ = LsetS gam ordγ`,
hypotheses `lam, ordλ, succλ, ∅∈λ, gam, ordγ, γ∈λ, ω∈γ`.

### 1.1 The five envK-* fields, GREEN, exit 0

Each concludes `fst E ∈ Lset lam` from a numeral premise
`∥ Σ n, fst ar ≡ # n ∥₁` and a satisfaction `⊨ envSetAt`. The reader is
exactly the brief's: `envSetAt-ident` (L3, the shared decode) turns the
satisfaction into `E ≡ Generic.envSetGen B₀ ar`; `envSetK` turns the numeral
into `envSetGen B₀ ar ∈ Lset lam`; one `subst` closes it.

| field | arity slot | carrier slot | lines |
|---|---:|---:|---:|
| `envK-mem` | 4 | 6 | 17 |
| `envK-neg` | 4 | 6 | 17 |
| `envK-top` | 3 | 5 | 17 |
| `envK-imp` | 6 | 8 | 17 |
| `envK-allin` | 5 | 7 | 17 |

17 lines each = 6 signature + 11 proof body. The signature is the field type,
already written in the `TFacts` record; the supply's marginal cost is the 11
proof lines.

### 1.2 The four envInK-* fields, BLOCKED, and the term I could not write (C-36)

The field as it stands in `TFacts` (`TwelveAgree.lagda.md:216-244`) has the
premise `⟨ fst ar ∈ K ⟩` and NO numeral equation. The brief's reader
(`Generic.Holds.bwd` + `envSetK` + `transK`) cannot close it: the delivered
join `envSetK` is numeral-restricted and needs `fst ar ≡ # n`, which this
field's telescope does not contain. The term that fails is the last step:

```agda
  -- envInK-mem yc b a ar c E z arK h =
  --   transK z (Generic.envSetGen B₀ ar)
  --     (envOverAt-in (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ B₀ ∷ [])
  --        (suc (suc (suc (suc zero))))
  --        (suc (suc (suc (suc (suc (suc zero)))))) z h)
  --     ? -- envSetGen B₀ ar ∈ Lset lam  [needs fst ar ≡ # n]
```

`envOverAt-in` (L4) gives `z ∈ envSetGen B₀ ar`; the last step needs
`envSetGen B₀ ar ∈ Lset lam`, and the only delivered supplier is
`envSetK ar n arn`, which demands a numeral `arn`. **What each of the four
needs: the numeral equation `(n : ℕ) → fst ar ≡ # n` (the same cure the
`envK-*` fields carry), OR a general-arity power closure
`envSetGen B ar ∈ Lset lam` from `ar ∈ Lset lam`, which is NOT delivered.**
This is exactly the disease [LJ-1.173] section 31.2-31.3 named; its cure table
assigned `envInK-*` the `ar ∈ K` hypothesis, and that cure is insufficient
because the join itself is numeral-restricted.

### 1.3 someEnv, BLOCKED, and dearer than the ten (MEASURED as a read)

`someEnv` (`TwelveAgree.lagda.md:285`, `someEnvDef` at
`LowerAgree.lagda.md:52-61`) takes `ya ∈ K, yc ∈ K, ar ∈ K` and must
construct an `E ∈ K` satisfying `envHypB2` = `envSetB zero (suc⁵ zero)
(suc⁷ B) (suc⁷ K)` — the BOUNDED environment-set description. It is blocked
in TWO places, and both are real work, not plumbing:

1. `E ∈ K` needs `envSetGen B₀ ar ∈ Lset lam` from `ar ∈ K` alone: the SAME
   missing numeral (or general power closure) as 1.2.
2. `E ⊨ envSetB` is the adequacy join [LJ-1.173] section 3.4 priced at
   **about 120 lines**: the bounded `envFoB` against `envSetGen`, both
   directions, through `carveSat`'s `Δ₀` witness.

So `someEnv` is dearer than the envK-* and envInK-* fields combined: it needs
the numeral cure PLUS the ~120-line adequacy. **0 built.**

### 1.4 t0eq and t1eq really cost zero (MEASURED, not inferred)

`t0eq`/`t1eq` are Type-level premises at the consumer's own site, not
obligations the supply proves: `src/L/Condensation.lagda.md:3063-3067`
defines `t0eq = fst (lookup t0 γ) ≡ fst (numeralL 0)` and `t1eq` likewise,
and they are consumed as hypothesis parameters (`:3082`, `:3120`), supplied
by `refl` where the consumer's environment already holds `numeralL 0`/`1` at
the `t0`/`t1` slots. **The brief's inference ("the consumer's site states
them; the supply pays zero") is CORRECT, and I now mark it MEASURED rather
than INFERRED.**

## 2. THE MARGINAL RATE, AND IT BREAKS THE 255

**255 / 28 = 9.1 lines per field.** My measured marginal is **17 lines per
field with the signature, 11 for the proof body alone** — 1.2x to 1.9x the
budget. The field entries were priced at about 1.5 lines each in [LJ-1.168]
section 4.1; **the measured entry is about 11 proof lines, a ~7x undercount.**

The five `envK-*` fields alone cost **85 lines**, plus the **38 lines of
one-time setup** (`envSetAt-ident` L3 25, `envOverAt-in` L4 8, `#∈λ` 2,
`transK` 3). So the envK group is 123 lines for 5 fields.

**Verdict: the 255 does NOT hold as a marginal figure.** If the remaining
27 fields cost the same 11-17 lines each, they price at 297-459 lines before
the shared lemmas, and the total passes 255 well before the 28th field. The
255 was built on a 1.5-line entry estimate that this probe refutes.

## 3. SECONDS, LOAD, RUN COUNT

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run past
20 minutes. No heap exhaustion. No kill. The first (cold) check pulled the
whole dependency chain at 7m9s real and is the discarded warm-up.

| run | exit | user s | real s | load |
|---|---:|---:|---:|---|
| warm-up (discarded) | 0 | 1.16 | 1.40 | 4.40 |
| kept 1 | 0 | 1.13 | 1.27 | 4.40 |
| kept 2 | 0 | 1.11 | 1.25 | 4.40 |
| kept 3 | 0 | 1.10 | 1.22 | 4.40 |

Mean user time of the three kept runs: **about 1.11 s**. The five envK-*
fields plus the shared decodes add nothing measurable to [LJ-1.254]'s 1.08 s;
none of this walls, exactly as [LJ-1.254] measured for `sucK`.

## 4. DD4

**The eleven fall where [LJ-1.113]:219-239 put them, with one correction.**

- The 9 `envK-*`/`envInK-*` fields are coding machinery: each concludes a
  K-membership from a coding-formula satisfaction, and the proof is the
  L3/L4 decode plus the join, all stated over the structure parameters. The
  J tower re-instantiates them against its own `Lset lam` and carrier, but
  the proof shape is shared.
- `someEnv` and `t0eq`/`t1eq` are the tower fields: they name the concrete
  slots and the environment the tower's condensation builds.

**The correction:** the probe's `envSetK` is B₀-FIXED — it specializes
`B = LsetS gam ordγ` and drops the `B ∈ K` premise. A generic shared helper
over the carrier slot needs the GENERAL field `envSetK : (B ar) → … →
envSetGen B ar ∈ K` (`TwelveAgree.lagda.md:302-307`), which is the truly
shared form and which [LJ-1.254] did not build. So the join beneath the nine
is tower-specific as the probe wrote it; the shareable form is the TFacts
field, still unbuilt.

## 5. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| all eleven build | **MEASURED FALSE.** 5 of 11 |
| `envK-*` (5) build | **MEASURED TRUE.** exit 0 |
| `envInK-*` (4) build as stated | **MEASURED FALSE.** the join needs a numeral the field lacks |
| `someEnv` builds as stated | **MEASURED FALSE.** same missing numeral plus the ~120-line adequacy |
| `t0eq`/`t1eq` cost the supply anything | **MEASURED FALSE.** consumer-site premises, `:3063-3067` |
| the 255 holds as a marginal figure | **MEASURED FALSE.** 17 (or 11) lines/field against 9.1 |
| a wall occurred | **MEASURED FALSE.** max 7m9s cold, ~1.1 s warm |
| I edited a master | **MEASURED FALSE.** only `agents/tasks/LJ-1-255/` written |
| I built the other 16 fields | **MEASURED FALSE.** none |

## 6. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-254/lj-1.254-report.md`, read WHOLE. Line read `:64`,
  the twelve-row table naming the eleven and the readers.
- `agents/tasks/LJ-1-254/ProbeLJ1254.agda`, read WHOLE. Line read `:102`,
  `envSetK`'s numeral-restricted type.
- `agents/tasks/LJ-1-199/lj-1.199-report.md`, read section 5. Line read
  `:128`, the eleven named before the join existed.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`, read section 4. Line read
  `:338`, the L1-L9 table with the 1.5-line entry estimate.
- `agents/tasks/LJ-1-173/lj-1.173-report.md`, read sections 3 and 31. Line
  read `:724`, the nine fields carrying the disease and the two cures.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`, read `:219-239`. Line read
  `:219`, the 28 and the 25-3 split.
- `src/L/Condensation/TwelveAgree.lagda.md`, read whole. Line read `:216`,
  the `envInK-mem` field with the `ar ∈ K` premise and no numeral.
- `src/L/Coding/Key.lagda.md`, read `:476`. Line read `:476`,
  `envSetNumeral∈`'s `ω ∈ σ` hypothesis.
- `archive/dev/TASKS-archived.md`, read the header. Line read `:10`, the
  shape note; nothing in the retired route bears on the numeral question.

## 7. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md`, via [LJ-1.254] section 7. **Devlin's
  construction needs FEWER than these eleven facts.** His arities are all
  finite, so the numeral restriction — the one thing that makes `envSetK`
  and the five `envK-*` provable — is HIS form, not an artifact. The eleven
  environment facts are largely an artifact of the coding: they are the
  satisfier-in-K closures the machine's satisfaction relation demands,
  which Devlin's prose never states separately because his construction is
  not a machine coding. The genuinely mathematical residue is `sucK` and
  `envSetK`, both of which are Devlin's `α > ω` plus the definable-powerset
  closure. The four `envInK-*` and `someEnv` inherit the same numeral
  restriction; with it they are Devlin's finite-arities form too.

## 8. WHAT I RECOMMEND, offered not taken

1. **The cure is atomic across the ten, not per-field.** `envInK-*` and
   `someEnv` need the SAME numeral equation the `envK-*` fields already
   carry. [LJ-1.173] section 35 already measured that curing nine without
   curing the sibling records breaks the tree; this probe adds that the
   `ar ∈ K` cure assigned to `envInK-*` is insufficient on its own.
2. **Re-price step 6 with the measured entry rate**, not the 1.5-line
   estimate: about 11-17 lines per coding field.
3. **Fund the `someEnv` adequacy** ([LJ-1.173]'s ~120 lines) as its own
   block before dispatching the remaining 16.
