# LJ-1.257 report: the four `envInK-*` and `someEnv` are not blocked after all

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**N of five built: 5.** `envInK-mem`, `envInK-neg`, `envInK-top`,
`envInK-imp` and `someEnv` all typecheck (exit 0) at the concrete site, WITH
the numeral premise the cure adds to the four `envInK-*`. `agents/tasks/LJ-1-257/ProbeLJ1257.agda`.

**Collapsed line count for the five `envK-*`: 67 against their 85.**
One `envK-gen` shell (15 lines) plus five applications (52 lines) replaces
the five written-out bodies. **Proof bodies shrink from 55 to 30 lines.**

**The numeral premise must be added to `TFacts`** (and to `LFacts`/`UFacts`).
It is a master change; I did not make it. Its consumers are named and priced
in section 4.

## 1. WHAT BUILT (MEASURED, exit 0)

Probe `agents/tasks/LJ-1-257/ProbeLJ1257.agda`, module `Supply`, the same
concrete site as `[LJ-1.254]` and `[LJ-1.255]`: `K = Lset lam`, carrier
`B₀ = LsetS gam ordγ`, hypotheses `lam, ordλ, succλ, ∅∈λ, gam, ordγ, γ∈λ,
ω∈γ`.

The five built, each WITH the numeral premise the four `envInK-*` lack in the
master:

| field | what it closes | marginal lines |
|---|---|---:|
| `envInK-mem` | `z ∈ K` from `⊨ envOverAt` + numeral + `ar ∈ K` | 11 |
| `envInK-neg` | `z ∈ K` from `⊨ envOverAt` + numeral + `ar ∈ K` | 11 |
| `envInK-top` | `z ∈ K` from `⊨ envOverAt` + numeral + `ar ∈ K` | 11 |
| `envInK-imp` | `z ∈ K` from `⊨ envOverAt` + numeral + `ar ∈ K` | 12 |
| `someEnv` | `Σ E, E ∈ K × ⊨ envSetB` from `ya,yc,ar ∈ K` + numeral | 30 |

The four `envInK-*` collapse into one `envInK-gen` shell (12 lines) plus four
applications (45 lines). The shell is `envOverAt-in` + `envSetK` + `transK`,
the same three steps the four would otherwise write four times.

`someEnv` builds exactly as `[LJ-1.256]` said it would, in the four delivered
lines plus the generic environment set: `E = Generic.envSetGen B₀ ar`,
`E ∈ K` is `envSetK`, `⊨ envSetAt` is `Generic.Holds` (three `refl`s), and
`⊨ envSetB` is the DELIVERED `EnvSet.back` at `src/L/Condensation.lagda.md:3042`,
instantiated at a 4-slot frame `E ∷ ar ∷ B₀ ∷ level ∷ []` with
`level = LsetS lam ordλ`. The 120-line adequacy `[LJ-1.255]` priced is
MEASURED FALSE: it is four delivered lines plus the module application.

**The five `envK-*` still build**, now as applications of `envK-gen`. Nothing
regressed: exit 0 over the whole file.

## 2. COLLAPSED LINE COUNT FOR THE FIVE `envK-*`

Measured by non-blank code lines, `ProbeLJ1257.agda`:

| form | lines |
|---|---:|
| original five `envK-*` (ProbeLJ1255) | **85** (17 each) |
| collapsed: `envK-gen` shell | 15 |
| collapsed: five applications | 52 |
| **collapsed total** | **67** |

**67 against 85** is the brief's number. The sharper number is the proof
body, which is the part the per-field rate cares about: the original wrote
the 11-line body five times (55 lines); the collapse writes the 10-line
`envK-gen` body once plus a 4-line application five times (**30 body lines**).
**55 to 30, a 45 percent cut.**

The one extra premise over `[LJ-1.256]`'s predicted `~11 + 5×2..3` is
`qb : lookup bi γ ≡ B₀` (`refl` at every call site), which is exactly the
premise `[LJ-1.256]` Q1 said the collapse needs (`lj-1.256-report.md:79-80`).
It exists because the probe's delivered `envSetK` is B₀-fixed; the fully
generic form is the TFacts `envSetK` field (section 4).

## 3. UNBUILT FIELDS, TERM NEEDED (C-36)

**None of the five is unbuilt.** All five build WITH the numeral premise.

The honest negative is elsewhere: **the four `envInK-*` do NOT build AS THE
MASTER STATES THEM** (premise `⟨ fst ar ∈ K ⟩` and no numeral). MEASURED:
`[LJ-1.255]` wrote the failing last step (`ProbeLJ1255.agda:354-355`, the
`? -- envSetGen B₀ ar ∈ Lset lam [needs numeral]`), and the general-arity
closure that would close it is REFUTED at `src/L/Condensation/TwelveAgree.lagda.md:292-297`
with the witness at `agents/tasks/LJ-1-172/lj-1.172-report.md:758-772`. The
cure is the numeral premise, which is what my probe adds.

## 4. THE `TFacts` NUMERAL PREMISE AND ITS CONSUMERS (C-40)

**The numeral premise must be added.** MEASURED for the field content: the
four build only with it, and fail without it. The change is
`∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` added to the four `envInK-*` telescopes.

The four fields live in THREE records, so all three change:

- `TFacts` (TwelveAgree.lagda.md:216-244): all four.
- `LFacts` (LowerAgree.lagda.md:158-170): `envInK-mem`, `envInK-neg`, `envInK-imp`.
- `UFacts` (UpperAgree.lagda.md:158-170): `envInK-neg`, `envInK-top`, `envInK-imp`.

**Consumers of the `TFacts` record:**

1. `AbstractFrame` (TwelveAgree.lagda.md:337-338), the only `tf : TFacts`
   consumer; it projects the fields into `lf`/`uf` (pass-through, no text
   change, re-typecheck only).

**Consumers of the changed fields, through `LFacts`/`UFacts`:**

2. `LowerAgree` (LowerAgree.lagda.md:226), forwards `envInK-mem/-neg/-imp` to
   row modules.
3. `UpperAgree` (UpperAgree.lagda.md:213), forwards `envInK-neg/-top/-imp`.

**Row modules that take `envInK` as a parameter and must gain the premise**
(all in src/L/Condensation.lagda.md): `MemAgree` (:4420), `EqAgree` (:5358),
`ImpAgree` (:5270), `NegAgree` (:3763), `TopAgree` (:3684), `ExistAgree`
(:3980), `ForallAgree` (:3872), `AllInAgree` (:5029), `ExInAgree` (:5153),
`ClauseAgree` (:4158). Every one of these already takes `codesK`, whose
fourth component IS `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, so the numeral is
dischargeable at every call site with no new hypothesis — the master's own
note at TwelveAgree.lagda.md:298-301.

**Price: INFERRED, about 40-60 lines of mechanical edits, no new proof.**
Basis: +10 field-type lines (4+3+3), +10 parameter lines (one per row
module), and ~20 `envInK` call sites each gaining the numeral argument (in
the `back` direction `arNum` is already in scope from `codesK`; in the `out`
direction each site derives it in one `codesK` decode line). The proof itself
is already MEASURED: `envInK-gen` is 12 lines. I did not run the master
change, so the line price is INFERRED; the field content is MEASURED.

The change is contained: `AbstractFrame`'s exports `twelve-out`/`twelve-back`
do not mention `envInK-*`, so nothing past `SatGraphAgree`
(Condensation.lagda.md:6802) or `LeafAgree` (:7065) sees the new premise.

## 5. SECONDS, LOAD, RUN COUNT

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No run past 20
minutes. No heap exhaustion. No kill. The first successful check is the
discarded warm-up (untimed cold check that wrote the interface cache).

| run | exit | user s | real s | load |
|---|---:|---:|---:|---|
| warm-up (discarded) | 0 | — | — | — |
| kept 1 | 0 | 1.72 | 2.62 | 4.97 / 5.32 / 4.97 |
| kept 2 | 0 | 1.75 | 1.90 | 4.97 / 5.32 / 4.97 |
| kept 3 | 0 | 1.75 | 1.90 | 4.98 / 5.31 / 4.97 |

Mean user time of the three kept runs: **about 1.74 s**. The four `envInK-*`,
`someEnv`, the `envK-gen` collapse and the `L.Condensation` import together
add about 0.6 s over `[LJ-1.255]`'s 1.11 s; nothing walls.

## 6. DD4

**The collapse follows the tower-neutral pattern, but the probe's shells are
the concrete-site special case, not the general form.** The shape — one
slot-generic shell plus thin per-layout applications — is exactly the shape
of the delivered `EnvSet` module (whose own comment at
`src/L/Condensation.lagda.md:2917-2925` says one copy serves every layout and
both towers) and of the probe's `envSetAt-ident`. So the MOVE is tower-neutral
and MEASURED green.

**The two shells themselves are NOT yet tower-neutral.** `envK-gen` and
`envInK-gen` carry `qb : lookup bi γ ≡ B₀`, pinning the carrier to the
concrete `B₀`, and they sit on the B₀-fixed `envSetK`. The fully
tower-neutral form needs the general `envSetK : (B ar) (n) → fst ar ≡ # n →
fst B ∈ K → fst ar ∈ K → envSetGen B ar ∈ K` field
(TwelveAgree.lagda.md:302-307, L9, still unbuilt), which replaces `qb` with
the `B ∈ K` premise and makes the shells generic over the carrier slot. That
is the same residue ProbeLJ1255's DD4 note named (`ProbeLJ1255.agda:249-254`).

**The per-tower figure does not rise from anything here.** `someEnv`'s
environment construction is the only per-tower line in the five, and it is
one `Generic.Holds` + one `EnvSet.back` application at whatever slot layout
the tower uses — about 30 lines once, not per tower. `t0eq`/`t1eq` stay
MEASURED zero (`src/L/Condensation.lagda.md:3063-3067`).

## 7. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| all five build | **MEASURED TRUE**, exit 0, WITH the numeral premise |
| the four `envInK-*` build as the master states them | **MEASURED FALSE.** the numeral is missing and the general form is REFUTED |
| the five `envK-*` collapse | **MEASURED TRUE.** 67 vs 85 total, 30 vs 55 body |
| `someEnv` needs a 120-line adequacy | **MEASURED FALSE.** `EnvSet.back` is four delivered lines |
| `someEnv` builds | **MEASURED TRUE.** exit 0 |
| the `TFacts` numeral premise must be added | **MEASURED** (field content); the master-change line price is **INFERRED** |
| a wall occurred | **MEASURED FALSE.** max ~1.74 s user |
| I edited a master | **MEASURED FALSE.** only `agents/tasks/LJ-1-257/` written |
| I touched `Name.lagda.md`, `LJ-1-258/`, or `Everything` | **MEASURED FALSE.** none |

**C-44:** every claim this brief states that I needed I found, at the
`file:line`s above. Nothing is left unproven from my side except the
master-change line price, which I mark INFERRED.

## 8. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-256/lj-1.256-report.md`, read WHOLE. **Line read `:79`**,
  the predicted collapse premise `lookup bi γ ≡ B₀`.
- `agents/tasks/LJ-1-255/lj-1.255-report.md`, read WHOLE. **Line read `:52`**,
  the four `envInK-*` BLOCKED on the missing numeral.
- `agents/tasks/LJ-1-255/ProbeLJ1255.agda`, read WHOLE. **Line read `:354`**,
  the failing last step `? -- envSetGen B₀ ar ∈ Lset lam [needs numeral]`.
- `agents/tasks/LJ-1-254/lj-1.254-report.md`, read WHOLE. **Line read `:50`**,
  `union∈Lset-suc` adapted from `mkUnion`.
- `agents/tasks/LJ-1-173/lj-1.173-report.md`, read the `:843-846` region.
  **Line read `:846`**, the cure-table row that gave `envInK-*` `ar ∈ K` and
  not the numeral.
- `src/L/Coding/CodeSet.lagda.md`, read `:185-204`. **Line read `:198`**,
  `arityNumAtL-out`, the delivered numeral reader.
- `src/L/Condensation.lagda.md`, read `:2917-3070` and the `envInK` sites.
  **Line read `:3042`**, `EnvSet.back`, the four-line transfer.
- `src/L/Condensation/TwelveAgree.lagda.md`, read `:129-480`. **Line read
  `:298`**, the master's note that the restriction costs consumers nothing.
- `archive/dev/TASKS-archived.md`, read the header. **Line read `:10`**, the
  shape note; nothing in the retired route bears on the numeral question.

## 9. LITERATURE USED (DD18)

**Devlin does NOT need these five facts; they are an artifact of the coding.**
`dev/literature/devlin-II5.md:246-255` says Devlin requires only that SOME
bounded description with a bound inside the carrier exists — the finite
sequences over the formula set — and not any particular shape for it. The
four `envInK-*` and `someEnv` are this machine's way of meeting that
requirement, and the numeral restriction is Devlin's finite-arities form.
