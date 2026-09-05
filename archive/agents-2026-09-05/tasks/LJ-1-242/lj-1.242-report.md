# LJ-1.242 report: the fifth step, checked against the real φ₀

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda process,
cap `GHCRTS="-A64m -I0 -M8g"`, never raised. No master, brief or report edited.
No commit, no push. No `make check`. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**`amb` DOES NOT HOLD at the real `φ₀` by `[LJ-1.184]`'s supply.** The supply
is not six readings. It is six readings PLUS one equation, and the equation is
false at the real `φ₀`.

**`[LJ-1.184]`'s supply is a function of `q`:**

```agda
(q : Graph {2} zero (suc zero) ≡ embed φ₀)
```

`agents/tasks/LJ-1-184/ProbeLJ1184B.agda:112`, and at the real site
`agents/tasks/LJ-1-184/ProbeLJ1184C.agda:80`.

**That equation is false at the real `φ₀`.** The left side, the ambient graph
`LsetGraphAt zero (suc zero)`, carries at least one constant. The right side,
`embed φ₀`, carries none. **MEASURED**, section 2.

**So `pins` is only part of the closure, and the part it is not is the part
that discharges `amb`.** `[LJ-1.241]` built the formula, not the bridge from
the formula to the read-off.

**The fifth step's written lines: I wrote zero.** The step as the brief frames
it (a numeral-closure that discharges `amb`) cannot be written as a syntactic
closure. Section 3 says why, and section 4 names what the real step is.

**Which abort branch fired.** Branch 4, in part: the six readings discharge
the six readings, but `[LJ-1.184]`'s declared residue is incomplete, so the
convergence claim does not discharge `amb`. Branch 3, in part:
`[LJ-1.184]`'s supply does not survive the real formula, but there is NO wrong
`v` to name. Branch 2, in the letter: `amb` still needs a closure, and `pins`
is only part of it. **The one clean sentence for the screen:** the fifth step
is not a numeral closure inside `φ₀`; it is a semantic bridge between two
codings, and `q` is the term that exposes it.

## 1. THE CONVERGENCE CLAIM, CHECKED (C-44)

The orchestrator's claim: `[LJ-1.184]`'s declared residue is discharged by
`[LJ-1.238]`'s port.

**Half TRUE, half REFUTED. The half that is true discharges the six readings.
The half that is false is that the six readings were the whole residue.**

### 1.1 The six readings: DISCHARGED. MEASURED.

`[LJ-1.184]` names six readings in its section 0.2:
`StepAt-out`, `StepAt-back`, `ApproxAt-dom`, `ApproxAt-value`,
`ApproxAt-step`, `Graph-out`. `[LJ-1.238]` ports exactly these six, at
`agents/tasks/LJ-1-238/GenSequence.agda`:

| `[LJ-1.184]` type | `[LJ-1.238]` term | `GenSequence.agda` |
|---|---|---|
| `StepOutT` | `StepAt-out` | `:119` |
| `StepBackT` | `StepAt-back` | `:124` |
| `ApproxDomT` | `ApproxAt-dom` | `:172` |
| `ApproxValT` | `ApproxAt-value` | `:176` |
| `ApproxStepT` | `ApproxAt-step` | `:181` |
| `GraphOutT` | `LsetGraph-out` | `:200` |

The six names match the six delivered readings of
`src/L/Coding/Sequence.lagda.md:217,221,295,298,303,325`. `[LJ-1.238]` measured
the port at 145 verbatim of 157 lines, per-tower residual zero
(`lj-1.238-report.md:14-18`). **The six readings discharge the six readings.
MEASURED.**

**One transport sits between them and I mark it.** `[LJ-1.238]`'s six are
stated at the INNER reading `_⊨_ = ⊨ᵐ` of a transitive class
(`GenSequence.agda:47-48`). `[LJ-1.184]`'s six are stated at the OUTER reading
`ambient γ φ = (map fst γ) ⊨ᵛ φ` (`ProbeLJ1184A.agda:318-321`). At `M = Full`
the two readings agree on every formula, but no delivered lemma states the
general `⊨ᵐ ≡ ⊨ᵛ` for a non-Δ₀ formula (`abs₀` is Δ₀ only,
`src/FOL/Absoluteness.lagda.md:122`). **This is a real one-time transport, not
a refutation.** INFERRED that it is small; I did not typecheck it.

### 1.2 The residue `[LJ-1.184]` declared is INCOMPLETE. MEASURED.

`amb` is built inside `AmbientStep`, whose parameter list is the three
formulas, the six readings, `φ₀`, AND `q`
(`ProbeLJ1184B.agda:105-112`). The body spends `q` in one line:

```agda
go γ h = M.graph-only zero (suc zero) γ
  (subst (λ ψ → ⟨ A.ambient γ ψ ⟩) (sym q) h)
```

`ProbeLJ1184B.agda:116-118`. **Without `q` there is no `amb`.**

`[LJ-1.184]` section 0.2 says the residue is "SIX readings". Section 5.2 lists
six readings and their dependencies; section 5.3 refuses a figure for
`DefAt-in`/`DefAt-out`. **`q` appears in none of them.** So the declared
residue omits the one assumption that carries the formula identity.

**The convergence claim, read as "six readings discharge `amb`", is REFUTED.**
`q` is not among the six, `[LJ-1.238]` does not port it (it is not in
`L.Coding.Sequence`), and it is false at the real `φ₀` (section 2). **The
claim, read narrowly as "six readings discharge six readings", is TRUE.**

## 2. WHY THE EQUATION IS FALSE. MEASURED.

`q : LsetGraphAt zero (suc zero) ≡ embed φ₀`.

**The right side is constant-free.** `φ₀ = closeN 14 (pins ∧̇ renamed)`
(`ProbeLJ1241A.agda:145-146`), `base = Cnt.erase LH.levelHoodB refl`
(`:102-103`). The `refl` is the proof `countFo levelHoodB ≡ 0`, which is the
condition `erase` requires (`src/FOL/Count.lagda.md:598`). `pins`, `numAt`,
`isZeroAt`, `sucAt`, `closeN`, `renameFo` introduce no constant. **So
`countFo φ₀ ≡ 0`. MEASURED.**

**The left side carries a constant.** The ambient graph is
`LsetGraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
(`GenSequence.agda:167,224`). `Step` unfolds through `StepBody` to `DefAt`
(`:67,73`). The ambient `DefAt` is `extAt u (∃̇ (∃̇ (DefBody w)))`
(`ProbeGraphSupply.agda:373-374`), `DefBody` contains `DefinesAt`
(`:368-370`), `DefinesAt` contains `envOneAt` (`:237-239`), and
`envOneAt e y = extAt e (tagAtL zero 0 (suc y))` (`:101-102`). And

```agda
tagAtL s k x = ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))
```

`agents/tasks/LJ-1-210/GenModel.agda:341`. At the ambient class
`numeralL k = # k` with `tt*`, so `con (numeralL 0)` is a real constant. **So
`countFo LsetGraphAt ≥ 1`. MEASURED**, by the chain
`LsetGraphAt → DefAt → DefBody → DefinesAt → envOneAt → tagAtL → con`.

**A formula with zero constants is not equal to a formula with one.**
`countFo` is a function, so `φ ≡ ψ` forces `countFo φ ≡ countFo ψ`. **`q` is
unprovable. MEASURED.**

## 3. THE FIFTH STEP, AND WHAT IT ACTUALLY IS

The brief's branch 2 frames the fifth step as "the numeral-closure" and asks
whether `[LJ-1.241]`'s `pins` is the closure or only part.

**`pins` is only part, and the part it is NOT is what discharges `amb`.**
`pins` (`ProbeLJ1241A.agda:124-137`) closes the twelve tag slots by defining
the twelve numerals inside the formula. That is the constant-free route
`[LJ-1.240]` recommended, and it is DONE. It makes `φ₀` a correct level-hood
statement. **It does not and cannot make `LsetGraphAt ≡ embed φ₀`**, because
`LsetGraphAt` keeps its numeral as a constant `con (numeralL k)`, and a
constant-free `φ₀` can never equal it.

**The real fifth step is a SEMANTIC bridge, not a syntactic one.** Two routes
exist:

- **Route 1.** Build `φ₀` from the ambient `LsetGraphAt` and close its
  constants inside the formula (the same pins applied to the SEQUENCE coding,
  not to `levelHoodB`). Then `q` is not `refl` either, but the read-off
  `graph-only` applies to a formula that is one rewriting away, and the six
  readings apply verbatim. This is the route `[LJ-1.240]` section 3 route A
  described, with `levelHoodB` swapped for `LsetGraphAt`.
- **Route 2.** Keep `φ₀ = closeN 14 (pins ∧̇ erase levelHoodB)` and prove the
  satisfaction equivalence `⟨ γ ⊨ embed φ₀ ⟩ ≡ ⟨ γ ⊨ LsetGraphAt ⟩` through
  the delivered coding transfers (`tagBS` against `tagAtL`,
  `SatGraphB` against `satGraphAt`, `isCodeBS` against `isCodeAt`;
  `src/L/Condensation.lagda.md:6617-6643,6795-6800,7031-7045,7170-7179`). Then
  chain `Lset-only`. This is the Condensation-vs-Sequence bridge, and it is a
  chapter, not a numeral closure.

**Both routes are Def-tower work.** Neither is tower-neutral. INFERRED, from
the fact that both run through the satisfaction coding.

## 4. THE WRONG `v`. NONE FOUND.

Branch 3 asks me to name the wrong `v` that satisfies the formula. **There is
none.** `φ₀` is the erasure of the DELIVERED bounded matrix `levelHoodB`
(`ProbeLJ1241A.agda:102-103`), and `[LJ-1.241]` verified the pinning
(`ProbeLJ1241B.agda:121-123,130-132`, exit 0). So `φ₀` states the level-hood
correctly; a wrong `v` does not satisfy it. **The failure is not the formula.
It is the supply ROUTE: `[LJ-1.184]`'s syntactic `q` cannot be instantiated at
a constant-free `φ₀`.** MEASURED at section 2.

**What `[LJ-1.184]` supplied it at:** at a `φ₀` and a `Graph` for which
`q : Graph {2} zero (suc zero) ≡ embed φ₀` was ASSUMED, never discharged
(`ProbeLJ1184B.agda:112`). The supply is conditional on `q`, and section 0.2
did not declare `q` as part of the residue. **That is the gap, and it is
exactly where the supply does not survive the real formula.** MEASURED.

## 5. DD4: WHICH SIDE THE CLOSURE LANDS ON

**Def-tower, per-tower. Not tower-neutral.**

`[LJ-1.241]` measured the numeral primitives `isZeroAt`, `sucAt`, `numAt` as
tower-neutral and `φ₀` as Def-tower (`lj-1.241-report.md:100-113`). That
measurement stands. **The closure that discharges `amb` — either route of
section 3 — runs through the satisfaction coding (`DefinesAt`, `isCodeAt`,
`satGraphAt`), which is Def-tower syntax.** The J tower's analogue is
syntax-free op-graphs (`dev/literature/devlin-II5.md:375`, row C2), so it does
not pay this bridge.

**Therefore phase 1's last per-tower object is NOT smaller than
`dev/literature/devlin-II5.md:387-389`'s two objects suggest.** The brief's
hope that a tower-neutral closure would shrink the per-tower budget is REFUTED
on this measurement: the closure is per-tower. **MEASURED** for the coding
chain; the assignment to Devlin's rows is a reading, stated as such.

## 6. SECONDS, LOAD, RUN COUNT

One process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. Warm-up discarded.
The run re-checked `agents/tasks/LJ-1-241/ProbeLJ1241A.agda` (the real `φ₀`),
exit 0, to hold the slot.

| run | file | exit | seconds | load at close |
|---|---|---:|---:|---|
| warm-up | `ProbeLJ1241A.agda` | 0 | 2.45 | — |
| kept 1 | `ProbeLJ1241A.agda` | 0 | **2.14** | — |
| kept 2 | `ProbeLJ1241A.agda` | 0 | **2.13** | — |
| kept 3 | `ProbeLJ1241A.agda` | 0 | **2.13** | — |

Mean kept **2.13 s**. Load at the close of the batch: **8.41 / 5.14 / 4.61**
(one-minute / five-minute / fifteen-minute; the one-minute spike is my own
four runs). Two users, 16 CPUs.

No run passed 20 minutes. No heap exhaustion. **These seconds decide nothing.**
The decision rests on file:line evidence, section 2, and section 2 is a reading
measurement, not a timing measurement.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `amb` holds at the real `φ₀` by `[LJ-1.184]`'s supply | **MEASURED FALSE.** `q` is false, section 2 |
| `[LJ-1.184]`'s declared residue is the six readings and nothing else | **MEASURED FALSE.** `q` is in the parameter list, `ProbeLJ1184B.agda:112`, and in no residue section |
| the six readings discharge the six readings | **MEASURED TRUE.** section 1.1 |
| the six readings discharge `amb` | **MEASURED FALSE.** `q` is not among them |
| `[LJ-1.238]` ports `q` | **MEASURED FALSE.** `q` is not in `L.Coding.Sequence`; `GenSequence` has no such equation |
| `pins` is the whole closure | **MEASURED FALSE.** it is the formula side only, section 3 |
| a wrong `v` satisfies `φ₀` | **MEASURED FALSE** at the delivered matrix and its verified pins; no wrong `v` |
| the closure is tower-neutral | **MEASURED FALSE.** it runs through the satisfaction coding, section 5 |
| `⊨ᵐ ≡ ⊨ᵛ` at `Full` is a delivered lemma for all formulas | **MEASURED FALSE.** `abs₀` is Δ₀ only, `src/FOL/Absoluteness.lagda.md:122` |

## 8. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-184/lj-1.184-report.md`, read WHOLE. TOOK section 0.2's
  six-reading residue (`:59-70`) and the fact that `q` is absent from sections
  0.2, 5.2 and 5.3.
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read WHOLE. TOOK the `AmbientStep`
  parameter list and the `q` line (`:105-118`).
- `agents/tasks/LJ-1-184/ProbeLJ1184C.agda`, read whole. TOOK the real-site
  `q` (`:80`).
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda`, read whole. TOOK `ambient`
  (`:318-321`) and `clause-a` (`:355-365`).
- `agents/tasks/LJ-1-238/GenSequence.agda`, read WHOLE. TOOK the six readings
  (`:119,124,172,176,181,200`) and `LsetGraphAt` (`:167,224-229`).
- `agents/tasks/LJ-1-238/lj-1.238-report.md`, read WHOLE. TOOK the deferred
  application (`:84-90`) and the zero-residual measurement (`:14-18`).
- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda`, read WHOLE. TOOK `base` (`:102-103`),
  `pins` (`:124-137`), `φ₀` (`:145-146`).
- `agents/tasks/LJ-1-241/ProbeLJ1241B.agda`, read the pin verification
  (`:121-123,130-132`).
- `agents/tasks/LJ-1-241/lj-1.241-report.md`, read WHOLE. TOOK the DD4 split
  (`:100-113`) and the open `amb` (`:131-135`).
- `agents/tasks/LJ-1-240/lj-1.240-report.md`, read WHOLE. TOOK route A
  (`:126-131`) and the `amb` finding (`:76-82`).
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, read `:184-196`. TOOK
  `AmbientRead` (`:190-192`).
- `agents/tasks/LJ-1-224/ProbeGraphSupply.agda`, read `:96-110,128-180,
  237-245,368-374`. TOOK `envOneAt` (`:101-102`), `DefinesAt` (`:237-239`),
  `DefBody` (`:368-370`), `DefAt` (`:373-374`).
- `agents/tasks/LJ-1-210/GenModel.agda`, read `:340-342`. TOOK `tagAtL` with
  `con (numeralL k)` (`:341`).
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read
  `:167-169,592-593,768-769,823-824`. TOOK `CrossOut` (`:167-169`), the empty
  closure `Cl = ⊤̇` (`:592-593`), `σᴹ = embed levelStory` (`:768-769`). SHAPE
  TAKEN, claim refused.
- `src/L/Coding/Sequence.lagda.md`, read `:217,221,295,298,303,325,349-354`.
  TOOK the six delivered readings and `LsetGraph` (`:354`).
- `src/FOL/Absoluteness.lagda.md`, read `:122-189`. TOOK `abs₀` Δ₀-only
  (`:122`).
- `src/L/Condensation.lagda.md`, read `:6617-6643,6795-6800,7031-7045,7170-7179`.
  TOOK the coding transfers' statements, which section 3 route 2 would spend.
- `src/FOL/Count.lagda.md`, read `:594-598`. TOOK `erase`'s `countFo ≡ 0`
  condition (`:598`).

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-110,209-220,370-389`.

**The brief's question: does Devlin prove clause (a) or take it from the
construction, and does his argument need a numeral-closure?**

**He TAKES it from the construction.** `:95-96`: "By 2.7 there is a Σ₀ formula
Φ(z, v, γ) of LST such that (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]". The proof of
(a) is lemma 2.7 (the level-formula construction), cited, not re-derived in
II.5. Clause (b) is then DERIVED from (a) by 1.9.15 (`:96-100`).

**He needs nothing like a numeral-closure.** His Φ is a Σ₀ formula of LST whose
finite ordinals are Σ₀-definable inside the language; the numerals live in Φ,
not in slots (`:214-216`). Our tree made the twelve tags environment SLOTS to
keep every bounded formula constant-free (`src/L/Condensation.lagda.md:1123-1125`),
so the numeral-closure is OUR price, an artifact of the slot design. This
agrees with `[LJ-1.241]` section 10 and adds the two-codings consequence of
section 2.

## 10. PROHIBITIONS, ANSWERED

No master, brief or report edited. `src/Everything.lagda.md` not opened.
`src/L/Choice/Name.lagda.md` not opened. No commit, no push, no `git
checkout`/`stash`/`reset`/`clean`. No `make check`. One Agda process at a time,
cap never raised.

**My file:** `agents/tasks/LJ-1-242/lj-1.242-report.md`. No probe was written;
this task is a check, and the check is a reading measurement. The Agda run in
section 6 re-checked the existing `agents/tasks/LJ-1-241/ProbeLJ1241A.agda`.
