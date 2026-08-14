# LJ-1.244 report: the third route, route 2 cut in half

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda process,
cap `GHCRTS="-A64m -I0 -M8g"`, never raised. No master, brief or report
edited. No commit, no push. No `make check`. Written incrementally (C-22).
Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**`q'` does not build. `amb` is NOT supplied outright.**

Two probes, both MEASURED. Probe A replaces `q` with `q'` as a HYPOTHESIS;
it typechecks, exit 0, and `amb` comes out. **But `q'` is then a hypothesis,
not a term.** Probe B tries to DEFINE `q'`; the goal is stuck, exit 42.

**The abort branch that fired:** "`q'` IS AS HARD AS `q`." The third route
collapses into route 2. The phase faces a chapter.

**The one use site IS one.** `q` is spent at `ProbeLJ1184B.agda:122` and
nowhere else. The halving applies. MEASURED, section 3.

## 1. DOES `q'` BUILD

**NO. MEASURED, two ways.**

### 1.1 As a hypothesis, it typechecks and `amb` comes out

`agents/tasks/LJ-1-244/ProbeLJ1244A.agda` is `ProbeLJ1184B.agda` with `q`
replaced by `q'`:

```agda
(q' : (γ : Vec A.R.SC 2)
    → ⟨ A.ambient γ (embed φ₀) ⟩
    → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩)
```

`go` becomes `go γ h = M.graph-only zero (suc zero) γ (q' γ h)`. Nothing
else changes. **Exit 0, `amb` and `Discharge` come out.** This confirms
`[LJ-1.243]`'s reading of the direction: `sym q` at `:122` spends exactly
the `embed φ₀ → Graph` direction.

**But `amb` is NOT supplied outright.** `q'` is a module parameter. The
module typechecks fast for the same reason a module with a false hypothesis
typechecks fast. C-45's exact failure mode. Section 2 audits it.

### 1.2 As a definition, the goal is stuck

`agents/tasks/LJ-1-244/ProbeLJ1244B.agda` drops `q'` from the telescope and
tries to define it from the six readings and `φ₀`:

```agda
q' : (γ : Vec A.R.SC 2)
   → ⟨ A.ambient γ (embed φ₀) ⟩
   → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩
q' γ h = {!!}
```

**Exit 42, unsolved interaction meta at `ProbeLJ1244B.agda:75`.** The goal
is `⟨ A.ambient γ (Graph zero (suc zero)) ⟩`. The context has
`h : ⟨ A.ambient γ (embed φ₀) ⟩`, the six readings, and `φ₀`. Nothing
produces `⟨ Graph ⟩` from `⟨ embed φ₀ ⟩`.

### 1.3 The term that blocks it

To close the goal, one must produce a witness for the graph formula:

```agda
Graph zero (suc zero) = ∃̇ (ApproxAt zero (suc (suc zero))
                        ∧̇ Step (suc zero) (suc (suc zero)) zero)
```

`GenSequence.agda:167`. So one must construct `f : A.R.SC` with
`⟨ ambient (f ∷ γ) (ApproxAt zero (suc (suc zero))) ⟩` and
`⟨ ambient (f ∷ γ) (Step (suc zero) (suc (suc zero)) zero) ⟩`, from
`φ₀`'s fourteen witnesses (`ProbeLJ1241A.agda:145-146`).

**That construction is the coding-transfer bridge.** The delivered form is
at the CLASS carrier: `TagAgree` (`tagAtL` against `tagBS`,
`src/L/Condensation.lagda.md:6617-6654`), `SatGraphB` against `satGraphAt`
(`:6795-7045`), `isCodeBS` against `isCodeAt` (`:7170-7179`). None of it is
ported to the ambient carrier, and none of it is in the four green files.

**So `q'` is route 2's one direction, the B→At half. It is not a free
weakening.** `q` was refuted (false, twice). `q'` is true but unbuilt, and
building it is a chapter.

## 2. THE INSTANTIATION AUDIT (C-45)

C-45 says: audit the instantiation, never the telescope.

**MEASURED, by a repository-wide search.**

| module | application | what it gives for `q` / `q'` |
|---|---|---|
| `AmbientStep` (`ProbeLJ1184B.agda:101`) | `ProbeLJ1184C.agda:83` | `q` (relayed from `Step184`'s own parameter) |
| `Step184` (`ProbeLJ1184C.agda:76`) | nowhere | nothing |

`ProbeLJ1184C.agda:83` reads
`module AS' = P184B.AmbientStep AS AA AG so sb ad av ast gout φ₀ q`, and
`q` there is `Step184`'s parameter at `ProbeLJ1184C.agda:80`. `Step184`
itself is applied nowhere. **So nothing gives a real term for `q`, and
nothing gives one for `q'`.** The arc relays the hypothesis. It never
discharges it. MEASURED.

**Consequence for the third route.** Replacing `q` with `q'` in the
telescope does not change this. The relay becomes
`... gout φ₀ q'`, and `q'` is still `Step184`'s parameter. `amb` stays
conditional. A file that exits 0 with `q'` in the telescope proves nothing.
MEASURED, by Probe A plus the audit.

## 3. THE ONE USE SITE, AND WHAT ELSE `sym` WAS CARRYING

**The one use site IS one.** MEASURED. `q` appears in `ProbeLJ1184B.agda`
at `:112` (declaration) and `:122` (the single `sym q`). It appears in
`ProbeLJ1184C.agda` at `:80` (declaration) and `:83` (relay). **No other
site reads `q`.** `[LJ-1.243]`'s measurement holds.

**What else `sym` was carrying: nothing the module needs.** C-36. The `sym
q` at `:122` spends only `embed φ₀ → Graph`. The reverse direction
`Graph → embed φ₀` is never used. So `q'` is the exact weakening. The two
things `q` carried beyond `q'` are: (a) the reverse direction, unused,
MEASURED by the one-use-site count; (b) the SYNTACTIC form (a path of
formulas), which is what the two refutations of `[LJ-1.242]` and
`[LJ-1.243]` killed. `q'` keeps nothing of (b).

**So the "module needs more" branch does not fire.** The module does not
need more than `q'`. It needs `q'` itself, and `q'` is unbuilt.

## 4. SECONDS, LOAD, RUN COUNT

One process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. Warm-up
discarded.

| run | file | exit | seconds |
|---|---|---:|---|
| warm-up | `ProbeLJ1244A.agda` | 0 | 1.74 |
| kept 1 | `ProbeLJ1244A.agda` | 0 | 1.69 |
| kept 2 | `ProbeLJ1244A.agda` | 0 | 1.70 |
| kept 3 | `ProbeLJ1244A.agda` | 0 | 1.70 |
| attempt | `ProbeLJ1244B.agda` | 42 | — (unsolved hole) |

Mean kept **1.70 s**. Load at the close of the batch: **4.45 / 4.53 / 4.30**
(one-minute / five-minute / fifteen-minute). Two users.

No run passed 20 minutes. No heap exhaustion. **These seconds decide
nothing.** The decision rests on the audit (section 2) and the stuck goal
(section 1.2), which are structural, not timing.

## 5. DD4

**`q'` is smaller than `q` in one sense and not smaller in the sense that
matters.**

`q` was refuted. It is unbuildable. `q'` is true and, in principle,
buildable. So `q'` is smaller than `q` on that axis. MEASURED, from the two
refutations plus the true direction.

**`q'` is NOT smaller than route 2.** `q'` is route 2's B→At direction.
Route 2 asks for `⟨ γ ⊨ embed φ₀ ⟩ ≡ ⟨ γ ⊨ LsetGraphAt ⟩`, a path of hProps,
both directions. `q'` is one direction of it. The one direction it keeps is
the one `amb` spends. So the third route does not avoid route 2's work; it
IS route 2, cut in half, and the half it keeps is the hard half. MEASURED,
from section 1.3's blocking term.

**No part of `q'` is tower-neutral.** `q'` names `Graph` (=
`LsetGraphAt`), and `LsetGraphAt` runs to the satisfaction coding through
`DefAt` (`GenSequence.agda:69`). That is Def-tower syntax. The J tower's
analogue is syntax-free op-graphs (`dev/literature/devlin-II5.md:375`, row
C2), so it does not pay this bridge. MEASURED. This agrees with
`[LJ-1.243]` section 7.

**"A one-directional implication may share more than an equation does."
The answer is yes, and it does not help here.** `q'` is a satisfaction
implication, so its proof would run through the carrier-generic satisfaction
machinery (`Machine`, the six readings), which the two towers already share.
`q` was a syntactic equation, which is per-tower and shared by nobody. So
`q'` sits at the shared layer and `q` did not. **But the load-bearing part
of `q'`'s proof is the graph-witness construction, which is per-tower.** The
shared layer carries the shape; the per-tower layer carries the content.
INFERRED, from the two types.

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `q'` builds as a definition from the six readings and `φ₀` | **MEASURED FALSE.** Exit 42, stuck goal at `ProbeLJ1244B.agda:75` |
| `amb` is supplied outright by replacing `q` with `q'` | **MEASURED FALSE.** `q'` is a hypothesis, section 1.1 and 2 |
| the module needs more than `q'` | **MEASURED FALSE.** It needs `q'` itself; `sym` carried nothing else, section 3 |
| the one use site is not one | **MEASURED FALSE.** One use site, `ProbeLJ1184B.agda:122` |
| `q'` is tower-neutral | **MEASURED FALSE.** It names `Graph`, Def-tower syntax, section 5 |
| `q'` avoids route 2's work | **MEASURED FALSE.** It is route 2's B→At direction, section 5 |
| the six readings produce `⟨ Graph ⟩` | **MEASURED FALSE.** All six run FROM Step/Approx/Graph TO Lset facts; the "in" directions `Graph-in` (`GenSequence.agda:196`), `ApproxAt-in` (`:184`), `StepAt-in` (`:145`) are not in `AmbientStep`'s telescope |

## 7. ARCHIVE USED (DD18)

- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read
  `:166-170`, `:206-210`, `:795-810`. **Line read:** `:808`, "the
  class-carrier equivalence, stated in the crossing section below and left
  standing with the ambient obligations." The archive names the SAME owed
  equivalence and leaves it standing. The archive's `CrossOut φ` at `:208`
  is a hypothesis, instantiated nowhere. The archive shows the crossing was
  parameterized and never discharged; `q'` is the same obligation in the
  one-direction form. **It shows no direction I could reuse.**

## 8. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-115`, `:205-415`.

**Is 1.9.15's shape `q'`? NO. MEASURED.**

1.9.15 is "Σ₀ absoluteness: Σ₀ formulas of the ℒ-analogue are absolute for
transitive sets ... the bridge between satisfaction inside a transitive
carrier and ambient truth" (`dev/literature/devlin-II5.md:321-323`). That
is ONE formula read at TWO carriers.

`q'` is TWO formulas (`embed φ₀`, the BoundedSubset coding, and
`LsetGraphAt`, the Sequence coding) read at ONE carrier. The shapes are
orthogonal. 1.9.15 moves a formula between a carrier and the universe. `q'`
moves between two codings at one carrier.

Devlin never needs a two-coding bridge. He has one formula `Φ` and its
ℒ-analogue `φ` (`dev/literature/devlin-II5.md:95-100`), bridged by 1.9.15.
**So `q'` is Bedrock's own artifact, from the slot design that made the two
codings differ. INFERRED** from the two shapes plus the absence in Devlin.
This agrees with `[LJ-1.243]` section 3.4.

## 9. PROHIBITIONS, ANSWERED

No master, brief or report edited. `src/Everything.lagda.md` not opened.
`src/L/Choice/Name.lagda.md` not opened. `agents/tasks/LJ-1-245/` not
touched. No commit, no push, no `git checkout`/`stash`/`reset`/`clean`. No
`make check`. One Agda process at a time, cap never raised.

**My files:** `agents/tasks/LJ-1-244/lj-1.244-report.md`,
`agents/tasks/LJ-1-244/ProbeLJ1244A.agda`,
`agents/tasks/LJ-1-244/ProbeLJ1244B.agda`.

Both probes pass `scripts/lint-agda.py --check`. The report passes
`scripts/lint-prose.py --check`.
