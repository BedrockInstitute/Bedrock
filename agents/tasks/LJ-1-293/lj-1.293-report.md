# LJ-1.293 report: discharge `q`, the phase's last OPEN parameter

tier: pi (pi-subagent-mode), model `glm-5.3`. One Agda process at a time,
cap `GHCRTS="-A64m -I0 -M8g"`, never raised. No master, brief or report
edited. No commit, no push. No `make check`. Written incrementally (C-22).
Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**FALSE.**

`q`, at its intended instantiation, is refuted BY MACHINE. The term is
`q-false` at `agents/tasks/LJ-1-293/ProbeLJ1293A.agda:132-133`, exit 0,
mean kept 2.51 s over three runs. It derives `Empty` from

```agda
IntendedQ = Seq.LsetGraphAt {2} zero (suc zero) ≡ embed P1241.φ₀
```

(`ProbeLJ1293A.agda:121-122`), which IS `q` at the reading the probe's own
residue statement names (`Graph := LsetGraphAt`, the ambient port of
`L.Coding.Sequence`, `ProbeLJ1184B.agda:48-51`). The carrier check is
`ambient≡ = refl` at `ProbeLJ1293A.agda:82-83`: the port's carrier is
probe A's ambient carrier, by `refl`.

This upgrades the record. `[LJ-1.242]` measured the equation false by
READING two constructor chains, and `[LJ-1.243]` upheld the reading but
re-ran nothing (`lj-1.243-report.md`, section 13). The reading is now a
machine-checked term, run against today's tree.

The countermodel, stated once. The two sides differ at DEPTH TWO:

- LHS `LsetGraphAt {2} zero (suc zero)` is ONE `∃̇` over a `∧̇`
  (`GenSequence.agda:167`, `GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇
  Step (suc w) (suc b) zero)`). MEASURED by `left-tag = refl`
  (`ProbeLJ1293A.agda:125-126`): the depth-two tag is `isAnd`.
- RHS `embed φ₀` is FOURTEEN nested `∃̇` over one `∧̇` (`φ₀ = closeN 14
  (pins ∧̇ renamed)`, `ProbeLJ1241A.agda:145-146`, `closeN` at `:140-142`).
  MEASURED by `right-tag = refl` (`ProbeLJ1293A.agda:128-129`): the
  depth-two tag is `isEx`.

`∧̇` and `∃̇` are two constructors of one data type
(`src/FOL/Syntax.lagda.md:96,99`), so no path connects the two sides. The
term `q-false` transports `tt* : Unit*` along `q` into `Lift Empty.⊥`.

**The refutation is stronger than the site it was asked about.** The
Def-step coding enters `RefuteQ` as THREE HYPOTHESES
(`ProbeLJ1293A.agda:106-118`), and the depth-two shape of `LsetGraphAt`
does not depend on it. So `q` is false at the intended instantiation for
EVERY Def-step coding, `[LJ-1.224]`'s ambient one included. MEASURED, by
the hypothesis-shaped telescope of the green term.

**The abort branch that fired: `q` IS FALSE. Report the countermodel.
STOP.** D-10 was run in the right order: the truth was priced (by machine)
before any proof was attempted, and the proof is now known not to exist.

## 1. WHAT `q`'s FALSITY DOES AND DOES NOT MEAN

- **`q` as WRITTEN is not refutable.** `Graph` is a module parameter at
  `ProbeLJ1184B.agda:104`, so the equation is an ASSUMPTION, and it is
  satisfiable at degenerate instantiations. `[LJ-1.243]` section 1.3
  already bounded the negative this way, and I confirm it: my term
  refutes the equation AT the intended `Graph`, not the universally
  quantified telescope. MEASURED, from the parameter's position.
- **`q` is false at the only `Graph` the readings exist for.** The six
  readings are delivered for the SEQUENCE coding (`[LJ-1.238]` ported
  them, `GenSequence.agda:119,124,172,176,181,200`), and my refutation
  covers that coding at every DefAt. So the equation sits exactly between
  the two objects the phase needs to identify: the coded graph that HAS
  the readings, and the embedded level-hood formula the site is stated
  at. MEASURED, section 0.
- **The falsity is not about `φ₀` being wrong.** `[LJ-1.242]` section 4
  already separated this: `φ₀` states level-hood correctly (twelve pins
  verified, `ProbeLJ1241B.agda:121-123,130-132`); the failure is the
  syntactic SUPPLY ROUTE. I did not re-measure the pins; I take the
  record's word, marked as taken.
- **For an ARBITRARY `φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2`, the depth-two term
  does not automatically apply.** A differently-shaped `φ₀` could share
  the depth-two tag. The `φ₀`-independent refutation is the constant
  count: `embed φ₀` is constant-free (`embed = mapFo Empty.rec*`,
  `src/FOL/Manipulation/Relabelling.lagda.md:117-118`; no `con` node is
  constructible over `⊥*`), while `LsetGraphAt zero (suc zero)` carries at
  least one constant (the chain `LsetGraphAt → DefAt → DefBody →
  DefinesAt → envOneAt → tagAtL → con`, every link opened by
  `[LJ-1.243]` section 1.2). That argument is INFERRED from the type plus
  the verified chain; its induction term (`countFo (mapFo f φ) ≡
  countFo φ`) is not delivered, MEASURED by reading
  `src/FOL/Manipulation/Parameters.lagda.md:74-86`, which has no such
  lemma. For the phase's `φ₀`, the machine term above needs none of this.

## 2. THE PREMISES, EACH CHECKED (C-44)

| premise | verdict |
|---|---|
| `q` is `Graph {2} zero (suc zero) ≡ embed φ₀` at `ProbeLJ1184B.agda:112` | **VERIFIED**, by grep and by reading `:101-130` whole |
| `go` spends `q` at `:122` | **VERIFIED**, `subst ... (sym q) h` at `:121-122` |
| the only application is `ProbeLJ1184C.agda:83`, feeding `q` from its own telescope | **VERIFIED** by repository-wide grep; `q` declared at `ProbeLJ1184C.agda:80`, relayed at `:83`; `Step184` applied nowhere |
| nothing instantiates `AmbientStep` | **VERIFIED**, same grep. One nuance the premise omits: `agents/tasks/LJ-1-244/ProbeLJ1244A.agda:92` declares a module NAMED `AmbientStep`, but it is a COPY with `q` replaced by `q'`, not an instantiation |
| `amb`'s type is Devlin's clause (a) at the ambient carrier, `ProbeLJ1178A.agda:190-192` | **VERIFIED**, by reading those lines |
| `sl`, `sc`, `s₁` BUILT and `el`, `fwd`, `bwd` SUPPLIED, `lj-1.267-report.md:13-19` | **VERIFIED**, the table reads exactly that, so `amb` is the last one |

## 3. WHAT `amb`'s STATUS BECOMES, AND THE RESIDUE

**`amb` stays OPEN. `[LJ-1.7]`'s residue is NOT empty.**

`amb` is supplied inside `AmbientStep` only conditionally on `q`
(`ProbeLJ1184B.agda:128-129` under the `:112` telescope), and `q` is now
MEASURED FALSE by machine at the intended instantiation. A conditional
supply whose condition is refuted is not a supply (C-38 as extended).

**The named obligation, at file:line.** The discharge needs the
one-direction satisfaction implication that `go` actually spends
(`[LJ-1.243]` section 3.1):

```agda
q' : (γ : Vec A.R.SC 2) → ⟨ A.ambient γ (embed φ₀) ⟩
   → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩
```

`[LJ-1.244]` measured the landscape: `q'` as a HYPOTHESIS typechecks and
`amb` comes out (`ProbeLJ1244A.agda`, exit 0), but as a DEFINITION the
goal is stuck (`ProbeLJ1244B.agda:75`, exit 42), and the blocking term is
the graph-witness construction, the coding-transfer bridge at the ambient
carrier. Its class-carrier analogues are delivered at
`src/L/Condensation.lagda.md:6617-6654` (`TagAgree`), `:6795-7045`
(`SatGraphB` against `satGraphAt`), `:7170-7179` (`isCodeBS` against
`isCodeAt`), none ported to the ambient carrier. `[LJ-1.244]` priced that
build as a chapter. I cite the price and do not re-price it; the abort
criterion fired first.

**A second obligation the record already carries:** even at `q'`, the six
readings are delivered at the INNER reading `⊨ᵐ` while `q'` is stated at
the ambient reading, and the transport between them is a one-time
`⊨ᵐ ≡ ⊨ᵛ` step no delivered lemma states for non-Δ₀ formulas
(`[LJ-1.242]` section 1.1). INFERRED small; not measured by anyone.

## 4. DD4, WITH THE AXIS NAMED (C-46)

**Axis of THIS answer: the port's L-against-ambient axis, on which `amb`
is the SUBJECT, not a label.** Not DD4's own AC-against-GCH axis (fixed
in code at `scripts/ledger.py:50`), and not Devlin's Def-against-J axis,
which I use below only for the replacement obligation.

**Would a proof of `q` be reusable at the other carrier, or written
twice?** There is no proof to reuse: `q` is false. What exists instead:

- **The refutation is written ONCE and covers every carrier.** `tag₂` is
  generic in `K` (`ProbeLJ1293A.agda:97-99`), the depth-two shapes of
  both sides are carrier-independent, and the term never opens a carrier
  fact. The same term refutes the equation at the class carrier and at
  the ambient carrier. So on the L-against-ambient axis the shared object
  is the NEGATIVE, one term for both ends. MEASURED, from the term's
  type.
- **The true discharge object, `q'`, is a satisfaction implication.** Its
  SHAPE runs through the carrier-generic `Machine` (the six readings),
  which both carriers already share. Its LOAD-BEARING content, the
  graph-witness construction, is per-tower on the Def-against-J axis:
  the Def tower must bridge two codings, the J tower's analogue is
  syntax-free op-graphs (`dev/literature/devlin-II5.md:375`, row C2).
  So a syntactic identity would be written twice, once per tower; the
  satisfaction bridge is written once in shape and once per tower in
  content. This confirms `[LJ-1.244]` section 5 rather than extending it.

## 5. SECONDS, LOAD, RUN COUNT

One process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
Warm-up discarded.

| run | exit | seconds |
|---|---:|---:|
| warm-up | 0 | 3.42 |
| kept 1 | 0 | 2.59 |
| kept 2 | 0 | 2.51 |
| kept 3 | 0 | 2.44 |

Mean kept **2.51 s**. First full check (checking `ProbeLJ1241A` too):
3.95 s. Load at the close of the batch: **5.13 / 5.58 / 5.55**
(one-minute / five-minute / fifteen-minute), 3 users; two sibling tasks
are live (`LJ-1-291`, `LJ-1-292`). No heap exhaustion. No run passed
30 minutes. These seconds decide nothing; the term decides.

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `q` is provable at the intended instantiation | **MEASURED FALSE**, `q-false`, `ProbeLJ1293A.agda:132-133`, exit 0 |
| `q` is true at the intended instantiation | **MEASURED FALSE**, `left-tag` and `right-tag`, `:125-129` |
| `q`'s falsity depends on the Def-step coding | **MEASURED FALSE.** DefAt enters as hypotheses; the term holds for every DefAt |
| the port's carrier differs from probe A's ambient carrier | **MEASURED FALSE.** `ambient≡ = refl`, `:82-83` |
| something instantiates `AmbientStep` | **MEASURED FALSE.** Only the relay at `ProbeLJ1184C.agda:83` |
| `LJ-1-244`'s `AmbientStep` instantiates the original | **MEASURED FALSE.** It is a copy with `q` replaced, `ProbeLJ1244A.agda:92` |
| `amb` becomes SUPPLIED by this task | **MEASURED FALSE.** The supply's condition is refuted |
| `[LJ-1.7]`'s residue is empty | **MEASURED FALSE.** `amb` OPEN, section 3 |
| `q` is refutable as written, `Graph` abstract | **MEASURED FALSE.** The parameter makes it an assumption; satisfiable at degenerate `Graph` |
| the depth-two term refutes `q` for every `φ₀` of the site's type | **MEASURED FALSE.** It needs `φ₀`'s shape; the `φ₀`-independent argument is the constant count, INFERRED here, section 1 |
| a `countFo`-under-`mapFo` lemma is delivered | **MEASURED FALSE.** `Parameters.lagda.md:74-86` has none |
| Devlin proves clause (a) inside II.5 | **MEASURED FALSE.** He takes it from II.2.7, section 8 |
| Devlin's proof bridges two codings syntactically | **MEASURED FALSE.** One formula, 1.9.15 between carriers, section 8 |

## 7. WHAT I DID NOT SETTLE

- **The graph-witness construction (`q'`'s body).** `[LJ-1.244]` measured
  it stuck and priced it as a chapter. I did not re-attempt it; the abort
  criterion fired on the truth, not the proof.
- **The 1,688-constant census today.** My term does not need it. Whether
  the census still holds is still un-re-run, as `[LJ-1.243]` section 13
  left it.
- **A wrong `v` for `φ₀`.** Still undecidable on the record, as
  `[LJ-1.243]` section 5 left it.
- **The sweep for other sub-shape-B sites.** `[LJ-1.243]` section 6.1
  counted seven. My refutation measures the intended instantiation and
  covers, by its hypothesis-shaped telescope, every DefAt at that site;
  it does not re-sweep the tree (C-42).

## 8. ARCHIVE USED (DD18)

One line read per archived file, as the brief requires.

- `agents/tasks/LJ-1-267/lj-1.267-report.md`, read WHOLE, section 1.6
  read WHOLE. **Line read:** section 1.6, "`amb` is OPEN ... the supply
  relays `q` and never discharges it". TOOK the seven-parameter table and
  the residue statement; every status in my premise check comes from it.
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read WHOLE, `:101-130` read
  WHOLE FIRST. **Line read:** `:112`, `(q : Graph {2} zero (suc zero) ≡
  embed φ₀)`. TOOK the telescope, `go` at `:121-122`, and the residue
  statement at `:48-51` that names the intended instantiation.
- `agents/tasks/LJ-1-184/ProbeLJ1184C.agda`, read WHOLE. **Line read:**
  `:83`, `module AS' = P184B.AmbientStep AS AA AG so sb ad av ast gout φ₀ q`.
  TOOK the relay shape; copied `[LJ-1.243]`'s method for my own grep.
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda`, read WHOLE. **Line read:**
  `:352-354`, "for a `Graph` whose two-slot instance is the embedded
  level-hood formula". TOOK `Full`, `Full-tr`, `ambient`, `clause-a`, and
  the carrier `R.SC` my probe checks against.
- `agents/tasks/LJ-1-243/lj-1.243-report.md`, read WHOLE, section 2.2
  read WHOLE. **Line read:** section 2.2's audit table. TOOK the
  instantiation-audit method and the depth-two refutation sketch my term
  machine-checks.
- `agents/tasks/LJ-1-242/lj-1.242-report.md`, read WHOLE. **Line read:**
  section 2, "`q` is unprovable. MEASURED." TOOK the constant chain and
  the reading my term replaces.
- `agents/tasks/LJ-1-244/lj-1.244-report.md` and
  `agents/tasks/LJ-1-244/ProbeLJ1244A.agda`, read WHOLE. **Line read:**
  report section 1.2, "the goal is stuck". TOOK `q'`'s type and the
  chapter price I cite.
- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda`, read WHOLE. **Line read:**
  `:146`, `φ₀ = closeN 14 (pins ∧̇ renamed)`. TOOK `φ₀` itself; my probe
  imports it.
- `agents/tasks/LJ-1-238/GenSequence.agda`, read WHOLE. **Line read:**
  `:167`, `GraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b)
  zero)`. TOOK `LsetGraphAt`'s definition, the refutation's LHS.
- `agents/tasks/LJ-1-249/ProbeLJ1249.agda`, read WHOLE. **Line read:**
  `:59-66`, the GenSequence application. TOOK the instantiation shape my
  probe mirrors.
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, read `:180-200`. **Line
  read:** `:190-192`, `AmbientRead`. TOOK `amb`'s verbatim type.
- `archive/dev/TASKS-archived.md`, read `:60-110`. **Line read:** `:68`,
  "`L3.32-T33 | Condensation crossing | DELIVERED`". TOOK the boundary:
  the archive's TASKS row claims DELIVERED for the PARAMETERIZED
  crossing, while the archived code leaves `Assembly (φ : Formula Sᴹ 2)
  (co : CrossOut φ)` applied nowhere and its own owed "class-carrier
  equivalence" standing (`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:208`
  and `:806-809`, both read). **What would NOT transfer:** the retired
  route worked at a transitive carrier `Sᴹ` directly, so it owes no
  `el`, `fwd` or `bwd`, and its `σᴹ` is the rud-side story, so its owed
  equivalence is story-against-description on the S tower. Bedrock's `q`
  is Def-coding-against-parameter-free on the L tower. The SHAPE
  transfers, a parameterized crossing plus an owed equivalence; the
  content does not. INFERRED, from the two files.

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-115`, `:209-232`, `:370-392`.

**Which row, and does Devlin prove this clause or assume it?**

**Row C1**, "level-hood formula, Σ₁-with-Σ₀-matrix, uniform Δ₁, witness
in carrier, PER-TOWER content" (`dev/literature/devlin-II5.md:374`).
`amb` is clause (a)'s right-to-left half at the ambient carrier, the
soundness direction; `[LJ-1.267]` section 4 labells the same row.

**He TAKES it, he does not prove it in II.5.** `:95-96` quotes
`dev2.txt:1186-1194`: "By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST
such that (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]". The citation is to
II.2.7, the level-formula construction; II.5 consumes it. Section 5.1
(`:400-407`) names the chain 2.4 to 2.7 as "the engine". **This is
evidence about outcome 2, as the brief wanted:** the source itself
imports its level-hood certificate from an earlier chapter, and
Bedrock's phase imports the same content from a chapter it has not
written (`q'`).

**Devlin has NO two-coding bridge.** He carries ONE formula `Φ` and its
ℒ-analogue `φ`, bridged by 1.9.15, Σ₀ absoluteness between one formula
read at two carriers (`:98-101`, requirement 3 at `:222-225`). Nothing
in the source asks two different formulas to be syntactically equal.
**So `q` is Bedrock's own artifact**, born of making the level-hood
formula parameter-free while the coded graph keeps its constants.
INFERRED, from the absence in Devlin plus my measured depth-two
mismatch. This agrees with `[LJ-1.243]` section 3.4 and `[LJ-1.244]`
section 8.

**WHY NOT the other rows:** C2 is the bounded Def-step matrix, C3 the
Σ₀ absoluteness, C4 the transfer along elementarity, C5-C6 bookkeeping
and unions, D and G the well-order, E the counting, F the cardinal
chain. `q` names none of them; it is the level-hood certificate's
ambient half, C1.

## 10. PROHIBITIONS, ANSWERED

No master edited. `src/Everything.lagda.md` not opened.
`src/L/Coding/EnvSupply.lagda.md` and `src/L/Coding/Key.lagda.md` not
touched. `agents/tasks/LJ-1-291/`, `agents/tasks/LJ-1-292/` and
`scripts/` not touched. `src/L/Choice/Name.lagda.md` not opened.
`dev/ledger.toml` and `dev/PLAN.md` not touched. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`. One Agda
process at a time, cap never raised, no heap exhaustion.

**My files:** `agents/tasks/LJ-1-293/lj-1.293-report.md` and
`agents/tasks/LJ-1-293/ProbeLJ1293A.agda`. The probe passes
`scripts/lint-agda.py --check`. This report passes
`scripts/lint-prose.py --check`.
