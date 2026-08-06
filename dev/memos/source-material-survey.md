# Source material survey, and its cost anatomy (archived from dev/PLAN.md section 2)

> **STATUS: STANDING.** The measurements here remain the calibration anchor for the two-caliber discipline (dev/PLAN.md section 6.2); only the survey's plan placement is archived. Moved out of dev/PLAN.md by [L3.32-T113] because it updates rarely and is evidence, not instruction. Read it when a recon needs the source-scale figures: 172 modules and 70.7k lines, the field-level cost anatomy of the L⊨ZFC cone, the clone measurements, and the lever headroom table. The live plan is dev/PLAN.md section 0, and the goal registry is section 11.

---

## 2. Source material survey (condensed)

*Port-era history, kept for its measurements.* This section surveys the source
repository as it stood in July 2026 and prices the port that opened this
registry. Its cost anatomy (§2.1) is still cited as a calibration anchor; its
scope statements describe the original milestone, not the current campaign
(§0).

Facts an implementing agent needs before touching the port:

- **Scale:** 172 literate modules, about 70.7k lines. Of these, `L/` holds 142
  modules and 66.5k lines (94%). The `--safe` core (Prelude, Truth, FOL,
  Reification, ZF, Models/HITV, Examples) is only about 4k lines and is
  already clean.
- **Root module:** `src/L/ModelZFCFinal.lagda.md` defines `L⊨ZFC : ZFCModel`
  (alias `Con-AC`). The ZF axiom fields live in `src/ZF/Model.lagda.md`
  (records `ZFModel`, `ZFCModel`); separation and replacement consume the
  deeply embedded `Formula`, which is where the reification framework is
  load-bearing.
- **Difficulty concentration:** the bulk of `L/` is the well-order `<L` and
  the L-recursion, reified as Δ₀ graph-certificate clusters (`Cmp*`, `Depth*`,
  `Order*`, `Trace*`, `Coh*`), plus internal satisfaction (`Sat*`, `Tarski*`)
  and coding (`Code*`, `Formula*`). These clusters are the L3 reduction-review
  targets.
- **Prose:** Chinese research-log style throughout (milestone provenance,
  probe numbers, performance archaeology). It is **construction intelligence
  for the porting agent, not translation input** (D6).
- **Performance engineering:** the source carries a documented playbook of
  conversion-blowup countermeasures (opaque seals, explicit implicit
  arguments, Π-parameterized assumption bundles); see
  `../fol-reification/docs/WORKLOG.md` §5. After the upstream M2.7
  optimization, the full lem-cone cold check runs in about 8.5 minutes at
  `-j4` with per-module heap caps (down from 157 minutes). The build machinery
  is portable; its trust model is codified as constraints in §7.
- **Goal management:** the source runs an append-only route-tree register
  (`../fol-reification/docs/ROUTE-TREE.md`) with dotted-decimal goal codes.
  Bedrock adopts a lightened version of the same discipline (D9, rules in
  §6.0).

### 2.1 Cost anatomy (measured 2026-07-25)

Where the source's mass actually sits, measured by attributing every module to
the `isZFCModel` field whose proof term reaches it. Method: non-blank lines
inside ` ```agda ` fences (prose excluded); transitive dependency closure from
each field's filling term; module granularity, except the six assembly modules
(`L.ModelAC`, `L.ModelACSep`, `L.ModelACNum`, `L.Condensation`, `L.ModelZFC`,
`L.ModelZFCFinal`), which are split per definition. The whole `L⊨ZFC` cone is
150 modules and 48,260 code lines; the other 22 modules (2,521 lines) are
probes and unwired experiments, which the consumption audit drops at port time.

Field names below are Bedrock's (§4 ledger), source names in parentheses where
they differ. "Body" is the code that literally fills the field, "cone" includes
all shared dependencies, "own" is code reachable from this field alone.

| `isZFCModel` field | body | cone | own |
|---|---:|---:|---:|
| `extensional` | 13 | 2,279 | 13 |
| `regularity` (`foundation`) | 7 | 2,273 | 7 |
| `hasEmpty` | 20 | 2,286 | 0 |
| `hasPair` | 48 | 2,314 | 0 |
| `hasUnion` | 65 | 2,331 | 0 |
| `hasSeparation` (`hasSep`) | 87 | 4,924 | 0 |
| `hasReplacement` (`hasRepl`) | 167 | 5,004 | 0 |
| `hasPower` | 33 | 3,038 | 149 |
| `numeral` | 54 | 2,791 | 0 |
| `numeral-zero` (`num0`) | 3 | 2,819 | 3 |
| `numeral-suc` (`numS`) | 18 | 2,834 | 18 |
| `hasInfinity` | 21 | 2,812 | 21 |
| `hasChoice` | 68 | 47,839 | **42,354** |

Read as a partition, the twelve ZF fields own 211 lines between them. Their
real cost is three shared blocks: the framework and carrier trunk (2,266
lines), the Δ₀ engine with the full-formula reflection machinery (2,571
lines), and the numeral chain (392 lines). Everything else is `hasChoice`:
42,354 lines, 88% of the cone, of which 42,258 sit in 106 modules that no other
field touches.

That mass is not one proof. It is 8 to 10 hand-built instantiations of a single
pipeline (step function to Δ₀ graph to "the graph is a set of L" to
certificate to soundness), once each for comparison, depth, the order itself,
satisfaction, traces, coherence, sequence codes, and the closure families.
Clone measurement over the twin families, after normalizing names:

| module pair (renaming-normalized) | similarity |
|---|---:|
| `CmpCertMatrix` / `DepthCertMatrix` | 86% |
| `CmpCodeCarrier` / `DepthCodeCarrier` | 67% |
| `CmpGraphInL` / `DepthGraphInL` | 60% |
| `CmpGraphInLFinal` / `DepthGraphInLFinal` | 50% |
| `CmpSound` / `DepthSound` | 8% |
| `OrderGraph` / `CmpGraph` | 4% |

So the scaffolding repeats and the soundness segments do not: the mathematics
genuinely differs per instance, but the harness around it is written out once
per instance. The reason is structural: the source has no general theorem
saying a recursively defined function is internalizable in L, so every
function builds its own. Density counts corroborate: 27.9 formula-syntax
tokens and 8.3 Δ₀ witness tokens per 100 lines, 3,963 explicitly spelled
implicit arguments and 139 `opaque` seals (the M2.7 performance tax), and 53%
of all lines sitting inside `where` blocks.

Projected reduction, by lever, each with the goal code that executes it and the
register entry that tracks it:

| Lever | Headroom | Code | Candidate |
|---|---|---|---|
| General internalization theorem | to roughly 8k to 12k total | `[L3.0]` | S5 |
| `reify!` macro industrialization | 4k to 6k | `[L3.2]` | S6 |
| Scaffolding parameterization | 3k to 5k | `[L3.4]` | S3 |
| Transition-layer sweep | 2k to 3k | `[L3.1]` | S9 |
| Transport and cast solver | 1k to 2k, high risk | `[L3.9]` | S7 |
| Dispatch-grid generation | 1k to 1.5k, source lines only | `[L3.8]` | S8 |

The five syntactic levers together are 25% to 40%, and every one of them trades
against cold-check time. The general theorem is the only lever that reaches
further; it is also the only lever that is research rather than refactoring.
D12 rules on which to take, §6.1 orders their execution.

> **Correction (2026-07-25, `[L3.0.3]`).** The 8k to 12k figure above is the
> ceiling of a **three-theorem programme**, not the yield of `[L3.0]`. The
> probe measured the pipelines directly: the constant-table theorem covers
> 13,518 of the 42,258 lines, `Order*` (11,386 with its trace machinery) needs
> a separate stage-indexed theorem, and `Sat*` / `Tarski*` / `Coh*` (10,706)
> fit only by halves. On tier 1 alone the honest projection is 42.3k to about
> 36k. The route survives; the probe also found a second abstraction worth as
> much as the theorem (a per-tag clause bundle). Full tier table and evidence:
> [memos/L3.0.3-subsumption-probe.md](memos/L3.0.3-subsumption-probe.md) §5
> and §6.
