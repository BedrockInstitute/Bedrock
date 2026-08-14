# LJ-1.228 report: `sl` and `sc` are not supplied, and they price at about 0.15k each

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. **No Agda ran. No
slot held. No master, brief or report edited. No commit, no push.** Every
negative is marked **MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. LEAD

**NEITHER `sl` NOR `sc` IS SUPPLIED. I mark that MEASURED.** The tree delivers
the level-hood formula and its Σ₁ certificate at the class carrier, the
class-carrier read-offs in both directions, the ambient read-off in one
direction, the stage ordinal facts, and the absoluteness. It proves nothing
that says the stage believes its own level-hood. `LevelHood0.Σ₂` is defined and
unconsumed.

**The price is neither 2.8k to 3.3k nor 16.** `sl` prices at about **0.15k**
in-fence lines, `sc` at about **0.15k**. Both share one object, the stage-carrier
level-hood instantiation, so the joint price is about **0.25k to 0.35k**. The
basis is `[LJ-1.123]`'s delivered-component map, with the hull-transfer band
removed because `[LJ-1.160]` and `[LJ-1.178]` bypassed it. **INFERRED**: no probe
ran, and P-l says a class-carrier comparable is a hypothesis at another carrier.

**Neither hypothesis is false at the site.** `sl` holds for every stage. `sc`
holds exactly at limit stages, and the site already carries the limit hypothesis
`succλ`. **This is one per-tower object, not two.**

## 1. QUESTION 1: DOES THE TREE SUPPLY THEM

I searched for the content, not the name. The two are internal `⊨ᵐ` statements
at the stage carrier `Lset lam`.

### 1.1 What the tree delivers

| object | what it is | at |
|---|---|---|
| the level-hood formula and its Σ₁ certificate | the bounded matrix and `Σ₁-levelHood` | `src/L/BoundedSubset.lagda.md:74-146` |
| the two-variable level-hood at arity zero | `Σ₂`, `Σ₁-Σ₂`, `reverse` | `src/L/BoundedSubset.lagda.md:840-869` |
| the class-carrier read-off, both directions | `Lset-only`, `Lset-defines` | `src/L/Hierarchy.lagda.md:334`, `:646` |
| the ambient read-off, one direction | `graph-only`, `clause-a` | `agents/tasks/LJ-1-184/ProbeLJ1184A.agda:257`, `:355` |
| the stage ordinal facts | `ord∈Lset-suc`, `ord∈Lset→∈`, `Lset-cumul` | `src/L/Ordinal/Stages.lagda.md:434`, `:265`, `:164` |
| the level closure machinery | `isL-Lset`, `Lset-suc`, `Lset-mono` | `src/L/Axioms/Basic.lagda.md:154-157`, `:196`, `src/L/Constructible.lagda.md:355` |
| absoluteness | `abs₀`, `σ₁-up` | `src/FOL/Absoluteness.lagda.md:122`, `:182` |

### 1.2 What the tree does NOT deliver

`sl` is `StageLevels` at `agents/tasks/LJ-1-178/ProbeLJ1178A.agda:360-361`:
the stage believes every ordinal has a level. `sc` is `StageCovered` at
`:405-406`: the stage believes every set lies in a level. Both are inner `⊨ᵐ`
statements at the stage carrier.

I searched every site where the stage inner semantics `⊨ᵐ` is used. The uses are
in `src/L/BoundedSubset.lagda.md` (56), `src/L/Hull.lagda.md` (24), and
`src/L/Choice/Name.lagda.md` (11). All of them concern the hull's elementarity,
the collapse iso-invariance, or the naming of constructs. None of them concludes
that the stage believes the level-hood. **MEASURED**, by `git grep -n "⊨ᵐ"` over
`src/`.

`LevelHood0.Σ₂` and `LevelHood0.reverse` (`src/L/BoundedSubset.lagda.md:855-869`)
are the level-hood and covering statements. `LevelHood0` has no consumer outside
its own definition. **MEASURED**, by `git grep -n "LevelHood0"` over the tree:
the only hits outside the definition are agent reports and probes.

**Neither is supplied. MEASURED.**

## 2. QUESTION 2: THE CROSSING OR THE BYPASS

### 2.1 What `[LJ-1.160]`'s 16 lines reach

`[LJ-1.160]`'s probe derives `levelIn` and `cover` from one crossing face. The
face is `CrossOut`, `HasLevels` and `Covered` at the collapse image
(`agents/tasks/LJ-1-160/ProbeLJ1160A.agda`, its report section 2.2). The 16
lines price the ASSEMBLY of `levelIn` and `cover` from that face. **The 16 lines
do NOT reach `sl` or `sc`. MEASURED.** `[LJ-1.160]`'s own report says the three
face facts stay open (its section 3.3).

### 2.2 What `[LJ-1.178]` moved

`[LJ-1.178]` showed that `HasLevels` and `Covered` derive from two stage facts
plus two delivered transports. The two stage facts are `StageLevels`
(`ProbeLJ1178A.agda:360-361`) and `StageCovered` (`:405-406`). The transports
are the hull's elementarity and the collapse iso-invariance. So the debt moved
off the collapse image and onto the stage. `[LJ-1.178]`'s report section 7 says
this at `file:line`, and the probe's `module Whole` (`:489-493`) takes `sl` and
`sc` as hypotheses.

### 2.3 What this means for the two records

`[LJ-1.121]` priced `levelIn` and `cover` by the HULL route, at 2.8k to 3.3k.
The hull route needs `hullLevel`, `piFixesLevel` and the wall
`π (Lset m') ≡ Lset (π m')`. `[LJ-1.160]` bypassed that route. So
`[LJ-1.121]`'s figure prices a route nobody uses now.

`[LJ-1.123]` already re-priced the same content to 0.6k, and it named the
missing load-bearing term: the bounded level-graph decode. `[LJ-1.178]` then
moved the debt to the stage. **The record that matches today is `[LJ-1.178]`.**
The 16 was right about the assembly and wrong as a price of `sl` and `sc`. The
2.8k to 3.3k was right about the hull route and that route is bypassed.

## 3. QUESTION 3: THE PRICE

`sl` and `sc` are the level-hood instantiation at the STAGE carrier. This is
Devlin's clause (b), the localized form, not the hull transfer and not the
assembly. The content is the bounded level-hood decode at the stage, the
placement of the bound and the internal hierarchy into the stage, and the two
stage closure facts.

`[LJ-1.123]` split the remaining content into four bands. Two of them are this
content:

| `[LJ-1.123]` band | size | maps to |
|---|---:|---|
| the bounded level-graph decode, both ways | 0.10k to 0.25k | the shared object |
| the certificate truth at the stage ordinals, bound in the stage | 0.10k to 0.25k | `sl` |
| the three transfer lemmas at the hull | 0.10k to 0.25k | BYPASSED, removed |
| the assembly into `Co` | 0.03k to 0.08k | delivered by `[LJ-1.178]` |

**Prices.**

- **`sl`: about 0.15k in-fence lines**, band 0.10k to 0.25k. **INFERRED.** Basis:
  `[LJ-1.123]`'s certificate-truth band, plus the level closure `Lset b ∈ Lset lam`
  from `isL-Lset`, `Lset-suc` and `Lset-mono`.
- **`sc`: about 0.15k in-fence lines**, band 0.10k to 0.25k. **INFERRED.** Basis:
  the same shared decode, plus the covering fact for limit `lam`, from `Lset-out`
  and `Lset-suc`. The limit hypothesis `succλ` is already in the site telescope
  (`src/L/BoundedSubset.lagda.md:904`, `:1394`).
- **Joint: about 0.25k to 0.35k**, because both share the decode.

**The basis is a probe nobody has run.** `[LJ-1.123]` section 3 named it: the
two-way decode of the bounded level-hood `graphBndAt`, GO at 150 to 250 probe
lines. Nobody ran it. For `sl` and `sc` the probe is the stage-carrier version:
write the decode at the stage with the bound and the internal hierarchy placed
in `Lset lam`. **GO** if the delivered class-carrier decode plus `isL-Lset`,
`Lset-suc` and `succλ` close it at or below 150 lines. **NO-GO** if the
placement of the bound into the stage needs new machinery.

**Which record was right: NEITHER.** The 16 prices the assembly. The 2.8k to
3.3k prices the hull route. Both are real, and neither is the price of `sl` and
`sc`. The correct record is `[LJ-1.178]`, which moved the debt to the stage, and
the stage debt prices at about 0.15k each.

## 4. COULD EITHER BE FALSE

**No Tarskian or cardinality obstruction exists. MEASURED** for the structure,
**INFERRED** for the full proof.

`sl` holds for every stage. For an ordinal `b` of `Lset lam`, the level
`Lset b` is a member of `Lset lam` by `isL-Lset`, `Lset-suc` and `Lset-mono`
(`src/L/Axioms/Basic.lagda.md:154-157`, `:196`,
`src/L/Constructible.lagda.md:355`). No limit hypothesis is needed.

`sc` holds exactly at limit stages. At a successor stage `Lset (sucV β)`, the
level `Lset β` itself is a member of `Lset (sucV β)` but of no earlier level, so
`sc` fails there. **INFERRED**: the membership `Lset β ∈ Lset (sucV β)` follows
from `isL-Lset` and `Lset-suc`, but I did not typecheck the no-earlier-level half.
The site already carries the limit hypothesis `succλ`
(`src/L/BoundedSubset.lagda.md:904`, restated `:1394`), so `sc` is not false at
the site.

**This is the value of D-10 here.** `sc`'s truth turns on `lim(lam)`, and that
hypothesis is already present. The residue is proof content, not a false target.

## 5. DD4: ONE OBJECT OR TWO

**ONE object.** `sl` and `sc` both consume the single stage-carrier level-hood
instantiation. `dev/literature/devlin-II5.md:374` classes the level-hood formula
row C1 as PER-TOWER, and `:387-389` says the per-tower content is exactly two
objects: the level-hood certificate and the definable well-order. `sl` and `sc`
are one object: the level-hood certificate's stage instantiation. The J tower
will need its own pair, but it is one object, not two. **MEASURED** for the
structure, **INFERRED** for the J side because no J tower exists in this tree.

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the tree supplies `sl` | **MEASURED FALSE.** No stage inner statement concludes the level-hood. Section 1 |
| the tree supplies `sc` | **MEASURED FALSE.** Same |
| `LevelHood0` has a consumer | **MEASURED FALSE.** No hit outside its definition |
| `[LJ-1.160]`'s 16 lines reach `sl` and `sc` | **MEASURED FALSE.** They reach `levelIn` and `cover` from the crossing face |
| the 2.8k to 3.3k prices `sl` and `sc` | **MEASURED FALSE.** It prices the hull route, which `[LJ-1.160]` bypassed |
| the debt is still at the collapse image | **MEASURED FALSE.** `[LJ-1.178]` moved it to the stage |
| `sl` is false at some stage | **MEASURED FALSE.** Level closure holds for every stage |
| `sc` is false at the site | **MEASURED FALSE.** The site carries `succλ` |
| `sc` is false at successor stages | **INFERRED TRUE.** The level at the index has no earlier level |
| the price is a measurement | **MEASURED FALSE.** It is INFERRED. No probe ran, and P-l binds |
| this is two per-tower objects | **MEASURED FALSE.** One object, two consumers |

## 7. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-178/lj-1.178-report.md`, READ WHOLE.** TOOK the four-row
  table (`:30-36`), the supply search (`:118-141`), the debt move (`:240-250`),
  and the four-statement residue (`:290-310`).
- **`agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, READ WHOLE.** TOOK `StageLevels`
  (`:360-361`), `StageCovered` (`:405-406`), `module Whole` (`:489-493`), the
  transports (`:311-351`), and `LevelHood0`'s shape at the site.
- **`agents/tasks/LJ-1-121/lj-1.121-report.md`, READ WHOLE.** TOOK the hull route
  (`hullLevel`, `piFixesLevel`, `CoverTransfer`) and its 2.8k to 3.3k anchor
  (`:113-150`).
- **`agents/tasks/LJ-1-160/lj-1.160-report.md`, READ WHOLE.** TOOK the 16-line
  assembly (`:24-44`), the three open face facts (`:266-279`), and the bypass
  mechanism (`:224-262`).
- **`agents/tasks/LJ-1-184/lj-1.184-report.md`, READ WHOLE.** TOOK the SUPPLIED
  template for `amb` (`:11-40`) and the generic read-off module (`:84-120`).
- **`agents/tasks/LJ-1-225/lj-1.225-report.md`, READ WHOLE.** TOOK the
  four-hypothesis table (`:20-34`) and the Devlin mapping (`:60-80`).
- **`agents/tasks/LJ-1-123/lj-1.123-report.md`, READ WHOLE.** TOOK the re-price
  to 0.6k (`:20-40`), the four bands (`:30-36`), and the named probe (`:150-190`).
  **This is the price anchor, and it is not in the brief's ARCHIVE list.**
- **`src/L/BoundedSubset.lagda.md`**, read `:60-160`, `:780-1035`, `:1385-1621`.
  TOOK `LevelHood` (`:74-146`), `LevelHood0` (`:840-869`), `HullStage` with
  `succλ` (`:903-904`), `levelIn` and `cover` (`:1555-1557`), `theorem`
  (`:1621`). **NOT edited.**
- **`src/L/Hierarchy.lagda.md`**, read `:300-660`. TOOK `Lset-only` (`:334`),
  `graph-table` (`:382`), `hierL` (`:621`), `Lset-defines` (`:646`).
- **`src/L/Ordinal/Stages.lagda.md`**, read WHOLE. TOOK `Lset-cumul` (`:164`),
  `ord∈Lset→∈` (`:265`), `ord∈Lset-suc` (`:434`).
- **`src/L/Axioms/Basic.lagda.md`**, read `:80-235`. TOOK `isL-Lset`
  (`:154-157`), `Lset-suc` (`:196`).
- **`src/L/Constructible.lagda.md`**, read `:300-360`. TOOK `Lset-mono` (`:355`).
- **`src/L/Coding/Sequence.lagda.md`**, read `:200-360`. TOOK `StepAt-out`
  (`:217`), `StepAt-back` (`:221`), `ApproxAt-dom` (`:295`), `ApproxAt-value`
  (`:298`), `LsetGraphAt` (`:349`).
- **`src/L/Condensation.lagda.md`**, read `:240-440`. TOOK `Σ₁-cert` (`:269`),
  `ClauseDecode` (`:312-407`), `CertTransfer` (`:409`), `ride-only` and
  `ride-defines` (`:419-428`). **NOT edited.**
- **`src/FOL/Absoluteness.lagda.md`**, read WHOLE. TOOK `abs₀` (`:122`), `σ₁-up`
  (`:182`).
- **`src/L/Hull.lagda.md`**, read `:148-360`. TOOK `AtStage` (`:149`),
  `ASt.SL` (`:157-158`), `AtM.Elementary` (`:174`).
- `archive/dev/`: **NOT read.** No archived ruling bears on this task.

## 8. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:88-120` and `:365-395`.**

Devlin states (a) at the ambient carrier and derives (b), the localized form, at
`L_α` by 1.9.15. `sl` and `sc` are exactly (b)'s two directions at the stage.
Devlin does NOT price them as a separate chapter. They are one line in the
transfer chain (`:100-106`). His proof assumes (a), which our tree now supplies
in one direction through `[LJ-1.184]`, and the Σ₁ certificate, which our tree
supplies at the class carrier. **Devlin discharges `sl` and `sc` as corollaries
of (a), not as assumptions. MEASURED** by reading `:100-112`.

The per-tower verdict at `:374` (row C1) and `:387-389` (two objects) places
`sl` and `sc` inside the single level-hood certificate object. Section 5.

## 9. RULES, ANSWERED

- **D-10.** This task IS D-10. I priced the truth before the proof: `sl` is true
  at every stage, `sc` is true at limit stages, and the site carries `succλ`.
- **C-38 as extended.** `amb` is discharged by `[LJ-1.184]`. `sl` and `sc` are
  not discharged. Nothing supplies them.
- **C-36.** Section 1.2 writes the missing term: the stage-carrier level-hood
  instantiation, the localized form of Devlin's (b).
- **C-22.** This file was written before the searches closed.
- **C-42.** I measured one site: the stage inner semantics of the level-hood. I
  did not sweep the tree for other unpriced instantiations.
- **P-l.** Section 3. The price is a class-carrier comparable, a hypothesis at
  the stage carrier. I mark it INFERRED.
- **DD8.** One figure each, with basis. Section 3.
- **D-26.** Section 5 uses the digest's per-step carrier column.
- **DD4.** Section 5. One object, not two.

## 10. PROHIBITIONS, ANSWERED

**No Agda ran. No master, brief or report edited.** `src/Everything.lagda.md`
not opened. `src/L/Choice/Name.lagda.md` not opened. The sibling directories
`agents/tasks/LJ-1-226/`, `LJ-1-227/` and `LJ-1-229/` were not touched. No
commit, no push, no `git checkout`, `stash`, `reset` or `clean`. No `make check`.

**My only file is** `agents/tasks/LJ-1-228/lj-1.228-report.md`.

`scripts/ledger.py --brief`: standing **29,777 lines over 88 masters**, from HEAD.
