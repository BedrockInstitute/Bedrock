# LJ-1.123: re-price the level-hood certificate, the phase's last wall

tier: codex (default)

## STATUS

COMPLETE. The price fell. The inherited figure priced the whole
certificate chapter. The LJ-1 series delivered almost all of it. The
remainder is the transfer into the hull. It re-prices at about 0.6
thousand in-fence lines, band 0.35 to 0.85 thousand. The inherited
figure was 2.8 to 3.3 thousand lines. The tree grew under the price.
The chapter shrank by about 2.45 thousand lines, center to center.

No Agda probe ran. The widest unmeasured term is the bounded level-graph
decode. Its probe is named in section 3. One Agda process would have
run the chapter's own content, and the smaller candidate steps are
already delivered. The pricing rests on read evidence at `file:line`,
not on a probe.

No commit. No push. No master edited. `src/L/Coding/` read only.
The sibling landed `[LJ-1.122]` during this turn. HEAD moved from
`65a48d1` to `8d60efe`. The pricing evidence was read against
`65a48d1`'s tree. The landed `EnvSet` content strengthens the carrier
facts half (section 2.1). It does not change the figure.

## 0. THE RE-PRICED FIGURE

**The remainder re-prices at 0.6 thousand in-fence lines, band 0.35 to
0.85 thousand.** The inherited figure was 2.8 to 3.3 thousand lines
(`_build/lj-1.12-report.md:8-14`). The new figure is one best-effort
number. Its basis is the delivered component map in section 1.

The remaining content is four pieces:

| piece | band | class |
|---|---:|---|
| the bounded level-graph decode, both ways | 0.10-0.25k | INFERRED, on delivered agreements |
| the certificate truth at the hull ordinals, with the bound in the stage | 0.10-0.25k | INFERRED, on delivered level facts |
| the three transfer lemmas at the hull | 0.10-0.25k | INFERRED, on delivered transfer machinery |
| the assembly into `Co` | 0.03-0.08k | INFERRED, glue |

The four bands sum to 0.33 to 0.83 thousand lines. The center is about
0.6 thousand, and the headline band rounds to 0.35 to 0.85 thousand.
The inherited center was about 3.05 thousand. The price fell by about
2.45 thousand lines, a factor of about five.

Every band is a projection, not a measurement. The pieces it names are
delivered. The assembly that uses them is not built. The projection
follows the delivered-piece rate of this tree. A probe in section 3
measures the widest band before funding.

Load averages at the measurement: 4.28 / 5.30 / 5.55, four users; at
the close: 6.53 / 6.04 / 5.82. Standing at the close: 28,611 lines
over 85 masters, measured from HEAD by `scripts/ledger.py --brief`.

## 1. WHAT THE INHERITED FIGURE COVERED

**The figure covered the whole certificate chapter, and the chapter has
since been mostly delivered.** The figure was not one residue. It was
the entire crossing: the bounded substrate, the adequacy, the transfer,
the carrier facts, the iso-invariance, and the limit case.

Route A's component table is at `_build/lj-1.12-report.md:27-45`:

| component | band at LJ-1.12 | today |
|---|---:|---|
| bounded code-set description and adequacy | 0.2-0.5k | DELIVERED |
| bounded twelve-clause table and adequacy | 0.7-1.6k | DELIVERED |
| bounded step, approximation, graph, Sigma-1 stack | 0.3-0.6k | DELIVERED, decode excepted |
| equivalence against the delivered machine | 0.3-0.8k | DELIVERED |
| transport certificate | 0.15-0.30k | DELIVERED |
| carrier facts: sequence and bound in the carrier | 0.15-0.45k | DELIVERED, site half landed at `8d60efe` |
| satisfaction iso-invariance under the collapse | 0.08-0.14k | DELIVERED |
| limit case | 0.124k measured | DELIVERED |

The report's own words said the price "re-bases the substrate band and
adds the carrier facts" (`_build/lj-1.12-report.md:8-11`). Section 3 of
the report split the crossing into a shared part of 0.4 thousand and a
Def-only part of 2.9 thousand (`:95-124`). Neither part excluded the
transfer into the hull. Both parts are the substrate the hull transfer
rides.

The LJ-1 series then built the substrate. `src/L/Condensation.lagda.md`
did not exist at the LJ-1.12 commit. It exists today at 6,445 in-fence
lines. `src/L/BoundedSubset.lagda.md` did not exist either. It exists
today at 1,409 in-fence lines. This is **MEASURED** by
`git diff --stat 823cbf8 65a48d1 -- src/`: Condensation +7,033, and
BoundedSubset +1,626.

The delivered components, at `file:line`:

- The bounded existential clause and its two-way decode:
  `src/L/Condensation.lagda.md:117-273` (the matrix), `:312-407`
  (`ClauseDecode`, `existBnd-out`, `existBnd-in`, `σL-out`, `σL-in`).
- The Sigma-1 stack: `:266-273` (`existCertAt`, `Σ₁-cert`).
- The transport certificate: `:284-312` (`EraseTransfer`),
  `:409-413` (`CertTransfer`, `cert-transfer`).
- The bounded step, approximation and graph matrices:
  `:2410-2493` (`StepB`, `ApproxB`, `GraphB`).
- The row agreements against the machine:
  `src/L/Condensation/TwelveAgree.lagda.md:46` (the abstract frame),
  `:6680-6900` (`SatGraphAgree`), and `:7000-7033` (`LeafAgree`).
- The graph reads the tower, and the tower writes the graph:
  `:419-428` (`ride-only`, `ride-defines`), from
  `src/L/Hierarchy.lagda.md:334-338` (`Lset-only`) and
  `:386-387` (`graph-table`).
- The Sigma-1 level-hood at the class carrier:
  `src/L/BoundedSubset.lagda.md:74-146` (`LevelHood`, `levelHoodΣ₁`,
  `Σ₁-levelHood`), and `:840-869` (`LevelHood0`, `Σ₂`, `reverse`).
- The satisfaction iso-invariance under the collapse:
  `:152-320` (`IsoInv`, `iso-inv`, `iso-inv-bwd`), `:321-350`
  (`CollapseIso`).
- The down-reflection at the hull: `:356-450` (`DownReflect`,
  `down-reflect`), `:667-788` (`HullElemDown`, `elem-down`).
- The limit case: `:903-1035` (`HullStage`, `Condense`, `β-succ`,
  `πX⊆Lβ`, `Lβ⊆πX`, `ext`, `condenses`).
- The level sequence inside the stage: `src/L/Axioms/Basic.lagda.md:154-157`
  (`isL-Lset`, the level is a definable subset of itself),
  `:196` (`Lset-suc`), `src/L/Constructible.lagda.md:355`
  (`Lset-mono`).
- The environment set inside L: `src/L/Coding/EnvSet.lagda.md:182-194`
  and `:381-385`. The sibling landed this at `8d60efe` during this
  turn.

The answer to the brief's question: the figure covered this certificate
alone, but "alone" meant the whole chapter. The chapter is not a residue
that survived. It is a chapter the tree built under the price.

## 2. THE THREE FACTS

The three facts are the supply wall of `[LJ-1.121]`
(`_build/lj-1.121-report.md:113-150`, `src/ProbeLJ1121A.agda:102-118`).
Each fact below names its delivered halves. The halves exist. The
assembly does not.

### 2.1 `hullLevel`

`hullLevel : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ πX ⟩ → ⟨ Lset δ ∈ˢ M ⟩`
(`src/ProbeLJ1121A.agda:103`).

**NOT DELIVERED as a named lemma.** No master names `hullLevel` or any
lemma of its type. This is **MEASURED** by `rg` over `src/`.

**HALF-DELIVERED.** The halves:

- The hull is Sigma-1 closed at hull parameters: `hull-closed`,
  `src/L/Hull.lagda.md:415-418`.
- The down-reflection from the stage into the hull:
  `DownReflect.down-reflect`, `src/L/BoundedSubset.lagda.md:443-449`.
- The Sigma-1 level-hood statement at an ordinal:
  `LevelHood0.Σ₂` and `Σ₁-Σ₂`, `src/L/BoundedSubset.lagda.md:855-859`.
- The collapse value of a member of the hull:
  `πX-member`, `src/V/Collapse.lagda.md:78-84`.
- An ordinal of the stage is an ordinal of the index:
  `ord∈Lset→∈`, `src/L/Ordinal/Stages.lagda.md:265-268`.
- The stage contains the level at an ordinal below it:
  `isL-Lset`, `src/L/Axioms/Basic.lagda.md:154-157`; `Lset-suc`, `:196`;
  `Lset-mono`, `src/L/Constructible.lagda.md:355`.

The missing half is the assembly: for a collapse ordinal `δ`, take its
hull preimage `δ'` (`πX-member`), show the level-hood statement at `δ'`
in the stage, reflect it down (`down-reflect`), and conclude
`Lset δ' ∈ M`. The statement "δ' is an ordinal" transfers along the
collapse by `IsoInv` (section 2.2). The conclusion needs `δ' ∈ λ`,
which is `ord∈Lset→∈` at `Hull⊆L` (`src/L/Hull.lagda.md:330-331`).

### 2.2 `piFixesLevel`

`piFixesLevel : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ πX ⟩ → π (Lset δ) ≡ Lset δ`
(`src/ProbeLJ1121A.agda:104`).

**NOT DELIVERED as a named lemma.** No master names `piFixesLevel` or
any lemma of its type. This is **MEASURED** by `rg` over `src/`.

**HALF-DELIVERED.** The halves:

- The collapse fixes a transitive subset pointwise:
  `fixes`, `src/V/Collapse.lagda.md:337-355`.
- The satisfaction iso-invariance along the collapse, both ways:
  `IsoInv.iso-inv` and `iso-inv-bwd`,
  `src/L/BoundedSubset.lagda.md:195-319`; the collapse instance at
  `:321-350` (`CollapseIso`).
- The graph reads the tower, both ways:
  `ride-only`, `ride-defines`, `src/L/Condensation.lagda.md:419-428`.

The missing half is the transfer: the level-hood statement at `δ'` in
the hull maps under `π` to the level-hood statement at `δ` in `πX`.
`IsoInv` carries the satisfaction. The level-hood statement must decode
at both carriers. The decode is the bounded graph decode of section 3.

### 2.3 `CoverTransfer`

`CoverTransfer : (y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ γ ∈ S ] (IsOrd γ ×
⟨ γ ∈ˢ πX ⟩ × ⟨ π y ∈ˢ Lset γ ⟩) ∥₁`
(`src/ProbeLJ1121A.agda:116-118`).

**NOT DELIVERED as a named lemma.** No master names `CoverTransfer`.
The consumer `cover` is still a hypothesis at
`src/L/BoundedSubset.lagda.md:918-919` and `:1409-1411`. This is
**MEASURED**.

**HALF-DELIVERED.** The halves:

- The covering Sigma-1 statement: `LevelHood0.reverse`,
  `src/L/BoundedSubset.lagda.md:861-869`.
- A member of a stage lies below the stage:
  `Lset-out`, `src/L/Constructible.lagda.md:336-338`.
- The down-reflection and the iso-invariance, as in sections 2.1 and
  2.2.

The missing half is the assembly: for `y ∈ M`, take `δ'` with
`y ∈ Lset (sucV δ')` (`Lset-out`, `Lset-suc`), reflect the covering
statement at `y`, and transfer it along `π`. The result is `π y ∈ Lset γ`
with `γ = π δ' ∈ πX`.

### 2.4 The three facts are one content

All three are the same transfer: the level-hood statement moves between
the hull and the collapse, and the collapse fixes the level. The
`[LJ-1.121]` reduction measured this (`src/ProbeLJ1121A.agda:102-111`,
GREEN at 2.96 s). The reduction's two parameters and the covering type
are the wall. The wall is not a missing theorem. It is a missing
assembly of delivered theorems.

## 3. THE WIDEST UNMEASURED TERM AND ITS PROBE

**The widest unmeasured term is the bounded level-graph decode.** The
matrices `StepB`, `ApproxB` and `GraphB` are delivered with their
Delta-0 witnesses (`src/L/Condensation.lagda.md:2410-2493`). No master
decodes them. `graphBndAt` has no two-way lemma against `LsetGraphAt`
or against `Lset`. `ride-only` and `ride-defines` decode the unbounded
graph only (`src/L/Condensation.lagda.md:419-428`). `LevelHood` consumes
`GraphB` at `src/L/BoundedSubset.lagda.md:81-109`, and nothing consumes
`LevelHood`. This is **MEASURED** by `rg` over `src/`.

The decode is the load-bearing step of all three facts. Without it, the
level-hood statement cannot be read or written at the class carrier.
With it, the assembly in section 2 is a composition of delivered
agreements (`LeafAgree`, `src/L/Condensation.lagda.md:7000-7033`; the
step and approximation decodes of `src/L/Coding/Sequence.lagda.md:217-301`).

**The probe**: write the two-way decode of `graphBndAt` at the class
carrier, under the `KFacts` site facts
(`src/L/Condensation.lagda.md:5939-5975`). One direction reads the level
from the satisfied matrix. The other writes the matrix from the level.
GO: both directions close at or below 150 probe lines. Then the decode
band moves from INFERRED to MEASURED. NO-GO: a missing site fact walls
one direction. Then the band re-opens at the full substrate rate.

This probe is `[LJ-1.12]`'s probe, re-targeted
(`_build/lj-1.12-report.md:173-200`). Its statement 1, the existential
clause decode, is now DELIVERED (`ClauseDecode`,
`src/L/Condensation.lagda.md:312-407`). Its statement 2, the carrier
facts, is DELIVERED in the level half (`isL-Lset`, `Lset-suc`) and in
flight in the site half, now landed (`EnvSet`, `8d60efe`). The
remaining probe is the graph decode, one dispatch at about 150 to 250
probe lines.

## 4. DOES THE SITE NARROW THE NEED

**No.** The consumers use the three facts at the hull's own objects.
`levelIn` feeds `Lβ⊆πX` at `src/L/BoundedSubset.lagda.md:1020`. `cover`
feeds `β-succ` at `:967`, `πX⊆Lβ` at `:1002`, and `x∈Lκ` at `:1606`.
All four uses quantify over arbitrary hull members or collapse
ordinals. The site values `α = ω`, `x = ∅` do not enter the types
(`src/ProbeLJ194A.agda:1186-1233`). This is **MEASURED** by reading the
uses.

The D-30 narrowing already happened. `[LJ-1.117]` and `[LJ-1.119]`
restricted `sq` and `absorbs-subset` to the site. `levelIn` and `cover`
were already at the hull's objects (`_build/lj-1.121-report.md:174-184`).
No further restriction is available.

## 5. HOW DEVLIN PROVES IT

Devlin proves the two halves as one Sigma-1 transfer
(`dev/literature/devlin-II5.md` section 1.2). The level-hood statement
"v = L_γ" is Sigma-1 with a Sigma-0 matrix (Devlin 2.7), so its truth
transfers from L_α down to the hull and along the collapse.

The forward half: for each collapse ordinal γ, the Sigma-1 statement
"∃v∃z φ(z, v, γ)" moves from L_α to X and then to M. Absoluteness and
the level formula decode the witness v as L_γ, giving L_γ ∈ M for every
γ < β (`dev2.txt:1200-1240`). This is `hullLevel` plus `piFixesLevel`.

The reverse half: the same transfer on "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)"
gives M ⊆ ⋃_{γ<β} L_γ (`dev2.txt:1245-1290`). This is `CoverTransfer`.
The digest's requirement list for the transfer is section 2.3 of
`devlin-II5.md`, and the delivered tree now covers it.

## 6. THE C-39 SECTION

No brief prohibition blocked a route I could see. Audited one by one:

- **Do not edit any master.** Respected. No master changed by me. The
  sibling's three files were modified during this turn, then committed
  at `8d60efe`.
- **Do not touch `src/L/Coding/`.** Respected. Read only.
- **Do not build the chapter.** Respected. This report prices the
  remainder. It does not write it.
- **Probes are `src/ProbeLJ1123*.agda`.** No probe written. The reason
  is in the next item.
- **One Agda process at a time, cap never raised.** No Agda ran. The
  decisive probe would have built the chapter's hardest piece, the
  bounded graph decode. That is a build, not a price. The smaller
  candidate steps, the level-sequence membership and the ordinal
  transfer, are already delivered (`isL-Lset`, `Lset-suc`, `IsoInv`).
  Nothing small remained to measure.
- **Never `src/Everything.lagda.md`.** Not touched.
- **Do not run `make check`.** Not run.
- **Do not raise the heap cap.** No Agda process ran, so no cap was set
  or raised.

The door worth naming: the remainder is not one wall. It is three
assemblies over delivered machinery, and one unbuilt decode gates all
three. The next dispatch should run the section 3 probe, then build the
assembly. The brief's own wall, "the certificate priced at 2.8 to 3.3
thousand and not built", is the wall I re-priced, not a prohibition.

## 7. NEGATIVES AND THEIR STATUS

1. "The inherited figure covered the whole certificate chapter":
   **MEASURED TRUE**. The component table and the split are at
   `_build/lj-1.12-report.md:27-45` and `:95-124`.
2. "The chapter has since been mostly delivered": **MEASURED TRUE**.
   The components are at `file:line` in section 1. The tree diff is
   **MEASURED** by `git diff --stat 823cbf8 65a48d1`.
3. "`hullLevel` is not delivered": **MEASURED TRUE**. No master names
   it or its type.
4. "`hullLevel`'s halves are delivered": **MEASURED TRUE**. Section 2.1
   lists them at `file:line`.
5. "`piFixesLevel` is not delivered": **MEASURED TRUE**. No master
   names it or its type.
6. "`piFixesLevel`'s halves are delivered": **MEASURED TRUE**. Section
   2.2 lists them.
7. "`CoverTransfer` is not delivered": **MEASURED TRUE**. `cover` is a
   hypothesis at `src/L/BoundedSubset.lagda.md:918-919`.
8. "`CoverTransfer`'s halves are delivered": **MEASURED TRUE**. Section
   2.3 lists them.
9. "The bounded level-graph decode is missing": **MEASURED TRUE**.
   `graphBndAt` has no two-way lemma, and `LevelHood` has no consumer.
10. "The remaining assembly is about 0.6 thousand lines": **INFERRED**.
    It is a projection over delivered pieces. No probe measured it.
11. "The assembly stays in the parameterized check class":
    **INFERRED**. The statements are at variable slots, but the check
    rate is not measured at this assembly.
12. "The site narrows the need": **MEASURED FALSE**. The consumers are
    at the hull's own objects.
13. "The certificate assembly is tower-free": **MEASURED TRUE on the
    Def side** (the three facts name only hull and collapse objects).
    **INFERRED on the J side** (no J tower exists in this tree).

## 8. DD4

**The assembly is tower-generic. The certificate instance is per-tower.**
The three facts name only the hull carrier `M`, the collapse `π`, and
the collapse image `πX`. They name `Lset` only through the level-hood
statement. The transfer machinery they ride is shared: the collapse
(`src/V/Collapse.lagda.md`), the hull with `hull-closed`
(`src/L/Hull.lagda.md:415-418`), the iso-invariance
(`src/L/BoundedSubset.lagda.md:152-350`), and the down-reflection
(`:356-450`) name no tower.

The per-tower content is the certificate instance: `LevelHood` and
`LevelHood0` at the class carrier (`src/L/BoundedSubset.lagda.md:74-146`,
`:840-869`) are Def-tower content, because the level-hood graph is the
Def tower's (`LsetGraphAt`, `src/L/Coding/Sequence.lagda.md:349-354`).
This matches `[LJ-1.12]` section 3: the per-tower objects are the
level-hood certificate and the definable well-order
(`_build/lj-1.12-report.md:95-124`), and `devlin-II5.md` section 4 (rows
C1, C2, D). A J tower instantiates the same assembly with its own
certificate and its own order. The collapse and the hull are about
well-orders and transitivity, not about definability. The assembly
stays tower-free.

## 9. GATES

No Agda ran, so no check time is reported. Load averages beside every
absolute figure: 4.28 / 5.30 / 5.55 at the measurement; 6.53 / 6.04 /
5.82 at the close, four users.

- `scripts/ledger.py --brief`: standing 28,611 lines over 85 masters,
  measured from HEAD at the close. The figure in section 0 was read at
  the measurement, 28,432 lines over 85 masters.
- `scripts/lint-prose.py --check` on this report: run at the end.
- `scripts/check-unbound-hyp.py`: nothing new to check. The report is
  the only file written. No probe exists.
- `scripts/lint-agda.py --check`: nothing new to check.
- `scripts/check-probes.py --check`: clean (no new probe).
- `make check` not run (forbidden).
- Working tree: clean at the close. The sibling committed `8d60efe`
  during this turn. This report sits under `_build/`, ignored. HEAD is
  `8d60efe`. No commit, no push by me. No Agda process left running.

## 10. ARCHIVE USED

- `_build/lj-1.121-report.md`, read WHOLE. Took the reduction to
  `hullLevel`, `piFixesLevel`, `CoverTransfer` (`:113-150`), the
  inherited figure (`:148-150`), the generality check (`:174-184`), and
  the four consumer uses of the two (`:48-58`).
- `src/ProbeLJ1121A.agda`, read WHOLE. Took the two targets (`:44-50`),
  the refutation types (`:72-77`), the `Supply` reduction (`:102-111`),
  and `CoverTransfer` (`:116-118`).
- `_build/lj-1.12-report.md`, read WHOLE. Took the three prices
  (`:8-14`), the Route A component table (`:27-45`), the shared-template
  split (`:95-124`), the substitution bridge (`:160-171`), and the probe
  (`:173-205`).
- `_build/lj-1.119-report.md`, read WHOLE. Took the site entry, the
  fifteen values, and the `Co` boundary.
- `src/L/BoundedSubset.lagda.md`, read `:1-1035` and `:1355-1630`. Took
  `LevelHood` (`:74-146`), `IsoInv` (`:152-320`), `CollapseIso`
  (`:321-350`), `DownReflect` (`:356-450`), `LevelHood0` (`:840-869`),
  `Condense` (`:916-1035`), the `Co` telescope (`:1409-1411`), and the
  four uses (`:967`, `:1002`, `:1020`, `:1606`).
- `src/L/Hull.lagda.md`, read WHOLE. Took `Hull⊆L` (`:330-331`),
  `X⊆M` (`:354-355`), `hull-closed` (`:415-418`), and the order atom
  (`:437-525`).
- `src/V/Collapse.lagda.md`, read WHOLE. Took `πX-member` (`:78-84`),
  `πX-intro` (`:86-87`), `πX-trans` (`:89-98`), `fixes`
  (`:337-355`), and the `Mostowski` statement (`:213-215`, `:311-313`).
- `src/L/Condensation.lagda.md`, read the certificate and agreement
  sections (`:95-500`, `:2230-2530`, `:5939-6030`, `:6550-7033`). Took
  `Clause` (`:117-273`), `ClauseDecode` (`:312-407`), `CertTransfer`
  (`:409-413`), `ride-only`/`ride-defines` (`:419-428`), `StepB`,
  `ApproxB`, `GraphB` (`:2410-2493`), `KFacts` (`:5939-5975`),
  `SatGraphAgree` (`:6680-6900`), and `LeafAgree` (`:7000-7033`).
- `src/L/Hierarchy.lagda.md:300-440`, read. Took `Lset-only`
  (`:334-338`) and `graph-table` (`:386-387`).
- `src/L/Coding/Sequence.lagda.md`, read the header and the graph
  section (`:1-60`, `:349-354`). Took `LsetGraphAt` and its decode
  names.
- `src/L/Coding/EnvSet.lagda.md`, read the in-flight sections
  (`:120-200`, `:280-390`). Took `envS g ∈ Lset β` and `envSet-in`.
  The sibling edits this file; I read it only.
- `src/L/Axioms/Basic.lagda.md:148-205`, read. Took `isL-Lset` and
  `Lset-suc`.
- `src/L/Ordinal/Stages.lagda.md:150-270` and `:410-445`, read. Took
  `rank-Lset` (`:190`) and `ord∈Lset→∈` (`:265-268`).
- `src/L/Rank.lagda.md:191-192`, read. Took `rank-fix`.
- `src/L/Constructible.lagda.md:301-360`, read. Took `𝒟ₒ-intro`,
  `Lset-in`, `Lset-out`, `Lset-mono`.
- `dev/LESSONS.md`, read WHOLE: D-8 (`:1377`), D-30 (`:3332`), P-l
  (`:2305`), C-36 (`:3284`), C-38 (`:3427`), C-39 (`:3521`), D-10
  (`:1316`), D-29 (`:3242`), C-35 (`:3200`), C-37 (`:3381`), D-26
  (`:1676`), D-1 (`:1038`), plus the `--for recon` and `--for probe`
  bundles via `scripts/rules.py`.
- `dev/literature/devlin-II5.md`, read WHOLE. Took section 1.2 (the
  transfer), section 2.3 (the requirement list), and section 4 (the
  per-tower verdict).
- `_build/literature/dev2.txt`, NOT opened directly. Took the forward
  transfer (`:1200-1240`) and the reverse transfer (`:1245-1290`) from
  `devlin-II5.md`'s quotes.
