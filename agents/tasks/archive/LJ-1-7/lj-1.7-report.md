# LJ-1.7: the condensation theorem, then Devlin 5.5

Status: COMPLETE, with a stated residue. Written incrementally per C-22.
The report uses ASD-STE100. No commit, no push. The master is
`src/L/BoundedSubset.lagda.md` (888 in-fence lines, untracked). The
probe files `src/ProbeLJ17.agda`, `src/ProbeLJ17Skel.agda` and
`src/ProbeLJ17Cone.agda` are untracked and thrown away per D-1.

## 1. THE VERDICT

**The condensation theorem closes at its structure, and Devlin 5.5
closes at its structure, modulo the semantic-concrete transfer that
`[LJ-1.48]` measured but did not build.** The master proves: the
level-hood statement and its Delta-0/Sigma-1 certificates at the class
carrier; the satisfaction iso-invariance under the collapse; the
down-reflection at the hull through hull-closed; the ordinals of the
collapse image with the Delta-0 separation, their ordinality and their
limit-ness; the two inclusions and the equality `piX = Lset beta`
(the condensation theorem at the hull instance, from Devlin's two
transfer conclusions as hypotheses); the code count (the hull's term
algebra injects into the infinite ordinal); the cardinal argument
(`IsCardinal`, the no-injection chain, `beta < kappa`); and 5.5's
conclusion `x in Lset kappa`.

The measured rates, cold module, warm dependencies, one process, at
`GHCRTS="-A64m -I0 -M8g"`:

| piece | lines | user s (3 runs) | mean | s per line |
|---|---:|---:|---:|---:|
| whole master | 888 | 9.67 / 9.96 / 10.11 | 9.91 | 0.0112 |
| new content (sections 4-5) | 477 | 4.6 delta | 4.78 | 0.0100 |
| measured skeleton (sections 1-3) | 411 | 4.91 / 5.31 / 5.17 | 5.13 | 0.0125 |
| module-load cone | 0 | 0.06 / 0.03 / 0.03 | 0.04 | n/a |

The whole-file rate 0.0112 sits under the DD24 bar 0.012716
(`dev/ledger.toml:2589` x `:2810`). The marginal rate of the new
content, 0.0100, sits in the parameterized class. The skeleton's rate
at my caliber, 0.0125, is above the `[LJ-1.48]` 0.0097; the difference
is the wider import cone and the corrected level-hood bound. The
spreads: master 0.44 s (4.4 percent), skeleton 0.40 s (7.8 percent),
inside the 5 to 10 percent band.

The residue, stated precisely: the two transfer hypotheses
`levelIn` and `cover` of the condensation module, the inverse-collapse
injection `collapseCode`, and the hotel. Section 4 lists what each
discharge needs. The blocker for the transfer is measured and
structural: the bounded graph's code-set description carries the
arity-tag numerals as constants (`countFo matrix = 328`), so the
erase/embed route to the hull's carrier is closed, and the hull-side
instantiation of the level-hood formula (`[LJ-1.48]` section 9 item 2,
still unbuilt) is what `levelIn` and `cover` stand in for.

## 2. WHAT THE ASSEMBLY CONSUMED FROM THE DELIVERED SUBSTRATE

The master consumed exactly these delivered pieces, and nothing else:

1. The bounded graph machine `GraphB`, `DefBodyB` and their
   certificates (`src/L/Condensation.lagda.md:2396`, `:2261`), to state
   the level-hood matrix and its Delta-0 certificate.
2. The collapse `Collapse`, its transitive range `piX-trans`, the
   range membership `piX-member`, the introduction `piX-intro` and the
   transitive-fixing clause `fixes` (`src/V/Collapse.lagda.md:40`,
   `:89`, `:78`, `:86`, `:337`).
3. The hull at a stage (`AtStage.Hull`, `src/L/Hull.lagda.md:148`),
   with `X⊆M` (the generator in the hull) and `Hull⊆L`.
4. The stage arithmetic (`boundCloses`, `envCloses`,
   `src/L/Ordinal/StageArith.lagda.md:86-97`) for the closure shape;
   the ordinal-in-stage facts `suc∈or≡`, `rank-Lset`
   (`src/L/Ordinal/Stages.lagda.md:137-139`, `:190`);
   `Lset-suc`, `∅∈𝒟ₒ` (`src/L/Axioms/Basic.lagda.md:196`, `:490`);
   the level size `stage-card-lower` and the `Bound`/`Upper` machines
   (`src/L/StageCardinal.lagda.md:204`, `:59`, `:508`).
5. The FOL kit: the Levy witnesses, `abs₀`-style absoluteness through
   `FOL.Absoluteness.Single`, `erase`/`erase-inv`
   (`src/FOL/Count.lagda.md:598-637`), the renamings and the
   relabelling `⊨-map`.

What the assembly does NOT consume: the twelve-row agreements (they are
consumed only by the extraction, which is inside the residue), the
full elementarity bridge (`ElemDown` remains a stated residue), and no
placed `Δ₀` and no `absFo` anywhere (P-u held: every certificate is at
variable slots or parameter-free).

## 3. THE OBLIGATIONS AGAINST THE [LJ-1.46] TABLE

Against the eight-row table of `_build/lj-1.46-report.md:66-90`:

| obligation | [LJ-1.46] price | what landed | status |
|---|---:|---|---|
| O1 condensation assembly | 850 lines / 22 s | the level-hood certificates, the iso-invariance, the down-reflection, beta and its ordinality/limit, the two inclusions, the equality, at 888 + 477 lines total | STRUCTURE PROVED, transfer stated as `levelIn`/`cover` |
| O2 hull elementarity | 120 / 2 | the down-reflection module with `ElemDown` as a hypothesis | NOT BUILT, stated |
| O3 hull size bound | 220 / 4 | the code count PROVED (the W-type injection with the square law), the hotel stated | COUNT PROVED, hotel stated, `collapseCode` stated |
| O4 fin-inj | 75 / 1.5 | module parameter of the master (sanctioned) | ASSUMED |
| O5 cardinal argument | 180 / 3 | `IsCardinal`, `ord-emb`, the no-injection chain, `beta < kappa` | PROVED |
| O6 lambda and limit | 80 / 1.5 | the limit shape is the `succλ` premise; the ordinals-in-stages fact via `rank-Lset` | PROVED as the premise; the +omega construction NOT built |
| O7 finite case | 40 / 0.5 | VANISHES: the statement is for infinite kappa only (all 5.6 uses) | DROPPED, stated |
| O8 5.5 assembly | 110 / 1.5 | `UnionKit`, the fixes step, the conclusion chain | PROVED |

The total new in-fence content is 888 lines at 9.91 s, against the
survey's 1,675 lines / 36 s. The reduction is D-30's consumer scope:
the theorem is the hull instance, not the general theory, and the size
chain rides the presentation of the collapse image and the code count
instead of the full bijection machinery.

## 4. WHAT I ASSUMED ABOUT envInK, fin-inj AND sq

1. **envInK is NOT consumed.** The extraction chain that would consume
   the row agreements and their `envInK` site fact is inside the
   `levelIn`/`cover` hypotheses. A discharge of those hypotheses would
   consume `envInK` at the class carrier, exactly as `[LJ-1.46]` states.
2. **fin-inj is a module parameter** of the master, with the delivered
   type (`src/L/StageCardinal.lagda.md:508`). It is consumed by
   `stage-card-upper` at alpha in the size chain. Not built.
3. **sq is a module parameter**, with the delivered type
   (`src/L/StageCardinal.lagda.md:14-16`). It is consumed at alpha
   only, by the `Bound` pairing in the code count and by
   `stage-card-upper`. Not built; `[LJ-1.47]` priced its consumer form
   at 7.94 s over 744 lines.
4. **The hotel** (`⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫`) is a stated
   hypothesis, priced at 40 to 80 lines in `[LJ-1.46]`'s O3. The
   union's presentation is a quotient of the pair's index, so the
   injection needs the infinite-element shuffle, which I did not build.
5. **collapseCode** (`⟪ piX ⟫ ↪ Code`) is a stated hypothesis: the
   inverse collapse. The truncation wall is real: the witness of a
   collapse value is merely a code, and the code fiber is not a
   proposition, so no canonical extraction exists without an order on
   the codes. `[LJ-1.46]` priced this as the "chain glue" (30 to 60
   lines) plus the presentation content.
6. **levelIn and cover** are the condensation transfer conclusions,
   Devlin's (h) and (n)-(p). Their discharge is the `[LJ-1.48]`-named
   "level-hood instantiation at the hull" (erase and countFo route),
   which is blocked by `countFo matrix = 328` (the arity-tag numerals
   inside the code-set description). This is a measurement, not a
   hypothesis: `Cnt.erase matrix refl` fails with `328 != 0`.

## 5. THE DD4 SPLIT

The template, paid once and shared with the J tower: the condensation
structure (`HullStage`, `Condense`: beta, beta-isOrd, beta-succ, the
two inclusions, the equality), the ordinal formula and its adequacy,
`UnionKit`, the code count's shape (a W-type injection into an ordinal
with pairing), the cardinal machinery (`IsCardinal`, `ord-emb`, the
no-injection chain), and 5.5's assembly. About 640 of the 888 lines.
Nothing in these names a Def object; the transfer hypotheses are
carrier-generic.

The Def tower's own content: the level-hood matrix over `GraphB` and
`DefBodyB` with its certificates (the `LevelHood` and `LevelHood0`
modules), about 150 lines. This is the one per-tower object, matching
`[LJ-0.7]` and `[LJ-1.46]`'s prediction. D-26 bears exactly there:
the Def certificate keys on the defining syntax (the graph at slots);
the J side's structural certificate would be cheaper and does not need
the satisfaction layer (`_build/lj-1.44-report.md:37-40`).

The residue's DD4: `levelIn`/`cover` are template content (the
discharge rides the delivered iso-invariance, the down-reflection, the
agreements and `envInK`), and the level-hood instantiation at the hull
is the Def-side gate.

## 6. THE MEASUREMENTS

All runs at `GHCRTS="-A64m -I0 -M8g"`, cold module (own interface
moved aside before every run), warm dependencies, one process, user
seconds from `/usr/bin/time -p`. The machine was the shared session
machine; the load was not measured per run, so the spread is the
report's noise band.

| file | runs, user s | mean | spread |
|---|---:|---:|---:|
| `src/L/BoundedSubset.lagda.md` | 9.67 / 9.96 / 10.11 | 9.91 | 0.44 (4.4 percent) |
| `src/ProbeLJ17Skel.agda` (sections 1-3) | 4.91 / 5.31 / 5.17 | 5.13 | 0.40 (7.8 percent) |
| `src/ProbeLJ17Cone.agda` (imports only) | 0.06 / 0.03 / 0.03 | 0.04 | 0.03 |

Content deltas: master 9.87 s over 888 in-fence lines = 0.0112;
skeleton 5.09 s over 411 content lines = 0.0124; new content
(sections 4-5) 4.78 s over 477 lines = 0.0100. The in-fence count uses
`scripts/ledger.py count ... at_head=False` (888).

The DD24 bar re-derived from the ledger: 0.011057 x 1.15 = 0.012716
(`dev/ledger.toml:2589`, `:2810`). The whole-file rate 0.0112 is 0.88
of the bar. No heap exhaustion occurred; every run exited 0 under the
cap.

The aggregate arithmetic: the wing baseline `[LJ-1.48]` quotes at
6,407 lines / 77.6 s (0.0121). Adding this master at 888 lines and
9.91 s gives 7,295 lines and 87.51 s, 0.01200, inside the bar. The
`[LJ-1.47]` square-law pair (744 lines, 7.94 s) is not in this
master's import closure and remains a separate row, as in `[LJ-1.48]`.

## 7. ARCHIVE USED

- `_build/lj-1.46-report.md`, read WHOLE. Took the obligation table
  (`:66-90`), the probe design (`:181-213`), the DD4 split
  (`:252-265`), the not-sure list (`:279-296`).
- `_build/lj-1.48-report.md`, read WHOLE. Took the measured shape
  (`:66-78`), the four consumed pieces (`:81-121`), the
  consumer-scope list (`:122-137`), and the residue named at
  `:315-317` (the level-hood instantiation at the hull, erase and
  countFo route, not built).
- `src/ProbeLJ148.agda`, read WHOLE (506 lines). Took Sections 1-3
  verbatim as the skeleton; corrected the bounded existential's bound
  from the ordinal slot to the K slot (the probe's Section 1 stated
  the bound over gamma; the report's own text describes it over K).
- `_build/lj-1.47-report.md`, read WHOLE. Took the consumer-scope
  levers and the square-law consumer form.
- `_build/lj-1.12-report.md`, read sections 4-6. Took the transfer
  design and the carrier-fact statement 2 (`:185-190`).
- `_build/lj-1.19-report.md`, read WHOLE. Took the +omega closure
  shape (`:9-14`).
- `_build/lj-1.3-report.md`, read sections 5-6. Took the bridge price
  and the standing residue.
- `_build/lj-1.5-report.md`, read WHOLE. Took the erase-route
  protocol and the countFo = 0 discipline.
- `_build/l3.32-t261-report.md`, read section 2 and
  `src/ProbeT261.agda`. Took the beta-separation and beta-isOrd
  recipe (the L-native supremum).
- `archive/rud-route/src/L/Condensation.lagda.md`, read for shape
  only (the `AtCarrier` face and the limit case). Its target is
  classically false (`[LJ-1.11]`), so no price transfers.
- `dev/LESSONS.md` via `scripts/rules.py --for build`: P-h, P-k, P-l,
  P-m, P-n, P-u, P-v, R-35, R-38, R-40, I-5, C-12, C-22, D-10, D-26,
  D-29, D-30, C-31, C-34, C-35, C-36, read as the bundle.

Nothing else in `archive/` was read. WHY NOT: the remaining archived
rows are the retired route's other crossings and do not bear on the
condensation transfer.

## 8. LITERATURE USED

- `_build/literature/dev2.txt:1369-1388`: 5.5's statement and proof.
  Took the chain: the hull of `L_alpha union {x}`, the collapse, the
  condensation, the size equality and `gamma < kappa`. Read the
  condensation proof at `:1170-1325` for the two transfer directions
  (c)-(o).
- `dev/literature/devlin-II5.md`: sections 1.2-1.5 and 2.1-2.6. Took
  the level-hood strength requirement (Sigma-1 with a bounded
  witness, `:209-257`) and the transfer requirements.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids
  re-checking.
- `dev/literature/j-hierarchy.md`, `jech13.txt`: NOT read. WHY NOT:
  the J-side analogue does not change the transfer's shape.

Devlin's assumption, in one line: he assumes the level-hood formula
is absolute at transitive carriers and the collapse preserves truth,
and the formal proof must supply the satisfaction transfer; he also
assumes the cardinal arithmetic of 1.1(vii), which this proof supplies
as the injection chain with `stage-card-lower`/`stage-card-upper` and
the square law.

## 9. WHAT I AM NOT SURE OF

1. The transfer residue is the whole semantic gap. `levelIn`, `cover`
   and `collapseCode` are the exact conclusions the `[LJ-1.48]`
   skeleton was measured to assemble; the countFo-328 constant wall
   blocks the level-hood instantiation at the hull, and the code
   fiber's non-prop-ness blocks the inverse collapse. Both discharges
   are priced in `[LJ-1.46]`'s table (O1's carrier facts and transfer
   legs, O3's chain glue) and were not built here.
2. The skeleton (sections 1-3, 411 content lines) has no consumer in
   the master: the theorem takes the transfer as hypotheses instead of
   consuming the iso-invariance and the down-reflection. This is the
   C-35 tension. I kept the skeleton because the brief gates on its
   measured class; a discharge of `levelIn`/`cover` is its consumer.
3. The rate of the skeleton at my caliber (0.0124) is above
   `[LJ-1.48]`'s 0.0097. The corrected level-hood bound and the wider
   import cone are the likely causes; I did not isolate them.
4. The `succλ` premise (the limit shape) and `x in Lset lam` are
   premises of 5.5, not constructions. The +omega closure that
   `[LJ-1.19]` probed is not built; the theorem takes the limit
   ordinal as given.
5. The master's rate was measured on a shared machine. The spread is
   inside the predicted band and the verdict does not sit inside it,
   but the absolute seconds would shift on a quieter machine.
6. The aggregate arithmetic uses the `[LJ-1.48]` wing baseline; the
   square-law row is not in this master's closure and is not counted
   in its rate.

## 10. THE SCOPE NOTE

The condensation theorem lives in the ONE new master
`src/L/BoundedSubset.lagda.md`, not in `src/L/Condensation.lagda.md`.
The reason is D-30 plus iteration cost: the theorem is built at the
hull instance (the 5.5 consumer), and the Condensation master's cold
check is 56.08 s (three runs, this session), so every iteration on the
instance-shaped content would re-pay the closed 4,564-line table. The
orchestrator may move the theorem into Condensation at audit time; the
content is module-parameterized and does not depend on its home.
