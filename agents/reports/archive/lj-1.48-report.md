# LJ-1.48: gate LJ-1.7 by measuring the condensation theorem assembly

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100. The probe is `src/ProbeLJ148.agda`, untracked,
thrown away per D-1.

## 1. THE VERDICT

**GO, leaning to the parameterized end. The measured rate is 0.0097 s per
line over the probe's 337 content lines, with the transfer statements at
0.003 s per line.** The probe's cold check is 5.01 s mean (runs 5.30,
4.93, 4.94, 4.86, spread 0.44, 8.8 percent). The import cone is 1.73 s
mean (runs 1.81, 1.74, 1.64). The content delta is 3.28 s. The brief's GO
line is 0.0127 s per line. The NO-GO line is 0.05. The measured rate is
below the GO line. The [LJ-1.46] probe GO criterion is also met: the three
statements close in 337 content lines, at or below the 350-line stop, and
the transfer statements check at or below 0.02 s per line.

The wing arithmetic with the measured O1 rate: the [LJ-1.46] survey priced
O1 at 22 s center. The probe's content rate re-prices O1 at 8 to 11 s
center. LJ-1.7 then lands at about 22 to 25 s instead of 36 s. The
aggregate row lands at 0.0129 to 0.0132 against the 0.012716 bar, inside
the 5 to 10 percent run-to-run noise band, leaning to the GO end. This is
exactly the band [LJ-1.46] predicted for the GO scenario ("0.0130 to
0.0134, near the bar, fundable with the one-spelling discipline",
`_build/lj-1.46-report.md:203-205`).

The assembly is NOT at P-n's instantiation floor (0.22 to 0.297) and NOT
at the agreement class (0.026). The transfer content is the parameterized
class. One row is not parameterized: the per-tower level-hood certificate
`Δ₀-levelHoodB` measures 2.0 s over 65 content lines, about 0.03 to 0.04 s
per line, one order above the transfer legs. It is small in absolute terms
and the whole-probe rate still lands below the GO line. Report it plainly:
the certificate is the Def tower's own content and its rate is the middle
class, not the parameterized band.

## 2. WHAT THE ASSEMBLY NEEDED FROM THE DELIVERED TABLE

The assembly consumed exactly four things from the delivered condensation
substrate, and nothing else:

1. The bounded graph machine: `GraphB`, `StepB` via `ApproxB`, `DefBodyB`
   and the certificates `Δ₀-DefBodyB`, `Δ₀-graphBndAt`
   (`src/L/Condensation.lagda.md:2261`, `:2396`). The probe states the
   level-hood matrix as `∃ w ∈ K (graphBndAt w γ K ∧ x = w)` at variable
   slots, with `Σ₁ levelHoodΣ₁ = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)`, the exact
   block-1 certificate shape (`existCertAt`, `Σ₁-cert`, at `:255-259`).
2. The collapse iso: `V.Collapse.InjExt.iso` (membership both ways),
   `InjExt.π-inj` (injectivity on the carrier) and `πX-member`
   (surjectivity of the range) (`src/V/Collapse.lagda.md:220`, `:299`,
   `:277`, `:78-80`). These are delivered; the probe's formula
   induction consumes them as data.
3. `hull-closed` for the down-reflection (`src/L/Hull.lagda.md:415`),
   which hands the witness in M from the Sigma-1 statement at the stage.
4. The FOL absoluteness kit (`abs₀`, `σ₁-up`) only for the certificate
   transfers that the delivered `EraseTransfer` template already assembles
   (`src/FOL/Absoluteness.lagda.md:122-189`). The probe used no `absFo`
   and no placed `Δ₀` (P-u): every certificate is at variable slots.

What the consumer does NOT need:

- The twelve-row decode machinery beyond the graph certificate. The probe
  imports `GraphB`, `DefBodyB` and their certificates only; it never opens
  the row agreement modules and never states a decode.
- The full elementarity equivalence. The down-reflection consumes only
  the matrix-down direction at M. The probe states it as the hypothesis
  `ElemDown` (O2's priced residue) and never needs the upward direction.
- The hull's transitivity. The iso-invariance induction uses the
  membership iso and injectivity on the carrier; it needs `isExt M`, not
  `isTrans M`. The probe takes `isExt` as a hypothesis.
- General carrier facts: the probe never proves `envInK` or any
  K-closure fact. Nothing in the three statements needs it.

## 3. WHAT THE CONSUMER DOES NOT NEED

See section 2. The consumer is the condensation theorem of 5.5. It needs
the transfer of ONE Sigma-1 statement at the hull and its collapse. It
does not need a tower-wide general law, a decode of the twelve rows, or
the upward elementarity half. The [LJ-1.47] lesson applies: content with
no consumer is the cheapest deletion, and the assembly as designed already
avoids it.

## 4. THE PROFILE ATTRIBUTION

Profile (`agda --profile=definitions`, cold module, same caliber). Total
5,401 ms with profiling overhead. The cone control measures 1,931 ms, all
Miscellaneous.

| row | ms | share of total |
|---|---:|---:|
| Miscellaneous | 2,871 | 53 percent |
| `LevelHood.Δ₀-levelHoodB` (the per-tower certificate) | 2,001 | 37 percent |
| `IsoInv.iso-inv` + `iso-inv-bwd` + helpers | 377 | 7 percent |
| `DownReflect` family (`mapFo-ext`, bridge, transports, down-reflect) | 144 | 3 percent |

The content delta over the cone is 3.28 s. The attribution of that delta:
the certificate is about 2.0 s, the transfer induction is about 0.4 s, the
down-reflection is about 0.15 s, and the un-attributed remainder is about
0.7 s. The remainder is the level-hood formula's own elaboration: the
`GraphB` instantiation with both `DefBodyB` leaves and the module-level
checks. I attribute it to Section 1 by reading, not by a gut experiment.

The per-piece rates, content lines in parentheses:

| piece | lines | attributed s | s per line | class |
|---|---:|---:|---:|---|
| Section 1, level-hood statement and certificate | 65 | about 2.4 to 2.9 | 0.037 to 0.045 | middle, Def-tower certificate |
| Section 2, iso-invariance and the collapse instance | 180 | about 0.5 to 0.8 | 0.003 to 0.004 | parameterized |
| Section 3, down-reflection and the bridge | 92 | about 0.3 to 0.5 | 0.003 to 0.005 | parameterized |
| whole probe content | 337 | 3.28 | 0.0097 | parameterized, one middle row |

The class evidence: the iso-invariance is a plain structural recursion
over `Formula SM n` at a variable carrier with the collapse data as module
parameters. Nothing in its type names a built construction. The
certificate is the opposite: its type `Δ₀ levelHoodB` names the built
graph, and the elaborator re-normalizes the graph at the certificate. This
is the P-v family at the leaves, at the measured middle rate.

## 5. THE DD4 SPLIT

The template is Sections 2 and 3, 272 content lines at 0.003 to 0.005 s
per line: the satisfaction iso-invariance under the collapse (generic in
the carrier, the collapse map, the membership iso, injectivity and
surjectivity), the collapse instantiation, and the down-reflection bridge
through `hull-closed`. Nothing in these sections names a Def object. The J
tower reuses the same transfer induction unchanged: its collapse is the
same `V.Collapse`, and only the certificate differs.

The Def tower's own content is Section 1, 65 content lines: the bounded
graph level-hood matrix over `GraphB` and `DefBodyB` and its `Δ₀`
certificate, at about 0.04 s per line. This is the one per-tower object
`[LJ-0.7]` and `[LJ-1.46]` predicted (`_build/lj-1.46-report.md:252-265`):
the level-hood certificate is the remaining per-tower object on the chain,
and DD27 already removed the second one, the definable well-order. The
measured split confirms the prediction: the template is cheap and
parameterized, and the Def certificate is the only middle-class row.

D-26 bears in one line: YES, on the Def side the level-hood certificate
keys on the defining syntax (the twelve-row graph at slots), and that
certificate is delivered; the J side's structural certificate keys on
generation data and is cheaper.

## 6. THE MEASUREMENTS

All runs at `GHCRTS="-A64m -I0 -M8g"`, cold module (own interface moved
aside to `/tmp/lj148-agdai/`), warm dependencies, one process. User
seconds from `/usr/bin/time -p`.

| probe | runs, user s | mean | spread |
|---|---:|---:|---:|
| ProbeLJ148 (506 lines) | 5.30 / 4.93 / 4.94 / 4.86 | 5.01 | 0.44 (8.8 percent) |
| ProbeLJ148Cone (imports only, 66 lines) | 1.81 / 1.74 / 1.64 | 1.73 | 0.17 (9.8 percent) |
| content delta | | 3.28 | |

Content rate: 3.28 / 337 content lines = 0.0097 s per line. Whole-file
rate over 506 lines: 0.0099 s per line. Non-comment whole-file rate over
386 lines: 0.0085 s per line. The transfer statements (Sections 2 and 3,
272 lines) attribute to about 0.8 to 1.3 s, 0.003 to 0.005 s per line.

The bar re-verified from the ledger: `ac_baseline_module_rate = 0.011057`
(`dev/ledger.toml:2589`) times `tolerance = 1.15` (`:2810`) is
0.012716. The brief's table rows re-verified by arithmetic:
79.95 / 6,459 = 0.01238; plus the square law pair (7.94 s over 744 lines)
is 87.89 / 7,203 = 0.01220; plus the LJ-1.8 remainder survey (1,200 lines,
20 s) is 107.89 / 8,403 = 0.01284; plus the LJ-1.7 survey (1,675 lines,
36 s) is 143.89 / 10,078 = 0.01428.

The wing row with the measured O1: O1 at 8 to 11 s instead of 22 s gives
LJ-1.7 at 22 to 25 s, and the aggregate is (107.89 + 22 to 25) / 10,078 =
0.0129 to 0.0132, 1.7 to 3.6 percent over the bar, inside the run-to-run
noise band. The [LJ-1.46] GO scenario predicted 0.0130 to 0.0134 for this
row and called it fundable.

No heap exhaustion occurred. Every run exited 0 under the cap. The machine
load read 4.1 at the start of the measurements; the spread is reported and
the verdict does not sit inside it, so the load does not decide the call.

## 7. ARCHIVE USED

- `_build/lj-1.46-report.md`, read WHOLE. Took the probe design
  (`:181-213`), the O1 component table (`:66-90`), the GO and NO-GO lines
  (`:198-211`), the DD4 split (`:252-265`), and the aggregate arithmetic
  (`:108-123`).
- `archive/rud-route/src/L/Condensation.lagda.md`, read WHOLE (885 lines).
  Took the shape only: `Believes`, `CrossOut`, `Condenses` (`:279-303`),
  the set-carrier `AtCarrier` (`:230-260`), the level story at both
  carriers (`:603-616`, `:683-690`). The target is classically false
  (`[LJ-1.11]`), so no price transfers.
- `_build/lj-1.47-report.md`, read WHOLE. Took the deletion levers (the
  dead general-law sections, `col→τ-fiber` at 94.3 percent of a module)
  and the consumer-first discipline.
- `_build/lj-1.43-report.md`, read WHOLE. Took the closed twelve-row
  table, the 0.0139 whole-file rate, and the marginal 0.0459 breach.
- `_build/lj-1.45-report.md`, read WHOLE. Took the pooled 58.62 s and the
  0.01273 best-set rate that the wing baseline uses.
- `_build/lj-1.12-report.md`: read sections 2 and 6. Took the
  iso-invariance estimate at 0.08 to 0.14k (`:37`, `:155-158`) and the
  class risk statement (`:160-167`).
- `src/L/Condensation.lagda.md`: `GraphB` (`:2396`), `DefBodyB` (`:2261`),
  `StepAtB`/`ApproxB` (`:2354`, `:2377`), block-1 `existCertAt` and
  `Σ₁-cert` (`:255-259`), `EraseTransfer` (`:273`), `ride-only` and
  `ride-defines` (`:403-417`).
- `src/L/Hull.lagda.md`: `AtStage` (`:148`), `AtM` (`:163`), `TV-thm`
  (`:306`), `hull-closed` (`:415`), `Hull⊆L` (`:330-331`).
- `src/V/Collapse.lagda.md`: `Collapse` (`:40`), `πX-intro` (`:86-87`),
  `πX-member` (`:78-80`), `InjExt` (`:220`), `InjExt.π-inj` (`:277`),
  `InjExt.iso` (`:299`).
- `src/FOL/Absoluteness.lagda.md`: `Single` (`:57`), `abs₀` (`:122`),
  `σ₁-up` (`:182`), `π₁-down` (`:187`).
- `dev/ledger.toml`: the module baseline (`:2589`), the tolerance
  (`:2810`).
- `dev/LESSONS.md` via `scripts/rules.py --for probe` and `--for recon`:
  D-1, D-10, C-12, C-22, C-31, C-32, C-34, C-36, D-26, P-l, P-m, P-n,
  P-t, P-u, P-v, R-40, read as the bundles.

## 8. LITERATURE USED

- `dev/literature/devlin-II5.md`: Step C (`:209-257`) and section 1.5
  (`:145-170`). Took the level-hood shape (Sigma-1 over a Sigma-0 matrix
  with the witness unbounded), the uniform Delta-1 requirement, and the
  transfer requirements (down at M, along pi both ways).
- `_build/literature/dev2.txt:1369-1388`: the 5.5 statement and proof
  chain, read to verify the digest's quote. Took the chain: the collapse
  is stated as the condensation, and the transfer is asserted.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids re-checking.
- `dev/literature/j-hierarchy.md` and `jech13.txt`: NOT read. WHY NOT: the
  J-side analogue does not change the seconds class of the transfer
  statements, which is the whole subject here.

Devlin's assumption, in one line: he assumes the Sigma-1 statement is
absolute at transitive carriers and that the collapse preserves all
first-order truth, and the formal proof must prove the satisfaction
transfer that this probe measured.

## 9. WHAT I AM NOT SURE OF

1. The elementarity-down residue `ElemDown` and the carrier
   extensionality `isExt` are hypotheses, not built. The probe measures
   the assembly around them. O2's bridge (120 lines, about 2 s, survey)
   is the gate that makes the down-reflection usable at the actual hull.
2. The level-hood instantiation at the hull with the parameters as Code
   constants (the erase and `countFo` route) is not built. The probe keeps
   every certificate at variable slots per P-u. If the placed form forces
   the placed-certificate class, the level-hood piece could cost more than
   the measured 2 s; the wall P-u measured was 8 GB in 55 s, and I did not
   re-test it.
3. The 850-line O1 center and the 36 s LJ-1.7 survey are residues from
   `[LJ-1.46]`. I re-verified the RATE, not the line counts; no code
   exists yet for O1's non-probe pieces.
4. The un-attributed 0.7 s remainder of the content delta is assigned to
   Section 1's formula elaboration by reading, not by a gut experiment.
   A gutted Section 1 (certificate replaced by a postulate) would settle
   it; the brief forbade postulates and I did not build the variant.
5. The machine load read 4.1 at measurement time. The spread is inside
   the brief's predicted 5 to 10 percent band, and the verdict does not
   sit inside the spread, but the absolute seconds would shift on a
   quieter machine.
6. The wing row at 0.0129 to 0.0132 is 1.7 to 3.6 percent over the bar.
   The bar is inside the run-to-run noise band. The one-spelling
   discipline of `[LJ-1.45]` is what the wing needs, exactly as
   `[LJ-1.46]` predicted; nothing in this probe replaces it.

Probe files created for this probe, untracked by standing rule:
`src/ProbeLJ148.agda` and `src/ProbeLJ148Cone.agda`. Interfaces moved
aside into `/tmp/lj148-agdai/`. No master, no `dev/` file, no commit.
