# LJ-1.81: is the STAGE enough, or does the proof need KFacts at the hull?

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.81-report.md`.

## 0. THE VERDICT

**The stage is the site. The hull is not.** The condensation proof does
not need `KFacts` at the hull `M` or at the collapse `C.πX`. The `K`
slot of the site-fact block, in the chain that reaches `levelIn` and
`cover`, is the bound of the level-hood matrix. That bound is a
constructible set that is an element of the stage. It is a member of the
hull `M`, and `M` is a subset of `Lset lam`. It is never the hull
itself, and it is never `Lset lam` itself.

The wall named in `[LJ-1.80]` report section 2 is not a wall. No `isL`
certificate for `M` or `πX` is needed. No such certificate exists in
the tree, and no consumer needs one.

The phase's remaining obstruction is NOT smaller than believed, in one
sense. `levelIn` and `cover` still stand as hypotheses. They still need
the unplaced leaf chain and the collapse-of-the-level step. What is
resolved is the specific question: a hull-side `KFacts` is not part of
that obstruction.

## 1. THE CONSUMER CHAIN, AT FILE:LINE

`levelIn` and `cover` are parameters of `HullStage.Condense`
(`src/L/BoundedSubset.lagda.md:916-917`). The module consumes them at
`:966` (`β-succ`), `:1001` (`πX⊆Lβ`), `:1019` (`Lβ⊆πX`), and `:1606`
(`cover x x∈M` in `Co`). Nothing supplies them anywhere in `src/`.
MEASURED: no definition of either term exists outside the parameter
lines and their uses.

The planned discharge is the level-hood adequacy at the hull. The
`[LJ-1.52]` report pins it as `Adeq m`, the parameter-index form
(`_build/lj-1.52-report.md:24-36`):

```text
Adeq m = ∥ Σ[ K' ∈ S ] Σ[ v' ∈ S ] Σ[ w' ∈ S ]
  (⟨ w' ∈ˢ K' ⟩ × ⟨ (w' ∷ v' ∷ m ∷ K' ∷ []) ⊨ LH0.matrix ⟩) ∥₁
```

The probe states it at `src/ProbeLJ152A.agda:78-81`. The matrix lives
at `src/L/BoundedSubset.lagda.md:848-849` and `:108-112`. Its env is
`w' ∷ v' ∷ m ∷ K'`. The bound is the env's last slot, `K'`.

The elementarity-down half is delivered. `HullElemDown`
(`src/L/BoundedSubset.lagda.md:667-768`) proves the TarskiVaught
instance and the `ElemDown` at the hull. The `Co` module instantiates
it as `elem-down : DR54.ElemDown` at `:1568`. MEASURED: the term is in
the tree at `:1568` and its home module is green at HEAD.

The decode of `Adeq m` needs the graph agreement at the class carrier.
`GraphAgree` is universal over the bound `K : S`
(`src/ProbeLJ152A.agda:48-51`). `matrix-decode` closes the decode from
it (`:58-61`). `graph-assembly` assembles it from `StepAgree`,
`ApproxAgree` and the site-fact bundle (`src/ProbeLJ152B.agda:71-87`).
The site-fact bundle is the `KFacts`-shaped block.

The twelve-row band states that block as one record. `SatGraphAgree`
and `LeafAgree` take `f : KFacts {8 + n} ... γ` as a parameter
(`src/L/Condensation.lagda.md:6476-6484` and `:6705-6713`). The `K`
slot of the record is the bound of the bounded graph frame in that env.

So the `K` slot, at the site the proof reaches, is the level-graph
witness bound. The witnesses `K' v' w'` are members of the hull, by
the elementarity down. Every member of the hull is an element of the
stage, by `Hull.Hull⊆L` (`src/L/Hull.lagda.md:330-331`). The bound is
therefore a constructible set inside `Lset lam`.

## 2. WHY THE HULL IS NOT THE SITE

1. `KFacts` slots are members of the class `𝒮ʟ`. The record takes
   `γ : S ^ n` with `S = ZFStructure.S 𝒮ʟ`
   (`src/L/Condensation.lagda.md:5734-5736`). A `K`-slot value must be
   a constructible set.
2. The hull `M = H.T.Hull` (`src/L/BoundedSubset.lagda.md:911`) is a
   subset of `Lset lam`, not a delivered member of `𝒮ʟ`. No `isL`
   certificate for `M` or `πX` exists in `src/`. MEASURED: a search
   for `isL M`, `isL C.πX` and their aliases returns zero hits.
3. No consumer needs one. The `Condense` mathematics quantifies over
   `M` and `C.πX` as V-sets (`:916-917`). `levelIn` and `cover` state
   memberships in `C.πX` and `M`, not constructibility of either.
4. The bounded-formula machinery is evaluated at the class carrier and
   re-based to the hull's inner world. In both readings the bound is a
   member of the carrier. The carrier itself is never the bound.
   MEASURED from the envs at `src/ProbeLJ152A.agda:48-51,78-81`.
5. `Lset lam` itself cannot be a witness bound. The Σ₂ existential
   ranges over the stage's universe. `Lset lam` is not a member of
   `Lset lam`. INFERRED from regularity; the tree delivers no
   `Lset lam ∉ Lset lam` term, but this negative sets no verdict.

## 3. THE EXACT K SLOT, AND THE ONE CAVEAT

The stage-valued `KFacts` from `[LJ-1.80]` is the satisfiability
witness and the construction template. `src/ProbeLJ180A.agda:186-226`
builds it at `K = LsetS lam`, `A = LsetS α`, with all 27 fields
supplied from the stage's closure machinery. The module `StageKFacts`
is parameterized by `lam`, `ordλ`, `succλ`, `α`, `ordα`, `α∈λ`,
`α∉ω` (`src/ProbeLJ180A.agda:32-38`).

That value is not itself the value the `levelIn` chain consumes. The
consumed bound is the witness `K'` at env `w' ∷ v' ∷ m ∷ K'`. It is a
proper stage element. The same closure construction supplies the site
facts at such bounds: the fields come from `pr∈Lset-suc`,
`Lset-mono`, `layer-trans`, trichotomy and `succλ`, which hold of
stage elements below `lam`.

The chain itself is not placed. The six masters are generic modules.
No master instantiates `SatGraphAgree` or `LeafAgree` at a concrete
env. MEASURED: instantiations exist only in probes, never in a master.
So the exact `K`-slot value of the final instantiation is not pinned by
any delivered term. What is pinned is the site class: a constructible
set inside the stage, never the hull.

## 4. WHAT THE REMAINING OBSTRUCTION STILL IS

`levelIn` and `cover` survive. Their discharge needs the pieces named
by `[LJ-1.52]` section 4.1 and the wall list:

1. The `DefBodyB`/`DefBody` leaf adequacy, both directions. The `out`
   direction produces `Adeq m` from the machine graph, per `[LJ-1.59]`
   section 0.
2. The re-basing of the graph agreement to the hull's inner world.
3. The collapse-of-the-level step `π (Lset m') = Lset (π m')`. No
   measured price exists for it.
4. For `cover`: the least-δ selection and the level-preservation under
   the collapse iso.

None of these needs a hull-side `KFacts`. The obstruction is not
smaller overall. The `KFacts`-inhabitation part of it is resolved at
the stage. MEASURED: `levelIn` and `cover` remain parameters at
`src/L/BoundedSubset.lagda.md:916-917`.

## 5. NEGATIVES AND THEIR STATUS

1. "The proof needs `KFacts` at the hull `M` or at `πX`": MEASURED
   FALSE as a delivered consumer. No master instantiates the six
   masters at a hull. No `isL M` or `isL πX` exists. The planned
   chain's bounds are stage elements.
2. "The final proof will never use a hull-side `KFacts`": INFERRED.
   The planned chain is documented, not delivered. This claim sets no
   verdict on its own; negative 1 carries the verdict.
3. "The stage-valued record from `[LJ-1.80]` is the exact value the
   chain consumes": INFERRED FALSE. The chain is uninstantiated. The
   consumed bound is the witness `K'`, not `Lset lam`.
4. "`levelIn` and `cover` are discharged by the stage `KFacts`":
   MEASURED FALSE. They remain parameters at
   `src/L/BoundedSubset.lagda.md:916-917`.
5. "The hull is the carrier of the transfers, never the bound":
   MEASURED. The statements read at `src/ProbeLJ152A.agda:48-51,
   58-61,78-81` quantify over `K : S` as a member of the env.

## 6. DEVLIN'S BOUNDING SET

Devlin's bounding set is `K(u)`: the union of the finite sequences of
members of `Fml ∪ {v_i | i ∈ ω} ∪ u`, the finite sequences of finite
sequences of those, and the finite sequences of finite subsets of the
variables. It is a member of the carrier where the level-hood formula
is evaluated. It is neither a stage nor the hull.

## 7. DD4

The site is generic in structure. The record `KFacts` and the six
masters are shared. Both towers evaluate the bounded level formulas at
their own level bounds. Neither tower's condensation needs a hull-side
`KFacts`.

The closure content is per-tower. The L tower supplies it from
`pr∈Lset-suc`, `Lset-mono`, `layer-trans` and `succλ`. The J tower
supplies its own stage closure, exactly as it supplies its own
`levelIn` and `cover`. This matches the `[LJ-1.52]` DD4 split: the
adequacy machinery is template content, and the level-hood statements
are Def-side.

## 8. TREE STATE

The working tree is byte-identical to its start at `45a395a`. No master
was edited. No probe was created. No Agda process was run. The `git
status` at start and finish: clean.

Load average during this dispatch: 4.37 / 8.03 / 16.84 (1, 5, 15
minutes), four users. The machine was NOT quiet. No absolute timing
figure appears in this report; every figure is a line number or a
membership statement.

## 9. ARCHIVE USED

- `src/ProbeLJ180A.agda`, read WHOLE. TOOK the stage-valued `kfacts`
  (`:186-226`), the `StageKFacts` parameterization (`:32-38`), and the
  field suppliers (`pair-in-lam`, `layer-trans`, `Lset-mono`).
- `_build/lj-1.80-report.md`, read WHOLE. TOOK section 2, the hull
  wall (no `isL` certificate for `M` or `πX`).
- `src/L/BoundedSubset.lagda.md`, read the mandated regions and the
  chain: `:74-356` (`LevelHood`, `IsoInv`, `DownReflect`), `:650-905`
  (`HullElemDown`, `AtHullInstance`, `LevelHood0`), `:880-1033`
  (`HullStage.Condense`), `:1144-1234` (`UnionKit`), `:1345-1423`
  (`Devlin55`, `BoundedSubsetAt`, `Co`), `:1500-1620` (`elem-down`,
  `x∈Lκ`). TOOK `levelIn`/`cover` at `:916-917`, consumers at
  `:966,:1001,:1019,:1606`, `M` at `:911`, `matrix` at `:847-849`,
  `elem-down` at `:1568`.
- `_build/lj-1.52-report.md`, read WHOLE. TOOK the `Adeq` form and
  the levelIn chain (`:24-36`, `:68-86`), the graph agreement
  decomposition (`:2.2`), the DD4 split (`:170-177`).
- `_build/lj-1.51-report.md`, read WHOLE. TOOK the survivor ledger and
  the `levelIn`/`cover` term structures.
- `_build/lj-1.49-report.md`, read WHOLE. TOOK the residue: the
  twelve-row agreement re-based at the hull's carrier and the
  collapse-of-the-level (`:4`).
- `_build/lj-1.79-report.md`, read WHOLE. TOOK the guarded `KFacts`
  forms and the supply points.
- `_build/diag-twelve-row-math.md`, read the verdict summary and
  section 3. TOOK: `TwelveAgree` is Devlin II.2.4 unrolled, and the
  closure facts are hull-relativized in Devlin.
- `_build/lj-1.54-report.md`, read WHOLE. TOOK the slot-convention
  wall (the twelve agreements do not instantiate at the consumer's
  frame).
- `_build/lj-1.59-report.md`, read WHOLE. TOOK the direction answer:
  `Adeq m` production is machine-to-story.
- `_build/lj-1.62-report.md`, read WHOLE. TOOK the chain placement
  history and the `KFacts` bundle's content class.
- `dev/LESSONS.md`, read C-38 (`:3427-3520`), C-35 (`:3200-3242`),
  C-36 (`:3284-3332`), D-30 (`:3332-3380`), whole. TOOK the discharge
  standard and the price-what-the-consumer-needs rule.
- `archive/rud-route/`, SHAPE only. Took nothing. WHY NOT more:
  `[LJ-1.11]` ruled the retired route's condensation target classically
  false, and the brief forbids taking a price from it.

## 10. LITERATURE USED

- `dev/literature/devlin-II5.md` Step C (`:209-257`), read WHOLE.
  TOOK the Σ₁ level-hood with the Σ₀ matrix, the transfer along
  elementarity and the collapse, and the bound `K(u)`.
- `_build/literature/dev2.txt:1372-1385`, read. TOOK Devlin 5.5: the
  hull of `L_α ∪ {x}`, the collapse `π : M ≅ L_γ`, and the fixing of
  `L_α ∪ {x}`.
- `_build/literature/dev2.txt:593-630`, read. TOOK the bounding set
  construction: `K(u)` is the finite-sequence union built from
  `Fml ∪ Vbl ∪ u`.
- The errata were NOT re-checked. WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered.

## 11. GATES

- `scripts/check-fences.py --check`: clean, 87 masters.
- `scripts/lint-prose.py --check` on this report: exit 0.
- `scripts/lint-agda.py --check`: nothing to check. No Agda file was
  touched.
- No `make check`. No commit, no push. Tree byte-identical.
