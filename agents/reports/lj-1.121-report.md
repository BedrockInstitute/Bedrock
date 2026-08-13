# LJ-1.121: supply levelIn and cover at the site

tier: codex (default)

## STATUS

COMPLETE, with an honest boundary. **Neither is refutable. Neither is
supplied.** The two hypotheses are the two halves of Devlin 5.2 part
(i), the condensation level-hood transfer. The refutation attempt
found no term and no counterexample. The supply attempt walls on the
one fact the tree does not deliver: the hull is closed under the level
construction at the ordinals it contains. That fact is the `[LJ-1.12]`
crossing, priced at 2.8 to 3.3 thousand lines and not yet built. The
site itself is reached cleanly: all fifteen telescope values close and
the body elaborates through `code-inj` (`src/ProbeLJ1119A.agda:38-79`,
GREEN). `levelIn` and `cover` are the first hypotheses nothing
supplies, and there is no hypothesis after them: the `Co` body closes
to `theorem : ⟨ x ∈ˢ Lset κ ⟩` once they are given. No commit, no push.
One Agda process at a time, under the C-12 cap.

## 0. THE VERDICT

| question | answer | where |
|---|---|---|
| either refutable? | NO. Neither. | section 2 |
| `levelIn` supplied? | NOT SUPPLIED | section 3 |
| `cover` supplied? | NOT SUPPLIED | section 3 |
| stated more generally than used? | NO. Neither. | section 5 |
| next unsupplied hypothesis | none after these two | section 4 |

The abort criterion fires on the middle row. Both are NOT SUPPLIED, so
I report both with the terms I could not write (C-36).

## 1. WHAT EACH ASSERTS

The two, quoted from the source at `src/L/BoundedSubset.lagda.md:1409-1411`:

```agda
(levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩)
(cover : (y : S) → ⟨ y ∈ˢ HS.M ⟩
       → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩) ∥₁)
```

`HS.M` is the hull carrier, `HS.C.π` is its Mostowski collapse, and
`HS.C.πX` is the collapse image. The readings I verified from the
source:

- `levelIn` asserts: the collapse image is closed under the level
  construction at the ordinals it contains. For every ordinal `δ` in
  `πX`, the level `Lset δ` is again in `πX`. This is the forward half
  of Devlin 5.2 part (i), `Lset β ⊆ πX`.
- `cover` asserts: every collapsed member lands in a level whose index
  is an ordinal of the collapse. For every hull member `y`, there is an
  ordinal `γ` in `πX` with `π y ∈ Lset γ`. This is the reverse half,
  `πX ⊆ ⋃_{γ∈πX∩On} Lset γ`.

These are the brief's own readings, and I verified them against the two
consumers. `levelIn` is used at `src/L/BoundedSubset.lagda.md:1020` in
`Condense.Lβ⊆πX`. `cover` is used at `:967` (`β-succ`), `:1002`
(`πX⊆Lβ`), and `:1606` (`x∈Lκ`). All four uses match the readings. This
verification is **MEASURED**.

One correction to the brief, read from the source. The pair at
`:917-919` is in `Condense`, which is nested inside `HullStage`
(`:903-921`), not in `HullExt`. `HullExt` is at `:1235` and takes no
such parameters; it proves `hullExt : isExt M`. So the pair binds in
two places that are `Condense`'s parameters (`:917-919`) and `Co`'s
restatement of them (`:1409-1411`, passed to `Condense` at `:1414`).
This is **MEASURED** by reading both sites.

## 2. REFUTATION ATTEMPT

First the checker, as the brief ordered. `check-unbound-hyp.py` on the
master reports clean (`scripts/check-unbound-hyp.py
src/L/BoundedSubset.lagda.md`, exit 0). The checker flags exactly the
empty-K-closure shape that C-38 records: a hypothesis that concludes a
membership for a set no premise constrains. It does **not** flag
`levelIn` or `cover`. That is **MEASURED**: neither has the shape of
the eleven empty hypotheses.

Then the ProbeLJ197A shape. That probe refutes by varying a frame. It
picks a frame where a universally quantified set is unconstrained and
derives a membership cycle from regularity. That shape does not apply
here, and the reason is structural. `levelIn` and `cover` have no free
frame: the site's `HS.M` and `HS.C.πX` are fixed objects. Both
statements are guarded by real premises. `levelIn` needs `IsOrd δ` and
`δ ∈ πX`. `cover` needs `y ∈ M`. Their conclusions are positive
memberships about specific sets, `Lset δ` and `π y`. No delivered
regularity lemma (`∈-irrefl`, the no-cycle lemmas) fires on a positive,
premise-guarded membership about a specific set. A refutation would be
a counterexample: an ordinal `δ` of the collapse whose level leaves the
collapse, or a hull member whose collapse value escapes every level
below the collapse's ordinals. Both would contradict Devlin 5.2 part
(i). I wrote the refutation types (`RefuteLevelIn`, `RefuteCover`) and
found no term for either (`src/ProbeLJ1121A.agda:72-77`, GREEN). The
claim that no term exists is **INFERRED**: a refutation search that
finds nothing proves no absence. The claim that the shape differs from
the eleven empty hypotheses is **MEASURED** by the checker and by
reading the premises.

Conclusion: neither is refutable. Both survive, so the task proceeds to
the supply.

## 3. SUPPLY AT THE SITE

The site is the `[LJ-1.119]` entry (`src/ProbeLJ1119A.agda:38-56`),
where `α = ω`, `x = ∅`, and `κ` is the Hartogs cardinal. There the
hull carrier and the collapse are concrete. The probe restates the two
targets at that site (`src/ProbeLJ1121A.agda:44-50`) and they elaborate
as types.

**`levelIn`: NOT SUPPLIED.** The supply reduces to two facts, and both
are the level-hood transfer. The reduction is machine-checked in
`src/ProbeLJ1121A.agda:88-98` (GREEN):

```agda
module Supply
  (hullLevel : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BA.HS.M ⟩)
  (piFixesLevel : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BA.HS.C.πX ⟩ → BA.HS.C.π (Lset δ) ≡ Lset δ)
  where
  levelIn δ oδ δ∈πX = subst (λ w → ⟨ w ∈ˢ BA.HS.C.πX ⟩)
    (piFixesLevel δ oδ δ∈πX)
    (BA.HS.C.πX-intro (Lset δ) (hullLevel δ oδ δ∈πX))
```

The two parameters name the wall. `hullLevel` says the hull contains
the level at each of its ordinals. `piFixesLevel` says the collapse
fixes that level. Both are the transfer of the internalized level-hood
statement into the hull, which is Step C of the condensation argument
(`dev/literature/devlin-II5.md` section 2.3). Neither is delivered by
any master. A search for a delivered lemma that supplies either finds
only `Hull⊆L` (`src/L/Hull.lagda.md:330`), which is the wrong direction:
it says every hull member lies in the stage `Lset lam`, not that
`Lset δ` lies in the hull. No master delivers the reverse fact. This
negative is **MEASURED** by the grep, and the wall itself is
**MEASURED** by the GREEN reduction that stops exactly at the two named
parameters.

**`cover`: NOT SUPPLIED.** It is the covering direction of the same
transfer, the (j)-line of Devlin 5.2 (`devlin-II5.md` section 1.2):
every hull member's collapse value lies below an ordinal level of the
collapse. The probe states the missing fact as a type to name the wall
(`src/ProbeLJ1121A.agda:104-108`). Writing it needs the same level-hood
transfer as `hullLevel`, in the covering direction. No master delivers
it. This negative is **MEASURED** in the same way as `levelIn`.

The one fact behind all of this is the `[LJ-1.12]` crossing, priced at
2.8 to 3.3 thousand naive non-blank in-fence lines
(`_build/lj-1.12-report.md:8-12`), and it is not built. So the terms I
could not write are `hullLevel`, `piFixesLevel`, and `CoverTransfer`,
and the reason is the missing crossing, not a local defect.

## 4. HOW FAR / NEXT UNSUPPLIED HYPOTHESIS

The entry reaches `Co`'s telescope. All fifteen `BoundedSubsetAt`
values close, and the body elaborates through `code-inj`
(`src/ProbeLJ1119A.agda:38-79`, GREEN). The first hypotheses nothing
supplies are `levelIn` and `cover`, at `src/L/BoundedSubset.lagda.md:1409-1411`.
This is **MEASURED**.

There is no hypothesis after them. `Co`'s telescope holds only
`levelIn` and `cover` (`:1409-1411`). Every later name in the body is a
definition, not a hypothesis, down to `theorem : ⟨ x ∈ˢ Lset κ ⟩`
(`:1621`). So once these two are supplied, the body closes. This is
**MEASURED** by reading `:1409-1621`.

In reduced form, the next unsupplied hypotheses are the three named in
section 3: `hullLevel`, `piFixesLevel`, and `CoverTransfer`. They are
all one content: the level-hood transfer into the hull.

## 5. GENERALITY CHECK

The brief asked whether the two are the same shape as `Devlin55`'s old
parameters, stated more generally than the site uses them. The answer
is no. The `[LJ-1.117]` and `[LJ-1.119]` defects were whole-function
parameters over every `(α, x)`. `levelIn` and `cover` are not. They are
stated at the hull's own objects, `HS.C.πX` and `HS.M`, which are
already fixed inside `BoundedSubsetAt`. They are as narrow as the module
structure allows, and their consumers use them at exactly this shape.
So there is no restriction available of the D-30 kind. This check is
**MEASURED** by reading the two statements against their consumers.

## 6. check-unbound-hyp

Master: `scripts/check-unbound-hyp.py src/L/BoundedSubset.lagda.md`
reports clean, exit 0. It flags nothing, so it flags neither `levelIn`
nor `cover`. Probe: `scripts/check-unbound-hyp.py src/ProbeLJ1121A.agda`
reports clean, exit 0. Both are **MEASURED**. The checker's clean
report is not a proof that the telescopes are inhabited; the script
says so itself (`scripts/check-unbound-hyp.py:36-39`). It means only
that the two are not the empty-K-closure shape.

## 7. THE C-39 SECTION

No prohibition in this brief blocked a route I could see. Audited one
by one:

- **Do not weaken either statement.** Respected. I did not weaken. I
  reported them as NOT SUPPLIED.
- **Do not add a hypothesis to the site.** Respected. The probe's
  `Supply` module names the missing facts as parameters, but that is a
  probe, not the site, and it names the wall rather than discharging
  it. No master changed.
- **Do not edit any master.** Respected. `git status --short` is empty;
  only the probe (ignored) and this report (under `_build/`) exist.
- **Do not write a probe as `.lagda.md`.** Respected. The probe is
  `src/ProbeLJ1121A.agda`.
- **Never `src/Everything.lagda.md`.** Not touched.
- **Do not raise the heap cap.** Respected. Every check ran one process
  at `GHCRTS="-A64m -I0 -M8g"`.
- **Do not run `make check`.** Not run.

The one door worth naming: the reduction in section 3 shows the supply
is one content away, the level-hood transfer. That route is not blocked
by this brief. It is blocked by the tree, because the `[LJ-1.12]`
crossing is not built. The next dispatch that can move is the crossing
itself, not a further restriction of these two.

## 8. NEGATIVES AND THEIR STATUS

1. "`levelIn` is refutable": **MEASURED FALSE** as a search result. No
   refutation term exists in the probe, and the checker does not flag
   it. "It is not refutable at all" is **INFERRED**, because no search
   proves absence.
2. "`cover` is refutable": **MEASURED FALSE** as a search result, same
   classification.
3. "`levelIn` is supplied at the site": **MEASURED FALSE**. The probe
   walls at `hullLevel` and `piFixesLevel`, and no master supplies them.
4. "`cover` is supplied at the site": **MEASURED FALSE**. The probe
   names `CoverTransfer` as the missing fact, and no master supplies
   it.
5. "Either is stated more generally than used": **MEASURED FALSE**.
   Both are at the hull's own objects.
6. "The two are the same shape as the eleven empty hypotheses":
   **MEASURED FALSE**. The checker flags those eleven and not these.
7. "There is a hypothesis after these two": **MEASURED FALSE**. The
   `Co` body closes to `theorem` after them.
8. "The J tower inherits the two unchanged": **INFERRED**, see the DD4
   answer. No J tower exists in this tree.

## 9. DD4

The brief asks whether the J tower inherits `levelIn` and `cover`
unchanged, and it says the two are about the hull and the collapse, not
about definability. The first half of that is right; the second half is
not. The hull and the collapse are shared, either-tower machinery, and
the two statements name only hull and collapse objects. But SUPPLYING
them is definability content, and the literature already measured the
split. The transfer needs the level construction to be definable in the
hull's language. That is the level-hood certificate, and it is per-tower
content (`dev/literature/devlin-II5.md` section 4, rows C1 and C2). The
literal statements name `Lset`, the Def tower's level. A J tower would
state the same shape about its own level construction, the J-level
certificate, and would need its own Step C, the S-sequence and the
uniform Σ₁-ness (SZ 1.10 and 1.16, in
`dev/literature/j-hierarchy.md`). So the shape is shared and maximally
generic; the instance that mentions `Lset` is Def-tower content. This
is **INFERRED** on the J side, because no J tower exists in this tree,
and **MEASURED** on the Def side, because the statements literally name
`Lset`. The probe is tower-generic in the same sense: it instantiates
the shared `BoundedSubsetAt` at the site, and a J consumer would
instantiate the same module with its own level certificate.

## 10. GATES

- `src/ProbeLJ1121A.agda`: GREEN, 2.96 s wall, 2.62 s user, one process
  at `GHCRTS="-A64m -I0 -M8g"`. 118 lines whole, 101 non-blank. No
  `postulate`, no `TERMINATING`, no holes.
- `scripts/check-unbound-hyp.py` on the master: clean, exit 0. On the
  probe: clean, exit 0.
- `scripts/check-fences.py --check`: clean, 87 masters.
- `scripts/lint-prose.py --check` on the probe: exit 0.
- `scripts/lint-agda.py --check` on the probe: exit 0.
- `scripts/check-probes.py --check`: clean.
- `scripts/ledger.py --brief`: standing 28,432 lines over 85 masters.
- `make check` not run (forbidden).
- Load averages: 6.92 / 5.54 / 5.56 at the probe check; 7.14 / 5.87 /
  5.69 at the end. Four users.
- Working tree: `git status --short` empty. HEAD `f941eea` unchanged.
  No commit, no push. No Agda process left running.

## 11. ARCHIVE USED

- `_build/lj-1.119-report.md`, read WHOLE. Took the site entry, the
  fifteen values, and the statement that `levelIn` and `cover` are the
  first unsupplied hypotheses at `:1409-1410`.
- `src/ProbeLJ1119A.agda`, read WHOLE. Took `BA`, the site entry, and
  the `C0` boundary module.
- `_build/lj-1.118-report.md` and `src/ProbeLJ1118A.agda`, read the
  site block and `AbsorbsIn`. Took `site-inj` and the site's `α = ω`,
  `x = ∅`.
- `_build/lj-1.117-report.md`, read WHOLE. Took the restriction pattern
  and checked the two against it (section 5).
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda:1186-1233`, read
  the site block. Took the site values.
- `src/L/BoundedSubset.lagda.md:890-1050` and `:1235-1621`, read. Took
  `Condense`'s parameters (`:917-919`), `Co`'s parameters
  (`:1409-1411`), the four uses of the two (`:967`, `:1002`, `:1020`,
  `:1606`), and the closing `theorem` (`:1621`).
- `src/L/Hull.lagda.md:148-430`, read. Took `AtStage`, `Hull`,
  `hull-closed`, `hull-member`.
- `src/V/Collapse.lagda.md`, read WHOLE. Took `πX-intro`, `πX-member`,
  `πX-trans`, `fixes`.
- `src/L/Hierarchy.lagda.md:320-440`, read. Took `Lset-only`,
  `Lset-defines`, `graph-table` (the internalized level-hood graph).
- `src/ProbeLJ197A.agda`, read WHOLE. Took the refutation shape and
  confirmed it does not apply.
- `dev/LESSONS.md`, read WHOLE: C-38 (`:3427`), C-39 (`:3521`), C-40
  (`:3602`), C-35 (`:3200`), C-36 (`:3284`), C-37 (`:3381`), D-30
  (`:3332`), D-10 (`:1316`), D-29 (`:3242`), D-8 (`:1377`), D-1
  (`:1038`), D-26 (`:1676`), P-x (`:3564`), P-c (`:71`), P-h (`:174`),
  P-i (`:203`), P-k (`:2401`), P-m (`:2460`), P-n (`:2483`), P-o
  (`:2509`), P-q (`:2633`), P-t (`:2601`), P-u (`:2908`), P-v
  (`:3037`), P-w (`:3094`), R-35 (`:782`), R-36 (`:808`), R-38
  (`:829`), R-40 (`:929`), C-31 (`:1855`), C-32 (`:2947`), C-33
  (`:2987`), C-34 (`:3171`), and the `--for build` bundle via
  `scripts/rules.py`. Took C-38's supply standard, C-36's write-the-term
  rule, D-30's consumer-audit rule.

## 12. LITERATURE (DD18)

Two lines on how Devlin 5.5 gets the hull closed under stages, from
`dev/literature/devlin-II5.md`. 5.5 itself does not prove the closure;
it calls condensation 5.2, which is where the closure is proved
(`devlin-II5.md` section 1.2 and 1.5). 5.2 transfers the level-hood
statement "v = L_γ", which is Σ₁ with a Σ₀ matrix by Devlin 2.7, along
Σ₁-elementarity and the collapse, giving `L_γ ∈ M` for every collapse
ordinal γ (`dev2.txt:1186-1240`); the reverse transfer gives
`M ⊆ ⋃_{γ<β} L_γ` (`dev2.txt:1245-1290`). Those two transfers are
exactly `levelIn` and `cover`.
