# LJ-1.666 report: the slot commitment the satisfaction half cannot meet

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-666/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`.

TARGET: build ONE term in `agents/tasks/LJ-1-666/Probe666.agda`:

    sat-at-level : SatAtLevel φ₀

where `φ₀` is chosen by the coder, arity 2, parameter-free. Nothing lands
in `src/`.

The brief's GO branch is at the CHAPTER's levelhood (bounded matrix, Δ₀,
arity 4). The brief forbids pinning at `LevelHood0`: "twelve numeral
columns cannot come from five committed slots." The literature file says
level-hood should have arity 2 with the free pair `(value, ordinal)`.

## VERDICT

**NO-GO on `sat-at-level`.** The obligation is not inhabited for any
arity-2, parameter-free `φ₀` built from the chapter's bounded matrix. The
witness meter reads `1 UNRESOLVED of 1, 0.98 s, probe_red=False`
(`runs/meter-obligation.out`). The probe is green and carries no hole
(`runs/probe-2.out`, EXIT=0).

The stated NO-GO is
`agents/tasks/LJ-1-666/review-of-sat-at-level.md`. The commitment that
cannot be met is the **fourteen environment slots** that the `KFacts`
record requires for the bounded-unbounded bridge, against the **two free
slots** that the arity-2 satisfaction obligation provides. The gap is
structural, not parametric: it is in the bounded graph machinery itself,
not in `LevelHood0`'s parameterization.

**This is not a refutation of the level-hood's satisfaction.** The bounded
matrix IS satisfied at the stage. What is measured is that the tree cannot
close it: the only bridge between the bounded and unbounded graphs
(`LeafAgree`/`extAtB→extAt`) requires the `KFacts` at fourteen slots.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.662]` delivered `SatAtLevel` as a TYPE, not as a term. Its report
is a STOP at the obligation
(`agents/tasks/LJ-1-662/lj-1.662-report.md:6-7`), with the named residue
`SatAtLevel φ₀` at `Probe662.agda:284`. Section 7 of that report names the
slot count: "twelve numeral columns cannot come from five committed slots"
and the third option: "A formula that SAYS its own columns are the
numerals is the third option and nobody has priced it."

I took the type. I priced the third option. I did not build a term of a
type the predecessor named UNBUILT: the predecessor named it ABSENT (the
probe is green, the term is missing), which is the same thing.

`[LJ-1.661]` closed NO-GO on the SOUNDNESS half
(`agents/tasks/LJ-1-661/lj-1.661-report.md:3-6`): `hoodsound-at-levelhood0`
cannot be built because no pin has both inputs (`Δ₀ φ₀` and
`LsetOnlyAt φ₀`). That NO-GO is about the soundness side. This task is the
satisfaction side. The two are independent: the satisfaction side is
blocked by the KFacts slot count, the soundness side by the shape
mismatch at the `Lset-only` pin.

## 2. THE THREE WALLS, MEASURED

### Wall 1: The KFacts slot count

| fact | site | value |
|---|---|---|
| `KFacts` record definition | `src/L/Condensation.lagda.md:6079` | 12 numeral + 1 bound + 1 carrier = 14 slots |
| `KValue.Kenv` | `src/L/Condensation.lagda.md:7389` | `S ^ 14` |
| `KValue.facts` | `src/L/Condensation.lagda.md:7411` | the sole `KFacts` value |
| `LevelHood0.matrix` arity | `src/L/BoundedSubset.lagda.md:849` | 4 |
| `LevelHood0` N-parameters | `src/L/BoundedSubset.lagda.md:841` | `Fin 5` (at most 5 slots) |
| `LevelHood0` M-parameters | `src/L/BoundedSubset.lagda.md:842` | `Fin 7` (at most 7 slots) |
| `KFacts` numeral columns | `src/L/Condensation.lagda.md:7397-7408` | 12 distinct `Fin 14` indices |

Five does not reach twelve. Seven does not reach twelve. Fourteen is the
environment arity of the sole `KFacts` value.

### Wall 2: The bounded-unbounded gap

| fact | site |
|---|---|
| `graphBndAt` definition | `src/L/Condensation.lagda.md:2492` |
| `graphBndAt` occurrences in src/ | 6 lines: `Condensation:2492,2493,2495,2496`; `BoundedSubset:111,115` |
| `Lset-only` (unbounded, class carrier) | `src/L/Hierarchy.lagda.md:334-335` |
| `Lset-defines` (unbounded, class carrier) | `src/L/Hierarchy.lagda.md:646` |
| `LeafAgree` (the bridge) | `src/L/Condensation.lagda.md:7224` |
| `extAtB→extAt` (the lift) | `src/L/Condensation.lagda.md:2510-2517` |
| `extAtB→extAt` requires `KFacts` | `src/L/Condensation.lagda.md:2510` (the `fwd`/`bwd` arguments are `KFacts`-indexed) |

None of the six `graphBndAt` lines provides a stage-satisfaction lemma.
The delivered adequacy is for the UNBOUNDED graph at the CLASS CARRIER.
The only bridge requires the `KFacts` at fourteen slots.

### Wall 3: The third option does not create slots

The 662 report's third option: "A formula that SAYS its own columns are
the numerals." The tag equations are:

    fst (lookup i env) ≡ fst (numeralL k)

for twelve values of `i : Fin 14`. At arity 2, `lookup i env` is defined
only for `i < 2`. Lookups 2 through 13 are undefined. **Folding the
equations into the formula body does not create the missing slots.**

## 3. THE STATEMENT ABOUT THE CHAPTER

The 662 count was about `LevelHood0`'s parameterization. This review
sharpens it: **the commitment is in the bounded graph machinery itself.**
The `graphBndAt` formula requires the `KFacts` for its satisfaction
bridge. The `KFacts` requires fourteen environment slots. This is true of
ANY instantiation of the bounded graph, at ANY arity.

`LevelHood {n}` for `n ≥ 14` has room for the columns (Fin (5 + n)
parameters address 5 + n ≥ 19 slots). But its matrix is at arity `4 + n ≥
18`. Closing the surplus by `∃̇` to return to arity 2 loses the tag
equations that the `KFacts` asserts. **The chapter's bounded graph and the
chapter's arity-2 satisfaction obligation are in structural tension.**

## 4. W3, ANSWERED

**Question:** the `φ₀` itself, estimated 90 to 200 lines.
**Answer:** the `φ₀` is the chapter's `hood2`
(`agents/tasks/LJ-1-662/Probe662.agda:110-111`), already built and sealed
in the predecessor. It is arity 2, parameter-free, and constant-free
(`count-hood2 = refl`, `Probe662.agda:119`). The formula is not the
problem. The satisfaction is. The 90 to 200 line estimate was for the
formula construction; the satisfaction proof is a different object and it
is not 90 to 200 lines. It is the `KFacts`-indexed leaf agreement at
fourteen slots, which is the `LeafAgree` module and its consumers, a
different price.

## 5. RUNS

Caliber `-A64m -I0 -M2g`, set on the pane by the program and untouched
here. ONE Agda process at a time, from the repository root.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---:|
| `runs/probe-1.out` | first attempt, `_-_` not in scope | — | — | 0 (warning) + error |
| `runs/probe-2.out` | final, green | 1.2 | not measured | 0 |
| `runs/meter-obligation.out` | witness meter, one obligation | 0.98 | not taken | 42 |

The probe is 155 lines, of which 38 are non-blank non-comment code lines.
The brief's W3 estimate was 90 to 200 lines for the `φ₀`. The delivered
probe is smaller because the `φ₀` is already built in the predecessor and
the probe states the slot count facts, not the formula.

The witness meter: `1 UNRESOLVED of 1, 0.98 s, probe_red=False`. The
obligation is ABSENT and the probe is GREEN: that is what
`probe_red=False` beside a `missing` row means.

This worktree has no `.venv`. The meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0.
Nothing landed in `src/`.

## 6. WHAT THE SHAPE RESISTED

- **What it cost.** 38 code lines, one green run at 1.2 s, no heap event.
- **What the shape resisted.** The shape did not resist the probe. The
  probe is a measurement, not a proof. The resistance is in the
  satisfaction: the `KFacts` slot count is a structural fact about the
  bounded graph machinery, and no probe can change it.
- **What I had to weaken.** Nothing. The obligation is absent, not
  weakened.
- **What I could not close.** `sat-at-level : SatAtLevel φ₀` for any
  arity-2, parameter-free `φ₀` built from the chapter's bounded matrix.
  The three walls are measured above.

## 7. WHAT THE NEXT BRIEF NEEDS

1. **A satisfaction lemma for the bounded graph at the stage, that does
   NOT go through `KFacts`.** No such lemma exists in `src/`. A new
   module would need to construct the witnesses (the codes, the shapes,
   the clauses) in the stage and prove the bounded formulas hold,
   without the `LeafAgree` bridge. This is the chapter's own named
   residue ("the level-hood instantiation at the hull",
   `src/L/BoundedSubset.lagda.md:901-902`).
2. **OR: a `KFacts` value at arity 2.** Redefine the `KFacts` record to
   carry its twelve numeral columns as parameters rather than as
   environment lookups. This changes the record's shape and every
   consumer.
3. **OR: the unbounded graph at the stage.** A `φ₀` that is the
   UNBOUNDED `LsetGraphAt` (Σ₁, arity 2) rather than the bounded matrix.
   The chapter delivers `Lset-defines` for the unbounded graph at the
   CLASS CARRIER. The stage satisfaction would require the graph's
   witnesses to be in the stage, which is a different proof. This route
   is also not delivered in the tree.
4. **OR: a different `φ₀`.** A formula that is NOT the level-hood at
   all, but whose satisfaction IS provable at the stage, and whose
   `HoodSoundP` is also meaningful. The constraint is that the formula
   must pin the value to `Lset γ` in a way the soundness half can read.

## 8. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Done in section 2 and the review.
  The recorded residue is `SatAtLevel φ₀`. Its truth at the intended
  generality: the bounded matrix IS true (the witnesses exist, the
  formula holds), but the TREE cannot close the stage-satisfaction term
  because the delivered bridge requires fourteen environment slots and
  the arity-2 formula provides two. The corrected target is stated in
  the review, section 3.
- **C-22** (`dev/LESSONS.md:2307`). The report was written as a
  skeleton before the probe ran and filled as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Did not bind. No type in the probe
  names a stage presentation. The probe states natural number constants
  and no formula.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). The review's section 4 is the sweep.
  The refutation measures one site (the `SatAtLevel` obligation at the
  bounded matrix). The sweep searched `graphBndAt`, `KFacts` and
  `LeafAgree` over `src/`. Count: 1.

## 9. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `clean (10318 tracked files, no
  probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

I did not run `make check`. I did not commit and I did not push.

## ARCHIVE USED

- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  The archived process document. This task measures a slot count and does
  not consult dispatch process.
- **`archive/dev/DD-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`.
  A history. The live status is `dev/pod/screen.toml`.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# ARCHIVED 2026-08-20`. A history.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# STATUS-archived: the goal table of the internalization route`.
  The internalization route is not this measurement.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read beyond its first
  line. `:1` reads `# Archived task index: the \`L3.32-T\` series`. A history.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  The free pair is `(value, ordinal)`, arity 2. This confirms the
  satisfaction obligation's arity.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read
  beyond its first line. `:1` reads `# Glossary review: the 119 pre-protocol entries`.
  No naming question arose.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Devlin errata: documented error classes`.
  This task certifies no leaf as bounded.
- **`dev/literature/primary-sources.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Primary sources, second round`. No source was
  missing.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read beyond its
  first line. `:1` reads `# Bibliography for the rud route`. No citation
  was added.
