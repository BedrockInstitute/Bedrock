# [LJ-1.618] report: the pairing at one alpha, and the circle that reaches it

Head slot: coder. Machine: shared. Caliber on this pane: GHCRTS
`[-A64m -I0 -M2g]`, set by the program. I did not set it. One Agda
process at a time, every run capped and recorded under `runs/`.

## VERDICT

**NO-GO, stated.** The obligation `pairing-at-alpha` is not inhabited
by the tree, and the probe measures that the gap is ONE named residue:
the untruncation of the least-cardinal injection. The probe proves
`Inj-extract → Obligation`
(`agents/tasks/LJ-1-618/Probe618.agda:210-211`), green, and no term in
the tree inhabits `Inj-extract`
(`agents/tasks/LJ-1-618/Probe618.agda:151-154`). The full statement of
the stop is `agents/tasks/LJ-1-618/review-of-pairing-at-alpha.md`.
Nothing was postulated. Nothing landed in `src/`. Nothing was committed
and nothing was pushed.

## WHAT THE TREE ALREADY HAS

The brief's Σ payload is already a named type former: `sq`
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). Every candidate the
search found, marked by whether it reaches ONE α:

| candidate | file:line | reaches one α? | honest? |
|---|---|---|---|
| `squareω : sq ω` | `src/L/InjChain.lagda.md:184-185` | YES, at ω only | YES, no truncation |
| `via-col-square : (α : S) → Init α → sq α` | `src/L/Ordinal/SquareLaw.lagda.md:960-961` | YES, at every `Init` ordinal, one at a time | YES, no truncation |
| `sq` band parameter of `L.StageCardinal` | `src/L/StageCardinal.lagda.md:17-20` | NO, it is the uniform supply over `δ ∈ˢ sucV α₀` | it is a parameter, not a term |
| consumer's telescope copy | `src/L/BoundedSubset.lagda.md:1388-1391` | NO, same band shape | same |
| `SqFam` restatement | `src/L/StageBound.lagda.md:36-40` | NO, band shape, type only | not inhabited |
| `sq-trunc-closed` | `src/L/SquareLawClosed.lagda.md:325-328` | NO, truncated: `∥ sq δ ∥₁` at every δ of the band | truncated in the type |
| `via-col-truncated` | `src/L/Ordinal/SquareLaw.lagda.md:963-964` | YES at `Init`, but truncated | truncated |

So the tree holds the honest fiber at ω and at every initial ordinal,
and the truncated fiber everywhere in the band. No term in the tree
holds the honest fiber at a non-initial, non-ω infinite ordinal. The
first two rows are re-ascribed at the brief's own Σ, TYPE ONLY, in
`agents/tasks/LJ-1-618/runs/W3.agda:62-78`, and that file was written
FIRST and typechecked ALONE, green in 1.51 s under a 120 s cap
(`runs/w3-3.out`; the two earlier runs `w3-1.out` and `w3-2.out`
record the two scope fixes it took, exit 42 each).

## DOES THE CIRCLE REACH THE SITE GRAIN

**YES.** At the site `src/L/BoundedSubset.lagda.md:1410` the band
parameter is spent at one α, but the honest fiber at that α, for every
infinite α, needs the least-cardinal descent
(`src/L/SquareLawClosed.lagda.md:314-318`), whose one missing
ingredient is the payload of `κ-inj`
(`src/L/Cardinal.lagda.md:133-134`), a truncation the search builds in
by necessity because `leastOf` takes an hProp
(`src/L/Cardinal.lagda.md:66-67`). The circle is the same object
`[LJ-1.605]` measured at the band
(`agents/tasks/LJ-1-605/review-of-uniform-pairing.md:96-98`), seen one
grain down: the two grains differ by uniformity only, and the missing
ingredient is the same at both.

## WHAT I BUILT AND WHAT IT COST

`agents/tasks/LJ-1-618/Probe618.agda`, 242 lines, five sections:

- Section 0: `PairingAt`, the brief's Σ verbatim, and `PairingAt ≡ sq`
  by `refl` (`:85-86`). `Obligation`, the brief's full Π, as a type
  (`:90-91`). No term of the file carries the brief's name
  `pairing-at-alpha`, per the NO-GO idiom of `[LJ-1.605]`.
- Section 1: the coverage map, `at-ω` and `at-init` re-ascribed
  (`:102-115`), and `Band` for contrast (`:122-123`).
- Section 2: what the tree delivers today, `trunc-at-band`
  (`:131-133`) and the truncated injection `κ-inj-at` (`:139-141`).
- Section 3: `Inj-extract`, type only, not inhabited (`:151-154`), and
  `pairing-from-extract : Inj-extract → Obligation` (`:210-211`). This
  is the tree's own closed recursion
  (`src/L/SquareLawClosed.lagda.md:280-323`) with the motive
  untruncated. Three cases: ω spends `squareω`; the own-least-cardinal
  case spends `via-col-square` at an `Init` served by the truncated
  hypothesis, which is harmless there because clause 4 concludes `⊥`;
  the descent case spends the residue at exactly one row, the `down`
  argument of `descent-core`.
- Section 4: why the residue is an untruncation and not a `dne`
  (`:214-242`), with the file:line for each fact.

Prices, all under the program's caliber and the caps this task set:

| run | cap | result |
|---|---|---|
| W3 alone (`runs/w3-3.out`) | 120 s | green, 1.51 s |
| floor, recursion holed (`runs/floor-1.out`) | 300 s | 7.01 s, only error is the deliberate hole |
| final 1, 2, 3 (`runs/final-*.out`) | 300 s | green, 1.56 s, 1.52 s, 1.50 s |

The floor run also elaborated two `src/` modules whose interfaces were
cold (`L.Absorption`, `L.SquareLawClosed`); the finals ran warm. No run
approached its cap. The heap-wall clause never fired: nothing walled.

The brief estimated about 160 lines; the file is 242, of which the
obligation-from-residue machinery is about 50. The extra length is the
coverage map and the comment record, not proof mass.

## W2, ANSWERED

The probe is written once at the generic carrier `{ℓ}` with `lem` as
the only hypothesis, and it reuses the tree's own generic modules
(`L.Ordinal.SquareLaw`, `L.InjChain`, `L.Cardinal`,
`L.SquareLawClosed`) at that carrier. No fixed level appears anywhere
in the file. Nothing was written twice, and both trophy proofs would
consume this measurement unchanged. No deadline forced a fixed form.

## WHAT THE NEXT BRIEF NEEDS

- The residue is now a named type with a green proved consequence:
  `Inj-extract` at `agents/tasks/LJ-1-618/Probe618.agda:151-154`. If
  the owner funds it, the funding is for a per-site untruncation of a
  truncated injection, and the site grain is the cheapest place it can
  be asked. The necessary-and-sufficient criterion for any untruncation
  is on record at `dev/literature/truncation-and-selection.md:152-161`
  (the `splitSup` form: a weakly constant endomap).
- The class-pred formula stays one ingredient short: `[LJ-1.613]`'s
  (i) and (ii) are internal, (iv) and (v) are paid, and (iii) at the
  spend grain is exactly this residue. That is the whole gap; the probe
  closes every other row of the recursion.
- What resisted: the descent case only. Every other case of the
  untruncated recursion closes with the tree's own rows, at zero new
  mathematics. I weakened nothing: the probe's `step′` is the tree's
  `step` with the truncation removed from the motive, row by row.
- For `[LJ-1.617]`, running in parallel: this task's answer gives its
  question a floor. The narrow grain does not close without the same
  untruncation the wide grain needs, so a YES at 617 saves less than
  the bill hoped.

## PREMISE CHECKS

- Premises 1, 2, 3 verified at the cited lines
  (`src/L/BoundedSubset.lagda.md:1397`, `:1388`, `:1410`).
- Premise 4 verified (`agents/tasks/LJ-1-604/lj-1.604-report.md:116-117`).
- Premise 5: the cited line `agents/tasks/LJ-1-605/review-of-uniform-pairing.md:90`
  is a section heading; the statement itself sits at `:96-98`. The
  premise holds, at the corrected line.
- **Premise 6 is NOT checkable in this tree.**
  `agents/tasks/LJ-1-607/lj-1.607-report.md` does not exist here; no
  `LJ-1-607` directory and no `LJ-1-617` artifacts are present in this
  worktree. I did not treat `[LJ-1.607]`'s result as evidence. The
  module-grain claim I needed is carried by `[LJ-1.605]`, which is in
  the tree. This does not block the stop: my object is strictly below
  the module grain.
- Premises 7, 8 verified (`src/L/StageCardinal.lagda.md:17`,
  `src/L/Cardinal.lagda.md:22`).
- Premise 9 verified (`agents/tasks/LJ-1-593/review-of-square-coded.md:82-84`).
- Premise 10 verified (`agents/tasks/LJ-1-613/Probe613.agda:137` and
  its surrounding section).

## ARCHIVE USED

Candidates named in the brief's ARCHIVE block, each answered:

- `archive/dev/LJ-dispatch-index.md` - READ, USED.
  `:183`: "`| LJ-1.107 | sq at every infinite ordinal | PARTIAL:
  initial ordinals only | The non-initial case needs an injection the
  truncated least-of witness cannot give: the inject type is not a
  prop |`" and `:190`: "`| LJ-1.114 | Thread the truncation from
  StageCardinal to Devlin55 | WALL, ROUTE-LEVEL | Upper's h-inj needs
  ONE honest injection; two truncation eliminations collide. Reverted;
  the cause is proved |`". Both rows are the direct predecessors of
  this task's measurement.
- `archive/dev/JOURNAL.md` - READ, USED. `:661`: "`law as \`Formula K
  1\`, pairing at β, not a stronger one, so the fork neither`". This
  records that the count's own need is pairing at β, the spend grain
  this task measured.
- `archive/dev/JOURNAL-archived.md` - READ, USED. `:1231`:
  "`conditional core, so the missing piece is exactly the pairing
  chapter, priced at 250-400 lines`". The old T2 wall, at the same
  object.
- `archive/dev/DD-archived.md` - NOT USED. The search over it found no
  square-law or pairing row; this task decided nothing on DD material.
- `archive/dev/DECISIONS-archived.md` - NOT USED. Same search, same
  result: no row on the square law, `[LJ-1.107]` or `[LJ-1.114]`.

## LITERATURE USED

Candidates named in the brief's LITERATURE block, each answered:

- `dev/literature/truncation-and-selection.md` - READ, USED. `:146-147`:
  "`**The constraint the route carries: \`P\` must be \`hProp\`-valued.**
  So `leastOf` delivers the least INDEX untruncated, and any payload it
  delivers with the index is a proposition. **A data payload does not
  come out.**`" and `:84-85`: "`formalization that states its
  conclusion with the injection as data is asking for something the
  sources do not supply`". Section 2.4's `splitSup` criterion
  (`:149-161`) is the test any funded residue must pass.
- `dev/literature/devlin-II5.md` - READ, USED. `:281-282`: "`(ii),
  |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact`". This
  is the classical side: Devlin cites the level-size equation, whose
  counting half is the `Bound` module this task's spend site feeds.
- `dev/literature/digest.md` - DECLINED. Its pairing row
  (`:241`, Gödel pairing, `α → J_α^A`) is the syntactic pairing of the
  J tower, a different object from the square law at an ordinal.
- `dev/literature/terms-2026-08.md` - DECLINED. Glossary terms only
  (`:37`, `:42`); this task adds no term, and the glossary rule forbids
  a self-chosen entry.
- `dev/literature/geology.md` - DECLINED. The search found no
  square-law or pairing content; not surveyed further.

## GATE

The cheap gate parts that can see this task's files pass clean:
`weave-i18n.py --check`, `lint-prose.py --check`,
`check-probes.py --check` ("clean", 7831 tracked files). The full
`make check` was not run: no `src/` file changed, the probe is checked
by its recorded runs, and the tree typecheck is the program's commit
gate, not this slot's.
