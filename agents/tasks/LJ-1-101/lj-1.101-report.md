# LJ-1.101: close the cardκ type gap, then price sq for every infinite ordinal

tier: codex (default)

## STATUS

COMPLETE. Step 1 is GREEN: `cardκ` checks at the master's `IsCardinal`
with no transport. Step 2 is priced, with two machine-checked
measurements. The probe is `src/ProbeLJ1101A.agda`, GREEN at the C-12
cap, one process. No master was touched. No commit, no push. The report
is `_build/lj-1.101-report.md`.

## 0. THE VERDICT

**YES. `cardκ` typechecks at the MASTER's `IsCardinal`.** The term is
`cardκ-at-master : IsCardinal SiteAt.κ` at
`src/ProbeLJ1101A.agda:56-57`, with the body `SiteAt.cardκ` unchanged.
It checks GREEN, exit 0, one process at the C-12 cap
(`GHCRTS="-A64m -I0 -M8g"`). The local copy at
`src/ProbeLJ194A.agda:67-68,73-74` and the master's statement at
`src/L/BoundedSubset.lagda.md:1042-1043,1045-1046` are **definitionally
the same type**: both unfold over the same `hPropStructure 𝒮ᵥ` carrier,
and the two `_↪_` definitions connect by the identity function
(`↪-agree`, `src/ProbeLJ1101A.agda:50-51`). No transport is needed.

The seconds, Step-1 content only, import cache warm: **3.1 s** (two
runs, 3.115 s and 3.128 s) at load averages 6.32/6.08/5.31 and
4.65/5.65/5.20, four users, machine NOT quiet. The whole probe with the
Step-2 extensions checks at 21.1 s cold for its own content (first
run, load 5.59/4.87/4.71) and 3.3 s warm (re-run, load 5.16/4.84/4.70).
The probe is 136 non-blank lines.

The brief's predicted "100 s or more" for the master import is about the
cold check of `L.BoundedSubset` itself. With the project's persistent
Agda cache warm, a consumer pays seconds, not minutes: the whole probe,
which imports the master, checks in 3.1 s. The cold master check is not
measured here (clearing the shared cache would disturb the sibling
agent's slot). **INFERRED** for the cold figure; **MEASURED** for the
warm consumer price.

## 1. STEP 1, THE TYPE GAP

The two statements agree. `ProbeLJ194A`'s local copy
(`src/ProbeLJ194A.agda:73-74`) and `L.BoundedSubset`'s
(`src/L/BoundedSubset.lagda.md:1045-1046`) have identical bodies, both
over the same `hPropStructure 𝒮ᵥ` (`FOL/ZFStructure.lagda.md:91-94`,
`V/Hierarchy.lagda.md`), so `S`, `_∈ˢ_`, `⟨_⟩`, `⟪_⟫` and `Empty.⊥` are
the same constants. The identity `↪-agree` (`src/ProbeLJ1101A.agda:50-51`)
checks, which proves the two `_↪_` definitions agree definitionally at
every carrier pair. Then `cardκ-at-master = SiteAt.cardκ` (`:56-57`)
checks. If the types had differed, the identity and the direct
application would both have failed; they check. **MEASURED.**

The only friction was syntactic: a qualified mixfix operator needs
parentheses in prefix position, and the applied module needs an alias
for qualified access. Neither is a type difference.

## 2. STEP 2, THE THREE PRICES

### 2.1 Does `Init κ` follow for the Hartogs `κ`?

Two of `Init`'s four components are delivered: `IsOrd κ`
(`src/ProbeLJ194A.agda:919-920`) and `ω ∈ κ` (`:876-877`). The other
two are new content.

**The square cardinality clause follows from `IsCardinal` through a
bridge, machine-checked.** `IsCardinal` forbids an injection into a
member `⟪ δ ⟫` (`src/L/BoundedSubset.lagda.md:1045-1046`); `Init`
forbids one into `⟪ β ⟫ × ⟪ β ⟫` (`src/L/Ordinal/SquareLaw.lagda.md:692-701`).
The bridge: every member `β ∈ κ` is countable (the delivered `countAt`,
`src/ProbeLJ194A.agda:535-537`, via `κ-mem` `:879-880`), so an
injection `κ ↪ β × β` composes through the countability and an
injective pairing on `⟪ ω ⟫` into an injection `κ ↪ ω`, which `cardκ`
refutes at `δ = ω ∈ κ`. `InitClauseBridge.square-clause`
(`src/ProbeLJ1101A.agda:78-103`) checks this under one hypothesis: the
pairing. **MEASURED.**

The pairing `⟪ ω ⟫ × ⟪ ω ⟫ ↪ ⟪ ω ⟫` is the one assembleable-but-not-
delivered piece. The tree delivers the square-scheme pairing on ℕ with
injectivity (`pair`/`pair-inj`, `src/FOL/Count.lagda.md:29-30,59-60`)
and the injective numerals (`#-inj′`, `src/V/Coding.lagda.md:114-115`).
The assembly is priced at 20 to 50 lines. The one unmeasured step
inside it is the `⟪ ω ⟫ ≃ ℕ` presentation bijection. **INFERRED.**

**The successor closure is not delivered.** `[LJ-1.94]` delivers
initial segments, the downward direction (`member-of-ot`,
`src/ProbeLJ194A.agda:884-885`), not successors. The statement
`γ ∈ κ → sucV γ ∈ κ` is the "a successor of a countable ordinal is
countable and realizes as an order type" content at the `WO` level. It
is new content, priced at 60 to 150 lines, in the same instantiation
class as the probe's `InitialSegment` block (280 lines, about 16 s,
measured by `[LJ-1.94]`). **INFERRED** price.

**One best-effort figure for `Init κ`: 150 lines** (band 80 to 200),
on top of the delivered probe. Basis: the successor piece (60 to 150)
at the measured rate of the delivered `InitialSegment` block, plus the
bridge's measured shape (the square clause itself checks; the pairing
assembly is 20 to 50). The assembly is machine-checked:
`InitAtSite.initκ : Init SiteAt.κ` (`src/ProbeLJ1101A.agda:105-109`)
checks under exactly these two hypotheses, the pairing and the
successor closure. The widest unmeasured term of this answer is the
successor closure at the `WO` level.

### 2.2 The route from `Init` at the cardinals to `sq` at every infinite ordinal

The route is the standard reduction, and it is choice-free. For
infinite `α`, let `β = |α|`, the least ordinal with `α ≈ β`. Then:

- `sq ω` comes directly from the ℕ pairing (`src/FOL/Count.lagda.md:29-30,59-60`).
  The `ω` case is NOT via `Init`: `Init ω` is false, because it
  requires `ω ∈ ω`.
- `Init β` for uncountable initial `β`: `ω ∈ β` since `β` is infinite;
  successor closure because an infinite cardinal is a limit ordinal
  (successor-absorption content, 30 to 80 lines); the square clause by
  minimality of `β` plus `sq β'` for smaller infinite `β'`, by
  transfinite induction over the ordinals (the tree's `∈-induction` is
  delivered, used at `src/L/StageCardinal.lagda.md:559`).
- `sq β` from `Init β` by the delivered `via-col-square`
  (`src/L/Ordinal/SquareLaw.lagda.md:960-961`).
- `sq α` from `sq β`: `α ↪ β` by definition of `|α|`, and `β ⊆ α`
  because `|α| ≤ α`. Then `α² ↪ β² ↪ β ↪ α`. Composition only.

Choice-free: every step is explicit; no choice axiom appears anywhere.
LEM enters only in the standing form, through `leastOf` for the least
ordinal and through the impredicativity parameter. **INFERRED** by
reading: the delivered col and order-type machinery is choice-free
(`_build/lj-1.92-report.md` section 7, `_build/lj-1.94-report.md`
section 3), and none of the new steps adds a choice principle.

**One best-effort figure: 500 lines** (band 350 to 750). Basis: the
delivered comparable, the `[LJ-1.94]` Hartogs chain at `ω` (1058
non-blank lines, 27 s cold, measured), minus the order-type block now
delivered generically (365 lines, `src/ProbeLJ192A.agda`, measured by
`[LJ-1.92]`), re-instantiated at a generic ordinal carrier. The new
content is (a) the generic Hartogs and least-`|α|` construction, 200 to
350 lines; (b) the transfinite induction proving the square clause at
initial ordinals, 100 to 250 lines; (c) successor absorption, 30 to 80;
(d) the final assembly, 15 to 40.

**The widest unmeasured term of the whole step 2: the generic-Hartogs
block at an arbitrary ordinal carrier.** Its seconds rate is unmeasured
at that carrier. The only measured site is `ω`: 27 s for 1058 lines,
the instantiation class of P-m. A re-instantiation at a generic carrier
may check at a different rate. **INFERRED.**

### 2.3 `absorbs-subset`, separately

**The general statement is FALSE as stated.**
`absorbs-subset` (`src/L/BoundedSubset.lagda.md:1364-1368`) quantifies
over ALL ordinals `α`. At `α = ∅`, `Lset ∅` is the empty stage
(`Lset-out`, `src/L/Constructible.lagda.md:336-338`), so with `x = ∅`
the statement demands an injection from the singleton stage
`Lset ∅ ∪ {∅}` into the empty stage `Lset ∅`. There is none. The
refutation is machine-checked: `AbsorbsRefute.refute`
(`src/ProbeLJ1101A.agda:153-156`). **MEASURED.** This is a D-10 check:
the recorded hypothesis cannot be discharged by any theorem. Only its
infinite instances are true content.

**What the consumer needs (D-30): the site instance.** The consumer
applies `absorbs-subset` at its own site (`BoundedSubsetAt`,
`src/L/BoundedSubset.lagda.md:1530`), where `α = ω` and `x = ∅`
(`SiteAt`, `src/ProbeLJ194A.agda:1202-1215`). There `∅ ∈ Lset ω`
(`∅∈𝒟ₒ`, `src/L/Axioms/Basic.lagda.md:490-491`, climbed by `Lset-in`),
so `Lset ω ∪ {∅} ≡ Lset ω` and the injection is the identity on
presentations. **One best-effort figure: 20 to 30 lines.**

The general infinite-`α` form (the true content, if the hypothesis is
corrected) prices at **150 lines** (band 80 to 200): the case split
`x ∈ Lset α` versus not (LEM), then for `x ∉ Lset α`, the composition
`Lset α ∪ {x} ↪ α+1` (via `stage-card-upper`,
`src/L/StageCardinal.lagda.md:557-559`, plus a top), `α+1 ↪ α`
(successor absorption, 30 to 60 lines), and `α ↪ Lset α`
(`stage-card-lower`, `src/L/StageCardinal.lagda.md:207-209`). The
hardest piece is the injection on the union PRESENTATION
`⟪ Lset α ∪ ⁅ x ⁆s ⟫`, the R-35 class (union representations). Its
seconds are the widest unmeasured term of this answer. **INFERRED.**

## 3. THE NEGATIVES AND THEIR STATUS

1. "The two `↪` definitions differ": **MEASURED FALSE**. The identity
   `↪-agree` (`src/ProbeLJ1101A.agda:50-51`) checks; the statements
   are definitionally equal.
2. "`cardκ` checks at the master's `IsCardinal`": **MEASURED TRUE**.
   `cardκ-at-master` (`:56-57`), exit 0 at the C-12 cap.
3. "`[LJ-1.94]`'s machinery alone reaches `Init κ`": **MEASURED
   FALSE**. `initκ` (`:105-109`) needs the successor closure and the
   pairing as hypotheses; `IsOrd κ` and `ω ∈ κ` are delivered.
4. "`IsCardinal` gives the `Init` square clause directly": **MEASURED
   TRUE through a bridge**. The bridge checks under the pairing
   hypothesis (`:78-103`); the pairing itself is assembleable from
   delivered pieces (`src/FOL/Count.lagda.md:29-30,59-60`).
5. "`absorbs-subset` is true as stated": **MEASURED FALSE**.
   `AbsorbsRefute.refute` (`src/ProbeLJ1101A.agda:153-156`), the
   counterexample at `α = ∅`, `x = ∅`.
6. "The route to `sq` at every infinite ordinal is choice-free":
   **INFERRED TRUE** by reading the delivered machinery's
   choice-freedom; no machine check of the new route exists.
7. "Importing the consumer master costs 100 s or more":
   **INFERRED FALSE** at this site with the warm cache. Measured: the
   Step-1 consumer file, master import included, checks in 3.1 s
   (`src/ProbeLJ1101A.agda:50-57`). The cold master check itself is
   unmeasured here.

## 4. DD4

**Step 2's square-law half keeps the generic class. MEASURED.** The
probe's mathematics names only the ambient universe `S`, the small
presentations, injections, the pairing, `ω`, `sucV` and the ordinal
supply. No tower object (no `Def`, no `Rud`, no `Lset` beyond the
refutation) appears in any type of the `Init`/`sq` content. The square
law is exactly the shared block the digest classifies as EITHER-tower
(`dev/literature/devlin-II5.md:382-387`); the J half is **INFERRED**
(no J tower exists in this tree).

The one per-tower item is `absorbs-subset`, by consumer decree: it is
about `Lset` and the level-size equation, the L tower's analogue of
which the J tower carries as SZ 1.27. **INFERRED** for J.

## 5. LITERATURE USED

Devlin assumes the square law and the cardinal arithmetic; he does not
prove them in II.5. The digest records 5.5's proof consuming
`|M| = |L_α|` and `|γ| = |α| < κ ⇒ γ < κ` as Chapter I ZF content
(`dev/literature/devlin-II5.md:145-166`). Spent little, as banked by
`[LJ-1.92]`.

## 6. GATES

- `src/ProbeLJ1101A.agda`: GREEN at the C-12 cap, one process, exit 0.
  Step-1 content: 3.1 s (3.115 s, 3.128 s) at loads 6.32/6.08/5.31 and
  4.65/5.65/5.20. Whole probe: 21.1 s first run (own content cold) at
  load 5.59/4.87/4.71; 3.3 s re-run at load 5.16/4.84/4.70. Four users
  at every run, machine NOT quiet. 136 non-blank lines. No process was
  left alive; every check returned.
- `scripts/lint-agda.py --check src/ProbeLJ1101A.agda`: exit 0.
- `scripts/lint-prose.py --check` on the probe and this report: exit 0.
- No `make check` (forbidden by the brief). No master was touched.
  DD23: no mathematical prose was written.
- `git status`: clean at the end. HEAD moved during the dispatch from
  `7dec213` to `03fa4d2` (the orchestrator's LJ-1.100 commit); my work
  touched no tracked file. The probe and this report are ignored.
  No commit, no push.
- `scripts/ledger.py --brief`: standing 28,189 lines over 85 masters,
  measured from HEAD `03fa4d2`. This dispatch changes no standing
  figure.

## 7. ARCHIVE USED

- `_build/lj-1.94-report.md`, read WHOLE. TOOK the Hartogs chain, the
  site table, and the measurement basis (1058 lines, 27 s).
- `src/ProbeLJ194A.agda`, read the scope (`:60-80`, `:1180-1240`) and
  the whole of `SmallWO`/`Count`/`InitialSegment`/`Natural`/`Hartogs`
  where quoted. TOOK `SiteAt` (`:1186-1233`), `cardκ` (`:1160-1161`),
  `countAt` (`:535-537`), `κ-mem` (`:879-880`), `member-of-ot`
  (`:884-885`), `ω∈κ` (`:876-877`), `WO` (`:184-185`), `ot`
  (`:237-238`), the local `_↪_`/`IsCardinal` (`:67-74`).
- `src/L/BoundedSubset.lagda.md`, read `:1040-1050`, `:1361-1370`,
  `:1396-1402`, `:1520-1535`. TOOK the master `_↪_`/`IsCardinal`
  (`:1042-1046`), `Devlin55` (`:1361`), `absorbs-subset`
  (`:1364-1368`), `BoundedSubsetAt` (`:1396`), the consumer use
  (`:1530`).
- `src/L/Ordinal/SquareLaw.lagda.md`, read `:685-701`, `:703-760`,
  `:938-964`. TOOK `sq` (`:685-687`), `Init` (`:692-701`),
  `InitialCore` (`:703`), `via-col-square` (`:960-961`).
- `src/L/StageCardinal.lagda.md`, read `:1-40`, `:195-215`, `:500-560`.
  TOOK `sq` as a module parameter (`:15`), `stage-card-lower`
  (`:207-209`), `stage-card-upper` (`:557-559`).
- `src/FOL/Count.lagda.md`, read `:27-66`. TOOK `pair`/`pair-inj`
  (`:29-30`, `:59-60`).
- `src/L/Constructible.lagda.md`, read `:210-250`, `:318-345`. TOOK
  `Lset` (`:222`), `Lset-compute` (`:227-228`), `Lset-out`
  (`:336-338`).
- `src/L/Axioms/Basic.lagda.md`, read `:485-495`. TOOK `∅∈𝒟ₒ`
  (`:490-491`).
- `src/V/Coding.lagda.md`, read `:100-120`. TOOK `#-inj′` (`:114-115`).
- `src/V/Model.lagda.md`, read `:85-105`, `:170-185`. TOOK
  `pair-singleton` (`:173`).
- `src/FOL/ZFStructure.lagda.md`, read `:40-105`. TOOK `hPropStructure`
  (`:91-94`), `S`, `_∈ˢ_` as structure fields.
- `_build/lj-1.92-report.md` and `src/ProbeLJ192A.agda`, read WHOLE.
  TOOK the order-type block price and its choice-freedom.
- `_build/lj-1.91-report.md`, read WHOLE. TOOK the five-step route and
  the EITHER-tower classification.
- `dev/LESSONS.md`, read WHOLE C-38 (`:3427`), C-35 (`:3200`),
  C-36 (`:3284`), D-8 (`:1377`), D-30 (`:3332`), P-l (`:2305`), and
  the `--for build` and `--for probe` bundles via `scripts/rules.py`.
- `dev/literature/devlin-II5.md`, read `:140-170`, `:375-420`. TOOK the
  literature answer.
