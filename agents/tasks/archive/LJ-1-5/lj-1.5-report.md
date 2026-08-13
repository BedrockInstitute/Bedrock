# LJ-1.5 report: the condensation lemma, block 1, on the erase route

Status: COMPLETE. Written incrementally per C-22. One untracked master,
no commit, no push. ASD-STE100.

## 1. THE VERDICT

DELIVERED. `src/L/Condensation.lagda.md` carries the first block on the
erase route. It has 308 in-fence non-blank lines. It checks cold in 2.42
seconds of user time, one process, at `GHCRTS="-A64m -I0 -M8g"`. The
rate is 0.0079 seconds per line. DD24's bar is 0.013193. The block lands
at 0.60 of the bar. The gate is GO.

## 2. DID YOU NEED A PLACEMENT ANYWHERE?

NO. The master uses no placement at any point. It does not name `absFo`,
`placeFo`, a constant vector, an appended environment, or a witness
transport. The clause reaches the parameter-free axis through the
delivered `erase` (`src/FOL/Count.lagda.md:598-611`), and `erase-inv`
(`:617-637`) makes `σL ≡ φ` a syntactic equality. The transfer is two
syntactic `cong`s around one `abs₀` at the original clause's Delta-0
witness. That is P-u's law: certify before you place. No placement means
no `mapΔ₀` and no placed witness, so the measured wall never enters.

The arity tag is a slot `N` in `Clause.shapeBnd`, not a constant. The
`refl` at `ClauseDecode`'s `EraseTransfer` instantiation machine-checks
`countFo (Clause.existBndAt C T B N) ≡ 0` at a variable arity.

## 3. THE ELEVEN OBLIGATIONS

All eleven landed, with the probe's types. The master splits them by
DD4 side; the template half is `EraseTransfer`, the per-tower half is
`Clause` and `ClauseDecode`.

| obligation | where it lives | status |
|---|---|---|
| the whole `Clause` module, ten Delta-0 witnesses | `Clause` (`src/L/Condensation.lagda.md:52-195`) | landed |
| `existCertAt` | `:198-199` | landed |
| `Σ₁-cert` | `:201-202` | landed |
| `existBnd-out` | `ClauseDecode`, `:253` | landed |
| `existBnd-in` | `ClauseDecode`, `:273` | landed |
| `σL` (with `σL₀`, `σL≡`) | `EraseTransfer`, `:216-224`; re-exported at the clause, `:299-303` | landed |
| `σL-eq` | `EraseTransfer`, `:226-227`; re-exported at the clause, `:304-306` | landed |
| `σL-out` | `ClauseDecode`, `:315` | landed |
| `σL-in` | `ClauseDecode`, `:329` | landed |
| `σL-transfer` | `EraseTransfer`, `:229-233`; re-exported at the clause, `:307-309` | landed |
| `σL-up` | `EraseTransfer`, `:235-236`; re-exported at the clause, `:310-312` | landed |
| `cert-transfer` | `CertTransfer`, `:345-346` | landed |
| `ride-only` | `:355-358` | landed |
| `ride-defines` | `:360-363` | landed |

`[LJ-1.32-R]` counts these as eleven groups; the table lists the
separate names so nothing is dropped. Nothing is dropped. Each type is
the probe's type, checked by Agda.

## 4. THE NUMBER

308 in-fence non-blank lines at the ledger caliber, one master,
`src/L/Condensation.lagda.md`. The probe measured 251. The difference is
the template split and the DD4-side comments. The catalogs are excluded
by DD26; this master is not a catalog.

The count uses `scripts/ledger.py`'s `count` with `at_head=False`: every
non-blank line inside a ` ```agda ` fence.

## 5. SECONDS AND RATE

Two cold runs, one Agda process each, quiet machine, at
`GHCRTS="-A64m -I0 -M8g"`. The master's own interface was moved aside
before each run; dependencies were warm through
`_build/2.8.0/agda/src/`. No interface ever sat beside a source.

| run | user s | wall s |
|---|---:|---:|
| 1 | 2.46 | 3.47 |
| 2 | 2.38 | 2.52 |
| mean | 2.42 | |

The pair is flat under the noise rule: the delta is 3.3 percent, under 5
percent.

Rate: 2.42 / 308 = 0.0079 seconds per line. DD24's bar is 0.013193. The
block lands at 0.60 of the bar. The probe measured 0.0107 to 0.0114
(`_build/lj-1.32-review.md:37-48`). The master's rate is DOWN from the
probe, and the total is down too: 2.42 seconds against the probe's 2.69.
The brief expected a master to pay a module-load floor and move UP. It
moved DOWN instead. The template factoring and the lighter import block
are the likely causes; I did not profile them separately.

C-31 framing: the per-module rate is advice, and the aggregate is the
judgment. The GCH seconds budget is 99.6 to 147.7 seconds over a
projected 7,553 to 11,197 lines (`dev/ledger.toml`). DD24's bar is that
budget divided by the projected size. This block sits under the bar, so
the aggregate framing does not move the verdict.

## 6. WHAT THE NEXT BLOCK NEEDS

The next block is the rest of route A, priced at about 3.3k lines over
eight components (`_build/lj-1.12-report.md:20-49`). This block is the
clause component. What remains:

1. The twelve-clause table: the other eleven clauses, each with its
   two-way decode at the class carrier and its certificate. Each should
   instantiate the same `EraseTransfer` template.
2. The step and graph stack: the bounded matrices for the delivered
   `StepAt`, `ApproxAt` and `LsetGraphAt` readings, and the story-to-
   machine agreement at `L`. This is `[LJ-1.28]` leg D.
3. The iso-invariance and the limit case of the condensation induction.

One honest price, with its basis. The clause-shaped residue lands at
this block's measured rate: the remaining 2.7 to 3.0k lines at 0.008 to
0.010 seconds per line cost about 22 to 30 seconds. Leg D is the widest
unmeasured term: 0.3 to 0.8k lines at 0.0052 to 0.085 seconds per line
(`_build/lj-1.28-report.md:95-106`, `:128-135`), which is 5 to 68
seconds. The next gate should measure leg D's rate before the block is
funded. The price is a projection until then.

## 7. DD4

Each piece falls on one side.

| piece | side |
|---|---|
| `Clause` and its ten Delta-0 witnesses | per-tower (Def) |
| `existCertAt`, `Σ₁-cert` | per-tower (Def) |
| `existBnd-out`, `existBnd-in`, `σL-out`, `σL-in` | per-tower (Def) |
| `EraseTransfer` (`σL₀`, `σL`, `σL≡`, `σL-eq`, `σL-transfer`, `σL-up`) | template |
| `cert-transfer` | delivered shape (`AbsL.σ₁-up`), per-tower residue is one line |
| `ride-only`, `ride-defines` | delivered, neither side |

The template is the erase route itself: a fact about constant-free
formulas at the class carrier, not about `L`'s Def syntax. Both towers
instantiate it with their own formulas and witnesses.

What the J tower gets: the `EraseTransfer` template with its own story
formula and its structural Delta-0 witness (D-26), the delivered
`σ₁-up` shape, and the delivered landing legs. It does not get the
`Clause` module. Its certificate avoids the defining syntax entirely,
which is `[LJ-1.27-R]`'s finding, and the template is what makes that
possible without re-writing the transfer.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md`, sections 2.1 to 2.8. Step C at
`:209-256` is the one that bears. Took: level-hood at Sigma-1 strength
with a Sigma-0 matrix, the witness inside the carrier, and the bounded
Def-step description. The transfer chain moves ONE formula by name
across the carriers, and the formal proof pays the two-way decodes at
each carrier. That gap is exactly what this block prices. The clause
matrix and its certificate are the Sigma-0 matrix and the Sigma-1
witness, in the project's coding.

`_build/literature/dev2.txt:1369-1388`. Read 5.5 and 5.6. They consume
parts (i) and (ii) of condensation and the level-size equation. Nothing
there changes the clause's shape or the certificate's level.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: the brief rules
it out, and `[LJ-1.14]` verified it does not cover Chapter II section 5
(`_build/lj-1.14-report.md:107-108`).

`dev/literature/j-hierarchy.md`. NOT read. WHY NOT: the J tower enters
only as the DD4 comparison target. The measured block is the Def-tower
half.

## 9. ARCHIVE USED

`src/ProbeDD25E.agda`, in full. The green starting point. Each
obligation was lifted from it and re-verified at the master (D-10). The
clause formulas and witness bodies match it line for line; the
organization is re-derived, not copied.

`_build/lj-1.32-review.md`, in full. Took the eleven-obligation list at
`:61-68`, the count-0 wall evidence at `:129-143`, and the erase-route
recommendation at `:284-311`.

`_build/lj-1.27-review.md`, in full. Took the wall location, in building
the placed witness, at `:59-91`, and the erase-route mechanism with
`erase` and `erase-inv` at `:204-256`.

`_build/lj-1.27-report.md`. Took the profile at `:58-69`
(`σL-transfer` 24.8, `σL-eq` 6.2), the 179-millisecond `σ₁-up` at
`:93-95`, and the 1.6-second `abs₀` at `:95`.

`_build/lj-1.28-report.md`. Took legs A and B as delivered at `:6-10`
and leg D's 0.3 to 0.8k lines at `:95-106` with its price at `:128-135`.

`_build/lj-1.29-report.md`. Took the ruling at `:1-42`: the crossing
keeps the shared formula, and the placement must go.

`_build/lj-1.31-report.md`. Took section 6 at `:93-117`: `consAtL` is
constant-free, and the real clause forms keep the arity tag and the
term-value tags.

`_build/lj-1.32-report.md`. Took the count-0 wall at `:6-10` and the
flat ladder at `:31-52`.

`archive/rud-route/src/L/Condensation.lagda.md`, 885 lines, in full.
Read for SHAPE only. Its story is born parameter-free on `⊥*`, embedded
with `embed`, and witnessed with `mapΔ₀` and `mapΣ₁`. The modern clause
cannot be born parameter-free (it names the delivered readers), so
`erase` carries it instead. No price was taken from the archive: its
target is classically false (`[LJ-1.11]`).

`dev/LESSONS.md`. P-u at `:2908`: certify before you place. P-m at
`:2460`, P-l at `:2305`, P-n at `:2483`, D-10 at `:1316`, C-12 at
`:2075`, C-22 at `:2237`, through `scripts/rules.py --for build`.

## 10. WHAT I AM NOT SURE OF

1. The matrix-to-clause link is unproven. Nothing shows the bounded
   matrix says what the delivered `existClauseAt` says. The gap is
   older than this task and equal on both routes (`_build/lj-1.32-
   review.md:191-195`). The story-to-machine leg must close it.
2. The slot's environment obligation is unmeasured. The crossing must
   show the slot holds `numeralL 8`. It is one environment lookup. P-l
   forbids pricing it by analogy.
3. The rate moved down from the probe: 0.0107 to 0.0114 down to 0.0079.
   The template factoring and the lighter imports are the candidates. I
   did not profile which. The number stands on its own two cold runs.
4. The M-side story mirror is still unmeasured. `[LJ-1.29]` settled
   that the crossing needs the shared formula, and the L-side landing
   is this block. The M-side cost is additive and open.
5. I did not run `make check`. The brief forbids it. The orchestrator
   wires the catalog after auditing. I ran `lint-prose.py --check` and
   `lint-agda.py --check` on the master, `lint-agda.py --check` on the
   whole tree, and `weave-i18n.py --check` on the master. All pass.
   The master has no prose markers: DD23 freezes mathematical prose, so
   it carries code and its own comments only.
6. There are no consumers of `L.Condensation` in the tree. Nothing
   imports it yet. The consumer typecheck is vacuous by construction.
