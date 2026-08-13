# DIAG: the DD24 residual of 2.33 s on the GCH wing

Status: COMPLETE.
Agent: diagnostic, read-only for masters. Branch `two-tower-bridge`, HEAD `21f8f26`.
Gate reading (orchestrator's run, current): wing aggregate 0.0130 s/line over 8,269 lines
and 107.48 s; ceiling 105.15 s; residual 2.33 s.

**This diagnosis ran NO Agda process.** Every figure comes from the orchestrator's gate
reading, from the five cited reports, or from arithmetic over those figures. Code claims
come from reading `src/L/Condensation.lagda.md` in the working tree (6,390 in-fence lines).
No load average is reported because this agent measured nothing.

## 0. Recommendation, first

**Band-wide in-place treatment, in the KFacts record-bundle shape, gated by a one-family
probe. Not row-level treatment.** The three named rows hold 5.845 s together (MEASURED);
a cure of all three cannot reliably return 2.33 s, and no measured precedent cures a
once-elaborated named proof in place. The band holds 44.31 s at 0.0202 s/line (MEASURED),
and only 5.8 s of that sits in profile-visible named definitions. The other ~38.5 s is
elaboration cost, and the band's code shows the exact shape the KFacts bundle already
cured once in this file for minus 30 s: near-identical hypothesis telescopes restated
across thirteen row modules (591 of 2,196 band lines are module headers; see section 1).
A 5.3 percent cut of the band closes the residual. Section 4 gives the dispatch and its
abort criteria.

## 1. Where the 2.33 s is

**The residual is a net figure.** At the bar rate 0.012716, `L.Condensation`'s own share
of the ceiling is 6,390 x 0.012716 = 81.25 s; it measures 99.45 s, so it is **+18.20 s
over its share**. The five other wing modules measure 8.03 s against a 23.89 s share, so
they run **15.86 s under**. The net is the 2.33 s. **MEASURED** (arithmetic over the
gate's own current rows). Every second of the overage lives in `L.Condensation`.

**Inside the module, the band is the mass.** The row-agreement band
(`src/L/Condensation.lagda.md:2720-5101`, 2,196 in-fence lines) costs 44.31 s at
0.0202 s/line: **MEASURED**, same-session before/after removal at the gate's caliber
(`_build/lj-1.64-report.md:82-91`). The rest of the module reads 55.34 s over 4,194
lines = 0.0132 (`lj-1.64` after-row). The residual equals 5.26 percent of the band.

**The band's cost is NOT in its named proofs.** Two independent cold profiles agree
(`_build/lj-1.63-report.md:109-119`, `_build/lj-1.64-report.md:52-57`): the only band
definitions above the profile threshold are `PropAgree.subB2T-back` (2,949 ms),
`ImpLeaf.yaOut` (1,579 ms) and the three together hold 5.8 s. The band's remaining
~38.5 s sits in `Miscellaneous` (42,379 ms module-wide) plus sub-threshold definitions.
That is elaboration cost, not proof-body cost. **MEASURED** for the band total and the
named 5.8 s; **INFERRED** for the exact split of the 38.5 s (no profile of the
band-stripped module exists, and `Miscellaneous` has no per-definition attribution).

**The band has the KFacts shape, and this is the diagnosis.** Direct code evidence,
all **MEASURED** (countable in the file today):

- Thirteen row modules (`BotAgree`, `AndAgree`, `OrAgree`, `TopAgree`, `NegAgree`,
  `ForallAgree`, `ExistAgree`, `ClauseAgree`, `MemAgree`, `ImpAgree`, `EqAgree`,
  `AllInAgree`, `ExInAgree`) each restate a near-identical hypothesis telescope of 10 to
  17 entries. Module headers hold **591 of the band's 2,196 lines (27 percent)**:
  `PropAgree` 56 lines (`:3090-3145`), `AllInAgree` and `ExInAgree` 58 each, `MemAgree`
  and `EqAgree` 43 each, `AndAgree`/`OrAgree`/`NegAgree` 33 each.
- The restatement counts inside the band: the `tagEq`/`numK`/`innerK`/`codesK`/`valK`
  family appears **14 times each**; `keyK` 29 times; `arSubK` 31; `envInK` 30;
  `entryK` 15; `envK` 10. `AndAgree` (`:3336-3368`) and `OrAgree` (`:3386-3418`) restate
  `PropAgree`'s eleven-entry core verbatim, then pass all of it back to `PropAgree`
  (`:3369-3383`).
- Each hypothesis TYPE contains a built formula tree (`subValAt`, `envSetAt`,
  `envOverAt`, `tmValAt`). Satisfaction is a transparent recursion, so the elaborator
  unfolds the tree at every restatement (P-t, `dev/LESSONS.md:2601`).
- The band holds **33 inner module applications inside proof bodies**: `EnvSet` 15
  times, `AtomLeaf` 4, `BndLeaf` 4, `ImpLeaf` 2, `PropAgree` 2, `ExistAgree` 1. Each
  application re-elaborates the applied module's contents at its arguments.

The KFacts bundle cured exactly this class in this file: "the 24 to 44 parameter module
telescopes were re-elaborated at every instantiation site, and the record packages them
into one elaboration per module", minus 30 s and minus 34.1 s of `Miscellaneous`
(`_build/lj-1.62-report.md:106-112`). The band was never given that cure; the only
attempts against the band were deletion (`lj-1.64`, rejected) and three moves that
targeted the CHAIN, not the band (`lj-1.63` section 5). **The projected yield of a band
bundle is INFERRED until probed; the shape match is code fact.**

## 2. Row-level in-place treatment: not the right move

The three rows, each read in the working tree:

**`PropAgree.subB2T-back` (2,949 ms; `:3204-3246`).** One named proof inside the
parameterized `PropAgree`. Its statement and its `let`-bound intermediate types each
spell `subValAt`/`prAtL`/`appAt` trees at 7-to-9-deep environments, with
`prAtL-adequate`/`appAt-adequate` transport compositions. The environment is a module
VARIABLE (`γ : S ^ m`), so P-n's "concrete carrier" wording does not describe it; P-t
does: the formula is built, so it unfolds, whoever the carrier is. The definition is
elaborated ONCE. No measured precedent cures a once-paid named proof in place: the three
measured regressions at this wall (seal +1.61 s, shared frames +17.23 s, alias +3.29 s,
`_build/lj-1.63-report.md:149-191`) all tried to move once-paid cost, and
"sealing buys the repeats, never the once" (`_build/lj-1.47-report.md:137-140`).
Verdict: leave it. **INFERRED** (no row cure was measured here), bracketed by three
measured negatives of the adjacent move class.

**`ImpLeaf.yaOut` (1,579 ms; `:4280-4326`).** Same class. `ImpLeaf`'s telescope is small
(one `keyK` hypothesis, `:4218-4219`); the cost is the `subValAt` trees and adequacy
transports in the statement types, paid once at the parameterized module. Its two
instantiations by `ImpAgree` are applications whose cost lands at `ImpAgree`'s sites,
inside the band's elaboration mass. Same verdict, same status.

**`BinFormAgree._.go` (1,317 ms; `:5432-5513`).** A different shape, and the one row
where an in-place cure has a measured precedent. `out` and `back` are hand-written
three-deep `PT.rec` chains (`go`/`go₂`/`go₃`); every level restates the full result type
and the partial existential trees, and the innermost `where` instantiates
`BinShapeClosed` twice per direction (`:5477`, `:5512`). This is the Lift12 wall shape at
depth 3; `Lift12Back` measured 4.28x on the twelve-wide version
(`_build/lj-1.58-report.md` section 2). A depth-3 lift kit could cut most of its 1.3 s,
and `UnFormAgree` (`:5515`) repeats the shape smaller. Ceiling of the lever: about 1.0
to 1.5 s. **INFERRED**, with a same-file measured precedent.

**The arithmetic that closes the question.** Three rows = 5.845 s. Closing 2.33 s from
them needs a 40 percent cut across all three; the only precedented lever among them
(`BinFormAgree`) tops out near 1.3 s. So row-level treatment cannot reliably close the
residual, and the claim that the three rows ARE the residual repeats `lj-1.64`'s error
in a smaller form: the residual is the band's aggregate elaboration, and the rows are
its visible tip (their 5.8 s against the band's 44.31 s). The "P-n payable floor" label
for the three rows stays **INFERRED and imprecise**: P-n names concrete-carrier
satisfaction with hot NAMED definitions (T195's signature is 17 to 37 s per name); this
band's profile shape is the opposite (cost in `Miscellaneous`, names under 3 s), which
is the cure-able class, not the floor class. The floor here is real but smaller: the
once-paid named proofs, about 5.8 s of the 44.31.

## 3. Alternatives examined

**(a) The band-wide record bundle — the answer.** Pack the restated hypothesis families
into records: the numeral-indexed core (`tagEq`/`numK`/`innerK`/`pairK`/`codesK`/`valK`
at the row's k) and the environment family (`keyK`/`envK`/`entryK`/`arSubK`/`envInK`/
`subK`-variants). Each row module then takes one or two record parameters; each future
instantiation site passes one value. The existing `KFacts` (`:5675-5708`) does not cover
the band's `subValAt`-shaped facts, so this is a sibling record, not a reuse. Yield
needed: 5.3 percent of the band. Precedent: same file, same mechanism, minus 30 s
(`lj-1.62`). Two more reasons this beats every alternative:

- **It prices the pending wiring down.** The band's consumer is the work that remains:
  the discharge of `TwelveAgree`'s 24 hypotheses will instantiate all thirteen rows, and
  today every instantiation restates a 10-to-17-entry telescope. KFacts measured that
  the instantiation site is where telescope cost is paid. The bundle is paid once and
  collected twice: now on the residual, again when the wiring lands.
- **DD4 is served, not traded.** A shared record is more generic structure, stated once;
  the J tower inherits it as it inherits `KFacts`.

Named risks: (i) the failure shape of `lj-1.63` attempt 3 (+17.23 s) was ADDING a module
application layer with abstract arguments; the bundle must change the parameter shape
only and add no application layer, which is exactly what KFacts did. (ii) P-o
(`dev/LESSONS.md`): a record field at a carrier-indexed type can hang the elaborator;
KFacts' membership-typed fields measured fine, but the band's fields include
`⊨`-satisfaction function types, so the probe must include one `subK`-class field before
any roll-out.

**(b) Attack the 42,379 ms `Miscellaneous` directly.** Partly the same answer: the
band's share of `Miscellaneous` is what (a) attacks. The chain's share (13.6 s of growth
at placement, `lj-1.62:104`) already carries the KFacts cure at its site-fact blocks;
what remains there is slot-parameter headers (14 to 16 `Fin n` parameters per chain
module), a class with no measured cure. Do not fund a second pass on the chain.
**INFERRED** on both halves.

**(c) Drop `V.Presentation` from the wing list — dead on arithmetic.** Without it the
wing reads (107.48 - 0.64) / (8,269 - 18) = 106.84 s over 8,251 lines = 0.012949,
still OVER (ceiling 104.92 s, residual 1.92 s). **MEASURED** (arithmetic over the gate's
own rows). Membership stands anyway: the ledger's criterion is structural (a master
outside the `Landmarks` closure whose consumers are wing; the 2026-08-10 correction
added it by exactly that test, `dev/ledger.toml` `[ratio]` block), the module's four
facts all have consumers (`_build/lj-1.63-report.md:85-101`), and the ledger's own
words on the last bucket move: "no progress may be claimed from this row". One stale
footnote for the orchestrator: the ledger comment "imported by V.Collapse and L.Hull
and by nothing else" is out of date; five masters import it today (`V/Collapse:12`,
`L/StageCardinal:23`, `L/BoundedSubset:35`, `L/Hull:28`, `L/Ordinal/SquareLaw:32`).
The criterion's outcome does not change.

**(d) Accept the 2.33 s.** Not available as a steady state: the gate is red on the
aggregate, and the wing is still mid-build. The pending wiring adds seconds at the
chain's measured marginal class (0.045 to 0.047 s/line, `lj-1.62:87-88`), so the
aggregate moves further OVER as the deliverable completes. A cure that returns only
2.33 s leaves nothing for the wiring; this is one more reason to take the band bundle
(the largest identified recoverable mass) over micro-cures.

## 4. Recommendation and the dispatch

**Dispatch a band-bundle build, gated by a one-family probe, and do not dispatch
row-level surgery.** Shape:

1. **Probe (the widest unmeasured term: the band's telescope-elaboration share).**
   Convert ONE row family in place: `PropAgree` + `AndAgree` + `OrAgree`, whose
   eleven-entry core is restated three times (`:3090-3145`, `:3336-3368`,
   `:3386-3418`). Replace the core with one record parameter (include at least one
   `subK`-class field, for P-o). Measure `L.Condensation` cold before/after at the
   gate's caliber, three runs each, same session.
2. **Abort criteria, pre-fixed:** (i) family saving under 0.5 s (pro-rata under the
   band-wide 2.33 s target); (ii) any measured regression; (iii) an elaboration hang or
   heap wall at the record declaration (P-o's signature). On abort, the report prices
   the negative and stops; the fallback lever is the `BinFormAgree`/`UnFormAgree`
   depth-3 lift kit (section 2), ceiling about 1.5 s, which alone does not close the
   residual and should then go to the owner as a re-price.
3. **On GO, roll family by family** (the env-family record next: `keyK`/`envK`/
   `entryK`/`arSubK`/`envInK` across the ten rows that restate them), one gate run per
   family, stop at the first family measuring at or above zero. Never add a module
   application layer (the +17.23 s shape); change parameter shape only.
4. **DD4 line for the brief:** the records are generic, stated once, inherited by the J
   tower; the rows keep their statements and proofs unchanged.

## Ledger of evidence

| claim | status | basis |
|---|---|---|
| Residual = Condensation +18.20 s net of 15.86 s under-run elsewhere | MEASURED | gate rows, arithmetic |
| Band = 44.31 s over 2,196 lines at 0.0202 | MEASURED | `lj-1.64:82-91`, same-session pair |
| Named band rows = 5.8 s; rest is elaboration class | MEASURED (totals) / INFERRED (split) | two profiles agree; no stripped-module profile exists |
| Band restates 10-17-entry telescopes across 13 rows; 591/2,196 header lines; 33 inner applications | MEASURED | working-tree code, counts in section 1 |
| KFacts mechanism cut 30 s / 34.1 s Miscellaneous at the same file | MEASURED | `lj-1.62:85-112` |
| Band bundle returns >= 2.33 s | INFERRED — the probe in section 4 measures it | shape match + precedent |
| Row-level cure of the three rows closes 2.33 s | INFERRED FALSE (arithmetic: 40 pc of 5.845 s needed; only precedented lever tops at ~1.3 s) — sets no verdict alone; the dispatch choice rests on the band evidence above | sections 1-2 |
| Seal / frames / alias regress at this wall | MEASURED | `lj-1.63:149-191`, do not re-run |
| Dropping V.Presentation leaves the wing OVER (1.92 s) | MEASURED | arithmetic over gate rows |
| "P-n floor" label for the band | INFERRED and imprecise; band profile shape is the cure-able class (P-t repeated elaboration), floor is ~5.8 s of named once-payments | sections 1-2 |

## ARCHIVE USED

- `_build/lj-1.64-report.md`, whole. TOOK the band boundary (`:2720-5101`), the 44.31 s
  same-session pair (`:82-91`), the consumer audit (`:59-80`), the three-row profile
  (`:52-57`).
- `_build/lj-1.63-report.md`, whole. TOOK the module profile (`:109-119`), the three
  regressions (`:149-191`), the V.Presentation attribution (`:85-101`).
- `_build/lj-1.62-report.md`, sections 2-3. TOOK the bundle mechanism and its
  Miscellaneous arithmetic (`:85-112`), the chain marginal (`:87-88`).
- `_build/lj-1.60-report.md`, sections 0-1. TOOK the Lift12Out marginal (0.0538) and the
  profile attribution shape.
- `_build/lj-1.58-report.md`, section 2. TOOK Lift12Back's 4.28x and the P-c/R-36
  argument that a seal moves this wall's cost.
- `_build/lj-1.47-report.md`. TOOK "sealing buys the repeats, never the once"
  (`:137-140`) and D-30's consumer-audit limit ("it does not make required content
  cheaper").
- `dev/LESSONS.md`: P-m `:2460`, P-n `:2483`, P-t `:2601`, P-q `:2633`, P-o (record
  field hazard), P-c `:71`, P-i `:203`, R-36 `:808`, R-38 `:829`, I-5 `:1257`, D-30
  `:3255`. TOOK P-t as the band's correct class law, P-n's true signature for the
  contrast, P-o as the probe risk, P-q against any deletion move.
- `scripts/check-ratio.py` header (aggregate doctrine); `dev/ledger.toml` `[ratio]`
  block: bar arithmetic (`ac_baseline_module_rate` 0.011057 at `:2590`, tolerance 1.15),
  wing list (`:2855-2862`), membership criterion and the V.Presentation correction.
- `src/L/Condensation.lagda.md` working tree: the band (`:2720-5101`), `PropAgree`
  (`:3090-3246`), `AndAgree`/`OrAgree` (`:3336-3454`), `NegAgree` (`:3520`), `MemAgree`
  (`:4117`), `ImpLeaf` (`:4218-4326`), `BinFormAgree` (`:5432-5513`), `KFacts`
  (`:5675-5708`).
