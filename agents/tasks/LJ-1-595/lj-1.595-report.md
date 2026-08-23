# LJ-1.595 report: clause (ii) of the level-hood certificate

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO on `defines-cover`; clause (ii) is Devlin's sibling of clause (i) and NOT [LJ-1.578]'s

Written as a skeleton before any Agda beyond W3 and filled as each answer landed
(C-22). No commit, no push. I wrote only inside `agents/tasks/LJ-1-595/`. Agda
ran under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event. Nothing is
postulated, the probe carries `--safe`, there is no hole, and nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**[LJ-1.582] IS NOT IN THE TREE.** `ls agents/tasks/` in this worktree lists no
`LJ-1-582` directory, so nothing of clause (i) was reused and the brief's
alternative ("build clause (ii) alone") is the one in force. I cite no file I
did not open.

## VERDICT

**THE OBLIGATION IS NOT INHABITED.** The meter says so:
`agents/tasks/LJ-1-595/Probe595.agda::defines-cover` returns
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`.
The stop is stated at `agents/tasks/LJ-1-595/review-of-defines-cover.md`.

**THE PROBE IS GREEN AND SEVEN TERMS LAND**
(`agents/tasks/LJ-1-595/runs/p-final.out`, `EXIT=0`, 8.68 s). All seven were
metered by name and return `0 UNRESOLVED of 7`.

| what | `Probe595.agda` | conditional on |
|---|---|---|
| the collapse sends an ordinal to an ordinal | `:145` | nothing |
| W3: the covering ordinal EXISTS at the inner world | `:289` | nothing |
| clause (ii) at an ordinal-valued code | `:324` | nothing |
| clause (ii) from a coded covering ordinal | `:380` | `CodedCover` |
| the ordinal half of clause (ii) is free | `:418` | `InternalCover` |
| **Fact C with no formula at all** | `:439` | `HullCovered` |
| Devlin's ONE matrix gives clause (ii) | `:542` | `Sound` and `Complete` |

## HOW CLAUSE (ii) DIFFERS FROM (i)

**VERDICT: DIFFERENT, AND THE DIFFERENCE IS THE BINDER ON THE INDEX.**
Read them side by side at their own lines. Neither is restated here: the probe
names both at [LJ-1.578]'s module (`Probe595.agda:100-112`).

| | clause (i) `DefinesLevel` | clause (ii) `DefinesCover` |
|---|---|---|
| where | `Probe578.agda:234-240` | `Probe578.agda:244-251` |
| side condition on the code | `IsOrd (HS.C.π (fst (T.val c)))`, `:236` | **none**, `:246` |
| ordinal-hood is | a HYPOTHESIS, about the argument | a CONCLUSION, about the witness (`:250`) |
| what a witness must be | `fst a ≡ Lset (fst (T.val c))`, an EQUATION (`:240`) | a member relation, `fst (T.val c) ∈ˢ Lset (fst a)` (`:251`) |
| the code's role | the INDEX of the level | a MEMBER of the level |
| the index of the level | NAMED by the code, so a constant | NOT named: it is the free variable |
| binder, arity, semantics | `Formula T.Code 1`, `(a ∷ [])`, `T.⊨c` | the same |

**SO ONLY THE FRAME IS SHARED.** The two agree on alphabet, arity, environment
and satisfaction relation; they disagree on every line of content.

**AND DEVLIN SAYS THE RESEMBLANCE IS REAL ONE LEVEL DOWN.** He fixes ONE Σ₀
matrix `Φ(z, v, γ)` (`dev/literature/devlin-II5.md:95-99`) and builds two Σ₁
statements from it: the forward inclusion runs on `∃v∃z φ(z, v, γ)` with the
index FREE (`:102-103`), the reverse inclusion on
`∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)` with the index BOUND (`:107-108`). Clause (i) is
the first, clause (ii) is the second. **They are siblings in the MATRIX and not
in the STATEMENT.**

**THAT IS WHY THE THREE CLAUSES ARE NOT ONE OBJECT.** `[LJ-1.578]` split the
certificate at three consequences (`Probe578.agda:525-534`), and each of the
three hides the matrix behind its own existential, one code at a time. **A
family of index-fixed formulas cannot be put under a binder**, so clause (ii)
does not follow from clause (i), and this task could not use clause (i) even
if `[LJ-1.582]` had landed it. Section 8 of the probe states the repair: with
the matrix itself as the object, clause (ii) falls out
(`shared-gives-clause-ii`, `Probe595.agda:542`, 54 lines including the two
adequacy statements).

## WHAT CLAUSE (ii) COST

**MEASURED. 325 non-blank non-comment lines, 544 lines with comments, and the
last full elaboration is 8.68 s.** The counts are mine, by section:

| section | lines | code lines |
|---|---|---|
| header and imports | 1-61 | 32 |
| S1 W3, the type | 62-91 | 13 |
| S2 the two clauses, taken | 92-114 | 12 |
| S3 `π-ord` | 115-175 | 42 |
| S4 the Δ₀ bridge at the inner world | 176-257 | 42 |
| S5 the covering ordinal exists | 258-299 | 27 |
| S6 clause (ii): the two cases I can pay | 300-384 | 60 |
| S7 where the price sits | 385-459 | 43 |
| S8 Devlin's shared matrix | 460-544 | 54 |

**THE ESTIMATE WAS 190 LINES WITH 45 FOR THE OBLIGATION. THE 45 IS RIGHT AND
THE 190 IS NOT.** `cover-at-ordinal` (`:324-347`) is 24 code lines and
`shared-gives-cover` (`:501-540`) is 40, so a clause-(ii) term at ONE case is
inside the size the brief guessed. The overrun is the two pieces the brief did not know
were owed: `π-ord` (42 lines, no lemma in `src/` carries it) and the Δ₀ bridge
(42 lines, because the hull reads its formulas at the CODE alphabet and `abs₀`
reads them at the stage's, so three relabellings sit between them).

**TIMES, ALL FROM `runs/`.** W3 alone, exit 0: 2.86 s (`runs/w3-2.out`). The
first full check, which built the `[LJ-1.578]` import chain: 68.84 s
(`runs/p-1.out`). Every later check of the whole probe, interfaces warm:
5.97 s, 6.62 s, 7.12 s, 7.38 s, 7.58 s, 8.82 s and 8.68 s; a reload with
nothing changed is 4.22 s. Peak resident set 2.53 GB at `p-1` against the 8 GB
caliber. No wall event.

**AND ON CLAUSE (iii), SAY ONLY WHAT MY OWN NUMBERS SUGGEST.** Clause (iii)
(`Probe578.agda:503-510`) is the same formula read in the COLLAPSE, and
`[LJ-1.578]` already paid its transfer leg (`Probe578.agda:330-337`, 6 lines).
Two of my numbers bear on it and neither is a price. First: `π-ord` and the Δ₀
bridge, 84 of my 325 lines, are about carrying facts between the stage, the
inner world and the collapse; clause (iii) crosses the same two joints, so a
comparable overhead is plausible there. Second: clause (iii) has NO
existential over the index at all (its `δ` is a bound variable of the type, not
of a formula), so the obstruction I hit does not obviously appear in it. **I did
not attempt clause (iii) and I do not price it.**

## RE-MEASURED, BECAUSE A MEASURED CURE DOES NOT TRANSFER (AGENTS.md:45)

The brief ordered `AtStage`'s two hypotheses re-measured here, since
`[LJ-1.562]` paid them at a different formula and a different site
(`agents/tasks/LJ-1-562/lj-1.562-report.md:1-6`). **At this site NEITHER
hypothesis arises.** The formula that carries the ordinal condition is
`isOrdAt` (`src/L/BoundedSubset.lagda.md:795`), its Δ₀ witness is DELIVERED
(`:800`, `Δ₀-isOrdAt`), and it has ZERO constants, so `BoundedFo` (the
hypothesis `[LJ-1.562]` priced) has nothing to bound. What the site costs
instead is the relabelling chain `ord-read` (`Probe595.agda:245`): the hull
reads at the code alphabet, `abs₀` reads at the stage's, and `Amb` reads at
the empty one. **One measurement inside it is worth passing on: `⊨-map` leaves
its `fst` unsolved as a meta and the projection must be NAMED**
(`Probe595.agda:218`, `prj`); with `fst` written bare the file fails with
`UnsolvedMetaVariables` (`runs/p-4.out`).

## C-42, THE SWEEP

The refutation names one site, so the shape was swept for. **The phrase
"defined the same way" has exactly ONE origin and TWO restatements, and no
third site carries it.** Origin: `agents/tasks/LJ-1-578/Probe578.agda:242-243`.
Restatements: `agents/tasks/LJ-1-578/review-of-cohyps-supplied.md:28` and this
task's brief, `agents/tasks/LJ-1-595/LJ-1.595.md:24` and `:71`. The command is
`grep -rn "defined the same way" agents/ dev/ src/`. **The shape did not
spread, so no cure is owed anywhere else.**

## D-10, BEFORE ANY AGDA

The brief ordered the resemblance priced before the proof, and it was: the two
clauses were read at `Probe578.agda:234-240` and `:244-251` and the table above
was written before the probe's first line. **The finding held up: the
difference is real, and it is what this task then measured.** The one thing
D-10 did not catch and the Agda did: the difference is not merely a shape
difference but a BINDER difference, which is why no amount of clause (i)
supplies clause (ii).

## WHAT THE NEXT BRIEF SHOULD DECIDE

1. **Clause (ii) may be a detour.** `Facts.Covered` (`Probe578.agda:130-136`)
   is TRUNCATED. `factC-from-hull` (`Probe595.agda:439`) derives it from
   "every hull member sits in a level indexed by an ordinal OF THE HULL", with
   no formula, no satisfaction and no collapse condition: `π-ord` discharges
   the collapse half from the external one. **If the certificate exists only
   to buy Facts A, B and C, clause (ii) should be replaced by `HullCovered`.**
2. **If the certificate is kept, state it at the MATRIX.** `Shared`
   (`Probe595.agda:483-544`) is that shape and clause (ii) falls out of it.
   **Whether clause (i) also falls out I did not measure**: it needs the index
   substituted by a constant, a renaming this task did not price. That is the
   one open question I leave.
3. **`CodedCover` (`Probe595.agda:353`) is the whole residue of clause (ii)**
   at a non-ordinal value: a covering ordinal NAMED BY A CODE. The only
   code-making route in the tree is the Skolem constructor `wit`
   (`src/L/Hull.lagda.md:72-74`), which takes a formula over the empty
   alphabet, so the residue leads straight back to the level formula read at
   the stage. The tree proves the level graph at the CLASS `L`
   (`src/L/Hierarchy.lagda.md:334`, at the satisfaction opened at
   `src/L/Hierarchy.lagda.md:78`) and not at a stage, and `[LJ-1.578]`
   records the stage reading as not built anywhere
   (`agents/tasks/LJ-1-578/lj-1.578-report.md:50`).

## W3, THE WIDEST UNMEASURED TERM

**GO, AND IT IS STRONGER THAN A TYPE.** The brief asked whether the covering
ordinal STATES at the stage's inner world, estimated about 15 lines and under
2 minutes, and ordered it typechecked ALONE first. It states: the slice is
`agents/tasks/LJ-1-595/runs/W3.agda:52-58`, 13 code lines, exit 0 in 2.86 s
(`runs/w3-2.out`; `runs/w3-1.out` is the exit 42 before it, an import name that
does not exist). **The estimate was right.**

**AND THE OBJECT IS NOT MERELY STATEABLE, IT IS FREE.** `covering-ordinal`
(`Probe595.agda:289`) INHABITS that type for every code, unconditionally.
`Lset-out` names an index below `lam`, one successor covers there, `succλ`
keeps the successor below `lam`, and `π-ord` carries ordinal-hood across the
collapse. **So the brief's question resolves the other way round from the way
it was posed: the difficulty of clause (ii) is not the object, it is the
FORMULA that must select the object.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **not read.** It indexes dispatches by
  code, and this task's two predecessors were reachable in the live tree.
- `archive/dev/JOURNAL.md`: **declined.** A history, and the Boundary says a
  live document carries none; nothing here needed one.
- `archive/dev/JOURNAL-archived.md`: **declined**, same reason.
- `archive/dev/ORCHESTRATION.md`: **not used.** It is the archived operating
  document; this task's rules came from the five files the program cats.
- `archive/dev/DD-archived.md`: **not used.** The `DD` series is set aside in
  that form, and no clause of this task rests on one.

**NO HIT WAS NEEDED.** The evidence this task turned on is live: the
predecessor's probe, the `src/` chapters it names, and one literature file.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it decided the finding.**
  `:96` reads

      > (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

  and `:108` reads

      statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally

  The first is the shared matrix; the second is clause (ii) with the index
  bound. Line `:99` is clause (i)'s own form, which is the brief's premise 4.
- `dev/literature/truncation-and-selection.md`: **not read.** The truncation
  question this task met (`Facts.Covered` is truncated, so no selection is
  owed) was settled by reading the type at `Probe578.agda:130-136`, and a
  general treatment would not have changed that reading.
- `dev/literature/digest.md`: **not used.**
- `dev/literature/level-formula-slot-roles.md`: **not read**, and this is the
  one decline I am least comfortable with: its name suggests it holds the slot
  order of the level formula, which is what section 8's `Sound` and `Complete`
  fix by hand. I chose Devlin's own order (`z`, `v`, `γ`) from the quoted
  source instead of a second convention. **The next brief should check my
  order against that file.**
- `dev/literature/primary-sources.md`: **not used.**
