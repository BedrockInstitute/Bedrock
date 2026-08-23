# LJ-1.595 review-of-1: adversarial review of the LJ-1.595#1 return

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

## WHAT I ATTACKED, AND ONE MISSING RECORD

The return under attack is the work of the `coder` slot: the report
`agents/tasks/LJ-1-595/lj-1.595-report.md`, the stated NO-GO
`agents/tasks/LJ-1-595/review-of-defines-cover.md`, the probe
`agents/tasks/LJ-1-595/Probe595.agda`, the W3 slice
`agents/tasks/LJ-1-595/runs/W3.agda`, and the transcripts under
`agents/tasks/LJ-1-595/runs/`. I read them against the brief
`agents/tasks/LJ-1-595/LJ-1.595.md`. The critic is not the author. The
invariant holds.

`dev/pod/transitions/2026-08.jsonl` in this worktree carries no line
with `"task": "LJ-1.595"`. The file ends at seq 158, task `LJ-1.399`,
stamp 2026-08-19 (`dev/pod/transitions/2026-08.jsonl:157`). Model,
effort and `heads_sha256` are therefore not on the worktree record. The
six facts come from the accept arm. I report the absence. It is a
program gap. It is not a defect of the return.

## THE SIX FACTS OF THE INSTANCE

From `agents/tasks/LJ-1-595/runs/accept-1.out`:

- `Probe595.agda` rc 0, 2.95 s (`accept-1.out:16`)
- `runs/W3.agda` rc 0, 2.19 s (`:17`)
- conjuncts 1 to 6 held (`:10-15`)
- exit 0, error class none (`:23-24`)
- obligations delta 0, obligations open 1, probe not red
  (`:21`, `:25`, `obligations_probe_red: false`)
- heap wall false, in-fence lines 0, unbound_vacuous true (`:25`)
- 16 changed files, all under `agents/tasks/LJ-1-595/` (`:18`, `:25`)
- caliber `-A64m -I0 -M4g`, tier wide (`:5-6`)
- `agda slots during 1` (`:7`), `concurrency: 1` (`:25`)

`unbound_vacuous: true` here means conjunct 4 saw no `src/` master
change (`scripts/pod/accept.py:214-215`). It does not mean the
obligation name is missing. The obligation `defines-cover` is missing,
and the accept arm records that as delta 0 with one name still open.

## QUESTION 1. DOES THE VERDICT LINE MATCH THE BODY

Yes. The line is `agents/tasks/LJ-1-595/lj-1.595-report.md:6`:

> verdict: NO-GO on `defines-cover`; clause (ii) is Devlin's sibling of clause (i) and NOT [LJ-1.578]'s

The same stop stands at
`agents/tasks/LJ-1-595/review-of-defines-cover.md:5-8`. The body
carries each part of that line.

- The obligation is not inhabited. No binder named `defines-cover`
  stands in `Probe595.agda`. The witness meter today, via the brief,
  returns `missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`,
  `probe_red=False`. Accept agrees: delta 0, open 1
  (`accept-1.out:21`, `:25`).
- The probe is green. `runs/p-final.out:22` is `EXIT=0`, 8.68 s.
  Accept re-measured the same file today at rc 0, 2.95 s
  (`accept-1.out:16`).
- Clause (ii) as `[LJ-1.578]` wrote it is `Cert.DefinesCover` at
  `agents/tasks/LJ-1-578/Probe578.agda:244-251`. The probe takes that
  type by name (`Probe595.agda:107-112`) and does not inhabit it at a
  general code.
- The body says the two clauses share alphabet, arity, environment and
  satisfaction, and disagree on every line of content
  (`lj-1.595-report.md:48-59`). I opened both types. Clause (i) at
  `Probe578.agda:234-240` takes `IsOrd (HS.C.π (fst (T.val c)))` as a
  hypothesis and concludes `fst a ≡ Lset (fst (T.val c))`. Clause (ii)
  at `:244-251` takes no side condition on the code and concludes
  `IsOrd (HS.C.π (fst a))` and `fst (T.val c) ∈ˢ Lset (fst a)`. The
  index of the level is a constant in (i) and the free variable in
  (ii). The table matches the types.
- The body says they are siblings in Devlin's matrix and not in
  `[LJ-1.578]`'s split (`review-of-defines-cover.md:16-24`,
  `lj-1.595-report.md:64-77`). That is the second half of the line.
  Question 3 records a slip in that Devlin reading. The slip does not
  make the line disagree with the body: line and body say the same
  thing.

W3 closed. The type at `runs/W3.agda:51-56` is the covering ordinal
with the formula removed. `CoverAt.covering-ordinal` inhabits it at
`Probe595.agda:289`. `runs/w3-2.out:22` is `EXIT=0`, 2.86 s. Accept
re-measured `W3.agda` at rc 0, 2.19 s (`accept-1.out:17`). The body
does not claim the obligation from W3, and it is right not to: W3 is
the object, and clause (ii) asks for a formula that selects it
(`review-of-defines-cover.md:41-44`).

The body also refuses a stronger claim it did not earn. It does not
say `DefinesCover` is false. It says the general term is not supplied,
and it names the hypotheses under which partial terms land
(`review-of-defines-cover.md:56-69`). No term of a negation was
built. The refusal is correct.

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A FILE:LINE THAT RESOLVES TODAY

Yes for the claims that carry the NO-GO. Two satellite claims do not
reproduce as written. Neither moves the verdict.

The NO-GO's own numbers resolve today.

- `Probe578.agda:244-251` is `DefinesCover`. `Probe578.agda:234-240`
  is `DefinesLevel`. `Probe578.agda:525-534` is the three-clause
  `Certificate`. `Probe578.agda:130-136` is `Covered`, truncated.
- `body-is-clause-ii` at `Probe595.agda:316-318` is the identity, so
  `CoverBody` is `DefinesCover` at one code. `cover-at-ordinal` at
  `:324` inhabits that type when the code's value is an ordinal.
  `cover-from-coded-all` at `:380` inhabits `DefinesCover` from
  `CodedCover`. `shared-gives-clause-ii` at `:542` inhabits it from
  `Sound` and `Complete`. None of those three is a term of
  `DefinesCover` with no extra hypothesis.
- `π-ord` at `Probe595.agda:145` is general in the carrier. `ord-out`
  at `:251` reads ordinal-hood off `isOrdAt`. `isOrdAt` is
  `Formula (⊥* {ℓ-suc ℓ}) 1` at
  `src/L/BoundedSubset.lagda.md:795-798`, so it has zero constants.
  `Δ₀-isOrdAt` is delivered at `:800-803`. The `[LJ-1.562]` site is
  a different formula (`agents/tasks/LJ-1-562/lj-1.562-report.md:1-6`).
  The brief ordered those two hypotheses re-measured here. At this
  site they do not arise. What arises is the relabelling chain
  `ord-read` at `Probe595.agda:245`. `runs/p-4.out:3-6` is
  `[UnsolvedMetaVariables]` at the then-current `⊨-map` call. That
  is the measurement they pass on.
- `Lset-only` is at `src/L/Hierarchy.lagda.md:334`. Its satisfaction
  is `AbsL` at `:78`: `module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`.
  That is the class `L`, not a stage. `GraphAgree` as a type stands in
  probes and not in `src/`: `agents/tasks/LJ-1-570/Probe570.agda:289-290`,
  recorded at `agents/tasks/LJ-1-578/lj-1.578-report.md:50`.
- `Code` has `base` and `wit` only, at `src/L/Hull.lagda.md:72-74`.
  `wit` takes `Formula (⊥* {ℓ}) (suc k)`. That is the code-making
  route they name.
- `[LJ-1.582]` is not in this worktree. `ls agents/tasks/LJ-1-582`
  returns no directory.
- Line counts recompute. `Probe595.agda` has 544 lines, 325 non-blank
  non-comment. The section code counts they printed
  (`lj-1.595-report.md:84-94`) recompute exactly: 32, 13, 12, 42, 42,
  27, 60, 43, 54.
- Peak resident set at `p-1` is 2527182848 bytes
  (`runs/p-1.out:16`), which is 2.53 GB in SI units against the 8 GB
  pane caliber written on that file (`:1`). `p-1` is `EXIT=0` at
  `:33`, 68.84 s at `:15`.
- W3 alone is 2.86 s, `EXIT=0` (`runs/w3-2.out:4`, `:22`).
  `runs/w3-1.out` is `EXIT=42` at an import that does not exist
  (`:14-17`, `[NoSuchModule]`).
- Nothing is postulated. The word `postulate` occurs in
  `Probe595.agda` only in the comment at `:10`. The file carries
  `--safe` at `:1`.

**S1. The seven-name meter sentence does not reproduce under the names
as printed.** `review-of-defines-cover.md:58-69` lists seven terms and
says they return `0 UNRESOLVED of 7`. No transcript of that meter
stands under `runs/`. Metered today, the seven names as that table
writes them return `1 UNRESOLVED of 7`, `probe_red=False`. Six pass.
`Shared.shared-gives-clause-ii` is `missing exit=42 [NotInScope]`,
because `Shared` is not a top-level module. The term that the table
points at `:542` does exist: `CoverAt.Shared.shared-gives-clause-ii`
returns `pass exit=0`. The Agda is there. The meter sentence as
written is not. This is not the obligation. The obligation meter
reproduces.

**S2. The warm-time list mixes red runs, and one time has no file.**
`lj-1.595-report.md:106-108` lists 5.97 s, 6.62 s, 7.12 s, 7.38 s,
7.58 s, 8.82 s and 8.68 s as later checks of the whole probe with
interfaces warm. Those are `p-3` through `p-final`. `p-3.out` is
5.97 s at `:8` and `EXIT=42` at `:26`, with
`[UnsolvedMetaVariables]` at `:4`.
`p-4.out` is 6.62 s and `EXIT=42` (`:7`, `:25`). The report names
`p-4` as a red run in the `AtStage` section (`:136`). It does not
name `p-3` as red in the time list. The sentence `a reload with
nothing changed is 4.22 s` has no file under `runs/`. `p-2.out` is
3.75 s at `:10` and `EXIT=42` at `:28`, with `[NotInScope]` on
`mapFo` at `:4`, and is not in the list. The green finish they name
is real: `p-final.out` is 8.68 s at `:4`, `EXIT=0` at `:22`. Accept's 2.95 s is a later green recheck at a
different caliber (`-M4g` at `accept-1.out:5`, against the pane
`-M8g` written on `p-final.out:1`). The times that carry the NO-GO
are the green ones. The mixed list is a defect of the time
paragraph, not of the verdict.

Two precision notes. Neither is load-bearing.

- `runs/W3.agda:52-58` is cited for the W3 type
  (`lj-1.595-report.md:187`). The file has 56 lines. The type is at
  `:51-56`. The "13 code lines" figure is the S1 count of
  `Probe595.agda` (`:62-91`), not the W3 slice. W3 still typechecks.
- The C-42 grep for `"defined the same way"` does not hit
  `Probe578.agda:242-243`, because the phrase is split across a line
  break and `DEFINED` is uppercase. They still named that origin, and
  the two restatements they name resolve:
  `agents/tasks/LJ-1-578/review-of-cohyps-supplied.md:28` and
  `agents/tasks/LJ-1-595/LJ-1.595.md:24`. I re-ran the grep over
  `agents/`, `dev/` and `src/`. No third live site carries the
  phrase. The sweep of the phrase holds. C-42 asked for the shape.
  The shape they measured is the two types, and those have one origin.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

No. Three gaps. None of them inhabits `defines-cover`, so none of them
moves the verdict.

**F1. Devlin's reverse-inclusion statement is Fact C, not clause (ii).**
The stop file says the two clauses are Devlin's two Σ₁ statements,
and that the difference is which variable is bound
(`review-of-defines-cover.md:16-19`, citing
`dev/literature/devlin-II5.md:102-103` against `:107-108`).
Line `:103` is the forward statement `"∃v∃z φ(z, v, γ)"`, with γ a
parameter. Line `:108` is the reverse statement
`"∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)"`, with γ bound. Clause (ii) as
`DefinesCover` has the index free: the formula's free variable is the
covering ordinal, and the hull member is a constant
(`Probe578.agda:246-251`, `Probe595.agda:308-314`). The probe itself
writes that correction at `:495-499` and implements `coverFo` with
the index free (`:498-499`). The reverse-inclusion *statement* is the
truncated covering fact: `Facts.Covered` at `Probe578.agda:130-136`.
They prove that fact from `HullCovered` with no formula
(`Probe595.agda:439`). That is the right reading of Devlin's reverse,
and they already have it, under a different name.

The identification is inherited. The brief says the three clauses are
Devlin's own chain (`LJ-1.595.md:27-28`). The predecessor
`review-of-cohyps-supplied.md:32-33` already said clause (ii) is the
reverse inclusion's statement at `:107-108`. The brief did not
foreclose a GO. A GO still required a term of `DefinesCover`. The
Agda obstruction is independent of the name of Devlin's line: a
family of index-fixed formulas, one code at a time, does not put the
index under a binder, so clause (i) does not give clause (ii). That
argument stands at the two types.

**F2. The tree's Φ is not a missed inhabitant, and they did not name
its alphabet.** `LsetGraphAt` is `GraphAt` renamed at
`src/L/Coding/Sequence.lagda.md:349`. `GraphAt` is
`Formula S n` at `:291`. The hull language of clause (ii) is
`Formula T.Code 1` (`Probe578.agda:247`). Those alphabets do not
meet. `isOrdAt` embeds because it is `Formula (⊥* _) 1`. The graph
does not. The return names the class-`L` satisfaction of `Lset-only`
and the missing stage reading `GraphAgree`. It does not name this
third block. Naming it would have made the residue sharper. It would
not have paid `defines-cover`. Building `Sound` and `Complete` at
the Code alphabet is the matrix they left open
(`review-of-defines-cover.md:80-85`). The brief forbade clauses (i)
and (iii) (`LJ-1.595.md:85`) and estimated 45 lines for the
obligation. That matrix is a different object.

**F3. No missed cure inhabits the obligation.** I looked for one.

- Naming `cover-at-ordinal` as `defines-cover` fails: `DefinesCover`
  quantifies over every code, and `cover-at-ordinal` needs
  `IsOrd (fst (T.val c))`.
- Naming `cover-from-coded-all` as `defines-cover` fails: the type
  still has `CodedCover` as a hypothesis (`Probe595.agda:380-382`).
- A formula that is only `ordFo` fails adequacy: not every ordinal
  covers a given member.
- `covering-ordinal` shows the object exists in the stage's inner
  world, unconditionally (`:289`). Adequacy of clause (ii) is
  universal in the witnesses of a formula. Existence of some covering
  ordinal does not give that formula.
- `wit` cannot name the covering ordinal without a formula over the
  empty alphabet (`src/L/Hull.lagda.md:74`), which is the same missing
  graph, read at a different alphabet.
- Postulating `Sound` and `Complete` is forbidden (`LJ-1.595.md:87`).

W3 asked whether the covering ordinal states at the inner world. It
does, and they inhabited it. The brief's question then resolves as
they say: the difficulty of clause (ii) is the formula, not the
object (`lj-1.595-report.md:195-197`). Clause W3 of this slot asks
whether a mathematician's return named the term and the probe. This
return is a coder's. The brief named the term. The coder wrote the
slice and the inhabitant. That duty is met.

W2 holds at `CollapseOrd`: `π-ord` is proved at a generic carrier
(`Probe595.agda:127-145`) and instantiated at the hull's collapse
(`:204`). They did not duplicate the lemma at the hull.

The next brief they ask for is still the right one: either replace
clause (ii) by `HullCovered` if the certificate exists only to buy
Facts A, B and C, or restate the certificate at the matrix
(`review-of-defines-cover.md:71-85`). Whether clause (i) also falls
out of `Shared` they did not measure. That open question stands.

## VERDICT

`verdict: upheld`. The obligation is not inhabited. The stop is
stated. The measurement of the obstruction reproduces. The three
gaps above are defects of the Devlin label, of one meter sentence,
and of one time paragraph. They do not supply `defines-cover`.

This file and exit 0 close the task under row `sys-critic-upheld-no-go`
(`dev/pod/table.toml:4307-4321`): exit 0, this path, obligation still
open.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: **declined.** Line 1 reads

      > # ARCHIVED 2026-08-20

  It is a retired history. The Boundary says a live document carries
  none. The return under attack is live under `agents/tasks/LJ-1-595/`.

- `archive/dev/ORCHESTRATION.md`: **not used.** Line 1 reads

      > # ORCHESTRATION: the orchestrator's operating rules

  This slot's rules came from the five files the program cats. The
  archived operating document does not bear on whether `defines-cover`
  is inhabited.

- `archive/dev/DD-archived.md`: **READ, and it is the lens.** `:35`
  carries DD25, including

      > The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.

  Those four found the answers above. The three questions written here
  are section 6.6's list at `dev/memos/LJ-4-pod-program-design.md:2853-2858`.

- `archive/dev/PLAN-archived.md`: **declined.** Line 1 reads

      > # ARCHIVED 2026-08-20

  It is the construction registry as of archival day. Nothing in it
  is current, and this review is of a live NO-GO.

- `dev/ARCHIVE.md`: **not used.** Line 1 reads

      > # ARCHIVE.md: the archive registry

  It registers retired modules. This task does not retire one.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it is the check on the
  sibling claim.** `:96` reads

      > (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

  `:99` is Devlin's (b), the brief's premise 4. `:103` reads

      > statement "∃v∃z φ(z, v, γ)" is transferred from L_α to X (Σ₁-elementarity,

  and `:108` reads

      > statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally

  F1 above takes those two statements as they stand: the reverse binds
  the index. Clause (ii) frees it.

- `dev/literature/BIBLIOGRAPHY.md`: **not used.** Line 1 reads

      > # Bibliography for the rud route

  It is a citation list. It does not carry the II.5 chain.

- `dev/literature/digest.md`: **not used.** Line 1 reads

      > # Digest: the orthodox form of the rud route, pinned from the collected literature

  The chain at issue is the II.5 condensation paragraph, which is in
  `devlin-II5.md`.

- `dev/literature/geology.md`: **declined.** Line 1 reads

      > # Geology dossier: set-theoretic geology sources and the five questions

  Geology is not the condensation chain and not clause (ii).

- `dev/literature/devlin-errata.md`: **READ, and it does not touch
  II.5.** `:41` reads

      > section 9 of Chapter I and section 1 of Chapter VI."

  The documented error classes are confined there. They do not
  undercut the II.5 lines the return cites. The binder slip in F1 is
  in the return's mapping, not in Devlin's text.
