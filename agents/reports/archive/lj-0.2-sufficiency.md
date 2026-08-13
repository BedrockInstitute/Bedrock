# LJ-0.2 Sufficiency Audit of the Route Switch

Task code `[LJ-0.2]`. Branch `two-tower-bridge`. Read-only.

**Audit base.** I audited the 13-commit switch at `faf02fc..2391f05`. The tree
moved during the audit. Commit `48eef39` landed under `[LJ-0.2]` and
compressed PLAN section 11 into 31 rows, with the 96 retired rows archived to
`dev/STATUS-archived.md`. The working tree carries uncommitted repairs: a
rewritten section 0, `scripts/check-timing.py` (the D3 downgrade and D30 text
drop) and `scripts/ledger.py` (the D2 stderr banner). I report the state I
read and flag the repairs as in flight. After my read, further edits moved
the decision, journal, status and task archives to `archive/dev/` and the
dashboard tooling to `archive/tooling/`. My citations use the paths and
lines at read time. I re-verified B1, N3, N4, N5 and N6 against the current
tree; they still hold.

## 1. VERDICT

The switch is NOT yet sufficient to start phase 1, but the blockers are
LJ-0.1's tracked repairs, not new sufficiency gaps. The standing brief clause
at `dev/ORCHESTRATION.md:157-159` still pins the retired route R2' into every
phase-1 brief, and the gate stays RED until the AGENTS.md word cap and the
dashboard crash land. Once those repairs land, the sufficiency gaps I found do
not block `LJ-1.1`. They sit in the phase-2 and phase-3 machinery and in
informational documents. The switch is sufficient in structure. It is not
complete as a route.

## 2. BLOCKING GAPS

What must change before `LJ-1.1` is dispatched. LJ-0.1 already names two of
the three items; I list them because they gate the dispatch, and I mark them.

### B1. The standing brief clause states the retired route (tracked, LJ-0.1 D6)

`dev/ORCHESTRATION.md:157-159`, section 3, the "DD2 and DD5, what is ruled and
what is open" clause, states "Ruled: the campaign route, R2' with the trophy
stated in L". R2' is the retired internalization route
(`dev/DECISIONS-archived.md:47`). The live route is DD2
(`dev/PLAN.md:152`). No phase-1 brief can carry a correct ruled-and-open
header until this line changes. The smallest fix: replace R2' with DD2's
content, two towers, J through rud, both trophies on the bridge, and keep the
"Open: how to walk it" half of the clause.

### B2. The gate and the board are broken (tracked, LJ-0.1 D1 and D2)

`make check` fails on the AGENTS.md word cap (`scripts/check-dev-docs.py:105`),
and `make dashboard` crashes on the ledger banner
(`scripts/dashboard.py:274`). The orchestrator's return audit uses both.
Repair is under way in this worktree: `scripts/ledger.py` now prints the
banner to stderr. The AGENTS.md cut and the dashboard fix are still owed.

### B3. The LJ rows carry retired T labels (tracked, LJ-0.1 D17)

`dev/PLAN.md:381-399` names `T1`, `T3`, `T5`, `T6`, `T7`, `T12`, `T15`, `T16`
and `T19`. These resolve against the archived index and name the wrong rows.
A brief-writer who copies the row text sends the agent to a retired task. The
smallest fix is LJ-0.1's table: translate each label to its `LJ-<phase>.<step>`
code.

## 3. NON-BLOCKING GAPS

Ranked. None blocks phase 1. Each states the file and section, what is
missing, why it matters, and the smallest fix.

### N1. The reuse constraint has no measure, no declaration and no checker

DD4 (`dev/PLAN.md:153`) makes maximum shared code the route's core constraint.
Nothing measures sharing today. The latent machinery exists:
`scripts/ledger.py:213` computes import closures, and the trophy-split
partition (`dev/ledger.toml:246-360`, `scripts/ledger.py:262-398`) separates
ac-only, gch-only and shared parts. It is suspended and its roots name
archived modules, so it measures the retired route's wing partition, not the
two proofs on the bridge. No current document defines what "shared" means for
the two proofs, and no task row and no checker measure it. `LJ-3.8`
(`dev/PLAN.md:398`) measures lines and seconds only. The consequence: the
route's core constraint is a wish by the project's own standard, because a
rule with no enforcement point is a wish (DD19, `dev/PLAN.md:162`). The
smallest fix: declare the two proofs' closure roots in a `[reuse]` block in
`dev/ledger.toml`, and extend `ledger.py` to report shared lines and the
ratio. This gates `LJ-3.1`'s judgment and `LJ-3.8`'s pass-or-fail, not
phase 1.

### N2. The DD2 target skeleton is named as owed but owned by no row

`dev/PLAN.md:167` heads section 4 "Target skeleton (OWED a re-derivation for
DD2)". No task row delivers that re-derivation. `LJ-3.1`
(`dev/PLAN.md:391`) produces a reuse map, which is the skeleton's shared-core
half, but the row does not say it replaces the section 4 debt. Until then no
document states the two-tower tree's shape: L tower, J tower, bridge, shared
core. The smallest fix: amend the `LJ-3.1` row to name the section 4
re-derivation as part of its deliverable.

### N3. ORCHESTRATION section 5.1 describes the retired resume order

`dev/ORCHESTRATION.md:219-222` orders "the bridge landing (below-lim), then
the choice re-home, then AC on surviving machinery; and the StepInL rewrite,
then W3, then W7's residue and the GCH sentence", resumed "when the exit
condition is met". Every named item belongs to the retired route, and the
exit condition is D30's freeze, which the rewritten section 0 now closes. The
flowchart this section points to is built from the retired `[[lever]]` and
`[[owed]]` rows (`scripts/dashboard.py:14-15`, `:324-361`). The new route's
order lives only in the PLAN task-index preamble (`dev/PLAN.md:351-357`).
The smallest fix: rewrite the section for the LJ phase barrier, or mark it
superseded and point at the task index.

### N4. The ledger's dispatch queue still lists the retired route

`dev/ledger.toml:1014-1212` carries twelve `[[owed]]` rows: `ac-leg`,
`ac-rehome`, `bridge-landing`, three archival arms, five `gch-w*` rows, and
`stepinl-rewrite-owed`, with statuses `frozen`, `exempt` and `delivered` from
the retired freeze. The
board's "what is next" column reads this queue
(`dev/ORCHESTRATION.md:296-297`, `scripts/README.md:349`). No `LJ` row
appears there. A reader of the owner's board sees a retired dispatch queue.
The smallest fix: repoint the board at the PLAN task index, or add the LJ
rows and mark the old ones as history.

### N5. dev/README.md lists the revoked two-caliber discipline

`dev/README.md:10-12` describes PLAN.md as carrying "the two-caliber
discipline". DD8 (`dev/PLAN.md:155`) and section 6.2 (`dev/PLAN.md:239`)
revoke it. The smallest fix: name DD8's single best-effort projection
instead.

### N6. scripts/README.md describes retired machinery in four sections

The switch never opened this file. It is the canonical home for what each
script does (`AGENTS.md:103`). Four sections describe the retired route's
declarations: `ledger.py` ("minus the D18-booked retirement set", "endpoint
in both calibers", `scripts/README.md:118-119`); `deletion-test.py` ("D36's
judgment", "under 16,000", `:136-138`); `check-tree.py` ("a SURVIVING master
importing a chapter D18 retires", `:199-201`); and `dashboard.py` (five
panels reading `[[remaining]]`, `[[owed]]`, `[[hot]]` and the endpoint in
both calibers, `:335-349`). Each describes a suspended flag or an archived
code. The smallest fix: rewrite those sections for the suspended state.
The missing `check-ratio.py` section is LJ-0.1 D27, already reported.

### N7. The consolidation dropped no operative rule; one clause needs care

I compared every archived D row against the 15 DD rows. Every rule the new
route needs has a home: D22 to DD8, D26(A) and D26(C) to DD5 and DD8, D29 to
DD4, D23 and D37 to DD17, D27 and D28 to DD15, D17 and D20 to DD13, D24,
D34 and D35 to DD19, D19 to DD2, D2 and D13 to DD9, D6 and D7 to DD11, D4 to
DD22, D21 to DD23, D1 to DD1, D16 to DD13, D33 and D36 to DD5 as
diagnostics. D31 and D32 are spent. D30's wall is replaced by DD24 and DD5,
and its freeze is closed by the rewritten section 0. The one near-miss:
D26(B), "the technique is empirical and a working direction is not a ruling"
(`dev/DECISIONS-archived.md:47`), survives only inside the ORCHESTRATION
clause whose "Ruled:" half is stale (B1). The repair of B1 must keep the
"Open: how to walk it" half, or the principle loses its home. The warrant
discipline of D20(B), a kept chapter needs a named open goal and a dated
expiry, is dropped from DD13; LJ-0.1 judged that acceptable, and I agree,
because the new route keeps no chapter on a survivor-consumes warrant yet.

### N8. The phase-1 starting line has two small holes

`dev/PLAN.md:385`, `LJ-1.6`, builds the cardinality of a stage. The restored
`src/` has no cardinal machinery: `git ls-files src/` shows no `L/Cardinal*`
and no `FOL/Count`. The archive holds `L/Cardinal.lagda.md`,
`L/CardinalPredicates.lagda.md`, `L/CardinalCount.lagda.md` and
`FOL/Count.lagda.md` under `archive/rud-route/`. `LJ-1.4`
(`dev/PLAN.md:383`) carries an explicit "ARCHIVE FIRST" pointer for the
equally absent collapse, so the omission in `LJ-1.6` is an inconsistency,
not a policy. The recon will find it, so this does not block. The second
hole: the wing's fate after `LJ-2.1` measures it is unstated. The wing is a
measurement instrument (DD24, `dev/PLAN.md:165`), and nothing says whether
it stays in `src/` or is archived once the benchmarks are recorded. That
choice changes how the recon prices the wing's engineering. The smallest
fix: add the archive pointer to `LJ-1.6`, and let the `LJ-1.1` brief answer
the wing's fate.

## 4. WHAT I CHECKED AND FOUND SUFFICIENT

The DD table, 15 rows at `dev/PLAN.md:151-165`. I read every row. Each row
states its own minimum content. The consolidation paragraph
(`dev/PLAN.md:147`) accounts for every merged and revoked code, and
`scripts/check-rule-ids.py` accepts the merged codes by design. DD2, DD4,
DD5, DD8, DD17, DD23 and DD24 state the new route, its two constraints, its
bar and its freeze. The per-trophy split and the AC cap survive only as
diagnostics (DD5), which matches the suspension flags.

The task index, `dev/PLAN.md:348-399`. The phase barrier is stated
(`:351-357`), the rows are one per code and under the 200-character cap, and
the dependency logic holds once the D17 labels translate. The MASTER table,
compressed by `48eef39`, now states that `[L3]` is superseded wholesale by
the LJ series and that `[L4]` through `[L8]` are gated on both trophies
inside both constraints.

Section 0. The working-tree rewrite states DD2, DD5, DD24, DD23, the four
archives, and the closure of the retired check-cost freeze. It resolves
LJ-0.1 D10. It is uncommitted at the time of writing.

AGENTS.md. The "THE ROUTE" block (`AGENTS.md:162-170`) states DD2 and DD5
correctly. The "Where the rules live" table is current except the section 0
pointer, which the section 0 rewrite repairs.

dev/ledger.toml. The suspension flags and the re-arm condition are current
(`:83-109`, `:526-528`). The `[ratio]` block carries a measured baseline with
its protocol (`:2291-2328`). The `[timing]` block is flagged as the retired
route's record (`:1331-1336`). `scripts/check-ratio.py` exists, is staged,
reads `ratio.gch_wing` (`dev/ledger.toml:2328`), and refuses to invent a
baseline. Its warm-versus-cold and gate-placement defects are LJ-0.1 D4 and
D5.

dev/rules.toml. The recon bundle includes D-26, the J-tower and L-tower
fault line (`dev/rules.toml:47-49`), which the new route needs for `LJ-3.4`
and `LJ-3.5`.

Route-neutral documents. I scanned `README.md`, `CONTRIBUTING.md`,
`CLAUDE.md`, `src/README.md`, `archive/README.md`, `dev/STYLE-agda.md`,
`dev/STYLE-i18n.md`, `dev/GLOSSARY.md`, `dev/glossary.toml`, `docs/*`,
`site/README.md` and `.github/workflows/README.md` for route terms. None
assumes the retired route. The README first-goal text omits the AC trophy,
and that debt is registered at `dev/PLAN.md` row L4.2. The memos and the
literature folder describe the retired route by design; their status headers
mark them superseded. Two headers carry a stale citation: `dev/memos/route-tree.md`
and `dev/memos/source-material-survey.md` both name the revoked two-caliber
discipline as current. I list these under preferences.

What I did not reach. I did not read `dev/JOURNAL-archived.md` through; the
brief allows that, and S3 and S4 did not raise a question the other archives
could not answer. I read targeted entries of `dev/LESSONS.md`, not the whole
file. I did not read the bodies of the 72 archived modules, the `docs/zh`
and `docs/ja` translations, or the `_build` reports beyond their inventory.
I did not run `agda` or `make check`, per the constraints.

## 5. ARCHIVE USED

`dev/DECISIONS-archived.md`. I read the file in full. I used it for S4: the
D to DD map above, D26's three parts at line 47, D30's freeze and amendments
at line 50, D33 at 53, D37 at 56, D38 at 57, D39 at 58, D36 at 59, and
D20(B)'s warrant discipline at line 42.

`dev/TASKS-archived.md`. I read the header, lines 1 to 13, and targeted rows.
I took from it what the retired route tried for the J tower and the bridge:
T166 at line 196 (the movable-order and coding subsets), T260 at 265 (the
wing does not consume the bridge rows), T203 at 274 (crossing is forced, a
syntax-free key exists on Sset and none on Lset), and T155 at 297 (the fat
audit of the shared part). T203 is an archived row that names an unfinished
target; per D-10, I treat its verdict as history, not as evidence the target
is true on the new route.

`archive/rud-route/README.md`. I read it in full. I took the four things it
names: BelowLim is the expensive one (lines 21 to 26), Story and Bridge
carry the generic machinery (lines 27 to 29), the route's refutations are
priced in the archives (lines 30 to 36), and a measured cure does not
transfer (lines 37 to 40). Line 42 splits this archive from `dev/ARCHIVE.md`,
which registers the modules retired during the route under `archive/src/`.
The pointer to `dev/JOURNAL.md` at line 35 is LJ-0.1 D28, already reported.

`dev/JOURNAL-archived.md`. I surveyed it by grep only. I confirmed its
length, 4,280 lines, and that R2' appears there as history. I took nothing
else from it, because S3 and S4 did not raise a question the other three
archives could not answer.

`dev/LESSONS.md`. Not archived and still binding. I read D-26 at line 1660,
P-l at 2094, P-m at 2249, P-n at 2272, P-q at 2422 and P-t at 2390. D-26 is
the fault line for S3: a rud-style stage carries generation data and a
definable stage does not, which is why the bridge exists and why the J tower
is priced per D-26. P-m and P-n underpin DD24's ratio. P-l underpins the
port-pricing rule the LJ rows cite.

`dev/memos/L3.32-route-adjustment-conflicts.md`. I read it in full, 93
lines. It is the survey that decided the consolidation. I took from it which
D rows conflict with the new ruling, the [T257] weak point at section 4, and
the open D30-wall question that DD24 and the section 0 rewrite later closed.

`dev/STATUS-archived.md`. I read the header, lines 1 to 30. It appeared
mid-audit in commit `48eef39` and holds the retired route's 96 goal rows. I
used it to confirm that section 11's compression is real and that the goal
rows are preserved.

## 6. PREFERENCES

Extend `scripts/check-task-index.py` with a phase-barrier check, so a
phase-2 row cannot be dispatched while phase 1 is open. The barrier is
review-only today.

Build the reuse report as an extension of `ledger.py`'s closure machinery,
not as a second implementation. C-26 forbids a second module timer; the same
reason applies to a second closure walker.

Repoint the dashboard's agent table at the PLAN task index instead of the
ledger's `[[owed]]` queue. The task index is the route's live dispatch
order.

Fix the two memo status headers when next touched: `dev/memos/route-tree.md`
and `dev/memos/source-material-survey.md` both name the revoked two-caliber
discipline as current.
