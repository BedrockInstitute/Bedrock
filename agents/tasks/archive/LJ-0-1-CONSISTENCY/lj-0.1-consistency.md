# LJ-0.1: consistency audit of `faf02fc..HEAD`

Task code `[LJ-0.1]`. Branch `two-tower-bridge`. Read-only. No file in the
repository was edited.

## 1. VERDICT

**NOT consistent, and the gate is currently RED.** `make check` fails today and
`make dashboard` crashes today. Thirty defects follow. Six are load-bearing:
two gates are broken, one new checker measures the wrong thing, one standing
brief clause orders every future brief to state the RETIRED route as ruled, one
ruling lost a clause that another live document still points at, and the live
status screen still describes the retired route.

## 2. DEFECTS

Ordered most severe first. `CONFIRMED` means I ran something. `READ` means I
read the code or the text.

### D1. `make check` is RED right now (class C) — CONFIRMED

`scripts/check-dev-docs.py` fails: `AGENTS.md` is 2,422 words against the
2,200-word cap at `scripts/check-dev-docs.py:105`. The `AGENTS.md` refresh
(commit `956f9bf`) added about 420 words and nobody re-ran the checker.
`Makefile:36` puts `devdocs` in `check`, so no commit can pass the gate.

- Evidence: `scripts/check-dev-docs.py:105`, `AGENTS.md:1-193`.
- Repair: cut about 230 words from `AGENTS.md`, or raise the cap by the
  recorded ruling procedure. Do not leave it red.

### D2. `make dashboard` crashes (class D) — CONFIRMED

`make dashboard` exits 2. `scripts/ledger.py:508-510` now prints a
`ledger [thresholds SUSPENDED]: ...` banner line before EVERY mode's output.
`scripts/dashboard.py:274` calls `MATRIX_RE.match(line)` on the whole captured
stdout, so the banner is now the first line and the match fails.

- Evidence: `scripts/dashboard.py:274-277`, `scripts/dashboard.py:241`,
  `scripts/ledger.py:508-510`. Traceback reproduced.
- Same fault waits in `parse_trophy_split` at `scripts/dashboard.py:171-173`.
- This breaks `dev/ORCHESTRATION.md:286-287`, which orders `make dashboard` at
  every return, and `AGENTS.md:106`, which names it the owner's board.
- Repair: make `ledger_trophy_matrix_line` and `ledger_trophy_split_line`
  select the data line, or print the banner to stderr.

### D3. `check-timing.py` claims a suspension it does not apply (class C, D) — CONFIRMED

`dev/ledger.toml:518-521` states: "every threshold checker DOWNGRADES to a
report while this is true: it still measures, still prints, and does not fail.
The affected checkers are `scripts/ledger.py`, `scripts/deletion-test.py` and
`scripts/check-timing.py`."

`scripts/check-timing.py:274-281` reads `thresholds_suspended` and PRINTS
"measuring and reporting, not enforcing". The value `_susp` is then never used
again. `scripts/check-timing.py:387` still returns 1 whenever findings exist.

- Evidence: `scripts/check-timing.py:274-281` against `scripts/check-timing.py:380-387`.
- This is the exact failure class the project names: a row that claims more
  than its checker delivers. Here the checker claims LESS than it does, which
  is equally wrong, because the orchestrator will read a red as a rule that is
  suspended.
- Repair: return 0 when `_susp` is true, or delete the banner.

### D4. `check-ratio.py` compares WARM seconds against a COLD baseline (class C) — CONFIRMED by reading

`dev/PLAN.md:182` (DD24) defines the bar as "the ratio of **cold** build seconds
to in-fence lines". `dev/ledger.toml:2297-2298` records the baseline
`0.007614` from a **cold** whole-tree run.

`scripts/check-ratio.py:105-106` makes `--cold` OPT-IN, and `Makefile:70-71`
runs `scripts/check-ratio.py --check` WITHOUT it. So the gate will time each
wing module WARM and divide by lines, then compare to a cold baseline.

`scripts/check-timing.py:220-228` documents this exact defect in its own
docstring: "the first version of this tool compared a warm 2.8 s against a cold
204 s baseline and reported OK, so a module could have tripled its real cost
and passed. Comparing a measurement against a baseline taken a different way is
worse than not comparing at all."

- Evidence: `Makefile:70-71`, `scripts/check-ratio.py:105-106`,
  `scripts/check-ratio.py:140`, `scripts/check-timing.py:217-234`,
  `dev/PLAN.md:182`, `dev/ledger.toml:2297`.
- Repair: default `check-ratio.py` to cold, or pass `--cold` in the Makefile.

### D5. `check-ratio.py` in `make check` breaks two stated rules (class C) — CONFIRMED by reading

Two separate problems, both from `Makefile:36` including `ratio`.

(a) `dev/ORCHESTRATION.md:80-84` states that `check-timing.py` is deliberately
NOT in `make check` because "a warm module check costs minutes; the commit gate
must stay cheap enough to actually be run". `check-ratio.py` calls the same
`time_module` (`scripts/check-ratio.py:50-64`, `:94`). Once `ratio.gch_wing` is
non-empty, `make check` will run one Agda typecheck per wing module inside the
commit gate. That contradicts the rule directly.

(b) `scripts/check-ratio.py:73-85` fails closed when any `agda` process is
live. Under C-12 up to four agents may run Agda at once. So `make check` will
go RED for a reason unrelated to the change being gated.

- Repair: take `ratio` out of `check` and run it at the return, like
  `check-timing.py`; or make the Agda guard skip rather than fail.

### D6. A standing brief clause orders the RETIRED route into every brief header (class A, B) — READ

`dev/ORCHESTRATION.md:157-159`:

> **DD2 and DD5, what is ruled and what is open.** State BOTH in the brief's
> header. Ruled: the campaign route, R2' with the trophy stated in L ...

DD2 (`dev/PLAN.md:169`) is the two-tower bridge. **R2' is the retired
internalization route** (`dev/DECISIONS-archived.md:47`, D26). Every brief
written to this clause will pin the wrong route.

- Repair: replace with DD2's actual content: two towers, J through rud, both
  trophies on the bridge, and the bridge two-directional.

### D7. The gate clause forbids exactly what phase 1 must do (class B) — READ

`dev/ORCHESTRATION.md:128-134`, headed **DD8, the gate, FIRST**, then says:

> Before you fund a block, **do not write a brief that dispatches new
> mathematics.** ... If a brief would advance a trophy rather than the
> check-cost data, it waits.

That is D30's retired check-cost freeze, not DD8. DD8 (`dev/PLAN.md:172`) is
the gate-before-funding rule and says nothing about new mathematics. The task
index (`dev/PLAN.md:445-450`) dispatches five new-mathematics builds in phase 1.
A brief written to this clause cannot be sent.

- Repair: cut the freeze text; keep DD8's real content, which is the widest
  unmeasured term plus its probe.

### D8. DD17 dropped the emergency tier, and ORCHESTRATION points at DD17 for it (class B) — READ

`dev/ORCHESTRATION.md:41-46`:

> **The emergency tier belongs to PLAN DD17's standing loop, and this section
> does not restate it.** ... Read DD17 before using it; **the ruling names what
> must be recorded.**

DD17 (`dev/PLAN.md:177`) is three sentences and says nothing about Fable 5, the
two binding conditions, or what must be recorded. Its ancestor D37
(`dev/DECISIONS-archived.md:56`) carried the whole tier. The consolidation
dropped it while ORCHESTRATION still delegates to it, so the rule now has no
canonical home. That breaks DD19's one-home rule (`dev/PLAN.md:179`).

- Repair: restore the tier's operative clauses into DD17, or make
  ORCHESTRATION section 2 canonical and say so.

### D9. A live document cites the REVOKED DD7 as authority (class A) — READ

`dev/ORCHESTRATION.md:230`:

> otherwise keep and wait (DD7: an estimate is a measurement, and an overage is
> recorded rather than argued from).

DD7 is revoked outright (`dev/PLAN.md:164`). Its surviving content is in DD8.

- Repair: cite DD8.

### D10. PLAN section 0, the live status screen, describes the retired route (class E, F) — READ

`dev/PLAN.md:9` says "**Read §0 first.** It states where the work stands
today." `AGENTS.md:106` names section 0 as the live status screen. Section 0 is
dated `2026-08-06` (`dev/PLAN.md:35`) and states, as current:

- `dev/PLAN.md:42-50`: the Def-tower architecture and the rud retirement.
- `dev/PLAN.md:61-73`: "The mathematics is FROZEN and the only funded work is
  the check-cost campaign `[L3.32-F]`", with `[T88]`, `[T89]`, `[T93]` "Live".
- `dev/PLAN.md:86`: quote the ledger for "endpoint in both calibers, and
  overage against the 25k reference figure" — both revoked by DD7 and DD5.
- `dev/PLAN.md:91-92`: "The CAMPAIGN ROUTE is settled: R2'".
- `dev/PLAN.md:96-97`: "Line calibers and the projection discipline are defined
  in §6.2" — §6.2 now REVOKES the two calibers (`dev/PLAN.md:256`). Section 0
  and section 6.2 contradict each other inside one file.

- Repair: rewrite section 0 for the two-tower bridge route, or mark it archived
  and point at a new one.

### D11. The only admissible size source still emits the revoked caliber (class B, E) — CONFIRMED

DD5 (`dev/PLAN.md:171`) names `scripts/ledger.py --brief` as the caliber's
"only admissible source", and `AGENTS.md:62-63` repeats it. Its output today:

```
standing 17,492 | endpoint 30.68-35.42k naive, 37.88-49.99k calibrated
| naive corner +10.42k against the 25k reference; D39 benchmark 25.49-28.26k
naive, NOT YET CLEAR ENOUGH TO BIND
```

Three defects in one line. It prints both calibers, which DD8 revoked. It
prints the 25k reference, which `dev/ledger.toml:125-126` says is superseded.
It cites `D39`, an archived code, where the live home is DD5.

Worse: `dev/ledger.toml:111-117` says of the endpoint figure "**Do not quote
it.**" So DD5 names as its only admissible source a tool whose headline number
the ledger forbids anyone to quote.

- Evidence: `scripts/ledger.py:600-615` region for the printer,
  `dev/ledger.toml:111-117`, `dev/PLAN.md:171`, `AGENTS.md:62`.
- Repair: drop the calibrated figure and the 25k clause, cite DD5 not D39, and
  suppress or flag the endpoint while `[[remaining]]` is stale.

### D12. The ledger writes down a standing figure, and it is wrong (class E) — CONFIRMED

`dev/ledger.toml:116` states "Standing (17,630) is MEASURED and trustworthy."
`dev/ledger.toml:95` and `scripts/ledger.py:105` repeat 17,630. The measured
standing is **17,492** (`ledger.py --check`, `ledger.py --brief`,
`deletion-test.py`, all run today).

This is also the exact failure the ledger header forbids: a standing number
written into prose. `AGENTS.md:62-63` and DD15 (`dev/PLAN.md:176`) both say a
standing figure is never quoted from a paragraph.

- Repair: remove the number from the three comments, or restate it as the
  measurement of the day it was taken with its date.

### D13. The ledger says the AC seconds benchmark does not exist; DD5 and the ledger's own `[ratio]` say it was measured (class B, E) — READ

`dev/ledger.toml:145-168` (`[basis.internalization_benchmark]`):

- `seconds_state = "DOES NOT EXIST"` (`dev/ledger.toml:158`)
- "The AC half is MEASURABLE ... a cold wall on it is one run"
  (`dev/ledger.toml:162-163`)

But `dev/ledger.toml:2297-2298` records the AC wall MEASURED on 2026-08-09 at
133.19 s over 17,492 lines, and DD5 (`dev/PLAN.md:171`) says "The time
benchmark is **half-built**". Three statements, two of them stale.

Also stale in the same block: `dev/ledger.toml:168` says "the tree today:
15,188 metered lines", against a measured 17,492; and `lines_calibrated`
(`dev/ledger.toml:149`) keeps the caliber DD7's revocation removed.

- Repair: set `seconds_state` to half-built, write the 133.19 s figure in, and
  fix the 15,188.

### D14. DD5 calls the trophy split a surviving DIAGNOSTIC; it is suspended and now reports nonsense (class B, D) — CONFIRMED

DD5 (`dev/PLAN.md:171`): "The per-trophy split and the AC cap survive as
DIAGNOSTICS."

`ledger.py --trophy-split` today:

```
trophy split base 1,972 | ac-only 15,520 | shared 0 | gch-only 0
| ac-total 17,492 | standing 17,492
```

`gch-only 0` and `shared 0` mean the split no longer partitions anything: it
says the whole tree is AC. `dev/ledger.toml:102-109` suspends it precisely
because its roots are gone. A diagnostic that reports one bucket is not a
diagnostic.

- Repair: either drop the "survives as a diagnostic" clause from DD5, or make
  `--trophy-split` refuse to print while `trophy_split_suspended` is true.

### D15. `deletion-test.py` reads one suspension flag and ignores the other (class D) — CONFIRMED

`scripts/deletion-test.py:79-82` reads `thresholds_suspended`. Nothing in the
file reads `trophy_split_suspended`. But `scripts/deletion-test.py:53` builds
its whole state from `ledger.trophy_split(...)`, the suspended declaration.

Consequence: the shadow run prints `ac-total 17,492` from a split the ledger
declares meaningless, and exits 0 with a green-looking line. `--run` would
compute `gch_files` as the empty set (`gch-only 0`), delete nothing, typecheck
the whole tree, and report that as a deletion test.

- Repair: refuse both `--files` and `--run` while `trophy_split_suspended` is
  true, and say why.

### D16. `dashboard.py` reads no suspension flag at all (class D, E) — CONFIRMED by reading

`scripts/dashboard.py` has zero references to `retire_suspended`,
`trophy_split_suspended` or `thresholds_suspended` (grep over `scripts/`). It
still renders, from retired declarations:

- `scripts/dashboard.py:1048`: `<h3>The AC budget, ruling D36</h3>`, a cap DD5
  demoted to a diagnostic.
- `scripts/dashboard.py:386-395`: the "is D30's freeze lifted?" decision graph,
  a freeze belonging to the retired route.
- `scripts/dashboard.py:1010-1038`: the trophy matrix panel, from the suspended
  split.
- `scripts/dashboard.py:299`: the endpoint parser expects
  `naive ... calibrated ... 25k reference`, all revoked.

The orchestrator did not touch this file. It is the owner's board.

- Repair: gate every panel on its declaration's suspension flag, and remove the
  D30 freeze graph.

### D17. Ten stale task-code references inside the new LJ rows (class G) — CONFIRMED by reading

The renumbering to `LJ-<phase>.<step>` was mechanical and the prose kept the
old `T<n>` codes. `scripts/check-task-index.py` cannot catch these, because
`scripts/check-task-index.py:58-59` only extracts BRACKETED codes and these are
bare.

| Line | Text | Should read |
|---|---|---|
| `dev/PLAN.md:444` | "the widest unmeasured term T1 names" | LJ-1.1 |
| `dev/PLAN.md:448` | "Independent of T3 to T5" | LJ-1.3 to LJ-1.5 |
| `dev/PLAN.md:449` | "Condensation plus T6. Needs T5 and T6" | LJ-1.5 and LJ-1.6 |
| `dev/PLAN.md:450` | "Needs T7" | LJ-1.7 |
| `dev/PLAN.md:455` | "Adversarial review of T12's reuse map ... sends T12 back" | LJ-3.1 |
| `dev/PLAN.md:459` | "Needs T15 and T16" | LJ-3.4 and LJ-3.5 |
| `dev/PLAN.md:460` | "reusing what T12 mapped" | LJ-3.1 |
| `dev/PLAN.md:462` | "Only after T19 passes" | LJ-3.8 |

The dependency LOGIC is sound once translated: no phase-2 row depends on a
phase-3 row, and no row depends forward inside its phase. Only the labels are
wrong.

### D18. Stale `LJ1-T` codes in the ledger and three scripts (class G) — CONFIRMED

The `LJ1-T<n>` series was replaced by `LJ-<phase>.<step>` in commit `30b1c4f`.
These still name it:

- `dev/ledger.toml:104` "LJ1-T8 builds it" (now LJ-1.8)
- `dev/ledger.toml:107` "LJ1-T12's reuse map" (now LJ-3.1)
- `dev/ledger.toml:108` "LJ1-T11 rebuilds the split" (now LJ-2.2)
- `dev/ledger.toml:2304` "LJ1-T1 should plan for it" (now LJ-1.1)
- `dev/ledger.toml:2325` "Empty until LJ1-T3 lands its first module" (now LJ-1.3)
- `scripts/check-ratio.py:119` "until LJ1-T3 lands its first module" (now LJ-1.3)
- `scripts/check-task-index.py:49,55,96` `GOAL = "LJ"` comment says "the live
  goal is `LJ1`" and the example says "LJ1-T1"
- `scripts/ledger.py:253` "the GCH wing does not exist yet: LJ1-T8"
- `dev/TASKS-archived.md:6` "The live index ... uses a NEW series, `LJ1-T`"
- `dev/JOURNAL.md:3` "the two-tower bridge route, `[LJ1]`" and
  `dev/JOURNAL.md:26` "no `LJ1` task has returned"

### D19. Four live documents cite consolidated DD codes (class A) — CONFIRMED

A consolidated code resolves by design, but a LIVE document should point at the
survivor.

- `dev/PLAN.md:451` LJ-1.9: "DD24 is the bar, DD25 the only one". DD25 merged
  into DD24 (`dev/PLAN.md:164`). The sentence now reads as two rulings where
  there is one.
- `dev/PLAN.md:458` LJ-3.5: "DD3 keeps BOTH directions". DD3 merged into DD2.
- `Makefile:66`: "DD25 makes the seconds-per-line ratio the ONLY threshold".
  Should be DD24.
- `archive/rud-route/README.md:30`: "DD3 keeps the two-directional bridge".
  Should be DD2.

`scripts/check-rule-ids.py` cannot catch any of these: it accepts consolidated
codes by design (`scripts/check-rule-ids.py:69-75`), and it scans only
`dev/**/*.md` plus `AGENTS.md` (`scripts/check-rule-ids.py:165`), so neither
`Makefile`, `scripts/*.py` nor `archive/` is scanned at all.

### D20. Seven stale `D`-series citations in the live ORCHESTRATION document (class A) — CONFIRMED

Each resolves against the archive, so no checker fires. Each points at a
retired ruling where a live DD row now owns the rule.

| Line | Cites | Live home |
|---|---|---|
| `dev/ORCHESTRATION.md:35` | `PLAN D23` for the idle slot | DD17 |
| `dev/ORCHESTRATION.md:74` | `D22` for the gate | DD8 |
| `dev/ORCHESTRATION.md:135` | `D29` for generic writing | DD4 |
| `dev/ORCHESTRATION.md:151` | `D17` at a retirement question | DD13 |
| `dev/ORCHESTRATION.md:196` | `D29` for the route shape question | DD4 |
| `dev/ORCHESTRATION.md:259` | `D28` for the background gate | DD15 |
| `dev/ORCHESTRATION.md:278` | `D27` for ledger currency | DD15 |
| `dev/ORCHESTRATION.md:319` | `D35` for the glossary pipeline | DD19 |

`dev/ORCHESTRATION.md:35` is the sharpest: it cites `D23` for the idle-slot
rule while `dev/ORCHESTRATION.md:41` cites `DD17` for the same loop, eleven
lines apart.

A second trap: `D22` at `dev/ORCHESTRATION.md:74` and `:226` reads next to
`DD22`, which is LICENSING (`dev/PLAN.md:180`). One letter separates a gate
rule from a licence rule.

### D21. `dev/ORCHESTRATION.md:232` names DD8 twice (class A) — CONFIRMED

> *Enforcement:* the standing brief clauses in section 3 (DD8, DD8, DD13)

Section 3 carries three distinct clause families: the gate (DD8), generic
writing (DD4, written as D29 at line 135) and the port price (DD13). The second
`DD8` is almost certainly meant to be DD4.

### D22. Three PLAN sections point at "§3" for rows that left it (class F) — CONFIRMED

Section 3 is now the DD table. These still send a reader there for D rows:

- `dev/PLAN.md:190` (§5): "the ruling is D2 in §3"
- `dev/PLAN.md:296` (§8): "D11's mechanisms are stated in the D11 row of §3"
- `dev/PLAN.md:300` (§9): "D1 and D26 in §3"

`dev/PLAN.md:296` is the worst: DD11 exists in §3 and is "Code and prose
craft", a different subject from D11's "Revisability". A reader who follows the
pointer lands on a real row that says the wrong thing.

Also `scripts/check-timing.py:384` prints "D30 (dev/PLAN.md section 3) freezes
new mathematics" at every defect. D30 is not in section 3 and the freeze is
retired.

### D23. PLAN's section 6 heading cites the wrong DD row (class A) — CONFIRMED

`dev/PLAN.md:192`: `## 6. Route tree (DD18)`.

Section 6 holds the goal-coding rules and the task-index rules. DD18 is now
**the archive-survey mechanism** (`dev/PLAN.md:178`). The old DD18 content moved
to DD19 (`dev/PLAN.md:164`, `:179`), so the heading should cite DD19.

### D24. Two live clauses claim a mechanism that does not exist (class C) — CONFIRMED

`scripts/dispatch.py` is not in the repository (`ls` confirms).

- `dev/ORCHESTRATION.md:265`: "`dispatch.py gate-ready` checks it." It does not.
  The rule it guards, "do not arm a full gate while any agent is live", is
  therefore review-only, and the document says otherwise.
- `dev/ORCHESTRATION.md:94`: "the dispatch path REFUSES a brief that does not
  carry it, with the kind DERIVED from the brief's write scope". No such path
  exists. `scripts/rules.py` emits a bundle; it refuses nothing.

Both are the failure the project names by its own rule: a claim of enforcement
that no checker delivers.

- Repair: restate both as review steps, or name the real enforcement point.

### D25. `AGENTS.md` keeps the two-caliber factors three lines before revoking them (class B) — CONFIRMED

`AGENTS.md:150-153`:

> **Gate every block before you fund it.** This is arithmetic, not caution: a
> green gate moves the term **from the 3x class to about 1.3x** and lowers the
> top of **the band** ...

`AGENTS.md:155-160`:

> **The two-caliber rule is REVOKED** (owner, 2026-08-09) ...

The 3x and 1.3x factors and "the band" ARE the two-caliber discipline
(`dev/PLAN.md:256-258`). The same page states and revokes it.

The same language survives at `dev/ORCHESTRATION.md:226` ("priced at x3 with an
unmeasured widest term") and `dev/ORCHESTRATION.md:280` ("move a gated row's
class from x3 toward x1.3"). DD8 itself keeps "narrows the band and lowers its
top" (`dev/PLAN.md:172`), which is softer but the same frame.

### D26. Section 6.0's coding rules contradict the live task-code form (class B) — CONFIRMED

- `dev/PLAN.md:226-231` rule 7 defines a dispatched task as
  `L<goal>.<subgoal>-T<n>`. No live code has that shape. Every live code is
  `LJ-<phase>.<step>` (`dev/PLAN.md:442-462`).
- `dev/PLAN.md:203-209` rule 3 says a code is "never renamed, deleted, reused,
  or renumbered", and that the one carve-out "is spent". Commit `30b1c4f`
  renumbered twenty LJ codes on 2026-08-09. The renumbering may be correct, but
  rule 3 was not amended and no second carve-out is recorded.

- Repair: amend rule 7 for the `LJ-<phase>.<step>` form, and record the
  2026-08-09 renumbering as a second, dated carve-out with its owner ruling.

### D27. The new checker is undocumented in its canonical home (class F) — CONFIRMED

`AGENTS.md:103` makes `scripts/README.md` canonical for "What every script does
and when to run it". `scripts/README.md` has no `## check-ratio.py` section
(heading list confirmed). `check-timing.py`, `check-task-index.py` and
`check-rule-ids.py` are also absent, but only `check-ratio.py` is new in this
rework.

### D28. `archive/rud-route/README.md` points at the emptied journal (class F) — CONFIRMED

`archive/rud-route/README.md:36-37`: "all of it is priced in
`dev/TASKS-archived.md` and `dev/JOURNAL.md`". `dev/JOURNAL.md` is now empty
(`dev/JOURNAL.md:26`). The retired route's record is `dev/JOURNAL-archived.md`,
which the same README names correctly at line 43.

### D29. Two counts in the new documents are off by a small amount (class E) — CONFIRMED

- `dev/JOURNAL.md:6` says the archive is "4,260 lines". `wc -l` gives **4,280**.
- `dev/TASKS-archived.md:10` says "The 264 rows below", and DD18
  (`dev/PLAN.md:178`), `dev/ORCHESTRATION.md:116` and `AGENTS.md:174` all repeat
  264. There are **265** rows: 264 with the `L3.32-T<n>` shape plus
  `L3.32-T251r` at `dev/TASKS-archived.md:256`.
- `L3.32-T251r` is also invisible to `scripts/check-task-index.py`: neither
  `FULL` (`:58`) nor `ROW` (`:60`) accepts a letter suffix. A citation of
  `[L3.32-T251r]` would resolve against nothing and the checker would not say
  so. This one predates the rework.

### D30. `check-timing.py` still enforces retired-route rules (class E) — CONFIRMED by reading

- `scripts/check-timing.py:92` `REWRITE_SCOPES = ("L.Ordinal.SquareLaw", "L.Rud.")`.
  No `L.Rud.*` module is in `src/` any more; they are all in
  `archive/rud-route/`. The rewrite gate now scopes to one surviving module.
- `scripts/check-timing.py:367-375` still requires a per-definition profile
  under "D30 exit condition (1)", a retired ruling.
- `scripts/check-timing.py:354-363` still gates on
  `caliber.retiring_seconds_per_signature`, the retired subtree's rate.

These are not wrong answers with a green light today, because the tree changed
under them; they are dead rules that will fire on the new wing.

## 3. WHAT I CHECKED AND FOUND CLEAN

**Checkers I ran.** `check-rule-ids.py` clean, 46 files, 120 lessons, 64
decisions. `check-task-index.py` clean, 265 cited codes, 285 unique rows, all
within 200 characters. `check-ratio.py` returns 0 correctly while
`ratio.gch_wing` is empty. `ledger.py --check` declaration-clean, standing
17,492 over 75 masters. `check-tree.py --check` clean, 75 masters, seven
sub-checks. `check-probes.py` clean, 358 tracked files. `check-agents-guard.py`
clean, five guarded commits. `check-glossary.py` clean. `lint-prose.py --check`
clean. `rules.py --check` clean, five bundles. `link-check.py` clean.
`deletion-test.py` shadow ran and exited 0.

**DD citations that resolve AND say what the citing text claims.** I checked
each by opening the row: `AGENTS.md:40` (DD19, the AGENTS guard),
`AGENTS.md:56` (DD15, background typecheck), `AGENTS.md:99` (DD19, the glossary
pipeline), `AGENTS.md:119` (DD4, three moments), `AGENTS.md:155` (DD8, one
best-effort number), `AGENTS.md:162` (DD2 and DD5), `AGENTS.md:168-170` (DD24
and DD23), `dev/ORCHESTRATION.md:125` (DD13, a port is priced fresh),
`dev/ORCHESTRATION.md:218` for DD23's existence, `dev/JOURNAL.md:14` (DD23),
`dev/ledger.toml:97` (DD13), `scripts/deletion-test.py:75,161,223` (DD5),
`scripts/check-ratio.py:2,131,179` (DD24).

**LESSONS citations from the DD rows.** All resolve and all are APT. I read
each entry rather than trusting the ID:

- `P-l` (`dev/LESSONS.md:2094`) is cited five times for "a measured cure does
  not transfer by analogy" and "an anchored figure is a hypothesis, not a
  price". Its heading is about concrete stages, so the citation LOOKS wrong.
  It is not: `dev/LESSONS.md:2116` states "A CURE DOES NOT TRANSFER BY ANALOGY.
  Re-measure it at every new site", with a five-row transplant table, and
  `dev/LESSONS.md:2141` states "An expected figure anchored on a comparable is a
  HYPOTHESIS, not a price". DD18, `AGENTS.md:140`, `dev/ORCHESTRATION.md:126`,
  `scripts/check-ratio.py:28,132` and `archive/rud-route/README.md:41` are all
  correct.
- `P-m` (`dev/LESSONS.md:2249`) supports DD24's rate bands: "near 0.01 s per
  line" parameterized against "near 0.22" instantiation.
- `P-q` (`dev/LESSONS.md:2422`) supports DD24's "315 lines removed buying 11.8
  seconds": the table at `dev/LESSONS.md:2439` reads `-315` and `-11.80`.
- `P-t` (`dev/LESSONS.md:2390`) supports DD24's "twentyeightfold spread inside
  ONE file": `dev/LESSONS.md:2407` reads "**28 times, for the same content.**"
- `P-n` (`dev/LESSONS.md:2272`) exists and says what DD24 implies.
- `C-12` is cited correctly by `AGENTS.md:129-131` and
  `scripts/check-ratio.py:78`.

**The DD table's own shape.** Fifteen rows: DD1, 2, 4, 5, 8, 9, 11, 13, 15, 17,
18, 19, 22, 23, 24. The consolidation paragraph (`dev/PLAN.md:164`) accounts for
every missing number, and `scripts/check-rule-ids.py:74-75` parses that
paragraph so the merged codes still resolve. I verified the regex captures all
of DD3, DD6, DD7, DD10, DD12, DD14, DD16, DD20, DD21 and DD25.

**Dropped clauses I looked for and judged acceptable.** Comparing each DD row
against its D ancestors in `dev/DECISIONS-archived.md`:

- DD9 keeps D2's substance but drops "over 1.5x the M2.7 full-cone baseline".
  The threshold was route-specific; the escalation duty survives.
- DD13 keeps D17 and D20 but drops D20's warrant discipline (a kept chapter
  needs a named open goal and a dated expiry) and D17's "D-19 prices PORTS and
  must not be quoted at a rewrite question". The second still lives at
  `dev/ORCHESTRATION.md:154`, so it is not homeless.
- DD22 keeps D4's licensing in full.
- DD19 keeps D24, D34 and D35's operative content.
- Only DD17's loss (defect D8 above) leaves a rule with no home.

**Archive integrity.** `archive/rud-route/` holds 72 `.lagda.md` files, which
matches the claim at `dev/PLAN.md:178`, `dev/ORCHESTRATION.md:115` and
`AGENTS.md:173`. `rud-route-src.patch` is present. `check-tree.py`'s archive
sub-check passes, so nothing imports across the boundary.

**The suspension flags, per reader.** `retire_suspended` is read at both of its
consumers, `scripts/ledger.py:107` and `scripts/check-tree.py:232`, and both
apply it. `thresholds_suspended` is read at `scripts/ledger.py:509` and
`scripts/deletion-test.py:80` and applied at both. Only `check-timing.py`
(defect D3) reads it without applying it, and only `dashboard.py` (defect D16)
never reads it.

**Task-index dependency logic.** Once the stale `T<n>` labels of defect D17 are
translated, no row depends on a later phase and no row depends forward inside
its phase. The phase barrier stated at `dev/PLAN.md:417-420` holds.

**Not reviewed, by instruction.** `src/` content and the Agda files under
`archive/rud-route/`. I did not run `agda` or `make typecheck`.

**Named in the brief but absent.** `scripts/check-maintenance.py` does not
exist in this repository. I checked `scripts/` and found no file of that name
and no reference to one.

## 4. ARCHIVE USED

Required by DD18 (`dev/PLAN.md:178`).

- **`dev/DECISIONS-archived.md`** — read in full, 61 lines, all 30 D rows. Used
  for check B. It is what let me find defect D8: D37
  (`dev/DECISIONS-archived.md:56`) carries the emergency breakthrough tier in
  full, and DD17 (`dev/PLAN.md:177`) carries none of it, so I could see the
  clause was dropped rather than moved. It also gave me the true content of
  D22, D23, D26, D27, D28, D29, D30 and D35, which is how I judged each stale
  citation in defect D20 as pointing at a real but retired rule rather than at
  nothing. D26 (`dev/DECISIONS-archived.md:47`) is where I confirmed that R2'
  is the retired route, which is defect D6.

- **`dev/TASKS-archived.md`** — read the header (lines 1-13) and searched the
  table. Used to verify two counts: 264 codes of the `L3.32-T<n>` shape plus
  `L3.32-T251r` at line 256, giving defect D29. Its line 6 supplied one of the
  stale `LJ1-T` references in defect D18.

- **`dev/JOURNAL-archived.md`** — surveyed by `grep` only, not read through. I
  used it to confirm the file's real length, 4,280 lines, against the 4,260
  claimed at `dev/JOURNAL.md:6` (defect D29), and to confirm that R2' appears
  only as retired-route history there.

- **`archive/rud-route/README.md`** — read in full. It gave defect D19's fourth
  item (the DD3 citation at line 30) and defect D28 (the pointer to
  `dev/JOURNAL.md` at lines 36-37). Its line 41's P-l citation is correct, which
  I record under section 3.

- **`dev/LESSONS.md`** — NOT archived and still binding. I opened P-l
  (line 2094), P-k (2190), P-m (2249), P-n (2272), P-t (2390) and P-q (2422),
  and read each far enough to judge the citing text. The P-l finding was the
  reason: its heading does not match what five documents cite it for, and only
  reading the body (lines 2116 to 2143) showed the citations are sound. That is
  a near-miss defect I would have reported wrongly on the heading alone.
