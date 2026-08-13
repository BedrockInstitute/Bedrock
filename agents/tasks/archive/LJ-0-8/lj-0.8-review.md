# [LJ-0.8] Adversarial review of the AC-side compression

Status: COMPLETE. Reviewer: fable 5, owner-named tier, 2026-08-10.
Read-only on `src/`. No agda run. No commit.

A timeline note first. Block B returned REFUSED while this review ran
(commit `a83ea88`, 13:09). The orchestrator's audit already states the
target is not reachable by the planned blocks. This review confirms that
independently, bounds the remainder with two new measurements, and
corrects the record where it is wrong. Section 7 holds the pasteable
corrections.

MEASURED versus ESTIMATED is marked at every figure. A figure from a
typechecked build or a mechanical scan is MEASURED. A figure from a site
count, a surface read, or a comparable elsewhere is ESTIMATED.

## 1. VERDICT

**The target is not reachable and the plan to reach it is spent.**
Five of eight blocks are now tested. One landed. Four returned net zero
or worse. The evidence:

| Block | Band (estimated) | Result (measured) | Source |
|---|---|---|---|
| A dead names | -226 to -296 | **-240, landed** | `_build/lj-0.4a-report.md:5-16` |
| B existential frame | -190 to -340 | **+24 built; about -6 full-wired; refused** | `_build/lj-0.4b-report.md:9-32` |
| C clause frames | -180 to -315 | **-59 by gutting; stopped, reverted** | commit `4f40567` |
| E traversal share | -60 to -120 | **+19; refused** | `_build/lj-0.4e-report.md:21` |
| G lex kit | -40 to -80 | **+49; refused. The record says -49 and the sign is wrong** | `_build/lj-0.4e-report.md:85-93`; section 7.0 below |

Every kit block failed on one arithmetic: the kit costs more lines than
its sites save (kit 31, 43, 111 against savings 12, 49, 62). The July
survey priced the savings and never priced the kit. The orchestrator's
audit `a83ea88` names this diagnosis and it is correct.

**The honest reachable figure is about 17,000 lines** (basis in section
2). The gap to 16,400 is about 600 lines, and two mechanical scans this
session (section 6) show those lines do not exist in any class a
dispatch can extract. Reaching 16,400 needs a content-level ruling, and
the campaign rules content out. Say that to the owner plainly.

**What to do instead of blocks D, F, H as planned** (details in 3, text
in 7):

1. Skip block D. The finding saves a dispatch.
2. Run block F's named bisect probe first. Build F only on a GO.
3. Do not dispatch H alone. Fold it into F's build, or drop it.
4. Dispatch one new measured-class block: the within-file dedup sweep
   (section 6.3), net about -80 to -140.
5. Execute the orchestrator-side deletions block A left behind, about
   -60 (section 7.6).

## 2. THE TARGET, judged

**Question: does 16,400 rest on anything better than the refuted
16,000?** Answer: partly, and the part that held is spent.

Provenance of the two numbers:

- 16,000 was the July survey's optimistic end, never probed. `[T205]`
  refuted it (`archive/dev/TASKS-archived.md:276`).
- 16,400 is `[LJ-0.4]`'s center (`_build/lj-0.4-compression.md:11-27`).
  It rests on two inputs. Input one: T208's lever measurements. Input
  two: the N1 to N8 site counts, calibrated by T208's ratio law.

Input one was only half a measurement. T208 MEASURED the deletion class
(3.1: 54 names, 210 lines, verified by reading occurrence lines). For
the frame classes, T208 counted STATEMENT SURFACES and called the counts
measurements (3.2 to 3.4: "boilerplate about 126 lines", "one frame
instance costs about 15 to 20"). No kit was built. No instance was
wired. Five builds have now tested that class and the surface counts
missed the kit's own cost every time. So 16,400 was better-founded than
16,000 on the deletion class only, and block A has already banked that
class.

The recon knew this risk and recorded it: "A probe must measure N1 to N4
before dispatch" (`_build/lj-0.4-compression.md:182-183`). The dispatch
order did not honor that sentence. Blocks C and B went out as builds.
The build-measure-revert protocol did serve as the probe, at the price
of full dispatches, and in C's case it invited the gutting (section 4).

**The figure the evidence supports: about 17,000.** Basis (DD8, one
number, named basis): 17,273 standing, minus the three measured-class
remainders, minus half-weight on F.

| Remainder | Net | Class |
|---|---|---|
| Within-file dedup sweep | -80 to -140 | MEASURED surface (my scan, section 6.3), estimated glue |
| Prose-freed dead names | -55 to -65 | MEASURED dead in code (`_build/lj-0.4a-report.md:99-145,268-271`) |
| H residue (helpers) | -15 to -40 | ESTIMATED, site count |
| F, if its probe returns GO | 0, or -60 to -150 | ESTIMATED from comparables; P-l says hypothesis |

Without F: 17,028 to 17,123. With F landing mid-band: about 16,930.
No evidenced path reaches 16,400. The shortfall is not a pricing error
to work down; section 6 shows the mass is absent.

**If the owner keeps a line prerequisite, the honest figure is about
17,000, or about 16,900 with F green.** Below that, the moves are
content rulings the campaign excluded: S18's double-encoding collapse
(deferred by the owner, about -50 to -70,
`dev/memos/simplification-register.md:38`), a chapter retirement, or
proof rewrites with no measured comparable. Lead with the invariant:
compression of this tree by mechanical extraction is measured near
exhaustion at flat seconds.

## 3. EACH REMAINING BLOCK: credibility and attempt-or-skip

**Block B (returned during this review).** The refusal is correct and
the return is model-grade. It anchored the rate with one wired site (19
saved against 43 kit, flat seconds), priced the rest, reverted, and
preserved the kit. Two residues need action: the kit sits in volatile
`/tmp` (`_build/lj-0.4b-report.md:5`), and no revival trigger is
registered anywhere. Section 7.7 gives both.

**Block D, the Model arity-generic clause frame. SKIP. Credibility of
the -60 to -130 band: refuted by class.** Four grounds.

1. Same arithmetic as B, C, E, G: N4 is a site count with the kit
   unpriced (`_build/lj-0.4-compression.md:70`).
2. MEASURED this session: `Model`, the largest master at 1,289 lines,
   contains zero repeated 4-line blocks. The dedup scan found none.
3. The in/out pairs are two-way decode content. Read
   `src/L/Coding/Model.lagda.md:588-637`: `tagAtL-adequate` and
   `tagPairAtL-adequate` share a shape and share no extractable lines.
   The fwd/bwd bodies are per-clause equational glue. B measured the
   same fact at its sites: "the decode is content, and it stays at the
   site" (`_build/lj-0.4b-report.md:74-75`).
4. An arity-generic kit needs dependent parameters, which is G's
   transport-machinery trap, measured at +49
   (`_build/lj-0.4e-report.md:126-136`).

The skip is a finding. It saves a dispatch and about a day.

**Block F, the recursion-assembly triplication. PROBE FIRST. Credibility
of -100 to -200: medium-low.** The band is bracketed by two delivered
comparables, not measured at these sites (`_build/l3.32-t208-report.md`
3.6), and P-l refuses the transfer. The wall class is measured: rule 13
recorded over 400 s once for abstracting the recursion's value. T208
queued the named bisect probe and nobody ran it
(`_build/l3.32-t208-report.md:316-320`). F is also the only remaining
block whose dedup surface is real: the three assembly regions measure
about 127, 153, 188 lines, and unification is not a call-site kit. Do
not fund the build before the probe. Section 7.3 has the probe brief.

**Block H, preamble and shift helpers. DO NOT DISPATCH ALONE.
Credibility of -30 to -60: low.** MEASURED this session: the tree-wide
preamble repeat surface is 229 raw lines, and an import line cannot be
deleted by sharing, because every module still needs its opens. The
deletable part is the helper family (about 26 lines) plus small glue.
Realistic net: -15 to -40, at the cost of touching about 12 masters and
serializing against every other writer (C-25). Fold H into F's build
dispatch on a GO, or drop it. A dedicated dispatch cannot pay for
itself.

**The one block worth adding: the within-file dedup sweep.** MEASURED
basis, section 6.3. Net about -80 to -140, no new module for the
within-file part, no kit arithmetic to lose. Section 7.5 has the brief
core.

## 4. BLOCK C: BRIEF OR AGENT?

**The brief's share is dominant. The brief made the failure likely; the
agent made it invisible.**

What the brief asked, with its own numbers. The GOAL orders the agent to
"extract the repeated clause frames out of `Unique` and `Sound` into one
new shared module, and land 180 to 315" (`_build/briefs/LJ-0.4c.md:5-9`).
The measured inputs at that site were lever (b) at -55 to -75 and lever
(d) at -90 to -125, together **-145 to -200 at the surface, before any
kit cost** (`_build/l3.32-t208-report.md` 3.2, 3.4). Everything above
that was N2 and N3, site-count estimates. So the band floor sat at the
extreme edge of the measured surface, and the band top was double it. An
agent obeying "land 180 to 315" had one route: move mass. My scan
confirms the ceiling today: `Unique` holds about 54 raw lines of
repeated blocks and `Sound` about 38.

Five specific defects in the brief, ranked:

1. **The stop trigger named seconds only.** "If the extraction costs
   seconds, or forces a consumer to unfold, report the measurement and
   STOP" (`LJ-0.4c.md:172-174`). No line-band trigger. E and G stopped
   on the line meter by their own judgment, not by instruction. C's
   agent had no instruction to stop at a bad net.
2. **No chapter rule.** The words "chapter must remain", "stub", and
   "do not delete" do not appear in the brief. I verified by grep: the
   word "chapter" occurs twice, both descriptive (`LJ-0.4c.md:26,50`).
   The audit commit `4f40567` says C "broke a constraint the brief
   stated: do not delete a chapter". That constraint is in block A's
   brief (`_build/briefs/LJ-0.4a.md:89`), not in C's. The orchestrator
   audited C against a constraint it never wrote. That misattribution
   is the clearest evidence the rule was assumed, not stated.
3. **The DD4 paragraph pushed toward mass movement.** "Price your work
   by what it makes cheaper later, not only by the lines it removes
   today. Write the shared module generic at full strength. A stop-line
   is never a reason to write fixed" (`LJ-0.4c.md:87-97`). Read against
   a band the surface cannot pay, this licenses exactly what happened:
   1,354 lines moved into a generic `Pinned`.
4. **No staging.** Nothing ordered: convert one clause pair, measure,
   project, then decide. C-22 was cited (`LJ-0.4c.md:122,180`), but the
   RETURN's first fillable number exists only after the whole
   extraction, so the skeleton stayed empty by construction.
5. **"Extract the SHELL, not the fold" bounded the shape, not the
   mass** (`LJ-0.4c.md:73`). It forbids the P-r datatype. It does not
   forbid relocating every clause body as "shell instances".

The agent's share, real but secondary:

1. It filled nothing for 38 minutes. The brief ordered incremental
   writing twice. An agent that measures nothing mid-flight cannot be
   caught mid-flight. This is why the stop cost 38 minutes instead of
   ten.
2. It built the P-r shape the brief warned against: the audit records
   deep `.snd` chains, the nested-Sigma access pattern (`4f40567`).
3. "A stop is a deliverable" was in its brief (`LJ-0.4c.md:174`), and
   the E/G agent stopped under weaker wording the same morning.

**The text that would have prevented it** is now partly in B's brief
(`_build/briefs/LJ-0.4b.md:43-59,177`): the chapter rule, the net across
every file, the stub ban. Still missing from that brief, and owed to
every successor: the staging gate, the line-band stop trigger, the
break-even gate, and the twice-today rule. Section 7.1 gives the four as
pasteable text.

## 5. THE SECONDS BAR, judged

**The reasoning holds. The bar is correctly on seconds.** The ledger's
arithmetic is right: at flat seconds, fewer lines force the ratio up;
132.87 s over 16,400 lines is 0.008102, 5.3 percent over 0.007693, and
inside DD24's 1.15 tolerance (`dev/ledger.toml:2462-2475`). A ratio bar
would forbid all flat-seconds compression by arithmetic, so seconds is
the only coherent per-block bar. P-q confirms the direction: dedup buys
lines, not seconds (`dev/LESSONS.md:2427`).

Three refinements, none fatal:

1. **The ceiling sits inside instrument noise.** The wall measured
   133.19, then 133.69 after a -240 change the ledger calls noise, then
   132.87 after the shim (`dev/ledger.toml:2477-2499`). Spread: 0.82 s.
   The ceiling 133.4 is 0.53 s above the current wall, within that
   spread. One cold run cannot convict or acquit a block against it.
   The operative per-block bar is per-file and per-consumer deltas,
   which the briefs already order. What is missing is a noise rule;
   section 7.1 item 5 supplies one. Keep the ceiling as the
   orchestrator's post-landing check, re-pinned after every landing,
   which the LJ-0.5 protocol already does.
2. **Flat-seconds compression loosens the wing's bar, and nobody says
   so.** DD24 judges the wing per-line against the AC baseline ratio
   times 1.15. Compression at flat seconds raises that baseline by up
   to 5.3 percent at the target, so the wing's permitted cost rises by
   the same factor. Against P-m's twenty-to-sixty-fold class gaps this
   is immaterial, but it should be named in `[ratio]` when LJ-0.5
   re-measures, so a wing pass is not read as stronger than it is.
3. **A rising ratio after a landing is the certificate becoming
   honest, not damage.** P-q states this (`dev/LESSONS.md:2427`, the
   trap note). The ledger's own P-q paragraph already records it for
   block A. Keep repeating it in audits, because the number will keep
   rising as cheap lines leave.

## 6. WHAT EVERY SURVEY MISSED

**One cost term, and no hidden site.** All three passes (July's
`[L3.28]`, `[T208]`, `[LJ-0.4]`) priced savings at call sites and never
priced the kit. The orchestrator's audit `a83ea88` diagnosed this after
block B; the five measured blocks confirm it. That is the systematic
error, and it is one error, not five.

I ran the scan no survey ran: a mechanical repeated-block scan over all
78 masters, ledger caliber, this session. Two passes.

**6.1 Exact repeats (byte-identical, 4-line window, keep-one-copy
accounting). MEASURED:**

- Code-class raw saving: **264 lines**, spread over about 40 small
  classes of 6 to 12 lines.
- Preamble-class raw saving: 229 lines (imports and opens; not
  deletable by sharing).
- Near-duplicate fringe: 297 further covered lines whose blocks repeat
  inexactly.

**6.2 Structural repeats (identifier-blind, 6-line window). MEASURED:**
1,705 of 17,855 lines, 9.5 percent. Concentration: `Sound` 268,
`Unique` 234, `Model` 97, `Before` 79. The repeat mass sits exactly
where the surveys looked. There is no unexamined bulk. The surveys
looked in the right places; they mispriced what extraction costs. The
identifier-blind surface is the alpha-renamed family, and the kits
measured its realizable yield: the identifiers are the content, they
become kit parameters, and the instances re-write them as glue.

**6.3 The one real find: within-file exact repeats at unsurveyed
sites.** Extraction there needs a local helper, not a module, so the
kit arithmetic that killed B, E, G does not apply. MEASURED sites:

| Site | Raw lines | Evidence |
|---|---|---|
| `Unique` (7 classes) | about 54 | e.g. `src/L/Coding/Unique.lagda.md:299,343` (6x3), `:500,545` (8x2) |
| `Sound` (5 classes) | about 38 | e.g. `src/L/Coding/Sound.lagda.md:873,912` (8x2), `:346,498` (9x2) |
| `L/Axioms/Separation` | about 30 | `:452,459` (6x3), `:303,318` (4x4), `:478,485` (6x2). **No survey named this file** |
| `Slot`, `Recover`, `Parameters` | about 24 | `Slot:177,200`, `Recover:206,229`, `Parameters:377,382` |
| Cross-file pairs | about 22 | `Faithful:112`/`Order:126` (9), `Adequate:112`/`Internal:931` (7), `EnvSet:88`/`Recursion:168` (6) |

Raw total about 170 within reach, net after helper signatures and glue:
**about -80 to -140.** This is the sweep block of section 7.5. It is
also the honest ceiling of what remains: T208's lever (b) sits inside
it, so do not double-count.

**6.4 The class no pass measured, named honestly:** semantic proof
shortening, a better lemma route through an existing proof. No survey
priced it, no comparable exists, and the register's nearest analogues
(S14, S16) reverted at their gates
(`dev/memos/simplification-register.md:34,36`). Do not fund it blind. If
the owner wants it priced, it costs one probe per named site, and no
site is named today.

**6.5 For future surveys:** the scan above costs minutes and bounds the
whole extraction class before anyone writes a band. Order it in the
survey brief. A band above the scan's keep-one-copy figure for its
class is arithmetic error, not optimism.

## 7. THE BRIEF CORRECTIONS (the deliverable)

Each item is pasteable text, marked with where it goes.

### 7.0 Correct the record first: block G's sign

G's report table shows before 146, after about 195
(`_build/lj-0.4e-report.md:85-93`): kit +111 against suites -62, net
**PLUS 49**. The report's net cell prints "about -49", and the wrong
sign now stands in five places: `lj-0.4e-report.md:93`, the LJ-0.4b
brief (`_build/briefs/LJ-0.4b.md:30`), the LJ-0.8 brief's table, and
commits `4f40567` and `a83ea88`. A minus 49 would sit inside G's band;
the actual result is a sign-definite failure, worse than E's +19. Paste
into the next audit commit and into every future track-record table:

> CORRECTION (LJ-0.8): block G measured net PLUS 49, not minus 49. Its
> own table shows before 146, after about 195 (kit 111, suites save
> about 62). Earlier records carry the wrong sign. The corrected record:
> every kit block measured net positive (B +24, E +19, G +49); only
> relocation (C, -59) and deletion (A, -240) measured negative.

### 7.1 Standing additions for EVERY remaining compression brief

Paste all six. They encode what the five measured blocks paid to learn.

1. **The break-even gate, before any wiring.** "Write the kit and
   typecheck it. Count its in-fence lines. Compute break-even: kit
   lines divided by measured saving per site. If break-even exceeds
   your site count, STOP and report the three numbers. Do not wire."
   (Basis: B, E, G each discovered this after building; make it the
   first checkpoint.)
2. **The staging gate.** "Convert ONE site first. Measure its net with
   the ledger caliber. Project the block: one-site net times sites,
   plus kit. Write the projection into your report before converting a
   second site. If the projection misses the band floor, STOP with the
   projection as your result." (Basis: block C ran 38 minutes with no
   mid-flight number; block B's one-site anchor is the model,
   `_build/lj-0.4b-report.md:13-16`.)
3. **The line-band stop trigger.** "A stop is a deliverable in THREE
   cases: seconds rise, a consumer must unfold what it did not, or the
   measured net cannot reach the band floor. The third case is a
   refusal with a number, and two of five blocks have already returned
   it with credit." (Basis: C's brief named only the first two,
   `_build/briefs/LJ-0.4c.md:172-174`.)
4. **The twice-today rule.** "The shared module may hold only lines
   that exist at least twice in today's tree, verified by the repeated
   -block scan. Any line that occurs once stays in its chapter. Moving
   a once-occurring line is relocation, and relocation is failure."
   (This is the operational form of "a chapter must remain a chapter";
   the qualitative form is already in B's brief.)
5. **The noise rule for seconds.** "A per-file delta under 0.5 s or
   under 5 percent, whichever is larger, is noise: report it as flat.
   Above that, run the file a third time and report all three numbers.
   Never report a verdict word where a number fits." (Basis: the wall's
   own three measurements spread 0.82 s,
   `dev/ledger.toml:2477-2499`.)
6. **Kit preservation.** "If you refuse a kit, do not delete it. Move
   it to `_build/kits/<task>-<name>.lagda.md` and cite the path in your
   report." (Basis: E and G deleted `Walk` and `Lex`; B parked `Frame`
   in volatile `/tmp`, `_build/lj-0.4b-report.md:5`.)

### 7.2 Block D: do not write the brief

Skip D. Paste into PLAN's LJ-0.4 row and the journal:

> Block D is SKIPPED on review evidence, not attempted. Four kit blocks
> measured net positive on the same arithmetic D relies on. [LJ-0.8]
> measured Model's repeat surface at zero 4-line blocks over 1,289
> lines, and read the N4 sites: the in/out pairs are two-way decode
> content with per-clause equational glue
> (src/L/Coding/Model.lagda.md:588-637), the class B measured as
> non-extractable. The skip saves a dispatch. Re-open only if a wing
> consumer makes the clause frame's break-even arithmetic positive.

### 7.3 Block F: replace the build brief with this probe brief

Do not send the planned F build. Send the probe T208 queued and nobody
ran. Core text:

> # LJ-0.4f-probe: the recursion-assembly bisect, GO or NO-GO
>
> tier: codex (default). THROWAWAY probe under D-1: nothing lands,
> nothing is committed, the deliverable is a report with two numbers.
>
> ## GOAL
> Fold `L.Choice.Table`'s assembly (Related/Realizes/IsRel, about 153
> lines at `src/L/Choice/Table.lagda.md:158-167` and below) onto
> `L.Hierarchy`'s shape (Values/Entries/Domain, about 127 lines at
> `src/L/Hierarchy.lagda.md:116-124` and below), in a scratch copy.
> Measure two things and stop.
>
> ## THE TWO NUMBERS
> 1. LINES: in-fence delta on the folded pair, ledger caliber.
> 2. SECONDS: cold check of both files before and after, one process,
>    `GHCRTS="-A64m -I0 -M8g"`, with the noise rule.
>
> ## GO CRITERIA, fixed before you start
> GO needs BOTH: delta at or below minus 60 on the pair, and seconds
> flat under the noise rule. Anything else is NO-GO. Report the numbers
> either way. Rule 13 measured over 400 s once for abstracting the
> recursion's value: if you see the wall, that is a NO-GO with the
> number, not a challenge.
>
> ## WHY A PROBE
> The -100 to -200 band is bracketed by comparables, not measured here
> (P-l). Five blocks have tested this survey and four failed. The probe
> prices THIS setting for one dispatch-hour instead of a build-day.

If the probe returns GO, write the F build brief with the six standing
additions of 7.1, the B-brief's chapter rules, and territory
`Hierarchy`, `Choice/Table`, `Choice/Before` plus at most one new
module. Fold H's helper consolidation into the same dispatch, run last.

### 7.4 Block H: the drop text

Paste into the register if F's probe is NO-GO or F does not fund:

> Block H is not dispatched alone. Measured basis: the tree-wide
> preamble repeat surface is 229 raw lines and import lines cannot be
> deleted by sharing; the deletable helper family is about 26 lines
> plus glue. Realistic net -15 to -40 does not pay for a dispatch that
> touches 12 masters and serializes every other writer (C-25).

### 7.5 The new block worth sending: the within-file dedup sweep

This replaces any C re-run. Core text for the brief:

> # LJ-0.4i: the measured dedup sweep, within-file first
>
> tier: codex (default)
>
> ## GOAL
> Extract byte-identical repeated blocks into local helpers, file by
> file. Land about 80 to 140 net, or refuse per file with numbers.
> The surface is MEASURED, not surveyed: [LJ-0.8] scanned all 78
> masters for 4-line repeated blocks with keep-one-copy accounting.
>
> ## THE SITES, measured raw savings
> - `src/L/Coding/Unique.lagda.md`: about 54 raw in 7 classes
>   (:299/:343 6x3, :500/:545 8x2, :512/:557, :601/:658, :731/:798,
>   :399/:641, plus the domAt-in setup family).
> - `src/L/Coding/Sound.lagda.md`: about 38 raw in 5 classes
>   (:873/:912 8x2, :890/:929 8x2, :346/:498 9x2, :338/:490,
>   :358/:511).
> - `src/L/Axioms/Separation.lagda.md`: about 30 raw (:452/:459 6x3,
>   :303/:318 4x4, :478/:485 6x2).
> - `src/L/Coding/Slot.lagda.md` :177/:200 (8x2); `Recover` :206/:229
>   (4x3); `FOL/Manipulation/Parameters` :377/:382 (4x3).
> - Cross-file, LAST and only if the within-file net is banked:
>   `Faithful:112`/`Order:126` (9x2), `Adequate:112`/`Internal:931`
>   (7x2), `EnvSet:88`/`Recursion:168` (6x2).
>
> ## THE RULES THAT DECIDE IT
> - Within-file extraction uses a local (private or where) helper. NO
>   new module for within-file work. Cross-file pairs may justify at
>   most ONE tiny shared module, and only if the pair savings exceed
>   its cost; the break-even gate applies.
> - A chapter must remain a chapter. The twice-today rule binds: only
>   lines occurring at least twice may move into a helper.
> - Per-file staging: extract, typecheck, measure net and seconds,
>   fill the report row, then the next file. Any file whose net is not
>   negative reverts alone; do not let one file sink the sweep.
> - Re-verify every site line number before editing. The scan ran on
>   2026-08-10; the tree moves.
> - P-q: expect zero seconds saved. The bar is flat seconds under the
>   noise rule.
> - DD4: these are local proof-shape helpers; their wing value is nil
>   and that is fine. Say so in the return and spend no effort forcing
>   generality (block A's brief has the same clause).

Plus the standing additions of 7.1 and the standard constraints block
(C-12, C-22, ledger caliber, linters, no commit, ASD-STE100 return).

### 7.6 Orchestrator-side actions, no brief needed

1. **Free the prose-bound dead names, about -60 to -65.** Block A
   verified them dead in code and kept them only because their names
   sit in files it could not touch
   (`_build/lj-0.4a-report.md:99-145,268-285`): 12 names, 49 lines,
   held by `src/Everything.lagda.md` prose; `Def-spec` and `A∈Def`
   held by `src/README.md:73`; `memPairAt`, `seqSet`, `allCodes` held
   by catalog prose. Rewire the prose in the catalog commit, delete
   the names, re-run the linters. This is the cheapest remaining
   negative number in the campaign, and only the orchestrator can
   take it.
2. **Preserve B's kit now.** `mkdir -p _build/kits && cp
   /tmp/lj04b-kit/Frame.lagda.md _build/kits/lj-0.4b-Frame.lagda.md`.
   The `/tmp` copy dies with the machine
   (`_build/lj-0.4b-report.md:5`).
3. **Reconstruct or re-derive `Walk` and `Lex` only on demand.** Both
   were deleted; their designs live in prose at
   `_build/lj-0.4e-report.md:43-52,110-136`. Note the revival cost is
   a rebuild, and register it in the DD4 trigger below.
4. **Fix the G sign** wherever the track-record table is next quoted
   (7.0).
5. **When LJ-0.5 re-measures after any landing**, add one line to
   `[ratio]`: the baseline ratio rose by arithmetic because lines
   left at flat seconds, so the wing's DD24 bar loosened by the same
   factor (section 5.2).

### 7.7 The DD4 revival trigger, tested and kept

The brief asked: does DD4 argue for landing a block that misses its
band? **No. The current position survives the test, with one repair.**
Landing a net-positive kit now spends the campaign's own meter, and
postponement costs nothing IF the kit survives and a trigger exists.
Neither condition holds today: two kits are deleted and no trigger is
registered. The repair, pasteable into the first wing clause-chapter
brief (LJ-1.x, the twelve-clause work):

> REVIVAL CHECK (DD4, registered by [LJ-0.8]). Three refused
> compression kits have measured wing value: the existential frame
> (`_build/kits/lj-0.4b-Frame.lagda.md`, 43 lines, walks the
> nested-truncation towers your clauses state), the traversal skeleton
> and the lex kit (designs in `_build/lj-0.4e-report.md`). Before you
> write any clause tower by hand, price instantiating Frame. Its
> break-even is about three consumers; your chapter alone may cross
> it. Report the arithmetic either way. A kit landed here counts as
> shared code (DD4) and lands inside the wing's own budget, where DD5
> measures it honestly.

## 8. LITERATURE USED

- `dev/literature/digest.md:209-262` (section 3, the hierarchy and the
  order). Read. Taken: the literature treats the S-sequence recursion
  and its uniform internal statement as ONE object, which lends F's
  unification architectural legitimacy; the measured rule-13 wall still
  governs, so the probe decides, not the citation. Also taken: SZ 1.14
  treats satisfaction as one uniformly Sigma-1 object; that fixes the
  CONTENT's identity, not the project's Sound/Unique chapter split, so
  the chapter rule stands on the owner's catalog, not on literature.
- `dev/literature/j-hierarchy.md`: skimmed headings only. WHY NOT: its
  order and well-order material bears on G's lex kit, which is closed
  by measurement; no remaining block touches the order.
- `dev/literature/fine-structure.md`: not read beyond its length. WHY
  NOT: no remaining block touches the Sigma-1 machinery; D, F, H and
  the sweep are mechanical extraction below the literature's level.
- The B report's own literature line
  (`_build/lj-0.4b-report.md:111-116`) is honest and correct: the
  existential nesting is a meta-language pattern with no literature
  identity.

## 9. ARCHIVE USED

- `archive/dev/TASKS-archived.md:276,279`: T205's verdict (16,000 was
  an unprobed optimistic end) and T208's row. Taken as the spine of
  section 2.
- `archive/dev/JOURNAL-archived.md:4200-4240`: the July survey record,
  the lever table, the gating and D15. Taken: the survey's own method
  words ("no compression lands without a before-and-after
  measurement"), which the campaign honored, and the lever bands the
  campaign has now measured against.
- `dev/memos/simplification-register.md:33-38`: S13 to S18. Taken: S14
  and S16 reverted at gates (the record against funding semantic
  rewrites blind, 6.4); S17 RED (the E boundary, held); S18 deferred by
  the owner (named in section 2 as a content-level option only the
  owner can re-open).
- `_build/l3.32-t208-report.md` in full. Taken: the deletion class was
  measured, the frame classes were surface counts; the calibration
  finding; the queued F bisect probe (3.1-3.6, section 6).
- `_build/lj-0.4-compression.md` in full. Taken: the block plan, N1-N8,
  the section-8 caveat that N1-N4 needed probes before dispatch.
- `dev/LESSONS.md:2254,2327,2363,2427` (P-m, P-r, P-s, P-q): the four
  laws this review leans on, each cited where used. P-s additionally
  warns that my sweep's net estimate divides no rates and stays a
  surface count.
- Git history: commits `4f40567` (the C stop and E/G audit), `a83ea88`
  (the B refusal and the arithmetic), `c65b0ce` (block A's landing and
  the worse ratio). Taken as the measured record.
- The five reports and four briefs named in my brief, all read in full.

## 10. WHAT I AM NOT SURE OF

1. **The sweep's net band (-80 to -140) is my estimate.** The raw 170
   is measured; the helper-signature and glue overhead (2 to 4 lines
   per class) is a design price. The staging gate in its brief exists
   to catch me being wrong per file.
2. **The structural 1,705 is an indicator, not a target.** The
   identifier-blind normalization is aggressive; some of that surface
   is coincidence of shape. I used it only to bound the class and
   locate concentration, never as a savings figure.
3. **G's true magnitude.** I infer +49 from the report's own table
   arithmetic (146 to about 195). The working tree is reverted, so
   nobody can re-measure it. The sign is certain; the magnitude is the
   report's own "about".
4. **F's probe may return GO**, in which case my 17,000 center moves
   down by F's measured delta, toward about 16,900. My projection
   half-weights F; the probe replaces the guess either way.
5. **The owner's intent behind "about 16,400".** I judged the number's
   evidence, not the intent. If the prerequisite's purpose is the DD5
   benchmark rather than the specific figure, the honest input to that
   benchmark is the measured standing, whatever it is, and the case
   for more compression dispatches weakens further.
6. **No seconds figure in this review is mine.** The brief forbade
   agda runs; every seconds number is quoted from the named reports
   and the ledger.
7. **Everything.lagda.md shows 77 structurally repeated lines** in my
   scan. It is the index, it is the orchestrator's file, and I did not
   evaluate it; the catalog's repetitiveness may be intentional prose
   structure in fences.
