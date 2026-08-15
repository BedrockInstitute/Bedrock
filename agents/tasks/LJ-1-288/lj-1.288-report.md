# LJ-1.288 report: a vendor config for the dispatch policy, and a clock that belongs to the vendor

STATUS: COMPLETE. All six acceptance tests pass. The work landed.

Run on 2026-08-15, Beijing 15:41 to 16:20. No Agda was run, per the brief.

## THE SIX ACCEPTANCE TESTS

Baselines were captured BEFORE the first edit and are tracked beside this file:
`baseline-policy-print.txt`, `baseline-tests.txt`, `baseline-checker.txt`,
`baseline-dispatch-check.txt`.

### 1. `scripts/dispatch_policy.py` prints what it printed before. PASS

```
$ .venv/bin/python scripts/dispatch_policy.py > after.txt   # EXIT=0
$ diff <(norm baseline-policy-print.txt) <(norm after.txt)
BYTE-IDENTICAL apart from the wall-clock minute
```

`norm` replaces the live timestamp `Beijing 2026-08-15 15:41` with `<NOW>`. That
one field is the clock reading itself and it moved from 15:41 to 15:51 because
ten minutes passed. Every other byte is the same: the mode line, the clock line,
the window line, the boundary line, the reason, the revert, the three table rows,
the invariant, the note, the harness line and the limit paragraph.

### 2. The clock test passes, and it now holds 66 checks. PASS

```
$ .venv/bin/python scripts/tests/test_dispatch_clock.py
test_dispatch_clock: all checks passed (66)
EXIT=0
```

35 before, 66 after. 31 new checks, all in one new section named `the vendor`
(`scripts/tests/test_dispatch_clock.py:169-403`). They pin: the absent config,
the shipped config against the built-in floor, `MODEL`, `PEAK_WINDOWS`, a banded
vendor with its own hours, a flat vendor's refusal of the clock, `auto_mode`, the
pin beating both, the unwired refusal, a frozen record still judgeable under an
unwired vendor, ten malformed configs, and the two DD19 cross-checks.

### 3. `scripts/check-dispatch-policy.py` exits 0. PASS

```
$ .venv/bin/python scripts/check-dispatch-policy.py
dispatch policy OK: `in-harness-subagent-mode` in force, 586 brief(s) read, 30 pre-epoch note(s) not judged
EXIT=0
```

586 briefs, not the 585 the brief claimed. MEASURED: the extra brief is
`agents/tasks/LJ-1-288/LJ-1.288.md`, which this task wrote before it ran. The
baseline, captured after the brief was written, also reads 586.

### 4. `dispatch.py check` behaves as it did. PASS

```
$ .venv/bin/python .claude/skills/codex-dispatch/dispatch.py check \
    agents/tasks/LJ-1-279/LJ-1.279.md --agda
EXIT=1
$ diff baseline-dispatch-check.txt after.txt
IDENTICAL
```

Both refusals are unchanged, word for word. Exit code 1 before and after. That
exit code is dispatch.py's own standing refusal against a stale brief, and it is
not caused by this task.

### 5. Deleting the config crashes nothing. PASS

With `dev/vendors.toml` moved away, all four gates were run again:

```
policy printout   EXIT=0   IDENTICAL to baseline apart from the wall-clock minute
test_dispatch_clock: all checks passed (66)   EXIT=0
check-dispatch-policy.py                      EXIT=0
dispatch.py check                             EXIT=1, IDENTICAL to baseline
$ .venv/bin/python scripts/dispatch_policy.py --vendor
VENDOR IN FORCE: `deepseek`
  source: the built-in default, because dev/vendors.toml is absent
  model: deepseek-v4-pro
  pi provider: deepseek
```

The file was restored immediately afterwards. MEASURED: an absent config changes
no observable answer.

### 6. An unwired vendor produces a loud, specific refusal. PASS

`dev/vendors.toml` was replaced with `probe-glm-flat.toml`, which declares
`glm` with `pi_wired = false`. The full capture is in
`probe-unwired-refusal.txt`. The dispatch path:

```
$ .venv/bin/python .claude/skills/codex-dispatch/dispatch.py check \
    agents/tasks/LJ-1-279/LJ-1.279.md --agda
dispatch_policy: the vendor in force is `glm`, and its row says `pi_wired = false`.
`pi` is NOT wired to `glm`, so no head can start on the model
`glm-model-id-not-yet-known`. Source: /Users/alsg/Agentic/Bedrock/dev/vendors.toml,
`in_force = "glm"`. Set `in_force` to a wired vendor in
/Users/alsg/Agentic/Bedrock/dev/vendors.toml, or wire `pi` to `glm` and set
`pi_wired = true` in the same row. This is a refusal, not a reminder: a
declaration is not a wiring.
EXIT=1
```

The refusal names the vendor, the field, the model, the source file and the two
fixes. `dispatch.py` stops before it can launch anything. The config file was
restored immediately afterwards.

## THE CONFIG FILE

Path: `dev/vendors.toml`, 100 lines. It sits beside the four TOML configs the
brief named, and `REUSE.toml:32` already covers `dev/**`, so `reuse lint` passes
with no new declaration (MEASURED, 2346 of 2346 files compliant).

It needs no `dev/build-manifest.toml` entry. MEASURED: that manifest declares the
lifecycle of files under `_build/` only (`dev/build-manifest.toml:1`), and
`check-build-manifest.py` exits 0.

Full contents:

```toml
# dev/vendors.toml: the VENDOR DATA that the dispatch policy runs on.
#
# WHAT THIS FILE IS FOR. It names the vendor in force, the model ID that vendor
# runs, whether `pi` is wired to that vendor today, and the price bands the
# vendor bills on. `scripts/dispatch_policy.py` reads it with `tomllib`.
#
# WHAT THIS FILE DOES NOT HOLD, AND THIS IS THE DD19 LINE. It holds NO head
# table, NO mode, NO case, NO tier token and NO invariant. THE HEAD TABLES LIVE
# IN `scripts/dispatch_policy.py`, and `AGENTS.md` names that file the ONLY home
# of the tables. This file says WHEN a vendor is dear. That file says WHICH MODE
# each price band selects. Neither one states the other.
#
# DELETE THIS FILE AND NOTHING BREAKS. `scripts/dispatch_policy.py` then uses its
# built-in default vendor, which holds the data the code carried before this
# config existed. That default is a compatibility floor, not a second home: when
# this file exists it wins completely, and no field merges into it from the
# default.
#
# THE CAVEAT, from the repository owner, 2026-08-15. `pi` is wired to deepseek
# and to no other vendor today. This file opens compatibility before the need.
# It does not claim support that exists. A vendor row with `pi_wired = false` is
# a legal declaration, and `scripts/dispatch_policy.py` refuses loudly when that
# vendor is in force and a head must start.
#
# NO FIELD HAS A SILENT DEFAULT, because an escape hatch is the shape a wrong
# choice hides in (`dev/LESSONS.md` C-43). Each vendor row is one of two kinds,
# and each kind has its own required fields. A field that belongs to the other
# kind is a refusal, never an ignored line.

# The vendor in force. It must match one `[vendors.<name>]` table below.
in_force = "deepseek"

# ---------------------------------------------------------------------------
# THE VENDOR ROWS. Every row declares these three fields:
#
#   model        the model ID the herdr heads run. It is never empty.
#   pi_provider  the provider name `pi` needs for this vendor.
#   pi_wired     true only if `pi` can really run this vendor today.
#
# A BANDED VENDOR bills different prices at different hours. It adds:
#
#   base_state   the band that holds outside every declared window.
#   windows      the hours the vendor bills at another band, in Beijing time.
#                Each window names its band, its start and its end. A window is
#                half-open [start, end), so 09:00 is peak and 12:00 is off-peak.
#                The windows are ordered by start time and they never overlap.
#
# A FLAT VENDOR bills one price at every hour. It adds:
#
#   default_mode the mode that `VERSION_IN_FORCE = "auto"` resolves to. A flat
#                vendor gives the clock no basis, so the clock does not run.
#
# THE BAND NAMES ARE NOT FREE TEXT. `scripts/dispatch_policy.py` maps each band
# to a mode in `CLOCK_STATES`, and it refuses a band that the map does not know.
# ---------------------------------------------------------------------------

[vendors.deepseek]
model = "deepseek-v4-pro"
pi_provider = "deepseek"
pi_wired = true
base_state = "off-peak"
windows = [
    { state = "peak", start = "09:00", end = "12:00" },
    { state = "peak", start = "14:00", end = "18:00" },
]

# ---------------------------------------------------------------------------
# HOW TO ADD A VENDOR. Copy one template below, fill the model ID, and set
# `in_force` above.
#
# THE MODEL ID IS THE OWNER'S TO SUPPLY. This file ships no glm row and no grok
# row, because an invented model ID writes a certainty that no evidence gives.
# A row is added when its model ID is known, not before.
#
# A FLAT VENDOR, which is every vendor that does not price by the hour:
#
#   [vendors.glm]
#   model = "<the model ID, from the vendor>"
#   pi_provider = "glm"
#   pi_wired = false
#   default_mode = "in-harness-subagent-mode"
#
# A VENDOR WITH THREE PRICE BANDS declares two of them and names the third as
# its base:
#
#   [vendors.example]
#   model = "<the model ID, from the vendor>"
#   pi_provider = "example"
#   pi_wired = false
#   base_state = "off-peak"
#   windows = [
#       { state = "peak", start = "09:00", end = "12:00" },
#       { state = "super-peak", start = "14:00", end = "18:00" },
#   ]
#
# A NEW BAND NAME NEEDS ONE NEW ROW IN `CLOCK_STATES`, in
# `scripts/dispatch_policy.py`. That row says which mode the band selects. That
# is a policy decision about heads, so it belongs in the policy file and not
# here. This is the DD19 line again, seen from the other side.
# ---------------------------------------------------------------------------
```

WHY NO GLM ROW AND NO GROK ROW SHIPPED. I do not know their model IDs, and
`AGENTS.md` forbids adding a certainty the evidence does not give. The format
supports them today, and the two templates show the exact shape. The probe
configs beside this report declare glm both ways and prove it.

## THE DD19 LINE, IN ONE SENTENCE

**`dev/vendors.toml` says WHEN a vendor is dear, which is vendor data; `scripts/dispatch_policy.py` says WHICH MODE each price band selects and what each head is, which is policy; and neither file states the other's half.**

WHERE IT IS STATED, in both files, as the brief required:

- `dev/vendors.toml:7-11`, the header block titled "WHAT THIS FILE DOES NOT HOLD,
  AND THIS IS THE DD19 LINE".
- `dev/vendors.toml:95-99`, the same line seen from the other side: a new band
  name costs one row in `CLOCK_STATES`, in the policy file.
- `scripts/dispatch_policy.py:58-65`, the module docstring section titled "THE
  VENDOR DATA IS NOT HERE, AND THAT IS THE DD19 LINE".
- `scripts/dispatch_policy.py:411-415`, above `CLOCK_STATES`: "CLOCK_STATES IS
  POLICY AND IT STAYS HERE".

THE LINE IS ALSO ENFORCED, not only stated (C-48). The config may NAME a band or
a mode. The policy file decides whether that name is real:

- `_validate_vendor_against_policy()` refuses a band that `CLOCK_STATES` has no
  row for (`scripts/dispatch_policy.py:936-955`).
- The same function refuses a `default_mode` that is not in `POLICY`
  (`scripts/dispatch_policy.py:956-961`).
- Both run when the module loads, not at the first dispatch
  (`scripts/dispatch_policy.py:1023-1026`, the call at `:1026`).

MEASURED: the config holds zero head tables, zero cases, zero tier tokens and no
invariant. The policy file holds zero vendor literals outside `BUILTIN_VENDOR`,
which is labelled a compatibility floor and is read only when the config is
absent.

I did NOT edit `AGENTS.md`, and I do not think the `AGENTS.md:98` row needs to
change. It says `scripts/dispatch_policy.py` is "the ONLY home of the tables".
That is still true: the tables did not move, and no vendor row restates one.

## WHAT HAPPENS UNDER EACH CONFIG

The full evidence is `probe-output.txt`, produced by `probe-vendor-config.py`.

| Config | Clock | `auto` resolves to | `default_harness()` |
|---|---|---|---|
| **No config** | runs, deepseek's hours | the clock's mode | `herdr`, as today |
| **Naming deepseek** | runs, deepseek's hours | the clock's mode | `herdr`, as today |
| **Naming glm, flat, unwired** | REFUSES, names glm | glm's `default_mode` | REFUSES, names glm |
| **Naming glm, banded, wired** | runs, glm's OWN hours | the clock's mode | `herdr-pi` |
| **Naming an unknown vendor** | never loads | never loads | never loads |

**NO CONFIG.** `BUILTIN_VENDOR` applies. Its source line says so plainly: "the
built-in default, because dev/vendors.toml is absent". Every answer is today's.
MEASURED by acceptance test 5.

**NAMING DEEPSEEK.** Identical to no config. A test pins that the shipped config
and the built-in floor declare the same vendor, so the two can never drift apart
in silence (`scripts/tests/test_dispatch_clock.py:280-287`).

**NAMING GLM, FLAT AND UNWIRED.** Three separate things happen, and each one is
loud:

1. `clock_state()` REFUSES: "the vendor in force is `glm`, which declares no
   price window, so the clock has no basis and must not be read."
2. `auto_mode()` returns `in-harness-subagent-mode`, glm's declared
   `default_mode`. This is the answer to the brief's design question.
3. `default_harness()` REFUSES, and `dispatch.py` dies on it.

The inspection command still PRINTS. That is deliberate: a reader who has just
set an unrunnable vendor needs to see why, and a traceback is not a reading. The
refusal appears in the printout on the harness line, prefixed `REFUSED.`
(`scripts/dispatch_policy.py:816-827`).

**NAMING AN UNKNOWN VENDOR.** The load refuses before anything else runs:

```
dispatch_policy: .../probe-unknown-vendor.toml: `in_force` names the vendor `grok`,
which has no `[vendors.grok]` table. The declared vendors are: deepseek.
A vendor this file does not declare is never guessed (C-43).
```

**A FOURTH CASE WORTH THE OWNER'S ATTENTION.** A banded vendor other than
deepseek drives the clock on ITS hours. With glm dear from 20:00 to 23:00, 15:00
is off-peak for glm while the same instant is PEAK for deepseek, from the same
code. That is the proof that the windows became data about a vendor rather than
a global fact (`scripts/tests/test_dispatch_clock.py:295-300`).

## THE DIFF OF THE PRINTED OUTPUT

For deepseek and for no config, the printed output has NO diff at all, apart from
the wall-clock minute inside the clock line. That was acceptance test 1 and it is
the whole point of the exercise.

The output differs only where the vendor is not deepseek, and there it differs
because it must:

```
 DISPATCH POLICY: `in-harness-subagent-mode` is IN FORCE
-  selected by the clock, not by a ruling (VERSION_IN_FORCE = 'auto')
-  clock: PEAK now. Beijing 2026-08-15 15:51, window 14:00 to 18:00
-  peak windows (Beijing): 09:00 to 12:00, 14:00 to 18:00
-  next boundary: 2026-08-15 18:00 Beijing, off-peak begins, mode becomes `pi-subagent-mode`
+  selected by the vendor's `default_mode`, not by a ruling and not by a clock (VERSION_IN_FORCE = 'auto')
+  vendor: `glm` declares no price window, so the clock has no basis and does not run
+  default_mode: `in-harness-subagent-mode`
+  vendor source: /Users/alsg/Agentic/Bedrock/dev/vendors.toml, `in_force = "glm"`
```

ONE OTHER CHANGE, and it is cosmetic. The model column was a literal width of 18,
which fitted `deepseek-v4-pro` exactly. A longer model ID pushed the `tier:`
column out of line. The width is now `max(18, longest model)`, so deepseek's
table is unchanged to the byte and a long model still aligns
(`scripts/dispatch_policy.py:893-897`). MEASURED both ways.

## THE DESIGN QUESTION, ANSWERED

I took the orchestrator's reading, because I could not find a better shape. I
sharpened it in three places.

**1. THE WINDOWS BECAME THE VENDOR'S OWN ROWS.** Deepseek's 09:00-12:00 and
14:00-18:00 are now two rows in `[vendors.deepseek]`. `PART 2` is answered by
construction: a vendor with no windows has no clock, because the clock reads the
vendor's windows and there are none.

**2. `default_mode` IS PER-VENDOR AND REQUIRED, NOT A GLOBAL FALLBACK.** The
brief proposed "a configured `default_mode`". A single global one would be an
escape hatch: it would apply to any vendor that forgot to declare its bands, and
that is exactly the shape C-43 warns about. So a flat vendor MUST name its own
`default_mode`, and one that does not is refused when the config loads. There is
no value for `auto` to fall back TO.

**3. THE TWO VENDOR KINDS ARE EXCLUSIVE, AND BOTH DIRECTIONS ARE REFUSED.** A
banded vendor that also names `default_mode` is refused, because the field would
never be read. A flat vendor that also names `base_state` is refused, because it
has one band and the field names nothing. A field that is never read is a wish
written as configuration.

The precedence is unchanged and is pinned by test:
**a pin in `VERSION_IN_FORCE` beats everything; then the vendor's clock if it has one; then the vendor's `default_mode`.**

## THE DD4 SHAPE ANSWER

**A THIRD MODE: YES.** `POLICY`, `CLOCK_STATES` and `ALIASES` are plain dicts
keyed by mode name, and nothing in the config names a mode except one optional
`default_mode` string, which is validated against `POLICY` rather than listed.
A third mode is one new `POLICY` entry and, if a band should select it, one new
`CLOCK_STATES` row.

**A VENDOR WITH THREE PRICE BANDS: YES, AT A COST OF ONE ROW, AND THE COST IS IN
THE RIGHT FILE.** A window carries its band name, so three bands are two window
rows plus a `base_state`, all in the config. The boundary list is built from the
set of every window start and every window end, so two adjacent bands share one
boundary instead of producing a spurious pair. The one thing the config CANNOT
do alone is say which mode the third band selects, and that refusal is
deliberate: it is a decision about heads, so `CLOCK_STATES` must gain the row.
MEASURED, `probe-three-bands.toml`:

```
VALIDATION REFUSED: dispatch_policy: the vendor `example` names the price band
`super-peak`, and `CLOCK_STATES` has no row for it. The known bands are off-peak,
peak. A new band needs a row saying which mode it selects, and that row is a
decision about heads, so it belongs in this file and never in the config.
```

## PREMISE CHECKS (C-44)

| Premise | Verdict |
|---|---|
| `CLOCK_STATES` is hardcoded and its comment ties the clock to deepseek's pricing | VERIFIED, with line drift. It was at `:122-125`, not `:120-124`. The comment reads exactly as the brief quoted it |
| `MODEL = "deepseek-v4-pro"` is the vendor seam at `:215` | VERIFIED, with line drift. It was at `:218`. The comment did claim a swap is one edit to the literal, and it is now corrected |
| `FLASH` and `model_for()` were deleted, and no automatic model rule may return | VERIFIED at `scripts/dispatch_policy.py:220-241` before my edit. I reintroduced nothing. MEASURED: zero occurrences of `flash` or `model_for` in my diff |
| The public API list has twelve names | VERIFIED as present, but the list is WIDER than the real dependency. MEASURED: `dispatch.py` calls only five, which are `default_harness`, `canonical`, `in_force`, `head` and `tier_token`. It also reads `EMERGENCY_TOKEN` through `getattr` at `.claude/skills/codex-dispatch/dispatch.py:659` |
| `dev/` holds four TOML configs | VERIFIED: `build-manifest.toml`, `glossary.toml`, `ledger.toml`, `rules.toml`. `vendors.toml` is the fifth |
| `AGENTS.md:98` names the policy file the ONLY home of the tables | VERIFIED, quoted exactly |
| The checker reads 585 briefs | REFUTED, harmlessly. MEASURED 586, before and after, because this task's own brief is one of them |

**ONE CONSUMER THE BRIEF DID NOT NAME, and it matters.**
`scripts/check-dispatch-policy.py:191` reads `P.MODEL` and tests every governed
document for that string. `MODEL` therefore had to stay a module-level string
with the same name. It did. MEASURED: the governed globs are `AGENTS.md`,
`scripts/README.md` and `dev/**/*.md` (`scripts/check-dispatch-policy.py:84-85`),
so a TOML config is not scanned. `dev/vendors.toml` names
`scripts/dispatch_policy.py` six times anyway, so it would pass that check even
if the glob widened to TOML.

## ONE FINDING FOR THE ORCHESTRATOR, OUTSIDE MY WRITE SCOPE

`.claude/skills/codex-dispatch/dispatch.py:112` calls `POLICY.default_harness()`
at MODULE level, inside `try: ... except Exception`. `SystemExit` does not
inherit from `Exception`, so the unwired refusal propagates and kills
`dispatch.py` with the message. That is why acceptance test 6 is loud, and I
consider it correct for a launch.

IT IS BROADER THAN A LAUNCH, and the orchestrator should know. Because the call
is at import, an unwired vendor also stops `dispatch.py status` and every other
subcommand. INFERRED from the call site, not measured on `status`. If the owner
wants inspection to survive an unwired vendor, that one call moves out of module
scope and into the launch path. I did not touch the file, per the brief.

A SECOND, SMALLER ONE. `.claude/skills/codex-dispatch/dispatch.py:120` hardcodes
`PI_PROVIDER = "deepseek"`, and `:82` hardcodes `DEFAULT_MODEL =
"deepseek-v4-pro"`. Both are vendor literals outside the config.
`scripts/dispatch_policy.py` now exposes `MODEL` and `PI_PROVIDER` from the
vendor row, so each is a one-line adoption when the orchestrator chooses.

## WHAT I CHANGED

- `dev/vendors.toml`, NEW, 100 lines. The vendor data and the DD19 line.
- `scripts/dispatch_policy.py`, 634 lines changed. The vendor section, the
  loader, the vendor-conditional clock, `auto_mode()`, `require_vendor_wired()`,
  `render_vendor()`, the `--vendor` command, the load-time cross-checks, and the
  corrected vendor-seam comment.
- `scripts/tests/test_dispatch_clock.py`, 237 lines added. 35 checks became 66.
- `agents/tasks/LJ-1-288/`, this report, the brief, four baselines, five probe
  configs, one probe script and two probe outputs.

MEASURED: `git status --porcelain` shows exactly these paths, plus two untracked
sibling directories that were already there and that I did not touch.

## GATES RUN

| Gate | Result |
|---|---|
| `lint-prose.py --check` on all six files I wrote | EXIT=0, silent |
| `reuse lint` | compliant, 2346 of 2346 files |
| `check-rule-ids.py` | clean, 45 files, 152 lessons, 67 decisions |
| `check-probes.py` | clean, no probe outside `agents/tasks/` |
| `check-build-manifest.py` | every file in `_build/` declares a lifecycle |
| `check-dispatch-policy.py` | OK, 586 briefs |
| `make devdocs taskindex agentsguard dd4 dd25 archivecited tree fences` | all EXIT=0 |
| `make premises` | EXIT=2, PRE-EXISTING |

THE `premises` FAILURE IS NOT MINE. MEASURED: it names 13 briefs, from LJ-1.217
to LJ-1.283, each missing a `## PREMISES` section. `agents/tasks/LJ-1-288` appears
zero times in its output, because this brief carries the section. I did not run
`make check`, per the brief.

I DID NOT RUN AGDA. The sibling task in `agents/tasks/LJ-1-287/` holds the Agda
work and needs a quiet machine.

## ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-285/lj-1.285-report.md:96`. It claims the renamed structure
  survives a third mode, and names `PEAK_WINDOWS`'s "own two-window shape" as the
  one place that enumerates two. TAKEN: that sentence is exactly the seam this
  task had to open, so I generalized the window shape rather than the mode dicts,
  which were already generic.
- `archive/dev/JOURNAL-archived.md:191`. "DIED on a backend model rejection
  (deepseek-v4-pro unavailable until early [August 2026])". TAKEN: it is the one
  archived record of the model literal itself failing, and it confirms that the
  model ID is a fact about a vendor with its own history. That is an argument for
  the ID living in vendor data rather than in a policy literal. FROZEN, read
  only, not edited.

## LITERATURE USED (DD18)

None. No mathematical literature bears on a configuration format, as the brief
said. WHY NOT: this task writes no mathematics and proves no theorem. It moves
four literals and one table into a TOML file and adds refusals.
