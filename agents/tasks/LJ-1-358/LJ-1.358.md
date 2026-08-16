# LJ-1.358: redesign the DD18 mechanism on `[LJ-1.357]`'s corrected foundation

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** No Agda.

## WHY, and read this before anything else

**The owner asked for a mechanism that shouts when DD18 is not followed.**
`[LJ-1.356]` designed one. **`[LJ-1.357]`, the adversarial review, OVERTURNED
it.** **The core idea survived and three of its four signals did not.** **You
are the second pass, and you start from the corrected facts rather than from
the design.**

## WHAT `[LJ-1.357]` SETTLED, and you must not re-open these

**1. A LIVE-TREE CITATION IS NOT DD18 COMPLIANCE. MEASURED.** `dev/PLAN.md:608`
enumerates four corpora and every one is an ARCHIVE. `AGENTS.md` says「FOUR
ARCHIVES」. **And the delivered checker settles it in bold at
`scripts/gate/check-archive-cited.py:26-27`:「A section that names only live
`agents/tasks/` directories is THE DRIFT.」** **So `[LJ-1.356]`'s「the live half
is healthy」measured the health of the thing a wired checker calls the disease.
There is no healthy half.**

**2. R1 IS A NEW RULE, NOT AN ENFORCEMENT OF DD18.** **DD18's own row states its
satisfaction condition:「Each is satisfied by one honest line naming the
corpus」— ONE line per section, not four.** **R1 demands four.** **That may
still be the right rule. It is NOT the current rule, and a design that
presents it as enforcement misleads the owner who must rule on it.**

**3. R4's FOUNDING COUNTERFACTUAL IS FALSE. MEASURED.** `[LJ-1.356]` claimed R4
「is what would have stopped `[LJ-1.107]`」. **`[LJ-1.357]` ran R4's own code on
`[LJ-1.107]`'s brief and got `R4 kept terms: []`, zero candidates.**

**4. R3's HEADLINE IS FALSE. MEASURED.** Not 93 real failures. **51 of 92 fail
ONLY on a missing LITERATURE USED heading; 30 of 55 unanswered paths ARE
answered by a deeper path. The honest rate is about 15.** **And R3 enforces
「answer your brief」, which is WIDER than DD18.**

**5. DD4's PRECEDENT IS WEAKER THAN CLAIMED.** Number 1 verified. **The tool
for number 2, `dd4dup.py`, DOES NOT EXIST**; the re-derivation found 6
duplicate groups over 14 briefs. **`LJ-1-343` and `LJ-1-344` differ by the case
of one word.** **Distinct text is cheap.**

**6. R2's THRESHOLD IS A METRIC ON A RULE WHOSE PARENT FORBIDS ONE.** **DD4 has
no metric by the owner's ruling because a count is gamed the moment it gates.**
**Gaming R2 was MEASURED at one keystroke, twice. R2 must PRINT, never gate.**

**7. THE FOUNDING STORY WAS A MISATTRIBUTION, and I have now repaired it.**
`[LJ-1.107]` **DID** survey: `agents/tasks/LJ-1-107/lj-1.107-report.md:235-238`
names the retired module and its size, confirmed at
`archive/dev/TASKS-archived.md:116`. **It CHOSE to build its own 97-line CSB
for h-sets.** **A choice is not a lapse.** I corrected
`scripts/gate/check-archive-cited.py` today; **the `levelIn` case survives and
is the only case now cited.**

## WHAT `[LJ-1.357]` UPHELD

- **「Gate the ENUMERATION, not the relevance」is the right idea.**
- **The DD4-SHAPE argument is the best contribution**: a heading gate holds
  when the gated form forces TASK-SPECIFIC content, and decays when the
  minimal compliant form is CORPUS-GENERIC. **`[LJ-1.357]` weakened its
  evidence and did not refute the principle.**
- **R3 is the genuinely mode-proof half**, because a report is a file in the
  tree under both dispatch modes.
- **R4's synonym diagnosis is correct**: the archive spells it
  「Cantor-Schroeder-Bernstein」and briefs say「Cantor-Bernstein」.
- **The costs reproduce.**

## YOUR TASK

**Produce the SECOND design, and separate two things `[LJ-1.356]` fused:**

**A. WHAT ENFORCES DD18 AS IT IS WRITTEN TODAY.** One honest line per section.
**Say plainly whether anything mechanical can do more than the heading check
already does, given that satisfaction condition.** **If the answer is「almost
nothing」, that is a real finding and you should say it.**

**B. WHAT DD18 WOULD HAVE TO BECOME for a mechanism to bite, and what that
mechanism then is.** **Present it as a RULE CHANGE for the owner to rule on,
with its cost to every future brief author stated in lines and minutes.**
**The owner then rules on a rule, not on a checker.**

**Judge every signal you keep by three questions, each answered with a
number:** can it be passed by pasting; what does it cost per dispatch; **what
does it FAIL to catch.** **Name your own false negatives; a design claiming
full coverage is wrong.**

**Carry forward what survived and DROP what did not.** **Do not re-justify R4
with the refuted counterfactual. Do not quote R3's 93.**

## THE ABORT CRITERION (D-1)

- **A DESIGN WITH A AND B SEPARATED, each priced.** Best outcome.
- **A IS EMPTY.** **If DD18 as written cannot be enforced beyond the heading,
  say so with the evidence.** **That is a valuable answer and it makes B the
  only question.**
- **THE WHOLE APPROACH IS WRONG.** **If enumeration gating cannot work at all,
  give the evidence and stop.** `[LJ-1.357]` upheld the idea; **you are allowed
  to disagree with it, with a measurement.**

## CONSTRAINTS

- **PROPOSE, DO NOT LAND.** Write only in `agents/tasks/LJ-1-358/`. **You may
  write and RUN a prototype there for real numbers; do not wire it into
  `Makefile` or `scripts/`.** `src/` is forbidden (I-5).
- **DO NOT EDIT `AGENTS.md` or `dev/PLAN.md`.** DD19 gates the first. **Write
  any needed diff into your report.** **`[LJ-1.357]` judged `[LJ-1.356]`'s
  `AGENTS.md` insert DANGEROUS: it stated an enforcement that did not exist,
  dropped the mode caveat, and broke the rulebook's own prose rules at 22
  words, passive voice and a four-word noun cluster. Do not repeat that.**
- **`[LJ-1.356]`'s prototype is at `agents/tasks/LJ-1-356/probe_dd18_shout.py`
  and `[LJ-1.357]`'s re-runs are in `agents/tasks/LJ-1-357/`. Read and COPY
  them; edit neither directory.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-358/lj-1.358-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  ASD-STE100. Evidence is `file:line`, and for a rate, the command that
  produced it. Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**My last two briefs on this subject each carried a claim an agent measured
FALSE, and the second one was a claim I had accepted from the first inside an
hour.** **The one at risk now: that「gate the enumeration, not the relevance」
survives at all.** **`[LJ-1.357]` upheld it, but it upheld it while refuting
three of the four signals built on it, and an idea whose every instance fails
is not obviously a good idea.** **Test the idea itself, not only its
instances.**

## THE RULES

**C-59, written today: a gate you do not run is worth what a gate you do not
have is worth.** **C-48: a policy that only a document states is not
enforced.** **C-45, C-57, D-10, C-42, C-44, C-53, P-l, P-k.**
**C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD17, DD18, DD19, DD23, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and
`--grep archive`, and read every statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46).

**DD4 is evidence here rather than background, and `[LJ-1.357]` weakened it.**
**Re-derive its numbers yourself before you lean on them**, and note the
sharpest point against any DD18 metric: **DD4 has no metric BY RULING, because
a count is gamed the moment it gates.** **Any threshold you propose must answer
that objection or print instead of gating.**

## ARCHIVE (DD18)

**This section is the subject of the task. Give it the survey the task is
about, and report if I failed to.**

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:7` and `:89`.** The
  CSB the founding story is about. **`:7` holds the spelling that defeated R4's
  term match.**
- **`archive/dev/TASKS-archived.md:116`**, the T81 row `[LJ-1.107]` actually
  cited. **It is the evidence that the founding story was wrong.**
- **`archive/dev/DECISIONS-archived.md:42`.** **`[LJ-1.357]` upheld a NEGATIVE
  here: D20 governs RETIRING code, not surveying it, so no survey rule existed
  to die.** **Spot-check it; if a survey rule did exist, the history changes.**
- **`archive/dev/JOURNAL-archived.md`.** **`[LJ-1.357]` measured that
  `grep -c "LJ-1\."` on this file returns ZERO**, so it holds nothing about
  `[LJ-1.107]` and my earlier brief asked for something that cannot exist.
  **Confirm that, and do not substitute another passage silently: that
  substitution is one of the defects `[LJ-1.357]` found.**

**Return an ARCHIVE USED section naming ONE line read per archived file, with
WHY NOT for anything you decline.**

## LITERATURE (DD18)

**`[LJ-1.357]` verified `[LJ-1.356]`'s negative: `formalizations-landscape.md`
is 421 lines of systems index and holds no process mechanism, and nothing else
in `dev/literature/` bears on rule design.** **That negative is now checked
twice. Do not spend a third pass on it; cite it and move on.** Return a
**LITERATURE USED** section saying exactly that.

## SCOPE (read)

`agents/tasks/LJ-1-357/lj-1.357-report.md` WHOLE, FIRST. It is the corrected
foundation and it is 724 lines. **Then `dev/PLAN.md`'s DD18 row, for the
satisfaction condition R1 overshot.**

## SCOPE (write)

`agents/tasks/LJ-1-358/` only.

## RETURN

**Lead with ONE line: what enforces DD18 AS WRITTEN, and whether that is
anything at all.** Then design B, the rule change, priced per brief in lines
and minutes. Then each signal you keep, with its paste-cost, its per-dispatch
cost and its false negatives. Then what you dropped and why. Then whether the
core idea itself survives your test. **Mark every negative MEASURED or
INFERRED.**
