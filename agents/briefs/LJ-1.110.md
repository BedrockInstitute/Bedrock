# LJ-1.110: restate the three split frames, and make the tree green again

tier: codex (default)

## GOAL

**The tree is RED and I put it there.** The row repair changed every row
telescope; the three split masters instantiate those rows and now fail.
**Restate their frames to match, in tied form, and make them green.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`3f8301f`. **`src/L/Condensation.lagda.md` is GREEN. The three masters under
`src/L/Condensation/` are RED, exit 42, all three, and I measured that
myself.** A sibling agent works on the cardinal side and will not touch
these files.

## WHAT BROKE, and why it is the owed repair rather than a regression

`[LJ-1.105]`, `[LJ-1.108]` and `[LJ-1.109]` repaired every row in
`src/L/Condensation.lagda.md`:

- **`EnvSet` carries `arityK`, `E ∈ K` and `ar ∈ K`** and derives the
  `entryK` and `arSubK` ties inside itself.
- **Every row telescope lost `entryK`, `arSubK` and `tmKeyK`** and gained
  `arityK`.
- **The five key facts are stated only in tied form**, each carrying the
  site's membership premises.

**The three split masters still pass the OLD arguments.** `LowerAgree`'s
`MemAgree` application still passes `tmKeyK entryK arSubK-mem`, which no
longer exist in that telescope. **That is the error.**

**Every one of those names is REFUTED.** `src/ProbeLJ195A.agda:45-48` and
`src/ProbeLJ197A.agda`. **So the three frames were vacuous before they were
red. Restating them is the repair that was already owed, and it happens to
be the fix.**

## WHAT TO DO

1. **Restate each frame's telescope in tied form**, matching the rows'
   current shapes. **Read the row telescopes in
   `src/L/Condensation.lagda.md` as they stand now; every earlier report's
   line numbers are stale.**
2. **`arityK` replaces the deleted names.** It is a `KFacts` field in its
   exact shape. **`transK` in the existing frames
   (`src/L/Condensation/TwelveAgree.lagda.md:167-169`) already has that
   type: check whether it can simply be reused rather than a new name
   added.**
3. **The successor closure `sucK : (a : S) → a ∈ K → sucV a ∈ K` goes as a
   TELESCOPE FACT of the frame, never as a `KFacts` record field.** **P-x,
   measured one dispatch ago: the field walls the master at the C-12 cap in
   three configurations, and removing two lines returns it to green.**
4. **All three masters GREEN when you finish, or you revert all three and
   say so.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you leave in a frame must be one the CONSUMER can supply.
Name what supplies each, at `file:line`.** `[LJ-1.100]` built the extended
consumer frame and measured 28 of the 39 supplied; **`src/ProbeLJ1100A.agda`
is the record of what the consumer can hold. Use it.**

**Try to refute every hypothesis you write.** `src/ProbeLJ197A.agda` is the
shape. **Eleven refuted hypotheses is what this repair is about. Do not add
a twelfth.**

## THE ABORT CRITERION

- **All three go green**: report the diff, each master's cold seconds, and
  STOP.
- **A frame cannot be restated because a row needs something no frame fact
  supplies**: report it with the term you could not write, **and CONTINUE to
  the next frame. Report the count of frames that failed.**
- **Anything walls**: STOP, report the wall with its seconds. **The three
  measured 20.64, 11.23 and 21.33 s when they were built. If they now wall,
  that is a P-w or P-x finding and it is worth more than the green.**

**Do not stop at the first negative.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time. A sibling agent holds the other slot and I am
running `make check` in the background, so the machine is NOT quiet: say so
beside every figure. If a check does not return, KILL IT before you start
another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any row's or any frame's conclusion.** The frames must
  prove the SAME statements they state today.
- **Do not delete a frame to make the tree green.** Retirement is the
  owner's call and it is not this dispatch's.
- **Do not touch `src/L/Condensation.lagda.md`.** It is green and it is the
  base you build against.
- **Do not touch `src/L/Coding/`, `src/V/` or `src/L/BoundedSubset.lagda.md`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.** **The master
  moved three times today.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**The tied frame should be SMALLER than the old one**: eleven facts became
`arityK` plus `sucK` plus the site memberships the rows already bind.
**Report the frame's fact count before and after. That number is the DD4
answer for this dispatch.**

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
each master's cold seconds and non-blank in-fence lines, before and after,
with the load average.

## ARCHIVE (DD18)

- **`_build/lj-1.109-report.md`**, read WHOLE. **Its section 2 is P-x and it
  decides where `sucK` goes.**
- **`_build/lj-1.108-report.md`**, read WHOLE. **Its section 2 grep says
  exactly which names left the master.**
- `_build/lj-1.105-report.md`, the `EnvSet` shape.
- **`src/ProbeLJ1100A.agda`** and `_build/lj-1.100-report.md`, **the
  extended consumer frame: what the consumer can hold.**
- `src/ProbeLJ199A.agda`, `src/ProbeLJ1104A.agda`, the tied forms.
- `src/ProbeLJ197A.agda`, `src/ProbeLJ195A.agda`, the eleven refutations.
- `_build/lj-1.76-report.md`, which built the three masters and records why
  the split was drawn where it was, and the heap wall that forced it.
- `dev/LESSONS.md` **P-x, C-38 as extended, C-39**, C-35, C-36, D-29, D-30,
  P-i, P-w, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

The current row telescopes in `src/L/Condensation.lagda.md` FIRST, then
`src/L/Condensation/LowerAgree.lagda.md`, then `UpperAgree`, then
`TwelveAgree`.

## SCOPE (write)

`src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md`,
`src/L/Condensation/TwelveAgree.lagda.md` (**all three green at the end, or
all three reverted**) and `src/ProbeLJ1110*.agda`. Your report is
`_build/lj-1.110-report.md`. **Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **P-x.** A transparent construction in a RECORD FIELD type is paid by
  every elaboration of the record. **`sucK` is a telescope fact.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-35, C-36, D-29, D-30, D-10.**
- **P-i.** The conversion-explosion playbook. **Read it whole; heavy
  hypothesis packs go as module Pi-parameters, never as records.**
- **P-w.** A module application COPIES, and the copy is paid at USE.
- **P-h, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives
  them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`. **I am running it.**
- **Run `scripts/check-fences.py --check`** and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.110-report.md` incrementally, skeleton first.

**Lead with how many of the three are green**, with each one's cold seconds
before and after. Then the frame fact count before and after. Then every
hypothesis the restated frames carry, and what supplies each. Then whether
each survived your refutation attempt. Then the C-39 section. **Mark every
negative MEASURED or INFERRED.** Then the DD4 answer.
