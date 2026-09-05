# LJ-1.136: gate the remaining A-prime blocks

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Measure the five unmeasured blocks of Route A-prime, so that none of them is
funded on a band centre.** You gate. **You do NOT build.**

## THE RULING THAT SENT YOU

The owner ruled: **「GCH 侧，按你的 A' 继续」.** Route A-prime is chosen.
`[LJ-1.131]` split it into seven blocks and `[LJ-1.134]` gated the widest.
**The route is settled. The prices are not.**

## THE STATE, and I verified each line myself

`agents/reports/lj-1.131-report.md:367-373` holds the seven blocks:

| block | band | basis, in LJ-1.131's own words | state |
|---|---|---|---|
| A1 `⟨ isL x ⟩` replaces "assume V = L" | 30 to 60 | `src/L/Choice/Stage.lagda.md:294` delivers the bounding ordinal | **UNGATED** |
| A2 an injection as an ELEMENT of L, read back as a function | 120 to 220 | **INFERRED band**, marked the widest unmeasured term | **GATED GO**, 207 lines |
| A3 the `<_L`-least injection by `leastOf` over `orderAt` | 40 to 80 | three delivered instances of the pattern | **has a comparable, not a measurement** |
| A4 internal least cardinal and internal `IsCardinal` | 90 to 170 | `[LJ-1.107]` measured the AMBIENT `LeastCard` at 38 lines | **UNGATED** |
| A5 the square-law chain over L-injections | 300 to 450 | `[LJ-1.107]` MEASURED 582 ambient lines, 455 unconditional | **UNGATED, and the largest** |
| A6 `absorbs` as a theorem | 100 to 180 | `[LJ-1.107]` measured successor absorption at 103 lines | **UNGATED** |
| A7 the internal GCH statement | 80 to 160 | `ChoiceStatement` is 13 in-fence lines | **UNGATED** |

**Total band 760 to 1,320.**

## WHAT `[LJ-1.134]` FOUND, and it changes every remaining block

Read `agents/reports/lj-1.134-report.md` WHOLE before anything else.

**It is GO.** The fibre extraction, the composite with `leastOf (orderAt β)`,
a non-degenerate concrete graph and the injection the square-law chain
consumes all elaborate. `src/ProbeLJ1134A.agda`, 207 lines, `--safe`, exit 0.

**But it corrected `[LJ-1.131]` on a carrier crossing, and I verified both
lines:**

- `src/L/Choice/Step.lagda.md:78` opens `hPropStructure 𝒮ᵥ`, the **AMBIENT**
  structure. `orderAt` at `:740` therefore orders ambient sets.
- `src/L/Coding/Model.lagda.md:70` opens `hPropStructure 𝒮ʟ using ( S )`, the
  **L** carrier.

**So A-prime does not merely instantiate the order stack's generic code. It
crosses a carrier boundary at every use of `orderAt`.** `[LJ-1.134]` priced
the crossing at 22 lines, **but per use.**

**This is the thing to price across A3, A4, A5 and A6.** If the crossing is
paid once and shared, it is 22 lines. If it is paid at each site, it multiplies
by the number of sites. **Nobody has counted the sites.** That is your first
number.

## WHAT TO DO, and the order matters

1. **Read `[LJ-1.134]`, then `[LJ-1.131]`, then `[LJ-1.107]`.** `[LJ-1.107]`
   is the source of three of the five remaining bases and you must read what it
   actually measured, not what the table says about it.
2. **Count the carrier-crossing sites.** MEASURED, by grep, with the count and
   the file list.
3. **Decide which blocks need a probe and which do not.** **Not every block
   needs one.** A block whose price rests on a delivered comparable IN THIS
   TREE, at a site you can read, may be gated by reading. **Say which method
   you used for each, and why.**
4. **Probe the ones that need it.** **A5 is the largest and its basis is a
   restatement claim: 「the restatement rewrites types, not proofs」. That claim
   is INFERRED and it carries 300 to 450 lines. If one probe is affordable,
   it is that one.**
5. **Re-price every block**, one best-effort figure each, naming its basis
   (DD8). **Where your figure differs from `[LJ-1.131]`'s band, say so plainly
   and say why.**
6. **Give the build order**, with the dependency between blocks, and say which
   block must be built first for the others to be checkable.

## THE PATTERN THIS SESSION MEASURED, and it should shape your scepticism

**Three inherited figures came in LOW this session and one came in HIGH.**
`[LJ-1.128]` proved an identical tree cost 11.2 percent more on the same
machine on a different day. P-l: a price from a comparable elsewhere is a
hypothesis, and it must be re-measured at its own site.

**A5's basis is the strongest comparable of the five and also the weakest
argument**, because 582 delivered ambient lines tell you what the AMBIENT
proof cost, not what the restatement costs.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Here it is concrete and it is the carrier crossing.** If the crossing is
written once, generic in the structure, both the AC side and the GCH side use
one copy. **If your gating finds that a block can be written generic over the
carrier at little extra cost, that is a DD4 finding and it belongs at the top
of your return.**

## THE ABORT CRITERION

- **Every block has a price and a basis**: report the table and STOP.
- **A block turns out to be impossible or far more expensive than its band**:
  **STOP AND SAY SO.** That is the most valuable return available to you. A
  refutation has given this project its best results.
- **The carrier crossing turns out to be per-site and expensive**: that alone
  re-prices A-prime. Report it and stop.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do NOT build a block.** This is a gate. **A probe is thrown away.**
- **Do not edit any master.** Probes are `src/ProbeLJ1136*.agda`, never
  `.lagda.md`.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.
- **Do not raise the heap cap.** C-12: `GHCRTS="-A64m -I0 -M8g"`, **ONE agda
  process**. A sibling agent is measuring build times, so **the machine is NOT
  quiet and your seconds are upper bounds. Say so beside every figure.**
- **Do not price by analogy.** P-l.

## THE MACHINE, and a HARD ORDERING CONSTRAINT

Load average at dispatch: **9.27 / 7.67 / 12.81**. A trading application takes
about 58 percent across two helpers, and `[LJ-1.134]` saw three runaway
`siriactionsd` processes earlier today. **Measure the load yourself and report
it beside every absolute figure.**

**`[LJ-1.135]` is running RIGHT NOW and it is measuring BUILD TIMES.** C-12:
a task that measures check time gets a quiet machine. **Your Agda process
would corrupt its figures, and its builds would corrupt your seconds.**

**Therefore: do ALL the reading, the grep and the site counting FIRST, and
write them into your report. Do NOT start Agda until I message you that the
sibling has finished.** If you reach the point where only Agda is left,
**write the report up to that point and say you are waiting.** I will send you
the word.

**This is not a suggestion. Two measuring processes at once destroy both
measurements, and this project has paid for that once already.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** A negative that rests on an
inference sets no verdict.

## ARCHIVE (DD18)

- **`agents/reports/lj-1.134-report.md`**, read WHOLE. The GO and the carrier
  crossing.
- **`agents/reports/lj-1.131-report.md`**, read WHOLE, especially `:367-373`.
- **`agents/reports/lj-1.107-report.md`**, read WHOLE. **Three bases come from
  it and I want them checked, not quoted.**
- `agents/reports/lj-1.129-report.md`: why the route changed at all.
- `agents/reports/lj-1.111-report.md`, `lj-1.114-report.md`: the truncation
  wall, which A5 must not walk back into.
- `dev/LESSONS.md` **P-l, P-x, D-8, D-30, C-36, C-38 as extended**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md` for 5.5 and 1.1(vii), **and
`dev/literature/devlin-errata.md`, which `[LJ-1.131]` marked as its own gap:
it did not read the errata.** Say whether the errata touch anything A-prime
rests on. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/reports/lj-1.134-report.md` FIRST, then `lj-1.131-report.md:367-373`,
then `src/L/Choice/Step.lagda.md`, `src/L/Coding/Model.lagda.md`,
`src/L/Ordinal/SquareLaw.lagda.md`, `src/L/StageCardinal.lagda.md`.

## SCOPE (write)

`src/ProbeLJ1136*.agda` only. Your report is
`agents/reports/lj-1.136-report.md`. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for recon`, and
read every statement.

- **D-8.** Gate a block before you fund it. **This brief IS the gate.**
- **D-1.** A probe prices THIS setting and is thrown away. **A probe is
  `.agda`, never `.lagda.md`, and it is never committed.**
- **P-l, P-x, P-w.**
- **D-30.** Price what the CONSUMER needs: `L ⊨ GCH` stated in L.
- **C-36.** Write the term you could not write.
- **C-12, C-22, C-35, C-38 as extended, C-39, C-40, D-10, D-26, D-29.**
- **C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`. A size figure counts
  non-blank lines inside ` ```agda ` fences.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the re-priced table: seven blocks, one figure each, the basis, and
the method you used to gate it.** Then the carrier-crossing site count and
what it costs. Then the build order with dependencies. Then any block whose
price moved, and why. Then the DD4 answer. **Mark every negative MEASURED or
INFERRED.**
