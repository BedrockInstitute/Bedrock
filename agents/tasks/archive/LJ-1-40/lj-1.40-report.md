# LJ-1.40 report: the condensation rows, re-indexed and consumed

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100.

## 1. THE VERDICT

**REPAIRED, WITH THE AGREEMENT PARTIALLY CLOSED.** The rows are
re-indexed, the defective shapes and leaves are corrected, and the
master is green. The agreement is closed for the Bot row and for the
shared machinery. The remaining eleven rows' agreements are not closed;
the report says exactly what each owes. The first consumer audit is
done and its findings landed: the audit found defects the review's
index arithmetic missed, and the repair consumed those findings.

## 2. DID THE AGREEMENT CLOSE?

**NO, NOT FOR ALL ROWS.** The Bot row is closed in both directions:
`BotAgree.bot-out` and `BotAgree.bot-in`
(`src/L/Condensation.lagda.md:2610-2638`). The shared machinery is
closed and machine-checked: the extension-frame transfer
(`extAtB→extAt`, `extAt→extAtB`, `:2398-2416`), the unary and binary
shape transfers (`UnaryShape`, `BinaryShape`, `:2418-2608`), the empty
operation transfer (`:2597-2606`), the environment-condition transfer
at the atom layout (`EnvB2T`, `:2645-2682`) and the term-value transfer
(`TmVal`, `:2684-2776`).

The eleven remaining rows each need the same assembly: their leaf
transfers (the operations `sameAt`/`diffAt`/`interAt`/`unionAt`/`implAt`
against the bounded operations, the atom body, the quantifier bodies,
the bounded-quantifier bodies and the proposition body) and their frame
assemblies at the class carrier. The pattern is the Bot row's. The
environment transfer exists for the atom layout only; the other three
frame layouts need their own instances of the same transfer.

## 3. ARE THE ROWS TRUE NOW?

**THE MACHINE-CHECKED EVIDENCE IS THE CLOSED AGREEMENT.** The Bot row
is true of the machine's table: its two directions close only if the
row means what the machine's row means. The shared transfers close only
if the shapes, the environment condition and the term value mean what
the machine's mean. They close, so those pieces are true.

What would be false if a row were still wrong: the Bot row's closed
theorem would fail to typecheck. That is the C-35 test, and it is why
the audit found the defects it found: the two shapes read the arity
where the code should be read (`arTagB`, `arTagPairB`), the binary
shape forced the recorded value to equal the payload pair, the term
value read the environment at the tag position instead of the key, and
the environment condition read the ambient set where it should read the
member. Each was corrected before the corresponding transfer closed.

The eleven unclosed rows are not yet audited. They are re-indexed and
their certificates check, but the agreement does not consume them yet.

## 4. HOW MANY ROWS NEEDED AN INDIVIDUAL FIX BEYOND THE FRAME CHANGE?

**TWO OF THE TWELVE ROWS, PLUS BLOCK 1'S CLAUSE.** The frame change
removed the final binder from the four frames that carried it. Nine of
the eleven block-2 rows were pure mechanical re-indexing after that
change: Bot, Top, Neg, And, Or, Imp, Mem, Eq, AllIn, ExIn. Forall
needed one individual slot fix (the extended environment read `E`
instead of the subvalue `ya`). Exist needed the `extAtB` wrap. Block
1's `Clause` needed the same wrap.

The honest DD4 measure is the other way too: every row depended on
shared definitions that the audit found wrong. The two shapes and their
numeral twins, the term value and the environment condition were shared
and defective. The original design looked shared; the audit shows the
shared layer carried most of the defect.

## 5. DID THE SURVIVING 1,021 LINES REALLY SURVIVE?

**PARTLY.** The description region (`:1401-2251` of the old file) and
block 3 (`:2252-end`) survive. The bounded atoms did not survive
intact, against the review's estimate. Four definitions were re-laid:
`arTagB` (`:424`), `arTagPairB` (`:439`), `arTagBnum` (`:1468`) and
`arTagPairBnum` (`:1449`), with their Delta-0 witnesses re-verified.
`tmValB` (`:485`) and `envBndGen` (`:504`) were corrected too. The
review's "surviving" list was based on index arithmetic that did not
machine-check these; the first consumer audit is what found them.

## 6. THE NUMBER

2,141 in-fence non-blank lines before the repair (the review's figure,
including the uncommitted block 3), and 2,498 after. The difference is
the agreement machinery (the shapes' corrections and the closed
transfers), measured at the ledger's caliber.

## 7. SECONDS AND RATE

Cold runs, one process each, at `GHCRTS="-A64m -I0 -M8g"`, the
master's own interface moved aside, dependencies warm:

| run | user s | wall s |
|---|---:|---:|
| 1 | 13.35 | 13.87 |

The rate is 13.35 / 2,498 = **0.00534 seconds per line**, against
DD24's bar of 0.013193. The cone, measured with the imports-only
control `src/ProbeLJ140Ctrl.agda` in the same session, is 1.25 seconds
of user time. The net content cost is about 12.1 seconds over the
2,498 lines, which is 0.00484 seconds per line.

C-31 framing: the GCH side's whole budget is 99.6 to 147.7 seconds
(`dev/ledger.toml:305`). This master's whole measured cost is about
13.4 seconds, about 10 percent of the budget's low end.

## 8. DID YOU NEED A PLACEMENT ANYWHERE?

**NO.** No `absFo`, no `placeFo`, no constant vector and no appended
environment appear anywhere in the repair or the agreement. Every
certificate is stated on the unplaced formula. P-u holds.

## 9. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C (`:209-256`, summary `:299-302`).
Took the requirement: bind every Def-step quantifier by the concrete
set K(u) inside the matrix.

The extension-candidate question: **Devlin's bounded matrix does not
have the machine's extension-candidate structure.** His D(v, u) is an
equality: v is the set of definable subsets of u, with every quantifier
bounded by K(u) inside the matrix. The two directions of the equality
are present, which is the part the story's rows got wrong when they
replaced the two-way frame with a one-way universal over the value.
But his matrix evaluates formulas through the satisfaction predicate
over finite sequences; it has no candidate environment pushed on the
front, because there is no table. The machine's `extAt` candidate
structure is the coding of the table, and the K(u) bound appears in the
project as the K slot bounding the second direction of `extAtB`. The
story's defect was writing only one direction and bounding it by the
value itself instead of by K.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
verified it does not cover Chapter II section 5, and the brief rules
out re-checking it.

## 10. ARCHIVE USED

`_build/lj-1.38-review.md`, whole. Took the defect analysis, the scope
table (`:6.1-6.3`) and the dead-cure finding (`:3`). The review's
per-row claims beyond the Mem row were index arithmetic, not
machine-checked; the audit confirmed its Mem finding and found more.

`src/ProbeDD25E1.agda`, whole. Took the vacuity countermodel and the
`story-forces-all` collapse.

`src/ProbeDD25E2.agda`, whole. Took the frame transfer
`extAtB→extAt`, now delivered at the master (`:2398-2403`).

`src/ProbeDD25E3.agda`, whole. Took the control: the corrected atom
index is the one the collapse fails against.

`_build/lj-1.38-report.md`, whole. Took the per-row deviation table
(`:2`) and the refusal. The report's claim that the machine reads the
value slot is false; the review's correction is right.

`src/L/Condensation.lagda.md`, whole. The file under repair.

`src/L/Coding/Model.lagda.md`, whole. The machine, which is correct.
The slot definitions at `:1746-1751`, the atom body at `:1753-1759`,
the frame at `:897-1023`, the rows at `:1117-1990`, the shapes at
`:730-784`, the environment condition at `:210-300, :483-530` and the
term value at `:1686-1738`.

`_build/lj-1.37-report.md`, whole. Took the delivered figures and the
wrong premise about the machine (`:12-18`).

`dev/LESSONS.md`, the sections the build rules name. C-35 (`:3094`)
is the audit's law: the first consumer found the block defective.
P-l, P-m, P-n, P-t, P-u, P-v, P-h, R-35, R-38, R-40, I-5, C-12, C-22,
C-31, C-32, C-33, C-34 and D-10 were read through
`scripts/rules.py --for build`. P-v decided the spelling: the rows are
restatements of the machine, and the agreement states them at the
satisfaction level in the machine's vocabulary. P-u held: no placement.

`src/ProbeLJ140A.agda`, written and thrown away per D-1. The
prototype of the agreement machinery, green against the master.
`src/ProbeLJ140Ctrl.agda`, the cone control for this session.

## 11. WHAT I AM NOT SURE OF

1. The eleven unclosed rows. Each needs the leaf transfer and the
   frame assembly named in section 2. The machinery for the shapes,
   the environment condition and the term value is delivered and
   green; the per-row work is mechanical but real.
2. The environment condition's other three frame layouts. The
   atom-layout transfer (`EnvB2T`) is machine-checked; the unary,
   constant and binary-with-ya layouts instantiate the same condition
   at different slots and were not re-verified after the `envBndGen`
   correction.
3. The description's shapes beyond the numeral-tag twins. `arTagBnum`
   and `arTagPairBnum` had the same off-by-one and were corrected;
   the description's other shape formulas were not machine-checked
   against the machine's readings, because the description's adequacy
   is a later block.
4. The seconds are one cold run, flat against the session's earlier
   runs (12.10, 12.07 before the final additions; 13.35 after). The
   additions' marginal cost is about 1.2 seconds.
5. The site-fact bundle. Each row's agreement carries the site facts
   as hypotheses (the tag columns, the codes in K, the values in K,
   K's transitivity, the ambient environment set). Whether each fact
   is provable at the class carrier is the next block's work; the
   agreement treats them as the substrate, exactly as the probes did.
