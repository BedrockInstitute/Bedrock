# LJ-1.750 return: prʟ-numeral-in-Lset-lim, the tag-atom leaf

**Disposition: GO.** The obligation `prʟ-numeral-in-Lset-lim` is inhabited at
`agents/tasks/LJ-1-750/Probe750.agda:62-70`. The file typechecks at the pane
caliber with rc 0 (runs/green-1.out, runs/green-2.out; 1.18 s both,
runs/green-1.time, runs/green-2.time). `table-sat` and `Sat-in-carrier-lim`
are not inhabited; both names occur in the file only once, in the header
comment at Probe750.agda:22 that records their absence. Nothing landed in
`src/`. No `review-of-prʟ-numeral-in-Lset-lim.md` is written, because there
is no NO-GO to state.

## What the obligation is

The brief names one term in `agents/tasks/LJ-1-750/Probe750.agda`:

    prʟ-numeral-in-Lset-lim :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        → ⟨ ω ∈ˢ γ ⟩
        (k : ℕ) (a : S)
        → ⟨ fst a ∈ˢ Lset γ ⟩
        → ⟨ fst (prʟ (numeralL k) a) ∈ˢ Lset γ ⟩

`S` is `𝒮ʟ`'s carrier (`src/L/Constructible.lagda.md:420`, as 749's report
records), `numeralL : ℕ → S` (`src/L/Axioms/Numerals.lagda.md:175`), and
`prʟ : S → S → S` (`src/L/Coding/Model.lagda.md:326`). This is W3's
composition term, not a second numeral bound: 747's uniform numeral leaf
supplies `fst (numeralL k) ∈ˢ Lset γ`, 749's L-pair law lifts any two stage
members' pair into the code presentation, and the obligation is their
application at first argument `numeralL k`.

## Which predecessor type the file took

The brief's premise 3 says to take `prʟ-in-Lset-lim` as a TYPE if
`[LJ-1.749]` has no report yet. **749's report exists in the tree**
(`agents/tasks/LJ-1-749/lj-1.749-report.md`, disposition GO, obligation
inhabited at `agents/tasks/LJ-1-749/Probe749.agda:57-64`), so per the coder
clause ("a module hypothesis taken from a predecessor is the type that
predecessor delivered") this file took the delivered type from the probe
that typechecked and the verdict from the report. 747's report is likewise
GO at `agents/tasks/LJ-1-747/Probe747.agda:111`. Both premises held; nothing
named the statement FALSE; no stop.

## What was built

`agents/tasks/LJ-1-750/Probe750.agda`, 70 lines, ONE section.

- The module header takes the `(ℓ lem)` telescope the predecessor probes
  take, because the obligation's `closedω` home module reads `lem`
  (Probe750.agda:31).
- BOTH leaves are IMPORTED, not transcribed:
  `LJ-1-747.Probe747` for `numeralL-in-carrier-lim` (Probe750.agda:43) and
  `LJ-1-749.Probe749` for `prʟ-in-Lset-lim` (Probe750.agda:44).
  `bedrock.agda-lib` carries `agents/tasks` as an include root, the route
  749's report measured. The transitive tree behind the imports is 747's
  Bound instantiation plus 749's import of 748's transcription; none of it
  reopens here.
- The `S` handling is 749's, verbatim in shape: the V `hPropStructure` open
  supplies `∈ˢ` at V and hides its own `S`; the L open supplies the carrier
  (Probe750.agda:49-50).
- THE OBLIGATION (Probe750.agda:62-70) is a three-line body:

      prʟ-numeral-in-Lset-lim γ oγ clγ ω∈γ k a ha =
        prʟ-in-Lset-lim γ oγ clγ (numeralL k) a
          (numeralL-in-carrier-lim γ oγ clγ ω∈γ k) ha

  749's leaf at `a := numeralL k`, `b := a`; its first membership argument
  is 747's leaf at `k`. Nothing else enters.

## Deviations

1. **THE BRIEF'S STATEMENT TEXT DOES NOT PARSE, and the repair is one
   arrow per premise.** As written, `→ ⟨ ω ∈ˢ γ ⟩` is followed directly by
   `(k : ℕ) (a : S)` with no arrow; typed binders are not application
   arguments, so Agda dies at a ParseError (`runs/floor-1.out`, line 57,
   0.06 s, nothing elaborated, not a price). The delivered statement keeps
   the brief's argument order and content and writes one anonymous arrow
   per premise, which is the exact shape 747's delivered obligation has
   (`→ ⟨ ω ∈ˢ γ ⟩ → (k : ℕ) → ...`, Probe747.agda:111-115) and 748's
   report quotes for its own leaf. The repair is recorded in the probe at
   Probe750.agda:57-61. The π-type is the brief's own: same seven
   arguments, same order, same hypotheses.
2. **The `ω` scope gap, 747's measured discovery, recurred and was re-paid
   here.** The obligation's own `⟨ ω ∈ˢ γ ⟩` puts a bare `ω` in the file's
   scope (`runs/floor-2.out`, NotInScope, 1.48 s, not a price). The cure is
   747's, trimmed to what this file's rows use: `open InfinitySet using
   ( ω )` (Probe750.agda:36-38) without 747's `sucV`, which no row here
   mentions.
3. **The W3 probe and the obligation are ONE file.** The brief prices the
   widest unmeasured term, whether 747's leaf and the L-pair law compose,
   at 20 to 80 lines; the whole probe is 70 lines and the obligation IS the
   W3 term, so no separate miniature was written. The measurement is in the
   next section.
4. **Interpreter path.** This worktree carries no `.venv/`. The survey
   check ran with the main checkout's pinned interpreter,
   `/Users/alsg/Agentic/Bedrock/.venv/bin/python`, against this worktree's
   `scripts/pod/check-survey-quotes.py`. No dependency was added or
   installed. Same deviation as 748's report, deviation 4, and 749's,
   deviation 3.

## Measurements

All runs at the wide caliber `-A64m -I0 -M2g`, set on the pane by the
program, never set by this agent. One Agda process at a time.

| run | rc | real | file |
|---|---|---|---|
| floor-1 | 42, ParseError, the brief's statement text | 0.06 s | runs/floor-1.time |
| floor-2 | 42, NotInScope `ω`, expected scope discovery | 1.48 s | runs/floor-2.time |
| floor-3 | 42, the one floor hole is the only diagnostic | 1.21 s | runs/floor-3.time |
| green-1 | 0 | 1.18 s | runs/green-1.time |
| green-2 | 0 | 1.18 s | runs/green-2.time |

floor-2 ran the transitive tree cold (747, 749, and 749's import of 748 all
rechecked); floor-3 and the greens ran with interfaces cached. THE FLOOR is
floor-3 at 1.21 s: header, both leaf imports, the `S` opens, and the
obligation statement. THE PRICE is 1.18 s. The composition body costs
NOTHING over the frame (the green is inside the floor's run-to-run noise),
which is the expected shape for a term that is one application of two
already-checked leaves. The term is frame-dominated. No heap wall, no
timeout, no restructuring.

**W3, measured: the two leaves compose by direct application.** No adapter
term, no extra transport, and no conversion problem of their own: 747's
leaf returns exactly the type `prʟ-in-Lset-lim`'s first membership argument
demands, syntactically. The one caveat 749's report hands forward still
holds and now sits in this leaf's normal form: the conclusion's membership
is STUCK (one `subst` along `sym (prʟ-fst ...)` inside 749's body), so a
consumer that needs `fst (prʟ (numeralL k) a) ∈ˢ Lset γ` to compute
further, for example inside another conversion, faces that stuck term.
Each new projection law stacked on top adds one more such layer.

## What the next brief needs

- **Supply is now 1 for the tag-atom leaf.** Cite
  `agents/tasks/LJ-1-750/Probe750.agda:62`. 737's debt (i), which 747's
  report named as consuming the numeral leaf, now has its composition with
  the L-pair law named and green: the tag-atom shape, a numeral paired
  with a stage member, is a delivered top-level term.
- **The composition recipe, measured:** import both leaves
  (Probe750.agda:43-44) and apply 749's at `numeralL k` with 747's leaf as
  the first membership argument (Probe750.agda:68-70). Nothing else
  enters. Any successor that pairs numerals with OTHER stage members
  (singletons, tagged pairs) should try this route before writing
  anything.
- **The brief-builder should write obligation statements in parseable
  Agda.** One arrow per premise, as 747's, 748's and 749's briefs did.
  This brief's text cost one dispatch run to discover (floor-1, 0.06 s,
  cheap but avoidable).
- **Prices to plan with:** floor 1.21 s, green 1.18 s at wide caliber,
  cold tree behind the imports about 1.5 s (floor-2). Adding a third leaf
  import of this size costs its own interface load at the next cold run.
- **The stuck-subst caveat above** is the price a `succʟ`-or-higher
  presentation brief should read before it stacks transports.

## Stops

None. The obligation was supported, the premises held, the predecessor
reports were GO, and the term typechecked under the delivered telescope
after the one syntax repair, which changed no content.

## Check survey quotes

Output of the mandated check, run as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-750`
against the finished return:

    check-survey-quotes: LJ-1-750 clean (0 note(s), 0 defect(s))

    rc=0

`scripts/gate/lint-agda.py --check agents/tasks/LJ-1-750/Probe750.agda`
also ran, rc 0.

## ARCHIVE USED

Corpus search named five CANDIDATEs. One was read; it is the row that
runs this block.

- `archive/dev/DD-archived.md:30`: "| DD18 | **THE ARCHIVE AND LITERATURE
  SURVEYS are sections of the brief and of the return, not a hope.**".
  READ. This row is the mechanism the ARCHIVE USED and LITERATURE USED
  blocks run under, and its amendment history is why the quotes above
  name a line each.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch wiring and
  slot orchestration are the program's business; this return writes one
  probe and its report.
- `archive/dev/PLAN-archived.md`: declined, not read. The disposition
  follows the brief's own branch table, not a retired plan.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  evidence this return builds on is cited at `file:line` from the live
  tree: the 747, 748 and 749 probes and reports.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing
  status is `dev/pod/screen.toml`, and no standing figure is quoted here.

## LITERATURE USED

Corpus search named five CANDIDATEs. None was read; the obligation is a
one-application composition of two proved probe leaves, so no source,
terminology or attribution question arises.

- `dev/literature/glossary-review-2026-08.md`: declined, not surveyed. The
  return adds no term and proposes no glossary entry.
- `dev/literature/devlin-errata.md`: declined, not read. The mathematical
  content came from the tree (`src/L/Coding/Model.lagda.md:326`,
  `src/L/Axioms/Numerals.lagda.md:175`) and from the two predecessor
  probes, not from a source digest.
- `dev/literature/primary-sources.md`: declined, not read. No fetch or
  provenance decision is open in a code-only probe.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. The
  obligation quantifies over `k : ℕ` and `a : S` and names no level
  formula and no slot arithmetic.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. The probe cites no
  literature and the report cites no source beyond the tree.
