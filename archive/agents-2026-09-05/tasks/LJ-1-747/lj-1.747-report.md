# LJ-1.747 return: numeralL-in-carrier-lim, the uniform numeral leaf at a closed limit

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: GO.** The obligation is inhabited at
`agents/tasks/LJ-1-747/Probe747.agda:111`, the file typechecks at the
pane caliber (`runs/green-1.out`, rc 0, 2.14 s, no warnings), and
`table-sat` and `Sat-in-carrier-lim` stay absent as the brief demands.
The brief's W3 question, whether `Bound.num∈λ` converts at `lam := γ`,
has the answer YES.

## What the obligation is

The brief names one term in `agents/tasks/LJ-1-747/Probe747.agda`:

    numeralL-in-carrier-lim :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        → ⟨ ω ∈ˢ γ ⟩
        → (k : ℕ)
        → ⟨ fst (numeralL k) ∈ˢ Lset γ ⟩

Body: `Bound.num∈λ` (`src/L/Coding/Bound.lagda.md:139`,
`num∈λ : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩`) instantiated at
`lam := γ`, so the delivered term is one module application plus one
line (`Probe747.agda:116`). `table-sat` and `Sat-in-carrier-lim` are NOT
inhabited (premise 5; the brief forbids both, and 737 left `table-sat`
absent). Nothing lands in `src/`.

## Shape kept, shape changed

- KEPT: the 737-SPLIT closer legs `no-succ` and `suc∈γ`, verbatim from
  `agents/tasks/LJ-1-737-SPLIT/Probe737Split.agda:108-127`; the
  delivered term stands on them (`suc∈γ` is the `succλ` the bound
  takes, premise 3).
- TRIMMED: the closer's `hγ : ⟨ isL γ ⟩` argument. The obligation's
  telescope does not carry it, and neither clause ever reads it: their
  bodies mention only `oγ`, `clγ`, `mem-ord`, `+ω-mem`, `suc∈or≡`,
  `∈-irrefl` and `∈sucV-elim`. The trimmed module sits at
  `Probe747.agda:65` with the source's bodies token for token.
- ADDED: the `∅∈λ` leg the bound also takes. It is the brief's
  `∅ ∈ ω ∈ γ` in one line (`Probe747.agda:101`):
  `oγ .fst (#∈ω zero) ω∈γ`, that is, `#∈ω : (k : ℕ) → ⟨ (# k) ∈ˢ ω ⟩`
  (`src/L/Ordinal.lagda.md:248`) with `# zero` reducing to `∅`,
  carried down to `γ` by the transitivity half of `oγ` along `ω ∈ γ`.
- **ONE DEVIATION, measured:** the closer is TRANSCRIBED with the
  trimmed telescope, not imported from `LJ-1-737-SPLIT.Probe737Split`.
  An import cannot supply this obligation: the source `Closer` demands
  `hγ : ⟨ isL γ ⟩` (`Probe737Split.agda:105`) and the obligation has no
  such argument. `isL γ` is derivable from `IsOrd γ` through
  `Lset→isL` (`src/L/Constructible.lagda.md:405`) and
  `ord∈Lset-suc` (`src/L/Ordinal/Stages.lagda.md:434`), so the import
  route is not impossible, but it buys a dead argument plus that whole
  probe's frame in every recheck of this one. The same trade
  Probe737Split itself records as its ONE DEVIATION. W2 note: the
  closer is now written twice in the tree, once with `hγ` and once
  without; the canonical home stays the 737-SPLIT probe, and a later
  chapter-sized closer should absorb both shapes. No deadline forced
  this form; the telescope did.
- SCOPE DISCOVERY, one import the brief could not name: the
  obligation's `⟨ ω ∈ˢ γ ⟩` puts a bare `ω` in the file's scope, and
  737-SPLIT never mentions `ω`, so its import list does not carry it.
  The fix is `open InfinitySet using ( sucV; ω )` (`Probe747.agda:49`).

## A premise gap, recorded

Premise 1 cites `agents/tasks/LJ-1-737/lj-1.737-report.md:103`, and
that file does not exist in the tree: this worktree carries
`agents/tasks/LJ-1-737-SPLIT/` only, and `git log --all` on
`agents/tasks/LJ-1-737/` returns nothing, so the 737 report was never
committed. The gap does not block the obligation: premises 2 to 5 carry
the proof, and all four are verified above at `file:line`. Debt (i)'s
provenance survives in this brief's own text. If the mathematician
wants the 737 report citable again, it needs a re-commit from wherever
it survives; this return cannot rebuild it.

## What the next brief needs

- Supply 1 at the meter's name: later briefs may cite
  `Probe747.agda:111` as the uniform numeral leaf instead of
  re-deriving it, and may cite the trimmed closer at
  `Probe747.agda:65` when their telescope has no `isL γ`.
- The instantiation recipe, measured: `succλ := suc∈γ` (trimmed),
  `∅∈λ := oγ .fst (#∈ω zero) ω∈γ`, module application at
  `Probe747.agda:103`. Nothing else enters.
- The floor and the price sit 0.3 s apart (1.83 s against 2.14 s): the
  frame IS the cost, the leaf is free. There is no heap wall, no
  timeout, and no import left to trim.
- EXIT-CODE HAZARD for the branch table: Agda 2.8.0 exits 42, not 1,
  on a scope error (`runs/floor-1.out`, NotInScope on `ω`). Rows keyed
  on `exit_code = 42` (`no-go-attacked`, `no-go-stated`,
  `no-go-bare`) cannot tell a NO-GO from a lint-class defect on the
  exit code alone; this report is the disambiguator, and it names the
  GO.

## W3 answer

The brief's W3: whether Bound's `num∈λ` converts at `lam := γ` under
closedω and `ω ∈ γ` (estimated 20 to 80 lines). IT CONVERTS. The proof
proper is about 10 lines (the `∅∈λ` leg, the module application, and
the one-line body at `Probe747.agda:116`); the file is 116 lines
because the closer transcription and its header comments ride along,
which the estimate did not count. No binder resisted. The one
telescope surprise was scope, not typing: the `ω` in the obligation's
own hypothesis needed its InfinitySet open, and that cost the one
failed run of the dispatch.

## Runs (wide caliber, pane GHCRTS untouched, one Agda process per run,
/usr/bin/time -p, src/ chain warmed by the first run)

- `runs/floor-1.out`: first shape, `ω` missing from scope, rc 42,
  2.43 s. NOT a price; it is the cold-chain warm-up record, and the
  whole src/ cone of `L.Coding.Bound` checks in under 2.5 s cold on
  this box, so there is no watchdog exposure.
- `runs/floor-2.out`: floor, Sections 0-1 without the obligation
  block, rc 0, 1.83 s. THE FLOOR.
- `runs/green-1.out`: FULL file, rc 0, 2.14 s, no warnings. THE PRICE.
- `runs/green-2.out`: re-certification of the full file, rc 0, 2.33 s.

## Mandated paste

    $ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-747
    check-survey-quotes: LJ-1-747 clean (0 note(s), 0 defect(s))

    (The interpreter is the main tree's .venv; the worktree carries none.
    lint-agda.py --check also ran, rc 0.)

## ARCHIVE USED

- `archive/dev/DD-archived.md:30`: "**A return carries an ARCHIVE USED
  section** naming what it actually read and what it took from each item,
  at `file:line`." READ. This row is the mechanism this block runs under.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch wiring and
  slot orchestration are the program's business; this return writes one
  probe and its report.
- `archive/dev/PLAN-archived.md`: declined, not read. The disposition
  follows the brief's own branch table, not the archived plan.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing
  status is `dev/pod/screen.toml`, and no standing figure is quoted here.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  evidence this return builds on is cited at `file:line` from the live
  tree: `src/L/Coding/Bound.lagda.md` and the 737-SPLIT probe and report.

## LITERATURE USED

- `dev/literature/devlin-errata.md:98`: "- Bounding quantifiers (10.6,
  p. 60): the proposed bounding class for the". SCANNED for an entry
  touching the numerals-as-formula-set route that `Bound.num∈λ` encodes
  (`src/L/Coding/Bound.lagda.md:59`, Devlin's `𝓕 ∪ {vᵢ}`): the errata
  around bounding classes concern the §10.6 bounding class and Δ0
  domains, not the numeral leaf; nothing here bears on the
  instantiation.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. This
  return introduces no term and proposes no glossary entry.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. No
  level-formula slot is touched; the obligation quantifies over
  `k : ℕ` and never names a formula.
- `dev/literature/primary-sources.md`: declined, not read. The primary
  fact this return needs is already formal and green in
  `src/L/Coding/Bound.lagda.md`; no fetch decision is open.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No source is
  fetched or consumed by this task.
