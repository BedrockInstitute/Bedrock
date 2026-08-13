# LJ-1.103: restate absorbs-subset, and re-check Devlin55

tier: codex (default)

## STATUS

COMPLETE. The restated hypothesis checks, and `Devlin55` re-checks green
end to end. The brief's obvious candidate (`⟨ ω ∈ˢ α ⟩`) is TOO STRONG:
the consumer site runs at α = ω, where that premise is false. The
narrowest condition the body supplies is `⟨ α ∈ˢ ω ⟩ → Empty.⊥`. The
self-attack found no refutation. The master is green. No commit, no
push. The probe is `src/ProbeLJ1103A.agda`; the report is
`_build/lj-1.103-report.md`.

## 0. THE RESTATED HYPOTHESIS

The master now states (`src/L/BoundedSubset.lagda.md:1364-1366`):

```agda
(absorbs-subset : (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                → (x : S) → (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
                → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
```

The conclusion is unchanged. Only the hypothesis moves: the statement
now requires the premise `α ∉ ω` (`⟨ α ∈ˢ ω ⟩ → Empty.⊥`). The single
application passes the module parameter `α∉ω`
(`src/L/BoundedSubset.lagda.md:1530`).

## 1. THE VERDICT

**`Devlin55` re-checks green end to end with the restated hypothesis.**
The whole master `src/L/BoundedSubset.lagda.md` checks, one agda process
at the C-12 cap (`GHCRTS="-A64m -I0 -M8g"`), exit 0.

| run | cold own-content seconds (real / user) | load average |
|---|---|---|
| before the edit | 15.35 / 14.92 | 4.06/4.31/4.59 to 4.95/4.51/4.65, 4 users |
| after the edit | 15.74 / 14.57 | 4.64/4.46/4.63 at start; 5.21/4.80/4.75 at the next capture |

The basis is the [LJ-1.94] convention: the file's own content re-checked
cold, with the import cache warm (the master's `.agdai` moved aside, the
whole file re-typechecked). The delta is +0.39 s real, -0.35 s user:
measurement noise, not a cost change. Both figures are **MEASURED**.
The [LJ-1.101] inference that the cold master check costs "100 s or
more" is **MEASURED FALSE** at this site: 15.35 s.

## 2. WHAT THE BODY NEEDS (D-30)

`absorbs-subset` has exactly one use in the master:
`code-inj = comp-inj (absorbs-subset α α∉ω x x⊆Lα) (stage-card-upper α ordα α∉ω)`
(`src/L/BoundedSubset.lagda.md:1529-1530`), inside `BoundedSubsetAt`.

The module telescope of `BoundedSubsetAt` supplies these facts about `α`
(`src/L/BoundedSubset.lagda.md:1405-1407`): `ordα : IsOrd α`,
`α∈κ : ⟨ α ∈ˢ κ ⟩`, and `α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥`. There is no
premise forcing `ω ∈ α`. The consumer site instantiates the telescope
with `α = ω` and `α∉ω = ∈-irrefl ω`
(`src/ProbeLJ194A.agda:1202-1210`). So:

- The body never applies the statement at a finite `α` (**MEASURED** by
  reading: `α∉ω` is a module parameter of `BoundedSubsetAt`, and the
  site is `α = ω`).
- The body's domain includes `α = ω` (**MEASURED** by reading: the site
  shape is exactly the `BoundedSubsetAt` telescope, and no parameter
  excludes `α = ω`).
- The brief's obvious candidate, premise `⟨ ω ∈ˢ α ⟩`, is NOT a
  condition the site can supply (**MEASURED**: at the site it would
  demand `ω ∈ ω`, which `∈-irrefl` refutes; the site supplies only
  `α ∉ ω`).

The narrowest true statement the body still uses is therefore the one in
section 0: the same conclusion, conditional on `α ∉ ω`. This is C-38's
shape: the absorption is conditional, and the condition is exactly the
one the consumer's telescope supplies. A statement that holds only where
it is applied would not be a theorem; this statement holds on the whole
infinite ordinal class that the body's telescope permits, which includes
the site's `α = ω`.

## 3. THE REFUTATION ATTEMPT

**NOT REFUTED.** The attack file is `src/ProbeLJ1103A.agda`, GREEN at
the C-12 cap, exit 0, 4.04 s real (user 3.06) at load
5.21/4.80/4.75, four users.

- **Attack 1, the old counterexample (`α = ∅`, `x = ∅`).** The old
  refutation (`AbsorbsRefute.refute`, `src/ProbeLJ1101A.agda:153-156`)
  instantiates the statement at `α = ∅`. The new premise cannot be
  instantiated there: `∅ ∈ ω` (`#∈ω 0`), so
  `premise-refuted : (⟨ ∅ ∈ˢ ω ⟩ → Empty.⊥) → Empty.⊥` checks
  (`src/ProbeLJ1103A.agda:68-74`). The old counterexample is outside
  the new statement's domain. **MEASURED.**
- **Attack 2, the consumer site (`α = ω`, `x = ∅`).** The old attack
  pushes a union witness into an empty stage. At the site the stage is
  not empty (`∅ ∈ Lset ω`, `src/ProbeLJ1103A.agda:96-97`), and the
  conclusion is inhabited: `abs-site : ⟪ Lset ω ∪ ⁅ ∅ ⁆s ⟫ ↪ ⟪ Lset ω ⟫`
  checks, built by extensional equality of the union with the stage and
  transport with `transport⁻Transport` (`src/ProbeLJ1103A.agda:146-157`).
  The attack has no witness to refute with at the site, and the site
  supplies the premise (`α∉ω = ∈-irrefl ω`,
  `src/ProbeLJ1103A.agda:84-85`). **MEASURED.**
- The general form at every infinite `α` is not proved here and is
  **INFERRED** to hold, on the [LJ-1.101] price analysis
  (`_build/lj-1.101-report.md`, section 2.3: the infinite form is the
  true content, via the case split on `x ∈ Lset α` and the stage
  cardinality chain). Supply is outside this dispatch's abort
  criterion, so no proof is attempted.

## 4. THE DIFF

Two hunks in `src/L/BoundedSubset.lagda.md`:

1. the hypothesis at `:1364-1366`: the premise `(⟨ α ∈ˢ ω ⟩ → Empty.⊥)`
   inserted after `α` (2 lines replaced, same line count);
2. the application at `:1530`: `absorbs-subset α x x⊆Lα` becomes
   `absorbs-subset α α∉ω x x⊆Lα` (1 line replaced).

Six in-fence lines changed (3 removed, 3 added); **net non-blank
in-fence lines: 0** (1409 before, 1409 after, counted by the same
fence filter `scripts/ledger.py` uses). `scripts/ledger.py --brief`:
standing 28,189 lines over 85 masters, measured from HEAD `03fa4d2`
and re-verified at HEAD `b07d411` (the orchestrator's [LJ-1.101] commit,
which landed mid-dispatch); unchanged by this dispatch.
`scripts/check-fences.py --check`: clean, **87 masters**. No prose
changed (DD23): no sentence became false.

## 5. DD4

The corrected statement is shared content, unchanged in shape for the
other tower. It names only `S`, `ω`, `Lset`, the union presentation,
and injections; the new premise `α ∉ ω` is tower-independent ordinal
content, exactly the premise `stage-card-upper` already takes
(`src/L/BoundedSubset.lagda.md:1372-1374`). The J tower gets the same
statement with `Jset` in place of `Lset`, no other change: same
module telescope, same condition. **INFERRED** for J (no J tower exists
in this tree); **MEASURED** for the L side by the master check.

## 6. THE NEGATIVES AND THEIR STATUS

1. "The body applies `absorbs-subset` only at `α` with `ω ∈ α` (the
   brief's obvious candidate)": **MEASURED FALSE**. The consumer site
   runs at `α = ω` (`src/ProbeLJ194A.agda:1202-1210`), where `ω ∈ ω`
   is refutable.
2. "The body ever applies it at a finite `α`": **MEASURED FALSE**. Every
   application sits under `BoundedSubsetAt`'s `α∉ω` parameter
   (`src/L/BoundedSubset.lagda.md:1407`); the site is `α = ω`.
3. "The old `α = ∅` counterexample refutes the corrected statement":
   **MEASURED FALSE**. The premise at `α = ∅` is refuted by `∅ ∈ ω`
   (`src/ProbeLJ1103A.agda:70-74`).
4. "The conclusion is empty at the consumer site": **MEASURED FALSE**.
   `abs-site` inhabits it (`src/ProbeLJ1103A.agda:151-157`).
5. "The corrected statement is true at every infinite `α`":
   **INFERRED** (the [LJ-1.101] analysis plus the machine-checked site
   instance; no general proof exists).
6. "`Devlin55` re-checks green after the restatement": **MEASURED
   TRUE**. Exit 0, 15.74 s cold own content.

## 7. GATES

- `src/L/BoundedSubset.lagda.md`: GREEN after the edit, exit 0, cold
  own-content check 15.74 s at load 4.64/4.46/4.63 to 5.21/4.80/4.75,
  four users, machine NOT quiet, one process at the C-12 cap. Before:
  15.35 s at load 4.06/4.31/4.59 to 4.95/4.51/4.65. Final warm
  confirmation at HEAD `b07d411`: exit 0, 2.97 s.
- `src/ProbeLJ1103A.agda`: GREEN, exit 0, 4.04 s (user 3.06) at load
  5.21/4.80/4.75, four users, one process at the C-12 cap. 156 lines
  total, 131 non-blank lines (probe, not ledger-counted).
- `scripts/lint-prose.py --check` on the master, the probe and this
  report: exit 0.
- `scripts/lint-agda.py --check` on the master and the probe: exit 0.
- `scripts/check-fences.py --check`: clean, 87 masters.
- `scripts/ledger.py --brief`: standing 28,189 lines over 85 masters
  from HEAD `03fa4d2`, re-verified at `b07d411`; unchanged.
- C-12: every agda invocation returned; none hung, so nothing was
  killed. The sandbox denies `ps`/`pgrep` process listing, so liveness
  is verified by each invocation completing and reporting exit 0.
- No `make check` (forbidden). No commit, no push. `git status`: the
  only change is this dispatch's master edit; the probe and report are
  ignored. HEAD moved during the dispatch from `03fa4d2` to `b07d411`
  (the orchestrator's [LJ-1.101] commit); it did not touch the master.

## 8. ARCHIVE USED

- `_build/lj-1.101-report.md`, read WHOLE. TOOK the refutation
  (`AbsorbsRefute.refute`, `src/ProbeLJ1101A.agda:153-156`), the two
  candidate forms (site instance 20 to 30 lines; general infinite form
  150 lines with the union presentation as the widest unmeasured term),
  and the blast radius (`Devlin55` at `:1361`, `BoundedSubsetAt` at
  `:1396`, the use at `:1530`).
- `src/ProbeLJ1101A.agda`, read WHOLE. TOOK `AbsorbsRefute`
  (`:140-156`), the `cardκ`-at-master closure (`:56-57`), and the
  imports/notation the probe reuses.
- `src/L/BoundedSubset.lagda.md`, read `:1361-1626` WHOLE (the whole
  `Devlin55`), plus `:1040-1050`, `:1144-1215`, `:1520-1535`. TOOK the
  module telescope (`:1396-1402`), the single use (`:1530`), the
  `UnionKit` patterns (`X-mem`, `X⊆Lλ`, `sgl≡`, `∅∈Lset1` at
  `:1153-1215`), and `IsCardinal`/`_↪_` (`:1042-1046`).
- `src/ProbeLJ194A.agda`, read WHOLE. TOOK `SiteAt` (`:1186-1233`):
  `α = ω`, `α∉ω = ∈-irrefl ω`, `x = ∅`, `x⊆Lα`. This proves that the
  site needs the statement at `α = ω`.
- `src/ProbeLJ190A.agda`, read `:199-215`. TOOK the site shape
  (`:204-211`) and its `α = ω` instantiation.
- `_build/lj-1.94-report.md`, read WHOLE. TOOK the cold measurement
  convention (own content cold, import cache warm) and the site table.
- `src/L/StageCardinal.lagda.md`, read `:205-215` and `:555-565`. TOOK
  `stage-card-lower` (`:207-209`) and `stage-card-upper` (`:557-559`),
  which the general form would ride.
- `src/L/Axioms/Basic.lagda.md`, read `:485-495` and `:190-215`. TOOK
  `∅∈𝒟ₒ` (`:490-491`) and `Lset-suc` (`:196-197`).
- `dev/LESSONS.md`, read WHOLE C-38 as extended (`:3427`), C-36
  (`:3284`), D-10 (`:1316`), D-29 (`:3242`), D-30 (`:3332`). TOOK
  C-38's conditional-closure shape, D-10's consumer-walk, and D-30's
  price-what-the-consumer-needs.
- `dev/literature/devlin-II5.md`, read the 5.5 block (`:145-166`). TOOK
  the literature answer.
- `scripts/rules.py --for build` and `--for rewrite`: every statement
  read.

## 9. LITERATURE (DD18)

Devlin's 5.5 assumes `x ⊆ L_α` for some `α < κ` and consumes
`|L_α| = |α|` for infinite `α` (`dev/literature/devlin-II5.md:147-166`).
The absorption `|L_α ∪ {x}| = |L_α|` is exactly the content
`absorbs-subset` carries, and it is applied at infinite `α`. The
corrected premise matches the literature.

## 10. THE ABORT CRITERION

The first branch fired: the restated hypothesis survived the attack, and
`Devlin55` re-checks green. The report stops here; the hypothesis is NOT
supplied.

## 1. THE VERDICT

(placeholder: Devlin55 green? seconds before/after, load)

## 2. WHAT THE BODY NEEDS (D-30)

(placeholder: the single use at file:line, the site's α)

## 3. THE REFUTATION ATTEMPT

(placeholder: REFUTED or NOT REFUTED, MEASURED/INFERRED)

## 4. THE DIFF

(placeholder: lines changed, ledger count, fences count)

## 5. DD4

(placeholder)

## 6. THE NEGATIVES AND THEIR STATUS

(placeholder)

## 7. GATES

(placeholder)

## 8. ARCHIVE USED

(placeholder)
