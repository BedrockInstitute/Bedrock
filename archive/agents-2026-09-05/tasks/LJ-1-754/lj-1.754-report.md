# LJ-1.754 return: tagAtL-bounded-at-γ, the BoundedFo certificate of the tag reader

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: GO.** The obligation is inhabited at
`agents/tasks/LJ-1-754/Probe754.agda:81`. The file typechecks at the pane
caliber (`runs/green-2.out`, `runs/green-3.out`, `runs/green-4.out`, all rc 0,
under 1.6 s each, no warnings). `table-sat` and `mkBoundedFo` are absent from
the file, as the brief demands. Nothing lands in `src/`.

## What the obligation is

The brief names one term in `agents/tasks/LJ-1-754/Probe754.agda`:

    tagAtL-bounded-at-γ :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        → ⟨ ω ∈ˢ γ ⟩
        → {n : ℕ}
        → (s : Fin n)
        → (k : ℕ)
        → (x : Fin n)
        → BoundedFo (λ (c : S) → ⟨ fst c ∈ˢ Lset γ ⟩) (tagAtL s k x)

The body is one pair (`Probe754.agda:89-91`). `tagAtL s k x` unfolds to
`∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))`
(`src/L/Coding/Model.lagda.md:586`), so `BoundedFo` computes
(`src/FOL/Manipulation/Bounding.lagda.md:67`) to two factors:

- `(Lift Unit × P (numeralL k))` at `P := λ c → ⟨ fst c ∈ˢ Lset γ ⟩`. The
  second component is exactly `[LJ-1.747]`'s leaf. The probe imports it:
  `open import LJ-1-747.Probe747 {ℓ = ℓ} lem` (`Probe754.agda:31`), applied at
  `Probe754.agda:90`. The closer is NOT transcribed.
- `BoundedFo P (prAtL (suc s) zero (suc x))`. This is the new helper
  `prAtL-triv` (`Probe754.agda:69-71`), stated at ANY predicate `P` and any
  `q u v`, proved by the empty term `_`.

## The one finding: the empty certificate of prAtL is P-generic

`prAtL q u v = liftFo (prAt q u v) _` (`src/L/Coding/Model.lagda.md:123`).
`prAt` and its parts `sglAt` and `pairAt` are built from `var` alone
(`src/FOL/Bernstein.lagda.md:79-88`). So `liftFo` touches only `var`, and
`BoundedTm P (var i) = Lift Unit` for EVERY `P`
(`src/FOL/Manipulation/Bounding.lagda.md:65`). The certificate of `prAtL`
therefore normalizes to a closed nest of `Lift Unit`s that mentions neither
`P` nor the indices. Agda solves the hole in `prAtL-triv` at any predicate;
the file is green with `P` instantiated at the obligation's carrier predicate.
This is stronger than the brief's premise 3: the pair reader brings no
constant in, for any predicate whatsoever, not only this one.

## Shape kept, shape changed

- KEPT: the 747 leaf, imported whole. Its proof is untouched, and the file
  carries none of its internals (`Closer`, `Carrier`, `num∈λ` are never
  named). The import resolves in this worktree because
  `agents/tasks/LJ-1-747/Probe747.agda` is tracked here (`git ls-files`).
- ADDED: `prAtL-triv` (`Probe754.agda:69-71`), 3 lines. See the finding above.
- ONE telescope fact the brief could not name: the leaf is a lemma of a
  parameterized module. `Probe747` takes `lem : LEM (ℓ-suc ℓ)`
  (`agents/tasks/LJ-1-747/Probe747.agda:29`), so this probe carries the same
  parameter (`Probe754.agda:22`). The obligation's own telescope does not
  name `lem`; a consumer of this probe must supply it. If a later chapter
  needs this certificate without any classical parameter, the leaf itself
  must first be re-derived without `Stages`/`StageArith`. This is the only
  route constraint the obligation's type does not show.
- ONE scope repair, measured: the predicate's `S` is the carrier of `𝒮ʟ`.
  `L.Coding.Model` opens it non-publicly (`src/L/Coding/Model.lagda.md:70`),
  so the probe opens `hPropStructure 𝒮ʟ` for `S` directly
  (`Probe754.agda:55-56`). A blanket `open hPropStructure 𝒮ᵥ` also brings an
  `S`, and Agda refuses the ambiguity (`runs/floor-2.out`,
  AmbiguousOverloadedProjection). The cure is `hiding ( S )` on the `𝒮ᵥ`
  open (`Probe754.agda:47`). Both `S` names bind the same projection
  application as Model's own, so the predicate is the intended one.
- W2 answer. The brief's clause asks for one generic statement, instantiated
  per proof. `prAtL-triv` IS that statement: it is generic over the predicate
  and over all three indices, and the obligation instantiates it once. The
  747 leaf is imported, not copied. The only candidate for a `src/` home is
  `prAtL-triv` (a sibling of `BoundedFo` in
  `src/FOL/Manipulation/Bounding.lagda.md`, or beside `prAtL` in
  `src/L/Coding/Model.lagda.md`). Supply is 0 today and this brief forbids
  `src/` writes, so the probe is its home now. The first brief with a second
  consumer should lift it and name this return as the prior form.

## Premises, verified

1. `[LJ-1.747]` inhabited the leaf. `agents/tasks/LJ-1-747/lj-1.747-report.md:8`
   says "The obligation is inhabited at", naming `Probe747.agda:111`. Both
   files exist in this worktree and the import resolves.
2. `tagAtL` has one constant. `src/L/Coding/Model.lagda.md:585-586`: the body
   names `con (numeralL k)` once and `prAtL` once. Confirmed.
3. `prAtL` names no constants. `src/L/Coding/Model.lagda.md:103` says "the
   reader names no constants"; the trees at
   `src/FOL/Bernstein.lagda.md:79-88` are all `var`. Confirmed, and made
   P-generic by `prAtL-triv`.
4. Do not inhabit `table-sat` and `mkBoundedFo`. `table-sat` stays absent
   (`agents/tasks/LJ-1-747/lj-1.747-report.md:11` records the same absence at
   747). `mkBoundedFo` (`src/L/Axioms/Separation.lagda.md:449`) is never
   imported. Confirmed.

## What the next brief needs

- Supply 1 at the meter's name: later briefs may cite
  `agents/tasks/LJ-1-754/Probe754.agda:81` as the `BoundedFo` certificate of
  `tagAtL`, and `Probe754.agda:69` for the P-generic empty certificate of any
  all-variable formula reader built by `liftFo` from `var` trees. Note the
  `lem` parameter in the previous section before citing either.
- The assembly recipe, measured: `( lift tt , leaf k ) , prAtL-triv P (suc s)
  zero (suc x)` at `Probe754.agda:89-91`. The same recipe gives
  `prMemAtL`, `appAt`, and `tagPairAtL` certificates: their trees are the same
  all-variable `sglAt`/`pairAt` material (`src/FOL/Bernstein.lagda.md:79-96`),
  and `appAt f x y = ∃̇∈ (var f) (prAtL zero (suc x) (suc y))`
  (`src/L/Coding/Model.lagda.md:161`) needs only a `BoundedTm` for `var f`.
  A `tagPairAtL` certificate also needs the `numeralL` leaf once more; nothing
  new.
- The floor and the price sit 0.3 s apart (1.07 s against 1.36 s): the frame
  IS the cost, the certificate is free. No heap wall, no timeout, nothing left
  to trim: the import cone is the 747 cone plus `L.Coding.Model`, which the
  obligation's own type demands.
- EXIT-CODE HAZARD for the branch table, second occurrence: this dispatch
  produced rc 42 twice for reasons that are NOT a NO-GO
  (`runs/floor-1.out`, NoSuchModule on an unimported module;
  `runs/floor-2.out`, ambiguous projection), plus rc 42 for the floor hole
  itself (`runs/floor-3.out`, UnsolvedInteractionMetas, which is what a floor
  run is). Agda 2.8.0 exits 42 on every elaboration failure, so rows keyed on
  `exit_code = 42` cannot separate NO-GO from lint-class defects. This report
  is the disambiguator, and it names the GO.
- The ratio bar cannot fire here: the probe is a raw `.agda` file, so its
  in-fence line count is 0.

## W3 answer

The brief's W3: whether `BoundedFo` of `tagAtL` assembles from 747's leaf and
the empty certificate of `prAtL` (estimated 20 to 80 lines). IT ASSEMBLES. The
proof proper is 11 lines of file (`Probe754.agda:69-71` and
`Probe754.agda:81-91`); the rest is imports and header comments. No binder
resisted and no universe moved. The one resistance was scope, not typing: the
`S` ambiguity above, closed by `hiding ( S )`. The estimate was right.

## Runs (wide caliber, pane GHCRTS untouched, one Agda process per run,
/usr/bin/time -p, src/ chain warm from this worktree's `_build`)

- `runs/floor-1.out`: rc 42, NoSuchModule (`open` without `import`). Not a
  price. Scope-class failure, recorded for the hazard row above.
- `runs/floor-2.out`: rc 42, AmbiguousOverloadedProjection on `S`. Not a
  price. Scope-class failure, recorded for the cure above.
- `runs/floor-3.out`: rc 42, UnsolvedInteractionMetas at the floor hole. This
  is the floor run WITH the hole standing in, as the 2026-08-23 ruling asks.
- `runs/floor.out`: THE FLOOR. Obligation block removed, rc 0, 1.07 s.
- `runs/green-1.out`: first full shape, inline `_` for the `prAtL` factor,
  rc 0, 1.08 s.
- `runs/green-2.out`: THE PRICE. Final shape with `prAtL-triv`, rc 0, 1.36 s.
- `runs/green-3.out`: re-certification, rc 0, 1.52 s.
- `runs/green-4.out`: re-certification after a comment-only edit, rc 0,
  1.34 s. This is the file as it stands.

## Mandated paste

    $ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-754
    check-survey-quotes: LJ-1-754 clean (0 note(s), 0 defect(s))

    (lint-agda.py --check also ran, rc 0. The interpreter is the main tree's
    .venv; the worktree carries none.)

## ARCHIVE USED

- `archive/dev/DD-archived.md:25`: "| DD9 | Classical boundary, and generated
  proof | No `postulate` anywhere. LEM, and any classical or choice principle,
  is an explicit parameter; the whole tree is `--safe`." READ. This probe
  carries LEM as the explicit parameter the leaf already takes, postulates
  nothing, and sits outside `src/`, so DD9's claim stays true of the checked
  tree.
- `archive/dev/ORCHESTRATION.md`: declined, not read. Dispatch wiring is the
  program's business; this return writes one probe and its report.
- `archive/dev/PLAN-archived.md`: declined, not read. The disposition follows
  the brief's own branch table, not the archived plan.
- `archive/dev/STATUS-archived.md`: declined, not read. The standing status is
  `dev/pod/screen.toml`, and no standing figure is quoted here.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  evidence this return builds on is cited at `file:line` from the live tree.

## LITERATURE USED

- `dev/literature/devlin-errata.md:98`: "- Bounding quantifiers (10.6, p. 60):
  the proposed bounding class for the". SCANNED for anything on the tag and
  pair readers this certificate bounds. The errata rows concern the 10.6
  bounding class and the definability of Sat, not the syntax certificate; the
  formal side already carries the readers (`src/FOL/Bernstein.lagda.md:79-88`)
  and their absoluteness. Nothing here bears on the assembly.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. This return
  introduces no term and proposes no glossary entry.
- `dev/literature/level-formula-slot-roles.md`: declined, not read. No
  level-formula slot is touched; the obligation quantifies over `k : ℕ` and
  never names a formula code.
- `dev/literature/primary-sources.md`: declined, not read. The formal facts
  this return needs are already green in the tree; no fetch decision is open.
- `dev/literature/BIBLIOGRAPHY.md`: declined, not read. No source is fetched
  or consumed by this task.
