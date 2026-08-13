# B1 report: the closure chapter opens

Repository `/Users/alsg/Agentic/Bedrock`, branch `godel-route`. Batch B1 per
`dev/memos/L3.29-b-pivot.md`, task brief
`/private/tmp/claude-501/-Users-alsg-Agentic-Bedrock/32fd5cc7-cdf2-47c8-a038-6728849765b0/scratchpad/b1-brief.md`.
Only `src/L/Godel/Closure.lagda.md`, `src/Everything.lagda.md`, and
`_build/b1-report.md` were touched; no git operations, no postulates, holes,
or TERMINATING/NON_TERMINATING pragmas anywhere in the new file.

## Status

The chapter typechecks green against the delivered route; `make check`'s five
stages pass (typecheck, markers, prose lint, Agda code lint, glossary), and
`reuse lint` passes (the sandbox blocks `os.sysconf` in the `reuse` worker
spawn, so the final stage was run with a one-line wrapper supplying a fallback
value; the file is covered by the `src/**` CC-BY-NC-SA-4.0 carve-out in
`REUSE.toml`, so its licensing is declared centrally, per `AGENTS.md`).

Warm check of the chapter alone: ~1.7 s (the delivered route stays in the
seconds-per-chapter class, as the pivot memo's ruling requires). Everything
with the chapter imported: ~2.6 s.

## Delivered

1. **The values generalization** `valuesAllTuples : (n) → values (allTuples A (suc n)) ≡ A`.
   Proved membership-wise from the tuple algebra alone: forward, the values of
   the tuple family read the first entry of an extended graph, which is a
   member of the carrier; backward, the constant assignment's tuple witnesses
   the first key. **No transitivity was needed**, so the statement is at a bare
   carrier; the report records that explicitly (the brief asked which).
   The zero case is excluded (the values of the empty graph are empty).
2. **The selection equations** `sat-∈vv-sel` and `sat-≐vv-sel`:
   `selectMember (satSet φ) ⁅# (toℕ i)⁆s ⁅# (toℕ j)⁆s ≡ satSet (φ ∧̇ (var i ∈̇ var j))`
   and the `selectEqual` analog with `≐`. The delivered `Satisfaction`
   equations run the other way (they prove the atom from the selection over
   `allTuples`), so these are stated here as new equations consuming the
   delivered stock: each proof swaps the selection witness against the atom
   equation's, with the lookup specification reading the entries back.
3. **The renaming law** `satSet-rename-shift`:
   `satSet (renameFo suc φ) ≡ extendFamily (satSet φ) A`, the engine the
   kinded invariant's extendFamily clause will consume. Proved via the
   restricted-structure renaming theorem (`Renaming.Sat` instantiated at
   `DefOf.𝒮M`, per `DefOf`'s inner semantics), with the `Agrees` condition
   built from the lookup-tabulation identity.
4. **The forward pinning inclusion** `extendFamily-pin`: a member of the full
   extension whose head is the constant already lies in the singleton
   extension, proved by reading the extended member's head off the graph
   against the lookup specification (the `headOfGraph` lemma).
5. **The singleton family** `singletons X = sett ⟪ X ⟫ (λ m → ⁅ ⟪ X ⟫↪ m ⁆s)`
   with both membership laws, `singletons-in` and `singletons-out`. The
   definition is union-free, one direct `sett`, one index telescope, and has
   **no `⋃`-tower in the index**, so per P-c no seal is needed at the birth
   site (the report records that explicitly).

## The statement chosen for item 3, and why

The pivot memo and the cut probe price "the family-extension equation on
satisfaction sets" as `extendFamily (satSet φ) ⁅κ a⁆s ≡ satSet ((var zero ≐
con a) ∧̇ rename-shift φ)`, the shape `Terms.sound`'s `selEqConK` case reads
backward. This batch delivers the two halves separately: the renaming law
(item 3, full equation) and the forward pinning inclusion (item 4). The
reverse pinning inclusion, and the full equation's assembly, are recorded in
`LESSONS.md`'s hazard class below and left to the closure chapter's own
consumption, where the kinded-invariant induction will spend the forward
direction and the next batch completes the reverse. The report states this
plainly rather than papering over it (the pivot memo's honest-accounting
condition).

## LESSONS laws that shaped choices (by ID)

- **P-b** (union-free operation definitions): `singletons` is one direct
  `sett`, no `∪`/`⋃` under a membership obligation.
- **P-c** (seal `⋃`-tower indices at birth): `singletons` has no `⋃`-tower,
  so no seal; recorded rather than assumed.
- **P-a** (tag discrimination through explicit-data helpers): the numeral-zero
  facts (`# 0 ≡ ∅` via `numeralV≡#`) and the `pr-inj` head readings are
  spelled with explicit indices; the `headOfGraph` continuation is named with
  its payload written down.
- **P-d** (reductions travel as direction pairs, never hProp paths): the
  satisfaction-set identities are proved as extensional equalities via
  membership-wise directions, never by pointwise paths between satisfactions.
- **P-g** (no `cong` with a function lambda at concrete presentation-carrying
  types): the reverse pinning direction's graph-to-tuple path rewrite kept
  hitting this wall class (the typechecker normalizing a satisfaction-indexed
  tuple against an `extendGraph` endpoint); the batch ships the forward
  direction and defers the reverse, with this recorded as the measured hazard.
- **Rule 1** (discharge adequacy substitutions at variable arguments):
  `Ren.⊨-rename` is applied at variable environments (`vec g`, `vec (tail g)`),
  never at concrete ones.
- **Rule 20** (composites of adequacy equations consumed factor by factor):
  the rename-shift proof consumes the renaming theorem as one factor and the
  tuple algebra as another, never as one composite path.
- **C-8** (the gate has blind spots): the linters were run explicitly on the
  untracked new file, since `git ls-files` would skip it.

## Reused vs newly proved

Reused: `L.Godel.Operations` (`extendGraph`, `extendFamily`, `selectMember`,
`selectEqual`, `values`, `singleton-self/out`, `∩`, `∪`), `L.Godel.Tuples`
(`allTuples`, `tuple`, `tuple-extend`, `tuple-entry`), `L.Godel.Satisfaction`
(conceptually: the equations are restated locally because `Satisfaction`'s
`vec`/`tab` are private, so a local `satSet`/`sat-in`/`sat-out`/`sat-∧`/
`sat-∈vv`/`sat-≐vv` are restated in this chapter and the delivered stock is
consumed through them), `L.Coding.Environment` (`lookup-spec`, `cons`),
`FOL.Manipulation.Renaming` (`renameFo`, `Renaming.Sat`), `DefOf` (the inner
semantics), `V.Model` (`numeralV≡#`), `InL`'s reader class (`sglAt′`) is
restated locally since it is private there.

Newly proved: `valuesAllTuples`, `satSet-rename-shift` (+ `agrees-suc`),
`extendFamily-pin` (+ `headOfGraph`, `headEq`), `sat-∈vv-sel`,
`sat-≐vv-sel`, the local satisfaction machinery, `singletons` +
`singletons-in`/`singletons-out`.

## New term choices

- zh 单例族 for "singleton family" (the brief's suggestion, adopted; ja
  would be 単集合族, not shipped since the site is en+zh). Surfaced per
  `AGENTS.md`; the glossary entry is not added here because the term appears
  only in this chapter's prose, and the glossary checker enforces renderings
  for git-tracked files (C-8). The owner may add `单例族` when the closure
  chapter lands.

## Surprises

1. `Satisfaction`'s `vec`/`tab` are private, so the satisfaction-set
   machinery had to be restated locally (a ~90-line restatement) rather than
   reused by import; the equations then run against the local restatement.
2. The reverse pinning direction (graph-to-tuple membership transport) is a
   genuine P-g-class wall: the typechecker normalizes a satisfaction-indexed
   tuple against an `extendGraph` endpoint, hanging well past the 180 s
   tripwire in several formulations (single `subst` chains, separate
   `subst`s, `cong₂` variants). The forward direction is cheap; the reverse
   is left to the next batch with the hazard recorded.
3. The `reuse` lint stage cannot spawn its workers in this sandbox
   (`os.sysconf("SC_SEM_NSEMS_MAX")` is blocked); a wrapper supplying a
   fallback value lets it pass. The licensing itself is declared centrally in
   `REUSE.toml` (the file falls under `src/**` → CC-BY-NC-SA-4.0), with no
   in-file SPDX headers, per `AGENTS.md`.
