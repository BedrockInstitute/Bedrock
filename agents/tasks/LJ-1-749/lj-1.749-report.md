# LJ-1.749 return: prʟ-in-Lset-lim, the L-presentation of the closedω pair

**Disposition: GO.** The obligation `prʟ-in-Lset-lim` is inhabited at
`agents/tasks/LJ-1-749/Probe749.agda:57-64`. The file typechecks at the pane
caliber with rc 0 (runs/green-1.out, runs/green-2.out; 1.09 s and 1.08 s,
runs/green-1.time, runs/green-2.time). `pair-in-Lγω` and `table-sat` are not
inhabited; both names occur in the file only once, in the header comment at
Probe749.agda:11 that records their absence. Nothing landed in `src/`; the
working tree carries only `agents/tasks/LJ-1-749/`. No
`review-of-prʟ-in-Lset-lim.md` is written, because there is no NO-GO to state.

## What the obligation is

The brief asks for the L-PRESENTATION of the pairing leaf 748 delivered:

    prʟ-in-Lset-lim :
        (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        (a b : S)
        → ⟨ fst a ∈ˢ Lset γ ⟩ → ⟨ fst b ∈ˢ Lset γ ⟩
        → ⟨ fst (prʟ a b) ∈ˢ Lset γ ⟩

Here `a b : S` are CODES: `S` is `𝒮ʟ`'s carrier, the Σ of a V element over
`isL` (src/L/Constructible.lagda.md:420, `𝒮ʟ = 𝒮ᵥ ↾ isL`; the restriction's
carrier is `Σ[ x ∈ S ] (x ∈ᶜ M)` at src/FOL/ZFStructure.lagda.md:145-147), and
`fst a` is its underlying V element. `prʟ` pairs codes and `prʟ-fst` reads the
pair's first projection back as the V pair
(src/L/Coding/Model.lagda.md:326-330). So the obligation is 748's
`pr-in-Lset-lim` carried across one transport along `prʟ-fst`. It is not
`pair-in-Lγω` and it is not `table-sat`.

## What was built

`agents/tasks/LJ-1-749/Probe749.agda`, 64 lines, ONE section.

- The module header (Probe749.agda:36) takes the same `(ℓ lem)` telescope
  748's probe takes, because the obligation's own telescope `(γ oγ clγ)`
  needs `closedω`, whose home module reads `lem`.
- `pr-in-Lset-lim` is IMPORTED, not transcribed:
  `open import LJ-1-748.Probe748 {ℓ} lem using ( pr-in-Lset-lim )`
  (Probe749.agda:44). `bedrock.agda-lib` carries `agents/tasks` as an include
  root, so the predecessor probe is a module and the transcription wall of
  748 is paid once, on 748's side of the import.
- The obligation (Probe749.agda:57-64) is a three-line body:

      subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym (prʟ-fst a b))
        (pr-in-Lset-lim γ oγ clγ (fst a) (fst b) ha hb)

  `sym` points the transport the right way: `prʟ-fst a b : fst (prʟ a b) ≡
  pr (fst a) (fst b)`, and the proof in hand concludes at the V pair, so the
  substitution runs from the V pair back to `fst (prʟ a b)`.
- THE `S` HANDLING is the one shape worth naming. `hPropStructure 𝒮ᵥ`
  publicly re-exports its own `S` (`= V ℓ`), which would collide with the
  L carrier the obligation reads; the probe hides it and takes `S` from the
  L structure instead (Probe749.agda:47-51): the V open supplies `∈ˢ` at V,
  the L open supplies the carrier. With that, `fst a : V ℓ` and every clause
  of the statement assembles against 748's term.

## Deviations

1. **First floor attempt died in 0.08 s: the file had no module header**
   (Agda `ModuleNameDoesntMatchFileName`). That run elaborated nothing and is
   not a price; the floor files in `runs/` hold the real floor run after the
   header was added.
2. **The W3 probe and the obligation are ONE file here.** The brief priced
   the widest unmeasured term at 20 to 80 lines; the whole probe is 64 lines,
   and the obligation IS the W3 term, so no separate miniature was written.
   The measurement is in the next section.
3. **Interpreter path.** This worktree carries no `.venv/` (measured, `ls`).
   The survey check ran with the main checkout's pinned interpreter,
   `/Users/alsg/Agentic/Bedrock/.venv/bin/python`, against this worktree's
   `scripts/pod/check-survey-quotes.py`. No dependency was added or
   installed. Same deviation as 748's report, deviation 4.

## Measurements

All runs at the wide caliber `-A64m -I0 -M2g`, set on the pane by the
program, never set by this agent. One Agda process at a time.

| run | rc | real | file |
|---|---|---|---|
| floor-1 | 42, expected, the one floor hole is the only diagnostic | 1.28 s | runs/floor-1.time |
| green-1 | 0 | 1.09 s | runs/green-1.time |
| green-2 | 0 | 1.08 s | runs/green-2.time |

The floor prices the frame: the import header, the cross-probe import of
748's full tree, both `hPropStructure` opens, and the obligation statement.
green-1 and green-2 run with interfaces cached by the floor run, so the real
frame cost is between 1.08 s and 1.28 s and the body costs less than a
tenth of a second over the floor. The term is frame-dominated. No heap wall,
no timeout, no restructuring.

**W3, measured: the subst along `prʟ-fst` does NOT convert, and it does not
need to.** `subst`'s declared type already lands the application at the goal
(`P y` from `p : x ≡ y` and `P x`), so the elaborator accepts the body
without `prʟ-fst a b` reducing to `refl`, which it cannot: it is a composite
path over `pairʟ-fst` and `cong₂` (src/L/Coding/Model.lagda.md:329-330). The
green run is the proof. The caveat the next brief must carry: the transported
membership is STUCK in any normal form, so a later tag-atom brief that needs
`fst (prʟ a b) ∈ˢ Lset γ` to compute further (to unfold inside another
conversion) will face that stuck term, not `pr-in-Lset-lim`'s body.

## What the next brief needs

- **Supply is now 1 for the L-pair leaf.** Cite
  `agents/tasks/LJ-1-749/Probe749.agda:57`. Beside 748's V-pair leaf, the
  tag-atom leaf the tower graph wanted now exists at both presentations.
- **Probes import probes.** The transcription wall 748 reported has a
  cheaper route for ANY successor: `bedrock.agda-lib` puts `agents/tasks` on
  the include path, so `open import LJ-1-748.Probe748 {ℓ} lem using (...)`
  works and the probe stays at 64 lines instead of 137. The file must carry
  its module header (`module LJ-1-749.Probe749 ...`) for this to resolve.
- **The `∅∈λ` wall is behind us for the pairing laws.** It sits inside
  748's transcription, and importing 748 does not reopen it. The src split
  748 proposed (a numeral-free `BoundOver` core) is still open src surgery
  and is still barred to this slot.
- **The stuck-subst caveat above** is the one thing a `succʟ`-or-higher
  presentation brief should price before it stacks transports: each
  `prʟ`-projection law adds one stuck layer.
- **Prices to plan with:** floor 1.28 s, green 1.09/1.08 s at wide caliber.
- **`S` is ambiguous in this corner of the tree.** Any probe that opens
  `hPropStructure` on BOTH structures must `hiding ( S )` one of them; the
  L carrier is the one the obligation statement reads.

## Stops

None. The obligation was supported, the premises held, and the term
typechecked under the delivered telescope on the first real attempt.

## Check survey quotes

Output of the mandated check, run as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-749`
against the finished return:

    check-survey-quotes: LJ-1-749 clean (0 note(s), 0 defect(s))

    rc=0

## ARCHIVE USED

Corpus search named five CANDIDATEs. None was read; none bears on a closed
Agda transport.

- archive/dev/DD-archived.md: declined, not read; the closed campaign
  decisions name no pairing law and no transport shape.
- archive/dev/ORCHESTRATION.md: declined, not read; the probe rules this
  task ran under live in agents/README.md and the brief, both in hand.
- archive/dev/PLAN-archived.md: declined, not read; this task's plan came
  from its own brief, not from a retired plan.
- archive/dev/TASKS-archived.md: declined, not read; the retired-route task
  list cannot cite files this obligation stands on.
- archive/dev/STATUS-archived.md: declined, not read; standing status is
  dev/pod/screen.toml, the only admissible home for it.

## LITERATURE USED

Corpus search named five CANDIDATEs. None was read; the obligation is a
one-transport assembly of a proved src equation and a proved probe law, so
no source or terminology question arises.

- dev/literature/glossary-review-2026-08.md: declined, not surveyed; the
  return adds no term and translates nothing.
- dev/literature/devlin-errata.md: declined, not read; the mathematical
  content came from the tree, src/L/Coding/Model.lagda.md:326-330, not from
  a source digest.
- dev/literature/level-formula-slot-roles.md: declined, not read; this
  obligation names no level formula and no slot arithmetic.
- dev/literature/primary-sources.md: declined, not read; no attribution or
  provenance question is open in a code-only probe.
- dev/literature/BIBLIOGRAPHY.md: declined, not read; the probe cites no
  literature and the report cites no source beyond the tree.
