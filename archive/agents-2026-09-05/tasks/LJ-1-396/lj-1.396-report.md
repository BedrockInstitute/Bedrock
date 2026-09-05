# LJ-1.396 report: `AmbCard` has a producer; `kappa-is-limit` is false as stated

slot: `coder`. Written early as a skeleton and filled as answers landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-396/`. Agda ran under the
caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time, no heap event.

TARGET: build TWO terms in `agents/tasks/LJ-1-396/Probe396.agda`, at a GENERIC
ordinal: `amb-card-at-kappa` and `kappa-is-limit`.

## VERDICT

SPLIT. GO on `amb-card-at-kappa`. NO-GO on `kappa-is-limit`, and the NO-GO is
a refutation: the statement is FALSE as stated, and the refutation is green in
Agda. The repaired form `kappa-is-limit-ω∈γ` is also green.

1. `amb-card-at-kappa` is GREEN (`Probe396.agda:92-100`). The producer exists.
   It is one composition under a truncation, and no step untruncates anything.
2. `kappa-is-limit` is REFUTED. The site is `a := sucV ∅`. At that site
   `fst κ = sucV ∅`, and the member `γ := ∅` forces `⟨ sucV ∅ ∈ sucV ∅ ⟩`,
   which `∈-irrefl` kills. The refutation `kappa-is-limit-refuted` is green
   (`Probe396.agda:152-161`). The obligation is left as a hole (`:106-110`),
   red by design, exactly as `[LJ-1.392]` left its refuted `amb-limit`
   (`agents/tasks/LJ-1-392/Probe392.agda:215`).
3. The repaired form `kappa-is-limit-ω∈γ` is GREEN (`Probe396.agda:172-184`).
   It is `[LJ-1.392]`'s `amb-limit-ω∈γ` (`Probe392.agda:255-266`) at the
   selected `κ`, with TERM 1 as the no-injection hypothesis.

THE MISSING HYPOTHESIS, TWO LAYERS. The stated `kappa-is-limit` has no
infiniteness hypothesis at all. The local repair is `⟨ ω ∈ γ ⟩`: with that
conjunct, successor-closure at infinite members is one application of
`suc∈or≡`. The global repair is `⟨ ω ∈ fst a ⟩`: with that, full
successor-closure of `κ` would still need `⟨ ω ∈ fst κ ⟩` (that `|fst a|` is
infinite), which this probe does not build. The obstruction is stated in
`review-of-kappa-is-limit.md`, written for the branch `no-go-stated`.

## 1. What was built

All in `agents/tasks/LJ-1-396/Probe396.agda`, module
`LJ-1-396.Probe396 {ℓ} (lem) (suc-absorb)`:

- `beta-lifts`, the W3 probe, first (`:59-60`). TWO code lines.
- `comp-inj`, the 3-line generic composition, written INLINE (`:75-77`). It is
  the term `L.StageCardinal.Upper.comp-inj` (`src/L/StageCardinal.lagda.md:500`),
  but that module takes the square-law parameter `sq` this probe does not have
  and must not assume, so the probe writes the generic lemma itself.
- `AmbCard`, spelled UNFOLDED, as `[LJ-1.393]` did (`:79-81`). It is a
  definition, not a producer.
- `amb-card-at-kappa`, TERM 1, green (`:92-100`). Nine code lines.
- `kappa-is-limit`, TERM 2 as the brief states it, a hole (`:106-110`).
- The refutation: `a1` (`:122-125`), `o1` (`:127-128`), `noInjEmpty`
  (`:133-137`), `κ-not-∅` (`:139-143`), `κ≡suc∅` (`:145-150`),
  `kappa-is-limit-refuted` (`:152-161`).
- `kappa-is-limit-ω∈γ`, the repaired form, green (`:172-184`). Thirteen code
  lines. `suc-absorb` is spent here and only here.

`suc-absorb` is a module hypothesis. Its type is the unfolding of
`Probe392.agda:121` (`⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`). The probe does not import
`Probe392`. The brief named `[LJ-1.395]` as the precedent for that packaging
(`agents/tasks/LJ-1-395/lj-1.395-report.md:44-50`); that file is not in this
tree, so the packaging follows `[LJ-1.393]`'s module-hypothesis pattern
instead.

## 2. TERM 1: the producer, and how it costs nothing

`LeastCardInjL` is opened and not restated (`Probe396.agda:96`), as the brief
orders (`src/L/Cardinal.lagda.md:60`). The three steps are the brief's three:

1. `κ-inj` gives `∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁`
   (`src/L/Cardinal.lagda.md:133`).
2. `PT.map` carries `comp-inj` with `e` under the truncation (`Probe396.agda:100`).
3. `beta-lifts` turns the bare `β` into an L-element, and `κ-min-at` refutes it
   (`Probe396.agda:99`).

No step untruncates anything. `κ-min-at`'s third argument IS the truncated
injection (`src/L/Cardinal.lagda.md:140-142`), so the truncated result feeds it
directly, and its conclusion is `Empty.⊥`. This is why the producer costs no
principle: it is the checklist's first case, the proposition-valued goal absorbs
the truncation.

## 3. TERM 2: the refutation

`fst κ` is the least member of `sucV (fst a)` that admits an ambient injection
of `⟪ fst a ⟫` (`src/L/Cardinal.lagda.md:104-106`, `:122-123`). That is the
cardinality `|fst a|`. For `fst a = sucV ∅` it is `sucV ∅`, a finite ordinal.

The refutation proves this in Agda at the one site `a := sucV ∅`:

- `κ≡suc∅` (`Probe396.agda:145-150`): `fst κ ∈ sucV (sucV ∅)` (from `κ∈sα`),
  and `fst κ ≠ ∅` (from `κ-inj` plus the fact that `⟪ sucV ∅ ⟫` is inhabited
  and `⟪ ∅ ⟫` is empty, `noInjEmpty`), so `fst κ = sucV ∅`.
- `kappa-is-limit-refuted` (`:152-161`): feed `γ := ∅` with
  `∅ ∈ sucV ∅ = fst κ`, get `⟨ sucV ∅ ∈ sucV ∅ ⟩`, and `∈-irrefl` kills it.

So no term of the stated type exists in `--safe` cubical, because the
refutation builds a term of its negation.

## 4. The repaired form, green

`kappa-is-limit-ω∈γ` (`Probe396.agda:172-184`) is the brief's own reasoning
with `⟨ ω ∈ γ ⟩` made a hypothesis. `suc∈or≡`
(`src/L/Ordinal/Stages.lagda.md:137`) delivers both cases at once:

- `sucV γ ∈ fst κ`: that is the goal.
- `sucV γ ≡ fst κ`: `suc-absorb` produces `⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`, the equality
  rewrites it to `⟪ fst κ ⟫ ↪ ⟪ γ ⟫`, and TERM 1 at `β := γ` refutes it.

No case split on `γ`. The finite case is exactly the counterexample, so it is
cut by the new hypothesis and not proved.

## 5. W2 and DD4

TERM 1 is written once at a generic `a : S`, with `oa : IsOrd (fst a)`. The
statement names no ordinal, no site and no numeral. TERM 2's statement is also
generic; only the refutation names a site, which is what a refutation must do
(C-42). The repaired form is generic in `a` and in `γ`.

## 6. W3: `beta-lifts`, first

GO. The brief named step 3's lift as the widest unmeasured term, and ordered it
stated alone and run before anything else. It is `beta-lifts` (`Probe396.agda:59-60`),
TWO code lines. The lift is: `β , isL-trans β∈κ (snd κ)`, one membership in a
level plus the level proof `snd κ`, nothing else.

## 7. Runs, floor, slots

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, from the repository root, 2026-08-20. The only
error in every full-file run is the hole at `Probe396.agda:110`.

- Full file, three consecutive runs: 1.77 s, 1.86 s, 1.74 s. Median 1.77 s,
  exit 42 each time.
- Empty-module floor: 0.07 s, exit 0.

The repaired term, the producer and the refutation are all in the file that
Agda checked; they are green because the only unsolved meta is the stated hole.

## 8. C-42 sweep

The refutation measures ONE site: `a := sucV ∅`. COUNT of the named shape
(successor-closure of `LeastCardInjL.κ` with no infiniteness hypothesis) in
live `src/`: 0. COUNT of that shape as a stated obligation: 1, this task.

Two already-refuted cousins, not this shape and not funded against it:

- `amb-limit` (`agents/tasks/LJ-1-392/Probe392.agda:211-215`), successor-closure
  of a generic `α` given `AmbCard`, with `⟨ ω ∈ α ⟩` and without `⟨ ω ∈ γ ⟩`.
- `amb-init` (`agents/tasks/LJ-1-393/Probe393.agda:182-185`), `Init` from
  `AmbCard` without `⟨ sucV ω ∈ α ⟩`.

## 9. What GO and NO-GO each earn

GO on TERM 1 retires the sentence "`AmbCard` has no producer", at the selected
`κ` and at no other ordinal. The brief's own limits hold, and I state them:
`AmbCard (fst a)` stays without a producer, and the arrow from `a` down to `κ`
stays truncated (`src/L/Cardinal.lagda.md:132-134`).

NO-GO on TERM 2 earns the falsehood of the stated closure, at one site. The
repaired `kappa-is-limit-ω∈γ` is what the next brief can take as a hypothesis
if it wants the infinite-member case. Full successor-closure of `κ`, the
conjunct `amb-init'` needs, still wants `⟨ ω ∈ fst κ ⟩` and `⟨ sucV ω ∈ fst κ ⟩`.
The second follows from the first plus the repaired form. The first is not
built here.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md`: not used. It is the retired-route journal,
  and no step of this probe consults it.
- `dev/ARCHIVE.md`: not used. This probe retires no module and consults no
  archived module.
- `archive/dev/DECISIONS-archived.md`: not used. No archived ruling bears on
  this probe.
- `archive/dev/TASKS-archived.md`: not used. The archived task index names no
  task this probe reads.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`: not used. It is
  the condensation chapter of the archived rud route, and nothing in this
  probe needs it.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:143`, read: the reason
  "a proposition-valued goal absorbs the truncation" is exactly TERM 1's
  mechanism. The checklist's first case is the one the producer uses.
- `dev/literature/devlin-II5.md`: not used. The condensation digest bears on
  the GCH endpoint, not on the least-cardinal closure.
- `dev/literature/geology.md`: not used. It is sources for a later milestone.
- `dev/literature/terms-2026-08.md`: not used. No rendering question arises.
- `dev/literature/digest.md`: not used. The rud-route digest is not consulted
  by this probe.

## WHAT I DID NOT DO

- I did not restate or copy any part of `LeastCardInjL`; I opened it.
- I did not import `Probe392`; `suc-absorb` is a module hypothesis, unfolded.
- I did not touch `src/`, did not commit, did not push, and set no `GHCRTS`
  of my own.
- I did not claim the stated closure holds at any repaired statement. The
  refutation measures ONE site (C-42). The repaired form is a different
  statement, and I named it so.
- I did not build `⟨ ω ∈ fst κ ⟩` from `⟨ ω ∈ fst a ⟩`. That is the residue
  full closure still owes.
