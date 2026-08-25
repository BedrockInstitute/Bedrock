# [LJ-1.639] report: the residue's identification, as a term

**VERDICT: GO.** The obligation is discharged. `refl` closes it, on the nose,
with no transport and no unfolding hint.

**Evidence:** `agents/tasks/LJ-1-639/Probe639.agda:110-111`, green three
times: `agents/tasks/LJ-1-639/runs/final-1.out` (`EXIT=0`, 2.07 s),
`runs/final-2.out` (`EXIT=0`, 1.95 s), and `runs/final-3.out` (`EXIT=0`,
2.33 s), which is the run of the file exactly as it now stands.

Nothing landed in `src/`. The task wrote one probe, one floor form, one
negative control and this report.

## 1. The row

```
residue-is-kappa-inj : P618.Inj-extract ≡ UnTrunc KappaInj
residue-is-kappa-inj = refl
```

`agents/tasks/LJ-1-639/Probe639.agda:110-111`.

`P618.Inj-extract` is imported from `[LJ-1.618]`, not restated
(`agents/tasks/LJ-1-618/Probe618.agda:151-155`). `KappaInj` and `UnTrunc` are
`agents/tasks/LJ-1-639/Probe639.agda:82-83` and `:99-100`.

## 2. What the brief asked, and what stops the row from being empty

The brief asked for a row that `refl` closes if the two types agree. A `refl`
between two hand-written copies of one string agrees with itself and measures
nothing. Two devices prevent that here.

**Device 1: the untruncation is an OPERATOR, written once.**
`UnTrunc T = (a : S) (oa : IsOrd (fst a)) → ∥ T a oa ∥₁ → T a oa`
(`agents/tasks/LJ-1-639/Probe639.agda:99-100`) is generic in the family. The
residue's type is never written a second time by hand, so the row can only hold
if the residue really is this operator at this family.

**Device 2: the family is ANCHORED to `src/`'s own term.**
`kappa-injL-delivers : (a : S) (oa : IsOrd (fst a)) → ∥ KappaInj a oa ∥₁`, with
body `κ-injL` (`agents/tasks/LJ-1-639/Probe639.agda:85-86`). The elaborator
checks `src/L/SquareLawClosed.lagda.md:82-84`'s own term against the name. If
`KappaInj` ever stopped being the payload of `κ-injL`'s truncation, that row
goes red before the identification does.

**The negative control.** `agents/tasks/LJ-1-639/runs/Control.agda:45-46` is the
same row with the family deliberately wrong (`fst a` in place of
`fst (κL a oa)`). It is RED, and the error names the exact difference:

    Control.agda:46.21-25: error: [UnequalTerms]
    fst a != fst (κL a oa) of type
    Cubical.HITs.CumulativeHierarchy.Base.V ℓ

`agents/tasks/LJ-1-639/runs/control-1.out:5-8` (`EXIT=42`). So the `refl` in the
probe discriminates. It is a measurement.

## 3. W3, the widest unmeasured term: ANSWERED

The brief named this term: whether the two types agree ON THE NOSE or up to an
unfolding. **They agree on the nose.** `refl` closes the row with no `subst`, no
`transport` and no `unfolding` clause, in a module that sees `κL` only through
its `opaque` seal (`src/L/SquareLawClosed.lagda.md:72-84`).

Two further rows show the identification is definitional in BOTH directions,
because each passes a term across it as the identity function:

- `residue→untrunc r = r` (`agents/tasks/LJ-1-639/Probe639.agda:127-128`)
- `untrunc→residue u = u` (`agents/tasks/LJ-1-639/Probe639.agda:130-131`)

Both were already green in the floor run, with Section 2 holed
(`agents/tasks/LJ-1-639/runs/floor-1.out`), so the identification does not
depend on the row that states it.

The brief estimated 30 to 60 lines. The probe is 207 lines. The excess is not
the row. It is Sections 4 to 6, which record three more facts the next brief
would otherwise re-derive. Section 3.5 below prices them.

## 4. The floor, and the frame

Per the heavy-object rule, the floor was measured BEFORE the final form.

| run | file | cap | result | wall |
|---|---|---|---|---|
| `runs/floor-1.out` | `runs/Floor.agda`, Section 2 holed | 600 s | `EXIT=42`, one `UnsolvedInteractionMetas` | 2.40 s |
| `runs/final-1.out` | `Probe639.agda` | 600 s | `EXIT=0` | 2.07 s |
| `runs/final-2.out` | `Probe639.agda` | 600 s | `EXIT=0` | 1.95 s |
| `runs/final-3.out` | `Probe639.agda`, as it now stands | 600 s | `EXIT=0` | 2.33 s |
| `runs/control-1.out` | `runs/Control.agda` | 600 s | `EXIT=42`, `UnequalTerms` | 1.92 s |

Caliber `GHCRTS=[-A64m -I0 -M2g]` on every run, recorded in each `.out`. The
program set it; this task did not. One Agda process at a time. No heap wall
occurred and no restructuring was needed.

**Read the floor this way.** `floor-1` also had to check
`agents/tasks/LJ-1-618/Probe618.agda`, so 2.40 s is the frame plus that
dependency, cold. `final-1` did not, and it came in at 2.07 s. **The row itself
costs nothing measurable.** The imports were trimmed to the facts the rows use
before the first run: `L.SquareLawClosed` is opened with
`using ( κL; κ-injL; κ-min-atL )`, and `L.Cardinal` with
`using ( _↪_; module LeastCardInjL )`
(`agents/tasks/LJ-1-639/Probe639.agda:57-58`).

## 5. What else the probe records, and why each row is there

The next brief gets these as terms, not as prose.

**5.1 The truncation is `leastOf`'s interface, not the injection's.** The
brief's premise 3, as two `refl` rows:

- `payload-is-leastOf-Inj : KappaInj a oa ≡ LeastCardInjL.Inj a oa (κL a oa)`
  (`agents/tasks/LJ-1-639/Probe639.agda:153-156`)
- `premise-is-leastOf-InjP : ⟨ LeastCardInjL.InjP a oa (κL a oa) ⟩ ≡ ∥ KappaInj a oa ∥₁`
  (`agents/tasks/LJ-1-639/Probe639.agda:158-161`)

**This is the row with the most value for a later attack.** It says the `∥_∥₁`
in the residue's premise is the SAME `∥_∥₁` that `src/L/Cardinal.lagda.md:66-67`
introduces to satisfy `leastOf`'s hProp-valued predicate slot, and that no
second truncation is hiding anywhere between them. So the truncation is
removable in principle exactly where the hProp wrapper was added, and nowhere
else.

**5.2 The residue does not touch minimality.** The brief's premise 4.
`kappa-min-untouched` re-ascribes `κ-min-atL`'s type UNCHANGED
(`agents/tasks/LJ-1-639/Probe639.agda:182-186`). The membership half is what
the residue quantifies over; the minimality half stays truncated in its own
premise and stays available.

**HONEST LIMIT, stated in the file at `:174-179`.** `κ-injL` and `κ-min-atL` are
`opaque` (`src/L/SquareLawClosed.lagda.md:72`). From outside the seal this probe
checks TYPES against `src/`, not bodies. That `κ-inj = fst (snd least)` is READ
at `src/L/Cardinal.lagda.md:133-134`. It is not re-derived here, and no row of
this file proves it.

**5.3 The residue is a RESTRICTION, and this is the one a pricer needs.**
`Inj-extract-wide` (`agents/tasks/LJ-1-639/Probe639.agda:202-204`) is the
untruncation of an ambient injection between two ARBITRARY L-elements. TYPE
ONLY; no row inhabits it. The implication runs one way and only one way:

    wide→residue : Inj-extract-wide → P618.Inj-extract
    wide→residue w a oa = w a (κL a oa)

`agents/tasks/LJ-1-639/Probe639.agda:206-207`, green. **Anyone who prices the
residue against a general choice principle is pricing the WIDE form, which is
strictly more.** The residue asks only at the pairs `(a , κL a oa)`.

**5.4 The identification at the same `a` and `oa`, spent.**
`residue-at-src-witness ext a oa = ext a oa (kappa-injL-delivers a oa)`
(`agents/tasks/LJ-1-639/Probe639.agda:133-135`). This is the application
`[LJ-1.618]`'s descent case already makes
(`agents/tasks/LJ-1-618/Probe618.agda:204`: `ext a ox (κ-injL a ox)`), now a
fact of its own instead of a line inside a recursion. It is the term form of the
brief's "at the same `a` and `oa`".

**5.5 The line budget.** Section 2 alone would have been about 40 lines with its
frame, inside the brief's 30 to 60 estimate. Sections 4 to 6 add about 90 lines
of comment and 12 lines of code, and they cost 0 measurable seconds
(`final-1` is FASTER than `floor-1`, which carried the dependency build). I
judged the price zero and the value to the next brief real. If the mathematician
disagrees, Sections 4 to 6 can be deleted without touching the obligation.

## 6. What resisted, and what I did not weaken

**Nothing resisted.** No `subst`, no `transport`, no weakening, no hole in the
final form, and no restructuring under the caliber. That is itself the finding:
the identification was already definitional, and the campaign had been carrying
it as prose.

**One thing I could not close, and it was not asked.** Whether `κ-injL`'s BODY
is `fst (snd least)` is behind the `opaque` seal. See 5.2. If a later task needs
that inside the seal, it needs a row in `src/L/SquareLawClosed.lagda.md` with an
`unfolding` clause, not a probe.

## 7. For the next brief

1. **Cite this row instead of re-deriving.** The residue and the untruncation of
   `κ-injL` are the same type, by
   `agents/tasks/LJ-1-639/Probe639.agda:110-111`. `[LJ-1.623]` did this one
   level down and the campaign stopped attacking `SiteFiber` and `PairingAt` as
   two objects. This closes the same door one level up.
2. **The attack surface has a name now: 5.1.** The truncation enters at
   `src/L/Cardinal.lagda.md:66-67`, at `leastOf`'s predicate slot, and the probe
   says so as a term. The historic route at that slot is `[LJ-1.314]`: select
   the CODE, which is a proposition, and not the function
   (`archive/dev/LJ-dispatch-index.md:371`). A brief that revisits the residue
   should price THAT slot, not the injection.
3. **Do not price the residue as general choice.** See 5.3. The wide form is
   strictly more, and the residue is its restriction to `(a , κL a oa)`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED.** Two lines settle the
  history the premises rest on.
  `archive/dev/LJ-dispatch-index.md:183`:
  "| LJ-1.107 | sq at every infinite ordinal | PARTIAL: initial ordinals only | The non-initial case needs an injection the truncated least-of witness cannot give: the inject type is not a prop |"
  `archive/dev/LJ-dispatch-index.md:371`:
  "| LJ-1.314 | DD25 review of InjData's NECESSITY | SPLIT. THE RESIDUE IS NOT A NEW PRINCIPLE | Select the CODE, not the function: InjCode is a proposition, so leastOf untruncates it. Green probe |"
  The first confirms the residue's payload is not an hProp, which is why the
  truncation cannot be removed by unique choice. The second is the route note in
  section 7 item 2.
- `archive/dev/JOURNAL-archived.md`. **DECLINED.** Not used. Searched for the
  object and found only one line about a different untruncation (T31's wall,
  `:1732`). It bears on no row of this probe.
- `dev/ARCHIVE.md`. **DECLINED.** Not used. It records retired MODULES, and
  this task retires nothing and moves nothing.
- `archive/dev/JOURNAL.md`. **DECLINED.** Not read. A journal carries history,
  and this task needed two live types and their `src/` line numbers.
- `archive/dev/ORCHESTRATION.md`. **DECLINED.** Not read. It is the archived
  loop document and holds nothing about the least cardinal or the truncation.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ AND USED.** It states the
  reason behind the brief's premise 3, which Section 4 of the probe now carries
  as two `refl` rows.
  `dev/literature/truncation-and-selection.md:146`:
  "**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`"
  The sentence continues at `:147-148`: `leastOf` delivers the least INDEX
  untruncated, and a data payload does not come out. That is exactly what
  `premise-is-leastOf-InjP` records at
  `agents/tasks/LJ-1-639/Probe639.agda:158-161`.
- `dev/literature/devlin-II5.md`. **DECLINED.** Not read. This task states an
  identity between two Agda types and cites no classical source.
- `dev/literature/digest.md`. **DECLINED.** Not read. Same reason.
- `dev/literature/terms-2026-08.md`. **DECLINED.** Not read. It is a
  terminology record, and this task added no term to `dev/glossary.toml`.
- `dev/literature/fine-structure.md`. **DECLINED.** Not read. Fine structure
  bears on no row here.

## W2 (clause W2, from DD4)

**ANSWERED, and the clause is not engaged.** W2 binds the mathematics to a
generic carrier so both proofs share code. This task landed nothing in `src/`
and proved no mathematics: it records an identity between two types the tree
already carries. The generic carrier question arises at the object the residue
sits on, and that object is unchanged by this task.

The one generic thing here is deliberate and is a probe device, not a
mathematical choice: `UnTrunc` at
`agents/tasks/LJ-1-639/Probe639.agda:99-100` is generic in the family so that
Section 2's `refl` is not a tautology (see section 2, Device 1).

## SCOPE, AS LEFT

Created, all under `agents/tasks/LJ-1-639/`:

- `Probe639.agda` (207 lines), green, `EXIT=0`
- `runs/run.sh`, `runs/Floor.agda`, `runs/Control.agda`
- `runs/floor-1.out`, `runs/final-1.out`, `runs/final-2.out`, `runs/final-3.out`,
  `runs/control-1.out`
- `lj-1.639-report.md` (this file)

**`review-of-residue-identification.md` was NOT written.** That file is the
NO-GO channel and this task is GO.

Nothing under `src/` was touched. Nothing was committed. Gates run:
`scripts/gate/check-probes.py` clean, `scripts/gate/lint-agda.py` clean.
