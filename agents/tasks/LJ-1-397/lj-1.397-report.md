# LJ-1.397 report: the ordinal-least coded cardinal, and the arrow as data

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote only
in `agents/tasks/LJ-1-397/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time, no heap
event.

TARGET: build TWO terms in `agents/tasks/LJ-1-397/Probe397.agda`, at a
GENERIC ordinal: `coded-least`, the mirror of `LeastCardInjL` with the CODED
predicate, and `coded-arrow`, the arrow as data below a site where the
internal cardinal fails.

## VERDICT

**GO on both obligations.** `coded-least` and `coded-arrow` are GREEN at
`agents/tasks/LJ-1-397/Probe397.agda`, exit 0, and both resolve through the
witness meter (section 6). The two terms sit at floor price.

**Two deviations from the brief's stated types, and both are reported, not
hidden.** The brief's `coded-least` input carried the identity code at target
`up a δ`; the identity code has source and target both `a`, so I delivered the
input at target `a` (section 2). And the W3 probe `code-lands` failed, so
`coded-arrow` is delivered under the REPAIRED hypothesis, the Mem form
(section 4). The brief's W3 note authorises both.

**The W3 finding, in one sentence.** `code-lands`, the one implication from
the `S` form of the code quantifier to the `Mem` form, reduces to a single
placement obligation `⟨ fst F ∈ Lset (SiteBound.β a) ⟩` from `InjCode F a c`,
and nothing delivered pays that placement; it is the residue [LJ-1.386]
marked unbuilt ("bookkeeping about stages", section 2 of that report).

## 1. THE STATEMENTS, AS THE TREE TAKES THEM

Both terms are stated at a generic L-element `a` with its ordinal certificate
`oa : IsOrd (fst a)`. No ordinal, no site and no numeral is named in any
statement.

`coded-least` at `Probe397.agda:87-96` is the mirror of `LeastCardInjL`
(`src/L/Cardinal.lagda.md:60-155`), with the ambient predicate `InjP'`
replaced by the coded predicate `CodeP'` (`Probe397.agda:115-116`): a tower
member `m` satisfies it when its lift `upT m` receives a code from
`Mem (Lset (SiteBound.β a))`. The well-order `w` is SEALED exactly as the
delivered module seals it (`Probe397.agda:119-121`, `opaque`), and `w-lt` is
the one read the seal needs (`Probe397.agda:123-127`). The nonempty witness is
the identity code at `a`, carried at the tower member `self` whose lift is `a`
(`Probe397.agda:129-144`).

`coded-arrow` at `Probe397.agda:224-282` is three steps: step 1 reads a member
of `fst a` with a Mem-code out of the failure by `lem`; step 2 runs
`coded-least` fed by the identity code and refutes `fst b ≡ fst a` against
that member; step 3 applies the door at source `a` and target `b`.

The door and the identity code are HYPOTHESES, not imports. `Door` and
`IdCode` at `Probe397.agda:215-222` spell the statements `code-untruncates`
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`) and the identity code
`InjCode G D D` generalised to a generic `a`
(`agents/tasks/LJ-1-386/Probe386.agda:186-187`). The brief names
`code-exists` (`Probe386.agda:227-230`), which is `Canonical.Good` at one
site; the nonempty this mirror consumes is the stronger four-conjunct
identity. `coded-arrow` takes both as leading arguments (`Probe397.agda:224`).
Their types live in `lem`-taking modules and cannot sit in the preamble, so
they cannot be parameters of the outer module without breaking the witness
meter (section 4.7.2 of the program: the derivation copies only the lines
above the header). This is the same constraint `[LJ-1.395]` recorded
(`agents/tasks/LJ-1-395/lj-1.395-report.md:44-56`); that return unfolded the
notions, and this return takes the two statements as arguments of the term
that consumes them.

## 2. THE DEVIATION IN `coded-least`: THE IDENTITY CODE TARGETS `a`, NOT `up a δ`

The brief's obligation writes the input as

    ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β a)) ]
          InjCode (SiteBound.up a δ) a (SiteBound.up a δ) ∥₁

and calls this "the identity code". It is not. `InjCode F a b` reads "`F`
codes an injection `a ↪ b`", so the brief's input reads "`δ` codes `a ↪ δ`":
the code is `δ` and the target is `δ` itself. The identity code of
`IdGraph.idCode` (`agents/tasks/LJ-1-386/Probe386.agda:186-187`) is
`InjCode G D D`, source `D` and target `D` both the ordinal. Its 4th conjunct
`ran` (`Probe386.agda:180-183`) lands values in `D`, not in the graph `G`.

The input the mirror needs is the identity code at target `a` itself:

    ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
          InjCode (SiteBound.up a F) a a ∥₁

That is what `Probe397.agda:87-89` states, and it is the statement the
selection's nonempty witness consumes (`Probe397.agda:138-144`): the identity
code at `a` gives `a` itself as a tower member receiving a code, so the least
selection runs at every ordinal. **The third argument of the brief's input was
`up a δ`; I delivered `a`.** The shape of the conclusion is untouched.

## 3. THE MIRROR, LINE BY LINE

`coded-least` copies `LeastCardInjL`'s structure verbatim, with the ambient
predicate swapped for the coded one:

| delivered (`src/L/Cardinal.lagda.md`) | mirrored (`Probe397.agda`) |
|---|---|
| `InjP γ = ∥ ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫ ∥₁` | `CodeP γ = ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (upβ F) a γ ∥₁` |
| `up : ⟪ sucV (fst α) ⟫ → S` | `upT : ⟪ sucV (fst a) ⟫ → S` |
| `w = ordSWO (sucV (fst α)) (suc-ord oα)`, sealed | `w = ordSWO (sucV (fst a)) (suc-ord oa)`, sealed |
| `w-lt`, the one read | `w-lt`, identical |
| `nonempty` via `idInj` | `nonempty'` via the identity code |
| `least = leastOf w lem InjP' nonempty` | `least = leastOf w lem CodeP' nonempty'` |
| `κ-inj`, truncated, "not an hProp" | `κ-code`, truncated, and now a proposition |
| `κ-min-at` | `κ-min-at`, identical shape |

Two differences are forced by the coded predicate and both are where the
mirror earns its name. The witness `κ-code` (`Probe397.agda:159-160`) is a
PROPOSITION (`squash₁`), unlike the ambient `κ-inj` which the chapter marks
"still truncated, still not an hProp" (`src/L/Cardinal.lagda.md:132`); that is
what lets the door read it out as data in `coded-arrow` step 3. And the
minimality clause quantifies over `Mem (Lset β)` codes (`Probe397.agda:166-185`),
so its conclusion is `Empty.⊥`, which is what lets step 2 spend it against the
member from step 1 without untruncating anything.

The seal and the `w-lt` read are copied exactly because the delivered module's
comment names the cost of leaving them out (`src/L/Cardinal.lagda.md:85-89`):
the well-order is sealed so `γ-card` and `fst κ` never re-unfold, and `w-lt`
is the one read the seal needs. R-36's discipline transfers because the shape
is the same shape.

## 4. W3: `code-lands`, THE WIDEST UNMEASURED TERM, AND THE REPAIRED HYPOTHESIS

`IsCardinalL` quantifies the code over all of `S`
(`src/L/Cardinal.lagda.md:232-233`) and `coded-least`'s predicate quantifies
it over `Mem (Lset (SiteBound.β a))`. The probe `code-lands` is the one
implication from the `S` form to the `Mem` form. I stated it alone and ran it
FIRST, before treating the two obligations as closed, in
`agents/tasks/LJ-1-397/CodeLands.agda`.

**The hole run: NO-GO.** With the placement step left as `{!!}`, the file's
only error is that unsolved meta, exit 42, error class
`UnsolvedInteractionMetas`, at the placement line. Evidence:
`agents/tasks/LJ-1-397/runs/code-lands-hole.out`. The hole file was deleted
after the run, so it is not a deliverable and it will not sit in the
acceptance set.

**The reduction.** The whole implication reduces to one step, the placement
`⟨ fst F ∈ Lset (SiteBound.β a) ⟩` from `InjCode F a c`. Given the
placement, the rest of `code-lands` is free: the proof-irrelevance of the
`isL` certificate, a transport of the code along `Σ≡Prop`
(`CodeLands.agda:53-62`). So `CodeLands.agda` is delivered GREEN, with the
placement named as the hypothesis `Placement` (`CodeLands.agda:40-41`) and
`code-lands` stated conditional on it (`CodeLands.agda:46-49`). The residue is
named, and it is exactly what [LJ-1.386] marked unbuilt: a code `F` for
`a ↪ c` is a graph over members of `a`, and nothing delivered places it inside
`Lset (SiteBound.β a)` (that report, section 2, "bookkeeping about stages").

**D-10, the truth of the residue.** I did not refute `Placement` and I did
not prove it. `InjCode F a c` names no stage bound on `F`, so an arbitrary
code is not forced into `Lset (SiteBound.β a)`. `bound-below₂`
(`src/L/Choice/Stage.lagda.md:370-373`) places a member of a member of `a`,
and a graph is not that. [LJ-1.386] discharged the identity graph only by
taking the site to be the graph itself (`Probe386.agda:224-229`). That is
why `IdCode` stays a hypothesis: the identity at generic `a`, placed in
`Lset (SiteBound.β a)`, is not delivered.

**The repaired hypothesis, and why it is the finding.** Because `code-lands`
is the residue, `coded-arrow` is delivered under the Mem form of the failure.
The hypothesis is `IsCardinalL-Mem a → Empty.⊥`, where
`IsCardinalL-Mem` (`Probe397.agda:193-197`) is `IsCardinalL`'s shape with the
code quantifier replaced by `Σ[ F ∈ Mem (Lset (SiteBound.β κ)) ]`. Step 1 then
reads a member of `a` with a Mem-code directly out of the failure
(`Probe397.agda:258-271`), and no `code-lands` step sits anywhere. The brief
prices this: "A task that delivers the arrow under a repaired hypothesis is a
GO, and the repaired hypothesis is the finding." The GO is delivered; the
finding is `Placement`, priced below.

`IsCardinalL` (no S-code) always implies `IsCardinalL-Mem` (no Mem-code),
because a Mem-code is an S-code via `SiteBound.up`. The converse is
`code-lands`. So the repaired hypothesis `¬ IsCardinalL-Mem` is strictly
stronger than the brief's `¬ IsCardinalL`. That is the price of the repair.

**The price of the residue.** `Placement` is the placement of a code in
`Lset (SiteBound.β a)`. [LJ-1.386] priced the same residue at the intended
site `a := D` as "bookkeeping about stages, not cardinal arithmetic" and did
not build it (`agents/tasks/LJ-1-386/lj-1.386-report.md`, section 2). I do
not re-price it; there is no delivered comparable, and P-l forbids the
transfer. It is now the campaign's named bill on the coded side, exactly the
bill the brief's NO-GO clause said a failure would earn.

## 5. W2 AND DD4: WRITE IT GENERIC

Both terms are generic in `a`, and nothing names a site, a stage or a numeral.
The module `LJ-1-397.Probe397` takes only `ℓ` and `lem`; `coded-least` is at
generic `a oa`, `coded-arrow` at generic `a oa` with its hypotheses `door` and
`id-code` also generic in their parameters. The identity code and the door are
taken at a generic `a`, not at `[LJ-1.386]`'s site `+ω ω`. W2 answered.

## 6. RUNS, FLOOR, SLOTS

All runs on 2026-08-20, from the repository root,
`agda --safe agents/tasks/LJ-1-397/<file>.agda`, `GHCRTS="-A64m -I0 -M8g"`
(the program's pane caliber, never changed by me), ONE Agda process at a time.
Three consecutive walls each, warm interface cache.

| row | contents | 3 consecutive walls | median |
|---|---|---|---|
| 1 | `Floor397.agda`, imports only, no term | 1.67 / 1.59 / 1.62 | **1.62 s** |
| 2 | `Probe397.agda`, both obligations | 1.62 / 1.60 / 1.58 | **1.60 s** |
| 3 | `CodeLands.agda`, the W3 residue, green | 1.73 / 1.74 / 1.68 | **1.73 s** |

**WHAT THE TABLE SAYS.** Both obligations and the W3 residue sit inside the
floor's own spread; the whole file is FREE at this site. The brief estimated
about 70 code lines against `LeastCardInjL` at 95 lines including its
comments (`src/L/Cardinal.lagda.md:60-155`). The two obligations delivered are
137 code lines (`Probe397.agda:87-185` for `coded-least`, `:193-282` for
`IsCardinalL-Mem`, `Door`, `IdCode` and `coded-arrow`, comments and blanks
excluded), over the estimate, and they cost no time at all. The overage is
spelling, not mathematics: the coded predicate `Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
InjCode (SiteBound.up a F) a γ` is a longer spelling than the ambient
`⟪ fst α ⟫ ↪ ⟪ fst γ ⟫` of `LeastCardInjL`, and `coded-arrow`'s three steps
are a full assembly the estimate did not itemise. The mirror itself is
line-for-line the delivered module's shape. `Probe397.agda` checks
green (exit 0), and the witness meter resolves both obligation names
(`scripts/pod/witness.py --brief agents/tasks/LJ-1-397/LJ-1.397.md --code LJ-1.397`,
"0 UNRESOLVED of 2", 1.78 s, probe_red=False). The hole run of `code-lands`
(exit 42, the placement step) is `runs/code-lands-hole.out`.

## 7. WHAT GO EARNED

A GO on `coded-least` and `coded-arrow` pays the bill `[LJ-1.395]` named
(`agents/tasks/LJ-1-395/lj-1.395-report.md:205-210`), on the coded side,
conditional on the repaired hypothesis. That report's next bill is the
untruncated arrow at a negative site; [LJ-1.394] measured that nothing
produces it on the AMBIENT side (`agents/tasks/LJ-1-394/lj-1.394-report.md:36-39`).
On the coded side the arrow IS produced, by `coded-least` plus the door, and
the one unpaid step is the named residue `Placement`. The repaired hypothesis
is the type the next brief takes; the campaign's next bill on this side is
`Placement`.

## 8. ARCHIVE USED

- `archive/dev/JOURNAL-archived.md:1732`. **BEARS, as the wall my door does
  not move.** The line reads "The untruncated equivalence remains unavailable
  (T31's wall)". The door returns an INJECTION, not an equivalence, so T31's
  wall stands after this measurement; `coded-least`'s witness stays a
  proposition and the door reads it out as an injection, nothing wider.
- `archive/dev/TASKS-archived.md:82`. **BEARS, as the nearest recorded shape.**
  The row reads "Truncated square law at initial ordinals" and its verdict is
  DELIVERED. The retired route's square law was truncated; the coded door is
  the shape that untruncates a witness, at an injection and not a bijection,
  so the two walls do not collide.
- `archive/dev/DECISIONS-archived.md:44`. **BEARS, as this task's own funding
  rule.** The row is D22, "Every block is gated before it is funded", whose
  text makes the paired probe "not caution but arithmetic". The W3 probe
  `code-lands` is exactly D22's arithmetic here: it named the widest term,
  ran it first, and the band the probe left is the repaired hypothesis.
- `dev/ARCHIVE.md`. **Declined.** I read its archive-path rules
  (`:30-40`) and searched it for `least`, `cardinal`, `truncat`, `select`,
  `injection` and `InjCode`. The registry records where retired modules live
  and their revival conditions; no entry names the coded-carrier selection or
  the placement residue, so nothing in it bears on this task.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`. **Declined.**
  The condensation crossing: recognition of a collapsed elementary
  substructure as a level. A grep for `truncat`, `select` and `inject`
  returns one hit, a where-function comment, not a selection device and not
  a placement of a code in `Lset β`.

## 9. LITERATURE USED

- `dev/literature/truncation-and-selection.md:147`. **BEARS, and it is the
  decisive entry.** The line reads "delivers the least INDEX untruncated, and
  any payload it delivers with the". `coded-least` sits exactly inside that
  constraint: the least ordinal `b` comes out as data (the index), the code
  witness stays a proposition (the payload), and the door is what reads the
  witness out. The same line bounds the door: a data payload beside the index
  does not come out of `leastOf`.
- `dev/literature/truncation-and-selection.md:95`. **BEARS, as the free case
  the door spends.** The line reads "This is the only free case." The door's
  two untruncations are the code (by `leastOf` under `lem`) and the value at
  a member (by unique choice inside `Small`); both are the free case, so the
  route adds no axiom beyond `lem`.
- `dev/literature/devlin-II5.md`. **Declined.** The condensation lemma and
  the GCH in L. A grep for `truncat`, `select` and `inject` gives no hit on a
  selection device or a coded carrier; the cardinal lines are cardinal
  arithmetic in the hull, not this task's selection.
- `dev/literature/terms-2026-08.md`. **Declined.** The translation-terms
  dossier. Its "cardinal" entry at `:364` is a rendering of the word, not a
  statement about the selection device; nothing in it bears on the
  ordinal-least coded selection.
- `dev/literature/geology.md`. **Declined.** Set-theoretic geology sources
  (mantles, grounds). Not this subject.
- `dev/literature/digest.md`. **Declined.** The orthodox form of the rud
  route. This task measured a tree device at a tree site, and the form of the
  route is not what the mirror turns on.

## WHAT I DID NOT DO

- I did not import `[LJ-1.386]`'s probe; the door and the identity code are
  hypotheses with the statements their report gives.
- I did not touch `src/`; `src/` is forbidden for a probe.
- I did not weaken `coded-least`'s conclusion and I added no postulate.
- I did not deliver `coded-arrow` under the original `IsCardinalL` hypothesis
  with a `code-lands` postulate; the brief's W3 note rules the repaired Mem
  form, and that is what I delivered.
- I did not run `make check`; no file outside this task's directory changed,
  and the probes are not in `src/`.
- I did not set `GHCRTS`. W4 does not apply: no module was retired.

## GATES RUN ON MY FILES

`agda --safe agents/tasks/LJ-1-397/Probe397.agda` exits 0 and
`agda --safe agents/tasks/LJ-1-397/CodeLands.agda` exits 0;
`agda --safe agents/tasks/LJ-1-397/Floor397.agda` exits 0. The witness meter
resolves both obligations ("0 UNRESOLVED of 2", 1.78 s). `lint-agda.py --check`
on `Probe397.agda` is clean. `scripts/pod/check-survey-quotes.py LJ-1.397`
is clean.
