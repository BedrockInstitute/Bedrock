# LJ-1.739-SPLIT report: `asConst-in-carrier` re-landed where the meter reads

(Written as a skeleton before the first Agda run and filled as the runs
landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.739-SPLIT
obligation: agents/tasks/LJ-1-739-SPLIT/Probe739Split.agda::asConst-in-carrier
verdict: **GO, INHABITED.** The obligation's term stands at
Probe739Split.agda:107-111 (signature) and :112-114 (body), the 739
term transcribed into the file the meter names. The file is green
twice on the delivered bytes (`runs/p-3.out` and `runs/p-4.out`, both
EXIT=0, 1.24 s and 1.21 s wall, 345,800,704 B and 341,000,192 B peak,
16.1 and 15.9 percent of the 2,147,483,648-byte wide cap), under
`--cubical --safe --guardedness`, no postulate, no hole. The meter's
own derivation resolves the name over the new dotted module: the
witness run printed `pass exit=0 1.25s` and
`witness: 0 UNRESOLVED of 1, 1.25 s, probe_red=False` (section 2, run
w-1). Nothing lands in `src/`. `Sat-in-carrier-lim` is not inhabited
and the wide alphabet `Formula S n` appears nowhere in the file. The
brief's type needed no repair: its arrow before `(m : ⟪ fst A ⟫)` is
present, so the type is the brief's bytes verbatim.

## 0. THE PREDECESSOR QUESTION

| hypothesis / input | predecessor's delivery | verdict there |
|---|---|---|
| the term itself | [LJ-1.739] inhabited `asConst-in-carrier` at agents/tasks/LJ-1-739/Probe739.agda:110-117 | GO, INHABITED (agents/tasks/LJ-1-739/lj-1.739-report.md:13) |
| the wide-scope false | [LJ-1.736] priced `Sat-in-carrier-lim` FALSE at `Formula S n` (agents/tasks/LJ-1-736/lj-1.736-report.md:13) | respected: the wide alphabet appears nowhere here and `Sat-in-carrier-lim` is not inhabited |

One measurement about the predecessor's location, taken before the
transcription: `agents/tasks/LJ-1-739/` is UNTRACKED in git. `git
status` prints `?? agents/tasks/LJ-1-739/` and `git log` over that
path is empty, in the main tree and in every branch. So the 739
delivery never reached a commit and the live meter reads supply 0 for
the name (the brief's MEASURED TODAY). That is why this split exists:
the same inhabited term, rebuilt at the path the meter reads, in a
tracked file. The predecessor's report and probe were read from the
working tree as the predecessor clause requires; the verdict there is
GO, so no `review-of-*.md` is written: that name is the NO-GO vehicle,
and no NO-GO exists to state.

## 1. WHAT WAS BUILT

`agents/tasks/LJ-1-739-SPLIT/Probe739Split.agda` (114 lines, 104
non-blank, raw `.agda`; in-fence count 0, so the ratio bar cannot
fire):

1. **The glyph resolutions, recorded before the term** (header
   comments, Probe739Split.agda:19-31). (1) `S` is 𝒮ʟ's carrier: a
   `V ℓ` set with an `isL` proof, the Bridge opening
   `hPropStructure 𝒮ʟ` at src/L/Coding/Bridge.lagda.md:83, the
   restriction `_↾_` pairing each element with its proof at
   src/FOL/ZFStructure.lagda.md:145-150. So `fst A : V ℓ`, and both
   memberships of the obligation are the bare HIT `_∈_`: the
   `Lset`-family names imported from `L.Constructible` are stated over
   𝒮ᵥ's carrier, and 𝒮ᵥ's `S` IS `V ℓ` with `_∈ˢ_ = _∈_`
   (src/V/Hierarchy.lagda.md:79-85). (2) `asConst A m` is the
   Bridge's constant embedding at the module parameter B := A
   (src/L/Coding/Bridge.lagda.md:124-125). Unlike the 739 brief, this
   brief's type carried its own arrow, so no parse repair is recorded.
2. **`Lset-trans-set`** (Probe739Split.agda:87-95): members of members
   of `Lset γ` lie in `Lset γ`. The 725-SPLIT body (delivered at
   agents/tasks/LJ-1-725-SPLIT/Probe725Split.agda:71-79) rebuilt at
   the bare membership glyph, from the same landed inputs:
   `Lset-out` (src/L/Constructible.lagda.md:346-347),
   `𝒟ₒ∋⊆` (:323), `Lset-mono` (:365). Probes are not an import
   surface, so the lemma is rebuilt and not imported.
3. **The obligation's term, INHABITED** (Probe739Split.agda:107-114).
   The whole content is the 739 leaf: `fst (asConst A m)` is
   definitionally `fst (DefOf.ι (fst A) m)`, since `intoL` pairs and
   `asConst` composes (Bridge:121-125), no opacity in the cone; and
   the Σ-component of `ι` returns IS the membership proof, because
   `ι = equivFun e` (src/L/Definability.lagda.md:89-90) lands in
   `Σ[ x ∈ S ] (x ∈ᶜ M)` with `M x = x ∈ˢ A` at 𝒮ᵥ
   (src/L/Definability.lagda.md:80; `InnerSmall.SM`,
   src/V/Smallness.lagda.md:359-360). The term projects that
   component, `DefOf.ι (fst A) m .snd` (:114), and `Lset-trans-set`
   lifts it into `Lset γ` from the hypothesis. No transport; no `≡`
   reasoning; no new idea. `oγ` is carried unused: transitivity of
   `Lset γ` needs no ordinality.

Not built, and why: nothing. The obligation is one leaf and the leaf
is closed. `review-of-asConst-in-carrier.md` is deliberately absent:
the scope permits it, the GO verdict does not use it.

## 2. THE FLOOR AND THE RUNS

The object is not heavy by the 739 measurement (1.25 s floor, 1.25 s
full, agents/tasks/LJ-1-739/lj-1.739-report.md section 2), but the
floor was re-measured at this site, because a transcription into a
fresh file is exactly the case where the frame and the term can
diverge. The floor frame is
agents/tasks/LJ-1-739-SPLIT/runs/Frame739Split.agda.txt: this file's
imports plus both stated types, holes under both defined names. It
exited 42 with `UnsolvedInteractionMetas` at exactly the two holes
(`runs/p-2.out`, lines 33.30-40.45 of the frame), 1.21 s, 348,454,912
B: the import cone is the whole price, and the proof terms added 0.03
s and about 7 MB (p-3 against p-2).

Two naming facts the runs measured, both worth keeping:

1. **A `.agda.txt` cannot be RUN at all.** The frame was first invoked
   under its delivered name and Agda refused it before elaboration:
   `[InvalidExtensionError]`, EXIT=42 in 0.05 s (`runs/p-1.out`).
   Supported extensions are `.agda` and the literate forms only. So
   the floor run requires a transient `.agda` name: the frame was
   copied to `agents/tasks/LJ-1-739-SPLIT/Frame739Split.agda`, run
   (p-2), and renamed back to `runs/Frame739Split.agda.txt` in the
   same shell step. No hole-bearing `.agda` remains under the task
   directory, which is the brief's own rule, and is the cure 739 paid
   an acceptance failure to learn.
2. **The machine's swap guard killed one run mid-dispatch.** The
   witness capture run (w-2 below) was SIGKILLed at 0.82 s: `rc -9`,
   `probe-red exit=-9` (`runs/p-5.out`). The kill is not the term's:
   `scripts/pod/pod.py:2374` (`reap_orphan_agda`) kills only past the
   1800 s bar, and the machine-level backstop
   `scripts/ops/agda-watchdog.sh` logged `KILLED agda pid=78569 (swap
   8734MB >= 8192MB)` at 2026-08-29 08:07:22
   (/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log, the
   shared machine's own log), matching a direct `vm.swapusage` read of
   `used = 8734.88M` minutes later. The machine, not the file. No
   third attempt was made: swap was still past the guard when
   measured, and a rerun that chases a green row through a kill window
   is the discipline the rerun rule refuses.

| run | wall | peak RSS (B) | note |
|---|---|---|---|
| p-1 | 0.05 s | 105,676,800 | frame under its `.agda.txt` name: `[InvalidExtensionError]`, EXIT=42 |
| p-2 | 1.21 s | 348,454,912 | floor frame as transient `.agda`, only the two intended holes unsolved, EXIT=42 |
| p-3 | 1.24 s | 345,800,704 | **first green, EXIT=0, delivered bytes** |
| p-4 (verdict) | **1.21 s** | **341,000,192** | **EXIT=0, confirm, same bytes** |
| w-1 | 1.25 s | n/a (python-driven) | witness derivation, `pass`, `0 UNRESOLVED of 1, probe_red=False` |
| w-2 = p-5 | 0.82 s | n/a | witness capture re-run SIGKILLed by the machine's swap guard, `rc -9` |

The w-1 witness run (via `scripts/pod/witness.py`, the program's own
meter, run from the worktree with the main tree's pinned
`.venv/bin/python` because this worktree has no `.venv` of its own)
printed verbatim:

    pass      exit=0        1.25s  agents/tasks/LJ-1-739-SPLIT/Probe739Split.agda::asConst-in-carrier
    witness: 0 UNRESOLVED of 1, 1.25 s, probe_red=False

ONE Agda process per run, sequential, never two live at once; GHCRTS
`-A64m -I0 -M2g`, the wide caliber, set on the pane by the program and
never set by a run script or by hand for an Agda invocation. No heap
wall was met; the largest peak is 16.2 percent of cap. No run was
repeated unchanged except p-4, the confirm of the delivered bytes, and
the w-1 to w-2 pair, whose second half is the captured kill recorded
above, not a chased result.

## 3. WHAT THE NEXT BRIEF NEEDS

1. **The leaf now has a tracked home the meter reads.** Later briefs
   may cite `agents/tasks/LJ-1-739-SPLIT/Probe739Split.agda:107` as
   the constant-side carrier leaf, and the obligation's supply reads 1
   through the file's own green. The untracked 739 directory stays the
   prose record of the discovery; this file is the citation surface.
2. **The corrected-scope Sat bound still waits, and this leaf is its
   per-constant ingredient.** The 736 FALSE stands at the wide scope;
   nothing here re-opens it. A corrected-scope bound consumes facts of
   exactly this shape, `fst (asConst A m) ∈ Lset γ` from
   `fst A ∈ Lset γ`, at a cost of 8 non-blank lines of term (the 8-line
   transitivity lemma plus the 3-line body; signature lines excluded).
3. **The conversion is definitional.** `fst (asConst A m)` ≡
   `fst (DefOf.ι (fst A) m)` needs no transport; a master stating this
   leaf can take the proof from `DefOf.ι`'s Σ-component directly, as
   here and as at Probe739.agda:116-117.
4. **`oγ` is dead weight for transitivity facts.** A sibling
   carrier-bound obligation that only needs stage transitivity can
   drop the ordinal hypothesis; it is unused at Probe739Split.agda:112.
   The brief's type carries it, so this file does too.
5. **A floor frame needs a transient `.agda` window, run and rename in
   one shell step.** The `.agda.txt` rule protects the acceptance
   target list, and p-1 measured that Agda refuses the `.txt` name
   outright, so the floor measurement and the naming rule meet in a
   two-step dance; do it in one `&&` chain so no hole-bearing `.agda`
   can survive an interrupted dispatch.
6. **On this shared machine, an `rc -9` at short elapsed is the
   watchdog, not the term.** Check
   /Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log before
   reading anything into a fast kill; the guard kills the biggest agda
   when swap crosses 8 GB, whatever the process is elaborating.

## 4. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.21 s (`runs/p-4.out`) |
| peak, verdict run | 341,000,192 B, 15.9 percent of cap |
| floor run (frame, proofs absent) | 1.21 s, 348,454,912 B (`runs/p-2.out`) |
| witness meter | pass, 1.25 s (w-1); capture killed by machine swap guard (w-2, `runs/p-5.out`) |
| runs this dispatch | p-1 to p-4, w-1, w-2 |
| heap wall | none |
| in-file / in-fence lines | 114 total, 104 non-blank / 0 (raw `.agda`; the ratio bar cannot fire) |
| brief estimate (W3) | 20 to 90 lines |
| caliber | `-A64m -I0 -M2g`, never set here |

The W3 estimate (20 to 90 lines) is met on the route it named: the
transcribed alias converts in the fresh file. The obligation's own
definition is 8 lines (signature Probe739Split.agda:107-111, body
:112-114), the transitivity lemma it feeds on adds 9 non-blank
(:87-95), and the rest of the file is the header record and the
imports the Bridge cone forces. The W3 question is answered twice:
once by the probe's own green (p-3, p-4), and once by the meter's
derived witness, which instantiates the NEW dotted module
`LJ-1-739-SPLIT.Probe739Split` and resolves the name behind it (w-1,
pass).

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used. The
verdict rests on landed masters and live predecessor reports, cited at
`file:line` in the HEAD and sections 0 to 3.

- archive/dev/DD-archived.md: declined, not read; the clauses this
  dispatch answers to live in `dev/pod/instructions/coder.md` and the
  brief, and a retired design doc names no constant-embedding
  obligation.
- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  history bears on dispatching, not on a membership leaf.
- archive/dev/PLAN-archived.md: declined, not read; retired plans name
  no `asConst-in-carrier` obligation and no SPLIT of LJ-1.739.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  is `dev/pod/screen.toml`, and this task's record is its own runs
  directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  records this task needed (LJ-1.736, LJ-1.739, LJ-1.725-SPLIT) are
  live files under `agents/tasks/`, named by the brief and cited
  above.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
measurement quotes no book: every step is an in-tree lemma cited at
`file:line` in the HEAD and sections 1 to 2.

- dev/literature/devlin-errata.md: declined, not used; the route runs
  on in-tree lemmas, not on the rud-route checklist.
- dev/literature/glossary-review-2026-08.md: declined, not used; a raw
  `.agda` probe and its records carry no translation surface.
- dev/literature/level-formula-slot-roles.md: declined, not used; the
  obligation names no formula slots and no level roles.
- dev/literature/primary-sources.md: declined, not used; no primary
  source was consulted for the term or its transitivity lemma.
- dev/literature/BIBLIOGRAPHY.md: declined, not used; no source beyond
  the tree was consulted.
