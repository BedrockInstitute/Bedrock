# LJ-1.739 report: `asConst-in-carrier`, the constant-side carrier leaf

(Written as a skeleton before the first Agda run and filled as the runs
landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.739
obligation: agents/tasks/LJ-1-739/Probe739.agda::asConst-in-carrier
verdict: **GO, INHABITED.** The obligation's term stands at
Probe739.agda:110-117 (signature :110-115, body :116-117), built from
the five-line transitivity lemma `Lset-trans-set` it consumes
(:90-98, the 725-SPLIT body rebuilt at the bare membership glyph).
The file is green, EXIT=0 on the delivered bytes twice (`runs/p-3.out`
and `runs/p-4.out`, both 1.25 s wall, 349,995,008 B and 346,292,224 B
peak -- 16.3 percent of the 2,147,483,648-byte wide cap) and again on
re-dispatch after the frame's rename (`runs/p-5.out`, 1.23 s,
346,243,072 B), under `--cubical --safe --guardedness`, no postulate,
no hole. Nothing lands
in `src/`. `Sat-in-carrier-lim` is not inhabited and the wide alphabet
`Formula S n` appears nowhere in the file. One brief-literal detail
needed a recorded resolution: the named binder `(m : ⟪ fst A ⟫)` in
the brief's type has no arrow before it, which Agda rejects as a parse
error (see section 1, item 1); the Pi is unambiguous and the term
inhabits it with the brief's argument order exactly.

## 0. THE PREDECESSOR QUESTION

| hypothesis / input | predecessor's delivery | verdict there |
|---|---|---|
| the constant-side defect | [LJ-1.736] priced `Sat-in-carrier-lim` FALSE at the wide alphabet `Formula S n`, because a constant may sit above γ (agents/tasks/LJ-1-736/lj-1.736-report.md:13, :15) | respected: the wide alphabet appears nowhere here and `Sat-in-carrier-lim` is not inhabited |
| the asConst alphabet's consumption | [LJ-1.738] recorded that the bounded fill carries `Sat A (toS A ψ)` with `toS A ψ = mapFo (asConst A) ψ`, and that whether the constant-side side condition closes cheaply was UNMEASURED (agents/tasks/LJ-1-738/lj-1.738-report.md, section 3, point 2) | this dispatch is that measurement |
| the transitivity input | `Lset-trans-set` delivered at agents/tasks/LJ-1-725-SPLIT/Probe725Split.agda:71-79, from the landed `Lset-out`, `𝒟ₒ∋⊆`, `Lset-mono` | rebuilt in this probe (Probe739.agda:90-98), not imported: probes are not an import surface, and the brief's premise 3 names the technique, not a module |

One record on the brief itself: its "WHAT IS DELIVERED ALREADY" says
"`asConst` and `Lset-trans-set` in the 725-SPLIT probe". The evidence
splits that in two: `Lset-trans-set` is in the 725-SPLIT probe
(Probe725Split.agda:71), but `asConst` is a landed name of the Bridge
(src/L/Coding/Bridge.lagda.md:124-125, imported by this probe at
Probe739.agda:76 exactly as Probe738.agda:104 imports it). The probe
could not have delivered `asConst`: it lives in the Bridge's anonymous
carrier module. No consequence for the target.

No predecessor verdict is contradicted.

## 1. WHAT WAS BUILT

`agents/tasks/LJ-1-739/Probe739.agda` (117 lines, 107 non-blank, raw
`.agda`; in-fence count 0, so the ratio bar cannot fire):

1. **The glyph resolution, recorded before the term.** The brief's
   type puts `(m : ⟪ fst A ⟫)` straight after `⟨ fst A ∈ Lset γ ⟩`
   with no arrow between. Agda parses that as application and fails
   at the `⟪` (58.8, `runs/p-1.out`, 0.07 s, EXIT=42) -- a parse
   error, not a defect of the target: the same bytes are the only
   thing p-1 ran. The intended Pi is unambiguous, so the arrow moves
   before the binder (Probe739.agda:113); argument order is exactly
   the brief's (γ, oγ, A, hypothesis, m). The 738 discipline (record
   resolutions in the header) is followed at Probe739.agda:21-29.
   Two more resolutions are recorded there: `S` is the 𝒮ʟ carrier (a
   V ℓ set with an isL proof), so both memberships are the bare HITs
   `_∈_`; and `asConst A m` is the Bridge's constant embedding at the
   module parameter B := A.
2. **`Lset-trans-set`** (Probe739.agda:90-98): members of members of
   `Lset γ` lie in `Lset γ`. The 725-SPLIT body verbatim up to the
   membership glyph, from the same landed inputs -- `Lset-out`
   (src/L/Constructible.lagda.md:346-347), `𝒟ₒ∋⊆` (:323),
   `Lset-mono` (:365). The 725-SPLIT renaming `∈ˢᵥ` is not needed:
   the 𝒮ᵥ field `_∈ˢ_` is definitionally `_∈_`
   (src/V/Hierarchy.lagda.md:78-85) and 𝒮ʟ's `_∈ˢ_` is never named in
   this file.
3. **The obligation's term, INHABITED** (Probe739.agda:110-117). The
   whole content: `fst (asConst A m)` is definitionally
   `fst (DefOf.ι (fst A) m)` -- intoL pairs and asConst composes
   (src/L/Coding/Bridge.lagda.md:121-125), no opacity in the cone --
   and the Σ-component `ι` returns IS the membership proof, since
   `SM = Σ[ x ∈ S ] (x ∈ᶜ M)` with `M x = x ∈ˢ A` at 𝒮ᵥ
   (src/L/Definability.lagda.md:81-90; InnerSmall.SM,
   src/V/Smallness.lagda.md:359-360). So the member leaf is the
   projection `DefOf.ι (fst A) m .snd` (:117), lifted into `Lset γ`
   by `Lset-trans-set` from the hypothesis. No transport appears; no
   `≡` reasoning at all. `oγ` is carried unused: transitivity of
   `Lset γ` needs no ordinality.

Not built, and why: nothing. The obligation is one leaf and the leaf
is closed.

## 2. THE FLOOR AND THE RUNS

Per the heavy-object rule the floor was priced before the proof: p-2
is the frame (agents/tasks/LJ-1-739/runs/Frame739.agda.txt: imports
plus the stated types, holes under both defined names) -- green types,
ELABORATION-ONLY failure (`UnsolvedInteractionMetas` at exactly the
two holes, `runs/p-2.out`), 1.25 s, 354,729,984 B. The import cone
(the Bridge's, reached at Probe739.agda:76) is the whole price: the
proof terms added 0.00 s and 8.5 MB. No import trimming was possible
beyond the floor design -- the file consumes `asConst` and the three
`L.Constructible` lemmas and nothing else; there is no `Base.Truth`,
no `AbsL`, no `Sat`, no `EnvSet` import. ONE Agda process per run,
GHCRTS `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and never touched here. Peak RSS instrumented
(`/usr/bin/time -l`). No heap wall was met; the largest peak is 16.5
percent of cap. No run was repeated unchanged (p-1's bytes are not any
other run's bytes; p-3 and p-4 differ from p-2 by the two proof terms).

The first acceptance pass failed on the frame, not on the probe: the
harness makes every changed `.agda` under the task dir a conjunct-1
target (`scripts/pod/facts.py:521-523`), so the hole-bearing frame ran
as `runs/Frame739.agda`, exited 42 with `UnsolvedInteractionMetas`,
and conjunct 1 went red (`runs/accept-1.out`: conjunct 1 FAILED, the
probe itself rc 0 at 1.23 s). The cure is the brief's own naming rule
-- a file that cannot typecheck is named `.agda.txt`, never `.agda` --
so the frame moved to `runs/Frame739.agda.txt`, its bytes unchanged.
The target list then holds the green probe alone, re-verified p-5.

| run | wall | peak RSS (B) | note |
|---|---|---|---|
| p-1 | 0.07 s | 107,053,056 | brief-literal glyphs, parse error at `⟪` (58.8), EXIT=42 |
| p-2 | 1.25 s | 354,729,984 | floor frame, only the two interaction metas unsolved |
| p-3 | 1.25 s | 349,995,008 | first green, EXIT=0, delivered bytes |
| p-4 (verdict) | **1.25 s** | **346,292,224** | **EXIT=0, confirm, same bytes** |
| p-5 (re-dispatch) | **1.23 s** | **346,243,072** | **EXIT=0 on the delivered bytes after the frame rename** |

## 3. WHAT THE NEXT BRIEF NEEDS

1. **The leaf is closed and reusable.** Any corrected-scope Sat bound
   (the 736 review's correction 2, the shape 738's section 3 point 2
   sketched) consumes per-constant facts of exactly this form:
   `fst (asConst A m) ∈ Lset γ` from `fst A ∈ Lset γ`. The per-
   constant ingredient costs 2 lines (Probe739.agda:116-117) plus the
   8-line transitivity lemma. The SAT-side bound itself remains
   FALSE at the wide scope (736) and UNRULED at any corrected scope;
   this leaf does not change that, and the wide scope must not be
   re-funded.
2. **Do not import probes.** `Lset-trans-set` is rebuilt here at the
   bare glyph. If a master ever needs it in `src/`, the landed inputs
   (`Lset-out`, `𝒟ₒ∋⊆`, `Lset-mono`, all in
   src/L/Constructible.lagda.md) are its whole content -- 8 lines,
   no new measurement.
3. **The conversion is definitional.** `fst (asConst A m)` ≡
   `fst (DefOf.ι (fst A) m)` needs no transport; a master stating
   this leaf can take the proof from `DefOf.ι`'s Σ-component
   directly, as here.
4. **`oγ` is dead weight for transitivity facts.** Sibling
   carrier-bound obligations that only need stage transitivity can
   drop the ordinal hypothesis unless a downstream consumer needs it;
   it is unused at Probe739.agda:115.
5. **A hole-bearing floor frame is `.agda.txt`, not `.agda`.** The
   acceptance harness typechecks every changed `.agda` under the task
   dir (`scripts/pod/facts.py:521-523`), so a frame left as `.agda`
   with holes fails conjunct 1 for ever; this dispatch paid that
   acceptance pass (section 2). Name it `.agda.txt` from birth, per
   the brief's naming rule, and only the probe itself is a target.

## 4. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.23 s (`runs/p-5.out`) |
| peak, verdict run | 346,243,072 B, 16.1 percent of cap |
| floor run (frame, proofs absent) | 1.25 s, 354,729,984 B (`runs/p-2.out`) |
| runs this dispatch | p-1 to p-4, plus p-5 on re-dispatch |
| heap wall | none |
| in-file / in-fence lines | 117 total, 107 non-blank / 0 (raw `.agda`; the ratio bar cannot fire) |
| brief estimate (W3) | 10 to 40 lines |
| caliber | `-A64m -I0 -M2g`, never set here |

The W3 estimate (10 to 40 lines) is met on the route it named: the
obligation's own definition is 7 non-blank lines (signature
Probe739.agda:110-114, body :115-117), and the transitivity lemma it
feeds on adds 8. The rest of the file is the header record and the
imports the Bridge cone forces.

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used. The
verdict rests on landed masters and live predecessor reports, cited
at `file:line` in the HEAD and sections 0 to 3.

- archive/dev/DD-archived.md: declined, not read; the clauses this
  dispatch answers to live in `dev/pod/instructions/coder.md` and the
  brief, and no retired design doc names a constant-embedding bound.
- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  history bears on dispatching, not on a membership leaf.
- archive/dev/PLAN-archived.md: declined, not read; retired plans
  name no `asConst` obligation.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  is `dev/pod/screen.toml`, and this task's record is its own runs
  directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  reports this task needed (LJ-1.736, LJ-1.738, LJ-1.725-SPLIT) are
  live files named by the brief and cited above.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
measurement quotes no book: every step is an in-tree lemma cited at
`file:line` in the HEAD and sections 1 to 2.

- dev/literature/glossary-review-2026-08.md: declined, not used; a
  raw `.agda` probe and its records carry no translation surface.
- dev/literature/primary-sources.md: declined, not used; no primary
  source was consulted for the term or its transitivity lemma.
- dev/literature/devlin-errata.md: declined, not used; the route runs
  on in-tree lemmas, not on the rud-route checklist.
- dev/literature/level-formula-slot-roles.md: declined, not used; the
  obligation names no formula slots and no level roles.
- dev/literature/BIBLIOGRAPHY.md: declined, not used; no source
  beyond the tree was consulted.
