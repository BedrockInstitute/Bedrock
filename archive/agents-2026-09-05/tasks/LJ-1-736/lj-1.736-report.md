# LJ-1.736 report: `Sat-in-carrier-lim`, the Sat value bound

(Written as a skeleton before the first Agda run and filled as the runs
landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.736
obligation: agents/tasks/LJ-1-736/Probe736.agda::Sat-in-carrier-lim
verdict: **NO-GO, STATED.** The obligation's type is stated, not
inhabited, at Probe736.agda:147-153. The D-10 truth check (brief
premise 4) prices it FALSE at the full ruled scope: the alphabet
`Formula S n` lets a constant name any `L`-set, and the atom clause of
`cond` transports that constant's global membership into `Sat`'s
extension -- a transport this probe machine-checks in both directions
(the kernel, Probe736.agda:88-135, composed from the landed
`cond∈-in/out` and `tmIs-var-in/out`, green). `closedω` routes the 730
witness shape, but no closure absorbs a constant sitting above `γ`.
`review-of-Sat-in-carrier-lim.md` carries the refutation reduction,
the corrected-scope candidates, and the honest split between what is
machine-checked and what is argued. The file is green, EXIT=0
(`runs/p-33.out`, 1.30 s, 337,625,088 B peak), under
`--cubical --safe --guardedness`, no postulate, no hole. Nothing lands
in `src/`. `Sat-in-carrier-stage` and `envSet-in-carrier-stage` are
not inhabited.

## 0. THE PREDECESSOR QUESTION

| hypothesis / input | predecessor's delivery | verdict there |
|---|---|---|
| `envSet-in-carrier-stage` | agents/tasks/LJ-1-730/Probe730.agda:116 (type, stated) | NO-GO, FALSE, machine-checked (`envSet-in-carrier-stage-false`) -- so its type is NOT taken as a hypothesis here (brief premise 1) |
| `keyS-in-carrier-lim` | agents/tasks/LJ-1-729/Probe729.agda, Section 4 | INHABITED at `closedω γ` -- the model for this probe's shape, and the contrast that isolates the defect: 729's alphabet is `⟪ fst A ⟫`, this brief's is `S` |
| `envSet-in-carrier-lim` | NO predecessor delivery (LJ-1.735's worktree carries only its brief) | none -- the brief authorizes taking it as a hypothesis; the kernel made it unnecessary, so no hypothesis of any kind stands in this probe |
| LJ-1.733 | NO-GO on the bounded fill; premises inconsistent at `ω ∈ γ` | respected: nothing here takes any `ω ∈ γ`-family bound as a hypothesis |

No predecessor verdict is contradicted. The 733 clause (a module
hypothesis taken from a predecessor is the type that predecessor
delivered) was applied and produced a stop-or-proceed decision, not a
guessed specification: the brief named the file, the statement, and
the authorized hypothesis, so the dispatch proceeded to D-10 truth
pricing, and the truth price came out FALSE.

## 1. WHAT WAS BUILT

`agents/tasks/LJ-1-736/Probe736.agda` (153 lines, 133 non-blank, raw
`.agda`; in-fence count 0, so the ratio bar cannot fire):

1. **The semantic kernel** (Probe736.agda:88-135), machine-checked.
   For `φ₀ = var 0 ∈̇ con c`, at arbitrary carrier `A`, environment
   `x` and constant `c : S`:
   - `atom-in` (:99): entry-tagged-`# 0`-in-`x` and entry-in-`c` give
     `x ⊨ cond A φ₀`;
   - `atom-out` (:120): the converse, to the truncated witness Σ;
   - `sat-atom-out` (:132): the same for members of `Sat A φ₀`, via
     the landed `Sat-mem` (src/L/Coding/Sat.lagda.md:145), the
     `envSet` conjunct carried, never decoded.
   Both directions are built ONLY from the landed readers
   `cond∈-in/out` (src/L/Coding/Sat.lagda.md:213, :217) and
   `tmIs-var-in/out` (:92, :96). The satisfaction symbol is the very
   instance Sat opens (`AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL
   isL-trans`, Probe736.agda:60-61 vs src/L/Coding/Sat.lagda.md:57-58).
2. **The obligation's type, STATED, NOT INHABITED**
   (Probe736.agda:147-153): the brief's type verbatim up to the two
   membership glyphs (V-side renamed `∈ˢᵥ`, the 725-SPLIT
   disambiguation; L-side bare). Exported at top level; no postulate;
   `--safe`.
3. **`runs/Frame736.agda`**: the floor frame (imports plus stated
   type, kernel absent), per the heavy-object rule.

Not built, and why: the full membrane reducing `⟨ Sat A φ₀ ∈ˢ LsetS γ
oγ ⟩` to "the trace is stage-definable". Its ingredients are landed
(`envSet-out`, src/L/Coding/EnvSet.lagda.md:385; `Lset-out`,
src/L/Constructible.lagda.md:346; `𝒟ₒ-intro`, :301) but the reduction
needs the environment-decode as a defining formula, and its
conclusion still needs a bad constant that no landed lemma exhibits
(a constructible real of construction stage above `γ` -- the
diagonal). The review prices that diagonal at far more than a probe
and records the reduction with citations instead.

## 2. THE FLOOR AND THE RUNS

Per the heavy-object rule the floor was priced first: p-1 is the
frame (imports plus the stated type, kernel absent) -- green at
1.23 s, 340,230,144 B, so the import cone is not the cost. p-33 is
the verdict run on the delivered bytes: green, 1.30 s,
337,625,088 B -- 15.7 percent of the 2,147,483,648-byte wide cap.
The kernel is cheap; the elaboration frame is the whole price.

Iterations, one defect fixed per run, never repeated unchanged:
p-2 to p-29 walked the kernel in -- wrong `PT.rec` arity and
witness-shape (`∣ w ∣₁ , ...` vs `∣ w , ... ∣₁`), an unimported `⊨`
(fixed by opening the same `AbsL` instance Sat opens, the Sound
pattern), unexported names (`tmIs-var-in/out`, `tmIs`), a
double-truncation from pinning `PT.rec`'s `A` to the goal, the
`⊓`-annotation needing `⟨_⟩`, the `cond∈-in/out` `{n}` implicit
needing an explicit pin AFTER the `B` argument, and -- the deep one --
unpinned `Fin`-arity metas at `tmIs`/`tmIs-var-*` sites, which Agda
reports as absurd `UnequalTerms` far from the cause. Working rules
extracted: pin the formula-family arity at every `tmIs`-site;
never pin `PT.rec`'s `A` when the decoder lambda's domain should be
inferred. p-19 shows the known runner artifact
(`time: signal: Invalid argument`, no Agda output; re-run of the same
bytes passed, the 729-documented flake). No heap wall was met.

| run | wall | peak | note |
|---|---|---|---|
| p-1 | 1.23 s | 340,230,144 B | floor frame, green |
| p-2 to p-29 | 0.25 to 16.20 s | 178 to 476 MB | one defect per run; p-24 re-checked cubical (Vec import pulled new interfaces) |
| p-19 | 0.25 s | 178 MB | runner artifact, no Agda output |
| p-30 | 1.28 s | 337,608,704 B | first green |
| p-31 | 1.23 s | 340,230,144 B | frame re-run on final imports, green |
| p-32 | 1.27 s | 337,641,472 B | green on pre-comment-fix bytes |
| p-33 (verdict) | **1.30 s** | **337,625,088 B** | **EXIT=0, green, delivered bytes** |

## 3. WHAT THE NEXT BRIEF NEEDS

1. **Rule the corrected scope first** (the review's section
   "Corrected targets"). The recommendation is the carrier-bounded
   alphabet (`⟪ fst A ⟫`, the 729 shape): it is what DefAt's second
   existential most plausibly consumes, and the proof route is the
   729 climb run over `cond`'s recursion, with subformula `Sat`-values
   at finite iterates absorbed by `closedω`. Price after ruling.
2. **If `Formula S n` must stay**, the bounded-constants hypothesis is
   the second candidate. The third (Δ₀-only) does not touch the
   defect; do not fund it.
3. **Do not re-fund**: the kernel (reuse Probe736.agda:88-135), the
   730 rank chain, the 729 climb, `relativize-correct`. A diagonal
   ("exhibit a constructible real above a given stage") is a real
   project: price it separately, only if some proof actually needs a
   machine-checked FALSE verdict rather than this review's stated one.
4. **[LJ-1.735]** should be checked against the same observation: its
   obligation (`envSet-in-carrier-lim`) is about `envSet` only, whose
   description does not quantify over formula constants, so it should
   be unaffected -- but its brief's alphabet, if any, deserves the
   same one-line look this one now got.
5. The DefAt assembly (733's target) remains blocked on the corrected
   bounds; the assembly's per-conjunct needs are unchanged from the
   733 report.

## 4. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.30 s (`runs/p-33.out`) |
| peak, verdict run | 337,625,088 B, 15.7 percent of cap |
| floor run (frame, kernel absent) | 1.23 s, 340,230,144 B (`runs/p-31.out`) |
| runs this dispatch | p-1 to p-33 (one runner artifact re-run: p-19) |
| heap wall | none |
| in-file / in-fence lines | 153 total, 133 non-blank / 0 (raw `.agda`; the ratio bar cannot fire) |
| brief estimate (W3) | 20 to 80 lines |
| caliber | `-A64m -I0 -M2g`, never set here |

The W3 estimate (20 to 80 lines) named the GO route at the brief's
alphabet. The estimate is neither met nor missed: the clause fired
before the attempt -- the type at that alphabet is FALSE, and the
kernel that prices the falsehood is 133 non-blank lines. The GO route
at the corrected alphabet is unbuilt and unpriced, per the ruling
gate.

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used. The
verdict rests on landed masters and live predecessor reports, cited
at `file:line` in the review and sections 0 to 3.

- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  history bears on dispatching, not on a formula-alphabet defect.
- archive/dev/DD-archived.md: declined, not read; the clauses this
  dispatch answers to live in the slot file and the brief.
- archive/dev/PLAN-archived.md: declined, not read; retired plans
  name no Sat-bound obligation.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  is `dev/pod/screen.toml`, and this task's record is its own runs
  directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  reports this task needed (LJ-1.729, LJ-1.730, LJ-1.733) are live
  files named by the brief and cited above.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
measurement quotes no book: every step is an in-tree lemma cited at
`file:line` in the review and sections 1 to 2.

- dev/literature/glossary-review-2026-08.md: declined, not used; a
  raw `.agda` probe and its records carry no translation surface.
- dev/literature/devlin-errata.md: declined, not used; the defect
  this dispatch measured is in-tree, not a do-not-repeat checklist
  item from the rud route.
- dev/literature/primary-sources.md: declined, not used; no primary
  source was consulted for the kernel or the reduction.
- dev/literature/BIBLIOGRAPHY.md: declined, not used; no source
  beyond the tree was consulted.
- dev/literature/rudimentary-functions.md: declined, not used; the
  rudimentary-functions survey names no `cond` atom clause and no
  environment embedding.
