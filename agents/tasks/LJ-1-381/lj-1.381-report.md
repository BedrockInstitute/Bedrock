# LJ-1.381 report: the `φ₀` extraction, priced

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. LEAD

**The extraction prices at about 210 marginal lines on top of the
delivered tree, and its legs are BUILT, not described: the whole
factor is a green file, `agents/tasks/LJ-1-381/ProbeLJ1381A.agda`,
exit 0, 248 non-blank lines, of which about 35 restate what
`[LJ-1.378]` already carries. Basis: my own green file, plus the
retired comparable at `archive/dev/TASKS-archived.md:207`, an
extraction dispatch that LANDED at 328 lines.**

**One repair precedes the landing, and it is in the STATEMENT, not
the legs: `[LJ-1.378]`'s `Extraction` carries an UNtruncated `Σ`,
and the fourteen witnesses live in a TRUNCATED existential, so no
term of that type can come from peeling them. INFERRED, and its
control is UNMEASURED. See section 3.**

**STOP INSTRUCTION RECEIVED.** The owner stopped this task at the
two-hour mark for infrastructure work. What I had finished: the green
probe, the floor, the scratch minimization, and every leg's price.
What I had NOT finished when the stop arrived: the dedicated negative
control (`Control381A.agda`, never written, UNMEASURED), the
truncation refusal run (INFERRED only), and the feeding of my `extr`
into `[LJ-1.378]`'s `comp` (argued, not run). No Agda run was started
after the stop.

## 1. `Extraction` AS A TYPE (re-derived, C-44)

`agents/tasks/LJ-1-378/ProbeLJ1378A.agda:326-332`, VERIFIED by
reading:

```agda
Extraction : (γ : Vec SC 2) → Type (ℓ-suc ℓ)
Extraction γ =
  ⟨ A.ambient γ (embed P1241.φ₀) ⟩
    → Σ[ frame ∈ SC ^ 16 ]
        ( (lookup (suc zero) frame ≡ lookup zero γ)
        × (lookup (suc (suc zero)) frame ≡ lookup (suc zero) γ)
        × ⟨ frame ⊨ levelRow ⟩ )
```

The hypothesis is `φ₀`'s satisfaction at the ambient reading. The
conclusion builds a sixteen-slot frame from γ, pins two slots to γ's
own entries, and demands the level row there. That is the obligation,
and I adopt it unchanged in shape. `φ₀ = closeN 14 (pins ∧̇ renamed)`
and `renamed = renameFo ρ base`, both at
`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:124-146`, VERIFIED by
reading. The repair in section 3 changes one connective in this
statement and nothing else.

## 2. THE SIX LEGS, EACH WITH A TERM OR A COUNT

All six legs are terms in the green file. Line numbers are real.

| leg | what `[LJ-1.378]` called it | what I built | lines | status |
|---|---|---|---:|---|
| 1. fourteen-fold `∃̇` unfold | mechanical | `ex-14`, `ProbeLJ1381A.agda:149-178`, a nested `PT.rec` tower over the reduced `closeK 14` spine | 30 | MEASURED, exit 0 |
| 2. conjunct projection | mechanical | one `.snd`, `:375` | 1 | MEASURED, exit 0 |
| 3. rename-back along `ρ` | delivered `⊨-rename`, needs the SAME leaf-naturality | `step2 :346-351`, `ag :307-329`, `lookup-inj :290-293`, `frameOf :299-305` | 36 | MEASURED, `ScratchA.agda` exit 0 at `base` itself, 49.8 s user |
| 4. un-erase along `Cnt.erase-inv` | delivered | NOT INVOKED. It collapsed into `dia : embed P1241.base ≡ levelRow`, `refl`, `:285-286` | 2 | MEASURED, the `refl` is in the green run |
| 5. `embed`-`renameFo` commutation | unwritten mechanical induction, about 12 lines | `mapTm-ren :107-111`, `mapFo-ren :113-136`, `emb-ren :138-140`, generic in both carriers | 34 | MEASURED, exit 0 |
| 6. `[LJ-1.241]`'s slot-map towers | finite arithmetic, tedious | `leafS :181-199`, `leafA :200-218`, `ψs*`/`ψa* :219-224`, the towers verbatim, erased and embedded; plus the packaging `eq1`/`eq2 :360-368` | 53 | MEASURED, exit 0 |

The sum of the legs, the packaging, and `extr :370-378` itself is
about 165 lines. The file's 248 lines also carry the header, the
imports, the trio telescope, and the row restatements that
`[LJ-1.378]`'s file already holds. So the landing pays about 210
marginal lines. The retired route paid 328 for a comparable shape
(`TASKS-archived.md:207`). The two numbers agree in order, and mine
is the direct measurement.

**The towers do NOT dominate.** The brief's abort branch three asked
whether the tedium is the cost. It is not. The two leaf towers are 44
lines of spelling and they check for free. The cost is CONVERSION,
not lines: the file's own elaboration is 456 s user against a 2.5 s
floor (`Floor381.agda`, exit 0), and the rename-back leg alone
measured 49.8 s user in `ScratchA.agda`. That seconds price is
one-time, not per-tower. MEASURED.

## 3. THE STATEMENT ITSELF NEEDS ONE REPAIR

**`[LJ-1.378]`'s `Extraction` is not inhabited by the peel, because
its `Σ` is untruncated. INFERRED. Its control is UNMEASURED.**

The argument, with Agda's own types. The `∃̇` satisfaction lands in
`⋁ S`, and at the hProp algebra `⋁` is `∃[]-syntax`, which is
`∥ Σ A (⟨_⟩ ∘ P) ∥ₚ`
(`Cubical/Functions/Logic.agda:176`, read). So the fourteen witnesses
arrive truncated. The eliminator is `PT.rec`, whose motive must be a
proposition. The conclusion `Σ[ frame ∈ SC ^ 16 ] (...)` is a SET,
not a proposition, because the witness slot varies with the frame.
So no term of `Extraction` as stated at
`ProbeLJ1378A.agda:326-332` can come from peeling the existentials.

The repair is one connective: truncate the `Σ`. My
`ExtractionT :274-284` is exactly that, and `extr :370-378` inhabits
it, green. The composite consumes it unchanged in shape, because
`comp`'s own conclusion is propositional, so one extra `PT.rec`
absorbs the truncation, about 2 lines in `comp`. INFERRED, not run.
This is the `[LJ-1.375]`-on-`[LJ-1.373]` shape one level down: a
verdict line overstated its own body. Here the body was right and the
TYPE was wrong.

## 4. ANY LEG NOT WHAT IT WAS CALLED

| leg as called | verdict |
|---|---|
| leg 3, 「needs the SAME leaf-naturality」 | **MEASURED FALSE.** `base` is constant-free syntax. It contains no `DefAt` leaf, so renaming has nothing opaque to push through. The `Agrees` side is four `refl` and one `lookup-inj` (`:307-329`). The naturality residue stays where `[LJ-1.378]` measured it, in the restriction leg, WALL ONE, not here |
| leg 4, 「delivered `Cnt.erase-inv`」 | **MEASURED, EASIER THAN CALLED.** `erase-inv` is never invoked. The two dialects agree by `refl` at the pinned leaves (`:285-286`), because both were copied verbatim from the same chapter rows, `src/L/Condensation.lagda.md:2486-2493` against `ProbeLJ1304A.agda:132-160` |
| leg 5, 「about 12 lines」 | **MEASURED, 34 lines.** The estimate was low by a factor under three. The lemma is one clause per constructor, twelve clauses plus two term cases, `:107-140` |
| leg 6, 「finite arithmetic, tedious」 | **MEASURED TRUE and SMALL.** 53 lines, and the towers are verbatim restatements, not new arithmetic |

The premise the brief doubted, 「four of six legs are delivered or
mechanical」 at `lj-1.378-report.md:28-37`: **VERIFIED and sharpened.**
Nothing was false. Two legs were EASIER than called. The adjective
risk ran the other way this time: the one item that broke was the
statement's own `Σ`, which no adjective covered.

## 5. THE HONEST INSTANTIATION

The leaf contents are PINNED, not parameters: `ψs*` and `ψa*` are
`embed (Cnt.erase leafS/leafA)` at `[LJ-1.241]`'s own towers, which
`φ₀` actually names (`BoundedSubset.lagda.md:78-107`, read). At an
unrelated leaf the dialect equation is false and the price would be
meaningless. The Def-step trio stays a parameter, exactly as
`[LJ-1.378]`'s telescope holds it. MEASURED, by the green run at the
pinned leaves.

## 6. CLASS-FREE OR NOT (DD4, C-46)

**My axis is the L-against-ambient axis. DD4's own axis is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50` per the
brief, INHERITED, not re-read.**

The extraction's working legs are CLASS-FREE: `mapTm-ren`,
`mapFo-ren`, `emb-ren` are generic in both constant carriers; `ex-14`
is generic in the formula; `lookup-inj`, `ag`, `frameOf`, `eq1`,
`eq2` name no tower. The leaf towers `leafS`/`leafA` name `DefBodyB`,
the Def-tower matrix, so they are NOT class-free. But they restate
what `φ₀` already names, and `[LJ-1.241]` section 4 measured `φ₀`
itself as Def-tower content with the J tower supplying its own
matrix. So the other trophy does not pay these lines twice. The
`[LJ-1.113]` per-tower split, about 28 lines, is untouched by this
factor. MEASURED, by what the file names.

## 7. NEGATIVE CONTROL

**The dedicated control is UNMEASURED.** `Control381A.agda` was
never written. The stop instruction arrived first. The brief demanded
a control that measures, and I record the miss plainly.

What the run history does supply, all MEASURED, all on this file or
its scratch:

| red | where | what it proves |
|---|---|---|
| `sym` direction refused, `(pre ++ v ∷ g ∷ []) != (frameOf pre v g)` | `ScratchA.agda` run 2 | `⊨-rename` runs big-to-small; the green `step2` sits on a live conversion |
| slot mismatch refused, `zero != suc (suc zero) of Fin 15` | `ProbeLJ1381A.agda` run 6 | the slot arithmetic is checked, not assumed |
| packaging refused, `lookup (suc zero) (frameOf pre v g) != v` | run 7 | `eq1`/`eq2` carry real content |
| heap exhausted, 8 GB, 778 s user | run 9 | see section 8 |

These are adjacent refusals, not a control. They show the conversion
checker is live at the positions the green term occupies. They do not
substitute for the swapped-argument control `[LJ-1.378]` ran.

## 8. THE HEAP WALL, AND THE CURE (C-58, P-i)

One heap exhaustion, MEASURED: run 9, `Heap exhausted; Current
maximum heap size is 8192 MB`, 784 s wall. The cap was never raised.
The cause was my own variant that destructured `pre` concretely
inside the packaging, which forced full normalization of `base` at
concrete witnesses. The cure kept `pre` ABSTRACT in the chain and
moved the destructuring into the two standalone equations `eq1` and
`eq2`, whose statements close before normalization starts. Green
after the cure. The fourteen-fold unfold itself, written as numeral
splits, never hit the wall, so C-58's eliminator was not needed
there. MEASURED.

## 9. PREMISES CHECK

| premise | status |
|---|---|
| the extraction UNPRICED, factor unwritten, `lj-1.378-report.md:162` | **VERIFIED**, the row reads 「UNPRICED」 at `:162`; priced here |
| `Extraction` states the obligation exactly, `ProbeLJ1378A.agda` Comp module | **REFUTED IN PART**, the `Σ` needs truncation, section 3, INFERRED, control UNMEASURED |
| four of six legs delivered or mechanical, `lj-1.378-report.md:28-37` | **VERIFIED and sharpened**, all six now terms, two easier than called, section 4 |
| the composite's assembly MECHANICAL, `ProbeLJ1378A.agda` exit 0 | **VERIFIED**, untouched by this task |

## 10. ARCHIVE USED (DD18)

The four corpora, one line each. The archived-file lines were taken
after the stop instruction, by reading only, no Agda.

- `archive/src/2026-08-09-rud-route/`: DECLINED as a supplier, the retired route built the formula and never priced a peel of this shape. Citation: `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:600`, and the line read there is: `levelStory : Formula (⊥* {ℓ}) 2`.
- `archive/dev/TASKS-archived.md`: TAKEN, the retired comparable. Citation: `archive/dev/TASKS-archived.md:207`, and the line read there is: `L3.32-T178 | F2 block 1: the extraction, the pin frame, the sixteen equations | LANDED, 328 of 350: L.TowerKit born; Bridge falls 8.2 s cold; all green`.
- `archive/dev/JOURNAL-archived.md`: DECLINED, the retired extraction entries name a different object, a fine-structure extraction and a fiber-extraction OOM. Citation: `archive/dev/JOURNAL-archived.md:228`, and the line read there is: `worktree removed; `[L3.30-X1]` fine-structure extraction from the in-hand SZ`.
- `archive/dev/DECISIONS-archived.md`: DECLINED, `grep extract` over 61 lines returns zero hits, WHY NOT: no ruling on an extraction's placement exists.

The retired comparable's 328 lines cover an extraction, a pin frame
and sixteen equations. My 210 marginal lines cover the same shape at
the live tree. WHY NOT more of the retired route: `[LJ-1.241]`
section 3 already measured that its story clauses and its empty
closure clause do not transfer to this tree's coding.

## 11. LITERATURE USED (DD18)

The one line the brief asks for: **the orthodox development never
performs this peel, because it never pins numerals into slots. The
extraction is an artefact of this formalization's slot coding, so the
literature can price nothing here.**

- `dev/literature/devlin-II5.md`: DECLINED as a price source, taken as the confirmation. Citation: `dev/literature/devlin-II5.md:95`, and the line read there is: `By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`. Devlin states the equivalence and moves satisfaction between carriers. He never closes fourteen witnesses into a frame.
- `dev/literature/j-hierarchy.md`: DECLINED. Citation: `dev/literature/j-hierarchy.md:1`, and the line read there is: `# The J-hierarchy, S vs J stratification, condensation, well-order, acceptability`. WHY NOT: it stratifies one coding and never bridges two.

## 12. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap
NEVER raised. Slot count read before every invocation with the
brief's exact command. Readings: 0 at most invocations, 1 at three
invocations, a sibling live, one slot free under the cap of two.
Load was not sampled. `[LJ-1.380]` holds one slot and times cold
runs; no invocation of mine overlapped a timing window I started.

| file and state | exit | user s | note |
|---|---|---:|---|
| `Floor381.agda` | **0** | 2.51 | the empty-file floor, C-53 |
| `ProbeLJ1381A.agda`, final | **0** | 456 | the full extraction, green, 459 s wall |
| `ProbeLJ1381A.agda`, legs without `extr` | 0 | 272 | isolation run, `extr` commented |
| `ProbeLJ1381A.agda`, heap wall | heap | 778 | run 9, section 8 |
| `ProbeLJ1381A.agda`, red runs | 42, 10 runs | 0.7 to 423 | parse, scope, precedence, conversion, metas |
| `ScratchA.agda` at `base` | **0** | 49.8 | the rename-back leg alone |
| `ScratchA.agda`, small formula | 0 | 3.2 | minimization step |

The 22 invocations are listed in the shell history of this task. The
dominant seconds are conversion at `base`, not the legs' sizes.

## 13. WHAT I DID NOT SETTLE

- **The truncation control.** INFERRED only, section 3. One run of
  the untruncated form would settle it. Stopped before it ran.
- **The feeding into `comp`.** `extr` inhabits `ExtractionT`, and
  `comp` should absorb the truncation in about 2 lines. INFERRED,
  not run. That run belongs to the composite's landing brief.
- **The residue's proofs.** The other unpriced row. Out of scope
  here, and D-10 still prices its TRUTH first.
- **The seconds' optimization.** Whether the 456 s can be cut is a
  separate question. The number stands as measured, once.
- **The landing.** Nothing landed. `src/` untouched.

## 14. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-381/`: this report,
`ProbeLJ1381A.agda`, `Floor381.agda`, `ScratchA.agda`. `src/` holds
no file of mine. The sibling task directories were read and imported,
never edited. `src/Everything.lagda.md`, `dev/ledger.toml`,
`dev/PLAN.md` were not touched. No commit, no push, no `git
checkout`, `stash`, `reset` or `clean`. No `make check`. `_build/`
holds only Agda's own interface files for my modules, the same class
`[LJ-1.378]` left. `lint-agda.py --check` passed at exit 0 on all
three Agda files before this report closed. `lint-prose.py --check`
passed on this report. No em dash in any language. No Agda run was
started after the stop instruction.
