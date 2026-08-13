# LJ-1.164 report: `elem-down` is out of `Co`, and the move is pure

## 1. LEAD: THE MOVE IS PURE, AND THE DIFF SHAPE

**PURE. MEASURED, by the diff itself and by Agda.**

| | |
|---|---|
| lines added | **146** |
| lines removed | **146** |
| net lines | **0** |
| in-fence non-blank lines, before and after | **1409 and 1409** |
| **lines of PROOF changed** | **ZERO** |
| tokens changed | **ZERO** |
| the only textual change | **indentation, 6 spaces to 4, on every non-blank moved line** |
| hunks | **2**, one insertion and one deletion of the same block |

**The purity is MECHANICALLY CHECKED, not asserted.** Every added line is a
removed line with exactly two leading spaces taken off, **in order**:

```
added == removed dedented by 2, in order: True
identical ignoring indentation: True
```

Both tests ran over `git diff -U0` output. The dedent is forced: `module Co`'s
body sits at 6 spaces and `BoundedSubsetAt`'s body at 4, and Agda's layout is
significant. **No other character moved.**

The diff hunk headers show the shape in one line:

```
@@ -1407,0 +1408,146 @@ module Devlin55
@@ -1425,146 +1570,0 @@ module Devlin55
```

**Nothing was deleted. Nothing was written.**

## 2. WHAT MOVED, at `file:line`

One contiguous block, `src/L/BoundedSubset.lagda.md:1425-1570` before, now
`:1408-1553`, lifted from inside `module Co` to the scope directly above it,
inside `module Devlin55.BoundedSubsetAt`.

| definition | was | is now |
|---|---|---|
| the comment, "The code count: the hull's term algebra injects into alpha" | `:1425` | `:1408` |
| `module CodeCount (g : ⟪ UK.X ⟫ ↪ ⟪ α ⟫)` | `:1426` | `:1409` |
| `code-inj` | `:1529` | `:1512` |
| `module CC = CodeCount code-inj` | `:1532` | `:1515` |
| `module IC = InvColl ...` | `:1534` | `:1517` |
| `module CSel = CodeSelect ...` | `:1535` | `:1518` |
| `module CCn = CanonCode ...` | `:1545` | `:1528` |
| `hedF`, `hedF-spec` | `:1549`, `:1552` | `:1532`, `:1535` |
| `module HED = HullElemDown ...` | `:1560` | `:1543` |
| `module HEDC = HED.WithCode hedF hedF-spec` | `:1561` | `:1544` |
| `module DR54 = DownReflect ...` | `:1566` | `:1549` |
| **`elem-down : DR54.ElemDown`** | **`:1568-1569`** | **`:1551-1552`** |

**What stayed in `Co`, and why.** `module Cn = HS.Condense levelIn cover`
(`:1560` now), `β`, `β-isOrd` and `ext`. These are the only definitions in the
old `Co` prefix that read `levelIn` or `cover`. Everything from `πX↪α` down
(`πX↪α`, `β↪α`, `x∈M`, `x∈πX`, `β∈κ`, `x∈Lκ`, `theorem`) also stayed: `theorem`
is the site's conclusion and `β↪α` reads `β` and `ext`, so `Co` is still the
right home for it. **I moved the minimum that makes `elem-down` reachable, and
not one definition more.**

**Two definitions rode along, and I say so rather than hide them.** `IC` and
`CSel` (`:1517-1520` now) are inside the contiguous range and `elem-down` does
not need them; their only consumer is `πX↪α`, which stayed in `Co` and still
sees them by scoping. **I carried them so the move is ONE hunk and `Co` has no
hole in it.** Splitting the move to leave them behind would have produced two
holes and a longer diff for no gain. They are independent of `levelIn` and
`cover` for the same reason the rest of the block is.

## 3. CONSUMERS (C-40)

**Every consumer typechecked. One agda process throughout,
`GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**

| what | exit | wall clock | RSS |
|---|---|---|---|
| `src/L/BoundedSubset.lagda.md`, BASELINE before the edit | 0 | 2.54 s (interface reused, no recheck) | 631 MB |
| **`src/L/BoundedSubset.lagda.md`, after the move, full recheck** | **0** | **15.64 s** | **2032 MB** |
| **`src/Everything.lagda.md`, the ONLY importer** | **0** | **3.64 s** | **675 MB** |
| re-run of the master after the negative control | 0 | 15.80 s | 2032 MB |
| re-run of `src/Everything.lagda.md` | 0 | 2.80 s | 646 MB |
| `agents/tasks/LJ-1-164/ProbeLJ1164A.agda` | **0** | **7.56 s** | 1309 MB |

**No heap exhaustion. No wall. 2.03 GB peak against an 8 GB cap.**

**The consumer set is MEASURED, not assumed.**
`grep -rn "L.BoundedSubset" src/ archive/` outside the master returns exactly
one line, `src/Everything.lagda.md:374`. `grep -rn "Devlin55\|BoundedSubsetAt"
src/` outside the master returns nothing.

**The build directory is left consistent with the final source.** The master,
`Everything` and this task's probe were all re-run after the negative control
of section 5, so no stale interface is left behind.

### One probe outside `src/` went RED, and I did NOT repair it

**MEASURED.** `agents/tasks/LJ-1-163/ProbeLJ1163A.agda:211`, exit 42, ONE error:

```
Not in scope: Co₁.CC.count
  (did you mean 'BSA.CC.count' or 'BSA.CodeCount.count'?)
```

The line is `module LW₁ = Lift₁.WithCount Co₁.CC.count Co₁.CC.count-inj`. It
names `CC` through `Co`, and `CC` is now on `BoundedSubsetAt`. **One line, one
token path, and Agda names the repair itself.**

**I did not repair it, for three reasons and each stands alone.**

1. **The brief's abort criterion:** "A consumer goes RED: STOP, report it. Do
   not repair it in the same pass."
2. **It is outside my write scope.** `agents/tasks/LJ-1-163/` is another task's
   directory. My scope is `src/L/BoundedSubset.lagda.md` and
   `agents/tasks/LJ-1-164/`.
3. **The repo doctrine says a finished probe is text.**
   `scripts/check-probes.py:10-12`: "**A FINISHED PROBE IS TEXT.** Nothing
   typechecks it after its task closes. Its claim is true of the tree at its
   date and is never re-verified." **So this RED is expected by design and it
   is not a gate failure.** `make check` runs `check-probes.py --check`, which
   is a placement checker, not a typechecker; `make typecheck` runs
   `agda src/Everything.lagda.md` only.

**MEASURED, and it matters for the classification:** `[LJ-1.163]`'s probe was
already carrying a commented-out walling term at `:226`. Its BLOCK 3 was the
part that named `Co₁.CC`, and BLOCKS 1 and 2, the blocks its verdict rests on,
name nothing that moved. **The verdict of `[LJ-1.163]` is untouched by this
move.**

### A second probe is RED, and it is NOT my regression

**MEASURED.** `agents/tasks/LJ-1-119/ProbeLJ1119A.agda` exits 42 with
`ModuleNameDoesntMatchFileName` at `:23.8-20`: it declares
`module ProbeLJ1119A` while sitting at `agents/tasks/LJ-1-119/`, so its module
path should be `LJ-1-119.ProbeLJ1119A`. **The failure is in its own header and
Agda never reaches a BoundedSubset name.** It applies `BA.Co levelIn cover`
(`:76`), which the move leaves valid. **Pre-existing, and I report it only so
nobody reads it as fallout.**

**No other file anywhere references a moved name through `Co`.** A sweep of
`agents/tasks/` and `src/` for `BoundedSubsetAt`, `.Co`, `Co₁` and `Co₂`
returns the two probes above, this task's own probe, and comment text.

## 4. WHAT IS NOW REACHABLE THAT WAS NOT

**A proof of `levelIn` or of `cover` may now consume `ElemDown`. Before the
move it could not, and that was the whole of `[LJ-1.7]`'s blocker.**

**This is MEASURED, both directions, not inferred.**

**AFTER the move**, `agents/tasks/LJ-1-164/ProbeLJ1164A.agda`, exit 0 in
7.56 s. `:97-98` names the supply with `Co` applied nowhere:

```agda
  ed : BSA.DR54.ElemDown
  ed = BSA.elem-down
```

and `:111-115` states the shape `[LJ-1.7]` needs, which is the load-bearing
part:

```agda
  route-levelIn : (BSA.DR54.ElemDown → LevelIn) → LevelIn
  route-levelIn k = k BSA.elem-down

  route-cover : (BSA.DR54.ElemDown → Cover) → Cover
  route-cover k = k BSA.elem-down
```

These typecheck only if `elem-down` is in scope **at the point where `LevelIn`
and `Cover` are still open goals**. The probe discharges neither and claims
nothing about either; what it measures is SCOPE. `:124-131` then closes the
loop: it feeds the discharged pair back into `BSA.Co` and re-derives
`Co'.theorem : ⟨ x ∈ˢ Lset κ ⟩`, **so the move costs the delivered assembly
nothing.**

**BEFORE the move**, the SAME probe against the pre-move master: **exit 42,
`NotInScope` at `:97`.** I restored the original file, ran it, and restored the
moved file under a SHA-256 guard that matched. Agda's own suggestion list is
the cleanest statement of the defect this task removed:

```
Not in scope: BSA.DR54.ElemDown
  (did you mean ... 'BSA.Co.DR54.ElemDown' or 'BSA.Co.elem-down' ...)
```

**Every path Agda could offer ran through `Co`, and `Co` takes `levelIn` and
`cover` as parameters.** So the only way to reach the supply was to have
already supplied the two things you were trying to prove.

**What this does NOT do, stated plainly.** It does not prove `levelIn`. It does
not prove `cover`. It does not shorten `CrossOut`, still priced at 163 by
`[LJ-1.162]`. **It removes a scope obstruction, and nothing else.** Whether
`[LJ-1.160]`'s 16 in-fence lines close both hypotheses is now a question that
can be ASKED; before the move it could not be written down.

## 5. WAS THE RE-EXPORT NEEDED? NO

**MEASURED. No compatibility re-export was needed, and I added none.**

`grep -rn "elem-down" src/` returns four lines, and none is a use of the moved
definition:

- `src/L/BoundedSubset.lagda.md:762,765`, the top-level
  `HullElemDown.WithCode.elem-down`, a different definition;
- `:1551-1552`, the moved definition itself.

**`grep -rn "elem-down" src/` finds the DEFINITION and NO USE ANYWHERE.** That
confirms `[LJ-1.163]`'s measurement on today's tree. **C-35 fires: a delivered
block with no consumer is untested, and this is the fourth in this wing.**

**Nothing inside `Co` used `elem-down`, `HED`, `HEDC`, `DR54`, `CodeCount`,
`code-inj`, `CC` or `CCn` in a way the move breaks**, because Agda's scoping
gives an inner module everything the enclosing one binds. The only inner
consumers of the moved block are `πX↪α` (`IC`, `CSel`), and it typechecks
unchanged. **The tree is the proof: the master exits 0.**

## 6. DD4

**The moved definition lands BELOW the fork, and the move does not touch the
fork.**

`[LJ-1.163]` measured the fork point as ONE line, `src/L/BoundedSubset.lagda.md:670`,
`module ASt = AtStage α ordα` inside `HullElemDown` (`:667`). **That line is
untouched: my first changed line is `:1407`.** `elem-down` was at `:1568` and
is now at `:1551`; both are far below `:670`, and the site
`Devlin55.BoundedSubsetAt` (`:1385`) is below it in whole.

**MEASURED, by `[LJ-1.163]`'s own criterion:** of the **146 moved lines,
`grep "Lset|Def|𝒟ₒ"` matches ZERO.**

**I state what that 0 does and does not mean, because the number invites a
larger claim than it carries.** It is LEXICAL. The moved block names no tower
in its own text, but it reads `HS`, `UK` and `SC`, which are tower-fixed above
it, so the block is not thereby generic. **What the 0 does establish is that
the move introduced no new tower mention and removed none: the fork stays ONE
line at `:670`, exactly where `[LJ-1.163]` measured it.**

**A move cannot change what the two proofs share.** The 146 lines share what
they shared before, at a different indentation. **I claim no DD4 saving from
this task and I measured none.** The DD4 consequence, if any, is downstream:
the block that supplies `ElemDown` now sits at the site's top scope, where a J
tower's own site would instantiate it the same way, rather than behind two
hypotheses that are specific to the L condensation. **That is a shape argument
and I mark it INFERRED.**

## 7. ARCHIVE USED (DD18)

**The brief's question: did the archive place its elementarity above or below
its own condensation parameters? MEASURED: ABOVE, and in a different file. The
archive never had this defect.**

- **`archive/src/2026-08-09-rud-route/L/Hull.lagda.md:248-249`** holds
  `TV-thm : (Elementary → TarskiVaught) × (TarskiVaught → Elementary)`. It sits
  inside `module AtM (M) (Mtr) (M⊆L)` at **`:120`**, whose parameters are the
  substructure, its transitivity and its inclusion. **No condensation
  parameter.**
- **`:396-398`** holds `hull-closed`, inside `module Hull (X) (X⊆L)` at
  **`:274`**. **No condensation parameter.**
- **MEASURED over the whole file:** `grep "levelIn|cover|Condense|condens"`
  on `archive/.../L/Hull.lagda.md` returns **one prose line, `:4`**, and no
  code. **The archive's Hull chapter binds no condensation hypothesis at all.**
- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:40,123`**: the
  archive's condensation is a SEPARATE CHAPTER, `module AtCarrier (M) (Mtr)`.
  The two never shared a telescope.
- **The live tree agrees at the chapter level.** `src/L/Hull.lagda.md:163`
  `module AtM (M) (M⊆L)` and `:313` `module Hull (X) (X⊆L)` carry no
  condensation parameter either.

**So the defect was never in the elementarity chapter, in either route. It was
introduced at the SITE**, `Devlin55.BoundedSubsetAt`, when the wiring from the
site's own code count to the delivered top-level `HullElemDown` was written
inside `Co` rather than beside it. **The move restores the shape both routes
already had one level up.** SHAPE only, per the brief: `[LJ-1.11]` ruled that
route's condensation target classically FALSE, and I take no claim from it.

- `agents/tasks/LJ-1-163/lj-1.163-report.md`, read WHOLE. Its section 2 is the
  measurement this task acts on; its section 5 is the wall this task avoided.
- `dev/LESSONS.md` **C-35, C-40, P-i, C-36**, read WHOLE.

## 8. LITERATURE (DD18)

**Nothing in the literature governs module placement.**

## 9. CLASSIFICATION OF EVERY NEGATIVE

| claim | verdict |
|---|---|
| the move requires changing a proof line | **MEASURED FALSE.** 146 added, 146 removed, every added line a removed line dedented by 2, in order; zero tokens changed |
| the move breaks the master | **MEASURED FALSE.** Exit 0, 15.64 s, RSS 2032 MB, no heap exhaustion |
| the move breaks a `src/` consumer | **MEASURED FALSE.** `src/Everything.lagda.md` is the only importer; exit 0 |
| `elem-down` needed a compatibility re-export inside `Co` | **MEASURED FALSE.** `grep -rn "elem-down" src/` finds the definition and no use. C-35 |
| `elem-down` depends on `levelIn` or `cover` | **MEASURED FALSE**, now a third way: the master typechecks with the definition outside the module that binds them |
| `elem-down` was reachable before the move without applying `Co` | **MEASURED FALSE.** The same probe on the pre-move tree exits 42, `NotInScope`, and Agda offers only `BSA.Co.*` paths |
| nothing outside `src/` went RED | **MEASURED FALSE.** `agents/tasks/LJ-1-163/ProbeLJ1163A.agda:211` goes RED on ONE line. Not repaired, not in scope, and expected by `scripts/check-probes.py:10-12` |
| `agents/tasks/LJ-1-119/ProbeLJ1119A.agda` is fallout from this move | **MEASURED FALSE.** It fails at `:23` on `ModuleNameDoesntMatchFileName`, before any BoundedSubset name. Pre-existing |
| the move changes the DD4 fork point | **MEASURED FALSE.** `:670` is untouched; the first changed line is `:1407` |
| the move changes the standing size | **MEASURED FALSE.** In-fence non-blank lines 1409 before and 1409 after; `ledger.py --brief` still reports standing 28,940 over 85 masters |
| the block had to be split to leave `IC` and `CSel` behind | **MEASURED FALSE.** They moved with the block and their only consumer, `πX↪α`, typechecks unchanged |
| this task proves `levelIn` or `cover` | **TRUE that it does not.** It removes a scope obstruction and nothing else |

## 10. WHAT I DID NOT DO, AND THE STOP LINES I KEPT

- **No proof changed.** No line written, no line deleted.
- **No `refl` between two module applications.** `[LJ-1.163]` MEASURED that
  wall at 20:42.15, RSS 2074 MB against an 8 GB cap, no heap exhaustion. P-i:
  no surgery on a walling term, and this task does not need the
  identification, so it does not write it.
- **No repair of the RED probe** in `agents/tasks/LJ-1-163/`. Reported, with
  the exact line and the repair Agda itself names.
- **No `src/Everything.lagda.md` edit.** No `*Agree` master touched. No
  `src/L/Coding/Graph.lagda.md` touched.
- **No `src/` probe.** The probe is `agents/tasks/LJ-1-164/ProbeLJ1164A.agda`,
  tracked, run in place. **No `postulate`, no hole, no unsolved meta**, and
  `--safe` is on.
- **No commit, no push, no `git checkout .`, no `stash`, no `reset`, no
  `clean`.**
- **`make check` NOT run.** The orchestrator runs it. I ran
  `lint-agda.py --check`, `lint-prose.py --check`, `check-probes.py --check`
  and `weave-i18n.py --check` individually: **all four exit 0.**
- **ONE agda process throughout, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Working tree**: `src/L/BoundedSubset.lagda.md` modified;
  `agents/tasks/LJ-1-164/ProbeLJ1164A.agda` and this report untracked. Nothing
  else.

## 11. STANDING FIGURES

`.venv/bin/python scripts/ledger.py --brief`: standing **28,940 lines over 85
masters**, from HEAD; thresholds SUSPENDED per the ledger header; endpoint
REFUSED; DD5 benchmarks NOT MEASURED. **I quote no size figure from any
paragraph.**

## 12. MANDATORY RULES, ANSWERED

- **C-40.** Master AND every consumer typechecked, section 3, with the consumer
  set measured by grep rather than assumed. The one RED outside `src/` is named
  at `file:line`.
- **C-35.** `elem-down` still has NO consumer. Reported, not hidden, and it is
  the reason no re-export was needed.
- **P-i.** No surgery on the walling term. Not re-approached.
- **P-l.** I re-measured this site rather than carrying `[LJ-1.163]`'s numbers:
  the master's recheck cost, 15.64 s, is measured here, not inferred from the
  probe's 16.7 s.
- **C-12.** One agda process, `-M8g`, cap never raised, RSS reported beside
  every wall clock.
- **C-22.** This file was created as a skeleton before the first agda run and
  filled as each answer landed.
- **C-36, C-39.** The brief's premise held, and I say so; the one place the
  brief's expectation and the tree differ is the re-export, which the brief
  itself told me to check rather than assume, and the answer is NO.
- **D-1.** The probe is in `agents/tasks/LJ-1-164/`, tracked, run in place.
- **DD4.** Section 6, with the fork point measured as unchanged.
- **DD23.** No mathematical prose touched. Only code moved.
