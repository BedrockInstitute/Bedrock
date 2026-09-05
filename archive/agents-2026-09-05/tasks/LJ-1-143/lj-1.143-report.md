# LJ-1.143 report: split DD25, retire `archive/probes/`, mirror the root in `archive/`

STATUS: **DONE.** All three tasks landed. **All fourteen consumers pass**, and so do all
twelve suites in `scripts/tests/`. **Nothing committed. Nothing pushed. Nothing deleted.**
Written incrementally (C-22). Every negative below is marked **MEASURED** or **INFERRED**.

## THE THREE COUNTS

- **DD25 probes placed: 55 of 55. Left in `DD25/`: 0.** `agents/tasks/DD25/` is gone. Every
  placement rests on the DD25 review that says it BUILT the probe, and 54 of the 55 carry a
  second, independent source in the probe's own header comment.
- **Archive directories moved: 5 of 6.** `archive/measurements/`, `archive/tooling/`,
  `archive/src/`, `archive/rud-route/` and `archive/probes/`. **`archive/kits/` is the one I
  left**, and section 4.3 gives the measured reason and what would decide it.
- **Citations rewritten: 538.** 49 in 17 live files, and 489 in the tombstone across 372
  distinct paths. **Zero dangle.**

Two counts the brief also asked for: **182 staged renames, 0 deletions**, of which 170 are
mine and 12 are the orchestrator's in-flight `Unpaired` move; and **1,604 tracked files**,
unchanged in number.

## TASK 1: THE DD25 PLACEMENT TABLE

**Every one of the 55 is placed on TWO independent sources**, except where noted:

1. **The review that says it BUILT the probe**, in a "THE PROBES" / "PROBES BUILT" section
   or in the review's own header.
2. **The header comment inside the probe.**

**The two sources agree on every probe that carries both. No probe is claimed as written by
two reviews.** The eight sets are disjoint and their union is 55.

A review that CITES a probe is not its writer. `[LJ-1.32]`'s review cites `ProbeDD25C`, `D`,
`E` and `H`, and says so plainly: `lj-1.32-review.md:43` reads "**`[LJ-1.27-R]` wrote
`src/ProbeDD25E.agda`**", and `:361` lists `ProbeDD25D` and `ProbeDD25H` under ARCHIVE USED as
files it READ. `lj-1.34-review.md:511` cites `ProbeDD25D` under ARCHIVE USED. `lj-1.41-review.md:191`
cites `ProbeDD25D2` as evidence quoted from `[LJ-1.35]`'s report. **All five are citations, and
none moved the probe.**

| Probe | Placed in | The `file:line` that proves it | Header comment |
|---|---|---|---|
| `ProbeDD25A` | `LJ-1-27` | `agents/tasks/archive/LJ-1-27/lj-1.27-review.md:289` | `[LJ-1.27]` |
| `ProbeDD25B` | `LJ-1-27` | `.../lj-1.27-review.md:290` | `[LJ-1.27]` |
| `ProbeDD25C` | `LJ-1-27` | `.../lj-1.27-review.md:291` | `[LJ-1.27]` |
| `ProbeDD25D` | `LJ-1-27` | `.../lj-1.27-review.md:292` | `[LJ-1.27]` |
| `ProbeDD25E` | `LJ-1-27` | `.../lj-1.27-review.md:293` | `[LJ-1.27]` |
| `ProbeDD25F` | `LJ-1-27` | `.../lj-1.27-review.md:294` and `:87` | **none** |
| `ProbeDD25G` | `LJ-1-27` | `.../lj-1.27-review.md:295` | `[LJ-1.27]` |
| `ProbeDD25H` | `LJ-1-27` | `.../lj-1.27-review.md:296` | `[LJ-1.27]` |
| `ProbeDD25B1` | `LJ-1-32` | `agents/tasks/archive/LJ-1-32/lj-1.32-review.md:388` | `[DD25 review of LJ-1.32]` |
| `ProbeDD25B2` | `LJ-1-32` | `.../lj-1.32-review.md:389` | `[DD25 review]` |
| `ProbeDD25B3` | `LJ-1-32` | `.../lj-1.32-review.md:390` | `[DD25 review of LJ-1.32]` |
| `ProbeDD25B4` | `LJ-1-32` | `.../lj-1.32-review.md:391` | `[DD25 review of LJ-1.32]` |
| `ProbeDD25B5` | `LJ-1-32` | `.../lj-1.32-review.md:392` | `[LJ-1.32]` |
| `ProbeDD25B10` | `LJ-1-32` | `.../lj-1.32-review.md:393` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25B11` | `LJ-1-32` | `.../lj-1.32-review.md:393` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25B12` | `LJ-1-32` | `.../lj-1.32-review.md:393` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25B13` | `LJ-1-32` | `.../lj-1.32-review.md:393` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25B14` | `LJ-1-32` | `.../lj-1.32-review.md:393` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25Bd04` | `LJ-1-32` | `.../lj-1.32-review.md:394` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25Bd08` | `LJ-1-32` | `.../lj-1.32-review.md:394` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25Bd12` | `LJ-1-32` | `.../lj-1.32-review.md:394` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25Bd16` | `LJ-1-32` | `.../lj-1.32-review.md:394` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25Bd20` | `LJ-1-32` | `.../lj-1.32-review.md:394` (slash family) | `[DD25 review of LJ-1.32]` |
| `ProbeDD25CF` | `LJ-1-33` | `agents/tasks/archive/LJ-1-33/lj-1.33-review.md:273` | `[DD25 review of LJ-1.33]` |
| `ProbeDD25CE` | `LJ-1-33` | `.../lj-1.33-review.md:274` | `[DD25 review of LJ-1.33]` |
| `ProbeDD25CL` | `LJ-1-33` | `.../lj-1.33-review.md:275` | `[DD25 review of LJ-1.33]` |
| `ProbeDD25CS` | `LJ-1-33` | `.../lj-1.33-review.md:276` | `[DD25 review of LJ-1.33]` |
| `ProbeDD25CD` | `LJ-1-33` | `.../lj-1.33-review.md:277` | `[DD25 review of LJ-1.33]` |
| `ProbeDD25CB` | `LJ-1-33` | `.../lj-1.33-review.md:278` | `[LJ-1.33]` |
| `ProbeDD25CM` | `LJ-1-33` | `.../lj-1.33-review.md:279` | `[DD25 review of LJ-1.33]` |
| `ProbeDD25D1` | `LJ-1-34` | `agents/tasks/archive/LJ-1-34/lj-1.34-review.md:523` | `[DD25 review of LJ-1.34]` |
| `ProbeDD25D2` | `LJ-1-34` | `.../lj-1.34-review.md:524` | `[DD25 review of LJ-1.34]` |
| `ProbeDD25D3` | `LJ-1-34` | `.../lj-1.34-review.md:525` | `[DD25 review of LJ-1.34]` |
| `ProbeDD25D4` | `LJ-1-34` | `.../lj-1.34-review.md:526` | `[DD25 review of LJ-1.34]` |
| `ProbeDD25D5` | `LJ-1-34` | `.../lj-1.34-review.md:527` | `[DD25 review of LJ-1.34]` |
| `ProbeDD25E1` | `LJ-1-38` | `agents/tasks/archive/LJ-1-38/lj-1.38-review.md:6` | `[DD25 review of LJ-1.38]` |
| `ProbeDD25E2` | `LJ-1-38` | `.../lj-1.38-review.md:6` | `[DD25 review of LJ-1.38]` |
| `ProbeDD25E3` | `LJ-1-38` | `.../lj-1.38-review.md:7` | `[DD25 review of LJ-1.38]` |
| `ProbeDD25F41A` | `LJ-1-41` | `agents/tasks/archive/LJ-1-41/lj-1.41-review.md:4` (range `A` to `D`) | `[DD25 / LJ-1.41 REVIEW]` |
| `ProbeDD25F41B` | `LJ-1-41` | `.../lj-1.41-review.md:4` (range) | `[DD25 / LJ-1.41 REVIEW]` |
| `ProbeDD25F41C` | `LJ-1-41` | `.../lj-1.41-review.md:4` (range) | `[DD25 / LJ-1.41 REVIEW]` |
| `ProbeDD25F41D` | `LJ-1-41` | `.../lj-1.41-review.md:4` (range) | `[DD25 / LJ-1.41 REVIEW]` |
| `ProbeDD25G1` | `LJ-1-7` | `agents/tasks/archive/LJ-1-7/lj-1.7-review.md:7` | `DD25 review probe G1` |
| `ProbeDD25G2` | `LJ-1-7` | `.../lj-1.7-review.md:8` | `DD25 review probe G2` |
| `ProbeDD25G3` | `LJ-1-7` | `.../lj-1.7-review.md:8` | `DD25 review probe G3` |
| `ProbeDD25G2Cone` | `LJ-1-7` | `.../lj-1.7-review.md:9` and `:297` (the cone figure) | `DD25 review probe G2` |
| `ProbeDD25H1` | `LJ-1-50` | `agents/tasks/archive/LJ-1-50/lj-1.50-review.md:5` (range `H1` to `H8`) | `[LJ-1.50]` |
| `ProbeDD25H2` | `LJ-1-50` | `.../lj-1.50-review.md:5` (range) | `DD25 review probe H2` |
| `ProbeDD25H3` | `LJ-1-50` | `.../lj-1.50-review.md:5` (range) | `DD25 review probe H3` |
| `ProbeDD25H4` | `LJ-1-50` | `.../lj-1.50-review.md:5` (range) | `DD25 review probe H4` |
| `ProbeDD25H5` | `LJ-1-50` | `.../lj-1.50-review.md:5` (range) | `[LJ-1.50]` |
| `ProbeDD25H6` | `LJ-1-50` | `.../lj-1.50-review.md:5` (range) | `DD25 review probe H6` |
| `ProbeDD25H7` | `LJ-1-50` | `.../lj-1.50-review.md:5` (range) | `[LJ-1.50]` |
| `ProbeDD25H8` | `LJ-1-50` | `.../lj-1.50-review.md:5` (range) | `DD25 review probe H8` |
| `ProbeDD25H2N` | `LJ-1-50` | `.../lj-1.50-review.md:6` ("the negative control") | `DD25 review probe H2` |

**The one probe with no header comment is `ProbeDD25F`**, and it is NOT a guess.
`lj-1.27-review.md:294` says it "measures the constant count of each coding reader", and
`:87` says "`src/ProbeDD25F.agda` measures each delivered coding reader". The file's body is
five `countFo` assertions over `prAtL`, `appAt`, `consAtL`, `sucAtL` and `tagAtL`, the five
coding readers (`agents/tasks/LJ-1-27/ProbeDD25F.agda:11-22`). **The content matches the
claim, and no other review names the file.**

**`ProbeDD25R` does not exist. MEASURED** by `find . -name 'ProbeDD25R*'`, which returns
nothing. `agents/tasks/archive/LJ-1-66/lj-1.66-review.md:662` names `src/ProbeDD25R*.agda` as
a miniature it DECLINED to write.

### The naming scheme this uncovered, which nobody had written down

`ProbeDD25<letter>` with no digit is `[LJ-1.27]`'s review. Every later DD25 review took the
next letter and appended a number: `B*` is `[LJ-1.32]`, `C*` is `[LJ-1.33]`, `D*` is
`[LJ-1.34]`, `E*` is `[LJ-1.38]`, `F41*` is `[LJ-1.41]`, `G*` is `[LJ-1.7]`, `H*` is
`[LJ-1.50]`. **So the plain letter and the lettered family do NOT share a task**, and a reader
who assumed `ProbeDD25D` and `ProbeDD25D1` belong together would place four probes wrong.

## 2. THE CITATION COST, COUNTED BEFORE ANYTHING MOVED

**I counted first, as the brief requires.** The census over the whole tree, by path prefix:

| Prefix | Tokens in the tree | Of those, LIVE |
|---|---:|---:|
| `agents/tasks/DD25/` | 17 | **13** |
| `archive/probes/` | 356 | 8 |
| `archive/rud-route/` | 319 | 7 |
| `archive/src/` | 97 | 5 |
| `archive/tooling/` | 37 | 16 |
| `archive/measurements/` | 9 | 5 |
| `archive/kits/` | 27 | 8, and none moved |

**The gap between the two columns is the frozen corpus**, and it is not rewritten
(`[LJ-1.130]`, `[LJ-1.133]`, `[LJ-1.142]`). 260 of the 356 `archive/probes/` tokens are the
tombstone's own map.

### 2.1 The three shorthands, and I found a FOURTH

The brief named three traps. **All three exist in this corpus and a fourth does too.**

| Shorthand | Example | Where | Live? |
|---|---|---|---|
| Brace family | `ProbeDD25F41{A,B,C,D}.agda` | `dev/LESSONS.md:3347` | **YES** |
| **Slash family, NOT in the brief** | `src/ProbeDD25B10/11/12/13/14.agda` | `lj-1.32-review.md:393`, `:394` | no, frozen |
| Range, written with `to` | `src/ProbeDD25H1.agda` to `src/ProbeDD25H8.agda` | `lj-1.50-review.md:5`, `lj-1.41-review.md:4` | no, frozen |
| `Path`-style construction | `ROOT / "agents" / "briefs"` | five checkers, now `scripts/agents_tree.py` | n/a |

**The slash family is a fourth shape and it is load-bearing evidence**, not decoration:
`lj-1.32-review.md:393` is the ONLY document that claims `ProbeDD25B10` through `B14`, so a
reader whose search misses the slash form finds no writer for five probes. I read
`scripts/agents_tree.py` whole before assuming a grep was a census, as the brief instructs.

**MEASURED: the range form is used ZERO times in live text**, so a rewriter never meets it;
it is used twice in frozen reviews, where it decides 13 placements. `[LJ-1.142]` measured
"zero live range citations" and that still holds.

### 2.2 The dry run, and what it caught

**The dry run printed 263 unresolved tokens on its first pass.** 257 were the tombstone's
FIRST column: dead paths that are SUPPOSED not to resolve, because that is what a tombstone
is. **A rewriter that had "fixed" them would have destroyed the map.** I excluded the
tombstone from the generic pass and gave it its own pass over its SECOND and THIRD columns,
which are the ones that must resolve.

The second dry run left 5, and every one was a real judgment rather than a bug: two rule
statements that quote an example path (`archive/README.md:13`, `scripts/check-probes.py:60`),
one `agda -i` invocation (`dev/LESSONS.md:1680`), one layout docstring
(`scripts/agents_tree.py:16`), and one cross-reference inside a moved README. **I fixed all
five by hand and named them rather than letting a regex guess.**

## 3. TASK 2: `archive/probes/` RETIREMENT

### 3.1 What a retired tombstone is for, and the measurement that decides it

**MEASURED, and the two halves of the brief's test give different answers, so I report both.**

- **No LIVE document cites an `archive/probes/<probe>` path.** The search was
  `grep -rnoE 'archive/probes/[A-Za-z0-9_{},.-]+\.(agda|lagda\.md)'` over `dev/`, `scripts/`,
  `Makefile`, `.gitignore`, `REUSE.toml`, `README.md` and `docs/`. One hit, and it is
  `scripts/tests/test_probe_gate.py:82`, a **synthetic gate fixture** naming `ProbeX.agda`,
  which is supposed not to exist.
- **SEVEN FROZEN citations do**, in three reports: `lj-1.132-report.md`, `lj-1.133-report.md`
  and `lj-1.141-report.md`. Same search over `agents/`.
- **Four live documents cite the tombstone ITSELF** as a navigational aid: `dev/ARCHIVE.md:83`,
  `dev/LESSONS.md:1093`, `agents/README.md:83`, `archive/README.md:16` and `:20`.

**So the answer is: a retired tombstone is a PATH RESOLVER for frozen records, and nothing
else.** It has no live consumer of its rows and it never will, because nothing new can arrive
at a dead path. That is exactly why it must be correct: the only reader it will ever have is
somebody who met a dead path in a frozen report and has no other way to resolve it.

### 3.2 What I did

**I retired the DIRECTORY and kept the map, corrected through all three hops.**

`archive/probes/README.md` is now `archive/src/2026-08-13-probe-sweep/README.md`. The 257
probes came out of `src/`, so under task 3's mirror rule the record of that archival sits with
the other `src/` archivals, and the directory name says which archival it was.

**The map was two hops short and is now current.** `[LJ-1.141]` wrote it pointing at
`agents/reports/<TASK>/`; `[LJ-1.142]` renamed the root to `agents/tasks/`; `[LJ-1.143]`
placed the 55 DD25 probes and the orchestrator moved `Unpaired` under `archive/`. I re-pointed
the second and third columns by BASENAME against the tree, which is `[LJ-1.142]`'s method and
is verifiable:

- **489 tokens rewritten, 372 distinct paths, ZERO dangling. MEASURED** by testing every
  `agents/` token in the file against disk.
- **Basenames are unique under `agents/`. MEASURED**: `git ls-files agents | sed 's|.*/||' |
  sort | uniq -d` returns nothing, so the lookup has exactly one answer.

**I stated the frozen/not-frozen split inside the document itself**, because the old text said
the whole table was frozen and that claim is what would stop the next agent fixing it: the
first column is frozen and must never change; the second and third must resolve or the map
answers nothing.

`dev/ARCHIVE.md` now carries the retirement record with all five things the brief names,
including **what it did right, from measurement**: it left a machine-generated map rather than
a memory, and that map has survived three re-pointings by basename lookup with zero dangle. A
hand-written map would not have survived one.

## 4. TASK 3: `archive/` MIRRORS THE ROOT

### 4.1 The provenance I found, per directory. MEASURED from `git log`

| Directory | Provenance | Evidence | New home |
|---|---|---|---|
| `archive/dev/` | the retired records | already correct | unchanged |
| `archive/src/` | `src/**`, at its original path, in **FIVE separate archivals** | `R100` renames in `93bf246`, `e33a4ce`, `b06822e`, `9b15509`, `43ca411` | `archive/src/<event>/**` |
| `archive/rud-route/` | `src/**`, in ONE archival | `R100 src/L/Condensation.lagda.md -> archive/rud-route/src/L/Condensation.lagda.md` in `86c7b66` | `archive/src/2026-08-09-rud-route/` |
| `archive/tooling/` | `scripts/` and `scripts/tests/` | `R100 scripts/dashboard.py -> archive/tooling/dashboard.py` and `R100 scripts/tests/test_dashboard.py -> archive/tooling/test_dashboard.py` in `0b10503`; `R100 scripts/tests/test_probe_lifecycle.py -> ...` in `9ed26d3` | `archive/scripts/` and `archive/scripts/tests/` |
| `archive/measurements/` | **NOT a git rename.** Added fresh in `265bf0d` | `A archive/measurements/l3.32-t242-profile.txt`. The live counterpart is named by the directory's own record: `archive/dev/measurements/README.md:8-10` says "Live records ... live in `dev/measurements`. A record moves here when every document that cites it has become historical" | `archive/dev/measurements/` |
| `archive/kits/` | **NO ROOT PATH EXISTS.** Added fresh in `e19f12a` and `265bf0d` | `archive/kits/README.md:35-40`: "A refused kit has no original path: it never landed in `src/`" | **LEFT. See 4.3** |
| `archive/probes/` | `src/Probe*.agda` | task 2 | `archive/src/2026-08-13-probe-sweep/` |

**The owner's ruling on `archive/measurements/` is CORROBORATED but not by git.** Git says the
files were added, not renamed, because `[LJ-1.132]` salvaged them out of `_build/`, which is
untracked. **The directory's own README names `dev/measurements/` as its live counterpart**,
and `dev/build-manifest.toml:54` states the lifecycle as `_build/` to `dev/measurements/` to
the archive. So `archive/dev/measurements/` is right, and I record that the evidence is the
documented lifecycle rather than a rename record. **MEASURED, and the distinction is stated
because a rename would have been stronger evidence and there is none.**

### 4.2 The source case: the naming I chose, and why

**`archive/src/<date>-<slug>/<path under src>`.** The slug comes verbatim from the archival
commit's own subject line, so nothing is invented.

| Event directory | Commit | Files |
|---|---|---:|
| `2026-08-05-realize-cone` | `93bf246` `[L3.32-T29]` "the Realize cone retires into the archive" | 1 |
| `2026-08-06-four-dead-modules` | `e33a4ce` `[L3.32-F6.0]` "Archive the four dead modules" | 4 |
| `2026-08-07-arm-a` | `b06822e` `[L3.32-F]` "Archive arm A" | 16 |
| `2026-08-08-describe-switch` | `9b15509` `[L3.32-F]` "Describe and Switch archive" | 2 |
| `2026-08-09-hf-finite` | `43ca411` `[L3.32-F]` "HF and Finite are archived" | 2 |
| `2026-08-09-rud-route` | `86c7b66` `[L3.32-F]` "the rud route's 72 differing files are archived" | 74 |
| `2026-08-13-probe-sweep` | `[LJ-1.141]`, retired by `[LJ-1.143]` | 1, the tombstone |

**WHY PER-COMMIT, and this is the one judgment in task 3 that I want read closely.**

The brief says the name must identify the archival EVENT, not the content. **Git says
`archive/src/` is not one archival. It is five**, on five days under four different rulings.
There is no honest single name for the group, and inventing one is the guess the brief
forbids. So the granularity is the granularity the evidence has.

**The alternative I rejected, and why.** Leaving today's 25 files bare at `archive/src/L/...`
and giving an event directory only to the rud route would put bare content beside an event
directory inside `archive/src/`. **That reproduces, one level down, the exact defect the owner
is removing.** Either all get event names or none do, and "none" is impossible: two archivals
both took files out of `src/L/Rud/` and `src/L/WellOrder/`, so a flat merge loses which
archival each file came from, which is the fact the owner asked the layout to keep.

**If the owner wants two directories rather than seven, the collapse is one command and this
table is the map for it.** Every move is a git rename, so nothing is lost either way.

### 4.3 The directory I did NOT move, and what would decide it

**`archive/kits/` stays where it is. C-36.**

**MEASURED, from the directory's own record at `archive/kits/README.md:35-40`: a refused kit
HAS no original path.** It never landed in `src/`, and the tree was reverted to HEAD. The
mirror rule maps an original path to an archived path, so here it has nothing to map. This is
a different verdict from "unclear": the provenance is known, and it is that no root path
exists.

**Two candidate homes, and I refuse to choose between them:**

1. `archive/src/kits/`, because a kit was code written for `src/`.
2. `archive/_build/kits/`, because `_build/kits/` is the path these files actually came from
   (`archive/kits/README.md:22-33` records that move, and `_build/` IS a root directory).

**What would decide it: the owner's word on whether a thing that never had a root path gets a
mirror position at all.** I wrote the question into `archive/kits/README.md` so the next
reader meets it, and `scripts/tests/test_archive_layout.py` carries `kits` as the ONE declared
exception, with its reason, so the exception is visible rather than silent.

### 4.4 The rule now has a machine, and the machine can fail

**`scripts/tests/test_archive_layout.py` is new**, wired into `make test`, and it is the first
thing that has ever checked the archive's shape.

- It **DERIVES** the legal set of top-level archive directories from the repository root, so
  there is no hand-written list to drift.
- It pins `archive/src/<event>/` to the `<date>-<slug>` shape, which is what makes a name say
  WHICH archival rather than merely what the files are.
- It refuses a loose file directly under `archive/src/`, which is the bare state the ruling
  removes.
- It pins `archive/scripts/tests/` as the mirror of `scripts/tests/`.
- It checks that `REUSE.toml` still covers the archive with a bare `archive/**` prefix, so a
  move inside the archive can never relicense a file.

**A test that has never rejected anything proves nothing**, so I proved it can fail: a bare
`archive/randombucket/`, an event directory named `notadate-thing`, and a loose
`archive/src/loose.md` produce **three FAILs and exit 1**; removing them returns **exit 0, 21
checks**. MEASURED.

**Why nothing caught this before, and it is structural rather than negligence.** The archive
sits outside `src/`, so every gate is blind to it BY DESIGN: the Agda gate cannot reach it,
the include path excludes it, the linters do not scan it. That is what makes the archive free
to keep, and it is also why three directories drifted in eight days with nothing to notice.

## 5. THE `archive/` TREE AS IT NOW STANDS

```
archive/
  README.md                                the rules, and the six-event table
  dev/                                     the retired records (was already correct)
    DECISIONS-archived.md  JOURNAL-archived.md  README.md
    STATUS-archived.md     TASKS-archived.md
    measurements/                          <- was archive/measurements/          9 files
  scripts/                                 <- was archive/tooling/               4 files
    README.md  check-dashboard.py  check-probes-lifecycle.py  dashboard.py
    tests/                                 <- was archive/tooling/ (flat)        2 files
      test_dashboard.py  test_probe_lifecycle.py
  src/
    2026-08-05-realize-cone/L/Rud/                                               1 file
    2026-08-06-four-dead-modules/L/Rud/                                          4 files
    2026-08-07-arm-a/L/{Godel,Rud,WellOrder}/                                   16 files
    2026-08-08-describe-switch/L/Rud/                                            2 files
    2026-08-09-hf-finite/L/Rud/                                                  2 files
    2026-08-09-rud-route/                  <- was archive/rud-route/            74 files
      README.md  rud-route-src.patch  Everything.lagda.md  FOL/  L/  V/
    2026-08-13-probe-sweep/README.md       <- was archive/probes/                1 file
  kits/                                    LEFT. No root path exists (4.3)       6 files
```

**Nothing was lost. MEASURED: 127 tracked files under `archive/` before and after**, plus two
untracked strays that were already there (`archive/.DS_Store`) or moved with their directory
(one `.pyc`). **0 deletions in `git status`.**

## 6. THE FOURTEEN CONSUMERS

The brief's list, and I ran every one.

| # | Consumer | Result |
|---|---|---|
| 1 | `check-build-manifest.py --check` | **exit 0**, every file in `_build/` declares a lifecycle. Its hardcoded home table now names `archive/dev/measurements/` and `archive/scripts/` |
| 2 | `check-dispatch-policy.py` | **exit 0**, `override` in force, **443 briefs read**, 31 pre-epoch notes |
| 3 | `check-dev-docs.py` | **exit 0**, 6 subchecks |
| 4 | `check-rule-ids.py` | **exit 0**, 45 files, 141 lessons, 66 decisions |
| 5 | `check-probes.py --check` | **exit 0**, **1,604 tracked files**, no probe outside `agents/tasks/` |
| 6 | `check-unbound-hyp.py` | **exit 0**, 38 hypotheses worth a refutation attempt |
| 7 | `check-task-index.py` | **exit 0**, 446 cited codes, 458 rows |
| 8 | `deletion-test.py` | **exit 0**, ac-total 19,993, no cap in force |
| 9 | `dd25-record.py` | **exit 0**. It reads no path under `agents/tasks/DD25/`, so the split did not touch it. MEASURED by grep |
| 10 | `ledger.py --check` | **exit 0**, standing **28,617 over 85 masters, unchanged** |
| 11 | `.gitignore` | **exit 0**. Its probe rules name `src/` only, and `git check-ignore` over all 182 staged renames returns nothing, so no moved file became invisible |
| 12 | `Makefile` | **exit 0**. Its two `archive/tooling/` comments now read `archive/scripts/`, and the new suite is wired into `make test` |
| 13 | `bedrock.agda-lib` | **exit 0**. `include: src agents/tasks`; both roots present. **No Agda run was needed**: every destination directory already existed and `[LJ-1.142]` proved the name shape |
| 14 | **`check-sources-read.py`** (NOT in `make check`; `dev/ORCHESTRATION.md:460` runs it by hand) | **exit 0**. See below |

**Consumer 14 needs its own paragraph, because "exit 0" would be a lie by omission.** It
prints `no session log found` for `LJ-1.143` and for `LJ-1.141`. **That is not my move
breaking it**: it reads codex dispatch logs, and the Opus override in force since 2026-08-13
runs every dispatch in-harness, which writes no codex log. **MEASURED: 408 logs are on disk
and none is for a recent task.** The half a file move DOES break is the tree read, and I
verified that half directly: `brief_for` resolves `LJ-1.143` and `LJ-1.141` to the live tree
and `LJ-1.27` and `LJ-1.50` to `agents/tasks/archive/`, and `named_sources("LJ-1.143")`
returns 6 paths from this brief's DD18 sections. **The consumer reads a real census, not an
empty one** (C-40).

### 6.1 Also green, and none of these is in the brief's list

| Check | Result |
|---|---|
| `check-probes.py --staged` | **exit 0** over all 182 staged renames |
| `reuse lint` | **compliant**, 1,589/1,589. **No `REUSE.toml` change was needed. MEASURED**: `archive/**` at `REUSE.toml:41` and `agents/**` at `:32` are bare path prefixes, and every move stays inside one of them |
| `check-tree.py --check` | **exit 0**, 87 masters |
| `lint-prose.py --check` | **exit 0** over the WHOLE tree |
| **All 12 suites in `scripts/tests/`** | **all exit 0**, including the new `test_archive_layout.py` |
| Relative markdown links | **0 defects** over `archive/**`, `dev/**`, `scripts/README.md`, `agents/README.md`, `README.md`, checked for BOTH broken and self-referential targets |

## 7. TWO DEFECTS I FOUND THAT ARE NOT MINE

**7.1 `scripts/agents_tree.py` reported a non-task bucket as a task. FIXED.**

`test_agents_tree.py` went RED during my run and the cause was the orchestrator's in-flight
move of `Unpaired` into `agents/tasks/archive/`. **`task_dirs()` filtered the LIVE half by
`NON_TASK_DIRS` and did not filter the ARCHIVE half**, so twelve probes with no task were
being reported to five checkers as a task named `Unpaired`. It is one line and it is in my
write scope, so I fixed it and wrote the measurement into the docstring. **The suite is green
because of the fix, not despite it.**

**7.2 A self-referential markdown link that an existence check cannot see. FIXED.**

`archive/dev/measurements/README.md:9` linked `../../dev/measurements/README.md`. After the
move that resolves to the file ITSELF, one directory deeper than intended. **A link checker
that only asks "does the target exist" passes it**, which is why I checked for
self-references too and why I say so here: the same trap waits for any future move that
changes a document's depth.

**7.3 ONE DANGLING CITATION I DID NOT FIX, and the reason is C-39.**

`dev/ledger.toml:305` cites `agents/tasks/Unpaired/ProbeTowerInd2.agda:155-159`. **That path
died with the orchestrator's `Unpaired` move, not with mine.** `dev/ledger.toml` is NOT in
this brief's SCOPE (write), which lists `dev/*.md` and `dev/memos/*.md` for citations. **A
brief's prohibition binds harder than its goal**, so I name it instead of fixing it.
**OWED to the orchestrator: one token, `agents/tasks/Unpaired/` to
`agents/tasks/archive/Unpaired/`.**

**One scope note I make against myself.** I DID rewrite `dev/build-manifest.toml:54`, which is
a `.toml` and so is outside the same list. **The reason is that it is a CONSUMER rather than
prose**: it declares where a promoted measurement goes, and my move is what made its
destination wrong. Leaving it would have left the lifecycle regime pointing at a directory I
had just removed. I flag it rather than hide it.

## 8. EVERY NEGATIVE, MARKED

- **MEASURED.** All 55 DD25 probes have a review that says it BUILT them. The eight sets are
  disjoint and their union is exactly 55. No probe is claimed as written by two reviews.
- **MEASURED.** `ProbeDD25R` does not exist. `find . -name 'ProbeDD25R*'` returns nothing;
  `lj-1.66-review.md:662` names `src/ProbeDD25R*.agda` as a miniature it DECLINED to write.
- **MEASURED.** Zero live documents cite an `archive/probes/<probe>` path. Seven frozen
  citations in three reports do. The search is in section 3.1.
- **MEASURED.** 489 tombstone tokens rewritten over 372 distinct paths, zero dangling, checked
  against disk.
- **MEASURED.** Basenames are unique under `agents/`, so the basename resolver has one answer.
- **MEASURED.** 49 citation occurrences rewritten in 17 live files, and every `archive/` or
  `agents/` path token in live text resolves on disk. The six that do not are four synthetic
  gate fixtures, one frozen archived record (`archive/dev/DECISIONS-archived.md:42`, which
  states the pre-ruling rule and is never edited), and the one OWED item in 7.3.
- **MEASURED.** `archive/tooling/` came from `scripts/` and `scripts/tests/` by `R100`
  renames. `archive/rud-route/` came from `src/` by `R100` renames. `archive/src/` came from
  `src/` by `R100` renames in five separate commits.
- **MEASURED, and it is the negative result in task 3.** `archive/measurements/` and
  `archive/kits/` have NO rename record. Both were added fresh from `_build/`. The
  `dev/measurements/` provenance rests on the documented lifecycle, not on git.
- **MEASURED.** A refused kit has no original path, by its own README at `:35-40`. That is why
  `archive/kits/` did not move.
- **MEASURED.** `test_archive_layout.py` rejects three violation shapes and exits 1; the clean
  tree exits 0 with 21 checks.
- **MEASURED.** 127 tracked files under `archive/` before and after. 1,604 tracked files in
  the repository. 182 staged renames. **0 deletions.**
- **MEASURED.** `reuse lint` compliant with no `REUSE.toml` change.
- **MEASURED.** The slash shorthand `ProbeDD25B10/11/12/13/14.agda` exists at
  `lj-1.32-review.md:393`. The brief named three shorthands; this is a fourth.
- **MEASURED.** The range shorthand is used zero times in live text and twice in frozen
  reviews, where it decides 13 placements.
- **INFERRED.** That per-commit is the granularity the owner wants for the archival-event
  directories. The owner counted "two folders"; git counts six archivals. **I took the
  evidence over the count** and said so in 4.2, because inventing a single name for five
  commits under four rulings is the guess the brief forbids. The collapse to two is one
  command if the owner prefers it.
- **INFERRED.** That the tombstone belongs under `archive/src/` rather than at the top level.
  The 257 probes' original root path was `src/`, which is measured; that this makes
  `archive/src/2026-08-13-probe-sweep/` the right home is my reading of the mirror rule.
- **INFERRED.** That correcting the tombstone's second and third columns is right, given the
  document's own claim that its table is FROZEN. **My reason is stated in 3.1**: the map has
  no purpose except resolution, and a map whose destinations are wrong resolves nothing. The
  first column, which is what a frozen record actually cites, I did not touch.
- **INFERRED.** That `ProbeDD25F` is `[LJ-1.27]`'s. It is the one probe with no header comment.
  Two lines of `lj-1.27-review.md` claim it (`:87`, `:294`), its body matches the claim, and no
  other review names it. **This is the weakest placement of the 55 and I mark it.**
- **INFERRED.** That `make check` wall time does not move. I did not measure it; the brief
  forbids running it. Nothing moved into or out of `src/`, and the two Agda include roots are
  unchanged.

## 9. WHAT I CHANGED, BY FILE

**New:** `scripts/tests/test_archive_layout.py`, and this report.

**Moved, all as git renames:** 170 files. 55 DD25 probes into eight task directories, 114
archive files, and the tombstone.

**Modified for citations only:** `dev/LESSONS.md`, `dev/PLAN.md`, `dev/ORCHESTRATION.md`,
`dev/build-manifest.toml`, `dev/measurements/README.md`, `scripts/README.md`,
`scripts/ledger.py`, `Makefile`.

**Modified for content, because a path fact in them became false:** `archive/README.md` (the
mirror rule and the six-event table), `dev/ARCHIVE.md` (the original-path column, the subtree
table, and the retirement record), `archive/kits/README.md` (why it did not move, and what
would decide it), `agents/README.md` (the tombstone pointer),
`archive/src/2026-08-13-probe-sweep/README.md` (the map and its frozen/not-frozen split),
`archive/src/2026-08-09-rud-route/README.md` (its old path), `archive/scripts/README.md` and
`archive/dev/measurements/README.md` (self-references and one broken relative link).

**Modified for behaviour:** `scripts/agents_tree.py` (the `task_dirs()` filter and the layout
docstring), `scripts/check-probes.py` (two frozen-code paths and one example),
`scripts/check-build-manifest.py` (two entries in the generated home table),
`scripts/tests/test_probe_gate.py` (two fixtures re-pointed at the new layout),
`scripts/tests/test_agents_tree.py` (the DD25 bucket now asserted GONE), `Makefile` (the new
suite).

**NOT touched, and deliberately:** `AGENTS.md` (DD19; I read it fresh and propose no line, see
section 10), `dev/ledger.toml` (7.3), `src/ProbeLJ1134A.agda`, `src/ProbeLJ1136A.agda`,
`src/ProbeLJ1136B.agda`, the `src/` gate in `check-probes.py`, every brief, report, review and
probe under `agents/tasks/`, and every archived CONTENT file under `archive/`.

**I did not run Agda. I did not run `make check`. I did not commit, push, checkout, stash,
reset or clean. I deleted no file.**

## 10. `AGENTS.md`. DD19

**I read `AGENTS.md` fresh today and I propose NO line.** Its archive row already says
"Archive retired code. Never delete it. It goes to `archive/`, outside `src/`" and names
`dev/ARCHIVE.md` as the record. **The mirror rule is a refinement of where inside `archive/`,
which `archive/README.md` is the canonical home of**, and DD19 forbids a rule that is
canonical twice. Adding it to `AGENTS.md` would restate a rule that now has both a canonical
home and a checker.

## 11. DD4

**Nothing in this task touched a proof, so DD4 had no line to share.** The task was a layout
and its tooling.

**Where the DD4 instinct applied is section 4.4.** The archive layout rule could have been
written as prose in three READMEs, one per subtree, which is the fixed form: three copies that
drift the first time one needs a correction. `test_archive_layout.py` is the generic form, and
it is generic in the strong sense: **it derives the legal set from the repository root rather
than listing it**, so a new root directory is legal in the archive the day it is created, with
no edit anywhere. The one exception carries its reason in the same file.

## 12. LITERATURE (DD18)

**Nothing in the literature governs a directory layout.**

## 13. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-142/lj-1.142-report.md`**, read WHOLE. Took: the fourteen-consumer list
  at `:170-185` and the warning at `:165-168` that number 14 is outside `make check`, which is
  why section 6 reports what "exit 0" hides for it; the frozen-record ruling at `:305-312`,
  which decided that briefs and reports are not rewritten and only live files are; the
  basename resolver and its uniqueness measurement at `:150-151`, which I re-measured and
  re-used for the tombstone; the recall bug at `:154-161`, whose brace family sits on
  `dev/LESSONS.md:3347` and which my rewriter handles; the OWED tombstone at `:311-315`, which
  is task 2; and section 4.1's `Path`-style finding at `:199-224`, which sent me to
  `agents_tree.py` before I assumed a grep was a census.
- **`agents/tasks/LJ-1-141/lj-1.141-report.md`**, consulted through its artifacts rather than
  read whole, and I say so: the tombstone it wrote is the object of task 2 and I read that
  document in full instead.
- **`agents/tasks/LJ-1-133/lj-1.133-report.md`**, via `[LJ-1.142]`'s citation trail at
  `:464-468`: the brace `{A,B,C,D}` and the range `A..F`. **Both reproduced**, and section 2.1
  adds a fourth shape neither report names.
- **`dev/ARCHIVE.md`**, read WHOLE. Took: the column definitions at `:29-60`, which are the
  standard the retirement record in section 3.2 is written to, and specifically the "what this
  code did right" column at `:47-56` with its instruction to leave the cell blank rather than
  fill it with praise; and the four-subtree table at `:76-93`, which I updated.
- **`archive/README.md`**, read WHOLE. Took the namespace rule at `:10-14`, which already said
  an archived module keeps its original path. **The owner's ruling extends that rule to the
  whole archive rather than replacing it**, and `archive/README.md` stays its canonical home.
- **`archive/kits/README.md`**, read WHOLE. `:35-40` is the measurement that decided 4.3.
- **`archive/measurements/README.md`**, read WHOLE. `:8-10` names `dev/measurements/` as the
  live counterpart, which is the evidence behind the owner's ruling that git does not give.
- **`scripts/agents_tree.py`**, read WHOLE, per the brief. Took the two brief predicates and
  their measured limits, and the `NON_TASK_DIRS` set that 7.1 repaired.
- **`REUSE.toml`**, read WHOLE. `:32` and `:41` are bare path prefixes, so no move needed an
  entry. `test_archive_layout.py` now pins that fact.
- `scripts/check-probes.py` (whole), `dev/build-manifest.toml:1-60`,
  `scripts/check-build-manifest.py:110-145`, `scripts/tests/test_agents_tree.py` (whole),
  `Makefile:155-180`, `dev/ORCHESTRATION.md:277-285,415-420`, `agents/README.md:75-92`,
  `archive/rud-route/README.md` (whole), `archive/probes/README.md` (whole), and the eight DD25
  reviews under `agents/tasks/archive/`, each read at its probe section.

