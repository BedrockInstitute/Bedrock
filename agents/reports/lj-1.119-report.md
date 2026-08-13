# LJ-1.119: restrict absorbs-subset the way sq was restricted

tier: codex (default)

## STATUS

COMPLETE. The restriction lands and the site entry closes through
`BoundedSubsetAt`'s body. `absorbs-subset` is no longer a `Devlin55`
parameter; `BoundedSubsetAt` takes the single value
`absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫` at its own `α` and `x`,
and the [LJ-1.118] site value supplies it. The entry reaches `Co`'s
telescope: the first hypotheses nothing supplies are `levelIn` and
`cover`, the abort criterion's good stop. `code-inj`, the only consumer
of the hypothesis, elaborates against the supplied value
(`src/ProbeLJ1119A.agda:78-79`, GREEN). No theorem conclusion changed.
No commit, no push.

## 0. THE VERDICT

**The restriction lands: `absorbs-subset` moves out of `Devlin55`'s
telescope into `BoundedSubsetAt`, stated at the module's own `α` and
`x`, where the only consumer names them.** The restricted hypothesis,
quoted from `src/L/BoundedSubset.lagda.md:1392`:

```agda
(absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
```

`Devlin55` now has no parameter (`src/L/BoundedSubset.lagda.md:1362-1363`).
The [LJ-1.118] site value `Site.site-inj : ⟪ Lset ω ∪ ⁅ ∅ ⁆s ⟫ ↪ ⟪ Lset ω ⟫`
(`src/ProbeLJ1118A.agda:153-154`, GREEN at 3.14 s) is exactly the
restricted hypothesis at `α = ω`, `x = ∅`, so the site supplies it with
a VALUE, not a parameter (C-38).

`BoundedSubsetAt` IS entered at the site: all fifteen telescope values
close (`src/ProbeLJ1119A.agda:38-56`), and the body elaborates through
`code-inj`, the hypothesis's only use (`:78-79`). The entry then reaches
`Co`'s telescope; the first hypotheses nothing supplies are `levelIn`
and `cover` (`src/L/BoundedSubset.lagda.md:1409-1410`), which the abort
criterion names as a good stop.

## 1. THE RESTRICTION

**The master applied the whole function at exactly one place, and only
at `BoundedSubsetAt`'s own `α` and `x`.** The demand trace, at
`file:line`:

1. `absorbs-subset` appeared in the master at exactly two lines: the
   `Devlin55` parameter (`src/L/BoundedSubset.lagda.md:1363-1365`,
   before this dispatch) and the one use in `code-inj`
   (`:1532`, before this dispatch). `git grep absorbs-subset src/`
   after the change finds nothing; the name is gone from the tree.
2. The use is inside `BoundedSubsetAt`, which names `α` (`:1389`),
   `α∉ω` (`:1389`), `x` (`:1391`) and `x⊆Lα` (`:1391`) in its own
   telescope. The application was `absorbs-subset α α∉ω x x⊆Lα`, i.e.
   the function at exactly the module's own arguments.
3. So the hypothesis's domain moves from "every `(α, x)` with `α ∉ ω`
   and `x ⊆ Lset α`" to "the module's own `α` and `x`", exactly the
   `[LJ-1.117]` move for `sq`: state the hypothesis where the consumer
   names its arguments.

The restricted form `⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫` carries the
same four pieces (`α`, `α∉ω`, `x`, `x⊆Lα`) implicitly through the
telescope: the site's `α ∉ ω` is `SiteAt.α∉ω` and the site's
`x ⊆ Lset α` is `SiteAt.x⊆Lα`, both in the entry. Nothing is weakened:
the conclusion of the hypothesis is unchanged, only its quantifier
scope narrows. This last sentence about the domain is the brief's own
prescription; the demand trace above is **MEASURED** by reading at
`file:line` and by the post-change search.

## 2. WHERE IT LANDS

**`absorbs` sits in `BoundedSubsetAt`'s telescope next to `x⊆Lα`,
immediately after the arguments it names.** `Devlin55`
(`src/L/BoundedSubset.lagda.md:1362`) lost its whole-function parameter
and now takes none. The new parameter (`:1392`) is:

```agda
(absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
```

The one consumer changes from a four-argument application to a direct
use (`:1530`):

```agda
code-inj = comp-inj absorbs (stage-card-upper α ordα (self∈sucV α) α∉ω)
```

The diff is 2 insertions and 4 deletions in the master (8 changed
lines), and nothing else in the module moved. `theorem`
(`:1621`) is byte-identical (section 5). The [LJ-1.117] restriction of
`sq` (`:1390-1392`) is untouched.

## 3. THE SITE ENTRY

**`Devlin55` and `BoundedSubsetAt` are entered at the site, all fifteen
values supplied, and the body elaborates through `code-inj`.**
`src/ProbeLJ1119A.agda` imports the [LJ-1.94] site values
(`ProbeLJ194A.SiteAt`), the [LJ-1.117] restricted `sqω`
(`ProbeLJ1117A.sqω`), and the [LJ-1.118] site value
(`ProbeLJ1118A.Site.site-inj`), then instantiates the modules.

Hypothesis by hypothesis:

| boundary | site value | where |
|---|---|---|
| `Devlin55` | no parameter now | `src/L/BoundedSubset.lagda.md:1362` |
| `BoundedSubsetAt κ` | `P194.SiteAt.κ` | `src/ProbeLJ194A.agda:1190-1191` |
| `ordκ` | `Hartogs.ordκ` | `:1193-1194` |
| `cardκ` | `Hartogs.cardκ` | `:1196-1197` |
| `κ∉ω` | `Hartogs.κ∉ω` | `:1199-1200` |
| `α`, `ordα` | `ω`, `ω-ord` | `:1202-1206` |
| `α∈κ` | `Hartogs.ω∈κ` | `:1208-1209` |
| `α∉ω` | `∈-irrefl ω` | `:1211-1212` |
| `sq` | `sqω` from the honest ℕ pairing | `src/ProbeLJ1117A.agda:57-74` |
| `x`, `x⊆Lα` | `∅`, vacuous | `src/ProbeLJ194A.agda:1214-1218` |
| `absorbs` | `P118.Site.site-inj` | `src/ProbeLJ1118A.agda:153-154` |
| `lam`, `ordλ`, `α∈λ`, `succλ`, `x∈Lλ` | `SiteAt` | `src/ProbeLJ194A.agda:1220-1233` |
| `Co`'s `levelIn`, `cover` | NOT SUPPLIED, NOT REACHED as values | `src/L/BoundedSubset.lagda.md:1409-1410` |

The entry is forced through the body: `C0` enters `BA.Co` with
`levelIn` and `cover` as parameters, and `code-inj` (the hypothesis's
only consumer) is named with its type and checked against the supplied
`absorbs` (`src/ProbeLJ1119A.agda:73-79`, GREEN). The first hypotheses
the site does not supply are `levelIn` and `cover` at `Co`'s boundary,
one module boundary after `BoundedSubsetAt`. That is the abort
criterion's good stop: they are a separate dispatch.

## 4. THE C-40 SECTION

`git grep -l BoundedSubset src/` names three files. All three were
checked, one agda process at a time, and all three are GREEN:

| consumer | where it uses the master | result |
|---|---|---|
| `src/L/BoundedSubset.lagda.md` | the changed master itself | GREEN after, 3.11 s warm |
| `src/Everything.lagda.md` | imports `L.BoundedSubset` at `:374` | GREEN after, whole import closure, 2.83 s |
| `src/ProbeLJ1119A.agda` | instantiates `BS.Devlin55` and `BoundedSubsetAt` | GREEN after, 2.58 s and 2.55 s, two runs |

`Devlin55` has no instantiation anywhere else in the tree (`git grep -l
"Devlin55\|BoundedSubsetAt" src/` hits only `src/L/BoundedSubset.lagda.md`),
so the probe is the acceptance test and the C-40 list is complete.
The first check of `BoundedSubset` after the edit (cold import closure,
including `L.Condensation`) was 15.8 s; the warm runs are the table's
figures. Load 2.45 / 3.74 / 4.22, four users, at the timing runs.

## 5. CONCLUSIONS

No theorem's conclusion changed. `Devlin55.theorem :
⟨ x ∈ˢ Lset κ ⟩` (`src/L/BoundedSubset.lagda.md:1621`) is
byte-identical; the diff touches only the telescope and the one
consumer line. The only change is the hypothesis-domain move: the whole
function over every `α` and `x` becomes the single value at
`BoundedSubsetAt`'s own `α` and `x`. `levelIn`, `cover` and `sq` are
unchanged hypotheses.

The `[LJ-1.118]` site supply is now exactly what the consumer demands.
The 13-line site value (`src/ProbeLJ1118A.agda:136-155`) that could
not enter the module enters it directly: no total function over every
`α` and `x` is needed, so neither blocked route (the union-presentation
injection, or the stage shift through `stage-card-upper`) is re-attempted.

## 6. THE C-39 SECTION

No brief prohibition blocked a route; the goal route itself landed.
Prohibitions audited:

- **Do not re-attempt the union-presentation injection or the stage
  shift**: not attempted. The restriction makes the out-branch
  unreachable, because the hypothesis is now the in-branch site value
  itself.
- **Do not weaken a hypothesis to make it fit**: respected. The
  hypothesis's conclusion is unchanged; only its domain moved to the
  consumer's telescope. `Devlin55.theorem` is byte-identical
  (section 5).
- **Do not touch `src/L/Condensation*`, `src/L/Coding/` or `src/V/`**:
  no edit. `BoundedSubset` imports `L.Condensation` read-only.
- **Never `src/Everything.lagda.md`**: typechecked only as the C-40
  consumer; not edited.
- **Do not run `make check`**: not run; the individual gates of
  section 9 were run instead.
- **One agda process at a time, cap never raised**: every check ran one
  process at `GHCRTS="-A64m -I0 -M8g"`; every check returned; none was
  killed.

The door behind the [LJ-1.118] wall, per C-39: the union-presentation
injection and the stage shift are still undelivered, but the restricted
consumer no longer demands either. `levelIn` and `cover` are the next
boundary, named by this brief as a separate dispatch.

## 7. THE NEGATIVES AND THEIR STATUS

1. "`absorbs-subset` is used only at `code-inj`, at `BoundedSubsetAt`'s
   own `α` and `x`": **MEASURED TRUE**. Pre-change the name appeared at
   `src/L/BoundedSubset.lagda.md:1363-1365` and `:1532` only; the
   application is `absorbs-subset α α∉ω x x⊆Lα` with the module's own
   variables. Post-change `git grep absorbs-subset src/` finds nothing.
2. "The site supplies the restricted hypothesis": **MEASURED TRUE**.
   `P118.Site.site-inj` is the exact type, GREEN at
   `src/ProbeLJ1118A.agda:153-154`; the entry passes it as the value at
   `src/ProbeLJ1119A.agda:49`.
3. "`Devlin55` and `BoundedSubsetAt` are entered": **MEASURED TRUE**.
   The probe instantiates both (`src/ProbeLJ1119A.agda:36-56`) and the
   body elaborates through `code-inj` (`:78-79`), GREEN.
4. "The first hypothesis nothing supplies is `levelIn`/`cover`":
   **MEASURED TRUE** as the boundary: `BoundedSubsetAt`'s telescope is
   fully supplied, and `Co`'s telescope (`src/L/BoundedSubset.lagda.md:
   1409-1410`) is the next boundary. "Nothing supplies them" is
   **INFERRED** (this dispatch did not attempt them; the brief names
   them a separate dispatch).
5. "The whole `Co` body (through `theorem`) elaborates at the site":
   **INFERRED FALSE** as a claim: it needs `levelIn` and `cover`, which
   are not supplied. The body through `code-inj` is **MEASURED TRUE**
   (`src/ProbeLJ1119A.agda:78-79`).
6. "The J tower inherits the restricted module unchanged":
   **INFERRED** (no J tower exists in this tree, the same status as
   `[LJ-1.117]` section 7.4). The module is site-parameterized and
   tower-generic; a J consumer would supply the same shape at its own
   stage.

## 8. DD4

The restricted hypothesis is a weaker demand on both towers, and the
module stays generic. The change is a domain move inside one shared
master: `Devlin55`'s whole function over every `α` and `x` becomes the
single value at the consumer's own `α` and `x`, so no second statement
is introduced and the two proofs share the same signatures. The
supplied half is the same tower-generic absorption machinery
(`AbsorbsIn`, `src/ProbeLJ1118A.agda:72-130`) that names only `S`,
`Lset`, the union and injections; the [LJ-1.118] site block is
unchanged. The J half is **INFERRED** (no J tower in this tree): a J
consumer instantiates the same restricted module at its own stage with
its own absorption fact. Nothing in the change forks the shared
chapter.

## 9. GATES

- `src/L/BoundedSubset.lagda.md`: GREEN, 3.11 s warm (first check after
  the edit, cold import closure: 15.8 s), one process at the C-12 cap.
- `src/Everything.lagda.md`: GREEN, whole import closure, 2.83 s.
- `src/ProbeLJ1119A.agda`: GREEN, 2.58 s and 2.55 s, two runs, at the
  C-12 cap, one process at a time. 69 non-blank lines, 79 lines whole.
  Zero hits for `postulate`, `TERMINATING`; no holes.
- `scripts/check-fences.py --check`: clean, 87 masters.
- `scripts/lint-prose.py --check`: exit 0 on the master, the probe and
  this report.
- `scripts/lint-agda.py --check`: exit 0 on the master and the probe.
- `scripts/check-unbound-hyp.py src/ProbeLJ1119A.agda`: clean, exit 0.
- `scripts/check-probes.py --check`: clean.
- `scripts/ledger.py --brief`: standing 28,434 lines over 85 masters,
  measured from HEAD.
- Load averages: 4.08 / 4.51 / 4.54 at the first checks; 2.45 / 3.74 /
  4.22 at the timing runs. Four users.
- `make check` not run (forbidden). DD23: no mathematical prose changed
  (the diff is code only); no sentence became false.
- Working tree: `git status --short` shows only
  `src/L/BoundedSubset.lagda.md` modified. The probe is ignored by
  `.gitignore`, this report by `_build/`. HEAD `8c53fa2` unchanged. No
  commit, no push. Every agda invocation returned; none was left alive.

## 10. ARCHIVE USED

- `_build/lj-1.118-report.md`, read WHOLE. TOOK the site value
  (`Site.site-inj` at `src/ProbeLJ1118A.agda:153-154`), the two
  blocked routes, the branch decomposition, and the site table.
- `src/ProbeLJ1118A.agda`, read WHOLE. TOOK `Site.site-inj` and the
  generic `AbsorbsIn`.
- `_build/lj-1.117-report.md`, read WHOLE. TOOK the move (site ordinal
  as a module parameter), the C-40 section shape, and the conclusion
  invariant.
- `src/ProbeLJ1117A.agda`, read WHOLE. TOOK `sqω` and the restricted
  module shape.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, read the site
  block (`:1186-1233`). TOOK the fifteen site values.
- `_build/lj-1.103-report.md`, read WHOLE. TOOK the repaired premise
  context.
- `_build/lj-1.90-report.md`, read WHOLE. TOOK the entry-test shape.
- `src/L/BoundedSubset.lagda.md`, read `:1361-1627` (Devlin55 whole).
  TOOK the telescope, `code-inj` (`:1530` now), `theorem` (`:1621`),
  `levelIn`/`cover` (`:1409-1410`).
- `dev/LESSONS.md`, read WHOLE D-30 (`:3332`), C-40 (`:3602`), C-39
  (`:3521`), C-38 (`:3427`), C-35 (`:3200`), C-36 (`:3284`), D-8
  (`:1377`), D-10 (`:1316`), P-l (`:2305`), D-26 (`:1676`), P-i
  (`:203`), P-c (`:71`), P-x (`:3564`), P-h (`:174`), P-k (`:2401`),
  P-m (`:2460`), P-n (`:2483`), P-o (`:2509`), P-q (`:2633`), P-t
  (`:2601`), P-u (`:2908`), P-v (`:3037`), P-w (`:3094`), R-36
  (`:808`), R-38 (`:831`), C-31 (`:1855`), C-32 (`:2947`), C-33
  (`:2987`), C-34 (`:3171`), C-37 (`:3381`), D-29 (`:3242`), D-1
  (`:1038`), and the `--for build` and `--for rewrite` bundles via
  `scripts/rules.py`. TOOK C-38's supply standard, C-40's
  verify-consumers rule, C-39's report-the-door rule.

## 11. LITERATURE (DD18)

Banked. Spend nothing.
