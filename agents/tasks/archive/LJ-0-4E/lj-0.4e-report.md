# LJ-0.4e: compression blocks E and G

Status: COMPLETE. Both blocks refused on measurement. No commit, no push.
The working tree is as this report describes. My six files are unchanged from
HEAD. The two kit modules I built were deleted after measurement.

## Block E: the FOL/Manipulation traversal share

### 1. THE NUMBER

The kit was built and the three instances were wired, then reverted. The
counts are the ledger caliber: non-blank lines inside ```agda fences,
`scripts/ledger.py`'s own count with `at_head=False`.

| File | Before | After | Delta |
|---|---:|---:|---:|
| FOL/Manipulation/Walk (new kit) | 0 | 31 | +31 |
| FOL/Manipulation/Renaming | 67 | 66 | -1 |
| FOL/Manipulation/Relabelling | 108 | 102 | -6 |
| FOL/Manipulation/Relativize | 76 | 71 | -5 |
| **E net** | 251 | 270 | **+19** |

The measured band is minus 60 to minus 120 (`_build/l3.32-t208-report.md`
3.5). The band does not hold. The net is plus 19.

### 2. SECONDS

The owner's hard bar is seconds. The intermediate build checked with flat
seconds. One Agda process at a time under `GHCRTS="-A64m -I0 -M8g"`.

| File | Before (s) | After, kit build (s) | Exit |
|---|---:|---:|---:|
| FOL/Manipulation/Walk | n/a | 0.45 | 0 |
| FOL/Manipulation/Renaming | 1.36 | 1.01 | 0 |
| FOL/Manipulation/Relabelling | 0.53 | 0.55 | 0 |
| FOL/Manipulation/Relativize | 0.51 | 0.52 | 0 |

After the revert, the files are at HEAD. The after state equals the before
state.

### 3. WHAT I SHARED

I built `FOL.Manipulation.Walk`: a module-parameterized traversal skeleton.
It is one direct recursion over the twelve constructors. The parameters are
the state family, the binder step, the target arity, the term map, and the
four binder clauses. I wired three instances: `renameFo`, `mapFo`, and
`relativize`. All three files checked, exit 0.

The S17 boundary holds. The skeleton stores no decomposition and proves no
fusion lemma. The recursion reduces exactly as the inline form does
(`dev/memos/simplification-register.md:37`).

The stop reason is the line meter. The kit costs 31 lines. The three
instances save 12. The net is plus 19. A handler-based kit saves only the
type signature and the recursion header, about two to four lines per
instance. The correctness lemmas (`⊨-rename`, `⊨-map`, `relativize-correct`,
`⊨-place`) cannot share: their clause bodies are the content, and a kit
handler is as long as the clause it replaces. The survey's own note agrees
that the correctness lemmas do not share (`_build/cone-audit.md` B3).

### 4. WHAT THE WING COULD INSTANTIATE (DD4)

The kit serves any syntax-to-syntax traversal: a map over constants, a
renaming, a relativization. The wing's clauses move formulas between
carriers, and each such move is an instance. The kit's cost is one module,
and the wing would not re-derive the recursion.

### 5. CONSUMERS RE-VERIFIED

None changed. The intermediate build changed the bodies of `renameFo`,
`mapFo`, and `relativize` only. The definitions kept their names and their
transparent behavior. I did not re-verify consumers for a build that was
reverted. The consumers are `L/Axioms/Full` (Renaming, Relativize),
`L/Hull`, `L/Coding/Uniform`, `L/Coding/Recover`, `L/Coding/Bridge`,
`L/Coding/InL`, `L/Coding/Powerset`, `L/Coding/CodeSet`, `L/Coding/Model`,
`L/Coding/Base`, `L/Coding/Shape`, `L/Definability`, `L/Choice/Internal`,
`L/Choice/Adequate`, `L/Absoluteness`, `L/Ordinal/Stages`,
`L/Axioms/Separation`, and `L/ReflectFo`. None needs a re-check, because
none changed.

## Block G: the lex-order kit

### 1. THE NUMBER

The kit was built and typechecked, then reverted. The instances were priced
against the kit before wiring, because the arithmetic was already negative.

| File | Before | After | Delta |
|---|---:|---:|---:|
| L/Choice/Lex (new kit) | 0 | 111 | +111 |
| L/Choice/Name, vector suite | 64 | about 43 | about -21 |
| L/Choice/Name, name suite | 82 | about 41 | about -41 |
| **G net** | 146 | about 195 | **about -49** |

The measured band is minus 40 to minus 80 (`_build/lj-0.4-compression.md` 3,
N6). The band does not hold. The net is about minus 49.

### 2. SECONDS

| File | Before (s) | After, kit build (s) | Exit |
|---|---:|---:|---:|
| L/Choice/Lex | n/a | 1.57 | 0 |
| L/Choice/Name | 1.29 | not wired | n/a |

The kit typechecks fast because its content is parameterized
(`dev/LESSONS.md` P-m). The instances were not wired, so their seconds were
not measured. Their check class is the same parameterized class, because the
relations stay sums and nothing unfolds the limit order.

### 3. WHAT I SHARED

I built `L.Choice.Lex`: a module-parameterized lexicographic product over a
dependent family, with the four laws. The second-key comparison is stated
across the family, so an equality of first keys never transports the second
key's data. The relation uses the reversed equality convention, matching
`_≺ₙ_`'s load-bearing shape. A normal variant is derived by a flip for
`_≺ᵥ_`. The well-foundedness goes through generically: the construction
recurses on the first key's accessibility through `WFI.induction`, with the
second key's full well-foundedness supplying the arbitrary replacements.
This resolves the risk the brief names. The accessibility proof does go
through generically.

The stop reason is the line meter. The kit costs 111 lines. The two suites
it replaces measure 146 lines. The instances cost about 85 lines by my
pricing. Three constraints force the kit to carry machinery the instances
would otherwise carry. First, `_≺ᵥ_` and `_≺ₙ_` use opposite equality
conventions, and both shapes are load-bearing in consumers
(`Internal.lagda.md:1047-1100` constructs `_≺ᵥ_` evidence with `x ≡ y`;
`Internal.lagda.md:1343-1359` pattern-matches `_≺ₙ_` evidence with
`codeOf b ≡ codeOf a` and `arity b ≡ arity a`). The kit must serve both
conventions, which doubles the relation and the law suite. Second, the
name's second key is dependent (`Vec k` depends on the arity), so the tri
and the wf need the transport machinery: the stability argument and the pair
path. Third, the vector's laws are self-recursive, so the kit's laws take
the component laws as per-call arguments. The instances then write the same
glue the direct proofs wrote.

### 4. WHAT THE WING COULD INSTANTIATE (DD4)

The kit serves any lexicographic product whose first key is well-ordered:
the step order at a successor stage, a two-key order on a family, the wing's
name orders. The generic well-foundedness is the part a later route would
otherwise re-derive. The brief's rule stands: a stop-line is never a reason
to write fixed. The stop is a price, not a refusal of the generic form.

### 5. CONSUMERS RE-VERIFIED

None changed. The kit was reverted before wiring the instances. The
consumers of `L/Choice/Name` are `L/Choice/Internal`, `L/Choice/Adequate`,
`L/Choice/Order`, and `L/Choice/Step`. None needs a re-check, because none
changed.

## ARCHIVE USED

- `dev/memos/simplification-register.md:37` (S17): the RED probe. A stored
  decomposition walled at 12 GB; the inline form ran in one second. I read
  it before designing. The walk is a direct structural recursion with no
  stored decomposition and no fusion lemma.
- `_build/l3.32-t208-report.md` 3.5 (lever e): the measured sites,
  `Renaming` 13-25 and `Relabelling` 15-27, and the delivered comparable
  `_build/cone-audit.md` B3. The comparable prices the traversals at about
  a third of the mass and notes that the correctness lemmas do not share.
- `_build/lj-0.4-compression.md` 3 (N6) and 5 (blocks E and G): the bands
  and the well-foundedness risk named for G.
- `_build/lj-0.4a-report.md` 6 (item 3): P-k note on spec lemmas. No
  consumer site in my files needed a new spec lemma.
- `dev/LESSONS.md` via `scripts/rules.py --for build`: C-12, C-22, P-h,
  P-m, P-q, P-r, D-10. I ran one Agda process at a time under `-M8g`. I
  wrote the deliverable incrementally. I re-verified the sites before
  pricing.

## WHAT I AM NOT SURE OF

1. The G instance price, about 85 lines, is a design price, not a
   measurement. I did not wire the instances, because the kit's measured 111
   lines made the net negative even at the optimistic end of the price. An
   orchestrator who wants the exact number can fund the wiring.
2. The band failure is specific to this tree. The recon's numbers were site
   counts and delivered comparables, not measurements at these sites
   (`dev/LESSONS.md` P-l). A later tree with more lex orders or more
   traversals could amortize the kits.
3. The E intermediate build's seconds are within noise of the before
   seconds. The honest reading is flat, not faster.
4. The `Walk` and `Lex` modules were deleted. Their prose was linter-clean,
   but no gate saw them together with the instances.
