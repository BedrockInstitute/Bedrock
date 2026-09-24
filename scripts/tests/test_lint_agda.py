#!/usr/bin/env python3
"""Tests for scripts/gate/lint-agda.py (run: python3 scripts/tests/test_lint_agda.py)."""

import importlib.util
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = importlib.util.spec_from_file_location(
    "lint_agda", os.path.join(HERE, "..", "gate", "lint-agda.py"))
la = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(la)

OPTS = "{-# OPTIONS --cubical --safe --guardedness #-}"


def run(content, name="Test.lagda.md"):
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, name)
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
        return la.lint_file(path)


def rules(findings):
    return [(line, rule) for line, rule, _ in findings]


FAILS = 0


def check(label, got, want):
    global FAILS
    if got != want:
        FAILS += 1
        print(f"FAIL {label}:\n  got  {got}\n  want {want}")
    else:
        print(f"ok   {label}")


# 1. A clean module: multiline using, mixfix used infix, renamed target used,
#    qualified import used dotted, module-application args count as uses,
#    -syntax names exempt, public re-export exempt.
clean = f"""# T

```agda
{OPTS}

open import Base.Prelude using ( Level )

module Test {{ℓ : Level}} (lem : Level) where

open import A.B using ( Type; _∈ˢ_;
  ∃[∶]-syntax )
open import A.C renaming ( foo to bar )
import A.D
open import A.E {{ℓ}} lem using ( thing )
open import A.F public using ( unusedButPublic )
import A.G as PT

x : Type
x = bar (a ∈ˢ b) thing A.D.qux rec
  where open PT using ( rec )
```
"""

check("clean module", rules(run(clean)), [])

# An Agda fence ends on its final code line. Report one finding at the first
# trailing blank even when the run contains whitespace on several lines;
# ordinary blank lines within code and outside non-Agda fences remain valid.
trailing_blank = (f"""# T

```agda
{OPTS}

module Test where
x = x
""" + "   \n\t\n" + """
```

```text

```
""")

check("trailing blank in Agda fence", rules(run(trailing_blank)),
      [(8, "trailing-blank")])

# 2. Seeded violations, one of each kind.
bad = """# T

```agda
{-# OPTIONS --cubical --guardedness #-}
module Test where

open import A.B
open import A.C using ( used; unused )
import A.D

postulate
  oops : used

{-# TERMINATING #-}
f : used
f = {! hole !}
g = ?
```
"""

check("seeded violations", rules(run(bad)),
      [(4, "options"), (7, "bare-open"), (8, "unused-import"),
       (9, "unused-import"), (11, "forbidden"), (14, "forbidden"),
       (16, "forbidden"), (17, "forbidden")])

# 3. keep marker: on the import's own line, and on the preceding line.
kept = f"""# T

```agda
{OPTS}
module Test where

open import A.B using ( instanceOnly )  -- lint-agda: keep
-- lint-agda: keep
open import A.C
```
"""

check("keep marker", rules(run(kept)), [])

# 5. Missing OPTIONS pragma entirely.
check("missing OPTIONS", rules(run("# T\n\n```agda\nmodule Test where\n```\n")),
      [(1, "options")])

# 6. hiding alone does not satisfy the using-list discipline.
hiding = f"""# T

```agda
{OPTS}
module Test where

open import A.B hiding ( foo )
```
"""

check("hiding is bare", rules(run(hiding)), [(7, "bare-open")])

# Propositionhood is exposed through the reader-facing projection, while
# ordinary dependent-pair projections remain available.
hprop_snd = f"""# T

```agda
{OPTS}
module Test where

bad = P .snd
also-bad = (x ∈ˢ A) .snd
ordinary = pair .snd
good = ⟨ P ⟩isProp
```
"""

check("hProp snd projection", rules(run(hprop_snd)),
      [(7, "hprop-snd")])

# The zero-level qualified empty type is forbidden in Agda code. Prose,
# comments, strings and the distinct spelling Empty.⊥* do not trigger it.
empty_bottom = f"""Empty.⊥ in prose is permitted.

```agda
{OPTS}
module Test where

-- Empty.⊥ in a comment is permitted.
text = "Empty.⊥"
polymorphic = Empty.⊥*
bad : Empty.⊥
bad = ?
```
"""

check("qualified empty bottom", rules(run(empty_bottom)),
      [(10, "forbidden"), (11, "forbidden")])

# Base.Prelude alone owns open imports from the Empty module family. The
# broader Prelude-ownership rule independently rejects repeated vocabulary
# imports, including qualified aliases.
empty_open = f"""# T

```agda
{OPTS}
module Test where

open import Cubical.Data.Empty public using ( ⊥* )
open import Cubical.Data.Empty.Properties public using ( isProp⊥* )
import Cubical.Data.Empty as Empty
qualified = Empty.rec
```
"""

check("Empty open outside Prelude", rules(run(empty_open)),
      [(7, "empty-open"), (7, "prelude-import"),
       (8, "empty-open"), (8, "prelude-import"),
       (9, "prelude-import")])

prelude_empty_open = f"""# T

```agda
{OPTS}
module Base.Prelude where

open import Cubical.Data.Empty public using ( ⊥* )
```
"""

check("Empty open in Prelude", rules(run(prelude_empty_open)), [])

# Base.Prelude is the sole import boundary for its curated Cubical vocabulary.
# The rule covers open, qualified, aliased and renamed imports alike.
prelude_owned = f"""# T

```agda
{OPTS}
module Test where

open import Cubical.Data.Sigma using ( _×_ )  -- lint-agda: keep
import Cubical.Data.Sum as Sum  -- lint-agda: keep
open import Cubical.Functions.Logic renaming ( ⇔toPath to iffPath )  -- lint-agda: keep
open import Cubical.HITs.PropositionalTruncation
  renaming ( rec to localRec )  -- lint-agda: keep
```
"""

check("Prelude-owned imports", rules(run(prelude_owned)),
      [(7, "prelude-import"), (8, "prelude-import"),
       (9, "prelude-import"), (10, "prelude-import")])

prelude_nullary = f"""# T

```agda
{OPTS}
module Test where

open import Cubical.Relation.Nullary using ( Dec; yes; no; isPropDec )  -- lint-agda: keep
open import Cubical.Relation.Nullary using ( mapDec )  -- lint-agda: keep
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )  -- lint-agda: keep
```
"""

check("Prelude-owned decidability and lifting vocabulary", rules(run(prelude_nullary)),
      [(7, "prelude-import"), (8, "prelude-import"), (9, "prelude-import")])

prelude_bool = f"""# T

```agda
{OPTS}
module Test where

open import Cubical.Data.Bool using ( Bool; true; false )  -- lint-agda: keep
open import Cubical.Data.Bool using ( _≟_ )

compare = _≟_
```
"""

check("Prelude-owned Boolean vocabulary with local comparison allowed",
      rules(run(prelude_bool)), [(7, "prelude-import")])

prelude_equivalence = f"""# T

```agda
{OPTS}
module Test where

open import Cubical.Foundations.Equiv using ( _≃_; equivFun; invEq )  -- lint-agda: keep
open import Cubical.Foundations.Isomorphism using ( Iso; iso; isoToEquiv )  -- lint-agda: keep
open import Cubical.Foundations.Equiv.Properties using ( congEquiv )  -- lint-agda: keep
open import Cubical.Foundations.HLevels using ( isOfHLevelRespectEquiv )  -- lint-agda: keep
import Cubical.Foundations.Equiv as Equiv  -- lint-agda: keep
open import Cubical.Foundations.Equiv.Properties renaming ( congEquiv to pathEquiv )  -- lint-agda: keep
import Cubical.Foundations.Isomorphism using ( isoToEquiv )  -- lint-agda: keep
open import Cubical.Foundations.Equiv.Base using ( _≃_ )  -- lint-agda: keep
open import Cubical.Core.Glue using ( equivFun )  -- lint-agda: keep
open import Agda.Builtin.Cubical.Glue using ( _≃_ )  -- lint-agda: keep
open import Cubical.Foundations.Equiv  -- lint-agda: keep
open import Cubical.Foundations.Isomorphism hiding ( iso )  -- lint-agda: keep
```
"""

check("Prelude-owned equivalence vocabulary and reexports",
      rules(run(prelude_equivalence)),
      [(line, "prelude-import") for line in range(7, 19)])

prelude_owned_at_owner = f"""# T

```agda
{OPTS}
module Base.Prelude where

open import Cubical.Data.Sum public using ( _⊎_; inl; inr )
```
"""

check("Prelude-owned import at owner", rules(run(prelude_owned_at_owner)), [])

prelude_module_local_name = f"""# T

```agda
{OPTS}
module Test where

open import Cubical.Data.Sigma using ( ΣPathP )  -- lint-agda: keep
open import Cubical.Data.Sum renaming ( map to sumMap )  -- lint-agda: keep
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )  -- lint-agda: keep
open import Cubical.Foundations.Equiv using ( retEq; invEquiv )  -- lint-agda: keep
```
"""

check("proof-local names from Prelude modules",
      rules(run(prelude_module_local_name)), [])

unit_values = f"""# T

```agda
{OPTS}
module Test where

open import Cubical.Data.Unit using ( Unit; tt )  -- lint-agda: keep
open import Cubical.Data.Unit renaming ( tt* to unitWitness )  -- lint-agda: keep
```
"""

check("unit constructor imports", rules(run(unit_values)),
      [(7, "prelude-import"), (8, "prelude-import")])

# 7. Comments and strings never count as usage.
ghost = f"""# T

```agda
{OPTS}
module Test where

open import A.B using ( ghost )

{{- ghost -}}
-- ghost
s = "ghost"
```
"""

check("no ghost usage", rules(run(ghost)), [(7, "unused-import")])

for declaration in ('module Helper where', 'module Alias = Other'):
    bad_private = f'```agda\n{OPTS}\nmodule Test where\nprivate\n```\n\nLiterary text.\n\n```agda\n  {declaration}\n```\n'
    check('private module shares a line across fences: ' + declaration,
          rules(run(bad_private)), [(4, 'private-module')])
    good_private = f'```agda\n{OPTS}\nmodule Test where\nprivate {declaration}\n```\n'
    check('inline private module: ' + declaration, rules(run(good_private)), [])

private_values = f'```agda\n{OPTS}\nmodule Test where\nprivate\n  f : Set₁\n  f = Set\n```\n'
check('ordinary private value block is still allowed', rules(run(private_values)), [])

print()
if FAILS:
    print(f"{FAILS} test(s) failed")
    sys.exit(1)
print("all lint-agda tests passed")
