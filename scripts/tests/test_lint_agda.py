#!/usr/bin/env python3
"""Tests for scripts/lint-agda.py (run: python3 scripts/tests/test_lint_agda.py)."""

import importlib.util
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = importlib.util.spec_from_file_location(
    "lint_agda", os.path.join(HERE, "..", "lint-agda.py"))
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

# 3. Everything is exempt from B and C (but not A).
everything = f"""# E

```agda
{OPTS}
module Everything where

import A.B
import A.C
```
"""

check("Everything exempt", rules(run(everything, name="Everything.lagda.md")), [])

# 4. keep marker: on the import's own line, and on the preceding line.
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

print()
if FAILS:
    print(f"{FAILS} test(s) failed")
    sys.exit(1)
print("all lint-agda tests passed")
