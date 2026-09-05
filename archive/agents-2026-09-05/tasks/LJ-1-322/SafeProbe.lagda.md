# LJ-1.322 safe-flag probe

This probe answers ONE question: does `--no-syntactic-equality` co-exist with
`--safe`? The same question is asked for `--lossy-unification`. The module
carries the same OPTIONS header as `src/L/Condensation.lagda.md:4`, and the
flags go on the command line. The module body is empty, so a red result comes
from the option check and from nothing else.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

module LJ-1-322.SafeProbe where
```
