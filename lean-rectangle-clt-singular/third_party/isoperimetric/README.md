# Prékopa–Leindler source and attribution

The files below adapt Jonathan Ho's `isoperimetric` formalization:

- Upstream: https://github.com/hojonathanho/isoperimetric
- Pinned commit: `29768f8beeaf17295cdf3853d37da35d7e2b0a5f` (`release`).
- Upstream license: Apache License 2.0, reproduced in [LICENSE](LICENSE).
- Upstream toolchain: `leanprover/lean4:v4.26.0-rc2`.
- Upstream mathlib revision: `36362964cd6b6d5091319813dca81261efefac69`.

Adapted source:

- `RectangleCLTCompanion/Prekopa/Basic.lean` from `Isoperimetric/Basic.lean`.
- `RectangleCLTCompanion/Prekopa/PrekopaLeindler.lean` from
  `Isoperimetric/PrekopaLeindler.lean`.

The mathematical theorem statements and argument are preserved. Changes isolate
all declarations in `RectangleCLT.Companion.Prekopa`, update the import path,
and adapt APIs and tactic proofs to this project's pinned Lean/mathlib 4.19.
In particular, newer `grind` calls are replaced by explicit algebra and set
arguments; measure-preserving inverses and renamed ENNReal lemmas use their
4.19 interfaces. The package toolchain and mathlib revision are unchanged.

`RectangleCLTCompanion/Prekopa/ConvexCombination.lean` is a new wrapper. It
proves the usual convex-combination form by an actual Lebesgue change of
variables, then derives a real integral version for integrable nonnegative
functions. The upstream result supplies all finite dimensions, not just the
one-dimensional base case.

The backported full theorem and the wrappers were compiled with Lean 4.19;
the axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
There is no added Prékopa axiom or `sorry`.
