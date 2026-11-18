# Actual affine Gaussian-section Green identity

`SupplementalHGaussianGreen.lean` proves the analytic signed Green identity
for bounded continuously differentiable tests with bounded derivative,
under the actual Gaussian probability law on `u⋅x=b`, with `‖u‖₂²=1`:

```
∫ (‖x‖₂²-r) f(x) dγ_section
  = (b²-1) ∫ f(x) dγ_section
    + ∫ Df(x)[x-bu] dγ_section.
```

`gaussianSection_Green` states it under the concrete pushforward law
`gaussianSectionLaw`; `gaussianSection_Green_pullback` states the identical
formula using the standard Gaussian and its actual affine section map.
The coordinate chain rule and tangent-vector decomposition are proved.
The normal derivative cancels exactly because the orthogonal projection
annihilates its unit normal. The remaining radial and normal Gaussian
integration by parts come from the checked archive. No signed trace or
quantitative surface estimate is a premise.

This supplies a smooth-test analytic step toward the first Gauss–Green
calculation in frozen Supplemental H.1. It does not identify the section
law with normalized Hausdorff surface measure, pass to hard polyhedral
indicators, prove the ridge/codimension-three boundary sums, or close the
localized H.1 surface theorem. Those steps remain open.

Reproduce from the new project with the pinned Lean toolchain on PATH:

```
python3 evidence/supplemental-h-gaussian-green/run_checkpoint.py
```

The receipt records the build, forced source compilation and strict
transitive audit of all six new theorems. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. Sources are hashed before
and after checking. Historical files remain unchanged.
