# Supplemental H.1 weighted ridge cancellation

This checkpoint proves the actual coefficient cancellation in frozen
supplement lines 1044–1084 at paper commit
`1803366cc994d9facae8e128ee180f68e319486f`.
`SupplementalHSurfaceGeometry.lean` defines the two unit facet conormals,
identifies their summed inner product with the archived paired ridge
coefficient, and proves

```
abs (abs (u⋅z) * (n_v|u⋅z) + abs (v⋅z) * (n_u|v⋅z))
  ≤ 2 * arccos (u⋅v) * ‖z‖².
```

The estimate is first obtained with the smaller chord factor `‖u-v‖`.
The chord-to-angle comparison is proved from the actual arccosine angle;
no inverse angular gap is an assumption. Both normals are unit and are
neither equal nor antipodal, exactly as for the linearly independent
normals at an actual ridge.

The final endpoint `supplementalH_weighted_ridge_pair_radius_le` takes two
members of the actual signed face family and evaluates all coefficients
at the original point `g`. Orthogonal projection onto their span retains
the inner products, and the checked three-face radius bounds that
projection. Thus its right side is the actual `2 θ R(g)^2` in the paper.

This does not establish the Hausdorff Gauss–Green identities, the
codimension-three spherical balance, or the localized normal-cone volume
comparison. H.1's complete surface estimate remains open.

Reproduce from the new project, with the pinned Lean toolchain on PATH:

```
python3 evidence/supplemental-h-surface-geometry/run_checkpoint.py
```

The receipt records an actual build, forced compilation and strict
transitive audit of all six new theorem endpoints. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Sources are hashed
before and after the run. This checkpoint leaves historical sources and
receipts intact.
