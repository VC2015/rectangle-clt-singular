# Actual nonsimple spherical geometry adapter

All six new sources compile. The five coordinate sources pass a 61-target strict/type/dependency audit with 440 project nodes; the separate printed-name wrapper passes a four-target audit with 429 project nodes. Both complete kernel axiom unions contain only `propext`, `Classical.choice`, and `Quot.sound`.

Import `RectangleCLTArxivV1.SupplementalHNonsimpleFacePrintedSpherical` for the choice-free public endpoints:

- `nonsimpleActualConormalSum_eq_spherical_vector u b hi hw hu H`
- `nonsimpleActualConormalSum_norm_le_spherical_area u b hi hw hu H`

The hypotheses are the ordinary original finite unit-normal family, strict interior and irredundant witnesses, and an actual codimension-three face `H`. There is no generic-threshold, simplicity, coverage, cone-presentation or conormal-sign premise. Every original active facet and every actual ridge incidence is included. Original endpoint angles are derived from the exact two-facet property of actual ridges, and the full actual-ridge sum is reindexed without multiplicity.

`nonsimpleFaceCoordinateLift` is the canonical isometry from the complete H-normal space coordinates into the ambient Euclidean space. Its range, equality with the root orthonormal-frame isometry, coordinate inverse and normal-point identity are checked. `nonsimpleActualNormalCone_eq_incident_halfspaces` identifies the genuine `tripleOutwardNormalCone` by explicit coefficient reindexing; its closedness and measurability follow. `nonsimpleFaceCoordinateCone_facet_angle` proves the actual angular facet mass equals the original normal angle.

The geometry and vector identity implement supplement1101–1110 and1124–1132. The imported generic balance has an equivalent Gaussian hard-threshold first-moment proof. This packet does not separately implement the spherical tangent-field/Laplacian/divergence calculation at1112–1123 and does not assert the global nonsimple J_e Green identity at1081–1100. That analytic assembly is a separate task. The Euclidean `volume.toSphere` convention is retained explicitly.

Exact source, TeX-span and receipt hashes are in `source-freeze.json`. Core receipt: `checkpoint-1/run.json`. Wrapper receipt: `../supplemental-h-nonsimple-face-printed-spherical/checkpoint-1/run.json`. The earlier cone and polar-line packets remain unchanged. No Root, Audit, frozen passage ledger, registry, staging or commit was changed by this leaf.
