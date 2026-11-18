# Actual nonsimple ridge Gauss–Green analytic handoff

All seventeen `SupplementalHNonsimpleRidgeGreen*.lean` sources listed in
`correspondence/supplemental-h-nonsimple-ridge-green-passages.json` are stable.
No Root/Audit, frozen legacy ledger, staging or commit changes were made by
this packet. The new ledger records 92 distinct checked explicit declarations;
its seventeen source bindings overlap the single printed span 1081–1100 and
are not seventeen additional paper statements.

The final import is:

```lean
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenActual
```

The exact public endpoint is
`hardGaussianSignedRidgeTerm_Green_actualFace u b hi hw hu j l hjl R hR`.
Here `hi` is an actual strict interior, `hw` gives actual deleted-inequality
witnesses, `hu` gives unit original normals, `j ≠ l`, and `R` is the complete
actual rank-two face with active set `{j,l}`. In ambient dimension `n+1`, it proves:

```text
nativeSigned(j,l)
  = actualLeading(R)
    - Σ H : actual rank-three faces,
        actualAngle(R) * (<z_H, actualIncidenceConormal(R,H)> * rho_H).
```

The actual incidence conormal is zero off incidences. Every true coface is
counted exactly once by the independently checked selected-facet/coface
bijection, including faces with more than three active facets. The theorem
constructs its exact irredundant tangent presentation internally. There is no
generic-threshold, AE-threshold, limiting, surface estimate or Green-identity
premise.

The analytic route applies radial Gaussian Green to an exact irredundant
retained tangent presentation. It restores every original constraint
pointwise before identifying the full-event Gaussian mass. Frame rank and
supporting levels identify the actual normal point and canonical complete-face
mass; unit norm, ridge orthogonality and positive orientation identify the
actual conormal. Nonactual pairs vanish by genuine Gaussian hyperplane nullity.
The leading term has its separate exact q2 frame/mass proof.

Final checkpoints:

- `integrated/checkpoint-1/receipt.json`: ten analytic core sources,
  59 declarations, closed 300-node graph, 352 recursive source identities.
- `frame/checkpoint-1/receipt.json`: eight frame declarations.
- `conormal/checkpoint-1/receipt.json`: three orientation/uniqueness declarations.
- `leading/checkpoint-1/receipt.json`: twelve q2 declarations.
- `canonical/checkpoint-1/receipt.json`: two canonical adapter sources,
  six declarations, closed 193-node graph, 362 recursive source identities.
- `actual/checkpoint-1/receipt.json`: two selected/full-H assembly sources,
  four declarations, closed 480-node graph, 377 recursive source identities.

All module builds, owned-source re-elaborations, strict axiom audits and full
explicit type exports passed. Only `propext`, `Classical.choice` and `Quot.sound`
are used. The integrated/canonical/actual child semantic reviews are saved in
the respective directories and disclose imported support authorship. Root is
independently reviewing the child's seven supporting bodies. Separate selected
geometry review is
`evidence/supplemental-h-nonsimple-face-selected/independent-archive-review.json`.

Root owns the global half-ordered-pair count and signed incidence regrouping;
bounded owns the complete actual-face and arbitrary-edge cone bridge. Those
are separate source scopes. This packet does not itself change historical H1
acceptance metadata. It uses the existing orthogonal-chart Gaussian surface
measure convention and does not separately identify raw unnormalized Mathlib
Hausdorff measure with that convention.
