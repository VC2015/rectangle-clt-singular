# Actual four-edge balance at the nonsimple square vertex

The original square model has four genuine facets active at the origin
and actual normal rank three. This new source preserves that frozen model
and proves the actual four-edge normal-cone vector identity and area-norm
bound, with no parameters or supplier hypotheses in either final type.

The endpoint pairs are{0,2},{0,3},{1,2},{1,3}. Inward unit conormals are
(-1,-1,-1),(-1,1,-1),(1,-1,-1),(1,1,-1), each divided by sqrt3.
Their endpoint orthogonality and strict signs on the other generators are
proved. A nonzero polar direction annihilating two original generators
must have an adjacent pair: opposite-axis zeros would force the vector
to vanish. Adjacent zeros give exactly(-wz*sqrt3) times the corresponding
conormal, with nonnegative coefficient. This proves every needed finite
supporting-ray coverage fact instead of assuming a halfspace/balance input.

The checkpoint runs a Lake target build, forced source replay, strict26
transitive axiom audit and full26-type/314-node graph export. Types.lean
also checks both final kernel types are structurally not forall types.
Allowed axioms are exactly the standard propext/Classical.choice/Quot.sound
allowlist. Source, fixtures and every exact command log are hash-bound.

The square polygon is a constructed verification model motivated by the
arbitrary-edge discussion at supplement1101-1132. It is not an additional
printed assertion or passage count, and this packet does not prove the
final arbitrary-original-polyhedron nonsimple ridge Green/H1 theorem.
Native angular measure uses Euclidean charts and volume.toSphere.

To reproduce into fresh outputs, preserving the immutable receipt:

```sh
python3 evidence/supplemental-h-nonsimple-square-balance/checkpoint-1/run.py \
  --root "$PWD" --output /tmp/nonsimple-square-balance-fresh
```

Independent review is recorded separately. No frozen base source or
global statement/proof-environment/acceptance registry was changed.
