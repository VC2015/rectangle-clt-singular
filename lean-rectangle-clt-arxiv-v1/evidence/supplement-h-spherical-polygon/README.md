# Finite spherical-polygon support packet

This frozen packet contains exactly three modules: generated-cone support
faces(7 public declarations), tangent-chart angular identification(9), and
arbitrary-edge signed vector balance(13). All29 declarations are mapped once.

The final theorem retains an explicit GEOMETRIC completeness equivalence:
a point belongs to the actual finite generated cone iff every listed
inward conormal has nonnegative inner product with it. The unit/endpoint,
zero and strict support incidences are also explicit. No balance formula,
angular mass identity or spherical-area estimate is an input.

This does not yet instantiate every original nonsimple polyhedral face,
prove the printed nonsimple ridge Green identity, or promote final H1.
New Polar/Dual/Conormal/Coverage modules are separate active support and
are not part of this source freeze. The motivating source is
supplement1101-1132. The proof uses actual Gaussian cone integration by
parts and polar integration in place of a manifold-divergence primitive.
Surface angular measures use native orthonormal Euclidean charts and
volume.toSphere; raw unnormalized Hausdorff identification is not claimed.

The authoritative checkpoint is checkpoint-2/run.json: Lake build, all
three exact-path source replays, strict29 axioms and full29 types/232 closed
project nodes all pass. Only propext, Classical.choice and Quot.sound are
allowed. Exact source/fixture/command-log hashes are bound in the receipt.

checkpoint-1 is preserved unchanged. All six Lean commands there also
exited zero; a later Python metadata assertion failed because it searched
for the printed binder name hhalf, which pretty-printing omitted.
checkpoint-2 instead checks the structural generated-cone/Iff type.
The three Lean sources and both Audit/Types fixtures are byte-identical
between the attempts. No mathematical or kernel check was repaired.

For fresh reproduction, use the exact argv/cwd list and Audit/Types
fixtures recorded in checkpoint-2, placing any fresh logs in a new output
directory. Do not rerun the preserved fixed-output historical driver over
either immutable checkpoint. Independent review is recorded separately.
