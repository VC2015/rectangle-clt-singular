# Spherical balance in Supplemental H.1

The three new `SupplementalHSpherical*.lean` modules prove the spherical
balance for the actual cone cut out by any finite family of unit,
pairwise nonparallel normals in three-dimensional Euclidean space.
The inward-normal convention gives the positive sign; outward normals
give the negative sign. The resulting norm is at most twice the area
of the actual spherical cone section, with no dependence on facet count.

Each edge coefficient is the angular measure of the actual planar facet
cone in an orthogonal chart, rather than a supplied numerical weight or
an assumed boundary functional. Exact polar integration identifies this
coefficient with its actual unnormalized Gaussian surface mass. The
independently proved hard-polyhedron Gaussian boundary identity then
supplies the signed cancellation. The radial coefficients are proved to
be exactly 2 in dimension three and 1 in dimension two.

`SupplementalHSphericalSectors` proves that the angular measure of an
ordinary complex-plane argument arc `(a,b)` is `b-a`, and that the arc of
width `arccos c` has measure `arccos c`, including degenerate endpoints.
The angular and spherical measures use Euclidean-volume polar
normalization (`volume.toSphere`). No equality to mathlib's
diameter-normalized raw Hausdorff measure is asserted. A comparison with
the manuscript's conventional Hausdorff notation must retain this
normalization distinction.

`run.py` records a local module build, forced elaboration of each owned
source, and the strict theorem axiom audit. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. `source-freeze.json`
also binds the three new Gaussian-boundary dependency sources, package
manifest, and toolchain. This evidence concerns the spherical balance;
it does not claim completion of all of Supplemental H.1 or the paper.
