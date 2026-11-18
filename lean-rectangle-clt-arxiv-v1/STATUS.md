# Verification status

The exported checkpoint proves the bounded-sum expected-maximum inequality
of Lemma C.2 through `RectangleCLTArxivV1.lemma_C2_expected_maximum`.
Its constant is chosen before the probability space, dimensions, array,
envelope and covariance factor. The proof includes positive dimension one,
singular covariance and perfect correlations. A covariance factor is
constructed from the actual bounded array; the mixed-tail inequality and
Gaussian comparison are proved dependencies, not extra theorem premises.

The seven modules exported by `RectangleCLTArxivV1.lean` implement passages
C2.1–C2.7 in reading order. `Audit.lean` checks their transitive axioms;
`Correspondence/C2.lean` exposes the actual input fields and mapped types;
`Correspondence/Dependencies.lean` exports the kernel proof dependencies.
The managed fresh and clean-checkout evidence is recorded separately from
the initial interactive compilation logs. Passage acceptance in the JSON
ledgers also requires the independent frozen-source/PDF review.

The remaining 39 named results and the substantive passages in the main
paper and supplement remain open in the correspondence ledger. Intrinsic
concentration, smoothing, interpolation, transfer and width-calibration
modules outside the exported import chain are ongoing work until their
own checks and correspondence are recorded. Conjecture 1 is excluded.

The archived 31 statements and 253 accepted passages concern the earlier
November 7 manuscript. They are reusable inputs, not automatic certificates
for this release. The archived positive-integer derivative-order restriction
is preserved. See `REPRODUCIBILITY.md` for dependency access and the precise
scope of a checkpoint run.
