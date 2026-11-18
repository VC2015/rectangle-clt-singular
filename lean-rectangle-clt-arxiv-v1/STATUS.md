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
The clean-checkout run at proof commit
`5c97b31eead19bae45a737050712a8fbd5c4fbe9` passed all 18 commands, including
fresh elaboration of the seven modules, 56 transitive axiom checks, the
54-declaration chaining audit, and 58 expanded endpoint types. The kernel
dependency graph has 628 project nodes and no dependency on the archived
final bounded or polynomial CLT theorem. The independent reading-order
review passed C2.1–C2.7 against frozen main PDF pages 77–78.

The JSON ledgers therefore record one checked named statement and seven
checked printed passages. Evidence is in `evidence/c2-clean-checkpoint/`,
`evidence/c2-review/`, and `correspondence/c2-acceptance.json`. Initial
interactive logs and the preliminary dirty-workspace run are separate
development evidence and are not the acceptance receipt.

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
