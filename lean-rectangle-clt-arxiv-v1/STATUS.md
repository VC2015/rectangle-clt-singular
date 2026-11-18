# Verification status

Ten of the 40 named results are proved and freshly checked in the concrete probability models recorded by their expanded Lean types:

| Paper statement | Checked endpoint(s) in `RectangleCLTArxivV1` |
|---|---|
| Theorem 1 | `theorem_1_intrinsic_clt` |
| Corollary 1 | `corollary_1_normalized_observations` |
| Lemma 1 | `lemma_1_bounded_model`, `lemma_C1_gaussian_model` |
| Lemma 2 | `lemma_2_smoothing_error` |
| Proposition 1 | `proposition_1_intrinsic_derivatives` |
| Lemma A.1 | `integral_logisticEnvelope_intrinsic`, `averaged_translated_derivative_intrinsic` |
| Lemma B.3 | `gaussian_mean_relative_to_single_face` |
| Lemma B.4 | `logistic_matrix_estimate_intrinsic`, `selector_nuclear_bound_intrinsic_paper` |
| Lemma C.1 | `lemma_C1_rademacher_boundary`, `lemma_C1_rademacher_maximum` |
| Lemma C.2 | `lemma_C2_expected_maximum` |

The clean checkout at proof commit `6d28758` passed 51 commands: the project build, fresh elaboration of its entire exported import closure, 78 transitive axiom checks, the pinned 54-declaration chaining audit, and mapped type/dependency exports. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The kernel graph has no dependency on the archived final bounded or polynomial CLT. See `evidence/intrinsic-clean-checkpoint-2/` and `correspondence/intrinsic-acceptance.json`. The earlier clean attempt was interrupted by a broken output pipe; its failed receipt is preserved.

Independent reading-order reviews bind the checked statements and 33 accepted printed passages to the frozen sources and PDFs. Statement correctness and complete passage coverage have separate ledger fields: detailed internal passage bindings for Lemmas 1, 2, B.4, C.1 and the normalization paragraph remain explicit follow-up work. The helper-name collision under combined imports was fixed and rechecked. The literal A.1/common-threshold integration argument supersedes the earlier numerical variant, whose history is retained.

Theorem 2's two new width-sensitive proofs compile and are undergoing their own audits and independent review. Its statement row remains open until that evidence is bound. New supporting proofs cover actual Gaussian additions, conditional covariance restoration, two-count lower-bound families, and parts of Supplemental G–H. They do not certify the remaining 30 named results or unreviewed passages. The two-face concentration/restoration chain, localized surface argument, lower-detection calibrations and Supplemental I remain open. Conjecture 1 is excluded.

The archived 31 statements and 253 accepted passages concern the earlier November 7 manuscript. Its files and historical receipts remain unchanged. Fresh archive replay is recorded separately. Positive-integer derivative orders are preserved. `REPRODUCIBILITY.md` explains collaborator access to the private chaining dependency and the scope of each checkpoint.
