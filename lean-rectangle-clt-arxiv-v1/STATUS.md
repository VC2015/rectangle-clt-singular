# Verification status

Twenty-two of the 40 named results are proved and freshly checked in the concrete probability models recorded by their expanded Lean types:

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
| Theorem 2 | `theorem_2_i_intrinsic`, `theorem_2_ii_intrinsic`, `theorem_2_intrinsic_with_min` |
| Lemma B.5 | `lemma_B5_intrinsic_threshold` |
| Lemma E.2 | `lemma_E2_intrinsic_comparison` |
| Lemma E.3 | `lemma_E3_intrinsic_smoothing` |
| Lemma E.4 | `lemma_E4_paired_slepian` |
| Lemma E.5 | `lemma_E5_truncated_bennett_maximum`, `lemma_E5_truncated_bennett_maximum_zero_variance` |
| Corollary 2 | `corollary_2_intrinsic` |
| Corollary 3 | `corollary_3_intrinsic` |
| Theorem 4 | `theorem4_bounded_symmetric_lower` |
| Theorem 5 | `theorem_5_fourth_moment_two_sided` |
| Theorem 6 | `theorem_6_growing_fourth_moment_lower` |
| Theorem 7 | `theorem_7_polynomial_envelope_lower`, `theorem_7_fixed_envelope_fourth_lower` |

The clean checkout at proof commit `6d28758` passed 51 commands: the project build, fresh elaboration of its entire exported import closure, 78 transitive axiom checks, the pinned 54-declaration chaining audit, and mapped type/dependency exports. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The kernel graph has no dependency on the archived final bounded or polynomial CLT. See `evidence/intrinsic-clean-checkpoint-2/` and `correspondence/intrinsic-acceptance.json`. The earlier clean attempt was interrupted by a broken output pipe; its failed receipt is preserved.

The subsequent clean checkout at proof commit `436b91f` passed all 76 commands, including 61 fresh source elaborations, 90 exported transitive axiom checks, the pinned 54-declaration chaining audit, and 92 endpoint exports. A separate clean-environment harness checked all 104 declarations mapped by the new passage ledgers, with the same axiom allowlist. Its 4,778-node project dependency graph contains neither archived final bounded nor polynomial CLT. See `evidence/theorem2-clean-checkpoint/`, `evidence/theorem2-clean-mapping/`, and `correspondence/theorem2-acceptance.json`.

The clean checkout at proof commit `94b7330` then passed all 128 commands, including 112 fresh source elaborations, 100 exported axiom checks, the chaining audit, and 102 endpoint exports. Its 7,896-node dependency graph again excludes both archived final CLTs. A separate clean-environment harness checked 109 passage declarations and their axioms. See `evidence/transfers-lower-clean-checkpoint/`, `evidence/transfers-lower-clean-mapping/`, and `correspondence/transfers-lower-acceptance.json`.

Independent reading-order reviews bind the checked statements and 114 mapped passages to the frozen sources and PDFs. Four Corollary 2 passages have explicit local proof variations: Fatou at the exact Orlicz endpoint, an exponential Taylor moment bound, a sufficient variance ratio, and larger universal numerical constants. The unused printed layer-cake equality and sharper numerical ratio are not separately claimed. Corollary 3 has complementary independent reviews of all seven modules. Theorems 4–7 use actual finite independent symmetric observations, genuine moment membership and Gaussian-width limits, including rank one. Theorem 5 also has its matching upper bound from the new Theorem 2.

Statement correctness and complete passage coverage have separate ledger fields. Detailed internal bindings for Lemmas 1, 2, B.4, B.5, C.1, E.3, the normalization paragraph and parts of the lower-family proof remain follow-up work. The literal A.1/common-threshold argument supersedes the earlier numerical variant, whose history is retained.

Theorems 3 and 8 have passed targeted builds and axiom audits; their integrated clean checkpoint is pending. Supporting proofs cover actual two-face concentration and parts of Supplemental G–H. These checks do not certify the remaining 18 named results or unreviewed passages. The complete complementary-restoration chain, localized surface argument and Supplemental I remain open. Lemma E.1 has a separately proved nonnegative-budget qualification; its unrestricted-real-budget reading is not claimed. Conjecture 1 is excluded.

The archived 31 statements and 253 accepted passages concern the earlier November 7 manuscript. Its files and historical receipts remain unchanged. Fresh archive replay is recorded separately. Positive-integer derivative orders are preserved. `REPRODUCIBILITY.md` explains collaborator access to the private chaining dependency and the scope of each checkpoint.
