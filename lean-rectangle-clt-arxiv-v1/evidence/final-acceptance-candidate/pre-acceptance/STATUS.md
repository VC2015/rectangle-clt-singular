# Verification status

Thirty-three of the 40 named results are proved and freshly checked in the concrete probability models recorded by their expanded Lean types. Lemma E.1 is separately proved with an explicit nonnegative envelope-budget qualification.

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
| Theorem 3 | `theorem_3_intrinsic`, `theorem_3_intrinsic_positive_dimensions` |
| Theorem 8 | `theorem_8_sparse_polynomial_moment_lower`, `theorem_8_sparse_polynomial_moment_two_sided` |
| Lemma B.1 | `lemma_B1_gaussian_seed_interpolation` |
| Lemma B.2 | `lemma_B2_intrinsic_paired_restoration` |
| Lemma F.1 | `lemma_F_1_uniform_scalar_moderate_tail` |
| Lemma F.2 | `lemma_F_2_independently_shifted_variables` |
| Lemma F.3 | `lemma_F_3_common_symmetric_construction` |
| Supplemental one-/two-face concentration | `cap_one_projection_small_interval_nonneg`, `cap_two_projection_small_box_nonneg` |
| Proposition G.1 | `proposition_G1_dimension_log_cap_normalized` |
| Lemma G.3 | `cap_seededFourthRemainder_rank_complementary_bound`, `cap_seededFourthRemainder_rank_abs_intervalIntegrable` |
| Lemma H.2 | `lemma_H2_gaussian_matrix`, `lemma_H2_projected_reference` |

The clean checkout at proof commit `6d28758` passed 51 commands: the project build, fresh elaboration of its entire exported import closure, 78 transitive axiom checks, the pinned 54-declaration chaining audit, and mapped type/dependency exports. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The kernel graph has no dependency on the archived final bounded or polynomial CLT. See `evidence/intrinsic-clean-checkpoint-2/` and `correspondence/intrinsic-acceptance.json`. The earlier clean attempt was interrupted by a broken output pipe; its failed receipt is preserved.

The subsequent clean checkout at proof commit `436b91f` passed all 76 commands, including 61 fresh source elaborations, 90 exported transitive axiom checks, the pinned 54-declaration chaining audit, and 92 endpoint exports. A separate clean-environment harness checked all 104 declarations mapped by the new passage ledgers, with the same axiom allowlist. Its 4,778-node project dependency graph contains neither archived final bounded nor polynomial CLT. See `evidence/theorem2-clean-checkpoint/`, `evidence/theorem2-clean-mapping/`, and `correspondence/theorem2-acceptance.json`.

The clean checkout at proof commit `94b7330` then passed all 128 commands, including 112 fresh source elaborations, 100 exported axiom checks, the chaining audit, and 102 endpoint exports. Its 7,896-node dependency graph again excludes both archived final CLTs. A separate clean-environment harness checked 109 passage declarations and their axioms. See `evidence/transfers-lower-clean-checkpoint/`, `evidence/transfers-lower-clean-mapping/`, and `correspondence/transfers-lower-acceptance.json`.

Independent reading-order reviews bind the checked statements and 114 mapped passages to the frozen sources and PDFs. Four Corollary 2 passages have explicit local proof variations: Fatou at the exact Orlicz endpoint, an exponential Taylor moment bound, a sufficient variance ratio, and larger universal numerical constants. The unused printed layer-cake equality and sharper numerical ratio are not separately claimed. Corollary 3 has complementary independent reviews of all seven modules. Theorems 4–7 use actual finite independent symmetric observations, genuine moment membership and Gaussian-width limits, including rank one. Theorem 5 also has its matching upper bound from the new Theorem 2.

Statement correctness and complete passage coverage have separate ledger fields. The bounded/Gaussian proof of Lemma 1, Corollary 1 normalization and Lemma 2 now have 29 independently reviewed passage bindings. Their 124-declaration strict audit and source replay used the current hashed checkout; the new namespace source bytes match the clean Supplement G checkout. Historical stale receipts are preserved. See `evidence/early-correspondence/` and `correspondence/early-passages-acceptance.json`. This selected review makes no q0 derivative claim. Detailed internal bindings for B.4, B.5, C.1, E.3 and parts of the lower-family proof remain follow-up work. The literal A.1/common-threshold argument supersedes the earlier numerical variant, whose history is retained.

The clean checkout at `ec635a0` passed all 161 commands: the build, 145 fresh source elaborations, 119 exported axiom checks, the chaining audit, and 121 endpoint exports. The clean extension at `bc848e5` preserved every base source byte and freshly built/forced two further support modules. Its 273-declaration passage audit passed with the same three-axiom allowlist. See `evidence/main-results-clean-checkpoint/`, `evidence/main-results-clean-mapping/`, and `correspondence/main-results-acceptance.json`.

That checkpoint recorded 206 accepted passage correspondences, including 19 explicitly documented method variations. These include the actual C4 Taylor-operator form of two B.1 steps, two equivalent F.1 intermediates, the quantitative Fourier/kernel route for the projection lemma, and the finite-moment cap-limit argument for H.2. The pre-acceptance versions of the new ledgers are preserved. Lemma E.1 and its eight passages are counted separately: the envelope budget A must be nonnegative, and a checked obstruction refutes the unrestricted-real-budget reading.

The clean Supplement G checkout at `5e51788` passed all 212 commands. Its complete clean-environment passage audit checked 116 declarations and their transitive axioms, with a 3,997-node project graph. The initial 94-declaration mapping is retained as historical evidence; the complete audit includes the unqualified CamelCase names used by the signed-restoration ledger. See `evidence/supplement-g-clean-checkpoint/`, `evidence/supplement-g-clean-mapping-complete/`, and `correspondence/supplement-g-acceptance.json`.

Proposition G.1 now uses the exact printed normalized fourth remainder and its actual absolute time integral. Lemma G.3 constructs a minimal covariance factor internally and proves the complementary bound with the actual covariance rank, together with genuine time integrability. Independent reviews cover the actual signed matrices, Gaussian copy laws, scalar kernels, continuous majorant, bandwidth optimization and Gaussian-width substitution. Equivalent intermediate routes and constants are recorded explicitly. The older unrescaled integral theorem is an auxiliary valid bound.

There are now 266 accepted passage correspondences, including 32 units with documented method variations; the eight qualified E.1 passages remain separate. The six unaccepted named statements are Lemma H.1, Propositions H.3–H.4, Lemma H.5, and Corollaries 4–5. The actual facet component of H.1 has a separate reviewed volume-almost-every-threshold result; the complete all-threshold H.1 statement remains open. Unbound internal passages also remain open. Conjecture 1 is excluded.

The archived 31 statements and 253 accepted passages concern the earlier November 7 manuscript. Its files and historical receipts remain unchanged. Fresh archive replay is recorded separately. Positive-integer derivative orders are preserved. `REPRODUCIBILITY.md` explains collaborator access to the private chaining dependency and the scope of each checkpoint.
