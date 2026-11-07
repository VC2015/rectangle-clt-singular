# Split-V4 proof status and open obligations

The frozen proof checkpoint is `88157fe`. Eighteen of the 31 proved named
statements are checked; 13 remain pending. The whole manuscript is not
certified. Conjecture 1 is excluded and is never used as an assumption.
The exact declarations, expanded types, source excerpts, source hashes,
commands, and logs are in [statement-map.json](statement-map.json),
[dependency-map.json](dependency-map.json), and the
[verification record](../SPLIT_V4_VERIFICATION.json).

The target is handoff commit
`2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`, manuscript SHA-256
`f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`.
The manuscript and frozen October verification records are unchanged.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted
transitively. Statement completion and the manuscript's current proof route
are recorded separately.

## Checked statements

- Corollaries 1 and 2: actual full rectangle distance, universal constants
  fixed before the models, average marginal normalization, and genuine
  Orlicz hypotheses.
- Lemma 2: actual smoothing endpoint. Theorem 3: the growing-envelope
  skewed lower construction and its stated lower constant.
- Lemma B.3: actual Gaussian mean, positive masses, entropy and face
  contraction.
- Lemma 1 and Lemma C.1: both full intrinsic anti-concentration classes
  and the uniform cube inequality, including its logarithmic consequence.
  The Gaussian coefficient is `2`. The cube proof handles ties directly
  through selected supporting branches.
- Lemma E.1, Propositions 2 and 3, and Theorem 2: actual maximum bound,
  conditional-truncation and Bennett polynomial routes, their optimized
  minimum, and the literal supremum over the full array class. Genuine
  envelope and separate coordinate-fourth moments are retained even for
  `2 < q < 4`. Constants depend only on fixed `q`.
- Lemmas F.1–F.3: the general iid-free strict moderate-tail expansion,
  actual signed-shift CDF comparison, and the actual masked symmetric
  finite-product family with all stated moment, rank and gap properties.
- Lemmas G.1–G.4: the full five-term comparison with actual tail data,
  Gaussian-endpoint smoothing, exact paired interpolation, and the
  Bennett maximum bound. G.2 uses a proved good-clock cutoff in place
  of the printed expected-clock-width step. G.3 supplies canonical
  derivative tensors for ordinary bounded-derivative C4 inputs and proves
  that actual copy averages are the required conditional expectations.

## Relative theorem and Appendix B: seven pending statements

Theorem 1 (`thm:unrestricted`), Proposition 1 (`an:prop:derivative`),
Lemma A.1 (`appx-lem:envelope`), and Lemmas B.1, B.2, B.4 and B.5
(`appx-an:lem:identity`, `appx-an:lem:restoration`,
`appx-an:lem:matrix`, `appx-an:lem:threshold`) remain pending.

The historical `unrestrictedCLT` proves the envelope specialization; it
has no relative `s4` parameter. `RelativeMoments.lean` defines the signed
cubic tensor and both distinct fourth matrices with genuine integrability.
`RelativeFourthRefinement.lean` now derives the signed third budget from
fourth-only admissibility, preserving singular covariance and both fourth
matrices. `RelativeMomentTransfer.lean` proves the actual face-map
covariance and both relative fourth transfers.

`SeededInterpolation.lean` constructs the actual independently seeded
finite-mask path and proves its calibrated FaceSmoother fourth-order
identity. `VariableAmplitudeInterpolation.lean` proves differentiation of
the actual finite-mask expectation for arbitrary positive C1 amplitude,
with `varpi=(1-t)/gamma^2` in `[0,1]`, including the genuine Gaussian heat
contraction. These are checked components, not the full general B.1
statement for every smooth bounded-derivative test function.

The remaining assembly must:

1. Prove the complete arbitrary-amplitude fourth-order identity for the
   full B.1 test-function class. Preserve the signed aggregate cubic term
   and every actual same-copy and independent-copy kernel.
2. Establish B.2 from actual conditional moment budgets and conditional
   Gaussian independence, allowing all auxiliary arrays to depend on the
   conditioning field and on one another. Retain the signed first-order
   refinement at zero shifts and both squared-face fourth budgets.
3. Prove B.5 for the actual hard Gaussian CDF derivative, first with
   independent unit normals, then through repeated/dependent normals and
   singular regularization. The required averaged bound is
   `C*(sigma*L^(3/2)+delta*L^2)`, with cancellation of the near-parallel
   angular factor in the localized facet/ridge argument.
4. Derive B.4's actual nuclear-norm sum over every ordered face tuple from
   B.3, B.5 and the logistic selector mixture. Keep the generic
   concentration constant until the intended application fixes it.
5. Match Lemma A.1's arbitrary face norm and translated derivative
   supremum. Assemble Proposition 1, initial Slepian and seeded paths,
   time integrals, `epsilon=L*h^2`, and the endpoint cost. Obtain
   `C*min(1,L^(3/2)*(delta+sqrt(s4*D_L)))` without substituting `delta^2`
   for `s4` before the relative refinement is proved.

## Polyhedral transfer: one pending statement

Corollary 3 (`cor:polyhedral-transfer`) remains pending only through the
relative-moment endpoint of Theorem 1. The actual Gaussian pushforward and
bounded, Orlicz and polynomial final bounds are checked in
`GaussianFaceTransfer.lean`, `OrliczFaceTransfer.lean`, and
`PolynomialFaceTransfer.lean`. The latter derives `J >= 1` and the exact
`B -> J^2*B` class transfer. `ZeroVarianceFaces.lean` proves exact deletion
under both laws, including negative thresholds and empty face families.
No positive covariance rank, eigenvalue, or correlation gap is added.

## Lower-bound calibrations: five pending statements

Theorems 4–8 (`opt:symmetric-lower`, `opt:q4-lower`, `opt:q4-growing`,
`lower:dense`, `lower:sparse`) remain pending. The checked F.1–F.3 inputs
provide general moderate tails, the signed shift comparison and the common
symmetric model. They do not by themselves supply these calibrations.

Prove the actual maximum decompositions, Gaussian maximum moments and
threshold density calibration, local Rademacher maximum comparison,
activation/count estimates, eventual validity of all mask probabilities,
and both negligible remainders under the exact growth hypotheses. The
unmasked and masked calibrations have opposite discrepancy signs. Keep
fixed `B` separate from growing `B_n`, and retain constants `1/(8e)`,
`1/(2*sqrt(2)*e)` and `1/(4e)` in Theorems 4, 5 and 6. Theorems 7 and 8
must retain all `q`/`B` dependence, the separate coordinate-fourth condition,
and full/symmetric-class supremum conclusions. Coordinate duplication
must preserve the full rectangle distance while producing gap zero.

## Reproducibility

The runner checks the pinned Lean 4.19.0/mathlib revisions, hashes every
Lean source and frozen record before and after execution, builds the
terminal package and every SplitV4 module/audit, and executes every audit
fresh. The complete imported companion closure receives a separate strict
axiom audit. An isolated detached checkout keeps ongoing proofs outside
the frozen receipt. Historical checkpoints and raw failed diagnostics are
retained separately; no failed command is presented as successful evidence.
