# Frozen-source correspondence queue

This directory records the correspondence review for arXiv:2611.21474v1 and Supplemental Material G–I. Lemma C.2 and C2.1–C2.7 are checked, with a clean-checkout build, transitive axiom audit, expanded types, kernel dependencies, and independent frozen-source/PDF review. The remaining 39 named results are open; Conjecture 1 is excluded. This does **not** certify the whole new paper. An archived accepted passage is recorded as a historical candidate until its new correspondence is checked.

The paper snapshot is `1803366cc994d9facae8e128ee180f68e319486f`. The full frozen main source has SHA-256 `e96aaf12ca782c94d70587f128b58a20d3ace8b31a8c324a3272b2b1d71677a2`; the supplement has SHA-256 `5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb`. Span hashes use the exact UTF-8 bytes of inclusive source lines, including their original line endings. Statement-environment comparisons instead compare exact `\begin{...}` through `\end{...}` bytes, without surrounding line endings.

## Files and status

| File | Content |
|---|---|
| [statements.json](statements.json) | All 40 named results and the excluded conjecture, frozen statement spans and hashes, individual reuse obligations, declarations, expanded types and receipts. Only C.2 is currently accepted. |
| [c1-gaussian-passages.json](c1-gaussian-passages.json) | Appendix C.1 Gaussian proof spans C1.G.1–C1.G.8, archived analytic candidates, and drafted new wrappers; pending elaboration and representation review. |
| [c2-passages.json](c2-passages.json) | Seven accepted passages C2.1–C2.7, exact frozen spans, inference reviews, declarations, types, dependencies and receipts. |
| [c2-acceptance.json](c2-acceptance.json) | Binds C.2 acceptance to the successful clean-checkout run and independent reading-order review. |
| [proof-environments.json](proof-environments.json) | All 34 explicit proof environments. Only explicit caption references or the specified C.2 proof are linked to statements; the remaining subdivisions stay open. |
| [archive-candidates.json](archive-candidates.json) | The archive's 253 accepted same-argument records and its one order-zero repair record, with historical source-span hashes. None is automatically transplanted. |
| [build_source_ledger.py](build_source_ledger.py) | Reads frozen Git objects and validates source identity. It never invokes Lean or certifies an inference. |

An independent byte comparison reproduces 29 historical proved-label matches. Only Lemma B.3 has an identical statement environment. Of the other matches, 22 are wrapper or strengthening candidates and six require new width calibrations using historical components. The 11 remaining named results have no archived named-label counterpart. These are review classifications, not declarations that the corresponding wrappers already exist.

The archive concerns a different frozen manuscript, with SHA-256 `f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1`. Its saved expanded types and receipts are historical evidence. Fresh archive validators and fresh Lean execution must be recorded separately, as described in [LEAN_VERIFICATION.md](../../LEAN_VERIFICATION.md).

From the repository root, after enabling the archived original-commit aliases where required, run:

```sh
python3 lean-rectangle-clt-arxiv-v1/correspondence/build_source_ledger.py --check
```

The saved [initial source-identity receipt](source-identity-receipt.json) records this check. The success marker is `PASS_SOURCE_IDENTITY_ONLY`. It verifies both full source pins, new statement/proof/setup spans, archive-span hashes and the conjecture exclusion. It does not establish any mathematical correspondence. `--write-initial` creates the initial JSON files only when they do not already exist; it refuses to overwrite subsequent review work.

## C.2 assumptions and reading order

The setup in frozen main lines 145–157 supplies independent centered finite random vectors `ξ_i` in `R^p`, their bounded-coordinate envelope, `W = ∑ ξ_i`, `Σ = Cov(W)` with unit diagonal, and a centered Gaussian `Z` with covariance `Σ`. Formalization must state measurability and the resulting integrability explicitly. The theorem is uniform in positive dimension `p`, including `p = 1`. `L = log(e p)` is defined at lines 169–176, and `g_Σ = E‖Z‖∞` at lines 220–228.

No independence between coordinates of a summand, identical-distribution hypothesis, nonsingularity, small-envelope regime, relative moment matrix budget, or independence between `W` and `Z` is an extra premise of C.2. A separate Gaussian probability space is legitimate only after the matching distribution or representation is proved. A nonnegative envelope parameter must be stated or derived from the actual bounded-sum setup; degeneracies of individual contrasts still require explicit treatment.

| ID | Frozen main lines | Inference to review |
|---|---|---|
| C2.1 | 6384–6402 | Zero/signed-coordinate indices, both maxima and the discrete/canonical distances. Keep all original indices in the discrete metric. |
| C2.2 | 6404–6417 | Actual centered independent contrasts, envelope `2δ`, covariance identity and the two-sided Bernstein tail with explicit constants. Handle equal indices and zero contrast variance. |
| C2.3 | 6419–6435 | Indexed/subset net definitions, singleton first level, dyadic weights, finite real costs and metric homogeneity. |
| C2.4 | 6437–6448 | Dirksen at the zero base point and `2 sup_t E|X_t| ≤ 2` from variance one. |
| C2.5 | 6450–6461 | Literal singleton-then-full net witness, discrete cutoff estimate and `log(2p+1) ≤ C log(e p)`, including `p=1`. |
| C2.6 | 6463–6476 | Concrete Gaussian covariance factor/representation, canonical Euclidean geometry, one-sided signed maximum, audited majorizing measures and any zero-distance quotient. |
| C2.7 | 6478–6484 | Combine and absorb `2` using the standard-normal marginal lower bound `g_Σ ≥ sqrt(2/π)`, with the universal constant quantified first. |

Both principal bridges are now proved: C2.2 derives the mixed-tail premise from the actual summands, and C2.6 matches the Gaussian law, covariance factor, signed vectors and one-sided width. Duplicate signed vectors are identified only for the canonical metric and Gaussian maximum. The final raw-data theorem assumes no comparison inequality, MGF estimate or mixed-tail hypothesis.

## Derivative-order qualification and later proofs

The old archive's derivative-envelope qualification is **integer `q ≥ 1`**. Its literal order-zero reading was formally refuted; those counterexamples and receipts are unchanged. The new frozen main source already says “fixed positive integer” at lines 3138 and 3170. New mappings must preserve that restriction and all associated ranges for smoothing width and translation radius. No `q=0` claim is included here.

Beyond C.2, keep the intrinsic coefficient `κ` through the smoothing, initialization and interpolation arguments, together with both fourth-moment matrices. A historical worst-case logarithmic estimate is insufficient for a newly stated Gaussian-width bound. Lower-bound constructions require their new covariance, rank, width-profile and moment calibrations with the printed quantifier order. Supplemental G–I and prose outside explicit proof environments remain open work; the 34 proof-environment rows do not claim to exhaust the substantive passages.

A passage may be accepted only after its actual new declaration, expanded type, audited dependency closure and successful build/audit receipt have been recorded and independently reviewed against the frozen lines in reading order. A theorem proved by an alternative route must be distinguished from the printed passage it bypasses. Source identity alone is never evidence that a proof step has been implemented.


## Appendix C.1 Gaussian reuse review

The archive already proves the intrinsic Gaussian bound, rather than merely its logarithmic consequence. In particular, `SplitV4.GaussianIntrinsicConcentration` has the general common-variance, independent-shift result with coefficient `2s/v` times the actual expected face-projection norm. Its premises are a concrete Gaussian law, actual face variances and measurable independence; they do not assume the desired anti-concentration bound, an invertible factor, a correlation gap, distinct rows or shift moments.

The new `RectangleCLTArxivV1/IntrinsicGaussianBoundary.lean` deliberately uses the archive's `Printed.GaussianMollification` theorem for its unit-row boundary input, then carries that input through variance scaling and shift conditioning. This keeps the literal linear-ramp convolution route in the new dependency closure. The archive's alternative generic smooth-test-to-interval endpoint is not substituted for the printed mollification passage in this new chain.

The side ledger records eight frozen proof spans. Two representation differences remain explicit: the archived normalization uses a possibly singular square factor in the ambient dimension instead of the paper's rank-dimensional factor, and repeated directions are handled directly in the gradient limit instead of first removing duplicates. Neither imposes an extra probabilistic premise, but detailed correspondence still requires review before accepting the full statement. Compiled supporting wrappers alone do not mark those passages accepted.
