# Verify the 16 November rectangle CLT and its printed proofs

Work in this directory for the new certification. The target is arXiv:2611.21474v1 and its separate Supplemental Material, Appendices G–I. Freeze the two TeX files at paper commit **1803366cc994d9facae8e128ee180f68e319486f**. Their relative paths and SHA-256 hashes are in [inventory.json](inventory.json). Use that ledger as the initial work queue. It contains 40 named results, one excluded conjecture and 34 explicit proof environments. Some proofs occur in ordinary prose or span several sections.

**Assignment to Codex.** Establish the source pins and the new Lake project, then complete Lemma C.2 from the paper's bounded-sum assumptions, following the seven passages below. Continue through the main paper and supplement in dependency order. Deliver a formal result and a checked correspondence with the published argument for each proof. Keep compiling and committing independently checkable increments. The archive supplies reusable mathematical components and a model for the final evidence. Keep its files and historical receipts intact.

## Reuse the two existing developments

1. Read the [archived verification guide](../LEAN_VERIFICATION.md). Reproduce its validators in an isolated worktree and distinguish replay of saved receipts from fresh Lean execution. Reuse the pinned toolchain (Lean 4.19.0, mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`) and resolve the archive's local Lake dependencies as described there. Create a sibling Lake project and a new Lean namespace here. Import an archived declaration when its expanded type and dependencies implement a step of the new proof. Put adaptations, correspondence files, and evidence for this release here.
2. Compare against the archive's 31 statements and 253 accepted proof passages. Among the new results 29 have historical label matches, but only B.3 has identical statement-environment bytes among those 29. A matching label or identical text is a starting point for reviewing hypotheses, definitions and proof dependencies. Record which pieces survive verbatim, which require a wrapper or strengthened lemma, and which are new. The old positive-integer derivative qualification remains relevant when checking order ranges.
3. Pin the standalone [generic chaining proofs](https://github.com/VC2015/generic-chaining/tree/b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc) by the full SHA **b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc**. Its clean build and 54-declaration transitive audit were independently rerun for this handoff. Use `import GenericChaining`. [ChainingImports.lean](ChainingImports.lean) is a smoke check run against this revision. Register and lock the dependency in this project and rerun the smoke check here. Access to that private GitHub repository is needed to fetch the pin. Record this in reproducibility instructions and distinguish collaborator reproduction from a publicly reproducible release.

## First complete proof: Lemma C.2

All line numbers below refer to the [frozen main TeX](https://github.com/VC2015/rectangle-clt-singular/blob/1803366cc994d9facae8e128ee180f68e319486f/research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex#L6376-L6484). The target is $\mathbb E\|W\|_\infty\le C(g_\Sigma+\delta L)$, with the paper's universal quantifiers, arbitrary positive dimension, unit marginal variances and possibly singular covariance.

| Passage | What the Lean proof must supply |
|---|---|
| C2.1 · 6384–6402 | Construct the zero and signed-coordinate indices. Identify both maxima and the discrete and canonical pseudometrics. |
| C2.2 · 6404–6417 | For each contrast prove centering, independence, the envelope $2\delta$, and the variance identity. Apply the archive's scalar Bernstein MGF proof to both signs and optimize, treating equal indices and zero variance. Derive the actual mixed-tail hypothesis with the constants in the two scales. |
| C2.3 · 6419–6435 | Match the printed admissible subsets with the library definition via `gamma_eq_finset`. Verify the factor multiplying each metric and the corresponding homogeneity. |
| C2.4 · 6437–6448 | Apply `GenericChaining.dirksen_expectation` with base point zero. Use the variance normalization to prove the extra term is at most two. |
| C2.5 · 6450–6461 | Witness the printed singleton-then-full nets, invoke the discrete cutoff bound and prove the logarithmic estimate for $2p+1$. |
| C2.6 · 6463–6476 | Realize the centered Gaussian via a covariance factor on its support. Match the library's Euclidean canonical distance and one-sided width to the signed process. Invoke `GenericChaining.gamma2_le_gaussianWidth`. Identify duplicates only for this metric and maximum. Cover exact positive and negative correlation. |
| C2.7 · 6478–6484 | Combine the estimates and use $g_\Sigma\ge\sqrt{2/\pi}$ to absorb the constant, explicitly including $p=1$. |

## Continue through the paper

| Printed argument | Principal obligation in this version |
|---|---|
| Appendix C.1, Lemmas 1–2, Appendices A–B, §2 | Rebuild the intrinsic boundary and smoothing estimates, initialization and seeded interpolation with both fourth-moment matrices. Track the printed coefficient $\kappa$ until the final split. If $\delta L\le g_\Sigma$, C.2 gives $\kappa\lesssim g_\Sigma$. In the complementary regime use the trivial probability bound at the printed normalization. |
| §§1, 3 and Appendices D–E | Trace normalization, capping, projected zero variances, truncation and the paired interpolation/Bennett proof. Match each part of Theorem 2 to its own proof. |
| §4 and Appendix F | Formalize the actual lower-bound distributions, scalar tail estimates, maximum shifts, sparse masks, moments and width calibrations. Check all existential choices and the order of quantifiers in Theorems 3–8. |
| §5 and supplement G–I | In G check the face estimates, cancellation and minimum of remainders. In H check the localized surface and matrix estimates, conditioning and integration in time. In I combine the exceptional-pair sum with the ordinary-pair bounds. Check parallel faces, empty exceptional sets and uniformity in the correlation cutoff. |

For every substantive passage assign a stable ID and a frozen source span, explain its inference, and record the Lean declaration, dependencies, expanded type and build receipt. Link those IDs to the appropriate statement rows. Include displays and prose arguments outside theorem or proof environments. Record statements proved by an alternative route separately from printed passages actually matched. If an inference fails, identify the smallest unsatisfied premise and the downstream statements; preserve the published formulation for review.

Review all hypotheses for hidden conclusions. In particular an assumed comparison inequality, interpolation remainder, or distributional construction belongs in the dependency ledger until it is proved or imported from an audited source. Keep Conjecture 1 excluded. Rebuild the complete package in a clean checkout, force elaboration of all mapped declarations, run the transitive axiom audit against `propext`, `Classical.choice`, and `Quot.sound`, and record commands, toolchain, dependency SHAs and logs. A second reader should trace the mapped steps in reading order through both PDFs. Report per-statement and per-passage status, and identify any remaining gap before making a release-wide certification claim.
