# Sharp High-Dimensional Gaussian Approximations over Rectangles without Covariance Restrictions

Victor Chernozhukov, Denis Chetverikov, Kengo Kato, and Yuta Koike.

The [paper on arXiv](https://arxiv.org/abs/2611.21474v1) and its Supplemental Material are dated **16 November 2026**. The [paper homepage](https://vc2015.github.io/rectangle-clt-singular/) links to both PDFs. The [Lean verification guide for arXiv v1](LEAN_VERIFICATION_V1.md) links the mathematical results and their proofs to the code.

## Abstract

We study how well a sum of $n$ independent random vectors with $p$ coordinates can be approximated by a Gaussian vector with the same mean and covariance. We measure the error over rectangles, so the bounds apply to maxima and simultaneous confidence regions. The coordinates may be arbitrarily dependent, even exactly linearly dependent, and the bounds do not deteriorate as the covariance matrix becomes singular. After standardizing the coordinate variances, bounded or sub-exponential coordinates give the $n^{-1/2}$ sample-size rate up to logarithmic factors, with the size or tail bounds held fixed. The main upper bounds retain the Gaussian expected maximum, improving the rates when the coordinates are strongly dependent. Fourth-moment refinements give further improvements when large observations contribute little to individual coordinate variances. If we instead impose a fixed moment bound of order $q>4$ on the largest absolute coordinate, together with a coordinate fourth-moment bound, the rate becomes $n^{-1/2+1/q}$ up to logarithmic factors. At $q=4$, the slower $n^{-1/4}$ rate is unavoidable, confirming our earlier conjecture. We also allow the bounds on observation size to grow with $n$. Lower-bound examples show that the dependence on sample size, observation size, and Gaussian width is sharp up to logarithmic factors in the regimes studied, and in several regimes the upper and lower bounds match including the logarithmic terms.

## Paper and supplemental material

| Material | PDF | Sources |
| --- | --- | --- |
| Main paper, 107 pages | [Read the paper](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.pdf) | [LaTeX](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex) · [arXiv source ZIP](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16_source.zip) |
| Supplemental Material, 28 pages | [Read Appendices G–I](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.pdf) | [LaTeX](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex) · [Source ZIP](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16_source.zip) · [Build guide](research-rectangle-clt-singular/Rectangle_CLT_Supplement_README.md) |

The supplement contains the dimension-logarithm cap, the correlation-gap proof, and the exceptional-correlation-budget proof. It preserves Appendix labels G, H, and I. Corollaries 4 and 5 remain stated in the main paper. Save the two PDFs in the same folder to follow cross-document links in readers that support them.

Lean checks 39 of the 40 named results as stated. For Lemma E.1 it makes the envelope condition $A\ge 0$ explicit, as used in the proof. The correspondence records cover all 34 explicit proof environments, including the supplement, and identify where Lean takes a different route. Conjecture 1 remains open. [Theorem-to-Lean index](lean-rectangle-clt-arxiv-v1/STATUS.md) · [Proof correspondence](lean-rectangle-clt-arxiv-v1/correspondence/final-coverage.json) · [Reproducing the checks](lean-rectangle-clt-arxiv-v1/REPRODUCIBILITY.md)

The [7 November V4 certificate](LEAN_VERIFICATION.md) covers the 31 proved statements of that earlier manuscript.

The [provenance guide](PROVENANCE.md) records the selected history, original dates, commit mapping, and checksums. Historical manuscripts and original verification records are retained without editing their contents. The wider HDCLTs research repository remains private. The first public release of this selected archive is 16 November 2026; retained earlier commit dates describe development history, not earlier public availability.

The [submission checks](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16_checks.md) describe the PDF/source validation.
