# Sharp High-Dimensional Gaussian Approximations over Rectangles without Covariance Restrictions

Victor Chernozhukov, Denis Chetverikov, Kengo Kato, and Yuta Koike.

This repository contains the paper, its Supplemental Material, and the archived Lean verification with the source dependencies needed to reproduce it. The current manuscript and supplement are dated **16 November 2026**.

## Abstract

We study how well a sum of $n$ independent random vectors with $p$ coordinates can be approximated by a Gaussian vector with the same mean and covariance. We measure the error over rectangles, so the bounds apply to maxima and simultaneous confidence regions. The coordinates may be arbitrarily dependent, even exactly linearly dependent, and the bounds do not deteriorate as the covariance matrix becomes singular. After standardizing the coordinate variances, bounded or sub-exponential coordinates give the $n^{-1/2}$ sample-size rate up to logarithmic factors, with the size or tail bounds held fixed. The main upper bounds retain the Gaussian expected maximum, improving the rates when the coordinates are strongly dependent. Fourth-moment refinements give further improvements when large observations contribute little to individual coordinate variances. If we instead impose a fixed moment bound of order $q>4$ on the largest absolute coordinate, together with a coordinate fourth-moment bound, the rate becomes $n^{-1/2+1/q}$ up to logarithmic factors. At $q=4$, the slower $n^{-1/4}$ rate is unavoidable, confirming our earlier conjecture. We also allow the bounds on observation size to grow with $n$. Lower-bound examples show that the dependence on sample size, observation size, and Gaussian width is sharp up to logarithmic factors in the regimes studied, and in several regimes the upper and lower bounds match including the logarithmic terms.

## Paper and supplemental material

| Material | PDF | Sources |
| --- | --- | --- |
| Main paper, 107 pages | [Read the paper](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.pdf) | [LaTeX](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex) · [arXiv source ZIP](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16_source.zip) |
| Supplemental Material, 28 pages | [Read Appendices G–I](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.pdf) | [LaTeX](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex) · [Source ZIP](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16_source.zip) · [Build guide](research-rectangle-clt-singular/Rectangle_CLT_Supplement_README.md) |

The supplement contains the dimension-logarithm cap, the correlation-gap proof, and the exceptional-correlation-budget proof. It preserves Appendix labels G, H, and I. Corollaries 4 and 5 remain stated in the main paper. Save the two PDFs in the same folder to follow cross-document links in readers that support them.

The [Lean verification guide](LEAN_VERIFICATION.md) distinguishes the archived **7 November 2026** certificate from the current paper. That certificate covers the frozen manuscript's 31 proved statements and qualified formal counterparts of its substantive proof arguments. It does not cover the subsequent intrinsic refinements or the new supplement. Conjecture 1 is excluded. Publishing this archive does not constitute a new Lean certification.

The [verification assignment for the 16 November paper and supplement](lean-rectangle-clt-arxiv-v1/README.md) starts a separate certification, with a [statement and proof inventory](lean-rectangle-clt-arxiv-v1/inventory.json). It uses the completed finite chaining dependency. The new paper's proof obligations are open.

The [provenance guide](PROVENANCE.md) records the selected history, original dates, commit mapping, and checksums. Historical manuscripts and original verification records are retained without editing their contents. The wider HDCLTs research repository remains private. The first public release of this selected archive is 16 November 2026; retained earlier commit dates describe development history, not earlier public availability.

The [submission checks](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16_checks.md) describe the PDF/source validation. The arXiv identifier will be added after submission and announcement.
