# Sharp High-Dimensional Gaussian Approximations over Rectangles without Covariance Restrictions

Victor Chernozhukov, Denis Chetverikov, Kengo Kato, and Yuta Koike.

This repository contains the paper, its Supplemental Material, and the archived Lean verification with the source dependencies needed to reproduce it. The current manuscript and supplement are dated **16 November 2026**.

| Material | PDF | Sources |
| --- | --- | --- |
| Main paper, 107 pages | [Read the paper](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.pdf) | [LaTeX](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex) · [arXiv source ZIP](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16_source.zip) |
| Supplemental Material, 28 pages | [Read Appendices G–I](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.pdf) | [LaTeX](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex) · [Source ZIP](research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16_source.zip) · [Build guide](research-rectangle-clt-singular/Rectangle_CLT_Supplement_README.md) |

The supplement contains the dimension-logarithm cap, the correlation-gap proof, and the exceptional-correlation-budget proof. It preserves Appendix labels G, H, and I. Corollaries 4 and 5 remain stated in the main paper. Save the two PDFs in the same folder to follow cross-document links in readers that support them.

The [Lean verification guide](LEAN_VERIFICATION.md) distinguishes the archived **7 November 2026** certificate from the current paper. That certificate covers the frozen manuscript's 31 proved statements and qualified formal counterparts of its substantive proof arguments. It does not cover the subsequent intrinsic refinements or the new supplement. Conjecture 1 is excluded. Publishing this archive does not constitute a new Lean certification.

The [provenance guide](PROVENANCE.md) records the selected history, original dates, commit mapping, and checksums. Historical manuscripts and original verification records are retained without editing their contents. The wider HDCLTs research repository remains private. The first public release of this selected archive is 16 November 2026; retained earlier commit dates describe development history, not earlier public availability.

The [submission checks](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16_checks.md) describe the PDF/source validation. The arXiv identifier will be added after submission and announcement.
