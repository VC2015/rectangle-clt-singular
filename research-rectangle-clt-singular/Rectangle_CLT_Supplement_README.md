# Supplemental Material for Sharp High-Dimensional Gaussian Approximations over Rectangles without Covariance Restrictions

Victor Chernozhukov, Denis Chetverikov, Kengo Kato, and Yuta Koike. 16 November 2026.

[Supplement PDF](Rectangle_CLT_Supplement_2026-11-16.pdf) · [LaTeX source](Rectangle_CLT_Supplement_2026-11-16.tex) · [Source ZIP](Rectangle_CLT_Supplement_2026-11-16_source.zip) · [Main paper](Rectangle_CLT_arXiv_2026-11-16.pdf) · [Build and preservation checks](Rectangle_CLT_arXiv_2026-11-16_checks.md)

The supplement contains Appendix G (the dimension-logarithm cap), Appendix H (the proof of the positive-correlation-gap result in Corollary 4), and Appendix I (the proof of the exceptional-correlation-budget result in Corollary 5). Their statements, proofs, and G–I numbering are unchanged from the full manuscript at original commit `ed2a730b9aed5176065b7b34e5e7fa573ea9afa3`, whose public counterpart is listed in the [commit map](../provenance/commit-map.txt). Earlier manuscript and verification timestamps remain in the repository history. This extracted supplement is dated 16 November; it does not create a new certification claim.

The PDF uses S-prefixed pages and the same typography as the main paper. Unprefixed theorem/equation references and references to Sections 1–5 or Appendices A–F refer to the main paper. References prefixed G, H, or I refer to this supplement. To follow links between downloaded PDFs, save both PDFs in the same directory under their existing filenames; support for opening another PDF depends on the reader.

The source ZIP contains the supplement TeX and `Rectangle_CLT_main_reference_labels.aux`. The latter is a snapshot of the 30 labels used from the main paper and is required for compilation. No other HDCLTs research files are needed. Extract the ZIP, then run the following command three times with a standard TeX Live installation:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error Rectangle_CLT_Supplement_2026-11-16.tex
```

The main-paper ZIP contains only its standalone TeX source. To rebuild it, extract that ZIP and run the same command three times with `Rectangle_CLT_arXiv_2026-11-16.tex` as the input. Both documents include their bibliographies; no BibTeX step is needed.

If the main paper is edited, rebuild it first. Regenerate `Rectangle_CLT_main_reference_labels.aux` from the new main `.aux`, retaining the same label keys and complete corresponding `newlabel` lines, then rebuild the supplement and update its ZIP. This refreshes page numbers and hyperlink destinations, even when the mathematical numbering is unchanged.

The supplement is cited as “Supplemental Material for Sharp High-Dimensional Gaussian Approximations over Rectangles without Covariance Restrictions.” The paper and supplement link to the [public repository](https://github.com/VC2015/rectangle-clt-singular). The [Lean verification guide](../LEAN_VERIFICATION.md) identifies the frozen archive and explains reproduction. The broader HDCLTs research repository remains private.

The archived 7 November Lean verification does not cover the intrinsic refinements or these three appendices. See Section 1.5 of the main paper for the exact scope.
