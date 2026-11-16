# Submission checks, 16 November 2026

This checkpoint separates Appendices G, H, and I from the full manuscript at commit `ed2a730b9aed5176065b7b34e5e7fa573ea9afa3`. The main paper contains Sections 1–5 and Appendices A–F (107 pages). The supplement has 28 pages and retains the G–I numbering. Corollaries 4 and 5 remain stated in the main paper; their proofs are cited in the supplement. All three appendix bodies are preserved verbatim.

Section 1.4 is titled “Relationship to the Literature.” The Lopes–Masini discussion is last in that review, and the independent/contemporaneous acknowledgment retains the submission, announcement, and awareness dates. The discussion explicitly identifies the suboptimal dependence on log(ep), separating their sub-Gaussian Theorem 2.1 from their sharper bounded-observation Theorem 3.1. With L=log(ep), log p asymptotic to n^a, fixed 0<a<1, and fixed tail or envelope constants, the comparisons before truncation at 1 are:

| Common assumptions | This paper | Lopes–Masini | Ratio of their bound to ours |
| --- | --- | --- | --- |
| Sub-Gaussian coordinates | n^(-1/2) L^(3/2) (log n)^(3/2), Corollary 2 | n^(-1/2) L^3 log n, Theorem 2.1 | L^(3/2) / sqrt(log n) |
| Bounded coordinates | n^(-1/2) L^(3/2) sqrt(log n), Corollary 1 | n^(-1/2) L^(5/2) log n, Theorem 3.1 | L sqrt(log n) |

The first comparison uses our existing sub-exponential theorem under the stronger sub-Gaussian assumption. No new sub-Gaussian theorem is asserted. The bounded orthant result is transferred to rectangles by signed coordinate duplication. Table 2 gives convergence ranges a<1/3 for both of our bounds, versus a<1/6 and a<1/5 for theirs. These are guarantees of the displayed bounds, not necessary conditions for approximation. Theorem statements and locators were checked against [arXiv version 1](https://arxiv.org/html/2611.17923v1).

The bibliography is alphabetical by author list, then year and title. All 36 pre-existing entries are unchanged; the supplement is the 37th entry. Citation keys are retained and numbers are regenerated. The footnote now says “genuine collaboration.” Villani-inspired typography is retained. Zero inter-item spacing in the bibliography prevents a lone final reference from occupying a separate page, without changing the font or margins.

Both source ZIPs were extracted and compiled with pdfLaTeX in three passes, with shell execution disabled. There are no unresolved references or citations, missing glyphs, or overfull/underfull boxes. The only warning concerns disabled shell execution in epstopdf; no EPS conversion is needed. Recorded inputs contain only the respective source, generated auxiliary files, the supplement's 30-label snapshot, and the installed TeX runtime. arXiv's server has not yet compiled these files.

The main PDF has 701 valid internal links and 34 embedded fonts. The supplement has 122 valid internal links, 45 valid links to named destinations in the main PDF, and 23 embedded fonts. No extracted text falls outside a page. All pages were visually inspected in contact sheets, with detailed inspection of the revised literature discussion, tables, title, supplement contents, bibliography, and appendix transitions.

Across the two files, all 8 theorem, 23 lemma, 4 proposition, 5 corollary, 1 conjecture, and 34 proof environments are unchanged. All numbered equation/align environments and the figure are unchanged. All pre-existing result, equation, and section numbers are preserved. The proof-method and dimension-growth tables exchange numbers because their order changes. All 312 original labels remain unique across the two sources. The source packages match their compiled sources byte for byte.

This is a compilation, presentation, source-preservation, and targeted rate-comparison check, not a new full proof audit or Lean certification. Certification remains limited to the archived 7 November version described in Section 1.5.

**Public release:** the supplement, main-paper and Lean-verification links now point to the separate public rectangle-clt-singular repository. Both PDFs and source ZIPs were rebuilt and rechecked after these changes. The broader HDCLTs repository remains private. Select pdfLaTeX and `Rectangle_CLT_arXiv_2026-11-16.tex` as the top-level file, and review arXiv's server-generated PDF before final submission. The supplement source package is separate from the main-paper upload package.

| File | SHA-256 |
| --- | --- |
| Main source | `e96aaf12ca782c94d70587f128b58a20d3ace8b31a8c324a3272b2b1d71677a2` |
| Main source ZIP | `255f770ed166d424307fed2601e72b9e39f43ed5748b6992ba206d17c141379a` |
| Supplement source | `5abda8831ac33ed91c2c8e3f628d8ef6ecb7437e7573a52efa7b112efb93a0bb` |
| Supplement source ZIP | `e85bc3bd1c1312be742e908ef5bd666f3ab278493993d84f15545a67b73873ca` |
