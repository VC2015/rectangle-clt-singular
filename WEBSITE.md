# Paper website

The GitHub Pages site is built directly from `docs/` on `main`, without a build step or external dependencies. Its intended address is https://vc2015.github.io/rectangle-clt-singular/.

To enable publication, open this repository's **Settings → Pages**, choose **Deploy from a branch**, select **main** and **/docs**, and save. Subsequent commits to `docs/` update the site automatically.

The two PDFs in `docs/` are exact copies of the public manuscript and supplement in `research-rectangle-clt-singular/`. Keep their original filenames so that links between the documents continue to work. When replacing them, update the page counts, dates, and links in `docs/index.html`, the metadata in its head, `docs/citation.bib`, and `docs/sitemap.xml` as needed.

The website, README and BibTeX record link to [arXiv:2611.21474v1](https://arxiv.org/abs/2611.21474v1).

Keep the Lean scope statement aligned with [the v1 verification guide](LEAN_VERIFICATION_V1.md). The [V4 guide](LEAN_VERIFICATION.md) belongs to the frozen 7 November archive.

The page provides descriptive and scholarly citation metadata and a sitemap. Search indexing is controlled by search engines; publication alone does not establish that the site has been indexed.
