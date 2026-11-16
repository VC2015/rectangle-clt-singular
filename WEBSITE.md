# Paper website

The GitHub Pages site is built directly from `docs/` on `main`, without a build step or external dependencies. Its intended address is https://vc2015.github.io/rectangle-clt-singular/.

To enable publication, open this repository's **Settings → Pages**, choose **Deploy from a branch**, select **main** and **/docs**, and save. Subsequent commits to `docs/` update the site automatically.

The two PDFs in `docs/` are exact copies of the public manuscript and supplement in `research-rectangle-clt-singular/`. Keep their original filenames so that links between the documents continue to work. When replacing them, update the page counts, dates, and links in `docs/index.html`, the metadata in its head, `docs/citation.bib`, and `docs/sitemap.xml` as needed.

After arXiv assigns a permanent identifier, add its abstract-page link to the website and README and update the BibTeX record. The temporary submission number is not an arXiv identifier.

Keep the Lean scope statement aligned with `LEAN_VERIFICATION.md`. Later manuscript revisions are not covered by the archived certification unless a new verification record explicitly establishes their coverage.

The page provides descriptive and scholarly citation metadata and a sitemap. Search indexing is controlled by search engines; publication alone does not establish that the site has been indexed.
