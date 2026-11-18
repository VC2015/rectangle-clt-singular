# Building the rectangle CLT blueprint

The [interactive reader](https://vc2015.github.io/rectangle-clt-singular/blueprint/) and its [print edition](https://vc2015.github.io/rectangle-clt-singular/blueprint/rectangle-clt-blueprint.pdf) follow the main paper and supplement in the public release `arxiv-v1-lean-2026-11`. The build checks the release commit, manuscript files and archived evidence before rendering the statements. The code and links use the manuscript and Lean revisions recorded in that release.

From the root of a clone with the tag and its history, run the following command. The reader requires Python 3.10 or later, Pandoc 3, Graphviz and Poppler utilities. The HTML includes its styles, scripts, diagrams and MathML, so a downloaded copy can be read offline.

```sh
git fetch origin tag arxiv-v1-lean-2026-11
python3 blueprint/build.py
```

To build the PDF, install WeasyPrint and lxml in a Python environment and MathJax in a temporary Node directory. WeasyPrint also requires its usual system libraries. Both editions are written to `docs/blueprint/`.

```sh
python3 -m pip install 'weasyprint==66.0' lxml
math_dir=$(mktemp -d)
npm install --prefix "$math_dir" mathjax-full@3.2.2
NODE_PATH="$math_dir/node_modules" python3 blueprint/print_reader.py
```

The statement adapter reads the tagged LaTeX and resolves numbered references against the published PDFs. The evidence adapter checks manuscript hashes and links the printed proofs to the declarations in the release records. The introductions, proof outlines and suggested reading dependencies are in `commentary.json`. The diagrams show how a reader can follow the argument. The verification record links to the formal dependency data.

To exercise the reader at desktop and phone widths, install Python Playwright and Chromium, then run `python3 blueprint/check_reader.py`. Pass `--url` to check a deployed copy. To reproduce the Lean verification itself, follow the [release instructions](../lean-rectangle-clt-arxiv-v1/REPRODUCIBILITY.md).
