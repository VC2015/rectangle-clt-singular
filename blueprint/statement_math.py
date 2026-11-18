#!/usr/bin/env python3
"""Typeset the 41 pinned manuscript statements as native MathML and linked prose.

Run from any directory: python3 blueprint/statement_math.py /tmp/statements.json
Requires Python 3.10+, Pandoc with --mathml, and Poppler (pdfinfo, pdftotext).
The deployed fragments have no JavaScript, external font, or network dependency.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
import hashlib
from html import escape
import json
from pathlib import Path
import re
import subprocess
import sys
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "lean-rectangle-clt-arxiv-v1" / "correspondence" / "statements.json"
LABEL = re.compile(r"\\label\{([^}]+)\}")
NUMBERED_ENV = re.compile(r"\\begin\{(subequations|equation|align)\}")
REFERENCE = re.compile(r"\\(eqref|ref)\{([^}]+)\}")
FORMULA = re.compile(
    r"\\begin\{(?P<env>equation|align)\}(?P<content>.*?)\\end\{(?P=env)\}"
    r"|\\\[(?P<display>.*?)\\\]|\\\((?P<inline>.*?)\\\)|\$(?P<dollar>[^$]+)\$",
    re.S,
)


@dataclass(frozen=True)
class Reference:
    number: str
    pdf_name: str
    page: int
    paper: str

    def link(self, caption: str, css_class: str = "") -> str:
        target = f"../{self.pdf_name}#page={self.page}"
        description = f"{self.paper}, PDF page {self.page}"
        css = f' class="{css_class}"' if css_class else ""
        return f'<a{css} href="{escape(target)}" title="{description}">{escape(caption)}</a>'


def command(args: list[str], stdin: str | None = None) -> str:
    process = subprocess.run(args, input=stdin, text=True, capture_output=True)
    if process.returncode or process.stderr.strip():
        raise RuntimeError(f"{args[0]}: {process.stderr.strip()} (exit {process.returncode})")
    return process.stdout


def source_equation_labels(tex: str) -> list[str]:
    """Read the labels in counter order, including the parent of (10a)–(10b)."""
    labels = []
    for start in NUMBERED_ENV.finditer(tex):
        env = start[1]
        if env == "subequations":
            labels.append(LABEL.match(tex, start.end())[1])
            continue
        end = tex.index(r"\end{" + env + "}", start.end())
        body = tex[start.end():end]
        rows = re.split(r"\\\\(?:\[[^\]]*\])?", body) if env == "align" else [body]
        for row in rows:
            if r"\notag" in row or r"\nonumber" in row:
                continue
            names = LABEL.findall(row)
            if len(names) != 1:
                raise ValueError(f"Expected one label for a numbered row: {row}")
            labels.append(names[0])
    return labels


def pdf_references(tex: str, pdf: Path, paper: str, rows: list[dict]) -> dict[str, Reference]:
    # The left-numbered displays of these two PDFs make it possible to recover
    # their printed numbers. A second source, the PDF destination tree, checks
    # page assignments, including align rows and the parent of the subequations.
    layouts = command(["pdftotext", "-layout", str(pdf), "-"]).split("\f")
    numbers = {}
    for page, layout in enumerate(layouts, 1):
        for number in re.findall(r"^\s*\(((?:[A-I]\.)?\d+[ab]?)\)(?=\s|$)", layout, re.M):
            if number.endswith("a"):
                numbers.setdefault(number[:-1], page)
            numbers.setdefault(number, page)
    destinations = defaultdict(list)
    dest_text = command(["pdfinfo", "-dests", str(pdf)])
    for page, kind, index in re.findall(r'^\s*(\d+)\s+\[.*?\]\s+"([a-z]+)\.(\d+)"$', dest_text, re.M):
        destinations[kind].append((int(index), int(page)))
    for items in destinations.values():
        items.sort()

    labels = source_equation_labels(tex)
    refs = {}
    for label, (number, printed_page), (_, page) in zip(labels, numbers.items(), destinations["equation"], strict=True):
        if page != printed_page:
            raise ValueError(f"PDF text and destination disagree for {label}, ({number})")
        refs[label] = Reference(number, pdf.name, page, paper)

    by_kind = defaultdict(list)
    for row in rows:
        kind, number = row["statement"].split()
        by_kind[kind.lower()].append((row["tex_label"], number))
    for kind, statements in by_kind.items():
        for (label, number), (_, page) in zip(statements, destinations[kind], strict=True):
            refs[label] = Reference(number, pdf.name, page, paper)
    return refs


def prose(tex: str, refs: dict[str, Reference]) -> str:
    tex = re.sub(r"\\(?:begin|end)\{subequations\}", "", tex)
    tex = LABEL.sub("", tex)
    tex = re.sub(r"\\(?:par|noindent)\b", "\n\n", tex)
    tex = re.sub(r"\\textup\{([^{}]*)\}", r"\1", tex)
    html = REFERENCE.sub(lambda m: refs[m[2]].link(
        f"({refs[m[2]].number})" if m[1] == "eqref" else refs[m[2]].number
    ), escape(tex))
    html = html.replace("{", "").replace("}", "").replace("~", "\u00a0")
    if "\\" in html:
        raise ValueError(f"Unprocessed manuscript prose: {html}")
    return html


class MathBatch:
    """Use Pandoc's manuscript macro expansion and its native MathML writer."""
    def __init__(self, preamble: str):
        self.preamble = preamble
        self.formulas: list[tuple[bool, str]] = []

    def token(self, tex: str, display: bool) -> str:
        self.formulas.append((display, tex))
        return f"@@MATH{len(self.formulas) - 1}@@"

    def render(self) -> list[str]:
        formulas = [r"\[" + s + r"\]" if display else r"\(" + s + r"\)"
                    for display, s in self.formulas]
        source = self.preamble + "\n\n" + "\n\n".join(formulas)
        rendered = command(["pandoc", "--from=latex", "--to=html5", "--mathml", "--wrap=none"], source)
        mathml = re.findall(r"<math\b.*?</math>", rendered, re.S)
        if len(mathml) != len(formulas):
            raise ValueError(f"Pandoc rendered {len(mathml)} of {len(formulas)} formulas")
        results = []
        for (display, tex), node in zip(self.formulas, mathml):
            # Native elements speak the mathematics. No TeX fallback is needed.
            node = re.sub(r"<annotation\b[^>]*>.*?</annotation>", "", node, flags=re.S)
            node = node.replace("<semantics>", "").replace("</semantics>", "")
            node = node.replace(r"<mo>\</mo>", "<mo>∖</mo>")
            if display:
                node = node.replace("<math ", '<math class="statement-math" ', 1)
            if "<merror" in node or "\\" in node or "??" in node or "\ufffd" in node:
                raise ValueError(f"Unrendered mathematics in {tex}: {node}")
            ET.fromstring(node)
            results.append(node)
        return results


def statement_body(tex: str, label: str, refs: dict[str, Reference], batch: MathBatch) -> str:
    statement = re.fullmatch(
        r"\\begin\{([^}]+)\}\[([^\]]+)\]\s*\\label\{([^}]+)\}(.*?)\\end\{\1\}\s*", tex, re.S
    )
    if statement is None or statement[3] != label:
        raise ValueError(f"Cannot identify complete environment for {label}")
    body = statement[4]
    blocks = []
    paragraph = ""

    def flush() -> None:
        nonlocal paragraph
        for piece in re.split(r"\n\s*\n", paragraph):
            piece = re.sub(r"[\t\n\r ]+", " ", piece).strip()
            if piece:
                blocks.append("<p>" + piece + "</p>")
        paragraph = ""

    def display(formula: str, number_label: str | None) -> None:
        flush()
        number = ""
        if number_label:
            ref = refs[number_label]
            number = ref.link(f"({ref.number})", "statement-eqno")
        blocks.append('<div class="statement-display">' + number + batch.token(formula, True) + "</div>")

    cursor = 0
    for match in FORMULA.finditer(body):
        paragraph += prose(body[cursor:match.start()], refs)
        cursor = match.end()
        if match["env"]:
            formula = match["content"]
            labels = LABEL.findall(formula)
            if not labels:
                raise ValueError(f"Unlabelled numbered display in {label}")
            if match["env"] == "align" and len(labels) > 1:
                for row in re.split(r"\\\\", formula):
                    row_label, = LABEL.findall(row)
                    display(LABEL.sub("", row).replace("&", ""), row_label)
            else:
                formula = LABEL.sub("", formula).replace(r"\notag", "")
                if match["env"] == "align":
                    formula = r"\begin{aligned}" + formula + r"\end{aligned}"
                # split and aligned use the same alignment points in these sources.
                formula = formula.replace("{split}", "{aligned}")
                display(formula, labels[0])
        elif match["display"] is not None:
            display(match["display"], None)
        else:
            paragraph += batch.token(match["inline"] or match["dollar"], False)
    paragraph += prose(body[cursor:], refs)
    flush()
    return "\n".join(blocks)


def build() -> dict[str, str]:
    ledger = json.loads(LEDGER.read_text())
    statements = ledger["statements"]
    if len(statements) != 41:
        raise ValueError("Unexpected size of the pinned statement ledger")
    all_refs = {}
    texts = {}
    macros = set()
    for name, info in ledger["source_files"].items():
        path = ROOT / info["path"]
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != info["sha256"]:
            raise ValueError(f"Manuscript hash mismatch: {path}")
        tex = data.decode("utf-8")
        texts[name] = tex.splitlines(keepends=True)
        preamble = tex.split(r"\begin{document}", 1)[0]
        macros.update(re.findall(r"^\\newcommand\{\\[a-zA-Z]+\}(?:\[\d+\])?\{[^\n]*\}$", preamble, re.M))
        pdf = ROOT / "docs" / path.with_suffix(".pdf").name
        rows = [s for s in statements if s["location"]["source"] == name]
        refs = pdf_references(tex, pdf, "Main paper" if name == "main" else "Supplement", rows)
        if refs.keys() & all_refs.keys():
            raise ValueError("Ambiguous labels in the main paper and supplement")
        all_refs.update(refs)

    batch = MathBatch("\n".join(sorted(macros)))
    fragments = {}
    for row in statements:
        loc = row["location"]
        first, last = loc["lines"]
        tex = "".join(texts[loc["source"]][first - 1:last])
        if hashlib.sha256(tex.encode()).hexdigest() != loc["sha256"]:
            raise ValueError(f"Statement span hash mismatch: {row['statement']}")
        fragments[row["statement"]] = statement_body(tex, row["tex_label"], all_refs, batch)
    mathml = batch.render()
    for label, value in fragments.items():
        value = re.sub(r"@@MATH(\d+)@@", lambda m: mathml[int(m[1])], value)
        if "??" in value or "@@MATH" in value or "\\" in value:
            raise ValueError(f"Unresolved content in {label}")
        ET.fromstring("<article>" + value + "</article>")
        fragments[label] = value
    return fragments


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="JSON file of HTML fragments, keyed by printed result name")
    args = parser.parse_args()
    fragments = build()
    args.output.write_text(json.dumps(fragments, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Typeset {len(fragments)} statements.", file=sys.stderr)
