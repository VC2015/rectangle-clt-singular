"""Build the public rectangle CLT blueprint from its immutable release."""
import argparse
from collections import defaultdict
from functools import lru_cache
from html import escape
import json
from pathlib import Path
import re
import subprocess

from evidence import collect

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
TAG = 'arxiv-v1-lean-2026-11'
RELEASE = '8a13fd23d35c8556f8a356cf9484fd5565c4edf1'
PAPER_COMMIT = '1803366cc994d9facae8e128ee180f68e319486f'
GIT = 'https://github.com/VC2015/rectangle-clt-singular'
HOME = 'https://vc2015.github.io/rectangle-clt-singular/'
PROJECT = 'lean-rectangle-clt-arxiv-v1'
BLUEPRINT_TITLE = ('Lean Verification of Sharp High-Dimensional Gaussian Approximations '
                   'over Rectangles without Covariance Restrictions')
ARXIV = 'https://arxiv.org/abs/2611.21474v1'
CHAIN = 'https://github.com/VC2015/generic-chaining/blob/b0db8f333413b3d0fc9e1e20825dc7bd4d7019fc/GenericChaining/'
MAIN = 'research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex'
SUPPLEMENT = 'research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex'


def ahref(url, label, klass=''):
    return f'<a class="{klass}" href="{escape(url, quote=True)}">{label}</a>'


def src(path):
    return f'{GIT}/blob/{RELEASE}/{PROJECT}/{path}'


def slug(label):
    return label.lower().replace(' ', '-').replace('.', '-')


def group(label):
    if re.search(r' [A-F]\.', label):
        return 'Main paper · Appendices A–F'
    if re.search(r' [GH]\.', label):
        return 'Supplement · Appendices G–I'
    return 'Main paper · Sections 1–5'


def paper_lines(loc, default='main'):
    if len(loc) == 3:
        which, start, end = loc
    else:
        which, (start, end) = default, loc
    assert which in ('main','supplement') and 0 < start <= end
    path = MAIN if which == 'main' else SUPPLEMENT
    assert end <= len((REPO / path).read_text().splitlines())
    return f'{GIT}/blob/{PAPER_COMMIT}/{path}#L{start}-L{end}'


@lru_cache(None)
def prose(text):
    if not re.search(r'\\\(|\$', text):
        return escape(text)
    text = text.replace(r'\mathsf A', r'\mathsf{A}').replace(r'\mathbb E',r'\mathbb{E}')
    p = subprocess.run(['pandoc','-f','markdown+tex_math_single_backslash-smart','-t','html5',
                        '--mathml','--wrap=none'],input=text,text=True,capture_output=True,check=True)
    if '[WARNING]' in p.stderr or 'merror' in p.stdout:
        raise ValueError(text + '\n' + p.stderr)
    return p.stdout.strip().removeprefix('<p>').removesuffix('</p>')


def state(label):
    if label == 'Conjecture 1':
        return '<span class="state open">Open conjecture</span>'
    if label == 'Lemma E.1':
        return '<span class="state caution">Checked for <i>A</i> ≥ 0</span>'
    return '<span class="state">Checked as stated</span>'


def name_link(d, full=True):
    label = d['name'] if full else d['name'].rsplit('.',1)[-1]
    return ahref(d['url'], '<code>'+escape(label)+'</code>', 'lean')


def env_anchor(env_id):
    return 'proof-'+env_id.lower()


def pass_list(passages):
    statuses = {
        'checked_printed_proof': '',
        'checked_with_documented_route_variation': 'Alternative derivation',
        'checked_supporting_binding_not_an_additional_printed_atom': 'Supporting calculation',
        'checked_alternative_route_support_printed_nonsimple_identity_separately_completed': 'Alternative route to the bound',
        'checked_with_explicit_nonnegative_budget_qualification': 'Requires A ≥ 0',
        'checked_separate_printed_identities_with_documented_route': 'Separately proved identity',
        'independently_reviewed_theorem_endpoint': 'Reviewed proof of the theorem',
        'separately_checked_example': 'Separately checked example',
    }
    items = []
    for passage in passages:
        ds = passage['declarations']
        if not passage['id'].startswith('H1.NONSIMPLE.'):
            ds = [{'name': passage['lean_name'], 'url': passage['lean_url']}]
        links = ' · '.join(name_link(d, False) for d in ds)
        title = passage.get('title') or passage['id']
        source = ahref(passage['source_url'], escape(title))
        status = statuses[passage['status']]
        note = f' <small>({status})</small>' if status else ''
        receipt = ' · ' + ahref(passage['ledger_url'], 'Review record') if passage.get('ledger_url') else ''
        items.append(f'<li>{source}{note} · {links}{receipt}</li>')
    return '<ul class="pass-list">'+''.join(items)+'</ul>' if items else ''


def dep_graph(label, notes, titles):
    # Display the immediate mathematical prerequisites in the author's reading order.
    deps=notes[label]['uses']
    def q(value):
        return json.dumps(value,ensure_ascii=False)
    dot=['digraph route {','rankdir=BT; bgcolor="transparent"; nodesep=0.12; ranksep=0.34; pad=0.08;',
         'node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=12, margin="0.13,0.10", color="#aebfd2", fillcolor="#f0f4fa", fontcolor="#233e60"];',
         'edge [arrowsize=.60,color="#8596b3"];']
    for i, name in enumerate([label]+deps):
        dot.append(f'{q(name)} [label={q(name)},href={q("#"+slug(name))},tooltip={q(titles[name])}'
                   + (', fillcolor="#344c7c",fontcolor="white"' if i==0 else '') +'];')
    for predecessor in deps:
        dot.append(f'{q(predecessor)} -> {q(label)};')
    if len(deps)>3:
        # Split wide rows into vertical layers without suggesting additional mathematical edges.
        for col in range(0,len(deps)-3,3):
            dot.append(f'{q(deps[col])} -> {q(deps[col+3])} [style=invis, weight=3];')
    data=subprocess.check_output(['dot','-Tsvg'],input='\n'.join(dot+['}']),text=True)
    data=data[data.index('<svg'):].strip()
    data=re.sub(r'\s+id="[^"]+"','',data)
    data=data.replace('xlink:href=', 'href=').replace('<title>route</title>',f'<title>Reading dependencies for {escape(label)}</title>')
    return data


def make_reader(statements):
    meta=json.loads((REPO/PROJECT/'correspondence/statements.json').read_text())['statements']
    evidence,envs=collect(REPO,RELEASE)
    notes=json.loads((HERE/'commentary.json').read_text())
    labels=[r['statement'] for r in meta]
    assert len(labels)==41 and len(envs)==34 and set(labels)==set(statements)==set(notes)==set(evidence)
    # Keep references usable when the self-contained reader is saved outside the site.
    statements={k:v.replace('href="../Rectangle_CLT_',f'href="{HOME}Rectangle_CLT_') for k,v in statements.items()}
    titles={r['statement']:r['title'] for r in meta}
    env_by_id={e['id']:e for e in envs}
    groups=defaultdict(list)
    for label in labels:
        groups[group(label)].append(label)
        assert set(notes[label]['uses']) <= set(labels) and label not in notes[label]['uses']
    def internal(label, caption=None):
        return ahref('#'+slug(label),escape(caption or label))
    secondary=[('overview','Overview'),('theorem-index','Theorem-to-Lean index'),('dependencies','Proof dependencies'),('proof-passages','Printed proofs'),('release','Verification record')]
    nav=''.join(ahref('#'+k,v,'primary') for k,v in secondary)
    nav+='<div class="groups">' + ''.join('<details><summary>'+g+'</summary>'+''.join(internal(k,k+' · '+titles[k]) for k in rows)+'</details>' for g,rows in groups.items())+'</div>'
    nav+='<div class="side-foot">'+ahref(HOME,'Paper homepage')+ahref(ARXIV,'Paper on arXiv')+ahref(GIT+'/tree/'+RELEASE,'Tagged sources')+'</div>'
    intro=f'''<section class="page" id="overview" data-title="Overview"><div class="front"><p class="eyebrow">Mathematical blueprint · arXiv v1</p><h1>{escape(BLUEPRINT_TITLE)}</h1>
<p class="sub">How accurately can a Gaussian vector approximate the probability that a sum of independent random vectors falls in a rectangle? The paper gives bounds even when the covariance is singular. This blueprint follows the proofs from the probability argument to the corresponding Lean declarations.</p>
<p class="byline">Paper by Victor Chernozhukov, Denis Chetverikov, Kengo Kato and Yuta Koike.<br>Blueprint by GPT-Sol 6.2, prompted by Victor Chernozhukov.</p>
<div class="tools">{ahref('#theorem-1','Read Theorem 1','action')}{ahref(HOME+'blueprint/rectangle-clt-blueprint.pdf','Download PDF')}<a download="rectangle-clt-blueprint.html" href="{HOME}blueprint/index.html">Download HTML</a>{ahref(ARXIV,'Paper on arXiv')}</div></div>
<p class="start">To follow the role of Gaussian width, start with {internal('Lemma C.2')}. For the envelope condition, see {internal('Lemma E.1')}.</p>
<h2 id="theorem-index">Theorem-to-Lean index</h2>
<p>Of the 40 named results, Lean checks 39 as stated. In Lemma E.1 it makes explicit that the envelope scale is nonnegative. Conjecture 1 remains open.</p>
<div class="searchbar js-only"><label for="filter">Find a result</label><input type="search" id="filter" placeholder="Theorem, subject or Lean name"><output id="matches" aria-live="polite">41 of 41</output></div>'''
    table=[]
    for label in labels:
        ds=evidence[label]['declarations']
        names=' '.join(d['name'] for d in ds)
        lean='<br>'.join(name_link(d,False) for d in ds) if ds else 'Open'
        query=escape((label+' '+titles[label]+' '+names).lower(),quote=True)
        table.append(f'<tr data-search="{query}"><td>{internal(label)}</td><td>{escape(titles[label])}</td><td>{lean}</td><td class="i-status">{state(label)}</td></tr>')
    intro+='<div class="table-scroll"><table class="index"><thead><tr><th>Result</th><th>Subject</th><th>Lean declaration</th><th class="i-status">Status</th></tr></thead><tbody>'+''.join(table)+'</tbody></table></div></section>'
    sections=[intro]
    for i,label in enumerate(labels):
        note=notes[label]; ev=evidence[label]; ds=ev['declarations']
        content=f'<p class="eyebrow">{group(label)}</p><h1>{escape(label)}</h1><p class="sub">{escape(titles[label])}</p><p>{prose(note["lead"])}</p>'
        content+=f'<div class="links">{state(label)} {ahref(ev["location"],"Manuscript statement")}</div><div class="statement">{statements[label]}</div>'
        if label=='Theorem 1':
            notation = prose(r'Here \(W=\sum_i\xi_i\) is a sum of independent centered vectors with \(\|\xi_i\|_\infty\le\delta\). The Gaussian vector \(Z\) has the same covariance \(\Sigma\), with unit marginal variances. The distance \(\rho_{\mathcal R}\) is the largest discrepancy in their probabilities over axis-aligned rectangles. The Gaussian width is \(g_\Sigma=\mathbb{E}\|Z\|_\infty\). The two logarithmic factors are \(L=\log(ep)\) and \(D_L=1+\max\{0,\log(1/(\delta\sqrt L))\}\).')
            content+='<details class="panel"><summary>Assumptions and notation</summary><div class="inside"><p>'+notation+'</p>'+ahref(paper_lines([145,231]),'Setup and relative moment bounds')+'</div></details>'
        if label=='Lemma E.1':
            content+='<aside class="note"><p><strong>Envelope condition.</strong> Lean assumes <i>A</i> ≥ 0. The proof handles zero separately and uses a positive truncation level in the other case. The application takes the nonnegative root of the moment bound.</p></aside>'
        if label=='Lemma H.1':
            content+=f'<aside class="note route"><p><strong>How the proofs differ.</strong> The printed proof estimates the ridge contribution directly at the given threshold. The Lean proof first obtains the estimate at almost every nearby threshold, then uses continuity and Fatou’s lemma to pass to the given threshold. The nonsimple-ridge Gauss–Green identity and the spherical conormal identity for any number of edges have separate Lean proofs. For the spherical identity Lean uses Gaussian first moments and polar coordinates. The printed tangent-field and divergence calculation at lines 1112–1123 remains outside that correspondence. {ahref(src("correspondence/supplemental-h-nonsimple-printed-completion.json"),"H.1 completion record")}</p></aside>'
        lines=note.get('stepLines',[])
        if lines: assert len(lines)==len(note['steps']),label
        parts=[]
        for n,step in enumerate(note['steps']):
            link=''
            if lines and lines[n]:
                default='supplement' if group(label).startswith('Supplement') else 'main'
                link=' '+ahref(paper_lines(lines[n],default),'Paper passage','proof-link')
            parts.append('<li>'+prose(step)+link+'</li>')
        deps=note['uses']
        chips=('<p class="caption">Results used in this argument</p><div class="chips">'+''.join(internal(x) for x in deps)+'</div>') if deps else ''
        content+='<details class="panel proof" open><summary>'+('Why the question is open' if label=='Conjecture 1' else 'Proof outline')+'</summary><div class="inside"><ol>'+''.join(parts)+'</ol>'+chips+'</div></details>'
        if ds:
            dl=''.join('<li>'+name_link(d)+'</li>' for d in ds)
            if label=='Lemma C.2':
                dl+=''.join('<li>'+ahref(CHAIN+path,'<code>GenericChaining.'+name+'</code>','lean')+'</li>' for name,path in [('dirksen_expectation','Dirksen.lean#L24'),('gamma2_le_gaussianWidth','GaussianChaining.lean#L28')])
                dl+='<li>'+ahref('https://vc2015.github.io/generic-chaining/','Read the generic-chaining blueprint')+'</li>'
            content+='<details class="panel code" open><summary>Lean declarations</summary><div class="inside"><ul class="code-list">'+dl+'</ul></div></details>'
        if ev['proofs'] or ev['passages']:
            pls=''.join('<li>'+ahref('#'+env_anchor(key),escape(env_by_id[key]['title']))+'</li>' for key in ev['proofs'])
            content+='<details class="panel evidence print-hide"><summary>Paper and Lean proof passages</summary><div class="inside">'+('<ul>'+pls+'</ul>' if pls else '')+pass_list(ev['passages'])+'</div></details>'
        if label=='Lemma H.1':
            content+='<p class="links">'+ahref(src('writeups/H1_continuity_Fatou.pdf'),'Mathematical note on the continuity argument (PDF)','proof-link')+'</p>'
        if note.get('ledgers'):
            files=[path for name in note['ledgers'] if (path:= REPO/PROJECT/'correspondence'/(name+'.json')).is_file()]
            content+='<div class="links print-hide">'+''.join(ahref(src('correspondence/'+path.name),'Detailed proof record'+(f' {i+1}' if len(files)>1 else '')) for i,path in enumerate(files))+'</div>'
        if note.get('routeNote'):
            content+='<p class="meta">'+prose(note['routeNote'])+'</p>'
        prev=internal(labels[i-1],'← '+labels[i-1]) if i else ahref('#theorem-index','← Index')
        nxt=internal(labels[i+1],labels[i+1]+' →') if i+1<len(labels) else ahref('#proof-passages','Printed proofs →')
        content+='<nav class="prevnext" aria-label="Adjacent results">'+prev+ahref('#theorem-index','Index')+nxt+'</nav>'
        sections.append(f'<section class="page result" id="{slug(label)}" data-title="{label}">{content}</section>')
    graph_labels=[k for k in labels if notes[k]['uses']]
    options=''.join(f'<option value="graph-{slug(k)}">{escape(k)} · {escape(titles[k])}</option>' for k in graph_labels)
    def dep_links(key):
        return ''.join(internal(dep) for dep in notes[key]['uses'])
    plots=''.join(f'<div class="graph-card" id="graph-{slug(k)}"><h3>{escape(k)} · {escape(titles[k])}</h3><div class="graph-viz">{dep_graph(k,notes,titles)}</div><p class="links">{internal(k,"Read "+k)}</p><div class="chips" aria-label="Supporting results">{dep_links(k)}</div></div>' for k in graph_labels)
    sections.append('<section class="page" id="dependencies" data-title="Proof dependencies"><p class="eyebrow">Reading the argument</p><h1>Proof dependencies</h1><p>Each arrow leads from a supporting result to the argument that uses it. These diagrams follow the mathematical exposition. The verification record links to the larger dependency graphs extracted from Lean.</p><p class="graph-form js-only"><label for="graph-choice">Choose a result&nbsp;</label><select id="graph-choice">'+options+'</select></p>'+plots+'</section>')
    blocks=[]
    for env in envs:
        rs=env['results']; title=escape(env['title'])
        blocks.append(f'<details class="env" id="{env_anchor(env["id"])}"><summary>{title}</summary><div class="links">{ahref(env["source_url"],"Printed proof")}{ahref(env["ledger_url"],"Correspondence record","lean")}</div><div class="chips">'+''.join(internal(r) for r in rs)+'</div>'+pass_list(env['passages'])+'</details>')
    sections.append('<section class="page" id="proof-passages" data-title="Printed proofs"><p class="eyebrow">Paper and supplement</p><h1>Printed proofs</h1><p>The two manuscripts contain 34 explicit proof environments. Open an entry to move between a step in the printed argument and its formal evidence. Proofs given in running prose can also be reached from their theorem pages.</p>'+''.join(blocks)+'</section>')
    sections.append(f'''<section class="page" id="release" data-title="Verification record"><p class="eyebrow">Sources and scope</p><h1>Verification record</h1><p>This reader accompanies {ahref(ARXIV,'arXiv:2611.21474v1')} and its separate supplement. The release tag {ahref(GIT+'/releases/tag/'+TAG,'<code>'+TAG+'</code>')} identifies commit {ahref(GIT+'/commit/'+RELEASE,'<code>'+RELEASE[:7]+'</code>')}. The {ahref(src('source-pins.json'),'source manifest')} records the manuscript hashes, Lean 4.19.0 and the mathematical library revisions.</p>
<h2>What was checked</h2><p>The first clean run built the library and audited the released results. A second run at the same proof commit checked the full types of 1,949 declarations and recorded their dependencies. A later clean run built the whole library with the supplemental H.1 extension, directly checked 66 source modules and audited 182 registered targets. All three records report successful completion. The axiom audits found only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>.</p>
<ul><li>{ahref(src('evidence/final-clean-checkpoint/run.json'),'Baseline build and audit')}</li><li>{ahref(src('evidence/final-clean-mapping/run.json'),'Full manuscript mapping and dependency record')}</li><li>{ahref(src('evidence/supplemental-h-nonsimple-printed/clean-checkpoint/run.json'),'Clean H.1 extension')}</li><li>{ahref(src('REPRODUCIBILITY.md'),'Reproduction instructions')}</li></ul><h2>How to read the evidence</h2><p>The theorem index identifies the checked conclusion. The proof entries follow the reasoning in the paper and give links to corresponding Lean declarations or documented changes of argument. For example, {internal('Lemma E.1')} states its sign convention explicitly, and {internal('Lemma H.1')} distinguishes the proof of a bound from the separately proved identities. {ahref(src('correspondence/final-coverage.json'),'Full passage ledger')}.</p></section>''')
    css=(HERE/'reader.css').read_text();js=(HERE/'reader.js').read_text()
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{escape(BLUEPRINT_TITLE)} · Blue Blueprint</title><meta name="description" content="An interactive mathematical blueprint for arXiv:2611.21474v1, linking the rectangle CLT, its proofs and its supplement to Lean."><meta name="robots" content="index,follow"><link rel="canonical" href="{HOME}blueprint/"><style>{css}</style></head><body><a class="skip" href="#main">Skip to content</a><header class="mast"><button type="button" class="menu" id="menu" aria-expanded="false" aria-controls="contents">Contents</button><a class="brand" href="#overview">Blue Blueprint</a><span class="series">Rectangle CLT</span><a class="version" href="#release">arXiv v1 · Lean 4</a></header><nav class="sidebar" id="contents" aria-label="Table of contents">{nav}</nav><main id="main"><div class="shell">{''.join(sections)}</div></main><script>{js}</script></body></html>
'''


if __name__=='__main__':
    from statement_math import build as build_statements
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--statements',type=Path,help='Typeset statement map produced by the manuscript adapter')
    args=parser.parse_args()
    tagged=subprocess.check_output(['git','rev-parse',TAG+'^{commit}'],cwd=REPO,text=True).strip()
    if tagged!=RELEASE:
        raise SystemExit('Release tag differs from the verified commit')
    subprocess.run(['git','diff','--exit-code','--quiet',RELEASE,'--',PROJECT,MAIN,SUPPLEMENT,
                    'docs/Rectangle_CLT_arXiv_2026-11-16.pdf','docs/Rectangle_CLT_Supplement_2026-11-16.pdf',
                    'lean-kane','lean-rectangle-clt-local','lean-rectangle-clt-singular'],cwd=REPO,check=True)
    target=REPO/'docs/blueprint/index.html'
    target.parent.mkdir(exist_ok=True)
    target.write_text(make_reader(json.loads(args.statements.read_text()) if args.statements else build_statements()),encoding='utf-8')
    print(target)
