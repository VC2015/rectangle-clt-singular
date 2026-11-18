"""Export the print edition with vector formulas and clickable source links."""
import base64
import json
from pathlib import Path
import re
import subprocess
from lxml import html, etree
from weasyprint import HTML

HERE=Path(__file__).resolve().parent
DEST=HERE.parent/'docs/blueprint'
PUBLIC='https://vc2015.github.io/rectangle-clt-singular/blueprint/'


def print_reader():
    tree=html.parse(str(DEST/'index.html'))
    body=tree.getroot()
    for el in body.xpath('//script|//style|//header|//nav|//button|//*[@id="dependencies" or @id="proof-passages"]|//*[contains(concat(" ",normalize-space(@class)," "), " print-hide ") or contains(concat(" ",normalize-space(@class)," "), " tools ") or contains(concat(" ",normalize-space(@class)," "), " searchbar ") or contains(concat(" ",normalize-space(@class)," "), " skip ")]'):
        el.drop_tree()
    for child in body.xpath('//details'):
        child.tag='div'
    for summary in body.xpath('//summary'):
        summary.tag='h3'
    for result in body.xpath('//section[contains(@class,"result")]'):
        links=result.find("div[@class='links']")
        link=etree.SubElement(links,'a',href=PUBLIC+'#'+result.get('id'))
        link.text='Interactive proof and source passages'
    elems=body.xpath('//math')
    for ann in body.xpath('//annotation'):
        ann.drop_tree()
    equations=[(etree.tostring(m,encoding='unicode',with_tail=False),m.get('display')=='block') for m in elems]
    output=json.loads(subprocess.check_output(['node',str(HERE/'print_math.cjs')],input=json.dumps(equations),text=True))
    for math,svg in zip(elems,output,strict=True):
        node=etree.fromstring(svg.encode())
        width=node.get('width');height=node.get('height'); assert width.endswith('ex') and height.endswith('ex')
        baseline=re.search(r'vertical-align:\s*([-\d.]+)ex',node.get('style',''))
        base=float(baseline[1]) if baseline else 0.0
        fig=html.Element('img',src='data:image/svg+xml;base64,'+base64.b64encode(svg.encode()).decode(),
                         alt=''.join(math.itertext()))
        fig.set('class','formula block' if math.get('display')=='block' else 'formula')
        fig.set('style',f'width:{float(width[:-2])*0.48:.4f}em;vertical-align:{base*0.48:.4f}em')
        fig.tail=math.tail;math.getparent().replace(math,fig)
    head=body.find('head')
    etree.SubElement(head,'meta',name='author',content='GPT-Sol 6.2, prompted by Victor Chernozhukov')
    etree.SubElement(head,'style').text=(HERE/'print.css').read_text()
    text=etree.tostring(body,encoding='unicode',method='html')
    HTML(string=text,base_url=PUBLIC).write_pdf(DEST/'rectangle-clt-blueprint.pdf')


if __name__=='__main__':
    print_reader()
