"""Check the static reader on desktop and mobile."""
import argparse
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from functools import partial
from pathlib import Path
from threading import Thread
import shutil
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[1]


def check(page, url, mobile):
    errors = []
    page.on('pageerror', lambda e: errors.append(str(e)))
    page.goto(url + '#theorem-1',wait_until='load')
    assert page.locator('.page:visible').get_attribute('id') == 'theorem-1'
    assert page.locator('#theorem-1 .statement math, #theorem-1 .statement svg').count() > 0
    assert page.locator('section.result').count() == 41
    assert page.locator('#proof-passages details.env').count() == 34
    assert page.locator('merror,mjx-merror,.math-error').count() == 0
    for label in ('lemma-c-2','lemma-e-1','lemma-h-1','conjecture-1'):
        page.goto(url+'#'+label)
        assert page.locator('.page:visible').get_attribute('id') == label
    assert not page.locator('#conjecture-1 .code-list').count()
    page.goto(url+'#lemma-c-2')
    assert page.locator('#lemma-c-2 a[href*="generic-chaining/blob/"]').count() >= 2
    page.goto(url+'#overview')
    page.locator('#filter').fill('expected_maximum')
    assert 0 < page.locator('table.index tbody tr:visible').count() < 41
    page.locator('#filter').fill('Lemma E.1')
    assert page.locator('table.index tbody tr:visible').count() == 1
    page.locator('table.index tbody tr:visible a').first.click()
    assert 'A ≥ 0' in page.locator('#lemma-e-1 .state').inner_text()
    page.locator('#lemma-e-1 .proof > summary').focus()
    page.keyboard.press('Enter')
    assert not page.locator('#lemma-e-1 .proof').evaluate('(e)=>e.open')
    page.keyboard.press('Enter')
    page.locator('#filter').evaluate("(e)=>{e.value=''; e.dispatchEvent(new Event('input'))}")
    if mobile:
        page.locator('#menu').click()
        assert page.locator('#contents').is_visible()
    page.locator('#contents a[href="#dependencies"]').click()
    graph = page.locator('.graph-card:visible')
    assert graph.count() == 1
    graph.locator('svg a').first.click()
    assert page.locator('.page.result:visible').count() == 1
    page.goto(url+'#proof-passages')
    env = page.locator('.env').first.get_attribute('id')
    page.goto(url+'#'+env)
    assert page.locator('#'+env).evaluate('(e)=>e.open')
    for target in ('#theorem-1','#lemma-h-1','#theorem-8','#overview','#dependencies'):
        page.goto(url+target)
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth'),target
    assert not errors,errors


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url',help='Check an already deployed reader')
    args=parser.parse_args()
    handler=partial(SimpleHTTPRequestHandler,directory=ROOT/'docs')
    server=ThreadingHTTPServer(('127.0.0.1',0),handler)
    Thread(target=server.serve_forever,daemon=True).start()
    base=args.url or f'http://127.0.0.1:{server.server_port}/blueprint/'
    with sync_playwright() as p:
        browser=p.chromium.launch(executable_path=shutil.which('chromium'),args=['--no-sandbox'])
        for w,h in ((1360,880),(390,844)):
            page=browser.new_page(viewport={'width':w,'height':h})
            check(page,base,w<600)
            page.close()
        browser.close()
    server.shutdown()
    print('Desktop, mobile, deep links, theorem search, graph navigation and proof disclosures passed.')
