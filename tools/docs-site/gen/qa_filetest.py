#!/usr/bin/env python3
"""QA under file://: open pages in headless Chromium, click around, assert no console errors, no failed requests,
and zero non-file requests. Screenshots to <out>/../qa/.  Usage: python3 gen/qa_filetest.py out/html [deep-node-name]"""
import sys, os, time, json
from playwright.sync_api import sync_playwright
out = os.path.abspath(sys.argv[1]); qa = os.path.join(os.path.dirname(out), 'qa'); os.makedirs(qa, exist_ok=True)
deep = sys.argv[2] if len(sys.argv) > 2 else None
errors = []; nonfile = []; failed = []; timings = {}; mathstats = {}
report_path = os.path.join(os.path.dirname(out), 'render-report.json')
rep_in = json.load(open(report_path)) if os.path.exists(report_path) else {}
MATH_JS = "() => [document.querySelectorAll('span.tex').length, document.querySelectorAll('span.tex.k').length, document.querySelectorAll('span.tex.src').length, document.querySelectorAll('.katex-error, span.tex.k [style*=\"#cc0000\"], span.tex.k [style*=\"204, 0, 0\"]').length, document.querySelectorAll('code.tex').length, document.querySelectorAll('span.tex.k .katex').length]"
def attach(pg):
    pg.on('console', lambda m: errors.append(('console.' + m.type, pg.url, m.text)) if m.type in ('error',) else None)
    pg.on('pageerror', lambda e: errors.append(('pageerror', pg.url, str(e))))
    pg.on('request', lambda r: nonfile.append(r.url) if not r.url.startswith(('file://', 'data:', 'about:')) else None)
    pg.on('requestfailed', lambda r: failed.append((pg.url, r.url, r.failure)))
def shot(pg, name, full=False):
    pg.screenshot(path=os.path.join(qa, name + '.png'), full_page=full)
with sync_playwright() as p:
    b = p.chromium.launch()
    ctx = b.new_context(viewport={'width': 1280, 'height': 900})
    pg = ctx.new_page(); attach(pg)
    def go(rel, name, wait=None, full=False):
        t0 = time.time(); pg.goto('file://' + os.path.join(out, rel)); 
        if wait: pg.wait_for_selector(wait, timeout=15000)
        else: pg.wait_for_load_state('load')
        timings[name] = round(time.time() - t0, 2); shot(pg, name, full)
    def check_math(name, expect_some=False):
        """English-layer mathematics is TeX source in span.tex, typeset in the page by the bundled KaTeX: all of it must be typeset."""
        c = pg.evaluate(MATH_JS); mathstats[name] = {'fragments': c[0], 'typeset': c[1], 'left_as_source': c[2], 'katex_error_boxes': c[3], 'build_rejected': c[4]}
        if c[0] and c[1] != c[0]: errors.append(('qa', pg.url, 'mathematics not typeset: %d of %d fragments, %d shown as source' % (c[1], c[0], c[2])))
        if c[3]: errors.append(('qa', pg.url, '%d fragments rendered in the KaTeX error colour / error boxes' % c[3]))
        if c[5] != c[1]: errors.append(('qa', pg.url, 'typeset spans and KaTeX roots differ (%d roots in %d spans): double or missing typesetting' % (c[5], c[1])))
        if expect_some and not c[0]: errors.append(('qa', pg.url, 'expected English mathematics on this page, found none'))
    go('index.html', '01-index', 'svg')
    go('route/index.html', '02-route-index')
    go('route/s4.html', '03-route-s4')
    go('dag/index.html', '04-dag', 'svg')
    svgw = pg.eval_on_selector('.figure svg', 'e => e.getBoundingClientRect().width')
    if svgw <= 1280: errors.append(('qa', pg.url, 'landmark graph is not at reading size by default (svg width %s)' % svgw))
    pg.click('.figure.zoomable', position={'x': 5, 'y': 5}); time.sleep(0.3)
    svgw2 = pg.eval_on_selector('.figure svg', 'e => e.getBoundingClientRect().width')
    if svgw2 > 1280: errors.append(('qa', pg.url, 'click-to-fit did not shrink the landmark graph (svg width %s)' % svgw2))
    pg.click('.figure.zoomable', position={'x': 5, 'y': 5}); time.sleep(0.3)
    # click a node in the landmark DAG
    a = pg.query_selector('.figure svg a')
    if a: a.click(); pg.wait_for_selector('#stmt-box pre', timeout=15000); shot(pg, '05-dag-click')
    go('def/FLTPrelim_FreyPackage.html', '06-def'); check_math('06-def', expect_some=True)
    go('def/index.html', '07-def-index')
    go('docs/structure.html' if os.path.exists(os.path.join(out, 'docs', 'structure.html')) else 'docs/readme.html', '08-docs-page')   # a rendered Markdown document (structure.html is absent under --no-docs)
    go('thm.html#fermat_last_theorem', '09-thm-root', '#graph svg')
    go('thm.html#FreyPackage.no_frey_package', '10-thm-nofrey', '#graph svg', full=True); pg.wait_for_selector('#stmt-box pre', timeout=15000); check_math('10-thm-nofrey', expect_some=True); shot(pg, '10-thm-nofrey', True)
    # expand a neighbour in the graph: click a '+' cell
    plus = pg.query_selector('#graph svg a[*|href^="#x:"]')
    if plus:
        plus.click(); time.sleep(1.0); shot(pg, '11-thm-expanded')
    else: errors.append(('qa', pg.url, 'no expand control found in graph'))
    pg.click('#g-path'); time.sleep(0.8)
    if deep:
        go('thm.html#' + deep, '12-thm-deep', '#graph svg', full=True)
        t0 = time.time(); pg.wait_for_selector('#stmt-box pre'); timings['12-deep-stmt'] = round(time.time() - t0, 2); check_math('12-thm-deep')
    # the theorem whose English carries the most mathematics: time from navigation until every fragment is typeset
    mm = (rep_in.get('english') or {}).get('most_math_theorem')
    if mm:
        pg.goto('about:blank'); t0 = time.time(); pg.goto('file://' + os.path.join(out, 'thm.html') + '#' + mm)
        pg.wait_for_function("() => document.querySelector('#stmt-box pre') && document.querySelectorAll('span.tex').length > 0 && document.querySelectorAll('span.tex:not(.k):not(.src)').length === 0", timeout=20000)
        timings['12b-most-math-until-typeset'] = round(time.time() - t0, 2); check_math('12b-most-math', expect_some=True); shot(pg, '12b-most-math', True)
    # the heaviest namespace page (static, the largest HTML file of the site)
    big = max((os.path.getsize(os.path.join(out, 'areas', f)), f) for f in os.listdir(os.path.join(out, 'areas')))[1]
    go('areas/' + big, '12c-area-largest'); timings['12c-area-largest (%s, %.1f MB)' % (big, os.path.getsize(os.path.join(out, 'areas', big)) / 1e6)] = timings.pop('12c-area-largest')
    # search
    pg.fill('#q', 'level lowering odd'); pg.wait_for_selector('#q-results a.sr', timeout=15000); shot(pg, '13-search')
    first = pg.query_selector('#q-results a.sr'); href = first.get_attribute('href'); first.click(); pg.wait_for_selector('#stmt-box pre', timeout=15000); shot(pg, '14-search-result')
    pg.fill('#q', 'FreyPackage'); pg.wait_for_selector('#q-results a.sr', timeout=15000); shot(pg, '15-search-def')
    # a static page's search (lazy meta load from ../)
    go('route/s3.html', '16-route-s3'); pg.fill('#q', 'Mazur_Frey'); pg.wait_for_selector('#q-results a.sr', timeout=15000); shot(pg, '17-static-search')
    go('about.html', '18-about')
    go('thm.html#No.Such.Theorem', '19-notfound', '#thm-main h1')
    # degradation: with katex.min.js blocked the English mathematics must stay visible as TeX source (never blank, no page error)
    ctx2 = b.new_context(viewport={'width': 1280, 'height': 900}); pg2 = ctx2.new_page(); blocked = []
    pg2.on('pageerror', lambda e: errors.append(('pageerror(no-katex)', pg2.url, str(e))))
    pg2.on('console', lambda m: errors.append(('console.' + m.type + '(no-katex)', pg2.url, m.text)) if m.type == 'error' and 'katex.min.js' not in (m.text + str((m.location or {}).get('url', ''))) else None)
    pg2.route('**/katex.min.js', lambda route: (blocked.append(route.request.url), route.abort()))
    pg2.goto('file://' + os.path.join(out, 'thm.html') + '#FreyPackage.no_frey_package'); pg2.wait_for_selector('#stmt-box pre', timeout=15000); time.sleep(0.3)
    c = pg2.evaluate(MATH_JS); srcs = pg2.evaluate("() => Array.from(document.querySelectorAll('span.tex.src')).slice(0, 3).map(e => e.textContent)")
    mathstats['20-no-katex'] = {'fragments': c[0], 'typeset': c[1], 'left_as_source': c[2], 'blocked': blocked, 'sample_source': srcs}
    if not blocked: errors.append(('qa', pg2.url, 'degradation test did not block katex.min.js (route not applied under file://?)'))
    elif not (c[0] > 0 and c[1] == 0 and c[2] == c[0] and all(s.strip() for s in srcs)): errors.append(('qa', pg2.url, 'with KaTeX blocked the TeX source is not shown: %s' % c))
    pg2.screenshot(path=os.path.join(qa, '20-no-katex.png'), full_page=True); ctx2.close()
    b.close()
rep = {'errors': errors, 'nonfile_requests': nonfile, 'failed_requests': [(u, r, f) for u, r, f in failed], 'timings_s': timings, 'mathematics': mathstats}
json.dump(rep, open(os.path.join(qa, 'report.json'), 'w'), indent=1, default=str)
print(json.dumps(rep, indent=1, default=str))
bad = bool(errors or nonfile or failed)
print('QA', 'FAILED' if bad else 'PASSED')
sys.exit(1 if bad else 0)
