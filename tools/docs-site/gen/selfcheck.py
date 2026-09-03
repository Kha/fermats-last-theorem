#!/usr/bin/env python3
"""Self-check of the generated folder before hand-over: forbidden tokens, absolute paths/URLs, stray hashes.
Usage: python3 gen/selfcheck.py out/html [--deny-file=<tokens>]. Exit 1 on any finding in generated (non-Lean) text.
The Lean text in data/shard/*.js and def/*.html is copied verbatim from the documented commit; it is scanned for the
internal-reference tokens too, but hex-hash and URL checks apply only to text we generate."""
import os, re, sys, json, html, collections
out = sys.argv[1]
CASE_SENSITIVE = set()
# generic checks live here; site-specific deny-list entries (host names, storage and scratch paths of the build
# machine, organisation names, phrases that should not appear in the generated English) are read from a local file
# passed with --deny-file, one per line: a plain token (case-insensitive substring), 'cs:TOKEN' (case-sensitive whole
# word), 'phrase:WORDS' (looked for in generated pages and shard text only, reported as a tell), 'info:WORD' (counted,
# not failed). That file is kept out of the exported generator.
FORBIDDEN = ['file:///', 'localhost']
TELLS = []; INFO_WORDS = []
for arg in sys.argv[2:]:
    if arg.startswith('--deny-file='):
        for line in open(arg.split('=', 1)[1], encoding='utf-8'):
            tok = line.strip()
            if not tok or tok.startswith('#'): continue
            if tok.startswith('cs:'): CASE_SENSITIVE.add(tok[3:]); FORBIDDEN.append(tok[3:])
            elif tok.startswith('phrase:'): TELLS.append(tok[7:])
            elif tok.startswith('info:'): INFO_WORDS.append(tok[5:])
            else: FORBIDDEN.append(tok)
HEX = re.compile(r'\b[0-9a-f]{7,40}\b')
URL = re.compile(r'https?://[^\s"\'<>)]+')
ALLOWED_HEX = set()   # hex-like tokens not to list for review (none by default)
hits = collections.defaultdict(list); urls = collections.Counter(); hexes = collections.Counter()
for root, dirs, files in os.walk(out):
    for fn in files:
        p = os.path.join(root, fn); rel = os.path.relpath(p, out)
        if not fn.endswith(('.html', '.js', '.css', '.txt', '.md', '.svg', '.json')): continue
        try: txt = open(p, encoding='utf-8', errors='replace').read()
        except Exception: continue
        low = txt.lower()
        verbatim_lean = rel.startswith('data/shard/') or (rel.startswith('def/') and rel != 'def/index.html')
        vendor = rel.startswith('assets/vendor/')
        for tok in FORBIDDEN:
            if vendor: continue   # third-party minified code and licence texts are reviewed by name, not scanned
            if tok in CASE_SENSITIVE:
                ms = list(re.finditer(r'(?<![A-Za-z0-9_])' + re.escape(tok) + r'(?![a-z])', txt))
                if ms: hits[tok].append((rel, len(ms), txt[max(0, ms[0].start()-60):ms[0].start()+60].replace('\n', ' ')))
                continue
            t = tok.lower()
            if t in low:
                k = low.count(t); i = low.find(t)
                hits[tok].append((rel, k, txt[max(0, i-60):i+60].replace('\n', ' ')))
        if not verbatim_lean and not vendor:
            for u in URL.findall(txt): urls[u.rstrip('.,;')] += 1
            if True:
                for hx in HEX.findall(txt):
                    if hx not in ALLOWED_HEX and not hx.isdigit() and re.search(r'[a-f]', hx) and re.search(r'[0-9]', hx): hexes[(rel, hx)] += 1
# the generated English layer (shard en.* strings; the English block of definition pages) may contain only the markup the generator
# itself produces: no raw tag from a content row, no event-handler attribute, no scheme/off-site href, no image/script/frame
ALLOWED_TAGS = {'p', 'em', 'strong', 'b', 'i', 'code', 'pre', 'a', 'ul', 'ol', 'li', 'blockquote', 'br', 'hr', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6',
                'span', 'sub', 'sup', 'table', 'thead', 'tbody', 'tr', 'th', 'td', 'section', 'div'}
TAG = re.compile(r'<(/?)([a-zA-Z][a-zA-Z0-9-]*)\b([^>]*)>')
markup = []; prerendered = 0
def strip_prerendered_katex(s):
    """remove the generator's own pre-rendered KaTeX blocks (<span class="katex">… balanced …</span>), which legitimately carry style attributes"""
    global prerendered
    out = []; i = 0
    while True:
        k = s.find('<span class="katex">', i)
        if k < 0: out.append(s[i:]); return ''.join(out)
        out.append(s[i:k]); depth = 0; j = k
        for m in re.finditer(r'<span\b[^>]*>|</span>', s[k:]):
            depth += -1 if m.group(0) == '</span>' else 1
            if depth == 0: j = k + m.end(); break
        else: j = len(s)
        prerendered += 1; i = j
rawtex = []
def check_generated(where, s, has_prerendered_title=False):
    """scan one generated-English HTML string: tag allow-list, attributes, and feed the URL / hex census.
    Only the definition-page title is pre-rendered KaTeX; a katex block anywhere else in generated English is itself a finding.
    Prose outside mathematics/code must not carry TeX control sequences or escaped newlines (\\S, \\times, \\n …): they would print verbatim."""
    if has_prerendered_title: s = strip_prerendered_katex(s)
    if '<span class="katex' in s: markup.append((where, 'pre-rendered KaTeX markup where only TeX source is expected'))
    prose = re.sub(r'<(pre|code)\b.*?</\1>', ' ', s, flags=re.S)
    prose = re.sub(r'<span class="tex(?: d)?">.*?</span>', ' ', prose, flags=re.S)
    prose = html.unescape(re.sub(r'<[^>]+>', ' ', prose))
    m_bs = re.search(r'\\[A-Za-z]+', prose)
    if m_bs: rawtex.append((where, prose[max(0, m_bs.start() - 40):m_bs.end() + 20].replace('\n', ' ')))
    for close, name, attrs in TAG.findall(s):
        nm = name.lower(); attrs_u = html.unescape(attrs)
        if nm not in ALLOWED_TAGS: markup.append((where, '<%s%s>' % (close, name))); continue
        if re.search(r'\bon[a-z]+\s*=', attrs_u, re.I) or re.search(r'javascript\s*:|vbscript\s*:|data\s*:', attrs_u, re.I) or re.search(r'\b(?:src|srcset|style|formaction|action|background|poster)\s*=', attrs_u, re.I): markup.append((where, '<%s %s>' % (name, attrs.strip()[:80])))
        for q1, q2, q3 in re.findall(r'href\s*=\s*(?:"([^"]*)"|\'([^\']*)\'|([^\s>]+))', attrs_u, re.I):
            hv = (q1 or q2 or q3).strip()
            if re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:|^//', hv) or not q1: markup.append((where, 'href=' + hv[:80]))   # scheme//off-site, or not the generator's double-quoted form
    for u in URL.findall(s): urls[u.rstrip('.,;}$') + '  [in generated English: ' + where.split(':')[0] + ']'] += 1
    for hx in HEX.findall(re.sub(r'<[^>]+>', ' ', s)):
        if hx not in ALLOWED_HEX and not hx.isdigit() and re.search(r'[a-f]', hx) and re.search(r'[0-9]', hx): hexes[(where, hx)] += 1
# raw TeX must not reach visible text: titles.js and page text outside <pre>/<code>/<script>/<style>
dollar = []; texspans = 0; texerr = 0
tj = os.path.join(out, 'data', 'titles.js')
if os.path.exists(tj) and '$' in open(tj, encoding='utf-8').read(): dollar.append('data/titles.js')
for root, dirs, files in os.walk(out):
    for fn in files:
        if not fn.endswith('.html'): continue
        p = os.path.join(root, fn); rel = os.path.relpath(p, out)
        t = open(p, encoding='utf-8', errors='replace').read()
        if rel.startswith('def/') and rel != 'def/index.html':
            m_en = re.search(r'(<h2 class="en-title">|<section class="en">)(.*?)<ul class="kv">', t, re.S)
            if m_en: check_generated(rel, m_en.group(0), has_prerendered_title=True)
        t = re.sub(r'<(pre|code|script|style)\b.*?</\1>', ' ', t, flags=re.S)
        t = re.sub(r'<span class="katex.*?</span>(?=\s|<|$)', ' ', t, flags=re.S)
        texspans += len(re.findall(r'<span class="tex(?: d)?">', t))
        t = re.sub(r'<span class="tex(?: d)?">.*?</span>', ' ', t, flags=re.S)   # TeX source for the browser's KaTeX (no $ delimiters inside)
        t = re.sub(r'<[^>]+>', ' ', t)
        if re.search(r'\$\$|\$[^\s$]', t) or 'KQXMATH' in t: dollar.append(rel)
# TELLS / INFO_WORDS come from the deny file ('phrase:' / 'info:' lines): phrases that must not appear in generated pages, and words only counted
tell_hits = collections.defaultdict(list)
for root, dirs, files in os.walk(out):
    for fn in files:
        if not (fn.endswith('.html') or (fn.endswith('.js') and 'shard' in root)): continue
        p = os.path.join(root, fn); rel = os.path.relpath(p, out)
        if rel.startswith(('assets/', 'docs/', 'route/')): continue   # repository prose is rendered as written
        t = open(p, encoding='utf-8', errors='replace').read()
        if fn.endswith('.html'):
            t = re.sub(r'<(pre|script|style)\b.*?</\1>', ' ', t, flags=re.S)
        for w in TELLS:
            if w.lower() in t.lower(): tell_hits[w].append(rel)
        if re.search(r'&amp;(#39|lt|gt|quot|amp);', t) and not rel.startswith(('docs/',)): tell_hits['double-escaped entity'].append(rel)
print('== deny-file phrases / double escaping ==')
info_counts = collections.Counter()
for root, dirs, files in os.walk(os.path.join(out, 'data', 'shard')):
    for fn in files:
        t = open(os.path.join(root, fn), encoding='utf-8', errors='replace').read().lower()
        for w in INFO_WORDS: info_counts[w] += t.count(w)
print('  (info) word counts in shard text, not failures:', dict(info_counts))
for w, l in tell_hits.items():
    print(f'  {w}: {len(l)} files, e.g. {l[:3]}'); hits['tell:' + w] = [(x, 1, '') for x in l]
# English inside the data shards (statement/proof/context html) must not carry raw TeX or control characters either
for root, dirs, files in os.walk(os.path.join(out, 'data', 'shard')):
    for fn in sorted(files):
        t = open(os.path.join(root, fn), encoding='utf-8', errors='replace').read()
        try: obj = json.loads(t[t.index(',') + 1:t.rindex(')')])
        except Exception as e: dollar.append('data/shard/%s (unparseable: %s)' % (fn, e)); continue
        for name, rec in obj.items():
            en = rec.get('en') or {}
            for k, v in en.items():
                vals = v if isinstance(v, list) else [v]
                for s in vals:
                    if not isinstance(s, str): continue
                    check_generated('data/shard/%s:%s.%s' % (fn, name, k), s)
                    texerr += s.count('<code class="tex">')
                    plain = re.sub(r'<(code|pre)\b.*?</\1>', ' ', s, flags=re.S)
                    plain = re.sub(r'<span class="katex.*?</span>(?=\s|<|$)', ' ', plain, flags=re.S)
                    texspans += len(re.findall(r'<span class="tex(?: d)?">', plain))
                    plain = re.sub(r'<span class="tex(?: d)?">.*?</span>', ' ', plain, flags=re.S)
                    plain = re.sub(r'<[^>]+>', ' ', plain)
                    if re.search(r'\$\$|\$[^\s$]', plain) or 'KQXMATH' in plain or re.search(r'[\x00-\x08\x0b-\x1f]', s): dollar.append('shard %s: %s.%s' % (fn, name, k))
print(f'== raw $ in visible text ==  (info: {texspans:,} TeX fragments shipped as source for in-browser typesetting; {texerr} shipped as visible source because KaTeX rejected them at build time)')
for rel in dollar[:20]: print('  ', rel)
if dollar: hits['raw-TeX-dollar'] = [(rel, 1, '') for rel in dollar]
print(f'== markup in the generated English layer outside the allow-list (tags, on*= / src / style attributes, scheme hrefs) ==  {len(markup)} findings ({prerendered} pre-rendered KaTeX titles skipped)')
for where, what in markup[:20]: print('  ', where, what)
if markup: hits['generated-markup'] = [(w, 1, what) for w, what in markup]
print(f'== TeX control sequences / escaped newlines in prose outside mathematics ==  {len(rawtex)} findings')
for where, what in rawtex[:20]: print('  ', where, '…%s…' % what)
if rawtex: hits['raw-TeX-in-prose'] = [(w, 1, what) for w, what in rawtex]
print('== forbidden tokens ==')
for tok, l in hits.items():
    print(f'{tok}: {sum(k for _, k, _ in l)} occurrences in {len(l)} files; e.g. {l[0][0]}: …{l[0][2]}…')
print('== external URLs in generated text (never fetched; listed for review) ==')
for u, c in urls.most_common(40): print(f'{c:5d}  {u}')
print('== hex-like tokens outside docs/ (possible commit hashes / ids) ==')
agg = collections.Counter()
for (rel, hx), c in hexes.items(): agg[hx] += c
for hx, c in agg.most_common(30): print(f'{c:5d}  {hx}  e.g. {next(r for (r, h) in hexes if h == hx)}')
bad = bool(hits)
print('SELFCHECK', 'FINDINGS' if bad else 'CLEAN (no forbidden tokens)')
sys.exit(1 if bad else 0)
