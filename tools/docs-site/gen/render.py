#!/usr/bin/env python3
"""Stage 3: render the static site from <build>/ records.

python3 gen/render.py --build build --repo <repo> --docs <docs> --content <content-dir> --out out/html
Everything written is relative-linked and works from file:// (classic scripts only; no fetch).
"""
import os, re, sys, json, time, html, shutil, argparse, hashlib, datetime, collections
from jinja2 import Environment, DictLoader
import markdown
from pygments import highlight
from pygments.lexers import get_lexer_by_name
from pygments.formatters import HtmlFormatter

GEN = os.path.dirname(os.path.abspath(__file__))
LEAN = get_lexer_by_name('lean4')
FMT = HtmlFormatter(nowrap=True)
NSHARDS = 256
MATHLIB_DOCS_URL = 'https://leanprover-community.github.io/mathlib4_docs/'
SITE_TITLE = "Fermat's Last Theorem in Lean 4"

def fnv(s):
    h = 2166136261
    for ch in s:
        h ^= ord(ch); h = (h * 16777619) & 0xFFFFFFFF
    return h

def slim(h):
    h = re.sub(r'<span class="w">(\s*)</span>', r'\1', h)
    h = re.sub(r'<span class="(?:n|p|o|bp|x)">([^<]*)</span>', r'\1', h)
    return h

NAME_SEQ = re.compile(r'<span class="n">([^<]*)</span>((?:<span class="bp">\.</span><span class="n">[^<]*</span>)*)')

def hl_lean(code, resolver=None):
    h = highlight(code, LEAN, FMT)
    if resolver:
        def rep(m):
            full = html.unescape(m.group(1) + re.sub(r'<[^>]+>', '', m.group(2) or ''))
            r = resolver(full)
            if r: return '<a class="id" href="%s" title="%s">%s</a>' % (html.escape(r[0], quote=True), html.escape(r[1], quote=True), html.escape(full))
            return m.group(0)
        h = NAME_SEQ.sub(rep, h)
    return slim(h)

def load_jsonl(p):
    with open(p, encoding='utf-8') as fh:
        for line in fh:
            yield json.loads(line)

TEX_MACROS = {
    'mathbb{N}': 'ℕ', 'mathbb{Z}': 'ℤ', 'mathbb{Q}': 'ℚ', 'mathbb{R}': 'ℝ', 'mathbb{C}': 'ℂ', 'mathbb{F}': '𝔽', 'mathbb N': 'ℕ', 'mathbb Z': 'ℤ', 'mathbb Q': 'ℚ', 'mathbb C': 'ℂ',
    'mathbf{Q}': 'ℚ', 'mathbf{Z}': 'ℤ', 'mathcal{O}': '𝒪', 'mathfrak{m}': '𝔪', 'mathfrak{p}': '𝔭', 'mathfrak m': '𝔪', 'mathfrak p': '𝔭',
    'ge': '≥', 'geq': '≥', 'le': '≤', 'leq': '≤', 'ne': '≠', 'neq': '≠', 'to': '→', 'mid': '∣', 'nmid': '∤', 'cdot': '·', 'times': '×', 'pm': '±', 'infty': '∞',
    'equiv': '≡', 'cong': '≅', 'simeq': '≃', 'subset': '⊂', 'subseteq': '⊆', 'in': '∈', 'cap': '∩', 'cup': '∪', 'otimes': '⊗', 'oplus': '⊕', 'sim': '∼', 'approx': '≈',
    'Gamma': 'Γ', 'Delta': 'Δ', 'Lambda': 'Λ', 'Sigma': 'Σ', 'Omega': 'Ω', 'Phi': 'Φ', 'Psi': 'Ψ',
    'alpha': 'α', 'beta': 'β', 'gamma': 'γ', 'delta': 'δ', 'epsilon': 'ε', 'varepsilon': 'ε', 'zeta': 'ζ', 'eta': 'η', 'theta': 'θ', 'iota': 'ι', 'kappa': 'κ', 'lambda': 'λ',
    'mu': 'μ', 'nu': 'ν', 'xi': 'ξ', 'pi': 'π', 'rho': 'ρ', 'sigma': 'σ', 'tau': 'τ', 'phi': 'φ', 'varphi': 'φ', 'chi': 'χ', 'psi': 'ψ', 'omega': 'ω', 'ell': 'ℓ',
    'bar': '̄', 'overline': '̄', 'tilde': '̃', 'widetilde': '̃', 'hat': '̂', 'parallel': ' ∥ ', 'nparallel': ' ∦ ', 'lfloor': '⌊', 'rfloor': '⌋', 'lceil': '⌈', 'rceil': '⌉', 'frac': '', 'sqrt': '√', 'langle': '⟨', 'rangle': '⟩', 'lvert': '|', 'rvert': '|', 'Vert': '‖', 'vert': '|',
    'operatorname': '', 'mathrm': '', 'text': '', 'mathit': '', 'rm': '', 'left': '', 'right': '', 'big': '', 'Big': '', 'quad': ' ', 'qquad': '  ', ',': ' ', ';': ' ', '!': '', ' ': ' ',
    'colon': ':', 'ldots': '…', 'dots': '…', 'cdots': '⋯', 'prime': '′', 'circ': '∘', 'ast': '∗', 'star': '⋆', 'wedge': '∧', 'vee': '∨', 'neg': '¬', 'forall': '∀', 'exists': '∃',
    'longrightarrow': '⟶', 'rightarrow': '→', 'hookrightarrow': '↪', 'twoheadrightarrow': '↠', 'mapsto': '↦', 'iff': '⟺', 'implies': '⟹', 'setminus': '∖', 'emptyset': '∅', 'varnothing': '∅',
    'GL': 'GL', 'SL': 'SL', 'Gal': 'Gal', 'det': 'det', 'ker': 'ker', 'bmod': 'mod', 'pmod': 'mod', 'mod': 'mod', 'gcd': 'gcd', 'deg': 'deg', 'dim': 'dim', '#': '#', '{': '{', '}': '}', '_': '_', '%': '%', '&': '&',
}
SUBS = str.maketrans('0123456789+-=()aeijnoprstuvx', '₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑᵢⱼₙₒₚᵣₛₜᵤᵥₓ')
SUPS = str.maketrans('0123456789+-=()nipabcdx', '⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿⁱᵖᵃᵇᶜᵈˣ')

def tex_to_unicode(s):
    """Plain-text rendering of a short title with $…$ mathematics, for SVG labels, search results and headings in script-built lists."""
    def conv(tex):
        t = tex.replace('\\{', '⦃LB⦄').replace('\\}', '⦃RB⦄').replace('\\|', '‖')
        t = re.sub(r'\\(overline|bar|widetilde|tilde|hat)\s*\{\\(mathbb|mathcal|mathbf|mathrm)\s*\{?([A-Za-z])\}?\}', lambda m: conv('\\' + m.group(2) + '{' + m.group(3) + '}') + TEX_MACROS['widetilde' if m.group(1) == 'widetilde' else m.group(1)], t)
        t = re.sub(r'\\(mathbb|mathcal|mathfrak|mathbf|mathrm)\s+([A-Za-z])\b', lambda m: '\\' + m.group(1) + '{' + m.group(2) + '}', t)
        t = re.sub(r'\\(bar|overline|tilde|hat)\s*\{([^{}]*)\}', lambda m: conv(m.group(2)) + TEX_MACROS[m.group(1)], t)
        t = re.sub(r'\\(bar|overline|tilde|hat)\s*\\([A-Za-z]+)', lambda m: TEX_MACROS.get(m.group(2), m.group(2)) + TEX_MACROS[m.group(1)], t)
        t = re.sub(r'\\sqrt\s*\{([^{}]*)\}', lambda m: '√' + conv(m.group(1)), t)
        t = re.sub(r'\\[dt]?frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}', lambda m: conv(m.group(1)) + '/' + conv(m.group(2)), t)
        t = re.sub(r'\\pmod\s*\{([^{}]*)\}', lambda m: '(mod ' + conv(m.group(1)) + ')', t)
        t = re.sub(r'\\pmod\s+([A-Za-z0-9]+)', lambda m: '(mod ' + m.group(1) + ')', t)
        t = re.sub(r'\\widetilde\s*\{([^{}]*)\}', lambda m: conv(m.group(1)) + '̃', t)
        t = re.sub(r'\\widetilde\s*([A-Za-z])', lambda m: m.group(1) + '̃', t)
        t = re.sub(r'\\(?:mathbb|mathbf|mathcal|mathfrak|mathrm|mathsf)\s*\{([A-Za-z0-9])\}', lambda m: TEX_MACROS.get('mathbb{%s}' % m.group(1), m.group(1)) if 'mathbb' in m.group(0) else TEX_MACROS.get(m.group(0)[1:].replace(' ', ''), m.group(1)), t)
        t = re.sub(r'\\(?:operatorname|mathrm|text|mathit|mathbf)\s*\{([^{}]*)\}', lambda m: m.group(1), t)
        def macro(m):
            name = m.group(1)
            return TEX_MACROS.get(name, name)
        for _ in range(2):
            t = re.sub(r'\\([A-Za-z]+|.)(\{[A-Za-z]\})?', lambda m: TEX_MACROS.get(m.group(1) + (m.group(2) or ''), TEX_MACROS.get(m.group(1), m.group(1)) + ((m.group(2) or '')[1:-1])), t)
        def sub(m):
            body = m.group(1) if m.group(1) is not None else m.group(2)
            tr = body.translate(SUBS)
            return tr if all(ch != b or ch in '₀' for ch, b in zip(tr, body)) and not any(c in body for c in '{}\\') and tr != body else ('_' + body if m.group(1) is None or len(body) == 1 else '_⦃LB⦄' + body + '⦃RB⦄')
        def sup(m):
            body = m.group(1) if m.group(1) is not None else m.group(2)
            tr = body.translate(SUPS)
            return tr if tr != body and not any(c in body for c in '{}\\') and all(a != b for a, b in zip(tr, body)) else ('^' + body if m.group(1) is None or len(body) == 1 else '^⦃LB⦄' + body + '⦃RB⦄')
        t = re.sub(r'_\{([^{}]+)\}|_(.)', sub, t)
        t = re.sub(r'\^\{([^{}]+)\}|\^(.)', sup, t)
        t = t.replace('{', '').replace('}', '').replace('⦃LB⦄', '{').replace('⦃RB⦄', '}')
        t = re.sub(r'\s+', ' ', t)
        return t.strip()
    out = MATH_RE.sub(lambda m: conv(m.group(0).strip('$')), s)
    return out.replace('  ', ' ')

def trim_tail(tail):
    """Keep the solution block from its ':=' on: the signature repeats the statement already shown."""
    if not tail: return tail
    k = tail.find(':=')
    if k < 0: return tail
    return 'theorem solution … ' + tail[k:]

def fmt_int(n):
    return f'{n:,}'

STAGE_SHORT = {0: 'The statement', 1: 'Reduction to prime exponents p ≥ 5', 2: 'The Frey package', 3: 'Irreducibility (Mazur; exponents 5, 7, 11, 13 settled directly)',
               4: 'Modularity (Wiles, Taylor–Wiles)', 5: 'Level lowering (Ribet)', 6: 'No weight-2 cusp forms of level 2',
               7: 'Exact strength of the named theorems'}

# ----------------------------------------------------------------------------- markdown
MATH_RE = re.compile(r'(\$\$.+?\$\$|\$[^$\n]+?\$)', re.S)
CODE_SPAN_RE = re.compile(chr(96) + r'[^' + chr(96) + r'\n]*' + chr(96))

KATEX = {}     # (tex, display) -> KaTeX HTML, for mathematics on the static pages (pre-rendered at build time)
TEX_OK = set()   # (tex, display) fragments of the English layer that parse under KaTeX; shipped as TeX source and typeset in the browser
TEX_ERR = {}   # (tex, display) -> KaTeX error message; such fragments are shipped as visible TeX source in <code class="tex">

def math_key(s):
    return (s[2:-2], True) if s.startswith('$$') else (s[1:-1], False)

def math_spans(seg):
    """(start, end) of each $…$ / $$…$$ in a one-line segment. The closing delimiter is looked for at brace depth 0, so
    '$n (\\text{if $x$}) m$' is one fragment (KaTeX accepts $ inside \\text); \\$ is not a delimiter; if the braces never
    balance, the first following $ closes (KaTeX then reports the fragment, rather than raw TeX reaching the page)."""
    spans = []; i = 0; n = len(seg)
    while i < n:
        if seg[i] != '$' or (i > 0 and seg[i - 1] == '\\'): i += 1; continue
        dd = seg.startswith('$$', i); w = 2 if dd else 1
        j = i + w; depth = 0; close = -1; first = -1
        while j < n:
            ch = seg[j]
            if ch == '\\': j += 2; continue
            if ch == '{': depth += 1
            elif ch == '}': depth -= 1
            elif ch == '$' and (not dd or seg.startswith('$$', j)):
                if first < 0: first = j
                if depth == 0: close = j; break
            j += 1
        if close < 0: close = first
        if close < 0 or close == i + w: i += w; continue   # no closing delimiter, or empty: not mathematics
        spans.append((i, close + w)); i = close + w
    return spans

def sub_math(fn, seg):
    out = []; p = 0
    for s, e in math_spans(seg): out.append(seg[p:s]); out.append(fn(seg[s:e])); p = e
    out.append(seg[p:]); return ''.join(out)

def inline_scan(line):
    """[(kind, text)] for one line, kind in 'text' | 'code' | 'math'. Left to right, whichever construct opens first wins —
    a backtick inside $…$ (TeX's grave accent) is not a code delimiter and a $ inside a code span is not mathematics; backtick
    runs pair by length as in Markdown; backslash-escaped \\$ and \\\x60 open nothing."""
    out = []; i = 0; n = len(line); t0 = 0
    def text_upto(k):
        if k > t0: out.append(('text', line[t0:k]))
    while i < n:
        ch = line[i]
        if ch == '\\': i += 2; continue
        if ch == chr(96):
            run = re.match(r'\x60+', line[i:]).group(0); j = i + len(run)
            m = re.search(r'(?<!\x60)' + run + r'(?!\x60)', line[j:])   # the closing run of the same length
            if m:
                k = j + m.start(); text_upto(i); out.append(('code', line[i:k + len(run)])); i = k + len(run); t0 = i; continue
            i = j; continue
        if ch == '$':
            sp = math_spans(line[i:]) if line.find('$', i + 1) >= 0 else []
            if sp and sp[0][0] == 0:
                e = i + sp[0][1]; text_upto(i); out.append(('math', line[i:e])); i = e; t0 = i; continue
            i += 2 if line.startswith('$$', i) else 1; continue
        i += 1
    text_upto(n)
    return out

CODE_SPAN_ML = re.compile(r'(?<!\x60)(\x60+)(?!\x60)(.+?)(?<!\x60)\1(?!\x60)', re.S)   # Python-Markdown's pairing of backtick runs, across line breaks

def join_display_math(text):
    """Outside fenced code: put each code span and each $$…$$ block on one line. Python-Markdown pairs backticks across line
    breaks inside a paragraph; the per-line processing below must see the same code spans, or mathematics after a code span
    that straddles a line break would be mistaken for code and reach the page as raw $…$."""
    out = []; chunk = []; in_fence = False
    def one_line_code(para):
        return CODE_SPAN_ML.sub(lambda m: m.group(0).replace('\n', ' '), para)
    def flush():
        if chunk:
            paras = re.split(r'(\n\s*\n)', '\n'.join(chunk))   # code spans do not cross a blank line
            joined = ''.join(one_line_code(p) if i % 2 == 0 else p for i, p in enumerate(paras))
            out.append(re.sub(r'\$\$(.+?)\$\$', lambda m: '$$' + ' '.join(m.group(1).split()) + '$$', joined, flags=re.S)); chunk.clear()
    for line in text.split('\n'):
        if line.startswith('~~~') or line.startswith(chr(96) * 3):
            flush(); in_fence = not in_fence; out.append(line); continue
        if in_fence: out.append(line)
        else: chunk.append(line)
    flush()
    return '\n'.join(out)

def clean_md_text(text):
    """normalisation shared by math_fragments and md_to_html, so the fragments checked are exactly the fragments rendered"""
    text = re.sub(r'[\x00-\x08\x0b-\x1f]', '', (text or '').replace('\r\n', '\n').replace('\r', ''))
    return join_display_math(text)

def math_fragments(text):
    """The $…$ / $$…$$ fragments of a Markdown text, skipping code spans and fenced blocks exactly as md_to_html does."""
    in_fence = False
    text = clean_md_text(text)
    for line in text.split('\n'):
        if line.startswith('~~~') or line.startswith(chr(96) * 3):
            in_fence = not in_fence; continue
        if in_fence: continue
        for kind, s in inline_scan(line):
            if kind == 'math': yield s

def gather_math(text, acc):
    for s in math_fragments(text): acc.add(math_key(s))

def run_katex(items, want_html, chunk=20000):
    """[(tex, display)] -> [(html or '', error or None)] via bun + the vendored katex.min.js (strict: throwOnError)."""
    import subprocess
    res = []
    for k in range(0, len(items), chunk):
        part = items[k:k + chunk]
        r = subprocess.run(['bun', os.path.join(GEN, 'katex_render.js'), os.path.join(GEN, 'vendor', 'katex', 'katex.min.js')],
                           input=json.dumps([[t, d, want_html] for t, d in part]).encode(), capture_output=True)
        if r.returncode != 0: raise RuntimeError('katex failed: ' + r.stderr.decode()[:500])
        outl = json.loads(r.stdout.decode())
        if len(outl) != len(part): raise RuntimeError('katex returned %d results for %d fragments' % (len(outl), len(part)))
        res.extend((h, e) for h, e in outl)
    return res

def prerender_math(static_items, client_items):
    """Static-page mathematics is rendered to HTML once at build time; English-layer mathematics (theorem records in the data
    shards, definition-module pages) is only validated here — same KaTeX, same strict parse — and typeset in the browser by the
    bundled katex.min.js, because pre-rendered KaTeX HTML is ≈13× the size of its source and there are tens of thousands of records."""
    static_items = sorted(static_items); client_only = sorted(set(client_items) - set(static_items))
    for (t, d), (h, err) in zip(static_items, run_katex(static_items, True)):
        if err: TEX_ERR[(t, d)] = err
        else: KATEX[(t, d)] = h; TEX_OK.add((t, d))
    for (t, d), (h, err) in zip(client_only, run_katex(client_only, False)):
        if err: TEX_ERR[(t, d)] = err
        else: TEX_OK.add((t, d))
    print(f'katex: {len(static_items) + len(client_only)} fragments checked ({len(static_items)} pre-rendered for the static pages, '
          f'{len(set(client_items))} of the English layer validated for in-browser typesetting), {len(TEX_ERR)} failed (left as TeX source)', file=sys.stderr)

MATH_UNSEEN = collections.Counter()

def math_html(s, client=False):
    """HTML for one $…$ fragment: pre-rendered KaTeX (static pages), or a <span class="tex"> carrying the TeX source for the
    browser to typeset (client=True), or — when KaTeX cannot parse it — the source, visibly, in <code class="tex">."""
    key = math_key(s)
    if key in TEX_ERR: return '<code class="tex">' + html.escape(s) + '</code>'
    if client:
        if key not in TEX_OK: MATH_UNSEEN[key] += 1
        return '<span class="tex%s">%s</span>' % (' d' if key[1] else '', html.escape(key[0]))
    h = KATEX.get(key)
    if h: return h
    MATH_UNSEEN[key] += 1
    return '<code class="tex">' + html.escape(s) + '</code>'

LINK_WARNINGS = []

# markup the generator itself produces from Markdown of the generated English layer; anything else in untrusted output is shown as text
GEN_TAGS = {'p', 'em', 'strong', 'code', 'pre', 'a', 'ul', 'ol', 'li', 'blockquote', 'br', 'hr', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6',
            'table', 'thead', 'tbody', 'tr', 'th', 'td', 'sup', 'sub', 'span'}
GEN_ATTRS = {'class', 'href', 'id', 'title', 'colspan', 'rowspan', 'style'}
TAG_RE = re.compile(r'<(/?)([a-zA-Z][a-zA-Z0-9-]*)\b([^>]*)>')
ATTR_RE = re.compile(r'\s+([a-zA-Z-]+)="([^"]*)"')
def sanitize_generated(h):
    """Output-side guard for untrusted Markdown: keep only the tags/attributes this generator emits (relative hrefs, classes, heading ids,
    the table extension's text-align), and turn any other tag into visible text. Independent of how the input was tokenised."""
    def fix(m):
        close, name, attrs = m.group(1), m.group(2), m.group(3)
        ok = name.lower() in GEN_TAGS and re.fullmatch(r'(?:\s+[a-zA-Z-]+="[^"]*")*\s*/?', attrs) is not None
        if ok:
            for n, v in ATTR_RE.findall(attrs):
                n = n.lower(); v = html.unescape(v).strip()
                if n not in GEN_ATTRS: ok = False
                elif n == 'href' and re.match(r'^([a-zA-Z][a-zA-Z0-9+.-]*:|//)', v): ok = False
                elif n == 'style' and not re.fullmatch(r'text-align: ?(left|right|center);?', v): ok = False
        return m.group(0) if ok else html.escape(m.group(0))
    return TAG_RE.sub(fix, h)

REPORT = {}        # numbers for the build log / QA (written next to the output folder as render-report.json; not shipped)
REPORT_PATH = None

def md_to_html(text, linker, page_rel_root, doc_link_map, repo_root=None, client_math=False, untrusted=False):
    """Render Markdown faithfully; protect TeX; auto-link code spans that name theorems/definitions/files.
    client_math=True leaves the mathematics as TeX source in <span class="tex"> for the browser (see prerender_math).
    untrusted=True is for the generated English layer: raw HTML is shown as text (never becomes markup), Markdown images are
    dropped to their alt text and external links to their link text, so nothing in such a field can add an element, an
    attribute or an off-site reference to a page; the repository's own documents keep full Markdown."""
    text = clean_md_text(text)
    text = text.replace('KQXMATH', 'KQX\u200bMATH')   # the placeholder token itself can then never occur in the input
    stash = []
    def rep(frag):
        stash.append(frag); return 'KQXMATH%dKQX' % (len(stash) - 1)
    # mathematics -> placeholders (restored after Markdown); code spans and fenced blocks untouched; same tokeniser as math_fragments
    in_fence = False; lines = []
    for line in text.split('\n'):
        if line.startswith('~~~') or line.startswith(chr(96) * 3):
            in_fence = not in_fence; lines.append(line); continue
        if in_fence: lines.append(line); continue
        parts = []
        for kind, s in inline_scan(line):
            if kind == 'math': parts.append(rep(s))
            elif kind == 'code': parts.append(s)
            else: parts.append(s.replace('<', '&lt;') if untrusted else s)   # raw '<' outside mathematics and code becomes text
        lines.append(''.join(parts))
    text = '\n'.join(lines)
    h = markdown.markdown(text, extensions=['tables', 'fenced_code', 'sane_lists', 'toc'], output_format='html5')
    # fenced lean blocks -> highlighted
    def code_block(m):
        lang = m.group(1) or ''; body = html.unescape(m.group(2))
        if lang.startswith('lean') or (not lang and ('theorem ' in body or 'import ' in body or ' : ' in body)):
            return '<pre class="lean">' + hl_lean(body) + '</pre>'
        return '<pre><code>' + m.group(2) + '</code></pre>'
    h = re.sub(r'<pre><code(?: class="language-([^"]*)")?>(.*?)</code></pre>', code_block, h, flags=re.S)
    if untrusted:   # Markdown image syntax would fetch; keep the alt text only
        h = re.sub(r'<img\b[^>]*\balt="([^"]*)"[^>]*>', lambda m: m.group(1), h); h = re.sub(r'<img\b[^>]*>', '', h)
    # links between the markdown documents
    def any_link(m):
        target = html.unescape(m.group(1)); text_in = m.group(2)
        if untrusted and re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:', target): return text_in   # no off-site or scheme links from generated text
        if re.match(r'^(https?:|mailto:|#)', target): return m.group(0)
        base = target.split('#')[0]; frag = target[len(base):]
        key = re.sub(r'^(\./|\.\./|docs/)+', '', base)
        if key in doc_link_map:
            if doc_link_map[key] is None:
                return text_in + ' <span class="muted small">(not included here)</span>'
            return '<a href="%s%s%s">%s</a>' % (page_rel_root, doc_link_map[key], frag, text_in)
        # a file of the repository: link it if the documented tree has it, else neutralise
        rel = os.path.normpath(base.lstrip('./').replace('../', '')) if base else ''
        if repo_root and rel and os.path.exists(os.path.join(repo_root, rel)):
            return '<a href="%s../%s%s">%s</a>' % (page_rel_root, rel, frag, text_in)
        LINK_WARNINGS.append(target)
        return text_in + ' <span class="muted small">(not in this copy of the tree)</span>'
    h = re.sub(r'<a href="([^"]*)"(?: title="[^"]*")?>(.*?)</a>', any_link, h, flags=re.S)
    # auto-link inline code
    def code_inline(m):
        inner = html.unescape(m.group(1))
        link = linker(inner, page_rel_root)
        if link: return '<a href="%s"><code>%s</code></a>' % (html.escape(link, quote=True), m.group(1))
        return m.group(0)
    h = re.sub(r'<code>([^<]{2,300})</code>', code_inline, h)
    if untrusted: h = sanitize_generated(h)
    for i, s in enumerate(stash):
        h = h.replace('KQXMATH%dKQX' % i, math_html(s, client_math))
    return h

# ----------------------------------------------------------------------------- templates
T = {}
T['base'] = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{ title }} · FLT in Lean 4</title>
<link rel="stylesheet" href="{{ R }}assets/site.css"><link rel="stylesheet" href="{{ R }}assets/vendor/katex/katex-embedded.css">
<script>window.FLT_ROOT = "{{ R }}";</script>
{% block head %}{% endblock %}
</head><body>
<header class="top"><div class="inner">
<a class="brand" href="{{ R }}index.html"><b>Fermat's Last Theorem</b> in Lean 4</a>
<nav>{% for href, label, key in NAV %}<a href="{{ R }}{{ href }}"{% if key == navkey %} class="cur"{% endif %}>{{ label }}</a>{% endfor %}</nav>
<div class="search"><input id="q" type="search" placeholder="Search {{ n_thm }} theorems and {{ n_def }} definition files by name…" autocomplete="off" spellcheck="false"><div id="q-results"></div></div>
</div></header>
<main class="{{ mainclass or '' }}">
{% block main %}{{ body }}{% endblock %}
</main>
<footer>Documents {{ stamp }} ({{ toolchain }}). Statements are quoted textually from the .lean files; dependency edges are the <code>import Theorems.Thm_…</code> lines of the proof modules. <a href="{{ R }}about.html">About these pages</a>.</footer>
{% if katex_js %}<script src="{{ R }}assets/vendor/katex/katex.min.js"></script>{% endif %}<script src="{{ R }}assets/hl.js"></script><script src="{{ R }}assets/site.js"></script>
{% block tail %}{% endblock %}
</body></html>"""

T['thm'] = """{% extends 'base' %}
{% block head %}<script src="data/meta.js"></script><script src="data/ddecl.js"></script><script src="data/edges.js"></script><script src="data/titles.js"></script>
<script src="assets/vendor/graphviz.umd.js"></script>{% endblock %}
{% block main %}<div id="thm-main"><p class="muted">Loading…</p><noscript><p class="warn">This page needs JavaScript: it shows any of the {{ n_thm }} theorems selected by the #fragment of the URL. The route pages, definition pages and documents work without it.</p></noscript></div>{% endblock %}
{% block tail %}<script src="assets/explorer.js"></script>{% endblock %}"""

T['prose'] = """{% extends 'base' %}
{% block main %}<article class="prose math-scope">{{ body }}</article>{% if after %}{{ after }}{% endif %}{% endblock %}"""

NAV = [('index.html', 'Overview', 'index'), ('route/index.html', 'Route', 'route'), ('dag/index.html', 'Landmark graph', 'dag'),
       ('thm.html', 'Theorems', 'thm'), ('areas/index.html', 'Areas', 'areas'), ('def/index.html', 'Definitions', 'def'), ('docs/index.html', 'Documents', 'docs'), ('about.html', 'About', 'about')]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--build', required=True); ap.add_argument('--repo', required=True); ap.add_argument('--docs', required=True)
    ap.add_argument('--content', default=None); ap.add_argument('--out', required=True)
    ap.add_argument('--commit', default=None); ap.add_argument('--english-attribution', default='')
    ap.add_argument('--no-docs', dest='include_docs', action='store_false', help='do not render the optional prose documents (overview, structure, verification, limitations, port notes); the route chapters still come from docs/route.md')
    ap.add_argument('--no-mathlib-links', dest='mathlib_links', action='store_false', help='do not emit the (external, never auto-fetched) links from import Mathlib.X lines to the mathlib4 documentation')
    ap.add_argument('--link-report', action='store_true', help='count identifier links over all statements by rule class (adds ~20 s)')
    ap.add_argument('--tex-errors', choices=('fail', 'source'), default='fail', help="what to do when a $…$ fragment does not parse under KaTeX: 'fail' (default: list them and stop) or 'source' (ship those fragments as visible TeX source)")
    ap.add_argument('--references-origin', default='draft', help="for content rows whose references carry a parallel references_origin list: keep only the references tagged with this value ('all' keeps every reference; default 'draft')")
    ap.add_argument('--references-note', default='References are suggested automatically and have not been individually verified.', help='one muted sentence printed under every references list and once on About / in README-DOCS (empty to omit)')
    a = ap.parse_args()
    t0 = time.time()
    G = json.load(open(os.path.join(a.build, 'graph.json')))
    TH = G['theorems']; N = len(TH); cites = G['cites']; DEFS = G['defs']; cite_uses = G.get('cite_uses') or [[] for _ in range(N)]
    qidx = {t['qual']: i for i, t in enumerate(TH)}
    sidx = {t['stem']: i for i, t in enumerate(TH)}
    didx = {d['stem']: k for k, d in enumerate(DEFS)}
    defrecs = {d['stem']: d for d in load_jsonl(os.path.join(a.build, 'def.jsonl'))}
    # declaration names inside definition modules -> (def idx, line, kw)
    ddecl = {}; ddecl_list = []; extends_raw = {}
    for k, d in enumerate(DEFS):
        for dd in defrecs[d['stem']]['decls']:
            q = dd.get('qual') or dd.get('name')
            if not q: continue
            if q not in ddecl:
                ddecl[q] = (k, dd['line'], dd['kw'])
                ddecl_list.append([q, k, dd['line'], dd['kw']])
            if dd.get('extends'): extends_raw[q] = dd['extends']
    # parents of structures, resolved to project declarations where possible (else kept as written)
    EXT = {}
    for q, ps in extends_raw.items():
        ns = q.rsplit('.', 1)[0] if '.' in q else ''
        out_ps = []
        for p in ps:
            cand = None
            if p in ddecl: cand = p
            else:
                n2 = ns
                while n2 and cand is None:
                    if (n2 + '.' + p) in ddecl: cand = n2 + '.' + p
                    n2 = n2.rsplit('.', 1)[0] if '.' in n2 else ''
            out_ps.append(cand or p)
        EXT[q] = out_ps
    # identifier -> definition links, resolved textually and conservatively (a missing link is fine, a wrong one is not):
    #   exact      the token is a constant declared in a definition module (fully qualified), or a theorem name
    #   bare       an undotted token Foo with NS.Foo declared, for exactly one NS among the statement's open namespaces / own namespace prefixes
    #   qualified  a dotted token with a capitalised head, completed through exactly one such NS
    #   field      x.foo with a variable-like head: the suffix names exactly one constant, whose namespace is open/own or whose top
    #              namespace occurs as a token in the statement
    by_suffix = collections.defaultdict(set)
    for q in ddecl:
        parts = q.split('.')
        for j in range(1, len(parts)): by_suffix['.'.join(parts[j:])].add(q)
    TOK = re.compile(r"[A-Za-z_\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2100-\u214F\U0001D400-\U0001D7FF«][A-Za-z0-9_'!?\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2070-\u209F\u2100-\u214F\U0001D400-\U0001D7FF»«.]*")
    def scope_of(ctx_lines, qual, extra_ns=()):
        opened = set()
        for l in ctx_lines:
            s = l.strip()
            if s.startswith('open '):
                body = s[5:].replace('scoped ', ' ')
                body = body.split(' in ')[0]; body = re.sub(r'\([^)]*\)', ' ', body); body = body.split(' hiding')[0].split(' renaming')[0]
                opened |= set(x for x in body.split() if re.match(r'^[A-Za-z_][A-Za-z0-9_.\']*$', x))
            elif s.startswith('p2m_open ') or s.startswith('p2m_export '):
                for grp in re.findall(r'"([^"]*)"', s)[:1]:
                    opened |= set(x.split('~')[0] for x in grp.split())
        vis = set(opened) | set(extra_ns)
        own = qual.rsplit('.', 1)[0] if '.' in qual else ''
        while own:
            vis.add(own); own = own.rsplit('.', 1)[0] if '.' in own else ''
        # Lean resolves 'open X' inside namespace N also as N.X
        for o in list(opened):
            for n in list(vis):
                if (n + '.' + o) in ddecl or any(k.startswith(n + '.' + o + '.') for k in ()):
                    vis.add(n + '.' + o)
        return vis
    def tops_of(text):
        return set(w.split('.')[0] for w in TOK.findall(text))
    BINDER_RE = re.compile(r'[({\[⦃]\s*([^:(){}\[\]⦃⦄,]+?)\s*:(?!=)')
    QUANT_RE = re.compile(r'(?:∀|∃!?|fun|λ|∑|∏|⨆|⋃|⋂)\s+([^,:=(){}\[\]]+?)\s*(?:,|:|=>|↦)')
    BTYPE_RE = re.compile(r"[({\[⦃]\s*([^:(){}\[\]⦃⦄,]+?)\s*:\s*([A-Za-z_\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2100-\u214F\U0001D400-\U0001D7FF][A-Za-z0-9_'.\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2070-\u209F\u2100-\u214F\U0001D400-\U0001D7FF]*)")
    BTYPE_Q_RE = re.compile(r"(?:∀|∃!?|fun|λ)\s+([^,:=(){}\[\]]+?)\s*:\s*([A-Za-z_\u00C0-\u024F\u0370-\u03FF\u2100-\u214F][A-Za-z0-9_'.\u2070-\u209F]*)")
    def binder_types(text):
        """bound variable -> head constant of its type, as written ((W : WeierstrassCurve ℤ) gives W -> WeierstrassCurve)"""
        bt = {}
        for rx in (BTYPE_RE, BTYPE_Q_RE):
            for m in rx.finditer(text):
                for x in m.group(1).split():
                    if re.match(r"^[A-Za-z_\u00C0-\u1FFF][A-Za-z0-9_'\u00C0-\u1FFF\u2070-\u209F]*$", x):
                        ty = m.group(2).rstrip('.')
                        if x in bt and bt[x] != ty: bt[x] = None   # bound twice with different types: refuse field links on it
                        elif x not in bt: bt[x] = ty
        return {k: v for k, v in bt.items() if v is not None}
    def bound_names(text):
        b = set()
        for m in BINDER_RE.finditer(text):
            for x in m.group(1).split():
                if re.match(r"^[A-Za-z_\u00C0-\u1FFF][A-Za-z0-9_'\u00C0-\u1FFF\u2070-\u209F]*$", x): b.add(x)
        for m in QUANT_RE.finditer(text):
            for x in re.sub(r'[(){}\[\]]', ' ', m.group(1)).split():
                if re.match(r"^[A-Za-z_\u00C0-\u1FFF][A-Za-z0-9_'\u00C0-\u1FFF\u2070-\u209F]*$", x): b.add(x)
        return b
    LINKSTATS = collections.Counter()
    def make_resolver(R, this_def=None, vis=(), tops=frozenset(), self_name=None, bound=frozenset(), btypes=None):
        vis = set(vis); btypes = btypes or {}
        def resolve_type(t):
            """qualified name under which members of type t should be looked up: a project declaration if visible, else t as written / completed through open namespaces"""
            if t in ddecl: return [t]
            cands = [ns + '.' + t for ns in vis if (ns + '.' + t) in ddecl]
            if len(cands) == 1: return cands
            # not a project type (e.g. a Mathlib structure): members may still be project declarations in its namespace
            return [t] + [ns + '.' + t for ns in vis]
        def member(T, rest):
            """T.rest or T.<first component of rest>, also through 'extends' parents"""
            seen = set(); todo = [T]
            while todo:
                t = todo.pop(0)
                if t in seen: continue
                seen.add(t)
                if (t + '.' + rest) in ddecl: return t + '.' + rest
                first = rest.split('.')[0]
                if (t + '.' + first) in ddecl: return t + '.' + first
                todo.extend(EXT.get(t, []))
            return None
        def target(q, cls):
            k, line, kw = ddecl[q]
            stem = DEFS[k]['stem']
            href = ('#L%d' % line) if this_def == stem else (R + 'def/%s.html#L%d' % (stem, line))
            LINKSTATS[cls] += 1
            return (href, '%s %s — Def_%s.lean, line %d' % (kw, q, stem, line), cls)
        def res(w):
            w = w.rstrip('.')
            if w == self_name: return None
            parts = w.split('.')
            if len(parts) == 1 and w in bound: return None
            if w in ddecl: return target(w, 'exact')
            if w in qidx:
                LINKSTATS['theorem'] += 1
                return (R + 'thm.html#' + w, 'theorem ' + w, 'theorem')
            if len(parts) == 1:
                cands = set(ns + '.' + w for ns in vis if (ns + '.' + w) in ddecl)
                if len(cands) == 1: return target(cands.pop(), 'bare')
                return None
            head = parts[0]
            if len(head) > 1 and head[0].isupper() and head.isascii():
                cands = set(ns + '.' + w for ns in vis if (ns + '.' + w) in ddecl)
                if len(cands) == 1: return target(cands.pop(), 'qualified')
                return None
            # field notation x.foo: only when x is bound with a visible type T and T.foo (or a parent structure's foo) is a project declaration
            if head in btypes and btypes[head] not in bound:
                rest = '.'.join(parts[1:])
                for T in resolve_type(btypes[head]):
                    q = member(T, rest)
                    if q: return target(q, 'field')
            return None
        return res
    commit = a.commit
    if not commit:
        try:
            import subprocess
            commit = subprocess.run(['git', '-C', a.repo, 'rev-parse', '--short=8', 'HEAD'], capture_output=True, text=True).stdout.strip() or 'unknown'
        except Exception: commit = 'unknown'
    toolchain = open(os.path.join(a.repo, 'lean-toolchain')).read().strip().replace('leanprover/lean4:', 'Lean ') if os.path.exists(os.path.join(a.repo, 'lean-toolchain')) else 'Lean'
    mth = re.search(r'Mathlib .(v[0-9.]+).', open(os.path.join(a.repo, 'README.md'), encoding='utf-8').read())
    if mth: toolchain += ', Mathlib ' + mth.group(1)
    out = a.out
    global REPORT_PATH
    REPORT_PATH = os.path.join(os.path.dirname(os.path.abspath(out)), 'render-report.json')
    if os.path.exists(out): shutil.rmtree(out)
    for d in ('assets/vendor', 'data/shard', 'route', 'dag', 'def', 'docs'): os.makedirs(os.path.join(out, d), exist_ok=True)
    # ------------------------------------------------------------------ English layer (optional)
    content = {}; content_meta = {}
    top = json.load(open(os.path.join(GEN, 'data', 'top_dag.json'), encoding='utf-8'))
    for n in top['nodes']:
        content.setdefault(n['id'], {})['title'] = n['title']
        if n.get('title_raw'): content[n['id']]['title_math'] = n['title_raw']
    FIELD_MAP = (('title_en', 'title'), ('title', 'title'), ('statement_en', 'statement'), ('statement', 'statement'), ('summary_en', 'statement'),
                 ('proof_idea_en', 'proof_idea'), ('context_en', 'context'), ('context', 'context'), ('strength_note', 'strength'), ('strength_en', 'strength'),
                 ('note_md', 'strength'), ('source', 'strength_src'), ('mathlib_note', 'mathlib'), ('references', 'references'), ('mathlib_parallels', 'mathlib'))
    unmatched = []; odd_dollar = []   # rows with a line holding an odd number of $ (an unpaired delimiter: that text would ship as raw TeX and selfcheck would fail late)
    if a.content and os.path.isdir(a.content):
        for fn in sorted(os.listdir(a.content)):
            if not (fn.endswith('.json') or fn.endswith('.jsonl')): continue
            try:
                if fn.endswith('.jsonl'):
                    data = []
                    for ln_no, l in enumerate(open(os.path.join(a.content, fn), encoding='utf-8'), 1):
                        if not l.strip(): continue
                        try: data.append(json.loads(l))
                        except Exception as e: print(f'content: {fn} line {ln_no} unreadable ({e}); skipped', file=sys.stderr)
                else:
                    data = json.load(open(os.path.join(a.content, fn), encoding='utf-8'))
            except Exception as e: print('content: skip', fn, e, file=sys.stderr); continue
            recs = data
            if isinstance(data, dict) and ('nodes' in data or 'theorems' in data or 'entries' in data):
                content_meta.update({k: v for k, v in data.items() if k not in ('nodes', 'theorems', 'entries')})
                recs = data.get('nodes') or data.get('theorems') or data.get('entries')
            if isinstance(recs, dict): items = recs.items()
            else: items = [((r.get('name') or r.get('id') or r.get('qual') or r.get('lean_name')), r) for r in recs]
            n_ok = 0
            for name, r in items:
                if not name or not isinstance(r, dict): continue
                if r.get('kind') == 'def-module' or (name not in qidx and ('Def_' + name.replace('Def_', '')) and name.replace('Def_', '') in didx):
                    key = 'Def_' + name.replace('Definitions/', '').replace('.lean', '').replace('Def_', '')
                    if key[4:] not in didx: unmatched.append((fn, name)); continue
                else:
                    key = name
                    if key not in qidx: unmatched.append((fn, name)); continue
                c = content.setdefault(key, {})
                for src_k, dst_k in FIELD_MAP:
                    if r.get(src_k): c[dst_k] = r[src_k]
                # references may carry a parallel origin-tag list; keep only those with the requested tag
                if isinstance(r.get('references'), list) and isinstance(r.get('references_origin'), list) and len(r['references']) == len(r['references_origin']):
                    kept = [x for x, o in zip(r['references'], r['references_origin']) if o == a.references_origin or a.references_origin == 'all']
                    c['references'] = kept
                    c['references_dropped'] = len(r['references']) - len(kept)
                for fk in ('title', 'statement', 'proof_idea', 'context', 'strength', 'mathlib', 'references'):
                    for x in (c.get(fk) if isinstance(c.get(fk), list) else [c.get(fk)]):
                        if isinstance(x, str) and any(ln.replace('\\$', '').replace('$$', '').count('$') % 2 for ln in clean_md_text(x).split('\n') if not ln.startswith(chr(96) * 3)):
                            odd_dollar.append('%s:%s.%s' % (fn, key, fk))
                n_ok += 1
            print(f'content: {fn}: {n_ok} records merged', file=sys.stderr)
    print(f'content: {len(content)} theorems/definition modules carry English; {len(unmatched)} content records matched NO theorem or definition module%s' % ((': ' + ', '.join('%s:%s' % u for u in unmatched[:40]) + (' …' if len(unmatched) > 40 else '')) if unmatched else ''), file=sys.stderr)
    REPORT['content'] = {'keys_with_english': len(content), 'unmatched_records': ['%s:%s' % u for u in unmatched], 'odd_dollar_fields': odd_dollar}
    if odd_dollar: print(f'content: {len(odd_dollar)} fields have a line with an unpaired $ (will reach the page as raw TeX and fail selfcheck): {", ".join(odd_dollar[:30])}', file=sys.stderr)
    # all mathematics goes through KaTeX once at build time: the repository documents and English titles are pre-rendered to HTML
    # (static pages); the English statement/proof/context/reference text of the theorem records and definition-module pages is
    # validated with the same strict parse and shipped as TeX source, typeset in the browser by assets/vendor/katex/katex.min.js
    acc_static = set(); acc_client = {}   # client: (tex, display) -> content keys using it, for the error report
    for key, c in content.items():
        for f, v in c.items():
            for x in (v if isinstance(v, list) else [v]):
                if x is None or isinstance(x, (dict, bool)): continue
                x = str(x)
                if f in ('title', 'title_math'): gather_math(x, acc_static)   # titles are pre-rendered on the static pages and typeset live in the explorer heading
                for s in math_fragments(x): acc_client.setdefault(math_key(s), set()).add(key)
    for pth in [os.path.join(a.repo, 'README.md'), os.path.join(a.repo, 'PROOF-PATH.md'), os.path.join(a.repo, 'ATTRIBUTION.md')] + [os.path.join(a.docs, f) for f in (os.listdir(a.docs) if os.path.isdir(a.docs) else [])]:
        if os.path.exists(pth) and pth.endswith('.md'): gather_math(open(pth, encoding='utf-8').read(), acc_static)
    prerender_math(acc_static, acc_client.keys())
    REPORT['math'] = {'static_fragments': len(acc_static), 'english_fragments': len(acc_client), 'errors': [
        {'tex': ('$$%s$$' if d else '$%s$') % t, 'error': TEX_ERR[(t, d)], 'in': sorted(acc_client.get((t, d), [])) or ['(repository documents or titles)']}
        for (t, d) in sorted(TEX_ERR)]}
    for e in REPORT['math']['errors']: print('katex: does not parse: %s — %s — used by %s' % (e['tex'][:120], e['error'][:100], ', '.join(e['in'][:4])), file=sys.stderr)
    if TEX_ERR and a.tex_errors == 'fail':
        json.dump(REPORT, open(REPORT_PATH, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
        sys.exit('%d TeX fragments do not parse under KaTeX (listed above and in %s); fix the content rows, or rerun with --tex-errors=source to ship them as visible TeX source' % (len(TEX_ERR), REPORT_PATH))
    def md_inline(s, R='', client=False):
        """Markdown of the generated English layer (untrusted: no raw HTML, images or off-site links survive)."""
        if not s: return ''
        return md_to_html(str(s), linker, R, DOC_LINKS, a.repo, client, untrusted=True)
    def src_links(s):
        """'PROOF-PATH.md §4; docs/route.md §7; docs/limitations.md' -> links to the rendered pages (the reader's tree has no docs/ folder)"""
        if not a.include_docs:   # cite only documents that are rendered here: PROOF-PATH.md and the route chapters
            s = '; '.join(p for p in (x.strip() for x in str(s).split(';')) if not re.match(r'docs/(overview|structure|verification|limitations|port-lean433)\.md', p))
        s = html.escape(s)
        s = re.sub(r'docs/route\.md(?: §(\d)(?:\.\d)?)?', lambda m: '<a href="route/%s">the route document%s</a>' % (('s%s.html' % m.group(1)) if m.group(1) else 'index.html', (' §' + m.group(1)) if m.group(1) else ''), s)
        s = re.sub(r'docs/(overview|structure|verification|limitations)\.md', lambda m: '<a href="docs/%s.html">the %s document</a>' % (m.group(1), m.group(1)), s)
        s = re.sub(r'PROOF-PATH\.md(?: §(\d))?', lambda m: '<a href="route/index.html#in-brief">PROOF-PATH.md%s</a>' % ((' §' + m.group(1)) if m.group(1) else ''), s)
        return s
    def en_block(c):
        en = {}
        # the English layer of a theorem record: mathematics left as TeX source (client=True), typeset in the browser
        if c.get('statement'): en['statement_html'] = md_inline(c['statement'], '', True)
        if c.get('proof_idea'): en['proof_html'] = md_inline(c['proof_idea'], '', True)
        if c.get('context'): en['context_html'] = md_inline(c['context'], '', True)
        if c.get('strength'):
            src = src_links(str(c['strength_src'])) if c.get('strength_src') else ''   # empty when every source named is a document not rendered here
            en['strength_html'] = md_inline(c['strength'], '', True) + (('<p class="muted small">Condensed from %s.</p>' % src) if src else '')
        if c.get('mathlib'): en['mathlib_html'] = md_inline(c['mathlib'], '', True)
        refs = [str(x) for x in (c['references'] if isinstance(c['references'], list) else [c['references']]) if x is not None and not isinstance(x, (dict, bool, list))] if c.get('references') else []
        if refs: en['references_html'] = [re.sub(r'</?p>', '', md_inline(x, '', True)).strip() if '$' in x or chr(96) in x else html.escape(x) for x in refs]
        if en and c.get('title') and '$' in str(c['title']): en['title_html'] = re.sub(r'</?p>', '', md_inline(c['title'], '', True)).strip()   # the explorer heading, typeset; titles.js keeps the plain form for search and lists
        en['nm'] = sum(v.count('<span class="tex') for v in ([en.get('statement_html', ''), en.get('proof_html', ''), en.get('context_html', ''), en.get('strength_html', ''), en.get('mathlib_html', ''), en.get('title_html', '')] + en.get('references_html', [])))
        return en   # the caller pops 'nm' (a build statistic, not shipped)
    # ------------------------------------------------------------------ linker
    DOC_LINKS = {'README.md': 'docs/readme.html', 'PROOF-PATH.md': 'route/index.html#in-brief', 'ATTRIBUTION.md': 'docs/attribution.html',
                 'overview.md': 'docs/overview.html', 'route.md': 'route/index.html', 'structure.md': 'docs/structure.html',
                 'verification.md': 'docs/verification.html', 'limitations.md': 'docs/limitations.html', 'port-lean433.md': 'docs/port-lean433.html', 'LICENSE': '../LICENSE', 'NOTICE': '../NOTICE'}
    if not a.include_docs:
        for k in ('overview.md', 'structure.md', 'verification.md', 'limitations.md', 'port-lean433.md'): DOC_LINKS[k] = None
        DOC_LINKS['route.md'] = 'route/index.html'
    def linker(s, R):
        s = s.strip()
        base = s.split(' ')[0]
        if base in qidx: return R + 'thm.html#' + base
        m = re.match(r'^(?:Theorems/)?Thm_([A-Za-z0-9_]+?)(?:\.lean)?$', base)
        if m and m.group(1) in sidx: return R + 'thm.html#' + TH[sidx[m.group(1)]]['qual']
        m = re.match(r'^(?:P2M/Sol/)?S_([A-Za-z0-9_]+?)(?:\.lean)?$', base)
        if m and m.group(1) in sidx: return R + 'thm.html#' + TH[sidx[m.group(1)]]['qual']
        m = re.match(r'^(?:Definitions/|Definitions\.)?Def_([A-Za-z0-9_]+?)(?:\.lean)?$', base)
        if m and m.group(1) in didx: return R + 'def/' + m.group(1) + '.html'
        if base in ddecl: k, line, kw = ddecl[base]; return R + 'def/' + DEFS[k]['stem'] + '.html#L%d' % line
        rr = make_resolver(R)(base)
        if rr: return rr[0]
        if base in DOC_LINKS: return R + DOC_LINKS[base]
        if base in ('FinalCheck.lean',): return R + '../FinalCheck.lean'
        return None
    env = Environment(loader=DictLoader(T), autoescape=False)
    is_hash = re.fullmatch(r'[0-9a-f]{7,40}', commit) is not None
    stamp = ('commit <code>%s</code>' % commit) if is_hash else html.escape(commit)          # in sentences: 'Documents <stamp> (toolchain)'
    stamp_txt = ('commit %s of the tree' % commit) if is_hash else commit                      # plain-text variant for MANIFEST / README-DOCS
    common = dict(NAV=NAV, n_thm=fmt_int(N), n_def=fmt_int(len(DEFS)), commit=commit, stamp=stamp, toolchain=toolchain)
    def page(path, template, **kw):
        depth = path.count('/'); R = '../' * depth
        htmlt = env.get_template(template).render(R=R, **common, **kw)
        with open(os.path.join(out, path), 'w', encoding='utf-8') as fh: fh.write(htmlt)
    # ------------------------------------------------------------------ data files
    rq = TH[G['root']]['qual']
    if 'FLT.fermatLastTheorem' in content and content['FLT.fermatLastTheorem'].get('title') and content.get(rq, {}).get('title') and content['FLT.fermatLastTheorem']['title'].strip() == content[rq]['title'].strip():
        content['FLT.fermatLastTheorem']['title'] = content['FLT.fermatLastTheorem']['title'].strip() + " (Mathlib's formulation)"
    titles = {q: tex_to_unicode(c['title']) for q, c in content.items() if c.get('title') and q in qidx}
    titles_html = {q: md_to_html(c['title'], lambda s, R: None, '', {}, None, untrusted=True).replace('<p>', '').replace('</p>', '').strip() for q, c in content.items() if c.get('title') and '$' in c['title']}
    def title_html(q):
        return titles_html.get(q) or html.escape(titles.get(q) or tex_to_unicode(content.get(q, {}).get('title', '')))
    # statements touched by the Lean 4.33 port: the individually edited ones are listed by name in docs/port-lean433.md §5.2;
    # the ones re-pointed at Def_Compat_Mathlib430 are visible from their imports
    port = {}
    pnotes = os.path.join(a.docs, 'port-lean433.md')
    if os.path.exists(pnotes):
        ptxt = open(pnotes, encoding='utf-8').read()
        m52 = re.search(r'\*\*5\.2 (.*?)\*\*5\.3', ptxt, re.S)
        if m52:
            for stem in re.findall(r'Thm_([A-Za-z0-9_]+)', m52.group(1)):
                if stem in sidx: port[sidx[stem]] = 1
        print(f'port notes: {len(port)} individually edited statements found in §5.2', file=sys.stderr)
    if 'Compat_Mathlib430' in didx:
        dci = didx['Compat_Mathlib430']
        for i, t in enumerate(TH):
            if dci in t['stmt_defs'] and i not in port: port[i] = 2
    stemx = {i: t['stem'] for i, t in enumerate(TH) if t['stem'] != t['qual'].replace('.', '_')}
    pkind = {i: t['parent_kind'] for i, t in enumerate(TH) if t['parent_kind'] and t['parent_kind'] != 'cites'}
    aliases = {}
    ap_ = os.path.join(GEN, 'data', 'aliases.json')
    if os.path.exists(ap_):
        for q, al in json.load(open(ap_, encoding='utf-8'))['aliases'].items():
            if q in qidx: aliases[q] = '; '.join(al)
    meta = {'v': 1, 'commit': commit, 'aliases': aliases, 'root': G['root'], 'names': [t['qual'] for t in TH], 'stemx': stemx,
            'depth': [t['depth'] for t in TH], 'below': [t['below'] for t in TH], 'height': [t['height'] for t in TH],
            'parent': [t['parent'] for t in TH], 'pkind': pkind, 'via': [t['via'] for t in TH], 'stage': [t['stage'] for t in TH],
            'lm': [1 if t['landmark'] else 0 for t in TH], 'dup': [1 if t['is_dup'] else 0 for t in TH], 'port': port, 'portnotes': ('docs/port-lean433.html#port-5-2' if a.include_docs else ''),
            'defs': [d['stem'] for d in DEFS], 'stages': {str(k): v for k, v in STAGE_SHORT.items()},
            'enNote': a.english_attribution or '', 'refNote': a.references_note or '', 'mathlibDocs': MATHLIB_DOCS_URL if a.mathlib_links else ''}
    # pkind is sparse dict keyed by int -> JS object with string keys; explorer reads m.pkind[i]
    with open(os.path.join(out, 'data', 'meta.js'), 'w', encoding='utf-8') as fh:
        fh.write('window.FLT_META=' + json.dumps(meta, ensure_ascii=False, separators=(',', ':')) + ';\n')
    # the declaration index of the definition modules is its own file, so that no single data file is large
    with open(os.path.join(out, 'data', 'ddecl.js'), 'w', encoding='utf-8') as fh:
        fh.write('window.FLT_DDECL=' + json.dumps({'ddecl': ddecl_list, 'ext': EXT}, ensure_ascii=False, separators=(',', ':')) + ';\n')
    off = [0]; dst = []
    for i in range(N): dst.extend(cites[i]); off.append(len(dst))
    with open(os.path.join(out, 'data', 'edges.js'), 'w') as fh:
        fh.write('window.FLT_EDGES={off:' + json.dumps(off, separators=(',', ':')) + ',dst:' + json.dumps(dst, separators=(',', ':')) + '};\n')
    with open(os.path.join(out, 'data', 'titles.js'), 'w', encoding='utf-8') as fh:
        # an array parallel to meta.names (read through FLT.title(i)); keying by name would repeat 29k long names (≈2 MB)
        fh.write('window.FLT_TITLES=' + json.dumps([titles.get(t['qual'], '') for t in TH], ensure_ascii=False, separators=(',', ':')) + ';\n')
    print(f'meta/edges/titles written {time.time()-t0:.0f}s', file=sys.stderr)
    # shards: stream thm.jsonl + sol.jsonl (both sorted by stem) in lockstep
    shards = [dict() for _ in range(NSHARDS)]
    sol_iter = load_jsonl(os.path.join(a.build, 'sol.jsonl')); sol_cur = next(sol_iter, None)
    stmt_decl = {}   # decl text for landmark cards (landmarks only, to bound memory)
    n_en_thm = 0; most_math = (None, 0)   # theorem records carrying English; the one with the most $…$ fragments (for the browser test)
    lmset = set(i for i, t in enumerate(TH) if t['landmark'])
    for rec in load_jsonl(os.path.join(a.build, 'thm.jsonl')):
        i = sidx[rec['stem']]; t = TH[i]
        while sol_cur is not None and sol_cur['stem'] < rec['stem']: sol_cur = next(sol_iter, None)
        so = None
        if sol_cur is not None and sol_cur['stem'] == rec['stem']:
            s = sol_cur
            so = {'ln': s['lines'], 'cl': s['content_lines'], 'h': s['helpers'], 'dl': s['defs_local'], 'sl': s['solution_line'],
                  'tl': s.get('solution_lines_total', 0), 'tt': 1 if s['solution_tail_truncated'] else 0, 'tail': trim_tail(s['solution_tail'])}
        r = {'cx': rec['context'], 'dc': rec['decl'], 'tr': rec['trailer'], 'sd': t['stmt_defs'], 'pd': t['proof_defs'], 'st': t['stmt_thms'], 'so': so, 'cu': cite_uses[i]}
        if i in lmset:
            # landmarks: the whole proof module (minus imports and the generated preamble) is worth reading in the browser
            sp = os.path.join(a.repo, 'P2M', 'Sol', 'S_%s.lean' % rec['stem'])
            if os.path.exists(sp):
                ptext = open(sp, encoding='utf-8', errors='replace').read()
                if ptext.startswith('/-\n') and ptext.find('\n-/\n') >= 0: ptext = ptext[ptext.find('\n-/\n') + 4:]   # the licence header, as on statement pages
                plines = [l for l in ptext.split('\n') if not l.startswith('import ') and not l.startswith('attribute [-')]
                while plines and not plines[0].strip(): plines.pop(0)
                cap = 700
                ptxt = '\n'.join(plines[:cap])
                r['proof_html'] = hl_lean(ptxt, make_resolver('', None, scope_of(rec['context'] + plines[:cap], t['qual']), tops_of(ptxt), None, frozenset(), binder_types(ptxt + chr(10) + rec['decl']))) + ('\n<span class="c1">… %d more lines in the file</span>' % (len(plines) - cap) if len(plines) > cap else '')
                r['proof_lines'] = len(plines)
        ml = rec['imports']['mathlib']
        if ml and ml != ['Mathlib']: r['ml'] = ml
        c = content.get(t['qual']); nm = 0
        if c:
            en = en_block(c); nm = en.pop('nm', 0)
            if en: r['en'] = en
        if i in lmset: stmt_decl[i] = (rec['context'], rec['decl'])
        if a.link_report:
            rs = make_resolver('', None, scope_of(rec['context'], t['qual']), tops_of(rec['decl'] + ' ' + ' '.join(rec['context']) + ' ' + t['qual']), t['qual'], bound_names(rec['decl'] + chr(10) + chr(10).join(rec['context'])), binder_types(rec['decl'] + chr(10) + chr(10).join(rec['context'])))
            for w in set(TOK.findall(rec['decl'])):
                if rs(w) is None and w.rstrip('.') not in (t['qual'],): LINKSTATS['unlinked'] += 1
        shards[fnv(t['qual']) % NSHARDS][t['qual']] = r
        if r.get('en'):
            n_en_thm += 1
            if nm > most_math[1]: most_math = (t['qual'], nm)
    REPORT['english'] = {'theorem_records': n_en_thm, 'most_math_theorem': most_math[0], 'most_math_fragments': most_math[1]}
    if a.link_report: print('identifier links over all statements, by rule: ' + ', '.join('%s %s' % (k, fmt_int(v)) for k, v in LINKSTATS.most_common()), file=sys.stderr)
    LINKSTATS.clear()
    sizes = []
    for k in range(NSHARDS):
        sid = '%03d' % k
        js = 'FLT_SHARD_CB("%s",' % sid + json.dumps(shards[k], ensure_ascii=False, separators=(',', ':')) + ');\n'
        with open(os.path.join(out, 'data', 'shard', sid + '.js'), 'w', encoding='utf-8') as fh: fh.write(js)
        sizes.append(len(js.encode('utf-8'))); shards[k] = None
    print(f'shards written {time.time()-t0:.0f}s; max {max(sizes)/1e6:.2f} MB (shard {sizes.index(max(sizes)):03d}), mean {sum(sizes)/len(sizes)/1e6:.2f} MB, total {sum(sizes)/1e6:.0f} MB; {fmt_int(n_en_thm)} records carry English', file=sys.stderr)
    REPORT['shards'] = {'n': NSHARDS, 'max_bytes': max(sizes), 'max_shard': '%03d' % sizes.index(max(sizes)), 'mean_bytes': sum(sizes) // len(sizes), 'total_bytes': sum(sizes)}
    # ------------------------------------------------------------------ assets
    for fn in ('site.css', 'site.js', 'hl.js', 'explorer.js'): shutil.copy(os.path.join(GEN, 'assets', fn), os.path.join(out, 'assets', fn))
    shutil.copy(os.path.join(GEN, 'vendor', 'graphviz.umd.js'), os.path.join(out, 'assets', 'vendor', 'graphviz.umd.js'))
    shutil.copy(os.path.join(GEN, 'vendor', 'graphviz.LICENSE'), os.path.join(out, 'assets', 'vendor', 'graphviz.LICENSE.txt'))
    os.makedirs(os.path.join(out, 'assets', 'vendor', 'katex'))
    import base64
    kcss = open(os.path.join(GEN, 'vendor', 'katex', 'katex.min.css'), encoding='utf-8').read()
    def font_sub(m):
        name = m.group(1)
        data = base64.b64encode(open(os.path.join(GEN, 'vendor', 'katex', 'fonts', name + '.woff2'), 'rb').read()).decode()
        return 'src:url(data:font/woff2;base64,%s) format("woff2")' % data
    kcss2, nsub = re.subn(r'src:url\(fonts/([A-Za-z0-9_-]+)\.woff2\) format\("woff2"\),url\(fonts/\1\.woff\) format\("woff"\),url\(fonts/\1\.ttf\) format\("truetype"\)', font_sub, kcss)
    if 'fonts/' in kcss2: raise RuntimeError('katex css still references font files (%d substituted)' % nsub)
    open(os.path.join(out, 'assets', 'vendor', 'katex', 'katex-embedded.css'), 'w', encoding='utf-8').write(kcss2)
    shutil.copy(os.path.join(GEN, 'vendor', 'katex', 'LICENSE'), os.path.join(out, 'assets', 'vendor', 'katex', 'LICENSE'))
    shutil.copy(os.path.join(GEN, 'vendor', 'katex', 'FONTS-LICENSE.txt'), os.path.join(out, 'assets', 'vendor', 'katex', 'FONTS-LICENSE.txt'))
    shutil.copy(os.path.join(GEN, 'vendor', 'katex', 'katex.min.js'), os.path.join(out, 'assets', 'vendor', 'katex', 'katex.min.js'))
    with open(os.path.join(out, 'assets', 'vendor', 'LICENSES.txt'), 'w') as fh:
        fh.write('Third-party files in this folder\n\n'
                 'graphviz.umd.js - @hpcc-js/wasm 2.35.0 (Graphviz compiled to WebAssembly), Apache License 2.0, see graphviz.LICENSE.txt; '
                 'includes Graphviz (Eclipse Public License 1.0 / Common Public License) as compiled code.\n'
                 'katex/ - KaTeX 0.18.4 (katex.min.js, and katex-embedded.css = katex.min.css with the fonts inlined), MIT License, see katex/LICENSE; '
                 'the bundled fonts are under the SIL Open Font License 1.1, copyright Design Science, Inc. and Khan Academy, see katex/FONTS-LICENSE.txt.\n')
    # ------------------------------------------------------------------ thm.html (explorer)
    page('thm.html', 'thm', title='Theorems', navkey='thm', katex_js=True)
    # ------------------------------------------------------------------ documents
    docs_dir = a.docs
    docs = [('readme', os.path.join(a.repo, 'README.md'), 'README'), ('overview', os.path.join(docs_dir, 'overview.md'), 'Overview'),
            ('structure', os.path.join(docs_dir, 'structure.md'), 'Structure of the tree'), ('verification', os.path.join(docs_dir, 'verification.md'), 'Verification'),
            ('limitations', os.path.join(docs_dir, 'limitations.md'), 'Limitations and caveats'), ('attribution', os.path.join(a.repo, 'ATTRIBUTION.md'), 'Attribution'),
            ('port-lean433', os.path.join(docs_dir, 'port-lean433.md'), 'The Lean 4.33.1 port (engineering record)')]
    if not a.include_docs: docs = [d for d in docs if d[1].startswith(a.repo)]
    doc_rows = []
    for key, path, label in docs:
        if not os.path.exists(path): continue
        text = open(path, encoding='utf-8').read()
        if key == 'port-lean433': text = text.replace('**5.2 ', '<a id="port-5-2"></a>**5.2 ', 1).replace('**5.1 ', '<a id="port-5-1"></a>**5.1 ', 1)
        first = text.split('\n', 1)[0].lstrip('# ').strip() or label
        body = md_to_html(text, linker, '../', DOC_LINKS, a.repo)
        if path.startswith(a.repo):
            note = '<p class="muted small">Rendered from <code>%s</code> at the root of the repository.</p>' % html.escape(os.path.basename(path))
        else:
            note = '<p class="muted small provenance">From the project\'s documentation set (<code>docs/%s</code>); it describes the same Lean files as this tree. References to files this tree does not have are marked.</p>' % html.escape(os.path.basename(path))
        page('docs/%s.html' % key, 'prose', title=first, navkey='docs', body=note + body, mainclass='prose', after='')
        doc_rows.append((key, first, label))
    idx_body = '<h1>Documents</h1><p>The prose that accompanies the Lean tree, rendered as written. Backticked theorem and definition names link to their pages.</p><table class="plain">' + ''.join(
        '<tr><td><a href="%s.html">%s</a></td><td>%s</td></tr>' % (k, html.escape(lbl), html.escape(first)) for k, first, lbl in doc_rows) + '</table>'
    if a.include_docs and os.path.exists(os.path.join(docs_dir, 'README.md')):
        idx_body += '<h2>The documented branch\'s own index</h2><article class="prose math-scope">' + md_to_html(open(os.path.join(docs_dir, 'README.md'), encoding='utf-8').read(), linker, '../', DOC_LINKS, a.repo) + '</article>'
    page('docs/index.html', 'prose', title='Documents', navkey='docs', body=idx_body, mainclass='prose', after='')
    print(f'docs written {time.time()-t0:.0f}s', file=sys.stderr)
    # ------------------------------------------------------------------ landmark DAG + top DAG (dot at build time)
    import subprocess
    PAL = dict(fill='#E6F2EA', border='#6FA287', text='#1F3B2C', sub='#5C7466', rootFill='#2F7D55', rootBorder='#1E5C3C', rootText='#FFFFFF', rootSub='#CFE7D8', edge='#8A9AA5', step='#8C7FD9', stepB='#6B5FC0')
    def wrap_words(s, width):
        words = s.split(); lines = []; cur = ''
        for w in words:
            if len(cur) + 1 + len(w) > width and cur: lines.append(cur); cur = w
            else: cur = (cur + ' ' + w).strip()
        if cur: lines.append(cur)
        return lines
    def short_name(q):
        p = q.split('.'); return q if len(p) <= 2 else '.'.join(p[-2:])
    def gv(s):   # text for a Graphviz HTML-like label: HTML-escaped, and no backslash escapes for dot to interpret
        return html.escape(s).replace('\\', '&#92;')
    def node_label(q, is_root, R, width=28, lean=True, pt=12):
        title = titles.get(q)
        tc = PAL['rootText'] if is_root else PAL['text']; sc = PAL['rootSub'] if is_root else PAL['sub']
        leann = gv(short_name(q)) if len(short_name(q)) <= 46 else gv(short_name(q)[:44] + '…')
        if title:
            tl = '<BR/>'.join(gv(x) for x in wrap_words(title, width))
            sub = ('<TR><TD><FONT FACE="DejaVu Sans Mono" POINT-SIZE="8" COLOR="%s">%s</FONT></TD></TR>' % (sc, leann)) if lean else ''
            return '<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0" CELLPADDING="1" HREF="%sthm.html#%s" TOOLTIP="%s"><TR><TD><FONT FACE="Helvetica" POINT-SIZE="%d" COLOR="%s">%s</FONT></TD></TR>%s</TABLE>>' % (R, gv(q), gv(q), pt, tc, tl, sub)
        parts = short_name(q)
        return '<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0" CELLPADDING="2" HREF="%sthm.html#%s" TOOLTIP="%s"><TR><TD><FONT FACE="DejaVu Sans Mono" POINT-SIZE="9" COLOR="%s">%s</FONT></TD></TR></TABLE>>' % (R, html.escape(q), html.escape(q), tc, '<BR/>'.join(html.escape(x) for x in re.findall('.{1,%d}(?:[._]|$)' % width, parts) if x) or html.escape(parts))
    def run_dot(dot, path_svg):
        r = subprocess.run(['dot', '-Tsvg'], input=dot.encode(), capture_output=True)
        if r.returncode != 0: raise RuntimeError(r.stderr.decode()[:500])
        svg = r.stdout.decode()
        svg = svg[svg.index('<svg'):]
        # keep the intrinsic width/height: CSS fits the figure to the page and 'zoomed' shows it at natural (reading) size
        if path_svg:
            with open(path_svg, 'w', encoding='utf-8') as fh: fh.write(r.stdout.decode())
        return svg
    # top DAG (the nine statements at the top, with reduction-step squares as in the figure)
    def top_dot(R):
        L = ['digraph FLT {', ' graph [rankdir=TB, bgcolor="transparent", splines=spline, nodesep=0.3, ranksep=0.5, pad=0.2];',
             ' node [shape=box, style="rounded,filled", penwidth=1.2, margin="0.14,0.08", fontname="Helvetica"];',
             ' edge [color="%s", penwidth=1.2, arrowsize=0.7];' % PAL['edge']]
        ids = {n['id']: 'n%d' % k for k, n in enumerate(top['nodes'])}
        for n in top['nodes']:
            isr = n['id'] == 'fermat_last_theorem'
            L.append(' %s [label=%s, fillcolor="%s", color="%s", penwidth=%s];' % (ids[n['id']], node_label(n['id'], isr, R, 22, lean=False, pt=14), PAL['rootFill'] if isr else PAL['fill'], PAL['rootBorder'] if isr else PAL['border'], '1.6' if isr else '1.2'))
        for k, st in enumerate(top['steps']):
            s = 's%d' % k
            L.append(' %s [shape=square, label="", width=0.15, height=0.15, style=filled, fillcolor="%s", color="%s", margin=0, tooltip="one proof step: the conclusion below is proved from exactly the premises above"];' % (s, PAL['step'], PAL['stepB']))
            for p in st['premises']: L.append(' %s -> %s [arrowhead=none];' % (ids[p], s))
            L.append(' %s -> %s;' % (s, ids[st['conclusion']]))
        L.append('}')
        return '\n'.join(L)
    top_svg_index = run_dot(top_dot(''), None)
    # landmark DAG
    LM = G['landmarks']; lm_quals = [l['qual'] for l in LM]
    def lm_dot(R, quals, edges, ctx_quals=()):
        L = ['digraph L {', ' graph [rankdir=TB, bgcolor="transparent", splines=spline, nodesep=0.25, ranksep=0.55, pad=0.2, newrank=true];',
             ' node [shape=box, style="rounded,filled", penwidth=1.2, margin="0.12,0.06", fontname="Helvetica", fillcolor="%s", color="%s"];' % (PAL['fill'], PAL['border']),
             ' edge [color="%s", penwidth=1.1, arrowsize=0.65];' % PAL['edge']]
        ids = {q: 'n%d' % k for k, q in enumerate(quals)}
        for q in quals:
            isr = q == 'fermat_last_theorem'
            extra = ', fillcolor="%s", color="%s", penwidth=1.6' % (PAL['rootFill'], PAL['rootBorder']) if isr else ''
            if q in ctx_quals and not isr: extra = ', fillcolor="white", color="%s", style="rounded,filled,dashed"' % PAL['border']
            L.append(' %s [label=%s%s];' % (ids[q], node_label(q, isr, R, 24), extra))
        for parent, child in edges:
            if parent in ids and child in ids: L.append(' %s -> %s;' % (ids[child], ids[parent]))
        L.append('}')
        return '\n'.join(L)
    lm_edges = [(l['qual'], c) for l in LM for c in l['children']]
    # transitive reduction of the landmark DAG to keep the picture readable
    ch = collections.defaultdict(set)
    for p, c in lm_edges: ch[p].add(c)
    def reach(p, skip):
        seen = set(); st = [x for x in ch[p] if x != skip]
        while st:
            x = st.pop()
            if x in seen: continue
            seen.add(x); st.extend(ch[x])
        return seen
    red = [(p, c) for p, c in lm_edges if c not in reach(p, c)]
    lm_dot_src = lm_dot('../', lm_quals, red)
    open(os.path.join(a.build, 'landmarks.dot'), 'w', encoding='utf-8').write(lm_dot_src)
    lm_svg = run_dot(lm_dot_src, os.path.join(out, 'dag', 'landmarks.svg'))
    legend = '<div class="legend"><span><i class="root"></i> Fermat\'s Last Theorem</span><span><i></i> proved theorem (every node is proved)</span><span>arrows run from a premise to the theorem whose proof cites it, possibly through unnamed intermediate theorems</span></div>'
    rows = ''.join('<tr><td><a href="../thm.html#%s"><code>%s</code></a>%s</td><td>%s</td><td>%s</td><td>%d</td><td class="muted small">%s</td></tr>' % (
        html.escape(l['qual']), html.escape(l['qual']), (' <span class="muted small">%s</span>' % title_html(l['qual']) if l['qual'] in titles else ''),
        html.escape(STAGE_SHORT.get(l['stage'], '')) if l['stage'] is not None else '', fmt_int(TH[qidx[l['qual']]]['below']), TH[qidx[l['qual']]]['depth'], html.escape(', '.join(l['sources']))) for l in LM)
    body = (('<h1>The landmark theorems and how they depend on each other</h1><p>The %d theorems named in <code>PROOF-PATH.md</code> and in ' + ('the project\'s <a href="../route/index.html">route</a> and <a href="../docs/overview.html">overview</a> documents' if a.include_docs else 'the <a href="../route/index.html">route</a> chapters') + ', with an arrow when one lies below another in the citation graph with no third landmark in between (transitively reduced). Premises are drawn above conclusions, as in the proof. Click a node for its page; every one of the %s theorems has one.</p>%s<p class="muted small">The whole graph is wide and is shown at reading size: scroll sideways, or click it to fit the window; the <a href="../route/index.html">route pages</a> carry one smaller graph per step.</p><div class="figure zoomable zoomed" title="click to fit / enlarge">%s</div>')
            % (len(LM), fmt_int(N), legend, lm_svg) +
            '<h2>The landmarks as a table</h2><table class="plain"><tr><th>theorem</th><th>step</th><th>theorems below</th><th>depth</th><th>named in</th></tr>%s</table>' % rows)
    page('dag/index.html', 'prose', title='Landmark graph', navkey='dag', body=body, mainclass='', after='')
    print(f'dag written {time.time()-t0:.0f}s', file=sys.stderr)
    attr_md_path = os.path.join(a.repo, 'ATTRIBUTION.md')
    # ------------------------------------------------------------------ route chapters
    route_md = open(os.path.join(docs_dir, 'route.md'), encoding='utf-8').read()
    pre, secs = [], []
    cur = None
    for line in route_md.split('\n'):
        m = re.match(r'^## (\d+)\.\s+(.*)', line)
        if m: cur = {'num': int(m.group(1)), 'title': m.group(2).strip(), 'lines': [line]}; secs.append(cur); continue
        (cur['lines'] if cur else pre).append(line)
    ppath = open(os.path.join(a.repo, 'PROOF-PATH.md'), encoding='utf-8').read()
    TICK = re.compile(chr(96) + r"([A-Za-z_][A-Za-z0-9_.']*)" + chr(96))
    def thm_card(i, R):
        t = TH[i]; ctx, decl = stmt_decl.get(i, ([], None))
        title = titles.get(t['qual'])
        h = '<div class="thm-card"><div>' + ('<b>%s</b> ' % title_html(t['qual']) if title else '') + '<a class="name" href="%sthm.html#%s">%s</a></div>' % (R, html.escape(t['qual']), html.escape(t['qual']))
        if decl: h += '<pre class="lean">' + (('<span class="c1">' + html.escape('\n'.join(ctx)) + '</span>\n') if ctx else '') + hl_lean(decl, make_resolver(R, None, scope_of(ctx, t['qual']), tops_of(decl + ' ' + ' '.join(ctx) + ' ' + t['qual']), t['qual'], bound_names(decl + chr(10) + chr(10).join(ctx)), binder_types(decl + chr(10) + chr(10).join(ctx)))) + '</pre>'
        h += '<div class="meta">%s theorems below · cites %d · cited by %d · depth %d%s</div></div>' % (fmt_int(t['below']), t['outdeg'], t['indeg'], t['depth'], (' · proof %s lines, %d helpers' % (fmt_int(t['sol']['content_lines']), t['sol']['helpers']) if t.get('sol') else ''))
        return h
    chapters = []
    for s in secs:
        text = '\n'.join(s['lines'])
        named = []; seen = set()
        for nm in TICK.findall(text):
            if nm in qidx and nm not in seen: seen.add(nm); named.append(qidx[nm])
        defs_named = []; dseen = set()
        for mdef in re.findall(r'Def_([A-Za-z0-9_]+)\.lean', text):
            if mdef in didx and mdef not in dseen: dseen.add(mdef); defs_named.append(mdef)
        under = sum(1 for t in TH if t['stage'] == s['num'])
        chapters.append({'num': s['num'], 'title': s['title'], 'text': text, 'named': named, 'defs': defs_named, 'under': under, 'file': 's%d.html' % s['num']})
    for k, ch in enumerate(chapters):
        body = md_to_html(ch['text'], linker, '../', DOC_LINKS, a.repo)
        nav = '<p class="muted small">' + (('← <a href="%s">§%d %s</a>' % (chapters[k-1]['file'], chapters[k-1]['num'], html.escape(chapters[k-1]['title']))) if k > 0 else '<a href="index.html">← The route</a>') + ' · ' + (('<a href="%s">§%d %s</a> →' % (chapters[k+1]['file'], chapters[k+1]['num'], html.escape(chapters[k+1]['title']))) if k + 1 < len(chapters) else '') + '</p>'
        after = nav
        if ch['named'] and ch['num'] != 7:
            inset = set(TH[i]['qual'] for i in ch['named'] if TH[i]['landmark'])
            ctxn = set()
            for p_, c_ in red:
                if p_ in inset and c_ not in inset: ctxn.add(c_)
                if c_ in inset and p_ not in inset: ctxn.add(p_)
            quals_ch = [q for q in lm_quals if q in inset or q in ctxn]
            edges_ch = [(p_, c_) for p_, c_ in red if p_ in (inset | ctxn) and c_ in (inset | ctxn)]
            if len(quals_ch) >= 2:
                svg_ch = run_dot(lm_dot('../', quals_ch, edges_ch, ctxn), None)
                after += '<h2>How the theorems of this step depend on each other</h2><p class="muted small">Green cards are the landmarks named in this section; dashed white cards are landmarks of neighbouring steps they connect to. Premises above conclusions; an arrow may pass through unnamed intermediate theorems. Click a card for its page.</p><div class="figure zoomable" title="click to enlarge">%s</div>' % svg_ch
        if ch['named']:
            after += '<h2 id="named">Theorems named in this section <span class="muted small">(%d; statement as in the tree, numbers from the import graph)</span></h2>' % len(ch['named']) + ''.join(thm_card(i, '../') for i in ch['named'])
        if ch['defs']:
            after += '<h2>Definition modules named here</h2><ul class="refs defs">' + ''.join('<li><a href="../def/%s.html"><code>Definitions/Def_%s.lean</code></a></li>' % (d, d) for d in ch['defs']) + '</ul>'
        if ch['num'] != 7 and ch['under']:
            after += '<p class="muted small">%s theorems of the tree are first reached through this step, in the sense that the first landmark met on a shortest citation path up to <code>fermat_last_theorem</code> is one named in this section. That is a reading aid, not a classification: the infrastructure below modularity and level lowering is largely shared.</p>' % fmt_int(ch['under'])
        after += nav
        page('route/' + ch['file'], 'prose', title='§%d %s' % (ch['num'], ch['title']), navkey='route', body=body, mainclass='prose', after=after)
    toc = '<div class="cards">' + ''.join('<div class="card"><h3><span class="stage-num">%d</span><a href="%s">%s</a></h3><p class="num">%d named theorem%s%s</p></div>' % (
        ch['num'], ch['file'], html.escape(ch['title']), len(ch['named']), '' if len(ch['named']) == 1 else 's', (' · %s theorems first reached through this step' % fmt_int(ch['under'])) if ch['num'] != 7 else '') for ch in chapters) + '</div>'
    intro = md_to_html('\n'.join(pre), linker, '../', DOC_LINKS, a.repo)
    stage_anchors = ''.join('<a id="stage-%d"></a>' % ch['num'] for ch in chapters) + '<a id="stage-0"></a>'
    brief = '<h2 id="in-brief">The route in brief <span class="muted small">(<code>PROOF-PATH.md</code>, as shipped at the root of the repository)</span></h2><article class="prose math-scope">' + md_to_html(ppath, linker, '../', DOC_LINKS, a.repo) + '</article>'
    # a note for readers coming from the Imperial College London FLT project — strictly from PROOF-PATH.md, docs/route.md and ATTRIBUTION.md
    n_icl1 = n_icl2 = 0; sec = 0
    if os.path.exists(attr_md_path):
        for line in open(attr_md_path, encoding='utf-8'):
            mh = re.match(r'^## (\d+)\.', line)
            if mh: sec = int(mh.group(1))
            elif line.startswith('| ' + chr(96)) and sec == 1: n_icl1 += 1
            elif line.startswith('| ' + chr(96)) and sec == 2: n_icl2 += 1
    imperial = ('<aside class="imperial"><b>For readers of the Imperial College London FLT project.</b> The route taken here is the argument of Frey, Serre, Ribet, Wiles and Taylor–Wiles, largely as in Darmon, Diamond and Taylor (<a href="#in-brief">PROOF-PATH.md</a>): irreducibility of the mod-p representation of the Frey curve by Mazur\'s Eisenstein-quotient argument for p ≥ 17, the exponents 5, 7, 11, 13 being settled outright (<a href="s3.html">§3</a>); modularity of semistable curves by Wiles\'s method — Langlands–Tunnell at 3 in the weight-2, level-conditioned form, two modularity lifting theorems by Taylor–Wiles patching in Diamond\'s formulation, and the 3–5 switch (<a href="s4.html">§4</a>); level lowering by Ribet\'s theorem via Čerednik–Drinfeld uniformisation and the Mazur–Ribet step at p (<a href="s5.html">§5</a>); and S₂(Γ₀(2)) = 0 from Mathlib (<a href="s6.html">§6</a>). '
                'Each named theorem is proved in the strength this argument needs, not in textbook generality (<a href="s7.html">§7</a>). This is the architecture of Wiles (1995) and Taylor–Wiles; these pages describe it on its own terms and do not map it against the route planned in the Imperial College project\'s blueprint. '
                'Material from that project is part of the tree: <a href="../docs/attribution.html">ATTRIBUTION.md</a> lists %d files containing material from ImperialCollegeLondon/FLT directly and %d more through an intermediate port — among them the definition of a Frey package, <a href="../def/FLTPrelim_FreyPackage.html"><code>Def_FLTPrelim_FreyPackage</code></a> — and the definition pages concerned carry an "adapted from" badge.</aside>') % (n_icl1, n_icl2)
    page('route/index.html', 'prose', title='The route of the proof', navkey='route', mainclass='prose',
         body=stage_anchors + intro + imperial + '<h2>Step by step</h2>' + toc, after=brief)
    print(f'route written {time.time()-t0:.0f}s', file=sys.stderr)
    # ------------------------------------------------------------------ definition pages
    attrib = {}
    attr_md = os.path.join(a.repo, 'ATTRIBUTION.md')
    if os.path.exists(attr_md):
        sec = 0   # ATTRIBUTION.md section the row is in: 1-2 Imperial College London FLT project, 3 flt-regular, 4 Mathlib
        for line in open(attr_md, encoding='utf-8'):
            mh = re.match(r'^## (\d+)\.', line)
            if mh: sec = int(mh.group(1)); continue
            m = re.match(r'^\|\s*.(Definitions|Theorems|P2M/Sol)/([^ |]+?)\.lean.\s*\|\s*([^|]*)\|\s*(.*)\|\s*$', line)
            if m: attrib[m.group(1) + '/' + m.group(2)] = (m.group(3).strip(), m.group(4).strip(), sec)
    UPSTREAM = {1: 'the Imperial College London FLT project', 2: 'the Imperial College London FLT project', 3: 'the flt-regular project', 4: 'Mathlib'}
    def_used_by_defs = collections.defaultdict(list)
    for k, d in enumerate(DEFS):
        for j in d['imports_defs']: def_used_by_defs[j].append(k)
    IMPORT_RE = re.compile(r'^(<span class="kn">import</span> )(Definitions\.Def_([A-Za-z0-9_]+)|Theorems\.Thm_([A-Za-z0-9_]+))$')
    MATHLIB_IMPORT_RE = re.compile(r'^(<span class="kn">import</span> )(Mathlib(?:\.[A-Za-z0-9_]+)+)$')
    MATHLIB_DOCS = 'https://leanprover-community.github.io/mathlib4_docs/'
    def mathlib_link(mod):
        return '<a class="ext" href="%s%s.html" title="external link: the mathlib4 documentation for this module (tracks current Mathlib, which may differ from the v4.33.0 this tree uses); nothing is fetched unless you click">%s ↗</a>' % (MATHLIB_DOCS, mod.replace('.', '/'), mod)
    for k, d in enumerate(DEFS):
        stem = d['stem']; rec = defrecs[stem]
        src = open(os.path.join(a.repo, 'Definitions', 'Def_%s.lean' % stem), encoding='utf-8', errors='replace').read()
        dvis = scope_of(src.split('\n'), '', extra_ns=rec['namespaces'])
        hl = hl_lean(src, make_resolver('../', stem, dvis, tops_of(src), None, frozenset(), binder_types(src))).split('\n')
        lines_out = []
        for ln, hline in enumerate(hl, 1):
            mm = MATHLIB_IMPORT_RE.match(hline) if a.mathlib_links else None
            if mm: hline = mm.group(1) + mathlib_link(mm.group(2))
            m = IMPORT_RE.match(hline)
            if m:
                if m.group(3) and m.group(3) in didx: hline = m.group(1) + '<a href="%s.html">%s</a>' % (m.group(3), m.group(2))
                elif m.group(4) and m.group(4) in sidx: hline = m.group(1) + '<a href="../thm.html#%s">%s</a>' % (html.escape(TH[sidx[m.group(4)]]['qual']), m.group(2))
            lines_out.append('<span class="l" id="L%d">%s</span>' % (ln, hline))
        decls = [dd for dd in rec['decls'] if dd.get('qual')]
        idx_html = '<ul class="decl-index">' + ''.join('<li><span class="kw">%s</span><a href="#L%d"><code>%s</code></a></li>' % (dd['kw'], dd['line'], html.escape(dd['qual'])) for dd in decls[:400]) + '</ul>' + ('<p class="muted small">… %d more declarations in the file.</p>' % (len(decls) - 400) if len(decls) > 400 else '')
        used = d['used_in_statements']
        used_sorted = sorted(used, key=lambda i: (-(1 if TH[i]['landmark'] else 0), TH[i]['depth'], TH[i]['qual']))
        used_html = '<ul class="refs">' + ''.join('<li><a class="thm-ref" href="../thm.html#%s">%s<code>%s</code></a> <span class="muted nums">%s below · depth %d</span></li>' % (
            html.escape(TH[i]['qual']), ('<span class="badge lm">landmark</span> ' if TH[i]['landmark'] else '') + (('<span class="t">%s</span> ' % html.escape(titles[TH[i]['qual']])) if TH[i]['qual'] in titles else ''), html.escape(TH[i]['qual']), fmt_int(TH[i]['below']), TH[i]['depth']) for i in used_sorted[:150]) + '</ul>'
        if len(used) > 150: used_html += '<p class="muted small">… and %s more statements (search for the module name to find them).</p>' % fmt_int(len(used) - 150)
        at = attrib.get('Definitions/Def_' + stem)
        en = content.get('Def_' + stem) or content.get('Definitions/Def_%s.lean' % stem) or {}
        body = ['<p class="muted small"><a href="index.html">← all definition modules</a></p>',
                '<h1><code>Definitions/Def_%s.lean</code></h1>' % html.escape(stem),
                '<div class="badges"><span class="badge def">definition module</span>%s%s</div>' % (
                    ''.join('<a class="badge stage" href="../route/index.html">named in %s</a>' % html.escape(s) for s in d['landmark_src']),
                    ('<a class="badge" href="../docs/attribution.html" title="see ATTRIBUTION.md for the copyright holders and authors">adapted from %s%s</a>' % (UPSTREAM.get(at[2], 'an upstream project'), (': ' + html.escape(m_up.group(1))) if (m_up := re.search(chr(96) + r'([^' + chr(96) + r']+)' + chr(96), at[1])) else '') if at else '')),
                (('<h2 class="en-title">%s</h2>' % title_html('Def_' + stem) if ('Def_' + stem) in titles_html or en.get('title') else '') +
                 '<section class="en">%s</section>' % md_inline(en.get('statement') or '', '../', True) +
                 (('<h3>Relation to Mathlib</h3><div class="en-context">%s</div>' % md_inline(en['mathlib'], '../', True)) if en.get('mathlib') else '') +
                 (('<h3>Where it is used</h3><div class="en-context">%s</div>' % md_inline(en['context'], '../', True)) if en.get('context') else '') +
                 (('<h3>References</h3><ol class="refs-lit small">%s</ol>' % ''.join('<li>%s</li>' % (html.escape(str(x)) if ('$' not in str(x) and chr(96) not in str(x)) else re.sub(r'</?p>', '', md_inline(str(x), '../', True)).strip()) for x in en['references'] if x is not None and not isinstance(x, (dict, bool, list))) + (('<p class="muted small">%s</p>' % html.escape(a.references_note)) if a.references_note else '')) if en.get('references') else '') +
                 ('<p class="muted small">%s</p>' % html.escape(a.english_attribution) if a.english_attribution else '')) if en and en.get('statement') else '',
                '<ul class="kv"><li><b>%s</b> lines</li><li><b>%d</b> declarations</li><li>used in the statements of <b>%s</b> theorems and imported by <b>%s</b> proofs</li><li>imports %d definition modules%s</li></ul>' % (
                    fmt_int(d['lines']), d['n_decls'], fmt_int(len(used)), fmt_int(d['used_in_proofs']), len(d['imports_defs']),
                    (', and the statements of %d theorems' % len(d['imports_thms'])) if d['imports_thms'] else ''),
                '<p>Source file: <a href="../../Definitions/Def_%s.lean"><code>Definitions/Def_%s.lean</code></a> <button class="copy small" data-copy="Definitions/Def_%s.lean">copy</button></p>' % (stem, stem, stem)]
        if d['imports_defs'] or def_used_by_defs[k] or d['imports_thms']:
            body.append('<section class="two-col"><div><h2>Imports</h2><ul class="refs defs">%s</ul>%s</div><div><h2>Imported by</h2><ul class="refs defs">%s</ul></div></section>' % (
                ''.join('<li><a href="%s.html"><code>Def_%s</code></a></li>' % (DEFS[j]['stem'], DEFS[j]['stem']) for j in d['imports_defs']) or '<li class="muted">only Mathlib</li>',
                ('<h3>Theorems imported by this definition module</h3><ul class="refs">%s</ul>' % ''.join('<li><a href="../thm.html#%s"><code>%s</code></a></li>' % (html.escape(TH[i]['qual']), html.escape(TH[i]['qual'])) for i in d['imports_thms'])) if d['imports_thms'] else '',
                ''.join('<li><a href="%s.html"><code>Def_%s</code></a></li>' % (DEFS[j]['stem'], DEFS[j]['stem']) for j in def_used_by_defs[k]) or '<li class="muted">no other definition module</li>'))
        body.append('<h2>Declarations</h2>' + idx_html)
        body.append('<h2>Source</h2><div class="src"><pre class="lean">' + '\n'.join(lines_out) + '</pre></div>')
        body.append('<h2>Statements phrased using this module <span class="muted small">(%s)</span></h2>' % fmt_int(len(used)) + (used_html if used else '<p class="muted">No statement module imports it directly%s.</p>' % (' (it is used through other definition modules or by proofs)' if (def_used_by_defs[k] or d['used_in_proofs']) else '')))
        page('def/%s.html' % stem, 'prose', title='Def_' + stem, navkey='def', body='\n'.join(body), mainclass='', after='', katex_js=bool(en and en.get('statement')))
        if en and en.get('statement'): REPORT.setdefault('english_def_pages', []).append(stem)
        if k % 300 == 0: print(f'  def {k}/{len(DEFS)} {time.time()-t0:.0f}s', file=sys.stderr)
    # def index: grouped by first name component
    groups = collections.defaultdict(list)
    for k, d in enumerate(DEFS): groups[d['stem'].split('_')[0]].append(k)
    gl = sorted(groups.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    body = ['<h1>The %s definition modules</h1><p>Ordinary Lean files declaring the structures, predicates and instances the statements are phrased in (Frey packages, Galois representations attached to curves, modularity predicates, modular curves, automorphic forms, deformation data, …). Grouped by the first component of the file name; within a group, the modules most used by theorem statements come first. The modules named in the route documents:</p>' % fmt_int(len(DEFS))]
    named_defs = [k for k, d in enumerate(DEFS) if d['landmark_src']]
    body.append('<ul class="refs defs">' + ''.join('<li><a href="%s.html"><code>Definitions/Def_%s.lean</code></a> <span class="muted nums">statements of %s theorems</span></li>' % (DEFS[k]['stem'], DEFS[k]['stem'], fmt_int(len(DEFS[k]['used_in_statements']))) for k in named_defs) + '</ul>')
    body.append('<p class="toc">' + ' · '.join('<a href="#g-%s">%s</a> <span class="muted small">%d</span>' % (html.escape(g), html.escape(g), len(ks)) for g, ks in gl) + '</p>')
    for g, ks in gl:
        ks.sort(key=lambda k: (-len(DEFS[k]['used_in_statements']), DEFS[k]['stem']))
        body.append('<h2 id="g-%s">%s <span class="muted small">%d modules</span></h2><ul class="refs defs">' % (html.escape(g), html.escape(g), len(ks)) + ''.join(
            '<li><a href="%s.html"><code>Def_%s</code></a> <span class="muted nums">%s lines · statements of %s theorems%s</span></li>' % (DEFS[k]['stem'], DEFS[k]['stem'], fmt_int(DEFS[k]['lines']), fmt_int(len(DEFS[k]['used_in_statements'])), ' · adapted from upstream' if ('Definitions/Def_' + DEFS[k]['stem']) in attrib else '') for k in ks) + '</ul>')
    page('def/index.html', 'prose', title='Definition modules', navkey='def', body='\n'.join(body), mainclass='', after='')
    print(f'defs written {time.time()-t0:.0f}s', file=sys.stderr)
    # ------------------------------------------------------------------ areas (top-level namespaces)
    os.makedirs(os.path.join(out, 'areas'), exist_ok=True)
    by_ns = collections.defaultdict(list)
    for i, t in enumerate(TH): by_ns[t['ns'] or '(no namespace)'].append(i)
    ns_sorted = sorted(by_ns.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    _nsf = {}; _taken = set()
    for ns, _m in ns_sorted:   # largest namespaces first keep the plain name; a later case-insensitive twin gets a suffix
        base = re.sub(r'[^A-Za-z0-9_]+', '_', ns) or '_'
        cand = base; k2 = 2
        while cand.lower() in _taken: cand = '%s_%d' % (base, k2); k2 += 1
        _taken.add(cand.lower()); _nsf[ns] = cand + '.html'
    def ns_file(ns): return _nsf[ns]
    rows = []
    for ns, members in ns_sorted:
        lmk = [i for i in members if TH[i]['landmark']]
        stages = collections.Counter(TH[i]['stage'] for i in members if TH[i]['stage'] is not None)
        top_stage = ', '.join('%s (%s)' % (STAGE_SHORT.get(s, s), fmt_int(c)) for s, c in stages.most_common(2))
        rows.append('<tr><td><a href="%s"><code>%s</code></a></td><td>%s</td><td>%d</td><td class="muted small">%s</td></tr>' % (ns_file(ns), html.escape(ns), fmt_int(len(members)), len(lmk), html.escape(top_stage)))
        members.sort(key=lambda i: (TH[i]['qual'].split('.')[1] if TH[i]['qual'].count('.') >= 2 else '', TH[i]['depth'], TH[i]['qual']))
        groups = collections.OrderedDict()
        for i in members:
            parts = TH[i]['qual'].split('.')
            g = parts[1] if len(parts) >= 3 else '—'
            groups.setdefault(g, []).append(i)
        body = ['<p class="muted small"><a href="index.html">← all areas</a></p><h1>Namespace <code>%s</code> <span class="muted small">%s theorems</span></h1>' % (html.escape(ns), fmt_int(len(members)))]
        if lmk:
            body.append('<p>Landmarks here: ' + ' · '.join('<a href="../thm.html#%s">%s</a>' % (html.escape(TH[i]['qual']), html.escape(titles.get(TH[i]['qual']) or TH[i]['qual'].split('.')[-1])) for i in sorted(lmk, key=lambda i: TH[i]['depth'])) + '</p>')
        if len(groups) > 1:
            body.append('<p class="toc">' + ' · '.join('<a href="#g-%s">%s</a> <span class="muted small">%d</span>' % (html.escape(g), html.escape(g), len(v)) for g, v in groups.items()) + '</p>')
        for g, v in groups.items():
            if len(groups) > 1: body.append('<h2 id="g-%s"><code>%s.%s</code> <span class="muted small">%d</span></h2>' % (html.escape(g), html.escape(ns), html.escape(g), len(v)) if g != '—' else '<h2 id="g-%s">directly in <code>%s</code> <span class="muted small">%d</span></h2>' % (html.escape(g), html.escape(ns), len(v)))
            body.append('<ul class="refs">' + ''.join('<li><a class="thm-ref" href="../thm.html#%s">%s%s<code>%s</code></a> <span class="muted nums">%s below · cited by %d · depth %d</span></li>' % (
                html.escape(TH[i]['qual']), '<span class="badge lm">landmark</span> ' if TH[i]['landmark'] else '', ('<span class="t">%s</span> ' % html.escape(titles[TH[i]['qual']])) if TH[i]['qual'] in titles else '', html.escape(TH[i]['qual']), fmt_int(TH[i]['below']), TH[i]['indeg'], TH[i]['depth']) for i in v) + '</ul>')
        page('areas/' + ns_file(ns), 'prose', title='Namespace ' + ns, navkey='areas', body='\n'.join(body), mainclass='', after='')
    body = '<h1>Areas: the %d top-level namespaces</h1><p>Every theorem, grouped by the first component of its name. The namespace is the nearest thing the tree has to a table of contents by subject: <code>ModularCurve</code> and <code>AlgebraicGeometry</code> carry Mazur\'s argument and the modular-curve infrastructure, <code>CerednikDrinfeld</code> the uniformisation behind level lowering, <code>LanglandsTunnell</code> and <code>AutomorphicForm</code> the automorphic input to modularity, and so on. The "mostly under" column says which step of the route the members sit under (first landmark above them), as a rough guide.</p><table class="plain"><tr><th>namespace</th><th>theorems</th><th>landmarks</th><th>mostly under</th></tr>%s</table>' % (len(ns_sorted), ''.join(rows))
    page('areas/index.html', 'prose', title='Areas', navkey='areas', body=body, mainclass='', after='')
    print(f'areas written {time.time()-t0:.0f}s', file=sys.stderr)
    # ------------------------------------------------------------------ smoke test for a human on another browser
    with open(os.path.join(out, 'SMOKE-TEST.md'), 'w', encoding='utf-8') as fh:
        fh.write("""# Six clicks to check these pages in your browser

The pages were machine-tested in a Chromium browser opened on the files directly (no web server). Safari and
Firefox could not be tested where they were built; these six steps (three minutes) exercise everything:

1. Open 'html/index.html' by double-clicking it. Expected: the statement of the theorem, and on the right a small
   graph of nine green cards. Click the card "%(t_nfp)s".
2. Expected: the theorem page for FreyPackage.no_frey_package, with an informal statement, its Lean statement, a
   "Neighbourhood" graph (a handful of green cards and a violet definition box) and lists "Uses" / "Used by". If the graph box instead shows a sentence
   beginning "The interactive graph needs WebAssembly", everything else still works; note the browser and version.
3. In that graph, click the small "+" on the card "%(t_mod)s". Expected: the graph grows by a few cards.
   Then click the name on any card. Expected: that theorem's page opens.
4. Type  level lowering odd  in the search box at the top. Expected: a drop-down whose first entry is
   FreyPackage.level_lowering_odd_prime_of_conductorLevel; press Enter to open it.
5. Open "Definitions" in the top bar, then "Def_FLTPrelim_FreyPackage". Expected: the file shown with line numbers and
   highlighted keywords; mathematical symbols display correctly; clicking "FreyPackage" inside a later line jumps to the
   line that declares it.
6. On any theorem page, under "Source", click the Theorems/Thm_....lean link. Expected when the html/ folder sits at
   the root of the repository: the browser shows or downloads the Lean file. (If the folder is elsewhere this link
   cannot work; the copy button next to it gives the path to open in your editor.)

Mathematics in the English text should look typeset (e.g. S with a subscript 2, not "$S_2$"). Script and
double-struck letters inside Lean text (𝓞, 𝔭, 𝔽) need a system font with mathematical alphabets; macOS and Windows
have one, some Linux desktops do not (they show boxes; the text is still correct when copied). If any step fails,
the browser name and version and the step number are enough to reproduce it.
""" % dict(t_nfp=titles.get('FreyPackage.no_frey_package', 'FreyPackage.no_frey_package'), t_mod=titles.get('FreyPackage.frey_isModular', 'FreyPackage.frey_isModular')))
    # ------------------------------------------------------------------ index + about
    readme = open(os.path.join(a.repo, 'README.md'), encoding='utf-8').read()
    m = re.search(r'~~~lean\n(theorem fermat_last_theorem.*?)\n~~~', readme, re.S)
    stmt = m.group(1) if m else TH[G['root']]['qual']
    m2 = re.search(r'~~~lean\n(/-- info: .fermat_last_theorem. depends on axioms.*?)\n~~~', readme, re.S)
    axioms = m2.group(1) if m2 else ''
    ns = G['namespaces'][:14]
    numbers = [(fmt_int(N), 'theorems, each with a statement file and a proof file'), (fmt_int(len(DEFS)), 'definition modules'), (fmt_int(G['n_edges']), 'citation edges between theorems'),
               (str(G['max_depth']), 'deepest shortest path from the theorem'), (str(G['height_root']), 'longest citation chain'), (fmt_int(G['leaves']), 'theorems proved from Mathlib and definitions alone'),
               (fmt_int(len(LM)), 'landmark theorems named in the route documents')]
    chapters_html = '<div class="cards">' + ''.join('<div class="card"><h3><span class="stage-num">%d</span><a href="route/%s">%s</a></h3><p class="num">%d named theorem%s</p></div>' % (ch['num'], ch['file'], html.escape(ch['title']), len(ch['named']), '' if len(ch['named']) == 1 else 's') for ch in chapters) + '</div>'
    body = """
<div class="hero"><div class="stmt">
<h1>Fermat's Last Theorem, proved in Lean 4</h1>
<p class="muted">A reader's guide to the tree: what is proved, by which route, and how the %(N)s theorems hang together. Every name links to a page with the exact Lean statement, what it cites, what cites it, and its place under the theorem.</p>
<pre class="lean">%(stmt)s</pre>
<p class="small">The default build target <a href="../FinalCheck.lean"><code>FinalCheck.lean</code></a> makes the build fail unless the proof rests on exactly Lean's three standard axioms:</p>
<pre class="lean">%(axioms)s</pre>
<p><a class="badge root" href="thm.html#fermat_last_theorem">open the theorem's page →</a> <a class="badge" href="route/index.html">the route, step by step</a> <a class="badge" href="dag/index.html">landmark graph</a> <a class="badge" href="docs/readme.html">README</a></p>
</div>
<div><div class="figure">%(top_svg)s<div class="caption">The top of the proof. Each small square is one proof step: the theorem below it is proved from exactly the premises above it (these are the <code>import Theorems.Thm_…</code> lines of its proof module). <code>FreyPackage.no_frey_package</code> combines irreducibility, modularity, level lowering and the vanishing of S₂(Γ₀(2)) into a contradiction. Click any card.</div></div></div></div>
<h2>The route</h2>
<p>The argument is that of Frey, Serre, Ribet, Wiles and Taylor–Wiles, largely as in Darmon–Diamond–Taylor, run as a proof by contradiction. The chapters below reproduce the project's route document %(docset)s, one page per step, each followed by the exact statements of the theorems it names. Named classical theorems are proved in the strength the argument needs; <a href="route/s7.html">§7</a> says exactly what that is.</p>
%(chapters)s
<h2>The numbers</h2><div class="numbers-grid">%(numbers)s</div>
<p class="small muted">Largest namespaces by number of theorems: %(ns)s.</p>
<h2>How to use these pages</h2>
<ul>
<li><b>Search</b> (top of every page) matches any part of a theorem name, %(title_cov)s, a definition-module name, or a declaration inside a definition module. Landmarks rank first.</li>
<li>A <b>theorem page</b> (<code>thm.html#Name</code>) shows the statement as written in <code>Theorems/Thm_….lean</code> with the preamble removed, %(en_cov)sthe theorems its proof cites and the proofs that cite it, the definition modules it is phrased in, one shortest citation path up to <code>fermat_last_theorem</code>, an expandable neighbourhood graph, and the closing <code>solution</code> declaration of the proof file. Links to the <code>.lean</code> files work when this <code>html/</code> folder sits at the root of the repository.</li>
<li><b>Definition pages</b> show each <code>Definitions/Def_….lean</code> in full with an index of its declarations and the statements that use it.</li>
%(docs_li)s
<li>Conventions, from the documents: <i>proved</i> always means a kernel-checked proof of exactly the quoted type from <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>, never that the classical theorem of the same name holds in its usual generality; <i>below T</i> means in the import closure of T's proof module.</li>
</ul>
""" % dict(N=fmt_int(N), stmt=hl_lean(stmt, make_resolver('', None, (), tops_of(stmt), 'fermat_last_theorem', bound_names(stmt), binder_types(stmt))), axioms=hl_lean(axioms), top_svg=top_svg_index, chapters=chapters_html,
           docset=('(part of its documentation set, all of which is under <a href="docs/index.html">Documents</a>)' if a.include_docs
                   else '(the repository\'s own documents are under <a href="docs/index.html">Documents</a>)'),
           docs_li=('<li>The <a href="docs/index.html">documents</a> are the repository\'s prose (README, overview, structure, verification, limitations, attribution), rendered as written; read <a href="docs/structure.html">structure</a> once for the file conventions (<code>Thm_</code>/<code>S_</code>/<code>Def_</code>, <code>p2m_exact_reverting</code>, the <code>attribute [-instance]</code> preambles).</li>' if a.include_docs
                    else '<li>The <a href="docs/index.html">documents</a> are the repository\'s prose (README and attribution; <code>PROOF-PATH.md</code> opens the <a href="route/index.html">route</a>), rendered as written; <a href="about.html">About</a> states the file conventions (<code>Thm_</code>/<code>S_</code>/<code>Def_</code>, <code>p2m_exact_reverting</code>, the <code>attribute [-instance]</code> preambles).</li>'),
           title_cov=('its English title' if len(titles) >= 0.98 * N else 'an English title where one exists'),
           en_cov=('an informal English statement and context paragraph (a reading aid; the Lean is what is proved), ' if REPORT.get('english', {}).get('theorem_records', 0) >= 0.98 * N else ('an informal English statement where one exists, ' if REPORT.get('english', {}).get('theorem_records', 0) else '')),
           numbers=''.join('<div><b>%s</b><span>%s</span></div>' % (n, html.escape(l)) for n, l in numbers),
           ns=', '.join('<code>%s</code> %s' % (html.escape(n), fmt_int(c)) for n, c in ns))
    page('index.html', 'prose', title='Overview', navkey='index', body=body, mainclass='', after='')
    gen_date = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%d')
    n_unused = sum(1 for i in range(N) for c in cite_uses[i] if c == 0)
    n_cite_only = G.get('n_cite_only')
    if n_cite_only != TH[G['root']]['below'] + 1: raise SystemExit('inconsistent reach counts: citation-BFS %s vs below(root)+1 %s' % (n_cite_only, TH[G['root']]['below'] + 1))
    n_other = N - n_cite_only
    n_other_direct = sum(1 for t in TH if t['parent_kind'] and t['parent_kind'] != 'cites')
    about = """<h1>About these pages</h1>
<p>These pages document %(stamp)s (%(toolchain)s). They were generated on %(date)s by a script that reads the <code>.lean</code> files as text; no Lean was run to produce them. Consequences worth knowing:</p>
<ul>
<li><b>Statements are quoted textually</b> from <code>Theorems/Thm_….lean</code> (the declaration up to <code>:= by p2m_exact_reverting …</code>), with any leading licence header, the <code>import</code> lines and the generated <code>attribute [-instance] …</code> / <code>attribute [-simp] …</code> preamble removed and the remaining context lines (<code>open</code>, <code>variable</code>, <code>universe</code>, <code>set_option</code>, local notation) shown above the statement. They are not pretty-printed by Lean, so notation is exactly as the file spells it.</li>
<li><b>Edges are imports.</b> "T cites U" means the proof module <code>P2M/Sol/S_T.lean</code> has the line <code>import Theorems.Thm_U</code>. By the construction of the tree these are the theorems the proof uses, but an import is an upper bound on logical dependence: for %(n_unused)s of the %(n_edges)s citation edges (%(pct_unused)s) the cited theorem's name does not occur textually in the importing proof (it may still be used through an instance or notation, or not at all); theorem pages mark those citations.</li>
<li><b>"Below T"</b> counts the distinct theorems in the import closure of T's proof module, as in the repository's documents. <b>Depth</b> is the length of a shortest citation path from <code>fermat_last_theorem</code>; %(n_cite_only)s of the %(N)s theorems have one. The other %(n_other)s lie outside the citation closure of the final theorem: %(n_other_direct)s are cited by no proof and are reached through a definition module that imports them (or a statement that mentions them), the remaining %(n_other_rest)s only through those; their path says so.</li>
<li><b>Proof sizes</b> count the lines of the proof module after its import and preamble lines; <b>helpers</b> counts the <code>theorem</code>/<code>lemma</code> declarations in the proof module other than <code>solution</code>. Helpers are file-local and machine-named; they are not presented as library lemmas.</li>
<li><b>Landmarks</b> are the %(nlm)d theorems whose names occur in <code>PROOF-PATH.md</code> or in %(lm_docs)s. The step printed on other theorem pages ("under: …") is the step of the first landmark met going up one shortest path; it is a reading aid, not a classification.</li>
<li><b>Identifier links</b> inside statements are resolved textually against the declarations of the definition modules: an exact qualified name; a bare or partly qualified name completed through the statement's <code>open</code> lines or its own namespace; or field notation <code>x.foo</code> whose suffix names exactly one project constant in a visible namespace. An unlinked name is Mathlib's, a bound variable, or one the rule declined to guess.</li>
<li><b>The Lean 4.33 port.</b> 28 statement files were edited by hand when the tree was carried from Lean 4.30 to 4.33 and 52 import <code>Def_Compat_Mathlib430</code>; their pages carry %(port_badge)s. The 1,366 statements changed only by scripted token renames (e.g. <code>ramificationIdx</code> → <code>ramificationIdx'</code>) are not badged.</li>
<li>The English titles, informal statements, proof ideas and context paragraphs (%(en_cov)s) are editorial additions kept outside the Lean files; the Lean statement on the same page is what is proved.%(ennote)s The mathematics in that English text is typeset in your browser by a bundled copy of KaTeX; with scripts disabled, or if a formula does not parse, you see its TeX source instead.%(refnote)s</li>
<li>Everything is proved: there are no conjectural or incomplete nodes, so the graphs use one colour. Boxes with a folded corner are definition modules.</li>
</ul>
<h2>Using the folder</h2>
<p>Open <code>html/index.html</code> in a browser; no server is needed and nothing is fetched from the network. All links are relative. The links to <code>.lean</code> source files assume the folder sits at the root of the repository (next to <code>Theorems/</code>, <code>P2M/</code>, <code>Definitions/</code>); everything else works wherever the folder is. The interactive neighbourhood graphs use Graphviz compiled to WebAssembly (bundled); if a browser refuses to run it from a local file, the page says so and the lists carry the same information. Tested with a Chromium-based browser; the pages use only long-standing web features (classic scripts, SVG, no modules or network requests) so that Firefox and Safari behave the same from disk.</p>
<h2>Third-party material</h2>
<p>Graph layout: Graphviz via @hpcc-js/wasm (Apache-2.0). Mathematics typesetting: KaTeX (MIT; fonts SIL OFL 1.1). Licence texts are in <code>assets/vendor/</code>. The Lean files' own attribution is in <a href="docs/attribution.html">ATTRIBUTION.md</a>.</p>
""" % dict(stamp=(stamp + ' of the tree') if is_hash else stamp, toolchain=html.escape(toolchain), date=gen_date, nlm=len(LM), N=fmt_int(N),
           lm_docs=('the project\'s route and overview documents (reproduced under <a href="docs/index.html">Documents</a>; your copy of the tree carries <code>README.md</code>, <code>PROOF-PATH.md</code> and <code>ATTRIBUTION.md</code>, not the <code>docs/</code> folder)' if a.include_docs
                    else 'the <a href="route/index.html">route</a> chapters'),
           port_badge=('a badge linking to the <a href="docs/port-lean433.html#port-5-2">port notes</a>' if a.include_docs else 'a badge saying so'),
           n_unused=fmt_int(n_unused), n_edges=fmt_int(G['n_edges']), pct_unused='%.1f%%' % (100.0 * n_unused / max(1, G['n_edges'])),
           n_cite_only=fmt_int(n_cite_only), n_other=fmt_int(n_other), n_other_direct=fmt_int(n_other_direct), n_other_rest=fmt_int(n_other - n_other_direct),
           ennote=(' Each such page carries the note <i>%s</i>' % html.escape(a.english_attribution.rstrip('.') + '.')) if a.english_attribution else '',
           en_cov=('on every theorem page and every definition-module page' if REPORT.get('english', {}).get('theorem_records', 0) == N and len(REPORT.get('english_def_pages', [])) == len(DEFS)
                   else 'on %s of the %s theorem pages and %s of the %s definition-module pages' % (fmt_int(REPORT.get('english', {}).get('theorem_records', 0)), fmt_int(N), fmt_int(len(REPORT.get('english_def_pages', []))), fmt_int(len(DEFS)))),
           refnote=(' ' + html.escape(a.references_note)) if a.references_note else '')
    page('about.html', 'prose', title='About these pages', navkey='about', body=about, mainclass='prose', after='')
    with open(os.path.join(out, 'MANIFEST.txt'), 'w') as fh:
        fh.write('Reader\'s documentation for the Lean 4 proof of Fermat\'s Last Theorem.\nDocuments %s (%s). Generated %s.\nOpen index.html in a browser. Place this folder at the repository root for the .lean source links to resolve.\n%d theorem records, %d definition pages.\n' % (stamp_txt, toolchain, gen_date, N, len(DEFS)))
    total_bytes = 0
    for root_, dirs_, files_ in os.walk(out):
        for fn in files_: total_bytes += os.path.getsize(os.path.join(root_, fn))
    with open(os.path.join(out, 'README-DOCS.md'), 'w', encoding='utf-8') as fh:
        fh.write("""# Reader's documentation for the Lean 4 proof of Fermat's Last Theorem

This folder is a set of static web pages describing %(stamp)s (%(toolchain)s): the statement and
its axiom check, the route of the proof step by step, a page for each of the %(N)s theorems (exact Lean statement,
what its proof cites and what cites it, its place under the final theorem, an expandable neighbourhood graph, the
proof's closing lines), a page for each of the %(ndef)s definition modules (full highlighted source, declaration
index, which statements use it), the landmark theorems as a graph, the theorems grouped by namespace, and the
repository's own prose documents rendered with cross-links.

## How to open it

1. This 'html/' folder ships at the root of the repository, next to 'Theorems/', 'P2M/' and 'Definitions/'; if you
   received it as a separate archive, unpack it there. (Anywhere else also works; only the links to the raw .lean
   files need that position.)
2. Open 'html/index.html' in a web browser. No web server and no network connection are needed; nothing is fetched
   from the internet. The few links that leave the folder (the Mathlib documentation for an imported module, the
   upstream projects named in ATTRIBUTION.md) are marked and are only followed if you click them.
3. The pages were machine-tested in a Chromium-based browser only. 'SMOKE-TEST.md' lists six clicks that exercise
   everything; if you use Safari or Firefox, please run through it once (three minutes).

## What is quoted and what is generated

* Lean text (statements, definition modules, proof excerpts) is quoted byte-for-byte from the .lean files described
  above, with the import lines, the generated 'attribute [-instance] …' preambles and (on theorem pages) any leading
  licence header left out.
* Dependency information is read off the import lines: a proof module's 'import Theorems.Thm_…' lines are the
  theorems it cites. Counts ('theorems below', depth, proof lines, helper lemmas) are computed from the files.
* %(docsline)s
* English titles, informal statements, proof ideas and context paragraphs (on %(n_en_thm)s theorem pages and
  %(n_en_def)s definition-module pages) are editorial additions kept outside the Lean files.%(ennote)s
  Their mathematics is typeset in the browser by the bundled KaTeX (assets/vendor/katex/katex.min.js).%(refnote)s
* 'About these pages' (about.html) states the conventions and the limits of a textual reading of the tree.

Size: about %(mb)d MB unpacked, %(nfiles)s files. Generated %(date)s.
""" % dict(stamp=stamp_txt, toolchain=toolchain, N=fmt_int(N), ndef=fmt_int(len(DEFS)), ennote=(' Each such page\n  carries the note "%s".' % a.english_attribution.rstrip('.')) if a.english_attribution else '', mb=total_bytes // 1000000, nfiles=fmt_int(sum(len(f) for _, _, f in os.walk(out))), date=gen_date,
           n_en_thm=fmt_int(REPORT.get('english', {}).get('theorem_records', 0)), n_en_def=fmt_int(len(REPORT.get('english_def_pages', []))),
           refnote=('\n  ' + a.references_note) if a.references_note else '',
           docsline=("The documents under 'Documents' and the route chapters are the repository's Markdown files rendered as written." if a.include_docs
                     else "The documents under 'Documents' are the repository's README.md and ATTRIBUTION.md rendered as written; the route\n  chapters render PROOF-PATH.md ('The route in brief') and the project's longer route document, which is not itself a\n  file of the repository.")))
    # file names must be unique case-insensitively (the folder will be unpacked on macOS / Windows),
    # and no single file may be large (the check below refuses files over 4.5 MB)
    seen_ci = {}
    for root_, dirs_, files_ in os.walk(out):
        for fn in files_:
            full = os.path.join(root_, fn); pth = os.path.relpath(full, out).lower()
            if pth in seen_ci: raise SystemExit('case-insensitive file name collision: %s' % pth)
            seen_ci[pth] = 1
            if os.path.getsize(full) > 4_500_000: raise SystemExit('output file too large (%d bytes > 4.5 MB): %s' % (os.path.getsize(full), pth))
    if LINK_WARNINGS: print('links neutralised (target absent from the documented tree): ' + ', '.join(sorted(set(LINK_WARNINGS))), file=sys.stderr)
    REPORT['files'] = {'count': len(seen_ci), 'largest': sorted(((os.path.getsize(os.path.join(r_, f_)), os.path.relpath(os.path.join(r_, f_), out)) for r_, d_, fs_ in os.walk(out) for f_ in fs_), reverse=True)[:8]}
    REPORT['english_def_pages'] = len(REPORT.get('english_def_pages', []))
    REPORT['math']['unchecked_fragments'] = len(MATH_UNSEEN)
    json.dump(REPORT, open(REPORT_PATH, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
    if MATH_UNSEEN:   # a fragment reached a page without passing through the KaTeX check: by construction this cannot happen; if it does, stop
        print(f'katex: {len(MATH_UNSEEN)} fragments were emitted without having been checked: {list(MATH_UNSEEN)[:5]}', file=sys.stderr)
        if a.tex_errors == 'fail': sys.exit('unchecked TeX fragments reached the output (see above); this is a generator bug — do not ship this folder')
    print(f'all written {time.time()-t0:.0f}s; numbers in {REPORT_PATH}', file=sys.stderr)

if __name__ == '__main__':
    main()
