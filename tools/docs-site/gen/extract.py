#!/usr/bin/env python3
"""Stage 1: stream the Lean tree (read-only) and write build-time JSONL records.

Outputs (in <build>/):
  thm.jsonl   one record per statement module Theorems/Thm_<stem>.lean:
              {stem, qual, kw, is_dup, namespaces, context[], decl, univs, aux_decls[], trailer[],
               imports:{mathlib[], defs[], thms[], other[]}, lines, bytes}
  sol.jsonl   one record per proof module P2M/Sol/S_<stem>.lean:
              {stem, cites[] (Thm stems imported), defs[], mathlib_imports:int, lines, content_lines,
               helpers:int (file-local theorem/lemma decls other than 'solution'), defs_local:int,
               print_axioms:int, solution_tail (text from the last column-0 'theorem solution' to EOF, capped)}
  def.jsonl   one record per Definitions/Def_<stem>.lean:
              {stem, imports:{defs[], thms[], mathlib[], other[]}, lines, bytes, decls:[{kw, name, line, ns}],
               namespaces[], has_copyright:bool}
The statement parser follows the three rules that made it total on this tree: find the
'p2m_exact_reverting' tail first and walk back to the nearest column-0 theorem/lemma; qualify the name with the
enclosing namespaces and strip 'P2M.Dup.' / explicit universes; keep what follows the tail as trailer.
Nothing here holds more than one file in memory. stdlib only.
"""
import os, re, sys, json, time, collections

def header_len(text):
    """Number of lines of a leading '/- ... -/' licence header, if present, else 0."""
    if not text.startswith('/-\n'): return 0
    i = text.find('\n-/\n')
    return text[:i + 4].count('\n') if i >= 0 else 0

def main(repo, build):
    os.makedirs(build, exist_ok=True)
    THM = os.path.join(repo, 'Theorems'); SOL = os.path.join(repo, 'P2M', 'Sol'); DEF = os.path.join(repo, 'Definitions')
    t0 = time.time()
    stats = collections.Counter(); fails = collections.defaultdict(list)
    def fail(k, n, d=''):
        stats['fail_' + k] += 1
        if len(fails[k]) < 20: fails[k].append({'name': n, 'detail': d[:300]})

    # ---------------- statements
    TAIL = re.compile(r':=\s*by\s+p2m_exact_reverting\s+@?_root_\.P2MW\.(S_[^\s.]+)\.solution\b')
    MODS = r'(?:@\[[^\]]*\]\s*)*(?:(?:protected|private|noncomputable|nonrec|unsafe)\s+)*'
    DECL_START = re.compile(r'^' + MODS + r'(theorem|lemma)\b')
    AUX = re.compile(r'^' + MODS + r'(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b')
    HEAD = re.compile(r'^' + MODS + r'(theorem|lemma)\s+([^\s{(\[:]+?)(\.\{[^}]*\})?(?=[\s{(\[:])', re.S)
    thm_stems = sorted(f[4:-5] for f in os.listdir(THM) if f.startswith('Thm_') and f.endswith('.lean'))
    out = open(os.path.join(build, 'thm.jsonl'), 'w')
    qual_of = {}
    for n in thm_stems:
        p = os.path.join(THM, f'Thm_{n}.lean')
        raw = open(p, encoding='utf-8').read()
        lines = raw.split('\n')[header_len(raw):]   # the licence header is not part of the statement's context
        imports = [l.split()[1] for l in lines if l.startswith('import ')]
        body = [l for l in lines if not l.startswith('import ') and not l.startswith('attribute [-')]
        ti = next((i for i, l in enumerate(body) if TAIL.search(l)), None)
        if ti is None: fail('no_tail', n); continue
        di = next((i for i in range(ti, -1, -1) if DECL_START.match(body[i])), None)
        if di is None: fail('no_decl', n); continue
        context = [l for l in body[:di] if l.strip()]
        aux_decls = [l for l in context if AUX.match(l)]
        rest = '\n'.join(body[di:])
        m = TAIL.search(rest)
        decl_text = rest[:m.start()].rstrip()
        trailer = [l for l in rest[m.end():].split('\n') if l.strip()]
        mh = HEAD.match(decl_text)
        if not mh: fail('head_parse', n, decl_text[:200]); continue
        kw, short, univs = mh.group(1), mh.group(2), mh.group(3)
        ns = []
        for l in context:
            w = l.split()
            if w[0] == 'namespace': ns.append(w[1])
            elif w[0] == 'end' and len(w) > 1 and ns and ns[-1] == w[1]: ns.pop()
        is_dup = short.startswith('P2M.Dup.')
        base = short[len('P2M.Dup.'):] if is_dup else short
        qual = base[len('_root_.'):] if base.startswith('_root_.') else ('.'.join(ns + [base]) if ns else base)
        if qual.replace('.', '_') != n: stats['qual_ne_stem'] += 1
        qual_of[n] = qual
        if m.group(1) != 'S_' + n: fail('solref_mismatch', n, m.group(1))
        imps = {'mathlib': [i for i in imports if i.startswith('Mathlib')],
                'defs': [i[16:] for i in imports if i.startswith('Definitions.Def_')],
                'thms': [i[13:] for i in imports if i.startswith('Theorems.Thm_')],
                'other': [i for i in imports if not i.startswith(('Mathlib', 'Definitions.', 'Theorems.', 'P2M.Sol.'))]}
        out.write(json.dumps({'stem': n, 'qual': qual, 'kw': kw, 'is_dup': is_dup, 'namespaces': ns, 'context': context,
                              'decl': decl_text, 'univs': univs, 'aux_decls': aux_decls, 'trailer': trailer, 'imports': imps,
                              'lines': len(lines), 'bytes': len(raw.encode('utf-8'))}, ensure_ascii=False) + '\n')
        stats['thm_ok'] += 1
    out.close()
    print(f'statements: {stats["thm_ok"]}/{len(thm_stems)} in {time.time()-t0:.0f}s', file=sys.stderr)

    # ---------------- proofs (streamed line by line)
    SOLDECL = re.compile(r'^' + MODS + r'(theorem|lemma)\s+(?:_root_\.P2MW\.S_[^\s.]+\.)?solution\b')
    HELPER = re.compile(r'^\s*' + MODS + r'(theorem|lemma)\s')
    LOCALDEF = re.compile(r'^\s*' + MODS + r'(def|abbrev|instance|structure|class|inductive)\s')
    TAILCAP = 3500; TAILLINES = 40   # show how the cited theorems combine; long tactic blocks are cut with a pointer to the file
    out = open(os.path.join(build, 'sol.jsonl'), 'w')
    sol_stems = sorted(f[2:-5] for f in os.listdir(SOL) if f.startswith('S_') and f.endswith('.lean'))
    for k, n in enumerate(sol_stems):
        p = os.path.join(SOL, f'S_{n}.lean')
        imports = []; nlines = 0; content = 0; helpers = 0; ldefs = 0; pax = 0
        tail = None; tail_len = 0; tail_trunc = False; sol_decls = 0; tail_line = 0; tail_total = 0
        with open(p, encoding='utf-8', errors='replace') as fh:
            text = fh.read()
        if True:
            # 'theorem' alone on a line with 'solution' on the next: join them so the declaration is recognised
            text = re.sub(r'(?m)^((?:@\[[^\]]*\]\s*)*(?:(?:protected|private|noncomputable|nonrec|unsafe)\s+)*(?:theorem|lemma))\s*\n\s*((?:_root_\.P2MW\.S_[^\s.]+\.)?solution\b)', r'\1 \2', text)
            hlen = header_len(text)   # licence header: counted in line numbers, not as proof content
            for line in text.splitlines(keepends=True):
                nlines += 1
                if nlines <= hlen: continue
                if line.startswith('import '):
                    imports.append(line.split()[1]); continue
                if line.startswith('attribute [-'): continue
                if line.strip(): content += 1
                if line.startswith('#print axioms'): pax += 1
                if SOLDECL.match(line):
                    sol_decls += 1; tail = [line]; tail_len = len(line); tail_trunc = False; tail_line = nlines; tail_total = 1; continue
                if tail is not None:
                    tail_total += 1
                    if tail_len < TAILCAP and len(tail) < TAILLINES and not tail_trunc: tail.append(line); tail_len += len(line)
                    else: tail_trunc = True
                    # a later helper after 'solution' is unusual but keep counting
                if HELPER.match(line): helpers += 1
                elif LOCALDEF.match(line): ldefs += 1
        if sol_decls == 0: stats['sol_no_solution_line'] += 1
        cites = [i[13:] for i in imports if i.startswith('Theorems.Thm_')]
        # how often each cited theorem's short name occurs in the proof text (0 = imported but not textually cited)
        body_start = text.find('\nnamespace ')
        body = text[body_start:] if body_start >= 0 else text
        uses = []
        for c in cites:
            q = qual_of.get(c, c); short = q.rsplit('.', 1)[-1]
            uses.append(len(re.findall(r'(?<![A-Za-z0-9_.\'])(?:[A-Za-z0-9_.\']*\.)?' + re.escape(short) + r'(?![A-Za-z0-9_\'])', body)))
        rec = {'stem': n, 'cites': cites, 'cite_uses': uses,
               'defs': [i[16:] for i in imports if i.startswith('Definitions.Def_')],
               'mathlib_imports': sum(1 for i in imports if i.startswith('Mathlib')),
               'lines': nlines, 'content_lines': content, 'helpers': helpers, 'defs_local': ldefs, 'print_axioms': pax,
               'solution_line': tail_line, 'solution_lines_total': tail_total, 'solution_tail': (''.join(tail).rstrip() if tail else None), 'solution_tail_truncated': tail_trunc}
        out.write(json.dumps(rec, ensure_ascii=False) + '\n')
        if k % 10000 == 0: print(f'  sol {k}/{len(sol_stems)} {time.time()-t0:.0f}s', file=sys.stderr)
    out.close()
    print(f'proofs: {len(sol_stems)} in {time.time()-t0:.0f}s; no-solution-line {stats["sol_no_solution_line"]}', file=sys.stderr)

    # ---------------- definitions
    DDECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:protected|private|noncomputable|scoped|nonrec|unsafe)\s+)*(structure|class inductive|class|inductive|def|abbrev|instance|theorem|lemma|opaque|axiom)\s+([^\s:({\[]*)')
    out = open(os.path.join(build, 'def.jsonl'), 'w')
    def_stems = sorted(f[4:-5] for f in os.listdir(DEF) if f.startswith('Def_') and f.endswith('.lean'))
    for n in def_stems:
        p = os.path.join(DEF, f'Def_{n}.lean')
        raw = open(p, encoding='utf-8', errors='replace').read()
        lines = raw.split('\n')
        imports = [l.split()[1] for l in lines if l.startswith('import ')]
        decls = []; ns = []; namespaces = []
        cur_struct = None   # (qual, indent) while inside a structure/class body: its fields become '<qual>.<field>' declarations
        FIELD = re.compile(r"^(\s+)\(?([a-zA-Z_][A-Za-z0-9_'!?₀-₉]*)\s*(?:[:({\[⦃]|$)")
        NOT_FIELD = {'deriving', 'with', 'extends', 'where', 'fun', 'by', 'let', 'have', 'show', 'if', 'then', 'else', 'match', 'do', 'mk'}
        for i, l in enumerate(lines, 1):
            w = l.split()
            if not w: continue
            if cur_struct is not None:
                if not l[:1].isspace():
                    cur_struct = None
                else:
                    fm = FIELD.match(l)
                    if fm and fm.group(2) not in NOT_FIELD and not l.lstrip().startswith(('--', '/-', '|')):
                        decls.append({'kw': 'field', 'name': fm.group(2), 'qual': cur_struct + '.' + fm.group(2), 'line': i})
                    continue
            if w[0] == 'namespace' and len(w) > 1:
                ns.append(w[1]); namespaces.append('.'.join(ns)); continue
            if w[0] == 'end' and len(w) > 1 and ns and ns[-1] == w[1]: ns.pop(); continue
            m = DDECL.match(l)
            if m:
                kw, name = m.group(1), m.group(2)
                if name.startswith('_root_.'): q = name[7:]
                elif kw == 'instance' and not name: q = ''
                else: q = '.'.join(ns + [name]) if ns and name else name
                d = {'kw': kw, 'name': name, 'qual': q, 'line': i}
                if kw in ('structure', 'class', 'class inductive'):
                    em = re.search(r'\bextends\s+(.+?)(?:\s+where\b|\s*:=|$)', l)
                    if em:
                        d['extends'] = [x.strip().split(' ')[0] for x in re.split(r',', re.sub(r'\([^)]*\)', '', em.group(1))) if x.strip()]
                    if q: cur_struct = q
                decls.append(d)
        imps = {'mathlib': [i for i in imports if i.startswith('Mathlib')],
                'defs': [i[16:] for i in imports if i.startswith('Definitions.Def_')],
                'thms': [i[13:] for i in imports if i.startswith('Theorems.Thm_')],
                'other': [i for i in imports if not i.startswith(('Mathlib', 'Definitions.', 'Theorems.'))]}
        out.write(json.dumps({'stem': n, 'imports': imps, 'lines': len(lines), 'bytes': len(raw.encode('utf-8')), 'decls': decls,
                              'namespaces': sorted(set(namespaces)), 'has_copyright': 'Copyright' in raw[:600],
                              'axiom_count': sum(1 for d in decls if d['kw'] == 'axiom')}, ensure_ascii=False) + '\n')
    out.close()
    stats['elapsed_s'] = round(time.time() - t0, 1)
    json.dump({'stats': dict(stats), 'fails': fails}, open(os.path.join(build, 'extract_stats.json'), 'w'), indent=1, ensure_ascii=False)
    print(json.dumps(dict(stats)), file=sys.stderr)
    if any(k.startswith('fail_') for k in stats):
        print('WARNING: extraction failures, see extract_stats.json', file=sys.stderr)

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
