#!/usr/bin/env python3
"""Stage 2: graph metrics over the citation DAG, landmark selection, route stages.

Reads <build>/{thm,sol,def}.jsonl and the route prose (docs/route.md, PROOF-PATH.md); writes <build>/graph.json:
  theorems: list (index = node id) of {qual, stem, indeg, outdeg, depth, below, parent, via, stage, landmark, ns}
  cites:    list of lists (node -> cited theorem ids, in import order)
  defs, landmark list, landmark DAG edges, route stages, global numbers.
'below' = number of distinct theorems in the import closure of the node's proof module (docs/README's "below T"),
computed exactly with integer bitsets in reverse topological order.
"""
import os, re, sys, json, time, collections
from collections import deque

ROOT = 'fermat_last_theorem'
BT = chr(96)
TICK = re.compile(BT + r"([A-Za-z_][A-Za-z0-9_.']*)" + BT)

def load_jsonl(p):
    with open(p, encoding='utf-8') as fh:
        for line in fh:
            yield json.loads(line)

def route_sections(route_md):
    secs = []; cur = None
    for line in route_md.split('\n'):
        m = re.match(r'^## (\d+)\.\s+(.*)', line)
        if m:
            cur = [int(m.group(1)), m.group(2).strip(), []]; secs.append(cur); continue
        if cur is not None: cur[2].append(line)
    return [(n, t, '\n'.join(b)) for n, t, b in secs]

def main(build, repo, docs):
    t0 = time.time()
    thms = list(load_jsonl(os.path.join(build, 'thm.jsonl')))
    stems = [t['stem'] for t in thms]
    idx = {s: i for i, s in enumerate(stems)}
    qidx = {t['qual']: i for i, t in enumerate(thms)}
    N = len(thms)
    defs = list(load_jsonl(os.path.join(build, 'def.jsonl')))
    dstems = [d['stem'] for d in defs]; didx = {s: i for i, s in enumerate(dstems)}
    cites = [[] for _ in range(N)]; cite_uses = [[] for _ in range(N)]
    solinfo = {}; sol_defs = [[] for _ in range(N)]
    unmatched_sol = []; unmatched_cite = []
    for s in load_jsonl(os.path.join(build, 'sol.jsonl')):
        i = idx.get(s['stem'])
        if i is None: unmatched_sol.append(s['stem']); continue
        unmatched_cite.extend(c for c in s['cites'] if c not in idx)
        seen = set(); cl = []; cu = []
        for k, c in enumerate(s['cites']):
            j = idx.get(c)
            if j is not None and j not in seen and j != i:
                seen.add(j); cl.append(j); cu.append(s.get('cite_uses', [None] * len(s['cites']))[k])
        cites[i] = cl; cite_uses[i] = cu
        solinfo[i] = {k: s[k] for k in ('lines', 'content_lines', 'helpers', 'defs_local', 'print_axioms', 'solution_line', 'solution_tail_truncated')}
        sol_defs[i] = [didx[d] for d in s['defs'] if d in didx]
    if unmatched_sol or unmatched_cite:
        raise SystemExit(f'proof modules without a statement: {unmatched_sol[:5]} ({len(unmatched_sol)}); cited stems without a statement: {unmatched_cite[:5]} ({len(unmatched_cite)})')
    if len(solinfo) != N: raise SystemExit(f'{N - len(solinfo)} statements have no proof module record')
    cited_by = [[] for _ in range(N)]
    for i in range(N):
        for j in cites[i]: cited_by[j].append(i)
    indeg = [len(cited_by[i]) for i in range(N)]
    outdeg = [len(cites[i]) for i in range(N)]
    stmt_thm = {i: [idx[x] for x in t['imports']['thms'] if x in idx] for i, t in enumerate(thms) if t['imports']['thms']}
    def_thm = {d['stem']: [idx[x] for x in d['imports']['thms'] if x in idx] for d in defs if d['imports']['thms']}
    thm_defs = [sorted(set(didx[d] for d in t['imports']['defs'] if d in didx)) for t in thms]
    def_imports_def = [[didx[x] for x in d['imports']['defs'] if x in didx] for d in defs]
    root = qidx[ROOT]
    depth = [-1] * N; parent = [-1] * N; parent_kind = [''] * N
    depth[root] = 0
    # phase 1: shortest paths over citation edges only (what 'cites' means everywhere else on the pages)
    def bfs_cites(dq):
        while dq:
            i = dq.popleft()
            for j in cites[i]:
                if depth[j] < 0: depth[j] = depth[i] + 1; parent[j] = i; parent_kind[j] = 'cites'; dq.append(j)
    bfs_cites(deque([root]))
    n_cite_only = sum(1 for d in depth if d >= 0)
    # phase 2: the few theorems no proof cites are reached through a statement that mentions them or a definition module that
    # imports them; extend from already-reached nodes (shallowest first), then continue over citations, until nothing changes
    def_seen = [False] * len(defs)
    changed = True
    while changed:
        changed = False
        newly = deque()
        for i in sorted((k for k in range(N) if depth[k] >= 0), key=lambda k: depth[k]):
            for j in stmt_thm.get(i, []):
                if depth[j] < 0: depth[j] = depth[i] + 1; parent[j] = i; parent_kind[j] = 'statement'; newly.append(j); changed = True
            stack = [d for d in list(thm_defs[i]) + sol_defs[i] if not def_seen[d]]
            while stack:
                d = stack.pop()
                if def_seen[d]: continue
                def_seen[d] = True
                for j in def_thm.get(dstems[d], []):
                    if depth[j] < 0: depth[j] = depth[i] + 1; parent[j] = i; parent_kind[j] = 'definition:' + dstems[d]; newly.append(j); changed = True
                stack.extend(x for x in def_imports_def[d] if not def_seen[x])
        bfs_cites(newly)
    print(f'reached by citations only: {n_cite_only}; after statement/definition hops: {sum(1 for d in depth if d >= 0)}', file=sys.stderr)
    unreached = [stems[i] for i in range(N) if depth[i] < 0]
    print(f'unreached theorems: {len(unreached)} {unreached[:5]}', file=sys.stderr)
    if unreached: raise SystemExit('every theorem must have a path from the root; %d do not' % len(unreached))
    order = []; indeg_k = indeg[:]
    dq = deque(i for i in range(N) if indeg_k[i] == 0)
    while dq:
        i = dq.popleft(); order.append(i)
        for j in cites[i]:
            indeg_k[j] -= 1
            if indeg_k[j] == 0: dq.append(j)
    acyclic = len(order) == N
    print(f'acyclic={acyclic} topo={len(order)} {time.time()-t0:.0f}s', file=sys.stderr)
    below = [0] * N; clo = [0] * N; height = [0] * N
    for i in reversed(order):
        b = 0; h = 0
        for j in cites[i]:
            b |= clo[j] | (1 << j)
            if height[j] + 1 > h: h = height[j] + 1
        clo[i] = b; height[i] = h
    for i in range(N): below[i] = clo[i].bit_count()
    del clo
    print(f'below done {time.time()-t0:.0f}s; root below={below[root]} height={height[root]}', file=sys.stderr)
    route_md = open(os.path.join(docs, 'route.md'), encoding='utf-8').read()
    ppath = open(os.path.join(repo, 'PROOF-PATH.md'), encoding='utf-8').read()
    ovp = os.path.join(docs, 'overview.md')
    overview = open(ovp, encoding='utf-8').read() if os.path.exists(ovp) else ''
    stage_of = {}; landmark_src = collections.defaultdict(set); def_landmarks = collections.defaultdict(set)
    secs = route_sections(route_md)
    for num, title, text in secs:
        for name in TICK.findall(text):
            if name in qidx:
                landmark_src[name].add(f'route.md §{num}')
                if num != 7: stage_of.setdefault(name, set()).add(num)
        for mdef in re.findall(r'Def_([A-Za-z0-9_]+)\.lean', text):
            if mdef in didx: def_landmarks[mdef].add(f'route.md §{num}')
    for name in TICK.findall(ppath):
        if name in qidx: landmark_src[name].add('PROOF-PATH.md')
    for mdef in re.findall(r'Def_([A-Za-z0-9_]+)\.lean', ppath):
        if mdef in didx: def_landmarks[mdef].add('PROOF-PATH.md')
    for name in TICK.findall(overview):
        if name in qidx: landmark_src[name].add('overview.md')
    landmark_src[ROOT].add('README.md')
    # a theorem named in several sections belongs to the latest step that names it (§2 names all four ingredients of the
    # contradiction; each is the subject of its own later section), except the top reductions named in §1
    stage_of = {q: (1 if (1 in s and depth[qidx[q]] <= 2) else max(s)) for q, s in stage_of.items()}
    stage_of[ROOT] = 0
    # the reviewed hand table wins (gen/data/landmark_stages.json); the rule above is the fallback for names it does not list
    hand = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data', 'landmark_stages.json'), encoding='utf-8'))['stages']
    for q, s in hand.items():
        if q in qidx: stage_of[q] = s
    missing = [q for q in landmark_src if q not in hand]
    if missing: print(f'landmarks without a hand-assigned step (rule used): {missing}', file=sys.stderr)
    landmarks = sorted(landmark_src, key=lambda q: (depth[qidx[q]], q))
    L = set(qidx[q] for q in landmarks)
    ldag = {}
    for q in landmarks:
        i = qidx[q]; seen = {i}; kids = set(); st = list(cites[i])
        while st:
            j = st.pop()
            if j in seen: continue
            seen.add(j)
            if j in L: kids.add(j); continue
            st.extend(cites[j])
        ldag[q] = sorted((thms[j]['qual'] for j in kids), key=lambda x: (depth[qidx[x]], x))
    via = [-1] * N
    byd = sorted((i for i in range(N) if depth[i] >= 0), key=lambda k: depth[k])
    for i in byd:
        if i == root: continue
        p = parent[i]
        via[i] = p if p in L else via[p]
    stage = [None] * N
    for i in range(N):
        q = thms[i]['qual']
        if q in stage_of: stage[i] = stage_of[q]
    for i in byd:
        if stage[i] is None and depth[i] > 0: stage[i] = stage[parent[i]]
    def_used_stmt = [[] for _ in defs]; def_used_proof = [0] * len(defs)
    for i in range(N):
        for d in thm_defs[i]: def_used_stmt[d].append(i)
        for d in sol_defs[i]: def_used_proof[d] += 1
    ns_count = collections.Counter(t['qual'].split('.')[0] if '.' in t['qual'] else '(root)' for t in thms)
    out = {
        'root': root, 'N': N, 'acyclic': acyclic, 'n_cite_only': n_cite_only, 'n_edges': sum(outdeg), 'max_indeg': max(indeg), 'max_outdeg': max(outdeg),
        'max_depth': max(depth), 'height_root': height[root], 'unreached': unreached,
        'leaves': sum(1 for i in range(N) if outdeg[i] == 0),
        'theorems': [{'qual': thms[i]['qual'], 'stem': stems[i], 'indeg': indeg[i], 'outdeg': outdeg[i], 'depth': depth[i],
                      'below': below[i], 'height': height[i], 'parent': parent[i], 'parent_kind': parent_kind[i], 'via': via[i],
                      'stage': stage[i], 'landmark': (thms[i]['qual'] in landmark_src), 'is_dup': thms[i]['is_dup'],
                      'ns': thms[i]['qual'].split('.')[0] if '.' in thms[i]['qual'] else '',
                      'stmt_defs': thm_defs[i], 'proof_defs': sol_defs[i], 'stmt_thms': stmt_thm.get(i, []),
                      'sol': solinfo.get(i)} for i in range(N)],
        'cites': cites, 'cite_uses': cite_uses,
        'defs': [{'stem': d['stem'], 'lines': d['lines'], 'bytes': d['bytes'], 'n_decls': len(d['decls']),
                  'imports_defs': def_imports_def[k], 'imports_thms': def_thm.get(d['stem'], []),
                  'used_in_statements': def_used_stmt[k], 'used_in_proofs': def_used_proof[k],
                  'landmark_src': sorted(def_landmarks.get(d['stem'], [])), 'has_copyright': d['has_copyright'],
                  'namespaces': d['namespaces']} for k, d in enumerate(defs)],
        'landmarks': [{'qual': q, 'sources': sorted(landmark_src[q]), 'stage': stage_of.get(q), 'children': ldag[q]} for q in landmarks],
        'stages': [{'num': n, 'title': t} for n, t, _ in secs],
        'namespaces': ns_count.most_common(),
    }
    json.dump(out, open(os.path.join(build, 'graph.json'), 'w'), ensure_ascii=False)
    print(f'graph.json written {time.time()-t0:.0f}s; landmarks {len(landmarks)}; stages {[(n,t) for n,t,_ in secs]}', file=sys.stderr)

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3])
