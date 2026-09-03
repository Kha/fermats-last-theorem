#!/usr/bin/env python3
"""One command: extract -> graph -> render (-> optional QA).
python3 gen/build.py --repo <checkout of the tree> --docs <its docs/ folder> [--content <folder of English json/jsonl>] --out out/html [--skip-extract] [--qa] [--english-attribution "…"]
"""
import os, sys, argparse, subprocess, time
GEN = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument('--repo', required=True); ap.add_argument('--docs', required=True); ap.add_argument('--content', default='')
ap.add_argument('--out', required=True); ap.add_argument('--build', default=os.path.join(os.path.dirname(GEN), 'build'))
ap.add_argument('--skip-extract', action='store_true', help='reuse build/*.jsonl from a previous run (the repo did not change)')
ap.add_argument('--qa', action='store_true'); ap.add_argument('--english-attribution', default='', help='one sentence shown under generated English text and on About, e.g. "English text generated automatically from the Lean source; the Lean statement is authoritative."')
ap.add_argument('--references-origin', default='all')
ap.add_argument('--allow-drops', action='store_true')
ap.add_argument('--no-docs', action='store_true')
ap.add_argument('--link-report', action='store_true')
ap.add_argument('--commit', default=None, help='what the pages say they document: a commit hash, or a phrase such as "the Lean sources in this repository" (default: HEAD of --repo)')
ap.add_argument('--tex-errors', choices=('fail', 'source'), default='fail', help="a $…$ fragment KaTeX cannot parse: 'fail' = list and stop (default), 'source' = ship it as visible TeX source")
ap.add_argument('--deep-node', default='CerednikDrinfeld.FormalODModule.exists_isEtaSection_one_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq')
a = ap.parse_args()
t0 = time.time()
def run(cmd):
    print('$', ' '.join(cmd), flush=True)
    r = subprocess.run(cmd)
    if r.returncode != 0: sys.exit(f'step failed: {cmd[1]}')
py = sys.executable
if not a.skip_extract or not os.path.exists(os.path.join(a.build, 'sol.jsonl')):
    run([py, os.path.join(GEN, 'extract.py'), a.repo, a.build])
import json as _json
st = _json.load(open(os.path.join(a.build, 'extract_stats.json')))['stats']
drops = {k: v for k, v in st.items() if k.startswith('fail_') and v}
if drops and not a.allow_drops: sys.exit(f'extraction dropped records: {drops} (see build/extract_stats.json; --allow-drops to proceed)')
run([py, os.path.join(GEN, 'graphdata.py'), a.build, a.repo, a.docs])
cmd = [py, os.path.join(GEN, 'render.py'), '--build', a.build, '--repo', a.repo, '--docs', a.docs, '--out', a.out]
if a.content: cmd += ['--content', a.content]
if a.english_attribution: cmd += ['--english-attribution', a.english_attribution]
cmd += ['--references-origin', a.references_origin]
if a.no_docs: cmd += ['--no-docs']
if a.commit: cmd += ['--commit', a.commit]
if a.link_report: cmd += ['--link-report']
cmd += ['--tex-errors', a.tex_errors]
run(cmd)
deny = os.path.join(os.path.dirname(GEN), 'denylist.local')
run([py, os.path.join(GEN, 'selfcheck.py'), a.out] + (['--deny-file=' + deny] if os.path.exists(deny) else []))
if a.qa: run([py, os.path.join(GEN, 'qa_filetest.py'), a.out, a.deep_node])
print(f'build done in {time.time()-t0:.0f}s')
