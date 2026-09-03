# Documentation generator for the Lean 4 FLT tree

Builds a folder of static web pages (open `html/index.html` from disk; no server) from a checkout of the tree:
one page per theorem and per definition module, the route chapters, the landmark graph, the namespace index and the
repository's own Markdown documents, all cross-linked. Nothing here runs Lean; the .lean files are read as text.

## Requirements

Python 3.10+ with `jinja2`, `markdown`, `pygments` (2.18+ for the Lean 4 lexer) and, for the optional browser test,
`playwright` with a Chromium build; Graphviz (`dot`) on the PATH; `bun` (or Node: adjust `gen/katex_render.js`'s
invocation in `gen/render.py`) to run the vendored KaTeX at build time (pre-rendering and validation).

## One command

    python3 gen/build.py --repo <checkout> --docs <checkout>/docs --content <folder with english.jsonl etc.> --out out/html --qa \
        --english-attribution "English text generated automatically from the Lean source; the Lean statement is authoritative."

Stages (each can be run alone): `gen/extract.py <repo> build/` streams `Theorems/`, `P2M/Sol/`, `Definitions/` into
`build/{thm,sol,def}.jsonl` (a few minutes; most of it is counting how often each cited name occurs in each proof);
`gen/graphdata.py build/ <repo> <docs>` computes the citation graph, exact "below" counts, shortest paths from the final
theorem, landmarks and route steps (`gen/data/landmark_stages.json` is the reviewed step table); `gen/render.py` writes the
site (≈30 s; every `$…$` fragment goes through KaTeX once: the repository documents and English titles are pre-rendered to HTML,
the English statement/proof/context text is validated with the same strict parse and shipped as TeX source that the bundled
`katex.min.js` typesets in the browser — a fragment KaTeX cannot parse stops the build unless `--tex-errors=source`; numbers land
in `render-report.json` next to the output folder); `gen/selfcheck.py out/html` scans the output for absolute paths, raw TeX, double escaping and lists every
external URL and hex-like token for review (`--deny-file=<file>` adds site-specific tokens and phrases, one per line; see the top of the script);
`gen/qa_filetest.py out/html <deep theorem name>` drives headless Chromium over file:// and fails on any console error,
failed request or non-file request (screenshots in `out/qa/`).

Useful flags of `render.py` / `build.py`: `--skip-extract` (reuse build/), `--no-docs` (do not render the optional prose documents),
`--no-mathlib-links`, `--references-origin <tag>|all` (filter references by their origin tag), `--link-report` (identifier-link counts by rule),
`--tex-errors fail|source`.

## Inputs

* `--repo`: the tree (needs `Theorems/`, `P2M/Sol/`, `Definitions/`, `README.md`, `PROOF-PATH.md`, `ATTRIBUTION.md`,
  `lean-toolchain`). `--docs`: the folder with `route.md` (required: the route chapters and landmark selection come from
  it; `overview.md`, if present, adds landmark names) and, optionally, the other prose documents, which are rendered under
  Documents unless `--no-docs` is given (`overview.md`, `structure.md`, `verification.md`, `limitations.md`, `port-lean433.md`).
* `--content` (optional): `*.json`/`*.jsonl` records keyed by Lean name (theorems) or module name (definition modules)
  with any of `title_en`, `statement_en`, `proof_idea_en`, `summary_en`, `context_en`, `mathlib_note`, `references`
  (+ `references_origin`), and `strength.json` (`{name: {note_md, source}}`). Markdown with `$…$` mathematics. Pages render
  without it; records that match no theorem or module are reported.

## Vendored third-party files

`gen/vendor/graphviz.umd.js` — @hpcc-js/wasm 2.35.0 (Graphviz compiled to WebAssembly), Apache-2.0.
`gen/vendor/katex/` — KaTeX 0.18.4, MIT; fonts SIL OFL 1.1 (embedded into one CSS file as data: URIs at build time); `katex.min.js`
is both the build-time renderer (under bun) and shipped to `assets/vendor/katex/` for the theorem explorer and definition pages.

## Output layout

`index.html`, `thm.html` (+ `data/meta.js`, `data/edges.js`, `data/titles.js`, `data/shard/NNN.js`), `route/`, `dag/`,
`areas/`, `def/`, `docs/`, `about.html`, `assets/`, `README-DOCS.md`, `SMOKE-TEST.md`, `MANIFEST.txt`. All links are
relative; classic scripts only (no fetch/XHR/modules), so the folder works from `file://`.
