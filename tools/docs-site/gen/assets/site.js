/* FLT documentation site: client code. Classic script, no modules, no fetch/XHR (works from file://).
   Data files are classic scripts that assign globals: data/meta.js (FLT_META), data/edges.js (FLT_EDGES),
   data/titles.js (FLT_TITLES), data/shard/NNN.js (calls FLT_SHARD_CB). */
(function () {
  "use strict";
  var ROOT = window.FLT_ROOT || "";
  var FLT = window.FLT = window.FLT || {};
  var PAL = { fill: "#E6F2EA", border: "#6FA287", text: "#1F3B2C", sub: "#5C7466", rootFill: "#2F7D55", rootBorder: "#1E5C3C",
              rootText: "#FFFFFF", edge: "#8A9AA5", defFill: "#F4F1FA", defBorder: "#8C7FD9", stubFill: "#FFFFFF", lmBorder: "#2F7D55" };
  FLT.PAL = PAL;
  function $(sel, el) { return (el || document).querySelector(sel); }
  function esc(s) { return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;"); }
  FLT.esc = esc;
  function loadScript(src, cb) {
    var s = document.createElement("script"); s.src = src; s.async = true;
    s.onload = function () { cb && cb(null); }; s.onerror = function () { cb && cb(new Error("could not load " + src)); };
    document.head.appendChild(s);
  }
  FLT.loadScript = loadScript;
  function fmt(n) { return String(n).replace(/\B(?=(\d{3})+(?!\d))/g, ","); }
  FLT.fmt = fmt;

  // ---------- data access ----------
  var metaCbs = null;
  FLT.withMeta = function (cb) {           // ensures FLT_META, FLT_EDGES, FLT_TITLES are loaded
    if (window.FLT_META && window.FLT_EDGES && window.FLT_TITLES && window.FLT_DDECL) { prep(); return cb(); }
    if (metaCbs) { metaCbs.push(cb); return; }
    metaCbs = [cb];
    var need = 4, failed = null;
    function done(e) { if (e) failed = e; if (--need === 0) { if (!window.FLT_TITLES) window.FLT_TITLES = {}; prep(); var l = metaCbs; metaCbs = null; l.forEach(function (f) { f(failed); }); } }
    window.FLT_META ? done() : loadScript(ROOT + "data/meta.js", done);
    window.FLT_EDGES ? done() : loadScript(ROOT + "data/edges.js", done);
    window.FLT_TITLES ? done() : loadScript(ROOT + "data/titles.js", done);
    window.FLT_DDECL ? done() : loadScript(ROOT + "data/ddecl.js", done);
  };
  var M = null;   // prepared meta
  function prep() {
    if (M) return M;
    var m = window.FLT_META, e = window.FLT_EDGES;
    if (!m || !e) return null;
    var dd = window.FLT_DDECL || { ddecl: [], ext: {} };
    m.ddecl = dd.ddecl; m.ext = dd.ext;
    var N = m.names.length, idx = Object.create(null);
    for (var i = 0; i < N; i++) idx[m.names[i]] = i;
    // cited_by from CSR cites
    var cnt = new Int32Array(N + 1), k;
    for (k = 0; k < e.dst.length; k++) cnt[e.dst[k] + 1]++;
    for (i = 0; i < N; i++) cnt[i + 1] += cnt[i];
    var boff = new Int32Array(cnt), bdst = new Int32Array(e.dst.length), fill = new Int32Array(N);
    for (i = 0; i < N; i++) for (k = e.off[i]; k < e.off[i + 1]; k++) { var d = e.dst[k]; bdst[boff[d] + fill[d]++] = i; }
    M = { N: N, names: m.names, idx: idx, off: e.off, dst: e.dst, boff: boff, bdst: bdst, m: m };
    FLT.M = M; return M;
  }
  FLT.cites = function (i) { var r = []; for (var k = M.off[i]; k < M.off[i + 1]; k++) r.push(M.dst[k]); return r; };
  FLT.citedBy = function (i) { var r = []; for (var k = M.boff[i]; k < M.boff[i + 1]; k++) r.push(M.bdst[k]); return r; };
  FLT.indexOf = function (name) {
    if (name in M.idx) return M.idx[name];
    // accept file-stem spelling (dots as underscores) and Thm_/S_ prefixes
    var s = name.replace(/^Thm_|^S_/, "").replace(/\.lean$/, "");
    if (M.m.stemIndex && s in M.m.stemIndex) return M.m.stemIndex[s];
    if (!M.stemIdx) { M.stemIdx = {}; for (var i = 0; i < M.N; i++) M.stemIdx[FLT.stem(i)] = i; }
    return s in M.stemIdx ? M.stemIdx[s] : -1;
  };
  FLT.stem = function (i) { var x = M.m.stemx && M.m.stemx[i]; return x || M.names[i].replace(/\./g, "_"); };
  FLT.title = function (i) { var T = window.FLT_TITLES; var t = T && (T.length !== undefined ? T[i] : T[M.names[i]]); return t || null; };   // titles.js: array parallel to names
  FLT.shortName = function (name) { var p = name.split("."); return p.length <= 2 ? name : p.slice(-2).join("."); };
  FLT.stageName = function (s) { var st = M.m.stages; return (s === null || s === undefined) ? null : (st && st[String(s)]) || ("Step " + s); };
  FLT.pathToRoot = function (i) { var p = [], par = M.m.parent; while (i >= 0) { p.push(i); i = par[i]; if (p.length > 400) break; } return p; };
  FLT.thmHref = function (i) { return ROOT + "thm.html#" + M.names[i]; };
  FLT.defHref = function (d) { return ROOT + "def/" + M.m.defs[d] + ".html"; };

  // identifier -> definition resolution (textual, conservative: a missing link is fine, a wrong one is not).
  //   exact      token is a constant declared in a definition module, or a theorem name
  //   bare       undotted Foo with NS.Foo declared for exactly one NS among the open namespaces / own namespace prefixes
  //   qualified  dotted token with a capitalised head, completed through exactly one such NS
  //   field      x.foo where x is bound in the statement with a type whose head T is visible: links only to T.foo (or foo of a
  //              structure T extends) when that is a project declaration or structure field; never guessed from the suffix alone
  var idExact = null;
  function buildIdIndex() {
    idExact = Object.create(null);
    var dd = M.m.ddecl || [];
    for (var k = 0; k < dd.length; k++) idExact[dd[k][0]] = k;
  }
  var TOKRE = /[A-Za-z_\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2100-\u214F«][A-Za-z0-9_'!?\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2070-\u209F\u2100-\u214F»«.]*/g;
  FLT.makeResolver = function (ctxLines, qual, text) {
    if (!M) return null;
    if (!idExact) buildIdIndex();
    var vis = Object.create(null), opened = [];
    (ctxLines || []).forEach(function (l) {
      var s = l.trim(), body = null;
      if (s.indexOf("open ") === 0) { body = s.slice(5).replace(/scoped /g, " ").split(" in ")[0].replace(/\([^)]*\)/g, " ").split(" hiding")[0].split(" renaming")[0]; body.split(/\s+/).forEach(function (x) { if (/^[A-Za-z_][A-Za-z0-9_.']*$/.test(x)) opened.push(x); }); }
      else if (s.indexOf("p2m_open ") === 0 || s.indexOf("p2m_export ") === 0) { var mq = s.match(/"([^"]*)"/); if (mq) mq[1].split(/\s+/).forEach(function (x) { if (x) opened.push(x.split("~")[0]); }); }
      else if (s.indexOf("namespace ") === 0) { opened.push(s.slice(10).trim()); }
    });
    opened.forEach(function (o) { vis[o] = 1; });
    var own = qual && qual.indexOf(".") > 0 ? qual.slice(0, qual.lastIndexOf(".")) : "";
    while (own) { vis[own] = 1; own = own.indexOf(".") > 0 ? own.slice(0, own.lastIndexOf(".")) : ""; }
    Object.keys(vis).forEach(function (n) { opened.forEach(function (o) { if (idExact[n + "." + o] !== undefined) vis[n + "." + o] = 1; }); });
    var visList = Object.keys(vis);
    var tops = Object.create(null);
    ((text || "") + " " + (ctxLines || []).join(" ") + " " + (qual || "")).replace(TOKRE, function (w) { tops[w.split(".")[0]] = 1; return w; });
    var selfName = qual;
    // names bound in the statement itself are never linked
    var bound = Object.create(null);
    var src = (text || "") + "\n" + (ctxLines || []).join("\n");
    src.replace(/[({\[⦃]\s*([^:(){}\[\]⦃⦄,]+?)\s*:(?!=)/g, function (mm, g) { g.split(/\s+/).forEach(function (x) { if (/^[A-Za-z_\u00C0-\u1FFF][A-Za-z0-9_'\u00C0-\u1FFF\u2070-\u209F]*$/.test(x)) bound[x] = 1; }); return mm; });
    src.replace(/(?:∀|∃!?|fun|λ|∑|∏|⨆|⋃|⋂)\s+([^,:=(){}\[\]]+?)\s*(?:,|:|=>|↦)/g, function (mm, g) { g.replace(/[(){}\[\]]/g, " ").split(/\s+/).forEach(function (x) { if (/^[A-Za-z_\u00C0-\u1FFF][A-Za-z0-9_'\u00C0-\u1FFF\u2070-\u209F]*$/.test(x)) bound[x] = 1; }); return mm; });
    // bound variable -> head constant of its type as written: (W : WeierstrassCurve ℤ) gives W -> WeierstrassCurve
    var btypes = Object.create(null);
    var BT1 = /[({\[⦃]\s*([^:(){}\[\]⦃⦄,]+?)\s*:\s*([A-Za-z_\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2100-\u214F][A-Za-z0-9_'.\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2070-\u209F\u2100-\u214F]*)/g;
    var BT2 = /(?:∀|∃!?|fun|λ)\s+([^,:=(){}\[\]]+?)\s*:\s*([A-Za-z_\u00C0-\u024F\u0370-\u03FF\u2100-\u214F][A-Za-z0-9_'.\u2070-\u209F]*)/g;
    [BT1, BT2].forEach(function (rx) { src.replace(rx, function (mm, g, ty) { ty = ty.replace(/\.+$/, ""); g.split(/\s+/).forEach(function (x) { if (!/^[A-Za-z_\u00C0-\u1FFF][A-Za-z0-9_'\u00C0-\u1FFF\u2070-\u209F]*$/.test(x)) return; if (btypes[x] === undefined) btypes[x] = ty; else if (btypes[x] !== ty) btypes[x] = null; /* bound twice with different types: no field links */ }); return mm; }); });
    var EXT = M.m.ext || {};
    function resolveType(t) {
      if (idExact[t] !== undefined) return [t];
      var c = []; for (var i3 = 0; i3 < visList.length; i3++) if (idExact[visList[i3] + "." + t] !== undefined && c.indexOf(visList[i3] + "." + t) < 0) c.push(visList[i3] + "." + t);
      if (c.length === 1) return c;
      return [t].concat(visList.map(function (n) { return n + "." + t; }));
    }
    function member(T, rest) {
      var seen = {}, todo = [T], first = rest.split(".")[0];
      while (todo.length) {
        var t = todo.shift(); if (seen[t]) continue; seen[t] = 1;
        if (idExact[t + "." + rest] !== undefined) return idExact[t + "." + rest];
        if (idExact[t + "." + first] !== undefined) return idExact[t + "." + first];
        (EXT[t] || []).forEach(function (p) { todo.push(p); });
      }
      return undefined;
    }
    function target(k, cls) { var d = M.m.ddecl[k]; return [FLT.defHref(d[1]) + "#L" + d[2], d[3] + " " + d[0] + " — Def_" + M.m.defs[d[1]] + ".lean, line " + d[2], cls]; }
    return function (w) {
      w = w.replace(/\.+$/, "");
      if (w === selfName) return null;
      var parts = w.split("."), cands, i2;
      if (parts.length === 1 && bound[w]) return null;
      var k = idExact[w];
      if (k !== undefined) return target(k, "exact");
      if (w in M.idx) return [FLT.thmHref(M.idx[w]), "theorem " + w, "theorem"];
      if (parts.length === 1) {
        cands = []; for (i2 = 0; i2 < visList.length; i2++) { var c = idExact[visList[i2] + "." + w]; if (c !== undefined && cands.indexOf(c) < 0) cands.push(c); }
        return cands.length === 1 ? target(cands[0], "bare") : null;
      }
      var head = parts[0];
      if (head.length > 1 && /^[A-Z]/.test(head)) {
        cands = []; for (i2 = 0; i2 < visList.length; i2++) { var c2 = idExact[visList[i2] + "." + w]; if (c2 !== undefined && cands.indexOf(c2) < 0) cands.push(c2); }
        return cands.length === 1 ? target(cands[0], "qualified") : null;
      }
      // field notation x.foo: only when x is bound with a visible type T and T.foo (or a parent structure's foo) is a project declaration
      if (btypes[head] && !bound[btypes[head]]) {
        var rest = parts.slice(1).join("."), Ts = resolveType(btypes[head]);
        for (var j = 0; j < Ts.length; j++) { var kk = member(Ts[j], rest); if (kk !== undefined) return target(kk, "field"); }
      }
      return null;
    };
  };
  FLT.resolveId = null;

  // shards
  var NSH = 256, shardWait = {}, shardData = {};
  function fnv(s) { var h = 2166136261; for (var i = 0; i < s.length; i++) { var c = s.charCodeAt(i); if (c >= 0xD800 && c < 0xDC00 && i + 1 < s.length) { var lo = s.charCodeAt(i + 1); c = 0x10000 + ((c - 0xD800) << 10) + (lo - 0xDC00); i++; } h ^= c; h = Math.imul(h, 16777619) >>> 0; } return h; }
  FLT.shardOf = function (name) { return fnv(name) % NSH; };
  window.FLT_SHARD_CB = function (id, data) { shardData[id] = data; var w = shardWait[id] || []; shardWait[id] = null; w.forEach(function (f) { f(); }); };
  FLT.withRecord = function (name, cb) {
    var id = FLT.shardOf(name), sid = ("00" + id).slice(-3);
    if (shardData[sid]) return cb(shardData[sid][name] || null);
    if (shardWait[sid]) { shardWait[sid].push(function () { cb(shardData[sid][name] || null); }); return; }
    shardWait[sid] = [function () { cb(shardData[sid][name] || null); }];
    loadScript(ROOT + "data/shard/" + sid + ".js", function (e) { if (e) { var w = shardWait[sid] || []; shardWait[sid] = null; shardData[sid] = {}; w.forEach(function (f) { f(); }); } });
  };

  // ---------- math ----------
  // English-layer mathematics arrives as TeX source in <span class="tex"> (display: "tex d") and is typeset here by the
  // bundled katex.min.js (loaded by thm.html and the definition-module pages). Without the script, or for a fragment
  // KaTeX rejects, the TeX source stays visible (styled by site.css) — never a blank.
  // Same options as gen/katex_render.js validated every fragment with at build time (keep textually identical; trust is false here,
  // a throwing hook there, so a trust-gated command never reaches this page).
  FLT.KATEX_OPTS = { throwOnError: true, output: "html", strict: "ignore", maxSize: 20, maxExpand: 1000, errorColor: "#cc0000", trust: false };
  FLT.KATEX_MACROS = { "\\bigsqcap": "\\mathop{\\Large\\sqcap}" };   // same table as gen/katex_render.js MACROS; copied per call (KaTeX writes \gdef's into it)
  FLT.renderMath = function (el) {
    if (!el) return 0;
    var spans = el.querySelectorAll("span.tex:not(.k):not(.src)"), n = 0;
    if (!spans.length) return 0;
    if (!window.katex || !window.katex.render) { for (var j = 0; j < spans.length; j++) spans[j].classList.add("src"); return 0; }
    for (var i = 0; i < spans.length; i++) {
      var s = spans[i], tex = s.textContent;
      var o = { displayMode: s.classList.contains("d"), macros: {} }, key; for (key in FLT.KATEX_OPTS) o[key] = FLT.KATEX_OPTS[key]; for (key in FLT.KATEX_MACROS) o.macros[key] = FLT.KATEX_MACROS[key];
      try { window.katex.render(tex, s, o); s.classList.add("k"); n++; }
      catch (e) { s.textContent = tex; s.classList.add("src"); s.title = "TeX source (could not be typeset)"; }
    }
    return n;
  };

  // ---------- search ----------
  FLT.initSearch = function (input, resultsEl) {
    if (!input) return;
    var timer = null, active = -1;
    function ensure(cb) { FLT.withMeta(function () { cb(); }); }
    input.addEventListener("focus", function () { ensure(function () { }); });
    input.addEventListener("input", function () { clearTimeout(timer); timer = setTimeout(run, 60); });
    input.addEventListener("keydown", function (ev) {
      var items = resultsEl.querySelectorAll("a.sr");
      if (ev.key === "ArrowDown") { active = Math.min(items.length - 1, active + 1); mark(items); ev.preventDefault(); }
      else if (ev.key === "ArrowUp") { active = Math.max(0, active - 1); mark(items); ev.preventDefault(); }
      else if (ev.key === "Enter") { var a = items[Math.max(0, active)]; if (a) { window.location.href = a.getAttribute("href"); resultsEl.style.display = "none"; } }
      else if (ev.key === "Escape") { resultsEl.style.display = "none"; }
    });
    document.addEventListener("click", function (ev) { if (!resultsEl.contains(ev.target) && ev.target !== input) resultsEl.style.display = "none"; });
    function mark(items) { for (var i = 0; i < items.length; i++) items[i].classList.toggle("active", i === active); }
    function run() {
      var q = input.value.trim();
      if (!q) { resultsEl.style.display = "none"; return; }
      ensure(function () {
        var res = FLT.search(q, 40); active = -1;
        if (!res.length) { resultsEl.innerHTML = '<div class="sr-empty">No theorem or definition name contains all of these words.</div>'; resultsEl.style.display = "block"; return; }
        resultsEl.innerHTML = res.map(function (r) {
          if (r.kind === "thm") {
            var t = FLT.title(r.i), lm = M.m.lm[r.i] ? ' <span class="badge lm">landmark</span>' : "";
            return '<a class="sr" href="' + FLT.thmHref(r.i) + '"><span class="sr-kind">theorem</span>' + lm + (t ? '<span class="sr-title">' + esc(t) + '</span>' : "") + '<code>' + esc(M.names[r.i]) + '</code><span class="sr-num">' + fmt(M.m.below[r.i]) + ' below · depth ' + M.m.depth[r.i] + '</span></a>';
          } else if (r.kind === "def") {
            return '<a class="sr" href="' + FLT.defHref(r.d) + '"><span class="sr-kind def">definitions</span><code>Def_' + esc(M.m.defs[r.d]) + '.lean</code></a>';
          } else {
            var dd = M.m.ddecl[r.k];
            return '<a class="sr" href="' + FLT.defHref(dd[1]) + '#L' + dd[2] + '"><span class="sr-kind def">' + esc(dd[3] || "def") + '</span><code>' + esc(dd[0]) + '</code><span class="sr-num">in Def_' + esc(M.m.defs[dd[1]]) + '.lean</span></a>';
          }
        }).join("") + (res.more ? '<div class="sr-more">' + fmt(res.more) + ' more matches — keep typing to narrow</div>' : "");
        resultsEl.style.display = "block";
      });
    }
  };
  FLT.search = function (q, limit) {
    function norm(s) { return s.toLowerCase().replace(/[\u2010-\u2015\u2212]/g, "-").replace(/\s*=\s*/g, "=").replace(/č/g, "c"); }
    var toks = norm(q).split(/[\s,]+/).filter(Boolean);
    var out = [], total = 0, N = M.N, names = M.names, lname = M.lname, al = M.m.aliases || {};
    if (!lname) { lname = M.lname = new Array(N); for (var i = 0; i < N; i++) { var t = FLT.title(i); lname[i] = norm(names[i] + " " + (t || "") + " " + (al[names[i]] || "")); } }
    function matches(s) { for (var k = 0; k < toks.length; k++) if (s.indexOf(toks[k]) < 0) return false; return true; }
    var scored = [];
    for (var i2 = 0; i2 < N; i2++) {
      if (!matches(lname[i2])) continue;
      total++;
      var last = names[i2].slice(names[i2].lastIndexOf(".") + 1).toLowerCase();
      var sc = (M.m.lm[i2] ? 1e7 : 0) + (last === toks[0] ? 1e6 : 0) + (last.indexOf(toks[0]) === 0 ? 1e5 : 0) + Math.min(99999, M.m.below[i2]) - M.m.depth[i2];
      scored.push([sc, i2]);
    }
    scored.sort(function (a, b) { return b[0] - a[0]; });
    var defs = M.m.defs || [], dres = [];
    for (var d = 0; d < defs.length; d++) if (matches(("def_" + defs[d]).toLowerCase())) { total++; dres.push({ kind: "def", d: d }); }
    var dd = M.m.ddecl || [], ddres = [];
    if (!M.lddecl) { M.lddecl = dd.map(function (x) { return x[0].toLowerCase(); }); }
    for (var k2 = 0; k2 < dd.length && ddres.length < 200; k2++) if (matches(M.lddecl[k2]) && !(dd[k2][3] === "field" && dd[k2][0].length - dd[k2][0].lastIndexOf(".") - 1 < 4)) { total++; ddres.push({ kind: "ddecl", k: k2, exact: M.lddecl[k2].slice(M.lddecl[k2].lastIndexOf(".") + 1) === toks[0] }); }
    ddres.sort(function (a, b) { return (b.exact ? 1 : 0) - (a.exact ? 1 : 0); });
    // interleave: exact def-decl hits first, then landmarks/theorems, then def modules
    ddres.filter(function (x) { return x.exact; }).forEach(function (x) { out.push(x); });
    scored.forEach(function (x) { out.push({ kind: "thm", i: x[1] }); });
    dres.forEach(function (x) { out.push(x); });
    ddres.filter(function (x) { return !x.exact; }).forEach(function (x) { out.push(x); });
    var r = out.slice(0, limit); r.more = Math.max(0, total - r.length); return r;
  };

  // ---------- graph widget (Graphviz compiled to WebAssembly, embedded in assets/vendor/graphviz.umd.js) ----------
  var gvPromise = null;
  function getGV() {
    if (gvPromise) return gvPromise;
    var ns = window["@hpcc-js/wasm/graphviz"] || window["@hpcc-js/wasm"];
    if (!ns || !ns.Graphviz) return (gvPromise = Promise.reject(new Error("graph layout engine not available")));
    gvPromise = ns.Graphviz.load(); return gvPromise;
  }
  FLT.getGV = getGV;
  function wrapName(name, width) {   // break a dotted Lean name into lines of <= width at dots/underscores
    var parts = name.split(/(?=[._])/), lines = [], cur = "";
    parts.forEach(function (p) { if ((cur + p).length > width && cur) { lines.push(cur); cur = p; } else cur += p; });
    if (cur) lines.push(cur);
    if (lines.length > 4) { lines = lines.slice(0, 3).concat(["…" + name.slice(-Math.min(width, 12))]); }
    return lines;
  }
  FLT.Graph = function (container, focus, opts) {
    this.el = container; this.focus = focus; this.opts = opts || {};
    this.capUp = {}; this.capDown = {}; this.expanded = {}; this.extra = {}; this.showDefs = true;
    this.expanded[focus] = true; this.capUp[focus] = 14; this.capDown[focus] = 8;
    var self = this;
    container.addEventListener("click", function (ev) {
      var a = ev.target.closest ? ev.target.closest("a") : null; if (!a) return;
      var h = a.getAttribute("xlink:href") || a.getAttribute("href") || "";
      if (h.indexOf("#x:") === 0) { ev.preventDefault(); var v = +h.slice(3); self.expanded[v] = !self.expanded[v]; if (self.expanded[v]) { self.capUp[v] = self.capUp[v] || 10; self.capDown[v] = self.capDown[v] || 6; } self.draw(); }
      else if (h.indexOf("#mu:") === 0) { ev.preventDefault(); var v2 = +h.slice(4); self.capUp[v2] = (self.capUp[v2] || 10) + 20; self.draw(); }
      else if (h.indexOf("#md:") === 0) { ev.preventDefault(); var v3 = +h.slice(4); self.capDown[v3] = (self.capDown[v3] || 6) + 20; self.draw(); }
    });
  };
  FLT.Graph.prototype.addPathToRoot = function () { var p = FLT.pathToRoot(this.focus), self = this; p.forEach(function (v) { self.extra[v] = true; }); this.draw(); };
  FLT.Graph.prototype.reset = function () { this.capUp = {}; this.capDown = {}; this.expanded = {}; this.extra = {}; this.expanded[this.focus] = true; this.capUp[this.focus] = 14; this.capDown[this.focus] = 8; this.draw(); };
  FLT.Graph.prototype.visible = function () {
    var vis = {}, stubs = [], self = this;
    vis[this.focus] = true; Object.keys(this.extra).forEach(function (k) { vis[+k] = true; });
    var queue = Object.keys(this.expanded).filter(function (k) { return self.expanded[k]; }).map(Number);
    // expand in a stable order; expanded nodes contribute their neighbours up to their caps
    var seen = {};
    while (queue.length) {
      var v = queue.shift(); if (seen[v]) continue; seen[v] = true; vis[v] = true;
      var up = FLT.cites(v), down = FLT.citedBy(v);
      var cu = this.capUp[v] || 10, cd = this.capDown[v] || 6;
      down.sort(function (a, b) { return (M.m.lm[b] - M.m.lm[a]) || (M.m.depth[a] - M.m.depth[b]) || (M.m.below[b] - M.m.below[a]); });
      up.slice(0, cu).forEach(function (u) { vis[u] = true; });
      down.slice(0, cd).forEach(function (u) { vis[u] = true; });
      if (up.length > cu) stubs.push({ of: v, dir: "u", n: up.length - cu });
      if (down.length > cd) stubs.push({ of: v, dir: "d", n: down.length - cd });
    }
    var total = Object.keys(vis).length;
    return { vis: vis, stubs: stubs, total: total };
  };
  FLT.Graph.prototype.dot = function () {
    var V = this.visible(), vis = V.vis, self = this, L = [];
    var ids = Object.keys(vis).map(Number);
    if (ids.length > 400) { ids = ids.slice(0, 400); }
    L.push("digraph G {");
    L.push(' graph [rankdir=TB, bgcolor="transparent", nodesep=0.22, ranksep=0.45, pad=0.2, splines=spline];');
    L.push(' node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=10, penwidth=1.1, margin="0.08,0.04", fillcolor="' + PAL.fill + '", color="' + PAL.border + '", fontcolor="' + PAL.text + '"];');
    L.push(' edge [color="' + PAL.edge + '", penwidth=1.0, arrowsize=0.6];');
    ids.forEach(function (v) {
      var name = M.names[v], t = FLT.title(v), isF = (v === self.focus), isRoot = (v === M.m.root), lm = M.m.lm[v];
      var lines = t ? wrapText(t, 26).map(esc) : wrapName(FLT.shortName(name), 26).map(esc);
      var tc = isF ? PAL.rootText : PAL.text, sc = isF ? "#CFE7D8" : PAL.sub;
      var exp = self.expanded[v] ? "−" : "+";
      var hasN = (M.off[v + 1] - M.off[v]) + (M.boff[v + 1] - M.boff[v]) > 0;
      var label = '<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0" CELLPADDING="2"><TR><TD HREF="' + esc(FLT.thmHref(v)) + '" TOOLTIP="' + esc(name) + '">' +
        '<FONT FACE="Helvetica" POINT-SIZE="10" COLOR="' + tc + '">' + lines.join("<BR/>") + "</FONT>" +
        (t ? '<BR/><FONT FACE="Courier" POINT-SIZE="7" COLOR="' + sc + '">' + esc(wrapName(FLT.shortName(name), 34)[0]) + "</FONT>" : "") +
        "</TD>" + (hasN && !isF ? '<TD HREF="#x:' + v + '" TOOLTIP="' + (self.expanded[v] ? "collapse" : "expand neighbours") + '"><FONT FACE="Helvetica" POINT-SIZE="11" COLOR="' + (isF ? "#FFFFFF" : "#2F7D55") + '"><B>' + exp + "</B></FONT></TD>" : "") + "</TR></TABLE>>";
      var attrs = isF ? ' fillcolor="' + PAL.rootFill + '", color="' + PAL.rootBorder + '", penwidth=1.6' : (lm || isRoot ? ' color="' + PAL.lmBorder + '", penwidth=1.8' : "");
      L.push(" n" + v + " [label=" + label + attrs + "];");
    });
    ids.forEach(function (v) {
      for (var k = M.off[v]; k < M.off[v + 1]; k++) { var u = M.dst[k]; if (vis[u]) L.push(" n" + u + " -> n" + v + ";"); }
    });
    V.stubs.forEach(function (s, k) {
      var lab = "+" + fmt(s.n) + (s.dir === "u" ? " more cited" : " more citing");
      L.push(" s" + k + ' [label="' + lab + '", shape=box, style="rounded,dashed", fontsize=9, fontcolor="#5C7466", color="#8A9AA5", href="#m' + s.dir + ":" + s.of + '", tooltip="show more"];');
      if (s.dir === "u") L.push(" s" + k + " -> n" + s.of + ' [style=dashed, arrowhead=none];'); else L.push(" n" + s.of + " -> s" + k + " [style=dashed, arrowhead=none];");
    });
    if (this.showDefs && this.defs && this.defs.length) {
      this.defs.slice(0, 10).forEach(function (d, k) {
        L.push(" d" + k + ' [label="Def_' + esc(M.m.defs[d]) + '", shape=note, style=filled, fillcolor="' + PAL.defFill + '", color="' + PAL.defBorder + '", fontsize=9, fontname="Courier", margin="0.12,0.06", href="' + esc(FLT.defHref(d)) + '", tooltip="definition module used by the statement"];');
        L.push(" d" + k + " -> n" + self.focus + ' [style=dotted, color="' + PAL.defBorder + '", arrowhead=odiamond, arrowsize=0.7];');
      });
    }
    L.push("}");
    this.count = V.total;
    return L.join("\n");
  };
  function wrapText(s, width) {
    var words = s.split(/\s+/), lines = [], cur = "";
    words.forEach(function (w) { if ((cur + " " + w).length > width && cur) { lines.push(cur); cur = w; } else cur = cur ? cur + " " + w : w; });
    if (cur) lines.push(cur); if (lines.length > 4) lines = lines.slice(0, 3).concat([lines.slice(3).join(" ").slice(0, width - 1) + "…"]);
    return lines;
  }
  FLT.wrapText = wrapText;
  FLT.Graph.prototype.draw = function () {
    var self = this, el = this.el, dot;
    try { dot = this.dot(); } catch (e) { el.innerHTML = '<p class="muted">Graph unavailable (' + esc(e.message) + ').</p>'; return; }
    getGV().then(function (gv) {
      var t0 = Date.now(), svg = gv.layout(dot, "svg", "dot");
      el.innerHTML = svg;
      var s = el.querySelector("svg");
      if (s) { var wpt = parseFloat(s.getAttribute("width")) || 0; s.removeAttribute("width"); s.removeAttribute("height"); if (wpt) s.style.width = Math.round(wpt * 1.25) + "px"; s.style.maxWidth = "100%"; s.style.height = "auto"; }
      if (self.opts.onDraw) self.opts.onDraw({ ms: Date.now() - t0, nodes: self.count });
    }, function (e) {
      el.innerHTML = '<p class="muted">The interactive graph needs WebAssembly, which this browser did not provide (' + esc(e.message || e) + '). Everything else on this page works without it; the lists above give the same information.</p>';
    });
  };

  // copy buttons: clipboard API when it works, a hidden textarea otherwise, a prompt as the last resort
  FLT.copyText = function (t, done, fail) {
    function fallback() {
      try { var ta = document.createElement("textarea"); ta.value = t; ta.style.position = "fixed"; ta.style.opacity = "0"; document.body.appendChild(ta); ta.select(); var ok = document.execCommand("copy"); document.body.removeChild(ta); if (ok) done(); else { window.prompt("Copy:", t); fail(); } }
      catch (e) { window.prompt("Copy:", t); fail(); }
    }
    if (navigator.clipboard && navigator.clipboard.writeText) { navigator.clipboard.writeText(t).then(done, fallback); } else fallback();
  };
  FLT.wireCopyButtons = function (root) {
    root.querySelectorAll("button.copy").forEach(function (b) {
      if (b._wired) return; b._wired = true;
      b.addEventListener("click", function () { var t = b.getAttribute("data-copy") || ""; FLT.copyText(t, function () { b.textContent = "copied"; setTimeout(function () { b.textContent = "copy"; }, 1200); }, function () { }); });
    });
  };
  // ---------- page furniture ----------
  FLT.initPage = function () {
    FLT.initSearch($("#q"), $("#q-results"));
    document.querySelectorAll(".math-scope").forEach(function (el) { FLT.renderMath(el); });
    document.querySelectorAll(".figure.zoomable").forEach(function (f) {
      f.addEventListener("click", function (ev) { if (ev.target.closest && ev.target.closest("a")) return; f.classList.toggle("zoomed"); });
    });
    FLT.wireCopyButtons(document);
  };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", FLT.initPage); else FLT.initPage();
})();
