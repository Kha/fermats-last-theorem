/* thm.html: one page for every theorem, selected by the URL fragment (#Lean.name). */
(function () {
  "use strict";
  var FLT = window.FLT, esc = FLT.esc, fmt = FLT.fmt;
  var main = document.getElementById("thm-main");
  function byHash() {
    var h = decodeURIComponent((window.location.hash || "").replace(/^#/, ""));
    FLT.withMeta(function (err) {
      if (err || !FLT.M) { main.innerHTML = '<p class="warn">Could not load the site data (data/meta.js). If you moved thm.html out of the html/ folder, put it back next to data/.</p>'; return; }
      if (!h) { renderLanding(); return; }
      var mh = /^(?:x|mu|md):(\d+)$/.exec(h);   // a graph control opened in a new tab: show that theorem
      if (mh && +mh[1] < FLT.M.N) { try { history.replaceState(null, "", "#" + FLT.M.names[+mh[1]]); } catch (e) { } renderTheorem(+mh[1]); return; }
      var i = FLT.indexOf(h);
      if (i < 0) { renderNotFound(h); return; }
      if (FLT.M.names[i] !== h) { try { history.replaceState(null, "", "#" + FLT.M.names[i]); } catch (e) { } }
      renderTheorem(i);
    });
  }
  window.addEventListener("hashchange", byHash);
  byHash();

  function renderLanding() {
    var M = FLT.M, m = M.m;
    document.title = "Theorems · FLT in Lean 4";
    var lms = []; for (var i = 0; i < M.N; i++) if (m.lm[i]) lms.push(i);
    lms.sort(function (a, b) { return m.depth[a] - m.depth[b] || (M.names[a] < M.names[b] ? -1 : 1); });
    main.innerHTML = '<h1>All ' + fmt(M.N) + ' theorems</h1><p>Type a name (or part of one) in the search box, or start from a landmark:</p><ul class="lm-list">' +
      lms.map(function (i) { var t = FLT.title(i); return '<li><a href="#' + esc(M.names[i]) + '">' + (t ? esc(t) + ' <code>' + esc(M.names[i]) + '</code>' : '<code>' + esc(M.names[i]) + '</code>') + '</a> <span class="muted">' + fmt(m.below[i]) + ' below</span></li>'; }).join("") + "</ul>";
  }
  function renderNotFound(h) {
    document.title = "Not found · FLT in Lean 4";
    var res = FLT.search(h.replace(/[._]/g, " "), 30);
    main.innerHTML = '<h1>No theorem named <code>' + esc(h) + '</code></h1>' + (res.length ? '<p>Closest names:</p><ul>' + res.filter(function (r) { return r.kind === "thm"; }).map(function (r) { return '<li><a href="#' + esc(FLT.M.names[r.i]) + '"><code>' + esc(FLT.M.names[r.i]) + '</code></a></li>'; }).join("") + '</ul>' : "");
  }
  function thmLink(i, withNums) {
    var M = FLT.M, t = FLT.title(i), lm = M.m.lm[i] ? '<span class="badge lm" title="named in the route documents">landmark</span> ' : "";
    return '<a class="thm-ref" href="#' + esc(M.names[i]) + '">' + lm + (t ? '<span class="t">' + esc(t) + '</span> ' : "") + '<code>' + esc(M.names[i]) + '</code></a>' +
      (withNums ? ' <span class="muted nums">' + fmt(M.m.below[i]) + ' below · depth ' + M.m.depth[i] + '</span>' : "");
  }
  function renderTheorem(i) {
    var M = FLT.M, m = M.m, name = M.names[i], t = FLT.title(i), stem = FLT.stem(i);
    document.title = (t || FLT.shortName(name)) + " · FLT in Lean 4";
    var cites = FLT.cites(i), citedBy = FLT.citedBy(i);
    citedBy.sort(function (a, b) { return (m.lm[b] - m.lm[a]) || (m.depth[a] - m.depth[b]) || (M.names[a] < M.names[b] ? -1 : 1); });
    var path = FLT.pathToRoot(i);   // i ... root
    var stageName = FLT.stageName(m.stage[i]);
    var via = m.via[i];
    var H = [];
    // breadcrumb / path to FLT
    var crumbs = path.slice().reverse();
    var nOther = 0;
    function crumb(v, k, abbreviate) {
      var lab = FLT.title(v) || FLT.shortName(M.names[v]);
      var pk = m.pkind[v], hop = "";
      if (k > 0 && pk && pk !== "cites") {
        nOther++;
        hop = pk.indexOf("definition:") === 0 ? '<span class="hop" title="not a citation: the previous theorem uses the definition module Def_' + esc(pk.slice(11)) + ', which imports this theorem">via <a href="' + (window.FLT_ROOT || "") + 'def/' + esc(pk.slice(11)) + '.html">Def_' + esc(pk.slice(11)) + '</a> ›</span> ' : '<span class="hop" title="not a citation: the previous theorem\'s statement mentions this theorem">statement mentions ›</span> ';
      }
      return hop + ((k === crumbs.length - 1) ? '<span class="here">' + esc(lab) + '</span>' : '<a href="#' + esc(M.names[v]) + '" title="' + esc(M.names[v]) + '">' + esc(lab) + '</a>');
    }
    var pc = crumbs.map(function (v, k) { return crumb(v, k); });
    var nCite = crumbs.length - 1 - nOther;
    var countTxt = nCite + ' citation' + (nCite === 1 ? "" : "s") + (nOther ? " + " + nOther + (nOther === 1 ? " definition/statement hop" : " definition/statement hops") : "");
    if (pc.length > 9) { pc = pc.slice(0, 4).concat(['<a href="javascript:void(0)" class="path-more" title="show the whole path">… ' + (pc.length - 8) + ' more …</a>']).concat(pc.slice(-4)); }
    H.push('<nav class="path" aria-label="one shortest path from Fermat\'s Last Theorem to this theorem"><span class="muted">Path from FLT (' + countTxt + '):</span> ' + pc.join(' <span class="sep">›</span> ') + '</nav>');
    H.push('<header class="thm-head">' + (t ? '<h1 class="math-scope">' + esc(t) + '</h1><div class="lean-name"><code>' + esc(name) + '</code></div>' : '<h1><code>' + esc(name) + '</code></h1>') + '<div class="badges">' +
      (i === m.root ? '<span class="badge root">the theorem</span>' : "") +
      (m.lm[i] ? '<span class="badge lm">landmark: named in the route documents</span>' : "") +
      (stageName ? '<a class="badge stage" href="' + (window.FLT_ROOT || "") + 'route/index.html#stage-' + m.stage[i] + '">' + (m.lm[i] || i === m.root ? "" : "under: ") + esc(stageName) + '</a>' : "") +
      (m.port && m.port[i] === 1 ? (m.portnotes ? '<a class="badge dup" href="' + (window.FLT_ROOT || "") + m.portnotes + '"' : '<span class="badge dup"') + ' title="one of the 28 statement files edited by hand when the tree was carried from Lean 4.30 to Lean 4.33' + (m.portnotes ? '; the port notes (§5.2) argue the proposition is unchanged' : '') + '">statement text edited in the Lean 4.33 port' + (m.portnotes ? '</a>' : '</span>') : "") +
      (m.port && m.port[i] === 2 ? '<a class="badge dup" href="' + (window.FLT_ROOT || "") + 'def/Compat_Mathlib430.html" title="the statement imports Def_Compat_Mathlib430: Mathlib v4.30 definitions that changed meaning under the same name in v4.33, kept verbatim under new names' + (m.portnotes ? ' (port notes §4)' : '') + '">uses a kept Mathlib v4.30 definition</a>' : "") +
      (m.aliases && m.aliases[name] ? '<span class="badge" title="classical name(s) this step goes by in the route documents">' + esc(m.aliases[name]) + '</span>' : "") +
      (m.dup[i] ? '<span class="badge dup" title="the statement module declares P2M.Dup.' + esc(name) + ' because a definition module already declares this name with the same type">duplicate-name statement</span>' : "") +
      '<span class="badge proved" title="kernel-checked; depends only on propext, Classical.choice, Quot.sound">proved</span></div></header>');
    H.push('<section id="en-box"></section>');
    H.push('<section><h2>Lean statement <span class="muted small">from <code>Theorems/Thm_' + esc(stem) + '.lean</code>, preamble omitted</span> <button class="copy small" id="copy-stmt">copy</button></h2><div id="stmt-box"><p class="muted">loading the statement…</p></div></section>');
    H.push('<section class="numbers"><h2>Numbers</h2><ul class="kv">' +
      (m.below[i] > 0 ? '<li><b>' + fmt(m.below[i]) + '</b> theorems below (in the import closure of its proof)</li>' : '<li><b>0</b> theorems below: its proof cites no theorem of the tree and is carried out directly from Mathlib' + " and the definition modules</li>") +
      '<li>cites <b>' + cites.length + '</b> theorems directly; cited by <b>' + citedBy.length + '</b></li>' +
      '<li>depth <b>' + m.depth[i] + '</b> from <code>fermat_last_theorem</code> (shortest citation path); longest chain below it: <b>' + m.height[i] + '</b></li>' +
      '<li id="num-proof" class="muted">proof size: loading…</li></ul></section>');
    H.push('<section><h2>Neighbourhood <span class="muted small">premises above, conclusions below; click a name to go there, <b>+</b> to expand</span></h2>' +
      '<div class="graph-tools"><button id="g-path">add path to FLT</button> <button id="g-reset">reset</button> <label><input type="checkbox" id="g-defs" checked> definition modules</label> <span class="muted small" id="g-info"></span></div>' +
      '<div id="graph" class="graph-box"><p class="muted">laying out…</p></div></section>');
    H.push('<section class="two-col"><div><h2>Uses <span class="muted small">(' + cites.length + ' cited theorems, in import order)</span></h2>' + (cites.length ? '<ul class="refs" id="uses-list">' + cites.map(function (v) { return "<li>" + thmLink(v, true) + "</li>"; }).join("") + "</ul>" : '<p class="muted">Cites no theorem of the tree: proved from Mathlib and the definitions alone.</p>') +
      '<div id="uses-defs"></div></div>' +
      '<div><h2>Used by <span class="muted small">(' + citedBy.length + ')</span></h2>' + (citedBy.length ? '<ul class="refs" id="usedby">' + citedBy.slice(0, 60).map(function (v) { return "<li>" + thmLink(v, true) + "</li>"; }).join("") + "</ul>" + (citedBy.length > 60 ? '<p><a href="javascript:void(0)" id="usedby-all">show all ' + citedBy.length + '</a></p>' : "") : '<p class="muted">' + (i === m.root ? "This is the final theorem." : "No proof module cites it" + (m.pkind[i] && m.pkind[i] !== "cites" ? "; it is reached through " + esc(m.pkind[i].indexOf("definition:") === 0 ? "the definition module Def_" + m.pkind[i].slice(11) + ", which imports it" : "a statement that mentions it") + "." : ".")) + "</p>") + "</div></section>");
    H.push('<section id="source-box"><h2>Source</h2><p class="muted">loading…</p></section>');
    main.innerHTML = H.join("");
    window.scrollTo(0, 0);
    var pm = main.querySelector(".path-more");
    if (pm) pm.addEventListener("click", function () { nOther = 0; var full = crumbs.map(function (v, k) { return crumb(v, k); }); main.querySelector("nav.path").innerHTML = '<span class="muted">Path from FLT (' + countTxt + '):</span> ' + full.join(' <span class="sep">›</span> '); });
    var ua = document.getElementById("usedby-all");
    if (ua) ua.addEventListener("click", function () { document.getElementById("usedby").innerHTML = citedBy.map(function (v) { return "<li>" + thmLink(v, true) + "</li>"; }).join(""); ua.parentNode.removeChild(ua); });
    // graph
    var g = new FLT.Graph(document.getElementById("graph"), i, { onDraw: function (s) { document.getElementById("g-info").textContent = s.nodes + " nodes · laid out in " + s.ms + " ms"; } });
    document.getElementById("g-path").addEventListener("click", function () { g.addPathToRoot(); });
    document.getElementById("g-reset").addEventListener("click", function () { g.reset(); });
    document.getElementById("g-defs").addEventListener("change", function (ev) { g.showDefs = ev.target.checked; g.draw(); });
    // record (statement text etc.) from the shard
    FLT.withRecord(name, function (r) {
      if (FLT.M.names[i] !== decodeURIComponent((window.location.hash || "").slice(1))) return; // navigated away
      if (!r) { document.getElementById("stmt-box").innerHTML = '<p class="warn">The data shard for this theorem did not load.</p>'; g.draw(); return; }
      g.defs = r.sd || []; g.draw();
      // English
      if (r.en) {
        var en = r.en, E = [], P = [];
        if (en.title_html) { var h1 = main.querySelector("header.thm-head h1"); if (h1) h1.innerHTML = en.title_html; }   // the title with its mathematics typeset (titles.js carries the plain form)
        if (en.context_html) { var cx = document.createElement("div"); cx.className = "en-context lead"; cx.innerHTML = en.context_html; var hd = main.querySelector("header.thm-head"); hd.parentNode.insertBefore(cx, hd.nextSibling); }
        if (en.statement_html) E.push('<h2>Informal statement <span class="muted small">a reading aid; the Lean statement below is what is proved</span></h2><div class="en">' + en.statement_html + '</div>');
        if (en.strength_html) E.push('<div class="strength"><h3>Compared with the classical theorem</h3>' + en.strength_html + '</div>');
        if (m.enNote && (en.statement_html || en.proof_html || en.context_html)) E.push('<p class="muted small en-note">' + esc(m.enNote) + '</p>');
        document.getElementById("en-box").innerHTML = E.join("");
        if (en.proof_html) P.push('<h2>Idea of the proof <span class="muted small">(informal)</span></h2><div class="en-context">' + en.proof_html + '</div>');
        if (en.references_html && en.references_html.length) P.push('<h3>References</h3><ol class="refs-lit small">' + en.references_html.map(function (x) { return "<li>" + x + "</li>"; }).join("") + '</ol>' + (m.refNote ? '<p class="muted small">' + esc(m.refNote) + '</p>' : ''));
        if (P.length) { var ps = document.createElement("section"); ps.innerHTML = P.join(""); var sb = document.getElementById("stmt-box").parentNode; sb.parentNode.insertBefore(ps, sb.nextSibling); }
        FLT.renderMath(main);   // typeset the $…$ of the English text just inserted (TeX source in span.tex)
      }
      // Lean statement
      var ctx = (r.cx || []), S = [];
      var resolve = FLT.makeResolver(ctx, name, r.dc);
      var resolveP = r.so && r.so.tail ? FLT.makeResolver(ctx.concat(r.so.tail.split("\n")), name, r.so.tail) : resolve;
      if (ctx.length) S.push('<pre class="lean ctx" title="context lines of the statement module: open namespaces, variables, options">' + FLT_highlightLean(ctx.join("\n"), null, resolve) + '</pre>');
      S.push('<pre class="lean stmt">' + FLT_highlightLean(r.dc, name, resolve) + ' <span class="c1">:= … </span></pre>');
      if (r.tr && r.tr.length) S.push('<pre class="lean ctx">' + FLT_highlightLean(r.tr.join("\n"), null, resolve) + '</pre>');
      if (r.ml && r.ml.length && !(r.ml.length === 1 && r.ml[0] === "Mathlib")) S.push('<p class="muted small">Mathlib imports of the statement file: ' + r.ml.map(function (x) { return m.mathlibDocs ? '<a class="ext" href="' + m.mathlibDocs + x.replace(/\./g, "/") + '.html" title="external link: mathlib4 documentation for this module (tracks current Mathlib, not necessarily v4.33.0); nothing is fetched unless you click"><code>' + esc(x) + '</code> ↗</a>' : '<code>' + esc(x) + '</code>'; }).join(", ") + '</p>');
      document.getElementById("stmt-box").innerHTML = S.join("");
      document.getElementById("copy-stmt").setAttribute("data-copy", (ctx.length ? ctx.join("\n") + "\n" : "") + r.dc);
      // defs used
      var D = [];
      if (r.sd && r.sd.length) D.push('<h3>Definition modules imported by the statement file</h3><ul class="refs defs">' + r.sd.map(function (d) { return '<li><a href="' + FLT.defHref(d) + '"><code>Def_' + esc(m.defs[d]) + '</code></a></li>'; }).join("") + '</ul>');
      var pdOnly = (r.pd || []).filter(function (d) { return !r.sd || r.sd.indexOf(d) < 0; });
      if (pdOnly.length) D.push('<h3>Further definition modules imported by the proof</h3><ul class="refs defs">' + pdOnly.map(function (d) { return '<li><a href="' + FLT.defHref(d) + '"><code>Def_' + esc(m.defs[d]) + '</code></a></li>'; }).join("") + '</ul>');
      if (r.st && r.st.length) D.push('<h3>Theorems mentioned in the statement itself</h3><ul class="refs">' + r.st.map(function (v) { return '<li>' + thmLink(v, false) + '</li>'; }).join("") + '</ul>');
      document.getElementById("uses-defs").innerHTML = D.join("");
      // per-citation textual use counts
      if (r.cu && r.cu.length === cites.length) {
        var lis = main.querySelectorAll("#uses-list > li");
        for (var q = 0; q < lis.length && q < r.cu.length; q++) {
          var c = r.cu[q], sp = document.createElement("span");
          sp.className = "muted nums cu"; sp.textContent = c === null ? "" : (c > 0 ? " · name occurs " + c + "× in the proof" : " · imported; name not in the proof text");
          if (c === 0) sp.className += " warnish";
          lis[q].appendChild(sp);
        }
      }
      // landmark: whole proof module
      if (r.proof_html) {
        var det = document.createElement("section");
        det.innerHTML = '<h2>The proof module <span class="muted small">' + fmt(r.proof_lines) + ' lines after the imports and the generated preamble; file-local helpers first, <code>solution</code> last</span></h2><details' + (r.proof_lines <= 120 ? " open" : "") + '><summary>show the proof text</summary><pre class="lean sol">' + r.proof_html + '</pre></details>';
        document.getElementById("source-box").parentNode.insertBefore(det, document.getElementById("source-box").nextSibling);
      }
      // numbers
      if (r.so) document.getElementById("num-proof").outerHTML = '<li>proof module: <b>' + fmt(r.so.cl) + '</b> lines after the preamble (' + fmt(r.so.ln) + ' in the file), <b>' + fmt(r.so.h) + '</b> file-local helper theorem' + (r.so.h === 1 ? "" : "s") + (r.so.dl ? ', ' + r.so.dl + ' local definition' + (r.so.dl === 1 ? "" : "s") : "") + '</li>';
      // source
      var src = [];
      src.push('<ul class="src-links"><li>Statement: <a href="../Theorems/Thm_' + esc(stem) + '.lean"><code>Theorems/Thm_' + esc(stem) + '.lean</code></a> <button class="copy small" data-copy="Theorems/Thm_' + esc(stem) + '.lean">copy</button></li>' +
        '<li>Proof: <a href="../P2M/Sol/S_' + esc(stem) + '.lean"><code>P2M/Sol/S_' + esc(stem) + '.lean</code></a> <button class="copy small" data-copy="P2M/Sol/S_' + esc(stem) + '.lean">copy</button> <span class="muted small">(links work when this html/ folder sits at the root of the repository)</span></li></ul>');
      if (r.so && r.so.tail) {
        src.push('<h3>How the proof concludes <span class="muted small">the final <code>solution</code> declaration of the proof module' + (r.so.tt ? ', first ' + r.so.tail.split("\n").length + ' of its ' + fmt(r.so.tl) + ' lines' : "") + ' (line ' + fmt(r.so.sl) + ')</span></h3><pre class="lean sol">' + FLT_highlightLean(r.so.tail, null, resolveP) + (r.so.tt ? '\n<span class="c1">  … continues in the file</span>' : "") + '</pre>');
      }
      document.getElementById("source-box").innerHTML = '<h2>Source</h2>' + src.join("");
      FLT.wireCopyButtons(main);
    });
  }
})();
