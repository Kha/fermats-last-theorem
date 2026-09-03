/* Minimal Lean 4 highlighter for statements shown in the explorer. Emits the same CSS classes as the
   build-time (Pygments) highlighting used on the static pages, so one stylesheet serves both. Textual only. */
(function () {
  var KW = {};
  ("theorem lemma def abbrev instance structure class inductive where extends deriving fun let have show from by at " +
   "with match if then else do return open namespace end section variable universe set_option noncomputable private " +
   "protected local scoped attribute import example axiom opaque mutual in calc obtain intro exact apply rw simp " +
   "refine constructor cases induction rcases rintro using this p2m_open p2m_export notation macro syntax")
    .split(" ").forEach(function (k) { if (k) KW[k] = 1; });
  var SORTS = { "Type": 1, "Prop": 1, "Sort": 1 };
  function esc(s) { return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;"); }
  var IDSTART = /[A-Za-z_\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2100-\u214F\uD835«]/;
  var IDCHAR = /[A-Za-z0-9_'!?\u00C0-\u024F\u0370-\u03FF\u1D00-\u1DBF\u2070-\u209F\u2100-\u214F\uD800-\uDFFF»«.]/;
  function highlightLean(src, declName, resolve) {
    var out = [], i = 0, n = src.length;
    while (i < n) {
      var c = src.charAt(i);
      if (c === "-" && src.charAt(i + 1) === "-") {            // line comment
        var j = src.indexOf("\n", i); if (j < 0) j = n;
        out.push('<span class="c1">' + esc(src.slice(i, j)) + "</span>"); i = j; continue;
      }
      if (c === "/" && src.charAt(i + 1) === "-") {            // block comment / docstring
        var j2 = src.indexOf("-/", i + 2); j2 = j2 < 0 ? n : j2 + 2;
        out.push('<span class="cm">' + esc(src.slice(i, j2)) + "</span>"); i = j2; continue;
      }
      if (c === '"') {
        var j3 = i + 1; while (j3 < n && src.charAt(j3) !== '"') { if (src.charAt(j3) === "\\") j3++; j3++; }
        j3 = Math.min(n, j3 + 1); out.push('<span class="s">' + esc(src.slice(i, j3)) + "</span>"); i = j3; continue;
      }
      if (c === "@" && src.charAt(i + 1) === "[") {
        var j4 = src.indexOf("]", i); j4 = j4 < 0 ? n : j4 + 1;
        out.push('<span class="nd">' + esc(src.slice(i, j4)) + "</span>"); i = j4; continue;
      }
      if (/[0-9]/.test(c)) {
        var j5 = i; while (j5 < n && /[0-9_.xXa-fA-F]/.test(src.charAt(j5))) j5++;
        if (src.charAt(j5 - 1) === ".") j5--;
        out.push('<span class="mi">' + esc(src.slice(i, j5)) + "</span>"); i = j5; continue;
      }
      if (IDSTART.test(c)) {
        var j6 = i + 1; while (j6 < n && IDCHAR.test(src.charAt(j6))) j6++;
        var w = src.slice(i, j6);
        if (w.charAt(w.length - 1) === ".") { j6--; w = src.slice(i, j6); }
        if (KW[w]) out.push('<span class="kn">' + esc(w) + "</span>");
        else if (SORTS[w.split(".")[0]] || /^(Type|Sort)\*?$/.test(w)) out.push('<span class="kt">' + esc(w) + "</span>");
        else if (declName && w === declName) out.push('<span class="nf">' + esc(w) + "</span>");
        else { var hr = resolve ? resolve(w) : null; out.push(hr ? '<a class="id" href="' + hr[0] + '" title="' + esc(hr[1]) + '">' + esc(w) + "</a>" : esc(w)); }
        i = j6; continue;
      }
      if ("∀∃λ→↔¬∧∨≠≤≥∣⁻¹×⊗⊕∘∑∏∫⟨⟩⟪⟫≃≅≌⥤⟶↦•∈∉⊆⊂∪∩⊤⊥ᵒᵖ".indexOf(c) >= 0 || ":=<>+*/^|&!~%".indexOf(c) >= 0) {
        out.push('<span class="o">' + esc(c) + "</span>"); i++; continue;
      }
      out.push(esc(c)); i++;
    }
    return out.join("");
  }
  window.FLT_highlightLean = highlightLean;
})();
