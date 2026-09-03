// usage: bun gen/katex_render.js <katex.min.js> < in.json > out.json
// in  = [[tex, display, wantHtml], ...]
// out = [[html, null] | [null, "KaTeX error message"], ...]  (strict parse: a fragment that KaTeX cannot parse is reported, never rendered in red)
// The same katex.min.js is shipped to the browser, and assets/site.js (FLT.KATEX_OPTS) typesets the English-layer fragments with the SAME
// options as OPTS below — keep the two textually identical — except 'trust': here any trust-gated command (\href, \url, \includegraphics,
// \html…) is turned into a parse error so it is caught at build time; the browser passes trust:false and never meets one that got through.
const fs = require("fs");
const katex = require(require("path").resolve(process.argv[2]));
// MACROS: the few amsmath/stmaryrd commands the English text uses that KaTeX 0.18 lacks, defined by their standard construction
// (same table in assets/site.js; copied per call because KaTeX writes \gdef's into the macros object it is given)
const MACROS = { "\\bigsqcap": "\\mathop{\\Large\\sqcap}" };
const OPTS = { throwOnError: true, output: "html", strict: "ignore", maxSize: 20, maxExpand: 1000, errorColor: "#cc0000",
               trust: (ctx) => { throw new katex.ParseError("trust-gated command " + ctx.command + " is not accepted here"); } };
const items = JSON.parse(fs.readFileSync(0, "utf8"));
const out = items.map(([tex, display, wantHtml]) => {
  try {
    const h = katex.renderToString(tex, Object.assign({ displayMode: !!display, macros: Object.assign({}, MACROS) }, OPTS));
    if (h.indexOf(OPTS.errorColor) >= 0) return [null, "KaTeX rendered part of this in its error colour (unsupported command)"];
    return [wantHtml ? h : "", null];
  } catch (e) {
    return [null, String((e && e.message) || e).slice(0, 400)];
  }
});
fs.writeFileSync(1, JSON.stringify(out));
