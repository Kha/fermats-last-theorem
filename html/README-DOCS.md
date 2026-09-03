# Reader's documentation for the Lean 4 proof of Fermat's Last Theorem

This folder is a set of static web pages describing the Lean sources in this repository (Lean v4.33.1, Mathlib v4.33.0): the statement and
its axiom check, the route of the proof step by step, a page for each of the 29,511 theorems (exact Lean statement,
what its proof cites and what cites it, its place under the final theorem, an expandable neighbourhood graph, the
proof's closing lines), a page for each of the 1,450 definition modules (full highlighted source, declaration
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
* The documents under 'Documents' are the repository's README.md and ATTRIBUTION.md rendered as written; the route
  chapters render PROOF-PATH.md ('The route in brief') and the project's longer route document, which is not itself a
  file of the repository.
* English titles, informal statements, proof ideas and context paragraphs (on 29,511 theorem pages and
  1,450 definition-module pages) are editorial additions kept outside the Lean files. Each such page
  carries the note "English text generated automatically from the Lean source; the Lean statement is authoritative".
  Their mathematics is typeset in the browser by the bundled KaTeX (assets/vendor/katex/katex.min.js).
  References are suggested automatically and have not been individually verified.
* 'About these pages' (about.html) states the conventions and the limits of a textual reading of the tree.

Size: about 390 MB unpacked, 2,073 files. Generated 2026-09-03.
