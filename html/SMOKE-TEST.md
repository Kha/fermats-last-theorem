# Six clicks to check these pages in your browser

The pages were machine-tested in a Chromium browser opened on the files directly (no web server). Safari and
Firefox could not be tested where they were built; these six steps (three minutes) exercise everything:

1. Open 'html/index.html' by double-clicking it. Expected: the statement of the theorem, and on the right a small
   graph of nine green cards. Click the card "No Frey package exists".
2. Expected: the theorem page for FreyPackage.no_frey_package, with an informal statement, its Lean statement, a
   "Neighbourhood" graph (a handful of green cards and a violet definition box) and lists "Uses" / "Used by". If the graph box instead shows a sentence
   beginning "The interactive graph needs WebAssembly", everything else still works; note the browser and version.
3. In that graph, click the small "+" on the card "Modularity of the Frey curve". Expected: the graph grows by a few cards.
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
