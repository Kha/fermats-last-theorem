import Theorems.Thm_fermatLastTheoremEleven
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_CofixedLine
import P2M.Util
namespace P2MW.S_FreyPackage_frey_no_cofixed_eleven

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace FreyPackage p2m_export "FreyPackage" "freyCurve c p a hc0 ha0 b hFLT hb0" end FreyPackage
namespace FreyPackage
p2m_open_scoped "FreyPackage" in

private theorem _root_.FreyPackage.p_ne_of_fermatLastTheoremFor_K (P : FreyPackage) {n : ℕ}
    (hn : FermatLastTheoremFor n) : P.p ≠ n := by
  intro h
  have hint := (fermatLastTheoremFor_iff_int.mp hn) P.a P.b P.c P.ha0 P.hb0 P.hc0
  rw [← h] at hint
  exact hint P.hFLT

end FreyPackage
p2m_export "" "FreyPackage.p_ne_of_fermatLastTheoremFor_K"
theorem solution (P : FreyPackage) (hp : P.p = 11) : ¬ HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by
  exact absurd hp (P.p_ne_of_fermatLastTheoremFor_K fermatLastTheoremEleven)
