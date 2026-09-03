import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_freyCurve_rational_p_torsion_eq_zero

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem FreyPackage.freyCurve_rational_p_torsion_eq_zero (P : FreyPackage) (y : (P.freyCurve⁄ℚ).Point) (hy : P.p • y = 0) : y = 0 := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.solution
