import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY

namespace WeierstrassCurve.Affine.Point
theorem two_nsmul_eq_zero_iff_Y_eq_negY {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y) :
    2 • (some _ _ h : W.Point) = 0 ↔ y = W.negY x y := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY.solution
end WeierstrassCurve.Affine.Point
