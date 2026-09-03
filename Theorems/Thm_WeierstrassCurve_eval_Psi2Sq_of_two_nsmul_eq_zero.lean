import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero

namespace WeierstrassCurve
theorem eval_Psi2Sq_of_two_nsmul_eq_zero {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y)
    (h2 : 2 • (Affine.Point.some _ _ h : W.Point) = 0) : W.Ψ₂Sq.eval x = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero.solution
end WeierstrassCurve
